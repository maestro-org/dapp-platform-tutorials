use aiken/interval.{Finite, Interval, IntervalBound}
use aiken/list
use aiken/option.{is_none}
use aiken/transaction.{InlineDatum, Output, ScriptContext, Spend, Transaction}
use aiken/transaction/credential.{Address, VerificationKeyCredential}
use aiken/transaction/value.{Value, add, flatten, negate}

type OracleAnswer =
  Int

type BetRefParam {
  oracle_pkh: ByteArray,
  bet_until: Int,
  bet_reveal: Int,
  bet_step: Value,
}

type BetRefDatum {
  bets: List<(ByteArray, OracleAnswer)>,
  previous_bet: Value,
}

type BetRefAction {
  Bet(OracleAnswer)
  Take
}

validator(bet_param: BetRefParam) {
  fn bet_ref_spend(
    dat: BetRefDatum,
    action: BetRefAction,
    ctx: ScriptContext,
  ) -> Bool {
    let BetRefParam { oracle_pkh, bet_until, bet_reveal, bet_step } =
      bet_param

    let BetRefDatum { bets, previous_bet } =
      dat

    let ScriptContext { transaction, purpose } =
      ctx

    expect Spend(utxo_ref) =
      purpose

    let Transaction {
      inputs,
      reference_inputs,
      outputs,
      extra_signatories,
      validity_range,
      ..
    } =
      transaction

    expect [signer] =
      extra_signatories

    let Interval { lower_bound, upper_bound } =
      validity_range

    expect Some(own_input) =
      list.find(inputs, fn(input) { input.output_reference == utxo_ref })

    let Output { address: in_address, value: in_value, .. } =
      own_input.output
    when action is {
      Bet(guess) -> {
        // Output address check is here
        expect [own_output] =
          list.filter(outputs, fn(output) { output.address == in_address })

        let Output { value: out_value, datum: out_datum, .. } =
          own_output

        expect InlineDatum(out_datum) =
          out_datum

        expect BetRefDatum { bets: out_bets, previous_bet: out_previous_bet }: BetRefDatum =
          out_datum

        let IntervalBound { bound_type, .. } =
          upper_bound

        expect Finite(upper_bound) =
          bound_type

        let expected_value =
          in_value
            |> add(previous_bet)
            |> add(bet_step)
            |> flatten

        let bet_value_greater =
          out_value
            |> flatten
            |> check_bet_value_greater(expected_value)

        let fin =
          (bet_until >= upper_bound)? && ([(signer, guess), ..bets] == out_bets)? && bet_value_greater? && (out_previous_bet == add(
            out_value,
            negate(in_value),
          ))?

        fin
      }

      Take -> {
        let IntervalBound { bound_type, .. } =
          lower_bound

        expect Finite(lower_bound) =
          bound_type

        expect Some((_, guess)) =
          list.find(
            bets,
            fn(item) {
              let (signer_item, _) =
                item
              signer_item == signer
            },
          )

        expect [ref_output] =
          list.filter(
            reference_inputs,
            fn(item) {
              let ref_script =
                item.output.reference_script
              is_none(ref_script)
            },
          )

        let Output {
          address: Address { payment_credential, .. },
          datum: oracle_datum,
          ..
        } =
          ref_output.output

        expect VerificationKeyCredential(oracle_payment_key) =
          payment_credential

        expect InlineDatum(oracle_datum) =
          oracle_datum

        expect oracle_answer: Int =
          oracle_datum

        let user_guess_diff =
          guess_diff(oracle_answer, guess)

        let oracle_pkh_matches =
          oracle_payment_key == oracle_pkh

        let no_continuing_outputs =
          outputs
            |> list.find(fn(output) { output.address == in_address })
            |> is_none

        let guess_is_closest =
          list.all(
            bets,
            fn(other_bet) {
              let (_, other_guess) =
                other_bet

              user_guess_diff <= guess_diff(other_guess, oracle_answer)
            },
          )

        let fin =
          (bet_reveal <= lower_bound)? && no_continuing_outputs? && oracle_pkh_matches? && guess_is_closest?
        fin
      }
    }
  }
}

fn check_bet_value_greater(
  value1: List<(ByteArray, ByteArray, Int)>,
  value2: List<(ByteArray, ByteArray, Int)>,
) -> Bool {
  when (value1, value2) is {
    (
      [(policy1, name1, quantity1), ..rest_values1],
      [(policy2, name2, quantity2), ..rest_values2],
    ) -> {
      let value_check =
        policy1 == policy2 && name1 == name2 && quantity1 >= quantity2

      value_check && check_bet_value_greater(rest_values1, rest_values2)
    }
    ([], []) ->
      True

    _ ->
      False
  }
}

fn guess_diff(left: Int, right: Int) -> Int {
  let diff =
    left - right
  if diff < 0 {
    -diff
  } else {
    diff
  }
}
