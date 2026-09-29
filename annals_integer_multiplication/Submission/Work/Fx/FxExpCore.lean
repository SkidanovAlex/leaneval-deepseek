import Submission.Work.Fx.FxAdapt

/-!
# Numerical sub-words used by the exponential words (paper §2.8)

`NumWords hk hi` bundles the three primitive numerical words the exponential fields need:
fixed-point `π`, fixed-point `log 2`, and the complex exponential of a bounded argument.
-/

set_option autoImplicit false

namespace Work.Fx

open HvdH

/-- The numerical constants/words required by `cis`, `expNeg` and `expPos`. -/
structure NumWords (hk : KernelLib) (hi : IntLib) : Prop where
  /-- `|u - 2^p π| ≤ 1` -/
  pi : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p : ℕ), 100 ≤ p →
    WordR main prog (fun vs => ∃ (rest : List Val), vs = .int (p : ℤ) :: rest)
      (fun vs out => ∃ (rest : List Val) (u : ℤ), vs = .int (p : ℤ) :: rest ∧
        out = .int u :: rest ∧ |(u : ℝ) - 2 ^ p * Real.pi| ≤ 1)
      (fun _ => K * (p + 1) ^ K)
  /-- `|u - 2^p log 2| ≤ 1` -/
  log2 : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p : ℕ), 100 ≤ p →
    WordR main prog (fun vs => ∃ (rest : List Val), vs = .int (p : ℤ) :: rest)
      (fun vs out => ∃ (rest : List Val) (u : ℤ), vs = .int (p : ℤ) :: rest ∧
        out = .int u :: rest ∧ |(u : ℝ) - 2 ^ p * Real.log 2| ≤ 1)
      (fun _ => K * (p + 1) ^ K)
  /-- complex exponential of a bounded argument, error `≤ 4·2^-p` -/
  expc : ∃ (prog : Cmd) (K : ℕ), ∀ (main : Cmd) (p : ℕ) (X Y : ℤ), 100 ≤ p →
    ((X : ℝ) ^ 2 + (Y : ℝ) ^ 2 ≤ (32 * 2 ^ p) ^ 2) →
    WordR main prog (fun vs => ∃ (rest : List Val),
        vs = .int (p : ℤ) :: .int X :: .int Y :: rest)
      (fun vs out => ∃ (rest : List Val) (U V : ℤ),
        vs = .int (p : ℤ) :: .int X :: .int Y :: rest ∧ out = .int U :: .int V :: rest ∧
        ‖((U : ℂ) + (V : ℂ) * Complex.I) / 2 ^ p -
          Complex.exp (((X : ℂ) + (Y : ℂ) * Complex.I) / 2 ^ p)‖ ≤ 4 / (2 : ℝ) ^ p)
      (fun _ => K * (p + 1) ^ K)

end Work.Fx
