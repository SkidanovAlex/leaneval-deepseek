import Mathlib
import Submission.Work.WilkiesH.Interp.V2Params

/-!
# The constant comparison `72 · K^μ · (μ+2)^(μ+1) · (EE μ + 2) ≤ CCc μ`

With `K = KK μ = 2μ+4 = 2(μ+2)`, `E = EE μ = (μ+2)^(40(μ+1)²)` and
`C = CCc μ = (μ+2)^(100(μ+1)²)`, and writing `N = μ+2 ≥ 2`, the claim reads

  `72 · (2N)^μ · N^(μ+1) · (N^(40(μ+1)²) + 2) ≤ N^(100(μ+1)²)`.

It follows from three elementary estimates:

* `72 · (2N)^μ ≤ N^(2μ+7)`: here `72 ≤ 2^7 ≤ N^7` and `2^μ ≤ N^μ`;
* `N^(40(μ+1)²) + 2 ≤ N^(40(μ+1)²+1)`: here `2 ≤ N` (so `2 ≤ N^(40(μ+1)²)`)
  and `2·N^a ≤ N·N^a = N^(a+1)`;
* `(2μ+7) + (μ+1) + (40(μ+1)² + 1) = 40(μ+1)² + 3μ + 9 ≤ 100(μ+1)²`,
  because `3μ + 9 ≤ 60(μ+1) ≤ 60(μ+1)²` for `μ ≥ 0`;

together with monotonicity of `n ↦ N^n`.
-/

set_option autoImplicit false

namespace Work.WilkiesH.Interp.V2qd

theorem const_le_CCc (μ : ℕ) :
    72 * (Work.WilkiesH.Interp.KK μ) ^ μ * (μ + 2) ^ (μ + 1) * (Work.WilkiesH.Interp.EE μ + 2)
      ≤ Work.WilkiesH.Interp.CCc μ := by
  have hK : Work.WilkiesH.Interp.KK μ = 2 * (μ + 2) := by
    show 2 * μ + 4 = 2 * (μ + 2)
    ring
  have hEE : Work.WilkiesH.Interp.EE μ = (μ + 2) ^ (40 * (μ + 1) ^ 2) := rfl
  have hCC : Work.WilkiesH.Interp.CCc μ = (μ + 2) ^ (100 * (μ + 1) ^ 2) := rfl
  rw [hCC, hK]
  have h2 : 2 ≤ μ + 2 := by omega
  have hpos : 0 < μ + 2 := by omega
  -- Step 1: `72 · (2(μ+2))^μ ≤ (μ+2)^(2μ+7)`.
  have hstep1 : 72 * (2 * (μ + 2)) ^ μ ≤ (μ + 2) ^ (2 * μ + 7) := by
    have hsum : 7 + μ + μ = 2 * μ + 7 := by omega
    have h72 : 72 ≤ (μ + 2) ^ 7 := by
      calc 72 ≤ 2 ^ 7 := by norm_num
        _ ≤ (μ + 2) ^ 7 := Nat.pow_le_pow_left h2 7
    calc 72 * (2 * (μ + 2)) ^ μ = 72 * 2 ^ μ * (μ + 2) ^ μ := by
          rw [mul_pow]; ring
      _ ≤ (μ + 2) ^ 7 * (μ + 2) ^ μ * (μ + 2) ^ μ :=
            Nat.mul_le_mul (Nat.mul_le_mul h72 (Nat.pow_le_pow_left h2 μ)) le_rfl
      _ = (μ + 2) ^ (2 * μ + 7) := by
            rw [← pow_add, ← pow_add, hsum]
  -- Step 2: `EE μ + 2 ≤ (μ+2)^(40(μ+1)²+1)`.
  have hstep2 : Work.WilkiesH.Interp.EE μ + 2 ≤ (μ + 2) ^ (40 * (μ + 1) ^ 2 + 1) := by
    rw [hEE]
    have h1le : 1 ≤ 40 * (μ + 1) ^ 2 := by
      have hsq : 1 ≤ (μ + 1) ^ 2 := Nat.one_le_pow' 2 μ
      calc (1 : ℕ) = 1 * 1 := by ring
        _ ≤ 40 * (μ + 1) ^ 2 := Nat.mul_le_mul (by norm_num) hsq
    have h2le : 2 ≤ (μ + 2) ^ (40 * (μ + 1) ^ 2) := by
      calc 2 ≤ μ + 2 := h2
        _ = (μ + 2) ^ 1 := (pow_one _).symm
        _ ≤ (μ + 2) ^ (40 * (μ + 1) ^ 2) := Nat.pow_le_pow_right hpos h1le
    have hmul : (μ + 2) * (μ + 2) ^ (40 * (μ + 1) ^ 2)
        = (μ + 2) ^ (40 * (μ + 1) ^ 2) * (μ + 2) := Nat.mul_comm _ _
    calc (μ + 2) ^ (40 * (μ + 1) ^ 2) + 2
        ≤ (μ + 2) ^ (40 * (μ + 1) ^ 2) + (μ + 2) ^ (40 * (μ + 1) ^ 2) :=
          Nat.add_le_add_left h2le _
      _ = 2 * (μ + 2) ^ (40 * (μ + 1) ^ 2) := by ring
      _ ≤ (μ + 2) * (μ + 2) ^ (40 * (μ + 1) ^ 2) := Nat.mul_le_mul_right _ h2
      _ = (μ + 2) ^ (40 * (μ + 1) ^ 2 + 1) := by rw [hmul, ← pow_succ]
  -- Step 3: the exponent comparison.
  have hexp : 2 * μ + 7 + (μ + 1) + (40 * (μ + 1) ^ 2 + 1) ≤ 100 * (μ + 1) ^ 2 := by
    have hsq : μ + 1 ≤ (μ + 1) ^ 2 := by
      calc μ + 1 = (μ + 1) ^ 1 := (pow_one _).symm
        _ ≤ (μ + 1) ^ 2 := Nat.pow_le_pow_right (by omega) (by norm_num)
    have h1 : 3 * μ + 9 ≤ 60 * (μ + 1) := by omega
    have h3 : 3 * μ + 9 ≤ 60 * (μ + 1) ^ 2 :=
      le_trans h1 (Nat.mul_le_mul_left 60 hsq)
    have h4 : 40 * (μ + 1) ^ 2 + (3 * μ + 9) ≤ 40 * (μ + 1) ^ 2 + 60 * (μ + 1) ^ 2 :=
      Nat.add_le_add_left h3 _
    nlinarith [h4]
  calc 72 * (2 * (μ + 2)) ^ μ * (μ + 2) ^ (μ + 1) * (Work.WilkiesH.Interp.EE μ + 2)
      ≤ (μ + 2) ^ (2 * μ + 7) * (μ + 2) ^ (μ + 1) * (μ + 2) ^ (40 * (μ + 1) ^ 2 + 1) :=
        Nat.mul_le_mul (Nat.mul_le_mul hstep1 le_rfl) hstep2
    _ = (μ + 2) ^ (2 * μ + 7 + (μ + 1) + (40 * (μ + 1) ^ 2 + 1)) := by
        rw [← pow_add, ← pow_add]
    _ ≤ (μ + 2) ^ (100 * (μ + 1) ^ 2) := Nat.pow_le_pow_right hpos hexp

end Work.WilkiesH.Interp.V2qd
