import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.cellSplitDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.cellPhi_beta_le` — the `β`-increment of `cellPhi`

`cellPhi τ β = τ + β − √(τ² + 2τβ)`.  For `0 ≤ τ ≤ u_hi`, `|b| ≤ V`, `|b'| ≤ V` and
`|b − b'| ≤ o`:

  `cellPhi τ b − cellPhi τ b' ≤ o + √(2 o u_hi)`.

Proof.  Put `A = τ² + 2τb`, `B = τ² + 2τb'`; then

  `cellPhi τ b − cellPhi τ b' = (b − b') + (√B − √A)`.

* If `b' ≤ b` then `B ≤ A`, so `√B ≤ √A` by monotonicity of `√` and the whole expression
  is `≤ b − b' ≤ o ≤ o + √(2ou_hi)`.
* If `b ≤ b'`, write `d = b' − b ≥ 0`, so `B − A = 2τd`.  Since `√` is subadditive in the
  form `√B ≤ √A + √(B − A)` (proved below, and honest even for the junk value on negative
  arguments), `√B − √A ≤ √(2τd)`, whence
  `cellPhi τ b − cellPhi τ b' ≤ −d + √(2τd) ≤ √(2τd) ≤ √(2ou_hi)`,
  using `τ ≤ u_hi` and `d ≤ o` (here the hypothesis `|b − b'| ≤ o` is used only through
  `b' − b ≤ o`; the bounds `|b|,|b'| ≤ V` are not needed).

Both branches are `≤ o + √(2ou_hi)` since `o ≥ 0`.
-/

noncomputable section

namespace Work.BoseBogFS

/-- Subadditivity of `Real.sqrt` in the form `√B ≤ √A + √(B − A)` for `A ≤ B`.  This holds
for *all* reals `A ≤ B`, with the junk value `√x = 0` for `x < 0`: if `A < 0` then `√A = 0`
and `√B ≤ √(B − A)` since `B ≤ B − A`. -/
lemma sqrt_le_sqrt_add_sub {A B : ℝ} (hAB : A ≤ B) :
    Real.sqrt B ≤ Real.sqrt A + Real.sqrt (B - A) := by
  have hBA : 0 ≤ B - A := sub_nonneg.mpr hAB
  rcases le_or_gt 0 A with hA | hA
  · have hB : 0 ≤ B := le_trans hA hAB
    refine (Real.sqrt_le_left (add_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg (B - A)))).mpr ?_
    have hexp : (Real.sqrt A + Real.sqrt (B - A)) ^ 2
        = A + 2 * (Real.sqrt A * Real.sqrt (B - A)) + (B - A) := by
      rw [add_sq, Real.sq_sqrt hA, Real.sq_sqrt hBA]
      ring
    have hnn : 0 ≤ Real.sqrt A * Real.sqrt (B - A) :=
      mul_nonneg (Real.sqrt_nonneg A) (Real.sqrt_nonneg (B - A))
    linarith
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_lt hA), zero_add]
    exact Real.sqrt_le_sqrt (by linarith)

/-- `√B − √A ≤ √(B − A)` for `A ≤ B` (junk-value-safe version of the standard estimate). -/
lemma sqrt_sub_sqrt_le_sqrt_sub {A B : ℝ} (hAB : A ≤ B) :
    Real.sqrt B - Real.sqrt A ≤ Real.sqrt (B - A) := by
  have h := sqrt_le_sqrt_add_sub hAB
  linarith

theorem cellPhi_beta_le {τ b b' o u_hi V : ℝ}
    (hτ0 : 0 ≤ τ) (hτh : τ ≤ u_hi) (hb : |b| ≤ V) (hb' : |b'| ≤ V) (ho : |b - b'| ≤ o) :
    Work.BoseBogFS.cellPhi τ b - Work.BoseBogFS.cellPhi τ b' ≤ o + Real.sqrt (2 * o * u_hi) := by
  have ho0 : 0 ≤ o := le_trans (abs_nonneg (b - b')) ho
  have hb'b : b' - b ≤ o := by have h := (abs_le.mp ho).1; linarith
  have hdec : cellPhi τ b - cellPhi τ b'
      = (b - b') + (Real.sqrt (τ ^ 2 + 2 * τ * b') - Real.sqrt (τ ^ 2 + 2 * τ * b)) := by
    have h1 : cellPhi τ b = τ + b - Real.sqrt (τ ^ 2 + 2 * τ * b) := rfl
    have h2 : cellPhi τ b' = τ + b' - Real.sqrt (τ ^ 2 + 2 * τ * b') := rfl
    rw [h1, h2]; ring
  rcases le_total b b' with hbb | hbb
  · -- `b ≤ b'`: the only case in which the square-root term can hurt
    have hd : 0 ≤ b' - b := sub_nonneg.mpr hbb
    have hAB : τ ^ 2 + 2 * τ * b ≤ τ ^ 2 + 2 * τ * b' := by nlinarith
    have hle : Real.sqrt (τ ^ 2 + 2 * τ * b') - Real.sqrt (τ ^ 2 + 2 * τ * b)
        ≤ Real.sqrt (2 * τ * (b' - b)) := by
      have h := sqrt_sub_sqrt_le_sqrt_sub hAB
      have hBA : τ ^ 2 + 2 * τ * b' - (τ ^ 2 + 2 * τ * b) = 2 * τ * (b' - b) := by ring
      rwa [hBA] at h
    have hrad : (2:ℝ) * τ * (b' - b) ≤ 2 * o * u_hi := by
      have h1 : τ * (b' - b) ≤ u_hi * o :=
        mul_le_mul hτh hb'b hd (le_trans hτ0 hτh)
      linarith
    have h3 : Real.sqrt (2 * τ * (b' - b)) ≤ Real.sqrt (2 * o * u_hi) := Real.sqrt_le_sqrt hrad
    calc cellPhi τ b - cellPhi τ b'
        = (b - b') + (Real.sqrt (τ ^ 2 + 2 * τ * b') - Real.sqrt (τ ^ 2 + 2 * τ * b)) := hdec
      _ ≤ (b - b') + Real.sqrt (2 * τ * (b' - b)) := by linarith
      _ ≤ o + Real.sqrt (2 * o * u_hi) := by
            have : b - b' ≤ 0 := by linarith
            linarith
  · -- `b' ≤ b`: the square-root term is non-positive
    have hAB : τ ^ 2 + 2 * τ * b' ≤ τ ^ 2 + 2 * τ * b := by nlinarith
    have hle : Real.sqrt (τ ^ 2 + 2 * τ * b') ≤ Real.sqrt (τ ^ 2 + 2 * τ * b) :=
      Real.sqrt_le_sqrt hAB
    have hbb' : b - b' ≤ o := (abs_le.mp ho).2
    calc cellPhi τ b - cellPhi τ b'
        = (b - b') + (Real.sqrt (τ ^ 2 + 2 * τ * b') - Real.sqrt (τ ^ 2 + 2 * τ * b)) := hdec
      _ ≤ (b - b') + 0 := by linarith
      _ = b - b' := by ring
      _ ≤ o := hbb'
      _ ≤ o + Real.sqrt (2 * o * u_hi) := by
            have : 0 ≤ Real.sqrt (2 * o * u_hi) := Real.sqrt_nonneg _
            linarith

end Work.BoseBogFS
