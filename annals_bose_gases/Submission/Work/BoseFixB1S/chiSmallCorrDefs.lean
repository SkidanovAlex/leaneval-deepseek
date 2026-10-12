import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.DLSmallKernels
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.chiSmallCorrDefs` — the one-dimensional tensor split of `chiSmall`

The cosine bump `Submission.BoseGases.chiSmall M` is a product of three copies of a
single 1-D profile,

    chiSmall M y = ∏ j, gM M (y_j),      gM M u := ζ(u)^M / √(∫_ℝ ζ^{2M}),

where `ζ = Submission.BoseGases.zeta1d` is `cos (π u)` on `|u| ≤ 1/2` and `0` outside.
This module records the 1-D profile `gM` and its normalising constant `zetaMassM`
(the number `∫ ζ^{2M}`), together with the elementary pointwise facts about them, so
that the localisation estimates about `chiSmall` can be stated and proved
coordinatewise.

## The facts assembled here

* `zetaMassM_pos` : `0 < ∫ ζ^{2M}`;
* `zeta1d_abs_antitone` : `ζ` is nonincreasing in `|·|`;
* `gM_nonneg`, `gM_even`, `gM_eq_zero_of_one_half_lt`, `gM_continuous`,
  `gM_mono_abs` (nonincreasing in `|·|`), `gM_sq_integral` (`∫ g² = 1`).

## The two consumers (their statements are NOT here)

* `Work.BoseFixB1S.chiSmallCorr1D` — the 1-D correlation inequality: for `|s| ≤ 1/16`,
  `0 < t ≤ T`, `t ≤ 1/2`,

      (t/T) * (∫_{[-T,T]} g²) * (∫_ℝ g(u+s/2) g(u−s/2) du)
        ≤ ∫_{[-t,t]} g(u+s/2) g(u−s/2) du .

  Proof route. Write `f(u) := g(u+s/2)·g(u−s/2)` (nonnegative, even, supported in
  `[−1/2,1/2]` as soon as `|s| ≤ 1`) and `F(t) := ∫_{[-t,t]} f`, `K(T) := ∫_{[-T,T]} g²`.
  Two inputs, both from `ζ = cos (π·)` on `[−1/2,1/2]`:

  (i) `f` is nonincreasing on `[0,∞)`.  For `s ≥ 0` and `0 ≤ u ≤ 1/2 − s/2` one has
      `f(u) = ((cos (2πu) + cos (πs))/2)^M / Z` (product-to-sum `Real.cos_add`,
      `Real.cos_sub`), which is nonincreasing in `u`; for `u > 1/2 − s/2`,
      `f(u) = 0`.  Hence `2t f(t) ≤ F(t)` and `F(T) ≤ F(t) + 2(T−t) f(t) ≤
      F(t)·T/t` for `0 < t ≤ T`: that is `I(t) ≥ (t/T) I(T)` — the **first 1-D
      inequality**, valid for all `t ≤ T ≤ 1/2`.

  (ii) `I(T) ≥ K(T)·I(∞)` for `T ≤ 1/2` (the **second 1-D inequality**).  Put
      `S := 1/2 − |s|/2`; on `[−S,S]` the exact identity
      `f(u) = g(u)²·R(u)`, `R(u) := (cos (2πu) + cos (πs))/(1 + cos (2πu))`, holds,
      while `R ≤ 0` off `[−S,S]` so `f ≥ g²R` everywhere.  `R` is nonincreasing in
      `|u|` and `R(S) = 0`.  Hence, with `A := K(T)`, `B := ∫_{T<|u|≤S} g²`
      (so `A + B ≤ ∫g² = 1`),
      `∫_S g²R ≤ A·R(T) + B·R(T)` and `∫_{[-T,T]} f ≥ R(T)·A`, so
      `A·I(∞) ≤ A R(T)(A+B) ≤ A R(T) ≤ ∫_{[-T,T]} f = I(T)`.
      (For `T ≥ S`, `I(T) = I(∞)` and `K(T) ≤ 1` give it too.)

  Assembly: if `T ≤ 1/2`, (ii) then (i) gives `(t/T)K(T)I(∞) ≤ (t/T)I(T) ≤ I(t)`.
  If `T ≥ 1/2` then `K(T) = 1`, `I(1/2) = I(∞)` and (i) at `T = 1/2` gives
  `I(t) ≥ 2t I(∞) ≥ (t/T)I(∞) = (t/T)K(T)I(∞)` (using `t ≤ 1/2 ≤ T`).

* `Work.BoseFixB1S.chiSmallCorr3D` — the Fubini assembly: `chiSmall M = ⊗³ gM`,
  `conv3Small M s = ∏_j ∫_ℝ gM(u+s_j/2) gM(u−s_j/2) du`, so multiplying the three
  per-coordinate inequalities `h1D` gives the box-integral bound.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1S

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The 1-D normalising mass `Z M = ∫_ℝ ζ(u)^{2M} du` of the cosine profile `ζ = zeta1d`
(equal to `(2M choose M)/4^M`, but only positivity and the definition are used). -/
noncomputable def zetaMassM (M : ℕ) : ℝ := ∫ u : ℝ, (zeta1d u) ^ (2 * M)

lemma zetaMassM_def (M : ℕ) :
    zetaMassM M = ∫ u : ℝ, (zeta1d u) ^ (2 * M) := rfl

/-- The 1-D profile of which `chiSmall M` is the threefold tensor product:
`gM M u = ζ(u)^M / √(Z M)`.  It is nonnegative, even, supported in `[-1/2,1/2]` and
`∫_ℝ (gM M u)^2 du = 1`. -/
noncomputable def gM (M : ℕ) : ℝ → ℝ :=
  fun u => (zeta1d u) ^ M / Real.sqrt (zetaMassM M)

lemma gM_def (M : ℕ) (u : ℝ) :
    gM M u = (zeta1d u) ^ M / Real.sqrt (zetaMassM M) := rfl

/-- **`ζ` is nonincreasing in `|·|`**: for `|u| ≤ |v|`, `ζ v ≤ ζ u`. -/
lemma zeta1d_abs_antitone {u v : ℝ} (h : |u| ≤ |v|) : zeta1d v ≤ zeta1d u := by
  by_cases hv : |v| ≤ 1 / 2
  · have hu : |u| ≤ 1 / 2 := le_trans h hv
    have hv' : zeta1d v = Real.cos (Real.pi * |v|) := by
      rw [zeta1d_of_abs_le hv, cos_pi_mul_eq_cos_pi_abs]
    have hu' : zeta1d u = Real.cos (Real.pi * |u|) := by
      rw [zeta1d_of_abs_le hu, cos_pi_mul_eq_cos_pi_abs]
    rw [hv', hu']
    have h1 : (0 : ℝ) ≤ Real.pi * |u| := by positivity
    have h2 : Real.pi * |v| ≤ Real.pi := by nlinarith [Real.pi_pos, hv]
    have h3 : Real.pi * |u| ≤ Real.pi * |v| := by nlinarith [Real.pi_pos, h]
    exact Real.cos_le_cos_of_nonneg_of_le_pi h1 h2 h3
  · have hv' : 1 / 2 < |v| := lt_of_not_ge hv
    rw [zeta1d_of_one_half_lt hv']
    exact zeta1d_nonneg u

/-- `ζ` has compact support (it vanishes off the closed unit cell `[-1/2,1/2]`). -/
lemma zeta1d_hasCompactSupport : HasCompactSupport zeta1d := by
  change IsCompact (tsupport zeta1d)
  change IsCompact (closure (Function.support zeta1d))
  refine IsCompact.of_isClosed_subset (isCompact_Icc (a := (-1 / 2 : ℝ)) (b := 1 / 2))
    isClosed_closure ?_
  calc
    closure (Function.support zeta1d) ⊆ closure (Set.Icc (-1 / 2) (1 / 2)) := by
      apply closure_mono
      intro y hy
      rw [Set.mem_Icc]
      have h := zeta1d_ne_zero_abs_le (Function.mem_support.mp hy)
      exact ⟨by linarith [(abs_le.mp h).1], by linarith [(abs_le.mp h).2]⟩
    _ = Set.Icc (-1 / 2) (1 / 2) := closure_Icc _ _

/-- **Positivity of the 1-D normalisation** `Z M = ∫ ζ^{2M} > 0` (`M ≥ 1`). -/
lemma zetaMassM_pos {M : ℕ} (hM : 1 ≤ M) : 0 < zetaMassM M := by
  have h2M : 2 * M ≠ 0 := by omega
  dsimp [zetaMassM]
  refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero
    (f := fun u : ℝ => (zeta1d u) ^ (2 * M)) (x := 0)
    (zeta1d_continuous.pow _) ?_ (fun u => pow_nonneg (zeta1d_nonneg u) _) ?_
  · refine HasCompactSupport.mono zeta1d_hasCompactSupport ?_
    intro u hu
    rw [Function.mem_support] at hu ⊢
    intro hc
    exact hu (by rw [hc, zero_pow h2M])
  · rw [zeta1d_zero, one_pow]
    norm_num

lemma zetaMassM_ne_zero {M : ℕ} (hM : 1 ≤ M) : zetaMassM M ≠ 0 :=
  ne_of_gt (zetaMassM_pos hM)

lemma zetaMassM_nonneg (M : ℕ) : 0 ≤ zetaMassM M :=
  integral_nonneg (fun u => pow_nonneg (zeta1d_nonneg u) _)

lemma sqrt_zetaMassM_pos {M : ℕ} (hM : 1 ≤ M) : 0 < Real.sqrt (zetaMassM M) :=
  Real.sqrt_pos.mpr (zetaMassM_pos hM)

lemma sqrt_zetaMassM_ne_zero {M : ℕ} (hM : 1 ≤ M) : Real.sqrt (zetaMassM M) ≠ 0 :=
  ne_of_gt (sqrt_zetaMassM_pos hM)

lemma gM_nonneg (M : ℕ) (u : ℝ) : 0 ≤ gM M u :=
  div_nonneg (pow_nonneg (zeta1d_nonneg u) _) (Real.sqrt_nonneg _)

lemma gM_even (M : ℕ) (u : ℝ) : gM M (-u) = gM M u := by
  rw [gM_def, gM_def, zeta1d_neg]

lemma gM_eq_zero_of_one_half_lt {M : ℕ} (hM : 1 ≤ M) {u : ℝ} (h : 1 / 2 < |u|) :
    gM M u = 0 := by
  have hM0 : M ≠ 0 := by omega
  rw [gM_def, zeta1d_of_one_half_lt h, zero_pow hM0]
  simp

lemma gM_continuous (M : ℕ) : Continuous (gM M) :=
  (zeta1d_continuous.pow M).div_const _

lemma gM_hasCompactSupport {M : ℕ} (hM : 1 ≤ M) : HasCompactSupport (gM M) := by
  have hM0 : M ≠ 0 := by omega
  refine HasCompactSupport.mono zeta1d_hasCompactSupport ?_
  intro u hu
  rw [Function.mem_support] at hu ⊢
  intro hc
  exact hu (by rw [gM_def, hc, zero_pow hM0]; simp)

/-- **`gM` is nonincreasing in `|·|`.** -/
lemma gM_mono_abs (M : ℕ) {u v : ℝ} (h : |u| ≤ |v|) : gM M v ≤ gM M u := by
  rw [gM_def, gM_def]
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ (zeta1d_nonneg v) (zeta1d_abs_antitone h) M)
    (Real.sqrt_nonneg _)

lemma gM_zero (M : ℕ) : gM M 0 = 1 / Real.sqrt (zetaMassM M) := by
  rw [gM_def, zeta1d_zero, one_pow]

lemma gM_pos_zero {M : ℕ} (hM : 1 ≤ M) : 0 < gM M 0 := by
  rw [gM_zero]
  exact div_pos one_pos (sqrt_zetaMassM_pos hM)

/-- The 1-D normalisation `∫_ℝ (gM M u)^2 du = 1` (`M ≥ 1`; for `M = 0` the Lean
Bochner convention makes `zetaMassM 0 = 0` and the statement is false). -/
lemma gM_sq_integral {M : ℕ} (hM : 1 ≤ M) : ∫ u : ℝ, (gM M u) ^ 2 = 1 := by
  have hZ : 0 < zetaMassM M := zetaMassM_pos hM
  have hsq : (Real.sqrt (zetaMassM M)) ^ 2 = zetaMassM M := Real.sq_sqrt (le_of_lt hZ)
  calc
    (∫ u : ℝ, (gM M u) ^ 2)
        = ∫ u : ℝ, (zeta1d u) ^ (2 * M) / zetaMassM M := by
          apply integral_congr_ae
          exact ae_of_all _ (by
            intro u
            show (gM M u) ^ 2 = (zeta1d u) ^ (2 * M) / zetaMassM M
            rw [gM_def, div_pow, hsq, ← pow_mul, Nat.mul_comm M 2])
    _ = (∫ u : ℝ, (zeta1d u) ^ (2 * M)) / zetaMassM M := integral_div _ _
    _ = 1 := by
          rw [← zetaMassM_def]
          exact div_self (ne_of_gt hZ)

end Work.BoseFixB1S
