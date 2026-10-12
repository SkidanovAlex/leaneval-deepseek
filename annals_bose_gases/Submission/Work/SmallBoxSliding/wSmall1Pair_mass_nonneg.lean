import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.SmallBoxSliding.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Nonnegativity of the sliding one-body mass `∬ w_{1,B(u)}`

The a-priori remainder `R_Ψ` of FS step 4 carries the per-box weight
`∬ w_{1,B(u)} = ∫_x∫_y wSmall1Pair h M ℓ d u x y`, and `R_Ψ ≥ 0` needs that
weight to be nonnegative (`R_Psi_nonneg` takes it as the hypothesis `hker`).

Here we prove it unconditionally, from the sign structure of the corpus
building blocks:

* `chiSmallB M ℓ d u x = χ_M(x/ℓ)·χ_M(x/(ℓd) − u) ≥ 0` pointwise
  (`chiSmall_nonneg`);
* `convScaleSmall M (ℓd) z = (χ_M ⋆ χ_M)(z/(ℓd)) ≥ 0` pointwise (product of
  nonnegative factors, integrated);
* the numerator `g₀ v h = v·(1 − w₀)` is `≥ 0` almost everywhere
  (`g0_nonneg_ae`, FS: `v ≥ 0` and `w₀ ≤ 1` a.e.).

Since `wSmall1Pair h M ℓ d u x y = χ_{B(u)}(x)·(g₀(x−y)/conv(x−y))·χ_{B(u)}(y)`,
the double integrand is `≥ 0` a.e. — for the inner integral the a.e. statement
is transported along the measure-preserving reflection `y ↦ x − y` — and two
applications of `integral_nonneg_of_ae` finish.
-/

set_option linter.unusedVariables false

namespace Work.SmallBoxSliding

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open MeasureTheory

open Submission.BoseGases

/-- The small-box cutoff is nonnegative pointwise. -/
lemma chiSmallB_nonneg (M : ℕ) (ℓ d : ℝ) (u z : ℝ³) :
    0 ≤ chiSmallB M ℓ d u z := by
  simp only [chiSmallB]
  exact mul_nonneg (chiScale_nonneg ℓ z) (chiSmall_nonneg M _)

/-- The renormalisation denominator `(χ_M ⋆ χ_M)(z/(ℓd))` is nonnegative
pointwise. -/
lemma convScaleSmall_nonneg (M : ℕ) (c : ℝ) (z : ℝ³) :
    0 ≤ convScaleSmall M c z := by
  simp only [convScaleSmall, conv3Small]
  apply integral_nonneg
  intro w
  exact mul_nonneg (chiSmall_nonneg M w) (chiSmall_nonneg M _)

/-- The reflection `y ↦ x − y` preserves Lebesgue measure, so an a.e.
statement about `g` transfers to `g (x − ·)`. -/
lemma ae_g0_comp_sub {v : ℝ³ → ℝ} {Rv : ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) Rv) (hRv : 0 < Rv)
    (h : ∃ w : ℝ³ → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v) (x : ℝ³) :
    ∀ᵐ y : ℝ³, 0 ≤ g0 v h (x - y) := by
  have hmp : MeasurePreserving (fun y : ℝ³ => x - y) volume volume := by
    have h1 : (fun y : ℝ³ => x - y)
        = (fun z : ℝ³ => x + z) ∘ (fun y : ℝ³ => -y) := by
      funext y; simp [sub_eq_add_neg]
    rw [h1]
    exact (measurePreserving_add_left (volume : Measure ℝ³) x).comp
      (Measure.measurePreserving_neg (volume : Measure ℝ³))
  exact hmp.quasiMeasurePreserving.ae
    (g0_nonneg_ae hRv hv_nonneg hvrad hv_supp h)

lemma wSmall1Pair_mass_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {Rv : ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) Rv) (hRv : 0 < Rv)
    (h : ∃ w : EuclideanSpace ℝ (Fin 3) → ℝ, BoseGases.IsRadial w ∧ BoseGases.IsScatteringSolution w v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ ∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.wSmall1Pair h M ℓ d u x y := by
  -- inner integral is `0 ≤ · x` for every `x`
  have hinner : ∀ x : ℝ³, 0 ≤ ∫ y : ℝ³, wSmall1Pair h M ℓ d u x y := by
    intro x
    apply integral_nonneg_of_ae
    filter_upwards [ae_g0_comp_sub hv_nonneg hvrad hv_supp hRv h x] with y hy
    simp only [wSmall1Pair, wSmallPair, wSmallScaled]
    exact mul_nonneg
      (mul_nonneg (chiSmallB_nonneg M ℓ d u x)
        (div_nonneg (div_nonneg hy (convScaleSmall_nonneg M (ℓ * d) (x - y)))
          (convScale_nonneg ℓ (x - y))))
      (chiSmallB_nonneg M ℓ d u y)
  apply integral_nonneg_of_ae
  exact Filter.Eventually.of_forall hinner

end Work.SmallBoxSliding
