import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.PairGc21Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairGc21_continuous` — continuity of the clean `pairG21` fibre

The clean fibre of `Work.BoseBoxFock.pairGCore` is the set integral

    pairGc21 ℓ p hp Θ₀ A u y
      = ∫ z in triBox ℓ p, star (Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)) * A z.1.1 * A z.1.2
          * Θ₀ (insertCoord2 p y u z.2)

The dependence on `(u,y)` sits **only** in the last factor, which is the smooth state evaluated at
the configuration `insertCoord2 p y u z.2`; that map is continuous in `(u,y)` for every fixed `z`.
The remaining factor depends on `z` only, and is merely *measurable* (the kernel `A` is only assumed
measurable and bounded, not continuous).  So the parametric-integral lemma one needs is the one
where the integrand is a bounded measurable function times a jointly continuous one — that is the
general lemma `continuous_setIntegral_mul_of_bounded` proved below (dominated convergence, with the
dominating constant obtained from the uniform continuity of the continuous factor on the product of
a neighbourhood of the parameter and the (compact) box).

`sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped Topology

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn

/-- `BorelSpace` implies `OpensMeasurableSpace` (Mathlib registers the opposite direction only
under a second countability assumption). -/
local instance instOpensMeasurableSpaceOfBorelSpace' {α : Type*} [TopologicalSpace α]
    [MeasurableSpace α] [BorelSpace α] : OpensMeasurableSpace α :=
  ⟨by rw [← BorelSpace.measurable_eq]⟩

/-! ## 1. The parametric-integral lemma -/

/-- **Continuity of a parametric integral with a bounded measurable multiplier.**  For a compact
set `k`, a function `a` which is measurable and bounded by `Ca ≥ 0` on `k`, and a jointly continuous
`g : P → G → ℂ`, the function `p ↦ ∫ z in k, a z * g p z` is continuous.

The proof is dominated convergence: near a parameter `p₀` the continuous factor `g` is bounded by
`C₀ + 1` on `k` (uniform continuity on the compact `{p₀} × k` together with a bound of `g p₀` on
`k`), and `‖a‖` is bounded by `Ca` almost everywhere on `k`. -/
theorem continuous_setIntegral_mul_of_bounded
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [MeasureSpace G] [BorelSpace G]
    [IsFiniteMeasureOnCompacts (volume : Measure G)]
    {P : Type*} [TopologicalSpace P] [FirstCountableTopology P]
    {k : Set G} (hk : IsCompact k) {a : G → ℂ} {Ca : ℝ} (hCa : 0 ≤ Ca)
    (ha : AEStronglyMeasurable a ((volume : Measure G).restrict k))
    (hab : ∀ᵐ z ∂((volume : Measure G).restrict k), ‖a z‖ ≤ Ca)
    {g : P → G → ℂ} (hg : Continuous (Function.uncurry g)) :
    Continuous (fun p => ∫ z in k, a z * g p z) := by
  rw [continuous_iff_continuousAt]
  intro p₀
  have hgp₀ : Continuous (fun z : G => g p₀ z) :=
    hg.comp (((continuous_const : Continuous fun _ : G => p₀)).prodMk continuous_id)
  obtain ⟨V, hV, C, hC⟩ : ∃ V ∈ 𝓝 p₀, ∃ C : ℝ, ∀ p ∈ V, ∀ z ∈ k, ‖g p z‖ ≤ C := by
    obtain ⟨V, hV, hVu⟩ := hk.mem_uniformity_of_prod (s := Set.univ) (q := p₀) (f := g)
      (u := {z : ℂ × ℂ | dist z.1 z.2 < 1}) hg.continuousOn (Set.mem_univ p₀)
      (Metric.dist_mem_uniformity zero_lt_one)
    obtain ⟨C₀, hC₀⟩ := hk.exists_bound_of_continuousOn hgp₀.continuousOn
    refine ⟨V, by simpa using hV, C₀ + 1, fun p hp z hz => ?_⟩
    have h1 := hC₀ z hz
    have h2 : dist (g p z) (g p₀ z) < 1 := hVu p hp z hz
    rw [dist_eq_norm] at h2
    calc ‖g p z‖ = ‖g p₀ z + (g p z - g p₀ z)‖ := by congr 1; abel
      _ ≤ ‖g p₀ z‖ + ‖g p z - g p₀ z‖ := norm_add_le _ _
      _ ≤ C₀ + 1 := by linarith
  refine MeasureTheory.continuousAt_of_dominated (F := fun p z => a z * g p z)
    (bound := fun _ => Ca * C) ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall (fun p => ha.mul
      ((hg.comp (((continuous_const : Continuous fun _ : G => p)).prodMk
        continuous_id)).aestronglyMeasurable))
  · filter_upwards [hV] with p hp
    filter_upwards [hab, ae_restrict_mem hk.measurableSet] with z hz1 hz2
    rw [norm_mul]
    exact mul_le_mul hz1 (hC p hp z hz2) (norm_nonneg _) hCa
  · exact integrableOn_const hk.measure_lt_top.ne
  · filter_upwards with z
    exact ((hg.comp (continuous_id.prodMk
      (continuous_const : Continuous fun _ : P => z))).continuousAt).const_mul (a z)

/-! ## 2. The `z`-dependent factor of the `pairGc21` integrand -/

/-- The state/kernel factor of the `pairGc21` integrand: everything except the second configuration
`insertCoord2 p y u z.2`.  It depends on the integration variable `z` only. -/
noncomputable def pairGc21Factor {n : ℕ} (p : Fin n × Fin n) (Θ₀ : Xn n → ℂ) (A : E3 → ℂ)
    (z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) : ℂ :=
  star (Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)) * A z.1.1 * A z.1.2

/-! ## 3. Continuity of the fibre -/

theorem pairGc21_continuous {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (p : Fin n × Fin n) (hp : p.1 ≠ p.2)
    {Θ₀ : Work.BoseDict.Xn n → ℂ} {A : EuclideanSpace ℝ (Fin 3) → ℂ} {cA : ℝ}
    (hΘ₀ : ContDiff ℝ (⊤ : ℕ∞) Θ₀) (hA : Measurable A) (hAb : ∀ x, ‖A x‖ ≤ cA)
    (hcA : 0 ≤ cA) :
    Continuous (Function.uncurry (pairGc21 ℓ p hp Θ₀ A)) := by
  have hK : IsCompact (triBox ℓ p) := isCompact_triBox hℓ p
  -- bound on the state factor over the compact box
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn
    ((hΘ₀.continuous.comp (continuous_insertCoord2 p hp)).continuousOn)
  have hCa : (0 : ℝ) ≤ max M 0 * cA * cA :=
    mul_nonneg (mul_nonneg (le_max_right M 0) hcA) hcA
  -- measurability of the `z`-factor
  have ha : AEStronglyMeasurable (pairGc21Factor p Θ₀ A)
      ((volume : Measure ((E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3))).restrict
        (triBox ℓ p)) := by
    refine Measurable.aestronglyMeasurable ?_
    have h1 : Measurable (fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
        Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)) :=
      hΘ₀.continuous.measurable.comp (continuous_insertCoord2 p hp).measurable
    unfold pairGc21Factor
    exact ((continuous_star.measurable.comp h1).mul (hA.comp (continuous_fst.fst).measurable)).mul
      (hA.comp (continuous_fst.snd).measurable)
  -- the bound on the `z`-factor on the box
  have hab : ∀ᵐ z ∂((volume : Measure ((E3 × E3) ×
        ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3))).restrict (triBox ℓ p)),
      ‖pairGc21Factor p Θ₀ A z‖ ≤ max M 0 * cA * cA := by
    refine ae_restrict_of_forall_mem hK.measurableSet (fun z hz => ?_)
    unfold pairGc21Factor
    have hz1 : ‖Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)‖ ≤ max M 0 :=
      le_trans (hM z hz) (le_max_left M 0)
    calc ‖star (Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)) * A z.1.1 * A z.1.2‖
        = ‖Θ₀ (insertCoord2 p z.1.1 z.1.2 z.2)‖ * ‖A z.1.1‖ * ‖A z.1.2‖ := by
          rw [norm_mul, norm_mul, norm_star]
      _ ≤ max M 0 * cA * cA :=
          mul_le_mul (mul_le_mul hz1 (hAb _) (norm_nonneg _) (le_trans (norm_nonneg _) hz1))
            (hAb _) (norm_nonneg _) (mul_nonneg (le_max_right M 0) hcA)
  -- joint continuity of the `(u,y)`-dependent factor
  have hg : Continuous (Function.uncurry
      (fun x : E3 × E3 => fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
        Θ₀ (insertCoord2 p x.2 x.1 z.2))) := by
    show Continuous (fun q : (E3 × E3) × ((E3 × E3) ×
      ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3)) => Θ₀ (insertCoord2 p q.1.2 q.1.1 q.2.2))
    exact hΘ₀.continuous.comp ((continuous_insertCoord2 p hp).comp
      (((continuous_fst.snd).prodMk (continuous_fst.fst)).prodMk (continuous_snd.snd)))
  have hmain := continuous_setIntegral_mul_of_bounded (k := triBox ℓ p) hK
    (a := pairGc21Factor p Θ₀ A) (Ca := max M 0 * cA * cA) hCa ha hab
    (g := fun x : E3 × E3 => fun z : (E3 × E3) × ({k : Fin n // k ≠ p.1 ∧ k ≠ p.2} → E3) =>
      Θ₀ (insertCoord2 p x.2 x.1 z.2)) hg
  change Continuous (fun x : E3 × E3 => ∫ z in triBox ℓ p,
    pairGc21Factor p Θ₀ A z * Θ₀ (insertCoord2 p x.2 x.1 z.2))
  exact hmain

end Work.BoseBoxFock
