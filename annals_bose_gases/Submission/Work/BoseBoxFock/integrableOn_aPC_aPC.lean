import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.cIPn_sum_aPC_re
import Submission.Work.BoseBoxFock.uSlot_regular
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.integrableOn_aPC_aPC`

The `L²`-regularity of the *iterated* slot mean.  If `Θ : Xn (n+2) → ℂ` is a.e. bounded
(`MemLp Θ ⊤`) with support inside the box `abox (n+2) ℓ`, then for every pair of slots
`i j` the function `x ↦ ‖aPC ℓ i (aPC ℓ j Θ) x‖²` is integrable on the box.

The mathematics is the observation that both `aPC` and its iterates only depend on the state
through its values on slices, so an a.e. bounded *measurable representative* `g'` of `Θ`
(bounded everywhere, supported in the box) produces *pointwise equal* iterated slot means up
to a null set.  More precisely:

* `Θ =ᵐ[volume] g'` (the a.e. equality only holds on the box for `Θ`, but `g'` is supported
  in the box and `Θ` is too, so they agree *pointwise* off the box);
* the slices `z ↦ Θ (x[i ↦ z])` and `z ↦ g' (x[i ↦ z])` agree `(volume × volume)`-a.e., hence
  the slot means agree volume-a.e. (`ae_aPC_congr_vol`), and applying the argument twice gives
  `aPC ℓ i (aPC ℓ j Θ) =ᵐ aPC ℓ i (aPC ℓ j g')`;
* `aPC ℓ i (aPC ℓ j g')` is *everywhere* bounded by `C` (`norm_aPC_le`, twice) and the
  iterated means of an everywhere bounded strongly measurable state are a.e. strongly
  measurable (`aPC_aestronglyMeasurable_of_stronglyMeasurable` + `aPC_aesm_aux`).

The result then follows from `IntegrableOn.of_bound` plus transfer along the a.e. equality.

This also covers the `L²`-integrability of the excitation count `cnPlusC` for states that are
`L^∞` only, which is the form in which the box ↔ model dictionary consumes `aPC`.
-/

noncomputable section

open MeasureTheory
open scoped Topology BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.BoseDict

/-! ## 1. An a.e. bound out of an `L^∞` hypothesis -/

/-- An `L^∞`-function for an arbitrary measure is a.e. bounded by a nonnegative constant.
(Generalises `exists_ae_bound_of_memLp_top_xn` to an arbitrary measure, which is what the
box-restricted `MemLp` hypothesis of the target provides.) -/
theorem exists_ae_bound_of_memLp_top_gen {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : MemLp f (⊤ : ENNReal) μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂μ, ‖f x‖ ≤ C := by
  have h1 : eLpNormEssSup f μ < ⊤ := by
    rw [← eLpNorm_exponent_top hf.aestronglyMeasurable]; exact hf.eLpNorm_lt_top
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp h1
  rw [Filter.eventually_map] at hC
  exact ⟨C, C.coe_nonneg, Filter.Eventually.mono hC fun x hx => by exact_mod_cast hx⟩

/-! ## 2. Null sets and the slice map -/

/-- A.e. equality of two states propagates to their slices, for the *full* Lebesgue measure
(not only its restriction to the box): the set of pairs `(x,z)` with
`Θ (x[i↦z]) ≠ g (x[i↦z])` is null for the product measure. -/
theorem ae_update_eq_of_ae_eq_vol {m : ℕ} (j : Fin (m + 1)) {Θ g : Xn (m + 1) → ℂ}
    (h : Θ =ᵐ[(volume : Measure (Xn (m + 1)))] g) :
    ∀ᵐ x ∂(volume : Measure (Xn (m + 1))), ∀ᵐ y ∂(volume : Measure Sp),
      Θ (Function.update x j y) = g (Function.update x j y) := by
  have hD : (volume : Measure (Xn (m + 1))) {x | ¬ (Θ x = g x)} = 0 := ae_iff.mp h
  obtain ⟨D', hsub, hD'm, hD'0⟩ := exists_measurable_superset_of_null hD
  have hprod : ((volume : Measure (Xn (m + 1))).prod (volume : Measure Sp))
      {p : Xn (m + 1) × Sp | Function.update p.1 j p.2 ∈ D'} = 0 :=
    prod_update_preimage_null j hD'm hD'0
  have hae : ∀ᵐ p ∂((volume : Measure (Xn (m + 1))).prod (volume : Measure Sp)),
      ¬ (Function.update p.1 j p.2 ∈ D') := by
    rw [ae_iff]; simpa using hprod
  have h2 := Measure.ae_ae_of_ae_prod hae
  filter_upwards [h2] with x hx
  filter_upwards [hx] with y hy
  by_contra hcon
  exact hy (hsub hcon)

/-- A.e. equality of states lifts to a.e. equality of their slot means, for the full
Lebesgue measure. -/
theorem ae_aPC_congr_vol {m : ℕ} {ℓ : ℝ} (j : Fin (m + 1)) {Θ g : Xn (m + 1) → ℂ}
    (h : Θ =ᵐ[(volume : Measure (Xn (m + 1)))] g) :
    aPC ℓ j Θ =ᵐ[(volume : Measure (Xn (m + 1)))] aPC ℓ j g := by
  filter_upwards [ae_update_eq_of_ae_eq_vol j h] with x hx
  unfold aPC
  congr 1
  exact MeasureTheory.integral_congr_ae (MeasureTheory.ae_mono Measure.restrict_le_self hx)

/-! ## 3. The target -/

theorem integrableOn_aPC_aPC {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Θ : Work.BoseDict.Xn (n + 2) → ℂ}
    (hsupp : Function.support Θ ⊆ Submission.BoseGases.abox (n + 2) ℓ)
    (hint : MeasureTheory.MemLp Θ ⊤
      ((MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn (n + 2))).restrict
        (Submission.BoseGases.abox (n + 2) ℓ)))
    (i j : Fin (n + 2)) :
    MeasureTheory.IntegrableOn
      (fun x : Work.BoseDict.Xn (n + 2) =>
        ‖Work.BoseBoxFock.aPC ℓ i (Work.BoseBoxFock.aPC ℓ j Θ) x‖ ^ 2)
      (Submission.BoseGases.abox (n + 2) ℓ) MeasureTheory.volume := by
  set B : Set (Xn (n + 2)) := Submission.BoseGases.abox (n + 2) ℓ with hB
  set ν : Measure (Xn (n + 2)) := (volume : Measure (Xn (n + 2))).restrict B with hν
  have hB_meas : MeasurableSet B := Submission.BoseGases.abox_measurable (n + 2) ℓ
  have hB_lt : (volume : Measure (Xn (n + 2))) B < ⊤ :=
    Submission.BoseGases.abox_lt_top (n + 2) ℓ hℓ.le
  -- ## an a.e. bound and a bounded strongly measurable representative of `Θ`
  obtain ⟨C₀, hC₀nn, hC₀⟩ := exists_ae_bound_of_memLp_top_gen hint
  have hAESM : AEStronglyMeasurable Θ ν := hint.aestronglyMeasurable
  set g : Xn (n + 2) → ℂ := hAESM.mk Θ with hgdef
  have hg_sm : StronglyMeasurable g := hAESM.stronglyMeasurable_mk
  have hg_eq : Θ =ᵐ[ν] g := hAESM.ae_eq_mk
  have hgC : ∀ᵐ x ∂ν, ‖g x‖ ≤ C₀ := by
    filter_upwards [hC₀, hg_eq] with x h1 h2
    rw [← h2]; exact h1
  -- ## the everywhere bounded, box-supported representative `g'`
  set g' : Xn (n + 2) → ℂ := {x | x ∈ B ∧ ‖g x‖ ≤ C₀}.indicator g with hg'def
  have hset_meas : MeasurableSet {x : Xn (n + 2) | x ∈ B ∧ ‖g x‖ ≤ C₀} :=
    hB_meas.inter
      (measurableSet_le (continuous_norm.measurable.comp hg_sm.measurable) measurable_const)
  have hg'_sm : StronglyMeasurable g' := hg_sm.indicator hset_meas
  have hg'_bound : ∀ x, ‖g' x‖ ≤ C₀ := by
    intro x
    by_cases hx : x ∈ {x : Xn (n + 2) | x ∈ B ∧ ‖g x‖ ≤ C₀}
    · rw [hg'def, Set.indicator_of_mem hx]
      exact hx.2
    · rw [hg'def, Set.indicator_of_notMem hx]
      simpa using hC₀nn
  have hg'_supp : Function.support g' ⊆ B := by
    intro x hx
    by_contra hcon
    exact hx (by
      rw [hg'def, Set.indicator_of_notMem
        (fun h : x ∈ {x : Xn (n + 2) | x ∈ B ∧ ‖g x‖ ≤ C₀} => hcon h.1)])
  have hg'_eq : g' =ᵐ[ν] g := by
    filter_upwards [hgC, self_mem_ae_restrict hB_meas] with x hx hxB
    rw [hg'def,
      Set.indicator_of_mem (show x ∈ {x : Xn (n + 2) | x ∈ B ∧ ‖g x‖ ≤ C₀} from ⟨hxB, hx⟩)]
  have hΘg' : Θ =ᵐ[ν] g' := hg_eq.trans hg'_eq.symm
  -- ## transport the a.e. equality from the box to the full volume
  have hΘg'vol : Θ =ᵐ[(volume : Measure (Xn (n + 2)))] g' := by
    have h1 : ∀ᵐ x ∂(volume : Measure (Xn (n + 2))), x ∈ B → Θ x = g' x :=
      (ae_restrict_iff' hB_meas).mp hΘg'
    filter_upwards [h1] with x hx
    by_cases hmem : x ∈ B
    · exact hx hmem
    · have hz1 : Θ x = 0 := by
        by_contra hne; exact hmem (hsupp hne)
      have hz2 : g' x = 0 := by
        by_contra hne; exact hmem (hg'_supp hne)
      rw [hz1, hz2]
  -- ## the iterated slot means agree a.e.
  have hj_eq : aPC ℓ j Θ =ᵐ[(volume : Measure (Xn (n + 2)))] aPC ℓ j g' :=
    ae_aPC_congr_vol j hΘg'vol
  have hi_eq : aPC ℓ i (aPC ℓ j Θ)
      =ᵐ[(volume : Measure (Xn (n + 2)))] aPC ℓ i (aPC ℓ j g') :=
    ae_aPC_congr_vol i hj_eq
  -- ## the proxy function `x ↦ ‖aPC ℓ i (aPC ℓ j g') x‖²` is integrable
  have hbnd : ∀ x, ‖aPC ℓ i (aPC ℓ j g') x‖ ≤ C₀ :=
    norm_aPC_le hℓ i hC₀nn (norm_aPC_le hℓ j hC₀nn hg'_bound)
  have hAESM₁ : AEStronglyMeasurable (aPC ℓ j g') (volume : Measure (Xn (n + 2))) :=
    aPC_aestronglyMeasurable_of_stronglyMeasurable j hg'_sm
  have hAESM₂ : AEStronglyMeasurable (aPC ℓ i (aPC ℓ j g')) (volume.restrict B) :=
    aPC_aesm_aux (ℓ := ℓ) i hAESM₁
  have hInt_proxy : IntegrableOn (fun x => ‖aPC ℓ i (aPC ℓ j g') x‖ ^ 2) B volume := by
    refine IntegrableOn.of_bound (f := fun x => ‖aPC ℓ i (aPC ℓ j g') x‖ ^ 2) hB_lt
      (hAESM₂.norm.pow 2) (C₀ * C₀) ?_
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    simpa [pow_two] using mul_self_le_mul_self (norm_nonneg _) (hbnd x)
  -- ## transfer along the a.e. equality
  refine hInt_proxy.congr_fun_ae ?_
  filter_upwards [MeasureTheory.ae_mono Measure.restrict_le_self hi_eq] with x hx
  rw [hx]

end Work.BoseBoxFock
