import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.SliceBadAux
import Submission.Work.BoseBoxFock.SlotProjDefs
import Submission.Work.BoseBoxFock.integrableOn_aPC_aPC
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.aPC_finsetSum_ae` — the slot mean is finitely additive

The slot mean `aPC ℓ i Ψ x = ℓ⁻³ ∫_{acube ℓ} Ψ (x[i↦y]) dy` is a Bochner integral of a
*slice* of the state, so its linearity in the state is the finite additivity of the Bochner
integral — but that additivity (`MeasureTheory.integral_finsetSum`) carries an integrability
hypothesis on *each* summand, and the integrability of the slice `y ↦ Ψ (x[i↦y])` is only an
almost-everywhere statement about `x` (a.e. boundedness of `Ψ` says nothing about a single
line *a priori*).

The argument therefore proceeds through bounded measurable representatives, where the
additivity is pointwise:

* `exists_bdd_sm_repr` — an `L^∞` complex function has a **strongly measurable, everywhere
  bounded** representative `g` (`f =ᵐ[μ] g`): take a measurable representative of `f` and cut
  it by the indicator of `{‖·‖ ≤ C}` for an a.e. bound `C`;
* the finite sum of the representatives is again everywhere bounded and strongly measurable,
  so **every** slice `y ↦ (Σ_k g k) (x[i↦y])` is integrable on the finite-measure box
  `acube ℓ` (boundedness + `IntegrableOn.of_bound`), and
  `MeasureTheory.integral_finsetSum` gives the additivity of `aPC` *pointwise*;
* a.e. equalities are transported along the finite sum (`Finset.eventually_all`) and through
  `aPC` (`ae_aPC_congr_vol`, which needs the a.e. equality w.r.t. the *full* Lebesgue
  measure, not only its restriction to the box).

Everything is `sorry`-free; the auxiliary lemmas live in
`Submission/Work/BoseBoxFock/integrableOn_aPC_aPC.lean` (`exists_ae_bound_of_memLp_top_gen`,
`ae_aPC_congr_vol`) and `Submission/Work/BoseBoxFock/cIPn_sum_aPC_re.lean`
(`norm_aPC_le`, `aPC_aestronglyMeasurable_of_stronglyMeasurable`).
-/

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators
open Work.BoseDict

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "Sp" => EuclideanSpace ℝ (Fin 3)

/-- **An `L^∞` complex function has an everywhere bounded strongly measurable
representative.**  Given `MemLp f ⊤ μ`, the measurable representative of `f` cut by the
indicator of the a.e. bound set `{x | ‖·‖ ≤ C}` is everywhere bounded by `C`, strongly
measurable, and still a.e. equal to `f`. -/
theorem exists_bdd_sm_repr {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℂ}
    (hf : MemLp f (⊤ : ENNReal) μ) :
    ∃ (g : α → ℂ) (C : ℝ), 0 ≤ C ∧ (∀ x, ‖g x‖ ≤ C) ∧ StronglyMeasurable g ∧ f =ᵐ[μ] g := by
  obtain ⟨C, hCnn, hCb⟩ := exists_ae_bound_of_memLp_top_gen hf
  have hAESM : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  set g₀ : α → ℂ := hAESM.mk f with hg₀def
  have hg₀sm : StronglyMeasurable g₀ := hAESM.stronglyMeasurable_mk
  have hg₀eq : f =ᵐ[μ] g₀ := hAESM.ae_eq_mk
  have hCb' : ∀ᵐ x ∂μ, ‖g₀ x‖ ≤ C := by
    filter_upwards [hCb, hg₀eq] with x hx hx0
    rwa [← hx0]
  have hset : MeasurableSet {x : α | ‖g₀ x‖ ≤ C} :=
    measurableSet_le hg₀sm.measurable.norm measurable_const
  refine ⟨{x : α | ‖g₀ x‖ ≤ C}.indicator g₀, C, hCnn, ?_, hg₀sm.indicator hset, ?_⟩
  · intro x
    by_cases hx : x ∈ {x : α | ‖g₀ x‖ ≤ C}
    · rw [Set.indicator_of_mem hx]; exact hx
    · rw [Set.indicator_of_notMem hx]; simpa using hCnn
  · refine hg₀eq.trans ?_
    filter_upwards [hCb'] with x hx
    exact (Set.indicator_of_mem (show x ∈ {x : α | ‖g₀ x‖ ≤ C} from hx) g₀).symm

theorem aPC_finsetSum_ae (ℓ : ℝ) (hℓ : 0 < ℓ) {N : ℕ} (i : Fin N) {ι : Type*}
    (s : Finset ι) {Θ : ι → (Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hΘ : ∀ k ∈ s, MeasureTheory.MemLp (Θ k) ⊤) :
    (fun x => Work.BoseBoxFock.aPC ℓ i (fun y => ∑ k ∈ s, Θ k y) x)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (Fin N → EuclideanSpace ℝ (Fin 3)))]
      (fun x => ∑ k ∈ s, Work.BoseBoxFock.aPC ℓ i (Θ k) x) := by
  have hN : N ≠ 0 := by rintro rfl; exact i.elim0
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  -- an everywhere bounded strongly measurable representative of every summand
  have key : ∀ k : ι, ∃ (g : Xn (m + 1) → ℂ) (C : ℝ), 0 ≤ C ∧ (∀ x, ‖g x‖ ≤ C) ∧
      StronglyMeasurable g ∧ (k ∈ s → Θ k =ᵐ[(volume : Measure (Xn (m + 1)))] g) := by
    intro k
    by_cases hk : k ∈ s
    · obtain ⟨g, C, hCnn, hgbd, hgsm, hgeq⟩ :=
        exists_bdd_sm_repr (volume : Measure (Xn (m + 1))) (hΘ k hk)
      exact ⟨g, C, hCnn, hgbd, hgsm, fun _ => hgeq⟩
    · exact ⟨fun _ => (0 : ℂ), 0, le_rfl, fun x => by simp, stronglyMeasurable_const,
        fun hk' => absurd hk' hk⟩
  choose g C hCnn hgbd hgsm hgΘ using key
  -- the finite sum is a.e. equal to the finite sum of the representatives
  have hsum : (fun x : Xn (m + 1) => ∑ k ∈ s, Θ k x)
      =ᵐ[(volume : Measure (Xn (m + 1)))] (fun x => ∑ k ∈ s, g k x) := by
    filter_upwards [(Finset.eventually_all (l := ae (volume : Measure (Xn (m + 1)))) s
      (p := fun k x => Θ k x = g k x)).2 (fun k hk => hgΘ k hk)] with x hx
    exact Finset.sum_congr rfl (fun k hk => hx k hk)
  -- on the representatives `aPC` is additive *pointwise*: every slice is bounded
  have hpoint : (fun x : Xn (m + 1) => aPC ℓ i (fun y => ∑ k ∈ s, g k y) x)
      = (fun x => ∑ k ∈ s, aPC ℓ i (g k) x) := by
    funext x
    have hint : ∀ k ∈ s, Integrable (fun y : Sp => g k (Function.update x i y))
        ((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ)) := by
      intro k _
      have hmeas : AEStronglyMeasurable (fun y : Sp => g k (Function.update x i y))
          ((volume : Measure Sp).restrict (Submission.BoseGases.acube ℓ)) :=
        ((hgsm k).measurable.comp (by fun_prop : Measurable
          fun y : Sp => Function.update x i y)).aestronglyMeasurable
      exact IntegrableOn.of_bound (Submission.BoseGases.acube_lt_top ℓ hℓ.le) hmeas (C k)
        (ae_of_all _ fun y => hgbd k _)
    unfold aPC
    rw [MeasureTheory.integral_finsetSum s hint, Finset.mul_sum]
  refine Filter.EventuallyEq.trans (ae_aPC_congr_vol (ℓ := ℓ) i hsum) ?_
  refine (Filter.EventuallyEq.of_eq hpoint).trans ?_
  filter_upwards [(Finset.eventually_all (l := ae (volume : Measure (Xn (m + 1)))) s
    (p := fun k x => aPC ℓ i (g k) x = aPC ℓ i (Θ k) x)).2
    (fun k hk => ae_aPC_congr_vol (ℓ := ℓ) i (hgΘ k hk).symm)] with x hx
  exact Finset.sum_congr rfl (fun k hk => hx k hk)

end Work.BoseBoxFock
