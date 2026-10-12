import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.slotProj_adjoint
import Submission.Work.BoseBoxFock.uSlot_regular

/-!
# `Work.BoseBoxFock.slotProj_finsetSum_ae` — the slot projection is finitely additive

`slotProj e U Ψ x = ∫ z, (∏_{i ∈ U} PV e (x i) (z i)) · Ψ (x with the slots of U replaced by z)`
(`SlotProjDefs`) is the Bochner integral of the fixed projection kernel against the state `Ψ`.
The target states that it is **finitely additive in the state**:

`slotProj e U (Σ_{k∈s} Θ k) =ᵐ[volume.restrict (abox N ℓ)] Σ_{k∈s} slotProj e U (Θ k)`,

where the modes carry `MemLp ⊤` bounds and are supported in the box `boxL ℓ`, while each summand
is only `MemLp ⊤` (so only a.e. bounded).

The proof has three parts, exactly parallel to the sibling `aPC_finsetSum_ae` for the slot mean.

* **`updateFinset_qmp`** — the insertion map `p ↦ Function.updateFinset p.1 U p.2` is
  quasi-measure-preserving.  It is the first component of the *measure preserving* automorphism
  `slotSwapMeas U` of `slotProj_adjoint` (`slotSwapMeas_fst`), hence a projection followed by a
  measure preserving equivalence.
* **`slotProj_ae_eq_congr`** — `slotProj e U` is insensitive to null modifications of its state:
  a null set pulls back to a null set of the product measure, and Fubini
  (`Measure.ae_ae_of_ae_prod`) turns that into "a.e. `z` for a.e. `x`", where the integrands
  agree a.e. (`integral_congr_ae`).  Note that this needs **no** hypothesis on the modes.
* **`integrable_slotKernel_finset` / `slotProj_finsetSum_bdd`** — for an *everywhere* bounded
  measurable state the identity holds **pointwise**: `MemLp ⊤` gives an a.e. bound on the modes,
  so for every fixed `x` the kernel `z ↦ ∏_{i∈U} PV e (x i) (z i)` is a.e. bounded and (by
  `hsupp`) pointwise supported in the compact set `(boxL ℓ)^{U}`; each summand is therefore
  integrable and `MeasureTheory.integral_finsetSum` applies.

The statement of the target is then obtained by replacing every `Θ k` by an everywhere bounded
strongly measurable representative (`exists_bdd_sm_repr_aux`), applying the pointwise identity to
the sum of the representatives, and transporting along the two a.e. equalities.
-/

noncomputable section

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. An a.e. bound out of an `L^∞` hypothesis -/

/-- An `L^∞` complex function is a.e. bounded by a nonnegative constant. -/
theorem exists_ae_bound_of_memLp_top_aux {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℂ} (hf : MemLp f (⊤ : ENNReal) μ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂μ, ‖f x‖ ≤ C := by
  have h1 : eLpNormEssSup f μ < ⊤ := by
    rw [← eLpNorm_exponent_top hf.aestronglyMeasurable]; exact hf.eLpNorm_lt_top
  obtain ⟨C, hC⟩ := eLpNormEssSup_lt_top_iff_isBoundedUnder.mp h1
  rw [Filter.eventually_map] at hC
  exact ⟨C, C.coe_nonneg, Filter.Eventually.mono hC fun x hx => by exact_mod_cast hx⟩

/-- **An `L^∞` complex function has an everywhere bounded strongly measurable representative.**
The measurable representative of `f` cut by the indicator of the a.e. bound set
`{x | ‖·‖ ≤ C}` is everywhere bounded by `C`, strongly measurable, and still a.e. equal to `f`. -/
theorem exists_bdd_sm_repr_aux {α : Type*} [MeasurableSpace α] (μ : Measure α) {f : α → ℂ}
    (hf : MemLp f (⊤ : ENNReal) μ) :
    ∃ (g : α → ℂ) (C : ℝ), 0 ≤ C ∧ (∀ x, ‖g x‖ ≤ C) ∧ StronglyMeasurable g ∧ f =ᵐ[μ] g := by
  obtain ⟨C, hCnn, hCb⟩ := exists_ae_bound_of_memLp_top_aux hf
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

/-! ## 2. The insertion map is quasi-measure-preserving -/

/-- **The insertion map `p ↦ Function.updateFinset p.1 U p.2` is quasi-measure-preserving.**
It is the first component of the measure preserving automorphism `slotSwapMeas U`
(`slotSwapMeas_fst`), i.e. `Prod.fst ∘ slotSwapMeas U`, and a projection of a product measure is
quasi-measure-preserving. -/
theorem updateFinset_qmp {N : ℕ} (U : Finset (Fin N)) :
    Measure.QuasiMeasurePreserving
      (fun p : (Fin N → Ω) × (↑U → Ω) => Function.updateFinset p.1 U p.2)
      (volume : Measure ((Fin N → Ω) × (↑U → Ω))) (volume : Measure (Fin N → Ω)) := by
  have h1 : (fun p : (Fin N → Ω) × (↑U → Ω) => Function.updateFinset p.1 U p.2)
      = Prod.fst ∘ (⇑(slotSwapMeas U)) := by
    funext p
    exact (slotSwapMeas_fst U p).symm
  rw [h1]
  exact Measure.quasiMeasurePreserving_fst.comp
    (measurePreserving_slotSwapMeas U).quasiMeasurePreserving

/-! ## 3. Insensitivity of the slot projection to null modifications -/

/-- **`slotProj e U` is insensitive to null modifications of the state** (for the full Lebesgue
measure on the configuration space).  No hypothesis on the modes is needed: the argument is
`integral_congr_ae` applied to the a.e. equality of the integrands, which follows from the fact
that a null set of configurations pulls back to a null set of the product measure along the
insertion map `updateFinset_qmp`, plus Fubini. -/
theorem slotProj_ae_eq_congr {m N : ℕ} (e : Fin m → Ω → ℂ) (U : Finset (Fin N))
    {f g : (Fin N → Ω) → ℂ} (h : f =ᵐ[(volume : Measure (Fin N → Ω))] g) :
    slotProj e U f =ᵐ[(volume : Measure (Fin N → Ω))] slotProj e U g := by
  have hae : ∀ᵐ p ∂(volume : Measure ((Fin N → Ω) × (↑U → Ω))),
      f (Function.updateFinset p.1 U p.2) = g (Function.updateFinset p.1 U p.2) :=
    (updateFinset_qmp U).ae h
  have hiter := Measure.ae_ae_of_ae_prod hae
  filter_upwards [hiter] with x hx
  rw [slotProj_eq_slotInt_fun e U f, slotProj_eq_slotInt_fun e U g]
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hx] with z hz
  rw [hz]

/-! ## 4. Integrability of the slot integrand -/

/-- **The slot integrand of an everywhere bounded measurable state is integrable.**

`MemLp ⊤` gives an a.e. bound on each mode, so for fixed `x` the kernel
`z ↦ ∏_{i ∈ U} PV e (x i.1) (z i)` is bounded a.e. (with an `x`-dependent constant), and `hsupp`
makes it vanish pointwise off the compact box `(boxL ℓ)^{U}` (a `PV`-factor vanishes as soon as its
fibre variable leaves `boxL ℓ`).  Bounded a.e. + supported in a finite measure set gives
integrability (`Integrable.mono'` against the indicator of the box). -/
theorem integrable_slotKernel_finset {m N : ℕ} {ℓ : ℝ} {B : Work.BoseB4.BoxData}
    (e : Fin m → Ω → ℂ) (U : Finset (Fin N))
    (hbdd : ∀ l, MemLp (e l) ⊤) (hsupp : ∀ l, Function.support (e l) ⊆ B.boxL ℓ)
    {x : Fin N → Ω} {G : (Fin N → Ω) → ℂ} (hGm : Measurable G) {C : ℝ}
    (hGb : ∀ w, ‖G w‖ ≤ C) :
    Integrable (fun z : (↑U → Ω) =>
      (∏ i : ↑U, PV e (x i.1) (z i)) * G (Function.updateFinset x U z))
      (volume : Measure (↑U → Ω)) := by
  classical
  choose Bl hBl0 hBl using fun l : Fin m => exists_ae_bound_of_memLp_top_aux (hbdd l)
  -- the a.e. bound, for every fibre coordinate at once
  have hcoord : ∀ᵐ z ∂(volume : Measure (↑U → Ω)), ∀ i : ↑U, ∀ l : Fin m, ‖e l (z i)‖ ≤ Bl l := by
    rw [volume_pi, Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro l
    rw [ae_iff]
    exact Measure.pi_eval_preimage_null (μ := fun _ : ↑U => (volume : Measure Ω))
      (ae_iff.mp (hBl l))
  -- the majorant (constant in `z`), pointwise supported in the compact box of finite volume
  set M : ℝ := ∏ i : ↑U, (∑ l : Fin m, ‖e l (x i.1)‖ * Bl l) with hMdef
  have hMnn : 0 ≤ M := by
    rw [hMdef]
    exact Finset.prod_nonneg
      (fun i _ => Finset.sum_nonneg (fun l _ => mul_nonneg (norm_nonneg _) (hBl0 l)))
  have hmaj : Integrable (fun z : ↑U → Ω =>
      (Set.univ.pi (fun _ : ↑U => B.boxL ℓ)).indicator (fun _ => M * C) z)
      (volume : Measure (↑U → Ω)) := by
    rw [integrable_indicator_iff
      (MeasurableSet.pi Set.countable_univ (fun _ _ => B.boxL_measurableSet ℓ))]
    refine integrableOn_const ?_ ?_
    · rw [volume_pi, Measure.pi_pi]
      exact ENNReal.prod_ne_top (fun i _ => by
        rw [← lt_top_iff_ne_top]; exact (B.boxL_compact ℓ).measure_lt_top)
    · exact enorm_ne_top
  -- a.e. strong measurability of the integrand
  have hmeas : AEStronglyMeasurable (fun z : ↑U → Ω =>
      (∏ i : ↑U, PV e (x i.1) (z i)) * G (Function.updateFinset x U z))
      (volume : Measure (↑U → Ω)) := by
    rw [aestronglyMeasurable_iff_aemeasurable, volume_pi]
    refine AEMeasurable.mul ?_ ?_
    · refine Finset.aemeasurable_fun_prod Finset.univ (fun i _ => ?_)
      have hsum : AEMeasurable (∑ l : Fin m, fun z : ↑U → Ω => e l (x i.1) * star (e l (z i)))
          (Measure.pi (fun _ : ↑U => (volume : Measure Ω))) := by
        refine Finset.aemeasurable_sum Finset.univ (fun l _ => ?_)
        have hstar : AEMeasurable (fun w : Ω => star (e l w)) (volume : Measure Ω) :=
          aestronglyMeasurable_iff_aemeasurable.mp (((hbdd l).aestronglyMeasurable).star)
        have h2 := hstar.comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_eval (fun _ : ↑U => (volume : Measure Ω)) i)
        have h3 := h2.const_mul (e l (x i.1))
        simpa [Function.comp_def] using h3
      refine hsum.congr ?_
      filter_upwards with z
      simp [PV, Finset.sum_apply]
    · exact (hGm.comp ((measurable_updateFinset_pair U).comp
        (measurable_const.prodMk measurable_id))).aemeasurable
  refine hmaj.mono' hmeas ?_
  filter_upwards [hcoord] with z hz
  by_cases hzZ : z ∈ Set.univ.pi (fun _ : ↑U => B.boxL ℓ)
  · rw [Set.indicator_of_mem hzZ, norm_mul, hMdef]
    rw [norm_prod]
    refine mul_le_mul (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => ?_))
      (hGb _) (norm_nonneg _) ?_
    · simp only [PV]
      calc ‖∑ l : Fin m, e l (x i.1) * star (e l (z i))‖
          ≤ ∑ l : Fin m, ‖e l (x i.1) * star (e l (z i))‖ := norm_sum_le _ _
        _ = ∑ l : Fin m, ‖e l (x i.1)‖ * ‖e l (z i)‖ := by simp
        _ ≤ ∑ l : Fin m, ‖e l (x i.1)‖ * Bl l :=
            Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (hz i l) (norm_nonneg _))
    · rw [hMdef] at hMnn; exact hMnn
  · rw [Set.indicator_of_notMem hzZ]
    have hex : ∃ i : ↑U, z i ∉ B.boxL ℓ := by
      simpa only [Set.mem_univ_pi, not_forall] using hzZ
    obtain ⟨i, hi⟩ := hex
    have hzero : PV e (x i.1) (z i) = 0 := by
      refine PV_eq_zero_of_factors e (fun l => ?_)
      by_contra hne
      exact hi (hsupp l (Function.mem_support.mpr hne))
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero, zero_mul, norm_zero]

/-! ## 5. Pointwise additivity on bounded measurable states -/

/-- **Linearity of `slotProj e U` in its state argument on bounded measurable states.**  The
finite sum of integrable integrands is integrable, and the integral of the sum is the sum of the
integrals (`MeasureTheory.integral_finsetSum`); both sides are honest Bochner integrals for every
`x` by `integrable_slotKernel_finset`. -/
theorem slotProj_finsetSum_bdd {m N : ℕ} {ℓ : ℝ} {B : Work.BoseB4.BoxData}
    (e : Fin m → Ω → ℂ) (U : Finset (Fin N))
    (hbdd : ∀ l, MemLp (e l) ⊤) (hsupp : ∀ l, Function.support (e l) ⊆ B.boxL ℓ)
    {ι : Type*} (s : Finset ι) {G : ι → (Fin N → Ω) → ℂ}
    (hGm : ∀ k ∈ s, Measurable (G k)) (hGb : ∀ k ∈ s, ∃ C, ∀ x, ‖G k x‖ ≤ C) :
    (fun x => slotProj e U (fun y => ∑ k ∈ s, G k y) x)
      = fun x => ∑ k ∈ s, slotProj e U (G k) x := by
  funext x
  simp only [slotProj_eq_slotInt_fun]
  show (∫ z : ↑U → Ω, (∏ i : ↑U, PV e (x i.1) (z i)) *
        (∑ k ∈ s, G k (Function.updateFinset x U z)))
      = ∑ k ∈ s, ∫ z : ↑U → Ω, (∏ i : ↑U, PV e (x i.1) (z i)) *
          G k (Function.updateFinset x U z)
  have hInt : ∀ k ∈ s, Integrable (fun z : ↑U → Ω =>
      (∏ i : ↑U, PV e (x i.1) (z i)) * G k (Function.updateFinset x U z))
      (volume : Measure (↑U → Ω)) :=
    fun k hk => integrable_slotKernel_finset e U hbdd hsupp (hGm k hk) (hGb k hk).choose_spec
  rw [show (∫ z : ↑U → Ω, (∏ i : ↑U, PV e (x i.1) (z i)) *
        (∑ k ∈ s, G k (Function.updateFinset x U z)))
      = ∫ z : ↑U → Ω, ∑ k ∈ s, (∏ i : ↑U, PV e (x i.1) (z i)) *
          G k (Function.updateFinset x U z) from
      integral_congr_ae (Filter.Eventually.of_forall (fun z => Finset.mul_sum _ _ _))]
  rw [integral_finsetSum s hInt]

/-! ## 6. The target -/

theorem slotProj_finsetSum_ae {m N : ℕ} {ℓ : ℝ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (U : Finset (Fin N)) {ι : Type*} (s : Finset ι)
    {Θ : ι → (Fin N → EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hΘ : ∀ k ∈ s, MeasureTheory.MemLp (Θ k) ⊤) :
    (fun x => Work.BoseBoxFock.slotProj e U (fun y => ∑ k ∈ s, Θ k y) x)
      =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure
          (Fin N → EuclideanSpace ℝ (Fin 3))).restrict (Submission.BoseGases.abox N ℓ)]
      (fun x => ∑ k ∈ s, Work.BoseBoxFock.slotProj e U (Θ k) x) := by
  classical
  -- an everywhere bounded strongly measurable representative of every summand
  have key : ∀ k : ι, ∃ (g : (Fin N → Ω) → ℂ) (C : ℝ), 0 ≤ C ∧ (∀ x, ‖g x‖ ≤ C) ∧
      StronglyMeasurable g ∧ (k ∈ s → Θ k =ᵐ[(volume : Measure (Fin N → Ω))] g) := by
    intro k
    by_cases hk : k ∈ s
    · obtain ⟨g, C, hCnn, hCb, hgsm, hgeq⟩ :=
        exists_bdd_sm_repr_aux (volume : Measure (Fin N → Ω)) (hΘ k hk)
      exact ⟨g, C, hCnn, hCb, hgsm, fun _ => hgeq⟩
    · exact ⟨fun _ => (0 : ℂ), 0, le_rfl, fun x => by simp, stronglyMeasurable_const,
        fun hk' => absurd hk' hk⟩
  choose g C hCnn hCb hgsm hgeq using key
  -- the sum of the representatives is a.e. equal to the sum
  have hsum : (fun x : Fin N → Ω => ∑ k ∈ s, Θ k x)
      =ᵐ[(volume : Measure (Fin N → Ω))] (fun x => ∑ k ∈ s, g k x) := by
    filter_upwards [(Finset.eventually_all (l := ae (volume : Measure (Fin N → Ω))) s
      (p := fun k x => Θ k x = g k x)).2 (fun k hk => hgeq k hk)] with x hx
    exact Finset.sum_congr rfl (fun k hk => hx k hk)
  -- the identity holds *pointwise* on the sum of the representatives
  have hpoint : slotProj e U (fun y => ∑ k ∈ s, g k y)
      = fun x => ∑ k ∈ s, slotProj e U (g k) x :=
    slotProj_finsetSum_bdd e U hbdd hsupp s
      (fun k _ => (hgsm k).measurable) (fun k _ => ⟨C k, hCb k⟩)
  -- transport along the a.e. equalities
  have h1 : (fun x => slotProj e U (fun y => ∑ k ∈ s, Θ k y) x)
      =ᵐ[(volume : Measure (Fin N → Ω))] (fun x => slotProj e U (fun y => ∑ k ∈ s, g k y) x) :=
    slotProj_ae_eq_congr e U hsum
  have h3 : (fun x => slotProj e U (fun y => ∑ k ∈ s, g k y) x)
      =ᵐ[(volume : Measure (Fin N → Ω))] (fun x => ∑ k ∈ s, slotProj e U (g k) x) :=
    Filter.Eventually.of_forall (fun x => congrFun hpoint x)
  have h2 : (fun x => ∑ k ∈ s, slotProj e U (g k) x)
      =ᵐ[(volume : Measure (Fin N → Ω))] (fun x => ∑ k ∈ s, slotProj e U (Θ k) x) := by
    filter_upwards [(Finset.eventually_all (l := ae (volume : Measure (Fin N → Ω))) s
      (p := fun k x => slotProj e U (g k) x = slotProj e U (Θ k) x)).2
        (fun k hk => slotProj_ae_eq_congr e U (hgeq k hk).symm)] with x hx
    exact Finset.sum_congr rfl (fun k hk => hx k hk)
  exact (h1.trans (h3.trans h2)).filter_mono (ae_mono Measure.restrict_le_self)

end Work.BoseBoxFock
