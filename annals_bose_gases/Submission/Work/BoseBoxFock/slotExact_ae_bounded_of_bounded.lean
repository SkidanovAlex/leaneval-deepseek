import Mathlib.CategoryTheory.Countable
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.FibreProjDefs
import Submission.Work.BoseBoxFock.SliceBadAux
import Submission.Work.BoseBoxFock.slotProj_finsetSum_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.slotExact_ae_bounded_of_bounded`

The sector `slotExact e S Ψ` (`FibreProjDefs.lean`) is the finite inclusion–exclusion
combination `Σ_{T ⊇ S} (−1)^{|T|−|S|} • slotProj e T Ψ` of slot projections

`slotProj e T Ψ x = ∫ z : (↥T → Ω), (∏ i, PV e (x i) (z i)) · Ψ (updateFinset x T z)`,

so it is an integral whose integrand involves the modes `e l` only through the kernel
`PV e a z = Σ_l e l a · conj (e l z)`.  The standing hypotheses are the weak ones
`MemLp (e l) ⊤` (each mode only a.e. bounded and a.e. strongly measurable) together with
`support (e l) ⊆ boxL ℓ` (the modes live in the box of side `ℓ`), and `MemLp Ψ ⊤`
(the state is only `L^∞`).

This file proves that `slotExact e S Ψ` is a.e. strongly measurable and a.e. bounded:

* **a.e. strong measurability** (`slotProj_aesm`): the joint integrand
  `p ↦ (∏ i, PV e (p.1 i.1) (p.2 i)) · Ψ (updateFinset p.1 T p.2)` is a.e. strongly
  measurable on the product space — the kernel product because the coordinate projections are
  quasi-measure-preserving (`Measure.quasiMeasurePreserving_eval` composed with
  `Measure.quasiMeasurePreserving_fst/snd`), the state factor because the insertion map
  `p ↦ updateFinset p.1 T p.2` is quasi-measure-preserving (`updateFinset_qmp`) and
  `Ψ` has an a.e. equal strongly measurable representative.  Then
  `AEStronglyMeasurable.integral_prod_right'` gives the a.e. strong measurability of the
  `z`-integral viewed as a function of `x`.

* **a.e. boundedness** (`slotProj_ae_bounded`): the `z`-integrand vanishes unless every fibre
  coordinate `z i` lies in `boxL ℓ` (a `PV`-factor dies as soon as its second argument leaves
  the support of all modes), and on `(boxL ℓ)^{T}` it is bounded by
  `(Σ_l M l ^ 2) ^ T.card · C` where `M l` bounds the mode `e l` a.e. and `C` bounds an
  everywhere bounded representative of `Ψ` — so the integral is bounded by that constant times
  the (finite) volume of `(boxL ℓ)^{T}`.  The bound is transported back to `Ψ` along the a.e.
  equality `slotProj_ae_eq_congr`.

The sector case is then the finite-sum bookkeeping of these two facts.
-/

noncomputable section

namespace Work.BoseBoxFock

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-! ## 1. A.e. bounds of the modes along the slots -/

/-- If every mode `e l` is a.e. bounded by `M l`, then on the configuration space `ι → Ω` the
values of the modes at *all* slots are a.e. bounded by the same constants: the coordinate
evaluations are a.e.-convergent (`Measure.tendsto_eval_ae_ae`). -/
theorem slotExactAux_ae_forall_eval_le {ι : Type*} [Fintype ι] {m : ℕ} {e : Fin m → Ω → ℂ}
    {M : Fin m → ℝ} (hM : ∀ l, ∀ᵐ y ∂(volume : Measure Ω), ‖e l y‖ ≤ M l) :
    ∀ᵐ x ∂(volume : Measure (ι → Ω)), ∀ (l : Fin m) (i : ι), ‖e l (x i)‖ ≤ M l := by
  rw [Filter.eventually_all]
  intro l
  rw [Filter.eventually_all]
  intro i
  exact (Measure.tendsto_eval_ae_ae (μ := fun _ : ι => (volume : Measure Ω)) (i := i)).eventually
    (hM l)

/-! ## 2. A.e. strong measurability -/

/-- A single slot kernel factor `p ↦ PV e (p.1 i.1) (p.2 i)` is a.e. strongly measurable on the
pair space `(Fin n → Ω) × (↥T → Ω)`, for a.e. strongly measurable modes: the two coordinates
are quasi-measure-preserving, so the a.e. strongly measurable modes can be composed with them. -/
theorem aesm_PV_pair {m n : ℕ} {e : Fin m → Ω → ℂ}
    (he : ∀ l, AEStronglyMeasurable (e l) (volume : Measure Ω)) (T : Finset (Fin n))
    (i : ↥T) :
    AEStronglyMeasurable (fun p : (Fin n → Ω) × (↥T → Ω) => PV e (p.1 i.1) (p.2 i))
      ((volume : Measure (Fin n → Ω)).prod (volume : Measure (↥T → Ω))) := by
  have h1 : Measure.QuasiMeasurePreserving (fun p : (Fin n → Ω) × (↥T → Ω) => p.1 i.1)
      ((volume : Measure (Fin n → Ω)).prod (volume : Measure (↥T → Ω)))
      (volume : Measure Ω) :=
    (Measure.quasiMeasurePreserving_eval (fun _ : Fin n => (volume : Measure Ω)) i.1).comp
      (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure (Fin n → Ω)))
        (ν := (volume : Measure (↥T → Ω))))
  have h2 : Measure.QuasiMeasurePreserving (fun p : (Fin n → Ω) × (↥T → Ω) => p.2 i)
      ((volume : Measure (Fin n → Ω)).prod (volume : Measure (↥T → Ω)))
      (volume : Measure Ω) :=
    (Measure.quasiMeasurePreserving_eval (fun _ : ↥T => (volume : Measure Ω)) i).comp
      (Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Fin n → Ω)))
        (ν := (volume : Measure (↥T → Ω))))
  have hfun : (fun p : (Fin n → Ω) × (↥T → Ω) => PV e (p.1 i.1) (p.2 i))
      = ∑ l : Fin m,
          (fun p : (Fin n → Ω) × (↥T → Ω) => e l (p.1 i.1) * star (e l (p.2 i))) := by
    funext p
    simp only [PV, Finset.sum_apply]
  rw [hfun]
  refine Finset.aestronglyMeasurable_sum _ (fun l _ => ?_)
  exact ((he l).comp_quasiMeasurePreserving h1).mul
    (((he l).comp_quasiMeasurePreserving h2).star)

/-- **A.e. strong measurability of the slot projection.**  For a.e. strongly measurable modes
and an a.e. strongly measurable state, `slotProj e T Ψ` is a.e. strongly measurable: the joint
integrand is a.e. strongly measurable on the product space, so its partial Bochner integral is
a.e. strongly measurable on the configuration space. -/
theorem slotProj_aesm {m n : ℕ} {e : Fin m → Ω → ℂ}
    (he : ∀ l, AEStronglyMeasurable (e l) (volume : Measure Ω)) (T : Finset (Fin n))
    {Ψ : (Fin n → Ω) → ℂ} (hΨ : AEStronglyMeasurable Ψ (volume : Measure (Fin n → Ω))) :
    AEStronglyMeasurable (slotProj e T Ψ) (volume : Measure (Fin n → Ω)) := by
  obtain ⟨g, hgsm, hgeq⟩ := hΨ
  have hprod : AEStronglyMeasurable
      (fun p : (Fin n → Ω) × (↥T → Ω) => ∏ i : ↥T, PV e (p.1 i.1) (p.2 i))
      ((volume : Measure (Fin n → Ω)).prod (volume : Measure (↥T → Ω))) := by
    have hfun : (fun p : (Fin n → Ω) × (↥T → Ω) => ∏ i : ↥T, PV e (p.1 i.1) (p.2 i))
        = ∏ i : ↥T, (fun p : (Fin n → Ω) × (↥T → Ω) => PV e (p.1 i.1) (p.2 i)) := by
      funext p
      simp only [Finset.prod_apply]
    rw [hfun]
    exact Finset.aestronglyMeasurable_prod _ (fun i _ => aesm_PV_pair he T i)
  have hstate : AEStronglyMeasurable
      (fun p : (Fin n → Ω) × (↥T → Ω) => Ψ (Function.updateFinset p.1 T p.2))
      ((volume : Measure (Fin n → Ω)).prod (volume : Measure (↥T → Ω))) :=
    ((hgsm.comp_measurable (measurable_updateFinset_pair T)).aestronglyMeasurable).congr
      ((updateFinset_qmp T).ae_eq hgeq.symm)
  have hF : AEStronglyMeasurable
      (fun p : (Fin n → Ω) × (↥T → Ω) =>
        (∏ i : ↥T, PV e (p.1 i.1) (p.2 i)) * Ψ (Function.updateFinset p.1 T p.2))
      ((volume : Measure (Fin n → Ω)).prod (volume : Measure (↥T → Ω))) :=
    hprod.mul hstate
  have hres := hF.integral_prod_right'
  have hfun : (fun x : Fin n → Ω => ∫ z : ↥T → Ω,
      (∏ i : ↥T, PV e (x i.1) (z i)) * Ψ (Function.updateFinset x T z)) = slotProj e T Ψ := by
    funext x
    rw [slotProj_eq_slotInt, slotInt]
  rw [← hfun]
  exact hres

/-! ## 3. A.e. boundedness -/

/-- **A.e. boundedness of the slot projection.**  The modes are a.e. bounded by `M` and supported
in the box `boxL ℓ`; the state is only `L^∞`.  Then `slotProj e T Ψ` is a.e. bounded by
`vol((boxL ℓ)^{T}) · (Σ_l M l ^ 2)^{|T|} · C`, where `C` bounds an everywhere bounded
representative of `Ψ`.

The `z`-integrand of the slot projection is pointwise supported on `(boxL ℓ)^{T}`: a factor
`PV e (x i) (z i) = Σ_l e l (x i) · conj (e l (z i))` vanishes identically as soon as `z i` lies
outside `⋃_l support (e l)`.  Since `boxL ℓ` is compact it has finite measure, so the integral of
the (a.e.) pointwise bound over `z` is finite and `x`-independent. -/
theorem slotProj_ae_bounded {m n : ℕ} {ℓ : ℝ} {e : Fin m → Ω → ℂ}
    (hbdd : ∀ l, MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (T : Finset (Fin n)) {Ψ : (Fin n → Ω) → ℂ} (hΨ : MemLp Ψ ⊤) :
    ∃ C, ∀ᵐ x ∂(volume : Measure (Fin n → Ω)), ‖slotProj e T Ψ x‖ ≤ C := by
  classical
  choose M hM0 hM using fun l => exists_ae_bound_of_memLp_top_aux (hbdd l)
  obtain ⟨g, C₀, hC₀0, hC₀b, _hgsm, hgeq⟩ :=
    exists_bdd_sm_repr_aux (volume : Measure (Fin n → Ω)) hΨ
  set K : ℝ := ∑ l : Fin m, M l * M l with hKdef
  have hKnn : 0 ≤ K := by
    rw [hKdef]
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (hM0 l) (hM0 l))
  set Z : Set (↥T → Ω) := Set.univ.pi (fun _ : ↥T => Work.BoseK15.corpusBox.boxL ℓ) with hZdef
  have hZmeas : MeasurableSet Z :=
    MeasurableSet.pi Set.countable_univ
      (fun _ _ => Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)
  have hZvol : (volume : Measure (↥T → Ω)) Z
      = ∏ _i : ↥T, (volume : Measure Ω) (Work.BoseK15.corpusBox.boxL ℓ) := by
    rw [hZdef]
    exact Measure.pi_pi (fun _ : ↥T => (volume : Measure Ω))
      (fun _ => Work.BoseK15.corpusBox.boxL ℓ)
  have hZfin : (volume : Measure (↥T → Ω)) Z < ⊤ := by
    rw [hZvol]
    exact ENNReal.prod_lt_top (s := Finset.univ) (fun _ _ =>
      (Work.BoseB4.BoxData.boxL_compact Work.BoseK15.corpusBox ℓ).measure_lt_top)
  have hIntZ : Integrable (Z.indicator (fun _ : ↥T → Ω => K ^ T.card * C₀))
      (volume : Measure (↥T → Ω)) := by
    haveI : IsFiniteMeasure ((volume : Measure (↥T → Ω)).restrict Z) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hZfin⟩
    rw [integrable_indicator_iff hZmeas]
    exact integrable_const _
  refine ⟨(volume Z).toReal * (K ^ T.card * C₀), ?_⟩
  have hxfine : ∀ᵐ x ∂(volume : Measure (Fin n → Ω)),
      ∀ (l : Fin m) (i : Fin n), ‖e l (x i)‖ ≤ M l := slotExactAux_ae_forall_eval_le hM
  have hzfine : ∀ᵐ z ∂(volume : Measure (↥T → Ω)),
      ∀ (l : Fin m) (i : ↥T), ‖e l (z i)‖ ≤ M l := slotExactAux_ae_forall_eval_le hM
  have hbddg : ∀ᵐ x ∂(volume : Measure (Fin n → Ω)),
      ‖slotProj e T g x‖ ≤ (volume Z).toReal * (K ^ T.card * C₀) := by
    filter_upwards [hxfine] with x hx
    have hdom : ∀ᵐ z ∂(volume : Measure (↥T → Ω)),
        ‖(∏ i : ↥T, PV e (x i.1) (z i)) * g (Function.updateFinset x T z)‖
          ≤ Z.indicator (fun _ => K ^ T.card * C₀) z := by
      filter_upwards [hzfine] with z hz
      by_cases hzZ : z ∈ Z
      · rw [Set.indicator_of_mem hzZ]
        have hPV : ∀ i : ↥T, ‖PV e (x i.1) (z i)‖ ≤ K := by
          intro i
          calc ‖PV e (x i.1) (z i)‖ = ‖∑ l : Fin m, e l (x i.1) * star (e l (z i))‖ := rfl
            _ ≤ ∑ l : Fin m, ‖e l (x i.1) * star (e l (z i))‖ := norm_sum_le _ _
            _ = ∑ l : Fin m, ‖e l (x i.1)‖ * ‖e l (z i)‖ := by
                refine Finset.sum_congr rfl fun l _ => ?_
                rw [norm_mul, norm_star]
            _ ≤ ∑ l : Fin m, M l * M l :=
                Finset.sum_le_sum (fun l _ =>
                  mul_le_mul (hx l i.1) (hz l i) (norm_nonneg _) (hM0 l))
            _ = K := hKdef
        calc ‖(∏ i : ↥T, PV e (x i.1) (z i)) * g (Function.updateFinset x T z)‖
            = (∏ i : ↥T, ‖PV e (x i.1) (z i)‖) * ‖g (Function.updateFinset x T z)‖ := by
              rw [norm_mul, norm_prod]
          _ ≤ (∏ _i : ↥T, K) * C₀ :=
              mul_le_mul
                (Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => hPV i))
                (hC₀b _) (norm_nonneg _) (Finset.prod_nonneg (fun i _ => hKnn))
          _ = K ^ T.card * C₀ := by
              rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
      · rw [Set.indicator_of_notMem hzZ]
        have hnot : ∃ i : ↥T, z i ∉ Work.BoseK15.corpusBox.boxL ℓ := by
          simpa only [hZdef, Set.mem_univ_pi, not_forall] using hzZ
        obtain ⟨i, hi⟩ := hnot
        have hzero : PV e (x i.1) (z i) = 0 :=
          PV_eq_zero_of_factors e (fun l => by
            by_contra hne
            exact hi (hsupp l (Function.mem_support.mpr hne)))
        rw [Finset.prod_eq_zero (Finset.mem_univ i) hzero, zero_mul, norm_zero]
    have h1 : ‖slotProj e T g x‖
        ≤ ∫ z : ↥T → Ω,
            ‖(∏ i : ↥T, PV e (x i.1) (z i)) * g (Function.updateFinset x T z)‖ := by
      rw [slotProj_eq_slotInt, slotInt]
      exact norm_integral_le_integral_norm _
    calc ‖slotProj e T g x‖
        ≤ ∫ z : ↥T → Ω,
            ‖(∏ i : ↥T, PV e (x i.1) (z i)) * g (Function.updateFinset x T z)‖ := h1
      _ ≤ ∫ z : ↥T → Ω, Z.indicator (fun _ => K ^ T.card * C₀) z :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _) hIntZ hdom
      _ = (volume Z).toReal * (K ^ T.card * C₀) := by
          rw [integral_indicator_const _ hZmeas, Measure.real, smul_eq_mul]
  filter_upwards [hbddg, slotProj_ae_eq_congr e T hgeq] with x hx heq
  rw [heq]
  exact hx

/-! ## 4. The sector -/

theorem slotExact_ae_bounded_of_bounded {n m : ℕ} {ℓ : ℝ} {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (S : Finset (Fin n)) {Ψ : (Fin n → EuclideanSpace ℝ (Fin 3)) → ℂ}
    (hΨ : MeasureTheory.MemLp Ψ ⊤) :
    MeasureTheory.AEStronglyMeasurable (Work.BoseBoxFock.slotExact e S Ψ)
        (MeasureTheory.volume : MeasureTheory.Measure (Fin n → EuclideanSpace ℝ (Fin 3)))
    ∧ ∃ C, ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure
        (Fin n → EuclideanSpace ℝ (Fin 3))), ‖Work.BoseBoxFock.slotExact e S Ψ x‖ ≤ C := by
  classical
  have heasm : ∀ T : Finset (Fin n),
      MeasureTheory.AEStronglyMeasurable (Work.BoseBoxFock.slotProj e T Ψ)
        (MeasureTheory.volume : MeasureTheory.Measure (Fin n → EuclideanSpace ℝ (Fin 3))) :=
    fun T => slotProj_aesm (fun l => (hbdd l).aestronglyMeasurable) T hΨ.aestronglyMeasurable
  refine ⟨?_, ?_⟩
  · show MeasureTheory.AEStronglyMeasurable
      (∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
        (-1 : ℂ) ^ (T.card - S.card) • Work.BoseBoxFock.slotProj e T Ψ)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin n → EuclideanSpace ℝ (Fin 3)))
    exact Finset.aestronglyMeasurable_sum _
      (fun T _ => (heasm T).const_smul _)
  · choose Cpt hCpt using fun T : Finset (Fin n) => slotProj_ae_bounded hbdd hsupp T hΨ
    refine ⟨∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T), Cpt T, ?_⟩
    have hall : ∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin n → Ω)),
        ∀ T : ↥(Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T)),
          ‖Work.BoseBoxFock.slotProj e T.1 Ψ x‖ ≤ Cpt T.1 := by
      rw [Filter.eventually_all]
      intro T
      exact hCpt T.1
    filter_upwards [hall] with x hx
    calc ‖Work.BoseBoxFock.slotExact e S Ψ x‖
        = ‖∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
              (-1 : ℂ) ^ (T.card - S.card) • Work.BoseBoxFock.slotProj e T Ψ x‖ := by
          simp only [Work.BoseBoxFock.slotExact, Finset.sum_apply, Pi.smul_apply]
      _ ≤ ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T),
              ‖(-1 : ℂ) ^ (T.card - S.card) • Work.BoseBoxFock.slotProj e T Ψ x‖ :=
          norm_sum_le _ _
      _ ≤ ∑ T ∈ Finset.univ.filter (fun T : Finset (Fin n) => S ⊆ T), Cpt T :=
          Finset.sum_le_sum (fun T hT => by
            rw [norm_smul, norm_pow, norm_neg, norm_one, one_pow, one_mul]
            exact hx ⟨T, hT⟩)

end Work.BoseBoxFock
