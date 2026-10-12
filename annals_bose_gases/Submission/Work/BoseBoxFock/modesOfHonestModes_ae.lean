import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.modesOfHonestModes
import Submission.Work.BoseBoxFock.slotProj_finsetSum_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.modesOfHonestModes_ae` — the **weak mode bundle** of the honest model

`FINDING_continuous_hypotheses_UNSATISFIABLE.md` proves that the `Continuous` mode hypotheses of
the BF3c selection chain (`SlotFacts`, `exists_slice_le_window_of_op`, `AVgen_slotFacts`,
`modelAssemblyAVgen`, …) are **unsatisfiable**: the honest mode `e 0` is a.e. the box indicator
`thetaFun ℓ`, so it has no continuous representative.  The repair is to run the chain with the
weak bundle

    (hmeas : ∀ l, Measurable (e l))     (hbdE : ∀ l, ∃ C, ∀ x, ‖e l x‖ ≤ C)
    (hsupp : ∀ l, support (e l) ⊆ boxL ℓ)   (horth)   (hint : Integrable (star (e l) · e l'))
    (hbdd : ∀ l, MemLp (e l) ⊤)   (hpin : e 0 =ᵐ c · thetaFun ℓ)

This module produces exactly that bundle from the honest mode data `HM : HonestModes v μ`, starting
from the honest complex ONB of `Work.BoseBoxFock.modesOfHonestModes`
(`Work.BoseBoxFock.modeONBCplx_phys` + `e0_prop_theta`):

* `exists_modes_honestModes` gives modes `e` with `horth`, `MemLp ⊤`, box support and the pinning;
* each mode is replaced by an **everywhere bounded, measurable, box supported representative**
  (the `L^∞` representative of `Work.BoseBoxFock.exists_bdd_sm_repr_aux`, cut by the box
  indicator), which is a.e. equal to the original mode — so all the *a.e.*/integral properties
  (`horth`, `hint`, `hpin`, `MemLp ⊤`) transport unchanged.

This is the interface through which the weak chain is instantiated; nothing here is `sorry`ed.
-/

noncomputable section
open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

/-- **The weak mode bundle of the honest model.**  For every `HM : HonestModes v μ` there is a mode
family `e : Fin HM.m → Ω → ℂ` which is measurable, everywhere bounded, supported in the box
`boxL (ellH v μ)`, orthonormal, has integrable mode products and `MemLp ⊤` modes, and pins the
condensate coordinate: `e 0 =ᵐ c · thetaFun (ellH v μ)` with `conj c * c = ((ellH v μ) ^ 3)⁻¹`.

These are exactly the hypotheses under which the BF3c selection chain must be re-run
(the `Continuous`/`HasCompactSupport` spellings cannot be instantiated — see
`FINDING_continuous_hypotheses_UNSATISFIABLE.md`). -/
theorem exists_modes_honestModes_ae (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (HM : Work.BoseBoxFock.HonestModes v μ) :
    ∃ e : Fin HM.m → Ω → ℂ,
      (∀ l, Measurable (e l)) ∧
      (∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C) ∧
      (∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL (ellH v μ)) ∧
      (∀ l l', (∫ x : Ω, (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then (1 : ℂ) else 0) ∧
      (∀ l l', Integrable (fun x : Ω => (starRingEnd ℂ) (e l x) * e l' x)) ∧
      (∀ l, MemLp (e l) ⊤ (volume : Measure Ω)) ∧
      (∃ c : ℂ, (starRingEnd ℂ) c * c = ((ellH v μ) ^ 3)⁻¹ ∧
        e 0 =ᵐ[volume] fun x => c * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x) := by
  obtain ⟨e, horth, hbdd, hsupp, hpin⟩ := exists_modes_honestModes v μ HM
  classical
  -- ## 1. replace each mode by an everywhere bounded measurable box supported representative
  choose g C hCnn hCb _hgsm hgeq using fun l : Fin HM.m =>
    exists_bdd_sm_repr_aux (volume : Measure Ω) (hbdd l)
  set e' : Fin HM.m → Ω → ℂ :=
    fun l => (Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator (g l) with he'def
  -- ## 2. the a.e. equality `e' l =ᵐ e l`
  have heq : ∀ l, e' l =ᵐ[volume] e l := by
    intro l
    have hzero : ∀ᵐ x ∂(volume : Measure Ω), x ∉ Work.BoseK15.corpusBox.boxL (ellH v μ) →
        g l x = 0 := by
      filter_upwards [hgeq l] with x hx hxout
      rw [← hx]
      exact Function.notMem_support.mp (fun hmem => hxout (hsupp l hmem))
    filter_upwards [hgeq l, hzero] with x hx hxl
    by_cases hmem : x ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
    · rw [he'def]
      simp only
      rw [Set.indicator_of_mem hmem, hx]
    · rw [he'def]
      simp only
      rw [Set.indicator_of_notMem hmem, hx, hxl hmem]
  -- ## 3. the bundle
  have hmeas : ∀ l, Measurable (e' l) := by
    intro l
    exact ((_hgsm l).measurable.indicator (Work.BoseB4.BoxData.boxL_measurableSet
      Work.BoseK15.corpusBox (ellH v μ)))
  have hbd' : ∀ (l : Fin HM.m) (x : Ω), ‖e' l x‖ ≤ C l := by
    intro l x
    by_cases hmem : x ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
    · rw [he'def]
      simp only
      rw [Set.indicator_of_mem hmem]
      exact hCb l x
    · rw [he'def]
      simp only
      rw [Set.indicator_of_notMem hmem]
      simpa using hCnn l
  have hsupp' : ∀ l, Function.support (e' l) ⊆ Work.BoseK15.corpusBox.boxL (ellH v μ) := by
    intro l x hx
    by_contra hout
    exact hx (by
      rw [he'def]
      simp only
      rw [Set.indicator_of_notMem hout])
  have hboxc : IsCompact (Work.BoseK15.corpusBox.boxL (ellH v μ)) :=
    Work.BoseK15.corpusBox.boxL_compact (ellH v μ)
  refine ⟨e', hmeas, fun l => ⟨C l, hbd' l⟩, hsupp', ?_, ?_, ?_, ?_⟩
  · -- orthonormality
    intro l l'
    have h : (∫ x : Ω, (starRingEnd ℂ) (e' l x) * e' l' x)
        = ∫ x : Ω, (starRingEnd ℂ) (e l x) * e l' x :=
      integral_congr_ae (by
        filter_upwards [heq l, heq l'] with x hx hx'
        rw [hx, hx'])
    rw [h, horth l l']
  · -- integrability of the mode products
    intro l l'
    set F : Ω → ℂ := fun x => (starRingEnd ℂ) (e' l x) * e' l' x with hFdef
    have htsupp : tsupport F ⊆ Work.BoseK15.corpusBox.boxL (ellH v μ) :=
      closure_minimal (fun x hx => by
        have h1 : e' l x ≠ 0 := fun h0 => hx (by
          rw [hFdef]
          simp only
          rw [h0, map_zero, zero_mul])
        exact hsupp' l h1) hboxc.isClosed
    have hcs : HasCompactSupport F :=
      hboxc.of_isClosed_subset (isClosed_tsupport _) htsupp
    have hbound : ∀ᵐ x ∂(volume : Measure Ω), ‖F x‖ ≤ C l * C l' :=
      Filter.Eventually.of_forall fun x => by
        rw [hFdef, norm_mul]
        exact mul_le_mul (by simpa [RCLike.norm_conj] using hbd' l x) (hbd' l' x)
          (norm_nonneg _) (hCnn l)
    have hm : MemLp F 1 (volume : Measure Ω) :=
      hcs.memLp_of_bound
        (((Complex.continuous_conj.measurable.comp (hmeas l)).mul (hmeas l')).aestronglyMeasurable)
        (C l * C l') hbound
    exact (memLp_one_iff_integrable).mp hm
  · -- `MemLp ⊤`
    intro l
    have hcs : HasCompactSupport (e' l) :=
      hboxc.of_isClosed_subset (isClosed_tsupport _) (closure_minimal (hsupp' l) hboxc.isClosed)
    exact hcs.memLp_of_bound (hmeas l).aestronglyMeasurable (C l)
      (Filter.Eventually.of_forall fun x => hbd' l x)
  · -- the pinning of the condensate coordinate
    obtain ⟨c, hc, hpin'⟩ := hpin
    exact ⟨c, hc, (heq 0).trans hpin'⟩

end Work.BoseBoxFock
