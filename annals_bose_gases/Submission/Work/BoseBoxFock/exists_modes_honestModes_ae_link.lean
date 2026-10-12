import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.modesOfHonestModes_ae
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.exists_modes_honestModes_ae_link`

The **weak mode bundle of the honest box model together with the physical pairings**.

`Work.BoseBoxFock.modeONBCplx_phys` produces, from the honest mode data `HM`, a complex ONB
`e` of the box model which is box supported and `MemLp ⊤`, and whose pairings with the physical
mode family are exact:

* `∫ conj (e l) · qVec ℓ (kmomLab ℓ N k) = ℓ^{3/2} · HM.f k l`,
* `∫ conj (e l) · thetaExp ℓ (kmomLab ℓ N s) = ℓ^{3/2} · HM.g s l` (`s ≠ 0`),
* `∫ conj (e 0) · thetaFun ℓ = ℓ^{3/2}`.

`Work.BoseBoxFock.modesOfHonestModes_ae` upgrades that family to an everywhere bounded,
measurable, box supported family (the `L^∞` representative cut by the box indicator), a.e. equal
to the original one, and keeps the orthonormality, the integrability of the mode products, the
`MemLp ⊤` and the pinning of the condensate coordinate `e 0 =ᵐ c · thetaFun ℓ`.

Here the two upgrades are combined: the three pairings with the physical family are transported
along the a.e. equality, so that the resulting bundle carries **all** the hypotheses of the BF3c
selection chain (`FINDING_continuous_hypotheses_UNSATISFIABLE.md`) *and* the dictionary rows
`Q(e^{ikx}χ_Λ)`, `e^{isx}θ` needed by the box ↔ Fock dictionary.  Nothing here is `sorry`ed.
-/

namespace Work.BoseBoxFock

open MeasureTheory

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

theorem exists_modes_honestModes_ae_link (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (HM : Work.BoseBoxFock.HonestModes v μ) :
    ∃ e : Fin HM.m → EuclideanSpace ℝ (Fin 3) → ℂ,
      (∀ l, Measurable (e l)) ∧
      (∀ l, ∃ C : ℝ, ∀ x, ‖e l x‖ ≤ C) ∧
      (∀ l, Function.support (e l)
        ⊆ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)) ∧
      (∀ l l', (∫ x : EuclideanSpace ℝ (Fin 3),
        (starRingEnd ℂ) (e l x) * e l' x) = if l = l' then (1 : ℂ) else 0) ∧
      (∀ l l', MeasureTheory.Integrable
        (fun x : EuclideanSpace ℝ (Fin 3) => (starRingEnd ℂ) (e l x) * e l' x)) ∧
      (∀ l, MeasureTheory.MemLp (e l) ⊤
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) ∧
      (∃ c : ℂ, (starRingEnd ℂ) c * c = ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹ ∧
        e 0 =ᵐ[MeasureTheory.volume] fun x =>
          c * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x) ∧
      (∀ (k : Work.BoseBoxFock.Lab HM.N) (l : Fin HM.m),
        (∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (e l x)
            * Work.BoseK15.corpusBox.qVec (Work.BoseBoxFock.ellH v μ)
                (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N k) x)
          = (((Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) * HM.f k l : ℝ) : ℂ)) ∧
      (∀ (s : Work.BoseBoxFock.Lab HM.N) (l : Fin HM.m), s ≠ 0 →
        (∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (e l x)
            * Work.BoseK15.corpusBox.thetaExp (Work.BoseBoxFock.ellH v μ)
                (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) HM.N s) x)
          = (((Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) * HM.g s l : ℝ) : ℂ)) ∧
      (∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (e 0 x)
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x)
        = (((Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) : ℝ) : ℂ) := by
  classical
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  -- ## 0. the honest modes with their physical pairings
  obtain ⟨e, horth, hpairq, hpairt, hpairθ, hsupp, hbddtop⟩ := modeONBCplx_phys v μ HM
  -- ## 0b. the pinning of the condensate coordinate
  have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (Work.BoseK15.corpusBox.boxL (ellH v μ)) ≠ ⊤ := by
    rw [corpusBox_boxL_eq_acube hℓ]
    exact (Submission.BoseGases.acube_lt_top _ hℓ.le).ne
  have hmem2 : MemLp (e 0) 2 (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
    (hbddtop 0).mono_exponent_of_measure_support_ne_top
      (s := Work.BoseK15.corpusBox.boxL (ellH v μ))
      (fun x hx => Function.notMem_support.mp (fun hmem => hx (hsupp 0 hmem))) hvol le_top
  obtain ⟨c, hc, hpin⟩ := e0_prop_theta hℓ hmem2 (horth 0 0) hpairθ
  -- ## 1. replace each mode by an everywhere bounded measurable box supported representative
  choose g C hCnn hCb _hgsm hgeq using fun l : Fin HM.m =>
    exists_bdd_sm_repr_aux (volume : Measure (EuclideanSpace ℝ (Fin 3))) (hbddtop l)
  set e' : Fin HM.m → EuclideanSpace ℝ (Fin 3) → ℂ :=
    fun l => (Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator (g l) with he'def
  -- ## 2. the a.e. equality `e' l =ᵐ e l`
  have heq : ∀ l, e' l =ᵐ[volume] e l := by
    intro l
    have hzero : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))),
        x ∉ Work.BoseK15.corpusBox.boxL (ellH v μ) → g l x = 0 := by
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
    exact ((_hgsm l).measurable.indicator
      (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox (ellH v μ)))
  have hbd' : ∀ (l : Fin HM.m) (x : EuclideanSpace ℝ (Fin 3)), ‖e' l x‖ ≤ C l := by
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
  have hsupp' : ∀ l, Function.support (e' l)
      ⊆ Work.BoseK15.corpusBox.boxL (ellH v μ) := by
    intro l x hx
    by_contra hout
    exact hx (by
      rw [he'def]
      simp only
      rw [Set.indicator_of_notMem hout])
  have hboxc : IsCompact (Work.BoseK15.corpusBox.boxL (ellH v μ)) :=
    Work.BoseK15.corpusBox.boxL_compact (ellH v μ)
  refine ⟨e', hmeas, fun l => ⟨C l, hbd' l⟩, hsupp', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- orthonormality
    intro l l'
    have h : (∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (e' l x) * e' l' x)
        = ∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (e l x) * e l' x :=
      integral_congr_ae (by
        filter_upwards [heq l, heq l'] with x hx hx'
        rw [hx, hx'])
    rw [h, horth l l']
  · -- integrability of the mode products
    intro l l'
    set F : EuclideanSpace ℝ (Fin 3) → ℂ :=
      fun x => (starRingEnd ℂ) (e' l x) * e' l' x with hFdef
    have htsupp : tsupport F ⊆ Work.BoseK15.corpusBox.boxL (ellH v μ) :=
      closure_minimal (fun x hx => by
        have h1 : e' l x ≠ 0 := fun h0 => hx (by
          rw [hFdef]
          simp only
          rw [h0, map_zero, zero_mul])
        exact hsupp' l h1) hboxc.isClosed
    have hcs : HasCompactSupport F :=
      hboxc.of_isClosed_subset (isClosed_tsupport _) htsupp
    have hbound : ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))),
        ‖F x‖ ≤ C l * C l' :=
      Filter.Eventually.of_forall fun x => by
        rw [hFdef, norm_mul]
        exact mul_le_mul (by simpa [RCLike.norm_conj] using hbd' l x) (hbd' l' x)
          (norm_nonneg _) (hCnn l)
    have hm : MemLp F 1 (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
      hcs.memLp_of_bound
        (((Complex.continuous_conj.measurable.comp (hmeas l)).mul (hmeas l')).aestronglyMeasurable)
        (C l * C l') hbound
    exact (memLp_one_iff_integrable).mp hm
  · -- `MemLp ⊤`
    intro l
    have hcs : HasCompactSupport (e' l) :=
      hboxc.of_isClosed_subset (isClosed_tsupport _)
        (closure_minimal (hsupp' l) hboxc.isClosed)
    exact hcs.memLp_of_bound (hmeas l).aestronglyMeasurable (C l)
      (Filter.Eventually.of_forall fun x => hbd' l x)
  · -- the pinning of the condensate coordinate
    exact ⟨c, hc, (heq 0).trans hpin⟩
  · -- the χ-mode pairings
    intro k l
    have h : (∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (e' l x)
          * Work.BoseK15.corpusBox.qVec (ellH v μ) (kmomLab (ellH v μ) HM.N k) x)
        = ∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (e l x)
          * Work.BoseK15.corpusBox.qVec (ellH v μ) (kmomLab (ellH v μ) HM.N k) x :=
      integral_congr_ae (by
        filter_upwards [heq l] with x hx
        rw [hx])
    rw [h, hpairq k l]
  · -- the θ-mode pairings
    intro s l hs
    have h : (∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (e' l x)
          * Work.BoseK15.corpusBox.thetaExp (ellH v μ) (kmomLab (ellH v μ) HM.N s) x)
        = ∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (e l x)
          * Work.BoseK15.corpusBox.thetaExp (ellH v μ) (kmomLab (ellH v μ) HM.N s) x :=
      integral_congr_ae (by
        filter_upwards [heq l] with x hx
        rw [hx])
    rw [h, hpairt s l hs]
  · -- the condensate pairing
    have h : (∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (e' 0 x)
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x)
        = ∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (e 0 x)
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x :=
      integral_congr_ae (by
        filter_upwards [heq 0] with x hx
        rw [hx])
    rw [h, hpairθ]

end Work.BoseBoxFock
