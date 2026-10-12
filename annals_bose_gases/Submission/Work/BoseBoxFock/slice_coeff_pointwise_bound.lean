import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.XSpow_modeProd_pairing
import Submission.Work.BoseBoxFock.norm_integral_mul_sq_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- **The pointwise-in-slice bound on the monomial coefficient.**
For an a.e. strongly measurable, a.e. bounded `g` on `Fin d → Ω` with `0 < d − α 0`, the pairing
`Work.BoseBoxFock.XSpow_modeProd_pairing` identifies
`∫ conj(M_α)·XSpow ℓ univ j g` with `((d − α 0 : ℕ) : ℂ)^j · ∫ conj(M_α)·g`, and the `L²`
Cauchy–Schwarz inequality `Work.BoseBoxFock.norm_integral_mul_sq_le` bounds the former by
`‖M_α‖²_{L²(box)} · ∫ ‖XSpow ℓ univ j g‖²`. Dividing by `((d − α 0 : ℕ) : ℝ)^{2j}` gives the
stated inequality. The `MemLp` hypotheses of Cauchy–Schwarz are supplied by `hgm`, `hgb`
(a.e. strong measurability and a.e. boundedness on the finite-measure box) together with
`ae_bound_modeProd` for the mode product; `hk` is needed to divide.
⚠ the file must NOT import `Submission.Work.BoseBoxFock.slotSum_sectorPointwise` (a `update_pairCoord` clash). -/
theorem slice_coeff_pointwise_bound {m : ℕ} [NeZero m]
    {e : Fin m → EuclideanSpace ℝ (Fin 3) → ℂ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (he : ∀ l l', (∫ x : EuclideanSpace ℝ (Fin 3), (starRingEnd ℂ) (e l x) * e l' x)
      = if l = l' then 1 else 0)
    (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (hc : ∃ c : ℂ, (starRingEnd ℂ) c * c = (ℓ ^ 3)⁻¹ ∧
      (∀ᵐ x ∂(MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))),
        e 0 x = c * Work.BoseK15.corpusBox.thetaFun ℓ x))
    {d : ℕ} (α : Fin m →₀ ℕ) (j : ℕ) {g : (Fin d → EuclideanSpace ℝ (Fin 3)) → ℂ} {C : ℝ}
    (hgm : MeasureTheory.AEStronglyMeasurable g
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → EuclideanSpace ℝ (Fin 3))))
    (hgb : ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure
      (Fin d → EuclideanSpace ℝ (Fin 3))), ‖g u‖ ≤ C)
    (hk : 0 < d - α 0) :
    ‖∫ u in Submission.BoseGases.abox d ℓ,
        (starRingEnd ℂ) (Work.BoseDict.modeProd e d α u) * g u‖ ^ 2
      ≤ ((∫ u in Submission.BoseGases.abox d ℓ, ‖Work.BoseDict.modeProd e d α u‖ ^ 2)
          / (((d - α 0 : ℕ)) : ℝ) ^ (2 * j))
        * (∫ u in Submission.BoseGases.abox d ℓ,
            ‖Work.BoseBoxFock.XSpow ℓ (Finset.univ : Finset (Fin d)) j g u‖ ^ 2) := by
  classical
  -- the box carries a finite measure, so a.e. boundedness gives `MemLp`
  haveI : MeasureTheory.IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.abox d ℓ)) :=
    ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]
        exact Submission.BoseGases.abox_lt_top d ℓ hℓ.le⟩
  -- ## a.e. strong measurability of the mode product
  -- `M_α` is the finite sum of the labelling products `∏_i e (σ i) (x i)`, each of which is a
  -- finite product of coordinate pullbacks of the a.e. strongly measurable `e l`.
  have hmode : MeasureTheory.AEStronglyMeasurable
      (fun x : Fin d → EuclideanSpace ℝ (Fin 3) => Work.BoseDict.modeProd e d α x)
      (MeasureTheory.volume : MeasureTheory.Measure (Fin d → EuclideanSpace ℝ (Fin 3))) := by
    have hpull : ∀ (l : Fin m) (i : Fin d),
        MeasureTheory.AEStronglyMeasurable
          (fun x : Fin d → EuclideanSpace ℝ (Fin 3) => e l (x i))
          (MeasureTheory.volume : MeasureTheory.Measure (Fin d → EuclideanSpace ℝ (Fin 3))) :=
      fun l i => (hbdd l).aestronglyMeasurable.comp_quasiMeasurePreserving
        (MeasureTheory.Measure.quasiMeasurePreserving_eval
          (fun _ : Fin d =>
            (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) i)
    have hα : (fun x : Fin d → EuclideanSpace ℝ (Fin 3) => Work.BoseDict.modeProd e d α x)
        = ∑ σ : Fin d → Fin m, (fun x : Fin d → EuclideanSpace ℝ (Fin 3) =>
            (if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
              * ∏ i : Fin d, e (σ i) (x i)) := by
      funext x
      rw [Finset.sum_apply, Work.BoseDict.modeProd]
    rw [hα]
    refine Finset.aestronglyMeasurable_sum _ fun σ _ => ?_
    refine MeasureTheory.AEStronglyMeasurable.const_mul ?_ _
    rw [show (fun x : Fin d → EuclideanSpace ℝ (Fin 3) => ∏ i : Fin d, e (σ i) (x i))
        = ∏ i : Fin d, (fun x : Fin d → EuclideanSpace ℝ (Fin 3) => e (σ i) (x i)) from by
      funext x; rw [Finset.prod_apply]]
    exact Finset.aestronglyMeasurable_prod _ fun i _ => hpull (σ i) i
  -- ## the two `L²` memberships on the box
  -- `conj M_α ∈ L²`: `ae_bound_modeProd` supplies the a.e. bound on the (finite-measure) box.
  have hmemM : MeasureTheory.MemLp
      (fun u : Fin d → EuclideanSpace ℝ (Fin 3) =>
        (starRingEnd ℂ) (Work.BoseDict.modeProd e d α u)) 2
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.abox d ℓ)) := by
    obtain ⟨CM, -, hCM⟩ := Work.BoseBoxFock.ae_bound_modeProd hbdd d α
    refine MeasureTheory.MemLp.of_bound ?_ CM ?_
    · exact Complex.continuous_conj.comp_aestronglyMeasurable
        (hmode.mono_measure MeasureTheory.Measure.restrict_le_self)
    · filter_upwards [MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self hCM] with u hu
      rwa [Complex.norm_conj]
  -- `XSpow j g ∈ L²`: `XSpow_aeStronglyMeasurable_ae_bounded` propagates `hgm` and `hgb`.
  have hmemX : MeasureTheory.MemLp
      (fun u : Fin d → EuclideanSpace ℝ (Fin 3) =>
        Work.BoseBoxFock.XSpow ℓ (Finset.univ : Finset (Fin d)) j g u) 2
      ((MeasureTheory.volume : MeasureTheory.Measure (Fin d → EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.abox d ℓ)) := by
    obtain ⟨hma, CX, hCX⟩ := Work.BoseBoxFock.XSpow_aeStronglyMeasurable_ae_bounded ℓ hℓ
      (Finset.univ : Finset (Fin d)) hgm ⟨C, hgb⟩ j
    exact MeasureTheory.MemLp.of_bound hma.restrict CX
      (MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self hCX)
  -- ## the pairing identity and Cauchy–Schwarz on the box
  have hpair := Work.BoseBoxFock.XSpow_modeProd_pairing hℓ he hbdd hsupp hc d α j hgm hgb
  have hcs : ‖∫ u in Submission.BoseGases.abox d ℓ,
        (starRingEnd ℂ) (Work.BoseDict.modeProd e d α u)
          * Work.BoseBoxFock.XSpow ℓ (Finset.univ : Finset (Fin d)) j g u‖ ^ 2
      ≤ (∫ u in Submission.BoseGases.abox d ℓ,
          ‖(starRingEnd ℂ) (Work.BoseDict.modeProd e d α u)‖ ^ 2)
        * (∫ u in Submission.BoseGases.abox d ℓ,
            ‖Work.BoseBoxFock.XSpow ℓ (Finset.univ : Finset (Fin d)) j g u‖ ^ 2) :=
    Work.BoseBoxFock.norm_integral_mul_sq_le _ hmemM hmemX
  -- ## the scalar splitting `‖(n : ℂ)^j · B‖² = n^{2j} ‖B‖²`
  have hsplit : ‖((((d - α 0 : ℕ)) : ℂ) ^ j
        * ∫ u in Submission.BoseGases.abox d ℓ,
            (starRingEnd ℂ) (Work.BoseDict.modeProd e d α u) * g u)‖ ^ 2
      = (((d - α 0 : ℕ) : ℝ)) ^ (2 * j)
        * ‖∫ u in Submission.BoseGases.abox d ℓ,
            (starRingEnd ℂ) (Work.BoseDict.modeProd e d α u) * g u‖ ^ 2 := by
    rw [norm_mul, norm_pow, Complex.norm_natCast, mul_pow, ← pow_mul, Nat.mul_comm 2 j]
  -- ## `‖conj M_α‖ = ‖M_α‖` under the integral sign
  have hXMeq : (∫ u in Submission.BoseGases.abox d ℓ,
        ‖(starRingEnd ℂ) (Work.BoseDict.modeProd e d α u)‖ ^ 2)
      = ∫ u in Submission.BoseGases.abox d ℓ, ‖Work.BoseDict.modeProd e d α u‖ ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
    simp only [Complex.norm_conj]
  -- ## the un-divided Cauchy–Schwarz bound, with the two sides in the order needed below
  have hmain : ‖∫ u in Submission.BoseGases.abox d ℓ,
            (starRingEnd ℂ) (Work.BoseDict.modeProd e d α u) * g u‖ ^ 2
        * (((d - α 0 : ℕ) : ℝ)) ^ (2 * j)
      ≤ (∫ u in Submission.BoseGases.abox d ℓ, ‖Work.BoseDict.modeProd e d α u‖ ^ 2)
        * (∫ u in Submission.BoseGases.abox d ℓ,
            ‖Work.BoseBoxFock.XSpow ℓ (Finset.univ : Finset (Fin d)) j g u‖ ^ 2) := by
    have h := hcs
    rw [hpair, hsplit, hXMeq] at h
    calc ‖∫ u in Submission.BoseGases.abox d ℓ,
            (starRingEnd ℂ) (Work.BoseDict.modeProd e d α u) * g u‖ ^ 2
          * (((d - α 0 : ℕ) : ℝ)) ^ (2 * j)
        = (((d - α 0 : ℕ) : ℝ)) ^ (2 * j)
          * ‖∫ u in Submission.BoseGases.abox d ℓ,
              (starRingEnd ℂ) (Work.BoseDict.modeProd e d α u) * g u‖ ^ 2 :=
          mul_comm _ _
      _ ≤ _ := h
  -- ## divide by the positive number `n^{2j}`
  rw [div_mul_eq_mul_div]
  exact (le_div_iff₀ (pow_pos (by exact_mod_cast hk) (2 * j))).mpr hmain

end Work.BoseBoxFock
