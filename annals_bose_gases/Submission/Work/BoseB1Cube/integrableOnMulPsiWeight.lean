import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.WB.cs_apply
import Submission.Work.BoseFixB1.WB.psiWeight_le_affine
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Integrability of `g · ψ_μ(t)` on a set `G`

Let `ψ_μ(t) = (t − μ)²/(1 + t/μ)` be the `F`-remainder weight of FS
(`Work.SmallBoxSliding.psiWeight 1 μ`) and let `G ⊆ ℝ³` be an arbitrary set (no
measurability is assumed).  If

* `g`, `t` are non-negative on `G`,
* `g` and `g·t` are integrable on `G`,
* `t` is a.e. measurable on `G` (with respect to `volume.restrict G`),

then `g·ψ_μ(t)` is integrable on `G`.

The mathematical content is the pointwise bound `ψ_μ(t) ≤ μ² + μ t` for `t ≥ 0`
(`WB.psiWeight_one_le`) applied on `G`, together with the fact that the
hypotheses `g, t, g·t ∈ L¹(G)` are *a.e.* statements with respect to
`volume.restrict G`, so that one may replace `g`, `t` by measurable
representatives `g' =ᵐ g`, `t' =ᵐ t` (`AEMeasurable.mk`).  The only genuinely
measure-theoretic point is then the transfer of the pointwise hypothesis
`0 ≤ t` **on `G`** to the a.e. statement `0 ≤ t'` on `G`; this is
`ae_nonneg_of_ae_eq_of_forall_mem_restrict` below, whose proof uses that the
outer measure of a measure is the infimum over measurable supersets
(`MeasureTheory.measure_eq_iInf`): the measurable set `{t' < 0}` satisfies
`{t' < 0} ∩ G ⊆ {t ≠ t'}`, and every measurable superset `v ⊇ {t ≠ t'}` has
`volume (v ∩ G) ≥ volume ({t' < 0} ∩ G)`.

Note that all functions here are real-valued, so no measurability of `g` is
needed as a hypothesis: it is a consequence of `IntegrableOn g G volume`.
-/

namespace Work.BoseB1Cube

open MeasureTheory

/-- **The a.e. non-negativity transfer.**  If `s` is measurable, `f` is
non-negative on `G`, and `s =ᵐ f` with respect to `volume.restrict G`, then `s`
is non-negative a.e. with respect to `volume.restrict G`.

On `{s < 0} ∩ G` we have `s u < 0 ≤ f u`, so `s u ≠ f u`; hence
`{s < 0} ∩ G ⊆ {s ≠ f}`, and since `volume.restrict G` is the infimum over
measurable supersets and `(volume.restrict G) {s ≠ f} = 0`, the measurable set
`{s < 0}` is a null set for `volume.restrict G`. -/
theorem ae_nonneg_of_ae_eq_of_forall_mem_restrict
    {G : Set (EuclideanSpace ℝ (Fin 3))} {s f : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hsm : Measurable s) (hae : s =ᵐ[volume.restrict G] f)
    (hf : ∀ u ∈ G, 0 ≤ f u) :
    ∀ᵐ u ∂(volume.restrict G), 0 ≤ s u := by
  refine (ae_iff).mpr ?_
  have hA0 : (volume.restrict G) {u : EuclideanSpace ℝ (Fin 3) | ¬ s u = f u} = 0 :=
    (ae_iff).mp hae
  have hms : MeasurableSet {u : EuclideanSpace ℝ (Fin 3) | s u < 0} := hsm measurableSet_Iio
  have hkey : (volume.restrict G) {u : EuclideanSpace ℝ (Fin 3) | s u < 0}
      ≤ (volume.restrict G) {u : EuclideanSpace ℝ (Fin 3) | ¬ s u = f u} := by
    rw [Measure.restrict_apply hms]
    conv_rhs => rw [measure_eq_iInf]
    refine le_iInf fun v => le_iInf fun hv => le_iInf fun hvm => ?_
    rw [Measure.restrict_apply hvm]
    refine measure_mono fun u hu => ⟨hv ?_, hu.2⟩
    exact fun h => absurd (h.symm ▸ hf u hu.2) (not_le.mpr (show s u < 0 from hu.1))
  have hset : {u : EuclideanSpace ℝ (Fin 3) | ¬ 0 ≤ s u}
      = {u : EuclideanSpace ℝ (Fin 3) | s u < 0} := by
    ext u; exact not_le
  rw [hset]
  exact le_antisymm (hA0 ▸ hkey) zero_le

theorem integrableOnMulPsiWeight {G : Set (EuclideanSpace ℝ (Fin 3))} {t g : EuclideanSpace ℝ (Fin 3) → ℝ}
    {μ : ℝ}
    (hμ : 0 < μ)
    (ht : ∀ u ∈ G, 0 ≤ t u) (hg : ∀ u ∈ G, 0 ≤ g u)
    (hIg : MeasureTheory.IntegrableOn g G MeasureTheory.volume)
    (hIgt : MeasureTheory.IntegrableOn (fun u => g u * t u) G MeasureTheory.volume)
    (htm : AEMeasurable t (MeasureTheory.volume.restrict G)) :
    MeasureTheory.IntegrableOn (fun u => g u * Work.SmallBoxSliding.psiWeight 1 μ (t u)) G
      MeasureTheory.volume := by
  set ν : Measure (EuclideanSpace ℝ (Fin 3)) := volume.restrict G with hν
  have hgm : AEStronglyMeasurable g ν := hIg.aestronglyMeasurable
  have hψm : Measurable (fun t : ℝ => Work.SmallBoxSliding.psiWeight 1 μ t) :=
    Work.BoseFixB1.WB.measurable_psiWeight_cs 1 μ
  -- measurable representatives of `t` and `g`
  set t' : EuclideanSpace ℝ (Fin 3) → ℝ := AEMeasurable.mk t htm with ht'def
  have ht'm : Measurable t' := htm.measurable_mk
  have ht'ae : t =ᵐ[ν] t' := htm.ae_eq_mk
  set g' : EuclideanSpace ℝ (Fin 3) → ℝ := AEMeasurable.mk g hgm.aemeasurable with hg'def
  have hg'm : Measurable g' := hgm.aemeasurable.measurable_mk
  have hg'ae : g =ᵐ[ν] g' := hgm.aemeasurable.ae_eq_mk
  -- the pointwise hypotheses, transferred to a.e. statements
  have ht'nn : ∀ᵐ u ∂ν, 0 ≤ t' u :=
    ae_nonneg_of_ae_eq_of_forall_mem_restrict ht'm ht'ae.symm ht
  have hg'nn : ∀ᵐ u ∂ν, 0 ≤ g' u :=
    ae_nonneg_of_ae_eq_of_forall_mem_restrict hg'm hg'ae.symm hg
  -- transfer the integrability hypotheses to the representatives
  have hIg' : Integrable g' ν := hIg.congr hg'ae
  have hIgt' : Integrable (fun u => g' u * t' u) ν := by
    refine hIgt.congr ?_
    filter_upwards [hg'ae, ht'ae] with u h1 h2
    rw [h1, h2]
  have hdom : Integrable (fun u => μ ^ 2 * g' u + μ * (g' u * t' u)) ν :=
    (hIg'.const_mul (μ ^ 2)).add (hIgt'.const_mul μ)
  -- the pointwise bound `ψ_μ(t) ≤ μ² + μ t` for `t ≥ 0`
  have hInt2 : Integrable (fun u => g' u * Work.SmallBoxSliding.psiWeight 1 μ (t' u)) ν := by
    refine hdom.mono' ?_ ?_
    · exact (hg'm.mul (hψm.comp ht'm)).aestronglyMeasurable
    · filter_upwards [ht'nn, hg'nn] with u ht0 hg0
      have hpsi0 : 0 ≤ Work.SmallBoxSliding.psiWeight 1 μ (t' u) :=
        Work.BoseFixB1.WB.psiWeight_one_nonneg hμ ht0
      have hpsi : Work.SmallBoxSliding.psiWeight 1 μ (t' u) ≤ μ ^ 2 + μ * t' u :=
        Work.BoseFixB1.WB.psiWeight_one_le hμ ht0
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hg0 hpsi0)]
      calc g' u * Work.SmallBoxSliding.psiWeight 1 μ (t' u)
          ≤ g' u * (μ ^ 2 + μ * t' u) := mul_le_mul_of_nonneg_left hpsi hg0
        _ = μ ^ 2 * g' u + μ * (g' u * t' u) := by ring
  -- return along the a.e. equalities
  exact hInt2.congr (by
    filter_upwards [hg'ae, ht'ae] with u h1 h2
    rw [← h1, ← h2])

end Work.BoseB1Cube
