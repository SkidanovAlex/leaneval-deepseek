import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.Defs
import Submission.Work.SmallBoxA0.PolarSphere.polarNullAe
import Submission.Work.SmallBoxA0.UncondDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.fj_kernel_bounds`

The four pointwise/integrability facts about the renormalised kernels
`wSmallScaled M (ℓd) ·` divided by `convScale ℓ`, together with the mass
`∫|g₀| = 8π a v`.

`g₀ = v(1−w₀)`, `w₀ := Classical.choose h`.  The mathematically substantive
point is the mass identity `∫|g₀| = 8π a v`: it needs `g₀ ≥ 0` a.e., i.e.
`w₀ ≤ 1` a.e.  The corpus's radial maximum principle
(`Submission.BoseGases.scattering_bounds_ae`) gives this for a *radial,
nonnegative* potential, and `v` here is not assumed radial.  The route used
below replaces `v` by its **spherical average**

    ṽ(x) := (4π)⁻¹ ∫_{S²} v(‖x‖ω) dω,

which is radial and nonnegative, and for which `w₀` is *still* a scattering
solution:  `ṽ(1−w₀) =ᵐ v(1−w₀)`.  Indeed `v(1−w₀)` is a.e. rotation invariant
(`Work.SmallBoxA0.g0_rotation_invariant`), hence a.e. equal to a radial `g`
(`Work.SmallBoxA0.radial_rep_of_rotation_invariant`), and the profile of `g`
is the spherical mean of `v` times `1 − w₀` (see `sphAvg_profile_identity`).
Then `Submission.BoseGases.scattering_bounds_ae` at `(ṽ, w₀)` gives
`0 ≤ w₀ ≤ 1` a.e.
-/

namespace Work.BoseFixB1B

open MeasureTheory

noncomputable section

/-- The **spherically averaged potential** of `v`: the radial function whose value at
`x` is the normalised average of `v` over the sphere of radius `‖x‖`. -/
noncomputable def sphPot (v : EuclideanSpace ℝ (Fin 3) → ℝ) :
    EuclideanSpace ℝ (Fin 3) → ℝ :=
  fun x => (4 * Real.pi)⁻¹ * Work.SmallBoxA0.sphAvg v ‖x‖

lemma sphPot_isRadial (v : EuclideanSpace ℝ (Fin 3) → ℝ) :
    _root_.BoseGases.IsRadial (sphPot v) := by
  intro x y hxy
  simp only [sphPot, hxy]

lemma sphPot_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v) : 0 ≤ sphPot v := by
  intro x
  have hnn : 0 ≤ Work.SmallBoxA0.sphAvg v ‖x‖ := by
    rw [Work.SmallBoxA0.sphAvg]
    exact integral_nonneg (fun ω => hv (‖x‖ • (ω : EuclideanSpace ℝ (Fin 3))))
  exact mul_nonneg (by positivity) hnn

lemma sphPot_tsupport_subset {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) {R' : ℝ}
    (hR' : R < R') :
    tsupport (sphPot v) ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R' := by
  have hzero : ∀ x : EuclideanSpace ℝ (Fin 3), R ≤ ‖x‖ →
      Work.SmallBoxA0.sphAvg v ‖x‖ = 0 := by
    intro x hx
    have hpt : (fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
          v (‖x‖ • (ω : EuclideanSpace ℝ (Fin 3)))) = fun _ => (0 : ℝ) := by
      funext ω
      have hω1 : ‖(ω : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
        simpa using (mem_sphere_iff_norm.mp ω.2)
      refine Submission.BoseGases.v_eq_zero_of_norm_ge hv_supp ?_
      rw [norm_smul, hω1, mul_one, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg x)]
      exact hx
    rw [Work.SmallBoxA0.sphAvg, hpt]
    simp
  have hsupp : Function.support (sphPot v)
      ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R := by
    intro x hx
    rw [Function.mem_support] at hx
    by_contra hmem
    rw [Metric.mem_ball, dist_zero_right, not_lt] at hmem
    exact hx (by simp [sphPot, hzero x hmem])
  calc tsupport (sphPot v) = closure (Function.support (sphPot v)) := rfl
    _ ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) R :=
        closure_minimal (subset_trans hsupp Metric.ball_subset_closedBall)
          Metric.isClosed_closedBall
    _ ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R' := Metric.closedBall_subset_ball hR'

lemma tsupport_g0_subset {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    tsupport (Submission.BoseGases.g0 v h)
      ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R := by
  refine subset_trans (closure_mono ?_) hv_supp
  intro x hx
  rw [Function.mem_support] at hx ⊢
  intro hvx
  exact hx (by simp [Submission.BoseGases.g0, hvx])

/-- **Spherical-mean identity for the profile of the source.**  If `g` is a radial
function that agrees a.e. with `v·(1−w)` and `w` is radial, then for almost every
radius `r > 0` the profile of `g` at `r` is the spherical mean of `v` at `r` times
`1 − w`:

    `4π · g(r·u₀) = (1 − w(r·u₀)) · ∫_{S²} v(rω) dω`.

(Equivalently `g(r·u₀) = ṽ(r·u₀)·(1 − w(r·u₀))` for the spherically averaged
potential `ṽ`.) -/
lemma sphAvg_profile_identity {v w g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw : _root_.BoseGases.IsRadial w) (hg : _root_.BoseGases.IsRadial g)
    (hae : (fun x : EuclideanSpace ℝ (Fin 3) => v x * (1 - w x))
      =ᵐ[MeasureTheory.volume] g) :
    ∀ᵐ r ∂(volume : Measure ℝ), 0 < r →
      4 * Real.pi * g (r • Submission.BoseGases.radU0)
        = (1 - w (r • Submission.BoseGases.radU0)) * Work.SmallBoxA0.sphAvg v r := by
  -- a measurable null superset of the set where `g` and `v(1-w)` differ
  let M : Set (EuclideanSpace ℝ (Fin 3)) :=
    MeasureTheory.toMeasurable (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      {x : EuclideanSpace ℝ (Fin 3) | g x ≠ v x * (1 - w x)}
  have hMmeas : MeasurableSet M := MeasureTheory.measurableSet_toMeasurable _ _
  have hMsub : {x : EuclideanSpace ℝ (Fin 3) | g x ≠ v x * (1 - w x)} ⊆ M :=
    MeasureTheory.subset_toMeasurable _ _
  have hMnull : (volume : Measure (EuclideanSpace ℝ (Fin 3))) M = 0 := by
    rw [show M = MeasureTheory.toMeasurable (volume : Measure (EuclideanSpace ℝ (Fin 3)))
        {x : EuclideanSpace ℝ (Fin 3) | g x ≠ v x * (1 - w x)} from rfl,
      MeasureTheory.measure_toMeasurable]
    exact MeasureTheory.ae_iff.mp hae.symm
  have hslice : ∀ᵐ r ∂(volume : Measure ℝ),
      (volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere
        {ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 |
          (r : ℝ) • (ω : EuclideanSpace ℝ (Fin 3)) ∈ M} = 0 :=
    Work.SmallBoxA0.PolarSphere.polarNullAe hMmeas hMnull
  filter_upwards [hslice] with r hr hrpos
  -- the two spherical integrands agree a.e. on the sphere
  have hsphere : (fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
        g (r • (ω : EuclideanSpace ℝ (Fin 3))))
      =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere]
        (fun ω => v (r • (ω : EuclideanSpace ℝ (Fin 3)))
          * (1 - w (r • (ω : EuclideanSpace ℝ (Fin 3))))) := by
    rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
    refine measure_mono_null (t := {ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 |
      (r : ℝ) • (ω : EuclideanSpace ℝ (Fin 3)) ∈ M}) ?_ hr
    intro ω hω
    exact hMsub hω
  have h1 : (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        g (r • (ω : EuclideanSpace ℝ (Fin 3)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere)
      = ∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
          v (r • (ω : EuclideanSpace ℝ (Fin 3)))
            * (1 - w (r • (ω : EuclideanSpace ℝ (Fin 3))))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere :=
    integral_congr_ae hsphere
  have h2 : (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        g (r • (ω : EuclideanSpace ℝ (Fin 3)))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere)
      = 4 * Real.pi * g (r • Submission.BoseGases.radU0) := by
    have hconst : (fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
          g (r • (ω : EuclideanSpace ℝ (Fin 3))))
        = fun _ : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
            g (r • Submission.BoseGases.radU0) := by
      funext ω
      apply hg
      have hω1 : ‖(ω : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
        simpa using (mem_sphere_iff_norm.mp ω.2)
      rw [norm_smul, norm_smul, hω1, Submission.BoseGases.radU0_norm]
    rw [hconst, integral_const,
      show ((volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere
          : Measure (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)).real Set.univ
        = 4 * Real.pi from Submission.BoseGases.shell_toSphere_total]
    simp [smul_eq_mul]
  have h3 : (∫ ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1,
        v (r • (ω : EuclideanSpace ℝ (Fin 3)))
          * (1 - w (r • (ω : EuclideanSpace ℝ (Fin 3))))
          ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere)
      = (1 - w (r • Submission.BoseGases.radU0)) * Work.SmallBoxA0.sphAvg v r := by
    have hconst : (fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
          v (r • (ω : EuclideanSpace ℝ (Fin 3)))
            * (1 - w (r • (ω : EuclideanSpace ℝ (Fin 3)))))
        = fun ω : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 =>
            (1 - w (r • Submission.BoseGases.radU0))
              * v (r • (ω : EuclideanSpace ℝ (Fin 3))) := by
      funext ω
      have hwω : w (r • (ω : EuclideanSpace ℝ (Fin 3)))
          = w (r • Submission.BoseGases.radU0) := by
        apply hw
        have hω1 : ‖(ω : EuclideanSpace ℝ (Fin 3))‖ = 1 := by
          simpa using (mem_sphere_iff_norm.mp ω.2)
        rw [norm_smul, norm_smul, hω1, Submission.BoseGases.radU0_norm]
      rw [hwω]
      ring
    rw [hconst, integral_const_mul]
    rfl
  rw [← h2, h1, h3]

/-- **From a radial profile to an a.e. statement on `ℝ³`.**  If two radial functions
have the same profile along the ray `r ↦ r·u₀` for almost every `r > 0`, then they
agree almost everywhere. -/
lemma ae_eq_of_ae_profile_of_radial {F G : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hF : _root_.BoseGases.IsRadial F) (hG : _root_.BoseGases.IsRadial G)
    (h : ∀ᵐ r ∂(volume : Measure ℝ), 0 < r →
      F (r • Submission.BoseGases.radU0) = G (r • Submission.BoseGases.radU0)) :
    F =ᵐ[MeasureTheory.volume] G := by
  classical
  set d : Set ℝ := {s : ℝ | 0 < s ∧ F (s • Submission.BoseGases.radU0)
    ≠ G (s • Submission.BoseGases.radU0)} with hd
  have hd0 : (volume : Measure ℝ) d = 0 := by
    have h' := MeasureTheory.ae_iff.mp h
    refine measure_mono_null (s := d)
      (t := {a : ℝ | ¬(0 < a → F (a • Submission.BoseGases.radU0)
        = G (a • Submission.BoseGases.radU0))}) ?_ h'
    intro r hr
    rw [hd] at hr
    exact fun hiff => hr.2 (hiff hr.1)
  -- radiality turns the positive bad set into the negative one
  set e : Set ℝ := {s : ℝ | s < 0 ∧ F (s • Submission.BoseGases.radU0)
    ≠ G (s • Submission.BoseGases.radU0)} with he
  have he0 : (volume : Measure ℝ) e = 0 := by
    have hsub : e ⊆ -d := by
      intro r hr
      rw [he] at hr
      rw [Set.mem_neg]
      rw [hd]
      refine ⟨?_, ?_⟩
      · linarith [hr.1]
      · intro hcontra
        exact hr.2 (by
          have hF' : F ((-r) • Submission.BoseGases.radU0)
              = F (r • Submission.BoseGases.radU0) := by
            apply hF
            rw [Submission.BoseGases.norm_smul_radU0, Submission.BoseGases.norm_smul_radU0,
              abs_neg]
          have hG' : G ((-r) • Submission.BoseGases.radU0)
              = G (r • Submission.BoseGases.radU0) := by
            apply hG
            rw [Submission.BoseGases.norm_smul_radU0, Submission.BoseGases.norm_smul_radU0,
              abs_neg]
          rw [← hF', ← hG']
          exact hcontra)
    refine measure_mono_null hsub ?_
    rw [Measure.measure_neg]
    exact hd0
  set S : Set ℝ := {r : ℝ | F (r • Submission.BoseGases.radU0)
    ≠ G (r • Submission.BoseGases.radU0)} with hS
  have hS0 : (volume : Measure ℝ) S = 0 := by
    refine measure_mono_null (s := S) (t := d ∪ e ∪ {0}) ?_ ?_
    · intro r hr
      rw [hS] at hr
      rcases lt_trichotomy r 0 with hlt | heq | hgt
      · exact Or.inl (Or.inr ⟨hlt, hr⟩)
      · exact Or.inr (by simpa using heq)
      · exact Or.inl (Or.inl ⟨hgt, hr⟩)
    · refine measure_union_null (measure_union_null hd0 he0) ?_
      simp
  have hSmeas : MeasurableSet (MeasureTheory.toMeasurable (volume : Measure ℝ) S) :=
    MeasureTheory.measurableSet_toMeasurable _ _
  have hSmeasnull : (volume : Measure ℝ)
      (MeasureTheory.toMeasurable (volume : Measure ℝ) S) = 0 := by
    rw [MeasureTheory.measure_toMeasurable]
    exact hS0
  have hpre : (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      {x : EuclideanSpace ℝ (Fin 3) |
        ‖x‖ ∈ MeasureTheory.toMeasurable (volume : Measure ℝ) S} = 0 :=
    Submission.BoseGases.volume_preimage_norm_null_r3 hSmeas hSmeasnull
  rw [Filter.EventuallyEq, MeasureTheory.ae_iff]
  refine measure_mono_null (t := {x : EuclideanSpace ℝ (Fin 3) |
      ‖x‖ ∈ MeasureTheory.toMeasurable (volume : Measure ℝ) S}) ?_ hpre
  intro x hx
  simp only [Set.mem_setOf_eq] at hx ⊢
  have hnorm : ‖‖x‖ • Submission.BoseGases.radU0‖ = ‖x‖ := by
    rw [Submission.BoseGases.norm_smul_radU0, abs_of_nonneg (norm_nonneg x)]
  have h1 : F x = F (‖x‖ • Submission.BoseGases.radU0) := hF x _ hnorm.symm
  have h2 : G x = G (‖x‖ • Submission.BoseGases.radU0) := hG x _ hnorm.symm
  refine MeasureTheory.subset_toMeasurable (volume : Measure ℝ) S ?_
  rw [hS]
  simp only [Set.mem_setOf_eq]
  rw [← h1, ← h2]
  exact hx

/-- **`w₀` is a scattering solution of the spherically averaged potential.**  For a
radial scattering solution `w₀` of `v` with `tsupport v ⊆ ball 0 R`, the pair
`(w₀, ṽ)` with `ṽ := sphPot v` is again a scattering solution: the two weak
equations differ only in the source, and `ṽ(1−w₀) =ᵐ v(1−w₀)`. -/
lemma isScatteringSolution_sphPot {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    _root_.BoseGases.IsScatteringSolution (Classical.choose h) (sphPot v) := by
  classical
  set w₀ : EuclideanSpace ℝ (Fin 3) → ℝ := Classical.choose h with hw₀def
  have hspec : _root_.BoseGases.IsRadial w₀
      ∧ _root_.BoseGases.IsScatteringSolution w₀ v := Classical.choose_spec h
  obtain ⟨g, hgrad, hgli, hgaeeq, _hgsupp⟩ :=
    Work.SmallBoxA0.radial_rep_of_rotation_invariant
      (f := Submission.BoseGases.g0 v h)
      (fun A => Work.SmallBoxA0.g0_rotation_invariant hR hv_supp h A)
      (Submission.BoseGases.g0_integrable hR hv_supp h).locallyIntegrable
      (tsupport_g0_subset hv_supp)
  have hgaeeq' : (fun x : EuclideanSpace ℝ (Fin 3) => v x * (1 - w₀ x))
      =ᵐ[MeasureTheory.volume] g := hgaeeq
  have hprof := sphAvg_profile_identity hspec.1 hgrad hgaeeq'
  -- the source of the averaged potential agrees a.e. with `g`
  have hΛeq : (fun x : EuclideanSpace ℝ (Fin 3) => sphPot v x * (1 - w₀ x))
      =ᵐ[MeasureTheory.volume] g := by
    have h1 : ∀ᵐ r ∂(volume : Measure ℝ), 0 < r →
        sphPot v (r • Submission.BoseGases.radU0)
          * (1 - w₀ (r • Submission.BoseGases.radU0))
          = g (r • Submission.BoseGases.radU0) := by
      filter_upwards [hprof] with r hr hrpos
      have hsph : sphPot v (r • Submission.BoseGases.radU0)
          = (4 * Real.pi)⁻¹ * Work.SmallBoxA0.sphAvg v r := by
        simp only [sphPot, Submission.BoseGases.norm_smul_radU0, abs_of_pos hrpos]
      have h4 : (4 * Real.pi) ≠ 0 := by positivity
      have hr' : 4 * Real.pi * g (r • Submission.BoseGases.radU0)
          = (1 - w₀ (r • Submission.BoseGases.radU0)) * Work.SmallBoxA0.sphAvg v r :=
        hr hrpos
      have hcalc : (4 * Real.pi)⁻¹ * ((1 - w₀ (r • Submission.BoseGases.radU0))
            * Work.SmallBoxA0.sphAvg v r) = g (r • Submission.BoseGases.radU0) := by
        rw [← hr', ← mul_assoc, inv_mul_cancel₀ h4, one_mul]
      rw [hsph, show (4 * Real.pi)⁻¹ * Work.SmallBoxA0.sphAvg v r
            * (1 - w₀ (r • Submission.BoseGases.radU0))
          = (4 * Real.pi)⁻¹ * ((1 - w₀ (r • Submission.BoseGases.radU0))
            * Work.SmallBoxA0.sphAvg v r) by ring, hcalc]
    have hΛrad : _root_.BoseGases.IsRadial
        (fun x : EuclideanSpace ℝ (Fin 3) => sphPot v x * (1 - w₀ x)) := by
      intro x y hxy
      simp only [sphPot_isRadial v x y hxy, hspec.1 x y hxy]
    exact ae_eq_of_ae_profile_of_radial hΛrad hgrad h1
  have hΛeqg0 : (fun x : EuclideanSpace ℝ (Fin 3) => sphPot v x * (1 - w₀ x))
      =ᵐ[MeasureTheory.volume] (fun x : EuclideanSpace ℝ (Fin 3) => v x * (1 - w₀ x)) :=
    hΛeq.trans hgaeeq'.symm
  refine ⟨hspec.2.lhs_integrable, ?_, ?_, hspec.2.lim⟩
  · exact hgli.congr hΛeq.symm
  · intro φ hφ
    have hkey : (∫ x, sphPot v x * (1 - w₀ x) * φ x)
        = ∫ x, v x * (1 - w₀ x) * φ x := by
      apply integral_congr_ae
      filter_upwards [hΛeqg0] with x hx
      rw [hx]
    rw [hkey]
    exact hspec.2.eq φ hφ

theorem fj_kernel_bounds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) {h : Work.UBB.ScatSol v} {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    (∀ z : EuclideanSpace ℝ (Fin 3),
        |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z
          / Submission.BoseGases.convScale ℓ z|
          ≤ 2 * |Submission.BoseGases.g0 v h z| / Work.SmallBoxSliding.smallConvLower M) ∧
      (∀ z : EuclideanSpace ℝ (Fin 3),
        |Submission.BoseGases.wSmallScaled M (ℓ * d) v z / Submission.BoseGases.convScale ℓ z|
          ≤ 2 * |v z| / Work.SmallBoxSliding.smallConvLower M) ∧
      (MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.g0 v h z|)) ∧
      (MeasureTheory.Integrable (fun z : EuclideanSpace ℝ (Fin 3) => |v z|)) ∧
      (∫ z : EuclideanSpace ℝ (Fin 3), |Submission.BoseGases.g0 v h z| = 8 * Real.pi * _root_.BoseGases.a v) := by
  classical
  have hscl : 0 < Work.SmallBoxSliding.smallConvLower M :=
    Work.SmallBoxSliding.smallConvLower_pos M
  have hcpos : 0 < ℓ * d := mul_pos hℓ hd
  have hsuppg0 : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ →
      Submission.BoseGases.g0 v h z = 0 :=
    fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h
  have hsuppv : ∀ z : EuclideanSpace ℝ (Fin 3), R ≤ ‖z‖ → v z = 0 :=
    fun z hz => Submission.BoseGases.v_eq_zero_of_norm_ge hv_supp hz
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro z
    have hD2 : |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z|
        ≤ |Submission.BoseGases.g0 v h z| / Work.SmallBoxSliding.smallConvLower M :=
      Work.SmallBoxSliding.abs_wSmallScaled_le (M := M) (c := ℓ * d) (R := R) hM hcpos
        hsuppg0 hR16 z
    by_cases hnorm : ‖z‖ ≤ R
    · have hinv : |(Submission.BoseGases.convScale ℓ z)⁻¹| ≤ 2 :=
        Submission.BoseGases.abs_inv_convScale_le_two (ℓ := ℓ) (R := R) hℓ hRχ hnorm
      rw [div_eq_mul_inv, abs_mul]
      calc
        |Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z|
              * |(Submission.BoseGases.convScale ℓ z)⁻¹|
            ≤ (|Submission.BoseGases.g0 v h z| / Work.SmallBoxSliding.smallConvLower M) * 2 :=
              mul_le_mul hD2 hinv (abs_nonneg _) (div_nonneg (abs_nonneg _) (le_of_lt hscl))
        _ = 2 * |Submission.BoseGases.g0 v h z| / Work.SmallBoxSliding.smallConvLower M := by
              ring
    · have hz0 : Submission.BoseGases.g0 v h z = 0 :=
        hsuppg0 z (le_of_lt (lt_of_not_ge hnorm))
      have hw0 : Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) z = 0 := by
        dsimp [Submission.BoseGases.wSmallScaled]
        rw [hz0]
        ring
      rw [hw0, hz0]
      simp
  · intro z
    have hD2 : |Submission.BoseGases.wSmallScaled M (ℓ * d) v z|
        ≤ |v z| / Work.SmallBoxSliding.smallConvLower M :=
      Work.SmallBoxSliding.abs_wSmallScaled_le (M := M) (c := ℓ * d) (R := R) hM hcpos
        hsuppv hR16 z
    by_cases hnorm : ‖z‖ ≤ R
    · have hinv : |(Submission.BoseGases.convScale ℓ z)⁻¹| ≤ 2 :=
        Submission.BoseGases.abs_inv_convScale_le_two (ℓ := ℓ) (R := R) hℓ hRχ hnorm
      rw [div_eq_mul_inv, abs_mul]
      calc
        |Submission.BoseGases.wSmallScaled M (ℓ * d) v z|
              * |(Submission.BoseGases.convScale ℓ z)⁻¹|
            ≤ (|v z| / Work.SmallBoxSliding.smallConvLower M) * 2 :=
              mul_le_mul hD2 hinv (abs_nonneg _) (div_nonneg (abs_nonneg _) (le_of_lt hscl))
        _ = 2 * |v z| / Work.SmallBoxSliding.smallConvLower M := by ring
    · have hz0 : v z = 0 := hsuppv z (le_of_lt (lt_of_not_ge hnorm))
      have hw0 : Submission.BoseGases.wSmallScaled M (ℓ * d) v z = 0 := by
        dsimp [Submission.BoseGases.wSmallScaled]
        rw [hz0]
        ring
      rw [hw0, hz0]
      simp
  · exact (Submission.BoseGases.g0_integrable hR hv_supp h).abs
  · exact (MeasureTheory.memLp_one_iff_integrable.mp hv1).abs
  · -- the mass identity: `w₀ ≤ 1` a.e. via the radial maximum principle at `sphPot v`
    have hscat : _root_.BoseGases.IsScatteringSolution (Classical.choose h) (sphPot v) :=
      isScatteringSolution_sphPot hR hv_supp
    have hw₀rad : _root_.BoseGases.IsRadial (Classical.choose h) :=
      (Classical.choose_spec h).1
    obtain ⟨_hwnn, hwle⟩ := Submission.BoseGases.scattering_bounds_ae
      (v := sphPot v) (w := Classical.choose h) (R := R + 1) (by linarith)
      (sphPot_nonneg hv) (sphPot_isRadial v)
      (sphPot_tsupport_subset hR hv_supp (by linarith)) hw₀rad hscat
    have hg0nn : ∀ᵐ x : EuclideanSpace ℝ (Fin 3),
        0 ≤ Submission.BoseGases.g0 v h x := by
      filter_upwards [hwle] with x hx
      have hx' : Classical.choose h x ≤ 1 := hx
      rw [show Submission.BoseGases.g0 v h x = v x * (1 - Classical.choose h x) from rfl]
      exact mul_nonneg (hv x) (by linarith)
    have habs : (fun z : EuclideanSpace ℝ (Fin 3) => |Submission.BoseGases.g0 v h z|)
        =ᵐ[MeasureTheory.volume] (fun z : EuclideanSpace ℝ (Fin 3) =>
          Submission.BoseGases.g0 v h z) := by
      filter_upwards [hg0nn] with x hx
      exact abs_of_nonneg hx
    rw [integral_congr_ae habs]
    exact Submission.BoseGases.g0_integral hR hv_supp h

end

end Work.BoseFixB1B
