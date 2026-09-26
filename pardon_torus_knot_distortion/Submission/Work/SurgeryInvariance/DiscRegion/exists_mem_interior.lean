import Mathlib
import Submission.Work.SurgeryInvariance.Defs

/-!
# Every point of the torus lies in the interior of an embedded disc

`Work.SurgeryInvariance.DiscRegion P` records an embedded disc `D` of the surface `F = P.carrier`
of a parametrised torus: an injective continuous map `D.e` of the closed unit disc of `ℂ` into
`F`, whose interior is open in `F`.

The parametrisation `psiMap P.psi : ℝ² → F` is a covering map
(`Work.TorusCover.isCoveringMap_psiMapToRange_param`), hence a local homeomorphism; the inverse
branch at a parameter point `p` with `P.psi p.1 p.2 = x` is a homeomorphism of a neighbourhood of
`p` onto a neighbourhood of `x`, and pulling back a small Euclidean disc of parameters through it
produces an embedded disc of `F` whose interior contains `x`.

This file proves `exists_mem_interior`: **every point of the torus is in the interior of an
embedded disc of the torus**.  It is the point-set input making the local model of the surgery
(`Work.SurgeryInvariance.SurgeryStep`) meaningful at every point.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open Work.TorusCover

namespace Work.SurgeryInvariance.DiscRegion

/-- **Every point of the torus lies in the interior of an embedded disc of the torus.**

The parametrisation of the torus is a covering map onto its image
(`Work.TorusCover.isCoveringMap_psiMapToRange_param`), so it is a local homeomorphism: at a
parameter point `p` over `x` there is an open partial homeomorphism `E` of the parameter plane
onto the surface with `p ∈ E.source`.  Composing it with the similarity
`Φ z = (p.1 + r * z.re, p.2 + r * z.im)` (`r > 0` small enough that the closed disc of radius `r`
about `p` lies in `E.source`) gives an embedding of the closed unit disc of `ℂ` into the surface
whose image of the open unit disc — the image of an open set under the local homeomorphism — is
open in the surface, i.e. an embedded disc of the torus whose interior contains `x`. -/
theorem exists_mem_interior (P : Work.CoreTopology.ParamTorus)
    (x : LeanEval.KnotTheory.PardonDistortion.R3) (hx : x ∈ P.carrier) :
    ∃ D : Work.SurgeryInvariance.DiscRegion P, x ∈ D.interior := by
  have hcov : IsCoveringMap (psiMapToRange P.psi) := isCoveringMap_psiMapToRange_param P
  have hf : IsLocalHomeomorph (psiMapToRange P.psi) := hcov.isLocalHomeomorph
  -- the same local homeomorphism, with the range of the parametrisation written as `P.carrier`
  have hf' : IsLocalHomeomorph
      (fun q : ℝ × ℝ => (⟨P.psi q.1 q.2, P.psi_mem_carrier q.1 q.2⟩ : P.carrier)) := hf
  obtain ⟨a, b, hab⟩ := (Work.CoreTopology.ParamTorus.mem_carrier_iff P x).mp hx
  set p : ℝ × ℝ := (a, b) with hp_def
  have hp : P.psi p.1 p.2 = x := hab
  obtain ⟨E, hp_src, hE⟩ := hf' p
  have hEp : E p = (⟨x, hx⟩ : P.carrier) := by
    have h := congrFun hE p
    rw [← h]
    exact Subtype.ext hp
  obtain ⟨ε, hεpos, hεball⟩ := Metric.isOpen_iff.mp E.open_source p hp_src
  let r : ℝ := ε / 2
  have hrpos : 0 < r := by positivity
  have hrlt : r < ε := by show ε / 2 < ε; linarith
  -- the similarity of the parameter plane carrying the unit disc to the disc of radius `r` at `p`
  let Φ : ℂ → ℝ × ℝ := fun z => (p.1 + r * z.re, p.2 + r * z.im)
  have hΦcont : Continuous Φ := by fun_prop
  -- the Euclidean disc of radius `r` about `p`
  let S : Set (ℝ × ℝ) := {w | (w.1 - p.1)^2 + (w.2 - p.2)^2 < r^2}
  have hSopen : IsOpen S :=
    isOpen_lt (by fun_prop : Continuous fun w : ℝ × ℝ => (w.1 - p.1)^2 + (w.2 - p.2)^2)
      continuous_const
  have hSsub : S ⊆ E.source := by
    intro w hw
    apply hεball
    have hw' : (w.1 - p.1)^2 + (w.2 - p.2)^2 < r^2 := hw
    have h1 : |w.1 - p.1| < r :=
      abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg (w.2 - p.2), hw']) (le_of_lt hrpos)
    have h2 : |w.2 - p.2| < r :=
      abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg (w.1 - p.1), hw']) (le_of_lt hrpos)
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : w - p = (w.1 - p.1, w.2 - p.2) := by ext <;> simp
    rw [hsub, Prod.norm_def]
    simp only [Real.norm_eq_abs]
    exact max_lt (lt_trans h1 hrlt) (lt_trans h2 hrlt)
  -- `S` is exactly the image of the open unit disc of `ℂ` under `Φ`
  have hΦS : Φ '' {z : ℂ | ‖z‖ < 1} = S := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      simp only [S, Set.mem_ofPred_eq]
      have hz' : ‖z‖ < 1 := hz
      have hz2 : ‖z‖^2 < 1 := by
        have h : ‖z‖^2 < (1:ℝ)^2 := by
          rw [sq_lt_sq, abs_of_nonneg (norm_nonneg z), abs_one]; exact hz'
        simpa using h
      have hnorm : z.re^2 + z.im^2 = ‖z‖^2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      have hr2 : 0 < r^2 := by positivity
      have hcalc : (p.1 + r * z.re - p.1)^2 + (p.2 + r * z.im - p.2)^2
          = r^2 * (z.re^2 + z.im^2) := by ring
      rw [hcalc, hnorm]
      calc r^2 * ‖z‖^2 < r^2 * 1 := mul_lt_mul_of_pos_left hz2 hr2
        _ = r^2 := by ring
    · intro hw
      simp only [S, Set.mem_ofPred_eq] at hw
      refine ⟨⟨(w.1 - p.1)/r, (w.2 - p.2)/r⟩, ?_, ?_⟩
      · have hnorm : ‖(⟨(w.1 - p.1)/r, (w.2 - p.2)/r⟩ : ℂ)‖^2
            = ((w.1 - p.1)^2 + (w.2 - p.2)^2) / r^2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          field_simp
        have hlt : ‖(⟨(w.1 - p.1)/r, (w.2 - p.2)/r⟩ : ℂ)‖^2 < 1 := by
          rw [hnorm, div_lt_one (by positivity : (0:ℝ) < r^2)]
          simpa using hw
        have h : ‖(⟨(w.1 - p.1)/r, (w.2 - p.2)/r⟩ : ℂ)‖^2 < (1:ℝ)^2 := by simpa using hlt
        rwa [sq_lt_sq, abs_of_nonneg (norm_nonneg _), abs_one] at h
      · ext <;> simp only [Φ]
        · field_simp; ring
        · field_simp; ring
  -- the closed unit disc of parameters is mapped into the source of `E`
  have hΦclosed : ∀ z : Metric.closedBall (0 : ℂ) 1, Φ (z : ℂ) ∈ E.source := by
    intro z
    apply hεball
    have hnorm : ‖(z : ℂ)‖ ≤ 1 := by
      have hz := z.2
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      simpa using hz
    have hre : |(z : ℂ).re| ≤ 1 := le_trans (Complex.abs_re_le_norm _) hnorm
    have him : |(z : ℂ).im| ≤ 1 := le_trans (Complex.abs_im_le_norm _) hnorm
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : Φ (z : ℂ) - p = (r * (z : ℂ).re, r * (z : ℂ).im) := by
      ext <;> simp [Φ]
    rw [hsub, Prod.norm_def]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hrpos]
    exact max_lt (by nlinarith) (by nlinarith)
  -- the parametrisation of the disc
  let f : Metric.closedBall (0 : ℂ) 1 → R3 := fun z => (E (Φ (z : ℂ)) : R3)
  have hf_cont : Continuous f := by
    have h1 : Continuous fun z : Metric.closedBall (0 : ℂ) 1 => Φ (z : ℂ) :=
      hΦcont.comp continuous_subtype_val
    have h2 : Continuous (E ∘ fun z : Metric.closedBall (0 : ℂ) 1 => Φ (z : ℂ)) :=
      E.continuousOn.comp_continuous h1 (fun z => hΦclosed z)
    exact Continuous.subtype_val h2
  have hf_inj : Function.Injective f := by
    intro z z' hzz
    have h1 : E (Φ (z : ℂ)) = E (Φ (z' : ℂ)) := Subtype.val_injective hzz
    have h2 : Φ (z : ℂ) = Φ (z' : ℂ) := E.injOn (hΦclosed z) (hΦclosed z') h1
    have hre : (z : ℂ).re = (z' : ℂ).re := by
      have h := congrArg Prod.fst h2
      simp only [Φ] at h
      exact mul_left_cancel₀ (ne_of_gt hrpos) (add_left_cancel h)
    have him : (z : ℂ).im = (z' : ℂ).im := by
      have h := congrArg Prod.snd h2
      simp only [Φ] at h
      exact mul_left_cancel₀ (ne_of_gt hrpos) (add_left_cancel h)
    exact Subtype.ext (Complex.ext hre him)
  have hf_mem : ∀ z : Metric.closedBall (0 : ℂ) 1, f z ∈ P.carrier :=
    fun z => (E (Φ (z : ℂ))).2
  -- the interior of the disc is the image of the open Euclidean disc under the local inverse
  have hf_image : f '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1}
      = Subtype.val '' (E '' S) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨E (Φ (z : ℂ)), ⟨Φ (z : ℂ), by rw [← hΦS]; exact ⟨(z : ℂ), hz, rfl⟩, rfl⟩, rfl⟩
    · intro hy
      obtain ⟨u, hu, rfl⟩ := hy
      obtain ⟨v, hv, rfl⟩ := hu
      rw [← hΦS] at hv
      obtain ⟨z, hz, hzv⟩ := hv
      refine ⟨⟨z, ?_⟩, hz, ?_⟩
      · rw [Metric.mem_closedBall, dist_eq_norm]; simpa using le_of_lt hz
      · show (E (Φ z) : R3) = (E v : R3)
        rw [hzv]
  have hf_open : IsOpenInCarrier P (f '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1}) := by
    rw [hf_image]
    have hEimage : IsOpen (E '' S) := E.isOpen_image_of_subset_source hSopen hSsub
    show IsOpen (Subtype.val ⁻¹' (Subtype.val '' (E '' S)) : Set P.carrier)
    rw [Set.preimage_image_eq _ Subtype.val_injective]
    exact hEimage
  refine ⟨{ e := ⟨f, hf_cont⟩, inj := hf_inj, mem := hf_mem, open_interior := hf_open }, ?_⟩
  -- the centre of the disc is `x`
  refine ⟨⟨0, by simp [Metric.mem_closedBall]⟩, ?_, ?_⟩
  · simp
  · show (E (Φ (0 : ℂ)) : R3) = x
    have h0 : Φ (0 : ℂ) = p := by ext <;> simp [Φ]
    rw [h0, hEp]

end Work.SurgeryInvariance.DiscRegion
