import Mathlib
import Submission.Work.Drive.Neutral.StripDiskAux
import Submission.Work.OneDim.circle_gluing_prereq

/-!
# Smoothness of `curvePtAt`

`Work.Drive.Neutral.curvePtAt γ x s = symmC (γ (toCirc (x * exp (sClamp s · I))))` is the complexified point of
the chord endpoint at the circle parameter `x * exp (sClamp s · I)` (with a junk value at `x = 0`).
We prove that it is `C^∞` on `{p : ℂ × ℝ | p.1 ≠ 0}`; the clamped opening `sClamp` is smooth
(`Work.Drive.Neutral.contDiff_sClamp`), which is the only place where the precise definition of
`curvePtAt` enters.

The only non-trivial point is that `z ↦ toCirc z = z / ‖z‖` is smooth as a map `ℂ \ {0} → Circle`
for the *manifold* structure of the circle.  We prove this with the two explicit stereographic
parametrisations of `Work.OneDim`: on `{‖z‖ + z.re ≠ 0}` the point `toCirc z` misses the pole `-1`
and equals `spherePt (sphereCoord (z / ‖z‖))`, and on `{‖z‖ - z.re ≠ 0}` it misses `1` and equals
`spherePt' (sphereCoord' (z / ‖z‖))`.  These two open sets cover `ℂ \ {0}`.
-/

namespace Work.Drive.Neutral

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-! ## The normalised circle point -/

/-- The point of the unit circle in the direction of a complex number, with the junk value `1` at
`0`. -/
def circNorm (z : ℂ) : Circle := if h : z = 0 then Work.OneDim.Q else toCirc z h

lemma circNorm_of_ne {z : ℂ} (hz : z ≠ 0) : circNorm z = toCirc z hz :=
  dif_neg hz

lemma coe_circNorm {z : ℂ} (hz : z ≠ 0) : (circNorm z : ℂ) = z / (‖z‖ : ℂ) := by
  rw [circNorm_of_ne hz]
  rfl

lemma circNorm_ne_Qm {z : ℂ} (hz : z ≠ 0) (h : (z / (‖z‖ : ℂ)).re ≠ -1) :
    circNorm z ≠ Work.OneDim.Qm := by
  intro hq
  have hc := congrArg Complex.re (show (circNorm z : ℂ) = (Work.OneDim.Qm : ℂ) from by rw [hq])
  rw [coe_circNorm hz, Work.OneDim.Qm_coe] at hc
  exact h (by simpa using hc)

lemma circNorm_ne_Q {z : ℂ} (hz : z ≠ 0) (h : (z / (‖z‖ : ℂ)).re ≠ 1) :
    circNorm z ≠ Work.OneDim.Q := by
  intro hq
  have hc := congrArg Complex.re (show (circNorm z : ℂ) = (Work.OneDim.Q : ℂ) from by rw [hq])
  rw [coe_circNorm hz, Work.OneDim.Q_coe] at hc
  exact h (by simpa using hc)

lemma circNorm_eq_spherePt {z : ℂ} (hz : z ≠ 0) (h : (z / (‖z‖ : ℂ)).re ≠ -1) :
    circNorm z = Work.OneDim.spherePt (Work.OneDim.sphereCoord (z / (‖z‖ : ℂ))) := by
  have hne : toCirc z hz ≠ Work.OneDim.Qm := by
    rw [← circNorm_of_ne hz]
    exact circNorm_ne_Qm hz h
  rw [circNorm_of_ne hz]
  rw [← Work.OneDim.spherePt_sphereCoord (toCirc z hz) hne]
  rfl

lemma circNorm_eq_spherePt' {z : ℂ} (hz : z ≠ 0) (h : (z / (‖z‖ : ℂ)).re ≠ 1) :
    circNorm z = Work.OneDim.spherePt' (Work.OneDim.sphereCoord' (z / (‖z‖ : ℂ))) := by
  have hne : toCirc z hz ≠ Work.OneDim.Q := by
    rw [← circNorm_of_ne hz]
    exact circNorm_ne_Q hz h
  rw [circNorm_of_ne hz]
  rw [← Work.OneDim.spherePt'_sphereCoord' (toCirc z hz) hne]
  rfl

/-! ## The two charts -/

lemma contDiffOn_sphereCoord_div {s : Set ℂ} (h0 : ∀ z ∈ s, z ≠ 0)
    (hden : ∀ z ∈ s, (z / (‖z‖ : ℂ)).re ≠ -1) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => Work.OneDim.sphereCoord (z / (‖z‖ : ℂ))) s := by
  have hnorm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => ‖z‖) s :=
    ContDiffOn.norm ℝ contDiffOn_id h0
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) s :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hnorm
  have hcinv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => (((‖z‖ : ℝ) : ℂ))⁻¹) s :=
    hc.inv (fun z hz h => by
      rw [Complex.ofReal_eq_zero] at h
      exact (norm_ne_zero_iff.mpr (h0 z hz)) h)
  have hdiv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => z / (‖z‖ : ℂ)) s :=
    (contDiffOn_id.mul hcinv).congr (fun z hz => by simp [div_eq_mul_inv])
  have him : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => (z / (‖z‖ : ℂ)).im) s :=
    Complex.imCLM.contDiff.comp_contDiffOn hdiv
  have hre : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => 1 + (z / (‖z‖ : ℂ)).re) s :=
    contDiffOn_const.add (Complex.reCLM.contDiff.comp_contDiffOn hdiv)
  have hden' : ∀ z ∈ s, 1 + (z / (‖z‖ : ℂ)).re ≠ 0 := by
    intro z hz hh
    exact hden z hz (by linarith)
  refine (ContDiffOn.div him hre hden').congr (fun z hz => ?_)
  simp only [Pi.div_apply, Work.OneDim.sphereCoord]

lemma contDiffOn_sphereCoord'_div {s : Set ℂ} (h0 : ∀ z ∈ s, z ≠ 0)
    (hden : ∀ z ∈ s, (z / (‖z‖ : ℂ)).re ≠ 1) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => Work.OneDim.sphereCoord' (z / (‖z‖ : ℂ))) s := by
  have hnorm : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => ‖z‖) s :=
    ContDiffOn.norm ℝ contDiffOn_id h0
  have hc : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => ((‖z‖ : ℝ) : ℂ)) s :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hnorm
  have hcinv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => (((‖z‖ : ℝ) : ℂ))⁻¹) s :=
    hc.inv (fun z hz h => by
      rw [Complex.ofReal_eq_zero] at h
      exact (norm_ne_zero_iff.mpr (h0 z hz)) h)
  have hdiv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z : ℂ => z / (‖z‖ : ℂ)) s :=
    (contDiffOn_id.mul hcinv).congr (fun z hz => by simp [div_eq_mul_inv])
  have him : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => (z / (‖z‖ : ℂ)).im) s :=
    Complex.imCLM.contDiff.comp_contDiffOn hdiv
  have hre : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => 1 - (z / (‖z‖ : ℂ)).re) s :=
    contDiffOn_const.sub (Complex.reCLM.contDiff.comp_contDiffOn hdiv)
  have hden' : ∀ z ∈ s, 1 - (z / (‖z‖ : ℂ)).re ≠ 0 := by
    intro z hz hh
    exact hden z hz (by linarith)
  refine (ContDiffOn.div him hre hden').congr (fun z hz => ?_)
  simp only [Pi.div_apply, Work.OneDim.sphereCoord']

/-! ## A cover of `ℂ \ {0}` -/

/-- The open set where the direction of `z` misses the pole `-1`. -/
def goodNeg : Set ℂ := {z : ℂ | ‖z‖ + z.re ≠ 0}

/-- The open set where the direction of `z` misses the pole `1`. -/
def goodPos : Set ℂ := {z : ℂ | ‖z‖ - z.re ≠ 0}

lemma isOpen_goodNeg : IsOpen goodNeg :=
  isOpen_ne.preimage (continuous_norm.add Complex.continuous_re)

lemma isOpen_goodPos : IsOpen goodPos :=
  isOpen_ne.preimage (continuous_norm.sub Complex.continuous_re)

lemma circNorm_eq_spherePt_of_mem_goodNeg {z : ℂ} (hz : z ∈ goodNeg) :
    circNorm z = Work.OneDim.spherePt (Work.OneDim.sphereCoord (z / (‖z‖ : ℂ))) := by
  have hz0 : z ≠ 0 := fun h => hz (by simp [goodNeg, h])
  have hzpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  refine circNorm_eq_spherePt hz0 ?_
  intro h
  rw [Complex.div_ofReal_re] at h
  have h' : z.re = -‖z‖ := by
    rw [div_eq_iff (ne_of_gt hzpos)] at h
    linarith
  exact hz (by show ‖z‖ + z.re = 0; linarith)

lemma circNorm_eq_spherePt'_of_mem_goodPos {z : ℂ} (hz : z ∈ goodPos) :
    circNorm z = Work.OneDim.spherePt' (Work.OneDim.sphereCoord' (z / (‖z‖ : ℂ))) := by
  have hz0 : z ≠ 0 := fun h => hz (by simp [goodPos, h])
  have hzpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hz0
  refine circNorm_eq_spherePt' hz0 ?_
  intro h
  rw [Complex.div_ofReal_re] at h
  have h' : z.re = ‖z‖ := by
    rw [div_eq_iff (ne_of_gt hzpos)] at h
    linarith
  exact hz (by show ‖z‖ - z.re = 0; linarith)

lemma contMDiffOn_circNorm_of_goodNeg :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ((⊤ : ℕ∞) : WithTop ℕ∞) circNorm goodNeg := by
  have h0 : ∀ z ∈ goodNeg, z ≠ 0 := fun z hz h => hz (by simp [goodNeg, h])
  have hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => Work.OneDim.sphereCoord (z / (‖z‖ : ℂ))) goodNeg :=
    contDiffOn_sphereCoord_div h0 (fun z hz => by
      intro h
      rw [Complex.div_ofReal_re] at h
      have hzpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr (h0 z hz)
      have h' : z.re = -‖z‖ := by
        rw [div_eq_iff (ne_of_gt hzpos)] at h
        linarith
      exact hz (by show ‖z‖ + z.re = 0; linarith))
  have hcomp : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.OneDim.spherePt ∘ fun z : ℂ => Work.OneDim.sphereCoord (z / (‖z‖ : ℂ)))
      goodNeg :=
    ContMDiff.comp_contMDiffOn Work.OneDim.contMDiff_spherePt
      (contMDiffOn_iff_contDiffOn.mpr hG)
  refine hcomp.congr (fun z hz => ?_)
  exact circNorm_eq_spherePt_of_mem_goodNeg hz

lemma contMDiffOn_circNorm_of_goodPos :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ((⊤ : ℕ∞) : WithTop ℕ∞) circNorm goodPos := by
  have h0 : ∀ z ∈ goodPos, z ≠ 0 := fun z hz h => hz (by simp [goodPos, h])
  have hG : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℂ => Work.OneDim.sphereCoord' (z / (‖z‖ : ℂ))) goodPos :=
    contDiffOn_sphereCoord'_div h0 (fun z hz => by
      intro h
      rw [Complex.div_ofReal_re] at h
      have hzpos : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr (h0 z hz)
      have h' : z.re = ‖z‖ := by
        rw [div_eq_iff (ne_of_gt hzpos)] at h
        linarith
      exact hz (by show ‖z‖ - z.re = 0; linarith))
  have hcomp : ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (Work.OneDim.spherePt' ∘ fun z : ℂ => Work.OneDim.sphereCoord' (z / (‖z‖ : ℂ)))
      goodPos :=
    ContMDiff.comp_contMDiffOn Work.OneDim.contMDiff_spherePt'
      (contMDiffOn_iff_contDiffOn.mpr hG)
  refine hcomp.congr (fun z hz => ?_)
  exact circNorm_eq_spherePt'_of_mem_goodPos hz

/-- The normalised circle point is `C^∞` on the complement of the origin. -/
theorem contMDiffOn_circNorm :
    ContMDiffOn 𝓘(ℝ, ℂ) (𝓡 1) ((⊤ : ℕ∞) : WithTop ℕ∞) circNorm {z : ℂ | z ≠ 0} := by
  refine contMDiffOn_of_locally_contMDiffOn (s := {z : ℂ | z ≠ 0}) ?_
  intro z₀ hz₀
  by_cases hm : ‖z₀‖ + z₀.re = 0
  · refine ⟨goodPos, isOpen_goodPos, ?_, ?_⟩
    · have hzpos : (0 : ℝ) < ‖z₀‖ := norm_pos_iff.mpr hz₀
      show ‖z₀‖ - z₀.re ≠ 0
      linarith
    · exact contMDiffOn_circNorm_of_goodPos.mono Set.inter_subset_right
  · exact ⟨goodNeg, isOpen_goodNeg, hm,
      contMDiffOn_circNorm_of_goodNeg.mono Set.inter_subset_right⟩

/-! ## `curvePtAt` -/

/-- The circle parameter at which `curvePtAt` evaluates `γ`, for a smooth clamped opening `h`. -/
def circArgOf (h : ℝ → ℝ) (p : ℂ × ℝ) : ℂ := p.1 * Complex.exp ((h p.2) * Complex.I)

lemma contDiff_circArgOf {h : ℝ → ℝ} (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (circArgOf h) := by
  unfold circArgOf
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℂ × ℝ => ((h p.2 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (hh.comp contDiff_snd)
  have h3 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℂ × ℝ => ((h p.2 : ℝ) : ℂ) * Complex.I) := h2.mul contDiff_const
  exact contDiff_fst.mul (Complex.contDiff_exp.comp h3)

/-- **Smoothness of the normalised curve point.**  For any smooth `h`, the map
`p ↦ circNorm (p.1 * exp (h p.2 · I))` is `C^∞` on `{p | p.1 ≠ 0}`. -/
theorem contMDiffOn_circNorm_comp {h : ℝ → ℝ}
    (hh : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) h) :
    ContMDiffOn 𝓘(ℝ, ℂ × ℝ) (𝓡 1) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℂ × ℝ => circNorm (circArgOf h p)) {p : ℂ × ℝ | p.1 ≠ 0} := by
  have hg : ContMDiffOn 𝓘(ℝ, ℂ × ℝ) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) (circArgOf h)
      {p : ℂ × ℝ | p.1 ≠ 0} :=
    ((contMDiff_iff_contDiff (𝕜 := ℝ) (E := ℂ × ℝ) (E' := ℂ)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).mpr (contDiff_circArgOf hh)).contMDiffOn
  have hmaps : {p : ℂ × ℝ | p.1 ≠ 0} ⊆ circArgOf h ⁻¹' {z : ℂ | z ≠ 0} := by
    intro p hp
    simp only [Set.mem_preimage, Set.mem_setOf_eq, circArgOf]
    exact mul_ne_zero hp (Complex.exp_ne_zero _)
  exact contMDiffOn_circNorm.comp hg hmaps

lemma curvePtAt_eq (γ : Circle → ℝ × ℝ) {p : ℂ × ℝ} (hp : p.1 ≠ 0) :
    curvePtAt γ p.1 p.2 = symmC (γ (circNorm (circArgOf sClamp p))) := by
  have hz : circArgOf sClamp p ≠ 0 := by
    simp only [circArgOf]
    exact mul_ne_zero hp (Complex.exp_ne_zero _)
  simp only [curvePtAt]
  rw [dif_neg hp, circNorm_of_ne hz]
  exact congrArg (fun z => symmC (γ z)) (Subtype.ext rfl)

open Manifold in
open scoped Manifold ContDiff in
theorem contDiffOn_curvePtAt (γ : Circle → ℝ × ℝ)
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℂ × ℝ => curvePtAt γ p.1 p.2) {p : ℂ × ℝ | p.1 ≠ 0} := by
  have hF : ContMDiffOn 𝓘(ℝ, ℂ × ℝ) (𝓡 1) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℂ × ℝ => circNorm (circArgOf sClamp p)) {p : ℂ × ℝ | p.1 ≠ 0} :=
    contMDiffOn_circNorm_comp contDiff_sClamp
  have hcomp : ContMDiffOn 𝓘(ℝ, ℂ × ℝ) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (γ ∘ fun p : ℂ × ℝ => circNorm (circArgOf sClamp p)) {p : ℂ × ℝ | p.1 ≠ 0} :=
    hγ.contMDiff.comp_contMDiffOn hF
  have hcd : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℂ × ℝ => symmC ((γ ∘ fun p : ℂ × ℝ => circNorm (circArgOf sClamp p)) p))
      {p : ℂ × ℝ | p.1 ≠ 0} :=
    contDiff_symmC.comp_contDiffOn (contMDiffOn_iff_contDiffOn.mp hcomp)
  refine hcd.congr (fun p hp => ?_)
  simp only [Function.comp_apply]
  exact curvePtAt_eq γ hp

end

end Work.Drive.Neutral
