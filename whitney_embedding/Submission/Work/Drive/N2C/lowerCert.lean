import Mathlib
import Submission.Work.Drive.N2C.defs
import Submission.Work.Drive.N2Lead.isCertifiedAt_of_starRegions
import Submission.Work.Drive.N2Lead.saddlePacket
import Submission.Work.Drive.N2Lead.polarCurve_rows

/-!
# The lower (anchor-level) certificate of the saddle packet

`Work.Drive.N2C.IsCertifiedAt f u W` says that the picture `W` restricted to the level `f = u` is
isotopic, through pictures of that level, to a disjoint round configuration read through a
parametrisation of the level.  The saddle window `D2` of the coherent-window design
(`Submission/Work/Drive/N2Lead/NOTES_LEAD_saddlePacket.md`) needs such a certificate at the two
collar levels `f p ∓ 3η/2`.

This file proves the certificate at the **lower** collar level `a = f p - 3η/2` for the packet's
picture `A`: the marked component of the level is drawn by the *planar polar curve*
`C₀ t = cE3 (r (Θ t) · exp (i Θ t))` (with `r` the profile of
`Work.Drive.N2Lead.mobius_lowerProfile` and `Θ` the packet's angle function) and the other
components by the parked round circles `farCurve` (`(-20, 20 + 5j, 1) + ang t`).  The planar polar
curve is star-shaped about `0` on the region `ball 0 5` and the far circles are round of radius `1`
about their (far away) centres, so the star-region engine
`Work.Drive.N2Lead.isCertifiedAt_of_starRegions` applies with the families of regions

  `Ω i = ball 0 5` (centre `0`, the marked component) and
  `Ω j = ball (proj2 (farPos n j)) 2` (centre `proj2 (farPos n j)`, the `j`-th far circle).

The two derivative (`hrate`) rows are the *radial-rate* rows of the two kinds of curves — the polar
curve has `Θ' ≠ 0` and the round circle turns — and the `hhit` rows use the direction `1`: the
positive real axis meets the marked curve exactly at `Θ ≡ 0 (mod 2π)`, and the horizontal half-line
through a far centre meets that circle exactly once.

The consumer (`Work.Drive.N2Lead.exists_certifiedWindow_saddle_oneComp`) supplies
`W = A` on the level (the packet's rows), with `w i = C₀` on the marked component and
`w j = proj2 ∘ farCurve n j` on the others.
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set Filter

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
  [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

section Rows

/-- The squared norm of the planar projection, from the two coordinates. -/
lemma norm_proj2_sq (v : Work.Drive.N2Lead.E3) :
    ‖Work.Drive.N2Lead.proj2 v‖ ^ 2 = (v 0) ^ 2 + (v 1) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Work.Drive.N2Lead.proj2]
  ring

/-- The planar projection of the parking spot `(-20, 20 + 5j, 1)`. -/
lemma proj2_farPos (n : ℕ) (j : Fin n) :
    Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n j)
      = (⟨(-20 : ℝ), 20 + 5 * ((j : ℕ) : ℝ)⟩ : ℂ) := by
  apply Complex.ext <;> simp [Work.Drive.N2Lead.proj2, Work.Drive.N2Lead.farPos_apply]

/-- The planar projection of the far circle: a round circle of radius `1` about the parking spot. -/
lemma proj2_farCurve (n : ℕ) (j : Fin n) (t : ℝ) :
    Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farCurve n j t)
      = Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n j)
        + Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang t) := by
  rw [Work.Drive.N2Lead.farCurve_eq, Work.Drive.N2Lead.proj2_add]

/-- The planar projection of the round picture is `exp (i 2πt)`. -/
lemma proj2_ang (t : ℝ) :
    Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang t)
      = Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := by
  rw [Work.Drive.N2.ang, Work.Drive.N2Lead.proj2_roundPic, Complex.exp_ofReal_mul_I]
  apply Complex.ext
  · rw [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    simp
  · rw [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
    simp

lemma norm_proj2_ang (t : ℝ) : ‖Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang t)‖ = 1 := by
  rw [proj2_ang, Complex.norm_exp]
  norm_num

lemma norm_proj2_farPos_ge (n : ℕ) (j : Fin n) :
    19 ≤ ‖Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n j)‖ := by
  have h : (‖Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n j)‖) ^ 2
      = (20 : ℝ) ^ 2 + (20 + 5 * ((j : ℕ) : ℝ)) ^ 2 := by
    rw [norm_proj2_sq]
    simp [Work.Drive.N2Lead.farPos_apply]
  nlinarith [norm_nonneg (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n j)),
    sq_nonneg (20 + 5 * ((j : ℕ) : ℝ))]


end Rows

section Deriv

/-- The derivative of `t ↦ 2πt`. -/
lemma hasDerivAt_two_pi_mul (t : ℝ) :
    HasDerivAt (fun u : ℝ => 2 * Real.pi * u) (2 * Real.pi) t := by
  simpa using (hasDerivAt_id t).const_mul (2 * Real.pi)

/-- **The derivative of the planar projection of the round picture**: the velocity of the round
circle is the rotation of the position by `π/2`, scaled by `2π`. -/
lemma hasDerivAt_proj2_ang (t : ℝ) :
    HasDerivAt (fun u : ℝ => Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang u))
      ((2 * Real.pi : ℂ) * Complex.I * Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang t)) t := by
  have h1 : HasDerivAt (fun u : ℝ => ((2 * Real.pi * u : ℝ) : ℂ))
      ((2 * Real.pi : ℝ) : ℂ) t :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_two_pi_mul t)
  have hlin : HasDerivAt (fun u : ℝ => ((2 * Real.pi * u : ℝ) : ℂ) * Complex.I)
      (((2 * Real.pi : ℝ) : ℂ) * Complex.I) t := h1.mul_const Complex.I
  have hexp : HasDerivAt (fun u : ℝ => Complex.exp (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
        * (((2 * Real.pi : ℝ) : ℂ) * Complex.I)) t :=
    (Complex.hasDerivAt_exp _).comp t hlin
  have hfun : (fun u : ℝ => Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang u))
      = (fun u : ℝ => Complex.exp (((2 * Real.pi * u : ℝ) : ℂ) * Complex.I)) :=
    funext fun u => proj2_ang u
  rw [hfun, proj2_ang t]
  refine hexp.congr_deriv ?_
  push_cast
  ring

/-- The derivative of the planar projection of a far circle. -/
lemma hasDerivAt_proj2_farCurve (n : ℕ) (j : Fin n) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farCurve n j u))
      ((2 * Real.pi : ℂ) * Complex.I * Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang t)) t := by
  have hfun : (fun u : ℝ => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farCurve n j u))
      = (fun u : ℝ => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n j)
          + Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang u)) := by
    funext u
    rw [proj2_farCurve]
  rw [hfun]
  exact (hasDerivAt_proj2_ang t).const_add _

/-- **The derivative of the packet's polar curve.** -/
lemma hasDerivAt_polar {r Θ : ℝ → ℝ} (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r)
    (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => (r (Θ u) : ℂ) * Complex.exp (((Θ u : ℝ) : ℂ) * Complex.I))
      ((Complex.ofReal (deriv r (Θ t)) + Complex.I * (r (Θ t) : ℂ))
        * Complex.ofReal (deriv Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)) t := by
  have hdr : HasDerivAt r (deriv r (Θ t)) (Θ t) :=
    (hr.contDiffAt.differentiableAt (by simp)).hasDerivAt
  have hdΘ : HasDerivAt Θ (deriv Θ t) t :=
    (hΘ.contDiffAt.differentiableAt (by simp)).hasDerivAt
  have hcomp : HasDerivAt (fun u : ℝ => r (Θ u)) (deriv r (Θ t) * deriv Θ t) t :=
    hdr.comp t hdΘ
  have hcast : HasDerivAt (fun u : ℝ => ((r (Θ u) : ℝ) : ℂ))
      (Complex.ofReal (deriv r (Θ t) * deriv Θ t)) t :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hcomp
  have hcastΘ : HasDerivAt (fun u : ℝ => ((Θ u : ℝ) : ℂ)) (Complex.ofReal (deriv Θ t)) t :=
    Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hdΘ
  have harg : HasDerivAt (fun u : ℝ => ((Θ u : ℝ) : ℂ) * Complex.I)
      (Complex.ofReal (deriv Θ t) * Complex.I) t := hcastΘ.mul_const Complex.I
  have hexp : HasDerivAt (fun u : ℝ => Complex.exp (((Θ u : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)
        * (Complex.ofReal (deriv Θ t) * Complex.I)) t :=
    (Complex.hasDerivAt_exp _).comp t harg
  have hprod := hcast.mul hexp
  refine hprod.congr_deriv ?_
  push_cast
  ring

/-- **The basis form of the derivative of the polar curve.** -/
lemma deriv_polar {r Θ : ℝ → ℝ} (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r)
    (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ) (t : ℝ) :
    deriv (fun u : ℝ => (r (Θ u) : ℂ) * Complex.exp (((Θ u : ℝ) : ℂ) * Complex.I)) t
      = (Complex.ofReal (deriv r (Θ t)) + Complex.I * (r (Θ t) : ℂ))
        * Complex.ofReal (deriv Θ t) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I) :=
  (hasDerivAt_polar hr hΘ t).deriv

/-- **The polar curve has no radial derivative**: its velocity is never a real multiple of its
position (the angular rate `Θ'` is nonzero). -/
lemma polar_deriv_not_radial {r Θ : ℝ → ℝ} (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r)
    (hrpos : ∀ φ : ℝ, 0 < r φ) (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΘderiv : ∀ t : ℝ, deriv Θ t ≠ 0) (t : ℝ) :
    ¬ ∃ s : ℝ, deriv (fun u : ℝ => (r (Θ u) : ℂ) * Complex.exp (((Θ u : ℝ) : ℂ) * Complex.I)) t
      = s • ((r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)) := by
  rintro ⟨s, hs⟩
  rw [deriv_polar hr hΘ t] at hs
  set E : ℂ := Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I) with hEdef
  have hE : E ≠ 0 := Complex.exp_ne_zero _
  have h2 : (Complex.ofReal (deriv r (Θ t)) + Complex.I * (r (Θ t) : ℂ))
      * Complex.ofReal (deriv Θ t) = (s : ℂ) * (r (Θ t) : ℂ) := by
    refine mul_right_cancel₀ hE ?_
    simpa [E, smul_eq_mul, mul_assoc] using hs
  have him := congrArg Complex.im h2
  simp only [Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, zero_mul, mul_zero, add_zero] at him
  have hrp : 0 < r (Θ t) := hrpos _
  have hd : deriv Θ t = 0 := by
    have hmul : r (Θ t) * deriv Θ t = 0 := by linarith [him]
    exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hrp)
  exact hΘderiv t hd

/-- **The far circle has no radial derivative** (about its own centre): the velocity is the rotation
of the radius vector. -/
lemma farCurve_deriv_not_radial (n : ℕ) (j : Fin n) (t : ℝ) :
    ¬ ∃ s : ℝ, deriv (fun u : ℝ => Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farCurve n j u)) t
      = s • (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farCurve n j t)
        - Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n j)) := by
  rintro ⟨s, hs⟩
  rw [(hasDerivAt_proj2_farCurve n j t).deriv, proj2_farCurve n j t, add_sub_cancel_left] at hs
  have hZ : Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang t) ≠ 0 := by
    intro h
    have h1 := norm_proj2_ang t
    rw [h] at h1
    simp at h1
  have hs' : ((2 * Real.pi : ℂ) * Complex.I) * Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang t)
      = (s : ℂ) * Work.Drive.N2Lead.proj2 (Work.Drive.N2.ang t) := by
    simpa [smul_eq_mul] using hs
  have h2 : ((2 * Real.pi : ℂ) * Complex.I) = (s : ℂ) := mul_right_cancel₀ hZ hs'
  have him := congrArg Complex.im h2
  simp only [Complex.mul_im, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, add_zero, sub_zero] at him
  norm_num at him

end Deriv

section Aux

/-- From `(r : ℂ) * exp (iθ) = (s : ℂ)` with `r, s > 0`: the exponential factor is `1`. -/
lemma exp_eq_one_of_mul_eq_pos {r s θ : ℝ} (hr : 0 < r) (hs : 0 < s)
    (h : (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) = (s : ℂ)) :
    Complex.exp ((θ : ℂ) * Complex.I) = 1 := by
  have h1 : ‖(r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)‖ = r := by
    rw [norm_mul, Complex.norm_exp]
    simp [Complex.ofReal_re, Real.norm_eq_abs, abs_of_pos hr]
  have h2 : ‖(s : ℂ)‖ = s := by
    simp [Real.norm_eq_abs, abs_of_pos hs]
  have hrs : r = s := by rw [← h1, h, h2]
  refine mul_left_cancel₀ (show (r : ℂ) ≠ 0 by exact_mod_cast (ne_of_gt hr)) ?_
  rw [h, mul_one, hrs]

/-- `exp (iθ) = 1` iff `θ` is an integer multiple of `2π`. -/
lemma exp_eq_one_iff_int_mul (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) = 1 ↔ ∃ m : ℤ, θ = m * (2 * Real.pi) := by
  constructor
  · intro h
    rw [Complex.exp_ofReal_mul_I] at h
    have hre := congrArg Complex.re h
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, sub_zero, add_zero] at hre
    norm_num at hre
    obtain ⟨m, hm⟩ := (Real.cos_eq_one_iff θ).mp hre
    exact ⟨m, hm.symm⟩
  · rintro ⟨m, rfl⟩
    refine Complex.exp_eq_one_iff.mpr ⟨m, ?_⟩
    push_cast
    ring

/-- `r (m · 2π) = r 0` for an integer `m`, from `2π`-periodicity. -/
lemma periodic_two_pi_int_mul {r : ℝ → ℝ} (hrper : ∀ φ : ℝ, r (φ + 2 * Real.pi) = r φ)
    (m : ℤ) : r ((m : ℝ) * (2 * Real.pi)) = r 0 := by
  have h : Function.Periodic r (2 * Real.pi) := hrper
  have h2 := h.int_mul m 0
  simpa using h2

end Aux



section Regions



/-- The region family of the lower certificate: the marked component `i` gets the disc `ball 0 5`,
every other component `k` the disc of radius `2` about the planar projection of its parking spot. -/
noncomputable def polarRegions (n : ℕ) (i : Fin n) : Fin n → Set ℂ :=
  fun k => if k = i then Metric.ball 0 5 else Metric.ball (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n k)) 2

/-- The centres of the region family. -/
noncomputable def polarCentres (n : ℕ) (i : Fin n) : Fin n → ℂ :=
  fun k => if k = i then 0 else Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n k)

lemma mem_polarRegions_iff {n : ℕ} (i k : Fin n) (z : ℂ) :
    z ∈ polarRegions n i k ↔
      (k = i ∧ z ∈ Metric.ball 0 5)
        ∨ (k ≠ i ∧ z ∈ Metric.ball (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n k)) 2) := by
  by_cases hk : k = i
  · simp [polarRegions, hk]
  · simp [polarRegions, hk]

lemma mem_polarCentres_iff {n : ℕ} (i k : Fin n) (z : ℂ) :
    polarCentres n i k = z ↔ (k = i ∧ (0 : ℂ) = z) ∨ (k ≠ i ∧ Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n k) = z) := by
  by_cases hk : k = i
  · simp [polarCentres, hk]
  · simp [polarCentres, hk]

lemma isOpen_convex_polarRegions (n : ℕ) (i : Fin n) :
    ∀ k : Fin n, IsOpen (polarRegions n i k) ∧ Convex ℝ (polarRegions n i k) := by
  intro k
  by_cases hk : k = i
  · rw [polarRegions, if_pos hk]
    exact ⟨Metric.isOpen_ball, convex_ball _ _⟩
  · rw [polarRegions, if_neg hk]
    exact ⟨Metric.isOpen_ball, convex_ball _ _⟩

lemma closedBall_subset_polarRegions (n : ℕ) (i : Fin n) :
    ∀ k : Fin n, Metric.closedBall (polarCentres n i k) 1 ⊆ polarRegions n i k := by
  intro k
  by_cases hk : k = i
  · rw [polarRegions, polarCentres, if_pos hk, if_pos hk]
    intro z hz
    have h := Metric.mem_closedBall.mp hz
    rw [dist_eq_norm, sub_zero] at h
    rw [Metric.mem_ball, dist_eq_norm, sub_zero]
    linarith
  · rw [polarRegions, polarCentres, if_neg hk, if_neg hk]
    intro z hz
    rw [Metric.mem_ball]
    exact lt_of_le_of_lt (Metric.mem_closedBall.mp hz) (by norm_num)

/-- The distance between two distinct parking spots' planar projections is at least `5`. -/
lemma dist_proj2_farPos_ge {n : ℕ} {j k : Fin n} (h : j ≠ k) :
    5 ≤ dist (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n j)) (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n k)) := by
  rw [dist_eq_norm]
  have him : (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n j) - Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n k)).im
      = 5 * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) := by
    rw [proj2_farPos, proj2_farPos, Complex.sub_im]
    simp
    ring
  have h1 := Complex.abs_im_le_norm (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n j) - Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n k))
  rw [him] at h1
  have hne : (((j : ℕ) : ℝ)) ≠ (((k : ℕ) : ℝ)) := by
    intro hh
    exact h (Fin.ext (by exact_mod_cast hh))
  have h2 : 1 ≤ |(((j : ℕ) : ℝ) - ((k : ℕ) : ℝ))| := by
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have h1 : ((j : ℕ) : ℝ) + 1 ≤ ((k : ℕ) : ℝ) := by
        have h3 : (j : ℕ) < (k : ℕ) := by exact_mod_cast hlt
        exact_mod_cast (by omega : (j : ℕ) + 1 ≤ (k : ℕ))
      rw [abs_of_neg (by linarith)]
      linarith
    · have h1 : ((k : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
        have h3 : (k : ℕ) < (j : ℕ) := by exact_mod_cast hlt
        exact_mod_cast (by omega : (k : ℕ) + 1 ≤ (j : ℕ))
      rw [abs_of_pos (by linarith)]
      linarith
  have h3 : |5 * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ))| = 5 * |(((j : ℕ) : ℝ) - ((k : ℕ) : ℝ))| := by
    rw [abs_mul]; norm_num
  rw [h3] at h1
  linarith

lemma pairwiseDisjoint_polarRegions (n : ℕ) (i : Fin n) :
    Pairwise fun k l : Fin n => Disjoint (polarRegions n i k) (polarRegions n i l) := by
  intro k l hkl
  rw [Set.disjoint_left]
  intro z hzk hzl
  rw [mem_polarRegions_iff] at hzk hzl
  have hfar_ge : 19 ≤ ‖Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n l)‖ := norm_proj2_farPos_ge n l
  have hfar_ge' : 19 ≤ ‖Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n k)‖ := norm_proj2_farPos_ge n k
  have htri : ∀ a b : ℂ, ‖a‖ - ‖b‖ ≤ ‖a - b‖ := by
    intro a b
    have h := norm_add_le (a - b) b
    rw [sub_add_cancel] at h
    linarith
  rcases hzk with ⟨hk, hzk⟩ | ⟨hk, hzk⟩
  · rcases hzl with ⟨hl, hzl⟩ | ⟨hl, hzl⟩
    · exact hkl (hk.trans hl.symm)
    · have h1 : ‖z‖ < 5 := by simpa [Metric.mem_ball, dist_zero_right] using hzk
      have h2 : ‖z - Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n l)‖ < 2 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hzl
      have h3 := htri (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n l)) z
      rw [norm_sub_rev] at h3
      linarith
  · rcases hzl with ⟨hl, hzl⟩ | ⟨hl, hzl⟩
    · have h1 : ‖z‖ < 5 := by simpa [Metric.mem_ball, dist_zero_right] using hzl
      have h2 : ‖z - Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n k)‖ < 2 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hzk
      have h3 := htri (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n k)) z
      rw [norm_sub_rev] at h3
      linarith
    · have h1 : ‖z - Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n k)‖ < 2 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hzk
      have h2 : ‖z - Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n l)‖ < 2 := by
        simpa [Metric.mem_ball, dist_eq_norm] using hzl
      have h4 : dist (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n k)) (Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n l)) ≤
          ‖z - Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n k)‖ + ‖z - Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n l)‖ := by
        rw [dist_eq_norm]
        calc ‖Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n k) - Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n l)‖
            = ‖(Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n k) - z) + (z - Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n l))‖ := by ring_nf
          _ ≤ ‖Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n k) - z‖ + ‖z - Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n l)‖ := norm_add_le _ _
          _ = ‖z - Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n k)‖ + ‖z - Work.Drive.N2Lead.proj2 (Work.Drive.N2Lead.farPos n l)‖ := by rw [norm_sub_rev]
      have h5 := dist_proj2_farPos_ge (n := n) (j := k) (k := l) hkl
      linarith

end Regions


section Transport

open Work.Drive.N2Lead (proj2 farPos farCurve)

variable {f : M → ℝ} {u : ℝ}

/-- Real scalar multiplication of `ℂ` is complex multiplication by the coercion. -/
lemma real_smul_eq_mul (c : ℝ) (z : ℂ) : c • z = Complex.ofReal c * z := by
  rw [Algebra.smul_def]; rfl

/-- Division of a real scalar becomes division of the coerced scalar. -/
lemma smul_div_eq (c r : ℝ) (z : ℂ) (hr : r ≠ 0) : (c / r) • z = (c • z) / (r : ℂ) := by
  rw [real_smul_eq_mul, real_smul_eq_mul, Complex.ofReal_div]
  field_simp


lemma im_proj2_ang (t : ℝ) :
    (proj2 (Work.Drive.N2.ang t)).im = Real.sin (2 * Real.pi * t) := by
  rw [Work.Drive.N2.ang, Work.Drive.N2Lead.proj2_roundPic]

lemma re_proj2_ang (t : ℝ) :
    (proj2 (Work.Drive.N2.ang t)).re = Real.cos (2 * Real.pi * t) := by
  rw [Work.Drive.N2.ang, Work.Drive.N2Lead.proj2_roundPic]

lemma im_proj2_farCurve (n : ℕ) (j : Fin n) (t : ℝ) :
    (proj2 (farCurve n j t)).im = (20 + 5 * ((j : ℕ) : ℝ)) + Real.sin (2 * Real.pi * t) := by
  rw [proj2_farCurve, proj2_farPos, Complex.add_im, im_proj2_ang]

lemma norm_proj2_farCurve_ge (n : ℕ) (j : Fin n) (t : ℝ) :
    19 ≤ ‖proj2 (farCurve n j t)‖ := by
  have h1 := Complex.abs_im_le_norm (proj2 (farCurve n j t))
  rw [im_proj2_farCurve] at h1
  have h2 : -1 ≤ Real.sin (2 * Real.pi * t) := Real.neg_one_le_sin _
  have h3 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
  have h4 := abs_le.mp h1
  nlinarith [h4.1]

lemma proj2_farCurve_sub (n : ℕ) (j : Fin n) (t : ℝ) :
    proj2 (farCurve n j t) - proj2 (farPos n j) = proj2 (Work.Drive.N2.ang t) := by
  rw [proj2_farCurve, add_sub_cancel_left]

/-- **The chain rule on a level curve**: the derivative of the picture along the level, in terms of
the parametrisation of the component. -/
lemma mfderiv_levelCurve_eq_deriv {W : M → Work.Drive.N2Lead.E3} {n : ℕ}
    (L : Work.Drive.N2C.LevelCurves f u n) {w : Fin n → ℝ → ℂ}
    (hWsm : ∀ y : M, f y = u → ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) W y)
    (hw : ∀ (j : Fin n) (t : ℝ), proj2 (W (L.γ j t)) = w j t)
    (j : Fin n) (s t₀ : ℝ) :
    mfderiv (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => proj2 (W z)) (L.γ j s)
        (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ j) s t₀)
      = deriv (w j) s * (t₀ : ℂ) := by
  have hg : MDifferentiableAt (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => proj2 (W z)) (L.γ j s) :=
    Work.Drive.N2Lead.proj2CLM.mdifferentiableAt.comp _
      ((hWsm _ (L.val j s)).mdifferentiableAt (by simp))
  have hf : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2) (L.γ j) s :=
    (L.sm j).contMDiffAt.mdifferentiableAt (by simp)
  have hchain := mfderiv_comp_apply (I := 𝓘(ℝ,ℝ)) (I' := 𝓡 2) (I'' := 𝓘(ℝ,ℂ)) s
    (f := L.γ j) (g := fun z : M => proj2 (W z)) hg hf t₀
  have hcomp : ((fun z : M => proj2 (W z)) ∘ L.γ j) = fun u : ℝ => proj2 (W (L.γ j u)) := rfl
  rw [hcomp] at hchain
  rw [← hchain]
  have hfun : (fun u : ℝ => proj2 (W (L.γ j u))) = w j := funext fun u => hw j u
  rw [hfun]
  rw [mfderiv_eq_fderiv]
  calc (fderiv ℝ (w j) s) t₀ = (fderiv ℝ (w j) s) (t₀ • (1 : ℝ)) := by rw [smul_eq_mul, mul_one]
    _ = t₀ • (fderiv ℝ (w j) s) 1 := by rw [map_smul]
    _ = t₀ • deriv (w j) s := by rw [fderiv_apply_one_eq_deriv]
    _ = deriv (w j) s * (t₀ : ℂ) := by
      rw [Algebra.smul_def]
      exact mul_comm _ _

/-- The polar curve has no radial derivative even after multiplying the velocity by a nonzero real
factor. -/
lemma polar_deriv_mul_not_radial {r Θ : ℝ → ℝ} (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r)
    (hrpos : ∀ φ : ℝ, 0 < r φ) (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hΘderiv : ∀ t : ℝ, deriv Θ t ≠ 0) (t t₀ : ℝ) (ht : t₀ ≠ 0) :
    ¬ ∃ c : ℝ, deriv (fun u : ℝ => (r (Θ u) : ℂ) * Complex.exp (((Θ u : ℝ) : ℂ) * Complex.I)) t
        * (t₀ : ℂ)
      = c • ((r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)) := by
  rintro ⟨c, hc⟩
  refine polar_deriv_not_radial hr hrpos hΘ hΘderiv t ⟨c / t₀, ?_⟩
  have ht₀ : ((t₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht
  have hsm : (c / t₀) • ((r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))
      = (c • ((r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))) / (t₀ : ℂ) :=
    smul_div_eq c t₀ _ ht
  rw [hsm]
  rw [eq_div_iff ht₀]
  exact hc

/-- The far circle has no radial derivative about its own centre, even after multiplying the
velocity by a nonzero real factor. -/
lemma farCurve_deriv_mul_not_radial (n : ℕ) (j : Fin n) (t t₀ : ℝ) (ht : t₀ ≠ 0) :
    ¬ ∃ c : ℝ, deriv (fun u : ℝ => proj2 (farCurve n j u)) t * (t₀ : ℂ)
      = c • (proj2 (farCurve n j t) - proj2 (farPos n j)) := by
  rintro ⟨c, hc⟩
  refine farCurve_deriv_not_radial n j t ⟨c / t₀, ?_⟩
  have ht₀ : ((t₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht
  have hsm : (c / t₀) • (proj2 (farCurve n j t) - proj2 (farPos n j))
      = (c • (proj2 (farCurve n j t) - proj2 (farPos n j))) / (t₀ : ℂ) :=
    smul_div_eq c t₀ _ ht
  rw [hsm]
  rw [eq_div_iff ht₀]
  exact hc

end Transport


section Main

open Work.Drive.N2Lead (proj2 farPos farCurve)

/-- The norm of a coerced real. -/
lemma norm_ofReal_complex (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by
  rw [Complex.norm_def, Complex.normSq_ofReal]
  have h : x * x = |x| * |x| := by rw [← sq, ← sq]; exact (sq_abs x).symm
  rw [h, Real.sqrt_mul_self (abs_nonneg x)]

/-- The imaginary part of a far circle minus a parking spot's projection. -/
lemma im_proj2_farCurve_sub_farPos (n : ℕ) (j k : Fin n) (t : ℝ) :
    (proj2 (farCurve n j t) - proj2 (farPos n k)).im
      = 5 * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) + Real.sin (2 * Real.pi * t) := by
  rw [proj2_farCurve, proj2_farPos, proj2_farPos, Complex.sub_im, Complex.add_im, im_proj2_ang]
  simp
  ring

/-- The real part of a far circle. -/
lemma re_proj2_farCurve (n : ℕ) (j : Fin n) (t : ℝ) :
    (proj2 (farCurve n j t)).re = (-20 : ℝ) + Real.cos (2 * Real.pi * t) := by
  rw [proj2_farCurve, proj2_farPos, Complex.add_re, re_proj2_ang]

/-- The imaginary part of a parking spot's projection. -/
lemma im_proj2_farPos (n : ℕ) (k : Fin n) :
    (proj2 (farPos n k)).im = 20 + 5 * ((k : ℕ) : ℝ) := by
  rw [proj2_farPos]

/-- **The lower certificate of the saddle packet** (the split case). -/
theorem isCertifiedAt_of_polarPacket
    {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (𝓡 2) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {f : M → ℝ} (hf : ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) f) {u : ℝ}
    (hreg : ∀ x : M, f x = u → ¬ Work.Drive.Morse.IsCritical f x)
    {W : M → Work.Drive.N2Lead.E3}
    (hW : IsLevelIsotopy f u (fun _ : ℝ => W))
    {n : ℕ} (L : LevelCurves f u n) (i : Fin n)
    {r Θ : ℝ → ℝ} (hr : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r)
    (hrpos : ∀ φ : ℝ, 0 < r φ) (hrper : ∀ φ : ℝ, r (φ + 2 * Real.pi) = r φ)
    (hrb : ∀ φ : ℝ, r φ ≤ 3)
    (hΘ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ) (hΘmono : StrictMono Θ)
    (hΘderiv : ∀ t : ℝ, deriv Θ t ≠ 0) (hΘper : ∀ t : ℝ, Θ (t + 1) = Θ t + 2 * Real.pi)
    {w : Fin n → ℝ → ℂ}
    (hw : ∀ (j : Fin n) (t : ℝ), proj2 (W (L.γ j t)) = w j t)
    (hwi : ∀ t : ℝ, w i t = (r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I))
    (hwj : ∀ (j : Fin n), j ≠ i → ∀ t : ℝ,
      w j t = proj2 (farCurve n j t)) :
    IsCertifiedAt f u W := by
  classical
  have hWsm : ∀ y : M, f y = u → ContMDiffAt (𝓡 2) (𝓡 3) ((⊤ : ℕ∞) : WithTop ℕ∞) W y :=
    fun y hy => (hW.1 0 y hy).comp y (contMDiffAt_const.prodMk contMDiffAt_id)
  -- the polar curve and its norm
  have hnormP : ∀ t : ℝ, ‖(r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)‖
      = r (Θ t) := by
    intro t
    rw [norm_mul, Complex.norm_exp, norm_ofReal_complex, abs_of_pos (hrpos _)]
    simp
  have hpol := Work.Drive.N2Lead.polarCurve_rows hr hrpos hrper hΘ hΘmono hΘderiv hΘper
  have hwinj : ∀ s t : ℝ, w i s = w i t → ∃ k : ℤ, s = t + k := by
    intro s t hst
    refine hpol.2.2.1 s t ?_
    simpa [hwi s, hwi t] using hst
  have hnormi : ∀ t : ℝ, ‖w i t‖ ≤ 3 := by
    intro t
    rw [hwi t, hnormP t]
    exact hrb _
  have hrate_i : ∀ s t₀ : ℝ, t₀ ≠ 0 → ¬ ∃ c : ℝ, deriv (w i) s * (t₀ : ℂ) = c • (w i s) := by
    intro s t₀ ht₀
    have h := polar_deriv_mul_not_radial hr hrpos hΘ hΘderiv s t₀ ht₀
    rw [show w i = (fun u : ℝ => (r (Θ u) : ℂ) * Complex.exp (((Θ u : ℝ) : ℂ) * Complex.I)) from
      funext fun u => hwi u]
    exact h
  have hrate_j : ∀ (j : Fin n), j ≠ i → ∀ s t₀ : ℝ, t₀ ≠ 0 →
      ¬ ∃ c : ℝ, deriv (w j) s * (t₀ : ℂ) = c • (w j s - proj2 (farPos n j)) := by
    intro j hj s t₀ ht₀
    have h := farCurve_deriv_mul_not_radial n j s t₀ ht₀
    rw [show w j = (fun u : ℝ => proj2 (farCurve n j u)) from funext fun u => hwj j hj u]
    exact h
  have hmfderiv : ∀ (j : Fin n) (s : ℝ) (v : TangentSpace (𝓡 2) (L.γ j s)),
      mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f (L.γ j s) v = 0 → v ≠ 0 →
      ∃ t₀ : ℝ, t₀ ≠ 0 ∧
        mfderiv (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => proj2 (W z)) (L.γ j s) v
          = deriv (w j) s * (t₀ : ℂ) := by
    intro j s v hv hv0
    obtain ⟨t₀, ht₀⟩ := L.ker j s v hv
    have ht₀ne : t₀ ≠ 0 := by
      intro h0
      apply hv0
      rw [← ht₀, h0]
      exact map_zero _
    exact ⟨t₀, ht₀ne, by rw [← ht₀]; exact mfderiv_levelCurve_eq_deriv L hWsm hw j s t₀⟩
  have hin : ∀ y : M, f y = u → ∃ k : Fin n, proj2 (W y) ∈ polarRegions n i k := by
    intro y hy
    obtain ⟨j, s, rfl⟩ := L.cover y hy
    by_cases hji : j = i
    · refine ⟨i, ?_⟩
      rw [hw j s, hji, mem_polarRegions_iff]
      refine Or.inl ⟨rfl, ?_⟩
      rw [Metric.mem_ball, dist_zero_right]
      linarith [hnormi s]
    · refine ⟨j, ?_⟩
      rw [hw j s, mem_polarRegions_iff]
      refine Or.inr ⟨hji, ?_⟩
      rw [hwj j hji s, Metric.mem_ball, dist_eq_norm, proj2_farCurve_sub, norm_proj2_ang]
      norm_num
  have hregion_id : ∀ (j : Fin n) (s : ℝ) (k : Fin n),
      proj2 (W (L.γ j s)) ∈ polarRegions n i k → k = j := by
    intro j s k hk
    rw [mem_polarRegions_iff] at hk
    have htri : ∀ a b : ℂ, ‖a‖ - ‖b‖ ≤ ‖a - b‖ := by
      intro a b
      have h := norm_add_le (a - b) b
      rw [sub_add_cancel] at h
      linarith
    rcases hk with ⟨hk_eq, hk⟩ | ⟨hk_ne, hk⟩
    · rw [hk_eq]
      by_contra hij
      have hji : j ≠ i := fun h => hij h.symm
      rw [hw j s, hwj j hji s, Metric.mem_ball, dist_zero_right] at hk
      have h2 := norm_proj2_farCurve_ge n j s
      linarith
    · by_cases hji : j = i
      · exfalso
        rw [hji, hw i s, hwi s, Metric.mem_ball, dist_eq_norm] at hk
        have hX : ‖(r (Θ s) : ℂ) * Complex.exp (((Θ s : ℝ) : ℂ) * Complex.I)‖ ≤ 3 := by
          rw [← hwi s]; exact hnormi s
        have h2 : 19 ≤ ‖proj2 (farPos n k)‖ := norm_proj2_farPos_ge n k
        have h3 := htri (proj2 (farPos n k))
          ((r (Θ s) : ℂ) * Complex.exp (((Θ s : ℝ) : ℂ) * Complex.I))
        rw [norm_sub_rev] at h3
        linarith
      · by_contra hkj
        rw [hw j s, hwj j hji s, Metric.mem_ball, dist_eq_norm] at hk
        have h1 : (proj2 (farCurve n j s) - proj2 (farPos n k)).im
            = 5 * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) + Real.sin (2 * Real.pi * s) :=
          im_proj2_farCurve_sub_farPos n j k s
        have hsin : -1 ≤ Real.sin (2 * Real.pi * s) := Real.neg_one_le_sin _
        have hsin' : Real.sin (2 * Real.pi * s) ≤ 1 := Real.sin_le_one _
        have hne : (((j : ℕ) : ℝ)) ≠ (((k : ℕ) : ℝ)) := by
          intro hh
          exact hkj (Fin.ext (by exact_mod_cast hh)).symm
        have h5 : 5 ≤ |5 * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ))| := by
          rcases lt_or_gt_of_ne hne with hlt | hlt
          · have h6 : ((j : ℕ) : ℝ) + 1 ≤ ((k : ℕ) : ℝ) := by
              have h7 : (j : ℕ) < (k : ℕ) := by exact_mod_cast hlt
              exact_mod_cast (by omega : (j : ℕ) + 1 ≤ (k : ℕ))
            rw [abs_of_neg (by linarith)]
            linarith
          · have h6 : ((k : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
              have h7 : (k : ℕ) < (j : ℕ) := by exact_mod_cast hlt
              exact_mod_cast (by omega : (k : ℕ) + 1 ≤ (j : ℕ))
            rw [abs_of_pos (by linarith)]
            linarith
        have habs : |(proj2 (farCurve n j s) - proj2 (farPos n k)).im| ≤
            ‖proj2 (farCurve n j s) - proj2 (farPos n k)‖ :=
          Complex.abs_im_le_norm _
        rw [h1] at habs
        have h10 : |Real.sin (2 * Real.pi * s)| ≤ 1 := abs_le.mpr ⟨hsin, hsin'⟩
        have h9 : 4 ≤ |5 * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) + Real.sin (2 * Real.pi * s)| := by
          have h11 := abs_sub_abs_le_abs_sub (5 * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)))
            (-(Real.sin (2 * Real.pi * s)))
          rw [abs_neg, sub_neg_eq_add] at h11
          linarith
        linarith
  have hrate : ∀ (y : M) (k : Fin n), f y = u → proj2 (W y) ∈ polarRegions n i k →
      proj2 (W y) ≠ polarCentres n i k ∧
      ∀ v : TangentSpace (𝓡 2) y, mfderiv (𝓡 2) 𝓘(ℝ,ℝ) f y v = 0 → v ≠ 0 →
        ¬ (∃ t : ℝ, mfderiv (𝓡 2) 𝓘(ℝ,ℂ) (fun z : M => proj2 (W z)) y v
            = t • (proj2 (W y) - polarCentres n i k)) := by
    intro y k hy hk
    obtain ⟨j, s, rfl⟩ := L.cover y hy
    have hkj : k = j := hregion_id j s k hk
    rw [hkj]
    by_cases hji : j = i
    · rw [hji, hw i s]
      have hctr : polarCentres n i i = 0 := by rw [polarCentres, if_pos rfl]
      rw [hctr]
      refine ⟨?_, ?_⟩
      · rw [hwi s]
        intro h0
        have h1 : r (Θ s) = 0 := by
          rw [← hnormP s, h0, norm_zero]
        linarith [hrpos (Θ s)]
      · intro v hv hv0 hcon
        obtain ⟨t₀, ht₀ne, hD⟩ := hmfderiv i s v hv hv0
        obtain ⟨c, hc⟩ := hcon
        refine hrate_i s t₀ ht₀ne ⟨c, ?_⟩
        rw [sub_zero] at hc
        exact hD.symm.trans hc
    · rw [hw j s]
      have hctr : polarCentres n i j = proj2 (farPos n j) := by rw [polarCentres, if_neg hji]
      rw [hctr]
      refine ⟨?_, ?_⟩
      · rw [hwj j hji s]
        intro h0
        have h1 : ‖proj2 (farCurve n j s) - proj2 (farPos n j)‖ = 1 := by
          rw [proj2_farCurve_sub, norm_proj2_ang]
        rw [h0, sub_self, norm_zero] at h1
        norm_num at h1
      · intro v hv hv0 hcon
        obtain ⟨t₀, ht₀ne, hD⟩ := hmfderiv j s v hv hv0
        obtain ⟨c, hc⟩ := hcon
        refine hrate_j j hji s t₀ ht₀ne ⟨c, ?_⟩
        exact hD.symm.trans hc
  have hhit : ∀ k : Fin n, ∃ e : ℂ, e ≠ 0 ∧ ∀ x y : M, f x = u → f y = u →
      (∃ s : ℝ, 0 < s ∧ proj2 (W x) = polarCentres n i k + s • e) →
      (∃ s : ℝ, 0 < s ∧ proj2 (W y) = polarCentres n i k + s • e) → x = y := by
    intro k
    refine ⟨1, one_ne_zero, ?_⟩
    intro x y hx hy hxray hyray
    obtain ⟨s, hs, hxs⟩ := hxray
    obtain ⟨s', hs', hys⟩ := hyray
    obtain ⟨j, t, rfl⟩ := L.cover x hx
    obtain ⟨j', t', rfl⟩ := L.cover y hy
    -- ## the marked ray: the positive real axis from `0`
    have key0 : ∀ (j : Fin n) (t : ℝ) (s : ℝ), 0 < s →
        proj2 (W (L.γ j t)) = s • (1 : ℂ) → j = i ∧ w i t = ((r 0 : ℝ) : ℂ) := by
      intro j t s hs hval
      have hst : w j t = (s : ℂ) := by
        rw [← hw j t]
        simpa using hval
      by_cases hji : j = i
      · rw [hji] at hst ⊢
        refine ⟨rfl, ?_⟩
        have hmul : (r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I) = (s : ℂ) := by
          rw [← hwi t]; exact hst
        have hexp : Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I) = 1 :=
          exp_eq_one_of_mul_eq_pos (hrpos (Θ t)) hs hmul
        rw [hwi t, hexp, mul_one]
        congr 1
        obtain ⟨m, hm⟩ := (exp_eq_one_iff_int_mul (Θ t)).mp hexp
        rw [hm, periodic_two_pi_int_mul hrper m]
      · exfalso
        rw [hwj j hji t] at hst
        have h2 := congrArg Complex.im hst
        rw [im_proj2_farCurve, Complex.ofReal_im] at h2
        have h3 : -1 ≤ Real.sin (2 * Real.pi * t) := Real.neg_one_le_sin _
        have h4 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
    -- ## a far ray: the half line in direction `1` from the parking spot of `k`
    have key1 : ∀ (j : Fin n) (t : ℝ) (s : ℝ), 0 < s →
        proj2 (W (L.γ j t)) = proj2 (farPos n k) + s • (1 : ℂ) →
        j = k ∧ ∃ m : ℤ, t = (m : ℝ) := by
      intro j t s hs hval
      have hst : w j t = proj2 (farPos n k) + (s : ℂ) := by
        rw [← hw j t]
        simpa using hval
      by_cases hji : j = i
      · exfalso
        have h1 : ‖(r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)‖ ≤ 3 := by
          rw [← hwi t]; exact hnormi t
        have h2 : ‖proj2 (farPos n k) + (s : ℂ)‖ ≥ 20 := by
          have him : (proj2 (farPos n k) + (s : ℂ)).im = (20 + 5 * ((k : ℕ) : ℝ)) + 0 := by
            rw [Complex.add_im, Complex.ofReal_im, im_proj2_farPos]
          have h3 := Complex.abs_im_le_norm (proj2 (farPos n k) + (s : ℂ))
          rw [him] at h3
          have h4 : (0 : ℝ) ≤ ((k : ℕ) : ℝ) := Nat.cast_nonneg _
          have h5 := abs_le.mp h3
          linarith [h5.1]
        rw [hji, hwi t] at hst
        have h6 : ‖(r (Θ t) : ℂ) * Complex.exp (((Θ t : ℝ) : ℂ) * Complex.I)‖
            = ‖proj2 (farPos n k) + (s : ℂ)‖ := congrArg (fun z => ‖z‖) hst
        linarith
      · rw [hwj j hji t] at hst
        have him := congrArg Complex.im hst
        rw [im_proj2_farCurve, Complex.add_im, Complex.ofReal_im, im_proj2_farPos] at him
        have hsin : -1 ≤ Real.sin (2 * Real.pi * t) := Real.neg_one_le_sin _
        have hsin' : Real.sin (2 * Real.pi * t) ≤ 1 := Real.sin_le_one _
        have hjk : j = k := by
          by_contra hne
          have hne' : (((j : ℕ) : ℝ)) ≠ (((k : ℕ) : ℝ)) := by
            intro hh
            exact hne (Fin.ext (by exact_mod_cast hh))
          have h5 : 5 ≤ |5 * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ))| := by
            rcases lt_or_gt_of_ne hne' with hlt | hlt
            · have h6 : ((j : ℕ) : ℝ) + 1 ≤ ((k : ℕ) : ℝ) := by
                have h7 : (j : ℕ) < (k : ℕ) := by exact_mod_cast hlt
                exact_mod_cast (by omega : (j : ℕ) + 1 ≤ (k : ℕ))
              rw [abs_of_neg (by linarith)]
              linarith
            · have h6 : ((k : ℕ) : ℝ) + 1 ≤ ((j : ℕ) : ℝ) := by
                have h7 : (k : ℕ) < (j : ℕ) := by exact_mod_cast hlt
                exact_mod_cast (by omega : (k : ℕ) + 1 ≤ (j : ℕ))
              rw [abs_of_pos (by linarith)]
              linarith
          have h7 : |Real.sin (2 * Real.pi * t)| ≤ 1 := abs_le.mpr ⟨hsin, hsin'⟩
          have h8 : 5 * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) = -(Real.sin (2 * Real.pi * t)) := by
            linarith [him]
          have h9 : |5 * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ))| ≤ 1 := by
            rw [h8, abs_neg]
            exact h7
          linarith
        refine ⟨hjk, ?_⟩
        subst hjk
        have hsin0 : Real.sin (2 * Real.pi * t) = 0 := by linarith
        have hreal : Real.cos (2 * Real.pi * t) = s := by
          have h8 := congrArg Complex.re hst
          rw [re_proj2_farCurve, proj2_farPos] at h8
          simp at h8
          linarith
        have hcos1 : Real.cos (2 * Real.pi * t) = 1 := by
          have h9 : Real.cos (2 * Real.pi * t) ^ 2 = 1 := by
            have h10 := Real.sin_sq_add_cos_sq (2 * Real.pi * t)
            rw [hsin0] at h10
            nlinarith [h10]
          rcases sq_eq_one_iff.mp h9 with h | h <;> linarith
        have hexp : Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) = 1 := by
          rw [Complex.exp_ofReal_mul_I, hcos1, hsin0]
          simp
        obtain ⟨m, hm⟩ := (exp_eq_one_iff_int_mul (2 * Real.pi * t)).mp hexp
        refine ⟨m, ?_⟩
        have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
        have h2 : (2 * Real.pi) * t = (2 * Real.pi) * (m : ℝ) := by rw [hm]; ring
        exact mul_left_cancel₀ (ne_of_gt hpi) h2
    by_cases hki : k = i
    · rw [polarCentres, if_pos hki] at hxs hys
      rw [zero_add] at hxs hys
      obtain ⟨hj, hv⟩ := key0 j t s hs hxs
      obtain ⟨hj', hv'⟩ := key0 j' t' s' hs' hys
      have hwinj' : w i t = w i t' := by rw [hv, hv']
      obtain ⟨m, hm⟩ := hwinj t t' hwinj'
      rw [hj, hj', hm]
      simpa using Function.Periodic.int_mul (L.per i) m t'
    · rw [polarCentres, if_neg hki] at hxs hys
      obtain ⟨hj, m, hm⟩ := key1 j t s hs hxs
      obtain ⟨hj', m', hm'⟩ := key1 j' t' s' hs' hys
      rw [hj, hj', hm, hm']
      rw [show L.γ k (↑m) = L.γ k 0 from by
            simpa using Function.Periodic.int_mul (L.per k) m 0,
        show L.γ k (↑m') = L.γ k 0 from by
            simpa using Function.Periodic.int_mul (L.per k) m' 0]
  exact Work.Drive.N2Lead.isCertifiedAt_of_starRegions hf hreg hW (polarRegions n i)
    (polarCentres n i) (fun _ => 1) (isOpen_convex_polarRegions n i)
    (fun _ => one_pos) (closedBall_subset_polarRegions n i) (pairwiseDisjoint_polarRegions n i)
    hin hrate hhit

end Main

end Work.Drive.N2C
