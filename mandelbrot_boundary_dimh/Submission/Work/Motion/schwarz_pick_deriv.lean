import Mathlib
import Submission.Work.Motion.disc_autom
import Submission.Work.Motion.mob_disc
import Submission.Work.Motion.deriv_rescale
import Submission.Work.Motion.arith_bound

/-!
# Schwarz–Pick derivative bound

We prove that a holomorphic map `f` of the disc `ball c R` into the concentric disc
`ball c M` satisfies `‖deriv f z‖ ≤ M * R / (R ^ 2 - ‖z - c‖ ^ 2)` at every `z` of the disc.

The argument is the standard Schwarz–Pick reduction:

* `mob a t = (t - a) / (1 - conj a * t)` is the disc automorphism sending `a` to `0`.
* For a self-map `F` of the unit disc and `w` in the disc, put `G t = mob (F w) (F (mob (-w) t))`.
  Then `G` is a self-map of the disc fixing `0`; the Schwarz lemma gives
  `‖deriv G 0‖ ≤ 1`, and the chain rule identifies `deriv G 0` with
  `deriv (mob (F w)) (F w) * deriv F w * deriv (mob (-w)) 0`, whose norm is
  `(1 - ‖F w‖ ^ 2)⁻¹ * ‖deriv F w‖ * (1 - ‖w‖ ^ 2)`.
* Rearranging gives the unit-disc bound `‖deriv F w‖ ≤ 1 / (1 - ‖w‖ ^ 2)`.
* Rescaling `ball c R` to the unit disc finishes the proof.

-/

namespace Work.Motion

open Metric Set
open scoped ComplexConjugate

/-- Derivative of the disc automorphism `mob a`. -/
theorem deriv_mob_eq (a t : ℂ) (h : 1 - conj a * t ≠ 0) :
    deriv (mob a) t = (1 - conj a * a) / (1 - conj a * t) ^ 2 := by
  have hc : DifferentiableAt ℂ (fun y : ℂ => y - a) t := by fun_prop
  have hd : DifferentiableAt ℂ (fun y : ℂ => 1 - conj a * y) t := by fun_prop
  have hnum : deriv (fun y : ℂ => y - a) t = 1 := by
    rw [deriv_sub_const]; simp
  have hden : deriv (fun y : ℂ => 1 - conj a * y) t = -(conj a) := by
    rw [deriv_const_sub, deriv_const_mul _ (differentiableAt_id)]; simp
  change deriv ((fun y : ℂ => y - a) / (fun y : ℂ => 1 - conj a * y)) t = _
  rw [deriv_div hc hd h, hnum, hden]
  ring

/-- Norms of the derivative of `mob a` at `a` (which maps `a` to `0`) and at `0`. -/
theorem norm_deriv_mob_aux {a : ℂ} (ha : ‖a‖ < 1) :
    ‖deriv (mob a) a‖ = (1 - ‖a‖ ^ 2)⁻¹ ∧
    ‖deriv (mob a) 0‖ = 1 - ‖a‖ ^ 2 := by
  have hlt : Complex.normSq a < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg a]
  have hcast : (1 : ℂ) - conj a * a = ↑(1 - Complex.normSq a) := by
    rw [← Complex.normSq_eq_conj_mul_self (z := a)]
    push_cast
    ring
  have hDnorm : ‖(1 : ℂ) - conj a * a‖ = 1 - Complex.normSq a := by
    rw [hcast]
    exact (RCLike.norm_ofReal (1 - Complex.normSq a)).trans (abs_of_nonneg (by linarith))
  have hne : 1 - conj a * a ≠ 0 := by
    rw [hcast]; exact Complex.ofReal_ne_zero.mpr (by linarith)
  constructor
  · rw [deriv_mob_eq a a hne]
    have hsimp : (1 - conj a * a) / (1 - conj a * a) ^ 2 = (1 - conj a * a)⁻¹ := by
      field_simp
    rw [hsimp, norm_inv, hDnorm, Complex.normSq_eq_norm_sq]
  · rw [deriv_mob_eq a 0 (by simp)]
    rw [show (1 - conj a * 0) = 1 by ring, one_pow, div_one, hDnorm, Complex.normSq_eq_norm_sq]

/-- **Schwarz–Pick on the unit disc.** A holomorphic self-map of the unit disc satisfies
`‖deriv F w‖ ≤ 1 / (1 - ‖w‖ ^ 2)`. -/
theorem unit_disc_bound {F : ℂ → ℂ} (hF : DifferentiableOn ℂ F (ball 0 1))
    (hmap : MapsTo F (ball 0 1) (ball 0 1)) {w : ℂ} (hw : w ∈ ball 0 1) :
    ‖deriv F w‖ ≤ 1 / (1 - ‖w‖ ^ 2) := by
  have hw1 : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
  have ha1 : ‖F w‖ < 1 := mem_ball_zero_iff.mp (hmap hw)
  obtain ⟨hmapm, hdm, hm0⟩ := mob_disc ha1
  have hda : ‖deriv (mob (F w)) (F w)‖ = (1 - ‖F w‖ ^ 2)⁻¹ := (norm_deriv_mob_aux ha1).1
  have hwn : ‖-w‖ < 1 := by rwa [norm_neg]
  obtain ⟨hmapw, hdw, _⟩ := mob_disc hwn
  have hd0 : ‖deriv (mob (-w)) 0‖ = 1 - ‖w‖ ^ 2 := by
    have h := (norm_deriv_mob_aux hwn).2
    rwa [norm_neg] at h
  let G : ℂ → ℂ := fun t => mob (F w) (F (mob (-w) t))
  have hmobw0 : mob (-w) 0 = w := by simp [mob]
  have hGdiff : DifferentiableOn ℂ G (ball 0 1) := by
    have h1 : DifferentiableOn ℂ (F ∘ (mob (-w))) (ball 0 1) := hF.comp hdw hmapw
    exact hdm.comp h1 (fun t ht => hmap (hmapw ht))
  have hG0 : G 0 = 0 := by
    change mob (F w) (F (mob (-w) 0)) = 0
    rw [hmobw0, hm0]
  have hGmap : MapsTo G (ball 0 1) (closedBall (G 0) 1) := by
    intro t ht
    have hlt : ‖G t‖ < 1 := by
      change ‖mob (F w) (F (mob (-w) t))‖ < 1
      exact mem_ball_zero_iff.mp (hmapm (hmap (hmapw ht)))
    rw [hG0]
    simpa [mem_closedBall_zero_iff] using hlt.le
  have hSch : ‖deriv G 0‖ ≤ 1 := by
    have h := Complex.norm_deriv_le_div_of_mapsTo_ball (c := 0) (R₁ := 1) (R₂ := 1)
      (f := G) hGdiff hGmap (by norm_num)
    simpa using h
  have hFcomp_diff : DifferentiableAt ℂ (F ∘ (mob (-w))) 0 := by
    have h1 : DifferentiableAt ℂ (mob (-w)) 0 := hdw.differentiableAt (ball_mem_nhds 0 zero_lt_one)
    have h2 : DifferentiableAt ℂ F ((mob (-w)) 0) := by
      rw [hmobw0]; exact hF.differentiableAt (isOpen_ball.mem_nhds hw)
    exact h2.comp 0 h1
  have hmoba_diff : DifferentiableAt ℂ (mob (F w)) ((F ∘ (mob (-w))) 0) := by
    have hpt : (F ∘ (mob (-w))) 0 = F w := by simp only [Function.comp_apply, hmobw0]
    rw [hpt]
    exact hdm.differentiableAt (isOpen_ball.mem_nhds (hmap hw))
  have hGderiv : deriv G 0 = deriv (mob (F w)) (F w) * (deriv F w * deriv (mob (-w)) 0) := by
    have hinner : deriv (F ∘ (mob (-w))) 0 = deriv F w * deriv (mob (-w)) 0 := by
      have h := deriv_comp (h := mob (-w)) (h₂ := F) 0
        (by rw [hmobw0]; exact hF.differentiableAt (isOpen_ball.mem_nhds hw))
        (hdw.differentiableAt (ball_mem_nhds 0 zero_lt_one))
      rwa [hmobw0] at h
    have houter := deriv_comp (h := F ∘ (mob (-w))) (h₂ := mob (F w)) 0 hmoba_diff hFcomp_diff
    rw [hinner] at houter
    simp only [Function.comp_apply, hmobw0] at houter
    change deriv ((mob (F w)) ∘ (F ∘ (mob (-w)))) 0 = _
    rw [houter]
  have hnorm : ‖deriv G 0‖ = (1 - ‖F w‖ ^ 2)⁻¹ * (‖deriv F w‖ * (1 - ‖w‖ ^ 2)) := by
    rw [hGderiv, norm_mul, norm_mul, hda, hd0]
  have hFwpos : 0 < 1 - ‖F w‖ ^ 2 := by
    have : ‖F w‖ ^ 2 < 1 := by nlinarith [norm_nonneg (F w), ha1]
    linarith
  have hX : ‖deriv F w‖ * (1 - ‖w‖ ^ 2) ≤ 1 - ‖F w‖ ^ 2 := by
    have h1 : (1 - ‖F w‖ ^ 2)⁻¹ * (‖deriv F w‖ * (1 - ‖w‖ ^ 2)) ≤ 1 := by
      rw [← hnorm]; exact hSch
    have h1' : (‖deriv F w‖ * (1 - ‖w‖ ^ 2)) / (1 - ‖F w‖ ^ 2) ≤ 1 := by
      rwa [inv_mul_eq_div] at h1
    rw [div_le_iff₀ hFwpos] at h1'
    simpa using h1'
  have hwpos : 0 < 1 - ‖w‖ ^ 2 := by
    have : ‖w‖ ^ 2 < 1 := by nlinarith [norm_nonneg w, hw1]
    linarith
  rw [le_div_iff₀ hwpos]
  calc ‖deriv F w‖ * (1 - ‖w‖ ^ 2) ≤ 1 - ‖F w‖ ^ 2 := hX
    _ ≤ 1 := by linarith [sq_nonneg ‖F w‖]

/-- **Schwarz–Pick derivative bound.** A holomorphic `f` on the disc `ball c R` mapping it into
the concentric disc `ball c M` satisfies `‖deriv f z‖ ≤ M * R / (R ^ 2 - ‖z - c‖ ^ 2)` at every
`z` of the disc. -/
theorem schwarz_pick_deriv {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball c R)) (hM : MapsTo f (ball c R) (ball c M))
    {z : ℂ} (hz : z ∈ ball c R) :
    ‖deriv f z‖ ≤ M * R / (R ^ 2 - ‖z - c‖ ^ 2) := by
  have hMpos : 0 < M := by
    rcases hM.nonempty (nonempty_ball.2 hR) with ⟨y, hy⟩
    exact nonempty_ball.1 ⟨y, hy⟩
  have hRnorm : ‖(R : ℂ)‖ = R := (RCLike.norm_ofReal R).trans (abs_of_pos hR)
  have hMnorm : ‖(M : ℂ)‖ = M := (RCLike.norm_ofReal M).trans (abs_of_pos hMpos)
  have hzlt : ‖z - c‖ < R := by
    have h := hz
    rwa [mem_ball_iff_norm] at h
  have haff : MapsTo (fun w : ℂ => c + (R : ℂ) * w) (ball 0 1) (ball c R) := by
    intro w hw
    rw [mem_ball_iff_norm]
    have hwlt : ‖w‖ < 1 := mem_ball_zero_iff.mp hw
    calc ‖c + (R : ℂ) * w - c‖ = R * ‖w‖ := by
          rw [show c + (R : ℂ) * w - c = (R : ℂ) * w by ring, norm_mul, hRnorm]
      _ < R * 1 := mul_lt_mul_of_pos_left hwlt hR
      _ = R := mul_one R
  have hFdiff : DifferentiableOn ℂ (fun w : ℂ => (f (c + (R : ℂ) * w) - c) / (M : ℂ))
      (ball 0 1) := by
    have h1 : DifferentiableOn ℂ (fun w : ℂ => f (c + (R : ℂ) * w)) (ball 0 1) :=
      hf.comp (by fun_prop) haff
    exact (h1.sub_const c).div_const (M : ℂ)
  have hFmap : MapsTo (fun w : ℂ => (f (c + (R : ℂ) * w) - c) / (M : ℂ))
      (ball 0 1) (ball 0 1) := by
    intro w hw
    have hwin : c + (R : ℂ) * w ∈ ball c R := haff hw
    have hfin : f (c + (R : ℂ) * w) ∈ ball c M := hM hwin
    rw [mem_ball_zero_iff, norm_div, hMnorm]
    rw [mem_ball_iff_norm] at hfin
    rw [div_lt_one hMpos]
    exact hfin
  set w₀ : ℂ := (z - c) / (R : ℂ) with hw₀def
  have hw₀mem : w₀ ∈ ball 0 1 := by
    rw [mem_ball_zero_iff, hw₀def, norm_div, hRnorm]
    rw [div_lt_one hR]
    exact hzlt
  have hub := unit_disc_bound hFdiff hFmap hw₀mem
  have hdw₀ : c + (R : ℂ) * w₀ = z := by
    rw [hw₀def]
    have hRne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR.ne'
    field_simp
    ring
  have hdiffz : DifferentiableAt ℂ f z := hf.differentiableAt (isOpen_ball.mem_nhds hz)
  have hdr := deriv_rescale (f := f) (c := c) (R := R) (M := M) (w := w₀)
    (by rw [hdw₀]; exact hdiffz)
  have hnorm : ‖deriv (fun u => (f (c + (R : ℂ) * u) - c) / (M : ℂ)) w₀‖
      = R / M * ‖deriv f z‖ := by
    rw [hdr, norm_mul, norm_div, hRnorm, hMnorm, hdw₀]
  have hub' : R / M * ‖deriv f z‖ ≤ 1 / (1 - ‖w₀‖ ^ 2) := by
    rw [← hnorm]; exact hub
  have hw₀norm : ‖w₀‖ = ‖z - c‖ / R := by
    rw [hw₀def, norm_div, hRnorm]
  have hfinal : R / M * ‖deriv f z‖ ≤ 1 / (1 - (‖z - c‖ / R) ^ 2) := by
    have : ‖w₀‖ ^ 2 = (‖z - c‖ / R) ^ 2 := by rw [hw₀norm]
    rwa [this] at hub'
  exact arith_bound hR hMpos (norm_nonneg _) hzlt hfinal

end Work.Motion
