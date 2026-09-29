import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.setup
import Submission.Work.A14D.H_cont
import Submission.Work.A14D.Dzc_helpers
import Submission.Work.A14D.conj_toolkit
import Submission.Work.A14D.half_log_vanishes
import Submission.Work.A14D.conjRefl_HU_eq_HL
import Submission.Work.A14D.LZ_sub_const_mul
import Submission.Work.A14D.kappa_both_zero_of_halfs
import Submission.Work.A14D.hol_sol_at_ninth_smul
import Submission.Work.A14D.glue_three_LZ

namespace Work.A14D

open Complex Metric Filter
open scoped BigOperators
open Work.A14D

noncomputable section

/-! ## Elementary conjugation facts -/

lemma star_mem_SL_of_mem_SU {z : ℂ} (hz : z ∈ SU) : star z ∈ SL := by
  rw [mem_SU_iff] at hz
  rw [mem_SL_iff]
  simp only [Complex.star_def, Complex.conj_im, Complex.conj_re]
  linarith

lemma star_mem_SU_of_mem_SL {z : ℂ} (hz : z ∈ SL) : star z ∈ SU := by
  rw [mem_SL_iff] at hz
  rw [mem_SU_iff]
  simp only [Complex.star_def, Complex.conj_im, Complex.conj_re]
  linarith

lemma star_mem_Om1 {z : ℂ} (hz : z ∈ Om1) : star z ∈ Om1 := by
  rcases hz with h | h
  · exact Or.inl (by simpa [Complex.star_def, Complex.conj_im] using h)
  · exact Or.inr (by simpa [Complex.star_def, Complex.conj_re] using h)

lemma star_mem_ball_ninth {δ : ℝ} {z : ℂ} (hz : z ∈ Metric.ball ninth δ) :
    star z ∈ Metric.ball ninth δ := by
  rw [Metric.mem_ball, Complex.dist_eq] at hz ⊢
  have h : star z - ninth = star (z - ninth) := by simp [ninth]
  rw [h, norm_star]
  exact hz

/-- On the lower half-plane the principal `log (· - 1/9)` commutes with `star`. -/
lemma star_log_of_im_neg {z : ℂ} (hz : z.im < 0) :
    star (Complex.log (star z - ninth)) = Complex.log (z - ninth) := by
  have harg : (z - ninth).arg ≠ Real.pi := by
    intro h
    rw [Complex.arg_eq_pi_iff] at h
    have him : (z - ninth).im = z.im := by simp [ninth]
    rw [him] at h
    linarith [h.2, hz]
  have h1 : star z - ninth = star (z - ninth) := by simp [ninth]
  rw [h1, Complex.star_def]
  rw [Complex.log_conj (z - ninth) harg]
  exact Complex.conj_conj _

/-- The jump `D` of `Hfun a b c` is anti-real: `HL = conj ∘ HU ∘ conj`, hence `D = HU - HL` is
anti-real too.  Consequently the log coefficient of `D` at `1/9` computed from below equals
`-conj` of the one computed from above, in the conjugation-invariant form `κ * y9 (1/9)`.

PROOF ROUTE (checked by two reviewers):
* `conjRefl f := fun z => star (f (star z))` maps `LZ`-solutions to `LZ`-solutions (real coefficients
  of `PZ, PZ', RZ`, `Work.A14D.LZ_conjRefl`); `conjRefl (Hfun a b c) = Hfun a b c` (`Hfun_conj`).
* Hence `conjRefl HU = HL` on `SL` (both solve `LZ = rhsZ b c` there and agree with `Hfun` on the
  nonempty open `SL ∩ ball 0 1`, and `SL` is convex), giving `conjRefl D = -D` on `Om1` by the
  identity theorem on the connected open `Om1`.  (This is `Work.A14D.conjRefl_HU_eq_HL`.)
* On `halfL δ`: from `D = κL · y9 · log (· - 1/9) + hL` (hL holomorphic on the ball) and
  `conjRefl D = -D`, the reflection of the upper relation `D = κU · y9 · log(· - 1/9) + hU` gives
  an identity `G z · log (z - 1/9) = H z` on `halfL δ` with `G`, `H` holomorphic on the ball.  By
  `Work.A14D.half_log_vanishes`, `G ≡ 0`, and evaluating at `1/9` gives the claim. -/
theorem kappaL_conj_symm (a b c : ℤ) (h : Submission.CDTPlan.ARel a b c)
    (HU HL : ℂ → ℂ)
    (hHU : DifferentiableOn ℂ HU SU ∧ (∀ z ∈ SU, LZ HU z = rhsZ b c z) ∧
      ∀ z ∈ SU ∩ ball 0 1, HU z = Hfun a b c z)
    (hHL : DifferentiableOn ℂ HL SL ∧ (∀ z ∈ SL, LZ HL z = rhsZ b c z) ∧
      ∀ z ∈ SL ∩ ball 0 1, HL z = Hfun a b c z)
    (y9 : ℂ → ℂ) (δ : ℝ) (hY : Y9 y9 δ)
    (D : ℂ → ℂ) (hD : DifferentiableOn ℂ D Om1) (hDL : ∀ z ∈ Om1, LZ D z = 0)
    (hDj : ∀ z ∈ SU ∩ SL, D z = HU z - HL z)
    (κU κL : ℂ) (hU : LogCoeff y9 δ (halfU δ) D κU) (hL : LogCoeff y9 δ (halfL δ) D κL) :
    κL * y9 ninth = -(star (κU * y9 ninth)) := by
  obtain ⟨hR1, hR2⟩ := conjRefl_HU_eq_HL a b c h HU HL hHU hHL
  -- ### Step 1: `D` is anti-real on the slit plane
  have hRD : ∀ z ∈ Om1, conjRefl D z = -D z := by
    have hd1 : DifferentiableOn ℂ (conjRefl D) Om1 :=
      conjRefl_differentiableOn hD Dzc_isOpen_Om1 (fun z hz => star_mem_Om1 hz)
    have hL1 : ∀ z ∈ Om1, LZ (conjRefl D) z = 0 := by
      intro z hz
      rw [LZ_conjRefl, hDL (star z) (star_mem_Om1 hz), star_zero]
    have hd2 : DifferentiableOn ℂ (fun z => -D z) Om1 := hD.neg
    have hL2 : ∀ z ∈ Om1, LZ (fun z => -D z) z = 0 := by
      intro z hz
      have hkey := Dzc_LZ_const_mul Dzc_isOpen_Om1 hD (c := (-1 : ℂ)) hz
      rw [hDL z hz, mul_zero] at hkey
      simpa using hkey
    have hVne : (SU ∩ SL).Nonempty :=
      ⟨2, by rw [mem_SU_iff]; norm_num, by rw [mem_SL_iff]; norm_num⟩
    have hag : Set.EqOn (conjRefl D) (fun z => -D z) (SU ∩ SL) := by
      intro z hz
      obtain ⟨hzSU, hzSL⟩ := hz
      change conjRefl D z = -D z
      have hsz : star z ∈ SU ∩ SL := ⟨star_mem_SU_of_mem_SL hzSL, star_mem_SL_of_mem_SU hzSU⟩
      have h1 : conjRefl D z = star (HU (star z)) - star (HL (star z)) := by
        rw [conjRefl_apply, hDj (star z) hsz, star_sub]
      rw [h1, show star (HU (star z)) = HL z from hR1 z hzSL,
        show star (HL (star z)) = HU z from hR2 z hzSU, hDj z ⟨hzSU, hzSL⟩]
      ring
    exact Dzc_eqOn_of_agree_open Dzc_isOpen_Om1 Dzc_isPreconnected_Om1
      (fun z hz => Dzc_PZ_ne_zero_of_mem_Om1 hz) hd1 hd2 hL1 hL2
      (fun z hz => SU_subset_Om1 hz.1) (isOpen_SU_H_cont.inter isOpen_SL_H_cont) hVne hag
  -- ### Step 2: the local `log`-relation on the lower half disc
  obtain ⟨hUfun, hUfun_d, hUeq⟩ := hU
  obtain ⟨hLfun, hLfun_d, hLeq⟩ := hL
  have hy9d : DifferentiableOn ℂ y9 (Metric.ball ninth δ) := hY.2.2.1
  have hcy9 : DifferentiableOn ℂ (conjRefl y9) (Metric.ball ninth δ) :=
    conjRefl_differentiableOn hy9d Metric.isOpen_ball (fun z hz => star_mem_ball_ninth hz)
  have hchU : DifferentiableOn ℂ (conjRefl hUfun) (Metric.ball ninth δ) :=
    conjRefl_differentiableOn hUfun_d Metric.isOpen_ball (fun z hz => star_mem_ball_ninth hz)
  set G : ℂ → ℂ := fun z => star κU * conjRefl y9 z + κL * y9 z with hGdef
  set H : ℂ → ℂ := fun z => -(conjRefl hUfun z + hLfun z) with hHdef
  have hGd : DifferentiableOn ℂ G (Metric.ball ninth δ) := by
    rw [hGdef]
    exact (hcy9.const_mul (star κU)).add (hy9d.const_mul κL)
  have hHd : DifferentiableOn ℂ H (Metric.ball ninth δ) := by
    rw [hHdef]
    exact (hchU.add hLfun_d).neg
  have hrel : ∀ z ∈ halfL δ, G z * Complex.log (z - ninth) = H z := by
    intro z hz
    obtain ⟨hzb, hzim⟩ := hz
    have hzim' : z.im < 0 := hzim
    have hzOm1 : z ∈ Om1 := Or.inl (ne_of_lt hzim')
    have hszU : star z ∈ halfU δ :=
      ⟨star_mem_ball_ninth hzb, by
        show 0 < (star z).im
        rw [Complex.star_def, Complex.conj_im]; linarith⟩
    have hDz : D z = κL * y9 z * Complex.log (z - ninth) + hLfun z := hLeq z ⟨hzb, hzim⟩
    have hDsz : D (star z) = κU * y9 (star z) * Complex.log (star z - ninth) + hUfun (star z) :=
      hUeq (star z) hszU
    have hkey : conjRefl D z = star κU * conjRefl y9 z * Complex.log (z - ninth) + conjRefl hUfun z := by
      rw [conjRefl_apply, hDsz]
      simp only [star_add, star_mul, star_log_of_im_neg hzim', conjRefl_apply]
      ring
    rw [hRD z hzOm1, hDz] at hkey
    simp only [hGdef, hHdef]
    linear_combination -hkey
  have hGzero : ∀ z ∈ Metric.ball ninth δ, G z = 0 := half_log_vanishes hY.1 hGd hHd hrel
  -- ### Step 3: evaluate at `1/9`
  have h9mem : ninth ∈ Metric.ball ninth δ := Metric.mem_ball_self hY.1
  have h9 := hGzero ninth h9mem
  rw [hGdef] at h9
  simp only [conjRefl_apply] at h9
  have hstar9 : star ninth = ninth := by simp [ninth]
  rw [hstar9] at h9
  have hkey : κL * y9 ninth = -(star κU * star (y9 ninth)) :=
    eq_neg_of_add_eq_zero_right h9
  rw [hkey, star_mul]
  ring

end

end Work.A14D
