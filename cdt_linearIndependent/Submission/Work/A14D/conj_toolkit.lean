import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.setup
import Submission.Work.A14D.H_cont
import Submission.Work.A14D.Dzc_helpers
import Submission.Work.A14D.log_structured_vanishes
import Submission.Work.A14D.eqOn_of_sol_LZ

/-!
# `Work.A14D.conj_toolkit`

Conjugation (`star = conj` on `ℂ`) and the Zagier operator `LZ`.

The operator `LZ f = PZ·f'' + PZ'·f' + RZ·f` has *real* coefficient functions `PZ, PZ', RZ`,
so it commutes with the reflection `conjRefl f := z ↦ star (f (star z))`:
`LZ (conjRefl f) z = star (LZ f (star z))`.  Likewise `rhsZ b c` (`b, c ∈ ℤ`) is real, and so is the
power series `Hfun a b c` (rational coefficients).  Finally `star '' SU = SL`, `star '' SL = SU`
and `star '' Om1 = Om1`.
-/

namespace Work.A14D

open Complex Metric Filter
open scoped Topology BigOperators

noncomputable section

/-- The reflection `f ↦ conj ∘ f ∘ conj`. -/
def conjRefl (f : ℂ → ℂ) : ℂ → ℂ := fun z => star (f (star z))

@[simp] lemma conjRefl_apply (f : ℂ → ℂ) (z : ℂ) : conjRefl f z = star (f (star z)) := rfl

lemma star_PZ (z : ℂ) : star (PZ (star z)) = PZ z := by
  rw [Complex.star_def]
  simp only [PZ, map_mul, map_sub, map_one, map_ofNat, Complex.conj_conj]

lemma star_PZ' (z : ℂ) : star (PZ' (star z)) = PZ' z := by
  rw [Complex.star_def]
  simp only [PZ', map_add, map_sub, map_mul, map_pow, map_one, map_ofNat, Complex.conj_conj]

lemma star_RZ (z : ℂ) : star (RZ (star z)) = RZ z := by
  rw [Complex.star_def]
  simp only [RZ, map_add, map_sub, map_mul, map_ofNat, Complex.conj_conj]

lemma star_rhsZ (b c : ℤ) (z : ℂ) : star (rhsZ b c (star z)) = rhsZ b c z := by
  rw [Complex.star_def]
  simp only [rhsZ, map_add, map_div₀, map_sub, map_one, map_intCast, Complex.conj_conj]

/-- `Hfun a b c` has rational Taylor coefficients, hence satisfies `conj (Hfun (conj z)) = Hfun z`. -/
theorem Hfun_conj (a b c : ℤ) (z : ℂ) : star (Hfun a b c (star z)) = Hfun a b c z := by
  rw [Hfun]
  simp only [Complex.star_def]
  rw [Complex.conj_tsum]
  simp
  rw [Hfun]

lemma conjRefl_deriv (f : ℂ → ℂ) (z : ℂ) :
    deriv (conjRefl f) z = star (deriv f (star z)) := by
  show deriv (fun w => star (f (star w))) z = star (deriv f (star z))
  have h := congrFun (deriv_conj_conj (f := f)) z
  simpa [Function.comp_def, Complex.star_def] using h

lemma conjRefl_deriv_deriv (f : ℂ → ℂ) (z : ℂ) :
    deriv (deriv (conjRefl f)) z = star (deriv (deriv f) (star z)) := by
  have h1 : deriv (conjRefl f) = conjRefl (deriv f) := by
    funext w; exact conjRefl_deriv f w
  rw [h1]
  exact conjRefl_deriv (deriv f) z

/-- `LZ` commutes with conjugation. -/
theorem LZ_conjRefl (f : ℂ → ℂ) (z : ℂ) : LZ (conjRefl f) z = star (LZ f (star z)) := by
  rw [LZ_def, conjRefl_deriv f z, conjRefl_deriv_deriv f z]
  rw [LZ_def]
  simp only [star_add, star_mul, star_PZ, star_PZ', star_RZ, conjRefl_apply]
  ring

/-- If `f` is holomorphic on `U` and `star '' V ⊆ U`, then `conjRefl f` is holomorphic on `V`. -/
lemma conjRefl_differentiableOn {f : ℂ → ℂ} {U V : Set ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : IsOpen U) (hVU : ∀ z ∈ V, star z ∈ U) :
    DifferentiableOn ℂ (conjRefl f) V := by
  intro z hz
  have hz' : U ∈ 𝓝 (star z) := hU.mem_nhds (hVU z hz)
  have h := (hf.differentiableAt hz').conj_conj
  have h2 : (starRingEnd ℂ) (star z) = z := by simp [Complex.star_def]
  rw [h2] at h
  show DifferentiableWithinAt ℂ (fun w => star (f (star w))) V z
  simpa [Function.comp_def, Complex.star_def] using h.differentiableWithinAt

lemma star_image_SU : star '' SU = SL := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_SU_iff] at hw
    rw [mem_SL_iff]
    simp only [Complex.star_def, Complex.conj_im, Complex.conj_re]
    linarith
  · intro hz
    refine ⟨star z, ?_, by simp⟩
    rw [mem_SL_iff] at hz
    rw [mem_SU_iff]
    simp only [Complex.star_def, Complex.conj_im, Complex.conj_re]
    linarith

lemma star_image_SL : star '' SL = SU := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [mem_SL_iff] at hw
    rw [mem_SU_iff]
    simp only [Complex.star_def, Complex.conj_im, Complex.conj_re]
    linarith
  · intro hz
    refine ⟨star z, ?_, by simp⟩
    rw [mem_SU_iff] at hz
    rw [mem_SL_iff]
    simp only [Complex.star_def, Complex.conj_im, Complex.conj_re]
    linarith

lemma star_image_Om1 : star '' Om1 = Om1 := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    simp only [Complex.star_def]
    rcases hw with him | hre
    · exact Or.inl (by simpa [Complex.conj_im] using him)
    · exact Or.inr (by simpa [Complex.conj_re] using hre)
  · intro hz
    refine ⟨star z, ?_, by simp⟩
    simp only [Complex.star_def]
    rcases hz with him | hre
    · exact Or.inl (by simpa [Complex.conj_im] using him)
    · exact Or.inr (by simpa [Complex.conj_re] using hre)

lemma star_image_ball_one : star '' (Metric.ball (0 : ℂ) 1) = Metric.ball 0 1 := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    rw [Metric.mem_ball, Complex.dist_eq] at hw ⊢
    rw [sub_zero] at hw ⊢
    rwa [norm_star]
  · intro hz
    refine ⟨star z, ?_, by simp⟩
    rw [Metric.mem_ball, Complex.dist_eq] at hz ⊢
    rw [sub_zero] at hz ⊢
    rwa [norm_star]

end

end Work.A14D
