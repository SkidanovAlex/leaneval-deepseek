import Mathlib
import Submission.Work.FIArea4.Vflip.exists_bump_majorant
import Submission.Work.FIArea4.box_defs

/-!
# A uniform bump majorant for the dyadic dual variance

For every `S ≥ 1` we produce a continuous bump `f` with `0 ≤ f ≤ 1`, `f = 1` on `(S, 2S]` and
`f = 0` off `[S/2, 5S/2]`, together with its Fourier transform `F`, in such a way that the decay
constant `C₀` in `‖F ξ‖ ≤ C₀ S (1 + S|ξ|)^{-2}` is **absolute** (independent of `S`).  This is
what lets the local-variance estimate `Wdyad_diff_part_le_unif` be applied with a single constant
for all `S`.

The construction is the one of `Work.FIArea4.bump_majorant_uniform` (`f x = bumpF (x/S)`), stated
with the fields of `Work.FIArea4.BumpData` bundled, plus the `HasCompactSupport` facts used to feed
the Fourier-analytic hypothesis of `Wdyad_bilinear_gen`.
-/

namespace Work.FIArea4.UnitsFlat

open scoped BigOperators FourierTransform

noncomputable section

/-- The bump `bumpF` is bounded by `1`. -/
lemma bumpF_le_one (x : ℝ) : Work.FIArea4.Vflip.bumpF x ≤ 1 := by
  unfold Work.FIArea4.Vflip.bumpF
  have h1 := Real.smoothTransition.le_one (2 * x - 1)
  have h2 := Real.smoothTransition.le_one (5 - 2 * x)
  have h1' := Real.smoothTransition.nonneg (2 * x - 1)
  have h2' := Real.smoothTransition.nonneg (5 - 2 * x)
  nlinarith

/-- **A uniform bump majorant.**  There is an absolute constant `C₀ > 0` such that for every
`S ≥ 1` there are `f : ℝ → ℝ` and `F : ℝ → ℂ` with
`0 ≤ f ≤ 1`, `f = 1` on `(S,2S]`, `f = 0` off `[S/2,5S/2]`, `f` continuous, `F = 𝓕(f:ℂ)` and
`‖F ξ‖ ≤ C₀ S (1+S|ξ|)^{-2}`. -/
theorem bump_majorant_uniform_units :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ S : ℕ, 1 ≤ S →
      ∃ (f : ℝ → ℝ) (F : ℝ → ℂ),
        (∀ x, 0 ≤ f x) ∧ (∀ x, f x ≤ 1) ∧
        (∀ x, (S : ℝ) < x → x ≤ 2 * (S : ℝ) → 1 ≤ f x) ∧
        (∀ x, f x ≠ 0 → (S : ℝ) / 2 ≤ x ∧ x ≤ 5 * (S : ℝ) / 2) ∧
        Continuous f ∧
        (∀ ξ, F ξ = FourierTransform.fourier (fun x : ℝ => (f x : ℂ)) ξ) ∧
        (∀ ξ, ‖F ξ‖ ≤ C₀ * (S : ℝ) * (1 + (S : ℝ) * |ξ|) ^ (-(2 : ℝ))) := by
  obtain ⟨C₀, hC₀, hbnd⟩ := Work.FIArea4.Vflip.bumpFc_fourier_bound
  refine ⟨C₀ + 1, by linarith, fun S hS => ?_⟩
  set s : ℝ := (S : ℝ) with hsdef
  have hs : 0 < s := by
    rw [hsdef]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hS)
  refine ⟨fun x => Work.FIArea4.Vflip.bumpF (x / s),
    fun ξ => FourierTransform.fourier (fun x : ℝ => (Work.FIArea4.Vflip.bumpF (x / s) : ℂ)) ξ,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x; exact Work.FIArea4.Vflip.bumpF_nonneg _
  · intro x; exact bumpF_le_one _
  · intro x hx1 hx2
    have h1 : 1 ≤ x / s := by rw [one_le_div₀ hs]; linarith
    have h2 : x / s ≤ 2 := by rw [div_le_iff₀ hs]; linarith
    show (1 : ℝ) ≤ Work.FIArea4.Vflip.bumpF (x / s)
    rw [Work.FIArea4.Vflip.bumpF_eq_one h1 h2]
  · intro x hx
    obtain ⟨h1, h2⟩ := Work.FIArea4.Vflip.bumpF_support hx
    rw [lt_div_iff₀ hs] at h1
    rw [div_lt_iff₀ hs] at h2
    constructor <;> linarith
  · exact Work.FIArea4.Vflip.bumpF_continuous.comp (continuous_id.div_const s)
  · intro ξ; rfl
  · intro ξ
    have hfun : (fun x : ℝ => (Work.FIArea4.Vflip.bumpF (x / s) : ℂ))
        = fun x : ℝ => Work.FIArea4.Vflip.bumpFc (s⁻¹ • x) := by
      funext x
      simp only [Work.FIArea4.Vflip.bumpFc]
      congr 1
      congr 1
      rw [smul_eq_mul, div_eq_mul_inv, mul_comm]
    have hscale := Commons.Analysis.Fourier.fourier_comp_inv_smul (V := ℝ)
      (f := Work.FIArea4.Vflip.bumpFc) hs ξ
    have hnorm : ‖FourierTransform.fourier
          (fun x : ℝ => (Work.FIArea4.Vflip.bumpF (x / s) : ℂ)) ξ‖
        = s * ‖FourierTransform.fourier Work.FIArea4.Vflip.bumpFc (s * ξ)‖ := by
      rw [hfun, hscale, Module.finrank_self, pow_one, norm_smul, Real.norm_eq_abs,
        abs_of_pos hs, smul_eq_mul]
    have hb := hbnd (s * ξ)
    have hP : 0 < (1 + s * |ξ|) ^ (-(2 : ℝ)) := Real.rpow_pos_of_pos (by positivity) _
    have hle : C₀ * (1 + s * |ξ|) ^ (-(2 : ℝ))
        ≤ (C₀ + 1) * (1 + s * |ξ|) ^ (-(2 : ℝ)) := by
      nlinarith [hP]
    calc ‖FourierTransform.fourier
          (fun x : ℝ => (Work.FIArea4.Vflip.bumpF (x / s) : ℂ)) ξ‖
        = s * ‖FourierTransform.fourier Work.FIArea4.Vflip.bumpFc (s * ξ)‖ := hnorm
      _ ≤ s * (C₀ * (1 + |s * ξ|) ^ (-(2 : ℝ))) :=
            mul_le_mul_of_nonneg_left hb hs.le
      _ = s * (C₀ * (1 + s * |ξ|) ^ (-(2 : ℝ))) := by
            rw [abs_mul, abs_of_pos hs]
      _ ≤ (C₀ + 1) * s * (1 + s * |ξ|) ^ (-(2 : ℝ)) := by
            calc s * (C₀ * (1 + s * |ξ|) ^ (-(2 : ℝ)))
                ≤ s * ((C₀ + 1) * (1 + s * |ξ|) ^ (-(2 : ℝ))) :=
                  mul_le_mul_of_nonneg_left hle hs.le
              _ = (C₀ + 1) * s * (1 + s * |ξ|) ^ (-(2 : ℝ)) := by ring

end

end Work.FIArea4.UnitsFlat
