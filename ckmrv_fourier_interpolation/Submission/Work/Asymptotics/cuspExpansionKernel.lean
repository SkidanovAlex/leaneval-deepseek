/-
# The cusp-`i∞` expansion of the CKMRV kernel along the contour, uniformly on a compact `K ⊆ 𝒟`

Target: `Work.Asymptotics.cuspExpansionKernel`.  The proof assembles the expansion

`K^{(d)}(τ,it) = Aexp (Gcusp ℓ d) τ t + O((1+t)^M e^{-π t})`   for `τ ∈ K`, `t ≥ 1`,

from three ingredients:

* `Work.Asymptotics.CuspExp.kernelKfun_cuspExp`: `K^{(d)}(τ,z) = MK ℓ d τ z + O(cuspG z 3 1)`
  for `Im z ≥ T(K)`, where the explicit model `MK` (`CuspExp/Models.lean`) is obtained by
  replacing every atom of the explicit kernel by its truncated cusp expansion in `E = e^{πiz}`;
* `Work.Asymptotics.CuspExp.cuspModel_bound`: the model differs from the non-decaying part
  `AexpZ (Gcusp ℓ d)` by `O(‖E(z)‖)` — the `E^{-2}`, `E^{-1}`, `E^{0}` coefficients of the
  difference cancel algebraically;
* `Work.Asymptotics.CuspExp.smallT_bound`: on the compact piece `1 ≤ t ≤ T` of the contour the
  difference `Kaxis - Aexp` is bounded (the kernel is continuous there: all coincidences
  `j(τ) = j(it)` are removable).
-/
import Mathlib
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.CuspExp.Basic
import Submission.Work.Asymptotics.CuspExp.Exp
import Submission.Work.Asymptotics.CuspExp.Models
import Submission.Work.Asymptotics.CuspExp.kernelKfun_cuspExp
import Submission.Work.Asymptotics.CuspExp.cuspModel_bound
import Submission.Work.Asymptotics.CuspExp.smallT_bound

open UpperHalfPlane

namespace Work.Asymptotics

lemma cuspW_imagAxis (t : ℝ) (ht : 0 < t) : cuspW (Work.Kernels.imagAxis t ht) = 1 + t := by
  have hcoe : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ) = (t : ℂ) * Complex.I := rfl
  have him : (Work.Kernels.imagAxis t ht).im = t := by
    rw [← UpperHalfPlane.coe_im, hcoe]
    simp
  have hre : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ).re = 0 := by
    rw [hcoe]; simp
  unfold cuspW
  rw [him, hre]
  simp

lemma cuspG_imagAxis_one (t : ℝ) (ht : 0 < t) (M : ℝ) :
    cuspG (Work.Kernels.imagAxis t ht) M 1 = (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
  unfold cuspG
  rw [cuspW_imagAxis t ht, norm_Ept_imagAxis t ht, zpow_one]

/-- The model estimate at a contour point. -/
lemma mk_bound_axis (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ C M : ℝ, 0 < C ∧ 0 ≤ M ∧ ∀ τ ∈ K, ∀ (t : ℝ) (ht : 0 < t),
      ‖MK ℓ d τ (Work.Kernels.imagAxis t ht) - AexpZ (Gcusp ℓ d) τ (Work.Kernels.imagAxis t ht)‖
        ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
  obtain ⟨C, M, hC, hM, hb⟩ := CuspExp.cuspModel_bound ℓ d hd hK
  refine ⟨C, M, hC, hM, fun τ hτ t ht => ?_⟩
  have h1 := hb τ hτ (Work.Kernels.imagAxis t ht)
  rw [cuspW_imagAxis t ht, norm_Ept_imagAxis t ht] at h1
  exact h1

/-- The kernel estimate at a contour point `z = it`, `t ≥ T`, in terms of `Aexp`. -/
lemma kernel_axis_bound (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K) :
    ∃ C M T : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 < T ∧ ∀ τ ∈ K, ∀ (t : ℝ), T ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t‖
        ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * t)) := by
  obtain ⟨Cm, Mm, hCm, hMm, hm⟩ := mk_bound_axis ℓ d hd hK
  obtain ⟨T, hT, C, hC, hCb⟩ := CuspExp.kernelKfun_cuspExp ℓ (K := K) hK
  refine ⟨C + Cm, max 3 Mm, max T 1, by positivity, by positivity, lt_max_of_lt_left hT,
    fun τ hτ t ht => ?_⟩
  have htT : T ≤ t := le_trans (le_max_left _ _) ht
  have hT1 : (0 : ℝ) < max T 1 := lt_max_of_lt_left hT
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le hT1 ht
  set z : ℍ := Work.Kernels.imagAxis t htpos with hz
  have hzim : z.im = t := by
    rw [hz]
    rw [← UpperHalfPlane.coe_im, show ((Work.Kernels.imagAxis t htpos : ℍ) : ℂ)
      = (t : ℂ) * Complex.I from rfl]
    simp
  have hAz : Aexp (Gcusp ℓ d) τ t = AexpZ (Gcusp ℓ d) τ z := by
    rw [hz]; exact (AexpZ_imagAxis _ _ _ htpos).symm
  have hsplit : Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Aexp (Gcusp ℓ d) τ t =
      (Work.Kernels.Kfun ℓ d τ z - MK ℓ d τ z) + (MK ℓ d τ z - AexpZ (Gcusp ℓ d) τ z) := by
    rw [hAz, Work.Kernels.Kaxis, dif_pos htpos, hz]
    ring
  rcases hd with h8 | h24
  · subst h8
    obtain ⟨hKp, _⟩ := hCb τ hτ z (by rw [hzim]; exact htT)
    have h1 : ‖Work.Kernels.Kfun ℓ 8 τ z - MK ℓ 8 τ z‖ ≤ C * cuspG z 3 1 := hKp
    have h2 : ‖MK ℓ 8 τ z - AexpZ (Gcusp ℓ 8) τ z‖ ≤ Cm * (1 + t) ^ Mm * Real.exp (-(Real.pi * t)) := by
      have h := hm τ hτ t htpos
      rwa [← hz] at h
    have h3 : ‖(Work.Kernels.Kfun ℓ 8 τ z - MK ℓ 8 τ z) + (MK ℓ 8 τ z - AexpZ (Gcusp ℓ 8) τ z)‖
        ≤ C * cuspG z 3 1 + Cm * (1 + t) ^ Mm * Real.exp (-(Real.pi * t)) :=
      le_trans (norm_add_le _ _) (add_le_add h1 h2)
    rw [hsplit]
    refine le_trans h3 ?_
    rw [cuspG_imagAxis_one t htpos, hz] at *
    have hw : (1:ℝ) ≤ 1 + t := by linarith
    have he : (0:ℝ) < Real.exp (-(Real.pi * t)) := Real.exp_pos _
    have h3' := Real.rpow_le_rpow_of_exponent_le hw (le_max_left (3:ℝ) Mm)
    have hmm' := Real.rpow_le_rpow_of_exponent_le hw (le_max_right (3:ℝ) Mm)
    have hG : (0:ℝ) ≤ (1 + t) ^ max 3 Mm := Real.rpow_nonneg (by linarith) _
    have h3n : (0:ℝ) ≤ (1 + t) ^ (3:ℝ) := Real.rpow_nonneg (by linarith) _
    have hmn : (0:ℝ) ≤ (1 + t) ^ Mm := Real.rpow_nonneg (by linarith) _
    have hkey : C * ((1 + t) ^ (3:ℝ) * Real.exp (-(Real.pi * t)))
        + Cm * (1 + t) ^ Mm * Real.exp (-(Real.pi * t))
        ≤ (C + Cm) * (1 + t) ^ max 3 Mm * Real.exp (-(Real.pi * t)) := by
      nlinarith [h3', hmm', hG, he, hC.le, hCm.le, h3n, hmn,
        mul_pos hC he, mul_pos hCm he]
    exact hkey
  · subst h24
    obtain ⟨_, hKm⟩ := hCb τ hτ z (by rw [hzim]; exact htT)
    have h1 : ‖Work.Kernels.Kfun ℓ 24 τ z - MK ℓ 24 τ z‖ ≤ C * cuspG z 3 1 := hKm
    have h2 : ‖MK ℓ 24 τ z - AexpZ (Gcusp ℓ 24) τ z‖ ≤ Cm * (1 + t) ^ Mm * Real.exp (-(Real.pi * t)) := by
      have h := hm τ hτ t htpos
      rwa [← hz] at h
    have h3 : ‖(Work.Kernels.Kfun ℓ 24 τ z - MK ℓ 24 τ z) + (MK ℓ 24 τ z - AexpZ (Gcusp ℓ 24) τ z)‖
        ≤ C * cuspG z 3 1 + Cm * (1 + t) ^ Mm * Real.exp (-(Real.pi * t)) :=
      le_trans (norm_add_le _ _) (add_le_add h1 h2)
    rw [hsplit]
    refine le_trans h3 ?_
    rw [cuspG_imagAxis_one t htpos, hz] at *
    have hw : (1:ℝ) ≤ 1 + t := by linarith
    have he : (0:ℝ) < Real.exp (-(Real.pi * t)) := Real.exp_pos _
    have h3' := Real.rpow_le_rpow_of_exponent_le hw (le_max_left (3:ℝ) Mm)
    have hmm' := Real.rpow_le_rpow_of_exponent_le hw (le_max_right (3:ℝ) Mm)
    have hG : (0:ℝ) ≤ (1 + t) ^ max 3 Mm := Real.rpow_nonneg (by linarith) _
    have h3n : (0:ℝ) ≤ (1 + t) ^ (3:ℝ) := Real.rpow_nonneg (by linarith) _
    have hmn : (0:ℝ) ≤ (1 + t) ^ Mm := Real.rpow_nonneg (by linarith) _
    have hkey : C * ((1 + t) ^ (3:ℝ) * Real.exp (-(Real.pi * t)))
        + Cm * (1 + t) ^ Mm * Real.exp (-(Real.pi * t))
        ≤ (C + Cm) * (1 + t) ^ max 3 Mm * Real.exp (-(Real.pi * t)) := by
      nlinarith [h3', hmm', hG, he, hC.le, hCm.le, h3n, hmn,
        mul_pos hC he, mul_pos hCm he]
    exact hkey

theorem cuspExpansionKernel (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {K : Set UpperHalfPlane} (hK : IsCompact K) (hsub : K ⊆ Work.Asymptotics.DomainD) :
    ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ K → 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
          ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) := by
  obtain ⟨Ck, Mk, Tk, hCk, hMk, hTk, hkb⟩ := kernel_axis_bound ℓ d hd hK
  obtain ⟨Cs, hCs, hsb⟩ := CuspExp.smallT_bound ℓ d hd hK hsub (T := max Tk 1) (by positivity)
  refine ⟨max Cs (Ck * Real.exp (-(Real.pi * max Tk 1)) + 1), max Mk 0, max Tk 1,
    lt_max_of_lt_left (by positivity), by positivity, by positivity, fun τ t hτ ht1 => ?_⟩
  have hT0pos : (0:ℝ) < max Tk 1 := lt_max_of_lt_left hTk
  rcases le_or_gt t (max Tk 1) with ht | ht
  · -- the compact piece of the contour
    have hb := hsb τ hτ t ht1 ht
    refine le_trans hb ?_
    have hw : (1:ℝ) ≤ 1 + t := by linarith
    have h1 : (1:ℝ) ≤ (1 + t) ^ max Mk 0 := Real.one_le_rpow hw (by positivity)
    have h2 : (1:ℝ) ≤ Real.exp (-(Real.pi * (t - max Tk 1))) := by
      rw [Real.one_le_exp_iff]
      nlinarith [Real.pi_pos]
    have hA : (0:ℝ) ≤ (1 + t) ^ max Mk 0 := Real.rpow_nonneg (by linarith) _
    have hB : (0:ℝ) ≤ Real.exp (-(Real.pi * (t - max Tk 1))) := (Real.exp_pos _).le
    calc Cs ≤ Cs * ((1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - max Tk 1)))) :=
          le_mul_of_one_le_right hCs.le (by nlinarith [h1, h2])
      _ ≤ max Cs (Ck * Real.exp (-(Real.pi * max Tk 1)) + 1) * (1 + t) ^ max Mk 0
            * Real.exp (-(Real.pi * (t - max Tk 1))) := by
          calc Cs * ((1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - max Tk 1))))
              = Cs * (1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - max Tk 1))) := by ring
            _ ≤ max Cs (Ck * Real.exp (-(Real.pi * max Tk 1)) + 1) * (1 + t) ^ max Mk 0
                  * Real.exp (-(Real.pi * (t - max Tk 1))) := by
                refine mul_le_mul_of_nonneg_right ?_ hB
                exact mul_le_mul_of_nonneg_right (le_max_left _ _) hA
  · -- beyond the threshold
    have ht2 : max Tk 1 ≤ t := le_of_lt ht
    have ht3 : Tk ≤ t := le_trans (le_max_left _ _) ht2
    have hb := hkb τ hτ t ht3
    refine le_trans hb ?_
    have hw : (1:ℝ) ≤ 1 + t := by linarith
    have h2 : (1 + t) ^ Mk ≤ (1 + t) ^ max Mk 0 :=
      Real.rpow_le_rpow_of_exponent_le hw (le_max_left _ _)
    have hexp : Real.exp (-(Real.pi * t))
        = Real.exp (-(Real.pi * (t - max Tk 1))) * Real.exp (-(Real.pi * max Tk 1)) := by
      rw [← Real.exp_add]; congr 1; ring
    have h7 : (0:ℝ) ≤ (1 + t) ^ max Mk 0 := Real.rpow_nonneg (by linarith) _
    have h5 : (0:ℝ) < Real.exp (-(Real.pi * (t - max Tk 1))) := Real.exp_pos _
    have h4 : (0:ℝ) < Real.exp (-(Real.pi * max Tk 1)) := Real.exp_pos _
    have hB : (0:ℝ) ≤ (1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - max Tk 1))) :=
      mul_nonneg h7 h5.le
    calc Ck * (1 + t) ^ Mk * Real.exp (-(Real.pi * t))
        = Ck * Real.exp (-(Real.pi * max Tk 1))
            * ((1 + t) ^ Mk * Real.exp (-(Real.pi * (t - max Tk 1)))) := by
          rw [hexp]; ring
      _ ≤ Ck * Real.exp (-(Real.pi * max Tk 1))
            * ((1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - max Tk 1)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_pos hCk h4).le
          exact mul_le_mul_of_nonneg_right h2 h5.le
      _ ≤ (Ck * Real.exp (-(Real.pi * max Tk 1)) + 1)
            * ((1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - max Tk 1)))) := by
          refine mul_le_mul_of_nonneg_right (by linarith) hB
      _ ≤ max Cs (Ck * Real.exp (-(Real.pi * max Tk 1)) + 1) * (1 + t) ^ max Mk 0
            * Real.exp (-(Real.pi * (t - max Tk 1))) := by
          calc (Ck * Real.exp (-(Real.pi * max Tk 1)) + 1)
                * ((1 + t) ^ max Mk 0 * Real.exp (-(Real.pi * (t - max Tk 1))))
              = (Ck * Real.exp (-(Real.pi * max Tk 1)) + 1) * (1 + t) ^ max Mk 0
                  * Real.exp (-(Real.pi * (t - max Tk 1))) := by ring
            _ ≤ max Cs (Ck * Real.exp (-(Real.pi * max Tk 1)) + 1) * (1 + t) ^ max Mk 0
                  * Real.exp (-(Real.pi * (t - max Tk 1))) := by
                refine mul_le_mul_of_nonneg_right ?_ h5.le
                exact mul_le_mul_of_nonneg_right (le_max_right _ _) h7

end Work.Asymptotics
