import Mathlib
import Submission.Work.Kernels.Section5

namespace Work.Kernels.Section5Facts

open UpperHalfPlane ModularForm ModularGroup Matrix MeasureTheory
open scoped MatrixGroups ModularForm Modular Manifold Bundle

open Work.Kernels

/-!
# The third functional equation of `F = Fgen K` and `F̃ = Ftgen K̂`

CKMRV Corollary 5.2 (`corin4.1`) derives the functional equations of the pair
`(F, F̃) = (Fgen K, Ftgen K̂)` from the two equations satisfied by the kernel transform

  `F₂(τ,r) = 4 sin²(πr²/2) ∫_0^∞ K(τ,it) e^{-πr²t} dt`,

together with the definitional relation `K̂ = -K |^τ_{d/2} S` (Theorem 4.9).  The first two
equations (the action of `(T-I)²`) are the subject of `Work.Kernels.Fgen_T2` and
`Work.Kernels.Section5Facts.Ftgen_T2`; this file is the third,

  `F(τ,r) + (i/τ)^{d/2} F̃(Sτ,r) = e^{πiτr²}`.

Everything here is the definition of `Fgen`, `Ftgen`, `gaussTerm` and `kernelTransform`,
the definitional relation between `K` and `K̂`, the action of `S` on `ℍ`, and the elementary
algebraic identity

  `(i/t)^{d/2} · (-t⁻¹)^{-d/2} = 1`   whenever `(-i)^{d/2} = 1` and `t ≠ 0`.
-/

/-- The elementary algebraic identity behind the third functional equation: for
`(-I)^(d/2) = 1` and `t ≠ 0` one has `(I/t)^(d/2) · (-t⁻¹)^(-(d/2)) = 1`.

Indeed `(I/t)^(d/2) = I^(d/2) t^(-d/2)` and `(-t⁻¹)^(-(d/2)) = (-1)^(d/2) t^(d/2)`, so the
product is `(I·(-1))^(d/2) = (-I)^(d/2) = 1`. -/
lemma Fgen_third_Ipow_key (t : ℂ) (ht : t ≠ 0) (d : ℕ) (hdI : (-Complex.I) ^ (d / 2) = 1) :
    (Complex.I / t) ^ (d / 2) * (-t⁻¹) ^ (-((d : ℤ) / 2)) = 1 := by
  have hm : ((d : ℤ) / 2) = ((d / 2 : ℕ) : ℤ) := (Int.natCast_ediv d 2).symm
  rw [hm]
  have hconv : (-t⁻¹) ^ (-(((d / 2 : ℕ)) : ℤ)) = (-1 : ℂ) ^ (d / 2) * t ^ (d / 2) := by
    rw [_root_.zpow_neg, ← _root_.inv_zpow, zpow_natCast]
    have he : (-t⁻¹ : ℂ)⁻¹ = -t := by rw [inv_neg, inv_inv]
    rw [he, show (-t : ℂ) = (-1) * t by ring, mul_pow]
  calc (Complex.I / t) ^ (d / 2) * (-t⁻¹) ^ (-(((d / 2 : ℕ)) : ℤ))
      = (Complex.I / t) ^ (d / 2) * ((-1 : ℂ) ^ (d / 2) * t ^ (d / 2)) := by rw [hconv]
    _ = ((Complex.I / t) * (-1) * t) ^ (d / 2) := by rw [← mul_assoc, ← mul_pow, ← mul_pow]
    _ = (-Complex.I) ^ (d / 2) := by
          congr 1
          field_simp
    _ = 1 := hdI

/-- Pointwise form `K̂(τ,·) = -(τ)^{-d/2} K(Sτ,·)` of `K̂ = -K|^τ_{d/2}S` on the imaginary
axis, extended by `0` off `t > 0`: for every real `t` the two sides of `Kaxis` agree. -/
lemma Fgen_third_Kaxis {d : ℕ} {K Khat : ℍ → ℍ → ℂ}
    (hKhat : ∀ τ z : ℍ, Khat τ z = - (τ : ℂ) ^ (-((d : ℤ) / 2)) * K (ModularGroup.S • τ) z)
    (σ : ℍ) (t : ℝ) :
    Kaxis Khat σ t = - (σ : ℂ) ^ (-((d : ℤ) / 2)) * Kaxis K (ModularGroup.S • σ) t := by
  unfold Kaxis
  by_cases h : 0 < t
  · rw [dif_pos h, dif_pos h, hKhat]
  · rw [dif_neg h, dif_neg h, mul_zero]

/-- The relation `K̂ = -K|^τ_{d/2}S` lifted to the kernel transform:
`kernelTransform K̂ σ r = -(σ)^{-d/2} · kernelTransform K (Sσ) r`. -/
lemma Fgen_third_kernelTransform {d : ℕ} {K Khat : ℍ → ℍ → ℂ}
    (hKhat : ∀ τ z : ℍ, Khat τ z = - (τ : ℂ) ^ (-((d : ℤ) / 2)) * K (ModularGroup.S • τ) z)
    (σ : ℍ) (r : ℝ) :
    kernelTransform Khat σ r
      = - (σ : ℂ) ^ (-((d : ℤ) / 2)) * kernelTransform K (ModularGroup.S • σ) r := by
  unfold kernelTransform
  have hI : (∫ t in Set.Ioi 0,
        Kaxis Khat σ t * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
      = ∫ t in Set.Ioi 0, (-(σ : ℂ) ^ (-((d : ℤ) / 2))) *
          (Kaxis K (ModularGroup.S • σ) t *
            Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    dsimp only
    rw [Fgen_third_Kaxis hKhat σ t]
    ring
  rw [hI, integral_const_mul]
  ring

/-- **The third functional equation of CKMRV Corollary 5.2.**  If `K̂ = -K|^τ_{d/2}S`
and `(-i)^{d/2} = 1`, then the pair `(F, F̃) = (Fgen K, Ftgen K̂)` satisfies
`F(τ,r) + (i/τ)^{d/2} F̃(Sτ,r) = e^{πiτr²}`. -/
theorem Fgen_third {d : ℕ} (hdI : (-Complex.I) ^ (d / 2) = 1)
    {K Khat : UpperHalfPlane → UpperHalfPlane → ℂ}
    (hKhat : ∀ τ z : UpperHalfPlane,
      Khat τ z = - (τ : ℂ) ^ (-((d : ℤ) / 2)) * K (ModularGroup.S • τ) z) :
    ∀ (τ : UpperHalfPlane) (r : ℝ),
      Work.Kernels.Fgen K τ r + (Complex.I / (τ : ℂ)) ^ (d / 2)
          * Work.Kernels.Ftgen Khat (ModularGroup.S • τ) r = Work.Kernels.gaussTerm τ r := by
  intro τ r
  have hSS : ModularGroup.S • (ModularGroup.S • τ) = τ := by
    rw [UpperHalfPlane.ext_iff, UpperHalfPlane.modular_S_smul, UpperHalfPlane.modular_S_smul]
    simp
  have hcoe : ((ModularGroup.S • τ : ℍ) : ℂ) = -((τ : ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul]; simp
  have hkt := Fgen_third_kernelTransform hKhat (ModularGroup.S • τ) r
  rw [hSS, hcoe] at hkt
  have hkey := Fgen_third_Ipow_key (τ : ℂ) (UpperHalfPlane.ne_zero τ) d hdI
  simp only [Fgen, Ftgen]
  rw [hkt]
  have hX : (Complex.I / (τ : ℂ)) ^ (d / 2)
        * (-(-(τ : ℂ)⁻¹) ^ (-((d : ℤ) / 2)) * kernelTransform K τ r)
      = - kernelTransform K τ r := by
    rw [show (Complex.I / (τ : ℂ)) ^ (d / 2)
          * (-(-(τ : ℂ)⁻¹) ^ (-((d : ℤ) / 2)) * kernelTransform K τ r)
          = - ((Complex.I / (τ : ℂ)) ^ (d / 2) * (-(τ : ℂ)⁻¹) ^ (-((d : ℤ) / 2)))
              * kernelTransform K τ r by ring]
    rw [hkey]
    ring
  rw [hX]
  ring

end Work.Kernels.Section5Facts
