import Mathlib
import Submission.Work.Kernels.Section5

/-!
# `F̃` satisfies the second functional equation

CKMRV Corollary 5.2, second functional equation: if `K̂ = -K|^τ_{d/2}S` (Theorem 4.9) and
`F₂ = K|^τ_{d/2}(T-I)²S` vanishes, i.e.

  `F₂ |^τ_{d/2} S (T-I)² = 0`  (`h` below, in group-algebra form),

then the generating function `F̃ = Ftgen K̂` of (5.4) satisfies

  `F̃(τ+2) - 2F̃(τ+1) + F̃(τ) = 0`,

which is `T2op (Ftgen K̂ ·) = 0`.

The proof is the chain

  `Ftgen K̂ = - (Ftgen K)|^τ_{d/2} S`  (Section 4.4, `K̂ = -K|^τ_{d/2}S`),
  `T2op (X|^τ_{d/2}S) = slash (d/2) (S (T-I)²) X`  (`T2op_slash_S`),

so that `T2op (Ftgen K̂·) = - slash (d/2) (S(T-I)²) (Ftgen K·) = -0 = 0` by `h`.  The first
equality is the pointwise relation `K̂(τ,z) = -τ^{-d/2}K(S•τ,z)` pushed through the (Bochner)
integral defining `kernelTransform`; it is proved here directly so that the file is
self-contained.
-/

noncomputable section

namespace Work.Kernels.Section5Facts

theorem Ftgen_T2 {d : ℕ} {K Khat : UpperHalfPlane → UpperHalfPlane → ℂ}
    (hKhat : ∀ τ z : UpperHalfPlane,
      Khat τ z = - (τ : ℂ) ^ (-((d : ℤ) / 2)) * K (ModularGroup.S • τ) z)
    (h : ∀ r : ℝ, Work.Kernels.slash ((d : ℤ) / 2)
      (Work.Kernels.R_S * (Work.Kernels.R_T - 1) ^ 2)
      (fun τ : UpperHalfPlane => Work.Kernels.kernelTransform K τ r) = 0) :
    ∀ r : ℝ, Work.Kernels.T2op (fun τ : UpperHalfPlane => Work.Kernels.Ftgen Khat τ r) = 0 := by
  intro r
  -- Step 1: `Ftgen K̂ · r = - (Ftgen K · r) |^[d/2] S`, pointwise.
  have key : (fun τ : UpperHalfPlane => Work.Kernels.Ftgen Khat τ r)
      = - SlashAction.map ((d : ℤ) / 2) ModularGroup.S
          (fun σ : UpperHalfPlane => Work.Kernels.kernelTransform K σ r) := by
    funext τ
    show Work.Kernels.kernelTransform Khat τ r
      = - (SlashAction.map ((d : ℤ) / 2) ModularGroup.S
          (fun σ : UpperHalfPlane => Work.Kernels.kernelTransform K σ r)) τ
    rw [Work.Kernels.slash_S_apply]
    -- `Kaxis K̂ τ = -τ^{-d/2} · Kaxis K (S•τ)`, from the hypothesis `hKhat`.
    have hKax : ∀ t : ℝ, Work.Kernels.Kaxis Khat τ t
        = - (τ : ℂ) ^ (-((d : ℤ) / 2)) * Work.Kernels.Kaxis K (ModularGroup.S • τ) t := by
      intro t
      by_cases ht : 0 < t
      · rw [Work.Kernels.Kaxis, Work.Kernels.Kaxis, dif_pos ht, dif_pos ht, hKhat]
      · rw [Work.Kernels.Kaxis, Work.Kernels.Kaxis, dif_neg ht, dif_neg ht]; ring
    have hint : Work.Kernels.kernelTransform Khat τ r
        = - (τ : ℂ) ^ (-((d : ℤ) / 2))
            * Work.Kernels.kernelTransform K (ModularGroup.S • τ) r := by
      simp only [Work.Kernels.kernelTransform]
      have hintegrand :
          (fun t : ℝ => Work.Kernels.Kaxis Khat τ t
              * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))))
            = fun t : ℝ => (-(τ : ℂ) ^ (-((d : ℤ) / 2)))
                * (Work.Kernels.Kaxis K (ModularGroup.S • τ) t
                    * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) := by
        funext t
        rw [hKax t]
        ring
      rw [hintegrand, MeasureTheory.integral_const_mul]
      ring
    rw [hint]; ring
  -- Step 2: apply `T2op` and use the group-algebra form of the hypothesis.
  rw [key]
  change Work.Kernels.T2op (fun τ : UpperHalfPlane =>
      - (SlashAction.map ((d : ℤ) / 2) ModularGroup.S
          (fun σ : UpperHalfPlane => Work.Kernels.kernelTransform K σ r)) τ) = 0
  rw [Work.Kernels.T2op_neg', Work.Kernels.T2op_slash_S, h r]
  simp

end Work.Kernels.Section5Facts
