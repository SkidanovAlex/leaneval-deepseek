/-
# Multiplicativity of the `ExpBdd` shape under pointwise products

`Work.Asymptotics.ExpBdd c N f` records that `f : ℝ → ℂ` is smooth and that every iterated
derivative is dominated by `C_j (1+|x|)^N e^{-c x}`.  This file proves that the class is
closed under pointwise multiplication, with the two parameters *added*:

`ExpBdd c₁ N₁ f → ExpBdd c₂ N₂ g → ExpBdd (c₁ + c₂) (N₁ + N₂) (f * g)`.

The proof is the Leibniz rule for `iteratedDeriv` (`iteratedDeriv_mul`): the `j`-th derivative
of `f * g` is the finite sum `∑ k ≤ j, (j.choose k) f^{(k)} g^{(j-k)}`, and each summand is
bounded by the product of the two given bounds, with
`e^{-c₁x} e^{-c₂x} = e^{-(c₁+c₂)x}` and `(1+|x|)^{N₁}(1+|x|)^{N₂} = (1+|x|)^{N₁+N₂}`.
-/
import Mathlib
import Submission.Work.Asymptotics.highPartDefs

namespace Work.Asymptotics

theorem ExpBdd_mul {c₁ c₂ : ℝ} {N₁ N₂ : ℕ} {f g : ℝ → ℂ}
    (hf : Work.Asymptotics.ExpBdd c₁ N₁ f) (hg : Work.Asymptotics.ExpBdd c₂ N₂ g) :
    Work.Asymptotics.ExpBdd (c₁ + c₂) (N₁ + N₂) (f * g) := by
  refine ⟨hf.1.mul hg.1, fun j => ?_⟩
  choose Cf hCf0 hCf using hf.2
  choose Cg hCg0 hCg using hg.2
  refine ⟨∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * Cf k * Cg (j - k),
    Finset.sum_nonneg fun k _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCf0 k)) (hCg0 (j - k)),
    fun x => ?_⟩
  have hleib : iteratedDeriv j (f * g) x =
      ∑ k ∈ Finset.range (j + 1), (j.choose k : ℂ) * iteratedDeriv k f x *
        iteratedDeriv (j - k) g x :=
    iteratedDeriv_mul (hf.1.contDiffAt.of_le le_top) (hg.1.contDiffAt.of_le le_top)
  have hbnd : ∀ k ∈ Finset.range (j + 1),
      ‖(j.choose k : ℂ) * iteratedDeriv k f x * iteratedDeriv (j - k) g x‖
        ≤ (j.choose k : ℝ) * Cf k * Cg (j - k) * (1 + |x|) ^ (N₁ + N₂)
            * Real.exp (-((c₁ + c₂) * x)) := by
    intro k _
    have hmain : ‖iteratedDeriv k f x‖ * ‖iteratedDeriv (j - k) g x‖
        ≤ Cf k * Cg (j - k) * (1 + |x|) ^ (N₁ + N₂) * Real.exp (-((c₁ + c₂) * x)) := by
      have h1 := hCf k x
      have h2 := hCg (j - k) x
      have hp1 : (0 : ℝ) ≤ Cf k * (1 + |x|) ^ N₁ * Real.exp (-(c₁ * x)) :=
        mul_nonneg (mul_nonneg (hCf0 k) (pow_nonneg (by positivity) _)) (Real.exp_pos _).le
      have hexp : Real.exp (-(c₁ * x)) * Real.exp (-(c₂ * x))
          = Real.exp (-((c₁ + c₂) * x)) := by
        rw [← Real.exp_add]; congr 1; ring
      have hpair : (Cf k * (1 + |x|) ^ N₁ * Real.exp (-(c₁ * x)))
            * (Cg (j - k) * (1 + |x|) ^ N₂ * Real.exp (-(c₂ * x)))
          = Cf k * Cg (j - k) * (1 + |x|) ^ (N₁ + N₂) * Real.exp (-((c₁ + c₂) * x)) := by
        rw [pow_add]
        calc Cf k * (1 + |x|) ^ N₁ * Real.exp (-(c₁ * x))
              * (Cg (j - k) * (1 + |x|) ^ N₂ * Real.exp (-(c₂ * x)))
            = Cf k * Cg (j - k) * ((1 + |x|) ^ N₁ * (1 + |x|) ^ N₂)
                * (Real.exp (-(c₁ * x)) * Real.exp (-(c₂ * x))) := by ring
          _ = Cf k * Cg (j - k) * ((1 + |x|) ^ N₁ * (1 + |x|) ^ N₂)
                * Real.exp (-((c₁ + c₂) * x)) := by rw [hexp]
      calc ‖iteratedDeriv k f x‖ * ‖iteratedDeriv (j - k) g x‖
          ≤ (Cf k * (1 + |x|) ^ N₁ * Real.exp (-(c₁ * x)))
              * (Cg (j - k) * (1 + |x|) ^ N₂ * Real.exp (-(c₂ * x))) :=
            mul_le_mul h1 h2 (norm_nonneg _) hp1
        _ = _ := hpair
    rw [norm_mul, norm_mul, Complex.norm_natCast]
    nlinarith [hmain, Nat.cast_nonneg (α := ℝ) (j.choose k), hCf0 k, hCg0 (j - k),
      norm_nonneg (iteratedDeriv k f x), norm_nonneg (iteratedDeriv (j - k) g x)]
  calc ‖iteratedDeriv j (f * g) x‖
      = ‖∑ k ∈ Finset.range (j + 1),
          (j.choose k : ℂ) * iteratedDeriv k f x * iteratedDeriv (j - k) g x‖ := by
        rw [hleib]
    _ ≤ ∑ k ∈ Finset.range (j + 1),
          ‖(j.choose k : ℂ) * iteratedDeriv k f x * iteratedDeriv (j - k) g x‖ :=
        norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * Cf k * Cg (j - k)
          * (1 + |x|) ^ (N₁ + N₂) * Real.exp (-((c₁ + c₂) * x)) :=
        Finset.sum_le_sum hbnd
    _ = (∑ k ∈ Finset.range (j + 1), (j.choose k : ℝ) * Cf k * Cg (j - k))
          * (1 + |x|) ^ (N₁ + N₂) * Real.exp (-((c₁ + c₂) * x)) := by
        rw [Finset.sum_mul, Finset.sum_mul]

end Work.Asymptotics
