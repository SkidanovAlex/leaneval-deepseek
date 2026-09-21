import Mathlib
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

namespace Commons.Geometry.Ulam

open scoped ContDiff Topology

noncomputable section

/-- Base case of the Faà-di-Bruno representation: the `0`-th derivative is the
function itself, and `J` is the constant `1`. -/
lemma exists_iteratedDeriv_rpow_zero (α : ℝ) :
    ∃ J : ℝ → (Fin 1 → ℝ) → ℝ,
      ∀ (u : ℝ → ℝ) (s : ℝ),
        ContDiff ℝ ∞ u → 0 < u s →
        iteratedDeriv 0 (fun x : ℝ => u x ^ α) s =
          J s (fun i : Fin 1 => iteratedDeriv i.1 u s) * u s ^ (α - 0) := by
  refine ⟨fun _ _ => 1, ?_⟩
  intro u s hu hpos
  rw [iteratedDeriv_zero]
  ring_nf

/-- First nontrivial case: the ordinary chain rule for a real power. -/
lemma exists_iteratedDeriv_rpow_one (α : ℝ) :
    ∃ J : ℝ → (Fin 2 → ℝ) → ℝ,
      ∀ (u : ℝ → ℝ) (s : ℝ),
        ContDiff ℝ ∞ u → 0 < u s →
        iteratedDeriv 1 (fun x : ℝ => u x ^ α) s =
          J s (fun i : Fin 2 => iteratedDeriv i.1 u s) * u s ^ (α - 1) := by
  refine ⟨fun _ v => α * v 1, ?_⟩
  intro u s hu hpos
  rw [iteratedDeriv_succ, iteratedDeriv_zero]
  have hdiff : DifferentiableAt ℝ u s := hu.differentiable (by simp) s
  have h := hdiff.hasDerivAt.rpow_const (p := α) (Or.inl (ne_of_gt hpos))
  rw [h.deriv]
  have h1 : iteratedDeriv 1 u s = deriv u s := by
    rw [iteratedDeriv_succ, iteratedDeriv_zero]
  change deriv u s * α * u s ^ (α - 1) =
    α * (fun i : Fin 2 => iteratedDeriv i.1 u s) 1 * u s ^ (α - 1)
  have h2 : (fun i : Fin 2 => iteratedDeriv i.1 u s) 1 = iteratedDeriv 1 u s := by
    norm_num
  rw [h2, h1]
  ring

/-- **Faà-di-Bruno representation for iterated derivatives of a real power.**

For a smooth positive function `u`, the `m`-th derivative of `u ^ α` is a
universal function `J` of `s` and the first `m+1` derivatives of `u`, times the
remaining power `u ^ (α - m)`.  This is the formal content of the paper's
“`J₁(s,t,f)` is a polynomial expression in `s,t,f,h(s)`, and the derivatives of
`h(s)`”: the paper applies it to `u(s) = f² - (s t + h(s))²`.

The lemma states only the representation identity (which defines `J`); the
polynomiality of `J` in its arguments is a separate, stronger statement. -/
lemma exists_iteratedDeriv_rpow (m : ℕ) (α : ℝ) :
    ∃ J : ℝ → (Fin (m + 1) → ℝ) → ℝ,
      ∀ (u : ℝ → ℝ) (s : ℝ),
        ContDiff ℝ ∞ u → 0 < u s →
        iteratedDeriv m (fun x : ℝ => u x ^ α) s =
          J s (fun i : Fin (m + 1) => iteratedDeriv i.1 u s) * u s ^ (α - m) := by
  let J : ℝ → (Fin (m + 1) → ℝ) → ℝ := fun _ v =>
    (∑ c : OrderedFinpartition m,
      (iteratedFDeriv ℝ c.length (fun x : ℝ => x ^ α) (v 0))
        (fun j : Fin c.length => v ⟨c.partSize j, Nat.lt_succ_of_le (c.partSize_le j)⟩))
      * v 0 ^ (m - α)
  refine ⟨J, ?_⟩
  intro u s hu hpos
  have hg : ContDiffAt ℝ ∞ (fun x : ℝ => x ^ α) (u s) :=
    Real.contDiffAt_rpow_const_of_ne (ne_of_gt hpos)
  have hf : ContDiffAt ℝ ∞ u s := hu.contDiffAt
  have hfaa := iteratedDeriv_vcomp_eq_sum_orderedFinpartition
    (g := fun x : ℝ => x ^ α) (f := u) (x := s) (n := ∞) (i := m) hg hf (WithTop.coe_le_coe.mpr le_top)
  have hcomp : ((fun x : ℝ => x ^ α) ∘ u) = fun x : ℝ => u x ^ α := rfl
  rw [hcomp] at hfaa
  rw [hfaa]
  dsimp [J]
  simp only [iteratedDeriv_zero]
  rw [mul_assoc, ← Real.rpow_add hpos]
  have hsum : (m : ℝ) - α + (α - m) = 0 := by ring
  rw [hsum, Real.rpow_zero, mul_one]

/-- **The `J₁` representation.**  Specialising the power identity to
`α = n + 1/2` and `m = n + 1`, the remaining power is `u ^ (-1/2) = 1 / √u`:
the `(n+1)`-st derivative of `(f² - L_s²)^{n+1/2}` has the paper's form
`J₁ / √(f² - L_s²)`. -/
lemma exists_J1_representation (n : ℕ) :
    ∃ J₁ : ℝ → (Fin (n + 2) → ℝ) → ℝ,
      ∀ (u : ℝ → ℝ) (s : ℝ),
        ContDiff ℝ ∞ u → 0 < u s →
        iteratedDeriv (n + 1) (fun x : ℝ => u x ^ ((n : ℝ) + 1 / 2)) s =
          J₁ s (fun i : Fin (n + 2) => iteratedDeriv i.1 u s) / Real.sqrt (u s) := by
  obtain ⟨J, hJ⟩ := exists_iteratedDeriv_rpow (n + 1) ((n : ℝ) + 1 / 2)
  refine ⟨J, ?_⟩
  intro u s hu hpos
  have h := hJ u s hu hpos
  have hpow : u s ^ (((n : ℝ) + 1 / 2) - ((n + 1 : ℕ) : ℝ)) = 1 / Real.sqrt (u s) := by
    have hexp : ((n : ℝ) + 1 / 2) - ((n + 1 : ℕ) : ℝ) = -(1 / 2) := by
      push_cast
      ring
    rw [hexp, Real.rpow_neg (le_of_lt hpos), Real.sqrt_eq_rpow]
    norm_num
  rw [h, hpow, div_eq_mul_inv]
  ring

/-- **The `J₂` representation.**  Specialising to `α = n - 1/2` and `m = n`,
the remaining power is again `u ^ (-1/2)`: the `n`-th derivative of
`(f² - L_s²)^{n-1/2}` has the form `J₂ / √(f² - L_s²)`, matching the centroid
equation. -/
lemma exists_J2_representation (n : ℕ) :
    ∃ J₂ : ℝ → (Fin (n + 1) → ℝ) → ℝ,
      ∀ (u : ℝ → ℝ) (s : ℝ),
        ContDiff ℝ ∞ u → 0 < u s →
        iteratedDeriv n (fun x : ℝ => u x ^ ((n : ℝ) - 1 / 2)) s =
          J₂ s (fun i : Fin (n + 1) => iteratedDeriv i.1 u s) / Real.sqrt (u s) := by
  obtain ⟨J, hJ⟩ := exists_iteratedDeriv_rpow n ((n : ℝ) - 1 / 2)
  refine ⟨J, ?_⟩
  intro u s hu hpos
  have h := hJ u s hu hpos
  have hpow : u s ^ (((n : ℝ) - 1 / 2) - (n : ℝ)) = 1 / Real.sqrt (u s) := by
    have hexp : ((n : ℝ) - 1 / 2) - (n : ℝ) = -(1 / 2) := by ring
    rw [hexp, Real.rpow_neg (le_of_lt hpos), Real.sqrt_eq_rpow]
    norm_num
  rw [h, hpow, div_eq_mul_inv]
  ring

end

end Commons.Geometry.Ulam
