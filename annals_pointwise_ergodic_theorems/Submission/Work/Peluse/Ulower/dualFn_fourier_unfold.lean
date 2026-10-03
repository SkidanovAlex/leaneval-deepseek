import Mathlib
import Submission.Work.Peluse.Tools.dualFn_supportIn

/-!
# Unfolding the Fourier transform of Peluse's dual function `F₂`

Peluse's dual function (`Work.Peluse.dualFn`) is

`dualFn N P f₀ f₁ (x) = (1/N) ∑_{y ∈ [N]} f₀ (x - P y) · f₁ (x + y - P y)`.

This file computes its Fourier transform: for every real `ξ`,

`∑_x dualFn N P f₀ f₁ (x) · e(ξ x) = (1/N) ∑_{y ∈ [N]} e(ξ · P(y)) · ∑_u f₀ u · e(ξ u) · f₁ (u + y)`,

where `e(t) = exp(2πi t)`.

The proof is the elementary change of variable `u = x - P(y)`, once for each `y`: the shift
`x ↦ x + P(y)` is an additive bijection of `ℤ` (`Equiv.addRight`), under which
`dualFn`'s `y`-th summand turns into the `u`-th summand of the right-hand side, times the
character `e(ξ·P(y))`; the character splits as `e(ξ(u + P y)) = e(ξ u) · e(ξ P y)`.
Everything is finitely supported, so all the `tsum`s are genuine finite sums.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.Ulower

noncomputable section

/-- The additive character `x ↦ e(ξ x) = exp(2πiξx)` on `ℤ`. -/
private def chiP (ξ : ℝ) (x : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * ξ * (x : ℝ))

private lemma chiP_add (ξ : ℝ) (m n : ℤ) : chiP ξ (m + n) = chiP ξ m * chiP ξ n := by
  simp only [chiP, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The stated Fourier unfold. -/
theorem dualFn_fourier_unfold {N : ℕ} (hN : 1 ≤ N) (P : Polynomial ℤ) {f₀ f₁ : ℤ → ℂ}
    (hf₀ : Work.Peluse.FinSuppZ f₀) (hf₁ : Work.Peluse.FinSuppZ f₁) (ξ : ℝ) :
    (∑' x : ℤ, Work.Peluse.dualFn N P f₀ f₁ x * Complex.exp (2 * Real.pi * Complex.I * ξ * (x : ℝ)))
      = ((N : ℂ))⁻¹ * ∑ y ∈ Finset.Icc 1 N,
          Complex.exp (2 * Real.pi * Complex.I * ξ * (((P.eval (y : ℤ) : ℤ)) : ℝ)) *
            (∑' u : ℤ, f₀ u * Complex.exp (2 * Real.pi * Complex.I * ξ * (u : ℝ)) *
              f₁ (u + (y : ℤ))) := by
  classical
  change (∑' x : ℤ, Work.Peluse.dualFn N P f₀ f₁ x * chiP ξ x)
      = ((N : ℂ))⁻¹ * ∑ y ∈ Finset.Icc 1 N,
          chiP ξ (P.eval (y : ℤ)) *
            (∑' u : ℤ, f₀ u * chiP ξ u * f₁ (u + (y : ℤ)))
  obtain ⟨B₀, hB₀⟩ := hf₀
  obtain ⟨B₁, hB₁⟩ := hf₁
  set B : ℕ := max B₀ (max B₁ N) with hBdef
  have hB0 : Work.Peluse.SupportIn f₀ B := hB₀.mono (le_max_left _ _)
  have hB1 : Work.Peluse.SupportIn f₁ B :=
    hB₁.mono (le_trans (le_max_left _ _) (le_max_right _ _))
  have hNB : N ≤ B := le_trans (le_max_right _ _) (le_max_right _ _)
  have hNpos : 0 < N := hN
  -- ### Summability of the individual terms
  have hsummable : ∀ y ∈ Finset.Icc 1 N,
      Summable (fun x : ℤ =>
        f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ)) * chiP ξ x) := by
    intro y hy
    have hyN : y ≤ N := (Finset.mem_Icc.mp hy).2
    have hyB : (y : ℤ) ≤ (B : ℤ) := by exact_mod_cast le_trans hyN hNB
    have hPy : |P.eval (y : ℤ)| ≤ ((Work.Peluse.polySup P B : ℕ) : ℤ) :=
      Work.Peluse.Tools.eval_abs_le_polySup P (Int.natCast_nonneg y) hyB
    refine summable_of_ne_finset_zero
      (s := Finset.Icc (-(((B + Work.Peluse.polySup P B : ℕ)) : ℤ))
        (((B + Work.Peluse.polySup P B : ℕ)) : ℤ)) (fun x hx => ?_)
    have hxabs : (((B + Work.Peluse.polySup P B : ℕ)) : ℤ) < |x| := by
      rw [Finset.mem_Icc] at hx
      rcases not_and_or.mp hx with h | h
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hcast : (((B + Work.Peluse.polySup P B : ℕ)) : ℤ)
        = (B : ℤ) + ((Work.Peluse.polySup P B : ℕ) : ℤ) := by push_cast; ring
    rw [hcast] at hxabs
    have hkey : (B : ℕ) < (x - P.eval (y : ℤ)).natAbs := by
      have h1 : |x| - |P.eval (y : ℤ)| ≤ |x - P.eval (y : ℤ)| :=
        abs_sub_abs_le_abs_sub x (P.eval (y : ℤ))
      have h2 : (B : ℤ) < |x| - |P.eval (y : ℤ)| := by linarith
      have h3 : (B : ℤ) < |x - P.eval (y : ℤ)| := lt_of_lt_of_le h2 h1
      have h4 : (B : ℤ) < (((x - P.eval (y : ℤ)).natAbs : ℕ) : ℤ) := by
        rwa [Int.natCast_natAbs]
      exact_mod_cast h4
    rw [hB0 _ hkey]
    ring
  -- ### Step 1: unfold the dual function
  have hstep1a : ∀ x : ℤ, Work.Peluse.dualFn N P f₀ f₁ x * chiP ξ x =
      ((N : ℂ))⁻¹ * (∑ y ∈ Finset.Icc 1 N,
        f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ)) * chiP ξ x) := by
    intro x
    rw [Work.Peluse.dualFn, mul_assoc, Finset.sum_mul]
  have hstep1 : (∑' x : ℤ, Work.Peluse.dualFn N P f₀ f₁ x * chiP ξ x)
      = ((N : ℂ))⁻¹ * (∑ y ∈ Finset.Icc 1 N, ∑' x : ℤ,
        f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ)) * chiP ξ x) := by
    rw [tsum_congr hstep1a, tsum_mul_left]
    congr 1
    exact Summable.tsum_finsetSum (fun y hy => hsummable y hy)
  -- ### Step 2: change the variable `x ↦ x + P(y)` in each `y`-summand
  have key : ∀ y : ℕ,
      (∑' x : ℤ,
        f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ)) * chiP ξ x)
        = chiP ξ (P.eval (y : ℤ)) * (∑' u : ℤ, f₀ u * chiP ξ u * f₁ (u + (y : ℤ))) := by
    intro y
    have hpt : ∀ x : ℤ,
        f₀ (x + (-(P.eval (y : ℤ)))) * f₁ (x + (-(P.eval (y : ℤ))) + (y : ℤ))
            * chiP ξ (x + (-(P.eval (y : ℤ))) + P.eval (y : ℤ))
          = f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ)) * chiP ξ x := by
      intro x
      have e3 : x + (-(P.eval (y : ℤ))) + P.eval (y : ℤ) = x := by ring
      have e2 : x + (-(P.eval (y : ℤ))) + (y : ℤ) = x + (y : ℤ) - P.eval (y : ℤ) := by ring
      have e1 : x + (-(P.eval (y : ℤ))) = x - P.eval (y : ℤ) := by ring
      rw [e3, e2, e1]
    have hre : (∑' x : ℤ, f₀ (x + (-(P.eval (y : ℤ)))) * f₁ (x + (-(P.eval (y : ℤ))) + (y : ℤ))
            * chiP ξ (x + (-(P.eval (y : ℤ))) + P.eval (y : ℤ)))
        = ∑' u : ℤ, f₀ u * f₁ (u + (y : ℤ)) * chiP ξ (u + P.eval (y : ℤ)) := by
      have h := Equiv.tsum_eq (Equiv.addRight (-(P.eval (y : ℤ))))
        (fun u : ℤ => f₀ u * f₁ (u + (y : ℤ)) * chiP ξ (u + P.eval (y : ℤ)))
      simpa only [Equiv.coe_addRight] using h
    calc (∑' x : ℤ, f₀ (x - P.eval (y : ℤ)) * f₁ (x + (y : ℤ) - P.eval (y : ℤ)) * chiP ξ x)
        = ∑' x : ℤ, f₀ (x + (-(P.eval (y : ℤ)))) * f₁ (x + (-(P.eval (y : ℤ))) + (y : ℤ))
            * chiP ξ (x + (-(P.eval (y : ℤ))) + P.eval (y : ℤ)) := by
          refine tsum_congr (fun x => ?_)
          exact (hpt x).symm
      _ = ∑' u : ℤ, f₀ u * f₁ (u + (y : ℤ)) * chiP ξ (u + P.eval (y : ℤ)) := hre
      _ = chiP ξ (P.eval (y : ℤ)) * (∑' u : ℤ, f₀ u * chiP ξ u * f₁ (u + (y : ℤ))) := by
          have hsplit : (∑' u : ℤ, f₀ u * f₁ (u + (y : ℤ)) * chiP ξ (u + P.eval (y : ℤ)))
              = ∑' u : ℤ, chiP ξ (P.eval (y : ℤ)) * (f₀ u * chiP ξ u * f₁ (u + (y : ℤ))) :=
            tsum_congr (fun u => by rw [chiP_add]; ring)
          rw [hsplit, tsum_mul_left]
  -- ### Step 3: assemble
  rw [hstep1]
  congr 1
  exact Finset.sum_congr rfl (fun y _ => key y)

end

end Work.Peluse.Ulower
