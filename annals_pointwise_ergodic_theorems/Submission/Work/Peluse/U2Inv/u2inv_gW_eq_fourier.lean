import Mathlib
import Submission.Work.Peluse.U2Inv.Defs

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Fourier inversion for the group weighted `Δ`-sum `gW`

This module proves `Work.Peluse.U2Inv.u2inv_gW_eq_fourier`: the group weighted difference sum
`gW L m f` (the transported, `μ_m`-weighted average of `Δ_{a,b} (pF L f)` over `ZMod (Gmod L)`)
can be recovered from its Fourier coefficients in the two shift variables, i.e.

`gW L m f = (G^2)⁻¹ * ∑_{k₁,k₂} dft (nu L m) k₁ * dft (nu L m) k₂ * TT L k₁ k₂ (pF L f)`.

The proof is the classical orthogonality argument: expanding the discrete Fourier transforms and
using the Fourier inversion formula `∑_k dft ν k · χ(a k) = N · ν a` on the cyclic group
`ZMod N`, all but the diagonal in the `(a,b)`-shifts cancels.

## Main results

* `sum_dft_mul_stdAddChar` : Fourier inversion in the shift variable;
* `key` : the two-variable orthogonality identity;
* `u2inv_gW_eq_fourier` : the target.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.U2Inv

noncomputable section

/-- **Fourier inversion in the shift variable.**  For a function `ν` on the cyclic group
`ZMod N`, the sum of its discrete Fourier transform against the characters `k ↦ χ (a * k)`
recovers `N` times the value at `a`. -/
lemma sum_dft_mul_stdAddChar {N : ℕ} [NeZero N] (ν : ZMod N → ℂ) (a : ZMod N) :
    ∑ k : ZMod N, ZMod.dft ν k * ZMod.stdAddChar (a * k) = (N : ℂ) * ν a := by
  have h := congr_fun (ZMod.dft_dft ν) (-a)
  simp only [smul_eq_mul, ZMod.dft_apply, neg_neg] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  have harg : -(k * -a) = k * a := by ring
  rw [harg, mul_comm a k]
  exact mul_comm _ _

/-- Fubini for a double sum in the two Fourier variables `k₁, k₂` followed by a triple sum in
`x, a, b`: the Fourier pair `(k₁, k₂)` may be moved past the shift triple `(x, a, b)`. -/
lemma swap23 {α : Type*} [Fintype α] (f : α → α → α → α → α → ℂ) :
    (∑ k₁, ∑ k₂, ∑ x, ∑ a, ∑ b, f k₁ k₂ x a b)
      = ∑ x, ∑ a, ∑ b, ∑ k₁, ∑ k₂, f k₁ k₂ x a b := by
  have h1 : (∑ k₁, ∑ k₂, ∑ x, ∑ a, ∑ b, f k₁ k₂ x a b)
      = ∑ k₁, ∑ x, ∑ k₂, ∑ a, ∑ b, f k₁ k₂ x a b := by
    refine Finset.sum_congr rfl (fun k₁ _ => ?_)
    exact Finset.sum_comm
  have h2 : (∑ k₁, ∑ x, ∑ k₂, ∑ a, ∑ b, f k₁ k₂ x a b)
      = ∑ k₁, ∑ x, ∑ a, ∑ k₂, ∑ b, f k₁ k₂ x a b := by
    refine Finset.sum_congr rfl (fun k₁ _ => ?_)
    refine Finset.sum_congr rfl (fun x _ => ?_)
    exact Finset.sum_comm
  have h3 : (∑ k₁, ∑ x, ∑ a, ∑ k₂, ∑ b, f k₁ k₂ x a b)
      = ∑ k₁, ∑ x, ∑ a, ∑ b, ∑ k₂, f k₁ k₂ x a b := by
    refine Finset.sum_congr rfl (fun k₁ _ => ?_)
    refine Finset.sum_congr rfl (fun x _ => ?_)
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact Finset.sum_comm
  have h4 : (∑ k₁, ∑ x, ∑ a, ∑ b, ∑ k₂, f k₁ k₂ x a b)
      = ∑ x, ∑ k₁, ∑ a, ∑ b, ∑ k₂, f k₁ k₂ x a b := Finset.sum_comm
  have h5 : (∑ x, ∑ k₁, ∑ a, ∑ b, ∑ k₂, f k₁ k₂ x a b)
      = ∑ x, ∑ a, ∑ k₁, ∑ b, ∑ k₂, f k₁ k₂ x a b := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    exact Finset.sum_comm
  have h6 : (∑ x, ∑ a, ∑ k₁, ∑ b, ∑ k₂, f k₁ k₂ x a b)
      = ∑ x, ∑ a, ∑ b, ∑ k₁, ∑ k₂, f k₁ k₂ x a b := by
    refine Finset.sum_congr rfl (fun x _ => ?_)
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact Finset.sum_comm
  exact h1.trans (h2.trans (h3.trans (h4.trans (h5.trans h6))))

/-- **Orthogonality in the two shift variables.**  Summing the two Fourier transforms against the
characters of the shifts `a` and `b` produces `N ^ 2` times the original bilinear form. -/
lemma key {N : ℕ} [NeZero N] (ν : ZMod N → ℂ) (A : ZMod N → ZMod N → ZMod N → ℂ) :
    (∑ k₁ : ZMod N, ∑ k₂ : ZMod N, ZMod.dft ν k₁ * ZMod.dft ν k₂ *
        (∑ x : ZMod N, ∑ a : ZMod N, ∑ b : ZMod N,
          A x a b * ZMod.stdAddChar (a * k₁) * ZMod.stdAddChar (b * k₂)))
      = (N : ℂ) ^ 2 * ∑ x : ZMod N, ∑ a : ZMod N, ∑ b : ZMod N, ν a * ν b * A x a b := by
  have hinner : ∀ x a b : ZMod N,
      (∑ k₁ : ZMod N, ∑ k₂ : ZMod N,
        ZMod.dft ν k₁ * ZMod.dft ν k₂ *
          (A x a b * ZMod.stdAddChar (a * k₁) * ZMod.stdAddChar (b * k₂)))
        = (N : ℂ) ^ 2 * (ν a * ν b * A x a b) := by
    intro x a b
    have h1 : (∑ k₁ : ZMod N, ∑ k₂ : ZMod N,
        ZMod.dft ν k₁ * ZMod.dft ν k₂ *
          (A x a b * ZMod.stdAddChar (a * k₁) * ZMod.stdAddChar (b * k₂)))
        = A x a b * ((∑ k₁ : ZMod N, ZMod.dft ν k₁ * ZMod.stdAddChar (a * k₁)) *
                     (∑ k₂ : ZMod N, ZMod.dft ν k₂ * ZMod.stdAddChar (b * k₂))) := by
      rw [Finset.sum_mul_sum]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k₁ _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k₂ _ => ?_)
      ring
    rw [h1, sum_dft_mul_stdAddChar, sum_dft_mul_stdAddChar]
    ring
  rw [show (∑ k₁ : ZMod N, ∑ k₂ : ZMod N, ZMod.dft ν k₁ * ZMod.dft ν k₂ *
        (∑ x : ZMod N, ∑ a : ZMod N, ∑ b : ZMod N,
          A x a b * ZMod.stdAddChar (a * k₁) * ZMod.stdAddChar (b * k₂)))
      = ∑ k₁ : ZMod N, ∑ k₂ : ZMod N, ∑ x : ZMod N, ∑ a : ZMod N, ∑ b : ZMod N,
          ZMod.dft ν k₁ * ZMod.dft ν k₂ *
            (A x a b * ZMod.stdAddChar (a * k₁) * ZMod.stdAddChar (b * k₂))
      from by simp only [Finset.mul_sum]]
  rw [swap23]
  rw [show (∑ x : ZMod N, ∑ a : ZMod N, ∑ b : ZMod N, ∑ k₁ : ZMod N, ∑ k₂ : ZMod N,
        ZMod.dft ν k₁ * ZMod.dft ν k₂ *
          (A x a b * ZMod.stdAddChar (a * k₁) * ZMod.stdAddChar (b * k₂)))
      = ∑ x : ZMod N, ∑ a : ZMod N, ∑ b : ZMod N, (N : ℂ) ^ 2 * (ν a * ν b * A x a b)
      from Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun a _ =>
             Finset.sum_congr rfl (fun b _ => hinner x a b)))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [Finset.mul_sum]

/-- The normalising factor `(G ^ 3)⁻¹` in front of `TT` may be moved out of the two Fourier
sums, since it does not depend on the Fourier variable. -/
lemma dft_double_mul_const {N : ℕ} [NeZero N] (ν : ZMod N → ℂ) (c : ℂ)
    (T : ZMod N → ZMod N → ℂ) :
    (∑ k₁ : ZMod N, ∑ k₂ : ZMod N,
        ZMod.dft ν k₁ * ZMod.dft ν k₂ * (c * T k₁ k₂))
      = c * ∑ k₁ : ZMod N, ∑ k₂ : ZMod N, ZMod.dft ν k₁ * ZMod.dft ν k₂ * T k₁ k₂ := by
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k₁ _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun k₂ _ => ?_)
  ring

theorem u2inv_gW_eq_fourier (L m : ℕ) (f : ℤ → ℂ) :
    Work.Peluse.U2Inv.gW L m f = (((Work.Peluse.U2Inv.Gmod L : ℂ)) ^ 2)⁻¹ *
      ∑ k₁ : ZMod (Work.Peluse.U2Inv.Gmod L), ∑ k₂ : ZMod (Work.Peluse.U2Inv.Gmod L),
        ZMod.dft (Work.Peluse.U2Inv.nu L m) k₁ * ZMod.dft (Work.Peluse.U2Inv.nu L m) k₂ *
          Work.Peluse.U2Inv.TT L k₁ k₂ (Work.Peluse.U2Inv.pF L f) := by
  simp only [gW, TT]
  rw [dft_double_mul_const]
  have hkey : (∑ k₁ : ZMod (Gmod L), ∑ k₂ : ZMod (Gmod L),
        ZMod.dft (nu L m) k₁ * ZMod.dft (nu L m) k₂ *
          (∑ x : ZMod (Gmod L), ∑ a : ZMod (Gmod L), ∑ b : ZMod (Gmod L),
            DeltaG a b (pF L f) x * ZMod.stdAddChar (a * k₁) * ZMod.stdAddChar (b * k₂)))
      = ((Gmod L : ℂ)) ^ 2 * ∑ x : ZMod (Gmod L), ∑ a : ZMod (Gmod L),
          ∑ b : ZMod (Gmod L), nu L m a * nu L m b * DeltaG a b (pF L f) x :=
    key (ν := nu L m) (A := fun x a b => DeltaG a b (pF L f) x)
  rw [hkey]
  have hN : ((Gmod L : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne (Gmod L))
  field_simp

end

end Work.Peluse.U2Inv
