import Mathlib
import Submission.Work.Peluse.Pairing.dualFn_pairing
import Submission.Work.Peluse.Pairing.cs_dualFn_bound

/-!
# Cauchy–Schwarz against Peluse's dual function

This module proves the elementary step that turns a lower bound for the correlation
`Λ(f₀,f₁,f₂)` into a *lower* bound for the self-pairing of the dual function `F₂ = dualFn N P f₀ f₁`.

With `F := dualFn N P f₀ f₁` and `R := dSup P N₀ N` (the support radius of `F` whenever `f₀` is
supported in `[-N₀,N₀]`), the two ingredients are

* the pairing identity `Λ^{N₀,N}(f₀,f₁,f₂) = (1/N₀) ∑_z F(z) f₂(z)` of
  `Submission/Work/Peluse/Pairing/dualFn_pairing.lean` (Peluse's duality, Corollary 3.8), and
* the elementary Cauchy–Schwarz bound `‖∑_z F(z) f₂(z)‖² ≤ (2R+1) ∑_z ‖F(z)‖²` for a `1`-bounded
  `f₂` (`Submission/Work/Peluse/Pairing/cs_dualFn_bound.lean`).

Taking `f₂` in the pairing to be `star ∘ F` gives
`Λ^{N₀,N}(f₀,f₁,star ∘ F) = (1/N₀) ∑_z ‖F(z)‖²`, a nonnegative real; combining the two displayed
inequalities with `δ ≤ ‖Λ^{N₀,N}(f₀,f₁,f₂)‖` yields

`δ² N₀ / (2 R + 1) ≤ ‖Λ^{N₀,N}(f₀,f₁, star ∘ F)‖`.

This is the "energy" step of the elementary reduction of Area A2: it converts Peluse's correlation
hypothesis into a lower bound for the `ℓ²` mass of the dual function (which is then converted into
a lower bound for a Gowers box norm by the `BoxNorm/` chapter).
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open scoped BigOperators
open Polynomial

namespace Work.Peluse.Pairing

noncomputable section

/-- An integer outside the symmetric interval `symIcc R = [-R,R]` has `natAbs > R`. -/
private lemma natAbs_lt_of_not_mem_symIcc {R : ℕ} {x : ℤ} (h : x ∉ Work.Peluse.symIcc R) :
    R < x.natAbs := by
  rw [Work.Peluse.symIcc, Finset.mem_Icc] at h
  have h2 : ¬ x.natAbs ≤ R := by
    intro hle
    apply h
    have h3 : |x| ≤ (R : ℤ) := by rw [← Int.natCast_natAbs]; exact_mod_cast hle
    exact abs_le.mp h3
  omega

/-- The symmetric interval has `2R+1` elements. -/
private lemma card_symIcc (R : ℕ) : (Work.Peluse.symIcc R).card = 2 * R + 1 := by
  rw [Work.Peluse.symIcc, Int.card_Icc]
  have h : (R : ℤ) + 1 - (-(R : ℤ)) = ((2 * R + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [h, Int.toNat_natCast]

/-- The support statement for the dual function, *without* the hypothesis `M ≤ N` that
`Work.Peluse.Tools.dualFn_supportIn` carries (that hypothesis is not used in its proof: only the
first factor `f₀ (x - P y)` can vanish, and it does as soon as `|x| > N + polySup P M`). -/
theorem dualFn_supportIn_gen {N M : ℕ} (P : Polynomial ℤ) (f₀ f₁ : ℤ → ℂ)
    (hs0 : Work.Peluse.SupportIn f₀ N) :
    Work.Peluse.SupportIn (Work.Peluse.dualFn M P f₀ f₁) (Work.Peluse.dSup P N M) := by
  intro x hx
  rw [Work.Peluse.dSup] at hx
  simp only [Work.Peluse.dualFn]
  rw [Finset.sum_eq_zero (fun y hy => ?_), mul_zero]
  obtain ⟨hy1, hy2⟩ := Finset.mem_Icc.mp hy
  have hkey : (N : ℤ) < |x - P.eval ((y : ℕ) : ℤ)| := by
    have hS : |P.eval ((y : ℕ) : ℤ)| ≤ ((Work.Peluse.polySup P M : ℕ) : ℤ) :=
      Work.Peluse.Tools.eval_abs_le_polySup P (by positivity) (by exact_mod_cast hy2)
    have hx' : (N : ℤ) + ((Work.Peluse.polySup P M : ℕ) : ℤ) < |x| := by
      have h : ((N + Work.Peluse.polySup P M : ℕ) : ℤ) < ((x.natAbs : ℕ) : ℤ) := by
        exact_mod_cast hx
      push_cast at h
      exact h
    have h2 := abs_sub_abs_le_abs_sub x (P.eval ((y : ℕ) : ℤ))
    linarith
  have hnat : N < (x - P.eval ((y : ℕ) : ℤ)).natAbs := by
    have hcast : (N : ℤ) < (((x - P.eval ((y : ℕ) : ℤ)).natAbs : ℕ) : ℤ) := by
      rw [Int.natCast_natAbs]
      exact hkey
    exact_mod_cast hcast
  rw [hs0 _ hnat, zero_mul]

/-- For a function supported in `[-R,R]`, `∑'_x F x * star (F x)` is the `ℓ²` mass of `F`, seen
as a complex number. -/
private lemma tsum_mul_star_eq {R : ℕ} (F : ℤ → ℂ)
    (hF : ∀ x : ℤ, R < x.natAbs → F x = 0) :
    ∑' x : ℤ, F x * star (F x) = (((∑' x : ℤ, ‖F x‖ ^ 2) : ℝ) : ℂ) := by
  have h1 : ∀ x ∉ Work.Peluse.symIcc R, F x * star (F x) = 0 := by
    intro x hx
    rw [hF x (natAbs_lt_of_not_mem_symIcc hx), zero_mul]
  have h2 : ∀ x ∉ Work.Peluse.symIcc R, ‖F x‖ ^ 2 = 0 := by
    intro x hx
    rw [hF x (natAbs_lt_of_not_mem_symIcc hx)]
    norm_num
  rw [tsum_eq_sum h1, tsum_eq_sum h2, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem cs_dualFn_step {N₀ N : ℕ} (hN₀ : 0 < N₀) (hN : 0 < N) (P : Polynomial ℤ)
    (f₀ f₁ f₂ : ℤ → ℂ) (h₀ : Work.Peluse.SupportIn f₀ N₀) (h₁ : Work.Peluse.SupportIn f₁ N₀)
    (hb₂ : ∀ x : ℤ, ‖f₂ x‖ ≤ 1) {δ : ℝ} (hδ0 : 0 ≤ δ)
    (hδ : δ ≤ ‖Work.Peluse.LambdaZ N₀ N P f₀ f₁ f₂‖) :
    δ ^ 2 * (N₀ : ℝ) / (2 * ((Work.Peluse.dSup P N₀ N : ℕ) : ℝ) + 1)
      ≤ ‖Work.Peluse.LambdaZ N₀ N P f₀ f₁ (fun x => star (Work.Peluse.dualFn N P f₀ f₁ x))‖ := by
  set R : ℕ := Work.Peluse.dSup P N₀ N with hR
  set F : ℤ → ℂ := Work.Peluse.dualFn N P f₀ f₁ with hF
  have hsuppF : Work.Peluse.SupportIn F R := by
    rw [hF, hR]; exact dualFn_supportIn_gen P f₀ f₁ h₀
  have hN₀pos : (0 : ℝ) < (N₀ : ℝ) := by exact_mod_cast hN₀
  have hN₀ne : (N₀ : ℝ) ≠ 0 := ne_of_gt hN₀pos
  have hdenpos : (0 : ℝ) < 2 * (R : ℝ) + 1 := by positivity
  have hsnn : 0 ≤ ∑' x : ℤ, ‖F x‖ ^ 2 := tsum_nonneg (fun x => by positivity)
  -- Peluse's duality, for `f₂`
  have hpair₂ : Work.Peluse.LambdaZ N₀ N P f₀ f₁ f₂
      = ((N₀ : ℂ))⁻¹ * ∑' x : ℤ, F x * f₂ x := by
    rw [hF]; exact Work.Peluse.Pairing.dualFn_pairing P f₀ f₁ f₂ h₀
  have hnorm₂ : ‖Work.Peluse.LambdaZ N₀ N P f₀ f₁ f₂‖
      = ((N₀ : ℝ))⁻¹ * ‖∑' x : ℤ, F x * f₂ x‖ := by
    rw [hpair₂, norm_mul, norm_inv, Complex.norm_natCast]
  -- Cauchy–Schwarz
  have hcard : (((Work.Peluse.symIcc R).card : ℕ) : ℝ) = 2 * (R : ℝ) + 1 := by
    rw [card_symIcc]; push_cast; ring
  have hCS : ‖∑' x : ℤ, F x * f₂ x‖ ^ 2 ≤ (2 * (R : ℝ) + 1) * ∑' x : ℤ, ‖F x‖ ^ 2 := by
    have h := cs_dualFn_bound F f₂ hsuppF hb₂
    rwa [hcard] at h
  -- Peluse's duality, for `star ∘ F`: the self-pairing of `F` is its `ℓ²` mass
  have hpair₃ : Work.Peluse.LambdaZ N₀ N P f₀ f₁ (fun x => star (F x))
      = ((N₀ : ℂ))⁻¹ * (((∑' x : ℤ, ‖F x‖ ^ 2) : ℝ) : ℂ) := by
    rw [hF]
    rw [Work.Peluse.Pairing.dualFn_pairing P f₀ f₁
      (fun x => star (Work.Peluse.dualFn N P f₀ f₁ x)) h₀]
    congr 1
    exact tsum_mul_star_eq (Work.Peluse.dualFn N P f₀ f₁)
      (by intro x hx; rw [← hF]; exact hsuppF x hx)
  have hnorm₃ : ‖Work.Peluse.LambdaZ N₀ N P f₀ f₁ (fun x => star (F x))‖
      = ((N₀ : ℝ))⁻¹ * ∑' x : ℤ, ‖F x‖ ^ 2 := by
    rw [hpair₃, norm_mul, norm_inv, Complex.norm_natCast]
    have hcast : ‖((((∑' x : ℤ, ‖F x‖ ^ 2) : ℝ)) : ℂ)‖ = |(∑' x : ℤ, ‖F x‖ ^ 2)| :=
      RCLike.norm_ofReal _
    rw [hcast, abs_of_nonneg hsnn]
  -- the chain of inequalities
  have hkey₁ : δ * (N₀ : ℝ) ≤ ‖∑' x : ℤ, F x * f₂ x‖ := by
    have h := hδ
    rw [hnorm₂] at h
    have h2 := mul_le_mul_of_nonneg_right h hN₀pos.le
    have h3 : ((N₀ : ℝ))⁻¹ * ‖∑' x : ℤ, F x * f₂ x‖ * (N₀ : ℝ)
        = ‖∑' x : ℤ, F x * f₂ x‖ := by
      rw [mul_comm (((N₀ : ℝ))⁻¹ * ‖∑' x : ℤ, F x * f₂ x‖) ((N₀ : ℝ)), ← mul_assoc,
        mul_inv_cancel₀ hN₀ne, one_mul]
    rw [h3] at h2
    exact h2
  have hkey₂ : δ ^ 2 * (N₀ : ℝ) ^ 2 ≤ (2 * (R : ℝ) + 1) * ∑' x : ℤ, ‖F x‖ ^ 2 := by
    have h5 : (δ * (N₀ : ℝ)) ^ 2 ≤ ‖∑' x : ℤ, F x * f₂ x‖ ^ 2 :=
      pow_le_pow_left₀ (mul_nonneg hδ0 hN₀pos.le) hkey₁ 2
    have e : δ ^ 2 * (N₀ : ℝ) ^ 2 = (δ * (N₀ : ℝ)) ^ 2 := by ring
    linarith [h5, hCS, e]
  have hkey₃ : δ ^ 2 * (N₀ : ℝ) * (N₀ : ℝ) ≤ (∑' x : ℤ, ‖F x‖ ^ 2) * (2 * (R : ℝ) + 1) := by
    have e1 : δ ^ 2 * (N₀ : ℝ) ^ 2 = δ ^ 2 * (N₀ : ℝ) * (N₀ : ℝ) := by ring
    have e2 : (2 * (R : ℝ) + 1) * (∑' x : ℤ, ‖F x‖ ^ 2)
        = (∑' x : ℤ, ‖F x‖ ^ 2) * (2 * (R : ℝ) + 1) := by ring
    linarith [hkey₂, e1, e2]
  rw [hnorm₃]
  rw [show ((N₀ : ℝ))⁻¹ * (∑' x : ℤ, ‖F x‖ ^ 2) = (∑' x : ℤ, ‖F x‖ ^ 2) / (N₀ : ℝ) by
    rw [div_eq_inv_mul, mul_comm]]
  rw [div_le_div_iff₀ hdenpos hN₀pos]
  exact hkey₃

end

end Work.Peluse.Pairing
