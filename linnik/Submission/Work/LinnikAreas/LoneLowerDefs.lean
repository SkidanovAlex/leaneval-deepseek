/-
Vocabulary for the "exceptional zero forces a lower bound for `L(1,χ*)`" argument
(`Work.LinnikAreas.L_one_lower_relation`).

Everything lives at the level `N` of a primitive character `ψ`:
* `zlFun ψ s = ζ(s)·L(s,ψ)` — the meromorphic continuation of `Σ_n λ(n)n^{-s}`,
  `λ(n) = Σ_{d ∣ n} ψ(d)`, beyond `Re s = 1`;
* `triFun ψ β x s = ζ(s+β)L(s+β,ψ)·x^s/(s(s+1))` — the Perron integrand with the triangle
  ("second order") kernel `1/(s(s+1))`;
* `SsmC ψ β x = Σ_{n ≤ x} λ(n) n^{-β}(1 - n/x)` in complex form;
* `perrErr ψ β x T = Σ_n λ(n)n^{-(1+β)}min(1, 1/(T|log(x/n)|))` — the standard Perron
  truncation-error majorant.
-/
import Mathlib
import Submission.Work.LinnikAreas.RatioDefs
import Submission.Work.LinnikAreas.lamRealNonneg
import Submission.Work.LinnikAreas.lamAbelIntegral

namespace Work.LinnikAreas

open DirichletCharacter Complex
open scoped BigOperators

noncomputable section

/-- `ζ(s) · L(s,ψ)`: the holomorphic continuation of `Σ_n λ(n) n^{-s}` beyond `Re s = 1`. -/
def zlFun {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  riemannZeta s * LFunction ψ s

/-- The triangle-kernel Perron integrand `ζ(s+β)L(s+β,ψ) x^s/(s(s+1))`. -/
def triFun {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (β x : ℝ) (s : ℂ) : ℂ :=
  zlFun ψ (s + (β : ℂ)) * (x : ℂ) ^ s / (s * (s + 1))

/-- The complex version of the smoothed sum `S(x) = Σ_{n ≤ x} λ(n) n^{-β} (1 - n/x)`. -/
def SsmC {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (β x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, lam ψ n * (n : ℂ) ^ (-(β : ℂ)) * (1 - (n : ℂ) / (x : ℂ))

/-- The Perron error majorant `Σ_n λ(n) n^{-(1+β)} min(1, 1/(T|log(x/n)|))`. -/
def perrErr {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (β x T : ℝ) : ℝ :=
  ∑' n : ℕ, lamR ψ n * (n : ℝ) ^ (-(1 + β)) * min 1 (1 / (T * |Real.log (x / (n : ℝ))|))

end

end Work.LinnikAreas

namespace Work.LinnikAreas
open DirichletCharacter Complex
open scoped BigOperators
noncomputable section

/-- For a real character, `(lamR ψ n : ℂ) = lam ψ n`. -/
lemma lamR_cast {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ^ 2 = 1) (n : ℕ) :
    ((lamR ψ n : ℝ) : ℂ) = lam ψ n := by
  have h := (lamRealNonneg ψ hψ).1 n
  rw [lamR_apply, Complex.ext_iff]
  exact ⟨rfl, by simpa using h.symm⟩

/-- `lamR ψ 1 = 1`. -/
lemma lamR_one {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) : lamR ψ 1 = 1 := by
  rw [lamR_apply, lam_one_eq_one]; simp

/-- `LSeries (fun n => lam ψ n * n^{-β}) s = ζ(s+β)L(s+β,ψ)` for `Re (s+β) > 1`. -/
lemma LSeries_lam_shift {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1)
    {β : ℝ} {s : ℂ} (hs : 1 < (s + (β : ℂ)).re) :
    LSeries (fun n : ℕ => lam ψ n * (n : ℂ) ^ (-(β : ℂ))) s = zlFun ψ (s + (β : ℂ)) := by
  rw [zlFun, ← LSeries_lam ψ hs]
  rw [LSeries, LSeries]
  refine tsum_congr (fun n => ?_)
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term_def]
  · rw [LSeries.term_of_ne_zero hn, LSeries.term_of_ne_zero hn]
    have hn0 : (n : ℂ) ≠ 0 := by
      rw [← Complex.ofReal_natCast n]; exact_mod_cast hn
    have h1 : (n : ℂ) ^ (-(β : ℂ)) / (n : ℂ) ^ s = (n : ℂ) ^ (-(s + (β : ℂ))) := by
      rw [div_eq_mul_inv, ← Complex.cpow_neg, ← Complex.cpow_add _ _ hn0]
      congr 1; ring
    rw [mul_div_assoc, h1, div_eq_mul_inv, ← Complex.cpow_neg]

end

end Work.LinnikAreas
