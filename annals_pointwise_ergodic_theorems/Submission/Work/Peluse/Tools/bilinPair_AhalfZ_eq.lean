import Mathlib
import Submission.Work.Peluse.Nodes
import Submission.Work.Analysis.InverseTheory.Basic

/-!
# `⟨Ã_N(f,g), h⟩ = N₀ · Λ^{N₀,N}_{half}(h,f,g)`

The two sides are the same double sum, written in the two orders:

* `bilinPair (AhalfZ N P f g) h = ∑_x Ã_N(f,g)(x) · h(x)`, where
  `Ã_N(f,g)(x) = (1/N) ∑_{N/2 < n ≤ N} f(x+n) g(x+P(n))`;
* `N₀ · LambdaHalfZ N₀ N P h f g = (1/N) ∑_x h(x) ∑_{N/2 < y ≤ N} f(x+y) g(x+P(y))`.

After unfolding both sides the identity is the scalar identity
`N₀ · ((N₀)(N))⁻¹ = N⁻¹` together with the commutativity of `ℂ` inside the `tsum`, so the
support hypotheses `SupportIn · N₀` are not needed for it: the equality is an identity between
the formal series and holds for arbitrary `f, g, h : ℤ → ℂ`.  (The support hypotheses are kept
because the statement is used in that context by the `Peluse` area.)
-/

namespace Work.Peluse.Tools

/-- Pull the scalar out of `∑' x, (c * A x) * B x` and swap the two factors. -/
lemma tsum_mul_swap (c : ℂ) (A B : ℤ → ℂ) :
    (∑' x : ℤ, (c * A x) * B x) = c * ∑' x : ℤ, B x * A x := by
  rw [show (∑' x : ℤ, (c * A x) * B x) = (∑' x : ℤ, c * (B x * A x)) from
    tsum_congr (fun x => by ring)]
  rw [tsum_mul_left]

/-- `N₀ · ((N₀ · N)⁻¹ · T) = N⁻¹ · T` for `N₀, N > 0`. -/
lemma natCast_mul_inv_mul_inv (N₀ N : ℕ) (hN₀ : 0 < N₀) (hN : 0 < N) (T : ℂ) :
    (N₀ : ℂ) * (((N₀ : ℂ) * (N : ℂ))⁻¹ * T) = ((N : ℂ))⁻¹ * T := by
  have h0 : (N₀ : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hN₀)
  have h1 : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hN)
  field_simp

/-- The scalar `(N : ℝ)⁻¹`, seen in `ℂ`, is `(N : ℂ)⁻¹`. -/
lemma ofReal_inv_natCast_eq (N : ℕ) : ((((N : ℝ))⁻¹ : ℝ) : ℂ) = ((N : ℂ))⁻¹ := by
  rw [Complex.ofReal_inv, Complex.ofReal_natCast]

theorem bilinPair_AhalfZ_eq {N₀ N : ℕ} (hN₀ : 0 < N₀) (hN : 0 < N) (P : Polynomial ℤ) (f g h : ℤ → ℂ)
    (hs0 : Work.Peluse.SupportIn h N₀) (hs1 : Work.Peluse.SupportIn f N₀)
    (hs2 : Work.Peluse.SupportIn g N₀) :
    Work.Analysis.InverseTheory.bilinPair (Work.Analysis.InverseTheory.AhalfZ N P f g) h
      = (N₀ : ℂ) * Work.Peluse.LambdaHalfZ N₀ N P h f g := by
  simp only [Work.Analysis.InverseTheory.bilinPair, Work.Analysis.InverseTheory.AhalfZ,
    Work.Peluse.LambdaHalfZ]
  rw [ofReal_inv_natCast_eq]
  rw [tsum_mul_swap]
  rw [natCast_mul_inv_mul_inv N₀ N hN₀ hN]

end Work.Peluse.Tools
