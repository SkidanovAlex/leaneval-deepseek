import Mathlib.Analysis.Real.Sqrt
import Submission.Work.UBBInputs3.MatLoc.gamma_sum_cross
import Submission.Work.UBBInputs3.MatLoc.gamma_sum_shift
import Submission.Work.UBBInputs3.MatLoc.prof_norm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.UBBInputs3.MatLoc.Rcorr_eq_one_sub_gamma`

The Lieb–Solovej identity `R(k) = 1 - γ_k`, relating the autocorrelation

    R(k) = Σ_s prof(s) prof(s+k)

of the normalised triangle profile to the "deficit"

    γ_k = ½ Σ_s (prof(s+k) - prof(s))² .

Both sums are over the *symmetric widening* `[-p-|k|, p+|k|]` of the support `[-p,p]` of the
profile, which is the range used in the definitions (`Defs.lean`); the widening is what
makes the identity hold *without* any boundary correction, because the profile vanishes off
`[-p,p]` and the translated range `[-p-|k|, p+|k|] - k` still contains `[-p,p]`.

## Proof

Expanding the square,

    ½ Σ_s (f(s+k) - f(s))² = ½ (Σ_s f(s+k)² + Σ_s f(s)² - 2 Σ_s f(s+k) f(s)) ,

and for a function `f` supported in `[-p,p]` with `Σ_s f(s)² = 1` each of the three sums
over the wide range collapses to the corresponding sum over `[-p,p]`:

* `Σ_s f(s+k)² = Σ_t f(t)² = 1`  — reindexing `t = s+k` and using the support
  (`Work.UBBInputs3.MatLoc.gamma_sum_shift`);
* `Σ_s f(s)² = 1`  — the support again (`RcorrAux.gamma_sq_wide`);
* `Σ_s f(s+k) f(s) = Σ_t f(t) f(t+k) = R(k)`  (`Work.UBBInputs3.MatLoc.gamma_sum_cross`).

This is `RcorrAux.gamma_eq_of_support`, a statement about an arbitrary such `f`; applying
it to `f = prof p`, whose support is `[-p,p]` (`prof_eq_zero_of_not_mem`) and whose
normalisation is `Σ_s prof(s)² = 1` (`prof_norm`), gives the claim.
-/

noncomputable section

open scoped BigOperators
open Finset

namespace Work.UBBInputs3.MatLoc

namespace RcorrAux

/-- **The profile vanishes off its support `[-p,p]`.** For `s ∉ [-p,p]` we have
`|s| ≥ p+1`, hence `tri p s = max 0 (p+1-|s|) = 0`, hence `prof p s = 0`. -/
lemma prof_eq_zero_of_not_mem (p : ℕ) {s : ℤ}
    (hs : s ∉ Finset.Icc (-(p:ℤ)) (p:ℤ)) : Work.UBBInputs3.prof p s = 0 := by
  have htri : Work.UBBInputs3.tri p s = 0 := by
    have hmem : ¬ ((-(p:ℤ) ≤ s) ∧ (s ≤ (p:ℤ))) := by
      simpa only [Finset.mem_Icc] using hs
    have h : (p:ℤ) < |s| := by
      rcases not_and_or.mp hmem with h1 | h2
      · have h1' : s < -(p:ℤ) := not_le.mp h1
        have : (p:ℤ) < -s := by omega
        exact lt_of_lt_of_le this (neg_le_abs s)
      · exact lt_of_lt_of_le (not_le.mp h2) (le_abs_self s)
    unfold Work.UBBInputs3.tri
    rw [max_eq_left_iff]
    have h2 : (p:ℤ) + 1 ≤ |s| := by omega
    have hs' : ((((p:ℤ) + 1 : ℤ) : ℝ)) ≤ ((|s| : ℤ) : ℝ) := by exact_mod_cast h2
    push_cast at hs'
    linarith
  unfold Work.UBBInputs3.prof
  rw [htri, zero_div]

/-- For a function supported in `[-p,p]`, the sum of `f²` over the widened range
`[-p-|k|, p+|k|]` equals the sum over `[-p,p]`: the extra indices contribute `0`. -/
lemma gamma_sq_wide (p : ℕ) (k : ℤ) {f : ℤ → ℝ}
    (hsupp : ∀ s, s ∉ Finset.Icc (-(p:ℤ)) (p:ℤ) → f s = 0) :
    (∑ s ∈ Finset.Icc (-(p:ℤ) - |k|) ((p:ℤ) + |k|), (f s)^2)
      = ∑ t ∈ Finset.Icc (-(p:ℤ)) (p:ℤ), (f t)^2 := by
  apply Work.UBBInputs3.sum_Icc_congr_of_eq_zero_outside (fun t : ℤ => (f t)^2)
  · have h : (0:ℤ) ≤ |k| := abs_nonneg k
    omega
  · have h : (0:ℤ) ≤ |k| := abs_nonneg k
    omega
  · intro t ht
    rw [hsupp t ht]
    ring

/-- **The general form of the Lieb–Solovej identity.** For any `f : ℤ → ℝ` supported in
`[-p,p]` and normalised by `Σ_s f(s)² = 1`,

    ½ Σ_{s∈[-p-|k|,p+|k|]} (f(s+k) - f(s))² = 1 - Σ_{s∈[-p,p]} f(s) f(s+k) . -/
lemma gamma_eq_of_support {f : ℤ → ℝ} (p : ℕ) (k : ℤ)
    (hsupp : ∀ s, s ∉ Finset.Icc (-(p:ℤ)) (p:ℤ) → f s = 0)
    (hnorm : ∑ s ∈ Finset.Icc (-(p:ℤ)) (p:ℤ), (f s)^2 = 1) :
    (1/2) * ∑ s ∈ Finset.Icc (-(p:ℤ) - |k|) ((p:ℤ) + |k|), (f (s+k) - f s)^2
      = 1 - ∑ s ∈ Finset.Icc (-(p:ℤ)) (p:ℤ), f s * f (s+k) := by
  have h1 := Work.UBBInputs3.MatLoc.gamma_sum_shift p k hsupp
  have h2 := gamma_sq_wide p k hsupp
  have h3 := Work.UBBInputs3.MatLoc.gamma_sum_cross p k hsupp
  have hexp : ∀ s ∈ Finset.Icc (-(p:ℤ) - |k|) ((p:ℤ) + |k|),
      (f (s+k) - f s)^2 = (f (s+k))^2 + (f s)^2 - 2*(f (s+k)*f s) := fun s _ => by ring
  rw [Finset.sum_congr rfl hexp]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [show (∑ s ∈ Finset.Icc (-(p:ℤ) - |k|) ((p:ℤ) + |k|), 2 * (f (s+k) * f s))
        = 2 * ∑ s ∈ Finset.Icc (-(p:ℤ) - |k|) ((p:ℤ) + |k|), f (s+k) * f s from
      (Finset.mul_sum _ _ _).symm]
  rw [h1, h2, h3, hnorm]
  ring

end RcorrAux

/-- **The Lieb–Solovej autocorrelation identity** `R(k) = 1 - γ_k` for the normalised
triangle profile: the autocorrelation and the squared first difference of the profile are
complementary. -/
theorem Rcorr_eq_one_sub_gamma (p : ℕ) (k : ℤ) :
    Work.UBBInputs3.Rcorr p k = 1 - Work.UBBInputs3.gamma p k := by
  have hsupp : ∀ s, s ∉ Finset.Icc (-(p:ℤ)) (p:ℤ) → Work.UBBInputs3.prof p s = 0 :=
    fun s hs => RcorrAux.prof_eq_zero_of_not_mem p hs
  have h := RcorrAux.gamma_eq_of_support p k hsupp (prof_norm p)
  simp only [Work.UBBInputs3.Rcorr, Work.UBBInputs3.gamma]
  linarith

end Work.UBBInputs3.MatLoc
