import Mathlib
import Submission.Work.CharCore.star_trace_eq_trace_pow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Coherence.char_inv_eq_conj`

For a finite-dimensional complex representation `V` of a finite group `G` and any `g : G`,
the character of `V` at `g⁻¹` is the complex conjugate of its value at `g`:

`V.character g⁻¹ = starRingEnd ℂ (V.character g)`.

The character is a trace, so this is the statement that for a finite-order endomorphism the
trace of the inverse is the complex conjugate of the trace.  Choosing `n = |G|`, we have
`g ^ n = 1`, hence `T := V.ρ g` satisfies `T ^ n = 1`, so `g⁻¹ = g ^ (n - 1)` and
`V.ρ g⁻¹ = T ^ (n - 1)`.  The linear-algebra input

`starRingEnd ℂ (trace T) = trace (T ^ (n - 1))`  (`Work.CharCore.star_trace_eq_trace_pow`)

is that all eigenvalues of such a `T` are `n`-th roots of unity, so the eigenvalues of `T⁻¹`
are the conjugates of those of `T`.
-/

namespace Work.Coherence


theorem char_inv_eq_conj {G : Type*} [Group G] [Fintype G] (V : FDRep ℂ G) (g : G) :
    V.character g⁻¹ = starRingEnd ℂ (V.character g) := by
  set n : ℕ := Fintype.card G with hn
  have hnpos : 0 < n := by rw [hn]; exact Fintype.card_pos
  have hgn : g ^ n = 1 := by rw [hn]; exact pow_card_eq_one
  have hT : (V.ρ g) ^ n = 1 := by rw [← map_pow, hgn, map_one]
  have htr : starRingEnd ℂ (LinearMap.trace ℂ (↥V.V) (V.ρ g))
      = LinearMap.trace ℂ (↥V.V) ((V.ρ g) ^ (n - 1)) :=
    Work.CharCore.star_trace_eq_trace_pow (V.ρ g) n hnpos hT
  have hnn : n - 1 + 1 = n := by omega
  have hg : g⁻¹ = g ^ (n - 1) := by
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_succ, hnn, hgn]
  have hpow : V.ρ g⁻¹ = (V.ρ g) ^ (n - 1) := by rw [hg, map_pow]
  rw [show V.character g⁻¹ = LinearMap.trace ℂ (↥V.V) (V.ρ g⁻¹) from rfl]
  rw [show V.character g = LinearMap.trace ℂ (↥V.V) (V.ρ g) from rfl]
  rw [htr, hpow]

end Work.Coherence
