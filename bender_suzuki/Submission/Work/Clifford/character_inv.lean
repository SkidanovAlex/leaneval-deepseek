import Mathlib
import Submission.Work.Clifford.Basic
import Submission.Work.Clifford.charpoly_pow_sub_one_roots

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.character_inv`

For a finite-dimensional complex representation `V` of a finite group `G` and `g : G`, the
character of `V` at `g⁻¹` is the complex conjugate of its value at `g`:
`V.character g⁻¹ = starRingEnd ℂ (V.character g)`.

The proof reduces to a statement of linear algebra.  Choosing `n = |G|`, we have `g ^ n = 1`,
hence `T := V.ρ g` satisfies `T ^ n = 1`, so that `T ^ (n - 1) = T⁻¹` and
`V.ρ g⁻¹ = (V.ρ g) ^ (n - 1)`.  The trace of an endomorphism of a finite-dimensional complex
vector space is the sum of the roots of its characteristic polynomial
(`Module.End.trace_eq_sum_roots_charpoly_of_splits`); the characteristic polynomial of `T⁻¹` has
as roots the complex conjugates of those of `T`, since every eigenvalue of `T` is an `n`-th root
of unity (this is the delegated lemma `charpoly_pow_sub_one_roots` / `star_trace_eq_trace_pow`).
Finally `starRingEnd ℂ` commutes with the (finite) sum of a multiset.
-/

noncomputable section

open Classical

namespace Work.Clifford

/-- For an endomorphism `T` of a finite-dimensional complex vector space with `T ^ n = 1`
(and `n > 0`), the trace of `T ^ (n - 1) = T⁻¹` is the complex conjugate of the trace of `T`. -/
theorem star_trace_eq_trace_pow {W : Type*} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (T : W →ₗ[ℂ] W) (n : ℕ) (hn : 0 < n) (hT : T ^ n = 1) :
    starRingEnd ℂ (LinearMap.trace ℂ W T) = LinearMap.trace ℂ W (T ^ (n - 1)) := by
  rw [Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _),
      Module.End.trace_eq_sum_roots_charpoly_of_splits (IsAlgClosed.splits _)]
  rw [map_multiset_sum]
  rw [charpoly_pow_sub_one_roots T n hn hT]

theorem character_inv {G : Type*} [Group G] [Fintype G] (V : FDRep ℂ G) (g : G) :
    V.character g⁻¹ = starRingEnd ℂ (V.character g) := by
  set n : ℕ := Fintype.card G with hn
  have hnpos : 0 < n := by rw [hn]; exact Fintype.card_pos
  have hgn : g ^ n = 1 := by rw [hn]; exact pow_card_eq_one
  have hT : (V.ρ g) ^ n = 1 := by rw [← map_pow, hgn, map_one]
  have htr : starRingEnd ℂ (LinearMap.trace ℂ (↥V.V) (V.ρ g))
      = LinearMap.trace ℂ (↥V.V) ((V.ρ g) ^ (n - 1)) :=
    star_trace_eq_trace_pow (V.ρ g) n hnpos hT
  have hnn : n - 1 + 1 = n := by omega
  have hg : g⁻¹ = g ^ (n - 1) := by
    apply inv_eq_of_mul_eq_one_left
    rw [← pow_succ, hnn, hgn]
  have hpow : V.ρ g⁻¹ = (V.ρ g) ^ (n - 1) := by rw [hg, map_pow]
  rw [show V.character g⁻¹ = LinearMap.trace ℂ (↥V.V) (V.ρ g⁻¹) from rfl]
  rw [show V.character g = LinearMap.trace ℂ (↥V.V) (V.ρ g) from rfl]
  rw [htr, hpow]

end Work.Clifford
