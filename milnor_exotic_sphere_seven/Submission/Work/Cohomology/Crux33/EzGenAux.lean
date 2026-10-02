import Mathlib
import Submission.Work.Cohomology.Crux33.EzGen
import Submission.Work.Cohomology.Crux33.ShuffleIndex

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Finite shuffle bookkeeping for `ezGen_isCycle`

This file isolates the purely combinatorial content of the Eilenberg–Zilber chain-map identity
at bidegree `(3,3)`.

* `ezIdxL`/`ezCoefL` index the `20 · 7 = 140` terms of `∂ (ezGen 3 3 σ τ)` by the pair of
  monotone maps `(a_S ∘ δ_j, b_S ∘ δ_j) ∈ (⦋5⦌ ⟶ ⦋3⦌) × (⦋5⦌ ⟶ ⦋3⦌)` and the signed coefficient;
* `ezIdxR`/`ezCoefR` index the `4 · 10 + 4 · 10 = 80` terms of the right hand side
  `Σ_i (-1)^i ezGen(2,3)(δ_i σ, τ) + (-1)^3 Σ_i (-1)^i ezGen(3,2)(σ, δ_i τ)`;
* `ezLfun`/`ezRfun` collect the coefficients of a fixed index, and `ezLfun_eq_ezRfun` (a finite
  computation over the `110` occurring indices) says that the two collections agree;
* `ezSum_reindex` is the generic reindexing lemma turning `Σ_t c t • G (f t)` into the sum over the
  occurring indices with their total coefficients.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial

namespace Work.Cohomology.Crux33

/-- The index type: pairs of monotone maps `⦋5⦌ ⟶ ⦋3⦌`. -/
abbrev EzIdx : Type := (⦋5⦌ ⟶ ⦋3⦌) × (⦋5⦌ ⟶ ⦋3⦌)

/-- The index set of the `140` faces of the twenty `(3,3)`-shuffle cells. -/
abbrev EzTL : Type := PShuffle 3 3 × Fin 7

/-- The index set of the `80` terms of the two boundary shuffle chains. -/
abbrev EzTR : Type := (Fin 4 × PShuffle 2 3) ⊕ (Fin 4 × PShuffle 3 2)

/-- The two coordinates `(a_S ∘ δ_j, b_S ∘ δ_j)` of the `j`-th face of the `S`-th shuffle cell. -/
def ezIdxL (t : EzTL) : EzIdx :=
  (SimplexCategory.δ t.2 ≫ aHom t.1.1 t.1.2, SimplexCategory.δ t.2 ≫ bHom t.1.1 t.1.2)

/-- The signed coefficient `sign(S) · (-1)^j` of the `j`-th face of the `S`-th shuffle cell. -/
def ezCoefL (t : EzTL) : ℤ := shufSign (p := 3) (q := 3) t.1.1 * (-1 : ℤ) ^ (t.2 : ℕ)

/-- The two coordinates of the `i`-th term of the two boundary shuffle chains. -/
def ezIdxR (t : EzTR) : EzIdx :=
  Sum.elim
    (fun u : Fin 4 × PShuffle 2 3 => (aHom u.2.1 u.2.2 ≫ SimplexCategory.δ u.1, bHom u.2.1 u.2.2))
    (fun u : Fin 4 × PShuffle 3 2 => (aHom u.2.1 u.2.2, bHom u.2.1 u.2.2 ≫ SimplexCategory.δ u.1)) t

/-- The signed coefficient of the `i`-th term of the two boundary shuffle chains. -/
def ezCoefR (t : EzTR) : ℤ :=
  Sum.elim
    (fun u : Fin 4 × PShuffle 2 3 => ((-1 : ℤ) ^ (u.1 : ℕ)) * shufSign (p := 2) (q := 3) u.2.1)
    (fun u : Fin 4 × PShuffle 3 2 =>
      (-1 : ℤ) ^ 3 * ((-1 : ℤ) ^ (u.1 : ℕ)) * shufSign (p := 3) (q := 2) u.2.1) t

/-- The indices occurring in the boundary of the shuffle chain. -/
def ezSuppL : Finset EzIdx := (Finset.univ : Finset EzTL).image ezIdxL

/-- The indices occurring in the two boundary shuffle chains. -/
def ezSuppR : Finset EzIdx := (Finset.univ : Finset EzTR).image ezIdxR

/-- The union of the two index sets above. -/
def ezSupp : Finset EzIdx := ezSuppL ∪ ezSuppR

/-- The coefficient of the index `y` in `∂ (ezGen 3 3 σ τ)`. -/
def ezLfun (y : EzIdx) : ℤ := ∑ t : EzTL, if ezIdxL t = y then ezCoefL t else 0

/-- The coefficient of the index `y` in the two boundary shuffle chains. -/
def ezRfun (y : EzIdx) : ℤ := ∑ t : EzTR, if ezIdxR t = y then ezCoefR t else 0

/-- **The finite shuffle identity.**  The two coefficient functions agree on the indices occurring
in the boundary of the shuffle chain.  This is the `110`-index computation of the prism
cancellation: the `30` interior pairs of faces cancel and the `80` remaining faces are exactly the
faces of the two boundary shuffle chains. -/
theorem ezLfun_eq_ezRfun (y : EzIdx) (hy : y ∈ ezSupp) : ezLfun y = ezRfun y := by
  have h0 : (∑ y ∈ ezSupp, (ezLfun y - ezRfun y) ^ 2) = 0 := by decide
  have h1 : ∀ y ∈ ezSupp, (ezLfun y - ezRfun y) ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun y _ => sq_nonneg _)).mp h0
  have h2 : (ezLfun y - ezRfun y) * (ezLfun y - ezRfun y) = 0 := by
    simpa [pow_two] using h1 y hy
  have h3 : ezLfun y - ezRfun y = 0 := mul_self_eq_zero.mp h2
  omega

/-- **Reindexing a sum of generators.**  If every index `f t` lies in `S`, the total coefficient of
`G y` in `Σ_t c t • G (f t)` is `Σ_{t : f t = y} c t`. -/
theorem ezSum_reindex {ι : Type*} [Fintype ι] {M : Type*} [AddCommGroup M] [Module ℤ M]
    (f : ι → EzIdx) (c : ι → ℤ) (G : EzIdx → M) (S : Finset EzIdx) (hS : ∀ t, f t ∈ S) :
    (∑ t : ι, c t • G (f t)) = ∑ y ∈ S, (∑ t : ι, if f t = y then c t else 0) • G y := by
  calc (∑ t : ι, c t • G (f t))
      = ∑ t : ι, ∑ y ∈ S, (if f t = y then c t else 0) • G y := by
        refine Finset.sum_congr rfl (fun t _ => ?_)
        have hstep : ∀ y ∈ S, (if f t = y then c t else 0) • G y
            = (if f t = y then c t • G y else 0) := by
          intro y _
          by_cases h : f t = y
          · simp only [h, if_true]
          · simp only [h, if_false, zero_zsmul]
        rw [Finset.sum_congr rfl hstep, Finset.sum_eq_single (f t)]
        · simp
        · intro b _ hb
          simp only [if_neg (show ¬ (f t = b) from fun hh => hb hh.symm)]
        · intro h; exact absurd (hS t) h
    _ = ∑ y ∈ S, ∑ t : ι, (if f t = y then c t else 0) • G y := Finset.sum_comm
    _ = ∑ y ∈ S, (∑ t : ι, if f t = y then c t else 0) • G y := by
        refine Finset.sum_congr rfl (fun y _ => ?_)
        exact (map_sum (AddMonoidHom.mk' (fun n : ℤ => n • G y) (fun a b => add_zsmul (G y) a b))
          (fun t : ι => if f t = y then c t else 0) Finset.univ).symm

end Work.Cohomology.Crux33
