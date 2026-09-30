import Mathlib
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.RatHurewicz.homotopyFibreMap_exists
import Submission.Work.StemsB.PiMap

/-!
# Homotopy excision (Blakers–Massey): the interface

Area **RATHUREWICZ** (`Submission/Work/RatHurewicz/`).  This module records the *statement* of
**homotopy excision** (Blakers–Massey) for an open triad, in the form in which the classical proofs
of the Hurewicz statements use it.

## The statement, and the index conventions

Let `B, C ⊆ X` be open with `X = B ∪ C` (the classical formulation is for CW triads; the open-cover
version is the one recorded here) and let `x₀ ∈ B ∩ C`.  Put `m_B = p+1` for the largest integer
such that the classical relative groups `π_j(B, B∩C)` vanish for `j ≤ m_B` and similarly `m_C = q+1`
for `(C, B∩C)`.  The Blakers–Massey result for the triad `(X; B, C)` states that the map

`π_i(B, B∩C) → π_i(X, C)`

induced by the inclusions is an isomorphism for `i ≤ m_B + m_C - 1 = p + q + 1`.

In the `RelHomotopyGroup` indexing of `RelHomotopy.lean` (`RelHomotopyGroup i a₀ n` is the classical
relative group `π_{n+1}` of the pair, realised as `π_n` of the homotopy fibre of the inclusion),
the comparison map is

`excisionMap B C x₀ n : RelHomotopyGroup (interInclLeft B C) x₀ (n+1) →* RelHomotopyGroup (setIncl C) ⟨x₀,_⟩ (n+1)`,

built from `Work.RatHurewicz.homotopyFibreMap` (the canonical `(a,γ) ↦ (g a, f ∘ γ)` of the square of
inclusions) and `Work.StemsB.πmap`, and the isomorphism range is `n + 1 ≤ p + q`.

**Two traps, both avoided by the statement below** (the first draft of this file fell into both):
the cover hypothesis `B ∪ C = X` is essential (without it the statement is false, e.g.
`B = C = {x₀} ⊆ S²`), and the range is *not* `p + q + 1` — Blakers–Massey gives an isomorphism only
up to `m_B + m_C - 1` in the classical degrees, and the (mere) surjectivity at `m_B + m_C` cannot be
used to deduce vanishing of the target there.  A counterexample to the naive range: the open cover
of `S³` by two thickened hemispheres `B`, `C` (so `B ∩ C ≃ S²`, `B ≃ C ≃ pt`), where `p = q = 1`
but `π_4(X,C) ≅ π_4(S³) = ℤ/2` while `π_4(B, B∩C) ≅ π_3(S²) = ℤ` — the map is *not* an
isomorphism in classical degree `4 = m_B + m_C`.

Freudenthal's suspension theorem is the special case for the triad `(ΣX; CX₊, CX₋)` (with
`B = CX₊`, `C = CX₋`, `B ∩ C = X`): for `X` `(r-1)`-connected one has `m_B = m_C = r` and the result
gives that the suspension map `π_j(X) → π_{j+1}(ΣX)` is an isomorphism for `j ≤ 2r-2`.  It is not
stated separately because the workspace has no suspension functor.
-/

open scoped Topology unitInterval

namespace Work.RatHurewicz

noncomputable section

variable {X : Type} [TopologicalSpace X]

/-- **The inclusion of a subset** as a continuous map. -/
def setIncl (C : Set X) : C(↥C, X) where
  toFun x := x.1
  continuous_toFun := continuous_subtype_val

/-- **The inclusion `B ∩ C ↪ B`.** -/
def interInclLeft (B C : Set X) : C(↥(B ∩ C), ↥B) where
  toFun x := ⟨x.1, x.2.1⟩
  continuous_toFun := by fun_prop

/-- **The inclusion `B ∩ C ↪ C`.** -/
def interInclRight (B C : Set X) : C(↥(B ∩ C), ↥C) where
  toFun x := ⟨x.1, x.2.2⟩
  continuous_toFun := by fun_prop

/-- The square of inclusions of the triad commutes. -/
theorem excision_square (B C : Set X) :
    (setIncl B).comp (interInclLeft B C) = (setIncl C).comp (interInclRight B C) := by
  ext x
  rfl

/-- **The comparison map of the triad `(X; B, C)`**: the map
`π_i(B, B∩C) → π_i(X, C)` induced by the inclusions, in the `RelHomotopyGroup` indexing — so
`excisionMap B C x₀ n` lives on the index `n + 1`, i.e. on the classical relative group of degree
`n + 2`. -/
noncomputable def excisionMap (B C : Set X) (x₀ : ↥(B ∩ C)) (n : ℕ) :
    RelHomotopyGroup (interInclLeft B C) x₀ (n + 1) →*
      RelHomotopyGroup (setIncl C) ⟨x₀.1, x₀.2.2⟩ (n + 1) :=
  (Work.StemsB.homotopyGroupCast
      (homotopyFibreMap_basepoint (interInclLeft B C) (setIncl C) (setIncl B)
        (interInclRight B C) (excision_square B C) x₀) n).toMonoidHom.comp
    (Work.StemsB.πmap
      (homotopyFibreMap (interInclLeft B C) (setIncl C) (setIncl B) (interInclRight B C)
        (excision_square B C) x₀) n
      (homotopyFibreBasepoint (interInclLeft B C) x₀))

/-- **Homotopy excision (Blakers–Massey) for open triads.**

For an open cover `X = B ∪ C` (`hBC`, `hB`, `hC`) and `x₀ ∈ B ∩ C`: if the relative groups of
`(B, B∩C)` vanish up to `p` and those of `(C, B∩C)` up to `q` in the `RelHomotopyGroup` indexing
(i.e. the classical relative groups `π_j` vanish for `j ≤ p+1`, resp. `q+1`), then the comparison map
`excisionMap B C x₀ n` is bijective for `n + 1 ≤ p + q` (i.e. in the classical degrees
`j ≤ p + q + 1 = m_B + m_C - 1`). -/
def HomotopyExcision : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (B C : Set X) (hBC : B ∪ C = Set.univ)
    (hB : IsOpen B) (hC : IsOpen C) (x₀ : ↥(B ∩ C)) (p q : ℕ),
    (∀ k : ℕ, k ≤ p →
      Subsingleton (RelHomotopyGroup (interInclLeft B C) x₀ k)) →
    (∀ k : ℕ, k ≤ q →
      Subsingleton (RelHomotopyGroup (interInclRight B C) x₀ k)) →
    ∀ n : ℕ, n + 1 ≤ p + q → Function.Bijective (excisionMap B C x₀ n)

end

end Work.RatHurewicz
