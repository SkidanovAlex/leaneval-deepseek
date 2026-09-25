import Mathlib
import Submission.Work.CFT.Ledger.Coind
import Submission.Work.CFT.Ledger.CoindHm1
import Submission.Work.CFT.IdeleClassGroup.tateCohomology_zero_iso

/-!
# Shapiro's lemma in degree `0` for a coinduced representation

For an injective homomorphism `φ : G →* H` of finite groups and a `ℤ`-linear representation
`A` of `G`, the zeroth Tate cohomology of the coinduced representation `Rep.coind φ A` has the
same cardinality as the zeroth Tate cohomology of `A`.

On the level of invariants, the comparison is "evaluate at `1 : H`": an `H`-invariant
function on `H` takes the same value at every point, and the resulting `G`-invariant of `A`
descends to the presentation `Ĥ⁰ = A^G / N A` of the zeroth Tate cohomology, because the
norms correspond (`normMap_coindEval_one`).  The inverse is `constCoind` (the constant
function), and injectivity uses that an invariant element of `coind φ A` is determined by its
value at `1` together with `iota` (the section supported on the trivial coset).

## Main results

* `Work.CFT.Ledger.H0QuotientCoindEquiv` — `Ĥ⁰(coind φ A) ≃+ Ĥ⁰(A)` on the presentations.
* `Work.CFT.Ledger.tateCohomology_coind_zero_card` — the cardinality statement.
-/

open scoped Classical
open CategoryTheory
open Work.CFT.IdeleClassGroup

namespace Work.CFT.Ledger

noncomputable section

variable {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H]
variable (φ : G →* H) (A : Rep ℤ G)

/-- Evaluation at `1 : H`, as an additive homomorphism from the `H`-invariants of the
coinduced representation `coind φ A` to the `G`-invariants of `A`. -/
noncomputable def invariantsCoindEval :
    ↥(invariants (Rep.coind φ A)) →+ ↥(invariants A) where
  toFun f := ⟨coindEval φ A f.1 1, coindEval_mem_invariants φ A f⟩
  map_zero' := Subtype.ext rfl
  map_add' f g := Subtype.ext rfl

/-- `invariantsCoindEval` carries the norms of `coind φ A` into the norms of `A`: the value at
`1` of the norm of `g` is the norm of `evalSum g` (`normMap_coindEval_one`). -/
lemma invariantsCoindEval_norms_le (hφ : Function.Injective φ) :
    norms (Rep.coind φ A) ≤ (norms A).comap (invariantsCoindEval φ A) := by
  intro f hf
  obtain ⟨g, hg⟩ := AddMonoidHom.mem_range.mp
    (show f.1 ∈ (normMap (Rep.coind φ A)).range from hf)
  show (invariantsCoindEval φ A f).1 ∈ (normMap A).range
  refine AddMonoidHom.mem_range.mpr ⟨evalSum φ A g, ?_⟩
  show normMap A (evalSum φ A g) = coindEval φ A f.1 1
  rw [← normMap_coindEval_one φ A hφ g, hg]

/-- The comparison map `Ĥ⁰(coind φ A) → Ĥ⁰(A)` induced by evaluation at `1`. -/
abbrev H0QuotientCoindMap (hφ : Function.Injective φ) :
    (↥(invariants (Rep.coind φ A)) ⧸ norms (Rep.coind φ A)) →+
      (↥(invariants A) ⧸ norms A) :=
  QuotientAddGroup.map (norms (Rep.coind φ A)) (norms A) (invariantsCoindEval φ A)
    (invariantsCoindEval_norms_le φ A hφ)

/-- The comparison map is surjective: the class of a `G`-invariant `a` is the image of the
constant function with value `a`. -/
lemma H0QuotientCoindMap_surjective (hφ : Function.Injective φ) :
    Function.Surjective (H0QuotientCoindMap φ A hφ) := by
  intro q
  obtain ⟨a, rfl⟩ := QuotientAddGroup.mk'_surjective (norms A) q
  refine ⟨QuotientAddGroup.mk' (norms (Rep.coind φ A))
    ⟨constCoind φ A a, constCoind_mem_invariants φ A a⟩, ?_⟩
  rw [QuotientAddGroup.map_mk']
  have hE : invariantsCoindEval φ A ⟨constCoind φ A a, constCoind_mem_invariants φ A a⟩ = a :=
    Subtype.ext (coindEval_constCoind φ A a 1)
  rw [hE, QuotientAddGroup.mk'_apply]

/-- The comparison map is injective: an `H`-invariant of `coind φ A` whose value at `1` is a
norm is itself a norm, because it agrees with `N (iota 1 a)` everywhere. -/
lemma H0QuotientCoindMap_injective (hφ : Function.Injective φ) :
    Function.Injective (H0QuotientCoindMap φ A hφ) := by
  rw [injective_iff_map_eq_zero]
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective (norms (Rep.coind φ A)) q
  rw [QuotientAddGroup.map_mk', QuotientAddGroup.eq_zero_iff] at hq
  rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]
  obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp
    (show (invariantsCoindEval φ A x).1 ∈ (normMap A).range from hq)
  have hx1 : ∀ h : H, (Rep.coind φ A).ρ h x.1 = x.1 := (mem_invariants _ _).mp x.2
  have hnorm_inv : ∀ h : H,
      (Rep.coind φ A).ρ h (normMap (Rep.coind φ A) (iota φ A hφ (oneCoset φ) a))
        = normMap (Rep.coind φ A) (iota φ A hφ (oneCoset φ) a) :=
    (mem_invariants _ _).mp (normMap_mem_invariants (Rep.coind φ A) _)
  have hkey : x.1 = normMap (Rep.coind φ A) (iota φ A hφ (oneCoset φ) a) := by
    apply Subtype.ext
    funext h
    change coindEval φ A x.1 h
      = coindEval φ A (normMap (Rep.coind φ A) (iota φ A hφ (oneCoset φ) a)) h
    rw [coindEval_eq_one_of_invariant φ A x.1 hx1 h,
      coindEval_eq_one_of_invariant φ A _ hnorm_inv h,
      normMap_coindEval_one φ A hφ, evalSum_iota φ A hφ]
    exact ha.symm
  show x.1 ∈ (normMap (Rep.coind φ A)).range
  exact AddMonoidHom.mem_range.mpr ⟨iota φ A hφ (oneCoset φ) a, hkey.symm⟩

/-- Shapiro's lemma in degree `0`: the comparison map is an isomorphism
`Ĥ⁰(H, coind φ A) ≃+ Ĥ⁰(G, A)` on the presentations `A^G / N A`. -/
noncomputable def H0QuotientCoindEquiv (hφ : Function.Injective φ) :
    (↥(invariants (Rep.coind φ A)) ⧸ norms (Rep.coind φ A)) ≃+ (↥(invariants A) ⧸ norms A) :=
  AddEquiv.ofBijective (H0QuotientCoindMap φ A hφ)
    ⟨H0QuotientCoindMap_injective φ A hφ, H0QuotientCoindMap_surjective φ A hφ⟩

end

theorem tateCohomology_coind_zero_card {G H : Type} [Group G] [Group H] [Fintype G] [Fintype H]
    (φ : G →* H) (hφ : Function.Injective φ) (A : Rep ℤ G) :
    Nat.card ↥(tateCohomology (Rep.coind φ A) 0) = Nat.card ↥(tateCohomology A 0) := by
  obtain ⟨eB⟩ := Work.CFT.IdeleClassGroup.tateCohomology_zero_iso (Rep.coind φ A)
  obtain ⟨eA⟩ := Work.CFT.IdeleClassGroup.tateCohomology_zero_iso A
  refine Eq.trans (Nat.card_congr eB.toEquiv) (Eq.trans ?_ (Nat.card_congr eA.toEquiv).symm)
  exact Nat.card_congr (H0QuotientCoindEquiv φ A hφ).toEquiv

end Work.CFT.Ledger
