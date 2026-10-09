import Mathlib
import Submission.Work.SSGRoute.Step4CokerData
import Submission.Work.SSGRoute.overK
import Submission.Work.SSGRoute.ramifiedPlaces_finite_over_K
import Submission.Work.SSGRoute.local_transport
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.ZSplit.BaseChange
import Submission.Work.SSGRoute.ZConstruction.exists_finset_KConj_cover
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The place set `S` over `↥K` of Step 4 (the coker side of Schmidt–Wingberg §5)

The coker side of Step 4 works over the base field `↥K` rather than over `ℚ`: the local data `y`
lives in `H¹(k_S|K, E(n,τ))` and its local conditions are the level-`K` ones, i.e. they are
constant along `Gal(ℚ̄/K)`-conjugacy classes of places (`Work.SSGRoute.KConj`) and involve
ramification in `overK K Λ` and the place `p` seen over `↥K`.  The place set `S` that this requires
is therefore a set of representatives of the `Gal(ℚ̄/K)`-classes of the finite places of `ℚ̄` that
are *ramified in `Λ/K` or lie over `p`*, chosen inside the `ℚ`-conjugacy closure of the place set
`D.S` of the datum `D`:

* every element of `S` is `ℚ`-conjugate to an element of `D.S` (clause 4);
* every finite place of `ℚ` that is `ℚ`-conjugate to an element of `D.S` is `K`-conjugate to an
  element of `S` (clause 5);
* every finite place of `↥K` that ramifies in `overK K D.Λ` or lies over `p` is `K`-conjugate to an
  element of `S` (clause 3).

## The construction

`Work.SSGRoute.ZConstruction.exists_finset_KConj_cover` provides, for any finite set `S'` of
pairwise `ℚ`-non-conjugate finite places, a finite set `T''` of pairwise `K`-non-conjugate finite
places (all of them finite places over `↥K`) meeting every `K`-class of every place of `T''`...
precisely, meeting every `K`-class inside `cs(S')`, the `ℚ`-conjugacy closure of `S'`.  Filtering
`T''` by the predicate "is `ℚ`-conjugate to an element of `S'`" (clause 4) preserves the two
finiteness/disjointness clauses and the covering clause (a `K`-conjugate of a `ℚ`-conjugate of `S'`
is again `ℚ`-conjugate to `S'`), and gives exactly the four clauses required here with
`S' := D.S`.

Clause 3 is then the same covering clause: by `LocalFields`-type transport of ramification,
`IsRamifiedIn ↥K (overK K D.Λ D.hKΛ) B` implies `IsRamifiedIn ℚ D.Λ B`, so `D.hSram` produces an
element of `D.S` `ℚ`-conjugate to `B`; and `B.valuation (p : ℚ̄) < 1` is the same condition over
`ℚ` and over `↥K`.

## The diamond warning

`exists_finset_KConj_cover` is stated for a general base field `k`; calling it at `k := ℚ`,
`Ω := ℚ̄` cannot rely on instance search for its `[IsGalois k ↥K]` argument (there are two
competing `Algebra ℚ ↥K` instances, `IntermediateField.algebra'` and `DivisionRing.toRatAlgebra`,
and the search does not unify them), so the `@`-form with the instance passed as an explicit term is
used below.
-/

namespace Work.SSGRoute

open _root_.SSGRoute
open scoped Pointwise

set_option linter.style.haveILetI false

/-- **Ramification over `↥K` implies ramification over `ℚ`.**  A place of `ℚ̄` that ramifies in
`N/K` (for `K ⊆ N` finite over `ℚ`) also ramifies in `N/ℚ`: an element of the inertia group over
`ℚ` fixing `K` and not fixing `N` is exactly what `IsRamifiedIn ↥K (overK K N hKN)` provides,
through `local_transport_isRamifiedIn`. -/
theorem step4_isRamifiedIn_overK_imp (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    (N : IntermediateField ℚ SSGRoute.QBar) (hKN : K ≤ N) (B : ValuationSubring SSGRoute.QBar)
    (h : SSGRoute.IsRamifiedIn ↥K (overK K N hKN) B) :
    SSGRoute.IsRamifiedIn ℚ N B := by
  obtain ⟨σ, -, hσI, hσN⟩ := (local_transport_isRamifiedIn K (overK K N hKN) B).mp h
  refine ⟨σ, hσI, fun hmem => ?_⟩
  apply hσN
  rw [IntermediateField.mem_fixingSubgroup_iff] at hmem ⊢
  intro x hx
  exact hmem x hx

/-- **The level-`K` cover of the `ℚ`-conjugacy closure of a finite place set.**

For a finite set `S'` of pairwise `ℚ`-non-conjugate finite places of `ℚ̄` there is a finite set `T`
of pairwise `K`-non-conjugate finite places over `↥K` such that

* every element of `T` is `ℚ`-conjugate to an element of `S'`;
* every finite place `B` over `↥K` that is `ℚ`-conjugate to an element of `S'` is `K`-conjugate to
  an element of `T`.

This is `Work.SSGRoute.ZConstruction.exists_finset_KConj_cover` (at `T := ∅`) filtered by the
predicate "is `ℚ`-conjugate to an element of `S'`". -/
theorem step4_isConjPlace_cover (K : IntermediateField ℚ SSGRoute.QBar) [FiniteDimensional ℚ K]
    [IsGalois ℚ K]
    (S' : Finset (ValuationSubring SSGRoute.QBar))
    (hS'fin : ∀ A ∈ S', SSGRoute.IsFinPlace ℚ A)
    (hS'disj : ∀ A ∈ S', ∀ B ∈ S', SSGRoute.IsConjPlace ℚ A B → A = B) :
    ∃ T : Finset (ValuationSubring SSGRoute.QBar),
      (∀ A ∈ T, SSGRoute.IsFinPlace ↥K A) ∧
      (∀ A ∈ T, ∀ B ∈ T, SSGRoute.IsConjPlace ↥K A B → A = B) ∧
      (∀ A ∈ T, ∃ A₀ ∈ S', SSGRoute.IsConjPlace ℚ A₀ A) ∧
      (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ↥K B →
        (∃ A₀ ∈ S', SSGRoute.IsConjPlace ℚ A₀ B) → ∃ A ∈ T, SSGRoute.IsConjPlace ↥K A B) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfd : FiniteDimensional ℚ ↥K := inferInstance
  have hgal : IsGalois ℚ ↥K := inferInstance
  obtain ⟨T'', hT''fin, hT''disj, -, hT''cover⟩ :=
    @ZConstruction.exists_finset_KConj_cover 2 _ ℚ SSGRoute.QBar _ _ _ _ _ K hfd hgal
      (∅ : Finset (ValuationSubring SSGRoute.QBar)) S' (by simp) (by simp) hS'fin hS'disj
  refine ⟨T''.filter (fun A => ∃ A₀ ∈ S', SSGRoute.IsConjPlace ℚ A₀ A), ?_, ?_, ?_, ?_⟩
  · intro A hA
    exact (local_transport_isFinPlace K A).mpr (hT''fin A (Finset.mem_filter.mp hA).1)
  · intro A hA B hB hconj
    exact hT''disj A (Finset.mem_filter.mp hA).1 B (Finset.mem_filter.mp hB).1
      ((isConjPlace_baseChange ℚ SSGRoute.QBar K A B).mpr hconj)
  · intro A hA
    exact (Finset.mem_filter.mp hA).2
  · intro B hBK hEx
    obtain ⟨A, hA, hKA⟩ := hT''cover B ((local_transport_isFinPlace K B).mp hBK) hEx
    refine ⟨A, Finset.mem_filter.mpr ⟨hA, ?_⟩,
      (isConjPlace_baseChange ℚ SSGRoute.QBar K A B).mp hKA⟩
    obtain ⟨A₀, hA₀, hA₀B⟩ := hEx
    exact ⟨A₀, hA₀, isConjPlace_trans hA₀B
      (isConjPlace_symm (ZConstruction.kConj_isConjPlace hKA))⟩

/-- **The place set `S` over `↥K` of Step 4.**

Let `D` be a coker-side datum of Step 4 for `K/ℚ` with place set `D.S` (one place per rational
prime of `Ram(Λ) ∪ {p}`) and let `Λ = D.Λ` be the field of the push-down of `ψ`.  Then there is a
finite set `S` of pairwise `Gal(ℚ̄/K)`-non-conjugate finite places of `ℚ̄` such that

* every finite place of `↥K` that ramifies in `Λ/K` or lies over `p` is `K`-conjugate to an
  element of `S`;
* every element of `S` is `ℚ`-conjugate to an element of `D.S`;
* every finite place of `ℚ` that is `ℚ`-conjugate to an element of `D.S` is `K`-conjugate to an
  element of `S`.

The proof takes `S := T''.filter (· is ℚ-conjugate into D.S)` where `T''` is the level-`K` cover of
the `ℚ`-closure of `D.S`; clause 3 uses `step4_isRamifiedIn_overK_imp` and `D.hSram`. -/
theorem step4_tool_S_exists (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ SSGRoute.QBar)
    [FiniteDimensional ℚ K] [Normal ℚ K] (n i j : ℕ)
    (D : Step4CokerData p K n i j) :
    ∃ S : Finset (ValuationSubring SSGRoute.QBar),
      (∀ A ∈ S, SSGRoute.IsFinPlace ↥K A) ∧
      (∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace ↥K A B → A = B) ∧
      (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ↥K B →
        (SSGRoute.IsRamifiedIn ↥K (overK K D.Λ D.hKΛ) B ∨
          B.valuation (p : SSGRoute.QBar) < 1) →
        ∃ A ∈ S, SSGRoute.IsConjPlace ↥K A B) ∧
      (∀ A ∈ S, ∃ A₀ ∈ D.S, SSGRoute.IsConjPlace ℚ A₀ A) ∧
      (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
        (∃ A₀ ∈ D.S, SSGRoute.IsConjPlace ℚ A₀ B) →
        ∃ A ∈ S, SSGRoute.IsConjPlace ↥K A B) := by
  haveI hGalQ : IsGalois ℚ K := isGalois_of_normal K
  obtain ⟨T, hTfin, hTdisj, hTconj, hTcover⟩ :=
    step4_isConjPlace_cover K D.S D.hSfin D.hSdisj
  refine ⟨T, hTfin, hTdisj, ?_, hTconj, ?_⟩
  · -- clause 3: ramification in `overK K D.Λ` or `p`-adic places
    intro B hBK hrel
    have hBℚ : SSGRoute.IsFinPlace ℚ B := (local_transport_isFinPlace K B).mp hBK
    have hrelℚ : SSGRoute.IsRamifiedIn ℚ D.Λ B ∨ B.valuation (p : SSGRoute.QBar) < 1 := by
      rcases hrel with h | h
      · exact Or.inl (step4_isRamifiedIn_overK_imp K D.Λ D.hKΛ B h)
      · exact Or.inr h
    obtain ⟨A₀, hA₀S, hconj⟩ := D.hSram B hBℚ hrelℚ
    exact hTcover B hBK ⟨A₀, hA₀S, hconj⟩
  · -- clause 5: the `ℚ`-conjugates of `D.S`
    intro B hBℚ hEx
    exact hTcover B ((local_transport_isFinPlace K B).mpr hBℚ) hEx

end Work.SSGRoute
