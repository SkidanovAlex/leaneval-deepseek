import Mathlib
import Submission.Work.SSGRoute.Step4CokerData
import Submission.Work.SSGRoute.Interfaces
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # The interface of the arithmetic of Step 4 of Theorem 15 (the datum `y`)

This module holds the two *definitions* of the node `Work.SSGRoute.step4_y_exists` --- the local
prescriptions `Step4YPrescribed` (the form of the Fourth Step of Schmidt--Wingberg that the node
consumes) and the "arithmetic output" `Step4YLocalData` (the local data and the global class `ε`
that the sub-base obstruction theorem produces) --- together with the three `↥K`-side bookkeeping
lemmas used by the clause verification.

Keeping them in a module *below* the node lets both the node file and the separate lemma
`Work.SSGRoute.step4_yPrescribed_of_localData` (the clause verification) import them without a
cycle.  The import list is deliberately minimal: the workspace's two chains now use two *different*
`KConj`-style predicates (`Work.SSGRoute.KConjLocal` in `step4_y_clauses.lean` for this node's
level-`↥K` conjugacy, and `Work.SSGRoute.KConj` in `ZConstruction/AuxInterface.lean` for the
Z-construction lane), so a module that imports both chains is safe only if the names differ ---
which is why `KConj` here was renamed to `KConjLocal`. -/

namespace Work.SSGRoute

open _root_.SSGRoute
open Work.CohomologicalShrinking
open scoped Pointwise

variable {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ SSGRoute.QBar}
  [FiniteDimensional ℚ K] [Normal ℚ K] {n i j : ℕ}

/-! ## The interface of the arithmetic of the Fourth Step, and its clause verification

The target of this node is reached through the following three layers.

1. **The arithmetic** (the only place where `SSGRoute.coker_obstruction_splitOverSubbase` and the
   second shrinking enter) must produce, for a coker-side datum `D` and a `Tnew`/`ηt` block, an
   element of `Work.SSGRoute.Step4YLocalData D Tnew ηt` below: a finite set `S` of places
   (one per `K`-prime over the relevant rational primes, covering everything ramified in `D.Λ`
   over `↥K` and everything over `p`, and sitting inside the `ℚ`-conjugacy classes of `D.S`) and a
   global class `ε` on `Gal(ℚ̄/↥K)` which is additive (`hadd`) and locally constant (`hloc`), equals
   the local target `ηt A` on the decomposition group of every `A ∈ Tnew` (`hpres`), vanishes on
   the decomposition group of every other element of `S` (`hzero`), and is unramified at every
   place outside `cs(S)` that is not completely split over `ℚ` in `D.Λ` (`hesc` — the escape
   clause of the sub-base version of the obstruction theorem).

2. **The clause verification** (this is where `Step4YLocalData` is turned into
   `Step4YPrescribed`, i.e. into `y` and its nine clauses): the class `ε` is transported to `G_ℚ`
   by `patchFun K ε` (extended by `0` off `G_K`); the prescriptions at the elements of `S` are
   propagated to *all* places with the same `K`-prime by conjugation invariance
   (`step4_conj_eq_of_additive_K` below, the counterpart of `step4_conj_eq_of_additive` on the
   `↥K`-side); the passage between `decomp ↥K A` and `decomp ℚ A` is
   `Work.SSGRoute.local_transport_decomp`/`local_transport_isInertia`.
   *(Being written; the two `↥K`-side helpers `smul_eq_of_coe_eq`,
   `isConjPlace_of_isConjPlace_over_K` and `step4_conj_eq_of_additive_K` are proved below.)*

3. **The final assembly** `step4_y_exists_of_prescribed`: `Step4YPrescribed → Step4YData`, already
   on disk (`step4_y_clauses.lean`), together with `step4_coker_data_exists` for the data `D`.

Two details of the interface deserve to be recorded.

* `Tnew ∩ D.T0 = ∅` is *needed* for the clause verification (clause 7 `y = 0` on the decomposition
  groups of `D.T0` and clause 8 `y = ηt A` on those of `Tnew` are otherwise contradictory), and it
  is *not* derivable from the hypotheses of `step4_y_prescribed` as stated in session 3.  It is
  true for the natural choice `Tnew := D.S.filter D.IsNewRamp` (`D.hT0unram` says that `D.psi` is
  trivial on the inertia of a `T0`-place, whereas `IsNewRamp` demands a nontrivial `D.psi` there),
  and it is supplied by the separate lemma
  `Work.SSGRoute.step4_y_tnew_split_T0` (`step4_y_tnew_split.lean` plus that one conjunct).
* The class `ε` of the tool `SSGRoute.coker_obstruction_splitOverSubbase` is *at level `Λ`*: with
  the base `k := ↥K`, the middle field `K := ⊥`, `N₂ := N := Λ` and `f := id`, its naturality
  hypothesis reads `(map q F 1) x = 0` with `q = id`, `F = id`, i.e. `x = 0`; equivalently the
  local data must be orthogonal to the dual Selmer group.  This is the second shrinking
  (`Work.CohomologicalShrinking.exists_shrinking_H1`, `Work.SSGRoute.step4_h1_normal_shrink`),
  which is the one genuinely missing arithmetic ingredient of this node. -/

/-- Two `ℚ`-algebra automorphisms of `ℚ̄` with the same underlying function act in the same way on
places. -/
theorem smul_eq_of_coe_eq {φ ψ : SSGRoute.QBar ≃ₐ[ℚ] SSGRoute.QBar} (h : ⇑φ = ⇑ψ)
    (A : ValuationSubring SSGRoute.QBar) : φ • A = ψ • A := by
  apply ValuationSubring.ext
  intro x
  rw [ValuationSubring.mem_smul_pointwise_iff_exists,
    ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, h]⟩
  · rintro ⟨s, hs, hx⟩
    exact ⟨s, hs, by rw [← hx, AlgEquiv.smul_def, AlgEquiv.smul_def, h]⟩

/-- Conjugacy of places over `↥K` implies conjugacy over `ℚ`. -/
theorem isConjPlace_of_isConjPlace_over_K {A B : ValuationSubring SSGRoute.QBar}
    (h : SSGRoute.IsConjPlace ↥K A B) : SSGRoute.IsConjPlace ℚ A B := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨AlgEquiv.restrictScalars ℚ σ, ?_⟩
  rw [← hσ]
  exact smul_eq_of_coe_eq (by funext x; rfl) A

/-- **Conjugation invariance on the `↥K`-side**: an additive function on `Gal(ℚ̄/↥K)` with values in
an abelian group is invariant under conjugation. -/
theorem step4_conj_eq_of_additive_K (ε : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) →
      E p (K ≃ₐ[ℚ] K) n i j)
    (hε : ∀ x y : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, ε (x * y) = ε x + ε y)
    (a b : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) : ε (a * b * a⁻¹) = ε b := by
  have h1 : ε 1 = 0 := by
    have h := hε 1 1
    rw [mul_one] at h
    exact (add_left_cancel (show ε 1 + 0 = ε 1 + ε 1 from by rw [add_zero, ← h])).symm
  have hinv : ∀ c : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, ε c⁻¹ = - ε c := by
    intro c
    have h := hε c⁻¹ c
    rw [inv_mul_cancel, h1] at h
    exact eq_neg_of_add_eq_zero_left h.symm
  rw [show a * b * a⁻¹ = a * (b * a⁻¹) from mul_assoc a b a⁻¹, hε a (b * a⁻¹), hε b a⁻¹,
    hinv a]
  abel

/-- **The arithmetic output of Schmidt--Wingberg's Fourth Step, at base `↥K`** (the interface of
`Work.SSGRoute.step4_yPrescribed_of_localData`): a set `S` of places and a global class `ε` on
`Gal(ℚ̄/↥K)` with the prescribed local behaviour and the sub-base escape clause.

`S` is "one place per `K`-prime over the relevant rational primes": it is pairwise
`↥K`-non-conjugate (`hSdisj`), covers every place that is `↥K`-ramified in `D.Λ` or lies over `p`
(`hSfin`/`hSram`-style coverage, through `hSconj` and `hScover` it is contained in and covers the
`ℚ`-conjugacy classes of `D.S`), and every element of `S` is `ℚ`-conjugate to an element of `D.S`
(`hSconj`) while every place `ℚ`-conjugate to `D.S` is `↥K`-conjugate to an element of `S`
(`hScover`).

`ε` is additive (`hadd`) and locally constant (`hloc`) on the whole of `Gal(ℚ̄/↥K)`; it equals the
local target `ηt A` on the decomposition group of `A`, for every `A ∈ Tnew` (`hpres`); it vanishes
on the decomposition group of every element of `S` that is not `↥K`-conjugate to an element of
`Tnew` (`hzero`); and it vanishes on the inertia of every place outside `cs(S)` that is not
completely split over `ℚ` in `D.Λ` (`hesc`). -/
structure Step4YLocalData (D : Step4CokerData p K n i j)
    (Tnew : Finset (ValuationSubring SSGRoute.QBar))
    (ηt : (A : ValuationSubring SSGRoute.QBar) → A ∈ Tnew →
      SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j) : Type where
  S : Finset (ValuationSubring SSGRoute.QBar)
  ε : (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar) → E p (K ≃ₐ[ℚ] K) n i j
  hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace ↥K A
  hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace ↥K A B → A = B
  hSconj : ∀ A ∈ S, ∃ A₀ ∈ D.S, SSGRoute.IsConjPlace ℚ A₀ A
  hScover : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
    (∃ A₀ ∈ D.S, SSGRoute.IsConjPlace ℚ A₀ B) → ∃ A ∈ S, SSGRoute.IsConjPlace ↥K A B
  hadd : ∀ x y : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, ε (x * y) = ε x + ε y
  hloc : SSGRoute.IsLocConstOn (⊤ : Subgroup (SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar)) ε
  hpres : ∀ (A : ValuationSubring SSGRoute.QBar) (hA : A ∈ Tnew),
    ∀ δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, δ ∈ SSGRoute.decomp ↥K A →
      ε δ = ηt A hA (((IntermediateField.fixingSubgroupEquiv K).symm δ : SSGRoute.GalQ))
  hzero : ∀ A ∈ S, (∀ A₀ ∈ Tnew, ¬ SSGRoute.IsConjPlace ↥K A A₀) →
    ∀ δ ∈ SSGRoute.decomp ↥K A, ε δ = 0
  hesc : ∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ↥K B →
    (∀ A ∈ S, ¬ SSGRoute.IsConjPlace ↥K A B) → ¬ SSGRoute.IsSplitIn ℚ D.Λ B →
    ∀ δ : SSGRoute.QBar ≃ₐ[↥K] SSGRoute.QBar, SSGRoute.IsInertia ↥K B δ → ε δ = 0

/-- **The arithmetic input of the node** (SW's Fourth Step, Schmidt--Wingberg arXiv:math/9809211
§5, pp. 29--31).  For a coker-side datum `D` and a `Tnew`/`ηt` block (the chosen prolongations of
the places of new ramification with their local targets), there is a function
`y : G_ℚ → E(n,τ)` — the paper's class of the Fourth Step — with:

* `y` is supported on `G_K` and is additive and locally constant there (`y` is the paper's class in
  `H¹(k_S|K, E(n,τ))`, extended by `0` off `G_K`);
* `y` vanishes on the inertia of the places of `cs(S)` and of the places outside `cs(S)` that are
  not completely split in `Λ` (clauses 3 and 4 of `Step4YData`, the *escape* of the obstruction);
* `y` vanishes on the decomposition groups at the places of `cs(S)` at which `K` does not split
  completely, or which lie over `p`, or at which the level-`τ` solution `D.phi` ramifies (clauses 5
  and 7);
* `y` vanishes on `D_A ∩ G_K` for `A ∈ D.T0`, on the conjugates `(sec s)⁻¹ • A` (`s ≠ 1`) of the
  `T⁰`-places, and on the conjugates of the `Tnew`-places (what makes the formal corestriction
  collapse, clause 6 and the agreement clause);
* `y` equals `ηt A` on `D_A ∩ G_K` for `A ∈ Tnew` (the agreement clause).

This is exactly the output of SW's Lemma 10 + Lemma 12 + the shrinking, instantiated in the
"hybrid" form needed here (base field `K`, escape measured over `k = ℚ`): see
`SSGRoute/coker_obstruction_splitOverSubbase` and the discussion in the module docstring.  It is
stated as a single labelled obligation so that the rest of this module is a *proof*. -/
def Step4YPrescribed (D : Step4CokerData p K n i j)
    (Tnew : Finset (ValuationSubring SSGRoute.QBar))
    (ηt : (A : ValuationSubring SSGRoute.QBar) → A ∈ Tnew →
      SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j) : Prop :=
  ∃ y : SSGRoute.GalQ → E p (K ≃ₐ[ℚ] K) n i j,
    (∀ σ : SSGRoute.GalQ, σ ∉ K.fixingSubgroup → y σ = 0) ∧
    (∀ σ ∈ K.fixingSubgroup, ∀ τ ∈ K.fixingSubgroup, y (σ * τ) = y σ + y τ) ∧
    SSGRoute.IsLocConstOn K.fixingSubgroup y ∧
    (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∀ A ∈ D.S, ¬ SSGRoute.IsConjPlace ℚ A B) → ¬ SSGRoute.IsSplitIn ℚ D.Λ B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia ℚ B σ → y σ = 0) ∧
    (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∃ A ∈ D.S, SSGRoute.IsConjPlace ℚ A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia ℚ B σ → y σ = 0) ∧
    (∀ B : ValuationSubring SSGRoute.QBar, SSGRoute.IsFinPlace ℚ B →
      (∃ A ∈ D.S, SSGRoute.IsConjPlace ℚ A B) →
      (¬ SSGRoute.IsSplitIn ℚ K B ∨ B.valuation (p : SSGRoute.QBar) < 1 ∨
        (∃ σ, SSGRoute.IsInertia ℚ B σ ∧ σ ∈ K.fixingSubgroup ∧ D.phi σ ≠ 1)) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp ℚ B → y σ = 0) ∧
    (∀ A ∈ D.T0, ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp ℚ A → y σ = 0) ∧
    (∀ (A : ValuationSubring SSGRoute.QBar) (hA : A ∈ Tnew),
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp ℚ A → y σ = ηt A hA σ) ∧
    (∀ A ∈ Tnew, ∀ s : K ≃ₐ[ℚ] K, s ≠ 1 →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp ℚ ((D.sec s)⁻¹ • A) → y σ = 0) ∧
    (∀ A ∈ D.T0, ∀ s : K ≃ₐ[ℚ] K, s ≠ 1 →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp ℚ ((D.sec s)⁻¹ • A) → y σ = 0)

end Work.SSGRoute
