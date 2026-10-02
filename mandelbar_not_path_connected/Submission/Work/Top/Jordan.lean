/-
# The Jordan curve theorem, as an explicit hypothesis, and its consequences

The endgame `Work.Top.not_isPathConnected_of_twoSidedPinch` uses planar separation: the pinch
curve `J_r` built from two parameter-ray tails, an equipotential arc and a straight segment
must separate the point `p ∈ closure (paramRay θ)` from `1/4`.

This file isolates the *only* input from plane topology:

* `IsJordanCurve C` — `C` is the image of an injective continuous map of the circle;
* `JordanForm` — the Jordan curve theorem, in the exact form needed: the complement of a
  Jordan curve has two components, one bounded and one unbounded, each having the curve as
  its frontier.

Everything else in this file is derived from `JordanForm` (no winding numbers, no Janiszewski,
no Schoenflies): `Sides` packages the two sides, `Sides.subset_of_preconnected` puts every
connected subset of the complement into one side, `Sides.not_joinedIn` says that points of
different sides are not joined in the complement, `Sides.path_meets` says that a path joining
the two sides meets the curve, and `Sides.sides_of_halves` is the local two-sidedness at a
crossing (a neighbourhood `B` of a point of the curve which is cut by the curve into two
connected halves `P`, `Q` puts `P`, `Q` in different sides).
-/
import ChallengeDeps

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.Top

/-! ## Jordan curves -/

/-- A **Jordan curve** in the plane: the image of a continuous injective map of the circle
(`AddCircle (1 : ℝ)` is a circle, homeomorphic to the unit circle of `ℂ`). -/
def IsJordanCurve (C : Set ℂ) : Prop :=
  ∃ γ : C(AddCircle (1 : ℝ), ℂ), Function.Injective γ ∧ Set.range γ = C

/-- **The Jordan curve theorem**, in the form needed by the endgame: the complement of a
Jordan curve has exactly two components, one bounded and one unbounded, and each of them has
the curve as its frontier.

This is the single plane-topological input of the whole area; it is *proved elsewhere* (planar
Jordan--Schoenflies) and copied in, so here it is a hypothesis. -/
def JordanForm : Prop :=
  ∀ C : Set ℂ, IsJordanCurve C → ∃ I O : Set ℂ,
    IsOpen I ∧ IsOpen O ∧ I ∪ O = Cᶜ ∧ Disjoint I O ∧
    IsPreconnected I ∧ IsPreconnected O ∧ Bornology.IsBounded I ∧
    (∀ n : ℕ, ∃ z ∈ O, (n : ℝ) ≤ ‖z‖) ∧ frontier I = C ∧ frontier O = C

/-! ## The two sides of a Jordan curve -/

/-- The two sides of a Jordan curve `C`: the bounded component `I` and the unbounded component
`O` of `Cᶜ`, both with `C` as frontier. -/
structure Sides (C : Set ℂ) : Type where
  /-- the bounded side. -/
  I : Set ℂ
  /-- the unbounded side. -/
  O : Set ℂ
  isOpen_I : IsOpen I
  isOpen_O : IsOpen O
  union_eq : I ∪ O = Cᶜ
  disjoint : Disjoint I O
  preconnected_I : IsPreconnected I
  preconnected_O : IsPreconnected O
  bounded_I : Bornology.IsBounded I
  unbounded_O : ∀ n : ℕ, ∃ z ∈ O, (n : ℝ) ≤ ‖z‖
  frontier_I : frontier I = C
  frontier_O : frontier O = C

/-- The two sides of a Jordan curve, extracted from the Jordan curve theorem. -/
def JordanForm.sides (hJ : JordanForm) (C : Set ℂ) (hC : IsJordanCurve C) : Sides C :=
  let h := hJ C hC
  { I := Classical.choose h
    O := Classical.choose (Classical.choose_spec h)
    isOpen_I := (Classical.choose_spec (Classical.choose_spec h)).1
    isOpen_O := (Classical.choose_spec (Classical.choose_spec h)).2.1
    union_eq := (Classical.choose_spec (Classical.choose_spec h)).2.2.1
    disjoint := (Classical.choose_spec (Classical.choose_spec h)).2.2.2.1
    preconnected_I := (Classical.choose_spec (Classical.choose_spec h)).2.2.2.2.1
    preconnected_O := (Classical.choose_spec (Classical.choose_spec h)).2.2.2.2.2.1
    bounded_I := (Classical.choose_spec (Classical.choose_spec h)).2.2.2.2.2.2.1
    unbounded_O := (Classical.choose_spec (Classical.choose_spec h)).2.2.2.2.2.2.2.1
    frontier_I := (Classical.choose_spec (Classical.choose_spec h)).2.2.2.2.2.2.2.2.1
    frontier_O := (Classical.choose_spec (Classical.choose_spec h)).2.2.2.2.2.2.2.2.2 }

namespace Sides

variable {C : Set ℂ} (S : Sides C)

theorem subset_compl_I : S.I ⊆ Cᶜ := fun _ hx => by
  rw [← S.union_eq]
  exact Or.inl hx

theorem subset_compl_O : S.O ⊆ Cᶜ := fun _ hx => by
  rw [← S.union_eq]
  exact Or.inr hx

theorem notMem_C_of_mem_I {x : ℂ} (hx : x ∈ S.I) : x ∉ C := by
  intro h
  have h' : x ∈ Cᶜ := S.subset_compl_I hx
  exact h' h

theorem notMem_C_of_mem_O {x : ℂ} (hx : x ∈ S.O) : x ∉ C := by
  intro h
  have h' : x ∈ Cᶜ := S.subset_compl_O hx
  exact h' h

/-- A point of the bounded side is not in the unbounded side. -/
theorem notMem_O_of_mem_I {x : ℂ} (hx : x ∈ S.I) : x ∉ S.O :=
  fun h => Set.disjoint_left.mp S.disjoint hx h

/-- A point of the unbounded side is not in the bounded side. -/
theorem notMem_I_of_mem_O {x : ℂ} (hx : x ∈ S.O) : x ∉ S.I :=
  fun h => Set.disjoint_left.mp S.disjoint h hx

/-- **Every connected subset of the complement of a Jordan curve lies in one of the two
sides.** -/
theorem subset_of_preconnected {T : Set ℂ} (hconn : IsPreconnected T) (hsub : T ⊆ Cᶜ) :
    T ⊆ S.I ∨ T ⊆ S.O := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · exact Or.inl (Set.empty_subset _)
  · have h1 : T ⊆ S.I ∪ S.O := by rw [S.union_eq]; exact hsub
    have h2 : T ∩ (S.I ∩ S.O) = ∅ := by
      have h3 : S.I ∩ S.O = ∅ := Set.disjoint_iff_inter_eq_empty.mp S.disjoint
      rw [h3, Set.inter_empty]
    exact isPreconnected_iff_subset_of_disjoint.mp hconn S.I S.O S.isOpen_I S.isOpen_O h1 h2

/-- **A connected unbounded subset of the complement of a Jordan curve lies in the unbounded
side.** -/
theorem subset_O_of_unbounded {T : Set ℂ} (hconn : IsPreconnected T) (hsub : T ⊆ Cᶜ)
    (hunb : ∀ n : ℕ, ∃ z ∈ T, (n : ℝ) ≤ ‖z‖) : T ⊆ S.O := by
  rcases S.subset_of_preconnected hconn hsub with h | h
  · exfalso
    obtain ⟨D, hD⟩ := isBounded_iff_forall_norm_le.mp S.bounded_I
    obtain ⟨z, hzT, hz⟩ := hunb (Nat.ceil (D + 1))
    have h2 : ‖z‖ ≤ D := hD z (h hzT)
    have h4 : D < (Nat.ceil (D + 1) : ℝ) := by
      have := Nat.le_ceil (D + 1)
      linarith
    linarith
  · exact h

/-- **Points in different sides of a Jordan curve are not joined in the complement.** -/
theorem not_joinedIn {x y : ℂ} (hx : x ∈ S.I) (hy : y ∈ S.O) : ¬ JoinedIn Cᶜ x y := by
  rintro ⟨γ, hγ⟩
  have hconn : IsPreconnected (Set.range γ) := isPreconnected_range γ.continuous
  have hsub : Set.range γ ⊆ Cᶜ := by
    rintro z ⟨t, rfl⟩
    exact hγ t
  rcases S.subset_of_preconnected hconn hsub with h | h
  · exact S.notMem_O_of_mem_I (h ⟨1, γ.target⟩) hy
  · exact S.notMem_I_of_mem_O (h ⟨0, γ.source⟩) hx

/-- **A path joining the two sides of a Jordan curve meets the curve.** -/
theorem path_meets {f : C(unitInterval, ℂ)} (h0 : f 0 ∈ S.I) (h1 : f 1 ∈ S.O) :
    ∃ t, f t ∈ C := by
  by_contra hcon
  have hcon' : ∀ t, f t ∉ C := fun t ht => hcon ⟨t, ht⟩
  have hmem : JoinedIn Cᶜ (f 0) (f 1) :=
    ⟨⟨f, rfl, rfl⟩, fun t => by
      simpa [Set.mem_compl_iff] using hcon' t⟩
  exact S.not_joinedIn h0 h1 hmem

/-- **Local two-sidedness of a Jordan curve.**  Let `B` be an open neighbourhood of a point of
the curve `C`, cut by `C` into the two connected pieces `P` and `Q` (so `B ∖ C ⊆ P ∪ Q`).
If `Q` meets the unbounded side `O`, then `P` lies in the bounded side `I`. -/
theorem sides_of_halves {B P Q : Set ℂ} (hopen : IsOpen B) (hBC : (B ∩ C).Nonempty)
    (hcov : B \ C ⊆ P ∪ Q)
    (hPconn : IsPreconnected P) (hQconn : IsPreconnected Q)
    (hPC : Disjoint P C) (hQC : Disjoint Q C)
    (hQz : ∃ z ∈ Q, z ∈ S.O) : P ⊆ S.I := by
  have hPsub : P ⊆ Cᶜ := fun x hx => by
    simp only [Set.mem_compl_iff]
    exact fun h => Set.disjoint_left.mp hPC hx h
  have hQsub : Q ⊆ Cᶜ := fun x hx => by
    simp only [Set.mem_compl_iff]
    exact fun h => Set.disjoint_left.mp hQC hx h
  rcases S.subset_of_preconnected hPconn hPsub with h | h
  · exact h
  · exfalso
    obtain ⟨z, hzQ, hzO⟩ := hQz
    have hQO : Q ⊆ S.O := by
      rcases S.subset_of_preconnected hQconn hQsub with h' | h'
      · exact absurd (h' hzQ) (S.notMem_I_of_mem_O hzO)
      · exact h'
    -- `B ∖ C ⊆ O`, but `I` meets `B ∖ C`
    obtain ⟨q, hqB, hqC⟩ := hBC
    have hqfront : q ∈ frontier S.I := by rw [S.frontier_I]; exact hqC
    have hqcl : q ∈ closure S.I := frontier_subset_closure hqfront
    have hBnhds : B ∈ 𝓝 q := hopen.mem_nhds hqB
    obtain ⟨w, hwB, hwI⟩ := mem_closure_iff.mp hqcl B hopen hqB
    have hwC : w ∉ C := S.notMem_C_of_mem_I hwI
    have hwBC : w ∈ B \ C := ⟨hwB, hwC⟩
    rcases hcov hwBC with hw | hw
    · exact S.notMem_O_of_mem_I hwI (h hw)
    · exact S.notMem_O_of_mem_I hwI (hQO hw)

end Sides

end Work.Top
