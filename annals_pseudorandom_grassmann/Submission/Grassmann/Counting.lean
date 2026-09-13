import Mathlib
import Submission.Grassmann.Structure
import Submission.Grassmann.Cardinality

/-!
# Enumeration of the Grassmannian over 𝔽₂ (Layer 1)

The denominators of the density ratios in Khot--Minzer--Safra's Theorem 1.12 are
`#(SubGr k ℓ A B)`, the number of `ℓ`-dimensional subspaces `L` of `𝔽₂ᵏ` lying in the
interval `[A,B]`.  This file develops the counting theory of these intervals and of
the Grassmannian itself:

* the interval ↔ quotient correspondence (submodules of `[A,B]` biject with submodules
  of `V ⧸ A` lying in `B/A`), together with its dimension transport
  `finrank W = ℓ  ↔  finrank (W/A) = ℓ - finrank A`;
* exact cardinality identities expressing `#(SubGr k ℓ A B)` as a count of
  `(ℓ - dim A)`-dimensional subspaces of the quotient space;
* positivity of the denominators (used so the real ratio
  `#(S ∩ SubGr)/#(SubGr) ≥ ε` is well behaved).

Everything is stated over a general field `K` where possible (the generic lemmas are
also published to the shared Commons), and instantiated over `𝔽₂ = ZMod 2`.
-/

open Module Submodule Finset Filter
open scoped BigOperators

set_option autoImplicit false

local notation "𝔽₂" => ZMod 2

namespace Submission.Grassmann

noncomputable section

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The image of `B` under the quotient map by `A` (with `A ≤ B`) has dimension
`finrank B - finrank A`: the quotient `B/A`. -/
lemma finrank_map_mkQ_of_le [Module.Finite K V] (A B : Submodule K V) (h : A ≤ B) :
    Module.finrank K (Submodule.map A.mkQ B) = Module.finrank K B - Module.finrank K A := by
  classical
  let g : B →ₗ[K] V ⧸ A := A.mkQ.comp B.subtype
  have hker : LinearMap.ker g = A.comap B.subtype := by
    dsimp [g]
    rw [LinearMap.ker_comp, Submodule.ker_mkQ]
  have hker_finrank : Module.finrank K (LinearMap.ker g) = Module.finrank K A := by
    rw [hker]
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (p := A) (q := B) h)
  have hrange : LinearMap.range g = Submodule.map A.mkQ B := by
    dsimp [g]
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange, hker_finrank] at hrn
  omega

/-- The interval of submodules `[A, B]` of `V` bijects with the submodules of `V ⧸ A`
lying in the image of `B` (i.e. `B/A`). -/
noncomputable def interval_quotient_equiv (A B : Submodule K V) (hAB : A ≤ B) :
    {W : Submodule K V // A ≤ W ∧ W ≤ B} ≃
      {T : Submodule K (V ⧸ A) // T ≤ Submodule.map A.mkQ B} where
  toFun W :=
    ⟨Submodule.map A.mkQ W.1, Submodule.map_mono W.2.2⟩
  invFun T :=
    ⟨Submodule.comap A.mkQ T.1,
      le_comap_mkQ A T.1,
      by
        calc
          Submodule.comap A.mkQ T.1 ≤ Submodule.comap A.mkQ (Submodule.map A.mkQ B) := Submodule.comap_mono T.2
          _ = A ⊔ B := by rw [Submodule.comap_map_mkQ]
          _ = B := by exact sup_eq_right.mpr hAB⟩
  left_inv W := by
    apply Subtype.ext
    change Submodule.comap A.mkQ (Submodule.map A.mkQ W.1) = W.1
    rw [Submodule.comap_map_mkQ]
    exact sup_eq_right.mpr W.2.1
  right_inv T := by
    apply Subtype.ext
    change Submodule.map A.mkQ (Submodule.comap A.mkQ T.1) = T.1
    exact Submodule.map_comap_eq_of_surjective (f := A.mkQ)
      (LinearMap.range_eq_top.mp (Submodule.range_mkQ A)) T.1

/-- Dimension transport across the correspondence: `finrank W = ℓ` becomes
`finrank (W/A) = ℓ - finrank A`. -/
lemma finrank_interval_iff_quotient [Module.Finite K V] (A B : Submodule K V) (hAB : A ≤ B)
    {ℓ : ℕ} (hA : Module.finrank K A ≤ ℓ) (W : {W : Submodule K V // A ≤ W ∧ W ≤ B}) :
    Module.finrank K W.1 = ℓ ↔
      Module.finrank K ((interval_quotient_equiv A B hAB) W).1 = ℓ - Module.finrank K A := by
  have hq : Module.finrank K (Submodule.map A.mkQ W.1) =
      Module.finrank K W.1 - Module.finrank K A := by
    exact finrank_map_mkQ_of_le A W.1 W.2.1
  have hdecomp : Module.finrank K W.1 =
      Module.finrank K (Submodule.map A.mkQ W.1) + Module.finrank K A := by
    have hle : Module.finrank K A ≤ Module.finrank K W.1 := by
      exact Submodule.finrank_mono W.2.1
    omega
  constructor
  · intro h
    rw [hdecomp] at h
    exact (Nat.sub_eq_of_eq_add h.symm).symm
  · intro h
    change Module.finrank K (Submodule.map A.mkQ W.1) = ℓ - Module.finrank K A at h
    rw [hdecomp, h]
    exact Nat.sub_add_cancel hA

/-- Counting the `ℓ`-dimensional members of the interval `[A,B]` of submodules of `V`
equals counting the `(ℓ - finrank A)`-dimensional submodules of the quotient `V ⧸ A`
that lie in `B/A`. -/
theorem card_interval_finrank_eq_quotient [Module.Finite K V] (A B : Submodule K V) (hAB : A ≤ B)
    {ℓ : ℕ} (hA : Module.finrank K A ≤ ℓ) :
    Nat.card {x : Submodule K V // (A ≤ x ∧ x ≤ B) ∧ Module.finrank K x = ℓ} =
      Nat.card {x : Submodule K (V ⧸ A) // x ≤ Submodule.map A.mkQ B ∧
        Module.finrank K x = ℓ - Module.finrank K A} := by
  classical
  let e := interval_quotient_equiv A B hAB
  let pAB : Submodule K V → Prop := fun p => A ≤ p ∧ p ≤ B
  let qℓ : Submodule K V → Prop := fun p => Module.finrank K p = ℓ
  let pB' : Submodule K (V ⧸ A) → Prop := fun p => p ≤ Submodule.map A.mkQ B
  let qm : Submodule K (V ⧸ A) → Prop := fun p =>
    Module.finrank K p = ℓ - Module.finrank K A
  -- regroup the domain side:  {x // (AB x) ∧ finrank x = ℓ} ≃ {W : {x // AB x} // finrank W.1 = ℓ}
  let R1 : {x : Submodule K V // (A ≤ x ∧ x ≤ B) ∧ Module.finrank K x = ℓ} ≃
      {W : {p : Submodule K V // A ≤ p ∧ p ≤ B} // Module.finrank K W.1 = ℓ} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter (fun p : Submodule K V => A ≤ p ∧ p ≤ B)
      (fun p : Submodule K V => Module.finrank K p = ℓ)).symm
  -- regroup the codomain side
  let R2 : {x : Submodule K (V ⧸ A) // x ≤ Submodule.map A.mkQ B ∧
        Module.finrank K x = ℓ - Module.finrank K A} ≃
      {T : {p : Submodule K (V ⧸ A) // p ≤ Submodule.map A.mkQ B} //
        Module.finrank K T.1 = ℓ - Module.finrank K A} :=
    (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun p : Submodule K (V ⧸ A) => p ≤ Submodule.map A.mkQ B)
      (fun p : Submodule K (V ⧸ A) => Module.finrank K p = ℓ - Module.finrank K A)).symm
  have hp : ∀ W : {p : Submodule K V // A ≤ p ∧ p ≤ B},
      Module.finrank K W.1 = ℓ ↔
        Module.finrank K (e W).1 = ℓ - Module.finrank K A := by
    intro W
    simpa [e] using finrank_interval_iff_quotient A B hAB hA W
  calc
    Nat.card {x : Submodule K V // (A ≤ x ∧ x ≤ B) ∧ Module.finrank K x = ℓ}
        = Nat.card {W : {p : Submodule K V // A ≤ p ∧ p ≤ B} // Module.finrank K W.1 = ℓ} := by
          exact Nat.card_congr R1
    _ = Nat.card {T : {p : Submodule K (V ⧸ A) // p ≤ Submodule.map A.mkQ B} //
          Module.finrank K T.1 = ℓ - Module.finrank K A} := by
          exact Nat.card_congr (Equiv.subtypeEquiv e hp)
    _ = Nat.card {x : Submodule K (V ⧸ A) // x ≤ Submodule.map A.mkQ B ∧
          Module.finrank K x = ℓ - Module.finrank K A} := by
          exact (Nat.card_congr R2).symm

end

/-! ## The Grassmannian over 𝔽₂ -/

open PseudorandomGrassmann

namespace F2

variable {k ℓ : ℕ}

/-- `#(SubGr k ℓ A B)` equals the number of `ℓ`-dimensional subspaces `x` of `𝔽₂ᵏ`
with `A ≤ x ≤ B`, expressed as a `Nat.card` of a single subtype of submodules. -/
lemma card_SubGr_eq_flat_natCard (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    #(SubGr k ℓ A B) = Nat.card {x : Submodule 𝔽₂ (Fin k → 𝔽₂) //
      (A ≤ x ∧ x ≤ B) ∧ Module.finrank 𝔽₂ x = ℓ} := by
  classical
  -- (1) Finset ↔ subtype of GrVertex
  have h1 : #(SubGr k ℓ A B) =
      Nat.card {L : GrVertex k ℓ // A ≤ (L : Submodule 𝔽₂ (Fin k → 𝔽₂)) ∧ (L : Submodule 𝔽₂ (Fin k → 𝔽₂)) ≤ B} := by
    have h : (SubGr k ℓ A B).card = Fintype.card {L : GrVertex k ℓ // A ≤ (L : Submodule 𝔽₂ (Fin k → 𝔽₂)) ∧ (L : Submodule 𝔽₂ (Fin k → 𝔽₂)) ≤ B} := by
      unfold SubGr
      rw [Fintype.card_subtype]
    rw [Nat.card_eq_fintype_card]
    exact h
  rw [h1]
  -- (2) subtype-of-GrVertex ≃ flat {x : Submodule // (AB x) ∧ finrank x = ℓ}
  let e : {L : GrVertex k ℓ // A ≤ (L : Submodule 𝔽₂ (Fin k → 𝔽₂)) ∧ (L : Submodule 𝔽₂ (Fin k → 𝔽₂)) ≤ B} ≃
      {x : Submodule 𝔽₂ (Fin k → 𝔽₂) // (A ≤ x ∧ x ≤ B) ∧ Module.finrank 𝔽₂ x = ℓ} := by
    refine (Equiv.subtypeSubtypeEquivSubtypeInter
      (fun U : Submodule 𝔽₂ (Fin k → 𝔽₂) => Module.finrank 𝔽₂ U = ℓ)
      (fun U : Submodule 𝔽₂ (Fin k → 𝔽₂) => A ≤ U ∧ U ≤ B)).trans ?_
    refine Equiv.subtypeEquiv (Equiv.refl (Submodule 𝔽₂ (Fin k → 𝔽₂))) ?_
    intro x
    constructor
    · intro hx; exact ⟨hx.2, hx.1⟩
    · intro hx; exact ⟨hx.2, hx.1⟩
  exact Nat.card_congr e

/-- The interval count `#(SubGr k ℓ A B)` (for `A ≤ B` and `ℓ ≥ finrank A`) equals the
number of `(ℓ - finrank A)`-dimensional subspaces of the quotient `𝔽₂ᵏ ⧸ A` lying in
`B/A`.  This is the interval-count ↔ quotient correspondence specialised to the
Grassmann setting. -/
lemma card_SubGr_eq_quotient (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) (hAB : A ≤ B)
    {ℓ : ℕ} (hℓa : Module.finrank 𝔽₂ A ≤ ℓ) :
    #(SubGr k ℓ A B) = Nat.card {x : Submodule 𝔽₂ ((Fin k → 𝔽₂) ⧸ A) //
      x ≤ Submodule.map A.mkQ B ∧ Module.finrank 𝔽₂ x = ℓ - Module.finrank 𝔽₂ A} := by
  rw [card_SubGr_eq_flat_natCard]
  exact card_interval_finrank_eq_quotient (K := 𝔽₂) (V := Fin k → 𝔽₂) A B hAB hℓa

/-- `#(SubGr k ℓ A B) > 0` exactly when the interval dimension constraints hold. -/
lemma card_SubGr_pos_iff (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) :
    0 < #(SubGr k ℓ A B) ↔ A ≤ B ∧ Module.finrank 𝔽₂ A ≤ ℓ ∧ ℓ ≤ Module.finrank 𝔽₂ B := by
  rw [Finset.card_pos]
  exact SubGr_nonempty_iff (k := k) (ℓ := ℓ) A B

/-- `#(SubGr k ℓ A B) > 0` whenever `A ≤ B` and `finrank A ≤ ℓ ≤ finrank B`. -/
lemma card_SubGr_pos_of_le (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) (hAB : A ≤ B)
    (hA : Module.finrank 𝔽₂ A ≤ ℓ) (hB : ℓ ≤ Module.finrank 𝔽₂ B) :
    0 < #(SubGr k ℓ A B) := by
  rw [card_SubGr_pos_iff]
  exact ⟨hAB, hA, hB⟩

/-- `SubGr ⊥ ⊤` is the whole vertex set. -/
lemma card_SubGr_bot_top (k ℓ : ℕ) : #(SubGr k ℓ ⊥ ⊤) = Fintype.card (GrVertex k ℓ) := by
  simp [SubGr_bot_top]

/-- The total vertex count equals the number of `ℓ`-dimensional subspaces of `𝔽₂ᵏ`
(definitionally, `GrVertex k ℓ` is that subtype). -/
lemma card_GrVertex_eq_natCard :
    Fintype.card (GrVertex k ℓ) =
      Nat.card {x : Submodule 𝔽₂ (Fin k → 𝔽₂) // Module.finrank 𝔽₂ x = ℓ} := by
  rw [← Nat.card_eq_fintype_card]

/-- `#(SubGr k ℓ ⊥ ⊤)` is the number of `ℓ`-dimensional subspaces of `𝔽₂ᵏ`. -/
lemma card_SubGr_bot_top_eq_natCard (k ℓ : ℕ) : #(SubGr k ℓ ⊥ ⊤) =
    Nat.card {x : Submodule 𝔽₂ (Fin k → 𝔽₂) // Module.finrank 𝔽₂ x = ℓ} := by
  rw [card_SubGr_bot_top, card_GrVertex_eq_natCard]

end F2

end Submission.Grassmann
