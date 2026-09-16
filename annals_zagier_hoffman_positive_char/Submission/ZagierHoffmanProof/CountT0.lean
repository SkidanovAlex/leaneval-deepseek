/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.LinIndep

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# The counting statement for the Hoffman set `𝒯0 w` (all entries `< q`)

`𝒯0 w` is the set of MZVs `ζ_A(s_1,…,s_r)` of weight `w` with **all** entries `< q`
(`ChallengeDeps.𝒯0`), the spanning set of the second half of Dac's Theorem B.  This module
provides the analogue of `Counting`/`DegCountAnyF` for `𝒯0`:

* `ShapeT0 F w v` — the padded Hoffman shapes whose entries are all `< q`, and `hoffCount0`;
* `mem_T0aux`, `mem_T0` — membership in `𝒯0_aux`/`𝒯0` as `ζ_A` of a bounded tuple;
* `T0Exists`, `T0tuple` — a chosen bounded representative of a value of `𝒯0 w`;
* `valueToShape0` and `valueToShape0_inj` — the injection `𝒯0 w ↪ ShapeT0 F w w`;
* `ncard_T0_eq_hoffCount0 : ncard (𝒯0 F w) = hoffCount0 F w` for every finite field;
* `ncard_T0_le_d : ncard (𝒯0 F w) ≤ d F w`;
* `shapeEquivT0` and `linearIndependent_T0`, the `𝒯0`-analogues of `shapeEquivT` and
  `linearIndependent_T` of `LinIndep`.

Everything is stated for an arbitrary finite field `F`.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## 1. Membership in `𝒯0_aux` and `𝒯0` -/

/-- Membership in `𝒯0_aux`: a `ζ_A` of a weight-`w` tuple of depth `r` all of whose entries
are `< q`. -/
lemma mem_T0aux (w : ℕ) (r : ℕ+) (v : RatFunc.CompletionAtInfty F) :
    v ∈ 𝒯0_aux F w r ↔ ∃ s : Fin (r : ℕ) → ℕ+,
      (∑ i : Fin (r : ℕ), ((s i : ℕ+)) : ℕ) = w ∧
      (∀ i : Fin (r : ℕ), (s i : ℕ) < Nat.card F) ∧
      ζ_A F s = v := by
  classical
  simp only [𝒯0_aux, 𝔖_w, Set.mem_setOf_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨s, ⟨hsum, hlt⟩, hζ⟩
    exact ⟨s, hsum, hlt, hζ⟩
  · rintro ⟨s, hsum, hlt, hζ⟩
    exact ⟨s, ⟨hsum, hlt⟩, hζ⟩

/-- Membership in `𝒯0`: a `ζ_A` of a weight-`w` tuple with all entries `< q`, of some depth. -/
lemma mem_T0 (w : ℕ) (v : RatFunc.CompletionAtInfty F) :
    v ∈ 𝒯0 F w ↔ ∃ r : ℕ+, v ∈ 𝒯0_aux F w r := by
  simp [𝒯0]

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## 2. The `𝒯0`-shapes -/

/-- Weight-`v` padded Hoffman shapes all of whose entries are `< q` (the shapes of `𝒯0`). -/
def ShapeT0 (w v : ℕ) : Type :=
  {x : ShapeT F w v // ∀ i : Fin w, ((x.1.2 i : Fin (Nat.card F + 1)) : ℕ) < Nat.card F}

/-- The number of weight-`w` Hoffman shapes with all entries `< q`. -/
noncomputable def hoffCount0 (w : ℕ) : ℕ := Nat.card (ShapeT0 F w w)

noncomputable instance (w v : ℕ) : Fintype (ShapeT0 F w v) := by
  classical
  unfold ShapeT0
  infer_instance

/-- The entries of the tuple of a `𝒯0`-shape are `< q`. -/
lemma shapeTuple_lt_card {w : ℕ} (x : ShapeT0 F w w)
    (i : Fin ((x.1.1.1 : ℕ) + 1)) :
    (shapeTuple F x.1 i : ℕ) < Nat.card F := by
  rw [shapeTuple_val F x.1 i]
  exact x.2 ⟨(i : ℕ), by have h1 := i.isLt; have h2 := x.1.1.1.isLt; omega⟩

/-- The MZV of the tuple attached to a `𝒯0`-shape lies in `𝒯0 F w`. -/
lemma shapeTuple_mem_T0 {w : ℕ} (ehw : w ≠ 0) (x : ShapeT0 F w w) :
    ζ_A F (shapeTuple F x.1) ∈ 𝒯0 F w := by
  have hw : 1 ≤ w := Nat.one_le_iff_ne_zero.mpr ehw
  rw [mem_T0 F w]
  refine ⟨⟨(x.1.1.1 : ℕ) + 1, by have h := x.1.1.1.isLt; omega⟩, ?_⟩
  rw [mem_T0aux F w ⟨(x.1.1.1 : ℕ) + 1, by have h := x.1.1.1.isLt; omega⟩]
  exact ⟨shapeTuple F x.1, shapeTuple_weight F x.1, fun i => shapeTuple_lt_card F x i, rfl⟩

/-- **The MZV of the shape of a Hoffman tuple is the MZV of the tuple.** -/
lemma shapeTuple_tupleShape_zeta {w : ℕ} (hw : 1 ≤ w) {r : ℕ} (hr1 : 1 ≤ r) (hrw : r ≤ w)
    (s : Fin r → ℕ+) (hsum : (∑ i : Fin r, ((s i : ℕ+)) : ℕ) = w)
    (hfirst : ∀ i : Fin r, (i : ℕ) < r - 1 → (s i : ℕ) ≤ Nat.card F)
    (hlast : (s ⟨r - 1, by omega⟩ : ℕ) < Nat.card F) :
    ζ_A F (shapeTuple F (tupleShape F w hw r hr1 hrw s hsum hfirst hlast)) = ζ_A F s := by
  refine ζ_A_eq_of_reindex F (tupleShape_depth F hw hr1 hrw s hsum hfirst hlast) _ _ ?_
  intro i
  exact Subtype.ext (shapeTuple_tupleShape F hw hr1 hrw s hsum hfirst hlast i)

/-! ## 3. A chosen bounded representative of a value of `𝒯0 w` -/

/-- Every value of `𝒯0 F w` admits a bounded weight-`w` tuple. -/
noncomputable def T0Exists (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    ∃ t : Σ r : ℕ, Fin r → ℕ+,
      1 ≤ t.1 ∧ (∑ i : Fin t.1, (t.2 i : ℕ)) = w ∧
      (∀ i : Fin t.1, (t.2 i : ℕ) < Nat.card F) ∧
      ζ_A F t.2 = v.val := by
  classical
  obtain ⟨r, hr⟩ := (mem_T0 F w v.val).mp v.2
  obtain ⟨s, hsum, hlt, hζ⟩ := (mem_T0aux F w r v.val).mp hr
  exact ⟨⟨(r : ℕ), s⟩, Nat.succ_le_of_lt r.pos, hsum, hlt, hζ⟩

/-- The chosen bounded weight-`w` tuple of a value of `𝒯0 F w`. -/
noncomputable def T0tuple (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) : Σ r : ℕ, Fin r → ℕ+ :=
  Classical.choose (T0Exists F w hw v)

lemma T0tuple_weight (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    (∑ i : Fin (T0tuple F w hw v).1, ((T0tuple F w hw v).2 i : ℕ)) = w :=
  (Classical.choose_spec (T0Exists F w hw v)).2.1

lemma T0tuple_lt (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    ∀ i : Fin (T0tuple F w hw v).1, ((T0tuple F w hw v).2 i : ℕ) < Nat.card F :=
  (Classical.choose_spec (T0Exists F w hw v)).2.2.1

lemma T0tuple_zeta (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    ζ_A F (T0tuple F w hw v).2 = v.val :=
  (Classical.choose_spec (T0Exists F w hw v)).2.2.2

/-- The arity of the chosen representative is positive. -/
lemma T0tuple_arity_pos (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    1 ≤ (T0tuple F w hw v).1 :=
  (Classical.choose_spec (T0Exists F w hw v)).1

/-- The arity of the chosen representative is at most the weight. -/
lemma T0tuple_arity_le (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    (T0tuple F w hw v).1 ≤ w := by
  have hc := card_le_sum_pnat (T0tuple F w hw v).1 (T0tuple F w hw v).2
  rw [T0tuple_weight F w hw v] at hc
  exact hc

/-! ## 4. The injection `𝒯0 w ↪ ShapeT0` -/

/-- The shape of the chosen bounded representative of a value of `𝒯0 F w`. -/
noncomputable def valueToShapeT0 (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) : ShapeT F w w :=
  tupleShape F w hw (T0tuple F w hw v).1 (T0tuple_arity_pos F w hw v)
    (T0tuple_arity_le F w hw v) (T0tuple F w hw v).2 (T0tuple_weight F w hw v)
    (fun i _ => le_of_lt (T0tuple_lt F w hw v i))
    (T0tuple_lt F w hw v ⟨(T0tuple F w hw v).1 - 1, by
      have h := T0tuple_arity_pos F w hw v; omega⟩)

/-- All entries of that shape are `< q`. -/
lemma valueToShapeT0_mem (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    ∀ i : Fin w, (((valueToShapeT0 F w hw v).1.2 i : Fin (Nat.card F + 1)) : ℕ) < Nat.card F := by
  intro i
  by_cases hi : (i : ℕ) < (T0tuple F w hw v).1
  · have h1 : (valueToShapeT0 F w hw v).1.2 i
        = (tupleShape F w hw (T0tuple F w hw v).1 (T0tuple_arity_pos F w hw v)
            (T0tuple_arity_le F w hw v) (T0tuple F w hw v).2 (T0tuple_weight F w hw v)
            (fun i _ => le_of_lt (T0tuple_lt F w hw v i))
            (T0tuple_lt F w hw v ⟨(T0tuple F w hw v).1 - 1, by
              have h := T0tuple_arity_pos F w hw v; omega⟩)).1.2 i := rfl
    rw [h1,
      tupleShape_entry F hw (T0tuple_arity_pos F w hw v) (T0tuple_arity_le F w hw v)
        (T0tuple F w hw v).2 (T0tuple_weight F w hw v)
        (fun i _ => le_of_lt (T0tuple_lt F w hw v i))
        (T0tuple_lt F w hw v ⟨_, _⟩) (i := i) hi]
    exact T0tuple_lt F w hw v ⟨(i : ℕ), hi⟩
  · have hge : (T0tuple F w hw v).1 ≤ (i : ℕ) := by omega
    have h1 : (valueToShapeT0 F w hw v).1.2 i
        = (tupleShape F w hw (T0tuple F w hw v).1 (T0tuple_arity_pos F w hw v)
            (T0tuple_arity_le F w hw v) (T0tuple F w hw v).2 (T0tuple_weight F w hw v)
            (fun i _ => le_of_lt (T0tuple_lt F w hw v i))
            (T0tuple_lt F w hw v ⟨(T0tuple F w hw v).1 - 1, by
              have h := T0tuple_arity_pos F w hw v; omega⟩)).1.2 i := rfl
    rw [h1]
    show (((tupleEntry F (T0tuple_arity_pos F w hw v) (T0tuple F w hw v).2
        (fun i _ => le_of_lt (T0tuple_lt F w hw v i))
        (T0tuple_lt F w hw v ⟨(T0tuple F w hw v).1 - 1, by
          have h := T0tuple_arity_pos F w hw v; omega⟩)) i :
        Fin (Nat.card F + 1)) : ℕ) < Nat.card F
    rw [tupleEntry_val_ge F (T0tuple_arity_pos F w hw v) (T0tuple F w hw v).2
      (fun i _ => le_of_lt (T0tuple_lt F w hw v i))
      (T0tuple_lt F w hw v ⟨_, _⟩) (i := i) hge]
    exact (by have := card_ge_two F; omega : (0:ℕ) < Nat.card F)

/-- ★ The shape of a value of `𝒯0 F w`, as a `𝒯0`-shape. -/
noncomputable def valueToShape0 (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) : ShapeT0 F w w :=
  ⟨valueToShapeT0 F w hw v, valueToShapeT0_mem F w hw v⟩

/-- The MZV of the shape of a value of `𝒯0 F w` is the value. -/
lemma valueToShape0_zeta (w : ℕ) (hw : 1 ≤ w)
    (v : {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}) :
    ζ_A F (shapeTuple F (valueToShape0 F w hw v).1) = v.val := by
  show ζ_A F (shapeTuple F (valueToShapeT0 F w hw v)) = v.val
  unfold valueToShapeT0
  exact (shapeTuple_tupleShape_zeta F hw (T0tuple_arity_pos F w hw v)
    (T0tuple_arity_le F w hw v) (T0tuple F w hw v).2 (T0tuple_weight F w hw v)
    (fun i _ => le_of_lt (T0tuple_lt F w hw v i))
    (T0tuple_lt F w hw v ⟨(T0tuple F w hw v).1 - 1, by
      have h := T0tuple_arity_pos F w hw v; omega⟩)).trans (T0tuple_zeta F w hw v)

/-- ★★ **The map sending a value of `𝒯0 F w` to the shape of a bounded representative is
injective.** -/
lemma valueToShape0_inj (w : ℕ) (hw : 1 ≤ w) :
    Function.Injective (valueToShape0 F w hw) := by
  intro v₁ v₂ h
  apply Subtype.ext
  rw [← valueToShape0_zeta F w hw v₁, h, valueToShape0_zeta F w hw v₂]

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## 5. The count `ncard (𝒯0 F w) = hoffCount0 F w` -/

/-- ★★ `ncard (𝒯0 F w) ≤ hoffCount0 F w`. -/
theorem ncard_T0_le_hoffCount0 (w : ℕ) (hw : 1 ≤ w) :
    Set.ncard (𝒯0 F w) ≤ hoffCount0 F w := by
  haveI : Finite {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} :=
    Finite.of_injective (valueToShape0 F w hw) (valueToShape0_inj F w hw)
  have hcard : Nat.card {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}
      ≤ Nat.card (ShapeT0 F w w) :=
    Nat.card_le_card_of_injective _ (valueToShape0_inj F w hw)
  have hco : Set.ncard (𝒯0 F w)
      = (Set.univ : Set {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}).ncard :=
    (Set.ncard_coe (𝒯0 F w)).symm
  have hun : (Set.univ : Set {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w}).ncard
      = Nat.card {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} := Set.ncard_univ _
  calc Set.ncard (𝒯0 F w) = Nat.card {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} := by
        rw [hco, hun]
    _ ≤ Nat.card (ShapeT0 F w w) := hcard
    _ = hoffCount0 F w := rfl

/-- `hoffCount0 F w ≤ ncard (𝒯0 F w)`: the `𝒯0`-shapes inject into `𝒯0 w`. -/
theorem hoffCount0_le_ncard_T0 (w : ℕ) (hw : 1 ≤ w) :
    hoffCount0 F w ≤ Set.ncard (𝒯0 F w) := by
  classical
  haveI : Finite {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} :=
    Finite.of_injective (valueToShape0 F w hw) (valueToShape0_inj F w hw)
  have hinj : Function.Injective (fun x : ShapeT0 F w w =>
      (⟨ζ_A F (shapeTuple F x.1),
        shapeTuple_mem_T0 F (Nat.one_le_iff_ne_zero.mp hw) x⟩ :
        {v : RatFunc.CompletionAtInfty F // v ∈ 𝒯0 F w})) := by
    intro x y hxy
    exact Subtype.ext (shapeTuple_zeta_injective F hw (congrArg Subtype.val hxy))
  have hcard : Nat.card (ShapeT0 F w w)
      ≤ Nat.card {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} :=
    Nat.card_le_card_of_injective _ hinj
  have hco : Set.ncard (𝒯0 F w)
      = Nat.card {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} := by
    rw [(Set.ncard_coe (𝒯0 F w)).symm, Set.ncard_univ]
  calc hoffCount0 F w = Nat.card (ShapeT0 F w w) := rfl
    _ ≤ Nat.card {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯0 F w} := hcard
    _ = Set.ncard (𝒯0 F w) := hco.symm

/-- ★★★ **`ncard (𝒯0 F w) = hoffCount0 F w`** — the number of MZVs in `𝒯0 w` is the number of
weight-`w` tuples all of whose entries are `< q`, for every finite field. -/
theorem ncard_T0_eq_hoffCount0 (w : ℕ) (hw : 1 ≤ w) :
    Set.ncard (𝒯0 F w) = hoffCount0 F w :=
  le_antisymm (ncard_T0_le_hoffCount0 F w hw) (hoffCount0_le_ncard_T0 F w hw)

/-- ★★ **`ncard (𝒯0 F w) ≤ d F w`** (the `𝒯0`-analogue of `ncard_T_eq_d`). -/
theorem ncard_T0_le_d (w : ℕ) (hw : 1 ≤ w) : Set.ncard (𝒯0 F w) ≤ d F w := by
  have hfinT : Set.Finite (𝒯 F w) := by
    have hFin : Finite {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯 F w} :=
      Finite.of_injective (valueToShape F w hw) (valueToShape_inj F w hw)
    letI := hFin
    exact Set.toFinite (𝒯 F w)
  calc Set.ncard (𝒯0 F w) ≤ Set.ncard (𝒯 F w) :=
        Set.ncard_le_ncard (𝒯0_subset_𝒯 F w) hfinT
    _ = d F w := ncard_T_eq_d F w hw

end ZagierHoffmanPositiveChar

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

/-! ## 6. The shape ↔ `𝒯0 w` bijection and `F_q`-linear independence of `𝒯0 w` -/

/-- The shape-to-MZV map of a weight-`w` `𝒯0`-shape. -/
noncomputable def shapeVal0 {w : ℕ} (hw : 1 ≤ w) (x : ShapeT0 F w w) :
    {v : RatFunc.CompletionAtInfty F // v ∈ 𝒯0 F w} :=
  ⟨ζ_A F (shapeTuple F x.1), shapeTuple_mem_T0 F (Nat.one_le_iff_ne_zero.mp hw) x⟩

/-- `shapeVal0` is injective. -/
lemma shapeVal0_injective {w : ℕ} (hw : 1 ≤ w) : Function.Injective (shapeVal0 F hw) := by
  intro x y hxy
  exact Subtype.ext (shapeTuple_zeta_injective F hw (congrArg Subtype.val hxy))

/-- `shapeVal0` is surjective. -/
lemma shapeVal0_surjective {w : ℕ} (hw : 1 ≤ w) : Function.Surjective (shapeVal0 F hw) := by
  intro v
  refine ⟨valueToShape0 F w hw v, ?_⟩
  apply Subtype.ext
  exact valueToShape0_zeta F w hw v

/-- ★★ **The canonical bijection between the weight-`w` `𝒯0`-shapes and the set `𝒯0 F w`.**
(As a byproduct, `ncard (𝒯0 F w) = hoffCount0 F w`.) -/
noncomputable def shapeEquivT0 {w : ℕ} (hw : 1 ≤ w) :
    ShapeT0 F w w ≃ {v : RatFunc.CompletionAtInfty F // v ∈ 𝒯0 F w} :=
  Equiv.ofBijective (shapeVal0 F hw) ⟨shapeVal0_injective F hw, shapeVal0_surjective F hw⟩

/-- ★★ **No nontrivial `F_q`-linear relation between the MZVs of `𝒯0 w` with all entries
`< q`** (the `𝒯0`-analogue of `linearIndependent_shape`). -/
theorem linearIndependent_shape0 {w : ℕ} (hw : 1 ≤ w) (c : ShapeT0 F w w → F)
    (h : (∑ x : ShapeT0 F w w, cst F (c x) * ζ_A F (shapeTuple F x.1)) = 0) :
    ∀ x, c x = 0 := by
  classical
  refine zeta_linearIndependent_le_card F
    (fun x : ShapeT0 F w w =>
      (⟨(x.1.1.1 : ℕ) + 1, shapeTuple F x.1⟩ : Σ r : ℕ, Fin r → ℕ+))
    (fun x => Nat.succ_le_succ (Nat.zero_le _))
    (fun x j => le_of_lt (shapeTuple_lt_card F x j))
    (fun x y hxy => Subtype.ext (degExp_shapeTuple_injective F hw hxy))
    c h

/-- ★★ **No nontrivial `F_q`-linear relation between the elements of `𝒯0 F w`** (transported
along the shape bijection `shapeEquivT0`). -/
theorem linearIndependent_T0 {w : ℕ} (hw : 1 ≤ w)
    (c : {v : RatFunc.CompletionAtInfty F // v ∈ 𝒯0 F w} → F)
    (h : (∑ x : ShapeT0 F w w, cst F (c (shapeEquivT0 F hw x)) * ζ_A F (shapeTuple F x.1)) = 0) :
    ∀ v, c v = 0 := by
  classical
  have hc := linearIndependent_shape0 F hw (fun x => c (shapeEquivT0 F hw x)) h
  intro v
  obtain ⟨x, rfl⟩ := (shapeEquivT0 F hw).surjective v
  exact hc x

/-! ## 7. Regression -/

attribute [local instance 100] Classical.decEq

/-- Over `F₄`: the `𝒯0`-count is at most `d`. -/
example : Set.ncard (𝒯0 (GaloisField 2 2) 3) ≤ d (GaloisField 2 2) 3 :=
  ncard_T0_le_d (GaloisField 2 2) 3 (by norm_num)

end ZagierHoffmanPositiveChar
