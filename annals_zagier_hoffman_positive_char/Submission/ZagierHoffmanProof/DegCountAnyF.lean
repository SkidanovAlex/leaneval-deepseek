/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Submission.ZagierHoffmanProof.DegAnyF
import Submission.ZagierHoffmanProof.Counting

set_option autoImplicit false
set_option maxHeartbeats 4000000

open Polynomial RatFunc
open scoped BigOperators WithZero
open WithZero

/-!
# The counting statement `ncard (𝒯 F w) = d F w` over an *arbitrary* finite field

Because the MZVs attached to tuples with entries `≤ q` are injective
(`DegAnyF.zeta_A_injective_le_card`), the canonical tuple attached to a Hoffman shape gives an
injection from the shapes into `𝒯 F w`.  Combined with the existing
`Counting.𝒯_ncard_le` and `Counting.hoffCount_eq_d` this yields `ncard (𝒯 F w) = d F w`
(the reverse of SESSION 285's `≤`) for **every** finite field.
-/

namespace ZagierHoffmanPositiveChar

variable (F : Type*) [Field F] [Finite F] [DecidableEq (RatFunc F)]

section ShapeTuple

/-- The positive-exponent tuple attached to a padded Hoffman shape. -/
noncomputable def shapeTuple {w : ℕ} (x : ShapeT F w w) : Fin ((x.1.1 : ℕ) + 1) → ℕ+ :=
  fun i =>
    ⟨((x.1.2 ⟨(i : ℕ), by have h1 := i.isLt; have h2 := x.1.1.isLt; omega⟩ :
        Fin (Nat.card F + 1)) : ℕ),
      x.2.2.1 ⟨(i : ℕ), by have h1 := i.isLt; have h2 := x.1.1.isLt; omega⟩
        (by show (i : ℕ) ≤ (x.1.1 : ℕ); omega)⟩

lemma shapeTuple_val {w : ℕ} (x : ShapeT F w w) (i : Fin ((x.1.1 : ℕ) + 1)) :
    (shapeTuple F x i : ℕ)
      = ((x.1.2 ⟨(i : ℕ), by have h1 := i.isLt; have h2 := x.1.1.isLt; omega⟩ :
          Fin (Nat.card F + 1)) : ℕ) := rfl

lemma shapeTuple_le {w : ℕ} (x : ShapeT F w w) (i : Fin ((x.1.1 : ℕ) + 1)) :
    (shapeTuple F x i : ℕ) ≤ Nat.card F := by
  rw [shapeTuple_val F x i]
  have h := (x.1.2 ⟨(i : ℕ), by have h1 := i.isLt; have h2 := x.1.1.isLt; omega⟩ :
    Fin (Nat.card F + 1)).isLt
  omega

lemma shapeTuple_last {w : ℕ} (x : ShapeT F w w) :
    (shapeTuple F x ⟨(x.1.1 : ℕ), by omega⟩ : ℕ) < Nat.card F := by
  rw [shapeTuple_val F x ⟨(x.1.1 : ℕ), by omega⟩]
  exact x.2.2.2.2

lemma shapeTuple_weight_sum {w : ℕ} (x : ShapeT F w w) :
    (∑ i : Fin ((x.1.1 : ℕ) + 1), (shapeTuple F x i : ℕ))
      = ∑ i : Fin w, ((x.1.2 i : Fin (Nat.card F + 1)) : ℕ) := by
  have hcut := sum_fin_cut (v := (x.1.1 : ℕ) + 1) (w := w)
    (by have h := ShapeT_depth_le F x; omega)
    (g := fun i : Fin w => ((x.1.2 i : Fin (Nat.card F + 1)) : ℕ))
    (fun i hi => x.2.2.2.1 i (by omega))
  rw [hcut]
  refine Finset.sum_congr (by rfl) ?_
  intro j _
  exact shapeTuple_val F x j

lemma shapeTuple_weight {w : ℕ} (x : ShapeT F w w) :
    (∑ i : Fin ((x.1.1 : ℕ) + 1), (shapeTuple F x i : ℕ)) = w := by
  rw [shapeTuple_weight_sum F x, x.2.1]

end ShapeTuple

section Membership

/-- The MZV of the tuple attached to a shape lies in `𝒯 F w`. -/
lemma shapeTuple_mem_T {w : ℕ} (ehw : w ≠ 0) (x : ShapeT F w w) :
    ζ_A F (shapeTuple F x) ∈ 𝒯 F w := by
  have hw : 1 ≤ w := Nat.one_le_iff_ne_zero.mpr ehw
  have hd : 0 < (x.1.1 : ℕ) + 1 := by omega
  rw [mem_T F w]
  refine ⟨⟨(x.1.1 : ℕ) + 1, hd⟩, ?_⟩
  rw [mem_Taux F w ⟨(x.1.1 : ℕ) + 1, hd⟩]
  exact ⟨shapeTuple F x, shapeTuple_weight F x, fun i _ => shapeTuple_le F x i,
    shapeTuple_last F x, rfl⟩

/-- The entry of `shapeTuple` at an index `≤` the marker is the padded entry. -/
lemma shapeTuple_val_apply {w : ℕ} (x : ShapeT F w w) {i : Fin w}
    (hi : (i : ℕ) ≤ (x.1.1 : ℕ)) :
    (shapeTuple F x ⟨(i : ℕ), by have h := ShapeT_depth_le F x; omega⟩ : ℕ)
      = ((x.1.2 i : Fin (Nat.card F + 1)) : ℕ) := by
  rw [shapeTuple_val F x ⟨(i : ℕ), by have h := ShapeT_depth_le F x; omega⟩]

end Membership

section RoundTrip

/-- The value of a transported `Fin` element. -/
lemma fin_cast_val {a b : ℕ} (h : a = b) (i : Fin a) : ((h ▸ i : Fin b) : ℕ) = (i : ℕ) := by
  cases h
  rfl

/-- **The Hoffman shape of the tuple attached to a shape is the shape itself.** -/
lemma tupleShape_shapeTuple {w : ℕ} (hw : 1 ≤ w) (x : ShapeT F w w) :
    tupleShape F w hw ((x.1.1 : ℕ) + 1) (by omega)
      (by have h := ShapeT_depth_le F x; omega) (shapeTuple F x)
      (shapeTuple_weight F x) (fun i _ => shapeTuple_le F x i) (shapeTuple_last F x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    have h := tupleShape_depth F hw (by omega)
      (by have h := ShapeT_depth_le F x; omega) (shapeTuple F x)
      (shapeTuple_weight F x) (fun i _ => shapeTuple_le F x i) (shapeTuple_last F x)
    omega
  · funext i
    by_cases hi : (i : ℕ) ≤ (x.1.1 : ℕ)
    · have hir : (i : ℕ) < (x.1.1 : ℕ) + 1 := by omega
      apply Fin.ext
      rw [tupleShape_entry F hw (by omega) (by have h := ShapeT_depth_le F x; omega)
        (shapeTuple F x) (shapeTuple_weight F x) (fun i _ => shapeTuple_le F x i)
        (shapeTuple_last F x) (i := i) hir,
        shapeTuple_val_apply F x hi]
    · have hir : (x.1.1 : ℕ) < (i : ℕ) := by omega
      have htd := tupleShape_depth F hw (by omega)
        (by have h := ShapeT_depth_le F x; omega) (shapeTuple F x)
        (shapeTuple_weight F x) (fun i _ => shapeTuple_le F x i) (shapeTuple_last F x)
      apply Fin.ext
      rw [show (((tupleShape F w hw ((x.1.1 : ℕ) + 1) (by omega)
          (by have h := ShapeT_depth_le F x; omega) (shapeTuple F x)
          (shapeTuple_weight F x) (fun i _ => shapeTuple_le F x i)
          (shapeTuple_last F x)).1.2 i : Fin (Nat.card F + 1)) : ℕ) = 0 from
        (tupleShape F w hw ((x.1.1 : ℕ) + 1) (by omega)
          (by have h := ShapeT_depth_le F x; omega) (shapeTuple F x)
          (shapeTuple_weight F x) (fun i _ => shapeTuple_le F x i)
          (shapeTuple_last F x)).2.2.2.1 i (by omega),
        x.2.2.2.1 i hir]

end RoundTrip

section Injective

/-- **The MZV map is injective on the tuples attached to Hoffman shapes** (entries `≤ q`),
over an arbitrary finite field. -/
lemma shapeTuple_zeta_injective {w : ℕ} (hw : 1 ≤ w) {x y : ShapeT F w w}
    (h : ζ_A F (shapeTuple F x) = ζ_A F (shapeTuple F y)) : x = y := by
  obtain ⟨h1, h2⟩ := zeta_A_injective_le_card F (by omega) (by omega) (shapeTuple F x)
    (shapeTuple F y) (fun i => shapeTuple_le F x i) (fun i => shapeTuple_le F y i)
    (by rw [tupleWeight, tupleWeight, shapeTuple_weight F x, shapeTuple_weight F y]) h
  have hmark : (x.1.1 : ℕ) = (y.1.1 : ℕ) := by omega
  apply Subtype.ext
  apply Prod.ext
  · apply Fin.ext
    exact hmark
  · funext i
    by_cases hi : (i : ℕ) ≤ (x.1.1 : ℕ)
    · have hxi : (i : ℕ) < (x.1.1 : ℕ) + 1 := by omega
      have hyi : (i : ℕ) ≤ (y.1.1 : ℕ) := by omega
      apply Fin.ext
      have key := h2 ⟨(i : ℕ), hxi⟩
      have hidx : (h1 ▸ ⟨(i : ℕ), hxi⟩ : Fin ((y.1.1 : ℕ) + 1))
          = ⟨(i : ℕ), by omega⟩ := by
        apply Fin.ext
        rw [fin_cast_val h1 ⟨(i : ℕ), hxi⟩]
      have e2 : (shapeTuple F y (h1 ▸ ⟨(i : ℕ), hxi⟩) : ℕ)
          = (shapeTuple F y ⟨(i : ℕ), by omega⟩ : ℕ) := by
        rw [hidx]
      rw [← shapeTuple_val_apply F x hi, ← shapeTuple_val_apply F y hyi, ← e2]
      exact congrArg (fun t : ℕ+ => (t : ℕ)) key
    · have hxi : (x.1.1 : ℕ) < (i : ℕ) := by omega
      have hyi : (y.1.1 : ℕ) < (i : ℕ) := by omega
      apply Fin.ext
      rw [x.2.2.2.1 i hxi, y.2.2.2.1 i hyi]

end Injective

section Count

/-- ★★★ **`ncard (𝒯 F w) = hoffCount F w = d F w`** for every finite field `F`. -/
theorem ncard_T_eq_hoffCount (w : ℕ) (hw : 1 ≤ w) :
    Set.ncard (𝒯 F w) = hoffCount F w := by
  refine le_antisymm (𝒯_ncard_le F w hw) ?_
  haveI : Finite (ShapeT F w w) := Finite.of_fintype _
  haveI : Finite {v : RatFunc.CompletionAtInfty F // v ∈ 𝒯 F w} :=
    Finite.of_injective (valueToShape F w hw) (valueToShape_inj F w hw)
  have hφ : Function.Injective
      (fun x : ShapeT F w w =>
        (⟨ζ_A F (shapeTuple F x), shapeTuple_mem_T F (by omega) x⟩ :
          {v : RatFunc.CompletionAtInfty F // v ∈ 𝒯 F w})) := by
    intro x y hxy
    exact shapeTuple_zeta_injective F hw (congrArg Subtype.val hxy)
  have h1 : Nat.card (ShapeT F w w)
      ≤ Nat.card {v : RatFunc.CompletionAtInfty F // v ∈ 𝒯 F w} :=
    Nat.card_le_card_of_injective _ hφ
  have hco : Set.ncard (𝒯 F w)
      = (Set.univ : Set {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯 F w}).ncard :=
    (Set.ncard_coe (𝒯 F w)).symm
  have hun : (Set.univ : Set {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯 F w}).ncard
      = Nat.card {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯 F w} := Set.ncard_univ _
  calc hoffCount F w = Nat.card (ShapeT F w w) := rfl
    _ ≤ Nat.card {x : RatFunc.CompletionAtInfty F // x ∈ 𝒯 F w} := h1
    _ = (Set.univ : Set {x // x ∈ 𝒯 F w}).ncard := hun.symm
    _ = Set.ncard (𝒯 F w) := hco.symm

/-- ★★★ **`ncard (𝒯 F w) = d F w`** for every finite field `F` (the reverse of
`Counting.𝒯_ncard_le`). -/
theorem ncard_T_eq_d (w : ℕ) (hw : 1 ≤ w) : Set.ncard (𝒯 F w) = d F w := by
  rw [ncard_T_eq_hoffCount F w hw, hoffCount_eq_d F w hw]

end Count

section Regression

attribute [local instance 100] Classical.decEq

/-- Over the prime field `F₂`: `ncard (𝒯 F 2) = d F 2`. -/
example : Set.ncard (𝒯 (ZMod 2) 2) = d (ZMod 2) 2 :=
  ncard_T_eq_d (ZMod 2) 2 (by norm_num)

/-- Over `F₄ = GaloisField 2 2`: `ncard (𝒯 F 3) = d F 3`. -/
example : Set.ncard (𝒯 (GaloisField 2 2) 3) = d (GaloisField 2 2) 3 :=
  ncard_T_eq_d (GaloisField 2 2) 3 (by norm_num)

/-- Over `F₄`: the MZV `ζ_A(1,1)` (entries `≤ 4`) is nonzero. -/
example : ζ_A (GaloisField 2 2) (fun _ : Fin 2 => (1 : ℕ+)) ≠ 0 :=
  zeta_ne_zero_le_card (GaloisField 2 2) (by norm_num) _
    (by intro i; fin_cases i <;>
      rw [GaloisField.card (p := 2) (n := 2) (by norm_num)] <;> norm_num)

/-- Over `F₉ = GaloisField 3 2`: the MZV `ζ_A(1,1)` (entries `≤ 9`) is nonzero. -/
example : ζ_A (GaloisField 3 2) (fun _ : Fin 2 => (1 : ℕ+)) ≠ 0 :=
  zeta_ne_zero_le_card (GaloisField 3 2) (by norm_num) _
    (by intro i; fin_cases i <;>
      rw [GaloisField.card (p := 3) (n := 2) (by norm_num)] <;> norm_num)

end Regression

end ZagierHoffmanPositiveChar
