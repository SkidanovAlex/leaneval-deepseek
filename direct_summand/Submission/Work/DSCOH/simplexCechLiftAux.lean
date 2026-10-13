/-
Area DSCOH — auxiliary constructions for the simplex (Čech) acyclicity lemma
`Work.DSCOH.simplex_cech_lift_level`.

Given a finite linearly ordered type `V`, a finite set `Z : Finset V` and `m` with
`Z.card + 1 ≤ m`, the acyclicity lemma produces an `A`-linear contraction `L` which, on
cocycles, inverts the alternating coboundary
`(d f)(T) = Σ_{i ∈ T\Z} (-1)^{#{x ∈ T : x < i}} f(T \ {i})`.

The construction is the classical "cone over the smallest element of `V \ Z`" contraction:
pick `a = min (V \ Z)` and put

  `(L c)(U) = (-1)^{z₀} • c (U ∪ {a})`  if `a ∉ U`,  and `0` otherwise,

where `z₀ = #{x ∈ Z : x < a}`.  This file collects the (small) definitional scaffolding
for that construction, kept separate from the main combinatorial verification.
-/
import Mathlib

open Finset
open scoped BigOperators

namespace Work.DSCOH

variable {A : Type*} [CommRing A] {V : Type*} [LinearOrder V] [DecidableEq V]

/-! ## The index obtained by adjoining the cone point -/

/-- The level-`m` index obtained from a level-`(m-1)` index `U` by adjoining an element
`a ∉ U`:  `U ∪ {a}`. -/
def augIdx (Z : Finset V) (m : ℕ) (a : V)
    (U : {U : Finset V // Z ⊆ U ∧ U.card + 1 = m}) (h : a ∉ U.1) :
    {S : Finset V // Z ⊆ S ∧ S.card = m} :=
  ⟨U.1 ∪ {a}, fun j hj => Finset.mem_union.mpr (Or.inl (U.2.1 hj)),
   by rw [Finset.union_singleton, Finset.card_insert_of_notMem h, U.2.2]⟩

@[simp] lemma augIdx_val (Z : Finset V) (m : ℕ) (a : V)
    (U : {U : Finset V // Z ⊆ U ∧ U.card + 1 = m}) (h : a ∉ U.1) :
    (augIdx Z m a U h).1 = U.1 ∪ {a} := rfl

/-- The level-`(m-1)` index `T \ {i}`, for `T` a level-`m` index and `i ∈ T \ Z`. -/
def mkEraseIdx (Z : Finset V) (m : ℕ)
    (T : {T : Finset V // Z ⊆ T ∧ T.card = m}) (i : V) (hi : i ∈ T.1 \ Z) :
    {U : Finset V // Z ⊆ U ∧ U.card + 1 = m} :=
  ⟨T.1.erase i,
   fun j hj => Finset.mem_erase.mpr
     ⟨fun hji => (Finset.mem_sdiff.mp hi).2 (hji ▸ hj), T.2.1 hj⟩,
   by rw [Finset.card_erase_add_one (Finset.mem_sdiff.mp hi).1, T.2.2]⟩

@[simp] lemma mkEraseIdx_val (Z : Finset V) (m : ℕ)
    (T : {T : Finset V // Z ⊆ T ∧ T.card = m}) (i : V) (hi : i ∈ T.1 \ Z) :
    (mkEraseIdx Z m T i hi).1 = T.1.erase i := rfl

/-- The level-`m` index `T \ {i}`, for `T` a level-`(m+1)` index and `i ∈ T \ Z`. -/
def mkEraseIdxH (Z : Finset V) (m : ℕ)
    (T : {T : Finset V // Z ⊆ T ∧ T.card = m + 1}) (i : V) (hi : i ∈ T.1 \ Z) :
    {S : Finset V // Z ⊆ S ∧ S.card = m} :=
  ⟨T.1.erase i,
   fun j hj => Finset.mem_erase.mpr
     ⟨fun hji => (Finset.mem_sdiff.mp hi).2 (hji ▸ hj), T.2.1 hj⟩,
   by rw [Finset.card_erase_of_mem (Finset.mem_sdiff.mp hi).1]; omega⟩

@[simp] lemma mkEraseIdxH_val (Z : Finset V) (m : ℕ)
    (T : {T : Finset V // Z ⊆ T ∧ T.card = m + 1}) (i : V) (hi : i ∈ T.1 \ Z) :
    (mkEraseIdxH Z m T i hi).1 = T.1.erase i := rfl

/-! ## The cone contraction -/

/-- The `a`-cone contraction `L` with sign `(-1)^{z₀}`. -/
noncomputable def apexL (Z : Finset V) (m : ℕ) (a : V) (z0 : ℕ) :
    ({S : Finset V // Z ⊆ S ∧ S.card = m} → A) →ₗ[A]
      ({U : Finset V // Z ⊆ U ∧ U.card + 1 = m} → A) :=
  LinearMap.pi fun U =>
    if h : a ∈ U.1 then 0
    else ((-1 : ℤ) ^ z0) • LinearMap.proj (augIdx Z m a U h)

lemma apexL_apply (Z : Finset V) (m : ℕ) (a : V) (z0 : ℕ)
    (c : {S : Finset V // Z ⊆ S ∧ S.card = m} → A)
    (U : {U : Finset V // Z ⊆ U ∧ U.card + 1 = m}) :
    apexL (A := A) Z m a z0 c U =
      if h : a ∈ U.1 then 0 else ((-1 : ℤ) ^ z0) • c (augIdx Z m a U h) := by
  rw [apexL, LinearMap.pi_apply]
  by_cases h : a ∈ U.1
  · rw [dite_eq_left h, dite_eq_left h, LinearMap.zero_apply]
  · rw [dite_eq_right h, dite_eq_right h, LinearMap.smul_apply, LinearMap.proj_apply]

lemma apexL_apply_of_mem {Z : Finset V} {m : ℕ} {a : V} {z0 : ℕ}
    {c : {S : Finset V // Z ⊆ S ∧ S.card = m} → A}
    {U : {U : Finset V // Z ⊆ U ∧ U.card + 1 = m}} (h : a ∈ U.1) :
    apexL (A := A) Z m a z0 c U = 0 := by
  rw [apexL_apply, dite_eq_left h]

lemma apexL_apply_of_not_mem {Z : Finset V} {m : ℕ} {a : V} {z0 : ℕ}
    {c : {S : Finset V // Z ⊆ S ∧ S.card = m} → A}
    {U : {U : Finset V // Z ⊆ U ∧ U.card + 1 = m}} (h : a ∉ U.1) :
    apexL (A := A) Z m a z0 c U = ((-1 : ℤ) ^ z0) • c (augIdx Z m a U h) := by
  rw [apexL_apply, dite_eq_right h]

/-- Two subtype elements with the same underlying value have equal images. -/
lemma subtype_apply_eq {α : Type*} {p : α → Prop} {β : Type*} {c : {x // p x} → β}
    {S T : α} {hS : p S} {hT : p T} (h : S = T) : c ⟨S, hS⟩ = c ⟨T, hT⟩ :=
  congrArg c (Subtype.ext h)

/-! ## Elementary sign lemmas -/

lemma negOne_pow_mul_self (n : ℕ) : ((-1 : ℤ) ^ n) * ((-1 : ℤ) ^ n) = 1 := by
  rw [← pow_add]
  exact Even.neg_one_pow ⟨n, rfl⟩

lemma negOne_pow_smul_self {M : Type*} [AddCommGroup M] [Module ℤ M] (n : ℕ) (x : M) :
    ((-1 : ℤ) ^ n) • (((-1 : ℤ) ^ n) • x) = x := by
  rw [smul_smul, negOne_pow_mul_self, one_smul]

/-- For `T ⊇ Z` and `a` lying below every element of `Z`, the elements of `T` smaller than `a`
are exactly the elements of `Z` smaller than `a`. -/
lemma filter_lt_eq_of_lt_imp_mem {Z T : Finset V} {a : V}
    (hZT : Z ⊆ T) (hmin : ∀ x, x < a → x ∈ Z) :
    T.filter (fun x => x < a) = Z.filter (fun x => x < a) := by
  apply Finset.Subset.antisymm
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hmin x hx.2, hx.2⟩
  · intro x hx
    rw [Finset.mem_filter] at hx ⊢
    exact ⟨hZT hx.1, hx.2⟩

lemma card_filter_lt_eq_of_lt_imp_mem {Z T : Finset V} {a : V}
    (hZT : Z ⊆ T) (hmin : ∀ x, x < a → x ∈ Z) :
    (T.filter (fun x => x < a)).card = (Z.filter (fun x => x < a)).card := by
  rw [filter_lt_eq_of_lt_imp_mem hZT hmin]

lemma filter_insert_lt {T : Finset V} {a i : V} (hai : a < i) :
    (insert a T).filter (fun x => x < i) = insert a (T.filter (fun x => x < i)) := by
  rw [Finset.filter_insert, ite_eq_left hai]

lemma card_filter_lt_insert {T : Finset V} {a i : V} (haT : a ∉ T) (hai : a < i) :
    ((insert a T).filter (fun x => x < i)).card = (T.filter (fun x => x < i)).card + 1 := by
  rw [filter_insert_lt hai, Finset.card_insert_of_notMem]
  exact fun hmem => haT (Finset.mem_filter.mp hmem).1

/-! ## The summands of the two boundary sums -/

/-- Guarded form of the summand of the contraction boundary sum at a level-`m` index `T`. -/
noncomputable def summandG (Z : Finset V) (m : ℕ) (a : V) (z0 : ℕ)
    (c : {S : Finset V // Z ⊆ S ∧ S.card = m} → A)
    (T : {T : Finset V // Z ⊆ T ∧ T.card = m}) : V → A :=
  fun i => if h : i ∈ T.1 \ Z then
      ((-1 : ℤ) ^ ((T.1.filter (fun x => x < i)).card)) •
        apexL (A := A) Z m a z0 c (mkEraseIdx Z m T i h)
    else 0

/-- Guarded form of the summand of the cocycle boundary sum at a level-`(m+1)` index `T`. -/
noncomputable def summandH (Z : Finset V) (m : ℕ)
    (c : {S : Finset V // Z ⊆ S ∧ S.card = m} → A)
    (T : {T : Finset V // Z ⊆ T ∧ T.card = m + 1}) : V → A :=
  fun j => if h : j ∈ T.1 \ Z then
      ((-1 : ℤ) ^ ((T.1.filter (fun x => x < j)).card)) •
        c (mkEraseIdxH Z m T j h)
    else 0

lemma summandG_eq (Z : Finset V) (m : ℕ) (a : V) (z0 : ℕ)
    (c : {S : Finset V // Z ⊆ S ∧ S.card = m} → A)
    (T : {T : Finset V // Z ⊆ T ∧ T.card = m}) (i : V) (hi : i ∈ T.1 \ Z) :
    summandG (A := A) Z m a z0 c T i =
      ((-1 : ℤ) ^ ((T.1.filter (fun x => x < i)).card)) •
        apexL (A := A) Z m a z0 c (mkEraseIdx Z m T i hi) := by
  unfold summandG
  rw [dite_eq_left hi]

lemma summandH_eq (Z : Finset V) (m : ℕ)
    (c : {S : Finset V // Z ⊆ S ∧ S.card = m} → A)
    (T : {T : Finset V // Z ⊆ T ∧ T.card = m + 1}) (j : V) (hj : j ∈ T.1 \ Z) :
    summandH (A := A) Z m c T j =
      ((-1 : ℤ) ^ ((T.1.filter (fun x => x < j)).card)) •
        c (mkEraseIdxH Z m T j hj) := by
  unfold summandH
  rw [dite_eq_left hj]

end Work.DSCOH
