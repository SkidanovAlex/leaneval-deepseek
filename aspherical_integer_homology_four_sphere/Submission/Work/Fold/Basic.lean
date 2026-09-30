/-
# The fold map on `E4 = ℝ⁴`

This file starts the chapter `Work.Fold`: the coordinate-level `2^c`-fold of Euclidean space that
underlies the *fold charts* of the Davis/Tschantz hyperbolic piece `M̄`.

Conventions (fixed for the whole chapter):

* `E4 := EuclideanSpace ℝ (Fin 4)` — the chart model of every area of this project.
* `Sign c := Fin c → Bool` — the `2^c` sign vectors for the first `c` coordinates.
* `foldMap c hc x` is `(|x 0|, …, |x (c-1)|, x c, …, x 3)`: absolute values in the first `c`
  coordinates, the identity in the remaining `4 - c`.
* `orthant r` is the closed orthant `{x | rᵢ · xᵢ ≥ 0}` (the remaining coordinates unconstrained).
  The *positive* orthant `posOrthant c` is the one whose signs are all `+1`.
* `reflVec r` is the coordinate reflection `xᵢ ↦ rᵢ xᵢ` on the first `c` coordinates (the identity
  in the other coordinates). It is an involution, an isometry, and it maps the positive orthant onto
  `orthant r`.

Main facts proved here:

* `foldMap_reflVec` : `foldMap (reflVec r x) = foldMap x` (`foldMap` is invariant under the fold),
* `foldMap_eq_reflVec_of_mem_orthant` : on `orthant r`, `foldMap` is `reflVec r`,
* `foldMap_eq_foldMap_iff` : the fibres of `foldMap` are exactly the `reflVec`-orbits,
* `foldMap_preimage_eq_iUnion` : for `S ⊆ posOrthant c`, `foldMap ⁻¹' S = ⋃ r, reflVec r '' S`,
* `isOpen_foldMap_preimage` : that set is open if `S` is relatively open in `posOrthant c`.

These are the tools with which the *fold chart lemma* (`Work.Fold.FoldGlue`) glues `2^c` closed
pieces over the common coordinate hyperplanes.
-/
import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.Fold

open Set Function

/-- The chart model: `ℝ⁴` as a Euclidean space. -/
abbrev E4 := EuclideanSpace ℝ (Fin 4)

/-- Sign vectors of a `c`-fold: the `2^c` choices of a sign for each of the first `c` coordinates. -/
abbrev Sign (c : ℕ) := Fin c → Bool

/-- The first `c` coordinates of `Fin 4`, for `c ≤ 4`. -/
def emb {c : ℕ} (hc : c ≤ 4) (i : Fin c) : Fin 4 := ⟨i.1, lt_of_lt_of_le i.2 hc⟩

@[simp] lemma emb_apply {c : ℕ} (hc : c ≤ 4) (i : Fin c) : (emb hc i).1 = i.1 := rfl

lemma emb_injective {c : ℕ} (hc : c ≤ 4) : Function.Injective (emb hc) :=
  fun i j h => Fin.ext (by simpa using congrArg Fin.val h)

@[simp] lemma emb_mk {c : ℕ} (hc : c ≤ 4) (i : Fin 4) (h : i.1 < c) : emb hc ⟨i.1, h⟩ = i :=
  Fin.ext rfl

lemma emb_lt {c : ℕ} (hc : c ≤ 4) (i : Fin c) : (emb hc i).1 < c := i.2

/-- The all-`+1` sign vector. -/
def oneSign (c : ℕ) : Sign c := fun _ => true

/-- Coordinatewise product of sign vectors (the fold group operation). -/
def signVecMul {c : ℕ} (r s : Sign c) : Sign c := fun i => (r i == s i)

/-- Coordinatewise negation of a sign vector. -/
def signVecNeg {c : ℕ} (r : Sign c) : Sign c := fun i => !(r i)

/-- The real number `±1` attached to a sign bit. -/
def signVal {c : ℕ} (r : Sign c) (i : Fin c) : ℝ := if r i then 1 else -1

/-- Build an element of `E4` from its coordinates. -/
def e4Of (f : Fin 4 → ℝ) : E4 := WithLp.toLp 2 f

@[simp] lemma e4Of_apply (f : Fin 4 → ℝ) (i : Fin 4) : e4Of f i = f i := rfl

lemma e4_ext {x y : E4} (h : ∀ i, x i = y i) : x = y := PiLp.ext h

lemma e4_ext_iff {x y : E4} : x = y ↔ ∀ i, x i = y i :=
  ⟨fun h _ => by rw [h], e4_ext⟩

@[simp] lemma signVal_oneSign (c : ℕ) (i : Fin c) : signVal (oneSign c) i = 1 := rfl

@[simp] lemma signVal_signVecNeg {c : ℕ} (r : Sign c) (i : Fin c) :
    signVal (signVecNeg r) i = - signVal r i := by
  rw [signVal, signVal, signVecNeg]
  cases h : r i <;> simp

lemma signVal_signVecMul {c : ℕ} (r s : Sign c) (i : Fin c) :
    signVal r i * signVal s i = signVal (signVecMul r s) i := by
  rw [signVal, signVal, signVal, signVecMul]
  cases hr : r i <;> cases hs : s i <;> simp

lemma signVal_eq_one_or {c : ℕ} (r : Sign c) (i : Fin c) : signVal r i = 1 ∨ signVal r i = -1 := by
  rw [signVal]; split <;> simp

lemma signVal_ne_zero {c : ℕ} (r : Sign c) (i : Fin c) : signVal r i ≠ 0 := by
  rcases signVal_eq_one_or r i with h | h <;> rw [h] <;> norm_num

lemma signVal_mul_self {c : ℕ} (r : Sign c) (i : Fin c) (x : ℝ) :
    signVal r i * (signVal r i * x) = x := by
  rcases signVal_eq_one_or r i with h | h <;> rw [h] <;> ring

lemma abs_signVal {c : ℕ} (r : Sign c) (i : Fin c) : |signVal r i| = 1 := by
  rcases signVal_eq_one_or r i with h | h <;> rw [h] <;> norm_num

lemma mul_eq_abs_iff {s x : ℝ} (h : s = 1 ∨ s = -1) : s * x = |x| ↔ 0 ≤ s * x := by
  constructor
  · intro hx; rw [hx]; exact abs_nonneg x
  · intro hx
    rcases h with h1 | h1
    · rw [h1, one_mul] at hx ⊢; exact (abs_of_nonneg hx).symm
    · rw [h1] at hx ⊢; rw [abs_of_nonpos (by linarith)]; ring

lemma signVal_mul_eq_abs_iff {c : ℕ} (r : Sign c) (i : Fin c) (x : ℝ) :
    signVal r i * x = |x| ↔ 0 ≤ signVal r i * x :=
  mul_eq_abs_iff (signVal_eq_one_or r i)

lemma signVal_mul_pos_iff {c : ℕ} (r : Sign c) (i : Fin c) (x : ℝ) :
    0 < signVal r i * x ↔ (r i = true ∧ 0 < x) ∨ (r i = false ∧ x < 0) := by
  constructor
  · intro h
    by_cases hr : r i
    · exact Or.inl ⟨hr, by simpa [signVal, hr] using h⟩
    · exact Or.inr ⟨by simpa using hr, by simpa [signVal, hr] using h⟩
  · rintro (⟨hr, hx⟩ | ⟨hr, hx⟩)
    · simpa [signVal, hr] using hx
    · have h1 : signVal r i = -1 := by simp [signVal, hr]
      rw [h1]; linarith

/-! ### The coordinate reflection -/

/-- The coordinate reflection in the `c` coordinate hyperplanes. -/
def reflVec {c : ℕ} (r : Sign c) : E4 → E4 :=
  fun x => e4Of (fun i => if h : i.1 < c then signVal r ⟨i.1, h⟩ * x i else x i)

@[simp] lemma reflVec_apply {c : ℕ} (r : Sign c) (x : E4) (i : Fin 4) :
    reflVec r x i = if h : i.1 < c then signVal r ⟨i.1, h⟩ * x i else x i := rfl

lemma reflVec_apply_of_lt {c : ℕ} (r : Sign c) (x : E4) {i : Fin 4} (h : i.1 < c) :
    reflVec r x i = signVal r ⟨i.1, h⟩ * x i := by
  rw [reflVec_apply, dite_eq_left h]

lemma reflVec_apply_of_le {c : ℕ} (r : Sign c) (x : E4) {i : Fin 4} (h : c ≤ i.1) :
    reflVec r x i = x i := by
  rw [reflVec_apply, dite_eq_right (not_lt.mpr h)]

@[simp] lemma reflVec_oneSign (c : ℕ) (x : E4) : reflVec (oneSign c) x = x := by
  ext i
  by_cases h : i.1 < c
  · rw [reflVec_apply_of_lt (oneSign c) x h]; simp
  · rw [reflVec_apply_of_le (oneSign c) x (not_lt.mp h)]

lemma reflVec_involutive {c : ℕ} (r : Sign c) (x : E4) : reflVec r (reflVec r x) = x := by
  ext i
  by_cases h : i.1 < c
  · rw [reflVec_apply_of_lt r _ h, reflVec_apply_of_lt r x h, signVal_mul_self]
  · rw [reflVec_apply_of_le r _ (not_lt.mp h), reflVec_apply_of_le r x (not_lt.mp h)]

lemma reflVec_reflVec {c : ℕ} (r s : Sign c) (x : E4) :
    reflVec r (reflVec s x) = reflVec (signVecMul r s) x := by
  ext i
  by_cases h : i.1 < c
  · rw [reflVec_apply_of_lt r _ h, reflVec_apply_of_lt s x h,
      reflVec_apply_of_lt (signVecMul r s) x h, ← mul_assoc, signVal_signVecMul]
  · rw [reflVec_apply_of_le r _ (not_lt.mp h), reflVec_apply_of_le s x (not_lt.mp h),
      reflVec_apply_of_le (signVecMul r s) x (not_lt.mp h)]

lemma continuous_reflVec {c : ℕ} (r : Sign c) : Continuous (reflVec r) := by
  have hcont : Continuous fun y : (Fin 4 → ℝ) => (WithLp.toLp 2 y : E4) :=
    PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)
  refine hcont.comp ?_
  apply continuous_pi
  intro i
  by_cases h : i.1 < c
  · have hfun : (fun x : E4 => (if h' : i.1 < c then signVal r ⟨i.1, h'⟩ * x i else x i)) =
        fun x => signVal r ⟨i.1, h⟩ * x i := by
      funext x; rw [dite_eq_left h]
    rw [hfun]
    exact continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) i)
  · have hfun : (fun x : E4 => (if h' : i.1 < c then signVal r ⟨i.1, h'⟩ * x i else x i)) =
        fun x => x i := by
      funext x; rw [dite_eq_right h]
    rw [hfun]
    exact PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) i

lemma reflVec_injective {c : ℕ} (r : Sign c) : Function.Injective (reflVec r) :=
  fun x y h => by rw [← reflVec_involutive r x, h, reflVec_involutive r y]

lemma image_reflVec_eq_preimage {c : ℕ} (r : Sign c) (S : Set E4) : reflVec r '' S = reflVec r ⁻¹' S := by
  ext y
  constructor
  · rintro ⟨v, hv, rfl⟩
    rw [mem_preimage, reflVec_involutive]; exact hv
  · intro hy
    exact ⟨reflVec r y, by rwa [mem_preimage] at hy, reflVec_involutive r y⟩

/-- `reflVec r` is an open map: it is an involution of `E4`. -/
lemma isOpenMap_reflVec {c : ℕ} (r : Sign c) : IsOpenMap (reflVec r) := by
  intro V hV
  rw [image_reflVec_eq_preimage]
  exact hV.preimage (continuous_reflVec r)

/-! ### The closed orthants -/

/-- The closed orthant of signs `r`: `rᵢ xᵢ ≥ 0` for `i < c` (the other coordinates are free). -/
def orthant {c : ℕ} (r : Sign c) : Set E4 :=
  {x | ∀ (i : Fin 4) (h : i.1 < c), 0 ≤ signVal r ⟨i.1, h⟩ * x i}

/-- The positive closed orthant: `xᵢ ≥ 0` for `i < c`. -/
def posOrthant (c : ℕ) : Set E4 := orthant (oneSign c)

@[simp] lemma mem_orthant_iff {c : ℕ} {r : Sign c} {x : E4} :
    x ∈ orthant r ↔ ∀ (i : Fin 4) (h : i.1 < c), 0 ≤ signVal r ⟨i.1, h⟩ * x i := Iff.rfl

lemma mem_posOrthant_iff {c : ℕ} {x : E4} :
    x ∈ posOrthant c ↔ ∀ (i : Fin 4) (h : i.1 < c), 0 ≤ x i := by
  simp [posOrthant, orthant]

lemma mem_orthant_iff' {c : ℕ} (hc : c ≤ 4) {r : Sign c} {x : E4} :
    x ∈ orthant r ↔ ∀ i : Fin c, 0 ≤ signVal r i * x (emb hc i) := by
  constructor
  · intro hx i
    exact hx (emb hc i) i.2
  · intro hx i h
    exact hx ⟨i.1, h⟩

lemma reflVec_mem_posOrthant_iff {c : ℕ} (r : Sign c) (x : E4) :
    reflVec r x ∈ posOrthant c ↔ x ∈ orthant r := by
  rw [mem_posOrthant_iff, mem_orthant_iff]
  constructor
  · intro h i hi
    have := h i hi
    rwa [reflVec_apply_of_lt r x hi] at this
  · intro h i hi
    rw [reflVec_apply_of_lt r x hi]
    exact h i hi

lemma reflVec_mem_orthant_iff {c : ℕ} (r : Sign c) (x : E4) :
    reflVec r x ∈ orthant r ↔ x ∈ posOrthant c := by
  rw [mem_orthant_iff, mem_posOrthant_iff]
  constructor
  · intro h i hi
    have := h i hi
    rwa [reflVec_apply_of_lt r x hi, signVal_mul_self] at this
  · intro h i hi
    rw [reflVec_apply_of_lt r x hi, signVal_mul_self]
    exact h i hi

lemma reflVec_image_posOrthant {c : ℕ} (r : Sign c) : reflVec r '' posOrthant c = orthant r := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [reflVec_mem_orthant_iff]
  · intro hy
    exact ⟨reflVec r y, by rwa [reflVec_mem_posOrthant_iff], reflVec_involutive r y⟩

lemma reflVec_image_orthant {c : ℕ} (r : Sign c) : reflVec r '' orthant r = posOrthant c := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rwa [reflVec_mem_posOrthant_iff]
  · intro hy
    exact ⟨reflVec r y, by rwa [reflVec_mem_orthant_iff], reflVec_involutive r y⟩

/-! ### The fold map -/

/-- The fold map: absolute values in the first `c` coordinates, identity in the others. -/
def foldMap (c : ℕ) (_hc : c ≤ 4) : E4 → E4 :=
  fun x => e4Of (fun i => if i.1 < c then |x i| else x i)

@[simp] lemma foldMap_apply (c : ℕ) (hc : c ≤ 4) (x : E4) (i : Fin 4) :
    foldMap c hc x i = if i.1 < c then |x i| else x i := rfl

lemma foldMap_apply_of_lt {c : ℕ} (hc : c ≤ 4) (x : E4) {i : Fin 4} (h : i.1 < c) :
    foldMap c hc x i = |x i| := by rw [foldMap_apply, ite_eq_left h]

lemma foldMap_apply_of_le {c : ℕ} (hc : c ≤ 4) (x : E4) {i : Fin 4} (h : c ≤ i.1) :
    foldMap c hc x i = x i := by rw [foldMap_apply, ite_eq_right (not_lt.mpr h)]

lemma foldMap_mem_posOrthant {c : ℕ} (hc : c ≤ 4) (x : E4) : foldMap c hc x ∈ posOrthant c := by
  rw [mem_posOrthant_iff]
  intro i h
  rw [foldMap_apply_of_lt hc x h]
  exact abs_nonneg _

lemma continuous_foldMap (c : ℕ) (hc : c ≤ 4) : Continuous (foldMap c hc) := by
  have hcont : Continuous fun y : (Fin 4 → ℝ) => (WithLp.toLp 2 y : E4) :=
    PiLp.continuous_toLp 2 (fun _ : Fin 4 => ℝ)
  refine hcont.comp ?_
  apply continuous_pi
  intro i
  by_cases h : i.1 < c
  · have : (fun x : E4 => (if i.1 < c then |x i| else x i)) = fun x => |x i| := by
      funext x; rw [ite_eq_left h]
    rw [this]
    exact (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) i).abs
  · have : (fun x : E4 => (if i.1 < c then |x i| else x i)) = fun x => x i := by
      funext x; rw [ite_eq_right h]
    rw [this]
    exact PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) i

lemma foldMap_reflVec {c : ℕ} (hc : c ≤ 4) (r : Sign c) (x : E4) :
    foldMap c hc (reflVec r x) = foldMap c hc x := by
  ext i
  by_cases h : i.1 < c
  · rw [foldMap_apply_of_lt hc _ h, foldMap_apply_of_lt hc x h, reflVec_apply_of_lt r x h,
      abs_mul, abs_signVal, one_mul]
  · rw [foldMap_apply_of_le hc _ (not_lt.mp h), foldMap_apply_of_le hc x (not_lt.mp h),
      reflVec_apply_of_le r x (not_lt.mp h)]

lemma foldMap_eq_reflVec_of_mem_orthant {c : ℕ} (hc : c ≤ 4) {r : Sign c} {x : E4} (hx : x ∈ orthant r) :
    foldMap c hc x = reflVec r x := by
  ext i
  by_cases h : i.1 < c
  · have hxi : 0 ≤ signVal r ⟨i.1, h⟩ * x i := hx i h
    rw [foldMap_apply_of_lt hc x h, reflVec_apply_of_lt r x h,
      (signVal_mul_eq_abs_iff r ⟨i.1, h⟩ (x i)).mpr hxi]
  · rw [foldMap_apply_of_le hc x (not_lt.mp h), reflVec_apply_of_le r x (not_lt.mp h)]

lemma foldMap_eq_reflVec_iff {c : ℕ} (hc : c ≤ 4) (r : Sign c) (x : E4) :
    foldMap c hc x = reflVec r x ↔ x ∈ orthant r := by
  constructor
  · intro h
    rw [mem_orthant_iff]
    intro i hi
    have h1 := e4_ext_iff.mp h i
    rw [foldMap_apply_of_lt hc x hi, reflVec_apply_of_lt r x hi] at h1
    exact (signVal_mul_eq_abs_iff r ⟨i.1, hi⟩ (x i)).mp h1.symm
  · exact foldMap_eq_reflVec_of_mem_orthant hc

lemma foldMap_eq_of_mem_orthant {c : ℕ} (hc : c ≤ 4) {r : Sign c} {x y : E4}
    (hx : x ∈ orthant r) (hy : y ∈ orthant r) (h : foldMap c hc x = foldMap c hc y) : x = y := by
  have h' : reflVec r x = reflVec r y := by
    rw [← foldMap_eq_reflVec_of_mem_orthant hc hx, ← foldMap_eq_reflVec_of_mem_orthant hc hy]
    exact h
  calc x = reflVec r (reflVec r x) := (reflVec_involutive r x).symm
    _ = reflVec r (reflVec r y) := by rw [h']
    _ = y := reflVec_involutive r y

lemma foldMap_injOn_orthant {c : ℕ} (hc : c ≤ 4) (r : Sign c) : Set.InjOn (foldMap c hc) (orthant r) :=
  fun _ hx _ hy h => foldMap_eq_of_mem_orthant hc hx hy h

lemma foldMap_eq_self_of_mem_posOrthant {c : ℕ} (hc : c ≤ 4) {x : E4} (hx : x ∈ posOrthant c) :
    foldMap c hc x = x := by
  have := foldMap_eq_reflVec_of_mem_orthant hc hx
  rwa [reflVec_oneSign] at this

lemma foldMap_idem {c : ℕ} (hc : c ≤ 4) (x : E4) : foldMap c hc (foldMap c hc x) = foldMap c hc x :=
  foldMap_eq_self_of_mem_posOrthant hc (foldMap_mem_posOrthant hc x)

/-- The canonical sign vector of a point: the sign of `xᵢ`, with `+` on zeros. -/
def signOf (c : ℕ) (hc : c ≤ 4) (x : E4) : Sign c := fun i => decide (0 ≤ x (emb hc i))

@[simp] lemma signOf_apply (c : ℕ) (hc : c ≤ 4) (x : E4) (i : Fin c) :
    signOf c hc x i = decide (0 ≤ x (emb hc i)) := rfl

lemma reflVec_signOf_foldMap {c : ℕ} (hc : c ≤ 4) (x : E4) :
    reflVec (signOf c hc x) (foldMap c hc x) = x := by
  ext i
  by_cases h : i.1 < c
  · rw [reflVec_apply_of_lt _ _ h, foldMap_apply_of_lt hc x h]
    simp only [signOf_apply, emb_mk hc i h, signVal]
    by_cases hx : 0 ≤ x i
    · rw [decide_eq_true hx]; simp [abs_of_nonneg hx]
    · rw [decide_eq_false hx]; simp [abs_of_neg (lt_of_not_ge hx)]
  · rw [reflVec_apply_of_le _ _ (not_lt.mp h), foldMap_apply_of_le hc x (not_lt.mp h)]

lemma foldMap_eq_reflVec_signOf {c : ℕ} (hc : c ≤ 4) (x : E4) :
    foldMap c hc x = reflVec (signOf c hc x) x := by
  calc foldMap c hc x
      = reflVec (signOf c hc x) (reflVec (signOf c hc x) (foldMap c hc x)) :=
        (reflVec_involutive _ _).symm
    _ = reflVec (signOf c hc x) x := by rw [reflVec_signOf_foldMap hc x]

/-- The fibres of the fold map are exactly the reflection orbits. -/
theorem foldMap_eq_foldMap_iff {c : ℕ} (hc : c ≤ 4) (x y : E4) :
    foldMap c hc x = foldMap c hc y ↔ ∃ r : Sign c, y = reflVec r x := by
  constructor
  · intro h
    refine ⟨signVecMul (signOf c hc y) (signOf c hc x), ?_⟩
    calc y = reflVec (signOf c hc y) (foldMap c hc y) := (reflVec_signOf_foldMap hc y).symm
      _ = reflVec (signOf c hc y) (foldMap c hc x) := by rw [h]
      _ = reflVec (signOf c hc y) (reflVec (signOf c hc x) x) := by
            rw [foldMap_eq_reflVec_signOf hc x]
      _ = reflVec (signVecMul (signOf c hc y) (signOf c hc x)) x := reflVec_reflVec _ _ _
  · rintro ⟨r, rfl⟩
    exact (foldMap_reflVec hc r x).symm

/-- For `S` contained in the positive orthant, the preimage under the fold map is the union of the
reflected copies of `S`. -/
theorem foldMap_preimage_eq_iUnion {c : ℕ} (hc : c ≤ 4) {S : Set E4} (hS : S ⊆ posOrthant c) :
    foldMap c hc ⁻¹' S = ⋃ r : Sign c, reflVec r '' S := by
  ext x
  constructor
  · intro hx
    refine mem_iUnion.mpr ⟨signOf c hc x, ?_⟩
    exact ⟨foldMap c hc x, hx, reflVec_signOf_foldMap hc x⟩
  · intro hx
    rcases mem_iUnion.mp hx with ⟨r, s, hs, rfl⟩
    rw [mem_preimage, foldMap_reflVec, foldMap_eq_self_of_mem_posOrthant hc (hS hs)]
    exact hs

/-- `S` is open in the subspace `T`: `S = V ∩ T` for an open `V`. -/
def IsRelOpen {α : Type*} [TopologicalSpace α] (T S : Set α) : Prop :=
  ∃ V : Set α, IsOpen V ∧ S = V ∩ T

lemma IsRelOpen.subset {α : Type*} [TopologicalSpace α] {T S : Set α} (h : IsRelOpen T S) :
    S ⊆ T := by
  obtain ⟨V, -, rfl⟩ := h
  exact inter_subset_right

lemma isRelOpen_iff {α : Type*} [TopologicalSpace α] {T S : Set α} :
    IsRelOpen T S ↔ ∃ V : Set α, IsOpen V ∧ S = V ∩ T := Iff.rfl

lemma isRelOpen_posOrthant (c : ℕ) : IsRelOpen (posOrthant c) (posOrthant c) :=
  ⟨univ, isOpen_univ, by simp⟩

lemma IsRelOpen.reflVec_image {c : ℕ} {S : Set E4} (hS : IsRelOpen (posOrthant c) S)
    (r : Sign c) : IsRelOpen (orthant r) (reflVec r '' S) := by
  obtain ⟨V, hV, rfl⟩ := hS
  refine ⟨reflVec r '' V, isOpenMap_reflVec r V hV, ?_⟩
  rw [image_inter (reflVec_injective r), reflVec_image_posOrthant]

/-- **The target is open.** If `S` is relatively open in the positive orthant, then its full
preimage under the fold map is open in `E4`. -/
theorem isOpen_foldMap_preimage {c : ℕ} (hc : c ≤ 4) {S : Set E4} (hS : IsRelOpen (posOrthant c) S) :
    IsOpen (foldMap c hc ⁻¹' S) := by
  obtain ⟨V, hV, rfl⟩ := hS
  have h : foldMap c hc ⁻¹' (V ∩ posOrthant c) = foldMap c hc ⁻¹' V := by
    rw [preimage_inter, inter_eq_left]
    intro x hx
    rw [mem_preimage]
    exact foldMap_mem_posOrthant hc x
  rw [h]
  exact hV.preimage (continuous_foldMap c hc)

/-! ### Further API: closedness of the orthants, relative openness -/

lemma isClosed_orthant {c : ℕ} (r : Sign c) : IsClosed (orthant r) := by
  have h : orthant r = ⋂ (i : Fin 4) (h : i.1 < c), {x : E4 | 0 ≤ signVal r ⟨i.1, h⟩ * x i} := by
    ext x; simp [orthant]
  rw [h]
  refine isClosed_iInter fun i => isClosed_iInter fun h => ?_
  exact isClosed_le continuous_const
    (continuous_const.mul (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) i))

@[simp] lemma zero_mem_orthant {c : ℕ} (r : Sign c) : (0 : E4) ∈ orthant r := by
  intro i h; simp

@[simp] lemma foldMap_preimage_posOrthant {c : ℕ} (hc : c ≤ 4) :
    foldMap c hc ⁻¹' posOrthant c = univ := by
  ext x; simp [foldMap_mem_posOrthant hc x]

lemma foldMap_eq_self_iff_mem_posOrthant {c : ℕ} (hc : c ≤ 4) {x : E4} :
    foldMap c hc x = x ↔ x ∈ posOrthant c := by
  refine ⟨fun h => ?_, foldMap_eq_self_of_mem_posOrthant hc⟩
  rw [← h]; exact foldMap_mem_posOrthant hc x

lemma IsRelOpen.inter {α : Type*} [TopologicalSpace α] {T S S' : Set α}
    (hS : IsRelOpen T S) (hS' : IsRelOpen T S') : IsRelOpen T (S ∩ S') := by
  obtain ⟨V, hV, rfl⟩ := hS
  obtain ⟨V', hV', rfl⟩ := hS'
  refine ⟨V ∩ V', hV.inter hV', ?_⟩
  ext x
  simp only [mem_inter_iff]
  tauto

lemma IsRelOpen.iUnion {α ι : Type*} [TopologicalSpace α] {T : Set α} {S : ι → Set α}
    (hS : ∀ i, IsRelOpen T (S i)) : IsRelOpen T (⋃ i, S i) := by
  choose V hV hVS using hS
  refine ⟨⋃ i, V i, isOpen_iUnion hV, ?_⟩
  rw [iUnion_inter]
  exact iUnion_congr fun i => hVS i

lemma IsRelOpen.empty {α : Type*} [TopologicalSpace α] (T : Set α) : IsRelOpen T ∅ :=
  ⟨∅, isOpen_empty, by simp⟩

end Work.Fold
