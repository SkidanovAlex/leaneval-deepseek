import Mathlib
import Submission.Work.SSGRoute.free_lie_four_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Infrastructure for `freeLieFourFixedGeneration`

We work in `A = MonoidAlgebra (ZMod 2) (FreeMonoid X)`, the free associative `𝔽₂`-algebra on a
type `X` of letters, with the commutator `⁅a,b⁆ = a*b + b*a` (`Work.SSGRoute.brk`), the degree-four
left-nested commutator `brk4` and the subspaces `Wsub X` (spanned by the `brk4`s) and `Tsub X`.

Collected here:

* the bracket identities (`⁅a,b⁆ = ⁅b,a⁆`, additivity, Jacobi) and their degree-four consequences;
* the letter set `flg_letters w` of a word and its basic properties;
* the letter-set projection `flg_proj T` and its interaction with `Wsub` and with `σA`;
* the abbreviations `flgThetaSpan` (the "residual" span of the target statement) and `flgDelta`.
-/

namespace Work.SSGRoute

open scoped BigOperators

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {X : Type}

/-! ## 0. Characteristic two bookkeeping -/

theorem flg_add_self {A : Type*} [Ring A] [Algebra (ZMod 2) A] (t : A) : t + t = 0 := by
  have h : t + t = ((1 : ZMod 2) + 1) • t := by rw [add_smul, one_smul]
  rw [h, show ((1 : ZMod 2) + 1) = 0 from by decide, zero_smul]

/-! ## 0'. The two spans of the target statement -/

/-- The residual span `span{u * σA u + σA u * u : u ∈ Tsub X}`. -/
noncomputable abbrev flgThetaSpan (X : Type) (σA : MonoidAlgebra (ZMod 2) (FreeMonoid X) →ₗ[ZMod 2]
    MonoidAlgebra (ZMod 2) (FreeMonoid X)) : Submodule (ZMod 2)
    (MonoidAlgebra (ZMod 2) (FreeMonoid X)) :=
  Submodule.span (ZMod 2) (Set.range fun u :
      {u : MonoidAlgebra (ZMod 2) (FreeMonoid X) // u ∈ Tsub X} =>
    (u : MonoidAlgebra (ZMod 2) (FreeMonoid X)) * σA u + σA u * u)

/-- `(1 + σA)` applied to an element. -/
noncomputable abbrev flgDelta (X : Type) (σA : MonoidAlgebra (ZMod 2) (FreeMonoid X) →ₗ[ZMod 2]
    MonoidAlgebra (ZMod 2) (FreeMonoid X)) (v : MonoidAlgebra (ZMod 2) (FreeMonoid X)) :=
  v + σA v

/-- The image `(1 + σA)(Wsub X)`. -/
noncomputable abbrev flgDeltaW (X : Type) (σA : MonoidAlgebra (ZMod 2) (FreeMonoid X) →ₗ[ZMod 2]
    MonoidAlgebra (ZMod 2) (FreeMonoid X)) : Submodule (ZMod 2)
    (MonoidAlgebra (ZMod 2) (FreeMonoid X)) :=
  Submodule.map (σA + LinearMap.id) (Wsub X)

/-! ## 1. Bracket identities -/

section Bracket

theorem flg_brk_comm (X : Type) (a b : MonoidAlgebra (ZMod 2) (FreeMonoid X)) :
    brk X a b = brk X b a := by
  simp only [brk]; abel

theorem flg_brk_add_left (X : Type) (a b c : MonoidAlgebra (ZMod 2) (FreeMonoid X)) :
    brk X (a + b) c = brk X a c + brk X b c := by
  simp only [brk]; noncomm_ring

theorem flg_brk_add_right (X : Type) (a b c : MonoidAlgebra (ZMod 2) (FreeMonoid X)) :
    brk X a (b + c) = brk X a b + brk X a c := by
  simp only [brk]; noncomm_ring

theorem flg_brk_brk (X : Type) (a b c : MonoidAlgebra (ZMod 2) (FreeMonoid X)) :
    brk X a (brk X b c) = brk X (brk X a b) c + brk X (brk X a c) b := by
  simp only [brk]; noncomm_ring
  simp only [two_zsmul, flg_add_self, add_zero]

theorem flg_brk_brk' (X : Type) (a b c : MonoidAlgebra (ZMod 2) (FreeMonoid X)) :
    brk X (brk X a b) c = brk X (brk X a c) b + brk X (brk X b c) a := by
  rw [flg_brk_comm X (brk X a b) c, flg_brk_brk X c a b,
      flg_brk_comm X c a, flg_brk_comm X c b]

end Bracket

/-! ## 2. The degree-four bracket -/

/-- A letter viewed in the free algebra. -/
noncomputable abbrev flg_ltr (X : Type) (x : X) : MonoidAlgebra (ZMod 2) (FreeMonoid X) :=
  MonoidAlgebra.single (FreeMonoid.of x) 1

theorem flg_brk4_eq (X : Type) (x y z w : X) :
    brk4 X (x, y, z, w)
      = brk X (brk X (brk X (flg_ltr X x) (flg_ltr X y)) (flg_ltr X z)) (flg_ltr X w) := rfl

theorem flg_brk4_symm (X : Type) (x y z w : X) :
    brk4 X (x, y, z, w) = brk4 X (y, x, z, w) := by
  simp only [brk4]
  rw [flg_brk_comm X (flg_ltr X y) (flg_ltr X x)]

theorem flg_brk4_jacobi (X : Type) (x y z w : X) :
    brk4 X (x, y, z, w) = brk4 X (x, z, y, w) + brk4 X (y, z, x, w) := by
  simp only [brk4]
  rw [flg_brk_brk' X (flg_ltr X x) (flg_ltr X y) (flg_ltr X z), flg_brk_add_left]

theorem flg_brk4_outer (X : Type) (x y z w : X) :
    brk4 X (x, y, z, w) + brk4 X (x, y, w, z)
      = brk X (brk X (flg_ltr X x) (flg_ltr X y)) (brk X (flg_ltr X z) (flg_ltr X w)) := by
  simp only [brk4]
  rw [flg_brk_brk X (brk X (flg_ltr X x) (flg_ltr X y)) (flg_ltr X z) (flg_ltr X w)]

theorem flg_brk4_swapadd (X : Type) (x y z w : X) :
    brk4 X (x, y, z, w) + brk4 X (x, y, w, z)
      = brk4 X (z, w, x, y) + brk4 X (z, w, y, x) := by
  rw [flg_brk4_outer X x y z w, flg_brk4_outer X z w x y,
      flg_brk_comm X (brk X (flg_ltr X z) (flg_ltr X w))
        (brk X (flg_ltr X x) (flg_ltr X y))]

theorem flg_brk4_swap34 (X : Type) (x y z w : X) :
    brk4 X (x, y, z, w)
      = brk4 X (x, y, w, z) + brk4 X (z, w, x, y) + brk4 X (z, w, y, x) := by
  have h := flg_brk4_swapadd X x y z w
  calc brk4 X (x, y, z, w) = brk4 X (x, y, z, w) + 0 := by rw [add_zero]
    _ = brk4 X (x, y, z, w) + (brk4 X (x, y, w, z) + brk4 X (x, y, w, z)) := by
          rw [flg_add_self, add_zero]
    _ = (brk4 X (x, y, z, w) + brk4 X (x, y, w, z)) + brk4 X (x, y, w, z) := by abel
    _ = (brk4 X (z, w, x, y) + brk4 X (z, w, y, x)) + brk4 X (x, y, w, z) := by rw [h]
    _ = brk4 X (x, y, w, z) + brk4 X (z, w, x, y) + brk4 X (z, w, y, x) := by abel

/-- `σA` acts on `brk4` by acting on the letters. -/
theorem flg_sigmaA_brk4 (X : Type) (σ : X → X)
    (σA : MonoidAlgebra (ZMod 2) (FreeMonoid X) →ₗ[ZMod 2]
      MonoidAlgebra (ZMod 2) (FreeMonoid X))
    (hmul : ∀ a b, σA (a * b) = σA a * σA b) (hone : σA 1 = 1)
    (hgen : ∀ x, σA (MonoidAlgebra.single (FreeMonoid.of x) 1)
      = MonoidAlgebra.single (FreeMonoid.of (σ x)) 1) (x y z w : X) :
    σA (brk4 X (x, y, z, w)) = brk4 X (σ x, σ y, σ z, σ w) := by
  simp only [brk4, brk, map_add, hmul, hgen]

/-! ## 3. Letter sets -/

/-- The set of letters occurring in a word. -/
def flg_letters [DecidableEq X] (w : FreeMonoid X) : Finset X := w.toList.toFinset

@[simp] theorem flg_letters_one [DecidableEq X] :
    flg_letters (1 : FreeMonoid X) = ∅ := by
  simp [flg_letters]

@[simp] theorem flg_letters_of [DecidableEq X] (x : X) :
    flg_letters (FreeMonoid.of x) = {x} := by
  simp [flg_letters]

theorem flg_letters_mul [DecidableEq X] (u v : FreeMonoid X) :
    flg_letters (u * v) = flg_letters u ∪ flg_letters v := by
  simp [flg_letters, FreeMonoid.toList_mul]

theorem flg_letters_le_length [DecidableEq X] (w : FreeMonoid X) :
    (flg_letters w).card ≤ w.toList.length := by
  simpa [flg_letters] using List.toFinset_card_le w.toList

theorem flg_letters_map {X Y : Type} [DecidableEq X] [DecidableEq Y] (f : X → Y)
    (w : FreeMonoid X) :
    flg_letters (FreeMonoid.map f w) = (flg_letters w).image f := by
  induction w using FreeMonoid.recOn with
  | one => simp [flg_letters]
  | of_mul x w ih =>
      rw [map_mul (FreeMonoid.map f) (FreeMonoid.of x) w, FreeMonoid.map_of,
        flg_letters_mul, flg_letters_of, flg_letters_mul, flg_letters_of, ih,
        Finset.image_union, Finset.image_singleton]

/-- The letter set of a quadruple of letters. -/
def flg_letters4 [DecidableEq X] (t : X × X × X × X) : Finset X :=
  (({t.1} ∪ {t.2.1}) ∪ {t.2.2.1}) ∪ {t.2.2.2}

theorem flg_letters4_card_le [DecidableEq X] (t : X × X × X × X) :
    (flg_letters4 t).card ≤ 4 := by
  have hsub : flg_letters4 t ≤ ([t.1, t.2.1, t.2.2.1, t.2.2.2] : List X).toFinset := by
    intro x
    simp only [flg_letters4, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
      List.mem_toFinset, List.mem_cons]
    try tauto
  calc (flg_letters4 t).card
      ≤ ([t.1, t.2.1, t.2.2.1, t.2.2.2] : List X).toFinset.card := Finset.card_le_card hsub
    _ ≤ ([t.1, t.2.1, t.2.2.1, t.2.2.2] : List X).length := List.toFinset_card_le _
    _ = 4 := rfl

/-- The eight-monomial expansion of `brk4`. -/
theorem flg_brk4_expand (X : Type) (x0 x1 x2 x3 : X) :
    brk4 X (x0, x1, x2, x3) =
      MonoidAlgebra.single
          (FreeMonoid.of x0 * FreeMonoid.of x1 * FreeMonoid.of x2 * FreeMonoid.of x3)
          (1 : ZMod 2)
      + MonoidAlgebra.single
          (FreeMonoid.of x1 * FreeMonoid.of x0 * FreeMonoid.of x2 * FreeMonoid.of x3) 1
      + MonoidAlgebra.single
          (FreeMonoid.of x2 * FreeMonoid.of x0 * FreeMonoid.of x1 * FreeMonoid.of x3) 1
      + MonoidAlgebra.single
          (FreeMonoid.of x2 * FreeMonoid.of x1 * FreeMonoid.of x0 * FreeMonoid.of x3) 1
      + MonoidAlgebra.single
          (FreeMonoid.of x3 * FreeMonoid.of x0 * FreeMonoid.of x1 * FreeMonoid.of x2) 1
      + MonoidAlgebra.single
          (FreeMonoid.of x3 * FreeMonoid.of x1 * FreeMonoid.of x0 * FreeMonoid.of x2) 1
      + MonoidAlgebra.single
          (FreeMonoid.of x3 * FreeMonoid.of x2 * FreeMonoid.of x0 * FreeMonoid.of x1) 1
      + MonoidAlgebra.single
          (FreeMonoid.of x3 * FreeMonoid.of x2 * FreeMonoid.of x1 * FreeMonoid.of x0) 1 := by
  simp only [brk4, brk, MonoidAlgebra.single_mul_single, mul_one, add_mul, mul_add]
  abel

section WordLetters

variable [DecidableEq X]

theorem flg_letters_w1 (t : X × X × X × X) :
    flg_letters (FreeMonoid.of t.1 * FreeMonoid.of t.2.1 * FreeMonoid.of t.2.2.1
      * FreeMonoid.of t.2.2.2) = flg_letters4 t := by
  ext x
  simp only [flg_letters4, flg_letters_mul, flg_letters_of, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  try tauto

theorem flg_letters_w2 (t : X × X × X × X) :
    flg_letters (FreeMonoid.of t.2.1 * FreeMonoid.of t.1 * FreeMonoid.of t.2.2.1
      * FreeMonoid.of t.2.2.2) = flg_letters4 t := by
  ext x
  simp only [flg_letters4, flg_letters_mul, flg_letters_of, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  try tauto

theorem flg_letters_w3 (t : X × X × X × X) :
    flg_letters (FreeMonoid.of t.2.2.1 * FreeMonoid.of t.1 * FreeMonoid.of t.2.1
      * FreeMonoid.of t.2.2.2) = flg_letters4 t := by
  ext x
  simp only [flg_letters4, flg_letters_mul, flg_letters_of, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  try tauto

theorem flg_letters_w4 (t : X × X × X × X) :
    flg_letters (FreeMonoid.of t.2.2.1 * FreeMonoid.of t.2.1 * FreeMonoid.of t.1
      * FreeMonoid.of t.2.2.2) = flg_letters4 t := by
  ext x
  simp only [flg_letters4, flg_letters_mul, flg_letters_of, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  try tauto

theorem flg_letters_w5 (t : X × X × X × X) :
    flg_letters (FreeMonoid.of t.2.2.2 * FreeMonoid.of t.1 * FreeMonoid.of t.2.1
      * FreeMonoid.of t.2.2.1) = flg_letters4 t := by
  ext x
  simp only [flg_letters4, flg_letters_mul, flg_letters_of, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  try tauto

theorem flg_letters_w6 (t : X × X × X × X) :
    flg_letters (FreeMonoid.of t.2.2.2 * FreeMonoid.of t.2.1 * FreeMonoid.of t.1
      * FreeMonoid.of t.2.2.1) = flg_letters4 t := by
  ext x
  simp only [flg_letters4, flg_letters_mul, flg_letters_of, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  try tauto

theorem flg_letters_w7 (t : X × X × X × X) :
    flg_letters (FreeMonoid.of t.2.2.2 * FreeMonoid.of t.2.2.1 * FreeMonoid.of t.1
      * FreeMonoid.of t.2.1) = flg_letters4 t := by
  ext x
  simp only [flg_letters4, flg_letters_mul, flg_letters_of, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  try tauto

theorem flg_letters_w8 (t : X × X × X × X) :
    flg_letters (FreeMonoid.of t.2.2.2 * FreeMonoid.of t.2.2.1 * FreeMonoid.of t.2.1
      * FreeMonoid.of t.1) = flg_letters4 t := by
  ext x
  simp only [flg_letters4, flg_letters_mul, flg_letters_of, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton]
  try tauto

/-- If the letter set of `w` is not that of `t`, then the coefficient of `w` in `brk4 t` vanishes. -/
theorem flg_brk4_coeff_eq_zero (X : Type) [DecidableEq X] (t : X × X × X × X) (w : FreeMonoid X)
    (h : flg_letters w ≠ flg_letters4 t) : (brk4 X t).coeff w = 0 := by
  rw [flg_brk4_expand X t.1 t.2.1 t.2.2.1 t.2.2.2]
  simp only [MonoidAlgebra.coeff_add, Finsupp.add_apply, MonoidAlgebra.coeff_single]
  rw [Finsupp.single_eq_of_ne (show w ≠ _ from fun hw => h (by rw [hw, flg_letters_w1 t])),
      Finsupp.single_eq_of_ne (show w ≠ _ from fun hw => h (by rw [hw, flg_letters_w2 t])),
      Finsupp.single_eq_of_ne (show w ≠ _ from fun hw => h (by rw [hw, flg_letters_w3 t])),
      Finsupp.single_eq_of_ne (show w ≠ _ from fun hw => h (by rw [hw, flg_letters_w4 t])),
      Finsupp.single_eq_of_ne (show w ≠ _ from fun hw => h (by rw [hw, flg_letters_w5 t])),
      Finsupp.single_eq_of_ne (show w ≠ _ from fun hw => h (by rw [hw, flg_letters_w6 t])),
      Finsupp.single_eq_of_ne (show w ≠ _ from fun hw => h (by rw [hw, flg_letters_w7 t])),
      Finsupp.single_eq_of_ne (show w ≠ _ from fun hw => h (by rw [hw, flg_letters_w8 t]))]
  simp

/-- The words of the support of `brk4` have the same letter set. -/
theorem flg_brk4_letters (X : Type) [DecidableEq X] (t : X × X × X × X) (w : FreeMonoid X)
    (h : (brk4 X t).coeff w ≠ 0) : flg_letters w = flg_letters4 t :=
  by_contra fun hc => h (flg_brk4_coeff_eq_zero X t w hc)

end WordLetters

/-! ## 4. Elements of `Wsub` are supported on words with at most four letters -/

section Len4

variable [DecidableEq X]

noncomputable def flg_len4Sub (X : Type) [DecidableEq X] :
    Submodule (ZMod 2) (MonoidAlgebra (ZMod 2) (FreeMonoid X)) where
  carrier := {v | ∀ w : FreeMonoid X, v.coeff w ≠ 0 → (flg_letters w).card ≤ 4}
  zero_mem' := by intro w hw; exact absurd rfl hw
  add_mem' := by
    intro a b ha hb w hw
    rw [MonoidAlgebra.coeff_add, Finsupp.add_apply] at hw
    by_cases h : a.coeff w = 0
    · rw [h, zero_add] at hw; exact hb w hw
    · exact ha w h
  smul_mem' := by
    intro c a ha w hw
    rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply] at hw
    by_cases h : c = 0
    · rw [h, zero_smul] at hw; exact absurd rfl hw
    · exact ha w (fun h0 => hw (by rw [h0, smul_zero]))

theorem flg_Wsub_letters_le {v : MonoidAlgebra (ZMod 2) (FreeMonoid X)} (hv : v ∈ Wsub X)
    {w : FreeMonoid X} (hw : v.coeff w ≠ 0) : (flg_letters w).card ≤ 4 := by
  have hle : Wsub X ≤ flg_len4Sub X := by
    rw [Wsub]
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨t, rfl⟩
    exact fun w hw => by rw [flg_brk4_letters X t w hw]; exact flg_letters4_card_le t
  exact hle hv w hw

end Len4

/-! ## 5. The letter-set projection -/

section Proj

variable [DecidableEq X]

/-- Projection onto the words whose letter set is exactly `T`. -/
noncomputable def flg_proj (X : Type) [DecidableEq X] (T : Finset X) :
    MonoidAlgebra (ZMod 2) (FreeMonoid X) →ₗ[ZMod 2] MonoidAlgebra (ZMod 2) (FreeMonoid X) where
  toFun v := MonoidAlgebra.ofCoeff
    (Finsupp.filter (fun w : FreeMonoid X => flg_letters w = T) v.coeff)
  map_add' a b := by
    ext w
    simp only [MonoidAlgebra.coeff_add, Finsupp.filter_apply, Finsupp.add_apply]
    by_cases h : flg_letters w = T <;> simp [h]
  map_smul' c a := by
    ext w
    simp only [MonoidAlgebra.coeff_smul, Finsupp.filter_apply, Finsupp.smul_apply,
      RingHom.id_apply]
    by_cases h : flg_letters w = T <;> simp [h]

theorem flg_proj_apply (T : Finset X) (v : MonoidAlgebra (ZMod 2) (FreeMonoid X))
    (w : FreeMonoid X) :
    (flg_proj X T v).coeff w = if flg_letters w = T then v.coeff w else 0 := rfl

theorem flg_proj_coeff_brk4 (T : Finset X) (t : X × X × X × X) (w : FreeMonoid X) :
    (flg_proj X T (brk4 X t)).coeff w
      = if flg_letters4 t = T then (brk4 X t).coeff w else 0 := by
  rw [flg_proj_apply]
  by_cases hc : (brk4 X t).coeff w = 0
  · rw [hc]; by_cases h : flg_letters4 t = T <;> simp [h]
  · rw [flg_brk4_letters X t w hc]

theorem flg_proj_brk4 (T : Finset X) (t : X × X × X × X) :
    flg_proj X T (brk4 X t) = if flg_letters4 t = T then brk4 X t else 0 := by
  by_cases h : flg_letters4 t = T
  · rw [if_pos h]; ext w; rw [flg_proj_coeff_brk4, if_pos h]
  · rw [if_neg h]; ext w; rw [flg_proj_coeff_brk4, if_neg h]; simp

theorem flg_proj_idem (T : Finset X) (v : MonoidAlgebra (ZMod 2) (FreeMonoid X)) :
    flg_proj X T (flg_proj X T v) = flg_proj X T v := by
  ext w
  rw [flg_proj_apply, flg_proj_apply]
  by_cases h : flg_letters w = T <;> simp [h]

theorem flg_proj_mem_Wsub (T : Finset X) {v : MonoidAlgebra (ZMod 2) (FreeMonoid X)}
    (hv : v ∈ Wsub X) : flg_proj X T v ∈ Wsub X := by
  rw [Wsub] at hv ⊢
  refine Submodule.span_induction (p := fun v _ => flg_proj X T v ∈ Submodule.span (ZMod 2)
      (Set.range (brk4 X))) ?_ ?_ ?_ ?_ hv
  · rintro _ ⟨t, rfl⟩
    rw [flg_proj_brk4]
    split
    · exact Submodule.subset_span ⟨t, rfl⟩
    · exact Submodule.zero_mem _
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha; rw [map_smul]; exact Submodule.smul_mem _ c ha

theorem flg_proj_support (T : Finset X) (v : MonoidAlgebra (ZMod 2) (FreeMonoid X))
    {w : FreeMonoid X} (hw : (flg_proj X T v).coeff w ≠ 0) : flg_letters w = T := by
  rw [flg_proj_apply] at hw
  split at hw
  · assumption
  · exact absurd rfl hw

theorem flg_proj_sum (v : MonoidAlgebra (ZMod 2) (FreeMonoid X)) (s : Finset (Finset X))
    (h : ∀ w : FreeMonoid X, v.coeff w ≠ 0 → flg_letters w ∈ s) :
    ∑ T ∈ s, flg_proj X T v = v := by
  ext w
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp only [flg_proj_apply]
  rw [Finset.sum_ite_eq (s := s) (a := flg_letters w) (b := fun _ => v.coeff w)]
  by_cases hw : v.coeff w = 0
  · rw [hw]; by_cases h2 : flg_letters w ∈ s <;> simp [h2]
  · rw [if_pos (h w hw)]

end Proj

/-! ## 6. `σA` commutes with the letter-set projection -/

section SigmaProj

variable [DecidableEq X]

theorem flg_letters_image_eq (σ : X ≃ X) (w : FreeMonoid X) (T : Finset X) :
    flg_letters (FreeMonoid.map (fun x => σ x) w) = T.image σ ↔ flg_letters w = T := by
  rw [flg_letters_map (fun x => σ x) w]
  constructor
  · intro h
    have h2 := congrArg (Finset.image (fun x => σ.symm x)) h
    rw [Finset.image_image, Finset.image_image,
        show (fun x => σ.symm x) ∘ (fun x => σ x) = id from funext (fun x => σ.symm_apply_apply x),
        Finset.image_id] at h2
    simpa using h2
  · intro h; rw [h]

theorem flg_proj_single (T : Finset X) (w : FreeMonoid X) (c : ZMod 2) :
    flg_proj X T (MonoidAlgebra.single w c)
      = if flg_letters w = T then MonoidAlgebra.single w c else 0 := by
  show MonoidAlgebra.ofCoeff (Finsupp.filter (fun u : FreeMonoid X => flg_letters u = T)
      (Finsupp.single w c)) = if flg_letters w = T then MonoidAlgebra.single w c else 0
  by_cases hw : flg_letters w = T
  · rw [if_pos hw,
      Finsupp.filter_single_of_pos (p := fun u : FreeMonoid X => flg_letters u = T) hw]
    rfl
  · rw [if_neg hw,
      Finsupp.filter_single_of_neg (p := fun u : FreeMonoid X => flg_letters u = T) hw]
    rfl

theorem flg_sigmaA_proj (σ : X ≃ X)
    (σA : MonoidAlgebra (ZMod 2) (FreeMonoid X) →ₗ[ZMod 2]
      MonoidAlgebra (ZMod 2) (FreeMonoid X))
    (hmul : ∀ a b, σA (a * b) = σA a * σA b) (hone : σA 1 = 1)
    (hgen : ∀ y, σA (MonoidAlgebra.single (FreeMonoid.of y) 1)
      = MonoidAlgebra.single (FreeMonoid.of (σ y)) 1) (T : Finset X)
    (v : MonoidAlgebra (ZMod 2) (FreeMonoid X)) :
    σA (flg_proj X T v) = flg_proj X (T.image σ) (σA v) := by
  refine MonoidAlgebra.induction_on (motive := fun v =>
    σA (flg_proj X T v) = flg_proj X (T.image σ) (σA v)) v ?_ ?_ ?_
  · intro m
    simp only [MonoidAlgebra.of_apply]
    rw [flg_proj_single]
    rw [sigmaA_single X σ σA hmul hone hgen m, flg_proj_single]
    by_cases h : flg_letters m = T
    · rw [if_pos h, if_pos ((flg_letters_image_eq σ m T).mpr h)]
      exact sigmaA_single X σ σA hmul hone hgen m
    · rw [if_neg h, if_neg (fun hc => h ((flg_letters_image_eq σ m T).mp hc)), map_zero]
  · intro a b ha hb
    simp only [map_add]
    rw [ha, hb]
  · intro c a ha
    simp only [map_smul, RingHom.id_apply]
    rw [ha]

theorem flg_image_image (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x) (T : Finset X) :
    (T.image σ).image σ = T := by
  rw [Finset.image_image, show (⇑σ ∘ ⇑σ) = id from funext hσ, Finset.image_id]

theorem flg_image_eq_self (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x) {T : Finset X}
    (hT : ∀ x ∈ T, σ x ∈ T) : T.image σ = T := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact hT y hy
  · intro x hx
    exact Finset.mem_image.mpr ⟨σ x, hT x hx, hσ x⟩

/-- If `T` is `σ`-stable, then `flg_proj T` commutes with `σA`. -/
theorem flg_sigmaA_proj_stable (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x)
    (σA : MonoidAlgebra (ZMod 2) (FreeMonoid X) →ₗ[ZMod 2]
      MonoidAlgebra (ZMod 2) (FreeMonoid X))
    (hmul : ∀ a b, σA (a * b) = σA a * σA b) (hone : σA 1 = 1)
    (hgen : ∀ y, σA (MonoidAlgebra.single (FreeMonoid.of y) 1)
      = MonoidAlgebra.single (FreeMonoid.of (σ y)) 1) {T : Finset X}
    (hT : ∀ x ∈ T, σ x ∈ T) (v : MonoidAlgebra (ZMod 2) (FreeMonoid X)) :
    σA (flg_proj X T v) = flg_proj X T (σA v) := by
  rw [flg_sigmaA_proj (X := X) σ σA hmul hone hgen, flg_image_eq_self σ hσ hT]

end SigmaProj

/-! ## 7. The "odd part" decomposition -/

section OddPart

variable [DecidableEq X]

/-- **The odd part of a `σ`-fixed element lies in `(1 + σA)Wsub`.**

If `s` is a `σ`-invariant finite family of letter sets none of which is `σ`-stable, and `v ∈ Wsub`
is `σ`-fixed, then the sum of the projections of `v` onto the letter sets of `s` is of the form
`u + σA u` with `u ∈ Wsub`. -/
theorem flg_odd_sum_delta (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x)
    (σA : MonoidAlgebra (ZMod 2) (FreeMonoid X) →ₗ[ZMod 2]
      MonoidAlgebra (ZMod 2) (FreeMonoid X))
    (hmul : ∀ a b, σA (a * b) = σA a * σA b) (hone : σA 1 = 1)
    (hgen : ∀ y, σA (MonoidAlgebra.single (FreeMonoid.of y) 1)
      = MonoidAlgebra.single (FreeMonoid.of (σ y)) 1)
    (v : MonoidAlgebra (ZMod 2) (FreeMonoid X)) (hv : v ∈ Wsub X) (hvfix : σA v = v)
    (s : Finset (Finset X)) (hsinv : ∀ T ∈ s, T.image σ ∈ s)
    (hodd : ∀ T ∈ s, ¬ (∀ x ∈ T, σ x ∈ T)) :
    ∃ u ∈ Wsub X, (∑ T ∈ s, flg_proj X T v) = u + σA u := by
  suffices H : ∀ n, ∀ s : Finset (Finset X), s.card = n → (∀ T ∈ s, T.image σ ∈ s) →
      (∀ T ∈ s, ¬ (∀ x ∈ T, σ x ∈ T)) →
      ∃ u ∈ Wsub X, (∑ T ∈ s, flg_proj X T v) = u + σA u by
    exact H s.card s rfl hsinv hodd
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro s hcard hsinv hodd
    rcases s.eq_empty_or_nonempty with h | ⟨T0, hT0⟩
    · refine ⟨0, Submodule.zero_mem _, ?_⟩
      rw [h]; simp
    · set T1 : Finset X := T0.image σ with hT1def
      have hT1mem : T1 ∈ s := hsinv T0 hT0
      have hne : T1 ≠ T0 := by
        intro hc
        refine hodd T0 hT0 (fun x hx => ?_)
        rw [← hc]; exact Finset.mem_image_of_mem σ hx
      set s' : Finset (Finset X) := (s.erase T0).erase T1 with hs'def
      have hs'T1 : T1 ∈ s.erase T0 := Finset.mem_erase.mpr ⟨hne, hT1mem⟩
      have hcard' : s'.card < n := by
        have h1 : (s.erase T0).card < s.card := Finset.card_erase_lt_of_mem hT0
        have h2 : s'.card < (s.erase T0).card := Finset.card_erase_lt_of_mem hs'T1
        omega
      have hsinv' : ∀ T ∈ s', T.image σ ∈ s' := by
        intro T hT
        have hTs : T ∈ s := (Finset.mem_erase.mp (Finset.mem_erase.mp hT).2).2
        have hTne1 : T ≠ T1 := (Finset.mem_erase.mp hT).1
        have hTne0 : T ≠ T0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hT).2).1
        have hTin := hsinv T hTs
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hTin⟩⟩
        · intro hc
          have h2 : T = T0 := by
            calc T = (T.image σ).image σ := (flg_image_image σ hσ T).symm
              _ = T1.image σ := by rw [hc]
              _ = T0 := by rw [hT1def, flg_image_image σ hσ T0]
          exact hTne0 h2
        · intro hc
          have h2 : T = T1 := by
            calc T = (T.image σ).image σ := (flg_image_image σ hσ T).symm
              _ = T0.image σ := by rw [hc]
              _ = T1 := by rw [hT1def]
          exact hTne1 h2
      have hodd' : ∀ T ∈ s', ¬ (∀ x ∈ T, σ x ∈ T) :=
        fun T hT => hodd T (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hT))
      obtain ⟨u', hu', hu'eq⟩ := ih s'.card hcard' s' rfl hsinv' hodd'
      have hsig : σA (flg_proj X T0 v) = flg_proj X T1 v := by
        rw [hT1def, flg_sigmaA_proj (X := X) σ σA hmul hone hgen, hvfix]
      refine ⟨flg_proj X T0 v + u', Submodule.add_mem _ (flg_proj_mem_Wsub T0 hv) hu', ?_⟩
      have hsum : (∑ T ∈ s, flg_proj X T v)
          = flg_proj X T0 v + flg_proj X T1 v + ∑ T ∈ s', flg_proj X T v := by
        have h1 := Finset.sum_erase_add s (fun T => flg_proj X T v) hT0
        have h2 := Finset.sum_erase_add (s.erase T0) (fun T => flg_proj X T v) hs'T1
        rw [← h1, ← h2]
        simp only [hs'def]
        abel
      rw [hsum, hu'eq, map_add, hsig]
      abel

end OddPart

/-! ## 8. The support of a `σA`-fixed element, and `σ`-stable letter sets -/

section Support

variable [DecidableEq X]

/-- The letterwise map on words is injective. -/
theorem flg_map_injective (σ : X ≃ X) {m w : FreeMonoid X}
    (h : FreeMonoid.map (fun x => σ x) m = FreeMonoid.map (fun x => σ x) w) : m = w :=
  FreeMonoid.toList.injective <| (List.map_injective_iff.mpr σ.injective) <| by
    have hh := congrArg FreeMonoid.toList h
    rwa [FreeMonoid.toList_map, FreeMonoid.toList_map] at hh

/-- `σA` is the letterwise map on the monomial basis, hence moves the support accordingly. -/
theorem flg_sigmaA_coeff (σ : X ≃ X)
    (σA : MonoidAlgebra (ZMod 2) (FreeMonoid X) →ₗ[ZMod 2]
      MonoidAlgebra (ZMod 2) (FreeMonoid X))
    (hmul : ∀ a b, σA (a * b) = σA a * σA b) (hone : σA 1 = 1)
    (hgen : ∀ y, σA (MonoidAlgebra.single (FreeMonoid.of y) 1)
      = MonoidAlgebra.single (FreeMonoid.of (σ y)) 1)
    (v : MonoidAlgebra (ZMod 2) (FreeMonoid X)) (w : FreeMonoid X) :
    (σA v).coeff (FreeMonoid.map (fun x => σ x) w) = v.coeff w := by
  have key : ∀ v : MonoidAlgebra (ZMod 2) (FreeMonoid X), ∀ w : FreeMonoid X,
      (σA v).coeff (FreeMonoid.map (fun x => σ x) w) = v.coeff w := by
    intro v
    refine MonoidAlgebra.induction_on (motive := fun v =>
      ∀ w : FreeMonoid X, (σA v).coeff (FreeMonoid.map (fun x => σ x) w) = v.coeff w) v ?_ ?_ ?_
    · intro m w
      simp only [MonoidAlgebra.of_apply]
      rw [sigmaA_single X σ σA hmul hone hgen m, MonoidAlgebra.coeff_single,
        MonoidAlgebra.coeff_single]
      by_cases h : m = w
      · subst h; rw [Finsupp.single_eq_same, Finsupp.single_eq_same]
      · have h2 : FreeMonoid.map (fun x => σ x) m ≠ FreeMonoid.map (fun x => σ x) w :=
          fun hc => h (flg_map_injective σ hc)
        rw [Finsupp.single_eq_of_ne (Ne.symm h2), Finsupp.single_eq_of_ne (Ne.symm h)]
    · intro a b ha hb w
      simp only [map_add, MonoidAlgebra.coeff_add, Finsupp.add_apply, ha, hb]
    · intro c a ha w
      simp only [map_smul, MonoidAlgebra.coeff_smul, Finsupp.smul_apply, ha]
  exact key v w

/-- A support word of an element of `Wsub` has the letter set of some quadruple. -/
theorem flg_Wsub_letters4 {v : MonoidAlgebra (ZMod 2) (FreeMonoid X)} (hv : v ∈ Wsub X)
    {w : FreeMonoid X} (hw : v.coeff w ≠ 0) :
    ∃ t : X × X × X × X, flg_letters w = flg_letters4 t := by
  rw [Wsub] at hv
  refine Submodule.span_induction
    (p := fun v _ => ∀ w : FreeMonoid X, v.coeff w ≠ 0 →
      ∃ t : X × X × X × X, flg_letters w = flg_letters4 t) ?_ ?_ ?_ ?_ hv w hw
  · rintro _ ⟨t, rfl⟩ w hw
    exact ⟨t, flg_brk4_letters X t w hw⟩
  · intro w hw; exact absurd rfl hw
  · intro a b _ _ ha hb w hw
    rw [MonoidAlgebra.coeff_add, Finsupp.add_apply] at hw
    by_cases h : a.coeff w = 0
    · rw [h, zero_add] at hw; exact hb w hw
    · exact ha w h
  · intro c a _ ha w hw
    rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply] at hw
    by_cases h : c = 0
    · rw [h, zero_smul] at hw; exact absurd rfl hw
    · exact ha w (fun h0 => hw (by rw [h0, smul_zero]))

theorem flg_letters4_ne_empty (t : X × X × X × X) : flg_letters4 t ≠ ∅ := by
  intro h
  have : t.1 ∈ flg_letters4 t := by simp [flg_letters4]
  rw [h] at this
  exact absurd this (Finset.notMem_empty t.1)

/-- A `σ`-stable finite set of letters has even cardinality. -/
theorem flg_stable_card_even [Fintype X] (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x)
    (hfree : ∀ x, σ x ≠ x) (T : Finset X) (hT : ∀ x ∈ T, σ x ∈ T) : Even T.card := by
  have key : (∑ x ∈ T, (1 : ZMod 2)) = 0 :=
    Finset.sum_involution (s := T) (f := fun (_ : X) => (1 : ZMod 2))
      (fun a _ => σ a) (fun _ _ => by decide) (fun a _ _ => hfree a)
      (fun a ha => hT a ha) (fun a _ => hσ a)
  rw [Finset.sum_const, nsmul_eq_mul, mul_one] at key
  have h' : ((T.card : ℤ) : ZMod 2) = 0 := by push_cast; exact key
  have h2 : (2 : ℤ) ∣ (T.card : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 2).mp h'
  exact even_iff_two_dvd.mpr (Int.natCast_dvd_natCast.mp h2)

end Support

end Work.SSGRoute
