import Mathlib
import Submission.Work.SSGRoute.free_lie_four_defs
import Submission.Work.SSGRoute.CC.Bf4Defs
import Submission.Work.SSGRoute.brk4_support_perm
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The four-letter base case of the free-Lie-algebra residual statement
-/

namespace Work.SSGRoute.CC

open scoped BigOperators Matrix

noncomputable section

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
set_option linter.unusedVariables false
set_option maxErrors 5000

/-! ## 1. The `Θ`-span -/

/-- The `Θ`-span `span{u * σA u + σA u * u : u ∈ Tsub Y}`. -/
noncomputable def THspanX (Y : Type)
    (σA : MonoidAlgebra (ZMod 2) (FreeMonoid Y) →ₗ[ZMod 2]
      MonoidAlgebra (ZMod 2) (FreeMonoid Y)) : Submodule (ZMod 2)
    (MonoidAlgebra (ZMod 2) (FreeMonoid Y)) :=
  Submodule.span (ZMod 2) (Set.range fun u :
      {u : MonoidAlgebra (ZMod 2) (FreeMonoid Y) // u ∈ Tsub Y} =>
    (u : MonoidAlgebra (ZMod 2) (FreeMonoid Y)) * σA u + σA u * u)

/-! ## 2. The monomial-sum toolkit over `Fin 4` -/

/-- A `4`-tuple of letters. -/
abbrev Tp : Type := Fin 4 × Fin 4 × Fin 4 × Fin 4

/-- The word of a `4`-tuple. -/
def wrd (t : Tp) : FreeMonoid (Fin 4) := FreeMonoid.ofList [t.1, t.2.1, t.2.2.1, t.2.2.2]

/-- The monomial of a word. -/
noncomputable def mn (w : FreeMonoid (Fin 4)) : A4 := MonoidAlgebra.single w 1

/-- The eight words of the degree-`4` left-nested bracket, as tuples. -/
def arr (t : Tp) : List Tp :=
  [ (t.1, t.2.1, t.2.2.1, t.2.2.2),
    (t.2.1, t.1, t.2.2.1, t.2.2.2),
    (t.2.2.1, t.1, t.2.1, t.2.2.2),
    (t.2.2.1, t.2.1, t.1, t.2.2.2),
    (t.2.2.2, t.1, t.2.1, t.2.2.1),
    (t.2.2.2, t.2.1, t.1, t.2.2.1),
    (t.2.2.2, t.2.2.1, t.1, t.2.1),
    (t.2.2.2, t.2.2.1, t.2.1, t.1) ]

/-- The number of occurrences of a tuple in a list of tuples. -/
def tcnt (l : List Tp) (t : Tp) : ℕ := (l.filter (· = t)).length

/-- The monomial sum of a list of tuples. -/
noncomputable def tsum (l : List Tp) : A4 := (l.map (fun t => mn (wrd t))).sum

theorem tsum_nil : tsum [] = 0 := rfl

theorem tsum_cons (t : Tp) (l : List Tp) : tsum (t :: l) = mn (wrd t) + tsum l := rfl

theorem tsum_singleton (t : Tp) : tsum [t] = mn (wrd t) := by
  rw [tsum_cons, tsum_nil, add_zero]

theorem tsum_append (l₁ l₂ : List Tp) : tsum (l₁ ++ l₂) = tsum l₁ + tsum l₂ := by
  simp only [tsum, List.map_append, List.sum_append]

/-- The eight-monomial expansion of `⁅⁅⁅t₁,t₂⁆,t₃⁆,t₄⁆`. -/
theorem brk4_tsum (t : Tp) : brk4 (Fin 4) t = tsum (arr t) := by
  simp only [brk4, brk, mn, wrd, arr, tsum, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil, MonoidAlgebra.single_mul_single, mul_one, mul_add, add_mul, mul_assoc,
    FreeMonoid.ofList_cons, FreeMonoid.ofList_nil]
  abel

/-- The coeff of a monomial. -/
theorem coeff_mn (v w : FreeMonoid (Fin 4)) : (mn v).coeff w = if v = w then 1 else 0 := by
  rw [mn, MonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- The word map is injective. -/
theorem wrd_injective : Function.Injective wrd := by
  intro s t h
  have h' : ([s.1, s.2.1, s.2.2.1, s.2.2.2] : List (Fin 4))
      = [t.1, t.2.1, t.2.2.1, t.2.2.2] := FreeMonoid.ofList.injective h
  simp only [List.cons.injEq, and_true] at h'
  obtain ⟨p1, p2, p3, p4⟩ := h'
  exact Prod.ext p1 (Prod.ext p2 (Prod.ext p3 p4))

/-- The word of a tuple, as a product of letters (right-associated). -/
theorem wrd_of4 (x y z w : Fin 4) :
    wrd (x, y, z, w)
      = FreeMonoid.of x * (FreeMonoid.of y * (FreeMonoid.of z * FreeMonoid.of w)) := by
  simp [wrd, FreeMonoid.ofList_cons]

/-- The product of two monomials. -/
theorem mn_mul (a b : FreeMonoid (Fin 4)) : mn a * mn b = mn (a * b) := by
  simp only [mn, MonoidAlgebra.single_mul_single, mul_one]

theorem tcnt_cons_self (l : List Tp) (t : Tp) : tcnt (t :: l) t = tcnt l t + 1 := by
  simp only [tcnt, List.filter_cons]
  rw [if_pos (by simp)]
  simp

theorem tcnt_cons_of_ne {t u : Tp} (h : t ≠ u) (l : List Tp) : tcnt (t :: l) u = tcnt l u := by
  simp only [tcnt, List.filter_cons]
  rw [if_neg (by simp [h])]

theorem my_ext_coeff {x y : A4} (h : ∀ w : FreeMonoid (Fin 4), x.coeff w = y.coeff w) : x = y := by
  apply MonoidAlgebra.ext
  exact Finsupp.ext h

/-- The coefficient of a monomial sum at a four-letter word. -/
theorem coeff_tsum (l : List Tp) (t : Tp) :
    (tsum l).coeff (wrd t) = ((tcnt l t : ℕ) : ZMod 2) := by
  induction l with
  | nil => rw [tsum_nil]; simp [tcnt]
  | cons s l ih =>
      rw [tsum_cons, MonoidAlgebra.coeff_add, Finsupp.add_apply, ih]
      have hcoeff : (mn (wrd s)).coeff (wrd t) = if s = t then 1 else 0 := by
        rw [coeff_mn]
        by_cases h : s = t
        · rw [if_pos (by rw [h]), if_pos h]
        · rw [if_neg (fun hh => h (wrd_injective hh)), if_neg h]
      rw [hcoeff]
      by_cases hst : s = t
      · subst hst; rw [if_pos rfl, tcnt_cons_self, Nat.cast_add, Nat.cast_one]
        ring
      · rw [if_neg hst, tcnt_cons_of_ne hst]
        exact zero_add _

theorem coeff_tsum_ne (l : List Tp) {w : FreeMonoid (Fin 4)}
    (hw : ∀ t : Tp, wrd t ≠ w) : (tsum l).coeff w = 0 := by
  induction l with
  | nil => rw [tsum_nil]; rfl
  | cons s l ih =>
      rw [tsum_cons, MonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_mn, if_neg (hw s), ih,
        zero_add]

/-- A monomial sum is determined by the parities of its multiplicities. -/
theorem tsum_eq_of_tcnt (l l' : List Tp)
    (h : ∀ t : Tp, ((tcnt l t : ℕ) : ZMod 2) = ((tcnt l' t : ℕ) : ZMod 2)) :
    tsum l = tsum l' := by
  apply my_ext_coeff
  intro w
  by_cases hw : ∃ t : Tp, wrd t = w
  · obtain ⟨t, rfl⟩ := hw
    rw [coeff_tsum, coeff_tsum, h t]
  · rw [coeff_tsum_ne l (fun t ht => hw ⟨t, ht⟩), coeff_tsum_ne l' (fun t ht => hw ⟨t, ht⟩)]

/-! ## 3. The concrete setup -/

/-- The four letters of `Fin 4` as elements of `A4`. -/
noncomputable def ltr4 (x : Fin 4) : A4 := mn (FreeMonoid.of x)

theorem ltr4_def (x : Fin 4) : ltr4 x = mn (FreeMonoid.of x) := rfl

/-- The fixed-point-free involution `(0 1)(2 3)` of `Fin 4`. -/
def sg4 : Fin 4 ≃ Fin 4 := Equiv.swap 0 1 * Equiv.swap 2 3

/-- The letterwise algebra automorphism of `A4` induced by `sg4`. -/
noncomputable def sgAlg : A4 ≃ₐ[ZMod 2] A4 :=
  MonoidAlgebra.domCongr (ZMod 2) (ZMod 2) (FreeMonoid.freeMonoidCongr sg4)

/-- The letterwise linear map of `A4` induced by `sg4`. -/
noncomputable def sgA : A4 →ₗ[ZMod 2] A4 := sgAlg.toLinearMap

theorem sgA_gen (x : Fin 4) (c : ZMod 2) :
    sgA (MonoidAlgebra.single (FreeMonoid.of x) c)
      = MonoidAlgebra.single (FreeMonoid.of (sg4 x)) c := by
  show sgAlg _ = _
  rw [sgAlg, MonoidAlgebra.domCongr_single, FreeMonoid.freeMonoidCongr_of]

theorem sgA_one : sgA 1 = 1 := by
  change sgAlg (1 : A4) = 1
  exact map_one sgAlg

theorem sgA_mul (a b : A4) : sgA (a * b) = sgA a * sgA b := by
  change sgAlg (a * b) = sgAlg a * sgAlg b
  exact map_mul sgAlg a b

theorem ltr4_gen (x : Fin 4) : sgA (ltr4 x) = ltr4 (sg4 x) := sgA_gen x 1

theorem sg4_0 : sg4 0 = 1 := by decide
theorem sg4_1 : sg4 1 = 0 := by decide
theorem sg4_2 : sg4 2 = 3 := by decide
theorem sg4_3 : sg4 3 = 2 := by decide

/-- The six permutation tuples starting with `0`. -/
def TB : Fin 6 → Tp :=
  ![(0,1,2,3), (0,1,3,2), (0,2,1,3), (0,2,3,1), (0,3,1,2), (0,3,2,1)]

/-- The six generators of the permutation-supported piece. -/
noncomputable def e6 (i : Fin 6) : A4 := brk4 (Fin 4) (TB i)

/-- The span of the six generators. -/
noncomputable def V6 : Submodule (ZMod 2) A4 := Submodule.span (ZMod 2) (Set.range e6)

/-- The span of the brackets of the permutation tuples. -/
noncomputable def Vperm : Submodule (ZMod 2) A4 :=
  Submodule.span (ZMod 2) (Set.range (fun t : {t : Tp // IsPerm4 t} => brk4 (Fin 4) t.1))

theorem e6_mem (i : Fin 6) : e6 i ∈ V6 := Submodule.subset_span ⟨i, rfl⟩

/-! ## 4. The unitriangular certificate -/

/-- Six tuples whose words separate the six generators. -/
def wit : Fin 6 → Tp :=
  ![(3,2,1,0), (2,3,1,0), (0,2,1,3), (0,2,3,1), (0,3,1,2), (1,2,3,0)]

theorem wit_triangular (i j : Fin 6) :
    ((tcnt (arr (TB i)) (wit j) : ℕ) : ZMod 2) = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> decide

theorem coeff_e6_wit (i j : Fin 6) :
    (e6 i).coeff (wrd (wit j)) = if i = j then 1 else 0 := by
  rw [e6, brk4_tsum, coeff_tsum]
  exact wit_triangular i j

/-- The six generators are linearly independent. -/
theorem e6_indep {a : Fin 6 → ZMod 2} (h : ∑ i, a i • e6 i = 0) : a = 0 := by
  funext j
  have h1 : (∑ i, a i • e6 i).coeff (wrd (wit j)) = 0 := by rw [h]; rfl
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply] at h1
  simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, coeff_e6_wit] at h1
  rw [Finset.sum_eq_single j] at h1
  · simpa using h1
  · intro i _ hij
    simp [hij]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-! ## 5. Values of the six generators -/

theorem e6_val_0 : e6 0 = brk4 (Fin 4) ((0 : Fin 4), 1, 2, 3) := by rw [e6]; rfl
theorem e6_val_1 : e6 1 = brk4 (Fin 4) ((0 : Fin 4), 1, 3, 2) := by rw [e6]; rfl
theorem e6_val_2 : e6 2 = brk4 (Fin 4) ((0 : Fin 4), 2, 1, 3) := by rw [e6]; rfl
theorem e6_val_3 : e6 3 = brk4 (Fin 4) ((0 : Fin 4), 2, 3, 1) := by rw [e6]; rfl
theorem e6_val_4 : e6 4 = brk4 (Fin 4) ((0 : Fin 4), 3, 1, 2) := by rw [e6]; rfl
theorem e6_val_5 : e6 5 = brk4 (Fin 4) ((0 : Fin 4), 3, 2, 1) := by rw [e6]; rfl

/-! ## 6. Products of four letters and the `Θ`-identities -/

/-- A product of four letters, as a monomial sum. -/
theorem mn_mul4 (x y z w : Fin 4) :
    (mn (FreeMonoid.of x) * mn (FreeMonoid.of y)) * (mn (FreeMonoid.of z) * mn (FreeMonoid.of w))
      = tsum [(x, y, z, w)] := by
  rw [tsum_singleton, wrd_of4]
  simp only [mn_mul, mul_assoc]

theorem ltr4_mul4 (x y z w : Fin 4) :
    (ltr4 x * ltr4 y) * (ltr4 z * ltr4 w) = tsum [(x, y, z, w)] := by
  rw [ltr4_def, ltr4_def, ltr4_def, ltr4_def]
  exact mn_mul4 x y z w

/-- `sgA` of the commutator `[0,2]`. -/
theorem sgA_brk02 :
    sgA (ltr4 0 * ltr4 2 + ltr4 2 * ltr4 0) = ltr4 1 * ltr4 3 + ltr4 3 * ltr4 1 := by
  simp only [map_add, sgA_mul, ltr4_gen, sg4_0, sg4_1, sg4_2, sg4_3]

/-- `sgA` of the commutator `[0,3]`. -/
theorem sgA_brk03 :
    sgA (ltr4 0 * ltr4 3 + ltr4 3 * ltr4 0) = ltr4 1 * ltr4 2 + ltr4 2 * ltr4 1 := by
  simp only [map_add, sgA_mul, ltr4_gen, sg4_0, sg4_1, sg4_2, sg4_3]

theorem flg_theta_ac :
    (ltr4 0 * ltr4 2 + ltr4 2 * ltr4 0) * sgA (ltr4 0 * ltr4 2 + ltr4 2 * ltr4 0)
      + sgA (ltr4 0 * ltr4 2 + ltr4 2 * ltr4 0) * (ltr4 0 * ltr4 2 + ltr4 2 * ltr4 0)
    = e6 2 + e6 3 := by
  have h : (ltr4 0 * ltr4 2 + ltr4 2 * ltr4 0) * (ltr4 1 * ltr4 3 + ltr4 3 * ltr4 1)
      + (ltr4 1 * ltr4 3 + ltr4 3 * ltr4 1) * (ltr4 0 * ltr4 2 + ltr4 2 * ltr4 0)
      = brk4 (Fin 4) ((0 : Fin 4), 2, 1, 3) + brk4 (Fin 4) ((0 : Fin 4), 2, 3, 1) := by
    rw [brk4_tsum, brk4_tsum, ← tsum_append]
    repeat rw [add_mul]
    repeat rw [mul_add]
    repeat rw [ltr4_mul4]
    repeat rw [← tsum_append]
    exact tsum_eq_of_tcnt _ _ (by decide)
  rw [sgA_brk02]
  rw [h, e6_val_2, e6_val_3]

theorem flg_theta_ad :
    (ltr4 0 * ltr4 3 + ltr4 3 * ltr4 0) * sgA (ltr4 0 * ltr4 3 + ltr4 3 * ltr4 0)
      + sgA (ltr4 0 * ltr4 3 + ltr4 3 * ltr4 0) * (ltr4 0 * ltr4 3 + ltr4 3 * ltr4 0)
    = e6 4 + e6 5 := by
  have h : (ltr4 0 * ltr4 3 + ltr4 3 * ltr4 0) * (ltr4 1 * ltr4 2 + ltr4 2 * ltr4 1)
      + (ltr4 1 * ltr4 2 + ltr4 2 * ltr4 1) * (ltr4 0 * ltr4 3 + ltr4 3 * ltr4 0)
      = brk4 (Fin 4) ((0 : Fin 4), 3, 1, 2) + brk4 (Fin 4) ((0 : Fin 4), 3, 2, 1) := by
    rw [brk4_tsum, brk4_tsum, ← tsum_append]
    repeat rw [add_mul]
    repeat rw [mul_add]
    repeat rw [ltr4_mul4]
    repeat rw [← tsum_append]
    exact tsum_eq_of_tcnt _ _ (by decide)
  rw [sgA_brk03]
  rw [h, e6_val_4, e6_val_5]

/-! ## 7. The `σ`-action on the six generators -/

theorem sgA_e6_0 : sgA (e6 0) = e6 1 := by
  rw [e6_val_0, sigmaA_brk4 (Fin 4) sg4 sgA sgA_mul sgA_one (fun x => sgA_gen x 1),
    show (sg4 (0 : Fin 4), sg4 1, sg4 2, sg4 3) = ((1 : Fin 4), 0, 3, 2) from by decide,
    brk4_symm 1 0 3 2, e6_val_1]

theorem sgA_e6_2 : sgA (e6 2) = e6 1 + e6 4 := by
  rw [e6_val_2, sigmaA_brk4 (Fin 4) sg4 sgA sgA_mul sgA_one (fun x => sgA_gen x 1),
    show (sg4 (0 : Fin 4), sg4 2, sg4 1, sg4 3) = ((1 : Fin 4), 3, 0, 2) from by decide,
    e6_val_1, e6_val_4,
    brk4_tsum, brk4_tsum, brk4_tsum, ← tsum_append]
  exact tsum_eq_of_tcnt _ _ (by decide)

/-! ## 8. The spanning of `Vperm` by the six generators -/

theorem alpha1111_val (x : Fin 4) : alpha1111 x = 1 := by
  fin_cases x <;> decide

theorem tvec_eq_one {t : Tp} (h : tvec t = alpha1111) (x : Fin 4) : tvec t x = 1 := by
  rw [h, alpha1111_val]

/-- In a permutation tuple the letter `0` occurs. -/
theorem zero_mem : ∀ t : Tp, tvec t = alpha1111 →
    t.1 = 0 ∨ t.2.1 = 0 ∨ t.2.2.1 = 0 ∨ t.2.2.2 = 0 := by decide

/-- A permutation tuple beginning with `0` is one of the six listed tuples. -/
theorem six_perm_1 : ∀ t : Tp, t.1 = 0 → tvec t 0 = 1 → tvec t 1 = 1 → tvec t 2 = 1 →
    tvec t 3 = 1 → ∃ i : Fin 6, t = TB i := by decide

theorem six_perm_2 : ∀ t : Tp, t.2.1 = 0 → tvec t 0 = 1 → tvec t 1 = 1 → tvec t 2 = 1 →
    tvec t 3 = 1 → ∃ i : Fin 6, (t.2.1, t.1, t.2.2.1, t.2.2.2) = TB i := by decide

theorem six_perm_3a : ∀ t : Tp, t.2.2.1 = 0 → tvec t 0 = 1 → tvec t 1 = 1 → tvec t 2 = 1 →
    tvec t 3 = 1 → ∃ i : Fin 6, (t.2.2.1, t.2.1, t.1, t.2.2.2) = TB i := by decide

theorem six_perm_3b : ∀ t : Tp, t.2.2.1 = 0 → tvec t 0 = 1 → tvec t 1 = 1 → tvec t 2 = 1 →
    tvec t 3 = 1 → ∃ i : Fin 6, (t.2.2.1, t.1, t.2.1, t.2.2.2) = TB i := by decide

theorem six_perm_4a : ∀ t : Tp, t.2.2.2 = 0 → tvec t 0 = 1 → tvec t 1 = 1 → tvec t 2 = 1 →
    tvec t 3 = 1 → ∃ i : Fin 6, (t.2.2.2, t.1, t.2.1, t.2.2.1) = TB i := by decide

theorem six_perm_4b : ∀ t : Tp, t.2.2.2 = 0 → tvec t 0 = 1 → tvec t 1 = 1 → tvec t 2 = 1 →
    tvec t 3 = 1 → ∃ i : Fin 6, (t.2.2.2, t.2.2.1, t.1, t.2.1) = TB i := by decide

theorem six_perm_4c : ∀ t : Tp, t.2.2.2 = 0 → tvec t 0 = 1 → tvec t 1 = 1 → tvec t 2 = 1 →
    tvec t 3 = 1 → ∃ i : Fin 6, (t.2.2.2, t.2.2.1, t.2.1, t.1) = TB i := by decide

theorem six_perm_4d : ∀ t : Tp, t.2.2.2 = 0 → tvec t 0 = 1 → tvec t 1 = 1 → tvec t 2 = 1 →
    tvec t 3 = 1 → ∃ i : Fin 6, (t.2.2.2, t.2.1, t.1, t.2.2.1) = TB i := by decide

/-- Every bracket of a permutation tuple lies in `V6`. -/
theorem span_mem (t : Tp) (h : IsPerm4 t) : brk4 (Fin 4) t ∈ V6 := by
  have hz := zero_mem t h
  have e0 := tvec_eq_one h 0
  have e1 := tvec_eq_one h 1
  have e2 := tvec_eq_one h 2
  have e3 := tvec_eq_one h 3
  rcases hz with h0 | h0 | h0 | h0
  · obtain ⟨i, hi⟩ := six_perm_1 t h0 e0 e1 e2 e3
    rw [hi]; exact e6_mem i
  · obtain ⟨i, hi⟩ := six_perm_2 t h0 e0 e1 e2 e3
    rw [brk4_symm t.1 t.2.1 t.2.2.1 t.2.2.2, hi]; exact e6_mem i
  · obtain ⟨i, hi⟩ := six_perm_3a t h0 e0 e1 e2 e3
    obtain ⟨j, hj⟩ := six_perm_3b t h0 e0 e1 e2 e3
    rw [brk4_pos3 t.1 t.2.1 t.2.2.1 t.2.2.2, hi, hj]
    exact Submodule.add_mem _ (e6_mem i) (e6_mem j)
  · obtain ⟨i, hi⟩ := six_perm_4a t h0 e0 e1 e2 e3
    obtain ⟨j, hj⟩ := six_perm_4b t h0 e0 e1 e2 e3
    obtain ⟨k, hk⟩ := six_perm_4c t h0 e0 e1 e2 e3
    obtain ⟨l, hl⟩ := six_perm_4d t h0 e0 e1 e2 e3
    rw [brk4_pos4 t.1 t.2.1 t.2.2.1 t.2.2.2, hi, hj, hk, hl]
    exact Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.add_mem _ (e6_mem i) (e6_mem j)) (e6_mem k)) (e6_mem l)

theorem Vperm_le_V6 : Vperm ≤ V6 := by
  rw [Vperm]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨t, rfl⟩
  exact span_mem t.1 t.2
theorem A4_add_self (t : A4) : t + t = 0 := by
  have h : t + t = ((1 : ZMod 2) + 1) • t := by rw [add_smul, one_smul]
  rw [h, show ((1 : ZMod 2) + 1) = 0 from by decide, zero_smul]

theorem A4_add_cancel (x A : A4) : x + A + x = A := by
  rw [show x + A + x = A + (x + x) from by abel, A4_add_self, add_zero]

theorem A4_add_three (x : A4) : x + (x + x) = x := by
  rw [← add_assoc, A4_add_self, zero_add]

/-! ## 10. The kernel of the coordinate condition -/

/-- Letterwise action of `sg4` on a tuple. -/
def sg4t (t : Tp) : Tp := (sg4 t.1, sg4 t.2.1, sg4 t.2.2.1, sg4 t.2.2.2)

/-- The matrix of the `σ`-action in the witness coordinates. -/
noncomputable def M6 (j i : Fin 6) : ZMod 2 :=
  ((tcnt (arr (sg4t (TB i))) (wit j) : ℕ) : ZMod 2)

/-- The matrix-vector product of `M6` with a coordinate vector. -/
noncomputable def mvec (j : Fin 6) (a : Fin 6 → ZMod 2) : ZMod 2 := ∑ i, M6 j i * a i

theorem M6_0_0 : M6 0 0 = 0 := by decide
theorem M6_0_1 : M6 0 1 = 1 := by decide
theorem M6_0_2 : M6 0 2 = 0 := by decide
theorem M6_0_3 : M6 0 3 = 0 := by decide
theorem M6_0_4 : M6 0 4 = 1 := by decide
theorem M6_0_5 : M6 0 5 = 1 := by decide
theorem M6_1_0 : M6 1 0 = 1 := by decide
theorem M6_1_1 : M6 1 1 = 0 := by decide
theorem M6_1_2 : M6 1 2 = 1 := by decide
theorem M6_1_3 : M6 1 3 = 1 := by decide
theorem M6_1_4 : M6 1 4 = 0 := by decide
theorem M6_1_5 : M6 1 5 = 0 := by decide


theorem mvec_row0 (a : Fin 6 → ZMod 2) : mvec 0 a = a 1 + a 4 + a 5 := by
  rw [mvec, Fin.sum_univ_six, M6_0_0, M6_0_1, M6_0_2, M6_0_3, M6_0_4, M6_0_5]
  ring

theorem mvec_row1 (a : Fin 6 → ZMod 2) : mvec 1 a = a 0 + a 2 + a 3 := by
  rw [mvec, Fin.sum_univ_six, M6_1_0, M6_1_1, M6_1_2, M6_1_3, M6_1_4, M6_1_5]
  ring

noncomputable def g1 : A4 := e6 0 + e6 1
noncomputable def g2 : A4 := e6 1 + e6 2 + e6 4
noncomputable def g3 : A4 := e6 2 + e6 3
noncomputable def g4 : A4 := e6 4 + e6 5

theorem g1_mem : g1 ∈ V6 := by
  rw [g1]; exact Submodule.add_mem _ (e6_mem 0) (e6_mem 1)

theorem g2_mem : g2 ∈ V6 := by
  rw [g2]
  exact Submodule.add_mem _ (Submodule.add_mem _ (e6_mem 1) (e6_mem 2)) (e6_mem 4)

theorem g3_mem : g3 ∈ V6 := by
  rw [g3]; exact Submodule.add_mem _ (e6_mem 2) (e6_mem 3)

theorem g4_mem : g4 ∈ V6 := by
  rw [g4]; exact Submodule.add_mem _ (e6_mem 4) (e6_mem 5)

/-- The four coordinate vectors of the kernel. -/
def kap1 : Fin 6 → ZMod 2 := fun j => if j = 0 ∨ j = 1 then 1 else 0
def kap2 : Fin 6 → ZMod 2 := fun j => if j = 1 ∨ j = 2 ∨ j = 4 then 1 else 0
def kap3 : Fin 6 → ZMod 2 := fun j => if j = 2 ∨ j = 3 then 1 else 0
def kap4 : Fin 6 → ZMod 2 := fun j => if j = 4 ∨ j = 5 then 1 else 0

theorem kap1_0 : kap1 0 = 1 := by decide
theorem kap1_1 : kap1 1 = 1 := by decide
theorem kap1_2 : kap1 2 = 0 := by decide
theorem kap1_3 : kap1 3 = 0 := by decide
theorem kap1_4 : kap1 4 = 0 := by decide
theorem kap1_5 : kap1 5 = 0 := by decide
theorem kap2_0 : kap2 0 = 0 := by decide
theorem kap2_1 : kap2 1 = 1 := by decide
theorem kap2_2 : kap2 2 = 1 := by decide
theorem kap2_3 : kap2 3 = 0 := by decide
theorem kap2_4 : kap2 4 = 1 := by decide
theorem kap2_5 : kap2 5 = 0 := by decide
theorem kap3_0 : kap3 0 = 0 := by decide
theorem kap3_1 : kap3 1 = 0 := by decide
theorem kap3_2 : kap3 2 = 1 := by decide
theorem kap3_3 : kap3 3 = 1 := by decide
theorem kap3_4 : kap3 4 = 0 := by decide
theorem kap3_5 : kap3 5 = 0 := by decide
theorem kap4_0 : kap4 0 = 0 := by decide
theorem kap4_1 : kap4 1 = 0 := by decide
theorem kap4_2 : kap4 2 = 0 := by decide
theorem kap4_3 : kap4 3 = 0 := by decide
theorem kap4_4 : kap4 4 = 1 := by decide
theorem kap4_5 : kap4 5 = 1 := by decide

/-- The coordinate functional on `V6`. -/
theorem coeff_e6_sum_eq (a : Fin 6 → ZMod 2) (j : Fin 6) :
    (∑ i, a i • e6 i).coeff (wrd (wit j)) = a j := by
  rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.sum_eq_single j]
  · rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, coeff_e6_wit]
    simp
  · intro i _ hij
    rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, coeff_e6_wit, if_neg hij, smul_zero]
  · intro hj; exact absurd (Finset.mem_univ j) hj


/-! ## 11. The kernel of the fixedness conditions -/

/-- The coordinate map `(Fin 6 → ZMod 2) → A4` attached to the six generators. -/
noncomputable def cc4_thetaL : (Fin 6 → ZMod 2) →ₗ[ZMod 2] A4 where
  toFun a := ∑ i, a i • e6 i
  map_add' a b := by
    simp only [Fin.sum_univ_six, Pi.add_apply, add_smul]
    abel
  map_smul' c a := by
    simp only [Fin.sum_univ_six, Pi.smul_apply, smul_assoc, smul_add]
    abel

theorem thetaL_apply (a : Fin 6 → ZMod 2) : cc4_thetaL a = ∑ i, a i • e6 i := rfl

theorem thetaL_kap1 : cc4_thetaL kap1 = g1 := by
  rw [thetaL_apply, Fin.sum_univ_six, g1, kap1_0, kap1_1, kap1_2, kap1_3, kap1_4, kap1_5]
  simp

theorem thetaL_kap2 : cc4_thetaL kap2 = g2 := by
  rw [thetaL_apply, Fin.sum_univ_six, g2, kap2_0, kap2_1, kap2_2, kap2_3, kap2_4, kap2_5]
  simp

theorem thetaL_kap3 : cc4_thetaL kap3 = g3 := by
  rw [thetaL_apply, Fin.sum_univ_six, g3, kap3_0, kap3_1, kap3_2, kap3_3, kap3_4, kap3_5]
  simp

theorem thetaL_kap4 : cc4_thetaL kap4 = g4 := by
  rw [thetaL_apply, Fin.sum_univ_six, g4, kap4_0, kap4_1, kap4_2, kap4_3, kap4_4, kap4_5]
  simp

theorem z2_add_self (x : ZMod 2) : x + x = 0 := by
  rw [← two_mul, show (2 : ZMod 2) = 0 from by decide, zero_mul]

theorem z2_xxy (x y : ZMod 2) : x + (x + y) = y := by
  rw [show x + (x + y) = (x + x) + y from by abel, z2_add_self, zero_add]

theorem z2_three_self (x y z : ZMod 2) : x + y + z + x + y + z = 0 := by
  have h : x + y + z + x + y + z = (x + x) + (y + y) + (z + z) := by abel
  rw [h]
  simp only [z2_add_self, add_zero, zero_add]

theorem z2_three_self2 (x y z : ZMod 2) : x + (x + y + z) + y + z = 0 := by
  have h : x + (x + y + z) + y + z = (x + x) + (y + y) + (z + z) := by abel
  rw [h]
  simp only [z2_add_self, add_zero, zero_add]

/-- The four coordinate conditions solve for the kernel of the fixedness conditions. -/
theorem kap_decomp (a : Fin 6 → ZMod 2) (h0 : a 0 + a 1 + a 4 + a 5 = 0)
    (h1 : a 0 + a 1 + a 2 + a 3 = 0) :
    a = a 0 • kap1 + (a 0 + a 1) • kap2 + a 3 • kap3 + a 5 • kap4 := by
  have h2 : a 2 = a 0 + a 1 + a 3 := by
    rw [← add_zero (a 0 + a 1 + a 3), ← h1]
    have h : (a 0 + a 1 + a 3) + (a 0 + a 1 + a 2 + a 3)
        = (a 0 + a 0) + (a 1 + a 1) + (a 3 + a 3) + a 2 := by abel
    rw [h]
    simp only [z2_add_self, add_zero, zero_add]
  have h4 : a 4 = a 0 + a 1 + a 5 := by
    rw [← add_zero (a 0 + a 1 + a 5), ← h0]
    have h : (a 0 + a 1 + a 5) + (a 0 + a 1 + a 4 + a 5)
        = (a 0 + a 0) + (a 1 + a 1) + (a 5 + a 5) + a 4 := by abel
    rw [h]
    simp only [z2_add_self, add_zero, zero_add]
  funext i
  have hi : i = (0 : Fin 6) ∨ i = (1 : Fin 6) ∨ i = (2 : Fin 6) ∨ i = (3 : Fin 6)
      ∨ i = (4 : Fin 6) ∨ i = (5 : Fin 6) := by
    fin_cases i <;> simp
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h2, h4, z2_xxy,
      kap1_0, kap1_1, kap1_2, kap1_3, kap1_4, kap1_5,
      kap2_0, kap2_1, kap2_2, kap2_3, kap2_4, kap2_5,
      kap3_0, kap3_1, kap3_2, kap3_3, kap3_4, kap3_5,
      kap4_0, kap4_1, kap4_2, kap4_3, kap4_4, kap4_5,
      mul_one, mul_zero, add_zero, zero_add]

/-- Linearity of the coordinate map read on the four kernel vectors. -/
theorem Lsum_kap (c1 c2 c3 c4 : ZMod 2) :
    ∑ i, (c1 • kap1 + c2 • kap2 + c3 • kap3 + c4 • kap4) i • e6 i
      = c1 • g1 + c2 • g2 + c3 • g3 + c4 • g4 := by
  rw [← thetaL_apply]
  conv_rhs => rw [← thetaL_kap1, ← thetaL_kap2, ← thetaL_kap3, ← thetaL_kap4]
  simp only [map_add, map_smul]

/-- The kernel of the fixedness conditions: recombination. -/
theorem flg_kernel (a : Fin 6 → ZMod 2) (h0 : a 0 + a 1 + a 4 + a 5 = 0)
    (h1 : a 0 + a 1 + a 2 + a 3 = 0) :
    ∑ i, a i • e6 i = a 0 • g1 + (a 0 + a 1) • g2 + a 3 • g3 + a 5 • g4 := by
  conv_lhs => rw [kap_decomp a h0 h1]
  exact Lsum_kap (a 0) (a 0 + a 1) (a 3) (a 5)

theorem tac_mem : ltr4 0 * ltr4 2 + ltr4 2 * ltr4 0 ∈ Tsub (Fin 4) := by
  have hgen : ∀ p : Fin 4 × Fin 4,
      (MonoidAlgebra.single (FreeMonoid.of p.1) (1 : ZMod 2)
          * MonoidAlgebra.single (FreeMonoid.of p.1) 1
        + (MonoidAlgebra.single (FreeMonoid.of p.2) 1 * MonoidAlgebra.single (FreeMonoid.of p.1) 1
          + MonoidAlgebra.single (FreeMonoid.of p.1) 1 * MonoidAlgebra.single (FreeMonoid.of p.2) 1))
      ∈ Tsub (Fin 4) := fun p => Submodule.subset_span ⟨p, rfl⟩
  have h := Submodule.add_mem _ (hgen ((2 : Fin 4), (0 : Fin 4))) (hgen ((2 : Fin 4), (2 : Fin 4)))
  simp only [ltr4, mn]
  rw [show
      (MonoidAlgebra.single (FreeMonoid.of (2 : Fin 4)) (1 : ZMod 2)
            * MonoidAlgebra.single (FreeMonoid.of 2) 1
          + (MonoidAlgebra.single (FreeMonoid.of (0 : Fin 4)) 1 * MonoidAlgebra.single (FreeMonoid.of 2) 1
            + MonoidAlgebra.single (FreeMonoid.of 2) 1 * MonoidAlgebra.single (FreeMonoid.of 0) 1))
        + (MonoidAlgebra.single (FreeMonoid.of (2 : Fin 4)) (1 : ZMod 2)
            * MonoidAlgebra.single (FreeMonoid.of 2) 1
          + (MonoidAlgebra.single (FreeMonoid.of (2 : Fin 4)) 1 * MonoidAlgebra.single (FreeMonoid.of 2) 1
            + MonoidAlgebra.single (FreeMonoid.of 2) 1 * MonoidAlgebra.single (FreeMonoid.of 2) 1))
      = MonoidAlgebra.single (FreeMonoid.of (0 : Fin 4)) (1 : ZMod 2)
          * MonoidAlgebra.single (FreeMonoid.of 2) 1
        + MonoidAlgebra.single (FreeMonoid.of 2) 1 * MonoidAlgebra.single (FreeMonoid.of (0 : Fin 4)) 1
      from by rw [A4_add_three, A4_add_cancel]] at h
  exact h

theorem tad_mem : ltr4 0 * ltr4 3 + ltr4 3 * ltr4 0 ∈ Tsub (Fin 4) := by
  have hgen : ∀ p : Fin 4 × Fin 4,
      (MonoidAlgebra.single (FreeMonoid.of p.1) (1 : ZMod 2)
          * MonoidAlgebra.single (FreeMonoid.of p.1) 1
        + (MonoidAlgebra.single (FreeMonoid.of p.2) 1 * MonoidAlgebra.single (FreeMonoid.of p.1) 1
          + MonoidAlgebra.single (FreeMonoid.of p.1) 1 * MonoidAlgebra.single (FreeMonoid.of p.2) 1))
      ∈ Tsub (Fin 4) := fun p => Submodule.subset_span ⟨p, rfl⟩
  have h := Submodule.add_mem _ (hgen ((3 : Fin 4), (0 : Fin 4))) (hgen ((3 : Fin 4), (3 : Fin 4)))
  simp only [ltr4, mn]
  rw [show
      (MonoidAlgebra.single (FreeMonoid.of (3 : Fin 4)) (1 : ZMod 2)
            * MonoidAlgebra.single (FreeMonoid.of 3) 1
          + (MonoidAlgebra.single (FreeMonoid.of (0 : Fin 4)) 1 * MonoidAlgebra.single (FreeMonoid.of 3) 1
            + MonoidAlgebra.single (FreeMonoid.of 3) 1 * MonoidAlgebra.single (FreeMonoid.of 0) 1))
        + (MonoidAlgebra.single (FreeMonoid.of (3 : Fin 4)) (1 : ZMod 2)
            * MonoidAlgebra.single (FreeMonoid.of 3) 1
          + (MonoidAlgebra.single (FreeMonoid.of (3 : Fin 4)) 1 * MonoidAlgebra.single (FreeMonoid.of 3) 1
            + MonoidAlgebra.single (FreeMonoid.of 3) 1 * MonoidAlgebra.single (FreeMonoid.of 3) 1))
      = MonoidAlgebra.single (FreeMonoid.of (0 : Fin 4)) (1 : ZMod 2)
          * MonoidAlgebra.single (FreeMonoid.of 3) 1
        + MonoidAlgebra.single (FreeMonoid.of 3) 1 * MonoidAlgebra.single (FreeMonoid.of (0 : Fin 4)) 1
      from by rw [A4_add_three, A4_add_cancel]] at h
  exact h

/-! ## 12. The finite core statement -/

theorem e6_mem_Wsub (i : Fin 6) : e6 i ∈ Wsub (Fin 4) :=
  Submodule.subset_span ⟨TB i, rfl⟩

theorem flg_fin4_core (v : A4) (hv : v ∈ Vperm) (hfix : sgA v = v) :
    ∃ w ∈ Wsub (Fin 4), v - (w + sgA w) ∈ THspanX (Fin 4) sgA := by
  have hv6 : v ∈ V6 := Vperm_le_V6 hv
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp hv6
  have hfix' : sgA (∑ i, a i • e6 i) = ∑ i, a i • e6 i := by rw [ha]; exact hfix
  have hcoeffσ : ∀ j i : Fin 6, (sgA (e6 i)).coeff (wrd (wit j)) = M6 j i := by
    intro j i
    show (sgA (brk4 (Fin 4) (TB i))).coeff (wrd (wit j)) = M6 j i
    rw [sigmaA_brk4 (Fin 4) sg4 sgA sgA_mul sgA_one (fun x => sgA_gen x 1)]
    show (brk4 (Fin 4) (sg4t (TB i))).coeff (wrd (wit j)) = M6 j i
    rw [brk4_tsum, coeff_tsum]
    rfl
  have hmvec : ∀ j, mvec j a = a j := by
    intro j
    have h3 : (∑ i, a i • sgA (e6 i)).coeff (wrd (wit j)) = a j := by
      have h3' := congrArg (fun x : A4 => x.coeff (wrd (wit j))) hfix'
      rw [map_sum, coeff_e6_sum_eq a j] at h3'
      simpa only [map_smul] using h3'
    have hsum_eq : (∑ i, a i • sgA (e6 i)).coeff (wrd (wit j))
        = ∑ i, a i * (sgA (e6 i)).coeff (wrd (wit j)) := by
      rw [MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
      simp only [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
    have h7 : (∑ i, a i * (sgA (e6 i)).coeff (wrd (wit j))) = a j := by
      rw [← hsum_eq]; exact h3
    rw [mvec]
    rw [show (∑ i, M6 j i * a i) = ∑ i, a i * M6 j i from
      Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
    rw [← h7]
    exact Finset.sum_congr rfl (fun i _ => by rw [hcoeffσ j i])
  have h0 : a 0 + a 1 + a 4 + a 5 = 0 := by
    have hh := hmvec 0
    rw [mvec_row0 a] at hh
    rw [← hh]
    exact z2_three_self (a 1) (a 4) (a 5)
  have h1 : a 0 + a 1 + a 2 + a 3 = 0 := by
    have hh := hmvec 1
    rw [mvec_row1 a] at hh
    rw [← hh]
    exact z2_three_self2 (a 0) (a 2) (a 3)
  have hker : ∑ i, a i • e6 i = a 0 • g1 + (a 0 + a 1) • g2 + a 3 • g3 + a 5 • g4 :=
    flg_kernel a h0 h1
  refine ⟨a 0 • e6 0 + (a 0 + a 1) • e6 2, ?_, ?_⟩
  · exact Submodule.add_mem _ (Submodule.smul_mem _ _ (e6_mem_Wsub 0))
      (Submodule.smul_mem _ _ (e6_mem_Wsub 2))
  · have hw : a 0 • e6 0 + (a 0 + a 1) • e6 2
          + sgA (a 0 • e6 0 + (a 0 + a 1) • e6 2) = a 0 • g1 + (a 0 + a 1) • g2 := by
      rw [map_add, map_smul, map_smul, sgA_e6_0, sgA_e6_2, g1, g2]
      simp only [smul_add]
      abel
    have hres : v - ((a 0 • e6 0 + (a 0 + a 1) • e6 2)
          + sgA (a 0 • e6 0 + (a 0 + a 1) • e6 2)) = a 3 • g3 + a 5 • g4 := by
      rw [hw, ← ha, hker]
      abel
    rw [hres, g3, g4, ← flg_theta_ac, ← flg_theta_ad]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ ?_) (Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span ⟨⟨ltr4 0 * ltr4 2 + ltr4 2 * ltr4 0, tac_mem⟩, rfl⟩
    · exact Submodule.subset_span ⟨⟨ltr4 0 * ltr4 3 + ltr4 3 * ltr4 0, tad_mem⟩, rfl⟩

end

end Work.SSGRoute.CC
