import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Data.Int.Star
import Submission.Commons.Algebra.Lie.SerreConstruction.liftOfSerrePresentation
import Submission.Commons.Algebra.MonoidAlgebra.freeAlgebra_counit

set_option backward.isDefEq.respectTransparency false
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 100] LieAlgebra.ofAssociativeAlgebra
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

noncomputable section
open scoped BigOperators

namespace Commons.Algebra.Lie.SerreConstruction

/-
# Non-vanishing of the `E`-generators of the Serre-constructed `e₈`

The ⋆-model of the Verma module, copied from `Submission/StarModule.lean`,
`Submission/StarDerivation.lean` and `Submission/StarQuotient.lean` (Mathlib-only), is used to
exhibit an `e₈`-module on which `E_k` acts nontrivially, so that `E_k ≠ 0` in `e₈(ℂ)`.
-/

namespace SerreEStarModel






variable {ι : Type*}

abbrev FA (ι : Type*) := MonoidAlgebra ℂ (FreeMonoid ι)

def wordElt (v : List ι) : FA ι := MonoidAlgebra.single (FreeMonoid.ofList v) (1:ℂ)

/-- the standard basis of the free algebra, indexed by words -/
def bas (ι : Type*) [DecidableEq ι] : Module.Basis (List ι) ℂ (FA ι) :=
  MonoidAlgebra.basis (FreeMonoid ι) ℂ

lemma bas_apply [DecidableEq ι] (v : List ι) : bas ι v = wordElt v := by
  rw [show bas ι v = (MonoidAlgebra.basis (FreeMonoid ι) ℂ) ((v : FreeMonoid ι)) from rfl]
  rw [MonoidAlgebra.basis_apply]; rfl

variable [DecidableEq ι]
variable (A : Matrix ι ι ℤ) (lam : ι → ℂ)

def wrho (i : ι) (v : List ι) : ℂ := (v.map (fun t => (A i t : ℂ))).sum

def Lop (a : ι) : Module.End ℂ (FA ι) := LinearMap.mulLeft ℂ (wordElt [a])

def Dword (i : ι) : List ι → FA ι
  | [] => 0
  | a :: v => Lop a (Dword i v) + (if a = i then wordElt v else 0)

def Eword (i : ι) : List ι → FA ι
  | [] => 0
  | a :: v => Lop a (Eword i v) + (if a = i then (lam i - wrho A i v) • wordElt v else 0)

def Hword (i : ι) (v : List ι) : FA ι := (lam i - wrho A i v) • wordElt v

def Dop (i : ι) : Module.End ℂ (FA ι) := (bas ι).constr ℂ (Dword i)
def Eop (i : ι) : Module.End ℂ (FA ι) := (bas ι).constr ℂ (Eword A lam i)
def Hop (i : ι) : Module.End ℂ (FA ι) := (bas ι).constr ℂ (Hword A lam i)

lemma Dop_apply (i : ι) (v : List ι) : Dop i (wordElt v) = Dword i v :=
  Module.Basis.constr_basis (bas ι) ℂ (Dword i) v

lemma Eop_apply (i : ι) (v : List ι) : Eop A lam i (wordElt v) = Eword A lam i v :=
  Module.Basis.constr_basis (bas ι) ℂ (Eword A lam i) v

lemma Hop_apply (i : ι) (v : List ι) : Hop A lam i (wordElt v) = Hword A lam i v :=
  Module.Basis.constr_basis (bas ι) ℂ (Hword A lam i) v

lemma Lop_wordElt (a : ι) (v : List ι) : Lop a (wordElt v) = wordElt (a :: v) := by
  simp [Lop, wordElt, LinearMap.mulLeft_apply, MonoidAlgebra.single_mul_single]

lemma wordElt_nil : wordElt ([] : List ι) = (1 : FA ι) := by
  rw [wordElt, FreeMonoid.ofList_nil, MonoidAlgebra.one_def]

/-- map version of the defining recursion of `Eop` -/
lemma Eop_Lop_map (i a : ι) :
    (Eop A lam i).comp (Lop a) = (Lop a).comp (Eop A lam i)
      + (if a = i then Hop A lam i else 0) := by
  refine Module.Basis.ext (bas ι) (fun v => ?_)
  simp only [LinearMap.comp_apply, LinearMap.add_apply, bas_apply]
  rw [Lop_wordElt, Eop_apply, Eop_apply]
  by_cases ha : a = i
  · subst ha; simp only [↓reduceIte, Hop_apply, Eword, Hword, LinearMap.zero_apply]
  · simp only [ha, ↓reduceIte, Hop_apply, Eword, Hword, LinearMap.zero_apply]

lemma Eop_Lop (i a : ι) (x : FA ι) :
    Eop A lam i (Lop a x) = Lop a (Eop A lam i x) + (if a = i then Hop A lam i x else 0) := by
  have h := DFunLike.congr_fun (Eop_Lop_map A lam i a) x
  by_cases ha : a = i <;>
    simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.zero_apply, ha, ↓reduceIte]
      using h

/-- map version for `Hop` -/
lemma Hop_Lop_map (i a : ι) :
    (Hop A lam i).comp (Lop a) = (Lop a).comp (Hop A lam i) - ((A i a : ℤ) : ℂ) • Lop a := by
  refine Module.Basis.ext (bas ι) (fun v => ?_)
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, bas_apply]
  rw [Lop_wordElt, Hop_apply, Hop_apply]
  simp only [Hword, map_smul, Lop_wordElt, wrho, List.map_cons, List.sum_cons]
  push_cast
  simp only [sub_smul]
  module

lemma Hop_Lop (i a : ι) (x : FA ι) :
    Hop A lam i (Lop a x) = Lop a (Hop A lam i x) - ((A i a : ℤ) : ℂ) • Lop a x := by
  have h := DFunLike.congr_fun (Hop_Lop_map A lam i a) x
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply] using h

lemma Hop_Hop_map (i j : ι) :
    (Hop A lam i).comp (Hop A lam j) = (Hop A lam j).comp (Hop A lam i) := by
  refine Module.Basis.ext (bas ι) (fun v => ?_)
  simp only [LinearMap.comp_apply, bas_apply, Hop_apply, Hword, map_smul]
  rw [smul_comm]

lemma Hop_Hop (i j : ι) (x : FA ι) : Hop A lam i (Hop A lam j x) = Hop A lam j (Hop A lam i x) := by
  have h := DFunLike.congr_fun (Hop_Hop_map A lam i j) x
  simpa only [LinearMap.comp_apply] using h

lemma Dop_Lop_map (i a : ι) :
    (Dop i).comp (Lop a) = (Lop a).comp (Dop i) + (if a = i then (LinearMap.id : Module.End ℂ (FA ι)) else 0) := by
  refine Module.Basis.ext (bas ι) (fun v => ?_)
  simp only [LinearMap.comp_apply, LinearMap.add_apply, bas_apply]
  rw [Lop_wordElt, Dop_apply, Dop_apply]
  by_cases ha : a = i
  · subst ha; simp only [↓reduceIte, Dword, LinearMap.zero_apply, LinearMap.id_apply]
  · simp only [ha, ↓reduceIte, Dword, LinearMap.zero_apply, LinearMap.id_apply]

/-- **Technique lemma.**  A linear endomorphism of the free algebra that commutes with all left
multiplications by generators and kills `1` is zero. -/
lemma eq_zero_of_comm_L (S : FA ι →ₗ[ℂ] FA ι)
    (hS : ∀ a x, S (Lop a x) = Lop a (S x)) (h1 : S 1 = 0) : S = 0 := by
  refine Module.Basis.ext (bas ι) (fun v => ?_)
  rw [bas_apply (ι := ι) v]
  simp only [LinearMap.zero_apply]
  induction v with
  | nil => simpa [wordElt_nil] using h1
  | cons a v ih =>
    rw [← Lop_wordElt, hS a (wordElt v), ih, map_zero]




variable (A : Matrix ι ι ℤ) (lam : ι → ℂ)

/-- relation 2: `[H_i, E_j] = A i j • E_j` -/
theorem Hop_Eop (i j : ι) (x : FA ι) :
    Hop A lam i (Eop A lam j x) = Eop A lam j (Hop A lam i x) + ((A i j : ℤ) : ℂ) • Eop A lam j x := by
  let S : FA ι →ₗ[ℂ] FA ι := (Hop A lam i).comp (Eop A lam j) - (Eop A lam j).comp (Hop A lam i)
      - ((A i j : ℤ) : ℂ) • Eop A lam j
  have hS : ∀ a y, S (Lop a y) = Lop a (S y) := by
    intro a y
    simp only [S, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, Eop_Lop, Hop_Lop,
      map_add, map_sub, map_smul]
    by_cases haj : a = j
    · subst haj
      simp only [↓reduceIte]
      rw [Hop_Hop A lam i a y]
      abel
    · simp only [if_neg haj, zero_apply, map_zero, smul_zero]
      abel
  have h1 : S 1 = 0 := by
    simp only [S, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply]
    rw [← wordElt_nil]
    simp [Eop_apply, Eword, Hop_apply, Hword, map_zero, LinearMap.map_smul_of_tower]
  have hzero : S = 0 := eq_zero_of_comm_L S hS h1
  have hcong := DFunLike.congr_fun hzero x
  simp only [S, LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.zero_apply] at hcong
  rw [sub_eq_zero] at hcong
  rw [sub_eq_iff_eq_add] at hcong
  rw [add_comm] at hcong
  exact hcong


/-- relation 2 as an operator identity -/
lemma Hop_Eop_map (i j : ι) :
    (Hop A lam i).comp (Eop A lam j)
      = (Eop A lam j).comp (Hop A lam i) + ((A i j : ℤ) : ℂ) • Eop A lam j := by
  refine Module.Basis.ext (bas ι) (fun v => ?_)
  rw [LinearMap.comp_apply, LinearMap.add_apply]
  exact Hop_Eop A lam i j (wordElt v)

/-- relation 1 -/
lemma lie_Hop_Hop (i j : ι) : ⁅Hop A lam i, Hop A lam j⁆ = 0 := by
  rw [show ⁅Hop A lam i, Hop A lam j⁆
      = (Hop A lam i).comp (Hop A lam j) - (Hop A lam j).comp (Hop A lam i) from rfl,
    Hop_Hop_map, sub_self]

/-- relation 3 as a Lie bracket -/
lemma lie_Hop_Lop (i a : ι) : ⁅Hop A lam i, Lop a⁆ = -((A i a : ℤ) : ℂ) • Lop a := by
  rw [show ⁅Hop A lam i, Lop a⁆ = (Hop A lam i).comp (Lop a) - (Lop a).comp (Hop A lam i) from rfl,
    Hop_Lop_map]
  module

/-- relation 4 as a Lie bracket -/
lemma lie_Eop_Lop (i a : ι) :
    ⁅Eop A lam i, Lop a⁆ = (if a = i then Hop A lam i else 0) := by
  rw [show ⁅Eop A lam i, Lop a⁆ = (Eop A lam i).comp (Lop a) - (Lop a).comp (Eop A lam i) from rfl,
    Eop_Lop_map]
  abel

/-- relation 2 as a Lie bracket -/
lemma lie_Hop_Eop (i j : ι) : ⁅Hop A lam i, Eop A lam j⁆ = ((A i j : ℤ) : ℂ) • Eop A lam j := by
  rw [show ⁅Hop A lam i, Eop A lam j⁆
      = (Hop A lam i).comp (Eop A lam j) - (Eop A lam j).comp (Hop A lam i) from rfl,
    Hop_Eop_map]
  abel

/-- scalar linearity of the commutator on `Module.End` (left slot) -/
lemma cmt_smul_left (c : ℂ) (x y : Module.End ℂ (FA ι)) :
    ⁅c • x, y⁆ = c • ⁅x, y⁆ := by
  rw [show ⁅c • x, y⁆ = (c • x).comp y - y.comp (c • x) from rfl,
    show ⁅x, y⁆ = x.comp y - y.comp x from rfl,
    LinearMap.smul_comp, LinearMap.comp_smul, smul_sub]

/-- scalar linearity of the commutator on `Module.End` (right slot) -/
lemma cmt_smul_right (c : ℂ) (x y : Module.End ℂ (FA ι)) :
    ⁅x, c • y⁆ = c • ⁅x, y⁆ := by
  rw [show ⁅x, c • y⁆ = x.comp (c • y) - (c • y).comp x from rfl,
    show ⁅x, y⁆ = x.comp y - y.comp x from rfl,
    LinearMap.smul_comp, LinearMap.comp_smul, smul_sub]

/-- `⁅x, x⁆ = 0` for `Module.End` -/
lemma cmt_self (x : Module.End ℂ (FA ι)) : ⁅x, x⁆ = 0 := by
  rw [show ⁅x, x⁆ = x.comp x - x.comp x from rfl, sub_self]

/-- `[Lop a, Eop i]` -/
lemma lie_Lop_Eop (i a : ι) :
    ⁅Lop a, Eop A lam i⁆ = -(if a = i then Hop A lam i else 0) := by
  rw [← lie_skew (Lop a) (Eop A lam i), lie_Eop_Lop]

/-- the Serre relation `[E_i, E_j] = 0` when `A i j = 0` -/
theorem Eop_Eop_lie_eq_zero (i j : ι) (hij : A i j = 0) (hji : A j i = 0) (x : FA ι) :
    (⁅Eop A lam i, Eop A lam j⁆ : Module.End ℂ (FA ι)) x = 0 := by
  have key : ∀ a : ι, ⁅(⁅Eop A lam i, Eop A lam j⁆ : Module.End ℂ (FA ι)), Lop a⁆ = 0 := by
    intro a
    have hsk : ⁅(⁅Eop A lam i, Eop A lam j⁆ : Module.End ℂ (FA ι)), Lop a⁆
        = -⁅Lop a, ⁅Eop A lam i, Eop A lam j⁆⁆ :=
      (neg_eq_iff_eq_neg).mp (lie_skew (Lop a) _)
    rw [hsk, leibniz_lie (Lop a) (Eop A lam i) (Eop A lam j), lie_Lop_Eop, lie_Lop_Eop,
      neg_lie, lie_neg]
    by_cases hai : a = i
    · rw [if_pos hai]
      by_cases haj : a = j
      · rw [if_pos haj, ← lie_skew (Eop A lam i) (Hop A lam j), lie_Hop_Eop, lie_Hop_Eop,
          hij, hji]
        simp
      · rw [if_neg haj, lie_zero, lie_Hop_Eop, hij]
        simp
    · rw [if_neg hai, zero_lie]
      by_cases haj : a = j
      · rw [if_pos haj, ← lie_skew (Eop A lam i) (Hop A lam j), lie_Hop_Eop, hji]
        simp
      · rw [if_neg haj, lie_zero]
        simp
  have hS1 : (⁅Eop A lam i, Eop A lam j⁆ : Module.End ℂ (FA ι)) 1 = 0 := by
    have hj : (Eop A lam j) (1 : FA ι) = 0 := by rw [← wordElt_nil, Eop_apply]; rfl
    have hi : (Eop A lam i) (1 : FA ι) = 0 := by rw [← wordElt_nil, Eop_apply]; rfl
    rw [show (⁅Eop A lam i, Eop A lam j⁆ : Module.End ℂ (FA ι)) 1
        = (Eop A lam i) ((Eop A lam j) 1) - (Eop A lam j) ((Eop A lam i) 1) from rfl,
      hj, hi]
    simp
  have hS : ∀ a y, (⁅Eop A lam i, Eop A lam j⁆ : Module.End ℂ (FA ι)) (Lop a y)
      = Lop a ((⁅Eop A lam i, Eop A lam j⁆ : Module.End ℂ (FA ι)) y) := by
    intro a y
    have h := congrArg (fun f : Module.End ℂ (FA ι) => f y) (key a)
    rw [show (⁅(⁅Eop A lam i, Eop A lam j⁆ : Module.End ℂ (FA ι)), Lop a⁆) y
        = (⁅Eop A lam i, Eop A lam j⁆ : Module.End ℂ (FA ι)) (Lop a y)
          - Lop a ((⁅Eop A lam i, Eop A lam j⁆ : Module.End ℂ (FA ι)) y) from rfl,
      LinearMap.zero_apply] at h
    simpa using sub_eq_zero.mp h
  have hzero := eq_zero_of_comm_L (⁅Eop A lam i, Eop A lam j⁆ : Module.End ℂ (FA ι)) hS hS1
  rw [hzero]
  rfl

set_option maxHeartbeats 8000000 in
/-- the Serre relation `(ad E_i)^2 (E_j) = 0` when `A i i = 2` and `A i j = -1` -/
theorem serre_adE_two (i j : ι) (hii : A i i = 2) (hij : A i j = -1) (x : FA ι) :
    (⁅Eop A lam i, ⁅Eop A lam i, Eop A lam j⁆⁆ : Module.End ℂ (FA ι)) x = 0 := by
  have h1 : ⁅Hop A lam i, ⁅Eop A lam i, Eop A lam j⁆⁆
      = (((A i i : ℤ) : ℂ) + ((A i j : ℤ) : ℂ)) • ⁅Eop A lam i, Eop A lam j⁆ := by
    rw [leibniz_lie (Hop A lam i) (Eop A lam i) (Eop A lam j), lie_Hop_Eop, lie_Hop_Eop,
      cmt_smul_left, cmt_smul_right]
    module
  have key : ∀ a : ι,
      ⁅(⁅Eop A lam i, ⁅Eop A lam i, Eop A lam j⁆⁆ : Module.End ℂ (FA ι)), Lop a⁆ = 0 := by
    intro a
    have hsk : ⁅(⁅Eop A lam i, ⁅Eop A lam i, Eop A lam j⁆⁆ : Module.End ℂ (FA ι)), Lop a⁆
        = -⁅Lop a, ⁅Eop A lam i, ⁅Eop A lam i, Eop A lam j⁆⁆⁆ :=
      (neg_eq_iff_eq_neg).mp (lie_skew (Lop a) _)
    have hC : ⁅-(if a = i then Hop A lam i else 0), Eop A lam j⁆
        = -((if a = i then (A i j : ℤ) else 0 : ℤ) : ℂ) • Eop A lam j := by
      by_cases hai : a = i
      · rw [if_pos hai, if_pos hai, neg_lie, lie_Hop_Eop]; module
      · rw [if_neg hai, if_neg hai]; simp
    have hD : ⁅Eop A lam i, -(if a = j then Hop A lam j else 0)⁆
        = ((if a = j then (A j i : ℤ) else 0 : ℤ) : ℂ) • Eop A lam i := by
      by_cases haj : a = j
      · rw [if_pos haj, if_pos haj, lie_neg, ← lie_skew (Eop A lam i) (Hop A lam j),
          lie_Hop_Eop]; module
      · rw [if_neg haj, if_neg haj]; simp
    have hA : ⁅-(if a = i then Hop A lam i else 0), ⁅Eop A lam i, Eop A lam j⁆⁆
        = -((if a = i then (((A i i : ℤ) : ℂ) + ((A i j : ℤ) : ℂ)) else 0)) •
            ⁅Eop A lam i, Eop A lam j⁆ := by
      by_cases hai : a = i
      · rw [if_pos hai, if_pos hai, neg_lie, h1]; module
      · rw [if_neg hai, if_neg hai]; simp
    rw [hsk]
    rw [leibniz_lie (Lop a) (Eop A lam i) (⁅Eop A lam i, Eop A lam j⁆),
      leibniz_lie (Lop a) (Eop A lam i) (Eop A lam j), lie_Lop_Eop, lie_Lop_Eop]
    rw [hA, lie_add, hC, hD]
    simp only [cmt_smul_right, cmt_self, smul_zero, add_zero]
    by_cases hai : a = i
    · rw [if_pos hai]
      by_cases hij' : i = j
      · rw [hij'] at hij hii
        omega
      · simp only [if_pos hai, hii, hij]
        module
    · simp only [if_neg hai, zero_smul, neg_zero, zero_add, add_zero]
      module
  have hS1 : (⁅Eop A lam i, ⁅Eop A lam i, Eop A lam j⁆⁆ : Module.End ℂ (FA ι)) 1 = 0 := by
    have hj : (Eop A lam j) (1 : FA ι) = 0 := by rw [← wordElt_nil, Eop_apply]; rfl
    have hi : (Eop A lam i) (1 : FA ι) = 0 := by rw [← wordElt_nil, Eop_apply]; rfl
    rw [show (⁅Eop A lam i, ⁅Eop A lam i, Eop A lam j⁆⁆ : Module.End ℂ (FA ι)) 1
        = (Eop A lam i) ((⁅Eop A lam i, Eop A lam j⁆ : Module.End ℂ (FA ι)) 1)
          - (⁅Eop A lam i, Eop A lam j⁆ : Module.End ℂ (FA ι)) ((Eop A lam i) 1) from rfl,
      hi,
      show (⁅Eop A lam i, Eop A lam j⁆ : Module.End ℂ (FA ι)) 1
        = (Eop A lam i) ((Eop A lam j) 1) - (Eop A lam j) ((Eop A lam i) 1) from rfl,
      hj, hi]
    simp only [LinearMap.map_zero, sub_zero, zero_sub]
  have hS : ∀ a y, (⁅Eop A lam i, ⁅Eop A lam i, Eop A lam j⁆⁆ : Module.End ℂ (FA ι)) (Lop a y)
      = Lop a ((⁅Eop A lam i, ⁅Eop A lam i, Eop A lam j⁆⁆ : Module.End ℂ (FA ι)) y) := by
    intro a y
    have h := congrArg (fun f : Module.End ℂ (FA ι) => f y) (key a)
    rw [show (⁅(⁅Eop A lam i, ⁅Eop A lam i, Eop A lam j⁆⁆ : Module.End ℂ (FA ι)), Lop a⁆) y
        = (⁅Eop A lam i, ⁅Eop A lam i, Eop A lam j⁆⁆ : Module.End ℂ (FA ι)) (Lop a y)
          - Lop a ((⁅Eop A lam i, ⁅Eop A lam i, Eop A lam j⁆⁆ : Module.End ℂ (FA ι)) y)
        from rfl, LinearMap.zero_apply] at h
    simpa using sub_eq_zero.mp h
  have hzero := eq_zero_of_comm_L
    (⁅Eop A lam i, ⁅Eop A lam i, Eop A lam j⁆⁆ : Module.End ℂ (FA ι)) hS hS1
  rw [hzero]
  rfl


variable {ι : Type*} [DecidableEq ι]
variable (A : Matrix ι ι ℤ) (lam : ι → ℂ)

def wdelta (i : ι) : Module.End ℂ (FA ι) :=
  (bas ι).constr ℂ (fun v => wrho A i v • wordElt v)

lemma wdelta_apply (i : ι) (v : List ι) :
    wdelta A i (wordElt v) = wrho A i v • wordElt v :=
  Module.Basis.constr_basis (bas ι) ℂ _ v

lemma wrho_append (i : ι) (u v : List ι) : wrho A i (u ++ v) = wrho A i u + wrho A i v := by
  simp [wrho, List.map_append, List.sum_append]

lemma wordElt_mul (u v : List ι) : wordElt u * wordElt v = wordElt (u ++ v) := by
  simp [wordElt, MonoidAlgebra.single_mul_single]

lemma wdelta_deriv_word (i : ι) (u v : List ι) :
    wdelta A i (wordElt u * wordElt v)
      = wdelta A i (wordElt u) * wordElt v + wordElt u * wdelta A i (wordElt v) := by
  rw [wordElt_mul, wdelta_apply, wdelta_apply, wdelta_apply, wrho_append,
    show wordElt (u ++ v) = wordElt u * wordElt v from (wordElt_mul u v).symm, add_smul,
    smul_mul_assoc, mul_smul_comm]

lemma wdelta_deriv_word' (i : ι) (u : List ι) (y : FA ι) :
    wdelta A i (wordElt u * y) = wdelta A i (wordElt u) * y + wordElt u * wdelta A i y := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => rw [mul_add, map_add, hp, hq, mul_add, map_add, mul_add]; abel
  | single v d =>
    rw [show (MonoidAlgebra.single v d : FA ι) = d • wordElt (FreeMonoid.toList v) by
      rw [wordElt]; simp [MonoidAlgebra.smul_single]]
    rw [map_smul, mul_smul_comm, map_smul, mul_smul_comm, mul_smul_comm]
    rw [← smul_add]; congr 1
    exact wdelta_deriv_word A i u (FreeMonoid.toList v)

lemma wdelta_deriv (i : ι) (x y : FA ι) :
    wdelta A i (x * y) = wdelta A i x * y + x * wdelta A i y := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq => rw [add_mul, map_add, hp, hq]; simp only [add_mul, map_add]; abel
  | single u c =>
    rw [show (MonoidAlgebra.single u c : FA ι) = c • wordElt (FreeMonoid.toList u) by
      rw [wordElt]; simp [MonoidAlgebra.smul_single]]
    rw [smul_mul_assoc, map_smul, map_smul, smul_mul_assoc, smul_mul_assoc,
      wdelta_deriv_word' A i (FreeMonoid.toList u) y]
    module



variable {ι : Type*} [DecidableEq ι]
variable (A : Matrix ι ι ℤ) (lam : ι → ℂ)

lemma Hop_eq (i : ι) : Hop A lam i = (lam i) • (1 : Module.End ℂ (FA ι)) - wdelta A i := by
  refine Module.Basis.ext (bas ι) (fun v => ?_)
  rw [LinearMap.sub_apply, LinearMap.smul_apply, bas_apply, Hop_apply, wdelta_apply, Hword]
  rw [show ((1 : Module.End ℂ (FA ι))) (wordElt v) = wordElt v from rfl]
  module

/-- the "f-side" Serre relation element `⁅f_i, f_j⁆` -/
def serreGen (i j : ι) : FA ι := wordElt [i] * wordElt [j] - wordElt [j] * wordElt [i]

/-- the "f-side" Serre relation element `⁅f_i, ⁅f_i, f_j⁆⁆` -/
def serreGen2 (i j : ι) : FA ι := wordElt [i] * serreGen i j - serreGen i j * wordElt [i]

/-- the set of the "f-side" Serre relation elements -/
def serreSet : Set (FA ι) :=
  (Set.range fun p : ι × ι => serreGen p.1 p.2) ∪ (Set.range fun p : ι × ι => serreGen2 p.1 p.2)

/-- the two-sided ideal generated by the "f-side" Serre relation elements -/
def serreIdeal : Ideal (FA ι) := Ideal.span (serreSet (ι := ι))

lemma wdelta_wordElt_single (i p : ι) :
    wdelta A i (wordElt [p]) = ((A i p : ℤ) : ℂ) • wordElt [p] := by
  rw [wdelta_apply]
  simp [wrho]

lemma wdelta_serreGen (i p q : ι) :
    wdelta A i (serreGen p q) = (((A i p : ℤ) : ℂ) + ((A i q : ℤ) : ℂ)) • serreGen p q := by
  rw [serreGen, map_sub, wdelta_deriv, wdelta_deriv, wdelta_wordElt_single, wdelta_wordElt_single,
    smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm]
  simp only [add_smul, sub_smul]
  module

lemma wdelta_serreGen2 (i p q : ι) :
    wdelta A i (serreGen2 p q)
      = (2 * ((A i p : ℤ) : ℂ) + ((A i q : ℤ) : ℂ)) • serreGen2 p q := by
  rw [serreGen2, map_sub, wdelta_deriv, wdelta_deriv, wdelta_wordElt_single, wdelta_serreGen,
    smul_mul_assoc, mul_smul_comm, smul_mul_assoc, mul_smul_comm]
  simp only [add_smul, sub_smul]
  module





variable {ι : Type*} [DecidableEq ι]
variable (A : Matrix ι ι ℤ) (lam : ι → ℂ)

/-- The generators of the two-sided ideal cutting out `U(𝔫⁻)`: the "f-side" Serre relations
`⁅f_p, f_q⁆` (when `A p q = 0`) and `(ad f_p)^2 f_q` (when `A p q = -1`). -/
def Gen : Set (FA ι) :=
  {s | (∃ p q : ι, A p q = 0 ∧ A q p = 0 ∧ s = serreGen p q)
      ∨ (∃ p q : ι, A p p = 2 ∧ A p q = -1 ∧ s = serreGen2 p q)}

/-- `J = A · ⟨Gen⟩ · A`, the two-sided ideal generated by the "f-side" Serre relations,
realised as the `ℂ`-span of the products `wordElt u * s * wordElt v`. -/
def J : Submodule ℂ (FA ι) :=
  Submodule.span ℂ {x | ∃ s ∈ Gen A, ∃ u v : List ι, x = wordElt u * s * wordElt v}

lemma subset_J_gen : {x | ∃ s ∈ Gen A, ∃ u v : List ι, x = wordElt u * s * wordElt v} ⊆ J A :=
  Submodule.subset_span

lemma gen_subset_J : Gen A ⊆ J A := by
  intro s hs
  exact subset_J_gen A ⟨s, hs, [], [], by rw [wordElt_nil]; simp⟩

lemma wordElt_mul_mem_J (u : List ι) {x : FA ι} (hx : x ∈ J A) : wordElt u * x ∈ J A := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨s, hs, u', v, rfl⟩ := hx
      refine subset_J_gen A ⟨s, hs, u ++ u', v, ?_⟩
      rw [← wordElt_mul]
      simp only [mul_assoc]
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => rw [mul_add]; exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih => rw [mul_smul_comm]; exact Submodule.smul_mem _ c ih

lemma mul_wordElt_mem_J {x : FA ι} (hx : x ∈ J A) (v : List ι) : x * wordElt v ∈ J A := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨s, hs, u', v', rfl⟩ := hx
      refine subset_J_gen A ⟨s, hs, u', v' ++ v, ?_⟩
      rw [← wordElt_mul]
      simp only [mul_assoc]
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y hx hy ihx ihy => rw [add_mul]; exact Submodule.add_mem _ ihx ihy
  | smul c x hx ih => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ih

lemma Dop_Lop (i a : ι) (x : FA ι) :
    Dop i (Lop a x) = Lop a (Dop i x) + (if a = i then x else 0) := by
  have h := DFunLike.congr_fun (Dop_Lop_map (ι := ι) i a) x
  by_cases ha : a = i <;>
    simpa only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.zero_apply,
      LinearMap.id_apply, ha, ↓reduceIte] using h

/-! ## Right multiplication by a single generator -/

lemma Hop_mul_single_map (i b : ι) :
    (Hop A lam i).comp (LinearMap.mulRight ℂ (wordElt [b]))
      = (LinearMap.mulRight ℂ (wordElt [b])).comp (Hop A lam i)
        - ((A i b : ℤ) : ℂ) • (LinearMap.mulRight ℂ (wordElt [b])) := by
  refine Module.Basis.ext (bas ι) (fun v => ?_)
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply, bas_apply,
    LinearMap.mulRight_apply]
  rw [wordElt_mul, Hop_apply, Hop_apply, Hword, Hword, wrho_append]
  have hb : wrho A i [b] = ((A i b : ℤ) : ℂ) := by simp [wrho]
  rw [hb, sub_smul, smul_mul_assoc, wordElt_mul]
  module

lemma Hop_mul_single (i b : ι) (y : FA ι) :
    Hop A lam i (y * wordElt [b]) = (Hop A lam i y - ((A i b : ℤ) : ℂ) • y) * wordElt [b] := by
  have := DFunLike.congr_fun (Hop_mul_single_map A lam i b) y
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.mulRight_apply, sub_mul, smul_mul_assoc] using this
lemma Lop_mul_single (a b : ι) (z : FA ι) :
    Lop a z * wordElt [b] = Lop a (z * wordElt [b]) := by simp [Lop, mul_assoc]

lemma wordElt_cons_eq (a : ι) (u : List ι) : wordElt (a :: u) = wordElt [a] * wordElt u := by
  rw [show a :: u = [a] ++ u from rfl, wordElt_mul]

lemma wrho_single (i b : ι) : wrho A i [b] = ((A i b : ℤ) : ℂ) := by simp [wrho]

lemma Dword_append_single (i : ι) (u : List ι) (b : ι) :
    Dword i (u ++ [b]) = (if b = i then wordElt u else 0) + Dword i u * wordElt [b] := by
  induction u with
  | nil => simp [wordElt_nil, Dword]
  | cons a u ih =>
      rw [List.cons_append, Dword, Dword, ih, ← wordElt_mul u [b], wordElt_cons_eq a u]
      simp only [Lop, LinearMap.mulLeft_apply]
      split_ifs <;> noncomm_ring

lemma Dop_mul_single (i b : ι) (y : FA ι) :
    Dop i (y * wordElt [b]) = Dop i y * wordElt [b] + (if b = i then y else 0) := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
      rw [add_mul, map_add, hp, hq, map_add, add_mul]
      split_ifs <;> abel
  | single w c =>
      rw [show (MonoidAlgebra.single w c : FA ι) = c • wordElt (FreeMonoid.toList w) by
        rw [wordElt]; simp [MonoidAlgebra.smul_single]]
      simp only [smul_mul_assoc, map_smul, wordElt_mul, Dop_apply]
      rw [Dword_append_single]
      simp only [smul_add, smul_mul_assoc]
      split_ifs <;> module

lemma Eword_append_single (i : ι) (u : List ι) (b : ι) :
    Eword A lam i (u ++ [b])
      = Eword A lam i u * wordElt [b]
        - (((A i b : ℤ) : ℂ) • (Dword i u * wordElt [b]))
        + (if b = i then (lam i) • wordElt u else 0) := by
  induction u with
  | nil => simp [wordElt_nil, Eword, Dword, wrho]
  | cons a u ih =>
      rw [List.cons_append, Eword, Eword, Dword, ih, ← wordElt_mul u [b], wordElt_cons_eq a u,
        wrho_append, wrho_single]
      simp only [Lop, LinearMap.mulLeft_apply]
      split_ifs <;>
        simp only [smul_add, smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, sub_smul,
          add_smul, add_sub, sub_add, zero_add, add_zero, mul_add, mul_sub, add_mul,
          sub_mul, mul_assoc] <;> module

lemma Eop_mul_single (i b : ι) (y : FA ι) :
    Eop A lam i (y * wordElt [b])
      = (Eop A lam i y - ((A i b : ℤ) : ℂ) • Dop i y) * wordElt [b]
        + (if b = i then (lam i) • y else 0) := by
  induction y using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
      rw [add_mul, map_add, hp, hq]
      simp only [map_add, map_sub, sub_mul, add_mul, smul_add, smul_mul_assoc, sub_add, add_sub,
        add_assoc, mul_assoc]
      split_ifs <;> module
  | single w c =>
      rw [show (MonoidAlgebra.single w c : FA ι) = c • wordElt (FreeMonoid.toList w) by
        rw [wordElt]; simp [MonoidAlgebra.smul_single]]
      simp only [smul_mul_assoc, map_smul, wordElt_mul, Eop_apply, Dop_apply]
      rw [Eword_append_single]
      simp only [smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, smul_add,
        smul_zero, mul_assoc, mul_add, mul_sub, add_mul, sub_mul, add_smul, sub_smul]
      split_ifs <;> module

lemma Dop_single (i p : ι) : Dop i (wordElt [p]) = (if p = i then (1 : FA ι) else 0) := by
  rw [Dop_apply]; simp [Dword, wordElt_nil]

lemma Hop_single (i p : ι) :
    Hop A lam i (wordElt [p]) = (lam i - ((A i p : ℤ) : ℂ)) • wordElt [p] := by
  rw [Hop_apply]; simp [Hword, wrho]

lemma Eop_single (i p : ι) :
    Eop A lam i (wordElt [p]) = (if p = i then (lam i) • (1 : FA ι) else 0) := by
  rw [Eop_apply]; simp [Eword, wordElt_nil, wrho]

lemma Dop_deriv_wordElt (i : ι) : ∀ (u : List ι) (y : FA ι),
    Dop i (wordElt u * y) = Dop i (wordElt u) * y + wordElt u * Dop i y := by
  intro u
  induction u with
  | nil =>
      intro y
      rw [wordElt_nil]
      have h1 : Dop i (1 : FA ι) = 0 := by
        change Dop i (wordElt ([] : List ι)) = 0
        rw [Dop_apply]
        rfl
      rw [one_mul, h1]
      simp
  | cons a u ih =>
      intro y
      rw [← Lop_wordElt, show Lop a (wordElt u) * y = Lop a (wordElt u * y) from by
        simp [Lop, mul_assoc], Dop_Lop, Dop_Lop, ih]
      simp only [map_add, add_mul, ite_mul, zero_mul, Lop, LinearMap.mulLeft_apply, mul_assoc]
      abel

lemma Dop_deriv (i : ι) (x y : FA ι) : Dop i (x * y) = Dop i x * y + x * Dop i y := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
      rw [add_mul, map_add, hp, hq, map_add]
      simp only [add_mul]
      abel
  | single w c =>
      rw [show (MonoidAlgebra.single w c : FA ι) = c • wordElt (FreeMonoid.toList w) by
        rw [wordElt]; simp [MonoidAlgebra.smul_single]]
      rw [smul_mul_assoc, map_smul, Dop_deriv_wordElt]
      simp only [smul_mul_assoc, map_smul]
      module

lemma Dop_serreGen (i p q : ι) : Dop i (serreGen p q) = 0 := by
  rw [serreGen, map_sub, Dop_mul_single, Dop_mul_single]
  simp only [Dop_single, ite_mul, zero_mul, one_mul]
  by_cases hp : p = i <;> by_cases hq : q = i <;> simp [hp, hq]

lemma Dop_serreGen2 (i p q : ι) : Dop i (serreGen2 p q) = 0 := by
  rw [serreGen2, map_sub, Dop_deriv_wordElt, Dop_mul_single, Dop_serreGen]
  simp only [map_zero, zero_mul, mul_zero, add_zero, zero_add, sub_self, Dop_single]
  by_cases hp : p = i <;> simp [hp]


lemma Hop_fp_fq (i p q : ι) :
    Hop A lam i (wordElt [p] * wordElt [q])
      = (lam i - ((A i p : ℤ) : ℂ) - ((A i q : ℤ) : ℂ)) • (wordElt [p] * wordElt [q]) := by
  rw [wordElt_mul, Hop_apply, Hword]
  simp only [wrho, List.map_append, List.map_cons, List.map_nil, List.sum_append, List.sum_cons,
    List.sum_nil, add_zero]
  congr 1
  ring

lemma Eop_fp_fq (i p q : ι) :
    Eop A lam i (wordElt [p] * wordElt [q])
      = (if q = i then (lam i) • wordElt [p] else 0)
        + (if p = i then (lam i - ((A i q : ℤ) : ℂ)) • wordElt [q] else 0) := by
  rw [show wordElt [p] * wordElt [q] = Lop p (wordElt [q]) from by
    rw [wordElt_mul, Lop_wordElt]
    rfl, Eop_Lop, Eop_single, Hop_single]
  simp only [Lop, LinearMap.mulLeft_apply]
  by_cases hq : q = i <;> by_cases hp : p = i <;>
    simp [hq, hp, mul_ite, mul_smul_comm, mul_one, zero_mul, mul_zero, add_zero, zero_add]

lemma Hop_serreGen (i p q : ι) :
    Hop A lam i (serreGen p q)
      = (lam i - ((A i p : ℤ) : ℂ) - ((A i q : ℤ) : ℂ)) • serreGen p q := by
  rw [serreGen, map_sub, Hop_fp_fq, Hop_fp_fq, smul_sub]
  module

lemma Eop_serreGen (i p q : ι) (hpq : A p q = 0) (hqp : A q p = 0) :
    Eop A lam i (serreGen p q) = 0 := by
  by_cases hpq' : p = q
  · subst hpq'; rw [serreGen, sub_self, map_zero]
  · rw [serreGen, map_sub, Eop_fp_fq, Eop_fp_fq]
    by_cases hp : p = i
    · rw [if_pos hp, if_pos hp]
      by_cases hq : q = i
      · exact absurd (hp.trans hq.symm) hpq'
      · rw [if_neg hq, if_neg hq]
        have h : ((A i q : ℤ) : ℂ) = 0 := by rw [← hp]; exact_mod_cast hpq
        simp [h]
    · rw [if_neg hp, if_neg hp]
      by_cases hq : q = i
      · rw [if_pos hq, if_pos hq]
        have h : ((A i p : ℤ) : ℂ) = 0 := by rw [← hq]; exact_mod_cast hqp
        simp [h]
      · rw [if_neg hq, if_neg hq]; module

lemma Eop_serreGen_formula (i p q : ι) :
    Eop A lam i (serreGen p q)
      = (if q = i then ((A i p : ℤ) : ℂ) else 0) • wordElt [p]
        - (if p = i then ((A i q : ℤ) : ℂ) else 0) • wordElt [q] := by
  rw [serreGen, map_sub, Eop_fp_fq, Eop_fp_fq]
  by_cases hp : p = i
  · by_cases hq : q = i
    · simp only [if_pos hp, if_pos hq, smul_sub, sub_smul, sub_add, add_sub, add_assoc]
      module
    · simp only [if_pos hp, if_neg hq, zero_add, add_zero, smul_sub, sub_smul, zero_smul,
        sub_zero]
      module
  · by_cases hq : q = i
    · simp only [if_neg hp, if_pos hq, zero_add, add_zero]
      module
    · simp only [if_neg hp, if_neg hq]; simp

lemma Eop_serreGen2 (i p q : ι) (hpp : A p p = 2) (hpq : A p q = -1) :
    Eop A lam i (serreGen2 p q) = 0 := by
  by_cases hpq' : p = q
  · rw [hpq']
    simp only [serreGen2, serreGen]
    simp
  · rw [serreGen2, map_sub, show wordElt [p] * serreGen p q = Lop p (serreGen p q) from by
      rw [Lop, LinearMap.mulLeft_apply], Eop_Lop, Eop_mul_single, Dop_serreGen, smul_zero,
      sub_zero, Hop_serreGen, Eop_serreGen_formula]
    simp only [Lop, LinearMap.mulLeft_apply]
    rw [sub_eq_zero]
    by_cases hp : p = i
    · have hii : ((A i i : ℤ) : ℂ) = 2 := by rw [← hp]; exact_mod_cast hpp
      have hiq : ((A i q : ℤ) : ℂ) = -1 := by rw [← hp]; exact_mod_cast hpq
      have hqi : ¬(q = i) := fun h => hpq' (hp.trans h.symm)
      simp only [if_pos hp, if_neg hqi]
      rw [hp, hii, hiq, serreGen]
      simp only [one_smul, neg_smul, smul_sub, mul_sub, mul_add, sub_mul,
        add_mul, sub_smul, add_smul, smul_mul_assoc, mul_smul_comm, mul_assoc, neg_add,
        neg_sub, mul_neg, neg_mul, neg_neg]
      module
    · by_cases hq : q = i
      · simp only [if_neg hp, if_pos hq]
        simp only [smul_mul_assoc, mul_smul_comm, mul_sub, sub_mul, sub_smul, add_smul,
          smul_sub, mul_assoc, zero_add, add_zero, smul_zero, sub_self]
        module
      · simp only [if_neg hp, if_neg hq]
        simp

lemma wdelta_triMon (i : ι) (u v : List ι) (s : FA ι) :
    wdelta A i (wordElt u * s * wordElt v)
      = (wrho A i u + wrho A i v) • (wordElt u * s * wordElt v)
        + wordElt u * wdelta A i s * wordElt v := by
  rw [show wordElt u * s * wordElt v = (wordElt u * s) * wordElt v from rfl, wdelta_deriv,
    wdelta_deriv, wdelta_apply, wdelta_apply, add_smul]
  simp only [add_mul, smul_mul_assoc, mul_smul_comm]
  module

lemma wdelta_mem_J (i : ι) {x : FA ι} (hx : x ∈ J A) : wdelta A i x ∈ J A := by
  have hle : J A ≤ Submodule.comap (wdelta A i) (J A) := by
    rw [J, Submodule.span_le]
    rintro x ⟨s, hs, u, v, rfl⟩
    change wdelta A i (wordElt u * s * wordElt v) ∈ J A
    have hgen : wordElt u * s * wordElt v ∈ J A := subset_J_gen A ⟨s, hs, u, v, rfl⟩
    have hmid : wordElt u * wdelta A i s * wordElt v ∈ J A := by
      rcases hs with ⟨p, q, hpq, hqp, rfl⟩ | ⟨p, q, hpp, hpq, rfl⟩
      · rw [wdelta_serreGen, mul_smul_comm, smul_mul_assoc]
        exact Submodule.smul_mem _ _ hgen
      · rw [wdelta_serreGen2, mul_smul_comm, smul_mul_assoc]
        exact Submodule.smul_mem _ _ hgen
    rw [wdelta_triMon A i u v s]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hgen) hmid
  exact hle hx

lemma Hop_mem_J (i : ι) {x : FA ι} (hx : x ∈ J A) : Hop A lam i x ∈ J A := by
  rw [Hop_eq]
  exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hx) (wdelta_mem_J A i hx)

lemma Eop_gen_mem_J (i : ι) {s : FA ι} (hs : s ∈ Gen A) : Eop A lam i s ∈ J A := by
  rcases hs with ⟨p, q, hpq, hqp, rfl⟩ | ⟨p, q, hpp, hpq, rfl⟩
  · rw [Eop_serreGen (A := A) (lam := lam) i p q hpq hqp]; exact Submodule.zero_mem _
  · rw [Eop_serreGen2 (A := A) (lam := lam) i p q hpp hpq]; exact Submodule.zero_mem _

lemma Dop_gen_mem_J (i : ι) {s : FA ι} (hs : s ∈ Gen A) : Dop i s ∈ J A := by
  rcases hs with ⟨p, q, hpq, hqp, rfl⟩ | ⟨p, q, hpp, hpq, rfl⟩
  · rw [Dop_serreGen i p q]; exact Submodule.zero_mem _
  · rw [Dop_serreGen2 i p q]; exact Submodule.zero_mem _

/-- Left expansion: `Eop` applied to `wordElt u * y` stays in `J` when `y` and `Eop i y` do. -/
lemma Eop_wordElt_mul_mem (i : ι) (u : List ι) {y : FA ι} (hy : y ∈ J A)
    (hyE : Eop A lam i y ∈ J A) : Eop A lam i (wordElt u * y) ∈ J A := by
  induction u with
  | nil => simpa [wordElt_nil] using hyE
  | cons a u ih =>
      rw [show wordElt (a :: u) * y = Lop a (wordElt u * y) from by
        rw [wordElt_cons_eq, Lop, LinearMap.mulLeft_apply, mul_assoc], Eop_Lop]
      refine Submodule.add_mem _ (wordElt_mul_mem_J A [a] ih) ?_
      by_cases ha : a = i
      · rw [if_pos ha]; exact Hop_mem_J A lam i (wordElt_mul_mem_J A u hy)
      · rw [if_neg ha]; exact Submodule.zero_mem _

/-- Left expansion for `Dop`. -/
lemma Dop_wordElt_mul_mem (i : ι) (u : List ι) {y : FA ι} (hy : y ∈ J A)
    (hyD : Dop i y ∈ J A) : Dop i (wordElt u * y) ∈ J A := by
  induction u with
  | nil => simpa [wordElt_nil] using hyD
  | cons a u ih =>
      rw [show wordElt (a :: u) * y = Lop a (wordElt u * y) from by
        rw [wordElt_cons_eq, Lop, LinearMap.mulLeft_apply, mul_assoc], Dop_Lop]
      refine Submodule.add_mem _ (wordElt_mul_mem_J A [a] ih) ?_
      by_cases ha : a = i
      · rw [if_pos ha]; exact wordElt_mul_mem_J A u hy
      · rw [if_neg ha]; exact Submodule.zero_mem _

/-- Right expansion for `Eop` (together with the companion `Dop`). -/
lemma Eop_Dop_right_mem (i : ι) (y : FA ι) (hy : y ∈ J A)
    (hyE : Eop A lam i y ∈ J A) (hyD : Dop i y ∈ J A) : ∀ v : List ι,
    Eop A lam i (y * wordElt v) ∈ J A ∧ Dop i (y * wordElt v) ∈ J A := by
  intro v
  induction v using List.reverseRecOn with
  | nil => simpa [wordElt_nil] using ⟨hyE, hyD⟩
  | append_singleton v b ih =>
      obtain ⟨hE, hD⟩ := ih
      have hyb : y * wordElt v ∈ J A := mul_wordElt_mem_J A hy v
      have hsplit : y * wordElt (v ++ [b]) = (y * wordElt v) * wordElt [b] := by
        rw [mul_assoc, wordElt_mul]
      refine ⟨?_, ?_⟩
      · rw [hsplit, Eop_mul_single]
        refine Submodule.add_mem _
          (mul_wordElt_mem_J A (Submodule.sub_mem _ hE (Submodule.smul_mem _ _ hD)) [b]) ?_
        by_cases hb : b = i
        · rw [if_pos hb]; exact Submodule.smul_mem _ _ hyb
        · rw [if_neg hb]; exact Submodule.zero_mem _
      · rw [hsplit, Dop_mul_single]
        refine Submodule.add_mem _ (mul_wordElt_mem_J A hD [b]) ?_
        by_cases hb : b = i
        · rw [if_pos hb]; exact hyb
        · rw [if_neg hb]; exact Submodule.zero_mem _

/-- Right expansion for `Dop`. -/
lemma Dop_right_mem (i : ι) {y : FA ι} (hy : y ∈ J A) (hyD : Dop i y ∈ J A) :
    ∀ v : List ι, Dop i (y * wordElt v) ∈ J A := by
  intro v
  induction v using List.reverseRecOn with
  | nil => simpa [wordElt_nil] using hyD
  | append_singleton v b ih =>
      have hyb : y * wordElt v ∈ J A := mul_wordElt_mem_J A hy v
      have hsplit : y * wordElt (v ++ [b]) = (y * wordElt v) * wordElt [b] := by
        rw [mul_assoc, wordElt_mul]
      rw [hsplit, Dop_mul_single]
      refine Submodule.add_mem _ (mul_wordElt_mem_J A ih [b]) ?_
      by_cases hb : b = i
      · rw [if_pos hb]; exact hyb
      · rw [if_neg hb]; exact Submodule.zero_mem _

/-- The "delete" operator preserves the ideal `J`. -/
lemma Eop_mem_J (i : ι) {x : FA ι} (hx : x ∈ J A) : Eop A lam i x ∈ J A := by
  have hle : J A ≤ Submodule.comap (Eop A lam i) (J A) := by
    rw [J, Submodule.span_le]
    rintro x ⟨s, hs, u, v, rfl⟩
    change Eop A lam i (wordElt u * s * wordElt v) ∈ J A
    rw [show wordElt u * s * wordElt v = wordElt u * (s * wordElt v) from by simp [mul_assoc]]
    refine Eop_wordElt_mul_mem A lam i u (mul_wordElt_mem_J A (gen_subset_J A hs) v) ?_
    exact (Eop_Dop_right_mem A lam i s (gen_subset_J A hs) (Eop_gen_mem_J A lam i hs)
      (Dop_gen_mem_J A i hs) v).1
  exact hle hx

/-- The "derivation" operator preserves the ideal `J`. -/
lemma Dop_mem_J (i : ι) {x : FA ι} (hx : x ∈ J A) : Dop i x ∈ J A := by
  have hle : J A ≤ Submodule.comap (Dop i) (J A) := by
    rw [J, Submodule.span_le]
    rintro x ⟨s, hs, u, v, rfl⟩
    change Dop i (wordElt u * s * wordElt v) ∈ J A
    rw [show wordElt u * s * wordElt v = wordElt u * (s * wordElt v) from by simp [mul_assoc]]
    refine Dop_wordElt_mul_mem A i u (mul_wordElt_mem_J A (gen_subset_J A hs) v) ?_
    exact Dop_right_mem A i (gen_subset_J A hs) (Dop_gen_mem_J A i hs) v
  exact hle hx

/-! ## The quotient `V = A / J` and the descended operators -/

abbrev V (A : Matrix ι ι ℤ) := FA ι ⧸ (J A)

lemma mapQ_ext {f g : FA ι →ₗ[ℂ] FA ι} (hf : ∀ x ∈ J A, f x ∈ J A)
    (hg : ∀ x ∈ J A, g x ∈ J A) (h : ∀ x, f x - g x ∈ J A) :
    (Submodule.mapQ (J A) (J A) f (fun x hx => Submodule.mem_comap.mpr (hf x hx))) =
      (Submodule.mapQ (J A) (J A) g (fun x hx => Submodule.mem_comap.mpr (hg x hx))) := by
  refine LinearMap.ext (fun v => ?_)
  induction v using Submodule.Quotient.induction_on with
  | _ x =>
      rw [Submodule.mapQ_apply, Submodule.mapQ_apply, Submodule.Quotient.eq]
      exact h x

lemma mapQ_sub_eq (f g : FA ι →ₗ[ℂ] FA ι) (hf : ∀ x ∈ J A, f x ∈ J A)
    (hg : ∀ x ∈ J A, g x ∈ J A) :
    (Submodule.mapQ (J A) (J A) (f - g)
        (fun x hx => Submodule.mem_comap.mpr (Submodule.sub_mem _ (hf x hx) (hg x hx)))) =
      (Submodule.mapQ (J A) (J A) f (fun x hx => Submodule.mem_comap.mpr (hf x hx))) -
        (Submodule.mapQ (J A) (J A) g (fun x hx => Submodule.mem_comap.mpr (hg x hx))) := by
  refine LinearMap.ext (fun v => ?_)
  induction v using Submodule.Quotient.induction_on with
  | _ x =>
      simp only [Submodule.mapQ_apply, LinearMap.sub_apply]
      rw [← Submodule.Quotient.mk_sub]

lemma mapQ_comp_eq (f g : FA ι →ₗ[ℂ] FA ι) (hf : ∀ x ∈ J A, f x ∈ J A)
    (hg : ∀ x ∈ J A, g x ∈ J A) :
    (Submodule.mapQ (J A) (J A) (f.comp g)
        (fun x hx => Submodule.mem_comap.mpr (hf _ (hg x hx)))) =
      (Submodule.mapQ (J A) (J A) f (fun x hx => Submodule.mem_comap.mpr (hf x hx))).comp
        (Submodule.mapQ (J A) (J A) g (fun x hx => Submodule.mem_comap.mpr (hg x hx))) := by
  refine LinearMap.ext (fun v => ?_)
  induction v using Submodule.Quotient.induction_on with
  | _ x =>
      simp only [Submodule.mapQ_apply, LinearMap.comp_apply]

def Lbar (a : ι) : Module.End ℂ (V A) :=
  Submodule.mapQ (J A) (J A) (Lop a)
    (fun x hx => Submodule.mem_comap.mpr (wordElt_mul_mem_J A [a] hx))

def Hbar (i : ι) : Module.End ℂ (V A) :=
  Submodule.mapQ (J A) (J A) (Hop A lam i)
    (fun x hx => Submodule.mem_comap.mpr (Hop_mem_J A lam i hx))

def Ebar (i : ι) : Module.End ℂ (V A) :=
  Submodule.mapQ (J A) (J A) (Eop A lam i)
    (fun x hx => Submodule.mem_comap.mpr (Eop_mem_J A lam i hx))

lemma Lbar_mk (a : ι) (x : FA ι) :
    Lbar A a (Submodule.Quotient.mk x) = Submodule.Quotient.mk (Lop a x) :=
  Submodule.mapQ_apply _ _ _ x

lemma Hbar_mk (i : ι) (x : FA ι) :
    Hbar A lam i (Submodule.Quotient.mk x) = Submodule.Quotient.mk (Hop A lam i x) :=
  Submodule.mapQ_apply _ _ _ x

lemma Ebar_mk (i : ι) (x : FA ι) :
    Ebar A lam i (Submodule.Quotient.mk x) = Submodule.Quotient.mk (Eop A lam i x) :=
  Submodule.mapQ_apply _ _ _ x


lemma mul_mem_J (z : FA ι) (hz : z ∈ J A) (x : FA ι) : z * x ∈ J A := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [mul_zero]; exact Submodule.zero_mem _
  | add p q hp hq => rw [mul_add]; exact Submodule.add_mem _ hp hq
  | single w c =>
      rw [show (MonoidAlgebra.single w c : FA ι) = c • wordElt (FreeMonoid.toList w) by
        rw [wordElt]; simp [MonoidAlgebra.smul_single]]
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ _ (mul_wordElt_mem_J A hz _)

lemma mul_mem_J' (x : FA ι) {z : FA ι} (hz : z ∈ J A) : x * z ∈ J A := by
  induction x using MonoidAlgebra.induction_linear with
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add p q hp hq => rw [add_mul]; exact Submodule.add_mem _ hp hq
  | single w c =>
      rw [show (MonoidAlgebra.single w c : FA ι) = c • wordElt (FreeMonoid.toList w) by
        rw [wordElt]; simp [MonoidAlgebra.smul_single]]
      rw [smul_mul_assoc]
      exact Submodule.smul_mem _ _ (wordElt_mul_mem_J A _ hz)

lemma mk_eq_zero_iff {x : FA ι} :
    (Submodule.Quotient.mk x : V A) = 0 ↔ x ∈ J A :=
  Submodule.Quotient.mk_eq_zero _

lemma lie_Lbar_Lbar_apply (i j : ι) (x : FA ι) :
    (⁅Lbar A i, Lbar A j⁆ : Module.End ℂ (V A)) (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (serreGen i j * x) := by
  rw [show (⁅Lbar A i, Lbar A j⁆ : Module.End ℂ (V A))
      = (Lbar A i).comp (Lbar A j) - (Lbar A j).comp (Lbar A i) from rfl,
    LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.comp_apply, Lbar_mk, Lbar_mk, Lbar_mk,
    Lbar_mk, ← Submodule.Quotient.mk_sub]
  congr 1
  simp only [serreGen, Lop, LinearMap.mulLeft_apply]
  noncomm_ring


/-! ## The Serre relations on `V` -/

lemma lie_Hbar_Hbar (i j : ι) : ⁅Hbar A lam i, Hbar A lam j⁆ = 0 := by
  refine LinearMap.ext (fun v => ?_)
  induction v using Submodule.Quotient.induction_on with
  | _ x =>
      rw [show (⁅Hbar A lam i, Hbar A lam j⁆ : Module.End ℂ (V A))
          = (Hbar A lam i).comp (Hbar A lam j) - (Hbar A lam j).comp (Hbar A lam i)
          from rfl]
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.zero_apply, Hbar_mk]
      rw [← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
      rw [show Hop A lam i (Hop A lam j x) - Hop A lam j (Hop A lam i x) = 0 from by
        rw [Hop_Hop, sub_self]]
      exact Submodule.zero_mem _

lemma lie_Hbar_Ebar (i j : ι) :
    ⁅Hbar A lam i, Ebar A lam j⁆ = ((A i j : ℤ) : ℂ) • Ebar A lam j := by
  refine LinearMap.ext (fun v => ?_)
  induction v using Submodule.Quotient.induction_on with
  | _ x =>
      rw [show (⁅Hbar A lam i, Ebar A lam j⁆ : Module.End ℂ (V A))
          = (Hbar A lam i).comp (Ebar A lam j) - (Ebar A lam j).comp (Hbar A lam i)
          from rfl]
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, Hbar_mk,
        Ebar_mk]
      rw [← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_smul]
      congr 1
      rw [show Hop A lam i (Eop A lam j x) - Eop A lam j (Hop A lam i x)
          = ((A i j : ℤ) : ℂ) • Eop A lam j x from by rw [Hop_Eop]; abel]

lemma lie_Hbar_Lbar (i j : ι) :
    ⁅Hbar A lam i, Lbar A j⁆ = -((A i j : ℤ) : ℂ) • Lbar A j := by
  refine LinearMap.ext (fun v => ?_)
  induction v using Submodule.Quotient.induction_on with
  | _ x =>
      rw [show (⁅Hbar A lam i, Lbar A j⁆ : Module.End ℂ (V A))
          = (Hbar A lam i).comp (Lbar A j) - (Lbar A j).comp (Hbar A lam i) from rfl]
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, Hbar_mk,
        Lbar_mk]
      rw [← Submodule.Quotient.mk_sub, ← Submodule.Quotient.mk_smul]
      congr 1
      rw [show Hop A lam i (Lop j x) - Lop j (Hop A lam i x)
          = -((A i j : ℤ) : ℂ) • Lop j x from by
        rw [show Hop A lam i (Lop j x) = Lop j (Hop A lam i x) - ((A i j : ℤ) : ℂ) • Lop j x
          from Hop_Lop A lam i j x]; module]

lemma lie_Ebar_Lbar (i j : ι) :
    ⁅Ebar A lam i, Lbar A j⁆ = if i = j then Hbar A lam i else 0 := by
  refine LinearMap.ext (fun v => ?_)
  induction v using Submodule.Quotient.induction_on with
  | _ x =>
      rw [show (⁅Ebar A lam i, Lbar A j⁆ : Module.End ℂ (V A))
          = (Ebar A lam i).comp (Lbar A j) - (Lbar A j).comp (Ebar A lam i) from rfl]
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, Ebar_mk, Lbar_mk]
      rw [← Submodule.Quotient.mk_sub]
      by_cases hij : i = j
      · rw [if_pos hij, Hbar_mk]
        have h := DFunLike.congr_fun (lie_Eop_Lop (A := A) (lam := lam) i j) x
        rw [if_pos hij.symm] at h
        rw [show Eop A lam i (Lop j x) - Lop j (Eop A lam i x) = Hop A lam i x from h]
      · rw [if_neg hij, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
        have h := DFunLike.congr_fun (lie_Eop_Lop (A := A) (lam := lam) i j) x
        rw [if_neg (fun hji => hij hji.symm)] at h
        rw [show Eop A lam i (Lop j x) - Lop j (Eop A lam i x) = 0 from h]
        exact Submodule.zero_mem _

lemma Ebar_Ebar_apply (i j : ι) (x : FA ι) :
    (⁅Ebar A lam i, Ebar A lam j⁆ : Module.End ℂ (V A)) (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (⁅Eop A lam i, Eop A lam j⁆ x) := by
  rw [show (⁅Ebar A lam i, Ebar A lam j⁆ : Module.End ℂ (V A))
      = (Ebar A lam i).comp (Ebar A lam j) - (Ebar A lam j).comp (Ebar A lam i) from rfl]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, Ebar_mk]
  rw [← Submodule.Quotient.mk_sub]
  rfl

lemma lie_Ebar_Ebar_zero (i j : ι) (hij : A i j = 0) (hji : A j i = 0) :
    ⁅Ebar A lam i, Ebar A lam j⁆ = 0 := by
  refine LinearMap.ext (fun v => ?_)
  induction v using Submodule.Quotient.induction_on with
  | _ x =>
      rw [Ebar_Ebar_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
      rw [show (⁅Eop A lam i, Eop A lam j⁆ : Module.End ℂ (FA ι)) x = 0 from
        Eop_Eop_lie_eq_zero A lam i j hij hji x]
      exact Submodule.zero_mem _

lemma adE2_apply (i j : ι) (x : FA ι) :
    (⁅Ebar A lam i, ⁅Ebar A lam i, Ebar A lam j⁆⁆ : Module.End ℂ (V A))
        (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (⁅Eop A lam i, ⁅Eop A lam i, Eop A lam j⁆⁆ x) := by
  rw [show (⁅Ebar A lam i, ⁅Ebar A lam i, Ebar A lam j⁆⁆ : Module.End ℂ (V A))
      = (Ebar A lam i).comp (⁅Ebar A lam i, Ebar A lam j⁆)
        - (⁅Ebar A lam i, Ebar A lam j⁆).comp (Ebar A lam i) from rfl]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, Ebar_mk, Ebar_Ebar_apply]
  rw [← Submodule.Quotient.mk_sub]
  rw [show (⁅Eop A lam i, Eop A lam j⁆ : Module.End ℂ (FA ι))
      = (Eop A lam i).comp (Eop A lam j) - (Eop A lam j).comp (Eop A lam i) from rfl]
  rfl

lemma serre_adE_two_V (i j : ι) (hii : A i i = 2) (hij : A i j = -1) :
    ⁅Ebar A lam i, ⁅Ebar A lam i, Ebar A lam j⁆⁆ = 0 := by
  refine LinearMap.ext (fun v => ?_)
  induction v using Submodule.Quotient.induction_on with
  | _ x =>
      rw [adE2_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
      rw [show (⁅Eop A lam i, ⁅Eop A lam i, Eop A lam j⁆⁆ : Module.End ℂ (FA ι)) x = 0 from
        serre_adE_two A lam i j hii hij x]
      exact Submodule.zero_mem _

lemma lie_Lbar_Lbar_zero (i j : ι) (hij : A i j = 0) (hji : A j i = 0) :
    ⁅Lbar A i, Lbar A j⁆ = 0 := by
  refine LinearMap.ext (fun v => ?_)
  induction v using Submodule.Quotient.induction_on with
  | _ x =>
      rw [lie_Lbar_Lbar_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
      have hg : serreGen i j ∈ J A :=
        gen_subset_J A (Or.inl ⟨i, j, hij, hji, rfl⟩)
      exact mul_mem_J A _ hg x

lemma adF2_apply (i j : ι) (x : FA ι) :
    (⁅Lbar A i, ⁅Lbar A i, Lbar A j⁆⁆ : Module.End ℂ (V A)) (Submodule.Quotient.mk x)
      = Submodule.Quotient.mk (serreGen2 i j * x) := by
  rw [show (⁅Lbar A i, ⁅Lbar A i, Lbar A j⁆⁆ : Module.End ℂ (V A))
      = (Lbar A i).comp (⁅Lbar A i, Lbar A j⁆) - (⁅Lbar A i, Lbar A j⁆).comp (Lbar A i)
      from rfl]
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, Lbar_mk, lie_Lbar_Lbar_apply]
  rw [← Submodule.Quotient.mk_sub]
  congr 1
  simp only [serreGen2, serreGen, Lop, LinearMap.mulLeft_apply]
  noncomm_ring

lemma serre_adF_two_V (i j : ι) (hii : A i i = 2) (hij : A i j = -1) :
    ⁅Lbar A i, ⁅Lbar A i, Lbar A j⁆⁆ = 0 := by
  refine LinearMap.ext (fun v => ?_)
  induction v using Submodule.Quotient.induction_on with
  | _ x =>
      rw [adF2_apply, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero]
      have hg : serreGen2 i j ∈ J A :=
        gen_subset_J A (Or.inr ⟨i, j, hii, hij, rfl⟩)
      exact mul_mem_J A _ hg x

lemma adE_zero (i j : ι) (hsymm : ∀ i j, A i j = A j i) (hii : ∀ i, A i i = 2)
    (hA : ∀ i j, i ≠ j → A i j = 0 ∨ A i j = -1) :
    (LieAlgebra.ad ℂ (Module.End ℂ (V A)) (Ebar A lam i) ^ ((-A i j).toNat))
      (⁅Ebar A lam i, Ebar A lam j⁆ : Module.End ℂ (V A)) = 0 := by
  by_cases hij : i = j
  · rw [← hij, hii i, show ((-(2 : ℤ)).toNat) = 0 from by norm_num, pow_zero]
    simpa using cmt_self (Ebar A lam i)
  · rcases hA i j hij with h0 | h1
    · rw [h0, show ((-(0 : ℤ)).toNat) = 0 from by norm_num, pow_zero]
      simpa using lie_Ebar_Ebar_zero A lam i j h0 (by rw [hsymm]; exact h0)
    · rw [h1, show ((-(-(1 : ℤ))).toNat) = 1 from by norm_num, pow_one]
      exact serre_adE_two_V A lam i j (hii i) h1

lemma adF_zero (i j : ι) (hsymm : ∀ i j, A i j = A j i) (hii : ∀ i, A i i = 2)
    (hA : ∀ i j, i ≠ j → A i j = 0 ∨ A i j = -1) :
    (LieAlgebra.ad ℂ (Module.End ℂ (V A)) (Lbar A i) ^ ((-A i j).toNat))
      (⁅Lbar A i, Lbar A j⁆ : Module.End ℂ (V A)) = 0 := by
  by_cases hij : i = j
  · rw [← hij, hii i, show ((-(2 : ℤ)).toNat) = 0 from by norm_num, pow_zero]
    simpa using cmt_self (Lbar A i)
  · rcases hA i j hij with h0 | h1
    · rw [h0, show ((-(0 : ℤ)).toNat) = 0 from by norm_num, pow_zero]
      simpa using lie_Lbar_Lbar_zero A i j h0 (by rw [hsymm]; exact h0)
    · rw [h1, show ((-(-(1 : ℤ))).toNat) = 1 from by norm_num, pow_one]
      exact serre_adF_two_V A i j (hii i) h1



end SerreEStarModel

open SerreEStarModel

/-- The Cartan matrix of `e₈`. -/
abbrev serreE_E8 : Matrix (Fin 8) (Fin 8) ℤ := CartanMatrix.E₈

lemma serreE_E8_symm : ∀ i j : Fin 8, serreE_E8 i j = serreE_E8 j i := by decide

lemma serreE_E8_diag : ∀ i : Fin 8, serreE_E8 i i = 2 := by decide

lemma serreE_E8_offdiag : ∀ i j : Fin 8, i ≠ j → serreE_E8 i j = 0 ∨ serreE_E8 i j = -1 := by decide

/-- The weight `λ` used for the ⋆-model: all its components are `1`. -/
def serreE_lamOne : Fin 8 → ℂ := fun _ => 1

/-! ## The counit of the free algebra

The counit `FA (Fin 8) → ℂ` kills every word of positive length; hence it kills the two-sided ideal
`J` generated by the `f`-side Serre relations (all of which have degree `≥ 2`).  Since it sends `1`
to `1`, the class of `1` in `V = FA ⧸ J` is nonzero. -/

lemma serreE_counit_serreGen (φ : FA (Fin 8) →ₐ[ℂ] ℂ)
    (hφ : ∀ v : List (Fin 8), φ (wordElt v) = if v = [] then 1 else 0) (p q : Fin 8) :
    φ (serreGen p q) = 0 := by
  rw [serreGen, map_sub, map_mul, map_mul, hφ [p], hφ [q]]
  simp

lemma serreE_counit_serreGen2 (φ : FA (Fin 8) →ₐ[ℂ] ℂ)
    (hφ : ∀ v : List (Fin 8), φ (wordElt v) = if v = [] then 1 else 0) (p q : Fin 8) :
    φ (serreGen2 p q) = 0 := by
  rw [serreGen2, map_sub, map_mul, map_mul, hφ [p], serreE_counit_serreGen φ hφ p q]
  simp

lemma serreE_counit_gen (φ : FA (Fin 8) →ₐ[ℂ] ℂ)
    (hφ : ∀ v : List (Fin 8), φ (wordElt v) = if v = [] then 1 else 0)
    {s : FA (Fin 8)} (hs : s ∈ Gen serreE_E8) : φ s = 0 := by
  rcases hs with ⟨p, q, -, -, rfl⟩ | ⟨p, q, -, -, rfl⟩
  · exact serreE_counit_serreGen φ hφ p q
  · exact serreE_counit_serreGen2 φ hφ p q

lemma serreE_counit_mem_J (φ : FA (Fin 8) →ₐ[ℂ] ℂ)
    (hφ : ∀ v : List (Fin 8), φ (wordElt v) = if v = [] then 1 else 0)
    (x : FA (Fin 8)) (hx : x ∈ J serreE_E8) : φ x = 0 := by
  have hle : J serreE_E8 ≤ LinearMap.ker φ.toLinearMap := by
    rw [J, Submodule.span_le]
    rintro x ⟨s, hs, u, v, rfl⟩
    change φ (wordElt u * s * wordElt v) = 0
    rw [map_mul, map_mul, hφ u, hφ v, serreE_counit_gen φ hφ hs]
    split_ifs <;> ring
  exact LinearMap.mem_ker.mp (hle hx)

/-- The highest-weight vector `1 + J` of the ⋆-model is nonzero. -/
theorem serreE_mk_one_ne_zero : (Submodule.Quotient.mk (1 : FA (Fin 8)) : V serreE_E8) ≠ 0 := by
  obtain ⟨φ, hφ⟩ := Commons.Algebra.MonoidAlgebra.freeAlgebra_counit (Fin 8)
  intro h
  rw [Submodule.Quotient.mk_eq_zero] at h
  have h0 := serreE_counit_mem_J φ hφ 1 h
  rw [map_one] at h0
  exact one_ne_zero h0

/-! ## `E_k` acts nontrivially on the ⋆-model -/

lemma serreE_Eword_single_self (k : Fin 8) : Eword serreE_E8 serreE_lamOne k [k] = 1 := by
  rw [show Eword serreE_E8 serreE_lamOne k [k]
      = Lop k (Eword serreE_E8 serreE_lamOne k [])
        + (if k = k then (serreE_lamOne k - wrho serreE_E8 k ([] : List (Fin 8))) •
            wordElt ([] : List (Fin 8)) else 0) from rfl]
  simp [Eword, wrho, serreE_lamOne, wordElt_nil]

lemma serreE_Ebar_apply_wordElt (k : Fin 8) :
    Ebar serreE_E8 serreE_lamOne k (Submodule.Quotient.mk (wordElt [k] : FA (Fin 8)))
      = Submodule.Quotient.mk (1 : FA (Fin 8)) := by
  rw [Ebar_mk, Eop_apply, serreE_Eword_single_self]

lemma serreE_Ebar_ne_zero (k : Fin 8) : Ebar serreE_E8 serreE_lamOne k ≠ 0 := by
  intro h
  have h1 := serreE_Ebar_apply_wordElt k
  rw [h, LinearMap.zero_apply] at h1
  exact serreE_mk_one_ne_zero h1.symm

/-! ## The main theorem -/

/-- The image of the `E`-generator `E_k` in the Serre-constructed `e₈` over `ℂ` is nonzero.

This is a nontriviality statement: it needs a module (representation) of `LieAlgebra.e₈ ℂ` on which
`E_k` acts nontrivially.  The canonical such module is the "⋆-model" `FA ⧸ J` (the Verma module
`U(𝔫⁻)`), where `FA = MonoidAlgebra ℂ (FreeMonoid (Fin 8))` is the free associative algebra on the
eight `F`-letters, `J` is the two-sided ideal generated by the `f`-side Serre relations, and the
operators `Hbar/Ebar/Lbar` of `Submission.StarQuotient` (all definitions available, fully proved, in
`Submission/StarModule.lean`, `Submission/StarDerivation.lean`, `Submission/StarQuotient.lean` --
only Mathlib imports, so their content may be copied verbatim into this file, renamed to a fresh
namespace) satisfy the six Serre families, giving `act lam : LieAlgebra.e₈ ℂ →ₗ⁅ℂ⁆ Module.End ℂ V`
(`Submission.VermaNonzero.act`).  Taking `lam : Fin 8 → ℂ` with `lam k = 1` and noting
`Ebar E8 lam k (Submodule.Quotient.mk (wordElt [k])) = Submodule.Quotient.mk (Eword E8 lam k [k])
= Submodule.Quotient.mk (lam k • 1) = Submodule.Quotient.mk 1 ≠ 0`
(`Submission.VermaNonzero.mk_one_ne_zero`, via the augmentation `aug` of `FA` and
`Commons.Algebra.MonoidAlgebra.freeAlgebra_counit`) gives `Ebar k ≠ 0`, hence `E_k ≠ 0`. -/
theorem e8_serreE_ne_zero (k : Fin 8) :
    (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)
      (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E k)) : LieAlgebra.e₈ ℂ) ≠ 0 := by
  intro h
  obtain ⟨φ, hφH, hφE, hφF⟩ := liftOfSerrePresentation (R := ℂ) (B := Fin 8) CartanMatrix.E₈
    (Hbar serreE_E8 serreE_lamOne) (Ebar serreE_E8 serreE_lamOne) (Lbar serreE_E8)
    (fun i j => lie_Hbar_Hbar serreE_E8 serreE_lamOne i j)
    (fun i j => lie_Hbar_Ebar serreE_E8 serreE_lamOne i j)
    (fun i j => lie_Hbar_Lbar serreE_E8 serreE_lamOne i j)
    (fun i j => lie_Ebar_Lbar serreE_E8 serreE_lamOne i j)
    (fun i j => adE_zero serreE_E8 serreE_lamOne i j serreE_E8_symm serreE_E8_diag serreE_E8_offdiag)
    (fun i j => adF_zero serreE_E8 i j serreE_E8_symm serreE_E8_diag serreE_E8_offdiag)
  have h2 : Ebar serreE_E8 serreE_lamOne k = 0 := by
    have h3 : φ (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)
        (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E k))) = φ 0 := by rw [h]
    rwa [hφE k, map_zero] at h3
  exact serreE_Ebar_ne_zero k h2

end Commons.Algebra.Lie.SerreConstruction