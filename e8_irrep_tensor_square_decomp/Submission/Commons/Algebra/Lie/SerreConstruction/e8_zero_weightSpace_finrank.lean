import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Lie.SerreConstruction
import Mathlib.Algebra.Lie.Quotient
import Mathlib.Algebra.Lie.UniversalEnveloping
import Mathlib.Data.List.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.Tactic
import Submission.Commons.Algebra.Lie.SerreConstruction.liftOfSerrePresentation
import Submission.Commons.Algebra.Lie.SerreConstruction.eq_top_of_lieSubalgebra_of_generators
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_iota_injective
import Submission.Commons.Algebra.Lie.SerreConstruction.e8_eq_sup_cartan_positive_negative
import Submission.Commons.LinearAlgebra.exists_separating_functional
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_posDef
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false


set_option backward.isDefEq.respectTransparency false
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 100] LieAlgebra.ofAssociativeAlgebra
set_option linter.unusedSectionVars false

noncomputable section
open scoped BigOperators
namespace Submission.StarModule




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

end Submission.StarModule



set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
noncomputable section
open scoped BigOperators
namespace Submission.StarModule

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

end Submission.StarModule

namespace Submission.StarModule

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

end Submission.StarModule



set_option backward.isDefEq.respectTransparency false
attribute [local instance 100] LieRing.ofAssociativeRing
attribute [local instance 100] LieAlgebra.ofAssociativeAlgebra
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

noncomputable section
open scoped BigOperators

namespace Submission.StarQuotient

open Submission.StarModule

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


end Submission.StarQuotient



namespace Commons.Algebra.Lie.SerreConstruction

open CartanMatrix

/-- The Cartan matrix of `E₈`. -/
abbrev E8 : Matrix (Fin 8) (Fin 8) ℤ := CartanMatrix.E₈

abbrev L8 : Type := LieAlgebra.e₈ ℂ

abbrev FL8 : Type := FreeLieAlgebra ℂ (CartanMatrix.Generators (Fin 8))

abbrev lieJ : LieIdeal ℂ FL8 := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈

noncomputable def SerreH (i : Fin 8) : L8 :=
  LieSubmodule.Quotient.mk (N := lieJ) (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i))

noncomputable def SerreE (i : Fin 8) : L8 :=
  LieSubmodule.Quotient.mk (N := lieJ) (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i))

noncomputable def SerreF (i : Fin 8) : L8 :=
  LieSubmodule.Quotient.mk (N := lieJ) (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i))

lemma E8_symm : ∀ i j : Fin 8, E8 i j = E8 j i := by decide
lemma E8_diag : ∀ i : Fin 8, E8 i i = 2 := by decide
lemma E8_offdiag : ∀ i j : Fin 8, i ≠ j → E8 i j = 0 ∨ E8 i j = -1 := by decide

/-! ### The Serre relations in `e₈` -/

lemma HH_mem_lieJ (i j : Fin 8) :
    CartanMatrix.Relations.HH ℂ (i, j) ∈ (lieJ : Submodule ℂ FL8) :=
  LieSubmodule.subset_lieSpan (by simp [CartanMatrix.Relations.toSet] : _ ∈ _)

lemma HE_mem_lieJ (i j : Fin 8) :
    CartanMatrix.Relations.HE ℂ CartanMatrix.E₈ (i, j) ∈ (lieJ : Submodule ℂ FL8) :=
  LieSubmodule.subset_lieSpan (by simp [CartanMatrix.Relations.toSet] : _ ∈ _)

lemma HF_mem_lieJ (i j : Fin 8) :
    CartanMatrix.Relations.HF ℂ CartanMatrix.E₈ (i, j) ∈ (lieJ : Submodule ℂ FL8) :=
  LieSubmodule.subset_lieSpan (by simp [CartanMatrix.Relations.toSet] : _ ∈ _)

lemma EF_mem_lieJ (i j : Fin 8) :
    CartanMatrix.Relations.EF ℂ (i, j) ∈ (lieJ : Submodule ℂ FL8) :=
  LieSubmodule.subset_lieSpan (by simp [CartanMatrix.Relations.toSet] : _ ∈ _)

lemma serreLie_HH (i j : Fin 8) : ⁅SerreH i, SerreH j⁆ = 0 := by
  unfold SerreH
  change LieSubmodule.Quotient.mk (N := lieJ) ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i),
      FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H j)⁆ = 0
  rw [LieSubmodule.Quotient.mk_eq_zero']
  have hdeq : ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i),
      FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H j)⁆ =
      CartanMatrix.Relations.HH ℂ (i, j) := rfl
  rw [hdeq]
  exact HH_mem_lieJ i j

lemma serreLie_H_E (i j : Fin 8) : ⁅SerreH i, SerreE j⁆ = (E8 i j) • SerreE j := by
  unfold SerreH SerreE
  change LieSubmodule.Quotient.mk (N := lieJ) ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i),
      FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E j)⁆ =
      (E8 i j) • LieSubmodule.Quotient.mk (N := lieJ) (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E j))
  have hz : (E8 i j) • LieSubmodule.Quotient.mk (N := lieJ)
        (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E j)) =
      LieSubmodule.Quotient.mk (N := lieJ) ((E8 i j) • FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E j)) := by
    simpa using (map_zsmul (f := Submodule.mkQ (lieJ.toSubmodule)) (E8 i j)
      (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E j)))
  rw [hz, ← sub_eq_zero]
  change LieSubmodule.Quotient.mk (N := lieJ)
      (⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i), FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E j)⁆
        - (E8 i j) • FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E j)) = 0
  rw [LieSubmodule.Quotient.mk_eq_zero']
  have hdeq : CartanMatrix.Relations.HE ℂ CartanMatrix.E₈ (i, j) =
      ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i), FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E j)⁆
        - (E8 i j) • FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E j) := rfl
  rw [← hdeq]
  exact HE_mem_lieJ i j

lemma serreLie_H_F (i j : Fin 8) : ⁅SerreH i, SerreF j⁆ = (-(E8 i j)) • SerreF j := by
  unfold SerreH SerreF
  change LieSubmodule.Quotient.mk (N := lieJ) ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i),
      FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)⁆ =
      (-(E8 i j)) • LieSubmodule.Quotient.mk (N := lieJ) (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j))
  have hz : (-(E8 i j)) • LieSubmodule.Quotient.mk (N := lieJ)
        (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)) =
      LieSubmodule.Quotient.mk (N := lieJ) ((-(E8 i j)) • FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)) := by
    simpa using (map_zsmul (f := Submodule.mkQ (lieJ.toSubmodule)) (-(E8 i j))
      (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)))
  rw [hz, ← sub_eq_zero]
  change LieSubmodule.Quotient.mk (N := lieJ)
      (⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i), FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)⁆
        - (-(E8 i j)) • FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)) = 0
  rw [LieSubmodule.Quotient.mk_eq_zero']
  have hdeq : CartanMatrix.Relations.HF ℂ CartanMatrix.E₈ (i, j) =
      ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i), FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)⁆
        + (E8 i j) • FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j) := rfl
  have : ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i), FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)⁆
        - (-(E8 i j)) • FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j) =
      CartanMatrix.Relations.HF ℂ CartanMatrix.E₈ (i, j) := by
    rw [hdeq]; module
  rw [this]
  exact HF_mem_lieJ i j

lemma serreLie_E_F (i j : Fin 8) : ⁅SerreE i, SerreF j⁆ = if i = j then SerreH i else 0 := by
  unfold SerreE SerreF SerreH
  by_cases h : i = j
  · subst h
    simp only [if_pos rfl]
    change LieSubmodule.Quotient.mk (N := lieJ) ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i),
        FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i)⁆ =
        LieSubmodule.Quotient.mk (N := lieJ) (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i))
    rw [← sub_eq_zero]
    change LieSubmodule.Quotient.mk (N := lieJ)
        (⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i), FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i)⁆
          - FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i)) = 0
    rw [LieSubmodule.Quotient.mk_eq_zero']
    have hdeq : CartanMatrix.Relations.EF ℂ (i, i) =
        ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i), FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i)⁆
          - FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i) := by
      simp [CartanMatrix.Relations.EF]
    rw [← hdeq]
    exact EF_mem_lieJ i i
  · simp only [if_neg h]
    change LieSubmodule.Quotient.mk (N := lieJ) ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i),
        FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)⁆ = 0
    rw [LieSubmodule.Quotient.mk_eq_zero']
    have hdeq : CartanMatrix.Relations.EF ℂ (i, j) =
        ⁅FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i), FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F j)⁆ := by
      simp [CartanMatrix.Relations.EF, h]
    rw [← hdeq]
    exact EF_mem_lieJ i j

end Commons.Algebra.Lie.SerreConstruction


namespace Commons.Algebra.Lie.SerreConstruction

open CartanMatrix
open Submission.StarQuotient
open Submission.StarModule

/-! ### Non-vanishing of the cyclic vector of the free-algebra model -/

/-- The counit of the free monoid: `1 ↦ 1`, every nonempty word `↦ 0`. -/
def counitHom : FreeMonoid (Fin 8) →* ℂ := FreeMonoid.lift fun _ : Fin 8 => (0 : ℂ)

/-- The algebra homomorphism `FA (Fin 8) → ℂ` killing every generator. -/
def aug : FA (Fin 8) →ₐ[ℂ] ℂ := MonoidAlgebra.lift ℂ ℂ (FreeMonoid (Fin 8)) counitHom

lemma aug_wordElt (v : List (Fin 8)) : aug (wordElt v) = if v = [] then 1 else 0 := by
  classical
  rw [show wordElt v = MonoidAlgebra.single (FreeMonoid.ofList v) (1 : ℂ) from rfl,
    show (aug : FA (Fin 8) → ℂ) = MonoidAlgebra.lift ℂ ℂ (FreeMonoid (Fin 8)) counitHom from rfl,
    MonoidAlgebra.lift_single, one_smul, counitHom, FreeMonoid.lift_ofList]
  by_cases hv : v = []
  · subst hv; simp
  · rw [if_neg hv]
    obtain ⟨a, t, rfl⟩ := List.exists_cons_of_ne_nil hv
    simp

lemma aug_wordElt_single (p : Fin 8) : aug (wordElt [p]) = 0 := by
  rw [aug_wordElt]; simp

lemma aug_serreGen (p q : Fin 8) : aug (serreGen p q) = 0 := by
  rw [serreGen, map_sub, map_mul, map_mul, aug_wordElt_single]
  simp

lemma aug_serreGen2 (p q : Fin 8) : aug (serreGen2 p q) = 0 := by
  rw [serreGen2, map_sub, map_mul, map_mul, aug_wordElt_single, aug_serreGen]
  simp

lemma aug_gen (s : FA (Fin 8)) (hs : s ∈ Gen E8) : aug s = 0 := by
  rcases hs with ⟨p, q, hpq, hqp, rfl⟩ | ⟨p, q, hpp, hpq, rfl⟩
  · exact aug_serreGen p q
  · exact aug_serreGen2 p q

lemma aug_mem_J (x : FA (Fin 8)) (hx : x ∈ J E8) : aug x = 0 := by
  have hle : J E8 ≤ LinearMap.ker aug.toLinearMap := by
    rw [J, Submodule.span_le]
    rintro x ⟨s, hs, u, v, rfl⟩
    change aug (wordElt u * s * wordElt v) = 0
    simp only [map_mul, aug_gen s hs, mul_zero, zero_mul]
  exact LinearMap.mem_ker.mp (hle hx)

/-- The cyclic vector `1 + J` of the free-algebra model is nonzero. -/
lemma mk_one_ne_zero : (Submodule.Quotient.mk (1 : FA (Fin 8)) : V E8) ≠ 0 := by
  intro h
  rw [mk_eq_zero_iff] at h
  have := aug_mem_J 1 h
  rw [map_one] at this
  exact one_ne_zero this

/-- The universal property of the Serre presentation applied to the ⋆-operators. -/
noncomputable def actExists (lam : Fin 8 → ℂ) :
    ∃ φ : L8 →ₗ⁅ℂ⁆ Module.End ℂ (V E8),
      (∀ i, φ (SerreH i) = Hbar E8 lam i) ∧
      (∀ i, φ (SerreE i) = Ebar E8 lam i) ∧
      (∀ i, φ (SerreF i) = Lbar E8 i) :=
  Commons.Algebra.Lie.SerreConstruction.liftOfSerrePresentation (R := ℂ) (B := Fin 8)
    CartanMatrix.E₈ (Hbar E8 lam) (Ebar E8 lam) (Lbar E8)
    (fun i j => lie_Hbar_Hbar E8 lam i j)
    (fun i j => lie_Hbar_Ebar E8 lam i j)
    (fun i j => lie_Hbar_Lbar E8 lam i j)
    (fun i j => lie_Ebar_Lbar E8 lam i j)
    (fun i j => adE_zero E8 lam i j E8_symm E8_diag E8_offdiag)
    (fun i j => adF_zero E8 i j E8_symm E8_diag E8_offdiag)

noncomputable def act (lam : Fin 8 → ℂ) : L8 →ₗ⁅ℂ⁆ Module.End ℂ (V E8) :=
  (actExists lam).choose

lemma act_H (lam : Fin 8 → ℂ) (i : Fin 8) : act lam (SerreH i) = Hbar E8 lam i :=
  (actExists lam).choose_spec.1 i

lemma act_E (lam : Fin 8 → ℂ) (i : Fin 8) : act lam (SerreE i) = Ebar E8 lam i :=
  (actExists lam).choose_spec.2.1 i

lemma act_F (lam : Fin 8 → ℂ) (i : Fin 8) : act lam (SerreF i) = Lbar E8 i :=
  (actExists lam).choose_spec.2.2 i

lemma Hbar_mk_one (lam : Fin 8 → ℂ) (i : Fin 8) :
    Hbar E8 lam i (Submodule.Quotient.mk (1 : FA (Fin 8)) : V E8)
      = lam i • (Submodule.Quotient.mk (1 : FA (Fin 8)) : V E8) := by
  rw [Hbar_mk]
  rw [show (1 : FA (Fin 8)) = wordElt [] from wordElt_nil.symm]
  rw [Hop_apply, Hword]
  have hw : wrho E8 i ([] : List (Fin 8)) = 0 := by simp [wrho]
  rw [hw, sub_zero, ← Submodule.Quotient.mk_smul, wordElt_nil]

/-- **The `H`-generators of `e₈` are linearly independent.** -/
theorem e8_H_linearIndependent :
    LinearIndependent ℂ (fun i : Fin 8 => SerreH i) := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i0
  have key : ∀ lam : Fin 8 → ℂ, (∑ j, g j * lam j) = 0 := by
    intro lam
    let psi : L8 →ₗ[ℂ] V E8 :=
      { toFun := fun x => act lam x (Submodule.Quotient.mk (1 : FA (Fin 8)) : V E8)
        map_add' := by intro a b; rw [map_add]; rfl
        map_smul' := by intro c a; rw [map_smul]; rfl }
    have hpsi : ∀ j, psi (SerreH j) = lam j • (Submodule.Quotient.mk (1 : FA (Fin 8)) : V E8) := by
      intro j
      show act lam (SerreH j) (Submodule.Quotient.mk (1 : FA (Fin 8)) : V E8) = _
      rw [act_H, Hbar_mk_one]
    have h0 : psi (∑ j, g j • SerreH j) = 0 := by rw [hg, map_zero]
    have h1 : ∑ j, g j • psi (SerreH j) = 0 := by
      simpa only [map_sum, map_smul] using h0
    simp only [hpsi] at h1
    have h3 : (∑ j, g j * lam j) • (Submodule.Quotient.mk (1 : FA (Fin 8)) : V E8) = 0 := by
      rw [Finset.sum_smul]
      rw [show (∑ j, (g j * lam j) • (Submodule.Quotient.mk (1 : FA (Fin 8)) : V E8))
          = ∑ j, g j • (lam j • (Submodule.Quotient.mk (1 : FA (Fin 8)) : V E8)) from
        Finset.sum_congr rfl (fun j _ => by rw [smul_smul])]
      exact h1
    rcases smul_eq_zero.mp h3 with h | h
    · exact h
    · exact absurd h mk_one_ne_zero
  have := key (fun j => if j = i0 then (1 : ℂ) else 0)
  simpa using this

end Commons.Algebra.Lie.SerreConstruction


namespace Commons.Algebra.Lie.SerreConstruction

open CartanMatrix
open Submission.StarQuotient
open Submission.StarModule

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-! ### Weight spaces of the adjoint action of the Cartan -/

abbrev U8 : Type := UniversalEnvelopingAlgebra ℂ L8

/-- The image of the Cartan generators in the enveloping algebra. -/
noncomputable def hh (i : Fin 8) : U8 := UniversalEnvelopingAlgebra.ι ℂ (SerreH i)

/-- The weight space of `L8` for the weight `μ`. -/
noncomputable def W (μ : Fin 8 → ℂ) : Submodule ℂ L8 :=
  ⨅ i, LinearMap.ker (LieAlgebra.ad ℂ L8 (SerreH i) - μ i • 1)

/-- The weight space of the adjoint action of the Cartan on the enveloping algebra. -/
noncomputable def uW (μ : Fin 8 → ℂ) : Submodule ℂ U8 :=
  ⨅ i, LinearMap.ker (LieAlgebra.ad ℂ U8 (hh i) - μ i • 1)

lemma mem_W_iff {μ : Fin 8 → ℂ} {x : L8} : x ∈ W μ ↔ ∀ i, ⁅SerreH i, x⁆ = μ i • x := by
  simp only [W, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero, LieAlgebra.ad_apply]

lemma mem_uW_iff {μ : Fin 8 → ℂ} {x : U8} : x ∈ uW μ ↔ ∀ i, ⁅hh i, x⁆ = μ i • x := by
  simp only [uW, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero, LieAlgebra.ad_apply]

lemma smul_mem_W {μ : Fin 8 → ℂ} {x : L8} (hx : x ∈ W μ) (c : ℂ) : c • x ∈ W μ :=
  (W μ).smul_mem c hx

lemma add_mem_W {μ : Fin 8 → ℂ} {x y : L8} (hx : x ∈ W μ) (hy : y ∈ W μ) : x + y ∈ W μ :=
  (W μ).add_mem hx hy

/-- The bracket of weight vectors has the sum of the weights. -/
lemma bracket_mem_W {μ ν : Fin 8 → ℂ} {x y : L8} (hx : x ∈ W μ) (hy : y ∈ W ν) :
    ⁅x, y⁆ ∈ W (μ + ν) := by
  rw [mem_W_iff] at hx hy ⊢
  intro i
  rw [leibniz_lie, hx i, hy i, smul_lie, lie_smul, Pi.add_apply, add_smul]

/-- Distinct weight spaces intersect trivially. -/
lemma W_disjoint {μ ν : Fin 8 → ℂ} (h : μ ≠ ν) : W μ ⊓ W ν = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf] at hx
  have hx1 := mem_W_iff.mp hx.1
  have hx2 := mem_W_iff.mp hx.2
  by_contra hx0
  exact h (funext fun i => by
    have h3 : (μ i - ν i) • x = 0 := by
      rw [sub_smul, ← hx1 i, hx2 i, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact sub_eq_zero.mp h4
    · exact absurd h4 hx0)

lemma SerreH_mem_W_zero (i : Fin 8) : SerreH i ∈ W 0 := by
  rw [mem_W_iff]
  intro j
  rw [serreLie_HH, Pi.zero_apply, zero_smul]

lemma serreE_mem_W (j : Fin 8) : SerreE j ∈ W (fun i => (E8 i j : ℂ)) := by
  rw [mem_W_iff]
  intro i
  simpa only [Int.cast_smul_eq_zsmul] using serreLie_H_E i j

lemma serreF_mem_W (j : Fin 8) : SerreF j ∈ W (fun i => ((-(E8 i j) : ℤ) : ℂ)) := by
  rw [mem_W_iff]
  intro i
  simpa only [Int.cast_smul_eq_zsmul] using serreLie_H_F i j

end Commons.Algebra.Lie.SerreConstruction


namespace Commons.Algebra.Lie.SerreConstruction

open CartanMatrix
open Submission.StarQuotient
open Submission.StarModule

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-! ### The `wdelta`-grading of the free algebra -/

/-- The multiplicity vector of a word. -/
def counts (v : List (Fin 8)) : Fin 8 → ℕ := fun j => v.count j

/-- The integer eigenvalue of `wdelta i` on the layer of multiplicity `n`. -/
noncomputable def cvalZ (n : Fin 8 → ℕ) (i : Fin 8) : ℤ :=
  ∑ j, (n j : ℤ) * E8 i j

/-- The eigenvalue of `wdelta i` on the layer of multiplicity `n`. -/
noncomputable def cval (n : Fin 8 → ℕ) (i : Fin 8) : ℂ := (cvalZ n i : ℂ)

lemma cval_zero (i : Fin 8) : cval 0 i = 0 := by simp [cval, cvalZ]
lemma cval_add (n m : Fin 8 → ℕ) (i : Fin 8) :
    cval (n + m) i = cval n i + cval m i := by
  simp only [cval, cvalZ, Pi.add_apply]
  push_cast
  trans ∑ j, (((n j : ℤ) : ℂ) * (E8 i j : ℂ) + ((m j : ℤ) : ℂ) * (E8 i j : ℂ))
  · exact Finset.sum_congr rfl (fun j _ => by push_cast; ring)
  · rw [Finset.sum_add_distrib]
    simp

/-- The map `n ↦ cval n` is injective. -/
lemma cval_injective : Function.Injective cval := by
  intro n m h
  have hZ : cvalZ n = cvalZ m := by
    funext i
    have := congrFun h i
    simpa only [cval, Int.cast_inj] using this
  have hmul : ∀ i, ∑ j, ((n j : ℤ) - (m j : ℤ)) * E8 i j = 0 := by
    intro i
    have := congrFun hZ i
    simp only [cvalZ, sub_mul, Finset.sum_sub_distrib] at this ⊢
    linarith [this]
  have hq : ∀ i, ∑ j, (((n j : ℚ) - (m j : ℚ))) * (E8 i j : ℚ) = 0 := by
    intro i
    have := hmul i
    have : ((∑ j, ((n j : ℤ) - (m j : ℤ)) * E8 i j : ℤ) : ℚ) = 0 := by rw [this]; simp
    push_cast at this
    simpa [sub_mul, Finset.sum_sub_distrib] using this
  by_contra hne
  have hv : (fun j => (n j : ℚ) - (m j : ℚ)) ≠ 0 := by
    intro hv
    apply hne
    funext j
    have := congrFun hv j
    simp only [Pi.zero_apply] at this
    have : (n j : ℚ) = (m j : ℚ) := by linarith
    exact_mod_cast this
  have hpos := Commons.LinearAlgebra.Matrix.Cartan.E8_posDef
    (fun j => (n j : ℚ) - (m j : ℚ)) hv
  have hzero : ∑ i, ∑ j, ((n i : ℚ) - (m i : ℚ)) * (E8 i j : ℚ) *
      ((n j : ℚ) - (m j : ℚ)) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    calc ∑ j, ((n i : ℚ) - (m i : ℚ)) * (E8 i j : ℚ) * ((n j : ℚ) - (m j : ℚ))
        = ((n i : ℚ) - (m i : ℚ)) *
            ∑ j, ((n j : ℚ) - (m j : ℚ)) * (E8 i j : ℚ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = 0 := by rw [hq i, mul_zero]
  linarith

/-- The layer of `FA` of multiplicity `n`: the span of the words with multiplicity vector `n`. -/
noncomputable def FAeig (n : Fin 8 → ℕ) : Submodule ℂ (FA (Fin 8)) :=
  Submodule.span ℂ {y | ∃ u : List (Fin 8), counts u = n ∧ y = wordElt u}

lemma wordElt_mem_FAeig (u : List (Fin 8)) : wordElt u ∈ FAeig (counts u) :=
  Submodule.subset_span ⟨u, rfl, rfl⟩

lemma wrho_eq_cval (i : Fin 8) (v : List (Fin 8)) : wrho E8 i v = cval (counts v) i := by
  have key : (v.map (fun t => (E8 i t : ℂ))).sum
      = ∑ j, ((v.count j : ℕ) : ℂ) * (E8 i j : ℂ) := by
    rw [Finset.sum_list_map_count v (fun t => (E8 i t : ℂ))]
    trans ∑ a ∈ v.toFinset, ((v.count a : ℕ) : ℂ) * (E8 i a : ℂ)
    · exact Finset.sum_congr rfl (fun a _ => by rw [nsmul_eq_mul])
    · exact Finset.sum_subset (Finset.subset_univ _) (fun j _ hj => by
        rw [List.count_eq_zero_of_not_mem (fun h => hj (List.mem_toFinset.mpr h))]
        simp)
  rw [show wrho E8 i v = (v.map (fun t => (E8 i t : ℂ))).sum from rfl, key]
  simp only [cval, cvalZ, counts]
  push_cast
  rfl

lemma wdelta_wordElt (i : Fin 8) (v : List (Fin 8)) :
    wdelta E8 i (wordElt v) = cval (counts v) i • wordElt v := by
  rw [wdelta_apply, wrho_eq_cval i v]

/-- On the layer `n`, `wdelta i` acts by the scalar `cval n i`. -/
lemma wdelta_eq_of_mem_FAeig {n : Fin 8 → ℕ} {y : FA (Fin 8)} (hy : y ∈ FAeig n)
    (i : Fin 8) : wdelta E8 i y = cval n i • y := by
  refine Submodule.span_induction (p := fun y _ => wdelta E8 i y = cval n i • y) ?_ ?_ ?_ ?_ hy
  · rintro y ⟨u, hu, hyu⟩
    rw [hyu, ← hu, wdelta_wordElt]
  · rw [map_zero, smul_zero]
  · intro a b _ _ ha hb
    rw [map_add, ha, hb, smul_add]
  · intro c a _ ha
    rw [map_smul, ha]
    exact smul_comm c (cval n i) a

/-- The layers are multiplicative. -/
lemma mul_mem_FAeig {n m : Fin 8 → ℕ} {x y : FA (Fin 8)} (hx : x ∈ FAeig n)
    (hy : y ∈ FAeig m) : x * y ∈ FAeig (n + m) := by
  refine Submodule.span_induction (p := fun z _ => z * y ∈ FAeig (n + m)) ?_ ?_ ?_ ?_ hx
  · rintro z ⟨u, hu, hzu⟩
    rw [hzu]
    refine Submodule.span_induction (p := fun w' _ => wordElt u * w' ∈ FAeig (n + m)) ?_ ?_ ?_ ?_ hy
    · rintro w' ⟨w, hw, hww⟩
      rw [hww, wordElt_mul]
      refine Submodule.subset_span ⟨u ++ w, ?_, rfl⟩
      ext j
      simp only [List.count_append, counts, Pi.add_apply]
      rw [show u.count j = n j from congrFun hu j, show w.count j = m j from congrFun hw j]
    · rw [mul_zero]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb; rw [mul_add]; exact Submodule.add_mem _ ha hb
    · intro c a _ ha; rw [mul_smul_comm]; exact Submodule.smul_mem _ c ha
  · rw [zero_mul]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [add_mul]; exact Submodule.add_mem _ ha hb
  · intro c a _ ha; rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha

lemma FAeig_zero_eq : FAeig 0 = Submodule.span ℂ ({1} : Set (FA (Fin 8))) := by
  have h0 : (0 : Fin 8 → ℕ) = counts ([] : List (Fin 8)) := by
    funext j; simp [counts]
  rw [h0]
  refine le_antisymm ?_ ?_
  · rw [FAeig, Submodule.span_le]
    rintro y ⟨u, hu, hyu⟩
    have hnil : u = [] := by
      refine List.eq_nil_iff_forall_not_mem.mpr fun a ha => ?_
      have h := congrFun hu a
      simp only [counts] at h
      exact absurd ha (List.count_eq_zero.mp h)
    rw [hyu, hnil, wordElt_nil]
    exact Submodule.subset_span rfl
  · rw [Submodule.span_singleton_le_iff_mem, FAeig]
    exact Submodule.subset_span ⟨[], rfl, wordElt_nil.symm⟩

/-- The Lie subalgebra generated by the free-algebra generators. -/
noncomputable def LieGen : LieSubalgebra ℂ (FA (Fin 8)) :=
  LieSubalgebra.lieSpan ℂ (FA (Fin 8)) (Set.range (fun j : Fin 8 => wordElt [j]))

lemma wordElt_mem_LieGen (j : Fin 8) : wordElt [j] ∈ LieGen :=
  LieSubalgebra.subset_lieSpan (Set.mem_range_self j)

/-- The kernel of the augmentation is a Lie subalgebra. -/
noncomputable def kerAugLie : LieSubalgebra ℂ (FA (Fin 8)) where
  carrier := LinearMap.ker (aug : FA (Fin 8) →ₗ[ℂ] ℂ)
  add_mem' := fun {x y} hx hy =>
    LinearMap.mem_ker.mpr (by rw [map_add, LinearMap.mem_ker.mp hx, LinearMap.mem_ker.mp hy, add_zero])
  zero_mem' := LinearMap.mem_ker.mpr (map_zero _)
  smul_mem' := fun c x hx =>
    LinearMap.mem_ker.mpr (by rw [map_smul, LinearMap.mem_ker.mp hx, smul_zero])
  lie_mem' := by
    intro x y hx hy
    have hx' : (aug : FA (Fin 8) →ₐ[ℂ] ℂ) x = 0 := LinearMap.mem_ker.mp hx
    have hy' : (aug : FA (Fin 8) →ₐ[ℂ] ℂ) y = 0 := LinearMap.mem_ker.mp hy
    show (aug : FA (Fin 8) →ₐ[ℂ] ℂ) ⁅x, y⁆ = 0
    rw [Ring.lie_def, map_sub, map_mul, map_mul, hx', hy']
    simp

lemma LieGen_le_kerAug : LieGen ≤ kerAugLie := by
  rw [show LieGen = LieSubalgebra.lieSpan ℂ (FA (Fin 8))
      (Set.range (fun j : Fin 8 => wordElt [j])) from rfl]
  refine LieSubalgebra.lieSpan_le.mpr ?_
  rintro x ⟨j, rfl⟩
  exact LinearMap.mem_ker.mpr (aug_wordElt_single j)

lemma one_notMem_LieGen : (1 : FA (Fin 8)) ∉ LieGen := by
  intro h
  have h' : (aug : FA (Fin 8) →ₐ[ℂ] ℂ) 1 = 0 := LinearMap.mem_ker.mp (LieGen_le_kerAug h)
  rw [map_one] at h'
  exact one_ne_zero h'

lemma disjoint_lieGen_FAeig_zero : (LieGen : Submodule ℂ (FA (Fin 8))) ⊓ FAeig 0 = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf, FAeig_zero_eq] at hx
  obtain ⟨hx1, hx2⟩ := hx
  rw [Submodule.mem_span_singleton] at hx2
  obtain ⟨c, hc⟩ := hx2
  have h : (aug : FA (Fin 8) →ₐ[ℂ] ℂ) x = 0 := LinearMap.mem_ker.mp (LieGen_le_kerAug hx1)
  rw [← hc, map_smul, map_one, smul_eq_mul, mul_one] at h
  rw [← hc, h, zero_smul]

/-- The sum of the layers of `LieGen`. -/
noncomputable def LieGenLayersSub : Submodule ℂ (FA (Fin 8)) :=
  ⨆ n : Fin 8 → ℕ, (LieGen : Submodule ℂ (FA (Fin 8))) ⊓ FAeig n

lemma lie_mem_layers_left {n : Fin 8 → ℕ} {x : FA (Fin 8)}
    (hx : x ∈ (LieGen : Submodule ℂ (FA (Fin 8))) ⊓ FAeig n) :
    ∀ {y : FA (Fin 8)}, y ∈ LieGenLayersSub → ⁅x, y⁆ ∈ LieGenLayersSub := by
  intro y hy
  simp only [LieGenLayersSub] at hy ⊢
  refine Submodule.iSup_induction (fun m => (LieGen : Submodule ℂ (FA (Fin 8))) ⊓ FAeig m) hy
    (motive := fun y => ⁅x, y⁆ ∈ ⨆ m, (LieGen : Submodule ℂ (FA (Fin 8))) ⊓ FAeig m)
    (fun m y hy => ?_) (by rw [lie_zero]; exact Submodule.zero_mem _)
    (fun y₁ y₂ h₁ h₂ => by rw [lie_add]; exact Submodule.add_mem _ h₁ h₂)
  refine Submodule.mem_iSup_of_mem (n + m) ⟨LieGen.lie_mem hx.1 hy.1, ?_⟩
  rw [Ring.lie_def]
  exact (FAeig (n + m)).sub_mem (mul_mem_FAeig hx.2 hy.2)
    (by simpa [add_comm] using mul_mem_FAeig hy.2 hx.2)

noncomputable def LieGenLayers : LieSubalgebra ℂ (FA (Fin 8)) where
  carrier := LieGenLayersSub
  add_mem' := fun ha hb => LieGenLayersSub.add_mem ha hb
  zero_mem' := LieGenLayersSub.zero_mem
  smul_mem' := fun c _ ha => LieGenLayersSub.smul_mem c ha
  lie_mem' := by
    intro x y hx hy
    simp only [LieGenLayersSub] at hx hy ⊢
    refine Submodule.iSup_induction (fun n => (LieGen : Submodule ℂ (FA (Fin 8))) ⊓ FAeig n) hx
      (motive := fun x => ⁅x, y⁆ ∈ ⨆ n, (LieGen : Submodule ℂ (FA (Fin 8))) ⊓ FAeig n)
      (fun n x hx => ?_) (by rw [zero_lie]; exact Submodule.zero_mem _)
      (fun x₁ x₂ h₁ h₂ => by rw [add_lie]; exact Submodule.add_mem _ h₁ h₂)
    exact lie_mem_layers_left hx hy

lemma lieGen_le_layers : LieGen ≤ LieGenLayers := by
  rw [show LieGen = LieSubalgebra.lieSpan ℂ (FA (Fin 8))
      (Set.range (fun j : Fin 8 => wordElt [j])) from rfl]
  refine LieSubalgebra.lieSpan_le.mpr ?_
  rintro x ⟨j, rfl⟩
  exact Submodule.mem_iSup_of_mem (counts [j]) ⟨wordElt_mem_LieGen j, wordElt_mem_FAeig [j]⟩

lemma layers_le_lieGen_sub : LieGenLayersSub ≤ (LieGen : Submodule ℂ (FA (Fin 8))) :=
  iSup_le_iff.mpr (fun _ => inf_le_left)

lemma layers_le_lieGen : LieGenLayers ≤ LieGen := layers_le_lieGen_sub

lemma lieGenLayers_eq : LieGenLayers = LieGen :=
  le_antisymm layers_le_lieGen lieGen_le_layers

end Commons.Algebra.Lie.SerreConstruction


namespace Commons.Algebra.Lie.SerreConstruction

open CartanMatrix
open Submission.StarQuotient
open Submission.StarModule

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-! ### The general separation lemma for joint weight spaces -/

/-- A finite sum of eigenvectors of a family of operators, all with distinct weights separated by a
linear functional and all different from the weight of the sum, is zero. -/
theorem joint_eigenspace_sum_eq_zero {K M σ ι : Type*} [Field K] [AddCommGroup M]
    [Module K M] [Fintype ι] [Fintype σ]
    (T : ι → Module.End K M) (c : ι → K) (w : σ → ι → K) (x : σ → M) (ν : ι → K)
    (hsep : Function.Injective (fun o : Option σ => match o with
      | some m => ∑ i, c i * w m i | none => ∑ i, c i * ν i))
    (hx : ∀ m, ∀ i, T i (x m) = w m i • x m)
    (hsum : ∀ i, T i (∑ m, x m) = ν i • (∑ m, x m)) : ∀ m, x m = 0 := by
  classical
  let Tc : Module.End K M := ∑ i, c i • T i
  have hTc : ∀ (μ : ι → K) (y : M), (∀ i, T i y = μ i • y) →
      Tc y = (∑ i, c i * μ i) • y := by
    intro μ y hy
    have h1 : Tc y = ∑ i, c i • (T i y) := by simp [Tc]
    rw [h1]
    simp only [hy, smul_smul]
    rw [← Finset.sum_smul]
  let lab : Option σ → K := fun o => match o with
    | some m => ∑ i, c i * w m i
    | none => ∑ i, c i * ν i
  have hind : iSupIndep (fun o : Option σ => Tc.eigenspace (lab o)) :=
    (Module.End.eigenspaces_iSupIndep Tc).comp hsep
  have hiff := (iSupIndep_iff_finsetSum_eq_imp_eq
    (fun o : Option σ => Tc.eigenspace (lab o))).mp hind
  let f : Option σ → M := fun o => match o with | some m => x m | none => 0
  let g : Option σ → M := fun o => match o with | some _ => 0 | none => ∑ m, x m
  have hfmem : ∀ o ∈ (Finset.univ : Finset (Option σ)),
      f o ∈ Tc.eigenspace (lab o) ∧ g o ∈ Tc.eigenspace (lab o) := by
    intro o _
    match o with
    | some m =>
        refine ⟨?_, ?_⟩
        · rw [Module.End.mem_eigenspace_iff]
          exact (hTc (w m) (x m) (hx m)).trans rfl
        · rw [Module.End.mem_eigenspace_iff]; simp [g]
    | none =>
        refine ⟨?_, ?_⟩
        · rw [Module.End.mem_eigenspace_iff]; simp [f]
        · rw [Module.End.mem_eigenspace_iff]
          exact (hTc ν (∑ m, x m) hsum).trans rfl
  have hsum_eq : ∑ o, f o = ∑ o, g o := by
    simp [Fintype.sum_option, f, g]
  have hres := hiff (Finset.univ : Finset (Option σ)) f g hfmem hsum_eq
  intro m
  exact hres (some m) (Finset.mem_univ _)

end Commons.Algebra.Lie.SerreConstruction


namespace Commons.Algebra.Lie.SerreConstruction

open CartanMatrix
open Submission.StarQuotient
open Submission.StarModule

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-- The composite `⁅x, y * z⁆ = ⁅x,y⁆ * z + y * ⁅x,z⁆` in the commutator Lie structure. -/
private lemma comm_mul (x y z : U8) : ⁅x, y * z⁆ = ⁅x, y⁆ * z + y * ⁅x, z⁆ := by
  rw [Ring.lie_def, Ring.lie_def, Ring.lie_def]; noncomm_ring

/-- The algebra homomorphism `FA → U(e₈)` sending the generators to the `E`-generators. -/
noncomputable def phi : FA (Fin 8) →ₐ[ℂ] U8 :=
  MonoidAlgebra.lift ℂ U8 (FreeMonoid (Fin 8))
    (FreeMonoid.lift (fun j : Fin 8 => UniversalEnvelopingAlgebra.ι ℂ (SerreE j)))

/-- The algebra homomorphism `FA → U(e₈)` sending the generators to the `F`-generators. -/
noncomputable def phiF : FA (Fin 8) →ₐ[ℂ] U8 :=
  MonoidAlgebra.lift ℂ U8 (FreeMonoid (Fin 8))
    (FreeMonoid.lift (fun j : Fin 8 => UniversalEnvelopingAlgebra.ι ℂ (SerreF j)))

lemma phi_wordElt (v : List (Fin 8)) :
    phi (wordElt v) = (v.map (fun t => UniversalEnvelopingAlgebra.ι ℂ (SerreE t))).prod := by
  rw [show wordElt v = MonoidAlgebra.single (FreeMonoid.ofList v) (1 : ℂ) from rfl,
    show (phi : FA (Fin 8) → U8) =
      MonoidAlgebra.lift ℂ U8 (FreeMonoid (Fin 8))
        (FreeMonoid.lift (fun j : Fin 8 => UniversalEnvelopingAlgebra.ι ℂ (SerreE j))) from rfl,
    MonoidAlgebra.lift_single, one_smul, FreeMonoid.lift_ofList]

lemma phiF_wordElt (v : List (Fin 8)) :
    phiF (wordElt v) = (v.map (fun t => UniversalEnvelopingAlgebra.ι ℂ (SerreF t))).prod := by
  rw [show wordElt v = MonoidAlgebra.single (FreeMonoid.ofList v) (1 : ℂ) from rfl,
    show (phiF : FA (Fin 8) → U8) =
      MonoidAlgebra.lift ℂ U8 (FreeMonoid (Fin 8))
        (FreeMonoid.lift (fun j : Fin 8 => UniversalEnvelopingAlgebra.ι ℂ (SerreF j))) from rfl,
    MonoidAlgebra.lift_single, one_smul, FreeMonoid.lift_ofList]

lemma hh_eq (i : Fin 8) : hh i = UniversalEnvelopingAlgebra.ι ℂ (SerreH i) := rfl

lemma adU_E_single (i a : Fin 8) :
    ⁅hh i, UniversalEnvelopingAlgebra.ι ℂ (SerreE a)⁆
      = (E8 i a : ℂ) • UniversalEnvelopingAlgebra.ι ℂ (SerreE a) := by
  rw [hh_eq, ← LieHom.map_lie (f := UniversalEnvelopingAlgebra.ι ℂ) (SerreH i) (SerreE a),
    serreLie_H_E]
  rw [show (E8 i a) • SerreE a = ((E8 i a : ℤ) : ℂ) • SerreE a from by
    rw [Int.cast_smul_eq_zsmul]]
  rw [map_smul]

lemma adU_F_single (i a : Fin 8) :
    ⁅hh i, UniversalEnvelopingAlgebra.ι ℂ (SerreF a)⁆
      = (-(E8 i a : ℂ)) • UniversalEnvelopingAlgebra.ι ℂ (SerreF a) := by
  rw [hh_eq, ← LieHom.map_lie (f := UniversalEnvelopingAlgebra.ι ℂ) (SerreH i) (SerreF a),
    serreLie_H_F]
  rw [show (-(E8 i a)) • SerreF a = ((-(E8 i a) : ℤ) : ℂ) • SerreF a from by
    rw [Int.cast_smul_eq_zsmul]]
  rw [map_smul, Int.cast_neg]

lemma adU_prod_aux (x : U8) (g : Fin 8 → U8) (c : Fin 8 → ℂ)
    (hc : ∀ a, ⁅x, g a⁆ = c a • g a) (v : List (Fin 8)) :
    ⁅x, (v.map g).prod⁆ = (v.map c).sum • (v.map g).prod := by
  induction v with
  | nil =>
      rw [List.map_nil, List.map_nil, List.prod_nil, List.sum_nil, zero_smul, Ring.lie_def, mul_one,
        one_mul, sub_self]
  | cons a t ih =>
      rw [List.map_cons, List.map_cons, List.prod_cons, List.sum_cons, comm_mul, hc a, ih,
        smul_mul_assoc, mul_smul_comm, ← add_smul]

lemma adU_prod (i : Fin 8) (v : List (Fin 8)) :
    ⁅hh i, (v.map (fun t => UniversalEnvelopingAlgebra.ι ℂ (SerreE t))).prod⁆
      = (v.map (fun t => (E8 i t : ℂ))).sum •
          (v.map (fun t => UniversalEnvelopingAlgebra.ι ℂ (SerreE t))).prod :=
  adU_prod_aux (hh i) (fun t => UniversalEnvelopingAlgebra.ι ℂ (SerreE t))
    (fun a => (E8 i a : ℂ)) (fun a => adU_E_single i a) v

lemma adU_prod_F (i : Fin 8) (v : List (Fin 8)) :
    ⁅hh i, (v.map (fun t => UniversalEnvelopingAlgebra.ι ℂ (SerreF t))).prod⁆
      = (v.map (fun t => (-(E8 i t) : ℂ))).sum •
          (v.map (fun t => UniversalEnvelopingAlgebra.ι ℂ (SerreF t))).prod :=
  adU_prod_aux (hh i) (fun t => UniversalEnvelopingAlgebra.ι ℂ (SerreF t))
    (fun a => (-(E8 i a) : ℂ)) (fun a => adU_F_single i a) v

lemma sum_neg_map (v : List (Fin 8)) (f : Fin 8 → ℂ) :
    (v.map (fun t => - f t)).sum = -(v.map f).sum := by
  induction v with
  | nil => simp
  | cons a t ih => simp [ih, add_comm]

lemma phi_wdelta_wordElt (i : Fin 8) (v : List (Fin 8)) :
    ⁅hh i, phi (wordElt v)⁆ = phi (wdelta E8 i (wordElt v)) := by
  rw [phi_wordElt, wdelta_apply, map_smul (f := phi), phi_wordElt]
  exact adU_prod i v

lemma phiF_wdelta_wordElt (i : Fin 8) (v : List (Fin 8)) :
    ⁅hh i, phiF (wordElt v)⁆ = phiF (-(wdelta E8 i (wordElt v))) := by
  have hw : wdelta E8 i (wordElt v) = wrho E8 i v • wordElt v := wdelta_apply E8 i v
  rw [hw, map_neg, map_smul, ← neg_smul, phiF_wordElt, adU_prod_F, sum_neg_map]
  rfl

lemma phi_wdelta (i : Fin 8) (y : FA (Fin 8)) :
    ⁅hh i, phi y⁆ = phi (wdelta E8 i y) := by
  have h : (LieAlgebra.ad ℂ U8 (hh i)).comp phi.toLinearMap
      = phi.toLinearMap.comp (wdelta E8 i) := by
    refine Module.Basis.ext (bas (Fin 8)) (fun v => ?_)
    simp only [LinearMap.comp_apply, bas_apply]
    simpa [LieAlgebra.ad_apply] using phi_wdelta_wordElt i v
  simpa using DFunLike.congr_fun h y

lemma phiF_wdelta (i : Fin 8) (y : FA (Fin 8)) :
    ⁅hh i, phiF y⁆ = phiF (-(wdelta E8 i y)) := by
  have h : (LieAlgebra.ad ℂ U8 (hh i)).comp phiF.toLinearMap
      = phiF.toLinearMap.comp (-(wdelta E8 i)) := by
    refine Module.Basis.ext (bas (Fin 8)) (fun v => ?_)
    simp only [LinearMap.comp_apply, LinearMap.neg_apply, bas_apply]
    simpa [LieAlgebra.ad_apply] using phiF_wdelta_wordElt i v
  simpa using DFunLike.congr_fun h y

end Commons.Algebra.Lie.SerreConstruction


namespace Commons.Algebra.Lie.SerreConstruction

open CartanMatrix
open Submission.StarQuotient
open Submission.StarModule

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-! ### The images of the layers under `phi` and `phiF` -/

noncomputable def phiLie : FA (Fin 8) →ₗ⁅ℂ⁆ U8 where
  toLinearMap := phi.toLinearMap
  map_lie' := by
    intro x y
    show phi ⁅x, y⁆ = ⁅phi x, phi y⁆
    rw [Ring.lie_def, Ring.lie_def, map_sub, map_mul, map_mul]

noncomputable def phiFLie : FA (Fin 8) →ₗ⁅ℂ⁆ U8 where
  toLinearMap := phiF.toLinearMap
  map_lie' := by
    intro x y
    show phiF ⁅x, y⁆ = ⁅phiF x, phiF y⁆
    rw [Ring.lie_def, Ring.lie_def, map_sub, map_mul, map_mul]

noncomputable def uNpt : LieSubalgebra ℂ U8 :=
  LieSubalgebra.lieSpan ℂ U8 (Set.range (fun j : Fin 8 => UniversalEnvelopingAlgebra.ι ℂ (SerreE j)))

noncomputable def uNmnt : LieSubalgebra ℂ U8 :=
  LieSubalgebra.lieSpan ℂ U8 (Set.range (fun j : Fin 8 => UniversalEnvelopingAlgebra.ι ℂ (SerreF j)))

noncomputable def uX (n : Fin 8 → ℕ) : Submodule ℂ U8 :=
  Submodule.map phi.toLinearMap ((LieGen : Submodule ℂ (FA (Fin 8))) ⊓ FAeig n)

noncomputable def uY (n : Fin 8 → ℕ) : Submodule ℂ U8 :=
  Submodule.map phiF.toLinearMap ((LieGen : Submodule ℂ (FA (Fin 8))) ⊓ FAeig n)

lemma uNpt_eq_map : uNpt = LieSubalgebra.map phiLie LieGen := by
  apply le_antisymm
  · rw [show uNpt = LieSubalgebra.lieSpan ℂ U8
        (Set.range (fun j : Fin 8 => UniversalEnvelopingAlgebra.ι ℂ (SerreE j))) from rfl]
    refine LieSubalgebra.lieSpan_le.mpr ?_
    rintro x ⟨j, rfl⟩
    refine ⟨wordElt [j], wordElt_mem_LieGen j, ?_⟩
    show phi (wordElt [j]) = UniversalEnvelopingAlgebra.ι ℂ (SerreE j)
    rw [phi_wordElt]; simp
  · have h : LieGen ≤ uNpt.comap phiLie := by
      rw [show LieGen = LieSubalgebra.lieSpan ℂ (FA (Fin 8))
          (Set.range (fun j : Fin 8 => wordElt [j])) from rfl]
      refine LieSubalgebra.lieSpan_le.mpr ?_
      rintro x ⟨j, rfl⟩
      show phiLie (wordElt [j]) ∈ uNpt
      rw [show phiLie (wordElt [j]) = UniversalEnvelopingAlgebra.ι ℂ (SerreE j) from by
        rw [show phiLie (wordElt [j]) = phi (wordElt [j]) from rfl, phi_wordElt]; simp]
      exact LieSubalgebra.subset_lieSpan (Set.mem_range_self j)
    exact (LieSubalgebra.map_le_iff_le_comap).mpr h

lemma uNmnt_eq_map : uNmnt = LieSubalgebra.map phiFLie LieGen := by
  apply le_antisymm
  · rw [show uNmnt = LieSubalgebra.lieSpan ℂ U8
        (Set.range (fun j : Fin 8 => UniversalEnvelopingAlgebra.ι ℂ (SerreF j))) from rfl]
    refine LieSubalgebra.lieSpan_le.mpr ?_
    rintro x ⟨j, rfl⟩
    refine ⟨wordElt [j], wordElt_mem_LieGen j, ?_⟩
    show phiF (wordElt [j]) = UniversalEnvelopingAlgebra.ι ℂ (SerreF j)
    rw [phiF_wordElt]; simp
  · have h : LieGen ≤ uNmnt.comap phiFLie := by
      rw [show LieGen = LieSubalgebra.lieSpan ℂ (FA (Fin 8))
          (Set.range (fun j : Fin 8 => wordElt [j])) from rfl]
      refine LieSubalgebra.lieSpan_le.mpr ?_
      rintro x ⟨j, rfl⟩
      show phiFLie (wordElt [j]) ∈ uNmnt
      rw [show phiFLie (wordElt [j]) = UniversalEnvelopingAlgebra.ι ℂ (SerreF j) from by
        rw [show phiFLie (wordElt [j]) = phiF (wordElt [j]) from rfl, phiF_wordElt]; simp]
      exact LieSubalgebra.subset_lieSpan (Set.mem_range_self j)
    exact (LieSubalgebra.map_le_iff_le_comap).mpr h

lemma uX_le_uW (n : Fin 8 → ℕ) : uX n ≤ uW (cval n) := by
  rintro x ⟨y, hy, rfl⟩
  rw [mem_uW_iff]
  intro i
  change ⁅hh i, phi y⁆ = cval n i • phi y
  rw [phi_wdelta i y, wdelta_eq_of_mem_FAeig hy.2 i, map_smul]

lemma uY_le_uW (n : Fin 8 → ℕ) : uY n ≤ uW (fun i => -(cval n i)) := by
  rintro x ⟨y, hy, rfl⟩
  rw [mem_uW_iff]
  intro i
  change ⁅hh i, phiF y⁆ = (-(cval n i)) • phiF y
  rw [phiF_wdelta i y, wdelta_eq_of_mem_FAeig hy.2 i, ← neg_smul, map_smul]

lemma iSup_layers_eq :
    (⨆ n : Fin 8 → ℕ, ((LieGen : Submodule ℂ (FA (Fin 8))) ⊓ FAeig n))
      = (LieGen : Submodule ℂ (FA (Fin 8))) := by
  refine le_antisymm layers_le_lieGen_sub ?_
  intro x hx
  exact lieGen_le_layers hx

lemma iSup_uX_eq : (⨆ n : Fin 8 → ℕ, uX n)
    = Submodule.map phi.toLinearMap (LieGen : Submodule ℂ (FA (Fin 8))) := by
  have h : (⨆ n : Fin 8 → ℕ, uX n)
      = ⨆ n : Fin 8 → ℕ,
          Submodule.map phi.toLinearMap ((LieGen : Submodule ℂ (FA (Fin 8))) ⊓ FAeig n) := rfl
  rw [h, ← Submodule.map_iSup, iSup_layers_eq]

lemma iSup_uY_eq : (⨆ n : Fin 8 → ℕ, uY n)
    = Submodule.map phiF.toLinearMap (LieGen : Submodule ℂ (FA (Fin 8))) := by
  have h : (⨆ n : Fin 8 → ℕ, uY n)
      = ⨆ n : Fin 8 → ℕ,
          Submodule.map phiF.toLinearMap ((LieGen : Submodule ℂ (FA (Fin 8))) ⊓ FAeig n) := rfl
  rw [h, ← Submodule.map_iSup, iSup_layers_eq]

lemma uNpt_eq_iSup : (uNpt : Submodule ℂ U8) = ⨆ n : Fin 8 → ℕ, uX n := by
  rw [uNpt_eq_map, iSup_uX_eq]
  rfl

lemma uNmnt_eq_iSup : (uNmnt : Submodule ℂ U8) = ⨆ n : Fin 8 → ℕ, uY n := by
  rw [uNmnt_eq_map, iSup_uY_eq]
  rfl

lemma uX_zero : uX 0 = ⊥ := by
  rw [uX, disjoint_lieGen_FAeig_zero, Submodule.map_bot]

lemma uY_zero : uY 0 = ⊥ := by
  rw [uY, disjoint_lieGen_FAeig_zero, Submodule.map_bot]

lemma uNpt_le_iSup_ne : (uNpt : Submodule ℂ U8) ≤ ⨆ n ∈ ({n : Fin 8 → ℕ | n ≠ 0} : Set _), uX n := by
  rw [uNpt_eq_iSup]
  refine iSup_le (fun n => ?_)
  by_cases hn : n = 0
  · rw [hn, uX_zero]; exact bot_le
  · exact le_iSup_of_le n (le_iSup_of_le hn le_rfl)

end Commons.Algebra.Lie.SerreConstruction


namespace Commons.Algebra.Lie.SerreConstruction

open CartanMatrix
open Submission.StarQuotient
open Submission.StarModule

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

/-! ### The integer-indexed weight functional -/

/-- The eigenvalue of the Cartan on the weight vector `cvalZi n`. -/
noncomputable def cvalZi (n : Fin 8 → ℤ) (i : Fin 8) : ℂ := ((∑ j, n j * E8 i j : ℤ) : ℂ)

lemma cvalZi_zero (i : Fin 8) : cvalZi 0 i = 0 := by simp [cvalZi]
lemma cvalZi_eq_cval (n : Fin 8 → ℕ) (i : Fin 8) : cvalZi (fun j => (n j : ℤ)) i = cval n i := rfl
lemma cvalZi_eq_cval' (n : Fin 8 → ℕ) : cvalZi (fun j => (n j : ℤ)) = cval n :=
  funext (cvalZi_eq_cval n)
lemma cvalZi_neg (n : Fin 8 → ℤ) (i : Fin 8) : cvalZi (-n) i = -cvalZi n i := by
  have h : (∑ j, (-n) j * E8 i j : ℤ) = -(∑ j, n j * E8 i j : ℤ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun j _ => by simp)
  simp only [cvalZi, h, Int.cast_neg]

lemma cvalZi_injective : Function.Injective cvalZi := by
  intro n m h
  have hZ : ∀ i, ∑ j, n j * E8 i j = ∑ j, m j * E8 i j := by
    intro i
    have := congrFun h i
    simp only [cvalZi] at this
    exact_mod_cast this
  have hmul : ∀ i, ∑ j, (n j - m j) * E8 i j = 0 := by
    intro i
    rw [show (∑ j, (n j - m j) * E8 i j)
        = (∑ j, n j * E8 i j) - (∑ j, m j * E8 i j) from by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl (fun j _ => by ring)]
    rw [hZ i, sub_self]
  have hq : ∀ i, ∑ j, (((n j : ℚ) - (m j : ℚ))) * (E8 i j : ℚ) = 0 := by
    intro i
    have := hmul i
    have h2 : ((∑ j, (n j - m j) * E8 i j : ℤ) : ℚ) = 0 := by rw [this]; simp
    push_cast at h2
    simpa [sub_mul, Finset.sum_sub_distrib] using h2
  by_contra hne
  have hv : (fun j => (n j : ℚ) - (m j : ℚ)) ≠ 0 := by
    intro hv
    apply hne
    funext j
    have := congrFun hv j
    simp only [Pi.zero_apply] at this
    have : (n j : ℚ) = (m j : ℚ) := by linarith
    exact_mod_cast this
  have hpos := Commons.LinearAlgebra.Matrix.Cartan.E8_posDef
    (fun j => (n j : ℚ) - (m j : ℚ)) hv
  have hzero : ∑ i, ∑ j, ((n i : ℚ) - (m i : ℚ)) * (E8 i j : ℚ) *
      ((n j : ℚ) - (m j : ℚ)) = 0 := by
    refine Finset.sum_eq_zero (fun i _ => ?_)
    calc ∑ j, ((n i : ℚ) - (m i : ℚ)) * (E8 i j : ℚ) * ((n j : ℚ) - (m j : ℚ))
        = ((n i : ℚ) - (m i : ℚ)) *
            ∑ j, ((n j : ℚ) - (m j : ℚ)) * (E8 i j : ℚ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = 0 := by rw [hq i, mul_zero]
  linarith

lemma cvalZi_ne_zero {n : Fin 8 → ℤ} (hn : n ≠ 0) : cvalZi n ≠ 0 := by
  intro h
  refine hn (cvalZi_injective ?_)
  rw [h]
  funext i
  exact (cvalZi_zero i).symm

/-! ### The separation argument -/

lemma sum_eq_zero_of_mem_uW {σ : Type*} [Fintype σ] (μ : σ → (Fin 8 → ℂ)) (x : σ → U8)
    (ν : Fin 8 → ℂ) (hx : ∀ m, x m ∈ uW (μ m)) (hsum : ∑ m, x m ∈ uW ν) (d : Fin 8 → ℂ)
    (hinj : ∀ m m', (∑ i, d i * μ m i) = (∑ i, d i * μ m' i) → m = m')
    (hne : ∀ m, (∑ i, d i * μ m i) ≠ (∑ i, d i * ν i)) : ∀ m, x m = 0 := by
  refine joint_eigenspace_sum_eq_zero (fun i => LieAlgebra.ad ℂ U8 (hh i)) d μ x ν ?_ ?_ ?_
  · intro o1 o2 h
    match o1, o2 with
    | some m1, some m2 => exact congrArg some (hinj m1 m2 h)
    | some m1, none => exact absurd h (hne m1)
    | none, some m2 => exact absurd h.symm (hne m2)
    | none, none => rfl
  · intro m i; exact (mem_uW_iff.mp (hx m)) i
  · intro i; exact (mem_uW_iff.mp hsum) i

lemma iSupIndep_uW : iSupIndep (fun n : Fin 8 → ℤ => uW (cvalZi n)) := by
  classical
  rw [iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero]
  intro s v hv hsum i hi
  -- choose a weight vector `ν` outside the finite set and separating
  obtain ⟨ν, hν⟩ := Finset.exists_notMem (s.image (fun m => cvalZi m))
  obtain ⟨d, hd⟩ := Commons.LinearAlgebra.exists_separating_functional
    (insert ν (s.image (fun m => cvalZi m)))
  have hmem : ∀ m ∈ s, cvalZi m ∈ insert ν (s.image (fun m => cvalZi m)) :=
    fun m hm => Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hm)
  have hνmem : ν ∈ insert ν (s.image (fun m => cvalZi m)) := Finset.mem_insert_self _ _
  have hinj : ∀ m m' : ↥s, (∑ k, d k * cvalZi m.1 k) = (∑ k, d k * cvalZi m'.1 k) → m = m' := by
    intro m m' h
    exact Subtype.ext (cvalZi_injective (hd _ (hmem m.1 m.2) _ (hmem m'.1 m'.2) h))
  have hne : ∀ m : ↥s, (∑ k, d k * cvalZi m.1 k) ≠ (∑ k, d k * ν k) := by
    intro m h
    have hc : cvalZi m.1 = ν := hd _ (hmem m.1 m.2) _ hνmem h
    exact hν (hc.symm ▸ Finset.mem_image_of_mem _ m.2)
  have hsum' : ∑ m : ↥s, v m.1 ∈ uW ν := by
    have : ∑ m : ↥s, v m.1 = 0 := by
      rw [Finset.univ_eq_attach, Finset.sum_attach]; exact hsum
    rw [this]; exact Submodule.zero_mem _
  have hall := sum_eq_zero_of_mem_uW (fun m : ↥s => cvalZi m.1) (fun m => v m.1) ν
    (fun m => hv m.1 m.2) hsum' d hinj hne
  exact hall ⟨i, hi⟩

lemma uW_zero_inf_iSup_uW : uW 0 ⊓ (⨆ n : Fin 8 → ℤ, ⨆ (_ : n ≠ 0), uW (cvalZi n)) = ⊥ := by
  have h := iSupIndep_def.mp iSupIndep_uW 0
  rw [show cvalZi 0 = 0 from funext cvalZi_zero] at h
  exact disjoint_iff.mp h

lemma uNpt_sup_uNmnt_le : (uNpt : Submodule ℂ U8) ⊔ (uNmnt : Submodule ℂ U8)
    ≤ ⨆ n : Fin 8 → ℤ, ⨆ (_ : n ≠ 0), uW (cvalZi n) := by
  refine sup_le ?_ ?_
  · rw [uNpt_eq_iSup]
    refine iSup_le (fun n => ?_)
    by_cases hn : n = 0
    · rw [hn, uX_zero]; exact bot_le
    · refine le_trans (uX_le_uW n) ?_
      rw [← cvalZi_eq_cval' n]
      refine le_iSup_of_le (fun j => (n j : ℤ)) (le_iSup_of_le ?_ le_rfl)
      intro hc
      exact hn (funext fun j => by
        have := congrFun hc j
        simp only [Pi.zero_apply] at this
        exact_mod_cast this)
  · rw [uNmnt_eq_iSup]
    refine iSup_le (fun n => ?_)
    by_cases hn : n = 0
    · rw [hn, uY_zero]; exact bot_le
    · refine le_trans (uY_le_uW n) ?_
      rw [show (fun i => -(cval n i)) = cvalZi (-(fun j => (n j : ℤ))) from by
        funext i; rw [cvalZi_neg, cvalZi_eq_cval]]
      refine le_iSup_of_le (-(fun j => (n j : ℤ))) (le_iSup_of_le ?_ le_rfl)
      intro hc
      have hc' : (fun j => (n j : ℤ)) = 0 := by
        funext j
        have := congrFun hc j
        simpa using this
      exact hn (funext fun j => by
        have := congrFun hc' j
        simp only [Pi.zero_apply] at this
        exact_mod_cast this)

lemma uW_zero_inf_uNpt_sup_uNmnt :
    uW 0 ⊓ ((uNpt : Submodule ℂ U8) ⊔ (uNmnt : Submodule ℂ U8)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro y hy
  rw [Submodule.mem_inf] at hy
  have hmem : y ∈ (⨆ n : Fin 8 → ℤ, ⨆ (_ : n ≠ 0), uW (cvalZi n)) := uNpt_sup_uNmnt_le hy.2
  have hbot : y ∈ (⊥ : Submodule ℂ U8) := by
    rw [← uW_zero_inf_iSup_uW]
    exact Submodule.mem_inf.mpr ⟨hy.1, hmem⟩
  simpa using hbot

/-! ### Transfer to `e₈` -/

noncomputable def nplus : LieSubalgebra ℂ L8 :=
  LieSubalgebra.lieSpan ℂ L8 (Set.range SerreE)

noncomputable def nminus : LieSubalgebra ℂ L8 :=
  LieSubalgebra.lieSpan ℂ L8 (Set.range SerreF)

lemma iota_mem_uW {μ : Fin 8 → ℂ} {x : L8} (hx : x ∈ W μ) :
    UniversalEnvelopingAlgebra.ι ℂ x ∈ uW μ := by
  rw [mem_uW_iff]
  intro i
  rw [show hh i = UniversalEnvelopingAlgebra.ι ℂ (SerreH i) from rfl,
    ← LieHom.map_lie (f := UniversalEnvelopingAlgebra.ι ℂ) (SerreH i) x,
    (mem_W_iff.mp hx) i, map_smul]

lemma iota_mem_uNpt {x : L8} (hx : x ∈ nplus) :
    UniversalEnvelopingAlgebra.ι ℂ x ∈ uNpt := by
  have hle : nplus ≤ uNpt.comap (UniversalEnvelopingAlgebra.ι ℂ : L8 →ₗ⁅ℂ⁆ U8) := by
    rw [show nplus = LieSubalgebra.lieSpan ℂ L8 (Set.range SerreE) from rfl]
    refine LieSubalgebra.lieSpan_le.mpr ?_
    rintro x ⟨j, rfl⟩
    exact LieSubalgebra.subset_lieSpan (Set.mem_range_self j)
  exact hle hx

lemma iota_mem_uNmnt {x : L8} (hx : x ∈ nminus) :
    UniversalEnvelopingAlgebra.ι ℂ x ∈ uNmnt := by
  have hle : nminus ≤ uNmnt.comap (UniversalEnvelopingAlgebra.ι ℂ : L8 →ₗ⁅ℂ⁆ U8) := by
    rw [show nminus = LieSubalgebra.lieSpan ℂ L8 (Set.range SerreF) from rfl]
    refine LieSubalgebra.lieSpan_le.mpr ?_
    rintro x ⟨j, rfl⟩
    exact LieSubalgebra.subset_lieSpan (Set.mem_range_self j)
  exact hle hx

end Commons.Algebra.Lie.SerreConstruction


namespace Commons.Algebra.Lie.SerreConstruction

open CartanMatrix

attribute [local instance 100] LieRing.ofAssociativeRing LieAlgebra.ofAssociativeAlgebra

lemma W_zero_inf_nplus_sup_nminus :
    W 0 ⊓ ((nplus : Submodule ℂ L8) ⊔ (nminus : Submodule ℂ L8)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro x hx
  rw [Submodule.mem_inf] at hx
  obtain ⟨hxW, hxS⟩ := hx
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hxS
  have hxW' : a + b ∈ W 0 := by rw [hab]; exact hxW
  have hmem : UniversalEnvelopingAlgebra.ι ℂ (a + b)
      ∈ uW 0 ⊓ ((uNpt : Submodule ℂ U8) ⊔ (uNmnt : Submodule ℂ U8)) := by
    refine Submodule.mem_inf.mpr ⟨iota_mem_uW hxW', ?_⟩
    rw [map_add]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (iota_mem_uNpt ha))
      (Submodule.mem_sup_right (iota_mem_uNmnt hb))
  have hbot : UniversalEnvelopingAlgebra.ι ℂ (a + b) ∈ (⊥ : Submodule ℂ U8) := by
    rw [← uW_zero_inf_uNpt_sup_uNmnt]; exact hmem
  have hz : UniversalEnvelopingAlgebra.ι ℂ (a + b) = UniversalEnvelopingAlgebra.ι ℂ 0 := by
    rw [map_zero]; simpa using hbot
  have hzero : a + b = 0 := e8_iota_injective hz
  rw [← hab]; exact hzero

theorem e8_zero_weightSpace_finrank :
    Module.finrank ℂ ↥(⨅ i : Fin 8, (LinearMap.ker (LieAlgebra.ad ℂ (LieAlgebra.e₈ ℂ)
      (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)
        (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i))) - (0 : ℂ) • 1) :
        Submodule ℂ (LieAlgebra.e₈ ℂ))) = 8 := by
  have hW : (⨅ i : Fin 8, (LinearMap.ker (LieAlgebra.ad ℂ (LieAlgebra.e₈ ℂ)
      (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)
        (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i))) - (0 : ℂ) • 1) :
        Submodule ℂ (LieAlgebra.e₈ ℂ))) = W 0 := rfl
  rw [hW]
  have hH_le : Submodule.span ℂ (Set.range SerreH) ≤ W 0 :=
    Submodule.span_le.mpr (by rintro y ⟨i, rfl⟩; exact SerreH_mem_W_zero i)
  have hspan : W 0 = Submodule.span ℂ (Set.range SerreH) := by
    refine le_antisymm ?_ hH_le
    intro x hx
    have htop : x ∈ (LieSubalgebra.lieSpan ℂ (LieAlgebra.e₈ ℂ) (Set.range (fun i : Fin 8 =>
          (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)
            (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.E i)) : LieAlgebra.e₈ ℂ))) :
          Submodule ℂ (LieAlgebra.e₈ ℂ))
        ⊔ Submodule.span ℂ (Set.range (fun i : Fin 8 =>
          (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)
            (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.H i)) : LieAlgebra.e₈ ℂ)))
        ⊔ (LieSubalgebra.lieSpan ℂ (LieAlgebra.e₈ ℂ) (Set.range (fun i : Fin 8 =>
          (LieSubmodule.Quotient.mk (N := CartanMatrix.Relations.toIdeal ℂ CartanMatrix.E₈)
            (FreeLieAlgebra.of ℂ (CartanMatrix.Generators.F i)) : LieAlgebra.e₈ ℂ))) :
          Submodule ℂ (LieAlgebra.e₈ ℂ)) := by
      rw [e8_eq_sup_cartan_positive_negative]; exact Submodule.mem_top
    obtain ⟨ab, hab, c, hc, habc⟩ := Submodule.mem_sup.mp htop
    obtain ⟨a, ha, b, hb, hab'⟩ := Submodule.mem_sup.mp hab
    have hnplus : a ∈ (nplus : Submodule ℂ L8) := ha
    have hnminus : c ∈ (nminus : Submodule ℂ L8) := hc
    have hxc : x - b ∈ W 0 ⊓ ((nplus : Submodule ℂ L8) ⊔ (nminus : Submodule ℂ L8)) := by
      refine Submodule.mem_inf.mpr ⟨(W 0).sub_mem hx (hH_le hb), ?_⟩
      have hxb : x - b = a + c := by rw [← habc, ← hab']; abel
      rw [hxb]
      exact Submodule.add_mem _ (Submodule.mem_sup_left hnplus) (Submodule.mem_sup_right hnminus)
    have hzero : x - b = 0 := by
      have := (Submodule.eq_bot_iff _).mp W_zero_inf_nplus_sup_nminus (x - b) hxc
      simpa using this
    rw [sub_eq_zero.mp hzero]; exact hb
  rw [hspan, finrank_span_eq_card e8_H_linearIndependent]
  simp

end Commons.Algebra.Lie.SerreConstruction


namespace Commons.Algebra.Lie.SerreConstruction
end Commons.Algebra.Lie.SerreConstruction
