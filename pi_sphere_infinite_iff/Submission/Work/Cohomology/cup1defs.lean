import Mathlib
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.AlexanderWhitney

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

open CategoryTheory AlgebraicTopology Simplicial Limits
open scoped Simplicial

namespace Work.Cohomology

noncomputable section

variable (R : Type) [CommRing R] (X : SSet)

/-- The order map `⦋n⦌ ⟶ ⦋n+m-1⦌` with `i ↦ s + i` (the front `n`-face shifted by `s`). -/
def Fface (n m s : ℕ) (h : s + n ≤ n + m - 1) : ⦋n⦌ ⟶ ⦋n + m - 1⦌ :=
  SimplexCategory.Hom.mk
    { toFun := fun i => ⟨s + i.val, by have := i.isLt; simp only [SimplexCategory.len_mk] at *; omega⟩
      monotone' := fun i j hij => by simp only [Fin.le_def] at hij ⊢; omega }

/-- The order map `⦋m⦌ ⟶ ⦋n+m-1⦌` with `j ↦ j` for `j ≤ s` and `j ↦ j + (n-1)` for `j > s`. -/
def Gfun (n m s : ℕ) (h : s + n ≤ n + m - 1) (j : Fin (m+1)) : Fin (n + m - 1 + 1) :=
  if hj : j.val ≤ s then ⟨j.val, by omega⟩ else ⟨j.val + n - 1, by omega⟩

def Gface (n m s : ℕ) (h : s + n ≤ n + m - 1) : ⦋m⦌ ⟶ ⦋n + m - 1⦌ :=
  SimplexCategory.Hom.mk
    { toFun := Gfun n m s h
      monotone' := fun i j hij => by
        simp only [Gfun]
        split_ifs with h1 h2 h2 <;> simp only [Fin.le_def] at hij ⊢ <;> omega }

@[simp] lemma Fface_val (n m s : ℕ) (h : s + n ≤ n + m - 1) (i : Fin (n+1)) :
    ((ConcreteCategory.hom (Fface n m s h)) i).val = s + i.val := rfl

@[simp] lemma Gface_apply (n m s : ℕ) (h : s + n ≤ n + m - 1) (j : Fin (m+1)) :
    ((ConcreteCategory.hom (Gface n m s h)) j) = Gfun n m s h j := rfl

lemma Gfun_val_le (n m s : ℕ) (h : s + n ≤ n + m - 1) (j : Fin (m+1)) (hj : j.val ≤ s) :
    (Gfun n m s h j).val = j.val := by
  simp only [Gfun]; rw [dif_pos hj]

lemma Gfun_val_gt (n m s : ℕ) (h : s + n ≤ n + m - 1) (j : Fin (m+1)) (hj : s < j.val) :
    (Gfun n m s h j).val = j.val + n - 1 := by
  simp only [Gfun]; rw [dif_neg (by omega)]

/-- The cochain homotopy `cup1 α β` of degree `n+m-1`, defined as a morphism. -/
noncomputable def cup1Hom (n m : ℕ) (α : Cochain R X n) (β : Cochain R X m) :
    (X.chainComplex (ModuleCat.of R R)).X (n + m - 1) ⟶ ModuleCat.of R R :=
  (X.isColimitChainComplexXCofan (ModuleCat.of R R) (n + m - 1)).desc
    (Cofan.mk (ModuleCat.of R R)
      (fun σ : X _⦋n + m - 1⦌ =>
        ModuleCat.ofHom (LinearMap.toSpanSingleton R R
          (∑ s : Fin m,
            ((-1:R)^(s.val*(n+1)+n)) *
              genEval R X α (X.map (Fface n m s.val (by have := s.isLt; omega)).op σ) *
              genEval R X β (X.map (Gface n m s.val (by have := s.isLt; omega)).op σ)))))

@[simp]
lemma ιChainComplex_cup1Hom (n m : ℕ) (α : Cochain R X n) (β : Cochain R X m)
    (σ : X _⦋n + m - 1⦌) :
    X.ιChainComplex σ ≫ cup1Hom R X n m α β =
      ModuleCat.ofHom (LinearMap.toSpanSingleton R R
        (∑ s : Fin m,
          ((-1:R)^(s.val*(n+1)+n)) *
            genEval R X α (X.map (Fface n m s.val (by have := s.isLt; omega)).op σ) *
            genEval R X β (X.map (Gface n m s.val (by have := s.isLt; omega)).op σ))) :=
  Cofan.IsColimit.fac _ _ _

/-- The cochain homotopy `cup1 α β` of degree `n+m-1`. -/
noncomputable def cup1 (n m : ℕ) (α : Cochain R X n) (β : Cochain R X m) :
    Cochain R X (n + m - 1) := (cup1Hom R X n m α β).hom

lemma genEval_cup1 (n m : ℕ) (α : Cochain R X n) (β : Cochain R X m)
    (σ : X _⦋n + m - 1⦌) :
    genEval R X (cup1 R X n m α β) σ =
      ∑ s : Fin m,
        ((-1:R)^(s.val*(n+1)+n)) *
          genEval R X α (X.map (Fface n m s.val (by have := s.isLt; omega)).op σ) *
          genEval R X β (X.map (Gface n m s.val (by have := s.isLt; omega)).op σ) := by
  have h2 := congrArg (fun (g : ModuleCat.of R R ⟶ ModuleCat.of R R) => g.hom 1)
    (ιChainComplex_cup1Hom R X n m α β σ)
  simpa only [cup1, genEval, ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
    LinearMap.toSpanSingleton_apply, one_smul] using h2

