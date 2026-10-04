/-
# `Work.Diff.STE.flat.level_defs`

The vocabulary of the multi-level (`level_step`) a priori estimate of the flat DeTurck
Galerkin system, plus the elementary identifications that every later estimate uses.

The principal part of the flat DeTurck operator is `secOpFlat A B |_{ij} = Σ_{cd} (reMat A)⁻¹_{cd}
B_{cd,ij}`.  Since `∂_c∂_d u` is *symmetric* in `(c,d)` (Clairaut), only the symmetric part
`(G + Gᵀ)/2` of the inverse matrix `G = (reMat A)⁻¹` contributes; the symmetrised matrix is
positive definite with a uniform constant (`elliptic_inv`) and satisfies the same Moser bounds as
`G` (`inv_jet_bound_symm`).  This file introduces the symmetrised matrix (`symInvR`, `symInvC`) and
the value-and-first-jet map `jetP` of a series, and proves the elementary unfolding lemmas.
-/
import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.level_aux
import Submission.Work.Diff.STE.ENormSq_pairing_le
import Submission.Work.Diff.STE.pdList_mul_sub

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators

noncomputable section

open Work.Diff.STE.Flat

/-! ## The symmetrised inverse metric -/

/-- The symmetrised inverse metric matrix, as a **real** function: the operator that multiplies
the second derivatives in the principal part of the flat DeTurck operator (the antisymmetric part
of the inverse metric drops out by Clairaut against `∂_c∂_d u`). -/
def symInvR {n : ℕ} (c : (Fin n → ℤ) → MatC n) (a b : Fin n) : (Fin n → ℝ) → ℝ :=
  fun x => (((reMat (seriesFunM c x))⁻¹) a b + ((reMat (seriesFunM c x))⁻¹) b a) / 2

/-- The symmetrised inverse metric matrix, as a complex-valued function (the shape in which it
enters the Leibniz/commutator estimates). -/
def symInvC {n : ℕ} (c : (Fin n → ℤ) → MatC n) (a b : Fin n) : (Fin n → ℝ) → ℂ :=
  fun x => ((symInvR c a b x : ℝ) : ℂ)

@[simp] lemma symInvC_apply {n : ℕ} (c : (Fin n → ℤ) → MatC n) (a b : Fin n)
    (x : Fin n → ℝ) : symInvC c a b x = ((symInvR c a b x : ℝ) : ℂ) := rfl

@[simp] lemma symInvR_apply {n : ℕ} (c : (Fin n → ℤ) → MatC n) (a b : Fin n)
    (x : Fin n → ℝ) :
    symInvR c a b x
      = (((reMat (seriesFunM c x))⁻¹) a b + ((reMat (seriesFunM c x))⁻¹) b a) / 2 := rfl

/-- The symmetrised inverse metric is symmetric. -/
lemma symInvR_symm {n : ℕ} (c : (Fin n → ℤ) → MatC n) (a b : Fin n) :
    symInvR c a b = symInvR c b a := by
  funext x
  simp only [symInvR_apply]
  ring

lemma symInvR_symm_apply {n : ℕ} (c : (Fin n → ℤ) → MatC n) (a b : Fin n) (x : Fin n → ℝ) :
    symInvR c a b x = symInvR c b a x := by
  rw [symInvR_symm]

/-- The symmetrised inverse metric is the average of the inverse metric and its transpose. -/
lemma symInvR_eq_add {n : ℕ} (c : (Fin n → ℤ) → MatC n) (a b : Fin n) :
    symInvR c a b
      = fun x => ((((reMat (seriesFunM c x))⁻¹) a b + ((reMat (seriesFunM c x))⁻¹) b a) / 2) :=
  rfl

/-! ## The value-and-first-jet map -/

/-- The value and the first jet of the matrix-valued series of `c`: the argument of the
lower-order part of the DeTurck nonlinearity. -/
def jetP {n : ℕ} (c : (Fin n → ℤ) → MatC n) :
    (Fin n → ℝ) → (MatC n × (Fin n → MatC n)) :=
  fun x => (seriesFunM c x, fun a i j => pd a (fun y => seriesFunM c y i j) x)

@[simp] lemma jetP_apply {n : ℕ} (c : (Fin n → ℤ) → MatC n) (x : Fin n → ℝ) :
    jetP c x = (seriesFunM c x, fun a i j => pd a (fun y => seriesFunM c y i j) x) := rfl

@[simp] lemma jetP_fst {n : ℕ} (c : (Fin n → ℤ) → MatC n) (x : Fin n → ℝ) :
    (jetP c x).1 = seriesFunM c x := rfl

@[simp] lemma jetP_snd {n : ℕ} (c : (Fin n → ℤ) → MatC n) (x : Fin n → ℝ) :
    (jetP c x).2 = (fun a i j => pd a (fun y => seriesFunM c y i j) x) := rfl

/-! ## Elementary energy bounds -/

/-- A single summand of the `H^k` energy of `u` is bounded by the whole energy. -/
lemma int_pdVec_le_ENormSq {n k : ℕ} (u : (Fin n → ℝ) → ℂ) (l : Fin k → Fin n) :
    ∫ x in unitCube (ι := Fin n), ‖pdVec k l u x‖ ^ 2 ≤ ENormSq k u := by
  rw [ENormSq]
  refine Finset.single_le_sum (f := fun l' : Fin k → Fin n =>
    ∫ x in unitCube (ι := Fin n), ‖pdVec k l' u x‖ ^ 2) ?_ (Finset.mem_univ l)
  intro l' _
  exact integral_nonneg (fun x => sq_nonneg _)

/-- A single summand of the matrix energy `ENormSqM k u` is bounded by the whole energy. -/
lemma int_pdVec_le_ENormSqM {n k : ℕ} (u : Torus n) (i j : Fin n) (l : Fin k → Fin n) :
    ∫ x in unitCube (ι := Fin n), ‖pdVec k l (fun y => u y i j) x‖ ^ 2 ≤ ENormSqM k u := by
  have h2 : ENormSq k (fun y => u y i j) ≤ ENormSqM k u := by
    rw [ENormSqM]
    calc ENormSq k (fun y => u y i j)
        ≤ ∑ j' : Fin n, ENormSq k (fun y => u y i j') :=
          Finset.single_le_sum (f := fun j' : Fin n => ENormSq k (fun y => u y i j'))
            (fun j' _ => ENormSq_nonneg k _) (Finset.mem_univ j)
      _ ≤ ∑ i' : Fin n, ∑ j' : Fin n, ENormSq k (fun y => u y i' j') :=
          Finset.single_le_sum
            (f := fun i' : Fin n => ∑ j' : Fin n, ENormSq k (fun y => u y i' j'))
            (fun i' _ => Finset.sum_nonneg (fun j' _ => ENormSq_nonneg k _))
            (Finset.mem_univ i)
  exact (int_pdVec_le_ENormSq (fun y => u y i j) l).trans h2

/-- The `j`-fold derivative of the second derivative `∂_a∂_b u` is the `(j+2)`-fold derivative of
`u` along the concatenated direction tuple. -/
lemma pdVec_pd_pd_eq {n : ℕ} (m : ℕ) (l : Fin m → Fin n) (a b : Fin n)
    (u : (Fin n → ℝ) → ℂ) :
    pdVec m l (pd a (pd b u)) = pdVec (m + 2) (Fin.append l ![a, b]) u := by
  simp only [pdVec, pdList, List.ofFn_fin_append, List.foldr_append]
  rfl

/-- **The `L²` bound for a differentiated second derivative.**  Any `m`-fold derivative of
`∂_a∂_b u` is dominated by the level-`(m+2)` energy of `u`. -/
lemma int_pdVec_pd_pd_le_ENormSq {n : ℕ} (m : ℕ) (l : Fin m → Fin n) (a b : Fin n)
    (u : (Fin n → ℝ) → ℂ) :
    ∫ x in unitCube (ι := Fin n), ‖pdVec m l (pd a (pd b u)) x‖ ^ 2 ≤ ENormSq (m + 2) u := by
  rw [pdVec_pd_pd_eq]
  exact int_pdVec_le_ENormSq u _

/-- A summand of the level-`(m+2)` energy of an entry of `seriesFunM c` is dominated by the
matrix energy `ENormSqM (m+2) (seriesFunM c)`. -/
lemma int_pdVec_pd_pd_le_ENormSqM {n : ℕ} (c : (Fin n → ℤ) → MatC n) (m : ℕ)
    (l : Fin m → Fin n) (a b i j : Fin n) :
    ∫ x in unitCube (ι := Fin n),
        ‖pdVec m l (pd a (pd b (fun y => seriesFunM c y i j))) x‖ ^ 2
      ≤ ENormSqM (m + 2) (seriesFunM c) := by
  rw [pdVec_pd_pd_eq]
  exact int_pdVec_le_ENormSqM (seriesFunM c) i j _

/-! ## Symmetrising a double sum -/

/-- Averaging a double sum with its transpose does not change it. -/
lemma sum2_add_div_two {α : Type*} [Fintype α] (F G : α → α → ℂ) :
    (∑ a, ∑ b, (F a b + G a b) / 2) = ((∑ a, ∑ b, F a b) + (∑ a, ∑ b, G a b)) / 2 := by
  simp only [add_div, Finset.sum_add_distrib, Finset.sum_div]

/-- A double sum is unchanged if each summand is replaced by its average with the transposed
summand. -/
lemma sum_swap_half {α : Type*} [Fintype α] (F : α → α → ℂ) :
    (∑ a, ∑ b, F a b) = ∑ a, ∑ b, (F a b + F b a) / 2 := by
  rw [sum2_add_div_two]
  have hswap : (∑ a, ∑ b, F b a) = ∑ a, ∑ b, F a b := by
    rw [Finset.sum_comm]
  rw [hswap]
  ring

/-- **Symmetrising the coefficient of `Σ_{ab} G_{ab} B_{ab}`.**  For a symmetric family of
matrices `B` (e.g. `B_{ab} = ∂_a∂_b u`), only the symmetric part of `G` contributes. -/
lemma sum_symmetrize {n : ℕ} (G : Fin n → Fin n → ℝ) (B : Fin n → Fin n → MatC n)
    (hB : ∀ a b, B a b = B b a) (i j : Fin n) :
    (∑ a, ∑ b, ((G a b : ℝ) : ℂ) * B a b i j)
      = ∑ a, ∑ b, ((((G a b + G b a) / 2 : ℝ)) : ℂ) * B a b i j := by
  rw [sum_swap_half (fun a b => ((G a b : ℝ) : ℂ) * B a b i j)]
  refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
  rw [hB a b]
  push_cast
  ring

/-- **The principal part only sees the symmetrised inverse metric.** -/
lemma secOpFlat_eq_symInvR {n : ℕ} (c : (Fin n → ℤ) → MatC n)
    (B : Fin n → Fin n → MatC n) (hB : ∀ a b, B a b = B b a) (x : Fin n → ℝ) (i j : Fin n) :
    secOpFlat (seriesFunM c x) B i j
      = ∑ a, ∑ b, ((symInvR c a b x : ℝ) : ℂ) * B a b i j := by
  rw [secOpFlat]
  simp only [symInvR_apply]
  exact sum_symmetrize (fun a b => ((reMat (seriesFunM c x))⁻¹) a b) B hB i j

end

end Work.Diff.STE.flat
