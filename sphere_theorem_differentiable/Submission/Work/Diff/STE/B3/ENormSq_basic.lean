import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.pdList_mul_sub
import Submission.Work.Diff.STE.commutator_core
import Submission.Work.Diff.STE.bessel_continuous
import Submission.Work.Diff.STE.continuous_pdVec
import Submission.Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv
import Submission.Work.Diff.STE.B3.tame_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Elementary facts about the `H^m` energy `ENormSq` on the flat torus

This file collects the elementary (measure-theoretic and algebraic) facts about

* the iterated partial derivatives `pdList`/`pdVec` (`Work.Diff.STE.Torus`): they are linear
  over finite sums, they annihilate constants, and they are continuous for `C^k` functions;
* the energy `ENormSq k f = Σ_{l : Fin k → ι} ∫_{cube} ‖∂^l f‖²`: nonnegativity, the
  single-jet domination `∫ ‖∂^l f‖² ≤ ENormSq k f`, and the fact that `ENormSq 0 f` is the
  `L²` norm squared;
* integrability on the unit cube of the `p`-th powers of the jets of a smooth function
  (via continuity);
* the total mass of the cube, `volume unitCube = 1`.

These are shared by the tame (Moser/Gagliardo–Nirenberg) estimates for the inverse of a bounded
periodic matrix field, in particular `Work.Diff.STE.B3.ENormSq_mat_inv_le`.
-/

noncomputable section

open MeasureTheory BigOperators

namespace Work.Diff.STE.B3

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `pdVec` in order `0` is the identity. -/
lemma pdVec_zero_apply (l : Fin 0 → ι) (f : (ι → ℝ) → ℂ) :
    Work.Diff.STE.pdVec 0 l f = f := by
  rw [Work.Diff.STE.pdVec, List.ofFn_zero]
  rfl

/-- A single partial derivative annihilates a constant. -/
lemma pd_const (i : ι) (c : ℂ) :
    Work.Diff.STE.pd i (fun _ : ι → ℝ => c) = fun _ => 0 := by
  funext x
  simp [Work.Diff.STE.pd]

/-- Every positive-order iterated partial derivative annihilates a constant. -/
lemma pdList_cons_const (i : ι) (l : List ι) (c : ℂ) :
    Work.Diff.STE.pdList (i :: l) (fun _ : ι → ℝ => c) = fun _ => 0 := by
  induction l generalizing i with
  | nil =>
      rw [Work.Diff.STE.pdList, List.foldr_cons, List.foldr_nil]
      exact pd_const i c
  | cons j l ih =>
      rw [Work.Diff.STE.pdList, List.foldr_cons]
      rw [show List.foldr (fun i g => Work.Diff.STE.pd i g) (fun x => c) (j :: l)
          = Work.Diff.STE.pdList (j :: l) (fun x => c) from rfl, ih j]
      exact pd_const i 0

/-- A single partial derivative of a finite sum (with differentiable summands). -/
lemma pd_finset_sum {β : Type*} (i : ι) (s : Finset β) (g : β → (ι → ℝ) → ℂ)
    (hg : ∀ b ∈ s, Differentiable ℝ (g b)) :
    Work.Diff.STE.pd i (fun x => ∑ b ∈ s, g b x)
      = fun x => ∑ b ∈ s, Work.Diff.STE.pd i (g b) x := by
  funext x
  have hsum : (fun y => ∑ b ∈ s, g b y) = (∑ b ∈ s, g b) := by
    funext y
    exact (Finset.sum_apply y s g).symm
  have h1 : fderiv ℝ (fun y => ∑ b ∈ s, g b y) x = ∑ b ∈ s, fderiv ℝ (g b) x := by
    rw [hsum]
    exact fderiv_sum (u := s) (A := g) (x := x) (fun b hb => (hg b hb) x)
  simp only [Work.Diff.STE.pd, h1]
  exact sum_apply s (fun b => fderiv ℝ (g b) x) (Pi.single i 1)

/-- `pdList` of a finite sum of smooth functions is the sum of the `pdList`s. -/
lemma pdList_finset_sum {β : Type*} (l : List ι) (s : Finset β)
    (f : β → (ι → ℝ) → ℂ) (hf : ∀ b ∈ s, ContDiff ℝ (⊤ : ℕ∞) (f b)) :
    Work.Diff.STE.pdList l (fun x => ∑ b ∈ s, f b x)
      = fun x => ∑ b ∈ s, Work.Diff.STE.pdList l (f b) x := by
  induction l with
  | nil => rfl
  | cons i l ih =>
      have hfd : ∀ b ∈ s, Differentiable ℝ (Work.Diff.STE.pdList l (f b)) := by
        intro b hb
        refine (cm_contDiff_pdList l 1 (f b) ?_).differentiable (by norm_num)
        exact (hf b hb).of_le (by exact_mod_cast le_top)
      rw [show Work.Diff.STE.pdList (i :: l) (fun x => ∑ b ∈ s, f b x)
            = Work.Diff.STE.pd i (Work.Diff.STE.pdList l (fun x => ∑ b ∈ s, f b x))
          from rfl,
        ih, pd_finset_sum i s (fun b => Work.Diff.STE.pdList l (f b)) hfd]
      rfl

/-- `ENormSq 0` is the squared `L²` norm on the cube. -/
lemma ENormSq_zero_eq (f : (ι → ℝ) → ℂ) :
    Work.Diff.STE.ENormSq 0 f = ∫ x in Work.Diff.STE.unitCube, ‖f x‖ ^ 2 := by
  rw [Work.Diff.STE.ENormSq]
  have huniv : (Finset.univ : Finset (Fin 0 → ι)) = {fun i => i.elim0} := by
    refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_univ _, ?_⟩
    intro x _
    funext i
    exact Fin.elim0 i
  rw [huniv, Finset.sum_singleton, pdVec_zero_apply]

/-- The energy is nonnegative. -/
lemma ENormSq_nonneg (k : ℕ) (f : (ι → ℝ) → ℂ) : 0 ≤ Work.Diff.STE.ENormSq k f := by
  rw [Work.Diff.STE.ENormSq]
  refine Finset.sum_nonneg fun l _ => ?_
  exact integral_nonneg (f := fun x => ‖Work.Diff.STE.pdVec k l f x‖ ^ 2) fun x => by positivity

/-- A single jet is dominated by the full energy. -/
lemma integral_normSq_pdVec_le_ENormSq (k : ℕ) (l : Fin k → ι) (f : (ι → ℝ) → ℂ) :
    ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l f x‖ ^ 2
      ≤ Work.Diff.STE.ENormSq k f := by
  rw [Work.Diff.STE.ENormSq]
  refine Finset.single_le_sum (f := fun l : Fin k → ι =>
    ∫ x in Work.Diff.STE.unitCube, ‖Work.Diff.STE.pdVec k l f x‖ ^ 2) ?_ (Finset.mem_univ l)
  intro l _
  exact integral_nonneg (f := fun x => ‖Work.Diff.STE.pdVec k l f x‖ ^ 2) fun x => by positivity

/-- The energy of a matrix field is nonnegative. -/
lemma ENormSqMat_nonneg {n : ℕ} (m : ℕ) (M : (ι → ℝ) → Fin n → Fin n → ℂ) :
    0 ≤ ENormSqMat m M := by
  rw [ENormSqMat]
  exact Finset.sum_nonneg fun i _ =>
    Finset.sum_nonneg fun j _ => ENormSq_nonneg m _

/-- Total mass of the half-open unit cube: `volume unitCube = 1`. -/
lemma vol_unitCube : (volume : Measure (ι → ℝ)) (Work.Diff.STE.unitCube (ι := ι)) = 1 :=
  Work.Diff.STE.BesselCont.vol_unitCube

/-- The `p`-th power of the norm of a jet of a `C^k` function is integrable on the cube. -/
lemma integrableOn_norm_rpow_pdVec {p : ℝ} (hp : 0 ≤ p) (k : ℕ) (l : Fin k → ι)
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ ((k : ℕ) : WithTop ℕ∞) f) :
    IntegrableOn (fun x => ‖Work.Diff.STE.pdVec k l f x‖ ^ p)
      (Work.Diff.STE.unitCube (ι := ι)) volume := by
  refine cm_integrableOn_unitCube_of_continuous ?_
  exact (continuous_pdVec k l f hf).norm.rpow_const (fun x => Or.inr hp)

/-- A list-sum of a constant. -/
lemma list_sum_const {α : Type*} (L : List α) (c : ℝ) :
    ((L.map (fun _ => c)) : List ℝ).sum = L.length * c := by
  induction L with
  | nil => simp
  | cons a L ih => rw [List.map_cons, List.sum_cons, ih, List.length_cons]; push_cast; ring

/-- If every entry of a list is `≤ c` and `c ≥ 0` then the sum is `≤ length * c`. -/
lemma list_sum_le_length_mul (L : List ℝ) (c : ℝ) (hc : 0 ≤ c)
    (h : ∀ z ∈ L, z ≤ c) : L.sum ≤ L.length * c := by
  induction L with
  | nil => simp
  | cons a L ih =>
      have ha : a ≤ c := h a (List.mem_cons_self ..)
      have hL : ∀ z ∈ L, z ≤ c := fun z hz => h z (List.mem_cons_of_mem a hz)
      have := ih hL
      rw [List.sum_cons, List.length_cons]
      push_cast
      linarith

/-- A list-sum of integrable functions is integrable. -/
lemma integrable_list_sum (L : List ((ι → ℝ) → ℝ))
    (h : ∀ g ∈ L, Integrable g (volume.restrict (Work.Diff.STE.unitCube (ι := ι)))) :
    Integrable (fun x => (L.map (fun g => g x)).sum)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) := by
  induction L with
  | nil => simpa using (integrable_zero (ι → ℝ) (volume.restrict (Work.Diff.STE.unitCube (ι := ι))))
  | cons g L ih =>
      have hg : Integrable g (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
        h g (List.mem_cons_self ..)
      have hL : ∀ g' ∈ L, Integrable g' (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
        fun g' hg' => h g' (List.mem_cons_of_mem g hg')
      have hres := hg.add (ih hL)
      have hfun : (fun x => (List.map (fun g => g x) (g :: L)).sum)
          = g + fun x => (List.map (fun g => g x) L).sum := by
        funext x
        simp only [List.map_cons, List.sum_cons, Pi.add_apply]
      rw [hfun]
      exact hres

/-- The integral of a list-sum of integrable functions is the list-sum of the integrals. -/
lemma integral_list_sum (L : List ((ι → ℝ) → ℝ))
    (h : ∀ g ∈ L, Integrable g (volume.restrict (Work.Diff.STE.unitCube (ι := ι)))) :
    ∫ x in Work.Diff.STE.unitCube, (L.map (fun g => g x)).sum
      = (L.map (fun g => ∫ x in Work.Diff.STE.unitCube, g x)).sum := by
  induction L with
  | nil => simp
  | cons g L ih =>
      have hg : Integrable g (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
        h g (List.mem_cons_self ..)
      have hL : ∀ g' ∈ L, Integrable g' (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
        fun g' hg' => h g' (List.mem_cons_of_mem g hg')
      have hintL := integrable_list_sum L hL
      have hmain : (fun x => (List.map (fun g => g x) (g :: L)).sum)
          = fun x => g x + (List.map (fun g => g x) L).sum := by
        funext x
        simp only [List.map_cons, List.sum_cons]
      rw [hmain, integral_add hg hintL, ih hL, List.map_cons, List.sum_cons]

/-- The `p`-th power of the norm of an iterated partial derivative of a smooth function is
continuous. -/
lemma continuous_norm_pdList_rpow {p : ℝ} (hp : 0 ≤ p) (l : List ι) (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Continuous (fun x => ‖Work.Diff.STE.pdList l f x‖ ^ p) := by
  have h1 : Work.Diff.STE.pdList l f = Work.Diff.STE.pdVec l.length l.get f := by
    rw [Work.Diff.STE.pdVec, List.ofFn_get]
  rw [h1]
  exact (continuous_pdVec _ _ _ ((hf.of_le (by exact_mod_cast le_top)))).norm.rpow_const
    (fun x => Or.inr hp)

/-- The `p`-th power of the norm of an iterated partial derivative of a smooth function is
integrable on the cube. -/
lemma integrableOn_norm_pdList_rpow {p : ℝ} (hp : 0 ≤ p) (l : List ι) (f : (ι → ℝ) → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    Integrable (fun x => ‖Work.Diff.STE.pdList l f x‖ ^ p)
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
  cm_integrableOn_unitCube_of_continuous (continuous_norm_pdList_rpow hp l f hf)

end Work.Diff.STE.B3
