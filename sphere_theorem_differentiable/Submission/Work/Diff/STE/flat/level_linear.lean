/-
# `Work.Diff.STE.flat.level_linear`

The elementary linearity and integrability plumbing used by the multi-level energy estimate
(`Work.Diff.STE.flat.level_step`).

Contents:

* `pd`, `pdList`, `pdVec` commute with finite sums (and hence with the sums over the matrix
  entries of the DeTurck decomposition `Φ = secOpFlat + N`);
* `L2re` is additive over finite sums of its first argument;
* every continuous function on the unit cube is integrable against `star` of a continuous
  function;
* the iterated derivatives of a component of a smooth matrix-valued function are dominated by
  the iterated derivatives of the matrix-valued function itself.
-/
import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.level_defs
import Submission.Work.Diff.STE.commutator_pd
import Submission.Work.Diff.STE.commutator_core
import Submission.Work.Diff.STE.pdList_mul_sub

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators

noncomputable section

open Work.Diff.STE.Flat

/-! ## Smoothness of iterated partial derivatives -/

/-- A partial derivative of a smooth function is smooth. -/
lemma contDiff_pd_top {n : ℕ} {f : (Fin n → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (j : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (pd j f) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) :=
    hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Fin n → ℝ => (fderiv ℝ f x) (Pi.single j (1 : ℝ))) := by
    fun_prop
  exact h2

/-- Iterated partial derivatives of a smooth function are smooth. -/
lemma contDiff_pdList_top {n : ℕ} {f : (Fin n → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (L : List (Fin n)) : ContDiff ℝ (⊤ : ℕ∞) (pdList L f) := by
  induction L with
  | nil => simpa [pdList] using hf
  | cons a L ih => exact contDiff_pd_top ih a

/-- Iterated partial derivatives of a smooth function are smooth (`pdVec` form). -/
lemma contDiff_pdVec_top {n m : ℕ} {f : (Fin n → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (l : Fin m → Fin n) : ContDiff ℝ (⊤ : ℕ∞) (pdVec m l f) :=
  contDiff_pdList_top hf _

/-! ## Linearity of `pd` and `pdVec` over finite sums -/

/-- `pd` commutes with a finite sum. -/
lemma pd_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι) (F : ι → (Fin n → ℝ) → ℂ)
    (hF : ∀ i ∈ s, Differentiable ℝ (F i)) (a : Fin n) :
    pd a (fun x => ∑ i ∈ s, F i x) = fun x => ∑ i ∈ s, pd a (F i) x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      funext x
      simp only [Finset.sum_empty]
      simp [pd]
  | insert i s hi ih =>
      have hFi : Differentiable ℝ (F i) := hF i (Finset.mem_insert_self i s)
      have hs : Differentiable ℝ (fun x : Fin n → ℝ => ∑ j ∈ s, F j x) :=
        Differentiable.fun_sum (fun j hj => hF j (Finset.mem_insert_of_mem hj))
      have hsum : (fun x : Fin n → ℝ => ∑ j ∈ insert i s, F j x)
          = F i + fun x : Fin n → ℝ => ∑ j ∈ s, F j x := by
        funext x
        rw [Finset.sum_insert hi]
        rfl
      rw [hsum, Work.Diff.STE.pd_add_fn a (F i) (fun x : Fin n → ℝ => ∑ j ∈ s, F j x) hFi hs,
        ih (fun j hj => hF j (Finset.mem_insert_of_mem hj))]
      funext x
      rw [Finset.sum_insert hi]
      rfl

/-- `pdList` commutes with a finite sum of smooth functions. -/
lemma pdList_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι) (L : List (Fin n))
    (F : ι → (Fin n → ℝ) → ℂ) (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) :
    pdList L (fun x => ∑ i ∈ s, F i x) = fun x => ∑ i ∈ s, pdList L (F i) x := by
  classical
  induction L with
  | nil => rfl
  | cons a L ih =>
      show pd a (pdList L (fun x => ∑ i ∈ s, F i x))
        = fun x => ∑ i ∈ s, pd a (pdList L (F i)) x
      rw [ih]
      exact pd_finset_sum s (fun i => pdList L (F i))
        (fun i _ => (contDiff_pdList_top (hF i) L).differentiable (by simp)) a

/-- `pdVec` commutes with a finite sum of smooth functions. -/
lemma pdVec_finset_sum {n m : ℕ} {ι : Type*} (s : Finset ι) (l : Fin m → Fin n)
    (F : ι → (Fin n → ℝ) → ℂ) (hF : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (F i)) :
    pdVec m l (fun x => ∑ i ∈ s, F i x) = fun x => ∑ i ∈ s, pdVec m l (F i) x := by
  have h := pdList_finset_sum s (List.ofFn l) F hF
  simpa only [pdVec] using h

/-- `pdVec` commutes with a double sum of smooth functions. -/
lemma pdVec_sum2 {n m : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ] (l : Fin m → Fin n)
    (F : ι → κ → (Fin n → ℝ) → ℂ) (hF : ∀ i k, ContDiff ℝ (⊤ : ℕ∞) (F i k)) :
    pdVec m l (fun x => ∑ i, ∑ k, F i k x) = fun x => ∑ i, ∑ k, pdVec m l (F i k) x := by
  have hinner : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => ∑ k, F i k x) :=
    fun i => ContDiff.sum (fun k _ => hF i k)
  rw [pdVec_finset_sum Finset.univ l (fun i => fun x => ∑ k, F i k x) hinner]
  funext x
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact congrFun (pdVec_finset_sum Finset.univ l (F i) (fun k => hF i k)) x

/-- `pdList` is additive in the function. -/
lemma pdList_add {n : ℕ} (L : List (Fin n)) {f g : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    pdList L (f + g) = pdList L f + pdList L g := by
  induction L with
  | nil => rfl
  | cons a L ih =>
      show pd a (pdList L (f + g)) = pd a (pdList L f) + pd a (pdList L g)
      rw [ih]
      exact Work.Diff.STE.pd_add_fn a (pdList L f) (pdList L g)
        ((contDiff_pdList_top hf L).differentiable (by simp))
        ((contDiff_pdList_top hg L).differentiable (by simp))

/-- `pdList` version of the linearity over the DeTurck decomposition. -/
lemma pdList_sum2_add {n : ℕ} (L : List (Fin n))
    (F : Fin n → Fin n → (Fin n → ℝ) → ℂ) (G : (Fin n → ℝ) → ℂ)
    (hF : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (F a b)) (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    pdList L (fun x => (∑ a, ∑ b, F a b x) + G x)
      = fun x => (∑ a, ∑ b, pdList L (F a b) x) + pdList L G x := by
  have hSum : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => ∑ a, ∑ b, F a b x) :=
    ContDiff.sum (fun a _ => ContDiff.sum (fun b _ => hF a b))
  have hInner : ∀ a : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => ∑ b, F a b x) :=
    fun a => ContDiff.sum (fun b _ => hF a b)
  have h1 : (fun x : Fin n → ℝ => (∑ a, ∑ b, F a b x) + G x)
      = (fun x : Fin n → ℝ => ∑ a, ∑ b, F a b x) + G := rfl
  rw [h1, pdList_add L hSum hG,
    pdList_finset_sum Finset.univ L (fun a => fun x => ∑ b, F a b x) hInner]
  funext x
  have hkey : (∑ a : Fin n, pdList L (fun y : Fin n → ℝ => ∑ b, F a b y) x)
      = ∑ a : Fin n, ∑ b : Fin n, pdList L (F a b) x :=
    Finset.sum_congr rfl (fun a _ =>
      congrFun (pdList_finset_sum Finset.univ L (F a) (fun b => hF a b)) x)
  show (∑ a : Fin n, pdList L (fun y : Fin n → ℝ => ∑ b, F a b y) x) + pdList L G x
      = (∑ a : Fin n, ∑ b : Fin n, pdList L (F a b) x) + pdList L G x
  rw [hkey]

/-- **Linearity of `pdVec` over the DeTurck decomposition.**  The `m`-fold derivative of
`Σ_{a,b} F_{ab} + G` is the sum of the `m`-fold derivatives. -/
lemma pdVec_sum2_add {n m : ℕ} (l : Fin m → Fin n)
    (F : Fin n → Fin n → (Fin n → ℝ) → ℂ) (G : (Fin n → ℝ) → ℂ)
    (hF : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (F a b)) (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    pdVec m l (fun x => (∑ a, ∑ b, F a b x) + G x)
      = fun x => (∑ a, ∑ b, pdVec m l (F a b) x) + pdVec m l G x := by
  have h := pdList_sum2_add (List.ofFn l) F G hF hG
  simpa only [pdVec] using h

/-! ## Integrability on the unit cube -/

/-- A continuous complex-valued function on the unit cube is integrable there. -/
lemma integrableOn_unitCube_of_continuous {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : Continuous f) :
    Integrable f (volume.restrict (unitCube (ι := Fin n))) := by
  have hC : IsCompact (Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hsub : unitCube (ι := Fin n) ⊆ Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
    intro x hx
    simp only [unitCube, Set.mem_pi, Set.mem_univ, true_implies] at hx ⊢
    exact fun j => ⟨le_of_lt (hx j).1, (hx j).2⟩
  exact (ContinuousOn.integrableOn_compact hC hf.continuousOn).mono_set hsub

/-- The pairing integrand of two continuous functions is integrable on the unit cube. -/
lemma integrableOnUnitCube_mul_star {n : ℕ} {f g : (Fin n → ℝ) → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    Integrable (fun x => f x * star (g x)) (volume.restrict (unitCube (ι := Fin n))) :=
  integrableOn_unitCube_of_continuous (hf.mul hg.star)

/-! ## Linearity of `L2re` over finite sums -/

/-- `L2re` is additive over a finite sum in its first argument (continuous case). -/
lemma L2re_finset_sum {n : ℕ} {ι : Type*} (s : Finset ι) (F : ι → (Fin n → ℝ) → ℂ)
    (g : (Fin n → ℝ) → ℂ) (hF : ∀ i ∈ s, Continuous (F i)) (hg : Continuous g) :
    L2re (fun x => ∑ i ∈ s, F i x) g = ∑ i ∈ s, L2re (F i) g := by
  classical
  have hpt : (fun x : Fin n → ℝ => (∑ i ∈ s, F i x) * star (g x))
      = fun x => ∑ i ∈ s, F i x * star (g x) := by
    funext x
    rw [Finset.sum_mul]
  simp only [L2re]
  rw [hpt, integral_finsetSum s (fun i hi => integrableOnUnitCube_mul_star (hF i hi) hg),
    Complex.re_sum]

/-- `L2re` is additive in its first argument (continuous case). -/
lemma L2re_add_left {n : ℕ} {f₁ f₂ g : (Fin n → ℝ) → ℂ}
    (h1 : Continuous f₁) (h2 : Continuous f₂) (hg : Continuous g) :
    L2re (fun x => f₁ x + f₂ x) g = L2re f₁ g + L2re f₂ g := by
  have hI1 : Integrable (fun x => f₁ x * star (g x)) (volume.restrict (unitCube (ι := Fin n))) :=
    integrableOnUnitCube_mul_star h1 hg
  have hI2 : Integrable (fun x => f₂ x * star (g x)) (volume.restrict (unitCube (ι := Fin n))) :=
    integrableOnUnitCube_mul_star h2 hg
  have hpt : (fun x : Fin n → ℝ => (f₁ x + f₂ x) * star (g x))
      = fun x => f₁ x * star (g x) + f₂ x * star (g x) := by
    funext x; rw [add_mul]
  simp only [L2re]
  rw [hpt, integral_add hI1 hI2, Complex.add_re]

/-- `L2re` is additive over a double sum in its first argument (continuous case). -/
lemma L2re_sum2 {n : ℕ} {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : ι → κ → (Fin n → ℝ) → ℂ) (g : (Fin n → ℝ) → ℂ)
    (hF : ∀ i k, Continuous (F i k)) (hg : Continuous g) :
    L2re (fun x => ∑ i, ∑ k, F i k x) g = ∑ i, ∑ k, L2re (F i k) g := by
  rw [L2re_finset_sum Finset.univ (fun i => fun x => ∑ k, F i k x) g
    (fun i _ => continuous_finsetSum Finset.univ (fun k _ => hF i k)) hg]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact L2re_finset_sum Finset.univ (F i) g (fun k _ => hF i k) hg


/-- `L2re` of a double sum plus an extra summand (continuous case). -/
lemma L2re_sum2_add {n : ℕ} (F : Fin n → Fin n → (Fin n → ℝ) → ℂ) (G v : (Fin n → ℝ) → ℂ)
    (hF : ∀ a b, Continuous (F a b)) (hG : Continuous G) (hv : Continuous v) :
    L2re (fun x => (∑ a, ∑ b, F a b x) + G x) v
      = (∑ a, ∑ b, L2re (F a b) v) + L2re G v := by
  rw [L2re_add_left (continuous_finsetSum Finset.univ (fun a _ =>
      continuous_finsetSum Finset.univ (fun b _ => hF a b))) hG hv, L2re_sum2 F v hF hv]

/-! ## Components of a smooth matrix-valued function -/

/-- The iterated derivatives of a component of a smooth matrix-valued function are dominated by
the iterated derivatives of the matrix-valued function itself. -/
lemma norm_iteratedFDeriv_component_le {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {n : ℕ} (G : F → MatC n) (z : F) (hG : ContDiffAt ℝ (⊤ : ℕ∞) G z) (j : ℕ)
    (i j' : Fin n) :
    ‖iteratedFDeriv ℝ j (fun p => G p i j') z‖ ≤ ‖iteratedFDeriv ℝ j G z‖ := by
  set g : MatC n →L[ℝ] ℂ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j').comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => Fin n → ℂ) i) with hg
  have hcomp : (fun p => G p i j') = g ∘ G := by
    funext p
    simp [hg]
  have hle : ((j : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    rw [show ((j : ℕ) : WithTop ℕ∞) = ((j : ℕ∞) : WithTop ℕ∞) by simp]
    exact WithTop.coe_le_coe.mpr le_top
  rw [hcomp, g.iteratedFDeriv_comp_left (f := G) (x := z) hG hle]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le g
    (iteratedFDeriv ℝ j G z)).trans ?_
  have hgn : ‖g‖ ≤ 1 := by
    rw [hg]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun v => ?_)
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
    calc ‖v i j'‖ ≤ ‖v i‖ := norm_le_pi_norm _ _
      _ ≤ ‖v‖ := norm_le_pi_norm _ _
      _ = 1 * ‖v‖ := (one_mul _).symm
  calc ‖g‖ * ‖iteratedFDeriv ℝ j G z‖ ≤ 1 * ‖iteratedFDeriv ℝ j G z‖ :=
        mul_le_mul_of_nonneg_right hgn (norm_nonneg _)
    _ = ‖iteratedFDeriv ℝ j G z‖ := one_mul _

end

end Work.Diff.STE.flat
