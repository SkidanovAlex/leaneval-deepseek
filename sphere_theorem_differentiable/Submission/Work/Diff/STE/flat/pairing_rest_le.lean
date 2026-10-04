import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.level_defs
import Submission.Work.Diff.STE.flat.level_aux
import Submission.Work.Diff.STE.flat.inv_jet_bound_symm
import Submission.Work.Diff.STE.flat.leibniz_l2_gen
import Submission.Work.Diff.STE.flat.jet_comp_l2_local
import Submission.Work.Diff.STE.flat.jet_sup_le_uniform_level

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.flat

open MeasureTheory BigOperators Filter
open scoped Topology
open Work.Diff.STE.Flat

set_option maxHeartbeats 1000000

noncomputable section

/-! ## Part 1: comparing multilinear derivatives with iterated partial derivatives

`pdVec k l f x` is the `k`-fold partial derivative of the scalar function `f` along the coordinate
directions `l`.  The first lemma bounds the *operator norm* of the `k`-th iterated Fréchet
derivative of `f` by the sum of the absolute values of those partial derivatives (which are exactly
the values of `iteratedFDeriv` on the coordinate basis tuples).  The second transports this bound to
vector-valued functions by projecting onto the coordinates, and the third combines the two for the
value-and-first-jet map `jetP c`. -/

/-- A product of absolute values of the coordinates of vectors is bounded by the product of the
sup norms of those vectors. -/
lemma prod_abs_le_prod_norm {ι : Type*} [Fintype ι] {m : ℕ} (v : Fin m → (ι → ℝ))
    (r : Fin m → ι) : ∏ i : Fin m, |v i (r i)| ≤ ∏ i : Fin m, ‖v i‖ := by
  induction m with
  | zero => simp
  | succ k ih =>
    rw [Fin.prod_univ_castSucc (fun i : Fin (k + 1) => |v i (r i)|),
        Fin.prod_univ_castSucc (fun i : Fin (k + 1) => ‖v i‖)]
    exact mul_le_mul (ih (fun i : Fin k => v i.castSucc) (fun i : Fin k => r i.castSucc))
      (norm_le_pi_norm (v (Fin.last k)) (r (Fin.last k)))
      (abs_nonneg _) (Finset.prod_nonneg (fun i _ => norm_nonneg _))

/-- **Multilinear norms versus partial derivatives.**  For a `C^∞` scalar function on `ι → ℝ`, the
operator norm of the `k`-th iterated Fréchet derivative is at most the sum of the absolute values of
its `k`-th partial derivatives along the coordinate basis tuples.  (`private`: a sibling module
declares the same name, and both are imported downstream.) -/
private lemma norm_iteratedFDeriv_le_sum_pdVec {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ℕ)
    (f : (ι → ℝ) → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ m f x‖ ≤ ∑ l : Fin m → ι, ‖pdVec m l f x‖ := by
  refine (iteratedFDeriv ℝ m f x).opNorm_le_bound
    (Finset.sum_nonneg (fun l _ => norm_nonneg _)) (fun v => ?_)
  have hv : (fun i : Fin m => ∑ j : ι, Pi.single j (v i j)) = v := by
    funext i
    exact Finset.univ_sum_single (v i)
  have hexp : (iteratedFDeriv ℝ m f x) v
      = ∑ r : Fin m → ι, (∏ i : Fin m, v i (r i))
          • (iteratedFDeriv ℝ m f x) (fun i => Pi.single (r i) (1 : ℝ)) := by
    conv_lhs => rw [← hv]
    rw [ContinuousMultilinearMap.map_sum]
    refine Finset.sum_congr rfl (fun r _ => ?_)
    have hsmul : (fun i : Fin m => Pi.single (r i) (v i (r i)))
        = (fun i : Fin m => v i (r i) • Pi.single (r i) (1 : ℝ)) := by
      funext i j
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      by_cases h : j = r i <;> simp [h]
    rw [hsmul, ContinuousMultilinearMap.map_smul_univ]
  calc ‖(iteratedFDeriv ℝ m f x) v‖
      ≤ ∑ r : Fin m → ι, (∏ i : Fin m, ‖v i‖)
          * ‖(iteratedFDeriv ℝ m f x) (fun i => Pi.single (r i) (1 : ℝ))‖ := by
        rw [hexp]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun r _ => ?_))
        rw [norm_smul, norm_prod]
        exact mul_le_mul_of_nonneg_right (prod_abs_le_prod_norm v r) (norm_nonneg _)
    _ = (∏ i : Fin m, ‖v i‖)
          * ∑ r : Fin m → ι, ‖(iteratedFDeriv ℝ m f x) (fun i => Pi.single (r i) (1 : ℝ))‖ := by
        rw [Finset.mul_sum]
    _ = (∏ i : Fin m, ‖v i‖) * ∑ r : Fin m → ι, ‖pdVec m r f x‖ := by
        congr 1
        refine Finset.sum_congr rfl (fun r _ => ?_)
        rw [Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv m f hf x r]
    _ = (∑ r : Fin m → ι, ‖pdVec m r f x‖) * ∏ i : Fin m, ‖v i‖ := by ring

/-- **Multilinear norms versus the components of a product-valued function.**  For a `C^∞` map `V`
into a finite product `J → W`, the operator norm of the `k`-th iterated Fréchet derivative is at
most the sum of the operator norms of the `k`-th derivatives of the components. -/
lemma norm_iteratedFDeriv_pi_le {ι : Type*} [Fintype ι] [DecidableEq ι] {J : Type*} [Fintype J]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (m : ℕ)
    (V : (ι → ℝ) → (J → W)) (hV : ContDiff ℝ (⊤ : ℕ∞) V) (x : ι → ℝ) :
    ‖iteratedFDeriv ℝ m V x‖ ≤ ∑ j : J, ‖iteratedFDeriv ℝ m (fun y => V y j) x‖ := by
  refine (iteratedFDeriv ℝ m V x).opNorm_le_bound
    (Finset.sum_nonneg (fun j _ => norm_nonneg _)) (fun v => ?_)
  have hcomp : ∀ j : J, iteratedFDeriv ℝ m (fun y => V y j) x
      = (ContinuousLinearMap.proj j).compContinuousMultilinearMap (iteratedFDeriv ℝ m V x) := by
    intro j
    have h := ContinuousLinearMap.iteratedFDeriv_comp_left (𝕜 := ℝ)
      (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (ContinuousLinearMap.proj j) (f := V) (x := x)
      hV.contDiffAt (i := m)
      (WithTop.coe_le_coe.mpr le_top : ((m : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
    convert h using 2
    funext y
    rfl
  calc ‖(iteratedFDeriv ℝ m V x) v‖
      ≤ ∑ j : J, ‖(iteratedFDeriv ℝ m V x) v j‖ :=
        (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg (fun j _ => norm_nonneg _))).mpr
          (fun j => Finset.single_le_sum (fun j _ => norm_nonneg _) (Finset.mem_univ j))
    _ = ∑ j : J, ‖(iteratedFDeriv ℝ m (fun y => V y j) x) v‖ := by
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [hcomp j]
        rfl
    _ ≤ ∑ j : J, ‖iteratedFDeriv ℝ m (fun y => V y j) x‖ * ∏ i : Fin m, ‖v i‖ :=
        Finset.sum_le_sum (fun j _ => ContinuousMultilinearMap.le_opNorm _ _)
    _ = (∑ j : J, ‖iteratedFDeriv ℝ m (fun y => V y j) x‖) * ∏ i : Fin m, ‖v i‖ := by
        rw [Finset.sum_mul]

/-- **The norm of the iterated derivative of the jet.**  The operator norm of the `m`-th iterated
Fréchet derivative of `jetP c = (seriesFunM c, ∂ seriesFunM c)` is bounded by the sum of the
absolute values of the `m`-fold partial derivatives of the entries of `seriesFunM c` and of their
first partial derivatives, indexed by the product of the multi-index set with the matrix indices. -/
theorem jetP_iteratedFDeriv_norm_le {n s : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (hm : m ≤ s + 2)
      (c : (Fin n → ℤ) → MatC n)
      (hsm : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => jetP c x))
      (x : Fin n → ℝ),
      ‖iteratedFDeriv ℝ m (jetP c) x‖ ≤ C *
        ((∑ t : (Fin m → Fin n) × (Fin n × Fin n),
            ‖pdVec m t.1 (fun y : Fin n → ℝ => seriesFunM c y t.2.1 t.2.2) x‖)
         + ∑ t : (Fin m → Fin n) × (Fin n × (Fin n × Fin n)),
            ‖pdVec m t.1 (fun y : Fin n → ℝ => pd t.2.1
              (fun z : Fin n → ℝ => seriesFunM c z t.2.2.1 t.2.2.2) y) x‖) := by
  refine ⟨1, zero_le_one, ?_⟩
  intro m hm c hsm x
  have h1sm : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => (jetP c x).1) := contDiff_fst.comp hsm
  have h2sm : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => (jetP c x).2) := contDiff_snd.comp hsm
  have hpair : jetP c = fun x => ((jetP c x).1, (jetP c x).2) := by
    funext y
    rfl
  have hnorm : ‖iteratedFDeriv ℝ m (jetP c) x‖
      ≤ ‖iteratedFDeriv ℝ m (fun x : Fin n → ℝ => (jetP c x).1) x‖
        + ‖iteratedFDeriv ℝ m (fun x : Fin n → ℝ => (jetP c x).2) x‖ := by
    rw [hpair, iteratedFDeriv_prodMk h1sm.contDiffAt h2sm.contDiffAt (i := m)
      (WithTop.coe_le_coe.mpr le_top :
        ((m : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))]
    refine ContinuousMultilinearMap.opNorm_le_bound (by positivity) (fun v => ?_)
    rw [ContinuousMultilinearMap.prod_apply]
    calc ‖(iteratedFDeriv ℝ m (fun x : Fin n → ℝ => (jetP c x).1) x v,
            iteratedFDeriv ℝ m (fun x : Fin n → ℝ => (jetP c x).2) x v)‖
        ≤ ‖iteratedFDeriv ℝ m (fun x : Fin n → ℝ => (jetP c x).1) x v‖
          + ‖iteratedFDeriv ℝ m (fun x : Fin n → ℝ => (jetP c x).2) x v‖ := by
          rw [Prod.norm_def]
          exact max_le (le_add_of_nonneg_right (norm_nonneg _))
            (le_add_of_nonneg_left (norm_nonneg _))
      _ ≤ (‖iteratedFDeriv ℝ m (fun x : Fin n → ℝ => (jetP c x).1) x‖
            + ‖iteratedFDeriv ℝ m (fun x : Fin n → ℝ => (jetP c x).2) x‖)
            * ∏ i : Fin m, ‖v i‖ := by
          rw [add_mul]
          exact add_le_add (ContinuousMultilinearMap.le_opNorm _ _)
            (ContinuousMultilinearMap.le_opNorm _ _)
  -- the two product-type identifications
  have hprod1 : ∀ F : Fin n → Fin n → ℝ,
      (∑ t : (Fin n) × (Fin n), F t.1 t.2) = ∑ i, ∑ j, F i j := by
    intro F
    rw [Fintype.sum_prod_type]
  have hprod2 : ∀ F : (Fin m → Fin n) → Fin n → Fin n → ℝ,
      (∑ t : (Fin m → Fin n) × (Fin n × Fin n), F t.1 t.2.1 t.2.2)
        = ∑ l, ∑ i, ∑ j, F l i j := by
    intro F
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Fintype.sum_prod_type]
  have hprod3 : ∀ F : (Fin m → Fin n) → Fin n → Fin n → Fin n → ℝ,
      (∑ t : (Fin m → Fin n) × (Fin n × (Fin n × Fin n)),
          F t.1 t.2.1 t.2.2.1 t.2.2.2) = ∑ l, ∑ a, ∑ i, ∑ j, F l a i j := by
    intro F
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Fintype.sum_prod_type]
  -- the value component
  have hP1 : ‖iteratedFDeriv ℝ m (fun x : Fin n → ℝ => (jetP c x).1) x‖
      ≤ ∑ t : (Fin m → Fin n) × (Fin n × Fin n),
          ‖pdVec m t.1 (fun y : Fin n → ℝ => seriesFunM c y t.2.1 t.2.2) x‖ := by
    have h1i : ∀ i : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => (jetP c x).1 i) :=
      fun i => (contDiff_pi.mp h1sm) i
    have h1ij : ∀ i j : Fin n,
        ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => (jetP c x).1 i j) :=
      fun i j => (contDiff_pi.mp (h1i i)) j
    have hstep : ‖iteratedFDeriv ℝ m (fun x : Fin n → ℝ => (jetP c x).1) x‖
        ≤ ∑ i : Fin n, ∑ j : Fin n,
            ∑ l : Fin m → Fin n, ‖pdVec m l (fun y : Fin n → ℝ => seriesFunM c y i j) x‖ := by
      calc ‖iteratedFDeriv ℝ m (fun x : Fin n → ℝ => (jetP c x).1) x‖
          ≤ ∑ i : Fin n, ‖iteratedFDeriv ℝ m (fun y => (jetP c y).1 i) x‖ :=
            norm_iteratedFDeriv_pi_le m _ h1sm x
        _ ≤ ∑ i : Fin n, ∑ j : Fin n, ‖iteratedFDeriv ℝ m (fun y => (jetP c y).1 i j) x‖ :=
            Finset.sum_le_sum (fun i _ => norm_iteratedFDeriv_pi_le m _ (h1i i) x)
        _ ≤ ∑ i : Fin n, ∑ j : Fin n,
              ∑ l : Fin m → Fin n, ‖pdVec m l (fun y : Fin n → ℝ => seriesFunM c y i j) x‖ :=
            Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
              norm_iteratedFDeriv_le_sum_pdVec m _ (h1ij i j) x))
    calc ‖iteratedFDeriv ℝ m (fun x : Fin n → ℝ => (jetP c x).1) x‖
        ≤ ∑ i : Fin n, ∑ j : Fin n,
            ∑ l : Fin m → Fin n, ‖pdVec m l (fun y : Fin n → ℝ => seriesFunM c y i j) x‖ :=
          hstep
      _ = ∑ l : Fin m → Fin n, ∑ i : Fin n, ∑ j : Fin n,
            ‖pdVec m l (fun y : Fin n → ℝ => seriesFunM c y i j) x‖ := by
          calc (∑ i : Fin n, ∑ j : Fin n,
                ∑ l : Fin m → Fin n, ‖pdVec m l (fun y : Fin n → ℝ => seriesFunM c y i j) x‖)
              = ∑ i : Fin n, ∑ l : Fin m → Fin n, ∑ j : Fin n,
                  ‖pdVec m l (fun y : Fin n → ℝ => seriesFunM c y i j) x‖ :=
                Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
            _ = ∑ l : Fin m → Fin n, ∑ i : Fin n, ∑ j : Fin n,
                  ‖pdVec m l (fun y : Fin n → ℝ => seriesFunM c y i j) x‖ := Finset.sum_comm
      _ = ∑ t : (Fin m → Fin n) × (Fin n × Fin n),
            ‖pdVec m t.1 (fun y : Fin n → ℝ => seriesFunM c y t.2.1 t.2.2) x‖ :=
          (hprod2 (fun l i j => ‖pdVec m l (fun y : Fin n → ℝ => seriesFunM c y i j) x‖)).symm
  -- the first-jet component
  have hP2 : ‖iteratedFDeriv ℝ m (fun x : Fin n → ℝ => (jetP c x).2) x‖
      ≤ ∑ t : (Fin m → Fin n) × (Fin n × (Fin n × Fin n)),
          ‖pdVec m t.1 (fun y : Fin n → ℝ => pd t.2.1
            (fun z : Fin n → ℝ => seriesFunM c z t.2.2.1 t.2.2.2) y) x‖ := by
    have h2a : ∀ a : Fin n, ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => (jetP c x).2 a) :=
      fun a => (contDiff_pi.mp h2sm) a
    have h2ai : ∀ a i : Fin n,
        ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => (jetP c x).2 a i) :=
      fun a i => (contDiff_pi.mp (h2a a)) i
    have h2aij : ∀ a i j : Fin n,
        ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => (jetP c x).2 a i j) :=
      fun a i j => (contDiff_pi.mp (h2ai a i)) j
    have hstep : ‖iteratedFDeriv ℝ m (fun x : Fin n → ℝ => (jetP c x).2) x‖
        ≤ ∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin m → Fin n,
            ‖pdVec m l (fun y : Fin n → ℝ => pd a
              (fun z : Fin n → ℝ => seriesFunM c z i j) y) x‖ := by
      calc ‖iteratedFDeriv ℝ m (fun x : Fin n → ℝ => (jetP c x).2) x‖
          ≤ ∑ a : Fin n, ‖iteratedFDeriv ℝ m (fun y => (jetP c y).2 a) x‖ :=
            norm_iteratedFDeriv_pi_le m _ h2sm x
        _ ≤ ∑ a : Fin n, ∑ i : Fin n, ‖iteratedFDeriv ℝ m (fun y => (jetP c y).2 a i) x‖ :=
            Finset.sum_le_sum (fun a _ => norm_iteratedFDeriv_pi_le m _ (h2a a) x)
        _ ≤ ∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n,
              ‖iteratedFDeriv ℝ m (fun y => (jetP c y).2 a i j) x‖ :=
            Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun i _ =>
              norm_iteratedFDeriv_pi_le m _ (h2ai a i) x))
        _ ≤ ∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin m → Fin n,
              ‖pdVec m l (fun y : Fin n → ℝ => pd a
                (fun z : Fin n → ℝ => seriesFunM c z i j) y) x‖ :=
            Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun i _ =>
              Finset.sum_le_sum (fun j _ =>
                norm_iteratedFDeriv_le_sum_pdVec m _ (h2aij a i j) x)))
    calc ‖iteratedFDeriv ℝ m (fun x : Fin n → ℝ => (jetP c x).2) x‖
        ≤ ∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin m → Fin n,
            ‖pdVec m l (fun y : Fin n → ℝ => pd a
              (fun z : Fin n → ℝ => seriesFunM c z i j) y) x‖ := hstep
      _ = ∑ l : Fin m → Fin n, ∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n,
            ‖pdVec m l (fun y : Fin n → ℝ => pd a
              (fun z : Fin n → ℝ => seriesFunM c z i j) y) x‖ := by
          calc (∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin m → Fin n,
                ‖pdVec m l (fun y : Fin n → ℝ => pd a
                  (fun z : Fin n → ℝ => seriesFunM c z i j) y) x‖)
              = ∑ a : Fin n, ∑ i : Fin n, ∑ l : Fin m → Fin n, ∑ j : Fin n,
                  ‖pdVec m l (fun y : Fin n → ℝ => pd a
                    (fun z : Fin n → ℝ => seriesFunM c z i j) y) x‖ :=
                Finset.sum_congr rfl (fun a _ =>
                  Finset.sum_congr rfl (fun i _ => Finset.sum_comm))
            _ = ∑ a : Fin n, ∑ l : Fin m → Fin n, ∑ i : Fin n, ∑ j : Fin n,
                  ‖pdVec m l (fun y : Fin n → ℝ => pd a
                    (fun z : Fin n → ℝ => seriesFunM c z i j) y) x‖ :=
                Finset.sum_congr rfl (fun a _ => Finset.sum_comm)
            _ = ∑ l : Fin m → Fin n, ∑ a : Fin n, ∑ i : Fin n, ∑ j : Fin n,
                  ‖pdVec m l (fun y : Fin n → ℝ => pd a
                    (fun z : Fin n → ℝ => seriesFunM c z i j) y) x‖ := Finset.sum_comm
      _ = ∑ t : (Fin m → Fin n) × (Fin n × (Fin n × Fin n)),
            ‖pdVec m t.1 (fun y : Fin n → ℝ => pd t.2.1
              (fun z : Fin n → ℝ => seriesFunM c z t.2.2.1 t.2.2.2) y) x‖ :=
          (hprod3 (fun l a i j => ‖pdVec m l (fun y : Fin n → ℝ => pd a
            (fun z : Fin n → ℝ => seriesFunM c z i j) y) x‖)).symm
  calc ‖iteratedFDeriv ℝ m (jetP c) x‖
      ≤ ‖iteratedFDeriv ℝ m (fun x : Fin n → ℝ => (jetP c x).1) x‖
        + ‖iteratedFDeriv ℝ m (fun x : Fin n → ℝ => (jetP c x).2) x‖ := hnorm
    _ ≤ (∑ t : (Fin m → Fin n) × (Fin n × Fin n),
          ‖pdVec m t.1 (fun y : Fin n → ℝ => seriesFunM c y t.2.1 t.2.2) x‖)
        + ∑ t : (Fin m → Fin n) × (Fin n × (Fin n × Fin n)),
          ‖pdVec m t.1 (fun y : Fin n → ℝ => pd t.2.1
            (fun z : Fin n → ℝ => seriesFunM c z t.2.2.1 t.2.2.2) y) x‖ :=
        add_le_add hP1 hP2
    _ = 1 * ((∑ t : (Fin m → Fin n) × (Fin n × Fin n),
          ‖pdVec m t.1 (fun y : Fin n → ℝ => seriesFunM c y t.2.1 t.2.2) x‖)
        + ∑ t : (Fin m → Fin n) × (Fin n × (Fin n × Fin n)),
          ‖pdVec m t.1 (fun y : Fin n → ℝ => pd t.2.1
            (fun z : Fin n → ℝ => seriesFunM c z t.2.2.1 t.2.2.2) y) x‖) := by
        rw [one_mul]

/-! ## Part 2: regularity and energy bounds for the jet -/

/-- The entries of `seriesFunM c` are `C^∞` when the coefficient family is supported in `box n N`. -/
lemma seriesFunM_entry_contDiff {n : ℕ} (N : ℕ) (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) (i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => seriesFunM c x i j) := by
  have h := Work.Diff.STE.contDiff_seriesFun (c := fun k : Fin n → ℤ => c k i j)
    (fun M => summable_moment_box c hc i j M)
  simpa only [Flat.seriesFunM_apply] using h

/-- The first partial derivatives of the entries of `seriesFunM c` are `C^∞` when the coefficient
family is supported in `box n N`. -/
lemma seriesFunM_entry_pd_contDiff {n : ℕ} (N : ℕ) (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) (a i j : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => pd a (fun y => seriesFunM c y i j) x) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fun y : Fin n → ℝ => seriesFunM c y i j)) :=
    (seriesFunM_entry_contDiff N c hc i j).fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ =>
      (fderiv ℝ (fun y : Fin n → ℝ => seriesFunM c y i j) x) (Pi.single a 1)) :=
    h1.clm_apply contDiff_const
  simpa only [pd] using h2

/-- The value-and-first-jet map of a box-supported coefficient family is `C^∞`. -/
lemma jetP_contDiff {n : ℕ} (N : ℕ) (c : (Fin n → ℤ) → MatC n)
    (hc : ∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => jetP c x) := by
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => seriesFunM c x) :=
    contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => seriesFunM_entry_contDiff N c hc i j))
  have h1 : ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Fin n → ℝ => fun a i j => pd a (fun y => seriesFunM c y i j) x) :=
    contDiff_pi.mpr (fun a => contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j =>
      seriesFunM_entry_pd_contDiff N c hc a i j)))
  simpa only [jetP] using h0.prodMk h1

/-- The first partial derivative of a scalar function, iterated along `l`, equals the iterated
partial derivative along the concatenated multi-index `l ++ [a]`. -/
lemma pdVec_pd_eq {n : ℕ} (m : ℕ) (l : Fin m → Fin n) (a : Fin n) (g : (Fin n → ℝ) → ℂ) :
    pdVec m l (pd a g) = pdVec (m + 1) (Fin.append l ![a]) g := by
  simp only [pdVec, pdList, List.ofFn_fin_append, List.foldr_append]
  rfl

/-- **`L²` bounds for the jets of the matrix entries.**  For a coefficient family supported in
`box n N`, every `m`-fold partial derivative (`m ≤ M`) of every entry of `seriesFunM c` has
`L²` norm squared at most a constant (depending only on `n` and `M`) times `ENormSqFull M`. -/
lemma entry_pdVec_l2_le {n : ℕ} (M : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) →
      ∀ (m : ℕ) (hm : m ≤ M) (l : Fin m → Fin n) (i j : Fin n),
        ∫ x in unitCube (ι := Fin n),
          ‖pdVec m l (fun y : Fin n → ℝ => seriesFunM c y i j) x‖ ^ 2
          ≤ C * ENormSqFull M (seriesFunM c) := by
  obtain ⟨Ce, hCe, hCe'⟩ := invJet_CSq_entry_le_uniform (n := n) M
  refine ⟨((2 * Real.pi) ^ 2) ^ M * Ce, by positivity, ?_⟩
  intro N c hc m hm l i j
  have hmom : ∀ K : ℕ, Summable (fun k : Fin n → ℤ => (wt k) ^ K * ‖c k i j‖) :=
    fun K => summable_moment_box c hc i j K
  have hY : 0 ≤ Ce * ENormSqFull M (seriesFunM c) :=
    mul_nonneg hCe (ENormSqFull_nonneg M _)
  have hcsq : CSq M (fun k : Fin n → ℤ => c k i j)
      ≤ (Ce * ENormSqFull M (seriesFunM c)) * (1 + 0) ^ 2 := by
    simpa using hCe' N c hc i j
  have hfun : (fun y : Fin n → ℝ => seriesFunM c y i j) = Work.Diff.STE.seriesFun
      (fun k : Fin n → ℤ => c k i j) := by
    funext y
    rw [Flat.seriesFunM_apply]
  rw [hfun]
  refine (invJet_int_pdVec_seriesFun_le (n := n) (s := M) (d := fun k : Fin n → ℤ => c k i j)
    hmom (Y := Ce * ENormSqFull M (seriesFunM c)) (Bs := 0) hY hcsq m hm l).trans_eq ?_
  ring

/-- Cauchy–Schwarz in a finite sum. -/
lemma sq_sum_le_card_mul {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    (∑ i, f i) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, (f i) ^ 2 := by
  simpa [Finset.card_univ] using sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := f)

/-- The integral of the square of a finite sum of continuous real functions. -/
lemma integral_sq_sum_le {ι : Type*} [Fintype ι] {n : ℕ} (u : ι → (Fin n → ℝ) → ℝ)
    (hu : ∀ i, Continuous (u i)) (B : ℝ) (hB : 0 ≤ B)
    (hint : ∀ i, ∫ y in unitCube (ι := Fin n), (u i y) ^ 2 ≤ B) :
    ∫ y in unitCube (ι := Fin n), (∑ i, u i y) ^ 2
      ≤ (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) * B) := by
  have hpt : ∀ y : Fin n → ℝ, (∑ i, u i y) ^ 2 ≤ (Fintype.card ι : ℝ) * ∑ i, (u i y) ^ 2 :=
    fun y => sq_sum_le_card_mul (fun i => u i y)
  have hcontL : Continuous fun y : Fin n → ℝ => (∑ i, u i y) ^ 2 :=
    (continuous_finsetSum _ (fun i _ => hu i)).pow 2
  have hcontR : Continuous fun y : Fin n → ℝ => (Fintype.card ι : ℝ) * ∑ i, (u i y) ^ 2 :=
    continuous_const.mul (continuous_finsetSum _ (fun i _ => (hu i).pow 2))
  have h1 : ∫ y in unitCube (ι := Fin n), (∑ i, u i y) ^ 2
      ≤ ∫ y in unitCube (ι := Fin n), (Fintype.card ι : ℝ) * ∑ i, (u i y) ^ 2 :=
    integral_mono_ae (el_integrableOn_unitCube_of_continuous_real hcontL)
      (el_integrableOn_unitCube_of_continuous_real hcontR) (Filter.Eventually.of_forall hpt)
  have h2 : ∫ y in unitCube (ι := Fin n), (Fintype.card ι : ℝ) * ∑ i, (u i y) ^ 2
      = (Fintype.card ι : ℝ) * ∑ i, ∫ y in unitCube (ι := Fin n), (u i y) ^ 2 := by
    rw [integral_const_mul]
    congr 1
    exact integral_finsetSum (s := Finset.univ) (f := fun i y => (u i y) ^ 2)
      (fun i _ => el_integrableOn_unitCube_of_continuous_real ((hu i).pow 2))
  rw [h2] at h1
  refine h1.trans ?_
  have hsum : ∑ i : ι, ∫ y in unitCube (ι := Fin n), (u i y) ^ 2
      ≤ (Fintype.card ι : ℝ) * B := by
    calc ∑ i : ι, ∫ y in unitCube (ι := Fin n), (u i y) ^ 2
        ≤ ∑ _i : ι, B := Finset.sum_le_sum (fun i _ => hint i)
      _ = (Fintype.card ι : ℝ) * B := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

/-- The integral of the square of a sum of two continuous real functions. -/
lemma integral_sq_add_le {n : ℕ} (A B : (Fin n → ℝ) → ℝ) (hA : Continuous A)
    (hB : Continuous B) :
    ∫ y in unitCube (ι := Fin n), (A y + B y) ^ 2
      ≤ 2 * ((∫ y in unitCube (ι := Fin n), A y ^ 2)
        + (∫ y in unitCube (ι := Fin n), B y ^ 2)) := by
  have hpt : ∀ y : Fin n → ℝ, (A y + B y) ^ 2 ≤ 2 * (A y ^ 2 + B y ^ 2) :=
    fun y => by nlinarith [sq_nonneg (A y - B y)]
  have hcontL : Continuous fun y : Fin n → ℝ => (A y + B y) ^ 2 := (hA.add hB).pow 2
  have hcontR : Continuous fun y : Fin n → ℝ => 2 * (A y ^ 2 + B y ^ 2) :=
    continuous_const.mul ((hA.pow 2).add (hB.pow 2))
  have h1 := integral_mono_ae (el_integrableOn_unitCube_of_continuous_real hcontL)
    (el_integrableOn_unitCube_of_continuous_real hcontR) (Filter.Eventually.of_forall hpt)
  have h2 : ∫ y in unitCube (ι := Fin n), 2 * (A y ^ 2 + B y ^ 2)
      = 2 * ((∫ y in unitCube (ι := Fin n), A y ^ 2)
        + (∫ y in unitCube (ι := Fin n), B y ^ 2)) := by
    rw [integral_const_mul]
    have hAB : ∫ y in unitCube (ι := Fin n), (A y ^ 2 + B y ^ 2)
        = (∫ y in unitCube (ι := Fin n), A y ^ 2)
          + (∫ y in unitCube (ι := Fin n), B y ^ 2) :=
      integral_add (el_integrableOn_unitCube_of_continuous_real (hA.pow 2))
        (el_integrableOn_unitCube_of_continuous_real (hB.pow 2))
    rw [hAB]
  rw [h2] at h1
  exact h1

/-- **`L²` bound for the iterated derivatives of the jet.**  For a coefficient family supported in
`box n N`, the `L²` norm squared of the `m`-th iterated Fréchet derivative of `jetP c`
(`m ≤ s + 1`) is bounded by a constant times the sum of the level-`(s+1)` and level-`(s+2)`
energies. -/
lemma jetP_l2_le {n s : ℕ} (hn : 1 ≤ n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) →
      ∀ (m : ℕ) (hm : m ≤ s + 1) (x : Fin n → ℝ),
        (∫ y in unitCube (ι := Fin n), ‖iteratedFDeriv ℝ m (jetP c) y‖ ^ 2)
          ≤ C * (ENormSqFull (s + 1) (seriesFunM c)
            + ENormSqFull (s + 2) (seriesFunM c)) := by
  obtain ⟨Cj, hCj, hj⟩ := jetP_iteratedFDeriv_norm_le (n := n) (s := s)
  obtain ⟨CL1, hCL1, hL1⟩ := entry_pdVec_l2_le (n := n) (s + 1)
  obtain ⟨CL2, hCL2, hL2⟩ := entry_pdVec_l2_le (n := n) (s + 2)
  refine ⟨2 * Cj ^ 2 * (((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 2) ^ 2 * CL1
      + ((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 3) ^ 2 * CL2) + 1, by positivity, ?_⟩
  intro N c hc m hm x
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => jetP c x) := jetP_contDiff N c hc
  have hm2 : m ≤ s + 2 := by omega
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  let A : (Fin n → ℝ) → ℝ := fun y => ∑ t : (Fin m → Fin n) × (Fin n × Fin n),
      ‖pdVec m t.1 (fun z : Fin n → ℝ => seriesFunM c z t.2.1 t.2.2) y‖
  let B : (Fin n → ℝ) → ℝ := fun y => ∑ t : (Fin m → Fin n) × (Fin n × (Fin n × Fin n)),
      ‖pdVec m t.1 (fun z : Fin n → ℝ => pd t.2.1
        (fun w : Fin n → ℝ => seriesFunM c w t.2.2.1 t.2.2.2) z) y‖
  have hpt : ∀ y : Fin n → ℝ, ‖iteratedFDeriv ℝ m (jetP c) y‖ ≤ Cj * (A y + B y) := by
    intro y
    exact hj m hm2 c hsm y
  have hu_cont : ∀ t : (Fin m → Fin n) × (Fin n × Fin n),
      Continuous (fun y : Fin n → ℝ => ‖pdVec m t.1
        (fun z : Fin n → ℝ => seriesFunM c z t.2.1 t.2.2) y‖) := by
    intro t
    refine (continuous_pdVec m t.1 _
      ((seriesFunM_entry_contDiff N c hc t.2.1 t.2.2).of_le (by simp))).norm
  have hv_cont : ∀ t : (Fin m → Fin n) × (Fin n × (Fin n × Fin n)),
      Continuous (fun y : Fin n → ℝ => ‖pdVec m t.1 (fun z : Fin n → ℝ => pd t.2.1
        (fun w : Fin n → ℝ => seriesFunM c w t.2.2.1 t.2.2.2) z) y‖) := by
    intro t
    refine (continuous_pdVec m t.1 _
      ((seriesFunM_entry_pd_contDiff N c hc t.2.1 t.2.2.1 t.2.2.2).of_le (by simp))).norm
  have hA_cont : Continuous A := by
    refine continuous_finsetSum _ (fun t _ => hu_cont t)
  have hB_cont : Continuous B := by
    refine continuous_finsetSum _ (fun t _ => hv_cont t)
  have hpt2 : ∀ y : Fin n → ℝ, ‖iteratedFDeriv ℝ m (jetP c) y‖ ^ 2
      ≤ Cj ^ 2 * (A y + B y) ^ 2 := by
    intro y
    calc ‖iteratedFDeriv ℝ m (jetP c) y‖ ^ 2 ≤ (Cj * (A y + B y)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hpt y) 2
      _ = Cj ^ 2 * (A y + B y) ^ 2 := by ring
  have hcontL : Continuous fun y : Fin n → ℝ => ‖iteratedFDeriv ℝ m (jetP c) y‖ ^ 2 :=
    ((hsm.continuous_iteratedFDeriv (m := m) (by simp)).norm).pow 2
  have hcontR : Continuous fun y : Fin n → ℝ => Cj ^ 2 * (A y + B y) ^ 2 :=
    continuous_const.mul ((hA_cont.add hB_cont).pow 2)
  have hstep1 : (∫ y in unitCube (ι := Fin n), ‖iteratedFDeriv ℝ m (jetP c) y‖ ^ 2)
      ≤ Cj ^ 2 * ∫ y in unitCube (ι := Fin n), (A y + B y) ^ 2 := by
    have h1 : (∫ y in unitCube (ι := Fin n), ‖iteratedFDeriv ℝ m (jetP c) y‖ ^ 2)
        ≤ ∫ y in unitCube (ι := Fin n), Cj ^ 2 * (A y + B y) ^ 2 :=
      integral_mono_ae (el_integrableOn_unitCube_of_continuous_real hcontL)
        (el_integrableOn_unitCube_of_continuous_real hcontR) (Filter.Eventually.of_forall hpt2)
    have h2 : (∫ y in unitCube (ι := Fin n), Cj ^ 2 * (A y + B y) ^ 2)
        = Cj ^ 2 * ∫ y in unitCube (ι := Fin n), (A y + B y) ^ 2 := by
      rw [integral_const_mul]
    rw [h2] at h1
    exact h1
  have hcard1 : (Fintype.card ((Fin m → Fin n) × (Fin n × Fin n)) : ℝ)
      ≤ (n : ℝ) ^ (s + 1) * (n : ℝ) ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    push_cast
    calc (n : ℝ) ^ m * ((n : ℝ) * (n : ℝ))
        ≤ (n : ℝ) ^ (s + 1) * ((n : ℝ) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hn1 (by omega)) (by positivity)
      _ = (n : ℝ) ^ (s + 1) * (n : ℝ) ^ 2 := by ring
  have hcard2 : (Fintype.card ((Fin m → Fin n) × (Fin n × (Fin n × Fin n))) : ℝ)
      ≤ (n : ℝ) ^ (s + 1) * (n : ℝ) ^ 3 := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    push_cast
    calc (n : ℝ) ^ m * ((n : ℝ) * ((n : ℝ) * (n : ℝ)))
        ≤ (n : ℝ) ^ (s + 1) * ((n : ℝ) * ((n : ℝ) * (n : ℝ))) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hn1 (by omega)) (by positivity)
      _ = (n : ℝ) ^ (s + 1) * (n : ℝ) ^ 3 := by ring
  have hA2 : (∫ y in unitCube (ι := Fin n), A y ^ 2)
      ≤ ((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 2)
        * (((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 2)
          * (CL1 * ENormSqFull (s + 1) (seriesFunM c))) := by
    have hnon : 0 ≤ CL1 * ENormSqFull (s + 1) (seriesFunM c) :=
      mul_nonneg hCL1 (ENormSqFull_nonneg _ _)
    have h1 : (∫ y in unitCube (ι := Fin n), A y ^ 2)
        ≤ (Fintype.card ((Fin m → Fin n) × (Fin n × Fin n)) : ℝ)
          * ((Fintype.card ((Fin m → Fin n) × (Fin n × Fin n)) : ℝ)
            * (CL1 * ENormSqFull (s + 1) (seriesFunM c))) := by
      refine integral_sq_sum_le (fun t : (Fin m → Fin n) × (Fin n × Fin n) => fun y =>
        ‖pdVec m t.1 (fun z : Fin n → ℝ => seriesFunM c z t.2.1 t.2.2) y‖) hu_cont
        (CL1 * ENormSqFull (s + 1) (seriesFunM c)) hnon ?_
      intro t
      exact hL1 N c hc m (le_trans hm (by omega)) t.1 t.2.1 t.2.2
    exact h1.trans (by
      refine mul_le_mul hcard1 (mul_le_mul hcard1 le_rfl hnon (by positivity))
        (mul_nonneg (by positivity) hnon) (by positivity))
  have hB2 : (∫ y in unitCube (ι := Fin n), B y ^ 2)
      ≤ ((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 3)
        * (((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 3)
          * (CL2 * ENormSqFull (s + 2) (seriesFunM c))) := by
    have hnon : 0 ≤ CL2 * ENormSqFull (s + 2) (seriesFunM c) :=
      mul_nonneg hCL2 (ENormSqFull_nonneg _ _)
    have h1 : (∫ y in unitCube (ι := Fin n), B y ^ 2)
        ≤ (Fintype.card ((Fin m → Fin n) × (Fin n × (Fin n × Fin n))) : ℝ)
          * ((Fintype.card ((Fin m → Fin n) × (Fin n × (Fin n × Fin n))) : ℝ)
            * (CL2 * ENormSqFull (s + 2) (seriesFunM c))) := by
      refine integral_sq_sum_le (fun t : (Fin m → Fin n) × (Fin n × (Fin n × Fin n)) => fun y =>
        ‖pdVec m t.1 (fun z : Fin n → ℝ => pd t.2.1
          (fun w : Fin n → ℝ => seriesFunM c w t.2.2.1 t.2.2.2) z) y‖) hv_cont
        (CL2 * ENormSqFull (s + 2) (seriesFunM c)) hnon ?_
      intro t
      rw [pdVec_pd_eq m t.1 t.2.1 (fun z : Fin n → ℝ => seriesFunM c z t.2.2.1 t.2.2.2)]
      exact hL2 N c hc (m + 1) (by omega) (Fin.append t.1 ![t.2.1]) t.2.2.1 t.2.2.2
    exact h1.trans (by
      refine mul_le_mul hcard2 (mul_le_mul hcard2 le_rfl hnon (by positivity))
        (mul_nonneg (by positivity) hnon) (by positivity))
  have hsum2 : ((∫ y in unitCube (ι := Fin n), A y ^ 2)
        + (∫ y in unitCube (ι := Fin n), B y ^ 2))
      ≤ (((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 2) ^ 2 * CL1) * ENormSqFull (s + 1) (seriesFunM c)
        + (((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 3) ^ 2 * CL2) * ENormSqFull (s + 2) (seriesFunM c) := by
    refine add_le_add ?_ ?_
    · calc (∫ y in unitCube (ι := Fin n), A y ^ 2)
          ≤ ((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 2)
            * (((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 2)
              * (CL1 * ENormSqFull (s + 1) (seriesFunM c))) := hA2
        _ = (((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 2) ^ 2 * CL1)
              * ENormSqFull (s + 1) (seriesFunM c) := by ring
    · calc (∫ y in unitCube (ι := Fin n), B y ^ 2)
          ≤ ((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 3)
            * (((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 3)
              * (CL2 * ENormSqFull (s + 2) (seriesFunM c))) := hB2
        _ = (((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 3) ^ 2 * CL2)
              * ENormSqFull (s + 2) (seriesFunM c) := by ring
  have hF1 : 0 ≤ ENormSqFull (s + 1) (seriesFunM c) := ENormSqFull_nonneg _ _
  have hF2 : 0 ≤ ENormSqFull (s + 2) (seriesFunM c) := ENormSqFull_nonneg _ _
  have hP : 0 ≤ ((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 2) ^ 2 * CL1 :=
    mul_nonneg (sq_nonneg _) hCL1
  have hQ : 0 ≤ ((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 3) ^ 2 * CL2 :=
    mul_nonneg (sq_nonneg _) hCL2
  have hfinal : Cj ^ 2 * 2 * ((((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 2) ^ 2 * CL1)
        * ENormSqFull (s + 1) (seriesFunM c)
      + (((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 3) ^ 2 * CL2)
        * ENormSqFull (s + 2) (seriesFunM c))
      ≤ (2 * Cj ^ 2 * (((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 2) ^ 2 * CL1
          + ((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 3) ^ 2 * CL2) + 1)
        * (ENormSqFull (s + 1) (seriesFunM c) + ENormSqFull (s + 2) (seriesFunM c)) := by
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg Cj) hP) hF2,
      mul_nonneg (mul_nonneg (sq_nonneg Cj) hQ) hF1,
      mul_nonneg (sq_nonneg Cj) hF1, mul_nonneg (sq_nonneg Cj) hF2, hF1, hF2]
  have hmid : Cj ^ 2 * (∫ y in unitCube (ι := Fin n), (A y + B y) ^ 2)
      ≤ Cj ^ 2 * 2 * ((∫ y in unitCube (ι := Fin n), A y ^ 2)
        + (∫ y in unitCube (ι := Fin n), B y ^ 2)) := by
    calc Cj ^ 2 * (∫ y in unitCube (ι := Fin n), (A y + B y) ^ 2)
        ≤ Cj ^ 2 * (2 * ((∫ y in unitCube (ι := Fin n), A y ^ 2)
          + (∫ y in unitCube (ι := Fin n), B y ^ 2))) :=
          mul_le_mul_of_nonneg_left (integral_sq_add_le A B hA_cont hB_cont) (by positivity)
      _ = Cj ^ 2 * 2 * ((∫ y in unitCube (ι := Fin n), A y ^ 2)
          + (∫ y in unitCube (ι := Fin n), B y ^ 2)) := by ring
  have hAB : Cj ^ 2 * 2 * ((∫ y in unitCube (ι := Fin n), A y ^ 2)
        + (∫ y in unitCube (ι := Fin n), B y ^ 2))
      ≤ Cj ^ 2 * 2 * ((((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 2) ^ 2 * CL1)
        * ENormSqFull (s + 1) (seriesFunM c)
        + (((n : ℝ) ^ (s + 1) * (n : ℝ) ^ 3) ^ 2 * CL2)
          * ENormSqFull (s + 2) (seriesFunM c)) :=
    mul_le_mul_of_nonneg_left hsum2 (by positivity)
  exact (hstep1.trans hmid).trans (hAB.trans hfinal)

/-- **Sup bound for the iterated derivatives of the jet.**  For a coefficient family supported in
`box n N` with `ENormSqFull s ≤ Bs²`, the `m`-th iterated Fréchet derivative of `jetP c` is
bounded by `C (1 + Bs)` for `m ≤ M`, uniformly in `N`, `c` and `m`. -/
lemma jetP_sup_le {n s : ℕ} (hn : 1 ≤ n) (hs : n + 5 ≤ s) (Bs : ℝ) (hBs : 0 ≤ Bs) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) →
      ENormSqFull s (seriesFunM c) ≤ Bs ^ 2 →
      ∀ (M : ℕ), M + 1 + sob n ≤ s →
      ∀ (m : ℕ), m ≤ M → ∀ x : Fin n → ℝ,
        ‖iteratedFDeriv ℝ m (jetP c) x‖ ≤ C * (1 + Bs) := by
  obtain ⟨Cj, hCj, hj⟩ := jetP_iteratedFDeriv_norm_le (n := n) (s := s)
  obtain ⟨Cs, hCs, hs'⟩ := jet_sup_le_uniform_level (n := n) (s := s)
  refine ⟨Cj * (((n : ℝ) ^ s * (n : ℝ) ^ 2) + ((n : ℝ) ^ s * (n : ℝ) ^ 3)) * Cs,
    by positivity, ?_⟩
  intro N c hc hen M hMs m hm x
  have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => jetP c x) := jetP_contDiff N c hc
  have hm2 : m ≤ s + 2 := by omega
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hms : m ≤ s := by omega
  have hsq : Real.sqrt (ENormSqFull s (seriesFunM c)) ≤ Bs := by
    rw [← Real.sqrt_sq hBs]
    exact Real.sqrt_le_sqrt hen
  have hterm1 : ∀ t : (Fin m → Fin n) × (Fin n × Fin n),
      ‖pdVec m t.1 (fun z : Fin n → ℝ => seriesFunM c z t.2.1 t.2.2) x‖
        ≤ Cs * (1 + Bs) := by
    intro t
    refine (hs' m (by omega) N c hc t.1 t.2.1 t.2.2 x).trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith) hCs
  have hterm2 : ∀ t : (Fin m → Fin n) × (Fin n × (Fin n × Fin n)),
      ‖pdVec m t.1 (fun z : Fin n → ℝ => pd t.2.1
        (fun w : Fin n → ℝ => seriesFunM c w t.2.2.1 t.2.2.2) z) x‖ ≤ Cs * (1 + Bs) := by
    intro t
    rw [pdVec_pd_eq m t.1 t.2.1 (fun z : Fin n → ℝ => seriesFunM c z t.2.2.1 t.2.2.2)]
    refine (hs' (m + 1) (by omega) N c hc (Fin.append t.1 ![t.2.1]) t.2.2.1 t.2.2.2 x).trans ?_
    exact mul_le_mul_of_nonneg_left (by linarith) hCs
  have hcard1 : (Fintype.card ((Fin m → Fin n) × (Fin n × Fin n)) : ℝ)
      ≤ (n : ℝ) ^ s * (n : ℝ) ^ 2 := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    push_cast
    calc (n : ℝ) ^ m * ((n : ℝ) * (n : ℝ)) ≤ (n : ℝ) ^ s * ((n : ℝ) * (n : ℝ)) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hn1 hms) (by positivity)
      _ = (n : ℝ) ^ s * (n : ℝ) ^ 2 := by ring
  have hcard2 : (Fintype.card ((Fin m → Fin n) × (Fin n × (Fin n × Fin n))) : ℝ)
      ≤ (n : ℝ) ^ s * (n : ℝ) ^ 3 := by
    simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    push_cast
    calc (n : ℝ) ^ m * ((n : ℝ) * ((n : ℝ) * (n : ℝ)))
        ≤ (n : ℝ) ^ s * ((n : ℝ) * ((n : ℝ) * (n : ℝ))) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hn1 hms) (by positivity)
      _ = (n : ℝ) ^ s * (n : ℝ) ^ 3 := by ring
  have hA : (∑ t : (Fin m → Fin n) × (Fin n × Fin n),
      ‖pdVec m t.1 (fun z : Fin n → ℝ => seriesFunM c z t.2.1 t.2.2) x‖)
      ≤ ((n : ℝ) ^ s * (n : ℝ) ^ 2) * (Cs * (1 + Bs)) := by
    have h1 : (∑ t : (Fin m → Fin n) × (Fin n × Fin n),
        ‖pdVec m t.1 (fun z : Fin n → ℝ => seriesFunM c z t.2.1 t.2.2) x‖)
        ≤ ∑ _t : (Fin m → Fin n) × (Fin n × Fin n), (Cs * (1 + Bs)) :=
      Finset.sum_le_sum (fun t _ => hterm1 t)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_right hcard1 (by positivity)
  have hB : (∑ t : (Fin m → Fin n) × (Fin n × (Fin n × Fin n)),
      ‖pdVec m t.1 (fun z : Fin n → ℝ => pd t.2.1
        (fun w : Fin n → ℝ => seriesFunM c w t.2.2.1 t.2.2.2) z) x‖)
      ≤ ((n : ℝ) ^ s * (n : ℝ) ^ 3) * (Cs * (1 + Bs)) := by
    have h1 : (∑ t : (Fin m → Fin n) × (Fin n × (Fin n × Fin n)),
        ‖pdVec m t.1 (fun z : Fin n → ℝ => pd t.2.1
          (fun w : Fin n → ℝ => seriesFunM c w t.2.2.1 t.2.2.2) z) x‖)
        ≤ ∑ _t : (Fin m → Fin n) × (Fin n × (Fin n × Fin n)), (Cs * (1 + Bs)) :=
      Finset.sum_le_sum (fun t _ => hterm2 t)
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h1
    refine h1.trans ?_
    exact mul_le_mul_of_nonneg_right hcard2 (by positivity)
  calc ‖iteratedFDeriv ℝ m (jetP c) x‖ ≤ Cj * ((∑ t : (Fin m → Fin n) × (Fin n × Fin n),
        ‖pdVec m t.1 (fun z : Fin n → ℝ => seriesFunM c z t.2.1 t.2.2) x‖)
      + ∑ t : (Fin m → Fin n) × (Fin n × (Fin n × Fin n)),
        ‖pdVec m t.1 (fun z : Fin n → ℝ => pd t.2.1
          (fun w : Fin n → ℝ => seriesFunM c w t.2.2.1 t.2.2.2) z) x‖) := hj m hm2 c hsm x
    _ ≤ Cj * (((n : ℝ) ^ s * (n : ℝ) ^ 2) * (Cs * (1 + Bs))
        + ((n : ℝ) ^ s * (n : ℝ) ^ 3) * (Cs * (1 + Bs))) :=
        mul_le_mul_of_nonneg_left (add_le_add hA hB) hCj
    _ = Cj * (((n : ℝ) ^ s * (n : ℝ) ^ 2) + ((n : ℝ) ^ s * (n : ℝ) ^ 3)) * Cs
        * (1 + Bs) := by ring

/-! ## Part 3: the two halves of the pairing estimate

The pairing in the statement splits into the *commutator* part, where the Leibniz formula against
the symmetrised inverse metric is estimated by `leibniz_l2_gen`, and the *nonlinearity* part, where
the composite `x ↦ Nfun (x, jetP c x)` is estimated by the Faà di Bruno bound `jet_comp_l2_local`
combined with Cauchy–Schwarz. -/

/-- `√(a + b) ≤ √a + √b`. -/
lemma sqrt_add_le' {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a + b) ≤ Real.sqrt a + Real.sqrt b := by
  rw [Real.sqrt_le_iff]
  refine ⟨add_nonneg (Real.sqrt_nonneg a) (Real.sqrt_nonneg b), ?_⟩
  have h1 : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
  have h2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg b, sq_nonneg (Real.sqrt a - Real.sqrt b)]

/-- Young's inequality for square roots: `K √G √F ≤ (θ/2) G + (K²/(2θ)) F`. -/
lemma sqrt_mul_sqrt_le_young {F G K θ : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G) (hK : 0 ≤ K)
    (hθ : 0 < θ) :
    K * (Real.sqrt G * Real.sqrt F) ≤ θ / 2 * G + K ^ 2 / (2 * θ) * F := by
  have h2θ : (0 : ℝ) < 2 * θ := by linarith
  have hsq : 0 ≤ (θ * Real.sqrt G - K * Real.sqrt F) ^ 2 := sq_nonneg _
  have hG' : Real.sqrt G ^ 2 = G := Real.sq_sqrt hG
  have hF' : Real.sqrt F ^ 2 = F := Real.sq_sqrt hF
  have key : K * (Real.sqrt G * Real.sqrt F) ≤ (θ ^ 2 * G + K ^ 2 * F) / (2 * θ) := by
    rw [le_div_iff₀ h2θ]
    nlinarith [hsq, hG', hF']
  refine key.trans (le_of_eq ?_)
  field_simp

/-- The square-root estimate for the nonlinearity: `√(1+F+G) √F` controlled by `θ G + C (1+F)`. -/
lemma sqrt_one_add_sqrt_le_young {F G K θ : ℝ} (hF : 0 ≤ F) (hG : 0 ≤ G) (hK : 0 ≤ K)
    (hθ : 0 < θ) :
    K * (Real.sqrt (1 + F + G) * Real.sqrt F)
      ≤ θ / 2 * G + (3 / 2 * K + K ^ 2 / (2 * θ)) * (1 + F) := by
  have h1F : 0 ≤ 1 + F := by linarith
  have h1 : Real.sqrt (1 + F + G) ≤ Real.sqrt (1 + F) + Real.sqrt G := by
    rw [show (1 : ℝ) + F + G = (1 + F) + G by ring]
    exact sqrt_add_le' h1F hG
  have h2 : Real.sqrt (1 + F) * Real.sqrt F ≤ 1 + F := by
    have hsq : 0 ≤ (Real.sqrt (1 + F) - Real.sqrt F) ^ 2 := sq_nonneg _
    have h1' : Real.sqrt (1 + F) ^ 2 = 1 + F := Real.sq_sqrt h1F
    have h2' : Real.sqrt F ^ 2 = F := Real.sq_sqrt hF
    nlinarith [hsq, h1', h2', Real.sqrt_nonneg (1 + F), Real.sqrt_nonneg F]
  have h3 := sqrt_mul_sqrt_le_young hF hG hK hθ
  calc K * (Real.sqrt (1 + F + G) * Real.sqrt F)
      ≤ K * ((Real.sqrt (1 + F) + Real.sqrt G) * Real.sqrt F) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg F)) hK
    _ = K * (Real.sqrt (1 + F) * Real.sqrt F) + K * (Real.sqrt G * Real.sqrt F) := by ring
    _ ≤ K * (1 + F) + (θ / 2 * G + K ^ 2 / (2 * θ) * F) :=
        add_le_add (mul_le_mul_of_nonneg_left h2 hK) h3
    _ ≤ θ / 2 * G + (3 / 2 * K + K ^ 2 / (2 * θ)) * (1 + F) := by
        have hK2 : 0 ≤ K ^ 2 / (2 * θ) := by positivity
        nlinarith [hF, hK, hK2]

/-- A partial derivative of a `C^∞` function is `C^∞`. -/
lemma pd_contDiff_top {n : ℕ} {f : (Fin n → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (pd a f) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => fderiv ℝ f x (Pi.single a 1)) :=
    h1.clm_apply contDiff_const
  exact h2

/-- A partial derivative of a periodic `C^∞` function is periodic. -/
lemma periodic_pd {n : ℕ} {f : (Fin n → ℝ) → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hper : Periodic1 f) (a : Fin n) : Periodic1 (pd a f) := by
  intro i x
  exact Work.Diff.STE.periodicIn_pd_of_differentiable i a (hf.differentiable (by simp)) (hper i) x

/-- The entries of `seriesFunM c` are periodic. -/
lemma seriesFunM_entry_periodic {n : ℕ} (c : (Fin n → ℤ) → MatC n) (i j : Fin n) :
    Periodic1 (fun x : Fin n → ℝ => seriesFunM c x i j) := by
  intro k x
  simpa only [Flat.seriesFunM_apply] using
    (periodic1_seriesFun (fun m : Fin n → ℤ => c m i j) k x : _)


/-- **The commutator half of the pairing estimate.**  The pairing of the Leibniz commutator
`∂^l (symInvC · ∂_a∂_b u) - symInvC · ∂^l ∂_a∂_b u` against `∂^l u`, summed over all orders and
matrix indices, is bounded by `θ/8` times the level-`(s+2)` energy plus a constant times the
level-`(s+1)` full energy. -/
lemma commutator_pair_le {n s : ℕ} (hn : 1 ≤ n) (hs : n + 5 ≤ s)
    (lam : ℝ) (hlam : 0 < lam) (Bs : ℝ) (hBs : 0 ≤ Bs) (θ : ℝ) (hθ : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k : Fin n → ℤ, k ∉ box n N → c k = 0) →
      ENormSqFull s (seriesFunM c) ≤ Bs ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          reMat (seriesFunM c x) i j * v i * v j) →
      (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n,
        |∑ l : Fin (s + 1) → Fin n,
            L2re (fun x => pdVec (s + 1) l (fun y =>
                  symInvC c a b y * pd a (pd b (fun z => seriesFunM c z i j)) y) x
                - symInvC c a b x * pdVec (s + 1) l
                    (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
              (pdVec (s + 1) l (fun x => seriesFunM c x i j))|)
        ≤ θ / 8 * ENormSqFull (s + 2) (seriesFunM c)
          + C * (1 + ENormSqFull (s + 1) (seriesFunM c)) := by
  obtain ⟨CG, hCG, hsym⟩ := inv_jet_bound_symm hn hs lam hlam Bs hBs
  obtain ⟨Cs, hCs, hsup_entry⟩ := jet_sup_le_uniform_level (n := n) (s := s)
  obtain ⟨C2, hC2, hL2⟩ := entry_pdVec_l2_le (n := n) (s + 2)
  have hMs : s ≤ (s - sob n) + (s - sob n - 2) := by
    have h := two_sob_le n
    omega
  obtain ⟨Cl, hCl, hleib⟩ := leibniz_l2_gen (n := n) (s := s)
    (MF := s - sob n) (Mg := s - sob n - 2) hMs
  refine ⟨(n : ℝ) ^ 8 * ((Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ)
      + Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs))) + 1)
      + (n : ℝ) ^ 8 * (Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ)
      + θ / 8 * Bs ^ 2 + 1, by positivity, ?_⟩
  intro N c hc hen hell
  obtain ⟨hsym_sm, hsym_per, hsym_sup, hsym_l2, _⟩ := hsym N c hc hen hell
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hEsub : Real.sqrt (ENormSqFull s (seriesFunM c)) ≤ Bs := by
    rw [← Real.sqrt_sq hBs]
    exact Real.sqrt_le_sqrt hen
  have hper : ∀ (a b i j : Fin n),
      |∑ l : Fin (s + 1) → Fin n,
          L2re (fun x => pdVec (s + 1) l (fun y =>
                symInvC c a b y * pd a (pd b (fun z => seriesFunM c z i j)) y) x
              - symInvC c a b x * pdVec (s + 1) l
                  (fun z => pd a (pd b (fun w => seriesFunM c w i j)) z) x)
            (pdVec (s + 1) l (fun x => seriesFunM c x i j))|
        ≤ Cl * (CG * (1 + Bs)) * Real.sqrt C2
            * (Real.sqrt (ENormSqFull (s + 2) (seriesFunM c))
              * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c)))
          + Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs)))
            * (1 + ENormSqFull (s + 1) (seriesFunM c)) := by
    intro a b i j
    have hu_sm : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => seriesFunM c x i j) :=
      seriesFunM_entry_contDiff N c hc i j
    have hpd_sm : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Fin n → ℝ => pd b (fun w => seriesFunM c w i j) z) := pd_contDiff_top hu_sm b
    have hg_sm : ContDiff ℝ (⊤ : ℕ∞)
        (fun z : Fin n → ℝ => pd a (pd b (fun w => seriesFunM c w i j)) z) :=
      pd_contDiff_top hpd_sm a
    have hu_per : Periodic1 (fun x : Fin n → ℝ => seriesFunM c x i j) :=
      seriesFunM_entry_periodic c i j
    have hpd_per : Periodic1 (fun z : Fin n → ℝ => pd b (fun w => seriesFunM c w i j) z) :=
      periodic_pd hu_sm hu_per b
    have hg_per : Periodic1 (fun z : Fin n → ℝ => pd a (pd b (fun w => seriesFunM c w i j)) z) :=
      periodic_pd hpd_sm hpd_per a
    have hHF : 0 ≤ CG * (1 + Bs) := by positivity
    have hHG : 0 ≤ Cs * (1 + Bs) := by positivity
    have hEF : 0 ≤ Real.sqrt (CG * (1 + Bs) ^ 2 * (1 + ENormSqFull (s + 1) (seriesFunM c))) :=
      Real.sqrt_nonneg _
    have hEG : 0 ≤ Real.sqrt (C2 * ENormSqFull (s + 2) (seriesFunM c)) := Real.sqrt_nonneg _
    have hEV : 0 ≤ Real.sqrt (ENormSqFull (s + 1) (seriesFunM c)) := Real.sqrt_nonneg _
    have hFsup : ∀ m ≤ s - sob n, ∀ l : Fin m → Fin n, ∀ x : Fin n → ℝ,
        ‖pdVec m l (symInvC c a b) x‖ ≤ CG * (1 + Bs) := by
      intro m hm l x
      exact (hsym_sup a b m (by omega) l x).trans
        (mul_le_mul_of_nonneg_left (by linarith [hEsub]) hCG)
    have hgsup : ∀ m ≤ s - sob n - 2, ∀ l : Fin m → Fin n, ∀ x : Fin n → ℝ,
        ‖pdVec m l (fun z : Fin n → ℝ => pd a (pd b (fun w => seriesFunM c w i j)) z) x‖
          ≤ Cs * (1 + Bs) := by
      intro m hm l x
      rw [pdVec_pd_pd_eq m l a b (fun w => seriesFunM c w i j)]
      exact (hsup_entry (m + 2) (by omega) N c hc (Fin.append l ![a, b]) i j x).trans
        (mul_le_mul_of_nonneg_left (by linarith [hEsub]) hCs)
    have hFl2 : ∀ m ≤ s + 1, ∀ l : Fin m → Fin n,
        (∫ x in unitCube (ι := Fin n), ‖pdVec m l (symInvC c a b) x‖ ^ 2)
          ≤ (Real.sqrt (CG * (1 + Bs) ^ 2 * (1 + ENormSqFull (s + 1) (seriesFunM c)))) ^ 2 := by
      intro m hm l
      refine (hsym_l2 a b m hm l).trans (le_of_eq ?_)
      have hnn : 0 ≤ CG * (1 + Bs) ^ 2 * (1 + ENormSqFull (s + 1) (seriesFunM c)) :=
        mul_nonneg (mul_nonneg hCG (sq_nonneg _))
          (by linarith [ENormSqFull_nonneg (s + 1) (seriesFunM c)])
      rw [Real.sq_sqrt hnn]
    have hgl2 : ∀ m ≤ s, ∀ l : Fin m → Fin n,
        (∫ x in unitCube (ι := Fin n),
          ‖pdVec m l (fun z : Fin n → ℝ => pd a (pd b (fun w => seriesFunM c w i j)) z) x‖ ^ 2)
          ≤ (Real.sqrt (C2 * ENormSqFull (s + 2) (seriesFunM c))) ^ 2 := by
      intro m hm l
      rw [pdVec_pd_pd_eq m l a b (fun w => seriesFunM c w i j)]
      refine (hL2 N c hc (m + 2) (by omega) (Fin.append l ![a, b]) i j).trans (le_of_eq ?_)
      rw [Real.sq_sqrt (mul_nonneg hC2 (ENormSqFull_nonneg _ _))]
    have hvl2 : ∀ l : Fin (s + 1) → Fin n,
        (∫ x in unitCube (ι := Fin n),
          ‖pdVec (s + 1) l (fun x : Fin n → ℝ => seriesFunM c x i j) x‖ ^ 2)
          ≤ (Real.sqrt (ENormSqFull (s + 1) (seriesFunM c))) ^ 2 := by
      intro l
      refine (int_pdVec_le_ENormSq (fun x => seriesFunM c x i j) l).trans ?_
      refine (ENormSq_le_ENormSqM (j := s + 1) (seriesFunM c) i j).trans ?_
      rw [Real.sq_sqrt (ENormSqFull_nonneg _ _)]
      exact ENormSqM_le_ENormSqFull (s + 1) (seriesFunM c)
    have hbound := hleib (symInvC c a b)
      (fun z : Fin n → ℝ => pd a (pd b (fun w => seriesFunM c w i j)) z)
      (fun x : Fin n → ℝ => seriesFunM c x i j)
      (hsym_sm a b) hg_sm hu_sm (hsym_per a b) hg_per hu_per
      (CG * (1 + Bs)) (Cs * (1 + Bs))
      (Real.sqrt (CG * (1 + Bs) ^ 2 * (1 + ENormSqFull (s + 1) (seriesFunM c))))
      (Real.sqrt (C2 * ENormSqFull (s + 2) (seriesFunM c)))
      (Real.sqrt (ENormSqFull (s + 1) (seriesFunM c)))
      hHF hHG hEF hEG hEV hFsup hgsup hFl2 hgl2 hvl2
    refine hbound.trans ?_
    have hsplit : Cl * ((CG * (1 + Bs))
          * (Real.sqrt (C2 * ENormSqFull (s + 2) (seriesFunM c)))
            * (Real.sqrt (ENormSqFull (s + 1) (seriesFunM c)))
        + (Real.sqrt (CG * (1 + Bs) ^ 2 * (1 + ENormSqFull (s + 1) (seriesFunM c))))
            * (Cs * (1 + Bs)) * (Real.sqrt (ENormSqFull (s + 1) (seriesFunM c)))) = _ := rfl
    -- the two terms
    have hterm1 : Cl * ((CG * (1 + Bs))
          * (Real.sqrt (C2 * ENormSqFull (s + 2) (seriesFunM c)))
            * (Real.sqrt (ENormSqFull (s + 1) (seriesFunM c))))
        ≤ Cl * (CG * (1 + Bs)) * Real.sqrt C2
            * (Real.sqrt (ENormSqFull (s + 2) (seriesFunM c))
              * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c))) := by
      rw [Real.sqrt_mul hC2]
      have h1 : (0:ℝ) ≤ CG * (1 + Bs) := by positivity
      have h2 : (0:ℝ) ≤ Cl := hCl
      nlinarith [h1, h2, Real.sqrt_nonneg C2, Real.sqrt_nonneg (ENormSqFull (s + 2) (seriesFunM c)),
        Real.sqrt_nonneg (ENormSqFull (s + 1) (seriesFunM c))]
    have hterm2 : Cl * ((Real.sqrt (CG * (1 + Bs) ^ 2 * (1 + ENormSqFull (s + 1) (seriesFunM c))))
            * (Cs * (1 + Bs)) * (Real.sqrt (ENormSqFull (s + 1) (seriesFunM c))))
        ≤ Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs)))
            * (1 + ENormSqFull (s + 1) (seriesFunM c)) := by
      have hsq1 : Real.sqrt (CG * (1 + Bs) ^ 2 * (1 + ENormSqFull (s + 1) (seriesFunM c)))
          = Real.sqrt CG * (1 + Bs) * Real.sqrt (1 + ENormSqFull (s + 1) (seriesFunM c)) := by
        rw [show CG * (1 + Bs) ^ 2 * (1 + ENormSqFull (s + 1) (seriesFunM c))
            = CG * ((1 + Bs) ^ 2 * (1 + ENormSqFull (s + 1) (seriesFunM c))) by ring]
        rw [Real.sqrt_mul hCG]
        rw [Real.sqrt_mul (by positivity : (0:ℝ) ≤ (1 + Bs) ^ 2)]
        rw [Real.sqrt_sq (by linarith : (0:ℝ) ≤ 1 + Bs)]
        ring
      have hu1F : Real.sqrt (1 + ENormSqFull (s + 1) (seriesFunM c))
            * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c))
          ≤ 1 + ENormSqFull (s + 1) (seriesFunM c) := by
        have hF : 0 ≤ ENormSqFull (s + 1) (seriesFunM c) := ENormSqFull_nonneg _ _
        have hsq : 0 ≤ (Real.sqrt (1 + ENormSqFull (s + 1) (seriesFunM c))
            - Real.sqrt (ENormSqFull (s + 1) (seriesFunM c))) ^ 2 := sq_nonneg _
        have h1 : Real.sqrt (1 + ENormSqFull (s + 1) (seriesFunM c)) ^ 2
            = 1 + ENormSqFull (s + 1) (seriesFunM c) := Real.sq_sqrt (by linarith)
        have h2 : Real.sqrt (ENormSqFull (s + 1) (seriesFunM c)) ^ 2
            = ENormSqFull (s + 1) (seriesFunM c) := Real.sq_sqrt hF
        nlinarith [hsq, h1, h2, Real.sqrt_nonneg (1 + ENormSqFull (s + 1) (seriesFunM c)),
          Real.sqrt_nonneg (ENormSqFull (s + 1) (seriesFunM c))]
      rw [hsq1]
      have hP : 0 ≤ Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs))) := by positivity
      have hrewrite : Cl * ((Real.sqrt CG * (1 + Bs)
            * Real.sqrt (1 + ENormSqFull (s + 1) (seriesFunM c))) * (Cs * (1 + Bs))
            * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c)))
          = Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs)))
            * (Real.sqrt (1 + ENormSqFull (s + 1) (seriesFunM c))
              * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c))) := by ring
      rw [hrewrite]
      exact mul_le_mul_of_nonneg_left hu1F hP
    nlinarith [hterm1, hterm2]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) =>
      Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) =>
        Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => hper a b i j))))
  refine hsum.trans ?_
  have hcount : (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n,
      (Cl * (CG * (1 + Bs)) * Real.sqrt C2
          * (Real.sqrt (ENormSqFull (s + 2) (seriesFunM c))
            * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c)))
        + Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs)))
          * (1 + ENormSqFull (s + 1) (seriesFunM c))))
      = (n : ℝ) ^ 4 * (Cl * (CG * (1 + Bs)) * Real.sqrt C2
          * (Real.sqrt (ENormSqFull (s + 2) (seriesFunM c))
            * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c)))
        + Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs)))
          * (1 + ENormSqFull (s + 1) (seriesFunM c))) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hcount]
  have hGnn : 0 ≤ ENormSqFull (s + 2) (seriesFunM c) := ENormSqFull_nonneg _ _
  have hFnn : 0 ≤ ENormSqFull (s + 1) (seriesFunM c) := ENormSqFull_nonneg _ _
  have hK : 0 ≤ (n : ℝ) ^ 4 * (Cl * (CG * (1 + Bs)) * Real.sqrt C2) := by positivity
  have hθ8 : (0 : ℝ) < θ / 8 := by linarith
  have hyoung := sqrt_mul_sqrt_le_young hFnn hGnn hK hθ8
  have hmain1 : (n : ℝ) ^ 4 * (Cl * (CG * (1 + Bs)) * Real.sqrt C2
        * (Real.sqrt (ENormSqFull (s + 2) (seriesFunM c))
          * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c))))
      ≤ θ / 16 * ENormSqFull (s + 2) (seriesFunM c)
        + (n : ℝ) ^ 8 * (Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ)
          * ENormSqFull (s + 1) (seriesFunM c) := by
    have h1 : (n : ℝ) ^ 4 * (Cl * (CG * (1 + Bs)) * Real.sqrt C2
        * (Real.sqrt (ENormSqFull (s + 2) (seriesFunM c))
          * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c))))
        = ((n : ℝ) ^ 4 * (Cl * (CG * (1 + Bs)) * Real.sqrt C2))
          * (Real.sqrt (ENormSqFull (s + 2) (seriesFunM c))
            * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c))) := by ring
    rw [h1]
    refine hyoung.trans ?_
    have h2 : (θ / 8) / 2 = θ / 16 := by ring
    have h3 : ((n : ℝ) ^ 4 * (Cl * (CG * (1 + Bs)) * Real.sqrt C2)) ^ 2 / (2 * (θ / 8))
        = (n : ℝ) ^ 8 * (Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ) := by
      field_simp
      ring
    rw [h2, h3]
  have hmain2 : (n : ℝ) ^ 4 * (Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs)))
        * (1 + ENormSqFull (s + 1) (seriesFunM c)))
      ≤ (n : ℝ) ^ 8 * ((Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ)
          + Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs))) + 1)
        * (1 + ENormSqFull (s + 1) (seriesFunM c)) := by
    have hA2' : 0 ≤ Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs))) := by positivity
    have h1F : 0 ≤ 1 + ENormSqFull (s + 1) (seriesFunM c) := by linarith [hFnn]
    have hcoef : 0 ≤ (Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ) + 1 := by positivity
    have hp1 : (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 8 := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 4 := one_le_pow₀ hn1
      calc (n : ℝ) ^ 4 = (n : ℝ) ^ 4 * 1 := by ring
        _ ≤ (n : ℝ) ^ 4 * (n : ℝ) ^ 4 := mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (n : ℝ) ^ 8 := by ring
    have hX : 0 ≤ (Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ)
        + Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs))) + 1 := by positivity
    have hlow : (n : ℝ) ^ 4 * (Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs))))
        ≤ (n : ℝ) ^ 8 * ((Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ)
            + Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs))) + 1) := by
      have h1 : Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs)))
          ≤ (Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ)
            + Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs))) + 1 := by
        have h4 : 0 ≤ (4 : ℝ) / θ := by positivity
        have hsq : 0 ≤ (Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 := sq_nonneg _
        linarith [mul_nonneg hsq h4, hA2', hcoef]
      calc (n : ℝ) ^ 4 * (Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs))))
          ≤ (n : ℝ) ^ 4 * ((Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ)
              + Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs))) + 1) :=
            mul_le_mul_of_nonneg_left h1 (by positivity)
        _ ≤ (n : ℝ) ^ 8 * ((Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ)
              + Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs))) + 1) :=
            mul_le_mul_of_nonneg_right hp1 hX
    calc (n : ℝ) ^ 4 * (Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs)))
          * (1 + ENormSqFull (s + 1) (seriesFunM c)))
        = ((n : ℝ) ^ 4 * (Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs)))))
          * (1 + ENormSqFull (s + 1) (seriesFunM c)) := by ring
      _ ≤ ((n : ℝ) ^ 8 * ((Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ)
            + Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs))) + 1))
          * (1 + ENormSqFull (s + 1) (seriesFunM c)) :=
          mul_le_mul_of_nonneg_right hlow h1F
  have hfinal : (n : ℝ) ^ 4 * (Cl * (CG * (1 + Bs)) * Real.sqrt C2
        * (Real.sqrt (ENormSqFull (s + 2) (seriesFunM c))
          * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c)))
        + Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs)))
          * (1 + ENormSqFull (s + 1) (seriesFunM c)))
      ≤ θ / 8 * ENormSqFull (s + 2) (seriesFunM c)
        + ((n : ℝ) ^ 8 * ((Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ)
              + Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs))) + 1)
          + (n : ℝ) ^ 8 * (Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ)
          + θ / 8 * Bs ^ 2 + 1)
          * (1 + ENormSqFull (s + 1) (seriesFunM c)) := by
    have h1F : 0 ≤ 1 + ENormSqFull (s + 1) (seriesFunM c) := by linarith [hFnn]
    have hA1s : 0 ≤ (n : ℝ) ^ 8 * (Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ) := by
      positivity
    have hX1 : (n : ℝ) ^ 8 * (Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ)
          * ENormSqFull (s + 1) (seriesFunM c)
        ≤ (n : ℝ) ^ 8 * (Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ)
          * (1 + ENormSqFull (s + 1) (seriesFunM c)) :=
      mul_le_mul_of_nonneg_left (by linarith) hA1s
    have hc1 : θ / 16 * ENormSqFull (s + 2) (seriesFunM c)
        ≤ θ / 8 * ENormSqFull (s + 2) (seriesFunM c) :=
      mul_le_mul_of_nonneg_right (by linarith) hGnn
    rw [show (n : ℝ) ^ 4 * (Cl * (CG * (1 + Bs)) * Real.sqrt C2
          * (Real.sqrt (ENormSqFull (s + 2) (seriesFunM c))
            * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c)))
          + Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs)))
            * (1 + ENormSqFull (s + 1) (seriesFunM c)))
        = (n : ℝ) ^ 4 * (Cl * (CG * (1 + Bs)) * Real.sqrt C2
            * (Real.sqrt (ENormSqFull (s + 2) (seriesFunM c))
              * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c))))
          + (n : ℝ) ^ 4 * (Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs)))
            * (1 + ENormSqFull (s + 1) (seriesFunM c))) by ring]
    refine (add_le_add hmain1 hmain2).trans ?_
    have hstep : θ / 16 * ENormSqFull (s + 2) (seriesFunM c)
          + (n : ℝ) ^ 8 * (Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ)
            * ENormSqFull (s + 1) (seriesFunM c)
          + (n : ℝ) ^ 8 * ((Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ)
              + Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs))) + 1)
            * (1 + ENormSqFull (s + 1) (seriesFunM c))
        ≤ θ / 8 * ENormSqFull (s + 2) (seriesFunM c)
          + ((n : ℝ) ^ 8 * ((Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ)
                + Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs))) + 1)
            + (n : ℝ) ^ 8 * (Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ))
            * (1 + ENormSqFull (s + 1) (seriesFunM c)) := by
      rw [add_mul]
      linarith [hc1, hX1]
    refine hstep.trans ?_
    have hcoef : (n : ℝ) ^ 8 * ((Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ)
              + Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs))) + 1)
          + (n : ℝ) ^ 8 * (Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ)
        ≤ (n : ℝ) ^ 8 * ((Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ)
              + Cl * (Real.sqrt CG * (1 + Bs) * (Cs * (1 + Bs))) + 1)
          + (n : ℝ) ^ 8 * (Cl * (CG * (1 + Bs)) * Real.sqrt C2) ^ 2 * (4 / θ)
          + θ / 8 * Bs ^ 2 + 1 := by
      have hpos : 0 ≤ θ / 8 * Bs ^ 2 + 1 := by nlinarith [hBs, hθ, sq_nonneg Bs]
      linarith [hpos]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hcoef h1F)
  exact hfinal

/-- **The nonlinearity half of the pairing estimate.**  The pairing of the `(s+1)`-st derivative of
the composite `x ↦ Nfun (x, jetP c x)` against `∂^{s+1} u`, summed over the matrix indices, is
bounded by `θ/8` times the level-`(s+2)` energy plus a constant times the level-`(s+1)` full
energy. -/
lemma nonlinearity_pair_le {n s : ℕ} (hn : 1 ≤ n) (hs : n + 5 ≤ s)
    (Nfun : (Fin n → ℝ) × (MatC n × (Fin n → MatC n)) → MatC n)
    (hNsm : ContDiffOn ℝ (⊤ : ℕ∞) Nfun (Set.univ ×ˢ
        {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0}))
    (lam : ℝ) (hlam : 0 < lam) (Bs : ℝ) (hBs : 0 ≤ Bs) (θ : ℝ) (hθ : 0 < θ)
    (K : ℝ) (hK : 0 ≤ K)
    (hKsup : ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0) →
      ENormSqFull s (seriesFunM c) ≤ Bs ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          reMat (seriesFunM c x) i j * v i * v j) →
      ∀ (j : ℕ), j ≤ s + 1 → ∀ (x : Fin n → ℝ),
        ‖iteratedFDeriv ℝ j Nfun
          (x, seriesFunM c x,
            fun a i j' => pd a (fun y => seriesFunM c y i j') x)‖ ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ box n N → c k' = 0) →
      ENormSqFull s (seriesFunM c) ≤ Bs ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          reMat (seriesFunM c x) i j * v i * v j) →
      (∑ i : Fin n, ∑ j : Fin n,
        |∑ l : Fin (s + 1) → Fin n,
            L2re (pdVec (s + 1) l (fun x => Nfun (x, jetP c x) i j))
              (pdVec (s + 1) l (fun x => seriesFunM c x i j))|)
        ≤ θ / 8 * ENormSqFull (s + 2) (seriesFunM c)
          + C * (1 + ENormSqFull (s + 1) (seriesFunM c)) := by
  obtain ⟨Cjet, hCjet, hjetsup⟩ := jetP_sup_le (n := n) (s := s) hn hs Bs hBs
  obtain ⟨Cl2, hCl2, hjPl2⟩ := jetP_l2_le (n := n) (s := s) hn
  have hM1 : (s + 1) / 2 ≤ s - 1 - sob n := by
    have h1 : 2 * ((s + 1) / 2) ≤ s + 1 := by omega
    have h2 : 2 * sob n ≤ n + 2 := two_sob_le n
    omega
  obtain ⟨Ccp, hCcp, hcomp⟩ := jet_comp_l2_local (n := n) (s := s) (M := s - 1 - sob n) hM1
  have hSopen : IsOpen {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0} := by
    have hcont : Continuous fun w : MatC n × (Fin n → MatC n) => (reMat w.1).det := by
      refine Continuous.matrix_det ?_
      refine continuous_pi (fun i => continuous_pi (fun j => ?_))
      have h1 : Continuous fun w : MatC n × (Fin n → MatC n) => reMat w.1 := by
        unfold reMat
        fun_prop
      exact (continuous_apply j).comp ((continuous_apply i).comp h1)
    have h1 : IsOpen ((fun w : MatC n × (Fin n → MatC n) => (reMat w.1).det)
        ⁻¹' ({0}ᶜ : Set ℝ)) :=
      (isOpen_compl_singleton (x := (0 : ℝ))).preimage hcont
    have h2 : ((fun w : MatC n × (Fin n → MatC n) => (reMat w.1).det) ⁻¹' ({0}ᶜ : Set ℝ))
        = {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0} := by
      ext w
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_singleton_iff, Set.mem_setOf_eq]
    rwa [h2] at h1
  let Ajet : ℝ := Cjet * (1 + Bs)
  have hAjet : 0 ≤ Ajet := by
    refine mul_nonneg hCjet ?_
    linarith
  refine ⟨3 / 2 * ((n : ℝ) ^ 2
      * Real.sqrt ((n : ℝ) ^ (s + 1)
        * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Cl2))))
      + ((n : ℝ) ^ 2
      * Real.sqrt ((n : ℝ) ^ (s + 1)
        * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Cl2)))) ^ 2 * (2 / θ)
      + 1, by positivity, ?_⟩
  intro N c hc hen hell
  have hPsm : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => jetP c x) := jetP_contDiff N c hc
  have hF1nn : 0 ≤ ENormSqFull (s + 1) (seriesFunM c) := ENormSqFull_nonneg _ _
  have hG2nn : 0 ≤ ENormSqFull (s + 2) (seriesFunM c) := ENormSqFull_nonneg _ _
  have hE0 : ENormSqM 0 (seriesFunM c) ≤ Bs ^ 2 := by
    have h := hen
    simp only [ENormSqFull] at h
    have h2 : 0 ≤ ENormSqM s (seriesFunM c) := ENormSqM_nonneg _ _
    linarith
  -- the pointwise Faà di Bruno input
  have hper : ∀ i j : Fin n,
      |∑ l : Fin (s + 1) → Fin n,
          L2re (pdVec (s + 1) l (fun x => Nfun (x, jetP c x) i j))
            (pdVec (s + 1) l (fun x => seriesFunM c x i j))|
        ≤ Real.sqrt ((n : ℝ) ^ (s + 1)
            * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Cl2)))
          * (Real.sqrt (1 + ENormSqFull (s + 1) (seriesFunM c)
              + ENormSqFull (s + 2) (seriesFunM c))
            * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c))) := by
    intro i j
    set Lm : MatC n →L[ℝ] ℂ :=
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => (Fin n → ℂ)) i) with hLmDef
    have hLm : Lm = (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) j).comp
        (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => (Fin n → ℂ)) i) := rfl
    set Etop : ℝ := Cl2 * (ENormSqFull (s + 1) (seriesFunM c)
      + ENormSqFull (s + 2) (seriesFunM c)) with hEtop
    have hEtopnn : 0 ≤ Etop := by
      rw [hEtop]
      exact mul_nonneg hCl2 (by linarith)
    have hEtop1 : 1 + Etop ≤ (1 + Cl2) * (1 + ENormSqFull (s + 1) (seriesFunM c)
        + ENormSqFull (s + 2) (seriesFunM c)) := by
      rw [hEtop]
      nlinarith [hCl2, hF1nn, hG2nn]
    have hΨsm : ∀ x : Fin n → ℝ, ContDiffAt ℝ (⊤ : ℕ∞)
        (fun p : (Fin n → ℝ) × (MatC n × (Fin n → MatC n)) => Nfun p i j) (x, jetP c x) := by
      intro x
      have hmem : (x, jetP c x) ∈ Set.univ ×ˢ
          {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0} :=
        ⟨Set.mem_univ x, det_ne_zero_of_quadForm_le _ hlam (hell x)⟩
      have hnh : (Set.univ ×ˢ
          {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0}) ∈ 𝓝 (x, jetP c x) := by
        rw [nhds_prod_eq]
        exact Filter.prod_mem_prod Filter.univ_mem (hSopen.mem_nhds hmem.2)
      have hN : ContDiffAt ℝ (⊤ : ℕ∞) Nfun (x, jetP c x) := hNsm.contDiffAt hnh
      have hL : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun _ : (Fin n → ℝ) × (MatC n × (Fin n → MatC n)) => Lm) (x, jetP c x) :=
        contDiffAt_const
      simpa only [hLmDef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
        using hL.clm_apply hN
    have hΨ : ∀ (j' : ℕ), j' ≤ s + 1 → ∀ x : Fin n → ℝ,
        ‖iteratedFDeriv ℝ j'
          (fun p : (Fin n → ℝ) × (MatC n × (Fin n → MatC n)) => Nfun p i j) (x, jetP c x)‖
          ≤ K := by
      intro j' hj' x
      have hmem : (x, jetP c x) ∈ Set.univ ×ˢ
          {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0} :=
        ⟨Set.mem_univ x, det_ne_zero_of_quadForm_le _ hlam (hell x)⟩
      have hnh : (Set.univ ×ˢ
          {w : MatC n × (Fin n → MatC n) | (reMat w.1).det ≠ 0}) ∈ 𝓝 (x, jetP c x) := by
        rw [nhds_prod_eq]
        exact Filter.prod_mem_prod Filter.univ_mem (hSopen.mem_nhds hmem.2)
      have hN : ContDiffAt ℝ (⊤ : ℕ∞) Nfun (x, jetP c x) := hNsm.contDiffAt hnh
      have hLnorm : ‖Lm‖ ≤ 1 := by
        rw [ContinuousLinearMap.opNorm_le_iff (by norm_num : (0 : ℝ) ≤ 1)]
        intro v
        rw [one_mul]
        simp only [hLmDef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
        exact (norm_le_pi_norm (v i) j).trans (norm_le_pi_norm v i)
      have hcomp' := ContinuousLinearMap.iteratedFDeriv_comp_left (𝕜 := ℝ)
        (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) Lm
        (f := Nfun) (x := (x, jetP c x)) hN (i := j')
        (WithTop.coe_le_coe.mpr le_top :
          ((j' : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
      have h1 : ‖iteratedFDeriv ℝ j'
          (fun p : (Fin n → ℝ) × (MatC n × (Fin n → MatC n)) => Lm (Nfun p))
          (x, jetP c x)‖ ≤ K := by
        rw [show iteratedFDeriv ℝ j'
            (fun p : (Fin n → ℝ) × (MatC n × (Fin n → MatC n)) => Lm (Nfun p)) (x, jetP c x)
            = iteratedFDeriv ℝ j' (Lm ∘ Nfun) (x, jetP c x) from rfl, hcomp']
        calc ‖Lm.compContinuousMultilinearMap (iteratedFDeriv ℝ j' Nfun (x, jetP c x))‖
            ≤ ‖Lm‖ * ‖iteratedFDeriv ℝ j' Nfun (x, jetP c x)‖ :=
              ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _
          _ ≤ 1 * K := mul_le_mul hLnorm (hKsup N c hc hen hell j' hj' x) (norm_nonneg _) zero_le_one
          _ = K := one_mul K
      simpa only [hLmDef, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using h1
    have hPsup : ∀ m ≤ s - 1 - sob n, ∀ x : Fin n → ℝ,
        ‖iteratedFDeriv ℝ m (jetP c) x‖ ≤ Ajet := by
      intro m hm x
      exact hjetsup N c hc hen (s - 1 - sob n) (by omega) m hm x
    have hPl2 : ∀ m ≤ s + 1,
        (∫ y in unitCube (ι := Fin n), ‖iteratedFDeriv ℝ m (fun x => jetP c x) y‖ ^ 2) ≤ Etop := by
      intro m hm
      have h1 := hjPl2 N c hc m hm (0 : Fin n → ℝ)
      rw [hEtop]
      exact h1
    have hvu : ∀ l : Fin (s + 1) → Fin n,
        Integrable (fun x : Fin n → ℝ =>
          ‖pdVec (s + 1) l (fun x => Nfun (x, jetP c x) i j) x‖ ^ 2)
          (volume.restrict (unitCube (ι := Fin n))) := by
      intro l
      have hsm : ContDiff ℝ (⊤ : ℕ∞) (fun x : Fin n → ℝ => Nfun (x, jetP c x) i j) :=
        contDiff_comp_pair_of_contDiffAt _ _ hΨsm hPsm
      exact el_integrableOn_unitCube_of_continuous_real
        ((continuous_pdVec (s + 1) l _ (hsm.of_le (by simp))).norm.pow 2)
    have huu : ∀ l : Fin (s + 1) → Fin n,
        Integrable (fun x : Fin n → ℝ =>
          ‖pdVec (s + 1) l (fun x => seriesFunM c x i j) x‖ ^ 2)
          (volume.restrict (unitCube (ι := Fin n))) := by
      intro l
      exact el_integrableOn_unitCube_of_continuous_real
        ((continuous_pdVec (s + 1) l _
          ((seriesFunM_entry_contDiff N c hc i j).of_le (by simp))).norm.pow 2)
    have hpair := ENormSq_pairing_le (s + 1) (fun x => Nfun (x, jetP c x) i j)
      (fun x => seriesFunM c x i j) hvu huu
    have hENv : ENormSq (s + 1) (fun x => Nfun (x, jetP c x) i j)
        ≤ (n : ℝ) ^ (s + 1)
          * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Etop)) := by
      rw [ENormSq]
      calc ∑ l : Fin (s + 1) → Fin n,
            (∫ x in unitCube (ι := Fin n),
              ‖pdVec (s + 1) l (fun x => Nfun (x, jetP c x) i j) x‖ ^ 2)
          ≤ ∑ _l : Fin (s + 1) → Fin n,
              (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Etop)) :=
            Finset.sum_le_sum (fun l _ =>
              hcomp (fun p : (Fin n → ℝ) × (MatC n × (Fin n → MatC n)) => Nfun p i j)
                (fun x : Fin n → ℝ => jetP c x) K Ajet Etop hAjet hK hΨsm hPsm hΨ hPsup hPl2 l)
        _ = (n : ℝ) ^ (s + 1) * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Etop)) := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_fun,
              Fintype.card_fin, Fintype.card_fin]
            push_cast
            ring
      -- note: the `calc` block above is the body
    have hENu : ENormSq (s + 1) (fun x => seriesFunM c x i j)
        ≤ ENormSqFull (s + 1) (seriesFunM c) := by
      refine (ENormSq_le_ENormSqM (j := s + 1) (seriesFunM c) i j).trans ?_
      exact ENormSqM_le_ENormSqFull (s + 1) (seriesFunM c)
    have hsq : |∑ l : Fin (s + 1) → Fin n,
          L2re (pdVec (s + 1) l (fun x => Nfun (x, jetP c x) i j))
            (pdVec (s + 1) l (fun x => seriesFunM c x i j))|
        ≤ Real.sqrt (ENormSq (s + 1) (fun x => Nfun (x, jetP c x) i j))
          * Real.sqrt (ENormSq (s + 1) (fun x => seriesFunM c x i j)) := by
      have h1 := Real.sqrt_le_sqrt hpair
      rw [sq_abs] at h1
      rw [Real.sqrt_sq_eq_abs] at h1
      rw [Real.sqrt_mul (ENormSq_nonneg (s + 1) (fun x => Nfun (x, jetP c x) i j))] at h1
      exact h1
    refine hsq.trans ?_
    have h1 : Real.sqrt (ENormSq (s + 1) (fun x => Nfun (x, jetP c x) i j))
        ≤ Real.sqrt ((n : ℝ) ^ (s + 1)
            * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Etop))) :=
      Real.sqrt_le_sqrt hENv
    have h2 : Real.sqrt (ENormSq (s + 1) (fun x => seriesFunM c x i j))
        ≤ Real.sqrt (ENormSqFull (s + 1) (seriesFunM c)) := Real.sqrt_le_sqrt hENu
    have h3 : Real.sqrt ((n : ℝ) ^ (s + 1)
          * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Etop)))
        ≤ Real.sqrt ((n : ℝ) ^ (s + 1)
            * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Cl2)))
          * Real.sqrt (1 + ENormSqFull (s + 1) (seriesFunM c)
              + ENormSqFull (s + 2) (seriesFunM c)) := by
      have hpos1 : 0 ≤ (n : ℝ) ^ (s + 1)
          * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Cl2)) := by positivity
      have hdiv : (1 + Etop) / (1 + Cl2)
          ≤ 1 + ENormSqFull (s + 1) (seriesFunM c) + ENormSqFull (s + 2) (seriesFunM c) := by
        rw [div_le_iff₀ (by linarith : (0 : ℝ) < 1 + Cl2)]
        nlinarith [hEtop1, hCl2]
      have harg : (n : ℝ) ^ (s + 1)
            * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Etop))
          = ((n : ℝ) ^ (s + 1) * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Cl2)))
            * ((1 + Etop) / (1 + Cl2)) := by
        field_simp
      rw [harg, Real.sqrt_mul hpos1]
      exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdiv) (Real.sqrt_nonneg _)
    calc Real.sqrt (ENormSq (s + 1) (fun x => Nfun (x, jetP c x) i j))
          * Real.sqrt (ENormSq (s + 1) (fun x => seriesFunM c x i j))
        ≤ Real.sqrt ((n : ℝ) ^ (s + 1)
            * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Etop)))
          * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c)) :=
          mul_le_mul h1 h2 (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt ((n : ℝ) ^ (s + 1)
            * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Cl2)))
          * (Real.sqrt (1 + ENormSqFull (s + 1) (seriesFunM c)
              + ENormSqFull (s + 2) (seriesFunM c))
            * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c))) := by
          calc Real.sqrt ((n : ℝ) ^ (s + 1)
                * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Etop)))
                * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c))
              ≤ (Real.sqrt ((n : ℝ) ^ (s + 1)
                  * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Cl2)))
                  * Real.sqrt (1 + ENormSqFull (s + 1) (seriesFunM c)
                    + ENormSqFull (s + 2) (seriesFunM c)))
                * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c)) :=
                mul_le_mul h3 le_rfl (Real.sqrt_nonneg _)
                  (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
            _ = Real.sqrt ((n : ℝ) ^ (s + 1)
                  * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Cl2)))
                * (Real.sqrt (1 + ENormSqFull (s + 1) (seriesFunM c)
                    + ENormSqFull (s + 2) (seriesFunM c))
                  * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c))) := by
                rw [mul_assoc]
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hper i j))
  refine hsum.trans ?_
  have hcount : (∑ _i : Fin n, ∑ _j : Fin n,
      (Real.sqrt ((n : ℝ) ^ (s + 1)
          * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Cl2)))
        * (Real.sqrt (1 + ENormSqFull (s + 1) (seriesFunM c)
            + ENormSqFull (s + 2) (seriesFunM c))
          * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c)))))
      = (n : ℝ) ^ 2 * (Real.sqrt ((n : ℝ) ^ (s + 1)
          * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Cl2)))
        * (Real.sqrt (1 + ENormSqFull (s + 1) (seriesFunM c)
            + ENormSqFull (s + 2) (seriesFunM c))
          * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c)))) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hcount]
  have hK2 : 0 ≤ (n : ℝ) ^ 2 * Real.sqrt ((n : ℝ) ^ (s + 1)
      * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Cl2))) := by positivity
  have hθ4 : (0 : ℝ) < θ / 4 := by linarith
  have hy := sqrt_one_add_sqrt_le_young hF1nn hG2nn hK2 hθ4
  rw [show (n : ℝ) ^ 2
        * (Real.sqrt ((n : ℝ) ^ (s + 1)
              * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Cl2)))
          * (Real.sqrt (1 + ENormSqFull (s + 1) (seriesFunM c)
              + ENormSqFull (s + 2) (seriesFunM c))
            * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c))))
      = ((n : ℝ) ^ 2 * Real.sqrt ((n : ℝ) ^ (s + 1)
            * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Cl2))))
        * (Real.sqrt (1 + ENormSqFull (s + 1) (seriesFunM c)
            + ENormSqFull (s + 2) (seriesFunM c))
          * Real.sqrt (ENormSqFull (s + 1) (seriesFunM c))) by ring]
  refine hy.trans ?_
  have hc : (θ / 4) / 2 * ENormSqFull (s + 2) (seriesFunM c)
      = θ / 8 * ENormSqFull (s + 2) (seriesFunM c) := by ring
  have hc2 : ((n : ℝ) ^ 2 * Real.sqrt ((n : ℝ) ^ (s + 1)
        * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Cl2)))) ^ 2 / (2 * (θ / 4))
      = ((n : ℝ) ^ 2 * Real.sqrt ((n : ℝ) ^ (s + 1)
        * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Cl2)))) ^ 2 * (2 / θ) := by
    field_simp
    ring
  rw [hc, hc2]
  refine add_le_add le_rfl (mul_le_mul_of_nonneg_right ?_ (by linarith))
  have hfin : 3 / 2 * ((n : ℝ) ^ 2 * Real.sqrt ((n : ℝ) ^ (s + 1)
        * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Cl2))))
      + ((n : ℝ) ^ 2 * Real.sqrt ((n : ℝ) ^ (s + 1)
        * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Cl2)))) ^ 2 * (2 / θ)
      ≤ 3 / 2 * ((n : ℝ) ^ 2 * Real.sqrt ((n : ℝ) ^ (s + 1)
        * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Cl2))))
      + ((n : ℝ) ^ 2 * Real.sqrt ((n : ℝ) ^ (s + 1)
        * (Ccp * K ^ 2 * (1 + Ajet) ^ (2 * (s + 2)) * (1 + Cl2)))) ^ 2 * (2 / θ) + 1 := by
    linarith
  exact hfin


theorem pairing_rest_le {n s : ℕ} (hn : 1 ≤ n) (hs : n + 5 ≤ s)
    (Nfun : (Fin n → ℝ) × (Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n))
      → Work.Diff.STE.Flat.MatC n)
    (hNsm : ContDiffOn ℝ (⊤ : ℕ∞) Nfun (Set.univ ×ˢ
        {w : Work.Diff.STE.Flat.MatC n × (Fin n → Work.Diff.STE.Flat.MatC n)
          | (Work.Diff.STE.Flat.reMat w.1).det ≠ 0}))
    (lam : ℝ) (hlam : 0 < lam) (Bs : ℝ) (hBs : 0 ≤ Bs) (θ : ℝ) (hθ : 0 < θ)
    (K : ℝ) (hK : 0 ≤ K)
    (hKsup : ∀ (N : ℕ),
      ∀ (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
      Work.Diff.STE.Flat.ENormSqFull s (Work.Diff.STE.Flat.seriesFunM c) ≤ Bs ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
      ∀ (j : ℕ), j ≤ s + 1 → ∀ (x : Fin n → ℝ),
        ‖iteratedFDeriv ℝ j Nfun
          (x, Work.Diff.STE.Flat.seriesFunM c x,
            fun a i j' => Work.Diff.STE.pd a
              (fun y => Work.Diff.STE.Flat.seriesFunM c y i j') x)‖ ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (c : (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
      (∀ k' : Fin n → ℤ, k' ∉ Work.Diff.STE.Flat.box n N → c k' = 0) →
      Work.Diff.STE.Flat.ENormSqFull s (Work.Diff.STE.Flat.seriesFunM c) ≤ Bs ^ 2 →
      (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
          Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM c x) i j * v i * v j) →
      (∑ i : Fin n, ∑ j : Fin n,
        ((∑ a, ∑ b, |∑ l : Fin (s + 1) → Fin n,
            Work.Diff.STE.L2re (fun x => Work.Diff.STE.pdVec (s + 1) l (fun y =>
                  Work.Diff.STE.flat.symInvC c a b y
                  * Work.Diff.STE.pd a (Work.Diff.STE.pd b
                      (fun z => Work.Diff.STE.Flat.seriesFunM c z i j)) y) x
                - Work.Diff.STE.flat.symInvC c a b x * Work.Diff.STE.pdVec (s + 1) l
                    (fun z => Work.Diff.STE.pd a (Work.Diff.STE.pd b
                        (fun w => Work.Diff.STE.Flat.seriesFunM c w i j)) z) x)
              (Work.Diff.STE.pdVec (s + 1) l (fun x => Work.Diff.STE.Flat.seriesFunM c x i j))|)
          + |∑ l : Fin (s + 1) → Fin n,
              Work.Diff.STE.L2re (Work.Diff.STE.pdVec (s + 1) l
                  (fun x => Nfun (x, Work.Diff.STE.flat.jetP c x) i j))
                (Work.Diff.STE.pdVec (s + 1) l (fun x => Work.Diff.STE.Flat.seriesFunM c x i j))|))
        ≤ θ * Work.Diff.STE.Flat.ENormSqM (s + 2) (Work.Diff.STE.Flat.seriesFunM c)
          + C * (1 + Work.Diff.STE.Flat.ENormSqFull (s + 1) (Work.Diff.STE.Flat.seriesFunM c)) := by
  classical
  obtain ⟨Cc, hCc, hcomm⟩ := commutator_pair_le hn hs lam hlam Bs hBs θ hθ
  obtain ⟨Cn, hCn, hnonlin⟩ :=
    nonlinearity_pair_le hn hs Nfun hNsm lam hlam Bs hBs θ hθ K hK hKsup
  refine ⟨Cc + Cn + θ * Bs ^ 2 + 1, by positivity, ?_⟩
  intro N c hc hen hell
  have h1 := hcomm N c hc hen hell
  have h2 := hnonlin N c hc hen hell
  have hsplit : (∑ i : Fin n, ∑ j : Fin n,
        ((∑ a, ∑ b, |∑ l : Fin (s + 1) → Fin n,
            Work.Diff.STE.L2re (fun x => Work.Diff.STE.pdVec (s + 1) l (fun y =>
                  Work.Diff.STE.flat.symInvC c a b y
                  * Work.Diff.STE.pd a (Work.Diff.STE.pd b
                      (fun z => Work.Diff.STE.Flat.seriesFunM c z i j)) y) x
                - Work.Diff.STE.flat.symInvC c a b x * Work.Diff.STE.pdVec (s + 1) l
                    (fun z => Work.Diff.STE.pd a (Work.Diff.STE.pd b
                        (fun w => Work.Diff.STE.Flat.seriesFunM c w i j)) z) x)
              (Work.Diff.STE.pdVec (s + 1) l
                (fun x => Work.Diff.STE.Flat.seriesFunM c x i j))|)
          + |∑ l : Fin (s + 1) → Fin n,
              Work.Diff.STE.L2re (Work.Diff.STE.pdVec (s + 1) l
                  (fun x => Nfun (x, Work.Diff.STE.flat.jetP c x) i j))
                (Work.Diff.STE.pdVec (s + 1) l
                  (fun x => Work.Diff.STE.Flat.seriesFunM c x i j))|))
      = (∑ i : Fin n, ∑ j : Fin n, ∑ a : Fin n, ∑ b : Fin n,
          |∑ l : Fin (s + 1) → Fin n,
              Work.Diff.STE.L2re (fun x => Work.Diff.STE.pdVec (s + 1) l (fun y =>
                    Work.Diff.STE.flat.symInvC c a b y
                    * Work.Diff.STE.pd a (Work.Diff.STE.pd b
                        (fun z => Work.Diff.STE.Flat.seriesFunM c z i j)) y) x
                  - Work.Diff.STE.flat.symInvC c a b x * Work.Diff.STE.pdVec (s + 1) l
                      (fun z => Work.Diff.STE.pd a (Work.Diff.STE.pd b
                          (fun w => Work.Diff.STE.Flat.seriesFunM c w i j)) z) x)
                (Work.Diff.STE.pdVec (s + 1) l
                  (fun x => Work.Diff.STE.Flat.seriesFunM c x i j))|)
        + (∑ i : Fin n, ∑ j : Fin n,
            |∑ l : Fin (s + 1) → Fin n,
              Work.Diff.STE.L2re (Work.Diff.STE.pdVec (s + 1) l
                  (fun x => Nfun (x, Work.Diff.STE.flat.jetP c x) i j))
                (Work.Diff.STE.pdVec (s + 1) l
                  (fun x => Work.Diff.STE.Flat.seriesFunM c x i j))|) := by
    simp only [Finset.sum_add_distrib]
  rw [hsplit]
  refine (add_le_add h1 h2).trans ?_
  have hE0 : Work.Diff.STE.Flat.ENormSqM 0 (Work.Diff.STE.Flat.seriesFunM c) ≤ Bs ^ 2 := by
    have h := hen
    simp only [Work.Diff.STE.Flat.ENormSqFull] at h
    have h2 : 0 ≤ Work.Diff.STE.Flat.ENormSqM s (Work.Diff.STE.Flat.seriesFunM c) :=
      Work.Diff.STE.flat.ENormSqM_nonneg _ _
    linarith
  have hF1 : 0 ≤ Work.Diff.STE.Flat.ENormSqFull (s + 1) (Work.Diff.STE.Flat.seriesFunM c) :=
    Work.Diff.STE.flat.ENormSqFull_nonneg _ _
  have hM2 : 0 ≤ Work.Diff.STE.Flat.ENormSqM (s + 2) (Work.Diff.STE.Flat.seriesFunM c) :=
    Work.Diff.STE.flat.ENormSqM_nonneg _ _
  have hθnn : 0 ≤ θ := le_of_lt hθ
  have hBs2 : 0 ≤ Bs ^ 2 := sq_nonneg Bs
  have hstep1 : θ / 4 * Work.Diff.STE.Flat.ENormSqFull (s + 2) (Work.Diff.STE.Flat.seriesFunM c)
      ≤ θ * Work.Diff.STE.Flat.ENormSqM (s + 2) (Work.Diff.STE.Flat.seriesFunM c)
        + θ * Bs ^ 2 * (1 + Work.Diff.STE.Flat.ENormSqFull (s + 1)
            (Work.Diff.STE.Flat.seriesFunM c)) := by
    have hA : θ / 4 * Work.Diff.STE.Flat.ENormSqM (s + 2) (Work.Diff.STE.Flat.seriesFunM c)
        ≤ θ * Work.Diff.STE.Flat.ENormSqM (s + 2) (Work.Diff.STE.Flat.seriesFunM c) :=
      mul_le_mul_of_nonneg_right (by linarith) hM2
    have hB : θ / 4 * Work.Diff.STE.Flat.ENormSqM 0 (Work.Diff.STE.Flat.seriesFunM c)
        ≤ θ * Bs ^ 2 := by
      refine (mul_le_mul_of_nonneg_left hE0 (by linarith)).trans ?_
      exact mul_le_mul_of_nonneg_right (by linarith) hBs2
    have hC : θ * Bs ^ 2
        ≤ θ * Bs ^ 2 * (1 + Work.Diff.STE.Flat.ENormSqFull (s + 1)
            (Work.Diff.STE.Flat.seriesFunM c)) := by
      have h := mul_nonneg (mul_nonneg hθnn hBs2) hF1
      nlinarith [h]
    have hG2 : Work.Diff.STE.Flat.ENormSqFull (s + 2) (Work.Diff.STE.Flat.seriesFunM c)
        = Work.Diff.STE.Flat.ENormSqM (s + 2) (Work.Diff.STE.Flat.seriesFunM c)
          + Work.Diff.STE.Flat.ENormSqM 0 (Work.Diff.STE.Flat.seriesFunM c) := rfl
    calc θ / 4 * Work.Diff.STE.Flat.ENormSqFull (s + 2) (Work.Diff.STE.Flat.seriesFunM c)
        = θ / 4 * Work.Diff.STE.Flat.ENormSqM (s + 2) (Work.Diff.STE.Flat.seriesFunM c)
          + θ / 4 * Work.Diff.STE.Flat.ENormSqM 0 (Work.Diff.STE.Flat.seriesFunM c) := by
          rw [hG2]; ring
      _ ≤ θ * Work.Diff.STE.Flat.ENormSqM (s + 2) (Work.Diff.STE.Flat.seriesFunM c)
          + θ * Bs ^ 2 := add_le_add hA hB
      _ ≤ θ * Work.Diff.STE.Flat.ENormSqM (s + 2) (Work.Diff.STE.Flat.seriesFunM c)
          + θ * Bs ^ 2 * (1 + Work.Diff.STE.Flat.ENormSqFull (s + 1)
              (Work.Diff.STE.Flat.seriesFunM c)) := add_le_add le_rfl hC
  have hstep2 : (Cc + Cn) * (1 + Work.Diff.STE.Flat.ENormSqFull (s + 1)
        (Work.Diff.STE.Flat.seriesFunM c))
      ≤ (Cc + Cn + 1) * (1 + Work.Diff.STE.Flat.ENormSqFull (s + 1)
        (Work.Diff.STE.Flat.seriesFunM c)) := by
    refine mul_le_mul_of_nonneg_right ?_ (by linarith [hF1])
    linarith
  have hleft : θ / 8 * Work.Diff.STE.Flat.ENormSqFull (s + 2) (Work.Diff.STE.Flat.seriesFunM c)
        + Cc * (1 + Work.Diff.STE.Flat.ENormSqFull (s + 1) (Work.Diff.STE.Flat.seriesFunM c))
        + (θ / 8 * Work.Diff.STE.Flat.ENormSqFull (s + 2) (Work.Diff.STE.Flat.seriesFunM c)
          + Cn * (1 + Work.Diff.STE.Flat.ENormSqFull (s + 1)
            (Work.Diff.STE.Flat.seriesFunM c)))
      = θ / 4 * Work.Diff.STE.Flat.ENormSqFull (s + 2) (Work.Diff.STE.Flat.seriesFunM c)
        + (Cc + Cn) * (1 + Work.Diff.STE.Flat.ENormSqFull (s + 1)
            (Work.Diff.STE.Flat.seriesFunM c)) := by ring
  rw [hleft]
  refine (add_le_add hstep1 hstep2).trans ?_
  exact le_of_eq (by ring)

end

end Work.Diff.STE.flat
