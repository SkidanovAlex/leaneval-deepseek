import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.OSubKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM_addArg`

The moving `δ`-tower `deltaTowerM G t c = ∇^{G t, c}(∇^{G t} − ∇^{G 0})` (a vector-valued
`(1, 2 + c)`-tensor: `c` derivative slots and two section slots, `RicFlip/Defs.lean`) is
**additive in each of its `c + 2` slots** on smooth fields.

This is the "tensoriality (slot-additivity) of the tower" that the flip chapter consumes whenever it
has to replace a slot field by a sum.  The proof is an induction on `c`:

* the recursion `vstepM` is built from the value `τ (…) X Z` of the previous level together with the
  *connection corrections* `lcOf g A (·) (v 0 ·)`; additivity of `vstepM g τ` therefore follows from
  additivity of `τ` plus additivity of `lcOf g` in the section slot (the covariant derivative
  axiom `add`) and in the direction slot (pointwise, `(lcOf g A x)` is a continuous linear map);
* the base case is the connection difference `covDiff G t X Z = ∇^{G t}_X Z − ∇^{G 0}_X Z`, whose
  additivity in the section slot is `CovariantDerivative.add` for each of the two connections (the
  `smulRight` terms of the two Leibniz rules cancel), and in the direction slot is pointwise;
* the induction hypothesis must also carry *smoothness* of the tower on smooth tuples, because
  `lcOf` is additive only on differentiable sections (`SmE`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov.RicFlip

open Work.Diff.EXT.ATower

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [I.Boundaryless] [T2Space M]

/-! ## Additivity of `lcOf` (direction and section) -/

/-- Additivity of the covariant derivative in its **direction** slot (pointwise; no smoothness is
needed, the connection is a continuous linear map in the direction). -/
lemma dta_lcOf_add_dir_pt (g : SMet I M) (S W W' : TF) (x : M) :
    lcOf g S x ((W + W') x) = lcOf g S x (W x) + lcOf g S x (W' x) := by
  rw [Pi.add_apply, map_add]

/-- The function-level form of `dta_lcOf_add_dir_pt`. -/
lemma dta_lcOf_add_dir_fun (g : SMet I M) (S W W' : TF) :
    (fun y => lcOf g S y ((W + W') y))
      = (fun y => lcOf g S y (W y)) + (fun y => lcOf g S y (W' y)) := by
  funext y
  exact dta_lcOf_add_dir_pt g S W W' y

/-- `dta_lcOf_add_dir_pt` in the pointwise-sum form (the form produced by `Pi.add_apply`). -/
lemma dta_lcOf_add_dir_pt' (g : SMet I M) (S W W' : TF) (x : M) :
    lcOf g S x (W x + W' x) = lcOf g S x (W x) + lcOf g S x (W' x) :=
  map_add _ _ _

/-- The function-level form of `dta_lcOf_add_dir_pt'`. -/
lemma dta_lcOf_add_dir_fun' (g : SMet I M) (S W W' : TF) :
    (fun y => lcOf g S y (W y + W' y))
      = (fun y => lcOf g S y (W y)) + (fun y => lcOf g S y (W' y)) := by
  funext y
  exact dta_lcOf_add_dir_pt' g S W W' y

/-- Additivity of the covariant derivative in its **section** slot (pointwise), from the covariant
derivative axiom `add`; smoothness of the two sections is required. -/
lemma dta_lcOf_add_sec_pt (g : SMet I M) (A B Z : TF) (hA : SmE I M A) (hB : SmE I M B) (x : M) :
    lcOf g (A + B) x (Z x) = lcOf g A x (Z x) + lcOf g B x (Z x) := by
  rw [((lcOf g).isCovariantDerivativeOn (s := Set.univ)).add (σ := A) (σ' := B)
    (hA.mdifferentiableAt (by simp)) (hB.mdifferentiableAt (by simp)) (by simp)]
  exact add_apply ..

/-- The function-level form of `dta_lcOf_add_sec_pt`. -/
lemma dta_lcOf_add_sec_fun (g : SMet I M) (A B Z : TF) (hA : SmE I M A) (hB : SmE I M B) :
    (fun y => lcOf g (A + B) y (Z y))
      = (fun y => lcOf g A y (Z y)) + (fun y => lcOf g B y (Z y)) := by
  funext y
  exact dta_lcOf_add_sec_pt g A B Z hA hB y

/-! ## `Fin` bookkeeping for `Function.update` and `Fin.succ` -/

lemma dta_upd_zero_succ {X : Type*} {k : ℕ} (v : Fin (k+1) → X) (w : X) :
    (fun j : Fin k => (Function.update v 0 w) j.succ) = fun j : Fin k => v j.succ := by
  funext j; exact Function.update_of_ne (Fin.succ_ne_zero j) w v

lemma dta_upd_zero_succ_apply {X : Type*} {k : ℕ} (v : Fin (k+1) → X) (j : Fin k) (w : X) :
    (Function.update v 0 w) j.succ = v j.succ :=
  Function.update_of_ne (Fin.succ_ne_zero j) w v

lemma dta_upd_succ_zero_apply {X : Type*} {k : ℕ} (v : Fin (k+1) → X) (i : Fin k) (w : X) :
    (Function.update v i.succ w) 0 = v 0 :=
  Function.update_of_ne (Fin.succ_ne_zero i).symm w v

lemma dta_upd_succ_succ_apply {X : Type*} {k : ℕ} (v : Fin (k+1) → X) (i : Fin k) (w : X)
    (i' : Fin k) :
    (Function.update v i.succ w) i'.succ = Function.update (fun j : Fin k => v j.succ) i w i' := by
  by_cases h : i' = i
  · subst h; rw [Function.update_self, Function.update_self]
  · rw [Function.update_of_ne (fun hc => h (Fin.succ_inj.mp hc)) w v,
      Function.update_of_ne h w (fun j : Fin k => v j.succ)]

lemma dta_upd_succ_succ {X : Type*} {k : ℕ} (v : Fin (k+1) → X) (i : Fin k) (w : X) :
    (fun j : Fin k => (Function.update v i.succ w) j.succ)
      = Function.update (fun j : Fin k => v j.succ) i w := by
  funext j; exact dta_upd_succ_succ_apply v i w j

/-! ## The expansions of one recursion step at an updated slot -/

/-- The value of `vstepM` when the updated slot is the *first* one (the direction slot). -/
lemma dta_vstepM_update_zero (g : SMet I M) {k : ℕ} (τ : VOpM (I := I) (M := M) k)
    (v : Fin (k+1) → TF) (w P Q : TF) :
    vstepM g τ (Function.update v 0 w) P Q
      = fun x => lcOf g (τ (fun i : Fin k => v i.succ) P Q) x (w x)
        - ∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
            (fun y => lcOf g (v i.succ) y (w y))) P Q x
        - τ (fun i : Fin k => v i.succ) (fun y => lcOf g P y (w y)) Q x
        - τ (fun i : Fin k => v i.succ) P (fun y => lcOf g Q y (w y)) x := by
  funext x
  simp only [vstepM, dta_upd_zero_succ, dta_upd_zero_succ_apply, Function.update_self]

/-- The value of `vstepM` when the updated slot is a later one (`j.succ`). -/
lemma dta_vstepM_update_succ (g : SMet I M) {k : ℕ} (τ : VOpM (I := I) (M := M) k)
    (v : Fin (k+1) → TF) (j : Fin k) (w P Q : TF) :
    vstepM g τ (Function.update v j.succ w) P Q
      = fun x => lcOf g (τ (Function.update (fun j' : Fin k => v j'.succ) j w) P Q) x (v 0 x)
        - ∑ i : Fin k, τ (Function.update (Function.update (fun j' : Fin k => v j'.succ) j w) i
            (fun y => lcOf g ((Function.update (fun j' : Fin k => v j'.succ) j w) i) y (v 0 y)))
            P Q x
        - τ (Function.update (fun j' : Fin k => v j'.succ) j w)
            (fun y => lcOf g P y (v 0 y)) Q x
        - τ (Function.update (fun j' : Fin k => v j'.succ) j w) P
            (fun y => lcOf g Q y (v 0 y)) x := by
  funext x
  simp only [vstepM, dta_upd_succ_succ, dta_upd_succ_succ_apply, dta_upd_succ_zero_apply]

/-- The value of `vstepM` (no update): kept as a named rewrite rule. -/
lemma dta_vstepM_eq (g : SMet I M) {k : ℕ} (τ : VOpM (I := I) (M := M) k)
    (v : Fin (k+1) → TF) (P Q : TF) :
    vstepM g τ v P Q
      = fun x => lcOf g (τ (fun i : Fin k => v i.succ) P Q) x (v 0 x)
        - ∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
            (fun y => lcOf g (v i.succ) y (v 0 y))) P Q x
        - τ (fun i : Fin k => v i.succ) (fun y => lcOf g P y (v 0 y)) Q x
        - τ (fun i : Fin k => v i.succ) P (fun y => lcOf g Q y (v 0 y)) x := rfl

/-! ## The slot-additivity predicates -/

/-- `VAddArg τ` says that `τ` is additive in each of its `k + 2` slots, **on smooth fields**. -/
def VAddArg {k : ℕ} (τ : VOpM (I := I) (M := M) k) : Prop :=
  (∀ (i : Fin k) (v : Fin k → TF) (W W' P Q : TF),
    (∀ j, SmE I M (v j)) → SmE I M W → SmE I M W' → SmE I M P → SmE I M Q →
    τ (Function.update v i (W + W')) P Q = τ (Function.update v i W) P Q
      + τ (Function.update v i W') P Q)
  ∧ (∀ (v : Fin k → TF) (P P' Q : TF),
    (∀ j, SmE I M (v j)) → SmE I M P → SmE I M P' → SmE I M Q →
    τ v (P + P') Q = τ v P Q + τ v P' Q)
  ∧ (∀ (v : Fin k → TF) (P Q Q' : TF),
    (∀ j, SmE I M (v j)) → SmE I M P → SmE I M Q → SmE I M Q' →
    τ v P (Q + Q') = τ v P Q + τ v P Q')

/-- `VSm τ` says that `τ` sends smooth tuples to smooth fields. -/
def VSm {k : ℕ} (τ : VOpM (I := I) (M := M) k) : Prop :=
  ∀ (v : Fin k → TF) (P Q : TF),
    (∀ i, SmE I M (v i)) → SmE I M P → SmE I M Q → SmE I M (τ v P Q)

/-! ## The recursion step preserves slot-additivity -/

lemma dta_vstepM_addArg (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M)
    {k : ℕ} {τ : VOpM (I := I) (M := M) k} (hadd : VAddArg τ) (hsm : VSm τ) :
    VAddArg (vstepM g τ) := by
  obtain ⟨hadd1, hadd2, hadd3⟩ := hadd
  refine ⟨?_, ?_, ?_⟩
  · -- (1) the `k + 1` derivative slots
    intro i
    induction i using Fin.cases with
    | zero =>
      intro v W W' P Q hv hW hW' hP hQ
      have hv' : ∀ j : Fin k, SmE I M (v j.succ) := fun j => hv j.succ
      have hv0 : SmE I M (v 0) := hv 0
      have hDW : ∀ j : Fin k, SmE I M (fun y => lcOf g (v j.succ) y (W y)) :=
        fun j => lcOf_apply_smE hLC g (v j.succ) W (hv j.succ) hW
      have hDW' : ∀ j : Fin k, SmE I M (fun y => lcOf g (v j.succ) y (W' y)) :=
        fun j => lcOf_apply_smE hLC g (v j.succ) W' (hv j.succ) hW'
      have hDP : SmE I M (fun y => lcOf g P y (W y)) := lcOf_apply_smE hLC g P W hP hW
      have hDP' : SmE I M (fun y => lcOf g P y (W' y)) := lcOf_apply_smE hLC g P W' hP hW'
      have hDQ : SmE I M (fun y => lcOf g Q y (W y)) := lcOf_apply_smE hLC g Q W hQ hW
      have hDQ' : SmE I M (fun y => lcOf g Q y (W' y)) := lcOf_apply_smE hLC g Q W' hQ hW'
      rw [dta_vstepM_update_zero g τ v (W + W') P Q,
          dta_vstepM_update_zero g τ v W P Q,
          dta_vstepM_update_zero g τ v W' P Q]
      funext x
      simp only [Pi.add_apply]
      have hout : lcOf g (τ (fun j : Fin k => v j.succ) P Q) x (W x + W' x)
          = lcOf g (τ (fun j : Fin k => v j.succ) P Q) x (W x)
            + lcOf g (τ (fun j : Fin k => v j.succ) P Q) x (W' x) :=
        dta_lcOf_add_dir_pt' g _ W W' x
      have hsum : (∑ j : Fin k, τ (Function.update (fun i : Fin k => v i.succ) j
            (fun y => lcOf g (v j.succ) y (W y + W' y))) P Q x)
          = (∑ j : Fin k, τ (Function.update (fun i : Fin k => v i.succ) j
              (fun y => lcOf g (v j.succ) y (W y))) P Q x)
            + (∑ j : Fin k, τ (Function.update (fun i : Fin k => v i.succ) j
              (fun y => lcOf g (v j.succ) y (W' y))) P Q x) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [dta_lcOf_add_dir_fun' g (v j.succ) W W']
        exact congrFun (hadd1 j (fun i : Fin k => v i.succ)
          (fun y => lcOf g (v j.succ) y (W y)) (fun y => lcOf g (v j.succ) y (W' y)) P Q
          hv' (hDW j) (hDW' j) hP hQ) x
      have hA : τ (fun i : Fin k => v i.succ) (fun y => lcOf g P y (W y + W' y)) Q x
          = τ (fun i : Fin k => v i.succ) (fun y => lcOf g P y (W y)) Q x
            + τ (fun i : Fin k => v i.succ) (fun y => lcOf g P y (W' y)) Q x := by
        rw [dta_lcOf_add_dir_fun' g P W W']
        exact congrFun (hadd2 (fun i : Fin k => v i.succ)
          (fun y => lcOf g P y (W y)) (fun y => lcOf g P y (W' y)) Q hv' hDP hDP' hQ) x
      have hB : τ (fun i : Fin k => v i.succ) P (fun y => lcOf g Q y (W y + W' y)) x
          = τ (fun i : Fin k => v i.succ) P (fun y => lcOf g Q y (W y)) x
            + τ (fun i : Fin k => v i.succ) P (fun y => lcOf g Q y (W' y)) x := by
        rw [dta_lcOf_add_dir_fun' g Q W W']
        exact congrFun (hadd3 (fun i : Fin k => v i.succ) P
          (fun y => lcOf g Q y (W y)) (fun y => lcOf g Q y (W' y)) hv' hP hDQ hDQ') x
      rw [hout, hsum, hA, hB]
      abel
    | succ j =>
      intro v W W' P Q hv hW hW' hP hQ
      have hv' : ∀ i : Fin k, SmE I M (v i.succ) := fun i => hv i.succ
      have hv0 : SmE I M (v 0) := hv 0
      have hDW : SmE I M (fun y => lcOf g W y (v 0 y)) := lcOf_apply_smE hLC g W (v 0) hW hv0
      have hDW' : SmE I M (fun y => lcOf g W' y (v 0 y)) := lcOf_apply_smE hLC g W' (v 0) hW' hv0
      have hDP : SmE I M (fun y => lcOf g P y (v 0 y)) := lcOf_apply_smE hLC g P (v 0) hP hv0
      have hDQ : SmE I M (fun y => lcOf g Q y (v 0 y)) := lcOf_apply_smE hLC g Q (v 0) hQ hv0
      rw [dta_vstepM_update_succ g τ v j (W + W') P Q,
          dta_vstepM_update_succ g τ v j W P Q,
          dta_vstepM_update_succ g τ v j W' P Q]
      funext x
      simp only [Pi.add_apply]
      -- the single outer term
      have hout : lcOf g (τ (Function.update (fun j' : Fin k => v j'.succ) j (W + W')) P Q) x (v 0 x)
          = lcOf g (τ (Function.update (fun j' : Fin k => v j'.succ) j W) P Q) x (v 0 x)
            + lcOf g (τ (Function.update (fun j' : Fin k => v j'.succ) j W') P Q) x (v 0 x) := by
        rw [hadd1 j (fun j' : Fin k => v j'.succ) W W' P Q hv' hW hW' hP hQ]
        exact dta_lcOf_add_sec_pt g (τ (Function.update (fun j' : Fin k => v j'.succ) j W) P Q)
          (τ (Function.update (fun j' : Fin k => v j'.succ) j W') P Q) (v 0)
          (hsm _ P Q (smE_updateM j hv' hW) hP hQ)
          (hsm _ P Q (smE_updateM j hv' hW') hP hQ) x
      -- the sum
      have hsum : (∑ i : Fin k, τ (Function.update
            (Function.update (fun j' : Fin k => v j'.succ) j (W + W')) i
            (fun y => lcOf g ((Function.update (fun j' : Fin k => v j'.succ) j (W + W')) i) y
              (v 0 y))) P Q x)
          = (∑ i : Fin k, τ (Function.update
              (Function.update (fun j' : Fin k => v j'.succ) j W) i
              (fun y => lcOf g ((Function.update (fun j' : Fin k => v j'.succ) j W) i) y
                (v 0 y))) P Q x)
            + (∑ i : Fin k, τ (Function.update
              (Function.update (fun j' : Fin k => v j'.succ) j W') i
              (fun y => lcOf g ((Function.update (fun j' : Fin k => v j'.succ) j W') i) y
                (v 0 y))) P Q x) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        by_cases hji : i = j
        · -- the summand at `i = j`
          rw [hji]
          rw [Function.update_self j (W + W') (fun j' : Fin k => v j'.succ),
              Function.update_self j W (fun j' : Fin k => v j'.succ),
              Function.update_self j W' (fun j' : Fin k => v j'.succ)]
          rw [Function.update_idem (a := j) (W + W')
                (fun y => lcOf g (W + W') y (v 0 y)) (fun j' : Fin k => v j'.succ),
              Function.update_idem (a := j) W
                (fun y => lcOf g W y (v 0 y)) (fun j' : Fin k => v j'.succ),
              Function.update_idem (a := j) W'
                (fun y => lcOf g W' y (v 0 y)) (fun j' : Fin k => v j'.succ)]
          rw [dta_lcOf_add_sec_fun g W W' (v 0) hW hW']
          exact congrFun (hadd1 j (fun j' : Fin k => v j'.succ)
            (fun y => lcOf g W y (v 0 y)) (fun y => lcOf g W' y (v 0 y)) P Q hv' hDW hDW' hP hQ) x
        · -- the summand at `i ≠ j`
          rw [Function.update_of_ne hji (W + W') (fun j' : Fin k => v j'.succ),
              Function.update_of_ne hji W (fun j' : Fin k => v j'.succ),
              Function.update_of_ne hji W' (fun j' : Fin k => v j'.succ)]
          rw [Function.update_comm (fun h' => hji h'.symm) (W + W')
                (fun y => lcOf g ((fun j' : Fin k => v j'.succ) i) y (v 0 y))
                (fun j' : Fin k => v j'.succ)]
          have hX : SmE I M (fun y => lcOf g ((fun j' : Fin k => v j'.succ) i) y (v 0 y)) :=
            lcOf_apply_smE hLC g _ (v 0) (hv' i) hv0
          have hpt : τ (Function.update (Function.update (fun j' : Fin k => v j'.succ) i
                (fun y => lcOf g ((fun j' : Fin k => v j'.succ) i) y (v 0 y))) j (W + W')) P Q x
              = τ (Function.update (Function.update (fun j' : Fin k => v j'.succ) i
                  (fun y => lcOf g ((fun j' : Fin k => v j'.succ) i) y (v 0 y))) j W) P Q x
                + τ (Function.update (Function.update (fun j' : Fin k => v j'.succ) i
                  (fun y => lcOf g ((fun j' : Fin k => v j'.succ) i) y (v 0 y))) j W') P Q x :=
            congrFun (hadd1 j
              (Function.update (fun j' : Fin k => v j'.succ) i
                (fun y => lcOf g ((fun j' : Fin k => v j'.succ) i) y (v 0 y))) W W' P Q
              (smE_updateM i hv' hX) hW hW' hP hQ) x
          rw [hpt]
          rw [Function.update_comm hji (fun y => lcOf g ((fun j' : Fin k => v j'.succ) i) y (v 0 y))
                W (fun j' : Fin k => v j'.succ),
              Function.update_comm hji (fun y => lcOf g ((fun j' : Fin k => v j'.succ) i) y (v 0 y))
                W' (fun j' : Fin k => v j'.succ)]
      -- the two section corrections
      have hA : τ (Function.update (fun j' : Fin k => v j'.succ) j (W + W'))
            (fun y => lcOf g P y (v 0 y)) Q x
          = τ (Function.update (fun j' : Fin k => v j'.succ) j W)
              (fun y => lcOf g P y (v 0 y)) Q x
            + τ (Function.update (fun j' : Fin k => v j'.succ) j W')
              (fun y => lcOf g P y (v 0 y)) Q x :=
        congrFun (hadd1 j (fun j' : Fin k => v j'.succ) W W'
          (fun y => lcOf g P y (v 0 y)) Q hv' hW hW' hDP hQ) x
      have hB : τ (Function.update (fun j' : Fin k => v j'.succ) j (W + W')) P
            (fun y => lcOf g Q y (v 0 y)) x
          = τ (Function.update (fun j' : Fin k => v j'.succ) j W) P
              (fun y => lcOf g Q y (v 0 y)) x
            + τ (Function.update (fun j' : Fin k => v j'.succ) j W') P
              (fun y => lcOf g Q y (v 0 y)) x :=
        congrFun (hadd1 j (fun j' : Fin k => v j'.succ) W W' P
          (fun y => lcOf g Q y (v 0 y)) hv' hW hW' hP hDQ) x
      rw [hout, hsum, hA, hB]
      abel
  · -- (2) the first section slot
    intro v P P' Q hv hP hP' hQ
    have hv' : ∀ i : Fin k, SmE I M (v i.succ) := fun i => hv i.succ
    have hv0 : SmE I M (v 0) := hv 0
    rw [dta_vstepM_eq g τ v (P + P') Q, dta_vstepM_eq g τ v P Q, dta_vstepM_eq g τ v P' Q]
    funext x
    simp only [Pi.add_apply]
    have hout : lcOf g (τ (fun i : Fin k => v i.succ) (P + P') Q) x (v 0 x)
        = lcOf g (τ (fun i : Fin k => v i.succ) P Q) x (v 0 x)
          + lcOf g (τ (fun i : Fin k => v i.succ) P' Q) x (v 0 x) := by
      rw [hadd2 (fun i : Fin k => v i.succ) P P' Q hv' hP hP' hQ]
      exact dta_lcOf_add_sec_pt g (τ (fun i : Fin k => v i.succ) P Q)
        (τ (fun i : Fin k => v i.succ) P' Q) (v 0)
        (hsm _ P Q hv' hP hQ) (hsm _ P' Q hv' hP' hQ) x
    have hsum : (∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
          (fun y => lcOf g (v i.succ) y (v 0 y))) (P + P') Q x)
        = (∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
            (fun y => lcOf g (v i.succ) y (v 0 y))) P Q x)
          + (∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
            (fun y => lcOf g (v i.succ) y (v 0 y))) P' Q x) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact congrFun (hadd2 (Function.update (fun j : Fin k => v j.succ) i
        (fun y => lcOf g (v i.succ) y (v 0 y))) P P' Q
        (smE_updateM i hv' (lcOf_apply_smE hLC g (v i.succ) (v 0) (hv' i) hv0)) hP hP' hQ) x
    have hA : τ (fun i : Fin k => v i.succ) (fun y => lcOf g (P + P') y (v 0 y)) Q x
        = τ (fun i : Fin k => v i.succ) (fun y => lcOf g P y (v 0 y)) Q x
          + τ (fun i : Fin k => v i.succ) (fun y => lcOf g P' y (v 0 y)) Q x := by
      rw [dta_lcOf_add_sec_fun g P P' (v 0) hP hP']
      exact congrFun (hadd2 (fun i : Fin k => v i.succ)
        (fun y => lcOf g P y (v 0 y)) (fun y => lcOf g P' y (v 0 y)) Q hv'
        (lcOf_apply_smE hLC g P (v 0) hP hv0)
        (lcOf_apply_smE hLC g P' (v 0) hP' hv0) hQ) x
    have hB : τ (fun i : Fin k => v i.succ) (P + P') (fun y => lcOf g Q y (v 0 y)) x
        = τ (fun i : Fin k => v i.succ) P (fun y => lcOf g Q y (v 0 y)) x
          + τ (fun i : Fin k => v i.succ) P' (fun y => lcOf g Q y (v 0 y)) x := by
      exact congrFun (hadd2 (fun i : Fin k => v i.succ) P P'
        (fun y => lcOf g Q y (v 0 y)) hv' hP hP'
        (lcOf_apply_smE hLC g Q (v 0) hQ hv0)) x
    rw [hout, hsum, hA, hB]
    abel
  · -- (3) the second section slot
    intro v P Q Q' hv hP hQ hQ'
    have hv' : ∀ i : Fin k, SmE I M (v i.succ) := fun i => hv i.succ
    have hv0 : SmE I M (v 0) := hv 0
    rw [dta_vstepM_eq g τ v P (Q + Q'), dta_vstepM_eq g τ v P Q, dta_vstepM_eq g τ v P Q']
    funext x
    simp only [Pi.add_apply]
    have hout : lcOf g (τ (fun i : Fin k => v i.succ) P (Q + Q')) x (v 0 x)
        = lcOf g (τ (fun i : Fin k => v i.succ) P Q) x (v 0 x)
          + lcOf g (τ (fun i : Fin k => v i.succ) P Q') x (v 0 x) := by
      rw [hadd3 (fun i : Fin k => v i.succ) P Q Q' hv' hP hQ hQ']
      exact dta_lcOf_add_sec_pt g (τ (fun i : Fin k => v i.succ) P Q)
        (τ (fun i : Fin k => v i.succ) P Q') (v 0)
        (hsm _ P Q hv' hP hQ) (hsm _ P Q' hv' hP hQ') x
    have hsum : (∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
          (fun y => lcOf g (v i.succ) y (v 0 y))) P (Q + Q') x)
        = (∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
            (fun y => lcOf g (v i.succ) y (v 0 y))) P Q x)
          + (∑ i : Fin k, τ (Function.update (fun j : Fin k => v j.succ) i
            (fun y => lcOf g (v i.succ) y (v 0 y))) P Q' x) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      exact congrFun (hadd3 (Function.update (fun j : Fin k => v j.succ) i
        (fun y => lcOf g (v i.succ) y (v 0 y))) P Q Q'
        (smE_updateM i hv' (lcOf_apply_smE hLC g (v i.succ) (v 0) (hv' i) hv0)) hP hQ hQ') x
    have hA : τ (fun i : Fin k => v i.succ) (fun y => lcOf g P y (v 0 y)) (Q + Q') x
        = τ (fun i : Fin k => v i.succ) (fun y => lcOf g P y (v 0 y)) Q x
          + τ (fun i : Fin k => v i.succ) (fun y => lcOf g P y (v 0 y)) Q' x := by
      exact congrFun (hadd3 (fun i : Fin k => v i.succ) (fun y => lcOf g P y (v 0 y)) Q Q'
        hv' (lcOf_apply_smE hLC g P (v 0) hP hv0) hQ hQ') x
    have hB : τ (fun i : Fin k => v i.succ) P (fun y => lcOf g (Q + Q') y (v 0 y)) x
        = τ (fun i : Fin k => v i.succ) P (fun y => lcOf g Q y (v 0 y)) x
          + τ (fun i : Fin k => v i.succ) P (fun y => lcOf g Q' y (v 0 y)) x := by
      rw [dta_lcOf_add_sec_fun g Q Q' (v 0) hQ hQ']
      exact congrFun (hadd3 (fun i : Fin k => v i.succ) P
        (fun y => lcOf g Q y (v 0 y)) (fun y => lcOf g Q' y (v 0 y)) hv' hP
        (lcOf_apply_smE hLC g Q (v 0) hQ hv0)
        (lcOf_apply_smE hLC g Q' (v 0) hQ' hv0)) x
    rw [hout, hsum, hA, hB]
    abel

/-! ## The additivity of the connection difference (the base case) -/

/-- Additivity of the connection difference in its section slot. -/
lemma dta_covDiff_add_sec (G : ℝ → SMet I M) (t : ℝ) (X X' Z : TF)
    (hX : SmE I M X) (hX' : SmE I M X') :
    covDiff G t (X + X') Z = covDiff G t X Z + covDiff G t X' Z := by
  funext y
  simp only [Work.Diff.EXT.ConnCov.covDiff, Pi.add_apply, Pi.sub_apply]
  rw [dta_lcOf_add_sec_pt (G t) X X' Z hX hX' y,
    dta_lcOf_add_sec_pt (G 0) X X' Z hX hX' y]
  abel

/-- Additivity of the connection difference in its direction slot. -/
lemma dta_covDiff_add_dir (G : ℝ → SMet I M) (t : ℝ) (X Z Z' : TF) :
    covDiff G t X (Z + Z') = covDiff G t X Z + covDiff G t X Z' := by
  funext y
  simp only [Work.Diff.EXT.ConnCov.covDiff, Pi.add_apply, Pi.sub_apply]
  rw [dta_lcOf_add_dir_pt' (G t) X Z Z' y, dta_lcOf_add_dir_pt' (G 0) X Z Z' y]
  abel

lemma dta_deltaBaseM_addArg (G : ℝ → SMet I M) (t : ℝ) :
    VAddArg (I := I) (M := M) (deltaBaseM G t) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i; exact Fin.elim0 i
  · intro v X X' Z hv hX hX' hZ
    exact dta_covDiff_add_sec (I := I) (M := M) G t X X' Z hX hX'
  · intro v X Z Z' hv hX hZ hZ'
    exact dta_covDiff_add_dir (I := I) (M := M) G t X Z Z'

lemma dta_deltaBaseM_sm (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → SMet I M) (t : ℝ) :
    VSm (I := I) (M := M) (deltaBaseM G t) := by
  intro v X Y hv hX hY
  exact (lcOf_apply_smE hLC (G t) X Y hX hY).sub_section (lcOf_apply_smE hLC (G 0) X Y hX hY)

/-! ## The induction on the order -/

lemma dta_vtowerM_addArg (hLC : Submission.Diff.LCSmooth I M) (g : SMet I M)
    {δ : VOpM (I := I) (M := M) 0} (hadd : VAddArg δ) (hsm : VSm δ) :
    ∀ k : ℕ, VAddArg (vtowerM g δ k) := by
  intro k
  induction k with
  | zero => exact hadd
  | succ k ih =>
    have hδ : ∀ (w : Fin 0 → TF) (X Y : TF), SmE I M X → SmE I M Y → SmE I M (δ w X Y) :=
      fun w X Y hX hY => hsm w X Y (fun j => Fin.elim0 j) hX hY
    have hsmk : VSm (vtowerM g δ k) :=
      fun v X Y hv hX hY => smE_vtowerM hLC g δ hδ k v X Y hv hX hY
    exact dta_vstepM_addArg hLC g ih hsmk

/-! ## The target theorem -/

theorem deltaTowerM_addArg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (c : ℕ) :
    (∀ (j : Fin c) (v : Fin c → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
      (W W' X Z : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)),
      (∀ i, Work.Diff.EXT.ATower.SmE I M (v i)) → Work.Diff.EXT.ATower.SmE I M W →
      Work.Diff.EXT.ATower.SmE I M W' → Work.Diff.EXT.ATower.SmE I M X →
      Work.Diff.EXT.ATower.SmE I M Z → ∀ x : M,
      Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t c (Function.update v j (W + W')) X Z x
        = Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t c (Function.update v j W) X Z x
          + Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t c (Function.update v j W') X Z x)
    ∧ (∀ (v : Fin c → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
      (X X' Z : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)),
      (∀ i, Work.Diff.EXT.ATower.SmE I M (v i)) → Work.Diff.EXT.ATower.SmE I M X →
      Work.Diff.EXT.ATower.SmE I M X' → Work.Diff.EXT.ATower.SmE I M Z → ∀ x : M,
      Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t c v (X + X') Z x
        = Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t c v X Z x
          + Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t c v X' Z x)
    ∧ (∀ (v : Fin c → Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M))
      (X Z Z' : Work.Diff.EXT.ConnCov.AMB.TF (I := I) (M := M)),
      (∀ i, Work.Diff.EXT.ATower.SmE I M (v i)) → Work.Diff.EXT.ATower.SmE I M X →
      Work.Diff.EXT.ATower.SmE I M Z → Work.Diff.EXT.ATower.SmE I M Z' → ∀ x : M,
      Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t c v X (Z + Z') x
        = Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t c v X Z x
          + Work.Diff.EXT.ConnCov.RicFlip.deltaTowerM G t c v X Z' x) := by
  have h := dta_vtowerM_addArg (I := I) (M := M) hLC (G t)
    (dta_deltaBaseM_addArg (I := I) (M := M) G t) (dta_deltaBaseM_sm (I := I) (M := M) hLC G t) c
  have h' : VAddArg (I := I) (M := M) (deltaTowerM G t c) := h
  obtain ⟨h1, h2, h3⟩ := h'
  exact ⟨fun j v W W' X Z hv hW hW' hX hZ x => congrFun (h1 j v W W' X Z hv hW hW' hX hZ) x,
    fun v X X' Z hv hX hX' hZ x => congrFun (h2 v X X' Z hv hX hX' hZ) x,
    fun v X Z Z' hv hX hZ hZ' x => congrFun (h3 v X Z Z' hv hX hZ hZ') x⟩

end Work.Diff.EXT.ConnCov.RicFlip
