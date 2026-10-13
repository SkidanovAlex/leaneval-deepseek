/-
  `Work.CoreStep.branchDomainPairFacts`: the tangent-space facts for a `Good` stratum of the
  same-base pair set `absPairSet T` (used by `Work.CoreStep.branchDomain_open`).
-/
import Mathlib
import Submission.Work.CoreStep.branchDomainSetup
import Submission.Work.CoreStep.tangent_ker_of_vanishing
import Submission.Work.CoreStep.absPairSet_mem_iff
import Submission.Work.WilE7.DimAPI.range_fderiv_good_eq_top
import Submission.Work.WilE7.DimAPI.jac_eq_fderiv

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open WilkiesDesign WilkiesDesign.E
namespace Work.CoreStep

open Work.WilE7 Work.WilE7.CoreStep

/-- The application form of `DimAPI.jac_eq_fderiv`. -/
theorem eqMap_fderiv_apply {N : ℕ} (S : Stratum 0 N) (z v : Fin (0 + N) → ℝ) :
    (fderiv ℝ (DimAPI.eqMap S) z) v = MainDesign.jac S z v := by
  change (fderiv ℝ (fun w : Fin (0 + N) → ℝ => fun a : Fin S.j =>
    eaEval S.X.c (S.h a) w) z) v = MainDesign.jac S z v
  exact LinearMap.congr_fun (DimAPI.jac_eq_fderiv S z).symm v

/-- **The tangent space of a `Good` stratum kills functions vanishing on it, applied to the pair
structure of `absPairSet T`.**  For `z` in a `Good` stratum `W` of the same-base pair set of `T`
and `v` in the tangent space `ker (jac W z)`:

* the two halves of `absPt v` have the same base projection (they are tangent to the same-base
  pair set);
* the second half lies in the tangent space of `T` at the second half of `z`;
* the first half lies in the tangent space of `T` at the first half of `z`. -/
theorem jac_pair_facts {n m : ℕ} (T : Stratum 0 (n + (m + 1))) (hT : T.Good)
    (W : Stratum 0 (pPair n m)) (hW : W.Good)
    (hWsub : W.X.set ⊆ (absPairSet T).set)
    {z : Fin (0 + pPair n m) → ℝ} (hz : z ∈ W.X.set) :
    ∀ v : Fin (0 + pPair n m) → ℝ, MainDesign.jac W z v = 0 →
      (projFirst n (m + 1) (projFirst (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt v)) =
        projFirst n (m + 1) (projSnd (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt v))) ∧
      (MainDesign.jac T (absPtUp (projSnd (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt z)))
        (absPtUp (projSnd (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt v))) = 0) ∧
      (MainDesign.jac T (absPtUp (projFirst (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt z)))
        (absPtUp (projFirst (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt v))) = 0) := by
  intro v hv
  have hsurjW : (fderiv ℝ (DimAPI.eqMap W) z).range = ⊤ := by
    change (fderiv ℝ (fun w : Fin (0 + pPair n m) → ℝ => fun a : Fin W.j =>
      eaEval W.X.c (W.h a) w) z).range = ⊤
    exact DimAPI.range_fderiv_good_eq_top W hW hz
  have hP : Filter.Eventually (fun y => DimAPI.eqMap W y = DimAPI.eqMap W z → y ∈ W.X.set)
      (nhds z) := by
    filter_upwards [Work.WilE5.Stratum.good_local hW hz] with y hy
    intro heq
    refine hy (Subsingleton.elim _ _) (fun a => ?_)
    have h1 : eaEval W.X.c (W.h a) y = eaEval W.X.c (W.h a) z := by
      have := congrFun heq a
      rwa [DimAPI.eqMap_apply, DimAPI.eqMap_apply] at this
    rw [h1]
    exact congrFun (DimAPI.eqMap_eq_zero_of_good W hW hz) a
  have hv' : (fderiv ℝ (DimAPI.eqMap W) z) v = 0 := by
    rw [eqMap_fderiv_apply W z v, hv]
  have hparts : ∀ y, y ∈ W.X.set →
      absPtUp (projFirst (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt y)) ∈ T.X.set ∧
      absPtUp (projSnd (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt y)) ∈ T.X.set ∧
      projFirst n (m + 1) (projFirst (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt y)) =
        projFirst n (m + 1) (projSnd (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt y)) :=
    fun y hy => (absPairSet_mem_iff T y).mp (hWsub hy)
  -- (i) the base-projection gap is linear and vanishes on `W.X.set`
  have hf1 : projFirst n (m + 1) (projFirst (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt v)) =
      projFirst n (m + 1) (projSnd (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt v)) := by
    set G : (Fin (0 + pPair n m) → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
      (linProjFirst n (m + 1)).comp
        (((linProjFirst (n + (m + 1)) (n + (m + 1))) -
          (linProjSnd (n + (m + 1)) (n + (m + 1)))).comp (linAbsPt (pPair n m))) with hG
    have hGv : ∀ y, y ∈ W.X.set → G y = 0 := by
      intro y hy
      have hy1 := (hparts y hy).2.2
      rw [hG]
      show projFirst n (m + 1) (projFirst (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt y)) -
        projFirst n (m + 1) (projSnd (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt y)) = 0
      rw [hy1, sub_self]
    have hG' : HasFDerivAt (fun y => G y) (LinearMap.toContinuousLinearMap G) z :=
      (LinearMap.toContinuousLinearMap G).hasFDerivAt
    have hkey := tangent_ker_of_vanishing (F := DimAPI.eqMap W) (z := z)
      (fun y => DimAPI.analyticAt_eqMap W y) hsurjW (fun y => y ∈ W.X.set) hP
      (fun y => G y) (LinearMap.toContinuousLinearMap G) hG' hGv v hv'
    have hvG : G v = 0 := hkey
    have hGapp : G v = projFirst n (m + 1) (projFirst (n + (m + 1)) (n + (m + 1))
        (MainDesign.absPt v)) -
        projFirst n (m + 1) (projSnd (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt v)) := by
      simp only [hG, LinearMap.comp_apply, LinearMap.sub_apply, linProjFirst_apply,
        linProjSnd_apply, linAbsPt_apply, map_sub]
    rw [hGapp] at hvG
    exact sub_eq_zero.mp hvG
  refine ⟨hf1, ?_, ?_⟩
  · -- (ii) the second half lies in the tangent space of `T`
    have hEqT : HasFDerivAt (DimAPI.eqMap T) (fderiv ℝ (DimAPI.eqMap T) (pairSndLift z))
        (pairSndLift (n := n) (m := m) z) :=
      (DimAPI.analyticAt_eqMap T (pairSndLift (n := n) (m := m) z)).hasStrictFDerivAt.hasFDerivAt
    have hlift : HasFDerivAt (fun y => pairSndLift (n := n) (m := m) y)
        (LinearMap.toContinuousLinearMap (pairSndLift (n := n) (m := m))) z :=
      (LinearMap.toContinuousLinearMap (pairSndLift (n := n) (m := m))).hasFDerivAt
    have hGder := hEqT.comp z hlift
    have hGder' : HasFDerivAt (fun y => DimAPI.eqMap T (pairSndLift (n := n) (m := m) y))
        ((fderiv ℝ (DimAPI.eqMap T) (pairSndLift (n := n) (m := m) z)) ∘SL
          (LinearMap.toContinuousLinearMap (pairSndLift (n := n) (m := m)))) z := by
      simpa [Function.comp_def] using hGder
    have hP2 : Filter.Eventually (fun y => DimAPI.eqMap W y = DimAPI.eqMap W z →
        DimAPI.eqMap T (pairSndLift (n := n) (m := m) y) = 0) (nhds z) := by
      filter_upwards [hP] with y hy hyeq
      have hy' : y ∈ W.X.set := hy hyeq
      rw [pairSndLift_apply]
      exact DimAPI.eqMap_eq_zero_of_good T hT ((hparts y hy').2.1)
    have hkey := tangent_ker_of_vanishing (F := DimAPI.eqMap W) (z := z)
      (fun y => DimAPI.analyticAt_eqMap W y) hsurjW
      (fun y => DimAPI.eqMap T (pairSndLift (n := n) (m := m) y) = 0) hP2
      (fun y => DimAPI.eqMap T (pairSndLift (n := n) (m := m) y))
      ((fderiv ℝ (DimAPI.eqMap T) (pairSndLift (n := n) (m := m) z)) ∘SL
        (LinearMap.toContinuousLinearMap (pairSndLift (n := n) (m := m))))
      hGder' (fun y hy => hy) v hv'
    have hconv : ((fderiv ℝ (DimAPI.eqMap T) (pairSndLift (n := n) (m := m) z)) ∘SL
        (LinearMap.toContinuousLinearMap (pairSndLift (n := n) (m := m)))) v =
        MainDesign.jac T (absPtUp (projSnd (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt z)))
          (absPtUp (projSnd (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt v))) := by
      rw [ContinuousLinearMap.comp_apply]
      change (fderiv ℝ (DimAPI.eqMap T) (pairSndLift (n := n) (m := m) z))
        (pairSndLift (n := n) (m := m) v) =
        MainDesign.jac T (absPtUp (projSnd (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt z)))
          (absPtUp (projSnd (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt v)))
      rw [pairSndLift_apply, pairSndLift_apply]
      exact eqMap_fderiv_apply T _ _
    rw [hconv] at hkey
    exact hkey
  · -- (iii) the first half lies in the tangent space of `T`
    have hEqT : HasFDerivAt (DimAPI.eqMap T) (fderiv ℝ (DimAPI.eqMap T) (pairFstLift z))
        (pairFstLift (n := n) (m := m) z) :=
      (DimAPI.analyticAt_eqMap T (pairFstLift (n := n) (m := m) z)).hasStrictFDerivAt.hasFDerivAt
    have hlift : HasFDerivAt (fun y => pairFstLift (n := n) (m := m) y)
        (LinearMap.toContinuousLinearMap (pairFstLift (n := n) (m := m))) z :=
      (LinearMap.toContinuousLinearMap (pairFstLift (n := n) (m := m))).hasFDerivAt
    have hGder := hEqT.comp z hlift
    have hGder' : HasFDerivAt (fun y => DimAPI.eqMap T (pairFstLift (n := n) (m := m) y))
        ((fderiv ℝ (DimAPI.eqMap T) (pairFstLift (n := n) (m := m) z)) ∘SL
          (LinearMap.toContinuousLinearMap (pairFstLift (n := n) (m := m)))) z := by
      simpa [Function.comp_def] using hGder
    have hP2 : Filter.Eventually (fun y => DimAPI.eqMap W y = DimAPI.eqMap W z →
        DimAPI.eqMap T (pairFstLift (n := n) (m := m) y) = 0) (nhds z) := by
      filter_upwards [hP] with y hy hyeq
      have hy' : y ∈ W.X.set := hy hyeq
      rw [pairFstLift_apply]
      exact DimAPI.eqMap_eq_zero_of_good T hT ((hparts y hy').1)
    have hkey := tangent_ker_of_vanishing (F := DimAPI.eqMap W) (z := z)
      (fun y => DimAPI.analyticAt_eqMap W y) hsurjW
      (fun y => DimAPI.eqMap T (pairFstLift (n := n) (m := m) y) = 0) hP2
      (fun y => DimAPI.eqMap T (pairFstLift (n := n) (m := m) y))
      ((fderiv ℝ (DimAPI.eqMap T) (pairFstLift (n := n) (m := m) z)) ∘SL
        (LinearMap.toContinuousLinearMap (pairFstLift (n := n) (m := m))))
      hGder' (fun y hy => hy) v hv'
    have hconv : ((fderiv ℝ (DimAPI.eqMap T) (pairFstLift (n := n) (m := m) z)) ∘SL
        (LinearMap.toContinuousLinearMap (pairFstLift (n := n) (m := m)))) v =
        MainDesign.jac T (absPtUp (projFirst (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt z)))
          (absPtUp (projFirst (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt v))) := by
      rw [ContinuousLinearMap.comp_apply]
      change (fderiv ℝ (DimAPI.eqMap T) (pairFstLift (n := n) (m := m) z))
        (pairFstLift (n := n) (m := m) v) =
        MainDesign.jac T (absPtUp (projFirst (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt z)))
          (absPtUp (projFirst (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt v)))
      rw [pairFstLift_apply, pairFstLift_apply]
      exact eqMap_fderiv_apply T _ _
    rw [hconv] at hkey
    exact hkey

end Work.CoreStep
