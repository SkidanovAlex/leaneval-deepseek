import Mathlib
import Submission.Work.ORLyndon.CLDirect.cldDefs
import Submission.Work.ORLyndon.CLDirect.thetaLin_of
import Submission.Work.ORLyndon.CLDirect.presentSec_inv_mul_mem
import Submission.Work.ORLyndon.CLDirect.thetaFun_mul_mem
import Submission.Work.ORLyndon.CLDirect.thetaLin_mul_of_mem_span
import Submission.Work.ORLyndon.CLDirect.sum_smul_of_sub_one_eq

namespace Work.ORLyndon.Fox

/-- Re-export of `Work.ORLyndon.foxD` under the `Fox` namespace, matching the name used in the
statement of `Work.ORLyndon.CLDirect.foxKernel_vanish`. -/
noncomputable abbrev foxD {X : Type*} [DecidableEq X] {K : Type*} [Ring K] (x : X) :
    FreeGroup X → MonoidAlgebra K (FreeGroup X) := Work.ORLyndon.foxD (K := K) x

end Work.ORLyndon.Fox

namespace Work.ORLyndon.CLDirect

open MonoidAlgebra

variable {X : Type*} [DecidableEq X] {K : Type*} [Field K]

/-- Auxiliary: the presentation `presentAlg` commutes with scalar multiplication. -/
private theorem presentAlg_smul (r : FreeGroup X) (c : K) (z : MonoidAlgebra K (FreeGroup X)) :
    Work.ORLyndon.presentAlg K r (c • z) = c • Work.ORLyndon.presentAlg K r z := by
  rw [Algebra.smul_def, map_mul]
  have hc : Work.ORLyndon.presentAlg K r
      ((algebraMap K (MonoidAlgebra K (FreeGroup X))) c) =
      algebraMap K (MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup r)) c :=
    (Work.ORLyndon.presentAlgAlg (K := K) r).commutes c
  rw [hc, ← Algebra.smul_def]

/-- Auxiliary: `Θ 1 = thetaFun 1`. -/
private theorem thetaLin_one (r : FreeGroup X)
    (φ : FreeGroup X → MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup r)) :
    thetaLin (K := K) r φ (1 : MonoidAlgebra K (FreeGroup X)) = thetaFun (K := K) r φ 1 := by
  rw [show (1 : MonoidAlgebra K (FreeGroup X)) = MonoidAlgebra.of K (FreeGroup X) (1 : FreeGroup X)
      from (map_one _).symm, thetaLin_of]

/-- Auxiliary: `thetaFun n - thetaFun 1 = φ n` for `n` in the normal closure of `r`. -/
private theorem thetaFun_sub_one (r : FreeGroup X)
    (φ : FreeGroup X → MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup r))
    (hmul : ∀ n n', n ∈ Subgroup.normalClosure ({r} : Set (FreeGroup X)) →
      n' ∈ Subgroup.normalClosure ({r} : Set (FreeGroup X)) → φ (n * n') = φ n + φ n')
    (n : FreeGroup X) (hn : n ∈ Subgroup.normalClosure ({r} : Set (FreeGroup X))) :
    thetaFun (K := K) r φ n - thetaFun (K := K) r φ 1 = φ n := by
  have h := thetaFun_mul_mem r φ hmul 1 n hn
  rw [one_mul] at h
  have h1 : Work.ORLyndon.presentRho r (1 : FreeGroup X) = 1 := map_one _
  rw [h1, map_one, one_mul] at h
  rw [h, add_sub_cancel_left]

/-- The Fox-kernel (Magnus embedding) lemma. Sketch: let `E := ∑ i, c i • foxFD (ρ i)` and `Dl := ∑ i, c i • (of (ρ i) − 1)`. `Θ Dl = ∑ c i • (thetaFun (ρ i) − thetaFun 1)` by `map_sum`, `map_smul`, `map_sub`, `thetaLin_of`; `thetaFun_mul_mem` with `f = 1`, `n = ρ i` gives `thetaFun (1 * ρ i) = thetaFun 1 + φ (ρ i)` (using `presentRho r 1 = 1`, `of 1 = 1`), so `Θ Dl = ∑ c i • φ (ρ i)`. By `sum_smul_of_sub_one_eq`, `Θ Dl = E.sum (fun x d => Θ (d * of x) − Θ d)` (`map_finsuppSum`, `mul_sub`, `mul_one`); each summand is `0` by `thetaLin_mul_of_mem_span` once `E x ∈ span`: `E x = ∑ i, c i • foxD x (ρ i)` (`Finsupp.finset_sum_apply`, `smul_apply`, `foxFD_apply`), and its `presentAlg` image is the sum in `h` (`presentAlgAlg`, `map_smul`), then `mapDomain_eq_zero_iff_mem_ker_span`. -/
theorem foxKernel_vanish {X : Type*} [DecidableEq X] {K : Type*} [Field K] (r : FreeGroup X)
    (φ : FreeGroup X → MonoidAlgebra K (Work.ORLyndon.OneRelatorGroup r))
    (hmul : ∀ n n', n ∈ Subgroup.normalClosure ({r} : Set (FreeGroup X)) →
      n' ∈ Subgroup.normalClosure ({r} : Set (FreeGroup X)) → φ (n * n') = φ n + φ n')
    (hconj : ∀ f n, n ∈ Subgroup.normalClosure ({r} : Set (FreeGroup X)) →
      φ (f * n * f⁻¹) = MonoidAlgebra.of K _ (Work.ORLyndon.presentRho r f) * φ n)
    (ι : Type) [Fintype ι] (ρ : ι → FreeGroup X)
    (hρ : ∀ i, ρ i ∈ Subgroup.normalClosure ({r} : Set (FreeGroup X))) (c : ι → K)
    (h : ∀ x : X, ∑ i, c i • Work.ORLyndon.presentAlg K r
      (Work.ORLyndon.Fox.foxD (K := K) x (ρ i)) = 0) :
    ∑ i, c i • φ (ρ i) = 0 := by
  classical
  set E : X →₀ MonoidAlgebra K (FreeGroup X) :=
    ∑ i, c i • Work.ORLyndon.foxFD (K := K) (ρ i) with hE
  set Dl : MonoidAlgebra K (FreeGroup X) :=
    ∑ i, c i • (MonoidAlgebra.of K (FreeGroup X) (ρ i) - 1) with hDl
  -- `E x` is the Fox derivative vector of the family `ρ`.
  have hEx : ∀ x : X, E x = ∑ i, c i • Work.ORLyndon.foxD (K := K) x (ρ i) := by
    intro x
    rw [hE, Finsupp.finsetSum_apply]
    exact Finset.sum_congr rfl (fun i _ => by
      rw [Finsupp.smul_apply, Work.ORLyndon.foxFD_apply])
  -- Each coefficient of `E` lies in the kernel span, because its image under `presentAlg` is `0`.
  have hspan : ∀ x : X, E x ∈ Submodule.span (MonoidAlgebra K (FreeGroup X))
      (Set.range fun m : MonoidHom.ker (Work.ORLyndon.presentRho r) =>
        MonoidAlgebra.single (m : FreeGroup X) (1 : K) - 1) := by
    intro x
    rw [← Work.ORLyndon.mapDomain_eq_zero_iff_mem_ker_span r (E x), hEx x, map_sum]
    rw [Finset.sum_congr rfl (fun i _ =>
      presentAlg_smul r (c i) (Work.ORLyndon.foxD (K := K) x (ρ i)))]
    exact h x
  -- Step 1: `Θ Dl = ∑ i, c i • φ (ρ i)`.
  have hstep1 : thetaLin (K := K) r φ Dl = ∑ i, c i • φ (ρ i) := by
    rw [hDl, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [map_smul, map_sub, thetaLin_of, thetaLin_one (K := K),
      thetaFun_sub_one r φ hmul (ρ i) (hρ i)]
  -- Step 2: `Θ Dl = E.sum (fun x d => Θ (d * of x) - Θ d)`.
  have hstep2 : thetaLin (K := K) r φ Dl =
      E.sum (fun x d => thetaLin (K := K) r φ
        (d * MonoidAlgebra.of K (FreeGroup X) (FreeGroup.of x)) -
        thetaLin (K := K) r φ d) := by
    rw [show Dl = E.sum (fun x d =>
        d * (MonoidAlgebra.of K (FreeGroup X) (FreeGroup.of x) - 1)) from by
      rw [hDl, hE]
      exact sum_smul_of_sub_one_eq ι ρ c]
    rw [map_finsuppSum]
    apply Finsupp.sum_congr
    intro x _
    rw [mul_sub, mul_one, map_sub]
  -- Step 3: the summands vanish by `thetaLin_mul_of_mem_span`.
  have hstep3 : E.sum (fun x d => thetaLin (K := K) r φ
        (d * MonoidAlgebra.of K (FreeGroup X) (FreeGroup.of x)) -
        thetaLin (K := K) r φ d) = 0 := by
    rw [Finsupp.sum_of_support_subset E (Finset.Subset.refl _)
      (fun x d => thetaLin (K := K) r φ
        (d * MonoidAlgebra.of K (FreeGroup X) (FreeGroup.of x)) -
        thetaLin (K := K) r φ d) (fun i _ => by simp)]
    apply Finset.sum_eq_zero
    intro x _
    rw [thetaLin_mul_of_mem_span r φ hmul hconj (hspan x) (FreeGroup.of x), sub_self]
  rw [← hstep1, hstep2, hstep3]

end Work.ORLyndon.CLDirect
