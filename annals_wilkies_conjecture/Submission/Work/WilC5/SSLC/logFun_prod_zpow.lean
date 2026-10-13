/-
  WilC5 / SSLC — `logFun` is compatible with finite products of integral powers.

      `logFun (∏ i ∈ s, f i ^ N i) = ∑ i ∈ s, (N i : K) · logFun (f i)`   (`0 < f i` on `s`).

  This is the multi-factor companion of `Work.WilC5.S4ExpF.logFun_zpow`
  (`logFun (x ^ n) = n · logFun x`).  The proof is

  * `logFun_prod_of_pos` below: `logFun` of a finite product of *positive* elements is the sum
    of the `logFun`s — an induction on the `Finset`, using the additive law of `logFun` on
    positive elements (`Work.WilC5.S4ExpF.logFun_mul_pos`) and `logFun 1 = 0`
    (`Work.WilC5.S4ExpF.logFun_one`), together with positivity of finite products
    (`Finset.prod_pos`);
  * each factor `f i ^ (N i)` is positive (`zpow_pos`), so the product law applies, and
    `logFun_zpow` rewrites each `logFun (f i ^ N i)`.
-/
import Mathlib
import Submission.Work.WilC5.S4ExpF.logclosure_exp
import Submission.Work.WilC5.S4ExpF.logFun_zpow

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
open Classical

namespace Work.WilC5.SSLC

/-- **Additivity of the definable logarithm over a finite product of positive elements**:

    `logFun (∏ i ∈ s, g i) = ∑ i ∈ s, logFun (g i)`   whenever `0 < g i` for all `i ∈ s`. -/
theorem logFun_prod_of_pos {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K]
    [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    (hTE : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    {ι : Type*} (s : Finset ι) (g : ι → K) (hpos : ∀ i ∈ s, 0 < g i) :
    Work.WilC5.logFun (∏ i ∈ s, g i) = ∑ i ∈ s, Work.WilC5.logFun (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.sum_empty,
        Work.WilC5.S4ExpF.logFun_one hTE hadd hone]
  | insert a s ha ih =>
      have ha_pos : 0 < g a := hpos a (Finset.mem_insert_self a s)
      have hs_pos : ∀ i ∈ s, 0 < g i := fun i hi => hpos i (Finset.mem_insert_of_mem hi)
      rw [Finset.prod_insert ha, Finset.sum_insert ha,
        Work.WilC5.S4ExpF.logFun_mul_pos hTE hadd hmul hleneg ha_pos (Finset.prod_pos hs_pos),
        ih hs_pos]

theorem logFun_prod_zpow {K : Type} [WilkiesDesign.CG.LEc.Structure K] [Field K] [LinearOrder K]
    [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    (hTE : FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TE)
    (hadd : ∀ x y : K, Work.WilC5.addE x y = x + y)
    (hmul : ∀ x y : K, Work.WilC5.mulE x y = x * y)
    (hone : (Work.WilC5.oneE : K) = 1)
    (hleneg : ∀ x y : K, Work.WilC5.leE x y ↔ x ≤ y)
    {ι : Type*} (s : Finset ι) (f : ι → K) (N : ι → ℤ)
    (hpos : ∀ i ∈ s, 0 < f i) :
    Work.WilC5.logFun (∏ i ∈ s, f i ^ (N i))
      = ∑ i ∈ s, (N i : K) * Work.WilC5.logFun (f i) := by
  classical
  have h := logFun_prod_of_pos hTE hadd hmul hone hleneg s (fun i => f i ^ (N i))
    (fun i hi => zpow_pos (hpos i hi) (N i))
  rw [h]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  exact Work.WilC5.S4ExpF.logFun_zpow hTE hadd hmul hone hleneg (f i) (hpos i hi) (N i)

end Work.WilC5.SSLC
