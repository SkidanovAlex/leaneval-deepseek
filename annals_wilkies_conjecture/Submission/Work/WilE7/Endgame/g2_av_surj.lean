import Mathlib
import Submission.Work.WilE7.Endgame.g2_defs
import Submission.Work.WilE7.CoreStep.CoreLTSuccNodes
import Submission.Work.WilE7.CoreStep.basePrLin_injective_on_ker_jac
import Submission.Work.WilE7.DimAPI.jac_range_eq_top_of_good
import Submission.Work.WilE7.exists_ker_equiv
import Submission.Work.WilE7.Endgame.eq_zero_of_mem_ker_jac_of_projTop_eq_zero

namespace Work.WilE7.Endgame

open WilkiesDesign WilkiesDesign.E Work.WilE7.MainDesign Work.WilE7.CoreStep Work.WilE7.DimAPI

theorem g2_av_surj {n m : ℕ} (T : WilkiesDesign.E.Stratum 0 (n + (m + 1))) (hT : T.Good) (himm : Work.WilE7.CoreLTSuccPlan.HImm T) (K : ℕ) (e : Fin K ↪ Fin n) (z : Fin (0 + (n + (m + 1))) → ℝ) (hz : z ∈ T.X.set) (hK : K + 1 = n + (m + 1) - T.j) (hAeb : ∀ ξ ∈ LinearMap.ker (Work.WilE7.MainDesign.jac T z), (∀ i : Fin K, Work.WilE7.MainDesign.basePrLin n (m + 1) ξ (e i) = 0) → Work.WilE7.MainDesign.basePrLin n (m + 1) ξ = 0) : (LinearMap.ker (Work.WilE7.MainDesign.jac T z)).map (Work.WilE7.Endgame.AvLin (n := n) (m := m) (K := K) e) = ⊤ := by
  classical
  -- `Good` makes the Jacobian of the equations onto `ℝ^{T.j}`.
  have hsurj : (Work.WilE7.MainDesign.jac T z).range = ⊤ :=
    Work.WilE7.DimAPI.jac_range_eq_top_of_good_aux T hT hz
  -- Rank-nullity: the tangent space has dimension `K + 1`, the dimension of the target.
  have hdom : Module.finrank ℝ ↥(LinearMap.ker (Work.WilE7.MainDesign.jac T z)) = K + 1 := by
    rw [Work.WilE7.finrank_ker_of_surjective _ hsurj, Nat.zero_add, ← hK]
  -- `AvLin e` is injective on the tangent space.
  have hinj : ∀ ξ ∈ LinearMap.ker (Work.WilE7.MainDesign.jac T z),
      AvLin (n := n) (m := m) (K := K) e ξ = 0 → ξ = 0 := by
    intro ξ hξ h0
    -- the vertical coordinate is `verT ξ`
    have hver : Work.WilE7.CoreStep.verT ξ = 0 := by
      have h := congrFun h0 (0 : Fin (K + 1))
      rw [AvLin_apply, Fin.cons_zero] at h
      simpa using h
    -- the remaining coordinates are the `e`-coordinates of the base projection
    have hcoord : ∀ i : Fin K, Work.WilE7.MainDesign.basePrLin n (m + 1) ξ (e i) = 0 := by
      intro i
      have h := congrFun h0 i.succ
      rw [AvLin_apply, Fin.cons_succ] at h
      simpa using h
    have hbase : Work.WilE7.MainDesign.basePrLin n (m + 1) ξ = 0 := hAeb ξ hξ hcoord
    -- hence `projTop` of `ξ` vanishes
    have hpt : Work.WilE7.CoreStep.projTopLin n m
        (Work.WilE7.CoreStep.absPtLin (n + (m + 1)) ξ) = 0 := by
      have hsnoc : Work.WilE7.CoreStep.projTopLin n m
          (Work.WilE7.CoreStep.absPtLin (n + (m + 1)) ξ)
          = Fin.snoc (Work.WilE7.MainDesign.basePrLin n (m + 1) ξ)
              (Work.WilE7.CoreStep.verT ξ) := by
        rw [← Fin.snoc_init_self (Work.WilE7.CoreStep.projTopLin n m
              (Work.WilE7.CoreStep.absPtLin (n + (m + 1)) ξ)),
          Work.WilE7.CoreStep.projTopLin_absPtLin_init,
          Work.WilE7.CoreStep.projTopLin_absPtLin_last]
      rw [hsnoc, hbase, hver]
      funext i
      refine Fin.lastCases ?_ ?_ i
      · rw [Fin.snoc_last]; rfl
      · intro j
        rw [Fin.snoc_castSucc]; rfl
    -- and `HImm` makes `projTop` injective on the tangent space
    exact Work.WilE7.Endgame.eq_zero_of_mem_ker_jac_of_projTop_eq_zero T hT himm hz hξ hpt
  -- Injectivity on the tangent space: the composite with the subtype has trivial kernel.
  have hkerbot : ((AvLin (n := n) (m := m) (K := K) e).comp
      (LinearMap.ker (Work.WilE7.MainDesign.jac T z)).subtype).ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply] at hx
    exact Subtype.ext (hinj x.1 x.2 hx)
  -- So the image has dimension `K + 1`, the dimension of the whole target.
  have hfr : Module.finrank ℝ ((LinearMap.ker (Work.WilE7.MainDesign.jac T z)).map
      (AvLin (n := n) (m := m) (K := K) e)) = K + 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker
      ((AvLin (n := n) (m := m) (K := K) e).comp
        (LinearMap.ker (Work.WilE7.MainDesign.jac T z)).subtype)
    rw [LinearMap.range_comp, Submodule.range_subtype, hkerbot,
      finrank_bot ℝ ↥(LinearMap.ker (Work.WilE7.MainDesign.jac T z)), hdom, add_zero] at h
    exact h
  exact Submodule.eq_top_of_finrank_eq (by rw [hfr, Module.finrank_fin_fun])

end Work.WilE7.Endgame
