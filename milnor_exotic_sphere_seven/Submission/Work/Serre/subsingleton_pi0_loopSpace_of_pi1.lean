import Submission.Work.Serre.Consumers
import Submission.Work.RatHurewicz.PairFibre
import Submission.Work.StemsB.fibrationLES_of_serre

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000
open scoped Topology Topology.Homotopy unitInterval
open Work.Serre

namespace Work.Serre
noncomputable section

/-- Two homotopic paths are joined by a path in the path space. -/
theorem joined_of_path_homotopic {X : Type} [TopologicalSpace X] {x y : X} {p q : Path x y}
    (h : p.Homotopic q) : Joined p q := by
  obtain ⟨F⟩ := h
  refine ⟨{ toFun := F.eval, continuous_toFun := ?_, source' := F.eval_zero, target' := F.eval_one }⟩
  have hcont : Continuous (fun t : I => ((F.eval t : Path x y) : C(I, X))) := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    show Continuous fun p : I × I => (F.toHomotopy : C(I × I, X)) p
    exact (F.toHomotopy).continuous
  exact continuous_induced_rng.mpr hcont

/-- **The loop space is path connected when `π₁` vanishes.** -/
theorem subsingleton_pi0_loopSpace_of_pi1 {X : Type} [TopologicalSpace X] (x : X)
    (h : Subsingleton (HomotopyGroup (Fin 1) X x)) :
    Subsingleton (HomotopyGroup (Fin 0) (Path x x) (Path.refl x)) := by
  haveI hFG : Subsingleton (Path.Homotopic.Quotient x x) := by
    haveI := h
    exact (HomotopyGroup.pi1EquivFundamentalGroup (x := x)).surjective.subsingleton
  have hpc : PathConnectedSpace (Path x x) := by
    refine ⟨⟨Path.refl x⟩, fun p q => ?_⟩
    have h1 : (p.trans q.symm).Homotopic (Path.refl x) :=
      Path.Homotopic.Quotient.eq.mp (Subsingleton.elim _ _)
    have ha : p.Homotopic (p.trans (q.symm.trans q)) :=
      (Path.Homotopic.trans_refl p).symm.trans
        ((Path.Homotopic.refl p).hcomp (Path.Homotopic.symm_trans q).symm)
    have hb : (p.trans (q.symm.trans q)).Homotopic ((p.trans q.symm).trans q) :=
      (Path.Homotopic.trans_assoc p q.symm q).symm
    have hc : ((p.trans q.symm).trans q).Homotopic q :=
      (h1.hcomp (Path.Homotopic.refl q)).trans (Path.Homotopic.refl_trans q)
    exact joined_of_path_homotopic (ha.trans (hb.trans hc))
  haveI := hpc
  have hZ : Subsingleton (ZerothHomotopy (Path x x)) :=
    (pathConnectedSpace_iff_zerothHomotopy (X := Path x x)).mp hpc |>.2
  exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (X := Path x x)
    (x := Path.refl x)).injective (Subsingleton.elim _ _)⟩

end
end Work.Serre

namespace Work.Serre
noncomputable section

end

end Work.Serre
