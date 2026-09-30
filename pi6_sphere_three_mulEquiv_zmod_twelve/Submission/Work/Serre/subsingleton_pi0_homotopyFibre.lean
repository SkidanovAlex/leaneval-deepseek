import Submission.Work.Serre.Consumers
import Submission.Work.RatHurewicz.PairFibre
import Submission.Work.StemsB.fibrationLES_of_serre
open scoped Topology Topology.Homotopy unitInterval
open Work.Serre

namespace Work.Serre
noncomputable section

/-- **`π₀` of the homotopy fibre vanishes** when the base is path connected and the fibre has
trivial `π₀` (path lifting along the Serre fibration). -/
theorem subsingleton_pi0_homotopyFibre {X : Type} [TopologicalSpace X] {A : Type}
    [TopologicalSpace A] (i : C(A, X)) (a₀ : A) (hA : ∀ a : A, Joined a₀ a)
    (hF : Subsingleton (HomotopyGroup (Fin 0) (Work.RatHurewicz.fibreOf i a₀)
      (Work.RatHurewicz.fibreOfPt i a₀))) :
    Subsingleton (HomotopyGroup (Fin 0) (Work.RatHurewicz.homotopyFibre i a₀)
      (Work.RatHurewicz.homotopyFibreBasepoint i a₀)) := by
  set E := Work.RatHurewicz.homotopyFibre i a₀ with hEdef
  set p := Work.RatHurewicz.homotopyFibreFst i a₀ with hpdef
  set e₀ := Work.RatHurewicz.homotopyFibreBasepoint i a₀ with he₀def
  -- the fibre over `a₀` is path connected
  have hFpc : PathConnectedSpace (Work.RatHurewicz.fibreOf i a₀) := by
    rw [pathConnectedSpace_iff_zerothHomotopy]
    refine ⟨⟨ZerothHomotopy.mk (Work.RatHurewicz.fibreOfPt i a₀)⟩, ?_⟩
    haveI := hF
    exact (HomotopyGroup.pi0EquivZerothHomotopy (X := Work.RatHurewicz.fibreOf i a₀)
      (x := Work.RatHurewicz.fibreOfPt i a₀)).surjective.subsingleton
  -- path lifting: every point of `E` is joined to the fibre
  have hjoin : ∀ e : E, ∃ f : Work.RatHurewicz.fibreOf i a₀,
      Joined e (Work.StemsB.fibreIncl p (p e₀) f) := by
    intro e
    have hσ : Nonempty (Path (p e) a₀) := (hA (p e)).symm
    obtain ⟨τ⟩ := hσ
    have hconst : (p.comp (ContinuousMap.const (Fin 0 → I) e))
        = ContinuousMap.const (Fin 0 → I) (p e) := ContinuousMap.comp_const p e
    have hhom : (p.comp (ContinuousMap.const (Fin 0 → I) e)).Homotopy
        (ContinuousMap.const (Fin 0 → I) a₀) := by
      rw [hconst]
      exact τ.toHomotopyConst
    obtain ⟨g, H', hH'⟩ := (Work.RatHurewicz.isSerreFibration_homotopyFibreFst i a₀ 0)
      (ContinuousMap.const (Fin 0 → I) e) (ContinuousMap.const (Fin 0 → I) a₀) hhom
    have hlast : p (g default) = a₀ := by
      have := congrFun (congrArg DFunLike.coe hH') (1, default)
      simpa [ContinuousMap.comp_apply, Path.toHomotopyConst] using this
    refine ⟨⟨g default, hlast⟩, ?_⟩
    refine ⟨⟨⟨fun s => H' (s, default), ?_⟩, ?_, ?_⟩⟩
    · fun_prop
    · show H' (0, default) = e
      rw [H'.apply_zero]; rfl
    · show H' (1, default) = g default
      rw [H'.apply_one]
  have hpc : PathConnectedSpace E := by
    refine ⟨⟨e₀⟩, fun x y => ?_⟩
    obtain ⟨fx, hx⟩ := hjoin x
    obtain ⟨fy, hy⟩ := hjoin y
    have hxy : Joined fx fy :=
      (hFpc.joined (Work.RatHurewicz.fibreOfPt i a₀) fx).symm.trans
        (hFpc.joined (Work.RatHurewicz.fibreOfPt i a₀) fy)
    obtain ⟨γxy⟩ := hxy
    have hxy' : Joined (Work.StemsB.fibreIncl p (p e₀) fx)
        (Work.StemsB.fibreIncl p (p e₀) fy) :=
      ⟨γxy.map (Work.StemsB.fibreIncl p (p e₀)).continuous⟩
    exact hx.trans (hxy'.trans hy.symm)
  haveI : PathConnectedSpace E := hpc
  have hZ : Subsingleton (ZerothHomotopy E) :=
    (pathConnectedSpace_iff_zerothHomotopy (X := E)).mp hpc |>.2
  exact ⟨fun a b => (HomotopyGroup.pi0EquivZerothHomotopy (X := E) (x := e₀)).injective
    (hZ.elim _ _)⟩

end
end Work.Serre
