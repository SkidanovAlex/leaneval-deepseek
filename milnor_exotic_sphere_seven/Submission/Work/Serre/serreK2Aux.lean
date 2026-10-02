import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.Serre.C1Cyl
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.Serre.cylRelPi
import Submission.Work.Serre.cylJoinedIncl
import Submission.Work.RatHurewicz.pair_les
import Submission.Work.RatHurewicz.LESConsequences
import Submission.Work.Stems.mulEquiv_of_homotopyEquiv
import Submission.Work.Stems.Pi
import Submission.Work.Serre.pathConnectedSpace_homotopyFibre
import Submission.Work.Serre.relPi_one_subsingleton
import Submission.Work.Serre.serreAttachKillPi
import Submission.Work.Serre.RangeOne.Comparison
import Submission.Work.Serre.C1CylExplicit
import Submission.Work.RatHurewicz.compressRel_attachCells_range
import Submission.Work.RatHurewicz.CompressRelToRelPi

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Auxiliary lemmas for `Submission/Work/Serre/serreK2Proved.lean`

* `cylRelPi_vanish` — the relative homotopy groups of the mapping-cylinder inclusion vanish in
  degrees `≤ n + 1`, from the `π`-data of the inclusion;
* `subsingleton_pi_cyl_of_subsingleton` — triviality of a homotopy group of `Y` transfers to the
  mapping cylinder of a map into `Y`.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicTopology
open scoped Topology Topology.Homotopy unitInterval

namespace Work.Serre

noncomputable section

set_option maxHeartbeats 1000000

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- **The relative groups of the mapping-cylinder inclusion vanish in degrees `≤ n + 1`** as soon as
`π_m(cylIncl f)` is injective for `m ≤ n` and surjective for `m ≤ n + 1`, together with the
geometric `π₀`-injectivity of the inclusion. -/
theorem cylRelPi_vanish (f : C(X, Y)) (x₀ : X) (n : ℕ)
    (hconn : ∀ x : X, Nonempty (Path (cylIncl f x₀) (cylIncl f x)) → Nonempty (Path x₀ x))
    (hinj : ∀ m : ℕ, m ≤ n →
      Function.Injective (Work.StemsB.πmap (cylIncl f) m x₀))
    (hsurj : ∀ m : ℕ, m ≤ n + 1 →
      Function.Surjective (Work.StemsB.πmap (cylIncl f) m x₀)) :
    ∀ k : ℕ, k ≤ n + 1 → Subsingleton
      (Work.RatHurewicz.RelHomotopyGroup (cylIncl f) x₀ k) := by
  classical
  have hnull : ∃ y : cyl f,
      ((cylIncl f).comp (Work.RatHurewicz.homotopyFibreFst (cylIncl f) x₀)).Homotopic
        (ContinuousMap.const (Work.RatHurewicz.homotopyFibre (cylIncl f) x₀) y) :=
    (cylIncl_comp_homotopyFibreFst_homotopic_const f x₀).imp (fun y hy => hy.symm)
  -- the projection of the homotopy fibre is zero in degrees `≤ n`
  have hfst : ∀ (m : ℕ), m ≤ n → ∀ a : HomotopyGroup (Fin (m + 1))
      (Work.RatHurewicz.homotopyFibre (cylIncl f) x₀)
      (Work.RatHurewicz.homotopyFibreBasepoint (cylIncl f) x₀),
      (Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst (cylIncl f) x₀) m
        (Work.RatHurewicz.homotopyFibreBasepoint (cylIncl f) x₀)) a = 1 := by
    intro m hm a
    have hmain : (Work.StemsB.πmap
        ((cylIncl f).comp (Work.RatHurewicz.homotopyFibreFst (cylIncl f) x₀)) m
        (Work.RatHurewicz.homotopyFibreBasepoint (cylIncl f) x₀)) a = 1 :=
      πmap_eq_one_of_homotopic_const _ m _ hnull a
    have hc : (Work.StemsB.πmap
        ((cylIncl f).comp (Work.RatHurewicz.homotopyFibreFst (cylIncl f) x₀)) m
        (Work.RatHurewicz.homotopyFibreBasepoint (cylIncl f) x₀)) a
        = (Work.StemsB.πmap (cylIncl f) m x₀)
          ((Work.StemsB.πmap (Work.RatHurewicz.homotopyFibreFst (cylIncl f) x₀) m
            (Work.RatHurewicz.homotopyFibreBasepoint (cylIncl f) x₀)) a) :=
      Work.StemsB.πmap_comp_apply (Work.RatHurewicz.homotopyFibreFst (cylIncl f) x₀)
        (cylIncl f) m (Work.RatHurewicz.homotopyFibreBasepoint (cylIncl f) x₀) a
    refine hinj m hm ?_
    rw [← hc]
    exact hmain
  intro k hk
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- `k = 0`: the homotopy fibre is path connected
    subst hk0
    have hpc : PathConnectedSpace (Work.RatHurewicz.homotopyFibre (cylIncl f) x₀) :=
      pathConnectedSpace_homotopyFibre (cylIncl f) x₀ hconn (hsurj 0 (by omega))
    haveI : Subsingleton (ZerothHomotopy (Work.RatHurewicz.homotopyFibre (cylIncl f) x₀)) :=
      (pathConnectedSpace_iff_zerothHomotopy.mp hpc).2
    exact ⟨fun u v => (HomotopyGroup.pi0EquivZerothHomotopy
      (X := Work.RatHurewicz.homotopyFibre (cylIncl f) x₀)
      (x := Work.RatHurewicz.homotopyFibreBasepoint (cylIncl f) x₀)).injective
      (Subsingleton.elim _ _)⟩
  · rcases eq_or_lt_of_le (show 1 ≤ k from hkpos) with hk1 | hk2
    · -- `k = 1`
      subst hk1
      refine subsingleton_pi_one_homotopyFibre (cylIncl f) x₀ (hinj 0 (by omega)) ?_
      exact piMap_fibreIncl_eq_one_of_surjective (cylIncl f) x₀ (hsurj 1 (by omega))
    · -- `k ≥ 2`: the exactness of the pair sequence
      have hk1' : 1 ≤ k := by omega
      obtain ⟨del, d, _h1, _h2, h3, h4⟩ :=
        Work.RatHurewicz.pair_les (cylIncl f) x₀ (k - 1) (by omega)
      have hd : ∀ z : HomotopyGroup (Fin ((k - 1) + 2)) (cyl f) (cylIncl f x₀), d z = 1 :=
        fun z => (h3 z).mpr (hsurj ((k - 1) + 1) (by omega) z)
      have hkey : ∀ y : Work.RatHurewicz.RelHomotopyGroup (cylIncl f) x₀ ((k - 1) + 1),
          y = 1 := by
        intro y
        obtain ⟨z, hz⟩ := (h4 y).mp (hfst (k - 1) (by omega) y)
        rw [← hz, hd z]
      rw [show k = (k - 1) + 1 from (Nat.sub_add_cancel hk1').symm]
      exact ⟨fun y y' => by rw [hkey y, hkey y']⟩

/-- **Triviality of a homotopy group of the target transfers to the mapping cylinder.** -/
theorem subsingleton_pi_cyl_of_subsingleton (f : C(X, Y)) (m : ℕ) (y' : cyl f)
    (h : Subsingleton (HomotopyGroup (Fin (m + 1)) Y (cylRetract f y'))) :
    Subsingleton (HomotopyGroup (Fin (m + 1)) (cyl f) y') := by
  obtain ⟨E, hE⟩ := cylHomotopyEquivExplicit f
  obtain ⟨e⟩ := Work.Stems.mulEquiv_of_homotopyEquiv (N := Fin (m + 1)) E y'
  rw [hE] at e
  exact ⟨fun a b => e.injective (Subsingleton.elim _ _)⟩

/-! ## The inclusion of an attachment is a homology isomorphism below the cell dimension -/

/-- `attachIncl m Y ι f` induces an isomorphism on rational homology in degrees `≤ m`. -/
theorem isIso_ratHomologyMap_attachIncl_aux (m : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere m, Y)) (t : ℕ) (ht : t ≤ m) :
    IsIso (ratHomologyMap (Work.RatHurewicz.attachIncl m Y ι f) t) := by
  have hcomp : ∀ d : ℕ, d ≤ m + 1 → Work.RatHurewicz.CompressRel
      (Work.RatHurewicz.attachCells m Y ι f)
      (Set.range (Work.RatHurewicz.attachIncl m Y ι f)) d :=
    Work.RatHurewicz.compressRel_attachCells_range m Y ι f
  have hiso : IsIso (ratHomologyMap
      (Work.RatHurewicz.setIncl (Set.range (Work.RatHurewicz.attachIncl m Y ι f))) t) :=
    isIso_ratHomologyMap_setIncl_of_compressRel hcomp t (by omega)
  let e := Work.RatHurewicz.rangeHomeo m Y ι f
  let eC : C(Y, ↥(Set.range (Work.RatHurewicz.attachIncl m Y ι f))) := ⟨⇑e, e.continuous⟩
  have hfact : (Work.RatHurewicz.setIncl
        (Set.range (Work.RatHurewicz.attachIncl m Y ι f))).comp eC
      = Work.RatHurewicz.attachIncl m Y ι f := by
    ext y
    rfl
  have hsplit : ratHomologyMap (Work.RatHurewicz.attachIncl m Y ι f) t
      = ratHomologyMap eC t ≫ ratHomologyMap (Work.RatHurewicz.setIncl
          (Set.range (Work.RatHurewicz.attachIncl m Y ι f))) t := by
    rw [← ratHomologyMap_comp eC
      (Work.RatHurewicz.setIncl (Set.range (Work.RatHurewicz.attachIncl m Y ι f))) t, hfact]
  rw [hsplit]
  have hE : IsIso (ratHomologyMap eC t) :=
    IsRatHomologyIso.of_homotopyEquiv e.toHomotopyEquiv t
  have := hiso
  have := hE
  infer_instance

end

end Work.Serre
