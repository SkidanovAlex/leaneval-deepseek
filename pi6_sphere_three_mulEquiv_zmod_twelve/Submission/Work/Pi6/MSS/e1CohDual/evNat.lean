import Mathlib
import Submission.Work.Pi6.MSS.e1CohDualDefs
import Submission.Work.Pi6.MSS.e1CohDual.Transport
import Submission.Work.SSSR.kF_eq_of_lift
import Submission.Work.SSSR.jF_eq_grFi
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

open CategoryTheory CategoryTheory.Limits Simplicial Opposite HomologicalComplex
open scoped Simplicial

namespace Work.Pi6.MSS.e1CohDual

noncomputable section

/-- The `next` of `ComplexShape.down ℕ` at `(s+1)+q`. -/
theorem down_next_succ_add (s q : ℕ) :
    (ComplexShape.down ℕ).next ((s + 1) + q) = s + q := by
  rw [Work.Cohomology.down_next]
  omega

/-- The `jF` of the exact couple of the Serre filtration `e1cFilt` is the map on homology induced
by the projection onto the graded piece. -/
theorem jF_e1cFilt (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s q : ℕ) :
    Work.SSSR.jF (Work.Pi6.MSS.e1cFilt 𝕜 p) s q
      = HomologicalComplex.homologyMap (Work.Pi6.MSS.e1cKgπ 𝕜 p s) (s + q) := by
  cases s with
  | zero =>
    show 𝟙 (((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj 0).homology (0 + q))
      = HomologicalComplex.homologyMap (Work.SSSR.grFι 𝕜 (Work.SSS.sSingP p) 0) (0 + q)
    rw [Work.SSSR.grFι_zero]
    exact (HomologicalComplex.homologyMap_id
      ((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj 0) (0 + q)).symm
  | succ k => rfl

/-- The canonical cycle representative of an element of `H_{(s+1)+q}(gr_{s+1})` is a cycle. -/
theorem iCycles_isCycle (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (s q : ℕ)
    (z : (Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).cycles ((s + 1) + q)) :
    (ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).d ((s + 1) + q)
        ((ComplexShape.down ℕ).next ((s + 1) + q))))
      ((ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).iCycles ((s + 1) + q))) z) = 0 := by
  have h := congrArg (fun (f : (Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).cycles ((s + 1) + q) ⟶
      (Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).X ((ComplexShape.down ℕ).next ((s + 1) + q))) => f z)
    (HomologicalComplex.iCycles_d (Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)) ((s + 1) + q)
      ((ComplexShape.down ℕ).next ((s + 1) + q)))
  simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply] using h

/-- **The value of the comparison map on the first differential**, computed from a lift `w` of the
cycle `z` and the corresponding cycle `v` of `F_s`: both sides are `x` evaluated on `v`. -/
theorem e1cEv_d1_apply (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (s q : ℕ)
    (x : ↥(Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 1 s (s + q)))
    (z : (Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).cycles ((s + 1) + q))
    (w : (Work.Pi6.MSS.e1cCc 𝕜 p (s + 2)).X ((s + 1) + q))
    (hw : (ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKgπ 𝕜 p (s + 1)).f ((s + 1) + q))) w
      = (ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).iCycles ((s + 1) + q))) z)
    (v : (Work.Pi6.MSS.e1cCc 𝕜 p (s + 1)).X (s + q))
    (hv : (ModuleCat.Hom.hom ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)) s).f (s + q))) v
      = (ModuleCat.Hom.hom
          (((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj (s + 1)).d ((s + 1) + q) (s + q))) w) :
    Work.Pi6.MSS.e1cEv 𝕜 p s (s + q) x
        ((Work.SSSR.d1 (Work.Pi6.MSS.e1cFilt 𝕜 p) s q)
          (((Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).homologyπ ((s + 1) + q)).hom z))
      = Work.Pi6.MSS.e1cPageCoch 𝕜 p s (s + q) x
          ((Work.Pi6.MSS.e1cIncl 𝕜 p (s + 1)).f (s + q) v) := by
  haveI hmono : Mono (Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)) s) :=
    (Work.Pi6.MSS.e1cFilt 𝕜 p).mono s
  have hz := iCycles_isCycle 𝕜 E B p s q z
  -- `v` is a cycle
  have hvcyc : (ModuleCat.Hom.hom
      (((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj s).d (s + q)
        ((ComplexShape.down ℕ).next (s + q)))) v = 0 := by
    have h2 : (ModuleCat.Hom.hom
        (((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj (s + 1)).d (s + q)
          ((ComplexShape.down ℕ).next (s + q))))
        ((ModuleCat.Hom.hom ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)) s).f (s + q))) v) = 0 := by
      rw [hv]
      have h := congrArg (fun (f : ((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj (s + 1)).X ((s + 1) + q) ⟶
          ((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj (s + 1)).X ((ComplexShape.down ℕ).next (s + q))) =>
            (ModuleCat.Hom.hom f) w)
        (HomologicalComplex.d_comp_d ((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj (s + 1))
          ((s + 1) + q) (s + q) ((ComplexShape.down ℕ).next (s + q)))
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
        LinearMap.zero_apply] using h
    have h3 := Work.SSSR.chainMap_comm_apply_elem
      (Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)) s)
      (i := s + q) (j := (ComplexShape.down ℕ).next (s + q)) v
    have h4 : (ModuleCat.Hom.hom ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)) s).f
        ((ComplexShape.down ℕ).next (s + q))))
        ((ModuleCat.Hom.hom
          (((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj s).d (s + q)
            ((ComplexShape.down ℕ).next (s + q)))) v) = 0 := by
      rw [← h3]
      exact h2
    exact (ModuleCat.mono_iff_injective ((Work.SSSR.incF (Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)) s).f
      ((ComplexShape.down ℕ).next (s + q)))).mp inferInstance (by rw [h4, map_zero])
  -- identify `cyclesMk (iCycles z)` with `z`
  have hz_eq : (Work.SSSR.grF (Work.Pi6.MSS.e1cFilt 𝕜 p).F (s + 1)).cyclesMk
      (((Work.SSSR.grF (Work.Pi6.MSS.e1cFilt 𝕜 p).F (s + 1)).iCycles ((s + 1) + q)).hom z)
      ((ComplexShape.down ℕ).next ((s + 1) + q)) rfl hz = z :=
    cyclesMk_iCycles _ z _ rfl hz
  have hkF := Work.SSSR.kF_eq_of_lift (Work.Pi6.MSS.e1cFilt 𝕜 p) s q
    (((Work.SSSR.grF (Work.Pi6.MSS.e1cFilt 𝕜 p).F (s + 1)).iCycles ((s + 1) + q)).hom z)
    hz w hw v hv hvcyc
  rw [hz_eq] at hkF
  have hkF' : (ModuleCat.Hom.hom (Work.SSSR.kF (Work.Pi6.MSS.e1cFilt 𝕜 p) s q))
      ((ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).homologyπ ((s + 1) + q))) z)
      = (ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cCc 𝕜 p (s + 1)).homologyπ (s + q)))
          (((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj s).cyclesMk v
            ((ComplexShape.down ℕ).next (s + q)) rfl hvcyc) := by
    exact hkF
  -- the first differential, computed
  have hstep1 : (Work.SSSR.d1 (Work.Pi6.MSS.e1cFilt 𝕜 p) s q)
        (((Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).homologyπ ((s + 1) + q)).hom z)
      = (ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKg 𝕜 p s).homologyπ (s + q)))
          (HomologicalComplex.cyclesMap (Work.Pi6.MSS.e1cKgπ 𝕜 p s) (s + q)
            (((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj s).cyclesMk v
              ((ComplexShape.down ℕ).next (s + q)) rfl hvcyc)) := by
    rw [Work.SSSR.d1, jF_e1cFilt 𝕜 E B p s q]
    change (ModuleCat.Hom.hom
        (HomologicalComplex.homologyMap (Work.Pi6.MSS.e1cKgπ 𝕜 p s) (s + q)))
        ((ModuleCat.Hom.hom (Work.SSSR.kF (Work.Pi6.MSS.e1cFilt 𝕜 p) s q))
          ((ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).homologyπ ((s + 1) + q))) z)) = _
    rw [hkF']
    exact homologyMap_homologyπ (Work.Pi6.MSS.e1cKgπ 𝕜 p s) (s + q)
      (((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj s).cyclesMk v
        ((ComplexShape.down ℕ).next (s + q)) rfl hvcyc)
  rw [hstep1, Work.Pi6.MSS.e1cEv_π, Work.Pi6.MSS.e1cEvCyc_apply]
  -- identify the cycle of the graded piece
  have hicy : (ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKg 𝕜 p s).iCycles (s + q)))
      (HomologicalComplex.cyclesMap (Work.Pi6.MSS.e1cKgπ 𝕜 p s) (s + q)
        (((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj s).cyclesMk v
          ((ComplexShape.down ℕ).next (s + q)) rfl hvcyc))
      = (ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKgπ 𝕜 p s).f (s + q))) v := by
    rw [iCycles_cyclesMap]
    exact congrArg (ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKgπ 𝕜 p s).f (s + q)))
      (iCycles_cyclesMk ((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj s) v
        ((ComplexShape.down ℕ).next (s + q)) rfl hvcyc)
  rw [hicy]
  -- replace the section of `e1cKgπ s v` by `v`
  have hkill := Work.Pi6.MSS.e1cKillKernel 𝕜 p s (s + q) x
    (w := (Work.Pi6.MSS.e1cSec 𝕜 p s (s + q)
        ((ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKgπ 𝕜 p s).f (s + q))) v)) - v) (by
      rw [map_sub, Work.Pi6.MSS.e1cSec_apply, sub_self])
  have hsplit : Work.Pi6.MSS.e1cSec 𝕜 p s (s + q)
        ((ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKgπ 𝕜 p s).f (s + q))) v)
      = v + (Work.Pi6.MSS.e1cSec 𝕜 p s (s + q)
          ((ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKgπ 𝕜 p s).f (s + q))) v) - v) := by abel
  rw [hsplit, map_add, map_add, hkill, add_zero]

/-- **The value of the comparison map after applying `pZmap`**, computed from a lift `W` of the
transported cycle: both sides are `x` evaluated on the boundary of `incl W`. -/
theorem e1cEv_pZmap_apply (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (s q : ℕ)
    (x : ↥(Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 1 s (s + q)))
    (z : (Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).cycles ((s + 1) + q))
    (h : (s + 1) + q = s + q + 1)
    (W : (Work.Pi6.MSS.e1cCc 𝕜 p (s + 2)).X (s + q + 1))
    (hW : (ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKgπ 𝕜 p (s + 1)).f (s + q + 1))) W
      = Xcast (Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)) h
          ((ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).iCycles ((s + 1) + q))) z)) :
    Work.Pi6.MSS.e1cEv 𝕜 p (s + 1) (s + q + 1)
        (Work.Pi6.MSS.pZmap 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 1 s (s + q) x)
        (HomCast (Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)) h
          ((ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).homologyπ ((s + 1) + q))) z))
      = Work.Pi6.MSS.e1cPageCoch 𝕜 p s (s + q) x
          ((Work.SSSR.sChains 𝕜 (Work.SSS.sSing E)).d (s + q + 1) (s + q)
            ((Work.Pi6.MSS.e1cIncl 𝕜 p (s + 2)).f (s + q + 1) W)) := by
  rw [HomCast_homologyπ, Work.Pi6.MSS.e1cEv_π, Work.Pi6.MSS.e1cEvCyc_apply]
  rw [iCycles_CycCast]
  -- replace the section of `Xcast h z₀` by `W`
  have hb : ((Work.Pi6.MSS.pZmap 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 1 s (s + q) x :
      (Work.Pi6.MSS.serreCF 𝕜 E B p).C.X (s + q + 1)))
      ∈ (Work.Pi6.MSS.serreCF 𝕜 E B p).F (s + 1) (s + q + 1) :=
    (Work.Pi6.MSS.pZmap 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 1 s (s + q) x).2.1
  have hker : (ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKgπ 𝕜 p (s + 1)).f (s + q + 1)))
      (W - Work.Pi6.MSS.e1cSec 𝕜 p (s + 1) (s + q + 1)
        (Xcast (Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)) h
          ((ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).iCycles ((s + 1) + q))) z))) = 0 := by
    rw [map_sub, hW, Work.Pi6.MSS.e1cSec_apply, sub_self]
  have hkill := Work.Pi6.MSS.e1cKillKernel' 𝕜 p (s + 1) (s + q + 1) hb hker
  have hkill' : Work.Pi6.MSS.e1cPageCoch 𝕜 p (s + 1) (s + q + 1)
      (Work.Pi6.MSS.pZmap 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 1 s (s + q) x)
      ((Work.Pi6.MSS.e1cIncl 𝕜 p (s + 2)).f (s + q + 1)
        (W - Work.Pi6.MSS.e1cSec 𝕜 p (s + 1) (s + q + 1)
          (Xcast (Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)) h
            ((ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).iCycles ((s + 1) + q))) z)))) = 0 :=
    hkill
  have hsplit : Work.Pi6.MSS.e1cSec 𝕜 p (s + 1) (s + q + 1)
        (Xcast (Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)) h
          ((ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).iCycles ((s + 1) + q))) z))
      = W - (W - Work.Pi6.MSS.e1cSec 𝕜 p (s + 1) (s + q + 1)
        (Xcast (Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)) h
          ((ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).iCycles ((s + 1) + q))) z))) := by abel
  rw [hsplit, map_sub, map_sub, hkill', sub_zero]
  -- convert the pairing with `pZmap x` into `x` applied to the boundary
  rw [show Work.Pi6.MSS.e1cPageCoch 𝕜 p (s + 1) (s + q + 1)
          (Work.Pi6.MSS.pZmap 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 1 s (s + q) x)
        = (Work.Pi6.MSS.serreCF 𝕜 E B p).d (s + q)
            (x : (Work.Pi6.MSS.serreCF 𝕜 E B p).C.X (s + q)) from
      pd_pZmap_apply 1 s (s + q) x]
  exact (Work.Pi6.MSS.e1cW_d_apply_applied 𝕜 p (s + q)
    (x : (Work.Pi6.MSS.serreCF 𝕜 E B p).C.X (s + q))
    ((Work.Pi6.MSS.e1cIncl 𝕜 p (s + 2)).f (s + q + 1) W)).symm

/-- The statement of the naturality of the comparison map. -/
theorem evNat (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (s q : ℕ)
    (x : ↥(Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 1 s (s+q)))
    (z : (Work.Pi6.MSS.e1cKg 𝕜 p (s+1)).cycles ((s+1)+q)) :
    Work.Pi6.MSS.e1cEv 𝕜 p s (s+q) x
        (Work.SSSR.d1 (Work.Pi6.MSS.e1cFilt 𝕜 p) s q
          (((Work.Pi6.MSS.e1cKg 𝕜 p (s+1)).homologyπ ((s+1)+q)).hom z))
      = Work.Pi6.MSS.e1cEv 𝕜 p (s+1) (s+q+1)
          (Work.Pi6.MSS.pZmap 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 1 s (s+q) x)
          ((CategoryTheory.eqToHom (congrArg (fun n => (Work.Pi6.MSS.e1cKg 𝕜 p (s+1)).homology n)
            (by omega : (s+1)+q = s+q+1))).hom
            (((Work.Pi6.MSS.e1cKg 𝕜 p (s+1)).homologyπ ((s+1)+q)).hom z)) := by
  have h : (s + 1) + q = s + q + 1 := by omega
  show Work.Pi6.MSS.e1cEv 𝕜 p s (s + q) x
        ((Work.SSSR.d1 (Work.Pi6.MSS.e1cFilt 𝕜 p) s q)
          (((Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).homologyπ ((s + 1) + q)).hom z))
      = Work.Pi6.MSS.e1cEv 𝕜 p (s + 1) (s + q + 1)
          (Work.Pi6.MSS.pZmap 𝕜 (Work.Pi6.MSS.serreCF 𝕜 E B p) 1 s (s + q) x)
          (HomCast (Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)) h
            (((Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).homologyπ ((s + 1) + q)).hom z))
  let z0 : (Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).X ((s + 1) + q) :=
    (ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).iCycles ((s + 1) + q))) z
  -- the lift at the shifted degree
  let X : (Work.Pi6.MSS.e1cCc 𝕜 p (s + 2)).X (s + q + 1) :=
    Work.Pi6.MSS.e1cSec 𝕜 p (s + 1) (s + q + 1)
      (Xcast (Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)) h z0)
  have hW : (ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKgπ 𝕜 p (s + 1)).f (s + q + 1))) X
      = Xcast (Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)) h z0 :=
    Work.Pi6.MSS.e1cSec_apply 𝕜 p (s + 1) (s + q + 1) _
  -- the transported lift
  let Y : ((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj (s + 1)).X ((s + 1) + q) :=
    Xcast ((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj (s + 1)) h.symm
      (show ((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj (s + 1)).X (s + q + 1) from X)
  have hw : (ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKgπ 𝕜 p (s + 1)).f ((s + 1) + q))) Y = z0 := by
    have h1 := map_Xcast (Work.Pi6.MSS.e1cKgπ 𝕜 p (s + 1)) h.symm
      (show ((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj (s + 1)).X (s + q + 1) from X)
    refine h1.trans ?_
    rw [hW]
    exact Xcast_symm (Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)) h z0
  have hz_sq : (ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).d ((s + 1) + q) (s + q)))
      z0 = 0 := by
    rw [← down_next_succ_add s q]
    exact iCycles_isCycle 𝕜 E B p s q z
  have hker : (ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKgπ 𝕜 p (s + 1)).f (s + q)))
      ((ModuleCat.Hom.hom
        (((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj (s + 1)).d ((s + 1) + q) (s + q))) Y) = 0 := by
    have h3 := Work.SSSR.chainMap_comm_apply_elem (Work.Pi6.MSS.e1cKgπ 𝕜 p (s + 1))
      (i := (s + 1) + q) (j := s + q) Y
    have h4 : (ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKg 𝕜 p (s + 1)).d ((s + 1) + q) (s + q)))
        ((ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cKgπ 𝕜 p (s + 1)).f ((s + 1) + q))) Y) = 0 := by
      rw [hw]
      exact hz_sq
    exact h3.symm.trans h4
  obtain ⟨v, hv⟩ := Work.Pi6.MSS.e1cKerπ_range 𝕜 p s (s + q)
    (w := (ModuleCat.Hom.hom
        (((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj (s + 1)).d ((s + 1) + q) (s + q))) Y) hker
  rw [e1cEv_d1_apply 𝕜 E B p s q x z Y hw v hv]
  rw [e1cEv_pZmap_apply 𝕜 E B p s q x z h X hW]
  congr 1
  -- the two chains agree
  rw [← Work.Pi6.MSS.e1cIncl_incF 𝕜 p s (s + q) v, hv]
  have hcd := Xcast_d ((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj (s + 1)) (j := s + q) h.symm
    (show ((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj (s + 1)).X (s + q + 1) from X)
  have hcd' : (ModuleCat.Hom.hom
        (((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj (s + 1)).d ((s + 1) + q) (s + q))) Y
      = (ModuleCat.Hom.hom
        (((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj (s + 1)).d (s + q + 1) (s + q)))
        (show ((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj (s + 1)).X (s + q + 1) from X) :=
    hcd
  exact (congrArg (ModuleCat.Hom.hom ((Work.Pi6.MSS.e1cIncl 𝕜 p (s + 2)).f (s + q))) hcd').trans
    (Work.Pi6.MSS.e1cIncl_d_apply 𝕜 p (s + 2) (s + q)
      (show ((Work.SSSR.serF 𝕜 (Work.SSS.sSingP p)).obj (s + 1)).X (s + q + 1) from X)).symm

end

end Work.Pi6.MSS.e1CohDual
