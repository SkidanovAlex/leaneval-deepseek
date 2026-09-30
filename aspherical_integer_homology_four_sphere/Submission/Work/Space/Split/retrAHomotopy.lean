import Mathlib
import Submission.Work.Space.Split
import Submission.Work.Space.Split.retrABasic
import Submission.Work.Space.Split.retrAUnroll
import Submission.Work.Space.Split.retrARetract

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function Filter
open scoped Topology
open unitInterval

namespace Work.Space

/-- The straight-line point of the shell. -/
def raySS (q : I × SS) : SS := ⟨rayPt q.1 q.2.1 q.2.2, sqNorm_rayPt_gt q.1 q.2.1 q.2.2⟩

theorem continuous_raySS : Continuous raySS :=
  Continuous.subtype_mk continuous_rayPtI fun q => sqNorm_rayPt_gt q.1 q.2.1 q.2.2

theorem rayPt_eq_self (s : I) (p : SquarePt) (hp : 1/4 < sqNorm p) (h : sqNorm p = 1) :
    rayPt s p hp = p := by
  apply Subtype.ext
  show rayVal s p = (p : E2)
  rw [rayVal, show rayCoef s p = 1 from by
        rw [rayCoef, h]; ring, one_smul]

end Work.Space

namespace Work.Space.Assembly

variable (a : Assembly)

/-- The straight-line point of the unrolled shell, for a fixed cusp. -/
def rayShellV (v : Cusp) (p : I × (SS × a.Torus v)) : a.ShellY :=
  ⟨v, (raySS (p.1, p.2.1), p.2.2)⟩

theorem continuous_rayShellV (v : Cusp) : Continuous (a.rayShellV v) :=
  continuous_sigmaMk.comp
    ((continuous_raySS.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd))).prodMk
      (continuous_snd.comp continuous_snd))

def rayShell (s : I) (y : a.ShellY) : a.ShellY := a.rayShellV y.1 (s, y.2)

theorem continuous_rayShell : Continuous (fun p : I × a.ShellY => a.rayShell p.1 p.2) := by
  rw [continuous_prod_sigma]
  intro v
  exact a.continuous_rayShellV v

theorem index_rayShell (s : I) (y : a.ShellY) : (a.rayShell s y).1 = y.1 := rfl

theorem rayShell_eq_self {y : a.ShellY} (hy : a.incShell y ∈ a.boundarySet) (s : I) :
    a.rayShell s y = y := by
  obtain ⟨v, ⟨⟨p, hp⟩, t⟩⟩ := y
  have hbsq : sqNorm p = 1 := hy
  have h1 : raySS (s, (⟨p, hp⟩ : SS)) = ⟨p, hp⟩ :=
    Subtype.ext (rayPt_eq_self s p hp hbsq)
  simp only [rayShell, rayShellV]
  rw [h1]

theorem incShell_rayShell_zero (y : a.ShellY) :
    a.incShell (a.rayShell 0 y) = (a.radShell y).1 := by
  obtain ⟨v, ⟨⟨p, hp⟩, t⟩⟩ := y
  rfl

theorem incShell_rayShell_one (y : a.ShellY) :
    a.incShell (a.rayShell 1 y) = a.incShell y := by
  obtain ⟨v, ⟨⟨p, hp⟩, t⟩⟩ := y
  simp only [rayShell, rayShellV, incShell]
  rw [show raySS (1, (⟨p, hp⟩ : SS)) = ⟨p, hp⟩ from Subtype.ext (rayPt_one p hp)]

/-- The unrolled homotopy, on the `M̄` piece. -/
def hpL (p : I × a.Mbar) : {z : a.Mhat // z ∈ a.Aset} :=
  ⟨a.incMbar p.2, a.incMbar_mem_Aset p.2⟩

theorem continuous_hpL : Continuous a.hpL :=
  Continuous.subtype_mk (a.continuous_incMbar.comp continuous_snd)
    fun p => a.incMbar_mem_Aset p.2

/-- The unrolled homotopy, on the shell piece. -/
def hpR (p : I × a.ShellY) : {z : a.Mhat // z ∈ a.Aset} :=
  ⟨a.incY (a.incShell (a.rayShell p.1 p.2)),
    a.incY_mem_Aset_iff.mpr (a.incShell_mem_outer (a.rayShell p.1 p.2))⟩

theorem continuous_hpR : Continuous a.hpR :=
  Continuous.subtype_mk
    ((a.continuous_incY.comp a.continuous_incShell).comp a.continuous_rayShell)
    fun p => a.incY_mem_Aset_iff.mpr (a.incShell_mem_outer (a.rayShell p.1 p.2))

/-- **The unrolled homotopy** `I × U → A`. -/
def hpFun (p : I × a.U) : {z : a.Mhat // z ∈ a.Aset} :=
  match p.2 with
  | Sum.inl m => a.hpL (p.1, m)
  | Sum.inr y => a.hpR (p.1, y)

theorem continuous_hpFun : Continuous a.hpFun := by
  rw [continuous_prod_sum]
  exact ⟨a.continuous_hpL, a.continuous_hpR⟩

theorem hpFun_eq_of_qA_eq (s : I) :
    ∀ y y' : a.U, a.qA y = a.qA y' → a.hpFun (s, y) = a.hpFun (s, y') := by
  intro y y' h
  rcases y with m | y <;> rcases y' with m' | y'
  · have hm : m = m' := a.incMbar_injective (Subtype.ext_iff.mp h)
    rw [hm]
  · obtain ⟨hm, hgl⟩ := a.incMbar_eq_incY_iff.mp (Subtype.ext_iff.mp h)
    have hy : a.incShell y' ∈ a.boundarySet := hgl ▸ (a.glue ⟨m, hm⟩).2
    have hm2 : a.incMbar m = a.incY (a.incShell y') := by
      rw [a.incMbar_eq_incY hm, hgl]
    apply Subtype.ext
    show a.incMbar m = a.incY (a.incShell (a.rayShell s y'))
    rw [a.rayShell_eq_self hy s, hm2]
  · obtain ⟨hm, hgl⟩ := a.incY_eq_incMbar_iff.mp (Subtype.ext_iff.mp h)
    have hy : a.incShell y ∈ a.boundarySet := hgl ▸ (a.glue ⟨m', hm⟩).2
    have hm2 : a.incMbar m' = a.incY (a.incShell y) := by
      rw [a.incMbar_eq_incY hm, hgl]
    apply Subtype.ext
    show a.incY (a.incShell (a.rayShell s y)) = a.incMbar m'
    rw [a.rayShell_eq_self hy s, hm2]
  · have h1 : a.incShell y = a.incShell y' := a.incY_injective (Subtype.ext_iff.mp h)
    rw [a.incShell_injective h1]

/-- The homotopy, descended to `A`. -/
noncomputable def gfun (p : I × {z : a.Mhat // z ∈ a.Aset}) :
    {z : a.Mhat // z ∈ a.Aset} :=
  a.hpFun (p.1, Classical.choose (a.surjective_qA p.2))

theorem gfun_eq_hpFun (s : I) (y : a.U) : a.gfun (s, a.qA y) = a.hpFun (s, y) :=
  a.hpFun_eq_of_qA_eq s _ y (Classical.choose_spec (a.surjective_qA (a.qA y)))

theorem continuous_gfun : Continuous a.gfun :=
  Topology.IsQuotientMap.continuous_lift_prod_right a.isQuotientMap_qA (g := a.gfun) (by
    rw [show (fun p : I × a.U => a.gfun (p.1, a.qA p.2)) = a.hpFun from
      funext fun p => a.gfun_eq_hpFun p.1 p.2]
    exact a.continuous_hpFun)

theorem hpFun_zero (y : a.U) : a.hpFun (0, y) = a.i (a.r (a.qA y)) := by
  rw [show a.r (a.qA y) = a.gFun y from a.r_qA y]
  rcases y with m | y
  · apply Subtype.ext
    show a.incMbar m = a.incMbar m
    rfl
  · apply Subtype.ext
    show a.incY (a.incShell (a.rayShell 0 y)) = a.incMbar ((a.glue.symm (a.radShell y)).1)
    rw [a.incMbar_eq_incY (a.glue.symm (a.radShell y)).2, Homeomorph.apply_symm_apply,
      a.incShell_rayShell_zero y]

theorem hpFun_one (y : a.U) : a.hpFun (1, y) = a.qA y := by
  rcases y with m | y
  · apply Subtype.ext
    show a.incMbar m = a.incMbar m
    rfl
  · apply Subtype.ext
    show a.incY (a.incShell (a.rayShell 1 y)) = a.incY (a.incShell y)
    rw [a.incShell_rayShell_one y]

theorem gfun_zero (z : {z : a.Mhat // z ∈ a.Aset}) : a.gfun (0, z) = a.i (a.r z) := by
  obtain ⟨y, rfl⟩ := a.surjective_qA z
  rw [a.gfun_eq_hpFun 0 y]
  exact a.hpFun_zero y

theorem gfun_one (z : {z : a.Mhat // z ∈ a.Aset}) : a.gfun (1, z) = z := by
  obtain ⟨y, rfl⟩ := a.surjective_qA z
  rw [a.gfun_eq_hpFun 1 y]
  exact a.hpFun_one y

/-- The homotopy as a continuous map. -/
def HCM : C(I × {z : a.Mhat // z ∈ a.Aset}, {z : a.Mhat // z ∈ a.Aset}) :=
  ⟨a.gfun, a.continuous_gfun⟩

theorem retrA_homotopyEquiv_core :
    Nonempty (ContinuousMap.HomotopyEquiv {z : a.Mhat // z ∈ a.Aset} a.Mbar) :=
  ⟨{ toFun := a.r
     invFun := a.i
     left_inv := ⟨{ toContinuousMap := a.HCM
                    map_zero_left := fun z => a.gfun_zero z
                    map_one_left := fun z => a.gfun_one z }⟩
     right_inv := by rw [a.r_comp_i] }⟩

end Work.Space.Assembly
