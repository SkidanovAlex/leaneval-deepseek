/-
Copyright: subproject `Submission/Work/LandLeaves/` of `mandelbar_not_path_connected`.

# Cyclic-order preservation of the angle map at a repelling periodic point
-/
import Mathlib
import Submission.Work.LandLeaves.TypeGeometry
import Submission.Work.LandLeaves.Defs
import Submission.Work.LandLeaves.armCrux
import Submission.Work.LandLeaves.ccBet_v2_defs
import Submission.Work.LandLeaves.eq_mod_one_of_rayAccum_of_angDouble_eq
import Submission.Work.ELTop.All
import Submission.Work.ELTop.RigInput
import Submission.Work.TopJordan.Main

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Classical Filter Set
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar)

noncomputable section

variable {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}

/-! ## 0. The bridge from `rayAccum` to `LandsN` -/

theorem landsN_of_rayAccum' {θ : ℝ} (hφ : Work.ParamRays.IsDynBottcher c φ)
    (h : Work.Landing.rayAccum c φ θ = {y}) :
    Work.EL.LandsN (dynBNakane hφ) θ y :=
  (Work.ELTop.landsN_iff_landsAt (dynBNakane hφ) hφ θ y).mpr (landsAt_of_rayAccum hφ h)

/-! ## 1. The angle–side dictionary for a point of a ray -/

theorem paramRay_eq_range' {hN : Work.EL.DynB c φ} (θ : ℝ) :
    Work.EL.paramRay hN θ = (fun t : ℝ => Work.EL.rayPt hN θ t) '' Set.Ioi (1 : ℝ) := by
  change Work.Top.NakaneData.paramRay hN θ =
    (fun t : ℝ => Work.Top.NakaneData.rayPt hN θ t) '' Set.Ioi (1 : ℝ)
  rw [Work.Top.NakaneData.paramRay_eq_range]
  ext z
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t.1, t.2, rfl⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨⟨t, ht⟩, rfl⟩

theorem isPreconnected_paramRay {hN : Work.EL.DynB c φ} (θ : ℝ) :
    IsPreconnected (Work.EL.paramRay hN θ) := by
  rw [paramRay_eq_range' (hN := hN) θ]
  exact isPreconnected_Ioi.image _ (by
    have h := Work.Top.continuousOn_rayPt hN θ
    exact h)

/-- For a normalised co-landing pair the angle–side dictionary holds for *every* angle `θ` and
*every* point `w` of the ray `R_θ` (no landing hypothesis on `θ`). -/
theorem mem_pairSide_iff_ccBet_of_mem_paramRay {hN : Work.EL.DynB c φ} {P : Work.EL.CoPair hN}
    (hab : P.a < P.b) (hb1 : P.b < P.a + 1) {θ : ℝ} {w : ℂ}
    (hw : w ∈ Work.EL.paramRay hN θ) :
    (w ∈ Work.EL.pairSide P ↔ ccBet P.a P.b θ) := by
  have hnd : Work.EL.arcLen P.a P.b ≠ 0 := Work.ELTop.arcLen_ne_zero_of_lt hab hb1
  have hPS : Work.EL.PairSides hN P := Work.ELTop.pairSides hN Work.TopJordan.jordanForm P hnd
  have hdisj : Disjoint (Work.EL.pairSide P) (Work.EL.pairSideNear P) :=
    Work.ELTop.pairSide_disjoint hN Work.TopJordan.jordanForm P hab hb1
  refine ⟨fun hwfar => ?_, fun hcc => ?_⟩
  · have hwcompl : w ∈ (Work.EL.pairCurve P)ᶜ := by
      rw [← hPS.union_eq]
      exact Or.inl hwfar
    by_contra hnc
    have hθa : ∀ m : ℤ, θ ≠ P.a + m := by
      intro m hm
      refine hwcompl ?_
      rw [Work.EL.mem_pairCurve_iff]
      refine Or.inl ?_
      have h2 : w ∈ Work.EL.paramRay hN (P.a + (m : ℝ)) := by rw [← hm]; exact hw
      have h3 : Work.EL.paramRay hN (P.a + (m : ℝ)) = Work.EL.paramRay hN P.a :=
        Work.ELTop.paramRay_add_int hN P.a m
      rwa [h3] at h2
    have hθb : ∀ m : ℤ, θ ≠ P.b + m := by
      intro m hm
      refine hwcompl ?_
      rw [Work.EL.mem_pairCurve_iff]
      refine Or.inr (Or.inr ?_)
      have h2 : w ∈ Work.EL.paramRay hN (P.b + (m : ℝ)) := by rw [← hm]; exact hw
      have h3 : Work.EL.paramRay hN (P.b + (m : ℝ)) = Work.EL.paramRay hN P.b :=
        Work.ELTop.paramRay_add_int hN P.b m
      rwa [h3] at h2
    have hnc2 : Int.fract (θ - P.a) ≠ 0 := fun h0 => by
      obtain ⟨m, hm⟩ := Int.fract_eq_zero_iff.mp h0
      exact hθa m (by linarith)
    have hnc3 : Int.fract (θ - P.b) ≠ 0 := fun h0 => by
      obtain ⟨m, hm⟩ := Int.fract_eq_zero_iff.mp h0
      exact hθb m (by linarith)
    rcases ccBet_or_ccBet_swap hnd hnc2 hnc3 with h | h
    · exact hnc h
    · exfalso
      have hnear : Work.EL.paramRay hN θ ⊆ Work.EL.pairSideNear P :=
        Work.ELTop.paramRay_subset_pairSideNear_of_InArc hN P hab hb1
          (InArc_iff_ccBet.mpr ((ccBet_shift_end (u := P.a) (v := P.b) (w := θ)).mpr h))
      exact (Set.disjoint_left.mp hdisj hwfar) (hnear hw)
  · exact Work.ELTop.paramRay_subset_pairSide_of_InArc hN P hab hb1 (InArc_iff_ccBet.mp hcc) hw


/-! ## 2. The cyclic-order preservation

The crux is `Work.LandLeaves.ccBet_angDouble_shift` (in `Submission/Work/LandLeaves/armCrux.lean`),
which proves the statement for a triple whose *first two* angles are non-integral.  As in
`Work.LandLeaves.armCrux`, the general case is reduced to that one by a cyclic rotation of the
triple: `ccBet` is invariant under cyclic rotation (`ccBet_rot_aux`), and if the first (or the
second) angle of a `ccBet`-triple is an integral multiple of `1` then the other two are not
(`fract_ne_zero_of_ccBet_left`, `fract_ne_zero_of_ccBet_third`, `fract_ne_zero_of_ccBet_third'`).
-/

/-- The cyclic-order preservation of the `2k`-fold angle map at a repelling periodic point
(Goldberg–Milnor, *Fixed points of polynomial maps II*, Lemma 2.2, tricorn form). -/
theorem ccBet_angDouble_typeSet_fresh {c : ℂ} {φ : ℂ → ℂ} {k : ℕ} {y : ℂ}
    (hφ : Work.ParamRays.IsDynBottcher c φ) (hrep : Work.Landing.IsRepelling c k y)
    {a b x : ℝ} (ha : Work.Landing.rayAccum c φ a = {y})
    (hb : Work.Landing.rayAccum c φ b = {y}) (hx : Work.Landing.rayAccum c φ x = {y})
    (hab : Work.LandLeaves.ccBet a b x) :
    Work.LandLeaves.ccBet ((Work.Landing.angDouble)^[2 * k] a)
      ((Work.Landing.angDouble)^[2 * k] b) ((Work.Landing.angDouble)^[2 * k] x) := by
  by_cases haf : Int.fract a = 0
  · -- `a` is integral: rotate so that the two non-integral angles come first
    have hbf : Int.fract b ≠ 0 := Work.LandLeaves.fract_ne_zero_of_ccBet_left hab haf
    have hxf : Int.fract x ≠ 0 := Work.LandLeaves.fract_ne_zero_of_ccBet_third hab haf
    have hrot : Work.LandLeaves.ccBet b x a := Work.LandLeaves.ccBet_rot_aux hab
    have h1 := Work.LandLeaves.ccBet_angDouble_shift hφ hrep hb hx ha hrot hbf hxf
    exact Work.LandLeaves.ccBet_rot_aux (Work.LandLeaves.ccBet_rot_aux h1)
  · by_cases hbf : Int.fract b = 0
    · -- `b` is integral: rotate the other way
      have hxf : Int.fract x ≠ 0 := Work.LandLeaves.fract_ne_zero_of_ccBet_third' hab hbf
      have hrot : Work.LandLeaves.ccBet x a b :=
        Work.LandLeaves.ccBet_rot_aux (Work.LandLeaves.ccBet_rot_aux hab)
      have h1 := Work.LandLeaves.ccBet_angDouble_shift hφ hrep hx ha hb hrot hxf haf
      exact Work.LandLeaves.ccBet_rot_aux h1
    · exact Work.LandLeaves.ccBet_angDouble_shift hφ hrep ha hb hx hab haf hbf
end

end Work.LandLeaves
