import Mathlib
import Submission.Work.ELPull.Defs
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.pairSides_decomposition

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Set Function Filter
open scoped Topology

/-! **The two-sidedness of a co-landing pair** (in the vocabulary of `Work.ELPull`): for a pair
`P` of rays that co-land at `P.y`, with `arcLen P.a P.b ≠ 0` (the two angles are not congruent
modulo `ℤ`, so that the two sides really are distinct), the two arc sides of the pair curve
`pairCurve hN P` are disjoint and their union is the whole complement of the pair curve.

The proof reduces the pair to its *unwrapped* representative `Q` with `Q.a = P.a` and
`Q.b = P.a + arcLen P.a P.b` (the same pair of rays, but with `Q.a < Q.b < Q.a + 1`), then
transports the pair and its two sides to the `Work.EL` vocabulary, where the two statements
`Work.ELTop.pairSide_disjoint` and `Work.ELTop.pairCurve_compl_eq` are available. -/

noncomputable section

namespace Work.ELPull

namespace ASDU

variable {c : ℂ}


/-! ## 1. The bridge to the `Work.EL` vocabulary -/

theorem dynPhi_EL_eq (c : ℂ) :
    Work.EL.dynPhi c (Work.ParamRays.dynPhi c) = Work.ParamRays.dynPhi c := by
  funext z
  by_cases hz : z ∈ K c
  · rw [Work.EL.dynPhi, ite_eq_left hz, Work.ParamRays.dynPhi_eq_zero_of_mem hz]
  · rw [Work.EL.dynPhi, ite_eq_right hz]

def toEL (hN : DynB c) : Work.EL.DynB c (Work.ParamRays.dynPhi c) where
  e := hN.e
  he := by
    intro x
    rw [Work.EL.dynPhi, ite_eq_right x.2]
    exact hN.he x
  Phi_eq_zero_of_mem := by
    intro z hz
    rw [Work.EL.dynPhi, ite_eq_left hz]
  continuous_potential := by
    rw [dynPhi_EL_eq]
    exact hN.continuous_potential
  tendsto_potential := by
    intro t
    rw [dynPhi_EL_eq]
    exact hN.tendsto_potential t

theorem toEL_rayPt (hN : DynB c) (θ t : ℝ) :
    hN.rayPt θ t = (toEL hN).rayPt θ t := rfl

theorem toEL_LandsN (hN : DynB c) (θ : ℝ) (y : ℂ) :
    LandsN hN θ y ↔ Work.EL.LandsN (toEL hN) θ y := Iff.rfl

theorem toEL_paramRay (hN : DynB c) (θ : ℝ) :
    hN.paramRay θ = (toEL hN).paramRay θ := by
  ext z
  rw [Work.Top.NakaneData.mem_paramRay_iff, Work.Top.NakaneData.mem_paramRay_iff]
  simp only [dynPhi_EL_eq]

def toELCoPair (hN : DynB c) (P : CoPair hN) : Work.EL.CoPair (toEL hN) where
  a := P.a
  b := P.b
  y := P.y
  lands_a := P.lands_a
  lands_b := P.lands_b

theorem toELCoPair_a (hN : DynB c) (P : CoPair hN) : (toELCoPair hN P).a = P.a := rfl
theorem toELCoPair_b (hN : DynB c) (P : CoPair hN) : (toELCoPair hN P).b = P.b := rfl
theorem toELCoPair_y (hN : DynB c) (P : CoPair hN) : (toELCoPair hN P).y = P.y := rfl

theorem toEL_pairCurve (hN : DynB c) (P : CoPair hN) :
    pairCurve hN P = Work.EL.pairCurve (toELCoPair hN P) := by
  simp only [pairCurve, Work.EL.pairCurve, Work.EL.RawPair.curve, toEL_paramRay,
    toELCoPair_a, toELCoPair_b, toELCoPair_y]

theorem toEL_arcSide (hN : DynB c) (P : CoPair hN) (p q : ℝ) :
    arcSide hN P p q =
      Work.EL.pairSideThroughArc (c := c) (φ := Work.ParamRays.dynPhi c) (hN := toEL hN)
        (toELCoPair hN P) p q := by
  simp only [arcSide, Work.EL.pairSideThroughArc, Work.EL.RawPair.sideThrough,
    toEL_pairCurve, toEL_rayPt]
  rfl

/-! ## 2. Elementary arithmetic of the arcs -/

theorem arcLen_self_add (a b : ℝ) : arcLen a (a + arcLen a b) = arcLen a b := by
  rw [arcLen, arcLen]
  rw [show a + Int.fract (b - a) - a = Int.fract (b - a) by ring]
  exact Int.fract_fract (b - a)

theorem lift_eq (a b : ℝ) : b + ((-⌊b - a⌋ : ℤ) : ℝ) = a + arcLen a b := by
  rw [arcLen, Int.fract]
  push_cast
  ring

theorem paramRay_self_add (hN : DynB c) (a b : ℝ) :
    hN.paramRay (a + arcLen a b) = hN.paramRay b := by
  rw [← lift_eq a b]
  exact paramRay_periodic hN b (-⌊b - a⌋)

theorem arcLen_symm {a b : ℝ} (h : arcLen a b ≠ 0) : arcLen b a = 1 - arcLen a b := by
  rw [arcLen, arcLen]
  rw [show a - b = -(b - a) by ring]
  exact Int.fract_neg h

theorem arcLen_pos {a b : ℝ} (h : arcLen a b ≠ 0) : 0 < arcLen a b :=
  lt_of_le_of_ne (Int.fract_nonneg _) (Ne.symm h)

theorem arcLen_lt_one (a b : ℝ) : arcLen a b < 1 := Int.fract_lt_one _

theorem arcLen_ne_zero_of {a b : ℝ} (h : arcLen a b ≠ 0) : arcLen b a ≠ 0 := by
  intro h0
  have h1 := arcLen_symm h
  have h2 := arcLen_lt_one a b
  rw [h0] at h1
  linarith

theorem LandsN_add_int (hN : DynB c) {θ : ℝ} {y : ℂ} (m : ℤ) (h : LandsN hN θ y) :
    LandsN hN (θ + m) y := by
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (rayPt_periodic hN θ t m ht).symm

theorem arcSide_congr (hN : DynB c) (P : CoPair hN) {p q p' q' : ℝ}
    (h : hN.rayPt (p + arcLen p q / 2) 2 = hN.rayPt (p' + arcLen p' q' / 2) 2) :
    arcSide hN P p q = arcSide hN P p' q' := by
  simp only [arcSide, h]

theorem rayPt_unwrap_snd (hN : DynB c) {a b : ℝ} (hab : arcLen a b ≠ 0) :
    hN.rayPt (a + arcLen a b + arcLen (a + arcLen a b) a / 2) 2
      = hN.rayPt (b + arcLen b a / 2) 2 := by
  set L := arcLen a b with hL
  have hLne : L ≠ 0 := hab
  have hself : arcLen a (a + L) = L := by rw [hL]; exact arcLen_self_add a b
  have h1 : arcLen (a + L) a = 1 - L := by
    have h := arcLen_symm (a := a) (b := a + L) (by rw [hself]; exact hLne)
    rwa [hself] at h
  have h2 : arcLen b a = 1 - L := arcLen_symm hab
  have hfloor : (⌊b - a⌋ : ℝ) + L = b - a := by
    rw [hL, arcLen, Int.floor_add_fract]
  have hsign : a + L + (1 - L) / 2 = (b + (1 - L) / 2) + ((-⌊b - a⌋ : ℤ) : ℝ) := by
    push_cast; linarith
  rw [h1, h2, hsign, rayPt_periodic hN (b + (1 - L) / 2) 2 (-⌊b - a⌋) (by norm_num)]

/-! ## 3. Unwrapping a co-landing pair -/

def unwrap (hN : DynB c) (P : CoPair hN) : CoPair hN where
  a := P.a
  b := P.b + ((-⌊P.b - P.a⌋ : ℤ) : ℝ)
  y := P.y
  lands_a := P.lands_a
  lands_b := LandsN_add_int hN (-⌊P.b - P.a⌋) P.lands_b

theorem unwrap_b_eq (hN : DynB c) (P : CoPair hN) :
    (unwrap hN P).b = P.a + arcLen P.a P.b := by
  show P.b + ((-⌊P.b - P.a⌋ : ℤ) : ℝ) = P.a + arcLen P.a P.b
  exact lift_eq P.a P.b

theorem unwrap_pairCurve (hN : DynB c) (P : CoPair hN) :
    pairCurve hN (unwrap hN P) = pairCurve hN P := by
  simp only [pairCurve, unwrap, lift_eq P.a P.b, paramRay_self_add hN P.a P.b]

theorem unwrap_arcSide_fst (hN : DynB c) (P : CoPair hN) :
    arcSide hN (unwrap hN P) (unwrap hN P).a (unwrap hN P).b = arcSide hN P P.a P.b := by
  simp only [arcSide, unwrap, pairCurve, lift_eq P.a P.b, paramRay_self_add hN P.a P.b,
    arcLen_self_add]

theorem unwrap_arcSide_snd (hN : DynB c) (P : CoPair hN) (hab : arcLen P.a P.b ≠ 0) :
    arcSide hN (unwrap hN P) (unwrap hN P).b (unwrap hN P).a = arcSide hN P P.b P.a := by
  have hmid : hN.rayPt ((unwrap hN P).b + arcLen (unwrap hN P).b (unwrap hN P).a / 2) 2
      = hN.rayPt (P.b + arcLen P.b P.a / 2) 2 := by
    show hN.rayPt (P.b + ((-⌊P.b - P.a⌋ : ℤ) : ℝ)
        + arcLen (P.b + ((-⌊P.b - P.a⌋ : ℤ) : ℝ)) P.a / 2) 2
      = hN.rayPt (P.b + arcLen P.b P.a / 2) 2
    rw [lift_eq P.a P.b]
    exact rayPt_unwrap_snd hN hab
  rw [arcSide_congr hN (unwrap hN P) hmid]
  simp only [arcSide, unwrap, pairCurve, lift_eq P.a P.b, paramRay_self_add hN P.a P.b]

/-! ## 4. Assembly (the two `Work.EL` facts as hypotheses) -/

theorem arcSide_disjoint_union_aux (hN : DynB c) (P : CoPair hN)
    (hab : arcLen P.a P.b ≠ 0)
    (hD : ∀ Q : Work.EL.CoPair (toEL hN), Q.a < Q.b → Q.b < Q.a + 1 →
      Disjoint (Work.EL.pairSide (c := c) (φ := Work.ParamRays.dynPhi c) Q)
        (Work.EL.pairSideNear (c := c) (φ := Work.ParamRays.dynPhi c) Q))
    (hU : ∀ Q : Work.EL.CoPair (toEL hN), Q.a < Q.b → Q.b < Q.a + 1 →
      Work.EL.pairSide (c := c) (φ := Work.ParamRays.dynPhi c) Q ∪
        Work.EL.pairSideNear (c := c) (φ := Work.ParamRays.dynPhi c) Q =
        (Work.EL.pairCurve Q)ᶜ) :
    Disjoint (arcSide hN P P.a P.b) (arcSide hN P P.b P.a) ∧
    arcSide hN P P.a P.b ∪ arcSide hN P P.b P.a = (pairCurve hN P)ᶜ := by
  have hLpos : 0 < arcLen P.a P.b := arcLen_pos hab
  have hLlt : arcLen P.a P.b < 1 := arcLen_lt_one _ _
  have hQlt : (unwrap hN P).a < (unwrap hN P).b := by
    rw [show (unwrap hN P).a = P.a from rfl, unwrap_b_eq]; linarith
  have hQ1 : (unwrap hN P).b < (unwrap hN P).a + 1 := by
    rw [show (unwrap hN P).a = P.a from rfl, unwrap_b_eq]; linarith
  refine ⟨?_, ?_⟩
  · rw [← unwrap_arcSide_fst hN P, ← unwrap_arcSide_snd hN P hab]
    rw [toEL_arcSide hN (unwrap hN P) (unwrap hN P).a (unwrap hN P).b]
    rw [toEL_arcSide hN (unwrap hN P) (unwrap hN P).b (unwrap hN P).a]
    have h := hD (toELCoPair hN (unwrap hN P)) hQlt hQ1
    unfold Work.EL.pairSide Work.EL.pairSideNear at h
    exact h
  · rw [← unwrap_arcSide_fst hN P, ← unwrap_arcSide_snd hN P hab]
    rw [toEL_arcSide hN (unwrap hN P) (unwrap hN P).a (unwrap hN P).b]
    rw [toEL_arcSide hN (unwrap hN P) (unwrap hN P).b (unwrap hN P).a]
    rw [← unwrap_pairCurve hN P, toEL_pairCurve hN (unwrap hN P)]
    have h := hU (toELCoPair hN (unwrap hN P)) hQlt hQ1
    unfold Work.EL.pairSide Work.EL.pairSideNear at h
    exact h


end ASDU

open ASDU

theorem arcSide_disjoint_union {c : ℂ} (hN : DynB c) (hJ : Work.Top.JordanForm) (P : CoPair hN)
    (hab : arcLen P.a P.b ≠ 0) :
    Disjoint (arcSide hN P P.a P.b) (arcSide hN P P.b P.a) ∧
    arcSide hN P P.a P.b ∪ arcSide hN P P.b P.a = (pairCurve hN P)ᶜ := by
  exact arcSide_disjoint_union_aux hN P hab
    (fun Q h1 h2 => Work.ELTop.pairSide_disjoint (c := c) (φ := Work.ParamRays.dynPhi c)
      (toEL hN) hJ Q h1 h2)
    (fun Q h1 h2 => (Work.ELTop.pairCurve_compl_eq (c := c) (φ := Work.ParamRays.dynPhi c)
      (toEL hN) Q h1 h2).symm)

end Work.ELPull
