import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.closure_rayPiece
import Submission.Work.ELTop.rayPiece_eq_image
import Submission.Work.ELTop.continuous_rayPt_angle

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

noncomputable section

namespace Work.ELTop

/-!
# The ray polygon `polyCurve` is closed

`Work.EL.polyCurve ps R` is the union of

* the finitely many ray pieces `rayPiece hN P.a 0 R`, `rayPiece hN P.b 0 R` together with the
  landing points `P.y` of the pairs `P ∈ ps`, and
* the equipotential arc at level `R` over the angles `θ ∈ [0,1]` which lie in none of the
  open cyclic arcs `(P.a, P.b)`.

Each of these is closed: a ray piece together with its landing point is the closure of the
piece (or is empty, when the level `R` is `≤ 1`), and the equipotential part is the image of a
closed subset of the compact interval `[0,1]` under the continuous map `θ ↦ rayPt hN θ R`.
-/

/-- The open cyclic arc `(a, b)` is an open set of angles: it is the union of the open
intervals `(a + j, a + j + arcLen a b)`, `j ∈ ℤ`. -/
theorem isOpen_setOf_InArc (a b : ℝ) : IsOpen {x : ℝ | Work.EL.InArc x a b} := by
  have hLt1 : Work.EL.arcLen a b < 1 := Work.EL.arcLen_lt_one a b
  have hset : {x : ℝ | Work.EL.InArc x a b}
      = ⋃ j : ℤ, Set.Ioo (a + (j : ℝ)) (a + (j : ℝ) + Work.EL.arcLen a b) := by
    ext x
    simp only [Work.EL.InArc, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Ioo]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨⌊x - a⌋, ?_, ?_⟩
      · have hf := Int.floor_add_fract (x - a)
        linarith
      · have hf := Int.floor_add_fract (x - a)
        linarith
    · rintro ⟨j, hj1, hj2⟩
      have hcpos : 0 < x - a - (j : ℝ) := by linarith
      have hclt : x - a - (j : ℝ) < 1 := by linarith
      have hfractc : Int.fract (x - a - (j : ℝ)) = x - a - (j : ℝ) := by
        rw [Int.fract_eq_self]
        exact ⟨le_of_lt hcpos, hclt⟩
      have hfract : Int.fract (x - a) = x - a - (j : ℝ) :=
        (Int.fract_eq_fract.mpr ⟨j, by ring⟩).trans hfractc
      rw [hfract]
      exact ⟨hcpos, by linarith⟩
  rw [hset]
  exact isOpen_iUnion fun _ => isOpen_Ioo

/-- The piece of the ray of angle `β` between the levels `0` and `R` only depends on `|R|`:
the level condition is `0 ≤ pot ≤ log R` and `log R = log |R|`. -/
theorem rayPiece_zero_eq_abs {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (β R : ℝ) :
    Work.EL.rayPiece hN β 0 R = Work.EL.rayPiece hN β 0 |R| := by
  ext z
  rw [mem_rayPiece_iff, mem_rayPiece_iff]
  constructor <;> intro h <;> refine ⟨h.1, h.2.1, ?_⟩
  · rw [Real.log_abs R]; exact h.2.2
  · rw [← Real.log_abs R]; exact h.2.2

/-- The landing point of the ray of angle `β`, together with the ray piece below level `R`,
is a closed set. -/
theorem isClosed_singleton_union_rayPiece {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    {β R : ℝ} {y : ℂ} (h : Work.EL.LandsN hN β y) :
    IsClosed ({y} ∪ Work.EL.rayPiece hN β 0 R) := by
  rcases lt_or_ge (1 : ℝ) |R| with hR | hR
  · rw [rayPiece_zero_eq_abs hN β R, ← closure_rayPiece hN hR h]
    exact isClosed_closure
  · have hempty : Work.EL.rayPiece hN β 0 |R| = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      intro z hz
      rw [mem_rayPiece_iff] at hz
      obtain ⟨hzray, hz0, hzR⟩ := hz
      have hlog : Real.log |R| ≤ 0 := Real.log_nonpos (abs_nonneg R) hR
      have hpot0 : Work.EL.pot hN z = 0 := le_antisymm (by linarith) hz0
      have hzK : z ∈ Work.EL.K c := (Work.EL.pot_eq_zero_iff hN z).mp hpot0
      exact Work.EL.paramRay_subset_compl hN β hzray hzK
    rw [rayPiece_zero_eq_abs hN β R, hempty, Set.union_empty]
    exact isClosed_singleton

/-- The equipotential part of a ray polygon is closed. -/
theorem isClosed_polyCurve_eqArc {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (ps : List (Work.EL.CoPair hN)) (R : ℝ) :
    IsClosed {z : ℂ | ∃ θ ∈ Set.Icc (0 : ℝ) 1,
      (∀ P ∈ ps, ¬ Work.EL.InArc θ P.a P.b) ∧ z = Work.EL.rayPt hN θ R} := by
  have hf : Continuous fun θ : ℝ => Work.EL.rayPt hN θ R := by
    rcases lt_or_ge (1 : ℝ) R with hR | hR
    · exact continuous_rayPt_angle hN hR
    · have hzero : ∀ θ : ℝ, Work.EL.rayPt hN θ R = 0 := by
        intro θ
        show Work.Top.NakaneData.rayPt hN θ R = 0
        rw [Work.Top.NakaneData.rayPt]
        exact dif_neg (not_lt.mpr hR)
      exact continuous_const.congr (fun θ => (hzero θ).symm)
  have hK' : ∀ l : List (Work.EL.CoPair hN),
      IsClosed {θ : ℝ | ∀ P ∈ l, ¬ Work.EL.InArc θ P.a P.b} := by
    intro l
    induction l with
    | nil =>
      have hnil : {θ : ℝ | ∀ P ∈ ([] : List (Work.EL.CoPair hN)),
          ¬ Work.EL.InArc θ P.a P.b} = Set.univ := by
        ext θ; simp
      rw [hnil]; exact isClosed_univ
    | cons P l ih =>
      have hcons : {θ : ℝ | ∀ Q ∈ P :: l, ¬ Work.EL.InArc θ Q.a Q.b}
          = {θ : ℝ | ¬ Work.EL.InArc θ P.a P.b} ∩
            {θ : ℝ | ∀ Q ∈ l, ¬ Work.EL.InArc θ Q.a Q.b} := by
        ext θ; simp only [Set.mem_setOf_eq, Set.mem_inter_iff, List.mem_cons]
        constructor
        · intro h; exact ⟨h P (Or.inl rfl), fun Q hQ => h Q (Or.inr hQ)⟩
        · rintro ⟨h1, h2⟩ Q (rfl | hQ)
          · exact h1
          · exact h2 Q hQ
      rw [hcons]
      exact ((isOpen_setOf_InArc P.a P.b).isClosed_compl).inter ih
  have hEq : {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ P ∈ ps, ¬ Work.EL.InArc θ P.a P.b}
      = Set.Icc (0 : ℝ) 1 ∩ {θ : ℝ | ∀ P ∈ ps, ¬ Work.EL.InArc θ P.a P.b} := by
    ext θ; simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
  have himg : {z : ℂ | ∃ θ ∈ Set.Icc (0 : ℝ) 1,
        (∀ P ∈ ps, ¬ Work.EL.InArc θ P.a P.b) ∧ z = Work.EL.rayPt hN θ R}
      = (fun θ : ℝ => Work.EL.rayPt hN θ R) ''
        {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ P ∈ ps, ¬ Work.EL.InArc θ P.a P.b} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨θ, hθ, hc, rfl⟩
      exact ⟨θ, ⟨hθ, hc⟩, rfl⟩
    · rintro ⟨θ, ⟨hθ, hc⟩, hyz⟩
      exact ⟨θ, hθ, hc, hyz.symm⟩
  rw [himg]
  have hK : IsClosed {θ : ℝ | θ ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ P ∈ ps, ¬ Work.EL.InArc θ P.a P.b} := by
    rw [hEq]
    exact isClosed_Icc.inter (hK' ps)
  exact ((isCompact_Icc.of_isClosed_subset hK Set.inter_subset_left).image hf).isClosed

theorem isClosed_polyCurve {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (ps : List (Work.EL.CoPair hN)) (R : ℝ) : IsClosed (Work.EL.polyCurve ps R) := by
  have hA : IsClosed {z : ℂ | ∃ P ∈ ps,
      z = P.y ∨ z ∈ Work.EL.rayPiece hN P.a 0 R ∨ z ∈ Work.EL.rayPiece hN P.b 0 R} := by
    have hgen : ∀ l : List (Work.EL.CoPair hN),
        IsClosed {z : ℂ | ∃ P ∈ l,
          z = P.y ∨ z ∈ Work.EL.rayPiece hN P.a 0 R ∨ z ∈ Work.EL.rayPiece hN P.b 0 R} := by
      intro l
      induction l with
      | nil =>
        have : {z : ℂ | ∃ P ∈ ([] : List (Work.EL.CoPair hN)),
            z = P.y ∨ z ∈ Work.EL.rayPiece hN P.a 0 R ∨ z ∈ Work.EL.rayPiece hN P.b 0 R}
            = ∅ := by
          ext z; simp
        rw [this]; exact isClosed_empty
      | cons P l ih =>
        have hsplit : {z : ℂ | ∃ Q ∈ P :: l,
              z = Q.y ∨ z ∈ Work.EL.rayPiece hN Q.a 0 R ∨ z ∈ Work.EL.rayPiece hN Q.b 0 R}
            = {z : ℂ | z = P.y ∨ z ∈ Work.EL.rayPiece hN P.a 0 R ∨
                z ∈ Work.EL.rayPiece hN P.b 0 R}
              ∪ {z : ℂ | ∃ Q ∈ l,
                  z = Q.y ∨ z ∈ Work.EL.rayPiece hN Q.a 0 R ∨ z ∈ Work.EL.rayPiece hN Q.b 0 R} := by
          ext z
          simp only [Set.mem_setOf_eq, Set.mem_union, List.mem_cons]
          constructor
          · rintro ⟨Q, (hQ | hQ), h⟩
            · subst hQ; exact Or.inl h
            · exact Or.inr ⟨Q, hQ, h⟩
          · rintro (h | ⟨Q, hQ, h⟩)
            · exact ⟨P, Or.inl rfl, h⟩
            · exact ⟨Q, Or.inr hQ, h⟩
        rw [hsplit]
        refine IsClosed.union ?_ ih
        have hpair : {z : ℂ | z = P.y ∨ z ∈ Work.EL.rayPiece hN P.a 0 R ∨
              z ∈ Work.EL.rayPiece hN P.b 0 R}
            = ({P.y} ∪ Work.EL.rayPiece hN P.a 0 R) ∪
              ({P.y} ∪ Work.EL.rayPiece hN P.b 0 R) := by
          ext z; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]; tauto
        rw [hpair]
        exact (isClosed_singleton_union_rayPiece (hN := hN) P.lands_a).union
          (isClosed_singleton_union_rayPiece (hN := hN) P.lands_b)
    exact hgen ps
  have hE := isClosed_polyCurve_eqArc hN ps R
  have hpoly : Work.EL.polyCurve ps R
      = {z : ℂ | ∃ P ∈ ps,
          z = P.y ∨ z ∈ Work.EL.rayPiece hN P.a 0 R ∨ z ∈ Work.EL.rayPiece hN P.b 0 R}
        ∪ {z : ℂ | ∃ θ ∈ Set.Icc (0 : ℝ) 1,
          (∀ P ∈ ps, ¬ Work.EL.InArc θ P.a P.b) ∧ z = Work.EL.rayPt hN θ R} := by
    ext z
    simp only [Work.EL.polyCurve, Set.mem_setOf_eq, Set.mem_union]
  rw [hpoly]
  exact hA.union hE

end Work.ELTop
