import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.paramRay_disjoint
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELTop.continuous_rayPt_angle
import Submission.Work.ELTop.rayPt_add_int
import Submission.Work.Top.continuousOn_rayPt
import Submission.Work.ELTop.mem_pairSideNear_of_nearArc

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELTop

/-!
# `Work.ELTop.paramRay_subset_pairSide`

If the angle `θ` lies in the open cyclic arc `(P.a, P.b)` of a co-landing pair `P`, then the
whole parameter ray `R(θ)` is contained in the *far side* `pairSide P`, the component of the
complement of the pair curve `pairCurve P = R(P.a) ∪ {P.y} ∪ R(P.b)` which contains the
reference ray point `rayPt hN mid 2` at the midpoint `mid = P.a + arcLen P.a P.b / 2` of that
arc.

The proof exhibits an explicit path in the complement of the pair curve joining a point
`rayPt hN θ t` of the ray to the reference point:

* the piece of the ray of angle `θ` between the levels `2` and `t`;
* the equipotential arc of level `2` between the angles `mid` and `θ`.

Both pieces are continuous images of intervals, hence preconnected, and they meet at
`rayPt hN θ 2`.  They avoid the pair curve because rays of different angles are disjoint
(`paramRay_disjoint`) and every angle involved is congruent to neither `P.a` nor `P.b`
modulo `ℤ`, while the landing point `P.y` lies in the filled Julia set `K c`, where the
potential vanishes and the ray points (of level `> 1`) do not.  No Jordan curve theorem is
used.

The angle is normalized by the following observation: `paramRay hN θ` depends on `θ` only
modulo `ℤ` (`Work.ELTop.rayPt_add_int`), so a general angle with `InArc θ P.a P.b` can be
replaced by the lift `P.a + Int.fract (θ - P.a)`, which lies in the honest interval
`(P.a, P.a + arcLen P.a P.b)` where the path above is available.
-/

open Work.EL

/-- Rays are `1`-periodic in the angle: `paramRay hN (θ + k) = paramRay hN θ` for `k : ℤ`. -/
theorem paramRay_add_int {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (θ : ℝ) (k : ℤ) :
    Work.Top.NakaneData.paramRay hN (θ + (k : ℝ)) = Work.Top.NakaneData.paramRay hN θ := by
  ext z
  rw [Work.Top.NakaneData.paramRay_eq_range hN (θ + (k : ℝ)),
    Work.Top.NakaneData.paramRay_eq_range hN θ]
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, (rayPt_add_int hN θ t.1 k).symm⟩
  · rintro ⟨t, rfl⟩
    exact ⟨t, rayPt_add_int hN θ t.1 k⟩

/-- An angle `s` of the honest interval `(a, a + arcLen a b)` is congruent modulo `ℤ` to
neither endpoint `a`, `b` of the cyclic arc. -/
theorem ne_add_int_of_mem_Ioo_fract {a b s : ℝ}
    (hs : s ∈ Set.Ioo a (a + Int.fract (b - a))) :
    (∀ j : ℤ, s ≠ a + (j : ℝ)) ∧ (∀ j : ℤ, s ≠ b + (j : ℝ)) := by
  obtain ⟨h1, h2⟩ := hs
  have hl1 : Int.fract (b - a) < 1 := Int.fract_lt_one (b - a)
  have hfr2 : Int.fract (s - a) = s - a :=
    Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
  constructor
  · intro j hj
    have hsa : s - a = (j : ℝ) := by linarith
    have hfr : Int.fract (s - a) = 0 := by
      rw [hsa]
      simp
    linarith
  · intro j hj
    have hsa : s - a = (b - a) + (j : ℝ) := by linarith
    have hfr : Int.fract (s - a) = Int.fract (b - a) := by rw [hsa, Int.fract_add_intCast]
    linarith

/-- The point `rayPt hN θ t` of a ray whose angle lies in the honest interval
`(P.a, P.a + arcLen P.a P.b)`, at a level `t > 1`, lies in the far side `pairSide P` of the
pair `P`. -/
theorem rayPt_mem_pairSide {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) {θ t : ℝ}
    (hθ1 : P.a < θ) (hθ2 : θ < P.a + Work.EL.arcLen P.a P.b) (ht : 1 < t) :
    Work.EL.rayPt hN θ t ∈ Work.EL.pairSide P := by
  have hl0 : 0 < Work.EL.arcLen P.a P.b := by
    have := Work.EL.arcLen_nonneg P.a P.b
    linarith
  have hmid_lo : P.a < P.a + Work.EL.arcLen P.a P.b / 2 := by linarith
  have hmid_hi : P.a + Work.EL.arcLen P.a P.b / 2 < P.a + Work.EL.arcLen P.a P.b := by linarith
  -- no angle of the arc is congruent to `P.a` or `P.b` modulo `ℤ`
  have hθne : (∀ j : ℤ, θ ≠ P.a + (j : ℝ)) ∧ (∀ j : ℤ, θ ≠ P.b + (j : ℝ)) :=
    ne_add_int_of_mem_Ioo_fract ⟨hθ1, hθ2⟩
  -- the same for the whole closed interval from the midpoint of the arc to `θ`
  have hseg : Set.uIcc (P.a + Work.EL.arcLen P.a P.b / 2) θ ⊆
      Set.Ioo P.a (P.a + Int.fract (P.b - P.a)) := by
    intro s hs
    rcases Set.mem_uIcc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨hmid_lo.trans_le h1, h2.trans_lt hθ2⟩
    · exact ⟨hθ1.trans_le h1, h2.trans_lt hmid_hi⟩
  -- the path: the ray piece of levels `2 … t` together with the equipotential arc of level `2`
  set S : Set ℂ := (fun s : ℝ => Work.EL.rayPt hN θ s) '' Set.uIcc (2 : ℝ) t
      ∪ (fun s : ℝ => Work.EL.rayPt hN s 2) '' Set.uIcc (P.a + Work.EL.arcLen P.a P.b / 2) θ
    with hS_def
  have hcont1 : ContinuousOn (fun s : ℝ => Work.EL.rayPt hN θ s) (Set.uIcc (2 : ℝ) t) :=
    (Work.Top.continuousOn_rayPt hN θ).mono (fun s hs => by
      rw [Set.mem_Ioi]
      rcases Set.mem_uIcc.mp hs with ⟨h2, -⟩ | ⟨ht', -⟩
      · linarith
      · linarith)
  have hcont2 : ContinuousOn (fun s : ℝ => Work.EL.rayPt hN s 2)
      (Set.uIcc (P.a + Work.EL.arcLen P.a P.b / 2) θ) :=
    (continuous_rayPt_angle hN (R := 2) (by norm_num)).continuousOn
  have hpre1 : IsPreconnected ((fun s : ℝ => Work.EL.rayPt hN θ s) '' Set.uIcc (2 : ℝ) t) :=
    (isPreconnected_uIcc (a := (2 : ℝ)) (b := t)).image _ hcont1
  have hpre2 : IsPreconnected ((fun s : ℝ => Work.EL.rayPt hN s 2) ''
      Set.uIcc (P.a + Work.EL.arcLen P.a P.b / 2) θ) :=
    (isPreconnected_uIcc (a := P.a + Work.EL.arcLen P.a P.b / 2) (b := θ)).image _ hcont2
  have hpre : IsPreconnected S := by
    rw [hS_def]
    exact IsPreconnected.union (Work.EL.rayPt hN θ 2)
      ⟨2, Set.left_mem_uIcc, rfl⟩ ⟨θ, Set.right_mem_uIcc, rfl⟩ hpre1 hpre2
  -- the path avoids the pair curve
  have hS_sub : S ⊆ (Work.EL.pairCurve P)ᶜ := by
    intro z hz
    rw [Set.mem_compl_iff, Work.EL.mem_pairCurve_iff]
    simp only [not_or]
    rw [hS_def] at hz
    rcases hz with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
    · -- a point of the ray of angle `θ`, of level `1 < s`
      have hs1 : 1 < s := by
        rcases Set.mem_uIcc.mp hs with ⟨h2, -⟩ | ⟨ht', -⟩
        · linarith
        · linarith
      refine ⟨notMem_paramRay_of_ne_int hN hθne.1 hs1,
        ?_, notMem_paramRay_of_ne_int hN hθne.2 hs1⟩
      intro hzy
      have hzK : P.y ∈ Work.EL.K c := landsN_mem_K hN P.lands_a
      rw [← hzy] at hzK
      exact (Work.EL.paramRay_subset_compl hN θ (Work.EL.rayPt_mem_paramRay hN hs1)) hzK
    · -- a point of the equipotential of level `2`, at an angle of the arc
      obtain ⟨hsA, hsB⟩ := ne_add_int_of_mem_Ioo_fract (hseg hs)
      refine ⟨notMem_paramRay_of_ne_int hN hsA (by norm_num),
        ?_, notMem_paramRay_of_ne_int hN hsB (by norm_num)⟩
      intro hzy
      have hzK : P.y ∈ Work.EL.K c := landsN_mem_K hN P.lands_a
      rw [← hzy] at hzK
      exact (Work.EL.paramRay_subset_compl hN s
        (Work.EL.rayPt_mem_paramRay hN (by norm_num : (1 : ℝ) < 2))) hzK
  -- the reference point and the target point lie on the path
  have hx_mem : Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2 ∈ S := by
    rw [hS_def]
    exact Or.inr ⟨_, Set.left_mem_uIcc, rfl⟩
  have hyt_mem : Work.EL.rayPt hN θ t ∈ S := by
    rw [hS_def]
    exact Or.inl ⟨t, Set.right_mem_uIcc, rfl⟩
  have hmem : Work.EL.rayPt hN θ t ∈ connectedComponentIn (Work.EL.pairCurve P)ᶜ
      (Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2) :=
    IsPreconnected.subset_connectedComponentIn hpre hx_mem hS_sub hyt_mem
  show Work.EL.rayPt hN θ t ∈ connectedComponentIn (Work.EL.pairCurve P)ᶜ
    (Work.EL.rayPt hN (P.a + Work.EL.arcLen P.a P.b / 2) 2)
  exact hmem

/-- A parameter ray whose angle lies in the open cyclic arc `(P.a, P.b)` of a co-landing pair
`P` is contained in the far side `pairSide P`. -/
theorem paramRay_subset_pairSide {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (P : Work.EL.CoPair hN) {θ : ℝ}
    (hθ : Work.EL.InArc θ P.a P.b) : Work.EL.paramRay hN θ ⊆ Work.EL.pairSide P := by
  intro z hz
  obtain ⟨hpos, hlt⟩ := hθ
  -- the ray of angle `θ` is the ray of the lift `P.a + Int.fract (θ - P.a)` of the arc
  have hzN : z ∈ Work.Top.NakaneData.paramRay hN θ := hz
  obtain ⟨k, hk⟩ : ∃ k : ℤ, θ = (P.a + Int.fract (θ - P.a)) + (k : ℝ) := by
    refine ⟨⌊θ - P.a⌋, ?_⟩
    have h := Int.floor_add_fract (θ - P.a)
    linarith
  rw [hk] at hzN
  rw [paramRay_add_int hN (P.a + Int.fract (θ - P.a)) k] at hzN
  rw [Work.Top.NakaneData.paramRay_eq_range hN (P.a + Int.fract (θ - P.a))] at hzN
  obtain ⟨t, ht_eq⟩ := hzN
  rw [← ht_eq]
  exact rayPt_mem_pairSide hN P (by linarith) (by linarith) t.2

end Work.ELTop
