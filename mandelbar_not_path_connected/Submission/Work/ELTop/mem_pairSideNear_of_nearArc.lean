import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.paramRay_disjoint
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELTop.continuous_rayPt_angle
import Submission.Work.Top.continuousOn_rayPt

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
# `Work.ELTop.mem_pairSideNear_of_nearArc`

A ray point at level `t > 1` whose angle `θ` lies in the *near arc* `(P.b, P.a + 1)` of a
co-landing pair `P` (with `P.a < P.b`) belongs to the near side `pairSideNear P`, the component
of the complement of the pair curve `pairCurve P = R(P.a) ∪ {P.y} ∪ R(P.b)` which contains the
reference ray point at the midpoint `P.b + arcLen P.b P.a / 2` of the near arc.

The proof exhibits an explicit path in the complement of the pair curve joining
`rayPt hN θ t` to the reference point:

* the piece of the ray of angle `θ` between the levels `2` and `t`;
* the equipotential arc of level `2` between the angles `mid` and `θ`.

Both pieces are continuous images of intervals, hence preconnected, and they meet at
`rayPt hN θ 2`.  They avoid the pair curve because

* rays of different angles are disjoint (`paramRay_disjoint`) and `θ`, `mid` are congruent to
  neither `P.a` nor `P.b` modulo `ℤ`;
* the ray points have potential `> 0`, while the landing point `P.y` lies in the filled Julia
  set `K c`, where the potential vanishes.

No Jordan curve theorem is used.
-/

open Work.EL

/-! ## Pure real-arithmetic helpers -/

/-- A real number lying strictly between `a` and `a + 1` is not congruent to `a` modulo `ℤ`. -/
theorem unitIoo_ne_add_int {a y : ℝ} (h1 : a < y) (h2 : y < a + 1) (j : ℤ) :
    y ≠ a + (j : ℝ) := by
  intro h
  have hj : (j : ℝ) = y - a := by linarith
  have hj0 : (0 : ℝ) < (j : ℝ) := by rw [hj]; linarith
  have hj1 : (j : ℝ) < 1 := by rw [hj]; linarith
  have hj0' : (0 : ℤ) < j := by exact_mod_cast hj0
  have hj1' : j < (1 : ℤ) := by exact_mod_cast hj1
  omega

/-- For `a < b` and an angle `x` in the near arc `(b, a + 1)`, the angle `x` is not congruent
modulo `ℤ` to either `a` or `b`. -/
theorem nearArc_ne_add_int {a b x : ℝ} (hab : a < b) (hx : x ∈ Set.Ioo b (a + 1)) :
    (∀ j : ℤ, x ≠ a + (j : ℝ)) ∧ (∀ j : ℤ, x ≠ b + (j : ℝ)) := by
  obtain ⟨hxb, hxa⟩ := hx
  refine ⟨fun j => unitIoo_ne_add_int (by linarith) hxa j,
          fun j => unitIoo_ne_add_int hxb (by linarith) j⟩

/-- The midpoint of the near arc of a pair whose angles satisfy `a < b` and `b < a + 1` lies
strictly inside that arc. -/
theorem mid_mem_nearArc {a b : ℝ} (hab : a < b) (hb1 : b < a + 1) :
    b + Work.EL.arcLen b a / 2 ∈ Set.Ioo b (a + 1) := by
  have hf : Int.fract (a - b) = a - b + 1 := by
    rw [Int.fract_eq_iff]
    exact ⟨by linarith, by linarith, ⟨-1, by push_cast; ring⟩⟩
  have harc : Work.EL.arcLen b a = a - b + 1 := hf
  rw [harc]
  constructor <;> linarith

/-- A ray point of angle `x` at a level `> 1` does not lie on the ray of an angle `y` which is
not congruent to `x` modulo `ℤ`. -/
theorem notMem_paramRay_of_ne_int {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) {x y : ℝ}
    (h : ∀ j : ℤ, x ≠ y + (j : ℝ)) {s : ℝ} (hs : 1 < s) :
    Work.EL.rayPt hN x s ∉ Work.EL.paramRay hN y := by
  intro hmem
  exact (Set.disjoint_left.mp (paramRay_disjoint hN h) hmem)
    (Work.EL.rayPt_mem_paramRay hN hs)

/-! ## The main statement -/

theorem mem_pairSideNear_of_nearArc {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) (hab : P.a < P.b) {θ t : ℝ}
    (hθ : θ ∈ Set.Ioo P.b (P.a + 1)) (ht : 1 < t) :
    Work.EL.rayPt hN θ t ∈ Work.EL.pairSideNear P := by
  have hb1 : P.b < P.a + 1 := lt_trans hθ.1 hθ.2
  set mid : ℝ := P.b + Work.EL.arcLen P.b P.a / 2 with hmid_def
  have hmid_mem : mid ∈ Set.Ioo P.b (P.a + 1) := mid_mem_nearArc hab hb1
  -- the two pieces of the path
  set S : Set ℂ := (fun s : ℝ => Work.EL.rayPt hN θ s) '' Set.uIcc (2 : ℝ) t
      ∪ (fun s : ℝ => Work.EL.rayPt hN s 2) '' Set.uIcc mid θ with hS_def
  -- continuity of the two parametrisations
  have hcont1 : ContinuousOn (fun s : ℝ => Work.EL.rayPt hN θ s) (Set.uIcc (2 : ℝ) t) :=
    (Work.Top.continuousOn_rayPt hN θ).mono (fun s hs => by
      rw [Set.mem_Ioi]
      rcases Set.mem_uIcc.mp hs with ⟨h2, -⟩ | ⟨ht', -⟩
      · linarith
      · linarith)
  have hcont2 : ContinuousOn (fun s : ℝ => Work.EL.rayPt hN s 2) (Set.uIcc mid θ) :=
    (continuous_rayPt_angle hN (R := 2) (by norm_num)).continuousOn
  -- the two pieces are preconnected, as continuous images of intervals
  have hpre1 : IsPreconnected ((fun s : ℝ => Work.EL.rayPt hN θ s) '' Set.uIcc (2 : ℝ) t) :=
    (isPreconnected_uIcc (a := (2 : ℝ)) (b := t)).image _ hcont1
  have hpre2 : IsPreconnected ((fun s : ℝ => Work.EL.rayPt hN s 2) '' Set.uIcc mid θ) :=
    (isPreconnected_uIcc (a := mid) (b := θ)).image _ hcont2
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
    · -- `z = rayPt hN θ s` on the ray of angle `θ`
      have hs1 : 1 < s := by
        rcases Set.mem_uIcc.mp hs with ⟨h2, -⟩ | ⟨ht', -⟩
        · linarith
        · linarith
      obtain ⟨hθA, hθB⟩ := nearArc_ne_add_int hab hθ
      refine ⟨notMem_paramRay_of_ne_int hN hθA hs1, ?_, notMem_paramRay_of_ne_int hN hθB hs1⟩
      intro hzy
      have hzK : P.y ∈ Work.EL.K c := landsN_mem_K hN P.lands_a
      rw [← hzy] at hzK
      exact (Work.EL.paramRay_subset_compl hN θ (Work.EL.rayPt_mem_paramRay hN hs1)) hzK
    · -- `z = rayPt hN s 2` on the equipotential of level `2`
      have hs_mem : s ∈ Set.Ioo P.b (P.a + 1) := by
        rcases Set.mem_uIcc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨hmid_mem.1.trans_le h1, h2.trans_lt hθ.2⟩
        · exact ⟨hθ.1.trans_le h1, h2.trans_lt hmid_mem.2⟩
      obtain ⟨hsA, hsB⟩ := nearArc_ne_add_int hab hs_mem
      refine ⟨notMem_paramRay_of_ne_int hN hsA (by norm_num),
        ?_, notMem_paramRay_of_ne_int hN hsB (by norm_num)⟩
      intro hzy
      have hzK : P.y ∈ Work.EL.K c := landsN_mem_K hN P.lands_a
      rw [← hzy] at hzK
      exact (Work.EL.paramRay_subset_compl hN s
        (Work.EL.rayPt_mem_paramRay hN (by norm_num : (1 : ℝ) < 2))) hzK
  -- the reference and the target lie on the path
  have hx_mem : Work.EL.rayPt hN mid 2 ∈ S := by
    rw [hS_def]
    exact Or.inr ⟨mid, Set.left_mem_uIcc, rfl⟩
  have hyt_mem : Work.EL.rayPt hN θ t ∈ S := by
    rw [hS_def]
    exact Or.inl ⟨t, Set.right_mem_uIcc, rfl⟩
  have hmem : Work.EL.rayPt hN θ t ∈
      connectedComponentIn (Work.EL.pairCurve P)ᶜ (Work.EL.rayPt hN mid 2) :=
    IsPreconnected.subset_connectedComponentIn hpre hx_mem hS_sub hyt_mem
  show Work.EL.rayPt hN θ t ∈ connectedComponentIn (Work.EL.pairCurve P)ᶜ
    (Work.EL.rayPt hN (P.b + Work.EL.arcLen P.b P.a / 2) 2)
  exact hmem

end Work.ELTop
