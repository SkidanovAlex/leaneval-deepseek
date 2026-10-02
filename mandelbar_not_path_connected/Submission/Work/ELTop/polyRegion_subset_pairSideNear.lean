/-
# The region of a ray polygon lies on the near side of each of its pairs

`Work.EL.polyRegion ps R` is the bounded side of the ray polygon `polyCurve ps R`, whose
boundary runs through the ray pieces at the `2m` angles of an admissible list `ps` and through
the equipotential arcs of level `R` in the *near* arcs.  This module proves the membership
statement consumed by the EL argument: for every pair `P ∈ ps` the region is contained in the
**near side** `Work.EL.pairSideNear P`, the component of the complement of the pair curve of `P`
reached through the complementary arc `(P.b, P.a + 1)`.

Two ingredients are needed.

* The region lies in the complement of the pair curve of `P`.  The ray pieces of `P` below level
  `R` and the landing point `P.y` are part of `polyCurve`; the remaining points of the pair curve
  are the points of the two rays of `P` at levels above `R`, which carry potential `> log R`, and
  the region lies strictly below the equipotential of level `R` (`polyRegion_subset_pot_lt`).
* The reference point `rayPt (midNear ps) (√R)` of the region lies on the near side of `P`: an
  integer translate of the angle `midNear ps` lies in `(P.b, P.a + 1)`, and every ray point whose
  angle lies in that near arc lies on the near side of `P`.

The conclusion then follows from the maximality of the connected component.
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.seed_mem_polyRegion
import Submission.Work.ELTop.rayPiece_eq_image
import Submission.Work.ELTop.rayPt_add_int
import Submission.Work.ELTop.paramRay_disjoint
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELTop.continuous_rayPt_angle
import Submission.Work.ELTop.exists_midNear_add_int_mem_Ioo
import Submission.Work.ELTop.polyRegion_subset_pot_lt
import Submission.Work.Top.Jordan

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

variable {c : ℂ} {φ : ℂ → ℂ}

/-! ## Elementary helpers -/

/-- In a list of pairs whose flattened angle list is strictly increasing, every pair satisfies
`a < b`. -/
private theorem pair_a_lt_b_of_pairwise {hN : Work.EL.DynB c φ} {ps : List (Work.EL.CoPair hN)}
    (h : (ps.flatMap fun P => [P.a, P.b]).Pairwise (· < ·)) :
    ∀ P ∈ ps, P.a < P.b := by
  induction ps with
  | nil => intro P hP; simp at hP
  | cons Q tl ih =>
    intro P hP
    rw [List.flatMap_cons] at h
    rcases List.mem_cons.mp hP with rfl | hPtl
    · exact (List.pairwise_cons.mp h).1 P.b (by simp)
    · exact ih ((List.pairwise_cons.mp (List.pairwise_cons.mp h).2).2) P hPtl

/-- Every pair of an admissible polygon satisfies `a < b`. -/
private theorem pair_a_lt_b {hN : Work.EL.DynB c φ} {ps : List (Work.EL.CoPair hN)}
    (hA : Work.EL.PolyAdmissible ps) {P : Work.EL.CoPair hN} (hP : P ∈ ps) : P.a < P.b :=
  pair_a_lt_b_of_pairwise (hN := hN) hA.cyc.2.1 P hP

/-- `InArc` depends on the angle only modulo `1`. -/
private theorem inArc_add_int (x : ℝ) (k : ℤ) (a b : ℝ) :
    Work.EL.InArc (x + k) a b ↔ Work.EL.InArc x a b := by
  simp only [Work.EL.InArc, Work.EL.arcLen]
  have h : (x + (k : ℝ)) - a = (x - a) + (k : ℝ) := by ring
  rw [h, Int.fract_add_intCast]

/-- The midpoint of the near arc `(b, a + 1)` of a pair lies in that arc. -/
private theorem nearArc_mid_mem {a b : ℝ} (hab : a < b) (hb1 : b < a + 1) :
    b + Work.EL.arcLen b a / 2 ∈ Set.Ioo b (a + 1) := by
  have hfrac : Work.EL.arcLen b a = a - b + 1 := by
    have h1 : (0 : ℝ) ≤ a - b + 1 := by linarith
    have h2 : a - b + 1 < 1 := by linarith
    have h3 : ∃ z : ℤ, (a - b) - (a - b + 1) = (z : ℝ) := ⟨-1, by push_cast; ring⟩
    unfold Work.EL.arcLen
    exact Int.fract_eq_iff.mpr ⟨h1, h2, h3⟩
  rw [hfrac]
  constructor <;> linarith

/-! ## The near arc of a pair lies on the near side -/

/-- A ray point whose angle lies in the near arc `(P.b, P.a + 1)` of a pair `P` with `a < b`
lies on the near side of `P`. -/
private theorem rayPt_mem_pairSideNear_of_mem_nearArc {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (P : Work.EL.CoPair hN) (hab : P.a < P.b) {θ t : ℝ}
    (hθ : θ ∈ Set.Ioo P.b (P.a + 1)) (ht : 1 < t) :
    Work.EL.rayPt hN θ t ∈ Work.EL.pairSideNear P := by
  have hb1 : P.b < P.a + 1 := lt_trans hθ.1 hθ.2
  set mid : ℝ := P.b + Work.EL.arcLen P.b P.a / 2 with hmid
  have hmid_mem : mid ∈ Set.Ioo P.b (P.a + 1) := nearArc_mid_mem hab hb1
  have hm1 : P.b < mid := hmid_mem.1
  have hm2 : mid < P.a + 1 := hmid_mem.2
  -- an angle of the near arc is congruent to neither `P.a` nor `P.b`
  have hne : ∀ x ∈ Set.Ioo P.b (P.a + 1), (∀ k : ℤ, x ≠ P.a + k) ∧ (∀ k : ℤ, x ≠ P.b + k) := by
    intro x hx
    have hxa : P.b < x := hx.1
    have hxb : x < P.a + 1 := hx.2
    constructor
    · intro k hk
      rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
      · have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
        linarith
      · subst hk0; simp only [Int.cast_zero, add_zero] at hk; linarith
      · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
        linarith
    · intro k hk
      rcases lt_trichotomy k 0 with hk0 | hk0 | hk0
      · have hk1 : (k : ℝ) ≤ -1 := by exact_mod_cast (show k ≤ -1 by omega)
        linarith
      · subst hk0; simp only [Int.cast_zero, add_zero] at hk; linarith
      · have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (show (1 : ℤ) ≤ k by omega)
        linarith
  set S₁ : Set ℂ := (fun s : ℝ => Work.EL.rayPt hN θ s) '' Set.uIcc t 2 with hS₁
  set S₂ : Set ℂ := (fun s : ℝ => Work.EL.rayPt hN s 2) '' Set.uIcc θ mid with hS₂
  have hcont₁ : ContinuousOn (fun s : ℝ => Work.EL.rayPt hN θ s) (Set.uIcc t 2) :=
    (Work.Top.continuousOn_rayPt hN θ).mono (fun s hs => by
      rw [Set.mem_Ioi]
      rcases Set.mem_uIcc.mp hs with ⟨h1, -⟩ | ⟨h1, -⟩
      · linarith
      · linarith)
  have hcont₂ : ContinuousOn (fun s : ℝ => Work.EL.rayPt hN s 2) (Set.uIcc θ mid) :=
    (continuous_rayPt_angle hN (by norm_num : (1 : ℝ) < 2)).continuousOn
  have hpre₁ : IsPreconnected S₁ := IsPreconnected.image isPreconnected_uIcc _ hcont₁
  have hpre₂ : IsPreconnected S₂ := IsPreconnected.image isPreconnected_uIcc _ hcont₂
  have hmem₁₂ : (S₁ ∩ S₂).Nonempty :=
    ⟨Work.EL.rayPt hN θ 2, ⟨2, Set.right_mem_uIcc, rfl⟩, θ, Set.left_mem_uIcc, rfl⟩
  have hconn : IsPreconnected (S₁ ∪ S₂) := IsPreconnected.union' hmem₁₂ hpre₁ hpre₂
  have hsub : S₁ ∪ S₂ ⊆ (Work.EL.pairCurve P)ᶜ := by
    intro z hz
    rw [Set.mem_compl_iff, Work.EL.mem_pairCurve_iff]
    push_neg
    rcases hz with ⟨s, hs, hs_eq⟩ | ⟨s, hs, hs_eq⟩
    · have hs1 : 1 < s := by
        rcases Set.mem_uIcc.mp hs with ⟨h1, -⟩ | ⟨h1, -⟩
        · linarith
        · linarith
      refine ⟨?_, ?_, ?_⟩
      · intro hmem
        exact (Set.disjoint_left.mp (paramRay_disjoint hN (θ := P.a) (θ' := θ)
          (fun k => (hne θ hθ).1 k)) hmem)
          (hs_eq ▸ Work.EL.rayPt_mem_paramRay hN hs1)
      · intro hy
        have h0 : Work.EL.pot hN P.y = 0 :=
          Work.EL.pot_of_mem hN (landsN_mem_K hN P.lands_a)
        have h2 : Work.EL.pot hN z = Real.log s := by
          rw [← hs_eq, Work.EL.pot_rayPt hN hs1]
        rw [hy, h0] at h2
        linarith [Real.log_pos hs1]
      · intro hmem
        exact (Set.disjoint_left.mp (paramRay_disjoint hN (θ := P.b) (θ' := θ)
          (fun k => (hne θ hθ).2 k)) hmem)
          (hs_eq ▸ Work.EL.rayPt_mem_paramRay hN hs1)
    · have hs_mem : s ∈ Set.Ioo P.b (P.a + 1) := by
        rcases Set.mem_uIcc.mp hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨by linarith [hθ.1, h1], by linarith [h2, hm2]⟩
        · exact ⟨by linarith [hm1, h1], by linarith [hθ.2, h2]⟩
      refine ⟨?_, ?_, ?_⟩
      · intro hmem
        exact (Set.disjoint_left.mp (paramRay_disjoint hN (θ := P.a) (θ' := s)
          (fun k => (hne s hs_mem).1 k)) hmem)
          (hs_eq ▸ Work.EL.rayPt_mem_paramRay hN (by norm_num : (1 : ℝ) < 2))
      · intro hy
        have h0 : Work.EL.pot hN P.y = 0 :=
          Work.EL.pot_of_mem hN (landsN_mem_K hN P.lands_a)
        have h2 : Work.EL.pot hN z = Real.log 2 := by
          rw [← hs_eq, Work.EL.pot_rayPt hN (by norm_num : (1 : ℝ) < 2)]
        rw [hy, h0] at h2
        linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
      · intro hmem
        exact (Set.disjoint_left.mp (paramRay_disjoint hN (θ := P.b) (θ' := s)
          (fun k => (hne s hs_mem).2 k)) hmem)
          (hs_eq ▸ Work.EL.rayPt_mem_paramRay hN (by norm_num : (1 : ℝ) < 2))
  have href : Work.EL.rayPt hN (P.b + Work.EL.arcLen P.b P.a / 2) 2 ∈ S₁ ∪ S₂ :=
    Or.inr ⟨mid, Set.right_mem_uIcc, by rw [hmid]⟩
  have hz : Work.EL.rayPt hN θ t ∈ S₁ ∪ S₂ := Or.inl ⟨t, Set.left_mem_uIcc, rfl⟩
  exact hconn.subset_connectedComponentIn href hsub hz

/-! ## The main theorem -/

theorem polyRegion_subset_pairSideNear {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps)
    {R : ℝ} (hR : 1 < R) (hC : Work.Top.IsJordanCurve (Work.EL.polyCurve ps R))
    (P : Work.EL.CoPair hN) (hP : P ∈ ps) :
    Work.EL.polyRegion ps R ⊆ Work.EL.pairSideNear P := by
  classical
  have hseed : Work.EL.rayPt hN (Work.EL.midNear ps) (Real.sqrt R) ∈ Work.EL.polyRegion ps R :=
    seed_mem_polyRegion hN ps hA hR
  have h1sR : 1 < Real.sqrt R := (Real.lt_sqrt zero_le_one).mpr (by simpa using hR)
  have hpot : Work.EL.polyRegion ps R ⊆ {z : ℂ | Work.EL.pot hN z < Real.log R} :=
    polyRegion_subset_pot_lt hN hJ ps hA hR hC
  have hsub : Work.EL.polyRegion ps R ⊆ (Work.EL.pairCurve P)ᶜ := by
    intro z hz
    rw [Set.mem_compl_iff, Work.EL.mem_pairCurve_iff]
    push_neg
    refine ⟨fun hzra => ?_, fun hzy => ?_, fun hzrb => ?_⟩
    · have hzt : z ∈ Work.EL.rayPiece hN P.a 0 R := by
        rw [mem_rayPiece_iff]
        refine ⟨hzra, Work.EL.pot_nonneg hN z, ?_⟩
        by_contra hle
        exact absurd (hpot hz) (not_lt.mpr (le_of_lt (not_le.mp hle)))
      have hzC : z ∈ Work.EL.polyCurve ps R := by
        simp only [Work.EL.polyCurve, Set.mem_ofPred_eq]
        exact Or.inl ⟨P, hP, Or.inr (Or.inl hzt)⟩
      exact (Work.EL.polyRegion_subset_compl (hN := hN) ps R hz) hzC
    · have hzC : z ∈ Work.EL.polyCurve ps R := by
        simp only [Work.EL.polyCurve, Set.mem_ofPred_eq]
        exact Or.inl ⟨P, hP, Or.inl hzy⟩
      exact (Work.EL.polyRegion_subset_compl (hN := hN) ps R hz) hzC
    · have hzt : z ∈ Work.EL.rayPiece hN P.b 0 R := by
        rw [mem_rayPiece_iff]
        refine ⟨hzrb, Work.EL.pot_nonneg hN z, ?_⟩
        by_contra hle
        exact absurd (hpot hz) (not_lt.mpr (le_of_lt (not_le.mp hle)))
      have hzC : z ∈ Work.EL.polyCurve ps R := by
        simp only [Work.EL.polyCurve, Set.mem_ofPred_eq]
        exact Or.inl ⟨P, hP, Or.inr (Or.inr hzt)⟩
      exact (Work.EL.polyRegion_subset_compl (hN := hN) ps R hz) hzC
  have hseedNear : Work.EL.rayPt hN (Work.EL.midNear ps) (Real.sqrt R)
      ∈ Work.EL.pairSideNear P := by
    obtain ⟨k, hk⟩ := exists_midNear_add_int_mem_Ioo hN ps hA P hP
    have hab : P.a < P.b := pair_a_lt_b hA hP
    rw [← rayPt_add_int hN (Work.EL.midNear ps) (Real.sqrt R) k]
    exact rayPt_mem_pairSideNear_of_mem_nearArc hN P hab hk h1sR
  have hcomp := (Work.EL.isPreconnected_polyRegion ps R).subset_connectedComponentIn hseed hsub
  have heq : connectedComponentIn (Work.EL.pairCurve P)ᶜ
      (Work.EL.rayPt hN (Work.EL.midNear ps) (Real.sqrt R)) = Work.EL.pairSideNear P :=
    (connectedComponentIn_eq (F := (Work.EL.pairCurve P)ᶜ) hseedNear).symm
  rwa [heq] at hcomp

end Work.ELTop
