import Mathlib
import Submission.Work.ELPull.pb1_of_notMem
import Submission.Work.ELPull.arcSide_disjoint_union

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.ELPull

open Classical Set Function Filter
open scoped Topology
open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-! ## 0. The Böttcher coordinate carried by `DynB c` -/

theorem dynBottcherExists_of_dynB {c : ℂ} (hN : DynB c) :
    Work.ParamRays.DynBottcherExists c := by
  by_contra hne
  have hphi0 : Work.ParamRays.dynPhi c = fun _ => (0 : ℂ) := by
    funext z
    rw [Work.ParamRays.dynPhi, Work.ParamRays.dynPhiOf, dif_neg hne]
    split <;> rfl
  have h2e : (1 : ℝ) < ‖(2 : ℂ)‖ := by norm_num
  have hz : ((hN.e.symm ⟨(2 : ℂ), by rw [Work.Top.mem_exteriorDisc]; exact h2e⟩ : ↥(K c)ᶜ) : ℂ)
      ∉ K c := (hN.e.symm ⟨(2 : ℂ), by rw [Work.Top.mem_exteriorDisc]; exact h2e⟩).2
  have h1 : Work.ParamRays.dynPhi c
        (((hN.e.symm ⟨(2 : ℂ), by rw [Work.Top.mem_exteriorDisc]; exact h2e⟩ : ↥(K c)ᶜ) : ℂ))
      = ((hN.e ⟨_, hz⟩ : Work.Top.exteriorDisc) : ℂ) := hN.he ⟨_, hz⟩
  have h3 : ((hN.e ⟨_, hz⟩ : Work.Top.exteriorDisc) : ℂ) = 0 := by
    rw [← h1, congrFun hphi0]
  have h4 : (1 : ℝ) < ‖((hN.e ⟨_, hz⟩ : Work.Top.exteriorDisc) : ℂ)‖ := (hN.e ⟨_, hz⟩).2
  rw [h3, norm_zero] at h4
  linarith

theorem isDynBottcher_dynPhiOf_of_dynB' {c : ℂ} (hN : DynB c) :
    Work.ParamRays.IsDynBottcher c (Work.ParamRays.dynPhiOf c) :=
  Work.ParamRays.isDynBottcher_dynPhiOf (dynBottcherExists_of_dynB hN)

/-! ## 1. The pair curve is closed -/

theorem pairCurve_isClosed {c : ℂ} (hN : DynB c) (P : CoPair hN) :
    IsClosed (pairCurve hN P) := by
  have h1 : IsClosed (hN.paramRay P.a ∪ {P.y}) :=
    Work.ELTop.isClosed_paramRay_union_singleton hN P.lands_a
  have h2 : IsClosed (hN.paramRay P.b ∪ {P.y}) :=
    Work.ELTop.isClosed_paramRay_union_singleton hN P.lands_b
  have heq : pairCurve hN P = (hN.paramRay P.a ∪ {P.y}) ∪ (hN.paramRay P.b ∪ {P.y}) := by
    ext z; simp only [pairCurve, Set.mem_union, Set.mem_singleton_iff]; tauto
  rw [heq]; exact h1.union h2

/-! ## 2. The angle-side fact in the general form -/

/-- **The angle-side fact**: a ray whose angle lies in one of the two arcs of a pair lies in the
`arcSide` met by that arc. -/
theorem arcSide_angle {c : ℂ} (hN : DynB c) (P : CoPair hN) (p q θ : ℝ)
    (hpq : (p = P.a ∧ q = P.b) ∨ (p = P.b ∧ q = P.a))
    (hθ : InArc θ p q) : hN.paramRay θ ⊆ arcSide hN P p q := by
  have hnot : ∀ a b : ℝ, InArc θ a b → arcLen a b ≠ 0 := by
    intro a b h h0
    have h2 : Int.fract (θ - a) < arcLen a b := h.2
    rw [h0] at h2
    exact absurd h2 (not_lt.mpr (le_of_lt h.1))
  rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- the far arc `(P.a, P.b)`: lift `P.b`
    have hne : arcLen P.a P.b ≠ 0 := hnot P.a P.b hθ
    have hxZ : ∀ n : ℤ, P.b - P.a ≠ (n : ℝ) := by
      intro n hn
      exact hne (by rw [arcLen, hn, Int.fract_intCast])
    obtain ⟨k, hk1, hk2⟩ : ∃ k : ℤ, P.a < P.b + k ∧ P.b + k < P.a + 1 := by
      refine ⟨⌊P.a - P.b⌋ + 1, ?_, ?_⟩
      · have h := Int.lt_floor_add_one (P.a - P.b); push_cast; linarith
      · have hfl : ⌊P.a - P.b⌋ < P.a - P.b := by
          rw [lt_iff_le_and_ne]
          refine ⟨Int.floor_le _, fun hc => hxZ (-⌊P.a - P.b⌋) ?_⟩
          push_cast; linarith
        push_cast; linarith
    have hL : arcLen P.a (P.b + k) = arcLen P.a P.b := by
      rw [arcLen, arcLen,
        show P.b + (k : ℝ) - P.a = (P.b - P.a) + (k : ℝ) by ring, Int.fract_add_intCast]
    have hθ' : InArc θ P.a (P.b + k) := ⟨hθ.1, by rw [hL]; exact hθ.2⟩
    have h := Work.ELTop.paramRay_subset_pairSide_of_InArc hN
      (⟨⟨P.a, P.b + k, P.y⟩, P.lands_a,
        (landsN_add_int hN P.b k P.y).mpr P.lands_b⟩ : Work.EL.CoPair hN) hk1 hk2 hθ'
    intro z hz
    have hz2 : z ∈ arcSide hN
        (⟨P.a, P.b + k, P.y, P.lands_a,
          (landsN_add_int hN P.b k P.y).mpr P.lands_b⟩ : CoPair hN) P.a (P.b + k) := h hz
    have h1 : arcSide hN
        (⟨P.a, P.b + k, P.y, P.lands_a,
          (landsN_add_int hN P.b k P.y).mpr P.lands_b⟩ : CoPair hN) P.a (P.b + k)
        = arcSide hN P P.a (P.b + k) := by
      simp only [arcSide, pairCurve, paramRay_add_int hN P.b k]
    rw [h1, arcSide_add_int_right hN P P.a P.b k] at hz2
    exact hz2
  · -- the near arc `(P.b, P.a)`: lift `P.a`
    have hne : arcLen P.b P.a ≠ 0 := hnot P.b P.a hθ
    have hxZ : ∀ n : ℤ, P.a - P.b ≠ (n : ℝ) := by
      intro n hn
      exact hne (by rw [arcLen, hn, Int.fract_intCast])
    obtain ⟨m, hm1, hm2⟩ : ∃ m : ℤ, P.b < P.a + m ∧ P.a + m < P.b + 1 := by
      refine ⟨⌊P.b - P.a⌋ + 1, ?_, ?_⟩
      · have h := Int.lt_floor_add_one (P.b - P.a); push_cast; linarith
      · have hfl : ⌊P.b - P.a⌋ < P.b - P.a := by
          rw [lt_iff_le_and_ne]
          refine ⟨Int.floor_le _, fun hc => hxZ (-⌊P.b - P.a⌋) ?_⟩
          push_cast; linarith
        push_cast; linarith
    have hL : arcLen P.b (P.a + m) = arcLen P.b P.a := by
      rw [arcLen, arcLen,
        show P.a + (m : ℝ) - P.b = (P.a - P.b) + (m : ℝ) by ring, Int.fract_add_intCast]
    have hθ' : InArc θ P.b (P.a + m) := ⟨hθ.1, by rw [hL]; exact hθ.2⟩
    have h := Work.ELTop.paramRay_subset_pairSide_of_InArc hN
      (⟨⟨P.b, P.a + m, P.y⟩, P.lands_b,
        (landsN_add_int hN P.a m P.y).mpr P.lands_a⟩ : Work.EL.CoPair hN) hm1 hm2 hθ'
    intro z hz
    have hU : hN.paramRay P.b ∪ {P.y} ∪ hN.paramRay (P.a + m)
        = hN.paramRay P.a ∪ {P.y} ∪ hN.paramRay P.b := by
      rw [paramRay_add_int hN P.a m]; ac_rfl
    have hz1 : z ∈ arcSide hN P P.b (P.a + m) := by
      have hz2 : z ∈ arcSide hN
          (⟨P.b, P.a + m, P.y, P.lands_b,
            (landsN_add_int hN P.a m P.y).mpr P.lands_a⟩ : CoPair hN) P.b (P.a + m) := h hz
      show z ∈ connectedComponentIn (pairCurve hN P)ᶜ
        (hN.rayPt (P.b + arcLen P.b (P.a + m) / 2) 2)
      rw [show pairCurve hN P = hN.paramRay P.b ∪ {P.y} ∪ hN.paramRay (P.a + m) from hU.symm]
      exact hz2
    rw [arcSide_add_int_right hN P P.b P.a m] at hz1
    exact hz1

/-! ## 3. The topological input -/

/-- The plane-topology input of the one-step pull-back, from the Jordan curve theorem. -/
theorem pb1Top_of_jordanForm {c : ℂ} (hN : DynB c) (hJ : Work.Top.JordanForm) :
    PB1Top hN where
  closed := fun P => pairCurve_isClosed hN P
  sep := fun P hab => (arcSide_disjoint_union hN hJ P hab).1
  angle := fun P p q θ hpq _ hθ => arcSide_angle hN P p q θ hpq hθ

/-! ## 4. The one-step pull-back -/

theorem pb1 {c : ℂ} (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) (hN : DynB c)
    (hJ : Work.Top.JordanForm) (Q : CoPair hN) (I : ℝ × ℝ) (hI : IsUnwrappedArcOf Q I)
    (hls : LocallyTwoSided hN Q)
    (hcv : c ∉ arcSide hN Q I.1 I.2) (hy : Q.y ≠ c) (k : Fin 2) :
    ∃ y' : ℂ, LeanEval.ComplexAnalysis.Tantibar c y' = Q.y ∧
      LandsN hN (preArc k I).1 y' ∧ LandsN hN (preArc k I).2 y' := by
  classical
  have hφ := isDynBottcher_dynPhiOf_of_dynB' hN
  by_cases hab : arcLen Q.a Q.b = 0
  · -- degenerate arc: both `preArc` angles coincide
    have hab' : arcLen Q.b Q.a = 0 := by
      rw [arcLen] at hab ⊢
      rw [Int.fract_eq_zero_iff] at hab ⊢
      obtain ⟨m, hm⟩ := hab
      exact ⟨-m, by push_cast; linarith⟩
    have hIeq : I.1 = I.2 := by
      rcases hI with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h1, h2, hab, add_zero]
      · rw [h1, h2, hab', add_zero]
    have hpre : (preArc k I).2 = (preArc k I).1 := by
      show Int.fract (-I.1 / 2 + (k : ℝ) / 2) = Int.fract (-I.2 / 2 + (k : ℝ) / 2)
      rw [hIeq]
    have hT : LandsN hN (T (preArc k I).1) Q.y := by
      rw [T_preArc_fst]
      rcases hI with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h2, hab, add_zero]
        exact (landsN_fract hN Q.a Q.y).mp Q.lands_a
      · rw [h2, hab', add_zero]
        exact (landsN_fract hN Q.b Q.y).mp Q.lands_b
    obtain ⟨y', hy', hl⟩ := landsN_preimage hN hφ hy hT
    exact ⟨y', hy', hl, by rw [hpre]; exact hl⟩
  · exact pb1_of_notMem hc hN hφ (pb1Top_of_jordanForm hN hJ)
      (fun P hab' => (arcSide_disjoint_union hN hJ P hab').2) Q hab I hI hcv hy k

end Work.ELPull
