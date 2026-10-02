import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.landsN_mem_K
import Submission.Work.ELTop.paramRay_disjoint

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

/-! ## Auxiliary combinatorial facts about the angle list of a ray polygon -/

/-- In a strictly increasing list of reals, the first entry is a lower bound for every entry. -/
theorem headD_le_of_pairwise_lt {l : List ℝ} (h : l.Pairwise (· < ·)) {x : ℝ} (hx : x ∈ l) :
    l.headD 0 ≤ x := by
  cases l with
  | nil => simp at hx
  | cons a t =>
    rw [List.headD_cons]
    rcases List.mem_cons.mp hx with rfl | hxt
    · exact le_rfl
    · exact le_of_lt ((List.pairwise_cons.mp h).1 x hxt)

/-- If `a < m < a + 1`, `a ≤ x < a + 1` and `x ≠ m`, then `m` is not congruent to `x` modulo `ℤ`:
`m ≠ x + k` for every integer `k`. -/
theorem ne_add_int_of_fract_ne_zero {a m x : ℝ} (hm₁ : a < m) (hm₂ : m < a + 1)
    (hx₁ : a ≤ x) (hx₂ : x < a + 1) (hne : x ≠ m) (k : ℤ) : m ≠ x + k := by
  have hfrac : Int.fract (x - m) ≠ 0 := by
    intro hz
    rw [Int.fract_eq_zero_iff] at hz
    obtain ⟨z, hz⟩ := hz
    have h1 : (-1 : ℝ) < (z : ℝ) := by rw [hz]; linarith
    have h2 : (z : ℝ) < 1 := by rw [hz]; linarith
    have hz0 : z = 0 := by
      have h1' : (-1 : ℤ) < z := by exact_mod_cast h1
      have h2' : z < (1 : ℤ) := by exact_mod_cast h2
      omega
    have hxz : x = m := by
      have : x - m = 0 := by rw [← hz, hz0]; simp
      linarith
    exact hne hxz
  intro h
  have hf0 : Int.fract (x - m) = 0 := by
    have he : x - m = ((-k : ℤ) : ℝ) := by rw [h]; push_cast; ring
    rw [he, Int.fract_intCast]
  exact hfrac hf0

/-- The midpoint of the near arc following the first pair of an admissible polygon is not
congruent modulo `ℤ` to any of the `2m` angles of the polygon: for every angle `X` of the
flattened angle list and every `k : ℤ`, `midNear ps ≠ X + k`. -/
theorem midNear_ne_angle_add_int {c : ℂ} {φ : ℂ → ℂ} {hN : Work.EL.DynB c φ}
    (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps)
    {X : ℝ} (hX : X ∈ ps.flatMap (fun P => [P.a, P.b])) (k : ℤ) :
    Work.EL.midNear ps ≠ X + k := by
  obtain ⟨P₀, tl, rfl⟩ := List.exists_cons_of_ne_nil hA.ne
  cases tl with
  | nil =>
    have hpw : ([P₀.a, P₀.b] : List ℝ).Pairwise (· < ·) := by
      simpa using hA.cyc.2.1
    have hlt : ∀ x ∈ ([P₀.a, P₀.b] : List ℝ), x < P₀.a + 1 := by
      intro x hx
      have hh := hA.cyc.2.2 x (by simpa using hx)
      simpa using hh
    have hab : P₀.a < P₀.b := (List.pairwise_cons.mp hpw).1 P₀.b (by simp)
    have hb1 : P₀.b < P₀.a + 1 := hlt P₀.b (by simp)
    have hX' : X = P₀.a ∨ X = P₀.b := by simpa using hX
    have hfract : Int.fract (P₀.a + 1 - P₀.b) = P₀.a + 1 - P₀.b :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hmval : Work.EL.midNear [P₀] = (P₀.a + P₀.b + 1) / 2 := by
      rw [Work.EL.midNear.eq_2, hfract]; ring
    have hm_gt : P₀.a < Work.EL.midNear [P₀] := by rw [hmval]; linarith
    have hm_lt : Work.EL.midNear [P₀] < P₀.a + 1 := by rw [hmval]; linarith
    have hXne : X ≠ Work.EL.midNear [P₀] := by
      rcases hX' with rfl | rfl <;> rw [hmval] <;> linarith
    have hx1 : P₀.a ≤ X := by rcases hX' with rfl | rfl <;> linarith
    have hx2 : X < P₀.a + 1 := by rcases hX' with rfl | rfl <;> linarith
    exact ne_add_int_of_fract_ne_zero hm_gt hm_lt hx1 hx2 hXne k
  | cons Q tl' =>
    have hpw : (P₀.a :: P₀.b :: (Q :: tl').flatMap (fun P => [P.a, P.b])).Pairwise (· < ·) := by
      simpa using hA.cyc.2.1
    have hcyc2 : ∀ x ∈ (P₀.a :: P₀.b :: (Q :: tl').flatMap (fun P => [P.a, P.b])),
        x < P₀.a + 1 := by
      intro x hx
      have hh := hA.cyc.2.2 x (by simpa using hx)
      simpa using hh
    have hab : P₀.a < P₀.b := (List.pairwise_cons.mp hpw).1 P₀.b (by simp)
    have hpw2 : ((Q :: tl').flatMap (fun P => [P.a, P.b])).Pairwise (· < ·) :=
      (List.pairwise_cons.mp (List.pairwise_cons.mp hpw).2).2
    have hP0b_lt_Qa : P₀.b < Q.a :=
      (List.pairwise_cons.mp (List.pairwise_cons.mp hpw).2).1 Q.a (by simp)
    have hXl : X ∈ (P₀.a :: P₀.b :: (Q :: tl').flatMap (fun P => [P.a, P.b])) := by
      simpa using hX
    have hQa_lt : Q.a < P₀.a + 1 := hcyc2 Q.a (by simp)
    have hfract : Int.fract (Q.a - P₀.b) = Q.a - P₀.b :=
      Int.fract_eq_self.mpr ⟨by linarith, by linarith⟩
    have hmval : Work.EL.midNear (P₀ :: Q :: tl') = (P₀.b + Q.a) / 2 := by
      rw [Work.EL.midNear.eq_1, hfract]; ring
    have hm_gt : P₀.a < Work.EL.midNear (P₀ :: Q :: tl') := by rw [hmval]; linarith
    have hm_lt : Work.EL.midNear (P₀ :: Q :: tl') < P₀.a + 1 := by rw [hmval]; linarith
    have hXne : X ≠ Work.EL.midNear (P₀ :: Q :: tl') := by
      intro h
      rcases List.mem_cons.mp hXl with h1 | h1
      · rw [h1, hmval] at h; linarith
      · rcases List.mem_cons.mp h1 with h2 | h2
        · rw [h2, hmval] at h; linarith
        · have hQle : Q.a ≤ X := by
            have := headD_le_of_pairwise_lt hpw2 h2
            simpa using this
          rw [hmval] at h; linarith
    have hx1 : P₀.a ≤ X := by
      have := headD_le_of_pairwise_lt hpw hXl
      simpa using this
    have hx2 : X < P₀.a + 1 := hcyc2 X hXl
    exact ne_add_int_of_fract_ne_zero hm_gt hm_lt hx1 hx2 hXne k

/-- The ray point of angle `midNear ps` at any level `t > 1` does not lie on a ray whose angle
occurs among the angles of the polygon. -/
theorem rayPt_midNear_notMem_paramRay {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps) {X t : ℝ}
    (hX : X ∈ ps.flatMap (fun P => [P.a, P.b])) (ht : 1 < t) :
    Work.EL.rayPt hN (Work.EL.midNear ps) t ∉ Work.EL.paramRay hN X := by
  intro hmem
  have hmem' : Work.EL.rayPt hN (Work.EL.midNear ps) t ∈
      Work.EL.paramRay hN (Work.EL.midNear ps) := Work.EL.rayPt_mem_paramRay hN ht
  have hdisj := paramRay_disjoint hN (θ := X) (θ' := Work.EL.midNear ps)
    (fun k => midNear_ne_angle_add_int ps hA hX k)
  exact (Set.disjoint_left.mp hdisj) hmem hmem'

/-- The base point of the region of a ray polygon lies in the region. -/
theorem seed_mem_polyRegion {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (ps : List (Work.EL.CoPair hN)) (hA : Work.EL.PolyAdmissible ps) {R : ℝ} (hR : 1 < R) :
    Work.EL.rayPt hN (Work.EL.midNear ps) (Real.sqrt R) ∈ Work.EL.polyRegion ps R := by
  have h1s : 1 < Real.sqrt R := (Real.lt_sqrt zero_le_one).mpr (by simpa using hR)
  have hsq_ne : Real.sqrt R ≠ R := by
    intro h
    have h2 : 0 < R := by linarith
    have hsq := Real.sq_sqrt (le_of_lt h2)
    nlinarith [hsq, h, hR]
  rw [Work.EL.polyRegion]
  apply mem_connectedComponentIn
  simp only [Set.mem_compl_iff, Work.EL.polyCurve, Set.mem_ofPred_eq, not_or]
  constructor
  · rintro ⟨P, hP, hPy | hPa | hPb⟩
    · have hK : P.y ∈ Work.EL.K c := landsN_mem_K hN P.lands_a
      have hpy : Work.EL.pot hN P.y = 0 := Work.EL.pot_of_mem hN hK
      have hpx : Work.EL.pot hN (Work.EL.rayPt hN (Work.EL.midNear ps) (Real.sqrt R))
          = Real.log (Real.sqrt R) := Work.EL.pot_rayPt hN h1s
      rw [hPy, hpy] at hpx
      exact absurd hpx (ne_of_lt (Real.log_pos h1s))
    · refine rayPt_midNear_notMem_paramRay hN ps hA ?_ h1s
        (Work.Top.NakaneData.rayPiece_subset_paramRay hPa)
      rw [List.mem_flatMap]; exact ⟨P, hP, by simp⟩
    · refine rayPt_midNear_notMem_paramRay hN ps hA ?_ h1s
        (Work.Top.NakaneData.rayPiece_subset_paramRay hPb)
      rw [List.mem_flatMap]; exact ⟨P, hP, by simp⟩
  · rintro ⟨θ, hθ, hfar, hθeq⟩
    have hpx : Work.EL.pot hN (Work.EL.rayPt hN (Work.EL.midNear ps) (Real.sqrt R))
        = Real.log (Real.sqrt R) := Work.EL.pot_rayPt hN h1s
    have hpθ : Work.EL.pot hN (Work.EL.rayPt hN θ R) = Real.log R := Work.EL.pot_rayPt hN hR
    rw [hθeq] at hpx
    have hlog : Real.log (Real.sqrt R) = Real.log R := hpx.symm.trans hpθ
    have h1 : (0 : ℝ) < Real.sqrt R := Real.sqrt_pos.mpr (by linarith)
    have h2 : (0 : ℝ) < R := by linarith
    exact hsq_ne (Real.log_injOn_pos h1 h2 hlog)

end Work.ELTop
