import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ELTop.paramRay_subset_pairSide
import Submission.Work.ELTop.pairSides_decomposition
import Submission.Work.Top.mem_paramRay_extAngle
import Submission.Work.ELTop.landsN_mem_K

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Set

noncomputable section

namespace Work.ELTop

variable {c : ℂ} {φ : ℂ → ℂ}

private lemma a_lt_b : (22 / 63 : ℝ) < 25 / 63 := by norm_num
private lemma b_lt_c : (25 / 63 : ℝ) < 37 / 63 := by norm_num
private lemma c_lt_a1 : (37 / 63 : ℝ) < 22 / 63 + 1 := by norm_num
private lemma b_lt_a1 : (25 / 63 : ℝ) < 22 / 63 + 1 := by norm_num
private lemma c_lt_b1 : (37 / 63 : ℝ) < 25 / 63 + 1 := by norm_num
private lemma a1_lt_c1 : (22 / 63 + 1 : ℝ) < 37 / 63 + 1 := by norm_num

private lemma fract_self {x : ℝ} (h1 : 0 ≤ x) (h2 : x < 1) : Int.fract x = x :=
  Int.fract_eq_self.mpr ⟨h1, h2⟩

private lemma arcLen_AB : Work.EL.arcLen (22 / 63 : ℝ) (25 / 63) = 3 / 63 := by
  rw [Work.EL.arcLen, show (25 / 63 : ℝ) - 22 / 63 = 3 / 63 by norm_num]
  exact fract_self (by norm_num) (by norm_num)

private lemma arcLen_BC : Work.EL.arcLen (25 / 63 : ℝ) (37 / 63) = 12 / 63 := by
  rw [Work.EL.arcLen, show (37 / 63 : ℝ) - 25 / 63 = 12 / 63 by norm_num]
  exact fract_self (by norm_num) (by norm_num)

private lemma arcLen_CA : Work.EL.arcLen (37 / 63 : ℝ) (22 / 63 + 1) = 48 / 63 := by
  rw [Work.EL.arcLen, show (22 / 63 + 1 : ℝ) - 37 / 63 = 48 / 63 by norm_num]
  exact fract_self (by norm_num) (by norm_num)

private lemma arcLen_bA : Work.EL.arcLen (25 / 63 : ℝ) (22 / 63 + 1) = 60 / 63 := by
  rw [Work.EL.arcLen, show (22 / 63 + 1 : ℝ) - 25 / 63 = 60 / 63 by norm_num]
  exact fract_self (by norm_num) (by norm_num)

private lemma arcLen_cB : Work.EL.arcLen (37 / 63 : ℝ) (25 / 63 + 1) = 51 / 63 := by
  rw [Work.EL.arcLen, show (25 / 63 + 1 : ℝ) - 37 / 63 = 51 / 63 by norm_num]
  exact fract_self (by norm_num) (by norm_num)

private lemma arcLen_a1c1 : Work.EL.arcLen (22 / 63 + 1 : ℝ) (37 / 63 + 1) = 15 / 63 := by
  rw [Work.EL.arcLen, show (37 / 63 + 1 : ℝ) - (22 / 63 + 1) = 15 / 63 by norm_num]
  exact fract_self (by norm_num) (by norm_num)

private lemma InArc_mem_Ioo_AB {θ : ℝ} (h1 : (22 / 63 : ℝ) < θ) (h2 : θ < 25 / 63) :
    Work.EL.InArc θ (22 / 63) (25 / 63) := by
  have hf : Int.fract (θ - 22 / 63) = θ - 22 / 63 := fract_self (by linarith) (by linarith)
  refine ⟨?_, ?_⟩
  · rw [hf]; linarith
  · rw [hf, arcLen_AB]; linarith

private lemma InArc_mem_Ioo_BC {θ : ℝ} (h1 : (25 / 63 : ℝ) < θ) (h2 : θ < 37 / 63) :
    Work.EL.InArc θ (25 / 63) (37 / 63) := by
  have hf : Int.fract (θ - 25 / 63) = θ - 25 / 63 := fract_self (by linarith) (by linarith)
  refine ⟨?_, ?_⟩
  · rw [hf]; linarith
  · rw [hf, arcLen_BC]; linarith

private lemma InArc_mem_Ioo_CA {θ : ℝ} (h1 : (37 / 63 : ℝ) < θ) (h2 : θ < 1) :
    Work.EL.InArc θ (37 / 63) (22 / 63 + 1) := by
  have hf : Int.fract (θ - 37 / 63) = θ - 37 / 63 := fract_self (by linarith) (by linarith)
  refine ⟨?_, ?_⟩
  · rw [hf]; linarith
  · rw [hf, arcLen_CA]; linarith

private lemma InArc_mem_Ico_0A {θ : ℝ} (h1 : 0 ≤ θ) (h2 : θ < 22 / 63) :
    Work.EL.InArc θ (37 / 63) (22 / 63 + 1) := by
  have hx : 0 ≤ θ - 37 / 63 + 1 ∧ θ - 37 / 63 + 1 < 1 := ⟨by linarith, by linarith⟩
  have hf : Int.fract (θ - 37 / 63) = θ - 37 / 63 + 1 := by
    calc Int.fract (θ - 37 / 63)
        = Int.fract ((θ - 37 / 63 + 1) - ((1 : ℤ) : ℝ)) :=
          congrArg Int.fract (by push_cast; ring)
      _ = Int.fract (θ - 37 / 63 + 1) := Int.fract_sub_intCast _ _
      _ = θ - 37 / 63 + 1 := fract_self hx.1 hx.2
  refine ⟨?_, ?_⟩
  · rw [hf]; linarith
  · rw [hf, arcLen_CA]; linarith

private lemma InArc_c_nearA : Work.EL.InArc (37 / 63 : ℝ) (25 / 63) (22 / 63 + 1) := by
  have hf : Int.fract ((37 : ℝ) / 63 - 25 / 63) = 12 / 63 := by
    rw [show (37 : ℝ) / 63 - 25 / 63 = 12 / 63 by norm_num]
    exact fract_self (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [hf]; norm_num
  · rw [hf, arcLen_bA]; norm_num

private lemma InArc_a_nearB : Work.EL.InArc (22 / 63 : ℝ) (37 / 63) (25 / 63 + 1) := by
  have hf : Int.fract ((22 : ℝ) / 63 - 37 / 63) = 48 / 63 := by
    have h3 : (22 : ℝ) / 63 - 37 / 63 = (48 / 63 : ℝ) + ((-1 : ℤ) : ℝ) := by push_cast; norm_num
    rw [h3, Int.fract_add_intCast]
    exact fract_self (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [hf]; norm_num
  · rw [hf, arcLen_cB]; norm_num

private lemma InArc_b_nearC : Work.EL.InArc (25 / 63 : ℝ) (22 / 63 + 1) (37 / 63 + 1) := by
  have hf : Int.fract ((25 : ℝ) / 63 - (22 / 63 + 1)) = 3 / 63 := by
    have h3 : (25 : ℝ) / 63 - (22 / 63 + 1) = (3 / 63 : ℝ) + ((-1 : ℤ) : ℝ) := by
      push_cast; norm_num
    rw [h3, Int.fract_add_intCast]
    exact fract_self (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · rw [hf]; norm_num
  · rw [hf, arcLen_a1c1]; norm_num

private lemma paramRay_a1 (hN : Work.EL.DynB c φ) :
    Work.EL.paramRay hN (22 / 63 + 1) = Work.EL.paramRay hN (22 / 63) := by
  have h := Work.ELTop.paramRay_add_int hN (22 / 63) 1
  simpa using h

private lemma curve_eq_pairA (hN : Work.EL.DynB c φ) (T : Work.EL.Tripod hN) :
    Work.EL.Tripod.curve T
      = Work.EL.pairCurve (Work.EL.Tripod.pairA T) ∪ Work.EL.paramRay hN (37 / 63) := by
  apply Set.Subset.antisymm
  · intro z hz
    simp only [Work.EL.Tripod.curve, Work.EL.pairCurve, Work.EL.RawPair.curve,
      Work.EL.Tripod.pairA, Set.mem_union, Set.mem_singleton_iff] at hz ⊢
    tauto
  · intro z hz
    simp only [Work.EL.Tripod.curve, Work.EL.pairCurve, Work.EL.RawPair.curve,
      Work.EL.Tripod.pairA, Set.mem_union, Set.mem_singleton_iff] at hz ⊢
    tauto

private lemma curve_eq_pairB (hN : Work.EL.DynB c φ) (T : Work.EL.Tripod hN) :
    Work.EL.Tripod.curve T
      = Work.EL.pairCurve (Work.EL.Tripod.pairB T) ∪ Work.EL.paramRay hN (22 / 63) := by
  apply Set.Subset.antisymm
  · intro z hz
    simp only [Work.EL.Tripod.curve, Work.EL.pairCurve, Work.EL.RawPair.curve,
      Work.EL.Tripod.pairB, Set.mem_union, Set.mem_singleton_iff] at hz ⊢
    tauto
  · intro z hz
    simp only [Work.EL.Tripod.curve, Work.EL.pairCurve, Work.EL.RawPair.curve,
      Work.EL.Tripod.pairB, Set.mem_union, Set.mem_singleton_iff] at hz ⊢
    tauto

private lemma curve_eq_pairC (hN : Work.EL.DynB c φ) (T : Work.EL.Tripod hN) :
    Work.EL.Tripod.curve T
      = Work.EL.pairCurve (Work.EL.Tripod.pairC T) ∪ Work.EL.paramRay hN (25 / 63) := by
  apply Set.Subset.antisymm
  · intro z hz
    simp only [Work.EL.Tripod.curve, Work.EL.pairCurve, Work.EL.RawPair.curve,
      Work.EL.Tripod.pairC, paramRay_a1 hN, Set.mem_union, Set.mem_singleton_iff] at hz ⊢
    tauto
  · intro z hz
    simp only [Work.EL.Tripod.curve, Work.EL.pairCurve, Work.EL.RawPair.curve,
      Work.EL.Tripod.pairC, paramRay_a1 hN, Set.mem_union, Set.mem_singleton_iff] at hz ⊢
    tauto

private lemma isClosed_curve (hN : Work.EL.DynB c φ) (T : Work.EL.Tripod hN) :
    IsClosed (Work.EL.Tripod.curve T) := by
  have h1 : IsClosed (Work.EL.paramRay hN (22 / 63) ∪ {T.y}) :=
    isClosed_paramRay_union_singleton hN T.lands₁
  have h2 : IsClosed (Work.EL.paramRay hN (25 / 63) ∪ {T.y}) :=
    isClosed_paramRay_union_singleton hN T.lands₂
  have h3 : IsClosed (Work.EL.paramRay hN (37 / 63) ∪ {T.y}) :=
    isClosed_paramRay_union_singleton hN T.lands₃
  have heq : Work.EL.Tripod.curve T
      = (Work.EL.paramRay hN (22 / 63) ∪ {T.y}) ∪ (Work.EL.paramRay hN (25 / 63) ∪ {T.y})
        ∪ (Work.EL.paramRay hN (37 / 63) ∪ {T.y}) := by
    apply Set.Subset.antisymm
    · intro z hz
      simp only [Work.EL.Tripod.curve, Set.mem_union, Set.mem_singleton_iff] at hz ⊢
      tauto
    · intro z hz
      simp only [Work.EL.Tripod.curve, Set.mem_union, Set.mem_singleton_iff] at hz ⊢
      tauto
  rw [heq]
  exact (h1.union h2).union h3

private lemma curve_inter_K_subset (hN : Work.EL.DynB c φ) (T : Work.EL.Tripod hN) :
    Work.EL.Tripod.curve T ∩ Work.EL.K c ⊆ {T.y} := by
  rintro z ⟨hzY, hzK⟩
  simp only [Work.EL.Tripod.curve, Set.mem_union, Set.mem_singleton_iff] at hzY
  rcases hzY with ((h | h) | h) | h
  · exact False.elim ((Work.EL.paramRay_subset_compl hN (22 / 63) h) hzK)
  · exact h
  · exact False.elim ((Work.EL.paramRay_subset_compl hN (25 / 63) h) hzK)
  · exact False.elim ((Work.EL.paramRay_subset_compl hN (37 / 63) h) hzK)

private lemma mem_curve_y (hN : Work.EL.DynB c φ) (T : Work.EL.Tripod hN) :
    T.y ∈ Work.EL.Tripod.curve T := by
  simp only [Work.EL.Tripod.curve, Set.mem_union, Set.mem_singleton_iff]
  tauto

private lemma pairCurve_subset_curve (hN : Work.EL.DynB c φ) (T : Work.EL.Tripod hN)
    {X : Work.EL.CoPair hN} (hX : X = T.pairA ∨ X = T.pairB ∨ X = T.pairC) :
    Work.EL.pairCurve X ⊆ Work.EL.Tripod.curve T := by
  rcases hX with rfl | rfl | rfl
  · rw [curve_eq_pairA hN T]; exact subset_union_left
  · rw [curve_eq_pairB hN T]; exact subset_union_left
  · rw [curve_eq_pairC hN T]; exact subset_union_left

private lemma preconnected_subset_arm {hN : Work.EL.DynB c φ} {T : Work.EL.Tripod hN}
    {X : Work.EL.CoPair hN} (hX : X = T.pairA ∨ X = T.pairB ∨ X = T.pairC)
    {S : Set ℂ} (hS : IsPreconnected S) (hSY : S ⊆ (Work.EL.Tripod.curve T)ᶜ)
    {w : ℂ} (hwS : w ∈ S) (hw : w ∈ Work.EL.pairSide X) :
    S ⊆ Work.EL.pairSide X := by
  have hsub : S ⊆ (Work.EL.pairCurve X)ᶜ :=
    fun u hu h => hSY hu (pairCurve_subset_curve hN T hX h)
  have h1 : S ⊆ connectedComponentIn (Work.EL.pairCurve X)ᶜ w :=
    IsPreconnected.subset_connectedComponentIn hS hwS hsub
  have heq : connectedComponentIn (Work.EL.pairCurve X)ᶜ w = Work.EL.pairSide X := by
    rw [← connectedComponentIn_eq (F := (Work.EL.pairCurve X)ᶜ) hw]
    exact rfl
  rwa [heq] at h1

theorem tripodArms_cover {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ)
    (hJ : Work.Top.JordanForm) (T : Work.EL.Tripod hN) :
    Work.EL.Tripod.armA T ∪ Work.EL.Tripod.armB T ∪ Work.EL.Tripod.armC T =
      (Work.EL.Tripod.curve T)ᶜ := by
  classical
  refine Set.Subset.antisymm ?_ ?_
  · intro z hz
    rw [Set.mem_compl_iff]
    rcases hz with (hzA | hzB) | hzC
    · rw [curve_eq_pairA hN T]
      rintro (h | h)
      · exact (connectedComponentIn_subset ((Work.EL.pairCurve (T.pairA))ᶜ) _ hzA) h
      · exact (Set.disjoint_left.mp (pairSide_disjoint hN hJ (T.pairA) a_lt_b b_lt_a1) hzA)
          (paramRay_subset_pairSideNear_of_InArc hN (T.pairA) a_lt_b b_lt_a1 InArc_c_nearA h)
    · rw [curve_eq_pairB hN T]
      rintro (h | h)
      · exact (connectedComponentIn_subset ((Work.EL.pairCurve (T.pairB))ᶜ) _ hzB) h
      · exact (Set.disjoint_left.mp (pairSide_disjoint hN hJ (T.pairB) b_lt_c c_lt_b1) hzB)
          (paramRay_subset_pairSideNear_of_InArc hN (T.pairB) b_lt_c c_lt_b1 InArc_a_nearB h)
    · rw [curve_eq_pairC hN T]
      rintro (h | h)
      · exact (connectedComponentIn_subset ((Work.EL.pairCurve (T.pairC))ᶜ) _ hzC) h
      · exact (Set.disjoint_left.mp (pairSide_disjoint hN hJ (T.pairC) c_lt_a1 a1_lt_c1) hzC)
          (paramRay_subset_pairSideNear_of_InArc hN (T.pairC) c_lt_a1 a1_lt_c1 InArc_b_nearC h)
  · intro z hz
    set D : Set ℂ := connectedComponentIn (Work.EL.Tripod.curve T)ᶜ z with hDdef
    have hzD : z ∈ D := mem_connectedComponentIn hz
    have hDsub : D ⊆ (Work.EL.Tripod.curve T)ᶜ := connectedComponentIn_subset _ _
    have hDpre : IsPreconnected D := isPreconnected_connectedComponentIn
    by_cases hoff : ∃ w ∈ D, w ∉ Work.EL.K c
    · obtain ⟨w, hwD, hwK⟩ := hoff
      set θ : ℝ := Work.Top.NakaneData.extAngle (Work.EL.dynPhi c φ) w with hθdef
      have hθIco : θ ∈ Set.Ico (0 : ℝ) 1 := Work.Top.NakaneData.extAngle_mem_Ico _ _
      have hθ0 : 0 ≤ θ := hθIco.1
      have hθ1 : θ < 1 := hθIco.2
      have hwray : w ∈ Work.EL.paramRay hN θ :=
        Work.Top.mem_paramRay_extAngle (Mb := Work.EL.K c) (Φ := Work.EL.dynPhi c φ) hN hwK
      have hneA : θ ≠ 22 / 63 := by
        intro heq
        have heq' : θ = (T.pairA).a := heq
        refine hDsub hwD ?_
        rw [curve_eq_pairA hN T]
        refine Or.inl ?_
        rw [Work.EL.mem_pairCurve_iff]
        exact Or.inl (heq' ▸ hwray)
      have hneB : θ ≠ 25 / 63 := by
        intro heq
        have heq' : θ = (T.pairB).a := heq
        refine hDsub hwD ?_
        rw [curve_eq_pairB hN T]
        refine Or.inl ?_
        rw [Work.EL.mem_pairCurve_iff]
        exact Or.inl (heq' ▸ hwray)
      have hneC : θ ≠ 37 / 63 := by
        intro heq
        have heq' : θ = (T.pairC).a := heq
        refine hDsub hwD ?_
        rw [curve_eq_pairC hN T]
        refine Or.inl ?_
        rw [Work.EL.mem_pairCurve_iff]
        exact Or.inl (heq' ▸ hwray)
      have harm : w ∈ Work.EL.Tripod.armA T ∪ Work.EL.Tripod.armB T ∪ Work.EL.Tripod.armC T := by
        rcases lt_trichotomy θ (22 / 63) with hltA | heqA | hgtA
        · have hIn : Work.EL.InArc θ (37 / 63) (22 / 63 + 1) := InArc_mem_Ico_0A hθ0 hltA
          exact Or.inr (paramRay_subset_pairSide_of_InArc hN (T.pairC) c_lt_a1 a1_lt_c1 hIn hwray)
        · exact absurd heqA hneA
        · rcases lt_trichotomy θ (25 / 63) with hltB | heqB | hgtB
          · have hIn : Work.EL.InArc θ (22 / 63) (25 / 63) := InArc_mem_Ioo_AB hgtA hltB
            exact Or.inl (Or.inl
              (paramRay_subset_pairSide_of_InArc hN (T.pairA) a_lt_b b_lt_a1 hIn hwray))
          · exact absurd heqB hneB
          · rcases lt_trichotomy θ (37 / 63) with hltC | heqC | hgtC
            · have hIn : Work.EL.InArc θ (25 / 63) (37 / 63) := InArc_mem_Ioo_BC hgtB hltC
              exact Or.inl (Or.inr
                (paramRay_subset_pairSide_of_InArc hN (T.pairB) b_lt_c c_lt_b1 hIn hwray))
            · exact absurd heqC hneC
            · have hIn : Work.EL.InArc θ (37 / 63) (22 / 63 + 1) := InArc_mem_Ioo_CA hgtC hθ1
              exact Or.inr
                (paramRay_subset_pairSide_of_InArc hN (T.pairC) c_lt_a1 a1_lt_c1 hIn hwray)
      rcases harm with (hwa | hwb) | hwc
      · exact Or.inl (Or.inl
          (preconnected_subset_arm (Or.inl rfl) hDpre hDsub hwD hwa hzD))
      · exact Or.inl (Or.inr
          (preconnected_subset_arm (Or.inr (Or.inl rfl)) hDpre hDsub hwD hwb hzD))
      · exact Or.inr
          (preconnected_subset_arm (Or.inr (Or.inr rfl)) hDpre hDsub hwD hwc hzD)
    · exfalso
      have hDK : D ⊆ Work.EL.K c := fun w hw => by
        by_contra hwK
        exact hoff ⟨w, hw, hwK⟩
      have hYCopen : IsOpen (Work.EL.Tripod.curve T)ᶜ := (isClosed_curve hN T).isOpen_compl
      have hDopen : IsOpen D := IsOpen.connectedComponentIn hYCopen
      have hDcl : closure D ⊆ D ∪ Work.EL.Tripod.curve T := by
        intro u hu
        by_cases huY : u ∈ Work.EL.Tripod.curve T
        · exact Or.inr huY
        · left
          obtain ⟨ε, hεpos, hε⟩ := Metric.isOpen_iff.mp hYCopen u huY
          obtain ⟨c₁, hc₁D, hc₁d⟩ := Metric.mem_closure_iff.mp hu ε hεpos
          have hc₁B : c₁ ∈ Metric.ball u ε := by
            rw [Metric.mem_ball, dist_comm]; exact hc₁d
          have hconn : IsPreconnected (D ∪ Metric.ball u ε) :=
            IsPreconnected.union c₁ hc₁D hc₁B hDpre (convex_ball u ε).isPreconnected
          have hsub : D ∪ Metric.ball u ε ⊆ (Work.EL.Tripod.curve T)ᶜ := by
            intro v hv
            rcases hv with hv | hv
            · exact hDsub hv
            · exact hε hv
          have hsubD := IsPreconnected.subset_connectedComponentIn hconn (Or.inl hzD) hsub
          exact hsubD (Or.inr (Metric.mem_ball_self hεpos))
      have hclK : closure D ⊆ Work.EL.K c := closure_minimal hDK hN.isClosed_mb
      have hclsub : closure D ⊆ D ∪ {T.y} := by
        intro u hu
        rcases hDcl hu with h | h
        · exact Or.inl h
        · exact Or.inr (curve_inter_K_subset hN T ⟨h, hclK hu⟩)
      have hDsuby : D ⊆ ({T.y}ᶜ : Set ℂ) := by
        intro u hu
        rw [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro huy
        exact hDsub hu (by rw [huy]; exact mem_curve_y hN T)
      have hDeq : D = ({T.y}ᶜ : Set ℂ) := by
        refine Set.Subset.antisymm hDsuby ?_
        have hrank : (1 : Cardinal) < Module.rank ℝ ℂ := by
          rw [Complex.rank_real_complex]; norm_num
        have hpu : IsPreconnected ({T.y}ᶜ : Set ℂ) :=
          (isConnected_compl_singleton_of_one_lt_rank hrank T.y).isPreconnected
        have hcov : ({T.y}ᶜ : Set ℂ) ⊆ D ∪ (closure D)ᶜ := by
          intro u hu
          rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hu
          by_cases huc : u ∈ closure D
          · left
            rcases hclsub huc with h | h
            · exact h
            · exact absurd h hu
          · right; exact huc
        have hdisj : ({T.y}ᶜ : Set ℂ) ∩ (D ∩ (closure D)ᶜ) = ∅ := by
          rw [Set.eq_empty_iff_forall_notMem]
          rintro u ⟨-, huD, hucl⟩
          exact hucl (subset_closure huD)
        rcases isPreconnected_iff_subset_of_disjoint.mp hpu D (closure D)ᶜ hDopen
          isClosed_closure.isOpen_compl hcov hdisj with h | h
        · exact h
        · exfalso; exact (h (hDsuby hzD)) (subset_closure hzD)
      obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.mp hN.isBounded_mb
      have hKbound : ∀ u ∈ Work.EL.K c, ‖u‖ ≤ max M 1 := fun u hu =>
        le_trans (hM u hu) (le_max_left M 1)
      set R : ℝ := max M 1 + ‖T.y‖ + 1 with hRdef
      have hRpos : 0 < R := by
        rw [hRdef]; linarith [norm_nonneg T.y, le_max_right M 1]
      have hmemD : T.y + ((R : ℝ) : ℂ) ∈ D := by
        rw [hDeq, Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hcon
        have h1 : ((R : ℝ) : ℂ) = 0 := by
          have := congrArg (fun u : ℂ => u - T.y) hcon
          simpa using this
        have h2 : R = 0 := by
          have := congrArg Complex.re h1
          simpa using this
        linarith
      have hle : ‖T.y + ((R : ℝ) : ℂ)‖ ≤ max M 1 := hKbound _ (hDK hmemD)
      have hbig : max M 1 < ‖T.y + ((R : ℝ) : ℂ)‖ := by
        have h5 : ‖((R : ℝ) : ℂ)‖ = R := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos]
        have h4 : ‖((R : ℝ) : ℂ)‖ - ‖T.y‖ ≤ ‖T.y + ((R : ℝ) : ℂ)‖ := by
          have h6 := abs_norm_sub_norm_le (((R : ℝ) : ℂ)) (-T.y)
          rw [norm_neg, show ((R : ℝ) : ℂ) - (-T.y) = T.y + ((R : ℝ) : ℂ) by ring] at h6
          exact le_trans (le_abs_self _) h6
        rw [h5] at h4
        rw [hRdef] at h4 ⊢
        linarith
      linarith

end Work.ELTop
