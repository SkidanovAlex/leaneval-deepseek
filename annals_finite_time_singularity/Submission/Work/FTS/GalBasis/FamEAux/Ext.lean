import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.GalBasis.Defs
import Submission.Work.FTS.GalBasis.FamEAux.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis

open Work.FTS.Galerkin (Fn galFun)
open Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The profile extended by zero off the open box -/

/-- The profile, extended by zero off the open box `(A,B) × (C,D)`. -/
def ext (g : ℝ → ℝ → ℝ) (A B C D : ℝ) : ℝ → ℝ → ℝ :=
  fun z θ => if (z, θ) ∈ Set.Ioo A B ×ˢ Set.Ioo C D then g z θ else 0

theorem ext_eq_g_of_mem {g : ℝ → ℝ → ℝ} {A B C D z θ : ℝ}
    (h : (z, θ) ∈ Set.Ioo A B ×ˢ Set.Ioo C D) : ext g A B C D z θ = g z θ := by
  simp only [ext, h, if_true]

theorem ext_eq_zero_of_not_mem {g : ℝ → ℝ → ℝ} {A B C D z θ : ℝ}
    (h : (z, θ) ∉ Set.Ioo A B ×ˢ Set.Ioo C D) : ext g A B C D z θ = 0 := by
  simp only [ext, h, if_false]

theorem ext_eq_zero_of_z_lt {g : ℝ → ℝ → ℝ} {A B C D A' B' C' D' z θ : ℝ}
    (hgsupp : SuppBox g A' B' C' D') (hz : z < A') : ext g A B C D z θ = 0 := by
  by_cases h : (z, θ) ∈ Set.Ioo A B ×ˢ Set.Ioo C D
  · rw [ext_eq_g_of_mem h]
    exact hgsupp z θ (Or.inl (fun hc => absurd hc.1 (not_le.mpr hz)))
  · exact ext_eq_zero_of_not_mem h

theorem ext_eq_zero_of_z_gt {g : ℝ → ℝ → ℝ} {A B C D A' B' C' D' z θ : ℝ}
    (hgsupp : SuppBox g A' B' C' D') (hz : B' < z) : ext g A B C D z θ = 0 := by
  by_cases h : (z, θ) ∈ Set.Ioo A B ×ˢ Set.Ioo C D
  · rw [ext_eq_g_of_mem h]
    exact hgsupp z θ (Or.inl (fun hc => absurd hc.2 (not_le.mpr hz)))
  · exact ext_eq_zero_of_not_mem h

theorem ext_eq_zero_of_th_lt {g : ℝ → ℝ → ℝ} {A B C D A' B' C' D' z θ : ℝ}
    (hgsupp : SuppBox g A' B' C' D') (hθ : θ < C') : ext g A B C D z θ = 0 := by
  by_cases h : (z, θ) ∈ Set.Ioo A B ×ˢ Set.Ioo C D
  · rw [ext_eq_g_of_mem h]
    exact hgsupp z θ (Or.inr (fun hc => absurd hc.1 (not_le.mpr hθ)))
  · exact ext_eq_zero_of_not_mem h

theorem ext_eq_zero_of_th_gt {g : ℝ → ℝ → ℝ} {A B C D A' B' C' D' z θ : ℝ}
    (hgsupp : SuppBox g A' B' C' D') (hθ : D' < θ) : ext g A B C D z θ = 0 := by
  by_cases h : (z, θ) ∈ Set.Ioo A B ×ˢ Set.Ioo C D
  · rw [ext_eq_g_of_mem h]
    exact hgsupp z θ (Or.inr (fun hc => absurd hc.2 (not_le.mpr hθ)))
  · exact ext_eq_zero_of_not_mem h

/-- On the complement of the inner support box the extension vanishes. -/
theorem ext_eq_zero_of_V1 {g : ℝ → ℝ → ℝ} {A B C D A' B' C' D' z θ : ℝ}
    (hgsupp : SuppBox g A' B' C' D') (h : z < A' ∨ B' < z ∨ θ < C' ∨ D' < θ) :
    ext g A B C D z θ = 0 := by
  rcases h with h | h | h | h
  · exact ext_eq_zero_of_z_lt hgsupp h
  · exact ext_eq_zero_of_z_gt hgsupp h
  · exact ext_eq_zero_of_th_lt hgsupp h
  · exact ext_eq_zero_of_th_gt hgsupp h

/-- The extension agrees with the profile on the closed box. -/
theorem ext_eq_g_of_mem_box {g : ℝ → ℝ → ℝ} {A B C D A' B' C' D' z θ : ℝ}
    (hgsupp : SuppBox g A' B' C' D') (hAA : A < A') (hBB : B' < B) (hCC : C < C')
    (hDD : D' < D) (hz : z ∈ Set.Icc A B) (hθ : θ ∈ Set.Icc C D) :
    ext g A B C D z θ = g z θ := by
  by_cases h : (z, θ) ∈ Set.Ioo A B ×ˢ Set.Ioo C D
  · exact ext_eq_g_of_mem h
  · rw [ext_eq_zero_of_not_mem h]
    by_cases hzA : z = A
    · rw [hzA]
      exact (hgsupp A θ (Or.inl (fun hc => absurd hc.1 (not_le.mpr hAA)))).symm
    · by_cases hzB : z = B
      · rw [hzB]
        exact (hgsupp B θ (Or.inl (fun hc => absurd hc.2 (not_le.mpr hBB)))).symm
      · by_cases hθC : θ = C
        · rw [hθC]
          exact (hgsupp z C (Or.inr (fun hc => absurd hc.1 (not_le.mpr hCC)))).symm
        · have hθD : θ = D := by
            by_contra hθD
            exact h (by
              rw [Set.mem_prod, Set.mem_Ioo, Set.mem_Ioo]
              exact ⟨⟨lt_of_le_of_ne hz.1 (Ne.symm hzA), lt_of_le_of_ne hz.2 hzB⟩,
                ⟨lt_of_le_of_ne hθ.1 (Ne.symm hθC), lt_of_le_of_ne hθ.2 hθD⟩⟩)
          rw [hθD]
          exact (hgsupp z D (Or.inr (fun hc => absurd hc.2 (not_le.mpr hDD)))).symm

/-- The extension is `C^9` on the open box containing `[0,B] × [0,D]` and the closed box. -/
theorem contDiffOn_uncurry_ext {g : ℝ → ℝ → ℝ} {A B C D A' B' C' D' : ℝ}
    (hAA : A < A') (hBB : B' < B) (hCC : C < C') (hDD : D' < D)
    (hg : ContDiffOn ℝ 9 (Function.uncurry g) (Set.Ioo A B ×ˢ Set.Ioo C D))
    (hgsupp : SuppBox g A' B' C' D') :
    ContDiffOn ℝ 9 (Function.uncurry (ext g A B C D))
      (Set.Ioo (min (A - 1) (-1)) (B + 1) ×ˢ Set.Ioo (min (C - 1) (-1)) (D + 1)) := by
  have hV1open : IsOpen {p : ℝ × ℝ | p.1 < A' ∨ B' < p.1 ∨ p.2 < C' ∨ D' < p.2} := by
    have h1 : IsOpen {p : ℝ × ℝ | p.1 < A'} := isOpen_lt continuous_fst continuous_const
    have h2 : IsOpen {p : ℝ × ℝ | B' < p.1} := isOpen_lt continuous_const continuous_fst
    have h3 : IsOpen {p : ℝ × ℝ | p.2 < C'} := isOpen_lt continuous_snd continuous_const
    have h4 : IsOpen {p : ℝ × ℝ | D' < p.2} := isOpen_lt continuous_const continuous_snd
    simpa only [setOf_or] using (h1.union (h2.union (h3.union h4)))
  have hV2open : IsOpen (Set.Ioo A B ×ˢ Set.Ioo C D) := isOpen_Ioo.prod isOpen_Ioo
  have hWopen : IsOpen (Set.Ioo (min (A - 1) (-1)) (B + 1)
      ×ˢ Set.Ioo (min (C - 1) (-1)) (D + 1)) := isOpen_Ioo.prod isOpen_Ioo
  set V₁ : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.1 < A' ∨ B' < p.1 ∨ p.2 < C' ∨ D' < p.2} with hV1
  set V₂ : Set (ℝ × ℝ) := Set.Ioo A B ×ˢ Set.Ioo C D with hV2
  set W : Set (ℝ × ℝ) := Set.Ioo (min (A - 1) (-1)) (B + 1)
    ×ˢ Set.Ioo (min (C - 1) (-1)) (D + 1) with hW
  have h1 : ContDiffOn ℝ 9 (Function.uncurry (ext g A B C D)) (W ∩ V₁) := by
    refine (contDiffOn_const (c := (0 : ℝ))).congr (fun p hp => ?_)
    rcases p with ⟨z, θ⟩
    simpa only [Function.uncurry] using ext_eq_zero_of_V1 hgsupp hp.2
  have h2 : ContDiffOn ℝ 9 (Function.uncurry (ext g A B C D)) (W ∩ V₂) := by
    refine (hg.mono Set.inter_subset_right).congr (fun p hp => ?_)
    rcases p with ⟨z, θ⟩
    simpa only [Function.uncurry] using ext_eq_g_of_mem hp.2
  have hWsub : W ⊆ V₁ ∪ V₂ := by
    intro p hp
    rcases p with ⟨z, θ⟩
    by_cases hmem : A < z ∧ z < B ∧ C < θ ∧ θ < D
    · exact Or.inr (by rw [hV2]; exact ⟨⟨hmem.1, hmem.2.1⟩, ⟨hmem.2.2.1, hmem.2.2.2⟩⟩)
    · refine Or.inl ?_
      rw [hV1]
      change z < A' ∨ B' < z ∨ θ < C' ∨ D' < θ
      by_contra hcon
      push_neg at hcon
      exact hmem ⟨by linarith [hcon.1, hAA], by linarith [hcon.2.1, hBB],
        by linarith [hcon.2.2.1, hCC], by linarith [hcon.2.2.2, hDD]⟩
  have hunion : W ∩ V₁ ∪ (W ∩ V₂) = W := by
    rw [← Set.inter_union_distrib_left, Set.inter_eq_left.mpr hWsub]
  have hU : ContDiffOn ℝ 9 (Function.uncurry (ext g A B C D)) (W ∩ V₁ ∪ (W ∩ V₂)) :=
    ContDiffOn.union_of_isOpen h1 h2 (hWopen.inter hV1open) (hWopen.inter hV2open)
  rwa [hunion] at hU

/-! ## Congruence of `D_z`- and `D_θ`-iterates, and of `mixed`, under eventual equality -/

theorem DzIter_congr_eqOn {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter i u))
      (Function.uncurry (Work.Spaces.DzIter i v)) V := by
  induction i with
  | zero => exact h
  | succ n ih =>
      intro p hp
      show p.1 * Work.Spaces.pz (Work.Spaces.DzIter n u) p.1 p.2
        = p.1 * Work.Spaces.pz (Work.Spaces.DzIter n v) p.1 p.2
      rw [Work.Spaces.pz_congr_of_isOpen hV ih hp]

theorem DthIter_congr_eqOn {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i u))
      (Function.uncurry (Work.Spaces.DthIter i v)) V := by
  induction i with
  | zero => exact h
  | succ n ih =>
      intro p hp
      show Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter n u) p.1 p.2
        = Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter n v) p.1 p.2
      rw [Work.Spaces.pth_congr_of_isOpen hV ih hp]

/-- If two functions agree eventually at a point, all their mixed derivatives agree there. -/
theorem mixed_congr_of_eventuallyEq {f1 f2 : ℝ → ℝ → ℝ} {z θ : ℝ} (a b : ℕ)
    (h : Function.uncurry f1 =ᶠ[𝓝 (z, θ)] Function.uncurry f2) :
    Work.Spaces.mixed a b f1 z θ = Work.Spaces.mixed a b f2 z θ := by
  obtain ⟨s, hs, hssub⟩ := Filter.Eventually.exists_mem h
  obtain ⟨W, hWsub, hWopen, hWmem⟩ := mem_nhds_iff.mp hs
  have heqW : Set.EqOn (Function.uncurry f1) (Function.uncurry f2) W := by
    intro p hp
    exact hssub p (hWsub hp)
  have hDth : Set.EqOn (Function.uncurry (Work.Spaces.DthIter b f1))
      (Function.uncurry (Work.Spaces.DthIter b f2)) W := DthIter_congr_eqOn hWopen heqW b
  have hfinal := DzIter_congr_eqOn hWopen hDth a hWmem
  simpa only [Function.uncurry, Work.Spaces.mixed] using hfinal

end Work.FTS.GalBasis
