import Mathlib
import Submission.Work.BMF.adi_all_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Polynomial Finset Real

variable {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}

/-! ## Local geometry of a step of the unrestricted graph

The file `adi_graph_aux` establishes, for the `q`-subgraph (`GAdjQ`), that the step data
`(stepV, stepU)` determine the target vertex, hence that the labels of a walk determine the walk.
Here we redo that local analysis for the *unrestricted* graph `GAdjAll`, where the prime `q`
no longer labels the arcs.  The only place where `GAdjQ` was used is the extraction of a
witnessing edge for a non-forward arc (`stepFwd_or_rev`), which for `GAdjAll` is immediate.
-/

/-- Reverse-arc existence for the unrestricted graph: an arc `x → y` is realised by an edge of
`D.edges` either in the forward or in the backward direction. -/
private lemma stepFwd_or_rev_all {D : QuadData k f c C X L P₁ P₂} {x y : GVert D}
    (hxy : GAdjAll D x y) (h : ¬ stepFwd D x y) :
    ∃ e ∈ D.edges, e.x₁ = y.1 ∧ e.x₂ = x.1 := by
  obtain ⟨e, he, hh | hh⟩ := hxy
  · exact absurd ⟨e, he, hh.1, hh.2⟩ h
  · exact ⟨e, he, hh.1, hh.2⟩

/-- The source prime of a step of the unrestricted graph lies in `[P₁, 2P₁]`. -/
lemma stepV_prime_all (D : QuadData k f c C X L P₁ P₂) {x y : GVert D}
    (hxy : GAdjAll D x y) : IsPrimeIn P₁ (2 * P₁) (stepV D x y) := by
  classical
  by_cases h : stepFwd D x y
  · rw [stepV_fwd D h]
    exact EdgeGeom.prime_p₂ (D.geom _ (arcWit_spec D h).1)
  · rw [stepV_rev D h]
    exact EdgeGeom.prime_p₁ (D.geom _ (arcWit_spec D (stepFwd_or_rev_all hxy h)).1)

/-- The target prime of a step of the unrestricted graph lies in `[P₁, 2P₁]`. -/
lemma stepU_prime_all (D : QuadData k f c C X L P₁ P₂) {x y : GVert D}
    (hxy : GAdjAll D x y) : IsPrimeIn P₁ (2 * P₁) (stepU D x y) := by
  classical
  by_cases h : stepFwd D x y
  · rw [stepU_fwd D h]
    exact EdgeGeom.prime_p₁ (D.geom _ (arcWit_spec D h).1)
  · rw [stepU_rev D h]
    exact EdgeGeom.prime_p₂ (D.geom _ (arcWit_spec D (stepFwd_or_rev_all hxy h)).1)

/-- Geometry of a step of the unrestricted graph: `x ≈ (stepV/stepU) y`. -/
lemma stepGeom_all (D : QuadData k f c C X L P₁ P₂) {x y : GVert D}
    (hxy : GAdjAll D x y) (hP : 0 < P₁) (hL : 0 < L) :
    |x.1 - ((stepV D x y : ℝ) / (stepU D x y : ℝ)) * y.1| ≤ 200 * L := by
  classical
  by_cases h : stepFwd D x y
  · have hspec := arcWit_spec D h
    have hg := EdgeGeom.geom (D.geom _ hspec.1)
    rw [hspec.2.1, hspec.2.2] at hg
    rw [stepV_fwd D h, stepU_fwd D h]
    linarith [hg, hP, hL]
  · have hrev := stepFwd_or_rev_all hxy h
    have hspec := arcWit_spec D hrev
    have hg := EdgeGeom.geom (D.geom _ hspec.1)
    rw [hspec.2.1, hspec.2.2] at hg
    rw [stepV_rev D h, stepU_rev D h]
    have hUpos : 0 < (((arcWit D y.1 x.1).p₂ : ℕ) : ℝ) := by
      have hh := (EdgeGeom.prime_p₂ (D.geom _ hspec.1)).2.1
      linarith [hP, hh]
    have hVpos : 0 < (((arcWit D y.1 x.1).p₁ : ℕ) : ℝ) := by
      have hh := (EdgeGeom.prime_p₁ (D.geom _ hspec.1)).2.1
      linarith [hP, hh]
    have h1 : (((arcWit D y.1 x.1).p₁ : ℕ) : ℝ) ≤ 2 * P₁ :=
      (EdgeGeom.prime_p₁ (D.geom _ hspec.1)).2.2
    have h2 : P₁ ≤ (((arcWit D y.1 x.1).p₂ : ℕ) : ℝ) :=
      (EdgeGeom.prime_p₂ (D.geom _ hspec.1)).2.1
    have hvu : (((arcWit D y.1 x.1).p₁ : ℕ) : ℝ) / (((arcWit D y.1 x.1).p₂ : ℕ) : ℝ) ≤ 2 := by
      rw [div_le_iff₀ (by linarith)]; linarith
    exact geom_swap hUpos hVpos hvu hg hL.le

/-- The reverse form of the step geometry of the unrestricted graph: `y ≈ (stepU/stepV) x`. -/
private lemma stepGeom'_all (D : QuadData k f c C X L P₁ P₂) {x y : GVert D}
    (hxy : GAdjAll D x y) (hP : 0 < P₁) (hL : 0 < L) :
    |y.1 - ((stepU D x y : ℝ) / (stepV D x y : ℝ)) * x.1| ≤ 200 * L := by
  classical
  have hu : (0:ℝ) < (stepU D x y : ℝ) := by
    have := (stepU_prime_all D hxy).2.1; linarith [hP]
  have hv : (0:ℝ) < (stepV D x y : ℝ) := by
    have := (stepV_prime_all D hxy).2.1; linarith [hP]
  have hvu : ((stepU D x y : ℝ) / (stepV D x y : ℝ)) ≤ 2 := by
    have h1 : (stepU D x y : ℝ) ≤ 2 * P₁ := (stepU_prime_all D hxy).2.2
    have h2 : P₁ ≤ (stepV D x y : ℝ) := (stepV_prime_all D hxy).2.1
    rw [div_le_iff₀ (by linarith)]; linarith
  by_cases h : stepFwd D x y
  · have hspec := arcWit_spec D h
    have hg := EdgeGeom.geom (D.geom _ hspec.1)
    rw [hspec.2.1, hspec.2.2] at hg
    have hgl : |x.1 - ((stepV D x y : ℝ) / (stepU D x y : ℝ)) * y.1| ≤ 100 * L := by
      rw [stepV_fwd D h, stepU_fwd D h]; exact hg
    have key : y.1 - ((stepU D x y : ℝ) / (stepV D x y : ℝ)) * x.1
        = -(((stepU D x y : ℝ) / (stepV D x y : ℝ)) *
            (x.1 - ((stepV D x y : ℝ) / (stepU D x y : ℝ)) * y.1)) := by
      field_simp
      ring
    rw [key, abs_neg, abs_mul, abs_of_nonneg (div_nonneg hu.le hv.le)]
    calc ((stepU D x y : ℝ) / (stepV D x y : ℝ)) *
          |x.1 - ((stepV D x y : ℝ) / (stepU D x y : ℝ)) * y.1|
        ≤ 2 * (100 * L) := mul_le_mul hvu hgl (abs_nonneg _) (by norm_num)
      _ = 200 * L := by ring
  · have hspec := arcWit_spec D (stepFwd_or_rev_all hxy h)
    have hg := EdgeGeom.geom (D.geom _ hspec.1)
    rw [hspec.2.1, hspec.2.2] at hg
    have hgl : |y.1 - ((stepU D x y : ℝ) / (stepV D x y : ℝ)) * x.1| ≤ 100 * L := by
      rw [stepU_rev D h, stepV_rev D h]; exact hg
    linarith [hgl, hP, hL]

/-- **The labels of a step of the unrestricted graph determine the next vertex.** -/
private lemma step_unique_all (D : QuadData k f c C X L P₁ P₂) (hP : 0 < P₁) (hL : 0 < L)
    {x y y' : GVert D} (hxy : GAdjAll D x y) (hxy' : GAdjAll D x y')
    (h1 : stepV D x y = stepV D x y') (h2 : stepU D x y = stepU D x y') : y = y' := by
  set M : ℝ := ((stepU D x y : ℝ) / (stepV D x y : ℝ)) * x.1 with hM
  have hA : |y.1 - M| ≤ 200 * L := by
    rw [hM]; exact stepGeom'_all D hxy hP hL
  have hB : |y'.1 - M| ≤ 200 * L := by
    have hh := stepGeom'_all D hxy' hP hL
    rw [← h1, ← h2] at hh
    rw [hM]
    exact hh
  have key : |y.1 - y'.1| ≤ |y.1 - M| + |y'.1 - M| := by
    have h := abs_sub_le y.1 M y'.1
    have h2' : |M - y'.1| = |y'.1 - M| := abs_sub_comm M y'.1
    linarith [h, h2']
  refine fam_eq_of_lt D hL ?_
  linarith

/-! ## Labels determine a walk of the unrestricted graph -/

theorem walk_eq_of_labels_GAdjAll {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    (D : Work.BMF.QuadData k f c C X L P₁ P₂) (hP : 0 < P₁) (hL : 0 < L)
    {ℓ : ℕ} {W W' : Fin (ℓ + 1) → Work.BMF.GVert D}
    (hW : W ∈ Work.BMF.walkSetAll D ℓ) (hW' : W' ∈ Work.BMF.walkSetAll D ℓ) (h0 : W 0 = W' 0) :
    Work.BMF.walkLabels D ℓ W = Work.BMF.walkLabels D ℓ W' → W = W' := by
  intro hlab
  have hV : ∀ j : Fin ℓ,
      stepV D (W j.castSucc) (W j.succ) = stepV D (W' j.castSucc) (W' j.succ) :=
    fun j => congrFun (congrArg Prod.fst hlab) j
  have hU : ∀ j : Fin ℓ,
      stepU D (W j.castSucc) (W j.succ) = stepU D (W' j.castSucc) (W' j.succ) :=
    fun j => congrFun (congrArg Prod.snd hlab) j
  have hadjW : ∀ j : Fin ℓ, GAdjAll D (W j.castSucc) (W j.succ) :=
    fun j => (Finset.mem_filter.mp hW).2 j
  have hadjW' : ∀ j : Fin ℓ, GAdjAll D (W' j.castSucc) (W' j.succ) :=
    fun j => (Finset.mem_filter.mp hW').2 j
  funext i
  induction i using Fin.induction with
  | zero => exact h0
  | succ j ih =>
      have h1 : stepV D (W j.castSucc) (W j.succ) = stepV D (W j.castSucc) (W' j.succ) := by
        have hh := hV j
        rw [← ih] at hh
        exact hh
      have h2 : stepU D (W j.castSucc) (W j.succ) = stepU D (W j.castSucc) (W' j.succ) := by
        have hh := hU j
        rw [← ih] at hh
        exact hh
      have hxy' : GAdjAll D (W j.castSucc) (W' j.succ) := by
        have hh := hadjW' j
        rw [← ih] at hh
        exact hh
      exact step_unique_all D hP hL (hadjW j) hxy' h1 h2

end Work.BMF
