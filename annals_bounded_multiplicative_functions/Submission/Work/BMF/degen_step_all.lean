import Mathlib
import Submission.Work.BMF.adi_all_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

variable {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}

/-! ## Step data of the full quadruple graph

The `GAdjAll`-versions of `stepFwd_or_rev`, `stepV_prime`, `stepU_prime`, `stepGeom'` and
`step_unique` of `Submission.Work.BMF.adi_graph_defs`.  The only difference is that the
adjacency carries no prime `q`, so the witnessing edge has to be extracted from the unfolding
of `GAdjAll` rather than from `GAdjQ`. -/

/-- The reverse-arc existence is forced when the forward one fails (full graph). -/
lemma stepFwd_or_rev_all {D : QuadData k f c C X L P₁ P₂} {x y : GVert D}
    (hxy : GAdjAll D x y) (h : ¬ stepFwd D x y) :
    ∃ e ∈ D.edges, e.x₁ = y.1 ∧ e.x₂ = x.1 := by
  obtain ⟨e, he, hh | hh⟩ := hxy
  · exact absurd ⟨e, he, hh.1, hh.2⟩ h
  · exact ⟨e, he, hh.1, hh.2⟩

/-- The source prime of a step of the full graph lies in `[P₁, 2P₁]`. -/
lemma stepV_prime_all (D : QuadData k f c C X L P₁ P₂) {x y : GVert D}
    (hxy : GAdjAll D x y) : IsPrimeIn P₁ (2 * P₁) (stepV D x y) := by
  classical
  by_cases h : stepFwd D x y
  · rw [stepV_fwd D h]
    exact EdgeGeom.prime_p₂ (D.geom _ (arcWit_spec D h).1)
  · rw [stepV_rev D h]
    exact EdgeGeom.prime_p₁ (D.geom _ (arcWit_spec D (stepFwd_or_rev_all hxy h)).1)

/-- The target prime of a step of the full graph lies in `[P₁, 2P₁]`. -/
lemma stepU_prime_all (D : QuadData k f c C X L P₁ P₂) {x y : GVert D}
    (hxy : GAdjAll D x y) : IsPrimeIn P₁ (2 * P₁) (stepU D x y) := by
  classical
  by_cases h : stepFwd D x y
  · rw [stepU_fwd D h]
    exact EdgeGeom.prime_p₁ (D.geom _ (arcWit_spec D h).1)
  · rw [stepU_rev D h]
    exact EdgeGeom.prime_p₂ (D.geom _ (arcWit_spec D (stepFwd_or_rev_all hxy h)).1)

/-- The reverse form of the step geometry for the full graph: `y ≈ (stepU/stepV) x`. -/
lemma stepGeom'_all (D : QuadData k f c C X L P₁ P₂) {x y : GVert D}
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

/-- The labels of a step of the full graph determine the next vertex. -/
lemma step_unique_all (D : QuadData k f c C X L P₁ P₂) (hP : 0 < P₁) (hL : 0 < L)
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

theorem degen_step_all {k : ℕ} {f : ℕ → ℂ} {c C X L P₁ P₂ : ℝ}
    (D : Work.BMF.QuadData k f c C X L P₁ P₂) (hP : 0 < P₁) (hL : 0 < L) :
    (∀ {x y : Work.BMF.GVert D}, Work.BMF.GAdjAll D x y →
        Work.BMF.IsPrimeIn P₁ (2 * P₁) (Work.BMF.stepV D x y) ∧
        Work.BMF.IsPrimeIn P₁ (2 * P₁) (Work.BMF.stepU D x y)) ∧
      (∀ {x y y' : Work.BMF.GVert D}, Work.BMF.GAdjAll D x y → Work.BMF.GAdjAll D x y' →
        Work.BMF.stepV D x y = Work.BMF.stepV D x y' →
        Work.BMF.stepU D x y = Work.BMF.stepU D x y' → y = y') := by
  constructor
  · intro x y hxy
    exact ⟨stepV_prime_all D hxy, stepU_prime_all D hxy⟩
  · intro x y y' hxy hxy' h1 h2
    exact step_unique_all D hP hL hxy hxy' h1 h2

end Work.BMF
