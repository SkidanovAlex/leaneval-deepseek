import Mathlib
import Submission.Work.Whitney.BumpModel.Defs

namespace Work.Whitney.BumpModel

/-- Under the standing hypothesis, `û` takes the value `1/2` at `e₀`. -/
private lemma uhat_e0_eq (n : ℕ) [NeZero n] {χ : (Fin n → ℝ) → ℝ}
    (hlevel : ∀ t : ℝ, Work.Whitney.uhat n χ (t • Work.Whitney.e0 n) = 1 / 2 ↔
      t = 1 ∨ t = -1) :
    Work.Whitney.uhat n χ (Work.Whitney.e0 n) = 1 / 2 := by
  have h := (hlevel 1).mpr (Or.inl rfl)
  simpa using h

/-- Under the standing hypothesis, `û` takes the value `1/2` at `-e₀`. -/
private lemma uhat_nege0_eq (n : ℕ) [NeZero n] {χ : (Fin n → ℝ) → ℝ}
    (hlevel : ∀ t : ℝ, Work.Whitney.uhat n χ (t • Work.Whitney.e0 n) = 1 / 2 ↔
      t = 1 ∨ t = -1) :
    Work.Whitney.uhat n χ (-(Work.Whitney.e0 n)) = 1 / 2 := by
  have h := (hlevel (-1)).mpr (Or.inr rfl)
  have hs : (-1 : ℝ) • Work.Whitney.e0 n = -(Work.Whitney.e0 n) := by simp
  rwa [hs] at h

/-- The structure map identifies the pair `±e₀`. -/
private lemma structMap_e0_eq_neg (n : ℕ) [NeZero n] {χ : (Fin n → ℝ) → ℝ}
    (hlevel : ∀ t : ℝ, Work.Whitney.uhat n χ (t • Work.Whitney.e0 n) = 1 / 2 ↔
      t = 1 ∨ t = -1) :
    Work.Whitney.structMap n χ (Work.Whitney.e0 n) =
      Work.Whitney.structMap n χ (-(Work.Whitney.e0 n)) := by
  have hu := uhat_e0_eq n hlevel
  have hu' := uhat_nege0_eq n hlevel
  rw [Work.Whitney.structMap_apply, Work.Whitney.structMap_apply]
  refine Prod.ext ?_ ?_
  · funext i
    by_cases hi : i = 0
    · subst hi
      have h1 : (Work.Whitney.e0 n) 0 = 1 := by simp [Work.Whitney.e0]
      have h2 : (-(Work.Whitney.e0 n)) 0 = -1 := by simp [Work.Whitney.e0]
      rw [h1, h2, hu, hu']
      norm_num
    · simp [Work.Whitney.e0, hi]
  · funext i
    by_cases hi : i = 0
    · subst hi
      exact hu.trans hu'.symm
    · simp [Work.Whitney.e0, hi]

/-- The double points of the structure map `structMap χ`: if `û = χ/(1 + ∑xᵢ²)` takes the value `1/2` on the axis exactly at `±e₀`, then `structMap χ` is injective except for the pair `±e₀` (which it identifies). -/
theorem structMap_double_point (n : ℕ) [NeZero n] {χ : (Fin n → ℝ) → ℝ}
    (hlevel : ∀ t : ℝ, Work.Whitney.uhat n χ (t • Work.Whitney.e0 n) = 1 / 2 ↔ t = 1 ∨ t = -1)
    (x y : Fin n → ℝ) :
    Work.Whitney.structMap n χ x = Work.Whitney.structMap n χ y ↔
      x = y ∨ (x = Work.Whitney.e0 n ∧ y = -(Work.Whitney.e0 n)) ∨
        (x = -(Work.Whitney.e0 n) ∧ y = Work.Whitney.e0 n) := by
  constructor
  · intro h
    have hsplit := h
    simp only [Work.Whitney.structMap_apply] at hsplit
    have hfst : ∀ i, (if i = 0 then x 0 * (1 - 2 * Work.Whitney.uhat n χ x) else x i)
        = (if i = 0 then y 0 * (1 - 2 * Work.Whitney.uhat n χ y) else y i) :=
      fun i => congrFun (congrArg Prod.fst hsplit) i
    have hsnd : ∀ i, (if i = 0 then Work.Whitney.uhat n χ x
        else Work.Whitney.uhat n χ x * x 0 * x i)
        = (if i = 0 then Work.Whitney.uhat n χ y
        else Work.Whitney.uhat n χ y * y 0 * y i) :=
      fun i => congrFun (congrArg Prod.snd hsplit) i
    have huEq : Work.Whitney.uhat n χ x = Work.Whitney.uhat n χ y := by
      have := hsnd 0
      simpa using this
    have hcoord : ∀ i, i ≠ 0 → x i = y i := by
      intro i hi
      have := hfst i
      simpa [hi] using this
    have h0 : x 0 * (1 - 2 * Work.Whitney.uhat n χ x)
        = y 0 * (1 - 2 * Work.Whitney.uhat n χ y) := by
      have := hfst 0
      simpa using this
    have hsnd' : ∀ i, i ≠ 0 →
        Work.Whitney.uhat n χ x * x 0 * x i = Work.Whitney.uhat n χ y * y 0 * y i := by
      intro i hi
      have := hsnd i
      simpa [hi] using this
    by_cases hz : ∀ i, i ≠ 0 → x i = 0
    · -- `x` and `y` both lie on the `e₀`-axis.
      have hz' : ∀ i, i ≠ 0 → y i = 0 := fun i hi => by rw [← hcoord i hi]; exact hz i hi
      have hxax : x = x 0 • Work.Whitney.e0 n := by
        funext i
        by_cases hi : i = 0
        · subst hi; simp [Work.Whitney.e0]
        · rw [hz i hi]; simp [Work.Whitney.e0, hi]
      have hyax : y = y 0 • Work.Whitney.e0 n := by
        funext i
        by_cases hi : i = 0
        · subst hi; simp [Work.Whitney.e0]
        · rw [hz' i hi]; simp [Work.Whitney.e0, hi]
      have hux : Work.Whitney.uhat n χ x = Work.Whitney.uhat n χ (x 0 • Work.Whitney.e0 n) :=
        congrArg (fun z => Work.Whitney.uhat n χ z) hxax
      have hvy : Work.Whitney.uhat n χ y = Work.Whitney.uhat n χ (y 0 • Work.Whitney.e0 n) :=
        congrArg (fun z => Work.Whitney.uhat n χ z) hyax
      by_cases hu12 : Work.Whitney.uhat n χ x = 1 / 2
      · have hx01 : x 0 = 1 ∨ x 0 = -1 := (hlevel (x 0)).mp (hux.symm.trans hu12)
        have hy01 : y 0 = 1 ∨ y 0 = -1 :=
          (hlevel (y 0)).mp (hvy.symm.trans (huEq ▸ hu12))
        rcases hx01 with hx | hx <;> rcases hy01 with hy | hy
        · left
          exact (hxax.trans (congrArg (fun c : ℝ => c • Work.Whitney.e0 n) hx)).trans
            (hyax.trans (congrArg (fun c : ℝ => c • Work.Whitney.e0 n) hy)).symm
        · right; left
          exact ⟨(hxax.trans (congrArg (fun c : ℝ => c • Work.Whitney.e0 n) hx)).trans (by simp),
                 (hyax.trans (congrArg (fun c : ℝ => c • Work.Whitney.e0 n) hy)).trans (by simp)⟩
        · right; right
          exact ⟨(hxax.trans (congrArg (fun c : ℝ => c • Work.Whitney.e0 n) hx)).trans (by simp),
                 (hyax.trans (congrArg (fun c : ℝ => c • Work.Whitney.e0 n) hy)).trans (by simp)⟩
        · left
          exact (hxax.trans (congrArg (fun c : ℝ => c • Work.Whitney.e0 n) hx)).trans
            (hyax.trans (congrArg (fun c : ℝ => c • Work.Whitney.e0 n) hy)).symm
      · left
        have hneq : (1 : ℝ) - 2 * Work.Whitney.uhat n χ x ≠ 0 := by
          intro hh; exact hu12 (by linarith)
        have h0' : x 0 * (1 - 2 * Work.Whitney.uhat n χ x)
            = y 0 * (1 - 2 * Work.Whitney.uhat n χ x) := by
          rw [← huEq] at h0; exact h0
        have hx0y0 : x 0 = y 0 := by
          have hkey : (x 0 - y 0) * (1 - 2 * Work.Whitney.uhat n χ x) = 0 := by
            nlinarith [h0']
          rcases mul_eq_zero.mp hkey with hh | hh
          · linarith
          · exact absurd hh hneq
        funext i
        by_cases hi : i = 0
        · subst hi; exact hx0y0
        · exact hcoord i hi
    · -- Some off-axis coordinate of `x` is nonzero, forcing `x 0 = y 0`.
      push Not at hz
      obtain ⟨i, hi, hxi⟩ := hz
      left
      have hyi : y i = x i := (hcoord i hi).symm
      have hx0y0 : x 0 = y 0 := by
        by_cases hu0 : Work.Whitney.uhat n χ x = 0
        · have hv0 : Work.Whitney.uhat n χ y = 0 := by rw [← huEq]; exact hu0
          have h0'' := h0
          rw [hu0, hv0] at h0''
          simpa using h0''
        · have hh := hsnd' i hi
          rw [← huEq, hyi] at hh
          have hh2 : Work.Whitney.uhat n χ x * x 0 = Work.Whitney.uhat n χ x * y 0 :=
            mul_right_cancel₀ hxi hh
          exact mul_left_cancel₀ hu0 hh2
      funext j
      by_cases hj : j = 0
      · subst hj; exact hx0y0
      · exact hcoord j hj
  · intro h
    rcases h with hxy | ⟨hx, hy⟩ | ⟨hx, hy⟩
    · rw [hxy]
    · rw [hx, hy]; exact structMap_e0_eq_neg n hlevel
    · rw [hx, hy]; exact (structMap_e0_eq_neg n hlevel).symm

end Work.Whitney.BumpModel
