import Mathlib
import Submission.Work.Interfaces.FatouNarrow

namespace Work.FatouL1

/-- A whole vertical line lies in `Qreg b₁ b₂` as soon as it is strictly to the right of every
vertex of `b₁` and strictly to the left of every vertex of `b₂`: the first condition of `Qreg`
becomes `Re (z - a) > 0` and the second `Re (z - b) < 0`, and both then follow from
`-|·| ≤ 0 ≤ |·|`. -/
lemma mem_Qreg_of_re {b₁ b₂ : Option ℂ} {x y : ℝ}
    (h₁ : ∀ a ∈ b₁, a.re < x) (h₂ : ∀ b ∈ b₂, x < b.re) :
    ((x : ℂ) + y * Complex.I) ∈ MandelDim.Qreg b₁ b₂ := by
  refine ⟨?_, ?_⟩
  · intro a ha
    have h := h₁ a ha
    have hre : (((x : ℂ) + y * Complex.I) - a).re = x - a.re := by simp
    have him : (((x : ℂ) + y * Complex.I) - a).im = y - a.im := by simp
    rw [hre, him]
    calc -|y - a.im| ≤ 0 := neg_nonpos.mpr (abs_nonneg _)
      _ < x - a.re := by linarith
  · intro b hb
    have h := h₂ b hb
    have hre : (((x : ℂ) + y * Complex.I) - b).re = x - b.re := by simp
    have him : (((x : ℂ) + y * Complex.I) - b).im = y - b.im := by simp
    rw [hre, him]
    calc x - b.re < 0 := by linarith
      _ ≤ |y - b.im| := abs_nonneg _

theorem strip_in_Qreg {b₁ b₂ : Option ℂ} (hadm : MandelDim.QAdm b₁ b₂) : ∃ x₀ : ℝ, ∀ x ∈ Set.Ioo (x₀ - 1 / 8) (x₀ + 9 / 8), ∀ y : ℝ, ((x : ℂ) + y * Complex.I) ∈ MandelDim.Qreg b₁ b₂ := by
  -- `b₁` and `b₂` are `Option`s, so there are only four cases; in each one we display `x₀`.
  rcases b₁ with _ | a <;> rcases b₂ with _ | b
  · -- both conditions on `Qreg` are vacuous
    exact ⟨0, fun x _ y => mem_Qreg_of_re (fun c hc => by simp at hc) (fun c hc => by simp at hc)⟩
  · -- `b₁ = none`, `b₂ = some b`: take `x₀ + 9/8 = b.re`
    refine ⟨b.re - 9 / 8, fun x hx y => mem_Qreg_of_re (fun c hc => by simp at hc) ?_⟩
    intro c hc
    have hc' : c = b := by simpa [eq_comm] using hc
    subst hc'
    have := hx.2
    linarith
  · -- `b₁ = some a`, `b₂ = none`: take `x₀ - 1/8 = a.re`
    refine ⟨a.re + 1 / 8, fun x hx y => mem_Qreg_of_re ?_ (fun c hc => by simp at hc)⟩
    intro c hc
    have hc' : c = a := by simpa [eq_comm] using hc
    subst hc'
    have := hx.1
    linarith
  · -- `b₁ = some a`, `b₂ = some b`: `QAdm` gives `a.re + 5/4 ≤ b.re`, and the strip
    -- `(a.re, a.re + 5/4)` fits between the two vertices.
    have hh : a.re + 4 < b.re := by simpa [MandelDim.QAdm] using hadm
    refine ⟨a.re + 1 / 8, fun x hx y => mem_Qreg_of_re ?_ ?_⟩
    · intro c hc
      have hc' : c = a := by simpa [eq_comm] using hc
      subst hc'
      have := hx.1
      linarith
    · intro c hc
      have hc' : c = b := by simpa [eq_comm] using hc
      subst hc'
      have := hx.2
      linarith

end Work.FatouL1
