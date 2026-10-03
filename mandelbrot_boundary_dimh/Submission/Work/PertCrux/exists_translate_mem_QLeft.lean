import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.Setup

/-!
# A uniform left translation into Shishikura's repelling sector `QLeft ξ₀`

Shishikura's repelling sector is `QLeft ξ = {w : ℂ | π/3 < |arg (w + ξ)|}`
(`MandelDim.QLeft`).  It contains the open half-plane `{w | w.re < -ξ}`: a point strictly to the
left of the vertex `-ξ` has `|arg (w + ξ)| ≥ π/2 > π/3` (Mathlib's
`Complex.abs_arg_le_pi_div_two_iff`), which is `halfplane_subset_QLeft` below.

The main lemma is the *uniform* form of the `exhaust` field of `MandelDim.ParabData`: on a compact
set `K' ⊆ Dφ` the whole translate `K' - N` lands in the sector for one single `N`.  Indeed `re` is
continuous, so `K'` is bounded above in real part, say by `a`; taking `N > a + ξ₀` gives
`re (w - N) ≤ a - N < -ξ₀` for every `w ∈ K'`, and then the half-plane lemma applies.  (The
hypothesis `K' ⊆ d.Dφ` is not needed for this argument; it is kept because the caller states the
lemma that way.)
-/

set_option linter.unusedVariables false

namespace Work.PertCrux

/-- `QLeft ξ = {w | π/3 < |arg (w + ξ)|}` contains the half-plane `{w | w.re < -ξ}`: a point
strictly left of the vertex `-ξ` satisfies `|arg (w + ξ)| > π/2 > π/3`. -/
lemma halfplane_subset_QLeft (ξ : ℝ) : {w : ℂ | w.re < -ξ} ⊆ MandelDim.QLeft ξ := by
  intro w hw
  have hwr : w.re < -ξ := hw
  have hleft : (w + (ξ : ℂ)).re < 0 := by
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith
  have h' : ¬ |Complex.arg (w + (ξ : ℂ))| ≤ Real.pi / 2 := by
    rw [Complex.abs_arg_le_pi_div_two_iff]
    exact not_le.mpr hleft
  have h2 : Real.pi / 2 < |Complex.arg (w + (ξ : ℂ))| := not_le.mp h'
  change Real.pi / 3 < |Complex.arg (w + (ξ : ℂ))|
  have hpi := Real.pi_pos
  linarith

theorem exists_translate_mem_QLeft {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    {K' : Set ℂ} (hK'c : IsCompact K') (hK' : K' ⊆ d.Dφ) :
    ∃ N : ℕ, ∀ w ∈ K', w - (N : ℂ) ∈ MandelDim.QLeft d.ξ₀ := by
  -- `re` is bounded above on the compact set `K'`
  obtain ⟨a, ha⟩ := (hK'c.image Complex.continuous_re).bddAbove
  have ha' : ∀ w ∈ K', w.re ≤ a := fun w hw => ha ⟨w, hw, rfl⟩
  refine ⟨⌈a + d.ξ₀⌉₊ + 1, fun w hw => halfplane_subset_QLeft d.ξ₀ ?_⟩
  show (w - ((⌈a + d.ξ₀⌉₊ + 1 : ℕ) : ℂ)).re < -d.ξ₀
  have hceil : a + d.ξ₀ ≤ ((⌈a + d.ξ₀⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hre : (w - ((⌈a + d.ξ₀⌉₊ + 1 : ℕ) : ℂ)).re =
      w.re - ((⌈a + d.ξ₀⌉₊ + 1 : ℕ) : ℝ) := by
    simp [Complex.sub_re, Complex.natCast_re]
  rw [hre]
  have hcast : ((⌈a + d.ξ₀⌉₊ + 1 : ℕ) : ℝ) = ((⌈a + d.ξ₀⌉₊ : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  rw [hcast]
  linarith [ha' w hw]

end Work.PertCrux
