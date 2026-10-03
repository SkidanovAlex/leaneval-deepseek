import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Fatou.Qreg.backwardIterate
import Submission.Work.Fatou.Qreg.forwardIterate
import Submission.Work.Fatou.Qreg.fatouInjOnQ
import Submission.Work.FatouL1.Surface.orbitDefs
import Submission.Work.FatouL1.Surface.meetFund
import Submission.Work.FatouL1.Surface.meetUniqTarget
import Submission.Work.FatouL1.Surface.specSucc

namespace Work.FatouL1.Surface

open Set Metric Complex MandelDim
open scoped Topology

noncomputable section

variable {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} {x₀ : ℝ}

/-- The candidate (representative, level) pair of a point of `𝒬` is unique: two candidates for the
same point `z` have the same representative (two points of the fundamental strip can only lie on a
common orbit if they are equal, `Work.FatouL1.Surface.meetFund`) and the same level (the signed
distance to the common meet point is determined, `Work.FatouL1.Surface.meetFund` again). -/
theorem spec_unique (hadm : MandelDim.QAdm b₁ b₂)
    (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂)) {z : ℂ} {p p' : ℂ × ℤ}
    (h : Spec b₁ b₂ F x₀ z p) (h' : Spec b₁ b₂ F x₀ z p') : p = p' := by
  obtain ⟨a, b, hm, -, hlv⟩ := h.2
  obtain ⟨a', b', hm', -, hlv'⟩ := h'.2
  obtain ⟨heq, hd⟩ := meetFund hadm hF h.1 h'.1 hm hm'
  refine Prod.ext heq ?_
  rw [hlv, hlv', hd]

/-- **The orbit coordinate (fundamental-strip representative + integer level).**

For a near-translation `F` on an admissible region `Qreg b₁ b₂` and a line `Re = x₀` inside it
(`∀ a ∈ b₁, a.re + 1 < x₀` and `∀ b ∈ b₂, x₀ + 3 < b.re`), every point of `𝒬` has a
*canonical* representative in the fundamental strip `fundStrip F (Qreg b₁ b₂) x₀` together with an
integer level, with the following properties:
* the representative lies in the fundamental strip;
* a point of the fundamental strip is its own representative, of level `0`;
* one step of `F` (staying in `𝒬`) keeps the representative and increases the level by one;
* the pair `(representative, level)` determines the point;
* the point and its representative lie on a common orbit piece entirely inside `𝒬`.

The canonical representative is obtained by iterating `F` forward until `Re ≥ x₀` (existence and
termination: `Work.Fatou.Qreg.forwardIterate`), and then backwards, taking at each step the
*unique* preimage in `𝒬` with `Re ≥ x₀` (uniqueness: `Work.Fatou.Qreg.fatouInjOnQ`), until the
fundamental strip is reached (termination: `Work.Fatou.Qreg.exists_iterate_eq_of_mem` = the
backward iteration).  The level is `(number of backward steps) - (number of forward steps)`. -/
theorem orbitCoord {b₁ b₂ : Option ℂ} {F : ℂ → ℂ} (hadm : MandelDim.QAdm b₁ b₂)
    (hF : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂)) {x₀ : ℝ}
    (h₁ : ∀ a ∈ b₁, a.re + 1 < x₀) (h₂ : ∀ b ∈ b₂, x₀ + 3 < b.re) :
    ∃ (rep : ℂ → ℂ) (lev : ℂ → ℤ),
      (∀ z ∈ MandelDim.Qreg b₁ b₂, rep z ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂) x₀) ∧
      (∀ z ∈ MandelDim.Qreg b₁ b₂, z ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂) x₀ →
        rep z = z ∧ lev z = 0) ∧
      (∀ z ∈ MandelDim.Qreg b₁ b₂, F z ∈ MandelDim.Qreg b₁ b₂ →
        rep (F z) = rep z ∧ lev (F z) = lev z + 1) ∧
      (∀ z ∈ MandelDim.Qreg b₁ b₂, ∀ z' ∈ MandelDim.Qreg b₁ b₂,
        rep z = rep z' → lev z = lev z' → z = z') ∧
      (∀ z ∈ MandelDim.Qreg b₁ b₂, ∃ k : ℕ,
        (F^[k] z = rep z ∧ ∀ j ≤ k, F^[j] z ∈ MandelDim.Qreg b₁ b₂) ∨
        (F^[k] (rep z) = z ∧ ∀ j ≤ k, F^[j] (rep z) ∈ MandelDim.Qreg b₁ b₂)) := by
  classical
  -- Shishikura A.2.1(i): every point of `𝒬` lies on the forward orbit of a point of the
  -- fundamental strip, and the level is the signed number of steps.
  have hex : ∀ z : ℂ, ∃ p : ℂ × ℤ, z ∉ MandelDim.Qreg b₁ b₂ ∨ Spec b₁ b₂ F x₀ z p := by
    intro z
    by_cases hz : z ∈ MandelDim.Qreg b₁ b₂
    · obtain ⟨q, hq⟩ :=
        exists_spec (b₁ := b₁) (b₂ := b₂) (F := F) (x₀ := x₀) hadm hF h₁ h₂ hz
      exact ⟨q, Or.inr hq⟩
    · exact ⟨(z, 0), Or.inl hz⟩
  let P : ℂ → ℂ × ℤ := fun z => Classical.choose (hex z)
  have hPspec : ∀ z (hz : z ∈ MandelDim.Qreg b₁ b₂), Spec b₁ b₂ F x₀ z (P z) := by
    intro z hz
    rcases Classical.choose_spec (hex z) with h | h
    · exact absurd hz h
    · exact h
  -- the representative and the level, as functions of the point
  let rep : ℂ → ℂ := fun z => (P z).1
  let lev : ℂ → ℤ := fun z => (P z).2
  have hrep_apply : ∀ z : ℂ, rep z = (P z).1 := fun z => rfl
  have hlev_apply : ∀ z : ℂ, lev z = (P z).2 := fun z => rfl
  refine ⟨rep, lev, ?_, ?_, ?_, ?_, ?_⟩
  · -- the representative lies in the fundamental strip
    intro z hz
    rw [hrep_apply]
    exact (hPspec z hz).1
  · -- a point of the fundamental strip is its own representative, of level zero
    intro z hz hzf
    have hself : Spec b₁ b₂ F x₀ z (z, 0) :=
      ⟨hzf, 0, 0, ⟨rfl, piece_zero hz, piece_zero hz⟩, Or.inl rfl, by simp⟩
    have hEq : P z = (z, 0) := spec_unique hadm hF (hPspec z hz) hself
    constructor
    · rw [hrep_apply, hEq]
    · rw [hlev_apply, hEq]
  · -- one step of `F` keeps the representative and increases the level by one
    intro z hz hzF
    have hsucc : Spec b₁ b₂ F x₀ (F z) ((P z).1, (P z).2 + 1) := specSucc (hPspec z hz) hzF
    have hEq : P (F z) = ((P z).1, (P z).2 + 1) := spec_unique hadm hF (hPspec (F z) hzF) hsucc
    constructor
    · rw [hrep_apply (F z), hrep_apply z, hEq]
    · rw [hlev_apply (F z), hlev_apply z, hEq]
  · -- the pair (representative, level) determines the point
    intro z hz z' hz' hrep hlev
    rw [hrep_apply z] at hrep
    rw [hrep_apply z'] at hrep
    rw [hlev_apply z] at hlev
    rw [hlev_apply z'] at hlev
    obtain ⟨-, a, b, hm, -, hlv⟩ := hPspec z hz
    obtain ⟨-, a', b', hm', -, hlv'⟩ := hPspec z' hz'
    rw [hrep] at hm
    refine meetUniqTarget hadm hF hm hm' ?_
    rw [← hlv, ← hlv', hlev]
  · -- the point and its representative lie on a common orbit piece inside `𝒬`
    intro z hz
    obtain ⟨-, a, b, hm, hab, -⟩ := hPspec z hz
    rcases hab with ha | hb
    · subst ha
      obtain ⟨hmeet, -, hpz⟩ := hm
      exact ⟨b, Or.inl ⟨by simpa [hrep_apply] using hmeet.symm, hpz⟩⟩
    · subst hb
      obtain ⟨hmeet, hps, -⟩ := hm
      exact ⟨a, Or.inr ⟨by simpa [hrep_apply] using hmeet, hps⟩⟩

end

end Work.FatouL1.Surface
