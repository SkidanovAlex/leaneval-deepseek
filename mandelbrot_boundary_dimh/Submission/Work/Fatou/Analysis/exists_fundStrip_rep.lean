import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.Fatou.Analysis.UniqueDefs
import Submission.Work.Fatou.Qreg.fatouFundamental
import Submission.Work.Fatou.Setup

/-!
# Representatives of a Fatou coordinate in the fundamental strip

`Work.Fatou.Qreg.fatouFundamental` (Shishikura A.2.1(i)) provides, for every point `z` of the
region `Qreg b₁ b₂` of a near-translation `F`, an orbit point in the fundamental strip
`fundStrip F (Qreg b₁ b₂) x₀` — reached in finitely many forward or backward steps inside
`Qreg b₁ b₂`.

Iterating the Abel equation `Φ₀ (F z) = Φ₀ z + 1` of a Fatou coordinate `Φ₀` along that orbit
piece shifts `Φ₀` by the integer number of steps.  Combining this with the surjectivity modulo
`ℤ` of `Φ₀` (`SurjMod`, A.2.3) gives the statement used in
`Work.Fatou.Analysis.fatouUniqueOfConstructed`: every `w : ℂ` has a representative
`s ∈ fundStrip F (Qreg b₁ b₂) (xOf b₁ b₂)` with `Φ₀ s + n = w` for some `n : ℤ`.
-/

namespace Work.Fatou.Analysis

open MandelDim

/-- Iterating the Abel equation of a Fatou coordinate along an orbit that stays in the region. -/
private lemma iterate_abel {b₁ b₂ : Option ℂ} {F Ψ : ℂ → ℂ}
    (hΨ : MandelDim.IsFatouCoordOn F Ψ (MandelDim.Qreg b₁ b₂)) {z : ℂ} {n : ℕ}
    (h : ∀ j ≤ n, F^[j] z ∈ MandelDim.Qreg b₁ b₂) :
    Ψ (F^[n] z) = Ψ z + (n : ℂ) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have hk : ∀ j ≤ k, F^[j] z ∈ MandelDim.Qreg b₁ b₂ :=
      fun j hj => h j (le_trans hj (Nat.le_succ k))
    have ihk : Ψ (F^[k] z) = Ψ z + (k : ℂ) := ih hk
    have hk1 : F^[k] z ∈ MandelDim.Qreg b₁ b₂ := h k (Nat.le_succ k)
    have hk2 : F (F^[k] z) ∈ MandelDim.Qreg b₁ b₂ := by
      have hstep : F^[k + 1] z = F (F^[k] z) := Function.iterate_succ_apply' F k z
      rw [← hstep]
      exact h (k + 1) le_rfl
    have habel : Ψ (F (F^[k] z)) = Ψ (F^[k] z) + 1 := hΨ.2.2 (F^[k] z) hk1 hk2
    calc Ψ (F^[k + 1] z) = Ψ (F (F^[k] z)) := by rw [Function.iterate_succ_apply']
      _ = Ψ (F^[k] z) + 1 := habel
      _ = Ψ z + (k : ℂ) + 1 := by rw [ihk]
      _ = Ψ z + ((k + 1 : ℕ) : ℂ) := by push_cast; ring

theorem exists_fundStrip_rep {b₁ b₂ : Option ℂ} {F Φ₀ : ℂ → ℂ}
    (hadm : MandelDim.QAdm b₁ b₂) (hNT : MandelDim.NearTranslationOn F (MandelDim.Qreg b₁ b₂))
    (hΦ₀ : MandelDim.IsFatouCoordOn F Φ₀ (MandelDim.Qreg b₁ b₂))
    (hsurj : Work.Fatou.Analysis.SurjMod b₁ b₂ Φ₀)
    (horb : Work.Fatou.Analysis.OrbitRel b₁ b₂ F Φ₀) (w : ℂ) :
    ∃ s ∈ MandelDim.fundStrip F (MandelDim.Qreg b₁ b₂) (Work.Fatou.xOf b₁ b₂),
      ∃ n : ℤ, Φ₀ s + (n : ℂ) = w := by
  -- a point of the region representing `w` modulo `ℤ`
  obtain ⟨z, hz, m, hm⟩ := hsurj w
  -- an orbit point of `z` in the fundamental strip, reached forwards or backwards
  obtain ⟨k, s, hs, hchain⟩ :=
    Work.Fatou.Qreg.fatouFundamental b₁ b₂ F (Work.Fatou.xOf b₁ b₂) hadm hNT
      (Work.Fatou.xOf_gt_left hadm) (Work.Fatou.xOf_lt_right hadm) z hz
  rcases hchain with ⟨hQ, hk⟩ | ⟨hQ, hk⟩
  · -- `s = F^[k] z`: `Φ₀ s = Φ₀ z + k`
    have hsval : Φ₀ s = w + (m : ℂ) + (k : ℂ) := by
      have := iterate_abel hΦ₀ hQ
      rw [hk, hm] at this
      exact this
    refine ⟨s, hs, -(m + (k : ℤ)), ?_⟩
    rw [hsval]
    push_cast
    ring
  · -- `z = F^[k] s`: `Φ₀ z = Φ₀ s + k`
    have hsval : Φ₀ s = w + (m : ℂ) - (k : ℂ) := by
      have h := iterate_abel hΦ₀ hQ
      rw [hk, hm] at h
      linear_combination -h
    refine ⟨s, hs, (k : ℤ) - m, ?_⟩
    rw [hsval]
    push_cast
    ring

end Work.Fatou.Analysis
