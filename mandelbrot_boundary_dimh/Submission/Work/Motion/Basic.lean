import Mathlib
import Submission.Work.Interfaces.Basic

/-!
# Holomorphic motion of a dynamical IFS — basic setup
-/

namespace Work.Motion

open MandelDim
open LeanEval.Dynamics.MandelbrotBoundary
open Set Metric Filter

noncomputable section

variable {c₀ : ℂ} {N : ℕ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {r K : ℝ}

/-- The compact core `⋃ i, τ i '' closedBall p (r/2)` is contained in a strictly smaller ball
`closedBall p s`, `s < r/2`. -/
theorem exists_image_bound (hN : 1 ≤ N) (hIFS : IsConformalIFS N τ p r K) :
    ∃ s : ℝ, s < r / 2 ∧ ∀ i, MapsTo (τ i) (closedBall p (r / 2)) (closedBall p s) := by
  obtain ⟨hr, hK, hdiff, hinj, hmaps, hdisj, hder⟩ := hIFS
  have hsub : closedBall p (r / 2) ⊆ ball p r := by
    intro z hz
    rw [mem_closedBall] at hz
    rw [mem_ball]
    linarith
  have hsubE : closedBall p (r / 2) ⊆ ball p r := hsub
  have hper : ∀ i, ∃ s : ℝ, s < r / 2 ∧ MapsTo (τ i) (closedBall p (r / 2)) (closedBall p s) := by
    intro i
    have hcont : ContinuousOn (fun z => ‖τ i z - p‖) (closedBall p (r / 2)) :=
      (((hdiff i).continuousOn.mono hsubE).sub continuousOn_const).norm
    obtain ⟨z₀, hz₀, hmax⟩ := (isCompact_closedBall p _).exists_isMaxOn
      ⟨p, by rw [mem_closedBall]; simp; linarith⟩ hcont
    have hz₀' : z₀ ∈ ball p r := hsubE hz₀
    have hlt : ‖τ i z₀ - p‖ < r / 2 := by
      have h1 := hmaps i hz₀'
      rw [mem_ball] at h1
      rwa [dist_eq_norm] at h1
    refine ⟨‖τ i z₀ - p‖, hlt, fun z hz => ?_⟩
    rw [mem_closedBall, dist_eq_norm]
    exact hmax hz
  choose s hs using hper
  have hne : (Finset.univ : Finset (Fin N)).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    exact Fin.pos_iff_nonempty.mp (by omega)
  refine ⟨Finset.univ.sup' hne s, ?_, ?_⟩
  · rw [Finset.sup'_lt_iff]
    intro i _
    exact (hs i).1
  · intro i z hz
    rw [mem_closedBall, dist_eq_norm]
    have h1 : ‖τ i z - p‖ ≤ s i := by
      have := (hs i).2 hz
      rwa [mem_closedBall, dist_eq_norm] at this
    exact le_trans h1 (Finset.le_sup' s (Finset.mem_univ i))

end

end Work.Motion

namespace Work.Motion

open MandelDim
open LeanEval.Dynamics.MandelbrotBoundary
open Set Metric Filter

noncomputable section

variable {c₀ : ℂ} {N : ℕ} {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {r K : ℝ}

/-- Bundled data for the perturbed ("moving") inverse branches of a dynamical IFS.

`τc c i` is the local inverse branch of `(Tc c)^[n i]` for the parameter `c`: it is holomorphic
and injective on `ball p r₁` (`r/2 < r₁ < r`) and satisfies `(Tc c)^[n i](τc c i z) = z` there.
The images of the core `closedBall p (r/2)` lie in `closedBall p s`, `s < r/2`, the derivative is
between `β > 0` and `θ < 1` there, the branches are Lipschitz in `c` with constant `Lc`, and their
derivatives are Lipschitz in `(c,z)` with constant `G`.  At `c = c₀` the branches are the given
`τ`. -/
structure PertData (c₀ : ℂ) (N : ℕ) (τ : Fin N → ℂ → ℂ) (n : Fin N → ℕ) (p : ℂ) (r K : ℝ)
    where
  ρ : ℝ
  hρ : 0 < ρ
  r₁ : ℝ
  hr₁ : r / 2 < r₁
  hr₁' : r₁ < r
  s : ℝ
  hs0 : 0 ≤ s
  hsr : s < r / 2
  θ : ℝ
  hθ0 : 0 ≤ θ
  hθ1 : θ < 1
  β : ℝ
  hβ : 0 < β
  Lc : ℝ
  hLc : 0 ≤ Lc
  G : ℝ
  hG : 0 ≤ G
  τc : ℂ → Fin N → ℂ → ℂ
  base : ∀ i z, z ∈ ball p r₁ → τc c₀ i z = τ i z
  hol : ∀ i, DifferentiableOn ℂ (fun q : ℂ × ℂ => τc q.1 i q.2) (ball c₀ ρ ×ˢ ball p r₁)
  dyn : ∀ c ∈ ball c₀ ρ, ∀ i z, z ∈ ball p r₁ → (Tc c)^[n i] (τc c i z) = z
  img : ∀ c ∈ ball c₀ ρ, ∀ i, MapsTo (τc c i) (closedBall p (r / 2)) (closedBall p s)
  deriv_le : ∀ c ∈ ball c₀ ρ, ∀ i, ∀ z ∈ closedBall p (r / 2), ‖deriv (τc c i) z‖ ≤ θ
  deriv_ge : ∀ c ∈ ball c₀ ρ, ∀ i, ∀ z ∈ closedBall p (r / 2), β ≤ ‖deriv (τc c i) z‖
  lips_c : ∀ i, ∀ z ∈ closedBall p (r / 2), ∀ c ∈ ball c₀ ρ, ∀ c' ∈ ball c₀ ρ,
      ‖τc c i z - τc c' i z‖ ≤ Lc * ‖c - c'‖
  deriv_lips : ∀ i, ∀ z ∈ closedBall p (r / 2), ∀ z' ∈ closedBall p (r / 2),
      ∀ c ∈ ball c₀ ρ, ∀ c' ∈ ball c₀ ρ,
      ‖deriv (τc c i) z - deriv (τc c' i) z'‖ ≤ G * (‖c - c'‖ + ‖z - z'‖)

end

end Work.Motion
