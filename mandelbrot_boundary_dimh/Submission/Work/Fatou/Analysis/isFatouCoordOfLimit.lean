import Mathlib
import Submission.Work.Interfaces.Fatou
import Submission.Work.FatouCH.Cont.SradGeo
import Submission.Work.FatouCH.Cont.InjOfTendsto
import Submission.Work.FatouCH.FC.abelPair

/-!
# The limit of a sequence of Fatou coordinates is a Fatou coordinate (Shishikura A.2.1(iii))

Given near-translations `F n` on the moving regions `𝒬(b₁ n, b₂ n)` with univalent Fatou
coordinates `Φ n`, whose regions eventually swallow every compact subset of the limit region
`𝒬(c₁, c₂)`, and such that `Φ n → Ψ` locally uniformly on `𝒬(c₁, c₂)`, the limit `Ψ` is a Fatou
coordinate of `F₀` on `𝒬(c₁, c₂)`, provided `Ψ` satisfies the Abel equation
`Ψ (F₀ z) = Ψ z + 1`.

Two ingredients:

* holomorphy of `Ψ`: a locally uniform limit of functions holomorphic on the (eventual)
  regions is holomorphic, since differentiability is a local property and every point of the
  limit region has a compact neighbourhood eventually inside all the moving regions
  (`differentiableOn_of_eventually_differentiableOn_compacts`);
* injectivity of `Ψ`: Hurwitz's theorem in its injective-or-constant form
  (`Work.FatouCH.Cont.InjOfTendsto`), the non-constancy coming from the Abel equation evaluated
  at a point of `𝒬(c₁, c₂)` whose image is still in `𝒬(c₁, c₂)`
  (`Work.FatouCH.FC.abelPair`).

The Abel equation itself is carried by the statement as the hypothesis `hAbel`.
-/

namespace Work.Fatou.Analysis

open Set Filter Metric
open scoped Topology

/-- Holomorphy of the limit: if `F n → g` locally uniformly on an open `Q`, and every compact
subset of `Q` is eventually a set on which `F n` is holomorphic, then `g` is holomorphic on `Q`.

This is `TendstoLocallyUniformlyOn.differentiableOn` applied on a small ball around each point,
using the hypothesis on the singleton compact `closedBall z r` to obtain the differentiability of
`F n` near `z`. -/
theorem differentiableOn_of_eventually_differentiableOn_compacts {Q : Set ℂ} (hQ : IsOpen Q)
    {F : ℕ → ℂ → ℂ} {g : ℂ → ℂ} (hconv : TendstoLocallyUniformlyOn F g atTop Q)
    (hloc : ∀ K ⊆ Q, IsCompact K → ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) K) :
    DifferentiableOn ℂ g Q := by
  intro z hz
  obtain ⟨ε, hε, hεsub⟩ := Metric.mem_nhds_iff.mp (hQ.mem_nhds hz)
  have hr0 : 0 < ε / 2 := by linarith
  have hsub : closedBall z (ε / 2) ⊆ Q := fun w hw =>
    hεsub (by rw [mem_ball]; linarith [mem_closedBall.mp hw])
  have hev : ∀ᶠ n in atTop, DifferentiableOn ℂ (F n) (ball z (ε / 2)) :=
    (hloc (closedBall z (ε / 2)) hsub (isCompact_closedBall z (ε / 2))).mono fun _ hn =>
      hn.mono ball_subset_closedBall
  have hd : DifferentiableOn ℂ g (ball z (ε / 2)) :=
    (hconv.mono fun _ hw => hsub (ball_subset_closedBall hw)).differentiableOn hev isOpen_ball
  exact (hd.differentiableAt (ball_mem_nhds z hr0)).differentiableWithinAt

theorem isFatouCoordOfLimit {b₁ b₂ : ℕ → Option ℂ} {c₁ c₂ : Option ℂ} {F : ℕ → ℂ → ℂ} {F₀ : ℂ → ℂ}
    {Φ : ℕ → ℂ → ℂ} {Ψ : ℂ → ℂ}
    (hAdm0 : MandelDim.QAdm c₁ c₂)
    (hNT0 : MandelDim.NearTranslationOn F₀ (MandelDim.Qreg c₁ c₂))
    (hΦ : ∀ n, MandelDim.IsFatouCoordOn (F n) (Φ n) (MandelDim.Qreg (b₁ n) (b₂ n)))
    (hdom : ∀ K ⊆ MandelDim.Qreg c₁ c₂, IsCompact K →
      ∀ᶠ n in atTop, K ⊆ MandelDim.Qreg (b₁ n) (b₂ n))
    (hΨ : TendstoLocallyUniformlyOn Φ Ψ atTop (MandelDim.Qreg c₁ c₂))
    (hAbel : ∀ z ∈ MandelDim.Qreg c₁ c₂, F₀ z ∈ MandelDim.Qreg c₁ c₂ → Ψ (F₀ z) = Ψ z + 1) :
    MandelDim.IsFatouCoordOn F₀ Ψ (MandelDim.Qreg c₁ c₂) := by
  obtain ⟨hOpen, hPre, -, -, -, -, -, -, hpair⟩ :=
    Work.FatouCH.Cont.SradGeo (b₁ := c₁) (b₂ := c₂) hAdm0
  have hloc : ∀ K ⊆ MandelDim.Qreg c₁ c₂, IsCompact K →
      ∀ᶠ n in atTop, DifferentiableOn ℂ (Φ n) K := by
    intro K hKQ hK
    filter_upwards [hdom K hKQ hK] with n hn
    exact ((hΦ n).1).mono hn
  have hdiff : DifferentiableOn ℂ Ψ (MandelDim.Qreg c₁ c₂) :=
    differentiableOn_of_eventually_differentiableOn_compacts hOpen hΨ hloc
  -- `Ψ` is not constant: the Abel equation moves some point of `𝒬` by `+1`.
  obtain ⟨z₀, hz₀, hFz₀⟩ := Work.FatouCH.FC.abelPair hAdm0 hNT0
  have hne : Ψ (F₀ z₀) ≠ Ψ z₀ := by
    rw [hAbel z₀ hz₀ hFz₀]
    intro hh
    have h1 : (1 : ℂ) = 0 := by simpa using hh
    exact one_ne_zero h1
  have hnc : ∀ c : ℂ, ∃ z ∈ MandelDim.Qreg c₁ c₂, Ψ z ≠ c := by
    intro c
    by_cases h : Ψ z₀ = c
    · exact ⟨F₀ z₀, hFz₀, fun hh => hne (hh.trans h.symm)⟩
    · exact ⟨z₀, hz₀, h⟩
  exact ⟨hdiff, Work.FatouCH.Cont.InjOfTendsto hOpen hPre hΦ hdom hΨ hpair hnc, hAbel⟩

end Work.Fatou.Analysis
