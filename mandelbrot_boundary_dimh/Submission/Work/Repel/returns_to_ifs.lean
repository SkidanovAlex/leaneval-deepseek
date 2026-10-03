import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Repel.Spec
import Submission.Work.Repel.invFunOn_differentiableOn

/-!
# REPEL: the return data of §6 gives a conformal IFS

`Work.Repel.ReturnData f p r K` records `N` disjoint islands `Ω i ⊆ ball p (r / 2)` on each of
which the iterate `f^[n i]` maps onto `ball p r`, is injective and has derivative bounded by `K`
on a ball `ball (u i) (δ i) ⊇ Ω i`.  This file turns that data into a conformal IFS: the branch
`τ i` is the inverse of `f^[n i]` on `ball p r`, taking values in `Ω i`.

Everything is elementary: `τ i` is `Function.invFunOn (f^[n i]) (Ω i)`, which agrees on
`ball p r` with `Function.invFunOn (f^[n i]) (ball (u i) (δ i))` (both are inverse branches, and
the latter is single-valued by injectivity on the open ball).  The inverse branch of an injective
holomorphic function on an open set is holomorphic (`Work.Repel.invFunOn_differentiableOn`), and
its derivative is the reciprocal of the derivative of the map, giving the lower bound
`(K')⁻¹ ≤ ‖deriv (τ i) z‖` from `‖deriv (f^[n i]) (τ i z)‖ ≤ K ≤ K'`.
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

noncomputable section

theorem returns_to_ifs {f : ℂ → ℂ} {p : ℂ} {r K K' : ℝ} (hr : 0 < r) (hKK : K ≤ K')
    (hK' : 1 < K') (RD : Work.Repel.ReturnData f p r K) :
    ∃ τ : Fin RD.N → ℂ → ℂ, MandelDim.IsConformalIFS RD.N τ p r K' ∧
      ∀ i, ∀ z ∈ Metric.ball p r, f^[RD.n i] (τ i z) = z := by
  classical
  -- the inverse branch of `f^[RD.n i]` on the island `RD.Ω i`
  let τ : Fin RD.N → ℂ → ℂ := fun i z => Function.invFunOn (f^[RD.n i]) (RD.Ω i) z
  have hmem : ∀ (i : Fin RD.N) (z : ℂ), z ∈ ball p r → τ i z ∈ RD.Ω i := fun i z hz =>
    Function.invFunOn_mem (RD.hsurj i hz)
  have happ : ∀ (i : Fin RD.N) (z : ℂ), z ∈ ball p r → f^[RD.n i] (τ i z) = z := fun i z hz =>
    Function.invFunOn_eq (RD.hsurj i hz)
  -- for each branch: differentiability on the target ball and the derivative bound
  have key : ∀ i : Fin RD.N, DifferentiableOn ℂ (τ i) (ball p r) ∧
      ∀ z ∈ ball p (r / 2), K'⁻¹ ≤ ‖deriv (τ i) z‖ := by
    intro i
    set g : ℂ → ℂ := f^[RD.n i] with hg
    set B : Set ℂ := ball (RD.u i) (RD.δ i) with hB
    set h : ℂ → ℂ := Function.invFunOn g B with hh
    have hBopen : IsOpen B := Metric.isOpen_ball
    have hinjB : InjOn g B := RD.hinj i
    have hdiffB : DifferentiableOn ℂ g B := RD.hdiff i
    have hsub : ball p r ⊆ g '' B := fun z hz =>
      ⟨τ i z, RD.hΩsub i (hmem i z hz), happ i z hz⟩
    have hinb : ∀ z ∈ ball p r, ∃ x ∈ B, g x = z := fun z hz =>
      ⟨τ i z, RD.hΩsub i (hmem i z hz), happ i z hz⟩
    have hhdiff : DifferentiableOn ℂ h (ball p r) :=
      (invFunOn_differentiableOn hBopen hinjB hdiffB).mono hsub
    have hagree : ∀ z ∈ ball p r, τ i z = h z := by
      intro z hz
      have hex := hinb z hz
      have h₁ : g (τ i z) = z := happ i z hz
      have h₂ : g (h z) = z := Function.invFunOn_eq hex
      exact hinjB (RD.hΩsub i (hmem i z hz)) (Function.invFunOn_mem hex) (h₁.trans h₂.symm)
    refine ⟨?_, ?_⟩
    · exact hhdiff.congr fun z hz => hagree z hz
    · intro z hz
      have hzr : z ∈ ball p r := Metric.ball_subset_ball (by linarith) hz
      have hball : ball p r ∈ 𝓝 z := IsOpen.mem_nhds Metric.isOpen_ball hzr
      have hev : τ i =ᶠ[𝓝 z] h := Filter.eventually_of_mem hball fun w hw => hagree w hw
      have hderiv_eq : deriv (τ i) z = deriv h z := hev.deriv_eq
      have hAt : DifferentiableAt ℂ h z := hhdiff.differentiableAt hball
      have hbAt : DifferentiableAt ℂ g (h z) :=
        hdiffB.differentiableAt
          (IsOpen.mem_nhds Metric.isOpen_ball (Function.invFunOn_mem (hinb z hzr)))
      -- the composite `g ∘ h` is the identity near `z`, so its derivative is `1`
      have hcomp : (fun w => g (h w)) =ᶠ[𝓝 z] (fun w => w) :=
        Filter.eventually_of_mem hball fun w hw => Function.invFunOn_eq (hinb w hw)
      have h1 : deriv (fun w => g (h w)) z = 1 := by
        rw [hcomp.deriv_eq]
        exact congr_fun deriv_id'' z
      have hchain : deriv (fun w => g (h w)) z = deriv g (h z) * deriv h z :=
        deriv_comp z hbAt hAt
      have hab : deriv g (h z) * deriv h z = 1 := by rw [← hchain]; exact h1
      have ha_ne : deriv g (h z) ≠ 0 := by
        intro h0
        rw [h0, zero_mul] at hab
        exact zero_ne_one hab
      have hb : deriv h z = (deriv g (h z))⁻¹ := eq_inv_of_mul_eq_one_right hab
      have hmemΩ : h z ∈ RD.Ω i := by rw [← hagree z hzr]; exact hmem i z hzr
      have hbound : ‖deriv g (h z)‖ ≤ K := RD.hderiv i (h z) hmemΩ
      have hpos : 0 < ‖deriv g (h z)‖ := norm_pos_iff.mpr ha_ne
      have hroot : deriv (τ i) z = (deriv g (h z))⁻¹ := by rw [hderiv_eq, hb]
      rw [hroot, norm_inv]
      exact inv_anti₀ hpos (le_trans hbound hKK)
  refine ⟨τ, ⟨hr, hK', (fun i => (key i).1), ?_, ?_, ?_, (fun i => (key i).2)⟩, happ⟩
  · -- injectivity of the branch
    intro i z₁ hz₁ z₂ hz₂ heq
    have h₁ : f^[RD.n i] (τ i z₁) = z₁ := happ i z₁ hz₁
    have h₂ : f^[RD.n i] (τ i z₂) = z₂ := happ i z₂ hz₂
    rw [heq] at h₁
    exact h₁.symm.trans h₂
  · -- the branch maps the target ball into the half-ball
    intro i z hz
    exact RD.hΩhalf i (hmem i z hz)
  · -- disjointness of the images, from the disjointness of the balls `ball (u i) (δ i)`
    intro i j hij
    rw [Set.disjoint_left]
    intro y hy₁ hy₂
    rw [Set.mem_image] at hy₁ hy₂
    obtain ⟨z₁, hz₁, hz₁'⟩ := hy₁
    obtain ⟨z₂, hz₂, hz₂'⟩ := hy₂
    have h₁ : τ i z₁ ∈ ball (RD.u i) (RD.δ i) := RD.hΩsub i (hmem i z₁ hz₁)
    have h₂ : τ j z₂ ∈ ball (RD.u j) (RD.δ j) := RD.hΩsub j (hmem j z₂ hz₂)
    have hne : τ i z₁ ≠ τ j z₂ := by
      intro heq
      refine Set.disjoint_left.mp (RD.hdisj i j hij) h₁ ?_
      rw [heq]
      exact h₂
    exact hne (by rw [hz₁', hz₂'])

end

end Work.Repel
