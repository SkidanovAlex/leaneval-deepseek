import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.dzbar_symm_le
import Submission.Work.MRMT.Found.norm_symm_sub_le
import Submission.Work.MRMT.Found.open_subset_closedBall_of_frontier_subset
import Submission.Work.MRMT.Found.courantLebesgue_uniform
import Submission.Work.MRMT.Found.norm_image_le_of_decay
import Submission.Work.MRMT.Found.surjective_of_tendstoLocallyUniformly_of_decay
import Submission.Work.MRMT.Found.injective_of_equicontinuous_symm
import Submission.Work.MRMT.Found.tendstoLocallyUniformly_of_equicontinuous_pointwise
import Submission.Work.MRMT.Found.equicontinuous_symm_of_beltrami

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Filter Topology

namespace Work.MRMT.Found

theorem inverse_limit {μn : ℕ → ℂ → ℂ} {k M Cd Rd : ℝ} {Fn : ℕ → ℂ ≃ₜ ℂ} {φ : ℂ → ℂ}
    (hk0 : 0 ≤ k) (hk1 : k < 1) (hM0 : 0 ≤ M) (hCd : 0 ≤ Cd) (hRd : 1 ≤ Rd)
    (hμnB : ∀ n z, ‖μn n z‖ ≤ k)
    (hμnSp : ∀ n z, μn n z ≠ 0 → ‖z‖ ≤ M)
    (hFC : ∀ n, ContDiff ℝ 1 (Fn n : ℂ → ℂ))
    (hFCS : ∀ n, ContDiff ℝ 1 ((Fn n).symm : ℂ → ℂ))
    (hFB : ∀ n z, Work.MRMT.dzbar (Fn n : ℂ → ℂ) z = μn n z * Work.MRMT.dz (Fn n : ℂ → ℂ) z)
    (hdec : ∀ n : ℕ, ∀ z : ℂ, Rd ≤ ‖z‖ → ‖Fn n z - z‖ ≤ Cd / ‖z‖)
    (hconv : TendstoLocallyUniformly (fun n => (Fn n : ℂ → ℂ)) φ Filter.atTop) :
    ∃ ψ : ℂ → ℂ, Continuous ψ ∧
      TendstoLocallyUniformly (fun n => ((Fn n).symm : ℂ → ℂ)) ψ Filter.atTop ∧
      (∀ z : ℂ, φ (ψ z) = z) ∧ (∀ w : ℂ, ψ (φ w) = w) := by
  classical
  -- ### 0. The limit `φ` is continuous and is the pointwise limit of the `Fn`.
  have hφc : Continuous φ :=
    hconv.continuous ((Filter.Eventually.of_forall fun n => (Fn n).continuous).frequently)
  have hptF : ∀ z : ℂ, Filter.Tendsto (fun n => (Fn n : ℂ → ℂ) z) Filter.atTop (nhds (φ z)) :=
    fun z => hconv.tendsto_comp hφc.continuousAt tendsto_const_nhds
  -- ### 1. Equicontinuity of the inverse family (Courant--Lebesgue).
  have heq : ∀ N : ℝ, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 4 ∧
      ∀ n : ℕ, ∀ u v : ℂ, ‖v‖ ≤ N → ‖u - v‖ < δ →
        ‖((Fn n).symm : ℂ → ℂ) u - ((Fn n).symm : ℂ → ℂ) v‖ < ε :=
    equicontinuous_symm_of_beltrami hk0 hk1 hCd hRd hμnB hFC hFCS hFB hdec
  -- ### 2. Injectivity and surjectivity of `φ`.
  have hinj : Function.Injective φ :=
    injective_of_equicontinuous_symm hCd hRd hdec hptF heq
  have hsurj : Function.Surjective φ :=
    surjective_of_tendstoLocallyUniformly_of_decay hRd hCd hdec hconv
  -- ### 3. The inverse of `φ`.
  let Ψ : ℂ ≃ ℂ := Equiv.ofBijective φ ⟨hinj, hsurj⟩
  -- ### 4. The inverses converge pointwise to `Ψ.symm`.
  have hptψ : ∀ w : ℂ,
      Filter.Tendsto (fun n => ((Fn n).symm : ℂ → ℂ) w) Filter.atTop (nhds ((Ψ.symm : ℂ → ℂ) w)) := by
    intro w
    rw [Metric.tendsto_nhds]
    intro ε hε
    obtain ⟨δ, hδpos, hδle, hδ⟩ := heq (‖w‖ + 1) ε hε
    have hzw : φ ((Ψ.symm : ℂ → ℂ) w) = w :=
      Equiv.ofBijective_apply_symm_apply φ ⟨hinj, hsurj⟩ w
    have hlim : Filter.Tendsto (fun n : ℕ => (Fn n : ℂ → ℂ) ((Ψ.symm : ℂ → ℂ) w))
        Filter.atTop (nhds w) := by
      have h := hptF ((Ψ.symm : ℂ → ℂ) w)
      rwa [hzw] at h
    have h1 : ∀ᶠ n : ℕ in Filter.atTop,
        ‖(Fn n : ℂ → ℂ) ((Ψ.symm : ℂ → ℂ) w)‖ ≤ ‖w‖ + 1 := by
      have h2 : ∀ᶠ n : ℕ in Filter.atTop,
          dist ((Fn n : ℂ → ℂ) ((Ψ.symm : ℂ → ℂ) w)) w < 1 :=
        Metric.tendsto_nhds.mp hlim 1 one_pos
      filter_upwards [h2] with n hn
      rw [dist_eq_norm] at hn
      have h3 : ‖(Fn n : ℂ → ℂ) ((Ψ.symm : ℂ → ℂ) w) - w + w‖
          ≤ ‖(Fn n : ℂ → ℂ) ((Ψ.symm : ℂ → ℂ) w) - w‖ + ‖w‖ := norm_add_le _ _
      rw [sub_add_cancel] at h3
      linarith
    have h2 : ∀ᶠ n : ℕ in Filter.atTop,
        ‖(Fn n : ℂ → ℂ) ((Ψ.symm : ℂ → ℂ) w) - w‖ < δ := by
      have h := Metric.tendsto_nhds.mp hlim δ hδpos
      filter_upwards [h] with n hn
      rwa [dist_eq_norm] at hn
    filter_upwards [h1, h2] with n hn1 hn2
    rw [dist_eq_norm]
    have hδn := hδ n w ((Fn n : ℂ → ℂ) ((Ψ.symm : ℂ → ℂ) w)) hn1 (by rw [norm_sub_rev]; exact hn2)
    rw [Homeomorph.symm_apply_apply] at hδn
    exact hδn
  -- ### 5. Local uniform convergence and continuity.
  obtain ⟨hψc, hlu⟩ :=
    tendstoLocallyUniformly_of_equicontinuous_pointwise heq hptψ
  refine ⟨(Ψ.symm : ℂ → ℂ), hψc, hlu, ?_, ?_⟩
  · intro z
    exact Equiv.ofBijective_apply_symm_apply φ ⟨hinj, hsurj⟩ z
  · intro w
    exact Equiv.ofBijective_symm_apply_apply φ ⟨hinj, hsurj⟩ w

end Work.MRMT.Found
