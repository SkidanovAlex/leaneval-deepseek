/-
# The tail induction of the ray-chain certificate: the ray `α₁` of a petal-entering chain lands
at the parabolic point

This is the `SeedCertRay` tail induction of `Submission/Work/NOTES_LEAD_mandelbar_noncusp.md`
§2.5, in the form in which the ray-chain certificate feeds it.

The data are the pieces `S k = seg hN α₁ (ρ (k+1)) (ρ k)` of the ray of angle `α₁` between the
levels `ρ (k+1) ≤ ρ k`, where `ρ (k+1) ^ 2 = ρ k`: consecutive pieces share the point of level
`ρ k`, and `S k` is compact and connected.  The chain certificate says that `S k` is covered by
`C k` for `k ≤ K + 9`, and the ten boxes `C K, …, C (K+9)` lie in the repelling petal
`Q_R = Petal z₁ A R` of the parabolic point `z₁`.

Because the holomorphic degree-`1024` map `F c = (T_c)^{10}` maps the ray of angle `θ` at level
`t` to the ray of angle `T^[10] θ` at level `t ^ 1024` (`rayPt_iterate`), and `T^[10] α₁ = α₁`,
the two petal conditions of the certificate

* `hP1`: no point of the sphere `‖z - z₁‖ = ρ₁` is mapped into the petal, and
* `hP2`: a point of the ball `‖z - z₁‖ ≤ ρ₁` whose image lies in the petal is itself in the petal,
  with its Fatou coordinate `w = -1/(A (z - z₁))` decreased by at least `δ`,

give, by induction on `j`, that *every* piece `S j` with `j ≥ K` lies in the petal, with
`Re w ≤ -R - ⌊(j-K)/10⌋ δ` on it.  The step uses exactly the ten-step recursion
`F c '' S j ⊆ S (j-10)` together with the intermediate-value argument
`preconnected_subset_closedBall`: the preconnected piece `S j`, which meets the previous piece
`S (j-1) ⊆ Q_R ⊆ {‖z - z₁‖ ≤ ρ₁}` at the level-`ρ j` point, cannot leave the ball, because
leaving it would force a point of the sphere, whose image in the petal is forbidden by `hP1`.

Consequently `‖z - z₁‖ ≤ 1/(‖A‖ (R + ⌊(j-K)/10⌋ δ))` on `S j`, and since the windows
`[ρ (j+1), ρ (j)]` tile `(1, ρ 1]` and the window index tends to infinity as the level tends to
`1`, the ray points of level `t → 1⁺` converge to `z₁`: the ray of angle `α₁` lands at `z₁`.
-/
import Mathlib
import Submission.Work.SeedCertRay.Basic
import Submission.Work.SeedCertRay.isPreconnected_seg
import Submission.Work.SeedCertRay.petal_tail_infra
import Submission.Work.ELRig.rayPt_iterate

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Set Function Filter
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.SeedCertRay

theorem landsN_of_petal_of_isDynBottcher {c : ℂ} {φ : ℂ → ℂ} (hN : Work.EL.DynB c φ) (hφ : Work.ParamRays.IsDynBottcher c φ) (z₁ A : ℂ) (R δ ρ₁ : ℝ) (ρ : ℕ → ℝ) (K : ℕ) (hρ : ∀ k, 1 < ρ (k + 1) ∧ ρ (k + 1) ^ 2 = ρ k) (hα : Work.EL.T^[10] Work.EL.alpha1 = Work.EL.alpha1) (C : ℕ → Set ℂ) (hC : ∀ k, k ≤ K + 9 → Work.SeedCertRay.seg hN Work.EL.alpha1 (ρ (k + 1)) (ρ k) ⊆ C k) (hQ : ∀ k, K ≤ k → k ≤ K + 9 → C k ⊆ Work.SeedCertRay.Petal z₁ A R) (hρ₁ : 0 < ρ₁) (hδ : 0 < δ) (hA : A ≠ 0) (hRQ : 1 ≤ R * ‖A‖ * ρ₁) (hP1 : ∀ z : ℂ, ‖z - z₁‖ = ρ₁ → Work.EL.F c z ∉ Work.SeedCertRay.Petal z₁ A R) (hP2 : ∀ z : ℂ, ‖z - z₁‖ ≤ ρ₁ → Work.EL.F c z ∈ Work.SeedCertRay.Petal z₁ A R → z ∈ Work.SeedCertRay.Petal z₁ A R ∧ (Work.SeedCertRay.fatou z₁ A z).re ≤ (Work.SeedCertRay.fatou z₁ A (Work.EL.F c z)).re - δ) : Work.EL.LandsN hN Work.EL.alpha1 z₁ := by
  have hApos : 0 < ‖A‖ := norm_pos_iff.mpr hA
  have hRpos : 0 < R := by
    by_contra hcon
    have hnn : 0 ≤ ‖A‖ * ρ₁ := mul_nonneg hApos.le hρ₁.le
    have hle : R * (‖A‖ * ρ₁) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hcon) hnn
    nlinarith [hRQ]
  have hanti : Antitone ρ := rho_antitone hρ
  -- ### Step 1: the tail induction
  have main : ∀ j, K ≤ j →
      (seg hN Work.EL.alpha1 (ρ (j + 1)) (ρ j) ⊆ Petal z₁ A R) ∧
      (∀ z ∈ seg hN Work.EL.alpha1 (ρ (j + 1)) (ρ j),
        (fatou z₁ A z).re ≤ -R - ((j - K) / 10 : ℕ) * δ) := by
    intro j
    induction j using Nat.strong_induction_on with
    | h j ih =>
      intro hjK
      by_cases hbase : j ≤ K + 9
      · -- the ten certified pieces
        have hsub : seg hN Work.EL.alpha1 (ρ (j + 1)) (ρ j) ⊆ Petal z₁ A R :=
          Subset.trans (hC j hbase) (hQ j hjK hbase)
        refine ⟨hsub, ?_⟩
        intro z hz
        have hzp : z ∈ Petal z₁ A R := hsub hz
        have hdiv : (j - K) / 10 = 0 := Nat.div_eq_of_lt (by omega)
        rw [hdiv]
        push_cast
        linarith [hzp.2]
      · -- the induction step
        push Not at hbase
        obtain ⟨d, rfl⟩ : ∃ d, j = K + 10 + d := ⟨j - (K + 10), by omega⟩
        -- indices
        have h1Kd : K + d < K + 10 + d := by omega
        have h1K9d : K + 9 + d < K + 10 + d := by omega
        have hIHd := ih (K + d) h1Kd (by omega)
        have hIH9 := ih (K + 9 + d) h1K9d (by omega)
        -- the level relations for the `F`-image
        have hp1 : ρ (K + d + 1) = (ρ (K + 10 + d + 1)) ^ (1024 : ℕ) := by
          rw [show K + 10 + d + 1 = (K + d + 1) + 10 from by omega]
          exact (rho_pow_ten hρ (K + d + 1)).symm
        have hp2 : ρ (K + d) = (ρ (K + 10 + d)) ^ (1024 : ℕ) := by
          rw [show K + 10 + d = (K + d) + 10 from by omega]
          exact (rho_pow_ten hρ (K + d)).symm
        have hle1 : ρ (K + 10 + d + 1) ≤ ρ (K + 10 + d) := hanti (by omega)
        have hle2 : ρ (K + 10 + d) ≤ ρ (K + 9 + d) := hanti (by omega)
        -- the `F`-image of a piece is the piece ten steps back
        have hFmap : ∀ z ∈ seg hN Work.EL.alpha1 (ρ (K + 10 + d + 1)) (ρ (K + 10 + d)),
            Work.EL.F c z ∈ seg hN Work.EL.alpha1 (ρ (K + d + 1)) (ρ (K + d)) := by
          rintro z ⟨t, ht, rfl⟩
          exact F_mem_seg hN hφ hα hp1 hp2 (hρ (K + 10 + d)).1 ht
        -- the piece meets the previous piece, in the petal
        have ha_mem : Work.EL.rayPt hN Work.EL.alpha1 (ρ (K + 10 + d))
            ∈ seg hN Work.EL.alpha1 (ρ (K + 10 + d + 1)) (ρ (K + 10 + d)) :=
          ⟨ρ (K + 10 + d), ⟨hle1, le_rfl⟩, rfl⟩
        have ha_prev : Work.EL.rayPt hN Work.EL.alpha1 (ρ (K + 10 + d))
            ∈ seg hN Work.EL.alpha1 (ρ ((K + 9 + d) + 1)) (ρ (K + 9 + d)) := by
          refine ⟨ρ (K + 10 + d), ⟨?_, hle2⟩, rfl⟩
          exact le_of_eq (congrArg ρ (by omega))
        have haball : ‖Work.EL.rayPt hN Work.EL.alpha1 (ρ (K + 10 + d)) - z₁‖ ≤ ρ₁ := by
          have h := petal_subset_closedBall hA hρ₁ hRQ (hIH9.1 ha_prev)
          rwa [Metric.mem_closedBall, dist_eq_norm] at h
        -- the piece lies in the ball
        have hball : seg hN Work.EL.alpha1 (ρ (K + 10 + d + 1)) (ρ (K + 10 + d))
            ⊆ Metric.closedBall z₁ ρ₁ :=
          preconnected_subset_closedBall
            (isPreconnected_seg hN Work.EL.alpha1 (ρ (K + 10 + d + 1)) (ρ (K + 10 + d))
              (hρ (K + 10 + d)).1)
            ⟨Work.EL.rayPt hN Work.EL.alpha1 (ρ (K + 10 + d)), ha_mem, haball⟩
            (fun z _ hzρ => hP1 z hzρ)
            (fun z hz => hIHd.1 (hFmap z hz))
        have hzball : ∀ z ∈ seg hN Work.EL.alpha1 (ρ (K + 10 + d + 1)) (ρ (K + 10 + d)),
            ‖z - z₁‖ ≤ ρ₁ := by
          intro z hz
          have h := hball hz
          rwa [Metric.mem_closedBall, dist_eq_norm] at h
        refine ⟨fun z hz => (hP2 z (hzball z hz) (hIHd.1 (hFmap z hz))).1, fun z hz => ?_⟩
        · obtain ⟨-, hdrop⟩ := hP2 z (hzball z hz) (hIHd.1 (hFmap z hz))
          have hprev := hIHd.2 (Work.EL.F c z) (hFmap z hz)
          have hidx1 : (K + d - K) / 10 = d / 10 := by congr 1; omega
          have hidx2 : (K + 10 + d - K) / 10 = d / 10 + 1 := by
            rw [show K + 10 + d - K = 10 + d from by omega]
            omega
          have hexp : ((d / 10 + 1 : ℕ) : ℝ) * δ = ((d / 10 : ℕ) : ℝ) * δ + δ := by
            push_cast; ring
          rw [hidx1] at hprev
          rw [hidx2, hexp]
          linarith
  have hmain : ∀ j, K ≤ j →
      seg hN Work.EL.alpha1 (ρ (j + 1)) (ρ j) ⊆ Petal z₁ A R := fun j hj => (main j hj).1
  have hdrif : ∀ j, K ≤ j → ∀ z ∈ seg hN Work.EL.alpha1 (ρ (j + 1)) (ρ j),
      (fatou z₁ A z).re ≤ -R - ((j - K) / 10 : ℕ) * δ := fun j hj => (main j hj).2
  -- ### Step 2: the ray points of small level converge to `z₁`
  rw [Work.EL.LandsN]
  refine Metric.tendsto_nhds.mpr ?_
  intro ε hε
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, (‖A‖ * (R + n₀ * δ))⁻¹ < ε := by
    obtain ⟨m, hm⟩ := exists_nat_gt ((ε⁻¹ / ‖A‖ - R) / δ)
    refine ⟨m + 1, ?_⟩
    have hm' : (ε⁻¹ / ‖A‖ - R) / δ < ((m : ℝ) + 1) := by
      have : (m : ℝ) < (m : ℝ) + 1 := by linarith
      linarith
    have hmul : (ε⁻¹ / ‖A‖ - R) < ((m : ℝ) + 1) * δ := by
      have := mul_lt_mul_of_pos_right hm' hδ
      rwa [div_mul_cancel₀ _ (ne_of_gt hδ)] at this
    have hlt : ε⁻¹ / ‖A‖ < R + ((m : ℝ) + 1) * δ := by linarith
    have hmul2 : ε⁻¹ < ‖A‖ * (R + ((m : ℝ) + 1) * δ) := by
      have h := mul_lt_mul_of_pos_left hlt hApos
      have heq : ‖A‖ * (ε⁻¹ / ‖A‖) = ε⁻¹ := by field_simp
      rw [heq] at h
      exact h
    refine (inv_lt_comm₀ (a := ‖A‖ * (R + (((m + 1 : ℕ) : ℝ)) * δ)) (b := ε)
      (by positivity) hε).mpr ?_
    push_cast
    linarith
  -- only levels `t` below the window of `K + 10 n₀ + 1` are relevant
  have hν : Set.Iio (ρ (K + 10 * n₀ + 1 + 1)) ∈ nhds (1 : ℝ) :=
    isOpen_Iio.mem_nhds (hρ (K + 10 * n₀ + 1)).1
  filter_upwards [self_mem_nhdsWithin, Filter.Eventually.filter_mono nhdsWithin_le_nhds hν]
    with t ht1 ht2
  have ht : 1 < t := ht1
  obtain ⟨j, hjge, hjlow, hjup⟩ :=
    rho_window hρ ht (by omega : 1 ≤ K + 10 * n₀ + 1) ht2
  have hKj : K ≤ j := by omega
  have hjs : Work.EL.rayPt hN Work.EL.alpha1 t
      ∈ seg hN Work.EL.alpha1 (ρ (j + 1)) (ρ j) := ⟨t, ⟨hjlow, hjup⟩, rfl⟩
  have hnorm := norm_sub_le_of_fatou_bound hA hRpos hδ ((j - K) / 10)
    (hmain j hKj hjs) (hdrif j hKj _ hjs)
  have hleidx : n₀ ≤ (j - K) / 10 := by
    rw [Nat.le_div_iff_mul_le (by norm_num : 0 < 10)]
    omega
  have hbound : (‖A‖ * (R + ((j - K) / 10 : ℕ) * δ))⁻¹ ≤ (‖A‖ * (R + n₀ * δ))⁻¹ := by
    refine (inv_le_inv₀ (a := ‖A‖ * (R + ((j - K) / 10 : ℕ) * δ))
      (b := ‖A‖ * (R + n₀ * δ)) (by positivity) (by positivity)).mpr ?_
    have hmid : (n₀ : ℝ) * δ ≤ ((j - K) / 10 : ℕ) * δ :=
      mul_le_mul_of_nonneg_right
        (show (n₀ : ℝ) ≤ ((j - K) / 10 : ℕ) by exact_mod_cast hleidx) hδ.le
    have hgoal : R + n₀ * δ ≤ R + ((j - K) / 10 : ℕ) * δ := by linarith
    exact mul_le_mul_of_nonneg_left hgoal hApos.le
  calc dist (Work.EL.rayPt hN Work.EL.alpha1 t) z₁
      = ‖Work.EL.rayPt hN Work.EL.alpha1 t - z₁‖ := dist_eq_norm _ _
    _ ≤ (‖A‖ * (R + ((j - K) / 10 : ℕ) * δ))⁻¹ := hnorm
    _ ≤ (‖A‖ * (R + n₀ * δ))⁻¹ := hbound
    _ < ε := hn₀

end Work.SeedCertRay
