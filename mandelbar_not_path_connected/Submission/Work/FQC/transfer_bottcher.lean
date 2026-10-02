import Mathlib
import Submission.Work.FQC.Defs
import Submission.Work.ParamRays.Bottcher

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology ComplexConjugate

noncomputable section

namespace Work.FQC

open LeanEval.ComplexAnalysis (Tantibar)
open Work.ParamRays (orbit orbit_succ Escaping escapingSet IsDynBottcher)

/-! ## Auxiliary lemmas about near-identity homeomorphisms of `ℂ`

These are the analytic facts about a homeomorphism `θ : ℂ ≃ₜ ℂ` that is `O(1/‖z‖)`-close
to the identity at infinity which the transport of a Böttcher coordinate along `θ` needs:

* `symm_decay` : the inverse `θ.symm` has the same decay;
* `tendsto_norm_comp_iff` : `θ` preserves the property of a sequence that its norms tend to
  infinity. -/

/-- On a closed ball, a continuous function `ℂ → ℂ` is bounded in norm. -/
lemma exists_norm_le_on_closedBall (f : ℂ → ℂ) (hf : Continuous f) (M : ℝ) :
    ∃ K : ℝ, ∀ w : ℂ, ‖w‖ ≤ M → ‖f w‖ ≤ K := by
  have hb : Bornology.IsBounded (f '' Metric.closedBall (0 : ℂ) M) :=
    ((isCompact_closedBall (0 : ℂ) M).image hf).isBounded
  obtain ⟨K, hK⟩ := hb.exists_norm_le
  exact ⟨K, fun w hw => hK (f w)
    (Set.mem_image_of_mem f (by simpa [Metric.mem_closedBall, dist_zero_right] using hw))⟩

/-- A property that holds eventually near infinity (that is, on a set of `cocompact ℂ`)
holds on the complement of some closed ball. -/
lemma exists_le_norm_of_eventually_cocompact {P : ℂ → Prop}
    (h : ∀ᶠ z : ℂ in Filter.cocompact ℂ, P z) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ z : ℂ, R ≤ ‖z‖ → P z := by
  obtain ⟨t, ht, htsub⟩ := Filter.mem_cocompact.mp h
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℂ)).mp ht.isBounded
  refine ⟨|R₀| + 1, by positivity, fun z hz => htsub ?_⟩
  intro hzt
  have h1 : z ∈ Metric.closedBall (0 : ℂ) R₀ := hR₀ hzt
  rw [Metric.mem_closedBall, dist_zero_right] at h1
  linarith [le_abs_self R₀]

/-- The inverse of a homeomorphism of `ℂ` which is `O(1/‖z‖)`-close to the identity at
infinity has the same decay. -/
lemma symm_decay (θ : ℂ ≃ₜ ℂ)
    (h : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖θ z - z‖ ≤ C / ‖z‖) :
    ∃ C R : ℝ, 0 ≤ C ∧ 1 ≤ R ∧ ∀ z : ℂ, R ≤ ‖z‖ → ‖θ.symm z - z‖ ≤ C / ‖z‖ := by
  obtain ⟨C, R, hCR⟩ := h
  set C₀ : ℝ := max C 0 with hC₀
  have hC₀nn : 0 ≤ C₀ := le_max_right C 0
  have hCR₀ : ∀ z : ℂ, R ≤ ‖z‖ → ‖θ z - z‖ ≤ C₀ / ‖z‖ := fun z hz =>
    le_trans (hCR z hz) (div_le_div_of_nonneg_right (le_max_left C 0) (norm_nonneg z))
  set R₁ : ℝ := max R 1 with hR₁
  have hR₁pos : 0 < R₁ := lt_of_lt_of_le one_pos (le_max_right R 1)
  have hR₁ge : R ≤ R₁ := le_max_left R 1
  obtain ⟨M, hM⟩ := exists_norm_le_on_closedBall (⇑θ) θ.continuous R₁
  have hMnn : 0 ≤ M := le_trans (norm_nonneg (θ 0))
    (hM 0 (by simpa [Metric.mem_closedBall] using hR₁pos.le))
  set R₂ : ℝ := max M (2 * C₀ / R₁) + 1 with hR₂
  have hR₂gtM : M < R₂ := by
    rw [hR₂]; linarith [le_max_left M (2 * C₀ / R₁)]
  have hR₂gt : 2 * C₀ / R₁ < R₂ := by
    rw [hR₂]; linarith [le_max_right M (2 * C₀ / R₁)]
  have hR₂pos : 0 < R₂ := lt_of_le_of_lt hMnn hR₂gtM
  refine ⟨2 * C₀, R₂, by positivity, by rw [hR₂]; linarith [le_max_left M (2 * C₀ / R₁)],
    fun z hz => ?_⟩
  have hznn : 0 < ‖z‖ := lt_of_lt_of_le hR₂pos hz
  set w : ℂ := θ.symm z with hwdef
  have hzw : θ w = z := by rw [hwdef]; exact θ.apply_symm_apply z
  have hwnorm_gt : R₁ < ‖w‖ := by
    by_contra hle
    have hle' : ‖w‖ ≤ R₁ := le_of_not_gt hle
    have h1 : ‖z‖ ≤ M := by
      have := hM w hle'
      rwa [hzw] at this
    linarith
  have hdecay_w : ‖z - w‖ ≤ C₀ / ‖w‖ := by
    have h := hCR₀ w (le_of_lt (lt_of_le_of_lt hR₁ge hwnorm_gt))
    rwa [hzw] at h
  have hwnorm_ge : ‖z‖ / 2 ≤ ‖w‖ := by
    by_contra hle
    have hlt : ‖w‖ < ‖z‖ / 2 := lt_of_not_ge hle
    have hwpos : 0 < ‖w‖ := lt_trans hR₁pos hwnorm_gt
    have h1 : ‖z‖ ≤ C₀ / ‖w‖ + ‖w‖ := by
      calc ‖z‖ = ‖(z - w) + w‖ := by rw [sub_add_cancel]
        _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
        _ ≤ C₀ / ‖w‖ + ‖w‖ := by linarith
    have h2 : ‖z‖ / 2 < C₀ / ‖w‖ := by linarith
    have h3 : ‖w‖ < 2 * C₀ / ‖z‖ := by
      rw [lt_div_iff₀ hznn]
      have h4 := (lt_div_iff₀ hwpos).mp h2
      linarith
    have hR2R1 : 2 * C₀ < R₂ * R₁ := (div_lt_iff₀ hR₁pos).mp hR₂gt
    have hlt_R1 : 2 * C₀ / ‖z‖ < R₁ := by
      rw [div_lt_iff₀ hznn]
      nlinarith [hz, hR2R1, hR₁pos]
    linarith
  have hhalf : 0 < ‖z‖ / 2 := by linarith
  calc ‖θ.symm z - z‖ = ‖w - z‖ := by rw [hwdef]
    _ = ‖z - w‖ := norm_sub_rev w z
    _ ≤ C₀ / ‖w‖ := hdecay_w
    _ ≤ C₀ / (‖z‖ / 2) := div_le_div_of_nonneg_left hC₀nn hhalf hwnorm_ge
    _ = 2 * C₀ / ‖z‖ := by field_simp

/-- A homeomorphism of `ℂ` which is `O(1/‖z‖)`-close to the identity at infinity preserves
the property of a sequence of `ℂ` that its norms tend to `∞`. -/
lemma tendsto_norm_comp_iff (θ : ℂ ≃ₜ ℂ)
    (h : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖θ z - z‖ ≤ C / ‖z‖) (u : ℕ → ℂ) :
    Filter.Tendsto (fun n : ℕ => ‖θ (u n)‖) Filter.atTop Filter.atTop ↔
      Filter.Tendsto (fun n : ℕ => ‖u n‖) Filter.atTop Filter.atTop := by
  obtain ⟨C, R, hCR⟩ := h
  set C₀ : ℝ := max C 0 with hC₀
  have hC₀nn : 0 ≤ C₀ := le_max_right C 0
  have hCR₀ : ∀ z : ℂ, R ≤ ‖z‖ → ‖θ z - z‖ ≤ C₀ / ‖z‖ := fun z hz =>
    le_trans (hCR z hz) (div_le_div_of_nonneg_right (le_max_left C 0) (norm_nonneg z))
  set D : ℝ := max R (max 2 (C₀ + 1)) with hD
  have hDnorm : ∀ w : ℂ, D ≤ ‖w‖ → ‖w‖ / 2 ≤ ‖θ w‖ := by
    intro w hw
    have hR : R ≤ ‖w‖ := le_trans (le_max_left R (max 2 (C₀ + 1))) hw
    have h2 : (2 : ℝ) ≤ ‖w‖ :=
      le_trans (le_max_left 2 (C₀ + 1)) (le_trans (le_max_right R (max 2 (C₀ + 1))) hw)
    have hC1 : C₀ + 1 ≤ ‖w‖ :=
      le_trans (le_max_right 2 (C₀ + 1)) (le_trans (le_max_right R (max 2 (C₀ + 1))) hw)
    have hd : ‖θ w - w‖ ≤ C₀ / ‖w‖ := hCR₀ w hR
    have hden : C₀ / ‖w‖ ≤ ‖w‖ / 2 := by
      rw [div_le_iff₀ (by linarith : (0 : ℝ) < ‖w‖)]
      nlinarith [hC1, hC₀nn, sq_nonneg (‖w‖ - (C₀ + 1)), sq_nonneg (C₀ + 1)]
    have htri : ‖w‖ ≤ ‖θ w‖ + ‖θ w - w‖ := by
      calc ‖w‖ = ‖θ w + (w - θ w)‖ := by rw [add_sub_cancel]
        _ ≤ ‖θ w‖ + ‖w - θ w‖ := norm_add_le _ _
        _ = ‖θ w‖ + ‖θ w - w‖ := by rw [norm_sub_rev]
    linarith
  constructor
  · intro hθ
    rw [Filter.tendsto_atTop_atTop] at hθ ⊢
    intro b
    by_cases hb : b ≤ 0
    · exact ⟨0, fun n _ => le_trans hb (norm_nonneg (u n))⟩
    · replace hb : 0 < b := not_le.mp hb
      obtain ⟨K, hK⟩ := exists_norm_le_on_closedBall (⇑θ) θ.continuous b
      obtain ⟨i, hi⟩ := hθ (K + 1)
      refine ⟨i, fun n hn => ?_⟩
      have h1 := hi n hn
      by_contra hcon
      replace hcon : ‖u n‖ < b := not_le.mp hcon
      have h2 := hK (u n) hcon.le
      linarith
  · intro hu
    rw [Filter.tendsto_atTop_atTop] at hu ⊢
    intro b
    obtain ⟨i, hi⟩ := hu (max D (2 * b))
    refine ⟨i, fun n hn => ?_⟩
    have h1 := hi n hn
    have h2 : D ≤ ‖u n‖ := le_trans (le_max_left D (2 * b)) h1
    have h3 : ‖u n‖ / 2 ≤ ‖θ (u n)‖ := hDnorm (u n) h2
    have h4 : b ≤ max D (2 * b) / 2 := by linarith [le_max_right D (2 * b)]
    have h5 : max D (2 * b) / 2 ≤ ‖u n‖ / 2 := by linarith
    linarith

/-! ## Transport of the orbits and of the escaping set -/

/-- `θ` conjugating the dynamics `T_c` and `T_{c₂}` transports orbits. -/
lemma theta_orbit {c c₂ : ℂ} (θ : ℂ → ℂ)
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) (z : ℂ) (n : ℕ) :
    θ (orbit c z n) = orbit c₂ (θ z) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [orbit_succ c z n, hconj, ih, orbit_succ c₂ (θ z) n]

/-- The escaping set is transported by a near-identity conjugacy. -/
lemma escaping_theta_iff {c c₂ : ℂ} (θ : ℂ ≃ₜ ℂ)
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z))
    (hdecay : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖θ z - z‖ ≤ C / ‖z‖) (z : ℂ) :
    Escaping c₂ (θ z) ↔ Escaping c z := by
  have h := tendsto_norm_comp_iff θ hdecay (fun n : ℕ => orbit c z n)
  have hfun : (fun n : ℕ => ‖θ (orbit c z n)‖) = fun n : ℕ => ‖orbit c₂ (θ z) n‖ := by
    funext n; rw [theta_orbit θ hconj z n]
  rw [hfun] at h
  exact h

/-! ## The Böttcher coordinate transports -/

theorem transfer_bottcher {c c₂ : ℂ} {φ : ℂ → ℂ} (θ : ℂ ≃ₜ ℂ) (hb : Work.ParamRays.IsDynBottcher c φ) (hconj : ∀ z : ℂ, θ (LeanEval.ComplexAnalysis.Tantibar c z) = LeanEval.ComplexAnalysis.Tantibar c₂ (θ z)) (hdecay : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖θ z - z‖ ≤ C / ‖z‖) : Work.ParamRays.IsDynBottcher c₂ (φ ∘ (θ.symm : ℂ → ℂ)) := by
  obtain ⟨hsC, hsR, hsCnn, hsR1, hsym⟩ := symm_decay θ hdecay
  have hesc : ∀ w : ℂ, Escaping c₂ w ↔ Escaping c (θ.symm w) := by
    intro w
    have h := escaping_theta_iff θ hconj hdecay (θ.symm w)
    rwa [θ.apply_symm_apply] at h
  refine ⟨?_, ?_, ?_⟩
  · refine ContinuousOn.comp hb.1 (θ.symm.continuous.continuousOn) ?_
    intro w hw
    exact (hesc w).mp hw
  · intro w hw
    have hw' : Escaping c (θ.symm w) := (hesc w).mp hw
    have h1 : Tantibar c (θ.symm w) = θ.symm (Tantibar c₂ w) :=
      (θ.eq_symm_apply).mpr (by rw [hconj (θ.symm w), θ.apply_symm_apply])
    simp only [Function.comp_apply]
    rw [← h1, hb.2.1 (θ.symm w) hw']
  · intro ε hε
    have hε3 : 0 < ε / 3 := by linarith
    obtain ⟨Rφ, hRφnn, hφthr⟩ := exists_le_norm_of_eventually_cocompact (hb.2.2 (ε / 3) hε3)
    set R₃ : ℝ := hsR + 2 * (Rφ + 1) + (hsC + 1) + (Real.sqrt (3 * hsC / ε) + 1) + 1 with hR₃
    refine Filter.mem_cocompact.mpr
      ⟨Metric.closedBall (0 : ℂ) R₃, isCompact_closedBall (0 : ℂ) R₃, ?_⟩
    intro z hz
    simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right] at hz
    have hzR : R₃ ≤ ‖z‖ := le_of_lt (not_le.mp hz)
    rw [hR₃] at hzR
    have hsqnn : 0 ≤ Real.sqrt (3 * hsC / ε) := Real.sqrt_nonneg _
    have b1 : hsR ≤ ‖z‖ := by linarith [hRφnn, hsCnn, hsqnn]
    have b2 : 2 * (Rφ + 1) ≤ ‖z‖ := by linarith [hsR1, hsCnn, hsqnn]
    have b3 : hsC + 1 ≤ ‖z‖ := by linarith [hsR1, hRφnn, hsqnn]
    have b4 : Real.sqrt (3 * hsC / ε) + 1 ≤ ‖z‖ := by linarith [hsR1, hRφnn, hsCnn]
    have hznn : 0 < ‖z‖ := by linarith [hsCnn, b3]
    set w : ℂ := θ.symm z with hwdef
    have hsymz : ‖w - z‖ ≤ hsC / ‖z‖ := by
      have h := hsym z b1
      rw [← hwdef] at h
      exact h
    have hwnorm_ge : ‖z‖ / 2 ≤ ‖w‖ := by
      have h2 : hsC / ‖z‖ ≤ ‖z‖ / 2 := by
        rw [div_le_iff₀ hznn]
        nlinarith [b3, hsCnn, sq_nonneg hsC]
      have h3 : ‖z‖ ≤ ‖w - z‖ + ‖w‖ := by
        calc ‖z‖ = ‖(z - w) + w‖ := by rw [sub_add_cancel]
          _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
          _ = ‖w - z‖ + ‖w‖ := by rw [norm_sub_rev]
      linarith
    have hRφw : Rφ ≤ ‖w‖ := by linarith [b2, hwnorm_ge]
    have hφw : ‖φ w - w‖ ≤ ε / 3 * ‖w‖ := hφthr w hRφw
    have hwnorm_le : ‖w‖ ≤ 2 * ‖z‖ := by
      have h3 : ‖w‖ ≤ ‖z‖ + ‖w - z‖ := by
        calc ‖w‖ = ‖(w - z) + z‖ := by rw [sub_add_cancel]
          _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
          _ = ‖z‖ + ‖w - z‖ := by ring
      have hbnd : hsC / ‖z‖ ≤ ‖z‖ := by
        rw [div_le_iff₀ hznn]
        nlinarith [b3, hsCnn, sq_nonneg hsC]
      linarith
    have hsmall : hsC / ‖z‖ ≤ ε / 3 * ‖z‖ := by
      rw [div_le_iff₀ hznn]
      have hsqrt : Real.sqrt (3 * hsC / ε) ≤ ‖z‖ := by linarith
      have hsq : 3 * hsC / ε ≤ ‖z‖ ^ 2 := by
        calc 3 * hsC / ε = (Real.sqrt (3 * hsC / ε)) ^ 2 := (Real.sq_sqrt (by positivity)).symm
          _ ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ hsqnn hsqrt 2
      rw [div_le_iff₀ hε] at hsq
      nlinarith
    have hmain : ‖φ w - z‖ ≤ ε * ‖z‖ := by
      have step1 : ‖φ w - z‖ ≤ ‖φ w - w‖ + ‖w - z‖ := by
        calc ‖φ w - z‖ = ‖(φ w - w) + (w - z)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖φ w - w‖ + ‖w - z‖ := norm_add_le _ _
      have step2 : ε / 3 * ‖w‖ ≤ ε / 3 * (2 * ‖z‖) :=
        mul_le_mul_of_nonneg_left hwnorm_le hε3.le
      linarith
    have hmain' : ‖φ (θ.symm z) - z‖ ≤ ε * ‖z‖ := by rw [← hwdef]; exact hmain
    simpa only [Set.mem_ofPred_eq, Function.comp_apply] using hmain'

end Work.FQC

end
