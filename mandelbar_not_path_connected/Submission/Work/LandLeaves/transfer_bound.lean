import Mathlib
import Submission.Work.LandLeaves.rayPtCore
import Submission.Work.LandLeaves.tendsto_critRayLevelPoint
import Submission.Work.LandLeaves.rayAccum_entry

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter
open scoped Topology

namespace Work.LandLeaves

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

noncomputable section

/-! ## Transfer of the anchor bound between nearby parameters

The statement `Work.LandLeaves.transfer_bound` says that if at a parameter `c ∈ M*` every
critical-ray level point of angle `θ` with level in a window `[ℓ, η₀]` is within `ρ / 2` of a
point `y`, then for every parameter `f` close enough to `c` the corresponding level points
(with levels in the same window) are within `ρ` of a point `yf f` which is close to `y`.

The mathematical content is the *joint* continuity of the level point
`(f, s) ↦ {z ∈ critDomain f : φ_f z = s · rayDir θ}` at the parameter `c`, uniformly in the
level `s ∈ [ℓ, η₀]`.  We prove it by compactness of `[ℓ, η₀]` and the sequential (cluster
point) lemma `exists_cluster_critRayLevel` below. -/

/-- For a parameter in the mandelbar the critical Böttcher level of the critical point is `1`. -/
theorem exp_greenFun_zero_eq_one_of_mem_mandelbar {c : ℂ} (hc : c ∈ Mandelbar) :
    Real.exp (Work.ParamRays.greenFun c 0) = 1 := by
  have h : Work.ParamRays.greenFun c 0 = 0 :=
    (Work.ParamRays.paramPotential_eq_zero_iff c).mpr hc
  rw [h, Real.exp_zero]

/-- A level point of the critical ray at a *positive* level lies strictly above the critical
level.  Indeed `‖φ_f z‖ = exp (G_f z)` and `G_f z > G_f 0` on the critical domain. -/
theorem exp_greenFun_zero_lt_of_level {f : ℂ} {θ s : ℝ} {z : ℂ} (hs : 0 < s)
    (hz : z ∈ Work.ParamRays.critDomain f)
    (hv : Work.Bottcher.varphiCrit f z = (s : ℂ) * Work.ParamRays.rayDir θ) :
    Real.exp (Work.ParamRays.greenFun f 0) < s := by
  have hmod := Work.ParamRays.IsCritBottcher_modulus
    (Work.Bottcher.isCritBottcher_varphiCrit f) hz
  have hnorm : ‖Work.Bottcher.varphiCrit f z‖ = s := by
    rw [hv, norm_mul, Work.ParamRays.norm_rayDir, mul_one]
    exact Complex.norm_of_nonneg hs.le
  have hgz : Real.exp (Work.ParamRays.greenFun f z) = s := by rw [← hmod, hnorm]
  have hlt : Work.ParamRays.greenFun f 0 < Work.ParamRays.greenFun f z :=
    (Work.ParamRays.mem_critDomain).mp hz
  calc Real.exp (Work.ParamRays.greenFun f 0) < Real.exp (Work.ParamRays.greenFun f z) :=
        Real.exp_lt_exp.mpr hlt
    _ = s := hgz

/-- **Cluster points of critical-ray level points.**

Let `fₙ → c` with `c` in the mandelbar, let `sₙ ∈ [ℓ, η₀]` with `ℓ > 1`, and let
`zₙ ∈ critDomain fₙ` with `φ_{fₙ} zₙ = sₙ · rayDir θ`.  Assume the parameters are uniformly
bounded (`‖fₙ‖ ≤ C`).  Then some subsequence has `sₙ → s ∈ [ℓ, η₀]`, `zₙ → z`, and the limit
point `z` is a level point of the *limit* parameter: `z ∈ critDomain c` and
`φ_c z = s · rayDir θ`.

This is the varying-level version of `tendsto_critRayLevelPoint`: the level points stay in a
fixed ball (`norm_le_of_norm_varphiCrit`), a subsequence converges by compactness, the Green
functions converge (`continuous_greenFun`) and the Böttcher coordinates converge by joint
continuity on `jointDomain` (`continuousOn_jointVarphi`). -/
theorem exists_cluster_critRayLevel {c : ℂ} {θ ℓ η₀ C : ℝ} (hc : c ∈ Mandelbar) (hℓ1 : 1 < ℓ)
    {fseq : ℕ → ℂ} {sseq : ℕ → ℝ} {zseq : ℕ → ℂ}
    (hf : Tendsto fseq atTop (𝓝 c)) (hC : ∀ n, ‖fseq n‖ ≤ C)
    (hs : ∀ n, sseq n ∈ Set.Icc ℓ η₀)
    (hz : ∀ n, zseq n ∈ Work.ParamRays.critDomain (fseq n))
    (hv : ∀ n, Work.Bottcher.varphiCrit (fseq n) (zseq n)
      = (sseq n : ℂ) * Work.ParamRays.rayDir θ) :
    ∃ (s : ℝ) (z : ℂ) (φ : ℕ → ℕ), StrictMono φ ∧ s ∈ Set.Icc ℓ η₀ ∧
      Tendsto (fun k => sseq (φ k)) atTop (𝓝 s) ∧
      z ∈ Work.ParamRays.critDomain c ∧
      Work.Bottcher.varphiCrit c z = (s : ℂ) * Work.ParamRays.rayDir θ ∧
      Tendsto (fun k => zseq (φ k)) atTop (𝓝 z) := by
  -- extract a convergent subsequence of the levels
  obtain ⟨s, hsmem, ψ, hψmono, hsψ⟩ :=
    (isCompact_Icc (a := ℓ) (b := η₀)).tendsto_subseq (fun n => hs n)
  -- the corresponding level points stay in a fixed ball
  have hzbd : ∀ k : ℕ, zseq (ψ k) ∈ Metric.closedBall (0 : ℂ) (max (max 2 C) (2 * η₀)) := by
    intro k
    rw [Metric.mem_closedBall, dist_zero_right]
    have ht1 : 1 < sseq (ψ k) := lt_of_lt_of_le hℓ1 (hs (ψ k)).1
    have hval : ‖Work.Bottcher.varphiCrit (fseq (ψ k)) (zseq (ψ k))‖ = sseq (ψ k) := by
      rw [hv (ψ k), norm_mul, Work.ParamRays.norm_rayDir, mul_one]
      exact Complex.norm_of_nonneg (le_of_lt (lt_trans zero_lt_one ht1))
    refine le_trans (norm_le_of_norm_varphiCrit ht1 (hC (ψ k)) (hz (ψ k)) hval) ?_
    exact max_le_max le_rfl (mul_le_mul_of_nonneg_left (hs (ψ k)).2 (by norm_num))
  obtain ⟨z, _, φ', hφ'mono, hzlim⟩ :=
    (isCompact_closedBall (0 : ℂ) (max (max 2 C) (2 * η₀))).tendsto_subseq hzbd
  -- the joint subsequence converges
  have hglim : Tendsto (fun k => fseq (ψ (φ' k))) atTop (𝓝 c) :=
    hf.comp (hψmono.comp hφ'mono).tendsto_atTop
  have htlim : Tendsto (fun k => sseq (ψ (φ' k))) atTop (𝓝 s) :=
    hsψ.comp hφ'mono.tendsto_atTop
  have hwlim : Tendsto (fun k => zseq (ψ (φ' k))) atTop (𝓝 z) := hzlim
  have hs0 : 0 < s := lt_of_lt_of_le (lt_trans zero_lt_one hℓ1) hsmem.1
  have hpair : Tendsto (fun k => (fseq (ψ (φ' k)), zseq (ψ (φ' k)))) atTop (𝓝 (c, z)) := by
    have h := hglim.prodMk hwlim
    rwa [← nhds_prod_eq] at h
  -- the Green functions converge to `log s`
  have hgreen_eq : ∀ k : ℕ, Work.ParamRays.greenFun (fseq (ψ (φ' k))) (zseq (ψ (φ' k)))
      = Real.log (sseq (ψ (φ' k))) := by
    intro k
    have hmod := Work.ParamRays.IsCritBottcher_modulus
      (Work.Bottcher.isCritBottcher_varphiCrit (fseq (ψ (φ' k)))) (hz (ψ (φ' k)))
    have hnorm : ‖Work.Bottcher.varphiCrit (fseq (ψ (φ' k))) (zseq (ψ (φ' k)))‖
        = sseq (ψ (φ' k)) := by
      rw [hv (ψ (φ' k)), norm_mul, Work.ParamRays.norm_rayDir, mul_one]
      exact Complex.norm_of_nonneg (le_of_lt (lt_trans zero_lt_one
        (lt_of_lt_of_le hℓ1 (hs (ψ (φ' k))).1)))
    have hexp : Real.exp (Work.ParamRays.greenFun (fseq (ψ (φ' k))) (zseq (ψ (φ' k))))
        = sseq (ψ (φ' k)) := by rw [← hmod, hnorm]
    rw [← hexp, Real.log_exp]
  have hzgreen : Work.ParamRays.greenFun c z = Real.log s := by
    refine tendsto_nhds_unique
      ((Work.NAKANE.continuous_greenFun.tendsto (c, z)).comp hpair) ?_
    have h2 : Tendsto (fun k => Real.log (sseq (ψ (φ' k)))) atTop (𝓝 (Real.log s)) :=
      (Real.continuousAt_log (ne_of_gt hs0)).tendsto.comp htlim
    exact h2.congr' (Eventually.of_forall fun k => (hgreen_eq k).symm)
  -- the limit point lies in the critical domain of `c`
  have hzcrit : z ∈ Work.ParamRays.critDomain c := by
    rw [Work.ParamRays.mem_critDomain]
    have hp : Work.ParamRays.paramPotential c = 0 :=
      (Work.ParamRays.paramPotential_eq_zero_iff c).mpr hc
    rw [hp, hzgreen]
    exact Real.log_pos (lt_of_lt_of_le hℓ1 hsmem.1)
  -- and its Böttcher coordinate is the limit value
  have hzphi : Work.Bottcher.varphiCrit c z = (s : ℂ) * Work.ParamRays.rayDir θ := by
    have hjointlim : (c, z) ∈ Work.NAKANE.jointDomain := hzcrit
    have hmem : ∀ᶠ k : ℕ in atTop,
        (fseq (ψ (φ' k)), zseq (ψ (φ' k))) ∈ Work.NAKANE.jointDomain :=
      Eventually.of_forall (fun k => hz (ψ (φ' k)))
    have hwith : Tendsto (fun k => (fseq (ψ (φ' k)), zseq (ψ (φ' k)))) atTop
        (𝓝[Work.NAKANE.jointDomain] (c, z)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hpair, hmem⟩
    have hjv : Tendsto (fun k => Work.NAKANE.jointVarphi (fseq (ψ (φ' k)), zseq (ψ (φ' k))))
        atTop (𝓝 (Work.NAKANE.jointVarphi (c, z))) :=
      (((Work.NAKANE.continuousOn_jointVarphi (c, z)) hjointlim).tendsto).comp hwith
    have hcst : Tendsto (fun k => Work.NAKANE.jointVarphi (fseq (ψ (φ' k)), zseq (ψ (φ' k))))
        atTop (𝓝 ((s : ℂ) * Work.ParamRays.rayDir θ)) := by
      have hcont : Continuous fun x : ℝ => (x : ℂ) * Work.ParamRays.rayDir θ := by fun_prop
      refine (hcont.tendsto s |>.comp htlim).congr' (Eventually.of_forall fun k => ?_)
      simpa only [Function.comp_apply, Work.NAKANE.jointVarphi_apply] using (hv (ψ (φ' k))).symm
    have := tendsto_nhds_unique hjv hcst
    simpa [Work.NAKANE.jointVarphi_apply] using this
  refine ⟨s, z, ψ ∘ φ', hψmono.comp hφ'mono, hsmem, ?_, hzcrit, hzphi, ?_⟩
  · exact hsψ.comp hφ'mono.tendsto_atTop
  · exact hzlim

/-- **Uniform transfer of critical-ray level points between nearby parameters.**

For `c` in the mandelbar, a window `[ℓ, η₀]` with `ℓ > 1`, and `ε > 0`, there is `δ > 0` such
that for every parameter `f` with `‖f - c‖ < δ`, every level `s ∈ [ℓ, η₀]` and every
`z ∈ critDomain f` with `φ_f z = s · rayDir θ`, the point `z` is within `ε` of a level point of
the *same* level `s` of the parameter `c`. -/
theorem critRayLevel_close_uniform {c : ℂ} (hc : c ∈ Mandelbar) {θ ℓ η₀ : ℝ} (hℓ1 : 1 < ℓ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ, ‖f - c‖ < δ → ∀ s : ℝ, ℓ ≤ s → s ≤ η₀ → ∀ z : ℂ,
      z ∈ Work.ParamRays.critDomain f →
      Work.Bottcher.varphiCrit f z = (s : ℂ) * Work.ParamRays.rayDir θ →
      ∃ z₀ : ℂ, z₀ ∈ Work.ParamRays.critDomain c ∧
        Work.Bottcher.varphiCrit c z₀ = (s : ℂ) * Work.ParamRays.rayDir θ ∧ ‖z - z₀‖ ≤ ε := by
  by_contra hcon
  push_neg at hcon
  have hcon' : ∀ n : ℕ, ∃ f : ℂ, ‖f - c‖ < 1 / ((n : ℝ) + 1) ∧ ∃ s : ℝ, ℓ ≤ s ∧ s ≤ η₀ ∧
      ∃ z : ℂ, z ∈ Work.ParamRays.critDomain f ∧
        Work.Bottcher.varphiCrit f z = (s : ℂ) * Work.ParamRays.rayDir θ ∧
        ∀ z₀ : ℂ, z₀ ∈ Work.ParamRays.critDomain c →
          Work.Bottcher.varphiCrit c z₀ = (s : ℂ) * Work.ParamRays.rayDir θ → ε < ‖z - z₀‖ :=
    fun n => hcon (1 / ((n : ℝ) + 1)) (by positivity)
  choose fseq hfseq using hcon'
  choose sseq hsseq using fun n => (hfseq n).2
  choose zseq hzseq using fun n => (hsseq n).2.2
  -- the parameters are uniformly bounded
  have hfbd : ∀ n : ℕ, ‖fseq n‖ ≤ ‖c‖ + 1 := by
    intro n
    have h1 : ‖fseq n - c‖ < 1 := by
      refine lt_of_lt_of_le (hfseq n).1 ?_
      rw [div_le_one (by positivity)]
      have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    calc ‖fseq n‖ = ‖(fseq n - c) + c‖ := by congr 1; ring
      _ ≤ ‖fseq n - c‖ + ‖c‖ := norm_add_le _ _
      _ ≤ 1 + ‖c‖ := by linarith
      _ = ‖c‖ + 1 := by ring
  have hftend : Tendsto fseq atTop (𝓝 c) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    exact squeeze_zero (fun n => norm_nonneg _) (fun n => le_of_lt (hfseq n).1)
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  obtain ⟨s, z, φ, hφmono, hsmem, hsφ, hzmem, hzv, hzφlim⟩ :=
    exists_cluster_critRayLevel (c := c) (θ := θ) (ℓ := ℓ) (η₀ := η₀) hc hℓ1 hftend hfbd
      (fun n => ⟨(hsseq n).1, (hsseq n).2.1⟩) (fun n => (hzseq n).1) (fun n => (hzseq n).2.1)
  -- the limit point is the level point of `c` at level `s`
  have hexp1 : Real.exp (Work.ParamRays.greenFun c 0) = 1 :=
    exp_greenFun_zero_eq_one_of_mem_mandelbar hc
  have hs1 : 1 < s := lt_of_lt_of_le hℓ1 hsmem.1
  have hzeq : z = rayPt c θ s := rayPt_unique hzmem hzv (by rw [hexp1]; exact hs1)
  have hraycont : ContinuousAt (fun t : ℝ => rayPt c θ t) s :=
    (continuousOn_rayPt c θ).continuousAt (isOpen_Ioi.mem_nhds (by rw [hexp1]; exact hs1))
  have hraylim : Tendsto (fun k : ℕ => rayPt c θ (sseq (φ k))) atTop (𝓝 z) := by
    rw [hzeq]
    exact hraycont.tendsto.comp hsφ
  have hdiff : Tendsto (fun k : ℕ => zseq (φ k) - rayPt c θ (sseq (φ k))) atTop (𝓝 0) := by
    have h := hzφlim.sub hraylim
    simpa using h
  have hnormlim : Tendsto (fun k : ℕ => ‖zseq (φ k) - rayPt c θ (sseq (φ k))‖) atTop (𝓝 0) := by
    simpa using hdiff.norm
  have hfail : ∀ k : ℕ, ε < ‖zseq (φ k) - rayPt c θ (sseq (φ k))‖ := by
    intro k
    have hsk : Real.exp (Work.ParamRays.greenFun c 0) < sseq (φ k) := by
      rw [hexp1]
      exact lt_of_lt_of_le hℓ1 (hsseq (φ k)).1
    obtain ⟨hzm, hzv'⟩ := rayPt_spec (f := c) (θ := θ) (t := sseq (φ k)) hsk
    exact (hzseq (φ k)).2.2 _ hzm hzv'
  have hle := ge_of_tendsto' hnormlim (fun k => le_of_lt (hfail k))
  linarith

/-- **Transfer of the anchor bound to nearby parameters.**

If every critical-ray level point of `T_c` at an angle `θ` with level `s ∈ [ℓ, η₀]` is within
`ρ / 2` of `y`, and `yf` is continuous at `c` with `yf c = y`, then for all `f` close enough to
`c` every critical-ray level point of `T_f` at level `s ∈ [ℓ, η₀]` is within `ρ` of `yf f`. -/
theorem transfer_bound {c : ℂ} {θ : ℝ} {y : ℂ} {ℓ η₀ ρ : ℝ} {yf : ℂ → ℂ}
    (hc : c ∈ LeanEval.ComplexAnalysis.Mandelbar) (hℓ1 : 1 < ℓ) (hℓη : ℓ ≤ η₀) (hρ : 0 < ρ)
    (hanchor : ∀ t : ℝ, ℓ ≤ t → t ≤ η₀ → ∀ z : ℂ, z ∈ Work.ParamRays.critDomain c →
      Work.Bottcher.varphiCrit c z = (t : ℂ) * Work.ParamRays.rayDir θ → ‖z - y‖ ≤ ρ / 2)
    (hyfcont : ContinuousAt yf c) (hyfc : yf c = y) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f : ℂ, ‖f - c‖ < δ → ∀ s : ℝ, ℓ ≤ s → s ≤ η₀ → ∀ z : ℂ,
      z ∈ Work.ParamRays.critDomain f →
      Work.Bottcher.varphiCrit f z = (s : ℂ) * Work.ParamRays.rayDir θ → ‖z - yf f‖ ≤ ρ := by
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := critRayLevel_close_uniform hc hℓ1 (ε := ρ / 4) (by linarith)
  have hyf : ∃ δ₁ : ℝ, 0 < δ₁ ∧ ∀ f : ℂ, ‖f - c‖ < δ₁ → ‖yf f - y‖ ≤ ρ / 4 := by
    obtain ⟨δ₁, hδ₁, hδ₁'⟩ := (Metric.continuousAt_iff.mp hyfcont) (ρ / 4) (by linarith)
    refine ⟨δ₁, hδ₁, fun f hf => ?_⟩
    have h := hδ₁' (x := f) (by rw [dist_eq_norm]; exact hf)
    rw [hyfc, dist_eq_norm] at h
    exact le_of_lt h
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hyf
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
  intro f hf s hs1 hs2 z hz hzv
  have hf1 : ‖f - c‖ < δ₁ := lt_of_lt_of_le hf (min_le_left _ _)
  have hf2 : ‖f - c‖ < δ₂ := lt_of_lt_of_le hf (min_le_right _ _)
  obtain ⟨z₀, hz₀mem, hz₀v, hdist⟩ := hδ₂ f hf2 s hs1 hs2 z hz hzv
  have hB : ‖z₀ - y‖ ≤ ρ / 2 := hanchor s hs1 hs2 z₀ hz₀mem hz₀v
  have hC : ‖yf f - y‖ ≤ ρ / 4 := hδ₁ f hf1
  calc ‖z - yf f‖ = ‖(z - z₀) + (z₀ - y) - (yf f - y)‖ := by congr 1; ring
    _ ≤ ‖z - z₀‖ + ‖z₀ - y‖ + ‖yf f - y‖ := by
        have h1 : ‖(z - z₀) + (z₀ - y) - (yf f - y)‖
            ≤ ‖(z - z₀) + (z₀ - y)‖ + ‖yf f - y‖ := norm_sub_le _ _
        have h2 : ‖(z - z₀) + (z₀ - y)‖ ≤ ‖z - z₀‖ + ‖z₀ - y‖ := norm_add_le _ _
        linarith
    _ ≤ ρ / 4 + ρ / 2 + ρ / 4 := by linarith
    _ = ρ := by ring

end

end Work.LandLeaves
