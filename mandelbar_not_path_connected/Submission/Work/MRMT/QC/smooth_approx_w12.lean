/-
Smooth (C^∞), compactly supported approximation of a locally W^{1,2} function on an open set,
with L² control of the Wirtinger derivatives.

This file proves `Work.MRMT.QC.smooth_approx_w12` together with the auxiliary lemmas it needs:
compact exhaustion, smooth cutoffs, the distributional Leibniz rule on an open set, the
convolution/differentiation identity for weak Wirtinger derivatives and the L² convergence of
mollification on compact sets.
-/
import Mathlib
import Submission.Work.MRMT.Basic
import Submission.Work.MRMT.Weyl.Defs
import Submission.Work.MRMT.QC.WirtingerCalc
import Submission.Work.MRMT.QC.isDzDeriv_mul_and_isDbarDeriv_mul
import Submission.Work.MRMT.Sobolev.dz_convolution_eq_of_isDzDerivOn
import Submission.Work.MRMT.Sobolev.dzbar_convolution_eq_of_isDbarDerivOn
import Submission.Work.MRMT.QCDegree.Defs
import Submission.Work.MRMT.Weyl.moll_L1_aux
import Submission.Work.MRMT.QC.lintegral_ofReal_norm_sq_moll_le
import Submission.Work.MRMT.Sobolev.tendsto_integral_normSq_translate_memLp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open MeasureTheory Complex Function Filter
open scoped Distributions Topology ENNReal Convolution

namespace Work.MRMT.QC

/-! ## 1. Compact exhaustion of an open subset of `ℂ` -/

/-- Every open subset of `ℂ` admits a compact exhaustion by sets of the form
`closedBall 0 (n+1) ∩ {z | ball z (1/(n+1)) ⊆ U}`: compact, increasing, contained in `U`, and
eventually containing every compact subset of `U`. -/
theorem compact_exhaustion {U : Set ℂ} (hU : IsOpen U) :
    ∃ Kx : ℕ → Set ℂ, (∀ n, IsCompact (Kx n)) ∧ Monotone Kx ∧ (∀ n, Kx n ⊆ U) ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ U → ∃ N, ∀ n ≥ N, K ⊆ Kx n) := by
  have hclosed_aux : ∀ n : ℕ, IsClosed {z : ℂ | Metric.ball z (1/((n:ℝ)+1)) ⊆ U} := by
    intro n
    rw [← isOpen_compl_iff]
    have hcomp : {z : ℂ | Metric.ball z (1/((n:ℝ)+1)) ⊆ U}ᶜ
        = ⋃ w ∈ Uᶜ, Metric.ball w (1/((n:ℝ)+1)) := by
      ext z
      simp only [Set.mem_compl_iff, Set.mem_iUnion₂, Metric.mem_ball]
      constructor
      · intro h
        by_contra hc
        push Not at hc
        apply h
        intro y hy
        by_contra hyu
        have hle : 1/((n:ℝ)+1) ≤ dist y z := by rw [dist_comm]; exact hc y hyu
        exact absurd (Metric.mem_ball.mp hy) (not_lt.mpr hle)
      · rintro ⟨w, hwu, hdist⟩ h
        exact hwu (h (Metric.mem_ball.mpr (by rw [dist_comm]; exact hdist)))
    rw [hcomp]
    exact isOpen_biUnion fun w _ => Metric.isOpen_ball
  refine ⟨fun n => Metric.closedBall (0:ℂ) ((n:ℝ)+1) ∩
      {z : ℂ | Metric.ball z (1/((n:ℝ)+1)) ⊆ U}, ?_, ?_, ?_, ?_⟩
  · intro n
    exact IsCompact.of_isClosed_subset (isCompact_closedBall (0:ℂ) _)
      (Metric.isClosed_closedBall.inter (hclosed_aux n)) Set.inter_subset_left
  · intro a b hab z hz
    simp only [Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right] at hz ⊢
    refine ⟨?_, ?_⟩
    · have h : (a:ℝ)+1 ≤ (b:ℝ)+1 := by exact_mod_cast Nat.add_le_add_right hab 1
      linarith [hz.1]
    · exact (Metric.ball_subset_ball (one_div_le_one_div_of_le (by positivity) (by
        exact_mod_cast Nat.add_le_add_right hab 1))).trans hz.2
  · intro n z hz
    exact hz.2 (Metric.mem_ball_self (by positivity))
  · intro K hK hKU
    obtain ⟨δ, hδpos, hδK⟩ := hK.exists_cthickening_subset_open hU hKU
    obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0:ℂ)
    obtain ⟨N, hN⟩ : ∃ N : ℕ, max (1/δ) R ≤ (N:ℝ)+1 := by
      obtain ⟨M, hM⟩ := exists_nat_ge (max (1/δ) R)
      exact ⟨M, by linarith⟩
    refine ⟨N, ?_⟩
    intro n hn z hz
    have hn' : (N:ℝ) ≤ n := by exact_mod_cast hn
    have hN1 : (N:ℝ)+1 ≤ (n:ℝ)+1 := by linarith
    have hδn : 1/((n:ℝ)+1) ≤ δ := by
      have h1 : (1:ℝ)/δ ≤ (N:ℝ)+1 := le_trans (le_max_left _ _) hN
      have h2 : (1:ℝ)/δ ≤ (n:ℝ)+1 := le_trans h1 hN1
      have h3 := one_div_le_one_div_of_le (by positivity : (0:ℝ) < 1/δ) h2
      simpa [one_div, inv_inv] using h3
    simp only [Set.mem_inter_iff, Metric.mem_closedBall, dist_zero_right]
    refine ⟨?_, ?_⟩
    · have h3 : R ≤ (n:ℝ)+1 := le_trans (le_trans (le_max_right _ _) hN) hN1
      have hRz : ‖z‖ ≤ R := by simpa [Metric.mem_closedBall, dist_eq_norm] using hR hz
      linarith
    · exact (Metric.ball_subset_ball hδn).trans ((Metric.ball_subset_thickening hz δ).trans
        ((Metric.thickening_subset_cthickening δ K).trans hδK))

/-! ## 2. Smooth cutoffs -/

/-- A point at distance `≤ δ` from a nonempty set lies in its closed `δ`-thickening. -/
theorem mem_cthickening_of_infDist_le {K : Set ℂ} (hne : K.Nonempty) {δ : ℝ} {z : ℂ}
    (h : Metric.infDist z K ≤ δ) : z ∈ Metric.cthickening δ K := by
  rw [Metric.mem_cthickening_iff, ← ENNReal.ofReal_toReal (Metric.infEDist_ne_top hne)]
  exact ENNReal.ofReal_le_ofReal h

/-- **Smooth cutoff.** For `K` compact inside the open set `U` there is a `C^∞` compactly
supported `χ` with `tsupport χ ⊆ U` which is identically `1` on a neighbourhood of `K`.

(For `K = ∅` we take `χ = 0` and the neighbourhood `∅`; otherwise the construction is the
mollification of the continuous function `z ↦ max 0 (min 1 ((3r/4 - d(z,K))/(r/4)))` built from
the distance to `K`, which equals `1` on `{d ≤ r/2}` and `0` on `{d ≥ 3r/4}`.) -/
theorem smooth_cutoff {U K : Set ℂ} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ χ : ℂ → ℂ, ContDiff ℝ (↑(⊤ : ℕ∞)) χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∃ W : Set ℂ, IsOpen W ∧ K ⊆ W ∧ ∀ z ∈ W, χ z = 1) := by
  by_cases hKne : K.Nonempty
  · obtain ⟨r, hrpos, hrK⟩ := hK.exists_cthickening_subset_open hU hKU
    set b : ContDiffBump (0 : ℂ) := ⟨r/16, r/8, by linarith, by linarith⟩ with hbdef
    set ρ : ℂ → ℝ := b.normed volume with hρdef
    set g : ℂ → ℂ :=
      fun z => ((max 0 (min 1 ((3*r/4 - Metric.infDist z K)/(r/4))) : ℝ) : ℂ) with hgdef
    have hρ_cd : ContDiff ℝ (⊤ : ℕ∞) ρ := by rw [hρdef]; exact b.contDiff_normed
    have hρ_cs : HasCompactSupport ρ := by rw [hρdef]; exact b.hasCompactSupport_normed
    have hρ_int : ∫ y, ρ y ∂volume = 1 := by rw [hρdef]; exact b.integral_normed
    have hρ_supp : Function.support ρ = Metric.ball (0:ℂ) (r/8) := by
      rw [hρdef, hbdef, ContDiffBump.support_normed_eq]
    have hgd : Continuous fun z : ℂ => (3*r/4 - Metric.infDist z K)/(r/4) :=
      (continuous_const.sub (Metric.continuous_infDist_pt K)).div_const (r/4)
    have hg_cont : Continuous g := by
      rw [hgdef]
      exact Complex.continuous_ofReal.comp (continuous_const.max (continuous_const.min hgd))
    have hg_one : ∀ z : ℂ, Metric.infDist z K ≤ r/2 → g z = 1 := by
      intro z hz
      show ((max 0 (min 1 ((3*r/4 - Metric.infDist z K)/(r/4))) : ℝ) : ℂ) = 1
      have ht : (1:ℝ) ≤ (3*r/4 - Metric.infDist z K)/(r/4) := by
        rw [le_div_iff₀ (by linarith : (0:ℝ) < r/4)]; linarith
      rw [min_eq_left ht, max_eq_right zero_le_one]
      norm_num
    have hg_zero : ∀ z : ℂ, 3*r/4 ≤ Metric.infDist z K → g z = 0 := by
      intro z hz
      show ((max 0 (min 1 ((3*r/4 - Metric.infDist z K)/(r/4))) : ℝ) : ℂ) = 0
      have ht : (3*r/4 - Metric.infDist z K)/(r/4) ≤ 0 := by
        rw [div_nonpos_iff]
        right
        exact ⟨by linarith, by linarith⟩
      rw [min_eq_right (le_trans ht zero_le_one), max_eq_left ht]
      norm_num
    -- the support containment, proved once
    have hsupp : Function.support (Weyl.moll ρ g) ⊆ {z : ℂ | Metric.infDist z K ≤ 7*r/8} := by
      intro z hz
      by_contra hnot
      rw [Set.mem_ofPred_eq, not_le] at hnot
      apply hz
      rw [Weyl.moll_apply]
      have hzero : ∀ y : ℂ, (ρ y : ℂ) * g (z - y) = 0 := by
        intro y
        by_cases hy : ρ y = 0
        · simp [hy]
        · have hyball : y ∈ Metric.ball (0:ℂ) (r/8) := by rw [← hρ_supp]; exact hy
          have hny : ‖y‖ < r/8 := by simpa [Metric.mem_ball, dist_eq_norm] using hyball
          have hgy : g (z - y) = 0 := by
            apply hg_zero
            have h1 := Metric.infDist_le_infDist_add_dist (x := z) (y := z - y) (s := K)
            have h2 : dist z (z - y) = ‖y‖ := by rw [dist_eq_norm]; ring_nf
            rw [h2] at h1
            linarith
          rw [hgy, mul_zero]
      exact integral_eq_zero_of_ae (Eventually.of_forall hzero)
    have hclosed : IsClosed {z : ℂ | Metric.infDist z K ≤ 7*r/8} :=
      isClosed_le (Metric.continuous_infDist_pt K) continuous_const
    have hcth : ∀ z : ℂ, Metric.infDist z K ≤ 7*r/8 → z ∈ Metric.cthickening r K := fun z hz =>
      (Metric.cthickening_mono (by linarith : 7*r/8 ≤ r) K)
        (mem_cthickening_of_infDist_le hKne hz)
    -- the `χ = 1` computation
    have hone : ∀ z : ℂ, Metric.infDist z K < 3*r/8 → Weyl.moll ρ g z = 1 := by
      intro z hz
      have hkey : (fun y : ℂ => (ρ y : ℂ) * g (z - y)) = fun y : ℂ => (ρ y : ℂ) := by
        funext y
        by_cases hy : ρ y = 0
        · simp [hy]
        · have hyball : y ∈ Metric.ball (0:ℂ) (r/8) := by rw [← hρ_supp]; exact hy
          have hny : ‖y‖ < r/8 := by simpa [Metric.mem_ball, dist_eq_norm] using hyball
          have hgy : g (z - y) = 1 := by
            apply hg_one
            have h1 := Metric.infDist_le_infDist_add_dist (x := z - y) (y := z) (s := K)
            have h2 : dist (z - y) z = ‖y‖ := by rw [dist_eq_norm]; simp
            rw [h2] at h1
            linarith
          rw [hgy, mul_one]
      rw [Weyl.moll_apply, hkey, integral_complex_ofReal, hρ_int]
      norm_num
    refine ⟨Weyl.moll ρ g, ?_, ?_, ?_, {z : ℂ | Metric.infDist z K < 3*r/8}, ?_, ?_, ?_⟩
    · exact Weyl.contDiff_moll (N := ⊤) hρ_cd hρ_cs hg_cont.locallyIntegrable
    · refine HasCompactSupport.of_support_subset_isCompact (hK.cthickening (r := r)) ?_
      exact hsupp.trans hcth
    · show closure (Function.support (Weyl.moll ρ g)) ⊆ U
      exact (closure_minimal hsupp hclosed).trans (fun z hz => hrK (hcth z hz))
    · exact isOpen_lt (Metric.continuous_infDist_pt K) continuous_const
    · intro z hz
      show Metric.infDist z K < 3 * r / 8
      have h0 : Metric.infDist z K = 0 := Metric.infDist_zero_of_mem hz
      linarith
    · exact hone
  · have hKe : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    exact ⟨0, contDiff_const,
      HasCompactSupport.of_support_subset_isCompact isCompact_empty (by simp),
      by show closure (Function.support (0 : ℂ → ℂ)) ⊆ U; simp,
      ∅, isOpen_empty,
      by simp [hKe],
      by intro z hz; exact absurd hz (Set.notMem_empty z)⟩

/-! ## 3. Multiplication by a smooth compactly supported function -/

theorem tsupport_dz_subset (ψ : ℂ → ℂ) : tsupport (dz ψ) ⊆ tsupport ψ :=
  closure_minimal (fun z hz => by
    show z ∈ closure (Function.support ψ)
    by_contra hzt
    have hnb : ψ =ᶠ[𝓝 z] 0 := by
      filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hzt] with w hw
      exact image_eq_zero_of_notMem_tsupport hw
    have hd : dz ψ z = 0 := by rw [dz, hnb.fderiv_eq]; simp
    exact hz hd) (isClosed_tsupport ψ)

theorem tsupport_dzbar_subset (ψ : ℂ → ℂ) : tsupport (dzbar ψ) ⊆ tsupport ψ :=
  closure_minimal (fun z hz => by
    show z ∈ closure (Function.support ψ)
    by_contra hzt
    have hnb : ψ =ᶠ[𝓝 z] 0 := by
      filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hzt] with w hw
      exact image_eq_zero_of_notMem_tsupport hw
    have hd : dzbar ψ z = 0 := by rw [dzbar, hnb.fderiv_eq]; simp
    exact hz hd) (isClosed_tsupport ψ)

theorem hasCompactSupport_dz {ψ : ℂ → ℂ} (h : HasCompactSupport ψ) : HasCompactSupport (dz ψ) := by
  have hF : HasCompactSupport (fun z => fderiv ℝ ψ z) := h.fderiv ℝ
  have h2 := hF.comp_left
    (g := fun L : ℂ →L[ℝ] ℂ => (L 1 - Complex.I * L Complex.I) * (2:ℂ)⁻¹) (by simp)
  have key : ((fun L : ℂ →L[ℝ] ℂ => (L 1 - Complex.I * L Complex.I) * (2:ℂ)⁻¹) ∘
      fun z => fderiv ℝ ψ z) = dz ψ := by
    funext z; simp only [Function.comp_apply, Work.MRMT.dz, div_eq_mul_inv]
  rwa [key] at h2

theorem hasCompactSupport_dzbar {ψ : ℂ → ℂ} (h : HasCompactSupport ψ) :
    HasCompactSupport (dzbar ψ) := by
  have hF : HasCompactSupport (fun z => fderiv ℝ ψ z) := h.fderiv ℝ
  have h2 := hF.comp_left
    (g := fun L : ℂ →L[ℝ] ℂ => (L 1 + Complex.I * L Complex.I) * (2:ℂ)⁻¹) (by simp)
  have key : ((fun L : ℂ →L[ℝ] ℂ => (L 1 + Complex.I * L Complex.I) * (2:ℂ)⁻¹) ∘
      fun z => fderiv ℝ ψ z) = dzbar ψ := by
    funext z; simp only [Function.comp_apply, Work.MRMT.dzbar, div_eq_mul_inv]
  rwa [key] at h2

/-- If `ψ` is continuous with `tsupport ψ ⊆ U` and `f` is continuous on the open set `U`, then
`ψ · f` is continuous (it vanishes identically off `U`). -/
theorem continuous_mul_of_tsupport_subset {f ψ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hψ : Continuous ψ) (hψts : tsupport ψ ⊆ U) (hf : ContinuousOn f U) :
    Continuous (fun z => ψ z * f z) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ tsupport ψ
  · exact hψ.continuousAt.mul (hf.continuousAt (hU.mem_nhds (hψts hz)))
  · have hnb : ∀ᶠ w in 𝓝 z, ψ w = 0 := by
      filter_upwards [(isClosed_tsupport ψ).isOpen_compl.mem_nhds hz] with w hw
      exact image_eq_zero_of_notMem_tsupport hw
    exact (continuousAt_const (y := (0:ℂ))).congr (by
      filter_upwards [hnb] with w hw; simp [hw])

/-- A continuous compactly supported function whose support lies in `U`, times a function locally
integrable on `U`, is integrable. -/
theorem integrable_mul_of_tsupport_subset {f g : ℂ → ℂ} {U : Set ℂ}
    (hf : LocallyIntegrableOn f U volume) (hg : Continuous g) (hgs : HasCompactSupport g)
    (hts : tsupport g ⊆ U) : Integrable (fun z => f z * g z) := by
  have hK : IsCompact (tsupport g) := hgs
  have h1 : IntegrableOn f (tsupport g) volume := hf.integrableOn_compact_subset hts hK
  have h2 : IntegrableOn (fun z => f z * g z) (tsupport g) volume :=
    h1.mul_continuousOn hg.continuousOn hK
  exact h2.integrable_of_forall_notMem_eq_zero (fun x hx => by
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero])

/-- **Leibniz rule for the weak `∂`-derivative on an open set.** -/
theorem isDzDerivOn_mul {f p ψ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hfc : ContinuousOn f U)
    (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) (hψcs : HasCompactSupport ψ) (hψts : tsupport ψ ⊆ U)
    (hp : Work.MRMT.IsDzDerivOn f p U) :
    Work.MRMT.IsDzDerivOn (fun z => ψ z * f z) (fun z => ψ z * p z + f z * Work.MRMT.dz ψ z) U := by
  have hψc : Continuous ψ := hψ.continuous
  have hdwψ : Continuous (Work.MRMT.dz ψ) := continuous_dz_of_contDiff (by simp) hψ
  have hdzψcs : HasCompactSupport (Work.MRMT.dz ψ) := hasCompactSupport_dz hψcs
  have hdzψts : tsupport (Work.MRMT.dz ψ) ⊆ U := (tsupport_dz_subset ψ).trans hψts
  have hcont : Continuous (fun z => ψ z * f z) :=
    continuous_mul_of_tsupport_subset hU hψc hψts hfc
  have hIntψp : Integrable (fun z => ψ z * p z) :=
    (integrable_mul_of_tsupport_subset hp.2.1 hψc hψcs hψts).congr
      (Filter.Eventually.of_forall fun z => mul_comm _ _)
  have hIntfdψ : Integrable (fun z => f z * Work.MRMT.dz ψ z) :=
    integrable_mul_of_tsupport_subset hp.1 hdwψ hdzψcs hdzψts
  refine ⟨?_, ?_, ?_⟩
  · exact hcont.locallyIntegrable.locallyIntegrableOn U
  · exact ((hIntψp.add hIntfdψ).locallyIntegrable).locallyIntegrableOn U
  · intro φ hφ
    let Ψ : 𝓓(⊤, ℂ) := ⟨ψ, hψ, hψcs, Set.subset_univ _⟩
    let Φ : 𝓓(⊤, ℂ) := testMul φ Ψ
    have hΦcoe : (Φ : ℂ → ℂ) = fun z => (φ : ℂ → ℂ) z * ψ z := by
      funext z
      show (φ : ℂ → ℂ) z * (Ψ : ℂ → ℂ) z = (φ : ℂ → ℂ) z * ψ z
      rfl
    have hΦts : tsupport (Φ : ℂ → ℂ) ⊆ U := by
      rw [hΦcoe]
      refine (closure_mono ?_).trans hψts
      intro z hz
      rw [Function.mem_support] at hz ⊢
      exact fun h => hz (by rw [h, mul_zero])
    obtain ⟨hI1, hI2, hEq⟩ := hp.2.2 Φ hΦts
    have hpoint : ∀ z, Work.MRMT.dz (Φ : ℂ → ℂ) z
        = Work.MRMT.dz (φ : ℂ → ℂ) z * ψ z + (φ : ℂ → ℂ) z * Work.MRMT.dz ψ z := by
      intro z
      rw [hΦcoe]
      exact dz_mul ((φ.contDiff.differentiable (by simp)) z) ((hψ.differentiable (by simp)) z)
    set A : ℂ := ∫ z, f z * (Work.MRMT.dz (φ : ℂ → ℂ) z * ψ z) with hAdef
    set B : ℂ := ∫ z, f z * ((φ : ℂ → ℂ) z * Work.MRMT.dz ψ z) with hBdef
    set C : ℂ := ∫ z, p z * ((φ : ℂ → ℂ) z * ψ z) with hCdef
    have hA : Integrable (fun z => f z * (Work.MRMT.dz (φ : ℂ → ℂ) z * ψ z)) := by
      refine integrable_mul_of_tsupport_subset (U := U) hp.1 ?_ ?_ ?_
      · exact (continuous_dz_of_contDiff (by simp) φ.contDiff).mul hψc
      · exact hψcs.mul_left
      · refine (closure_mono ?_).trans hψts
        intro z hz
        rw [Function.mem_support] at hz ⊢
        exact fun h => hz (by rw [h, mul_zero])
    have hB : Integrable (fun z => f z * ((φ : ℂ → ℂ) z * Work.MRMT.dz ψ z)) := by
      refine integrable_mul_of_tsupport_subset (U := U) hp.1 ?_ ?_ ?_
      · exact φ.continuous.mul hdwψ
      · exact φ.hasCompactSupport.mul_right
      · refine (closure_mono ?_).trans hφ
        intro z hz
        rw [Function.mem_support] at hz ⊢
        exact fun h => hz (by rw [h, zero_mul])
    have hC : Integrable (fun z => p z * ((φ : ℂ → ℂ) z * ψ z)) := by
      refine hI2.congr (Filter.Eventually.of_forall fun z => ?_)
      rw [hΦcoe]
    have hsplit : ∫ z, f z * Work.MRMT.dz (Φ : ℂ → ℂ) z = A + B := by
      rw [← integral_add hA hB]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show f z * Work.MRMT.dz (Φ : ℂ → ℂ) z
        = f z * (Work.MRMT.dz (φ : ℂ → ℂ) z * ψ z) + f z * ((φ : ℂ → ℂ) z * Work.MRMT.dz ψ z)
      rw [hpoint z]; ring
    have hΦC : ∫ z, p z * (Φ : ℂ → ℂ) z = C :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => by rw [hΦcoe])
    have hAB : A + B = -C := by rw [← hsplit, hEq, hΦC]
    refine ⟨?_, ?_, ?_⟩
    · have h1 : (fun z => (ψ z * f z) * Work.MRMT.dz (φ : ℂ → ℂ) z)
          = fun z => f z * (Work.MRMT.dz (φ : ℂ → ℂ) z * ψ z) := by
        funext z; ring
      rw [h1]; exact hA
    · have h1 : (fun z => (ψ z * p z + f z * Work.MRMT.dz ψ z) * (φ : ℂ → ℂ) z)
          = fun z => p z * ((φ : ℂ → ℂ) z * ψ z) + f z * ((φ : ℂ → ℂ) z * Work.MRMT.dz ψ z) := by
        funext z; ring
      rw [h1]; exact hC.add hB
    · show ∫ z, (ψ z * f z) * Work.MRMT.dz (φ : ℂ → ℂ) z
          = - ∫ z, (ψ z * p z + f z * Work.MRMT.dz ψ z) * (φ : ℂ → ℂ) z
      have hL : ∫ z, (ψ z * f z) * Work.MRMT.dz (φ : ℂ → ℂ) z = A :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
      have hR : ∫ z, (ψ z * p z + f z * Work.MRMT.dz ψ z) * (φ : ℂ → ℂ) z = C + B := by
        rw [← integral_add hC hB]
        exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
      rw [hL, hR, eq_neg_iff_add_eq_zero]
      linear_combination hAB

/-- **Leibniz rule for the weak `∂̄`-derivative on an open set.** -/
theorem isDbarDerivOn_mul {f q ψ : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hfc : ContinuousOn f U)
    (hψ : ContDiff ℝ (↑(⊤ : ℕ∞)) ψ) (hψcs : HasCompactSupport ψ) (hψts : tsupport ψ ⊆ U)
    (hq : Work.MRMT.IsDbarDerivOn f q U) :
    Work.MRMT.IsDbarDerivOn (fun z => ψ z * f z)
      (fun z => ψ z * q z + f z * Work.MRMT.dzbar ψ z) U := by
  have hψc : Continuous ψ := hψ.continuous
  have hdwψ : Continuous (Work.MRMT.dzbar ψ) := continuous_dzbar_of_contDiff (by simp) hψ
  have hdzψcs : HasCompactSupport (Work.MRMT.dzbar ψ) := hasCompactSupport_dzbar hψcs
  have hdzψts : tsupport (Work.MRMT.dzbar ψ) ⊆ U := (tsupport_dzbar_subset ψ).trans hψts
  have hcont : Continuous (fun z => ψ z * f z) :=
    continuous_mul_of_tsupport_subset hU hψc hψts hfc
  have hIntψq : Integrable (fun z => ψ z * q z) :=
    (integrable_mul_of_tsupport_subset hq.2.1 hψc hψcs hψts).congr
      (Filter.Eventually.of_forall fun z => mul_comm _ _)
  have hIntfdψ : Integrable (fun z => f z * Work.MRMT.dzbar ψ z) :=
    integrable_mul_of_tsupport_subset hq.1 hdwψ hdzψcs hdzψts
  refine ⟨?_, ?_, ?_⟩
  · exact hcont.locallyIntegrable.locallyIntegrableOn U
  · exact ((hIntψq.add hIntfdψ).locallyIntegrable).locallyIntegrableOn U
  · intro φ hφ
    let Ψ : 𝓓(⊤, ℂ) := ⟨ψ, hψ, hψcs, Set.subset_univ _⟩
    let Φ : 𝓓(⊤, ℂ) := testMul φ Ψ
    have hΦcoe : (Φ : ℂ → ℂ) = fun z => (φ : ℂ → ℂ) z * ψ z := by
      funext z
      show (φ : ℂ → ℂ) z * (Ψ : ℂ → ℂ) z = (φ : ℂ → ℂ) z * ψ z
      rfl
    have hΦts : tsupport (Φ : ℂ → ℂ) ⊆ U := by
      rw [hΦcoe]
      refine (closure_mono ?_).trans hψts
      intro z hz
      rw [Function.mem_support] at hz ⊢
      exact fun h => hz (by rw [h, mul_zero])
    obtain ⟨hI1, hI2, hEq⟩ := hq.2.2 Φ hΦts
    have hpoint : ∀ z, Work.MRMT.dzbar (Φ : ℂ → ℂ) z
        = Work.MRMT.dzbar (φ : ℂ → ℂ) z * ψ z + (φ : ℂ → ℂ) z * Work.MRMT.dzbar ψ z := by
      intro z
      rw [hΦcoe]
      exact dzbar_mul ((φ.contDiff.differentiable (by simp)) z) ((hψ.differentiable (by simp)) z)
    set A : ℂ := ∫ z, f z * (Work.MRMT.dzbar (φ : ℂ → ℂ) z * ψ z) with hAdef
    set B : ℂ := ∫ z, f z * ((φ : ℂ → ℂ) z * Work.MRMT.dzbar ψ z) with hBdef
    set C : ℂ := ∫ z, q z * ((φ : ℂ → ℂ) z * ψ z) with hCdef
    have hA : Integrable (fun z => f z * (Work.MRMT.dzbar (φ : ℂ → ℂ) z * ψ z)) := by
      refine integrable_mul_of_tsupport_subset (U := U) hq.1 ?_ ?_ ?_
      · exact (continuous_dzbar_of_contDiff (by simp) φ.contDiff).mul hψc
      · exact hψcs.mul_left
      · refine (closure_mono ?_).trans hψts
        intro z hz
        rw [Function.mem_support] at hz ⊢
        exact fun h => hz (by rw [h, mul_zero])
    have hB : Integrable (fun z => f z * ((φ : ℂ → ℂ) z * Work.MRMT.dzbar ψ z)) := by
      refine integrable_mul_of_tsupport_subset (U := U) hq.1 ?_ ?_ ?_
      · exact φ.continuous.mul hdwψ
      · exact φ.hasCompactSupport.mul_right
      · refine (closure_mono ?_).trans hφ
        intro z hz
        rw [Function.mem_support] at hz ⊢
        exact fun h => hz (by rw [h, zero_mul])
    have hC : Integrable (fun z => q z * ((φ : ℂ → ℂ) z * ψ z)) := by
      refine hI2.congr (Filter.Eventually.of_forall fun z => ?_)
      rw [hΦcoe]
    have hsplit : ∫ z, f z * Work.MRMT.dzbar (Φ : ℂ → ℂ) z = A + B := by
      rw [← integral_add hA hB]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      show f z * Work.MRMT.dzbar (Φ : ℂ → ℂ) z
        = f z * (Work.MRMT.dzbar (φ : ℂ → ℂ) z * ψ z)
          + f z * ((φ : ℂ → ℂ) z * Work.MRMT.dzbar ψ z)
      rw [hpoint z]; ring
    have hΦC : ∫ z, q z * (Φ : ℂ → ℂ) z = C :=
      integral_congr_ae (Filter.Eventually.of_forall fun z => by rw [hΦcoe])
    have hAB : A + B = -C := by rw [← hsplit, hEq, hΦC]
    refine ⟨?_, ?_, ?_⟩
    · have h1 : (fun z => (ψ z * f z) * Work.MRMT.dzbar (φ : ℂ → ℂ) z)
          = fun z => f z * (Work.MRMT.dzbar (φ : ℂ → ℂ) z * ψ z) := by
        funext z; ring
      rw [h1]; exact hA
    · have h1 : (fun z => (ψ z * q z + f z * Work.MRMT.dzbar ψ z) * (φ : ℂ → ℂ) z)
          = fun z => q z * ((φ : ℂ → ℂ) z * ψ z)
            + f z * ((φ : ℂ → ℂ) z * Work.MRMT.dzbar ψ z) := by
        funext z; ring
      rw [h1]; exact hC.add hB
    · show ∫ z, (ψ z * f z) * Work.MRMT.dzbar (φ : ℂ → ℂ) z
          = - ∫ z, (ψ z * q z + f z * Work.MRMT.dzbar ψ z) * (φ : ℂ → ℂ) z
      have hL : ∫ z, (ψ z * f z) * Work.MRMT.dzbar (φ : ℂ → ℂ) z = A :=
        integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
      have hR : ∫ z, (ψ z * q z + f z * Work.MRMT.dzbar ψ z) * (φ : ℂ → ℂ) z = C + B := by
        rw [← integral_add hC hB]
        exact integral_congr_ae (Filter.Eventually.of_forall fun z => by ring)
      rw [hL, hR, eq_neg_iff_add_eq_zero]
      linear_combination hAB

/-! ## 4. Auxiliary estimates and the diagonal construction -/

/-- If `0 ≤ g ≤ c` on a measurable set `s` of finite measure and `g` is a.e. strongly
measurable there, then `∫ z in s, g z ≤ c * (volume s).toReal`. -/
theorem setIntegral_le_of_bound {g : ℂ → ℝ} {s : Set ℂ} {c : ℝ}
    (hs : MeasurableSet s) (hsfin : volume s ≠ ⊤)
    (hg : AEStronglyMeasurable g (volume.restrict s))
    (hnn : ∀ z ∈ s, 0 ≤ g z) (hbound : ∀ z ∈ s, g z ≤ c) :
    ∫ z in s, g z ≤ c * (volume s).toReal := by
  haveI : IsFiniteMeasure (volume.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.mpr hsfin⟩
  have hgInt : Integrable g (volume.restrict s) :=
    Integrable.of_bound hg c (by
      filter_upwards [MeasureTheory.ae_restrict_mem hs] with z hz
      rw [Real.norm_of_nonneg (hnn z hz)]
      exact hbound z hz)
  have hcInt : Integrable (fun _ : ℂ => c) (volume.restrict s) := integrable_const c
  calc ∫ z in s, g z = ∫ z, g z ∂(volume.restrict s) := rfl
    _ ≤ ∫ z, c ∂(volume.restrict s) :=
        integral_mono_ae hgInt hcInt (by
          filter_upwards [MeasureTheory.ae_restrict_mem hs] with z hz
          exact hbound z hz)
    _ = c * (volume s).toReal := by
        rw [integral_const, smul_eq_mul, Measure.real, Measure.restrict_apply_univ, mul_comm]

/-- `‖a - b‖² ≤ 2‖a‖² + 2‖b‖²`. -/
theorem norm_sub_sq_le (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
  have h3 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := by
    rw [sq, sq]; exact mul_self_le_mul_self (norm_nonneg _) h1
  have h4 : (‖a‖ + ‖b‖) ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  linarith

/-- Given a compact exhaustion of `U` and, for every `n`, a `C^∞` compactly supported `v n`
approximating `f` on the exhaustion set with `L²` control `1/(n+1)` of both Wirtinger
derivatives, one obtains a single sequence `F` fulfilling all the conclusions of
`smooth_approx_w12`. -/
theorem build_sequence {f p q : ℂ → ℂ} {U : Set ℂ} {Kx : ℕ → Set ℂ}
    (hKx : ∀ n, IsCompact (Kx n)) (hKxU : ∀ n, Kx n ⊆ U)
    (hcof : ∀ K : Set ℂ, IsCompact K → K ⊆ U → ∃ N, ∀ n ≥ N, K ⊆ Kx n)
    (hp : Work.MRMT.IsDzDerivOn f p U) (hq : Work.MRMT.IsDbarDerivOn f q U)
    (hpL : Work.MRMT.MemL2LocOn p U) (hqL : Work.MRMT.MemL2LocOn q U)
    (hfc : ContinuousOn f U)
    (hW : ∀ n, ∃ v : ℂ → ℂ, ContDiff ℝ (↑(⊤ : ℕ∞)) v ∧ HasCompactSupport v ∧
      (∀ z ∈ Kx n, ‖v z - f z‖ ≤ 1/((n:ℝ)+1)) ∧
      (∫ z in Kx n, ‖Work.MRMT.dz v z - p z‖ ^ 2 ≤ 1/((n:ℝ)+1)) ∧
      (∫ z in Kx n, ‖Work.MRMT.dzbar v z - q z‖ ^ 2 ≤ 1/((n:ℝ)+1))) :
    ∃ F : ℕ → ℂ → ℂ,
      (∀ n, ContDiff ℝ (↑(⊤ : ℕ∞)) (F n)) ∧ (∀ n, HasCompactSupport (F n)) ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ U → TendstoUniformlyOn F f atTop K) ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ U →
        Filter.Tendsto (fun n => ∫ z in K, ‖F n z - f z‖ ^ 2) Filter.atTop (nhds 0)) ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ U →
        Filter.Tendsto (fun n => ∫ z in K, ‖Work.MRMT.dz (F n) z - p z‖ ^ 2)
          Filter.atTop (nhds 0)) ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ U →
        Filter.Tendsto (fun n => ∫ z in K, ‖Work.MRMT.dzbar (F n) z - q z‖ ^ 2)
          Filter.atTop (nhds 0)) := by
  classical
  choose F hF using hW
  have hlim : Filter.Tendsto (fun n : ℕ => 1/((n:ℝ)+1)) Filter.atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  refine ⟨F, fun n => (hF n).1, fun n => (hF n).2.1, ?_, ?_, ?_, ?_⟩
  · intro K hK hKU
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hcof K hK hKU
    have hev : ∀ᶠ n : ℕ in Filter.atTop, 1/((n:ℝ)+1) < ε :=
      hlim.eventually (eventually_lt_nhds hε)
    filter_upwards [hev, eventually_ge_atTop N] with n hn hNn
    intro z hz
    rw [dist_eq_norm]
    calc ‖f z - F n z‖ = ‖F n z - f z‖ := norm_sub_rev _ _
      _ ≤ 1/((n:ℝ)+1) := (hF n).2.2.1 z (hN n hNn hz)
      _ < ε := hn
  · intro K hK hKU
    obtain ⟨N, hN⟩ := hcof K hK hKU
    refine squeeze_zero' (g := fun n : ℕ => (1/((n:ℝ)+1))^2 * (volume K).toReal)
      (Filter.Eventually.of_forall fun n : ℕ => integral_nonneg fun z => by positivity) ?_ ?_
    · filter_upwards [eventually_ge_atTop N] with n hn
      have haesm : AEStronglyMeasurable (fun z => ‖F n z - f z‖ ^ 2) (volume.restrict K) :=
        (((hF n).1.continuous.continuousOn.sub (hfc.mono hKU)).aestronglyMeasurable
          hK.measurableSet).norm.pow 2
      exact setIntegral_le_of_bound hK.measurableSet hK.measure_lt_top.ne haesm
        (fun z _ => by positivity)
        (fun z hz => pow_le_pow_left₀ (norm_nonneg _) ((hF n).2.2.1 z (hN n hn hz)) 2)
    · simpa using (((hlim).pow 2).mul_const ((volume K).toReal))
  · intro K hK hKU
    obtain ⟨N, hN⟩ := hcof K hK hKU
    refine squeeze_zero' (g := fun n : ℕ => 1/((n:ℝ)+1))
      (Filter.Eventually.of_forall fun n : ℕ => integral_nonneg fun z => by positivity) ?_ ?_
    · filter_upwards [eventually_ge_atTop N] with n hn
      have hdzcont : ContinuousOn (fun z => 2 * ‖Work.MRMT.dz (F n) z‖ ^ 2) (Kx n) :=
        (continuous_const.mul
          ((continuous_dz_of_contDiff (by simp) ((hF n).1)).norm.pow 2)).continuousOn
      have hpInt : IntegrableOn (fun z => 2 * ‖p z‖ ^ 2) (Kx n) volume :=
        ((hpL (Kx n) (hKx n)).mono_set (Set.subset_inter_iff.mpr ⟨fun _ hz => hz, hKxU n⟩)).const_mul 2
      have haesm : AEStronglyMeasurable (fun z => ‖Work.MRMT.dz (F n) z - p z‖ ^ 2)
          (volume.restrict (Kx n)) :=
        (((continuous_dz_of_contDiff (by simp) ((hF n).1)).aestronglyMeasurable.sub
          (MeasureTheory.LocallyIntegrableOn.aestronglyMeasurable
            ((hp.2.1).mono_set (hKxU n)))).norm).pow 2
      have hInt : IntegrableOn (fun z => ‖Work.MRMT.dz (F n) z - p z‖ ^ 2) (Kx n) volume := by
        have hdom : Integrable (fun z => 2 * ‖Work.MRMT.dz (F n) z‖ ^ 2 + 2 * ‖p z‖ ^ 2)
            (volume.restrict (Kx n)) :=
          (ContinuousOn.integrableOn_compact (hKx n) hdzcont).add hpInt
        refine Integrable.mono' hdom haesm ?_
        filter_upwards with z
        rw [Real.norm_of_nonneg (by positivity)]
        exact norm_sub_sq_le (Work.MRMT.dz (F n) z) (p z)
      calc ∫ z in K, ‖Work.MRMT.dz (F n) z - p z‖ ^ 2
          ≤ ∫ z in Kx n, ‖Work.MRMT.dz (F n) z - p z‖ ^ 2 :=
            setIntegral_mono_set hInt (Filter.Eventually.of_forall fun z => by positivity)
              (hN n hn).eventuallySubset
        _ ≤ 1/((n:ℝ)+1) := (hF n).2.2.2.1
    · simpa using hlim
  · intro K hK hKU
    obtain ⟨N, hN⟩ := hcof K hK hKU
    refine squeeze_zero' (g := fun n : ℕ => 1/((n:ℝ)+1))
      (Filter.Eventually.of_forall fun n : ℕ => integral_nonneg fun z => by positivity) ?_ ?_
    · filter_upwards [eventually_ge_atTop N] with n hn
      have hdzcont : ContinuousOn (fun z => 2 * ‖Work.MRMT.dzbar (F n) z‖ ^ 2) (Kx n) :=
        (continuous_const.mul
          ((continuous_dzbar_of_contDiff (by simp) ((hF n).1)).norm.pow 2)).continuousOn
      have hqInt : IntegrableOn (fun z => 2 * ‖q z‖ ^ 2) (Kx n) volume :=
        ((hqL (Kx n) (hKx n)).mono_set (Set.subset_inter_iff.mpr ⟨fun _ hz => hz, hKxU n⟩)).const_mul 2
      have haesm : AEStronglyMeasurable (fun z => ‖Work.MRMT.dzbar (F n) z - q z‖ ^ 2)
          (volume.restrict (Kx n)) :=
        (((continuous_dzbar_of_contDiff (by simp) ((hF n).1)).aestronglyMeasurable.sub
          (MeasureTheory.LocallyIntegrableOn.aestronglyMeasurable
            ((hq.2.1).mono_set (hKxU n)))).norm).pow 2
      have hInt : IntegrableOn (fun z => ‖Work.MRMT.dzbar (F n) z - q z‖ ^ 2) (Kx n) volume := by
        have hdom : Integrable (fun z => 2 * ‖Work.MRMT.dzbar (F n) z‖ ^ 2 + 2 * ‖q z‖ ^ 2)
            (volume.restrict (Kx n)) :=
          (ContinuousOn.integrableOn_compact (hKx n) hdzcont).add hqInt
        refine Integrable.mono' hdom haesm ?_
        filter_upwards with z
        rw [Real.norm_of_nonneg (by positivity)]
        exact norm_sub_sq_le (Work.MRMT.dzbar (F n) z) (q z)
      calc ∫ z in K, ‖Work.MRMT.dzbar (F n) z - q z‖ ^ 2
          ≤ ∫ z in Kx n, ‖Work.MRMT.dzbar (F n) z - q z‖ ^ 2 :=
            setIntegral_mono_set hInt (Filter.Eventually.of_forall fun z => by positivity)
              (hN n hn).eventuallySubset
        _ ≤ 1/((n:ℝ)+1) := (hF n).2.2.2.2
    · simpa using hlim

/-! ## 5. `L²` convergence of mollification -/

/-- Pointwise Cauchy–Schwarz/Jensen bound: for a normalised nonnegative kernel `ρ` with compact
support, `‖moll ρ f z - f z‖² ≤ ∫ y, ρ y ‖f (z - y) - f z‖²`. -/
theorem moll_sq_le {f : ℂ → ℂ} (hf : MemLp f 2 (volume : Measure ℂ)) {ρ : ℂ → ℝ}
    (hρc : Continuous ρ) (hρcs : HasCompactSupport ρ) (hρ1 : ∫ y, ρ y = 1)
    (hρnn : ∀ y, 0 ≤ ρ y) (z : ℂ) :
    ‖Work.MRMT.Weyl.moll ρ f z - f z‖ ^ 2
      ≤ ∫ y, ρ y * ‖f (z - y) - f z‖ ^ 2 := by
  have hloc : LocallyIntegrable f volume := hf.locallyIntegrable (by norm_num)
  have hb := Work.MRMT.Weyl.norm_moll_sub_le hloc hρc hρcs hρ1 hρnn z
  obtain ⟨M, hM⟩ := (hρcs.isCompact_range hρc).isBounded.exists_norm_le
  have hMy : ∀ y, ρ y ≤ M := fun y => by
    have h := hM (ρ y) (Set.mem_range_self y)
    rwa [Real.norm_of_nonneg (hρnn y)] at h
  have hMemLpSub : MemLp (fun y : ℂ => f (z - y)) 2 volume :=
    hf.comp_measurePreserving ((volume : Measure ℂ).measurePreserving_sub_left z)
  have hIntBas : Integrable (fun y : ℂ => ‖f (z - y)‖ ^ 2) volume := by
    simpa using hMemLpSub.integrable_norm_rpow (by norm_num) (by norm_num)
  have hIntSq : Integrable (fun y : ℂ => ρ y * ‖f (z - y) - f z‖ ^ 2) volume := by
    have hdom : Integrable (fun y : ℂ => 2 * M * ‖f (z - y)‖ ^ 2 + 2 * ‖f z‖ ^ 2 * ρ y) volume :=
      (hIntBas.const_mul (2 * M)).add ((hρc.integrable_of_hasCompactSupport hρcs).const_mul _)
    refine Integrable.mono' hdom ?_ ?_
    · exact hρc.aestronglyMeasurable.mul
        ((hMemLpSub.aestronglyMeasurable.sub aestronglyMeasurable_const).norm.pow 2)
    · filter_upwards with y
      rw [Real.norm_of_nonneg (mul_nonneg (hρnn y) (sq_nonneg _))]
      have h2 : ‖f (z - y) - f z‖ ^ 2 ≤ 2 * ‖f (z - y)‖ ^ 2 + 2 * ‖f z‖ ^ 2 :=
        norm_sub_sq_le (f (z - y)) (f z)
      have h3 : ρ y * ‖f (z - y) - f z‖ ^ 2
          ≤ ρ y * (2 * ‖f (z - y)‖ ^ 2 + 2 * ‖f z‖ ^ 2) :=
        mul_le_mul_of_nonneg_left h2 (hρnn y)
      have h4 : ρ y * ‖f (z - y)‖ ^ 2 ≤ M * ‖f (z - y)‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (hMy y) (sq_nonneg _)
      calc ρ y * ‖f (z - y) - f z‖ ^ 2
          ≤ ρ y * (2 * ‖f (z - y)‖ ^ 2 + 2 * ‖f z‖ ^ 2) := h3
        _ = 2 * (ρ y * ‖f (z - y)‖ ^ 2) + 2 * ‖f z‖ ^ 2 * ρ y := by ring
        _ ≤ 2 * (M * ‖f (z - y)‖ ^ 2) + 2 * ‖f z‖ ^ 2 * ρ y := by linarith [h4]
        _ = 2 * M * ‖f (z - y)‖ ^ 2 + 2 * ‖f z‖ ^ 2 * ρ y := by ring
  have hsq : (∫ y, ρ y * ‖f (z - y) - f z‖) ^ 2
      ≤ ∫ y, ρ y * ‖f (z - y) - f z‖ ^ 2 := by
    have hp : (2:ℝ).HolderConjugate 2 := by rw [Real.holderConjugate_iff]; norm_num
    have hfnn : 0 ≤ᵐ[volume] (fun y : ℂ => Real.sqrt (ρ y)) :=
      Filter.Eventually.of_forall fun y => Real.sqrt_nonneg _
    have hgnn : 0 ≤ᵐ[volume] (fun y : ℂ => Real.sqrt (ρ y) * ‖f (z - y) - f z‖) :=
      Filter.Eventually.of_forall fun y => mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)
    have hfm : MemLp (fun y : ℂ => Real.sqrt (ρ y)) (ENNReal.ofReal 2) volume := by
      have hAESM : AEStronglyMeasurable (fun y : ℂ => Real.sqrt (ρ y)) volume :=
        (Real.continuous_sqrt.comp hρc).aestronglyMeasurable
      have h : MemLp (fun y : ℂ => Real.sqrt (ρ y)) 2 volume := by
        rw [MeasureTheory.memLp_two_iff_integrable_sq hAESM]
        exact (hρc.integrable_of_hasCompactSupport hρcs).congr
          (Filter.Eventually.of_forall fun y => (Real.sq_sqrt (hρnn y)).symm)
      simpa using h
    have hgm : MemLp (fun y : ℂ => Real.sqrt (ρ y) * ‖f (z - y) - f z‖)
        (ENNReal.ofReal 2) volume := by
      have hAESM : AEStronglyMeasurable
          (fun y : ℂ => Real.sqrt (ρ y) * ‖f (z - y) - f z‖) volume :=
        ((Real.continuous_sqrt.comp hρc).aestronglyMeasurable).mul
          ((hMemLpSub.aestronglyMeasurable.sub aestronglyMeasurable_const).norm)
      have h : MemLp (fun y : ℂ => Real.sqrt (ρ y) * ‖f (z - y) - f z‖) 2 volume := by
        rw [MeasureTheory.memLp_two_iff_integrable_sq hAESM]
        refine hIntSq.congr (Filter.Eventually.of_forall fun y => ?_)
        show ρ y * ‖f (z - y) - f z‖ ^ 2
          = (Real.sqrt (ρ y) * ‖f (z - y) - f z‖) ^ 2
        rw [mul_pow, Real.sq_sqrt (hρnn y)]
      simpa using h
    have hmain := MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume) hp hfnn hgnn hfm hgm
    have h1 : (∫ a : ℂ, Real.sqrt (ρ a) ^ (2:ℝ)) = ∫ a : ℂ, ρ a :=
      integral_congr_ae (Filter.Eventually.of_forall fun a => by
        show Real.sqrt (ρ a) ^ (2:ℝ) = ρ a
        rw [Real.rpow_two, Real.sq_sqrt (hρnn a)])
    have h2 : (∫ a : ℂ, (Real.sqrt (ρ a) * ‖f (z - a) - f z‖) ^ (2:ℝ))
        = ∫ a : ℂ, ρ a * ‖f (z - a) - f z‖ ^ 2 :=
      integral_congr_ae (Filter.Eventually.of_forall fun a => by
        show (Real.sqrt (ρ a) * ‖f (z - a) - f z‖) ^ (2:ℝ) = ρ a * ‖f (z - a) - f z‖ ^ 2
        rw [Real.rpow_two, mul_pow, Real.sq_sqrt (hρnn a)])
    have h3 : (∫ a : ℂ, Real.sqrt (ρ a) * (Real.sqrt (ρ a) * ‖f (z - a) - f z‖))
        = ∫ a : ℂ, ρ a * ‖f (z - a) - f z‖ :=
      integral_congr_ae (Filter.Eventually.of_forall fun a => by
        show Real.sqrt (ρ a) * (Real.sqrt (ρ a) * ‖f (z - a) - f z‖)
          = ρ a * ‖f (z - a) - f z‖
        rw [← mul_assoc, ← sq, Real.sq_sqrt (hρnn a)])
    rw [h1, h2, h3] at hmain
    rw [hρ1, Real.one_rpow, one_mul] at hmain
    calc (∫ y, ρ y * ‖f (z - y) - f z‖) ^ 2
        ≤ ((∫ y, ρ y * ‖f (z - y) - f z‖ ^ 2) ^ (1/2:ℝ)) ^ 2 :=
          pow_le_pow_left₀ (integral_nonneg fun y => mul_nonneg (hρnn y) (norm_nonneg _)) hmain 2
      _ = ∫ y, ρ y * ‖f (z - y) - f z‖ ^ 2 := by
          rw [← Real.sqrt_eq_rpow]
          exact Real.sq_sqrt (integral_nonneg fun y => mul_nonneg (hρnn y) (sq_nonneg _))
  calc ‖Work.MRMT.Weyl.moll ρ f z - f z‖ ^ 2
      ≤ (∫ y, ρ y * ‖f (z - y) - f z‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
    _ ≤ ∫ y, ρ y * ‖f (z - y) - f z‖ ^ 2 := hsq

/-- Integrability of `ρ y * ‖f (z - y) - f z‖²`. -/
theorem integrable_moll_sq_sub {f : ℂ → ℂ} (hf : MemLp f 2 (volume : Measure ℂ)) {ρ : ℂ → ℝ}
    (hρc : Continuous ρ) (hρcs : HasCompactSupport ρ) (hρnn : ∀ y, 0 ≤ ρ y) (z : ℂ) :
    Integrable (fun y : ℂ => ρ y * ‖f (z - y) - f z‖ ^ 2) volume := by
  obtain ⟨M, hM⟩ := (hρcs.isCompact_range hρc).isBounded.exists_norm_le
  have hMy : ∀ y, ρ y ≤ M := fun y => by
    have h := hM (ρ y) (Set.mem_range_self y)
    rwa [Real.norm_of_nonneg (hρnn y)] at h
  have hMemLpSub : MemLp (fun y : ℂ => f (z - y)) 2 volume :=
    hf.comp_measurePreserving ((volume : Measure ℂ).measurePreserving_sub_left z)
  have hIntBas : Integrable (fun y : ℂ => ‖f (z - y)‖ ^ 2) volume := by
    simpa using hMemLpSub.integrable_norm_rpow (by norm_num) (by norm_num)
  have hdom : Integrable (fun y : ℂ => 2 * M * ‖f (z - y)‖ ^ 2 + 2 * ‖f z‖ ^ 2 * ρ y) volume :=
    (hIntBas.const_mul (2 * M)).add ((hρc.integrable_of_hasCompactSupport hρcs).const_mul _)
  refine Integrable.mono' hdom ?_ ?_
  · exact hρc.aestronglyMeasurable.mul
      ((hMemLpSub.aestronglyMeasurable.sub aestronglyMeasurable_const).norm.pow 2)
  · filter_upwards with y
    rw [Real.norm_of_nonneg (mul_nonneg (hρnn y) (sq_nonneg _))]
    have h2 : ‖f (z - y) - f z‖ ^ 2 ≤ 2 * ‖f (z - y)‖ ^ 2 + 2 * ‖f z‖ ^ 2 :=
      norm_sub_sq_le (f (z - y)) (f z)
    have h3 : ρ y * ‖f (z - y) - f z‖ ^ 2
        ≤ ρ y * (2 * ‖f (z - y)‖ ^ 2 + 2 * ‖f z‖ ^ 2) :=
      mul_le_mul_of_nonneg_left h2 (hρnn y)
    have h4 : ρ y * ‖f (z - y)‖ ^ 2 ≤ M * ‖f (z - y)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (hMy y) (sq_nonneg _)
    calc ρ y * ‖f (z - y) - f z‖ ^ 2
        ≤ ρ y * (2 * ‖f (z - y)‖ ^ 2 + 2 * ‖f z‖ ^ 2) := h3
      _ = 2 * (ρ y * ‖f (z - y)‖ ^ 2) + 2 * ‖f z‖ ^ 2 * ρ y := by ring
      _ ≤ 2 * (M * ‖f (z - y)‖ ^ 2) + 2 * ‖f z‖ ^ 2 * ρ y := by linarith [h4]
      _ = 2 * M * ‖f (z - y)‖ ^ 2 + 2 * ‖f z‖ ^ 2 * ρ y := by ring

/-- Additivity of the mollification in its function argument. -/
theorem moll_add {f g : ℂ → ℂ} (hf : LocallyIntegrable f volume) (hg : LocallyIntegrable g volume)
    {ρ : ℂ → ℝ} (hρc : Continuous ρ) (hρcs : HasCompactSupport ρ) (z : ℂ) :
    Work.MRMT.Weyl.moll ρ (fun w => f w + g w) z
      = Work.MRMT.Weyl.moll ρ f z + Work.MRMT.Weyl.moll ρ g z := by
  have h1 : Integrable (fun t : ℂ => (ρ t : ℂ) * f (z - t)) volume := by
    have h := hρcs.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hρc hf z
    simpa only [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply, Complex.real_smul] using h
  have h2 : Integrable (fun t : ℂ => (ρ t : ℂ) * g (z - t)) volume := by
    have h := hρcs.convolutionExists_left (L := ContinuousLinearMap.lsmul ℝ ℝ) hρc hg z
    simpa only [ConvolutionExistsAt, ContinuousLinearMap.lsmul_apply, Complex.real_smul] using h
  rw [Work.MRMT.Weyl.moll_apply, Work.MRMT.Weyl.moll_apply, Work.MRMT.Weyl.moll_apply,
    ← integral_add h1 h2]
  exact integral_congr_ae (Filter.Eventually.of_forall fun t => by ring)

/-- For a nonnegative function with finite `lintegral`, the integral over a subset is at most the
integral over the whole space. -/
theorem setIntegral_le_integral_of_lintegral_lt_top {g : ℂ → ℝ} {K : Set ℂ} (hg : 0 ≤ g)
    (hgm : AEStronglyMeasurable g volume) (hfin : ∫⁻ z, ENNReal.ofReal (g z) < ⊤) :
    ∫ z in K, g z ≤ ∫ z, g z := by
  have h1 : ∫ z in K, g z = (∫⁻ z in K, ENNReal.ofReal (g z)).toReal := by
    rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae (μ := volume.restrict K)
      (Filter.Eventually.of_forall hg) hgm.restrict]
  calc ∫ z in K, g z = (∫⁻ z in K, ENNReal.ofReal (g z)).toReal := h1
    _ ≤ (∫⁻ z, ENNReal.ofReal (g z)).toReal := by
        refine ENNReal.toReal_mono (ne_of_lt hfin) ?_
        simpa using lintegral_mono_set (μ := volume) (t := Set.univ) (Set.subset_univ K)
    _ = ∫ z, g z :=
        (MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hg) hgm).symm

/-- **`L²` convergence of mollification on compact sets.** -/
theorem moll_tendsto_L2 {G : ℂ → ℂ} (hG : MemLp G 2 (volume : Measure ℂ))
    {K : Set ℂ} (hK : IsCompact K) :
    Filter.Tendsto
      (fun n : ℕ =>
        ∫ z in K, ‖Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump n).normed volume) G z - G z‖ ^ 2)
      Filter.atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hη : (0:ℝ) < ε/12 := by positivity
  have hGK : MemLp G (ENNReal.ofReal 2) volume := by simpa using hG
  obtain ⟨φ, hφsupp, hφapx, hφcont, hφmem⟩ :=
    hGK.exists_hasCompactSupport_integral_rpow_sub_le (p := 2) (by norm_num) hη
  have hφmem' : MemLp φ 2 volume := by simpa using hφmem
  have hφapx' : ∫ z, ‖G z - φ z‖ ^ 2 ≤ ε/12 := by simpa using hφapx
  have hIntDiff : Integrable (fun z : ℂ => ‖G z - φ z‖ ^ 2) volume := by
    simpa using (hG.sub hφmem').integrable_norm_rpow (by norm_num) (by norm_num)
  have hunif : TendstoUniformlyOn
      (fun n => Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump n).normed volume) φ) φ atTop K :=
    Work.MRMT.Weyl.tendstoUniformlyOn_moll hφcont isOpen_univ hK (Set.subset_univ K)
      Work.MRMT.Weyl.bump Work.MRMT.Weyl.tendsto_rOut_bump
  set Cv : ℝ := ε / 12 / ((volume K).toReal + 1) with hCvdef
  have hCvpos : 0 < Cv := div_pos hη (by positivity)
  have hCvk : Cv * (volume K).toReal ≤ ε/12 := by
    rw [hCvdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [ENNReal.toReal_nonneg (a := volume K), hη.le]
  rw [Metric.tendstoUniformlyOn_iff] at hunif
  obtain ⟨N, hN⟩ : ∃ N, ∀ n ≥ N, ∀ z ∈ K,
      dist (φ z) (Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump n).normed volume) φ z)
        < Real.sqrt Cv := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hunif (Real.sqrt Cv) (Real.sqrt_pos.mpr hCvpos))
    exact ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (integral_nonneg fun z => sq_nonneg _)]
  set ρ : ℂ → ℝ := (Work.MRMT.Weyl.bump n).normed volume with hρdef
  have hρcd : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ := by rw [hρdef]; exact (Work.MRMT.Weyl.bump n).contDiff_normed
  have hρc : Continuous ρ := hρcd.continuous
  have hρcs : HasCompactSupport ρ := by rw [hρdef]; exact (Work.MRMT.Weyl.bump n).hasCompactSupport_normed
  have hρnn : ∀ y : ℂ, 0 ≤ ρ y := by rw [hρdef]; exact (Work.MRMT.Weyl.bump n).nonneg_normed
  have hρ1 : ∫ y, ρ y = 1 := by rw [hρdef]; exact (Work.MRMT.Weyl.bump n).integral_normed
  have hsm1 : ContDiff ℝ (↑(⊤ : ℕ∞)) (Work.MRMT.Weyl.moll ρ (fun w => G w - φ w)) :=
    Work.MRMT.Weyl.contDiff_moll (N := ⊤) hρcd hρcs ((hG.sub hφmem').locallyIntegrable (by norm_num))
  have hsm2 : ContDiff ℝ (↑(⊤ : ℕ∞)) (Work.MRMT.Weyl.moll ρ φ) :=
    Work.MRMT.Weyl.contDiff_moll (N := ⊤) hρcd hρcs hφcont.locallyIntegrable
  have hmollφ : ∀ z : ℂ, Work.MRMT.Weyl.moll ρ G z
      = Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z + Work.MRMT.Weyl.moll ρ φ z := by
    intro z
    have hadd := moll_add (f := fun w => G w - φ w) (g := φ)
      ((hG.sub hφmem').locallyIntegrable (by norm_num))
      hφcont.locallyIntegrable hρc hρcs z
    have hfun : (fun w => (G w - φ w) + φ w) = G := by funext w; ring
    rw [hfun] at hadd
    exact hadd
  have hpt : ∀ z : ℂ, ‖Work.MRMT.Weyl.moll ρ G z - G z‖ ^ 2
      ≤ 3 * (‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖ ^ 2
        + ‖Work.MRMT.Weyl.moll ρ φ z - φ z‖ ^ 2 + ‖φ z - G z‖ ^ 2) := by
    intro z
    have h1 : ‖Work.MRMT.Weyl.moll ρ G z - G z‖
        ≤ ‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖
          + ‖Work.MRMT.Weyl.moll ρ φ z - φ z‖ + ‖φ z - G z‖ := by
      rw [hmollφ z]
      have heq : (Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z + Work.MRMT.Weyl.moll ρ φ z)
          - G z
          = Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z
            + (Work.MRMT.Weyl.moll ρ φ z - φ z) + (φ z - G z) := by ring
      rw [heq]
      calc ‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z
            + (Work.MRMT.Weyl.moll ρ φ z - φ z) + (φ z - G z)‖
          ≤ ‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z
              + (Work.MRMT.Weyl.moll ρ φ z - φ z)‖ + ‖φ z - G z‖ := norm_add_le _ _
        _ ≤ (‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖
              + ‖Work.MRMT.Weyl.moll ρ φ z - φ z‖) + ‖φ z - G z‖ := by
            linarith [norm_add_le (Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z)
              (Work.MRMT.Weyl.moll ρ φ z - φ z)]
        _ = _ := by ring
    have h2 : (‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖
          + ‖Work.MRMT.Weyl.moll ρ φ z - φ z‖ + ‖φ z - G z‖) ^ 2
        ≤ 3 * (‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖ ^ 2
          + ‖Work.MRMT.Weyl.moll ρ φ z - φ z‖ ^ 2 + ‖φ z - G z‖ ^ 2) := by
      nlinarith [sq_nonneg (‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖
          - ‖Work.MRMT.Weyl.moll ρ φ z - φ z‖),
        sq_nonneg (‖Work.MRMT.Weyl.moll ρ φ z - φ z‖ - ‖φ z - G z‖),
        sq_nonneg (‖φ z - G z‖ - ‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖)]
    exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have hAI : IntegrableOn (fun z : ℂ =>
      ‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖ ^ 2) K volume :=
    ContinuousOn.integrableOn_compact hK ((hsm1.continuous.norm.pow 2).continuousOn)
  have hBI : IntegrableOn (fun z : ℂ => ‖Work.MRMT.Weyl.moll ρ φ z - φ z‖ ^ 2) K volume :=
    ContinuousOn.integrableOn_compact hK (((hsm2.continuous.sub hφcont).norm.pow 2).continuousOn)
  have hCI : IntegrableOn (fun z : ℂ => ‖φ z - G z‖ ^ 2) K volume :=
    hIntDiff.integrableOn.congr_fun (fun z _ => by
      rw [show φ z - G z = -(G z - φ z) from by ring, norm_neg]) hK.measurableSet
  have hSumI : IntegrableOn (fun z : ℂ =>
      3 * (‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖ ^ 2
        + ‖Work.MRMT.Weyl.moll ρ φ z - φ z‖ ^ 2 + ‖φ z - G z‖ ^ 2)) K volume :=
    ((hAI.add hBI).add hCI).const_mul 3
  have hbd : ∀ z ∈ K, ‖Work.MRMT.Weyl.moll ρ φ z - φ z‖ ^ 2 ≤ Cv := by
    intro z hz
    have h := hN n hn z hz
    have h2 : ‖Work.MRMT.Weyl.moll ρ φ z - φ z‖ < Real.sqrt Cv := by
      rw [dist_comm, dist_eq_norm] at h; exact h
    calc ‖Work.MRMT.Weyl.moll ρ φ z - φ z‖ ^ 2 ≤ (Real.sqrt Cv) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h2.le 2
      _ = Cv := Real.sq_sqrt hCvpos.le
  have hB : ∫ z in K, ‖Work.MRMT.Weyl.moll ρ φ z - φ z‖ ^ 2 ≤ ε/12 := by
    have h1 : ∫ z in K, ‖Work.MRMT.Weyl.moll ρ φ z - φ z‖ ^ 2 ≤ ∫ z in K, Cv :=
      setIntegral_mono_on hBI
        (MeasureTheory.integrableOn_const (s := K) (C := Cv) hK.measure_lt_top.ne (by simp))
        hK.measurableSet hbd
    have h2 : ∫ z in K, Cv = Cv * (volume K).toReal := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, MeasureTheory.Measure.real, mul_comm]
    rw [h2] at h1
    linarith [h1, hCvk]
  have hAcont : AEStronglyMeasurable (fun z : ℂ =>
      ‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖ ^ 2) volume :=
    (hsm1.continuous.norm.pow 2).aestronglyMeasurable
  have hAfin : ∫⁻ z, ENNReal.ofReal (‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖ ^ 2) < ⊤ := by
    refine lt_of_le_of_lt (QC.lintegral_ofReal_norm_sq_moll_le (f := fun w => G w - φ w)
      (hG.aestronglyMeasurable.sub hφcont.aestronglyMeasurable) hρnn hρ1 hρc.aestronglyMeasurable) ?_
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntDiff
      (Filter.Eventually.of_forall fun z => sq_nonneg _)]
    exact ENNReal.ofReal_lt_top
  have hA1 : ∫ z in K, ‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖ ^ 2
      ≤ ∫ z, ‖G z - φ z‖ ^ 2 := by
    have h2 : ∫ z in K, ‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖ ^ 2
        ≤ ∫ z, ‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖ ^ 2 :=
      setIntegral_le_integral_of_lintegral_lt_top (fun z => sq_nonneg _) hAcont hAfin
    have h3 : ∫ z, ‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖ ^ 2
        ≤ ∫ z, ‖G z - φ z‖ ^ 2 := by
      have h4 : ∫ z, ‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖ ^ 2
          = (∫⁻ z, ENNReal.ofReal (‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖ ^ 2)).toReal :=
        MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => sq_nonneg _)
          hAcont
      have h5 : ∫ z, ‖G z - φ z‖ ^ 2
          = (∫⁻ z, ENNReal.ofReal (‖G z - φ z‖ ^ 2)).toReal :=
        MeasureTheory.integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall fun z => sq_nonneg _)
          hIntDiff.aestronglyMeasurable
      rw [h4, h5]
      refine ENNReal.toReal_mono ?_ (QC.lintegral_ofReal_norm_sq_moll_le (f := fun w => G w - φ w)
        (hG.aestronglyMeasurable.sub hφcont.aestronglyMeasurable) hρnn hρ1 hρc.aestronglyMeasurable)
      rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntDiff
        (Filter.Eventually.of_forall fun z => sq_nonneg _)]
      exact ENNReal.ofReal_ne_top
    linarith [h2, h3]
  have hC1 : ∫ z in K, ‖φ z - G z‖ ^ 2 ≤ ∫ z, ‖G z - φ z‖ ^ 2 := by
    have heq : (fun z : ℂ => ‖φ z - G z‖ ^ 2) = fun z => ‖G z - φ z‖ ^ 2 := by
      funext z
      rw [show φ z - G z = -(G z - φ z) from by ring, norm_neg]
    rw [heq]
    exact setIntegral_le_integral_of_lintegral_lt_top (g := fun z : ℂ => ‖G z - φ z‖ ^ 2)
      (fun z => sq_nonneg _) hIntDiff.aestronglyMeasurable
      (by rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntDiff
            (Filter.Eventually.of_forall fun z => sq_nonneg _)]
          exact ENNReal.ofReal_lt_top)
  calc ∫ z in K, ‖Work.MRMT.Weyl.moll ρ G z - G z‖ ^ 2
      ≤ ∫ z in K, 3 * (‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖ ^ 2
          + ‖Work.MRMT.Weyl.moll ρ φ z - φ z‖ ^ 2 + ‖φ z - G z‖ ^ 2) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun z => sq_nonneg _) hSumI
          (Filter.Eventually.of_forall hpt)
    _ = 3 * ((∫ z in K, ‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖ ^ 2)
        + (∫ z in K, ‖Work.MRMT.Weyl.moll ρ φ z - φ z‖ ^ 2)
        + (∫ z in K, ‖φ z - G z‖ ^ 2)) := by
        have hsplitA : ∫ z in K, (‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖ ^ 2
            + ‖Work.MRMT.Weyl.moll ρ φ z - φ z‖ ^ 2)
            = (∫ z in K, ‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖ ^ 2)
              + (∫ z in K, ‖Work.MRMT.Weyl.moll ρ φ z - φ z‖ ^ 2) :=
          MeasureTheory.integral_add hAI hBI
        have hsplitB : ∫ z in K, (‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖ ^ 2
            + ‖Work.MRMT.Weyl.moll ρ φ z - φ z‖ ^ 2 + ‖φ z - G z‖ ^ 2)
            = (∫ z in K, (‖Work.MRMT.Weyl.moll ρ (fun w => G w - φ w) z‖ ^ 2
                + ‖Work.MRMT.Weyl.moll ρ φ z - φ z‖ ^ 2))
              + (∫ z in K, ‖φ z - G z‖ ^ 2) :=
          MeasureTheory.integral_add (hAI.add hBI) hCI
        rw [integral_const_mul, hsplitB, hsplitA]
    _ ≤ 3 * (ε/12 + ε/12 + ε/12) := by
        linarith [hA1, hφapx', hB, hC1]
    _ < ε := by linarith

/-- A function locally integrable and locally square integrable on `U`, truncated to a compact
subset of `U`, is in `L²(ℂ)`. -/
theorem memLp_indicator_of_memL2LocOn {p : ℂ → ℂ} {U S : Set ℂ} (hS : IsCompact S) (hSU : S ⊆ U)
    (hpLI : LocallyIntegrableOn p U volume) (hpL : Work.MRMT.MemL2LocOn p U) :
    MemLp (S.indicator p) 2 volume := by
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hAESM : AEStronglyMeasurable (S.indicator p) volume :=
    (aestronglyMeasurable_indicator_iff hSm).mpr
      ((MeasureTheory.LocallyIntegrableOn.aestronglyMeasurable hpLI).mono_measure
        (MeasureTheory.Measure.restrict_mono hSU le_rfl))
  refine (MeasureTheory.memLp_two_iff_integrable_sq_norm hAESM).mpr ?_
  have hint : IntegrableOn (fun z : ℂ => ‖p z‖ ^ 2) S volume :=
    (hpL S hS).mono_set (Set.subset_inter (subset_refl S) hSU)
  rw [show (fun z : ℂ => ‖S.indicator p z‖ ^ 2)
      = S.indicator (fun z : ℂ => ‖p z‖ ^ 2) from by
    funext z
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz, norm_zero, zero_pow (by norm_num)]]
  exact (integrable_indicator_iff hSm).mpr hint

/-- `dz χ z = 0` where `χ` is eventually equal to the constant `1`. -/
theorem dz_eq_zero_of_eventuallyEq_one {χ : ℂ → ℂ} {z : ℂ}
    (h : χ =ᶠ[𝓝 z] fun _ => (1 : ℂ)) : Work.MRMT.dz χ z = 0 := by
  rw [Work.MRMT.dz, h.fderiv_eq]; simp

theorem dzbar_eq_zero_of_eventuallyEq_one {χ : ℂ → ℂ} {z : ℂ}
    (h : χ =ᶠ[𝓝 z] fun _ => (1 : ℂ)) : Work.MRMT.dzbar χ z = 0 := by
  rw [Work.MRMT.dzbar, h.fderiv_eq]; simp

/-- `‖moll ρ G - G‖²` is integrable for `G ∈ L²` and a normalised nonnegative kernel. -/
theorem integrable_moll_sub_sq {G : ℂ → ℂ} (hG : MemLp G 2 (volume : Measure ℂ)) {ρ : ℂ → ℝ}
    (hρc : Continuous ρ) (hρcs : HasCompactSupport ρ) (hρnn : ∀ y, 0 ≤ ρ y)
    (hρ1 : ∫ y, ρ y = 1) :
    Integrable (fun z : ℂ => ‖Work.MRMT.Weyl.moll ρ G z - G z‖ ^ 2) volume := by
  have hIntG : Integrable (fun z : ℂ => ‖G z‖ ^ 2) volume := by
    simpa using hG.integrable_norm_rpow (by norm_num) (by norm_num)
  have hAESMm : AEStronglyMeasurable (Work.MRMT.Weyl.moll ρ G) volume := by
    rw [Work.MRMT.Weyl.moll]
    exact AEStronglyMeasurable.convolution (ContinuousLinearMap.lsmul ℝ ℝ)
      hρc.aestronglyMeasurable hG.aestronglyMeasurable
  have hAESMsq : AEStronglyMeasurable (fun z : ℂ => ‖Work.MRMT.Weyl.moll ρ G z‖ ^ 2) volume :=
    (hAESMm.norm).pow 2
  have hAESMsub : AEStronglyMeasurable
      (fun z : ℂ => ‖Work.MRMT.Weyl.moll ρ G z - G z‖ ^ 2) volume :=
    ((hAESMm.sub hG.aestronglyMeasurable).norm).pow 2
  have hfin : ∫⁻ z, ENNReal.ofReal (‖Work.MRMT.Weyl.moll ρ G z‖ ^ 2) < ⊤ := by
    refine lt_of_le_of_lt (QC.lintegral_ofReal_norm_sq_moll_le hG.aestronglyMeasurable hρnn hρ1
      hρc.aestronglyMeasurable) ?_
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hIntG
      (Filter.Eventually.of_forall fun z => sq_nonneg _)]
    exact ENNReal.ofReal_lt_top
  have hIntM : Integrable (fun z : ℂ => ‖Work.MRMT.Weyl.moll ρ G z‖ ^ 2) volume := by
    refine ⟨hAESMsq, ?_⟩
    rw [MeasureTheory.HasFiniteIntegral]
    have heq : (fun a : ℂ => ‖‖Work.MRMT.Weyl.moll ρ G a‖ ^ 2‖ₑ)
        = fun a : ℂ => ENNReal.ofReal (‖Work.MRMT.Weyl.moll ρ G a‖ ^ 2) := by
      funext a
      exact Real.enorm_eq_ofReal (sq_nonneg _)
    rw [heq]
    exact hfin
  refine Integrable.mono' ((hIntG.const_mul 2).add (hIntM.const_mul 2)) hAESMsub ?_
  filter_upwards with z
  rw [Real.norm_of_nonneg (sq_nonneg _), Pi.add_apply]
  linarith [norm_sub_sq_le (Work.MRMT.Weyl.moll ρ G z) (G z)]

/-- **`ε`-version of the smooth approximation.** -/
theorem smooth_approx_eps {f p q : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hp : Work.MRMT.IsDzDerivOn f p U) (hq : Work.MRMT.IsDbarDerivOn f q U)
    (hpL : Work.MRMT.MemL2LocOn p U) (hqL : Work.MRMT.MemL2LocOn q U)
    (hfc : ContinuousOn f U)
    {K : Set ℂ} (hK : IsCompact K) (hKU : K ⊆ U) {ε : ℝ} (hε : 0 < ε) :
    ∃ v : ℂ → ℂ, ContDiff ℝ (↑(⊤ : ℕ∞)) v ∧ HasCompactSupport v ∧
      (∀ z ∈ K, ‖v z - f z‖ ≤ ε) ∧
      (∫ z in K, ‖Work.MRMT.dz v z - p z‖ ^ 2 ≤ ε) ∧
      (∫ z in K, ‖Work.MRMT.dzbar v z - q z‖ ^ 2 ≤ ε) := by
  obtain ⟨δ, hδpos, hδK⟩ := hK.exists_cthickening_subset_open hU hKU
  have hKc : IsCompact (Metric.cthickening (δ/2) K) := hK.cthickening (r := δ/2)
  have hKcU : Metric.cthickening (δ/2) K ⊆ U :=
    (Metric.cthickening_mono (by linarith) K).trans hδK
  obtain ⟨χ, hχcd, hχcs, hχts, W, hWo, hKW, hχ1⟩ := smooth_cutoff hU hKc hKcU
  have hχcont : Continuous (fun z => χ z * f z) :=
    continuous_mul_of_tsupport_subset hU hχcd.continuous hχts hfc
  -- the uniform convergence of `moll ρ (χ f)` to `χ f` on `K`
  have hunif : TendstoUniformlyOn
      (fun n => Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump n).normed volume)
        (fun z => χ z * f z)) (fun z => χ z * f z) atTop K :=
    Work.MRMT.Weyl.tendstoUniformlyOn_moll hχcont isOpen_univ hK (Set.subset_univ K)
      Work.MRMT.Weyl.bump Work.MRMT.Weyl.tendsto_rOut_bump
  -- derivative L² convergence data
  have hSG : MemLp ((Metric.cthickening (δ/2) K).indicator p) 2 volume :=
    memLp_indicator_of_memL2LocOn hKc hKcU hp.2.1 hpL
  have hSH : MemLp ((Metric.cthickening (δ/2) K).indicator q) 2 volume :=
    memLp_indicator_of_memL2LocOn hKc hKcU hq.2.1 hqL
  have hpconv := moll_tendsto_L2 hSG hK
  have hqconv := moll_tendsto_L2 hSH hK
  -- choose `n`
  have hEvUniform : ∀ᶠ n : ℕ in Filter.atTop, ∀ z ∈ K,
      ‖χ z * f z - Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump n).normed volume)
        (fun z => χ z * f z) z‖ < ε := by
    rw [Metric.tendstoUniformlyOn_iff] at hunif
    filter_upwards [hunif ε hε] with n hn
    intro z hz
    have h := hn z hz
    rwa [dist_eq_norm] at h
  have hEvδ : ∀ᶠ n : ℕ in Filter.atTop, (Work.MRMT.Weyl.bump n).rOut ≤ δ/2 :=
    (Work.MRMT.Weyl.tendsto_rOut_bump.eventually (eventually_le_nhds (by linarith)))
  have hEvP : ∀ᶠ n : ℕ in Filter.atTop,
      ∫ z in K, ‖Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump n).normed volume)
        ((Metric.cthickening (δ/2) K).indicator p) z
        - (Metric.cthickening (δ/2) K).indicator p z‖ ^ 2 < ε := by
    filter_upwards [Filter.eventually_atTop.mpr ((Metric.tendsto_atTop.mp hpconv) ε hε)]
      with n hn
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (integral_nonneg fun z => sq_nonneg _)] at hn
    exact hn
  have hEvQ : ∀ᶠ n : ℕ in Filter.atTop,
      ∫ z in K, ‖Work.MRMT.Weyl.moll ((Work.MRMT.Weyl.bump n).normed volume)
        ((Metric.cthickening (δ/2) K).indicator q) z
        - (Metric.cthickening (δ/2) K).indicator q z‖ ^ 2 < ε := by
    filter_upwards [Filter.eventually_atTop.mpr ((Metric.tendsto_atTop.mp hqconv) ε hε)]
      with n hn
    rw [Real.dist_eq, sub_zero,
      abs_of_nonneg (integral_nonneg fun z => sq_nonneg _)] at hn
    exact hn
  obtain ⟨n, hnU, hnδ, hnP, hnQ⟩ := (hEvUniform.and (hEvδ.and (hEvP.and hEvQ))).exists
  set ρ : ℂ → ℝ := (Work.MRMT.Weyl.bump n).normed volume with hρdef
  have hρcd : ContDiff ℝ (↑(⊤ : ℕ∞)) ρ := by
    rw [hρdef]; exact (Work.MRMT.Weyl.bump n).contDiff_normed
  have hρcs : HasCompactSupport ρ := by
    rw [hρdef]; exact (Work.MRMT.Weyl.bump n).hasCompactSupport_normed
  have hρnn : ∀ y : ℂ, 0 ≤ ρ y := by
    rw [hρdef]; exact (Work.MRMT.Weyl.bump n).nonneg_normed
  have hρ1 : ∫ y, ρ y = 1 := by
    rw [hρdef]; exact (Work.MRMT.Weyl.bump n).integral_normed
  have hρc : Continuous ρ := hρcd.continuous
  refine ⟨Work.MRMT.Weyl.moll ρ (fun z => χ z * f z), ?_, ?_, ?_, ?_, ?_⟩
  · exact Work.MRMT.Weyl.contDiff_moll (N := ⊤) hρcd hρcs
      hχcont.locallyIntegrable
  · -- compact support
    have hcs : HasCompactSupport (fun z : ℂ => χ z * f z) := by
      refine HasCompactSupport.of_support_subset_isCompact (K := tsupport χ)
        hχcs.isCompact ?_
      exact subset_closure.trans (tsupport_mul_subset_left (f := χ) (g := f))
    exact HasCompactSupport.convolution (L := ContinuousLinearMap.lsmul ℝ ℝ) hρcs hcs
  · -- uniform bound
    intro z hz
    have h := hnU z hz
    have hzχ : χ z = 1 := hχ1 z (hKW (Metric.self_subset_cthickening K hz))
    simp only [hzχ, one_mul] at h
    rw [norm_sub_rev]
    exact h.le
  · -- `∂`-derivative
    have hFG : Work.MRMT.IsDzDerivOn (fun z => χ z * f z)
        (fun z => χ z * p z + f z * Work.MRMT.dz χ z) U :=
      isDzDerivOn_mul hU hfc hχcd hχcs hχts hp
    have hloc : LocallyIntegrable (fun z => χ z * f z) volume := hχcont.locallyIntegrable
    have hzs : ∀ z ∈ K, ∀ t ∈ tsupport ρ, z - t ∈ U := by
      intro z hz t ht
      have htr : ‖t‖ ≤ (Work.MRMT.Weyl.bump n).rOut := by
        have h1 : t ∈ tsupport ((Work.MRMT.Weyl.bump n).normed volume) := by rwa [← hρdef]
        rw [ContDiffBump.tsupport_normed_eq] at h1
        simpa [Metric.mem_closedBall, dist_eq_norm] using h1
      refine hKcU (Metric.mem_cthickening_of_dist_le (z - t) z (δ/2) K hz ?_)
      rw [dist_eq_norm, show z - t - z = -t by ring, norm_neg]
      linarith
    have hpoint : ∀ z ∈ K, Work.MRMT.dz (Work.MRMT.Weyl.moll ρ (fun z => χ z * f z)) z
        = Work.MRMT.Weyl.moll ρ ((Metric.cthickening (δ/2) K).indicator p) z := by
      intro z hz
      rw [Work.MRMT.QCDegree.dz_moll (U := U) hFG hloc hρcd hρcs (z := z) (hzs z hz)]
      rw [Work.MRMT.Weyl.moll_apply, Work.MRMT.Weyl.moll_apply]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      dsimp only
      by_cases ht : ρ t = 0
      · simp [ht]
      · have ht' : t ∈ Function.support ρ := ht
        rw [hρdef, ContDiffBump.support_normed_eq] at ht'
        have htr : ‖t‖ < (Work.MRMT.Weyl.bump n).rOut := by
          simpa [Metric.mem_ball, dist_eq_norm] using ht'
        have hzt : z - t ∈ Metric.cthickening (δ/2) K := by
          refine Metric.mem_cthickening_of_dist_le (z - t) z (δ/2) K hz ?_
          rw [dist_eq_norm, show z - t - z = -t by ring, norm_neg]
          linarith
        have hzW : z - t ∈ W := hKW hzt
        have hχzt : χ (z - t) = 1 := hχ1 (z - t) hzW
        have hdzχ : Work.MRMT.dz χ (z - t) = 0 :=
          dz_eq_zero_of_eventuallyEq_one
            (Filter.mem_of_superset (hWo.mem_nhds hzW) fun w hw => hχ1 w hw)
        rw [Set.indicator_of_mem hzt, hχzt, hdzχ]
        ring
    refine le_trans ?_ hnP.le
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _)
      ((integrable_moll_sub_sq hSG hρc hρcs hρnn hρ1).integrableOn) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hK.measurableSet] with z hz
    rw [hpoint z hz, Set.indicator_of_mem (Metric.self_subset_cthickening K hz)]
  · -- `∂̄`-derivative
    have hFG : Work.MRMT.IsDbarDerivOn (fun z => χ z * f z)
        (fun z => χ z * q z + f z * Work.MRMT.dzbar χ z) U :=
      isDbarDerivOn_mul hU hfc hχcd hχcs hχts hq
    have hloc : LocallyIntegrable (fun z => χ z * f z) volume := hχcont.locallyIntegrable
    have hzs : ∀ z ∈ K, ∀ t ∈ tsupport ρ, z - t ∈ U := by
      intro z hz t ht
      have htr : ‖t‖ ≤ (Work.MRMT.Weyl.bump n).rOut := by
        have h1 : t ∈ tsupport ((Work.MRMT.Weyl.bump n).normed volume) := by rwa [← hρdef]
        rw [ContDiffBump.tsupport_normed_eq] at h1
        simpa [Metric.mem_closedBall, dist_eq_norm] using h1
      refine hKcU (Metric.mem_cthickening_of_dist_le (z - t) z (δ/2) K hz ?_)
      rw [dist_eq_norm, show z - t - z = -t by ring, norm_neg]
      linarith
    have hpoint : ∀ z ∈ K, Work.MRMT.dzbar (Work.MRMT.Weyl.moll ρ (fun z => χ z * f z)) z
        = Work.MRMT.Weyl.moll ρ ((Metric.cthickening (δ/2) K).indicator q) z := by
      intro z hz
      rw [Work.MRMT.QCDegree.dzbar_moll (U := U) hFG hloc hρcd hρcs (z := z) (hzs z hz)]
      rw [Work.MRMT.Weyl.moll_apply, Work.MRMT.Weyl.moll_apply]
      refine integral_congr_ae (Filter.Eventually.of_forall fun t => ?_)
      dsimp only
      by_cases ht : ρ t = 0
      · simp [ht]
      · have ht' : t ∈ Function.support ρ := ht
        rw [hρdef, ContDiffBump.support_normed_eq] at ht'
        have htr : ‖t‖ < (Work.MRMT.Weyl.bump n).rOut := by
          simpa [Metric.mem_ball, dist_eq_norm] using ht'
        have hzt : z - t ∈ Metric.cthickening (δ/2) K := by
          refine Metric.mem_cthickening_of_dist_le (z - t) z (δ/2) K hz ?_
          rw [dist_eq_norm, show z - t - z = -t by ring, norm_neg]
          linarith
        have hzW : z - t ∈ W := hKW hzt
        have hχzt : χ (z - t) = 1 := hχ1 (z - t) hzW
        have hdzχ : Work.MRMT.dzbar χ (z - t) = 0 :=
          dzbar_eq_zero_of_eventuallyEq_one
            (Filter.mem_of_superset (hWo.mem_nhds hzW) fun w hw => hχ1 w hw)
        rw [Set.indicator_of_mem hzt, hχzt, hdzχ]
        ring
    refine le_trans ?_ hnQ.le
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => sq_nonneg _)
      ((integrable_moll_sub_sq hSH hρc hρcs hρnn hρ1).integrableOn) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem hK.measurableSet] with z hz
    rw [hpoint z hz, Set.indicator_of_mem (Metric.self_subset_cthickening K hz)]

/-- **Main theorem.** A function with distributional `∂`- and `∂̄`-derivatives in `L²_loc` on an
open set `U`, and continuous on `U`, is approximated on compact subsets of `U` by smooth compactly
supported functions, together with their `∂`- and `∂̄`-derivatives in `L²`. -/
theorem smooth_approx_w12 {f p q : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hp : Work.MRMT.IsDzDerivOn f p U) (hq : Work.MRMT.IsDbarDerivOn f q U)
    (hpL : Work.MRMT.MemL2LocOn p U) (hqL : Work.MRMT.MemL2LocOn q U)
    (hfc : ContinuousOn f U) :
    ∃ F : ℕ → ℂ → ℂ,
      (∀ n, ContDiff ℝ (↑(⊤ : ℕ∞)) (F n)) ∧ (∀ n, HasCompactSupport (F n)) ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ U → TendstoUniformlyOn F f atTop K) ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ U →
        Filter.Tendsto (fun n => ∫ z in K, ‖F n z - f z‖ ^ 2) Filter.atTop (nhds 0)) ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ U →
        Filter.Tendsto (fun n => ∫ z in K, ‖Work.MRMT.dz (F n) z - p z‖ ^ 2) Filter.atTop (nhds 0)) ∧
      (∀ K : Set ℂ, IsCompact K → K ⊆ U →
        Filter.Tendsto (fun n => ∫ z in K, ‖Work.MRMT.dzbar (F n) z - q z‖ ^ 2) Filter.atTop (nhds 0)) := by
  obtain ⟨Kx, hKxC, _hKxmono, hKxU, hcof⟩ := compact_exhaustion hU
  exact build_sequence hKxC hKxU hcof hp hq hpL hqL hfc
    (fun n => smooth_approx_eps hU hp hq hpL hqL hfc (hKxC n) (hKxU n) (by positivity))

end Work.MRMT.QC
