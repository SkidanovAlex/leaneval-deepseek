/-
# The uniform asymptotic `Φ c / c → 1`

This file proves `Work.ParamRays.UniformBottcherAsymptotic` — the second of the two classical
inputs of the NAKANE contract, and one of the three fields of `Work.ParamRays.NakaneInput`:

`∀ ε > 0, ∀ᶠ c, ∀ φ, IsCritBottcher c φ → ‖φ c − c‖ ≤ ε ‖c‖`.

Two ingredients.

* **The product formula satisfies it.**  `Work.Bottcher.Critical.Phi_isBigO_atTop` proves
  `Φ_prod c / c → 1` for the product-formula Böttcher map, and away from the mandelbar
  `Φ_prod c = bottcher c c` (`Work.Bottcher.Phi_eq_bottcher`), so
  `bottcher c c / c → 1` (`Work.NAKANE.bottcher_self_div_tendsto_one`, `PotentialTop`).
* **The canonical coordinate equals the product formula there.**  For `‖c‖ > 8` the ratio
  `φ_c(c) / bottcher c c` is a fourth root of unity (both sides have the same fourth power, by the
  functional equations `varphiCrit_functional_iterate` / `bottcher_comm_pMap_iterate`, the far
  identity `jointVarphi_eq_jointBottcher_of_far'`, and `farRadius_lt_norm_pMap_self`) and is
  *continuous* in `c`, hence constant on the (preconnected) exterior `{8 < ‖c‖}`
  (`Work.NAKANE.Topological.eq_of_continuousOn_pow_eq_one`); at the real parameter `9` the ratio is
  a quotient of two positive reals (`Work.NAKANE.Asymptotic.varphiCrit_self_pos_of_real`,
  `Work.NAKANE.Asymptotic.bottcher_real_pos`), hence equals `1`.  So
  `varphiCrit c c = bottcher c c` for `‖c‖ > 8` (`varphiCrit_self_eq_bottcher_self`).

The statement for an arbitrary `IsCritBottcher` family follows from uniqueness
(`Work.Bottcher.varphiCrit_unique`).
-/
import Submission.Work.NAKANE.PotentialTop
import Submission.Work.NAKANE.BottcherFar.continuousOn_bottcher_self
import Submission.Work.NAKANE.Asymptotic.bottcher_real_pos
import Submission.Work.NAKANE.Asymptotic.varphiCrit_self_pos_of_real

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology ComplexConjugate

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

namespace Work.NAKANE

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

/-- The mandelbar is contained in the closed ball of radius `2`. -/
theorem norm_le_two_of_mem_Mb {c : ℂ} (hc : c ∈ Mb) : ‖c‖ ≤ 2 := by
  have h := Work.ParamRays.mandelbar_subset_closedBall hc
  rwa [Metric.mem_closedBall, dist_zero_right] at h

/-- The product formula does not vanish on the diagonal. -/
theorem bottcher_self_ne_zero {c : ℂ} (hc : c ≠ 0) : Work.Bottcher.bottcher c c ≠ 0 := by
  rw [Work.Bottcher.bottcher]
  exact mul_ne_zero hc (Complex.exp_ne_zero _)

/-- **The parameter Böttcher map is the product formula at large parameters.** -/
theorem varphiCrit_self_eq_bottcher_self {c : ℂ} (hc : 8 < ‖c‖) :
    Work.Bottcher.varphiCrit c c = Work.Bottcher.bottcher c c := by
  have hfar_nb : ∀ {c' : ℂ}, 8 < ‖c'‖ → c' ∉ Mb := fun {c'} hc' h => by
    have h1 := norm_le_two_of_mem_Mb h
    linarith
  have hcMb : c ∉ Mb := hfar_nb hc
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hc
    norm_num at hc
  have hcrit : c ∈ Work.ParamRays.critDomain c := Work.ParamRays.self_mem_critDomain hcMb
  -- the fourth power of the ratio is `1`
  have hpow : ∀ c' : ℂ, 8 < ‖c'‖ →
      (Work.Bottcher.varphiCrit c' c' / Work.Bottcher.bottcher c' c') ^ 4 = 1 := by
    intro c' hc'
    have hc'Mb : c' ∉ Mb := hfar_nb hc'
    have hc'ne : c' ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hc'
      norm_num at hc'
    have hcrit' : c' ∈ Work.ParamRays.critDomain c' := Work.ParamRays.self_mem_critDomain hc'Mb
    have h1 : (Work.Bottcher.varphiCrit c' c') ^ 4
        = Work.Bottcher.varphiCrit c' (Work.Bottcher.pMap c' c') := by
      have h := varphiCrit_functional_iterate hcrit' 1
      simpa using h
    have h2 : Work.Bottcher.varphiCrit c' (Work.Bottcher.pMap c' c')
        = Work.Bottcher.bottcher c' (Work.Bottcher.pMap c' c') :=
      jointVarphi_eq_jointBottcher_of_far' (C := ‖c'‖) le_rfl
        (farRadius_lt_norm_pMap_self hc')
    have h3 : Work.Bottcher.bottcher c' (Work.Bottcher.pMap c' c')
        = (Work.Bottcher.bottcher c' c') ^ 4 :=
      (Work.NAKANE.BottcherFar.bottcher_comm_pMap_iterate hcrit' 1).symm
    rw [div_pow, h1, h2, h3]
    exact div_self (pow_ne_zero 4 (bottcher_self_ne_zero hc'ne))
  have hcont : ContinuousOn
      (fun c' : ℂ => Work.Bottcher.varphiCrit c' c' / Work.Bottcher.bottcher c' c')
      {z : ℂ | 8 < ‖z‖} := by
    refine ContinuousOn.div ?_ ?_ ?_
    · refine continuousOn_varphiCrit_self.mono ?_
      intro c' hc'
      exact hfar_nb (Set.mem_ofPred_eq.mp hc')
    · refine Work.NAKANE.BottcherFar.continuousOn_bottcher_self.mono ?_
      intro c' hc'
      exact le_of_lt (Set.mem_ofPred_eq.mp hc')
    · intro c' hc'
      have hc'ne : c' ≠ 0 := by
        intro h0
        have h1 : (8 : ℝ) < ‖c'‖ := Set.mem_ofPred_eq.mp hc'
        rw [h0, norm_zero] at h1
        norm_num at h1
      exact bottcher_self_ne_zero hc'ne
  have h9mem : (9 : ℂ) ∈ {z : ℂ | 8 < ‖z‖} := by
    rw [Set.mem_ofPred_eq]
    norm_num
  have hcmem : c ∈ {z : ℂ | 8 < ‖z‖} := Set.mem_ofPred_eq.mpr hc
  -- the ratio is constant on the exterior of the disc of radius `8`, with the value at `9`
  have hconst := Work.NAKANE.Topological.eq_of_continuousOn_pow_eq_one
    (Work.ParamRays.isPreconnected_lt_norm (M := 8) (by norm_num)) hcont (m := 4) (by norm_num)
    (fun z hz => hpow z (Set.mem_ofPred_eq.mp hz)) h9mem hcmem
  have h9 : Work.Bottcher.varphiCrit (9 : ℂ) (9 : ℂ)
      / Work.Bottcher.bottcher (9 : ℂ) (9 : ℂ) = 1 := by
    obtain ⟨r, hr, hr9⟩ := Work.NAKANE.Asymptotic.varphiCrit_self_pos_of_real (c := 9) (by norm_num)
    obtain ⟨s, hs, hs9⟩ := Work.NAKANE.Asymptotic.bottcher_real_pos (c := 9) (x := 9)
      (by norm_num) (by norm_num)
    have hr9' : Work.Bottcher.varphiCrit (9 : ℂ) (9 : ℂ) = (r : ℂ) := by
      simpa only [Complex.ofReal_ofNat] using hr9
    have hs9' : Work.Bottcher.bottcher (9 : ℂ) (9 : ℂ) = (s : ℂ) := by
      simpa only [Complex.ofReal_ofNat] using hs9
    have h1 : Work.Bottcher.varphiCrit (9 : ℂ) (9 : ℂ)
        / Work.Bottcher.bottcher (9 : ℂ) (9 : ℂ) = ((r / s : ℝ) : ℂ) := by
      rw [hr9', hs9', ← Complex.ofReal_div]
    have h2 : ((r / s : ℝ) : ℂ) ^ 4 = 1 := by
      rw [← h1]
      exact hpow 9 (by norm_num)
    have h3 : (r / s : ℝ) ^ 4 = 1 := by exact_mod_cast h2
    have hpos : 0 < r / s := div_pos hr hs
    have h4 : (r / s : ℝ) = 1 := by
      have h5 : ((r / s : ℝ)) ^ 2 = 1 := by nlinarith [h3, sq_nonneg ((r / s : ℝ) ^ 2 - 1)]
      nlinarith [h5, hpos]
    rw [h1, h4]
    norm_num
  have hratio : Work.Bottcher.varphiCrit c c / Work.Bottcher.bottcher c c = 1 := by
    rw [← hconst]
    exact h9
  exact (div_eq_one_iff_eq (bottcher_self_ne_zero hcne)).mp hratio

/-- **The uniform asymptotic input `UniformBottcherAsymptotic`**, unconditionally. -/
theorem uniformBottcherAsymptotic : Work.ParamRays.UniformBottcherAsymptotic := by
  intro ε hε
  have h1 : ∀ᶠ c : ℂ in cocompact ℂ,
      ‖Work.Bottcher.bottcher c c / c - 1‖ < ε := by
    have := (Metric.tendsto_nhds.mp bottcher_self_div_tendsto_one) ε hε
    simpa [dist_eq_norm] using this
  filter_upwards [h1, tendsto_norm_cocompact_atTop.eventually (eventually_gt_atTop (8 : ℝ)),
    Work.ParamRays.eventually_not_mem_mandelbar] with c hc hcbig hcMb
  intro φ hφ
  have hcne : c ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hcbig
    norm_num at hcbig
  have hφeq : φ c = Work.Bottcher.varphiCrit c c :=
    (Work.Bottcher.varphiCrit_unique hφ (Work.ParamRays.self_mem_critDomain hcMb)).symm
  rw [hφeq, varphiCrit_self_eq_bottcher_self hcbig,
    show Work.Bottcher.bottcher c c - c = c * (Work.Bottcher.bottcher c c / c - 1) by field_simp,
    norm_mul]
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hcne
  calc ‖c‖ * ‖Work.Bottcher.bottcher c c / c - 1‖ ≤ ‖c‖ * ε :=
        le_of_lt (mul_lt_mul_of_pos_left hc hcpos)
    _ = ε * ‖c‖ := by ring

end Work.NAKANE
