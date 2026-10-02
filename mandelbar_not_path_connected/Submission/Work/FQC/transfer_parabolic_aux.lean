/-
# `Work.FQC.transfer_parabolic_aux`

Transport of the root-parabolic structure along a topological conjugacy `θ` of the
antipolynomial family that is asymptotically the identity at `∞`:

if `θ (T_c z) = T_{c₂} (θ z)`, `θ 0 = 0` and `‖θ z - z‖ ≤ C / ‖z‖` for large `z`, then a
root-parabolic parameter `c` is transported to a root-parabolic parameter `c₂`
(`Nonempty (RootParabolic c₂)`), the parabolic point being `θ d.z₁`.

The file is self-contained on top of the vocabulary of the workspace: it proves

* the transport of iterates, of the filled Julia set and of the escaping set (§0);
* the transport of the Böttcher coordinate `IsDynBottcher` (§1) and of the dynamical
  Nakane data `DynB` together with the ray points, rays, ray pieces, equipotential arcs
  and their sides (§2);
* the transport of landing (`landsAt`, §3);
* the multiplier of the transported parabolic point is `1` (§4), via the topological
  characterisation of a parabolic germ: a germ of a holomorphic map with a non-attracting,
  non-repelling fixed point, admitting both a "petal" of converging points and a repelling
  coordinate accumulating at the fixed point, has multiplier `1`;
* the assembly of `RootParabolic c₂` (§5).
-/
import Mathlib
import Submission.Work.ELTop.Defs
import Submission.Work.ParamRays.Bottcher
import Submission.Work.ParamRays.Interface
import Submission.Work.ParamRays.isDynBottcher_unique
import Submission.Work.FatouCoord.Flower
import Submission.Work.FatouCoord.Flower.exists_parabolicFlower
import Submission.Work.Landing.Family.deriv_tsq_iterate_odd_real

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open scoped Topology ComplexConjugate
open Filter Set Function
open Classical

set_option linter.unusedVariables false

noncomputable section

namespace Work.FQC

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)
open Work.EL (RootParabolic F K)

/-! ## 0. The iterates `Tsq` and `F` (local copies, to keep this file independent)

These two identities are the only facts about the ambient `Work.FQC` vocabulary this file
uses; they are proved here so that the module does not depend on `Submission.Work.FQC.Defs`. -/

/-- `Tsq c = (Tantibar c)^[2]`. -/
theorem tsq_eq_iterate_local (c : ℂ) : Work.Landing.Tsq c = (Tantibar c)^[2] := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, Function.iterate_add, Function.iterate_one]
  funext z
  rw [Function.comp_apply, Work.Landing.Tsq_apply, Work.Landing.Tantibar_apply,
    Work.Landing.Tantibar_apply]
  simp only [star_add, star_pow, star_star]

/-- `F c = (Tantibar c)^[10]`. -/
theorem elF_eq_iterate_local (c : ℂ) : F c = (Tantibar c)^[10] := by
  rw [Work.EL.F, tsq_eq_iterate_local, show (10 : ℕ) = 2 * 5 by norm_num,
    Function.iterate_mul]

/-! ## 0. Transport along a conjugating homeomorphism -/

/-- The homeomorphism `θ` intertwines the iterates of the antipolynomial. -/
theorem theta_iterate {c c₂ : ℂ} (θ : ℂ ≃ₜ ℂ)
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) (n : ℕ) (z : ℂ) :
    θ ((Tantibar c)^[n] z) = (Tantibar c₂)^[n] (θ z) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Function.iterate_succ_apply', hconj, ih]

/-- The inverse homeomorphism intertwines the dynamics in the other direction. -/
theorem theta_symm_conj {c c₂ : ℂ} (θ : ℂ ≃ₜ ℂ)
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) (z : ℂ) :
    θ.symm (Tantibar c₂ z) = Tantibar c (θ.symm z) := by
  apply θ.injective
  rw [θ.apply_symm_apply, hconj, θ.apply_symm_apply]

/-- A continuous self-map of `ℂ` is bounded on a closed ball. -/
theorem exists_bound_image_closedBall (θ : ℂ ≃ₜ ℂ) (M : ℝ) :
    ∃ M' : ℝ, 0 ≤ M' ∧ ∀ w : ℂ, ‖w‖ ≤ M → ‖θ w‖ ≤ M' := by
  obtain ⟨M', hM'⟩ := (isCompact_closedBall (0:ℂ) M).exists_bound_of_continuousOn
    θ.continuous.continuousOn
  refine ⟨max M' 0, le_max_right _ _, fun w hw => ?_⟩
  exact le_trans (hM' w (by simpa [Metric.mem_closedBall, dist_eq_norm] using hw)) (le_max_left _ _)

/-- Bounded orbits are preserved by a topological conjugacy. -/
theorem boundedOrbit_transfer {c c₂ : ℂ} (θ : ℂ ≃ₜ ℂ)
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) (z : ℂ) :
    Work.ParamRays.BoundedOrbit c z ↔ Work.ParamRays.BoundedOrbit c₂ (θ z) := by
  constructor
  · rintro ⟨M, hM⟩
    obtain ⟨M', _, hM'⟩ := exists_bound_image_closedBall θ M
    exact ⟨M', fun n => by
      rw [Work.ParamRays.orbit, ← theta_iterate θ hconj n z]
      exact hM' _ (hM n)⟩
  · rintro ⟨M, hM⟩
    obtain ⟨M', _, hM'⟩ := exists_bound_image_closedBall θ.symm M
    exact ⟨M', fun n => by
      have h2 : ‖(Tantibar c₂)^[n] (θ z)‖ ≤ M := hM n
      have h3 : θ.symm ((Tantibar c₂)^[n] (θ z)) = (Tantibar c)^[n] z := by
        rw [theta_iterate θ.symm (theta_symm_conj θ hconj) n (θ z), θ.symm_apply_apply]
      rw [Work.ParamRays.orbit, ← h3]
      exact hM' _ h2⟩

/-- The filled Julia set is transported to the filled Julia set. -/
theorem mem_K_iff {c c₂ : ℂ} (θ : ℂ ≃ₜ ℂ)
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) (z : ℂ) :
    z ∈ K c ↔ θ z ∈ K c₂ :=
  boundedOrbit_transfer θ hconj z

/-- Escaping sets are transported. -/
theorem escaping_transfer {c c₂ : ℂ} (θ : ℂ ≃ₜ ℂ)
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) (z : ℂ) :
    Work.ParamRays.Escaping c z ↔ Work.ParamRays.Escaping c₂ (θ z) := by
  rw [Work.ParamRays.escaping_iff_not_bounded, Work.ParamRays.escaping_iff_not_bounded,
    boundedOrbit_transfer θ hconj]

/-- The escaping set of `c₂` is the preimage of that of `c` under `θ.symm`. -/
theorem escapingSet_preimage {c c₂ : ℂ} (θ : ℂ ≃ₜ ℂ)
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) :
    Work.ParamRays.escapingSet c₂ = (θ.symm : ℂ → ℂ) ⁻¹' Work.ParamRays.escapingSet c := by
  ext w
  show Work.ParamRays.Escaping c₂ w ↔ Work.ParamRays.Escaping c (θ.symm w)
  rw [escaping_transfer θ hconj (θ.symm w), θ.apply_symm_apply]

/-- **The inverse of an asymptotically identity homeomorphism is asymptotically the
identity.**  If `‖θ z - z‖ ≤ C / ‖z‖` for large `z`, then the same holds for `θ.symm`. -/
theorem symm_decay_aux (θ : ℂ ≃ₜ ℂ)
    (hdecay : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖θ z - z‖ ≤ C / ‖z‖) :
    ∃ C R : ℝ, 0 ≤ C ∧ ∀ z : ℂ, R ≤ ‖z‖ → ‖θ.symm z - z‖ ≤ C / ‖z‖ := by
  obtain ⟨C₀, R₀, hC₀⟩ := hdecay
  set C₁ : ℝ := max C₀ 1 with hC₁def
  have hge1 : 1 ≤ C₁ := le_max_right _ _
  have hCpos : 0 ≤ C₁ := le_trans zero_le_one hge1
  have hCdec : ∀ z : ℂ, max R₀ 1 ≤ ‖z‖ → ‖θ z - z‖ ≤ C₁ / ‖z‖ := by
    intro z hz
    have h1 : ‖θ z - z‖ ≤ C₀ / ‖z‖ := hC₀ z (le_trans (le_max_left _ _) hz)
    have h2 : C₀ / ‖z‖ ≤ C₁ / ‖z‖ :=
      div_le_div_of_nonneg_right (le_max_left _ _) (norm_nonneg z)
    linarith
  obtain ⟨B, hB0, hB⟩ := exists_bound_image_closedBall θ (max R₀ 1)
  have hCfin : 0 ≤ max (2 * C₁) B + 2 := by
    have h1 : 0 ≤ 2 * C₁ := by linarith
    have h2 := le_max_left (2 * C₁) B
    linarith
  refine ⟨max (2 * C₁) B + 2, max (2 * C₁) B + 1, hCfin, ?_⟩
  intro z hz
  set w : ℂ := θ.symm z with hwdef
  have hzw : θ w = z := θ.apply_symm_apply z
  have hzpos : 0 < ‖z‖ := by
    have := le_max_left (2 * C₁) B
    linarith [norm_nonneg z]
  by_cases hw : max R₀ 1 ≤ ‖w‖
  · have h1 : ‖z - w‖ ≤ C₁ / ‖w‖ := by
      have h := hCdec w hw
      rwa [hzw] at h
    have hw1 : 1 ≤ ‖w‖ := le_trans (le_max_right R₀ (1:ℝ)) hw
    have hwpos : 0 < ‖w‖ := lt_of_lt_of_le one_pos hw1
    have h4 : ‖z - w‖ ≤ C₁ := by
      have h5 : C₁ / ‖w‖ ≤ C₁ := by
        rw [div_le_iff₀ hwpos]
        nlinarith [hw1, hCpos]
      linarith
    have h3 : ‖z‖ - C₁ ≤ ‖w‖ := by
      have h5 : ‖z‖ ≤ ‖z - w‖ + ‖w‖ := by
        calc ‖z‖ = ‖(z - w) + w‖ := by ring_nf
          _ ≤ ‖z - w‖ + ‖w‖ := norm_add_le _ _
      linarith
    have hd : 0 < ‖z‖ - C₁ := by
      have := le_max_left (2 * C₁) B
      linarith [norm_nonneg z]
    have step1 : C₁ / ‖w‖ ≤ C₁ / (‖z‖ - C₁) :=
      div_le_div_of_nonneg_left hCpos hd h3
    have step2 : C₁ / (‖z‖ - C₁) ≤ (max (2 * C₁) B + 2) / ‖z‖ := by
      rw [div_le_iff₀ hd, div_mul_eq_mul_div, le_div_iff₀ hzpos]
      have h1' : 2 * C₁ ≤ max (2 * C₁) B := le_max_left _ _
      have h2' : B ≤ max (2 * C₁) B := le_max_right _ _
      nlinarith [hz, hCpos, hB0, norm_nonneg z]
    have : ‖w - z‖ ≤ (max (2 * C₁) B + 2) / ‖z‖ := by
      rw [norm_sub_rev]
      linarith [h1, step1, step2]
    exact this
  · have hb : ‖z‖ ≤ B := by
      have := hB w (le_of_lt (not_le.mp hw))
      rwa [hzw] at this
    have hle : max (2 * C₁) B + 1 ≤ B := le_trans hz hb
    have h2 := le_max_right (2 * C₁) B
    linarith

/-! ## 1. Transport of the Böttcher coordinate -/

/-- `p z` eventually holds outside a large ball, in the form of an explicit threshold. -/
theorem exists_norm_ge_of_eventually_cocompact {p : ℂ → Prop}
    (h : ∀ᶠ z : ℂ in Filter.cocompact ℂ, p z) : ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → p z := by
  obtain ⟨t, ht, hts⟩ := Filter.mem_cocompact.mp h
  obtain ⟨R, hR⟩ := ht.isBounded.exists_norm_le
  refine ⟨max R 0 + 1, fun z hz => hts ?_⟩
  by_contra hzt
  have hzt' : z ∈ t := not_not.mp hzt
  have := hR z hzt'
  linarith [le_max_left R 0, le_max_right R 0]

/-- Conversely, an estimate valid outside a ball holds eventually in `cocompact ℂ`. -/
theorem eventually_cocompact_of_exists {p : ℂ → Prop} (h : ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → p z) :
    ∀ᶠ z : ℂ in Filter.cocompact ℂ, p z := by
  obtain ⟨R, hR⟩ := h
  refine Filter.mem_cocompact.mpr ⟨Metric.closedBall (0:ℂ) R, isCompact_closedBall _ _, ?_⟩
  intro z hz
  rw [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
  exact hR z (le_of_lt hz)

/-- **Transport of the Böttcher coordinate.** -/
theorem isDynBottcher_transfer {c c₂ : ℂ} {θ : ℂ ≃ₜ ℂ} {φ : ℂ → ℂ}
    (hb : Work.ParamRays.IsDynBottcher c φ)
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z))
    (hdecay : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖θ z - z‖ ≤ C / ‖z‖) :
    Work.ParamRays.IsDynBottcher c₂ (φ ∘ (θ.symm : ℂ → ℂ)) := by
  obtain ⟨C, R, hC⟩ := hdecay
  obtain ⟨C', R', hC'0, hC'⟩ := symm_decay_aux θ ⟨C, R, hC⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [escapingSet_preimage θ hconj]
    exact ContinuousOn.comp hb.1 θ.symm.continuous.continuousOn fun x hx => hx
  · intro z hz
    have hzw : Work.ParamRays.Escaping c (θ.symm z) :=
      (escaping_transfer θ hconj (θ.symm z)).mpr (by rwa [θ.apply_symm_apply])
    have h := hb.2.1 (θ.symm z) hzw
    rw [← theta_symm_conj θ hconj z] at h
    simpa [Function.comp_apply] using h
  · intro ε hε
    set ε' : ℝ := min ε 1 with hε'def
    have hε' : 0 < ε' := lt_min hε one_pos
    have hε'1 : ε' ≤ 1 := by rw [hε'def]; exact min_le_right _ _
    have hle' : ε' ≤ ε := min_le_left _ _
    have hε'4 : 0 < ε' / 4 := by linarith
    obtain ⟨R₁, hR₁⟩ := exists_norm_ge_of_eventually_cocompact (hb.2.2 (ε' / 4) hε'4)
    obtain ⟨Bθ, hBθ0, hBθ⟩ := exists_bound_image_closedBall θ 1
    refine eventually_cocompact_of_exists
      ⟨max (max (R₁ + C' + 1) (Bθ + 1)) (max (Real.sqrt (C' / (ε' / 4)) + 1) (R' + 1)) + 1,
        fun z hz => ?_⟩
    have hK1 : R₁ + C' + 1 ≤ ‖z‖ := by
      have h := le_max_left (max (R₁ + C' + 1) (Bθ + 1))
        (max (Real.sqrt (C' / (ε' / 4)) + 1) (R' + 1))
      have h' := le_max_left (R₁ + C' + 1) (Bθ + 1)
      linarith
    have hK2 : Bθ + 1 ≤ ‖z‖ := by
      have h := le_max_left (max (R₁ + C' + 1) (Bθ + 1))
        (max (Real.sqrt (C' / (ε' / 4)) + 1) (R' + 1))
      have h' := le_max_right (R₁ + C' + 1) (Bθ + 1)
      linarith
    have hK3 : Real.sqrt (C' / (ε' / 4)) + 1 ≤ ‖z‖ := by
      have h := le_max_right (max (R₁ + C' + 1) (Bθ + 1))
        (max (Real.sqrt (C' / (ε' / 4)) + 1) (R' + 1))
      have h' := le_max_left (Real.sqrt (C' / (ε' / 4)) + 1) (R' + 1)
      linarith
    have hK4 : R' + 1 ≤ ‖z‖ := by
      have h := le_max_right (max (R₁ + C' + 1) (Bθ + 1))
        (max (Real.sqrt (C' / (ε' / 4)) + 1) (R' + 1))
      have h' := le_max_right (Real.sqrt (C' / (ε' / 4)) + 1) (R' + 1)
      linarith
    have hz1 : 1 ≤ ‖z‖ := by linarith
    have hzpos : 0 < ‖z‖ := by linarith
    have h_zw_ge1 : 1 ≤ ‖θ.symm z‖ := by
      by_contra hcon
      have hlt : ‖θ.symm z‖ < 1 := not_le.mp hcon
      have hb := hBθ (θ.symm z) (le_of_lt hlt)
      rw [θ.apply_symm_apply] at hb
      linarith
    have hdec : ‖θ.symm z - z‖ ≤ C' / ‖z‖ := hC' z (by linarith)
    have h3 : C' / ‖z‖ ≤ (ε' / 4) * ‖z‖ := by
      rw [div_le_iff₀ hzpos]
      have hkey : C' ≤ (ε' / 4) * (‖z‖ * ‖z‖) := by
        rcases lt_or_ge 0 C' with hC'' | hC''
        · have h4 : Real.sqrt (C' / (ε' / 4)) ≤ ‖z‖ := by linarith
          have h6 : Real.sqrt (C' / (ε' / 4)) ^ 2 = C' / (ε' / 4) :=
            Real.sq_sqrt (by positivity)
          have h6' : (ε' / 4) * Real.sqrt (C' / (ε' / 4)) ^ 2 = C' := by
            rw [h6, mul_div_cancel₀ _ (ne_of_gt hε'4)]
          have h7 : Real.sqrt (C' / (ε' / 4)) ^ 2 ≤ ‖z‖ ^ 2 :=
            pow_le_pow_left₀ (Real.sqrt_nonneg _) h4 2
          have h8 : (ε' / 4) * Real.sqrt (C' / (ε' / 4)) ^ 2 ≤ (ε' / 4) * ‖z‖ ^ 2 :=
            mul_le_mul_of_nonneg_left h7 (by linarith)
          nlinarith [h6', h8]
        · have h9 : 0 ≤ (ε' / 4) * (‖z‖ * ‖z‖) := by positivity
          linarith
      nlinarith [hkey]
    have h_zw_le : ‖θ.symm z‖ ≤ 2 * ‖z‖ := by
      have h2 : ‖θ.symm z‖ ≤ ‖z‖ + ‖θ.symm z - z‖ := by
        calc ‖θ.symm z‖ = ‖z + (θ.symm z - z)‖ := by ring_nf
          _ ≤ ‖z‖ + ‖θ.symm z - z‖ := norm_add_le _ _
      nlinarith [h2, hdec, h3, hε'1, hzpos]
    have h_zw_ge_R1 : R₁ ≤ ‖θ.symm z‖ := by
      have hcz : C' / ‖z‖ ≤ C' := by
        rw [div_le_iff₀ hzpos]
        nlinarith [hz1, hC'0]
      have h2 : ‖z‖ - C' ≤ ‖θ.symm z‖ := by
        have h5 : ‖z‖ ≤ ‖θ.symm z‖ + ‖θ.symm z - z‖ := by
          calc ‖z‖ = ‖θ.symm z + (z - θ.symm z)‖ := by ring_nf
            _ ≤ ‖θ.symm z‖ + ‖z - θ.symm z‖ := norm_add_le _ _
            _ = ‖θ.symm z‖ + ‖θ.symm z - z‖ := by rw [norm_sub_rev]
        linarith
      linarith
    calc ‖(φ ∘ (θ.symm : ℂ → ℂ)) z - z‖ = ‖φ (θ.symm z) - z‖ := rfl
      _ ≤ ‖φ (θ.symm z) - θ.symm z‖ + ‖θ.symm z - z‖ := by
          have := norm_add_le (φ (θ.symm z) - θ.symm z) (θ.symm z - z)
          rwa [sub_add_sub_cancel] at this
      _ ≤ (ε' / 4) * ‖θ.symm z‖ + (ε' / 4) * ‖z‖ := by
          have h1 := hR₁ (θ.symm z) h_zw_ge_R1
          linarith [hdec, h3]
      _ ≤ (ε' / 4) * (2 * ‖z‖) + (ε' / 4) * ‖z‖ := by
          have h2 := h_zw_le
          have h5 : 0 ≤ ε' / 4 := by linarith
          nlinarith
      _ ≤ ε * ‖z‖ := by nlinarith [hle', norm_nonneg z, hε']

/-! ## 2. Transport of the dynamical Nakane data -/

/-- Membership of `θ.symm z` in the filled Julia set of `c` is membership of `z` in that of `c₂`. -/
theorem mem_K_symm_iff {c c₂ : ℂ} (θ : ℂ ≃ₜ ℂ)
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) (z : ℂ) :
    θ.symm z ∈ K c ↔ z ∈ K c₂ := by
  rw [mem_K_iff θ hconj (θ.symm z), θ.apply_symm_apply]

/-- The Böttcher coordinate of the transported data at `θ z` is the value at `z`. -/
theorem dynPhi_comp_transfer {c c₂ : ℂ} {θ : ℂ ≃ₜ ℂ} {φ : ℂ → ℂ}
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) {z : ℂ} (hz : z ∉ K c) :
    Work.EL.dynPhi c₂ (φ ∘ (θ.symm : ℂ → ℂ)) (θ z) = Work.EL.dynPhi c φ z := by
  have hzθ : θ z ∉ K c₂ := fun h => hz ((mem_K_iff θ hconj z).mpr h)
  rw [Work.EL.dynPhi_of_notMem hzθ, Function.comp_apply, θ.symm_apply_apply]
  exact (Work.EL.dynPhi_of_notMem hz).symm

/-- The homeomorphism of the complements of the filled Julia sets induced by `θ`. -/
def KcomplHomeo {c c₂ : ℂ} (θ : ℂ ≃ₜ ℂ)
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) : ↥(K c₂)ᶜ ≃ₜ ↥(K c)ᶜ :=
  Homeomorph.subtype θ.symm fun z => by
    rw [Set.mem_compl_iff, Set.mem_compl_iff]
    exact (mem_K_symm_iff θ hconj z).not.symm

/-- **Transport of the dynamical Nakane data.** -/
noncomputable def nakane_transfer {c c₂ : ℂ} {θ : ℂ ≃ₜ ℂ} {φ : ℂ → ℂ}
    (hN : Work.EL.DynB c φ)
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z))
    (hdecay : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖θ z - z‖ ≤ C / ‖z‖) :
    Work.EL.DynB c₂ (φ ∘ (θ.symm : ℂ → ℂ)) := by
  have hmem : ∀ z : ℂ, z ∈ (K c₂)ᶜ ↔ θ.symm z ∈ (K c)ᶜ := by
    intro z
    rw [Set.mem_compl_iff, Set.mem_compl_iff]
    exact (mem_K_symm_iff θ hconj z).not.symm
  have hpot : Work.Top.potential (K c₂) (Work.EL.dynPhi c₂ (φ ∘ (θ.symm : ℂ → ℂ)))
      = (Work.Top.potential (K c) (Work.EL.dynPhi c φ)) ∘ (θ.symm : ℂ → ℂ) := by
    funext z
    rw [Function.comp_apply]
    by_cases hz : z ∈ K c₂
    · rw [Work.Top.potential_of_mem hz,
        Work.Top.potential_of_mem ((mem_K_symm_iff θ hconj z).mpr hz)]
    · have hz' : θ.symm z ∉ K c := fun h => hz ((mem_K_symm_iff θ hconj z).mp h)
      rw [Work.Top.potential_of_not_mem hz, Work.Top.potential_of_not_mem hz',
        Work.EL.dynPhi_of_notMem hz, Work.EL.dynPhi_of_notMem hz']
      simp only [Function.comp_apply]
  refine ⟨(KcomplHomeo θ hconj).trans hN.e, ?_, ?_, ?_, ?_⟩
  · intro z
    show Work.EL.dynPhi c₂ (φ ∘ (θ.symm : ℂ → ℂ)) (z : ℂ) = _
    rw [Work.EL.dynPhi_of_notMem z.2, Function.comp_apply]
    have h := hN.he ⟨θ.symm (z : ℂ), (hmem (z:ℂ)).mp z.2⟩
    rw [Work.EL.dynPhi_of_notMem ((hmem (z:ℂ)).mp z.2)] at h
    exact h
  · intro z hz
    exact Work.EL.dynPhi_of_mem hz
  · rw [hpot]
    exact hN.continuous_potential.comp θ.symm.continuous
  · intro t
    obtain ⟨C', R', hC'0, hC'⟩ := symm_decay_aux θ hdecay
    obtain ⟨R₁, hR₁⟩ := hN.tendsto_potential t
    obtain ⟨Bθ, hBθ0, hBθ⟩ := exists_bound_image_closedBall θ 1
    refine ⟨max (max (R₁ + C' + 1) (R' + 1)) (Bθ + 1) + 1, fun z hz => ?_⟩
    have hK1 : R₁ + C' + 1 ≤ ‖z‖ := by
      have h := le_max_left (max (R₁ + C' + 1) (R' + 1)) (Bθ + 1)
      have h' := le_max_left (R₁ + C' + 1) (R' + 1); linarith
    have hK3 : R' + 1 ≤ ‖z‖ := by
      have h := le_max_left (max (R₁ + C' + 1) (R' + 1)) (Bθ + 1)
      have h' := le_max_right (R₁ + C' + 1) (R' + 1); linarith
    have hK2 : Bθ + 1 ≤ ‖z‖ := by
      have := le_max_right (max (R₁ + C' + 1) (R' + 1)) (Bθ + 1); linarith
    have hz1 : 1 ≤ ‖z‖ := by linarith
    have hzpos : 0 < ‖z‖ := by linarith
    have h_ge1 : 1 ≤ ‖θ.symm z‖ := by
      by_contra hcon
      have hlt : ‖θ.symm z‖ < 1 := not_le.mp hcon
      have hb := hBθ (θ.symm z) (le_of_lt hlt)
      rw [θ.apply_symm_apply] at hb
      linarith
    have hcz : C' / ‖z‖ ≤ C' := by
      rw [div_le_iff₀ hzpos]
      nlinarith [hz1, hC'0]
    have hdec : ‖θ.symm z - z‖ ≤ C' / ‖z‖ := hC' z (by linarith)
    have h1 : R₁ ≤ ‖θ.symm z‖ := by
      have h5 : ‖z‖ ≤ ‖θ.symm z‖ + ‖θ.symm z - z‖ := by
        calc ‖z‖ = ‖θ.symm z + (z - θ.symm z)‖ := by ring_nf
          _ ≤ ‖θ.symm z‖ + ‖z - θ.symm z‖ := norm_add_le _ _
          _ = ‖θ.symm z‖ + ‖θ.symm z - z‖ := by rw [norm_sub_rev]
      linarith
    rw [hpot]
    exact hR₁ (θ.symm z) h1

/-! ### Ray points, rays, curves and their sides -/

/-- Ray points are transported. -/
theorem rayPt_transfer {c c₂ : ℂ} {θ : ℂ ≃ₜ ℂ} {φ : ℂ → ℂ}
    {hN : Work.EL.DynB c φ} {hN₂ : Work.EL.DynB c₂ (φ ∘ (θ.symm : ℂ → ℂ))}
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) {ϑ t : ℝ} (ht : 1 < t) :
    hN₂.rayPt ϑ t = θ (hN.rayPt ϑ t) := by
  have h1 : hN₂.rayPt ϑ t ∉ K c₂ := hN₂.rayPt_notMem ht
  have h2 : θ (hN.rayPt ϑ t) ∉ K c₂ :=
    fun h => hN.rayPt_notMem ht ((mem_K_iff θ hconj _).mpr h)
  refine hN₂.injOn_Phi h1 h2 ?_
  rw [hN₂.Phi_rayPt ht, dynPhi_comp_transfer hconj (hN.rayPt_notMem ht), hN.Phi_rayPt ht]

/-- Dynamic rays are transported. -/
theorem paramRay_transfer {c c₂ : ℂ} {θ : ℂ ≃ₜ ℂ} {φ : ℂ → ℂ}
    {hN : Work.EL.DynB c φ} {hN₂ : Work.EL.DynB c₂ (φ ∘ (θ.symm : ℂ → ℂ))}
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) (ϑ : ℝ) :
    hN₂.paramRay ϑ = θ '' hN.paramRay ϑ := by
  rw [Work.Top.NakaneData.paramRay_eq_range, Work.Top.NakaneData.paramRay_eq_range]
  ext w
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨hN.rayPt ϑ t.1, ⟨t, rfl⟩, (rayPt_transfer hconj t.2).symm⟩
  · rintro ⟨w', ⟨t, rfl⟩, rfl⟩
    exact ⟨t, rayPt_transfer hconj t.2⟩

/-- The curve of a pair of rays is transported. -/
theorem rawCurve_transfer {c c₂ : ℂ} {θ : ℂ ≃ₜ ℂ} {φ : ℂ → ℂ}
    {hN : Work.EL.DynB c φ} {hN₂ : Work.EL.DynB c₂ (φ ∘ (θ.symm : ℂ → ℂ))}
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) (P : Work.EL.RawPair) :
    Work.EL.RawPair.curve hN₂ ⟨P.a, P.b, θ P.y⟩ = θ '' Work.EL.RawPair.curve hN P := by
  simp only [Work.EL.RawPair.curve, Work.EL.paramRay, Set.image_union, Set.image_singleton]
  rw [paramRay_transfer hconj, paramRay_transfer hconj]

/-- The image of a connected component under a homeomorphism, without a membership
hypothesis (both sides are empty when the point is outside the set). -/
theorem homeomorph_image_connectedComponentIn {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (h : X ≃ₜ Y) (s : Set X) (x : X) :
    h '' connectedComponentIn s x = connectedComponentIn (h '' s) (h x) := by
  by_cases hx : x ∈ s
  · exact h.image_connectedComponentIn hx
  · rw [connectedComponentIn_eq_empty hx, Set.image_empty, connectedComponentIn_eq_empty]
    rintro ⟨y, hy, hyx⟩
    exact hx (h.injective hyx ▸ hy)

/-- The side of a pair of rays is transported. -/
theorem sideThrough_transfer {c c₂ : ℂ} {θ : ℂ ≃ₜ ℂ} {φ : ℂ → ℂ}
    {hN : Work.EL.DynB c φ} {hN₂ : Work.EL.DynB c₂ (φ ∘ (θ.symm : ℂ → ℂ))}
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) (P : Work.EL.RawPair)
    (θ₁ θ₂ : ℝ) :
    Work.EL.RawPair.sideThrough hN₂ ⟨P.a, P.b, θ P.y⟩ θ₁ θ₂
      = θ '' Work.EL.RawPair.sideThrough hN P θ₁ θ₂ := by
  rw [Work.EL.RawPair.sideThrough, Work.EL.RawPair.sideThrough]
  have hmid : Work.EL.rayPt hN₂ (θ₁ + Work.EL.arcLen θ₁ θ₂ / 2) 2
      = θ (Work.EL.rayPt hN (θ₁ + Work.EL.arcLen θ₁ θ₂ / 2) 2) :=
    rayPt_transfer hconj (by norm_num)
  rw [hmid, rawCurve_transfer hconj P, ← Set.image_compl_eq θ.bijective]
  exact (homeomorph_image_connectedComponentIn θ _ _).symm

/-- **The wake sides are transported.** -/
theorem iterate_conj {c c₂ : ℂ} {θ : ℂ ≃ₜ ℂ}
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) (z : ℂ) (j : ℕ) :
    θ ((Tantibar c)^[j] z) = (Tantibar c₂)^[j] (θ z) := by
  induction j generalizing z with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih, hconj]

theorem wakeSide_transfer {c c₂ : ℂ} {θ : ℂ ≃ₜ ℂ} {φ : ℂ → ℂ}
    {hN : Work.EL.DynB c φ} {hN₂ : Work.EL.DynB c₂ (φ ∘ (θ.symm : ℂ → ℂ))}
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) (z₁ : ℂ) (j : ℕ) :
    Work.EL.wakeSide hN₂ (θ z₁) j = θ '' Work.EL.wakeSide hN z₁ j := by
  rw [Work.EL.wakeSide, Work.EL.wakeSide, Work.EL.alphaPairRaw, Work.EL.alphaPairRaw]
  rw [← iterate_conj hconj z₁ j]
  exact sideThrough_transfer hconj (Work.EL.alphaPairRaw c z₁ j) (Work.EL.wakeLo j)
    (Work.EL.wakeHi j)

/-! ## 3. Transport of landing -/

/-- Dynamic rays (as sets) are transported. -/
theorem dynRay_transfer {c c₂ : ℂ} {θ : ℂ ≃ₜ ℂ} {φ : ℂ → ℂ}
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) (ϑ : ℝ) :
    Work.Landing.dynRay c₂ (φ ∘ (θ.symm : ℂ → ℂ)) ϑ = θ '' Work.Landing.dynRay c φ ϑ := by
  ext w
  constructor
  · intro hw
    refine ⟨θ.symm w, ⟨?_, ?_⟩, θ.apply_symm_apply w⟩
    · exact (escaping_transfer θ hconj (θ.symm w)).mpr (by rw [θ.apply_symm_apply]; exact hw.1)
    · simpa [Function.comp_apply, θ.symm_apply_apply] using hw.2
  · rintro ⟨z, ⟨hz, hrad⟩, rfl⟩
    exact ⟨(escaping_transfer θ hconj z).mp hz, by
      simpa [Function.comp_apply, θ.symm_apply_apply] using hrad⟩

/-- The accumulation set of a ray depends only on the values of the Böttcher coordinate on the
escaping set. -/
theorem rayAccum_congr {c : ℂ} {φ ψ : ℂ → ℂ}
    (h : ∀ z : ℂ, Work.ParamRays.Escaping c z → φ z = ψ z) (ϑ : ℝ) :
    Work.Landing.rayAccum c φ ϑ = Work.Landing.rayAccum c ψ ϑ := by
  have key : ∀ ρ : ℝ, {z : ℂ | z ∈ Work.Landing.dynRay c φ ϑ ∧ ‖φ z‖ ≤ ρ}
      = {z : ℂ | z ∈ Work.Landing.dynRay c ψ ϑ ∧ ‖ψ z‖ ≤ ρ} := by
    intro ρ
    ext z
    constructor
    · rintro ⟨hz, hρ⟩
      have hesc : Work.ParamRays.Escaping c z := hz.1
      exact ⟨⟨hesc, by rw [← h z hesc]; exact hz.2⟩, by rw [← h z hesc]; exact hρ⟩
    · rintro ⟨hz, hρ⟩
      have hesc : Work.ParamRays.Escaping c z := hz.1
      exact ⟨⟨hesc, by rw [h z hesc]; exact hz.2⟩, by rw [h z hesc]; exact hρ⟩
  ext x
  simp only [Work.Landing.rayAccum, Set.mem_setOf_eq]
  constructor
  · intro hx ρ hρ
    rw [← key ρ]
    exact hx ρ hρ
  · intro hx ρ hρ
    rw [key ρ]
    exact hx ρ hρ

/-- The accumulation set of a ray is transported. -/
theorem rayAccum_transfer {c c₂ : ℂ} {θ : ℂ ≃ₜ ℂ} {φ : ℂ → ℂ}
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) (ϑ : ℝ) :
    Work.Landing.rayAccum c₂ (φ ∘ (θ.symm : ℂ → ℂ)) ϑ
      = θ '' Work.Landing.rayAccum c φ ϑ := by
  have key : ∀ ρ : ℝ, θ '' {z : ℂ | z ∈ Work.Landing.dynRay c φ ϑ ∧ ‖φ z‖ ≤ ρ}
      = {w : ℂ | w ∈ Work.Landing.dynRay c₂ (φ ∘ (θ.symm : ℂ → ℂ)) ϑ
          ∧ ‖(φ ∘ (θ.symm : ℂ → ℂ)) w‖ ≤ ρ} := by
    intro ρ
    rw [dynRay_transfer hconj ϑ]
    ext w
    constructor
    · rintro ⟨z, ⟨hz, hρ⟩, rfl⟩
      exact ⟨⟨z, hz, rfl⟩, by simpa [Function.comp_apply, θ.symm_apply_apply] using hρ⟩
    · rintro ⟨⟨z, hz, rfl⟩, hρ⟩
      exact ⟨z, ⟨hz, by simpa [Function.comp_apply, θ.symm_apply_apply] using hρ⟩, rfl⟩
  have himg : ∀ ρ : ℝ, θ '' closure {z : ℂ | z ∈ Work.Landing.dynRay c φ ϑ ∧ ‖φ z‖ ≤ ρ}
      = closure {w : ℂ | w ∈ Work.Landing.dynRay c₂ (φ ∘ (θ.symm : ℂ → ℂ)) ϑ
          ∧ ‖(φ ∘ (θ.symm : ℂ → ℂ)) w‖ ≤ ρ} := by
    intro ρ
    rw [Homeomorph.image_closure, key ρ]
  ext x
  simp only [Work.Landing.rayAccum, Set.mem_setOf_eq]
  constructor
  · intro hx
    refine ⟨θ.symm x, ?_, θ.apply_symm_apply x⟩
    intro ρ hρ
    have hx' : x ∈ θ '' closure {z : ℂ | z ∈ Work.Landing.dynRay c φ ϑ ∧ ‖φ z‖ ≤ ρ} := by
      rw [himg ρ]
      exact hx ρ hρ
    obtain ⟨y, hy, hyx⟩ := hx'
    rw [← hyx, θ.symm_apply_apply]
    exact hy
  · rintro ⟨y, hy, rfl⟩ ρ hρ
    rw [← himg ρ]
    exact ⟨y, hy ρ hρ, rfl⟩

/-- **Landing is transported.** -/
theorem landsAt_transfer {c c₂ : ℂ} (θ : ℂ ≃ₜ ℂ)
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z))
    (hdecay : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖θ z - z‖ ≤ C / ‖z‖)
    {φ : ℂ → ℂ} (hb : Work.ParamRays.IsDynBottcher c φ) (ϑ : ℝ) (z : ℂ) :
    Work.Landing.landsAt c ϑ z ↔ Work.Landing.landsAt c₂ ϑ (θ z) := by
  constructor
  · rintro ⟨ψ, hψ, hland⟩
    refine ⟨ψ ∘ (θ.symm : ℂ → ℂ), isDynBottcher_transfer hψ hconj hdecay, ?_⟩
    rw [Work.Landing.RayLands] at hland ⊢
    rw [rayAccum_transfer hconj ϑ, hland, Set.image_singleton]
  · rintro ⟨ψ₂, hψ₂, hland₂⟩
    refine ⟨φ, hb, ?_⟩
    rw [Work.Landing.RayLands] at hland₂ ⊢
    have hcongr : Work.Landing.rayAccum c₂ ψ₂ ϑ
        = Work.Landing.rayAccum c₂ (φ ∘ (θ.symm : ℂ → ℂ)) ϑ :=
      rayAccum_congr (fun w hw => by
        rw [Function.comp_apply]
        exact Work.ParamRays.isDynBottcher_unique hψ₂
          (isDynBottcher_transfer hb hconj hdecay) hw) ϑ
    have himg := rayAccum_transfer (c := c) (c₂ := c₂) (θ := θ) hconj ϑ (φ := φ)
    have hset : θ '' Work.Landing.rayAccum c φ ϑ = {θ z} := by
      rw [← himg, ← hcongr, hland₂]
    ext a
    constructor
    · intro ha
      have hmem : θ a = θ z := by
        have hmem' : θ a ∈ ({θ z} : Set ℂ) := by
          rw [← hset]
          exact ⟨a, ha, rfl⟩
        simpa using hmem'
      exact θ.injective hmem
    · intro ha
      have ha' : a = z := by simpa using ha
      rw [ha']
      have hmem : θ z ∈ θ '' Work.Landing.rayAccum c φ ϑ := by
        rw [hset]
        exact rfl
      obtain ⟨b, hb, hbz⟩ := hmem
      have hbz' : b = z := θ.injective hbz
      rwa [hbz'] at hb

/-! ## 4. The multiplier of a transported parabolic point -/

/-- The local contraction estimate at a fixed point whose multiplier has modulus `< c < 1`. -/
theorem exists_contraction_radius {F : ℂ → ℂ} {z₀ : ℂ} (hfix : F z₀ = z₀)
    (hF : DifferentiableAt ℂ F z₀) {c : ℝ} (hc : ‖deriv F z₀‖ < c) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ ≤ δ → ‖F (z₀ + u) - z₀‖ ≤ c * ‖u‖ := by
  set lam := deriv F z₀
  have hε : 0 < (c - ‖lam‖) / 2 := by linarith
  have hb : ∀ᶠ h : ℂ in 𝓝 0, ‖F (z₀ + h) - F z₀ - h * lam‖ ≤ (c - ‖lam‖) / 2 * ‖h‖ := by
    have h := Asymptotics.IsLittleO.def (hasDerivAt_iff_isLittleO_nhds_zero.mp hF.hasDerivAt) hε
    filter_upwards [h] with h hh
    simpa [smul_eq_mul] using hh
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hb
  refine ⟨δ / 2, by linarith, fun u hu => ?_⟩
  have h1 : dist u 0 < δ := by rw [dist_zero_right]; linarith
  have h2 : ‖F (z₀ + u) - F z₀ - u * lam‖ ≤ _ := hδ h1
  have h3 : ‖F (z₀ + u) - z₀‖ ≤ ‖F (z₀ + u) - F z₀ - u * lam‖ + ‖u * lam‖ := by
    calc ‖F (z₀ + u) - z₀‖ = ‖(F (z₀ + u) - F z₀ - u * lam) + u * lam‖ := by
          rw [hfix]; ring_nf
      _ ≤ _ := norm_add_le _ _
  have h4 : ‖u * lam‖ = ‖u‖ * ‖lam‖ := norm_mul u lam
  nlinarith [h2, h3, h4, norm_nonneg u, norm_nonneg lam, hu]

/-- The local expansion estimate at a fixed point whose multiplier has modulus `> c`. -/
theorem exists_expansion_radius {F : ℂ → ℂ} {z₀ : ℂ} (hfix : F z₀ = z₀)
    (hF : DifferentiableAt ℂ F z₀) {c : ℝ} (hc : c < ‖deriv F z₀‖) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ u : ℂ, ‖u‖ ≤ δ → c * ‖u‖ ≤ ‖F (z₀ + u) - z₀‖ := by
  set lam := deriv F z₀
  have hε : 0 < (‖lam‖ - c) / 2 := by linarith
  have hb : ∀ᶠ h : ℂ in 𝓝 0, ‖F (z₀ + h) - F z₀ - h * lam‖ ≤ (‖lam‖ - c) / 2 * ‖h‖ := by
    have h := Asymptotics.IsLittleO.def (hasDerivAt_iff_isLittleO_nhds_zero.mp hF.hasDerivAt) hε
    filter_upwards [h] with h hh
    simpa [smul_eq_mul] using hh
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hb
  refine ⟨δ / 2, by linarith, fun u hu => ?_⟩
  have h1 : dist u 0 < δ := by rw [dist_zero_right]; linarith
  have h2 : ‖F (z₀ + u) - F z₀ - u * lam‖ ≤ _ := hδ h1
  have h3 : ‖u * lam‖ ≤ ‖F (z₀ + u) - z₀‖ + ‖F (z₀ + u) - F z₀ - u * lam‖ := by
    calc ‖u * lam‖ = ‖(F (z₀ + u) - z₀) - (F (z₀ + u) - F z₀ - u * lam)‖ := by
          rw [hfix]; ring_nf
      _ ≤ _ := norm_sub_le _ _
  have h4 : ‖u * lam‖ = ‖u‖ * ‖lam‖ := norm_mul u lam
  nlinarith [h2, h3, h4, norm_nonneg u, norm_nonneg lam, hu]

/-- **The topological characterisation of a parabolic germ.**  If a holomorphic germ with a fixed
point admits both a set of points converging to the fixed point (accumulating there) and a
"repelling coordinate" ψ with `ψ (w+1) = F (ψ w)` converging to the fixed point as `Re w → -∞`,
then the multiplier has modulus `1`: the fixed point is neither attracting nor repelling. -/
theorem norm_deriv_eq_one_of_flower_data {F : ℂ → ℂ} {z₀ : ℂ} (hfix : F z₀ = z₀)
    (hF : DifferentiableAt ℂ F z₀) {Pa : Set ℂ} {Ψ : ℂ → ℂ}
    (hPa_not : z₀ ∉ Pa) (hPa_maps : MapsTo F Pa Pa)
    (hPa_tend : ∀ y ∈ Pa, Tendsto (fun n : ℕ => F^[n] y) atTop (nhds z₀))
    (hPa_acc : ∀ ε : ℝ, 0 < ε → ∃ y ∈ Pa, 0 < ‖y - z₀‖ ∧ ‖y - z₀‖ < ε)
    (hΨ_shift : ∀ w : ℂ, Ψ (w + 1) = F (Ψ w))
    (hΨ_small : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ w : ℂ, w.re < -R → Ψ w ≠ z₀ ∧ ‖Ψ w - z₀‖ < ε) :
    ‖deriv F z₀‖ = 1 := by
  set lam := deriv F z₀
  refine le_antisymm ?_ ?_
  · -- the fixed point is not repelling
    by_contra hcon
    have hgt : 1 < ‖lam‖ := not_le.mp hcon
    set c : ℝ := (1 + ‖lam‖) / 2 with hcdef
    have hc1 : c < ‖lam‖ := by rw [hcdef]; linarith
    have hc0 : 0 < c := by rw [hcdef]; linarith
    obtain ⟨δ, hδpos, hδ⟩ := exists_expansion_radius hfix hF hc1
    obtain ⟨y, hyPa, hyne, hylt⟩ := hPa_acc δ hδpos
    have hne : ∀ n : ℕ, F^[n] y ≠ z₀ :=
      fun n hn => hPa_not (hn ▸ hPa_maps.iterate n hyPa)
    have hpos : ∀ n : ℕ, 0 < ‖F^[n] y - z₀‖ :=
      fun n => norm_pos_iff.mpr (sub_ne_zero.mpr (hne n))
    have hconv : Tendsto (fun n : ℕ => ‖F^[n] y - z₀‖) atTop (nhds 0) := by
      have h1 : Tendsto (fun n : ℕ => F^[n] y - z₀) atTop (nhds (z₀ - z₀)) :=
        (hPa_tend y hyPa).sub tendsto_const_nhds
      simpa using h1.norm
    obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, ‖F^[n] y - z₀‖ < δ := by
      have h := hconv.eventually (Metric.ball_mem_nhds (0 : ℝ) hδpos)
      rw [eventually_atTop] at h
      obtain ⟨N, hN⟩ := h
      refine ⟨N, fun n hn => ?_⟩
      have := hN n hn
      simpa [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (norm_nonneg _)] using this
    have hgrow : ∀ n ≥ N, ‖F^[n] y - z₀‖ ≤ ‖F^[n+1] y - z₀‖ := by
      intro n hn
      have h1 : c * ‖F^[n] y - z₀‖ ≤ ‖F (z₀ + (F^[n] y - z₀)) - z₀‖ :=
        hδ _ (le_of_lt (hN n hn))
      have h2 : F (z₀ + (F^[n] y - z₀)) = F^[n+1] y := by
        have h3 : z₀ + (F^[n] y - z₀) = F^[n] y := by ring
        rw [h3, Function.iterate_succ_apply']
      rw [h2] at h1
      nlinarith [h1, hpos n, hc0]
    have hmono : ∀ k : ℕ, ‖F^[N] y - z₀‖ ≤ ‖F^[N+k] y - z₀‖ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        refine le_trans ih ?_
        rw [Nat.add_succ]
        exact hgrow (N + k) (Nat.le_add_right N k)
    have hle : ∀ m ≥ N, ‖F^[N] y - z₀‖ ≤ ‖F^[m] y - z₀‖ := by
      intro m hm
      obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
      exact hmono k
    have ha_pos : 0 < ‖F^[N] y - z₀‖ := hpos N
    obtain ⟨m, hmN, hm⟩ : ∃ m ≥ N, ‖F^[m] y - z₀‖ < ‖F^[N] y - z₀‖ := by
      have h := hconv.eventually (Iio_mem_nhds ha_pos)
      rw [eventually_atTop] at h
      obtain ⟨M, hM⟩ := h
      exact ⟨max M N, le_max_right _ _, hM _ (le_max_left _ _)⟩
    linarith [hle m hmN, hm]
  · -- the fixed point is not attracting
    by_contra hcon
    have hlt : ‖lam‖ < 1 := not_le.mp hcon
    set c : ℝ := (1 + ‖lam‖) / 2 with hcdef
    have hc_l : ‖lam‖ < c := by rw [hcdef]; linarith
    have hc_lt1 : c < 1 := by rw [hcdef]; linarith
    have hc_pos : 0 < c := by rw [hcdef]; linarith [norm_nonneg lam]
    obtain ⟨δ, hδpos, hδ⟩ := exists_contraction_radius hfix hF hc_l
    obtain ⟨R₀, hR₀⟩ := hΨ_small δ hδpos
    set w : ℂ := ⟨-R₀ - 1, 0⟩ with hwdef
    have hwre : w.re = -R₀ - 1 := rfl
    have hwlt : w.re < -R₀ := by rw [hwre]; linarith
    have hwne : Ψ w ≠ z₀ := (hR₀ w hwlt).1
    have hwsmall : ‖Ψ w - z₀‖ < δ := (hR₀ w hwlt).2
    have hposw : 0 < ‖Ψ w - z₀‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwne)
    have hsm : ∀ j : ℕ, ‖Ψ (w - (j:ℂ)) - z₀‖ < δ := by
      intro j
      have hre : (w - (j:ℂ)).re < -R₀ := by
        have h1 : (w - (j:ℂ)).re = (-R₀ - 1) - (j : ℝ) := by
          simp [Complex.sub_re, hwre]
        rw [h1]
        push_cast
        linarith
      exact (hR₀ _ hre).2
    have hstep : ∀ j : ℕ,
        ‖Ψ (w - (j:ℂ)) - z₀‖ ≤ c * ‖Ψ (w - ((j+1:ℕ):ℂ)) - z₀‖ := by
      intro j
      have hF : Ψ (w - (j:ℂ)) = F (Ψ (w - ((j+1:ℕ):ℂ))) := by
        have hs : w - ((j+1:ℕ):ℂ) + 1 = w - (j:ℂ) := by push_cast; ring
        rw [← hs]
        exact hΨ_shift _
      have hbnd : ‖Ψ (w - ((j+1:ℕ):ℂ)) - z₀‖ ≤ δ := le_of_lt (hsm (j+1))
      have h2 : ‖F (z₀ + (Ψ (w - ((j+1:ℕ):ℂ)) - z₀)) - z₀‖
          ≤ c * ‖Ψ (w - ((j+1:ℕ):ℂ)) - z₀‖ := hδ _ hbnd
      have h3 : z₀ + (Ψ (w - ((j+1:ℕ):ℂ)) - z₀) = Ψ (w - ((j+1:ℕ):ℂ)) := by ring
      rw [h3, ← hF] at h2
      exact h2
    have hiter : ∀ k : ℕ, ‖Ψ w - z₀‖ ≤ c^k * ‖Ψ (w - (k:ℂ)) - z₀‖ := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc ‖Ψ w - z₀‖
            ≤ c^k * ‖Ψ (w - (k:ℂ)) - z₀‖ := ih
          _ ≤ c^k * (c * ‖Ψ (w - ((k+1:ℕ):ℂ)) - z₀‖) :=
              mul_le_mul_of_nonneg_left (hstep k) (pow_nonneg hc_pos.le k)
          _ = c^(k+1) * ‖Ψ (w - ((k+1:ℕ):ℂ)) - z₀‖ := by ring
    have hbound : ∀ k : ℕ, ‖Ψ w - z₀‖ ≤ c^k * δ := by
      intro k
      refine le_trans (hiter k) ?_
      exact mul_le_mul_of_nonneg_left (le_of_lt (hsm k)) (pow_nonneg hc_pos.le k)
    have hzero : Tendsto (fun k : ℕ => c^k * δ) atTop (nhds 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hc_pos.le hc_lt1).mul_const δ
    obtain ⟨k, hk⟩ : ∃ k : ℕ, c^k * δ < ‖Ψ w - z₀‖ := by
      have h := hzero.eventually (Iio_mem_nhds hposw)
      rw [eventually_atTop] at h
      obtain ⟨K, hK⟩ := h
      exact ⟨K, hK K le_rfl⟩
    linarith [hbound k, hk]

/-! ## 5. The multiplier of the transported parabolic point -/

/-- Iterates of `F` are transported. -/
theorem theta_iterate_F {c c₂ : ℂ} (θ : ℂ ≃ₜ ℂ)
    (hFc : ∀ z : ℂ, θ (F c z) = F c₂ (θ z)) (n : ℕ) (z : ℂ) :
    θ ((F c)^[n] z) = (F c₂)^[n] (θ z) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Function.iterate_succ_apply', hFc, ih]

/-- The conjugacy for `T` gives a conjugacy for the holomorphic tenth iterate `F`. -/
theorem conj_F {c c₂ : ℂ} (θ : ℂ ≃ₜ ℂ)
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z)) :
    ∀ z : ℂ, θ (F c z) = F c₂ (θ z) := by
  intro z
  rw [elF_eq_iterate_local, elF_eq_iterate_local]
  exact theta_iterate θ hconj 10 z

/-- **The multiplier of the transported parabolic point is `1`.** -/
theorem multiplier_transfer {c : ℂ} (d : Work.EL.RootParabolic c) {c₂ : ℂ} (θ : ℂ ≃ₜ ℂ)
    (hconj : ∀ z : ℂ, θ (Tantibar c z) = Tantibar c₂ (θ z))
    (hdecay : ∃ C R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖θ z - z‖ ≤ C / ‖z‖) :
    Work.Landing.multiplier2 c₂ 5 (θ d.z₁) = 1 := by
  have hFc := conj_F θ hconj
  have hTsq : Differentiable ℂ (Work.Landing.Tsq c) := by
    show Differentiable ℂ (fun z : ℂ => (z ^ 2 + star c) ^ 2 + c); fun_prop
  have hTsq₂ : Differentiable ℂ (Work.Landing.Tsq c₂) := by
    show Differentiable ℂ (fun z : ℂ => (z ^ 2 + star c₂) ^ 2 + c₂); fun_prop
  set g : ℂ → ℂ := (Tantibar c)^[5] with hg
  have hgdiff : ∀ z : ℂ, DifferentiableAt ℂ (fun z => star (g z)) z := by
    have hstar_g : ∀ z : ℂ, star (g z) = ((Tantibar c)^[4] z)^2 + star c := by
      intro z
      rw [hg]
      rw [show (Tantibar c)^[5] z = Tantibar c ((Tantibar c)^[4] z) from by
        rw [show (5:ℕ) = 4 + 1 by norm_num, Function.iterate_succ_apply']]
      simp [Tantibar]
    have hf4 : Differentiable ℂ ((Tantibar c)^[4]) := by
      rw [show (4:ℕ) = 2 * 2 by norm_num, Function.iterate_mul, ← tsq_eq_iterate_local]
      exact hTsq.iterate 2
    intro z
    rw [show (fun z => star (g z)) = fun z => ((Tantibar c)^[4] z)^2 + star c from
      funext hstar_g]
    exact ((hf4.differentiableAt).pow 2).add_const (star c)
  have hgg : g ∘ g = F c := by
    rw [hg, ← Function.iterate_add, show (5:ℕ) + 5 = 10 by norm_num, elF_eq_iterate_local]
  have hfix : F c d.z₁ = d.z₁ := by
    rw [elF_eq_iterate_local, show (10:ℕ) = 5 + 5 by norm_num, Function.iterate_add_apply,
      d.per_half, d.per_half]
  have h1 : deriv (F c) d.z₁ = 1 := d.mult
  obtain ⟨fl⟩ := Work.FatouCoord.Flower.exists_parabolicFlower (F c) g d.z₁
    (show Differentiable ℂ ((Work.Landing.Tsq c)^[5]) from hTsq.iterate 5)
    hgdiff hgg hfix h1 d.simple d.per_half
  have hper : (Tantibar c₂)^[5] (θ d.z₁) = θ d.z₁ := by
    rw [← theta_iterate θ hconj 5 d.z₁, d.per_half]
  have hper' : F c₂ (θ d.z₁) = θ d.z₁ := by
    rw [elF_eq_iterate_local, show (10:ℕ) = 5 + 5 by norm_num, Function.iterate_add_apply,
      hper, hper]
  have hnot : θ d.z₁ ∉ (θ '' fl.Pa) := by
    rintro ⟨y, hy, hyx⟩
    exact fl.z₀_not_mem (by rwa [θ.injective hyx] at hy)
  have hmaps : MapsTo (F c₂) (θ '' fl.Pa) (θ '' fl.Pa) := by
    rintro y ⟨y₀, hy₀, rfl⟩
    exact ⟨F c y₀, fl.mapsTo_Pa hy₀, hFc y₀⟩
  have htend : ∀ y ∈ (θ '' fl.Pa),
      Tendsto (fun n : ℕ => (F c₂)^[n] y) atTop (nhds (θ d.z₁)) := by
    rintro y ⟨y₀, hy₀, rfl⟩
    have h3 := (θ.continuous.tendsto d.z₁).comp (fl.tendsto_Pa y₀ hy₀)
    have h4 : ∀ n : ℕ, θ ((F c)^[n] y₀) = (F c₂)^[n] (θ y₀) :=
      fun n => theta_iterate_F θ hFc n y₀
    rw [← show (fun n : ℕ => θ ((F c)^[n] y₀)) = fun n => (F c₂)^[n] (θ y₀) from funext h4]
    exact h3
  have hacc : ∀ ε : ℝ, 0 < ε →
      ∃ y ∈ (θ '' fl.Pa), 0 < ‖y - θ d.z₁‖ ∧ ‖y - θ d.z₁‖ < ε := by
    intro ε hε
    obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.continuousAt_iff.mp θ.continuous.continuousAt ε hε
    obtain ⟨R₁, hR₁⟩ := fl.Ψ_small ε₁ hε₁pos
    obtain ⟨R₂, hR₂⟩ := fl.Ψ_ends
    set R : ℝ := max R₂ R₁ + 1 with hRdef
    set w : ℂ := ⟨-R, max R₂ 0 + 1⟩ with hwdef
    have hwre : w.re = -R := rfl
    have hwim : w.im = max R₂ 0 + 1 := rfl
    have h1 : w.re < -R₁ := by
      rw [hwre, hRdef]; linarith [le_max_right R₂ R₁]
    have h2 : R₂ < |w.im| := by
      rw [hwim, abs_of_pos (by linarith [le_max_right R₂ 0])]
      linarith [le_max_left R₂ 0]
    have h3 : w.re < -R₂ := by
      rw [hwre, hRdef]; linarith [le_max_left R₂ R₁]
    refine ⟨θ (fl.Ψ w), ⟨fl.Ψ w, hR₂ w h3 h2, rfl⟩, ?_, ?_⟩
    · refine norm_pos_iff.mpr ?_
      rw [sub_ne_zero]
      intro hcon
      exact (hR₁ w h1).1 (θ.injective hcon)
    · have h4 : dist (θ (fl.Ψ w)) (θ d.z₁) < ε :=
        hε₁ (x := fl.Ψ w) (by simpa [dist_eq_norm] using (hR₁ w h1).2)
      simpa [dist_eq_norm] using h4
  have hshift : ∀ w : ℂ,
      (fun w : ℂ => θ (fl.Ψ w)) (w + 1) = F c₂ ((fun w : ℂ => θ (fl.Ψ w)) w) := by
    intro w
    show θ (fl.Ψ (w + 1)) = F c₂ (θ (fl.Ψ w))
    rw [fl.Ψ_shift, hFc]
  have hsmall : ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ w : ℂ, w.re < -R →
      (fun w : ℂ => θ (fl.Ψ w)) w ≠ θ d.z₁ ∧ ‖(fun w : ℂ => θ (fl.Ψ w)) w - θ d.z₁‖ < ε := by
    intro ε hε
    obtain ⟨ε₁, hε₁pos, hε₁⟩ := Metric.continuousAt_iff.mp θ.continuous.continuousAt ε hε
    obtain ⟨R₁, hR₁⟩ := fl.Ψ_small ε₁ hε₁pos
    refine ⟨R₁, fun w hw => ⟨?_, ?_⟩⟩
    · intro hcon
      exact (hR₁ w hw).1 (θ.injective hcon)
    · have h4 : dist (θ (fl.Ψ w)) (θ d.z₁) < ε :=
        hε₁ (x := fl.Ψ w) (by simpa [dist_eq_norm] using (hR₁ w hw).2)
      simpa [dist_eq_norm] using h4
  have hderiv : ‖deriv (F c₂) (θ d.z₁)‖ = 1 :=
    norm_deriv_eq_one_of_flower_data hper' (hTsq₂.iterate 5).differentiableAt
      hnot hmaps htend hacc hshift hsmall
  obtain ⟨r, hr0, hr⟩ := Work.Landing.Family.deriv_tsq_iterate_odd_real c₂
    (by norm_num : Odd 5) hper
  have hr1 : r = 1 := by
    have h2 : ‖((r : ℝ) : ℂ)‖ = 1 := by
      rw [← hr]
      exact hderiv
    rw [Complex.norm_real, Real.norm_of_nonneg hr0] at h2
    exact h2
  show deriv ((Work.Landing.Tsq c₂)^[5]) (θ d.z₁) = 1
  rw [hr, hr1]
  norm_num


end Work.FQC
