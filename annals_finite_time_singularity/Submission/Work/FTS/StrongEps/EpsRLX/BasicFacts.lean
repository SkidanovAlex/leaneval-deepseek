/-
Copyright: work module for the Elgindi finite-time singularity project.

# `EpsRLX/BasicFacts.lean` — two elementary tools for the `EpsRHSPLipXProof` assembly

* `DiffTraces`: the angular traces of `Δ = profRHS α Φs E W₁ − profRHS α Φs E W₂` vanish at both
  endpoints.  This is the two-line glue `ProfRHSTraces W₁` ⊖ `ProfRHSTraces W₂` along
  `Filter.Tendsto.sub`; it is the hypothesis `TraceToEpsMem` needs at the *difference* profile.

* `EpsSq_Pz_le`: the single-function energy bound for the projection `P₀`,
  `EpsMem α (Pz f) ∧ EpsSq α (Pz f) ≤ C · EpsSq α f` for `SmoothOpen f`, `HkMem α 4 f`,
  `EpsMem α f`.  It is the `g = 0` companion of the pair bound `EpsSq_Pz_sub_le`, obtained from
  the pointwise form `Pz f = f − c·bump` (`Pz_apply`), the corrected bump bound
  `EpsSq_sub_smul_bump_of_smoothOpen` and the zero-mode estimate `L12_le_sqrt_EpsSq`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsRLX.Defs
import Submission.Work.FTS.StrongEps.EpsRLX.ProfileFacts
import Submission.Work.FTS.StrongEps.EpsRLX.ProfRHSTraces
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_sub_smul_bump_res
import Submission.Work.FTS.StrongEps.EpsSqTools.L12_sub_EpsSq_le
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_Pz_sub_le
import Submission.Work.FTS.StrongEps.EpsLocalPStar.EpsRHSXrhs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## The angular traces of the difference of the right-hand side -/

/-- **The angular traces of `Δ = profRHS α Φs E W₁ − profRHS α Φs E W₂` vanish** at both
endpoints, for every `z > 0`.  This is what feeds `TraceToEpsMem` at the difference profile. -/
theorem DiffTraces {α Ce Cs : ℝ} (hα : α ∈ Set.Ioc 0 1) {Φs W₁ W₂ : Fn} {E : Fn → Fn}
    (hW₁ : Work.FTS.ClassC.ClassC α W₁) (hW₂ : Work.FTS.ClassC.ClassC α W₂)
    (hell₁ : Work.FTS.VocabO.EllPkgGo α Ce W₁ (E W₁))
    (hell₂ : Work.FTS.VocabO.EllPkgGo α Ce W₂ (E W₂))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    (∀ z : ℝ, 0 < z → Filter.Tendsto
        (fun θ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₁ z θ
          - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₂ z θ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) ∧
    (∀ z : ℝ, 0 < z → Filter.Tendsto
        (fun θ => Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₁ z θ
          - Work.FTS.StrongEps.EpsLocalPStar.profRHS α Φs E W₂ z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) := by
  obtain ⟨h1₁, h2₁⟩ := ProfRHSTraces hα hW₁ hell₁ hstar
  obtain ⟨h1₂, h2₂⟩ := ProfRHSTraces hα hW₂ hell₂ hstar
  exact ⟨fun z hz => by simpa using (h1₁ z hz).sub (h1₂ z hz),
    fun z hz => by simpa using (h2₁ z hz).sub (h2₂ z hz)⟩

/-! ## The single-function energy bound for the projection -/

/-- **The projection `P₀` preserves the weighted space `X` and its energy**, up to the fixed
constant `2 + B·C₁²/pzNorm²`: `EpsMem α (Pz f)` and `EpsSq α (Pz f) ≤ C · EpsSq α f` for
`SmoothOpen f`, `HkMem α 4 f` and `EpsMem α f`. -/
theorem EpsSq_Pz_le : ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ f : Fn,
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.StrongEps.EpsMem α f →
      Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.Pz f) ∧
      Work.FTS.StrongEps.EpsSq α (Work.FTS.StrongEps.Pz f)
        ≤ C * Work.FTS.StrongEps.EpsSq α f := by
  obtain ⟨B, hBpos, hB⟩ := Work.FTS.StrongEps.EpsSqTools.EpsSq_sub_smul_bump_of_smoothOpen
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongEps.EpsSqTools.L12_le_sqrt_EpsSq
  have hpz : 0 < Work.FTS.StrongEps.pzNorm := Work.FTS.StrongEps.PZeroAux.pzNorm_pos
  refine ⟨2 + B * C₁ ^ 2 / Work.FTS.StrongEps.pzNorm ^ 2, ?_, ?_⟩
  · have h1 : 0 ≤ B * C₁ ^ 2 / Work.FTS.StrongEps.pzNorm ^ 2 :=
      div_nonneg (mul_nonneg hBpos.le (sq_nonneg _)) (sq_nonneg _)
    linarith
  intro α hα f hsm hm hmem
  set c : ℝ := Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm with hcdef
  have hpt : ∀ z θ : ℝ, Work.FTS.StrongEps.Pz f z θ = f z θ - c * Work.FTS.StrongEps.bump z θ := by
    intro z θ
    rw [Work.FTS.StrongEps.Pz_apply, hcdef]
  obtain ⟨hmem', hbd'⟩ := hB α hα f c hsm hmem
  have hcsq : c ^ 2 ≤ C₁ ^ 2 / Work.FTS.StrongEps.pzNorm ^ 2
      * Work.FTS.StrongEps.EpsSq α f := by
    have hL := hC₁ α hα f hmem 0 (Set.mem_Ici.mpr le_rfl)
    have hS : 0 ≤ Work.FTS.StrongEps.EpsSq α f := Work.FTS.StrongEps.EpsSq_nonneg α f
    rw [hcdef]
    have h2 : (Work.Construction.L12 f 0) ^ 2 ≤ C₁ ^ 2 * Work.FTS.StrongEps.EpsSq α f := by
      have h3 : (Work.Construction.L12 f 0) ^ 2
          ≤ (C₁ * Real.sqrt (Work.FTS.StrongEps.EpsSq α f)) ^ 2 := by
        simpa only [sq_abs] using
          pow_le_pow_left₀ (abs_nonneg (Work.Construction.L12 f 0)) hL 2
      rwa [mul_pow, Real.sq_sqrt hS] at h3
    calc (Work.Construction.L12 f 0 / Work.FTS.StrongEps.pzNorm) ^ 2
        = (Work.Construction.L12 f 0) ^ 2 / Work.FTS.StrongEps.pzNorm ^ 2 := by rw [div_pow]
      _ ≤ (C₁ ^ 2 * Work.FTS.StrongEps.EpsSq α f) / Work.FTS.StrongEps.pzNorm ^ 2 :=
          div_le_div_of_nonneg_right h2 (pow_pos hpz 2).le
      _ = C₁ ^ 2 / Work.FTS.StrongEps.pzNorm ^ 2 * Work.FTS.StrongEps.EpsSq α f := by ring
  refine ⟨Work.FTS.StrongEps.EpsSqTools.EpsMem_congr (fun z θ => (hpt z θ).symm) hmem', ?_⟩
  rw [Work.FTS.StrongEps.EpsSq_congr (fun z θ => hpt z θ)]
  calc Work.FTS.StrongEps.EpsSq α (fun z θ => f z θ - c * Work.FTS.StrongEps.bump z θ)
      ≤ 2 * Work.FTS.StrongEps.EpsSq α f + B * c ^ 2 := hbd'
    _ ≤ 2 * Work.FTS.StrongEps.EpsSq α f
        + B * (C₁ ^ 2 / Work.FTS.StrongEps.pzNorm ^ 2 * Work.FTS.StrongEps.EpsSq α f) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_left hcsq hBpos.le)
    _ = (2 + B * C₁ ^ 2 / Work.FTS.StrongEps.pzNorm ^ 2) * Work.FTS.StrongEps.EpsSq α f := by ring

/-! ## The `ℋ⁶`-size of the projected-mollified profile, and monotonicity in `B` -/

/-- **`ProfileData` is monotone in the size parameter `B`.** -/
theorem ProfileData.mono_B {α C₀ B B' ε : ℝ} {ρ : ℝ × ℝ → ℝ} {u : Fn}
    (h : ProfileData α C₀ B ε ρ u) (hB : B ≤ B') : ProfileData α C₀ B' ε ρ u :=
  ⟨h.smo, h.hkmem, le_trans h.hknorm hB, h.cls, h.xn⟩

/-- **The `ℋ⁶`-size of `W_u = Pz (J_ε u)` is proportional to `B`**, with the loss
`(γ−1)^{-1}(C/ε)⁶`: `|W_u|_{ℋ⁶} ≤ C/(γ−1)·(C/ε)⁶·B` for `ProfileData α C₀ B ε ρ u`.  This is the
`ℋ⁶`-companion of `WpUniformBound` and is what allows `XDataClean`/`ProfRHSEpsData` (whose size
hypothesis is stated at the *profile*) to be applied at `W_u`, where only the datum's `ℋ⁶`-bound
`|u|_{ℋ⁶} ≤ B` is available. -/
theorem WpSixBound {ρ : ℝ × ℝ → ℝ} (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ ε ∈ Set.Ioc 0 1, ∀ {C₀ B : ℝ}, 0 ≤ B →
      ∀ {u : Fn}, ProfileData α C₀ B ε ρ u →
      Work.Spaces.HkNorm α 6 (Wp ρ ε u)
        ≤ C / (Work.Spaces.gam α - 1) * (C / ε) ^ 6 * B := by
  obtain ⟨CF, hCFpos, hPF⟩ := ProfileFacts ρ hρ
  refine ⟨max 1 CF, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro α hα ε hε C₀ B hB u hd
  have hγpos : 0 < Work.Spaces.gam α - 1 := by
    have := Work.Spaces.one_lt_gam hα.1
    linarith
  set C : ℝ := max 1 CF with hCdef
  have hC1 : (1 : ℝ) ≤ C := by rw [hCdef]; exact le_max_left _ _
  have hCFle : CF ≤ C := by rw [hCdef]; exact le_max_right _ _
  have hCF0 : 0 ≤ CF := hCFpos.le
  have hε0 : 0 ≤ ε := hε.1.le
  have hCe0 : 0 ≤ C / ε := div_nonneg (le_trans zero_le_one hC1) hε0
  obtain ⟨-, hsq_u, h6, -, -, -, hm7, -⟩ := hPF α hα ε hε hd
  have h1 : Work.Spaces.HkSq α 1 u ≤ B ^ 2 := by
    have h := Work.FTS.CoercivityStep.Norm.HkSq_mono_le α (by norm_num : 1 ≤ 6) hd.hkmem
    rw [show Work.Spaces.HkSq α 6 u = (Work.Spaces.HkNorm α 6 u) ^ 2 from by
      rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 6 u)]] at h
    exact le_trans h (pow_le_pow_left₀ (Work.Spaces.HkNorm_nonneg α 6 u) hd.hknorm 2)
  have hEps : Work.FTS.StrongEps.EpsSq α u
      ≤ C / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2 := by
    have hcoef : CF / (Work.Spaces.gam α - 1) ^ 2 ≤ C / (Work.Spaces.gam α - 1) ^ 2 :=
      div_le_div_of_nonneg_right hCFle (pow_pos hγpos 2).le
    calc Work.FTS.StrongEps.EpsSq α u
        ≤ CF / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 1 u := hsq_u
      _ ≤ CF / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2 :=
          mul_le_mul_of_nonneg_left h1 (div_nonneg hCF0 (pow_pos hγpos 2).le)
      _ ≤ C / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2 :=
          mul_le_mul_of_nonneg_right hcoef (sq_nonneg B)
  have h6' : Work.Spaces.HkSq α 6 (Wp ρ ε u)
      ≤ C * (C / ε) ^ 12 * (C / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2) := by
    have hbase : CF / ε ≤ C / ε := div_le_div_of_nonneg_right hCFle hε0
    have hp : (CF / ε) ^ 12 ≤ (C / ε) ^ 12 :=
      pow_le_pow_left₀ (div_nonneg hCF0 hε0) hbase 12
    have hCC : CF * (CF / ε) ^ 12 ≤ C * (C / ε) ^ 12 :=
      mul_le_mul hCFle hp (pow_nonneg (div_nonneg hCF0 hε0) 12) (le_trans zero_le_one hC1)
    calc Work.Spaces.HkSq α 6 (Wp ρ ε u)
        ≤ CF * (CF / ε) ^ 12 * Work.FTS.StrongEps.EpsSq α u := h6
      _ ≤ CF * (CF / ε) ^ 12 * (C / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2) :=
          mul_le_mul_of_nonneg_left hEps
            (mul_nonneg hCF0 (pow_nonneg (div_nonneg hCF0 hε0) 12))
      _ ≤ C * (C / ε) ^ 12 * (C / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2) :=
          mul_le_mul_of_nonneg_right hCC
            (mul_nonneg (div_nonneg (le_trans zero_le_one hC1) (pow_pos hγpos 2).le) (sq_nonneg B))
  have hY2 : (C / (Work.Spaces.gam α - 1) * (C / ε) ^ 6 * B) ^ 2
      = C * (C / ε) ^ 12 * (C / (Work.Spaces.gam α - 1) ^ 2 * B ^ 2) := by
    rw [show C / (Work.Spaces.gam α - 1) * (C / ε) ^ 6 * B
        = C / (Work.Spaces.gam α - 1) * ((C / ε) ^ 6 * B) from by ring]
    rw [mul_pow, div_pow, mul_pow, ← pow_mul (C / ε) 6 2]
    ring
  have hfin : C / (Work.Spaces.gam α - 1) * (C / ε) ^ 6 * B
      = max 1 CF / (Work.Spaces.gam α - 1) * (max 1 CF / ε) ^ 6 * B := by rw [hCdef]
  rw [← hfin]
  calc Work.Spaces.HkNorm α 6 (Wp ρ ε u)
      = Real.sqrt (Work.Spaces.HkSq α 6 (Wp ρ ε u)) := rfl
    _ ≤ Real.sqrt ((C / (Work.Spaces.gam α - 1) * (C / ε) ^ 6 * B) ^ 2) :=
        Real.sqrt_le_sqrt (by rw [hY2]; exact h6')
    _ = C / (Work.Spaces.gam α - 1) * (C / ε) ^ 6 * B := Real.sqrt_sq (by positivity)

end Work.FTS.StrongEps.EpsRLX
