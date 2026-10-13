/-
# `Work.FTS_StreamBdry.Inputs.SliceTr` — mechanical transport lemmas for the slice adapter

This module collects the *mechanical* facts that the three leaves
`ftau_Dz_le` (`Inputs/ftau_Dz_le.lean`), `ftau_cont` (`Inputs/ftau_cont.lean`) and
`ftau_Dz_cont` (`Inputs/ftau_Dz_cont.lean`) — and the assembly `slice_inputs_of_slot` — need
in order to build the `SrcOK` data of the adapter from the package `RegPkg' a S A B (extG G)`
and the agreement hypothesis `G = g` on the closed strip.

Everything is stated for the family that the adapter actually uses:
`F (τ) = Ftau (pExp a) g τ = F_* + slice g τ`.  The package `RegPkg'` describes the *extended*
family `extG G`, which agrees with `slice g τ` on the closed strip `z > 0`, `θ ∈ Iθ`,
`τ ≥ 0` (`Ftau_eq_profFull`); every RegPkg-field is transported through that identity, at the
horizon `S = τ + 1` (per `τ`, since the constants of `RegPkg'` may depend on the horizon).

Contents:

* `Ftau_eq_profFull` — the transport identity;
* the elementary profile bounds `FM_Fstar_abs_le_half`, `Fstar_abs_le_Gamma`,
  `Dz_Fstar_abs_le_Gamma`, and the endpoint values `Fstar_apply_zero`,
  `Fstar_apply_pi_div_two`;
* the continuity of `Γ` and its vanishing at the two ends (`continuous_Gamma`,
  `Gamma_apply_zero`, `Gamma_apply_pi_div_two`);
* the transported slice data at a fixed `τ ≥ 0`: `slice_abs_le_Gamma`, `ftau_abs_le_Gamma`,
  `ftau_vanish`, `ftau_supp`, `slice_pz_le`, `slice_pz_endpoint_le`;
* the two Curry/Fréchet tools `continuousOn_uncurry_pz_of` and `pz_add_of` used to identify
  and control `pz` of a sum on an open set.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.Construction.Basic
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.Spaces.CurrySmooth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open Set Filter

namespace Work.FTS_StreamBdry.Inputs

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## §1 The transport identity -/

/-- On the closed angular strip, for `z > 0` and `τ ≥ 0`, the slice `F_* + slice g τ` is the full
profile of the *extended* family `extG G` — the object the package `RegPkg'` describes. -/
theorem Ftau_eq_profFull {a : ℝ} {g G : Fam} {τ : ℝ} (hτ : 0 ≤ τ)
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ z θ
      = Work.FTS.Regularity.profFull a (Work.FTS.RegPkgGal.extG G) z θ τ := by
  have h1 : Work.FTS.RegPkgGal.extG G z θ τ = g z θ τ := by
    rw [Work.FTS.RegPkgGal.extG_of_pos (g := G) hz hτ, hG z θ τ hz hθ hτ]
  simp only [Work.Construction.Ftau, Work.FTS.Regularity.profFull, h1]

/-! ## §2 Elementary facts about `F_*` and `Γ` -/

/-- `|F_*(z)| ≤ 1/2`, with `F_*(z) = 2z/(1+z)²` (attained at `z = 1`). -/
theorem FM_Fstar_abs_le_half {z : ℝ} (hz : 0 ≤ z) : |Work.FM.Fstar z| ≤ 1 / 2 := by
  have hden : (0 : ℝ) < (1 + z) ^ 2 := by positivity
  have hzabs : |z| = z := abs_of_nonneg hz
  rw [Work.FM.Fstar, abs_div, abs_mul, abs_of_pos hden, abs_of_pos (by norm_num : (0:ℝ) < 2),
    hzabs, div_le_iff₀ hden]
  nlinarith [sq_nonneg (1 - z)]

/-- `Γ(θ) = Gam (pExp a) θ` is nonnegative on the closed strip. -/
theorem Gam_nonneg_of_Iθ {a θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ := by
  rw [← Work.FTS.Regularity.Gamma_eq_Gam a θ]
  exact Work.ConstructionInstance.Gamma_nonneg hθ

/-- `Γ(θ) = Gam (pExp a) θ` is at most `1` on the closed strip. -/
theorem Gam_le_one_of_Iθ {a θ : ℝ} (ha : 0 < a) (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ ≤ 1 := by
  rw [← Work.FTS.Regularity.Gamma_eq_Gam a θ]
  exact Work.ConstructionInstance.Gamma_le_one (le_of_lt ha) hθ

/-- **The `Γ`-decay of `F_*`**: `|F_*| ≤ 5 pExp a · Γ(θ)` on the closed strip (the `Γ`-factor
comes from the profile's angular factor `Γ/c`, with `c ≥ 1/10`). -/
theorem Fstar_abs_le_Gamma {a : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3) {z θ : ℝ} (hz : 0 ≤ z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar (Work.FTS.Regularity.pExp a) z θ|
      ≤ 5 * Work.FTS.Regularity.pExp a * Work.FTS.Regularity.Gamma a θ := by
  have hpa : 0 < Work.FTS.Regularity.pExp a := Work.FTS.Regularity.pExp_pos ha
  have hc := Work.Spaces.c_bounds (Work.FTS.Regularity.pExp a) hpa
    (Work.FTS.Regularity.pExp_le_one ha13)
  have hc0 : 0 < Work.Spaces.c (Work.FTS.Regularity.pExp a) := by linarith [hc.1]
  have hGam0 : 0 ≤ Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ := Gam_nonneg_of_Iθ hθ
  have hFM := FM_Fstar_abs_le_half hz
  have key : |Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ
        / Work.Spaces.c (Work.FTS.Regularity.pExp a)|
      ≤ 10 * Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ := by
    rw [abs_of_nonneg (div_nonneg hGam0 (le_of_lt hc0)), div_le_iff₀ hc0]
    nlinarith [hc.1]
  have hkey : |Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ
        / Work.Spaces.c (Work.FTS.Regularity.pExp a)| * |Work.FM.Fstar z|
      ≤ (10 * Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ) * (1 / 2) :=
    mul_le_mul key hFM (abs_nonneg _) (by linarith)
  rw [Work.Construction.Fstar, abs_mul, abs_mul, abs_of_pos hpa]
  calc Work.FTS.Regularity.pExp a * |Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ
          / Work.Spaces.c (Work.FTS.Regularity.pExp a)| * |Work.FM.Fstar z|
      = Work.FTS.Regularity.pExp a
          * (|Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp a)| * |Work.FM.Fstar z|) := by ring
    _ ≤ Work.FTS.Regularity.pExp a
          * ((10 * Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ) * (1 / 2)) :=
        mul_le_mul_of_nonneg_left hkey (le_of_lt hpa)
    _ = 5 * Work.FTS.Regularity.pExp a * Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ := by ring
    _ = 5 * Work.FTS.Regularity.pExp a * Work.FTS.Regularity.Gamma a θ := by
        rw [Work.FTS.Regularity.Gamma_eq_Gam]

/-- **The `Γ`-decay of `D_zF_*`**: `|D_zF_*| ≤ 20 pExp a · Γ(θ)` for `z > 0` on the closed strip. -/
theorem Dz_Fstar_abs_le_Gamma {a : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.Dz (Work.Construction.Fstar (Work.FTS.Regularity.pExp a)) z θ|
      ≤ 20 * Work.FTS.Regularity.pExp a * Work.FTS.Regularity.Gamma a θ := by
  have hpa : 0 < Work.FTS.Regularity.pExp a := Work.FTS.Regularity.pExp_pos ha
  have hc := Work.Spaces.c_bounds (Work.FTS.Regularity.pExp a) hpa
    (Work.FTS.Regularity.pExp_le_one ha13)
  have hc0 : 0 < Work.Spaces.c (Work.FTS.Regularity.pExp a) := by linarith [hc.1]
  have hGam0 : 0 ≤ Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ := Gam_nonneg_of_Iθ hθ
  have key : |Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ
        / Work.Spaces.c (Work.FTS.Regularity.pExp a)|
      ≤ 10 * Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ := by
    rw [abs_of_nonneg (div_nonneg hGam0 (le_of_lt hc0)), div_le_iff₀ hc0]
    nlinarith [hc.1]
  have hb : |2 * z * (1 - z) / (1 + z) ^ 3| ≤ 2 := by
    have hden : (0 : ℝ) < (1 + z) ^ 3 := by positivity
    rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
    rcases le_total z 1 with hz1 | hz1
    · have hnn : 0 ≤ 2 * z * (1 - z) := by nlinarith
      rw [abs_of_nonneg hnn]
      nlinarith [hz, hz1, sq_nonneg (1 + z), sq_nonneg z,
        pow_pos (by linarith : (0:ℝ) < 1 + z) 3]
    · have hnn : 0 ≤ 2 * z * (z - 1) := by nlinarith
      have heq : 2 * z * (1 - z) = -(2 * z * (z - 1)) := by ring
      rw [heq, abs_neg, abs_of_nonneg hnn]
      nlinarith [hz, hz1, sq_nonneg (1 + z)]
  have hkey : |Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ
        / Work.Spaces.c (Work.FTS.Regularity.pExp a)| * |2 * z * (1 - z) / (1 + z) ^ 3|
      ≤ (10 * Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ) * 2 :=
    mul_le_mul key hb (abs_nonneg _) (by linarith)
  have hz1' : (-1 : ℝ) < z := by linarith
  rw [Work.Construction.Dz_Fstar_eq hpa hz1', abs_mul, abs_mul, abs_of_pos hpa]
  calc Work.FTS.Regularity.pExp a * |Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ
          / Work.Spaces.c (Work.FTS.Regularity.pExp a)| * |2 * z * (1 - z) / (1 + z) ^ 3|
      = Work.FTS.Regularity.pExp a
          * (|Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ
              / Work.Spaces.c (Work.FTS.Regularity.pExp a)| * |2 * z * (1 - z) / (1 + z) ^ 3|) := by
        ring
    _ ≤ Work.FTS.Regularity.pExp a
          * ((10 * Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ) * 2) :=
        mul_le_mul_of_nonneg_left hkey (le_of_lt hpa)
    _ = 20 * Work.FTS.Regularity.pExp a * Work.Spaces.Gam (Work.FTS.Regularity.pExp a) θ := by ring
    _ = 20 * Work.FTS.Regularity.pExp a * Work.FTS.Regularity.Gamma a θ := by
        rw [Work.FTS.Regularity.Gamma_eq_Gam]

/-- `Γ` vanishes at `θ = 0`. -/
theorem Gamma_apply_zero {a : ℝ} (ha : a ≠ 0) :
    Work.FTS.Regularity.Gamma a 0 = 0 := by
  have h0 : (0 : ℝ) ^ a = 0 := Real.zero_rpow ha
  simp only [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma, Real.sin_zero,
    Real.cos_zero, mul_one, zero_mul, h0]

/-- `Γ` vanishes at `θ = π/2`. -/
theorem Gamma_apply_pi_div_two {a : ℝ} (ha : a ≠ 0) :
    Work.FTS.Regularity.Gamma a (π / 2) = 0 := by
  have h0 : (0 : ℝ) ^ a = 0 := Real.zero_rpow ha
  simp only [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma, Real.cos_pi_div_two,
    Real.sin_pi_div_two, one_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero, h0]

/-- `F_*` vanishes at `θ = 0`. -/
theorem Fstar_apply_zero {a z : ℝ} (ha : a ≠ 0) :
    Work.Construction.Fstar (Work.FTS.Regularity.pExp a) z 0 = 0 := by
  have hne : Work.FTS.Regularity.pExp a / 3 ≠ 0 := by
    rw [Work.FTS.Regularity.pExp]
    exact fun h => ha (by linarith [h])
  have h0 : Work.Spaces.Gam (Work.FTS.Regularity.pExp a) 0 = 0 := by
    have h := Real.zero_rpow hne
    simpa only [Work.Spaces.Gam, Real.sin_zero, Real.cos_zero, mul_one, zero_mul] using h
  simp only [Work.Construction.Fstar, h0, zero_div, zero_mul, mul_zero]

/-- `F_*` vanishes at `θ = π/2`. -/
theorem Fstar_apply_pi_div_two {a z : ℝ} (ha : a ≠ 0) :
    Work.Construction.Fstar (Work.FTS.Regularity.pExp a) z (π / 2) = 0 := by
  have hne : Work.FTS.Regularity.pExp a / 3 ≠ 0 := by
    rw [Work.FTS.Regularity.pExp]
    exact fun h => ha (by linarith [h])
  have h0 : Work.Spaces.Gam (Work.FTS.Regularity.pExp a) (π / 2) = 0 := by
    have h := Real.zero_rpow hne
    simpa only [Work.Spaces.Gam, Real.cos_pi_div_two, Real.sin_pi_div_two, one_mul,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] using h
  simp only [Work.Construction.Fstar, h0, zero_div, zero_mul, mul_zero]

/-- `Γ` is continuous (for a positive exponent, also at `0` and `π/2`). -/
theorem continuous_Gamma {a : ℝ} (ha : 0 < a) :
    Continuous (fun θ : ℝ => Work.FTS.Regularity.Gamma a θ) := by
  have hbase : Continuous (fun θ : ℝ => Real.sin θ * Real.cos θ ^ 2) :=
    Real.continuous_sin.mul (Real.continuous_cos.pow 2)
  have h := hbase.rpow_const (fun θ => Or.inr (le_of_lt ha))
  simpa only [Work.FTS.Regularity.Gamma, Work.ConstructionInstance.Gamma] using h

/-! ## §3 Transport of the `RegPkg'` data to the slice at a fixed `τ ≥ 0` -/

/-- **The `Γ`-decay of the perturbation** `|g| ≤ Cv·Γ(θ)` on the closed strip, transported from
`RegPkg'.hvan` (at the horizon `τ + 1`). -/
theorem slice_abs_le_Gamma {a τ : ℝ} (hτ : 0 ≤ τ) {g G : Fam} {A B : ℝ → ℝ}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |g z θ τ| ≤ Cv * Work.FTS.Regularity.Gamma a θ := by
  obtain ⟨Cv, hCv0, hCv⟩ := (hreg (τ + 1) (by linarith)).hvan
  refine ⟨Cv, hCv0, fun z θ hz hθ => ?_⟩
  have hmem : τ ∈ Set.Icc (0 : ℝ) (τ + 1) := ⟨hτ, by linarith⟩
  have h := hCv τ hmem z θ (le_of_lt hz) hθ
  rwa [Work.FTS.RegPkgGal.extG_of_pos (g := G) hz hτ, hG z θ τ hz hθ hτ] at h

/-- The pointwise `Γ`-bound of the whole profile at a fixed `τ ≥ 0`. -/
theorem ftau_abs_le_Gamma {a τ : ℝ} (ha : 0 < a) (ha13 : a ≤ 1 / 3) (hτ : 0 ≤ τ)
    {g G : Fam} {A B : ℝ → ℝ}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∃ Cg : ℝ, 0 ≤ Cg ∧ ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ z θ|
        ≤ Cg * Work.FTS.Regularity.Gamma a θ := by
  obtain ⟨Cv, hCv0, hCv⟩ := slice_abs_le_Gamma hτ hreg hG
  have hpa : 0 ≤ Work.FTS.Regularity.pExp a := le_of_lt (Work.FTS.Regularity.pExp_pos ha)
  refine ⟨5 * Work.FTS.Regularity.pExp a + Cv, by linarith, fun z θ hz hθ => ?_⟩
  have hstar := Fstar_abs_le_Gamma ha ha13 (le_of_lt hz) hθ
  have hg := hCv z θ hz hθ
  rw [Work.Construction.Ftau]
  calc |Work.Construction.Fstar (Work.FTS.Regularity.pExp a) z θ + g z θ τ|
      ≤ |Work.Construction.Fstar (Work.FTS.Regularity.pExp a) z θ| + |g z θ τ| := abs_add_le _ _
    _ ≤ 5 * Work.FTS.Regularity.pExp a * Work.FTS.Regularity.Gamma a θ
          + Cv * Work.FTS.Regularity.Gamma a θ := add_le_add hstar hg
    _ = (5 * Work.FTS.Regularity.pExp a + Cv) * Work.FTS.Regularity.Gamma a θ := by ring

/-- The profile `F(τ)` vanishes on the two angular boundary lines (on `z > 0`). -/
theorem ftau_vanish {a τ : ℝ} (ha : a ≠ 0) (hτ : 0 ≤ τ) {g G : Fam} {A B : ℝ → ℝ}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∀ z : ℝ, 0 < z →
      Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ z 0 = 0 ∧
      Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ z (π / 2) = 0 := by
  intro z hz
  have hmem : τ ∈ Set.Icc (0 : ℝ) (τ + 1) := ⟨hτ, by linarith⟩
  have hv := (hreg (τ + 1) (by linarith)).vanish hmem
  have hIθ0 : (0 : ℝ) ∈ Work.Spaces.Iθ := ⟨le_rfl, by positivity⟩
  have hIθ1 : (π / 2 : ℝ) ∈ Work.Spaces.Iθ := ⟨by positivity, le_rfl⟩
  have hg0 : g z 0 τ = 0 := by
    rw [← hG z 0 τ hz hIθ0 hτ, ← Work.FTS.RegPkgGal.extG_of_pos (g := G) hz hτ]
    exact hv.1 z
  have hg1 : g z (π / 2) τ = 0 := by
    rw [← hG z (π / 2) τ hz hIθ1 hτ, ← Work.FTS.RegPkgGal.extG_of_pos (g := G) hz hτ]
    exact hv.2 z
  constructor
  · simp only [Work.Construction.Ftau, Fstar_apply_zero ha, hg0, add_zero]
  · simp only [Work.Construction.Ftau, Fstar_apply_pi_div_two ha, hg1, add_zero]

/-- The profile `F(τ)` is supported in `z ≥ L` for some `L > 0`. -/
theorem ftau_supp {a τ : ℝ} (hτ : 0 ≤ τ) {g G : Fam} {A B : ℝ → ℝ}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∃ L : ℝ, 0 < L ∧ ∀ z θ : ℝ, L ≤ z → θ ∈ Work.Spaces.Iθ →
      Work.Construction.Ftau (Work.FTS.Regularity.pExp a) g τ z θ = 0 := by
  obtain ⟨L, hL0, hL⟩ := (hreg (τ + 1) (by linarith)).supp
  refine ⟨L, hL0, fun z θ hzL hθ => ?_⟩
  have hz : 0 < z := lt_of_lt_of_le hL0 hzL
  rw [Ftau_eq_profFull hτ hG hz hθ]
  exact hL τ ⟨hτ, by linarith⟩ z θ hzL

/-- The uniform bound on `∂_zg` on the closed strip, transported from `RegPkg'.abs_le_Npz`. -/
theorem slice_pz_le {a τ : ℝ} (hτ : 0 ≤ τ) {g G : Fam} {A B : ℝ → ℝ}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.pz (slice g τ) z θ| ≤ N := by
  obtain ⟨N, hN0, hN⟩ := (hreg (τ + 1) (by linarith)).abs_le_Npz
  refine ⟨N, hN0, fun z θ hz hθ => ?_⟩
  have hmem : τ ∈ Set.Icc (0 : ℝ) (τ + 1) := ⟨hτ, by linarith⟩
  have hev : (fun z' => Work.FTS.RegPkgGal.extG G z' θ τ) =ᶠ[𝓝 z] (fun z' => g z' θ τ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    rw [Work.FTS.RegPkgGal.extG_of_pos (g := G) hz' hτ, hG z' θ τ hz' hθ hτ]
  have hder : Work.Spaces.pz (Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG G) τ) z θ
      = Work.Spaces.pz (slice g τ) z θ := by
    simp only [Work.Spaces.pz, Work.FTS.Galerkin.slice, Work.FTS.Regularity.gSlice]
    exact hev.deriv_eq
  rw [← hder]
  exact hN τ hmem z θ (le_of_lt hz) hθ

/-- **The angular modulus of `∂_zg` at the two ends**: `|∂_zg(z,θ)| ≤ N·|θ - θ₀|^a` for
`θ₀ ∈ {0, π/2}`.  The value at `θ₀` is `0` (the slice vanishes identically in `z` there) and the
Jet-Hölder clause of `RegPkg'.hpz` gives the modulus. -/
theorem slice_pz_endpoint_le {a τ : ℝ} (hτ : 0 ≤ τ) {g G : Fam} {A B : ℝ → ℝ}
    (hreg : ∀ S : ℝ, 0 < S → Work.FTS.RegPkgGal.RegPkg' a S A B (Work.FTS.RegPkgGal.extG G))
    (hG : ∀ z θ τ, 0 < z → θ ∈ Work.Spaces.Iθ → 0 ≤ τ → G z θ τ = g z θ τ) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ θ₀ : ℝ, θ₀ ∈ Work.Spaces.Iθ → (θ₀ = 0 ∨ θ₀ = π / 2) →
      ∀ z θ : ℝ, 0 < z → θ ∈ Work.Spaces.Iθ →
        |Work.Spaces.pz (slice g τ) z θ| ≤ N * |θ - θ₀| ^ a := by
  obtain ⟨N, hN⟩ := (hreg (τ + 1) (by linarith)).hpz
  refine ⟨N, Work.FTS.Regularity.Jet.nonneg hN, ?_⟩
  intro θ₀ hθ₀ hθ₀' z θ hz hθ
  have hmem : τ ∈ Set.Icc (0 : ℝ) (τ + 1) := ⟨hτ, by linarith⟩
  have hv := (hreg (τ + 1) (by linarith)).vanish hmem
  -- `∂_zg` agrees with `∂_z` of the extended family
  have hev : (fun z' => Work.FTS.RegPkgGal.extG G z' θ τ) =ᶠ[𝓝 z] (fun z' => g z' θ τ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    rw [Work.FTS.RegPkgGal.extG_of_pos (g := G) hz' hτ, hG z' θ τ hz' hθ hτ]
  have hder : Work.Spaces.pz (Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG G) τ) z θ
      = Work.Spaces.pz (slice g τ) z θ := by
    simp only [Work.Spaces.pz, Work.FTS.Galerkin.slice, Work.FTS.Regularity.gSlice]
    exact hev.deriv_eq
  -- the value at the end `θ₀` is `0`
  have hzero : Work.Spaces.pz
      (Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG G) τ) z θ₀ = 0 := by
    have hz0 : ∀ z' : ℝ, 0 < z' →
        Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG G) τ z' θ₀ = 0 := by
      intro z' hz'
      rcases hθ₀' with h | h
      · rw [h]; exact hv.1 z'
      · rw [h]; exact hv.2 z'
    have hev2 : (fun z' => Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG G) τ z' θ₀)
        =ᶠ[𝓝 z] (fun _ => 0) := by
      filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
      exact hz0 z' hz'
    rw [Work.Spaces.pz, hev2.deriv_eq, deriv_const]
  have hth := Work.FTS.Regularity.Jet.thmod hN (z := z) (θ := θ) (θ' := θ₀) (τ := τ)
    (le_of_lt hz) hθ hθ₀ hmem
  calc |Work.Spaces.pz (slice g τ) z θ|
      = |Work.Spaces.pz (Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG G) τ) z θ
          - Work.Spaces.pz (Work.FTS.Regularity.gSlice (Work.FTS.RegPkgGal.extG G) τ) z θ₀| := by
        rw [hzero, sub_zero, hder]
    _ ≤ N * |θ - θ₀| ^ a := hth

/-! ## §4 Curry/Fréchet tools for `pz` on an open set -/

/-- **Continuity of `pz` from `C²`-smoothness of the uncurried function on an open set** (the
`C²`-instance of `Work.Spaces.contDiffOn_uncurry_pz`). -/
theorem continuousOn_uncurry_pz_of {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : ContDiffOn ℝ 2 (Function.uncurry G) V) :
    ContinuousOn (Function.uncurry (Work.Spaces.pz G)) V := by
  have hchain : ∀ p ∈ V, Work.Spaces.pz G p.1 p.2
      = (fderiv ℝ (Function.uncurry G) p) ((1, 0) : ℝ × ℝ) := by
    intro p hp
    exact Work.Spaces.pz_eq_fderiv
      ((h.differentiableOn (n := 2) (by norm_num)).differentiableAt (hV.mem_nhds hp))
  have hfd : ContinuousOn (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := 1) hV.uniqueDiffOn (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact (h'.continuousOn).congr (fun p hp => (fderivWithin_of_isOpen hV hp).symm)
  have hc : ContinuousOn (fun _ : ℝ × ℝ => ((1, 0) : ℝ × ℝ)) V := continuousOn_const
  have hcomp : ContinuousOn
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) ((1, 0) : ℝ × ℝ)) V :=
    hfd.clm_apply hc
  exact hcomp.congr hchain

/-- **`pz` of a sum** on an open set where both summands are `C¹` (the `deriv`-additivity of the
two slices). -/
theorem pz_add_of {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (hf : ContDiffOn ℝ 1 (Function.uncurry f) V) (hg : ContDiffOn ℝ 1 (Function.uncurry g) V)
    {p : ℝ × ℝ} (hp : p ∈ V) :
    Work.Spaces.pz (f + g) p.1 p.2
      = Work.Spaces.pz f p.1 p.2 + Work.Spaces.pz g p.1 p.2 := by
  have hdf : DifferentiableAt ℝ (fun z' => f z' p.2) p.1 :=
    Work.Spaces.differentiableAt_curry_left
      ((hf.differentiableOn (n := 1) (by norm_num)).differentiableAt (hV.mem_nhds hp))
  have hdg : DifferentiableAt ℝ (fun z' => g z' p.2) p.1 :=
    Work.Spaces.differentiableAt_curry_left
      ((hg.differentiableOn (n := 1) (by norm_num)).differentiableAt (hV.mem_nhds hp))
  have h := deriv_add hdf hdg
  rw [Work.Spaces.pz, Work.Spaces.pz, Work.Spaces.pz]
  exact h

end Work.FTS_StreamBdry.Inputs
