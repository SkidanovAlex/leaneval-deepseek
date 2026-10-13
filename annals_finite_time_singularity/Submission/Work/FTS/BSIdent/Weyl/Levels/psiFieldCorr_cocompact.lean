import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.FTS.BSIdent.Defs
import Submission.Work.FTS.BSIdent.Cyl.DecayAux.Basic
import Submission.Work.FTS.BSIdent.Weyl.Corrected
import Submission.Work.FTS.BSIdent.Weyl.Levels.merPsiT_decay_bounds_ne
import Submission.Work.FTS.BSIdent.Weyl.Levels._dev12

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The corrected stream-function field of the ansatz decays at infinity

`Work.FTS.BSIdent.psiFieldCorr ψ L` is the globally defined replacement of the Lean field
`Cyl.psiField ψ` (which is discontinuous at the axis): on the axis `r = 0` it takes the value
`-(2 L z) • e_z`, off the axis it is `Cyl.psiField ψ`.  For the concrete meridian stream
function `ψ = merPsiT α A B Φ C t` and the axis level
`L = Dev12.axisLevel α A B Φ (clockInv C t) = -z A(τ)⁻¹ ∂_θΦ(ρ(0,z)^{3α}/B(τ), π/2)`,
this file proves the decay clause of the corrected bundle
(`Weyl.merPsi_corrected_bundle`): `psiFieldCorr ψ L x → 0` as `x → ∞`.

The pointwise bound is `‖psiFieldCorr ψ L x‖ ≤ K / (1 + ‖x‖)`, obtained by combining

* the sharp decay bounds for `ψ/r`, `∂_zψ`, `∂_rψ` off the plane `z = 0`
  (`Levels.merPsiT_decay_bounds_ne`, which uses the *first* power of `π/2 - θ` in the rate and
  only `2 ≤ 3αλ`);
* the values `ψ = 0`, `∂_rψ = 0`, `∂_zψ = (A τ)⁻¹ r ∂_θΦ(r^{3α}/B(τ),0)` on the plane `z = 0`
  (`Dev5.merPsiT_zero_snd`, `Dev5.pdR_merPsiT_zero_snd`, `Dev11.pdZ_merPsiT_zero_snd`),
  bounded by the rate at `θ = 0`;
* the bound `|∂_θΦ(w,π/2)| ≤ C₀ (1+w)^{-λ}` at the endpoint `θ = π/2`, which the rate
  hypothesis only gives for `θ < π/2`; it is obtained by continuity of the slice derivative
  (`Dev2.continuousAt_pdZ_Phi`) and `le_of_tendsto`.  This bounds the axis level `L` by
  `|z| (1 + |z|^{3α}/B)^{-λ} ≤ 2 max 1 (B^λ)/(1+|z|)`, using `2 ≤ 3αλ`
  (`rho_mul_rpow_weight_le_two`).
-/

namespace Work.FTS.BSIdent.Weyl.Levels

open Filter Set
open scoped Topology

set_option maxHeartbeats 1000000

variable {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam} {C : Physical.PhysClock} {t : ℝ}

/-- The constant of the pointwise decay bound: `|A(τ)⁻¹| C₀ · 2 max 1 (B(τ)^λ)`. -/
noncomputable def corrDecayC (A B : ℝ → ℝ) (τ C₀ lam : ℝ) : ℝ :=
  |(A τ)⁻¹| * C₀ * (2 * max 1 ((B τ) ^ lam))

theorem corrDecayC_nonneg {A B : ℝ → ℝ} {τ C₀ lam : ℝ} (hC₀ : 0 ≤ C₀) :
    0 ≤ corrDecayC A B τ C₀ lam := by
  rw [corrDecayC]
  have h1 : (0 : ℝ) ≤ max 1 ((B τ) ^ lam) := le_trans zero_le_one (le_max_left _ _)
  exact mul_nonneg (mul_nonneg (abs_nonneg _) hC₀) (by linarith)

/-- **The derivative of the profile at the endpoint `θ = π/2`.**  The rate hypothesis bounds
`∂_θΦ` only for `θ < π/2`; at `θ = π/2` the bound follows by continuity, `∂_θΦ` being the
`θ`-derivative of a `C²` function. -/
theorem pdZ_Phi_pi_div_two_le {Φ : Work.FTS.BSIdent.Fam} {τ C₀ lam w : ℝ}
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (hw : 0 < w)
    (hrate : ∀ θ : ℝ, 0 ≤ θ → θ < Real.pi / 2 →
      |deriv (fun θ' : ℝ => Φ w θ' τ) θ| ≤ C₀ * (1 + w) ^ (-lam)) :
    |deriv (fun θ' : ℝ => Φ w θ' τ) (Real.pi / 2)| ≤ C₀ * (1 + w) ^ (-lam) := by
  have hcontP : ContinuousAt (fun p : ℝ × ℝ => deriv (fun z' : ℝ => Φ p.1 z' τ) p.2)
      (w, Real.pi / 2) := by
    have h := Work.FTS.BSIdent.Weyl.Dev2.continuousAt_pdZ_Phi (τ := τ) (Φ := Φ) hsm
      (w := w) (θ := Real.pi / 2) (by linarith) Work.FTS.BSIdent.Weyl.Dev2.abs_pi_div_two_lt
    simpa only [Work.Cyl.pdZ] using h
  have hcont' : ContinuousAt (fun θ : ℝ => deriv (fun θ' : ℝ => Φ w θ' τ) θ) (Real.pi / 2) :=
    hcontP.comp (continuousAt_const.prodMk continuousAt_id)
  have hlim : Filter.Tendsto (fun θ : ℝ => |deriv (fun θ' : ℝ => Φ w θ' τ) θ|)
      (𝓝[Set.Iio (Real.pi / 2)] (Real.pi / 2))
      (𝓝 |deriv (fun θ' : ℝ => Φ w θ' τ) (Real.pi / 2)|) :=
    (hcont'.tendsto.mono_left nhdsWithin_le_nhds).abs
  refine le_of_tendsto hlim ?_
  filter_upwards [self_mem_nhdsWithin (s := Set.Iio (Real.pi / 2)),
    nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds (show (0 : ℝ) < Real.pi / 2 by positivity))]
    with θ hθ hθ0
  exact hrate θ hθ0.le hθ

/-- **The axis level decays.**  For every `z`,
`|axisLevel α A B Φ τ z| ≤ |A(τ)⁻¹| C₀ · 2 max 1 (B(τ)^λ) / (1+|z|)`; at `z = 0` the level
vanishes, and for `z ≠ 0` the bound is the weighted rpow bound `rho_mul_rpow_weight_le_two`
applied to `ρ = |z|` together with the endpoint derivative bound. -/
theorem axisLevel_le {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam} {τ C₀ lam : ℝ}
    (hB : 0 < B τ) (hC₀ : 0 ≤ C₀) (hp : 0 < Work.FTS.Regularity.pExp α)
    (hlam : 0 < lam) (hpl : 2 ≤ Work.FTS.Regularity.pExp α * lam)
    (hD : ∀ w : ℝ, 0 < w → |deriv (fun θ' : ℝ => Φ w θ' τ) (Real.pi / 2)|
      ≤ C₀ * (1 + w) ^ (-lam)) (z : ℝ) :
    |Work.FTS.BSIdent.Weyl.Dev12.axisLevel α A B Φ τ z|
      ≤ corrDecayC A B τ C₀ lam / (1 + |z|) := by
  rcases eq_or_ne z 0 with hz | hz
  · subst hz
    have h0 : Work.FTS.BSIdent.Weyl.Dev12.axisLevel α A B Φ τ 0 = 0 := by
      rw [Work.FTS.BSIdent.Weyl.Dev12.axisLevel]; ring
    rw [h0, abs_zero]
    have hc := corrDecayC_nonneg (A := A) (B := B) (τ := τ) (C₀ := C₀) (lam := lam) hC₀
    positivity
  · have hwpos : 0 < Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ :=
      div_pos (Real.rpow_pos_of_pos (Work.FTS.BSIdent.Weyl.Dev8.rhoP_zero_pos hz) _) hB
    have h2 : |deriv (fun θ' : ℝ => Φ (Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ)
          θ' τ) (Real.pi / 2)|
        ≤ C₀ * (1 + Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ) ^ (-lam) :=
      hD _ hwpos
    have h1 : |Work.FTS.BSIdent.Weyl.Dev12.axisLevel α A B Φ τ z|
        = |z| * |(A τ)⁻¹| * |deriv (fun θ' : ℝ =>
            Φ (Work.Cyl.rhoP 0 z ^ Work.FTS.Regularity.pExp α / B τ) θ' τ) (Real.pi / 2)| := by
      rw [Work.FTS.BSIdent.Weyl.Dev12.axisLevel, abs_mul, abs_mul, abs_neg]
    rw [h1]
    rw [Work.FTS.BSIdent.Weyl.Dev8.rhoP_zero_eq_abs z] at h2 ⊢
    have h3 : |z| * (1 + |z| ^ Work.FTS.Regularity.pExp α / B τ) ^ (-lam)
        ≤ 2 * max 1 ((B τ) ^ lam) / (1 + |z|) :=
      Work.FTS.BSIdent.Weyl.Levels.rho_mul_rpow_weight_le_two
        (p := Work.FTS.Regularity.pExp α) (lam := lam) (b := B τ) (ρ := |z|)
        hp hlam hB (abs_nonneg z) hpl
    calc |z| * |(A τ)⁻¹| * |deriv (fun θ' : ℝ =>
            Φ (|z| ^ Work.FTS.Regularity.pExp α / B τ) θ' τ) (Real.pi / 2)|
        ≤ |z| * |(A τ)⁻¹| * (C₀ * (1 + |z| ^ Work.FTS.Regularity.pExp α / B τ) ^ (-lam)) :=
          mul_le_mul_of_nonneg_left h2 (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = |(A τ)⁻¹| * C₀ * (|z| * (1 + |z| ^ Work.FTS.Regularity.pExp α / B τ) ^ (-lam)) := by
          ring
      _ ≤ |(A τ)⁻¹| * C₀ * (2 * max 1 ((B τ) ^ lam) / (1 + |z|)) :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg (abs_nonneg _) hC₀)
      _ = corrDecayC A B τ C₀ lam / (1 + |z|) := by rw [corrDecayC]; ring

/-- **The values of `ψ`, `∂_zψ`, `∂_rψ` on the plane `θ = 0`.**  `ψ` and `∂_rψ` vanish there,
while `∂_zψ = (A τ)⁻¹ r ∂_θΦ(r^{3α}/B(τ), 0)`, which the rate at `θ = 0` and the weighted rpow
bound control by `corrDecayC/(1+r)`. -/
theorem merPsiT_zero_fst_bounds {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t τ C₀ lam : ℝ}
    (hτ : τ = Physical.clockInv C t)
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 →
      ContDiffAt ℝ 2 (fun p : ℝ × ℝ => Φ p.1 p.2 τ) (w, θ))
    (h0 : ∀ w : ℝ, 0 < w → Φ w 0 τ = 0) (hB : 0 < B τ)
    (hp : 0 < Work.FTS.Regularity.pExp α) (hlam : 0 < lam) (hC₀ : 0 ≤ C₀)
    (hpl : 2 ≤ Work.FTS.Regularity.pExp α * lam)
    (hrate0 : ∀ w : ℝ, 0 < w →
      |deriv (fun θ' : ℝ => Φ w θ' τ) 0| ≤ C₀ * (1 + w) ^ (-lam))
    {r : ℝ} (hr : 0 < r) :
    |Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r 0|
        ≤ corrDecayC A B τ C₀ lam / (1 + r) ∧
      Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r 0 = 0 ∧
      Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) r 0 = 0 := by
  have hψ := Work.FTS.BSIdent.Weyl.Dev5.merPsiT_zero_snd (α := α) (A := A) (B := B) (Φ := Φ)
    (C := C) (t := t) (τ := τ) hτ hB h0 hr
  have hpdR := Work.FTS.BSIdent.Weyl.Dev5.pdR_merPsiT_zero_snd (α := α) (A := A) (B := B)
    (Φ := Φ) (C := C) (t := t) (τ := τ) hτ hB h0 hr
  have hpdZ := Work.FTS.BSIdent.Weyl.Dev11.pdZ_merPsiT_zero_snd (α := α) (A := A) (B := B)
    (Φ := Φ) (C := C) (t := t) (τ := τ) hτ hsm h0 hB hr
  refine ⟨?_, hψ, hpdR⟩
  rw [hpdZ]
  have hD : |deriv (fun θ : ℝ => Φ (r ^ Work.FTS.Regularity.pExp α / B τ) θ τ) 0|
      ≤ C₀ * (1 + r ^ Work.FTS.Regularity.pExp α / B τ) ^ (-lam) :=
    hrate0 _ (div_pos (Real.rpow_pos_of_pos hr _) hB)
  have h3 : r * (1 + r ^ Work.FTS.Regularity.pExp α / B τ) ^ (-lam)
      ≤ 2 * max 1 ((B τ) ^ lam) / (1 + r) :=
    Work.FTS.BSIdent.Weyl.Levels.rho_mul_rpow_weight_le_two
      (p := Work.FTS.Regularity.pExp α) (lam := lam) (b := B τ) (ρ := r) hp hlam hB hr.le hpl
  calc |(A τ)⁻¹ * r * deriv (fun θ : ℝ => Φ (r ^ Work.FTS.Regularity.pExp α / B τ) θ τ) 0|
      = |(A τ)⁻¹| *
          (r * |deriv (fun θ : ℝ => Φ (r ^ Work.FTS.Regularity.pExp α / B τ) θ τ) 0|) := by
        rw [abs_mul, abs_mul, abs_of_pos hr]; ring
    _ ≤ |(A τ)⁻¹| * (r * (C₀ * (1 + r ^ Work.FTS.Regularity.pExp α / B τ) ^ (-lam))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hD hr.le) (abs_nonneg _)
    _ = |(A τ)⁻¹| * C₀ * (r * (1 + r ^ Work.FTS.Regularity.pExp α / B τ) ^ (-lam)) := by ring
    _ ≤ |(A τ)⁻¹| * C₀ * (2 * max 1 ((B τ) ^ lam) / (1 + r)) :=
        mul_le_mul_of_nonneg_left h3 (mul_nonneg (abs_nonneg _) hC₀)
    _ = corrDecayC A B τ C₀ lam / (1 + r) := by rw [corrDecayC]; ring

/-- **The norm of the stream-function field** from the three bounds: off the axis,
`psiField ψ x = (∂_zψ/r) • r e_r - (ψ/r + ∂_rψ) • e_z` in the orthogonal frame
`(radialVec, e_z)`, so `‖psiField ψ x‖ ≤ |∂_zψ| + |ψ|/r + |∂_rψ|`. -/
theorem psiField_norm_le {ψ : ℝ → ℝ → ℝ} {M : ℝ} {x : Work.FTS.BSIdent.R3}
    (hx : Work.Cyl.radial x ≠ 0)
    (h1 : |Work.Cyl.pdZ ψ (Work.Cyl.radial x) (Work.Cyl.axial x)| ≤ M / (1 + ‖x‖))
    (h2 : |ψ (Work.Cyl.radial x) (Work.Cyl.axial x)| / Work.Cyl.radial x ≤ M / (1 + ‖x‖))
    (h3 : |Work.Cyl.pdR ψ (Work.Cyl.radial x) (Work.Cyl.axial x)| ≤ M / (1 + ‖x‖)) :
    ‖Work.Cyl.psiField ψ x‖ ≤ 3 * M / (1 + ‖x‖) := by
  have hr : 0 < Work.Cyl.radial x := lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm hx)
  have hnorm : ‖Work.Cyl.psiField ψ x‖
      ≤ |Work.Cyl.pdZ ψ (Work.Cyl.radial x) (Work.Cyl.axial x)|
        + (|ψ (Work.Cyl.radial x) (Work.Cyl.axial x)| / Work.Cyl.radial x
          + |Work.Cyl.pdR ψ (Work.Cyl.radial x) (Work.Cyl.axial x)|) := by
    rw [Work.Cyl.psiField, Work.Cyl.cylField]
    refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [norm_smul, Real.norm_eq_abs, Work.FTS.BSIdent.Cyl.norm_radialVec_eq, abs_div,
        abs_of_pos hr]
      exact le_of_eq (div_mul_cancel₀ _ (ne_of_gt hr))
    · rw [norm_smul, Real.norm_eq_abs, Work.FTS.BSIdent.Cyl.norm_eZ_eq, mul_one]
      have hsplit : (-(ψ (Work.Cyl.radial x) (Work.Cyl.axial x) / Work.Cyl.radial x)
            - Work.Cyl.pdR ψ (Work.Cyl.radial x) (Work.Cyl.axial x))
          = -((ψ (Work.Cyl.radial x) (Work.Cyl.axial x) / Work.Cyl.radial x)
            + Work.Cyl.pdR ψ (Work.Cyl.radial x) (Work.Cyl.axial x)) := by ring
      rw [hsplit, abs_neg]
      refine (abs_add_le _ _).trans ?_
      rw [abs_div, abs_of_pos hr]
  calc ‖Work.Cyl.psiField ψ x‖
      ≤ |Work.Cyl.pdZ ψ (Work.Cyl.radial x) (Work.Cyl.axial x)|
        + (|ψ (Work.Cyl.radial x) (Work.Cyl.axial x)| / Work.Cyl.radial x
          + |Work.Cyl.pdR ψ (Work.Cyl.radial x) (Work.Cyl.axial x)|) := hnorm
    _ ≤ M / (1 + ‖x‖) + (M / (1 + ‖x‖) + M / (1 + ‖x‖)) := add_le_add h1 (add_le_add h2 h3)
    _ = 3 * M / (1 + ‖x‖) := by ring

theorem psiFieldCorr_cocompact {α : ℝ} {A B : ℝ → ℝ} {Φ : Work.FTS.BSIdent.Fam}
    {C : Physical.PhysClock} {t : ℝ}
    (hα : 0 < α) (hA : A (Physical.clockInv C t) ≠ 0) (hB : 0 < B (Physical.clockInv C t))
    (hsm : ∀ w θ : ℝ, -1 < w → -Real.pi / 2 - 1 < θ → θ < Real.pi / 2 + 1 → ContDiffAt ℝ 2
      (fun p : ℝ × ℝ => Φ p.1 p.2 (Physical.clockInv C t)) (w, θ))
    (hzeroPlane : ∀ w : ℝ, 0 < w → Φ w 0 (Physical.clockInv C t) = 0)
    (hzeroAxis : ∀ w : ℝ, 0 < w → Φ w (Real.pi / 2) (Physical.clockInv C t) = 0)
    {lam C₀ : ℝ} (hlam : 0 < lam) (hC₀ : 0 < C₀)
    (hexp : 2 ≤ Work.FTS.Regularity.pExp α * lam)
    (hrate : ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ (Physical.clockInv C t)| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam) ∧
      |deriv (fun w' : ℝ => Φ w' θ (Physical.clockInv C t)) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) θ| ≤ C₀ * (1 + w) ^ (-lam) ∧
      |deriv (fun θ' : ℝ => deriv (fun θ'' : ℝ => Φ w θ'' (Physical.clockInv C t)) θ') θ|
        ≤ C₀ * (1 + w) ^ (-lam) ∧
      |deriv (fun θ' : ℝ => deriv (fun w' : ℝ => Φ w' θ' (Physical.clockInv C t)) w) θ|
        ≤ C₀ * (1 + w) ^ (-lam - 1) ∧
      |deriv (fun w' : ℝ => deriv (fun w'' : ℝ => Φ w'' θ (Physical.clockInv C t)) w') w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-lam - 2)) :
    Filter.Tendsto (fun x : Work.FTS.BSIdent.R3 => Work.FTS.BSIdent.psiFieldCorr
        (fun r z => Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r z)
        (Work.FTS.BSIdent.Weyl.Dev12.axisLevel α A B Φ (Physical.clockInv C t)) x)
      (Filter.cocompact Work.FTS.BSIdent.R3) (nhds 0) := by
  have hp : 0 < Work.FTS.Regularity.pExp α := Work.FTS.Regularity.pExp_pos hα
  have hC₀nn : 0 ≤ C₀ := hC₀.le
  -- the sharp decay bounds off the plane `z = 0`
  obtain ⟨K₁, hK₁nn, hK₁⟩ :=
    merPsiT_decay_bounds_ne hα hA hB hsm hzeroPlane hzeroAxis hlam hC₀ hexp hrate
  set cA : ℝ := corrDecayC A B (Physical.clockInv C t) C₀ lam with hcA
  have hcAnn : 0 ≤ cA := by rw [hcA]; exact corrDecayC_nonneg hC₀nn
  set K : ℝ := max (3 * K₁) (3 * cA) with hK
  have hKnn : 0 ≤ K := by rw [hK]; exact le_trans (by linarith) (le_max_left _ _)
  -- the endpoint derivative bound at `θ = π/2`
  have hDpi : ∀ w : ℝ, 0 < w →
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) (Real.pi / 2)|
        ≤ C₀ * (1 + w) ^ (-lam) := by
    intro w hw
    exact pdZ_Phi_pi_div_two_le (τ := Physical.clockInv C t) hsm hw
      (fun θ hθ0 hθ1 => (hrate w θ hw.le hθ0 hθ1).2.2.1)
  -- the rate at `θ = 0`
  have hD0 : ∀ w : ℝ, 0 < w →
      |deriv (fun θ' : ℝ => Φ w θ' (Physical.clockInv C t)) 0| ≤ C₀ * (1 + w) ^ (-lam) :=
    fun w hw => (hrate w 0 hw.le le_rfl (by linarith [Real.pi_pos])).2.2.1
  -- the pointwise rate bound
  have hpoint : ∀ x : Work.FTS.BSIdent.R3, ‖Work.FTS.BSIdent.psiFieldCorr
        (fun r z => Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t r z)
        (Work.FTS.BSIdent.Weyl.Dev12.axisLevel α A B Φ (Physical.clockInv C t)) x‖
      ≤ K / (1 + ‖x‖) := by
    intro x
    by_cases hrad : Work.Cyl.radial x = 0
    · -- on the axis only the level `L (axial x)` survives
      rw [Work.FTS.BSIdent.psiFieldCorr_of_radial_eq hrad]
      have hL := axisLevel_le (α := α) (A := A) (B := B) (Φ := Φ)
        (τ := Physical.clockInv C t) (C₀ := C₀) (lam := lam) hB hC₀nn hp hlam hexp hDpi
        (Work.Cyl.axial x)
      rw [← hcA] at hL
      have hax : |Work.Cyl.axial x| = ‖x‖ := by
        have h01 : x 0 = 0 ∧ x 1 = 0 := (Work.Cyl.radial_eq_zero_iff x).mp hrad
        have hrho : Work.Cyl.rho x = |Work.Cyl.axial x| := by
          rw [Work.Cyl.rho, Work.Cyl.radSq, Work.Cyl.axial, h01.1, h01.2]
          rw [show (0 : ℝ) ^ 2 + 0 ^ 2 + x 2 ^ 2 = x 2 ^ 2 from by ring,
            Real.sqrt_sq_eq_abs]
        rw [← hrho]
        exact Work.Cyl.rho_eq_norm x
      have hnorm : ‖(-(2 * Work.FTS.BSIdent.Weyl.Dev12.axisLevel α A B Φ
            (Physical.clockInv C t) (Work.Cyl.axial x))) • Work.Cyl.eZ‖
          = 2 * |Work.FTS.BSIdent.Weyl.Dev12.axisLevel α A B Φ (Physical.clockInv C t)
            (Work.Cyl.axial x)| := by
        rw [norm_smul, Real.norm_eq_abs, Work.FTS.BSIdent.Cyl.norm_eZ_eq, mul_one, abs_neg,
          abs_mul]
        norm_num
      rw [hnorm]
      calc 2 * |Work.FTS.BSIdent.Weyl.Dev12.axisLevel α A B Φ (Physical.clockInv C t)
              (Work.Cyl.axial x)|
          ≤ 2 * (cA / (1 + |Work.Cyl.axial x|)) := mul_le_mul_of_nonneg_left hL (by norm_num)
        _ = 2 * cA / (1 + ‖x‖) := by rw [hax]; ring
        _ ≤ K / (1 + ‖x‖) := by
            rw [hK]
            exact div_le_div_of_nonneg_right
              (by linarith [le_max_right (3 * K₁) (3 * cA), hcAnn]) (by positivity)
    · -- off the axis: the three bounds for `∂_zψ`, `ψ/r`, `∂_rψ`
      rw [Work.FTS.BSIdent.psiFieldCorr_of_radial_ne hrad]
      change ‖Work.Cyl.psiField (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t) x‖
        ≤ K / (1 + ‖x‖)
      have hr : 0 < Work.Cyl.radial x :=
        lt_of_le_of_ne (Work.Cyl.radial_nonneg x) (Ne.symm hrad)
      have hρ : Work.Cyl.rhoP (Work.Cyl.radial x) (Work.Cyl.axial x) = ‖x‖ :=
        (Work.FTS.BSIdent.rhoP_radial_axial x).trans (Work.Cyl.rho_eq_norm x)
      have hd : 0 ≤ 1 + ‖x‖ := by positivity
      have hK3nn : 0 ≤ K / 3 := div_nonneg hKnn (by norm_num)
      rcases eq_or_ne (Work.Cyl.axial x) 0 with hz | hz
      · -- the plane `z = 0`
        obtain ⟨hz1, hz2, hz3⟩ := merPsiT_zero_fst_bounds (α := α) (A := A) (B := B) (Φ := Φ)
          (C := C) (t := t) (τ := Physical.clockInv C t) rfl hsm hzeroPlane
          hB hp hlam hC₀nn hexp hD0 (r := Work.Cyl.radial x) hr
        rw [← hcA] at hz1
        have hρ0 : Work.Cyl.rhoP (Work.Cyl.radial x) 0 = ‖x‖ := by rw [← hz]; exact hρ
        have hrx : Work.Cyl.radial x = ‖x‖ := by
          rw [← Work.FTS.BSIdent.Weyl.Dev11.rhoP_zero_snd hr]; exact hρ0
        have hcAk : cA ≤ K / 3 := by rw [hK]; linarith [le_max_right (3 * K₁) (3 * cA)]
        have hA1 : |Work.Cyl.pdZ (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t)
              (Work.Cyl.radial x) 0| ≤ K / 3 / (1 + ‖x‖) := by
          have hle : cA / (1 + Work.Cyl.radial x) ≤ K / 3 / (1 + ‖x‖) := by
            rw [hrx]
            exact div_le_div_of_nonneg_right hcAk hd
          exact hz1.trans hle
        have hA2 : |Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t (Work.Cyl.radial x) 0|
              / Work.Cyl.radial x ≤ K / 3 / (1 + ‖x‖) := by
          rw [hz2]
          simp only [abs_zero, zero_div]
          exact div_nonneg hK3nn hd
        have hA3 : |Work.Cyl.pdR (Work.FTS.BSIdent.Cyl.merPsiT α A B Φ C t)
              (Work.Cyl.radial x) 0| ≤ K / 3 / (1 + ‖x‖) := by
          rw [hz3]
          simp only [abs_zero]
          exact div_nonneg hK3nn hd
        refine (psiField_norm_le (M := K / 3) hrad ?_ ?_ ?_).trans (le_of_eq (by ring))
        · rw [hz]; exact hA1
        · rw [hz]; exact hA2
        · rw [hz]; exact hA3
      · -- off the plane `z = 0`
        obtain ⟨hk1, hk2, hk3⟩ := hK₁ (Work.Cyl.radial x) (Work.Cyl.axial x) hr hz
        rw [hρ] at hk1 hk2 hk3
        have hK1k : K₁ ≤ K / 3 := by rw [hK]; linarith [le_max_left (3 * K₁) (3 * cA)]
        refine (psiField_norm_le (M := K / 3) hrad ?_ ?_ ?_).trans (le_of_eq (by ring))
        · exact hk2.trans (div_le_div_of_nonneg_right hK1k hd)
        · exact hk1.trans (div_le_div_of_nonneg_right hK1k hd)
        · exact hk3.trans (div_le_div_of_nonneg_right hK1k hd)
  -- `K/(1+‖x‖) → 0` at cocompact, and squeeze
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have h4 : Filter.Tendsto (fun x : Work.FTS.BSIdent.R3 => 1 + ‖x‖)
      (Filter.cocompact Work.FTS.BSIdent.R3) Filter.atTop :=
    Filter.tendsto_atTop_mono (f := fun x : Work.FTS.BSIdent.R3 => ‖x‖)
      (fun x => by linarith [norm_nonneg x]) tendsto_norm_cocompact_atTop
  have h5 : Filter.Tendsto (fun x : Work.FTS.BSIdent.R3 => K / (1 + ‖x‖))
      (Filter.cocompact Work.FTS.BSIdent.R3) (nhds 0) := by
    simpa [div_eq_mul_inv] using (h4.inv_tendsto_atTop).const_mul K
  exact squeeze_zero' (Eventually.of_forall fun x => norm_nonneg _)
    (Eventually.of_forall hpoint) h5

end Work.FTS.BSIdent.Weyl.Levels
