import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeBound2
import Submission.Work.FTS_StreamBdry.SB6.UprimeAux.OdeFacts
import Submission.Work.FTS_StreamBdry.SB6.Vop_far
import Submission.Work.FTS_StreamBdry.SB6.clauses3
import Submission.Work.FTS_StreamBdry.SB6.uprime_le
import Submission.Work.FTS_StreamBdry.SBpsiP.SelfUprime
import Submission.Work.FTS_StreamBdry.sb2_c2_proved
import Submission.Work.FTS_StreamBdry.sb2_dthDV_proved
import Submission.Work.FTS_StreamBdry.sb5_barrier_proved

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_StreamBdry.SB6.sb6_rates` — the (SB6) rates for `Φ`

Assembles the three one-variable rates of `Φ w θ = oddPerS (psiP αG Ψ) w θ` (extended by `0`
on `w ≤ 0`) from the compact/far-field data:

* clause 1 (`clauses1.Phi_clause1`): `|Φ| ≤ A₁ (π/2-θ) (1+w)^{-4/αG}`;
* clause 2 (`clauses2.Phi_clause2`): `|∂_wΦ| ≤ A₂ (π/2-θ) (1+w)^{-4/αG-1}`;
* clause 3 (`clauses3.Phi_clause3`): `|∂_θΦ| ≤ A₃ (1+w)^{-4/αG}`.

The constant data: `Kf` (far-field decay of `D_z^j psiP` from `far_rate`), `Kv` (far-field
decay of `V(psiP)` from `psiP_Vop_far`), `Kpth` (compact bound on `∂_θ psiP` from
`pth_DzIter_le`), `K0` (the near-axis hypothesis `hnear0`), `M` (the `SlotBd` bound).

(The declaration `SB6.uprime_le` lives in `SB6/uprime_le.lean`; the former development-only
temporary `uprime_tmp` has been replaced by that import.)
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB6

open Work.FTS.StreamBdryIface (Uprime SlotBd SrcOK psiP oddPerS)

set_option autoImplicit false

/-- `psiP αG Ψ z (π/2) = 0` (the angular weight `sin 2θ` vanishes there). -/
lemma psiP_pi_div_two (αG : ℝ) (Ψ : ℝ → ℝ → ℝ) (z : ℝ) :
    psiP αG Ψ z (Real.pi / 2) = 0 := by
  simp only [Work.FTS.StreamBdryIface.psiP, Work.Construction.s2_eq,
    show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi, zero_div, zero_mul, neg_zero]

theorem sb6_rates {αG M L Mf : ℝ} (hαG : 0 < αG) {F Ψ : ℝ → ℝ → ℝ}
    (hsol : Work.FTS.StrongGlobal.IsBslSolPos αG F Ψ)
    (h3 : ContDiffOn ℝ 3 (Function.uncurry Ψ) Work.Construction.Qd)
    (hslot : Work.FTS.StreamBdryIface.SlotBd αG Ψ M)
    (hF : Work.FTS.StreamBdryIface.SrcOK F L Mf)
    (hnear0 : ∃ K : ℝ, ∀ z θ, (z, θ) ∈ Work.Construction.Qd → z ≤ 1 →
      |Work.Spaces.DzIter 1 (Work.FTS.StreamBdryIface.psiP αG Ψ) z θ|
        ≤ K * z * Work.Construction.s2 θ) :
    let Φ : ℝ → ℝ → ℝ := fun w θ =>
      if 0 < w then Work.FTS.StreamBdryIface.oddPerS (Work.FTS.StreamBdryIface.psiP αG Ψ) w θ
      else 0
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ w θ : ℝ, 0 ≤ w → 0 ≤ θ → θ < Real.pi / 2 →
      |Φ w θ| ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-(4 / αG)) ∧
      |deriv (fun w' : ℝ => Φ w' θ) w|
        ≤ C₀ * (Real.pi / 2 - θ) * (1 + w) ^ (-(4 / αG) - 1) ∧
      |deriv (fun θ' : ℝ => Φ w θ') θ| ≤ C₀ * (1 + w) ^ (-(4 / αG)) := by
  obtain ⟨hL, hF0⟩ := hF.2.2.2.2
  have hM : 0 ≤ M := M_nonneg hslot
  have hPpi : ∀ z, (psiP αG Ψ) z (Real.pi / 2) = 0 := psiP_pi_div_two αG Ψ
  have hpt : ((1 : ℝ), Real.pi / 4) ∈ Work.Construction.Qd :=
    Work.FTS_StreamBdry.mem_Qd.mpr ⟨by norm_num, by linarith [Real.pi_pos],
      by linarith [Real.pi_pos]⟩
  -- `|∂_θ(psiP/s2)| ≤ Ku` (from the ODE), hence `|∂_θ² psiP| ≤ K2`, hence the far-field rate
  obtain ⟨Ku, hKupos, hu⟩ := uprime_le (αG := αG) (M := M) (L := L) (Mf := Mf)
    hαG hsol h3 hslot hF
  obtain ⟨K2, hK2pos, hK2⟩ := psiP_pthIter2_le (Ku := Ku) hαG hsol h3 hslot hF hu
  obtain ⟨Kf, hKfpos, hfar⟩ := far_rate (K2 := K2) hαG hsol h3 hslot hF hK2
    (psiP_tendsto_atTop hαG hsol h3 hslot)
  have hKf0 : 0 ≤ Kf := le_of_lt hKfpos
  obtain ⟨Kv, hKvpos, hVop⟩ := psiP_Vop_far (Kf := Kf) hαG hsol h3 hslot hF hKf0 hfar
  have hKv0 : 0 ≤ Kv := le_of_lt hKvpos
  -- the compact `D_z`-bounds and `∂_θ(psiP)`
  have hDz : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 2,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ| ≤ M * Work.Construction.s2 θ :=
    fun z θ h j hj => Work.FTS_StreamBdry.SB3.psiP_DzLe hαG h3 hslot z θ h j hj
  have hDz3 : ∀ z θ, (z, θ) ∈ Work.Construction.Qd →
      |Work.Spaces.DzIter 3 (psiP αG Ψ) z θ| ≤ (2 * M / αG) * Work.Construction.s2 θ :=
    fun z θ h => Work.FTS_StreamBdry.SB3.psiP_D3_le hαG h3 hslot z θ h
  have hSg : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → ∀ j ≤ 3,
      |Work.Spaces.DzIter j (psiP αG Ψ) z θ|
        ≤ max M (2 * M / αG) * Work.Construction.s2 θ := by
    intro z θ h j hj
    have hs2nn : 0 ≤ Work.Construction.s2 θ :=
      Work.FTS_StreamBdry.s2_nonneg_of_Iθ (Work.FTS_StreamBdry.Qd_theta_Iθ h)
    rcases Nat.lt_or_ge j 3 with hj3 | hj3
    · exact (hDz z θ h j (by omega)).trans
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hs2nn)
    · have hj3' : j = 3 := by omega
      subst hj3'
      exact (hDz3 z θ h).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hs2nn)
  obtain ⟨Kpth, hKpth⟩ := Work.FTS_StreamBdry.SB3.pth_DzIter_le
    (Sg := max M (2 * M / αG)) hαG h3 hslot hSg
  have hKpth0 : 0 ≤ Kpth :=
    le_trans (abs_nonneg _) (hKpth 1 (Real.pi / 4) hpt 0 (by norm_num))
  obtain ⟨K0, hK0⟩ := hnear0
  have hK00 : 0 ≤ K0 := by
    have h1 := hK0 1 (Real.pi / 4) hpt (by norm_num)
    have h2 : Work.Construction.s2 (Real.pi / 4) = 1 := by
      rw [Work.Construction.s2_eq, show 2 * (Real.pi / 4) = Real.pi / 2 by ring,
        Real.sin_pi_div_two]
    rw [h2] at h1
    simp only [mul_one] at h1
    exact le_trans (abs_nonneg _) h1
  -- the near-axis bound on `∂_z psiP`
  have hpz_near : ∀ z θ, (z, θ) ∈ Work.Construction.Qd → z ≤ 1 →
      |Work.Spaces.pz (psiP αG Ψ) z θ| ≤ K0 * Work.Construction.s2 θ := by
    intro z θ hmem hz1
    have hzpos : 0 < z := Work.FTS_StreamBdry.Qd_pos hmem
    have h := hK0 z θ hmem hz1
    have hD : Work.Spaces.DzIter 1 (psiP αG Ψ) z θ
        = z * Work.Spaces.pz (psiP αG Ψ) z θ := rfl
    rw [hD, abs_mul, abs_of_pos hzpos] at h
    have h3 : |Work.Spaces.pz (psiP αG Ψ) z θ| ≤ (K0 * z * Work.Construction.s2 θ) / z :=
      (le_div_iff₀ hzpos).mpr (by linarith [h])
    have h4 : (K0 * z * Work.Construction.s2 θ) / z = K0 * Work.Construction.s2 θ := by
      field_simp
    linarith [h3, h4]
  -- the three clauses
  obtain ⟨A₁, hA₁0, hcl1⟩ := Phi_clause1 (M := M) (L := L) (Kf := Kf) (Ψ := Ψ)
    hαG hL hM hKf0 hPpi hDz hfar
  obtain ⟨A₂, hA₂0, hcl2⟩ := Phi_clause2 (M := M) (L := L) (Kf := Kf) (K0 := K0) (Ψ := Ψ)
    hαG hL hM hKf0 hK00 hPpi hpz_near hDz hfar
  obtain ⟨A₃, hA₃0, hcl3⟩ := Phi_clause3 (M := M) (L := L) (Kf := Kf) (Kpth := Kpth)
    (Kv := Kv) (Ψ := Ψ) hαG hL hM hKf0 hKpth0 hKv0 hPpi hDz hfar hKpth hVop
  refine ⟨max (max A₁ A₂) A₃ + 1, by positivity, ?_⟩
  intro w θ hw hθ hθ2
  refine ⟨?_, ?_, ?_⟩
  · refine (hcl1 w θ hw hθ hθ2).trans ?_
    have hA : A₁ ≤ max (max A₁ A₂) A₃ + 1 := by
      have h1 : A₁ ≤ max A₁ A₂ := le_max_left _ _
      have h2 : max A₁ A₂ ≤ max (max A₁ A₂) A₃ := le_max_left _ _
      linarith
    have hπ : 0 ≤ Real.pi / 2 - θ := by linarith [hθ2, Real.pi_pos]
    have hwk : 0 ≤ (1 + w) ^ (-(4 / αG)) := Real.rpow_nonneg (by linarith) _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hπ) hwk
  · refine (hcl2 w θ hw hθ hθ2).trans ?_
    have hA : A₂ ≤ max (max A₁ A₂) A₃ + 1 := by
      have h1 : A₂ ≤ max A₁ A₂ := le_max_right _ _
      have h2 : max A₁ A₂ ≤ max (max A₁ A₂) A₃ := le_max_left _ _
      linarith
    have hπ : 0 ≤ Real.pi / 2 - θ := by linarith [hθ2, Real.pi_pos]
    have hwk : 0 ≤ (1 + w) ^ (-(4 / αG) - 1) := Real.rpow_nonneg (by linarith) _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hπ) hwk
  · refine (hcl3 w θ hw hθ hθ2).trans ?_
    have hA : A₃ ≤ max (max A₁ A₂) A₃ + 1 := by
      have h1 : A₃ ≤ max (max A₁ A₂) A₃ := le_max_right _ _
      linarith
    have hwk : 0 ≤ (1 + w) ^ (-(4 / αG)) := Real.rpow_nonneg (by linarith) _
    exact mul_le_mul_of_nonneg_right hA hwk

end Work.FTS_StreamBdry.SB6
