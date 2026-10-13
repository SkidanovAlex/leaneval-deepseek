import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_StreamBdry.Basic
import Submission.Work.FTS_StreamBdry.SB25.Defs
import Submission.Work.FTS_StreamBdry.SB25.Sb5CmpAux
import Submission.Work.FTS_StreamBdry.SB25.Lgs_barrier
import Submission.Work.FTS_StreamBdry.SB25.Lgs_sub
import Submission.Work.FTS_StreamBdry.SB25.Lgs_le_zero_of_max
import Submission.Work.FTS_StreamBdry.SB25.exists_phi_ge_near_ends

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Sb5CmpCore` — the barrier comparison at a point (leaf E4c, core)

If `Lgs α u = 0` above the line `z = L`, `|u| ≤ Mb` there and `u` decays uniformly at infinity,
then `u z₁ θ₁ ≤ Mb (L/z₁)^k`: the Phragmén--Lindelöf comparison of `u` with the supersolution
`(Mb + ρ + δφ θ)(z/L)^{-k} + σ` of `Lgs`, via the maximum principle
`Lgs_le_zero_of_max` and the barrier computation `Lgs_barrier`.
-/

noncomputable section
open scoped Real Topology
open Set Filter MeasureTheory

namespace Work.FTS_StreamBdry.SB25

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The core comparison at a point -/

theorem sb5c_core_le (α k L Mb : ℝ) (φ : ℝ → ℝ) (Cφ : ℝ) (u : ℝ → ℝ → ℝ)
    (hα : 0 < α) (hαk : 0 < α * k) (hαk5 : α * k < 5) (hL : 0 < L) (hMb : 0 ≤ Mb)
    (hφ2 : ContDiffOn ℝ 2 φ (Ioo 0 (Real.pi / 2)))
    (hφ0 : ∀ θ ∈ Ioo 0 (Real.pi / 2), 0 ≤ φ θ)
    (hφe0 : ∀ B : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ θ : ℝ, 0 < θ → θ < ε → B ≤ φ θ)
    (hφeπ : ∀ B : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ θ : ℝ, Real.pi / 2 - ε < θ → θ < Real.pi / 2 → B ≤ φ θ)
    (hφA : ∀ θ ∈ Ioo 0 (Real.pi / 2),
      -Cφ ≤ -deriv (deriv φ) θ
        - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * deriv φ θ)
    (hu : ContDiffOn ℝ 2 (Function.uncurry u) Work.Construction.Qd)
    (hLgs0 : ∀ z θ, L < z → θ ∈ Ioo 0 (Real.pi / 2) → Lgs α u z θ = 0)
    (huMb : ∀ z θ, L ≤ z → θ ∈ Ioo 0 (Real.pi / 2) → |u z θ| ≤ Mb)
    (huDec : ∀ ε > 0, ∃ R, ∀ z θ, R ≤ z → θ ∈ Ioo 0 (Real.pi / 2) → |u z θ| ≤ ε)
    {z₁ θ₁ : ℝ} (hz₁ : L ≤ z₁) (hθ₁ : θ₁ ∈ Ioo 0 (Real.pi / 2)) :
    ∀ ρ σ : ℝ, 0 < ρ → 0 < σ → u z₁ θ₁ ≤ Mb * (L / z₁) ^ k + 2 * ρ + σ := by
  intro ρ σ hρ hσ
  have hz₁pos : 0 < z₁ := lt_of_lt_of_le hL hz₁
  have hk : 0 ≤ k := le_of_lt (by nlinarith [hα, hαk] : 0 < k)
  have hXpos : 0 < (L / z₁) ^ k := Real.rpow_pos_of_pos (div_pos hL hz₁pos) k
  have hXle : (L / z₁) ^ k ≤ 1 := by
    refine Real.rpow_le_one (le_of_lt (div_pos hL hz₁pos)) ?_ hk
    rw [div_le_one hz₁pos]
    exact hz₁
  have hcpos : 0 < α * k * (5 - α * k) := mul_pos hαk (by linarith)
  have hMpos : 0 < Mb + ρ := by linarith
  have hden : 0 < 2 * (|Cφ| + 1) := by positivity
  have hφθ₁ : 0 ≤ φ θ₁ := hφ0 θ₁ hθ₁
  have hq0 : 0 < (φ θ₁ + 1) * (L / z₁) ^ k := mul_pos (by linarith) hXpos
  set δ : ℝ := min ((α * k * (5 - α * k)) * (Mb + ρ) / (2 * (|Cφ| + 1)))
      (ρ / ((φ θ₁ + 1) * (L / z₁) ^ k)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (div_pos (mul_pos hcpos hMpos) hden) (div_pos hρ hq0)
  have hδle1 : δ ≤ (α * k * (5 - α * k)) * (Mb + ρ) / (2 * (|Cφ| + 1)) := by
    rw [hδdef]; exact min_le_left _ _
  have hδle2 : δ ≤ ρ / ((φ θ₁ + 1) * (L / z₁) ^ k) := by
    rw [hδdef]; exact min_le_right _ _
  have hδc : δ * |Cφ| ≤ (α * k * (5 - α * k)) * (Mb + ρ) / 2 := by
    have h1 : δ * |Cφ| ≤ ((α * k * (5 - α * k)) * (Mb + ρ) / (2 * (|Cφ| + 1))) * |Cφ| :=
      mul_le_mul_of_nonneg_right hδle1 (abs_nonneg Cφ)
    have h2 : ((α * k * (5 - α * k)) * (Mb + ρ) / (2 * (|Cφ| + 1))) * |Cφ|
        ≤ (α * k * (5 - α * k)) * (Mb + ρ) / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hden]
      nlinarith [abs_nonneg Cφ, mul_pos hcpos hMpos]
    linarith
  have hδρ : δ * φ θ₁ * (L / z₁) ^ k ≤ ρ := by
    have h0 : δ * ((φ θ₁ + 1) * (L / z₁) ^ k) ≤ ρ := by
      rw [le_div_iff₀ hq0] at hδle2
      linarith
    have h1 : δ * φ θ₁ * (L / z₁) ^ k ≤ δ * ((φ θ₁ + 1) * (L / z₁) ^ k) := by
      have h2 : φ θ₁ * (L / z₁) ^ k ≤ (φ θ₁ + 1) * (L / z₁) ^ k := by nlinarith [hXpos, hφθ₁]
      calc δ * φ θ₁ * (L / z₁) ^ k = δ * (φ θ₁ * (L / z₁) ^ k) := by ring
        _ ≤ δ * ((φ θ₁ + 1) * (L / z₁) ^ k) := mul_le_mul_of_nonneg_left h2 (le_of_lt hδpos)
    linarith
  -- the far-field radius
  obtain ⟨R₀, hR₀⟩ := huDec (σ / 2) (by linarith)
  have hR₀_le : R₀ ≤ max R₀ (max z₁ (L + 1)) := le_max_left _ _
  set R : ℝ := max R₀ (max z₁ (L + 1)) with hRdef
  have hRdec : ∀ z θ, R ≤ z → θ ∈ Ioo 0 (Real.pi / 2) → |u z θ| ≤ σ / 2 := by
    intro z θ hz hθ
    exact hR₀ z θ (le_trans hR₀_le hz) hθ
  have hz₁R : z₁ ≤ R := by
    rw [hRdef]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hL1R : L + 1 ≤ R := by
    rw [hRdef]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have hLR : L < R := by linarith
  have hRpos : 0 < R := by linarith
  have hRLpos : 0 < R / L := div_pos hRpos hL
  have hLRpos : 0 < L / R := div_pos hL hRpos
  obtain ⟨a₀, ha₀pos, ha₀lt, ha₀φ⟩ :=
    exists_phi_ge_near_ends φ ((Mb + 1) * (R / L) ^ k / δ) hφe0 hφeπ
  set a : ℝ := min a₀ (min θ₁ (Real.pi / 2 - θ₁)) / 2 with hadef
  have hminpos : 0 < min a₀ (min θ₁ (Real.pi / 2 - θ₁)) :=
    lt_min ha₀pos (lt_min hθ₁.1 (by linarith [hθ₁.2]))
  have hapos : 0 < a := by rw [hadef]; positivity
  have ha_lt_a₀ : a < a₀ := by
    rw [hadef]
    nlinarith [min_le_left a₀ (min θ₁ (Real.pi / 2 - θ₁)), hminpos]
  have ha_lt : a < min θ₁ (Real.pi / 2 - θ₁) := by
    rw [hadef]
    nlinarith [min_le_right a₀ (min θ₁ (Real.pi / 2 - θ₁)), hminpos]
  have haθ₁ : a < θ₁ := lt_of_lt_of_le ha_lt (min_le_left _ _)
  have haπθ₁ : a < Real.pi / 2 - θ₁ := lt_of_lt_of_le ha_lt (min_le_right _ _)
  have haπ : a < Real.pi / 2 - a := by linarith
  have haπ2 : a < Real.pi / 2 := by linarith
  -- the barrier and the comparison function
  set w : ℝ → ℝ → ℝ := fun z θ => (Mb + ρ + δ * φ θ) * (z / L) ^ (-k) + σ with hwdef
  set g : ℝ → ℝ → ℝ := fun z θ => u z θ - w z θ with hgdef
  have hbox : Set.Icc L R ×ˢ Set.Icc a (Real.pi / 2 - a) ⊆ Work.Construction.Qd := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
    rw [Work.Construction.Qd]
    exact Set.mem_prod.mpr
      ⟨lt_of_lt_of_le hL hp1.1,
        ⟨lt_of_lt_of_le hapos hp2.1, lt_of_le_of_lt hp2.2 (by linarith [haπ])⟩⟩
  have hwAt : ∀ {z θ : ℝ}, 0 < z → θ ∈ Ioo 0 (Real.pi / 2) →
      ContDiffAt ℝ 2 (Function.uncurry w) (z, θ) := by
    intro z θ hz hθ
    rw [hwdef]
    exact sb5c_barrier_contDiffAt k L (Mb + ρ) δ σ φ hφ2 (ne_of_gt hL) hz hθ
  have hcont : ContinuousOn (Function.uncurry g) (Set.Icc L R ×ˢ Set.Icc a (Real.pi / 2 - a)) := by
    have hu' : ContinuousOn (Function.uncurry u) (Set.Icc L R ×ˢ Set.Icc a (Real.pi / 2 - a)) :=
      hu.continuousOn.mono hbox
    have hw' : ContinuousOn (Function.uncurry w) (Set.Icc L R ×ˢ Set.Icc a (Real.pi / 2 - a)) := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
      exact ((hwAt (lt_of_lt_of_le hL hp1.1)
        ⟨lt_of_lt_of_le hapos hp2.1, lt_of_le_of_lt hp2.2 (by linarith [haπ])⟩).continuousAt).continuousWithinAt
    have hsub : Function.uncurry g = Function.uncurry u - Function.uncurry w := by
      rw [hgdef]; funext p; rfl
    rw [hsub]
    exact hu'.sub hw'
  have hbd' : ∀ z θ, z ∈ Set.Icc L R → θ ∈ Set.Icc a (Real.pi / 2 - a) →
      (z = L ∨ z = R ∨ θ = a ∨ θ = Real.pi / 2 - a) → g z θ < 0 := by
    intro z θ hz hθ hb
    have hθmem : θ ∈ Ioo 0 (Real.pi / 2) :=
      ⟨lt_of_lt_of_le hapos hθ.1, lt_of_le_of_lt hθ.2 (by linarith [haπ])⟩
    have hzpos : 0 < z := lt_of_lt_of_le hL hz.1
    have hφθ : 0 ≤ φ θ := hφ0 θ hθmem
    rw [hgdef]
    simp only [Pi.sub_apply]
    rcases hb with h | h | h | h
    · -- z = L
      rw [h]
      have huz : u L θ ≤ Mb := le_trans (le_abs_self _) (huMb L θ le_rfl hθmem)
      have h1 : (L / L) ^ (-k) = 1 := by rw [div_self (ne_of_gt hL), Real.one_rpow]
      have h2 : 0 ≤ δ * φ θ := mul_nonneg (le_of_lt hδpos) hφθ
      have h3 : w L θ = (Mb + ρ + δ * φ θ) + σ := by rw [hwdef]; simp only [h1, mul_one]
      rw [h3]
      linarith [hρ, hσ, h2]
    · -- z = R
      rw [h]
      have huz : u R θ ≤ σ / 2 := le_trans (le_abs_self _) (hRdec R θ le_rfl hθmem)
      have h1 : 0 < (R / L) ^ (-k) := Real.rpow_pos_of_pos hRLpos _
      have h2 : 0 < Mb + ρ + δ * φ θ := by nlinarith [hδpos, hφθ, hMpos]
      have h3 : σ ≤ w R θ := by
        rw [hwdef]
        exact le_add_of_nonneg_left (le_of_lt (mul_pos h2 h1))
      linarith [hσ]
    · -- θ = a
      rw [h]
      have huz : u z a ≤ Mb := le_trans (le_abs_self _) (huMb z a hz.1 ⟨hapos, haπ2⟩)
      have hφa : (Mb + 1) * (R / L) ^ k / δ ≤ φ a :=
        ha₀φ a ⟨hapos, haπ2⟩ (Or.inl (by linarith [ha_lt_a₀]))
      have hδφa : (Mb + 1) * (R / L) ^ k ≤ δ * φ a := by
        rw [div_le_iff₀ hδpos] at hφa
        linarith [hφa]
      have hφa0 : 0 ≤ φ a := hφ0 a ⟨hapos, haπ2⟩
      have hineq := sb5c_endpoint_ineq (Mb := Mb) (ρ := ρ) (δ := δ) (φa := φ a) (k := k)
        (z := z) (R := R) (L := L) hδφa hL hRpos hzpos hz.2 hk (le_of_lt hρ) hMb hδpos hφa0
      have h3 : (Mb + ρ + δ * φ a) * (L / z) ^ k ≤ w z a := by
        rw [hwdef]
        simp only
        rw [sb5c_rpow_neg_div_eq k L z hL hzpos]
        linarith [hσ]
      linarith
    · -- θ = π/2 - a
      rw [h]
      have hπmem : Real.pi / 2 - a ∈ Ioo 0 (Real.pi / 2) :=
        ⟨by linarith [haπ], by linarith [haπ]⟩
      have huz : u z (Real.pi / 2 - a) ≤ Mb :=
        le_trans (le_abs_self _) (huMb z _ hz.1 hπmem)
      have hφa : (Mb + 1) * (R / L) ^ k / δ ≤ φ (Real.pi / 2 - a) :=
        ha₀φ (Real.pi / 2 - a) hπmem (Or.inr (by linarith [ha_lt_a₀]))
      have hδφa : (Mb + 1) * (R / L) ^ k ≤ δ * φ (Real.pi / 2 - a) := by
        rw [div_le_iff₀ hδpos] at hφa
        linarith [hφa]
      have hφa0 : 0 ≤ φ (Real.pi / 2 - a) := hφ0 _ hπmem
      have hineq := sb5c_endpoint_ineq (Mb := Mb) (ρ := ρ) (δ := δ) (φa := φ (Real.pi / 2 - a))
        (k := k) (z := z) (R := R) (L := L) hδφa hL hRpos hzpos hz.2 hk (le_of_lt hρ) hMb hδpos hφa0
      have h3 : (Mb + ρ + δ * φ (Real.pi / 2 - a)) * (L / z) ^ k ≤ w z (Real.pi / 2 - a) := by
        rw [hwdef]
        simp only
        rw [sb5c_rpow_neg_div_eq k L z hL hzpos]
        linarith [hσ]
      linarith
  have hC2 : ∀ z θ, z ∈ Set.Ioo L R → θ ∈ Set.Ioo a (Real.pi / 2 - a) →
      ContDiffAt ℝ 2 (Function.uncurry g) (z, θ) := by
    intro z θ hz hθ
    have hzpos : 0 < z := lt_trans hL hz.1
    have hθmem : θ ∈ Ioo 0 (Real.pi / 2) :=
      ⟨lt_trans hapos hθ.1, lt_trans hθ.2 (by linarith [haπ])⟩
    have hQd : (z, θ) ∈ Work.Construction.Qd := by
      rw [Work.Construction.Qd]; exact Set.mem_prod.mpr ⟨hzpos, hθmem⟩
    have hu2 : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ) :=
      hu.contDiffAt (sb5c_Qd_mem_nhds hQd)
    have hw2' := hwAt hzpos hθmem
    rw [hgdef]
    exact hu2.sub hw2'
  have hneg : ∀ z θ, z ∈ Set.Ioo L R → θ ∈ Set.Ioo a (Real.pi / 2 - a) →
      Lgs α g z θ < 0 := by
    intro z θ hz hθ
    have hzpos : 0 < z := lt_trans hL hz.1
    have hθmem : θ ∈ Ioo 0 (Real.pi / 2) :=
      ⟨lt_trans hapos hθ.1, lt_trans hθ.2 (by linarith [haπ])⟩
    have hQd : (z, θ) ∈ Work.Construction.Qd := by
      rw [Work.Construction.Qd]; exact Set.mem_prod.mpr ⟨hzpos, hθmem⟩
    have hu2 : ContDiffAt ℝ 2 (Function.uncurry u) (z, θ) :=
      hu.contDiffAt (sb5c_Qd_mem_nhds hQd)
    have hw2' := hwAt hzpos hθmem
    have hsub := Lgs_sub α hu2 hw2'
    have hLb := Lgs_barrier α k L (Mb + ρ) δ σ φ hφ2 hL z θ hQd
    have hLw : Lgs α w z θ
        = (z / L) ^ (-k) * (α * k * (5 - α * k) * (Mb + ρ + δ * φ θ)
            + δ * (-deriv (deriv φ) θ
              - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * deriv φ θ)) := by
      rw [hwdef]
      exact hLb
    have hzp : 0 < (z / L) ^ (-k) := Real.rpow_pos_of_pos (div_pos hzpos hL) _
    have hφθ : 0 ≤ φ θ := hφ0 θ hθmem
    have hA := hφA θ hθmem
    have hbr : 0 < α * k * (5 - α * k) * (Mb + ρ + δ * φ θ)
        + δ * (-deriv (deriv φ) θ
              - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * deriv φ θ) := by
      have hb1 : α * k * (5 - α * k) * (Mb + ρ) ≤ α * k * (5 - α * k) * (Mb + ρ + δ * φ θ) := by
        refine mul_le_mul_of_nonneg_left ?_ (le_of_lt hcpos)
        linarith [mul_nonneg (le_of_lt hδpos) hφθ]
      have hb2 : -(δ * |Cφ|) ≤ δ * (-deriv (deriv φ) θ
              - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * deriv φ θ) := by
        have h1 : δ * (-Cφ) ≤ δ * (-deriv (deriv φ) θ
              - (4 * Real.cos (2 * θ) / Real.sin (2 * θ) - Real.tan θ) * deriv φ θ) :=
          mul_le_mul_of_nonneg_left hA (le_of_lt hδpos)
        have h2 : δ * (-Cφ) ≥ -(δ * |Cφ|) := by
          have : -|Cφ| ≤ -Cφ := neg_le_neg_iff.mpr (le_abs_self _)
          nlinarith [mul_le_mul_of_nonneg_left this (le_of_lt hδpos)]
        linarith
      have hb3 : (α * k * (5 - α * k)) * (Mb + ρ) / 2 > 0 :=
        div_pos (mul_pos hcpos hMpos) (by norm_num)
      linarith [hb1, hb2, hδc]
    have hLwpos : 0 < Lgs α w z θ := by rw [hLw]; exact mul_pos hzp hbr
    have hLgsu : Lgs α u z θ = 0 := hLgs0 z θ hz.1 hθmem
    rw [hgdef]
    rw [hsub]
    linarith
  have ha1 : Real.pi / 2 - a < Real.pi / 2 := by linarith [haπ]
  have hmain := Lgs_le_zero_of_max α L R a (Real.pi / 2 - a) g hLR haπ hL hapos ha1
    hcont hbd' hC2 hneg
  have hmem : (z₁, θ₁) ∈ Set.Icc L R ×ˢ Set.Icc a (Real.pi / 2 - a) :=
    Set.mem_prod.mpr ⟨⟨hz₁, hz₁R⟩, ⟨le_of_lt haθ₁, by linarith [haπθ₁]⟩⟩
  have hg0 : g z₁ θ₁ ≤ 0 := hmain z₁ θ₁ hmem.1 hmem.2
  have huw : u z₁ θ₁ ≤ (Mb + ρ + δ * φ θ₁) * (L / z₁) ^ k + σ := by
    rw [hgdef] at hg0
    simp only [Pi.sub_apply] at hg0
    rw [hwdef] at hg0
    simp only at hg0
    rw [sb5c_rpow_neg_div_eq k L z₁ hL hz₁pos] at hg0
    linarith
  have h2ρ : ρ * (L / z₁) ^ k ≤ ρ := by nlinarith [hXle, le_of_lt hρ]
  calc u z₁ θ₁ ≤ (Mb + ρ + δ * φ θ₁) * (L / z₁) ^ k + σ := huw
    _ = Mb * (L / z₁) ^ k + δ * φ θ₁ * (L / z₁) ^ k + ρ * (L / z₁) ^ k + σ := by ring
    _ ≤ Mb * (L / z₁) ^ k + 2 * ρ + σ := by linarith [hδρ, h2ρ]


end Work.FTS_StreamBdry.SB25
