import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.Stability.holderWith_of_dist_le
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.FireFix.Prime.physVort_support
import Submission.Work.FTS.FireFix.Prime.physVort_bound
import Submission.Work.FTS.FireFix.Prime.PhysVortHolderSlice
import Submission.Work.FTS.FireFix.Prime.physVort_holder_time
import Submission.Work.FTS.FireFix.Prime.physVort_hasDerivAt_and_bound
import Submission.Work.FTS.FireFix.Prime.physVort_timeDeriv_aesm
import Submission.Work.FTS.FireFix.Prime.profFullHolder
import Submission.Work.FTS.FireFix.Prime.profFullBounds
import Submission.Work.FTS.FireFix.Prime.dzProfFullUniform
import Submission.Work.FTS.FireFix.Prime.dzProfFullZero
import Submission.Work.FTS.FireFix.Prime.dtgZero
import Submission.Work.FTS.FireFix.Prime.clockBounds
import Submission.Work.FTS.FireFix.Prime.clockLipschitz
import Submission.Work.FTS.RegPkgGal.Basic
import Submission.Work.FTS.FireFix.Prime.PvbClock

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open FiniteTimeSingularity Set Filter Topology

open scoped Topology

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace Work.FTS.FireFix.Prime

open Work.FTS.Regularity Work.FTS.RegPkgGal

theorem pvb_vortDt_holder {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg' α S A B g) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ x : R3, ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      ‖vortDt α A B g x τ - vortDt α A B g x τ'‖ ≤ N * |τ - τ'| ^ α := by
  obtain ⟨a₀, a₁, ha₀, hAb⟩ := h.hAb
  obtain ⟨b₀, b₁, hb₀, hBb⟩ := h.hBb
  obtain ⟨Kb, hKb0, hKb⟩ := clockLipschitz h
  obtain ⟨CA, hCA0, hAic, hAhc, hBhc⟩ := pvb_clockData h
  obtain ⟨MA, hMA0, hMA⟩ := clockBounds h
  obtain ⟨Np, hNp0, hNph⟩ := profFullHolder h
  obtain ⟨Mp, hMp0, hMp⟩ := profFullBounds h
  obtain ⟨Nd, hNd⟩ := h.hgdoth
  obtain ⟨L₀, hL₀pos, hL₀supp⟩ := h.hsupp
  obtain ⟨Lτ, hLτpos, hLτ⟩ := dtgZero h
  obtain ⟨Lz, hLzpos, hLz⟩ := dzProfFullZero h
  have hb₁0 : 0 < b₁ := by
    have h0 : (0 : ℝ) ∈ Set.Icc 0 S := ⟨le_rfl, h.hS.le⟩
    linarith [(hBb 0 h0).1, (hBb 0 h0).2]
  set Lb : ℝ := max L₀ (max Lτ Lz) + 1 with hLbdef
  have hLb_gt₀ : L₀ < Lb := by
    rw [hLbdef]
    have h1 : L₀ ≤ max L₀ (max Lτ Lz) := le_max_left _ _
    linarith
  have hLb_gtτ : Lτ < Lb := by
    rw [hLbdef]
    have h1 : Lτ ≤ max Lτ Lz := le_max_left _ _
    have h2 : max Lτ Lz ≤ max L₀ (max Lτ Lz) := le_max_right _ _
    linarith
  have hLb_gtz : Lz < Lb := by
    rw [hLbdef]
    have h1 : Lz ≤ max Lτ Lz := le_max_right _ _
    have h2 : max Lτ Lz ≤ max L₀ (max Lτ Lz) := le_max_right _ _
    linarith
  have hLb0 : 0 < Lb := lt_trans hL₀pos hLb_gt₀
  set κ : ℝ := Lb * b₁ * Kb / b₀ ^ 2 with hκdef
  have hκ0 : 0 ≤ κ := by
    rw [hκdef]
    exact div_nonneg (mul_nonneg (mul_nonneg hLb0.le hb₁0.le) hKb0) (by positivity)
  set Rz : ℝ := Lb * b₁ / b₀ with hRzdef
  have hRz0 : 0 ≤ Rz := by
    rw [hRzdef]
    exact div_nonneg (mul_nonneg hLb0.le hb₁0.le) hb₀.le
  obtain ⟨hsplitR, ⟨M1, hM10, hM1⟩, ⟨N1, hN10, hN1⟩⟩ := dzProfFullUniform h Rz hRz0
  set Ka : ℝ := S ^ (1 - α) with hKadef
  have hKa0 : 0 ≤ Ka := by rw [hKadef]; exact Real.rpow_nonneg h.hS.le _
  set κa : ℝ := κ * Ka with hκadef
  have hκa0 : 0 ≤ κa := by rw [hκadef]; positivity
  set Kz : ℝ := (κ + 1) ^ α with hKzdef
  have hKz0 : 0 ≤ Kz := by rw [hKzdef]; exact Real.rpow_nonneg (by linarith) _
  have hNd0 : 0 ≤ Nd := hNd.1
  set ND : ℝ := Rz * M1 * CA + MA * (Rz * N1 * Kz + M1 * κa) + Nd * Kz with hNDdef
  set MD : ℝ := Rz * M1 * MA + Nd with hMDdef
  set NP : ℝ := Np * Kz with hNPdef
  set NN : ℝ := MA * ND + CA * MD + MA * NP + CA * Mp with hNNdef
  have hND0 : 0 ≤ ND := by
    rw [hNDdef]
    have h1 : 0 ≤ Rz * M1 * CA := by positivity
    have h2 : 0 ≤ MA * (Rz * N1 * Kz + M1 * κa) := by positivity
    have h3 : 0 ≤ Nd * Kz := by positivity
    linarith
  have hMD0 : 0 ≤ MD := by
    rw [hMDdef]
    have h1 : 0 ≤ Rz * M1 * MA := by positivity
    linarith
  have hNP0 : 0 ≤ NP := by rw [hNPdef]; positivity
  have hNN0 : 0 ≤ NN := by
    rw [hNNdef]
    have h1 : 0 ≤ MA * ND := by positivity
    have h2 : 0 ≤ CA * MD := by positivity
    have h3 : 0 ≤ MA * NP := by positivity
    have h4 : 0 ≤ CA * Mp := by positivity
    linarith
  refine ⟨NN, hNN0, ?_⟩
  intro x τ hτ τ' hτ'
  set ρ : ℝ := Work.Cyl.rho x with hρdef
  set θ : ℝ := Work.Cyl.theta x with hθdef
  set e : R3 := Work.Cyl.eTheta x with hedef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; exact Work.Cyl.rho_nonneg x
  have hφI : |θ| ∈ Work.Spaces.Iθ := by rw [hθdef]; exact abs_theta_mem_Iθ x
  have he1 : ‖e‖ ≤ 1 := by rw [hedef]; exact norm_eTheta_le_one x
  have hvort : ∀ s : ℝ, vortDt α A B g x s
      = (A s)⁻¹ • (dProfOdd α B g ρ θ s • e)
        + (-(deriv A s) / (A s) ^ 2) • (profOdd α g (ρ ^ pExp α / B s) θ s • e) := by
    intro s
    rw [vortDt]
  rw [hvort τ, hvort τ']
  by_cases hfar : Lb * b₁ < ρ ^ pExp α
  · -- FAR: outside the support everything vanishes
    have hZnn : ∀ s ∈ Set.Icc 0 S, 0 ≤ ρ ^ pExp α / B s :=
      fun s hs => div_nonneg (Real.rpow_nonneg hρ0 _) (h.hB s hs).le
    have hZfar : ∀ s ∈ Set.Icc 0 S, Lb ≤ ρ ^ pExp α / B s := by
      intro s hs
      have hBs : 0 < B s := h.hB s hs
      rw [le_div_iff₀ hBs]
      calc Lb * B s ≤ Lb * b₁ := mul_le_mul_of_nonneg_left (hBb s hs).2 hLb0.le
        _ ≤ ρ ^ pExp α := hfar.le
    have hD0 : ∀ s ∈ Set.Icc 0 S, dProfOdd α B g ρ θ s = 0 := by
      intro s hs
      have hpz0 : pzProf α g (ρ ^ pExp α / B s) |θ| s = 0 := by
        rw [pvb_pzProf_eq_deriv h (hZnn s hs) hφI hs]
        exact hLz _ |θ| s (lt_of_lt_of_le hLb_gtz (hZfar s hs)) hφI hs
      have hw0 : deriv (fun t => g (ρ ^ pExp α / B s) |θ| t) s = 0 :=
        hLτ _ |θ| s (lt_of_lt_of_le hLb_gtτ (hZfar s hs)) hφI hs
      rw [pvb_dProfOdd_eq (α := α) (B := B) (g := g) (ρ := ρ) (θ := θ) (τ := s)
        (ne_of_gt (h.hB s hs)), hpz0, hw0]
      ring
    have hP0 : ∀ s ∈ Set.Icc 0 S, profOdd α g (ρ ^ pExp α / B s) θ s = 0 := by
      intro s hs
      exact pvb_profOdd_eq_zero (hL₀supp s hs _ _ (le_trans hLb_gt₀.le (hZfar s hs)))
    rw [hD0 τ hτ, hP0 τ hτ, hD0 τ' hτ', hP0 τ' hτ']
    simp only [zero_smul, smul_zero, add_zero, sub_self, norm_zero]
    exact mul_nonneg hNN0 (Real.rpow_nonneg (abs_nonneg _) α)
  · -- NEAR: inside the support radius
    have hρp : ρ ^ pExp α ≤ Lb * b₁ := not_lt.mp hfar
    have hZnn : ∀ s ∈ Set.Icc 0 S, 0 ≤ ρ ^ pExp α / B s :=
      fun s hs => div_nonneg (Real.rpow_nonneg hρ0 _) (h.hB s hs).le
    have hZR : ∀ s ∈ Set.Icc 0 S, ρ ^ pExp α / B s ≤ Rz := by
      intro s hs
      have hBs : 0 < B s := h.hB s hs
      rw [hRzdef, div_le_iff₀ hBs]
      calc ρ ^ pExp α ≤ Lb * b₁ := hρp
        _ = Lb * b₁ / b₀ * b₀ := by field_simp
        _ ≤ Lb * b₁ / b₀ * B s := mul_le_mul_of_nonneg_left (hBb s hs).1 (by positivity)
    have hZlip : |ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'| ≤ κ * |τ - τ'| := by
      have hBτ : 0 < B τ := h.hB τ hτ
      have hBτ' : 0 < B τ' := h.hB τ' hτ'
      have hkey : ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'
          = ρ ^ pExp α * ((B τ' - B τ) / (B τ * B τ')) := by
        field_simp
      have hnum : |B τ' - B τ| ≤ Kb * |τ - τ'| := by
        rw [abs_sub_comm]; exact hKb τ hτ τ' hτ'
      have hden : b₀ ^ 2 ≤ B τ * B τ' := by
        have h1 := (hBb τ hτ).1
        have h2 := (hBb τ' hτ').1
        nlinarith [mul_le_mul h1 h2 hb₀.le hBτ.le]
      rw [hkey, abs_mul, abs_of_nonneg (Real.rpow_nonneg hρ0 _), abs_div,
        abs_of_pos (mul_pos hBτ hBτ')]
      have hstep : |B τ' - B τ| / (B τ * B τ') ≤ (Kb / b₀ ^ 2) * |τ - τ'| := by
        calc |B τ' - B τ| / (B τ * B τ') ≤ Kb * |τ - τ'| / (B τ * B τ') :=
              div_le_div_of_nonneg_right hnum (le_of_lt (mul_pos hBτ hBτ'))
          _ ≤ Kb * |τ - τ'| / b₀ ^ 2 :=
              div_le_div_of_nonneg_left (mul_nonneg hKb0 (abs_nonneg _)) (by positivity) hden
          _ = (Kb / b₀ ^ 2) * |τ - τ'| := by ring
      calc ρ ^ pExp α * (|B τ' - B τ| / (B τ * B τ'))
          ≤ ρ ^ pExp α * ((Kb / b₀ ^ 2) * |τ - τ'|) :=
            mul_le_mul_of_nonneg_left hstep (Real.rpow_nonneg hρ0 _)
        _ ≤ (Lb * b₁) * ((Kb / b₀ ^ 2) * |τ - τ'|) :=
            mul_le_mul_of_nonneg_right hρp (by positivity)
        _ = κ * |τ - τ'| := by rw [hκdef]; ring
    have hKa1 : |τ - τ'| ≤ Ka * |τ - τ'| ^ α := by
      have h1 : |τ - τ'| ≤ S := by
        rw [abs_sub_le_iff]
        constructor <;> linarith [hτ.1, hτ.2, hτ'.1, hτ'.2]
      exact pvb_self_le_rpow (abs_nonneg _) h1 h.hα (le_trans h.hα13 (by norm_num))
    have hra : ∀ {a b : ℝ}, 0 ≤ a → 0 ≤ b → a ≤ κ * |τ - τ'| → b ≤ |τ - τ'| →
        (a + b) ^ α ≤ Kz * |τ - τ'| ^ α := by
      intro a b ha hb ha' hb'
      have hd : 0 ≤ |τ - τ'| := abs_nonneg _
      have h1 : a + b ≤ (κ + 1) * |τ - τ'| := by nlinarith
      have h2 : 0 ≤ a + b := by linarith
      have hK1 : 0 ≤ κ + 1 := by linarith
      have h4 : ((κ + 1) * |τ - τ'|) ^ α = (κ + 1) ^ α * |τ - τ'| ^ α :=
        Real.mul_rpow hK1 hd
      calc (a + b) ^ α ≤ ((κ + 1) * |τ - τ'|) ^ α := Real.rpow_le_rpow h2 h1 h.hα.le
        _ = (κ + 1) ^ α * |τ - τ'| ^ α := h4
        _ = Kz * |τ - τ'| ^ α := by rw [hKzdef]
    -- the profile part
    have hPh : |profOdd α g (ρ ^ pExp α / B τ) θ τ - profOdd α g (ρ ^ pExp α / B τ') θ τ'|
        ≤ NP * |τ - τ'| ^ α := by
      rw [pvb_profOdd_sub]
      have h1 := hNph (ρ ^ pExp α / B τ) (ρ ^ pExp α / B τ') |θ| τ τ'
        (hZnn τ hτ) (hZnn τ' hτ') hφI hτ hτ'
      have h2 : (|ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'| + |τ - τ'|) ^ α
          ≤ Kz * |τ - τ'| ^ α := hra (abs_nonneg _) (abs_nonneg _) hZlip le_rfl
      calc |profFull α g (ρ ^ pExp α / B τ) |θ| τ - profFull α g (ρ ^ pExp α / B τ') |θ| τ'|
          ≤ Np * (|ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'| + |τ - τ'|) ^ α := h1
        _ ≤ Np * (Kz * |τ - τ'| ^ α) := mul_le_mul_of_nonneg_left h2 hNp0
        _ = NP * |τ - τ'| ^ α := by rw [hNPdef]; ring
    have hPb : |profOdd α g (ρ ^ pExp α / B τ') θ τ'| ≤ Mp := by
      rw [pvb_profOdd_abs_eq]
      exact hMp τ' hτ' _ _ (hZnn τ' hτ') hφI
    -- the `z`-derivative of the profile
    have hpzh : |pzProf α g (ρ ^ pExp α / B τ) |θ| τ
        - pzProf α g (ρ ^ pExp α / B τ') |θ| τ'| ≤ N1 * Kz * |τ - τ'| ^ α := by
      rw [pvb_pzProf_eq_deriv h (hZnn τ hτ) hφI hτ,
        pvb_pzProf_eq_deriv h (hZnn τ' hτ') hφI hτ']
      have h1 := hN1 (ρ ^ pExp α / B τ) (ρ ^ pExp α / B τ') |θ| τ τ'
        (hZnn τ hτ) (hZR τ hτ) (hZnn τ' hτ') (hZR τ' hτ') hφI hτ hτ'
      have h2 : (|ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'| + |τ - τ'|) ^ α
          ≤ Kz * |τ - τ'| ^ α := hra (abs_nonneg _) (abs_nonneg _) hZlip le_rfl
      calc |deriv (fun z' => profFull α g z' |θ| τ) (ρ ^ pExp α / B τ)
            - deriv (fun z' => profFull α g z' |θ| τ') (ρ ^ pExp α / B τ')|
          ≤ N1 * (|ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'| + |τ - τ'|) ^ α := h1
        _ ≤ N1 * (Kz * |τ - τ'| ^ α) := mul_le_mul_of_nonneg_left h2 hN10
        _ = N1 * Kz * |τ - τ'| ^ α := by ring
    have hpzb : |pzProf α g (ρ ^ pExp α / B τ') |θ| τ'| ≤ M1 := by
      rw [pvb_pzProf_eq_deriv h (hZnn τ' hτ') hφI hτ']
      exact hM1 (ρ ^ pExp α / B τ') |θ| τ' (hZnn τ' hτ') (hZR τ' hτ') hφI hτ'
    have hpzbτ : |pzProf α g (ρ ^ pExp α / B τ) |θ| τ| ≤ M1 := by
      rw [pvb_pzProf_eq_deriv h (hZnn τ hτ) hφI hτ]
      exact hM1 (ρ ^ pExp α / B τ) |θ| τ (hZnn τ hτ) (hZR τ hτ) hφI hτ
    -- `U = Z · ∂_zF`
    have hUb : |(ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ'| ≤ Rz * M1 := by
      rw [abs_mul, abs_of_nonneg (hZnn τ' hτ')]
      exact mul_le_mul (hZR τ' hτ') hpzb (abs_nonneg _) hRz0
    have hUbτ : |(ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ| ≤ Rz * M1 := by
      rw [abs_mul, abs_of_nonneg (hZnn τ hτ)]
      exact mul_le_mul (hZR τ hτ) hpzbτ (abs_nonneg _) hRz0
    have hUh : |(ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ
        - (ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ'|
        ≤ (Rz * N1 * Kz + M1 * κa) * |τ - τ'| ^ α := by
      have hsplit : (ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ
          - (ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ'
          = (ρ ^ pExp α / B τ) * (pzProf α g (ρ ^ pExp α / B τ) |θ| τ
              - pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
            + (ρ ^ pExp α / B τ - ρ ^ pExp α / B τ')
              * pzProf α g (ρ ^ pExp α / B τ') |θ| τ' := by ring
      rw [hsplit]
      have h1 : |(ρ ^ pExp α / B τ) * (pzProf α g (ρ ^ pExp α / B τ) |θ| τ
            - pzProf α g (ρ ^ pExp α / B τ') |θ| τ')| ≤ Rz * (N1 * Kz * |τ - τ'| ^ α) := by
        rw [abs_mul, abs_of_nonneg (hZnn τ hτ)]
        exact mul_le_mul (hZR τ hτ) hpzh (abs_nonneg _) hRz0
      have h2 : |(ρ ^ pExp α / B τ - ρ ^ pExp α / B τ')
            * pzProf α g (ρ ^ pExp α / B τ') |θ| τ'| ≤ (κa * M1) * |τ - τ'| ^ α := by
        rw [abs_mul]
        have hb : |ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'|
            * |pzProf α g (ρ ^ pExp α / B τ') |θ| τ'| ≤ (κ * |τ - τ'|) * M1 :=
          mul_le_mul hZlip hpzb (abs_nonneg _) (mul_nonneg hκ0 (abs_nonneg _))
        calc |ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'|
              * |pzProf α g (ρ ^ pExp α / B τ') |θ| τ'| ≤ (κ * |τ - τ'|) * M1 := hb
          _ = (κ * M1) * |τ - τ'| := by ring
          _ ≤ (κ * M1) * (Ka * |τ - τ'| ^ α) :=
              mul_le_mul_of_nonneg_left hKa1 (mul_nonneg hκ0 hM10)
          _ = (κa * M1) * |τ - τ'| ^ α := by rw [hκadef]; ring
      calc |(ρ ^ pExp α / B τ) * (pzProf α g (ρ ^ pExp α / B τ) |θ| τ
              - pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
            + (ρ ^ pExp α / B τ - ρ ^ pExp α / B τ')
              * pzProf α g (ρ ^ pExp α / B τ') |θ| τ'|
          ≤ |(ρ ^ pExp α / B τ) * (pzProf α g (ρ ^ pExp α / B τ) |θ| τ
              - pzProf α g (ρ ^ pExp α / B τ') |θ| τ')|
            + |(ρ ^ pExp α / B τ - ρ ^ pExp α / B τ')
              * pzProf α g (ρ ^ pExp α / B τ') |θ| τ'| := abs_add_le _ _
        _ ≤ Rz * (N1 * Kz * |τ - τ'| ^ α) + (κa * M1) * |τ - τ'| ^ α := add_le_add h1 h2
        _ = (Rz * N1 * Kz + M1 * κa) * |τ - τ'| ^ α := by ring
    -- `W = ∂_τ g`
    have hWh : |deriv (fun t => g (ρ ^ pExp α / B τ) |θ| t) τ
        - deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ'| ≤ Nd * Kz * |τ - τ'| ^ α := by
      have h1 := hNd.2.2 (ρ ^ pExp α / B τ) (ρ ^ pExp α / B τ') |θ| |θ| τ τ'
        (hZnn τ hτ) (hZnn τ' hτ') hφI hφI hτ hτ'
      have h1' : |deriv (fun t => g (ρ ^ pExp α / B τ) |θ| t) τ
          - deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ'|
          ≤ Nd * (|ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'| + |τ - τ'|) ^ α := by
        simpa only [sub_self, abs_zero, add_zero] using h1
      have h2 : (|ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'| + |τ - τ'|) ^ α
          ≤ Kz * |τ - τ'| ^ α := hra (abs_nonneg _) (abs_nonneg _) hZlip le_rfl
      calc |deriv (fun t => g (ρ ^ pExp α / B τ) |θ| t) τ
            - deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ'|
          ≤ Nd * (|ρ ^ pExp α / B τ - ρ ^ pExp α / B τ'| + |τ - τ'|) ^ α := h1'
        _ ≤ Nd * (Kz * |τ - τ'| ^ α) := mul_le_mul_of_nonneg_left h2 hNd0
        _ = Nd * Kz * |τ - τ'| ^ α := by ring
    have hWb : |deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ'| ≤ Nd :=
      hNd.abs_le (hZnn τ' hτ') hφI hτ'
    -- the clock factors
    have hVb : |deriv B τ' / B τ'| ≤ MA := (hMA τ' hτ').2.2.2
    have hVh : |deriv B τ / B τ - deriv B τ' / B τ'| ≤ CA * |τ - τ'| ^ α := hBhc τ hτ τ' hτ'
    -- the assembled derivative `D`
    have hDh : |dProfOdd α B g ρ θ τ - dProfOdd α B g ρ θ τ'| ≤ ND * |τ - τ'| ^ α := by
      rw [pvb_dProfOdd_eq (α := α) (B := B) (g := g) (ρ := ρ) (θ := θ) (τ := τ)
            (ne_of_gt (h.hB τ hτ)),
          pvb_dProfOdd_eq (α := α) (B := B) (g := g) (ρ := ρ) (θ := θ) (τ := τ')
            (ne_of_gt (h.hB τ' hτ'))]
      have hs1 : |(if 0 ≤ θ then (1 : ℝ) else -1)| = 1 := by split_ifs <;> norm_num
      rw [← mul_sub, abs_mul, hs1, one_mul]
      have hsplit : (-((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
              * (deriv B τ / B τ) + deriv (fun t => g (ρ ^ pExp α / B τ) |θ| t) τ)
          - (-((ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
              * (deriv B τ' / B τ') + deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ')
          = -(((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
                * (deriv B τ / B τ)
              - ((ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
                * (deriv B τ' / B τ'))
            + (deriv (fun t => g (ρ ^ pExp α / B τ) |θ| t) τ
              - deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ') := by ring
      rw [hsplit]
      have hUV : |((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
            * (deriv B τ / B τ)
          - ((ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
            * (deriv B τ' / B τ')| ≤ (Rz * M1 * CA + MA * (Rz * N1 * Kz + M1 * κa))
              * |τ - τ'| ^ α := by
        have hsp : ((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
              * (deriv B τ / B τ)
            - ((ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
              * (deriv B τ' / B τ')
            = ((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
                * (deriv B τ / B τ - deriv B τ' / B τ')
              + (deriv B τ' / B τ')
                * ((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ
                  - (ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ') := by ring
        rw [hsp]
        have h1 : |((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
              * (deriv B τ / B τ - deriv B τ' / B τ')|
            ≤ (Rz * M1) * (CA * |τ - τ'| ^ α) := by
          rw [abs_mul]
          exact mul_le_mul hUbτ hVh (abs_nonneg _) (mul_nonneg hRz0 hM10)
        have h2 : |(deriv B τ' / B τ')
              * ((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ
                - (ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')|
            ≤ MA * ((Rz * N1 * Kz + M1 * κa) * |τ - τ'| ^ α) := by
          rw [abs_mul]
          exact mul_le_mul hVb hUh (abs_nonneg _) hMA0
        calc |((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
                * (deriv B τ / B τ - deriv B τ' / B τ')
              + (deriv B τ' / B τ')
                * ((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ
                  - (ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')|
            ≤ (Rz * M1) * (CA * |τ - τ'| ^ α)
              + MA * ((Rz * N1 * Kz + M1 * κa) * |τ - τ'| ^ α) :=
              le_trans (abs_add_le _ _) (add_le_add h1 h2)
          _ = (Rz * M1 * CA + MA * (Rz * N1 * Kz + M1 * κa)) * |τ - τ'| ^ α := by ring
      calc |-(((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
                * (deriv B τ / B τ)
              - ((ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
                * (deriv B τ' / B τ'))
            + (deriv (fun t => g (ρ ^ pExp α / B τ) |θ| t) τ
              - deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ')|
          ≤ |-(((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
                * (deriv B τ / B τ)
              - ((ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
                * (deriv B τ' / B τ'))|
            + |deriv (fun t => g (ρ ^ pExp α / B τ) |θ| t) τ
              - deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ'| := abs_add_le _ _
        _ = |((ρ ^ pExp α / B τ) * pzProf α g (ρ ^ pExp α / B τ) |θ| τ)
                * (deriv B τ / B τ)
              - ((ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
                * (deriv B τ' / B τ')|
            + |deriv (fun t => g (ρ ^ pExp α / B τ) |θ| t) τ
              - deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ'| := by rw [abs_neg]
        _ ≤ (Rz * M1 * CA + MA * (Rz * N1 * Kz + M1 * κa)) * |τ - τ'| ^ α
            + Nd * Kz * |τ - τ'| ^ α := add_le_add hUV hWh
        _ = ND * |τ - τ'| ^ α := by rw [hNDdef]; ring
    have hDb : |dProfOdd α B g ρ θ τ'| ≤ MD := by
      rw [pvb_dProfOdd_eq (α := α) (B := B) (g := g) (ρ := ρ) (θ := θ) (τ := τ')
        (ne_of_gt (h.hB τ' hτ'))]
      have hs1 : |(if 0 ≤ θ then (1 : ℝ) else -1)| = 1 := by split_ifs <;> norm_num
      rw [abs_mul, hs1, one_mul]
      have hstep : |-((ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
              * (deriv B τ' / B τ') + deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ'|
          ≤ |(ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ'|
              * |deriv B τ' / B τ'|
            + |deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ'| := by
        refine le_trans (abs_add_le _ _) ?_
        rw [abs_mul, abs_neg]
      calc |-((ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ')
              * (deriv B τ' / B τ') + deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ'|
          ≤ |(ρ ^ pExp α / B τ') * pzProf α g (ρ ^ pExp α / B τ') |θ| τ'|
              * |deriv B τ' / B τ'|
            + |deriv (fun t => g (ρ ^ pExp α / B τ') |θ| t) τ'| := hstep
        _ ≤ Rz * M1 * MA + Nd :=
            add_le_add (mul_le_mul hUb hVb (abs_nonneg _) (mul_nonneg hRz0 hM10)) hWb
        _ = MD := by rw [hMDdef]
    -- the two groups of terms
    have hDterm : ‖(A τ)⁻¹ • (dProfOdd α B g ρ θ τ • e)
        - (A τ')⁻¹ • (dProfOdd α B g ρ θ τ' • e)‖
        ≤ (MA * ND + CA * MD) * |τ - τ'| ^ α := by
      have hsplit : (A τ)⁻¹ • (dProfOdd α B g ρ θ τ • e)
          - (A τ')⁻¹ • (dProfOdd α B g ρ θ τ' • e)
          = (A τ)⁻¹ • ((dProfOdd α B g ρ θ τ - dProfOdd α B g ρ θ τ') • e)
            + ((A τ)⁻¹ - (A τ')⁻¹) • (dProfOdd α B g ρ θ τ' • e) := by
        conv_rhs => rw [sub_smul, smul_sub, sub_smul]
        abel
      have ha1 : |(A τ)⁻¹| ≤ MA := (hMA τ hτ).1
      have ha2 : |(A τ)⁻¹ - (A τ')⁻¹| ≤ CA * |τ - τ'| ^ α := hAic τ hτ τ' hτ'
      calc ‖(A τ)⁻¹ • (dProfOdd α B g ρ θ τ • e)
            - (A τ')⁻¹ • (dProfOdd α B g ρ θ τ' • e)‖
          = ‖(A τ)⁻¹ • ((dProfOdd α B g ρ θ τ - dProfOdd α B g ρ θ τ') • e)
              + ((A τ)⁻¹ - (A τ')⁻¹) • (dProfOdd α B g ρ θ τ' • e)‖ := by rw [hsplit]
        _ ≤ ‖(A τ)⁻¹ • ((dProfOdd α B g ρ θ τ - dProfOdd α B g ρ θ τ') • e)‖
              + ‖((A τ)⁻¹ - (A τ')⁻¹) • (dProfOdd α B g ρ θ τ' • e)‖ := norm_add_le _ _
        _ = |(A τ)⁻¹| * (|dProfOdd α B g ρ θ τ - dProfOdd α B g ρ θ τ'| * ‖e‖)
              + |(A τ)⁻¹ - (A τ')⁻¹| * (|dProfOdd α B g ρ θ τ'| * ‖e‖) := by
            simp only [norm_smul, Real.norm_eq_abs]
        _ ≤ MA * (ND * |τ - τ'| ^ α * 1) + (CA * |τ - τ'| ^ α) * (MD * 1) := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul ha1 (mul_le_mul hDh he1 (norm_nonneg _) (by positivity))
                (by positivity) hMA0
            · exact mul_le_mul ha2 (mul_le_mul hDb he1 (norm_nonneg _) (by positivity))
                (by positivity) (by positivity)
        _ = (MA * ND + CA * MD) * |τ - τ'| ^ α := by ring
    have hPterm : ‖(-(deriv A τ) / (A τ) ^ 2) • (profOdd α g (ρ ^ pExp α / B τ) θ τ • e)
        - (-(deriv A τ') / (A τ') ^ 2) • (profOdd α g (ρ ^ pExp α / B τ') θ τ' • e)‖
        ≤ (MA * NP + CA * Mp) * |τ - τ'| ^ α := by
      have hsplit : (-(deriv A τ) / (A τ) ^ 2) • (profOdd α g (ρ ^ pExp α / B τ) θ τ • e)
          - (-(deriv A τ') / (A τ') ^ 2) • (profOdd α g (ρ ^ pExp α / B τ') θ τ' • e)
          = (-(deriv A τ) / (A τ) ^ 2)
              • ((profOdd α g (ρ ^ pExp α / B τ) θ τ
                  - profOdd α g (ρ ^ pExp α / B τ') θ τ') • e)
            + ((-(deriv A τ) / (A τ) ^ 2) - (-(deriv A τ') / (A τ') ^ 2))
              • (profOdd α g (ρ ^ pExp α / B τ') θ τ' • e) := by
        conv_rhs => rw [sub_smul, smul_sub, sub_smul]
        abel
      have hb1 : |-(deriv A τ) / (A τ) ^ 2| ≤ MA := by
        simpa only [abs_div, abs_neg, abs_of_nonneg (sq_nonneg (A τ))]
          using (hMA τ hτ).2.1
      have hb2 : |-(deriv A τ) / (A τ) ^ 2 - - (deriv A τ') / (A τ') ^ 2| ≤ CA * |τ - τ'| ^ α := by
        have := hAhc τ hτ τ' hτ'
        rwa [show -(deriv A τ) / (A τ) ^ 2 - -(deriv A τ') / (A τ') ^ 2
            = -(deriv A τ / (A τ) ^ 2 - deriv A τ' / (A τ') ^ 2) by ring, abs_neg]
      calc ‖(-(deriv A τ) / (A τ) ^ 2) • (profOdd α g (ρ ^ pExp α / B τ) θ τ • e)
            - (-(deriv A τ') / (A τ') ^ 2) • (profOdd α g (ρ ^ pExp α / B τ') θ τ' • e)‖
          = ‖(-(deriv A τ) / (A τ) ^ 2)
                • ((profOdd α g (ρ ^ pExp α / B τ) θ τ
                    - profOdd α g (ρ ^ pExp α / B τ') θ τ') • e)
              + ((-(deriv A τ) / (A τ) ^ 2) - (-(deriv A τ') / (A τ') ^ 2))
                • (profOdd α g (ρ ^ pExp α / B τ') θ τ' • e)‖ := by rw [hsplit]
        _ ≤ ‖(-(deriv A τ) / (A τ) ^ 2)
                • ((profOdd α g (ρ ^ pExp α / B τ) θ τ
                    - profOdd α g (ρ ^ pExp α / B τ') θ τ') • e)‖
              + ‖((-(deriv A τ) / (A τ) ^ 2) - (-(deriv A τ') / (A τ') ^ 2))
                • (profOdd α g (ρ ^ pExp α / B τ') θ τ' • e)‖ := norm_add_le _ _
        _ = |-(deriv A τ) / (A τ) ^ 2|
              * (|profOdd α g (ρ ^ pExp α / B τ) θ τ
                  - profOdd α g (ρ ^ pExp α / B τ') θ τ'| * ‖e‖)
              + |(-(deriv A τ) / (A τ) ^ 2) - (-(deriv A τ') / (A τ') ^ 2)|
                * (|profOdd α g (ρ ^ pExp α / B τ') θ τ'| * ‖e‖) := by
            simp only [norm_smul, Real.norm_eq_abs]
        _ ≤ MA * (NP * |τ - τ'| ^ α * 1) + (CA * |τ - τ'| ^ α) * (Mp * 1) := by
            refine add_le_add ?_ ?_
            · exact mul_le_mul hb1 (mul_le_mul hPh he1 (norm_nonneg _) (by positivity))
                (by positivity) hMA0
            · exact mul_le_mul hb2 (mul_le_mul hPb he1 (norm_nonneg _) (by positivity))
                (by positivity) (by positivity)
        _ = (MA * NP + CA * Mp) * |τ - τ'| ^ α := by ring
    calc ‖(A τ)⁻¹ • (dProfOdd α B g ρ θ τ • e)
          + (-(deriv A τ) / (A τ) ^ 2) • (profOdd α g (ρ ^ pExp α / B τ) θ τ • e)
          - ((A τ')⁻¹ • (dProfOdd α B g ρ θ τ' • e)
            + (-(deriv A τ') / (A τ') ^ 2) • (profOdd α g (ρ ^ pExp α / B τ') θ τ' • e))‖
        = ‖((A τ)⁻¹ • (dProfOdd α B g ρ θ τ • e)
              - (A τ')⁻¹ • (dProfOdd α B g ρ θ τ' • e))
            + ((-(deriv A τ) / (A τ) ^ 2) • (profOdd α g (ρ ^ pExp α / B τ) θ τ • e)
              - (-(deriv A τ') / (A τ') ^ 2)
                • (profOdd α g (ρ ^ pExp α / B τ') θ τ' • e))‖ := by abel_nf
      _ ≤ (MA * ND + CA * MD) * |τ - τ'| ^ α + (MA * NP + CA * Mp) * |τ - τ'| ^ α :=
          le_trans (norm_add_le _ _) (add_le_add hDterm hPterm)
      _ = NN * |τ - τ'| ^ α := by rw [hNNdef]; ring

theorem pvb_timeDeriv_holder {α S : ℝ} {A B : ℝ → ℝ} {g : ℝ → ℝ → ℝ → ℝ}
    (h : RegPkg' α S A B g) :
    ∃ N : ℝ, 0 ≤ N ∧ ∀ x : R3, ∀ τ ∈ Set.Icc 0 S, ∀ τ' ∈ Set.Icc 0 S,
      ‖FiniteTimeSingularity.timeDeriv (physVort α A B g) x τ
        - FiniteTimeSingularity.timeDeriv (physVort α A B g) x τ'‖ ≤ N * |τ - τ'| ^ α := by
  obtain ⟨N, hN0, hN⟩ := pvb_vortDt_holder h
  refine ⟨N, hN0, fun x τ hτ τ' hτ' => ?_⟩
  rw [pvb_timeDeriv_eq_vortDt h x τ hτ, pvb_timeDeriv_eq_vortDt h x τ' hτ']
  exact hN x τ hτ τ' hτ'


end Work.FTS.FireFix.Prime