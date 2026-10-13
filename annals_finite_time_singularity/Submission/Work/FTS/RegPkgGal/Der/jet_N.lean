import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Submission.Work.FTS.Regularity.Defs
import Submission.Work.FTS.Regularity.regPkg_inhabited
import Submission.Work.Construction.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.RegPkgGal.Der

open scoped Real Topology
open Set Filter

set_option autoImplicit false

/-- **Scalar multiplication of a `Jet`**: if `h` is a `Jet` of constant `N` then so is
`x ↦ c · h x`, with constant `|c| · N`. -/
theorem jetN_const_mul {α S N c : ℝ} {h : ℝ → ℝ → ℝ → ℝ}
    (H : Work.FTS.Regularity.Jet α S N h) :
    Work.FTS.Regularity.Jet α S (|c| * N) (fun z θ τ => c * h z θ τ) := by
  refine ⟨mul_nonneg (abs_nonneg _) H.1, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (H.2.1 z θ τ hz hθ hτ) (abs_nonneg c)
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have h1 := H.2.2 z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    rw [show c * h z θ τ - c * h z' θ' τ' = c * (h z θ τ - h z' θ' τ') by ring, abs_mul]
    calc |c| * |h z θ τ - h z' θ' τ'| ≤ |c| * (N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α) :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg c)
      _ = |c| * N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by ring

/-- A bounded Lipschitz function of `θ` alone gives a `Jet` (with constant `2N`): the `θ`-analogue
of `Work.FTS.Regularity.Jet.of_z_lipschitz`.  Needed for the angular factor `sin²θ` of `N`. -/
theorem jetN_of_th_lipschitz {α S N : ℝ} {ψ : ℝ → ℝ} (hN : 0 ≤ N) (hα0 : 0 ≤ α) (hα1 : α ≤ 1)
    (hb : ∀ θ ∈ Work.Spaces.Iθ, |ψ θ| ≤ N)
    (hl : ∀ θ θ' : ℝ, θ ∈ Work.Spaces.Iθ → θ' ∈ Work.Spaces.Iθ → |ψ θ - ψ θ'| ≤ N * |θ - θ'|) :
    Work.FTS.Regularity.Jet α S (2 * N) (fun _ θ _ => ψ θ) := by
  refine ⟨by linarith, ?_, ?_⟩
  · intro z θ τ hz hθ hτ
    linarith [hb θ hθ]
  · intro z z' θ θ' τ τ' hz hz' hθ hθ' hτ hτ'
    have hd0 : (0 : ℝ) ≤ |z - z'| + |θ - θ'| + |τ - τ'| := by positivity
    rcases le_total |θ - θ'| 1 with hcase | hcase
    · have hle1 : |θ - θ'| ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by
        have h := Work.FTS.Regularity.le_rpow_add hα0 hα1 (abs_nonneg (θ - θ')) hcase
          (by positivity : (0 : ℝ) ≤ |z - z'| + |τ - τ'|)
        rw [show |θ - θ'| + (|z - z'| + |τ - τ'|) = |z - z'| + |θ - θ'| + |τ - τ'| by ring] at h
        exact h
      calc |ψ θ - ψ θ'| ≤ N * |θ - θ'| := hl θ θ' hθ hθ'
        _ ≤ N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := mul_le_mul_of_nonneg_left hle1 hN
        _ ≤ 2 * N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by
            have := Real.rpow_nonneg hd0 α
            nlinarith [hN]
    · have hle1 : 1 ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α := by
        refine Real.one_le_rpow ?_ hα0
        have h1 : 0 ≤ |z - z'| := abs_nonneg _
        have h2 : 0 ≤ |τ - τ'| := abs_nonneg _
        linarith
      have h2N : |ψ θ - ψ θ'| ≤ 2 * N := by
        have h1 : |ψ θ| ≤ N := hb θ hθ
        have h2 : |ψ θ'| ≤ N := hb θ' hθ'
        calc |ψ θ - ψ θ'| = |ψ θ + (-ψ θ')| := by ring_nf
          _ ≤ |ψ θ| + |-ψ θ'| := abs_add_le _ _
          _ = |ψ θ| + |ψ θ'| := by rw [abs_neg]
          _ ≤ 2 * N := by linarith
      calc |ψ θ - ψ θ'| ≤ 2 * N := h2N
        _ = 2 * N * 1 := by ring
        _ ≤ 2 * N * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
            mul_le_mul_of_nonneg_left hle1 (by linarith)

/-- The angular factor `θ ↦ sin²θ` is a `Jet` (constant `4`). -/
theorem jetN_sin_sq {α S : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) :
    Work.FTS.Regularity.Jet α S 4 (fun _ θ _ => Real.sin θ ^ 2) := by
  have h2 := jetN_of_th_lipschitz (α := α) (S := S) (N := 2) (ψ := fun θ => Real.sin θ ^ 2)
    (by norm_num) hα.le hα1 ?_ ?_
  · simpa [show ((2:ℝ) * 2) = 4 by norm_num] using h2
  · intro θ hθ
    have h1 : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
    rw [abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (Real.sin θ - 1), sq_nonneg (Real.sin θ + 1), abs_le.mp h1]
  · intro θ θ' hθ hθ'
    have hs : |Real.sin θ - Real.sin θ'| ≤ |θ - θ'| := by
      have h := Real.lipschitzWith_sin.dist_le_mul θ θ'
      simpa [Real.dist_eq] using h
    have hp : |Real.sin θ + Real.sin θ'| ≤ 2 := by
      have h1 : |Real.sin θ| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ, Real.sin_le_one θ⟩
      have h2 : |Real.sin θ'| ≤ 1 := abs_le.mpr ⟨Real.neg_one_le_sin θ', Real.sin_le_one θ'⟩
      calc |Real.sin θ + Real.sin θ'| ≤ |Real.sin θ| + |Real.sin θ'| := abs_add_le _ _
        _ ≤ 1 + 1 := add_le_add h1 h2
        _ = 2 := by norm_num
    rw [show Real.sin θ ^ 2 - Real.sin θ' ^ 2
        = (Real.sin θ - Real.sin θ') * (Real.sin θ + Real.sin θ') by ring, abs_mul]
    calc |Real.sin θ - Real.sin θ'| * |Real.sin θ + Real.sin θ'| ≤ |θ - θ'| * 2 :=
          mul_le_mul hs hp (abs_nonneg _) (abs_nonneg _)
      _ = 2 * |θ - θ'| := by ring

theorem jet_N {α S : ℝ} {g Φ : ℝ → ℝ → ℝ → ℝ} {N₁ N₂ N₃ N₄ N₅ N₆ N₇ : ℝ}
    (hα : 0 < α) (hα13 : α ≤ 1 / 3) (hS : 0 < S)
    (hF : Work.FTS.Regularity.Jet α S N₁ (fun z θ τ => Work.Construction.Ftau
      (Work.FTS.Regularity.pExp α) g τ z θ))
    (hDthF : Work.FTS.Regularity.Jet α S N₂ (fun z θ τ => Work.Spaces.Dth
      (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ) z θ))
    (hDzF : Work.FTS.Regularity.Jet α S N₃ (fun z θ τ => Work.Spaces.Dz
      (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ) z θ))
    (hRop : Work.FTS.Regularity.Jet α S N₄ (fun z θ τ => Work.Construction.Rop
      (Work.FTS.Regularity.pExp α) (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ)) z θ))
    (hUopF : Work.FTS.Regularity.Jet α S N₅ (fun z θ τ => Work.Construction.Uop
      (Work.FTS.Regularity.pExp α) (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ)) z θ
      * Work.Spaces.pth (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
        g τ z θ) z θ))
    (hVop : Work.FTS.Regularity.Jet α S N₆ (fun z θ τ => Work.Construction.Vop
      (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ)) z θ))
    (hFK : Work.FTS.Regularity.Jet α S N₇ (fun z θ τ =>
      Work.Construction.FK (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ) z)) :
    ∃ Nc : ℝ, Work.FTS.Regularity.Jet α S Nc
      (fun z θ τ => Work.Construction.N (Work.FTS.Regularity.pExp α)
        (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
        (Work.FTS.Regularity.gSlice Φ τ) z θ) := by
  have hα0 : (0:ℝ) ≤ α := hα.le
  have hα1 : α ≤ 1 := by linarith
  have hTh : Work.FTS.Regularity.Jet α S 4 (fun _ θ _ => Real.sin θ ^ 2) :=
    jetN_sin_sq hα hα1
  have hRF : Work.FTS.Regularity.Jet α S (2 * N₄ * N₁)
      (fun z θ τ => Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
          (Work.FTS.Regularity.gSlice Φ τ)) z θ
        * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ) :=
    Work.FTS.Regularity.Jet.mul hRop hF
  have hT1 : Work.FTS.Regularity.Jet α S (|(2:ℝ)| * (2 * N₄ * N₁))
      (fun z θ τ => 2 * (Work.Construction.Rop (Work.FTS.Regularity.pExp α)
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
          (Work.FTS.Regularity.gSlice Φ τ)) z θ
        * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ)) :=
    jetN_const_mul (c := (2:ℝ)) hRF
  have hT2 : Work.FTS.Regularity.Jet α S (|(2:ℝ)| * N₅)
      (fun z θ τ => 2 * (Work.Construction.Uop
        (Work.FTS.Regularity.pExp α) (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
          (Work.FTS.Regularity.gSlice Φ τ)) z θ
        * Work.Spaces.pth (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          g τ z θ) z θ)) :=
    jetN_const_mul (c := (2:ℝ)) hUopF
  have hVZ : Work.FTS.Regularity.Jet α S (2 * N₆ * N₃)
      (fun z θ τ => Work.Construction.Vop
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
          (Work.FTS.Regularity.gSlice Φ τ)) z θ
        * Work.Spaces.Dz (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          g τ z θ) z θ) :=
    Work.FTS.Regularity.Jet.mul hVop hDzF
  have hT3 : Work.FTS.Regularity.Jet α S (|2 * Work.FTS.Regularity.pExp α| * (2 * N₆ * N₃))
      (fun z θ τ => 2 * Work.FTS.Regularity.pExp α * (Work.Construction.Vop
        (Work.Construction.PhiTil (Work.FTS.Regularity.pExp α)
          (Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ)
          (Work.FTS.Regularity.gSlice Φ τ)) z θ
        * Work.Spaces.Dz (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          g τ z θ) z θ)) :=
    jetN_const_mul (c := 2 * Work.FTS.Regularity.pExp α) hVZ
  have hKD : Work.FTS.Regularity.Jet α S (2 * N₇ * N₂)
      (fun z θ τ => Work.Construction.FK (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) g τ) z
        * Work.Spaces.Dth (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          g τ z θ) z θ) :=
    Work.FTS.Regularity.Jet.mul hFK hDthF
  have hT4 : Work.FTS.Regularity.Jet α S (|(1/2:ℝ)| * (2 * N₇ * N₂))
      (fun z θ τ => (1/2) * (Work.Construction.FK (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) g τ) z
        * Work.Spaces.Dth (fun z θ => Work.Construction.Ftau (Work.FTS.Regularity.pExp α)
          g τ z θ) z θ)) :=
    jetN_const_mul (c := (1/2:ℝ)) hKD
  have hKF : Work.FTS.Regularity.Jet α S (2 * 4 * (2 * N₇ * N₁))
      (fun z θ τ => Real.sin θ ^ 2 * (Work.Construction.FK (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) g τ) z
        * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ)) :=
    Work.FTS.Regularity.Jet.mul hTh (Work.FTS.Regularity.Jet.mul hFK hF)
  have hT5 : Work.FTS.Regularity.Jet α S (|(1:ℝ)| * (2 * 4 * (2 * N₇ * N₁)))
      (fun z θ τ => 1 * (Real.sin θ ^ 2 * (Work.Construction.FK (Work.Construction.Ftau
          (Work.FTS.Regularity.pExp α) g τ) z
        * Work.Construction.Ftau (Work.FTS.Regularity.pExp α) g τ z θ))) :=
    jetN_const_mul (c := (1:ℝ)) hKF
  have hcomb := Work.FTS.Regularity.Jet.add
    (Work.FTS.Regularity.Jet.add
      (Work.FTS.Regularity.Jet.add
        (Work.FTS.Regularity.Jet.add hT1 (Work.FTS.Regularity.Jet.neg hT2))
        (Work.FTS.Regularity.Jet.neg hT3))
      (Work.FTS.Regularity.Jet.neg hT4))
    (Work.FTS.Regularity.Jet.neg hT5)
  exact ⟨_, Work.FTS.Regularity.Jet.congr hcomb (fun z θ τ hz hθ hτ => by
    simp only [Work.Construction.N, Work.Spaces.Dth, Work.Construction.s2]
    ring)⟩

end Work.FTS.RegPkgGal.Der
