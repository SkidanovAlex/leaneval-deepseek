import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bPrep
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.T5bAux.t5bPieceAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux.T5bAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

theorem piece_abs_le_zero {α : ℝ} {f : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ → ℝ} {a b k : ℕ}
    {C4 C6 Cc : ℝ} (hC4 : 0 ≤ C4) (hC6 : 0 ≤ C6) (hCc : 0 ≤ Cc)
    (hsup4 : ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z) z|
        ≤ C4 * Work.Spaces.HkNorm α 4 f)
    (hsup6 : ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z) z|
        ≤ C6 * Work.Spaces.HkNorm α 6 f)
    (hCcbd : ∀ θ ∈ Work.Spaces.Iθ, |Work.Construction.c2m θ| ≤ Cc)
    (hk : k ≤ b) (hb : b ≤ 6) (hleaf : Work.FTS.TransportS.IsLeafW α a ρ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece f ρ a b k 0 (z, θ)|
      ≤ (Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
                else C6 * Work.Spaces.HkNorm α 6 f))
          * (ρ z θ * |Work.Spaces.mixed (b - k + 1) a f z θ|
              * |Work.Spaces.mixed b a f z θ|) := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hρnn : 0 ≤ ρ z θ := Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hleaf z hθI
  have hc2 : |Work.Construction.c2m θ| ≤ Cc := hCcbd θ hθI
  have hL : |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
      ≤ (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
          else C6 * Work.Spaces.HkNorm α 6 f) := by
    by_cases h : k ≤ 4
    · rw [if_pos h]; exact hsup4 k h z hz
    · rw [if_neg h]; exact hsup6 k (by omega) z hz
  have hKnn : 0 ≤ (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
      else C6 * Work.Spaces.HkNorm α 6 f) := by
    by_cases h : k ≤ 4
    · rw [if_pos h]; exact mul_nonneg hC4 (Work.Spaces.HkNorm_nonneg α 4 f)
    · rw [if_neg h]; exact mul_nonneg hC6 (Work.Spaces.HkNorm_nonneg α 6 f)
  have hfac : 0 ≤ ρ z θ * |Work.Spaces.mixed (b - k + 1) a f z θ|
      * |Work.Spaces.mixed b a f z θ| :=
    mul_nonneg (mul_nonneg hρnn (abs_nonneg _)) (abs_nonneg _)
  have h1 : |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        * |Work.Construction.c2m θ|
        ≤ (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
            else C6 * Work.Spaces.HkNorm α 6 f) * Cc :=
    mul_le_mul hL hc2 (abs_nonneg _) hKnn
  have h2 := mul_le_mul_of_nonneg_right h1 hfac
  have hkey : ρ z θ * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
        * |Work.Construction.c2m θ| * |Work.Spaces.mixed (b - k + 1) a f z θ|
        * |Work.Spaces.mixed b a f z θ|
      ≤ (Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
                else C6 * Work.Spaces.HkNorm α 6 f))
          * (ρ z θ * |Work.Spaces.mixed (b - k + 1) a f z θ|
              * |Work.Spaces.mixed b a f z θ|) := by
    calc ρ z θ * |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
          * |Work.Construction.c2m θ| * |Work.Spaces.mixed (b - k + 1) a f z θ|
          * |Work.Spaces.mixed b a f z θ|
        = (|Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
            * |Work.Construction.c2m θ|)
            * (ρ z θ * |Work.Spaces.mixed (b - k + 1) a f z θ|
                * |Work.Spaces.mixed b a f z θ|) := by ring
      _ ≤ ((if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
              else C6 * Work.Spaces.HkNorm α 6 f) * Cc)
            * (ρ z θ * |Work.Spaces.mixed (b - k + 1) a f z θ|
                * |Work.Spaces.mixed b a f z θ|) := h2
      _ = (Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
                else C6 * Work.Spaces.HkNorm α 6 f))
          * (ρ z θ * |Work.Spaces.mixed (b - k + 1) a f z θ|
              * |Work.Spaces.mixed b a f z θ|) := by ring
  simp only [Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece, Work.Spaces.DthIter_zero]
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hρnn]
  exact hkey

/-- The pointwise bound on the piece when the `c₂ₘ`-factor carries at least one angular
derivative: then `|D_θ^i c₂ₘ| ≤ Cc·sin(2θ)`, and the `σ`-gain `sigma_mul_leaf_le` upgrades
`sin(2θ)·ρ` to the single weight `w²·sin(2θ)^{-(γ-1)}`. -/
theorem piece_abs_le_pos {α : ℝ} {f : ℝ → ℝ → ℝ} {ρ : ℝ → ℝ → ℝ} {a b k i : ℕ}
    {C4 C6 Cc : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hC4 : 0 ≤ C4) (hC6 : 0 ≤ C6) (hCc : 0 ≤ Cc)
    (hsup4 : ∀ j : ℕ, j ≤ 4 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z) z|
        ≤ C4 * Work.Spaces.HkNorm α 4 f)
    (hsup6 : ∀ j : ℕ, j ≤ 6 → ∀ z : ℝ, 0 < z →
      |Work.Elliptic.DzdIter j (fun z => Work.Construction.L12 f z) z|
        ≤ C6 * Work.Spaces.HkNorm α 6 f)
    (hCcg : ∀ j : ℕ, 1 ≤ j → j ≤ 8 → ∀ (z θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.Spaces.DthIter j (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|
        ≤ Cc * Real.sin (2 * θ))
    (hk : k ≤ b) (hb : b ≤ 6) (hleaf : Work.FTS.TransportS.IsLeafW α a ρ)
    (hi1 : 1 ≤ i) (hi8 : i ≤ 8)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece f ρ a b k i (z, θ)|
      ≤ (Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
                else C6 * Work.Spaces.HkNorm α 6 f))
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))
              * |Work.Spaces.mixed (b - k + 1) (a - i) f z θ|
              * |Work.Spaces.mixed b a f z θ|) := by
  have hθI : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hσ : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hc2 : |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ|
      ≤ Cc * Real.sin (2 * θ) := hCcg i hi1 hi8 z θ hθI
  have hL : |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z|
      ≤ (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
          else C6 * Work.Spaces.HkNorm α 6 f) := by
    by_cases h : k ≤ 4
    · rw [if_pos h]; exact hsup4 k h z hz
    · rw [if_neg h]; exact hsup6 k (by omega) z hz
  have hKnn : 0 ≤ (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
      else C6 * Work.Spaces.HkNorm α 6 f) := by
    by_cases h : k ≤ 4
    · rw [if_pos h]; exact mul_nonneg hC4 (Work.Spaces.HkNorm_nonneg α 4 f)
    · rw [if_neg h]; exact mul_nonneg hC6 (Work.Spaces.HkNorm_nonneg α 6 f)
  have hsig : Real.sin (2 * θ) * ρ z θ
      ≤ (Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) :=
    Work.FTS.StrongPersist.H6Pair6Aux.sigma_mul_leaf_le hα hleaf hθ
  have hWnn : 0 ≤ (Work.Spaces.w z) ^ 2
      * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)) :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hσ _)
  set D : ℝ := |Work.Elliptic.DzdIter k (fun z => Work.Construction.L12 f z) z| with hD
  set Cz : ℝ := |Work.Spaces.DthIter i (fun _ θ : ℝ => Work.Construction.c2m θ) z θ| with hCz
  set Xx : ℝ := |Work.Spaces.mixed (b - k + 1) (a - i) f z θ| with hXx
  set Yy : ℝ := |Work.Spaces.mixed b a f z θ| with hYy
  have hDnn : 0 ≤ D := by rw [hD]; exact abs_nonneg _
  have hXnn : 0 ≤ Xx := by rw [hXx]; exact abs_nonneg _
  have hYnn : 0 ≤ Yy := by rw [hYy]; exact abs_nonneg _
  have hρ0 : 0 ≤ ρ z θ := Work.FTS.StrongPersist.H6Pair6Aux.leaf_nonneg hleaf z hθI
  have hc2' : Cz ≤ Cc * Real.sin (2 * θ) := by rw [hCz]; exact hc2
  have hL' : D ≤ (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
      else C6 * Work.Spaces.HkNorm α 6 f) := by rw [hD]; exact hL
  -- the three-factor step `ρ·|D_z^kL₁₂|·|D_θ^i c₂ₘ| ≤ (Cc·K)·W`
  have hstep1 : ρ z θ * D * Cz ≤ (Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
      else C6 * Work.Spaces.HkNorm α 6 f))
      * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))) := by
    have h1 : ρ z θ * Cz ≤ Cc * (Real.sin (2 * θ) * ρ z θ) := by
      calc ρ z θ * Cz ≤ ρ z θ * (Cc * Real.sin (2 * θ)) :=
            mul_le_mul_of_nonneg_left hc2' hρ0
        _ = Cc * (Real.sin (2 * θ) * ρ z θ) := by ring
    have h2 : Cc * (Real.sin (2 * θ) * ρ z θ)
        ≤ Cc * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))) :=
      mul_le_mul_of_nonneg_left hsig hCc
    calc ρ z θ * D * Cz = (ρ z θ * Cz) * D := by ring
      _ ≤ (Cc * ((Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1)))) * D :=
          mul_le_mul_of_nonneg_right (h1.trans h2) hDnn
      _ ≤ (Cc * ((Work.Spaces.w z) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))))
            * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
              else C6 * Work.Spaces.HkNorm α 6 f) :=
          mul_le_mul_of_nonneg_left hL' (mul_nonneg hCc hWnn)
      _ = (Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
              else C6 * Work.Spaces.HkNorm α 6 f))
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))) := by ring
  have hkey : ρ z θ * D * Cz * Xx * Yy
      ≤ (Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
                else C6 * Work.Spaces.HkNorm α 6 f))
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))
              * Xx * Yy) := by
    calc ρ z θ * D * Cz * Xx * Yy = (ρ z θ * D * Cz) * (Xx * Yy) := by ring
      _ ≤ ((Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
                else C6 * Work.Spaces.HkNorm α 6 f))
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))))
            * (Xx * Yy) := mul_le_mul_of_nonneg_right hstep1 (mul_nonneg hXnn hYnn)
      _ = (Cc * (if k ≤ 4 then C4 * Work.Spaces.HkNorm α 4 f
                else C6 * Work.Spaces.HkNorm α 6 f))
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α - 1))
              * Xx * Yy) := by ring
  simp only [Work.FTS.StrongPersist.H6Pair6Aux.t5bPiece]
  rw [abs_mul, abs_mul, abs_mul, abs_mul, abs_of_nonneg hρ0,
    ← hD, ← hCz, ← hXx, ← hYy]
  exact hkey

end Work.FTS.StrongPersist.H6Pair6Aux.T5bAux
