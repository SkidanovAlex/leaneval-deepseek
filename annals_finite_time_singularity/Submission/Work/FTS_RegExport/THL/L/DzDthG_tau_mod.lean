import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS_RegExport.THL.Defs
import Submission.Work.FTS_RegExport.RXR5.Pieces.mixed_slice_tau_modulus

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.THL.L.DzDthG_tau_mod` — B4: the `τ`-modulus of `D_z g̃`, `D_θ g̃`

`DzG α g z θ τ = D_z g̃(z,θ,τ)` and `DthG α g z θ τ = D_θ g̃(z,θ,τ)` for the sanitised family
`g̃ = gS α (tauExt g)`.  The lemma produces an `α`-Hölder modulus in the fake time `τ` on the
*closed* box `[0,∞) × Iθ × [0,S]`.

The proof has three ingredients.

* On the *open* quadrant `z > 0`, `0 < θ < π/2` the sanitiser and the right-Taylor extension are
  invisible: `gS α (tauExt g) z θ τ = g z θ τ` for `τ ≥ 0`, so the mixed slots agree there
  (`mixed_congr_of_isOpen`).  The weighted Lipschitz modulus in `τ` of the mixed slots of `g`
  is `RXR5.Pieces.mixed_slice_tau_modulus` (from the `LimApprox` clause of `DynOK'`), with the
  weight `z^{3/2}/(1+z)² ≤ 1`; Lipschitz on `[0,S]` is `α`-Hölder via
  `|Δτ| ≤ S^{1-α}|Δτ|^α`.
* On the two angular edges `θ = 0`, `θ = π/2` and on `z = 0` the families vanish identically:
  `g` vanishes at the angular edges (`RegPkgMin.vanish`), which makes the whole `z`-slice of
  `gS α (tauExt g)` vanish there, so the `z`-derivative is `0`; and `gS α (tauExt g)`
  vanishes at `z = 0`, so its `θ`-derivative is `0`.
-/

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS_RegExport.THL.L

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.Regularity (pExp)

/-! ## Elementary real facts -/

/-- Lipschitz on a compact interval is `α`-Hölder, with the factor `S^{1-α}`. -/
private lemma abs_sub_le_rpow {α S τ τ' : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (_hS : 0 < S)
    (hτ : τ ∈ Icc (0:ℝ) S) (hτ' : τ' ∈ Icc (0:ℝ) S) :
    |τ - τ'| ≤ S ^ (1 - α) * |τ - τ'| ^ α := by
  have ht0 : 0 ≤ |τ - τ'| := abs_nonneg _
  have htS : |τ - τ'| ≤ S := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [hτ.2, hτ'.1], by linarith [hτ'.2, hτ.1]⟩
  rcases eq_or_lt_of_le ht0 with h | h
  · rw [← h, Real.zero_rpow hα.ne', mul_zero]
  · have h1 : (0:ℝ) ≤ 1 - α := by linarith
    have h2 : |τ - τ'| ^ (1 - α) ≤ S ^ (1 - α) := Real.rpow_le_rpow ht0 htS h1
    have h3 : |τ - τ'| ^ (1 - α) * |τ - τ'| ^ α = |τ - τ'| := by
      rw [← Real.rpow_add h, show 1 - α + α = 1 by ring, Real.rpow_one]
    calc |τ - τ'| = |τ - τ'| ^ (1 - α) * |τ - τ'| ^ α := h3.symm
      _ ≤ S ^ (1 - α) * |τ - τ'| ^ α := mul_le_mul_of_nonneg_right h2 (Real.rpow_nonneg ht0 _)

/-- `z^{3/2} ≤ (1+z)²` for `z ≥ 0`. -/
private lemma rpow_three_halves_le_sq_add_one {z : ℝ} (hz : 0 ≤ z) :
    z ^ ((3:ℝ)/2) ≤ (1 + z) ^ 2 := by
  rcases lt_or_ge z 1 with h | h
  · calc z ^ ((3:ℝ)/2) ≤ 1 := Real.rpow_le_one hz h.le (by norm_num)
      _ ≤ (1 + z) ^ 2 := by nlinarith [sq_nonneg z]
  · calc z ^ ((3:ℝ)/2) ≤ z ^ (2:ℝ) := Real.rpow_le_rpow_of_exponent_le h (by norm_num)
      _ ≤ (1 + z) ^ (2:ℝ) := Real.rpow_le_rpow hz (by linarith) (by norm_num)
      _ = (1 + z) ^ 2 := Real.rpow_two (1+z)

/-- the weighted interior factor of `mixed_slice_tau_modulus` is `≤ 1` on `z ≥ 0`. -/
private lemma rpow_three_halves_div_sq_le_one {z : ℝ} (hz : 0 ≤ z) :
    z ^ ((3:ℝ)/2) / (1 + z) ^ 2 ≤ 1 := by
  rw [div_le_one (by positivity)]
  exact rpow_three_halves_le_sq_add_one hz

/-! ## The sanitiser and the right-Taylor extension on the closed box -/

/-- On the closed angular interval and for `τ ≥ 0`, the sanitised family is the original one. -/
private lemma gS_tauExt_eq_of_pos {α : ℝ} {g : Fam} {z θ τ : ℝ} (hz : 0 < z) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ π / 2) (hτ : 0 ≤ τ) :
    Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ τ = g z θ τ := by
  have h1 : Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z θ τ
      = Work.FTS.FinalV2.tauExt g z θ τ := by
    simp [Work.FTS.FinalV2.gS, hz, hθ0, hθ1]
  rw [h1, Work.FTS.FinalV2.tauExt_of_nonneg g hτ]

/-- The mixed slots of the sanitised family agree with those of `g` on the open quadrant. -/
private lemma mixed_gS_tauExt_eq {α : ℝ} {g : Fam} {τ z θ : ℝ} (j i : ℕ)
    (hz : 0 < z) (hθ0 : 0 < θ) (hθ1 : θ < π / 2) (hτ : 0 ≤ τ) :
    Work.Spaces.mixed j i (slice (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ) z θ
      = Work.Spaces.mixed j i (slice g τ) z θ := by
  have hagree : Set.EqOn
      (Function.uncurry (slice (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ))
      (Function.uncurry (slice g τ)) Work.FTS.EllipticEst.Q0 := by
    rintro ⟨z', θ'⟩ hzθ'
    obtain ⟨hz', hθ'⟩ := hzθ'
    exact gS_tauExt_eq_of_pos (α := α) (g := g) hz' hθ'.1.le hθ'.2.le hτ
  have h := Work.FTS.RegPkgGal.mixed_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hagree j i
  exact h (show (z, θ) ∈ Work.FTS.EllipticEst.Q0 from ⟨hz, hθ0, hθ1⟩)

/-! ## Vanishing on the degenerate set `{z = 0} ∪ {θ = 0} ∪ {θ = π/2}` -/

private lemma gS_tauExt_zero_theta0 {α : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ)
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (pExp α) g) (z : ℝ) :
    Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z 0 τ = 0 := by
  by_cases hz : 0 < z
  · have h := gS_tauExt_eq_of_pos (α := α) (g := g) (z := z) (θ := 0) (τ := τ)
      hz le_rfl Real.pi_div_two_pos.le hτ
    rw [h]
    exact (hmin.vanish τ hτ z hz.le).1
  · simp [Work.FTS.FinalV2.gS, hz]

private lemma gS_tauExt_zero_pi2 {α : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ)
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (pExp α) g) (z : ℝ) :
    Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z (π / 2) τ = 0 := by
  by_cases hz : 0 < z
  · have h := gS_tauExt_eq_of_pos (α := α) (g := g) (z := z) (θ := π / 2) (τ := τ)
      hz Real.pi_div_two_pos.le le_rfl hτ
    rw [h]
    exact (hmin.vanish τ hτ z hz.le).2
  · simp [Work.FTS.FinalV2.gS, hz]

/-- At `θ = 0` the whole `z`-slice of the sanitised family vanishes, hence so does `D_z`. -/
private lemma DzG_eq_zero_theta0 {α : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ)
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (pExp α) g) (z : ℝ) : DzG α g z 0 τ = 0 := by
  have h1 : ∀ z' : ℝ, Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z' 0 τ = 0 :=
    fun z' => gS_tauExt_zero_theta0 hτ hmin z'
  have h2 : (fun z' : ℝ => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z' 0 τ)
      = fun _ => (0 : ℝ) := funext h1
  simp only [DzG, Work.Spaces.Dz, Work.Spaces.pz]
  rw [h2]
  simp

/-- At `θ = π/2` the whole `z`-slice of the sanitised family vanishes, hence so does `D_z`. -/
private lemma DzG_eq_zero_pi2 {α : ℝ} {g : Fam} {τ : ℝ} (hτ : 0 ≤ τ)
    (hmin : Work.FTS.StrongGlobal.RegPkgMin (pExp α) g) (z : ℝ) : DzG α g z (π/2) τ = 0 := by
  have h1 : ∀ z' : ℝ, Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z' (π/2) τ = 0 :=
    fun z' => gS_tauExt_zero_pi2 hτ hmin z'
  have h2 : (fun z' : ℝ => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) z' (π/2) τ)
      = fun _ => (0 : ℝ) := funext h1
  simp only [DzG, Work.Spaces.Dz, Work.Spaces.pz]
  rw [h2]
  simp

/-- At `z = 0` the sanitised family vanishes identically, hence so does `D_θ`. -/
private lemma DthG_eq_zero_of_z {α : ℝ} {g : Fam} (θ τ : ℝ) : DthG α g 0 θ τ = 0 := by
  have hfun : (fun θ' : ℝ => Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g) 0 θ' τ)
      = fun _ => (0 : ℝ) := by
    funext θ'; simp [Work.FTS.FinalV2.gS]
  simp only [DthG, Work.Spaces.Dth, Work.Spaces.pth]
  rw [hfun]
  simp

/-- At `z = 0` the sanitised family vanishes identically, hence so does `D_z`. -/
private lemma DzG_eq_zero_of_z {α : ℝ} {g : Fam} (θ τ : ℝ) : DzG α g 0 θ τ = 0 := by
  simp [DzG, Work.Spaces.Dz]

theorem DzDthG_tau_mod {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S, ∀ z : ℝ, 0 ≤ z →
      ∀ θ ∈ Work.Spaces.Iθ,
        |Work.FTS_RegExport.THL.DzG α g z θ τ - Work.FTS_RegExport.THL.DzG α g z θ τ'|
            ≤ L * |τ - τ'| ^ α ∧
        |Work.FTS_RegExport.THL.DthG α g z θ τ - Work.FTS_RegExport.THL.DthG α g z θ τ'|
            ≤ L * |τ - τ'| ^ α := by
  have hα1 : α ≤ 1 := by linarith
  have hαG : 0 < pExp α := Work.FTS.Regularity.pExp_pos hα
  have hαG1 : pExp α ≤ 1 := Work.FTS.Regularity.pExp_le_one hα13
  have hmin : Work.FTS.StrongGlobal.RegPkgMin (pExp α) g := hOK.1.1
  obtain ⟨L₀, hL₀0, hL₀⟩ :=
    Work.FTS_RegExport.RXR5.Pieces.mixed_slice_tau_modulus hOK.2 hαG hαG1 S hS
  have hL0 : 0 ≤ L₀ * S ^ (1 - α) := mul_nonneg hL₀0 (Real.rpow_nonneg hS.le _)
  refine ⟨L₀ * S ^ (1 - α), hL0, ?_⟩
  intro τ hτ τ' hτ' z hz θ hθ
  have hτ0 : 0 ≤ τ := hτ.1
  have hτ'0 : 0 ≤ τ' := hτ'.1
  have hhd : |τ - τ'| ≤ S ^ (1 - α) * |τ - τ'| ^ α := abs_sub_le_rpow hα hα1 hS hτ hτ'
  have hnn : (0:ℝ) ≤ |τ - τ'| ^ α := Real.rpow_nonneg (abs_nonneg _) _
  have htriv : (0:ℝ) ≤ L₀ * S ^ (1 - α) * |τ - τ'| ^ α := mul_nonneg hL0 hnn
  -- the mixed slots on the open quadrant, upgraded from Lipschitz to `α`-Hölder
  have hbound : ∀ (j i : ℕ), j + i ≤ 2 → ∀ z' θ' : ℝ, 0 < z' → 0 < θ' → θ' < π / 2 →
      |Work.Spaces.mixed j i (slice (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ) z' θ'
        - Work.Spaces.mixed j i (slice (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ') z' θ'|
        ≤ L₀ * S ^ (1 - α) * |τ - τ'| ^ α := by
    intro j i hji z' θ' hz' hθ'0 hθ'1
    have e1 := mixed_gS_tauExt_eq (α := α) (g := g) (τ := τ) (z := z') (θ := θ')
      j i hz' hθ'0 hθ'1 hτ0
    have e2 := mixed_gS_tauExt_eq (α := α) (g := g) (τ := τ') (z := z') (θ := θ')
      j i hz' hθ'0 hθ'1 hτ'0
    have h3 := hL₀ τ hτ τ' hτ' j i (by omega) z' θ' hz' hθ'0 hθ'1
    calc |Work.Spaces.mixed j i (slice (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ) z' θ'
          - Work.Spaces.mixed j i (slice (Work.FTS.FinalV2.gS α (Work.FTS.FinalV2.tauExt g)) τ') z' θ'|
        = |Work.Spaces.mixed j i (slice g τ) z' θ' - Work.Spaces.mixed j i (slice g τ') z' θ'| := by
          rw [e1, e2]
      _ ≤ L₀ * (z' ^ ((3:ℝ)/2) / (1 + z') ^ 2) * |τ - τ'| := h3
      _ ≤ L₀ * 1 * |τ - τ'| := by
          refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
          exact mul_le_mul_of_nonneg_left (rpow_three_halves_div_sq_le_one hz'.le) hL₀0
      _ = L₀ * |τ - τ'| := by ring
      _ ≤ L₀ * (S ^ (1 - α) * |τ - τ'| ^ α) := mul_le_mul_of_nonneg_left hhd hL₀0
      _ = L₀ * S ^ (1 - α) * |τ - τ'| ^ α := by ring
  refine ⟨?_, ?_⟩
  · -- the `D_z` half
    rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
    · rw [hθ0.symm, DzG_eq_zero_theta0 (α := α) (g := g) (τ := τ) hτ0 hmin z,
        DzG_eq_zero_theta0 (α := α) (g := g) (τ := τ') hτ'0 hmin z]
      simp only [sub_zero, abs_zero]
      exact htriv
    · rcases eq_or_lt_of_le hθ.2 with hθ1 | hθ1
      · rw [hθ1, DzG_eq_zero_pi2 (α := α) (g := g) (τ := τ) hτ0 hmin z,
          DzG_eq_zero_pi2 (α := α) (g := g) (τ := τ') hτ'0 hmin z]
        simp only [sub_zero, abs_zero]
        exact htriv
      · rcases eq_or_lt_of_le hz with hz0 | hzpos
        · rw [hz0.symm, DzG_eq_zero_of_z (α := α) (g := g) θ τ,
            DzG_eq_zero_of_z (α := α) (g := g) θ τ']
          simp only [sub_zero, abs_zero]
          exact htriv
        · exact hbound 1 0 (by norm_num) z θ hzpos hθ0 hθ1
  · -- the `D_θ` half
    rcases eq_or_lt_of_le hθ.1 with hθ0 | hθ0
    · rw [hθ0.symm]
      have h0 : DthG α g z 0 τ = 0 := by simp [DthG, Work.Spaces.Dth]
      have h0' : DthG α g z 0 τ' = 0 := by simp [DthG, Work.Spaces.Dth]
      rw [h0, h0', sub_zero, abs_zero]
      exact htriv
    · rcases eq_or_lt_of_le hθ.2 with hθ1 | hθ1
      · rw [hθ1]
        have hsin : Real.sin (2 * (π/2)) = 0 := by
          rw [show 2 * (π/2) = π by ring, Real.sin_pi]
        have h0 : DthG α g z (π/2) τ = 0 := by simp [DthG, Work.Spaces.Dth, hsin]
        have h0' : DthG α g z (π/2) τ' = 0 := by simp [DthG, Work.Spaces.Dth, hsin]
        rw [h0, h0', sub_zero, abs_zero]
        exact htriv
      · rcases eq_or_lt_of_le hz with hz0 | hzpos
        · rw [hz0.symm, DthG_eq_zero_of_z (α := α) (g := g) θ τ,
            DthG_eq_zero_of_z (α := α) (g := g) θ τ']
          simp only [sub_zero, abs_zero]
          exact htriv
        · exact hbound 0 1 (by norm_num) z θ hzpos hθ0 hθ1

end Work.FTS_RegExport.THL.L
