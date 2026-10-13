import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.IntervalCases
import Submission.Work.FTS.H2.STEasyDefs
import Submission.Work.FTS.H2.Whz_Wm_sq
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.Spaces.SmoothCompact_Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 8000000

theorem contDiffOn_pth_zslice {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.SmoothNbhd g)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    ContDiffOn ℝ ⊤ (fun z => Work.Spaces.pth g z θ) (Set.Ioi (-1)) := by
  have hjoint : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.pth g)) Work.Spaces.nbhU :=
    Work.Spaces.contDiffOn_uncurry_pth Work.Spaces.isOpen_nbhU hg
  have hp : ContDiffOn ℝ ⊤ (fun z : ℝ => (z, θ)) (Set.Ioi (-1)) := by fun_prop
  have h2 := hjoint.comp hp (fun z hz =>
    ⟨hz, by linarith [hθ.1, Real.pi_pos], by linarith [hθ.2, Real.pi_pos]⟩)
  simpa [Function.comp_def, Function.uncurry] using h2

theorem smoothInt_pth {g : ℝ → ℝ → ℝ} (hg : Work.Spaces.SmoothNbhd g) :
    Work.Spaces.SmoothInt (Work.Spaces.pth g) := by
  have hjoint : ContDiffOn ℝ ⊤ (Function.uncurry (Work.Spaces.pth g)) Work.Spaces.nbhU :=
    Work.Spaces.contDiffOn_uncurry_pth Work.Spaces.isOpen_nbhU hg
  refine ⟨hjoint.mono ?_, fun θ hθ => contDiffOn_pth_zslice hg hθ⟩
  intro p hp
  exact ⟨hp.1, ⟨by linarith [hp.2.1], hp.2.2.trans_le (by linarith [Real.pi_pos])⟩⟩

theorem EasyId {α : ℝ} (hα : 0 < α) {f g : ℝ → ℝ → ℝ} (hsm : Work.Spaces.SmoothInt f)
    (hg : Work.Spaces.SmoothNbhd g) {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz)
    (hθ : θ ∈ Work.Spaces.Iθ) :
    H4PairInt α (fun z θ => f z θ * Work.Spaces.pth g z θ) g z θ
      = EZ f g z θ + EM α f g z θ + EC α f g z θ + HardF α f g z θ := by
  have hzr : (z, θ) ∈ Work.Spaces.nbhU := Work.Spaces.mem_nbhU hz hθ
  have hslice_pg := contDiffOn_pth_zslice hg hθ
  have hSint := smoothInt_pth hg
  have hWhz := (Whz_Wm_sq α hα z θ hθ).1
  have hWm := (Whz_Wm_sq α hα z θ hθ).2
  have hprodW : ∀ a b : ℝ, (a * Whz z θ) * (b * Whz z θ)
      = a * b * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by
    intro a b
    calc (a * Whz z θ) * (b * Whz z θ) = a * b * (Whz z θ * Whz z θ) := by ring
      _ = a * b * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)) := by
          rw [show Whz z θ * Whz z θ = (Whz z θ) ^ 2 by ring, hWhz]
  have hprodM : ∀ a b : ℝ, (a * Wm α z θ) * (b * Wm α z θ)
      = a * b * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
    intro a b
    calc (a * Wm α z θ) * (b * Wm α z θ) = a * b * (Wm α z θ * Wm α z θ) := by ring
      _ = a * b * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by
          rw [show Wm α z θ * Wm α z θ = (Wm α z θ) ^ 2 by ring, hWm]
  have hcomm4 : Work.Spaces.pth (Work.Spaces.DzIter 4 g) z θ
      = Work.Spaces.DzIter 4 (Work.Spaces.pth g) z θ := by
    change Function.uncurry (Work.Spaces.pth (Work.Spaces.DzIter 4 g)) (z, θ)
      = Function.uncurry (Work.Spaces.DzIter 4 (Work.Spaces.pth g)) (z, θ)
    exact (pth_dzIter_eq g hg 4 hzr).symm
  have hDz : ∀ i : ℕ, Work.Spaces.DzIter i (fun z θ => f z θ * Work.Spaces.pth g z θ) z θ
      = ∑ b ∈ Finset.range (i + 1), (i.choose b : ℝ)
          * (Work.Spaces.DzIter b f z θ * Work.Spaces.DzIter (i - b) (Work.Spaces.pth g) z θ) :=
    fun i => Work.Spaces.DzIter_mul i f (Work.Spaces.pth g) hz (hsm.2 θ hθ) hslice_pg
  have hMx : ∀ j i : ℕ, Work.Spaces.mixed j i (fun z θ => f z θ * Work.Spaces.pth g z θ) z θ
      = ∑ a ∈ Finset.range (i + 1), ∑ b ∈ Finset.range (j + 1),
          ((i.choose a : ℝ) * (j.choose b : ℝ))
            * (Work.Spaces.mixed b a f z θ
              * Work.Spaces.mixed (j - b) (i - a) (Work.Spaces.pth g) z θ) :=
    fun j i => Work.Spaces.mixed_mul_eq j i f (Work.Spaces.pth g) hsm hSint z hz θ hθ
  simp only [H4PairInt, EZ, EM, EC, HardF, hprodW, hprodM, hcomm4, hDz, hMx,
    Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num
  ring


/-! ## Nonnegativity and the AM-GM read-off -/

theorem w_nonneg {z : ℝ} (hz : 0 ≤ z) : 0 ≤ Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_nonneg (sq_nonneg _) (sq_nonneg _)

private theorem Whz_nonneg {z θ : ℝ} (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Whz z θ := by
  rw [Whz_eq]
  exact div_nonneg (w_nonneg hz) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)

private theorem Wm_nonneg (α z θ : ℝ) (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Wm α z θ := by
  rw [Wm_eq, Work.Spaces.Wt, Work.Spaces.wTheta]
  exact mul_nonneg (w_nonneg hz) (Real.rpow_nonneg (sin_two_nonneg_Iθ hθ) _)

theorem rpow_eta_le_gam {α θ : ℝ} (hα : 0 < α) (hθ : θ ∈ Work.Spaces.Iθ) :
    (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)
      ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by
  have hS : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθ
  have hS1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
  have hgam : Work.Spaces.eta ≤ Work.Spaces.gam α := by
    rw [Work.Spaces.gam]
    have := Work.Spaces.eta_lt_one
    linarith
  rcases eq_or_lt_of_le hS with h0 | h0
  · rw [← h0,
      Real.zero_rpow (show (-Work.Spaces.eta) ≠ 0 by linarith [Work.Spaces.eta_pos]),
      Real.zero_rpow (show (-(Work.Spaces.gam α)) ≠ 0 by
        have := Work.Spaces.gam_pos hα; linarith)]
  · rw [show -Work.Spaces.eta = -(Work.Spaces.gam α) + (Work.Spaces.gam α - Work.Spaces.eta)
        by ring, Real.rpow_add h0]
    have h1 : (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - Work.Spaces.eta) ≤ 1 :=
      Real.rpow_le_one hS hS1 (by linarith)
    have h2 : 0 ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hS _
    calc (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
            * (Real.sin (2 * θ)) ^ (Work.Spaces.gam α - Work.Spaces.eta)
        ≤ (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) * 1 := mul_le_mul_of_nonneg_left h1 h2
      _ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)) := by ring

/-- The `η`-weighted slot pairing: a mixed slot against a pure `D_z`-slot. -/
theorem eta_pair_le {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hHk : Work.Spaces.HkMem α 4 g)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ)
    {m j j₂ : ℕ} (hm : 1 ≤ m) (hmj : m + j ≤ 4) (hj₂ : j₂ ≤ 4) :
    |Work.Spaces.mixed j m g z θ| * |Work.Spaces.DzIter j₂ g z θ|
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hWh := Whz_nonneg hz0 hθ
  have hs := (Whz_Wm_sq α hα z θ hθ).1
  have hX : |Work.Spaces.mixed j m g z θ| * |Work.Spaces.DzIter j₂ g z θ|
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      = |Work.Spaces.mixed j m g z θ * Whz z θ| * |Work.Spaces.DzIter j₂ g z θ * Whz z θ| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hWh, ← hs]
    ring
  rw [hX]
  have hA : (Work.Spaces.mixed j m g z θ * Wm α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    have h := Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ m j hm (by omega)
    rwa [← Work.FTS.H2.Wm_eq] at h
  have hA' : (Work.Spaces.mixed j m g z θ * Whz z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    have hle : (Whz z θ) ^ 2 ≤ (Wm α z θ) ^ 2 := by
      rw [hs, (Whz_Wm_sq α hα z θ hθ).2]
      exact mul_le_mul_of_nonneg_left (rpow_eta_le_gam hα hθ) (sq_nonneg _)
    have h2 : (Work.Spaces.mixed j m g z θ * Whz z θ) ^ 2
        ≤ (Work.Spaces.mixed j m g z θ * Wm α z θ) ^ 2 := by
      rw [mul_pow, mul_pow]
      exact mul_le_mul_of_nonneg_left hle (sq_nonneg _)
    exact le_trans h2 hA
  have hB : (Work.Spaces.DzIter j₂ g z θ * Whz z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.sq_le_HkIntegrand_z α 4 g z θ j₂ hj₂
  nlinarith [sq_nonneg (|Work.Spaces.mixed j m g z θ * Whz z θ|
      - |Work.Spaces.DzIter j₂ g z θ * Whz z θ|),
    sq_abs (Work.Spaces.mixed j m g z θ * Whz z θ),
    sq_abs (Work.Spaces.DzIter j₂ g z θ * Whz z θ), hA', hB]

/-- The `γ`-weighted slot pairing: two mixed slots. -/
theorem gam_pair_le {α : ℝ} {g : ℝ → ℝ → ℝ} (hα : 0 < α) (hHk : Work.Spaces.HkMem α 4 g)
    {z θ : ℝ} (hz : z ∈ Work.Spaces.Iz) (hθ : θ ∈ Work.Spaces.Iθ)
    {m₁ j₁ m₂ j₂ : ℕ} (h1 : 1 ≤ m₁) (h1' : m₁ + j₁ ≤ 4) (h2 : 1 ≤ m₂) (h2' : m₂ + j₂ ≤ 4) :
    |Work.Spaces.mixed j₁ m₁ g z θ| * |Work.Spaces.mixed j₂ m₂ g z θ|
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
  have hz0 : (0 : ℝ) ≤ z := hz
  have hWm := Wm_nonneg α z θ hz0 hθ
  have hs := (Whz_Wm_sq α hα z θ hθ).2
  have hX : |Work.Spaces.mixed j₁ m₁ g z θ| * |Work.Spaces.mixed j₂ m₂ g z θ|
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))
      = |Work.Spaces.mixed j₁ m₁ g z θ * Wm α z θ|
        * |Work.Spaces.mixed j₂ m₂ g z θ * Wm α z θ| := by
    rw [abs_mul, abs_mul, abs_of_nonneg hWm, ← hs]
    ring
  rw [hX]
  have hA : (Work.Spaces.mixed j₁ m₁ g z θ * Wm α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    have h := Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ m₁ j₁ h1 h1'
    rwa [← Work.FTS.H2.Wm_eq] at h
  have hB : (Work.Spaces.mixed j₂ m₂ g z θ * Wm α z θ) ^ 2
      ≤ Work.Spaces.HkIntegrand α 4 g z θ := by
    have h := Work.Spaces.sq_le_HkIntegrand_mixed α 4 g z θ m₂ j₂ h2 h2'
    rwa [← Work.FTS.H2.Wm_eq] at h
  nlinarith [sq_nonneg (|Work.Spaces.mixed j₁ m₁ g z θ * Wm α z θ|
      - |Work.Spaces.mixed j₂ m₂ g z θ * Wm α z θ|),
    sq_abs (Work.Spaces.mixed j₁ m₁ g z θ * Wm α z θ),
    sq_abs (Work.Spaces.mixed j₂ m₂ g z θ * Wm α z θ), hA, hB]

theorem choose_le_six (m b : ℕ) (hm : m ≤ 4) (hb : b ≤ m) : (m.choose b : ℝ) ≤ 6 := by
  have h : m.choose b ≤ 6 := by interval_cases m <;> interval_cases b <;> decide
  exact_mod_cast h

end Work.FTS.H2
