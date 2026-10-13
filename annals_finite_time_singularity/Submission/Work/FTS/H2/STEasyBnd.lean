import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.STEasyId

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

/-- The per-term bound for the `D_z`-slot remainder. -/
theorem Z_term_le {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothInt f)
    (hcont : ContinuousOn (Function.uncurry f) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hvt : Work.Spaces.VanishTheta f) (hα : 0 < α) (hα1 : α ≤ 1)
    (hWl : Work.Spaces.WlInfMem α 4 (Work.Spaces.pth f))
    (hHk : Work.Spaces.HkMem α 4 g)
    {z θ : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ)) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    {m b : ℕ} (hbm : b ≤ m) (hm4 : m ≤ 4) (hnot : ¬ (m = 4 ∧ b = 0)) :
    |(m.choose b : ℝ)| * |Work.Spaces.DzIter b f z θ|
        * |Work.Spaces.DzIter (m - b) (Work.Spaces.pth g) z θ|
        * |Work.Spaces.DzIter m g z θ|
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
      ≤ 60000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
        * Work.Spaces.HkIntegrand α 4 g z θ := by
  have hzI : z ∈ Work.Spaces.Iz := Set.mem_Ici.mpr hz.le
  have hθIθ : θ ∈ Work.Spaces.Iθ := ⟨hθ.1.le, hθ.2.le⟩
  have hS : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg_Iθ hθIθ
  have hWnn : 0 ≤ Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := WlInf_nonneg hWl
  have hHkI : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  have hpair_s : ∀ c : ℕ,
      Real.sin (2 * θ) * |Work.Spaces.DzIter c (Work.Spaces.pth g) z θ|
        = |Work.Spaces.mixed c 1 g z θ| := by
    intro c
    rw [← abs_of_nonneg hS, ← abs_mul]
    exact congrArg abs (sin_mul_dzIter_pth g c z θ)
  rcases Nat.eq_zero_or_pos b with hb0 | hbpos
  · subst hb0
    have hcoef : |(m.choose 0 : ℝ)| = 1 := by rw [Nat.choose_zero_right]; norm_num
    have hm3 : m ≤ 3 := by
      rcases eq_or_ne m 4 with h | h
      · exact absurd ⟨h, rfl⟩ hnot
      · omega
    have hf1 : |Work.Spaces.DzIter 0 f z θ| ≤ 10000 * Real.sin (2 * θ)
        * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) :=
      abs_DzIter_f_le hsm hcont hvt hWl 0 (by norm_num) z hz θ hθIθ
    have hs := hpair_s m
    have hpair : |Work.Spaces.mixed m 1 g z θ| * |Work.Spaces.DzIter m g z θ|
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      eta_pair_le hα hHk hzI hθIθ (m := 1) (j := m) (j₂ := m) (by norm_num) (by omega)
        (by omega)
    have hstep : |(m.choose 0 : ℝ)| * |Work.Spaces.DzIter 0 f z θ|
        ≤ 10000 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := by
      rw [hcoef, one_mul]
      exact hf1
    calc |(m.choose 0 : ℝ)| * |Work.Spaces.DzIter 0 f z θ|
          * |Work.Spaces.DzIter (m - 0) (Work.Spaces.pth g) z θ|
          * |Work.Spaces.DzIter m g z θ|
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        = (|(m.choose 0 : ℝ)| * |Work.Spaces.DzIter 0 f z θ|)
          * (|Work.Spaces.DzIter (m - 0) (Work.Spaces.pth g) z θ|
            * |Work.Spaces.DzIter m g z θ|
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) := by ring
      _ ≤ (10000 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f))
          * (|Work.Spaces.DzIter (m - 0) (Work.Spaces.pth g) z θ|
            * |Work.Spaces.DzIter m g z θ|
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = 10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
          * (Real.sin (2 * θ) * |Work.Spaces.DzIter (m - 0) (Work.Spaces.pth g) z θ|
            * |Work.Spaces.DzIter m g z θ|
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) := by ring
      _ = 10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
          * (|Work.Spaces.mixed m 1 g z θ| * |Work.Spaces.DzIter m g z θ|
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) := by
          simp only [Nat.sub_zero]
          rw [← hs]
      _ ≤ 10000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
          * Work.Spaces.HkIntegrand α 4 g z θ :=
          mul_le_mul_of_nonneg_left hpair (by positivity)
      _ ≤ 60000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
          * Work.Spaces.HkIntegrand α 4 g z θ := by
          nlinarith [hWnn, hHkI]
  · have hcoef : |(m.choose b : ℝ)| ≤ 6 := by
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      exact choose_le_six m b hm4 hbm
    have hmb : m - b ≤ 3 := by omega
    have hf1 : |Work.Spaces.DzIter b f z θ| ≤ 10000 * Real.sin (2 * θ)
        * Work.Spaces.WlInf α 4 (Work.Spaces.pth f) :=
      abs_DzIter_f_le hsm hcont hvt hWl b (by omega) z hz θ hθIθ
    have hs := hpair_s (m - b)
    have hpair : |Work.Spaces.mixed (m - b) 1 g z θ| * |Work.Spaces.DzIter m g z θ|
        * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
      eta_pair_le hα hHk hzI hθIθ (m := 1) (j := m - b) (j₂ := m) (by norm_num) (by omega)
        (by omega)
    have hstep : |(m.choose b : ℝ)| * |Work.Spaces.DzIter b f z θ|
        ≤ 6 * (10000 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)) :=
      mul_le_mul hcoef hf1 (abs_nonneg _) (by norm_num)
    calc |(m.choose b : ℝ)| * |Work.Spaces.DzIter b f z θ|
          * |Work.Spaces.DzIter (m - b) (Work.Spaces.pth g) z θ|
          * |Work.Spaces.DzIter m g z θ|
          * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))
        = (|(m.choose b : ℝ)| * |Work.Spaces.DzIter b f z θ|)
          * (|Work.Spaces.DzIter (m - b) (Work.Spaces.pth g) z θ|
            * |Work.Spaces.DzIter m g z θ|
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) := by ring
      _ ≤ (6 * (10000 * Real.sin (2 * θ) * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)))
          * (|Work.Spaces.DzIter (m - b) (Work.Spaces.pth g) z θ|
            * |Work.Spaces.DzIter m g z θ|
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) :=
          mul_le_mul_of_nonneg_right hstep (by positivity)
      _ = 60000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
          * (Real.sin (2 * θ) * |Work.Spaces.DzIter (m - b) (Work.Spaces.pth g) z θ|
            * |Work.Spaces.DzIter m g z θ|
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) := by ring
      _ = 60000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
          * (|Work.Spaces.mixed (m - b) 1 g z θ| * |Work.Spaces.DzIter m g z θ|
            * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta))) := by
          rw [← hs]
      _ ≤ 60000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
          * Work.Spaces.HkIntegrand α 4 g z θ :=
          mul_le_mul_of_nonneg_left hpair (by positivity)

theorem EZ_bound {α : ℝ} {f g : ℝ → ℝ → ℝ}
    (hsm : Work.Spaces.SmoothInt f)
    (hcont : ContinuousOn (Function.uncurry f) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hvt : Work.Spaces.VanishTheta f) (hα : 0 < α) (hα1 : α ≤ 1)
    (hWl : Work.Spaces.WlInfMem α 4 (Work.Spaces.pth f))
    (hHk : Work.Spaces.HkMem α 4 g) {z θ : ℝ} (hz : z ∈ Set.Ioi (0 : ℝ))
    (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    |EZ f g z θ|
      ≤ 1500000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
        * Work.Spaces.HkIntegrand α 4 g z θ := by
  have hWnn : 0 ≤ Work.Spaces.WlInf α 4 (Work.Spaces.pth f) := WlInf_nonneg hWl
  have hHkI : 0 ≤ Work.Spaces.HkIntegrand α 4 g z θ :=
    Work.Spaces.HkIntegrand_nonneg α 4 g z θ
  rw [EZ]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hterm : ∀ m ∈ Finset.range 5, ∀ b ∈ Finset.range (m + 1),
      |(if m = 4 ∧ b = 0 then 0 else (m.choose b : ℝ)) *
        (Work.Spaces.DzIter b f z θ * Work.Spaces.DzIter (m - b) (Work.Spaces.pth g) z θ
          * Work.Spaces.DzIter m g z θ) * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)|
        ≤ 60000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
          * Work.Spaces.HkIntegrand α 4 g z θ := by
    intro m hm b hb
    have hbm : b ≤ m := by
      have := Finset.mem_range.mp hb
      omega
    have hm4 : m ≤ 4 := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
    have hwnn : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
    have hSn : 0 ≤ (Real.sin (2 * θ)) ^ (-Work.Spaces.eta) :=
      Real.rpow_nonneg (sin_two_nonneg_Iθ ⟨hθ.1.le, hθ.2.le⟩) _
    by_cases hcase : m = 4 ∧ b = 0
    · rw [if_pos hcase, zero_mul, zero_mul, zero_mul, abs_zero]
      positivity
    · rw [if_neg hcase]
      refine le_trans (le_of_eq ?_) (Z_term_le hsm hcont hvt hα hα1 hWl hHk hz hθ hbm hm4 hcase)
      simp only [abs_mul, abs_of_nonneg hwnn, abs_of_nonneg hSn]
      ring
  calc ∑ m ∈ Finset.range 5, |∑ b ∈ Finset.range (m + 1),
        (if m = 4 ∧ b = 0 then 0 else (m.choose b : ℝ)) *
          (Work.Spaces.DzIter b f z θ * Work.Spaces.DzIter (m - b) (Work.Spaces.pth g) z θ
            * Work.Spaces.DzIter m g z θ) * (Work.Spaces.w z) ^ 2
          * (Real.sin (2 * θ)) ^ (-Work.Spaces.eta)|
      ≤ ∑ m ∈ Finset.range 5, ((m + 1 : ℕ) : ℝ)
          * (60000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
            * Work.Spaces.HkIntegrand α 4 g z θ) := by
        refine Finset.sum_le_sum fun m hm => ?_
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine le_trans (Finset.sum_le_card_nsmul _ _ _ (fun b hb => hterm m hm b hb)) ?_
        rw [Finset.card_range, nsmul_eq_mul]
    _ ≤ ∑ _m ∈ Finset.range 5, (5 * (60000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
            * Work.Spaces.HkIntegrand α 4 g z θ)) := by
        refine Finset.sum_le_sum fun m hm => ?_
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        have : m + 1 ≤ 5 := by
          have := Finset.mem_range.mp hm
          omega
        exact_mod_cast this
    _ = 5 * (5 * (60000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
            * Work.Spaces.HkIntegrand α 4 g z θ)) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
        norm_num
    _ = 1500000 * Work.Spaces.WlInf α 4 (Work.Spaces.pth f)
        * Work.Spaces.HkIntegrand α 4 g z θ := by ring


end Work.FTS.H2
