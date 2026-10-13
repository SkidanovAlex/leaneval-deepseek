import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Submission.Work.Coercivity.E2Slice.E2SliceDefs
import Submission.Work.Spaces.Gamma_WlInf
import Submission.Work.Coercivity.DthU_iter_Gam_all

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-- `D_θ`-iterates of a function of `θ` alone, viewed as a function of `(z,θ)`,
agree with the univariate iterates `Spaces.dthU^[i]`. -/
lemma DthIter_rad_eq (i : ℕ) (g : ℝ → ℝ) (z θ : ℝ) :
    Spaces.DthIter i (fun _ θ => g θ) z θ = Spaces.dthU^[i] g θ := by
  have h : (fun (_ : ℝ) (θ : ℝ) => g θ) = (fun (z : ℝ) (θ : ℝ) => g θ * (1 : ℝ)) := by
    funext z θ; ring
  rw [h, Spaces.DthIter_decomp]
  ring

/-- The sequence `Tfun j α` is bounded on `[0,1]`. -/
lemma Tfun_bdd_on (j : ℕ) (α : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ θ ∈ Set.Icc (0:ℝ) 1, |Spaces.Tfun j α θ| ≤ B := by
  have hcont : ContinuousOn (Spaces.Tfun j α) (Set.Icc (0:ℝ) 1) :=
    (Spaces.Tfun_smooth j α).continuous.continuousOn
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨max B 0, le_max_right _ _, fun θ hθ => ?_⟩
  have hle := hB θ hθ
  rw [Real.norm_eq_abs] at hle
  exact hle.trans (le_max_left _ _)

/-- `|Γ(θ)| ≤ C·θ^{α/3}` on `(0,1)`, for every real `α`.

Near `θ = 0` the angular weight `Γ(θ) = (sinθ·cos²θ)^{α/3}` is comparable to
`θ^{α/3}`; on the whole open interval `(0,1)` the quotient `Γ(θ)/θ^{α/3}` is
bounded (with a bound depending on `α`), which is exactly the statement. -/
lemma Gam_abs_le_rpow_theta (α : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0:ℝ) 1,
      |Spaces.Gam α θ| ≤ C * θ ^ (α / 3) := by
  have hcos1pos : 0 < Real.cos 1 := by
    apply Real.cos_pos_of_mem_Ioo
    constructor <;> linarith [Real.pi_gt_three]
  have hπpos : 0 < π := Real.pi_pos
  have hmpos : 0 < (2 / π) * Real.cos 1 ^ 2 := by positivity
  refine ⟨1 + ((2 / π) * Real.cos 1 ^ 2) ^ (α / 3), ?_, ?_⟩
  · exact add_pos_of_pos_of_nonneg zero_lt_one
      (le_of_lt (Real.rpow_pos_of_pos hmpos _))
  · intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hθ1 : θ < 1 := hθ.2
    have hθlt : θ < π / 2 := by linarith [hθ1, Real.pi_gt_three]
    have hsinpos : 0 < Real.sin θ :=
      Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_gt_three])
    set g : ℝ := Real.sinc θ * Real.cos θ ^ 2 with hgdef
    have hsinθ : Real.sinc θ = Real.sin θ / θ := Real.sinc_of_ne_zero (ne_of_gt hθ0)
    have hcosθpos : 0 < Real.cos θ :=
      Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_gt_three], hθlt⟩
    have hg0 : 0 < g := by
      rw [hgdef, hsinθ]
      exact mul_pos (div_pos hsinpos hθ0) (pow_pos hcosθpos 2)
    have hgle1 : g ≤ 1 := by
      rw [hgdef, hsinθ]
      have h1 : Real.sin θ / θ ≤ 1 := div_le_one_of_le₀ (Real.sin_le hθ0.le) hθ0.le
      have h2 : Real.cos θ ^ 2 ≤ 1 := by
        nlinarith [Real.cos_le_one θ, Real.neg_one_le_cos θ, sq_nonneg (Real.cos θ)]
      simpa using mul_le_mul h1 h2 (sq_nonneg _) zero_le_one
    have hmg : (2 / π) * Real.cos 1 ^ 2 ≤ g := by
      rw [hgdef, hsinθ]
      have hj := Real.mul_le_sin (le_of_lt hθ0) (le_of_lt hθlt)
      have hsinle : 2 / π ≤ Real.sin θ / θ := by
        rw [le_div_iff₀ hθ0]; exact hj
      have hcos1le : Real.cos 1 ≤ Real.cos θ :=
        Real.cos_le_cos_of_nonneg_of_le_pi hθ0.le (by linarith [Real.pi_gt_three]) hθ1.le
      have hcos2 : Real.cos 1 ^ 2 ≤ Real.cos θ ^ 2 := by
        nlinarith [hcos1le, hcos1pos, Real.cos_le_one θ, Real.neg_one_le_cos θ]
      exact mul_le_mul hsinle hcos2 (sq_nonneg _) (by positivity)
    have hθrpow0 : 0 ≤ θ ^ (α / 3) := Real.rpow_nonneg hθ0.le _
    have hbase : Real.sin θ * Real.cos θ ^ 2 = θ * g := by
      rw [hgdef, hsinθ]; field_simp
    have hGam_eq : Spaces.Gam α θ = θ ^ (α / 3) * g ^ (α / 3) := by
      rw [Spaces.Gam, hbase]
      exact Real.mul_rpow hθ0.le hg0.le
    have hgabs : |Spaces.Gam α θ| = θ ^ (α / 3) * g ^ (α / 3) := by
      rw [hGam_eq, abs_of_nonneg (mul_nonneg hθrpow0 (Real.rpow_nonneg hg0.le _))]
    have hgb : g ^ (α / 3) ≤ 1 + ((2 / π) * Real.cos 1 ^ 2) ^ (α / 3) := by
      rcases le_total (α / 3) 0 with hle | hge
      · have h := Real.rpow_le_rpow_of_nonpos hmpos hmg hle
        linarith
      · have h := Real.rpow_le_rpow hg0.le hgle1 hge
        rw [Real.one_rpow] at h
        linarith [h, Real.rpow_nonneg hmpos.le (α / 3)]
    calc |Spaces.Gam α θ| = θ ^ (α / 3) * g ^ (α / 3) := hgabs
      _ ≤ θ ^ (α / 3) * (1 + ((2 / π) * Real.cos 1 ^ 2) ^ (α / 3)) :=
            mul_le_mul_of_nonneg_left hgb hθrpow0
      _ = (1 + ((2 / π) * Real.cos 1 ^ 2) ^ (α / 3)) * θ ^ (α / 3) := by ring

theorem Gam_jet_upper_zero (α : ℝ) (i : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ ∈ Set.Ioo (0:ℝ) 1,
      |Spaces.DthIter i (fun _ θ => Spaces.Gam α θ) 0 θ| ≤ C * θ ^ (α / 3) := by
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · subst h0
    obtain ⟨C, hC, hle⟩ := Gam_abs_le_rpow_theta α
    exact ⟨C, hC, fun θ hθ => by simpa using hle θ hθ⟩
  · obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
    obtain ⟨Cg, hCg, hg⟩ := Gam_abs_le_rpow_theta α
    obtain ⟨B, hB0, hB⟩ := Tfun_bdd_on k α
    have hB1 : (0 : ℝ) ≤ B + 1 := by linarith
    refine ⟨|α| * (B + 1) * Cg + 1, ?_, fun θ hθ => ?_⟩
    · have hprod : (0 : ℝ) ≤ |α| * (B + 1) * Cg :=
        mul_nonneg (mul_nonneg (abs_nonneg α) hB1) hCg.le
      linarith
    · have hθpos : 0 < θ := hθ.1
      have hθlt : θ < π / 2 := by linarith [hθ.2, Real.pi_gt_three]
      have hident := DthU_iter_Gam_all k α (show θ ∈ Set.Ioo (0:ℝ) (π/2) from ⟨hθpos, hθlt⟩)
      rw [DthIter_rad_eq, hident, abs_mul, abs_mul]
      have hT : |Spaces.Tfun k α θ| ≤ B + 1 :=
        (hB θ ⟨hθpos.le, hθ.2.le⟩).trans (by linarith)
      have hGm : |Spaces.Gam α θ| ≤ Cg * θ ^ (α / 3) := hg θ hθ
      have hθrpow0 : 0 ≤ θ ^ (α / 3) := Real.rpow_nonneg hθpos.le _
      have hstep1 : |α| * |Spaces.Tfun k α θ| * |Spaces.Gam α θ|
          ≤ |α| * (B + 1) * (Cg * θ ^ (α / 3)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hT (abs_nonneg α)) hGm
          (abs_nonneg _) (mul_nonneg (abs_nonneg α) hB1)
      calc |α| * |Spaces.Tfun k α θ| * |Spaces.Gam α θ|
          ≤ |α| * (B + 1) * (Cg * θ ^ (α / 3)) := hstep1
        _ = (|α| * (B + 1) * Cg) * θ ^ (α / 3) := by ring
        _ ≤ (|α| * (B + 1) * Cg + 1) * θ ^ (α / 3) :=
              mul_le_mul_of_nonneg_right (by linarith) hθrpow0

end Work.Coercivity
