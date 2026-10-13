import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.PhiStar.Series.sum_bmode_eFam_eq
import Submission.Work.FTS.PhiStar.Series.bmode_decay15
import Submission.Work.FTS.PhiStar.Series.eFam_sup_le
import Submission.Work.FTS.PhiStar.Series.Conjunctions34
import Submission.Work.FTS.PhiStar.Series.RemSetup

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series.Weil

set_option autoImplicit false

/-!
# `Work.FTS.PhiStar.Series.Weil.bmodeUniform`

The partial sums `Σ_{m ≤ N} bmode m ψ · eFam m θ` of the angular eigen-expansion of a model
function `ψ` (`Work.FTS.PhiStar.AngModel α ψ`) are

* **uniformly bounded** on `Iθ`, and
* **uniformly convergent** to `ψ` on `Iθ`,

for `0 < α ≤ 1/5`.

Both statements follow from the single term majorant

  `|bmode m ψ · eFam m θ| ≤ Cd · Cg · (m+1)^{-3/2}`   (`m ≥ 1`),

which combines the coefficient decay `|bmode m ψ| ≤ Cd (m+1)^{-5/2}` (`bmode_decay_pow`, from
`bmode_decay15`) with the uniform growth bound `|eFam m θ| ≤ Cg (m+1)` on `Iθ`
(`eFam_sup_le`).  The `m = 0` term vanishes because `AngModel.moment` forces `bmode 0 ψ = 0`.
The majorant is summable (`(m+1)^{-3/2}`), giving the uniform bound; and its tails tend to `0`,
giving uniform convergence once the pointwise identity `Σ'_m bmode m ψ · eFam m θ = ψ θ` on the
*open* interval (`sum_bmode_eFam_eq`) is used for the interior points.  At the endpoints
`θ = 0, π/2` every `eFam m` vanishes (`eFam_zero_right`, `eFam_zero_left`) and so does `ψ`
(`AngModel.bdry0`, `AngModel.bdry1`), so the difference is exactly `0` there.
-/

/-! ## The mode majorant `Cd · Cg · (m+1)^{-3/2}` -/

/-- The majorant of the mode terms `|bmode m ψ · eFam m θ|`, dictated by the coefficient decay
`|bmode m ψ| ≲ (m+1)^{-5/2}` and the uniform growth `|eFam m θ| ≲ (m+1)`. -/
private def maj (Cd Cg : ℝ) (m : ℕ) : ℝ := Cd * Cg * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ))

private lemma maj_nonneg {Cd Cg : ℝ} (hCd : 0 ≤ Cd) (hCg : 0 ≤ Cg) (m : ℕ) :
    0 ≤ maj Cd Cg m := by
  change 0 ≤ Cd * Cg * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ))
  exact mul_nonneg (mul_nonneg hCd hCg) (Real.rpow_nonneg (by positivity) _)

private lemma maj_summable (Cd Cg : ℝ) : Summable (maj Cd Cg) := by
  change Summable (fun m : ℕ => Cd * Cg * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ)))
  exact (Work.FTS.PhiStar.Series.summable_one_add_rpow (3 / 2) (by norm_num)).mul_left
    (Cd * Cg)

private lemma abs_bmode_mul_eFam_le_maj {α : ℝ} {ψ : ℝ → ℝ} {Cd Cg : ℝ}
    (hψ : Work.FTS.PhiStar.AngModel α ψ) (hCd : 0 < Cd) (hCg : 0 < Cg)
    (hsup : ∀ (m : ℕ) (θ : ℝ), θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ Cg * ((m : ℝ) + 1))
    (hdec : ∀ m : ℕ, 1 ≤ m →
      |Work.FTS.PhiStar.Series.bmode m ψ| ≤ Cd * ((m : ℝ) + 1) ^ (-(5 / 2 : ℝ)))
    (m : ℕ) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      ≤ maj Cd Cg m := by
  change |Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
      ≤ Cd * Cg * ((m : ℝ) + 1) ^ (-(3 / 2 : ℝ))
  exact Work.FTS.PhiStar.Series.abs_bmode_mul_eFam_le_aux α ψ hψ hCg hCd hsup hdec m hθ

/-! ## The tails of a summable majorant tend to zero -/

private lemma tail_tsum_tendsto_zero {G : ℕ → ℝ} (hG : Summable G) :
    Tendsto (fun k : ℕ => ∑' i : ℕ, G (i + k)) atTop (𝓝 0) := by
  have hsum : Tendsto (fun k : ℕ => ∑ i ∈ Finset.range k, G i) atTop (𝓝 (∑' i : ℕ, G i)) :=
    hG.hasSum.tendsto_sum_nat
  have heq : (fun k : ℕ => ∑' i : ℕ, G (i + k))
      = fun k : ℕ => (∑' i : ℕ, G i) - ∑ i ∈ Finset.range k, G i := by
    funext k
    have h := hG.sum_add_tsum_nat_add k
    linarith
  rw [heq]
  have h2 : Tendsto (fun k : ℕ => (∑' i : ℕ, G i) - ∑ i ∈ Finset.range k, G i) atTop
      (𝓝 ((∑' i : ℕ, G i) - (∑' i : ℕ, G i))) :=
    tendsto_const_nhds.sub hsum
  simpa using h2

/-! ## The theorem -/

theorem bmodeUniform (α : ℝ) (ψ : ℝ → ℝ) (hα : 0 < α) (hα5 : α ≤ 1 / 5)
    (hψ : Work.FTS.PhiStar.AngModel α ψ) :
    (∃ M : ℝ, 0 < M ∧ ∀ N : ℕ, ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      |∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.bmode m ψ
        * Work.FTS.PhiStar.Gegenbauer.eFam m θ| ≤ M) ∧
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ θ : ℝ, θ ∈ Work.Spaces.Iθ →
      |(∑ m ∈ Finset.range (n + 1), Work.FTS.PhiStar.Series.bmode m ψ
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ) - ψ θ| ≤ ε) := by
  obtain ⟨Cg, hCg, hsup⟩ := Work.FTS.PhiStar.Series.eFam_sup_le
  obtain ⟨Cd, hCd, hdec⟩ := Work.FTS.PhiStar.Series.bmode_decay_pow α ψ hα hα5 hψ
  have hsum : Summable (maj Cd Cg) := maj_summable Cd Cg
  have hnn : ∀ m : ℕ, 0 ≤ maj Cd Cg m := fun m => maj_nonneg (le_of_lt hCd) (le_of_lt hCg) m
  have hterm : ∀ (m : ℕ) {θ : ℝ}, θ ∈ Work.Spaces.Iθ →
      |Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
        ≤ maj Cd Cg m :=
    fun m θ hθ => abs_bmode_mul_eFam_le_maj hψ hCd hCg hsup hdec m hθ
  refine ⟨?_, ?_⟩
  · refine ⟨(∑' m : ℕ, maj Cd Cg m) + 1, ?_, ?_⟩
    · have h0 : 0 ≤ ∑' m : ℕ, maj Cd Cg m := tsum_nonneg hnn
      linarith
    · intro N θ hθ
      have h1 : |∑ m ∈ Finset.range (N + 1), Work.FTS.PhiStar.Series.bmode m ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ|
          ≤ ∑ m ∈ Finset.range (N + 1), maj Cd Cg m := by
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
        intro m _
        exact hterm m hθ
      have h2 : ∑ m ∈ Finset.range (N + 1), maj Cd Cg m ≤ ∑' m : ℕ, maj Cd Cg m :=
        hsum.sum_le_tsum (Finset.range (N + 1)) (fun m _ => hnn m)
      linarith
  · intro ε hε
    have htail := tail_tsum_tendsto_zero hsum
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp htail ε hε
    have hN' : ∀ k : ℕ, N ≤ k → |∑' i : ℕ, maj Cd Cg (i + k)| < ε := by
      intro k hk
      have hk2 := hN k hk
      simpa only [Real.dist_eq, sub_zero] using hk2
    refine ⟨N, fun n hn θ hθ => ?_⟩
    have hmem : θ ∈ Work.Spaces.Iθ := hθ
    have hθ' : (0 : ℝ) ≤ θ ∧ θ ≤ Real.pi / 2 := by
      rw [Work.Spaces.Iθ] at hθ
      exact hθ
    rcases eq_or_lt_of_le hθ'.1 with h0 | h0
    · subst h0
      have hz : (∑ m ∈ Finset.range (n + 1),
          Work.FTS.PhiStar.Series.bmode m ψ * Work.FTS.PhiStar.Gegenbauer.eFam m 0) = 0 :=
        Finset.sum_eq_zero (fun m _ => by
          rw [Work.FTS.PhiStar.Series.eFam_zero_right m, mul_zero])
      rw [hz, hψ.bdry0, sub_zero, abs_zero]
      exact le_of_lt hε
    · rcases eq_or_lt_of_le hθ'.2 with h2 | h2
      · subst h2
        have hz : (∑ m ∈ Finset.range (n + 1),
            Work.FTS.PhiStar.Series.bmode m ψ
              * Work.FTS.PhiStar.Gegenbauer.eFam m (Real.pi / 2)) = 0 :=
          Finset.sum_eq_zero (fun m _ => by
            rw [Work.FTS.PhiStar.Series.eFam_zero_left m, mul_zero])
        rw [hz, hψ.bdry1, sub_zero, abs_zero]
        exact le_of_lt hε
      · have hpsi : (∑' m : ℕ, Work.FTS.PhiStar.Series.bmode m ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) = ψ θ :=
          Work.FTS.PhiStar.Series.sum_bmode_eFam_eq α ψ hα hψ ⟨Cg, hCg, hsup⟩
            ⟨Cd, hCd, hdec⟩ θ h0 h2
        have hsumθ : Summable (fun m : ℕ => Work.FTS.PhiStar.Series.bmode m ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam m θ) :=
          Summable.of_norm_bounded hsum (fun m => by
            rw [Real.norm_eq_abs]
            exact hterm m hmem)
        have hsplit := hsumθ.sum_add_tsum_nat_add (n + 1)
        have hdiff : (∑ m ∈ Finset.range (n + 1), Work.FTS.PhiStar.Series.bmode m ψ
              * Work.FTS.PhiStar.Gegenbauer.eFam m θ) - ψ θ
            = -(∑' i : ℕ, Work.FTS.PhiStar.Series.bmode (i + (n + 1)) ψ
              * Work.FTS.PhiStar.Gegenbauer.eFam (i + (n + 1)) θ) := by
          rw [← hpsi]
          linarith
        rw [hdiff, abs_neg]
        have hshift : Summable (fun i : ℕ => maj Cd Cg (i + (n + 1))) :=
          hsum.comp_injective (fun a b hab => Nat.add_right_cancel hab)
        have hnorms : Summable (fun i : ℕ => ‖Work.FTS.PhiStar.Series.bmode (i + (n + 1)) ψ
            * Work.FTS.PhiStar.Gegenbauer.eFam (i + (n + 1)) θ‖) :=
          Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => by
            rw [Real.norm_eq_abs]
            exact hterm _ hmem) hshift
        calc |∑' i : ℕ, Work.FTS.PhiStar.Series.bmode (i + (n + 1)) ψ
              * Work.FTS.PhiStar.Gegenbauer.eFam (i + (n + 1)) θ|
            = ‖∑' i : ℕ, Work.FTS.PhiStar.Series.bmode (i + (n + 1)) ψ
                * Work.FTS.PhiStar.Gegenbauer.eFam (i + (n + 1)) θ‖ :=
              (Real.norm_eq_abs _).symm
          _ ≤ ∑' i : ℕ, ‖Work.FTS.PhiStar.Series.bmode (i + (n + 1)) ψ
                * Work.FTS.PhiStar.Gegenbauer.eFam (i + (n + 1)) θ‖ :=
              norm_tsum_le_tsum_norm hnorms
          _ ≤ ∑' i : ℕ, maj Cd Cg (i + (n + 1)) :=
              Summable.tsum_le_tsum (fun i => by
                rw [Real.norm_eq_abs]
                exact hterm _ hmem) hnorms hshift
          _ ≤ ε := by
              have hlt : |∑' i : ℕ, maj Cd Cg (i + (n + 1))| < ε := hN' (n + 1) (by omega)
              calc ∑' i : ℕ, maj Cd Cg (i + (n + 1))
                  ≤ |∑' i : ℕ, maj Cd Cg (i + (n + 1))| := le_abs_self _
                _ ≤ ε := le_of_lt hlt

end Work.FTS.PhiStar.Series.Weil
