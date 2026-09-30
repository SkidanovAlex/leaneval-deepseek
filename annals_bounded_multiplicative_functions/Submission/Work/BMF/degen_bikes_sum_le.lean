import Mathlib
import Submission.Work.BMF.good_bike_aux
import Submission.Work.BMF.adi_count
import Submission.Work.BMF.degen_closedWalkAll_le
import Submission.Work.BMF.edges_card_le
import Submission.Work.BMF.primesIn_half_card_le_all

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset Real

/-- `(π₀ P ^ 2)^{2ℓ+1} = π₀ P^{2ℓ} · π₀ P^{2ℓ} · π₀ P²`. -/
private lemma pi0_sq_pow (P : ℝ) (ℓ : ℕ) :
    (pi0 P ^ 2) ^ (2 * ℓ + 1) = pi0 P ^ (2 * ℓ) * pi0 P ^ (2 * ℓ) * pi0 P ^ 2 := by
  rw [← pow_mul, show 2 * (2 * ℓ + 1) = 2 * ℓ + (2 * ℓ + 2) by ring, pow_add, pow_add]
  ring

theorem degen_bikes_sum_le (k ℓ : ℕ) (hℓ : 2 ≤ ℓ) :
    ∃ C P₀ : ℝ, 0 < C ∧ 0 < P₀ ∧ ∀ (f : ℕ → ℂ) (c Cq X L P₁ P₂ c₅ : ℝ)
      (D : Work.BMF.QuadData k f c Cq X L P₁ P₂),
      P₀ ≤ P₁ → 0 < P₁ → 2 ≤ P₂ → 0 < L → 0 < X → 8000 * P₁ ^ 2 < X / L →
      3 ≤ X / L → X / L ≤ P₁ ^ (ℓ - 1) → 1 / Real.log P₁ ≤ c₅ →
      ∑ q ∈ Work.BMF.primesIn (P₂ / 2) P₂, ((Work.BMF.degenBikes D ℓ (X / L) c₅ q).card : ℝ)
        ≤ C * c₅ * Work.BMF.pi0 P₂ * (Work.BMF.pi0 P₁ ^ 2) ^ (2 * ℓ + 1) / (X / L) := by
  obtain ⟨Cw, Pw, hCw, hPw, hwalk⟩ := degenWalks_card_le k ℓ hℓ
  obtain ⟨Cv, Pv, hCv, hPv, hval⟩ := closedWalkVal_card_le k ℓ hℓ
  obtain ⟨Ce, Pe, hCe, hPe, hedge⟩ := edges_card_le_NR k
  obtain ⟨Cp, hCp, hprimes⟩ := primesIn_half_card_le_all
  refine ⟨2 * Cw * Cv * Ce * Cp, max (max Pw Pv) (max Pe 3), by positivity,
    lt_of_lt_of_le hPw (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro f c Cq X L P₁ P₂ c₅ D hP₀ hP₁ hP₂ hL hX hbig hN3 hNle hc₅
  have hPw' : Pw ≤ P₁ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hP₀
  have hPv' : Pv ≤ P₁ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hP₀
  have hPe' : Pe ≤ P₁ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hP₀
  have hP₁3 : (3 : ℝ) ≤ P₁ := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hP₀
  have hNpos : 0 < X / L := div_pos hX hL
  have hNne : X / L ≠ 0 := ne_of_gt hNpos
  have hpi1 : 0 < pi0 P₁ := pi0_pos (by linarith)
  have hpi1nn : 0 ≤ pi0 P₁ := hpi1.le
  have hpi2 : 0 < pi0 P₂ := pi0_pos hP₂
  set A : ℝ := Cw * c₅ * pi0 P₁ ^ (2 * ℓ) / (X / L) with hAdef
  set B : ℝ := Cv * pi0 P₁ ^ (2 * ℓ) / (X / L) with hBdef
  have hW : ∀ q x, ((degenWalks D ℓ (X / L) c₅ q x).card : ℝ) ≤ A :=
    fun q x => hwalk f c Cq X L P₁ P₂ c₅ D q x hPw' hP₁ hL hX hN3 hNle hc₅
  have hV : ∀ q x, ((closedWalkVal D q ℓ x).card : ℝ) ≤ B :=
    fun q x => hval f c Cq X L P₁ P₂ D q x hPv' hP₁ hL hX hN3 hNle
  have hE : (D.edges.card : ℝ) ≤ Ce * pi0 P₁ ^ 2 * (X / L) :=
    hedge f c Cq X L P₁ P₂ D hPe' hP₁ hL hX hbig hN3
  have hPr : ((primesIn (P₂ / 2) P₂).card : ℝ) ≤ Cp * pi0 P₂ := hprimes P₂ hP₂
  have hA0 : 0 ≤ A := le_trans (Nat.cast_nonneg _) (hW 0 0)
  have hB0 : 0 ≤ B := le_trans (Nat.cast_nonneg _) (hV 0 0)
  have hAB0 : 0 ≤ 2 * A * B := by positivity
  have hErhs0 : 0 ≤ Ce * pi0 P₁ ^ 2 * (X / L) := by positivity
  -- per-`q` bound
  have hq : ∀ q : ℕ, ((degenBikes D ℓ (X / L) c₅ q).card : ℝ) ≤
      (2 * A * B) * ((D.edges.filter (fun e => q ∈ edgeS D e)).card : ℝ) := by
    intro q
    have h1 : (degenBikes D ℓ (X / L) c₅ q).card ≤
        ∑ e ∈ D.edges.filter (fun e => q ∈ edgeS D e),
          ((degenWalks D ℓ (X / L) c₅ q e.x₁).card * (closedWalkVal D q ℓ e.x₂).card +
           (closedWalkVal D q ℓ e.x₁).card * (degenWalks D ℓ (X / L) c₅ q e.x₂).card) :=
      card_degenBikes_le D ℓ (X / L) c₅ q
    have h1R : ((degenBikes D ℓ (X / L) c₅ q).card : ℝ) ≤
        ((∑ e ∈ D.edges.filter (fun e => q ∈ edgeS D e),
          ((degenWalks D ℓ (X / L) c₅ q e.x₁).card * (closedWalkVal D q ℓ e.x₂).card +
           (closedWalkVal D q ℓ e.x₁).card * (degenWalks D ℓ (X / L) c₅ q e.x₂).card) : ℕ) : ℝ) := by
      exact_mod_cast h1
    have hsum : ((∑ e ∈ D.edges.filter (fun e => q ∈ edgeS D e),
          ((degenWalks D ℓ (X / L) c₅ q e.x₁).card * (closedWalkVal D q ℓ e.x₂).card +
           (closedWalkVal D q ℓ e.x₁).card * (degenWalks D ℓ (X / L) c₅ q e.x₂).card) : ℕ) : ℝ)
        ≤ (2 * A * B) * ((D.edges.filter (fun e => q ∈ edgeS D e)).card : ℝ) := by
      rw [Nat.cast_sum]
      calc ∑ e ∈ D.edges.filter (fun e => q ∈ edgeS D e),
              (((degenWalks D ℓ (X / L) c₅ q e.x₁).card * (closedWalkVal D q ℓ e.x₂).card +
               (closedWalkVal D q ℓ e.x₁).card * (degenWalks D ℓ (X / L) c₅ q e.x₂).card : ℕ) : ℝ)
          ≤ ∑ _e ∈ D.edges.filter (fun e => q ∈ edgeS D e), (2 * A * B) := by
            refine Finset.sum_le_sum (fun e _ => ?_)
            have t1 : ((degenWalks D ℓ (X / L) c₅ q e.x₁).card : ℝ)
                * ((closedWalkVal D q ℓ e.x₂).card : ℝ) ≤ A * B :=
              mul_le_mul (hW q e.x₁) (hV q e.x₂) (Nat.cast_nonneg _) hA0
            have t2 : ((closedWalkVal D q ℓ e.x₁).card : ℝ)
                * ((degenWalks D ℓ (X / L) c₅ q e.x₂).card : ℝ) ≤ A * B := by
              rw [mul_comm ((closedWalkVal D q ℓ e.x₁).card : ℝ)
                ((degenWalks D ℓ (X / L) c₅ q e.x₂).card : ℝ)]
              exact mul_le_mul (hW q e.x₂) (hV q e.x₁) (Nat.cast_nonneg _) hA0
            push_cast
            linarith
        _ = (2 * A * B) * ((D.edges.filter (fun e => q ∈ edgeS D e)).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
            ring
    linarith
  -- summation over `q`
  have hsumq : ∑ q ∈ primesIn (P₂ / 2) P₂, ((degenBikes D ℓ (X / L) c₅ q).card : ℝ)
      ≤ (2 * A * B) * ((D.edges.card : ℝ) * ((primesIn (P₂ / 2) P₂).card : ℝ)) := by
    calc ∑ q ∈ primesIn (P₂ / 2) P₂, ((degenBikes D ℓ (X / L) c₅ q).card : ℝ)
        ≤ ∑ q ∈ primesIn (P₂ / 2) P₂,
            (2 * A * B) * ((D.edges.filter (fun e => q ∈ edgeS D e)).card : ℝ) :=
          Finset.sum_le_sum (fun q _ => hq q)
      _ = (2 * A * B) * ∑ q ∈ primesIn (P₂ / 2) P₂,
            ((D.edges.filter (fun e => q ∈ edgeS D e)).card : ℝ) := by
          rw [Finset.mul_sum]
      _ ≤ (2 * A * B) * ((D.edges.card : ℝ) * ((primesIn (P₂ / 2) P₂).card : ℝ)) := by
          refine mul_le_mul_of_nonneg_left (sum_edgesS_le D) hAB0
  have hfinal : (2 * A * B) * ((Ce * pi0 P₁ ^ 2 * (X / L)) * (Cp * pi0 P₂))
      = 2 * Cw * Cv * Ce * Cp * c₅ * pi0 P₂ * (pi0 P₁ ^ 2) ^ (2 * ℓ + 1) / (X / L) := by
    rw [hAdef, hBdef, pi0_sq_pow]
    field_simp
  calc ∑ q ∈ primesIn (P₂ / 2) P₂, ((degenBikes D ℓ (X / L) c₅ q).card : ℝ)
      ≤ (2 * A * B) * ((D.edges.card : ℝ) * ((primesIn (P₂ / 2) P₂).card : ℝ)) := hsumq
    _ ≤ (2 * A * B) * ((Ce * pi0 P₁ ^ 2 * (X / L)) * (Cp * pi0 P₂)) := by
        refine mul_le_mul_of_nonneg_left ?_ hAB0
        exact mul_le_mul hE hPr (Nat.cast_nonneg _) hErhs0
    _ = 2 * Cw * Cv * Ce * Cp * c₅ * pi0 P₂ * (pi0 P₁ ^ 2) ^ (2 * ℓ + 1) / (X / L) := hfinal

end Work.BMF
