import Mathlib
import Submission.Work.FIArea4.A6R2.Defs
import Submission.Work.FIArea4.A6R2.EvGSupport
import Submission.Work.FIArea4.p14_uncond
import Submission.Work.FIArea4.S15red.EvarG_filtered_strU_defs
import Submission.Work.S15crux.prelude
import Submission.Work.FIArea4.A6R2.stratumDsetLe
import Submission.Work.FIArea4.A6R.enerQuad6
import Submission.Work.FIArea4.kBracketSum6c

namespace Work.FIArea4.A6R

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

private lemma p14Ener_nonneg (R S : ℕ) (α : ℕ → ℕ → ℂ) : 0 ≤ Work.FIArea4.p14Ener R S α := by
  unfold Work.FIArea4.p14Ener
  exact Finset.sum_nonneg (fun r _ => Finset.sum_nonneg (fun s _ =>
    mul_nonneg (Nat.cast_nonneg _) (Complex.normSq_nonneg _)))

private lemma S15Br6_nonneg' (Pa : Work.FITop.Params) (X : ℕ) : 0 ≤ Work.FIArea4.S15Br6 Pa X := by
  unfold Work.FIArea4.S15Br6
  have hN0 : (0:ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hX0 : (0:ℝ) ≤ (X:ℝ) := Nat.cast_nonneg X
  have h1 : 0 ≤ (X:ℝ)^(-(1:ℝ)/2) * Pa.N := mul_nonneg (Real.rpow_nonneg hX0 _) hN0
  have h2 : 0 ≤ Pa.N^((1:ℝ)/3) * (X:ℝ)^(-(1:ℝ)/3) * Pa.N^((2:ℝ)/3) :=
    mul_nonneg (mul_nonneg (Real.rpow_nonneg hN0 _) (Real.rpow_nonneg hX0 _))
      (Real.rpow_nonneg hN0 _)
  have h3 : 0 ≤ Pa.N^((23:ℝ)/24 + (1:ℝ)/1000) := Real.rpow_nonneg hN0 _
  linarith

private lemma S15Br6_ge_mid' (Pa : Work.FITop.Params) (X : ℕ) :
    (Pa.N)^((1:ℝ)/3) * (X:ℝ)^(-(1:ℝ)/3) * (Pa.N)^((2:ℝ)/3) ≤ Work.FIArea4.S15Br6 Pa X := by
  unfold Work.FIArea4.S15Br6
  have hN0 : (0:ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hX0 : (0:ℝ) ≤ (X:ℝ) := Nat.cast_nonneg X
  have h1 : 0 ≤ (X:ℝ)^(-(1:ℝ)/2) * Pa.N := mul_nonneg (Real.rpow_nonneg hX0 _) hN0
  have h3 : 0 ≤ Pa.N^((23:ℝ)/24 + (1:ℝ)/1000) := Real.rpow_nonneg hN0 _
  linarith

private lemma midnonneg (Pa : Work.FITop.Params) (X : ℕ) :
    0 ≤ (Pa.N)^((1:ℝ)/3) * (X:ℝ)^(-(1:ℝ)/3) * (Pa.N)^((2:ℝ)/3) := by
  have hN0 : (0:ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hX0 : (0:ℝ) ≤ (X:ℝ) := Nat.cast_nonneg X
  exact mul_nonneg (mul_nonneg (Real.rpow_nonneg hN0 _) (Real.rpow_nonneg hX0 _))
    (Real.rpow_nonneg hN0 _)

theorem strUvarSum6 : Work.FIArea4.A6R2.strUvarSum6 := by
  classical
  obtain ⟨Cp, hCp_pos, hCp⟩ := Work.FIArea4.p14_all ((1:ℝ)/4000) (by norm_num)
  obtain ⟨C2, hC2_pos, hC2⟩ := Work.FIArea4.kBracketSum6c
  obtain ⟨Ce, hCe_pos, hCe⟩ := enerQuad6
  refine ⟨32 * Cp * C2 * Ce, 0, by positivity, ?_⟩
  intro Pa _hx X j φ β ℓ u t hβ hX hX9
  have hL0 : (0:ℝ) ≤ (Real.log Pa.N + 1)^4 := by positivity
  have hBr0 : 0 ≤ Work.FIArea4.S15Br6 Pa X := S15Br6_nonneg' Pa X
  have hmid0 : 0 ≤ (Pa.N)^((1:ℝ)/3) * (X:ℝ)^(-(1:ℝ)/3) * (Pa.N)^((2:ℝ)/3) := midnonneg Pa X
  have hA0 : (0:ℝ) ≤ Work.FIArea4.A6Ener3 Pa β := Work.FIArea4.A6Ener3_nonneg Pa β
  have hEnr_nn : ∀ e : ℕ, 0 ≤ ∑ σ ∈ Work.FIArea4.S15red.Q,
      Work.FIArea4.p14Ener (Work.FIArea4.S15red.ReK Pa e) (Work.FIArea4.S15red.SeK Pa)
        (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa)
          (Work.FIArea4.S15strU β u t ℓ e) σ.1 σ.2) :=
    fun e => Finset.sum_nonneg (fun σ _ => p14Ener_nonneg _ _ _)
  have hE : ∀ σ ∈ Work.FIArea4.S15red.Q,
      (∑ e ∈ Finset.Icc 1 (Work.FIArea4.S15Y Pa X j),
          Work.FIArea4.p14Ener (Work.FIArea4.S15red.ReK Pa e) (Work.FIArea4.S15red.SeK Pa)
            (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa)
              (Work.FIArea4.S15strU β u t ℓ e) σ.1 σ.2))
        ≤ Ce * Work.FIArea4.A6Ener3 Pa β := by
    intro σ hσ
    obtain ⟨h1, h2⟩ := Work.FIArea4.S15red.Q_spec hσ
    have h := hCe Pa X j φ β u t ℓ σ.1 σ.2 hβ hX h1 h2
    simpa only [Work.FIArea4.S15red.KK, Work.FIArea4.S15red.ReK, Work.FIArea4.S15red.SeK,
      Work.FIArea4.S15EG_K, Work.FIArea4.S15EG_Re, Work.FIArea4.S15EG_Se] using h
  have hper : ∀ e ∈ Finset.Icc 1 (Work.FIArea4.S15Y Pa X j),
      (∑ d' ∈ Work.S15crux.dset Pa X j e,
          Work.FIArea4.EvarG (Work.FITop.radN Pa) (4 * d')
            (Work.FIArea4.S15strU β u t ℓ e))
        ≤ 4 * Cp * (C2 * ((Real.log Pa.N + 1)^4 *
              (Work.FIArea4.S15Br6 Pa X
                + (Pa.N)^((1:ℝ)/3) * (X:ℝ)^(-(1:ℝ)/3) * (Pa.N)^((2:ℝ)/3))))
            * (∑ σ ∈ Work.FIArea4.S15red.Q,
                Work.FIArea4.p14Ener (Work.FIArea4.S15red.ReK Pa e)
                  (Work.FIArea4.S15red.SeK Pa)
                  (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa)
                    (Work.FIArea4.S15strU β u t ℓ e) σ.1 σ.2)) := by
    intro e he
    obtain ⟨he1, _heY⟩ := Finset.mem_Icc.mp he
    have hstr := Work.FIArea4.A6R2.stratumDsetLe Cp ((1:ℝ)/4000) hCp Pa X j e φ β ℓ u t hβ hX he1
    have hB := hC2 Pa X j e hX hX9 he1
    have he1' : (1:ℝ) ≤ (e:ℝ) := by exact_mod_cast he1
    have heinv : (e:ℝ)^(-(1:ℝ)) ≤ 1 := by
      rw [Real.rpow_neg_one]; exact inv_le_one_of_one_le₀ he1'
    have hBB : Work.FIArea4.S15Br6 Pa X
          + (Pa.N)^((1:ℝ)/3) * (X:ℝ)^(-(1:ℝ)/3) * (Pa.N)^((2:ℝ)/3) * (e:ℝ)^(-(1:ℝ))
        ≤ Work.FIArea4.S15Br6 Pa X
          + (Pa.N)^((1:ℝ)/3) * (X:ℝ)^(-(1:ℝ)/3) * (Pa.N)^((2:ℝ)/3) := by
      have h := mul_le_mul_of_nonneg_left heinv hmid0
      linarith [h]
    have hB' : (∑ k ∈ Work.S15crux.kset Pa X j e,
          Work.FIArea4.p14Bracket (2 ^ k) (Work.FIArea4.S15red.ReK Pa e)
            (Work.FIArea4.S15red.SeK Pa) ((1:ℝ)/4000))
        ≤ C2 * ((Real.log Pa.N + 1)^4 *
            (Work.FIArea4.S15Br6 Pa X
              + (Pa.N)^((1:ℝ)/3) * (X:ℝ)^(-(1:ℝ)/3) * (Pa.N)^((2:ℝ)/3))) := by
      refine le_trans hB ?_
      rw [show C2 * (Real.log Pa.N + 1)^4 *
            (Work.FIArea4.S15Br6 Pa X
              + (Pa.N)^((1:ℝ)/3) * (X:ℝ)^(-(1:ℝ)/3) * (Pa.N)^((2:ℝ)/3) * (e:ℝ)^(-(1:ℝ)))
          = C2 * ((Real.log Pa.N + 1)^4 *
            (Work.FIArea4.S15Br6 Pa X
              + (Pa.N)^((1:ℝ)/3) * (X:ℝ)^(-(1:ℝ)/3) * (Pa.N)^((2:ℝ)/3) * (e:ℝ)^(-(1:ℝ)))) by ring]
      apply mul_le_mul_of_nonneg_left _ (le_of_lt hC2_pos)
      exact mul_le_mul_of_nonneg_left hBB hL0
    refine le_trans hstr ?_
    apply mul_le_mul_of_nonneg_right ?_ (hEnr_nn e)
    apply mul_le_mul_of_nonneg_left hB'
    positivity
  have hEnrSum : (∑ e ∈ Finset.Icc 1 (Work.FIArea4.S15Y Pa X j),
        (∑ σ ∈ Work.FIArea4.S15red.Q,
            Work.FIArea4.p14Ener (Work.FIArea4.S15red.ReK Pa e)
              (Work.FIArea4.S15red.SeK Pa)
              (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa)
                (Work.FIArea4.S15strU β u t ℓ e) σ.1 σ.2)))
      ≤ 4 * (Ce * Work.FIArea4.A6Ener3 Pa β) := by
    rw [Finset.sum_comm]
    calc (∑ σ ∈ Work.FIArea4.S15red.Q,
            ∑ e ∈ Finset.Icc 1 (Work.FIArea4.S15Y Pa X j),
              Work.FIArea4.p14Ener (Work.FIArea4.S15red.ReK Pa e)
                (Work.FIArea4.S15red.SeK Pa)
                (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa)
                  (Work.FIArea4.S15strU β u t ℓ e) σ.1 σ.2))
        ≤ ∑ _σ ∈ Work.FIArea4.S15red.Q, Ce * Work.FIArea4.A6Ener3 Pa β := Finset.sum_le_sum hE
      _ = 4 * (Ce * Work.FIArea4.A6Ener3 Pa β) := by
          rw [Finset.sum_const, Work.FIArea4.S15red.Q_card, nsmul_eq_mul]
          ring
  have hfac4 : (0:ℝ) ≤ 4 * (Ce * Work.FIArea4.A6Ener3 Pa β) := by
    have h1 : 0 ≤ Ce := le_of_lt hCe_pos
    positivity
  calc (∑ e ∈ Finset.Icc 1 (Work.FIArea4.S15Y Pa X j),
        ∑ d' ∈ (Finset.Icc 1 (Work.FIArea4.S15Y Pa X j / e)).filter (fun d' => X < e * d'),
          Work.FIArea4.EvarG (Work.FITop.radN Pa) (4 * d')
            (Work.FIArea4.S15strU β u t ℓ e))
      = ∑ e ∈ Finset.Icc 1 (Work.FIArea4.S15Y Pa X j),
          ∑ d' ∈ Work.S15crux.dset Pa X j e,
            Work.FIArea4.EvarG (Work.FITop.radN Pa) (4 * d')
              (Work.FIArea4.S15strU β u t ℓ e) := by
          simp only [Work.S15crux.dset]
    _ ≤ ∑ e ∈ Finset.Icc 1 (Work.FIArea4.S15Y Pa X j),
          4 * Cp * (C2 * ((Real.log Pa.N + 1)^4 *
                (Work.FIArea4.S15Br6 Pa X
                  + (Pa.N)^((1:ℝ)/3) * (X:ℝ)^(-(1:ℝ)/3) * (Pa.N)^((2:ℝ)/3))))
            * (∑ σ ∈ Work.FIArea4.S15red.Q,
                Work.FIArea4.p14Ener (Work.FIArea4.S15red.ReK Pa e)
                  (Work.FIArea4.S15red.SeK Pa)
                  (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa)
                    (Work.FIArea4.S15strU β u t ℓ e) σ.1 σ.2)) := Finset.sum_le_sum hper
    _ = 4 * Cp * (C2 * ((Real.log Pa.N + 1)^4 *
                (Work.FIArea4.S15Br6 Pa X
                  + (Pa.N)^((1:ℝ)/3) * (X:ℝ)^(-(1:ℝ)/3) * (Pa.N)^((2:ℝ)/3))))
          * (∑ e ∈ Finset.Icc 1 (Work.FIArea4.S15Y Pa X j),
              ∑ σ ∈ Work.FIArea4.S15red.Q,
                Work.FIArea4.p14Ener (Work.FIArea4.S15red.ReK Pa e)
                  (Work.FIArea4.S15red.SeK Pa)
                  (Work.FIArea4.quadArrE (Work.FIArea4.S15red.KK Pa)
                    (Work.FIArea4.S15strU β u t ℓ e) σ.1 σ.2)) := by
          rw [Finset.mul_sum]
    _ ≤ 4 * Cp * (C2 * ((Real.log Pa.N + 1)^4 *
                (Work.FIArea4.S15Br6 Pa X
                  + (Pa.N)^((1:ℝ)/3) * (X:ℝ)^(-(1:ℝ)/3) * (Pa.N)^((2:ℝ)/3))))
          * (4 * (Ce * Work.FIArea4.A6Ener3 Pa β)) := by
          apply mul_le_mul_of_nonneg_left hEnrSum
          positivity
    _ ≤ 4 * Cp * (C2 * ((Real.log Pa.N + 1)^4 *
                (2 * Work.FIArea4.S15Br6 Pa X)))
          * (4 * (Ce * Work.FIArea4.A6Ener3 Pa β)) := by
          have hbm : Work.FIArea4.S15Br6 Pa X
              + (Pa.N)^((1:ℝ)/3) * (X:ℝ)^(-(1:ℝ)/3) * (Pa.N)^((2:ℝ)/3)
              ≤ 2 * Work.FIArea4.S15Br6 Pa X := by linarith [S15Br6_ge_mid' Pa X]
          have hle1 : (Real.log Pa.N + 1)^4 *
                (Work.FIArea4.S15Br6 Pa X
                  + (Pa.N)^((1:ℝ)/3) * (X:ℝ)^(-(1:ℝ)/3) * (Pa.N)^((2:ℝ)/3))
              ≤ (Real.log Pa.N + 1)^4 * (2 * Work.FIArea4.S15Br6 Pa X) :=
            mul_le_mul_of_nonneg_left hbm hL0
          have hle2 : C2 * ((Real.log Pa.N + 1)^4 *
                (Work.FIArea4.S15Br6 Pa X
                  + (Pa.N)^((1:ℝ)/3) * (X:ℝ)^(-(1:ℝ)/3) * (Pa.N)^((2:ℝ)/3)))
              ≤ C2 * ((Real.log Pa.N + 1)^4 * (2 * Work.FIArea4.S15Br6 Pa X)) :=
            mul_le_mul_of_nonneg_left hle1 (le_of_lt hC2_pos)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hle2 (by positivity)) hfac4
    _ = 32 * Cp * C2 * Ce * (Real.log Pa.N + 1)^4 * Work.FIArea4.S15Br6 Pa X
          * Work.FIArea4.A6Ener3 Pa β := by ring

end

end Work.FIArea4.A6R
