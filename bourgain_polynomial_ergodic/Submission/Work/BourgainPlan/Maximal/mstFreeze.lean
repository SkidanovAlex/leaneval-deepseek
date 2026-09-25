import Mathlib
import Submission.Work.BourgainPlan.Maximal.level_l2_mst_large_n_aux_defs
import Submission.Work.BourgainPlan.Maximal.mstFreezeDefs
import Submission.Work.BourgainPlan.Maximal.opMul_modSeq
import Submission.Work.BourgainPlan.Maximal.opMul_index_add
import Submission.Work.BourgainPlan.Maximal.mstFreeze_diff_eq
import Submission.Work.BourgainPlan.Maximal.mstFreeze_per_n_sq
import Submission.Work.BourgainPlan.Maximal.mstProf_scale_decay
import Submission.Work.BourgainPlan.Maximal.mstFreezeSym_bound
import Submission.Work.BourgainPlan.Maximal.lintegral_iSup_sq_le_tsum_sq
import Submission.Work.BourgainPlan.Maximal.lintegral_iSup_sq_le_of_per_n_bound

namespace Work.BourgainPlan.Maximal

open MeasureTheory Finset
open scoped BigOperators ENNReal

open Work.BourgainPlan.IonescuWainger

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

local notation "Circ" => Work.BourgainPlan.IonescuWainger.Circle

/-- The dyadic tail identity `2^{-(N+k)/d} = 2^{-N/d}·(2^{-1/d})^k`. -/
private lemma two_rpow_neg_div_add (d N k : ℕ) :
    (2 : ℝ) ^ ((-(((N + k : ℕ) : ℝ))) / (d : ℝ))
      = (2 : ℝ) ^ ((-(N : ℝ)) / (d : ℝ))
        * ((2 : ℝ) ^ ((-(1 : ℝ)) / (d : ℝ))) ^ k := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ ((-(1 : ℝ)) / (d : ℝ))) k,
    ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  push_cast
  ring

/-- **The freezing estimate (MST §4.3).**  For `u ∈ ℕ_{Q_s}` the `ℓ²(ℤ)`-maximal functions
`sup_{n≥2^{κ_s}}|I_n(x,x)|` and `sup_{n≥2^{κ_s}}|I_n(x,x+u)|` — where `I_n(x,·)` is the level-`s`
model with the arc phases frozen at `x`, i.e. the single multiplier with symbol `Φ_{2^n}ψ_s` applied
to the modulated input `mstModSeq G E f x` — differ by at most
`C·2^{−2^{κ_s}/d}·Q_s·#𝒰·(s+1)^{−δl}G0·‖f‖₂`.  Route: `|sup_n|a_n| − sup_n|b_n|| ≤ sup_n|a_n−b_n|
≤ Σ_n|a_n−b_n|`; for each `n` the difference of the two entries is a multiplier with symbol
`φ_n(ξ)(1−e^{2πiuξ})` in the *second* variable, and Plancherel plus
`sup_ξ |ξ|·|Φ_{2^n}(ξ)| ≲ 2^{−n/d}` (`polyProfile_decay_sharp` where `|ξ|·polyDil ≥ 1`, the
Lipschitz bound `|Φ_N(ξ)−1| ≲ N^d|ξ|` for the rest) gives the per-`n` `ℓ²`-bound
`2π|u|·2^{−n/d}M·(Σ_β‖G β‖)·‖f‖`; then `Σ_{n≥2^{κ_s}}2^{−n/d} ≲ 2^{−2^{κ_s}/d}`. -/
theorem mstFreeze (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (l : ℕ) (hl : 1 ≤ l) (χ : ℝ)
    (hχ : 0 < χ) (hχ1 : χ < 1 / 10) (η : ℝ → ℂ) (hηc : ContDiff ℝ 2 η) (hη1 : η 0 = 1)
    (hηsup : ∀ x : ℝ, 1 / 2 ≤ |x| → η x = 0) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 < C ∧ ∃ s₀ : ℕ, ∀ s : ℕ, s₀ ≤ s →
      ∀ (G : Work.BourgainPlan.IonescuWainger.Circle → ℂ) (G0 : ℝ), 0 ≤ G0 →
      Work.BourgainPlan.Maximal.HasDecay G G0 l s δ →
      ∀ (hB : ∀ n : ℕ, Lp ℂ ⊤ Work.BourgainPlan.Maximal.mstHaar),
      Work.BourgainPlan.Maximal.HasModel P P.natDegree χ η s hB →
      ∀ (f : ℤ → ℂ) (hf : Memℓp f 2) (u : ℕ), u ∈ Finset.range (Work.BourgainPlan.Maximal.mstQ' s) →
        (∫⁻ x : ℤ, (⨆ n : ℕ, ⨆ (_ : Work.BourgainPlan.Maximal.mstN₀' P s ≤ n),
            ‖Work.BourgainPlan.IonescuWainger.opMul (hB n) (Work.BourgainPlan.Maximal.mstModSeq G (Work.BourgainPlan.Maximal.mstLvl l s) f x) (Work.BourgainPlan.Maximal.memℒp_mstModSeq hf x) x‖ₑ) ^ (2 : ℝ)
          ∂MeasureTheory.Measure.count)
          ≤ 2 * (∫⁻ x : ℤ, (⨆ n : ℕ, ⨆ (_ : Work.BourgainPlan.Maximal.mstN₀' P s ≤ n),
              ‖Work.BourgainPlan.IonescuWainger.opMul (hB n) (Work.BourgainPlan.Maximal.mstModSeq G (Work.BourgainPlan.Maximal.mstLvl l s) f x) (Work.BourgainPlan.Maximal.memℒp_mstModSeq hf x) (x + (u : ℤ))‖ₑ) ^ (2 : ℝ)
              ∂MeasureTheory.Measure.count)
            + 2 * ENNReal.ofReal
                ((C * (2 : ℝ) ^ (-((Work.BourgainPlan.Maximal.mstN₀' P s : ℝ) / (P.natDegree : ℝ))) * (Work.BourgainPlan.Maximal.mstQ' s : ℝ)
                  * ((s : ℝ) + 1) ^ (-(δ * l)) * G0 * ((Work.BourgainPlan.Maximal.mstLvl l s).card : ℝ)) ^ 2)
              * (∫⁻ m : ℤ, ‖f m‖ₑ ^ (2 : ℝ) ∂MeasureTheory.Measure.count) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := mstProf_scale_decay P hd
  obtain ⟨M, hM0, hMb⟩ := exists_bound_mstEta P.natDegree χ η hηc hηsup
  obtain ⟨Cs, hCspos, hCs⟩ := mstFreezeSym_bound P hd χ η hηc hηsup
  -- the geometric constant `(1 - 2^{-1/d})^{-1}`
  set ρ : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / (P.natDegree : ℝ)) with hρdef
  have hρ0 : 0 ≤ ρ := by rw [hρdef]; exact Real.rpow_nonneg (by norm_num) _
  have hρ1 : ρ < 1 := by
    rw [hρdef]
    have h1 : (1 : ℝ) < (2 : ℝ) ^ ((1 : ℝ) / (P.natDegree : ℝ)) :=
      Real.one_lt_rpow (by norm_num) (by positivity)
    rw [show (-(1 : ℝ) / (P.natDegree : ℝ)) = -((1 : ℝ) / (P.natDegree : ℝ)) by ring,
      Real.rpow_neg (by norm_num)]
    exact inv_lt_one_of_one_lt₀ h1
  set Kd : ℝ := (1 - ρ)⁻¹ with hKddef
  have hKdpos : 0 < Kd := by rw [hKddef]; exact inv_pos.mpr (by linarith)
  refine ⟨Cs * M * Kd + 1, by positivity, ⟨1, fun s hs G G0 hG0 hDecay hB hModel f hf u hu => ?_⟩⟩
  set S : ENNReal := ∫⁻ m : ℤ, ‖f m‖ₑ ^ (2 : ℝ) ∂Measure.count with hSdef
  set sg : ℝ := ∑ β ∈ mstLvl l s, ‖G β‖ with hsgdef
  have hsg0 : 0 ≤ sg := by rw [hsgdef]; exact Finset.sum_nonneg (fun β _ => norm_nonneg _)
  have hsgbd : sg ≤ ((mstLvl l s).card : ℝ) * G0 * ((s : ℝ) + 1) ^ (-(δ * l)) := by
    rw [hsgdef]
    calc ∑ β ∈ mstLvl l s, ‖G β‖ ≤ ∑ _β ∈ mstLvl l s, (G0 * ((s : ℝ) + 1) ^ (-(δ * l))) :=
          Finset.sum_le_sum (fun β hβ => hDecay β hβ)
      _ = ((mstLvl l s).card : ℝ) * (G0 * ((s : ℝ) + 1) ^ (-(δ * l))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ = ((mstLvl l s).card : ℝ) * G0 * ((s : ℝ) + 1) ^ (-(δ * l)) := by ring
  have huQ : (u : ℝ) ≤ (mstQ' s : ℝ) := by
    have h : u < mstQ' s := Finset.mem_range.mp hu
    exact_mod_cast le_of_lt h
  let bb : ℕ → ℝ := fun n => sg * (Cs * M * (u : ℝ) * (2 : ℝ) ^ (-(n : ℝ) / (P.natDegree : ℝ)))
  let Cc : ℝ := sg * Cs * M * (mstQ' s : ℝ) * Kd
    * (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ)))
  have hX0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ))) :=
    Real.rpow_nonneg (by norm_num) _
  have hu0 : (0 : ℝ) ≤ (u : ℝ) := Nat.cast_nonneg u
  have hQ0 : (0 : ℝ) ≤ (mstQ' s : ℝ) := Nat.cast_nonneg _
  have hcard0 : (0 : ℝ) ≤ ((mstLvl l s).card : ℝ) := Nat.cast_nonneg _
  have hbb0 : ∀ n : ℕ, 0 ≤ bb n := by
    intro n
    have h2 : 0 ≤ (2 : ℝ) ^ (-(n : ℝ) / (P.natDegree : ℝ)) := Real.rpow_nonneg (by norm_num) _
    simp only [bb]
    exact mul_nonneg hsg0 (mul_nonneg (mul_nonneg (mul_nonneg hCspos.le hM0) hu0) h2)
  have hCc0 : 0 ≤ Cc := by
    simp only [Cc]
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hsg0 hCspos.le) hM0) hQ0)
      hKdpos.le) hX0
  -- the pointwise triangle inequality
  have hABC : ∀ n : ℕ, ∀ x : ℤ,
      ‖opMul (hB n) (mstModSeq G (mstLvl l s) f x) (memℒp_mstModSeq hf x) x‖ₑ
        ≤ ‖opMul (hB n) (mstModSeq G (mstLvl l s) f x) (memℒp_mstModSeq hf x) (x + (u : ℤ))‖ₑ
          + ‖opMul (hB n) (mstModSeq G (mstLvl l s) f x) (memℒp_mstModSeq hf x) (x + (u : ℤ))
              - opMul (hB n) (mstModSeq G (mstLvl l s) f x) (memℒp_mstModSeq hf x) x‖ₑ := by
    intro n x
    have htri := norm_le_norm_add_norm_sub
      (opMul (hB n) (mstModSeq G (mstLvl l s) f x) (memℒp_mstModSeq hf x) (x + (u : ℤ)))
      (opMul (hB n) (mstModSeq G (mstLvl l s) f x) (memℒp_mstModSeq hf x) x)
    rw [← ofReal_norm, ← ofReal_norm, ← ofReal_norm,
      ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
    exact ENNReal.ofReal_le_ofReal htri
  -- the per-`n` `ℓ²` bound
  have hpern : ∀ n : ℕ, MeasureTheory.lintegral MeasureTheory.Measure.count (fun x : ℤ =>
      ‖opMul (hB n) (mstModSeq G (mstLvl l s) f x) (memℒp_mstModSeq hf x) (x + (u : ℤ))
        - opMul (hB n) (mstModSeq G (mstLvl l s) f x) (memℒp_mstModSeq hf x) x‖ₑ ^ (2 : ℝ))
      ≤ ENNReal.ofReal ((bb n) ^ 2) * S := by
    intro n
    have hident := mstFreeze_diff_eq P l P.natDegree χ η hηc.continuous s n u G f hf hB hModel
    have hsym : ∀ (β ξ : Circ), ‖mstFreezeSymFun P P.natDegree χ η s n u β ξ‖
        ≤ Cs * M * (u : ℝ) * (2 : ℝ) ^ (-(n : ℝ) / (P.natDegree : ℝ)) :=
      fun β ξ => hCs M hM0 hMb s n u β ξ
    have hb0 : 0 ≤ Cs * M * (u : ℝ) * (2 : ℝ) ^ (-(n : ℝ) / (P.natDegree : ℝ)) := by
      have h2 : 0 ≤ (2 : ℝ) ^ (-(n : ℝ) / (P.natDegree : ℝ)) := Real.rpow_nonneg (by norm_num) _
      positivity
    have hpn := mstFreeze_per_n_sq P l P.natDegree χ η hηc.continuous s n u G f hf hB hb0 hsym hident
    have harg : (∑ β ∈ mstLvl l s, ‖G β‖)
        * (Cs * M * (u : ℝ) * (2 : ℝ) ^ ((-(n : ℝ)) / (P.natDegree : ℝ))) = bb n := by
      simp only [bb, hsgdef]
    rw [hSdef, ← harg]
    exact hpn
  -- the tail sum is summable and bounded by `Cc`
  have hsumm : Summable (fun k : ℕ => bb (mstN₀' P s + k)) := by
    have hgeom : Summable (fun k : ℕ => ρ ^ k) := summable_geometric_of_lt_one hρ0 hρ1
    refine (hgeom.mul_left (sg * Cs * M * (u : ℝ)
      * (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ))))).congr fun k => ?_
    simp only [bb]
    rw [two_rpow_neg_div_add P.natDegree (mstN₀' P s) k, ← hρdef]
    ring
  have hCsum : (tsum (fun k : ℕ => bb (mstN₀' P s + k))) ≤ Cc := by
    have hpt : ∀ k : ℕ, bb (mstN₀' P s + k)
        = sg * Cs * M * (u : ℝ) * (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ)))
          * ρ ^ k := by
      intro k
      simp only [bb]
      rw [two_rpow_neg_div_add P.natDegree (mstN₀' P s) k, ← hρdef]
      ring
    have htsum : (tsum (fun k : ℕ => bb (mstN₀' P s + k)))
        = sg * Cs * M * (u : ℝ) * (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ)))
          * (1 - ρ)⁻¹ := by
      rw [tsum_congr hpt, tsum_mul_left, tsum_geometric_of_lt_one hρ0 hρ1]
    rw [htsum]
    show sg * Cs * M * (u : ℝ) * (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ))) * (1 - ρ)⁻¹
      ≤ sg * Cs * M * (mstQ' s : ℝ) * (1 - ρ)⁻¹
        * (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ)))
    have h1 : sg * Cs * M * (u : ℝ) ≤ sg * Cs * M * (mstQ' s : ℝ) :=
      mul_le_mul_of_nonneg_left huQ
        (mul_nonneg (mul_nonneg hsg0 hCspos.le) hM0)
    calc sg * Cs * M * (u : ℝ) * (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ)))
            * (1 - ρ)⁻¹
        ≤ sg * Cs * M * (mstQ' s : ℝ) * (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ)))
            * (1 - ρ)⁻¹ :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 hX0) hKdpos.le
      _ = sg * Cs * M * (mstQ' s : ℝ) * (1 - ρ)⁻¹
            * (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ))) := by ring
  -- the abstract maximal/Minkowski bound
  have hmain := lintegral_iSup_sq_le_of_per_n_bound
      (fun n x => ‖opMul (hB n) (mstModSeq G (mstLvl l s) f x) (memℒp_mstModSeq hf x) x‖ₑ)
      (fun n x => ‖opMul (hB n) (mstModSeq G (mstLvl l s) f x) (memℒp_mstModSeq hf x) (x + (u : ℤ))‖ₑ)
      (fun n x => ‖opMul (hB n) (mstModSeq G (mstLvl l s) f x) (memℒp_mstModSeq hf x) (x + (u : ℤ))
          - opMul (hB n) (mstModSeq G (mstLvl l s) f x) (memℒp_mstModSeq hf x) x‖ₑ)
      (mstN₀' P s) bb S Cc hbb0 hCc0 hsumm hABC hpern hCsum
  -- the comparison of the two constants
  have hCcbound : Cc ≤ (Cs * M * Kd + 1)
      * (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ))) * (mstQ' s : ℝ)
      * ((s : ℝ) + 1) ^ (-(δ * l)) * G0 * ((mstLvl l s).card : ℝ) := by
    have hY0 : 0 ≤ ((s : ℝ) + 1) ^ (-(δ * l)) :=
      Real.rpow_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) s]) _
    have hCsMK0 : 0 ≤ Cs * M * Kd :=
      mul_nonneg (mul_nonneg hCspos.le hM0) hKdpos.le
    have hCsMKQ : 0 ≤ Cs * M * Kd * (mstQ' s : ℝ)
        * (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ))) :=
      mul_nonneg (mul_nonneg hCsMK0 hQ0) hX0
    have h1 : sg * (Cs * M * Kd * (mstQ' s : ℝ)
          * (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ))))
        ≤ (((mstLvl l s).card : ℝ) * G0 * ((s : ℝ) + 1) ^ (-(δ * l)))
          * (Cs * M * Kd * (mstQ' s : ℝ)
            * (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ)))) :=
      mul_le_mul_of_nonneg_right hsgbd hCsMKQ
    have h2 : Cs * M * Kd * (mstQ' s : ℝ)
          * (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ)))
        ≤ (Cs * M * Kd + 1) * (mstQ' s : ℝ)
          * (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ))) := by
      have hle : Cs * M * Kd ≤ Cs * M * Kd + 1 := by linarith
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle hQ0) hX0
    have h3 := mul_le_mul_of_nonneg_left h2
      (mul_nonneg (mul_nonneg hcard0 hG0) hY0)
    calc Cc = sg * (Cs * M * Kd * (mstQ' s : ℝ)
            * (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ)))) := by simp only [Cc]; ring
      _ ≤ _ := h1
      _ ≤ _ := h3
      _ = (Cs * M * Kd + 1) * (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ)))
            * (mstQ' s : ℝ) * ((s : ℝ) + 1) ^ (-(δ * l)) * G0 * ((mstLvl l s).card : ℝ) := by ring
  refine le_trans hmain ?_
  have h2 : ENNReal.ofReal (Cc ^ 2) ≤ ENNReal.ofReal (((Cs * M * Kd + 1)
      * (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ))) * (mstQ' s : ℝ)
      * ((s : ℝ) + 1) ^ (-(δ * l)) * G0 * ((mstLvl l s).card : ℝ)) ^ 2) :=
    ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ hCc0 hCcbound 2)
  have hfinal : 2 * ENNReal.ofReal (Cc ^ 2) * S
      ≤ 2 * ENNReal.ofReal (((Cs * M * Kd + 1)
          * (2 : ℝ) ^ (-((mstN₀' P s : ℝ) / (P.natDegree : ℝ))) * (mstQ' s : ℝ)
          * ((s : ℝ) + 1) ^ (-(δ * l)) * G0 * ((mstLvl l s).card : ℝ)) ^ 2) * S :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left h2 (by norm_num : (0 : ENNReal) ≤ 2))
      (show (0 : ENNReal) ≤ S from bot_le)
  exact add_le_add le_rfl hfinal

end

end Work.BourgainPlan.Maximal
