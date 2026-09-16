import Submission.CertAnalytic
import Submission.Commons.Analysis.TensorApprox.sum_univ_pi_prod

set_option maxHeartbeats 1000000
set_option maxRecDepth 1000000

open scoped BigOperators
open Finset

/-!
# An explicit sup-bound for the certificate polynomial

The §5.3 assembly needs a *numerical* upper bound `M₀` for `sup |certPoly|` on the certificate
simplex (it enters the `J₂`-loss budget of `hkey_of_split_tensorData` through the scaling of the
tensor localisation).  Here we prove the crude but explicit bound `|certPoly t| ≤ 10^54`.

The two ingredients are

* `lmono_abs_le`: on the orthant, a labelled monomial sum is bounded by the corresponding power
  of the total mass, `|lmono α k t| ≤ (Σ t)^|α|` (placements are a subset of all functions, and
  `Σ_j t_j^{a} ≤ (Σ t)^a` for `a ≥ 1`);
* `certCl_abs_le`: every labelled certificate coefficient is at most `10^50` (a `decide`).
-/

namespace Commons.NumberTheory.MaynardSieve

noncomputable section

theorem certA_add_sigsum_leX (j : Fin 1780) : certA j + (certSig j).sum ≤ 25 := by
  have h := of_decide_eq_true (List.all_eq_true.mp certBasis_sum_le (certBasisAt j)
    (List.get_mem _ _))
  dsimp only [certA, certSig]
  omega

/-- **The labelled monomial sum on the orthant.**  `|lmono α k t| ≤ (Σ t)^|α|` whenever the
parts of `α` are positive and `t ≥ 0`. -/
lemma lmono_abs_le {α : List ℕ} (hα : ∀ x ∈ α, 1 ≤ x) (k : ℕ) (t : Fin k → ℝ)
    (ht : ∀ i, 0 ≤ t i) : |lmono α k t| ≤ (∑ i, t i) ^ α.sum := by
  classical
  have hFnn : ∀ f : Fin α.length → Fin k, 0 ≤ ∏ i : Fin α.length, (t (f i)) ^ (α.get i) :=
    fun f => Finset.prod_nonneg fun i _ => pow_nonneg (ht _) _
  have hstep1 : (∑ e : Fin α.length ↪ Fin k, ∏ i : Fin α.length, (t (e i)) ^ (α.get i))
      ≤ ∑ f : Fin α.length → Fin k, ∏ i : Fin α.length, (t (f i)) ^ (α.get i) := by
    have hinj : Set.InjOn (fun e : Fin α.length ↪ Fin k => (e : Fin α.length → Fin k))
        ↑(Finset.univ : Finset (Fin α.length ↪ Fin k)) :=
      fun x _ y _ h => Function.Embedding.coe_injective h
    have hsum : (∑ f ∈ (Finset.univ : Finset (Fin α.length ↪ Fin k)).image
            (fun e : Fin α.length ↪ Fin k => (e : Fin α.length → Fin k)),
            ∏ i : Fin α.length, (t (f i)) ^ (α.get i))
        = ∑ e : Fin α.length ↪ Fin k, ∏ i : Fin α.length, (t (e i)) ^ (α.get i) :=
      Finset.sum_image (s := (Finset.univ : Finset (Fin α.length ↪ Fin k))) hinj
    rw [← hsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun f _ _ => hFnn f)
  have hstep2 : (∑ f : Fin α.length → Fin k, ∏ i : Fin α.length, (t (f i)) ^ (α.get i))
      = ∏ i : Fin α.length, ∑ j : Fin k, (t j) ^ (α.get i) :=
    Commons.Analysis.TensorApprox.sum_univ_pi_prod (fun i (j : Fin k) => (t j) ^ (α.get i))
  have hstep3 : ∏ i : Fin α.length, ∑ j : Fin k, (t j) ^ (α.get i)
      ≤ ∏ i : Fin α.length, (∑ j : Fin k, t j) ^ (α.get i) := by
    refine Finset.prod_le_prod₀ (fun i _ => Finset.sum_nonneg fun j _ => pow_nonneg (ht j) _)
      (fun i _ => ?_)
    have hi : 1 ≤ α.get i := by
      rw [List.get_eq_getElem]; exact hα _ (List.getElem_mem _)
    have h1 : ∀ j : Fin k, (t j) ^ (α.get i) ≤ (∑ j : Fin k, t j) ^ (α.get i - 1) * t j := by
      intro j
      have hle : t j ≤ ∑ j : Fin k, t j :=
        Finset.single_le_sum (fun j _ => ht j) (Finset.mem_univ j)
      calc (t j) ^ (α.get i) = (t j) ^ (α.get i - 1) * t j := by
            rw [← pow_succ, Nat.sub_add_cancel hi]
        _ ≤ (∑ j : Fin k, t j) ^ (α.get i - 1) * t j :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (ht j) hle _) (ht j)
    calc ∑ j : Fin k, (t j) ^ (α.get i)
        ≤ ∑ j : Fin k, (∑ j : Fin k, t j) ^ (α.get i - 1) * t j :=
          Finset.sum_le_sum fun j _ => h1 j
      _ = (∑ j : Fin k, t j) ^ (α.get i - 1) * (∑ j : Fin k, t j) := (Finset.mul_sum ..).symm
      _ = (∑ j : Fin k, t j) ^ (α.get i) := by
          rw [← pow_succ, Nat.sub_add_cancel hi]
  have hstep4 : ∏ i : Fin α.length, (∑ j : Fin k, t j) ^ (α.get i)
      = (∑ j : Fin k, t j) ^ α.sum := by
    rw [Finset.prod_pow_eq_pow_sum, ← List.sum_ofFn (f := α.get), List.ofFn_get]
  have hmain : lmono α k t ≤ (∑ i, t i) ^ α.sum := by
    rw [lmono]
    calc ∑ e : Fin α.length ↪ Fin k, ∏ i : Fin α.length, (t (e i)) ^ (α.get i)
        ≤ ∑ f : Fin α.length → Fin k, ∏ i : Fin α.length, (t (f i)) ^ (α.get i) := hstep1
      _ = ∏ i : Fin α.length, ∑ j : Fin k, (t j) ^ (α.get i) := hstep2
      _ ≤ ∏ i : Fin α.length, (∑ j : Fin k, t j) ^ (α.get i) := hstep3
      _ = (∑ j : Fin k, t j) ^ α.sum := hstep4
  have hnn' : 0 ≤ lmono α k t := by
    rw [lmono]; exact Finset.sum_nonneg fun e _ => hFnn e
  rw [abs_of_nonneg hnn']
  exact hmain

/-- All labelled certificate coefficients are at most `10^50` in absolute value. -/
theorem certCoefLab_abs_le : certCoefLab.all (fun z => decide (z.natAbs ≤ 10 ^ 50)) = true := by
  decide

theorem certCl_abs_le (j : Fin 1780) : (certCl j).natAbs ≤ 10 ^ 50 :=
  of_decide_eq_true (List.all_eq_true.mp certCoefLab_abs_le _
    (certCl_eq_getElem j ▸ List.getElem_mem _))

theorem cast_abs_int (z : ℤ) : |(z : ℝ)| = ((z.natAbs : ℕ) : ℝ) := by
  rw [← Int.cast_abs, Int.abs_eq_natAbs]
  norm_num

/-- **The explicit sup-bound of the certificate polynomial.**  On the certificate simplex
`{t ≥ 0, Σ t ≤ 26/25}` the polynomial is bounded by `10^54`. -/
theorem abs_certPoly_le {t : Fin 50 → ℝ} (ht : t ∈ simplexC 50 ((26 : ℝ) / 25)) :
    |certPoly t| ≤ (10 : ℝ) ^ 54 := by
  classical
  have hnn : ∀ i : Fin 50, 0 ≤ t i := fun i => ht.1 i
  have hTnn : (0 : ℝ) ≤ ∑ i : Fin 50, t i := Finset.sum_nonneg fun i _ => hnn i
  have hle : (∑ i : Fin 50, t i) ≤ (26 : ℝ) / 25 := ht.2
  have hSnn : 0 ≤ (26 : ℝ) / 25 - ∑ i, t i := by linarith
  have hSle : (26 : ℝ) / 25 - ∑ i, t i ≤ (26 : ℝ) / 25 := by linarith
  have hlmono : ∀ j : Fin 1780, |lmono (certSig j) 50 t| ≤ ((26 : ℝ) / 25) ^ (certSig j).sum := by
    intro j
    refine le_trans (lmono_abs_le (fun x hx => ?_) 50 t hnn) ?_
    · rcases Nat.eq_zero_or_pos x with h0 | h0
      · exact absurd (h0 ▸ hx) (certSig_notMem_zero j)
      · omega
    · exact pow_le_pow_left₀ hTnn hle _
  have hb3 : ∀ j : Fin 1780,
      ((26 : ℝ) / 25 - ∑ i, t i) ^ (certA j) * |lmono (certSig j) 50 t| ≤ 3 := by
    intro j
    have h1 : ((26 : ℝ) / 25 - ∑ i, t i) ^ (certA j) ≤ ((26 : ℝ) / 25) ^ (certA j) :=
      pow_le_pow_left₀ hSnn hSle _
    have h2 : ((26 : ℝ) / 25) ^ (certA j) * ((26 : ℝ) / 25) ^ (certSig j).sum
        = ((26 : ℝ) / 25) ^ (certA j + (certSig j).sum) := (pow_add ..).symm
    have h3 : ((26 : ℝ) / 25) ^ (certA j + (certSig j).sum) ≤ ((26 : ℝ) / 25) ^ 25 :=
      pow_le_pow_right₀ (by norm_num) (certA_add_sigsum_leX j)
    have h4 : ((26 : ℝ) / 25) ^ 25 ≤ (3 : ℝ) := by norm_num
    calc ((26 : ℝ) / 25 - ∑ i, t i) ^ (certA j) * |lmono (certSig j) 50 t|
        ≤ ((26 : ℝ) / 25) ^ (certA j) * ((26 : ℝ) / 25) ^ (certSig j).sum :=
          mul_le_mul h1 (hlmono j) (abs_nonneg _) (pow_nonneg (by norm_num) _)
      _ = ((26 : ℝ) / 25) ^ (certA j + (certSig j).sum) := h2
      _ ≤ (3 : ℝ) := le_trans h3 h4
  have hmono : ∀ j : Fin 1780, |certTerm j t| ≤ ((certCl j).natAbs : ℝ) * 3 := by
    intro j
    have hcast : |(certCl j : ℝ)| = ((certCl j).natAbs : ℝ) := cast_abs_int (certCl j)
    rw [certTerm, abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hSnn _), hcast, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hb3 j) (Nat.cast_nonneg _)
  rw [certPoly_eq]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  calc ∑ j : Fin 1780, |certTerm j t|
      ≤ ∑ j : Fin 1780, ((certCl j).natAbs : ℝ) * 3 := Finset.sum_le_sum fun j _ => hmono j
    _ ≤ ∑ _j : Fin 1780, (((10 : ℕ) ^ 50 : ℕ) : ℝ) * 3 := by
        refine Finset.sum_le_sum fun j _ => ?_
        have h : ((certCl j).natAbs : ℝ) ≤ (((10 : ℕ) ^ 50 : ℕ) : ℝ) := by
          exact_mod_cast certCl_abs_le j
        exact mul_le_mul_of_nonneg_right h (by norm_num)
    _ ≤ (10 : ℝ) ^ 54 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        norm_num

end

end Commons.NumberTheory.MaynardSieve
