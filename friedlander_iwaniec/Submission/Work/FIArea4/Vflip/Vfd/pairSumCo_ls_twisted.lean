import Mathlib
import Submission.Work.FIArea4.Vflip.Vfd.pairSum_large_sieve_coprime
import Submission.Work.FIArea4.Vflip.Vfd.coprimeSetup
import Submission.Work.FIArea4.Vflip.Vfd.coprimeInner
import Submission.Work.FIArea4.Vflip.Vfd.coprimeEvar
import Submission.Work.FIArea4.Vflip.Vfd.pairSum_large_sieve

/-!
# The large-sieve bound for the `q`-sum of the *norms* of the coprime pair sums

`pairSum_large_sieve_coprime` bounds the norm of the `q`-sum `∑_{Q<q≤2Q} pairSumCo R S (m q) β γ`.
The lemma `pairSumCo_Ioc_norm_le` below proves the (formally stronger) *sum of the norms*

`∑_{Q<q≤2Q} ‖pairSumCo R S (m q) β γ‖ ≤ C(ε) T11(mQ,R,S,ε) (log 2R + 1) (L2 β)^{1/2}(L2 γ)^{1/2}`,

which is what a `q`-dependent coefficient `A q` in front of each pair sum demands.  Indeed for
every family `A` with `‖A q‖ ≤ 1` the triangle inequality gives

`‖∑_q A q · pairSumCo R S (m q) β γ‖ ≤ ∑_q ‖A q‖ ‖pairSumCo R S (m q) β γ‖
   ≤ ∑_q ‖pairSumCo R S (m q) β γ‖`,

so the two statements are in fact equivalent (choosing `A q = conj X_q / ‖X_q‖` realises the sum
of the norms for `X_q = pairSumCo R S (m q) β γ`): the twist costs nothing.

The proof is the proof of `pairSum_large_sieve_coprime` with the outer `norm_sum_le` replaced by
the identity, all the estimates in that proof being estimates on the sums of the norms.
-/

namespace Work.FIArea4.Vflip.Vfd

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

open Work.FIArea4

set_option maxHeartbeats 4000000

/-- The `q`-sum of the norms of the coprime pair sums is bounded by the bracket `p14T11`, the
logarithmic factor `log (2R) + 1` and the two `L²`-energies. -/
theorem pairSumCo_Ioc_norm_le (h11 : Work.FIArea4.p14Prop111All) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (m Q R S : ℕ) (β γ : ℕ → ℕ → ℂ),
        1 ≤ m → 1 ≤ Q → 1 ≤ R → 1 ≤ S →
        (∀ r s, β r s ≠ 0 → Odd r) → (∀ r s, γ r s ≠ 0 → Odd r) →
        ∑ q ∈ Finset.Ioc Q (2 * Q), ‖pairSumCo R S (m * q) β γ‖
          ≤ C * Work.FIArea4.p14T11 (m * Q) R S ε * (Real.log (2 * (R : ℝ)) + 1)
              * (Work.FIArea4.p14L2 R S β) ^ ((1 : ℝ) / 2)
              * (Work.FIArea4.p14L2 R S γ) ^ ((1 : ℝ) / 2) := by
  intro ε hε
  obtain ⟨C11, hC11pos, hC11⟩ := Evar_sum_le h11 (ε/2) (by linarith)
  obtain ⟨K, hKpos, hKrpow⟩ := sum_shift_L2_rpow_le ε hε
  have h2e : (0:ℝ) < 2 ^ (ε/2) := Real.rpow_pos_of_pos (by norm_num) _
  refine ⟨4*C11 + 4*C11*K*2^(ε/2) + C11 + 1, by positivity, ?_⟩
  intro m Q R S β γ hm hQ hR hS hβodd hγodd
  -- box-restrict the coefficient arrays
  let β' : ℕ → ℕ → ℂ := fun r s => if r ∈ Finset.Icc 1 (2*R) ∧ s ∈ Finset.Icc 1 (2*S) then β r s else 0
  let γ' : ℕ → ℕ → ℂ := fun r s => if r ∈ Finset.Icc 1 (2*R) ∧ s ∈ Finset.Icc 1 (2*S) then γ r s else 0
  have hβ'val : ∀ r s, β' r s = if r ∈ Finset.Icc 1 (2*R) ∧ s ∈ Finset.Icc 1 (2*S) then β r s else 0 := fun r s => rfl
  have hγ'val : ∀ r s, γ' r s = if r ∈ Finset.Icc 1 (2*R) ∧ s ∈ Finset.Icc 1 (2*S) then γ r s else 0 := fun r s => rfl
  have hβ'box : ∀ r s, β' r s ≠ 0 → r ≤ 2*R := by
    intro r s h
    rw [hβ'val r s] at h
    by_cases hc : r ∈ Finset.Icc 1 (2*R) ∧ s ∈ Finset.Icc 1 (2*S)
    · rw [if_pos hc] at h; exact (Finset.mem_Icc.mp hc.1).2
    · rw [if_neg hc] at h; exact absurd rfl h
  have hγ'box : ∀ r s, γ' r s ≠ 0 → r ≤ 2*R := by
    intro r s h
    rw [hγ'val r s] at h
    by_cases hc : r ∈ Finset.Icc 1 (2*R) ∧ s ∈ Finset.Icc 1 (2*S)
    · rw [if_pos hc] at h; exact (Finset.mem_Icc.mp hc.1).2
    · rw [if_neg hc] at h; exact absurd rfl h
  have hβ'odd : ∀ r s, β' r s ≠ 0 → Odd r := by
    intro r s h
    rw [hβ'val r s] at h
    by_cases hc : r ∈ Finset.Icc 1 (2*R) ∧ s ∈ Finset.Icc 1 (2*S)
    · rw [if_pos hc] at h; exact hβodd r s h
    · rw [if_neg hc] at h; exact absurd rfl h
  have hγ'odd : ∀ r s, γ' r s ≠ 0 → Odd r := by
    intro r s h
    rw [hγ'val r s] at h
    by_cases hc : r ∈ Finset.Icc 1 (2*R) ∧ s ∈ Finset.Icc 1 (2*S)
    · rw [if_pos hc] at h; exact hγodd r s h
    · rw [if_neg hc] at h; exact absurd rfl h
  have hL2β : Work.FIArea4.p14L2 R S β = Work.FIArea4.p14L2 R S β' := by
    simp only [Work.FIArea4.p14L2]
    refine Finset.sum_congr rfl (fun r hr => Finset.sum_congr rfl (fun s hs => ?_))
    rw [show β r s = β' r s from by rw [hβ'val r s, if_pos ⟨hr, hs⟩]]
  have hL2γ : Work.FIArea4.p14L2 R S γ = Work.FIArea4.p14L2 R S γ' := by
    simp only [Work.FIArea4.p14L2]
    refine Finset.sum_congr rfl (fun r hr => Finset.sum_congr rfl (fun s hs => ?_))
    rw [show γ r s = γ' r s from by rw [hγ'val r s, if_pos ⟨hr, hs⟩]]
  have hLHS : (∑ q ∈ Finset.Ioc Q (2*Q), ‖pairSumCo R S (m*q) β γ‖)
      = ∑ q ∈ Finset.Ioc Q (2*Q), ‖pairSumCo R S (m*q) β' γ'‖ := by
    refine Finset.sum_congr rfl (fun q _ => ?_)
    have hqeq : pairSumCo R S (m*q) β γ = pairSumCo R S (m*q) β' γ' := by
      simp only [pairSumCo]
      refine Finset.sum_congr rfl (fun r1 hr1 => Finset.sum_congr rfl (fun s1 hs1 =>
        Finset.sum_congr rfl (fun r2 hr2 => Finset.sum_congr rfl (fun s2 hs2 => ?_))))
      rw [show β r1 s1 = β' r1 s1 from by rw [hβ'val r1 s1, if_pos ⟨hr1, hs1⟩],
          show γ r2 s2 = γ' r2 s2 from by rw [hγ'val r2 s2, if_pos ⟨hr2, hs2⟩]]
    rw [hqeq]
  -- per-ρ bound
  have hper : ∀ ρ ∈ Finset.Icc 1 (2*R),
      ∑ q ∈ Finset.Ioc Q (2*Q), ‖Work.FIArea4.pairSum R S (m*q) (shiftCoef ρ β') (shiftCoef ρ γ')‖
        ≤ C11 * Work.FIArea4.p14T11 (m*Q) ((R+ρ-1)/ρ) S (ε/2)
            * Real.sqrt (Work.FIArea4.p14L2 R S (shiftCoef ρ β'))
            * Real.sqrt (Work.FIArea4.p14L2 R S (shiftCoef ρ γ')) := by
    intro ρ hρmem
    have hρ1 : 1 ≤ ρ := (Finset.mem_Icc.mp hρmem).1
    have hqbound : ∀ q ∈ Finset.Ioc Q (2*Q),
        ‖Work.FIArea4.pairSum R S (m*q) (shiftCoef ρ β') (shiftCoef ρ γ')‖
          ≤ Real.sqrt (Work.FIPlan.Evar R S (m*q) (shiftCoef ρ β'))
              * Real.sqrt (Work.FIPlan.Evar R S (m*q) (shiftCoef ρ γ')) := by
      intro q hq
      have hq1 : 0 < q := by have := (Finset.mem_Ioc.mp hq).1; omega
      exact pairSum_le_Evar_odd R S (m*q)
        (Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos (by omega) hq1).ne')
        (shiftCoef ρ β') (shiftCoef ρ γ') (shiftCoef_odd hβ'odd) (shiftCoef_odd hγ'odd)
    have hEβ := hC11 m Q R S ρ β' hm hQ hR hS hρ1 hβ'box
    have hEγ := hC11 m Q R S ρ γ' hm hQ hR hS hρ1 hγ'box
    have hCs := sum_sqrt_mul_sqrt_le (Finset.Ioc Q (2*Q))
      (fun q => Work.FIPlan.Evar R S (m*q) (shiftCoef ρ β'))
      (fun q => Work.FIPlan.Evar R S (m*q) (shiftCoef ρ γ'))
      (fun q _ => Evar_nonneg R S (m*q) (shiftCoef ρ β'))
      (fun q _ => Evar_nonneg R S (m*q) (shiftCoef ρ γ'))
    have hTnn : 0 ≤ Work.FIArea4.p14T11 (m*Q) ((R+ρ-1)/ρ) S (ε/2) := p14T11_nonneg _ _ _ _
    calc ∑ q ∈ Finset.Ioc Q (2*Q), ‖Work.FIArea4.pairSum R S (m*q) (shiftCoef ρ β') (shiftCoef ρ γ')‖
        ≤ ∑ q ∈ Finset.Ioc Q (2*Q), Real.sqrt (Work.FIPlan.Evar R S (m*q) (shiftCoef ρ β'))
            * Real.sqrt (Work.FIPlan.Evar R S (m*q) (shiftCoef ρ γ')) := Finset.sum_le_sum hqbound
      _ ≤ Real.sqrt (∑ q ∈ Finset.Ioc Q (2*Q), Work.FIPlan.Evar R S (m*q) (shiftCoef ρ β'))
            * Real.sqrt (∑ q ∈ Finset.Ioc Q (2*Q), Work.FIPlan.Evar R S (m*q) (shiftCoef ρ γ')) := hCs
      _ ≤ Real.sqrt (C11 * Work.FIArea4.p14T11 (m*Q) ((R+ρ-1)/ρ) S (ε/2)
              * Work.FIArea4.p14L2 R S (shiftCoef ρ β'))
            * Real.sqrt (C11 * Work.FIArea4.p14T11 (m*Q) ((R+ρ-1)/ρ) S (ε/2)
              * Work.FIArea4.p14L2 R S (shiftCoef ρ γ')) :=
          mul_le_mul (Real.sqrt_le_sqrt hEβ) (Real.sqrt_le_sqrt hEγ) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = C11 * Work.FIArea4.p14T11 (m*Q) ((R+ρ-1)/ρ) S (ε/2)
            * Real.sqrt (Work.FIArea4.p14L2 R S (shiftCoef ρ β'))
            * Real.sqrt (Work.FIArea4.p14L2 R S (shiftCoef ρ γ')) := by
          rw [sqrt_mul_sqrt_eq C11 (Work.FIArea4.p14T11 (m*Q) ((R+ρ-1)/ρ) S (ε/2))
              (Work.FIArea4.p14L2 R S (shiftCoef ρ β')) (Work.FIArea4.p14L2 R S (shiftCoef ρ γ'))
              hC11pos.le hTnn]
          rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  have hnorm : ∑ q ∈ Finset.Ioc Q (2*Q), ‖pairSumCo R S (m*q) β' γ'‖
      ≤ C11 * ∑ ρ ∈ Finset.Icc 1 (2*R), Work.FIArea4.p14T11 (m*Q) ((R+ρ-1)/ρ) S (ε/2)
          * Real.sqrt (Work.FIArea4.p14L2 R S (shiftCoef ρ β'))
          * Real.sqrt (Work.FIArea4.p14L2 R S (shiftCoef ρ γ')) := by
    calc ∑ q ∈ Finset.Ioc Q (2*Q), ‖pairSumCo R S (m*q) β' γ'‖
        = ∑ q ∈ Finset.Ioc Q (2*Q), ‖∑ ρ ∈ Finset.Icc 1 (2*R),
            ((ArithmeticFunction.moebius ρ : ℤ) : ℂ) *
              (if Nat.Coprime ρ (Work.FIPlan.oddPart (m*q)) then
                Work.FIArea4.pairSum R S (m*q) (shiftCoef ρ β') (shiftCoef ρ γ') else 0)‖ := by
          refine Finset.sum_congr rfl (fun q hq => ?_)
          have hq1 : 0 < q := by have := (Finset.mem_Ioc.mp hq).1; omega
          rw [pairSumCo_eq_moebius R S (m*q)
            (Nat.one_le_iff_ne_zero.mpr (Nat.mul_pos (by omega) hq1).ne')
            β' γ' hβ'odd hβ'box hγ'odd hγ'box]
      _ ≤ ∑ q ∈ Finset.Ioc Q (2*Q), ∑ ρ ∈ Finset.Icc 1 (2*R),
            ‖Work.FIArea4.pairSum R S (m*q) (shiftCoef ρ β') (shiftCoef ρ γ')‖ := by
          refine Finset.sum_le_sum (fun q _ => ?_)
          refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum (fun ρ _ => ?_))
          rw [norm_mul]
          have hμ : ‖((ArithmeticFunction.moebius ρ : ℤ) : ℂ)‖ ≤ 1 := by
            rw [Complex.norm_intCast, ← Int.cast_abs]
            exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := ρ)
          by_cases hc : Nat.Coprime ρ (Work.FIPlan.oddPart (m*q))
          · rw [if_pos hc]
            calc ‖((ArithmeticFunction.moebius ρ : ℤ) : ℂ)‖
                  * ‖Work.FIArea4.pairSum R S (m*q) (shiftCoef ρ β') (shiftCoef ρ γ')‖
                ≤ 1 * ‖Work.FIArea4.pairSum R S (m*q) (shiftCoef ρ β') (shiftCoef ρ γ')‖ :=
                  mul_le_mul_of_nonneg_right hμ (norm_nonneg _)
              _ = _ := one_mul _
          · rw [if_neg hc, norm_zero, mul_zero]
            exact norm_nonneg _
      _ = ∑ ρ ∈ Finset.Icc 1 (2*R), ∑ q ∈ Finset.Ioc Q (2*Q),
            ‖Work.FIArea4.pairSum R S (m*q) (shiftCoef ρ β') (shiftCoef ρ γ')‖ :=
          Finset.sum_comm
      _ ≤ ∑ ρ ∈ Finset.Icc 1 (2*R), C11 * Work.FIArea4.p14T11 (m*Q) ((R+ρ-1)/ρ) S (ε/2)
            * Real.sqrt (Work.FIArea4.p14L2 R S (shiftCoef ρ β'))
            * Real.sqrt (Work.FIArea4.p14L2 R S (shiftCoef ρ γ')) :=
          Finset.sum_le_sum hper
      _ = C11 * ∑ ρ ∈ Finset.Icc 1 (2*R), Work.FIArea4.p14T11 (m*Q) ((R+ρ-1)/ρ) S (ε/2)
            * Real.sqrt (Work.FIArea4.p14L2 R S (shiftCoef ρ β'))
            * Real.sqrt (Work.FIArea4.p14L2 R S (shiftCoef ρ γ')) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun ρ _ => by ring)
  -- the two σ-weighted sums
  set A : ℕ → ℝ := fun ρ => Work.FIArea4.p14L2 R S (shiftCoef ρ β') with hA
  set B : ℕ → ℝ := fun ρ => Work.FIArea4.p14L2 R S (shiftCoef ρ γ') with hB
  set L : ℝ := Real.sqrt (Work.FIArea4.p14L2 R S β') * Real.sqrt (Work.FIArea4.p14L2 R S γ') with hLdef
  have hAnn : ∀ ρ, 0 ≤ A ρ := fun ρ => p14L2_nonneg R S _
  have hBnn : ∀ ρ, 0 ≤ B ρ := fun ρ => p14L2_nonneg R S _
  have hLnn : 0 ≤ L := by rw [hLdef]; positivity
  have hlog : (0:ℝ) ≤ Real.log (2*R) + 1 := by
    have : (0:ℝ) ≤ Real.log (2*R) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2*R))
    linarith
  have hσ1 : ∑ ρ ∈ Finset.Icc 1 (2*R), ((ρ:ℝ))⁻¹ * Real.sqrt (A ρ) * Real.sqrt (B ρ)
      ≤ (Real.log (2*R) + 1) * L := by
    have hw : ∀ ρ ∈ Finset.Icc 1 (2*R), 0 ≤ ((ρ:ℝ))⁻¹ := fun ρ _ => by positivity
    have hwcs := sum_weighted_sqrt_le (Finset.Icc 1 (2*R)) (fun ρ => ((ρ:ℝ))⁻¹) A B hw
      (fun ρ _ => hAnn ρ) (fun ρ _ => hBnn ρ)
    have hA' : ∑ ρ ∈ Finset.Icc 1 (2*R), ((ρ:ℝ))⁻¹ * A ρ
        ≤ (Real.log (2*R) + 1) * Work.FIArea4.p14L2 R S β' := by
      have := sum_shift_L2_inv_le R S β' hR hβ'box
      simpa only [hA] using this
    have hB' : ∑ ρ ∈ Finset.Icc 1 (2*R), ((ρ:ℝ))⁻¹ * B ρ
        ≤ (Real.log (2*R) + 1) * Work.FIArea4.p14L2 R S γ' := by
      have := sum_shift_L2_inv_le R S γ' hR hγ'box
      simpa only [hB] using this
    have hs : Real.sqrt (Real.log (2*R) + 1) * Real.sqrt (Real.log (2*R) + 1) = Real.log (2*R) + 1 := by
      rw [← sq, Real.sq_sqrt hlog]
    calc ∑ ρ ∈ Finset.Icc 1 (2*R), ((ρ:ℝ))⁻¹ * Real.sqrt (A ρ) * Real.sqrt (B ρ)
        ≤ Real.sqrt (∑ ρ ∈ Finset.Icc 1 (2*R), ((ρ:ℝ))⁻¹ * A ρ)
            * Real.sqrt (∑ ρ ∈ Finset.Icc 1 (2*R), ((ρ:ℝ))⁻¹ * B ρ) := hwcs
      _ ≤ Real.sqrt ((Real.log (2*R) + 1) * Work.FIArea4.p14L2 R S β')
            * Real.sqrt ((Real.log (2*R) + 1) * Work.FIArea4.p14L2 R S γ') :=
          mul_le_mul (Real.sqrt_le_sqrt hA') (Real.sqrt_le_sqrt hB') (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = (Real.log (2*R) + 1) * L := by
          rw [Real.sqrt_mul hlog, Real.sqrt_mul hlog, hLdef]
          nlinarith [hs, Real.sqrt_nonneg (Work.FIArea4.p14L2 R S β'), Real.sqrt_nonneg (Work.FIArea4.p14L2 R S γ')]
  have hσ2 : ∑ ρ ∈ Finset.Icc 1 (2*R), ((ρ:ℝ))^(-(1:ℝ)/2) * Real.sqrt (A ρ) * Real.sqrt (B ρ)
      ≤ K * (2*R:ℝ)^(ε/2) * L := by
    have hw : ∀ ρ ∈ Finset.Icc 1 (2*R), 0 ≤ ((ρ:ℝ))^(-(1:ℝ)/2) :=
      fun ρ _ => Real.rpow_nonneg (by positivity) _
    have hwcs := sum_weighted_sqrt_le (Finset.Icc 1 (2*R)) (fun ρ => ((ρ:ℝ))^(-(1:ℝ)/2)) A B hw
      (fun ρ _ => hAnn ρ) (fun ρ _ => hBnn ρ)
    have hA' : ∑ ρ ∈ Finset.Icc 1 (2*R), ((ρ:ℝ))^(-(1:ℝ)/2) * A ρ
        ≤ K * (2*R:ℝ)^(ε/2) * Work.FIArea4.p14L2 R S β' := by
      have := hKrpow R S β' hR hS hβ'box
      simpa only [hA] using this
    have hB' : ∑ ρ ∈ Finset.Icc 1 (2*R), ((ρ:ℝ))^(-(1:ℝ)/2) * B ρ
        ≤ K * (2*R:ℝ)^(ε/2) * Work.FIArea4.p14L2 R S γ' := by
      have := hKrpow R S γ' hR hS hγ'box
      simpa only [hB] using this
    have hKnn : (0:ℝ) ≤ K * (2*R:ℝ)^(ε/2) := by positivity
    have hs : Real.sqrt (K * (2*R:ℝ)^(ε/2)) * Real.sqrt (K * (2*R:ℝ)^(ε/2)) = K * (2*R:ℝ)^(ε/2) := by
      rw [← sq, Real.sq_sqrt hKnn]
    calc ∑ ρ ∈ Finset.Icc 1 (2*R), ((ρ:ℝ))^(-(1:ℝ)/2) * Real.sqrt (A ρ) * Real.sqrt (B ρ)
        ≤ Real.sqrt (∑ ρ ∈ Finset.Icc 1 (2*R), ((ρ:ℝ))^(-(1:ℝ)/2) * A ρ)
            * Real.sqrt (∑ ρ ∈ Finset.Icc 1 (2*R), ((ρ:ℝ))^(-(1:ℝ)/2) * B ρ) := hwcs
      _ ≤ Real.sqrt (K * (2*R:ℝ)^(ε/2) * Work.FIArea4.p14L2 R S β')
            * Real.sqrt (K * (2*R:ℝ)^(ε/2) * Work.FIArea4.p14L2 R S γ') :=
          mul_le_mul (Real.sqrt_le_sqrt hA') (Real.sqrt_le_sqrt hB') (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      _ = K * (2*R:ℝ)^(ε/2) * L := by
          rw [Real.sqrt_mul hKnn, Real.sqrt_mul hKnn, hLdef]
          nlinarith [hs, Real.sqrt_nonneg (Work.FIArea4.p14L2 R S β'), Real.sqrt_nonneg (Work.FIArea4.p14L2 R S γ')]
  -- split the ρ-range at R
  have hsplit : (Finset.Icc 1 (2*R) : Finset ℕ) = Finset.Icc 1 R ∪ Finset.Ioc R (2*R) := by
    ext x; simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]; omega
  have hdisj : Disjoint (Finset.Icc 1 R) (Finset.Ioc R (2*R)) := by
    rw [Finset.disjoint_left]; intro x hx hx'
    rw [Finset.mem_Icc] at hx; rw [Finset.mem_Ioc] at hx'; omega
  rw [hsplit, Finset.sum_union hdisj] at hnorm
  have hW1 : ∑ ρ ∈ Finset.Icc 1 R, ((ρ:ℝ))⁻¹ * Real.sqrt (A ρ) * Real.sqrt (B ρ)
      ≤ (Real.log (2*R) + 1) * L := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hσ1
    · intro x hx; rw [Finset.mem_Icc] at hx ⊢; exact ⟨hx.1, by omega⟩
    · intro x _ _
      exact mul_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  have hW2 : ∑ ρ ∈ Finset.Icc 1 R, ((ρ:ℝ))^(-(1:ℝ)/2) * Real.sqrt (A ρ) * Real.sqrt (B ρ)
      ≤ K * (2*R:ℝ)^(ε/2) * L := by
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) hσ2
    · intro x hx; rw [Finset.mem_Icc] at hx ⊢; exact ⟨hx.1, by omega⟩
    · intro x _ _
      exact mul_nonneg (mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  -- the first block (ρ ≤ R)
  have hS1 : ∑ ρ ∈ Finset.Icc 1 R, Work.FIArea4.p14T11 (m*Q) ((R+ρ-1)/ρ) S (ε/2) * Real.sqrt (A ρ) * Real.sqrt (B ρ)
      ≤ 4 * (pT1 (m*Q) R S + pT3 (m*Q) R S (ε/2)) * (Real.log (2*R) + 1) * L
        + 4 * (pT2 (m*Q) R S (ε/2) + pT4 (m*Q) R S (ε/2)) * (K * (2*R:ℝ)^(ε/2)) * L := by
    have hstep : ∑ ρ ∈ Finset.Icc 1 R, Work.FIArea4.p14T11 (m*Q) ((R+ρ-1)/ρ) S (ε/2) * Real.sqrt (A ρ) * Real.sqrt (B ρ)
        ≤ ∑ ρ ∈ Finset.Icc 1 R, (4 * ((ρ:ℝ))⁻¹ * (pT1 (m*Q) R S + pT3 (m*Q) R S (ε/2))
            + 4 * ((ρ:ℝ))^(-(1:ℝ)/2) * (pT2 (m*Q) R S (ε/2) + pT4 (m*Q) R S (ε/2)))
              * Real.sqrt (A ρ) * Real.sqrt (B ρ) := by
      refine Finset.sum_le_sum (fun ρ hρ => ?_)
      have hρ1 : 1 ≤ ρ := (Finset.mem_Icc.mp hρ).1
      have hρR : ρ ≤ R := (Finset.mem_Icc.mp hρ).2
      have hle := p14T11_div_le (m*Q) R S ρ (ε/2) (by linarith) hR hS hρ1 hρR
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hle (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    refine le_trans hstep ?_
    have hrw : ∀ ρ : ℕ, (4 * ((ρ:ℝ))⁻¹ * (pT1 (m*Q) R S + pT3 (m*Q) R S (ε/2))
            + 4 * ((ρ:ℝ))^(-(1:ℝ)/2) * (pT2 (m*Q) R S (ε/2) + pT4 (m*Q) R S (ε/2)))
              * Real.sqrt (A ρ) * Real.sqrt (B ρ)
        = 4 * (pT1 (m*Q) R S + pT3 (m*Q) R S (ε/2)) * (((ρ:ℝ))⁻¹ * Real.sqrt (A ρ) * Real.sqrt (B ρ))
          + 4 * (pT2 (m*Q) R S (ε/2) + pT4 (m*Q) R S (ε/2))
              * (((ρ:ℝ))^(-(1:ℝ)/2) * Real.sqrt (A ρ) * Real.sqrt (B ρ)) := fun ρ => by ring
    rw [Finset.sum_congr rfl (fun ρ _ => hrw ρ), Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have hc1 : 0 ≤ 4 * (pT1 (m*Q) R S + pT3 (m*Q) R S (ε/2)) := by
      have := pT1_nonneg (m*Q) R S; have := pT3_nonneg (m*Q) R S (ε/2); linarith
    have hc2 : 0 ≤ 4 * (pT2 (m*Q) R S (ε/2) + pT4 (m*Q) R S (ε/2)) := by
      have := pT2_nonneg (m*Q) R S (ε/2); have := pT4_nonneg (m*Q) R S (ε/2); linarith
    have hk2 : 0 ≤ K * (2*R:ℝ)^(ε/2) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hW1 hc1
    have h2 := mul_le_mul_of_nonneg_left hW2 hc2
    nlinarith [h1, h2]
  -- the second block (ρ > R)
  have hS2 : ∑ ρ ∈ Finset.Ioc R (2*R), Work.FIArea4.p14T11 (m*Q) ((R+ρ-1)/ρ) S (ε/2) * Real.sqrt (A ρ) * Real.sqrt (B ρ)
      ≤ Work.FIArea4.p14T11 (m*Q) R S (ε/2) * L := by
    have hstep : ∑ ρ ∈ Finset.Ioc R (2*R), Work.FIArea4.p14T11 (m*Q) ((R+ρ-1)/ρ) S (ε/2) * Real.sqrt (A ρ) * Real.sqrt (B ρ)
        ≤ ∑ ρ ∈ Finset.Ioc R (2*R), Work.FIArea4.p14T11 (m*Q) R S (ε/2) * Real.sqrt (A ρ) * Real.sqrt (B ρ) := by
      refine Finset.sum_le_sum (fun ρ hρ => ?_)
      have hρR : R < ρ := (Finset.mem_Ioc.mp hρ).1
      have hρ2 : ρ ≤ 2*R := (Finset.mem_Ioc.mp hρ).2
      have hRρ : (R+ρ-1)/ρ = 1 :=
        Nat.div_eq_of_lt_le (by omega : 1 * ρ ≤ R+ρ-1) (by omega : R+ρ-1 < (1+1) * ρ)
      rw [hRρ]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (p14T11_mono_R (by linarith) (by omega) hS) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    refine le_trans hstep ?_
    have hfac : ∑ ρ ∈ Finset.Ioc R (2*R), Work.FIArea4.p14T11 (m*Q) R S (ε/2) * Real.sqrt (A ρ) * Real.sqrt (B ρ)
        = Work.FIArea4.p14T11 (m*Q) R S (ε/2) * ∑ ρ ∈ Finset.Ioc R (2*R), Real.sqrt (A ρ) * Real.sqrt (B ρ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun ρ _ => by ring)
    rw [hfac]
    have hCs := sum_sqrt_mul_sqrt_le (Finset.Ioc R (2*R)) A B
      (fun q _ => hAnn q) (fun q _ => hBnn q)
    have hma : ∑ ρ ∈ Finset.Ioc R (2*R), A ρ ≤ Work.FIArea4.p14L2 R S β' := by
      have := sum_shift_L2_mid_le R S β' hR hβ'box; simpa only [hA] using this
    have hmb : ∑ ρ ∈ Finset.Ioc R (2*R), B ρ ≤ Work.FIArea4.p14L2 R S γ' := by
      have := sum_shift_L2_mid_le R S γ' hR hγ'box; simpa only [hB] using this
    have hTnn : 0 ≤ Work.FIArea4.p14T11 (m*Q) R S (ε/2) := p14T11_nonneg _ _ _ _
    calc Work.FIArea4.p14T11 (m*Q) R S (ε/2) * ∑ ρ ∈ Finset.Ioc R (2*R), Real.sqrt (A ρ) * Real.sqrt (B ρ)
        ≤ Work.FIArea4.p14T11 (m*Q) R S (ε/2)
            * (Real.sqrt (∑ ρ ∈ Finset.Ioc R (2*R), A ρ) * Real.sqrt (∑ ρ ∈ Finset.Ioc R (2*R), B ρ)) :=
          mul_le_mul_of_nonneg_left hCs hTnn
      _ ≤ Work.FIArea4.p14T11 (m*Q) R S (ε/2) * L := by
          rw [hLdef]
          have hma' : Real.sqrt (∑ ρ ∈ Finset.Ioc R (2*R), A ρ) ≤ Real.sqrt (Work.FIArea4.p14L2 R S β') :=
            Real.sqrt_le_sqrt hma
          have hmb' : Real.sqrt (∑ ρ ∈ Finset.Ioc R (2*R), B ρ) ≤ Real.sqrt (Work.FIArea4.p14L2 R S γ') :=
            Real.sqrt_le_sqrt hmb
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul hma' hmb' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) hTnn
  -- arithmetic facts for the final combination
  have hRS1 : (1:ℝ) ≤ (R:ℝ)*(S:ℝ) := by
    have h1 : (1:ℝ) ≤ R := by exact_mod_cast hR
    have h2 : (1:ℝ) ≤ S := by exact_mod_cast hS
    nlinarith
  have hpt1 : pT1 (m*Q) R S + pT3 (m*Q) R S (ε/2) ≤ Work.FIArea4.p14T11 (m*Q) R S ε := by
    rw [p14T11_eq_sum]
    have h : pT3 (m*Q) R S (ε/2) ≤ pT3 (m*Q) R S ε := by
      unfold pT3
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hRS1 (by linarith : ε/2 ≤ ε))
        (by positivity : (0:ℝ) ≤ (R:ℝ)*(S:ℝ)^((3:ℝ)/4))
    have := pT1_nonneg (m*Q) R S; have := pT2_nonneg (m*Q) R S ε; have := pT4_nonneg (m*Q) R S ε
    linarith
  have hpt24 : (pT2 (m*Q) R S (ε/2) + pT4 (m*Q) R S (ε/2)) * (2*R:ℝ)^(ε/2)
      ≤ 2^(ε/2) * Work.FIArea4.p14T11 (m*Q) R S ε := by
    rw [p14T11_eq_sum]
    have hRSpos : (0:ℝ) < (R:ℝ)*(S:ℝ) := by
      have h1 : (1:ℝ) ≤ R := by exact_mod_cast hR
      have h2 : (1:ℝ) ≤ S := by exact_mod_cast hS
      nlinarith
    have hpow : (R:ℝ)^(ε/2) * ((R:ℝ)*(S:ℝ))^(ε/2) ≤ ((R:ℝ)*(S:ℝ))^ε := by
      have hRle : (R:ℝ) ≤ (R:ℝ)*(S:ℝ) := by
        nlinarith [show (0:ℝ) ≤ R by positivity, show (1:ℝ) ≤ S by exact_mod_cast hS]
      have h1 : (R:ℝ)^(ε/2) ≤ ((R:ℝ)*(S:ℝ))^(ε/2) :=
        Real.rpow_le_rpow (by positivity) hRle (by linarith)
      have h2 := mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hRSpos.le (ε/2))
      rwa [← Real.rpow_add hRSpos, show ε/2 + ε/2 = ε by ring] at h2
    have h2R : ((2*R:ℝ))^(ε/2) = 2^(ε/2) * (R:ℝ)^(ε/2) := by
      rw [show (2*R:ℝ) = 2 * (R:ℝ) by ring,
        Real.mul_rpow (by norm_num) (by positivity : (0:ℝ) ≤ (R:ℝ))]
    have hkey : (R:ℝ)^(ε/2) * (pT2 (m*Q) R S (ε/2) + pT4 (m*Q) R S (ε/2))
        ≤ pT2 (m*Q) R S ε + pT4 (m*Q) R S ε := by
      have e1 : (R:ℝ)^(ε/2) * pT2 (m*Q) R S (ε/2) ≤ pT2 (m*Q) R S ε := by
        unfold pT2
        calc (R:ℝ)^(ε/2) * (((m*Q:ℕ):ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)) * (((R:ℝ)*(S:ℝ))^(ε/2)))
            = (((m*Q:ℕ):ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)))
                * ((R:ℝ)^(ε/2) * (((R:ℝ)*(S:ℝ))^(ε/2))) := by ring
          _ ≤ (((m*Q:ℕ):ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ))) * (((R:ℝ)*(S:ℝ))^ε) :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = ((m*Q:ℕ):ℝ) * Real.sqrt ((R:ℝ)*(S:ℝ)) * (((R:ℝ)*(S:ℝ))^ε) := by ring
      have e2 : (R:ℝ)^(ε/2) * pT4 (m*Q) R S (ε/2) ≤ pT4 (m*Q) R S ε := by
        unfold pT4
        calc (R:ℝ)^(ε/2) * ((S:ℝ) * (R:ℝ)^((3:ℝ)/4) * (((R:ℝ)*(S:ℝ))^(ε/2)))
            = ((S:ℝ) * (R:ℝ)^((3:ℝ)/4))
                * ((R:ℝ)^(ε/2) * (((R:ℝ)*(S:ℝ))^(ε/2))) := by ring
          _ ≤ ((S:ℝ) * (R:ℝ)^((3:ℝ)/4)) * (((R:ℝ)*(S:ℝ))^ε) :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
          _ = (S:ℝ) * (R:ℝ)^((3:ℝ)/4) * (((R:ℝ)*(S:ℝ))^ε) := by ring
      rw [mul_add]
      exact add_le_add e1 e2
    have heq : (pT2 (m*Q) R S (ε/2) + pT4 (m*Q) R S (ε/2)) * (2*R:ℝ)^(ε/2)
        = 2^(ε/2) * ((R:ℝ)^(ε/2) * (pT2 (m*Q) R S (ε/2) + pT4 (m*Q) R S (ε/2))) := by
      rw [h2R]; ring
    rw [heq]
    refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (by norm_num) _)
    refine le_trans hkey ?_
    have := pT1_nonneg (m*Q) R S
    have := pT3_nonneg (m*Q) R S ε
    linarith
  have hptE : Work.FIArea4.p14T11 (m*Q) R S (ε/2) ≤ Work.FIArea4.p14T11 (m*Q) R S ε := by
    rw [p14T11_eq_sum, p14T11_eq_sum]
    have h2 : pT2 (m*Q) R S (ε/2) ≤ pT2 (m*Q) R S ε := by
      unfold pT2
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hRS1 (by linarith : ε/2 ≤ ε))
        (by positivity : (0:ℝ) ≤ ((m*Q:ℕ):ℝ)*Real.sqrt ((R:ℝ)*(S:ℝ)))
    have h3 : pT3 (m*Q) R S (ε/2) ≤ pT3 (m*Q) R S ε := by
      unfold pT3
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hRS1 (by linarith : ε/2 ≤ ε))
        (by positivity : (0:ℝ) ≤ (R:ℝ)*(S:ℝ)^((3:ℝ)/4))
    have h4 : pT4 (m*Q) R S (ε/2) ≤ pT4 (m*Q) R S ε := by
      unfold pT4
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hRS1 (by linarith : ε/2 ≤ ε))
        (by positivity : (0:ℝ) ≤ (S:ℝ)*(R:ℝ)^((3:ℝ)/4))
    linarith [h2, h3, h4]
  -- final combination
  have hbracket : 4 * (pT1 (m*Q) R S + pT3 (m*Q) R S (ε/2)) * (Real.log (2*R) + 1)
        + 4 * (pT2 (m*Q) R S (ε/2) + pT4 (m*Q) R S (ε/2)) * (K * (2*R:ℝ)^(ε/2))
        + Work.FIArea4.p14T11 (m*Q) R S (ε/2)
      ≤ (4 + 4*K*2^(ε/2) + 1) * Work.FIArea4.p14T11 (m*Q) R S ε * (Real.log (2*R) + 1) := by
    have hE := p14T11_nonneg (m*Q) R S ε
    have hlog1 : (1:ℝ) ≤ Real.log (2*R) + 1 := by
      have : (0:ℝ) ≤ Real.log (2*R) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 2*R))
      linarith
    have hK2 : (0:ℝ) ≤ K * 2^(ε/2) := by positivity
    have hc1 : 0 ≤ pT1 (m*Q) R S + pT3 (m*Q) R S (ε/2) := by
      have := pT1_nonneg (m*Q) R S; have := pT3_nonneg (m*Q) R S (ε/2); linarith
    have hc2 : 0 ≤ pT2 (m*Q) R S (ε/2) + pT4 (m*Q) R S (ε/2) := by
      have := pT2_nonneg (m*Q) R S (ε/2); have := pT4_nonneg (m*Q) R S (ε/2); linarith
    have hlogc : (0:ℝ) ≤ Real.log (2*R) + 1 := by linarith
    have hb1 : 4 * (pT1 (m*Q) R S + pT3 (m*Q) R S (ε/2)) * (Real.log (2*R) + 1)
        ≤ 4 * Work.FIArea4.p14T11 (m*Q) R S ε * (Real.log (2*R) + 1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpt1 (by norm_num)) hlogc
    have hb2 : 4 * (pT2 (m*Q) R S (ε/2) + pT4 (m*Q) R S (ε/2)) * (K * (2*R:ℝ)^(ε/2))
        ≤ 4 * K * 2^(ε/2) * Work.FIArea4.p14T11 (m*Q) R S ε := by
      have hKnn : (0:ℝ) ≤ 4 * K := by positivity
      calc 4 * (pT2 (m*Q) R S (ε/2) + pT4 (m*Q) R S (ε/2)) * (K * (2*R:ℝ)^(ε/2))
          = 4 * K * ((pT2 (m*Q) R S (ε/2) + pT4 (m*Q) R S (ε/2)) * (2*R:ℝ)^(ε/2)) := by ring
        _ ≤ 4 * K * (2^(ε/2) * Work.FIArea4.p14T11 (m*Q) R S ε) :=
            mul_le_mul_of_nonneg_left hpt24 hKnn
        _ = 4 * K * 2^(ε/2) * Work.FIArea4.p14T11 (m*Q) R S ε := by ring
    have hRHS : (4 + 4*K*2^(ε/2) + 1) * Work.FIArea4.p14T11 (m*Q) R S ε * (Real.log (2*R) + 1)
        = 4 * Work.FIArea4.p14T11 (m*Q) R S ε * (Real.log (2*R) + 1)
          + 4 * K * 2^(ε/2) * Work.FIArea4.p14T11 (m*Q) R S ε * (Real.log (2*R) + 1)
          + Work.FIArea4.p14T11 (m*Q) R S ε * (Real.log (2*R) + 1) := by ring
    rw [hRHS]
    have hEE : Work.FIArea4.p14T11 (m*Q) R S ε ≤ Work.FIArea4.p14T11 (m*Q) R S ε * (Real.log (2*R) + 1) := by
      nth_rewrite 1 [← mul_one (Work.FIArea4.p14T11 (m*Q) R S ε)]
      exact mul_le_mul_of_nonneg_left hlog1 hE
    have hK2E : 4 * K * 2^(ε/2) * Work.FIArea4.p14T11 (m*Q) R S ε
        ≤ 4 * K * 2^(ε/2) * Work.FIArea4.p14T11 (m*Q) R S ε * (Real.log (2*R) + 1) := by
      nth_rewrite 1 [← mul_one (4 * K * 2^(ε/2) * Work.FIArea4.p14T11 (m*Q) R S ε)]
      exact mul_le_mul_of_nonneg_left hlog1 (by positivity)
    linarith [hb1, hb2, hptE, hEE, hK2E]
  -- assemble
  have hbound : ∑ q ∈ Finset.Ioc Q (2*Q), ‖pairSumCo R S (m*q) β' γ'‖
      ≤ (4*C11 + 4*C11*K*2^(ε/2) + C11 + 1) * Work.FIArea4.p14T11 (m*Q) R S ε
          * (Real.log (2*R) + 1) * (Work.FIArea4.p14L2 R S β') ^ ((1:ℝ)/2)
          * (Work.FIArea4.p14L2 R S γ') ^ ((1:ℝ)/2) := by
    have hc11 : (0:ℝ) ≤ C11 := hC11pos.le
    have hX : (0:ℝ) ≤ (Work.FIArea4.p14L2 R S β') ^ ((1:ℝ)/2) := Real.rpow_nonneg (p14L2_nonneg R S β') _
    have hY : (0:ℝ) ≤ (Work.FIArea4.p14L2 R S γ') ^ ((1:ℝ)/2) := Real.rpow_nonneg (p14L2_nonneg R S γ') _
    have hLXY : L = (Work.FIArea4.p14L2 R S β') ^ ((1:ℝ)/2) * (Work.FIArea4.p14L2 R S γ') ^ ((1:ℝ)/2) := by
      rw [hLdef, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
    have hsum : (∑ ρ ∈ Finset.Icc 1 R, Work.FIArea4.p14T11 (m*Q) ((R+ρ-1)/ρ) S (ε/2) * Real.sqrt (A ρ) * Real.sqrt (B ρ))
          + (∑ ρ ∈ Finset.Ioc R (2*R), Work.FIArea4.p14T11 (m*Q) ((R+ρ-1)/ρ) S (ε/2) * Real.sqrt (A ρ) * Real.sqrt (B ρ))
        ≤ (4 + 4*K*2^(ε/2) + 1) * Work.FIArea4.p14T11 (m*Q) R S ε * (Real.log (2*R) + 1) * L := by
      have hbr2 : (4 * (pT1 (m*Q) R S + pT3 (m*Q) R S (ε/2)) * (Real.log (2*R) + 1)
            + 4 * (pT2 (m*Q) R S (ε/2) + pT4 (m*Q) R S (ε/2)) * (K * (2*R:ℝ)^(ε/2))
            + Work.FIArea4.p14T11 (m*Q) R S (ε/2)) * L
          ≤ ((4 + 4*K*2^(ε/2) + 1) * Work.FIArea4.p14T11 (m*Q) R S ε * (Real.log (2*R) + 1)) * L :=
        mul_le_mul_of_nonneg_right hbracket hLnn
      calc (∑ ρ ∈ Finset.Icc 1 R, Work.FIArea4.p14T11 (m*Q) ((R+ρ-1)/ρ) S (ε/2) * Real.sqrt (A ρ) * Real.sqrt (B ρ))
            + (∑ ρ ∈ Finset.Ioc R (2*R), Work.FIArea4.p14T11 (m*Q) ((R+ρ-1)/ρ) S (ε/2) * Real.sqrt (A ρ) * Real.sqrt (B ρ))
          ≤ (4 * (pT1 (m*Q) R S + pT3 (m*Q) R S (ε/2)) * (Real.log (2*R) + 1) * L
              + 4 * (pT2 (m*Q) R S (ε/2) + pT4 (m*Q) R S (ε/2)) * (K * (2*R:ℝ)^(ε/2)) * L)
              + Work.FIArea4.p14T11 (m*Q) R S (ε/2) * L := add_le_add hS1 hS2
        _ = (4 * (pT1 (m*Q) R S + pT3 (m*Q) R S (ε/2)) * (Real.log (2*R) + 1)
              + 4 * (pT2 (m*Q) R S (ε/2) + pT4 (m*Q) R S (ε/2)) * (K * (2*R:ℝ)^(ε/2))
              + Work.FIArea4.p14T11 (m*Q) R S (ε/2)) * L := by ring
        _ ≤ ((4 + 4*K*2^(ε/2) + 1) * Work.FIArea4.p14T11 (m*Q) R S ε * (Real.log (2*R) + 1)) * L := hbr2
        _ = (4 + 4*K*2^(ε/2) + 1) * Work.FIArea4.p14T11 (m*Q) R S ε * (Real.log (2*R) + 1) * L := by ring
    refine le_trans hnorm ?_
    refine le_trans (mul_le_mul_of_nonneg_left hsum hc11) ?_
    rw [hLXY]
    have hC11b : C11 * (4 + 4*K*2^(ε/2) + 1) ≤ 4*C11 + 4*C11*K*2^(ε/2) + C11 + 1 := by
      nlinarith [hc11, hKpos.le, Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) (ε/2)]
    calc C11 * ((4 + 4*K*2^(ε/2) + 1) * Work.FIArea4.p14T11 (m*Q) R S ε * (Real.log (2*R) + 1)
            * ((Work.FIArea4.p14L2 R S β') ^ ((1:ℝ)/2) * (Work.FIArea4.p14L2 R S γ') ^ ((1:ℝ)/2)))
        = (C11 * (4 + 4*K*2^(ε/2) + 1)) * Work.FIArea4.p14T11 (m*Q) R S ε * (Real.log (2*R) + 1)
            * ((Work.FIArea4.p14L2 R S β') ^ ((1:ℝ)/2) * (Work.FIArea4.p14L2 R S γ') ^ ((1:ℝ)/2)) := by ring
      _ ≤ (4*C11 + 4*C11*K*2^(ε/2) + C11 + 1) * Work.FIArea4.p14T11 (m*Q) R S ε * (Real.log (2*R) + 1)
            * ((Work.FIArea4.p14L2 R S β') ^ ((1:ℝ)/2) * (Work.FIArea4.p14L2 R S γ') ^ ((1:ℝ)/2)) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC11b ?_) ?_) (mul_nonneg hX hY)
          · exact p14T11_nonneg _ _ _ _
          · linarith [hlog]
      _ = (4*C11 + 4*C11*K*2^(ε/2) + C11 + 1) * Work.FIArea4.p14T11 (m*Q) R S ε * (Real.log (2*R) + 1)
            * (Work.FIArea4.p14L2 R S β') ^ ((1:ℝ)/2) * (Work.FIArea4.p14L2 R S γ') ^ ((1:ℝ)/2) := by ring
  rw [hLHS, hL2β, hL2γ]
  exact hbound


/-- **The `q`-weighted large-sieve bound for the coprime pair sum.**  Weights `A q` with
`‖A q‖ ≤ 1` are absorbed by the triangle inequality into the sum-of-norms estimate
`pairSumCo_Ioc_norm_le`, which the pigeonhole choice `A q = conj X_q / ‖X_q‖` shows to be the exact
content of the statement. -/
theorem pairSumCo_ls_twisted (h11 : Work.FIArea4.p14Prop111All) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ (m Q R S : ℕ) (β γ : ℕ → ℕ → ℂ) (A : ℕ → ℂ),
        1 ≤ m → 1 ≤ Q → 1 ≤ R → 1 ≤ S →
        (∀ r s, β r s ≠ 0 → Odd r) → (∀ r s, γ r s ≠ 0 → Odd r) →
        (∀ q, ‖A q‖ ≤ 1) →
        ‖∑ q ∈ Finset.Ioc Q (2 * Q), A q *
            Work.FIArea4.Vflip.Vfd.pairSumCo R S (m * q) β γ‖
          ≤ C * Work.FIArea4.p14T11 (m * Q) R S ε * (Real.log (2 * (R : ℝ)) + 1)
              * (Work.FIArea4.p14L2 R S β) ^ ((1 : ℝ) / 2)
              * (Work.FIArea4.p14L2 R S γ) ^ ((1 : ℝ) / 2) := by
  intro ε hε
  obtain ⟨C, hCpos, hC⟩ := pairSumCo_Ioc_norm_le h11 ε hε
  refine ⟨C, hCpos, ?_⟩
  intro m Q R S β γ A hm hQ hR hS hβodd hγodd hA
  refine le_trans ?_ (hC m Q R S β γ hm hQ hR hS hβodd hγodd)
  calc ‖∑ q ∈ Finset.Ioc Q (2*Q), A q * pairSumCo R S (m*q) β γ‖
      ≤ ∑ q ∈ Finset.Ioc Q (2*Q), ‖A q * pairSumCo R S (m*q) β γ‖ := norm_sum_le _ _
    _ = ∑ q ∈ Finset.Ioc Q (2*Q), ‖A q‖ * ‖pairSumCo R S (m*q) β γ‖ := by
        exact Finset.sum_congr rfl (fun q _ => by rw [norm_mul])
    _ ≤ ∑ q ∈ Finset.Ioc Q (2*Q), 1 * ‖pairSumCo R S (m*q) β γ‖ := by
        refine Finset.sum_le_sum (fun q _ => ?_)
        exact mul_le_mul_of_nonneg_right (hA q) (norm_nonneg _)
    _ = ∑ q ∈ Finset.Ioc Q (2*Q), ‖pairSumCo R S (m*q) β γ‖ := by
        exact Finset.sum_congr rfl (fun q _ => one_mul _)


end

end Work.FIArea4.Vflip.Vfd
