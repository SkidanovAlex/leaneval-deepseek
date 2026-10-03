import Mathlib
import Submission.Work.FIArea4.WdyadGen.Wdyad_strata_defs
import Submission.Work.FIArea4.WdyadGen.TZbox_stratum

namespace Work.FIArea4.WdyadGen

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-- The prefactor of the `e`-th stratum identity has `normSq ≤ 1`: it is either `0` or the
complex number attached to a Jacobi symbol, which is `0`, `1` or `-1`. -/
lemma normSq_stratum_prefactor (r e : ℕ) :
    Complex.normSq (if Nat.Coprime r e then
        (jacobiSym (r : ℤ) (Work.FIPlan.oddPart e) : ℂ) else 0) ≤ 1 := by
  by_cases hc : Nat.Coprime r e
  · rw [if_pos hc, Complex.normSq_intCast]
    rcases jacobiSym.trichotomy r (Work.FIPlan.oddPart e) with h | h | h
    · rw [h]; norm_num
    · rw [h]; norm_num
    · rw [h]; norm_num
  · rw [if_neg hc, Complex.normSq_zero]; norm_num

/-- The stratum inequality: the box form of the `gcd = e` stratum of `γ` over the modulus
window `(D, 2D]` is dominated by the box form of the reindexed coefficients `gamE γ e` over the
reduced modulus window `(D/e, 2D/e]` and the reduced `s`-window `(S/e, 2S/e]`. -/
theorem gLift_stratum_le (D R S e : ℕ) (γ : ℕ → ℕ → ℂ) (he : 1 ≤ e) :
    Work.FIArea4.WdyadGen.WboxI R S (2 * S) D (2 * D) (Work.FIArea4.gLift γ e)
      ≤ Work.FIArea4.WdyadGen.WboxI R (S / e) (2 * S / e) (D / e) (2 * D / e)
          (Work.FIArea4.gamE γ e) := by
  unfold WboxI
  refine Finset.sum_le_sum (fun r _ => ?_)
  set Z : ℕ → ℝ :=
    fun t => Complex.normSq (Work.FIArea4.TZbox (D / e) (2 * D / e) (Work.FIArea4.gamE γ e) r t)
    with hZ
  have hstep : ∀ s : ℕ,
      Complex.normSq (Work.FIArea4.TZbox D (2 * D) (Work.FIArea4.gLift γ e) r s)
        ≤ (if e ∣ s then Z (s / e) else 0) := by
    intro s
    rw [TZbox_stratum he γ D r s]
    by_cases hs : e ∣ s
    · rw [if_pos hs, if_pos hs, Complex.normSq_mul]
      refine le_trans (mul_le_of_le_one_left (Complex.normSq_nonneg _)
        (normSq_stratum_prefactor r e)) ?_
      simp only [hZ]
      exact le_refl _
    · rw [if_neg hs, if_neg hs]
      exact le_of_eq Complex.normSq_zero
  have hB : (∑ s ∈ Finset.Ioc S (2 * S), (if e ∣ s then Z (s / e) else 0))
      ≤ ∑ t ∈ Finset.Ioc (S / e) (2 * S / e), Z t := by
    have hsub : ((Finset.Ioc S (2 * S)).filter (fun s => e ∣ s)).image (fun s => s / e)
        ⊆ Finset.Ioc (S / e) (2 * S / e) := by
      intro t ht
      rw [Finset.mem_image] at ht
      obtain ⟨s, hs, rfl⟩ := ht
      rw [Finset.mem_filter, Finset.mem_Ioc] at hs
      obtain ⟨⟨hsl, hsh⟩, hsdvd⟩ := hs
      rw [Finset.mem_Ioc]
      refine ⟨?_, Nat.div_le_div_right hsh⟩
      rw [Nat.div_lt_iff_lt_mul (by omega : 0 < e), mul_comm (s / e) e,
        Nat.mul_div_cancel' hsdvd]
      exact hsl
    have hinj : Set.InjOn (fun s => s / e)
        ↑((Finset.Ioc S (2 * S)).filter (fun s => e ∣ s)) := by
      intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_filter] at hx hy
      have hxy' : x / e = y / e := hxy
      rw [← Nat.mul_div_cancel' hx.2, ← Nat.mul_div_cancel' hy.2, hxy']
    calc ∑ s ∈ Finset.Ioc S (2 * S), (if e ∣ s then Z (s / e) else 0)
        = ∑ s ∈ (Finset.Ioc S (2 * S)).filter (fun s => e ∣ s), Z (s / e) := by
          rw [Finset.sum_filter]
      _ = ∑ t ∈ ((Finset.Ioc S (2 * S)).filter (fun s => e ∣ s)).image
              (fun s => s / e), Z t := (Finset.sum_image hinj).symm
      _ ≤ ∑ t ∈ Finset.Ioc (S / e) (2 * S / e), Z t :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (fun t _ _ => Complex.normSq_nonneg _)
  exact le_trans (Finset.sum_le_sum (fun s _ => hstep s)) hB

end

end Work.FIArea4.WdyadGen
