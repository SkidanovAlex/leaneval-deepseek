import Mathlib
import Submission.Work.FIArea4.prop_11_1_defs
import Submission.Work.FIArea4.WdyadGenDefs
import Submission.Work.FIArea4.WdyadGen.Wdyad_strata_energy
import Submission.Work.FIArea4.Wdyad_units

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The gcd-strata decomposition of the dyadic dual variance, up to a divisor-count loss

`Work.FIArea4.Wdyad D R S γ` is a squared sum of class sums.  Splitting the coefficients `γ`
according to the gcd of `(a,d)` (`gLift γ e` is the stratum with `gcd a d = e`), the class sum
becomes a sum over the divisors `e` of `s`, so that

`|TZbox D (2D) γ r s|² ≤ τ(s) · Σ_e |TZbox D (2D) (gLift γ e) r s|²`.

Combining this with the *stratum energy* bound `Wdyad_strata_energy` (which sums the separate
stratum energies against `braceV`, using the unit-class estimate for each stratum) yields

`Wdyad D R S γ ≤ K · t · braceV D R S ε · WE D γ`

for any `S < R` and any `t` dominating `τ(s)` on the `s`-box.  The only loss is the trivial
divisor-count factor, which is subsequently absorbed using `(RS)^ε`-room.
-/

namespace Work.FIArea4

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Elementary Cauchy–Schwarz (local copy, to stay independent of the other modules) -/

/-- Cauchy–Schwarz for complex sums, cardinality form. -/
lemma normSq_sum_le_card_mul_sum'' {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    Complex.normSq (∑ x ∈ s, f x) ≤ (s.card : ℝ) * ∑ x ∈ s, Complex.normSq (f x) := by
  rw [Complex.normSq_eq_norm_sq]
  calc ‖∑ x ∈ s, f x‖ ^ 2 ≤ (∑ x ∈ s, ‖f x‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    _ ≤ (s.card : ℝ) * ∑ x ∈ s, ‖f x‖ ^ 2 := sq_sum_le_card_mul_sum_sq
    _ = (s.card : ℝ) * ∑ x ∈ s, Complex.normSq (f x) := by
        simp only [Complex.normSq_eq_norm_sq]

lemma Ioc_zero_eq_Icc_one (n : ℕ) : Finset.Ioc 0 n = Finset.Icc 1 n := by
  ext x; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega

/-! ## The strata of the class sum -/

/-- The strata of `γ` (by `gcd a d`) sum back to `γ` on the relevant box. -/
lemma sum_Icc_gLift_eq (D : ℕ) (γ : ℕ → ℕ → ℂ) {a d : ℕ} (hd : d ≤ 2 * D) (had : a < d) :
    ∑ e ∈ Finset.Icc 1 (2 * D), gLift γ e a d = γ a d := by
  have hdpos : 0 < d := by omega
  have hg1 : 1 ≤ Nat.gcd a d := Nat.gcd_pos_of_pos_right a hdpos
  have hg2 : Nat.gcd a d ≤ 2 * D := le_trans (Nat.gcd_le_right a hdpos) hd
  rw [Finset.sum_eq_single (Nat.gcd a d)]
  · simp [gLift]
  · intro e _ hne
    simp only [gLift]
    rw [if_neg (fun h => hne h.symm)]
  · intro h
    exact absurd (Finset.mem_Icc.mpr ⟨hg1, hg2⟩) h

/-- The class sum `TZbox` is the sum of its `gcd`-strata. -/
lemma TZbox_eq_sum_strata (D : ℕ) (γ : ℕ → ℕ → ℂ) (r s : ℕ) :
    TZbox D (2 * D) γ r s
      = ∑ e ∈ Finset.Icc 1 (2 * D), TZbox D (2 * D) (gLift γ e) r s := by
  unfold TZbox
  calc ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d, γ a d * Mentry d a r s
      = ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
          (∑ e ∈ Finset.Icc 1 (2 * D), gLift γ e a d) * Mentry d a r s := by
        refine Finset.sum_congr rfl (fun d hd => Finset.sum_congr rfl (fun a ha => ?_))
        rw [sum_Icc_gLift_eq D γ (Finset.mem_Ioc.mp hd).2 (Finset.mem_range.mp ha)]
    _ = ∑ d ∈ Finset.Ioc D (2 * D), ∑ a ∈ Finset.range d,
          ∑ e ∈ Finset.Icc 1 (2 * D), gLift γ e a d * Mentry d a r s := by
        refine Finset.sum_congr rfl (fun d _ => Finset.sum_congr rfl (fun a _ => ?_))
        rw [Finset.sum_mul]
    _ = ∑ d ∈ Finset.Ioc D (2 * D), ∑ e ∈ Finset.Icc 1 (2 * D),
          ∑ a ∈ Finset.range d, gLift γ e a d * Mentry d a r s := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [Finset.sum_comm]
    _ = ∑ e ∈ Finset.Icc 1 (2 * D), ∑ d ∈ Finset.Ioc D (2 * D),
          ∑ a ∈ Finset.range d, gLift γ e a d * Mentry d a r s := by
        rw [Finset.sum_comm]

/-- The stratum `e` of the class sum sees only `s` divisible by `e`. -/
lemma TZbox_gLift_dvd (D e r s : ℕ) (γ : ℕ → ℕ → ℂ) (he : 1 ≤ e)
    (h : TZbox D (2 * D) (gLift γ e) r s ≠ 0) : e ∣ s := by
  rw [TZbox] at h
  have hd : ∃ d ∈ Finset.Ioc D (2 * D),
      (∑ a ∈ Finset.range d, gLift γ e a d * Mentry d a r s) ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (Finset.sum_eq_zero hc)
  obtain ⟨d, hdmem, hdne⟩ := hd
  have ha : ∃ a ∈ Finset.range d, gLift γ e a d * Mentry d a r s ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact hdne (Finset.sum_eq_zero hc)
  obtain ⟨a, hamem, hane⟩ := ha
  have hgl : gLift γ e a d ≠ 0 := fun h0 => hane (by rw [h0, zero_mul])
  have hM : Mentry d a r s ≠ 0 := fun h0 => hane (by rw [h0, mul_zero])
  have hgcd : Nat.gcd a d = e := by
    by_contra hc
    simp only [gLift] at hgl
    rw [if_neg hc] at hgl
    exact hgl rfl
  have hcond : Nat.Coprime r d ∧ ((s : ZMod d) = (r : ZMod d) * (a : ZMod d)) := by
    by_contra hc
    simp only [Mentry] at hM
    rw [if_neg hc] at hM
    exact hM rfl
  have hmod : s ≡ r * a [MOD d] := by
    have h2 : ((s : ℕ) : ZMod d) = ((r * a : ℕ) : ZMod d) := by
      rw [hcond.2, Nat.cast_mul]
    exact (ZMod.natCast_eq_natCast_iff s (r * a) d).mp h2
  have hed : e ∣ d := hgcd ▸ Nat.gcd_dvd_right a d
  have hea : e ∣ a := hgcd ▸ Nat.gcd_dvd_left a d
  have hmod' : s ≡ r * a [MOD e] := hmod.of_dvd hed
  have hra : e ∣ r * a := Dvd.dvd.mul_left hea r
  have : s % e = 0 := by
    rw [hmod', Nat.mod_eq_zero_of_dvd hra]
  exact Nat.dvd_of_mod_eq_zero this

/-- **Cauchy–Schwarz over the strata**, with the divisor count of `s` as the loss. -/
lemma normSq_TZbox_le_divisors (D _R _S : ℕ) (γ : ℕ → ℕ → ℂ) (r s : ℕ) (hs : 0 < s) :
    Complex.normSq (TZbox D (2 * D) γ r s)
      ≤ ((s.divisors.card : ℕ) : ℝ) * ∑ e ∈ Finset.Icc 1 (2 * D),
          Complex.normSq (TZbox D (2 * D) (gLift γ e) r s) := by
  rw [TZbox_eq_sum_strata]
  set E : Finset ℕ := (Finset.Icc 1 (2 * D)).filter
      (fun e => TZbox D (2 * D) (gLift γ e) r s ≠ 0) with hE
  have hsum : (∑ e ∈ Finset.Icc 1 (2 * D), TZbox D (2 * D) (gLift γ e) r s)
      = ∑ e ∈ E, TZbox D (2 * D) (gLift γ e) r s := by
    rw [hE, Finset.sum_filter]
    exact Finset.sum_congr rfl (fun e _ => by
      by_cases h : TZbox D (2 * D) (gLift γ e) r s = 0 <;> simp [h])
  rw [hsum]
  have hcard : (E.card : ℝ) ≤ ((s.divisors.card : ℕ) : ℝ) := by
    have hsub : E ⊆ s.divisors := by
      intro e he
      rw [hE] at he
      simp only [Finset.mem_filter, Finset.mem_Icc] at he
      exact Nat.mem_divisors.mpr ⟨TZbox_gLift_dvd D e r s γ he.1.1 he.2, hs.ne'⟩
    exact_mod_cast Finset.card_le_card hsub
  calc Complex.normSq (∑ e ∈ E, TZbox D (2 * D) (gLift γ e) r s)
      ≤ (E.card : ℝ) * ∑ e ∈ E, Complex.normSq (TZbox D (2 * D) (gLift γ e) r s) :=
        normSq_sum_le_card_mul_sum'' E _
    _ ≤ ((s.divisors.card : ℕ) : ℝ)
          * ∑ e ∈ E, Complex.normSq (TZbox D (2 * D) (gLift γ e) r s) :=
        mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg (fun e _ => Complex.normSq_nonneg _))
    _ ≤ ((s.divisors.card : ℕ) : ℝ)
          * ∑ e ∈ Finset.Icc 1 (2 * D), Complex.normSq (TZbox D (2 * D) (gLift γ e) r s) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun e _ _ => Complex.normSq_nonneg _)
        rw [hE]; exact Finset.filter_subset _ _


/-! ## Sum rearrangements -/

/-- Swapping the outer two of three nested sums. -/
lemma sum_sum_sum_swap {R S K : ℕ} (F : ℕ → ℕ → ℕ → ℝ) :
    (∑ r ∈ Finset.Ioc R (2 * R), ∑ s ∈ Finset.Ioc S (2 * S),
        ∑ e ∈ Finset.Icc 1 K, F e r s)
      = ∑ e ∈ Finset.Icc 1 K, ∑ r ∈ Finset.Ioc R (2 * R),
          ∑ s ∈ Finset.Ioc S (2 * S), F e r s := by
  have h1 : ∀ r, (∑ s ∈ Finset.Ioc S (2 * S), ∑ e ∈ Finset.Icc 1 K, F e r s)
      = ∑ e ∈ Finset.Icc 1 K, ∑ s ∈ Finset.Ioc S (2 * S), F e r s :=
    fun r => Finset.sum_comm
  simp only [h1]
  exact Finset.sum_comm

/-- Pulling a scalar out of a doubly nested sum (`r` then `s`). -/
lemma mul_sum_sum {R S K : ℕ} (t : ℝ) (F : ℕ → ℕ → ℕ → ℝ) :
    (∑ r ∈ Finset.Ioc R (2 * R), ∑ s ∈ Finset.Ioc S (2 * S),
        t * ∑ e ∈ Finset.Icc 1 K, F e r s)
      = t * ∑ e ∈ Finset.Icc 1 K, ∑ r ∈ Finset.Ioc R (2 * R),
          ∑ s ∈ Finset.Ioc S (2 * S), F e r s := by
  have h1 : ∀ r s, t * (∑ e ∈ Finset.Icc 1 K, F e r s)
      = ∑ e ∈ Finset.Icc 1 K, t * F e r s := fun r s => Finset.mul_sum _ _ t
  simp only [h1]
  rw [sum_sum_sum_swap]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun r _ => ?_)
  rw [Finset.mul_sum]

/-- **Route S**: the dyadic dual variance is bounded by the target bracket, up to an arbitrary
divisor-count factor `t` dominating `τ(s)` on the `s`-box. -/
theorem Wdyad_le_tau_strata (ε : ℝ) (hε : 0 < ε) (C₁ : ℝ) (hC₁ : 0 < C₁)
    (hunit : ∀ (D₀ R S : ℕ) (β : ℕ → ℕ → ℂ), 1 ≤ D₀ → 1 ≤ R → 1 ≤ S →
      (∀ a d, β a d ≠ 0 → Nat.Coprime a d) →
      Work.FIArea4.Wdyad D₀ R S β ≤ C₁ * Work.FIArea4.WTb D₀ R S ε * Work.FIArea4.WE D₀ β) :
    ∃ K : ℝ, 0 < K ∧ ∀ (D R S : ℕ) (γ : ℕ → ℕ → ℂ) (t : ℝ),
      1 ≤ D → 1 ≤ R → 1 ≤ S → S < R →
      (∀ s ∈ Finset.Ioc S (2 * S), ((s.divisors.card : ℕ) : ℝ) ≤ t) →
      Work.FIArea4.Wdyad D R S γ ≤ K * t * Work.FIArea4.braceV D R S ε * Work.FIArea4.WE D γ := by
  obtain ⟨K₁, hK₁pos, hK₁⟩ := WdyadGen.Wdyad_strata_energy ε hε C₁ hC₁ hunit
  refine ⟨K₁, hK₁pos, ?_⟩
  intro D R S γ t hD hR hS hSR ht
  have hIoc : Finset.Ioc 0 (2 * D) = Finset.Icc 1 (2 * D) := Ioc_zero_eq_Icc_one (2 * D)
  have ht0 : 0 ≤ t := by
    have h1 : S + 1 ∈ Finset.Ioc S (2 * S) := by
      simp only [Finset.mem_Ioc]; omega
    exact le_trans (by positivity) (ht (S + 1) h1)
  have hW : Work.FIArea4.Wdyad D R S γ
      = ∑ r ∈ Finset.Ioc R (2 * R), ∑ s ∈ Finset.Ioc S (2 * S),
          Complex.normSq (TZbox D (2 * D) γ r s) := rfl
  rw [hW]
  have hpt : ∀ r ∈ Finset.Ioc R (2 * R), ∀ s ∈ Finset.Ioc S (2 * S),
      Complex.normSq (TZbox D (2 * D) γ r s)
        ≤ t * ∑ e ∈ Finset.Icc 1 (2 * D),
            Complex.normSq (TZbox D (2 * D) (gLift γ e) r s) := by
    intro r _ s hs
    have hs0 : 0 < s := by have := (Finset.mem_Ioc.mp hs).1; omega
    calc Complex.normSq (TZbox D (2 * D) γ r s)
        ≤ ((s.divisors.card : ℕ) : ℝ) * ∑ e ∈ Finset.Icc 1 (2 * D),
            Complex.normSq (TZbox D (2 * D) (gLift γ e) r s) :=
          normSq_TZbox_le_divisors D R S γ r s hs0
      _ ≤ t * ∑ e ∈ Finset.Icc 1 (2 * D),
            Complex.normSq (TZbox D (2 * D) (gLift γ e) r s) :=
          mul_le_mul_of_nonneg_right (ht s hs) (Finset.sum_nonneg (fun e _ => Complex.normSq_nonneg _))
  calc ∑ r ∈ Finset.Ioc R (2 * R), ∑ s ∈ Finset.Ioc S (2 * S),
          Complex.normSq (TZbox D (2 * D) γ r s)
      ≤ ∑ r ∈ Finset.Ioc R (2 * R), ∑ s ∈ Finset.Ioc S (2 * S),
          t * ∑ e ∈ Finset.Icc 1 (2 * D),
            Complex.normSq (TZbox D (2 * D) (gLift γ e) r s) :=
        Finset.sum_le_sum (fun r hr => Finset.sum_le_sum (fun s hs => hpt r hr s hs))
    _ = t * ∑ e ∈ Finset.Icc 1 (2 * D), ∑ r ∈ Finset.Ioc R (2 * R),
          ∑ s ∈ Finset.Ioc S (2 * S),
            Complex.normSq (TZbox D (2 * D) (gLift γ e) r s) :=
        mul_sum_sum t (fun e r s => Complex.normSq (TZbox D (2 * D) (gLift γ e) r s))
    _ ≤ t * (K₁ * Work.FIArea4.braceV D R S ε * Work.FIArea4.WE D γ) := by
        refine mul_le_mul_of_nonneg_left ?_ ht0
        have h := hK₁ D R S γ hD hR hS hSR
        rwa [hIoc] at h
    _ = K₁ * t * Work.FIArea4.braceV D R S ε * Work.FIArea4.WE D γ := by ring

end

end Work.FIArea4
