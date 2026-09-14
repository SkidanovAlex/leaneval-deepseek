import Mathlib
import Submission.Vdw.TameExponent
import Submission.Vdw.TamePrep
import Submission.Vdw.ResidueCompare
import Submission.Commons.NumberTheory.NumberField.different_not_pow_dvd_of_wild_witness
import Submission.Commons.RingTheory.DedekindDomain.pow_dvd_iff_normalizedFactors_count_le

open Classical
open scoped NumberField
open Ideal
open UniqueFactorizationMonoid

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# The wild small-prime discriminant bound (input side + reduction)

For a number field `K` of degree `n`, the Case-I *direct-regime* assembly
(S1 in the Roadmap) needs control of the *small-prime part*
`S := ∏_{p ≤ n} p^(v_p(|discr K|))` of the absolute discriminant: writing
`D = S · D*` (primes ≤ n / > n parts), the per-prime residue comparison
(`ResidueCompare.lemma24_field_Kpoly`) supplies the index conditions only at
primes `p > n`, and the per-D counting then runs over the large part `D*`
with the factor `S ≤ S₀(n)` absorbed — a constant depending only on `n`
(`CaseIDisc.discSmallPart_le_primorial_pow` reduces this to per-prime
exponent caps `v_p(|discr K|) ≤ C(n)` for `p ≤ n`).

The caps come from the **classical wild bound on the different**: for every
maximal ideal `P` of `𝒪_K` over `p` with ramification index `e_P`, the
exponent `m_P := (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P` of `P`
in the different ideal satisfies

    m_P ≤ e_P − 1 + e_P · v_p(e_P)        (Hensel/Conrad, "The Different
    Ideal" (4.12); sharp: equality for ℚ_p(p^(1/p^a)))

— the *tame* part `m_P ≤ e_P − 1` (i.e. `v_p(e_P) = 0`) being exactly
`Commons.NumberTheory.NumberField.tame_different_not_pow_dvd` (trace-witness
method, Session-30); the *wild* part (`p | e_P`) is **open** — Session-32's
delegation verdict: mathematically true but not dischargeable from current
Mathlib (local-field ramification-group theory absent); the reusable bridge
`different_not_pow_dvd_of_wild_witness` reduces it to a trace witness
`y ∈ Q^(v_p(e_P)+1)` with `p^(v_p(e_P)+1) ∤ Tr(y)`, equivalent by codifferent
duality.  The sum-level consequence (this module, PROVED):

    v_p(|discr K|) = Σ_{P | p} f_P · m_P ≤ n · (1 + ⌊log_p n⌋)   (all primes)

For `p > n` (`⌊log_p n⌋ = 0`) this is the tame bound `≤ n` (PROVED,
`discrVal_tame_le_degree`); for `p ≤ n` it is proved here **assuming** the
per-prime wild bound (hypothesis `hwild`), so the whole small-prime
programme reduces to the single open per-prime statement
`wild_different_count_le` (Roadmap Session-42).

Facts assembled: `TamePrep.discr_val_eq_f_mul_sub_one`-shape decompositions
(L60: `Commons.NumberTheory.NumberField.discr_padicValNat_eq_sum_over_p_count_mul_inertiaDeg`),
`ResidueCompare.diffFilter_sum_le_primesOver_sum` /
`mem_primesOverFinset_of_mem_diffFactors` / `sum_primesOverFinset_eq_sum_type` /
`sum_inertia_mul_ramIdx_sub_one_type` / `sum_ramification_inertia_type`,
`Ideal.ramificationIdx_pos` / `Ideal.inertiaDeg_pos`, Mathlib
`padicValNat_le_nat_log` and `Nat.log_mono_right`.
-/

namespace Submission.Vdw

noncomputable section

universe u
variable {K : Type u} [Field K] [NumberField K]

/-- **Tame bound.**  For a prime `p > [K : ℚ]` (tame at every prime of `K`),
`v_p(|discr K|) ≤ [K : ℚ]` — from the exact tame shape
`v_p(|discr K|) = Σ_{P | p} f_P (e_P − 1)` and `Σ_{P | p} f_P e_P = [K : ℚ]`. -/
theorem discrVal_tame_le_degree (p : ℕ) [Fact (Nat.Prime p)]
    (hgt : Module.finrank ℚ K < p) :
    padicValNat p (NumberField.discr K).natAbs ≤ Module.finrank ℚ K := by
  classical
  rw [discr_val_tame_of_gt_degree (K := K) (p := p) hgt]
  calc
    (((normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset.filter
        (fun P : Ideal (𝓞 K) => P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))).sum
        fun P : Ideal (𝓞 K) => P.inertiaDeg ℤ * (P.ramificationIdx ℤ - 1))
        ≤ ∑ q : (pZ p).primesOver (𝓞 K), q.1.inertiaDeg ℤ * (q.1.ramificationIdx ℤ - 1) :=
      diffFilter_sum_le_primesOver_sum (K := K) (p := p)
    _ = Module.finrank ℚ K - (∑ q : (pZ p).primesOver (𝓞 K), q.1.inertiaDeg ℤ) :=
      sum_inertia_mul_ramIdx_sub_one_type (K := K) (p := p)
    _ ≤ Module.finrank ℚ K := Nat.sub_le _ _

/-- A prime ideal over `p` has ramification index at most `[K : ℚ]` (its
`e_P·f_P` is a summand of the fundamental identity `Σ_{P|p} f_P e_P =
[K : ℚ]` and `f_P ≥ 1`). -/
lemma ramIdx_le_finrank_of_primeOver (p : ℕ) [Fact (Nat.Prime p)]
    (q : (pZ p).primesOver (𝓞 K)) :
    q.1.ramificationIdx ℤ ≤ Module.finrank ℚ K := by
  classical
  have hfpos : 0 < q.1.inertiaDeg ℤ := Ideal.inertiaDeg_pos (q := q.1) (R := ℤ)
  have hterm : q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ ≤
      (∑ r : (pZ p).primesOver (𝓞 K), r.1.ramificationIdx ℤ * r.1.inertiaDeg ℤ) := by
    exact Finset.single_le_sum (f := fun r : (pZ p).primesOver (𝓞 K) =>
      r.1.ramificationIdx ℤ * r.1.inertiaDeg ℤ) (s := Finset.univ)
      (fun r hr => Nat.zero_le _) (a := q) (Finset.mem_univ q)
  calc
    q.1.ramificationIdx ℤ ≤ q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ :=
      Nat.le_mul_of_pos_right _ hfpos
    _ ≤ ∑ r : (pZ p).primesOver (𝓞 K), r.1.ramificationIdx ℤ * r.1.inertiaDeg ℤ := hterm
    _ = Module.finrank ℚ K := sum_ramification_inertia_type (K := K) (p := p)

/-- The `p`-adic valuation of the ramification index of a prime over `p` is at
most `⌊log_p [K : ℚ]⌋ = Nat.log p [K : ℚ]` (Mathlib `padicValNat_le_nat_log`
plus monotonicity of `Nat.log`). -/
lemma padicValNat_ramIdx_le_natLog_finrank (p : ℕ) [Fact (Nat.Prime p)]
    (q : (pZ p).primesOver (𝓞 K)) :
    padicValNat p (q.1.ramificationIdx ℤ) ≤ Nat.log p (Module.finrank ℚ K) := by
  classical
  exact le_trans (padicValNat_le_nat_log (p := p) (n := q.1.ramificationIdx ℤ))
    (Nat.log_mono_right (ramIdx_le_finrank_of_primeOver (K := K) p q))

/-- Sum of the wild contributions over the primes over `p`:
`Σ_{q | p} f_q·e_q·v_p(e_q) ≤ [K : ℚ] · ⌊log_p [K : ℚ]⌋`. -/
lemma sum_primesOver_inertia_mul_ramIdx_mul_padicValNat_le (p : ℕ)
    [Fact (Nat.Prime p)] :
    (∑ q : (pZ p).primesOver (𝓞 K),
        q.1.inertiaDeg ℤ * (q.1.ramificationIdx ℤ * padicValNat p (q.1.ramificationIdx ℤ)))
      ≤ Module.finrank ℚ K * Nat.log p (Module.finrank ℚ K) := by
  classical
  let L : ℕ := Nat.log p (Module.finrank ℚ K)
  have hterm (q : (pZ p).primesOver (𝓞 K)) :
      q.1.inertiaDeg ℤ * (q.1.ramificationIdx ℤ * padicValNat p (q.1.ramificationIdx ℤ))
        ≤ q.1.inertiaDeg ℤ * (q.1.ramificationIdx ℤ * L) := by
    exact Nat.mul_le_mul_left (q.1.inertiaDeg ℤ)
      (Nat.mul_le_mul_left (q.1.ramificationIdx ℤ)
        (by simpa [L] using padicValNat_ramIdx_le_natLog_finrank (K := K) p q))
  calc
    (∑ q : (pZ p).primesOver (𝓞 K),
        q.1.inertiaDeg ℤ * (q.1.ramificationIdx ℤ * padicValNat p (q.1.ramificationIdx ℤ)))
      ≤ (∑ q : (pZ p).primesOver (𝓞 K),
          q.1.inertiaDeg ℤ * (q.1.ramificationIdx ℤ * L)) := by
        exact Finset.sum_le_sum (fun q hq => hterm q)
    _ = (∑ q : (pZ p).primesOver (𝓞 K),
          (q.1.inertiaDeg ℤ * q.1.ramificationIdx ℤ) * L) := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [mul_assoc]
    _ = (∑ q : (pZ p).primesOver (𝓞 K),
          q.1.inertiaDeg ℤ * q.1.ramificationIdx ℤ) * L := by
        rw [← Finset.sum_mul]
    _ = (∑ q : (pZ p).primesOver (𝓞 K),
          q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ) * L := by
        congr 1
        apply Finset.sum_congr rfl
        intro q hq
        rw [mul_comm]
    _ = Module.finrank ℚ K * Nat.log p (Module.finrank ℚ K) := by
        rw [sum_ramification_inertia_type (K := K) (p := p)]


/-- The wild weight sum over the different-ideal factors over `p` does not
exceed the sum over all primes of `𝒪_K` over `p` (weights
`f_P·(e_P·v_p(e_P)) ≥ 0`, filter ⊆ primes-over-p). -/
lemma diffFilter_wildWeight_le_primesOver (p : ℕ) [Fact (Nat.Prime p)] :
    (∑ P ∈ (normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset.filter
        (fun P : Ideal (𝓞 K) => P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))),
          P.inertiaDeg ℤ * (P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ)))
      ≤ ∑ q : (pZ p).primesOver (𝓞 K),
          q.1.inertiaDeg ℤ * (q.1.ramificationIdx ℤ * padicValNat p (q.1.ramificationIdx ℤ)) := by
  classical
  let s := IsDedekindDomain.primesOverFinset (pZ p) (𝓞 K)
  let w := fun P : Ideal (𝓞 K) =>
    P.inertiaDeg ℤ * (P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ))
  have hsub : ((normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset.filter
      (fun P : Ideal (𝓞 K) => P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))) ⊆ s := by
    intro P hP
    exact mem_primesOverFinset_of_mem_diffFactors (K := K) p
      (Finset.mem_filter.mp hP).1 (Finset.mem_filter.mp hP).2
  have hle : (∑ P ∈ ((normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset.filter
      (fun P : Ideal (𝓞 K) => P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))), w P) ≤ ∑ P ∈ s, w P := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro x hx hxA; exact Nat.zero_le _)
  rw [← sum_primesOverFinset_eq_sum_type (K := K) p w]
  simpa [s, w] using hle

/-- **Sum-level wild bound (with the per-prime wild different bound as a
hypothesis).**  For a number field `K`, every prime `p`, and the classical
per-prime bound `m_P ≤ e_P − 1 + e_P·v_p(e_P)` (tame: provable — Session-30;
wild: the open `wild_different_count_le`, see the module docstring):
`v_p(|discr K|) ≤ [K : ℚ]·(1 + ⌊log_p [K : ℚ]⌋)`.  For `p > [K : ℚ]`
(`⌊log_p [K : ℚ]⌋ = 0`) this is the unconditional tame bound
`discrVal_tame_le_degree`; for `p ≤ [K : ℚ]` the wild contribution
`Σ_{q | p} f_q·e_q·v_p(e_q) ≤ [K : ℚ]·⌊log_p [K : ℚ]⌋` dominates the
`e_q − 1` parts, giving the constant exponent cap (in `n` only) that the
Case-I small-prime programme needs. -/
theorem discrVal_le_wild (p : ℕ) [Fact (Nat.Prime p)]
    (hwild : ∀ P : Ideal (𝓞 K), P.IsMaximal →
        P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) →
        (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P ≤
          P.ramificationIdx ℤ - 1 + P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ)) :
    padicValNat p (NumberField.discr K).natAbs ≤
      Module.finrank ℚ K + Module.finrank ℚ K * Nat.log p (Module.finrank ℚ K) := by
  classical
  by_cases hgt : Module.finrank ℚ K < p
  · exact le_trans (discrVal_tame_le_degree (K := K) p hgt) (Nat.le_add_right _ _)
  · let F : Finset (Ideal (𝓞 K)) :=
      (normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset.filter
        (fun P : Ideal (𝓞 K) => P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)))
    let T := (pZ p).primesOver (𝓞 K)
    -- step 1: L60 decomposition
    have hL60 : padicValNat p (NumberField.discr K).natAbs =
        F.sum (fun P : Ideal (𝓞 K) => (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P * P.inertiaDeg ℤ) := by
      simpa [F] using (Commons.NumberTheory.NumberField.discr_padicValNat_eq_sum_over_p_count_mul_inertiaDeg (K := K) (p := p))
    -- step 2: per-term wild bound m·f ≤ (e−1+e·v)·f
    have hδ : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot (A := ℤ) (B := 𝓞 K)
    have hstep : ∀ P ∈ F,
        (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P * P.inertiaDeg ℤ ≤
          (P.ramificationIdx ℤ - 1 + P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ)) * P.inertiaDeg ℤ := by
      intro P hP
      have hPF' : P ∈ (normalizedFactors (differentIdeal ℤ (𝓞 K))).toFinset.filter
          (fun Q : Ideal (𝓞 K) => Q.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))) := by
        simpa [F] using hP
      simp at hPF'
      have hPmem : P ∈ normalizedFactors (differentIdeal ℤ (𝓞 K)) :=
        Multiset.mem_toFinset.mp hPF'.1
      have hlies : P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ)) := hPF'.2
      have hmax : P.IsMaximal :=
        Commons.NumberTheory.NumberField.isMaximal_of_mem_normalizedFactors hδ hPmem
      exact Nat.mul_le_mul_right _ (hwild P hmax hlies)
    have hsum1 : F.sum (fun P : Ideal (𝓞 K) =>
          (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P * P.inertiaDeg ℤ) ≤
        F.sum (fun P : Ideal (𝓞 K) =>
          (P.ramificationIdx ℤ - 1 + P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ)) * P.inertiaDeg ℤ) := by
      exact Finset.sum_le_sum (fun P hP => hstep P hP)
    -- step 3: (e−1+e·v)·f = f·(e−1) + f·(e·v) pointwise
    have hsplit : F.sum (fun P : Ideal (𝓞 K) =>
          (P.ramificationIdx ℤ - 1 + P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ)) * P.inertiaDeg ℤ) =
        F.sum (fun P : Ideal (𝓞 K) => P.inertiaDeg ℤ * (P.ramificationIdx ℤ - 1)) +
        F.sum (fun P : Ideal (𝓞 K) =>
          P.inertiaDeg ℤ * (P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro P hP
      rw [add_mul, mul_comm (P.ramificationIdx ℤ - 1), mul_comm (P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ))]
    -- step 4: two subset bounds and the two type-sum bounds
    have hsubA : F.sum (fun P : Ideal (𝓞 K) => P.inertiaDeg ℤ * (P.ramificationIdx ℤ - 1)) ≤
        (∑ q : (pZ p).primesOver (𝓞 K), q.1.inertiaDeg ℤ * (q.1.ramificationIdx ℤ - 1)) := by
      simpa [F] using (diffFilter_sum_le_primesOver_sum (K := K) (p := p))
    have hsubB : F.sum (fun P : Ideal (𝓞 K) =>
          P.inertiaDeg ℤ * (P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ))) ≤
        (∑ q : (pZ p).primesOver (𝓞 K),
          q.1.inertiaDeg ℤ * (q.1.ramificationIdx ℤ * padicValNat p (q.1.ramificationIdx ℤ))) := by
      simpa [F] using (diffFilter_wildWeight_le_primesOver (K := K) (p := p))
    have hleA : (∑ q : (pZ p).primesOver (𝓞 K), q.1.inertiaDeg ℤ * (q.1.ramificationIdx ℤ - 1)) ≤
        Module.finrank ℚ K := by
      calc
        (∑ q : (pZ p).primesOver (𝓞 K), q.1.inertiaDeg ℤ * (q.1.ramificationIdx ℤ - 1))
            = Module.finrank ℚ K - (∑ q : (pZ p).primesOver (𝓞 K), q.1.inertiaDeg ℤ) :=
              sum_inertia_mul_ramIdx_sub_one_type (K := K) (p := p)
        _ ≤ Module.finrank ℚ K := Nat.sub_le _ _
    have hleB : (∑ q : (pZ p).primesOver (𝓞 K),
          q.1.inertiaDeg ℤ * (q.1.ramificationIdx ℤ * padicValNat p (q.1.ramificationIdx ℤ))) ≤
        Module.finrank ℚ K * Nat.log p (Module.finrank ℚ K) :=
      sum_primesOver_inertia_mul_ramIdx_mul_padicValNat_le (K := K) (p := p)
    calc
      padicValNat p (NumberField.discr K).natAbs
          = F.sum (fun P : Ideal (𝓞 K) => (normalizedFactors (differentIdeal ℤ (𝓞 K))).count P * P.inertiaDeg ℤ) := hL60
      _ ≤ F.sum (fun P : Ideal (𝓞 K) =>
            (P.ramificationIdx ℤ - 1 + P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ)) * P.inertiaDeg ℤ) := hsum1
      _ = F.sum (fun P : Ideal (𝓞 K) => P.inertiaDeg ℤ * (P.ramificationIdx ℤ - 1)) +
            F.sum (fun P : Ideal (𝓞 K) =>
              P.inertiaDeg ℤ * (P.ramificationIdx ℤ * padicValNat p (P.ramificationIdx ℤ))) := hsplit
      _ ≤ (∑ q : (pZ p).primesOver (𝓞 K), q.1.inertiaDeg ℤ * (q.1.ramificationIdx ℤ - 1)) +
            (∑ q : (pZ p).primesOver (𝓞 K),
              q.1.inertiaDeg ℤ * (q.1.ramificationIdx ℤ * padicValNat p (q.1.ramificationIdx ℤ))) := by
              exact Nat.add_le_add hsubA hsubB
      _ ≤ Module.finrank ℚ K + Module.finrank ℚ K * Nat.log p (Module.finrank ℚ K) := by
              exact Nat.add_le_add hleA hleB

end
end Submission.Vdw
