import Submission.Work.GYFactor2
import Submission.Commons.NumberTheory.Sieve.locCount_ite_le
import Submission.Commons.NumberTheory.Sieve.hasSum_dirichlet_eulerProduct_weighted

/-!
# The local weights `vSys` satisfy the hypotheses of the weighted Euler product (GT §10, (10.7))

`Submission/Work/GYFactor2.lean` defines the local weight `vSys W A b p σ` of the affine system and
proves `rho = localWeight (vSys)`.  This file shows that `vSys` meets the four hypotheses (`hv1`,
`hv2`, `hv3`, `hv4`) of `Commons.NumberTheory.Sieve.hasSum_dirichlet_eulerProduct_weighted`, and
deduces the Euler-product representation of the §10 Dirichlet series (Green–Tao (10.6) = (10.7)).
-/

open Finset
open scoped BigOperators

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace BoxAvg

variable {m t : ℕ}

open Commons.NumberTheory.Sieve

/-- The local weight is a density, hence at most `1`. -/
lemma norm_vSys_le_one (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (p : ℕ)
    (σ : PrimeData m) : ‖vSys W A b p σ‖ ≤ 1 := by
  classical
  by_cases hp : p.Prime
  · rw [vSys, dif_pos hp]
    haveI : NeZero p := NeZero.of_pos hp.pos
    have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
    have hcard : (@locCount m t W A b (fun i => if i ∈ σ.X ∪ σ.X' then p else 1) p
        (NeZero.of_pos hp.pos)) ≤ p ^ t := by
      rw [locCount]
      calc ((Finset.univ : Finset (Fin t → ZMod p)).filter _).card
          ≤ (Finset.univ : Finset (Fin t → ZMod p)).card := Finset.card_filter_le _ _
        _ = p ^ t := by rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card]
    rw [norm_div, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
    rw [div_le_one (pow_pos hp0 t)]
    exact_mod_cast hcard
  · rw [vSys, dif_neg hp]
    split_ifs <;> simp

/-- **The local density bound** (Green–Tao's Lemma 10.1, quantitative form): for a prime `p` and a
nonzero local datum `σ`, the density of the system is at most `(Amax + W + 1)/p`. -/
lemma vSys_norm_le_inv {p : ℕ} [Fact p.Prime] {Amax : ℕ} (W : ℕ) (A : Fin m → Fin t → ℤ)
    (b : Fin m → ℤ) (ht : 1 ≤ t) (hA : ∀ i j, (A i j).natAbs ≤ Amax)
    (hne : ∀ i, ∃ j, A i j ≠ 0) (hW0 : 0 < W) :
    ∀ σ : PrimeData m, σ ≠ 0 → ‖vSys W A b p σ‖ ≤ ((Amax : ℝ) + W + 1) / p := by
  intro σ hσ
  have hp1 : (1 : ℝ) ≤ (p : ℝ) := by
    have := (Fact.out : p.Prime).one_lt
    exact_mod_cast this.le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  by_cases hbig : Amax < p ∧ W < p
  · rw [vSys, dif_pos (Fact.out : p.Prime)]
    set n : ℕ := @locCount m t W A b (fun i => if i ∈ σ.X ∪ σ.X' then p else 1) p
      (NeZero.of_pos (Fact.out : p.Prime).pos) with hn
    have hcard : n ≤ p ^ (t - 1) := by
      rw [hn]
      exact locCount_ite_le (p := p) (m := m) (t := t) W Amax A b σ hσ ht hA hne hW0 hbig.2 hbig.1
    have h3 : (n : ℝ) ≤ (p : ℝ) ^ (t - 1) := by exact_mod_cast hcard
    have h4 : (p : ℝ) ^ t = (p : ℝ) ^ (t - 1) * (p : ℝ) := by
      rw [← pow_succ, Nat.sub_add_cancel ht]
    have h5 : ‖(n : ℂ) / ((p : ℂ) ^ t)‖ ≤ 1 / (p : ℝ) := by
      rw [norm_div, norm_pow, Complex.norm_natCast, Complex.norm_natCast]
      rw [div_le_div_iff₀ (pow_pos hp0 t) hp0, h4]
      calc (n : ℝ) * (p : ℝ) ≤ (p : ℝ) ^ (t - 1) * (p : ℝ) :=
            mul_le_mul_of_nonneg_right h3 hp0.le
        _ = 1 * ((p : ℝ) ^ (t - 1) * (p : ℝ)) := by ring
    rw [hn] at h5
    refine le_trans h5 ?_
    rw [div_le_div_iff_of_pos_right hp0]
    have : (0 : ℝ) ≤ (Amax : ℝ) + W := by positivity
    linarith
  · have hple : p ≤ Amax + W := by omega
    have h1 : ‖vSys W A b p σ‖ ≤ 1 := norm_vSys_le_one W A b p σ
    have h2 : (1 : ℝ) ≤ ((Amax : ℝ) + W + 1) / p := by
      rw [le_div_iff₀ hp0]
      have : (p : ℝ) ≤ (Amax : ℝ) + W := by exact_mod_cast hple
      linarith
    linarith

/-- **`hv4` for `vSys`**, for every modulus `p` (composite moduli give the value `0`). -/
lemma vSys_norm_le_div {Amax : ℕ} (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    (ht : 1 ≤ t) (hA : ∀ i j, (A i j).natAbs ≤ Amax) (hne : ∀ i, ∃ j, A i j ≠ 0)
    (hW0 : 0 < W) :
    ∀ (p : ℕ) (σ : PrimeData m), σ ≠ 0 → ‖vSys W A b p σ‖ ≤ ((Amax : ℝ) + W + 1) / p := by
  intro p σ hσ
  by_cases hp : p.Prime
  · haveI : Fact p.Prime := ⟨hp⟩
    exact vSys_norm_le_inv (p := p) W A b ht hA hne hW0 σ hσ
  · rw [vSys_of_not_prime W A b p σ hp hσ, norm_zero]
    exact div_nonneg (by positivity) (Nat.cast_nonneg _)

/-- **The weighted summability hypothesis** (`hv3`) for `vSys`: for every `c > 0`,
`∑_p ∑_σ ‖vSys p σ - 1_{σ=0}‖·p^{-c} < ∞`. -/
lemma vSys_summable {c : ℝ} (hc : 0 < c) {Amax : ℕ} (W : ℕ) (A : Fin m → Fin t → ℤ)
    (b : Fin m → ℤ) (ht : 1 ≤ t) (hA : ∀ i j, (A i j).natAbs ≤ Amax)
    (hne : ∀ i, ∃ j, A i j ≠ 0) (hW0 : 0 < W) :
    Summable (fun p : ℕ =>
      ∑ σ : PrimeData m, ‖vSys W A b p σ - (if σ = 0 then 1 else 0)‖ * (p : ℝ) ^ (-c)) := by
  classical
  set K : ℝ := (Fintype.card (PrimeData m) : ℝ) * ((Amax : ℝ) + W + 1) with hK
  have hbase : Summable (fun p : ℕ => (((p : ℝ)) ^ (1 + c))⁻¹) :=
    Real.summable_nat_rpow_inv.mpr (show (1 : ℝ) < 1 + c by linarith)
  refine Summable.of_nonneg_of_le
    (fun p => Finset.sum_nonneg (fun σ _ => by positivity)) (fun p => ?_)
    (Summable.mul_left K hbase)
  by_cases hp : p.Prime
  · haveI : Fact p.Prime := ⟨hp⟩
    have hp0 : (0 : ℝ) ≤ (p : ℝ) := by positivity
    have hpc : (0 : ℝ) ≤ (p : ℝ) ^ (-c) := Real.rpow_nonneg hp0 _
    have hbound : ∀ σ ∈ (Finset.univ : Finset (PrimeData m)),
        ‖vSys W A b p σ - (if σ = 0 then 1 else 0)‖ * (p : ℝ) ^ (-c)
          ≤ ((Amax : ℝ) + W + 1) / p * (p : ℝ) ^ (-c) := by
      intro σ _
      refine mul_le_mul_of_nonneg_right ?_ hpc
      by_cases hσ : σ = 0
      · subst hσ
        rw [vSys_zero, if_pos rfl, sub_self, norm_zero]
        positivity
      · rw [if_neg hσ]
        simpa using vSys_norm_le_inv (p := p) W A b ht hA hne hW0 σ hσ
    calc ∑ σ : PrimeData m, ‖vSys W A b p σ - (if σ = 0 then 1 else 0)‖ * (p : ℝ) ^ (-c)
        ≤ ∑ _σ : PrimeData m, ((Amax : ℝ) + W + 1) / p * (p : ℝ) ^ (-c) :=
          Finset.sum_le_sum hbound
      _ = K * (((p : ℝ)) ^ (1 + c))⁻¹ := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hK]
          have hpne : (p : ℝ) ≠ 0 := by
            have := (Fact.out : p.Prime).pos
            positivity
          have hkey : ((p : ℝ)) ^ (1 + c) = (p : ℝ) * (p : ℝ) ^ c := by
            rw [Real.rpow_add (by positivity), Real.rpow_one]
          rw [hkey, mul_inv, Real.rpow_neg (Nat.cast_nonneg p) c]
          field_simp
  · have hsum0 : (∑ σ : PrimeData m,
        ‖vSys W A b p σ - (if σ = 0 then 1 else 0)‖ * (p : ℝ) ^ (-c)) = 0 := by
      refine Finset.sum_eq_zero (fun σ _ => ?_)
      by_cases hσ : σ = 0
      · subst hσ
        rw [vSys_zero, if_pos rfl, sub_self, norm_zero, zero_mul]
      · rw [if_neg hσ, vSys_of_not_prime W A b p σ hp hσ]
        simp
    rw [hsum0]
    positivity

/-- **The Euler product of the §10 Dirichlet series** (Green–Tao (10.6) = (10.7)), for the local
weights of the affine system and exponents with real part `≥ 1` (where everything converges
absolutely). -/
theorem hasSum_eulerProduct_vSys {Amax : ℕ} (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    (ht : 1 ≤ t) (hA : ∀ i j, (A i j).natAbs ≤ Amax) (hne : ∀ i, ∃ j, A i j ≠ 0)
    (hW0 : 0 < W) (z z' : Fin m → ℂ) (hz : ∀ i, 1 ≤ (z i).re) (hz' : ∀ i, 1 ≤ (z' i).re) :
    HasSum (fun de : (Fin m → ℕ) × (Fin m → ℕ) =>
        (∏ i, ((ArithmeticFunction.moebius (de.1 i) : ℂ)
            * (ArithmeticFunction.moebius (de.2 i) : ℂ)
            * ((de.1 i : ℂ) ^ (-(z i))) * ((de.2 i : ℂ) ^ (-(z' i)))))
        * localWeight m (vSys W A b) de.1 de.2)
      (∏' p : ℕ, eulerFactor m (vSys W A b) z z' p) :=
  hasSum_dirichlet_eulerProduct_weighted m (vSys W A b) ((Amax : ℝ) + W + 1) 1 one_pos
    (vSys_zero W A b) (fun p hp σ hσ => vSys_of_not_prime W A b p σ hp hσ)
    (vSys_summable one_pos W A b ht hA hne hW0)
    (fun p σ hσ => vSys_norm_le_div W A b ht hA hne hW0 p σ hσ) z z' hz hz'

end BoxAvg
end GYMaj
