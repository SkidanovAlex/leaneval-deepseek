import Submission.Work.GYAvg
import Submission.Commons.NumberTheory.Sieve.card_system_eq_prod_primeFactors

/-!
# The local-factor factorisation of `rho` (Green–Tao §10, from eq. (10.2) to eq. (10.7))

For squarefree `d e : Fin m → ℕ` (the only values that matter, since the Möbius function kills the
others in `mainSum`), the density `ρ(d,e) = (D^t)^{-1}·#{x ∈ (ZMod D)^t : lcm(d_i,e_i) ∣ θ_i(x)}`
factorises over the primes of `D = ∏_i lcm(d_i,e_i)`:

`ρ(d,e) = ∏_{p | D} p^{-t} · locCount(p)`,

which is the input of the Euler-product step (`hasSum_dirichlet_eulerProduct`).
-/

open Finset
open scoped BigOperators

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace BoxAvg

variable {m t : ℕ}

open Commons.NumberTheory.Sieve

/-- The least common multiple of two squarefree numbers is squarefree. -/
lemma squarefree_lcm {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b) :
    Squarefree (Nat.lcm a b) := by
  have ha0 : a ≠ 0 := ha.ne_zero
  have hb0 : b ≠ 0 := hb.ne_zero
  have h0 : Nat.lcm a b ≠ 0 := Nat.lcm_ne_zero ha0 hb0
  rw [Nat.squarefree_iff_factorization_le_one h0]
  intro p
  rw [Nat.factorization_lcm ha0 hb0]
  exact max_le (((Nat.squarefree_iff_factorization_le_one ha0).mp ha) p)
    (((Nat.squarefree_iff_factorization_le_one hb0).mp hb) p)

/-- **The local-factor factorisation of `ρ`.** -/
theorem rho_eq_prod_locCount (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    (d e : Fin m → ℕ) (hdsq : ∀ i, Squarefree (d i)) (hesq : ∀ i, Squarefree (e i))
    (hMpos : ∀ i, 0 < Nat.lcm (d i) (e i)) :
    rho W A b d e
      = ∏ p ∈ (Ddd d e).primeFactors.attach, ((p : ℕ) ^ t : ℝ)⁻¹ *
          (@locCount m t W A b (fun i => Nat.lcm (d i) (e i)) (p : ℕ)
            (NeZero.of_pos (Nat.Prime.pos (Nat.prime_of_mem_primeFactors p.2)))) := by
  classical
  have hd1 : ∀ i, 1 ≤ d i := fun i => Nat.one_le_iff_ne_zero.mpr (hdsq i).ne_zero
  have he1 : ∀ i, 1 ≤ e i := fun i => Nat.one_le_iff_ne_zero.mpr (hesq i).ne_zero
  have hDpos : 0 < Ddd d e := Ddd_pos d e hd1 he1
  haveI : NeZero (Ddd d e) := ⟨ne_of_gt hDpos⟩
  have hL : ∀ i, Nat.lcm (d i) (e i) ∣ Ddd d e := dvd_prod_lcm d e
  have hMsq : ∀ i, Squarefree (Nat.lcm (d i) (e i)) :=
    fun i => squarefree_lcm (hdsq i) (hesq i)
  have hCRT := card_system_eq_prod_primeFactors (m := m) (t := t) W (Ddd d e) A b
      (fun i => Nat.lcm (d i) (e i)) hL hMsq hMpos
  have hLHS : ((Finset.univ : Finset (Fin t → ZMod (Ddd d e))).filter
        (fun x => ∀ i, ZMod.castHom (hL i) (ZMod (Nat.lcm (d i) (e i)))
          (thetaMod W A b (Ddd d e) i x) = 0)).card
      = (SsetZ W A b (Ddd d e) d e hL).card := rfl
  have hcard := card_Sfin_eq (m := m) (t := t) W A b d e hL
  have hCRT' : (((SsetZ W A b (Ddd d e) d e hL).card : ℕ) : ℝ)
      = ∏ p ∈ (Ddd d e).primeFactors.attach,
          (((p : ℕ) ^ (((Ddd d e).factorization p - 1) * t) *
            (@locCount m t W A b (fun i => Nat.lcm (d i) (e i)) (p : ℕ)
              (NeZero.of_pos (Nat.Prime.pos (Nat.prime_of_mem_primeFactors p.2))))) : ℝ) := by
    rw [← hLHS, hCRT]
    simp only [Nat.cast_prod, Nat.cast_mul, Nat.cast_pow]
  have hDt : (Ddd d e : ℝ) ^ t
      = ∏ p ∈ (Ddd d e).primeFactors, ((p : ℝ)) ^ ((Ddd d e).factorization p * t) := by
    have hnat : (Ddd d e) ^ t = ∏ p ∈ (Ddd d e).primeFactors,
        p ^ ((Ddd d e).factorization p * t) := by
      conv_lhs => rw [Nat.prod_primeFactors_pow_factorization (ne_of_gt hDpos)]
      rw [← Finset.prod_pow]
      exact Finset.prod_congr rfl (fun p _ => by rw [pow_mul])
    calc (Ddd d e : ℝ) ^ t = (((Ddd d e) ^ t : ℕ) : ℝ) := by push_cast; ring
      _ = ((∏ p ∈ (Ddd d e).primeFactors, p ^ ((Ddd d e).factorization p * t) : ℕ) : ℝ) := by
            rw [hnat]
      _ = ∏ p ∈ (Ddd d e).primeFactors, ((p : ℝ)) ^ ((Ddd d e).factorization p * t) := by
            rw [Nat.cast_prod]
            exact Finset.prod_congr rfl (fun p _ => by rw [Nat.cast_pow])
  rw [rho, hcard, hCRT', hDt]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_attach, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  have hprime : Nat.Prime p.1 := Nat.prime_of_mem_primeFactors p.2
  have hv : 1 ≤ (Ddd d e).factorization p.1 :=
    (hprime.dvd_iff_one_le_factorization (ne_of_gt hDpos)).mp (Nat.dvd_of_mem_primeFactors p.2)
  have hexp : ((Ddd d e).factorization p.1 - 1) * t + t = (Ddd d e).factorization p.1 * t := by
    have hsub : (Ddd d e).factorization p.1 - 1 + 1 = (Ddd d e).factorization p.1 :=
      Nat.sub_add_cancel hv
    calc ((Ddd d e).factorization p.1 - 1) * t + t
        = ((Ddd d e).factorization p.1 - 1) * t + 1 * t := by ring
      _ = (((Ddd d e).factorization p.1 - 1) + 1) * t := by ring
      _ = (Ddd d e).factorization p.1 * t := by rw [hsub]
  have hpow : (p.1 : ℝ) ^ ((Ddd d e).factorization p.1 * t)
      = (p.1 : ℝ) ^ (((Ddd d e).factorization p.1 - 1) * t) * (p.1 : ℝ) ^ t := by
    rw [← pow_add, hexp]
  rw [hpow]
  have hB : ((p.1 : ℝ) ^ (((Ddd d e).factorization p.1 - 1) * t)) ≠ 0 :=
    pow_ne_zero _ (by exact_mod_cast (ne_of_gt hprime.pos))
  have hD : ((p.1 : ℝ) ^ t) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (ne_of_gt hprime.pos))
  rw [mul_inv]
  field_simp

end BoxAvg
end GYMaj
