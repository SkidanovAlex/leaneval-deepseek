import Submission.Work.GYFactor
import Submission.Commons.NumberTheory.Sieve.hasSum_dirichlet_eulerProduct

/-!
# The `localWeight` form of `rho` (Green–Tao §10, the Euler-product step)

`Submission/Work/GYFactor.lean` proves the CRT factorisation
`rho d e = ∏_{p | D} p^{-t}·locCount(p)`.  For the Euler-product step
(`Commons.NumberTheory.Sieve.hasSum_dirichlet_eulerProduct`) the Dirichlet series must be written
with the *global* coefficient `localWeight m v d e = ∏_{p | ∏_i d_i e_i} v_p ⟨{i : p | d_i}, {i : p | e_i}⟩`
for a local weight `v : ℕ → PrimeData m → ℂ` independent of `d, e`.

This file identifies the two: for squarefree `d, e` and the local weight
`vSys p σ = p^{-t}·#{x : ∀ i ∈ σ.X ∪ σ.X', θ_i(x) = 0}` one has
`rho d e = localWeight m (vSys ) d e`.
-/

open Finset
open scoped BigOperators

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false

namespace GYMaj
namespace BoxAvg

variable {m t : ℕ}

open Commons.NumberTheory.Sieve

/-- The prime factors of a least common multiple. -/
lemma primeFactors_lcm {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (Nat.lcm a b).primeFactors = a.primeFactors ∪ b.primeFactors := by
  ext p
  rw [Finset.mem_union, Nat.mem_primeFactors, Nat.mem_primeFactors, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hdvd, _⟩
    rcases hp.dvd_lcm.mp hdvd with h | h
    · exact Or.inl ⟨hp, h, ha⟩
    · exact Or.inr ⟨hp, h, hb⟩
  · rintro (⟨hp, h, _⟩ | ⟨hp, h, _⟩)
    · exact ⟨hp, h.trans (Nat.dvd_lcm_left _ _), Nat.lcm_ne_zero ha hb⟩
    · exact ⟨hp, h.trans (Nat.dvd_lcm_right _ _), Nat.lcm_ne_zero ha hb⟩

/-- The prime factors of a finite product of nonzero numbers. -/
lemma primeFactors_finset_prod {ι : Type*} (s : Finset ι) (f : ι → ℕ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    (∏ i ∈ s, f i).primeFactors = s.biUnion (fun i => (f i).primeFactors) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.biUnion_insert]
      have hfa : f a ≠ 0 := hf a (Finset.mem_insert_self a s)
      have hfs : ∀ i ∈ s, f i ≠ 0 := fun i hi => hf i (Finset.mem_insert_of_mem hi)
      have hprod : (∏ i ∈ s, f i) ≠ 0 := Finset.prod_ne_zero_iff.mpr hfs
      rw [Nat.primeFactors_mul hfa hprod, ih hfs]

/-- The moduli agree at every prime: `p | lcm (d i) (e i) ↔ p | (if i ∈ X ∪ X' then p else 1)`
for `X = {i : p | d i}`, `X' = {i : p | e i}`. -/
lemma dvd_ite_iff {p : ℕ} (hp : p.Prime) (d e : Fin m → ℕ) (i : Fin m) :
    (p ∣ Nat.lcm (d i) (e i))
      ↔ p ∣ (if i ∈ (Finset.univ.filter (fun i => p ∣ d i))
                ∪ (Finset.univ.filter (fun i => p ∣ e i)) then p else 1) := by
  have hmem : i ∈ (Finset.univ.filter (fun i => p ∣ d i))
        ∪ (Finset.univ.filter (fun i => p ∣ e i)) ↔ p ∣ d i ∨ p ∣ e i := by
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    simp
  by_cases h : i ∈ (Finset.univ.filter (fun i => p ∣ d i))
        ∪ (Finset.univ.filter (fun i => p ∣ e i))
  · rw [if_pos h, hp.dvd_lcm]
    exact ⟨fun _ => dvd_refl p, fun _ => hmem.mp h⟩
  · rw [if_neg h, Nat.dvd_one, hp.dvd_lcm]
    exact ⟨fun hh => absurd (hmem.mpr hh) h, fun hh => absurd hh hp.ne_one⟩

/-- **The local weight of the affine system.**  For a prime `p`, `vSys p σ` is the density, in
`(ZMod p)^t`, of the solution set of `θ_i(x) = 0` for the indices `i` with `p | d_i` or `p | e_i` —
a function of the local data `σ` alone (not of `d, e`), which is exactly what `localWeight` needs.
For a composite `p` (`p = 0` or `p = 1` included) we set `vSys p 0 = 1` and `vSys p σ = 0` otherwise,
as required by the Euler-product interface (`hv1`, `hv2` of
`Commons.NumberTheory.Sieve.hasSum_dirichlet_eulerProduct_weighted`). -/
noncomputable def vSys (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (p : ℕ)
    (σ : PrimeData m) : ℂ :=
  if hp : p.Prime then
    ((@locCount m t W A b (fun i => if i ∈ σ.X ∪ σ.X' then p else 1) p
        (NeZero.of_pos hp.pos) : ℕ) : ℂ) / ((p : ℂ) ^ t)
  else if σ = 0 then 1 else 0

/-- The local density `locCount` only depends on the prime divisors of the moduli. -/
lemma locCount_congr_iff {W N : ℕ} [NeZero N] {A : Fin m → Fin t → ℤ} {b : Fin m → ℤ}
    {M M' : Fin m → ℕ} (h : ∀ i, (N ∣ M i ↔ N ∣ M' i)) :
    locCount W A b M N = locCount W A b M' N := by
  classical
  have hset : (Finset.univ.filter (fun x => ∀ i, N ∣ M i → thetaMod W A b N i x = 0))
      = (Finset.univ.filter (fun x => ∀ i, N ∣ M' i → thetaMod W A b N i x = 0)) := by
    refine Finset.filter_congr (fun x _ => ?_)
    exact forall_congr' (fun i => imp_congr (h i) Iff.rfl)
  simp only [locCount, hset]


/-- **From `rho` to the Euler-product coefficient `localWeight`.**  For squarefree `d, e`, the
congruence density `ρ(d,e)` is the global coefficient `localWeight` of the local weights `vSys`. -/
theorem rho_eq_localWeight (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    (d e : Fin m → ℕ) (hdsq : ∀ i, Squarefree (d i)) (hesq : ∀ i, Squarefree (e i))
    (hMpos : ∀ i, 0 < Nat.lcm (d i) (e i)) :
    ((rho W A b d e : ℝ) : ℂ) = localWeight m (vSys W A b) d e := by
  classical
  have hd0 : ∀ i, d i ≠ 0 := fun i => (hdsq i).ne_zero
  have he0 : ∀ i, e i ≠ 0 := fun i => (hesq i).ne_zero
  have hD : (Ddd d e).primeFactors = (∏ i, d i * e i).primeFactors := by
    rw [Ddd]
    rw [primeFactors_finset_prod (ι := Fin m) Finset.univ (fun i => Nat.lcm (d i) (e i))
      (fun i _ => Nat.lcm_ne_zero (hd0 i) (he0 i))]
    rw [primeFactors_finset_prod (ι := Fin m) Finset.univ (fun i => d i * e i)
      (fun i _ => mul_ne_zero (hd0 i) (he0 i))]
    refine Finset.biUnion_congr rfl (fun i _ => ?_)
    rw [primeFactors_lcm (hd0 i) (he0 i), Nat.primeFactors_mul (hd0 i) (he0 i)]
  rw [rho_eq_prod_locCount W A b d e hdsq hesq hMpos, localWeight, ← hD]
  conv_rhs => rw [← Finset.prod_attach]
  rw [Complex.ofReal_prod]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  have hpp : p.1.Prime := Nat.prime_of_mem_primeFactors p.2
  have hlc : (@locCount m t W A b (fun i => Nat.lcm (d i) (e i)) p.1
        (NeZero.of_pos (Nat.Prime.pos (Nat.prime_of_mem_primeFactors p.2))))
      = (@locCount m t W A b
          (fun i => if i ∈ (Finset.univ.filter (fun i => p.1 ∣ d i))
              ∪ (Finset.univ.filter (fun i => p.1 ∣ e i)) then p.1 else 1) p.1
          (NeZero.of_pos hpp.pos)) :=
    locCount_congr_iff (fun i => dvd_ite_iff hpp d e i)
  rw [vSys, dif_pos hpp, hlc]
  push_cast
  rw [div_eq_mul_inv]
  ring


/-- The count is `p^t` for the vacuous system (all moduli equal to `1`). -/
lemma locCount_one {p : ℕ} [NeZero p] (hp : p.Prime) (W : ℕ) (A : Fin m → Fin t → ℤ)
    (b : Fin m → ℤ) : locCount W A b (fun _ => 1) p = p ^ t := by
  classical
  rw [locCount]
  have hfilter : (Finset.univ : Finset (Fin t → ZMod p)).filter
      (fun x => ∀ i, p ∣ 1 → thetaMod W A b p i x = 0) = Finset.univ := by
    refine Finset.filter_true_of_mem (fun x _ => ?_)
    exact fun i h => absurd h hp.not_dvd_one
  rw [hfilter, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, ZMod.card]

/-- The local weight of the empty system is `1`. -/
lemma vSys_zero (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (p : ℕ) :
    vSys W A b p 0 = 1 := by
  classical
  by_cases hp : p.Prime
  · rw [vSys, dif_pos hp]
    haveI : NeZero p := NeZero.of_pos hp.pos
    have hX : (0 : PrimeData m).X = ∅ := rfl
    have hX' : (0 : PrimeData m).X' = ∅ := rfl
    rw [hX, hX']
    have hfun : (fun i : Fin m => if i ∈ (∅ : Finset (Fin m)) ∪ ∅ then p else 1) = fun _ => 1 := by
      funext i; simp
    rw [hfun, locCount_one hp, Nat.cast_pow]
    have hp0 : (p : ℂ) ≠ 0 := by
      exact_mod_cast (NeZero.ne p)
    field_simp
  · rw [vSys, dif_neg hp]
    simp

/-- The local weight vanishes at composite moduli. -/
lemma vSys_of_not_prime (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (p : ℕ)
    (σ : PrimeData m) (hp : ¬ p.Prime) (hσ : σ ≠ 0) : vSys W A b p σ = 0 := by
  rw [vSys, dif_neg hp, if_neg hσ]

end BoxAvg
end GYMaj
