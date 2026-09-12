/-
The "make coprime" lemma (paper, Lemma "make_coprime"): through any tangent
pair (a, b) = (v 0, v 1) of a primitive Descartes quadruple v, the crack
family contains a circle whose curvature is coprime to a·b.

Proof outline (paper): it is enough that for every prime p | a·b the crack
quadratic f takes a value not divisible by p.  For an odd prime p the
quadratic cannot vanish identically mod p (else p | a,b,c,d contradicting
primitivity), so one of f(0), f(1), f(2) is nonzero mod p.  The p = 2 case is
handled by the parity structure (two odd and two even coordinates).  A
Chinese-remainder choice of x then makes f(x) coprime to a·b.
-/
import Submission.Apollo.Crack
import Submission.Apollo.PartnerEven
import Mathlib.Tactic
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.Logic.Equiv.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Function
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fin.Basic
set_option autoImplicit false
open scoped Pointwise
open LocalGlobalApollonianCirclePackings

namespace Apollo

/-- crackPoly v is a quadratic polynomial: values are congruent at congruent arguments. -/
lemma crackPoly_factor (v : Fin 4 → ℤ) (x y : ℤ) :
    crackPoly v x - crackPoly v y = (x - y) * ((v 0 + v 1) * (x + y) - (v 0 + v 1 + v 2 - v 3)) := by
  unfold crackPoly
  ring

/-- If x ≡ y (mod m) then f(x) ≡ f(y) (mod m). -/
lemma crackPoly_congr (v : Fin 4 → ℤ) (x y : ℤ) (m : ℕ) :
    (m : ℤ) ∣ x - y → (m : ℤ) ∣ crackPoly v x - crackPoly v y := by
  intro h
  rcases h with ⟨t, ht⟩
  refine ⟨t * ((v 0 + v 1) * (x + y) - (v 0 + v 1 + v 2 - v 3)), ?_⟩
  rw [crackPoly_factor]
  rw [ht]
  ring

/-- all coordinates vanish mod p contradicts primitivity (gcd = 1). -/
lemma coord_zero_of_gcd_one {v : Fin 4 → ℤ} {p : ℕ}
    (hg : Finset.univ.gcd v = 1) (pp : p.Prime)
    (h : ∀ k : Fin 4, (v k : ZMod p) = 0) : False := by
  have hd : ∀ k : Fin 4, (p : ℤ) ∣ v k := by
    intro k
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (v k) p).1 (h k)
  have hg' : (p : ℤ) ∣ Finset.univ.gcd v := by
    rw [Finset.dvd_gcd_iff]
    intro k hk
    exact hd k
  rw [hg] at hg'
  have hp2 : (2 : ℤ) ≤ (p : ℤ) := by exact_mod_cast pp.two_le
  have hle : (p : ℤ) ≤ 1 := Int.le_of_dvd (by norm_num) hg'
  omega

/-- If the crack polynomial vanishes at 0, 1 and 2 mod an odd prime p then all
coordinates vanish mod p. -/
lemma all_zero_of_crack_values {v : Fin 4 → ℤ}
    (hD : (∑ j : Fin 4, v j) ^ 2 = 2 * ∑ j : Fin 4, (v j) ^ 2)
    {p : ℕ} (pp : p.Prime) (hpodd : p ≠ 2)
    (hf0 : (v 2 : ZMod p) = 0) (hf1 : (v 3 : ZMod p) = 0)
    (hf2 : (crackPoly v 2 : ZMod p) = 0) : ∀ k : Fin 4, (v k : ZMod p) = 0 := by
  haveI : Fact p.Prime := ⟨pp⟩
  intro k
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro hz
    have hd : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).1 hz
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq pp Nat.prime_two).1 hd
    exact hpodd this
  have h4ne : (4 : ZMod p) ≠ 0 := by
    have : (4 : ZMod p) = (2 : ZMod p) * (2 : ZMod p) := by norm_num
    rw [this]
    exact mul_ne_zero h2ne h2ne
  have hpoly : (crackPoly v 2 : ZMod p) = 2 * (v 0 + v 1 : ZMod p) - (v 2 : ZMod p) + 2 * (v 3 : ZMod p) := by
    unfold crackPoly
    push_cast
    ring
  have hA : (v 0 + v 1 : ZMod p) = 0 := by
    have hmain : 2 * (v 0 + v 1 : ZMod p) - (v 2 : ZMod p) + 2 * (v 3 : ZMod p) = 0 := by
      rwa [hpoly] at hf2
    rw [hf0, hf1] at hmain
    have hA' : 2 * (v 0 + v 1 : ZMod p) = 0 := by
      simpa using hmain
    exact (mul_eq_zero.mp hA').resolve_left h2ne
  have hDz := congrArg (fun t : ℤ => (t : ZMod p)) hD
  push_cast at hDz
  have hsum1 : (∑ j : Fin 4, (v j : ZMod p)) = v 0 + v 1 := by
    rw [Fin.sum_univ_four]
    simp [hf0, hf1]
  have hsum2 : (∑ j : Fin 4, (v j : ZMod p) ^ 2) = (v 0 : ZMod p) ^ 2 + (v 1 : ZMod p) ^ 2 := by
    rw [Fin.sum_univ_four]
    simp [hf0, hf1]
  have hDz' : (v 0 + v 1 : ZMod p) ^ 2 = 2 * ((v 0 : ZMod p) ^ 2 + (v 1 : ZMod p) ^ 2) := by
    rw [hsum1, hsum2] at hDz
    exact hDz
  have hv1 : (v 1 : ZMod p) = -(v 0 : ZMod p) := by
    exact eq_neg_of_add_eq_zero_left (by simpa [add_comm] using hA)
  have hv0 : (v 0 : ZMod p) = 0 := by
    have hmain : 4 * (v 0 : ZMod p) ^ 2 = 0 := by
      have hD0 : 0 = 2 * ((v 0 : ZMod p) ^ 2 + (v 1 : ZMod p) ^ 2) := by
        rw [hA] at hDz'
        simpa using hDz'.symm
      rw [hv1] at hD0
      have hc : 2 * ((v 0 : ZMod p) ^ 2 + (-(v 0 : ZMod p)) ^ 2) = 4 * (v 0 : ZMod p) ^ 2 := by ring
      rw [hc] at hD0
      exact hD0.symm
    have hv0sq : (v 0 : ZMod p) ^ 2 = 0 := (mul_eq_zero.mp hmain).resolve_left h4ne
    exact sq_eq_zero_iff.mp hv0sq
  have hv1' : (v 1 : ZMod p) = 0 := by
    rw [hv1, hv0]
    simp
  fin_cases k <;> simp [hv0, hv1', hf0, hf1]

/-- for an odd prime p there is a residue r < p with p ∤ f(r). -/
lemma odd_prime_avoid (v : Fin 4 → ℤ)
    (hD : (∑ j : Fin 4, v j) ^ 2 = 2 * ∑ j : Fin 4, (v j) ^ 2)
    (hg : Finset.univ.gcd v = 1)
    {p : ℕ} (pp : p.Prime) (hpodd : p ≠ 2) :
    ∃ r : ℕ, r < p ∧ ¬ (p : ℤ) ∣ crackPoly v (r : ℤ) := by
  by_contra h
  have hall : ∀ r : ℕ, r < p → (p : ℤ) ∣ crackPoly v (r : ℤ) := by
    intro r hr
    by_contra hn
    exact h ⟨r, hr, hn⟩
  have hlt0 : (0 : ℕ) < p := pp.pos
  have hlt1 : (1 : ℕ) < p := by
    have : 2 ≤ p := pp.two_le
    omega
  have hlt2 : (2 : ℕ) < p := by
    have : 2 ≤ p := pp.two_le
    omega
  have hf0 : (p : ℤ) ∣ crackPoly v 0 := hall 0 hlt0
  have hf1 : (p : ℤ) ∣ crackPoly v 1 := hall 1 hlt1
  have hf2 : (p : ℤ) ∣ crackPoly v 2 := hall 2 hlt2
  have hz2 : (v 2 : ZMod p) = 0 := by
    have : (p : ℤ) ∣ v 2 := by simpa using hf0
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (v 2) p).2 this
  have hz3 : (v 3 : ZMod p) = 0 := by
    have : (p : ℤ) ∣ v 3 := by simpa using hf1
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (v 3) p).2 this
  have hz2' : (crackPoly v 2 : ZMod p) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (crackPoly v 2) p).2 hf2
  have hallz := all_zero_of_crack_values (v := v) hD pp hpodd hz2 hz3 hz2'
  exact coord_zero_of_gcd_one hg pp hallz

/-- a prime divisor of an integer divides its absolute value (as a natural). -/
lemma prime_dvd_natAbs {a : ℤ} {p : ℕ} (h : (p : ℤ) ∣ a) : p ∣ a.natAbs :=
  Int.natCast_dvd.mp h  -- (m : ℤ) ∣ n ↔ m ∣ n.natAbs

/-- an integer whose absolute value is even is even. -/
lemma even_of_natAbs_dvd_two {x : ℤ} (h : 2 ∣ x.natAbs) : 2 ∣ x := by
  rcases Int.natAbs_eq x with hx | hx
  · rw [hx]
    exact Int.natCast_dvd_natCast.mpr h
  · rw [hx]
    exact Int.dvd_neg.mpr (Int.natCast_dvd_natCast.mpr h)

/-- if 2 ∤ f(t) for t = 0 or 1 and x ≡ t (mod 2), then 2 ∤ f(x). -/
lemma crack_odd_at_parity (v : Fin 4 → ℤ) (x : ℤ) (t : ℕ) (ht : t = 0 ∨ t = 1)
    (hx : (x : ZMod 2) = ((t : ℕ) : ZMod 2)) (hf : ¬ 2 ∣ crackPoly v (t : ℤ)) : ¬ 2 ∣ crackPoly v x := by
  rcases ht with rfl | rfl
  · have h2x : (2 : ℤ) ∣ x := (ZMod.intCast_zmod_eq_zero_iff_dvd x 2).1 (by simpa using hx)
    intro h2fx
    have hc := crackPoly_congr v x 0 2 (by simpa using h2x)
    have : (2 : ℤ) ∣ crackPoly v 0 := by
      have hsub : (2 : ℤ) ∣ crackPoly v x - (crackPoly v x - crackPoly v 0) := by
        simpa using (Int.dvd_sub h2fx hc)
      simpa using hsub
    exact hf (by simpa using this)
  · have hz : ((x - 1 : ℤ) : ZMod 2) = 0 := by
      have hsub : ((x - 1 : ℤ) : ZMod 2) = (x : ZMod 2) - (1 : ZMod 2) := by simp
      rw [hsub, hx]
      norm_num
    have h2x : (2 : ℤ) ∣ x - 1 := (ZMod.intCast_zmod_eq_zero_iff_dvd (x - 1) 2).1 hz
    intro h2fx
    have hc := crackPoly_congr v x 1 2 h2x
    have : (2 : ℤ) ∣ crackPoly v 1 := by
      have hsub : (2 : ℤ) ∣ crackPoly v x - (crackPoly v x - crackPoly v 1) := by
        simpa using (Int.dvd_sub h2fx hc)
      simpa using hsub
    exact hf (by simpa using this)

/-- Main "make coprime" lemma: some crack value is coprime to a·b. -/
theorem make_coprime (v : Fin 4 → ℤ)
    (hD : (∑ j : Fin 4, v j) ^ 2 = 2 * ∑ j : Fin 4, (v j) ^ 2)
    (hg : Finset.univ.gcd v = 1) (hz : v 0 * v 1 ≠ 0)
    (hpar : 2 ∣ v 0 * v 1 → ¬ 2 ∣ v 2 ∨ ¬ 2 ∣ v 3) :
    ∃ x : ℕ, (crackPoly v (x : ℤ)).gcd (v 0 * v 1) = 1 := by
  classical
  let n : ℕ := (v 0 * v 1).natAbs
  have hn0 : n ≠ 0 := by
    intro hn
    apply hz
    exact Int.natAbs_eq_zero.mp hn
  -- odd prime divisors of n
  let s : Finset ℕ := (Finset.range (n + 1)).filter (fun p => p.Prime ∧ p ∣ n ∧ p ≠ 2)
  have s_prop : ∀ p : ℕ, p ∈ s → p.Prime ∧ p ∣ n ∧ p ≠ 2 := by
    intro p hps
    exact (Finset.mem_filter.mp hps).2
  -- the chosen residue avoiding p
  let resA : ℕ → ℕ := fun p =>
    if hps : p ∈ s then
      Classical.choose (odd_prime_avoid v hD hg (s_prop p hps).1 (s_prop p hps).2.2)
    else 0
  have res_prop : ∀ p : ℕ, p ∈ s → ¬ (p : ℤ) ∣ crackPoly v (resA p : ℤ) := by
    intro p hps
    dsimp [resA]
    rw [dif_pos hps]
    exact (Classical.choose_spec (odd_prime_avoid v hD hg (s_prop p hps).1 (s_prop p hps).2.2)).2
  have hs : ∀ p : ℕ, p ∈ s → p ≠ 0 := by
    intro p hps
    exact (s_prop p hps).1.ne_zero
  have hpair : (↑s : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun p : ℕ => p)) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (s_prop p hp).1 (s_prop q hq).1).2 hpq
  have hcrt := Nat.chineseRemainderOfFinset resA (fun p : ℕ => p) s hs hpair
  let k : ℕ := hcrt.1
  have hk : ∀ p : ℕ, p ∈ s → k ≡ resA p [MOD p] := by
    intro p hps
    exact hcrt.2 p hps
  let M : ℕ := s.prod (fun p => p)
  have hM1 : M % 2 = 1 := by
    have hodd : ∀ p : ℕ, p ∈ s → Odd p := by
      intro p hps
      have hpp : p.Prime := (s_prop p hps).1
      have hpodd : p ≠ 2 := (s_prop p hps).2.2
      exact (Nat.not_even_iff_odd).1 (by
        intro he
        have h2p : 2 ∣ p := even_iff_two_dvd.mp he
        have : p = 2 := ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).1 h2p).symm
        exact hpodd this)
    have hModd : Odd M := by
      dsimp [M]
      exact Finset.prod_induction (fun p : ℕ => p) (fun m : ℕ => Odd m)
        (fun a b ha hb => ha.mul hb)
        (by exact (Nat.not_even_iff_odd).1 (by norm_num))
        hodd
    exact Nat.odd_iff.mp hModd
  -- parity target t0 (only matters when 2 | n)
  let t0 : ℕ := if ¬ 2 ∣ v 2 then 0 else 1
  have hft0 : 2 ∣ v 0 * v 1 → ¬ 2 ∣ crackPoly v (t0 : ℤ) := by
    intro h2
    by_cases hv2c : 2 ∣ v 2
    · -- t0 = 1: 2 ∤ f(1) = v3 (from hpar, since v2 is even)
      have ht0 : t0 = 1 := by
        dsimp [t0]
        by_cases h : ¬ 2 ∣ v 2
        · exact False.elim (h hv2c)
        · simp [h]
      have hv3 : ¬ 2 ∣ v 3 := by
        rcases hpar h2 with h02 | h03
        · exact False.elim (h02 hv2c)
        · exact h03
      rw [ht0]
      simpa using hv3
    · -- t0 = 0: 2 ∤ f(0) = v2
      have ht0 : t0 = 0 := by
        dsimp [t0]
        simp [hv2c]
      rw [ht0]
      simpa using hv2c
  -- assemble x
  let x : ℕ := if 2 ∣ n then (if k % 2 = t0 then k else k + M) else k
  have hxcase : x = k ∨ x = k + M := by
    dsimp [x]
    by_cases h2n : 2 ∣ n
    · by_cases hkm : k % 2 = t0 <;> simp [h2n, hkm]
    · simp [h2n]
  have hparity : 2 ∣ n → ((x : ℕ) : ZMod 2) = ((t0 : ℕ) : ZMod 2) := by
    intro h2n
    have hk2 : k % 2 = 0 ∨ k % 2 = 1 := by omega
    have ht0lt : t0 < 2 := by dsimp [t0]; by_cases h : ¬ 2 ∣ v 2 <;> simp [h]
    dsimp [x]
    simp [h2n]
    by_cases hke : k % 2 = t0
    · -- x = k
      simp [hke]
      rw [ZMod.natCast_eq_natCast_iff]
      change k % 2 = t0 % 2
      rw [Nat.mod_eq_of_lt ht0lt]
      exact hke
    · -- x = k + M
      simp [hke]
      rw [← Nat.cast_add]
      rw [ZMod.natCast_eq_natCast_iff]
      change (k + M) % 2 = t0 % 2
      have hsum : (k + M) % 2 = (k % 2 + 1) % 2 := by
        rw [Nat.add_mod, hM1]
      rw [hsum]
      have hres : (k % 2 + 1) % 2 = t0 % 2 := by omega
      exact hres
  have hxodd : 2 ∣ n → ¬ 2 ∣ crackPoly v (x : ℤ) := by
    intro h2n
    have ht0 : 2 ∣ v 0 * v 1 := Int.natCast_dvd.mpr (by simpa [n] using h2n)
    exact crack_odd_at_parity v (x : ℤ) t0 (by dsimp [t0]; by_cases h : ¬ 2 ∣ v 2 <;> simp [h]) (by simpa using hparity h2n) (hft0 ht0)
  -- odd primes never divide f(x):
  have hxoddprime : ∀ p : ℕ, p ∈ s → ¬ (p : ℤ) ∣ crackPoly v (x : ℤ) := by
    intro p hps
    have hpM : p ∣ M := by
      dsimp [M]
      exact Finset.dvd_prod_of_mem (fun p : ℕ => p) hps
    have hkx : (p : ℤ) ∣ (x : ℤ) - (k : ℤ) := by
      rcases hxcase with hxk | hxk
      · rw [hxk]
        norm_num
      · have : ((k + M : ℕ) : ℤ) - (k : ℤ) = (M : ℤ) := by omega
        rw [hxk, this]
        exact Int.natCast_dvd_natCast.mpr hpM
    have hcong := crackPoly_congr v (x : ℤ) (k : ℤ) p hkx
    have hkres : (p : ℤ) ∣ (k : ℤ) - (resA p : ℤ) := by
      have hkz : ((k : ℤ) : ZMod p) = (((resA p : ℕ) : ℤ) : ZMod p) := by
        have hn : (k : ZMod p) = (resA p : ZMod p) := by
          rw [ZMod.natCast_eq_natCast_iff]
          exact hk p hps
        simpa using hn
      have hmod : (k : ℤ) ≡ ((resA p : ℕ) : ℤ) [ZMOD (p : ℤ)] := by
        exact (ZMod.intCast_eq_intCast_iff (k : ℤ) ((resA p : ℕ) : ℤ) p).mp hkz
      rw [Int.modEq_iff_dvd] at hmod
      -- hmod : p | (resA p) - k  ;  negate and reorder
      simpa [neg_sub] using (Int.dvd_neg.mpr hmod)
    have hkong := crackPoly_congr v (k : ℤ) (resA p : ℤ) p hkres
    intro hpfx
    have h1 : (p : ℤ) ∣ crackPoly v (k : ℤ) := by
      have hsub : (p : ℤ) ∣ crackPoly v (x : ℤ) - (crackPoly v (x : ℤ) - crackPoly v (k : ℤ)) := by
        simpa using (Int.dvd_sub hpfx hcong)
      simpa using hsub
    have h2 : (p : ℤ) ∣ crackPoly v (resA p : ℤ) := by
      have hsub : (p : ℤ) ∣ crackPoly v (k : ℤ) - (crackPoly v (k : ℤ) - crackPoly v (resA p : ℤ)) := by
        simpa using (Int.dvd_sub h1 hkong)
      simpa using hsub
    exact res_prop p hps h2
  -- assemble: gcd = 1
  refine ⟨x, ?_⟩
  rw [Int.gcd_eq_natAbs]
  rw [Int.natAbs_mul]
  by_contra hne
  rcases Nat.exists_prime_and_dvd hne with ⟨p, pp, hpg⟩
  have hpm : p ∣ (crackPoly v (x : ℤ)).natAbs := dvd_trans hpg (Nat.gcd_dvd_left (crackPoly v (x : ℤ)).natAbs ((v 0).natAbs * (v 1).natAbs))
  have hpn : p ∣ (v 0).natAbs * (v 1).natAbs := dvd_trans hpg (Nat.gcd_dvd_right (crackPoly v (x : ℤ)).natAbs ((v 0).natAbs * (v 1).natAbs))
  have hpn' : p ∣ (v 0 * v 1).natAbs := by simpa [Int.natAbs_mul] using hpn
  have hpfx : (p : ℤ) ∣ crackPoly v (x : ℤ) := Int.natCast_dvd.mpr hpm
  by_cases hp2 : p = 2
  · subst p
    exact hxodd (by simpa [n] using hpn') (even_of_natAbs_dvd_two hpm)
  · have hps : p ∈ s := by
      dsimp [s]
      rw [Finset.mem_filter]
      have hle : p ≤ (v 0 * v 1).natAbs := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hpn'
      have hmem : p ∈ Finset.range ((v 0 * v 1).natAbs + 1) := by
        have hlt : p < (v 0 * v 1).natAbs + 1 := Nat.lt_succ_of_le hle
        simpa using hlt
      exact ⟨hmem, pp, hpn', hp2⟩
    exact hxoddprime p hps hpfx
