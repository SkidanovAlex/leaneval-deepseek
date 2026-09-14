import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

open Polynomial
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Commons.NumberTheory.Padics

/-! # One-step Hensel lifting of a coprime monic factorization

Helper development for `hensel_lift_step` : lifting a monic factorization
`α * β = f (mod p^m)` to `(mod p^(m+1))`.  All helper declarations live in the
sub-namespace `HenselStep` to avoid name clashes with other files. -/

namespace HenselStep

variable {p : ℕ} [Fact p.Prime]

-- =====================================================================
-- 1. basic maps between the finite levels `ZMod (p^k)`
-- =====================================================================

/-- cast down `ZMod (p^(k+1)) →+* ZMod (p^k)` -/
def castDown (k : ℕ) : ZMod (p ^ (k+1)) →+* ZMod (p ^ k) :=
  ZMod.castHom (pow_dvd_pow p (by omega : k ≤ k+1)) (ZMod (p ^ k))

/-- reduction modulo `p` from level `k+1` -/
def redSucc (k : ℕ) : ZMod (p ^ (k+1)) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p (by omega : k+1 ≠ 0)) (ZMod p)

/-- reduction modulo `p` from level `k` (needs `k ≠ 0`) -/
def red (k : ℕ) (hk : k ≠ 0) : ZMod (p ^ k) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p hk) (ZMod p)

lemma redSucc_val (k : ℕ) (x : ZMod (p ^ (k+1))) :
    (redSucc k x).val = x.val % p := by
  change (ZMod.castHom (dvd_pow_self p (by omega : k+1 ≠ 0)) (ZMod p) x).val = x.val % p
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

lemma castDown_val (k : ℕ) (x : ZMod (p ^ (k+1))) :
    (castDown k x).val = x.val % p ^ k := by
  change (ZMod.castHom (pow_dvd_pow p (by omega : k ≤ k+1)) (ZMod (p ^ k)) x).val = x.val % p ^ k
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

/-- reduction at level `k+1` factors through the cast-down to level `k` -/
lemma redSucc_eq_red_comp_castDown (k : ℕ) (hk : 1 ≤ k) (x : ZMod (p ^ (k+1))) :
    redSucc k x = red k (by omega : k ≠ 0) (castDown k x) := by
  apply ZMod.val_injective p
  have hp : p ∣ p ^ k := dvd_pow_self p (by omega : k ≠ 0)
  have hR : (red k (by omega : k ≠ 0) (castDown k x)).val = x.val % p := by
    calc
      (red k (by omega : k ≠ 0) (castDown k x)).val
          = ((castDown k x).cast : ZMod p).val := by simp [red]
      _ = ((((castDown k x).val : ℕ)) : ZMod p).val := by rw [ZMod.cast_eq_val]
      _ = (castDown k x).val % p := by rw [ZMod.val_natCast]
      _ = (x.val % p ^ k) % p := by rw [castDown_val]
      _ = x.val % p := by rw [Nat.mod_mod_of_dvd x.val hp]
  calc
    (redSucc k x).val = x.val % p := redSucc_val k x
    _ = (red k (by omega : k ≠ 0) (castDown k x)).val := hR.symm

/-- casting the canonical lift of `c.val` down to level `k` recovers `c` -/
lemma castDown_lift (k : ℕ) (c : ZMod (p ^ k)) :
    castDown k ((c.val : ℕ) : ZMod (p ^ (k+1))) = c := by
  rw [castDown]
  rw [map_natCast]
  exact ZMod.natCast_zmod_val c

/-- reducing the canonical lift of `c.val` (for `c : ZMod p`) modulo `p` recovers `c` -/
lemma redSucc_lift_modp (k : ℕ) (c : ZMod p) :
    redSucc k ((c.val : ℕ) : ZMod (p ^ (k+1))) = c := by
  rw [redSucc]
  rw [map_natCast]
  exact ZMod.natCast_zmod_val c

/-- reducing the canonical lift of a natural number modulo `p` -/
lemma redSucc_natCast (k : ℕ) (n : ℕ) :
    redSucc k ((n : ℕ) : ZMod (p ^ (k+1))) = (n : ZMod p) := by
  rw [redSucc]
  rw [map_natCast]

/-- casting a natural number down to level `k` -/
lemma castDown_natCast (k : ℕ) (n : ℕ) :
    castDown k ((n : ℕ) : ZMod (p ^ (k+1))) = (n : ZMod (p ^ k)) := by
  rw [castDown]
  rw [map_natCast]

/-- `p^k` is sent to zero when cast down to level `k` -/
lemma castDown_pow_eq_zero (k : ℕ) :
    castDown k (((p ^ k : ℕ) : ZMod (p ^ (k+1)))) = 0 := by
  change (ZMod.castHom (pow_dvd_pow p (by omega : k ≤ k+1)) (ZMod (p ^ k)))
      (((p ^ k : ℕ) : ZMod (p ^ (k+1)))) = 0
  rw [map_natCast]
  exact (ZMod.natCast_eq_zero_iff (p ^ k) (p ^ k)).mpr dvd_rfl

/-- `p^k` reduces to zero modulo `p` when `1 ≤ k` -/
lemma redSucc_pow_eq_zero (k : ℕ) (hk : 1 ≤ k) :
    redSucc k (((p ^ k : ℕ) : ZMod (p ^ (k+1)))) = 0 := by
  change (ZMod.castHom (dvd_pow_self p (by omega : k+1 ≠ 0)) (ZMod p))
      (((p ^ k : ℕ) : ZMod (p ^ (k+1)))) = 0
  rw [map_natCast]
  exact (ZMod.natCast_eq_zero_iff (p ^ k) p).mpr (dvd_pow_self p (by omega : k ≠ 0))

/-- `x` maps to zero under the cast-down to level `k` iff `p^k ∣ x.val` -/
lemma castDown_eq_zero_iff_dvd_val (k : ℕ) (x : ZMod (p ^ (k+1))) :
    castDown k x = 0 ↔ p ^ k ∣ x.val := by
  constructor
  · intro h
    change (ZMod.castHom (pow_dvd_pow p (by omega : k ≤ k+1)) (ZMod (p ^ k))) x = 0 at h
    rw [ZMod.castHom_apply] at h
    rw [ZMod.cast_eq_val] at h
    exact (ZMod.natCast_eq_zero_iff x.val (p ^ k)).mp h
  · intro hd
    change (ZMod.castHom (pow_dvd_pow p (by omega : k ≤ k+1)) (ZMod (p ^ k))) x = 0
    rw [ZMod.castHom_apply]
    rw [ZMod.cast_eq_val]
    exact (ZMod.natCast_eq_zero_iff x.val (p ^ k)).mpr hd

/-- decomposition of an element divisible by `p^k` -/
lemma eq_pow_mul_div_val (k : ℕ) (x : ZMod (p ^ (k+1))) (hx : p ^ k ∣ x.val) :
    x = ((p ^ k : ℕ) : ZMod (p ^ (k+1))) * ((x.val / p ^ k : ℕ) : ZMod (p ^ (k+1))) := by
  calc
    x = ((x.val : ℕ) : ZMod (p ^ (k+1))) := (ZMod.natCast_zmod_val x).symm
    _ = (((p ^ k) * (x.val / p ^ k) : ℕ) : ZMod (p ^ (k+1))) := by
      congr 1
      rw [Nat.mul_comm, Nat.div_mul_cancel hx]
    _ = ((p ^ k : ℕ) : ZMod (p ^ (k+1))) * ((x.val / p ^ k : ℕ) : ZMod (p ^ (k+1))) := by
      rw [Nat.cast_mul]

/-- multiplying by `p^k` kills anything whose reduction mod `p` is zero -/
lemma pow_mul_eq_zero_of_redSucc_eq_zero (k : ℕ) (x : ZMod (p ^ (k+1)))
    (hx : redSucc k x = 0) :
    ((p ^ k : ℕ) : ZMod (p ^ (k+1))) * x = 0 := by
  have hz : p ∣ x.val := by
    change (ZMod.castHom (dvd_pow_self p (by omega : k+1 ≠ 0)) (ZMod p)) x = 0 at hx
    rw [ZMod.castHom_apply] at hx
    rw [ZMod.cast_eq_val] at hx
    exact (ZMod.natCast_eq_zero_iff x.val p).mp hx
  have hx' : x = (p : ZMod (p ^ (k+1))) * ((x.val / p : ℕ) : ZMod (p ^ (k+1))) := by
    calc
      x = ((x.val : ℕ) : ZMod (p ^ (k+1))) := (ZMod.natCast_zmod_val x).symm
      _ = ((p * (x.val / p) : ℕ) : ZMod (p ^ (k+1))) := by
        congr 1
        rw [Nat.mul_comm, Nat.div_mul_cancel hz]
      _ = (p : ZMod (p ^ (k+1))) * ((x.val / p : ℕ) : ZMod (p ^ (k+1))) := by
        rw [Nat.cast_mul]
  rw [hx', ← mul_assoc]
  have hpown : (((p ^ k : ℕ) : ZMod (p ^ (k+1))) * (p : ZMod (p ^ (k+1)))) = 0 := by
    calc
      (((p ^ k : ℕ) : ZMod (p ^ (k+1))) * (p : ZMod (p ^ (k+1))))
          = ((p ^ k * p : ℕ) : ZMod (p ^ (k+1))) := by rw [Nat.cast_mul]
      _ = ((p ^ (k+1) : ℕ) : ZMod (p ^ (k+1))) := by rw [pow_succ]
      _ = 0 := ZMod.natCast_self (p ^ (k+1))
  rw [hpown]
  simp

/-- `p^(2k) = 0` in `ZMod (p^(k+1))` as soon as `1 ≤ k` -/
lemma pow_two_mul_eq_zero (k : ℕ) (hk : 1 ≤ k) :
    ((p ^ k : ℕ) : ZMod (p ^ (k+1))) ^ 2 = 0 := by
  rw [pow_two, ← Nat.cast_mul]
  rw [ZMod.natCast_eq_zero_iff]
  rw [← pow_add]
  exact pow_dvd_pow p (by omega : k + 1 ≤ k + k)

/-- `1 < p^k` for prime `p` and `1 ≤ k` -/
lemma one_lt_pow_prime (k : ℕ) (hk : 1 ≤ k) : 1 < p ^ k := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  exact Nat.one_lt_pow (by omega : k ≠ 0) hp1

-- =====================================================================
-- 2. polynomials defined by finitely many coefficients
-- =====================================================================

/-- `coeff` distributes over `Finset.sum` -/
lemma coeff_finset_sum {ι R : Type*} [Semiring R] (s : Finset ι) (f : ι → R[X]) (n : ℕ) :
    (∑ i ∈ s, f i).coeff n = ∑ i ∈ s, (f i).coeff n := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s has ih
    rw [Finset.sum_insert has, Polynomial.coeff_add, ih, Finset.sum_insert has]

/-- the polynomial over `ZMod N` with `coeff j = F j` for `j < D`, zero otherwise -/
noncomputable def coeffPoly (N : ℕ) (F : ℕ → ZMod N) (D : ℕ) : (ZMod N)[X] :=
  ∑ i ∈ Finset.range D, Polynomial.monomial i (F i)

lemma coeffPoly_coeff (N : ℕ) (F : ℕ → ZMod N) (D j : ℕ) :
    (coeffPoly N F D).coeff j = if j < D then F j else 0 := by
  classical
  by_cases hj : j < D
  · have hmem : j ∈ Finset.range D := Finset.mem_range.mpr hj
    calc
      (coeffPoly N F D).coeff j = ∑ i ∈ Finset.range D, ((monomial i) (F i)).coeff j := by
        rw [coeffPoly, coeff_finset_sum]
      _ = ∑ i ∈ Finset.range D, (if i = j then F i else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [coeff_monomial]
      _ = F j := by
        rw [Finset.sum_eq_single j]
        · simp
        · intro b hb hbj
          simp [hbj]
        · intro hnot
          exact False.elim (hnot hmem)
      _ = if j < D then F j else 0 := by rw [if_pos hj]
  · have hnj : j ∉ Finset.range D := by
      intro hj'
      exact hj (Finset.mem_range.mp hj')
    calc
      (coeffPoly N F D).coeff j = ∑ i ∈ Finset.range D, ((monomial i) (F i)).coeff j := by
        rw [coeffPoly, coeff_finset_sum]
      _ = ∑ i ∈ Finset.range D, (if i = j then F i else 0) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [coeff_monomial]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have hij : i ≠ j := by
          intro hij
          subst hij
          exact hnj hi
        simp [hij]
      _ = if j < D then F j else 0 := by rw [if_neg hj]

/-- lift each coefficient of `g : (ZMod n)[X]` (up to `natDegree`) into `ZMod N` -/
noncomputable def coeffLift (N : ℕ) {n : ℕ} (g : (ZMod n)[X]) : (ZMod N)[X] :=
  coeffPoly N (fun i => (((g.coeff i).val : ℕ) : ZMod N)) (g.natDegree + 1)

lemma coeffLift_coeff (N : ℕ) {n : ℕ} (g : (ZMod n)[X]) (j : ℕ) :
    (coeffLift N g).coeff j = if j ≤ g.natDegree then ((((g.coeff j).val : ℕ) : ZMod N)) else 0 := by
  rw [coeffLift, coeffPoly_coeff]
  simp only [Nat.lt_succ_iff]

lemma coeffLift_coeff_zero_of_lt (N : ℕ) {n : ℕ} (g : (ZMod n)[X]) {j : ℕ}
    (hj : g.natDegree < j) :
    (coeffLift N g).coeff j = 0 := by
  rw [coeffLift_coeff]
  have : ¬ j ≤ g.natDegree := by omega
  rw [if_neg this]

/-- the top coefficient of the lift is the lift of the leading coefficient -/
lemma coeffLift_coeff_leadingCoeff (N : ℕ) {n : ℕ} (g : (ZMod n)[X]) :
    (coeffLift N g).coeff g.natDegree = ((((g.leadingCoeff).val : ℕ) : ZMod N)) := by
  rw [coeffLift_coeff]
  simp

/-- a monic `g` lifts to a monic polynomial of the same degree -/
lemma coeffLift_monic_natDegree {n N : ℕ} {g : (ZMod n)[X]} (hg : g.Monic)
    (h1 : ((((1 : ZMod n).val : ℕ) : ZMod N)) = 1) (hN : (1 : ZMod N) ≠ 0) :
    (coeffLift N g).Monic ∧ (coeffLift N g).natDegree = g.natDegree := by
  have hc : (coeffLift N g).coeff g.natDegree = 1 := by
    rw [coeffLift_coeff_leadingCoeff, hg.leadingCoeff]
    exact h1
  have hnd : (coeffLift N g).natDegree = g.natDegree := by
    refine le_antisymm ?_ ?_
    · rw [natDegree_le_iff_coeff_eq_zero]
      intro j hj
      exact coeffLift_coeff_zero_of_lt N g hj
    · exact le_natDegree_of_ne_zero (by simpa [hc] using hN)
  constructor
  · rw [Monic, Polynomial.leadingCoeff, hnd]
    exact hc
  · exact hnd

/-- lifting from level `k` and casting down to level `k` recovers the polynomial -/
lemma map_castDown_coeffLift (k : ℕ) (g : (ZMod (p ^ k))[X]) :
    Polynomial.map (castDown k) (coeffLift (p ^ (k+1)) g) = g := by
  ext j
  rw [Polynomial.coeff_map]
  by_cases hj : j ≤ g.natDegree
  · rw [coeffLift_coeff, if_pos hj]
    exact castDown_lift k (g.coeff j)
  · rw [coeffLift_coeff, if_neg hj]
    have hlt : g.natDegree < j := by omega
    rw [coeff_eq_zero_of_natDegree_lt hlt]
    simp

/-- lifting a `ZMod p` polynomial and reducing modulo `p` recovers the polynomial -/
lemma map_redSucc_coeffLift (k : ℕ) (g : (ZMod p)[X]) :
    Polynomial.map (redSucc k) (coeffLift (p ^ (k+1)) g) = g := by
  ext j
  rw [Polynomial.coeff_map]
  by_cases hj : j ≤ g.natDegree
  · rw [coeffLift_coeff, if_pos hj]
    exact redSucc_lift_modp k (g.coeff j)
  · rw [coeffLift_coeff, if_neg hj]
    have hlt : g.natDegree < j := by omega
    rw [coeff_eq_zero_of_natDegree_lt hlt]
    simp

/-- the degree of the lift of `g` is bounded by the degree of `g` -/
lemma coeffLift_degree_le (N : ℕ) {n : ℕ} (g : (ZMod n)[X]) :
    (coeffLift N g).degree ≤ (g.natDegree : WithBot ℕ) := by
  exact (Polynomial.degree_le_iff_coeff_zero (coeffLift N g) (g.natDegree : WithBot ℕ)).mpr
    (by intro m hm; exact coeffLift_coeff_zero_of_lt N g (WithBot.coe_lt_coe.mp hm))

/-- `1.val = 1` at prime-power levels -/
lemma one_val_cast_eq_one (k : ℕ) (hk : 1 ≤ k) :
    ((((1 : ZMod (p ^ k)).val : ℕ) : ZMod (p ^ (k+1)))) = 1 := by
  have h : (1 : ZMod (p ^ k)) = ((1 : ℕ) : ZMod (p ^ k)) := by norm_num
  rw [h, ZMod.val_natCast, Nat.mod_eq_of_lt (one_lt_pow_prime k hk)]
  norm_num

/-- `1 ≠ 0` in `ZMod (p^k)` when `1 ≤ k` -/
lemma one_ne_zero_zmod_pow (k : ℕ) (hk : 1 ≤ k) : (1 : ZMod (p ^ k)) ≠ 0 := by
  intro h1
  have h : ((1 : ℕ) : ZMod (p ^ k)) = 0 := by simpa using h1
  have hdvd : p ^ k ∣ 1 := (ZMod.natCast_eq_zero_iff 1 (p ^ k)).mp h
  have hdiv : p ^ k = 1 := Nat.dvd_one.mp hdvd
  have hpgt : 1 < p ^ k := one_lt_pow_prime k hk
  exact (ne_of_gt hpgt) hdiv

/-- lift of a monic level-`k` polynomial: monic of the same degree -/
lemma coeffLift_monic_natDegree_prime (k : ℕ) (hk : 1 ≤ k) {g : (ZMod (p ^ k))[X]}
    (hg : g.Monic) :
    (coeffLift (p ^ (k+1)) g).Monic ∧ (coeffLift (p ^ (k+1)) g).natDegree = g.natDegree := by
  refine coeffLift_monic_natDegree hg (one_val_cast_eq_one k hk) ?_
  exact one_ne_zero_zmod_pow (k+1) (by omega)


-- =====================================================================
-- 3. degree-bounded Bézout decomposition over a field
-- =====================================================================

/-- Over a field, if `a b` are monic coprime polynomials and `e` has degree
bounded by `deg a + deg b`, then `e = u * b + v * a` for some `u v` whose
coefficients vanish above `deg a` and `deg b` respectively. -/
lemma bezout_decomp {K : Type*} [Field K] {a b : K[X]}
    (ha : a.Monic) (hb : b.Monic) (hcop : IsCoprime a b) {e : K[X]}
    (he : e.degree < (a.natDegree + b.natDegree : WithBot ℕ)) :
    ∃ u v : K[X],
      (∀ i, a.natDegree ≤ i → u.coeff i = 0) ∧
      (∀ i, b.natDegree ≤ i → v.coeff i = 0) ∧ e = u * b + v * a := by
  classical
  by_cases he0 : e = 0
  · subst e; refine ⟨0, 0, ?_, ?_, ?_⟩ <;> simp
  · have he' : e.natDegree < a.natDegree + b.natDegree := by
      have hdeg : e.degree = (e.natDegree : WithBot ℕ) := degree_eq_natDegree he0
      rw [hdeg] at he
      exact WithBot.coe_lt_coe.mp he
    obtain ⟨s, t, hst⟩ := hcop  -- hst : s * a + t * b = 1
    let q : K[X] := (s * e) /ₘ b
    let v : K[X] := (s * e) %ₘ b
    let u : K[X] := a * q + t * e
    have hv : v = s * e - q * b := by
      dsimp [v, q]
      rw [modByMonic_eq_sub_mul_div]
      ring
    have hmain : e = u * b + v * a := by
      calc
        e = (a * q + t * e) * b + (s * e - q * b) * a := by
          calc
            e = e * (s * a + t * b) := by rw [hst]; ring
            _ = (a * q + t * e) * b + (s * e - q * b) * a := by ring
        _ = u * b + v * a := by
          dsimp [u]
          rw [hv]
    have hv_lt : v.natDegree < b.natDegree ∨ v = 0 := by
      by_cases hv0 : v = 0
      · exact Or.inr hv0
      · have hb1 : b ≠ 1 := by
          intro hb1
          apply hv0
          subst b
          simp [v]
        exact Or.inl (natDegree_modByMonic_lt (s * e) hb hb1)
    have hu_lt : u.natDegree < a.natDegree ∨ u = 0 := by
      by_cases hu0 : u = 0
      · exact Or.inr hu0
      · have h_eq : u * b = e - v * a := by
          rw [hmain]
          ring
        have hdeg_e : e.natDegree < a.natDegree + b.natDegree := he'
        have hdeg_va : (v * a).natDegree < a.natDegree + b.natDegree := by
          by_cases hv0 : v = 0
          · simp [hv0]
            omega
          · have hvd : v.natDegree < b.natDegree := hv_lt.resolve_right hv0
            rw [natDegree_mul hv0 ha.ne_zero]
            omega
        have hdeg : (e - v * a).natDegree < a.natDegree + b.natDegree := by
          have h1 : (e - v * a).natDegree ≤ max e.natDegree (v * a).natDegree := by
            simpa [sub_eq_add_neg] using natDegree_add_le e (-(v * a))
          exact lt_of_le_of_lt h1 (max_lt hdeg_e hdeg_va)
        have hdeg_ub : (u * b).natDegree < a.natDegree + b.natDegree := by
          rw [h_eq]
          exact hdeg
        have hdeg_u : u.natDegree < a.natDegree := by
          rw [natDegree_mul hu0 hb.ne_zero] at hdeg_ub
          omega
        exact Or.inl hdeg_u
    refine ⟨u, v, ?_, ?_, hmain⟩
    · intro i hi
      rcases hu_lt with hu_lt | hu0
      · exact coeff_eq_zero_of_natDegree_lt (p := u) (by omega)
      · simp [hu0]
    · intro i hi
      rcases hv_lt with hv_lt | hv0
      · exact coeff_eq_zero_of_natDegree_lt (p := v) (by omega)
      · simp [hv0]

end HenselStep

open HenselStep

-- =====================================================================
-- 4. the one-step Hensel lifting theorem
-- =====================================================================

theorem hensel_lift_step {p : ℕ} [Fact p.Prime] {m : ℕ} (hm : 1 ≤ m) {f : (PadicInt p)[X]}
    (hf : f.Monic) {a : (ZMod p)[X]} (ha : a.Monic) {b : (ZMod p)[X]} (hb : b.Monic)
    (hcop : IsCoprime a b) {α β : (ZMod (p ^ m))[X]}
    (hmonα : α.Monic) (hmonβ : β.Monic)
    (hdegα : α.natDegree = a.natDegree) (hdegβ : β.natDegree = b.natDegree)
    (hfac : α * β = Polynomial.map (PadicInt.toZModPow m) f)
    (hredα : Polynomial.map (ZMod.castHom (dvd_pow_self p (by omega : m ≠ 0)) (ZMod p)) α = a)
    (hredβ : Polynomial.map (ZMod.castHom (dvd_pow_self p (by omega : m ≠ 0)) (ZMod p)) β = b) :
    ∃ α' β' : (ZMod (p ^ (m+1)))[X],
      α'.Monic ∧ β'.Monic ∧ α'.natDegree = a.natDegree ∧ β'.natDegree = b.natDegree ∧
      α' * β' = Polynomial.map (PadicInt.toZModPow (m+1)) f ∧
      Polynomial.map (ZMod.castHom (pow_dvd_pow p (by omega : m ≤ m+1)) (ZMod (p ^ m))) α' = α ∧
      Polynomial.map (ZMod.castHom (pow_dvd_pow p (by omega : m ≤ m+1)) (ZMod (p ^ m))) β' = β ∧
      Polynomial.map (ZMod.castHom (dvd_pow_self p (by omega : m + 1 ≠ 0)) (ZMod p)) α' = a ∧
      Polynomial.map (ZMod.castHom (dvd_pow_self p (by omega : m + 1 ≠ 0)) (ZMod p)) β' = b := by
  classical
  -- ===== basic setup =====
  have hm0 : m ≠ 0 := by omega
  haveI factm : Fact (1 < p ^ m) := ⟨one_lt_pow_prime m hm⟩
  haveI factm1 : Fact (1 < p ^ (m + 1)) := ⟨one_lt_pow_prime (m + 1) (by omega)⟩
  let d1 : ℕ := a.natDegree
  let d2 : ℕ := b.natDegree
  let D : ℕ := d1 + d2
  let π : ZMod (p ^ (m + 1)) →+* ZMod (p ^ m) := castDown m
  let ρ : ZMod (p ^ (m + 1)) →+* ZMod p := redSucc m
  let ρm : ZMod (p ^ m) →+* ZMod p := red m hm0
  let c : ZMod (p ^ (m + 1)) := ((p ^ m : ℕ) : ZMod (p ^ (m + 1)))
  let A : (ZMod (p ^ (m + 1)))[X] := coeffLift (p ^ (m + 1)) α
  let B : (ZMod (p ^ (m + 1)))[X] := coeffLift (p ^ (m + 1)) β
  let fS : (ZMod (p ^ (m + 1)))[X] := Polynomial.map (PadicInt.toZModPow (m + 1)) f
  -- degree of the reduction of `f` at level `m+1`
  have hfac' : Polynomial.map (PadicInt.toZModPow m) f = α * β := hfac.symm
  have hαβdeg : (α * β).natDegree = D := by
    rw [Monic.natDegree_mul hmonα hmonβ, hdegα, hdegβ]
  have hfdeg : f.natDegree = D := by
    rw [← Polynomial.Monic.natDegree_map hf (PadicInt.toZModPow (p := p) m), hfac', hαβdeg]
  have hfSmon : fS.Monic := by
    dsimp [fS]
    exact Polynomial.Monic.map (PadicInt.toZModPow (m + 1)) hf
  have hfSdeg : fS.natDegree = D := by
    dsimp [fS]
    rw [Polynomial.Monic.natDegree_map hf (PadicInt.toZModPow (p := p) (m + 1)), hfdeg]
  -- monic lifts `A` of `α`, `B` of `β`
  have hAm : A.Monic := by
    dsimp [A]
    exact (coeffLift_monic_natDegree_prime m hm hmonα).1
  have hAd : A.natDegree = α.natDegree := by
    dsimp [A]
    exact (coeffLift_monic_natDegree_prime m hm hmonα).2
  have hBm : B.Monic := by
    dsimp [B]
    exact (coeffLift_monic_natDegree_prime m hm hmonβ).1
  have hBd : B.natDegree = β.natDegree := by
    dsimp [B]
    exact (coeffLift_monic_natDegree_prime m hm hmonβ).2
  have hAd1 : A.natDegree = d1 := by
    dsimp [d1]
    rw [hAd, hdegα]
  have hBd2 : B.natDegree = d2 := by
    dsimp [d2]
    rw [hBd, hdegβ]
  have hAc1 : A.coeff d1 = 1 := by
    have h := hAm.leadingCoeff
    rw [Polynomial.leadingCoeff, hAd1] at h
    exact h
  have hBc1 : B.coeff d2 = 1 := by
    have h := hBm.leadingCoeff
    rw [Polynomial.leadingCoeff, hBd2] at h
    exact h
  -- cast down and reduce the lifts
  have hAπ : Polynomial.map π A = α := by
    dsimp [A, π]
    exact map_castDown_coeffLift m α
  have hBπ : Polynomial.map π B = β := by
    dsimp [B, π]
    exact map_castDown_coeffLift m β
  have hredαm : Polynomial.map ρm α = a := by
    dsimp [ρm]
    simpa [red] using hredα
  have hredβm : Polynomial.map ρm β = b := by
    dsimp [ρm]
    simpa [red] using hredβ
  have hρ_comp : ρ = ρm.comp π := by
    ext x
    dsimp [ρ, ρm, π]
    exact redSucc_eq_red_comp_castDown m hm x
  have hAρ : Polynomial.map ρ A = a := by
    calc
      Polynomial.map ρ A = Polynomial.map (ρm.comp π) A := by rw [hρ_comp]
      _ = Polynomial.map ρm (Polynomial.map π A) := by rw [Polynomial.map_map]
      _ = a := by rw [hAπ, hredαm]
  have hBρ : Polynomial.map ρ B = b := by
    calc
      Polynomial.map ρ B = Polynomial.map (ρm.comp π) B := by rw [hρ_comp]
      _ = Polynomial.map ρm (Polynomial.map π B) := by rw [Polynomial.map_map]
      _ = b := by rw [hBπ, hredβm]
  -- ===== the error polynomial =====
  let E : (ZMod (p ^ (m + 1)))[X] := fS - A * B
  have hABdeg : (A * B).natDegree = D := by
    dsimp [D]
    rw [Monic.natDegree_mul hAm hBm, hAd1, hBd2]
  have hEdeg : ∀ j, D ≤ j → E.coeff j = 0 := by
    intro j hj
    dsimp [E]
    rw [Polynomial.coeff_sub]
    rcases lt_or_eq_of_le hj with hlt | heq
    · have hf0 : fS.coeff j = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [hfSdeg]
        exact hlt
      have hab0 : (A * B).coeff j = 0 := by
        apply coeff_eq_zero_of_natDegree_lt
        rw [hABdeg]
        exact hlt
      rw [hf0, hab0]
      simp
    · subst j
      have hf1 : fS.coeff D = 1 := by
        have h := hfSmon.leadingCoeff
        rw [Polynomial.leadingCoeff, hfSdeg] at h
        exact h
      have hab1 : (A * B).coeff D = 1 := by
        have h := (hAm.mul hBm).leadingCoeff
        rw [Polynomial.leadingCoeff, hABdeg] at h
        exact h
      rw [hf1, hab1]
      simp
  have hEπ : Polynomial.map π E = 0 := by
    dsimp [E]
    rw [Polynomial.map_sub, Polynomial.map_mul, hAπ, hBπ]
    have hcomp : π.comp (PadicInt.toZModPow (p := p) (m + 1)) = PadicInt.toZModPow (p := p) m := by
      dsimp [π]
      exact PadicInt.zmod_cast_comp_toZModPow (p := p) m (m + 1) (by omega : m ≤ m + 1)
    have hm : Polynomial.map π fS = α * β := by
      dsimp [fS]
      rw [Polynomial.map_map, hfac'.symm, hcomp]
    rw [hm]
    ring
  have hEπ_coeff : ∀ j, π (E.coeff j) = 0 := by
    intro j
    simpa [Polynomial.coeff_map] using (congrFun (congrArg Polynomial.coeff hEπ) j)
  have hEdiv : ∀ j, p ^ m ∣ (E.coeff j).val := by
    intro j
    have h := hEπ_coeff j
    dsimp [π] at h
    exact (castDown_eq_zero_iff_dvd_val m (E.coeff j)).mp h
  let W : (ZMod (p ^ (m + 1)))[X] :=
    coeffPoly (p ^ (m + 1)) (fun i => (((E.coeff i).val / p ^ m : ℕ) : ZMod (p ^ (m + 1)))) D
  have hEW : E = C c * W := by
    ext j
    rw [coeff_C_mul]
    by_cases hj : j < D
    · have hdivj := hEdiv j
      dsimp [W]
      rw [coeffPoly_coeff]
      rw [if_pos hj]
      exact eq_pow_mul_div_val m (E.coeff j) hdivj
    · have hjD : D ≤ j := by omega
      have hE0 : E.coeff j = 0 := hEdeg j hjD
      dsimp [W]
      rw [coeffPoly_coeff]
      rw [if_neg hj]
      rw [hE0]
      simp
  have hWdeg : W.degree < (D : WithBot ℕ) := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro j hj
    dsimp [W]
    rw [coeffPoly_coeff]
    have hnot : ¬ j < D := by omega
    rw [if_neg hnot]
  have hedeg : (Polynomial.map ρ W).degree < (a.natDegree + b.natDegree : WithBot ℕ) := by
    have hle : (Polynomial.map ρ W).degree ≤ W.degree := Polynomial.degree_map_le
    exact lt_of_le_of_lt hle (by
      have hD : (D : WithBot ℕ) = (a.natDegree + b.natDegree : WithBot ℕ) := by
        dsimp [D, d1, d2]
        simp
      simpa [hD] using hWdeg)
  let e : (ZMod p)[X] := Polynomial.map ρ W
  -- ===== the correction terms =====
  obtain ⟨u, v, hu_deg, hv_deg, hbez⟩ := bezout_decomp ha hb hcop hedeg
  let U : (ZMod (p ^ (m + 1)))[X] := coeffLift (p ^ (m + 1)) u
  let V : (ZMod (p ^ (m + 1)))[X] := coeffLift (p ^ (m + 1)) v
  have hUρ : Polynomial.map ρ U = u := by
    dsimp [U, ρ]
    exact map_redSucc_coeffLift m u
  have hVρ : Polynomial.map ρ V = v := by
    dsimp [V, ρ]
    exact map_redSucc_coeffLift m v
  have hUzero : ∀ i, a.natDegree ≤ i → U.coeff i = 0 := by
    intro i hi
    dsimp [U]
    rw [coeffLift_coeff (p ^ (m + 1))]
    by_cases hiu : i ≤ u.natDegree
    · rw [if_pos hiu]
      have hu0 := hu_deg i hi
      rw [hu0]
      simp
    · rw [if_neg hiu]
  have hVzero : ∀ i, b.natDegree ≤ i → V.coeff i = 0 := by
    intro i hi
    dsimp [V]
    rw [coeffLift_coeff (p ^ (m + 1))]
    by_cases hiv : i ≤ v.natDegree
    · rw [if_pos hiv]
      have hv0 := hv_deg i hi
      rw [hv0]
      simp
    · rw [if_neg hiv]
  -- ===== assemble the lifted factors =====
  let α' : (ZMod (p ^ (m + 1)))[X] := A + C c * U
  let β' : (ZMod (p ^ (m + 1)))[X] := B + C c * V
  have hAd' : A.natDegree = a.natDegree := by
    rw [hAd, hdegα]
  have hBd' : B.natDegree = b.natDegree := by
    rw [hBd, hdegβ]
  have hAc1' : A.coeff a.natDegree = 1 := by
    simpa [d1] using hAc1
  have hBc1' : B.coeff b.natDegree = 1 := by
    simpa [d2] using hBc1
  have hαc1 : α'.coeff a.natDegree = 1 := by
    dsimp [α']
    rw [Polynomial.coeff_add, coeff_C_mul]
    have hU1 : U.coeff a.natDegree = 0 := hUzero a.natDegree le_rfl
    rw [hAc1', hU1]
    simp
  have hαc0 : ∀ j, a.natDegree < j → α'.coeff j = 0 := by
    intro j hj
    dsimp [α']
    rw [Polynomial.coeff_add, coeff_C_mul]
    have hA0 : A.coeff j = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hAd']
      exact hj
    have hUj : U.coeff j = 0 := hUzero j (by omega)
    rw [hA0, hUj]
    simp
  have hβc1 : β'.coeff b.natDegree = 1 := by
    dsimp [β']
    rw [Polynomial.coeff_add, coeff_C_mul]
    have hV1 : V.coeff b.natDegree = 0 := hVzero b.natDegree le_rfl
    rw [hBc1', hV1]
    simp
  have hβc0 : ∀ j, b.natDegree < j → β'.coeff j = 0 := by
    intro j hj
    dsimp [β']
    rw [Polynomial.coeff_add, coeff_C_mul]
    have hB0 : B.coeff j = 0 := by
      apply coeff_eq_zero_of_natDegree_lt
      rw [hBd']
      exact hj
    have hVj : V.coeff j = 0 := hVzero j (by omega)
    rw [hB0, hVj]
    simp
  have hdegα' : α'.natDegree = a.natDegree := by
    refine le_antisymm ?_ ?_
    · rw [natDegree_le_iff_coeff_eq_zero]
      exact hαc0
    · exact le_natDegree_of_ne_zero (by rw [hαc1]; norm_num)
  have hdegβ' : β'.natDegree = b.natDegree := by
    refine le_antisymm ?_ ?_
    · rw [natDegree_le_iff_coeff_eq_zero]
      exact hβc0
    · exact le_natDegree_of_ne_zero (by rw [hβc1]; norm_num)
  have hmonα' : α'.Monic := by
    rw [Monic, Polynomial.leadingCoeff, hdegα']
    exact hαc1
  have hmonβ' : β'.Monic := by
    rw [Monic, Polynomial.leadingCoeff, hdegβ']
    exact hβc1
  have hQρ : Polynomial.map ρ (U * B + A * V - W) = 0 := by
    simp only [Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul]
    rw [hUρ, hBρ, hAρ, hVρ]
    rw [mul_comm a v, hbez]
    simp
  have hQcoeff : ∀ j, ρ ((U * B + A * V - W).coeff j) = 0 := by
    intro j
    have h := congrFun (congrArg Polynomial.coeff hQρ) j
    rw [Polynomial.coeff_map, Polynomial.coeff_zero] at h
    exact h
  have hlin : C c * (U * B + A * V - W) = 0 := by
    ext j
    rw [coeff_C_mul]
    exact pow_mul_eq_zero_of_redSucc_eq_zero m ((U * B + A * V - W).coeff j)
      (by simpa [ρ] using hQcoeff j)
  have hQuad : (C c) ^ 2 * (U * V) = 0 := by
    ext j
    calc
      ((C c) ^ 2 * (U * V)).coeff j = ((C c * C c) * (U * V)).coeff j := by rw [pow_two]
      _ = c * (c * (U * V).coeff j) := by
        rw [mul_assoc]
        rw [Polynomial.coeff_C_mul, Polynomial.coeff_C_mul]
      _ = (c * c) * (U * V).coeff j := by rw [mul_assoc]
      _ = c ^ 2 * (U * V).coeff j := by rw [← pow_two]
      _ = 0 := by
        have hc2 : c ^ 2 = 0 := by
          dsimp [c]
          exact pow_two_mul_eq_zero m hm
        rw [hc2]
        simp
  have hMain : A * B + C c * (U * B + A * V) + (C c) ^ 2 * (U * V) = fS := by
    have hAB : A * B = fS - C c * W := by
      have hh : fS - A * B = C c * W := by
        dsimp [E] at hEW
        exact hEW
      rw [sub_eq_iff_eq_add'] at hh
      rw [hh]
      ring
    have hStep : A * B + C c * (U * B + A * V) + (C c) ^ 2 * (U * V)
        = fS + C c * (U * B + A * V - W) + (C c) ^ 2 * (U * V) := by
      rw [hAB]
      ring
    rw [hStep, hlin, hQuad]
    ring
  have hprod : α' * β' = fS := by
    have hExp : α' * β' = A * B + C c * (U * B + A * V) + (C c) ^ 2 * (U * V) := by
      dsimp [α', β']
      ring
    exact hExp.trans hMain
  have hdownα' : Polynomial.map π α' = α := by
    dsimp [α']
    rw [Polynomial.map_add, hAπ]
    have hz : Polynomial.map π (C c * U) = 0 := by
      rw [Polynomial.map_mul, Polynomial.map_C]
      have hπc : π c = 0 := by
        dsimp [c, π]
        exact castDown_pow_eq_zero m
      rw [hπc]
      simp
    rw [hz]
    simp
  have hdownβ' : Polynomial.map π β' = β := by
    dsimp [β']
    rw [Polynomial.map_add, hBπ]
    have hz : Polynomial.map π (C c * V) = 0 := by
      rw [Polynomial.map_mul, Polynomial.map_C]
      have hπc : π c = 0 := by
        dsimp [c, π]
        exact castDown_pow_eq_zero m
      rw [hπc]
      simp
    rw [hz]
    simp
  have hredα' : Polynomial.map ρ α' = a := by
    dsimp [α']
    rw [Polynomial.map_add, hAρ]
    have hz : Polynomial.map ρ (C c * U) = 0 := by
      rw [Polynomial.map_mul, Polynomial.map_C]
      have hρc : ρ c = 0 := by
        dsimp [c, ρ]
        exact redSucc_pow_eq_zero m hm
      rw [hρc]
      simp
    rw [hz]
    simp
  have hredβ' : Polynomial.map ρ β' = b := by
    dsimp [β']
    rw [Polynomial.map_add, hBρ]
    have hz : Polynomial.map ρ (C c * V) = 0 := by
      rw [Polynomial.map_mul, Polynomial.map_C]
      have hρc : ρ c = 0 := by
        dsimp [c, ρ]
        exact redSucc_pow_eq_zero m hm
      rw [hρc]
      simp
    rw [hz]
    simp
  exact ⟨α', β', hmonα', hmonβ', by simpa [d1] using hdegα', by simpa [d2] using hdegβ',
    by simpa [fS] using hprod, hdownα', hdownβ', hredα', hredβ'⟩

end Commons.NumberTheory.Padics