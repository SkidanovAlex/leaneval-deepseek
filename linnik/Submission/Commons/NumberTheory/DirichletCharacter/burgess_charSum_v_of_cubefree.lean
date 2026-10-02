import Mathlib
import Submission.Commons.Data.Nat.factorization_prod_prime_pow_apply
import Submission.Commons.NumberTheory.DirichletCharacter.primitive_factor_coprime
import Submission.Commons.NumberTheory.DirichletCharacter.char_interval_sum_weyl_bound_aux

/-!
# Burgess's bound for general moduli from the cube-free case

This file proves `Commons.NumberTheory.DirichletCharacter.burgess_charSum_v_of_cubefree`:
a uniform Burgess-type bound for character sums over intervals, valid for arbitrary moduli,
deduced from the same bound for cube-free moduli.

The mathematical content is the reduction of Heath-Brown, *Zero-free regions for Dirichlet
L-functions and the least prime in an arithmetic progression*, Lemma 2.3: writing
`q = u · v` with `u` the cube-free part of `q` and `v` the product of the prime powers
`p ^ v_p(q)` over the primes `p` with `v_p(q) ≥ 3`, one factors a primitive character
`χ mod q` as `χ_u χ_v` with `χ_u` primitive of cube-free modulus `u`, splits the interval
`(N, N+H]` into its `v` residue classes modulo `v`, and applies the cube-free bound to
`χ_u` on the resulting intervals of length `≈ H/v`.  The `v` intervals contribute a factor
`v · (H/v)^{1-1/k} = v^{1/k} H^{1-1/k}`.

The whole argument is carried out at the level `u * v`; the reduction from a general modulus
`q` to `u * v` is a single substitution (`subst`).
-/

open Finset

namespace Commons.NumberTheory.DirichletCharacter

/-! ### The cube-free / cubeful splitting of a modulus -/

/-- The cubeful part of `q`: the product of the full prime powers `p ^ v_p(q)` over the
primes `p` with `v_p(q) ≥ 3`. -/
def cubefulPart (q : ℕ) : ℕ :=
  ∏ p ∈ q.primeFactors.filter (fun p => 3 ≤ q.factorization p), p ^ q.factorization p

/-- The cube-free part of `q`. -/
def cubeFreePart (q : ℕ) : ℕ :=
  ∏ p ∈ q.primeFactors.filter (fun p => ¬ 3 ≤ q.factorization p), p ^ q.factorization p

lemma factorization_cubefulPart_apply (q p : ℕ) :
    (cubefulPart q).factorization p =
      if p ∈ q.primeFactors.filter (fun r => 3 ≤ q.factorization r)
        then q.factorization p else 0 :=
  Commons.Data.Nat.factorization_prod_prime_pow_apply _ _
    (fun r hr => (Nat.mem_primeFactors.mp (Finset.mem_of_mem_filter r hr)).1) p

lemma factorization_cubeFreePart_apply (q p : ℕ) :
    (cubeFreePart q).factorization p =
      if p ∈ q.primeFactors.filter (fun r => ¬ 3 ≤ q.factorization r)
        then q.factorization p else 0 :=
  Commons.Data.Nat.factorization_prod_prime_pow_apply _ _
    (fun r hr => (Nat.mem_primeFactors.mp (Finset.mem_of_mem_filter r hr)).1) p

lemma cubefulPart_mul_cubeFreePart (q : ℕ) (hq : q ≠ 0) :
    cubefulPart q * cubeFreePart q = q := by
  rw [cubefulPart, cubeFreePart,
    Finset.prod_filter_mul_prod_filter_not q.primeFactors (fun p => 3 ≤ q.factorization p)
      (fun p => p ^ q.factorization p)]
  exact (Nat.prod_primeFactors_pow_factorization hq).symm

lemma cubefulPart_pos (q : ℕ) : 0 < cubefulPart q := by
  rw [cubefulPart]
  refine Finset.prod_pos fun p hp => pow_pos ?_ _
  exact (Nat.mem_primeFactors.mp (Finset.mem_of_mem_filter p hp)).1.pos

lemma cubeFreePart_pos (q : ℕ) : 0 < cubeFreePart q := by
  rw [cubeFreePart]
  refine Finset.prod_pos fun p hp => pow_pos ?_ _
  exact (Nat.mem_primeFactors.mp (Finset.mem_of_mem_filter p hp)).1.pos

lemma prime_dvd_cubefulPart_iff {q p : ℕ} (hp : p.Prime) (hq : q ≠ 0) :
    p ∣ cubefulPart q ↔ p ∈ q.primeFactors.filter (fun r => 3 ≤ q.factorization r) := by
  have hne : cubefulPart q ≠ 0 := ne_of_gt (cubefulPart_pos q)
  constructor
  · intro h
    have h1 : 1 ≤ (cubefulPart q).factorization p := (hp.dvd_iff_one_le_factorization hne).mp h
    rw [factorization_cubefulPart_apply] at h1
    by_contra hmem
    rw [if_neg hmem] at h1
    omega
  · intro hmem
    have hfact : 1 ≤ (cubefulPart q).factorization p := by
      rw [factorization_cubefulPart_apply, if_pos hmem]
      exact le_trans (by norm_num) (Finset.mem_filter.mp hmem).2
    exact (hp.dvd_iff_one_le_factorization hne).mpr hfact

lemma prime_dvd_cubeFreePart_iff {q p : ℕ} (hp : p.Prime) (hq : q ≠ 0) :
    p ∣ cubeFreePart q ↔ p ∈ q.primeFactors.filter (fun r => ¬ 3 ≤ q.factorization r) := by
  have hne : cubeFreePart q ≠ 0 := ne_of_gt (cubeFreePart_pos q)
  constructor
  · intro h
    have h1 : 1 ≤ (cubeFreePart q).factorization p := (hp.dvd_iff_one_le_factorization hne).mp h
    rw [factorization_cubeFreePart_apply] at h1
    by_contra hmem
    rw [if_neg hmem] at h1
    omega
  · intro hmem
    have hpq : p ∣ q := (Nat.mem_primeFactors.mp (Finset.mem_filter.mp hmem).1).2.1
    have hfact : 1 ≤ (cubeFreePart q).factorization p := by
      rw [factorization_cubeFreePart_apply, if_pos hmem]
      exact (hp.dvd_iff_one_le_factorization hq).mp hpq
    exact (hp.dvd_iff_one_le_factorization hne).mpr hfact

lemma cubefulPart_coprime_cubeFreePart (q : ℕ) (hq : q ≠ 0) :
    (cubefulPart q).Coprime (cubeFreePart q) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have h1 := (prime_dvd_cubefulPart_iff hp hq).mp (hpd.trans (Nat.gcd_dvd_left _ _))
  have h2 := (prime_dvd_cubeFreePart_iff hp hq).mp (hpd.trans (Nat.gcd_dvd_right _ _))
  rw [Finset.mem_filter] at h1 h2
  exact h2.2 h1.2

lemma cubeFreePart_mul_cubefulPart (q : ℕ) (hq : q ≠ 0) :
    cubeFreePart q * cubefulPart q = q := by
  rw [mul_comm]; exact cubefulPart_mul_cubeFreePart q hq

lemma cubefulPart_le (q : ℕ) (hq : q ≠ 0) : cubefulPart q ≤ q :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hq)
    ⟨cubeFreePart q, (cubefulPart_mul_cubeFreePart q hq).symm⟩

lemma cubeFreePart_le (q : ℕ) (hq : q ≠ 0) : cubeFreePart q ≤ q :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero hq)
    ⟨cubefulPart q, (cubeFreePart_mul_cubefulPart q hq).symm⟩

lemma cubeFreePart_cube_free (q : ℕ) (p : ℕ) (hp : p.Prime) :
    ¬ p ^ 3 ∣ cubeFreePart q := by
  intro h
  have hne : cubeFreePart q ≠ 0 := ne_of_gt (cubeFreePart_pos q)
  have h1 : 3 ≤ (cubeFreePart q).factorization p :=
    (hp.pow_dvd_iff_le_factorization hne).mp h
  rw [factorization_cubeFreePart_apply] at h1
  by_cases hmem : p ∈ q.primeFactors.filter (fun r => ¬ 3 ≤ q.factorization r)
  · rw [if_pos hmem] at h1
    exact (Finset.mem_filter.mp hmem).2 h1
  · rw [if_neg hmem] at h1
    omega

end Commons.NumberTheory.DirichletCharacter

namespace Commons.NumberTheory.DirichletCharacter

section Core

variable {k : ℕ} {ε CB : ℝ}

/-- The cube-free Burgess hypothesis `hB` in the `Icc` form in which it is applied to the
residue classes: the sum of a primitive character over `c` consecutive integers. -/
lemma burgess_Icc_of_hB (hε : 0 < ε) (hk : 2 ≤ k) (hCB : 0 < CB)
    (hB : ∀ {u : ℕ} [NeZero u] (ψ : DirichletCharacter ℂ u), ψ.IsPrimitive → ψ ≠ 1 →
      (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ u) →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ u →
        ‖∑ n ∈ Finset.Ioc N (N + H), ψ n‖ ≤
          CB * (u : ℝ) ^ (((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2) + ε)
            * (H : ℝ) ^ (1 - 1 / (k : ℝ)))
    {U : ℕ} [NeZero U] (ψ : DirichletCharacter ℂ U) (hprim : ψ.IsPrimitive) (h1 : ψ ≠ 1)
    (hcube : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ U)
    {L c : ℕ} (hL : 1 ≤ L) (hc : 1 ≤ c) (hcu : c ≤ U) :
    ‖∑ t ∈ Finset.Icc L (L + c - 1), ψ t‖ ≤
      (1 + CB) * (U : ℝ) ^ (((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2) + ε)
        * (c : ℝ) ^ (1 - 1 / (k : ℝ)) := by
  set a : ℝ := ((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2) + ε with ha
  set b : ℝ := 1 - 1 / (k : ℝ) with hb
  have hU1 : (1 : ℝ) ≤ (U : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne U)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
    have : (1 : ℕ) ≤ k := by omega
    exact_mod_cast this
  have hkpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le zero_lt_one hk1
  have hb0 : 0 ≤ b := by
    rw [hb]
    have hle : (1 : ℝ) / (k : ℝ) ≤ 1 := by rw [div_le_one hkpos]; exact hk1
    linarith only [hle]
  have ha0 : 0 ≤ a := by
    rw [ha]
    have hnum : (0 : ℝ) < (k : ℝ) + 1 := by linarith only [hk1]
    have hden : (0 : ℝ) < 4 * (k : ℝ) ^ 2 := by positivity
    have := div_pos hnum hden
    linarith only [hε, this]
  have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hc
  have hUa : (0 : ℝ) ≤ (U : ℝ) ^ a := Real.rpow_nonneg (by positivity) a
  have hcb0 : (0 : ℝ) ≤ (c : ℝ) ^ b := Real.rpow_nonneg (by positivity) b
  have hbase : (1 : ℝ) ≤ (U : ℝ) ^ a * (c : ℝ) ^ b := by
    have h1 := Real.one_le_rpow hU1 ha0
    have h2 := Real.one_le_rpow hc1 hb0
    have h3 : (1 : ℝ) * 1 ≤ (U : ℝ) ^ a * (c : ℝ) ^ b :=
      mul_le_mul h1 h2 (by norm_num) hUa
    simpa using h3
  rcases eq_or_lt_of_le hL with hL1 | hL2
  · -- L = 1
    subst hL1
    rcases eq_or_lt_of_le hc with hcv | hcv
    · -- c = 1
      have hset : Finset.Icc 1 (1 + c - 1) = ({1} : Finset ℕ) := by rw [← hcv]; norm_num
      rw [hset, Finset.sum_singleton]
      have hone : ψ ((1 : ℕ) : ZMod U) = 1 := by
        rw [show ((1 : ℕ) : ZMod U) = 1 by norm_num]; exact map_one ψ
      rw [hone, norm_one]
      have hcb1 : (c : ℝ) ^ b = 1 := by rw [← hcv]; simp
      rw [hcb1, mul_one]
      have hbase' : (1 : ℝ) ≤ (U : ℝ) ^ a := by rw [hcb1, mul_one] at hbase; exact hbase
      nlinarith only [hCB, hUa, hbase']
    · -- c ≥ 2
      have hset : Finset.Icc 1 (1 + c - 1) = insert 1 (Finset.Ioc 1 (1 + (c - 1))) := by
        ext t
        simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ioc]
        omega
      rw [hset, Finset.sum_insert (by simp)]
      have hone : ψ ((1 : ℕ) : ZMod U) = 1 := by
        rw [show ((1 : ℕ) : ZMod U) = 1 by norm_num]; exact map_one ψ
      rw [hone]
      have hc'1 : 1 ≤ c - 1 := by omega
      have hBapp := hB ψ hprim h1 hcube (N := 1) (H := c - 1) le_rfl hc'1 (by omega)
      have hcb : ((c - 1 : ℕ) : ℝ) ^ b ≤ (c : ℝ) ^ b :=
        Real.rpow_le_rpow (by positivity) (by exact_mod_cast Nat.sub_le c 1) hb0
      have hstep1 : ‖(1 : ℂ) + ∑ t ∈ Finset.Ioc 1 (1 + (c - 1)), ψ t‖
          ≤ 1 + CB * (U : ℝ) ^ a * ((c - 1 : ℕ) : ℝ) ^ b := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_one]
        linarith only [hBapp]
      have hstep2 : 1 + CB * (U : ℝ) ^ a * ((c - 1 : ℕ) : ℝ) ^ b
          ≤ 1 + CB * (U : ℝ) ^ a * (c : ℝ) ^ b := by
        have hCBU : (0 : ℝ) ≤ CB * (U : ℝ) ^ a := mul_nonneg hCB.le hUa
        have := mul_le_mul_of_nonneg_left hcb hCBU
        linarith only [this]
      have hstep3 : 1 + CB * (U : ℝ) ^ a * (c : ℝ) ^ b
          ≤ (1 + CB) * (U : ℝ) ^ a * (c : ℝ) ^ b := by
        linarith only [hCB, hUa, hcb0, hbase]
      linarith only [hstep1, hstep2, hstep3, hbase]
  · -- L ≥ 2
    have hset : Finset.Icc L (L + c - 1) = Finset.Ioc (L - 1) (L - 1 + c) := by
      ext t
      simp only [Finset.mem_Icc, Finset.mem_Ioc]
      omega
    rw [hset]
    have hBapp := hB ψ hprim h1 hcube (N := L - 1) (H := c) (by omega) hc (by omega)
    linarith only [hBapp, hCB, hUa, hcb0, hbase]

/-- Reindexing an `Icc`-sum by a translation. -/
lemma sum_Icc_add_eq {M : Type*} [AddCommMonoid M] (f : ℕ → M) (L s_lo s_hi : ℕ) :
    ∑ m ∈ Finset.Icc s_lo s_hi, f (L + m) = ∑ t ∈ Finset.Icc (L + s_lo) (L + s_hi), f t := by
  have hset : (Finset.Icc s_lo s_hi).image (fun m => L + m)
      = Finset.Icc (L + s_lo) (L + s_hi) := by
    have h := Finset.image_add_right_Icc s_lo s_hi L
    simpa [add_comm, add_left_comm, add_assoc] using h
  rw [← hset]
  refine Finset.sum_bij (fun m _ => L + m) ?_ ?_ ?_ ?_
  · intro m hm; rw [Finset.mem_image]; exact ⟨m, hm, rfl⟩
  · intro m₁ _ m₂ _ h; omega
  · intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨m, hm, rfl⟩ := ht
    exact ⟨m, hm, rfl⟩
  · intro m _; rfl

/-- An `Icc`-interval of naturals is the interval of the same length starting at its bottom. -/
lemma Icc_eq_Icc_card (l h : ℕ) :
    Finset.Icc l h = Finset.Icc l (l + (Finset.Icc l h).card - 1) := by
  rw [Nat.card_Icc]
  ext t
  simp only [Finset.mem_Icc]
  omega

/-- **The bound for a single residue class.**
For a primitive character `χ_u` of cube-free modulus `u` and a residue class `a mod v`
(`1 ≤ a ≤ v`), the sum of `χ_u` (after the substitution `n = a + v m ↦ (w a + a/v) + m`)
over the `m` for which `a + v m ∈ (N, N + H]` is bounded by the cube-free Burgess bound. -/
lemma burgess_class_bound {u v : ℕ} [NeZero u] [NeZero v]
    {k : ℕ} {ε CB : ℝ} (hε : 0 < ε) (hk : 2 ≤ k) (hCB : 0 < CB)
    (hB : ∀ {u' : ℕ} [NeZero u'] (ψ : DirichletCharacter ℂ u'), ψ.IsPrimitive → ψ ≠ 1 →
      (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ u') →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ u' →
        ‖∑ n ∈ Finset.Ioc N (N + H), ψ n‖ ≤
          CB * (u' : ℝ) ^ (((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2) + ε)
            * (H : ℝ) ^ (1 - 1 / (k : ℝ)))
    (hcube : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ u)
    {χu : DirichletCharacter ℂ u} (hprim : χu.IsPrimitive) (h1u : χu ≠ 1)
    {w : ℕ} (hw1 : 1 ≤ w) (hw : (w : ZMod u) * (v : ZMod u) = 1)
    {N H a : ℕ} (hN : 1 ≤ N) (ha1 : 1 ≤ a) (hav : a ≤ v) (hH : v < H) (hHu : H ≤ u * v) :
    ‖∑ m ∈ Finset.Icc ((N + v - a) / v) ((N + H - a) / v),
        χu (((w * (a % v) + (a + v * m) / v : ℕ)) : ZMod u)‖
      ≤ (1 + CB) * (u : ℝ) ^ (((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2) + ε)
          * (((Finset.Icc ((N + v - a) / v) ((N + H - a) / v)).card : ℝ))
              ^ (1 - 1 / (k : ℝ)) := by
  have hv1 : 0 < v := Nat.pos_of_ne_zero (NeZero.ne v)
  obtain ⟨s_lo, hslo⟩ : ∃ s, s = (N + v - a) / v := ⟨_, rfl⟩
  obtain ⟨s_hi, hshi⟩ : ∃ s, s = (N + H - a) / v := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c, c = (Finset.Icc s_lo s_hi).card := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = w * (a % v) + a / v + s_lo := ⟨_, rfl⟩
  have hu1 : 1 ≤ u := Nat.one_le_iff_ne_zero.mpr (NeZero.ne u)
  have hlo' : N + 1 ≤ a + v * ((N + v - a) / v) :=
    (le_add_mul_iff_div_le hv1 hav).mpr le_rfl
  have hhi' : a + v * ((N + H - a) / v) ≤ N + H :=
    (add_mul_le_iff_le_div hv1 (by omega : a ≤ N + H)).mpr le_rfl
  have hlo : N + 1 ≤ a + v * s_lo := by rw [hslo]; exact hlo'
  have hhi : a + v * s_hi ≤ N + H := by rw [hshi]; exact hhi'
  have hsle : s_lo ≤ s_hi := by
    rw [hslo, hshi]
    exact Nat.div_le_div_right (by omega)
  have hsle' : (N + v - a) / v ≤ (N + H - a) / v := by rw [← hslo, ← hshi]; exact hsle
  have hcard : c = s_hi + 1 - s_lo := by rw [hc, hslo, hshi]; exact Nat.card_Icc _ _
  have hcge1 : 1 ≤ c := by rw [hcard]; omega
  have hcleu : c ≤ u := by
    have h := div_interval_len_le (q := v) (Y := u) (N := N) (M := H) (a := a)
      (by omega) hu1 (by rw [mul_comm]; exact hHu) hlo' hhi'
    have heq : (N + H - a) / v + 1 - (N + v - a) / v
        = (N + H - a) / v - (N + v - a) / v + 1 := by omega
    rw [hcard, hslo, hshi, heq]
    exact h
  have hc1 : (1 : ℝ) ≤ (c : ℝ) := by exact_mod_cast hcge1
  have hLge1 : 1 ≤ L := by
    rw [hL]
    by_cases hmod0 : a % v = 0
    · have haeq : a = v :=
        le_antisymm hav (Nat.le_of_dvd (by omega : 0 < a) (Nat.dvd_of_mod_eq_zero hmod0))
      rw [haeq, Nat.mod_self, mul_zero, Nat.div_self hv1]
      omega
    · have hge1 : 1 ≤ a % v := by omega
      have h1 : 1 ≤ w * (a % v) := by
        calc (1 : ℕ) ≤ w := hw1
          _ = w * 1 := (mul_one w).symm
          _ ≤ w * (a % v) := Nat.mul_le_mul_left w hge1
      calc (1 : ℕ) ≤ w * (a % v) := h1
        _ ≤ w * (a % v) + a / v := Nat.le_add_right _ _
        _ ≤ w * (a % v) + a / v + s_lo := Nat.le_add_right _ _
  have hshift1 : ∑ m ∈ Finset.Icc s_lo s_hi, χu (((w * (a % v) + (a + v * m) / v : ℕ)) : ZMod u)
      = ∑ m ∈ Finset.Icc s_lo s_hi, χu ((((w * (a % v) + a / v) + m : ℕ)) : ZMod u) := by
    refine Finset.sum_congr rfl fun m _ => ?_
    have h : (w * (a % v) + (a + v * m) / v : ℕ) = (w * (a % v) + a / v) + m := by
      rw [Nat.add_mul_div_left a m hv1, add_assoc]
    rw [h]
  have hshift2 : ∑ m ∈ Finset.Icc s_lo s_hi, χu ((((w * (a % v) + a / v) + m : ℕ)) : ZMod u)
      = ∑ t ∈ Finset.Icc L (L + c - 1), χu t := by
    rw [sum_Icc_add_eq (f := fun n => χu ((n : ℕ) : ZMod u))]
    have e1 : w * (a % v) + a / v + s_lo = L := hL.symm
    have e2 : w * (a % v) + a / v + s_hi = L + c - 1 := by
      rw [hL, hcard]; omega
    rw [e1, e2]
  rw [← hslo, ← hshi, ← hc, hshift1, hshift2]
  exact burgess_Icc_of_hB hε hk hCB hB χu hprim h1u hcube hLge1 hcge1 hcleu


/-- The key pointwise decomposition: for a primitive character `χ = χ_u χ_v` of modulus
`u * v` (with `u`, `v` coprime) and `w` an inverse of `v` modulo `u`, the value of `χ` at
`n` is `χ_u(v) · χ_u(w (n % v) + n / v) · χ_v(n % v)`. -/
lemma char_decomp_pointwise {u v : ℕ} [NeZero u] [NeZero v] (hcop : u.Coprime v)
    {χu : DirichletCharacter ℂ u} {χv : DirichletCharacter ℂ v}
    {χ : DirichletCharacter ℂ (u * v)}
    (hfac : χ = χu.changeLevel (Nat.dvd_mul_right u v) *
      χv.changeLevel (Nat.dvd_mul_left v u))
    {w : ℕ} (hw : (w : ZMod u) * (v : ZMod u) = 1) (n : ℕ) :
    χ ((n : ℕ) : ZMod (u * v))
      = χu ((v : ℕ) : ZMod u) * χu (((w * (n % v) + n / v : ℕ)) : ZMod u)
          * χv ((n % v : ℕ) : ZMod v) := by
  have hkey : (((w * (n % v) + n / v : ℕ)) : ZMod u) * (v : ZMod u) = (n : ZMod u) := by
    have h1 : (((w * (n % v) + n / v : ℕ)) : ZMod u) * (v : ZMod u)
        = (((w * (n % v) + n / v : ℕ)) * v : ℕ) := by push_cast; ring
    rw [h1]
    have h2 : ((w * (n % v) + n / v : ℕ)) * v = (w * v) * (n % v) + v * (n / v) := by ring
    rw [h2]
    push_cast
    rw [hw, one_mul, ← Nat.cast_mul, ← Nat.cast_add, Nat.mod_add_div]
  rw [hfac, MulChar.mul_apply]
  by_cases hc : Nat.Coprime n (u * v)
  · have hu : IsCoprime (n : ℤ) ((u * v : ℕ) : ℤ) := (Nat.isCoprime_iff_coprime).mpr hc
    have e1 : (χu.changeLevel (Nat.dvd_mul_right u v)) ((n : ℕ) : ZMod (u * v))
        = χu ((n : ℕ) : ZMod u) := by
      have := DirichletCharacter.changeLevel_eq_cast_of_dvd' χu (Nat.dvd_mul_right u v) hu
      simpa using this
    have e2 : (χv.changeLevel (Nat.dvd_mul_left v u)) ((n : ℕ) : ZMod (u * v))
        = χv ((n % v : ℕ) : ZMod v) := by
      have h1 := DirichletCharacter.changeLevel_eq_cast_of_dvd' χv (Nat.dvd_mul_left v u) hu
      have h2 : ((n : ℕ) : ZMod v) = ((n % v : ℕ) : ZMod v) := by
        rw [ZMod.natCast_eq_natCast_iff]; exact (Nat.mod_modEq n v).symm
      have h3 : ((n : ℤ) : ZMod (u * v)) = ((n : ℕ) : ZMod (u * v)) := by push_cast; rfl
      have h4 : ((n : ℤ) : ZMod v) = ((n % v : ℕ) : ZMod v) := by push_cast; exact h2
      rw [h3, h4] at h1
      exact h1
    rw [e1, e2]
    congr 1
    rw [← hkey]
    simp only [map_mul]
    ring
  · have hnu : ¬ IsUnit ((n : ℕ) : ZMod (u * v)) := by
      rw [ZMod.isUnit_iff_coprime]; exact hc
    have h0u : (χu.changeLevel (Nat.dvd_mul_right u v)) ((n : ℕ) : ZMod (u * v)) = 0 :=
      MulChar.map_nonunit _ hnu
    have h0v : (χv.changeLevel (Nat.dvd_mul_left v u)) ((n : ℕ) : ZMod (u * v)) = 0 :=
      MulChar.map_nonunit _ hnu
    rw [h0u, h0v, zero_mul]
    symm
    rcases Classical.em (Nat.Coprime n v) with hcv | hcv
    · have hcnu : ¬ Nat.Coprime n u := fun h => hc (h.mul_right hcv)
      have hxu : ¬ IsUnit (((w * (n % v) + n / v : ℕ)) : ZMod u) := by
        intro hunit
        have hvu : IsUnit ((v : ℕ) : ZMod u) := (ZMod.isUnit_iff_coprime v u).mpr hcop.symm
        have hmul : IsUnit ((((w * (n % v) + n / v : ℕ)) : ZMod u) * (v : ZMod u)) :=
          IsUnit.mul hunit hvu
        rw [hkey] at hmul
        exact hcnu ((ZMod.isUnit_iff_coprime n u).mp hmul)
      rw [MulChar.map_nonunit _ hxu]
      ring
    · have hnv : ¬ IsUnit (((n % v : ℕ)) : ZMod v) := by
        intro hunit
        have h2 : ((n : ℕ) : ZMod v) = ((n % v : ℕ) : ZMod v) := by
          rw [ZMod.natCast_eq_natCast_iff]; exact (Nat.mod_modEq n v).symm
        rw [← h2] at hunit
        exact hcv ((ZMod.isUnit_iff_coprime n v).mp hunit)
      rw [MulChar.map_nonunit _ hnv]
      ring


/-- The number of integers of a residue class `a mod v` in an interval of length `H` is at
most `H / v + 1`. -/
lemma card_Icc_div_le {v a N H : ℕ} (hv : 0 < v) (ha : a ≤ v) (hH : 1 ≤ H) :
    ((Finset.Icc ((N + v - a) / v) ((N + H - a) / v)).card : ℝ) ≤ (H : ℝ) / v + 1 := by
  rcases le_or_gt ((N + v - a) / v) ((N + H - a) / v) with hle | hlt
  · have hcard : (Finset.Icc ((N + v - a) / v) ((N + H - a) / v)).card
        = (N + H - a) / v - (N + v - a) / v + 1 := by
      rw [Nat.card_Icc]; omega
    have hbd : (N + H - a) / v - (N + v - a) / v ≤ (H - 1) / v := by
      rw [Nat.le_div_iff_mul_le hv, Nat.mul_sub_right_distrib]
      have h1 : (N + H - a) / v * v ≤ N + H - a := Nat.div_mul_le_self _ _
      have h2 : N + 1 ≤ a + (N + v - a) / v * v := by
        have h := (le_add_mul_iff_div_le (N := N) hv ha).mpr le_rfl
        rwa [mul_comm v ((N + v - a) / v)] at h
      have hBA : (N + v - a) / v * v ≤ (N + H - a) / v * v :=
        Nat.mul_le_mul_right v hle
      omega
    have hbd' : (((N + H - a) / v - (N + v - a) / v : ℕ) : ℝ) ≤ (H : ℝ) / v := by
      have h1 : (((N + H - a) / v - (N + v - a) / v : ℕ) : ℝ) ≤ (((H - 1) / v : ℕ) : ℝ) := by
        exact_mod_cast hbd
      have h2 : (((H - 1) / v : ℕ) : ℝ) ≤ ((H - 1 : ℕ) : ℝ) / (v : ℝ) := Nat.cast_div_le
      have h3 : ((H - 1 : ℕ) : ℝ) / (v : ℝ) ≤ (H : ℝ) / (v : ℝ) :=
        div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le H 1) (by positivity)
      linarith only [h1, h2, h3]
    rw [hcard]
    push_cast
    linarith only [hbd']
  · have hz : (Finset.Icc ((N + v - a) / v) ((N + H - a) / v)).card = 0 := by
      rw [Finset.card_eq_zero, Finset.Icc_eq_empty_iff]; omega
    rw [hz]
    have : (0 : ℝ) ≤ (H : ℝ) / v := by positivity
    linarith only [this]

/-- **Reduction of the general modulus case to the cube-free case** (Heath-Brown, Lemma 2.3).

Given the cube-free Burgess bound `hB` for primitive characters of cube-free modulus, the
same bound holds for a primitive character of arbitrary modulus `q = u · v`, where `u` is
cube-free and `v` is the product of the prime powers `p ^ v_p(q)` over the primes with
`v_p(q) ≥ 3`, at the cost of the extra factor `v^((3k-1)/(4k²))`. -/
lemma burgess_v_aux {q u v : ℕ} [NeZero q] [NeZero u] [NeZero v]
    (hquv : q = u * v) (hcop : u.Coprime v) (hcube : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ u)
    {k : ℕ} {ε CB : ℝ} (hε : 0 < ε) (hk : 2 ≤ k) (hCB : 0 < CB)
    (hB : ∀ {u' : ℕ} [NeZero u'] (ψ : DirichletCharacter ℂ u'), ψ.IsPrimitive → ψ ≠ 1 →
      (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ u') →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ u' →
        ‖∑ n ∈ Finset.Ioc N (N + H), ψ n‖ ≤
          CB * (u' : ℝ) ^ (((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2) + ε)
            * (H : ℝ) ^ (1 - 1 / (k : ℝ)))
    (χ : DirichletCharacter ℂ q) (hprim : χ.IsPrimitive) (hne : χ ≠ 1)
    {N H : ℕ} (hN : 1 ≤ N) (hH : 1 ≤ H) (hHq : H ≤ q) :
    ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤
      (2 * (1 + CB)) * (v : ℝ) ^ ((3 * (k : ℝ) - 1) / (4 * (k : ℝ) ^ 2))
        * (q : ℝ) ^ (((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2) + ε)
        * (H : ℝ) ^ (1 - 1 / (k : ℝ)) := by
  subst hquv
  set A : ℝ := ((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2) + ε with hA
  set B : ℝ := 1 - 1 / (k : ℝ) with hB_def
  set S : ℝ := (3 * (k : ℝ) - 1) / (4 * (k : ℝ) ^ 2) with hS
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by
    have : (1 : ℕ) ≤ k := by omega
    exact_mod_cast this
  have hkpos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le zero_lt_one hk1
  have hB0 : 0 ≤ B := by
    rw [hB_def]
    have hle : (1 : ℝ) / (k : ℝ) ≤ 1 := by rw [div_le_one hkpos]; exact hk1
    linarith only [hle]
  have hB1 : B ≤ 1 := by
    rw [hB_def]
    have : (0 : ℝ) ≤ 1 / (k : ℝ) := by positivity
    linarith only [this]
  have hA0 : 0 ≤ A := by
    rw [hA]
    have hnum : (0 : ℝ) < (k : ℝ) + 1 := by linarith only [hk1]
    have hden : (0 : ℝ) < 4 * (k : ℝ) ^ 2 := by positivity
    have := div_pos hnum hden
    linarith only [hε, this]
  have hS0 : 0 ≤ S := by
    rw [hS]
    have hnum : (0 : ℝ) ≤ 3 * (k : ℝ) - 1 := by linarith only [hk1]
    have hden : (0 : ℝ) < 4 * (k : ℝ) ^ 2 := by positivity
    exact div_nonneg hnum hden.le
  have hexp : S + A = 1 / (k : ℝ) + ε := by
    rw [hS, hA]; field_simp; ring
  have hBexp : B + 1 / (k : ℝ) = 1 := by rw [hB_def]; ring
  have hv1 : (1 : ℝ) ≤ (v : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne v)
  have hu1 : (1 : ℝ) ≤ (u : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne u)
  have huv1 : (1 : ℝ) ≤ ((u * v : ℕ) : ℝ) := by
    have : (1 : ℕ) ≤ u * v :=
      Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (NeZero.ne u) (NeZero.ne v))
    exact_mod_cast this
  have hvpos : (0 : ℝ) < (v : ℝ) := by linarith only [hv1]
  rcases le_or_gt H v with hHv | hHv
  · -- case A: the interval is short compared to `v`
    have hSbd : ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤ (H : ℝ) := by
      calc ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖
          ≤ ∑ n ∈ Finset.Ioc N (N + H), ‖χ n‖ := norm_sum_le _ _
        _ ≤ ∑ _n ∈ Finset.Ioc N (N + H), (1 : ℝ) :=
            Finset.sum_le_sum fun n _ => χ.norm_le_one _
        _ = ((Finset.Ioc N (N + H)).card : ℝ) := by simp
        _ = (H : ℝ) := by rw [Nat.card_Ioc]; norm_num
    have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
    have hHbb : (0 : ℝ) ≤ (H : ℝ) ^ B := Real.rpow_nonneg hHpos.le B
    have hsplit : (H : ℝ) = (H : ℝ) ^ (1 / (k : ℝ)) * (H : ℝ) ^ B := by
      rw [← Real.rpow_add hHpos,
        show 1 / (k : ℝ) + B = 1 by rw [hB_def]; ring, Real.rpow_one]
    have hHk : (H : ℝ) ^ (1 / (k : ℝ)) ≤ (v : ℝ) ^ (1 / (k : ℝ)) :=
      Real.rpow_le_rpow hHpos.le (by exact_mod_cast hHv) (by positivity)
    have hvv : (v : ℝ) ^ (1 / (k : ℝ)) ≤ (v : ℝ) ^ S * ((u * v : ℕ) : ℝ) ^ A := by
      have h1 : (v : ℝ) ^ (1 / (k : ℝ)) ≤ (v : ℝ) ^ (1 / (k : ℝ) + ε) :=
        Real.rpow_le_rpow_of_exponent_le hv1 (by linarith only [hε])
      have h2 : (v : ℝ) ^ (1 / (k : ℝ) + ε) = (v : ℝ) ^ S * (v : ℝ) ^ A := by
        rw [← hexp, Real.rpow_add hvpos]
      have h3 : (v : ℝ) ^ S * (v : ℝ) ^ A ≤ (v : ℝ) ^ S * ((u * v : ℕ) : ℝ) ^ A :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (by positivity)
            (by exact_mod_cast Nat.le_mul_of_pos_left v (Nat.pos_of_ne_zero (NeZero.ne u))) hA0)
          (Real.rpow_nonneg hvpos.le S)
      exact h1.trans (h2.le.trans h3)
    have hstep : (v : ℝ) ^ S * ((u * v : ℕ) : ℝ) ^ A * (H : ℝ) ^ B
        ≤ (2 * (1 + CB)) * (v : ℝ) ^ S * ((u * v : ℕ) : ℝ) ^ A * (H : ℝ) ^ B := by
      have hX : (1 : ℝ) ≤ (v : ℝ) ^ S * ((u * v : ℕ) : ℝ) ^ A := by
        simpa using mul_le_mul (Real.one_le_rpow hv1 hS0) (Real.one_le_rpow huv1 hA0)
          (by norm_num) (Real.rpow_nonneg (by positivity) S)
      have hXY : (0 : ℝ) ≤ (v : ℝ) ^ S * ((u * v : ℕ) : ℝ) ^ A * (H : ℝ) ^ B :=
        mul_nonneg (mul_nonneg (Real.rpow_nonneg hvpos.le S)
          (Real.rpow_nonneg (by positivity) A)) hHbb
      have hC : (1 : ℝ) ≤ 2 * (1 + CB) := by linarith only [hCB]
      calc (v : ℝ) ^ S * ((u * v : ℕ) : ℝ) ^ A * (H : ℝ) ^ B
          ≤ (2 * (1 + CB)) * ((v : ℝ) ^ S * ((u * v : ℕ) : ℝ) ^ A * (H : ℝ) ^ B) :=
            le_mul_of_one_le_left hXY hC
        _ = (2 * (1 + CB)) * (v : ℝ) ^ S * ((u * v : ℕ) : ℝ) ^ A * (H : ℝ) ^ B := by ring
    calc ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤ (H : ℝ) := hSbd
      _ = (H : ℝ) ^ (1 / (k : ℝ)) * (H : ℝ) ^ B := hsplit
      _ ≤ (v : ℝ) ^ (1 / (k : ℝ)) * (H : ℝ) ^ B :=
          mul_le_mul_of_nonneg_right hHk hHbb
      _ ≤ ((v : ℝ) ^ S * ((u * v : ℕ) : ℝ) ^ A) * (H : ℝ) ^ B :=
          mul_le_mul_of_nonneg_right hvv hHbb
      _ ≤ (2 * (1 + CB)) * (v : ℝ) ^ S * ((u * v : ℕ) : ℝ) ^ A * (H : ℝ) ^ B := hstep
  · -- case B: the interval is long; split into residue classes modulo `v`
    have hu2 : 2 ≤ u := by
      have h1 : v < u * v := lt_of_lt_of_le hHv hHq
      have h2 : v * 1 < v * u := by rw [mul_comm u v] at h1; rw [mul_one]; exact h1
      have h3 : 1 < u := Nat.lt_of_mul_lt_mul_left h2
      omega
    obtain ⟨χu, χv, hχu_prim, hχv_prim, hfac⟩ := primitive_factor_coprime hcop χ hprim
    have hχu1 : χu ≠ 1 := by
      intro h
      have hc := (DirichletCharacter.isPrimitive_def χu).mp hχu_prim
      rw [h, DirichletCharacter.conductor_one] at hc
      omega
    have hvu : v.Coprime u := hcop.symm
    obtain ⟨w, hwdef⟩ : ∃ w, w = ((((ZMod.unitOfCoprime v hvu)⁻¹ : (ZMod u)ˣ) :
        ZMod u).val) + u := ⟨_, rfl⟩
    have hwcast : ((w : ℕ) : ZMod u) =
        (((ZMod.unitOfCoprime v hvu)⁻¹ : (ZMod u)ˣ) : ZMod u) := by
      rw [hwdef, Nat.cast_add, ZMod.natCast_self, add_zero, ZMod.natCast_zmod_val]
    have hw : (w : ZMod u) * (v : ZMod u) = 1 := by
      have hcoe : ((v : ℕ) : ZMod u) = ((ZMod.unitOfCoprime v hvu : (ZMod u)ˣ) : ZMod u) :=
        ZMod.coe_unitOfCoprime v hvu
      rw [hwcast, hcoe, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hw1 : 1 ≤ w := by
      rw [hwdef]
      exact (le_trans (by norm_num : (1 : ℕ) ≤ 2) hu2).trans (Nat.le_add_left u _)
    have hIoc : Finset.Ioc N (N + H) = Finset.Icc (N + 1) (N + H) := by
      ext t; simp only [Finset.mem_Ioc, Finset.mem_Icc]; omega
    have hmin : min v (N + H) = v := by rw [min_eq_left]; omega
    rw [hIoc, interval_residue_decomp v N H (Nat.one_le_iff_ne_zero.mpr (NeZero.ne v))
      (fun n => χ ((n : ℕ) : ZMod (u * v))), hmin]
    have hterm : ∀ a ∈ Finset.Icc 1 v,
        ‖∑ m ∈ Finset.Icc ((N + v - a) / v) ((N + H - a) / v),
            χ (((a + v * m : ℕ)) : ZMod (u * v))‖
          ≤ (1 + CB) * (u : ℝ) ^ A
              * (((Finset.Icc ((N + v - a) / v) ((N + H - a) / v)).card : ℝ)) ^ B := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      obtain ⟨ha1, hav⟩ := ha
      have hpt : ∀ m : ℕ, χ (((a + v * m : ℕ)) : ZMod (u * v))
          = χu ((v : ℕ) : ZMod u)
              * χu (((w * (a % v) + (a + v * m) / v : ℕ)) : ZMod u)
              * χv ((a % v : ℕ) : ZMod v) := by
        intro m
        have h := char_decomp_pointwise hcop hfac hw (a + v * m)
        rw [Nat.add_mul_mod_self_left a v m] at h
        exact h
      have hbound : ‖∑ m ∈ Finset.Icc ((N + v - a) / v) ((N + H - a) / v),
              χ (((a + v * m : ℕ)) : ZMod (u * v))‖
          ≤ ‖∑ m ∈ Finset.Icc ((N + v - a) / v) ((N + H - a) / v),
              χu (((w * (a % v) + (a + v * m) / v : ℕ)) : ZMod u)‖ := by
        rw [Finset.sum_congr rfl (fun m _ => hpt m), ← Finset.sum_mul, ← Finset.mul_sum]
        calc ‖χu ((v : ℕ) : ZMod u)
              * (∑ m ∈ Finset.Icc ((N + v - a) / v) ((N + H - a) / v),
                  χu (((w * (a % v) + (a + v * m) / v : ℕ)) : ZMod u))
              * χv ((a % v : ℕ) : ZMod v)‖
            = ‖χu ((v : ℕ) : ZMod u)‖
              * ‖∑ m ∈ Finset.Icc ((N + v - a) / v) ((N + H - a) / v),
                  χu (((w * (a % v) + (a + v * m) / v : ℕ)) : ZMod u)‖
              * ‖χv ((a % v : ℕ) : ZMod v)‖ := by rw [norm_mul, norm_mul]
          _ ≤ 1 * ‖∑ m ∈ Finset.Icc ((N + v - a) / v) ((N + H - a) / v),
                  χu (((w * (a % v) + (a + v * m) / v : ℕ)) : ZMod u)‖ * 1 :=
              mul_le_mul
                (mul_le_mul (χu.norm_le_one _) le_rfl (norm_nonneg _) (by norm_num))
                (χv.norm_le_one _) (norm_nonneg _) (by positivity)
          _ = ‖∑ m ∈ Finset.Icc ((N + v - a) / v) ((N + H - a) / v),
                  χu (((w * (a % v) + (a + v * m) / v : ℕ)) : ZMod u)‖ := by ring
      exact hbound.trans (burgess_class_bound hε hk hCB hB hcube hχu_prim hχu1 hw1 hw
        hN ha1 hav hHv hHq)
    have hcard_le : ∀ a ∈ Finset.Icc 1 v,
        ((Finset.Icc ((N + v - a) / v) ((N + H - a) / v)).card : ℝ)
          ≤ 2 * (H : ℝ) / (v : ℝ) := by
      intro a ha
      rw [Finset.mem_Icc] at ha
      have h1 := card_Icc_div_le (v := v) (a := a) (N := N) (H := H)
        (Nat.pos_of_ne_zero (NeZero.ne v)) ha.2 hH
      have h2 : (1 : ℝ) ≤ (H : ℝ) / (v : ℝ) := by
        rw [one_le_div hvpos]
        exact_mod_cast le_of_lt hHv
      have h3 : 2 * (H : ℝ) / (v : ℝ) = 2 * ((H : ℝ) / (v : ℝ)) := by ring
      rw [h3]
      linarith only [h1, h2]
    have hsum_card : ∑ a ∈ Finset.Icc 1 v,
          ((Finset.Icc ((N + v - a) / v) ((N + H - a) / v)).card : ℝ) ^ B
        ≤ (v : ℝ) * (2 * (H : ℝ) / (v : ℝ)) ^ B := by
      calc ∑ a ∈ Finset.Icc 1 v,
            ((Finset.Icc ((N + v - a) / v) ((N + H - a) / v)).card : ℝ) ^ B
          ≤ ∑ _a ∈ Finset.Icc 1 v, (2 * (H : ℝ) / (v : ℝ)) ^ B :=
            Finset.sum_le_sum fun a ha =>
              Real.rpow_le_rpow (by positivity) (hcard_le a ha) hB0
        _ = ((Finset.Icc 1 v).card : ℝ) * (2 * (H : ℝ) / (v : ℝ)) ^ B := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = (v : ℝ) * (2 * (H : ℝ) / (v : ℝ)) ^ B := by
            rw [Nat.card_Icc]; norm_num
    have hvw : (v : ℝ) * (2 * (H : ℝ) / (v : ℝ)) ^ B
        ≤ 2 * (v : ℝ) ^ (1 / (k : ℝ)) * (H : ℝ) ^ B := by
      have hHR : (0 : ℝ) < (H : ℝ) := by exact_mod_cast (by omega : 0 < H)
      have e1 : (2 * (H : ℝ) / (v : ℝ)) ^ B
          = (2 : ℝ) ^ B * (H : ℝ) ^ B / (v : ℝ) ^ B := by
        rw [Real.div_rpow (by positivity) hvpos.le,
          Real.mul_rpow (by norm_num) hHR.le]
      have e2 : (2 : ℝ) ^ B ≤ 2 := by
        calc (2 : ℝ) ^ B ≤ (2 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) hB1
          _ = 2 := Real.rpow_one 2
      have hbr : (v : ℝ) / (v : ℝ) ^ B = (v : ℝ) ^ (1 - B) := by
        rw [div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos hvpos B)), ← Real.rpow_add hvpos,
          show (1 : ℝ) - B + B = 1 by ring, Real.rpow_one]
      have hvsub : (1 : ℝ) - B = 1 / (k : ℝ) := by rw [hB_def]; ring
      have hvBne : (v : ℝ) ^ B ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hvpos B)
      calc (v : ℝ) * (2 * (H : ℝ) / (v : ℝ)) ^ B
          = (v : ℝ) * ((2 : ℝ) ^ B * (H : ℝ) ^ B / (v : ℝ) ^ B) := by rw [e1]
        _ = (2 : ℝ) ^ B * (H : ℝ) ^ B * ((v : ℝ) / (v : ℝ) ^ B) := by
              field_simp
        _ = (2 : ℝ) ^ B * (H : ℝ) ^ B * (v : ℝ) ^ (1 - B) := by rw [hbr]
        _ = (2 : ℝ) ^ B * (H : ℝ) ^ B * (v : ℝ) ^ (1 / (k : ℝ)) := by rw [hvsub]
        _ ≤ 2 * (H : ℝ) ^ B * (v : ℝ) ^ (1 / (k : ℝ)) := by
              have hHnn : (0 : ℝ) ≤ (H : ℝ) ^ B := Real.rpow_nonneg hHR.le B
              have hvnn : (0 : ℝ) ≤ (v : ℝ) ^ (1 / (k : ℝ)) := Real.rpow_nonneg hvpos.le _
              have hXY : (0 : ℝ) ≤ (H : ℝ) ^ B * (v : ℝ) ^ (1 / (k : ℝ)) :=
                mul_nonneg hHnn hvnn
              calc (2 : ℝ) ^ B * (H : ℝ) ^ B * (v : ℝ) ^ (1 / (k : ℝ))
                  = (2 : ℝ) ^ B * ((H : ℝ) ^ B * (v : ℝ) ^ (1 / (k : ℝ))) := by ring
                _ ≤ 2 * ((H : ℝ) ^ B * (v : ℝ) ^ (1 / (k : ℝ))) :=
                    mul_le_mul_of_nonneg_right e2 hXY
                _ = 2 * (H : ℝ) ^ B * (v : ℝ) ^ (1 / (k : ℝ)) := by ring
        _ = 2 * (v : ℝ) ^ (1 / (k : ℝ)) * (H : ℝ) ^ B := by ring
    have hstep1 : ‖∑ a ∈ Finset.Icc 1 v,
          ∑ m ∈ Finset.Icc ((N + v - a) / v) ((N + H - a) / v),
            χ (((a + v * m : ℕ)) : ZMod (u * v))‖
        ≤ (1 + CB) * (u : ℝ) ^ A * ((v : ℝ) * (2 * (H : ℝ) / (v : ℝ)) ^ B) := by
      refine (norm_sum_le _ _).trans ?_
      have h1 : ∑ a ∈ Finset.Icc 1 v, (1 + CB) * (u : ℝ) ^ A
            * ((Finset.Icc ((N + v - a) / v) ((N + H - a) / v)).card : ℝ) ^ B
          = (1 + CB) * (u : ℝ) ^ A * ∑ a ∈ Finset.Icc 1 v,
              ((Finset.Icc ((N + v - a) / v) ((N + H - a) / v)).card : ℝ) ^ B := by
        rw [Finset.mul_sum]
      refine (Finset.sum_le_sum hterm).trans ?_
      rw [h1]
      exact mul_le_mul_of_nonneg_left hsum_card
        (mul_nonneg (by linarith only [hCB]) (Real.rpow_nonneg (by positivity) A))
    have hvw2 : (1 + CB) * (u : ℝ) ^ A * ((v : ℝ) * (2 * (H : ℝ) / (v : ℝ)) ^ B)
        ≤ (1 + CB) * (u : ℝ) ^ A * (2 * (v : ℝ) ^ (1 / (k : ℝ)) * (H : ℝ) ^ B) :=
      mul_le_mul_of_nonneg_left (hvw.trans (le_of_eq (by ring)))
        (mul_nonneg (by linarith only [hCB]) (Real.rpow_nonneg (by positivity) A))
    have hmid : (1 + CB) * (u : ℝ) ^ A * (2 * (v : ℝ) ^ (1 / (k : ℝ)) * (H : ℝ) ^ B)
        = (1 + CB) * ((u : ℝ) ^ A * 2) * (v : ℝ) ^ (1 / (k : ℝ)) * (H : ℝ) ^ B := by ring
    have hmid2 : (1 + CB) * ((u : ℝ) ^ A * 2) * (v : ℝ) ^ (1 / (k : ℝ)) * (H : ℝ) ^ B
        ≤ (1 + CB) * ((u : ℝ) ^ A * 2) * (v : ℝ) ^ ((1 : ℝ) / (k : ℝ) + ε)
            * (H : ℝ) ^ B := by
      refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by positivity) B)
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact Real.rpow_le_rpow_of_exponent_le hv1 (by linarith only [hε])
    have hfin : (1 + CB) * ((u : ℝ) ^ A * 2) * (v : ℝ) ^ ((1 : ℝ) / (k : ℝ) + ε)
          * (H : ℝ) ^ B
        = (2 * (1 + CB)) * (v : ℝ) ^ S * ((u * v : ℕ) : ℝ) ^ A * (H : ℝ) ^ B := by
      rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity), ← hexp,
        Real.rpow_add hvpos]
      ring
    linarith only [hstep1, hvw2, hmid.le, hmid.ge, hmid2, hfin.le, hfin.ge, hfin]


end Core

/-- **Burgess's bound for arbitrary moduli, deduced from the cube-free case.**
If the Burgess bound `‖∑ ψ(n)‖ ≤ CB · u^((k+1)/(4k²)+ε) · H^(1-1/k)` holds uniformly for all
primitive characters `ψ` of cube-free modulus `u`, then for every primitive character `χ` of
arbitrary modulus `q` one has the same bound with the extra factor
`v^((3k-1)/(4k²))`, where `v = ∏_{p : v_p(q) ≥ 3} p^v_p(q)` is the product of the full prime
powers of `q` at the primes with exponent at least `3`. -/
theorem burgess_charSum_v_of_cubefree {ε : ℝ} (hε : 0 < ε) (k : ℕ) (hk : 2 ≤ k)
    {CB : ℝ} (hCB : 0 < CB)
    (hB : ∀ {u : ℕ} [NeZero u] (ψ : DirichletCharacter ℂ u), ψ.IsPrimitive → ψ ≠ 1 →
      (∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ u) →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ u →
        ‖∑ n ∈ Finset.Ioc N (N + H), ψ n‖ ≤
          CB * (u : ℝ) ^ (((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2) + ε)
            * (H : ℝ) ^ (1 - 1 / (k : ℝ))) :
    ∃ C : ℝ, 0 < C ∧ ∀ {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q),
        χ.IsPrimitive → χ ≠ 1 →
      ∀ {N H : ℕ}, 1 ≤ N → 1 ≤ H → H ≤ q →
        ‖∑ n ∈ Finset.Ioc N (N + H), χ n‖ ≤
          C * (((∏ p ∈ q.primeFactors.filter (fun p => 3 ≤ q.factorization p),
                    p ^ q.factorization p) : ℕ) : ℝ)
                ^ ((3 * (k : ℝ) - 1) / (4 * (k : ℝ) ^ 2))
            * (q : ℝ) ^ (((k : ℝ) + 1) / (4 * (k : ℝ) ^ 2) + ε)
            * (H : ℝ) ^ (1 - 1 / (k : ℝ)) := by
  refine ⟨2 * (1 + CB), by linarith only [hCB], ?_⟩
  intro q _ χ hprim hne N H hN hH hHq
  have hq0 : q ≠ 0 := NeZero.ne q
  have hcop : (cubeFreePart q).Coprime (cubefulPart q) :=
    (cubefulPart_coprime_cubeFreePart q hq0).symm
  have hcube : ∀ p : ℕ, p.Prime → ¬ p ^ 3 ∣ cubeFreePart q :=
    fun p hp => cubeFreePart_cube_free q p hp
  haveI : NeZero (cubeFreePart q) := ⟨ne_of_gt (cubeFreePart_pos q)⟩
  haveI : NeZero (cubefulPart q) := ⟨ne_of_gt (cubefulPart_pos q)⟩
  exact burgess_v_aux (u := cubeFreePart q) (v := cubefulPart q)
    (cubeFreePart_mul_cubefulPart q hq0).symm hcop hcube hε hk hCB hB χ hprim hne hN hH hHq

end Commons.NumberTheory.DirichletCharacter
