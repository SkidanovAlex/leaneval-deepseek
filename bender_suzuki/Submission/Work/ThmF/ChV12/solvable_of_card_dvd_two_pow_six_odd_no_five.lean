import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Solvability of odd-order groups of order dividing `20158709760` without a factor `5`

The number `20158709760` factors as `2^15 * 3^4 * 5 * 7^2 * 31`.  Hence a finite group `D` of odd
order whose order divides `20158709760` and is not divisible by `5` has order dividing
`3^4 * 7^2 * 31 = 123039`.

Every group of order dividing `123039` is solvable, and this is proved here by elementary
Sylow counting, *without* the Feit–Thompson odd order theorem:

* If `7 ∣ |D|`, the number `n_7` of Sylow `7`-subgroups satisfies `n_7 ≡ 1 [MOD 7]` and
  `n_7 ∣ 3^4 * 31` (the `7`-part of the index is killed by the congruence), and a finite check
  shows `1` is the only divisor of `3^4 * 31` congruent to `1` mod `7`.  So `n_7 = 1`, the Sylow
  `7`-subgroup is normal, and `D` is an extension of a `7`-group by a group of order dividing
  `3^4 * 31`.
* A group of order dividing `3^4 * 31` either has a normal Sylow `31`-subgroup (same counting,
  `n_31 ∣ 3^4` and `n_31 ≡ 1 [MOD 31]`, again only `n_31 = 1` is possible), making it an extension
  of a cyclic group of order `31` by a `3`-group, or is itself a `3`-group.

A `p`-group is nilpotent, hence solvable, and an extension of solvable groups is solvable.
-/

namespace Work.ThmF.ChV12

set_option maxRecDepth 100000
set_option linter.style.haveILetI false

/-- If `d` divides `a * p ^ k` with `p` a prime not dividing `d`, then `d` divides `a`. -/
lemma dvd_of_dvd_mul_prime_pow {d a p k : ℕ} (hp : p.Prime) (hm : ¬ p ∣ d)
    (h : d ∣ a * p ^ k) : d ∣ a := by
  have hcop : d.Coprime (p ^ k) := ((hp.coprime_iff_not_dvd.mpr hm).symm).pow_right k
  rw [mul_comm] at h
  exact hcop.dvd_of_dvd_mul_left h

/-- A finite `p`-group is solvable (it is nilpotent). -/
lemma isSolvable_of_isPGroup {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    (h : IsPGroup p G) : Group.IsSolvable G := by
  haveI := IsPGroup.isNilpotent h
  infer_instance

/-- The only divisor of `3^4 * 31` congruent to `1` modulo `7` is `1`. -/
lemma count7 (n : ℕ) (hdvd : n ∣ 3^4 * 31) (hmod : n ≡ 1 [MOD 7]) : n = 1 := by
  have hmem : n ∈ Nat.divisors (3^4 * 31) := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hkey : (Nat.divisors (3^4 * 31)).filter (fun n => n % 7 = 1 % 7) = {1} := by decide
  have : n ∈ (Nat.divisors (3^4 * 31)).filter (fun n => n % 7 = 1 % 7) := by
    simp only [Finset.mem_filter]; exact ⟨hmem, hmod⟩
  rw [hkey] at this; simpa using this

/-- The only divisor of `3^4` congruent to `1` modulo `31` is `1`. -/
lemma count31 (n : ℕ) (hdvd : n ∣ 3^4) (hmod : n ≡ 1 [MOD 31]) : n = 1 := by
  have hmem : n ∈ Nat.divisors (3^4) := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
  have hkey : (Nat.divisors (3^4)).filter (fun n => n % 31 = 1 % 31) = {1} := by decide
  have : n ∈ (Nat.divisors (3^4)).filter (fun n => n % 31 = 1 % 31) := by
    simp only [Finset.mem_filter]; exact ⟨hmem, hmod⟩
  rw [hkey] at this; simpa using this

/-- A group of order dividing `3^4 * 7^2 * 31` has a unique (hence normal) Sylow `7`-subgroup. -/
lemma sylow7_card_eq_one {G : Type*} [Group G] [Finite G]
    (hdvd : Nat.card G ∣ 3^4 * 7^2 * 31) : Nat.card (Sylow 7 G) = 1 := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨P⟩ := Sylow.nonempty (p := 7) (G := G)
  have hmod : Nat.card (Sylow 7 G) ≡ 1 [MOD 7] := card_sylow_modEq_one 7 G
  have hdvd' : Nat.card (Sylow 7 G) ∣ 3^4 * 7^2 * 31 :=
    (P.card_dvd_index.trans (Subgroup.index_dvd_card _)).trans hdvd
  have hnot : ¬ 7 ∣ Nat.card (Sylow 7 G) := by
    intro h
    have h0 : Nat.card (Sylow 7 G) % 7 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
    rw [hmod] at h0; norm_num at h0
  have hdvd'' : Nat.card (Sylow 7 G) ∣ 3^4 * 31 := by
    refine dvd_of_dvd_mul_prime_pow (p := 7) (k := 2) (by norm_num) hnot ?_
    simpa [mul_assoc, mul_left_comm, mul_comm] using hdvd'
  exact count7 _ hdvd'' hmod

/-- A group of order dividing `3^4 * 31` has a unique (hence normal) Sylow `31`-subgroup. -/
lemma sylow31_card_eq_one {G : Type*} [Group G] [Finite G]
    (hdvd : Nat.card G ∣ 3^4 * 31) : Nat.card (Sylow 31 G) = 1 := by
  haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
  obtain ⟨P⟩ := Sylow.nonempty (p := 31) (G := G)
  have hmod : Nat.card (Sylow 31 G) ≡ 1 [MOD 31] := card_sylow_modEq_one 31 G
  have hdvd' : Nat.card (Sylow 31 G) ∣ 3^4 * 31 :=
    (P.card_dvd_index.trans (Subgroup.index_dvd_card _)).trans hdvd
  have hnot : ¬ 31 ∣ Nat.card (Sylow 31 G) := by
    intro h
    have h0 : Nat.card (Sylow 31 G) % 31 = 0 := Nat.dvd_iff_mod_eq_zero.mp h
    rw [hmod] at h0; norm_num at h0
  have hdvd'' : Nat.card (Sylow 31 G) ∣ 3^4 := by
    refine dvd_of_dvd_mul_prime_pow (p := 31) (k := 1) (by norm_num) hnot ?_
    simpa using hdvd'
  exact count31 _ hdvd'' hmod

/-- Every finite group of order dividing `3^4 * 31` is solvable. -/
theorem solvable_of_card_dvd_3pow4_mul31 {D : Type*} [Group D] [Finite D]
    (hdvd : Nat.card D ∣ 3^4 * 31) : Group.IsSolvable D := by
  by_cases h31 : 31 ∣ Nat.card D
  · haveI : Fact (Nat.Prime 31) := ⟨by norm_num⟩
    obtain ⟨P⟩ := Sylow.nonempty (p := 31) (G := D)
    have hcard := sylow31_card_eq_one hdvd
    haveI : Subsingleton (Sylow 31 D) := (Nat.card_eq_one_iff_unique.mp hcard).1
    haveI hnorm : (P : Subgroup D).Normal := P.normal_of_subsingleton
    have hq : Nat.card (D ⧸ (P : Subgroup D)) ∣ 3^4 := by
      have h1 : Nat.card (D ⧸ (P : Subgroup D)) ∣ Nat.card D := by
        rw [← Subgroup.index_eq_card]; exact Subgroup.index_dvd_card _
      have h2 : Nat.card (D ⧸ (P : Subgroup D)) ∣ 3^4 * 31 := h1.trans hdvd
      have hnot : ¬ 31 ∣ Nat.card (D ⧸ (P : Subgroup D)) := by
        rw [← Subgroup.index_eq_card]; exact P.not_dvd_index
      refine dvd_of_dvd_mul_prime_pow (p := 31) (k := 1) (by norm_num) hnot ?_
      simpa using h2
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    haveI : Group.IsSolvable (D ⧸ (P : Subgroup D)) :=
      isSolvable_of_isPGroup (IsPGroup.of_card_dvd_pow (p := 3) (n := 4) hq)
    haveI : Group.IsSolvable ↥(P : Subgroup D) := isSolvable_of_isPGroup (p := 31) P.isPGroup'
    exact Group.isSolvable_of_subgroup_quotient (P : Subgroup D)
  · have hdvd3 : Nat.card D ∣ 3^4 := by
      refine dvd_of_dvd_mul_prime_pow (p := 31) (k := 1) (by norm_num) h31 ?_
      simpa using hdvd
    haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    exact isSolvable_of_isPGroup (IsPGroup.of_card_dvd_pow (p := 3) (n := 4) hdvd3)

/-- Every finite group of order dividing `3^4 * 7^2 * 31 = 123039` is solvable. -/
theorem solvable_of_card_dvd_123039 {D : Type*} [Group D] [Finite D]
    (hdvd : Nat.card D ∣ 3^4 * 7^2 * 31) : Group.IsSolvable D := by
  by_cases h7 : 7 ∣ Nat.card D
  · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    obtain ⟨P⟩ := Sylow.nonempty (p := 7) (G := D)
    have hcard := sylow7_card_eq_one hdvd
    haveI : Subsingleton (Sylow 7 D) := (Nat.card_eq_one_iff_unique.mp hcard).1
    haveI hnorm : (P : Subgroup D).Normal := P.normal_of_subsingleton
    have hq : Nat.card (D ⧸ (P : Subgroup D)) ∣ 3^4 * 31 := by
      have h1 : Nat.card (D ⧸ (P : Subgroup D)) ∣ Nat.card D := by
        rw [← Subgroup.index_eq_card]; exact Subgroup.index_dvd_card _
      have h2 : Nat.card (D ⧸ (P : Subgroup D)) ∣ 3^4 * 7^2 * 31 := h1.trans hdvd
      have hnot : ¬ 7 ∣ Nat.card (D ⧸ (P : Subgroup D)) := by
        rw [← Subgroup.index_eq_card]; exact P.not_dvd_index
      refine dvd_of_dvd_mul_prime_pow (p := 7) (k := 2) (by norm_num) hnot ?_
      simpa [mul_assoc, mul_left_comm, mul_comm] using h2
    haveI : Group.IsSolvable (D ⧸ (P : Subgroup D)) := solvable_of_card_dvd_3pow4_mul31 hq
    haveI : Group.IsSolvable ↥(P : Subgroup D) := isSolvable_of_isPGroup (p := 7) P.isPGroup'
    exact Group.isSolvable_of_subgroup_quotient (P : Subgroup D)
  · have hdvd' : Nat.card D ∣ 3^4 * 31 := by
      refine dvd_of_dvd_mul_prime_pow (p := 7) (k := 2) (by norm_num) h7 ?_
      simpa [mul_assoc, mul_left_comm, mul_comm] using hdvd
    exact solvable_of_card_dvd_3pow4_mul31 hdvd'

/-- A finite group of odd order dividing `20158709760` and not divisible by `5` is solvable.

Indeed `20158709760 = 2^15 * 3^4 * 5 * 7^2 * 31`, so such a group has order dividing
`3^4 * 7^2 * 31`. -/
theorem solvable_of_card_dvd_two_pow_six_odd_no_five {D : Type} [Group D] [Finite D]
    (hodd : Odd (Nat.card D)) (hdvd : Nat.card D ∣ 20158709760)
    (h5 : ¬ 5 ∣ Nat.card D) : Group.IsSolvable D := by
  apply solvable_of_card_dvd_123039
  have h1 : Nat.card D ∣ 2^15 * (3^4 * 5 * 7^2 * 31) := by
    have hnum : (20158709760 : ℕ) = 2^15 * (3^4 * 5 * 7^2 * 31) := by norm_num
    rwa [hnum] at hdvd
  have hodd2 : ¬ 2 ∣ Nat.card D := by
    have hne : ¬ Even (Nat.card D) := Nat.not_even_iff_odd.mpr hodd
    rwa [even_iff_two_dvd] at hne
  have h2 : Nat.card D ∣ 3^4 * 5 * 7^2 * 31 := by
    refine dvd_of_dvd_mul_prime_pow (p := 2) (k := 15) (by norm_num) hodd2 ?_
    simpa [mul_assoc, mul_left_comm, mul_comm] using h1
  refine dvd_of_dvd_mul_prime_pow (p := 5) (k := 1) (by norm_num) h5 ?_
  simpa [mul_assoc, mul_left_comm, mul_comm] using h2

end Work.ThmF.ChV12
