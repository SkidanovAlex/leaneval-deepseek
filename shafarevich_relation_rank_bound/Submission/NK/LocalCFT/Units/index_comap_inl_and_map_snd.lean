import Mathlib

/-!
# Splitting the index of a subgroup of `A × B` along the two factors

Let `A` and `B` be commutative groups with `A` of exponent dividing `p ^ e` and `B` of exponent
dividing `m`, where `p ^ e` and `m` are coprime.  For a subgroup `K ≤ A × B` of index `p ^ e * m`
we show that the two projections of `K` have the expected indices:

* `(K.comap (MonoidHom.inl A B)).index = p ^ e`, i.e. `K ∩ (A × 1)` has index `p ^ e` in `A`, and
* `(K.map (MonoidHom.snd A B)).index = m`, i.e. the image of `K` in `B` has index `m` in `B`.

The proof has two halves.

**Group theory.**  Writing `P = (MonoidHom.inl A B).range = A × 1` (also the kernel of `snd`), the
index is multiplicative in the tower `K ≤ K ⊔ P ≤ A × B`:

  `[A × B : K] = [A × B : K ⊔ P] · [K ⊔ P : K]`.

Now `[A × B : K ⊔ P] = [B : K.map snd]` because `(A × B)/(K ⊔ P) ≅ B/(K.map snd)`, and
`[K ⊔ P : K] = [A : K.comap inl]` because `(K ⊔ P)/K ≅ P/(P ⊓ K) ≅ A/(K.comap inl)`.  In Lean
both substitutions are the library identities `Subgroup.index_map` and `Subgroup.index_comap`
combined with `Subgroup.relIndex_sup_right`; no subgroup-lattice isomorphism is needed.

**Number theory.**  The quotients `A ⧸ K.comap inl` and `B ⧸ K.map snd` inherit the exponents
`p ^ e` and `m`, so by Cauchy's theorem every prime dividing their orders divides `p ^ e`
(resp. `m`).  With the multiplicativity established above, an elementary arithmetic argument
(`num_lemma`) then forces the orders to be `p ^ e` and `m`; the degenerate cases `p ^ e = 0` and
`m = 0` are handled separately, where coprimality forces `m = 1` (resp. `p ^ e = 1`) and the
corresponding group is trivial.
-/

set_option linter.style.haveILetI false

namespace NK.LocalCFT.Units

/-- A purely arithmetic lemma: if `a * b = P * M`, `P` and `M` are coprime, and every prime
dividing `a` (resp. `b`) also divides `P` (resp. `M`), then `a = P` and `b = M`.

Indeed the prime divisors of `a` are coprime to `M` and those of `b` are coprime to `P`, so
`a ∣ P` and `b ∣ M`; a product comparison then finishes. -/
lemma num_lemma {a b P M : ℕ} (hP : P ≠ 0) (hM : M ≠ 0)
    (hprod : a * b = P * M) (hcop : P.Coprime M)
    (ha : ∀ q, q.Prime → q ∣ a → q ∣ P) (hb : ∀ q, q.Prime → q ∣ b → q ∣ M) :
    a = P ∧ b = M := by
  have hPM : P * M ≠ 0 := mul_ne_zero hP hM
  have ha0 : a ≠ 0 := fun h => hPM (by rw [← hprod, h, zero_mul])
  have hb0 : b ≠ 0 := fun h => hPM (by rw [← hprod, h, mul_zero])
  have hcaM : a.Coprime M := by
    by_contra h
    have hg : a.gcd M ≠ 1 := h
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hg
    have hqa : q ∣ a := hqdvd.trans (Nat.gcd_dvd_left a M)
    have hqM : q ∣ M := hqdvd.trans (Nat.gcd_dvd_right a M)
    have hqP : q ∣ P := ha q hq hqa
    have : q ∣ 1 := by rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd hqP hqM
    exact hq.ne_one (Nat.dvd_one.mp this)
  have hcbP : b.Coprime P := by
    by_contra h
    have hg : b.gcd P ≠ 1 := h
    obtain ⟨q, hq, hqdvd⟩ := Nat.exists_prime_and_dvd hg
    have hqb : q ∣ b := hqdvd.trans (Nat.gcd_dvd_left b P)
    have hqP : q ∣ P := hqdvd.trans (Nat.gcd_dvd_right b P)
    have hqM : q ∣ M := hb q hq hqb
    have : q ∣ 1 := by rw [← hcop.gcd_eq_one]; exact Nat.dvd_gcd hqP hqM
    exact hq.ne_one (Nat.dvd_one.mp this)
  have ha_dvd : a ∣ P := hcaM.dvd_of_dvd_mul_right (by rw [← hprod]; exact dvd_mul_right a b)
  have hb_dvd : b ∣ M := hcbP.dvd_of_dvd_mul_left (by rw [← hprod]; exact dvd_mul_left b a)
  obtain ⟨x, hx⟩ := ha_dvd
  obtain ⟨y, hy⟩ := hb_dvd
  have hab : a * b ≠ 0 := mul_ne_zero ha0 hb0
  have h1 : a * b * 1 = a * b * (x * y) := by
    rw [mul_one]
    calc a * b = P * M := hprod
      _ = a * x * (b * y) := by rw [hx, hy]
      _ = a * b * (x * y) := by ring
  have hxy : x * y = 1 := (Nat.mul_left_cancel (Nat.pos_of_ne_zero hab) h1).symm
  exact ⟨by rw [hx, Nat.eq_one_of_mul_eq_one_right hxy, mul_one],
         by rw [hy, Nat.eq_one_of_mul_eq_one_left hxy, mul_one]⟩

/-- Cauchy's theorem in the form needed below: if every element of a finite group `G` satisfies
`x ^ n = 1`, then every prime `q` dividing the order of `G` divides `n`. -/
lemma prime_dvd_of_pow_eq_one {G : Type*} [Group G] [Finite G] {n q : ℕ}
    (h : ∀ x : G, x ^ n = 1) (hq : q.Prime) (hdvd : q ∣ Nat.card G) : q ∣ n := by
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' q hdvd
  rw [← hx]
  exact orderOf_dvd_of_pow_eq_one (h x)

theorem index_comap_inl_and_map_snd {A B : Type*} [CommGroup A] [CommGroup B]
    {p e m : ℕ} (hA : ∀ x : A, x ^ (p ^ e) = 1) (hB : ∀ x : B, x ^ m = 1) (hcop : (p ^ e).Coprime m)
    (K : Subgroup (A × B)) (hK : K.index = p ^ e * m) :
    (K.comap (MonoidHom.inl A B)).index = p ^ e ∧ (K.map (MonoidHom.snd A B)).index = m := by
  -- `P = A × 1` is both the kernel of `snd` and the range of `inl`
  have hker : (MonoidHom.snd A B).ker = (MonoidHom.inl A B).range := by
    ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have hx' : x.2 = 1 := hx
      rw [MonoidHom.mem_range]
      exact ⟨x.1, Prod.ext rfl hx'.symm⟩
    · rintro ⟨a, rfl⟩
      rw [MonoidHom.mem_ker]
      rfl
  have hrange : (MonoidHom.snd A B).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (fun b => ⟨(1, b), rfl⟩)
  -- the index is multiplicative in the tower `K ≤ K ⊔ P ≤ A × B`
  have hprod : K.index =
      (K.comap (MonoidHom.inl A B)).index * (K.map (MonoidHom.snd A B)).index := by
    rw [Subgroup.index_comap, Subgroup.index_map, hker, hrange, Subgroup.index_top, mul_one]
    have h1 := Subgroup.relIndex_mul_index (H := K)
      (K := K ⊔ (MonoidHom.inl A B).range) le_sup_left
    have h2 : K.relIndex (K ⊔ (MonoidHom.inl A B).range)
        = K.relIndex (MonoidHom.inl A B).range := by
      have h3 := Subgroup.relIndex_sup_right (H := (MonoidHom.inl A B).range) (K := K)
      rwa [sup_comm] at h3
    rw [← h1, h2]
  have hpk : (K.comap (MonoidHom.inl A B)).index * (K.map (MonoidHom.snd A B)).index
      = p ^ e * m := by rw [← hprod, hK]
  rcases eq_or_ne (p ^ e) 0 with hp0 | hp0
  · -- `p ^ e = 0`: coprimality forces `m = 1`, so `B` is trivial and its image is everything
    have hm1 : m = 1 := by
      have hc := hcop
      rw [hp0] at hc
      exact (Nat.coprime_zero_left m).mp hc
    have hBtriv : ∀ x : B, x = 1 := fun x => by simpa [hm1] using hB x
    have hKB : K.map (MonoidHom.snd A B) = ⊤ :=
      le_antisymm le_top fun x _ => by
        rw [hBtriv x]; exact (K.map (MonoidHom.snd A B)).one_mem
    have hb : (K.map (MonoidHom.snd A B)).index = 1 := by rw [hKB, Subgroup.index_top]
    have ha : (K.comap (MonoidHom.inl A B)).index = 0 := by
      have h := hpk
      rw [hb, mul_one, hp0, zero_mul] at h
      exact h
    exact ⟨by rw [ha, hp0], by rw [hb, hm1]⟩
  · rcases eq_or_ne m 0 with hm0 | hm0
    · -- `m = 0`: coprimality forces `p ^ e = 1`, so `A` is trivial and its preimage is everything
      have hp1 : p ^ e = 1 := by
        have hc := hcop
        rw [hm0] at hc
        exact (Nat.coprime_zero_right (p ^ e)).mp hc
      have hAtriv : ∀ x : A, x = 1 := fun x => by simpa [hp1] using hA x
      have hKA : K.comap (MonoidHom.inl A B) = ⊤ :=
        le_antisymm le_top fun x _ => by
          rw [hAtriv x]; exact (K.comap (MonoidHom.inl A B)).one_mem
      have ha : (K.comap (MonoidHom.inl A B)).index = 1 := by rw [hKA, Subgroup.index_top]
      have hb : (K.map (MonoidHom.snd A B)).index = 0 := by
        have h := hpk
        rw [ha, one_mul, hm0, mul_zero] at h
        exact h
      exact ⟨by rw [ha, hp1], by rw [hb, hm0]⟩
    · -- both factors nonzero: Cauchy + arithmetic
      have hn : p ^ e * m ≠ 0 := mul_ne_zero hp0 hm0
      have ha0 : (K.comap (MonoidHom.inl A B)).index ≠ 0 :=
        fun h => hn (by rw [← hpk, h, zero_mul])
      have hb0 : (K.map (MonoidHom.snd A B)).index ≠ 0 :=
        fun h => hn (by rw [← hpk, h, mul_zero])
      have hca : ∀ q, q.Prime → q ∣ (K.comap (MonoidHom.inl A B)).index → q ∣ p ^ e := by
        intro q hq hqdvd
        haveI : Finite (A ⧸ K.comap (MonoidHom.inl A B)) :=
          Subgroup.index_ne_zero_iff_finite.mp ha0
        have hexp : ∀ x : A ⧸ (K.comap (MonoidHom.inl A B)), x ^ (p ^ e) = 1 := by
          intro x
          obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (K.comap (MonoidHom.inl A B)) x
          rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hA y]
          exact (K.comap (MonoidHom.inl A B)).one_mem
        exact prime_dvd_of_pow_eq_one hexp hq hqdvd
      have hcb : ∀ q, q.Prime → q ∣ (K.map (MonoidHom.snd A B)).index → q ∣ m := by
        intro q hq hqdvd
        haveI : Finite (B ⧸ K.map (MonoidHom.snd A B)) :=
          Subgroup.index_ne_zero_iff_finite.mp hb0
        have hexp : ∀ x : B ⧸ (K.map (MonoidHom.snd A B)), x ^ m = 1 := by
          intro x
          obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (K.map (MonoidHom.snd A B)) x
          rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hB y]
          exact (K.map (MonoidHom.snd A B)).one_mem
        exact prime_dvd_of_pow_eq_one hexp hq hqdvd
      exact num_lemma hp0 hm0 hpk hcop hca hcb

end NK.LocalCFT.Units
