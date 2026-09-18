import Mathlib.Data.Nat.Totient

open scoped Nat

namespace Commons.Data.Nat

/-- The inverse of a unit of `ZMod n` is again a unit. -/
private lemma zmod_isUnit_inv {n : ℕ} (a : ZMod n) (h : IsUnit a) : IsUnit a⁻¹ := by
  refine ⟨⟨a⁻¹, a, ?_, ?_⟩, rfl⟩
  · exact ZMod.inv_mul_of_unit a h
  · exact ZMod.mul_inv_of_unit a h

/-- Coprimality `u.gcd n = 1` is equivalent to `u` being a unit modulo `n`. -/
private lemma gcd_eq_one_iff_isUnit (u n : ℕ) : u.gcd n = 1 ↔ IsUnit (u : ZMod n) := by
  constructor
  · intro h
    exact (ZMod.isUnit_iff_coprime u n).mpr (Nat.coprime_iff_gcd_eq_one.mpr h)
  · intro h
    exact Nat.coprime_iff_gcd_eq_one.mp ((ZMod.isUnit_iff_coprime u n).mp h)

/-- If `u` is coprime to `p ^ t` (`t > 0`), then `p` does not divide `u`. -/
private lemma not_dvd_of_gcd_prime_pow (p t u : ℕ) (hp : p.Prime) (ht : 0 < t)
    (hgcd : u.gcd (p ^ t) = 1) : ¬ p ∣ u := by
  have hu : IsUnit (u : ZMod (p ^ t)) := (gcd_eq_one_iff_isUnit u (p ^ t)).mp hgcd
  exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp ht (a := u)).mp hu

/-- A number coprime to `p` is a unit modulo a prime power with positive exponent. -/
private lemma isUnit_R (p d R : ℕ) (hp : p.Prime) (hd : 0 < d) (hR : ¬ p ∣ R) :
    IsUnit (R : ZMod (p ^ d)) := by
  exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp hd (a := R)).mpr hR

/-- When `p ∣ e` no pair satisfies the congruence: the residue of the right hand side is `0`
modulo `p` while the left hand side `u·R` is coprime to `p`. -/
private lemma card_eq_zero_of_prime_dvd (p a b R S e : ℕ) (hp : p.Prime) (hb : 0 < b)
    (hR : ¬ p ∣ R) (he : p ∣ e) :
    (((Finset.product (Finset.range (p ^ (a + b))) (Finset.range (p ^ a))).filter
      (fun uv : ℕ × ℕ => uv.1.gcd (p ^ (a + b)) = 1 ∧ uv.2.gcd (p ^ a) = 1 ∧
        ((uv.1 * R) % (p ^ (a + b)) = ((uv.2 * (p ^ b * S) + e) % (p ^ (a + b)))))).card) = 0 := by
  classical
  let M := p ^ (a + b)
  have hMpos : 0 < a + b := by omega
  have hpM : p ∣ M := by
    dsimp [M]
    simpa using (pow_dvd_pow p (show 1 ≤ a + b by omega) : p ^ 1 ∣ p ^ (a + b))
  have hfilter : (Finset.product (Finset.range M) (Finset.range (p ^ a))).filter
      (fun uv : ℕ × ℕ => uv.1.gcd M = 1 ∧ uv.2.gcd (p ^ a) = 1 ∧
        ((uv.1 * R) % M = ((uv.2 * (p ^ b * S) + e) % M))) = ∅ := by
    ext uv
    constructor
    · intro huv
      rw [Finset.mem_filter] at huv
      rcases huv with ⟨huvmem, hcond⟩
      rcases hcond with ⟨hgcd1, hgcd2, hcong⟩
      have hgcd1' : uv.1.gcd (p ^ (a + b)) = 1 := by simpa [M] using hgcd1
      have hpnd : ¬ p ∣ uv.1 := not_dvd_of_gcd_prime_pow p (a + b) uv.1 hp hMpos hgcd1'
      have hcongp : (uv.1 * R) % p = (uv.2 * (p ^ b * S) + e) % p := by
        calc
          (uv.1 * R) % p = ((uv.1 * R) % M) % p := by
            rw [← Nat.mod_mod_of_dvd (uv.1 * R) hpM]
          _ = ((uv.2 * (p ^ b * S) + e) % M) % p := by rw [hcong]
          _ = (uv.2 * (p ^ b * S) + e) % p := Nat.mod_mod_of_dvd (uv.2 * (p ^ b * S) + e) hpM
      have hpb : p ∣ p ^ b := by
        simpa using (pow_dvd_pow p (show 1 ≤ b by omega) : p ^ 1 ∣ p ^ b)
      have hpbs : p ∣ p ^ b * S := by
        rcases hpb with ⟨k, hk⟩
        refine ⟨k * S, ?_⟩
        calc
          p ^ b * S = (p * k) * S := by rw [hk]
          _ = p * (k * S) := by ring
      have hpv : p ∣ uv.2 * (p ^ b * S) := by
        rcases hpbs with ⟨k, hk⟩
        refine ⟨uv.2 * k, ?_⟩
        calc
          uv.2 * (p ^ b * S) = uv.2 * (p * k) := by rw [hk]
          _ = p * (uv.2 * k) := by ring
      have hpe2 : p ∣ uv.2 * (p ^ b * S) + e := (Nat.dvd_add_iff_left he).mp hpv
      have hy0 : (uv.2 * (p ^ b * S) + e) % p = 0 := Nat.mod_eq_zero_of_dvd hpe2
      have hx0 : (uv.1 * R) % p = 0 := by
        rw [hcongp, hy0]
      have hpx : p ∣ uv.1 * R := Nat.dvd_iff_mod_eq_zero.mpr hx0
      have hpR : p ∣ R := (hp.dvd_mul.mp hpx).resolve_left hpnd
      exact False.elim (hR hpR)
    · intro hmem
      simp at hmem
  calc
    (((Finset.product (Finset.range (p ^ (a + b))) (Finset.range (p ^ a))).filter
      (fun uv : ℕ × ℕ => uv.1.gcd (p ^ (a + b)) = 1 ∧ uv.2.gcd (p ^ a) = 1 ∧
        ((uv.1 * R) % (p ^ (a + b)) = ((uv.2 * (p ^ b * S) + e) % (p ^ (a + b)))))).card)
        = ((Finset.product (Finset.range M) (Finset.range (p ^ a))).filter
      (fun uv : ℕ × ℕ => uv.1.gcd M = 1 ∧ uv.2.gcd (p ^ a) = 1 ∧
        ((uv.1 * R) % M = ((uv.2 * (p ^ b * S) + e) % M)))).card := by
          simpa [M]
    _ = 0 := by rw [hfilter]; simp

/-- Step A: the natural count over ranges equals the count of the corresponding ZMod pairs. -/
private lemma nat_card_eq_zmod_card (p a b R S e : ℕ) (hp : p.Prime)
    [NeZero (p ^ (a + b))] [NeZero (p ^ a)] :
    (((Finset.product (Finset.range (p ^ (a + b))) (Finset.range (p ^ a))).filter
      (fun uv : ℕ × ℕ => uv.1.gcd (p ^ (a + b)) = 1 ∧ uv.2.gcd (p ^ a) = 1 ∧
        ((uv.1 * R) % (p ^ (a + b)) = ((uv.2 * (p ^ b * S) + e) % (p ^ (a + b)))))).card) =
    Fintype.card {z : ZMod (p ^ (a + b)) × ZMod (p ^ a) //
      IsUnit z.1 ∧ IsUnit z.2 ∧
        z.1 * (R : ZMod (p ^ (a + b))) = ((z.2.val * (p ^ b * S) + e : ℕ) : ZMod (p ^ (a + b)))} := by
  classical
  let M := p ^ (a + b)
  let N := p ^ a
  have hM0 : 0 < M := by dsimp [M]; exact pow_pos hp.pos (a + b)
  have hN0 : 0 < N := by dsimp [N]; exact pow_pos hp.pos a
  let Pz : ZMod M × ZMod N → Prop := fun z =>
    IsUnit z.1 ∧ IsUnit z.2 ∧
      z.1 * (R : ZMod M) = ((z.2.val * (p ^ b * S) + e : ℕ) : ZMod M)
  let D := (Finset.product (Finset.range M) (Finset.range N)).filter
      (fun uv : ℕ × ℕ => uv.1.gcd M = 1 ∧ uv.2.gcd N = 1 ∧
        ((uv.1 * R) % M = ((uv.2 * (p ^ b * S) + e) % M)))
  let ZZ := (Finset.univ : Finset (ZMod M × ZMod N)).filter Pz
  have hmem_units_gcd : ∀ (m : ℕ), IsUnit (m : ZMod M) ↔ m.gcd M = 1 := by
    intro m
    exact (gcd_eq_one_iff_isUnit m M).symm
  have hmem_units_gcd2 : ∀ (m : ℕ), IsUnit (m : ZMod N) ↔ m.gcd N = 1 := by
    intro m
    exact (gcd_eq_one_iff_isUnit m N).symm
  have hDcard : D.card = Fintype.card {z : ZMod M × ZMod N // Pz z} := by
    calc
      D.card = ZZ.card := by
        refine Finset.card_bij' (s := D) (t := ZZ)
          (fun uv _ => ((uv.1 : ZMod M), (uv.2 : ZMod N)))
          (fun z _ => (z.1.val, z.2.val)) ?hi ?hj ?li ?ri
        · intro uv huv
          have hmem := (Finset.mem_filter.mp huv)
          have hmemprod := hmem.1
          have huM : uv.1 < M := (Finset.mem_range.mp (Finset.mem_product.mp hmemprod).1)
          have hvN : uv.2 < N := (Finset.mem_range.mp (Finset.mem_product.mp hmemprod).2)
          refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
          have hgcd1 : uv.1.gcd M = 1 := hmem.2.1
          have hgcd2 : uv.2.gcd N = 1 := hmem.2.2.1
          have hcong : (uv.1 * R) % M = (uv.2 * (p ^ b * S) + e) % M := hmem.2.2.2
          constructor
          · exact (hmem_units_gcd uv.1).mpr hgcd1
          constructor
          · exact (hmem_units_gcd2 uv.2).mpr hgcd2
          · have hval2 : (uv.2 : ZMod N).val = uv.2 := ZMod.val_natCast_of_lt hvN
            rw [hval2]
            have hcong' : ((uv.1 * R : ℕ) : ZMod M) = ((uv.2 * (p ^ b * S) + e : ℕ) : ZMod M) :=
              (ZMod.natCast_eq_natCast_iff' (uv.1 * R) (uv.2 * (p ^ b * S) + e) M).mpr hcong
            simpa using hcong'
        · intro z hz
          have hmem := (Finset.mem_filter.mp hz).2
          refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
          · exact Finset.mem_range.mpr (ZMod.val_lt z.1)
          · exact Finset.mem_range.mpr (ZMod.val_lt z.2)
          refine ⟨?_, ⟨?_, ?_⟩⟩
          · exact (hmem_units_gcd z.1.val).mp (by simpa [ZMod.natCast_zmod_val] using hmem.1)
          · exact (hmem_units_gcd2 z.2.val).mp (by simpa [ZMod.natCast_zmod_val] using hmem.2.1)
          · have heq' : ((z.1.val * R : ℕ) : ZMod M) = ((z.2.val * (p ^ b * S) + e : ℕ) : ZMod M) := by
              simpa [ZMod.natCast_zmod_val] using hmem.2.2
            exact (ZMod.natCast_eq_natCast_iff' (z.1.val * R) (z.2.val * (p ^ b * S) + e) M).mp heq'
        · rintro ⟨u, v⟩ huv
          have hmem := (Finset.mem_filter.mp huv)
          have hmemprod := hmem.1
          have huM : u < M := (Finset.mem_range.mp (Finset.mem_product.mp hmemprod).1)
          have hvN : v < N := (Finset.mem_range.mp (Finset.mem_product.mp hmemprod).2)
          simp [ZMod.val_natCast_of_lt huM, ZMod.val_natCast_of_lt hvN]
        · intro z hz
          simp [ZMod.natCast_zmod_val]
      _ = Fintype.card {z : ZMod M × ZMod N // Pz z} := by
        calc
          ZZ.card = Fintype.card {z : ZMod M × ZMod N // z ∈ ZZ} := (Fintype.card_coe ZZ).symm
          _ = Fintype.card {z : ZMod M × ZMod N // Pz z} := by
            apply Fintype.card_congr
            refine Equiv.subtypeEquivRight ?_
            intro z
            simp [ZZ, Pz]
  simpa [D, M, N, Pz] using hDcard

/-- Step B: solving `z.1 * ρ = c z.2` for a unit `ρ` collapses the pair count to a count over
the second coordinate alone. -/
private lemma zmod_pair_card_eq_unit_card {M N : ℕ} [NeZero M] [NeZero N]
    (ρ : ZMod M) (c : ZMod N → ZMod M) (hρ : IsUnit ρ) :
    Fintype.card {z : ZMod M × ZMod N // IsUnit z.1 ∧ IsUnit z.2 ∧ z.1 * ρ = c z.2} =
    Fintype.card {v : ZMod N // IsUnit v ∧ IsUnit (c v)} := by
  classical
  refine Fintype.card_congr ?_
  refine {
    toFun := fun z => ⟨z.1.2, z.2.2.1, ?_⟩
    invFun := fun v => ⟨(ρ⁻¹ * c v.1, v.1), ?_, v.2.1, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · have heq : c z.1.2 = z.1.1 * ρ := z.2.2.2.symm
    rw [heq]
    exact z.2.1.mul hρ
  · exact (zmod_isUnit_inv ρ hρ).mul v.2.2
  · have h1 : ρ⁻¹ * ρ = 1 := ZMod.inv_mul_of_unit ρ hρ
    calc
      (ρ⁻¹ * c v.1) * ρ = (c v.1 * ρ⁻¹) * ρ := by rw [mul_comm ρ⁻¹ (c v.1)]
      _ = c v.1 * (ρ⁻¹ * ρ) := by rw [mul_assoc]
      _ = c v.1 * 1 := by rw [h1]
      _ = c v.1 := by rw [mul_one]
  · intro z
    apply Subtype.ext
    apply Prod.ext
    · have h1 : ρ⁻¹ * ρ = 1 := ZMod.inv_mul_of_unit ρ hρ
      calc
        ρ⁻¹ * c z.1.2 = ρ⁻¹ * (z.1.1 * ρ) := by rw [z.2.2.2]
        _ = (ρ⁻¹ * ρ) * z.1.1 := by ring
        _ = 1 * z.1.1 := by rw [h1]
        _ = z.1.1 := by rw [one_mul]
    · rfl
  · intro v
    apply Subtype.ext
    rfl

/-- When `Q v` holds for every `v`, the extra conjunct disappears from the count. -/
private lemma card_IsUnit_and (M : ℕ) [NeZero M] (Q : ZMod M → Prop) [DecidablePred Q]
    (hQ : ∀ v : ZMod M, Q v) :
    Fintype.card {v : ZMod M // IsUnit v ∧ Q v} = Fintype.card {v : ZMod M // IsUnit v} := by
  classical
  refine Fintype.card_congr ?_
  refine {
    toFun := fun v => ⟨v.1, v.2.1⟩
    invFun := fun v => ⟨v.1, v.2, hQ v.1⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro v
    apply Subtype.ext
    rfl
  · intro v
    apply Subtype.ext
    rfl

/-- Counting units as elements of `ZMod M` is the same as counting elements of the unit group. -/
private lemma card_isUnit_eq_units (M : ℕ) [NeZero M] :
    Fintype.card {v : ZMod M // IsUnit v} = Fintype.card (ZMod M)ˣ := by
  classical
  refine Fintype.card_congr ?_
  refine {
    toFun := fun v => v.2.unit
    invFun := fun u => ⟨(u : ZMod M), u.isUnit⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro v
    apply Subtype.ext
    exact v.2.unit_spec
  · intro u
    apply Units.ext
    exact (u.isUnit).unit_spec

/-- In the `¬ p ∣ e` case `c(v) = v.val·p^b·S + e` is a unit modulo `p ^ (a+b)` for every
representative `v` of a class modulo `p ^ a`. -/
private lemma isUnit_c_of_not_dvd (p a b S e : ℕ) (hp : p.Prime) (hb : 0 < b) (hne : ¬ p ∣ e)
    (v : ZMod (p ^ a)) : IsUnit ((v.val * (p ^ b * S) + e : ℕ) : ZMod (p ^ (a + b))) := by
  have hpb : p ∣ p ^ b := by
    simpa using (pow_dvd_pow p (show 1 ≤ b by omega) : p ^ 1 ∣ p ^ b)
  have hpbs : p ∣ p ^ b * S := by
    rcases hpb with ⟨k, hk⟩
    refine ⟨k * S, ?_⟩
    calc
      p ^ b * S = (p * k) * S := by rw [hk]
      _ = p * (k * S) := by ring
  have hpv : p ∣ v.val * (p ^ b * S) := by
    rcases hpbs with ⟨k, hk⟩
    refine ⟨v.val * k, ?_⟩
    calc
      v.val * (p ^ b * S) = v.val * (p * k) := by rw [hk]
      _ = p * (v.val * k) := by ring
  have hnd : ¬ p ∣ v.val * (p ^ b * S) + e := by
    intro hpx
    have hsub : p ∣ (v.val * (p ^ b * S) + e) - v.val * (p ^ b * S) :=
      Nat.dvd_sub hpx hpv
    have hsub' : (v.val * (p ^ b * S) + e) - v.val * (p ^ b * S) = e :=
      Nat.add_sub_cancel_left (v.val * (p ^ b * S)) e
    exact hne (by simpa [hsub'] using hsub)
  exact (ZMod.isUnit_natCast_iff_not_dvd_pow hp (show 0 < a + b by omega)
    (a := v.val * (p ^ b * S) + e)).mpr hnd

theorem pair_count_freshM (p a b R S e : ℕ) (hp : p.Prime) (hb : 0 < b)
    (hR : ¬ p ∣ R) (hS : ¬ p ∣ S) :
    (((Finset.product (Finset.range (p ^ (a + b))) (Finset.range (p ^ a))).filter
      (fun uv : ℕ × ℕ => uv.1.gcd (p ^ (a + b)) = 1 ∧ uv.2.gcd (p ^ a) = 1 ∧
        ((uv.1 * R) % (p ^ (a + b)) = ((uv.2 * (p ^ b * S) + e) % (p ^ (a + b)))))).card) =
      if p ∣ e then 0 else (p ^ a).totient := by
  classical
  by_cases he : p ∣ e
  · rw [if_pos he]
    exact card_eq_zero_of_prime_dvd p a b R S e hp hb hR he
  · rw [if_neg he]
    have hM0 : 0 < p ^ (a + b) := pow_pos hp.pos (a + b)
    have hN0 : 0 < p ^ a := pow_pos hp.pos a
    haveI : NeZero (p ^ (a + b)) := ⟨hM0.ne'⟩
    haveI : NeZero (p ^ a) := ⟨hN0.ne'⟩
    let c : ZMod (p ^ a) → ZMod (p ^ (a + b)) :=
      fun v => ((v.val * (p ^ b * S) + e : ℕ) : ZMod (p ^ (a + b)))
    have hRu : IsUnit (R : ZMod (p ^ (a + b))) := isUnit_R p (a + b) R hp (by omega : 0 < a + b) hR
    have hc_all : ∀ v : ZMod (p ^ a), IsUnit (c v) := by
      intro v
      dsimp [c]
      exact isUnit_c_of_not_dvd p a b S e hp hb he v
    calc
      (((Finset.product (Finset.range (p ^ (a + b))) (Finset.range (p ^ a))).filter
        (fun uv : ℕ × ℕ => uv.1.gcd (p ^ (a + b)) = 1 ∧ uv.2.gcd (p ^ a) = 1 ∧
          ((uv.1 * R) % (p ^ (a + b)) = ((uv.2 * (p ^ b * S) + e) % (p ^ (a + b)))))).card)
        = Fintype.card {z : ZMod (p ^ (a + b)) × ZMod (p ^ a) //
            IsUnit z.1 ∧ IsUnit z.2 ∧
              z.1 * (R : ZMod (p ^ (a + b))) = ((z.2.val * (p ^ b * S) + e : ℕ) : ZMod (p ^ (a + b)))} :=
            nat_card_eq_zmod_card p a b R S e hp
      _ = Fintype.card {v : ZMod (p ^ a) // IsUnit v ∧ IsUnit (c v)} := by
            simpa [c] using (zmod_pair_card_eq_unit_card (M := p ^ (a + b)) (N := p ^ a)
              (ρ := (R : ZMod (p ^ (a + b)))) (c := c) hRu)
      _ = Fintype.card {v : ZMod (p ^ a) // IsUnit v} := by
            exact card_IsUnit_and (p ^ a) (fun v : ZMod (p ^ a) => IsUnit (c v)) hc_all
      _ = (p ^ a).totient := by
            calc
              Fintype.card {v : ZMod (p ^ a) // IsUnit v} = Fintype.card (ZMod (p ^ a))ˣ :=
                card_isUnit_eq_units (p ^ a)
              _ = (p ^ a).totient := ZMod.card_units_eq_totient (p ^ a)

end Commons.Data.Nat