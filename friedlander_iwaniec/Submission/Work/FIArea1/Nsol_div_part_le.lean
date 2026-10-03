import Mathlib

namespace Work.FIArea1

/-- Reduction of a divisibility `m ∣ a^2 + b^2` to the residues mod `m`. -/
private lemma mod_reduce_dvd {m a b : ℕ} (h : m ∣ a^2 + b^2) : m ∣ (a % m)^2 + (b % m)^2 := by
  have hm : (a ^ 2 + b ^ 2) % m = ((a % m) ^ 2 + (b % m) ^ 2) % m :=
    (((Nat.mod_modEq a m).symm.pow 2).add ((Nat.mod_modEq b m).symm.pow 2))
  rw [Nat.dvd_iff_mod_eq_zero] at h ⊢
  rw [← hm]; exact h

/-- From `p^e ∣ (p a)^2 + (p b)^2` (with `e ≥ 2`) deduce `p^(e-2) ∣ a^2 + b^2`. -/
private lemma pow_sub_two_dvd {p e a b : ℕ} (hp : 0 < p) (he : 2 ≤ e)
    (h : p^e ∣ (p*a)^2 + (p*b)^2) : p^(e-2) ∣ a^2 + b^2 := by
  have h2 : p^e = p^2 * p^(e-2) := by rw [← Nat.pow_add]; congr 1; omega
  have hz : (p*a)^2 + (p*b)^2 = p^2 * (a^2+b^2) := by ring
  rw [hz, h2] at h
  exact (Nat.mul_dvd_mul_iff_left (by positivity : 0 < p^2)).mp h

/-- The quotient `x / p / p^(e-2)` is a natural number `< p` for `x < p^e` and `e ≥ 2`. -/
private lemma div_div_pow_sub_two_lt {p e : ℕ} (he : 2 ≤ e) (x : ℕ)
    (hx : x < p ^ e) : x / p / p ^ (e - 2) < p := by
  have he1 : p ^ e = p * p ^ (e - 1) := by rw [← pow_succ' p (e-1)]; congr 1; omega
  have h2'' : p ^ (e - 1) = p ^ (e - 2) * p := by rw [← Nat.pow_succ]; congr 1; omega
  have hx1 : x / p < p ^ (e - 1) := by
    apply Nat.div_lt_of_lt_mul
    rw [← he1]; exact hx
  apply Nat.div_lt_of_lt_mul
  rw [← h2'']; exact hx1

/-- The `≤ p^2`-to-one map underlying the estimate: a pair `z = (x, y)` is sent to
the pair of residues mod `p^(e-2)` of `(x/p, y/p)`, together with the corresponding
quotients mod `p`. -/
private def Ndiv_pair_map (p e : ℕ) (hp : p.Prime) (he : 2 ≤ e)
    (z : Fin (p ^ e) × Fin (p ^ e)) :
    (Fin (p ^ (e - 2)) × Fin (p ^ (e - 2))) × (Fin p × Fin p) :=
  ( (⟨z.1.val / p % p ^ (e - 2), Nat.mod_lt _ (pow_pos hp.pos _)⟩,
     ⟨z.2.val / p % p ^ (e - 2), Nat.mod_lt _ (pow_pos hp.pos _)⟩),
    (⟨z.1.val / p / p ^ (e - 2), div_div_pow_sub_two_lt he z.1.val z.1.isLt⟩,
     ⟨z.2.val / p / p ^ (e - 2), div_div_pow_sub_two_lt he z.2.val z.2.isLt⟩) )

/-- The map sends the pairs satisfying `p ∣ x`, `p ∣ y`, `p^e ∣ x^2 + y^2` to the
pairs of residues satisfying `p^(e-2) ∣ u^2 + v^2`. -/
private lemma Ndiv_pair_map_mem {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e)
    (z : Fin (p^e) × Fin (p^e))
    (h1 : p ∣ z.1.val) (h2 : p ∣ z.2.val) (h3 : p^e ∣ z.1.val^2 + z.2.val^2) :
    p^(e-2) ∣ (Ndiv_pair_map p e hp he z).1.1.val^2 + (Ndiv_pair_map p e hp he z).1.2.val^2 := by
  change p^(e-2) ∣ (z.1.val/p % p^(e-2))^2 + (z.2.val/p % p^(e-2))^2
  have h3' : p^e ∣ (p * (z.1.val/p))^2 + (p * (z.2.val/p))^2 := by
    rwa [← Nat.mul_div_cancel' h1, ← Nat.mul_div_cancel' h2] at h3
  exact mod_reduce_dvd (pow_sub_two_dvd hp.pos he h3')

/-- The map is injective on the set of pairs satisfying the divisibility conditions. -/
private lemma Ndiv_pair_map_injOn {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) :
    Set.InjOn (Ndiv_pair_map p e hp he)
      {z : Fin (p^e) × Fin (p^e) | p ∣ z.1.val ∧ p ∣ z.2.val ∧ p^e ∣ z.1.val^2 + z.2.val^2} := by
  intro z hz z' hz' heq
  obtain ⟨hz1, hz2, hz3⟩ := hz
  obtain ⟨hz1', hz2', hz3'⟩ := hz'
  have hrem1 : z.1.val / p % p^(e-2) = z'.1.val / p % p^(e-2) := by
    simpa [Ndiv_pair_map] using congrArg (fun w => w.1.1.val) heq
  have hquot1 : z.1.val / p / p^(e-2) = z'.1.val / p / p^(e-2) := by
    simpa [Ndiv_pair_map] using congrArg (fun w => w.2.1.val) heq
  have hrem2 : z.2.val / p % p^(e-2) = z'.2.val / p % p^(e-2) := by
    simpa [Ndiv_pair_map] using congrArg (fun w => w.1.2.val) heq
  have hquot2 : z.2.val / p / p^(e-2) = z'.2.val / p / p^(e-2) := by
    simpa [Ndiv_pair_map] using congrArg (fun w => w.2.2.val) heq
  have ha1 : z.1.val / p = z'.1.val / p := by
    rw [← Nat.div_add_mod (z.1.val/p) (p^(e-2)),
        ← Nat.div_add_mod (z'.1.val/p) (p^(e-2)), hquot1, hrem1]
  have ha2 : z.2.val / p = z'.2.val / p := by
    rw [← Nat.div_add_mod (z.2.val/p) (p^(e-2)),
        ← Nat.div_add_mod (z'.2.val/p) (p^(e-2)), hquot2, hrem2]
  have hx1 : z.1.val = z'.1.val := by
    rw [← Nat.mul_div_cancel' hz1, ← Nat.mul_div_cancel' hz1', ha1]
  have hx2 : z.2.val = z'.2.val := by
    rw [← Nat.mul_div_cancel' hz2, ← Nat.mul_div_cancel' hz2', ha2]
  exact Prod.ext (Fin.ext hx1) (Fin.ext hx2)

theorem Nsol_div_part_le {p e : ℕ} (hp : p.Prime) (he : 2 ≤ e) :
    ((Finset.univ : Finset (Fin (p ^ e) × Fin (p ^ e))).filter
        (fun z => p ∣ z.1.val ∧ p ∣ z.2.val ∧ p ^ e ∣ z.1.val ^ 2 + z.2.val ^ 2)).card
      ≤ p ^ 2 * ((Finset.univ : Finset (Fin (p ^ (e - 2)) × Fin (p ^ (e - 2)))).filter
          (fun w => p ^ (e - 2) ∣ w.1.val ^ 2 + w.2.val ^ 2)).card := by
  set A := (Finset.univ : Finset (Fin (p ^ e) × Fin (p ^ e))).filter
        (fun z => p ∣ z.1.val ∧ p ∣ z.2.val ∧ p ^ e ∣ z.1.val ^ 2 + z.2.val ^ 2) with hA
  set B := (Finset.univ : Finset (Fin (p ^ (e - 2)) × Fin (p ^ (e - 2)))).filter
          (fun w => p ^ (e - 2) ∣ w.1.val ^ 2 + w.2.val ^ 2) with hB
  have hle : A.card ≤ (B ×ˢ (Finset.univ : Finset (Fin p × Fin p))).card := by
    rw [hA, hB]
    apply Finset.card_le_card_of_injOn (Ndiv_pair_map p e hp he)
    · intro z hz
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hz
      rw [Finset.mem_coe, Finset.mem_product]
      refine ⟨?_, Finset.mem_univ _⟩
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, Ndiv_pair_map_mem hp he z hz.1 hz.2.1 hz.2.2⟩
    · have hset : (↑((Finset.univ : Finset (Fin (p^e) × Fin (p^e))).filter
            (fun z => p ∣ z.1.val ∧ p ∣ z.2.val ∧ p ^ e ∣ z.1.val ^ 2 + z.2.val ^ 2))
            : Set (Fin (p^e) × Fin (p^e)))
            = {z : Fin (p^e) × Fin (p^e) |
                p ∣ z.1.val ∧ p ∣ z.2.val ∧ p^e ∣ z.1.val^2 + z.2.val^2} := by
        ext z
        simp
      rw [hset]
      exact Ndiv_pair_map_injOn hp he
  have hcard : (B ×ˢ (Finset.univ : Finset (Fin p × Fin p))).card = p^2 * B.card := by
    rw [Finset.card_product, Finset.card_univ]
    simp only [Fintype.card_prod, Fintype.card_fin]
    ring
  calc A.card ≤ (B ×ˢ (Finset.univ : Finset (Fin p × Fin p))).card := hle
    _ = p^2 * B.card := hcard

end Work.FIArea1
