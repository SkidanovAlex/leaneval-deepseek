import Mathlib.GroupTheory.PGroup

set_option linter.style.haveILetI false

namespace Commons.GroupTheory.PGroup

lemma finset_prod_dvd_of_pairwise_coprime {ι : Type*} {a : ι → ℕ} {n : ℕ}
    (s : Finset ι)
    (hcop : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Nat.Coprime (a i) (a j))
    (hdvd : ∀ i ∈ s, a i ∣ n) : (∏ i ∈ s, a i) ∣ n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
      rw [Finset.prod_insert hi]
      have h1 : a i ∣ n := hdvd i (Finset.mem_insert_self i s)
      have h2 : (∏ j ∈ s, a j) ∣ n :=
        ih (fun j hj k hk hjk =>
              hcop j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk) hjk)
           (fun j hj => hdvd j (Finset.mem_insert_of_mem hj))
      have hc : Nat.Coprime (a i) (∏ j ∈ s, a j) := by
        rw [Nat.coprime_prod_right_iff]
        intro j hj
        exact hcop i (Finset.mem_insert_self i s) j (Finset.mem_insert_of_mem hj)
          (by rintro rfl; exact hi hj)
      exact hc.mul_dvd_of_dvd_of_dvd h1 h2

theorem exists_mul_mem_iInter_of_isPGroup_quotient {ι : Type*} [Fintype ι] {G : Type*} [Group G]
    [Finite G] {p : ι → ℕ} (hp : ∀ i, (p i).Prime) (hpd : ∀ i j, i ≠ j → p i ≠ p j)
    (N : ι → Subgroup G) [∀ i, (N i).Normal] (hNp : ∀ i, IsPGroup (p i) (G ⧸ N i))
    (x : ι → G) : ∃ y : G, ∀ i, ∃ n ∈ N i, y = x i * n := by
  classical
  -- The quotient orders are pairwise coprime.
  have hcop : ∀ i j, i ≠ j → Nat.Coprime (Nat.card (G ⧸ N i)) (Nat.card (G ⧸ N j)) := by
    intro i j hij
    haveI : Fact (p i).Prime := ⟨hp i⟩
    haveI : Fact (p j).Prime := ⟨hp j⟩
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card.mp (hNp i) : ∃ n, Nat.card (G ⧸ N i) = p i ^ n)
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card.mp (hNp j) : ∃ m, Nat.card (G ⧸ N j) = p j ^ m)
    rw [hn, hm]
    exact Nat.coprime_pow_primes n m (hp i) (hp j) (hpd i j hij)
  -- The product map `G →* ∏ i, G ⧸ N i`.
  let φ : G →* (∀ i, G ⧸ N i) := MonoidHom.pi (fun i => QuotientGroup.mk' (N i))
  let H : Subgroup (∀ i, G ⧸ N i) := φ.range
  -- Each projection `H →* G ⧸ N i` is surjective.
  have hproj_surj : ∀ i, Function.Surjective
      ((Pi.evalMonoidHom (fun i => G ⧸ N i) i).comp H.subtype) := by
    intro i y
    obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (N i) y
    refine ⟨⟨φ g, MonoidHom.mem_range.mpr ⟨g, rfl⟩⟩, ?_⟩
    show (φ g) i = y
    rw [MonoidHom.pi_apply]
    exact hg
  -- Hence the order of each quotient divides `|H|`.
  have hdvd_each : ∀ i, Nat.card (G ⧸ N i) ∣ Nat.card H := fun i =>
    Subgroup.card_dvd_of_surjective _ (hproj_surj i)
  -- The order of `H` divides the product.
  have hHdvd : Nat.card H ∣ ∏ i, Nat.card (G ⧸ N i) := by
    simpa [Nat.card_pi] using Subgroup.card_subgroup_dvd_card H
  -- The product divides `|H|`.
  have hprodvd : (∏ i, Nat.card (G ⧸ N i)) ∣ Nat.card H := by
    have := finset_prod_dvd_of_pairwise_coprime (s := Finset.univ)
      (a := fun i => Nat.card (G ⧸ N i)) (n := Nat.card H)
      (fun i _ j _ hij => hcop i j hij)
      (fun i _ => hdvd_each i)
    simpa using this
  have hcard : Nat.card H = Nat.card (∀ i, G ⧸ N i) := by
    rw [Nat.card_pi]
    exact Nat.dvd_antisymm hHdvd hprodvd
  have hHtop : H = ⊤ := Subgroup.eq_top_of_card_eq H hcard
  have hφsurj : Function.Surjective φ := MonoidHom.range_eq_top.mp hHtop
  obtain ⟨y, hy⟩ := hφsurj (fun i => QuotientGroup.mk' (N i) (x i))
  refine ⟨y, fun i => ?_⟩
  have hi : QuotientGroup.mk' (N i) y = QuotientGroup.mk' (N i) (x i) := by
    have := congr_fun hy i
    simpa [φ, MonoidHom.pi_apply] using this
  obtain ⟨n, hn, hyn⟩ := ((QuotientGroup.mk'_eq_mk' (N i)).mp hi.symm)
  exact ⟨n, hn, hyn.symm⟩

end Commons.GroupTheory.PGroup