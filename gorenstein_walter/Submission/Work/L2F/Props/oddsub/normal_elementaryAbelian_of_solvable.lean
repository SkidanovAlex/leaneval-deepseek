import Mathlib

namespace Work.L2F.Props.oddsub

open scoped commutatorElement

/-- A finite group all of whose elements have `q`-th power `1` is a `q`-group. -/
lemma isPGroup_of_pow_eq_one {G : Type*} [Group G] {q : ℕ} (h : ∀ x : G, x ^ q = 1) :
    IsPGroup q G :=
  fun x => ⟨1, by rw [pow_one]; exact h x⟩

theorem normal_elementaryAbelian_of_solvable (L : Type*) [Group L] [Finite L]
    (hL : Nontrivial L) (hsolv : Group.IsSolvable L) :
    ∃ (q : ℕ) (_ : Fact q.Prime) (Q : Subgroup L), Q.Normal ∧ Q ≠ ⊥ ∧
      IsPGroup q ↥Q ∧ (∀ x ∈ Q, x ^ q = 1) ∧ (∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) := by
  classical
  -- `⊤` is not `⊥` because `L` is nontrivial.
  have htne : (⊤ : Subgroup L) ≠ ⊥ := by
    intro h
    obtain ⟨a, b, hab⟩ := hL.exists_pair_ne
    refine hab ?_
    have ha : a = 1 := by
      have : a ∈ (⊥ : Subgroup L) := h ▸ Subgroup.mem_top a
      simpa using this
    have hb : b = 1 := by
      have : b ∈ (⊥ : Subgroup L) := h ▸ Subgroup.mem_top b
      simpa using this
    rw [ha, hb]
  -- The derived series reaches `⊥` eventually.
  obtain ⟨n, hn⟩ := hsolv.solvable
  have hex : ∃ m, derivedSeries L (m + 1) = ⊥ := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, derivedSeries_zero] at hn
      exact absurd hn htne
    · exact ⟨n - 1, by rw [Nat.sub_add_cancel h]; exact hn⟩
  obtain ⟨m, hm⟩ := hex
  -- Take the last index `k` with `derivedSeries L k ≠ ⊥`.
  have hP0 : derivedSeries L 0 ≠ ⊥ := by rw [derivedSeries_zero]; exact htne
  set k : ℕ := Nat.findGreatest (fun j => derivedSeries L j ≠ ⊥) m with hkdef
  have hPk : derivedSeries L k ≠ ⊥ := by
    rw [hkdef]
    exact Nat.findGreatest_spec (P := fun j => derivedSeries L j ≠ ⊥) (m := 0)
      (Nat.zero_le m) hP0
  have hkle : k ≤ m := by rw [hkdef]; exact Nat.findGreatest_le m
  have hknext : derivedSeries L (k + 1) = ⊥ := by
    by_cases h : k + 1 ≤ m
    · exact not_not.mp
        (Nat.findGreatest_is_greatest (P := fun j => derivedSeries L j ≠ ⊥)
          (Nat.lt_succ_self k) h)
    · simp only [not_le] at h
      have hkm : k = m := le_antisymm hkle (Nat.le_of_lt_succ h)
      rw [hkm]
      exact hm
  -- `A` is the last nontrivial term: nontrivial, normal and abelian.
  set A : Subgroup L := derivedSeries L k with hAdef
  have hAne : A ≠ ⊥ := by rw [hAdef]; exact hPk
  have hAnorm : A.Normal := by rw [hAdef]; exact derivedSeries_normal L k
  have hAbot : ⁅A, A⁆ = ⊥ := by
    have h1 : derivedSeries L (k + 1) = ⁅A, A⁆ := by
      rw [derivedSeries_succ L k, ← hAdef]
    rw [← h1]
    exact hknext
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
    have hle : A ≤ Subgroup.centralizer (A : Set L) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAbot
    intro x hx y hy
    exact Subgroup.mem_centralizer_iff.mp (hle hy) x hx
  -- Pick a prime `q` dividing `|A|` and an element of order `q`.
  have hAcard_ne : Nat.card ↥A ≠ 1 := fun h => hAne ((Subgroup.eq_bot_iff_card A).mpr h)
  obtain ⟨q, hqprime, hqdvd⟩ := Nat.exists_prime_and_dvd hAcard_ne
  obtain ⟨x0, hx0⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) q (hp := ⟨hqprime⟩) hqdvd
  have hx0powA : x0 ^ q = 1 := by rw [← hx0]; exact pow_orderOf_eq_one x0
  have hx0pow : (x0 : L) ^ q = 1 := by
    rw [← Subgroup.coe_pow, hx0powA, Subgroup.coe_one]
  have hx0ne : x0 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx0
    exact hqprime.ne_one hx0.symm
  -- The subgroup of elements of `A` of order dividing `q`.
  let Q : Subgroup L :=
    { carrier := {x | x ∈ A ∧ x ^ q = 1}
      mul_mem' := by
        intro x y hx hy
        obtain ⟨hxA, hxq⟩ := hx
        obtain ⟨hyA, hyq⟩ := hy
        exact ⟨A.mul_mem hxA hyA, by
          rw [Commute.mul_pow ((commute_iff_eq x y).mpr (hAcomm x hxA y hyA)), hxq, hyq,
            one_mul]⟩
      one_mem' := ⟨A.one_mem, one_pow q⟩
      inv_mem' := by
        intro x hx
        obtain ⟨hxA, hxq⟩ := hx
        exact ⟨A.inv_mem hxA, by rw [inv_pow, hxq, inv_one]⟩ }
  have hQmem : ∀ x : L, x ∈ Q ↔ x ∈ A ∧ x ^ q = 1 := fun x => Iff.rfl
  have hQnorm : Q.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨hxA, hxq⟩ := (hQmem x).mp hx
    refine (hQmem _).mpr ⟨hAnorm.conj_mem x hxA g, ?_⟩
    simp only [conj_pow, hxq, mul_one, mul_inv_cancel]
  have hQne : Q ≠ ⊥ := by
    have hx0Q : (x0 : L) ∈ Q := (hQmem _).mpr ⟨x0.2, hx0pow⟩
    intro h
    rw [h] at hx0Q
    exact hx0ne (Subtype.ext (Subgroup.mem_bot.mp hx0Q))
  have hQp : IsPGroup q ↥Q := by
    refine isPGroup_of_pow_eq_one (fun x => ?_)
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact (hQmem x).mp x.2 |>.2
  exact ⟨q, ⟨hqprime⟩, Q, hQnorm, hQne, hQp, fun x hx => ((hQmem x).mp hx).2,
    fun x hx y hy => hAcomm x ((hQmem x).mp hx).1 y ((hQmem y).mp hy).1⟩

end Work.L2F.Props.oddsub
