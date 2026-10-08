import Mathlib
import Submission.Work.Fitting.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Fitting.isPSolvable_of_solvable`

Every finite solvable group is `p`-solvable: the upper `p`-series
`1 ≤ O_{p'}(G) ≤ O_{p',p}(G) ≤ O_{p',p,p'}(G) ≤ ...` reaches `G`.

The argument is a descent along the even terms `B_{2i} = pCoreSeries p G (2i)`.
If `H` is a nontrivial finite solvable group then either `O_p(H) ≠ 1` or
`O_{p'}(H) ≠ 1`: `H` has a nontrivial abelian normal subgroup `A` (the last
nonzero term of the derived series), and for a prime `q` dividing `|A|` the
elements of `A` of order dividing `q` form a nontrivial normal `q`-subgroup of
`H`.  Consequently `B_{2i} < B_{2i+2}` whenever `B_{2i} ≠ ⊤`, and since the
subgroup lattice of a finite group is finite such a strictly increasing chain
cannot be infinite.
-/

noncomputable section

open Classical

open scoped commutatorElement

namespace Work.Fitting

/-- The `π`-core is preserved by an isomorphism of groups. -/
theorem piCore_map_mulEquiv {π : ℕ → Prop} {H K : Type*} [Group H] [Group K] (e : H ≃* K) :
    (piCore π H).map e.toMonoidHom = piCore π K := by
  rw [piCore, map_sSup]
  have himg : Subgroup.map e.toMonoidHom '' piCoreSet π H = piCoreSet π K := by
    refine le_antisymm ?_ ?_
    · rintro L ⟨L₀, hL₀, rfl⟩
      obtain ⟨hn, hc⟩ := hL₀
      exact ⟨hn.map _ e.surjective,
        by rw [Subgroup.card_map_of_injective e.injective]; exact hc⟩
    · intro L hL
      refine ⟨L.map e.symm.toMonoidHom, ?_, ?_⟩
      · obtain ⟨hn, hc⟩ := hL
        exact ⟨hn.map _ e.symm.surjective,
          by rw [Subgroup.card_map_of_injective e.symm.injective]; exact hc⟩
      · rw [Subgroup.map_map]
        have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id K := by
          ext x; simp
        rw [hcomp, Subgroup.map_id]
  rw [himg]
  rfl

/-- Monotonicity step of the upper `p`-series. -/
private theorem pCoreSeries_le_succ' (p : ℕ) (G : Type*) [Group G] (n : ℕ) :
    pCoreSeries p G n ≤ pCoreSeries p G (n + 1) := by
  rw [pCoreSeries_succ]
  intro x hx
  rw [Subgroup.mem_comap]
  have h1 : QuotientGroup.mk' (pCoreSeries p G n) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
  rw [h1]
  exact Subgroup.one_mem _

/-! ## A nontrivial abelian normal subgroup of a nontrivial solvable group -/

/-- Every nontrivial solvable group has a nontrivial abelian normal subgroup:
the last nonzero term of the derived series. -/
theorem exists_abelian_normal_of_solvable_nontrivial (H : Type*) [Group H]
    [Group.IsSolvable H] [Nontrivial H] :
    ∃ A : Subgroup H, A.Normal ∧ A ≠ ⊥ ∧ ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
  classical
  obtain ⟨n, hn⟩ := Group.IsSolvable.solvable (G := H)
  have hex : ∃ m : ℕ, derivedSeries H m = ⊥ := ⟨n, hn⟩
  set k := Nat.find hex with hk
  have hkspec : derivedSeries H k = ⊥ := by
    rw [hk]; exact Nat.find_spec hex
  have hk0 : k ≠ 0 := by
    intro h
    rw [h, derivedSeries_zero] at hkspec
    exact top_ne_bot hkspec
  refine ⟨derivedSeries H (k - 1), derivedSeries_normal H (k - 1), ?_, ?_⟩
  · intro h
    have hle := Nat.find_min' hex h
    rw [← hk] at hle
    omega
  · intro x hx y hy
    have hmem : ⁅x, y⁆ ∈ ⁅derivedSeries H (k - 1), derivedSeries H (k - 1)⁆ :=
      Subgroup.commutator_mem_commutator hx hy
    have hbot : ⁅derivedSeries H (k - 1), derivedSeries H (k - 1)⁆ = ⊥ := by
      rw [← derivedSeries_succ H (k - 1), Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0)]
      exact hkspec
    rw [hbot, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem

/-! ## The local key lemma -/

/-- A finite group with a nontrivial abelian normal subgroup has a nontrivial normal
`p`-subgroup or a nontrivial normal `p'`-subgroup. -/
theorem pCore_ne_bot_or_pPrimeCore_ne_bot_of_abelian_normal {p : ℕ} {H : Type*} [Group H]
    [Finite H] {A : Subgroup H} (hAn : A.Normal)
    (hab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAne : A ≠ ⊥) :
    pCore p H ≠ ⊥ ∨ pPrimeCore p H ≠ ⊥ := by
  classical
  haveI : Nontrivial ↥A := (Subgroup.nontrivial_iff_ne_bot A).mpr hAne
  have hcard : Nat.card ↥A ≠ 1 := by
    intro h
    have hs : Subsingleton ↥A := (Nat.card_eq_one_iff_unique.mp h).1
    obtain ⟨a, b, hab'⟩ := (inferInstance : Nontrivial ↥A).exists_pair_ne
    exact hab' (Subsingleton.elim a b)
  obtain ⟨q, hqprime, hqdvd⟩ := Nat.exists_prime_and_dvd hcard
  haveI : Fact q.Prime := ⟨hqprime⟩
  obtain ⟨x, hxq⟩ := exists_prime_orderOf_dvd_card' (G := ↥A) q hqdvd
  have hxne : x ≠ 1 := by
    intro h
    have hq1 : q = 1 := by rw [← hxq, h, orderOf_one]
    exact hqprime.ne_one hq1
  have hxqH : (x : H) ^ q = 1 := by
    have hord : orderOf (x : H) = q := (Subgroup.orderOf_coe x).trans hxq
    rw [← hord]; exact pow_orderOf_eq_one _
  let S : Subgroup H :=
    { carrier := {y : H | y ∈ A ∧ y ^ q = 1}
      one_mem' := ⟨A.one_mem, one_pow q⟩
      mul_mem' := by
        rintro y z ⟨hyA, hyq⟩ ⟨hzA, hzq⟩
        refine ⟨A.mul_mem hyA hzA, ?_⟩
        have hcomm : Commute y z := (commute_iff_eq y z).mpr (hab y hyA z hzA)
        rw [hcomm.mul_pow, hyq, hzq, mul_one]
      inv_mem' := by
        rintro y ⟨hyA, hyq⟩
        exact ⟨A.inv_mem hyA, by rw [inv_pow, hyq, inv_one]⟩ }
  have hSnorm : S.Normal :=
    ⟨fun n hn g => by
      obtain ⟨hnA, hnq⟩ := hn
      refine ⟨hAn.conj_mem n hnA g, ?_⟩
      rw [conj_pow, hnq, mul_one, mul_inv_cancel]⟩
  have hSne : S ≠ ⊥ := by
    intro hbot
    have hxS : (x : H) ∈ S := ⟨x.2, hxqH⟩
    rw [hbot] at hxS
    exact (fun h : (x : H) = 1 => hxne (Subtype.ext h)) (Subgroup.mem_bot.mp hxS)
  have hSpg : IsPGroup q ↥S := fun g => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (by simpa using g.2.2)⟩
  have key : ∀ π : ℕ → Prop, (∀ r, r.Prime → r ∣ q → π r) →
      IsPiNat π (Nat.card ↥S) := by
    intro π hπ r hr hrd
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hSpg
    have hrd' : r ∣ q := hr.dvd_of_dvd_pow (by rw [← hm]; exact hrd)
    exact hπ r hr hrd'
  rcases eq_or_ne q p with hqp | hqp
  · left
    have hpi : IsPiNat (fun r => r = p) (Nat.card ↥S) :=
      key _ (fun r hr hrd => by
        rw [(Nat.prime_dvd_prime_iff_eq hr hqprime).mp hrd]; exact hqp)
    have hle : S ≤ pCore p H := le_piCore hSnorm hpi
    intro hbot
    rw [hbot] at hle
    exact hSne (le_bot_iff.mp hle)
  · right
    have hpi : IsPiNat (fun r => r ≠ p) (Nat.card ↥S) :=
      key _ (fun r hr hrd => by
        have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr hqprime).mp hrd
        rw [hrq]; exact hqp)
    have hle : S ≤ pPrimeCore p H := le_piCore hSnorm hpi
    intro hbot
    rw [hbot] at hle
    exact hSne (le_bot_iff.mp hle)

/-! ## The group-theoretic key lemma -/

/-- A nontrivial finite solvable group has a nontrivial normal `p`-subgroup or a
nontrivial normal `p'`-subgroup. -/
theorem pCore_ne_bot_or_pPrimeCore_ne_bot (p : ℕ) (H : Type*) [Group H] [Finite H]
    [Group.IsSolvable H] [Nontrivial H] : pCore p H ≠ ⊥ ∨ pPrimeCore p H ≠ ⊥ := by
  obtain ⟨A, hAn, hAne, hab⟩ := exists_abelian_normal_of_solvable_nontrivial H
  exact pCore_ne_bot_or_pPrimeCore_ne_bot_of_abelian_normal hAn hab hAne

/-! ## The quotient correspondence -/

/-- If the `(n+1)`-st term of the upper `p`-series equals the `n`-th, then the
`π`-core of the quotient that defines it is trivial. -/
theorem piCore_quotient_eq_bot_of_pCoreSeries_eq {G : Type*} [Group G] (p n : ℕ)
    (h : pCoreSeries p G (n + 1) = pCoreSeries p G n) :
    piCore (fun q => if Even n then q ≠ p else q = p) (G ⧸ pCoreSeries p G n) = ⊥ := by
  apply Subgroup.comap_injective (QuotientGroup.mk'_surjective (pCoreSeries p G n))
  rw [MonoidHom.comap_bot, QuotientGroup.ker_mk', ← pCoreSeries_succ p G n]
  exact h

/-! ## The main theorem -/

theorem isPSolvable_of_solvable (p : ℕ) (G : Type*) [Group G] [Finite G] [Group.IsSolvable G] :
    Work.Fitting.IsPSolvable p G := by
  classical
  by_contra hnot
  have hnot' : ∀ n, pCoreSeries p G n ≠ ⊤ := fun n hn => hnot ⟨n, hn⟩
  -- The even terms of the upper `p`-series strictly increase unless they reach `⊤`.
  have hstep : ∀ i : ℕ, pCoreSeries p G (2 * i) ≠ ⊤ →
      pCoreSeries p G (2 * i) < pCoreSeries p G (2 * i + 2) := by
    intro i hi
    refine lt_of_le_of_ne ?_ ?_
    · exact le_trans (pCoreSeries_le_succ' p G (2 * i))
        (pCoreSeries_le_succ' p G (2 * i + 1))
    · intro heq
      have h1 : pCoreSeries p G (2 * i + 1) = pCoreSeries p G (2 * i) := by
        refine le_antisymm ?_ (pCoreSeries_le_succ' p G (2 * i))
        calc pCoreSeries p G (2 * i + 1)
            ≤ pCoreSeries p G (2 * i + 1 + 1) := pCoreSeries_le_succ' p G (2 * i + 1)
          _ = pCoreSeries p G (2 * i + 2) := rfl
          _ = pCoreSeries p G (2 * i) := heq.symm
      have h2 : pCoreSeries p G (2 * i + 2) = pCoreSeries p G (2 * i + 1) := by
        rw [← heq, h1]
      have hQ := piCore_quotient_eq_bot_of_pCoreSeries_eq p (2 * i) h1
      have hQ' : pPrimeCore p (G ⧸ pCoreSeries p G (2 * i)) = ⊥ := by
        have hpred : (fun q : ℕ => if Even (2 * i) then q ≠ p else q = p) =
            (fun q => q ≠ p) := by
          funext q; rw [if_pos (even_two_mul i)]
        rw [hpred] at hQ
        exact hQ
      have hP := piCore_quotient_eq_bot_of_pCoreSeries_eq p (2 * i + 1) h2
      have hP' : pCore p (G ⧸ pCoreSeries p G (2 * i)) = ⊥ := by
        have hodd : ¬ Even (2 * i + 1) := by rintro ⟨k, hk⟩; omega
        have hpred : (fun q : ℕ => if Even (2 * i + 1) then q ≠ p else q = p) =
            (fun q => q = p) := by
          funext q; rw [if_neg hodd]
        rw [hpred] at hP
        -- transfer along the canonical isomorphism `G ⧸ B = G ⧸ B'` given by `h1`
        have hmap := piCore_map_mulEquiv (π := fun q : ℕ => q = p)
          (QuotientGroup.quotientMulEquivOfEq h1)
        rw [hP, Subgroup.map_bot] at hmap
        exact hmap.symm
      haveI : Finite (G ⧸ pCoreSeries p G (2 * i)) := inferInstance
      haveI : Group.IsSolvable (G ⧸ pCoreSeries p G (2 * i)) := inferInstance
      haveI : Nontrivial (G ⧸ pCoreSeries p G (2 * i)) := by
        have hex : ∃ g : G, g ∉ pCoreSeries p G (2 * i) := by
          by_contra h
          exact hi ((Subgroup.eq_top_iff' (pCoreSeries p G (2 * i))).mpr
            fun g => by by_contra hg; exact h ⟨g, hg⟩)
        obtain ⟨g, hg⟩ := hex
        exact ⟨QuotientGroup.mk' (pCoreSeries p G (2 * i)) g, 1, by
          intro hcon
          exact hg ((QuotientGroup.eq_one_iff g).mp hcon)⟩
      rcases pCore_ne_bot_or_pPrimeCore_ne_bot p (G ⧸ pCoreSeries p G (2 * i)) with h | h
      · exact h hP'
      · exact h hQ'
  have hstrict : StrictMono (fun i : ℕ => pCoreSeries p G (2 * i)) :=
    strictMono_nat_of_lt_succ fun i => hstep i (hnot' (2 * i))
  have hinj : Function.Injective (fun i : ℕ => pCoreSeries p G (2 * i)) := hstrict.injective
  exact (Set.infinite_range_of_injective hinj).not_finite
    (Set.Finite.subset Set.finite_univ (Set.subset_univ _))

end Work.Fitting
