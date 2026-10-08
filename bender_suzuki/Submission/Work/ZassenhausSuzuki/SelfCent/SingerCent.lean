import Mathlib
import Submission.Work.ZassenhausSuzuki.prop14_normalizer_quotient_two
import Submission.Work.ZassenhausSuzuki.SingerData
import Submission.Work.ZassenhausSuzuki.SzSetting
import Submission.Work.ZassenhausSuzuki.centralizer_abelian_of_strongly_real
import Submission.Work.ZassenhausSuzuki.pow_two_classification

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki.SelfCent

/-! ## 1. Generic counting helpers

If `f : α → β` is a map between finite types and every fibre of `f` has card exactly `l`, then
`#α = l * #β`; if every fibre has at least `k` elements then `k * #β ≤ #α`. -/

theorem card_eq_mul_card_of_card_fiber {α β : Type*} [Fintype α] [Fintype β] (f : α → β) (l : ℕ)
    (h : ∀ b : β, Fintype.card {a : α // f a = b} = l) :
    Fintype.card α = l * Fintype.card β := by
  classical
  have h1 : ∀ b ∈ (Finset.univ : Finset β),
      (Finset.univ.filter (fun a : α => f a = b)).card = l := by
    intro b _
    have := h b
    rwa [Fintype.card_subtype] at this
  have h2 : ∑ b ∈ (Finset.univ : Finset β),
      (Finset.univ.filter (fun a : α => f a = b)).card
      = ∑ b ∈ (Finset.univ : Finset β), l := Finset.sum_congr rfl h1
  have h3 : ∑ b ∈ (Finset.univ : Finset β),
      (Finset.univ.filter (fun a : α => f a = b)).card = Fintype.card α := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ)
      (by intro a _; simp)]
    simp
  rw [h3, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] at h2
  exact h2

theorem mul_card_le_card_of_le_card_fiber {α β : Type*} [Fintype α] [Fintype β] (f : α → β)
    (k : ℕ) (h : ∀ b : β, k ≤ Fintype.card {a : α // f a = b}) :
    k * Fintype.card β ≤ Fintype.card α := by
  classical
  have h1 : ∀ b ∈ (Finset.univ : Finset β),
      k ≤ (Finset.univ.filter (fun a : α => f a = b)).card := by
    intro b _
    have := h b
    rwa [Fintype.card_subtype] at this
  have h2 : ∑ b ∈ (Finset.univ : Finset β), k
      ≤ ∑ b ∈ (Finset.univ : Finset β),
        (Finset.univ.filter (fun a : α => f a = b)).card := Finset.sum_le_sum h1
  have h3 : ∑ b ∈ (Finset.univ : Finset β),
      (Finset.univ.filter (fun a : α => f a = b)).card = Fintype.card α := by
    rw [← Finset.card_eq_sum_card_fiberwise (f := f) (s := Finset.univ) (t := Finset.univ)
      (by intro a _; simp)]
    simp
  rw [h3, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.mul_comm] at h2
  exact h2

/-! ## 2. The `p`-torsion of a commutative group -/

section PTorsion

variable {B : Type*} [CommGroup B]

/-- The `d`-torsion subgroup `{x | x ^ d = 1}` of a commutative group. -/
def ptorsion (d : ℕ) : Subgroup B where
  carrier := {x | x ^ d = 1}
  mul_mem' := by
    intro x y hx hy
    show (x * y) ^ d = 1
    rw [mul_pow, hx, hy, one_mul]
  one_mem' := by show (1 : B) ^ d = 1; simp
  inv_mem' := by
    intro x hx
    show x⁻¹ ^ d = 1
    rw [inv_pow, hx, inv_one]

@[simp] theorem mem_ptorsion {d : ℕ} {x : B} : x ∈ ptorsion (B := B) d ↔ x ^ d = 1 := Iff.rfl

theorem ptorsion_le_ptorsion {d n : ℕ} (h : d ∣ n) : ptorsion (B := B) d ≤ ptorsion (B := B) n := by
  intro x hx
  rw [mem_ptorsion] at hx ⊢
  obtain ⟨k, rfl⟩ := h
  rw [pow_mul, hx, one_pow]

/-- The `p`-torsion of a finite commutative group has `p`-power order. -/
theorem ptorsion_card_eq_prime_pow [Finite B] (p : ℕ) (hp : p.Prime) :
    ∃ r : ℕ, Nat.card {x : B // x ^ p = 1} = p ^ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : IsPGroup p ↥(ptorsion (B := B) p) := by
    rw [IsPGroup.iff_orderOf]
    intro x
    have hx : (x : B) ^ p = 1 := x.2
    have h1 : orderOf (x : B) ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hx
    have h2 : orderOf (x : ↥(ptorsion (B := B) p)) = orderOf (x : B) :=
      (Subgroup.orderOf_coe x).symm
    rcases (Nat.dvd_prime hp).mp h1 with h3 | h3
    · exact ⟨0, by rw [h2, h3, pow_zero]⟩
    · exact ⟨1, by rw [h2, h3, pow_one]⟩
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp this
  refine ⟨r, ?_⟩
  rw [← hr]
  exact Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))

/-- The `n`-torsion of a commutative group is bounded by `n` if all prime torsions are. -/
theorem card_ptorsion_le [Finite B]
    (h : ∀ p : ℕ, p.Prime → Nat.card {x : B // x ^ p = 1} ≤ p) :
    ∀ n : ℕ, 0 < n → Nat.card {x : B // x ^ n = 1} ≤ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro hn
    rcases Nat.lt_or_ge 1 n with h2 | h1
    · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
      set d := n / p with hd
      have hdp : d * p = n := Nat.div_mul_cancel hpdvd
      have hdpos : 0 < d := by
        rcases Nat.eq_zero_or_pos d with h | h
        · rw [h, zero_mul] at hdp; omega
        · exact h
      have hdlt : d < n := by
        have hp2 : 2 ≤ p := hp.two_le
        have hle : d * 2 ≤ d * p := Nat.mul_le_mul_left d hp2
        omega
      have IHd : Nat.card {x : B // x ^ d = 1} ≤ d := IH d hdlt hdpos
      let f : ↥(ptorsion (B := B) n) →* ↥(ptorsion (B := B) p) :=
        ((powMonoidHom d : B →* B).comp (ptorsion (B := B) n).subtype).codRestrict _
          (fun x => by
            rw [MonoidHom.comp_apply, powMonoidHom_apply, mem_ptorsion, ← pow_mul, hdp]
            exact x.2)
      have hcardn : Nat.card ↥(ptorsion (B := B) n) = Nat.card {x : B // x ^ n = 1} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))
      have hcardp : Nat.card ↥(ptorsion (B := B) p) = Nat.card {x : B // x ^ p = 1} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun x => Iff.rfl))
      have hdis : d ∣ n := ⟨p, hdp.symm⟩
      have hfx : ∀ x : ↥(ptorsion (B := B) n),
          ((f x : ↥(ptorsion (B := B) p)) : B) = (x : B) ^ d := by
        intro x
        show (powMonoidHom d : B →* B) ((x : B)) = (x : B) ^ d
        rw [powMonoidHom_apply]
      have hker : Nat.card ↥f.ker = Nat.card {x : B // x ^ d = 1} := by
        have hfker : f.ker = (ptorsion (B := B) d).subgroupOf (ptorsion (B := B) n) := by
          ext x
          rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_ptorsion]
          constructor
          · intro hx
            have hx' : ((f x : ↥(ptorsion (B := B) p)) : B) = 1 := congrArg Subtype.val hx
            rwa [hfx x] at hx'
          · intro hx
            apply Subtype.ext
            rw [hfx x]
            simpa using hx
        rw [hfker]
        exact Nat.card_congr
          { toFun := fun x => ⟨(x : ↥(ptorsion (B := B) n)), x.2⟩
            invFun := fun x => ⟨⟨(x : B), ptorsion_le_ptorsion hdis x.2⟩,
              Subgroup.mem_subgroupOf.mpr x.2⟩
            left_inv := fun x => Subtype.ext (Subtype.ext rfl)
            right_inv := fun x => Subtype.ext rfl }
      have hstep : Nat.card ↥(ptorsion (B := B) n)
          ≤ Nat.card ↥(ptorsion (B := B) p) * Nat.card ↥f.ker := by
        have h1 : Nat.card ↥f.ker * f.ker.index = Nat.card ↥(ptorsion (B := B) n) :=
          Subgroup.card_mul_index f.ker
        have h2 : f.ker.index = Nat.card ↥f.range := Subgroup.index_ker f
        have h3 : Nat.card ↥f.range ≤ Nat.card ↥(ptorsion (B := B) p) :=
          Nat.card_le_card_of_injective _ (Subtype.val_injective)
        rw [h2] at h1
        calc Nat.card ↥(ptorsion (B := B) n) = Nat.card ↥f.ker * Nat.card ↥f.range := h1.symm
          _ ≤ Nat.card ↥f.ker * Nat.card ↥(ptorsion (B := B) p) := Nat.mul_le_mul_left _ h3
          _ = Nat.card ↥(ptorsion (B := B) p) * Nat.card ↥f.ker := Nat.mul_comm _ _
      rw [hcardn, hcardp, hker] at hstep
      calc Nat.card {x : B // x ^ n = 1}
          ≤ Nat.card {x : B // x ^ p = 1} * Nat.card {x : B // x ^ d = 1} := hstep
        _ ≤ p * d := Nat.mul_le_mul (h p hp) IHd
        _ = n := by rw [Nat.mul_comm]; exact hdp
    · have hn1 : n = 1 := by omega
      subst hn1
      have hsub : Subsingleton {x : B // x ^ 1 = 1} :=
        ⟨fun a b => Subtype.ext (by simpa using a.2.trans b.2.symm)⟩
      have hthis : Nat.card {x : B // x ^ 1 = 1} = 1 :=
        Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨⟨1, by simp⟩⟩⟩
      rw [hthis]

/-- A finite commutative group all of whose prime torsions are small is cyclic. -/
theorem isCyclic_of_ptorsion_card_le [Finite B]
    (h : ∀ p : ℕ, p.Prime → Nat.card {x : B // x ^ p = 1} ≤ p) : IsCyclic B := by
  haveI : DecidableEq B := Classical.decEq B
  haveI : Fintype B := Fintype.ofFinite B
  refine isCyclic_of_card_pow_eq_one_le (fun n hn => ?_)
  have h1 : Nat.card {x : B // x ^ n = 1} = (Finset.univ.filter (fun a : B => a ^ n = 1)).card := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← h1]
  exact card_ptorsion_le (B := B) h n hn

end PTorsion

/-! ## 3. The non-cyclic `p`-torsion corollary -/

theorem exists_prime_ptorsion_sq_le_of_not_isCyclic {B : Type*} [Group B] [Finite B]
    (hcomm : IsMulCommutative B) (h : ¬ @IsCyclic B (@ZPow.toPow B _)) :
    ∃ p : ℕ, p.Prime ∧ p ^ 2 ≤ Nat.card {x : B // x ^ p = 1} := by
  letI hCB : CommGroup B := { toGroup := ‹Group B›, mul_comm := fun a b => hcomm.is_comm.comm a b }
  by_contra hcon
  push_neg at hcon
  refine h (isCyclic_of_ptorsion_card_le (B := B) (fun p hp => ?_))
  obtain ⟨r, hr⟩ := ptorsion_card_eq_prime_pow (B := B) p hp
  have hlt : p ^ r < p ^ 2 := by rw [← hr]; exact hcon p hp
  rw [hr]
  rcases Nat.lt_or_ge r 2 with h2 | h2
  · interval_cases r
    · simpa using hp.one_le
    · simp
  · exact absurd hlt (not_lt.mpr (Nat.pow_le_pow_right hp.one_le h2))

/-! ## 4. Counting orbits of a group action with one fixed singleton orbit -/

theorem mem_orbit_comm {Γ X : Type*} [Group Γ] [MulAction Γ X] (x y : X) :
    y ∈ MulAction.orbit Γ x ↔ x ∈ MulAction.orbit Γ y := by
  constructor
  · intro h
    rw [MulAction.mem_orbit_iff] at h ⊢
    obtain ⟨g, hg⟩ := h
    exact ⟨g⁻¹, by rw [← hg]; simp⟩
  · intro h
    rw [MulAction.mem_orbit_iff] at h ⊢
    obtain ⟨g, hg⟩ := h
    exact ⟨g⁻¹, by rw [← hg]; simp⟩

/-- Counting lemma: if the orbits of a finite group action on a finite type `X` are `{x₀}` and
a family of orbits of common size `l`, each of the latter meeting the finite set `Y` in at least
two points, then `#X - 1 = l c` and `2 c ≤ #Y` for `c` the number of these orbits. -/
theorem orbit_counting {Γ X : Type*} [Group Γ] [MulAction Γ X] [Fintype Γ] [Fintype X]
    (x₀ : X) (hfix : MulAction.orbit Γ x₀ = {x₀}) (l : ℕ)
    (horb : ∀ x : X, x ≠ x₀ → Fintype.card (MulAction.orbit Γ x) = l)
    (Y : Finset X) (hY : ∀ x : X, x ≠ x₀ → 2 ≤ (Y.filter (fun y => y ∈ MulAction.orbit Γ x)).card) :
    ∃ c : ℕ, Fintype.card X - 1 = l * c ∧ 2 * c ≤ Y.card := by
  classical
  set Q := Quotient (MulAction.orbitRel Γ X) with hQ
  have hmem : ∀ y x : X, (Quotient.mk (MulAction.orbitRel Γ X) y
      = Quotient.mk (MulAction.orbitRel Γ X) x) ↔ y ∈ MulAction.orbit Γ x := by
    intro y x
    rw [Quotient.eq, MulAction.orbitRel_apply, mem_orbit_comm]
  have hfib : ∀ x : X,
      Fintype.card {y : X // Quotient.mk (MulAction.orbitRel Γ X) y
        = Quotient.mk (MulAction.orbitRel Γ X) x} = Fintype.card (MulAction.orbit Γ x) := by
    intro x
    have hset : {y : X // Quotient.mk (MulAction.orbitRel Γ X) y
        = Quotient.mk (MulAction.orbitRel Γ X) x} ≃ MulAction.orbit Γ x :=
      { toFun := fun y => ⟨y.1, (hmem y.1 x).mp y.2⟩
        invFun := fun y => ⟨y.1, (hmem y.1 x).mpr y.2⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl }
    exact Fintype.card_congr hset
  set q₀ : Q := Quotient.mk (MulAction.orbitRel Γ X) x₀ with hq₀
  have hq₀card : Fintype.card {y : X // Quotient.mk (MulAction.orbitRel Γ X) y = q₀} = 1 := by
    have h1 := hfib x₀
    rw [← hq₀] at h1
    have hle : Fintype.card (MulAction.orbit Γ x₀) ≤ 1 := by
      refine Fintype.card_le_one_iff.mpr (fun a b => Subtype.ext ?_)
      have ha : (a : X) = x₀ := Set.mem_singleton_iff.mp (hfix ▸ a.2)
      have hb : (b : X) = x₀ := Set.mem_singleton_iff.mp (hfix ▸ b.2)
      rw [ha, hb]
    have hpos : 0 < Fintype.card {y : X // Quotient.mk (MulAction.orbitRel Γ X) y = q₀} :=
      Fintype.card_pos_iff.mpr ⟨⟨x₀, by rw [← hq₀]⟩⟩
    omega
  have hqcard : ∀ q : Q, q ≠ q₀ →
      Fintype.card {y : X // Quotient.mk (MulAction.orbitRel Γ X) y = q} = l := by
    intro q hq
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    have hx : x ≠ x₀ := by
      intro hxx
      apply hq
      rw [hxx]
    rw [hfib x, horb x hx]
  refine ⟨Fintype.card Q - 1, ?_, ?_⟩
  · have hsum : Fintype.card X
        = ∑ q : Q, Fintype.card {y : X // Quotient.mk (MulAction.orbitRel Γ X) y = q} := by
      have h := Finset.card_eq_sum_card_fiberwise
        (f := (Quotient.mk (MulAction.orbitRel Γ X) : X → Q))
        (s := (Finset.univ : Finset X)) (t := (Finset.univ : Finset Q))
        (by intro a _; simp)
      rw [Finset.card_univ] at h
      rw [h]
      apply Finset.sum_congr rfl
      intro q _
      rw [← Fintype.card_subtype]
    rw [hsum, ← Finset.sum_erase_add _ _ (Finset.mem_univ q₀), hq₀card]
    have h2 : (∑ q ∈ (Finset.univ.erase q₀),
        Fintype.card {y : X // Quotient.mk (MulAction.orbitRel Γ X) y = q})
        = l * (Fintype.card Q - 1) := by
      rw [Finset.sum_congr rfl (fun q hq => hqcard q (Finset.mem_erase.mp hq).1),
        Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ q₀), Finset.card_univ,
        smul_eq_mul, Nat.mul_comm]
    rw [h2]
    omega
  · have hsum2 : ∑ q ∈ (Finset.univ.erase q₀),
        (Finset.univ.filter (fun y : X => Quotient.mk (MulAction.orbitRel Γ X) y = q
          ∧ y ∈ Y)).card ≤ Y.card := by
      have hsub : (Finset.univ.erase q₀).biUnion (fun q : Q =>
          Finset.univ.filter (fun y : X => Quotient.mk (MulAction.orbitRel Γ X) y = q
            ∧ y ∈ Y)) ⊆ Y := by
        intro y hy
        rw [Finset.mem_biUnion] at hy
        obtain ⟨q, _, hyq⟩ := hy
        rw [Finset.mem_filter] at hyq
        exact hyq.2.2
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_biUnion (fun a _ b _ hne =>
        Finset.disjoint_left.mpr (fun y hy hy' => by
          rw [Finset.mem_filter] at hy hy'
          exact hne (by rw [← hy.2.1, ← hy'.2.1])))] at hcard
      exact hcard
    have hfib2 : ∀ q ∈ (Finset.univ.erase q₀),
        2 ≤ (Finset.univ.filter (fun y : X => Quotient.mk (MulAction.orbitRel Γ X) y = q
          ∧ y ∈ Y)).card := by
      intro q hq
      rw [Finset.mem_erase] at hq
      obtain ⟨x, rfl⟩ := Quotient.exists_rep q
      have hx : x ≠ x₀ := fun hxx => hq.1 (by rw [hxx])
      have h1 : (Finset.univ.filter (fun y : X =>
            Quotient.mk (MulAction.orbitRel Γ X) y = Quotient.mk (MulAction.orbitRel Γ X) x
              ∧ y ∈ Y)).card = (Y.filter (fun y => y ∈ MulAction.orbit Γ x)).card := by
        congr 1
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨fun h => ⟨h.2, (hmem y x).mp h.1⟩, fun h => ⟨(hmem y x).mpr h.2, h.1⟩⟩
      rw [h1]
      exact hY x hx
    calc 2 * (Fintype.card Q - 1) = 2 * (Finset.univ.erase q₀).card := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ q₀), Finset.card_univ]
      _ = ∑ _q ∈ (Finset.univ.erase q₀), 2 := by
          rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      _ ≤ ∑ q ∈ (Finset.univ.erase q₀), (Finset.univ.filter (fun y : X =>
            Quotient.mk (MulAction.orbitRel Γ X) y = q ∧ y ∈ Y)).card :=
          Finset.sum_le_sum hfib2
      _ ≤ Y.card := hsum2

/-- The orbit of `x` under `Γ`, as a `Finset`. -/
noncomputable def orbitFinset {Γ X : Type*} [Group Γ] [MulAction Γ X] [Fintype Γ] [Fintype X]
    (x : X) : Finset X :=
  Finset.univ.filter (fun y => y ∈ MulAction.orbit Γ x)

theorem orbitFinset_eq {Γ X : Type*} [Group Γ] [MulAction Γ X] [Fintype Γ] [Fintype X] (x : X) :
    orbitFinset (Γ := Γ) x = Finset.univ.filter (fun y => y ∈ MulAction.orbit Γ x) := rfl

@[simp] theorem mem_orbitFinset {Γ X : Type*} [Group Γ] [MulAction Γ X] [Fintype Γ] [Fintype X]
    {x y : X} : y ∈ orbitFinset (Γ := Γ) x ↔ y ∈ MulAction.orbit Γ x := by
  simp only [orbitFinset_eq, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Variant of `orbit_counting` for an invariant finite subset `Z`: if all orbits inside `Z`
have `l` elements and each meets the finite set `Y` in at least two points, then `#Z = l c` and
`2 c ≤ #Y`. -/
theorem orbit_counting_invariant {Γ X : Type*} [Group Γ] [MulAction Γ X] [Fintype Γ] [Fintype X]
    (Z Y : Finset X) (l : ℕ) (hZ : ∀ x ∈ Z, ∀ g : Γ, g • x ∈ Z)
    (horb : ∀ x ∈ Z, (Finset.univ.filter (fun y => y ∈ MulAction.orbit Γ x)).card = l)
    (hY : ∀ x ∈ Z, ∃ a ∈ Z, ∃ b ∈ Z, a ∈ MulAction.orbit Γ x ∧ b ∈ MulAction.orbit Γ x ∧
      a ∈ Y ∧ b ∈ Y ∧ a ≠ b) :
    ∃ c : ℕ, Z.card = l * c ∧ 2 * c ≤ Y.card := by
  classical
  set Orb : Finset (Finset X) := Z.image (orbitFinset (Γ := Γ)) with hOrbdef
  have hself : ∀ x ∈ Z, x ∈ orbitFinset (Γ := Γ) x := by
    intro x _
    exact mem_orbitFinset.mpr (MulAction.mem_orbit_iff.mpr ⟨1, by simp⟩)
  have hsubZ : ∀ x ∈ Z, ∀ y, y ∈ MulAction.orbit Γ x → y ∈ Z := by
    intro x hx y hy
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp hy
    rw [← hg]
    exact hZ x hx g
  have hcardOrb : ∀ O ∈ Orb, O.card = l := by
    intro O hO
    rw [hOrbdef] at hO
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hO
    rw [orbitFinset_eq]
    exact horb x hx
  have hdisj : ∀ O ∈ Orb, ∀ O' ∈ Orb, O ≠ O' → Disjoint O O' := by
    intro O hO O' hO' hne
    rw [hOrbdef] at hO hO'
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hO
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hO'
    rw [Finset.disjoint_left]
    intro z hz hz'
    rw [orbitFinset_eq] at hz hz'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz hz'
    have hxy : MulAction.orbit Γ x = MulAction.orbit Γ y := by
      rw [← MulAction.orbit_eq_iff.mpr hz, ← MulAction.orbit_eq_iff.mpr hz']
    exact hne (by rw [orbitFinset_eq, orbitFinset_eq, hxy])
  have hZeq : Z = Orb.biUnion id := by
    rw [hOrbdef]
    ext y
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · intro hy
      exact ⟨orbitFinset (Γ := Γ) y, ⟨y, hy, rfl⟩, hself y hy⟩
    · rintro ⟨O, ⟨x, hx, rfl⟩, hyO⟩
      exact hsubZ x hx y (mem_orbitFinset.mp hyO)
  refine ⟨Orb.card, ?_, ?_⟩
  · have h1 : (Orb.biUnion id).card = ∑ O ∈ Orb, O.card :=
      Finset.card_biUnion (t := id) (fun O hO O' hO' hne => hdisj O hO O' hO' hne)
    have h2 : ∑ O ∈ Orb, O.card = ∑ _O ∈ Orb, l :=
      Finset.sum_congr rfl (fun O hO => hcardOrb O hO)
    have h3 : ∑ _O ∈ Orb, l = l * Orb.card := by
      rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
    calc Z.card = (Orb.biUnion id).card := by rw [hZeq]
      _ = ∑ O ∈ Orb, O.card := h1
      _ = ∑ _O ∈ Orb, l := h2
      _ = l * Orb.card := h3
  · have hO2 : ∀ O ∈ Orb, 2 ≤ (O.filter (fun y => y ∈ Y)).card := by
      intro O hO
      rw [hOrbdef] at hO
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hO
      obtain ⟨a, haZ, b, hbZ, hao, hbo, haY, hbY, hab⟩ := hY x hx
      have hsub : ({a, b} : Finset X) ⊆ (orbitFinset (Γ := Γ) x).filter (fun y => y ∈ Y) := by
        intro y hy
        rw [Finset.mem_insert, Finset.mem_singleton] at hy
        rw [Finset.mem_filter]
        rcases hy with rfl | rfl
        · exact ⟨mem_orbitFinset.mpr hao, haY⟩
        · exact ⟨mem_orbitFinset.mpr hbo, hbY⟩
      have h2 : ({a, b} : Finset X).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simpa using hab), Finset.card_singleton]
      calc 2 = ({a, b} : Finset X).card := h2.symm
        _ ≤ _ := Finset.card_le_card hsub
    have hge : 2 * Orb.card ≤ ∑ O ∈ Orb, (O.filter (fun y => y ∈ Y)).card := by
      have hconst : (2 * Orb.card : ℕ) = ∑ _O ∈ Orb, 2 := by
        rw [Finset.sum_const, smul_eq_mul, Nat.mul_comm]
      rw [hconst]
      exact Finset.sum_le_sum (fun O hO => hO2 O hO)
    have hle : ∑ O ∈ Orb, (O.filter (fun y => y ∈ Y)).card ≤ Y.card := by
      have hdisjY : ∀ O ∈ Orb, ∀ O' ∈ Orb, O ≠ O' →
          Disjoint (O.filter (fun y => y ∈ Y)) (O'.filter (fun y => y ∈ Y)) :=
        fun O hO O' hO' hne => (hdisj O hO O' hO' hne).mono
          (Finset.filter_subset _ _) (Finset.filter_subset _ _)
      calc ∑ O ∈ Orb, (O.filter (fun y => y ∈ Y)).card
          = (Orb.biUnion (fun O => O.filter (fun y => y ∈ Y))).card :=
            (Finset.card_biUnion hdisjY).symm
        _ ≤ Y.card := Finset.card_le_card (fun y hy => by
            simp only [Finset.mem_biUnion, Finset.mem_filter] at hy
            obtain ⟨O, hO, hyO, hyY⟩ := hy
            exact hyY)
    exact le_trans hge hle

/-- Arithmetic step: with `n = 2 ^ a + 1`, `a ≥ 2`, `3 ∣ n`, `8 ∣ n * m - 1` and
`2 * (n * m - 1) ≤ 8 * (n - 1)` one has `m = 1`.

`3 ∣ 2 ^ a + 1` forces `a` odd, hence `a ≥ 3` and `8 ∣ 2 ^ a`, so `n ≡ 1 (mod 8)`; combined with
`8 ∣ n m - 1` this gives `m ≡ 1 (mod 8)`.  The inequality gives `n m ≤ 4 n - 3`, hence `m ≤ 3`.
With `1 ≤ m ≤ 3` and `m ≡ 1 (mod 8)` we get `m = 1`. -/
theorem m_eq_one_of_singer_arith {a m : ℕ} (ha : 2 ≤ a) (hm : 1 ≤ m) (h3 : 3 ∣ 2 ^ a + 1)
    (hdiv : 8 ∣ (2 ^ a + 1) * m - 1)
    (hbound : 2 * ((2 ^ a + 1) * m - 1) ≤ 8 * ((2 ^ a + 1) - 1)) : m = 1 := by
  -- `a` is odd
  have hodd : Odd a := by
    rw [← Nat.not_even_iff_odd]
    intro hev
    have h2a : (2 : ZMod 3) ^ a = -1 := by
      have h : ((2 ^ a + 1 : ℕ) : ZMod 3) = 0 := (ZMod.natCast_eq_zero_iff (2 ^ a + 1) 3).mpr h3
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_pow] at h
      exact eq_neg_of_add_eq_zero_left h
    obtain ⟨k, hk⟩ := even_iff_two_dvd.mp hev
    rw [hk, pow_mul] at h2a
    have h4 : (2 : ZMod 3) ^ 2 = 1 := by decide
    rw [h4, one_pow] at h2a
    exact absurd h2a (by decide)
  have ha3 : 3 ≤ a := by
    rcases hodd with ⟨j, hj⟩
    omega
  -- `8 ∣ 2 ^ a`
  have h8a : 8 ∣ 2 ^ a := by
    have h : 2 ^ a = 2 ^ 3 * 2 ^ (a - 3) := by rw [← pow_add]; congr 1; omega
    exact ⟨2 ^ (a - 3), by rw [h]; norm_num⟩
  -- `m ≤ 3`
  have hmle : m ≤ 3 := by
    have h1 : (2 ^ a + 1) * m - 1 ≤ 4 * ((2 ^ a + 1) - 1) := by
      have h : 2 * ((2 ^ a + 1) * m - 1) ≤ 2 * (4 * ((2 ^ a + 1) - 1)) := by
        calc 2 * ((2 ^ a + 1) * m - 1) ≤ 8 * ((2 ^ a + 1) - 1) := hbound
          _ = 2 * (4 * ((2 ^ a + 1) - 1)) := by ring
      exact Nat.le_of_mul_le_mul_left h (by norm_num)
    have h2 : (2 ^ a + 1) * m < (2 ^ a + 1) * 4 := by
      have hpos : 0 < 2 ^ a + 1 := by positivity
      omega
    have h3 : m < 4 := Nat.lt_of_mul_lt_mul_left h2
    omega
  -- `m ≡ 1 (mod 8)`
  have h8m : 8 ∣ m - 1 := by
    obtain ⟨u, hu⟩ := h8a
    obtain ⟨v, hv⟩ := hdiv
    have h : 8 * (u * m) + m = 8 * v + 1 := by
      have h1 : (2 ^ a + 1) * m = 8 * (u * m) + m := by rw [hu]; ring
      have h2 : (2 ^ a + 1) * m - 1 = 8 * v := hv
      omega
    refine ⟨v - u * m, by omega⟩
  obtain ⟨w, hw⟩ := h8m
  omega

/-- **`C_G(S.V) = S.V`** (Suzuki 1962, §8, pp. 117–118; Huppert–Blackburn III XI 10.8 (f)–(h)).

In the Zassenhaus split rank-one setting with `Q` a non-abelian `2`-group and `σ = ρ` (all
encoded in `SzHyp`), the centraliser in `G` of the Singer cycle `S.V` is `S.V` itself, given the
element structure `hD3` (every strongly real `x ≠ 1` with `x * x ≠ 1` is conjugate into `Q`, into
`twoPoint H t` or into `S.V`) and `hC1` (`C_G(k) = twoPoint H t` for `k ∈ twoPoint H t`).

This module is a copy of `Submission/Work/ZassenhausSuzuki/singerV_conj_inf_eq_bot.lean` (with the
declarations renamed into the namespace `Work.ZassenhausSuzuki.SelfCent`).  That file proves the
stronger statement "`W := C_G(S.V) = S.V` **and** distinct conjugates of `S.V` are trivial"; the
proof below stops at the internal step `have hWV : W = S.V`, which is precisely the goal here.
The route is Suzuki's: every `ω ∈ W#` is strongly real with `ω * ω ≠ 1`, so by `hD3` it is
conjugate into `Q`, `twoPoint H t` or `S.V` (the first two being impossible, `|W|` being odd and
`|twoPoint H t| = q - 1 < q + 1 ≤ |W|`); a `p`-torsion count with
`Work.ZassenhausSuzuki.prop14_normalizer_quotient_two` (`N_G(W)/W` is a `2`-group) and the
arithmetic of `m_eq_one_of_singer_arith` then gives `W = S.V`. -/
lemma singerV_selfcentralizing {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s : G}
    (h : Work.ZassenhausSuzuki.SzHyp H Q t s)
    (hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q)
    (S : Work.ZassenhausSuzuki.SingerCycle.Data G H t)
    (hD3 : ∀ x : G, x * x ≠ 1 →
      (∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = x) →
      (∃ g : G, g * x * g⁻¹ ∈ Q) ∨
        (∃ g : G, g * x * g⁻¹ ∈ Submission.Blueprint.twoPoint H t) ∨
        (∃ g : G, g * x * g⁻¹ ∈ S.V))
    (hC1 : ∀ k : G, k ∈ Submission.Blueprint.twoPoint H t → k ≠ 1 →
      Subgroup.centralizer ({k} : Set G) = Submission.Blueprint.twoPoint H t) :
    Subgroup.centralizer (S.V : Set G) = S.V := by
  classical
  -- ## cardinality data
  obtain ⟨a, ha2, hq2⟩ := Q0sub_card_eq_two_pow h
  have hVcard : Nat.card ↥(S.V) = 2 ^ a + 1 := by rw [S.card_V, hq2]
  have hV5 : 5 ≤ Nat.card ↥(S.V) := by
    rw [hVcard]
    have h4 : 4 ≤ 2 ^ a := by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha2
    omega
  have hVodd : Odd (Nat.card ↥(S.V)) := by
    rw [hVcard]
    obtain ⟨j, hj⟩ : ∃ j, 2 ^ a = 2 * j :=
      ⟨2 ^ (a - 1), by
        conv_lhs => rw [show a = (a - 1) + 1 from by omega, pow_succ']⟩
    exact ⟨j, by rw [hj]⟩
  -- ## W := C_G(S.V)
  set W : Subgroup G := Subgroup.centralizer (S.V : Set G) with hWdef
  -- a non-identity element of V
  have hVbot : ∃ v0 : G, v0 ∈ S.V ∧ v0 ≠ 1 := by
    by_contra hc
    push_neg at hc
    have hb : S.V = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      exact hc x hx
    rw [hb] at hV5
    simp at hV5
  obtain ⟨v0, hv0V, hv0ne⟩ := hVbot
  have hv02 : v0 * v0 ≠ 1 := by
    intro h2
    have hdvd : orderOf v0 ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]; simpa [pow_two] using h2
    have hodd : Odd (orderOf v0) := hVodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard S.V hv0V)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact hv0ne (orderOf_eq_one_iff.mp h1)
    · rw [h1] at hodd; exact absurd hodd (by decide)
  -- ## Proposition 14 at `v0`
  obtain ⟨a0, b0, ha0, hb0, hab0⟩ := S.stronglyReal v0 hv0V
  obtain ⟨hAbelian, hAodd, hAcent⟩ :=
    centralizer_abelian_of_strongly_real h.split h.zass h.two hv02 ⟨a0, b0, ha0, hb0, hab0⟩
  set A : Subgroup G := Subgroup.centralizer ({v0} : Set G) with hAdef
  have hVA : S.V ≤ A := by
    intro v hv
    rw [hAdef, Subgroup.mem_centralizer_singleton_iff]
    haveI : IsCyclic ↥(S.V) := S.cyclic
    exact congrArg Subtype.val (mul_comm' (⟨v, hv⟩ : ↥S.V) (⟨v0, hv0V⟩ : ↥S.V))
  have hcentA : A = W := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [hWdef, Subgroup.mem_centralizer_iff]
      intro v hv
      have hvA : v ∈ A := hVA hv
      haveI := hAbelian
      exact congrArg Subtype.val (mul_comm' (⟨v, hvA⟩ : ↥A) (⟨x, hx⟩ : ↥A))
    · intro x hx
      rw [hAdef, Subgroup.mem_centralizer_singleton_iff]
      exact ((Subgroup.mem_centralizer_iff.mp hx) v0 hv0V).symm
  have hWodd : Odd (Nat.card ↥W) := by rw [← hcentA]; exact hAodd
  have hVW : S.V ≤ W := by
    intro v hv
    rw [hWdef, Subgroup.mem_centralizer_iff]
    intro w hw
    haveI : IsCyclic ↥(S.V) := S.cyclic
    exact congrArg Subtype.val (mul_comm' (⟨w, hw⟩ : ↥S.V) (⟨v, hv⟩ : ↥S.V))
  have hcentW : ∀ z ∈ W, z ≠ 1 → Subgroup.centralizer ({z} : Set G) = W := by
    intro z hz hz1
    have hzA : z ∈ A := by rw [hcentA]; exact hz
    have h1 : Subgroup.centralizer ({z} : Set G)
        = Subgroup.centralizer ({v0} : Set G) := (hAcent z hzA hz1).2
    rw [h1, ← hAdef]
    exact hcentA
  have hstrongW : ∀ z ∈ W, z ≠ 1 → ∃ a b : G, a * a = 1 ∧ b * b = 1 ∧ a * b = z := by
    intro z hz hz1
    exact (hAcent z (by rw [hcentA]; exact hz) hz1).1
  have hsqW : ∀ z ∈ W, z ≠ 1 → z * z ≠ 1 := by
    intro z hz hz1
    have hodd : Odd (orderOf z) := hWodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard W hz)
    rcases hodd with ⟨k, hk⟩
    intro h2
    have hdvd : orderOf z ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]; simpa [pow_two] using h2
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h3 | h3
    · exact hz1 (orderOf_eq_one_iff.mp h3)
    · rw [h3] at hk; omega
  -- ## every element of `W#` is conjugate into `V#`
  have hconjV : ∀ z ∈ W, z ≠ 1 → ∃ g : G, g * z * g⁻¹ ∈ S.V := by
    intro z hz hz1
    have hz2 := hsqW z hz hz1
    have hzsr := hstrongW z hz hz1
    rcases hD3 z hz2 hzsr with ⟨g, hg⟩ | ⟨g, hg⟩ | ⟨g, hg⟩
    · -- the `Q`-case is impossible
      exfalso
      obtain ⟨e, he⟩ := h.two.exists_card_eq
      have h1 : orderOf z ∣ 2 ^ e := by
        have h2 : orderOf (g * z * g⁻¹) = orderOf z := Work.ThmF.Bender.orderOf_conj_eq g z
        rw [← h2, ← he]
        exact Subgroup.orderOf_dvd_natCard Q hg
      have hodd : Odd (orderOf z) := hWodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard W hz)
      have hcop : Nat.Coprime (orderOf z) (2 ^ e) :=
        Nat.Coprime.pow_right e hodd.coprime_two_right
      exact hz1 (orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop dvd_rfl h1))
    · -- the `twoPoint`-case is impossible
      exfalso
      have hk1 : g * z * g⁻¹ ≠ 1 := by
        intro hc
        apply hz1
        calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
          _ = 1 := by rw [hc]; group
      have hcentk : Subgroup.centralizer ({g * z * g⁻¹} : Set G)
          = Submission.Blueprint.twoPoint H t := hC1 (g * z * g⁻¹) hg hk1
      have hmap : Subgroup.map (MulAut.conj g).toMonoidHom
            (Subgroup.centralizer ({z} : Set G))
          = Subgroup.centralizer ({g * z * g⁻¹} : Set G) := by
        ext y
        simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
        constructor
        · rintro ⟨x, hx, rfl⟩
          show MulAut.conj g x * MulAut.conj g z = MulAut.conj g z * MulAut.conj g x
          rw [← map_mul, ← map_mul, hx]
        · intro hy
          refine ⟨g⁻¹ * y * g, ?_, ?_⟩
          · show (g⁻¹ * y * g) * z = z * (g⁻¹ * y * g)
            calc (g⁻¹ * y * g) * z = g⁻¹ * (y * (g * z * g⁻¹)) * g := by group
              _ = g⁻¹ * ((g * z * g⁻¹) * y) * g := by rw [hy]
              _ = z * (g⁻¹ * y * g) := by group
          · show MulAut.conj g (g⁻¹ * y * g) = y
            rw [MulAut.conj_apply]
            group
      have hcard : Nat.card ↥W = Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
        rw [← hcentW z hz hz1, ← hcentk, ← hmap]
        exact (Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
          (MulAut.conj g).injective (K := Subgroup.centralizer ({z} : Set G))).symm
      have hK : Nat.card ↥(Submission.Blueprint.twoPoint H t)
          = Nat.card ↥(Work.ThmF.Q0sub H) - 1 := twoPoint_card_eq_Q0sub_sub_one h
      have hle : Nat.card ↥(S.V) ≤ Nat.card ↥W :=
        Nat.card_le_card_of_injective (f := fun x : ↥S.V => (⟨(x : G), hVW x.2⟩ : ↥W))
          (fun a b hab => by simpa using hab)
      omega
    · exact ⟨g, hg⟩
  have hordW : ∀ z ∈ W, z ≠ 1 → orderOf z ∣ Nat.card ↥(S.V) := by
    intro z hz hz1
    obtain ⟨g, hg⟩ := hconjV z hz hz1
    rw [← Work.ThmF.Bender.orderOf_conj_eq g z]
    exact Subgroup.orderOf_dvd_natCard S.V hg
  -- ## `N := N_G(W)`, `l := [N : W]`, and the conjugation action of `N` on `W`
  set N : Subgroup G := Subgroup.normalizer (W : Set G) with hNdef
  have hWN : W ≤ N := Subgroup.le_normalizer
  haveI fintypeW : Fintype ↥W := Fintype.ofFinite _
  haveI fintypeN : Fintype ↥N := Fintype.ofFinite _
  haveI fintypeV : Fintype ↥(S.V) := Fintype.ofFinite _
  -- `Mathlib` provides the conjugation action `↥N ↥W` (with `g • x = g x g⁻¹`).
  set l : ℕ := (W.subgroupOf N).index with hldef
  have hNcard : Nat.card ↥N = Nat.card ↥W * l := by
    have h1 := Subgroup.card_mul_index (W.subgroupOf N)
    have h2 : Nat.card ↥(W.subgroupOf N) = Nat.card ↥W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWN).toEquiv
    rw [h2] at h1
    rw [← h1, hldef]
  obtain ⟨k, hk⟩ := prop14_normalizer_quotient_two h hv02 ⟨a0, b0, ha0, hb0, hab0⟩
  have hl2 : l = 2 ^ k := by
    rw [← hAdef, hcentA] at hk
    exact Nat.mul_left_cancel (Nat.card_pos (α := ↥W)) (by rw [← hNcard, hk])
  -- `τ ∈ N \ W`, hence `l ≥ 2`
  obtain ⟨τ, hτX5, hτ2, hτinv⟩ := S.inverting
  have hτinv' : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ2
  have hτconjW : ∀ x : G, x ∈ W → τ * x * τ⁻¹ ∈ W := by
    intro x hx
    rw [hWdef, Subgroup.mem_centralizer_iff] at hx ⊢
    intro v hv
    have hvinv : τ⁻¹ * v * τ ∈ S.V := by
      have h1 : τ⁻¹ * v * τ = v⁻¹ := by rw [hτinv']; exact hτinv v hv
      rw [h1]; exact S.V.inv_mem hv
    have hxc := hx (τ⁻¹ * v * τ) hvinv
    calc v * (τ * x * τ⁻¹) = τ * ((τ⁻¹ * v * τ) * x) * τ⁻¹ := by group
      _ = τ * (x * (τ⁻¹ * v * τ)) * τ⁻¹ := by rw [hxc]
      _ = (τ * x * τ⁻¹) * v := by group
  have hτN : τ ∈ N := by
    rw [hNdef, Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hτconjW x hx, fun hx => by
      have h1 := hτconjW (τ * x * τ⁻¹) hx
      have h2 : τ * (τ * x * τ⁻¹) * τ⁻¹ = x := by
        calc τ * (τ * x * τ⁻¹) * τ⁻¹ = (τ * τ) * (x * (τ⁻¹ * τ⁻¹)) := by group
          _ = x := by rw [hτ2, ← mul_inv_rev τ τ, hτ2, inv_one]; group
      rwa [h2] at h1⟩
  have hτnotW : τ ∉ W := by
    intro hτw
    have hc := (Subgroup.mem_centralizer_iff.mp (hWdef ▸ hτw)) v0 hv0V
    have h1 : τ * v0 * τ⁻¹ = v0⁻¹ := by rw [hτinv']; exact hτinv v0 hv0V
    have h2 : τ * v0 * τ⁻¹ = v0 := by rw [← hc]; group
    have h3 : v0⁻¹ = v0 := by rw [← h1, h2]
    refine hv02 ?_
    calc v0 * v0 = v0 * v0⁻¹ := by rw [h3]
      _ = 1 := mul_inv_cancel v0
  have hlge2 : 2 ≤ l := by
    by_contra hcon
    have hl1 : l ≤ 1 := by omega
    interval_cases l
    · exfalso
      rw [mul_zero] at hNcard
      exact (Nat.card_pos (α := ↥N)).ne' hNcard
    · exfalso
      have hWN' : W = N := Subgroup.eq_of_le_of_card_ge hWN (by rw [hNcard, mul_one])
      exact hτnotW (hWN' ▸ hτN)
  -- ## orbit facts for the action of `N` on `W`
  have hstab : ∀ z : ↥W, (z : G) ≠ 1 → MulAction.stabilizer ↥N z = W.subgroupOf N := by
    intro z hz
    have hcW : Subgroup.centralizer (Set.singleton ((z : G))) = W := hcentW (z : G) z.2 hz
    ext g
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro hg
      have h2 : ((g : G)) * (z : G) * ((g : G))⁻¹ = (z : G) := by
        show ((g • z : ↥W) : G) = ((z : ↥W) : G)
        exact congrArg (fun w : ↥W => (w : G)) hg
      have h3 : ((g : G)) * (z : G) = (z : G) * ((g : G)) := by
        calc (g : G) * (z : G) = ((g : G) * (z : G) * ((g : G))⁻¹) * (g : G) := by group
          _ = (z : G) * (g : G) := by rw [h2]
      have h4 : (g : G) ∈ Subgroup.centralizer (Set.singleton ((z : G))) :=
        Subgroup.mem_centralizer_singleton_iff.mpr h3
      rwa [hcW] at h4
    · intro hg
      have h4 : (g : G) ∈ Subgroup.centralizer (Set.singleton ((z : G))) := by
        rw [hcW]; exact Subgroup.mem_subgroupOf.mp hg
      have h3 : ((g : G)) * (z : G) = (z : G) * ((g : G)) :=
        Subgroup.mem_centralizer_singleton_iff.mp h4
      show (g • z : ↥W) = z
      apply Subtype.ext
      show ((g : G) * (z : G) * ((g : G))⁻¹) = ((z : ↥W) : G)
      rw [h3]; group
  have horbit : ∀ z : ↥W, (z : G) ≠ 1 → Nat.card (MulAction.orbit ↥N z) = l := by
    haveI : Fintype ↥N := Fintype.ofFinite _
    haveI : Fintype ↥W := Fintype.ofFinite _
    intro z hz
    have h1 := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := ↥N) z
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card] at h1
    rw [hstab z hz] at h1
    have hcardW : Nat.card ↥(W.subgroupOf N) = Nat.card ↥W :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWN).toEquiv
    rw [hcardW, hNcard, Nat.mul_comm (Nat.card (MulAction.orbit ↥N z)) (Nat.card ↥W)] at h1
    exact Nat.mul_left_cancel (Nat.card_pos (α := ↥W)) h1
  have horbit1 : MulAction.orbit ↥N (1 : ↥W) = {1} := by
    ext z
    constructor
    · intro hz
      rw [MulAction.mem_orbit_iff] at hz
      obtain ⟨g, hg⟩ := hz
      rw [← hg, Set.mem_singleton_iff]
      apply Subtype.ext
      show (g : G) * ((1 : ↥W) : G) * (g : G)⁻¹ = ((1 : ↥W) : G)
      rw [Subgroup.coe_one]
      group
    · intro hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact ⟨1, one_smul ↥N (1 : ↥W)⟩
  have hmeet : ∀ z : ↥W, z ≠ 1 →
      2 ≤ ((Finset.univ.filter (fun w : ↥W => (w : G) ∈ S.V ∧ w ≠ 1)).filter
        (fun w => w ∈ MulAction.orbit ↥N z)).card := by
    intro z hz1
    have hz : (z : G) ≠ 1 := fun h => hz1 (Subtype.ext h)
    obtain ⟨g, hg⟩ := hconjV (z : G) z.2 hz
    have hvW : g * (z : G) * g⁻¹ ∈ W := hVW hg
    have hvne : g * (z : G) * g⁻¹ ≠ 1 := by
      intro hc
      exact hz (by
        calc (z : G) = g⁻¹ * (g * (z : G) * g⁻¹) * g := by group
          _ = 1 := by rw [hc]; group)
    set v : ↥W := ⟨g * (z : G) * g⁻¹, hvW⟩ with hvdef
    have hvV : (v : G) ∈ S.V := hvdef ▸ hg
    have hvne' : v ≠ 1 := fun h => hvne (congrArg (fun w : ↥W => (w : G)) h)
    have hvval : (v : G) = g * (z : G) * g⁻¹ := by rw [hvdef]
    have hvval : (v : G) = g * (z : G) * g⁻¹ := by rw [hvdef]
    have hgN : g ∈ N := by
      rw [hNdef, Subgroup.mem_normalizer_iff]
      intro x
      have hcx : Subgroup.centralizer (Set.singleton ((z : G))) = W := hcentW (z : G) z.2 hz
      have hcv : Subgroup.centralizer (Set.singleton ((v : G))) = W :=
        hcentW (v : G) v.2 (fun h => hvne' (Subtype.ext h))
      have keyz : ∀ y : G, y ∈ W ↔ y * (z : G) = (z : G) * y := by
        intro y
        exact (show y ∈ W ↔ y ∈ Subgroup.centralizer (Set.singleton ((z : G))) from by
          rw [hcx]).trans Subgroup.mem_centralizer_singleton_iff
      have keyv : ∀ y : G, y ∈ W ↔ y * (v : G) = (v : G) * y := by
        intro y
        exact (show y ∈ W ↔ y ∈ Subgroup.centralizer (Set.singleton ((v : G))) from by
          rw [hcv]).trans Subgroup.mem_centralizer_singleton_iff
      constructor
      · intro hx
        have h2 : x * (z : G) = (z : G) * x := (keyz x).mp hx
        have h3 : (g * x * g⁻¹) * (v : G) = (v : G) * (g * x * g⁻¹) := by
          rw [hvval]
          calc (g * x * g⁻¹) * (g * (z : G) * g⁻¹) = g * (x * (z : G)) * g⁻¹ := by group
            _ = g * ((z : G) * x) * g⁻¹ := by rw [h2]
            _ = (g * (z : G) * g⁻¹) * (g * x * g⁻¹) := by group
        exact (keyv (g * x * g⁻¹)).mpr h3
      · intro hx
        have h2 : (g * x * g⁻¹) * (v : G) = (v : G) * (g * x * g⁻¹) :=
          (keyv (g * x * g⁻¹)).mp hx
        rw [hvval] at h2
        have h3 : x * (z : G) = (z : G) * x := by
          calc x * (z : G) = g⁻¹ * ((g * x * g⁻¹) * (g * (z : G) * g⁻¹)) * g := by group
            _ = g⁻¹ * ((g * (z : G) * g⁻¹) * (g * x * g⁻¹)) * g := by rw [h2]
            _ = (z : G) * x := by group
        exact (keyz x).mpr h3
    have hmemv : v ∈ MulAction.orbit ↥N z := by
      rw [MulAction.mem_orbit_iff]
      refine ⟨⟨g, hgN⟩, ?_⟩
      apply Subtype.ext
      rw [hvval]
      rfl
    have hmemvinv : v⁻¹ ∈ MulAction.orbit ↥N z := by
      have hτact : (⟨τ, hτN⟩ : ↥N) • v = v⁻¹ := by
        apply Subtype.ext
        show τ * (v : G) * τ⁻¹ = ((v⁻¹ : ↥W) : G)
        rw [hτinv', Subgroup.coe_inv]
        exact hτinv v hvV
      rw [← hτact]
      have hvz : MulAction.orbit (↥N) v = MulAction.orbit (↥N) z :=
        MulAction.orbit_eq_iff.mpr hmemv
      rw [← hvz]
      exact MulAction.mem_orbit (γ := ↥N) v ⟨τ, hτN⟩
    have hne : v ≠ v⁻¹ := by
      intro hc
      have h2 : (v : G) * (v : G) = 1 :=
        mul_eq_one_iff_eq_inv.mpr (congrArg (fun w : ↥W => (w : G)) hc)
      have h3 : orderOf (v : G) ∣ 2 := by
        rw [orderOf_dvd_iff_pow_eq_one]; simpa [pow_two] using h2
      have h4 : Odd (orderOf (v : G)) :=
        hVodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard S.V hvV)
      rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h5 | h5
      · exact hvne' (Subtype.ext (orderOf_eq_one_iff.mp h5))
      · rw [h5] at h4; exact absurd h4 (by decide)
    have hsub : ({v, v⁻¹} : Finset ↥W) ⊆
        (Finset.univ.filter (fun w : ↥W => (w : G) ∈ S.V ∧ w ≠ 1)).filter
          (fun w => w ∈ MulAction.orbit ↥N z) := by
      intro w hw
      rw [Finset.mem_insert, Finset.mem_singleton] at hw
      rw [Finset.mem_filter, Finset.mem_filter]
      rcases hw with rfl | rfl
      · exact ⟨⟨Finset.mem_univ _, hvV, hvne'⟩, hmemv⟩
      · exact ⟨⟨Finset.mem_univ _, S.V.inv_mem hvV, fun h => hvne' (inv_eq_one.mp h)⟩,
          hmemvinv⟩
    have h2 : ({v, v⁻¹} : Finset ↥W).card ≤ _ := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton] at h2
    omega
  -- ## the count on `W#`
  obtain ⟨c, hc1, hc2⟩ := orbit_counting (Γ := ↥N) (X := ↥W) 1 horbit1 l
    (fun x hx => by
      rw [← Nat.card_eq_fintype_card]
      exact horbit x (fun h => hx (Subtype.ext h)))
    (Finset.univ.filter (fun w : ↥W => (w : G) ∈ S.V ∧ w ≠ 1))
    (fun x hx => hmeet x hx)
  have hYcard : (Finset.univ.filter (fun w : ↥W => (w : G) ∈ S.V ∧ w ≠ 1)).card
      = Nat.card ↥(S.V) - 1 := by
    rw [← Fintype.card_subtype]
    have hbij : {w : ↥W // (w : G) ∈ S.V ∧ w ≠ 1} ≃ {v : ↥(S.V) // v ≠ 1} :=
      { toFun := fun w => ⟨⟨(w.1 : G), w.2.1⟩,
          fun h => w.2.2 (Subtype.ext (congrArg (fun t : ↥(S.V) => (t : G)) h))⟩
        invFun := fun v => ⟨⟨(v.1 : G), hVW v.1.2⟩, v.1.2,
          fun h => v.2 (Subtype.ext (congrArg (fun t : ↥W => (t : G)) h))⟩
        left_inv := fun w => by ext <;> rfl
        right_inv := fun v => by ext <;> rfl }
    rw [Fintype.card_congr hbij]
    rw [show Fintype.card {v : ↥(S.V) // v ≠ 1} = (Finset.univ.erase (1 : ↥(S.V))).card from by
      rw [Fintype.card_subtype]
      congr 1
      ext v
      simp [Finset.mem_filter, Finset.mem_erase]]
    rw [Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ, Nat.card_eq_fintype_card]
  have hcount : 2 * (Nat.card ↥W - 1) ≤ l * (Nat.card ↥(S.V) - 1) := by
    have h1 : 2 * (Nat.card ↥W - 1) = l * (2 * c) := by
      rw [show Nat.card ↥W - 1 = Fintype.card ↥W - 1 from by rw [Nat.card_eq_fintype_card], hc1]
      ring
    rw [h1]
    exact Nat.mul_le_mul_left l (hYcard ▸ hc2)
  -- ## `m := [W : V]`
  set m : ℕ := (S.V.subgroupOf W).index with hmdef
  have hWcard : Nat.card ↥W = Nat.card ↥(S.V) * m := by
    have h1 := Subgroup.card_mul_index (S.V.subgroupOf W)
    have h2 : Nat.card ↥(S.V.subgroupOf W) = Nat.card ↥(S.V) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVW).toEquiv
    rw [h2] at h1
    rw [← h1, hmdef]
  -- ## the main case distinction, proving `W = S.V`
  have hcommW : IsMulCommutative ↥W := by rw [← hcentA]; exact hAbelian
  have hWV : W = S.V := by
    by_cases hcycW : @IsCyclic ↥W (@ZPow.toPow ↥W _)
    · -- Case A: `W` is cyclic
      haveI hci : @IsCyclic ↥W (@ZPow.toPow ↥W _) := hcycW
      obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥W)
      have hg1 : (g : G) ≠ 1 := by
        intro h1
        have hg' : g = 1 := Subtype.ext h1
        rw [hg', orderOf_one] at hg
        have hle : Nat.card ↥(S.V) ≤ Nat.card ↥W :=
          Nat.card_le_card_of_injective (f := fun x : ↥S.V => (⟨(x : G), hVW x.2⟩ : ↥W))
            (fun a b hab => by simpa using hab)
        omega
      have hdvd : Nat.card ↥W ∣ Nat.card ↥(S.V) := by
        rw [← hg, ← Subgroup.orderOf_coe g]
        exact hordW (g : G) g.2 hg1
      have hdvd' : Nat.card ↥(S.V) ∣ Nat.card ↥W := ⟨m, hWcard⟩
      have hcardVW : Nat.card ↥W = Nat.card ↥(S.V) := Nat.dvd_antisymm hdvd hdvd'
      exact (Subgroup.eq_of_le_of_card_ge hVW (le_of_eq hcardVW)).symm
    · -- Case B: `W` is not cyclic
      obtain ⟨p, hpp, hptor⟩ := exists_prime_ptorsion_sq_le_of_not_isCyclic (B := ↥W) hcommW hcycW
      letI hCW : CommGroup ↥W :=
        { toGroup := (inferInstance : Group ↥W)
          mul_comm := fun a b => hcommW.is_comm.comm a b }
      obtain ⟨r, hr⟩ := ptorsion_card_eq_prime_pow (B := ↥W) p hpp
      have hr2 : 2 ≤ r := by
        by_contra hcon
        have hr1 : r ≤ 1 := by omega
        have hle : p ^ r ≤ p := by
          calc p ^ r ≤ p ^ 1 := Nat.pow_le_pow_right hpp.one_le hr1
            _ = p := pow_one p
        rw [hr] at hptor
        have hp2 : 2 ≤ p := hpp.two_le
        nlinarith [hptor, hle, hp2]
      -- ## the nonidentity `p`-torsion `Z` and its part `Y` inside `V`
      set Z : Finset ↥W := Finset.univ.filter (fun x : ↥W => x ^ p = 1 ∧ x ≠ 1) with hZdef
      set Y : Finset ↥W :=
        Finset.univ.filter (fun x : ↥W => (x : G) ∈ S.V ∧ x ≠ 1 ∧ x ^ p = 1) with hYdef
      have hZcard : Z.card = p ^ r - 1 := by
        have h1 : Z = (Finset.univ.filter (fun x : ↥W => x ^ p = 1)).erase 1 := by
          ext x
          simp only [hZdef, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
          tauto
        rw [h1, Finset.card_erase_of_mem (by simp)]
        rw [show (Finset.univ.filter (fun x : ↥W => x ^ p = 1)).card
              = Nat.card {x : ↥W // x ^ p = 1} from by
                rw [← Fintype.card_subtype (fun x : ↥W => x ^ p = 1), Nat.card_eq_fintype_card],
            hr]
      -- conjugation by `N` preserves the `p`-torsion
      have hmul_pow : ∀ (g : ↥N) (x : ↥W), x ^ p = 1 → (g • x) ^ p = 1 := by
        intro g x hx
        apply Subtype.ext
        have hxg : (x : G) ^ p = 1 := by
          have h := congrArg (fun t : ↥W => (t : G)) hx
          simpa using h
        show ((g • x : ↥W) : G) ^ p = ((1 : ↥W) : G)
        rw [Subgroup.coe_one]
        rw [show ((g • x : ↥W) : G) = (g : G) * (x : G) * ((g : G))⁻¹ from rfl]
        calc ((g : G) * (x : G) * ((g : G))⁻¹) ^ p
            = (MulAut.conj (g : G)) ((x : G) ^ p) := by rw [map_pow, MulAut.conj_apply]
          _ = 1 := by rw [hxg, map_one]
      have hZinv : ∀ x ∈ Z, ∀ g : ↥N, g • x ∈ Z := by
        intro x hx g
        rw [hZdef] at hx ⊢
        obtain ⟨-, hxp, hxne⟩ := Finset.mem_filter.mp hx
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmul_pow g x hxp, fun h => hxne ?_⟩
        apply Subtype.ext
        have h1 : ((g • x : ↥W) : G) = 1 := by rw [h]; rfl
        show (x : G) = 1
        rw [show (x : G) = ((g : G))⁻¹ * ((g • x : ↥W) : G) * (g : G) from by
          rw [show ((g • x : ↥W) : G) = (g : G) * (x : G) * ((g : G))⁻¹ from rfl]
          group]
        rw [h1]; group
      have horbZ : ∀ x ∈ Z,
          (Finset.univ.filter (fun y : ↥W => y ∈ MulAction.orbit (↥N) x)).card = l := by
        intro x hx
        rw [hZdef] at hx
        have hxne : (x : G) ≠ 1 := fun h => (Finset.mem_filter.mp hx).2.2 (Subtype.ext h)
        rw [show (Finset.univ.filter (fun y : ↥W => y ∈ MulAction.orbit (↥N) x)).card
              = Fintype.card (MulAction.orbit (↥N) x) from (Fintype.card_subtype _).symm,
            ← Nat.card_eq_fintype_card]
        exact horbit x hxne
      have hYZ : ∀ x ∈ Z, ∃ a ∈ Z, ∃ b ∈ Z, a ∈ MulAction.orbit (↥N) x ∧
          b ∈ MulAction.orbit (↥N) x ∧ a ∈ Y ∧ b ∈ Y ∧ a ≠ b := by
        intro x hx
        rw [hZdef] at hx
        obtain ⟨-, hxpe, hxne⟩ := Finset.mem_filter.mp hx
        have hxGne : (x : G) ≠ 1 := fun h => hxne (Subtype.ext h)
        obtain ⟨g, hg⟩ := hconjV (x : G) x.2 hxGne
        have hvW : g * (x : G) * g⁻¹ ∈ W := hVW hg
        have hvne : g * (x : G) * g⁻¹ ≠ 1 := by
          intro hc
          exact hxGne (by
            calc (x : G) = g⁻¹ * (g * (x : G) * g⁻¹) * g := by group
              _ = 1 := by rw [hc]; group)
        set v : ↥W := ⟨g * (x : G) * g⁻¹, hvW⟩ with hvdef
        have hvval : (v : G) = g * (x : G) * g⁻¹ := by rw [hvdef]
        have hvV : (v : G) ∈ S.V := hg
        have hvne' : v ≠ 1 := fun h => hvne (congrArg (fun w : ↥W => (w : G)) h)
        have hgN : g ∈ N := by
          rw [hNdef, Subgroup.mem_normalizer_iff]
          intro c
          have hcx : Subgroup.centralizer (Set.singleton ((x : G))) = W :=
            hcentW (x : G) x.2 hxGne
          have hcv : Subgroup.centralizer (Set.singleton ((v : G))) = W :=
            hcentW (v : G) v.2 (fun h => hvne' (Subtype.ext h))
          have keyz : ∀ y : G, y ∈ W ↔ y * (x : G) = (x : G) * y := by
            intro y
            exact (show y ∈ W ↔ y ∈ Subgroup.centralizer (Set.singleton ((x : G))) from by
              rw [hcx]).trans Subgroup.mem_centralizer_singleton_iff
          have keyv : ∀ y : G, y ∈ W ↔ y * (v : G) = (v : G) * y := by
            intro y
            exact (show y ∈ W ↔ y ∈ Subgroup.centralizer (Set.singleton ((v : G))) from by
              rw [hcv]).trans Subgroup.mem_centralizer_singleton_iff
          constructor
          · intro hc
            have h2 : c * (x : G) = (x : G) * c := (keyz c).mp hc
            have h3 : (g * c * g⁻¹) * (v : G) = (v : G) * (g * c * g⁻¹) := by
              rw [hvval]
              calc (g * c * g⁻¹) * (g * (x : G) * g⁻¹) = g * (c * (x : G)) * g⁻¹ := by group
                _ = g * ((x : G) * c) * g⁻¹ := by rw [h2]
                _ = (g * (x : G) * g⁻¹) * (g * c * g⁻¹) := by group
            exact (keyv (g * c * g⁻¹)).mpr h3
          · intro hc
            have h2 : (g * c * g⁻¹) * (v : G) = (v : G) * (g * c * g⁻¹) :=
              (keyv (g * c * g⁻¹)).mp hc
            rw [hvval] at h2
            have h3 : c * (x : G) = (x : G) * c := by
              calc c * (x : G) = g⁻¹ * ((g * c * g⁻¹) * (g * (x : G) * g⁻¹)) * g := by group
                _ = g⁻¹ * ((g * (x : G) * g⁻¹) * (g * c * g⁻¹)) * g := by rw [h2]
                _ = (x : G) * c := by group
            exact (keyz c).mpr h3
        have hmemv : v ∈ MulAction.orbit (↥N) x := by
          rw [MulAction.mem_orbit_iff]
          refine ⟨⟨g, hgN⟩, ?_⟩
          apply Subtype.ext
          rw [hvval]
          rfl
        have hmemvinv : v⁻¹ ∈ MulAction.orbit (↥N) x := by
          have hτact : (⟨τ, hτN⟩ : ↥N) • v = v⁻¹ := by
            apply Subtype.ext
            show τ * (v : G) * τ⁻¹ = ((v⁻¹ : ↥W) : G)
            rw [hτinv', Subgroup.coe_inv]
            exact hτinv v hvV
          rw [← hτact]
          have hvz : MulAction.orbit (↥N) v = MulAction.orbit (↥N) x :=
            MulAction.orbit_eq_iff.mpr hmemv
          rw [← hvz]
          exact MulAction.mem_orbit (γ := ↥N) v ⟨τ, hτN⟩
        have hne : v ≠ v⁻¹ := by
          intro hc
          have h2 : (v : G) * (v : G) = 1 :=
            mul_eq_one_iff_eq_inv.mpr (congrArg (fun w : ↥W => (w : G)) hc)
          have h3 : orderOf (v : G) ∣ 2 := by
            rw [orderOf_dvd_iff_pow_eq_one]; simpa [pow_two] using h2
          have h4 : Odd (orderOf (v : G)) :=
            hVodd.of_dvd_nat (Subgroup.orderOf_dvd_natCard S.V hvV)
          rcases (Nat.dvd_prime Nat.prime_two).mp h3 with h5 | h5
          · exact hvne' (Subtype.ext (orderOf_eq_one_iff.mp h5))
          · rw [h5] at h4; exact absurd h4 (by decide)
        have hvp : v ^ p = 1 := by
          have h1 : v = (⟨g, hgN⟩ : ↥N) • x := by
            apply Subtype.ext
            rw [hvval]
            rfl
          rw [h1]
          exact hmul_pow ⟨g, hgN⟩ x hxpe
        have hvinvp : (v⁻¹ : ↥W) ^ p = 1 := by rw [inv_pow, hvp, inv_one]
        refine ⟨v, ?_, v⁻¹, ?_, hmemv, hmemvinv, ?_, ?_, hne⟩
        · rw [hZdef]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvp, hvne'⟩
        · rw [hZdef]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvinvp, fun h => hvne' (inv_eq_one.mp h)⟩
        · rw [hYdef]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvV, hvne', hvp⟩
        · rw [hYdef]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, S.V.inv_mem hvV,
            fun h => hvne' (inv_eq_one.mp h), hvinvp⟩
      obtain ⟨c₂, he1, he2⟩ :=
        orbit_counting_invariant (Γ := ↥N) (X := ↥W) Z Y l hZinv horbZ hYZ
      -- ## `Y` has at most `p - 1` elements
      have hYle : Y.card ≤ p - 1 := by
        have hYeq : Y =
            (Finset.univ.filter (fun x : ↥W => (x : G) ∈ S.V ∧ x ^ p = 1)).erase 1 := by
          ext x
          simp only [hYdef, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
          constructor
          · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩
          · rintro ⟨h1, h2, h3⟩; exact ⟨h2, h1, h3⟩
        rw [hYeq, Finset.card_erase_of_mem (by simp)]
        haveI hcycV : IsCyclic ↥(S.V) := S.cyclic
        have hcard : (Finset.univ.filter (fun x : ↥W => (x : G) ∈ S.V ∧ x ^ p = 1)).card
            ≤ (Finset.univ.filter (fun v : ↥(S.V) => v ^ p = 1)).card := by
          rw [show (Finset.univ.filter (fun x : ↥W => (x : G) ∈ S.V ∧ x ^ p = 1)).card
                = Fintype.card {x : ↥W // (x : G) ∈ S.V ∧ x ^ p = 1} from
                  (Fintype.card_subtype _).symm]
          refine le_trans (Fintype.card_le_of_injective
            (fun x : {x : ↥W // (x : G) ∈ S.V ∧ x ^ p = 1} =>
              (⟨⟨(x.1 : G), x.2.1⟩, ?_⟩ : {v : ↥(S.V) // v ^ p = 1})) ?_) ?_
          · exact Subtype.ext (by
              have h := congrArg (fun t : ↥W => (t : G)) x.2.2
              simpa using h)
          · intro a b hab
            apply Subtype.ext
            apply Subtype.ext
            exact congrArg (fun t : {v : ↥(S.V) // v ^ p = 1} => ((t.1 : S.V) : G)) hab
          · exact le_of_eq (Fintype.card_subtype _)
        have h2 : (Finset.univ.filter (fun v : ↥(S.V) => v ^ p = 1)).card ≤ p :=
          IsCyclic.card_pow_eq_one_le (α := ↥(S.V)) hpp.pos
        have h3 : 1 ≤ (Finset.univ.filter (fun x : ↥W => (x : G) ∈ S.V ∧ x ^ p = 1)).card :=
          Finset.card_pos.mpr ⟨1, by simp⟩
        omega
      -- ## an element of order `p` in `W` is conjugate into `V`
      have hpV : p ∣ Nat.card ↥(S.V) := by
        have hbig : 1 < (Finset.univ.filter (fun x : ↥W => x ^ p = 1)).card := by
          rw [show (Finset.univ.filter (fun x : ↥W => x ^ p = 1)).card
                = Nat.card {x : ↥W // x ^ p = 1} from by
                  rw [← Fintype.card_subtype (fun x : ↥W => x ^ p = 1), Nat.card_eq_fintype_card],
              hr]
          calc 1 < p ^ 2 := by nlinarith [hpp.two_le]
            _ ≤ p ^ r := Nat.pow_le_pow_right hpp.one_le hr2
        have hpos : 0 < ((Finset.univ.filter (fun x : ↥W => x ^ p = 1)).erase 1).card := by
          rw [Finset.card_erase_of_mem (by simp)]
          omega
        obtain ⟨z, hz⟩ := Finset.card_pos.mp hpos
        have hzp : z ^ p = 1 := (Finset.mem_filter.mp (Finset.mem_of_mem_erase hz)).2
        have hzne : z ≠ 1 := Finset.ne_of_mem_erase hz
        have hord : orderOf z = p := by
          have hdvd : orderOf z ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hzp
          rcases (Nat.dvd_prime hpp).mp hdvd with h | h
          · exact absurd (orderOf_eq_one_iff.mp h) hzne
          · exact h
        have hordG : orderOf (z : G) = p := by rw [Subgroup.orderOf_coe z, hord]
        obtain ⟨g, hg⟩ := hconjV (z : G) z.2 (fun h => hzne (Subtype.ext h))
        rw [← hordG, ← Work.ThmF.Bender.orderOf_conj_eq g (z : G)]
        exact Subgroup.orderOf_dvd_natCard S.V hg
      have ha : p ∣ 2 ^ a + 1 := by rw [← hVcard]; exact hpV
      have hp2p : p ≠ 2 := by
        rintro rfl
        have h1 : 0 < a := by omega
        have heven : Even (2 ^ a) := ⟨2 ^ (a - 1), by
          have h : 2 ^ a = 2 * 2 ^ (a - 1) := by
            conv_lhs => rw [show a = (a - 1) + 1 from by omega, pow_succ']
          rw [h]; ring⟩
        have hodd : Odd (2 ^ a + 1) := heven.add_odd odd_one
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr ha)
      -- ## the number theory
      have hpc : p ^ r - 1 = l * c₂ := by rw [← he1, hZcard]
      have hl_dvd : 2 ^ k ∣ p ^ r - 1 := ⟨c₂, by rw [← hl2, ← hpc]⟩
      have hle2 : 2 * (p ^ r - 1) ≤ 2 ^ k * (p - 1) := by
        rw [← hl2, hpc]
        calc 2 * (l * c₂) = l * (2 * c₂) := by ring
          _ ≤ l * Y.card := Nat.mul_le_mul_left l he2
          _ ≤ l * (p - 1) := Nat.mul_le_mul_left l hYle
      obtain ⟨hp3, hr2', hlk⟩ := pow_two_classification hpp hp2p hr2 hl_dvd hle2 ha
      have hl8 : l = 8 := by rw [hl2, hlk]
      -- ## `m = 1`, hence `W = S.V`
      have hWcard' : Nat.card ↥W = (2 ^ a + 1) * m := by rw [hWcard, hVcard]
      have hmpos : 1 ≤ m := by
        by_contra hcon
        have h0 : m = 0 := by omega
        rw [h0, mul_zero] at hWcard
        have hpos : 0 < Nat.card ↥W := by
          rw [Nat.card_eq_fintype_card]
          exact Fintype.card_pos_iff.mpr ⟨(1 : ↥W)⟩
        omega
      have hm1 : m = 1 := by
        refine m_eq_one_of_singer_arith ha2 hmpos (by rw [← hp3]; exact ha) ?_ ?_
        · refine ⟨c, ?_⟩
          rw [← hl8, ← hc1, ← Nat.card_eq_fintype_card, hWcard']
        · calc 2 * ((2 ^ a + 1) * m - 1)
              = 2 * (Nat.card ↥W - 1) := by rw [hWcard']
            _ ≤ l * (Nat.card ↥(S.V) - 1) := hcount
            _ = 8 * ((2 ^ a + 1) - 1) := by rw [← hl8, ← hVcard]
      have hcardWV : Nat.card ↥W = Nat.card ↥(S.V) := by rw [hWcard, hm1, mul_one]
      exact (Subgroup.eq_of_le_of_card_ge hVW (le_of_eq hcardWV)).symm
  -- ## `W = C_G(S.V) = S.V`: the goal
  exact hWdef.symm.trans hWV

end Work.ZassenhausSuzuki.SelfCent
