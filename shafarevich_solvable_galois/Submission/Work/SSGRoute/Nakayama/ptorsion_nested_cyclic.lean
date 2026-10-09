import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 1000000

namespace Work.SSGRoute.Nakayama

/-- The coefficient endomorphism `x ↦ p • x`. -/
def nsmulEnd (X : Type*) [AddCommMonoid X] (p : ℕ) : X →+ X where
  toFun := fun x => p • x
  map_zero' := nsmul_zero p
  map_add' := fun x y => nsmul_add x y p

@[simp] theorem nsmulEnd_apply {X : Type*} [AddCommMonoid X] (p : ℕ) (x : X) :
    nsmulEnd X p x = p • x := rfl

/-- **In a finite cyclic additive group the elements killed by `p` number at most `p`.** -/
theorem natCard_ptorsion_le_of_isAddCyclic (A : Type*) [AddCommGroup A] [Fintype A]
    [IsAddCyclic A] (p : ℕ) (hp : 0 < p) :
    Nat.card {x : A // p • x = 0} ≤ p := by
  classical
  have h := IsAddCyclic.card_nsmul_eq_zero_le (α := A) (hn0 := hp)
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using h

/-- **The `p`-torsion of a group covered by a nested family of subgroups whose `p`-torsion has at
most `p` elements, one of which carries an element of order `p`, has exactly `p` elements.** -/
theorem ptorsion_nested_cyclic {B : Type*} [AddCommGroup B] (p : ℕ) [Fact p.Prime]
    {ι : Type*} {A : ι → Type*} [∀ i, AddCommGroup (A i)] [∀ i, Finite (A i)]
    (φ : ∀ i, A i →+ B) (hinj : ∀ i, Function.Injective (φ i))
    (hnest : ∀ i j, ∃ k, Set.range (φ i) ⊆ Set.range (φ k) ∧ Set.range (φ j) ⊆ Set.range (φ k))
    (hcov : ∀ b : B, ∃ i, b ∈ Set.range (φ i))
    (htor : ∀ i, Nat.card {x : A i // p • x = 0} ≤ p)
    (hex : ∃ i, ∃ a : A i, addOrderOf a = p) :
    Nat.card {b : B // p • b = 0} = p := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨i0, a0, ha0⟩ := hex
  have ha0_ne : a0 ≠ 0 := by
    rintro rfl
    rw [addOrderOf_zero] at ha0
    exact hp.ne_one ha0.symm
  have ha0_ptor : p • a0 = 0 :=
    (addOrderOf_dvd_iff_nsmul_eq_zero (x := a0) (n := p)).mp (by rw [ha0])
  set b0 : B := φ i0 a0 with hb0
  have hb0_ne : b0 ≠ 0 := by
    intro h
    rw [hb0] at h
    exact ha0_ne (hinj i0 (by rw [h, map_zero]))
  have hb0_ptor : p • b0 = 0 := by
    rw [hb0, ← map_nsmul, ha0_ptor, map_zero]
  have hkey : ∀ b : B, p • b = 0 → b ∈ AddSubgroup.zmultiples b0 := by
    intro b hb
    obtain ⟨j, hj⟩ := hcov b
    obtain ⟨k, hk1, hk2⟩ := hnest i0 j
    obtain ⟨w, hw⟩ := hk1 (show b0 ∈ Set.range (φ i0) from ⟨a0, hb0.symm⟩)
    obtain ⟨y, hy⟩ := hk2 hj
    have hw_ptor : p • w = 0 := by
      apply hinj k
      rw [map_nsmul, hw, map_zero, hb0_ptor]
    have hy_ptor : p • y = 0 := by
      apply hinj k
      rw [map_nsmul, hy, map_zero]
      exact hb
    have hw_ne : w ≠ 0 := by
      intro h
      rw [h, map_zero] at hw
      exact hb0_ne hw.symm
    have hcardT : Nat.card ↥(AddMonoidHom.ker (nsmulEnd (A k) p)) ≤ p := by
      rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x => ?_))]
      · exact htor k
      · rw [AddMonoidHom.mem_ker, nsmulEnd_apply]
    have hw_order : addOrderOf w = p := by
      have hdvd : addOrderOf w ∣ p :=
        (addOrderOf_dvd_iff_nsmul_eq_zero (x := w) (n := p)).mpr hw_ptor
      rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
      · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hw_ne
      · exact h1
    have hzsub : AddSubgroup.zmultiples w ≤ AddMonoidHom.ker (nsmulEnd (A k) p) := by
      rw [AddSubgroup.zmultiples_le, AddMonoidHom.mem_ker, nsmulEnd_apply]
      exact hw_ptor
    have hzcard : Nat.card ↥(AddSubgroup.zmultiples w) = p := by
      rw [Nat.card_zmultiples, hw_order]
    haveI : Finite ↥(AddSubgroup.zmultiples w) :=
      Nat.finite_of_card_ne_zero (by rw [Nat.card_zmultiples, hw_order]; exact hp.ne_zero)
    have hTeq : AddSubgroup.zmultiples w = AddMonoidHom.ker (nsmulEnd (A k) p) :=
      AddSubgroup.eq_of_le_of_card_ge hzsub (by rw [hzcard]; exact hcardT)
    have hy_mem : y ∈ AddSubgroup.zmultiples w := by
      rw [hTeq, AddMonoidHom.mem_ker, nsmulEnd_apply]
      exact hy_ptor
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hy_mem
    rw [AddSubgroup.mem_zmultiples_iff]
    exact ⟨n, by rw [← hw, ← map_zsmul, hn, hy]⟩
  have hzle : AddSubgroup.zmultiples b0 ≤ AddMonoidHom.ker (nsmulEnd B p) := by
    rw [AddSubgroup.zmultiples_le, AddMonoidHom.mem_ker, nsmulEnd_apply]
    exact hb0_ptor
  have hset : (AddMonoidHom.ker (nsmulEnd B p) : Set B) = (AddSubgroup.zmultiples b0 : Set B) :=
    Set.Subset.antisymm
      (fun b hb => by
        rw [SetLike.mem_coe, AddMonoidHom.mem_ker, nsmulEnd_apply] at hb
        exact hkey b hb)
      (fun x hx => hzle hx)
  have hcard0 : Nat.card ↥(AddSubgroup.zmultiples b0) = p := by
    rw [Nat.card_zmultiples]
    have hdvd : addOrderOf b0 ∣ p :=
      (addOrderOf_dvd_iff_nsmul_eq_zero (x := b0) (n := p)).mpr hb0_ptor
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h1) hb0_ne
    · exact h1
  have hgoal : Nat.card {b : B // p • b = 0} = Nat.card ↥(AddSubgroup.zmultiples b0) :=
    Nat.card_congr (Set.equivOfEq hset)
  rw [hgoal, hcard0]

end Work.SSGRoute.Nakayama
