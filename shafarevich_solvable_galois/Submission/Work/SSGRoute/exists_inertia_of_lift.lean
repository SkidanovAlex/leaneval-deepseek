import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The inertia condition for a lift of a character, from the inertia condition of its reduction

This file proves `Work.SSGRoute.exists_inertia_of_lift`.

The mathematical content is elementary abelian-group theory.  Let `p` be a prime and consider the
reduction homomorphism

`π : Multiplicative (ZMod (p ^ (a+1))) →* Multiplicative (ZMod (p ^ a))`

given by the ring homomorphism `ZMod.castHom (p ^ a ∣ p ^ (a+1))`.  For a subgroup `S` of the cyclic
`p`-group `Multiplicative (ZMod (p ^ (a+1)))` and `T := χ'.range ≥ S := (χ')''I`, one has
`π(T) = π(S) = χ.range`.  The main point is that `π.ker` is the unique subgroup of order `p`, so that

* every *nontrivial* subgroup of `Multiplicative (ZMod (p ^ (a+1)))` contains `π.ker`
  (`ker_castHom_le_of_ne_bot`), while
* `χ ≠ 1` forces both `χ.range` and `S` to be nontrivial.

Consequently `T ≤ S ⊔ π.ker = S`, so `S = T`.

The supporting facts about `ZMod` are isolated as `zmod_mul_eq_zero_castHom_eq_zero`,
`castHom_eq_one_of_pow_eq_one`, `natCard_ker_castHom_eq` and `ker_castHom_le_of_ne_bot`.
-/

namespace Work.SSGRoute

set_option linter.style.haveILetI false

/-- The `p`-torsion of `ZMod (p ^ (a+1))` lies in the kernel of the reduction `ZMod (p^(a+1)) → ZMod (p^a)`:
if `p * z = 0` then `z` is divisible by `p ^ a` modulo `p ^ (a+1)`, hence `z.cast = 0`. -/
lemma zmod_mul_eq_zero_castHom_eq_zero {p a : ℕ} (hp : p.Prime) (z : ZMod (p ^ (a+1)))
    (hz : (p : ZMod (p ^ (a + 1))) * z = 0) :
    ZMod.castHom (pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a)) z = 0 := by
  haveI : NeZero (p ^ (a + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff]
  have hp0 : 0 < p := hp.pos
  have hz' : p ^ (a + 1) ∣ p * z.val := by
    rw [← ZMod.natCast_eq_zero_iff]
    have hzval : ((p * z.val : ℕ) : ZMod (p ^ (a + 1)))
        = (p : ZMod (p ^ (a + 1))) * z := by
      rw [Nat.cast_mul, ZMod.natCast_val, ZMod.cast_id]
    rw [hzval]; exact hz
  apply Nat.dvd_of_mul_dvd_mul_left hp0
  rw [← pow_succ']
  exact hz'

/-- An element of order dividing `p` in `Multiplicative (ZMod (p ^ (a+1)))` is killed by the
reduction `ZMod (p^(a+1)) → ZMod (p^a)`. -/
lemma castHom_eq_one_of_pow_eq_one {p a : ℕ} (hp : p.Prime)
    (x : Multiplicative (ZMod (p ^ (a + 1)))) (hx : x ^ p = 1) :
    (ZMod.castHom (pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a))).toAddMonoidHom.toMultiplicative
      x = 1 := by
  apply Multiplicative.toAdd.injective
  simp only [AddMonoidHom.coe_toMultiplicative, Function.comp_apply, toAdd_ofAdd, toAdd_one]
  apply zmod_mul_eq_zero_castHom_eq_zero hp
  have h := congrArg Multiplicative.toAdd hx
  simp only [toAdd_pow, toAdd_one] at h
  rwa [nsmul_eq_mul] at h

/-- The kernel of the reduction `Multiplicative (ZMod (p ^ (a+1))) →* Multiplicative (ZMod (p^a))`
has exactly `p` elements. -/
lemma natCard_ker_castHom_eq {p a : ℕ} (hp : p.Prime) :
    Nat.card ((ZMod.castHom (pow_dvd_pow p (Nat.le_succ a))
      (ZMod (p ^ a))).toAddMonoidHom.toMultiplicative).ker = p := by
  classical
  let φ : Multiplicative (ZMod (p ^ (a + 1))) →* Multiplicative (ZMod (p ^ a)) :=
    (ZMod.castHom (pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a))).toAddMonoidHom.toMultiplicative
  change Nat.card φ.ker = p
  have hp0 : 0 < p := hp.pos
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨w, hw⟩ :=
      ZMod.castHom_surjective (pow_dvd_pow p (Nat.le_succ a)) (Multiplicative.toAdd y)
    refine ⟨Multiplicative.ofAdd w, ?_⟩
    simp only [φ, AddMonoidHom.coe_toMultiplicative, Function.comp_apply, toAdd_ofAdd]
    rw [show (ZMod.castHom (pow_dvd_pow p (Nat.le_succ a))
          (ZMod (p ^ a))).toAddMonoidHom w = Multiplicative.toAdd y from hw]
    simp
  have hC1 : Nat.card (Multiplicative (ZMod (p ^ (a + 1)))) = p ^ (a + 1) := by
    rw [← Nat.card_congr (Multiplicative.ofAdd (α := ZMod (p ^ (a + 1)))), Nat.card_zmod]
  have hC0 : Nat.card (Multiplicative (ZMod (p ^ a))) = p ^ a := by
    rw [← Nat.card_congr (Multiplicative.ofAdd (α := ZMod (p ^ a))), Nat.card_zmod]
  have hidx : φ.ker.index = p ^ a := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj]
    exact (Nat.card_congr (Subgroup.topEquiv (G := Multiplicative (ZMod (p ^ a)))).toEquiv).trans hC0
  have hmul := Subgroup.card_mul_index φ.ker
  rw [hidx, hC1] at hmul
  have hpa : 0 < p ^ a := pow_pos hp0 a
  have h2 : Nat.card φ.ker * p ^ a = p * p ^ a := by rw [hmul, pow_succ']
  exact Nat.mul_right_cancel hpa h2

/-- Every nontrivial subgroup of the cyclic `p`-group `Multiplicative (ZMod (p ^ (a+1)))` contains
the kernel of the reduction `ZMod (p^(a+1)) → ZMod (p^a)` (the unique subgroup of order `p`). -/
lemma ker_castHom_le_of_ne_bot {p a : ℕ} (hp : p.Prime)
    (S : Subgroup (Multiplicative (ZMod (p ^ (a + 1))))) (hS : S ≠ ⊥) :
    ((ZMod.castHom (pow_dvd_pow p (Nat.le_succ a))
      (ZMod (p ^ a))).toAddMonoidHom.toMultiplicative).ker ≤ S := by
  classical
  let φ : Multiplicative (ZMod (p ^ (a + 1))) →* Multiplicative (ZMod (p ^ a)) :=
    (ZMod.castHom (pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a))).toAddMonoidHom.toMultiplicative
  change φ.ker ≤ S
  haveI : Fact p.Prime := ⟨hp⟩
  have hKcard : Nat.card φ.ker = p := natCard_ker_castHom_eq hp
  -- A nontrivial subgroup of a finite `p`-group has cardinality divisible by `p`.
  have hSne1 : Nat.card ↥S ≠ 1 := by
    intro h1
    obtain ⟨x, hx⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hS
    have : Subsingleton ↥S := (Nat.card_eq_one_iff_unique.mp h1).1
    exact hx (this.elim x 1)
  have hdiv : p ∣ Nat.card ↥S := by
    have hC1card : Nat.card (Multiplicative (ZMod (p ^ (a + 1)))) = p ^ (a + 1) := by
      rw [← Nat.card_congr (Multiplicative.ofAdd (α := ZMod (p ^ (a + 1)))), Nat.card_zmod]
    haveI hpg : IsPGroup p (Multiplicative (ZMod (p ^ (a + 1)))) := IsPGroup.of_card hC1card
    rcases IsPGroup.card_eq_or_dvd (IsPGroup.to_subgroup hpg S) with h1 | hd
    · exact absurd h1 hSne1
    · exact hd
  -- Cauchy's theorem produces an element of order `p` in `S`, which lies in `φ.ker`.
  obtain ⟨y, hyord⟩ := exists_prime_orderOf_dvd_card' p hdiv
  have hypow : y ^ p = 1 := (orderOf_eq_prime_iff.mp hyord).1
  have hyne : y ≠ 1 := (orderOf_eq_prime_iff.mp hyord).2
  have hy1pow : ((y : ↥S) : Multiplicative (ZMod (p ^ (a + 1)))) ^ p = 1 := by
    rw [← Subgroup.coe_pow S y p, hypow]
    rfl
  have hy1ne : ((y : ↥S) : Multiplicative (ZMod (p ^ (a + 1)))) ≠ 1 := by
    intro h; exact hyne (Subtype.ext (by simpa using h))
  have hyK : ((y : ↥S) : Multiplicative (ZMod (p ^ (a + 1)))) ∈ φ.ker := by
    rw [MonoidHom.mem_ker]
    exact castHom_eq_one_of_pow_eq_one hp _ hy1pow
  have hyS : ((y : ↥S) : Multiplicative (ZMod (p ^ (a + 1)))) ∈ S := y.2
  -- `φ.ker` has prime order `p`, so the nontrivial subgroup `⟨y⟩ ≤ φ.ker` exhausts it.
  have hle : Subgroup.zpowers ((y : ↥S) : Multiplicative (ZMod (p ^ (a + 1)))) ≤ φ.ker :=
    Subgroup.zpowers_le.mpr hyK
  have hcard : Nat.card φ.ker
      ≤ Nat.card ↥(Subgroup.zpowers ((y : ↥S) : Multiplicative (ZMod (p ^ (a + 1))))) := by
    rw [Nat.card_zpowers, hKcard, orderOf_eq_prime hy1pow hy1ne]
  have heq : Subgroup.zpowers ((y : ↥S) : Multiplicative (ZMod (p ^ (a + 1)))) = φ.ker :=
    Subgroup.eq_of_le_of_card_ge hle hcard
  rw [← heq]
  exact Subgroup.zpowers_le.mpr hyS

/-- **The inertia condition for a lift of a character of a group, from the inertia condition for
its reduction.**

Let `p` be a prime, `I ≤ G` a subgroup and `χ' : G →* Multiplicative (ZMod (p ^ (a+1)))`,
`χ : G →* Multiplicative (ZMod (p ^ a))` two characters, with `χ'` reducing to `χ` (hypothesis
`hrel`). Suppose every value of `χ` is attained on `I` (`hine`) and `χ` is nontrivial. Then every
value of `χ'` is attained on `I`.

Mathematically: `T := range χ'` and `S := (image of I under χ')` are subgroups of the cyclic group
`Multiplicative (ZMod (p ^ (a+1)))` with `S ≤ T`. Let `π` be the reduction
`Multiplicative (ZMod (p^(a+1))) →* Multiplicative (ZMod (p^a))`; `hrel` says `π ∘ χ' = χ`, so
`π(T) = π(S) = range χ` and `ker π` is the subgroup `K` of order `p`. Since `χ ≠ 1` we get `S ≠ 1`,
and every nontrivial subgroup of a cyclic `p`-group contains its `p`-torsion subgroup
(`ker_castHom_le_of_ne_bot`), so `K ≤ S`. Finally `T ≤ S ⊔ K = S` and `S ≤ T` force `S = T`. -/
lemma exists_inertia_of_lift {p a : ℕ} (hp : p.Prime)
    {G : Type*} [Group G] (I : Subgroup G)
    (χ' : G →* Multiplicative (ZMod (p ^ (a + 1))))
    (χ : G →* Multiplicative (ZMod (p ^ a)))
    (hrel : ∀ σ : G, ZMod.castHom (pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a))
        (Multiplicative.toAdd (χ' σ)) = Multiplicative.toAdd (χ σ))
    (hine : ∀ σ : G, ∃ τ ∈ I, χ τ = χ σ)
    (hne : χ ≠ 1) :
    ∀ σ : G, ∃ τ ∈ I, χ' τ = χ' σ := by
  classical
  intro σ
  let φ : Multiplicative (ZMod (p ^ (a + 1))) →* Multiplicative (ZMod (p ^ a)) :=
    (ZMod.castHom (pow_dvd_pow p (Nat.le_succ a)) (ZMod (p ^ a))).toAddMonoidHom.toMultiplicative
  -- `φ ∘ χ' = χ`
  have hφ : ∀ σ : G, φ (χ' σ) = χ σ := by
    intro σ
    apply Multiplicative.toAdd.injective
    simp only [φ, AddMonoidHom.coe_toMultiplicative, Function.comp_apply, toAdd_ofAdd]
    exact hrel σ
  have hcomp : φ.comp χ' = χ := MonoidHom.ext hφ
  -- The image of `I.map χ'` under `φ` is `χ.range`, thanks to `hine`.
  have hmap : (I.map χ').map φ = χ.range := by
    rw [Subgroup.map_map, hcomp]
    apply le_antisymm
    · exact Subgroup.map_le_range χ I
    · rintro x ⟨σ, rfl⟩
      obtain ⟨τ, hτ, hχτ⟩ := hine σ
      exact Subgroup.mem_map.mpr ⟨τ, hτ, hχτ⟩
  -- `χ ≠ 1` makes `χ.range`, hence `I.map χ'`, nontrivial.
  have hRne : χ.range ≠ ⊥ := by
    intro hbot
    apply hne
    ext σ
    have hmem : χ σ ∈ χ.range := ⟨σ, rfl⟩
    rw [hbot] at hmem
    simpa using hmem
  have hSne : I.map χ' ≠ ⊥ := by
    intro hbot
    have : (I.map χ').map φ = ⊥ := by rw [hbot, Subgroup.map_bot]
    rw [hmap] at this
    exact hRne this
  -- Every nontrivial subgroup contains `φ.ker`, in particular `I.map χ'` does.
  have hKleS : φ.ker ≤ I.map χ' := ker_castHom_le_of_ne_bot hp _ hSne
  -- `χ'.range ≤ (I.map χ') ⊔ φ.ker`, hence `≤ I.map χ'`.
  have hTS : χ'.range ≤ I.map χ' := by
    rintro x ⟨σ, rfl⟩
    have hmem : χ' σ ∈ I.map χ' ⊔ φ.ker := by
      obtain ⟨τ, hτ, hχτ⟩ := hine σ
      refine Subgroup.mem_sup.mpr ⟨χ' τ, ?_, (χ' τ)⁻¹ * χ' σ, ?_, ?_⟩
      · exact Subgroup.mem_map.mpr ⟨τ, hτ, rfl⟩
      · rw [MonoidHom.mem_ker, map_mul, map_inv, hφ τ, hφ σ, hχτ]
        simp
      · group
    exact sup_le le_rfl hKleS hmem
  have hST : I.map χ' ≤ χ'.range := Subgroup.map_le_range χ' I
  have hEq : I.map χ' = χ'.range := le_antisymm hST hTS
  have : χ' σ ∈ I.map χ' := by rw [hEq]; exact ⟨σ, rfl⟩
  obtain ⟨τ, hτ, hτ'⟩ := Subgroup.mem_map.mp this
  exact ⟨τ, hτ, hτ'⟩

end Work.SSGRoute
