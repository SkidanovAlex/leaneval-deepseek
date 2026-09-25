import Mathlib

namespace NK.Mine

/-- If a finite abelian group `M` contains an element `x` of order `p ^ n`, then `M` admits a
surjective homomorphism onto the (multiplicative) cyclic group `ZMod (p ^ n)` of order `p ^ n`.
The proof uses the structure theorem for finite abelian groups: `M ≃* ∏ᵢ ZMod (n i)`, and the
factor `ZMod (n i)` whose order is divisible by `p ^ n` projects onto `ZMod (p ^ n)`. -/
theorem zmodQuotient_of_orderOf_eq {M : Type*} [CommGroup M] [Finite M]
    {p n : ℕ} (hp : p.Prime) (x : M) (hx : orderOf x = p ^ n) :
    ∃ f : M →* Multiplicative (ZMod (p ^ n)), Function.Surjective f := by
  classical
  by_cases hn : n = 0
  · -- the target group is trivial, so the trivial homomorphism is surjective
    subst hn
    rw [pow_zero]
    exact ⟨1, fun y => ⟨1, Subsingleton.elim _ _⟩⟩
  -- decompose `M` as a product of cyclic groups
  obtain ⟨ι, hι, nn, hnn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite M
  let y : ((i : ι) → Multiplicative (ZMod (nn i))) := e x
  have hy : orderOf y = p ^ n := by rw [← hx]; exact e.orderOf_eq x
  have hy_pow : y ^ (p ^ n) = 1 := by rw [← hy]; exact pow_orderOf_eq_one y
  -- some cyclic factor has order divisible by `p ^ n`
  have hclaim : ∃ i, p ^ n ∣ nn i := by
    by_contra hcon
    have hne : ∀ i, ¬ p ^ n ∣ nn i := fun i hi => hcon ⟨i, hi⟩
    have h1 : ∀ i, y i ^ (p ^ (n - 1)) = 1 := by
      intro i
      have hd : orderOf (y i) ∣ p ^ n := orderOf_dvd_of_pow_eq_one (by
        have := congr_fun hy_pow i
        simpa using this)
      obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow hp).mp hd
      have hdiv : orderOf (y i) ∣ nn i := by
        have hNeZero : NeZero (nn i) := NeZero.of_gt (hnn i)
        have hcard : Fintype.card (Multiplicative (ZMod (nn i))) = nn i := by
          rw [Fintype.card_multiplicative, ZMod.card]
        have hpc := pow_card_eq_one (G := Multiplicative (ZMod (nn i))) (x := y i)
        have hpow : (y i) ^ (nn i) = 1 := by rwa [hcard] at hpc
        exact orderOf_dvd_of_pow_eq_one hpow
      -- the order of `y i` is a power of `p`; it cannot be smaller than `p ^ n`,
      -- since `y ^ (p ^ (n - 1)) ≠ 1`
      have hklt : k < n := by
        rcases lt_or_ge k n with h' | h'
        · exact h'
        · exact absurd (by
            have hkn : k = n := le_antisymm hk_le h'
            have hkEq : orderOf (y i) = p ^ n := by rw [hk, hkn]
            exact hkEq ▸ hdiv) (hne i)
      have : orderOf (y i) ∣ p ^ (n - 1) := by
        rw [hk]; exact pow_dvd_pow p (Nat.le_sub_one_of_lt hklt)
      exact orderOf_dvd_iff_pow_eq_one.mp this
    have h2 : y ^ (p ^ (n - 1)) = 1 := by
      funext i; simpa using h1 i
    -- so `p ^ n ∣ p ^ (n - 1)`, which is absurd
    have h3 : p ^ n ∣ p ^ (n - 1) := by
      have h4 := orderOf_dvd_of_pow_eq_one h2
      rwa [hy] at h4
    have hpos : 0 < p ^ (n - 1) := pow_pos hp.pos _
    have hle : p ^ n ≤ p ^ (n - 1) := Nat.le_of_dvd hpos h3
    have hlt : p ^ (n - 1) < p ^ n := pow_lt_pow_right₀ hp.one_lt (Nat.sub_one_lt hn)
    omega
  obtain ⟨i, hi⟩ := hclaim
  have hNeZeroP : NeZero (p ^ n) := ⟨pow_ne_zero n hp.ne_zero⟩
  -- the projection onto the factor `i`, followed by reduction mod `p ^ n`
  let F2 : Multiplicative (ZMod (nn i)) →* Multiplicative (ZMod (p ^ n)) :=
    AddMonoidHom.toMultiplicative ((ZMod.castHom hi (ZMod (p ^ n))).toAddMonoidHom)
  let F1 : M →* Multiplicative (ZMod (nn i)) :=
    (Pi.evalMonoidHom (fun i => Multiplicative (ZMod (nn i))) i).comp e.toMonoidHom
  have hF2 : Function.Surjective F2 := by
    intro b
    obtain ⟨a, ha⟩ := ZMod.castHom_surjective hi (Multiplicative.toAdd b)
    exact ⟨Multiplicative.ofAdd a, congrArg Multiplicative.ofAdd ha⟩
  have hF1 : Function.Surjective F1 := by
    have h := Function.surjective_eval (β := fun i => Multiplicative (ZMod (nn i))) i
    have h' : Function.Surjective
        ⇑(Pi.evalMonoidHom (fun i => Multiplicative (ZMod (nn i))) i) := by
      simpa [Pi.coe_evalMonoidHom] using h
    exact h'.comp e.surjective
  refine ⟨F2.comp F1, fun b => ?_⟩
  obtain ⟨c, hc⟩ := hF2 b
  obtain ⟨m, hm⟩ := hF1 c
  exact ⟨m, by rw [MonoidHom.comp_apply, hm, hc]⟩

end NK.Mine
