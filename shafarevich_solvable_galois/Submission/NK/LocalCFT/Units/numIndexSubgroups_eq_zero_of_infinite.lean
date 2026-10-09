import Mathlib
import Submission.NK.LocalAnabelian.Basic
import Submission.NK.LocalCFT.Units.prod_ker_powMonoidHom_mulEquiv
import Submission.NK.LocalCFT.Units.index_comap_inl_and_map_snd
import Submission.NK.LocalCFT.Units.prime_dvd_natCard_of_pow_eq_one
import Submission.NK.LocalCFT.Units.exists_prime_pow_mul_coprime
import Submission.NK.LocalCFT.Units.EllRank.infinite_codim_submodule
import Submission.NK.LocalCFT.Units.EllRank.infinite_index_prime_pow_add
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false



namespace NK.LocalCFT.Units

/-- Index is preserved by `Subgroup.toAddSubgroup`. -/
theorem index_toAddSubgroup {G : Type*} [Group G] (H : Subgroup G) :
    (Subgroup.toAddSubgroup H : AddSubgroup (Additive G)).index = H.index := by
  rw [Subgroup.index_eq_card, AddSubgroup.index_eq_card]
  exact Nat.card_congr (Equiv.refl _)

/-- Multiplicative form of the prime-power case. -/
theorem infinite_index_prime_pow {M : Type*} [CommGroup M] {p e : ℕ} (hp : p.Prime) (he : 1 ≤ e)
    (hexp : ∀ x : M, x ^ (p ^ e) = 1) (hinf : Infinite M) :
    Infinite {K : Subgroup M // K.index = p ^ e} := by
  have h := NK.LocalCFT.Units.EllRank.infinite_index_prime_pow_add (A := Additive M) hp he
    (fun x => hexp x) hinf
  refine Infinite.of_injective
    (fun (K : {K : AddSubgroup (Additive M) // K.index = p ^ e}) =>
      ⟨AddSubgroup.toSubgroup' K.1, by
        have h4 : (Subgroup.toAddSubgroup (AddSubgroup.toSubgroup' K.1)).index = p ^ e := by
          have h3 : (Subgroup.toAddSubgroup (AddSubgroup.toSubgroup' K.1)) = K.1 := by
            rw [AddSubgroup.toSubgroup']
            exact OrderIso.apply_symm_apply _ _
          rw [h3]; exact K.2
        rw [← index_toAddSubgroup (H := AddSubgroup.toSubgroup' K.1)]
        exact h4⟩) ?_
  intro K K' hEq
  have h1 : AddSubgroup.toSubgroup' K.1 = AddSubgroup.toSubgroup' K'.1 := congrArg Subtype.val hEq
  have h2 : K.1 = K'.1 := by
    have h3 := congrArg Subgroup.toAddSubgroup h1
    simpa [AddSubgroup.toSubgroup'] using h3
  exact Subtype.ext h2

/-- The key counting claim: an infinite commutative group of exponent dividing `ℓ ≥ 2` has
`0` index-`ℓ` subgroups in the sense of `Nat.card` (i.e. either none or infinitely many). -/
theorem numIndexSubgroups_eq_zero_of_infinite_aux : ∀ (ℓ : ℕ), 2 ≤ ℓ → ∀ (M : Type*) [CommGroup M],
    (∀ x : M, x ^ ℓ = 1) → Infinite M → NK.LocalAnabelian.numIndexSubgroups ℓ M = 0 := by
  intro ℓ
  induction ℓ using Nat.strong_induction_on with
  | h ℓ ih =>
    intro hℓ M _ hexp hinf
    obtain ⟨p, e, m, hp, he, hℓeq, hcop, hmlt⟩ :=
      NK.LocalCFT.Units.exists_prime_pow_mul_coprime hℓ
    set A : Subgroup M := MonoidHom.ker (powMonoidHom (p ^ e) : M →* M) with hA
    set B : Subgroup M := MonoidHom.ker (powMonoidHom m : M →* M) with hB
    have hexp_prod : ∀ x : M, x ^ ((p ^ e) * m) = 1 := by
      intro x; rw [← hℓeq]; exact hexp x
    obtain ⟨φ⟩ : Nonempty (↥A × ↥B ≃* M) := by
      rw [hA, hB]
      exact NK.LocalCFT.Units.prod_ker_powMonoidHom_mulEquiv hcop hexp_prod
    have hexpA : ∀ x : ↥A, x ^ (p ^ e) = 1 := by
      intro x
      have hx : (x : M) ^ (p ^ e) = 1 :=
        (MonoidHom.mem_ker.mp (hA ▸ x.2) : (powMonoidHom (p ^ e) : M →* M) (x : M) = 1)
      exact Subtype.ext (by simpa using hx)
    have hexpB : ∀ x : ↥B, x ^ m = 1 := by
      intro x
      have hx : (x : M) ^ m = 1 :=
        (MonoidHom.mem_ker.mp (hB ▸ x.2) : (powMonoidHom m : M →* M) (x : M) = 1)
      exact Subtype.ext (by simpa using hx)
    rw [NK.LocalAnabelian.numIndexSubgroups_congr φ.symm ℓ]
    by_cases hAfin : Finite ↥A
    · -- A finite
      by_cases hBfin : Finite ↥B
      · -- both finite: M would be finite
        haveI : Finite ↥A := hAfin
        haveI : Finite ↥B := hBfin
        haveI : Finite (↥A × ↥B) := inferInstance
        exact absurd (Finite.of_equiv (↥A × ↥B) φ : Finite M) hinf.not_finite
      · -- A finite, B infinite: vary the B-part
        by_cases hneB : Nonempty {K' : Subgroup (↥A × ↥B) // K'.index = ℓ}
        · obtain ⟨K, hK⟩ := hneB
          have hKi : K.index = p ^ e * m := by rw [← hℓeq]; exact hK
          obtain ⟨hAidx, hBidx⟩ :=
            NK.LocalCFT.Units.index_comap_inl_and_map_snd hexpA hexpB hcop K hKi
          have hm1 : m ≠ 1 := by
            intro hm1
            have hBbot : B = ⊥ := by
              rw [hB, hm1]
              have : (powMonoidHom (1 : ℕ) : M →* M) = MonoidHom.id M := by ext x; simp
              rw [this, MonoidHom.ker_id]
            have : Finite ↥B := by rw [hBbot]; infer_instance
            exact hBfin this
          have hm2 : 2 ≤ m := by
            rcases Nat.eq_zero_or_pos m with h0 | hpos
            · exact absurd h0 (by rintro rfl; simp at hℓeq; omega)
            · omega
          have hmlt' : m < ℓ := hmlt hm2
          have hinfB : Infinite ↥B := not_finite_iff_infinite.mp hBfin
          have hIH : NK.LocalAnabelian.numIndexSubgroups m ↥B = 0 :=
            ih m hmlt' hm2 ↥B hexpB hinfB
          have hBinf' : Infinite {L : Subgroup ↥B // L.index = m} := by
            rcases (Nat.card_eq_zero.mp hIH) with hemp | hinf'
            · exact absurd ⟨⟨_, hBidx⟩⟩ (not_nonempty_iff.mpr hemp)
            · exact hinf'
          refine Nat.card_eq_zero.mpr (Or.inr ?_)
          refine Infinite.of_injective
            (fun (L : {L : Subgroup ↥B // L.index = m}) =>
              (⟨(K.comap (MonoidHom.inl ↥A ↥B)).prod L.1,
                by rw [Subgroup.index_prod, hAidx, L.2, ← hℓeq]⟩ :
                {K' : Subgroup (↥A × ↥B) // K'.index = ℓ})) ?_
          intro L L' hEq
          have hc : ((K.comap (MonoidHom.inl ↥A ↥B)).prod L.1).map (MonoidHom.snd ↥A ↥B) =
              ((K.comap (MonoidHom.inl ↥A ↥B)).prod L'.1).map (MonoidHom.snd ↥A ↥B) := by
            have hval : (K.comap (MonoidHom.inl ↥A ↥B)).prod L.1 =
                (K.comap (MonoidHom.inl ↥A ↥B)).prod L'.1 := congrArg Subtype.val hEq
            rw [hval]
          have h1 : ((K.comap (MonoidHom.inl ↥A ↥B)).prod L.1).map (MonoidHom.snd ↥A ↥B) = L.1 := by
            ext b; constructor
            · rintro ⟨x, hx, rfl⟩; exact hx.2
            · intro hb; exact ⟨(1, b), ⟨Subgroup.one_mem _, hb⟩, rfl⟩
          have h2 : ((K.comap (MonoidHom.inl ↥A ↥B)).prod L'.1).map (MonoidHom.snd ↥A ↥B) = L'.1 := by
            ext b; constructor
            · rintro ⟨x, hx, rfl⟩; exact hx.2
            · intro hb; exact ⟨(1, b), ⟨Subgroup.one_mem _, hb⟩, rfl⟩
          exact Subtype.ext (by rw [← h1, hc, h2])
        · exact Nat.card_eq_zero.mpr (Or.inl (not_nonempty_iff.mp hneB))
    · -- A infinite: vary the A-part
      have hinfA : Infinite ↥A := not_finite_iff_infinite.mp hAfin
      have hLinf : Infinite {L : Subgroup ↥A // L.index = p ^ e} :=
        infinite_index_prime_pow hp he hexpA hinfA
      by_cases hne : Nonempty {K' : Subgroup (↥A × ↥B) // K'.index = ℓ}
      · obtain ⟨K, hK⟩ := hne
        have hKi : K.index = p ^ e * m := by rw [← hℓeq]; exact hK
        obtain ⟨-, hBidx⟩ :=
          NK.LocalCFT.Units.index_comap_inl_and_map_snd hexpA hexpB hcop K hKi
        refine Nat.card_eq_zero.mpr (Or.inr ?_)
        refine Infinite.of_injective
          (fun (L : {L : Subgroup ↥A // L.index = p ^ e}) =>
            (⟨L.1.prod (K.map (MonoidHom.snd ↥A ↥B)),
              by rw [Subgroup.index_prod, L.2, hBidx, ← hℓeq]⟩ :
              {K' : Subgroup (↥A × ↥B) // K'.index = ℓ})) ?_
        intro L L' hEq
        have hc : (L.1.prod (K.map (MonoidHom.snd ↥A ↥B))).comap (MonoidHom.inl ↥A ↥B) =
            (L'.1.prod (K.map (MonoidHom.snd ↥A ↥B))).comap (MonoidHom.inl ↥A ↥B) := by
          have hval : L.1.prod (K.map (MonoidHom.snd ↥A ↥B)) =
              L'.1.prod (K.map (MonoidHom.snd ↥A ↥B)) := congrArg Subtype.val hEq
          rw [hval]
        have h1 : (L.1.prod (K.map (MonoidHom.snd ↥A ↥B))).comap (MonoidHom.inl ↥A ↥B) = L.1 := by
          ext a; constructor
          · intro ha; exact ha.1
          · intro ha; exact ⟨ha, Subgroup.one_mem _⟩
        have h2 : (L'.1.prod (K.map (MonoidHom.snd ↥A ↥B))).comap (MonoidHom.inl ↥A ↥B) = L'.1 := by
          ext a; constructor
          · intro ha; exact ha.1
          · intro ha; exact ⟨ha, Subgroup.one_mem _⟩
        exact Subtype.ext (by rw [← h1, hc, h2])
      · exact Nat.card_eq_zero.mpr (Or.inl (not_nonempty_iff.mp hne))

theorem numIndexSubgroups_eq_zero_of_infinite {M : Type*} [CommGroup M] {ℓ : ℕ}
    (hℓ : 2 ≤ ℓ) (hexp : ∀ x : M, x ^ ℓ = 1) (hinf : Infinite M) :
    NK.LocalAnabelian.numIndexSubgroups ℓ M = 0 :=
  numIndexSubgroups_eq_zero_of_infinite_aux ℓ hℓ M hexp hinf

end NK.LocalCFT.Units
