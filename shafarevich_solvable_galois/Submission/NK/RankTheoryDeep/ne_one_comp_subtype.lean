import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.RankTheoryDeep

/-- **A non-trivial homomorphism into a finite `ℓ`-group stays non-trivial on a subgroup of
`ℓ`'-index.**  If `N ≤ A` is a subgroup whose quotient `A ⧸ N` has order coprime to `ℓ`, and the
finite group `B` has `ℓ`-power order, then for every `φ : A →* B` with `φ ≠ 1` the restriction of
`φ` to `N` is again non-trivial.  (Indeed `φ` factors through `A ⧸ N`, so its image has order
dividing both `|A ⧸ N|` and `|B|`, which are coprime.) -/
theorem ne_one_comp_subtype {A B : Type*} [CommGroup A] [Finite A] [CommGroup B] [Finite B]
    {ℓ : ℕ} [Fact ℓ.Prime] (N : Subgroup A) (hN : Nat.Coprime ℓ (Nat.card (A ⧸ N)))
    (hB : ∃ k : ℕ, Nat.card B = ℓ ^ k) (φ : A →* B) (hφ : φ ≠ 1) :
    φ.comp N.subtype ≠ 1 := by
  intro h
  -- If the restriction of `φ` to `N` is trivial then `N ≤ ker φ`.
  have hker : N ≤ φ.ker := by
    intro n hn
    have h1 := DFunLike.congr_fun h (⟨n, hn⟩ : N)
    simpa using h1
  obtain ⟨k, hk⟩ := hB
  -- The index of `ker φ` divides the index of `N` (both being indices of subgroups containing `N`).
  have hdiv_idx : φ.ker.index ∣ N.index := Subgroup.index_dvd_of_le hker
  -- `N.index = |A ⧸ N|` is coprime to `ℓ`, hence to `ℓ ^ k`.
  have hcop : Nat.Coprime ℓ N.index := by
    rw [Subgroup.index_eq_card]; exact hN
  have hcop' : Nat.Coprime (ℓ ^ k) N.index := hcop.pow_left k
  -- The image of `φ` is a subgroup of `B`, so its order divides `ℓ ^ k` …
  have hdvdB : Nat.card φ.range ∣ ℓ ^ k := by
    rw [← hk]; exact Subgroup.card_subgroup_dvd_card φ.range
  -- … and it is isomorphic to `A ⧸ ker φ`, so its order also divides `N.index`.
  have hdvdIdx : Nat.card φ.range ∣ N.index := by
    rw [← Subgroup.index_ker φ]; exact hdiv_idx
  have hone : Nat.card φ.range = 1 := by
    have hg := Nat.dvd_gcd hdvdB hdvdIdx
    rw [hcop'.gcd_eq_one] at hg
    exact Nat.dvd_one.mp hg
  -- Hence `φ` has trivial range, i.e. `φ = 1`, contradicting `hφ`.
  have hbot : φ.range = ⊥ := Subgroup.card_eq_one.mp hone
  apply hφ
  ext a
  have : φ a ∈ φ.range := MonoidHom.mem_range.mpr ⟨a, rfl⟩
  rw [hbot] at this
  simpa using (Subgroup.mem_bot.mp this)

end NK.RankTheoryDeep
