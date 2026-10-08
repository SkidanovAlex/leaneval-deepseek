import Mathlib
import Submission.Work.NPC.Engine
import Submission.Work.ThmF.ChV12.sylow_normalizer_le_centralizer_of_card_prime
import Submission.Work.ThmF.ChV12.solvable_of_card_dvd_two_pow_six_odd_no_five

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV12

/-- **The order of `Aut A` for `A` an elementary abelian `2`-group of order `2 ^ 6`.**

`A` is a `6`-dimensional `𝔽₂`-vector space, so `MulAut A ≃* GL(6, 𝔽₂)`, whose order is
`∏_{i<6} (2 ^ 6 - 2 ^ i) = 2 ^ 15 * 3 ^ 4 * 5 * 7 ^ 2 * 31 = 20158709760`. -/
theorem card_mulAut_of_card_two_pow_six {A : Type} [Group A] [Finite A]
    (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x)
    (hk : Nat.card A = 2 ^ 6) : Nat.card (MulAut A) = 20158709760 := by
  classical
  letI : CommGroup A := { ‹Group A› with mul_comm := hAc }
  have h2 : ∀ x : Additive A, (2 : ℕ) • x = 0 := by
    intro x
    rw [two_nsmul]
    exact Additive.ext (show x.toMul * x.toMul = (0 : Additive A).toMul from hA2 x.toMul)
  letI : Module (ZMod 2) (Additive A) := AddCommGroup.zmodModule h2
  -- the monoid isomorphism `MulAut A ≃* (Additive A ≃ₗ[ZMod 2] Additive A)`
  let f : MulAut A →* (Additive A ≃ₗ[ZMod 2] Additive A) :=
    { toFun := fun σ =>
        (MulEquiv.toAdditive σ).toLinearEquiv (fun (c : ZMod 2) x => ZMod.map_smul _ c x)
      map_one' := by ext x; simp [AddEquiv.coe_toLinearEquiv]
      map_mul' := by intro σ τ; ext x; simp [AddEquiv.coe_toLinearEquiv, LinearEquiv.mul_apply] }
  have hbij : Function.Bijective f := by
    constructor
    · intro x y h
      have h1 : (MulEquiv.toAdditive x : Additive A ≃+ Additive A) = MulEquiv.toAdditive y := by
        ext a
        exact congrArg (fun (e : Additive A ≃ₗ[ZMod 2] Additive A) => e a) h
      exact MulEquiv.toAdditive.injective h1
    · intro y
      refine ⟨MulEquiv.toAdditive.symm (y.toAddEquiv), ?_⟩
      ext a
      simp [f, AddEquiv.coe_toLinearEquiv]
  let e := MulEquiv.ofBijective f hbij
  have hcard1 : Nat.card (MulAut A) = Nat.card (Additive A ≃ₗ[ZMod 2] Additive A) :=
    Nat.card_congr e.toEquiv
  -- `Additive A` is 6-dimensional over `ZMod 2`
  have hfr : Module.finrank (ZMod 2) (Additive A) = 6 := by
    haveI : Fintype (Additive A) := Fintype.ofFinite _
    have h1 : Fintype.card (Additive A)
        = Fintype.card (ZMod 2) ^ Module.finrank (ZMod 2) (Additive A) :=
      Module.card_eq_pow_finrank
    rw [ZMod.card] at h1
    have h2c : Fintype.card (Additive A) = 2 ^ 6 := by
      rw [← Nat.card_eq_fintype_card, Nat.card_congr (Additive.toMul : Additive A ≃ A), hk]
    rw [h2c] at h1
    exact Nat.pow_right_injective (by norm_num : 1 < 2) h1.symm
  have hcard2 : Nat.card (Additive A ≃ₗ[ZMod 2] Additive A)
      = Nat.card (GL (Fin 6) (ZMod 2)) := by
    have hb : Module.Basis (Fin 6) (ZMod 2) (Additive A) :=
      hfr ▸ Module.finBasis (ZMod 2) (Additive A)
    rw [← Nat.card_congr
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) (Additive A)).toEquiv]
    exact (Nat.card_congr (Matrix.GeneralLinearGroup.toLin' hb).toEquiv).symm
  rw [hcard1, hcard2, Matrix.card_GL_field 6]
  simp only [ZMod.card]
  decide

/-- **Bender–Suzuki, Chapter V/VI: solvability of an odd-order point-transitive linear group on a
`64`-element `𝔽₂`-space is elementary once one takes the `5`-part apart.**

Let `A` be a finite elementary abelian `2`-group of order `2 ^ 6 = 64` and `D` a finite group of
**odd** order acting faithfully and transitively on `A ∖ {1}`.  Then `D` is solvable.

The argument is completely free of Feit–Thompson:

* `D` embeds in `Aut A = GL(6, 𝔽₂)`, so `|D| ∣ 20158709760 = 2 ^ 15 * 3 ^ 4 * 5 * 7 ^ 2 * 31`.
* If `5 ∤ |D|`, then `|D| ∣ 3 ^ 4 * 7 ^ 2 * 31`, and a Sylow-counting argument
  (`Work.ThmF.ChV12.solvable_of_card_dvd_two_pow_six_odd_no_five`) gives solvability.
* If `5 ∣ |D|`, then `25 ∤ |D|`, so a Sylow `5`-subgroup `P` has order exactly `5`; since
  `Aut(C₅) = C₄` has `2`-power order while `|D|` is odd, `N_D(P) = C_D(P)`, and Burnside's normal
  `p`-complement theorem (`Work.NPC.burnside_npc`) produces a normal `5`-complement `N ⊴ D` with
  `|D : N| = 5`.  Then `N` again has odd order, `|N| ∣ 20158709760` and `5 ∤ |N|`, so `N` is
  solvable by the previous point, and `D` is solvable as an extension of `N` by the `5`-group
  `D ⧸ N`. -/
theorem isSolvable_of_transitive_of_card_two_pow_six {A D : Type} [Group A] [Finite A] [Group D] [Finite D]
    (hA2 : ∀ x : A, x * x = 1) (hAc : ∀ x y : A, x * y = y * x)
    (hk : Nat.card A = 2 ^ 6) (hodd : Odd (Nat.card D))
    (ρ : D →* MulAut A) (hfaith : Function.Injective ρ)
    (htrans : ∀ a b : A, a ≠ 1 → b ≠ 1 → ∃ d : D, ρ d a = b) :
    Group.IsSolvable D := by
  classical
  have hMul : Nat.card (MulAut A) = 20158709760 := card_mulAut_of_card_two_pow_six hA2 hAc hk
  -- `|D|` divides `|Aut A|`
  have hDvd : Nat.card D ∣ 20158709760 := by
    have h1 : Nat.card D = Nat.card ↥ρ.range :=
      Nat.card_congr (MonoidHom.ofInjective hfaith).toEquiv
    rw [h1]
    exact hMul ▸ Subgroup.card_subgroup_dvd_card ρ.range
  by_cases h5 : 5 ∣ Nat.card D
  · -- ## The case `5 ∣ |D|`
    haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    have h25 : ¬ 25 ∣ Nat.card D := fun h => absurd (dvd_trans h hDvd) (by norm_num)
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 5 D))
    -- `P` has order exactly `5`
    have hPcard : Nat.card (P : Subgroup D) = 5 := by
      obtain ⟨k, hk5⟩ := (IsPGroup.iff_card.mp P.isPGroup')
      have hdvd : 5 ^ k ∣ Nat.card D := hk5 ▸ Subgroup.card_subgroup_dvd_card (P : Subgroup D)
      have hcardmul : Nat.card (P : Subgroup D) * (P : Subgroup D).index = Nat.card D :=
        Subgroup.card_mul_index _
      have hk_le : k ≤ 1 := by
        by_contra h
        have h2k : 2 ≤ k := by omega
        exact h25 (by
          have hdvd' : 5 ^ 2 ∣ Nat.card D := dvd_trans (pow_dvd_pow 5 h2k) hdvd
          rw [show (25 : ℕ) = 5 ^ 2 from by norm_num]
          exact hdvd')
      have hk_ge : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | hpos
        · exfalso
          have hP1 : Nat.card (P : Subgroup D) = 1 := by rw [hk5, h0, pow_zero]
          have hidx : Nat.card D = (P : Subgroup D).index := by
            rw [← hcardmul, hP1, one_mul]
          exact P.not_dvd_index (hidx ▸ h5)
        · exact hpos
      rw [hk5, show k = 1 from le_antisymm hk_le hk_ge, pow_one]
    -- `4` is coprime to the odd number `|D|`
    have hcop : Nat.Coprime (5 - 1) (Nat.card D) := by
      have h2 : Nat.Coprime 2 (Nat.card D) := (Nat.coprime_two_right.mpr hodd).symm
      have h4 : Nat.Coprime 4 (Nat.card D) := by simpa using h2.pow_left 2
      simpa using h4
    have hNC : Subgroup.normalizer (P : Set D) ≤ Subgroup.centralizer (P : Set D) :=
      sylow_normalizer_le_centralizer_of_card_prime P hPcard hcop
    obtain ⟨N, hN⟩ := Work.NPC.burnside_npc P hNC
    haveI hNnormal : N.Normal := hN.normal
    have hNcop5 : ¬ 5 ∣ Nat.card ↥N := by
      intro hdvd
      have hg : (Nat.card ↥N).gcd 5 = 1 := hN.coprime_card
      have hgcd : 5 ∣ (Nat.card ↥N).gcd 5 := Nat.dvd_gcd hdvd (dvd_refl 5)
      rw [hg] at hgcd
      exact absurd hgcd (by norm_num)
    -- the quotient has order `5`
    have hNcard5 : Nat.card (D ⧸ N) = 5 := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_card.mp hN.isPGroup_quotient)
      have hcardmul : Nat.card ↥N * Nat.card (D ⧸ N) = Nat.card D := by
        rw [← Subgroup.index_eq_card]
        exact Subgroup.card_mul_index N
      have hk_le : k ≤ 1 := by
        by_contra h
        have h2k : 2 ≤ k := by omega
        exact h25 (by
          have h2k' : 5 ^ 2 ∣ 5 ^ k := pow_dvd_pow 5 h2k
          have h25' : 25 ∣ Nat.card ↥N * 5 ^ k := by
            rw [show (25 : ℕ) = 5 ^ 2 from by norm_num]
            exact dvd_mul_of_dvd_right h2k' _
          rw [← hcardmul, hk]
          exact h25')
      have hk_ge : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h0 | hpos
        · exfalso
          have h1 : Nat.card ↥N = Nat.card D := by
            have := hcardmul
            rw [hk, h0, pow_zero, mul_one] at this
            exact this
          exact hNcop5 (h1 ▸ h5)
        · exact hpos
      rw [hk, show k = 1 from le_antisymm hk_le hk_ge, pow_one]
    have hNodd : Odd (Nat.card ↥N) := by
      refine Nat.not_even_iff_odd.mp fun he => ?_
      have h2 : ¬ Even (Nat.card D) := Nat.not_even_iff_odd.mpr hodd
      exact h2 (he.trans_dvd (Subgroup.card_subgroup_dvd_card N))
    have hNdvd : Nat.card ↥N ∣ 20158709760 :=
      (Subgroup.card_subgroup_dvd_card N).trans hDvd
    haveI : Group.IsSolvable ↥N :=
      solvable_of_card_dvd_two_pow_six_odd_no_five hNodd hNdvd hNcop5
    haveI : Group.IsNilpotent (D ⧸ N) := hN.isPGroup_quotient.isNilpotent
    exact Group.isSolvable_of_subgroup_quotient N
  · -- ## The case `5 ∤ |D|`
    exact solvable_of_card_dvd_two_pow_six_odd_no_five hodd hDvd h5

end Work.ThmF.ChV12
