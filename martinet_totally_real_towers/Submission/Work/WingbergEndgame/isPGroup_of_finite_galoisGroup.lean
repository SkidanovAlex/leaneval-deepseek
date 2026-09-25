import Mathlib
import Submission.Work.WingbergEndgame.Defs

/-!
# `Work.WingbergEndgame.isPGroup_of_finite_galoisGroup`

A **finite** Galois group `Γ = Gal(F_∞/F)` of the wide maximal pro-`2` extension of a number
field `F` (`Work.WingbergEndgame.UnramifiedProTwoExtension`) is a `2`-group.

## The mathematics

Write `Γ = E.K ≃ₐ[F] E.K`.  The extension `E.K/F` is a (possibly infinite) Galois extension, but
the argument does not need it to be finite: it works one element at a time.

Let `σ ∈ Γ` with `σ ≠ 1`, of finite order `m = orderOf σ`, and suppose `m` has an odd prime
divisor `q`.  Then `τ := σ^(m/q)` has order `q`, so it is nontrivial, so it moves some `x ∈ E.K`.
Let `L ⊆ E.K` be the normal closure of `F⟮x⟯` inside `E.K`; it is a *finite dimensional* Galois
extension of `F` (this is why we work inside `E.K`, which is Galois over `F`), and hence by the
`proP` clause of `UnramifiedProTwoExtension` its Galois group `Gal(L/F)` is a finite `2`-group.

The restriction map `ρ : Γ →* Gal(L/F)` sends `τ` to a *nontrivial* element (`τ` moves
`x ∈ L`), whose order divides `q`.  But in a finite `2`-group the order of every element is a
power of `2`, so `orderOf (ρ τ) ∣ 2 ^ n` for some `n`, and together with `orderOf (ρ τ) ∣ q` this
forces `orderOf (ρ τ) = 1` -- a contradiction.  Hence `m` is a power of `2` for every `σ ∈ Γ`,
which is exactly `IsPGroup 2 Γ`.

Note that well-definedness of `orderOf` (and `orderOf_pos`) is the only place where
`Finite Γ` is used; the *field-theoretic* input is used only through `E.proP` on the finite
dimensional Galois subextensions.
-/

set_option linter.style.haveILetI false

open scoped Classical

namespace Work.WingbergEndgame

theorem isPGroup_of_finite_galoisGroup {F : Type} [Field F] [NumberField F]
    (E : Work.WingbergEndgame.UnramifiedProTwoExtension F)
    (hfin : Finite (Work.WingbergEndgame.galoisGroup E)) :
    IsPGroup 2 (Work.WingbergEndgame.galoisGroup E) := by
  classical
  haveI := hfin
  haveI hgalK : IsGalois F E.K := E.galoisK
  rw [IsPGroup]
  intro σ
  -- the order of `σ` is a power of `2`
  rcases Nat.eq_two_pow_or_exists_odd_prime_and_dvd (orderOf σ) with ⟨k, hk⟩ | ⟨q, hqprime, hqdvd, hqodd⟩
  · exact ⟨k, (orderOf_dvd_iff_pow_eq_one (x := σ) (n := 2 ^ k)).mp (by rw [hk])⟩
  · -- suppose an odd prime `q` divides the order of `σ`
    exfalso
    set τ : Work.WingbergEndgame.galoisGroup E := σ ^ (orderOf σ / q) with hτdef
    have hτq : τ ^ q = 1 := by
      rw [hτdef, ← pow_mul, Nat.div_mul_cancel hqdvd, pow_orderOf_eq_one]
    have hτne : τ ≠ 1 := by
      intro h
      have hp : σ ^ (orderOf σ / q) = 1 := hτdef ▸ h
      have hdvd' : orderOf σ ∣ orderOf σ / q := orderOf_dvd_iff_pow_eq_one.mpr hp
      have hmpos : 0 < orderOf σ := orderOf_pos σ
      have hkpos : 0 < orderOf σ / q := Nat.div_pos (Nat.le_of_dvd hmpos hqdvd) hqprime.pos
      have hle : orderOf σ ≤ orderOf σ / q := Nat.le_of_dvd hkpos hdvd'
      have hlt : orderOf σ / q < orderOf σ := Nat.div_lt_self hmpos hqprime.one_lt
      omega
    -- `τ` moves some element of `F_∞`
    obtain ⟨x, hx⟩ : ∃ x : E.K, τ x ≠ x := by
      by_contra h
      refine hτne (AlgEquiv.ext fun y => ?_)
      exact not_not.mp (not_exists.mp h y)
    -- the normal closure of `F⟮x⟯` inside `F_∞` is a finite dimensional Galois extension of `F`
    let E₀ : IntermediateField F E.K := IntermediateField.adjoin F ({x} : Set E.K)
    haveI hfdE₀ : FiniteDimensional F E₀ :=
      IntermediateField.finiteDimensional_adjoin (S := ({x} : Set E.K))
        (fun z _ => IsGalois.integral F z)
    let L : IntermediateField F E.K := IntermediateField.normalClosure F E₀ E.K
    haveI hfdL : FiniteDimensional F L := normalClosure.is_finiteDimensional F E₀ E.K
    haveI hgalL : IsGalois F L := IsGalois.normalClosure F E₀ E.K
    haveI hnormL : Normal F L := inferInstance
    haveI hnumL : NumberField ↥L := NumberField.of_module_finite F ↥L
    -- `Gal(L/F)` is a finite `2`-group by the `proP` clause, and `F⟮x⟯ ⊆ L`
    have hpgL : IsPGroup 2 (↥L ≃ₐ[F] ↥L) := E.proP L hfdL hgalL
    set ρ : ↥L ≃ₐ[F] ↥L := (AlgEquiv.restrictNormalHom (F := F) (K₁ := E.K) ↥L) τ with hρdef
    have hρne : ρ ≠ 1 := by
      intro h
      have hxmem : x ∈ L :=
        (IntermediateField.subset_adjoin F ({x} : Set E.K)).trans
          (IntermediateField.le_normalClosure E₀) (by simp)
      have h1 : ρ ⟨x, hxmem⟩ = (1 : ↥L ≃ₐ[F] ↥L) ⟨x, hxmem⟩ := by rw [h]
      have h2 : (↑(ρ ⟨x, hxmem⟩) : E.K) = (↑(⟨x, hxmem⟩ : ↥L) : E.K) := by rw [h1]; rfl
      rw [hρdef] at h2
      rw [AlgEquiv.restrictNormalHom_apply L τ ⟨x, hxmem⟩] at h2
      exact hx h2
    have hρq : ρ ^ q = 1 := by
      rw [hρdef, ← map_pow, hτq, map_one]
    -- in a finite `2`-group every element has order a power of `2`
    obtain ⟨n, hn⟩ := hpgL ρ
    have h1 : orderOf ρ ∣ q := orderOf_dvd_iff_pow_eq_one.mpr hρq
    have h2 : orderOf ρ ∣ 2 ^ n := orderOf_dvd_iff_pow_eq_one.mpr hn
    rcases (Nat.dvd_prime hqprime).mp h1 with h | h
    · exact hρne (orderOf_eq_one_iff.mp h)
    · have h2dvd : q ∣ 2 := hqprime.dvd_of_dvd_pow (h ▸ h2)
      have hqle : q ≤ 2 := Nat.le_of_dvd (by norm_num) h2dvd
      have hqge : 2 ≤ q := hqprime.two_le
      obtain ⟨j, hj⟩ := hqodd
      omega

end Work.WingbergEndgame
