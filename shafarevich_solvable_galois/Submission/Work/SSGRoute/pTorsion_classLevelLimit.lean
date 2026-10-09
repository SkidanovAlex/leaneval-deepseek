import Mathlib
import Submission.Work.SSGRoute.phi0_realization_in
import Submission.Work.SSGRoute.phi0_pTor_scalar
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- **The `p`-torsion of `A = colim_L H²(Gal(L/k), C_L)` has `p` elements.**

For a level `L₀` with `p ∣ [L₀:k]` (`Work.SSGRoute.exists_galois_level_p_dvd`,
`Work.SSGRoute.phi0_pTor_scalar.exists_lvl_finrank_dvd`), `H²(Gal(L₀/k),C_{L₀})` is cyclic of order
`[L₀:k]` (the class formation / fundamental class `NK.CFTLib.fundamentalClassElement`), so its
`p`-torsion is `ℤ/p` (`Work.SSGRoute.pt_char_pTorsion`); `ClassLevelLimit.of L₀` is injective
(`Work.SSGRoute.ClassLevelLimit.of_injective` in `Submission/Work/SSGRoute/phi0_realization_in.lean`)
and `Work.SSGRoute.pTor_classLevel_surj` shows every `y ∈ A[p]` is `of L₀ v` for a `p`-torsion `v`.
Hence `|A[p]| = p`. -/
theorem pTorsion_classLevelLimit (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω] :
    Nat.card {y : ClassLevelLimit (k := k) (K := K) (Ω := Ω) // p • y = 0} = p := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  -- a level `L₀` whose degree over `k` is divisible by `p`
  obtain ⟨L₀, hp₀⟩ := exists_lvl_finrank_dvd p k K Ω
  -- the `p`-torsion of `H²(Gal(L₀/k), C_{L₀})` is `ℤ/p`
  obtain ⟨P, χ, hP, hχ⟩ := pt_char_pTorsion p k K ↥L₀.1 hp₀
  let χe : ↥P ≃+ ZMod p := AddEquiv.ofBijective χ hχ
  -- the colimit map `P → A[p]`
  let gP : ↥P →+
      ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω))) :=
    pTorClassLevelHom p L₀ P hP
  have hgP_inj : Function.Injective gP := by
    intro x y hxy
    apply Subtype.ext
    refine ClassLevelLimit.of_injective (k := k) (K := K) (Ω := Ω) L₀ ?_
    have h := congrArg (fun z : ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω))) =>
      (z : ClassLevelLimit (k := k) (K := K) (Ω := Ω))) hxy
    simpa [gP, pTorClassLevelHom] using h
  have hgP_surj : Function.Surjective gP := by
    intro y
    obtain ⟨v, hv, hvy⟩ := pTor_classLevel_surj p k K Ω L₀ hp₀ y
    refine ⟨⟨v, (hP v).mpr hv⟩, ?_⟩
    apply Subtype.ext
    exact hvy
  have hbij : Nat.card ↥P
      = Nat.card ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω))) :=
    Nat.card_congr (Equiv.ofBijective gP ⟨hgP_inj, hgP_surj⟩)
  have hcard : Nat.card ↥P = p := by
    rw [Nat.card_congr χe.toEquiv, Nat.card_eq_fintype_card, ZMod.card]
  change Nat.card ↥(pTor p (ClassLevelLimit (k := k) (K := K) (Ω := Ω))) = p
  rw [← hbij, hcard]

end Work.SSGRoute
