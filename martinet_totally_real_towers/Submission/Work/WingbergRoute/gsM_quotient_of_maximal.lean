import Mathlib
import Submission.Work.WingbergRoute.Defs
import Submission.Work.WingbergRoute.gsM_aut_gsF_equiv_pi
import Submission.Work.QuadraticFields.CertificateRealSummary
import Submission.Work.ClassFieldTower.All

/-!
# `G_∅(gsF)` has `(ℤ/2)^6` as a quotient

The totally real quadratic field `F = gsF = ℚ(√(5·13·17·29·37·41·53))` carries the unramified
multiquadratic extension

  `M = gsM = ℚ(√5, √13, √17, √29, √37, √41, √53)`

of degree `2^6 = 64` (`Work.QuadraticFields.gs_certificate`: `M/F` is unramified at all finite
primes, at the infinite places, and `[M : F] = 64`).  Because `M/F` is a compositum of quadratic
extensions, its automorphism group has exponent `2` (`M` is generated over `F` by the square roots
`gsRoot a`, each of which is sent to `±` itself by every `F`-automorphism), and it has `2^6`
elements; hence

  `Gal(M/F) ≃* (ℤ/2)^6 = Multiplicative (Fin 6 → ZMod 2)`.

Since `M/F` is unramified, finite and Galois with a `2`-group as Galois group, the universal
property of the maximal unramified pro-`2` extension `M_∅` of `F` (definitionally: the
`MaximalUnramifiedProP` hypothesis is the totality of finite unramified `2`-Galois quotients)
exhibits `Gal(M/F)` as a quotient of `G_∅ = Gal(M_∅/F)`
(`Work.ClassFieldTower.exists_surjective_galoisGroup_of_finite_unramified`).  Composing the two
gives the statement below: `G_∅` admits `(ℤ/2)^6` as a quotient, i.e. the generator rank of `G_∅`
is at least `6`.

This is the numerical input of the totally real (unramified, Wingberg) route: with `d ≥ 6` and
Shafarevich's relation bound `r ≤ d + d₂(O_F^×) = d + 2`, Golod--Shafarevich gives `4r ≤ 4d + 8 ≤ d²`
and hence an infinite unramified pro-`2` tower over the totally real field `F`.

## Main result

* `Work.WingbergRoute.gsM_quotient_of_maximal`.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

open scoped NumberField
open NumberField

namespace Work.WingbergRoute

open Work.QuadraticFields

noncomputable section

/-- **`(ℤ/2)^6` is a quotient of the maximal unramified pro-`2` Galois group of `gsF`.**

The unramified multiquadratic certificate `gsM/gsF` has degree `64 = 2^6` and Galois group of
exponent `2`, so it is `(ℤ/2)^6`; it is a quotient of the maximal unramified pro-`2` extension.
-/
theorem gsM_quotient_of_maximal
    (M : Work.ClassFieldTower.MaximalUnramifiedProP.{0} ↥Work.QuadraticFields.gsF 2) :
    ∃ φ : Work.ClassFieldTower.galoisGroup M →* (Fin 6 → Multiplicative (ZMod 2)),
      Function.Surjective φ := by
  classical
  -- `gsM` is Galois over `ℚ` (it is multiquadratic), hence over the intermediate field `gsF`.
  haveI hgalQ : IsGalois ℚ gsM := multiQuad_isGalois gsPrimesQ
  haveI hgal : IsGalois ↥Work.QuadraticFields.gsF gsM :=
    IsGalois.tower_top_of_isGalois (F := ℚ) (E := gsM) Work.QuadraticFields.gsF
  -- `[gsM : gsF] = 64`, so `gsM/gsF` is finite dimensional.
  haveI hfd : FiniteDimensional ↥Work.QuadraticFields.gsF gsM :=
    Module.finite_of_finrank_eq_succ (by rw [gs_finrank])
  -- The group of automorphisms is finite, with `2 ^ 6` elements (Galois correspondence).
  haveI hfin : Fintype (gsM ≃ₐ[↥Work.QuadraticFields.gsF] gsM) :=
    AlgEquiv.fintype (↥Work.QuadraticFields.gsF) gsM
  have hcard : Nat.card (gsM ≃ₐ[↥Work.QuadraticFields.gsF] gsM) = 2 ^ 6 := by
    rw [IsGalois.card_aut_eq_finrank, gs_finrank]
    norm_num
  -- Every `gsF`-automorphism fixes `ℚ` (the scalars factor through the subfield `gsF`).
  have hrat : ∀ (q : ℚ) (x : gsM ≃ₐ[↥Work.QuadraticFields.gsF] gsM),
      x (algebraMap ℚ gsM q) = algebraMap ℚ gsM q := by
    intro q x
    rw [IsScalarTower.algebraMap_apply ℚ ↥Work.QuadraticFields.gsF gsM q]
    exact AlgEquiv.commutes x (algebraMap ℚ ↥Work.QuadraticFields.gsF q)
  -- `gsM` is generated over `ℚ` by the square roots `gsRoot a`; each is sent to `±` itself,
  -- so every `gsF`-automorphism is an involution.
  have hexp : ∀ x : gsM ≃ₐ[↥Work.QuadraticFields.gsF] gsM, x ^ 2 = 1 := by
    intro x
    have hgen : Algebra.adjoin ℚ (gsRoot '' (gsPrimes : Set ℤ)) = ⊤ := by
      rw [← IntermediateField.adjoin_eq_top_iff]
      exact gsRoot_generates
    rw [pow_two]
    refine AlgEquiv.ext (fun y => ?_)
    rw [AlgEquiv.mul_apply, AlgEquiv.one_apply]
    have hy : y ∈ Algebra.adjoin ℚ (gsRoot '' (gsPrimes : Set ℤ)) := by rw [hgen]; trivial
    refine Algebra.adjoin_induction (p := fun z _ => x (x z) = z) ?_ ?_ ?_ ?_ hy
    · rintro z ⟨a, ha, rfl⟩
      -- `x (gsRoot a)` is again a square root of `a`, hence `± gsRoot a`
      have h1 : x ((gsRoot a) ^ 2) = (gsRoot a) ^ 2 := by
        rw [gsRoot_sq a ha]
        exact hrat (a : ℚ) x
      have hsq : (x (gsRoot a)) ^ 2 = (gsRoot a) ^ 2 := by simpa only [map_pow] using h1
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
      · rw [h, h]
      · rw [h, map_neg, h, neg_neg]
    · intro r
      rw [hrat r x, hrat r x]
    · intro y z _ _ hy hz
      rw [map_add, map_add, hy, hz]
    · intro y z _ _ hy hz
      rw [map_mul, map_mul, hy, hz]
  -- A group of exponent `2` is commutative.
  haveI hcomm : IsMulCommutative (gsM ≃ₐ[↥Work.QuadraticFields.gsF] gsM) :=
    isMulCommutative_iff.mpr (fun a b => by
      have hinv : ∀ x : gsM ≃ₐ[↥Work.QuadraticFields.gsF] gsM, x⁻¹ = x := fun x =>
        inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hexp x)
      calc a * b = (a * b)⁻¹ :=
            (inv_eq_of_mul_eq_one_right (by rw [← pow_two]; exact hexp (a * b))).symm
        _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
        _ = b * a := by rw [hinv b, hinv a])
  -- An elementary abelian `2`-group of order `2 ^ 6` is `(ℤ/2)^6`.
  obtain ⟨e⟩ :=
    Commons.GroupTheory.SpecificGroups.ZModProd.exists_mulEquiv_multiplicative_fin_zmod_two_of_fintype_commutative_pow_two_eq_one_card
      hexp hcard
  -- `gsM/gsF` is unramified at the finite places, with a `2`-group as Galois group.
  have hunr : differentIdeal (𝓞 ↥Work.QuadraticFields.gsF) (𝓞 gsM) = ⊤ :=
    Work.ClassFieldTower.differentIdeal_eq_top_of_isUnramifiedAtFinitePrimes gs_unramified
  have hpg : IsPGroup 2 (gsM ≃ₐ[↥Work.QuadraticFields.gsF] gsM) := IsPGroup.of_card hcard
  -- Hence `Gal(gsM/gsF)` is a quotient of the maximal unramified pro-`2` group `G_∅`.
  obtain ⟨ψ, hψ⟩ :=
    Work.ClassFieldTower.exists_surjective_galoisGroup_of_finite_unramified M gsM hunr hpg
  -- Compose with the isomorphism `(ℤ/2)^6 ≃ (Fin 6 → Multiplicative (ZMod 2))`.
  refine ⟨(e.trans (MulEquiv.funMultiplicative (Fin 6) (ZMod 2))).toMonoidHom.comp ψ, ?_⟩
  intro y
  obtain ⟨z, hz⟩ := (MulEquiv.funMultiplicative (Fin 6) (ZMod 2)).surjective y
  obtain ⟨w, hw⟩ := e.surjective z
  obtain ⟨v, hv⟩ := hψ w
  exact ⟨v, by simp [hz, hw, hv]⟩

end

end Work.WingbergRoute
