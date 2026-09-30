import Mathlib
import Submission.Work.CurveFacts.KrullDim.ringKrullDim_le_of_isStandardEtale
import Submission.Work.CurveFacts.KrullDim.ringKrullDim_le_of_isLocalization
import Submission.Work.CurveFacts.KrullDim.rank_kaehler_of_isStandardEtale
import Submission.Work.AbVar.SmoothReduced.isGeometricallyReduced_of_smooth

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.CurveFacts

universe u

open CategoryTheory AlgebraicGeometry

set_option linter.style.haveILetI false

section CommAlg

/-- **The commutative algebra core of item A2.**  If `A` is a standard smooth algebra of relative
dimension one over a field `K`, then every prime of `A` has height at most one.

The local structure theorem for smooth algebras
(`Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`) gives, for a prime `p`,
an element `f ∉ p` such that `A_f` is standard étale over `P = K[X₁,…,Xₙ]`.  Then

* `A_f` is standard smooth of relative dimension one over `K`, so `Ω[A_f⁄K]` has rank one,
  while standard étaleness over `P` forces `Ω[A_f⁄K]` to have rank `n`
  (`Work.CurveFacts.KrullDim.rank_kaehler_of_isStandardEtale`); hence `n = 1`.
* `A_f` is standard étale over the polynomial ring `P = K[X₁]` of Krull dimension one, and
  standard étaleness does not increase the Krull dimension
  (`Work.CurveFacts.KrullDim.ringKrullDim_le_of_isStandardEtale`); hence
  `ringKrullDim A_f ≤ 1`.
* Height is preserved by the localization `A → A_f` (`IsLocalization.height_map_of_disjoint`),
  and the height of a prime is at most the Krull dimension of the ring, so `p.height ≤ 1`. -/
theorem height_le_one_of_isStandardSmoothOfRelativeDimension_one {K A : Type u} [Field K]
    [CommRing A] [Algebra K A] [Algebra.IsStandardSmoothOfRelativeDimension 1 K A]
    (p : Ideal A) [p.IsPrime] : (p.height : WithBot ℕ∞) ≤ 1 := by
  -- `p` is proper, so `A` is not the zero ring.
  haveI : Nontrivial A := by
    by_contra h
    have hsub : Subsingleton A := not_nontrivial_iff_subsingleton.mp h
    have htop : p = ⊤ :=
      (Ideal.eq_top_iff_one p).mpr (by rw [Subsingleton.elim (1 : A) 0]; exact p.zero_mem)
    exact Ideal.IsPrime.ne_top ‹p.IsPrime› htop
  haveI : Algebra.IsStandardSmooth K A :=
    Algebra.IsStandardSmoothOfRelativeDimension.isStandardSmooth (R := K) (S := A) 1
  haveI : Algebra.Smooth K A := inferInstance
  haveI : Algebra.FinitePresentation K A := inferInstance
  haveI : IsReduced A := Work.AbVar.SmoothReduced.isReduced_of_smooth_of_field K A
  -- local structure theory at `p`
  obtain ⟨f, hf, n, instAlg, hST, hSE⟩ :=
    Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K) (S := A) (p := p)
  letI := instAlg
  haveI : IsScalarTower K (MvPolynomial (Fin n) K) (Localization.Away f) := hST
  haveI : Algebra.IsStandardEtale (MvPolynomial (Fin n) K) (Localization.Away f) := hSE
  have hf0 : f ≠ 0 := fun h => hf (h ▸ p.zero_mem)
  -- `A_f` is nontrivial, since `A` is reduced and `f ≠ 0`
  haveI : Nontrivial (Localization.Away f) := by
    refine ⟨0, 1, fun h => hf0 ?_⟩
    have hz : algebraMap A (Localization.Away f) (1 : A) = 0 := by
      rw [map_one]; exact h.symm
    obtain ⟨m, hm⟩ :=
      (IsLocalization.map_eq_zero_iff (Submonoid.powers f) (Localization.Away f) 1).mp hz
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff (m : A) f).mp m.2
    exact IsReduced.eq_zero f ⟨k, by rw [hk]; simpa using hm⟩
  -- `A_f` is standard smooth of relative dimension one over `K`
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 0 A (Localization.Away f) :=
    Algebra.IsStandardSmoothOfRelativeDimension.localization_away f
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 K (Localization.Away f) := by
    have hcomp := Algebra.IsStandardSmoothOfRelativeDimension.trans (n := 1) (m := 0) (R := K)
      (S := A) (T := Localization.Away f)
    simpa using hcomp
  -- comparing Kähler ranks gives `n = 1`
  have hr1 : Module.rank (Localization.Away f) (KaehlerDifferential K (Localization.Away f)) =
      (1 : Cardinal) :=
    Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential 1
  have hrn : Module.rank (Localization.Away f) (KaehlerDifferential K (Localization.Away f)) =
      (n : Cardinal) :=
    Work.CurveFacts.KrullDim.rank_kaehler_of_isStandardEtale (K := K) (n := n)
      (S := Localization.Away f) instAlg hSE
  have hn : n = 1 := Nat.cast_injective (R := Cardinal) (hrn.symm.trans hr1)
  -- the Krull dimension of the standard étale algebra is at most one
  have hdim : ringKrullDim (Localization.Away f) ≤ (1 : WithBot ℕ∞) := by
    have h1 : ringKrullDim (Localization.Away f) ≤ ringKrullDim (MvPolynomial (Fin n) K) :=
      Work.CurveFacts.KrullDim.ringKrullDim_le_of_isStandardEtale
    have h2 : ringKrullDim (MvPolynomial (Fin n) K) = (n : WithBot ℕ∞) := by
      rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite (R := K) (ι := Fin n)]
      simp
    rw [h2, hn] at h1
    exact h1
  -- heights are preserved by `A → A_f`
  have hdisj : Disjoint ((Submonoid.powers f : Submonoid A) : Set A) (p : Set A) := by
    rw [Set.disjoint_left]
    intro x hx hxp
    obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff x f).mp hx
    exact hf ((‹p.IsPrime› : p.IsPrime).mem_of_pow_mem k (hk.symm ▸ hxp))
  haveI hqprime : (Ideal.map (algebraMap A (Localization.Away f)) p).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint (Submonoid.powers f) (Localization.Away f) p
      ‹p.IsPrime› hdisj
  have hqheight : (Ideal.map (algebraMap A (Localization.Away f)) p).height = p.height :=
    IsLocalization.height_map_of_disjoint (M := Submonoid.powers f) (S := Localization.Away f)
      p hdisj
  have hle : (p.height : WithBot ℕ∞) ≤ ringKrullDim (Localization.Away f) := by
    rw [← hqheight]
    exact Ideal.height_le_ringKrullDim_of_isPrime
  exact hle.trans hdim

end CommAlg

/-- **The local rings of a scheme smooth of relative dimension one over a field have Krull
dimension at most one.**  This is item A2 of the closure design
(`Submission/Work/NOTES_LEAD_jacobian_closure.md` §2.A); it supplies the hypothesis
`Ring.KrullDimLE 1 (stalk z)` required by `Work.CurveBasics.Curve.ofOver`.

Proof route.
1. `SmoothOfRelativeDimension 1 f` unfolds (`smoothOfRelativeDimension_iff`) to: for `z : X`
   there are affine opens `V ∋ z` in `X` and `U` in `Spec K` with `V ≤ f ⁻¹ᵁ U` such that
   `(f.appLE U V e).hom` is standard smooth of relative dimension `1`.  Take `A := Γ(X, V)`; then
   `RingHom.IsStandardSmoothOfRelativeDimension 1` on `Γ(Spec K, U) → Γ(X, V)` gives
   `Algebra.IsStandardSmoothOfRelativeDimension 1 K A` after identifying `Γ(Spec K, U) ≅ K`
   (for `U` nonempty; if `U` is empty then there is no such `V ∋ z`).
2. Let `p` be the prime of `A` at `z`.  By `Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial`
   (`Mathlib/RingTheory/Unramified/LocalStructure.lean`) there is `f ∉ p` such that `A_f` is
   standard étale over `P = MvPolynomial (Fin n) K`.
3. **`n = 1`**: `Ω[A_f⁄K] ≅ A_f ⊗[P] Ω[P⁄K]` is free of rank `n`
   (`Work.CurveFacts.KrullDim.rank_kaehler_of_isStandardEtale`), while `A_f` is standard smooth
   of relative dimension `1` over `K`, so `Module.rank A_f Ω[A_f⁄K] = 1`
   (`Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential`).  Comparing ranks
   gives `n = 1`.
4. **Dimension**: `A_f` is standard étale over `P = K[X_1]`, so
   `ringKrullDim A_f ≤ ringKrullDim P = 1`
   (`Work.CurveFacts.KrullDim.ringKrullDim_le_of_isStandardEtale`, together with
   `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite`).
5. Finally `ringKrullDim (stalk z) = height p ≤ ringKrullDim A_f ≤ 1`, using
   `IsLocalization.AtPrime.ringKrullDim_eq_height` and `Ideal.height_le_ringKrullDim_of_isPrime`;
   `Ring.krullDimLE_iff` converts this into `Ring.KrullDimLE 1 (X.presheaf.stalk z)`.

Steps 1–4 are carried out in the commutative algebra lemma
`Work.CurveFacts.height_le_one_of_isStandardSmoothOfRelativeDimension_one` above; the present
theorem reduces to it by identifying the stalk with the localization of `Γ(X,V)` at the prime
of `z`. -/
theorem krullDimLE_stalk_of_smoothOfRelativeDimension_one {K : Type u} [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [SmoothOfRelativeDimension 1 f] (z : X) :
    Ring.KrullDimLE 1 (X.presheaf.stalk z) := by
  -- the affine chart of the local structure theorem
  obtain ⟨U, hU, V, hV, hzV, e, hφ⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := f) z
  have hfz : f z ∈ U := (Scheme.Hom.mem_preimage f).mp (e hzV)
  -- `Spec K` is a one-point space, so the nonempty open `U` is everything
  have hUtop : U = ⊤ := by
    haveI : Subsingleton (Spec (CommRingCat.of K)) := inferInstance
    refine TopologicalSpace.Opens.ext ?_
    rw [TopologicalSpace.Opens.coe_top]
    exact Set.eq_univ_of_forall fun y => by
      rw [Subsingleton.elim y (f z)]
      exact hfz
  subst hUtop
  -- the `K`-algebra structure on the coordinate ring `Γ(X,V)`
  let σe : K ≃+* Γ(Spec (CommRingCat.of K), ⊤) :=
    CategoryTheory.Iso.commRingCatIsoToRingEquiv (Scheme.ΓSpecIso (CommRingCat.of K)).symm
  let ψ : K →+* Γ(X, V) :=
    (f.appLE ⊤ V e).hom.comp (σe : K →+* Γ(Spec (CommRingCat.of K), ⊤))
  have hψ : ψ.IsStandardSmoothOfRelativeDimension 1 := by
    have h := RingHom.IsStandardSmoothOfRelativeDimension.comp hφ
      (RingHom.IsStandardSmoothOfRelativeDimension.equiv σe)
    simpa [ψ] using h
  letI : Algebra K Γ(X, V) := ψ.toAlgebra
  have hψ' : (algebraMap K Γ(X, V)).IsStandardSmoothOfRelativeDimension 1 := by
    have h : algebraMap K Γ(X, V) = ψ := RingHom.algebraMap_toAlgebra ψ
    rwa [h]
  haveI : Algebra.IsStandardSmoothOfRelativeDimension 1 K Γ(X, V) :=
    (RingHom.isStandardSmoothOfRelativeDimension_algebraMap (n := 1)).mp hψ'
  -- the commutative algebra estimate at the prime of `z`
  have hca := height_le_one_of_isStandardSmoothOfRelativeDimension_one (K := K) (A := Γ(X, V))
    (hV.primeIdealOf ⟨z, hzV⟩)
  rw [Ring.krullDimLE_iff]
  letI : Algebra Γ(X, V) (X.presheaf.stalk z) :=
    TopCat.Presheaf.algebra_section_stalk X.presheaf (U := V) ⟨z, hzV⟩
  haveI : IsLocalization.AtPrime (X.presheaf.stalk z) (hV.primeIdealOf ⟨z, hzV⟩).asIdeal :=
    hV.isLocalization_stalk ⟨z, hzV⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height (hV.primeIdealOf ⟨z, hzV⟩).asIdeal
    (X.presheaf.stalk z)]
  exact hca

end Work.CurveFacts
