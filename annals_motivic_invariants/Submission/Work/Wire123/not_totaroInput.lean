import Mathlib
import Submission.Work.Wire123.Defs
import Submission.Work.CY3.Totaro
import Submission.Work.Totaro.StablyBirationalLaws
import Submission.Work.K3Inputs.exists_variety_prodOver_affineSpace

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Wire123

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

noncomputable section

/-- **`X 0 ∈ 𝕜[X]` is never a unit.**  If `X 0 * p = 1` then evaluating at `0` gives
`0 * eval p = 1`, i.e. `0 = 1`. -/
lemma mvPolynomial_X_zero_not_isUnit (𝕜 : Type) [CommSemiring 𝕜] [Nontrivial 𝕜] :
    ¬ IsUnit (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) 𝕜) := by
  rintro ⟨u, hu⟩
  have h : (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) 𝕜) * ↑u⁻¹ = 1 := by
    rw [← hu, Units.mul_inv]
  have hc := congrArg (MvPolynomial.eval (fun _ : Fin 1 => (0 : 𝕜))) h
  simp only [map_mul, map_one, MvPolynomial.eval_X, zero_mul] at hc
  exact zero_ne_one hc

/-- **There is no ring equivalence `𝕜 ≃+* 𝕜[X]`** for `𝕜` a field: a ring equivalence transports
units, so every nonzero element of `𝕜[X]` would be a unit (as `𝕜` is a field), whereas `X` is a
nonzero non-unit. -/
lemma not_ringEquiv_mvPolynomial_one (𝕜 : Type) [Field 𝕜] :
    ¬ Nonempty (MvPolynomial (Fin 1) 𝕜 ≃+* 𝕜) := by
  rintro ⟨f⟩
  have h1 : IsUnit (f (MvPolynomial.X (0 : Fin 1))) :=
    isUnit_iff_ne_zero.mpr (fun hc => MvPolynomial.X_ne_zero (0 : Fin 1)
      (f.injective (by rw [hc, map_zero])))
  have h2 : IsUnit (f.symm (f (MvPolynomial.X (0 : Fin 1)))) := h1.map f.symm
  rw [RingEquiv.symm_apply_apply] at h2
  exact mvPolynomial_X_zero_not_isUnit 𝕜 h2

/-- **`𝔸⁰` and `𝔸¹` are not isomorphic over `𝕜`.**  An isomorphism over the base induces an
isomorphism of the global section rings `𝕜[X] ≅ 𝕜`, which is impossible. -/
theorem not_isoOver_affineSpace_zero_one (𝕜 : Type) [Field 𝕜] :
    ¬ Work.CY3.IsoOver 𝕜 (𝔸(Fin 0; Spec (.of 𝕜))) (𝔸(Fin 1; Spec (.of 𝕜))) := by
  rintro ⟨e, _⟩
  -- Transport the isomorphism to the spectra of the polynomial rings.
  have e' : Spec (CommRingCat.of (MvPolynomial (Fin 0) 𝕜)) ≅
      Spec (CommRingCat.of (MvPolynomial (Fin 1) 𝕜)) :=
    (AffineSpace.SpecIso (Fin 0) (CommRingCat.of 𝕜)).symm ≪≫ e
      ≪≫ (AffineSpace.SpecIso (Fin 1) (CommRingCat.of 𝕜))
  -- Global sections: `𝕜[X] ≅ 𝕜`.
  let isoR : CommRingCat.of (MvPolynomial (Fin 1) 𝕜) ≅
      CommRingCat.of (MvPolynomial (Fin 0) 𝕜) :=
    (Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 1) 𝕜))).symm
      ≪≫ Scheme.Γ.mapIso e'.op
      ≪≫ Scheme.ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 0) 𝕜))
  exact not_ringEquiv_mvPolynomial_one 𝕜
    ⟨(Iso.commRingCatIsoToRingEquiv isoR).trans
      (MvPolynomial.isEmptyAlgEquiv 𝕜 (Fin 0)).toRingEquiv⟩

/-- **`𝔸⁰` and `𝔸¹` are stably birational.**  Take the exponents `n = 1`, `m = 0`: both products
are the fibre product over `Spec 𝕜` of the same two structure morphisms, in the two orders, and the
two are isomorphic by the symmetry of the pullback. -/
theorem stablyBirational_affineSpace_zero_one (𝕜 : Type) [Field 𝕜] :
    Work.CY3.StablyBirational 𝕜 (𝔸(Fin 0; Spec (.of 𝕜))) (𝔸(Fin 1; Spec (.of 𝕜))) := by
  refine ⟨1, 0, ?_, ?_, ?_⟩
  · exact Classical.choice
      (Work.K3Inputs.exists_variety_prodOver_affineSpace 𝕜 (𝔸(Fin 0; Spec (.of 𝕜))) 1)
  · exact Classical.choice
      (Work.K3Inputs.exists_variety_prodOver_affineSpace 𝕜 (𝔸(Fin 1; Spec (.of 𝕜))) 0)
  · -- the two products are `pullback` of the two structure morphisms in the two orders
    haveI h1 : Variety 𝕜 (pullback ((𝔸(Fin 0; Spec (.of 𝕜))) ↘ Spec (.of 𝕜))
      ((𝔸(Fin 1; Spec (.of 𝕜))) ↘ Spec (.of 𝕜))) :=
      Classical.choice
        (Work.K3Inputs.exists_variety_prodOver_affineSpace 𝕜 (𝔸(Fin 0; Spec (.of 𝕜))) 1)
    haveI h2 : Variety 𝕜 (pullback ((𝔸(Fin 1; Spec (.of 𝕜))) ↘ Spec (.of 𝕜))
      ((𝔸(Fin 0; Spec (.of 𝕜))) ↘ Spec (.of 𝕜))) :=
      Classical.choice
        (Work.K3Inputs.exists_variety_prodOver_affineSpace 𝕜 (𝔸(Fin 1; Spec (.of 𝕜))) 0)
    exact ⟨(PartialIso.ofIso (pullbackSymmetry (𝔸(Fin 0; Spec (.of 𝕜)) ↘ Spec (.of 𝕜))
      (𝔸(Fin 1; Spec (.of 𝕜)) ↘ Spec (.of 𝕜)))).toBirationalMap⟩

/-- In namespace `Work.Wire123`, file `Submission/Work/Wire123/not_totaroInput.lean` (module `Submission.Work.Wire123.not_totaroInput`). The universal named input `Work.CY3.TotaroInput 𝕜` is refutable: its single field asserts `¬ IsoOver 𝕜 X Y → ¬ StablyBirational 𝕜 X Y` for *every* pair of `𝕜`-varieties, its geometric hypotheses `Work.CY3.IsKTrivial` and `Work.CY3.PicardRankOne` being classes with no fields (hence satisfied by every `𝕜`-variety), and that general statement is false: two non-isomorphic varieties can perfectly well be stably birational. This is the second half of the diagnosis that the delivered `n ≥ 5` reduction `Work.CY3Stab.theorem_1_2_3_of_G2` is uninstantiable.

GUIDANCE FOR THE PROOF: refute it at the pair `X := 𝔸(Fin 0; Spec (.of 𝕜))` and `Y := 𝔸(Fin 1; Spec (.of 𝕜))` (both have the `Variety` instance of `ChallengeDeps.lean`). The two facts to prove are

* `¬ Work.K3.IsoOver 𝕜 (𝔸(Fin 0; Spec (.of 𝕜))) (𝔸(Fin 1; Spec (.of 𝕜)))`.  Note `𝔸(Fin n; Spec (.of 𝕜)) = Spec (MvPolynomial (Fin n) 𝕜)`.  An `IsoOver` is `∃ e : X ≅ Y, e.hom.IsOver (Spec (.of 𝕜))`; `e` induces a ring equivalence `MvPolynomial (Fin 0) 𝕜 ≃+* MvPolynomial (Fin 1) 𝕜` (via `Scheme.Γ.mapIso e` and `Scheme.ΓSpecIso`; the `IsOver`-hypothesis is not needed for this).  Composing with `MvPolynomial.isEmptyAlgEquiv` (`[IsEmpty (Fin 0)]`) gives a ring equivalence `𝕜 ≃+* MvPolynomial (Fin 1) 𝕜`, which is impossible: from a ring equivalence the inverse of a nonzero element transports from the field `𝕜`, so every nonzero element of `MvPolynomial (Fin 1) 𝕜` would be a unit, while `MvPolynomial.X 0` is not a unit (evaluate at `0`: `eval 0 (X 0 * p) = 0 ≠ 1`); `MvPolynomial.X 0 ≠ 0` follows from the coefficient/single API of `MvPolynomial`.
* `Work.K3.StablyBirational 𝕜 (𝔸(Fin 0; Spec (.of 𝕜))) (𝔸(Fin 1; Spec (.of 𝕜)))`.  Here `StablyBirational` is `∃ n m, Variety 𝕜 (prodOver 𝕜 X (𝔸(Fin n))) → ... → Nonempty (BirationalMap ...)`: take the exponents `n = 1`, `m = 0`, so that both sides are pullbacks over `Spec 𝕜` of the same two legs in the two orders — `prodOver 𝕜 (𝔸⁰) (𝔸¹) = pullback (𝔸⁰ ↘ Spec 𝕜) (𝔸¹ ↘ Spec 𝕜)` and `prodOver 𝕜 (𝔸¹) (𝔸⁰) = pullback (𝔸¹ ↘ Spec 𝕜) (𝔸⁰ ↘ Spec 𝕜)` — and use `CategoryTheory.Limits.pullbackSymmetry` (or the workspace's canonical product isomorphisms, e.g. `Work.Totaro.partialIso_prod_affine`) to get an isomorphism of the two products, from which `Scheme.PartialIso.toBirationalMap` (see `Submission/Work/Totaro/stablyBirational_of_birationalMap.lean` for the pattern, including `Work.K3Inputs.exists_variety_prodOver_affineSpace` for the two `Variety` instances that `StablyBirational` carries as explicit arguments) gives the birational map.

Finally the contradiction: from `T : Work.CY3.TotaroInput 𝕜` get `T.not_stablyBirat_of_not_iso X Y ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ hne : ¬ Work.K3.StablyBirational 𝕜 X Y` and apply it to the stable birationality just proved.  If the pair `(𝔸⁰, 𝔸¹)` turns out to be too costly, the pair `(𝔸(Fin 1; Spec 𝕜), ℙ¹)` works as well (non-isomorphism then needs `Γ(ℙ¹) = 𝕜`, `StablyBirational` is immediate from `Work.CY3.projectiveLine_birational_affineLine`). No `sorry`; build with `lake build Submission.Work.Wire123.not_totaroInput`. -/
theorem not_totaroInput (𝕜 : Type) [Field 𝕜] : ¬ Work.CY3.TotaroInput 𝕜 := by
  intro T
  exact (T.not_stablyBirat_of_not_iso (𝔸(Fin 0; Spec (.of 𝕜))) (𝔸(Fin 1; Spec (.of 𝕜)))
      ⟨⟩ ⟨⟩ ⟨⟩ ⟨⟩ (not_isoOver_affineSpace_zero_one 𝕜))
    (stablyBirational_affineSpace_zero_one 𝕜)

end

end Work.Wire123
