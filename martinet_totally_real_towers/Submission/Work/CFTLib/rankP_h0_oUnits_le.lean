import Mathlib
import Submission.Work.CFTLib.RelShafReps
import Submission.Work.CFTLib.RelShafDefs
import Submission.Work.CFT.IdeleClassGroup.tateCohomology_zero_iso
import Submission.Work.CFT.ClassFormation.rankP_eq_of_addEquiv
import Submission.Work.CFT.Kummer.finrank_unitsModPow
import Submission.Work.CFT.Kummer.finite_unitsModPow
import Submission.Work.CFTLib.rankP_eq_finrank_unitsModPow
import Submission.Work.CFTLib.oUnits_invariants_surjective

/-!
# The `p`-rank of `Ĥ⁰(Gal(K/F), 𝒪_Kˣ)` is bounded by `r₁ + r₂ − 1 + δ_p(F)`

For a finite Galois extension `K/F` of number fields with group `G = Gal(K/F)`, the zeroth Tate
cohomology `Ĥ⁰(G, 𝒪_Kˣ) = (𝒪_Kˣ)^G / N_{K/F}(𝒪_Kˣ)` is a quotient of the units of the base field:
by Galois descent `(𝒪_Kˣ)^G = 𝒪_Fˣ` (`oUnits_invariants_surjective`), and `Ĥ⁰` is a quotient of the
invariants (`tateCohomology_zero_iso`).  Passing to `𝔽_p`-ranks and applying Dirichlet's unit
theorem, `rank_p (𝒪_Fˣ) = (r₁ + r₂ − 1) + δ_p(F)`.

## Main result

* `Work.CFTLib.rankP_h0_oUnits_le`
-/

open scoped TensorProduct
open NumberField

set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Work.CFTLib

/-- `rankP p B ≤ rankP p A` whenever there is a surjection of abelian groups `A →+ B`: tensoring
the surjection with `𝔽_p = ℤ ⧸ (p)` is right exact, and any additive map between `ZMod p`-modules
is `ZMod p`-linear. -/
theorem rankP_le_of_surjective {p : ℕ} [Fact p.Prime] {A B : Type} [AddCommGroup A]
    [AddCommGroup B] [Module.Finite (ZMod p) (ZMod p ⊗[ℤ] A)] (f : A →+ B)
    (hf : Function.Surjective f) :
    Work.CFT.ClassFormation.rankP p B ≤ Work.CFT.ClassFormation.rankP p A := by
  rw [Work.CFT.ClassFormation.rankP, Work.CFT.ClassFormation.rankP]
  set G := TensorProduct.map (LinearMap.id : ZMod p →ₗ[ℤ] ZMod p) f.toIntLinearMap with hGdef
  have hG : Function.Surjective G := by
    intro y
    induction y using TensorProduct.inductionOn with
    | tmul x b =>
        obtain ⟨a, rfl⟩ := hf b
        exact ⟨x ⊗ₜ[ℤ] a, by simp [hGdef]⟩
    | add y z hy hz =>
        obtain ⟨y', hy'⟩ := hy
        obtain ⟨z', hz'⟩ := hz
        exact ⟨y' + z', by simp [map_add, hy', hz']⟩
  exact LinearMap.finrank_le_finrank_of_surjective
    (f := AddMonoidHom.toZModLinearMap p G.toAddMonoidHom) hG

/-- The indicator `δ_{F,p}` of `Work.CFT.Kummer.deltaK` (a primitive `p`-th root of unity in
`Fˣ`) agrees with `CFTLib.delta F p` (a primitive `p`-th root of unity in `F`). -/
theorem deltaK_eq_delta (F : Type) [Field F] [NumberField F] (p : ℕ) [Fact p.Prime] :
    Work.CFT.Kummer.deltaK F p = CFTLib.delta F p := by
  classical
  rw [Work.CFT.Kummer.deltaK, CFTLib.delta]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨ζ, hζ⟩
    exact ⟨ζ, (IsPrimitiveRoot.coe_units_iff (k := p) (ζ := ζ)).mpr hζ⟩
  · rintro ⟨ζ, hζ⟩
    refine ⟨Units.mk0 ζ (hζ.ne_zero (Fact.out : Nat.Prime p).ne_zero), ?_⟩
    exact (IsPrimitiveRoot.coe_units_iff (k := p)
      (ζ := Units.mk0 ζ (hζ.ne_zero (Fact.out : Nat.Prime p).ne_zero))).mp
      (by rw [Units.val_mk0]; exact hζ)

/-- **The `p`-rank of `Ĥ⁰(Gal(K/F), 𝒪_Kˣ)` is at most `r₁ + r₂ − 1 + δ_p(F)`.**

`Ĥ⁰(G, 𝒪_Kˣ) = (𝒪_Kˣ)^G / N(𝒪_Kˣ)` is a quotient of `(𝒪_Kˣ)^G`, which by Galois descent is the
image of `(𝒪_Fˣ)ˣ`; hence its `p`-rank is at most the `p`-rank of `𝒪_Fˣ`, which by Dirichlet's unit
theorem is `(r₁ + r₂ − 1) + δ_p(F)`. -/
theorem rankP_h0_oUnits_le {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [FiniteDimensional F K] [IsGalois F K] (p : ℕ) [Fact p.Prime] :
    Work.CFT.ClassFormation.rankP p ↑(tateCohomology (Work.CFTLib.oUnitsRep F K) 0)
      ≤ (NumberField.InfinitePlace.nrRealPlaces F + NumberField.InfinitePlace.nrComplexPlaces F - 1)
        + CFTLib.delta F p := by
  classical
  -- `(𝒪_Kˣ)^G = 𝒪_Fˣ`, so `Ĥ⁰(G, 𝒪_Kˣ)` is a quotient of `𝒪_Fˣ`
  obtain ⟨fB, hfB⟩ := oUnits_invariants_surjective (F := F) (K := K)
  have hcomp : Function.Surjective
      ((QuotientAddGroup.mk' (Work.CFT.IdeleClassGroup.norms (Work.CFTLib.oUnitsRep F K))).comp
        fB) :=
    (QuotientAddGroup.mk'_surjective _).comp hfB
  haveI : Module.Finite ℤ (Additive (𝓞 F)ˣ) :=
    Work.CFT.Kummer.module_finite_of_group_fg (R := ℤ) (G := (𝓞 F)ˣ)
  haveI hfin : Module.Finite (ZMod p) (ZMod p ⊗[ℤ] Additive (𝓞 F)ˣ) :=
    Module.Finite.base_change (R := ℤ) (A := ZMod p) (M := Additive (𝓞 F)ˣ)
  have hmono : Work.CFT.ClassFormation.rankP p
        (Work.CFT.IdeleClassGroup.H0Quotient (Work.CFTLib.oUnitsRep F K))
      ≤ Work.CFT.ClassFormation.rankP p (Additive (𝓞 F)ˣ) :=
    rankP_le_of_surjective _ hcomp
  -- `Ĥ⁰` is the invariants modulo the norms
  obtain ⟨e⟩ := Work.CFT.IdeleClassGroup.tateCohomology_zero_iso (Work.CFTLib.oUnitsRep F K)
  have heq : Work.CFT.ClassFormation.rankP p ↑(tateCohomology (Work.CFTLib.oUnitsRep F K) 0)
      = Work.CFT.ClassFormation.rankP p
          (Work.CFT.IdeleClassGroup.H0Quotient (Work.CFTLib.oUnitsRep F K)) :=
    Work.CFT.ClassFormation.rankP_eq_of_addEquiv p e
  -- Dirichlet's unit theorem for the base field
  have hdir : Work.CFT.ClassFormation.rankP p (Additive (𝓞 F)ˣ)
      ≤ NumberField.Units.rank F + Work.CFT.Kummer.deltaK F p := by
    rw [rankP_eq_finrank_unitsModPow F p,
      Work.CFT.Kummer.finrank_unitsModPow F p (Fact.out : Nat.Prime p)]
  have hrank : NumberField.Units.rank F =
      NumberField.InfinitePlace.nrRealPlaces F +
        NumberField.InfinitePlace.nrComplexPlaces F - 1 := by
    rw [NumberField.Units.rank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces]
  rw [heq]
  have h := le_trans hmono hdir
  rw [hrank, deltaK_eq_delta F p] at h
  exact h

end Work.CFTLib
