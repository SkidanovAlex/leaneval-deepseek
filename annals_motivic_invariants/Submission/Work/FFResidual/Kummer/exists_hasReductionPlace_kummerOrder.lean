/-
Copyright (c) 2026 The annals_motivic_invariants team. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: Work.FFResidual
-/
import Submission.Work.FFResidual.Kummer.Order
import Submission.Work.ClassA.Model
import Submission.Work.PointlessTwist.Constants.nonempty_constantTateData
import Submission.Work.SilvermanReduction.Marker

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The place obstruction at the Kummer place

Let `P : FunctionFieldPlace 𝔽 𝕜` be a place of a function field over its constants (with
uniformizer `π`), `Top P = 𝕜(s)` the Kummer extension `s ^ 5 = π` of
`Submission/Work/FFResidual/Kummer/Basic`, and `KummerOrder P = R[s]` its Eisenstein order
(`Submission/Work/FFResidual/Kummer/Order`).

This file proves the *place obstruction* at the Kummer place: with `c ∈ 𝔽` a good Tate parameter
(`Δ ≠ 0`, `c₄ ^ 3 ≠ 1728 Δ`), the constant Tate model `E(c)` base changed to `𝕜`, marked by the
base change of its `5`-torsion point `(0,0)`, has a twist by the Kummer extension whose reduction
map out of `E(𝕜(s))` is additive, `Gal(𝕜(s)/𝕜)`-invariant and does not kill the marker
(`Work.PointlessTwist.HasReductionPlace`).  The proof is the paper's route (ii):
`Work.ClassA.hasReductionPlace_of_model` applied at the Eisenstein order, with the two model
properties `ModelPreserves`/`ModelResidueTrivial` (`hpres`, `hres`) and the non-vanishing
reduction of the marker `(0,0)` (`Work.SilvermanReduction.redPoint_some_zero_zero_ne_zero`).

## Implementation notes

Two points of the construction are worth recording.

* The `ConstantTateData` produced is the constant Tate model `E(c)` base changed to `𝕜` marked by
  the *base change of `(0,0)` itself* (`Point.some 0 0 h` at `𝔽`-level), so its marker is an
  affine point with the explicit coordinates `(algebraMap 𝔽 𝕜) 0` over `𝕜` and `0` over the local
  model.  The good-reduction datum (`HasGoodAut`, Silverman A.1.2) is transported from `𝔽` to `𝕜`
  exactly as in `Work.PointlessTwist.Constants.nonempty_constantTateData`.
* The Kummer extension and the twist are written as *structure literals* whose underlying field is
  `P.Top` definitionally.  This is what makes the place data of the local model
  (`Algebra R D.ext.L`, `IsFractionRing R D.ext.L`, `HasGoodReduction R ...`) reducible to the data
  at `P.Top` for the typeclass system, so that `Work.ClassA.hasReductionPlace_of_model` applies
  verbatim.

## Main results

* `Work.FFResidual.Kummer.exists_hasReductionPlace_kummerOrder` — the place obstruction at the
  Kummer place.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.FFResidual

noncomputable section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (ResidueField residue)
open scoped WithZero

namespace FunctionFieldPlace

variable {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] {𝕜 : Type} [Field 𝕜] [DecidableEq 𝕜] [Algebra 𝔽 𝕜]

/-- **`j ≠ 1728` from the characteristic-free form `c₄ ^ 3 ≠ 1728 * Δ`.**  For an elliptic
Weierstrass model, `j = 1728` is equivalent to `c₄ ^ 3 = 1728 * Δ` once `Δ ≠ 0` (since
`j = c₄ ^ 3 / Δ`); this is the form in which the `j ≠ 1728` hypothesis of the function-field
classes is stable under base change. -/
theorem tate_j_ne_1728_of_c4_cube_ne {K : Type} [Field K] (W : WeierstrassCurve K) [W.IsElliptic]
    (hΔ : W.Δ ≠ 0) (h : W.c₄ ^ 3 ≠ 1728 * W.Δ) : W.j ≠ 1728 := by
  intro hj
  refine h ?_
  have h2 := congrArg (fun t => W.Δ * t) hj
  rw [WeierstrassCurve.j_eq] at h2
  rw [← mul_assoc, mul_inv_cancel₀ hΔ, one_mul, mul_comm W.Δ 1728] at h2
  exact h2

end FunctionFieldPlace

namespace Kummer

open FunctionFieldPlace

/-- **The place obstruction at the Kummer place.**  Let `P` be a place of the function field `𝕜`
over the constants `𝔽` with uniformizer `π`, and let `c ∈ 𝔽` be a good Tate parameter (its
discriminant is nonzero, so `c` and `c² - 11c - 1` are units at the place).  Then, with the constant
Tate model `E(c)` base changed to `𝕜`, the cyclic quintic Kummer extension `𝕜(s)`, `s ^ 5 = π` of
the place, and the local model `R[s] ⊆ 𝕜(s)` (the Eisenstein order `KummerOrder P`, a discrete
valuation ring with fraction field the top field, at which `E(c)` has good reduction, and on whose
residue field the generator `s ↦ ζ s` of `Gal(𝕜(s)/𝕜)` acts trivially), the twist of `E(c)` by the
class of `(0,0)` **has no rational point**: there is a `ConstantTateData 𝔽 𝕜 c` whose twist by the
Kummer extension satisfies the place obstruction `HasReductionPlace` (an additive, Galois-invariant
map out of `E(L)` not killing the marker).

The proof is the paper's route (ii): `Work.ClassA.hasReductionPlace_of_model` applied at the
Eisenstein order, with the two model properties and the non-vanishing reduction of the marker
`(0,0)` (`Work.SilvermanReduction.redPoint_some_zero_zero_ne_zero`). -/
theorem exists_hasReductionPlace_kummerOrder {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] {𝕜 : Type}
    [Field 𝕜] [DecidableEq 𝕜] [Algebra 𝔽 𝕜] (P : Work.FFResidual.FunctionFieldPlace 𝔽 𝕜)
    [IsDomain (Work.FFResidual.FunctionFieldPlace.KummerOrder P)]
    [IsDiscreteValuationRing (Work.FFResidual.FunctionFieldPlace.KummerOrder P)]
    [IsFractionRing (Work.FFResidual.FunctionFieldPlace.KummerOrder P) P.Top]
    [DecidableEq (IsLocalRing.ResidueField (Work.FFResidual.FunctionFieldPlace.KummerOrder P))]
    (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ)
    [WeierstrassCurve.HasGoodReduction (Work.FFResidual.FunctionFieldPlace.KummerOrder P)
      (((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).baseChange P.Top)]
    (ζ : 𝔽) (hζ : IsPrimitiveRoot ζ 5)
    (hpres : Work.ClassA.ModelPreserves (Work.FFResidual.FunctionFieldPlace.KummerOrder P)
      ⇑(P.kummerEquiv ζ hζ))
    (hres : Work.ClassA.ModelResidueTrivial (Work.FFResidual.FunctionFieldPlace.KummerOrder P)
      ⇑(P.kummerEquiv ζ hζ)) :
    ∃ d : Work.PointlessTwist.ConstantTateData 𝔽 𝕜 c,
      Work.PointlessTwist.HasReductionPlace
        (Work.PointlessTwist.twistOf d.C₅ (P.kummerCyclicExtension ζ hζ)) := by
  classical
  -- ### the side conditions on the Tate parameter
  have hEll : (TorsorExistence.Tate.tateCurve c).IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff]
    exact isUnit_iff_ne_zero.mpr hΔ
  haveI : (TorsorExistence.Tate.tateCurve c).IsElliptic := hEll
  have hc0 : c ≠ 0 := fun hc =>
    hΔ (by rw [TorsorExistence.Tate.tateCurve_Δ, hc]; ring)
  have hns00 : ((TorsorExistence.Tate.tateCurve c)⁄𝔽).Nonsingular 0 0 :=
    (equation_iff_nonsingular (W := TorsorExistence.Tate.tateCurve c)).mp
      (TorsorExistence.Tate.tateCurve_equation_zero c)
  have hΔ𝕜 : ((TorsorExistence.Tate.tateCurve c).baseChange 𝕜).Δ ≠ 0 := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    exact fun h => hΔ ((algebraMap 𝔽 𝕜).injective (by simpa using h))
  have hc4𝕜 : ((TorsorExistence.Tate.tateCurve c).baseChange 𝕜).c₄ ^ 3
      ≠ 1728 * ((TorsorExistence.Tate.tateCurve c).baseChange 𝕜).Δ := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄, WeierstrassCurve.map_Δ]
    refine fun h => hj ?_
    have h2 : (algebraMap 𝔽 𝕜) ((TorsorExistence.Tate.tateCurve c).c₄ ^ 3)
        = (algebraMap 𝔽 𝕜) (1728 * (TorsorExistence.Tate.tateCurve c).Δ) := by
      rw [map_pow, map_mul, map_ofNat]
      exact h
    exact (algebraMap 𝔽 𝕜).injective h2
  have hEll𝕜 : ((TorsorExistence.Tate.tateCurve c).baseChange 𝕜).IsElliptic := by
    rw [WeierstrassCurve.baseChange]
    infer_instance
  haveI : ((TorsorExistence.Tate.tateCurve c).baseChange 𝕜).IsElliptic := hEll𝕜
  have hj𝕜 : ((TorsorExistence.Tate.tateCurve c).baseChange 𝕜).j ≠ 1728 :=
    FunctionFieldPlace.tate_j_ne_1728_of_c4_cube_ne _ hΔ𝕜 hc4𝕜
  -- ### the marked point of the constant Tate model, as an explicit affine point
  -- The nonsingularity datum is recorded at the *doubly* base changed curve, because the marker
  -- of the twist is a point of `E(𝕜) ` base changed to the top field.
  have h₁ : Nonsingular (((TorsorExistence.Tate.tateCurve c).baseChange 𝕜).baseChange 𝕜)
      ((Algebra.ofId 𝔽 𝕜) 0) ((Algebra.ofId 𝔽 𝕜) 0) :=
    (baseChange_nonsingular (TorsorExistence.Tate.tateCurve c)
      (Algebra.ofId 𝔽 𝕜).injective (0 : 𝔽) (0 : 𝔽)).mpr hns00
  have hPmap : (Point.some ((Algebra.ofId 𝔽 𝕜) 0) ((Algebra.ofId 𝔽 𝕜) 0) h₁ :
      Point ((TorsorExistence.Tate.tateCurve c)⁄𝕜))
      = Point.map (W' := TorsorExistence.Tate.tateCurve c) (Algebra.ofId 𝔽 𝕜)
          (Point.some 0 0 hns00) := rfl
  have h5T : (5 : ℕ) • (Point.some 0 0 hns00 :
      Point ((TorsorExistence.Tate.tateCurve c)⁄𝔽)) = 0 :=
    TorsorExistence.Tate.tate_five_smul c hc0 hns00
  have h5marker : (5 : ℕ) • (Point.some ((Algebra.ofId 𝔽 𝕜) 0) ((Algebra.ofId 𝔽 𝕜) 0) h₁ :
      Point ((TorsorExistence.Tate.tateCurve c)⁄𝕜)) = 0 := by
    rw [hPmap]
    have hh := map_nsmul (Point.map (W' := TorsorExistence.Tate.tateCurve c)
      (Algebra.ofId 𝔽 𝕜)) 5 (Point.some 0 0 hns00 :
        Point ((TorsorExistence.Tate.tateCurve c)⁄𝔽))
    rw [← hh, h5T, Point.map_zero]
  -- ### the constant Tate data, marked by the base change of `(0,0)`
  let d : PointlessTwist.ConstantTateData 𝔽 𝕜 c := {
    C₅ := {
      E := (TorsorExistence.Tate.tateCurve c).baseChange 𝕜
      isElliptic := hEll𝕜
      j_ne := hj𝕜
      P := Point.some ((Algebra.ofId 𝔽 𝕜) 0) ((Algebra.ofId 𝔽 𝕜) 0) h₁
      P_ne_zero := Point.some_ne_zero h₁
      five_smul := h5marker
      order_aut := PointlessTwist.Constants.hasGoodAut_of_j_ne _ hj𝕜 }
    E_eq := rfl
    P := Point.some 0 0 hns00
    five_smul := h5T
    P_ne_zero := Point.some_ne_zero hns00
    P_eq := rfl }
  refine ⟨d, ?_⟩
  -- ### the Kummer extension, as a structure literal with underlying field `P.Top`
  haveI hsplit : IsSplittingField 𝕜 P.Top P.kummerPoly := P.isSplittingField_kummerPoly ζ hζ
  haveI hfd : FiniteDimensional 𝕜 P.Top :=
    IsSplittingField.finiteDimensional (L := P.Top) P.kummerPoly
  haveI hgal : IsGalois 𝕜 P.Top := P.isGalois_Top ζ hζ
  haveI hft : Fintype (P.Top ≃ₐ[𝕜] P.Top) := AlgEquiv.fintype 𝕜 P.Top
  have htop : Subgroup.zpowers (P.kummerEquiv ζ hζ) = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [Nat.card_zpowers, P.orderOf_kummerEquiv ζ hζ,
      IsGalois.card_aut_eq_finrank 𝕜 P.Top, P.finrank_Top ζ hζ]
  let L : TorsorExistence.CyclicExtension 𝕜 5 :=
    { L := P.Top
      field := inferInstance
      algebra := inferInstance
      finiteDimensional := IsSplittingField.finiteDimensional (L := P.Top) P.kummerPoly
      isGalois := P.isGalois_Top ζ hζ
      finrank_eq := P.finrank_Top ζ hζ
      gen := P.kummerEquiv ζ hζ
      gen_generator := fun g => by
        have hmem : g ∈ Submonoid.powers (P.kummerEquiv ζ hζ) :=
          (isOfFinOrder_of_finite (P.kummerEquiv ζ hζ)).mem_powers_iff_mem_zpowers.mpr
            (htop ▸ Subgroup.mem_top g)
        obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff g _).mp hmem
        exact ⟨k, hk.symm⟩
      orderOf_gen := P.orderOf_kummerEquiv ζ hζ }
  -- ### the twist, with the same data as `twistOf d.C₅ (P.kummerCyclicExtension ζ hζ)`
  let D : PointlessTwist.QuinticTwist 𝕜 :=
    { E := (TorsorExistence.Tate.tateCurve c).baseChange 𝕜
      isElliptic := hEll𝕜
      j_ne := hj𝕜
      P := Point.some ((Algebra.ofId 𝔽 𝕜) 0) ((Algebra.ofId 𝔽 𝕜) 0) h₁
      P_ne_zero := Point.some_ne_zero h₁
      five_smul := h5marker
      order_aut := PointlessTwist.Constants.hasGoodAut_of_j_ne _ hj𝕜
      ext := L
      decEq_ext := Classical.decEq P.Top }
  change PointlessTwist.HasReductionPlace D
  refine Work.ClassA.hasReductionPlace_of_model D (FunctionFieldPlace.KummerOrder P)
    hpres hres ?_
  -- ### the marker reduces non-trivially, because it is the base change of `(0,0)`
  have hs : D.PL = Point.map (W' := D.E) (Algebra.ofId 𝕜 P.Top)
      (Point.some ((Algebra.ofId 𝔽 𝕜) 0) ((Algebra.ofId 𝔽 𝕜) 0) h₁) := rfl
  rw [hs, Point.map_some]
  rw [Work.SilvermanReduction.redPoint_some_mk (R := FunctionFieldPlace.KummerOrder P)
    _ (r := 0) (s := 0) (by simp) (by simp)]
  exact Point.some_ne_zero _

end Kummer

end

end Work.FFResidual
