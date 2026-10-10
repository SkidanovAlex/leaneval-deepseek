import Mathlib
import Submission.Work.FFResidual.CharP.Order
import Submission.Work.ClassA.Model
import Submission.Work.PointlessTwist.Constants.nonempty_constantTateData
import Submission.Work.SilvermanReduction.Marker

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.FFResidual.CharP

noncomputable section

open Polynomial WeierstrassCurve WeierstrassCurve.Affine
open IsLocalRing (ResidueField residue)
open scoped WithZero

/-- **`j ≠ 1728` from the characteristic-free form `c₄ ^ 3 ≠ 1728 * Δ`.**  For an elliptic
Weierstrass model, `j = 1728` is equivalent to `c₄ ^ 3 = 1728 * Δ` once `Δ ≠ 0` (since
`j = c₄ ^ 3 / Δ`); this is the form in which the `j ≠ 1728` hypothesis is stable under base
change. -/
private theorem tate_j_ne_1728_of_c4_cube_ne {K : Type} [Field K] (W : WeierstrassCurve K)
    [W.IsElliptic] (hΔ : W.Δ ≠ 0) (h : W.c₄ ^ 3 ≠ 1728 * W.Δ) : W.j ≠ 1728 := by
  intro hj
  refine h ?_
  have h2 := congrArg (fun t => W.Δ * t) hj
  rw [WeierstrassCurve.j_eq] at h2
  rw [← mul_assoc, mul_inv_cancel₀ hΔ, one_mul, mul_comm W.Δ 1728] at h2
  exact h2

/-- **The place obstruction at the Artin–Schreier place** (characteristic `5`).  With the constant
Tate model `E(c)` over `𝔽` base changed to `𝕜`, the Artin–Schreier cyclic quintic extension
`AsTop = 𝕜(s)`, `s ^ 5 - s = π⁻¹`, of the place, and the local model `R[w] ⊆ AsTop` (`w = s⁻¹`,
a discrete valuation ring with fraction field `AsTop`, at which `E(c)` has good reduction and on
whose residue field the generator `s ↦ s + 1` acts trivially), the twist of `E(c)` by the class of
`(0,0)` **has no rational point**: there is a `ConstantTateData 𝔽 𝕜 c` whose twist by the
Artin–Schreier extension satisfies the place obstruction `HasReductionPlace`.

This is the characteristic-`5` analogue of `Kummer.exists_hasReductionPlace_kummerOrder`, proved by
`Work.ClassA.hasReductionPlace_of_model` at the Artin–Schreier order together with the non-vanishing
reduction of the marker `(0,0)`. -/
theorem exists_hasReductionPlace_asOrder {𝔽 : Type} [Field 𝔽] [DecidableEq 𝔽] {𝕜 : Type}
    [Field 𝕜] [DecidableEq 𝕜] [Algebra 𝔽 𝕜] (P : Work.FFResidual.FunctionFieldPlace 𝔽 𝕜)
    [CharP 𝕜 5]
    [IsDomain (Work.FFResidual.FunctionFieldPlace.AsOrder P)]
    [IsDiscreteValuationRing (Work.FFResidual.FunctionFieldPlace.AsOrder P)]
    [IsFractionRing (Work.FFResidual.FunctionFieldPlace.AsOrder P) P.AsTop]
    [DecidableEq (IsLocalRing.ResidueField (Work.FFResidual.FunctionFieldPlace.AsOrder P))]
    (c : 𝔽)
    (hΔ : (Work.TorsorExistence.Tate.tateCurve c).Δ ≠ 0)
    (hj : (Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3
      ≠ 1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ)
    [WeierstrassCurve.HasGoodReduction (Work.FFResidual.FunctionFieldPlace.AsOrder P)
      (((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).baseChange P.AsTop)]
    (hpres : Work.ClassA.ModelPreserves (Work.FFResidual.FunctionFieldPlace.AsOrder P) ⇑(P.asEquiv))
    (hres : Work.ClassA.ModelResidueTrivial (Work.FFResidual.FunctionFieldPlace.AsOrder P) ⇑(P.asEquiv)) :
    ∃ d : Work.PointlessTwist.ConstantTateData 𝔽 𝕜 c,
      Work.PointlessTwist.HasReductionPlace
        (Work.PointlessTwist.twistOf d.C₅ (P.asCyclicExtension)) := by
  classical
  -- ### the side conditions on the Tate parameter
  have hEll : (Work.TorsorExistence.Tate.tateCurve c).IsElliptic := by
    rw [WeierstrassCurve.isElliptic_iff]
    exact isUnit_iff_ne_zero.mpr hΔ
  haveI : (Work.TorsorExistence.Tate.tateCurve c).IsElliptic := hEll
  have hc0 : c ≠ 0 := fun hc =>
    hΔ (by rw [Work.TorsorExistence.Tate.tateCurve_Δ, hc]; ring)
  have hns00 : ((Work.TorsorExistence.Tate.tateCurve c)⁄𝔽).Nonsingular 0 0 :=
    (equation_iff_nonsingular (W := Work.TorsorExistence.Tate.tateCurve c)).mp
      (Work.TorsorExistence.Tate.tateCurve_equation_zero c)
  have hΔ𝕜 : ((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).Δ ≠ 0 := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_Δ]
    exact fun h => hΔ ((algebraMap 𝔽 𝕜).injective (by simpa using h))
  have hc4𝕜 : ((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).c₄ ^ 3
      ≠ 1728 * ((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).Δ := by
    rw [WeierstrassCurve.baseChange, WeierstrassCurve.map_c₄, WeierstrassCurve.map_Δ]
    refine fun h => hj ?_
    have h2 : (algebraMap 𝔽 𝕜) ((Work.TorsorExistence.Tate.tateCurve c).c₄ ^ 3)
        = (algebraMap 𝔽 𝕜) (1728 * (Work.TorsorExistence.Tate.tateCurve c).Δ) := by
      rw [map_pow, map_mul, map_ofNat]
      exact h
    exact (algebraMap 𝔽 𝕜).injective h2
  have hEll𝕜 : ((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).IsElliptic := by
    rw [WeierstrassCurve.baseChange]
    infer_instance
  haveI : ((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).IsElliptic := hEll𝕜
  have hj𝕜 : ((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).j ≠ 1728 :=
    tate_j_ne_1728_of_c4_cube_ne _ hΔ𝕜 hc4𝕜
  -- ### the marked point of the constant Tate model, as an explicit affine point
  have h₁ : Nonsingular (((Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜).baseChange 𝕜)
      ((Algebra.ofId 𝔽 𝕜) 0) ((Algebra.ofId 𝔽 𝕜) 0) :=
    (baseChange_nonsingular (Work.TorsorExistence.Tate.tateCurve c)
      (Algebra.ofId 𝔽 𝕜).injective (0 : 𝔽) (0 : 𝔽)).mpr hns00
  have hPmap : (Point.some ((Algebra.ofId 𝔽 𝕜) 0) ((Algebra.ofId 𝔽 𝕜) 0) h₁ :
      Point ((Work.TorsorExistence.Tate.tateCurve c)⁄𝕜))
      = Point.map (W' := Work.TorsorExistence.Tate.tateCurve c) (Algebra.ofId 𝔽 𝕜)
          (Point.some 0 0 hns00) := rfl
  have h5T : (5 : ℕ) • (Point.some 0 0 hns00 :
      Point ((Work.TorsorExistence.Tate.tateCurve c)⁄𝔽)) = 0 :=
    Work.TorsorExistence.Tate.tate_five_smul c hc0 hns00
  have h5marker : (5 : ℕ) • (Point.some ((Algebra.ofId 𝔽 𝕜) 0) ((Algebra.ofId 𝔽 𝕜) 0) h₁ :
      Point ((Work.TorsorExistence.Tate.tateCurve c)⁄𝕜)) = 0 := by
    rw [hPmap]
    have hh := map_nsmul (Point.map (W' := Work.TorsorExistence.Tate.tateCurve c)
      (Algebra.ofId 𝔽 𝕜)) 5 (Point.some 0 0 hns00 :
        Point ((Work.TorsorExistence.Tate.tateCurve c)⁄𝔽))
    rw [← hh, h5T, Point.map_zero]
  -- ### the constant Tate data, marked by the base change of `(0,0)`
  let d : Work.PointlessTwist.ConstantTateData 𝔽 𝕜 c := {
    C₅ := {
      E := (Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜
      isElliptic := hEll𝕜
      j_ne := hj𝕜
      P := Point.some ((Algebra.ofId 𝔽 𝕜) 0) ((Algebra.ofId 𝔽 𝕜) 0) h₁
      P_ne_zero := Point.some_ne_zero h₁
      five_smul := h5marker
      order_aut := Work.PointlessTwist.Constants.hasGoodAut_of_j_ne _ hj𝕜 }
    E_eq := rfl
    P := Point.some 0 0 hns00
    five_smul := h5T
    P_ne_zero := Point.some_ne_zero hns00
    P_eq := rfl }
  refine ⟨d, ?_⟩
  -- ### the Artin–Schreier extension, as a structure literal with underlying field `P.AsTop`
  haveI hsplit : IsSplittingField 𝕜 P.AsTop P.asPoly := P.isSplittingField_asPoly
  haveI hfd : FiniteDimensional 𝕜 P.AsTop := P.finiteDimensional_asTop
  haveI hgal : IsGalois 𝕜 P.AsTop := P.isGalois_asTop
  haveI hft : Fintype (P.AsTop ≃ₐ[𝕜] P.AsTop) := AlgEquiv.fintype 𝕜 P.AsTop
  have htop : Subgroup.zpowers P.asEquiv = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ ?_
    rw [Nat.card_zpowers, P.orderOf_asEquiv,
      IsGalois.card_aut_eq_finrank 𝕜 P.AsTop, P.finrank_asTop]
  let L : Work.TorsorExistence.CyclicExtension 𝕜 5 :=
    { L := P.AsTop
      field := inferInstance
      algebra := inferInstance
      finiteDimensional := inferInstance
      isGalois := inferInstance
      finrank_eq := P.finrank_asTop
      gen := P.asEquiv
      gen_generator := fun g => by
        have hmem : g ∈ Submonoid.powers P.asEquiv :=
          (isOfFinOrder_of_finite P.asEquiv).mem_powers_iff_mem_zpowers.mpr
            (htop ▸ Subgroup.mem_top g)
        obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff g _).mp hmem
        exact ⟨k, hk.symm⟩
      orderOf_gen := P.orderOf_asEquiv }
  -- ### the twist, with the same data as `twistOf d.C₅ (P.asCyclicExtension)`
  let D : Work.PointlessTwist.QuinticTwist 𝕜 :=
    { E := (Work.TorsorExistence.Tate.tateCurve c).baseChange 𝕜
      isElliptic := hEll𝕜
      j_ne := hj𝕜
      P := Point.some ((Algebra.ofId 𝔽 𝕜) 0) ((Algebra.ofId 𝔽 𝕜) 0) h₁
      P_ne_zero := Point.some_ne_zero h₁
      five_smul := h5marker
      order_aut := Work.PointlessTwist.Constants.hasGoodAut_of_j_ne _ hj𝕜
      ext := L
      decEq_ext := Classical.decEq P.AsTop }
  change Work.PointlessTwist.HasReductionPlace D
  refine Work.ClassA.hasReductionPlace_of_model D
    (Work.FFResidual.FunctionFieldPlace.AsOrder P) hpres hres ?_
  -- ### the marker reduces non-trivially, because it is the base change of `(0,0)`
  have hs : D.PL = Point.map (W' := D.E) (Algebra.ofId 𝕜 P.AsTop)
      (Point.some ((Algebra.ofId 𝔽 𝕜) 0) ((Algebra.ofId 𝔽 𝕜) 0) h₁) := rfl
  rw [hs, Point.map_some]
  rw [Work.SilvermanReduction.redPoint_some_mk
    (R := Work.FFResidual.FunctionFieldPlace.AsOrder P) _ (r := 0) (s := 0)
    (by simp) (by simp)]
  exact Point.some_ne_zero _

end

end Work.FFResidual.CharP
