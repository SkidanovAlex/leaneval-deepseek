import Mathlib
import Submission.Work.SpecLin.Alt.chartMap
import Submission.Work.SpecLin.Alt.chartTensorMap_isFractionRing
import Submission.Work.SpecLin.Content.exists_smul_notMem_maximalIdeal_map
import Submission.Work.SpecLin.Core.linEquiv_of_sections_of_chart

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Normalising a rational function on the generic fibre of a relative chart

Let `C` be a smooth proper geometrically irreducible curve over a field `K`, let `R` be a
`K`-valuation ring with fraction field `F = Frac R`, and let `W ⊆ C` be a nonempty affine open
chart with coordinate ring `A = Γ(C,W)`.  Write `B = A ⊗_K R` for the coordinate ring of the
relative chart and `P = chartFibrePrime R W = 𝔪_R·B` for the prime of the generic point of the
special fibre; let `φ = chartTensorMap R W : B →+* K(C_F)` be the chart-dictionary map, so that
`K(C_F) = Frac B` (`chartTensorMap_isFractionRing`).

The lemma proved here says that every nonzero `h ∈ K(C_F)` can be multiplied by a nonzero
*constant* of `F` (in particular `div h` is unchanged) so that the result is a quotient
`φ a / φ b` of two elements of the relative chart which are both **units modulo the special
fibre** `P`, i.e. `a, b ∉ P`.

This is step (C0) of the chart-dictionary reduction (`Alt/NOTES_chartCore.md`): dividing
numerator and denominator by their `R`-content
(`Work.SpecLin.Core.exists_smul_notMem_chartFibrePrime`, itself a coordinate computation in a
`K`-basis of `A`) makes both of them nonzero in `B ⧸ P`, so that `h` becomes a unit of the
localisation `B_P` and has a well defined reduction to `Frac(B ⧸ P) = K(C_κ)`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry

namespace Work.SpecLin.Alt

open Work.CurveBasics in
theorem exists_normalized_chartTensorMap {K : Type _} [Field K] {C : Work.CurveBasics.Curve K}
    (R : Type _) [CommRing R] [IsDomain R] [ValuationRing R] [Algebra K R]
    (W : C.left.Opens) (hW : AlgebraicGeometry.IsAffineOpen W) [Nonempty W]
    (h : (C.baseChange (FractionRing R)).functionField) (hh : h ≠ 0) :
    ∃ h' : (C.baseChange (FractionRing R)).functionField,
      ∃ a b : Work.SpecLin.Core.chartTensor R W,
        h' ≠ 0 ∧ a ∉ Work.SpecLin.Core.chartFibrePrime R W ∧
        b ∉ Work.SpecLin.Core.chartFibrePrime R W ∧
        (C.baseChange (FractionRing R)).div h' = (C.baseChange (FractionRing R)).div h ∧
        h' * Work.SpecLin.Alt.chartTensorMap R W hW b
          = Work.SpecLin.Alt.chartTensorMap R W hW a := by
  -- ## Abbreviations
  let B := Work.SpecLin.Core.chartTensor (K:=K) (C:=C) R W
  let L := (C.baseChange (FractionRing R)).functionField
  let F := FractionRing R
  let φ := Work.SpecLin.Alt.chartTensorMap (K:=K) (C:=C) R W hW
  letI : Algebra B L := φ.toAlgebra
  haveI hFR : IsFractionRing B L :=
    Work.SpecLin.Alt.chartTensorMap_isFractionRing (K:=K) (C:=C) R W hW
  haveI hDom : IsDomain B :=
    Work.SpecLin.Core.isDomain_chartTensor (K:=K) (C:=C) R W hW
  have hinj : Function.Injective φ := by
    intro a b hab
    exact IsFractionRing.injective B L hab
  -- ## A fraction `p / q` for `h` in the relative chart `B`
  obtain ⟨p, q, hq_mem, hpq⟩ := IsFractionRing.div_surjective B h
  have hq_ne : q ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp hq_mem
  have hφq_ne : algebraMap B L q ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hq_mem
  have hpq' : h * algebraMap B L q = algebraMap B L p := (eq_div_iff hφq_ne).mp hpq.symm
  -- ## Content normalisation of numerator and denominator
  letI : Algebra R B := Algebra.TensorProduct.rightAlgebra (R:=K) (A:=Γ(C.left, W)) (B:=R)
  obtain ⟨c₁, p', hp_eq, hp'_notMem⟩ :=
    Work.SpecLin.Core.exists_smul_notMem_chartFibrePrime (K:=K) (C:=C) R W hW p
  obtain ⟨c₂, q', hq_eq, hq'_notMem⟩ :=
    Work.SpecLin.Core.exists_smul_notMem_chartFibrePrime (K:=K) (C:=C) R W hW q
  have hc₂ : c₂ ≠ 0 := fun h0 => hq_ne (by rw [hq_eq, h0, zero_smul])
  have hpq'' : h * φ q = φ p := hpq'
  have hp_ne : p ≠ 0 := by
    intro h0
    have h1 : φ p = 0 := by rw [h0, map_zero]
    rw [← hpq''] at h1
    exact (mul_ne_zero hh hφq_ne) h1
  have hc₁ : c₁ ≠ 0 := fun h0 => hp_ne (by rw [hp_eq, h0, zero_smul])
  -- ## The values of `φ` on the scalars of `R`
  have hψ : ∀ c : R, φ (algebraMap R B c) = algebraMap F ↑L (algebraMap R F c) := by
    intro c
    rw [Algebra.TensorProduct.right_algebraMap_apply c]
    exact Work.SpecLin.Alt.chartTensorMap_one_tmul (K:=K) (C:=C) R W hW c
  -- ## The relation `h * (ψ c₂ * φ q') = ψ c₁ * φ p'`
  have hrel : h * (algebraMap F ↑L (algebraMap R F c₂) * φ q')
      = algebraMap F ↑L (algebraMap R F c₁) * φ p' := by
    have h1 : φ q = algebraMap F ↑L (algebraMap R F c₂) * φ q' := by
      rw [hq_eq, Algebra.smul_def, map_mul, hψ c₂]
    have h2 : φ p = algebraMap F ↑L (algebraMap R F c₁) * φ p' := by
      rw [hp_eq, Algebra.smul_def, map_mul, hψ c₁]
    rw [← h1, ← h2, hpq'']
  -- ## Nonvanishing
  have hmapF : Function.Injective (algebraMap F ↑L) := RingHom.injective _
  have hmapR : Function.Injective (algebraMap R F) := IsFractionRing.injective R F
  have hA₂ : algebraMap R F c₂ ≠ 0 := fun h0 => hc₂ (hmapR (by simpa using h0))
  have hA₁ : algebraMap R F c₁ ≠ 0 := fun h0 => hc₁ (hmapR (by simpa using h0))
  have hUA₁ : algebraMap F ↑L (algebraMap R F c₁) ≠ 0 := by simpa using hmapF.ne hA₁
  have hq'_ne : q' ≠ 0 := fun h0 => hq'_notMem (by rw [h0]; exact
    (Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W).zero_mem)
  have hp'_ne : p' ≠ 0 := fun h0 => hp'_notMem (by rw [h0]; exact
    (Work.SpecLin.Core.chartFibrePrime (K:=K) (C:=C) R W).zero_mem)
  have hφq' : φ q' ≠ 0 := fun h0 => hq'_ne (hinj (by rw [h0, map_zero]))
  have hφp' : φ p' ≠ 0 := fun h0 => hp'_ne (hinj (by rw [h0, map_zero]))
  -- ## `φ p' / φ q'` differs from `h` by the constant `ψ c₂ / ψ c₁` of `F`
  have hkey : φ p' / φ q'
      = h * (algebraMap F ↑L (algebraMap R F c₂) / algebraMap F ↑L (algebraMap R F c₁)) := by
    rw [← mul_div_assoc, div_eq_div_iff hφq' hUA₁]
    rw [mul_comm (φ p') (algebraMap F ↑L (algebraMap R F c₁)), mul_assoc h _ (φ q')]
    exact hrel.symm
  have hconst : algebraMap F ↑L (algebraMap R F c₂) / algebraMap F ↑L (algebraMap R F c₁)
      = algebraMap F ↑L (algebraMap R F c₂ * (algebraMap R F c₁)⁻¹) := by
    rw [div_eq_mul_inv, ← map_inv₀ (algebraMap F ↑L) (algebraMap R F c₁), ← map_mul]
  have hu : algebraMap F ↑L (algebraMap R F c₂ * (algebraMap R F c₁)⁻¹) ≠ 0 := fun h0 =>
    (mul_ne_zero hA₂ (inv_ne_zero hA₁)) (hmapF (by rw [h0, map_zero]))
  -- ## Multiplication by a nonzero constant does not change the divisor
  have hdiv : (C.baseChange F).div
        (h * algebraMap F ↑L (algebraMap R F c₂ * (algebraMap R F c₁)⁻¹))
      = (C.baseChange F).div h := by
    rw [Work.CurveBasics.Curve.div_mul (C.baseChange F) hh hu,
      Work.CurveBasics.Order.div_algebraMap_eq_zero (C.baseChange F)
        (algebraMap R F c₂ * (algebraMap R F c₁)⁻¹),
      add_zero]
  refine ⟨φ p' / φ q', p', q', div_ne_zero hφp' hφq', hp'_notMem, hq'_notMem, ?_, ?_⟩
  · rw [hkey, hconst]; exact hdiv
  · exact div_mul_cancel₀ (φ p') hφq'

end Work.SpecLin.Alt
