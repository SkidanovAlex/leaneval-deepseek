import Mathlib
import Submission.Work.WilkiesH.Defs
import Submission.Work.WilkiesH.Norm.finprod_finitePlace_algEquiv

/-!
# The absolute multiplicative height is invariant under inversion

For a real number `x` we prove `absMulHeight₁ x⁻¹ = absMulHeight₁ x`.

`NumberField.absMulHeight₁ x` is `(mulHeight₁ (gen ℚ x)) ^ (finrank ℚ ℚ⟮x⟯ : ℝ)⁻¹` when `x`
is algebraic (and `1` otherwise), where the height is taken inside the number field `ℚ⟮x⟯`.
The two fields `ℚ⟮x⟯` and `ℚ⟮x⁻¹⟯` are *the same subfield of `ℝ`* when `x ≠ 0`, so it suffices
to show that `Height.mulHeight₁` is invariant under `ℚ`-algebra isomorphisms of number fields
(`mulHeight₁_algEquiv`) and that inside a fixed field `mulHeight₁` is inversion invariant
(`Height.mulHeight₁_inv`).
-/

open scoped IntermediateField

set_option linter.style.haveILetI false

namespace Work.WilkiesH.Norm

open Height

/-- The archimedean part `∏_v (max (v x) 1) ^ (mult v)` of the multiplicative height of an
element of a number field is invariant under `ℚ`-algebra isomorphisms of number fields: an
algebra equivalence `e` induces the bijection `w ↦ w.comap e` between the infinite places of
the target and of the source, which preserves the multiplicity `v.mult` and the value. -/
theorem prod_infinitePlace_max_algEquiv {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] (e : K ≃ₐ[ℚ] L) (x : K) :
    (∏ v : NumberField.InfinitePlace L, max (v (e x)) 1 ^ v.mult)
      = ∏ v : NumberField.InfinitePlace K, max (v x) 1 ^ v.mult := by
  have hcomp2 : ((e : K →+* L).comp (e.symm : L →+* K)) = RingHom.id L := by
    ext y; simp
  have hcomp : ((e.symm : L →+* K).comp (e : K →+* L)) = RingHom.id K := by
    ext y; simp
  let Φ : NumberField.InfinitePlace L ≃ NumberField.InfinitePlace K :=
    { toFun := fun w => w.comap (e : K →+* L)
      invFun := fun v => v.comap (e.symm : L →+* K)
      left_inv := by
        intro w
        show (w.comap (e : K →+* L)).comap (e.symm : L →+* K) = w
        rw [← NumberField.InfinitePlace.comap_comp, hcomp2, NumberField.InfinitePlace.comap_id]
      right_inv := by
        intro v
        show (v.comap (e.symm : L →+* K)).comap (e : K →+* L) = v
        rw [← NumberField.InfinitePlace.comap_comp, hcomp, NumberField.InfinitePlace.comap_id] }
  exact Fintype.prod_equiv Φ _ _ (fun w => by
    have h : (w.comap (e : K →+* L)).IsReal ↔ w.IsReal :=
      NumberField.InfinitePlace.isReal_comap_iff (f := (e : K ≃+* L)) (w := w)
    have hmult : (Φ w).mult = w.mult := by
      show (w.comap (e : K →+* L)).mult = w.mult
      rw [NumberField.InfinitePlace.mult, NumberField.InfinitePlace.mult]
      by_cases hw : w.IsReal
      · have : (w.comap (e : K →+* L)).IsReal := h.mpr hw
        simp [hw, this]
      · have : ¬ (w.comap (e : K →+* L)).IsReal := fun hc => hw (h.mp hc)
        simp [hw, this]
    have hval : (Φ w) x = w (e x) := rfl
    rw [hval, hmult])

/-- The multiplicative height `Height.mulHeight₁` is invariant under `ℚ`-algebra isomorphisms
of number fields.  This is the well-definedness of the absolute (unnormalized) height: the
archimedean and the non-archimedean places correspond under the isomorphism, with the same
multiplicities and the same values on corresponding elements. -/
theorem mulHeight₁_algEquiv {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
    (e : K ≃ₐ[ℚ] L) (x : K) : Height.mulHeight₁ (e x) = Height.mulHeight₁ x := by
  rw [NumberField.mulHeight₁_eq, NumberField.mulHeight₁_eq,
    prod_infinitePlace_max_algEquiv e x, finprod_finitePlace_algEquiv e x]

/-- The absolute multiplicative height of `x` equals that of `x⁻¹`: the generator of `ℚ⟮x⟯` and
the generator of `ℚ⟮x⁻¹⟯` are both generators of the *same* number field, and inside a fixed
number field the height is inversion invariant (`Height.mulHeight₁_inv`). -/
theorem absMulHeight_inv (x : ℝ) : NumberField.absMulHeight₁ x⁻¹ = NumberField.absMulHeight₁ x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · simp
  by_cases hx : IsIntegral ℚ x
  · have hx' : IsIntegral ℚ x⁻¹ := (isAlgebraic_iff_isIntegral).mp hx.isAlgebraic.inv
    have hE : ℚ⟮x⁻¹⟯ = (ℚ⟮x⟯ : IntermediateField ℚ ℝ) := by
      apply le_antisymm
      · rw [IntermediateField.adjoin_le_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        exact IntermediateField.inv_mem _
          (IntermediateField.subset_adjoin ℚ ({x} : Set ℝ) (Set.mem_singleton x))
      · rw [IntermediateField.adjoin_le_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        have : (x⁻¹)⁻¹ ∈ (IntermediateField.adjoin ℚ ({x⁻¹} : Set ℝ) : IntermediateField ℚ ℝ) :=
          IntermediateField.inv_mem _
            (IntermediateField.subset_adjoin ℚ ({x⁻¹} : Set ℝ) (Set.mem_singleton x⁻¹))
        simpa using this
    haveI : FiniteDimensional ℚ ↥ℚ⟮x⁻¹⟯ := IntermediateField.adjoin.finiteDimensional hx'
    haveI : NumberField ↥ℚ⟮x⁻¹⟯ := {}
    haveI : FiniteDimensional ℚ ↥ℚ⟮x⟯ := IntermediateField.adjoin.finiteDimensional hx
    haveI : NumberField ↥ℚ⟮x⟯ := {}
    rw [NumberField.absMulHeight₁, NumberField.absMulHeight₁, dite_eq_left hx', dite_eq_left hx]
    have hH : Height.mulHeight₁ (IntermediateField.AdjoinSimple.gen ℚ x⁻¹)
        = Height.mulHeight₁ (IntermediateField.AdjoinSimple.gen ℚ x) := by
      rw [← mulHeight₁_algEquiv (IntermediateField.equivOfEq hE)
            (IntermediateField.AdjoinSimple.gen ℚ x⁻¹)]
      have hgen : IntermediateField.equivOfEq hE (IntermediateField.AdjoinSimple.gen ℚ x⁻¹)
          = (IntermediateField.AdjoinSimple.gen ℚ x)⁻¹ := by
        ext
        simp [IntermediateField.AdjoinSimple.coe_gen]
      rw [hgen, Height.mulHeight₁_inv]
    have hfin : Module.finrank ℚ ↥ℚ⟮x⁻¹⟯ = Module.finrank ℚ ↥ℚ⟮x⟯ := by rw [hE]
    rw [hH, hfin]
  · have hx' : ¬ IsIntegral ℚ x⁻¹ := by
      intro h
      exact hx (IsAlgebraic.isIntegral ((IsAlgebraic.inv_iff (R := ℚ) (x := x)).mp
        ((isAlgebraic_iff_isIntegral).mpr h)))
    rw [NumberField.absMulHeight₁, NumberField.absMulHeight₁,
      dite_eq_right hx', dite_eq_right hx]

end Work.WilkiesH.Norm
