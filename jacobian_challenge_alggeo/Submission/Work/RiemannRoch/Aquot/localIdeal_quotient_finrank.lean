import Mathlib
import Submission.Work.RiemannRoch.Quotients
import Submission.Work.CurveBasics.Linear.finrank_quotient_add_place

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits AlgebraicGeometry
open scoped Classical

universe u

namespace Work.RiemannRoch.Aquot

open Work.CurveBasics
open Work.RiemannRoch.Curve

noncomputable section

variable {k : Type u} [Field k]

/-! ## Dimension additivity along a chain of submodules -/

/-- Dimension additivity along a two-step chain `S ≤ T ≤ A` of submodules, in the
cardinal-valued form of `Module.rank` (so no finiteness hypothesis is needed). -/
theorem rank_tower {M : Type u} [AddCommGroup M] [Module k M]
    (S T A : Submodule k M) (hST : S ≤ T) (hTA : T ≤ A) :
    Module.rank k (↥A ⧸ Submodule.comap A.subtype S)
      = Module.rank k (↥A ⧸ Submodule.comap A.subtype T)
        + Module.rank k (↥T ⧸ Submodule.comap T.subtype S) := by
  set S' : Submodule k ↥A := Submodule.comap A.subtype S with hS'def
  set T' : Submodule k ↥A := Submodule.comap A.subtype T with hT'def
  have hS'T' : S' ≤ T' := Submodule.comap_mono hST
  -- the middle piece: `T/S ≅ T'.map S'.mkQ`
  have hmid : Module.rank k (T'.map S'.mkQ) = Module.rank k (↥T ⧸ Submodule.comap T.subtype S) := by
    have hker : (S'.mkQ.comp (Submodule.inclusion hTA)).ker = Submodule.comap T.subtype S := by
      rw [LinearMap.ker_comp, Submodule.ker_mkQ]
      ext t
      rw [Submodule.mem_comap, Submodule.mem_comap, ← Submodule.subtype_comp_inclusion T A hTA]
      rfl
    have hrange : (S'.mkQ.comp (Submodule.inclusion hTA)).range = T'.map S'.mkQ := by
      rw [LinearMap.range_eq_map, Submodule.map_comp]
      rw [← LinearMap.range_eq_map, Submodule.range_inclusion, ← hT'def]
    have h := (LinearMap.quotKerEquivRange (S'.mkQ.comp (Submodule.inclusion hTA))).rank_eq
    rw [hker, hrange] at h
    exact h.symm
  calc Module.rank k (↥A ⧸ S')
      = Module.rank k ((↥A ⧸ S') ⧸ T'.map S'.mkQ) + Module.rank k (T'.map S'.mkQ) :=
        (Submodule.rank_quotient_add_rank (T'.map S'.mkQ)).symm
    _ = Module.rank k (↥A ⧸ T') + Module.rank k (↥T ⧸ Submodule.comap T.subtype S) := by
        rw [(Submodule.quotientQuotientEquivQuotient S' T' hS'T').rank_eq, hmid]

/-! ## The one-step quotient `I_Q(j)/I_Q(j-1)` -/

/-- **The one-step local quotient.**  For every `j : ℤ` the quotient `I_Q(j)/I_Q(j-1)` of
consecutive fractional ideals at a place is the residue field `κ(Q)`, hence has `k`-dimension
`Q.degree`.

Let `ϖ` be a uniformizer of the discrete valuation ring `O_{C,Q}` and set `w = ϖ^j`.  The
`k`-linear map
`Φ : I_Q(j) → κ(Q), z ↦ (w z) mod 𝔪_Q`
(using the identification `O_{C,Q} ≅ I_Q(0)`, `z ↦ algebraMap z`) has kernel exactly `I_Q(j-1)`
and is surjective: the residue of an element of `O_{C,Q}` vanishes precisely on the maximal
ideal, and every residue class has a representative in `O_{C,Q}`. -/
theorem rank_localIdeal_step (C : Curve k) (Q : C.Place) (j : ℤ) :
    Module.rank k (↥(localIdeal C Q j) ⧸
        (localIdeal C Q (j - 1)).comap (localIdeal C Q j).subtype)
      = ((Q.degree : ℕ) : Cardinal) := by
  classical
  haveI hDVR : IsDiscreteValuationRing (C.left.presheaf.stalk Q.point) :=
    Place.isDiscreteValuationRing Q
  letI : Algebra k (C.left.presheaf.stalk Q.point) := Linear.instAlgebraStalk C Q
  haveI hST : IsScalarTower k (C.left.presheaf.stalk Q.point) C.functionField :=
    Linear.isScalarTower_stalk_field C Q
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible (C.left.presheaf.stalk Q.point)
  have hu_ne : (algebraMap (C.left.presheaf.stalk Q.point) C.functionField ϖ) ≠ 0 := by
    intro h
    exact hϖ.ne_zero ((FaithfulSMul.algebraMap_injective _ _) (by rw [h, map_zero]))
  set w : C.functionField := (algebraMap (C.left.presheaf.stalk Q.point) C.functionField ϖ) ^ j
    with hw_def
  have hw_ne : w ≠ 0 := by
    rw [hw_def]
    exact zpow_ne_zero j hu_ne
  have hordw : AlgebraicGeometry.Scheme.ord w Q.point = j := by
    rw [hw_def]
    exact Linear.ord_zpow_uniformizer C Q hϖ j
  have hordFrac_w : Ring.ordFrac (C.left.presheaf.stalk Q.point) w = WithZero.exp j := by
    rw [hw_def, map_zpow₀, Ring.ordFrac_irreducible hϖ, ← WithZero.exp_zsmul j (1 : ℤ)]
    have h : j • (1 : ℤ) = j := by simp
    rw [h, WithZero.exp_eq_coe_ofAdd]
  -- membership in `I_Q(0)` is nonnegativity of the order
  have hV0_ord : ∀ y : C.functionField,
      y ∈ localIdeal C Q 0 ↔ 0 ≤ AlgebraicGeometry.Scheme.ord y Q.point := fun y =>
    (mem_localIdeal_zero).trans (Place.mem_valuationSubring_iff C Q y)
  -- the linear map `ι : O_{C,Q} → K` given by `algebraMap`
  let ι : (C.left.presheaf.stalk Q.point) →ₗ[k] C.functionField :=
    (IsScalarTower.toAlgHom k (C.left.presheaf.stalk Q.point) C.functionField).toLinearMap
  have hι_apply (a : C.left.presheaf.stalk Q.point) :
      ι a = algebraMap (C.left.presheaf.stalk Q.point) C.functionField a := rfl
  have hι_inj : Function.Injective ι := by
    intro a b hab
    exact FaithfulSMul.algebraMap_injective _ _ (by simpa only [hι_apply] using hab)
  have hι_mem : ∀ a : C.left.presheaf.stalk Q.point, ι a ∈ localIdeal C Q 0 := by
    intro a
    rw [hV0_ord]
    show 0 ≤ AlgebraicGeometry.Scheme.ord
      (algebraMap (C.left.presheaf.stalk Q.point) C.functionField a) Q.point
    by_cases ha : a = 0
    · rw [ha, map_zero]; simp
    · have hane : algebraMap (C.left.presheaf.stalk Q.point) C.functionField a ≠ 0 :=
        fun h => ha ((FaithfulSMul.algebraMap_injective _ _) (by rw [h, map_zero]))
      have h1 : 1 ≤ Ring.ordFrac (C.left.presheaf.stalk Q.point)
          (algebraMap (C.left.presheaf.stalk Q.point) C.functionField a) :=
        Ring.ordFrac_ge_one_of_ne_zero ha
      exact (Linear.le_ord_iff_ordFrac C Q _ hane).mpr h1
  have hsurjι : Function.Surjective (ι.codRestrict (localIdeal C Q 0) hι_mem) := by
    intro y
    by_cases hy0 : (y : C.functionField) = 0
    · refine ⟨0, ?_⟩
      apply Subtype.ext
      simp [hy0]
    · have hyord : 0 ≤ AlgebraicGeometry.Scheme.ord (y : C.functionField) Q.point :=
        (hV0_ord _).mp y.2
      have h1 : 1 ≤ Ring.ordFrac (C.left.presheaf.stalk Q.point) (y : C.functionField) :=
        (Linear.le_ord_iff_ordFrac C Q _ hy0).mp hyord
      obtain ⟨a, ha⟩ := Linear.exists_algebraMap_eq_of_one_le_ordFrac h1
      exact ⟨a, by
        apply Subtype.ext
        simpa only [LinearMap.codRestrict_apply, hι_apply] using ha⟩
  let e : (C.left.presheaf.stalk Q.point) ≃ₗ[k] ↥(localIdeal C Q 0) :=
    LinearEquiv.ofBijective (ι.codRestrict (localIdeal C Q 0) hι_mem)
      ⟨fun a b hab =>
        hι_inj (by simpa only [LinearMap.codRestrict_apply] using congrArg Subtype.val hab),
        hsurjι⟩
  have he_apply (a : C.left.presheaf.stalk Q.point) :
      ((e a : ↥(localIdeal C Q 0)) : C.functionField) =
        algebraMap (C.left.presheaf.stalk Q.point) C.functionField a := by
    dsimp only [e]
    rfl
  have he_symm (y : ↥(localIdeal C Q 0)) :
      algebraMap (C.left.presheaf.stalk Q.point) C.functionField (e.symm y) =
        (y : C.functionField) := by
    have h := he_apply (e.symm y)
    rw [LinearEquiv.apply_symm_apply] at h
    exact h.symm
  -- the residue map as a `k`-linear map
  let ρ : (C.left.presheaf.stalk Q.point) →ₗ[k] C.left.residueField Q.point :=
    { toFun := fun a => (C.left.residue Q.point).hom a
      map_add' := fun a b => (C.left.residue Q.point).hom.map_add a b
      map_smul' := fun c a => by
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def, map_mul, Algebra.smul_def,
          show (C.left.residue Q.point).hom (algebraMap k (C.left.presheaf.stalk Q.point) c)
              = algebraMap k (C.left.residueField Q.point) c from Linear.residue_algebraMap_eq C Q c] }
  -- multiplication by `w`
  let θ : C.functionField →ₗ[k] C.functionField := LinearMap.mulLeft k w
  have hθ_apply (y : C.functionField) : θ y = w * y := LinearMap.mulLeft_apply k w y
  have hV' : ∀ x : ↥(localIdeal C Q j),
      (θ.comp (localIdeal C Q j).subtype) x ∈ localIdeal C Q 0 := by
    intro x
    rw [hV0_ord]
    show 0 ≤ AlgebraicGeometry.Scheme.ord (w * (x : C.functionField)) Q.point
    by_cases hx0 : (x : C.functionField) = 0
    · rw [hx0, mul_zero]; simp
    · have hordx : -j ≤ AlgebraicGeometry.Scheme.ord (x : C.functionField) Q.point := by
        rcases (mem_localIdeal.mp x.2) with h | h
        · exact absurd h hx0
        · simpa only [Work.CurveBasics.Curve.ordAt] using h
      rw [AlgebraicGeometry.Scheme.ord_mul hw_ne hx0, hordw]
      linarith
  -- the map `Φ`
  let Φ : ↥(localIdeal C Q j) →ₗ[k] C.left.residueField Q.point :=
    (ρ.comp e.symm.toLinearMap).comp
      ((θ.comp (localIdeal C Q j).subtype).codRestrict (localIdeal C Q 0) hV')
  have hΦ_apply (x : ↥(localIdeal C Q j)) :
      Φ x = (C.left.residue Q.point).hom
        (e.symm ⟨(θ.comp (localIdeal C Q j).subtype) x, hV' x⟩) := rfl
  -- the kernel of `Φ` is `I_Q(j-1)`
  have hker : Φ.ker = (localIdeal C Q (j - 1)).comap (localIdeal C Q j).subtype := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap]
    by_cases hx0 : (x : C.functionField) = 0
    · have hx : x = 0 := Subtype.ext hx0
      rw [hx, map_zero]
      constructor
      · intro _; exact Submodule.zero_mem _
      · intro _; rfl
    · have hordx : -j ≤ AlgebraicGeometry.Scheme.ord (x : C.functionField) Q.point := by
        rcases (mem_localIdeal.mp x.2) with h | h
        · exact absurd h hx0
        · simpa only [Work.CurveBasics.Curve.ordAt] using h
      set a : C.left.presheaf.stalk Q.point :=
        e.symm ⟨(θ.comp (localIdeal C Q j).subtype) x, hV' x⟩ with ha_def
      have ha_val : algebraMap (C.left.presheaf.stalk Q.point) C.functionField a =
          w * (x : C.functionField) := by
        rw [ha_def, he_symm]
        rfl
      have hwx : Ring.ordFrac (C.left.presheaf.stalk Q.point) (w * (x : C.functionField))
          = WithZero.exp (j + AlgebraicGeometry.Scheme.ord (x : C.functionField) Q.point) := by
        rw [map_mul, hordFrac_w, Linear.ordFrac_eq_exp_ord C Q _ hx0, ← WithZero.exp_add]
      rw [hΦ_apply x, ← ha_def]
      change IsLocalRing.residue (C.left.presheaf.stalk Q.point) a = 0 ↔
        (x : C.functionField) ∈ localIdeal C Q (j - 1)
      rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal]
      change (¬ IsUnit a) ↔ (x : C.functionField) ∈ localIdeal C Q (j - 1)
      rw [Ring.isUnit_iff_ordFrac_one_of_isDiscreteValuationRing (K := C.functionField), ha_val,
        hwx, ← WithZero.exp_zero, WithZero.exp_inj]
      rw [mem_localIdeal]
      constructor
      · intro h
        refine Or.inr ?_
        show -(j - 1) ≤ AlgebraicGeometry.Scheme.ord (x : C.functionField) Q.point
        have hpos : (0 : ℤ) < j + AlgebraicGeometry.Scheme.ord (x : C.functionField) Q.point :=
          lt_of_le_of_ne' (by linarith) h
        linarith
      · rintro (h0 | h0)
        · exact absurd h0 hx0
        · intro hc
          linarith
  -- `Φ` is surjective
  have hsurj : Function.Surjective Φ := by
    intro c
    obtain ⟨a, ha⟩ := IsLocalRing.residue_surjective c
    have hEA : 0 ≤ AlgebraicGeometry.Scheme.ord (e a : C.functionField) Q.point :=
      (hV0_ord _).mp (e a).2
    have hordwinv : AlgebraicGeometry.Scheme.ord (w⁻¹ : C.functionField) Q.point = -j := by
      show C.ordAt (w⁻¹) Q = -j
      rw [Work.CurveBasics.Curve.ordAt_inv C hw_ne Q]
      rw [show C.ordAt w Q = j from hordw]
    have hxmem : w⁻¹ * (e a : C.functionField) ∈ localIdeal C Q j := by
      rw [mem_localIdeal]
      by_cases hx0 : (e a : C.functionField) = 0
      · exact Or.inl (by rw [hx0, mul_zero])
      · refine Or.inr ?_
        show -j ≤ AlgebraicGeometry.Scheme.ord (w⁻¹ * (e a : C.functionField)) Q.point
        rw [AlgebraicGeometry.Scheme.ord_mul (inv_ne_zero hw_ne) hx0, hordwinv]
        linarith
    refine ⟨⟨w⁻¹ * (e a : C.functionField), hxmem⟩, ?_⟩
    rw [hΦ_apply]
    have hsub : (⟨(θ.comp (localIdeal C Q j).subtype)
          ⟨w⁻¹ * (e a : C.functionField), hxmem⟩, hV' _⟩ : ↥(localIdeal C Q 0)) = e a := by
      apply Subtype.ext
      show w * (w⁻¹ * (e a : C.functionField)) = (e a : C.functionField)
      rw [← mul_assoc, mul_inv_cancel₀ hw_ne, one_mul]
    rw [hsub, LinearEquiv.symm_apply_apply]
    exact ha
  have hrange : Φ.range = ⊤ := LinearMap.range_eq_top.mpr hsurj
  haveI : Module.Finite k (C.left.residueField Q.point) :=
    Linear.finiteDimensional_residueField C Q
  calc Module.rank k (↥(localIdeal C Q j) ⧸ (localIdeal C Q (j - 1)).comap
        (localIdeal C Q j).subtype)
      = Module.rank k (↥(localIdeal C Q j) ⧸ Φ.ker) := by rw [hker]
    _ = Module.rank k ↥Φ.range := (LinearMap.quotKerEquivRange Φ).rank_eq
    _ = Module.rank k ↥(⊤ : Submodule k (C.left.residueField Q.point)) := by rw [hrange]
    _ = Module.rank k (C.left.residueField Q.point) := Submodule.topEquiv.rank_eq
    _ = ((Q.degree : ℕ) : Cardinal) := by
        rw [← Module.finrank_eq_rank k (C.left.residueField Q.point),
          Work.CurveBasics.Place.degree_eq_finrank Q]

/-! ## The chain of local ideals -/

/-- **Dimension of `I_Q(m+N)/I_Q(m)`.**  Induction on `N` from the one-step computation
`I_Q(j)/I_Q(j-1) ≅ κ(Q)`, using additivity of `Module.rank` along a two-step chain. -/
theorem rank_localIdeal_chain (C : Curve k) (Q : C.Place) :
    ∀ N : ℕ, ∀ m : ℤ,
      Module.rank k (↥(localIdeal C Q (m + N)) ⧸
          (localIdeal C Q m).comap (localIdeal C Q (m + N)).subtype)
        = ((N * Q.degree : ℕ) : Cardinal) := by
  intro N
  induction N with
  | zero =>
      intro m
      have h1 : m + ((0 : ℕ) : ℤ) = m := by norm_num
      rw [h1, Submodule.comap_subtype_self,
        show ((0 * Q.degree : ℕ) : Cardinal) = 0 by simp, rank_zero_iff]
      exact inferInstance
  | succ N ih =>
      intro m
      have hcast : ((N + 1 : ℕ) : ℤ) = (N : ℤ) + 1 := by push_cast; ring
      rw [hcast]
      have hST : localIdeal C Q m ≤ localIdeal C Q (m + (N : ℤ)) :=
        localIdeal_mono C (by omega)
      have hTA : localIdeal C Q (m + (N : ℤ)) ≤ localIdeal C Q (m + ((N : ℤ) + 1)) :=
        localIdeal_mono C (by omega)
      rw [rank_tower (S := localIdeal C Q m) (T := localIdeal C Q (m + (N : ℤ)))
        (A := localIdeal C Q (m + ((N : ℤ) + 1))) hST hTA]
      have hstep : Module.rank k (↥(localIdeal C Q (m + ((N : ℤ) + 1))) ⧸
          (localIdeal C Q (m + (N : ℤ))).comap
            (localIdeal C Q (m + ((N : ℤ) + 1))).subtype)
          = ((Q.degree : ℕ) : Cardinal) := by
        have hidx : m + (N : ℤ) = (m + ((N : ℤ) + 1)) - 1 := by ring
        rw [hidx]
        exact rank_localIdeal_step C Q (m + ((N : ℤ) + 1))
      have harith : ((Q.degree : ℕ) : Cardinal) + ((N * Q.degree : ℕ) : Cardinal)
          = (((N + 1) * Q.degree : ℕ) : Cardinal) := by
        rw [← Nat.cast_add, Nat.succ_mul, Nat.add_comm]
      rw [hstep, ih m, harith]

end

/-! ## The dimension of the local quotient -/

/-- **The local ideal quotient `I_Q(n)/I_Q(m)`.**  For `m ≤ n` the quotient of the fractional
ideals `I_Q(t) = localIdeal C Q t = {u : K(C) | u = 0 ∨ ord_Q u ≥ -t}` of `K(C)` is finite
dimensional over `k` of dimension `(n - m) * [κ(Q) : k]`.

Suggested construction (`k` below denotes `(n-m).toNat`): let `w` be a uniformizer at `Q`
(`w = algebraMap O_{C,Q} K(C) ϖ` for `ϖ` irreducible in the DVR `O_{C,Q} = stalk Q.point`, so
`Scheme.ord (w ^ j) Q.point = j`, see `ord_zpow_uniformizer`), and use the two proven helpers
`e : O_{C,Q} ≃ₗ[k] ↥(localIdeal C Q 0)` (given by `algebraMap`, via
`exists_algebraMap_eq_of_one_le_ordFrac` for surjectivity) and
`ρ : O_{C,Q} →ₗ[k] κ(Q)` (the residue map, `k`-linearity from `residue_algebraMap_eq`).
The map `φ : ↥(localIdeal C Q n) →ₗ[k] (Fin k → κ(Q))`,
`φ z i = ρ (e.symm ⟨w ^ (m + 1 + i) * z, _⟩)` (well defined because `ord (w ^ (m+1+i) * z) ≥ 0`)
has kernel `(localIdeal C Q m).comap subtype` (compute
`ρ (e.symm ⟨u,_⟩) = 0 ↔ ord u ≥ 1`) and is surjective: for prescribed residues pick
`γ_i : O_{C,Q}` with `residue γ_i` prescribed and set
`z := Σ_i w ^ (-(m + 1 + i)) * e γ_i ∈ localIdeal C Q n`; then `φ z i = residue γ_i`.  Hence
`φ` induces an isomorphism `I_Q(n)/I_Q(m) ≅ (Fin k → κ(Q))` via `LinearMap.quotKerEquivRange`
and `Submodule.quotEquivOfEq`, and `finrank k κ(Q) = Q.degree` by `Place.degree_eq_finrank`. -/
theorem localIdeal_quotient_finrank {k : Type u} [Field k] (C : Work.CurveBasics.Curve k)
    (Q : C.Place) {m n : ℤ} (hmn : m ≤ n) :
    Module.Finite k (↥(Work.RiemannRoch.Curve.localIdeal C Q n) ⧸
        (Work.RiemannRoch.Curve.localIdeal C Q m).comap
          (Work.RiemannRoch.Curve.localIdeal C Q n).subtype) ∧
    Module.finrank k (↥(Work.RiemannRoch.Curve.localIdeal C Q n) ⧸
        (Work.RiemannRoch.Curve.localIdeal C Q m).comap
          (Work.RiemannRoch.Curve.localIdeal C Q n).subtype)
      = (n - m).toNat * Q.degree := by
  have hpos : 0 ≤ n - m := by omega
  have hidx : m + (((n - m).toNat : ℕ) : ℤ) = n := by
    rw [Int.toNat_of_nonneg hpos]
    ring
  have h := rank_localIdeal_chain C Q ((n - m).toNat) m
  rw [hidx] at h
  constructor
  · rw [← Module.rank_lt_aleph0_iff, h]
    exact Cardinal.natCast_lt_aleph0
  · simp only [Module.finrank, h, Cardinal.toNat_natCast]

end Work.RiemannRoch.Aquot
