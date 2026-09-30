import Mathlib
import Submission.Work.GroupChunk.GroupLaw.MulDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.GroupChunk.GroupLaw

noncomputable section

open Work.GCBasics
open Work.GroupChunk

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
  [SpecLin.DivBase C]

/-! ## The two pieces of the class of a point of `Sym^g C ⊗ Sym^g C`

The multiplication `mulσ i j k` of `MulDefs` is specified by RESID for the maps
`mulA i j : (x, y) ↦ E i + E j` and `mulB k : (x, y) ↦ x + y + E k`, so at a point
`q` of `Sym^g C ⊗ Sym^g C` the residual divisor is

`divOf q.1 + divOf q.2 + E k - E i - E j`,

of degree `g`.  `AFmul` is this divisor over the field `F` of definition of `q`, written in
the shape produced by VALUE of `mulσ`; `Aκmul` is its pullback to the residue field `κ(q)`,
which is the shape appearing in DEFINED (`mulσ_mem_domain`). -/

/-- The `F`-level divisor of the DEFINED property of `mulσ i j k`. -/
noncomputable abbrev AFmul (D : Input C P0) (i j k : D.Idx) {F : Type u} [Field F]
    [Algebra K F] (q : FPt (SymSym D) F) : Dv C F :=
  ((D.divOf D.g (q ≫ fst (D.Sym D.g) (D.Sym D.g))
    + D.divOf D.g (q ≫ snd (D.Sym D.g) (D.Sym D.g))) + bcKF F (D.EDiv k))
  - (bcKF F (D.EDiv i) + bcKF F (D.EDiv j))

/-- The `κ(q)`-level divisor of the DEFINED property of `mulσ i j k`. -/
noncomputable abbrev Aκmul (D : Input C P0) (i j k : D.Idx) {F : Type u} [Field F]
    [Algebra K F] (q : FPt (SymSym D) F) : Dv C (resK q) :=
  D.divOf ((D.g + D.g) + D.g)
      (resPt (SymSym D) (q.left (IsLocalRing.closedPoint F)) ≫ mulB D k)
    - D.divOf (D.g + D.g)
      (resPt (SymSym D) (q.left (IsLocalRing.closedPoint F)) ≫ mulA D i j)

/-- **Membership in `mulW i j k` from a representative in the chart.**  This is the
two-variable analogue of the second half of `Work.GroupChunk.landsIn_U_iff`: if the class
`picOf i q.1 + picOf j q.2` of a point `q` of `Sym^g C ⊗ Sym^g C` is represented in the
chart `V` with base divisor `E k`, then `mulσ i j k` is defined at `q` and its value lies
in `V`.

Indeed, with `y ∈ V` and `picOf k y = picOf i q.1 + picOf j q.2`, the divisor `AFmul i j k q`
is linearly equivalent to `divOf y`, and `ℓ(divOf y) = 1` (`ell_of_landsIn_V`), so
`ℓ(AFmul i j k q) = 1`; base changing to the residue field of the image point of `q`
(`ell_eq_one_of_bc`, as in `landsIn_U_iff`) gives the hypothesis of DEFINED
(`mulσ_mem_domain`).  VALUE (`mulσ_value`) then shows that the value of `mulσ` is an
effective divisor linearly equivalent to `divOf y`; since `ℓ(divOf y) = 1` it *is* `divOf y`
(`linEquiv_eq_of_ell_eq_one`), hence `divOf_injective` gives that the value is `y`, which
lies in `V`; `mulW_mem_of_val_mem_V` concludes. -/
theorem landsIn_mulW_of_picOf_eq_aux (D : Input C P0) (i j k : D.Idx)
    {F : Type u} [Field F] [Algebra K F] (q : FPt (SymSym D) F)
    (y : FPt (D.Sym D.g) F) (hy : RPt.LandsIn y D.V)
    (hc : D.picOf k y = D.picOf i (q ≫ fst (D.Sym D.g) (D.Sym D.g))
        + D.picOf j (q ≫ snd (D.Sym D.g) (D.Sym D.g))) :
    RPt.LandsIn q (mulW D i j k) := by
  -- the `F`-level linear equivalence `divOf y - E k ~ divOf q.1 + divOf q.2 - E i - E j`
  have hd1 := ddeg_sub_divOf D.symGeom D.g (q ≫ fst (D.Sym D.g) (D.Sym D.g)) (D.EF i)
  have hd2 := ddeg_sub_divOf D.symGeom D.g (q ≫ snd (D.Sym D.g) (D.Sym D.g)) (D.EF j)
  have hd3 : Ddeg C F ((D.divOf D.g (q ≫ fst (D.Sym D.g) (D.Sym D.g)) - D.divOf D.g (D.EF i))
      + (D.divOf D.g (q ≫ snd (D.Sym D.g) (D.Sym D.g)) - D.divOf D.g (D.EF j))) = 0 := by
    rw [map_add, hd1, hd2, add_zero]
  have hL : LinEquiv C (D.divOf D.g y - D.divOf D.g (D.EF k))
      ((D.divOf D.g (q ≫ fst (D.Sym D.g) (D.Sym D.g)) - D.divOf D.g (D.EF i))
       + (D.divOf D.g (q ≫ snd (D.Sym D.g) (D.Sym D.g)) - D.divOf D.g (D.EF j))) := by
    rw [Input.picOf_def, Input.picOf_def, Input.picOf_def] at hc
    rw [← Pic0.mk_add hd1 hd2 hd3] at hc
    exact (Pic0.mk_eq_iff _ _).mp hc
  -- rearrange it into the shape of VALUE of `mulσ`
  have hL' : LinEquiv C (D.divOf D.g y - D.divOf D.g (D.EF k))
      ((D.divOf D.g (q ≫ fst (D.Sym D.g) (D.Sym D.g))
        + D.divOf D.g (q ≫ snd (D.Sym D.g) (D.Sym D.g)))
       - (D.divOf D.g (D.EF i) + D.divOf D.g (D.EF j))) := by
    convert hL using 2
    abel
  have hyv : LinEquiv C (D.divOf D.g y + (D.divOf D.g (D.EF i) + D.divOf D.g (D.EF j)))
      ((D.divOf D.g (q ≫ fst (D.Sym D.g) (D.Sym D.g))
        + D.divOf D.g (q ≫ snd (D.Sym D.g) (D.Sym D.g))) + D.divOf D.g (D.EF k)) :=
    (linEquiv_add_iff_sub _ _ _ _).mp hL'
  have hyvbc : LinEquiv C (D.divOf D.g y + (bcKF F (D.EDiv i) + bcKF F (D.EDiv j)))
      ((D.divOf D.g (q ≫ fst (D.Sym D.g) (D.Sym D.g))
        + D.divOf D.g (q ≫ snd (D.Sym D.g) (D.Sym D.g))) + bcKF F (D.EDiv k)) := by
    simpa only [Input.EF_divOf] using hyv
  -- hence `ℓ (AFmul i j k q) = 1`
  have h5 : LinEquiv C (D.divOf D.g y) (AFmul D i j k q) := by
    have key := (LinEquiv.sub_iff
      (D.divOf D.g y + (bcKF F (D.EDiv i) + bcKF F (D.EDiv j)))
      ((D.divOf D.g (q ≫ fst (D.Sym D.g) (D.Sym D.g))
        + D.divOf D.g (q ≫ snd (D.Sym D.g) (D.Sym D.g))) + bcKF F (D.EDiv k))
      (bcKF F (D.EDiv i) + bcKF F (D.EDiv j))).mpr hyvbc
    simpa only [add_sub_cancel_right, AFmul] using key
  have hellF : ell C (AFmul D i j k q) = 1 := by
    rw [← ell_eq_of_linEquiv h5]
    exact ell_of_landsIn_V (D := D) y hy
  -- the same, base changed to the residue field of the image point of `q`
  obtain ⟨e, he⟩ := exists_factor_resPt (X := SymSym D) (p := q)
  have hmapB : RPt.map e (resPt (SymSym D) (q.left (IsLocalRing.closedPoint F)) ≫ mulB D k)
      = q ≫ mulB D k := by
    rw [show RPt.map e (resPt (SymSym D) (q.left (IsLocalRing.closedPoint F)) ≫ mulB D k)
        = RPt.map e (resPt (SymSym D) (q.left (IsLocalRing.closedPoint F))) ≫ mulB D k from rfl,
      ← he]
  have hmapA : RPt.map e (resPt (SymSym D) (q.left (IsLocalRing.closedPoint F)) ≫ mulA D i j)
      = q ≫ mulA D i j := by
    rw [show RPt.map e (resPt (SymSym D) (q.left (IsLocalRing.closedPoint F)) ≫ mulA D i j)
        = RPt.map e (resPt (SymSym D) (q.left (IsLocalRing.closedPoint F))) ≫ mulA D i j from rfl,
      ← he]
  have hB : SpecLin.DivBase.bc e
      (D.divOf ((D.g + D.g) + D.g) (resPt (SymSym D) (q.left (IsLocalRing.closedPoint F))
        ≫ mulB D k))
      = ((D.divOf D.g (q ≫ fst (D.Sym D.g) (D.Sym D.g))
        + D.divOf D.g (q ≫ snd (D.Sym D.g) (D.Sym D.g))) + bcKF F (D.EDiv k)) := by
    rw [← divOf_map' ((D.g + D.g) + D.g) e
      (resPt (SymSym D) (q.left (IsLocalRing.closedPoint F)) ≫ mulB D k), hmapB]
    exact divOf_mulB D k q
  have hA : SpecLin.DivBase.bc e
      (D.divOf (D.g + D.g) (resPt (SymSym D) (q.left (IsLocalRing.closedPoint F))
        ≫ mulA D i j)) = (bcKF F (D.EDiv i) + bcKF F (D.EDiv j)) := by
    rw [← divOf_map' (D.g + D.g) e
      (resPt (SymSym D) (q.left (IsLocalRing.closedPoint F)) ≫ mulA D i j), hmapA]
    exact divOf_mulA D i j q
  have hbc : SpecLin.DivBase.bc e (Aκmul D i j k q) = AFmul D i j k q := by
    simp only [Aκmul, AFmul, sub_eq_add_neg, SpecLin.DivBase.bc_add, SpecLin.DivBase.bc_neg,
      hB, hA]
  have hdeg : Ddeg C (resK q) (Aκmul D i j k q) = (D.g : ℤ) := by
    have h1 : Ddeg C (resK q) (D.divOf ((D.g + D.g) + D.g)
        (resPt (SymSym D) (q.left (IsLocalRing.closedPoint F)) ≫ mulB D k))
        = (((D.g + D.g) + D.g : ℕ) : ℤ) := (D.symGeom ((D.g + D.g) + D.g)).divOf_deg _
    have h2 : Ddeg C (resK q) (D.divOf (D.g + D.g)
        (resPt (SymSym D) (q.left (IsLocalRing.closedPoint F)) ≫ mulA D i j))
        = ((D.g + D.g : ℕ) : ℤ) := (D.symGeom (D.g + D.g)).divOf_deg _
    simp only [Aκmul, map_sub, h1, h2]
    push_cast
    ring
  have hAκ : ell C (Aκmul D i j k q) = 1 :=
    ell_eq_one_of_bc e _ hdeg (by rw [hbc]; exact hellF)
  -- DEFINED: `mulσ i j k` is defined at `q`
  have hdom : RPt.LandsIn q (mulσ D i j k).domain :=
    mulσ_mem_domain D i j k (q.left (IsLocalRing.closedPoint F)) hAκ
  -- VALUE: the value of `mulσ i j k` at `q` is `y`
  have hsv := mulσ_value D i j k q hdom
  have h4 : LinEquiv C (D.divOf D.g (mulσVal D i j k q hdom)
        + (bcKF F (D.EDiv i) + bcKF F (D.EDiv j)))
      (D.divOf D.g y + (bcKF F (D.EDiv i) + bcKF F (D.EDiv j))) :=
    hsv.trans hyvbc.symm
  have h6 : LinEquiv C (D.divOf D.g (mulσVal D i j k q hdom)) (D.divOf D.g y) := by
    have key := (LinEquiv.sub_iff
      (D.divOf D.g (mulσVal D i j k q hdom) + (bcKF F (D.EDiv i) + bcKF F (D.EDiv j)))
      (D.divOf D.g y + (bcKF F (D.EDiv i) + bcKF F (D.EDiv j)))
      (bcKF F (D.EDiv i) + bcKF F (D.EDiv j))).mpr h4
    simpa only [add_sub_cancel_right] using key
  have h7 : D.divOf D.g y = D.divOf D.g (mulσVal D i j k q hdom) :=
    linEquiv_eq_of_ell_eq_one ((D.symGeom D.g).divOf_isEffective y)
      (ell_of_landsIn_V (D := D) y hy)
      ((D.symGeom D.g).divOf_isEffective (mulσVal D i j k q hdom)) h6.symm
  have hyval : mulσVal D i j k q hdom = y :=
    ((D.symGeom D.g).divOf_injective y (mulσVal D i j k q hdom) h7).symm
  exact mulW_mem_of_val_mem_V D i j k q hdom (by rw [hyval]; exact hy)

/-! ## The pieces cover `G D ⊗ G D` -/

/-- **The pieces of the multiplication cover `G D ⊗ G D` at field points.**

Let `u : Spec F ⟶ G D ⊗ G D` be an `F`-point, with coordinates `x = u ≫ fst` and
`y = u ≫ snd`.  The charts cover `G D` (`Input.exists_factor`), so `x` factors through the
`i`-th chart `chartH i` and `y` through the `j`-th chart `chartH j`.  Let
`c = picOf i x' + picOf j y' = cls x + cls y` be the class of the pair in `Pic⁰`.  By COV
(`Input.cov'`) the class `c` has a representative `z ∈ V` with base divisor `E k` for some
`k`.  Then `landsIn_mulW_of_picOf_eq_aux` shows that the pair `(x', y')` lies in `mulW i j k`,
i.e. `(q) ∈ mulZ (i,j,k)` for the corresponding point `q` of `V ⊗ V`; factorising `q`
through the open `mulZ (i,j,k)` and composing with
`mulPieceGG (i,j,k) = ιOver (mulZ _) ≫ (chartH i ⊗ₘ chartH j)` gives the required
factorisation of `u`. -/
theorem mulZ_covers_pt {K : Type*} [Field K] {C : Work.CurveBasics.Curve K}
    {P0 : CategoryTheory.MonoidalCategoryStruct.tensorUnit (Work.GCBasics.Sch K) ⟶ C.toOver}
    [Work.SpecLin.DivBase C] (D : Work.GroupChunk.Input C P0) :
    Work.GroupChunk.GroupLaw.MulCovers D := by
  intro F _ _ u
  -- the two coordinates of `u`, expressed in the charts
  obtain ⟨i, q₁, hq₁⟩ := Work.GroupChunk.Input.exists_factor D (u ≫ fst (GSch D) (GSch D))
  obtain ⟨j, q₂, hq₂⟩ := Work.GroupChunk.Input.exists_factor D (u ≫ snd (GSch D) (GSch D))
  -- the corresponding point of `V ⊗ V`
  let p : FPt (VVo D) F := (FPt.tensorEquiv (Opens.toOver D.V) (Opens.toOver D.V) F).symm (q₁, q₂)
  have hp_fst : p ≫ fst (Opens.toOver D.V) (Opens.toOver D.V) = q₁ :=
    FPt.tensorEquiv_symm_fst _ _ F (q₁, q₂)
  have hp_snd : p ≫ snd (Opens.toOver D.V) (Opens.toOver D.V) = q₂ :=
    FPt.tensorEquiv_symm_snd _ _ F (q₁, q₂)
  have hq_fst : (p ≫ eVV D) ≫ fst (D.Sym D.g) (D.Sym D.g) = q₁ ≫ Opens.ιOver D.V := by
    rw [Category.assoc, eVV_fst, ← Category.assoc, hp_fst]
  have hq_snd : (p ≫ eVV D) ≫ snd (D.Sym D.g) (D.Sym D.g) = q₂ ≫ Opens.ιOver D.V := by
    rw [Category.assoc, eVV_snd, ← Category.assoc, hp_snd]
  -- COV: the class of the pair is represented in the chart `V` with base divisor `E k`
  obtain ⟨k, z, hzV, hz⟩ := D.cov' (D.picOf i ((p ≫ eVV D) ≫ fst (D.Sym D.g) (D.Sym D.g))
    + D.picOf j ((p ≫ eVV D) ≫ snd (D.Sym D.g) (D.Sym D.g)))
  have hW : RPt.LandsIn (p ≫ eVV D) (mulW D i j k) :=
    landsIn_mulW_of_picOf_eq_aux D i j k (p ≫ eVV D) z hzV hz
  have hZ : RPt.LandsIn p (mulZ D (i, j, k)) := by
    have := (RPt.landsIn_preimage (p := p) (f := eVV D) (V := mulW D i j k)).mp hW
    simpa only [mulZ] using this
  obtain ⟨v, hv, -⟩ := FPt.factor_of_landsIn (mulZ D (i, j, k)) p hZ
  refine ⟨(i, j, k), v, ?_⟩
  -- it remains to compare the two points of `G D ⊗ G D`
  rw [mulPieceGG, ← Category.assoc, hv]
  have hp : p = CartesianMonoidalCategory.lift q₁ q₂ := rfl
  rw [hp, CartesianMonoidalCategory.lift_map]
  show CartesianMonoidalCategory.lift (q₁ ≫ D.chart i) (q₂ ≫ D.chart j) = u
  rw [hq₁, hq₂]
  exact CartesianMonoidalCategory.lift_comp_fst_snd u

end

end Work.GroupChunk.GroupLaw
