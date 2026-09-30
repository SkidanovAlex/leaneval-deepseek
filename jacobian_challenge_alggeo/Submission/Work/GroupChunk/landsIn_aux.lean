import Mathlib
import Submission.Work.GroupChunk.Defs
import Submission.Work.CurveBasics.Order.deg_div
import Submission.Work.GCBasics.div_eq_zero_iff_isConstant
import Submission.Work.GCBasics.ell_eq_of_linEquiv
import Submission.Work.GCBasics.linEquiv_eq_of_ell_eq_one

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.GroupChunk

open CategoryTheory AlgebraicGeometry
open scoped MonoidalCategory
open scoped Work.GCBasics

universe u

noncomputable section

open Work.GCBasics

variable {K : Type u} [Field K] {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver}
  [SpecLin.DivBase C]

/-! ## Auxiliary lemmas: transfer of `ℓ = 1` along a field extension

The transition `σ i j` is only *specified* by the RESID engine: VALUE at the points of its
domain, and DEFINED (membership of the domain) at *scheme* points `x`, where the hypothesis
is a statement about the residue field `κ(x)`.  To use DEFINED at an arbitrary field point
`p : FPt X F` we must transfer `ℓ = 1` from `F` down to `κ(x)`.

The lemmas below do this, in the style of `Work.SpecLin.specLin`: the key is that base change
of points of `Sym^g` along a field extension is injective, so an effective divisor of degree
`g` over a field is determined by its base change.  `ell_eq_one_of_bc` is the lemma consumed
by `landsIn_U_iff`. -/

/-- Precomposition with the base change of the field of definition is injective:
`RPt.map e` is an injective map on points.  This is `cancel_epi`, using that
`Spec F' ⟶ Spec F` is an epimorphism of schemes (it is surjective and flat). -/
theorem smap_injective {X : Sch K} {F F' : Type u} [Field F] [Field F']
    [Algebra K F] [Algebra K F'] (e : F →ₐ[K] F') (p q : FPt X F)
    (h : RPt.map e p = RPt.map e q) : p = q := by
  apply Over.OverMorphism.ext
  have hleft : (specOfMap (K := K) e).left ≫ p.left =
      (specOfMap (K := K) e).left ≫ q.left := by
    have hh := congrArg Over.Hom.left h
    simpa [RPt.map, Over.comp_left] using hh
  have hE : Epi (Spec.map (CommRingCat.ofHom e.toRingHom)) := inferInstance
  haveI : Epi (specOfMap (K := K) e).left := by
    rw [specOfMap_left]
    exact hE
  exact (cancel_epi _).mp hleft

/-- `Ddeg` is invariant under linear equivalence: principal divisors have degree zero. -/
theorem ddeg_eq_of_linEquiv {F : Type u} [Field F] [Algebra K F] {A B : Dv C F}
    (h : LinEquiv C A B) : Ddeg C F A = Ddeg C F B := by
  obtain ⟨z, _hz, hdiv⟩ := h
  have h0 : Ddeg C F ((CurveBasics.Curve.baseChange C F).div z) = 0 :=
    CurveBasics.Order.deg_div (CurveBasics.Curve.baseChange C F) z
  have h1 : Ddeg C F (A - B) = 0 := by rw [← hdiv]; exact h0
  rw [map_sub, sub_eq_zero] at h1
  exact h1

/-- If `D` is effective and is the only effective divisor linearly equivalent to itself, then
`ℓ D = 1`: in that case the Riemann-Roch space `L D` is the line of constants.  This is the
direction of `Work.GCBasics.ell_eq_one_iff` that does not go through
`Work.GCBasics.linEquiv_eq_of_ell_eq_one`. -/
theorem ell_eq_one_of_unique {F : Type u} [Field F] [Algebra K F] (D : Dv C F)
    (hD : D.IsEffective)
    (huniq : ∀ D' : Dv C F, D'.IsEffective → LinEquiv C D D' → D = D') : ell C D = 1 := by
  set X : CurveBasics.Curve F := CurveBasics.Curve.baseChange C F with hX
  have hle : X.L D ≤ Submodule.span F ({1} : Set X.functionField) := by
    intro f hf
    rw [Submodule.mem_span_singleton]
    by_cases hf0 : f = 0
    · exact ⟨0, by rw [hf0]; simp⟩
    · have hE : (X.div f + D).IsEffective := by
        rcases (CurveBasics.Curve.mem_L_iff X).mp hf with h | h
        · exact absurd h hf0
        · exact h
      have hlin : LinEquiv C D (X.div f + D) := by
        refine ⟨f⁻¹, inv_ne_zero hf0, ?_⟩
        rw [CurveBasics.Order.div_inv X hf0]
        abel
      have hEq : D = X.div f + D := huniq _ hE hlin
      have hdiv0 : X.div f = 0 := by
        have h := congrArg (fun E : Dv C F => E - D) hEq
        simpa only [sub_self, add_sub_cancel_right] using h.symm
      obtain ⟨c, hc⟩ := (div_eq_zero_iff_isConstant X).mp hdiv0
      exact ⟨c, by rw [hc, Algebra.smul_def, mul_one]⟩
  have hge : Submodule.span F ({1} : Set X.functionField) ≤ X.L D := by
    rw [Submodule.span_le]
    rintro f (rfl : f = 1)
    rw [← map_one (algebraMap F X.functionField)]
    exact X.algebraMap_mem_L hD (1 : F)
  have hfin : Module.finrank F (X.L D) = 1 := by
    rw [le_antisymm hle hge, finrank_span_singleton (one_ne_zero)]
  exact hfin

/-- Adding `c` to the first and `d` to the second argument of a linear equivalence is the same
as subtracting `d` respectively `c`. -/
theorem linEquiv_add_iff_sub {F : Type u} [Field F] [Algebra K F] (a b c d : Dv C F) :
    LinEquiv C (a - d) (b - c) ↔ LinEquiv C (a + c) (b + d) := by
  rw [show (a - d : Dv C F) = (a + c) - (c + d) by abel,
    show (b - c : Dv C F) = (b + d) - (c + d) by abel]
  exact LinEquiv.sub_iff (a + c) (b + d) (c + d)

section

variable [D : Input C P0]

/-- `divOf` of a base-changed point: the bridge between `Work.GCBasics.RPt.map`, which is what
a caller writes, and `Work.SpecLin.RPt.map`, which is what `SymGeom.divOf_map` is stated with
(the two are definitionally equal, but not syntactically). -/
theorem divOf_map' (n : ℕ) {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') (p : FPt (D.Sym n) F) :
    D.divOf n (RPt.map e p) = SpecLin.DivBase.bc e (D.divOf n p) :=
  (D.symGeom n).divOf_map e p

/-- Base change of divisors is injective on effective divisors of a fixed degree: a point of
`Sym^n` is determined by its base change. -/
theorem bc_injective_effective (n : ℕ) [G : SpecLin.SymGeom C n] {F F' : Type u} [Field F]
    [Field F'] [Algebra K F] [Algebra K F'] (e : F →ₐ[K] F') {A B : Dv C F}
    (hA : A.IsEffective) (hB : B.IsEffective)
    (hdA : Ddeg C F A = (n : ℤ)) (hdB : Ddeg C F B = (n : ℤ))
    (h : SpecLin.DivBase.bc e A = SpecLin.DivBase.bc e B) : A = B := by
  obtain ⟨p, hp⟩ := G.divOf_complete A hA
    (by simpa only [Ddeg, CurveBasics.Curve.deg] using hdA)
  obtain ⟨q, hq⟩ := G.divOf_complete B hB
    (by simpa only [Ddeg, CurveBasics.Curve.deg] using hdB)
  have h2 : G.divOf (RPt.map e p) = G.divOf (RPt.map e q) := by
    have h1 : G.divOf (RPt.map e p) = SpecLin.DivBase.bc e (G.divOf p) := G.divOf_map e p
    have h1' : G.divOf (RPt.map e q) = SpecLin.DivBase.bc e (G.divOf q) := G.divOf_map e q
    rw [h1, h1', hp, hq, h]
  have h3 : RPt.map e p = RPt.map e q := G.divOf_injective _ _ h2
  have h4 : p = q := smap_injective (X := G.S) e p q h3
  rw [← hp, ← hq, h4]

/-- **Descent of `ℓ = 1` along a field extension**: if the base change of a degree-`g` divisor
has `ℓ = 1`, then so does the divisor itself. -/
theorem ell_eq_one_of_bc {F F' : Type u} [Field F] [Field F'] [Algebra K F] [Algebra K F']
    (e : F →ₐ[K] F') (A : Dv C F) (hd : Ddeg C F A = (D.g : ℤ))
    (h : ell C (SpecLin.DivBase.bc e A) = 1) : ell C A = 1 := by
  obtain ⟨A₀, hA₀eff, hA₀deg, hA₀lin⟩ := D.rr7 A (le_of_eq hd.symm)
  have hA₀dg : Ddeg C F A₀ = (D.g : ℤ) := hA₀deg.trans hd
  have hbc : ell C (SpecLin.DivBase.bc e A₀) = 1 := by
    rw [← ell_eq_of_linEquiv (SpecLin.DivBase.linEquiv_bc e hA₀lin)]
    exact h
  have hEff₀ : (SpecLin.DivBase.bc e A₀).IsEffective :=
    SpecLin.DivBase.isEffective_bc e hA₀eff
  have hA₀ : ell C A₀ = 1 := by
    refine ell_eq_one_of_unique A₀ hA₀eff ?_
    intro B hBeff hBlin
    have hBdg : Ddeg C F B = (D.g : ℤ) := (ddeg_eq_of_linEquiv hBlin).symm.trans hA₀dg
    have hbcB : SpecLin.DivBase.bc e A₀ = SpecLin.DivBase.bc e B :=
      linEquiv_eq_of_ell_eq_one hEff₀ hbc (SpecLin.DivBase.isEffective_bc e hBeff)
        (SpecLin.DivBase.linEquiv_bc e hBlin)
    exact bc_injective_effective D.g (G := D.symGeom D.g) e hA₀eff hBeff hA₀dg hBdg hbcB
  rw [ell_eq_of_linEquiv hA₀lin]
  exact hA₀

/-! ## The divisors appearing in the transition `σ i j` -/

/-- The residue field of the image point of a field point of a `K`-scheme, as a `K`-algebra. -/
abbrev resK {X : Sch K} {F : Type u} [Field F] [Algebra K F] (p : FPt X F) : Type u :=
  resField X (p.left (IsLocalRing.closedPoint F))

/-- The `F`-level divisor `divOf q + E j - E i`, whose `ℓ = 1` is precisely the class
condition of `InChart j (picOf i q)`. -/
abbrev AF (i j : D.Idx) {F : Type u} [Field F] [Algebra K F] (q : FPt (D.Sym D.g) F) : Dv C F :=
  D.divOf D.g q + bcKF F (D.EDiv j) - bcKF F (D.EDiv i)

/-- The `κ(x)`-level version of `AF`, for `x` the image point of `q`: this is the divisor
appearing in the DEFINED hypothesis of `σ i j`. -/
abbrev Aκ (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (D.Sym D.g) F) : Dv C (resK q) :=
  D.divOf D.g (resPt (D.Sym D.g) (q.left (IsLocalRing.closedPoint F)))
    + bcKF (resK q) (D.EDiv j) - bcKF (resK q) (D.EDiv i)

/-- `picOf` in terms of linear equivalence. -/
theorem picOf_eq_iff (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (a b : FPt (D.Sym D.g) F) :
    D.picOf i a = D.picOf j b ↔ LinEquiv C (D.divOf D.g a - D.divOf D.g (D.EF i))
      (D.divOf D.g b - D.divOf D.g (D.EF j)) := by
  rw [Input.picOf_def, Input.picOf_def]
  exact Pic0.mk_eq_iff _ _

/-- `picOf` in terms of linear equivalence, in the form in which `σ_value` produces it. -/
theorem picOf_eq_iff' (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (a b : FPt (D.Sym D.g) F) :
    D.picOf i a = D.picOf j b ↔ LinEquiv C (D.divOf D.g a + D.divOf D.g (D.EF j))
      (D.divOf D.g b + D.divOf D.g (D.EF i)) := by
  rw [picOf_eq_iff]
  exact linEquiv_add_iff_sub _ _ _ _

/-- A point of `V` has `ℓ = 1`. -/
theorem ell_of_landsIn_V {F : Type u} [Field F] [Algebra K F] (y : FPt (D.Sym D.g) F)
    (hy : RPt.LandsIn y D.V) : ell C (D.divOf D.g y) = 1 := by
  obtain ⟨y', hy', -⟩ := FPt.factor_of_landsIn D.V y hy
  rw [← hy']
  exact D.ell_eq_one_of_landsIn y'

/-! ## The value of `σ i j` at a field point -/

/-- The underlying point of the value of `σ i j` is the partial map applied to the (unique)
factorisation of the point through the domain. -/
theorem σVal_apply (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (D.Sym D.g) F) (h : RPt.LandsIn q (σ i j).domain) :
    (σVal i j q h).left (IsLocalRing.closedPoint F)
      = (σPM i j).hom ((Classical.choose
          (RPt.factor_of_closed_landsIn (σ i j).domain q h)).left
            (IsLocalRing.closedPoint F)) := by
  simp only [σVal, value]
  rfl

/-- The value of `σ i j` at a field point, computed with any factorisation of the point
through the domain. -/
theorem σVal_eq_of_factor (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (D.Sym D.g) F) (h : RPt.LandsIn q (σ i j).domain)
    (Q : FPt (Opens.toOver (σ i j).domain) F)
    (hQ : Q ≫ Opens.ιOver (σ i j).domain = q) :
    (σVal i j q h).left (IsLocalRing.closedPoint F)
      = (σPM i j).hom (Q.left (IsLocalRing.closedPoint F)) := by
  rw [σVal_apply]
  have huniq := (Classical.choose_spec
    (RPt.factor_of_closed_landsIn (σ i j).domain q h)).2
  have h' : Q.left (IsLocalRing.closedPoint F)
      = (Classical.choose (RPt.factor_of_closed_landsIn (σ i j).domain q h)).left
          (IsLocalRing.closedPoint F) :=
    congrArg (fun r : FPt (Opens.toOver (σ i j).domain) F =>
      r.left (IsLocalRing.closedPoint F)) (huniq Q hQ)
  rw [← h']

/-- The image in `Sym^g` of a point `Q` of the domain of `σ i j` is the image point of
`Q ≫ ιOver`; this is the identification used to pass between `W i j` and `σ`'s domain. -/
theorem domain_ι_apply_eq (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (D.Sym D.g) F)
    (Q : FPt (Opens.toOver (σ i j).domain) F)
    (hQ : Q ≫ Opens.ιOver (σ i j).domain = q) :
    (σPM i j).domain.ι (Q.left (IsLocalRing.closedPoint F))
      = q.left (IsLocalRing.closedPoint F) := by
  have h := congrArg Over.Hom.left hQ
  rw [Over.comp_left, Opens.ιOver_left] at h
  exact congrArg (fun g : (specOf K F).left ⟶ (D.Sym D.g).left =>
    g (IsLocalRing.closedPoint F)) h

/-- A point of `W i j` has its `σ i j`-value in `V`. -/
theorem σPM_hom_mem_V_of_landsIn_W (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (D.Sym D.g) F) (hqW : RPt.LandsIn q (W i j))
    (Q : FPt (Opens.toOver (σ i j).domain) F)
    (hQ : Q ≫ Opens.ιOver (σ i j).domain = q) :
    (σPM i j).hom (Q.left (IsLocalRing.closedPoint F)) ∈ D.V := by
  have hQι := domain_ι_apply_eq i j q Q hQ
  have hqmem : q.left (IsLocalRing.closedPoint F) ∈ (σPM i j).domain :=
    W_le_domain i j hqW
  have hι_inj : Function.Injective (σPM i j).domain.ι :=
    fun a b h => Subtype.val_injective h
  have hpt : Q.left (IsLocalRing.closedPoint F)
      = (⟨q.left (IsLocalRing.closedPoint F), hqmem⟩ : (σPM i j).domain) :=
    hι_inj (by rw [hQι, Scheme.Opens.ι_apply, Subtype.coe_mk])
  have hmem : (⟨q.left (IsLocalRing.closedPoint F), hqmem⟩ : (σPM i j).domain)
      ∈ (σPM i j).hom ⁻¹ᵁ D.V :=
    (Scheme.Opens.mem_ι_image_iff (U := (σPM i j).domain) (V := (σPM i j).hom ⁻¹ᵁ D.V)
      (x := (⟨q.left (IsLocalRing.closedPoint F), hqmem⟩ : (σPM i j).domain))).mp hqW
  rw [hpt]
  exact hmem

/-- Conversely, a point whose `σ i j`-value lies in `V` lands in `W i j`. -/
theorem landsIn_W_of_σPM_hom_mem_V (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (D.Sym D.g) F) (Q : FPt (Opens.toOver (σ i j).domain) F)
    (hQ : Q ≫ Opens.ιOver (σ i j).domain = q)
    (hV : (σPM i j).hom (Q.left (IsLocalRing.closedPoint F)) ∈ D.V) :
    RPt.LandsIn q (W i j) := by
  have hQι := domain_ι_apply_eq i j q Q hQ
  have hqmem : q.left (IsLocalRing.closedPoint F) ∈ (σPM i j).domain := by
    rw [← hQι]
    exact (Q.left (IsLocalRing.closedPoint F)).2
  have hι_inj : Function.Injective (σPM i j).domain.ι :=
    fun a b h => Subtype.val_injective h
  have hpt : (⟨q.left (IsLocalRing.closedPoint F), hqmem⟩ : (σPM i j).domain)
      = Q.left (IsLocalRing.closedPoint F) :=
    hι_inj (by rw [hQι, Scheme.Opens.ι_apply, Subtype.coe_mk])
  have hV' : (σPM i j).hom
      (⟨q.left (IsLocalRing.closedPoint F), hqmem⟩ : (σPM i j).domain) ∈ D.V := by
    rw [hpt]
    exact hV
  have hmem : (⟨q.left (IsLocalRing.closedPoint F), hqmem⟩ : (σPM i j).domain)
      ∈ (σPM i j).hom ⁻¹ᵁ D.V :=
    (Scheme.Hom.mem_preimage (f := (σPM i j).hom)
      (x := (⟨q.left (IsLocalRing.closedPoint F), hqmem⟩ : (σPM i j).domain))
      (U := D.V)).mpr hV'
  exact (Scheme.Opens.mem_ι_image_iff (U := (σPM i j).domain)
    (V := (σPM i j).hom ⁻¹ᵁ D.V)
    (x := (⟨q.left (IsLocalRing.closedPoint F), hqmem⟩ : (σPM i j).domain))).mpr hmem

end

end

end Work.GroupChunk
