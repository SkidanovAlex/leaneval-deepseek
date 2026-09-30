import Mathlib
import Submission.Work.GroupChunk.Glue
import Submission.Work.GroupChunk.landsIn_U_iff
import Submission.Work.GroupChunk.U_self
import Submission.Work.GroupChunk.sigmaOnW_value
import Submission.Work.GroupChunk.exists_factor_resPt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


/-!
# Area GC — the transition morphisms as actual morphisms

The transition `tr i j` from the `i`-th to the `j`-th chart, its inverse law (`tr_self` and the
`tpq_inv` pointwise inverse), and the elementary glue lemmas for open subschemes of `Sym^g C`
used by the gluing.
-/

set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory AlgebraicGeometry
open scoped Classical AlgebraicGeometry MonoidalCategory
open scoped Work.GCBasics

universe u

namespace Work.GroupChunk

noncomputable section

open Work.GCBasics

variable {K : Type u} [Field K]
variable {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]
  [D : Input C P0]


variable {K : Type u} [Field K]

/-! ## Glue lemmas for open subschemes -/

/-- The range of a morphism into an open subscheme is contained in it if and only if all the
canonical residue-field points of the source land in it. -/
theorem range_subset_iff_landsIn {X Y : Sch K} (f : Y ⟶ X) (U : X.left.Opens) :
    Set.range f.left ⊆ (U : Set X.left) ↔
      ∀ y : Y.left, RPt.LandsIn (resPt Y y ≫ f) U := by
  constructor
  · intro h y
    have h1 : f.left y ∈ (U : Set X.left) := h ⟨y, rfl⟩
    show (Over.Hom.left (resPt Y y ≫ f)) (IsLocalRing.closedPoint (resField Y y)) ∈ (U : Set X.left)
    have h2 : (Over.Hom.left (resPt Y y ≫ f)) (IsLocalRing.closedPoint (resField Y y))
        = (Over.Hom.left f) ((Over.Hom.left (resPt Y y)) (IsLocalRing.closedPoint (resField Y y))) :=
      Scheme.Hom.comp_apply _ _ _
    have h3 : (Over.Hom.left (resPt Y y)) (IsLocalRing.closedPoint (resField Y y)) = y :=
      resPt_apply Y y _
    rw [h2, h3]
    exact h1
  · intro h x hx
    obtain ⟨y, rfl⟩ := hx
    have h1 : (Over.Hom.left (resPt Y y ≫ f)) (IsLocalRing.closedPoint (resField Y y))
        ∈ (U : Set X.left) := h y
    have h2 : (Over.Hom.left (resPt Y y ≫ f)) (IsLocalRing.closedPoint (resField Y y))
        = (Over.Hom.left f) ((Over.Hom.left (resPt Y y)) (IsLocalRing.closedPoint (resField Y y))) :=
      Scheme.Hom.comp_apply _ _ _
    have h3 : (Over.Hom.left (resPt Y y)) (IsLocalRing.closedPoint (resField Y y)) = y :=
      resPt_apply Y y _
    rw [h2, h3] at h1
    exact h1

/-- **A morphism whose range is contained in an open subscheme factors through it**,
uniquely.  Scheme-level version of `RPt.factor_of_closed_landsIn`. -/
theorem exists_factor_of_range_subset {X Y : Sch K} (U : X.left.Opens) (f : Y ⟶ X)
    (h : Set.range f.left ⊆ (U : Set X.left)) :
    ∃! g : Y ⟶ Opens.toOver U, g ≫ Opens.ιOver U = f := by
  have hle : Set.range f.left ⊆ Set.range U.ι := by
    rw [Scheme.Opens.range_ι]; exact h
  let g0 := IsOpenImmersion.lift U.ι f.left hle
  have hg0 : g0 ≫ U.ι = f.left := IsOpenImmersion.lift_fac U.ι f.left hle
  have hw : g0 ≫ (Opens.toOver U).hom = Y.hom := by
    change g0 ≫ U.ι ≫ X.hom = Y.hom
    rw [← Category.assoc, hg0]
    exact Over.w f
  refine ⟨Over.homMk g0 hw, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    rw [Over.comp_left]
    exact hg0
  · intro g hg
    apply Over.OverMorphism.ext
    have hg' : g.left ≫ U.ι = f.left := by
      have h1 := congrArg Over.Hom.left hg
      simpa [Over.comp_left, Opens.ιOver_left] using h1
    exact IsOpenImmersion.lift_uniq U.ι f.left hle g.left hg'

/-- `Opens.ιOver U` is a monomorphism. -/
theorem mono_ιOver {X : Sch K} (U : X.left.Opens) : Mono (Opens.ιOver U) :=
  Over.mono_of_mono_left _

instance instMono_ιOver {X : Sch K} (U : X.left.Opens) : Mono (Opens.ιOver U) :=
  mono_ιOver U

/-- An `F`-point of `Opens.toOver U` lands in `U` after including into the ambient scheme. -/
theorem landsIn_ιOver_self {X : Sch K} (U : X.left.Opens) {F : Type u} [Field F]
    [Algebra K F] (q : FPt (Opens.toOver U) F) : RPt.LandsIn (q ≫ Opens.ιOver U) U := by
  show (Over.Hom.left (Opens.ιOver U)) ((Over.Hom.left q) (IsLocalRing.closedPoint F))
    ∈ (U : Set X.left)
  have h2 : (Over.Hom.left (Opens.ιOver U)) = U.ι := rfl
  rw [h2]
  exact (Scheme.Opens.range_ι U).le (Set.mem_range_self _)

/-! ## The chart datum -/

variable {C : CurveBasics.Curve K} {P0 : 𝟙_ (Sch K) ⟶ C.toOver} [SpecLin.DivBase C]
  [D : Input C P0]



instance instIsReducedV : IsReduced (Opens.toOver D.V).left :=
  isReduced_of_isOpenImmersion D.V.ι

instance instIsReducedU (i j : D.Idx) : IsReduced (Opens.toOver (U i j)).left :=
  isReduced_of_isOpenImmersion (U i j).ι

instance instIsSeparatedV : IsSeparated (Opens.toOver D.V).hom := by
  change IsSeparated (D.V.ι ≫ (D.Sym D.g).hom)
  exact MorphismProperty.IsStableUnderComposition.comp_mem _ _ (by infer_instance)
    (by haveI := D.isProper_Sym D.g; infer_instance)

instance instIsSeparatedU (i j : D.Idx) : IsSeparated (Opens.toOver (U i j)).hom := by
  change IsSeparated ((U i j).ι ≫ (Opens.toOver D.V).hom)
  exact MorphismProperty.IsStableUnderComposition.comp_mem _ _ (by infer_instance)
    (instIsSeparatedV (D := D))

theorem Uι_def (i j : D.Idx) : Uι i j = Opens.ιOver (U i j) ≫ Opens.ιOver D.V := rfl

/-! ## `tHom` and its class -/

theorem UToW_ιOver (i j : D.Idx) : UToW i j ≫ Opens.ιOver (W i j) = Uι i j := by
  apply Over.OverMorphism.ext
  show IsOpenImmersion.lift (W i j).ι (Uι i j).left _ ≫ (W i j).ι = (Uι i j).left
  rw [IsOpenImmersion.lift_fac]

theorem range_σOnW_le_V (i j : D.Idx) : Set.range (σOnW i j).left ⊆ (D.V : Set _) := by
  have hpre : (Scheme.homOfLE (D.Sym D.g).left (W_le_domain i j)
      ≫ (σPM i j).hom) ⁻¹ᵁ D.V = ⊤ := by
    have hS : (σPM i j).hom ⁻¹ᵁ D.V = (σPM i j).domain.ι ⁻¹ᵁ W i j := by
      rw [W]
      exact (Scheme.Hom.preimage_image_eq (σPM i j).domain.ι _).symm
    rw [Scheme.Hom.comp_preimage, hS, ← Scheme.Hom.comp_preimage, Scheme.homOfLE_ι,
      Scheme.Opens.ι_preimage_self]
  rintro z ⟨w, rfl⟩
  have h1 : w ∈ (Scheme.homOfLE (D.Sym D.g).left (W_le_domain i j)
      ≫ (σPM i j).hom) ⁻¹ᵁ D.V := by
    rw [hpre]; exact trivial
  exact h1

theorem tHom_range (i j : D.Idx) : Set.range (tHom i j).left ⊆ (D.V : Set _) := by
  rw [show (tHom i j).left = (UToW i j).left ≫ (σOnW i j).left from rfl]
  rintro z ⟨y, rfl⟩
  exact range_σOnW_le_V i j ⟨(UToW i j).left y, rfl⟩

theorem σVal_eq_of_point_eq (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    {p p' : FPt (D.Sym D.g) F} (h : p = p')
    (hp : RPt.LandsIn p (σ i j).domain) (hp' : RPt.LandsIn p' (σ i j).domain) :
    σVal i j p hp = σVal i j p' hp' := by
  subst h
  exact congrArg (fun hh => σVal i j p hh) (Subsingleton.elim hp hp')

theorem tHom_eq_σVal (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (Opens.toOver (U i j)) F)
    (hq : RPt.LandsIn (q ≫ Uι i j) (σ i j).domain) :
    q ≫ tHom i j = σVal i j (q ≫ Uι i j) hq := by
  have hU := UToW_ιOver i j
  have hX : ((q ≫ UToW i j) ≫ Opens.ιOver (W i j)) = (q ≫ Uι i j) := by
    rw [Category.assoc, hU]
  have hqX : RPt.LandsIn ((q ≫ UToW i j) ≫ Opens.ιOver (W i j)) (σ i j).domain := by
    rw [hX]; exact hq
  have h := sigmaOnW_value i j (q ≫ UToW i j) hqX
  rw [show q ≫ tHom i j = (q ≫ UToW i j) ≫ σOnW i j from rfl]
  rw [h]
  exact σVal_eq_of_point_eq i j hX hqX hq

theorem landsIn_W_self (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (Opens.toOver (U i j)) F) : RPt.LandsIn (q ≫ Uι i j) (W i j) :=
  range_Uι_le_W i j ⟨q.left (IsLocalRing.closedPoint F), rfl⟩

theorem tHom_picOf (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (Opens.toOver (U i j)) F) :
    D.picOf j (q ≫ tHom i j) = D.picOf i (q ≫ Uι i j) := by
  have hYX : ((q ≫ UToW i j) ≫ Opens.ιOver (W i j)) = (q ≫ Uι i j) := by
    rw [Category.assoc, UToW_ιOver i j]
  have hqX : RPt.LandsIn ((q ≫ UToW i j) ≫ Opens.ιOver (W i j)) (σ i j).domain := by
    rw [hYX]; exact W_le_domain i j (landsIn_W_self i j q)
  have hval := σ_value i j ((q ≫ UToW i j) ≫ Opens.ιOver (W i j)) hqX
  have hT : q ≫ tHom i j
      = σVal i j ((q ≫ UToW i j) ≫ Opens.ιOver (W i j)) hqX := by
    rw [show q ≫ tHom i j = (q ≫ UToW i j) ≫ σOnW i j from rfl]
    exact sigmaOnW_value i j (q ≫ UToW i j) hqX
  have hfin : D.picOf j (σVal i j ((q ≫ UToW i j) ≫ Opens.ιOver (W i j)) hqX)
      = D.picOf i ((q ≫ UToW i j) ≫ Opens.ιOver (W i j)) :=
    (picOf_eq_iff' j i _ _).mpr (by simpa only [← Input.EF_divOf] using hval)
  have hlast : D.picOf i ((q ≫ UToW i j) ≫ Opens.ιOver (W i j)) = D.picOf i (q ≫ Uι i j) := by
    rw [hYX]
  rw [hT, hfin, hlast]

/-! ## `picOf` is injective on the chart -/

abbrev picOfV (l : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Opens.toOver D.V) F) : Pic0 C F :=
  D.picOf l (p ≫ Opens.ιOver D.V)

theorem landsIn_V_ιOver {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Opens.toOver D.V) F) : RPt.LandsIn (p ≫ Opens.ιOver D.V) D.V := by
  show (Over.Hom.left (Opens.ιOver D.V)) ((Over.Hom.left p) (IsLocalRing.closedPoint F))
    ∈ (D.V : Set _)
  exact (Scheme.Opens.range_ι D.V).le
    (Set.mem_range_self ((Over.Hom.left p) (IsLocalRing.closedPoint F)))

/-- **`picOf` is injective on the chart**: two points of `V` with the same class with respect
to the same centre are equal (because `ℓ = 1` on `V`). -/
theorem picOf_inj_V (l : D.Idx) {F : Type u} [Field F] [Algebra K F]
    {p q : FPt (Opens.toOver D.V) F} (h : picOfV (D := D) l p = picOfV (D := D) l q) :
    p = q := by
  have hlin : LinEquiv C (D.divOf D.g (p ≫ Opens.ιOver D.V) - D.divOf D.g (D.EF l))
      (D.divOf D.g (q ≫ Opens.ιOver D.V) - D.divOf D.g (D.EF l)) :=
    (picOf_eq_iff l l _ _).mp h
  have hlin2 : LinEquiv C (D.divOf D.g (p ≫ Opens.ιOver D.V))
      (D.divOf D.g (q ≫ Opens.ιOver D.V)) :=
    (LinEquiv.sub_iff _ _ _).mp hlin
  have hell : ell C (D.divOf D.g (p ≫ Opens.ιOver D.V)) = 1 :=
    ell_of_landsIn_V _ (landsIn_V_ιOver p)
  have hdiv : D.divOf D.g (p ≫ Opens.ιOver D.V) = D.divOf D.g (q ≫ Opens.ιOver D.V) :=
    linEquiv_eq_of_ell_eq_one ((D.symGeom D.g).divOf_isEffective (p ≫ Opens.ιOver D.V)) hell
      ((D.symGeom D.g).divOf_isEffective (q ≫ Opens.ιOver D.V)) hlin2
  have hpq : p ≫ Opens.ιOver D.V = q ≫ Opens.ιOver D.V :=
    (D.symGeom D.g).divOf_injective _ _ hdiv
  exact (cancel_mono (Opens.ιOver D.V)).mp hpq

/-! ## The transition as a map into the chart -/

/-- The transition `tq i j : U i j ⟶ V`, the value of the RESID map `σ i j` on `U i j`. -/
def tq (i j : D.Idx) : Opens.toOver (U i j) ⟶ Opens.toOver D.V :=
  Classical.choose (exists_factor_of_range_subset D.V (tHom i j) (tHom_range i j))

theorem tq_ιOver (i j : D.Idx) : tq i j ≫ Opens.ιOver D.V = tHom i j :=
  (Classical.choose_spec (exists_factor_of_range_subset D.V (tHom i j) (tHom_range i j))).1

theorem tq_picOf (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (Opens.toOver (U i j)) F) :
    D.picOf j (q ≫ tq i j ≫ Opens.ιOver D.V) = D.picOf i (q ≫ Uι i j) := by
  rw [tq_ιOver]
  exact tHom_picOf i j q

/-- **The transition applied to a point of the chart `V`**: if `p` factors through `U i j`,
`tpq i j p` is the value of `tq i j` at that factor.  (If `p` does not factor, `tpq i j p`
is defined to be `p`; every statement below assumes the factorisation.) -/
def tpq (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Opens.toOver D.V) F) : FPt (Opens.toOver D.V) F :=
  if h : ∃ q : FPt (Opens.toOver (U i j)) F, q ≫ Opens.ιOver (U i j) = p
  then (Classical.choose h) ≫ tq i j
  else p

theorem tpq_eq_of_lift (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Opens.toOver D.V) F) (q : FPt (Opens.toOver (U i j)) F)
    (hq : q ≫ Opens.ιOver (U i j) = p) : tpq i j p = q ≫ tq i j := by
  have h0 : ∃ q' : FPt (Opens.toOver (U i j)) F, q' ≫ Opens.ιOver (U i j) = p := ⟨q, hq⟩
  unfold tpq
  rw [dif_pos h0]
  congr 1
  exact (cancel_mono (Opens.ιOver (U i j))).mp ((Classical.choose_spec h0).trans hq.symm)

/-- The class of `tpq i j p` with respect to `E j` is the class of `p` with respect to `E i`. -/
theorem tpq_picOfV (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Opens.toOver D.V) F) (hp : RPt.LandsIn p (U i j)) :
    picOfV (D := D) j (tpq i j p) = picOfV (D := D) i p := by
  obtain ⟨q, hq, -⟩ := FPt.factor_of_landsIn (U i j) p hp
  have h1 : tpq i j p ≫ Opens.ιOver D.V = q ≫ tq i j ≫ Opens.ιOver D.V := by
    rw [tpq_eq_of_lift i j p q hq, Category.assoc]
  show D.picOf j (tpq i j p ≫ Opens.ιOver D.V) = D.picOf i (p ≫ Opens.ιOver D.V)
  rw [h1, tq_picOf i j q, Uι_def, ← Category.assoc, hq]

/-- **`tq i j` maps `U i j ⊓ U i k` into `U j k`.** -/
theorem tpq_landsIn (i j k : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Opens.toOver D.V) F) (hp : RPt.LandsIn p (U i j))
    (hpk : RPt.LandsIn p (U i k)) : RPt.LandsIn (tpq i j p) (U j k) := by
  refine (landsIn_U_iff j k (tpq i j p)).mpr ?_
  obtain ⟨y, hyV, hycls⟩ := (landsIn_U_iff i k p).mp hpk
  exact ⟨y, hyV, hycls.trans (tpq_picOfV i j p hp).symm⟩

/-- **Composition of transitions**: from `i` via `j` and then `k` is the same as from `i`
via `k`. -/
theorem tpq_comp (i j k : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Opens.toOver D.V) F) (hp : RPt.LandsIn p (U i j))
    (hpk : RPt.LandsIn p (U i k)) (h : RPt.LandsIn (tpq i j p) (U j k)) :
    tpq j k (tpq i j p) = tpq i k p :=
  picOf_inj_V k (by
    rw [tpq_picOfV j k (tpq i j p) h, tpq_picOfV i j p hp, tpq_picOfV i k p hpk])

/-- The transition is the identity on `U i i`. -/
theorem tpq_self (i : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Opens.toOver D.V) F) (hp : RPt.LandsIn p (U i i)) : tpq i i p = p :=
  picOf_inj_V i (tpq_picOfV i i p hp)

/-- **The result of the transition is the base point**: `tpq i j (tpq j i p) = p`. -/
theorem tpq_inv (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (p : FPt (Opens.toOver D.V) F) (hp : RPt.LandsIn p (U i j))
    (h : RPt.LandsIn (tpq i j p) (U j i)) : tpq j i (tpq i j p) = p := by
  have hpii : RPt.LandsIn p (U i i) := by
    rw [U_self i]
    exact RPt.landsIn_top p
  have h1 := tpq_comp (D := D) i j i p hp hpii h
  rw [tpq_self i p hpii] at h1
  exact h1

/-- **The range of `tq i j` is contained in the transition domain `U j i`.** -/
theorem tq_range (i j : D.Idx) : Set.range (tq i j).left ⊆ (U j i : Set _) := by
  rw [range_subset_iff_landsIn]
  intro x
  let F : Type u := resField (Opens.toOver (U i j)) x
  set e : FPt (Opens.toOver (U i j)) F := resPt (Opens.toOver (U i j)) x with he
  have hp : RPt.LandsIn (e ≫ Opens.ιOver (U i j)) (U i j) := landsIn_ιOver_self (U i j) e
  have hk : RPt.LandsIn (e ≫ Opens.ιOver (U i j)) (U i i) := by
    rw [U_self i]
    exact RPt.landsIn_top (e ≫ Opens.ιOver (U i j))
  have h1 := tpq_landsIn (D := D) i j i (e ≫ Opens.ιOver (U i j)) hp hk
  rw [tpq_eq_of_lift i j (e ≫ Opens.ιOver (U i j)) e rfl] at h1
  exact h1


/-! ## The transition morphism `tr i j : U i j ⟶ U j i` -/

/-- The transition `tr i j`, the restriction of the RESID map `σ i j` to the transition
domain `U i j`. -/
def tr (i j : D.Idx) : Opens.toOver (U i j) ⟶ Opens.toOver (U j i) :=
  Classical.choose (exists_factor_of_range_subset (U j i) (tq i j) (tq_range i j))

theorem tr_ιOver (i j : D.Idx) : tr i j ≫ Opens.ιOver (U j i) = tq i j :=
  (Classical.choose_spec (exists_factor_of_range_subset (U j i) (tq i j) (tq_range i j))).1

theorem tr_ι (i j : D.Idx) : tr i j ≫ Uι j i = tHom i j := by
  rw [Uι_def, ← Category.assoc, tr_ιOver, tq_ιOver]

/-- The transition preserves the divisor class. -/
theorem tr_cls (i j : D.Idx) {F : Type u} [Field F] [Algebra K F]
    (q : FPt (Opens.toOver (U i j)) F) :
    D.picOf j (q ≫ tr i j ≫ Uι j i) = D.picOf i (q ≫ Uι i j) := by
  rw [tr_ι]
  exact tHom_picOf i j q

/-- `tHom i i = Uι i i`: on the diagonal the transition map is the identity. -/
theorem tHom_self (i : D.Idx) : tHom i i = Uι i i := by
  apply hom_ext_of_resPt (X := Opens.toOver (U i i)) (Y := D.Sym D.g)
  intro x
  let F : Type u := resField (Opens.toOver (U i i)) x
  set q : FPt (Opens.toOver (U i i)) F := resPt (Opens.toOver (U i i)) x with hqdef
  have hdom : RPt.LandsIn (q ≫ Uι i i) (σ i i).domain :=
    W_le_domain i i (landsIn_W_self i i q)
  have h1 : q ≫ tHom i i = σVal i i (q ≫ Uι i i) hdom := tHom_eq_σVal i i q hdom
  have hval : LinEquiv C (D.divOf D.g (σVal i i (q ≫ Uι i i) hdom))
      (D.divOf D.g (q ≫ Uι i i)) :=
    (LinEquiv.add_iff _ _ _).mp (σ_value i i (q ≫ Uι i i) hdom)
  have hell : ell C (D.divOf D.g (q ≫ Uι i i)) = 1 := by
    have hy : RPt.LandsIn (q ≫ Uι i i) D.V := by
      rw [Uι_def]
      exact landsIn_V_ιOver (q ≫ Opens.ιOver (U i i))
    exact ell_of_landsIn_V (q ≫ Uι i i) hy
  have hell' : ell C (D.divOf D.g (σVal i i (q ≫ Uι i i) hdom)) = 1 :=
    (ell_eq_of_linEquiv hval).trans hell
  have hdiv : D.divOf D.g (σVal i i (q ≫ Uι i i) hdom) = D.divOf D.g (q ≫ Uι i i) :=
    linEquiv_eq_of_ell_eq_one ((D.symGeom D.g).divOf_isEffective (σVal i i (q ≫ Uι i i) hdom)) hell'
      ((D.symGeom D.g).divOf_isEffective (q ≫ Uι i i)) hval
  have hpt : σVal i i (q ≫ Uι i i) hdom = q ≫ Uι i i :=
    (D.symGeom D.g).divOf_injective _ _ hdiv
  rw [h1, hpt]

theorem tq_self (i : D.Idx) : tq i i = Opens.ιOver (U i i) := by
  apply (cancel_mono (Opens.ιOver D.V)).mp
  rw [tq_ιOver, tHom_self, Uι_def]

theorem tr_self (i : D.Idx) : tr i i = 𝟙 (Opens.toOver (U i i)) := by
  apply (cancel_mono (Opens.ιOver (U i i))).mp
  rw [tr_ιOver, tq_self, Category.id_comp]

/-- The structure map of `Opens.toOver (U i i)` is an isomorphism, because `U i i = ⊤`. -/
theorem isIso_ιOver_self (i : D.Idx) : IsIso (Opens.ιOver (U i i)) := by
  rw [U_self i]
  refine IsIso.mk' ⟨Over.homMk (((Opens.toOver D.V).left.topIso)).inv ?_, ?_, ?_⟩
  · change ((Opens.toOver D.V).left.topIso).inv ≫ (⊤ : (Opens.toOver D.V).left.Opens).ι
        ≫ (Opens.toOver D.V).hom = (Opens.toOver D.V).hom
    rw [← Category.assoc, Scheme.toIso_inv_ι, Category.id_comp]
  · apply Over.OverMorphism.ext
    exact Scheme.toIso_inv_ι (Opens.toOver D.V).left
  · apply Over.OverMorphism.ext
    exact Scheme.ι_toIso_inv (Opens.toOver D.V).left
end

end Work.GroupChunk
