import Mathlib
import Submission.Work.CY3Stab.Prod.exDiv_prodMap_eq
import Submission.Work.CY3Stab.Prod.prodMap_symm
import Submission.Work.CY3Stab.Prod.resEquiv_prodPt_of_resEquiv
import Submission.Work.CY3Stab.Prod.isDomain_cylTriplet_tensor
import Submission.Work.CY3Stab.ProdCoeff
import Submission.Work.CY3Stab.Prod.exists_bijection_of_ncard_of_resEquiv
import Submission.Work.CY3Stab.Prod.wgt_image_eq_of_bijection
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

/-!
# `Work.CY3Stab.Prod.cInv_prodMap_eq_zero_of_strong` — the stabilisation step, and why the
requested statement needs its cylinder structures pinned

## The mathematical content

`cInv 𝕜 z ψ = excCount 𝕜 z ψ.symm - excCount 𝕜 z ψ` counts the exceptional divisors of `ψ` whose
residue field is `𝕜`-isomorphic to `κ(z)`.  The stabilisation step of Lin–Shinder's proof of
`thm:bir-generation` (c) is: *if all coefficients of `c(φ)` vanish then so do all coefficients of
`c(φ × id_{𝔸ᵏ})`*.  The reason is that `exDiv (φ × id_{𝔸ᵏ})` is the image of `exDiv φ` under the
cylinder-point map `x ↦ prodPt X x k`
(`Work.CY3Stab.Prod.exDiv_prodMap_eq`), and this map is class-preserving on structured residue
fields: `ResEquiv 𝕜 x y → ResEquiv 𝕜 (prodPt X x k) (prodPt Y y k)`
(`Work.CY3Stab.Prod.resEquiv_prodPt_of_resEquiv`).  Hence the *multiset of classes* of
`exDiv (φ × id)` is the image, under the class map `[κ] ↦ [κ(t₁,…,t_k)]`, of that of `exDiv φ`;
and the hypothesis `h` (all coefficients of `c(φ)` vanish) says precisely that the class multisets
of `exDiv φ` and `exDiv φ.symm` agree, so their images agree and all coefficients of `c(φ × id)`
vanish.  This needs **no** cylinder rigidity (unlike `Work.CY3Stab.cInv_prodMap_eq`, which
compares coefficients at a *cylinder* base point and needs the unproved `hR`).

## The defect of `cInv_prodMap_eq_zero_of_strong` as written

The requested statement takes the `Variety`-structures on the cylinders as *arbitrary* instance
binders, `[Variety 𝕜 (WProd X k)]`, `[Variety 𝕜 (WProd Y k)]`, but `cInv` depends on them: it is
built from `ResEquiv 𝕜 p z = ∃ e : κ(p) ≃+* κ(z), e ∘ resMap 𝕜 P p = resMap 𝕜 Z z`, and
`resMap 𝕜 P p` is defined from the *chosen* structure morphism `(P ↘ Spec 𝕜)` of the instance.  The
intended proof uses `Work.CY3Stab.Prod.resEquiv_prodPt_of_resEquiv`, whose conclusion is phrased
with the structure morphism found by instance search (`pullback.snd ≫ …`, equal to
`Work.CY3Stab.wProdOver …` by `pullback.condition`) — exactly the issue handled by *pinning* in
`exists_cInv_ne_zero_of_CY3Data.lean` and in the note "A note on the `Over`-structure of the
cylinder" of `stablyBirational_of_resEquiv_cyl_of_p1Bundle.lean`.

**The unpinned statement is false.**  Counterexample: let `𝕜 := ℚ(√2)`, `σ` the nontrivial
automorphism (`√2 ↦ -√2`), `X := Y := 𝔸²_𝕜` with the canonical structures, and
`φ := (s,u) ↦ (s, u + 1/(s² - √2))` — a birational map over `𝕜` whose exceptional divisors in both
directions are the generic point `x` of `D := V(s² - √2) ⊂ 𝔸²`, so that
`exDiv φ = exDiv φ.symm = {x}` and the hypothesis `h` holds (with `X = Y` and the same structures,
the two counts in `cInv 𝕜 z φ` are the same number).  Here `κ(x) = ℚ(2^{1/4})(u)` with the
canonical structure `incl`.  Install the structure found by instance search on `𝔸ᵏ × X`, and on
`𝔸ᵏ × Y` the *σ-twist* `c ↦ c ≫ Spec(σ)`: this is a legitimate `Variety`-structure (`IsIntegral`
is structure-free, `Spec(σ)` is an automorphism of the base, and
`IsSeparated (f ≫ Spec σ) ↔ IsSeparated f` by Mathlib's `IsSeparated.comp_iff`, likewise
`LocallyOfFiniteType` and `QuasiCompact`), and it changes `resMap` by σ.  Take `k = 0`, the test
scheme `𝔸ᵏ × X` with the canonical structure and `z := prodPt X x k`.  Then
`excCount 𝕜 z (prodMap k φ) = 1` (reflexivity of `ResEquiv`), while
`excCount 𝕜 z ((prodMap k φ).symm) = 0`: an isomorphism `e : κ(x) ≅ κ(x)` with
`e ∘ incl ∘ σ = incl` would satisfy `e(√2) = -√2`, whence `(e(2^{1/4})/2^{1/4})² = -1`, i.e. `-1`
would be a square in `ℚ(2^{1/4})(u)` — impossible (`p² = -q²` in `ℚ(2^{1/4})[u]` forces
`(lead p / lead q)² = -1` in `ℚ(2^{1/4}) ⊂ ℝ`).  So `cInv 𝕜 z (prodMap k φ) = 0 - 1 = -1 ≠ 0`
while all hypotheses of the unpinned statement hold.

## The repair, proved below

`Work.CY3Stab.Prod.cInv_prodMap_eq_zero_of_canonical` is the same statement with two pinning
hypotheses `hPX`, `hPY` (the cylinder structure morphisms are the canonical ones).  They are
dischargeable at any call site that installs the cylinder `Variety`-structure with
`over := Work.CY3Stab.wProdOver …` (as `exists_cInv_ne_zero_of_CY3Data.lean` does, via
`pullback.condition`).  The proof is the argument of the first section:
`Work.CY3Stab.Prod.exists_bijection_of_ncard_of_resEquiv` (class partition of `exDiv φ` and
`exDiv φ.symm` from `h`), the `exDiv` images (`exDiv_prodMap_eq`, `prodMap_symm`),
`resEquiv_prodPt_of_resEquiv` for the cylinder points, and
`Work.CY3Stab.Prod.wgt_image_eq_of_bijection` for the two `excCount`s.  The pinning enters only
through `Work.CY3Stab.Prod.cInv_congr_over_hom` (transport of `cInv` along an equality of structure
morphisms) between the pinned structure and the explicit cylinder structure
`Work.CY3Stab.Prod.cylOver` found by instance search.

The unpinned statement (with arbitrary `Variety`-structures on the cylinders) is **not** proved
here and is **not** provable — that is the point of the counterexample above; the pinned form
`cInv_prodMap_eq_zero_of_canonical` is the repair, and it is what the consumers use.  The residual
of the chapter (`Work.CY3Stab.ProdStab`, `Submission/Work/CY3Stab/Defs.lean`) is stated with its
cylinder structure pinned for exactly this reason.
-/

namespace Work.CY3Stab.Prod

noncomputable abbrev cylOver {𝕜 : Type} [Field 𝕜] (X : AlgebraicGeometry.Scheme.{0})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] (k : ℕ) :
    (Work.CY3Stab.WProd (𝕜 := 𝕜) X k).Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) :=
  inferInstance

theorem cylOver_hom_eq_wProdOver {𝕜 : Type} [Field 𝕜] (X : AlgebraicGeometry.Scheme.{0})
    [X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] (k : ℕ) :
    (cylOver (𝕜 := 𝕜) X k).hom = (Work.CY3Stab.wProdOver (𝕜 := 𝕜) X k).1 := by
  show pullback.snd (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝕜))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) ≫ (X ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝕜))
    = pullback.fst (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝕜))
      (X ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) ≫
        (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝕜))
  exact pullback.condition.symm

theorem resEquiv_congr_over_hom {𝕜 : Type} [Field 𝕜]
    {X Z : AlgebraicGeometry.Scheme.{0}}
    (oX oX' : X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
    (oZ oZ' : Z.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
    (hX : oX'.hom = oX.hom) (hZ : oZ'.hom = oZ.hom) (x : X) (z : Z) :
    @ResEquiv 𝕜 _ X Z oX oZ x z ↔ @ResEquiv 𝕜 _ X Z oX' oZ' x z := by
  have h1 : oX' = oX := congrArg OverClass.ofHom hX
  have h2 : oZ' = oZ := congrArg OverClass.ofHom hZ
  rw [h1, h2]

theorem cInv_congr_over_hom {𝕜 : Type} [Field 𝕜]
    {X Y Z : AlgebraicGeometry.Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (oX oX' : X.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
    (oY oY' : Y.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
    (oZ : Z.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)))
    (hX : oX'.hom = oX.hom) (hY : oY'.hom = oY.hom) (z : Z) (φ : X.BirationalMap Y) :
    @cInv 𝕜 _ X Y Z _ _ oX oY oZ z φ = @cInv 𝕜 _ X Y Z _ _ oX' oY' oZ z φ := by
  have hX' : @excCount 𝕜 _ X Y Z _ _ oX oZ z φ = @excCount 𝕜 _ X Y Z _ _ oX' oZ z φ := by
    simp only [excCount]
    congr 1
    ext w
    exact ⟨fun hw => ⟨hw.1, (resEquiv_congr_over_hom oX oX' oZ oZ hX rfl w z).mp hw.2⟩,
      fun hw => ⟨hw.1, (resEquiv_congr_over_hom oX oX' oZ oZ hX rfl w z).mpr hw.2⟩⟩
  have hY' : @excCount 𝕜 _ Y X Z _ _ oY oZ z φ.symm =
      @excCount 𝕜 _ Y X Z _ _ oY' oZ z φ.symm := by
    simp only [excCount]
    congr 1
    ext w
    exact ⟨fun hw => ⟨hw.1, (resEquiv_congr_over_hom oY oY' oZ oZ hY rfl w z).mp hw.2⟩,
      fun hw => ⟨hw.1, (resEquiv_congr_over_hom oY oY' oZ oZ hY rfl w z).mpr hw.2⟩⟩
  show ((@excCount 𝕜 _ Y X Z _ _ oY oZ z φ.symm : ℕ) : ℤ) - (@excCount 𝕜 _ X Y Z _ _ oX oZ z φ : ℕ)
    = ((@excCount 𝕜 _ Y X Z _ _ oY' oZ z φ.symm : ℕ) : ℤ) - (@excCount 𝕜 _ X Y Z _ _ oX' oZ z φ : ℕ)
  rw [hX', hY']

/-- The `cylOver`-flavoured vanishing statement. -/
theorem cInv_prodMap_eq_zero_of_cylOver {𝕜 : Type} [Field 𝕜] (k : ℕ)
    {X Y : AlgebraicGeometry.Scheme.{0}}
    [MotivicInvariants.Variety 𝕜 X] [MotivicInvariants.Variety 𝕜 Y]
    (φ : X.BirationalMap Y)
    [φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)]
    [MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k)]
    [∀ x : X, IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).tensor]
    [∀ y : Y, IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) Y y k).tensor]
    (hfin : (exDiv φ).Finite) (hfin' : (exDiv φ.symm).Finite)
    (h : ∀ (Z : AlgebraicGeometry.Scheme.{0})
      [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))], ∀ z : Z, cInv 𝕜 z φ = 0) :
    ∀ (Z : AlgebraicGeometry.Scheme.{0})
      [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))],
      ∀ z : Z, @cInv 𝕜 _ (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)
        (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k) Z _ _ (cylOver (𝕜 := 𝕜) X k) (cylOver (𝕜 := 𝕜) Y k) _
        z (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ) = 0 := by
  intro Z _ z
  letI hCX : (Work.CY3Stab.WProd (𝕜 := 𝕜) X k).Over
      (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) := cylOver X k
  letI hCY : (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k).Over
      (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) := cylOver Y k
  haveI hsy : (φ.symm).IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) :=
    inferInstanceAs (AlgebraicGeometry.Scheme.RationalMap.IsOver
      (AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) φ.inv)
  have hmatch : ∀ (W : AlgebraicGeometry.Scheme.{0})
      [W.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))] (w : W),
      (exDiv φ ∩ {x | ResEquiv 𝕜 x w}).ncard = (exDiv φ.symm ∩ {y | ResEquiv 𝕜 y w}).ncard := by
    intro W _ w
    have h0 := h W w
    have h1 : excCount 𝕜 w φ = excCount 𝕜 w φ.symm := by
      unfold cInv at h0
      omega
    have h2 : excCount 𝕜 w φ = (exDiv φ ∩ {x | ResEquiv 𝕜 x w}).ncard := rfl
    have h3 : excCount 𝕜 w φ.symm = (exDiv φ.symm ∩ {y | ResEquiv 𝕜 y w}).ncard := rfl
    rw [← h2, ← h3]
    exact h1
  obtain ⟨e, he⟩ := exists_bijection_of_ncard_of_resEquiv hfin hfin' hmatch
  have hf : exDiv (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ)
      = (fun x => Work.CY3Stab.prodPt (𝕜 := 𝕜) X x k) '' exDiv φ :=
    Work.CY3Stab.Prod.exDiv_prodMap_eq 𝕜 k φ
  have hi : exDiv ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ).symm)
      = (fun y => Work.CY3Stab.prodPt (𝕜 := 𝕜) Y y k) '' exDiv φ.symm := by
    rw [Work.CY3Stab.Prod.prodMap_symm 𝕜 k φ]
    exact Work.CY3Stab.Prod.exDiv_prodMap_eq 𝕜 k φ.symm
  have hpq : ∀ x y, ResEquiv 𝕜 x y →
      ResEquiv 𝕜 (Work.CY3Stab.prodPt (𝕜 := 𝕜) X x k) (Work.CY3Stab.prodPt (𝕜 := 𝕜) Y y k) := by
    intro x y hxy
    simpa only [Work.CY3Stab.prodPt] using
      Work.CY3Stab.Prod.resEquiv_prodPt_of_resEquiv 𝕜 k x y hxy
  have hp : Function.Injective (fun x => Work.CY3Stab.prodPt (𝕜 := 𝕜) X x k) := by
    intro x x' h
    exact Work.CY3Stab.prodPt_injective k x x' h
  have hq : Function.Injective (fun y => Work.CY3Stab.prodPt (𝕜 := 𝕜) Y y k) := by
    intro y y' h
    have h1 := congrArg (Work.K3.baseChangeAlongProj (Work.CY3Stab.AffineK (𝕜 := 𝕜) k ↘
      AlgebraicGeometry.Spec (CommRingCat.of 𝕜)) Y) h
    rwa [Work.CY3Stab.prodPt_snd, Work.CY3Stab.prodPt_snd] at h1
  have hw : Work.Motivic.wgt 𝕜 z (exDiv (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ))
      = Work.Motivic.wgt 𝕜 z (exDiv ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ).symm)) := by
    rw [hf, hi]
    exact wgt_image_eq_of_bijection _ _ hp hq e he hpq z
  show ((excCount 𝕜 z (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ).symm : ℕ) : ℤ)
      - excCount 𝕜 z (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ) = 0
  have h1 : excCount 𝕜 z (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ)
      = Work.Motivic.wgt 𝕜 z (exDiv (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ)) := rfl
  have h2 : excCount 𝕜 z (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ).symm
      = Work.Motivic.wgt 𝕜 z (exDiv ((Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ).symm)) := rfl
  rw [h1, h2, hw]
  first | refl_ring1 | ring

/-- **The repaired statement.** -/
theorem cInv_prodMap_eq_zero_of_canonical {𝕜 : Type} [Field 𝕜] (k : ℕ)
    {X Y : AlgebraicGeometry.Scheme.{0}}
    [MotivicInvariants.Variety 𝕜 X] [MotivicInvariants.Variety 𝕜 Y]
    (φ : X.BirationalMap Y)
    [φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)]
    [MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k)]
    (hPX : (Work.CY3Stab.WProd (𝕜 := 𝕜) X k ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝕜))
      = (Work.CY3Stab.wProdOver (𝕜 := 𝕜) X k).1)
    (hPY : (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k ↘ AlgebraicGeometry.Spec (CommRingCat.of 𝕜))
      = (Work.CY3Stab.wProdOver (𝕜 := 𝕜) Y k).1)
    [∀ x : X, IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).tensor]
    [∀ y : Y, IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) Y y k).tensor]
    (hfin : (exDiv φ).Finite) (hfin' : (exDiv φ.symm).Finite)
    (h : ∀ (Z : AlgebraicGeometry.Scheme.{0})
      [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))], ∀ z : Z, cInv 𝕜 z φ = 0) :
    ∀ (Z : AlgebraicGeometry.Scheme.{0})
      [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))],
      ∀ z : Z, cInv 𝕜 z (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ) = 0 := by
  intro Z _ z
  have hC2 : @cInv 𝕜 _ (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k) Z
        _ _
        (@MotivicInvariants.Variety.over 𝕜 _
          (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)
          ‹MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)›)
        (@MotivicInvariants.Variety.over 𝕜 _
          (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k)
          ‹MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k)›)
        _ z (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ)
      = @cInv 𝕜 _ (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k) Z
        _ _ (cylOver (𝕜 := 𝕜) X k) (cylOver (𝕜 := 𝕜) Y k) _ z
        (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ) :=
    cInv_congr_over_hom _ _ _ _ _
      (by rw [cylOver_hom_eq_wProdOver]; exact hPX.symm)
      (by rw [cylOver_hom_eq_wProdOver]; exact hPY.symm) z (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ)
  rw [hC2]
  exact cInv_prodMap_eq_zero_of_cylOver k φ hfin hfin' h Z z

/-- **The cylinder of a strong birationality is strong** (the stabilisation step of
Lin–Shinder's `thm:bir-generation` (c), in the form in which the CY3 packaging uses it).

If every invariant coefficient of `φ` vanishes, then every coefficient of `φ × id_{𝔸ᵏ}` vanishes.
The cylinder structures on `𝔸ᵏ × X` are those found by instance search (they are `cylOver`, i.e.
the canonical composite structure `𝔸ᵏ × X ⟶ 𝔸ᵏ ⟶ Spec 𝕜`, matching the `Over`-instances installed
at the call sites); this is what makes the statement provable — with *arbitrary* `Variety`
structures on the cylinders it is false (a base-change twist changes `resMap`). -/
theorem cInv_prodMap_eq_zero_of_strong {𝕜 : Type} [Field 𝕜] (k : ℕ) {X Y : AlgebraicGeometry.Scheme.{0}}
    [MotivicInvariants.Variety 𝕜 X] [MotivicInvariants.Variety 𝕜 Y] (φ : X.BirationalMap Y)
    [φ.IsOver (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))]
    [AlgebraicGeometry.IsIntegral (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)]
    [AlgebraicGeometry.IsIntegral (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k)]
    [∀ x : X, IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) X x k).tensor]
    [∀ y : Y, IsDomain (Work.CY3Stab.cylTriplet (𝕜 := 𝕜) Y y k).tensor]
    (hfin : (exDiv φ).Finite) (hfin' : (exDiv φ.symm).Finite)
    (h : ∀ (Z : AlgebraicGeometry.Scheme.{0}) [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))],
      ∀ z : Z, cInv 𝕜 z φ = 0) :
    ∀ (Z : AlgebraicGeometry.Scheme.{0}) [Z.Over (AlgebraicGeometry.Spec (CommRingCat.of 𝕜))],
      ∀ z : Z, cInv 𝕜 z (Work.CY3Stab.prodMap (𝕜 := 𝕜) k φ) = 0 := by
  -- the two `Variety`-structures on the cylinders, needed for the `Variety`/`IrreducibleSpace`
  -- arguments of `cInv_prodMap_eq_zero_of_cylOver`; their `over` fields are `cylOver`, which is
  -- the structure the goal's `cInv` uses by instance search
  letI hVX : MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) X k) :=
    { «over» := cylOver (𝕜 := 𝕜) X k
      isIntegral := ‹AlgebraicGeometry.IsIntegral (Work.CY3Stab.WProd (𝕜 := 𝕜) X k)›
      isSeparated := by
        show IsSeparated ((cylOver (𝕜 := 𝕜) X k).hom)
        rw [cylOver_hom_eq_wProdOver]
        exact (Work.CY3Stab.varietyWProd (𝕜 := 𝕜) X k).isSeparated
      locallyOfFiniteType := by
        show LocallyOfFiniteType ((cylOver (𝕜 := 𝕜) X k).hom)
        rw [cylOver_hom_eq_wProdOver]
        exact (Work.CY3Stab.varietyWProd (𝕜 := 𝕜) X k).locallyOfFiniteType
      quasicompact := by
        show QuasiCompact ((cylOver (𝕜 := 𝕜) X k).hom)
        rw [cylOver_hom_eq_wProdOver]
        exact (Work.CY3Stab.varietyWProd (𝕜 := 𝕜) X k).quasicompact }
  letI hVY : MotivicInvariants.Variety 𝕜 (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k) :=
    { «over» := cylOver (𝕜 := 𝕜) Y k
      isIntegral := ‹AlgebraicGeometry.IsIntegral (Work.CY3Stab.WProd (𝕜 := 𝕜) Y k)›
      isSeparated := by
        show IsSeparated ((cylOver (𝕜 := 𝕜) Y k).hom)
        rw [cylOver_hom_eq_wProdOver]
        exact (Work.CY3Stab.varietyWProd (𝕜 := 𝕜) Y k).isSeparated
      locallyOfFiniteType := by
        show LocallyOfFiniteType ((cylOver (𝕜 := 𝕜) Y k).hom)
        rw [cylOver_hom_eq_wProdOver]
        exact (Work.CY3Stab.varietyWProd (𝕜 := 𝕜) Y k).locallyOfFiniteType
      quasicompact := by
        show QuasiCompact ((cylOver (𝕜 := 𝕜) Y k).hom)
        rw [cylOver_hom_eq_wProdOver]
        exact (Work.CY3Stab.varietyWProd (𝕜 := 𝕜) Y k).quasicompact }
  intro Z _ z
  exact cInv_prodMap_eq_zero_of_cylOver k φ hfin hfin' h Z z

end Work.CY3Stab.Prod
