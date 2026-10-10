import Mathlib
import ChallengeDeps
import Submission.Work.K3.Defs
import Submission.Work.LLink.Count
import Submission.Work.LLink.cInv_eq_neg_symm
import Submission.Work.Motivic.cInv_add
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.CY3.Defs` — vocabulary for the `G₂`-Grassmannian L-link (Lin–Shinder, `thm:CY3`)

This is the base module of the **CY3 area** of `annals_motivic_invariants`, i.e. the `n ≥ 5` case
of Theorem 1.2 (3) of the challenge: for every **infinite** field `𝕜`, `Crₙ(𝕜)` is not generated
by pseudo-regularizable elements.

The source is H.-Y. Lin, E. Shinder, *Motivic invariants of birational maps*,
Annals of Math. **199** (1), 2024, § *K-trivial threefolds* (`Papers/lin_shinder/cremona-paper.tex`,
`thm:CY3` and its proof), a construction of Ito–Miura–Okawa–Ueda extended by the paper from
characteristic zero to an arbitrary infinite field.

## The link

```
        X_k  (zero locus of a general section σ of L = p*M ⊗ p'*M')
      /    \
    τ (Bl_Z)  τ' (Bl_{Z'})
    /          \
 Z ⊂ G/P --ψ--> G/P' ⊃ Z'
```

where `G` is the split simply connected simple group scheme of type `G₂` over `ℤ`, `B` its Borel,
`P, P'` the two maximal parabolics containing `B`; `G/B → G/P`, `G/B → G/P'` are the two
`ℙ¹`-fibrations; `M`, `M'` are the ample generators of `Pic(G/P) ≅ ℤ`, `Pic(G/P') ≅ ℤ`; and
`Z`, `Z'` are the K-trivial threefolds of Picard rank one which are the centres of the link.
The two `G₂`-Grassmannians `G/P`, `G/P'` are fivefolds, and `c(ψ) = [ℙ¹ × Z] − [ℙ¹ × Z']`.

## What this module provides

* the ambient scheme `Affine 𝕜 n` of the Cremona group `Cr 𝕜 n` and the **affine transport**
  `transport ε ψ δ = ε ∘ ψ ∘ δ` of a link to affine space, with the additivity of the invariant
  coefficient along it (`transportCr`, `cInv_transport_eq`, `cInv_transport_eq_of_eq_zero`) —
  stated for every `n`, hence for the CY3 case `n = 5`;
* **strong birationality** (`StronglyBirational`, the paper's `def:strong-birat`) with the
  equivalence relation laws **proved** from the additivity `Work.Motivic.cInv_add`, the exact form
  `cInv_symm_trans_eq` in which the paper uses (L2) of an L-link, and the L2-form of `c(φ) = c(ψ)`;
  the companion notion of **strong rationality** (strong birationality to `ℙⁿ`) is in
  `Submission/Work/CY3/StronglyRational.lean`;
* the vocabulary shared with the K3 area: `IsoOver`, `StablyBirational`, `prodOver` (re-exported
  from `Submission.Work.K3.Defs` — one notion, two names), and the **named geometric predicates**
  `IsG2Grassmannian`, `IsKTrivial`, `PicardRankOne` standing for those properties of smooth
  projective varieties that Mathlib cannot express (no Picard group, no canonical bundle, no
  Picard rank, no smoothness, no projectivity, no very ample sheaves).

## Conventions

* `𝕜` is a field, `Spec (.of 𝕜)` the base scheme, `X.Over (Spec (.of 𝕜))` the base structure.
* `exDiv`, `excCount`, `cInv`, `ResEquiv`, `ResAlgEquiv` are those of `Work.Motivic.Defs`.
* The two centres of the link are named `Z`, `Z'` and the two exceptional divisors `y` (birational
  to `ℙ¹ × Z`, the *target* exceptional divisor) and `x` (birational to `ℙ¹ × Z'`, the *source*
  exceptional divisor) — the same lettering as the K3 area.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
attribute [instance] MotivicInvariants.Variety.over MotivicInvariants.Variety.isIntegral

namespace Work.CY3

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
  MotivicInvariants Order

noncomputable section

/-! ## The ambient affine space and the affine transport -/

/-- Affine `n`-space over `𝕜`, the ambient scheme of the Cremona group `Cr 𝕜 n`. -/
noncomputable abbrev Affine (𝕜 : Type) [Field 𝕜] (n : ℕ) : Scheme.{0} := 𝔸(Fin n; Spec (.of 𝕜))

/-- Affine `5`-space over `𝕜`, the ambient space of `Cr 𝕜 5` for the CY3 link. -/
noncomputable abbrev Affine5 (𝕜 : Type) [Field 𝕜] : Scheme.{0} := Affine 𝕜 5

variable {𝕜 : Type} [Field 𝕜]
variable {S T : Scheme.{0}} [IrreducibleSpace S] [IrreducibleSpace T]

/-- The **affine transport** of a birational map `ψ : S ⤏ T` along birational identifications
`ε : 𝔸ⁿ ⤏ S` and `δ : T ⤏ 𝔸ⁿ`: the birational self-map `ε ∘ ψ ∘ δ` of `𝔸ⁿ`. -/
noncomputable def transport (n : ℕ) (ε : (Affine 𝕜 n).BirationalMap S) (ψ : S.BirationalMap T)
    (δ : T.BirationalMap (Affine 𝕜 n)) : (Affine 𝕜 n).BirationalMap (Affine 𝕜 n) :=
  ε.trans (ψ.trans δ)

@[simp]
theorem transport_def (n : ℕ) (ε : (Affine 𝕜 n).BirationalMap S) (ψ : S.BirationalMap T)
    (δ : T.BirationalMap (Affine 𝕜 n)) :
    transport n ε ψ δ = ε.trans (ψ.trans δ) := rfl

/-- The affine transport of maps over `𝕜` is over `𝕜`. -/
theorem transport_isOver (n : ℕ) [S.Over (Spec (.of 𝕜))] [T.Over (Spec (.of 𝕜))]
    (ε : (Affine 𝕜 n).BirationalMap S) (ψ : S.BirationalMap T) (δ : T.BirationalMap (Affine 𝕜 n))
    [ε.IsOver (Spec (.of 𝕜))] [ψ.IsOver (Spec (.of 𝕜))] [δ.IsOver (Spec (.of 𝕜))] :
    (transport n ε ψ δ).IsOver (Spec (.of 𝕜)) := by
  haveI hmid : (ψ.trans δ).IsOver (Spec (.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans ψ δ
  rw [transport_def]
  exact Work.Motivic.pseudoReg_isOver_trans ε (ψ.trans δ)

/-- The **transported Cremona map**: the affine transport, regarded as an element of the Cremona
group `Cr 𝕜 n` of the challenge. -/
noncomputable def transportCr (n : ℕ) [S.Over (Spec (.of 𝕜))] [T.Over (Spec (.of 𝕜))]
    (ε : (Affine 𝕜 n).BirationalMap S) (ψ : S.BirationalMap T) (δ : T.BirationalMap (Affine 𝕜 n))
    [ε.IsOver (Spec (.of 𝕜))] [ψ.IsOver (Spec (.of 𝕜))] [δ.IsOver (Spec (.of 𝕜))] : Cr 𝕜 n :=
  ⟨transport n ε ψ δ, transport_isOver n ε ψ δ⟩

@[simp]
theorem transportCr_coe (n : ℕ) [S.Over (Spec (.of 𝕜))] [T.Over (Spec (.of 𝕜))]
    (ε : (Affine 𝕜 n).BirationalMap S) (ψ : S.BirationalMap T) (δ : T.BirationalMap (Affine 𝕜 n))
    [ε.IsOver (Spec (.of 𝕜))] [ψ.IsOver (Spec (.of 𝕜))] [δ.IsOver (Spec (.of 𝕜))] :
    ((transportCr n ε ψ δ : Cr 𝕜 n) : (Affine 𝕜 n).BirationalMap (Affine 𝕜 n)) =
      transport n ε ψ δ := rfl

/-- **Additivity of the invariant coefficient along the transport**: the coefficient of the
transported map splits into the three coefficients of its factors. -/
theorem cInv_transport_eq (n : ℕ) [Variety 𝕜 S] [Variety 𝕜 T]
    (ε : (Affine 𝕜 n).BirationalMap S) (ψ : S.BirationalMap T) (δ : T.BirationalMap (Affine 𝕜 n))
    [ε.IsOver (Spec (.of 𝕜))] [ψ.IsOver (Spec (.of 𝕜))] [δ.IsOver (Spec (.of 𝕜))]
    {Z : Scheme.{0}} [Z.Over (Spec (.of 𝕜))] (z : Z) :
    cInv 𝕜 z (transport n ε ψ δ) = cInv 𝕜 z ε + cInv 𝕜 z ψ + cInv 𝕜 z δ := by
  haveI hmid : (ψ.trans δ).IsOver (Spec (.of 𝕜)) :=
    Work.Motivic.pseudoReg_isOver_trans ψ δ
  have h2 := Work.Motivic.cInv_add (𝕜 := 𝕜) (X := S) (Y := T) (Z := Affine 𝕜 n) z ψ δ
  have h1 := Work.Motivic.cInv_add (𝕜 := 𝕜) (X := Affine 𝕜 n) (Y := S) (Z := Affine 𝕜 n) z ε
    (ψ.trans δ)
  rw [transport_def, h1, h2]
  first | refl_ring1 | ring

/-- The transport of a map whose two identifications have vanishing invariant coefficient has the
same coefficient as the map itself: the paper's `c(φ) = c(ψ)` for an L-link, transported to
`𝔸ⁿ`. -/
theorem cInv_transport_eq_of_eq_zero (n : ℕ) [Variety 𝕜 S] [Variety 𝕜 T]
    (ε : (Affine 𝕜 n).BirationalMap S) (ψ : S.BirationalMap T) (δ : T.BirationalMap (Affine 𝕜 n))
    [ε.IsOver (Spec (.of 𝕜))] [ψ.IsOver (Spec (.of 𝕜))] [δ.IsOver (Spec (.of 𝕜))]
    {Z : Scheme.{0}} [Z.Over (Spec (.of 𝕜))] (z : Z)
    (hε : cInv 𝕜 z ε = 0) (hδ : cInv 𝕜 z δ = 0) :
    cInv 𝕜 z (transport n ε ψ δ) = cInv 𝕜 z ψ := by
  rw [cInv_transport_eq n ε ψ δ z, hε, hδ]
  first | refl_ring1 | ring

/-! ## Strong birationality and strong rationality (paper `def:strong-birat`) -/

/-- **Strong birationality** of two `𝕜`-varieties (paper `def:strong-birat`): there is a birational
map `γ : X ⤏ Y` over `𝕜` all of whose invariant coefficients vanish.  In the paper `c(γ) = 0` is
an identity in `ℤ[Bir/𝕜]`; per coefficient (`Work.Motivic.Defs`) this is
`∀ z, cInv 𝕜 z γ = 0`, which is what is consumed by `cInv_transport_eq_of_eq_zero`.

Since `cInv` is a *coefficient* of the paper's invariant, `StronglyBirational` is a *strengthening*
of the paper's notion of strong birationality: it asks all coefficients to vanish.  All the laws of
the relation are proved from the additivity of `cInv` (paper Lemma 2.2), see below. -/
def StronglyBirational (𝕜 : Type) [Field 𝕜] (X Y : Scheme.{0}) [Variety 𝕜 X] [Variety 𝕜 Y] : Prop :=
  ∃ γ : X.BirationalMap Y, γ.IsOver (Spec (.of 𝕜)) ∧
    ∀ (Z : Scheme.{0}) [Z.Over (Spec (.of 𝕜))], ∀ z : Z, cInv 𝕜 z γ = 0

namespace StronglyBirational

variable {X Y Z : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y] [Variety 𝕜 Z]

/-- The defining property, as a plain statement: all coefficients of a strong birationality
vanish. -/
theorem cInv_eq_zero {γ : X.BirationalMap Y} (_hγ : γ.IsOver (Spec (.of 𝕜)))
    (h : ∀ (Z : Scheme.{0}) [Z.Over (Spec (.of 𝕜))], ∀ z : Z, cInv 𝕜 z γ = 0)
    {W : Scheme.{0}} [W.Over (Spec (.of 𝕜))] (w : W) : cInv 𝕜 w γ = 0 :=
  h W w

/-- **Strong birationality is reflexive**: the identity has vanishing coefficients
(`Work.Motivic.pseudoReg_cInv_one`). -/
theorem refl (X : Scheme.{0}) [Variety 𝕜 X] : StronglyBirational 𝕜 X X := by
  refine ⟨1, ?_, ?_⟩
  · change (RationalMap.id X).IsOver (Spec (.of 𝕜))
    infer_instance
  · intro W _ w
    exact Work.Motivic.pseudoReg_cInv_one 𝕜 w

/-- Strong birationality is symmetric: the inverse of a birational map has the opposite
coefficients (`Work.LLink.cInv_eq_neg_symm`), and `−0 = 0`. -/
theorem symm (h : StronglyBirational 𝕜 X Y) : StronglyBirational 𝕜 Y X := by
  obtain ⟨γ, hγ, h0⟩ := h
  haveI : γ.IsOver (Spec (.of 𝕜)) := hγ
  refine ⟨γ.symm, ?_, ?_⟩
  · exact inferInstanceAs (γ.inv.IsOver (Spec (.of 𝕜)))
  · intro W _ w
    rw [Work.LLink.cInv_eq_neg_symm, h0 W w]
    first | refl_ring1 | ring

/-- **Strong birationality is transitive**: this is additivity of the invariant
(`Work.Motivic.cInv_add`) applied to the composite. -/
theorem trans (h : StronglyBirational 𝕜 X Y) (h' : StronglyBirational 𝕜 Y Z) :
    StronglyBirational 𝕜 X Z := by
  obtain ⟨γ, hγ, h0⟩ := h
  obtain ⟨γ', hγ', h0'⟩ := h'
  haveI : γ.IsOver (Spec (.of 𝕜)) := hγ
  haveI : γ'.IsOver (Spec (.of 𝕜)) := hγ'
  refine ⟨γ.trans γ', ?_, ?_⟩
  · exact Work.Motivic.pseudoReg_isOver_trans γ γ'
  · intro W _ w
    rw [Work.Motivic.cInv_add (𝕜 := 𝕜) w γ γ', h0 W w, h0' W w]
    first | refl_ring1 | ring

end StronglyBirational

/-- **Item (L2) of an L-link, in the exact form in which the paper uses it** (proof of
`lemma:L-link` (2): "Let `φ = γ⁻¹ψ ∈ Bir(XX)`, where `γ` comes from Definition `def:strong-birat`.
Then `c(φ) = c(ψ) = …`").

If `γ : X ⤏ Y` is a strong birationality — i.e. all its coefficients vanish — then for every
`ψ : X ⤏ Y` the self-map `γ⁻¹ ∘ ψ` of `Y` has the same coefficient as `ψ`.  This is additivity
plus `cInv 𝕜 w γ⁻¹ = −cInv 𝕜 w γ = 0`; it is the reason (L2) is enough for the coefficient
computation of `lemma:L-link` (2). -/
theorem cInv_symm_trans_eq {X Y : Scheme.{0}} [Variety 𝕜 X] [Variety 𝕜 Y]
    (γ : X.BirationalMap Y) (hγ : γ.IsOver (Spec (.of 𝕜)))
    (h0 : ∀ (W : Scheme.{0}) [W.Over (Spec (.of 𝕜))], ∀ w : W, cInv 𝕜 w γ = 0)
    (ψ : X.BirationalMap Y) [ψ.IsOver (Spec (.of 𝕜))] {W : Scheme.{0}} [W.Over (Spec (.of 𝕜))]
    (w : W) : cInv 𝕜 w (γ.symm.trans ψ) = cInv 𝕜 w ψ := by
  haveI : γ.IsOver (Spec (.of 𝕜)) := hγ
  haveI : (γ.symm).IsOver (Spec (.of 𝕜)) := inferInstanceAs (γ.inv.IsOver (Spec (.of 𝕜)))
  rw [Work.Motivic.cInv_add (𝕜 := 𝕜) w γ.symm ψ, Work.LLink.cInv_eq_neg_symm, h0 W w]
  first | refl_ring1 | ring

/-! ## Shared vocabulary (re-exported from the K3 area) -/

/-- The product of two `𝕜`-schemes, i.e. the fibred product over `Spec 𝕜`.  Same notion as
`Work.K3.prodOver`. -/
abbrev prodOver (𝕜 : Type) [Field 𝕜] (X Y : Scheme.{0}) [X.Over (Spec (.of 𝕜))]
    [Y.Over (Spec (.of 𝕜))] : Scheme.{0} := Work.K3.prodOver 𝕜 X Y

/-- Isomorphisms of `𝕜`-schemes, i.e. isomorphisms compatible with the structure morphisms.  Same
notion as `Work.K3.IsoOver`; "not isomorphic over `𝕜`" is the hypothesis of Totaro's Corollary
`cor-CYnSB` which distinguishes the two centres of the CY3 link. -/
abbrev IsoOver (𝕜 : Type) [Field 𝕜] (X Y : Scheme.{0}) [X.Over (Spec (.of 𝕜))]
    [Y.Over (Spec (.of 𝕜))] : Prop := Work.K3.IsoOver 𝕜 X Y

/-- **Stable birationality** over `𝕜`: `X × 𝔸ⁿ` is birational to `Y × 𝔸ᵐ` for some `n, m`.  Same
notion as `Work.K3.StablyBirational`.  Affine space is used rather than `ℙⁿ` because only the
function field matters and `𝔸ⁿ` is birational to `ℙⁿ`; the relation is the one in Totaro's
Corollary `cor-CYnSB`. -/
abbrev StablyBirational (𝕜 : Type) [Field 𝕜] (X Y : Scheme.{0}) [Variety 𝕜 X]
    [Variety 𝕜 Y] : Prop := Work.K3.StablyBirational 𝕜 X Y

namespace IsoOver

/-- Isomorphism over the base is reflexive. -/
theorem refl (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [X.Over (Spec (.of 𝕜))] : IsoOver 𝕜 X X :=
  Work.K3.IsoOver.refl 𝕜 X

/-- Isomorphism over the base is symmetric. -/
theorem symm {X Y : Scheme.{0}} [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))]
    (h : IsoOver 𝕜 X Y) : IsoOver 𝕜 Y X :=
  Work.K3.IsoOver.symm h

/-- Isomorphism over the base is transitive. -/
theorem trans {X Y Z : Scheme.{0}} [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))]
    [Z.Over (Spec (.of 𝕜))] (h : IsoOver 𝕜 X Y) (h' : IsoOver 𝕜 Y Z) : IsoOver 𝕜 X Z :=
  Work.K3.IsoOver.trans h h'

end IsoOver

/-! ## Named geometric predicates

These stand for the geometric hypotheses of the `G₂`-Grassmannian construction that Mathlib cannot
express.  They are *named inputs*: they are hypotheses, never proved in this area, and they are
recorded so that the theorem-level inputs of the construction can refer to them. -/

/-- **Named geometric predicate: `X` is a `G₂`-Grassmannian.**

`IsG2Grassmannian R X` says that `X` is one of the two five-dimensional quotients `G/P`, `G/P'`
of the split simply connected simple group scheme `G` of type `G₂` over `Spec R` (over a field
`𝕜`, this is `G_{2,𝕜}/P`), i.e.

* `X` is a smooth projective fivefold;
* `X` has Picard rank one, `Pic(X) ≅ ℤ` with ample generator (Raynaud, *Ample vector bundles*,
  Prop. VII.1.5, together with `X^*(G) = 0` and `Pic(G) = 0`, Remark VII.1.7 a));
* `X` is strongly rational in the paper's sense (`lem:GP-strongly-rational`:
  `Work.CY3.IsStronglyRational ℤ X 5`, i.e. strongly birational to `ℙ⁵` — from the Bruhat
  decomposition, which has a single cell in every dimension, so that `X` is isomorphic to `𝔸⁵`
  outside one irreducible rational divisor `D` and `c(X ⤏ ℙ⁵) = [ℙ⁴] − [D] = 0`);
* the motivic class of `X` is that of `ℙ⁵` (single Bruhat cell in each dimension).

Mathlib has no Picard group, no smoothness, no projectivity and no Bruhat decomposition, so this is
a named hypothesis.  It is phrased over an arbitrary commutative ring `R` because the whole `G₂`
datum is defined over `Spec ℤ` (`Milne`, *Algebraic Groups*, Theorem 13.33, and `SGA3`,
Cor. XXII.5.8.5 for the smoothness and projectivity of `G/B`, `G/P`, `G/P'` over `ℤ`), so that the
*same* input is available over every field `𝕜` by base change. -/
class IsG2Grassmannian (R : Type) [CommRing R] (X : Scheme.{0}) [X.Over (Spec (.of R))] : Prop

/-- **Named geometric predicate: `X` has trivial canonical bundle** (`ω_X ≃ 𝒪_X`), which for a
smooth projective threefold says that `X` is `K`-trivial.  This is the hypothesis of Totaro's
Theorem `thm:BurtCY` / Corollary `cor-CYnSB`; it is the paper's definition of a `K`-trivial
variety.  Same notion as `Work.K3.IsKTrivial` (where the same predicate is used for the K3
surfaces). -/
abbrev IsKTrivial (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [Variety 𝕜 X] : Prop :=
  Work.K3.IsKTrivial 𝕜 X

/-- **Named geometric predicate: `X` has Picard rank one** (`rk NS(X) = 1`).  The CY3 centres `Z`,
`Z'` have Picard rank one (paper `lem-nSBG2`, from `rk NS(X_𝕜) = 2` for the blow-up `X_𝕜 → Z_𝕜`,
which is a `ℙ¹`-bundle).  Mathlib has no Néron–Severi group, so this is a named hypothesis. -/
class PicardRankOne (𝕜 : Type) [Field 𝕜] (X : Scheme.{0}) [Variety 𝕜 X] : Prop

end

end Work.CY3
