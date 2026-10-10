import Mathlib
import ChallengeDeps
import Submission.Work.MotA.Defs
import Submission.Work.MotK.KleinData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Route V: definitions (characteristic `≠ 5` branch)

This is the definition layer of the area `Submission/Work/MotV` (`Work.MotV`), route V for
`theorem_1_2_2` / `theorem_1_2_3` of

* H.-Y. Lin, E. Shinder, *Motivic invariants of birational maps*, Ann. of Math. **199** (2024),

as designed in `MOTIVIC_S45_LEAD.md`.  The statements of the open nodes live in the sibling files
of this directory, one per node; this file holds only the vocabulary together with the two
polynomial identities that are proved outright.

## Conventions

* `kleinTw a b h y` is the T-twist of the Klein quadrics `kleinP a b` in Kummer coordinates
  `x_i = w^i y_i`, `w^5 = h`:  `kleinP a b (w^i y_i) = w^{4k} · kleinTw a b (w^5) y`.
* `TrivOn 𝕜 v` says that the valuation `v` is trivial on the constants `𝕜`;
  `FifthPowerValued 𝕜 g` says `v g` is a fifth power at every `ℤᵐ⁰`-valuation trivial on `𝕜`.
* `twistFieldT D h` is the function field `K(C_h) ⊆ K̄(E)` of the T-twist of the Klein curve by
  the Kummer class of `h`, with `K = 𝕜(t)`; `twCoord D h` are the twisted Klein coordinates.
* `ConstantsOnly 𝕜 F` says that every `𝕜`-embedding of `F` into a rational function field
  `M(y)` has image in `M ⊗ 1`; `LinkCert` / `CertN` are the two certificate levels of the link.
-/

set_option autoImplicit false
open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.MotV
noncomputable section

/-! ## §0 Twisted Klein equations (T-twist, Kummer coordinates `x_i = w^i y_i`) -/

def twMon {F : Type*} [CommRing F] (h : F) (y : Fin 5 → F) (i l : Fin 5) : F :=
  (if 5 ≤ i.val + l.val then h else 1) * y i * y l

/-- The T-twisted Klein quadrics: `kleinP a b (w^i y_i) = w^{4k} kleinTw a b (w^5) y`. -/
def kleinTw {F : Type*} [CommRing F] (a b h : F) (y : Fin 5 → F) (k : Fin 5) : F :=
  -a * b * twMon h y (2 * k) (2 * k) + a ^ 2 * twMon h y (2 * k + 2) (2 * k + 3)
    - b ^ 2 * twMon h y (2 * k + 1) (2 * k + 4)

theorem kleinTw_one {F : Type*} [CommRing F] (a b : F) (y : Fin 5 → F) :
    kleinTw a b 1 y = Work.MotK.kleinP a b y := by
  funext k; fin_cases k <;>
    simp [kleinTw, twMon, Work.MotK.kleinP, Work.MotK.kleinP0, Work.MotK.kleinP1,
      Work.MotK.kleinP2, Work.MotK.kleinP3, Work.MotK.kleinP4] <;> ring

theorem kleinTw_subst {F : Type*} [CommRing F] (a b w : F) (y : Fin 5 → F) (k : Fin 5) :
    Work.MotK.kleinP a b (fun i => w ^ (i : ℕ) * y i) k =
      w ^ ((4 * k : Fin 5) : ℕ) * kleinTw a b (w ^ 5) y k := by
  fin_cases k <;>
    simp [kleinTw, twMon, Work.MotK.kleinP, Work.MotK.kleinP0, Work.MotK.kleinP1,
      Work.MotK.kleinP2, Work.MotK.kleinP3, Work.MotK.kleinP4] <;> ring

/-! ## §1 Valuation vocabulary -/

def TrivOn (𝕜 : Type*) {F Γ₀ : Type*} [Field 𝕜] [Field F] [Algebra 𝕜 F]
    [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation F Γ₀) : Prop :=
  ∀ c : 𝕜, c ≠ 0 → v (algebraMap 𝕜 F c) = 1

/-- `g` has a fifth-power value at every `ℤᵐ⁰`-valuation trivial on `𝕜`. -/
def FifthPowerValued (𝕜 : Type*) {F : Type*} [Field 𝕜] [Field F] [Algebra 𝕜 F] (g : F) : Prop :=
  ∀ v : Valuation F ℤᵐ⁰, TrivOn 𝕜 v → ∃ u : F, v g = v u ^ 5

/-! ## §2 Klein data and the T-twist field -/

/-- `x, y` in the function field of a Weierstrass curve. -/
def genX {L : Type*} [Field L] (E : WeierstrassCurve L) : Affine.FunctionField E :=
  algebraMap (Affine.CoordinateRing E) _ (Affine.CoordinateRing.mk E (Polynomial.C Polynomial.X))
def genY {L : Type*} [Field L] (E : WeierstrassCurve L) : Affine.FunctionField E :=
  algebraMap (Affine.CoordinateRing E) _ (Affine.CoordinateRing.mk E Polynomial.X)

/-- Klein (Fisher) model data over `𝕜`: a Weierstrass curve and the Klein coordinates as linear
forms in the basis `1, x, y, x², xy` of `L(5·O)`. -/
structure KleinData (𝕜 : Type*) [Field 𝕜] where
  a : 𝕜
  b : 𝕜
  E : WeierstrassCurve 𝕜
  coord : Fin 5 → Fin 5 → 𝕜

def kleinCoord {𝕜 : Type*} [Field 𝕜] (D : KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L]
    (i : Fin 5) : Affine.FunctionField (D.E.baseChange L) :=
  let X := genX (D.E.baseChange L)
  let Y := genY (D.E.baseChange L)
  let bas : Fin 5 → Affine.FunctionField (D.E.baseChange L) := ![1, X, Y, X ^ 2, X * Y]
  ∑ m, algebraMap L _ (algebraMap 𝕜 L (D.coord i m)) * bas m

/-- The basis `1, x, y, x², xy` of `L(5·O)` in the function field of `E` over `L`: the coordinates
in which the Klein linear forms `kleinCoord D L i` are written. -/
def kleinBas {𝕜 : Type*} [Field 𝕜] (D : KleinData 𝕜) (L : Type*) [Field L] [Algebra 𝕜 L] :
    Fin 5 → Affine.FunctionField (D.E.baseChange L) :=
  let X := genX (D.E.baseChange L)
  let Y := genY (D.E.baseChange L)
  ![1, X, Y, X ^ 2, X * Y]

theorem kleinCoord_eq_sum {𝕜 : Type*} [Field 𝕜] (D : KleinData 𝕜) (L : Type*) [Field L]
    [Algebra 𝕜 L] (i : Fin 5) :
    kleinCoord D L i = ∑ m, algebraMap L _ (algebraMap 𝕜 L (D.coord i m)) * kleinBas D L m :=
  rfl

/-- Properties delivered by node KF (CAS data K0 plus identities).

WARNING (documented deviation from `MOTIVIC_S45_STATEMENTS.lean.txt`).  The three fields
`klein_eq`, `coord0_ne`, `T_diag` are stated for `L : Type` — the universe-`0` form of the design
file.  Consequently `D.Good` can only be *used* at `𝕜 : Type` (`Kb 𝕜` must be a universe-`0`
type), which is the universe of every node of this area except the design's `twCoord_eq`; the
latter is stated in this area at `{𝕜 : Type}` for exactly this reason.  (Widening the fields to
`∀ (L : Type*)` would turn the levels into unused parameters of the structure and make `D.Good`
unusable as a `Prop`; see the note in `Submission/Work/MotV/twCoord_eq.lean` for the
machine-checked obstruction at `{𝕜 : Type*}`.)

The field `spans` is the `generates` condition of `MOTIVIC_S45_LEAD.md` §5, which the design file's
`Good` omits: without it the *only* information about the Klein coordinates is `kleinP a b κ = 0`
(an inclusion `κ(E) ⊆ V(p)`, not an equality), and every node asking the twist field to be a
`K`-form of `K̄(E)` (`twist_regular`, `twist_natural`, `twist_iso_point`, `constantsOnly_twist`,
`rigidity`) is unprovable.  The CAS data satisfy `spans` because the `κ_i` are an explicit basis of
the eigenvalue spaces of the Heisenberg `μ₅`-action on `L(5·O)`: the matrix `D.coord` is
invertible over `𝕜`. -/
structure KleinData.Good {𝕜 : Type*} [Field 𝕜] (D : KleinData 𝕜) : Prop where
  elliptic : D.E.IsElliptic
  ab_ne : D.a * D.b ≠ 0
  j_ne_zero : D.E.j ≠ 0
  j_ne : D.E.j ≠ 1728
  klein_eq : ∀ (L : Type) [Field L] [Algebra 𝕜 L] (k : Fin 5),
    Work.MotK.kleinP (algebraMap 𝕜 _ D.a) (algebraMap 𝕜 _ D.b) (kleinCoord D L) k = 0
  coord0_ne : ∀ (L : Type) [Field L] [Algebra 𝕜 L], kleinCoord D L 0 ≠ 0
  /-- translation by the 5-torsion point `T` acts diagonally (over any `L ∋ ζ₅`) -/
  T_diag : ∀ (L : Type) [Field L] [Algebra 𝕜 L] (ζ : L), IsPrimitiveRoot ζ 5 →
    ∃ σ : Affine.FunctionField (D.E.baseChange L) ≃ₐ[L] Affine.FunctionField (D.E.baseChange L),
      ∀ i, σ (kleinCoord D L i / kleinCoord D L 0) = algebraMap L _ ζ ^ (i : ℕ) *
        (kleinCoord D L i / kleinCoord D L 0)
  /-- The Klein linear forms are invertible over `𝕜`: every element of the basis
  `1, x, y, x², xy` of `L(5·O)` is a `𝕜`-linear combination of the `κ_i` (equivalently, the matrix
  `D.coord` is invertible).  This is the `generates` condition of `MOTIVIC_S45_LEAD.md` §5: it
  gives `K̄(κ_i) = Om D`, hence `K̄ · F_h = Om D`. -/
  spans : ∃ e : Fin 5 → Fin 5 → 𝕜, ∀ (L : Type) [Field L] [Algebra 𝕜 L] (m : Fin 5),
    kleinBas D L m = ∑ i, algebraMap L _ (algebraMap 𝕜 L (e m i)) * kleinCoord D L i

abbrev Kb (𝕜 : Type*) [Field 𝕜] := AlgebraicClosure (RatFunc 𝕜)
abbrev Om {𝕜 : Type*} [Field 𝕜] (D : KleinData 𝕜) := Affine.FunctionField (D.E.baseChange (Kb 𝕜))

def root5 {𝕜 : Type*} [Field 𝕜] (h : RatFunc 𝕜) : Kb 𝕜 :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (algebraMap (RatFunc 𝕜) (Kb 𝕜) h)
    (by norm_num : 0 < 5))

/-- twisted coordinates `y_i = w^{-i} κ_i/κ_0`, `w^5 = h` -/
def twCoord {𝕜 : Type*} [Field 𝕜] (D : KleinData 𝕜) (h : RatFunc 𝕜) (i : Fin 5) : Om D :=
  ((algebraMap (Kb 𝕜) (Om D) (root5 h))⁻¹) ^ (i : ℕ) *
    (kleinCoord D (Kb 𝕜) i / kleinCoord D (Kb 𝕜) 0)

/-- **The T-twist field** `K(C_h)`, `K = 𝕜(t)`: function field of the twist of the Klein curve
by the Kummer class of `h` through `μ₅ ≅ ⟨T⟩`. -/
def twistFieldT {𝕜 : Type*} [Field 𝕜] (D : KleinData 𝕜) (h : RatFunc 𝕜) :
    IntermediateField (RatFunc 𝕜) (Om D) :=
  IntermediateField.adjoin (RatFunc 𝕜) (Set.range (twCoord D h))

/-! ## §3 The base parameter and the Artin–Schreier parameter -/

/-- The Kummer parameter `h = t(t-1)` of the T-twist. -/
abbrev hT (𝕜 : Type*) [Field 𝕜] : RatFunc 𝕜 := RatFunc.X * (RatFunc.X - 1)

/-- AS Galois coordinates of the S-twist: `x_i = Σ_j y_j (w+i)^j`, `w^5 - w = g`. -/
def asCoord {L : Type*} [Field L] (w : L) (y : Fin 5 → L) (i : Fin 5) : L :=
  ∑ j : Fin 5, y j * (w + ((i : ℕ) : L)) ^ (j : ℕ)

/-- The Artin–Schreier parameter `f = t³ + t` of the characteristic-5 branch. -/
abbrev fAS (𝕜 : Type*) [Field 𝕜] : RatFunc 𝕜 := RatFunc.X ^ 3 + RatFunc.X

/-! ## §7 Constants-only -/

/-- Every `𝕜`-embedding of `F` into a one-variable rational function field over a `𝕜`-algebra
`M` has image in the constants `M`. -/
def ConstantsOnly (𝕜 F : Type*) [Field 𝕜] [Field F] [Algebra 𝕜 F] : Prop :=
  ∀ (M : Type) [Field M] [Algebra 𝕜 M] (ι : F →ₐ[𝕜] RatFunc M) (x : F),
    ∃ c : M, algebraMap M _ c = ι x

/-! ## §8 Certificates: K-level link (from the K-route) and 𝕜-level -/

/-- residue field of a point of `𝔸ⁿ_K` -/
abbrev resF (K : Type) [Field K] {n : ℕ} (x : Work.MotA.polySpec K n) :=
  FractionRing (MvPolynomial (Fin n) K ⧸ x.asIdeal)

/-- a `K`-field admitting a non-constant `K`-embedding into a rational function field -/
def GeomRuled (K F₀ : Type) [Field K] [Field F₀] [Algebra K F₀] : Prop :=
  ∃ (M : Type) (_ : Field M) (_ : Algebra K M) (ι : F₀ →ₐ[K] RatFunc M) (x : F₀),
    ∀ c : M, algebraMap M _ c ≠ ι x

def JunkClass (K : Type) [Field K] {n : ℕ} (x : Work.MotA.polySpec K n) : Prop :=
  ∃ (F₀ : Type) (_ : Field F₀) (_ : Algebra K F₀), GeomRuled K F₀ ∧
    Nonempty (resF K x ≃ₐ[K] RatFunc F₀)

/-- **K-level link certificate** (deliverable of the K-route, affine form). -/
structure LinkCert (K : Type) [Field K] (F₁ F₂ : Type) [Field F₁] [Field F₂] [Algebra K F₁]
    [Algebra K F₂] where
  F : MvPolynomial (Fin 3) K
  G : MvPolynomial (Fin 3) K
  hF : F ≠ 0
  hG : G ≠ 0
  Φ : Localization.Away F ≃ₐ[K] Localization.Away G
  zP : Work.MotA.polySpec K 3
  zP_ht : Order.coheight zP = 1
  zP_mem : G ∈ zP.asIdeal
  zP_res : Nonempty (resF K zP ≃ₐ[K] RatFunc F₁)
  G_other : ∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 → G ∈ x.asIdeal → x ≠ zP →
    JunkClass K x
  F_all : ∀ x : Work.MotA.polySpec K 3, Order.coheight x = 1 → F ∈ x.asIdeal →
    Nonempty (resF K x ≃ₐ[K] RatFunc F₂) ∨ JunkClass K x

/-- **𝕜-level certificate**: exactly one divisor class `z` counted on the `G` side, none on `F`. -/
structure CertN (𝕜 : Type) [Field 𝕜] (n : ℕ) where
  F : MvPolynomial (Fin n) 𝕜
  G : MvPolynomial (Fin n) 𝕜
  hF : F ≠ 0
  hG : G ≠ 0
  Φ : Localization.Away F ≃ₐ[𝕜] Localization.Away G
  z : Work.MotA.polySpec 𝕜 n
  z_ht : Order.coheight z = 1
  z_mem : G ∈ z.asIdeal
  G_other : ∀ x : Work.MotA.polySpec 𝕜 n, Order.coheight x = 1 → G ∈ x.asIdeal → x ≠ z →
    ¬ ResEquiv 𝕜 x z
  F_none : ∀ x : Work.MotA.polySpec 𝕜 n, Order.coheight x = 1 → F ∈ x.asIdeal →
    ¬ ResEquiv 𝕜 x z

end
end Work.MotV
