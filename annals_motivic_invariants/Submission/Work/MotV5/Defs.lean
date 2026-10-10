import Mathlib
import ChallengeDeps
import Submission.Work.MotA.Defs
import Submission.Work.MotK.KleinData
import Submission.Work.MotV.Defs
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Route V, characteristic 5: definitions (the Artin–Schreier branch)

This is the definition layer of the area `Submission/Work/MotV5` (`Work.MotV5`), the
*characteristic 5* branch of route V for `theorem_1_2_3` of

* H.-Y. Lin, E. Shinder, *Motivic invariants of birational maps*, Ann. of Math. **199** (2024),

as designed in `MOTIVIC_S45_LEAD.md` §C5.  In characteristic 5 the multiplicative group `μ₅` is
infinitesimal, so the T-twist of the sibling area `Work.MotV` degenerates; the étale part
`ℤ/5 ≅ ⟨P⟩ ⊂ E[5]` is instead used through an **Artin–Schreier** class: the base field is
`K = 𝕜(t)` and the twisting extension is `L = K(w)` with `w⁵ - w = g`, for the class
`g ∈ K/℘(K)`, `℘(x) = x⁵ - x`.

The Galois coordinates of the S-twist are `x_i = σ^i(Y)`, `Y = ∑_j y_j w^j`
(`Work.MotV.asCoord`), and the *twisted* Klein coordinates are therefore the coefficients of the
interpolation polynomial of the Klein point through the nodes `w + i`:

  `y_j = -∑_i x_i ((W + i)^{4-j} - δ_{j,0})`,   `x_i = κ_i/κ_0`, `℘(W) = g`,

the sign and the `δ` correction being forced by `∏_{i'≠i}(i - i') = -1` and `∏_{i'≠i}(Z - i') =
(Z⁵ - Z)/(Z - i) - (Z⁵ - i)/(Z - i) - ... = Z⁴ + iZ³ + i²Z² + i³Z + i⁴ - 1` in characteristic 5.

## Contents

* `asPoly`, `asRoot`, `asRoot_spec` — a root of `X⁵ - X - g` in `Kb 𝕜 = AlgebraicClosure (RatFunc 𝕜)`;
* `asTwCoord`, `asTwistField` — the AS-twisted coordinates and **the AS twist field** `K(C^AS_g)`;
* `FifthPowAtPoles` — `g` has a fifth-power value at every valuation at which it has a pole;
  this is the property the *pointless* twist satisfies (`fifthPowAtPoles_of_asPoint`, from the
  visited node `tp_as`) and which the exponent count `exponent_rigidity_AS` refutes;
* `ASUnramified` — the bridge condition of the design: at the poles of `t`, `g` is congruent to a
  value `u⁵ - u` of the Artin–Schreier map modulo the valuation ring.
-/

set_option autoImplicit false
open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

namespace Work.MotV5
noncomputable section

/-! ## §1 The Artin–Schreier root -/

/-- `X⁵ - X - g` over `Kb 𝕜 = AlgebraicClosure (RatFunc 𝕜)`. -/
def asPoly {𝕜 : Type} [Field 𝕜] (g : RatFunc 𝕜) : Polynomial (Work.MotV.Kb 𝕜) :=
  Polynomial.X ^ 5 - Polynomial.X - Polynomial.C (algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g)

theorem asPoly_natDegree {𝕜 : Type} [Field 𝕜] (g : RatFunc 𝕜) : (asPoly g).natDegree = 5 := by
  unfold asPoly
  compute_degree!

theorem asPoly_ne_zero {𝕜 : Type} [Field 𝕜] (g : RatFunc 𝕜) : asPoly g ≠ 0 := by
  intro h
  have := asPoly_natDegree g
  rw [h, Polynomial.natDegree_zero] at this
  exact absurd this (by norm_num)

theorem asPoly_degree_ne_zero {𝕜 : Type} [Field 𝕜] (g : RatFunc 𝕜) : (asPoly g).degree ≠ 0 := by
  rw [Polynomial.degree_eq_natDegree (asPoly_ne_zero g), asPoly_natDegree]
  norm_num

/-- A root of `X⁵ - X - g` in the algebraic closure of `𝕜(t)`. -/
def asRoot {𝕜 : Type} [Field 𝕜] (g : RatFunc 𝕜) : Work.MotV.Kb 𝕜 :=
  Classical.choose (IsAlgClosed.exists_root (asPoly g) (asPoly_degree_ne_zero g))

/-- The defining relation of `asRoot`: `asRoot g` is a root of `X⁵ - X - g`. -/
theorem asRoot_spec {𝕜 : Type} [Field 𝕜] (g : RatFunc 𝕜) :
    asRoot g ^ 5 - asRoot g = algebraMap (RatFunc 𝕜) (Work.MotV.Kb 𝕜) g := by
  have h2 : (asPoly g).IsRoot (asRoot g) := by
    unfold asRoot
    exact Classical.choose_spec (IsAlgClosed.exists_root (asPoly g) (asPoly_degree_ne_zero g))
  have h3 : (asPoly g).eval (asRoot g) = 0 := h2
  simp only [asPoly, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
    Polynomial.eval_C] at h3
  linear_combination (norm := first | refl_ring1 | ring1) h3

/-! ## §2 The AS-twisted Klein coordinates -/

/-- The Artin–Schreier twist of the Klein point: the coefficients of the interpolation polynomial
of `x = κ_i/κ_0` through the Galois-conjugate nodes `W + i`, i.e. the `K`-rational coordinates of
the twisted curve `C^AS_g`.  The identity `asCoord W (asTwCoord D g) = x` is `asCoord_asTwCoord`. -/
def asTwCoord {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) (j : Fin 5) :
    Work.MotV.Om D :=
  -∑ i : Fin 5, (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i /
        Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0) *
      ((algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g) + ((i : ℕ) : Work.MotV.Om D)) ^
          (4 - (j : ℕ)) - (if (j : ℕ) = 0 then 1 else 0))

/-- **The AS twist field** `K(C^AS_g)`, `K = 𝕜(t)`: the function field of the twist of the Klein
curve by the Artin–Schreier class of `g` through `⟨S⟩ ⊂ E[5]`.  It is the `K`-subfield of
`K̄(E)` generated by the twisted Klein coordinates. -/
def asTwistField {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) :
    IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) :=
  IntermediateField.adjoin (RatFunc 𝕜) (Set.range (asTwCoord D g))

/-! ## §2.4 The corrected construction: the twist field as the fixed field of `σ ∘ S^*`

`asTwistField` above is the interpolation model and is *wrong* in characteristic 5 (it contains
`asRoot g`; see §5 of the README).  The correct object is the fixed field of the twisted
Artin–Schreier action: the AS generator `σ` of `Kb 𝕜` over `K` (with `σ (asRoot g) = asRoot g + 1`,
node `asAut_Kb`) acting on the coefficients of `Om D` (node `coeffAut`), composed with the
fifth-torsion shift `σS` of the Klein model (node `ShiftCompat`, the characteristic 5 replacement
of the vacuous `T_diag`).  The definitions below take the two automorphisms as *data*, which is the
honest interface: neither is implied by `KleinData.Good`. -/

/-- The twisted Artin–Schreier action `σ' = σ ∘ S^*` on `Om D`: the coefficient action `τ` of the
AS generator composed with the fifth-torsion shift `σS`. -/
def asTwistAction {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D) :
    Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D :=
  τ.trans (σS.restrictScalars (RatFunc 𝕜))

/-- **The corrected AS twist field**: the fixed field of the twisted action `σ' = σ ∘ S^*` in
`K̄(E)`.  This is the object `K(C^AS_g)` of the design; unlike `asTwistField` it is *not* generated
by the interpolated coordinates (which do not descend — see `asTwistField_contains_asRoot`). -/
def asTwistFieldFix {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D) :
    IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) :=
  IntermediateField.fixedField (Subgroup.zpowers (asTwistAction D τ σS))

/-- The field `K(E) ⊆ Om D`: generated over `K = RatFunc 𝕜` by the Klein ratios (equal to the
function field of the Klein curve over `K`, by `KleinData.Good.spans`). -/
def kleinField {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜) :
    IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) :=
  IntermediateField.adjoin (RatFunc 𝕜)
    (Set.range (fun i : Fin 5 => Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i /
      Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) 0))

/-- `L(E) = K(E) ⊔ K(asRoot g)`: the base change of the Klein curve to `L = K(asRoot g)`. -/
def asFieldL {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜) :
    IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) :=
  kleinField D ⊔ IntermediateField.adjoin (RatFunc 𝕜)
    {algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (asRoot g)}

/-- **The intended AS twist field**: the fixed field of the twisted action `σ' = σ ∘ σS` taken
*inside* `L(E)` rather than inside `K̄(E)`.  `asTwistFieldFix` is too large — it contains
`K̄ 𝕜 ^ σ`, which is algebraic over `K` but bigger than `K` — so the regularity and
constants-only statements must be made for this field. -/
def asTwistFieldTrue {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (g : RatFunc 𝕜)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D) :
    IntermediateField (RatFunc 𝕜) (Work.MotV.Om D) :=
  asTwistFieldFix D τ σS ⊓ asFieldL D g

/-! ## §2.5 A nondegeneracy condition missing from `KleinData.Good` in characteristic 5

In characteristic 5 no field has a primitive fifth root of unity, so the field `T_diag` of
`Work.MotV.KleinData.Good` is vacuous and does **not** exclude the degenerate case in which all
Klein coordinates `κ_i` are constant — for which `asTwistField D g` is a *finite* extension of
`K` (a constant point, not a curve), and every statement of the branch fails for trivial reasons.
`KleinData.Nonconstant` is the honest replacement: some Klein ratio `κ_i/κ_0` is transcendental
over `𝕜`, i.e. the Klein model really is a curve. -/

/-- Some Klein coordinate ratio `κ_i/κ_0` is transcendental over `𝕜`: the Klein model is a curve,
not a constant point.  Needed throughout the characteristic 5 branch (it is not implied by
`KleinData.Good`, whose `T_diag` is vacuous in characteristic 5). -/
def KleinData.Nonconstant {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜) : Prop :=
  ∃ i : Fin 5, ∀ (L : Type) [Field L] [Algebra 𝕜 L],
    Transcendental 𝕜 (Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0)

/-- The Klein ratios generate the function field of the Klein curve.  This is the `generates`
condition of `MOTIVIC_S45_LEAD.md` §5; in the current `Work.MotV.KleinData.Good` it follows from
the `spans` field (the Klein linear forms are a basis of `L(5·O)`), but it is recorded separately
here so that the statements of this branch carry it explicitly.  The file `as_regular.lean` in
this directory records a machine-checked counterexample showing that *without* such a condition
the Artin–Schreier twist field can contain `asRoot g`. -/
def KleinData.Generates {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜) : Prop :=
  ∀ (L : Type) [Field L] [Algebra 𝕜 L],
    IntermediateField.adjoin L
      (Set.range (fun i : Fin 5 =>
        Work.MotV.kleinCoord D L i / Work.MotV.kleinCoord D L 0)) = ⊤

/-- **Fifth-torsion shift compatibility** — a proposed characteristic 5 replacement of the
(vacuous) `Work.MotV.KleinData.Good.T_diag`, asking for a `Kb 𝕜`-automorphism of the function
field permuting the Klein coordinates, `σS κ_i = κ_{i+1}`.

**WARNING — this predicate is refuted** (see `README.md` §5): a prover showed that *no* nontrivial
automorphism of the Klein curve can permute the Klein coordinates.  The reason is a pole argument:
the `κ_i` are `𝕜`-linear combinations of `1, x, y, x², xy` (the `spans` field), each of which has
its only pole at the origin `O`; an automorphism `ψ` with `ψ^*(κ_i) = κ_{i+1}` would therefore
send the span — and in particular `x` — into the span of the `κ_i`, whence `x ∘ ψ` would have its
pole only at `O`; but `x ∘ ψ` has its pole at `ψ^{-1}(O)`.  Hence `ψ` fixes `O`, an order-5
upper-triangular computation in the Weierstrass flag then gives `ψ = id`, and then all `κ_i` are
equal, contradicting `spans`/`a² - ab - b² ≠ 0`.  So the fifth-torsion translation does *not*
act by permuting the Klein coordinates, and `∃ D, ASGood D ∧ ShiftCompat D` is false
(this was node `exists_kleinData_shift`, refuted).  The characterisation of the `E[5]`-structure
that the Artin–Schreier twist really needs is therefore still open; the fixed-field construction
`asTwistFieldFix` below is correct for *any* order-5 twisted action. -/
def KleinData.ShiftCompat {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜) : Prop :=
  ∃ σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D,
    ∀ i : Fin 5, σS (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i)
      = Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) (i + 1)

/-- **Projective fifth-torsion shift compatibility** (the satisfiable version of
`ShiftCompat`): there is a `Kb 𝕜`-automorphism `σS` of `Om D` and a *non-zero* `λ ∈ Om D` with
`σS κ_i = λ · κ_{i+1}`.  The scalar is essential: the unscaled version `σS κ_i = κ_{i+1}` is
unsatisfiable (see the docstring of `ShiftCompat`), whereas the scaled relation is what the shift
of `ℙ⁴` gives on the Klein coordinates, the coordinates being sections only up to scaling. -/
def KleinData.ShiftCompatProj {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜) : Prop :=
  ∃ (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D) (lam : Work.MotV.Om D),
    lam ≠ 0 ∧ ∀ i : Fin 5,
      σS (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i)
        = lam * Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) (i + 1)

/-- **The projective shift condition for a given `Kb 𝕜`-automorphism `σS`** of `Om D`: this is
`KleinData.ShiftCompatProj` with the existential over `σS` replaced by the given automorphism,
i.e. `σS κ_i = λ κ_{i+1}` for one `λ ≠ 0` and all `i`.

It is the hypothesis that keeps the twisted Artin–Schreier action `asTwistAction D τ σS` from
degenerating.  Without it (e.g. with `σS = 1`, which satisfies every other hypothesis of the
characteristic-`5` nodes) the "twist field" `asTwistFieldTrue D g τ 1` collapses to
`kleinField D = K(E) ≈ RatFunc (𝕜(E))`, a geometrically ruled field for which `ConstantsOnly`
*and* the rigidity `IsEmpty (F₁ ≃ₐ[𝕜] F₂)` both fail.  Two reviewers of the nodes
`bridge_AS`/`constantsOnly_AS` found exactly this counterexample, which is why every statement of
the branch carries this hypothesis (or the data from which it follows). -/
def KleinData.ShiftOf {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D) : Prop :=
  ∃ lam : Work.MotV.Om D, lam ≠ 0 ∧ ∀ i : Fin 5,
    σS (Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) i)
      = lam * Work.MotV.kleinCoord D (Work.MotV.Kb 𝕜) (i + 1)

/-- The characteristic 5 nondegeneracy conditions used by the AS branch: good Klein data, a genuine
curve, generating Klein coordinates, and a smooth Klein point (`a² - ab - b² = (a - 3b)² ≠ 0` is
exactly the smoothness of the Klein quintic in characteristic 5). -/
def KleinData.ASGood {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜) : Prop :=
  D.Good ∧ KleinData.Nonconstant D ∧ KleinData.Generates D ∧
    D.a ^ 2 - D.a * D.b - D.b ^ 2 ≠ 0

/-! ## §3 The bridge and exponent-count predicates -/

/-- `g` has a fifth-power value at every `ℤᵐ⁰`-valuation of `F` trivial on `𝕜` at which `g` has a
pole.  For the twist field `F = K(C^AS_g)` and `g` the AS class this is the statement that the
twist has no `K`-point (`fifthPowAtPoles_of_asPoint`), and `exponent_rigidity_AS` is exactly its
negation for the two classes of the link. -/
def FifthPowAtPoles (𝕜 F : Type*) [Field 𝕜] [Field F] [Algebra 𝕜 F] (g : F) : Prop :=
  ∀ v : Valuation F ℤᵐ⁰, Work.MotV.TrivOn 𝕜 v → 1 < v g → ∃ u : F, v g = v u ^ 5

/-- The Artin–Schreier bridge condition of `MOTIVIC_S45_LEAD.md` §C5: at every valuation of `F`
trivial on `𝕜` at which the parameter `t` has a pole, `g` is congruent to a value `u⁵ - u` of the
Artin–Schreier map modulo the valuation ring.  This is the hypothesis of `hurwitz_AS`. -/
def ASUnramified (𝕜 F : Type*) [Field 𝕜] [Field F] [Algebra 𝕜 F] (t g : F) : Prop :=
  ∀ v : Valuation F ℤᵐ⁰, Work.MotV.TrivOn 𝕜 v → 1 < v t → ∃ u : F, v (g - (u ^ 5 - u)) ≤ 1

end
end Work.MotV5
