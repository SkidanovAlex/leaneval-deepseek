import Mathlib
import ChallengeDeps
import Submission.Work.MotA.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotC2.Defs
import Submission.Work.MotC2.Translation
import Submission.Work.MotC2.Negation
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# `Submission/Work/MotT` — the T-twist over an arbitrary base field

This area is the *generic* layer of the T-twist (Kummer-coordinate) route to
Lin–Shinder, *Motivic invariants of birational maps*, Ann. of Math. **199** (2024), Theorem 1.2.

The design is `MOTIVIC_C6_R4_LEAD.md` (Claude research designer, 2026-10-03), whose statements were
typechecked in `MOTIVIC_C6_R4_STATEMENTS.lean.txt`.  Everything here is stated for an **arbitrary
base field** `K` and an arbitrary twist parameter `h ∈ K`, so that two consumers instantiate it:

* the *function-field* route R4 (`K = X.functionField`, `h = π` a uniformizer of the place
  `Work.FFResidual.FunctionFieldPlace 𝔽 K`), which is the new route for `theorem_1_2_1 (b), (c),
  (d)` in characteristic `≠ 5`;
* route V (`K = RatFunc 𝕜`, `h = t(t-1)`), which bridges to `Work.MotV.twistFieldT`
  (`Work.MotV.twistFieldT D hT = Work.MotT.twistFieldTK (D.baseChange (RatFunc 𝕜)) hT` morally).

## Conventions

* `KbK K = AlgebraicClosure K` is the algebraic closure of the base; `OmK D` is the function field
  of `D.E` after base change to `K̄` — the *split* model in which the T-twist is computed.
* `root5K h` is a chosen fifth root of `h` in `K̄`, and `wK D h = algebraMap _ _ (root5K h) ∈ OmK D`
  its image.
* `twCoordK D h i = w^{-i} κ_i/κ_0` are the twisted Klein coordinates (`κ_i = kleinCoord D (KbK K) i`
  are the Klein linear forms of the model, i.e. the eigenbasis of the Heisenberg `μ₅`-action), and
  **`twistFieldTK D h`** — the T-twist field `K(C_h)` — is the `K`-subalgebra of `OmK D` they
  generate.  It is a `K`-form of `K̄(E)`: `twistFieldTK_descent`.
* `vOne` is the normalized "order one" element of `ℤᵐ⁰ = WithZero (Multiplicative ℤ)`, so that
  `v π = vOne` says that `π` is a uniformizer and that `v` is trivial on the units (`v u = 1`).
* `AutRigid L E` is *node C2 of the audit* (MotC2's `aut_functionField`), in exactly the form of
  `Submission/Work/MotC2/aut_functionField.lean`; `LAM` (`twist_iso_pointK`) consumes it, since the
  rigidity of the T-twist field is a rigidity statement for the automorphisms of `K̄(E)`.
* `LinkCertTInput K` is *node T8* of the design (MotK's `linkCert_T`), the census certificate for
  the `(K, h)`-link, stated generically in `(K, h)`; the assembly of `not_gen_three_of_val`
  consumes it.
-/

namespace Work.MotT

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine
open scoped WithZero

/-! ## §1 The twist field `K(C_h)` over an arbitrary base -/

/-- The algebraic closure of the base field, over which the twist is split. -/
abbrev KbK (K : Type) [Field K] := AlgebraicClosure K

/-- The function field `K̄(E)` of the model in which the T-twist is computed. -/
abbrev OmK {K : Type} [Field K] (D : Work.MotV.KleinData K) : Type :=
  FunctionField (D.E.baseChange (KbK K))

/-- A chosen fifth root of `h` in `K̄`. -/
def root5K {K : Type} [Field K] (h : K) : KbK K :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (algebraMap K (KbK K) h) (by norm_num : 0 < 5))

/-- The defining property of `root5K`. -/
theorem root5K_spec {K : Type} [Field K] (h : K) : root5K h ^ 5 = algebraMap K (KbK K) h :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (algebraMap K (KbK K) h)
    (by norm_num : 0 < 5))

/-- `root5K h ≠ 0` for `h ≠ 0`. -/
theorem root5K_ne_zero {K : Type} [Field K] {h : K} (hh : h ≠ 0) : root5K h ≠ 0 := by
  have h5 := root5K_spec h
  intro h0
  rw [h0, zero_pow (by norm_num : 5 ≠ 0)] at h5
  exact hh ((algebraMap K (KbK K)).injective (by simpa using h5.symm))

/-- The image of `root5K h` in `K̄(E)`. -/
abbrev wK {K : Type} [Field K] (D : Work.MotV.KleinData K) (h : K) : OmK D :=
  algebraMap (KbK K) (OmK D) (root5K h)

/-- `wK` is a fifth root of the twist parameter `h`. -/
theorem wK_pow_five {K : Type} [Field K] (D : Work.MotV.KleinData K) (h : K) :
    wK D h ^ 5 = algebraMap K (OmK D) h := by
  show (algebraMap (KbK K) (OmK D) (root5K h)) ^ 5 = _
  rw [← map_pow, root5K_spec, IsScalarTower.algebraMap_apply K (KbK K) (OmK D)]

/-- `wK D h ≠ 0` for `h ≠ 0`. -/
theorem wK_ne_zero {K : Type} [Field K] (D : Work.MotV.KleinData K) {h : K} (hh : h ≠ 0) :
    wK D h ≠ 0 := by
  have h5 := wK_pow_five D h
  intro h0
  rw [h0, zero_pow (by norm_num : 5 ≠ 0)] at h5
  exact hh ((algebraMap K (OmK D)).injective (by simpa using h5.symm))

/-- The twisted Klein coordinates `y_i = w^{-i} κ_i/κ_0`, `w^5 = h`, of the T-twist. -/
def twCoordK {K : Type} [Field K] (D : Work.MotV.KleinData K) (h : K) (i : Fin 5) : OmK D :=
  (wK D h)⁻¹ ^ (i : ℕ) *
    (Work.MotV.kleinCoord D (KbK K) i / Work.MotV.kleinCoord D (KbK K) 0)

/-- **T0.** The T-twist field `K(C_h) ⊆ K̄(E)` over an arbitrary base `K`, `h ∈ Kˣ`. -/
def twistFieldTK {K : Type} [Field K] (D : Work.MotV.KleinData K) (h : K) :
    IntermediateField K (OmK D) :=
  IntermediateField.adjoin K (Set.range (twCoordK D h))

/-- The defining identity of the twisted coordinates: `w^i · y_i = κ_i/κ_0`. -/
theorem pow_mul_twCoordK {K : Type} [Field K] (D : Work.MotV.KleinData K) (h : K) (hh : h ≠ 0)
    (i : Fin 5) :
    wK D h ^ (i : ℕ) * twCoordK D h i =
      Work.MotV.kleinCoord D (KbK K) i / Work.MotV.kleinCoord D (KbK K) 0 := by
  rw [twCoordK, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ (wK_ne_zero D hh), one_pow, one_mul]

/-! ## §2 The normalized valuation value -/

/-- The normalized "order one" element of `ℤᵐ⁰`: `v π = vOne` says `π` is a uniformizer.  Note
`v u = 1` says that `u` is a unit. -/
abbrev vOne : ℤᵐ⁰ := ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : ℤᵐ⁰)

/-! ## §3 The audit's `C2` and `T8` interfaces -/

/-- **Audit node C2** (MotC2's `aut_functionField`), the *conclusion* at an elliptic Weierstrass
curve over a field `L` with `j ≠ 0, 1728` (those two hypotheses belong to the *proof*, not to the
conclusion): every `L`-algebra automorphism of `L(E)` is a translation composed with `1` or with
`[-1]`, i.e. `Θ = τ_Q ∘ [ε]` with `ε ∈ {0, 1}`.

**Deviation from the design, forced by a defect of the design's form.**  The design (and
`Submission/Work/MotC2/aut_functionField.lean`, and the `hC2` hypothesis of
`Work.MotC.not_algEquiv_ratFunc_twistField`) write this as `∃ (Q) (ε : ℤˣ), Θ = τ_Q * [-1]^ε` with
`[-1]^ε` read as the integral power `(negAlgEquiv E) ^ (ε : ℤ)`.  Since `[-1]` is an involution,
that power equals `[-1]` for *both* `ε = ±1`, so the design's form asserts
`∀ Θ, ∃ Q, Θ = τ_Q ∘ [-1]` — which is false (the pure translations `τ_Q`, in particular `1`, are
not of this shape).  The corrected form below uses the honest exponent `ε : Fin 2`, i.e.
`(negAlgEquiv E) ^ (ε : ℕ)`, which is `1` for `ε = 0` and `[-1]` for `ε = 1`; the two forms are
compared in `Submission/Work/MotT/C2_DEFECT.md`.

This is a research-level input of another area (the `MotC2` chapter).  `LAM`
(`twist_iso_pointK`) consumes it as an explicit hypothesis, exactly as
`Work.MotC.not_algEquiv_ratFunc_twistField` (the S-twist analogue) does. -/
def AutRigid (L : Type) [Field L] [DecidableEq L] (E : WeierstrassCurve L) [E.IsElliptic] : Prop :=
  ∀ Θ : Work.MotC2.Func E ≃ₐ[L] Work.MotC2.Func E,
    ∃ (Q : E.toAffine.Point) (ε : Fin 2),
      Θ = Work.MotC2.transAlgEquiv E Q * (Work.MotC2.negAlgEquiv E) ^ (ε : ℕ)

/-- `AutRigid` at the base-changed curve `D.E.baseChange K̄` of a Klein model, with the two class
arguments (`DecidableEq`, `IsElliptic`) pinned to the instances that are in scope at `D.Good`; this
is the form in which the nodes of this area consume node C2. -/
noncomputable def autRigidBaseChange {K : Type} [Field K] (D : Work.MotV.KleinData K)
    (hD : D.Good) : Prop :=
  @AutRigid (KbK K) _ (Classical.decEq (KbK K)) (D.E.map (algebraMap K (KbK K)))
    (by haveI := hD.elliptic; infer_instance)

/-- **The C2 rigidity input of the T-route**: node C2 at every Klein model over `K`.  This is the
form in which the assemblies of this area (`not_gen_three_of_val`, `not_gen_three_of_place`,
`not_gen_three_functionField_charNeFive`) consume node C2. -/
def AutRigidInput (K : Type) [Field K] : Prop :=
  ∀ (D : Work.MotV.KleinData K) (hD : D.Good), autRigidBaseChange D hD

/-- **Audit node T8** (MotK's `linkCert_T`), the census certificate of the `(K, h)`-link, stated
generically in `(K, h)` as required by the design: the affine certificate `LinkCert K F₁ F₂` whose
`G`-side special divisor has class `RatFunc (twistFieldTK D h)` and whose `F`-side class is
`RatFunc (twistFieldTK D (h^2))`.

This belongs to the K-route (`Submission/Work/MotK`, node K4/K5), not to this area; the assembly
`not_gen_three_of_val` consumes it. -/
def LinkCertTInput (K : Type) [Field K] : Prop :=
  ∀ (D : Work.MotV.KleinData K), D.Good → ∀ h : K, h ≠ 0 →
    Nonempty (Work.MotV.LinkCert K (twistFieldTK D h) (twistFieldTK D (h ^ 2)))

/-- **Audit node T7**, in the form consumed by the assemblies: at the normalized valuation of any
uniformizer there are Klein data whose Klein parameters are units (so that the twisted-point
valuation lemma `Work.MotV.Work.MotV.tp` applies).

This is the statement of `Work.MotT.exists_kleinData_val` (for `ringChar K ≠ 5`), packaged as a
`Prop` so that the assemblies can take it as an explicit hypothesis. -/
def KleinDataValued (K : Type) [Field K] : Prop :=
  ∀ (v : Valuation K ℤᵐ⁰) {π : K}, v π = vOne →
    ∃ D : Work.MotV.KleinData K, D.Good ∧ v D.a = 1 ∧ v D.b = 1

/-! ## §4 Base change of Klein data (the bridge to route V) -/

/-- Base change of Klein data along `𝕜 → L`: the Klein parameters and the coordinate matrix are
mapped, the Weierstrass curve is base changed.  This is the dictionary that lets route V
(`Submission/Work/MotV`, `K = RatFunc 𝕜`) instantiate the generic nodes of this area. -/
def kleinDataBaseChange {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜) (L : Type) [Field L]
    [Algebra 𝕜 L] : Work.MotV.KleinData L where
  a := algebraMap 𝕜 L D.a
  b := algebraMap 𝕜 L D.b
  E := D.E.baseChange L
  coord := fun i m => algebraMap 𝕜 L (D.coord i m)

/-! ## §5 Elementary Klein-model lemmas -/

/-- The Klein Pfaffians are homogeneous of degree two in the Klein parameters `(a, b)`:
`kleinP (u a) (u b) x = u² kleinP a b x`.  This is what makes the Klein model
`(a, b) → (u a, u b)` (and hence `kleinData_normalise`) legitimate. -/
theorem kleinP_smul_ab {R : Type*} [CommRing R] (u a b : R) (x : Fin 5 → R) (k : Fin 5) :
    Work.MotK.kleinP (u * a) (u * b) x k = u ^ 2 * Work.MotK.kleinP a b x k := by
  fin_cases k <;>
    simp only [Work.MotK.kleinP_zero', Work.MotK.kleinP_one', Work.MotK.kleinP_two',
      Work.MotK.kleinP_three', Work.MotK.kleinP_four'] <;>
    simp only [Work.MotK.kleinP0, Work.MotK.kleinP1, Work.MotK.kleinP2, Work.MotK.kleinP3,
      Work.MotK.kleinP4] <;>
    first | refl_ring1 | ring

/-! ## §6 The ruling bridge (design node CR6) -/

/-- **CR6.**  Constants-only for `A` gives the *ruling* hypothesis of
`Work.MotC.algEquiv_ratFunc_cancel`: under a `𝕜`-algebra isomorphism `RatFunc A ≃ₐ[𝕜] RatFunc B`,
the image of a constant is a constant.  This is the bridge consumed by `certN3_of_linkCert`. -/
theorem ruling_of_constantsOnly {𝕜 A B : Type} [Field 𝕜] [Field A] [Field B] [Algebra 𝕜 A]
    [Algebra 𝕜 B] (hCO : Work.MotV.ConstantsOnly 𝕜 A) (θ : RatFunc A ≃ₐ[𝕜] RatFunc B) (a : A) :
    ∃ b : B, θ (algebraMap A (RatFunc A) a) = algebraMap B (RatFunc B) b := by
  obtain ⟨c, hc⟩ := hCO B (θ.toAlgHom.comp (IsScalarTower.toAlgHom 𝕜 A (RatFunc A))) a
  exact ⟨c, hc.symm⟩

end

end Work.MotT
