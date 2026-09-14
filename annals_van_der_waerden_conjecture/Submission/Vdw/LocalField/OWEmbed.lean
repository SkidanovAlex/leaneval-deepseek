import Mathlib
import Submission.Vdw.LocalField.OWClosure
import Submission.Vdw.LocalField.WildDifferent

open Classical
open Polynomial
open Filter
open minpoly
open scoped NumberField WithZero Valued
open IsLocalRing
open IsDedekindDomain
open UniqueFactorizationMonoid

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

/-!
# Local-field chapter (S1, sub-stone (b) COMPLETE): the 𝒪_W-embedding into
`kpInt`, `𝔪_W · kpInt = 𝔪^e`, and the ϖ-integrality over 𝒪_W

Setup (as in OWClosure/WUnramified): `W = Wk p P α = ℚ_p(ζ)` is the
Teichmüller subfield of `K_P = kpAdic p P` (`ζ := teich p P α`, `α ≠ 0`
with `hgen` making α generate `κ^×`), `𝒪_W = OW_subring p P α` the
valuation subring (elements of `W` with a `kpInt` representative),
`𝔪_W = OW_ker p P α` the maximal ideal (kernel of `resOW_hom : 𝒪_W → κ`),
`mS := maximalIdeal (kpInt p P)` the maximal ideal of the completed
valuation ring, `e := P.ramificationIdx ℤ`.

This module proves (Roadmap Session-96 sub-stone (b), complete):

* `owWitness` / `owWitness_value` / `owWitness_ext` — the unique `kpInt`
  representative of an integral element of `W` (existence by the `OW`
  membership, uniqueness by injectivity of `kpInt → kpAdic`);
* **`owToKpInt`** — THE embedding: the ring hom
  `𝒪_W →+* kpInt p P` sending each `w ∈ 𝒪_W` to its `kpInt`
  representative (`owToKpInt_value`: values agree in `K_P`;
  `owToKpInt_injective`: representatives are unique);
* `owToKpInt_pOW` — the base scalar is fixed: `owToKpInt p = (p : kpInt)`;
* **`OW_ker_map_eq_mS_pow_ramIdx`** — THE ideal relation
  `𝔪_W · kpInt = 𝔪^e`: `(OW_ker p P α).map (owToKpInt p P α) =
  mS ^ P.ramificationIdx ℤ`.  Proof: `OW_ker = (p)·𝒪_W`
  (`OW_ker_eq_span_pOW`, e(W)=1) maps to the principal ideal `(p : kpInt)`
  (`owToKpInt_pOW`), which is `mS^e` by WildDifferent sub-stone (a)
  (`mR_map_eq_span_p` + `mR_map_eq_mS_pow_ramIdx`).

Sub-stone (b3) COMPLETE (in this module): the integrality of the
uniformizer `ϖ := uniformizer p P` over `𝒪_W`:

* `qpScalarWk_value` / `qpScalar_mem_OW` — QpInt scalars of `W` are
  integral: `algebraMap (QpInt p) (Wk p P α) q` has the `kpInt`
  representative `algebraMap (QpAdic p) (kpAdic p P) (q : QpAdic p)`
  (value equality via the two scalar towers `QpInt → Wk → kpAdic` and
  `QpInt → QpAdic → kpAdic`);
* `qpIntToOW` — the scalar embedding `QpInt p →+* OW_subring p P α`
  (`RingHom.codRestrict` of the scalar algebraMap);
* `qpIntToOW_val` / `qpIntToOW_scalar_compat` — its value and the scalar
  compatibility `owToKpInt (ψ q) = algebraMap (QpInt p) (kpInt p P) q`
  (both sides are `q` in `K_P`);
* `owToKpIntAlgebra` — the global algebra instance making `kpInt p P` an
  `OW_subring p P α`-algebra (via `owToKpInt`);
* **`uniformizer_isIntegral_OW`** — `IsIntegral (OW_subring p P α)
  (uniformizer p P : kpInt p P)`: ϖ ∈ kpInt is integral over `QpInt`
  (`Algebra.IsIntegral.isIntegral` from the `Algebra.IsIntegral (QpInt p)
  (kpInt p P)` instance), and `QpInt → 𝒪_W → kpInt` is a scalar tower
  (`IsScalarTower.of_algebraMap_eq` from
  `qpIntToOW_scalar_compat`), so `IsIntegral.tower_top` transports the
  integrality to `𝒪_W`.

Integral closure (the (c)-prerequisite, also in this module):
`OW_subring` is integrally closed in `W` — every element of `Wk` that is a
root of a monic polynomial over `𝒪_W` lies in `𝒪_W`
(**`OW_subring_integrallyClosed`**).  Proof: the value of such an element
in `K_P` has norm ≤ 1 — the classical ultrametric domination argument
(`integral_norm_le_one`: a root of a monic polynomial with integral
coefficients cannot have norm > 1, since the leading term would strictly
dominate the lower terms) — and `mem_OW_of_norm_le_one` recovers the
membership.  This gives the coefficient-integrality ingredient for (c):
`f_ϖ := minpoly (Wk p P α) ϖ` monic of degree `e` with `OW_subring`-
coefficients, then (d) Eisenstein property, (e) `v_P(f_ϖ'(ϖ)) ≤
e·v_p(e)+e−1`, (f) local conductor-different + completion transport
closing `hwild` (see the Session-96/97 Roadmap blocks).

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The `kpInt`-witness of an integral element `w` of `W`: the unique
element of the valuation ring of `K_P` whose value equals `w` (existence by
the `OW` membership `w.2`, uniqueness by injectivity of `kpInt → kpAdic`). -/
noncomputable def owWitness (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (w : OW_subring p P α) : kpInt p P :=
  Classical.choose (show ∃ z : kpInt p P, (z : kpAdic p P) = (w.1 : kpAdic p P) from w.2)

/-- The witness represents its element: values agree in `K_P`. -/
lemma owWitness_value (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (w : OW_subring p P α) :
    ((owWitness p P α w : kpInt p P) : kpAdic p P) = (w.1 : kpAdic p P) :=
  Classical.choose_spec (show ∃ z : kpInt p P, (z : kpAdic p P) = (w.1 : kpAdic p P) from w.2)

/-- Any element with the same value is the witness (the coercion
`kpInt → kpAdic` is injective). -/
lemma owWitness_ext (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (w : OW_subring p P α) (z : kpInt p P)
    (hz : (z : kpAdic p P) = (w.1 : kpAdic p P)) : owWitness p P α w = z := by
  apply Subtype.ext
  exact (owWitness_value p P α w).trans hz.symm

/-- **The embedding `𝒪_W → kpInt`**: the ring hom sending each integral
element `w ∈ 𝒪_W ⊆ W` to its `kpInt` representative (well-defined by
`owWitness_ext`, a ring hom by representative arithmetic in `kpInt`). -/
noncomputable def owToKpInt (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) : OW_subring p P α →+* kpInt p P where
  toFun := fun w => owWitness p P α w
  map_zero' := by
    change owWitness p P α (0 : OW_subring p P α) = (0 : kpInt p P)
    apply owWitness_ext p P α (0 : OW_subring p P α) (0 : kpInt p P)
    change ((0 : kpInt p P) : kpAdic p P) = ((0 : Wk p P α) : kpAdic p P)
    simp
  map_one' := by
    change owWitness p P α (1 : OW_subring p P α) = (1 : kpInt p P)
    apply owWitness_ext p P α (1 : OW_subring p P α) (1 : kpInt p P)
    change ((1 : kpInt p P) : kpAdic p P) = ((1 : Wk p P α) : kpAdic p P)
    simp
  map_add' := by
    intro x y
    change owWitness p P α (x + y) = owWitness p P α x + owWitness p P α y
    apply owWitness_ext p P α (x + y) (owWitness p P α x + owWitness p P α y)
    calc
      ((owWitness p P α x + owWitness p P α y : kpInt p P) : kpAdic p P)
          = (owWitness p P α x : kpAdic p P) + (owWitness p P α y : kpAdic p P) := rfl
      _ = (x.1 : kpAdic p P) + (y.1 : kpAdic p P) := by
            rw [owWitness_value p P α x, owWitness_value p P α y]
      _ = ((x.1 + y.1 : Wk p P α) : kpAdic p P) := rfl
      _ = (((x + y : OW_subring p P α) : Wk p P α) : kpAdic p P) := rfl
  map_mul' := by
    intro x y
    change owWitness p P α (x * y) = owWitness p P α x * owWitness p P α y
    apply owWitness_ext p P α (x * y) (owWitness p P α x * owWitness p P α y)
    calc
      ((owWitness p P α x * owWitness p P α y : kpInt p P) : kpAdic p P)
          = (owWitness p P α x : kpAdic p P) * (owWitness p P α y : kpAdic p P) := rfl
      _ = (x.1 : kpAdic p P) * (y.1 : kpAdic p P) := by
            rw [owWitness_value p P α x, owWitness_value p P α y]
      _ = ((x.1 * y.1 : Wk p P α) : kpAdic p P) := rfl
      _ = (((x * y : OW_subring p P α) : Wk p P α) : kpAdic p P) := rfl

/-- The value of the embedding agrees with the value of the element. -/
lemma owToKpInt_value (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (w : OW_subring p P α) :
    (((owToKpInt p P α w : kpInt p P) : kpAdic p P)) = (w.1 : kpAdic p P) := by
  change ((owWitness p P α w : kpInt p P) : kpAdic p P) = (w.1 : kpAdic p P)
  exact owWitness_value p P α w

/-- The embedding is injective: two integral elements with the same
representative have the same value in `K_P`, hence are equal in `W`
(`Wk_coe_injective`). -/
lemma owToKpInt_injective (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) : Function.Injective (owToKpInt p P α) := by
  intro x y h
  apply Subtype.ext
  apply Wk_coe_injective p P α
  have hc := congrArg (fun z : kpInt p P => (z : kpAdic p P)) h
  exact (owToKpInt_value p P α x).symm.trans (hc.trans (owToKpInt_value p P α y))

/-- The embedding sends the base scalar `pOW = (p : 𝒪_W)` to the integer
`p` of `kpInt` (both represent the same value `p` in `K_P`). -/
lemma owToKpInt_pOW (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) :
    owToKpInt p P α (pOW p P α) = (p : kpInt p P) := by
  change owWitness p P α (pOW p P α) = (p : kpInt p P)
  apply owWitness_ext p P α (pOW p P α) (p : kpInt p P)
  dsimp [pOW]

/-- **`𝔪_W · kpInt = 𝔪^e`**: the maximal ideal of `𝒪_W` extends to the
`e := P.ramificationIdx ℤ`-th power of the maximal ideal of `kpInt`:
`(OW_ker p P α).map (owToKpInt p P α) = mS ^ P.ramificationIdx ℤ`.
Proof chain: `OW_ker = (p)·𝒪_W` (`OW_ker_eq_span_pOW` — e(W) = 1) maps
to the principal ideal generated by the integer `p` (`owToKpInt_pOW`), and
`(p)·kpInt = mS^e` is WildDifferent sub-stone (a)
(`mR_map_eq_span_p` + `mR_map_eq_mS_pow_ramIdx`). -/
theorem OW_ker_map_eq_mS_pow_ramIdx (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    (OW_ker p P α).map (owToKpInt p P α)
      = (maximalIdeal (kpInt p P)) ^ P.ramificationIdx ℤ := by
  classical
  let φ : OW_subring p P α →+* kpInt p P := owToKpInt p P α
  have hker : OW_ker p P α = Ideal.span ({pOW p P α} : Set (OW_subring p P α)) :=
    OW_ker_eq_span_pOW p P hα hgen
  calc
    (OW_ker p P α).map φ = (Ideal.span ({pOW p P α} : Set (OW_subring p P α))).map φ := by
          rw [hker]
    _ = Ideal.span ({(φ (pOW p P α) : kpInt p P)} : Set (kpInt p P)) := by
          rw [Ideal.map_span, Set.image_singleton]
    _ = Ideal.span ({(p : kpInt p P)} : Set (kpInt p P)) := by
          apply congrArg Ideal.span
          apply congrArg Set.singleton
          exact owToKpInt_pOW p P α
    _ = (maximalIdeal (kpInt p P)) ^ P.ramificationIdx ℤ := by
          rw [← mR_map_eq_span_p p P]
          exact mR_map_eq_mS_pow_ramIdx p P


/-! ## Sub-stone (b3): the uniformizer is integral over 𝒪_W -/

/-- Value of a `QpInt` scalar viewed in `W`, coerced to `K_P`: it is the
same scalar in `K_P` (via the scalar tower `QpInt → Wk → kpAdic`). -/
lemma qpScalarWk_value (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (q : QpInt p) :
    (((algebraMap (QpInt p) (Wk p P α) q : Wk p P α) : kpAdic p P))
      = algebraMap (QpInt p) (kpAdic p P) q := by
  rw [IsScalarTower.algebraMap_eq (R := QpInt p) (S := Wk p P α) (A := kpAdic p P)]
  rfl

/-- Membership: the `QpInt` scalar of `W` is integral (its `K_P` value
`algebraMap (QpAdic p) (kpAdic p P) (q : QpAdic p)` is the `kpInt`
witness). -/
lemma qpScalar_mem_OW (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (q : QpInt p) :
    (algebraMap (QpInt p) (Wk p P α) q : Wk p P α) ∈ OW p P α := by
  refine ⟨⟨algebraMap (QpAdic p) (kpAdic p P) (q : QpAdic p),
    algebraMap_mem_kpInt (p := p) (P := P) q⟩, ?_⟩
  change algebraMap (QpAdic p) (kpAdic p P) (q : QpAdic p)
      = (((algebraMap (QpInt p) (Wk p P α) q : Wk p P α) : kpAdic p P))
  rw [qpScalarWk_value]
  rw [IsScalarTower.algebraMap_eq (R := QpInt p) (S := QpAdic p) (A := kpAdic p P)]
  rfl

/-- The scalar embedding `QpInt p → 𝒪_W`: base scalars of `W = ℚ_p(ζ)`
are integral (`RingHom.codRestrict` of the scalar algebraMap). -/
noncomputable def qpIntToOW (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) : QpInt p →+* OW_subring p P α :=
  RingHom.codRestrict (algebraMap (QpInt p) (Wk p P α)) (OW_subring p P α)
    (fun q => by
      change (algebraMap (QpInt p) (Wk p P α) q : Wk p P α) ∈ OW p P α
      exact qpScalar_mem_OW p P α q)

/-- The value of the codRestricted scalar is the scalar itself:
`(qpIntToOW q).1 = algebraMap (QpInt p) (Wk p P α) q`. -/
lemma qpIntToOW_val (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (q : QpInt p) :
    ((qpIntToOW p P α q : OW_subring p P α) : Wk p P α) = algebraMap (QpInt p) (Wk p P α) q := by
  dsimp [qpIntToOW]

/-- Scalar compatibility: the embedding of `𝒪_W` into `kpInt` fixes the
base scalars — `owToKpInt (ψ q) = algebraMap (QpInt p) (kpInt p P) q`
(both sides are the scalar `q` in `K_P`). -/
lemma qpIntToOW_scalar_compat (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (q : QpInt p) :
    owToKpInt p P α (qpIntToOW p P α q) = algebraMap (QpInt p) (kpInt p P) q := by
  apply owWitness_ext p P α (qpIntToOW p P α q) (algebraMap (QpInt p) (kpInt p P) q)
  calc
    ((algebraMap (QpInt p) (kpInt p P) q : kpInt p P) : kpAdic p P)
        = algebraMap (QpInt p) (kpAdic p P) q := by
          rw [algebraMap_QpInt_kpInt_eq]
          rfl
    _ = (((qpIntToOW p P α q : OW_subring p P α) : Wk p P α) : kpAdic p P) := by
          rw [qpIntToOW_val]
          rw [qpScalarWk_value]

/-- The `kpInt`-algebra structure of `OW_subring` (via the embedding
`owToKpInt`): makes integrality-over-`𝒪_W` statements well-formed. -/
noncomputable instance owToKpIntAlgebra (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) : Algebra (OW_subring p P α) (kpInt p P) :=
  RingHom.toAlgebra (owToKpInt p P α)

/-- **The uniformizer is integral over 𝒪_W**: `ϖ := uniformizer p P`, as an
element of the `OW_subring`-algebra `kpInt`, is a root of a monic
polynomial over `𝒪_W`.

Proof: ϖ ∈ kpInt is integral over `QpInt` (`kpInt` is integral over
`ℤ_[p]`: `Algebra.IsIntegral.isIntegral`); the base scalars embed
`QpInt → 𝒪_W` (`qpIntToOW`) compatibly with `𝒪_W → kpInt`
(`owToKpInt`, `qpIntToOW_scalar_compat`), so
`IsScalarTower.of_algebraMap_eq` makes `QpInt → 𝒪_W → kpInt` a scalar
tower, and `IsIntegral.tower_top` transports the integrality from
`QpInt` to `OW_subring`. -/
theorem uniformizer_isIntegral_OW (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) :
    IsIntegral (OW_subring p P α) (uniformizer p P : kpInt p P) := by
  classical
  letI : Algebra (QpInt p) (OW_subring p P α) := RingHom.toAlgebra (qpIntToOW p P α)
  haveI hst : IsScalarTower (QpInt p) (OW_subring p P α) (kpInt p P) := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro q
    exact (qpIntToOW_scalar_compat p P α q).symm
  exact IsIntegral.tower_top (R := QpInt p) (A := OW_subring p P α) (B := kpInt p P)
    (Algebra.IsIntegral.isIntegral (uniformizer p P))



/-! ## Integral closure: 𝒪_W is integrally closed in W (the (c)-prerequisite)

The valuation subring `𝒪_W = OW_subring p P α` of the subfield
`W = Wk p P α` of `K_P` is the unit ball of `W` in the `K_P`-norm
(`OW_norm_le_one` / `mem_OW_of_norm_le_one`), and the unit ball of a
valued field is integrally closed: a root of a monic polynomial with
integral coefficients has norm ≤ 1 (`integral_norm_le_one` — ultrametric
domination: with `‖y‖ > 1` the leading term `y^n` strictly dominates
`Σ_{i<n} c_i y^i`, so they cannot cancel).  This is the coefficient-
integrality input that (c) needs: coefficients of `minpoly (Wk) ϖ` in `𝒪_W`.
-/

/-- Nonarchimedean sums: if every term has norm ≤ B (B ≥ 0), so does the
sum (`IsNonarchimedean (‖·‖ : R → ℝ)`, Finset induction). -/
lemma norm_sum_le_of_all_le {R : Type*} [SeminormedAddCommGroup R]
    (hna : IsNonarchimedean (‖·‖ : R → ℝ))
    {ι : Type*} (s : Finset ι) (z : ι → R) {B : ℝ} (hB : 0 ≤ B)
    (hz : ∀ i ∈ s, ‖z i‖ ≤ B) :
    ‖∑ i ∈ s, z i‖ ≤ B := by
  classical
  revert hz
  let motive : Finset ι → Prop := fun t => (∀ i ∈ t, ‖z i‖ ≤ B) → ‖∑ i ∈ t, z i‖ ≤ B
  change motive s
  refine Finset.induction_on s ?_ ?_
  · intro h0
    simp [hB]
  · intro a s' has' ih hmem
    have hza : ‖z a‖ ≤ B := hmem a (by simp)
    have hrest : ‖∑ i ∈ s', z i‖ ≤ B := ih (fun i hi => hmem i (by simp [hi]))
    rw [Finset.sum_insert has']
    calc
      ‖z a + ∑ i ∈ s', z i‖ ≤ max ‖z a‖ ‖∑ i ∈ s', z i‖ := hna _ _
      _ ≤ B := max_le hza hrest

/-- OW-membership gives norm ≤ 1: an element of `W` with a `kpInt`
representative has value-norm at most one (its representative does). -/
lemma OW_norm_le_one (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P)
    (w : Wk p P α) (hw : w ∈ OW p P α) :
    ‖(w : kpAdic p P)‖ ≤ 1 := by
  rcases hw with ⟨z, hz⟩
  calc
    ‖(w : kpAdic p P)‖ = ‖((z : kpInt p P) : kpAdic p P)‖ := by rw [← hz]
    _ ≤ 1 := norm_le_one p P z

/-- **Ultrametric domination**: an element `w ∈ W` that is a root of a
monic polynomial over `𝒪_W` has value-norm ≤ 1 in `K_P`.  Proof: push the
monic equation into `K_P` (`hom_eval₂` through the algebra map
`Wk → kpAdic`), decompose at the degree (`eval₂_eq_sum_range` +
`Finset.range_add_one`), and bound the lower-term sum by `‖y‖^(n−1)`
(nonarchimedean sum lemma + `‖coeff‖ ≤ 1` + `pow_le_pow_right₀`); if
`‖y‖ > 1` this contradicts `‖y‖^n = ‖Σ lower‖`.  The degree-zero case is
impossible (a monic constant polynomial is `C 1`). -/
lemma integral_norm_le_one (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (w : Wk p P α)
    (g : Polynomial (OW_subring p P α)) (hg : g.Monic)
    (he : Polynomial.eval₂ (OW_subring p P α).subtype w g = 0) :
    ‖(w : kpAdic p P)‖ ≤ 1 := by
  classical
  let s : Subring (Wk p P α) := OW_subring p P α
  let φ : Wk p P α →+* kpAdic p P := algebraMap (Wk p P α) (kpAdic p P)
  let h : s →+* kpAdic p P := φ.comp s.subtype
  let y : kpAdic p P := (w : kpAdic p P)
  have heval : Polynomial.eval₂ h y g = 0 := by
    change Polynomial.eval₂ (φ.comp s.subtype) (φ w) g = 0
    have hm := Polynomial.hom_eval₂ g s.subtype φ w
    have hzero : φ (Polynomial.eval₂ s.subtype w g) = 0 := by
      rw [he]
      simp
    rw [← hm]
    exact hzero
  have hcoeff : ∀ i : ℕ, ‖h (g.coeff i)‖ ≤ 1 := by
    intro i
    change ‖φ (((g.coeff i : s) : Wk p P α))‖ ≤ 1
    have hmem : ((g.coeff i : s) : Wk p P α) ∈ OW p P α := by
      exact (g.coeff i : OW_subring p P α).2
    exact OW_norm_le_one p P α ((g.coeff i : s) : Wk p P α) hmem
  have heq0 : (∑ i ∈ Finset.range (g.natDegree + 1), h (g.coeff i) * y ^ i) = 0 := by
    exact (Polynomial.eval₂_eq_sum_range h y).symm.trans heval
  by_contra hnot
  have hy1 : 1 < ‖y‖ := lt_of_not_ge hnot
  by_cases hn0 : g.natDegree = 0
  · have hC : g = Polynomial.C (1 : s) := by
      have hc : g.coeff 0 = 1 := by
        have hcn := hg.coeff_natDegree
        simpa [hn0] using hcn
      exact (Polynomial.eq_C_of_natDegree_eq_zero hn0).trans (by rw [hc])
    have h1 : Polynomial.eval₂ h y g = 1 := by
      rw [hC]
      simp
    exact (one_ne_zero : (1 : kpAdic p P) ≠ 0) (h1.symm.trans heval)
  · have hnpos : 1 ≤ g.natDegree := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hn0)
    have hsplit : (∑ i ∈ Finset.range (g.natDegree + 1), h (g.coeff i) * y ^ i)
        = h (g.coeff g.natDegree) * y ^ g.natDegree
          + (∑ i ∈ Finset.range g.natDegree, h (g.coeff i) * y ^ i) := by
      rw [Finset.range_add_one, Finset.sum_insert (by simp)]
    have hlead : h (g.coeff g.natDegree) = 1 := by
      rw [hg.coeff_natDegree]
      simp [h]
    have heq' : y ^ g.natDegree
        + (∑ i ∈ Finset.range g.natDegree, h (g.coeff i) * y ^ i) = 0 := by
      have hs := heq0
      rw [hsplit, hlead, one_mul] at hs
      simpa using hs
    have hS : ‖∑ i ∈ Finset.range g.natDegree, h (g.coeff i) * y ^ i‖ ≤ ‖y‖ ^ (g.natDegree - 1) := by
      apply norm_sum_le_of_all_le (R := kpAdic p P) (s := Finset.range g.natDegree)
        (z := fun i => h (g.coeff i) * y ^ i)
        (B := ‖y‖ ^ (g.natDegree - 1))
        (IsUltrametricDist.isNonarchimedean_norm) (pow_nonneg (norm_nonneg y) _)
      intro i hi
      have hi' : i < g.natDegree := Finset.mem_range.mp hi
      calc
        ‖h (g.coeff i) * y ^ i‖ = ‖h (g.coeff i)‖ * ‖y ^ i‖ := by rw [norm_mul]
        _ = ‖h (g.coeff i)‖ * ‖y‖ ^ i := by rw [norm_pow]
        _ ≤ 1 * ‖y‖ ^ i := by
          exact mul_le_mul_of_nonneg_right (hcoeff i) (pow_nonneg (norm_nonneg y) i)
        _ ≤ ‖y‖ ^ (g.natDegree - 1) := by
          have hle : i ≤ g.natDegree - 1 := by omega
          simpa using (pow_le_pow_right₀ hy1.le hle)
    have hyneq : ‖y ^ g.natDegree‖ = ‖∑ i ∈ Finset.range g.natDegree, h (g.coeff i) * y ^ i‖ := by
      have heqneg : y ^ g.natDegree = - (∑ i ∈ Finset.range g.natDegree, h (g.coeff i) * y ^ i) :=
        eq_neg_of_add_eq_zero_left heq'
      rw [heqneg, norm_neg]
    have hchain : ‖y‖ ^ g.natDegree ≤ ‖y‖ ^ (g.natDegree - 1) := by
      rw [← norm_pow y g.natDegree, hyneq]
      exact hS
    have hstrict : ‖y‖ ^ (g.natDegree - 1) < ‖y‖ ^ g.natDegree := by
      exact pow_lt_pow_right₀ hy1 (by omega : g.natDegree - 1 < g.natDegree)
    exact (lt_irrefl (‖y‖ ^ g.natDegree)) (lt_of_le_of_lt hchain hstrict)

/-- **𝒪_W is integrally closed in W**: any element of `Wk p P α` that is a
root of a monic polynomial over `OW_subring p P α` (evaluated through the
subring inclusion) lies in `OW_subring p P α` — the integral-closure
statement for the valuation subring `𝒪_W` of the subfield `W = ℚ_p(ζ)`.

Proof: the monic annihilator has coefficients of value-norm ≤ 1
(`hcoeff`/`OW_norm_le_one`), so `integral_norm_le_one` gives
`‖(w : kpAdic)‖ ≤ 1` (ultrametric domination); `mem_OW_of_norm_le_one`
gives `w ∈ OW`, i.e. `w ∈ OW_subring`. -/
theorem OW_subring_integrallyClosed (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (w : Wk p P α)
    (hint : ∃ g : Polynomial (OW_subring p P α),
      g.Monic ∧ Polynomial.eval₂ (OW_subring p P α).subtype w g = 0) :
    w ∈ OW_subring p P α := by
  rcases hint with ⟨g, hg, he⟩
  have hn : ‖(w : kpAdic p P)‖ ≤ 1 := integral_norm_le_one p P α w g hg he
  have how : w ∈ OW p P α := mem_OW_of_norm_le_one p P α w hn
  simpa [OW_subring] using how



/-! ## (c)(i): the field-side f_ϖ — `minpoly` over the unramified subfield W

The uniformizer `ϖ := uniformizer p P` of `kpInt` is an element of
`K_P = kpAdic p P`, an element of the field-extension `kpAdic` over the
unramified subfield `W = Wk p P α`.  The minpoly-over-field instance
plumbing (Roadmap Session-101, (c)(i)):

* `[Algebra (Wk p P α) (kpAdic p P)]`, `[IsScalarTower (QpAdic p)
  (Wk p P α) (kpAdic p P)]` — synthesize (`infer_instance`, Intermediate-
  Field algebra);
* `[Algebra (kpInt p P) (kpAdic p P)]` and
  `[Algebra (OW_subring p P α) (kpAdic p P)]` — also synthesize
  (valuation-subring/subring algebras; NOTE `[Algebra (OW_subring)
  (Wk)]` does NOT synthesize — TC timeout — use local
  `RingHom.toAlgebra (OW_subring p P α).subtype` there, as in the (b3)
  proof and the integral-closure section);
* `uniformizer_isIntegral_Wk` — ϖ is integral over `W` (ϖ ∈ kpAdic is
  integral over `QpAdic` by `IsIntegral.of_finite` — `kpAdic` is a finite
  `QpAdic`-algebra — and `IsIntegral.tower_top` transports to the
  intermediate field `W`);
* **`fϖWk`** — `f_ϖ := minpoly (Wk p P α) ((ϖ : kpInt) : kpAdic p P)`,
  with `fϖWk_monic` (monic) and `fϖWk_aeval` (annihilates ϖ).

The remaining (c) steps (recorded in Roadmap Session-100/101): (c)(ii)
the classical coefficients-are-integral step (coefficients of `minpoly
(Wk) x` are integral over `OW_subring` whenever `x` is — via the
`isIntegrallyClosed_eq_field_fractions`/`minpoly.ofSubring`-type
machinery, needing the `IsFractionRing (OW_subring p P α) (Wk p P α)`
and abstract-`IsIntegrallyClosed (OW_subring p P α)` instances built from
`OW_subring_integrallyClosed` + `Wk = Frac(𝒪_W)`) followed by
`OW_subring_integrallyClosed` to land the coefficients in 𝒪_W; (c)(iii)
degree `e := P.ramificationIdx ℤ` via `finrank_kpAdic_over_Wk_eq_ramIdx`
+ `IntermediateField.adjoin.finrank` + K_P = W(ϖ); (d)-(f) Eisenstein
route.
-/

/-- ϖ is integral over the unramified subfield `W = ℚ_p(ζ)`: ϖ ∈ kpAdic is
integral over `QpAdic` (kpAdic is a finite `QpAdic`-algebra,
`IsIntegral.of_finite`) and `W` is an intermediate field
(`IsIntegral.tower_top`). -/
lemma uniformizer_isIntegral_Wk (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) :
    IsIntegral (Wk p P α) (((uniformizer p P : kpInt p P) : kpAdic p P)) := by
  exact IsIntegral.tower_top (R := QpAdic p) (A := Wk p P α) (B := kpAdic p P)
    (IsIntegral.of_finite (QpAdic p) (((uniformizer p P : kpInt p P) : kpAdic p P)))

/-- **f_ϖ := minpoly of the uniformizer over `W`** — the field-side minimal
polynomial that the Eisenstein route works with. -/
noncomputable def fϖWk (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) : Polynomial (Wk p P α) :=
  minpoly (Wk p P α) (((uniformizer p P : kpInt p P) : kpAdic p P))

/-- f_ϖ is monic. -/
lemma fϖWk_monic (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) : (fϖWk p P α).Monic := by
  exact minpoly.monic (uniformizer_isIntegral_Wk p P α)

/-- f_ϖ annihilates ϖ. -/
lemma fϖWk_aeval (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) :
    aeval (((uniformizer p P : kpInt p P) : kpAdic p P)) (fϖWk p P α) = 0 := by
  exact minpoly.aeval (Wk p P α) (((uniformizer p P : kpInt p P) : kpAdic p P))






/-! ## (c)(ii) COMPLETE: the coefficients of f_ϖ lie in 𝒪_W

The classical coefficients-are-integral step, assembled in this module:

* local instances (all inside the proof of `fϖWk_coeff_mem_OW`):
  `[Algebra (OW_subring p P α) (Wk p P α)] := RingHom.toAlgebra
  (OW_subring p P α).subtype`; `FaithfulSMul` (from the injective subtype
  algebraMap, `Subtype.ext`); **`IsFractionRing (OW_subring p P α)
  (Wk p P α)`** via `IsFractionRing.of_field` — surjectivity of the
  fraction map by the two cases `‖z‖ ≤ 1` (`z ∈ 𝒪_W`,
  `mem_OW_of_norm_le_one`) and `‖z‖ > 1` (`z = 1/z⁻¹`, `z⁻¹ ∈ 𝒪_W` via
  `norm_inv` + `inv_le_one₀`); **`IsIntegrallyClosedIn (OW_subring)
  (Wk)`** via `isIntegrallyClosedIn_iff` from `OW_subring_integrallyClosed`
  (membership form) + the `aeval`↔`eval₂` identification;
  `IsIntegrallyClosed.of_isIntegrallyClosedIn` gives the abstract
  `IsIntegrallyClosed (OW_subring)`; the tower
  `IsScalarTower (OW_subring) (Wk) (kpAdic)` is `rfl`-level (the inferred
  `[Algebra (OW_subring) (kpAdic)]` is the Wk-route); the tower
  `(OW_subring) → (kpInt) → (kpAdic)` via `owToKpInt_value`;
* `hϖint` — `IsIntegral (OW_subring) ((ϖ : kpInt) : kpAdic)` (map of the
  (b3) integrality along the `kpInt`-tower);
* `minpoly.isIntegrallyClosed_eq_field_fractions'` (R := OW_subring,
  K := Wk, S := kpAdic) identifies `fϖWk = (minpoly (OW_subring) s).map
  (algebraMap (OW_subring) (Wk))`, whose coefficients are values of
  𝒪_W-elements;

**`fϖWk_coeff_mem_OW`** — THE theorem (instance-free statement):
`∀ i : ℕ, (fϖWk p P α).coeff i ∈ OW_subring p P α` — the Eisenstein route's
coefficient-integrality input for `f_ϖ` (Roadmap Session-102).  Remaining
(c) steps: (c)(iii) `natDegree (fϖWk p P α) = P.ramificationIdx ℤ` via
`finrank_kpAdic_over_Wk_eq_ramIdx` + `IntermediateField.adjoin.finrank`
+ K_P = W(ϖ), and the Eisenstein/derivative/conductor steps (d)-(f).
-/

/-- (c)(ii): the coefficients of f_ϖ = minpoly over W of the uniformizer lie
in OW_subring. -/
theorem fϖWk_coeff_mem_OW (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) : ∀ i : ℕ, (fϖWk p P α).coeff i ∈ OW_subring p P α := by
  classical
  intro i
  let A : Subring (Wk p P α) := OW_subring p P α
  letI : Algebra A (Wk p P α) := RingHom.toAlgebra A.subtype
  -- FaithfulSMul
  have hfsmul : FaithfulSMul A (Wk p P α) := by
    refine ⟨fun {m₁ m₂} h => ?_⟩
    apply Subtype.ext
    have h1m : m₁ • (1 : Wk p P α) = algebraMap A (Wk p P α) m₁ := by
      rw [Algebra.smul_def, mul_one]
    have h2m : m₂ • (1 : Wk p P α) = algebraMap A (Wk p P α) m₂ := by
      rw [Algebra.smul_def, mul_one]
    have hA : algebraMap A (Wk p P α) m₁ = algebraMap A (Wk p P α) m₂ := by
      rw [← h1m, ← h2m]
      exact h 1
    exact hA
  haveI : FaithfulSMul A (Wk p P α) := hfsmul
  -- IsFractionRing A (Wk)
  haveI hfr : IsFractionRing A (Wk p P α) := by
    apply IsFractionRing.of_field
    intro z
    by_cases hz : ‖(z : kpAdic p P)‖ ≤ 1
    · have hmem : z ∈ OW p P α := mem_OW_of_norm_le_one p P α z hz
      refine ⟨⟨z, hmem⟩, 1, ?_⟩
      have hA1 : algebraMap A (Wk p P α) (1 : A) = 1 := map_one _
      have hAz : algebraMap A (Wk p P α) ⟨z, hmem⟩ = z := rfl
      rw [hA1, hAz]
      rw [div_one]
    · have hz1 : 1 < ‖(z : kpAdic p P)‖ := lt_of_not_ge hz
      have hzinv : ‖(((z : Wk p P α)⁻¹) : kpAdic p P)‖ ≤ 1 := by
        have hni : ‖(((z : Wk p P α)⁻¹) : kpAdic p P)‖ = ‖(z : kpAdic p P)‖⁻¹ := by
          exact norm_inv (z : kpAdic p P)
        rw [hni]
        exact (inv_le_one₀ (lt_trans zero_lt_one hz1)).mpr (le_of_lt hz1)
      have hmeminv : ((z : Wk p P α)⁻¹) ∈ OW p P α :=
        mem_OW_of_norm_le_one p P α ((z : Wk p P α)⁻¹) hzinv
      have hz0 : (z : Wk p P α) ≠ 0 := by
        intro h0
        have hk : (z : kpAdic p P) = 0 := congrArg (fun x : Wk p P α => (x : kpAdic p P)) h0
        rw [hk, norm_zero] at hz1
        exact (lt_irrefl (0 : ℝ)) (lt_trans zero_lt_one hz1)
      refine ⟨1, ⟨(z : Wk p P α)⁻¹, hmeminv⟩, ?_⟩
      have hA1 : algebraMap A (Wk p P α) (1 : A) = 1 := map_one _
      have hAv : algebraMap A (Wk p P α) ⟨(z : Wk p P α)⁻¹, hmeminv⟩ = (z : Wk p P α)⁻¹ := rfl
      rw [hA1, hAv]
      field_simp [hz0]
  -- IsIntegrallyClosedIn A (Wk)
  have hclosedIn : @IsIntegrallyClosedIn A (Wk p P α) _ _ (RingHom.toAlgebra A.subtype) := by
    rw [isIntegrallyClosedIn_iff]
    constructor
    · -- algebraMap injective
      intro x y h
      exact Subtype.ext h
    · intro x hx
      -- hx : IsIntegral A x; convert to the membership theorem's form
      rcases hx with ⟨g, hg, hgx⟩
      have hgx' : Polynomial.eval₂ A.subtype x g = 0 := by
        -- aeval x g with the toAlgebra instance = eval₂ A.subtype x g
        change Polynomial.eval₂ (algebraMap A (Wk p P α)) x g = 0
        simpa using hgx  -- aeval = eval₂ algebraMap
      have hmem : x ∈ A := OW_subring_integrallyClosed p P α x ⟨g, hg, hgx'⟩
      refine ⟨⟨x, hmem⟩, ?_⟩
      rfl
  haveI : IsIntegrallyClosedIn A (Wk p P α) := hclosedIn
  haveI hic : IsIntegrallyClosed A :=
    IsIntegrallyClosed.of_isIntegrallyClosedIn A (Wk p P α)
  -- tower A → Wk → kpAdic
  haveI htower : IsScalarTower A (Wk p P α) (kpAdic p P) := by
    refine IsScalarTower.of_algebraMap_eq ?_
    intro c
    calc
      algebraMap A (kpAdic p P) c = (((c : A) : Wk p P α) : kpAdic p P) := by rfl
      _ = algebraMap (Wk p P α) (kpAdic p P) ((c : A) : Wk p P α) := by rfl
  -- ϖ integral over A in kpAdic
  have hϖint : IsIntegral A (((uniformizer p P : kpInt p P) : kpAdic p P)) := by
    have hb3 : IsIntegral A (uniformizer p P : kpInt p P) := by
      simpa [A] using uniformizer_isIntegral_OW p P α
    -- need tower A → kpInt → kpAdic
    haveI htk : IsScalarTower A (kpInt p P) (kpAdic p P) := by
      refine IsScalarTower.of_algebraMap_eq ?_
      intro c
      calc
        algebraMap A (kpAdic p P) c = (((c : A) : Wk p P α) : kpAdic p P) := by rfl
        _ = (((owToKpInt p P α c : kpInt p P) : kpAdic p P)) := by
              exact (owToKpInt_value p P α c).symm
        _ = algebraMap (kpInt p P) (kpAdic p P) (owToKpInt p P α c) := by rfl
    exact hb3.map (IsScalarTower.toAlgHom A (kpInt p P) (kpAdic p P))
  -- apply isIntegrallyClosed_eq_field_fractions'
  have hmain := isIntegrallyClosed_eq_field_fractions' (R := A) (K := Wk p P α) (S := kpAdic p P)
    (s := (((uniformizer p P : kpInt p P) : kpAdic p P))) hϖint
  -- hmain : minpoly (Wk) s = (minpoly A s).map (algebraMap A (Wk))
  -- fϖWk = minpoly (Wk) s: rfl
  -- conclusion: coeff i membership
  have hci : (fϖWk p P α).coeff i ∈ A := by
    change (minpoly (Wk p P α) (((uniformizer p P : kpInt p P) : kpAdic p P))).coeff i ∈ A
    rw [hmain]
    rw [coeff_map]
    change ((((minpoly A (((uniformizer p P : kpInt p P) : kpAdic p P))).coeff i : A) : Wk p P α)) ∈ A
    exact ((minpoly A (((uniformizer p P : kpInt p P) : kpAdic p P))).coeff i : A).2
  simpa [A] using hci

/-! ## (c)(iii) opened: `natDegree (fϖWk p P α) = P.ramificationIdx ℤ`

Algebraic reduction (this module):

* `fϖWk_natDegree_eq_finrank_adjoin` — `natDegree (fϖWk p P α) =
  Module.finrank (Wk p P α) (adjoin (Wk p P α) {ϖ})` via
  `IntermediateField.adjoin.finrank` (`ϖ` is integral over `Wk`:
  `uniformizer_isIntegral_Wk`); `Module.Finite (Wk) (adjoin …)` and
  `Module.Finite (Wk) (kpAdic)` synthesize.

So (c)(iii) reduces to the generation statement
`adjoin (Wk p P α) {ϖ} = ⊤` (equivalently its `finrank (Wk)` equals
`finrank (Wk) (kpAdic p P) = P.ramificationIdx ℤ`, the latter by
`TowerDegree.finrank_kpAdic_over_Wk_eq_ramIdx (hα) (hgen)`).  The two
classical routes (recorded in Roadmap Session-103; each a dedicated
sub-stone): (I) density + closedness — every `x ∈ kpInt` is the limit of
𝒪_W[ϖ]-partial sums (each residue lifts to 𝒪_W because
`resOW_hom : 𝒪_W → κ` is surjective onto `kpInt ⧸ maximalIdeal`), and
`adjoin (Wk){ϖ}` is closed in the complete space `kpAdic` as a finite-
dimensional `Wk`-subspace; (II) the value-group argument — since ϖ is a
uniformizer of `K_P` (`maximalIdeal = (ϖ)`), ϖ ∈ `Wk(ϖ)` forces
`e_{K_P/Wk(ϖ)} = 1`, so `[K_P : Wk(ϖ)] = 1`.
-/

/-- (c)(iii), algebraic half: `natDegree (fϖWk p P α)` equals the degree of
the intermediate field `Wk(ϖ) ⊆ K_P` over `Wk` (`IntermediateField.adjoin.finrank`,
ϖ integral over `Wk` by `uniformizer_isIntegral_Wk`).  Combined with
`finrank_kpAdic_over_Wk_eq_ramIdx` this gives `natDegree f_ϖ = e` once
`adjoin (Wk p P α) {ϖ} = ⊤` (K_P = W(ϖ)) is established. -/
lemma fϖWk_natDegree_eq_finrank_adjoin (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) :
    Module.finrank (Wk p P α) (IntermediateField.adjoin (Wk p P α)
      ({(((uniformizer p P : kpInt p P) : kpAdic p P))} : Set (kpAdic p P)))
      = (fϖWk p P α).natDegree := by
  exact IntermediateField.adjoin.finrank (uniformizer_isIntegral_Wk p P α)



/-! ## Route (I) for `K_P = W(ϖ)`: the 𝒪_W[ϖ]-partial-sum approximation

First inventory items (Roadmap Session-103/104), each self-contained:

* `resOW_hom_eq_mk_owToKpInt` — the identification
  `resOW_hom p P α w = mk (owToKpInt p P α w)` (both are the reduction of
  the same `kpInt` witness — `rfl` after unfolding);
* **`lift_residue_to_OW`** — the LIFTING STEP: every `x : kpInt p P`
  differs from an 𝒪_W-element by an element of the maximal ideal:
  `∃ c : OW_subring p P α, x - owToKpInt p P α c ∈ maximalIdeal (kpInt p P)`
  (reduce `x` to its residue in `κ = kpInt ⧸ 𝔪`; `resOW_hom_surjective`
  (needs `hα`, `hgen`) produces `c ∈ 𝒪_W` with the same reduction).

The WildDifferent engine lemma
`uniformizer_mul_mem_maximalIdeal_pow_succ` (ϖ^n·𝔪 ⊆ 𝔪^{n+1}) is the other
input of the partial-sum induction that shows every `x ∈ kpInt` is the
limit of 𝒪_W[ϖ]-polynomials (→ density of `adjoin (Wk){ϖ}`), completing
with the finite-dimensional-subspace closedness of `adjoin (Wk){ϖ}` in the
complete `kpAdic`.
-/

/-- The reduction `𝒪_W → κ` is the residue of the embedded `kpInt` element:
`resOW_hom p P α w = mk (owToKpInt p P α w)` for every `w : 𝒪_W` (both
reduce the same `kpInt` witness). -/
lemma resOW_hom_eq_mk_owToKpInt (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (w : OW_subring p P α) :
    resOW_hom p P α w =
      Ideal.Quotient.mk (maximalIdeal (kpInt p P)) (owToKpInt p P α w) := by
  unfold resOW_hom owToKpInt owWitness resOW
  rfl

/-- **Lifting step** (Route (I)): every `x ∈ kpInt` differs from an element
of `𝒪_W` by an element of the maximal ideal — the reduction map
`𝒪_W → κ = kpInt ⧸ 𝔪` is surjective (`resOW_hom_surjective`), and the
reduction of the embedded element is the residue of `x`. -/
lemma lift_residue_to_OW (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    (x : kpInt p P) :
    ∃ c : OW_subring p P α, x - owToKpInt p P α c ∈ maximalIdeal (kpInt p P) := by
  classical
  let mkS : kpInt p P →+* kap p P := Ideal.Quotient.mk (maximalIdeal (kpInt p P))
  rcases (resOW_hom_surjective (p := p) (P := P) hα hgen) (mkS x) with ⟨w, hw⟩
  have hident : resOW_hom p P α w = mkS (owToKpInt p P α w) := by
    simpa [mkS] using resOW_hom_eq_mk_owToKpInt p P α w
  refine ⟨w, ?_⟩
  have hz : mkS x = mkS (owToKpInt p P α w) := by
    rw [← hident]
    exact hw.symm
  have h0 : mkS (x - owToKpInt p P α w) = 0 := by
    rw [map_sub, sub_eq_zero]
    exact hz
  exact (Ideal.Quotient.eq_zero_iff_mem (I := maximalIdeal (kpInt p P))).mp h0




/-! ## Route (I), engine COMPLETE: the 𝒪_W[ϖ]-partial-sum approximation

* **`approx_pow`** — THE partial-sum theorem: for `x : kpInt p P` and every
  `n`, there are coefficients `c : ℕ → OW_subring p P α` with
  `x − Σ_{i<n} (owToKpInt (c i))·ϖ^i ∈ 𝔪^n` (induction on `n`: the
  membership in `𝔪^n = (ϖ^n)` writes `x − S_n = ϖ^n·x'`
  (`mem_span_singleton`), the lifting step `lift_residue_to_OW` gives
  `cₙ ∈ 𝒪_W` with `x' − owToKpInt cₙ ∈ 𝔪`, and the engine
  `uniformizer_mul_mem_maximalIdeal_pow_succ` moves
  `ϖ^n·(x' − owToKpInt cₙ)` into `𝔪^(n+1)`; the coefficient tuple is
  extended by the `if i = n then cₙ else c i` pattern with the
  `Finset.range_add_one`/`sum_insert` split).

This is the density engine of Route (I) for `K_P = W(ϖ)`: combined with
the norm bound `mem_maximalIdeal_pow_iff_norm_le`
(`‖x − S_n‖ ≤ ‖ϖ‖^n → 0`), every `x ∈ kpInt` is a limit of 𝒪_W[ϖ]-
polynomials (elements of `adjoin (Wk){ϖ}`); the remaining pieces are the
convergence statement and the finite-dimensional-subspace closedness of
`adjoin (Wk){ϖ}` in the complete `kpAdic` (Roadmap Session-104).
-/

/-- partial sums in 𝔪^n: every x ∈ kpInt is congruent mod 𝔪^n to an
𝒪_W[ϖ]-polynomial of degree < n (Route (I), the density engine). -/
lemma approx_pow (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    (x : kpInt p P) (n : ℕ) :
    ∃ c : ℕ → OW_subring p P α,
      x - (∑ i ∈ Finset.range n, (owToKpInt p P α (c i)) * (uniformizer p P ^ i))
        ∈ (maximalIdeal (kpInt p P)) ^ n := by
  classical
  let ϖ : kpInt p P := uniformizer p P
  let mS : Ideal (kpInt p P) := maximalIdeal (kpInt p P)
  induction n with
  | zero =>
      refine ⟨fun _ => 0, ?_⟩
      simp
  | succ n ih =>
      rcases ih with ⟨c, hc⟩
      have hmem : x - (∑ i ∈ Finset.range n, (owToKpInt p P α (c i)) * (ϖ ^ i)) ∈ mS ^ n := by
        simpa [ϖ, mS] using hc
      have hspan : x - (∑ i ∈ Finset.range n, (owToKpInt p P α (c i)) * (ϖ ^ i))
          ∈ Ideal.span ({ϖ ^ n} : Set (kpInt p P)) := by
        rw [← maximalIdeal_pow_eq_span p P n]
        simpa [mS] using hmem
      rcases (Ideal.mem_span_singleton.mp hspan) with ⟨x', hx'⟩
      rcases lift_residue_to_OW p P hα hgen x' with ⟨cn, hcn⟩
      refine ⟨fun i => if i = n then cn else c i, ?_⟩
      have hstep : x - (∑ i ∈ Finset.range (n + 1),
            (owToKpInt p P α (if i = n then cn else c i)) * (ϖ ^ i))
          ∈ mS ^ (n + 1) := by
        have hsplit : (∑ i ∈ Finset.range (n + 1),
              (owToKpInt p P α (if i = n then cn else c i)) * (ϖ ^ i))
            = (owToKpInt p P α cn) * (ϖ ^ n)
              + (∑ i ∈ Finset.range n, (owToKpInt p P α (c i)) * (ϖ ^ i)) := by
          rw [Finset.range_add_one, Finset.sum_insert (by simp)]
          congr 1
          · simp
          · apply Finset.sum_congr rfl
            intro i hi
            have hin : i ≠ n := ne_of_lt (Finset.mem_range.mp hi)
            simp [hin]
        rw [hsplit]
        have hsub : x - ((owToKpInt p P α cn) * (ϖ ^ n)
              + (∑ i ∈ Finset.range n, (owToKpInt p P α (c i)) * (ϖ ^ i)))
            = (x - (∑ i ∈ Finset.range n, (owToKpInt p P α (c i)) * (ϖ ^ i)))
              - (owToKpInt p P α cn) * (ϖ ^ n) := by abel
        rw [hsub]
        have helem : (x - (∑ i ∈ Finset.range n, (owToKpInt p P α (c i)) * (ϖ ^ i)))
              - (owToKpInt p P α cn) * (ϖ ^ n)
            = ϖ ^ n * (x' - owToKpInt p P α cn) := by
          calc
            (x - (∑ i ∈ Finset.range n, (owToKpInt p P α (c i)) * (ϖ ^ i)))
                - (owToKpInt p P α cn) * (ϖ ^ n)
                = ϖ ^ n * x' - (owToKpInt p P α cn) * (ϖ ^ n) := by rw [hx']
            _ = ϖ ^ n * (x' - owToKpInt p P α cn) := by ring
        rw [helem]
        have hmlt : (x' - owToKpInt p P α cn) ∈ mS := by
          simpa [mS] using hcn
        exact uniformizer_mul_mem_maximalIdeal_pow_succ p P n (x' - owToKpInt p P α cn)
          (by simpa [mS] using hmlt)
      simpa [ϖ, mS] using hstep



/-! ## Route (I) item (3): density — 𝒪_W[ϖ]-partial sums approximate kpInt

* `wA p P α` — the intermediate field `Wk(ϖ) ⊆ kpAdic`
  (`IntermediateField.adjoin (Wk p P α) {ϖval}`, ϖval := the value of the
  uniformizer in `K_P`);
* `coeffVal_mem` / `uniformizerVal_mem` / `term_mem` / `partialSum_mem` —
  every term `(owToKpInt (c i) : kpAdic)·ϖval^i` and hence every 𝒪_W[ϖ]-
  partial sum lies in `wA` (𝒪_W-values are in `Wk ⊆ wA`
  (`IntermediateField.algebraMap_mem` + `owToKpInt_value`), ϖval is the
  adjoined generator, `mul_mem`/`pow_mem`/`sum_mem` of the Intermediate-
  Field);
* **`kpInt_mem_closure_wA (hα) (hgen) (x : kpInt p P)`** — the density
  core: `(x : kpAdic p P) ∈ closure (wA p P α : Set (kpAdic p P))`.
  Proof: `approx_pow` supplies 𝒪_W-coefficients with
  `x − S_N ∈ 𝔪^N`; `mem_maximalIdeal_pow_iff_norm_le` bounds
  `‖(x : kpAdic) − y‖ ≤ ‖ϖ‖^N` (y = the value of the partial sum; the
  coe is the ring hom `algebraMap kpInt kpAdic` — `map_sum`/`map_mul`/
  `map_pow`/`map_sub` — and `partialSum_mem` puts y in wA); choosing
  `N` with `‖ϖ‖^N < ε` (`tendsto_pow_atTop_nhds_zero_of_lt_one` +
  `Metric.ball_mem_nhds`, `Real.dist_eq`) and applying
  `Metric.mem_closure_iff` closes.

REMAINING Route (I) items (Roadmap Session-104/105): (3′) full density of
`wA` in `kpAdic` — clear denominators: for `z : kpAdic`, `‖ϖ^j·z‖ ≤ 1`
for large `j` gives `ϖ^j·z` equal to the value of a `kpInt` element (the
`norm ≤ 1 ⟺ kpInt-representable` fact via
`HeightOneSpectrum.mem_adicCompletionIntegers` +
`norm_le_one_iff_val`), so `z` is a limit of `wA`-elements (multiply the
kpInt-approximants by `ϖval^{-j}`); (4) closedness of `wA` in the
complete `kpAdic` (finite-dimensional `Wk`-subspace);
then `wA = ⊤` from dense + closed, closing (c)(iii).
-/

abbrev wA (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P) :
    IntermediateField (Wk p P α) (kpAdic p P) :=
  IntermediateField.adjoin (Wk p P α) ({(((uniformizer p P : kpInt p P) : kpAdic p P))} : Set (kpAdic p P))

lemma coeffVal_mem (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P)
    (c : OW_subring p P α) :
    (((owToKpInt p P α c : kpInt p P) : kpAdic p P)) ∈ (wA p P α : Set (kpAdic p P)) := by
  have hval : ((owToKpInt p P α c : kpInt p P) : kpAdic p P)
      = (((c : OW_subring p P α) : Wk p P α) : kpAdic p P) := owToKpInt_value p P α c
  rw [hval]
  exact IntermediateField.algebraMap_mem (wA p P α) ((c : OW_subring p P α) : Wk p P α)

lemma uniformizerVal_mem (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P) :
    (((uniformizer p P : kpInt p P) : kpAdic p P)) ∈ (wA p P α : Set (kpAdic p P)) := by
  exact IntermediateField.mem_adjoin_simple_self (Wk p P α)
    (((uniformizer p P : kpInt p P) : kpAdic p P))

lemma term_mem (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P)
    (c : OW_subring p P α) (i : ℕ) :
    (((owToKpInt p P α c : kpInt p P) : kpAdic p P)
      * (((uniformizer p P : kpInt p P) : kpAdic p P) ^ i))
      ∈ (wA p P α : Set (kpAdic p P)) := by
  refine IntermediateField.mul_mem (wA p P α) ?_ ?_
  · exact coeffVal_mem p P α c
  · exact pow_mem (uniformizerVal_mem p P α) i

lemma partialSum_mem (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P)
    (c : ℕ → OW_subring p P α) (n : ℕ) :
    (∑ i ∈ Finset.range n,
      ((owToKpInt p P α (c i) : kpInt p P) : kpAdic p P)
        * (((uniformizer p P : kpInt p P) : kpAdic p P) ^ i))
      ∈ (wA p P α : Set (kpAdic p P)) := by
  exact IntermediateField.sum_mem (wA p P α) (fun i hi => term_mem p P α (c i) i)

/-- density of the adjoin at kpInt values: every x ∈ kpInt is a limit of
𝒪_W[ϖ]-polynomials, i.e. (x : kpAdic) lies in the closure of wA. -/
lemma kpInt_mem_closure_wA (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    (x : kpInt p P) :
    (x : kpAdic p P) ∈ closure (wA p P α : Set (kpAdic p P)) := by
  classical
  rw [Metric.mem_closure_iff]
  intro ε hε
  have hr0 : 0 ≤ ‖uniformizer p P‖ := norm_nonneg _
  have hr1 : ‖uniformizer p P‖ < 1 := uniformizer_norm_lt_one p P
  have ht : Tendsto (fun n : ℕ => ‖uniformizer p P‖ ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  have hev : ∀ᶠ n in atTop, ‖uniformizer p P‖ ^ n < ε := by
    filter_upwards [ht.eventually (Metric.ball_mem_nhds (0 : ℝ) hε)] with n hn
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg hr0 n)] at hn
  rcases (Filter.eventually_atTop.mp hev) with ⟨N, hN⟩
  have hpow : ‖uniformizer p P‖ ^ N < ε := hN N (le_rfl)
  rcases approx_pow p P hα hgen x N with ⟨c, hc⟩
  let y : kpAdic p P := ∑ i ∈ Finset.range N,
    ((owToKpInt p P α (c i) : kpInt p P) : kpAdic p P)
      * (((uniformizer p P : kpInt p P) : kpAdic p P) ^ i)
  refine ⟨y, ?_, ?_⟩
  · -- y ∈ wA
    dsimp [y]
    exact partialSum_mem p P α c N
  · -- dist (x : kpAdic) y < ε
    have hdist : dist (x : kpAdic p P) y < ε := by
      -- express as norm of x - S
      have hval : (x : kpAdic p P) - y
          = (((x - (∑ i ∈ Finset.range N, (owToKpInt p P α (c i)) * (uniformizer p P ^ i))
              : kpInt p P) : kpInt p P) : kpAdic p P) := by
        have hy : y = (((∑ i ∈ Finset.range N, (owToKpInt p P α (c i)) * (uniformizer p P ^ i)) : kpInt p P) : kpAdic p P) := by
          dsimp [y]
          symm
          let e : kpInt p P →+* kpAdic p P := algebraMap (kpInt p P) (kpAdic p P)
          change e (∑ i ∈ Finset.range N, (owToKpInt p P α (c i)) * (uniformizer p P ^ i))
              = ∑ i ∈ Finset.range N,
                  e (owToKpInt p P α (c i)) * (e (uniformizer p P)) ^ i
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [map_mul, map_pow]
        rw [hy]
        let e : kpInt p P →+* kpAdic p P := algebraMap (kpInt p P) (kpAdic p P)
        change e x - e (∑ i ∈ Finset.range N, (owToKpInt p P α (c i)) * (uniformizer p P ^ i))
            = e (x - ∑ i ∈ Finset.range N, (owToKpInt p P α (c i)) * (uniformizer p P ^ i))
        exact (map_sub e x (∑ i ∈ Finset.range N, (owToKpInt p P α (c i)) * (uniformizer p P ^ i))).symm
      rw [dist_eq_norm, hval]
      have hnorm := (mem_maximalIdeal_pow_iff_norm_le p P
        (x - (∑ i ∈ Finset.range N, (owToKpInt p P α (c i)) * (uniformizer p P ^ i))) N).mp hc
      exact lt_of_le_of_lt hnorm hpow
    exact hdist



/-! ## Route (I) item (3′): full density of `wA` in `kpAdic`

* `kpIntRep_iff_norm_le_one` — the norm≤1 ⟺ kpInt-representable fact for
  `kpAdic` elements: `(∃ k : kpInt p P, (k : kpAdic p P) = q) ↔ ‖q‖ ≤ 1`
  (the reverse via `norm_le_one_iff_val` +
  `HeightOneSpectrum.mem_adicCompletionIntegers`, the forward via
  `norm_le_one`);
* `uniformizerVal_inv_pow_mem` — `(ϖval^j)⁻¹ ∈ wA` (the intermediate
  field is closed under inverses);
* **`mem_closure_wA (hα) (hgen) (z : kpAdic p P)`** — FULL DENSITY:
  `z ∈ closure (wA p P α : Set (kpAdic p P))`.  Proof (clearing
  denominators): choose `j` with `‖ϖv^j·z‖ = r^j·‖z‖ < 1`
  (`tendsto_pow_atTop_nhds_zero_of_lt_one`, `r := ‖ϖv‖ ∈ (0,1)` from the
  uniformizer norm); `kpIntRep_iff_norm_le_one` gives `k : kpInt` with
  `(k : kpAdic) = ϖv^j·z`; `kpInt_mem_closure_wA` approximates `k` within
  `ε·r^j` by `y ∈ wA`; `y' := y·(ϖv^j)⁻¹ ∈ wA` (`mul_mem` +
  `uniformizerVal_inv_pow_mem`) approximates `z` within ε (the value
  identity `z − y' = (ϖv^j·z − y)·(ϖv^j)⁻¹` by `field_simp`, and the
  norm bound via `norm_mul`/`norm_inv`/`inv_pow` + `mul_lt_mul_of_pos_right`
  + `(ε·r^j)·(r⁻¹)^j = ε`).
* Corollary `wA_dense` — `closure (wA p P α : Set (kpAdic p P)) = univ`.

Combined with the closedness of `wA` (finite-dimensional `Wk`-subspace of
the complete `kpAdic` — next sub-stone), `wA = ⊤` closes (c)(iii):
`natDegree (fϖWk p P α) = P.ramificationIdx ℤ`.  (Roadmap Session-105/106.)
-/

lemma kpIntRep_iff_norm_le_one (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (q : kpAdic p P) :
    (∃ k : kpInt p P, (k : kpAdic p P) = q) ↔ ‖q‖ ≤ 1 := by
  classical
  constructor
  · rintro ⟨k, rfl⟩
    exact norm_le_one p P k
  · intro h
    have hv : Valued.v q ≤ 1 := (norm_le_one_iff_val p P q).mp h
    refine ⟨⟨q, (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers
      (R := 𝓞 K) K (kprime p P)).mpr hv⟩, rfl⟩

lemma uniformizerVal_inv_pow_mem (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P) (j : ℕ) :
    (((uniformizer p P : kpInt p P) : kpAdic p P) ^ j)⁻¹ ∈ (wA p P α : Set (kpAdic p P)) := by
  exact IntermediateField.inv_mem (wA p P α) (pow_mem (uniformizerVal_mem p P α) j)

/-- full density: every element of kpAdic lies in the closure of wA. -/
lemma mem_closure_wA (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1)
    (z : kpAdic p P) :
    z ∈ closure (wA p P α : Set (kpAdic p P)) := by
  classical
  rw [Metric.mem_closure_iff]
  intro ε hε
  let ϖv : kpAdic p P := ((uniformizer p P : kpInt p P) : kpAdic p P)
  let r : ℝ := ‖ϖv‖
  have hr0 : 0 < r := by
    dsimp [r, ϖv]
    exact norm_pos_iff.mpr (by
      intro h0
      apply (uniformizer_ne_zero p P)
      apply Subtype.ext
      exact h0)
  have hr1 : r < 1 := by
    dsimp [r, ϖv]
    simpa using (uniformizer_norm_lt_one p P)
  -- choose j with ‖ϖv^j·z‖ ≤ 1
  have ht : Tendsto (fun n : ℕ => r ^ n * ‖z‖) atTop (nhds 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one (le_of_lt hr0) hr1).mul tendsto_const_nhds)
  have hev : ∀ᶠ n in atTop, r ^ n * ‖z‖ < 1 := by
    filter_upwards [ht.eventually (Metric.ball_mem_nhds (0 : ℝ) (by norm_num : (0:ℝ) < 1))] with n hn
    rwa [Real.dist_eq, sub_zero, abs_of_nonneg (mul_nonneg (pow_nonneg (le_of_lt hr0) n) (norm_nonneg z))] at hn
  rcases (Filter.eventually_atTop.mp hev) with ⟨j, hj⟩
  have hj1 : r ^ j * ‖z‖ < 1 := hj j (le_rfl)
  have hle1 : ‖ϖv ^ j * z‖ ≤ 1 := by
    rw [norm_mul, norm_pow]
    dsimp [r] at hj1
    exact le_of_lt hj1
  rcases (kpIntRep_iff_norm_le_one p P (ϖv ^ j * z)).mpr hle1 with ⟨k, hk⟩
  have hkc : (k : kpAdic p P) ∈ closure (wA p P α : Set (kpAdic p P)) :=
    kpInt_mem_closure_wA p P hα hgen k
  have hε0 : 0 < ε * r ^ j := mul_pos hε (pow_pos hr0 j)
  rw [Metric.mem_closure_iff] at hkc
  rcases hkc (ε * r ^ j) hε0 with ⟨y, hyA, hdist0⟩
  let y' : kpAdic p P := y * (ϖv ^ j)⁻¹
  have hyA' : y' ∈ (wA p P α : Set (kpAdic p P)) := by
    dsimp [y']
    exact IntermediateField.mul_mem (wA p P α) hyA (uniformizerVal_inv_pow_mem p P α j)
  refine ⟨y', hyA', ?_⟩
  have hϖ0 : ϖv ≠ 0 := by
    dsimp [ϖv]
    intro h0
    apply uniformizer_ne_zero p P
    apply Subtype.ext
    exact h0
  have hval : z - y' = (ϖv ^ j * z - y) * (ϖv ^ j)⁻¹ := by
    dsimp [y']
    field_simp [pow_ne_zero j hϖ0]
  rw [dist_eq_norm, hval, norm_mul]
  have hni : ‖(ϖv ^ j)⁻¹‖ = (r⁻¹) ^ j := by
    rw [norm_inv, norm_pow]
    dsimp [r]
    rw [inv_pow]
  have hmain : ‖(ϖv ^ j * z) - y‖ < ε * r ^ j := by
    have hh : dist (ϖv ^ j * z) y < ε * r ^ j := by
      simpa [hk] using hdist0
    rwa [dist_eq_norm] at hh
  calc
    ‖(ϖv ^ j * z - y)‖ * ‖(ϖv ^ j)⁻¹‖
        = ‖(ϖv ^ j * z - y)‖ * (r⁻¹) ^ j := by rw [hni]
    _ < (ε * r ^ j) * (r⁻¹) ^ j := by
          exact mul_lt_mul_of_pos_right hmain (pow_pos (inv_pos.mpr hr0) j)
    _ = ε := by
          rw [mul_assoc]
          rw [← mul_pow]
          field_simp [hr0.ne']
          simp


/-- Full density of the adjoin: `wA p P α` is dense in `kpAdic` (the
closure is everything). -/
lemma wA_dense (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    closure (wA p P α : Set (kpAdic p P)) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro z
  exact mem_closure_wA p P hα hgen z



/-! ## Route (I) item (4), first instance: `ContinuousSMul (Wk)(kpAdic)`

Closedness of `wA` (`Submodule.closed_of_finiteDimensional`, purely
topological) needs `[ContinuousSMul (Wk p P α) (kpAdic p P)]`
(Roadmap Session-107 inventory).  Provided here:

* `wkToKpAdic_continuous` — `Continuous (algebraMap (Wk p P α)
  (kpAdic p P))` (the coe is norm-nonincreasing:
  `AddMonoidHomClass.continuous_of_bound` with bound 1; the norm of a
  `Wk`-element (SubfieldClass instance) is the norm of its value, and
  `algebraMap = coe` — `simp`);
* **instance `continuousSMul_Wk_kpAdic`** — `ContinuousSMul (Wk p P α)
  (kpAdic p P)` via `continuousSMul_of_algebraMap`.

Remaining (Roadmap Session-107, in order): `ContinuousSMul (QpAdic p)
(kpAdic p P)` (same pattern, QpAdic-rebased map — cf. ModuleFinite
`continuous_algebraMap_padic`); `CompleteSpace (Wk p P α)` topologically
(`FiniteDimensional.complete` over 𝕜 := QpAdic + `ContinuousSMul
(QpAdic p) (Wk p P α)` + `FiniteDimensional (QpAdic p) (Wk p P α)` from
`TowerDegree.finrank_QpAdic_Wk_eq_inertiaDeg`); `FiniteDimensional
(Wk p P α) s` for s := the wA-submodule (from
`IntermediateField.adjoin.finiteDimensional
(uniformizer_isIntegral_Wk p P α)`); then
`Submodule.closed_of_finiteDimensional` closes `IsClosed (wA : Set
kpAdic)` and `wA = ⊤` from `wA_dense`.
-/

/-- The scalar embedding `Wk → kpAdic` is continuous (norm-nonincreasing:
the norm of a `Wk`-element is the norm of its value, and
`algebraMap = coe`). -/
lemma wkToKpAdic_continuous (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) :
    Continuous (algebraMap (Wk p P α) (kpAdic p P)) := by
  classical
  exact AddMonoidHomClass.continuous_of_bound
    (algebraMap (Wk p P α) (kpAdic p P)) 1 (by
      intro x
      simp)

/-- The `kpAdic`-module structure over the unramified subfield `W` is
continuous (the algebraMap is continuous and `kpAdic` has continuous
multiplication). -/
noncomputable instance continuousSMul_Wk_kpAdic (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) :
    ContinuousSMul (Wk p P α) (kpAdic p P) := by
  classical
  refine continuousSMul_of_algebraMap (Wk p P α) (kpAdic p P) ?_
  exact wkToKpAdic_continuous p P α



/-! ## Route (I) item (4), second instance: `ContinuousSMul (QpAdic)(kpAdic)`

* `qpAdicToKpAdic_continuous` — `Continuous (algebraMap (QpAdic p)
  (kpAdic p P))` (the completed embedding `qpToKp` is continuous:
  `rw [algebraMap_eq_qpToKp]; exact continuous_qpToKp p P`);
* **instance `continuousSMul_QpAdic_kpAdic`** — `ContinuousSMul (QpAdic p)
  (kpAdic p P)` (same `smul_def`-factorization pattern as ModuleFinite's
  Padic instance).

(Roadmap Session-108 inventory: remaining `CompleteSpace (Wk p P α)` via
the closed-subspace route, `ContinuousSMul (QpAdic p) (Wk p P α)`,
`FiniteDimensional (Wk) s` for the wA-submodule, then
`Submodule.closed_of_finiteDimensional` + `wA_dense` ⟹ `wA = ⊤`.)
-/

/-- The completed embedding `ℚ_p → K_P` is continuous (the rebased
algebraMap is the continuous completed map `qpToKp`). -/
lemma qpAdicToKpAdic_continuous (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Continuous (algebraMap (QpAdic p) (kpAdic p P)) := by
  rw [algebraMap_eq_qpToKp]
  exact continuous_qpToKp p P

/-- The `ℚ_p`-action on `K_P` is continuous (the scalar action factors
through the continuous field multiplication and the continuous completed
embedding). -/
noncomputable instance continuousSMul_QpAdic_kpAdic (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    ContinuousSMul (QpAdic p) (kpAdic p P) := by
  constructor
  show Continuous (fun q : (QpAdic p) × kpAdic p P => q.1 • q.2)
  have h : (fun q : (QpAdic p) × kpAdic p P => q.1 • q.2) =
      (fun z : kpAdic p P × kpAdic p P => z.1 * z.2) ∘
        (Prod.map (algebraMap (QpAdic p) (kpAdic p P)) (id : kpAdic p P → kpAdic p P)) := by
    funext q
    exact Algebra.smul_def q.1 q.2
  rw [h]
  exact continuous_mul.comp (Continuous.prodMap (qpAdicToKpAdic_continuous p P) continuous_id)




/-! ## Route (I) item (4), `FiniteDimensional (QpAdic)(Wk)` + `IsClosed (Wk)`

* **instance `instModuleFinite_QpAdic_Wk`** — `Module.Finite (QpAdic p)
  (Wk p P α)` (hence `FiniteDimensional (QpAdic p) (Wk p P α)`, since
  `FiniteDimensional` is an abbrev for `Module.Finite`; cf. the existing
  TowerDegree theorem `moduleFinite_QpAdic_Wk` which needs (hα) — this
  instance needs none): Wk is the adjoin
  of the Teichmüller lift over QpAdic
  (`Wk p P α = IntermediateField.adjoin (QpAdic p) {ζval}`, rfl), and ζval
  is integral over QpAdic (`IsIntegral.of_finite`, kpAdic finite over
  QpAdic) — `IntermediateField.adjoin.finiteDimensional`;
* `Wk_isClosed` (+ instance `Wk_isClosed_inst`) — `IsClosed (Wk p P α :
  Set (kpAdic p P))`: the finite-dimensional QpAdic-subspace
  `s := (Wk).toSubalgebra.toSubmodule` is closed in the complete `kpAdic`
  (`FiniteDimensional.of_injective s.subtype` — s injects into the
  finite-dimensional kpAdic — then
  `Submodule.closed_of_finiteDimensional`, purely topological; uses the
  `continuousSMul_QpAdic_kpAdic` instance).

DONE below (Roadmap Session-111): `CompleteSpace (Wk p P α)` — the
`IsClosed.completeSpace_coe` instance requires the type `(Wk p P α)` to be
the subtype over `(Wk : Set kpAdic)` definitionally (not the case through
the IntermediateField CoeSort); obtained instead by the isometric
embedding route: the coe `Wk → kpAdic` is an isometry
(`‖(x : kpAdic)‖ = ‖x‖`, simp-level) with closed range = `(Wk : Set …)`,
so `completeSpace_iff_isComplete_range` gives `CompleteSpace (Wk)` from
`IsComplete (range coe)`.  Then the closing of (c)(iii) is also below:
`wA_isClosed` (the carrier of `wA` is closed in `kpAdic` — its
QpAdic-restricted submodule is finite-dimensional, so
`Submodule.closed_of_finiteDimensional` applies over the complete field
`QpAdic`), `wA_eq_top` (closed + `wA_dense` ⟹ `wA = ⊤`), and
**`fϖWk_natDegree_eq_ramIdx`** — `natDegree (fϖWk) = P.ramificationIdx ℤ`
(ROUTE (I) COMPLETE, (c)(iii) closed: `fϖWk_natDegree_eq_finrank_adjoin` +
`wA = ⊤` via `IntermediateField.equivOfEq`/`topEquiv` +
`finrank_kpAdic_over_Wk_eq_ramIdx`).
-/

instance instModuleFinite_QpAdic_Wk (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P) :
    Module.Finite (QpAdic p) (Wk p P α) := by
  exact IntermediateField.adjoin.finiteDimensional
    (IsIntegral.of_finite (QpAdic p) (((teich p P α : kpInt p P) : kpAdic p P)))

/-- Wk is closed in kpAdic (finite-dimensional QpAdic-subspace of the
complete kpAdic — Submodule.closed_of_finiteDimensional, purely
topological). -/
lemma Wk_isClosed (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P) :
    IsClosed ((Wk p P α : Set (kpAdic p P))) := by
  classical
  let s : Submodule (QpAdic p) (kpAdic p P) := (Wk p P α).toSubalgebra.toSubmodule
  have hs : (s : Set (kpAdic p P)) = (Wk p P α : Set (kpAdic p P)) := rfl
  rw [← hs]
  haveI hfin : FiniteDimensional (QpAdic p) s := by
    exact FiniteDimensional.of_injective s.subtype (by
      intro x y h
      apply Subtype.ext
      exact h)
  exact Submodule.closed_of_finiteDimensional (𝕜 := QpAdic p) (E := kpAdic p P) s

/-- Wk is closed in kpAdic: instance form. -/
instance Wk_isClosed_inst (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P) :
    IsClosed ((Wk p P α : Set (kpAdic p P))) := Wk_isClosed p P α

/-! ## Route (I) item (4) COMPLETE: `CompleteSpace (Wk)` + closedness of `wA`

(Roadmap Session-111).  With the `ContinuousSMul (Wk)(kpAdic)` and
`continuousSMul_QpAdic_kpAdic` instances in place:

* **`Wk_completeSpace`** (+ instance `Wk_completeSpace_inst`) —
  `CompleteSpace (Wk p P α)`: the coe `Wk → kpAdic` is an isometry
  (`‖(x : kpAdic)‖ = ‖x‖` — the subfield norm is the ambient norm, `rfl`),
  so `completeSpace_iff_isComplete_range` reduces completeness of `Wk` to
  `IsComplete (range coe)`, the range is the (closed, by `Wk_isClosed`)
  carrier `(Wk : Set kpAdic)`;
* **`wA_isClosed`** — `IsClosed (wA p P α : Set (kpAdic p P))`: the
  carrier of the intermediate field `wA = Wk(ϖ)` is the QpAdic-restricted
  finite-dimensional submodule
  `(wA).toSubalgebra.toSubmodule.restrictScalars (QpAdic p)` of the
  complete `kpAdic`, so `Submodule.closed_of_finiteDimensional` applies
  over the complete field `QpAdic` (no `CompleteSpace (Wk)`/normed-space
  instance over `Wk` needed for this argument);
* **`wA_eq_top`** — `wA p P α = ⊤`: closed (`wA_isClosed`) + dense
  (`wA_dense`) carrier ⟹ carrier = univ (an IntermediateField is
  determined by its carrier);
* **`fϖWk_natDegree_eq_ramIdx`** — (c)(iii) CLOSED:
  `natDegree (fϖWk p P α) = P.ramificationIdx ℤ`: the degree of the
  uniformizer's minimal polynomial over `W = Wk` equals the ramification
  index `e`.  Chain: `fϖWk_natDegree_eq_finrank_adjoin`
  (`finrank (Wk) ↥wA = natDegree fϖWk`), `wA = ⊤` gives
  `↥(wA) ≃ₐ[Wk] kpAdic` (`IntermediateField.equivOfEq` +
  `IntermediateField.topEquiv`), so
  `finrank (Wk) ↥wA = finrank (Wk) kpAdic =
  P.ramificationIdx ℤ` (`finrank_kpAdic_over_Wk_eq_ramIdx`).

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

/-- **`CompleteSpace (Wk)`**: the coe `Wk → kpAdic` is an isometry with
closed range (the carrier), so `completeSpace_iff_isComplete_range` gives
completeness of the Teichmüller subfield. -/
lemma Wk_completeSpace (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P) :
    CompleteSpace (Wk p P α) := by
  classical
  let e : Wk p P α → kpAdic p P := algebraMap (Wk p P α) (kpAdic p P)
  have he : Isometry e := by
    dsimp [e]
    rw [AddMonoidHomClass.isometry_iff_norm]
    intro x
    simp
  have hui : IsUniformInducing e := (Isometry.isUniformEmbedding he).1
  rw [completeSpace_iff_isComplete_range (f := e) hui]
  change IsComplete (Set.range (fun y : Wk p P α => (y : kpAdic p P)))
  have hrange : Set.range (fun y : Wk p P α => (y : kpAdic p P)) =
      (Wk p P α : Set (kpAdic p P)) := by
    ext x
    constructor
    · rintro ⟨y, hy⟩
      simpa [hy] using (show (y : kpAdic p P) ∈ (Wk p P α : Set (kpAdic p P)) from y.2)
    · intro hx
      exact ⟨⟨x, hx⟩, rfl⟩
  rw [hrange]
  exact (Wk_isClosed p P α).isComplete

/-- `CompleteSpace (Wk)`: instance form. -/
instance Wk_completeSpace_inst (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P) :
    CompleteSpace (Wk p P α) := Wk_completeSpace p P α

/-- **`wA` is closed in `kpAdic`**: the carrier of the intermediate field
`wA = Wk(ϖ)` is the QpAdic-restricted finite-dimensional submodule of the
complete `kpAdic` (`FiniteDimensional.of_injective s.subtype` over the
finite-dimensional `kpAdic`, then
`Submodule.closed_of_finiteDimensional`). -/
lemma wA_isClosed (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P) :
    IsClosed ((wA p P α : Set (kpAdic p P))) := by
  classical
  let s : Submodule (QpAdic p) (kpAdic p P) :=
    (wA p P α).toSubalgebra.toSubmodule.restrictScalars (QpAdic p)
  have hs : (s : Set (kpAdic p P)) = (wA p P α : Set (kpAdic p P)) := by
    change ((wA p P α).toSubalgebra.toSubmodule.restrictScalars (QpAdic p)
        : Set (kpAdic p P)) = (wA p P α : Set (kpAdic p P))
    rfl
  rw [← hs]
  haveI hfin : FiniteDimensional (QpAdic p) s := by
    exact FiniteDimensional.of_injective s.subtype (by
      intro x y h
      apply Subtype.ext
      exact h)
  exact Submodule.closed_of_finiteDimensional (𝕜 := QpAdic p) (E := kpAdic p P) s

/-- **`wA = ⊤`**: closed (`wA_isClosed`) + dense (`wA_dense`) carrier.
Route (I): `K_P = W(ϖ)` — the uniformizer generates the completion over
the Teichmüller subfield. -/
lemma wA_eq_top (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    wA p P α = (⊤ : IntermediateField (Wk p P α) (kpAdic p P)) := by
  apply IntermediateField.ext
  intro x
  constructor
  · intro hx
    trivial
  · intro hx
    have hd := wA_dense p P hα hgen
    have hcl : IsClosed ((wA p P α : Set (kpAdic p P))) := wA_isClosed p P α
    have hxcl : x ∈ closure (wA p P α : Set (kpAdic p P)) := by
      rw [hd]
      trivial
    rw [hcl.closure_eq] at hxcl
    exact hxcl

/-- **(c)(iii) CLOSED**: `natDegree (fϖWk p P α) = P.ramificationIdx ℤ` —
the degree of the uniformizer's minimal polynomial over `W = Wk` equals the
ramification index `e` (`fϖWk_natDegree_eq_finrank_adjoin` +
`wA = ⊤` via `equivOfEq`/`topEquiv` +
`finrank_kpAdic_over_Wk_eq_ramIdx`). -/
lemma fϖWk_natDegree_eq_ramIdx (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    (fϖWk p P α).natDegree = P.ramificationIdx ℤ := by
  classical
  have hwA := fϖWk_natDegree_eq_finrank_adjoin p P α
  have htop : wA p P α = (⊤ : IntermediateField (Wk p P α) (kpAdic p P)) :=
    wA_eq_top p P hα hgen
  have heq : Module.finrank (Wk p P α) (wA p P α) =
      Module.finrank (Wk p P α) (kpAdic p P) := by
    let e : (wA p P α) ≃ₐ[Wk p P α] (kpAdic p P) :=
      (IntermediateField.equivOfEq (S := wA p P α) (T := ⊤) htop).trans
        (IntermediateField.topEquiv)
    exact LinearEquiv.finrank_eq e.toLinearEquiv
  have hfr : Module.finrank (Wk p P α) (kpAdic p P) = P.ramificationIdx ℤ :=
    finrank_kpAdic_over_Wk_eq_ramIdx p P hα hgen
  calc
    (fϖWk p P α).natDegree = Module.finrank (Wk p P α) (wA p P α) := hwA.symm
    _ = Module.finrank (Wk p P α) (kpAdic p P) := heq
    _ = P.ramificationIdx ℤ := hfr

end
end Submission.Vdw.LocalField
