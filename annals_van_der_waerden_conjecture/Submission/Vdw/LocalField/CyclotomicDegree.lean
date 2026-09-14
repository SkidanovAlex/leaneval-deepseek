import Mathlib
import Submission.Vdw.LocalField.RootsOfUnity
import Submission.Vdw.LocalField.TeichLift
import Submission.Commons.NumberTheory.OrderModulo.order_pow_sub_one_eq_self

open Classical
open scoped NumberField Polynomial WithZero

set_option autoImplicit false
set_option linter.style.haveILetI false

/-!
# Local-field chapter (G3 upper bound): the ℚ_p-cyclotomic degree statement

## THE OPEN TARGET (the last gap of the `[W : ℚ_p] = f` argument)

Let `ζ := teich p P α : kpInt p P` be the Teichmüller lift of a generator
`α` of the residue field `κ = kap p P` (so `α ≠ 0` and
`hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1`; `ζ` then has
exact order `q := p^f − 1`, `f := P.inertiaDeg ℤ`).  The **target** is

    natDegree (minpoly (QpAdic p) ((teich p P α : kpInt p P) : kpAdic p P))
      ≤ P.inertiaDeg ℤ

equivalently `[QpAdic(ζ) : QpAdic] ≤ f` (the upper bound; the lower bound
`f ≤ natDegree …` follows from `teich_powers_independent_qpAdic`
(TeichLift.lean, Sessions 73–75), which shows the `f` elements
`{1, ζ, …, ζ^(f−1)}` are linearly independent over `QpAdic p`).

## Unramified-extension framing (the classical proof the target needs)

With `d := [QpAdic(ζ) : QpAdic]`: (1) `ζ` reduces to `α`, and `α`
generates `κ^×`, so the residue field of `QpAdic(ζ)` contains `κ` — hence
the residue degree `f(W/ℚ_p) ≥ f` and in fact `= f` (`W ⊆ K_P` and
`res(K_P) = κ`); (2) since `p ∤ q`, the extension `QpAdic(ζ_q)/QpAdic` is
UNRAMIFIED (the `μ_{p'}`-unramified API absent from Mathlib: for a finite
extension with `ζ^q = 1` and `p ∤ q`, reduction of `x^q − 1` is separable,
so the ramification index is `1`); (3) unramified ⟹ `d = f(W/ℚ_p) = f`.
Alternatively via cyclotomic degrees: `d = ord_q(p)` (degree of the
`q`-th cyclotomic extension of ℚ_p) and `ord_q(p) = f` — the pure order
lemmas `order_pow_sub_one_eq_self` / `order_pow_sub_one_dvd` (fleet L109 /
L110) supply the order half.

## What this module provides (provable now)

* `teich_minpoly_natDegree_le_q` — the trivial bracket that makes the target
  well-posed: the minimal polynomial of `ζ` over `QpAdic p` divides
  `X^q − 1`, so its degree is at most `q = p^f − 1`.  (The target replaces
  the exponent `p^f − 1` by `f`.)
* the exact statement of the target is kept in the docstring above, ready to
  be cut-and-pasted as a `theorem` once the unramified/cyclotomic-degree
  lemmas exist.

Axioms of every statement: propext / Classical.choice / Quot.sound only.

## The bridging lemma and its decomposition (the cyclotomic route)

The target follows once the number-theoretic order lemma (L110:
`orderOf (p : ZMod (p^f − 1)) = f`) is attached to the cyclotomic-degree
identity.  The BRIDGING statement (to be proved as the cyclotomic-degree
theorem; kept here as the precise research target — do NOT commit it with a
`sorry`):

    teich_minpoly_natDegree_eq_order :
      (hζ : orderOf ((teich p P α : kpInt p P) : kpAdic p P) = p^f − 1) →
      natDegree (minpoly (QpAdic p) ((teich p P α : kpInt p P) : kpAdic p P))
        = orderOf (p : ZMod (p^f − 1))

Proof decomposition into named `have`s (the parts marked PROVIDED are
theorems in this module; UNPROVEN = the research-scale cyclotomic-degree
content):
* (A) PROVIDED `teich_orderOf_kpAdic`: from the generator hypothesis
  (`hgen`) the exact order of ζ in `kpAdic` is `q := p^f − 1`
  (`teich_orderOf_eq` in kpInt + `orderOf_injective` along the injection
  `kpInt ↪ kpAdic`);
* (B) UNPROVEN `primitive_qth_root_minpoly_degree_eq_order` — the
  cyclotomic-degree core: a primitive `q`-th root of unity `ζ` in `QpAdic`
  (with `p ∤ q`) has
  `natDegree (minpoly (QpAdic p) ζ) = orderOf (p : ZMod q)`.  Classical
  route: `QpAdic(μ_q)/QpAdic` is unramified (`p ∤ q` — the μ_{p'}-
  unramified API absent from Mathlib), so the degree equals the residue
  degree `[𝔽_p(ζ̄) : 𝔽_p]`, which is `ord_q(p)` (minimal `d` with
  `q | p^d − 1`);
* (C) PROVIDED `teich_minpoly_natDegree_le_f_of_eq_order`: the bridge +
  L110 rewrite the right-hand side to `f`, giving the target
  `natDegree ≤ f`.

Axioms of every statement: propext / Classical.choice / Quot.sound only.
-/

namespace Submission.Vdw.LocalField

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- The Teichmüller lift `ζ := teich p P α` satisfies `ζ^q = 1` in
`kpAdic p P`, `q := p^f − 1` (`f := P.inertiaDeg ℤ`). -/
lemma teich_pow_card_sub_one_kpAdic (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0) :
    (((teich p P α : kpInt p P) : kpAdic p P) ^ (p ^ P.inertiaDeg ℤ - 1) : kpAdic p P) = 1 := by
  have hq := teich_pow_card_sub_one (p := p) (P := P) (α := α) hα
  -- the kpInt → kpAdic coercion is the algebraMap (a ring hom)
  change (algebraMap (kpInt p P) (kpAdic p P) (teich p P α)) ^ (p ^ P.inertiaDeg ℤ - 1) =
      (algebraMap (kpInt p P) (kpAdic p P) (1 : kpInt p P))
  rw [← map_pow]
  rw [hq]

theorem teich_minpoly_natDegree_le_q (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0) :
    (minpoly (QpAdic p) ((teich p P α : kpInt p P) : kpAdic p P)).natDegree ≤
      p ^ P.inertiaDeg ℤ - 1 := by
  classical
  let q := p ^ P.inertiaDeg ℤ - 1
  let x : kpAdic p P := ((teich p P α : kpInt p P) : kpAdic p P)
  have hqn : q ≠ 0 := by
    have hpf := kap_pow_pf_ge_two p P
    dsimp [q]
    omega
  have hmon : (Polynomial.X ^ q - 1 : (QpAdic p)[X]).Monic :=
    Polynomial.monic_X_pow_sub_C (1 : QpAdic p) hqn
  have haev : Polynomial.aeval (x : kpAdic p P) (Polynomial.X ^ q - 1 : (QpAdic p)[X]) = 0 := by
    dsimp [x]
    -- aeval x (X^q − 1) = x^q − 1; and x^q = 1
    have hxq : (((teich p P α : kpInt p P) : kpAdic p P) ^ q : kpAdic p P) = 1 := by
      simpa [q] using teich_pow_card_sub_one_kpAdic (p := p) (P := P) (α := α) hα
    calc
      Polynomial.aeval (((teich p P α : kpInt p P) : kpAdic p P))
          (Polynomial.X ^ q - 1 : (QpAdic p)[X])
          = (((teich p P α : kpInt p P) : kpAdic p P) ^ q) - 1 := by
            simp [Polynomial.aeval_X_pow]
      _ = 0 := by rw [hxq]; simp
  have hdvd := minpoly.dvd (QpAdic p) (x : kpAdic p P) haev
  have hq0 : (Polynomial.X ^ q - 1 : (QpAdic p)[X]) ≠ 0 := by
    exact (Polynomial.monic_X_pow_sub_C (1 : QpAdic p) (by
      have hpf := kap_pow_pf_ge_two p P
      dsimp [q]
      omega)).ne_zero
  have hdeg := Polynomial.natDegree_le_of_dvd hdvd hq0
  -- natDegree (X^q − 1) = q (rewrite 1 = C 1 first)
  rw [← Polynomial.C_1] at hdeg
  rw [Polynomial.natDegree_X_pow_sub_C] at hdeg
  simpa [q, x] using hdeg

/-- **(A) Exact order in the completion**: with `α` a generator of `κ^×`,
the Teichmüller lift `ζ = teich p P α` has exact order `q := p^f − 1` in
`kpAdic p P` (`teich_orderOf_eq` in `kpInt`, transported along the injective
monoid hom `kpInt ↪ kpAdic` via `orderOf_injective`). -/
theorem teich_orderOf_kpAdic (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    orderOf (((teich p P α : kpInt p P) : kpAdic p P)) = p ^ P.inertiaDeg ℤ - 1 := by
  classical
  have hq := teich_orderOf_eq (p := p) (P := P) (α := α) hα hgen
  let f : kpInt p P →* kpAdic p P := algebraMap (kpInt p P) (kpAdic p P)
  have hfinj : Function.Injective f := by
    dsimp [f]
    exact (kpIntToKpAdic_injective p P)  -- same underlying function (coercion = algebraMap)
  have hm := orderOf_injective f hfinj (teich p P α)
  -- hm : orderOf (f (teich α)) = orderOf (teich α); f x = (x : kpAdic) by rfl
  simpa [f] using (hm.trans hq)

/-- **(C) Assembly**: if the cyclotomic-degree bridge holds (natDegree of the
minimal polynomial of ζ equals `orderOf (p : ZMod q)`), then L110 rewrites
that order to `f`, giving the upper-bound target
`natDegree ≤ P.inertiaDeg ℤ`. -/
theorem teich_minpoly_natDegree_le_f_of_eq_order (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (_hα : α ≠ 0)
    (hbridge : (minpoly (QpAdic p) ((teich p P α : kpInt p P) : kpAdic p P)).natDegree =
      orderOf (p : ZMod (p ^ P.inertiaDeg ℤ - 1))) :
    (minpoly (QpAdic p) ((teich p P α : kpInt p P) : kpAdic p P)).natDegree ≤
      P.inertiaDeg ℤ := by
  classical
  have hord : orderOf (p : ZMod (p ^ P.inertiaDeg ℤ - 1)) = P.inertiaDeg ℤ :=
    Commons.NumberTheory.OrderModulo.order_pow_sub_one_eq_self p (P.inertiaDeg ℤ)
      (Fact.out : Nat.Prime p).two_le (Nat.succ_le_of_lt (Ideal.inertiaDeg_pos P ℤ))
  rw [hbridge, hord]


/-- **Residue-extension claim (our residue field)**: the residue field
`κ = kap p P` (of `p^f` elements, `f := P.inertiaDeg ℤ`) has degree over
`𝔽_p` equal to `ord_q(p)`, `q := p^f − 1` — from `|κ| = p^f`
(`kap_card`) and the order lemma L110 (`ord_q(p) = f`).  For `α` a
generator of `κ^×` (`hgen`) the reduction `ᾱ = mk ζ` of the primitive
Teichmüller root of unity GENERATES κ over 𝔽_p (adjoin_eq_top_of_generator,
ResidueGenerator), so this is exactly the claim "a primitive q-th root of
unity generates a residue field of degree `ord_q(p)`" for the concrete
residue field of the completion. -/
theorem kap_finrank_eq_order (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] :
    Module.finrank (ZMod p) (kap p P) = orderOf (p : ZMod (p ^ P.inertiaDeg ℤ - 1)) := by
  classical
  have hf := kap_finrank (p := p) (P := P)
  have hord : orderOf (p : ZMod (p ^ P.inertiaDeg ℤ - 1)) = P.inertiaDeg ℤ :=
    Commons.NumberTheory.OrderModulo.order_pow_sub_one_eq_self p (P.inertiaDeg ℤ)
      (Fact.out : Nat.Prime p).two_le (Nat.succ_le_of_lt (Ideal.inertiaDeg_pos P ℤ))
  rw [hf]
  exact hord.symm

/-- ζ is integral over `QpAdic p`: a root of the monic polynomial
`X^q − 1`, `q := p^f − 1 ≥ 1`. -/
lemma teich_isIntegral_kpAdic (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0) :
    IsIntegral (QpAdic p) (teich p P α : kpAdic p P) := by
  classical
  let q := p ^ P.inertiaDeg ℤ - 1
  let x : kpAdic p P := (teich p P α : kpAdic p P)
  refine ⟨Polynomial.X ^ q - 1, ?_, ?_⟩
  · exact Polynomial.monic_X_pow_sub_C (1 : QpAdic p) (by
      have hpf := kap_pow_pf_ge_two p P
      dsimp [q]
      omega)
  · have hxq : ((teich p P α : kpAdic p P) ^ q : kpAdic p P) = 1 := by
      simpa [q, x] using teich_pow_card_sub_one_kpAdic (p := p) (P := P) (α := α) hα
    calc
      Polynomial.aeval ((teich p P α : kpAdic p P))
          (Polynomial.X ^ q - 1 : (QpAdic p)[X])
          = ((teich p P α : kpAdic p P) ^ q) - 1 := by
            simp [Polynomial.aeval_X_pow]
      _ = 0 := by rw [hxq]; simp

/-- **B1, smallest W-subfield lemma**: for `W := ℚ_p(ζ)` (the subfield of
`K_P = kpAdic p P` generated over `QpAdic p` by the Teichmüller lift ζ),
the degree `[W : QpAdic]` (the finrank of the `IntermediateField.adjoin`)
equals the degree of ζ's minimal polynomial over `QpAdic p` — the very
`natDegree` that the bridge statement `teich_minpoly_natDegree_eq_order`
controls.  (`IntermediateField.adjoin.finrank`, ζ integral by
`teich_isIntegral_kpAdic`.) -/
theorem adjoin_finrank_eq_minpoly_natDegree (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0) :
    Module.finrank (QpAdic p)
      (IntermediateField.adjoin (QpAdic p)
        ({(teich p P α : kpAdic p P)} : Set (kpAdic p P))) =
    (minpoly (QpAdic p) (teich p P α : kpAdic p P)).natDegree := by
  classical
  have hi := teich_isIntegral_kpAdic (p := p) (P := P) (α := α) hα
  exact IntermediateField.adjoin.finrank hi

/-- **Residue-embedding ligament (order level)**: with `α` a generator of
`κ^×`, the reduction map from the `ℤ_p`-order `QpInt[ζ] ⊆ kpInt p P`
(`ζ := teich p P α`) is SURJECTIVE onto the residue field `κ = kap p P`:
every residue `y` is hit by the reduction of an integral element of the
field `W = ℚ_p(ζ)` (indeed of `QpInt[ζ]`).  Proof: `y = 0` by `0`;
`y ≠ 0` by `generator_nat_pow` write `y = α^k = mk (ζ^k)` with
`ζ^k ∈ QpInt[ζ]` (`Algebra.subset_adjoin` + `Subalgebra.pow_mem`).  This is
the content of "`res(W) ⊇ κ`" at the level expressible before the
`𝒪_W = W ∩ kpInt` subfield theory exists. -/
theorem orderQpInt_reduction_surjective (p : ℕ) [Fact (Nat.Prime p)]
    (P : Ideal (𝓞 K)) [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    Function.Surjective
      (fun x : Algebra.adjoin (QpInt p) ({teich p P α} : Set (kpInt p P)) =>
        (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) (x : kpInt p P) : kap p P)) := by
  classical
  intro y
  by_cases hy : y = 0
  · refine ⟨0, ?_⟩
    simp [hy]
  · rcases generator_nat_pow (p := p) (P := P) (α := α) hα hgen (x := y) hy with ⟨k, hk⟩
    have hζmem : teich p P α ∈ Algebra.adjoin (QpInt p) ({teich p P α} : Set (kpInt p P)) := by
      exact Algebra.subset_adjoin (by simp)
    let x : Algebra.adjoin (QpInt p) ({teich p P α} : Set (kpInt p P)) :=
      ⟨(teich p P α : kpInt p P) ^ k, Subalgebra.pow_mem _ hζmem k⟩
    refine ⟨x, ?_⟩
    have hmkζ : Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) (teich p P α) = α :=
      teich_mod_eq (p := p) (P := P) α
    calc
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) (x : kpInt p P)
          = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P))
              ((teich p P α : kpInt p P) ^ k) := rfl
      _ = α ^ k := by
            rw [map_pow, hmkζ]
      _ = y := hk


/-- `W := ℚ_p(ζ)`: the subfield of `K_P = kpAdic p P` generated over
`QpAdic p` by the Teichmüller lift `ζ = teich p P α`. -/
abbrev Wk (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) : IntermediateField (QpAdic p) (kpAdic p P) :=
  IntermediateField.adjoin (QpAdic p)
    ({(teich p P α : kpAdic p P)} : Set (kpAdic p P))

/-- `𝒪_W := W ∩ kpInt`: the elements of `W` whose value in `K_P` lies in the
valuation ring (equivalently, is the image of some `kpInt` element). -/
abbrev OW (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) : Set (Wk p P α) :=
  {w | ∃ z : kpInt p P, (z : kpAdic p P) = (w : kpAdic p P)}

/-- **Well-definedness of the reduction on `𝒪_W`**: the reduction of two
`kpInt` representatives with the same value in `K_P` agrees (kpInt embeds
injectively into `kpAdic`, `Subtype.ext`). -/
lemma OW_mk_eq_of_coe_eq (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {z₁ z₂ : kpInt p P}
    (h : (z₁ : kpAdic p P) = (z₂ : kpAdic p P)) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) z₁ =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) z₂ := by
  congr 1
  exact Subtype.ext h

/-- **Witness independence**: for `w ∈ 𝒪_W`, the reduction of any
`kpInt`-representative `z` of `w` equals the reduction of the (chosen)
representative coming from the membership `hw` — reduction on `𝒪_W` is a
genuine function of `w ∈ W ∩ kpInt`, not of the chosen representative. -/
lemma OW_res_independent (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) {w : Wk p P α} (hw : w ∈ OW p P α)
    (z : kpInt p P) (hz : (z : kpAdic p P) = (w : kpAdic p P)) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) (Classical.choose hw) =
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) z := by
  have hz' : Classical.choose hw = z := Subtype.ext ((Classical.choose_spec hw).trans hz.symm)
  rw [hz']


/-- `0 ∈ 𝒪_W` (kpInt contains 0). -/
lemma OW_zero (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P) :
    (0 : Wk p P α) ∈ OW p P α := by
  refine ⟨0, ?_⟩
  simp

/-- `1 ∈ 𝒪_W`. -/
lemma OW_one (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))] (α : kap p P) :
    (1 : Wk p P α) ∈ OW p P α := by
  refine ⟨1, ?_⟩
  simp

/-- `𝒪_W` is closed under addition: witnesses add (kpInt is a subring and the
coercions `kpInt → kpAdic`, `W → kpAdic` are ring homomorphisms). -/
lemma OW_add (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) {w₁ w₂ : Wk p P α} (hw₁ : w₁ ∈ OW p P α) (hw₂ : w₂ ∈ OW p P α) :
    w₁ + w₂ ∈ OW p P α := by
  rcases hw₁ with ⟨z₁, hz₁⟩
  rcases hw₂ with ⟨z₂, hz₂⟩
  refine ⟨z₁ + z₂, ?_⟩
  calc
    ((z₁ + z₂ : kpInt p P) : kpAdic p P)
        = (z₁ : kpAdic p P) + (z₂ : kpAdic p P) := by rfl
    _ = (w₁ : kpAdic p P) + (w₂ : kpAdic p P) := by rw [hz₁, hz₂]
    _ = ((w₁ + w₂ : Wk p P α) : kpAdic p P) := by rfl

/-- `𝒪_W` is closed under multiplication: witnesses multiply. -/
lemma OW_mul (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) {w₁ w₂ : Wk p P α} (hw₁ : w₁ ∈ OW p P α) (hw₂ : w₂ ∈ OW p P α) :
    w₁ * w₂ ∈ OW p P α := by
  rcases hw₁ with ⟨z₁, hz₁⟩
  rcases hw₂ with ⟨z₂, hz₂⟩
  refine ⟨z₁ * z₂, ?_⟩
  calc
    ((z₁ * z₂ : kpInt p P) : kpAdic p P)
        = (z₁ : kpAdic p P) * (z₂ : kpAdic p P) := by rfl
    _ = (w₁ : kpAdic p P) * (w₂ : kpAdic p P) := by rw [hz₁, hz₂]
    _ = ((w₁ * w₂ : Wk p P α) : kpAdic p P) := by rfl

/-- `𝒪_W` is closed under negation. -/
lemma OW_neg (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) {w : Wk p P α} (hw : w ∈ OW p P α) : -w ∈ OW p P α := by
  rcases hw with ⟨z, hz⟩
  refine ⟨-z, ?_⟩
  calc
    ((-z : kpInt p P) : kpAdic p P) = - (z : kpAdic p P) := by rfl
    _ = - (w : kpAdic p P) := by rw [hz]
    _ = ((-w : Wk p P α) : kpAdic p P) := by rfl


/-- **Transport (ligament i)**: the kpAdic-value of an element of the
`ℤ_p`-order `QpInt[ζ] ⊆ kpInt p P` lies in the subfield `W = ℚ_p(ζ)`:
an induction over the adjoin generators (ζ, QpInt scalars, +, ·) with W's
closure properties (`mem_adjoin_simple_self`, the tower equality for
scalars, `add_mem`, `mul_mem`). -/
lemma orderQpInt_value_mem_Wk (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (x : Algebra.adjoin (QpInt p) ({teich p P α} : Set (kpInt p P))) :
    ((x : kpInt p P) : kpAdic p P) ∈ (Wk p P α : Set (kpAdic p P)) := by
  classical
  exact Algebra.adjoin_induction
    (s := ({teich p P α} : Set (kpInt p P)))
    (R := QpInt p) (A := kpInt p P)
    (p := fun (y : kpInt p P) (_hy : y ∈ Algebra.adjoin (QpInt p)
        ({teich p P α} : Set (kpInt p P))) =>
      ((y : kpAdic p P) ∈ (Wk p P α : Set (kpAdic p P))))
    (by
      intro y hy
      rw [Set.mem_singleton_iff.mp hy]
      exact IntermediateField.mem_adjoin_simple_self (QpAdic p)
        ((teich p P α : kpAdic p P)))
    (by
      intro r
      change algebraMap (kpInt p P) (kpAdic p P) (algebraMap (QpInt p) (kpInt p P) r) ∈
        (Wk p P α : Set (kpAdic p P))
      rw [show algebraMap (kpInt p P) (kpAdic p P) (algebraMap (QpInt p) (kpInt p P) r) =
          algebraMap (QpAdic p) (kpAdic p P) (algebraMap (QpInt p) (QpAdic p) r) by rfl]
      exact IntermediateField.algebraMap_mem (Wk p P α) (algebraMap (QpInt p) (QpAdic p) r))
    (by
      intro x y _hx _hy ihx ihy
      simpa using (Wk p P α).add_mem ihx ihy)
    (by
      intro x y _hx _hy ihx ihy
      simpa using (Wk p P α).mul_mem ihx ihy)
    x.2

/-- An element of `W` whose value has an integral representative `z : kpInt`
lies in `𝒪_W` (with `z` as the witness). -/
lemma mem_OW_of_value (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) {y : kpAdic p P} (hy : y ∈ (Wk p P α : Set (kpAdic p P)))
    (z : kpInt p P) (hz : (z : kpAdic p P) = y) :
    (⟨y, hy⟩ : Wk p P α) ∈ OW p P α := by
  refine ⟨z, ?_⟩
  exact hz

/-- **Ligament (i)**: every element of the order `QpInt[ζ]` gives an element
of `𝒪_W = W ∩ kpInt` whose reduction agrees with the reduction of the order
element — so the order-level surjectivity `orderQpInt_reduction_surjective`
lifts to the 𝒪_W-reduction. -/
theorem orderQpInt_mem_OW (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (x : Algebra.adjoin (QpInt p) ({teich p P α} : Set (kpInt p P))) :
    ∃ w : {w : Wk p P α // w ∈ OW p P α},
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) (Classical.choose w.2) =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) (x : kpInt p P) := by
  classical
  let y : kpAdic p P := ((x : kpInt p P) : kpAdic p P)
  have hy : y ∈ (Wk p P α : Set (kpAdic p P)) := orderQpInt_value_mem_Wk p P α x
  let w0 : Wk p P α := ⟨y, hy⟩
  have hw : w0 ∈ OW p P α := by
    dsimp [w0]
    exact mem_OW_of_value p P α hy (x : kpInt p P) rfl
  refine ⟨⟨w0, hw⟩, ?_⟩
  have hz : ((x : kpInt p P) : kpAdic p P) = (w0 : kpAdic p P) := by
    dsimp [w0, y]
  exact OW_res_independent p P α hw (x : kpInt p P) hz


/-- **The induced reduction on 𝒪_W**: an integral element `w ∈ 𝒪_W` of
`W = ℚ_p(ζ)` maps to its residue in `κ = kap p P`, by reducing any of its
`kpInt` representatives (representative-independent by
`OW_res_independent`).  This is the formal `res(W)` map at the 𝒪_W level. -/
noncomputable def resOW (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (w : {w : Wk p P α // w ∈ OW p P α}) : kap p P :=
  Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) (Classical.choose w.2)

/-- `resOW` agrees with the reduction of ANY integral representative of the
element (the map is a genuine function of `w ∈ W ∩ kpInt`). -/
lemma resOW_eq_mk (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) (w : {w : Wk p P α // w ∈ OW p P α}) (z : kpInt p P)
    (hz : (z : kpAdic p P) = (w.1 : kpAdic p P)) :
    resOW p P α w = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) z := by
  unfold resOW
  exact OW_res_independent p P α w.2 z hz

/-- **`res(W) ⊇ κ`**: the induced reduction from 𝒪_W is surjective onto the
residue field κ — every residue is the reduction of an integral element of
`W = ℚ_p(ζ)` (lift through the order `QpInt[ζ]` by
`orderQpInt_reduction_surjective`, transport into 𝒪_W with reduction
preserved by `orderQpInt_mem_OW`). -/
theorem resOW_surjective (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    Function.Surjective (resOW p P α) := by
  intro y
  rcases orderQpInt_reduction_surjective (p := p) (P := P) (α := α) hα hgen y with ⟨x, hx⟩
  rcases orderQpInt_mem_OW p P α x with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  calc
    resOW p P α w = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) (x : kpInt p P) := by
          unfold resOW
          exact hw
    _ = y := hx


/-- **Step (a), wrapper — `res(W) ⊆ κ`**: the image of the induced
reduction lies in the residue field κ (definitional: κ is the codomain). -/
theorem resOW_range_subset (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) : Set.range (resOW p P α) ⊆ Set.univ := by
  intro y hy
  trivial

/-- **Step (a), wrapped — `res(W) = κ`**: with α a generator of κ^× the
image of the induced reduction is the whole residue field (from
`resOW_surjective`).  When `res(W)` is formalised as `Set.range resOW`,
this is the reverse-inclusion-free statement of `res(W) = κ`, and then
`[res(W):𝔽_p] = [κ:𝔽_p] = ord_q(p)` via `kap_finrank_eq_order`. -/
theorem resOW_range_eq_univ (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    Set.range (resOW p P α) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  rcases resOW_surjective p P hα hgen y with ⟨w, hw⟩
  exact ⟨w, hw⟩


/-- 𝒪_W as a `Subring` of `W = ℚ_p(ζ)` (carrier 𝒪_W, closed by the
`OW_*` lemmas). -/
def OW_subring (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) : Subring (Wk p P α) where
  carrier := OW p P α
  zero_mem' := OW_zero p P α
  one_mem' := OW_one p P α
  add_mem' := by intro x y hx hy; exact OW_add p P α hx hy
  neg_mem' := by intro x hx; exact OW_neg p P α hx
  mul_mem' := by intro x y hx hy; exact OW_mul p P α hx hy

/-- `resOW` as a ring homomorphism from the subring 𝒪_W to κ: the reduction
respects `+`, `·` and `1` (representative arithmetic in kpInt). -/
noncomputable def resOW_hom (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) : OW_subring p P α →+* kap p P where
  toFun := fun x => resOW p P α ⟨x.1, x.2⟩
  map_zero' := by
    change resOW p P α ⟨(0 : ↥(OW_subring p P α)).1, (0 : ↥(OW_subring p P α)).2⟩ =
        (0 : kap p P)
    calc
      resOW p P α ⟨(0 : ↥(OW_subring p P α)).1, (0 : ↥(OW_subring p P α)).2⟩
          = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) (0 : kpInt p P) := by
            apply resOW_eq_mk p P α
              ⟨(0 : ↥(OW_subring p P α)).1, (0 : ↥(OW_subring p P α)).2⟩ (0 : kpInt p P)
            rfl
      _ = (0 : kap p P) := by
            simp
  map_one' := by
    change resOW p P α ⟨(1 : ↥(OW_subring p P α)).1, (1 : ↥(OW_subring p P α)).2⟩ =
        (1 : kap p P)
    calc
      resOW p P α ⟨(1 : ↥(OW_subring p P α)).1, (1 : ↥(OW_subring p P α)).2⟩
          = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) (1 : kpInt p P) := by
            apply resOW_eq_mk p P α
              ⟨(1 : ↥(OW_subring p P α)).1, (1 : ↥(OW_subring p P α)).2⟩ (1 : kpInt p P)
            rfl
      _ = (1 : kap p P) := by
            simp
  map_add' := by
    intro x y
    change resOW p P α ⟨(x + y : ↥(OW_subring p P α)).1, (x + y : ↥(OW_subring p P α)).2⟩ =
        resOW p P α ⟨x.1, x.2⟩ + resOW p P α ⟨y.1, y.2⟩
    -- kpInt witnesses for x and y
    let zx : kpInt p P := Classical.choose (show ∃ z : kpInt p P,
        (z : kpAdic p P) = (x.1 : kpAdic p P) from x.2)
    let zy : kpInt p P := Classical.choose (show ∃ z : kpInt p P,
        (z : kpAdic p P) = (y.1 : kpAdic p P) from y.2)
    have hxval : (zx : kpAdic p P) = (x.1 : kpAdic p P) :=
      Classical.choose_spec (show ∃ z : kpInt p P,
        (z : kpAdic p P) = (x.1 : kpAdic p P) from x.2)
    have hyval : (zy : kpAdic p P) = (y.1 : kpAdic p P) :=
      Classical.choose_spec (show ∃ z : kpInt p P,
        (z : kpAdic p P) = (y.1 : kpAdic p P) from y.2)
    -- zx + zy represents (x + y).1
    have hzadd : ((zx + zy : kpInt p P) : kpAdic p P) =
        (((x + y : ↥(OW_subring p P α)).1 : Wk p P α) : kpAdic p P) := by
      calc
        ((zx + zy : kpInt p P) : kpAdic p P)
            = (zx : kpAdic p P) + (zy : kpAdic p P) := by rfl
        _ = (x.1 : kpAdic p P) + (y.1 : kpAdic p P) := by rw [hxval, hyval]
        _ = (((x + y : ↥(OW_subring p P α)).1 : Wk p P α) : kpAdic p P) := by rfl
    have hred : resOW p P α ⟨(x + y : ↥(OW_subring p P α)).1, (x + y : ↥(OW_subring p P α)).2⟩ =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) (zx + zy) := by
          exact resOW_eq_mk p P α
            ⟨(x + y : ↥(OW_subring p P α)).1, (x + y : ↥(OW_subring p P α)).2⟩ (zx + zy) hzadd
    calc
      resOW p P α ⟨(x + y : ↥(OW_subring p P α)).1, (x + y : ↥(OW_subring p P α)).2⟩
          = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) (zx + zy) := hred
      _ = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) zx +
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) zy := by
            rw [map_add]
      _ = resOW p P α ⟨x.1, x.2⟩ + resOW p P α ⟨y.1, y.2⟩ := by
            rw [show Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) zx =
                resOW p P α ⟨x.1, x.2⟩ by
              unfold resOW
              rfl]
            rw [show Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) zy =
                resOW p P α ⟨y.1, y.2⟩ by
              unfold resOW
              rfl]
  map_mul' := by
    intro x y
    change resOW p P α ⟨(x * y : ↥(OW_subring p P α)).1, (x * y : ↥(OW_subring p P α)).2⟩ =
        resOW p P α ⟨x.1, x.2⟩ * resOW p P α ⟨y.1, y.2⟩
    let zx : kpInt p P := Classical.choose (show ∃ z : kpInt p P,
        (z : kpAdic p P) = (x.1 : kpAdic p P) from x.2)
    let zy : kpInt p P := Classical.choose (show ∃ z : kpInt p P,
        (z : kpAdic p P) = (y.1 : kpAdic p P) from y.2)
    have hxval : (zx : kpAdic p P) = (x.1 : kpAdic p P) :=
      Classical.choose_spec (show ∃ z : kpInt p P,
        (z : kpAdic p P) = (x.1 : kpAdic p P) from x.2)
    have hyval : (zy : kpAdic p P) = (y.1 : kpAdic p P) :=
      Classical.choose_spec (show ∃ z : kpInt p P,
        (z : kpAdic p P) = (y.1 : kpAdic p P) from y.2)
    have hzmul : ((zx * zy : kpInt p P) : kpAdic p P) =
        (((x * y : ↥(OW_subring p P α)).1 : Wk p P α) : kpAdic p P) := by
      calc
        ((zx * zy : kpInt p P) : kpAdic p P)
            = (zx : kpAdic p P) * (zy : kpAdic p P) := by rfl
        _ = (x.1 : kpAdic p P) * (y.1 : kpAdic p P) := by rw [hxval, hyval]
        _ = (((x * y : ↥(OW_subring p P α)).1 : Wk p P α) : kpAdic p P) := by rfl
    have hred : resOW p P α ⟨(x * y : ↥(OW_subring p P α)).1, (x * y : ↥(OW_subring p P α)).2⟩ =
        Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) (zx * zy) := by
          exact resOW_eq_mk p P α
            ⟨(x * y : ↥(OW_subring p P α)).1, (x * y : ↥(OW_subring p P α)).2⟩ (zx * zy) hzmul
    calc
      resOW p P α ⟨(x * y : ↥(OW_subring p P α)).1, (x * y : ↥(OW_subring p P α)).2⟩
          = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) (zx * zy) := hred
      _ = Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) zx *
            Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) zy := by
            rw [map_mul]
      _ = resOW p P α ⟨x.1, x.2⟩ * resOW p P α ⟨y.1, y.2⟩ := by
            rw [show Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) zx =
                resOW p P α ⟨x.1, x.2⟩ by
              unfold resOW
              rfl]
            rw [show Ideal.Quotient.mk (IsLocalRing.maximalIdeal (kpInt p P)) zy =
                resOW p P α ⟨y.1, y.2⟩ by
              unfold resOW
              rfl]

/-- `𝔪_W`: the maximal ideal of `𝒪_W` — the kernel of the reduction
homomorphism `𝒪_W → κ`. -/
abbrev OW_ker (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    (α : kap p P) : Ideal (OW_subring p P α) :=
  RingHom.ker (resOW_hom p P α)

/-- The reduction `𝒪_W → κ` is surjective: every residue of `κ` is the
reduction of an integral element of `W` (transport of `resOW_surjective`
from the `{w // w ∈ OW}` level to the subring elements). -/
theorem resOW_hom_surjective (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    Function.Surjective (resOW_hom p P α) := by
  intro y
  rcases resOW_surjective (p := p) (P := P) hα hgen y with ⟨w, hw⟩
  refine ⟨⟨w.1, w.2⟩, ?_⟩
  change resOW p P α w = y
  exact hw

/-- `𝒪_W/𝔪_W ≅ κ`: the reduction map induces a ring isomorphism of the
residue ring of `W` with the residue field of `K_P`. -/
noncomputable def OW_residueEquiv (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    (OW_subring p P α) ⧸ OW_ker p P α ≃+* kap p P :=
  RingHom.quotientKerEquivOfSurjective
    (resOW_hom_surjective (p := p) (P := P) hα hgen)

/-- The kernel `𝔪_W` is a maximal ideal of `𝒪_W` (it is the kernel of a
surjective homomorphism onto the field `κ`). -/
theorem OW_ker_isMaximal (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    (OW_ker p P α).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective (resOW_hom p P α)
    (resOW_hom_surjective (p := p) (P := P) hα hgen)

/-- The residue ring `𝒪_W/𝔪_W` of `W` has `p^f` elements, `f := P.inertiaDeg ℤ`
— i.e. the residue field of `W = ℚ_p(ζ)` identifies with `κ` (via
`OW_residueEquiv`), whose cardinality is `kpIntResidue_card`.  With
`[res(W):𝔽_p] = [κ:𝔽_p] = f` this is the residue-degree half of the
fundamental identity for `W/ℚ_p`. -/
theorem OW_residue_card (p : ℕ) [Fact (Nat.Prime p)] (P : Ideal (𝓞 K))
    [P.IsMaximal] [P.LiesOver (Ideal.span ({(p : ℤ)} : Set ℤ))]
    {α : kap p P} (hα : α ≠ 0)
    (hgen : orderOf (Units.mk0 α hα) = p ^ P.inertiaDeg ℤ - 1) :
    Nat.card ((OW_subring p P α) ⧸ OW_ker p P α) = p ^ P.inertiaDeg ℤ := by
  rw [Nat.card_congr (OW_residueEquiv p P hα hgen).toEquiv]
  simpa [kap] using (kpIntResidue_card (p := p) (P := P))

end
end Submission.Vdw.LocalField