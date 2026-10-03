import Mathlib
import Submission.Work.ORHughesFree.Rat.SourceFrame
import Submission.Work.ORHughesFree.Rat.SourceCore
import Submission.Work.ORHughesFree.Rat.Orbit
import Submission.Work.ORHughesFree.Rat.OrbitF
import Submission.Work.ORHughesFree.Rat.mem_A_mul_ofGroup_iff
import Submission.Work.ORHughesFree.Rat.mem_ofGroup_mul_A_iff
import Submission.Work.ORHughesFree.Rat.Source.Dichotomy
import Submission.Work.ORHughesFree.RatU.mul_ne_zero
import Submission.Work.ORHughesFree.RatU.exists_decomp

/-!
# The source subgroup of an element of `Rat(U)`: the induction setup

We prove [DHS04, Theorem 5.7] for the term model `RatU U` of `Rat(U)`: for every `α : RatU U` the
family

`Rat.F α = {V ≤ U | α ∈ Rat(V)·U}`

has a least element, which is finitely generated (`Rat.source_subgroup_exists`).

The proof is by well-founded induction on the complexity `Rat.treeOfRat U α`, using the four-way
decomposition `RatU.exists_decomp` of a non-zero element, together with two inputs about the
*translate dichotomy*:

* `Rat.Dich.both_of_ne_zero` (proved in `Rat/Dich/ofGroup_mul_A_eq_V_or_univ.lean`): for `x ≠ 0`
  and `b ∈ Rat.A V`, every translate `b·φw ∈ Rat.A V` (respectively `φw·b ∈ Rat.A V`) satisfies
  `w ∈ V`;
* the resulting *coset structure* of the translate sets `mem_T_iff`, `T_eq_coset` and `TL_eq_coset`
  below: at a level `V ∈ Rat.F x` (respectively `V ∈ Rat.FL x`) the set of translates of `x` that
  lie in `Rat.A V` is a coset of `V`.

This file contains the definitions (`IsLeastF`, `IsLeastL`), the coset structure, and the base
cases of the induction.  The induction itself is in `Rat/Source/Induction.lean`, and the individual
cases are delegated to `Rat/Source/F_add.lean`, `Rat/Source/FL_add.lean`,
`Rat/Source/F_mul.lean`, `Rat/Source/F_left_translate.lean`.

## Notation used below

`T x V = Orbit.T (supp (Psi x)) V = {u : U | x·φu ∈ A V}` is the right translate set, and
`TL x V = {u : U | φu·x ∈ A V}` the left one (`mem_T_iff`).  The two facts we use constantly are
`T_eq_coset` and `TL_eq_coset`: if `S` is the least element of `F x` (respectively of `FL x`) and
`u₀` is a translate of `x` landing in `A S`, then for every `V ⊇ S` with `V ∈ F x` one has
`T x V = {u₀·v | v ∈ V}` (a right coset), so in particular the *same* `u₀` describes the cosets at
all levels.  Consequently `T x V = T x S · V` (right multiplication by `V`).

## The four case lemmas of the induction

Let `IsLeastF y Sy` mean that `Sy` is the least element of `F y`, and let `uy : U` satisfy
`y·φuy ∈ A Sy` (equivalently `uy ∈ T y Sy`; such a `uy` exists because `Sy ∈ F y`).

* `F_left_translate` : `F (φa·x) = {V | V.map (MulAut.conj a⁻¹) ∈ F x}`.  Proof: unfold
  `mem_F_iff'` and use `V ∈ F (φa·x) ↔ V^{a⁻¹} ∈ F x`, where `V^{a⁻¹} = {a⁻¹va}`; the pointwise
  input is the conjugation of `Rat.A V`, i.e.

    `x ∈ A V ↔ φa·x·φa⁻¹ ∈ A (V.map (MulAut.conj a))`   (`A_conj`, to be proved as a helper),

  which follows from `Rat.mem_A_iff` by transporting a term along conjugation (multiply the term
  by `a` on the left and by `a⁻¹` on the right; the conjugation of the term carries the support
  `{v}` to `{a v a⁻¹}`, using `RatU.ofGroup_mul` and, for the `RTerm.rat` clause, the identity
  `φa·(⋄t)·φa⁻¹ = ⋄(φa·t·φa⁻¹)` which is the axiom `RationalUSemiring.rat_smul` at `u = a`,
  `v = a⁻¹`).

* `F_add` : for `y, z ≠ 0`, `V ∈ F (y+z) ↔ Sy ≤ V ∧ Sz ≤ V ∧ uy⁻¹·uz ∈ V`.  Proof:
  `V ∈ F (y+z) ↔ T y V ∩ T z V ≠ ∅` (by `mem_F_add_iff`), and for `V ∈ F y ∩ F z` the coset
  structure gives `T y V = uy·V` and `T z V = uz·V`, whose intersection is non-empty exactly when
  `uy⁻¹·uz ∈ V`.  The converse: if `Sy, Sz ≤ V` and `uy⁻¹·uz ∈ V`, then `uz ∈ T y V ∩ T z V`.

* `FL_add` : the mirror of `F_add` for the left family, with `TL` in place of `T`:
  `V ∈ FL (y+z) ↔ Sy ≤ V ∧ Sz ≤ V ∧ uy·uz⁻¹ ∈ V`, where now `φuy·y ∈ A Sy` and
  `TL y V = {v·uy | v ∈ V}` is a *right* coset of `V`, so `TL y V = TL z V` iff
  `uy·uz⁻¹ ∈ V`.

* `F_mul` : for words `y, z` (so that the `⋃`-decomposition `Rat.Src.hsplit_words` applies) with
  `IsLeastF y Sy`, `IsLeastF z Sz` and `y·φuy ∈ A Sy`:
  `V ∈ F (y·z) ↔ Sy ≤ V ∧ Sz.map (MulAut.conj uy⁻¹) ≤ V`, i.e. the least element is
  `Sy ⊔ {uy⁻¹·s·uy | s ∈ Sz}`.  Proof: by `Rat.Src.hsplit_words` (applied to the words `y` and
  `z·φu`), `(y·z)·φu ∈ A V` iff there are `w, u` with `y·φw ∈ A V` and `φ(w⁻¹)·z·φu ∈ A V`; for
  `V ∈ F y` the first conjunct says `w ∈ T y V = uy·V`, and dividing the second by the resulting
  element of `A V` shows that the second conjunct is equivalent to `φ(uy⁻¹)·z·φu ∈ A V`, i.e. to
  `V ∈ F (φ(uy⁻¹)·z)`.  By `F_left_translate` this holds iff `V.map (MulAut.conj uy) ∈ F z`, i.e.
  iff `Sz ≤ V.map (MulAut.conj uy) ≤ V`.  (The two directions are: for `V ∈ F (y·z)` use the coset
  structure to replace `w` by `uy`; conversely if `Sz.map (MulAut.conj uy⁻¹) ≤ V` then
  `uy ∈ T y V` and `φ(uy⁻¹)·z·φu ∈ A V` for suitable `u`, so that `y·φuy ∈ A V` and
  `φ(uy⁻¹)·z·φu ∈ A V` give `(y·z)·φu ∈ A V`.)

* `FL_mul` : the mirror of `F_mul` for the left family: for words `y, z`, `IsLeastL y Sy`,
  `IsLeastL z Sz` and `uz` with `φuz·z ∈ A Sz` (i.e. `uz ∈ TL z Sz`, a right coset of `Sz`):
  `V ∈ FL (y·z) ↔ Sz ≤ V ∧ Sy.map (MulAut.conj uz) ≤ V`, so the least element is
  `Sz ⊔ {uz·s·uz⁻¹ | s ∈ Sy}`.  Proof: `φu·(y·z) ∈ A V` iff (by `Rat.Src.hsplit_words` applied to
  the words `φu·y` and `z`) there is `x` with `φu·y·φx ∈ A V` and `φ(x⁻¹)·z ∈ A V`; the first
  conjunct is `∃u, φu·(y·φx) ∈ A V`, i.e. `V ∈ FL (y·φx)`, which by the conjugation input
  (see `F_left_translate`) and `IsLeastL y Sy` holds iff `x⁻¹·Sy·x ≤ V`; the second says that `x⁻¹`
  lies in the coset `TL z V = V·uz`.  Writing `x⁻¹ = v·uz` with `v ∈ V`, the first condition becomes
  `v·uz·Sy·uz⁻¹·v⁻¹ ≤ V`, which is equivalent to `uz·Sy·uz⁻¹ ≤ V` because `v ∈ V` (the subgroup
  `⟨v, vTv⁻¹⟩` contains `T`).  The converse takes `x = uz⁻¹`.

## The induction

The induction proves `(∃ S, IsLeastF x S) ∧ (∃ S, IsLeastL x S)` for all `x : RatU U` by
well-founded induction on `Rat.treeOfRat U x`:

* `x = 0`, `x = φu`: `⊥` works (`isLeastF_zero`, `isLeastF_ofGroup`, ...);
* `x = y⋄`: use the duality `Rat.F_ratOp_eq_FL` and `Rat.FL_ratOp_eq_F` (`isLeastF_ratOp`) and the
  induction hypothesis at `y` (whose complexity is strictly smaller by `RatU.exists_decomp`);
* `x = y + z` with `y, z ≠ 0`: `F_add` and `FL_add`, with `Sy`, `Sz` the least elements given by
  the induction hypothesis and `uy`, `uz` arbitrary elements of the non-empty translate sets;
* `x = y·z` with `y, z` words: `F_mul` for `F`, and the duality together with `F_mul` applied to
  the pair of words `(z⋄, y⋄)` for `FL` (note `F ((y·z)⋄) = F (z⋄·y⋄) = FL (y·z)`).

The target `Rat.source_subgroup_exists` then follows from the `F`-part by
`Rat.exists_source_subgroup_weak_of_le`.
-/

set_option autoImplicit false

namespace Work.ORHughesFree.Rat

open Work.ORHughesFree
open Work.ORHughesFree.Rat.FreeProduct

variable {U : Type} [Group U]

/-! ### The two "least element" predicates -/

/-- `IsLeastF x S`: `S` is the least element of the family `Rat.F x = {V | x ∈ Rat(V)·U}`. -/
def IsLeastF (x : RatU U) (S : Subgroup U) : Prop :=
  S ∈ F x ∧ ∀ V : Subgroup U, V ∈ F x → S ≤ V

/-- `IsLeastL x S`: `S` is the least element of the *left* family
`Rat.FL x = {V | ∃ u, φu·x ∈ Rat(V)}`. -/
def IsLeastL (x : RatU U) (S : Subgroup U) : Prop :=
  S ∈ FL x ∧ ∀ V : Subgroup U, V ∈ FL x → S ≤ V

theorem IsLeastF.mem {x : RatU U} {S : Subgroup U} (h : IsLeastF x S) : S ∈ F x := h.1

theorem IsLeastF.le {x : RatU U} {S : Subgroup U} (h : IsLeastF x S) {V : Subgroup U}
    (hV : V ∈ F x) : S ≤ V := h.2 V hV

theorem IsLeastL.mem {x : RatU U} {S : Subgroup U} (h : IsLeastL x S) : S ∈ FL x := h.1

theorem IsLeastL.le {x : RatU U} {S : Subgroup U} (h : IsLeastL x S) {V : Subgroup U}
    (hV : V ∈ FL x) : S ≤ V := h.2 V hV

/-! ### The right and left tail sets -/

/-- The right translate set of `x` at the level `V` is `Orbit.T (supp (Psi x)) V`, by the support
criterion `Rat.mem_A_mul_ofGroup_iff`. -/
theorem mem_T_iff (x : RatU U) (V : Subgroup U) (u : U) :
    u ∈ Orbit.T (Psi x).coeff.support V ↔ x * RatU.ofGroup u ∈ A V :=
  (mem_A_mul_ofGroup_iff V x u).symm

/-- The left translate set of `x` at the level `V`, by the support criterion
`Rat.mem_ofGroup_mul_A_iff`. -/
theorem mem_TL_iff (x : RatU U) (V : Subgroup U) (u : U) :
    u ∈ {u : U | RatU.ofGroup u * x ∈ A V} ↔ RatU.ofGroup u * x ∈ A V :=
  Iff.rfl

/-- `V ∈ Rat.F x` iff the translate set of `x` at `V` is non-empty. -/
theorem nonempty_T_iff (x : RatU U) (V : Subgroup U) :
    (Orbit.T (Psi x).coeff.support V).Nonempty ↔ V ∈ F x :=
  (Orbit.mem_F_iff_T_nonempty x V).symm

/-- `V ∈ Rat.FL x` iff the left translate set of `x` at `V` is non-empty. -/
theorem nonempty_TL_iff (x : RatU U) (V : Subgroup U) :
    (Set.Nonempty {u : U | RatU.ofGroup u * x ∈ A V}) ↔ V ∈ FL x := by
  constructor
  · rintro ⟨u, hu⟩
    exact (mem_BL_iff_ofGroup_mul).mpr ⟨u, hu⟩
  · intro hV
    exact (mem_BL_iff_ofGroup_mul).mp hV

/-! ### Non-vanishing -/

theorem ofGroup_ne_zero (u : U) : (RatU.ofGroup u : RatU U) ≠ 0 := fun h =>
  Tree.one_ne_zero
    (by rw [← Rat.treeOfRat_ofGroup u, h, Rat.treeOfRat_zero])

theorem mul_ofGroup_ne_zero {x : RatU U} (hx : x ≠ 0) (u : U) :
    x * RatU.ofGroup u ≠ 0 :=
  RatU.mul_ne_zero hx (ofGroup_ne_zero u)

theorem ofGroup_mul_ne_zero {x : RatU U} (hx : x ≠ 0) (u : U) :
    RatU.ofGroup u * x ≠ 0 :=
  RatU.mul_ne_zero (ofGroup_ne_zero u) hx

/-! ### The coset structure of the translate sets -/

/-- **The right translate set of `x ≠ 0` at a level `V ∈ Rat.F x` is a right coset of `V`.**

If `u₀` is any translate of `x` with `x·φu₀ ∈ Rat.A V`, then for every `u` with `x·φu ∈ Rat.A V`
one has `u₀⁻¹u ∈ V`, by the translate dichotomy `Rat.Dich.both_of_ne_zero`. -/
theorem T_eq_coset {x : RatU U} (hx : x ≠ 0) {V : Subgroup U} (hV : V ∈ F x) {u₀ : U}
    (hu₀ : u₀ ∈ Orbit.T (Psi x).coeff.support V) :
    Orbit.T (Psi x).coeff.support V = {u : U | ∃ v ∈ V, u = u₀ * v} := by
  have hmem : x * RatU.ofGroup u₀ ∈ A V := (mem_T_iff x V u₀).mp hu₀
  have hb0 : x * RatU.ofGroup u₀ ≠ 0 := mul_ofGroup_ne_zero hx u₀
  ext u
  rw [mem_T_iff]
  constructor
  · intro hu
    have hkey : (x * RatU.ofGroup u₀) * RatU.ofGroup (u₀⁻¹ * u) = x * RatU.ofGroup u := by
      rw [mul_assoc, ← RatU.ofGroup_mul, mul_inv_cancel_left]
    have h := (Dich.both_of_ne_zero (x * RatU.ofGroup u₀) hb0).1 V (u₀⁻¹ * u) hmem
      (by rw [hkey]; exact hu)
    exact ⟨u₀⁻¹ * u, h, (mul_inv_cancel_left u₀ u).symm⟩
  · rintro ⟨v, hv, rfl⟩
    have hkey : x * RatU.ofGroup (u₀ * v) = (x * RatU.ofGroup u₀) * RatU.ofGroup v := by
      rw [RatU.ofGroup_mul, mul_assoc]
    rw [hkey]
    exact (Weak.ASub V).mul_mem hmem (Weak.A_ofGroup_mem hv)

/-- **The left translate set of `x ≠ 0` at a level `V ∈ Rat.FL x` is a right coset of `V`.**

If `φu₀·x ∈ Rat.A V`, then for every `u` with `φu·x ∈ Rat.A V` one has `u·u₀⁻¹ ∈ V`, by the
translate dichotomy. -/
theorem TL_eq_coset {x : RatU U} (hx : x ≠ 0) {V : Subgroup U} (hV : V ∈ FL x) {u₀ : U}
    (hu₀ : RatU.ofGroup u₀ * x ∈ A V) :
    {u : U | RatU.ofGroup u * x ∈ A V} = {u : U | ∃ v ∈ V, u = v * u₀} := by
  have hb0 : RatU.ofGroup u₀ * x ≠ 0 := ofGroup_mul_ne_zero hx u₀
  ext u
  constructor
  · intro hu
    have hkey : RatU.ofGroup (u * u₀⁻¹) * (RatU.ofGroup u₀ * x) = RatU.ofGroup u * x := by
      rw [RatU.ofGroup_mul]
      rw [mul_assoc (RatU.ofGroup u) (RatU.ofGroup u₀⁻¹) (RatU.ofGroup u₀ * x)]
      rw [← mul_assoc (RatU.ofGroup u₀⁻¹) (RatU.ofGroup u₀) x]
      rw [← RatU.ofGroup_mul, inv_mul_cancel, RatU.ofGroup_one, one_mul]
    have h := (Dich.both_of_ne_zero (RatU.ofGroup u₀ * x) hb0).2 V (u * u₀⁻¹) hu₀
      (by rw [hkey]; exact hu)
    exact ⟨u * u₀⁻¹, h, by group⟩
  · rintro ⟨v, hv, rfl⟩
    show RatU.ofGroup (v * u₀) * x ∈ A V
    have hkey : RatU.ofGroup (v * u₀) * x = RatU.ofGroup v * (RatU.ofGroup u₀ * x) := by
      rw [RatU.ofGroup_mul, mul_assoc]
    rw [hkey]
    exact (Weak.ASub V).mul_mem (Weak.A_ofGroup_mem hv) hu₀

/-! ### The base cases -/

theorem FL_zero : FL (0 : RatU U) = Set.univ := by
  ext V
  refine iff_of_true ?_ trivial
  show (0 : RatU U) ∈ BL V
  rw [mem_BL_iff_ofGroup_mul]
  exact ⟨1, by rw [RatU.ofGroup_one, one_mul]; exact (Weak.ASub V).zero_mem⟩

theorem FL_ofGroup (u : U) : FL (RatU.ofGroup u) = Set.univ := by
  ext V
  refine iff_of_true ?_ trivial
  show (RatU.ofGroup u : RatU U) ∈ BL V
  rw [mem_BL_iff_ofGroup_mul]
  refine ⟨u⁻¹, ?_⟩
  rw [← RatU.ofGroup_mul, inv_mul_cancel, RatU.ofGroup_one]
  exact A_one V

theorem isLeastF_zero : IsLeastF (0 : RatU U) ⊥ :=
  ⟨by rw [F_zero]; trivial, fun _ _ => bot_le⟩

theorem isLeastL_zero : IsLeastL (0 : RatU U) ⊥ :=
  ⟨by rw [FL_zero]; trivial, fun _ _ => bot_le⟩

theorem isLeastF_ofGroup (u : U) : IsLeastF (RatU.ofGroup u) ⊥ :=
  ⟨by rw [F_ofGroup]; trivial, fun _ _ => bot_le⟩

theorem isLeastL_ofGroup (u : U) : IsLeastL (RatU.ofGroup u) ⊥ :=
  ⟨by rw [FL_ofGroup]; trivial, fun _ _ => bot_le⟩

/-! ### The `⋄`-case (the duality `Rat.F (x⋄) = Rat.FL x`)

These are immediate from `Rat.F_ratOp_eq_FL` and `Rat.FL_ratOp_eq_F`. -/

theorem isLeastF_ratOp {x : RatU U} {S : Subgroup U} (h : IsLeastL x S) :
    IsLeastF (RatU.ratOp x) S := by
  have hset : F (RatU.ratOp x) = FL x := F_ratOp_eq_FL x
  exact ⟨by rw [hset]; exact h.1, fun V hV => h.2 V (by rwa [hset] at hV)⟩

theorem isLeastL_ratOp {x : RatU U} {S : Subgroup U} (h : IsLeastF x S) :
    IsLeastL (RatU.ratOp x) S := by
  have hset : FL (RatU.ratOp x) = F x := FL_ratOp_eq_F x
  exact ⟨by rw [hset]; exact h.1, fun V hV => h.2 V (by rwa [hset] at hV)⟩

end Work.ORHughesFree.Rat
