import Mathlib
import Submission.Work.CharCore.Main
import Submission.Work.Coherence.All
import Submission.Work.Induction.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Tame` — Feit–Thompson §9–§10 (tamely imbedded subsets, coherent sets of characters)

This is the base module of the "Tame" area (area P2-04 of the Feit–Thompson drive).  It fixes the
vocabulary of Chapter III of

  W. Feit and J. G. Thompson, *Solvability of groups of odd order*, Pacific J. Math. **13** (1963),
  775–1029,

namely

* Definition 9.1 (p. 803–804): a *tamely imbedded subset* `L̂` of a finite group `X`, with a system
  of *supporting subgroups* `𝔎_1, …, 𝔎_n`;
* (9.2)–(9.5) (p. 805): the sets `𝔏_i`, `𝔄_L`, and the Dade-type map `τ` defined by (9.4);
* Definition 10.1 (p. 809): *coherent* sets of generalized characters (`FTCoherent`);
* Definition 10.2 (p. 811): *subcoherent* pairs (`Subcoherent`).

## Conventions

* The ambient finite group is `X`; characters are `ℂ`-valued functions, and the inner product is
  `Work.CharCore.cfInner` (definitionally `Work.Coherence.cfInner`), as in areas CharCore /
  Induction / Coherence.
* Subsets of `X` (such as `L̂`) are `Set X`; subgroups are `Subgroup X`, coerced to sets when
  needed.  `𝔏 = N(L̂)` is the **set** normalizer `Subgroup.normalizer Lhat`, written `Lgrp Lhat`.
* "`S`-subgroup" (Feit–Thompson's term for a Hall subgroup) is `IsHallIn`; a "T. I. set" is
  `IsTISet` (Feit–Thompson §2).

Everything is stated for an arbitrary finite group: Chapter III does not use the odd-order or
minimal-simple hypotheses (Feit–Thompson say so explicitly).
-/

noncomputable section

open Classical
open scoped Pointwise

namespace Work.Tame

universe u

variable {X : Type u}

section GroupOnly

variable [Group X]

/-! ## Elementary vocabulary: T. I. sets, `S`-subgroups, support sets -/

/-- `A^#`, the set of *non-identity* elements of `A`. -/
def punct (A : Set X) : Set X := A \ {1}

@[simp] theorem mem_punct {A : Set X} {x : X} : x ∈ punct A ↔ x ∈ A ∧ x ≠ 1 := by
  simp [punct]

/-- `A` is a **T. I. set** ("trivial intersection set") of `X` (Feit–Thompson §2): for every
`x : X`, either `A^x ∩ A ⊆ {1}` or `A^x = A`, where `A^x = {x⁻¹ a x | a ∈ A}`.

Feit–Thompson write `𝔄^x` for the conjugate set. -/
def IsTISet (A : Set X) : Prop :=
  ∀ x : X,
    ((fun a => x⁻¹ * a * x) '' A) ∩ A ⊆ ({1} : Set X) ∨ (fun a => x⁻¹ * a * x) '' A = A

/-- `H` is an **`S`-subgroup** of `K` (Feit–Thompson §2: a Hall subgroup): `H ≤ K` and
`(|H|, |K : H|) = 1`. -/
def IsHallIn (H K : Subgroup X) : Prop := H ≤ K ∧ (Nat.card H).Coprime (H.relIndex K)

/-! ## Definition 9.1 (Feit–Thompson, p. 803–804) -/

/-- Feit–Thompson's `𝔏 = N(L̂)`: the normalizer of the subset `L̂ ⊆ X` as a subgroup of `X`. -/
def Lgrp (Lhat : Set X) : Subgroup X := Subgroup.normalizer Lhat

@[simp] theorem mem_Lgrp {Lhat : Set X} {x : X} :
    x ∈ Lgrp Lhat ↔ ∀ a : X, a ∈ Lhat ↔ x * a * x⁻¹ ∈ Lhat := Iff.rfl

/-- Feit–Thompson's `𝔏₀` (Definition 9.1, p. 803): the elements of `L̂^#` whose centralizer in `X`
is contained in `𝔏 = N(L̂)`.

Feit–Thompson write "the set of elements `L` in `L̂` such that `C(L) ⊆ 𝔏`" and then define
`𝔇 = L̂^# - 𝔏₀`, so `𝔏₀ ⊆ L̂^#`; the two readings differ only when `𝔏 = N(L̂) = X` (the only case in
which `C 1 = X ⊆ 𝔏`), and the reading `𝔏₀ ⊆ L̂^#` is forced by Feit–Thompson's own corollary to
Lemma 9.5 ("`|𝔛₀|/|𝔛| = |L̂^#|/|𝔏|` for `θ = 1_𝔛`"), which would fail if `1 ∈ 𝔛₀`. -/
def L0set (Lhat : Set X) : Set X :=
  {l | l ∈ Lhat ∧ l ≠ 1 ∧ Subgroup.centralizer ({l} : Set X) ≤ Lgrp Lhat}

@[simp] theorem mem_L0set {Lhat : Set X} {l : X} :
    l ∈ L0set Lhat ↔ l ∈ Lhat ∧ l ≠ 1 ∧
      Subgroup.centralizer ({l} : Set X) ≤ Lgrp Lhat := Iff.rfl

/-- Feit–Thompson's `𝔇 = L̂^# - 𝔏₀` (Definition 9.1, p. 803). -/
def Dset (Lhat : Set X) : Set X :=
  {l | l ∈ Lhat ∧ l ≠ 1 ∧ ¬ (Subgroup.centralizer ({l} : Set X) ≤ Lgrp Lhat)}

@[simp] theorem mem_Dset {Lhat : Set X} {l : X} :
    l ∈ Dset Lhat ↔ l ∈ Lhat ∧ l ≠ 1 ∧ ¬ (Subgroup.centralizer ({l} : Set X) ≤ Lgrp Lhat) :=
  Iff.rfl

theorem Dset_subset (Lhat : Set X) : Dset Lhat ⊆ punct Lhat := fun _ h => ⟨h.1, h.2.1⟩

/-- Definition 9.1(ii)(e), p. 804: for a subgroup `K = 𝔎` with normalizer `𝔑 = N(K)`,
`⋃_{H ∈ K^#} C_𝔑(H)`. -/
def hatNCore (K : Subgroup X) : Set X :=
  ⋃ H ∈ punct (K : Set X),
    (((Subgroup.centralizer ({H} : Set X) ⊓ Lgrp K : Subgroup X)) : Set X)

/-- Definition 9.1(ii)(e), p. 804: `Ñ = (⋃_{H ∈ K^#} C_{N(K)}(H)) - K^#`.  The non-identity
elements of `Ñ` are required to form a non-empty T. I. set. -/
def hatN (K : Subgroup X) : Set X :=
  hatNCore K \ punct (K : Set X)

/-- The *punctured* set `Ñ^#` of Definition 9.1(ii)(e). -/
def hatNp (K : Subgroup X) : Set X := punct (hatN K)

/-- Feit–Thompson's `𝔏_i = {L ∈ 𝔇 | C(L) ⊆ 𝔑_i}` (p. 805), for a supporting subgroup `K = 𝔎_i`;
with `K = ⊥` (their `𝔎_0 = 1`, `𝔑_0 = X`) this is `𝔇` itself. -/
def Lset (Lhat : Set X) (K : Subgroup X) : Set X :=
  {l | l ∈ Dset Lhat ∧ Subgroup.centralizer ({l} : Set X) ≤ Lgrp K}

/-- Feit–Thompson's `𝔄_L = {LH | LH = HL, H ∈ 𝔎_i} = L{𝔎_i ∩ C(L)} ((9.2), p. 805), for a
supporting subgroup `K = 𝔎_i`. -/
def AL (L : X) (K : Subgroup X) : Set X :=
  {x | ∃ H : X, H ∈ K ∧ L * H = H * L ∧ x = L * H}

/-- Feit–Thompson's index for the sets `𝔏_0, 𝔏_1, …, 𝔏_n` of p. 805: `none` stands for `i = 0`
(`𝔎_0 = 1`, `𝔏_0` the set of Definition 9.1) and `some i` for the supporting subgroup `𝔎_i`. -/
abbrev Idx (n : ℕ) : Type := Option (Fin n)

/-- Feit–Thompson's `𝔏_j` (p. 805): `𝔏_0 = {L ∈ L̂ | C(L) ⊆ 𝔏}` is the set `𝔏_0` of Definition 9.1,
and `𝔏_i = {L ∈ 𝔇 | C(L) ⊆ 𝔑_i}` for a supporting subgroup `𝔎_i` (`𝔑_i = N(𝔎_i)`). -/
def LofIdx (Lhat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X) : Idx n → Set X
  | none => L0set Lhat
  | some i => Lset Lhat (Hs i)

/-- Feit–Thompson's `𝔄_L` ((9.2), p. 805): `{L}` when `L ∈ 𝔏_0`, and `L{𝔎_i ∩ C(L)}` when
`L ∈ 𝔏_i`. -/
def ALofIdx (Lhat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X) : Idx n → X → Set X
  | none => fun L => {L}
  | some i => fun L => AL L (Hs i)

/-- The union of the `𝔄_L` over all `L ∈ ⋃_{i=0}^n 𝔏_i`, i.e. the support of `α^τ` in
Feit–Thompson's Lemma 9.1. -/
def AU (Lhat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X) : Set X :=
  ⋃ j : Idx n, ⋃ L ∈ LofIdx Lhat n Hs j, ALofIdx Lhat n Hs j L

/-- Feit–Thompson's `𝔛₀` (Lemma 9.5): the elements of `X` which are conjugate to an element of
`𝔄_L` for some `L ∈ ⋃_{i=0}^n 𝔏_i`. -/
def X0 (Lhat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X) : Set X :=
  ⋃ x : X, (fun a => x * a * x⁻¹) '' AU Lhat n Hs

/-- **Definition 9.1** (Feit–Thompson, p. 803–804).  `L̂` is *tamely imbedded* in `X`, with
supporting subgroups `Hs : Fin n → Subgroup X` (Feit–Thompson's `𝔎_1, …, 𝔎_n`).

* (9.1) `⟨1⟩ ⊆ L̂ ⊆ N(L̂)`;
* (i) elements of `L̂` conjugate in `X` are conjugate in `𝔏 = N(L̂)`;
* (ii) if `𝔇 ≠ ∅` then `n ≥ 1` and, writing `𝔑_i = N(𝔎_i)`, for every `i`:
  `|𝔎_i|` is coprime to `|𝔎_j|` (`j ≠ i`), `𝔎_i` is an `S`-subgroup of `𝔑_i`,
  `𝔑_i = 𝔎_i(𝔏 ∩ 𝔑_i)`, `𝔎_i ∩ 𝔏 = 1`, `(|𝔎_i|, |C_𝔏(L)|) = 1` for `L ∈ L̂^#`, and `Ñ_i^#`
  is a non-empty T. I. set with `N(Ñ_i) = 𝔑_i`;
* (iii) every `L₀ ∈ 𝔇` has a conjugate `L ∈ L̂` with `C(L) = C_{𝔎_i}(L)·C_𝔏(L) ⊆ 𝔑_i` for some `i`.
-/
structure IsTamelyImbedded (Lhat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X) : Prop where
  /-- (9.1): `⟨1⟩ ⊆ L̂`. -/
  one_mem : (1 : X) ∈ Lhat
  /-- (9.1): `L̂ ⊆ N(L̂)`. -/
  sub_norm : Lhat ⊆ (Lgrp Lhat : Set X)
  /-- (i): two elements of `L̂` conjugate in `X` are conjugate in `𝔏 = N(L̂)`. -/
  conj : ∀ ⦃a : X⦄, a ∈ Lhat → ∀ ⦃b : X⦄, b ∈ Lhat → IsConj a b →
    ∃ l ∈ Lgrp Lhat, b = l * a * l⁻¹
  /-- (ii): if `𝔇` is non-empty there is at least one supporting subgroup. -/
  supp_one_le : (Dset Lhat).Nonempty → 1 ≤ n
  /-- (ii): the supporting subgroups are non-trivial. -/
  supp_ne_bot : (Dset Lhat).Nonempty → ∀ i : Fin n, Hs i ≠ ⊥
  /-- (ii)(a): `(|𝔎_i|, |𝔎_j|) = 1` for `i ≠ j`. -/
  supp_coprime : (Dset Lhat).Nonempty → ∀ i j : Fin n, i ≠ j →
    (Nat.card (Hs i)).Coprime (Nat.card (Hs j))
  /-- (ii)(b): `𝔎_i` is an `S`-subgroup of `𝔑_i = N(𝔎_i)`. -/
  supp_hall : (Dset Lhat).Nonempty → ∀ i : Fin n, IsHallIn (Hs i) (Lgrp (Hs i))
  /-- (ii)(c): `𝔑_i = 𝔎_i(𝔏 ∩ 𝔑_i)`. -/
  supp_prod : (Dset Lhat).Nonempty → ∀ i : Fin n,
    Lgrp (Hs i) = Hs i ⊔ (Lgrp Lhat ⊓ Lgrp (Hs i))
  /-- (ii)(c): `𝔎_i ∩ 𝔏 = 1`. -/
  supp_inf : (Dset Lhat).Nonempty → ∀ i : Fin n, Hs i ⊓ Lgrp Lhat = ⊥
  /-- (ii)(d): `(|𝔎_i|, |C_𝔏(L)|) = 1` for `L ∈ L̂^#`. -/
  supp_coprime_cent : (Dset Lhat).Nonempty → ∀ i : Fin n, ∀ l : X, l ∈ Lhat → l ≠ 1 →
    (Nat.card (Hs i)).Coprime (Nat.card ↥(Lgrp Lhat ⊓ Subgroup.centralizer ({l} : Set X)))
  /-- (ii)(e): `Ñ_i^#` is a T. I. set in `X`. -/
  supp_ti : (Dset Lhat).Nonempty → ∀ i : Fin n, IsTISet (hatNp (Hs i))
  /-- (ii)(e): `Ñ_i^#` is non-empty. -/
  supp_hatN_nonempty : (Dset Lhat).Nonempty → ∀ i : Fin n, (hatNp (Hs i)).Nonempty
  /-- (ii)(e): `N(Ñ_i) = 𝔑_i`. -/
  supp_hatN_norm : (Dset Lhat).Nonempty → ∀ i : Fin n,
    Subgroup.normalizer (hatN (Hs i)) = Lgrp (Hs i)
  /-- (iii): every `L₀ ∈ 𝔇` has a conjugate `L ∈ L̂` with
  `C(L) = C_{𝔎_i}(L)·C_𝔏(L) ⊆ 𝔑_i`. -/
  cover : ∀ l₀ : X, l₀ ∈ Dset Lhat →
    ∃ l ∈ Lhat, IsConj l₀ l ∧ ∃ i : Fin n,
      Subgroup.centralizer ({l} : Set X) =
        (Hs i ⊓ Subgroup.centralizer ({l} : Set X)) ⊔
          (Lgrp Lhat ⊓ Subgroup.centralizer ({l} : Set X)) ∧
      Subgroup.centralizer ({l} : Set X) ≤ Lgrp (Hs i)

/-- The data of Definition 9.1 is *non-degenerate* when either `𝔇 ≠ ∅` — in which case the
system of supporting subgroups with the properties (ii)(a)–(e) is asserted to exist — or there
are no supporting subgroups at all (`n = 0`), which by Feit–Thompson p. 804 is the case in which
`L̂` is a T. I. set.  (When `𝔇 = ∅` and `n = 0`, `𝔏_i = ∅` for every `i`, so all the statements
about the `𝔄_L` are vacuous and `τ` is just induction from `𝔏`.) -/
def HasTameData (Lhat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X) : Prop :=
  (Dset Lhat).Nonempty ∨ n = 0

/-- `x` is conjugate in `X` to an element of `𝔄_L` for some `L ∈ ⋃_{i=0}^n 𝔏_i`
(the support condition of Feit–Thompson's Lemma 9.1). -/
def inConjAU (Lhat : Set X) (n : ℕ) (Hs : Fin n → Subgroup X) (x : X) : Prop :=
  ∃ j : Idx n, ∃ L : ↥(Lgrp Lhat), (L : X) ∈ LofIdx Lhat n Hs j ∧
    ∃ A ∈ ALofIdx Lhat n Hs j (L : X), IsConj x A

end GroupOnly

section Finite

variable [Group X] [Fintype X]

/-- Feit–Thompson Lemma 10.4 (p. 815): `a`, the least common multiple of the orders of the
elements of `L̂`. -/
noncomputable def LhatExponent (Lhat : Set X) : ℕ :=
  ((Finset.univ : Finset ↥(Lgrp Lhat)).filter (fun l => (l : X) ∈ Lhat)).lcm (fun l => orderOf l)


/-! ## The class function spaces `𝓒(L̂)`, `𝓒₀(L̂)`, `𝓘₀(L̂)` -/

theorem isClassFun_add' {f g : X → ℂ} (hf : CharCore.IsClassFun f) (hg : CharCore.IsClassFun g) :
    CharCore.IsClassFun (f + g) := by
  intro a b
  simp only [Pi.add_apply, hf a b, hg a b]

theorem isClassFun_neg' {f : X → ℂ} (hf : CharCore.IsClassFun f) :
    CharCore.IsClassFun (-f) := by
  intro a b
  simp only [Pi.neg_apply, hf a b]

theorem isClassFun_zero' : CharCore.IsClassFun (0 : X → ℂ) := fun _ _ => rfl

/-- `𝓒(L̂)` (Feit–Thompson, p. 804): the complex valued class functions of `𝔏 = N(L̂)` which
vanish outside `L̂`. -/
def Cfun (Lhat : Set X) : AddSubgroup (↥(Lgrp Lhat) → ℂ) where
  carrier := {f | CharCore.IsClassFun f ∧ ∀ l : ↥(Lgrp Lhat), (l : X) ∉ Lhat → f l = 0}
  zero_mem' := ⟨isClassFun_zero', by intro l _; rfl⟩
  add_mem' := fun hf hg => ⟨isClassFun_add' hf.1 hg.1,
    fun l hl => by simp only [Pi.add_apply, hf.2 l hl, hg.2 l hl, add_zero]⟩
  neg_mem' := fun hf => ⟨isClassFun_neg' hf.1,
    fun l hl => by simp only [Pi.neg_apply, hf.2 l hl, neg_zero]⟩

/-- `𝓒₀(L̂)` (Feit–Thompson, p. 804): the complex valued class functions of `𝔏` which vanish
outside `L̂` **and at `1`**. -/
def C0 (Lhat : Set X) : AddSubgroup (↥(Lgrp Lhat) → ℂ) where
  carrier := {f | CharCore.IsClassFun f ∧
    (∀ l : ↥(Lgrp Lhat), (l : X) ∉ Lhat → f l = 0) ∧ f 1 = 0}
  zero_mem' := ⟨isClassFun_zero', (by intro l _; rfl), rfl⟩
  add_mem' := fun hf hg => ⟨isClassFun_add' hf.1 hg.1,
    (fun l hl => by simp only [Pi.add_apply, hf.2.1 l hl, hg.2.1 l hl, add_zero]),
    (by simp only [Pi.add_apply, hf.2.2, hg.2.2, add_zero])⟩
  neg_mem' := fun hf => ⟨isClassFun_neg' hf.1,
    (fun l hl => by simp only [Pi.neg_apply, hf.2.1 l hl, neg_zero]),
    (by simp only [Pi.neg_apply, hf.2.2, neg_zero])⟩

@[simp] theorem mem_C0 {Lhat : Set X} {f : ↥(Lgrp Lhat) → ℂ} :
    f ∈ C0 Lhat ↔ CharCore.IsClassFun f ∧
      (∀ l : ↥(Lgrp Lhat), (l : X) ∉ Lhat → f l = 0) ∧ f 1 = 0 := Iff.rfl

@[simp] theorem mem_Cfun {Lhat : Set X} {f : ↥(Lgrp Lhat) → ℂ} :
    f ∈ Cfun Lhat ↔ CharCore.IsClassFun f ∧
      ∀ l : ↥(Lgrp Lhat), (l : X) ∉ Lhat → f l = 0 := Iff.rfl

/-- `𝓘₀(L̂)` (Feit–Thompson, p. 804): the *generalized* characters of `𝔏 = N(L̂)` vanishing
outside `L̂` and at `1`. -/
def I0 (Lhat : Set X) : Set (↥(Lgrp Lhat) → ℂ) :=
  {f | CharCore.IsVChar f ∧ (∀ l : ↥(Lgrp Lhat), (l : X) ∉ Lhat → f l = 0) ∧ f 1 = 0}

@[simp] theorem mem_I0 {Lhat : Set X} {f : ↥(Lgrp Lhat) → ℂ} :
    f ∈ I0 Lhat ↔ CharCore.IsVChar f ∧
      (∀ l : ↥(Lgrp Lhat), (l : X) ∉ Lhat → f l = 0) ∧ f 1 = 0 := Iff.rfl

theorem I0_subset_C0 {Lhat : Set X} : I0 Lhat ⊆ (C0 Lhat : Set (↥(Lgrp Lhat) → ℂ)) :=
  fun f hf => ⟨hf.1.isClassFun, hf.2.1, hf.2.2⟩

end Finite

end Work.Tame
