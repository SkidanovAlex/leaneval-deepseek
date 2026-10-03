import Mathlib

/-!
# Tao's Ionescu–Wainger vocabulary

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066,
local copy `REFS/Tao_2008.05066_IonescuWainger.tex`.

## Why this file exists

The `1 < p < 2` half of `Submission.BourgainPlan.MaximalStatement` needs, as its one deep input,
an **Ionescu–Wainger multiplier theorem**: an `\ell^p(\Z^d)` bound, uniform in the set `S` of
moduli, for multipliers of the form

`m(ξ) = Σ_{α ∈ Σ_{≤k}} ε_α · θ(ξ − α) · η((ξ − α)/ε)`,

where `Σ_{≤k}` is the union of the torsion subgroups `T[q]`, `q` a product of at most `k`
pairwise coprime integers from `S`, `θ` has bounded `L^{2r}`-multiplier norm and `ε` is small.

The cleanest account of the proof is Tao's, who gives an *adelic-free* real form
(Theorem `main` of the paper) and derives the sharp major-arc sets from a set `S` of pairwise
coprime integers (Lemma `iwac`).  That proof rests on the three blocks below, in this file's
vocabulary:

* **superorthogonality** (Tao §2, following Pierce): a family of functions, indexed by a finite
  set or by a family of subsets, such that the integral `∫ ∏_j ⟨f_{s_j}, f_{s_{r+j}}⟩` vanishes
  whenever the tuple carries a *nonce*; then a Khintchine-type square-function inequality holds;
* the **sunflower** combinatorics (Tao §3): a probabilistic Erdős–Rado theorem, from which the
  square function of a `k`-hypersystem is controlled by its sum over sunflowers;
* the **major-arc construction** (Tao §5, Lemma `iwac`): a set `S` of *pairwise coprime* integers
  such that the classical Farey arcs `T[q]`, `q ≤ N`, are all contained in the arc set of depth
  `k = ⌊2/ρ⌋ + 1` built from `S`, with all elements of `S` at most `~ N`.

## Decomposition (the modules requested on top of this file)

1. `BourgainPlan/IonescuWainger/superorthogonal_khintchine` — Theorem `sys-ortho`(i):
   the Khintchine inequality for a Type II `2r`-superorthogonal *system*.
2. `BourgainPlan/IonescuWainger/sunflower_square_function` — Corollary `sunsquare` (first
   inequality), in the pointwise ("for each `x`") form; the `k = 1` case is IW Lemma 2.3.
3. `BourgainPlan/IonescuWainger/superorthogonal_khintchine_hypersystem` — Theorem `sys-ortho`(ii):
   the hypersystem form, needed for the arcs indexed by *subsets* of `S`.
4. `BourgainPlan/IonescuWainger/farey_cover_by_taoSetS` — Lemma `iwac`(i): the Farey cover.
5. `BourgainPlan/IonescuWainger/taoSetS_coprime` — pairwise coprimality of `S`.
6. (next) the *application of orthogonality* (Tao, Theorem `ortho-apply`) turning these into the
   `\ell^{2r}` bound for multipliers localized on the major arcs, and hence the Ionescu–Wainger
   multiplier theorem itself; the sampling principle of Magyar–Stein–Wainger (Tao, Proposition
   `msw`, Theorem `qss`) is the other reusable piece needed to pass between `ℝ^d` and `\Z^d`.

Everything here is stated for a general finite index set so that the results are reusable
harmonic analysis, not only bookkeeping for this project.
-/

open Finset
open scoped BigOperators

set_option autoImplicit false

namespace Work.BourgainPlan.IonescuWainger

/-- A tuple `s` of indices **has a nonce** if some value occurs exactly once in it.  This is Tao's
Definition `nonceflower`(i) applied to the collection of singletons `{s k}`: an element belonging
to exactly one of them is exactly a value of multiplicity one. -/
def HasNonceTuple {κ ι : Type*} (s : κ → ι) : Prop :=
  ∃ j : κ, ∀ k : κ, k ≠ j → s k ≠ s j

/-- A family of sets **has a nonce**: an element of the union that belongs to exactly one member. -/
def HasNonce {ι α : Type*} [DecidableEq α] (A : ι → Finset α) : Prop :=
  ∃ a : α, ∃ i : ι, a ∈ A i ∧ ∀ j : ι, a ∈ A j → j = i

/-- A family of sets is a **sunflower** if it has a common core and pairwise disjoint petals. -/
def IsSunflower {ι α : Type*} [DecidableEq α] (A : ι → Finset α) : Prop :=
  ∃ A₀ : Finset α, (∀ i, A₀ ⊆ A i) ∧ ∀ i j, i ≠ j → Disjoint (A i \ A₀) (A j \ A₀)

/-- The product of all prime powers `p^{⌊log N / log p⌋}` with `p ≤ N^{ρ/2}` (this is one element of
Tao's set `S`). -/
noncomputable def smallPrimePowerProd (ρ : ℝ) (N : ℕ) : ℕ :=
  ∏ p ∈ (Finset.Icc 2 ⌊(N : ℝ) ^ (ρ / 2)⌋₊).filter Nat.Prime,
    p ^ ⌊Real.log N / Real.log p⌋₊

/-- The individual prime powers `p^{⌊log N / log p⌋}` with `N^{ρ/2} < p ≤ N`, `p` prime. -/
noncomputable def largePrimePowers (ρ : ℝ) (N : ℕ) : Finset ℕ :=
  ((Finset.Icc (⌊(N : ℝ) ^ (ρ / 2)⌋₊ + 1) N).filter Nat.Prime).image
    (fun (p : ℕ) => p ^ ⌊Real.log N / Real.log p⌋₊)

/-- **Tao's major-arc set** (Lemma `iwac`): `S = {∏_{p ≤ N^{ρ/2}} p^{⌊log N/log p⌋}} ∪
{p^{⌊log N/log p⌋} : N^{ρ/2} < p ≤ N}`. -/
noncomputable def taoSetS (ρ : ℝ) (N : ℕ) : Finset ℕ :=
  insert (smallPrimePowerProd ρ N) (largePrimePowers ρ N)

end Work.BourgainPlan.IonescuWainger
