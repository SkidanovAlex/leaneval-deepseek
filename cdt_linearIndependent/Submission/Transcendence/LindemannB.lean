import Submission.Transcendence.LindemannLW
import Submission.Commons.Algebra.BigOperators.prod_sum_choice

/-!
# Lindemann–Weierstrass: Lemma B (integer coefficients, distinct algebraic exponents)

This module carries out **Step 2 of the §11 roadmap** (see
`Lindemann.lean` §11 and the status block in `LindemannLW.lean`): the
passage from **Lemma A** (`lemmaA_orbit_contradiction`, completed in
`LindemannLW.lean` §§11–16 — no nonzero integer coefficients constant on
`conjRoots`-classes can satisfy an exponential orbit relation) to
**Lemma B** — *if `γ₁,…,γₙ` are distinct algebraic numbers and
`b₁,…,bₙ ∈ ℤ` are not all zero then `Σₖ bₖ·e^{γₖ} ≠ 0`* — and from Lemma B
to Lindemann's theorem (`cexp z` transcendental for algebraic `z ≠ 0`) and
its corollaries (`Transcendental ℚ (log q)`, `Transcendental ℚ π`, the
`m = n` corner of Theorem C of CDT).

**Completed in this module so far — the engine bridge.**  Lemma A is
stated over `Fin n`-indexed *cleared* families
(`lemmaA_orbit_contradiction`: the family `ℓ₀αₖ` is conj-closed, has
nonzero integer coefficients constant on the cleared `conjRoots`-classes,
and `Σₖ βₖ·e^{αₖ} = 0`).  Lemma B's symmetrization produces instead a
finite *set of exponent values* `S ⊆ ℂ` with an integer coefficient
function `D` on it.  The engine lemma `lemmaA_grouped` closes that gap:
*on a finite conj-closed set of algebraic values with nonzero integer
coefficients constant on each conjugacy class, the exponential relation
`Σ_{v∈S} (D v)·e^v = 0` is impossible*.  Its proof clears the whole set by
one `ℓ₀` (`exists_clearing_finset`, the Finset analogue of
`LindemannLW.exists_clearing_fin`), transfers conj-closure and
class-constancy from the uncleared classes to the cleared ones via
`conjRoots_smul_nat_subset` (conjugates of `ℓ·z` are `ℓ` times conjugates
of `z`; the underlying general fact is delegated to the Commons as
`Commons.FieldTheory.Minpoly.ConjRoots.conjRoots_smul_nat_subset`),
enumerates `S` by `Fin S.card`, and invokes `lemmaA_orbit_contradiction`.


**Completed in this module so far (all proved, zero `sorry`).**

* The **engine bridge**: `exists_clearing_finset` (clear a whole finite set
  by one `ℓ₀`), `conjRoots_smul_nat_subset` (conjugates of `ℓ·z` are `ℓ`
  times conjugates of `z`, proved here via `Polynomial.scaleRoots`), and
  `lemmaA_grouped` — the Finset-form of Lemma A: a finite conj-closed set
  `S` of algebraic values with nonzero integer coefficients constant on
  each `conjRoots`-class cannot satisfy `Σ_{v∈S} (D v)·e^v = 0`.  (Proved
  by clearing `S`, transferring conj-closure/class-constancy through
  `conjRoots_smul_nat_subset`, enumerating `S` via `Finset.equivFin`, and
  invoking `lemmaA_orbit_contradiction`.)
* **§17.1 (symmetrization data)**: `ChoiceFun N = Equiv.Perm (Fin N) → Fin N`
  (choice functions), `chCoeff b k = ∏_σ b (k σ)` and
  `chVal γ k = Σ_σ γ (σ (k σ))`; `cexp_sum` (product of exponentials is the
  exponential of the sum); the expansion identity `ch_expand`
  (`∏_σ (Σ_j b_j·e^{γ_{σ j}}) = Σ_k (chCoeff b k)·e^{chVal γ k}`, via the
  Commons `prod_sum_choice`); `ch_relation_zero`: under
  `Σ_j b_j·e^{γ_j} = 0` (the `σ = 1` factor of the product vanishes) the
  whole choice-sum is zero.
* **§17.2 (grouping)**: `chValues γ` (finite set of values) and
  `chGrouped γ b v` (fiber-sum coefficient); `ch_grouped_sum` regroups the
  choice-sum into `Σ_{v ∈ chValues γ} (chGrouped γ b v)·e^v`.

**Status:** §17.3b–§17.8 (conjugacy closure & class constancy, the
lexicographic nonzero coefficient, `lemmaB_conjClosed`, the conj-closed
extension, Lemma B proper, Lindemann's theorem and the corollaries) are
**completed in `Submission.Transcendence.LindemannC`** (import this module).
The roadmap below is kept as documentation of the classical argument.

**Original roadmap (§§17.3–17.5, in order).**  (1) Drop zero
coefficients: `S := {v ∈ chValues γ | chGrouped γ b v ≠ 0}` and re-derive
the relation on `S`.  (2) *Conjugacy closure & class constancy of the
grouped coefficients*: for `v = Σᵢ cᵢγᵢ ∈ chValues` and `u ∈ conjRoots v`,
an embedding of `ℚ(v)` extends to the (normal, since conj-closed) field
`ℚ(γ₁,…,γ_N)` and sends each `γᵢ` to `γ_{π i}`, so
`u = Σᵢ cᵢ γ_{π i} = chVal γ (k∘L_{π⁻¹})` for every choice `k` realizing
`v`; the map `k ↦ k∘L_{π⁻¹}` (precomposition with left-multiplication by
`π⁻¹` on the permutation group — a bijection on `ChoiceFun N`) preserves
`chCoeff` (product over the whole group is invariant under relabeling), so
the grouped coefficient is constant on the class.  (3) *Nonzero grouped
coefficient*: lexicographic (real-part then imaginary-part) argument —
choose `k*` with `b (k*) ≠ 0`; in every factor `σ` the available exponent
values `{γ_{σ k} : b k ≠ 0}` are the same set, whose lex-maximum is
attained at the same underlying index; the simultaneous max choice has a
unique value `w* = Σ_σ (lex-max)`, so `chGrouped γ b w* ≠ 0` and `S ≠ ∅`.
Then `lemmaA_grouped` on `(S, chGrouped γ b)` contradicts the relation —
**Lemma B for conj-closed families**; a separate extension argument
(union of the `conjRoots`-classes of the given distinct algebraic
exponents, indexed by `Fin N`, coefficients extended by zero) removes the
conj-closed hypothesis; and Step 0 gives Lindemann's theorem
(`Transcendental ℚ (cexp z)` for algebraic `z ≠ 0`) with the corollaries
(`Transcendental ℚ (log q)`, `Transcendental ℚ π`, `Irrational
(log(1+1/m)²)` — the `m = n` corner of CDT Theorem C).

**Roadmap for Lemma B (what remains, all classical; source: Wikipedia
"Lindemann–Weierstrass theorem", Lemma B).**  From a relation
`Σₖ bₖ·e^{γₖ} = 0` on distinct algebraic exponents:

1. *Symmetrization data.*  Extend `{γₖ}` to the full set of distinct roots
   of an integer polynomial vanishing on it (equivalently: work with a
   conj-closed injective algebraic family `γ : Fin N → ℂ` containing the
   original, extending `b` by zero — the zero extension preserves the
   relation).  For the permutation group `G := Equiv.Perm (Fin N)` and
   choice functions `k : G → Fin N` define the value
   `val k := Σ_σ γ_{σ (k σ)}` and coefficient `coeff k := ∏_σ b (k σ)`.
   The expansion identity `∏_σ (Σ_j b_j·e^{γ_{σ j}}) =
   Σ_k coeff(k)·cexp(val k)` is a product-of-sums distributivity
   (`Commons.Algebra.BigOperators.prod_sum_choice`); the left side is `0`
   because the `σ = id` factor is the assumed relation.
2. *Grouping.*  Grouping terms with equal values gives the finite set
   `S := {val k | k}` of values with `D(v) := Σ_{k : val k = v} coeff k`,
   and `Σ_{v∈S} (D v)·e^v = 0`.  Drop the zero-coefficient values
   (`S' := {v ∈ S | D v ≠ 0}`) — the engine `lemmaA_grouped` then applies
   once `S'` is conj-closed, class-constant and nonempty.
3. *Conjugacy closure and class constancy.*  For `w = Σᵢ cᵢγᵢ ∈ S'`
   (`c` its count vector) and a conjugate `u ∈ conjRoots w`: `u = σ(w)`
   for an embedding of `ℚ(w)`, extended to the normal field
   `L = ℚ(γ₁,…,γ_N)` (normal because the `γ`-family is conj-closed, i.e.
   contains all conjugates of each of its members); `σ(γᵢ)` is a conjugate
   of `γᵢ`, hence `γ_{π(i)}` for a permutation `π` (family conj-closed),
   so `u = Σⱼ c_{π⁻¹ j}·γⱼ` — a permuted-count value; and the
   *coefficient symmetry* `Σ_{k : val k = w} coeff k =
   Σ_{k' : val k' = u} coeff k'` follows because precomposing a choice
   function with left-multiplication by `π⁻¹` is a bijection between the
   two sets preserving the product `∏_σ b (k σ)` (the product over the
   whole group is invariant under relabeling).
4. *Nonzero coefficient.*  Pick `k*` with `b_{k*} ≠ 0` (some coefficient
   is nonzero) and equip `ℂ` with the lexicographic order (compare real
   then imaginary parts — a strict total order additive-compatible with
   finite sums).  In each factor `σ` choose the term with nonzero
   coefficient of maximal exponent `γ_{σ k}`; the simultaneous choice is
   possible since every factor offers the same available values, and its
   value `w*` is the strict maximum, with the unique realizing choice
   function, so `D(w*) = ∏_σ b_{k(σ)} ≠ 0` — in particular `S' ≠ ∅`.
5. *Apply the engine.*  `lemmaA_grouped` on `(S', D)` contradicts the
   assumed relation — Lemma B.

**Step 3 (Lindemann's theorem and corollaries) — roadmap.**  If `z ≠ 0`
is algebraic and `β := cexp z` algebraic with minimal polynomial of degree
`d + 1`, the coefficients `bⱼ` of the ℤ-cleared minimal polynomial give the
relation `Σⱼ bⱼ·e^{jz} = 0` over the *distinct* algebraic exponents
`{0, z, …, d·z}` — Lemma B.  Hence `Transcendental ℚ (cexp z)`, then
`Transcendental ℚ (log q)` (`q ∈ ℚ∖{0,1}`, via `cexp(log q) = q`),
`Transcendental ℚ π` (via `cexp(iπ) = −1`) and the `m = n` corner
`Irrational (log(1+1/m)²)` of CDT Theorem C
(`Helpers.log_one_add_inv_int_ne_zero` plus transcendence of the log).
-/

open scoped BigOperators
open scoped Complex
open Polynomial
set_option maxHeartbeats 800000
noncomputable section

namespace Submission.Transcendence

lemma exists_clearing_finset (S : Finset ℂ) (hS : ∀ v ∈ S, IsAlgebraic ℚ v) :
    ∃ ℓ₀ : ℕ, ℓ₀ ≠ 0 ∧ ∀ v ∈ S, IsIntegral ℤ ((ℓ₀ : ℂ) * v) := by
  classical
  let ds : ℂ → ℕ := fun v => Algebra.natDenominator v
  let ℓ₀ : ℕ := ∏ v ∈ S, ds v
  have hd0 : ∀ v ∈ S, ds v ≠ 0 := by
    intro v hv
    have hz : IsAlgebraic ℤ v :=
      (IsFractionRing.isAlgebraic_iff (A := ℤ) (K := ℚ) (C := ℂ)).mpr (hS v hv)
    exact IsAlgebraic.natDenominator_ne_zero hz
  refine ⟨ℓ₀, ?_, ?_⟩
  · -- ℓ₀ ≠ 0
    apply Finset.prod_ne_zero_iff.mpr
    intro v hv
    exact hd0 v hv
  · intro v hv
    have hdv : IsIntegral ℤ (ds v • v) := Algebra.isIntegral_natDenominator_smul v
    have hfac : ℓ₀ = ds v * (∏ u ∈ S.erase v, ds u) := by
      have h := Finset.prod_erase_mul S ds hv
      dsimp [ℓ₀]
      rw [← h, mul_comm]
    have hℓeq : (ℓ₀ : ℂ) * v = (∏ u ∈ S.erase v, ds u) • (ds v • v) := by
      rw [hfac]
      simp [nsmul_eq_mul, Nat.cast_mul, Nat.cast_prod, mul_assoc, mul_comm]
    rw [hℓeq]
    exact IsIntegral.nsmul hdv (∏ u ∈ S.erase v, ds u)

lemma conjRoots_smul_nat_subset {z w : ℂ} (ℓ : ℕ) (hℓ : ℓ ≠ 0) (hz : IsAlgebraic ℚ z)
    (hw : w ∈ conjRoots ((ℓ : ℂ) * z)) : ∃ u : ℂ, u ∈ conjRoots z ∧ w = (ℓ : ℂ) * u := by
  classical
  let m : ℚ[X] := minpoly ℚ z
  let h : ℚ[X] := Polynomial.scaleRoots m (ℓ : ℚ)
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ
  have hq0 : (ℓ : ℚ) ≠ 0 := by exact_mod_cast hℓ
  have hmz : aeval z m = 0 := by
    dsimp [m]
    exact minpoly.aeval ℚ z
  -- h vanishes at ℓ•z
  have hsr : Polynomial.eval₂ (algebraMap ℚ ℂ) ((ℓ : ℂ) * z) (Polynomial.scaleRoots m (ℓ : ℚ)) = 0 := by
    change Polynomial.eval₂ (algebraMap ℚ ℂ)
      ((algebraMap ℚ ℂ (ℓ : ℚ)) * z) (Polynomial.scaleRoots m (ℓ : ℚ)) = 0
    rw [Polynomial.scaleRoots_eval₂_mul (f := algebraMap ℚ ℂ) (r := z) (s := (ℓ : ℚ)) (p := m)]
    have hz2 : Polynomial.eval₂ (algebraMap ℚ ℂ) z m = 0 := by
      rw [← Polynomial.aeval_def]
      exact hmz
    simp [hz2]
  have hhh : aeval ((ℓ : ℂ) * z) h = 0 := by
    dsimp [h]
    rw [Polynomial.aeval_def]
    exact hsr
  have hmdvd : minpoly ℚ ((ℓ : ℂ) * z) ∣ h := minpoly.dvd ℚ ((ℓ : ℂ) * z) (by simpa [h] using hhh)
  have haw : aeval w (minpoly ℚ ((ℓ : ℂ) * z)) = 0 := aeval_mem_conjRoots hw
  have hah : aeval w h = 0 := by
    obtain ⟨g, hg⟩ := hmdvd
    rw [hg, Polynomial.aeval_mul]
    simp [haw]
  -- evaluation at w: ℓ^d • aeval (w/ℓ) m = 0
  have hs2 := Polynomial.scaleRoots_eval₂_mul (f := algebraMap ℚ ℂ)
    (r := w / (ℓ : ℂ)) (s := (ℓ : ℚ)) (p := m)
  have hmm : aeval (w / (ℓ : ℂ)) m = 0 := by
    dsimp [h] at hah
    rw [Polynomial.aeval_def] at hah
    -- hah : eval₂ f w (m.scaleRoots (ℓ:ℚ)) = 0
    have hseq : (algebraMap ℚ ℂ (ℓ : ℚ)) * (w / (ℓ : ℂ)) = w := by
      have hc : (algebraMap ℚ ℂ (ℓ : ℚ)) = (ℓ : ℂ) := by norm_num
      rw [hc]
      field_simp [hℓc]
    have hmul : (algebraMap ℚ ℂ (ℓ : ℚ)) ^ m.natDegree *
        Polynomial.eval₂ (algebraMap ℚ ℂ) (w / (ℓ : ℂ)) m = 0 := by
      rw [← hs2, hseq]
      exact hah
    have hfac : (algebraMap ℚ ℂ (ℓ : ℚ)) ^ m.natDegree ≠ 0 := by
      exact pow_ne_zero _ ((_root_.map_ne_zero (algebraMap ℚ ℂ)).mpr hq0)
    have hz2 : Polynomial.eval₂ (algebraMap ℚ ℂ) (w / (ℓ : ℂ)) m = 0 :=
      (mul_eq_zero.mp hmul).resolve_left hfac
    exact (Polynomial.aeval_def (w / (ℓ : ℂ)) m).symm.trans hz2
  refine ⟨w / (ℓ : ℂ), ?_, ?_⟩
  · exact conjRoots_of_aeval hz (by simpa [m] using hmm)
  · field_simp [hℓc]


/-- The Finset-form of Lemma A (the engine consumed by Lemma B): a finite
family of exponent *values* `S ⊆ ℂ`, each algebraic, carrying a nonzero
integer coefficient `D v`, closed under `ℚ`-conjugacy (every conjugate of a
member lies in `S`) with the coefficient constant on each conjugacy class,
cannot satisfy `Σ_{v∈S} (D v)·e^v = 0`.  -/
lemma lemmaA_grouped (S : Finset ℂ) (D : ℂ → ℤ)
    (hSne : S.Nonempty)
    (hSnz : ∀ v ∈ S, D v ≠ 0)
    (hSalg : ∀ v ∈ S, IsAlgebraic ℚ v)
    (hconj : ∀ v ∈ S, ∀ w : ℂ, w ∈ conjRoots v → w ∈ S)
    (hcls : ∀ v ∈ S, ∀ w ∈ S, w ∈ conjRoots v → D w = D v)
    (hrel : (∑ v ∈ S, (D v : ℂ) * cexp v) = 0) : False := by
  classical
  obtain ⟨ℓ₀, hℓ0, hbS⟩ := exists_clearing_finset S hSalg
  have hℓc : (ℓ₀ : ℂ) ≠ 0 := by exact_mod_cast hℓ0
  let eS : S ≃ Fin S.card := Finset.equivFin S
  let α : Fin S.card → ℂ := fun i => ((eS.symm i) : ℂ)
  let β : Fin S.card → ℤ := fun i => D (α i)
  have hmem : ∀ i : Fin S.card, α i ∈ S := by
    intro i
    dsimp [α]
    exact (eS.symm i).2
  have hne0 : 0 < S.card := Finset.card_pos.mpr hSne
  refine lemmaA_orbit_contradiction hne0 α ℓ₀ hℓ0 ?hb β ?βnz ?hinj ?hclosed ?hβc ?hrel'
  · -- hb
    intro i
    exact hbS (α i) (hmem i)
  · -- β nonzero
    intro i
    exact hSnz (α i) (hmem i)
  · -- hinj (cleared injective)
    intro i j hij
    have hα : α i = α j := (mul_left_cancel₀ hℓc hij)
    dsimp [α] at hα
    apply (eS.symm).injective
    exact Subtype.ext hα
  · -- hclosed : conjClosedFamily (fun i => (ℓ₀ : ℂ) * α i)
    intro i w hw
    obtain ⟨u, hu, hwu⟩ := conjRoots_smul_nat_subset ℓ₀ hℓ0 (hSalg (α i) (hmem i)) hw
    have huS : u ∈ S := hconj (α i) (hmem i) u hu
    refine ⟨eS ⟨u, huS⟩, ?_⟩
    dsimp [α]
    have hback : (eS.symm (eS ⟨u, huS⟩)) = (⟨u, huS⟩ : S) := eS.symm_apply_apply ⟨u, huS⟩
    rw [hback]
    exact hwu.symm
  · -- hβc : coefficients constant on cleared conjRoots classes
    intro k t hkt
    obtain ⟨u, hu, hku⟩ := conjRoots_smul_nat_subset ℓ₀ hℓ0 (hSalg (α k) (hmem k)) hkt
    -- hku : (ℓ₀:ℂ)*α t = (ℓ₀:ℂ)*u
    have hα : α t = u := (mul_left_cancel₀ hℓc hku)
    have hαc : α t ∈ conjRoots (α k) := by
      rw [hα]
      exact hu
    have hD : D (α t) = D (α k) := hcls (α k) (hmem k) (α t) (hmem t) hαc
    dsimp [β]
    exact hD.symm
  · -- hrel' : the relation over the Fin-indexed family equals the one over S
    have hsum : (∑ i : Fin S.card, (β i : ℂ) * cexp (α i)) =
        (∑ v ∈ S, (D v : ℂ) * cexp v) := by
      refine Finset.sum_bij (s := (Finset.univ : Finset (Fin S.card))) (t := S)
        (f := fun i : Fin S.card => (β i : ℂ) * cexp (α i))
        (g := fun v : ℂ => (D v : ℂ) * cexp v)
        (fun i hi => α i) ?hi ?iinj ?isurj ?hval
      · -- hi
        exact fun i hi => hmem i
      · -- iinj
        intro i hi j hj hij
        dsimp [α] at hij
        apply (eS.symm).injective
        exact Subtype.ext hij
      · -- isurj
        intro v hv
        refine ⟨eS ⟨v, hv⟩, Finset.mem_univ _, ?_⟩
        dsimp [α]
        rw [eS.symm_apply_apply]
      · -- hval
        intro i hi
        dsimp [β]
    rw [hsum]
    exact hrel

/-! ## 17.1  The symmetrization data (`S_N`-expansion over choice functions)

For a finite exponent family `γ : Fin N → ℂ` and integer coefficients
`b : Fin N → ℤ`, `G = Equiv.Perm (Fin N)` is the permutation group and a
*choice function* `k : G → Fin N` picks, for each factor `σ`, the index of
the term taken from the linear factor `Σ_j b_j·x_{σ j}` of the symmetric
product `∏_σ (Σ_j b_j·x_{σ j})`.  Evaluating at `x_i = e^{γ_i}`:

* `chCoeff b k = ∏_σ b (k σ)` — the integer coefficient of the term;
* `chVal γ k = Σ_σ γ_{σ (k σ)}` — the exponent value of the term.

The expansion identity `ch_expand` (a product-of-sums distributivity,
`Commons.Algebra.BigOperators.prod_sum_choice`) makes the vanishing of the
product (one factor is the assumed relation) into the vanishing of the sum
over all choices (`ch_relation_zero`). -/

/-- `cexp` of a finite sum is the product of the exponentials. -/
lemma cexp_sum {ι : Type*} (s : Finset ι) (a : ι → ℂ) :
    (∏ i ∈ s, cexp (a i)) = cexp (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s his ih =>
      simp [his, ih, Complex.exp_add]

/-- Choice functions: to each permutation `σ` of the exponent indices, a
chosen summation index `k σ`. -/
abbrev ChoiceFun (N : ℕ) := Equiv.Perm (Fin N) → Fin N

/-- Integer coefficient contributed by a choice: `∏_σ b (k σ)`. -/
def chCoeff {N : ℕ} (b : Fin N → ℤ) (k : ChoiceFun N) : ℤ :=
  ∏ σ : Equiv.Perm (Fin N), b (k σ)

/-- Exponent value contributed by a choice: `Σ_σ γ (σ (k σ))`. -/
def chVal {N : ℕ} (γ : Fin N → ℂ) (k : ChoiceFun N) : ℂ :=
  ∑ σ : Equiv.Perm (Fin N), γ (σ (k σ))

/-- Per-term identity of the expansion: the term contributed by the choice
`k` to the expanded product equals `chCoeff b k · cexp (chVal γ k)`. -/
lemma ch_term {N : ℕ} (γ : Fin N → ℂ) (b : Fin N → ℤ) (k : ChoiceFun N) :
    (∏ σ : Equiv.Perm (Fin N), (b (k σ) : ℂ) * cexp (γ (σ (k σ)))) =
      (chCoeff b k : ℂ) * cexp (chVal γ k) := by
  classical
  rw [Finset.prod_mul_distrib]
  congr 1
  · dsimp [chCoeff]
    rw [Int.cast_prod]
  · dsimp [chVal]
    exact cexp_sum (Finset.univ : Finset (Equiv.Perm (Fin N))) (fun σ => γ (σ (k σ)))

/-- The expansion of the symmetric product `∏_σ (Σ_j b_j·e^{γ_{σ j}})` over
the terms of the factors. -/
lemma ch_expand {N : ℕ} (γ : Fin N → ℂ) (b : Fin N → ℤ) :
    (∏ σ : Equiv.Perm (Fin N), ∑ j : Fin N, (b j : ℂ) * cexp (γ (σ j))) =
      ∑ k : ChoiceFun N, (chCoeff b k : ℂ) * cexp (chVal γ k) := by
  classical
  rw [Commons.Algebra.BigOperators.prod_sum_choice (ι := Equiv.Perm (Fin N))
    (κ := Fin N) (R := ℂ) (x := fun σ j => (b j : ℂ) * cexp (γ (σ j)))]
  apply Finset.sum_congr
  · ext x
    simp
  · intro k hk
    exact ch_term γ b k
/-- Under the relation `Σ_j b_j·e^{γ_j} = 0` (the `σ = 1` factor vanishes),
the whole symmetric sum is zero. -/
lemma ch_relation_zero {N : ℕ} (γ : Fin N → ℂ) (b : Fin N → ℤ)
    (hrel : (∑ j : Fin N, (b j : ℂ) * cexp (γ j)) = 0) :
    (∑ k : ChoiceFun N, (chCoeff b k : ℂ) * cexp (chVal γ k)) = 0 := by
  classical
  rw [← ch_expand γ b]
  -- the product has a zero factor at σ = 1 (the identity permutation)
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : Equiv.Perm (Fin N)))
  simpa using hrel

/-! ## 17.2  Grouping the expansion by equal exponent values

`chValues γ` is the (finite) set of exponent values that occur, and
`chGrouped γ b v` is the sum of the coefficients of all choices producing
the value `v`.  `ch_grouped_sum` regroups `ch_relation_zero` into the
relation `Σ_{v ∈ chValues γ} (chGrouped γ b v)·e^v = 0` over *distinct*
values. -/

/-- The finite set of exponent values produced by the expansion. -/
def chValues {N : ℕ} (γ : Fin N → ℂ) : Finset ℂ :=
  (Finset.univ : Finset (ChoiceFun N)).image (chVal γ)

/-- The grouped integer coefficient of an exponent value. -/
def chGrouped {N : ℕ} (γ : Fin N → ℂ) (b : Fin N → ℤ) (v : ℂ) : ℤ :=
  ∑ k ∈ (Finset.univ : Finset (ChoiceFun N)).filter (fun k => chVal γ k = v), chCoeff b k

/-- Regrouping the sum over all choices by the distinct exponent values. -/
lemma ch_grouped_sum {N : ℕ} (γ : Fin N → ℂ) (b : Fin N → ℤ) :
    (∑ v ∈ chValues γ, (chGrouped γ b v : ℂ) * cexp v) =
      ∑ k : ChoiceFun N, (chCoeff b k : ℂ) * cexp (chVal γ k) := by
  classical
  refine Finset.sum_image' (s := (Finset.univ : Finset (ChoiceFun N))) (g := chVal γ)
    (f := fun v : ℂ => (chGrouped γ b v : ℂ) * cexp v)
    (h := fun k : ChoiceFun N => (chCoeff b k : ℂ) * cexp (chVal γ k)) ?eq
  · -- eq : ∀ i ∈ s, f (g i) = ∑ j ∈ s with g j = g i, h j
    intro i hi
    have hfib : (∑ j ∈ (Finset.univ : Finset (ChoiceFun N)) with chVal γ j = chVal γ i,
          (chCoeff b j : ℂ) * cexp (chVal γ j))
        = (chGrouped γ b (chVal γ i) : ℂ) * cexp (chVal γ i) := by
      calc
        (∑ j ∈ (Finset.univ : Finset (ChoiceFun N)) with chVal γ j = chVal γ i,
            (chCoeff b j : ℂ) * cexp (chVal γ j))
            = (∑ j ∈ (Finset.univ : Finset (ChoiceFun N)) with chVal γ j = chVal γ i,
            (chCoeff b j : ℂ) * cexp (chVal γ i)) := by
              apply Finset.sum_congr rfl
              intro j hj
              rw [(Finset.mem_filter.mp hj).2]
        _ = (chGrouped γ b (chVal γ i) : ℂ) * cexp (chVal γ i) := by
              rw [← Finset.sum_mul]
              congr 1
              dsimp [chGrouped]
              rw [← Int.cast_sum]
    exact hfib.symm

/-- The grouped relation over *all* values is zero under the base relation. -/
lemma ch_grouped_relation_zero {N : ℕ} (γ : Fin N → ℂ) (b : Fin N → ℤ)
    (hrel : (∑ j : Fin N, (b j : ℂ) * cexp (γ j)) = 0) :
    (∑ v ∈ chValues γ, (chGrouped γ b v : ℂ) * cexp v) = 0 := by
  rw [ch_grouped_sum]
  exact ch_relation_zero γ b hrel

/-- The values with nonzero grouped coefficient. -/
def chSupport {N : ℕ} (γ : Fin N → ℂ) (b : Fin N → ℤ) : Finset ℂ :=
  (chValues γ).filter (fun v => chGrouped γ b v ≠ 0)

/-- Dropping the zero-coefficient values does not change the relation. -/
lemma ch_support_relation_zero {N : ℕ} (γ : Fin N → ℂ) (b : Fin N → ℤ)
    (hrel : (∑ j : Fin N, (b j : ℂ) * cexp (γ j)) = 0) :
    (∑ v ∈ chSupport γ b, (chGrouped γ b v : ℂ) * cexp v) = 0 := by
  classical
  have hfull : (∑ v ∈ chValues γ, (chGrouped γ b v : ℂ) * cexp v) = 0 :=
    ch_grouped_relation_zero γ b hrel
  rw [← hfull]
  refine Finset.sum_subset ?sub ?zero
  · intro v hv
    dsimp [chSupport] at hv
    exact (Finset.mem_filter.mp hv).1
  · intro x hx hxs
    dsimp [chSupport] at hxs
    have hD : chGrouped γ b x = 0 := by
      by_contra h
      exact hxs (Finset.mem_filter.mpr ⟨hx, h⟩)
    simp [hD]

end Submission.Transcendence
