import Submission.Cwnorm
import Submission.CoverLemma
import Submission.GeneralDual
import Submission.RemezComplex
import Submission.WnormToolkit
import Submission.Contracts
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Polynomial
import Mathlib.Tactic

/-!
# `thm:adjust` + `cor:adjust` for the Serre data (root-data form)

This is the formalization of Smith GON.tex `thm:adjust` (flatness/covering
statement) together with the `cor:adjust` norm bound, specialised to our
contracts.  The theorem says: given a squarefree-like integer polynomial `Q`
of degree `n ≥ 2` WITH root data (`α : Fin n → ℂ` injective and the
factorization), for every REAL polynomial `P` of degree `≤ n−1` there is an
INTEGER polynomial `R` of degree `≤ n−1` and complex coefficients
`β : Fin n → ℂ` such that

    P (complexified) − R (complexified)  =  ∑ i, β i • q_i          (q_i := Qc /ₘ (X − C (α i)))
    ∑ i ‖β i‖ ≤ n^C
    wnorm n (P − zmap R) ≤ n^C · wnorm n (zmap Q)

where `wnorm` is `Submission.Contracts.wnorm` (weighted sup-norm over the
Serre interval at exponent n) and `zmap R = R.map (algebraMap ℤ ℝ)`.

## Why this is the right statement

- `AdjustContract` (Submission.Contracts) is exactly the last clause, with
  `Squarefree Q` + `natDegree = n` hypotheses (produce root data via
  `Submission.SqSep.squarefree_separable` + `Submission.RootData.root_data_of_separable`).
- `lem:second_squeeze` (next step) needs the identity + ℓ₁ bound with
  `P = ½ X^j` (`j < m`): then `H_j := X^j − 2R` is an integer polynomial
  (it equals `2·∑ β_i q_i` complexified), `H_j ≡ X^j (mod 2)`, and
  `‖H_j·G‖_n ≤ 2·(∑|β_i|)·(2n)^C·‖Q·G‖_n` by `RemezComplex` division.

## Definitions available (import these Submission modules)

- `Submission.GeneralDual` (which imports MonicDual, PartAFound, ValIntegral,
  CoeffIntegral): 
  * `Submission.MonicDual.qic (α : Fin n → ℂ) (i : Fin n) : Polynomial ℂ :=
    ∏ k ∈ univ.erase i, (X − C (α k))`
  * `Submission.MonicDual.Qc (Q) := Q.map (algebraMap ℤ ℂ)`
  * `Submission.MonicDual.cval (α) (d : Fin n → ℤ) (i : Fin n) : ℂ :=
    ∑ j, (d j : ℂ) · (qic α i).coeff j.val`
  * `Submission.GeneralDual.cvalc Q α d i := ∑ j, (d j : ℂ) · ((Q.leadingCoeff : ℂ) · (qic α i).coeff j.val)`
  * `Submission.GeneralDual.qic_lead_eq_divByMonic`: with `hfac`,
    `C(Q.leadingCoeff:ℂ) * qic α i = Qc Q /ₘ (X − C (α i))`
  * THEOREM `Submission.GeneralDual.general_dual {n} (hn : 1 ≤ n) (Q) (hQ0) (hQn)
    (α) (hαinj) (hfac) (d : Fin n → ℤ) (hd : d ≠ 0) :
    ∃ i, 1 ≤ ‖∑ j, (d j : ℂ) * ((Q.leadingCoeff : ℂ) * (qic α i).coeff (j.val))‖`
    i.e. `∃ i, 1 ≤ ‖cvalc Q α d i‖`.
- `Submission.CoverLemma.covering_of_dual (hn : 1 ≤ n) (B : Matrix (Fin n) (Fin n) ℝ)
  (hdet : B.det ≠ 0) (hdual : DualCondition B) :
  ∃ C : ℝ, 0 < C ∧ ∀ p : Fin n → ℝ, ∃ (r : Fin n → ℤ) (β : Fin n → ℝ),
    (∀ j, (∑ i, β i * B i j) = p j − (r j : ℝ)) ∧ (∑ i, |β i|) ≤ (n : ℝ)^C`
  where `DualCondition B := ∀ d : Fin n → ℤ, d ≠ 0 → ∃ i, 1 ≤ |∑ j, B i j * (d j : ℝ)|`.
- `Submission.Cwnorm.cwnorm k P := sSup_{x ∈ Icc aSerre bSerre} w(x)^k · ‖P.eval (x:ℂ)‖`
  for `P : Polynomial ℂ`; `Submission.RemezComplex.complex_remez`:
  `∃ C > 0, ∀ N m ≥ 1, ∀ P : Polynomial ℂ, P.natDegree = m → ∀ α, P.eval α = 0 →
    ∃ Q, P = (X − C α) * Q ∧ cwnorm N Q ≤ ((2·max N m : ℕ):ℝ)^C · cwnorm N P`.
  Also `cwnorm_map_eq_wnorm`: `cwnorm k (P.map (algebraMap ℝ ℂ)) = wnorm k P`
  and `Submission.Contracts.wnorm`, `zmap`.

## FULL PROOF ROADMAP (follow or improve)

Fix the data: `n ≥ 2`, `Q ≠ 0`, `natDegree Q = n`, `α` injective, `hfac`; set
`Qc := Qc Q` (complexification), `c := Q.leadingCoeff` (note `c ≠ 0`), and
`q i := Qc /ₘ (X − C (α i))` (the quotients, degree `n−1`, and
`q i = C(c) · qic α i`).

### Step A — conjugation structure
ℂ-conjugation `conj : ℂ → ℂ` is a ring automorphism fixing every real
coefficient of `Qc` (coefficients of `Qc` are real: they are images of ℤ).
Establish:
  A1. `Qc.eval (conj (α i)) = conj (Qc.eval (α i))` (coefficient-wise
      conjugation is a ring hom extending `conj` on ℂ; the polynomial is
      `eval₂ (RingHom.comp ... )` — take care: `Qc` has REAL coefficients so
      evaluation commutes with `conj`).
  A2. `Qc.eval (α i) = 0` (from `hfac`; product factor vanishes).
  A3. Hence `conj (α i)` is a root of `Qc`, and since
      `Qc = C(c)·∏ₖ (X − C (α k))` with `c ≠ 0`, conclude
      `∃ k, conj (α i) = α k` (field: product zero ⟹ some factor zero).
  A4. Define (classically) `σ i := Classical.choose` of that `k`.  You get
      `conj (α i) = α (σ i)`, and `σ (σ i) = i` follows by applying `conj`
      to `conj (α i) = α (σ i)` and using injectivity of `α` together with
      `conj (conj z) = z`.
  A5. `Qc` has real coefficients ⟹ for the quotient `q i`:
      `conjPoly (q i) = q (σ i)` where `conjPoly` is coefficient-wise
      conjugation: from the defining relation
      `Qc = (X − C (α i))·(q i)` apply conjugation to get
      `Qc = (X − C (α (σ i)))·conjPoly(q i)` and use uniqueness of division
      by the monic `X − C (α (σ i))`.  (You may use `divByMonic` API:
      `Polynomial.divByMonic_eq_of_dvd`-type lemmas, or
      `Polynomial.modByMonic_eq_zero_of_dvd`.)
  A6. Coefficient-wise: `(q (σ i)).coeff j = conj ((q i).coeff j)` (so with
      `d : Fin n → ℤ` real: `∑ j (d j)·(q (σ i)).coeff j = conj (∑ j (d j)·(q i).coeff j)`).

### Step B — the real rows
We need `n` REAL polynomials of degree `≤ n−1` whose coefficient matrix is
invertible (an ℝ-basis of the real polynomials of degree `< n`) and satisfies
the real dual condition.  Index them by a fresh finite type of cardinality n:

    RealRoot i := (α i : ℂ) = conj (α i)                     -- i.e. α i real
    R := {i : Fin n // RealRoot i}                           -- real roots
    Cpair := {i : Fin n // ¬ RealRoot i ∧ 0 < (α i).im}      -- canonical rep per conj-pair
    Row := R ⊕ (Cpair × Fin 2)

`Fintype.card Row = n`: prove `2·#Cpair + #R = n` using `σ` from Step A
(`σ` bijects `Cpair`-complement to itself without fixed points etc.; every
non-real root belongs to exactly one pair `{i, σ i}`, and exactly one of
`α i, α (σ i)` has positive imaginary part).

Define row polynomials with REAL coefficients:
  * for `(Sum.inl r)`:  `row = q r`   (already real coefficients: root real)
  * for `(Sum.inr (c, 0))`: `row = (q c + q (σ c)) / √2`
  * for `(Sum.inr (c, 1))`: `row = i·(q c − q (σ c)) / √2`
(Here `/ √2` means scalar division by the real number `√2` in `Polynomial ℂ`;
`i` is the imaginary unit `Complex.I`.)  Show each has REAL coefficients:
coefficient-wise, `coeff_j(row) = conj (coeff_j(row))` using A5/A6 (for
`Sum.inr` rows note `q (σ (σ c)) = q c`).  Build the real polynomial
`Q°row : Row → Polynomial ℝ` with `(Q°row r).map (algebraMap ℝ ℂ) = row`
(e.g. define by `∑ j, Real.re (coeff_j(row))·X^j` and prove the equality via
coefficient-wise `ext`; or use `Polynomial.map_injective`-style facts — your
choice, but the exported objects must be REAL polynomials).

Make a Fintype for `Row`, fix an equivalence `e : Row ≃ Fin n`
(`Fintype.equivFin`-type content, from `Fintype.card Row = n`), and define
`Q° : Fin n → Polynomial ℝ`, `Q° i := Q°row (e.symm i)`,
`B : Matrix (Fin n) (Fin n) ℝ`, `B i j := (Q° i).coeff j.val`.

### Step C — B is invertible (det ≠ 0)
Show the complex polynomials `{row r : r ∈ Row}` are ℂ-linearly independent,
using that `{q i : i ∈ Fin n}` is a ℂ-basis of the degree-`<n` polynomials:
the change-of-basis matrix from the `q`-basis to the rows is block-diagonal
per conjugate pair with blocks
    [[1/√2, 1/√2], [i/√2, −i/√2]]    (and `[1]`-block for real roots)
which is invertible.  The `q`-basis fact: evaluate at the roots — the matrix
`(q i)(α k) = δᵢₖ·Qc'(α k)` (Kronecker) with `Qc'(α k) ≠ 0` (roots simple:
`Qc = C(c)·∏(X−C(αᵢ))` and `α` injective ⟹ `Qc' (α k) = c·∏_{i≠k}(α k − α i) ≠ 0`).
Conclude the `Row`-indexed rows are ℂ-independent; since each is real, they
are ℝ-independent; equivalently the coefficient matrix has `det ≠ 0`
(`Matrix.det_ne_zero_iff`-style or via the basis theory).  Transport through
`e` to get `B.det ≠ 0`.

### Step D — real dual condition for B
`DualCondition B`: given `d : Fin n → ℤ`, `d ≠ 0`, find a ROW whose dot with
`d` (over the coefficient degrees) is `≥ 1` in absolute value.
Apply `Submission.GeneralDual.general_dual` with the same `Q, α, hfac, d`:
get `i₀` with `1 ≤ ‖cvalc Q α d i₀‖` where
`cvalc Q α d i₀ = ∑ j (d j : ℂ)·coeff_j(q i₀)` (use
`qic_lead_eq_divByMonic` to identify `C(c)·qic α i₀ = q i₀`).  Now:
  * if `RealRoot i₀`: the row `Sum.inl i₀` is `q i₀`; its dot product with
    `d` is real and equals `cvalc` (or its real part), absolute value `≥ 1`;
  * else write `{i₀, σ i₀} = {c, σ c}` with `c : Cpair` (exactly one of the
    two is in `Cpair` — if `0 < (α i₀).im` use `i₀`, else use `σ i₀`).  Let
    `v := cvalc Q α d c`.  Then `cvalc Q α d (σ c) = conj v` (A6), so
    `‖v‖ ≥ 1`.  The two rows of pair `c` have dot products with `d` equal to
    `√2·Re(v)` and `−√2·Im(v)` (compute coefficient-wise from Step B and A6;
    possibly up to the sign of the imaginary row).  Since
    `max (|√2·Re v|) (|√2·Im v|) ≥ 1` whenever `Re v² + Im v² ≥ 1`
    (use `Complex.normSq`, `Complex.re/im`, `abs` bounds:
    `√2·max(|Re|,|Im|) ≥ √(Re² + Im²)` — an elementary inequality), one of
    these two rows works.
Transport back through `e` to get the `Fin n`-indexed row witness.  Conclude
`DualCondition B`.

### Step E — apply CoverLemma
Given `P` with `natDegree P ≤ n−1`, let `p : Fin n → ℝ`, `p j := P.coeff j.val`.
`CoverLemma.covering_of_dual` (with `hn : 1 ≤ n` from `2 ≤ n`) gives
`r : Fin n → ℤ`, `β : Fin n → ℝ`, `Σ|β i| ≤ n^C0` (the CoverLemma's own C),
and `∀ j, Σ i β i·B i j = p j − (r j : ℝ)`.
Let `R := ∑ j : Fin n, Polynomial.C ((r j : ℤ)) · X^j.val` (integer poly,
`natDegree ≤ n−1` — coefficients beyond `n−1` are 0; note the top coefficient
`j.val = n−1` is included; prove `R.natDegree ≤ n−1` via coefficient
vanishing or `natDegree_le_iff_coeff_eq_zero`-style lemmas).
From the coefficient identity conclude the REAL polynomial identity
`P − zmap R = ∑ i, β i • Q° i` in `ℝ[X]` (ext by coefficients).  Convert to
the complex quotient basis: using the explicit row construction (Step B),
`Q° i` (complexified) equals
  `q i`           (if its row is a real-root row), or
  a combination `((β₀+β₁)/√2)·q c + ...`-type; concretely build
  `βc : Fin n → ℂ` with
  (i) `P.map (algebraMap ℝ ℂ) − (zmap R).map (algebraMap ℝ ℂ)
       = ∑ i, βc i • q i`  (coefficient-wise in ℂ[X]), and
  (ii) `∑ i ‖βc i‖ ≤ 2 · ∑ i |β i|` (each real `β°` contributes to at most
       two `q`-coefficients, each of modulus `≤ (1/√2)·(|β₀|+|β₁|) ≤ |β₀|+|β₁|`).
  For the REAL-root rows the conversion is identity.  (If the sign of the
  imaginary row comes out `+√2 Im`, just absorb signs into `βc`.)
This `βc` is the exported `β : Fin n → ℂ` of the theorem.

### Step F — norm bound
`wnorm n (P − zmap R) = cwnorm n ((P−zmap R).map ℝ→ℂ)` via
`cwnorm_map_eq_wnorm`, and `(P−zmap R).map = ∑ i βc i • q i`.  Hence
`wnorm n (P − zmap R) ≤ ∑ i ‖βc i‖ · cwnorm n (q i)` (use the cwnorm
triangle/smul API in `Submission.Cwnorm`, e.g. `cwnorm_sum_le`,
`cwnorm_smul`).  For each `i`, `q i = Qc /ₘ (X − C(α i))` and
`Qc = (X − C(α i))·(q i)`, so `complex_remez` applied to `P' = Qc`
(`natDegree = n`, root `α i`) gives `cwnorm n (q i) ≤ ((2·n:ℕ):ℝ)^C · cwnorm n Qc`.
And `cwnorm n Qc = wnorm n (zmap Q)` (`cwnorm_map_eq_wnorm` — note
`Qc = (zmap Q).map (algebraMap ℝ ℂ)`).  Bound `∑|βc i|·(2n)^C` by
`n^{C′}`: choose the final exponent large enough to absorb `∑‖β i‖ ≤ n^{C0}`,
the `(2n)^C` factor, and the small conversion constant.  Assemble
`∃ Cadj > 0` with the three clauses and return it.  (Be careful to make the
final `C` INDEPENDENT of `n, Q, α, P` — a single `∃ C` at the top.)

## Final note
Axioms ⊆ {propext, Quot.sound, Classical.choice}; no placeholders, no `axiom`.
You may add private helper definitions/lemmas in this file and import any
PROVED `Submission.*` modules.  The theorem is `adjust_lemma` below.  This is
a LONG task (expected 1000+ lines); work carefully, build incrementally, and
keep intermediate lemmas placeholder-free as you go.
-/

noncomputable section
open scoped BigOperators
open Polynomial
open ComplexOrder

namespace Submission.AdjustLemma

open Submission.Contracts
open Submission.Cwnorm
open Submission.MonicDual
open Submission.GeneralDual
open Submission.CoverLemma

/-- The quotient `Qc /ₘ (X − C α)` (degree `n−1` when `Q` has degree `n` and
`α` is one of its roots). -/
noncomputable def qDiv (Q : Polynomial ℤ) (α : ℂ) : Polynomial ℂ :=
  Q.map (algebraMap ℤ ℂ) /ₘ (Polynomial.X - Polynomial.C α)

/-! ## Basic consequences of the root-data factorization -/

section Basic

variable {n : ℕ}

lemma lc_ne_zero (Q : Polynomial ℤ) (hQ0 : Q ≠ 0) : Q.leadingCoeff ≠ 0 := by
  exact Polynomial.leadingCoeff_ne_zero.mpr hQ0

lemma Qc_natDegree (Q : Polynomial ℤ) {n : ℕ} (hQn : Q.natDegree = n) :
    (Q.map (algebraMap ℤ ℂ)).natDegree = n := by
  rw [Polynomial.natDegree_map_eq_of_injective (f := algebraMap ℤ ℂ) Int.cast_injective Q, hQn]

lemma qDiv_eq_qic (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (i : Fin n) : qDiv Q (α i) = Polynomial.C ((Q.leadingCoeff : ℂ)) * qic α i := by
  exact (qic_lead_eq_divByMonic Q α hfac i).symm

lemma alpha_root (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (i : Fin n) : (Q.map (algebraMap ℤ ℂ)).eval (α i) = 0 := by
  have hprod : (∏ k : Fin n, (X - C (α k))).eval (α i) = 0 := by
    classical
    rw [Polynomial.eval_prod]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
  calc
    (Q.map (algebraMap ℤ ℂ)).eval (α i)
        = (Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ k : Fin n, (X - C (α k))).eval (α i) := by
            rw [hfac]
    _ = (Q.leadingCoeff : ℂ) * 0 := by rw [Polynomial.eval_mul, Polynomial.eval_C, hprod]
    _ = 0 := by ring

lemma qDiv_mul (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (i : Fin n) :
    Q.map (algebraMap ℤ ℂ) = (X - Polynomial.C (α i)) * qDiv Q (α i) := by
  classical
  calc
    Q.map (algebraMap ℤ ℂ) = Polynomial.C ((Q.leadingCoeff : ℂ)) *
        ∏ k : Fin n, (X - Polynomial.C (α k)) := hfac
    _ = Polynomial.C ((Q.leadingCoeff : ℂ)) *
        ((X - Polynomial.C (α i)) * qic α i) := by
          rw [prod_univ_eq_mul_erase (f := fun k : Fin n => (X - C (α k))) (i := i)]
          rfl
    _ = (X - Polynomial.C (α i)) * qDiv Q (α i) := by
          rw [qDiv_eq_qic Q α hfac i]
          ring

lemma qDiv_eval_ne (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    {i j : Fin n} (hij : j ≠ i) : (qDiv Q (α i)).eval (α j) = 0 := by
  classical
  rw [qDiv_eq_qic Q α hfac i]
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  have herase : j ∈ (Finset.univ.erase i) := by simp [hij]
  have h0 : (∏ k ∈ (Finset.univ.erase i), (α j - α k)) = 0 :=
    Finset.prod_eq_zero herase (by simp)
  calc
    (Q.leadingCoeff : ℂ) * (qic α i).eval (α j)
        = (Q.leadingCoeff : ℂ) * (∏ k ∈ (Finset.univ.erase i), (α j - α k)) := by
            simp [qic, Polynomial.eval_prod]
    _ = 0 := by rw [h0, mul_zero]

lemma qDiv_eval_self (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (i : Fin n) :
    (qDiv Q (α i)).eval (α i) = (Q.leadingCoeff : ℂ) *
      ∏ k ∈ (Finset.univ.erase i), (α i - α k) := by
  rw [qDiv_eq_qic Q α hfac i]
  rw [Polynomial.eval_mul, Polynomial.eval_C]
  simp [qic, Polynomial.eval_prod]

lemma qDiv_eval_self_ne_zero (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ)
    (hQ0 : Q ≠ 0) (hαinj : Function.Injective α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (i : Fin n) :
    (qDiv Q (α i)).eval (α i) ≠ 0 := by
  rw [qDiv_eval_self Q α hfac i]
  apply mul_ne_zero
  · exact_mod_cast lc_ne_zero Q hQ0
  · apply Finset.prod_ne_zero_iff.mpr
    intro k hk
    exact sub_ne_zero.mpr (hαinj.ne (by
      intro hki
      have : k ∈ (Finset.univ.erase i) := hk
      simp at this
      exact this hki.symm))

lemma qic_natDegree {n : ℕ} (α : Fin n → ℂ) (i : Fin n) : (qic α i).natDegree = n - 1 := by
  classical
  unfold qic
  rw [Polynomial.natDegree_prod_of_monic]
  · have hcard : (Finset.univ.erase i).card = n - 1 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
      simp [Fintype.card_fin]
    calc
      (∑ k ∈ (Finset.univ.erase i), (X - C (α k)).natDegree) = ∑ k ∈ (Finset.univ.erase i), 1 := by
        apply Finset.sum_congr rfl
        intro k hk
        exact Polynomial.natDegree_X_sub_C (α k)
      _ = (Finset.univ.erase i).card := by simp
      _ = n - 1 := hcard
  · intro k hk
    exact Polynomial.monic_X_sub_C (α k)

lemma qDiv_natDegree (Q : Polynomial ℤ) {n : ℕ} (hQ0 : Q ≠ 0) (α : Fin n → ℂ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (i : Fin n) : (qDiv Q (α i)).natDegree = n - 1 := by
  rw [qDiv_eq_qic Q α hfac i]
  rw [Polynomial.natDegree_C_mul (a := (Q.leadingCoeff : ℂ)) (a0 := by
    exact_mod_cast lc_ne_zero Q hQ0)]
  exact qic_natDegree α i

lemma qDiv_coeff_ge (Q : Polynomial ℤ) {n : ℕ} (hQ0 : Q ≠ 0) (α : Fin n → ℂ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (i : Fin n) (j : ℕ) (hj : n ≤ j) : (qDiv Q (α i)).coeff j = 0 := by
  have hnpos : 0 < n := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  have hd : (qDiv Q (α i)).natDegree ≤ n - 1 := by
    rw [qDiv_natDegree Q hQ0 α hfac i]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd (by omega))

end Basic

/-! ## Coefficient-wise complex conjugation and the conjugation involution -/

section Conj

/-- Conjugate a complex polynomial coefficient-wise. -/
noncomputable def conjPoly (P : Polynomial ℂ) : Polynomial ℂ := P.map (starRingEnd ℂ)

lemma conj_eval (P : Polynomial ℂ) (z : ℂ) :
    (starRingEnd ℂ) (P.eval z) = (conjPoly P).eval ((starRingEnd ℂ) z) := by
  unfold conjPoly
  rw [← Polynomial.eval₂_eq_eval_map (f := starRingEnd ℂ) (x := (starRingEnd ℂ) z) (p := P)]
  exact (Polynomial.eval₂_at_apply (starRingEnd ℂ) z (p := P)).symm

lemma conjPoly_conjPoly (P : Polynomial ℂ) : conjPoly (conjPoly P) = P := by
  unfold conjPoly
  rw [Polynomial.map_map]
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_map]
  simp

lemma conjPoly_X_sub_C (z : ℂ) : conjPoly (X - C z) = X - C ((starRingEnd ℂ) z) := by
  simp [conjPoly]

lemma conjPoly_C (z : ℂ) : conjPoly (C z) = C ((starRingEnd ℂ) z) := by
  simp [conjPoly]

lemma conjPoly_mul (P Q : Polynomial ℂ) : conjPoly (P * Q) = conjPoly P * conjPoly Q := by
  simp [conjPoly]

lemma conjPoly_add (P Q : Polynomial ℂ) : conjPoly (P + Q) = conjPoly P + conjPoly Q := by
  simp [conjPoly]

lemma conjPoly_sub (P Q : Polynomial ℂ) : conjPoly (P - Q) = conjPoly P - conjPoly Q := by
  simp [conjPoly]

lemma conjPoly_prod {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℂ) :
    conjPoly (∏ i ∈ s, P i) = ∏ i ∈ s, conjPoly (P i) := by
  unfold conjPoly
  rw [Polynomial.map_prod]

lemma conjPoly_sum {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℂ) :
    conjPoly (∑ i ∈ s, P i) = ∑ i ∈ s, conjPoly (P i) := by
  unfold conjPoly
  rw [Polynomial.map_sum]

lemma conjPoly_smul (c : ℂ) (P : Polynomial ℂ) : conjPoly (c • P) = (starRingEnd ℂ) c • conjPoly P := by
  unfold conjPoly
  rw [Polynomial.map_smul]

/-- The conjugation data: an involution `σ` such that `conj (α i) = α (σ i)`. -/
structure ConjPair {n : ℕ} (α : Fin n → ℂ) where
  σ : Fin n → Fin n
  hσ : ∀ i, (starRingEnd ℂ) (α i) = α (σ i)
  hσ2 : ∀ i, σ (σ i) = i

namespace ConjPair

variable {n : ℕ} {α : Fin n → ℂ}

lemma σ_bijective (cp : ConjPair α) : Function.Bijective cp.σ := by
  refine ⟨?_, ?_⟩
  · intro a b hab
    calc
      a = cp.σ (cp.σ a) := (cp.hσ2 a).symm
      _ = cp.σ (cp.σ b) := by rw [hab]
      _ = b := cp.hσ2 b
  · intro a
    refine ⟨cp.σ a, ?_⟩
    exact cp.hσ2 a

lemma conjPoly_qic (cp : ConjPair α) (i : Fin n) : conjPoly (qic α i) = qic α (cp.σ i) := by
  classical
  unfold conjPoly qic
  rw [Polynomial.map_prod]
  refine Finset.prod_bijective cp.σ cp.σ_bijective ?_ ?_
  · intro k
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hk hkσ
      exact hk (cp.σ_bijective.1 hkσ)
    · intro hkσ hki
      apply hkσ
      rw [hki]
  · intro k hk
    simp [cp.hσ]

end ConjPair

lemma exists_root_conj (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ) (hQ0 : Q ≠ 0)
    (hαinj : Function.Injective α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (i : Fin n) : ∃ k : Fin n, (starRingEnd ℂ) (α i) = α k := by
  classical
  have hroot : (Q.map (algebraMap ℤ ℂ)).eval ((starRingEnd ℂ) (α i)) = 0 := by
    have hz := alpha_root Q α hfac i
    calc
      (Q.map (algebraMap ℤ ℂ)).eval ((starRingEnd ℂ) (α i))
          = (starRingEnd ℂ) ((Q.map (algebraMap ℤ ℂ)).eval (α i)) := by
              have hc := conj_eval (Q.map (algebraMap ℤ ℂ)) (α i)
              have hq : conjPoly (Q.map (algebraMap ℤ ℂ)) = Q.map (algebraMap ℤ ℂ) := by
                unfold conjPoly
                apply Polynomial.ext
                intro m
                rw [Polynomial.coeff_map, Polynomial.coeff_map]
                simp
              rw [hq] at hc
              exact hc.symm
      _ = 0 := by rw [hz]; simp
  have hroot' : (Polynomial.C ((Q.leadingCoeff : ℂ)) *
        (∏ k : Fin n, (X - Polynomial.C (α k)))).eval ((starRingEnd ℂ) (α i)) = 0 := by
    rw [← hfac]
    exact hroot
  have hlc0 : (Q.leadingCoeff : ℂ) ≠ 0 := by
    exact_mod_cast lc_ne_zero Q hQ0
  have hmul : (Q.leadingCoeff : ℂ) *
      (∏ k : Fin n, ((starRingEnd ℂ) (α i) - α k)) = 0 := by
    have hE : (Polynomial.C ((Q.leadingCoeff : ℂ)) *
        (∏ k : Fin n, (X - Polynomial.C (α k)))).eval ((starRingEnd ℂ) (α i))
        = (Q.leadingCoeff : ℂ) * (∏ k : Fin n, ((starRingEnd ℂ) (α i) - α k)) := by
      rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_prod]
      simp
    rw [← hE]
    exact hroot'
  have hprod0 : (∏ k : Fin n, ((starRingEnd ℂ) (α i) - α k)) = 0 := by
    exact (mul_eq_zero.mp hmul).resolve_left hlc0
  have hsome := (Finset.prod_eq_zero_iff (s := (Finset.univ : Finset (Fin n)))
    (f := fun k : Fin n => ((starRingEnd ℂ) (α i) - α k))).mp hprod0
  rcases hsome with ⟨k, hk, hk0⟩
  refine ⟨k, ?_⟩
  exact sub_eq_zero.mp hk0


/-- Build the conjugation involution from the root data. -/
noncomputable def conjPairOf (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ) (hQ0 : Q ≠ 0)
    (hαinj : Function.Injective α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i))) :
    ConjPair α := by
  classical
  let hroot : ∀ i : Fin n, ∃ k : Fin n, (starRingEnd ℂ) (α i) = α k :=
    fun i => exists_root_conj Q α hQ0 hαinj hfac i
  refine ⟨fun i => Classical.choose (hroot i), fun i => Classical.choose_spec (hroot i), ?_⟩
  intro i
  apply hαinj
  calc
    α (Classical.choose (hroot (Classical.choose (hroot i)))) =
        (starRingEnd ℂ) (α (Classical.choose (hroot i))) := by
          rw [← Classical.choose_spec (hroot (Classical.choose (hroot i)))]
    _ = (starRingEnd ℂ) ((starRingEnd ℂ) (α i)) := by
          rw [← Classical.choose_spec (hroot i)]
    _ = α i := by simp

lemma conjPoly_qDiv (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ) (cp : ConjPair α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (i : Fin n) : conjPoly (qDiv Q (α i)) = qDiv Q (α (cp.σ i)) := by
  rw [qDiv_eq_qic Q α hfac i, qDiv_eq_qic Q α hfac (cp.σ i)]
  calc
    conjPoly (Polynomial.C ((Q.leadingCoeff : ℂ)) * qic α i)
        = Polynomial.C ((starRingEnd ℂ) (Q.leadingCoeff : ℂ)) * conjPoly (qic α i) := by
            rw [conjPoly_mul, conjPoly_C]
    _ = Polynomial.C ((Q.leadingCoeff : ℂ)) * qic α (cp.σ i) := by
            rw [ConjPair.conjPoly_qic cp i]
            congr 1
            simp

end Conj


/-! ## Real row construction from the conjugation involution

For every orbit of `σ` on the roots (a real root `{i}`, or a conjugate pair
`{i, σ i}`) we build a real polynomial (`rowPoly`, given as its complex
embedding) whose ℂ-linear span is the same as the span of the `qDiv`-quotients:

  real orbit `{i}`:          row = q_i
  pair `{i, σ i}`, i < σ i:  row_i = q_i + q_{σ i},  row_{σ i} = I·(q_{σ i} − q_i)

(the case `σ i < i` is the mirror).  The rows are conjugate-invariant (hence
have real coefficients) and their coefficient matrix `rowMat` is invertible and
satisfies the real dual condition. -/

section Rows

open scoped Matrix

/-- The q-expansion coefficient of the row at index `i` on `q k`. -/
noncomputable def qcoef {n : ℕ} (σ : Fin n → Fin n) (i k : Fin n) : ℂ :=
  if σ i = i then (if k = i then 1 else 0)
  else if i < σ i then (if k = i then 1 else 0) + (if k = σ i then 1 else 0)
  else Complex.I * ((if k = i then 1 else 0) - (if k = σ i then 1 else 0))

/-- The row polynomial (complex version) attached to the root index `i`. -/
noncomputable def rowPoly {n : ℕ} (q : Fin n → Polynomial ℂ) (σ : Fin n → Fin n)
    (i : Fin n) : Polynomial ℂ :=
  if σ i = i then q i
  else if i < σ i then q i + q (σ i)
  else Polynomial.C (Complex.I) * (q i - q (σ i))

/-- Coefficient matrix of the rows (real parts of the row coefficients). -/
noncomputable def rowMat {n : ℕ} (q : Fin n → Polynomial ℂ) (σ : Fin n → Fin n) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ((rowPoly q σ i).coeff j.val).re

/-- Row polynomial with the quotient family. -/
noncomputable def qrow {n : ℕ} (Q : Polynomial ℤ) (α : Fin n → ℂ)
    (σ : Fin n → Fin n) (i : Fin n) : Polynomial ℂ :=
  rowPoly (fun k => qDiv Q (α k)) σ i

/-- Coefficient matrix of the quotient rows. -/
noncomputable def qrowMat {n : ℕ} (Q : Polynomial ℤ) (α : Fin n → ℂ)
    (σ : Fin n → Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => ((qrow Q α σ i).coeff j.val).re

lemma qrow_eq (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ) (σ : Fin n → Fin n) (i : Fin n) :
    qrow Q α σ i = rowPoly (fun k => qDiv Q (α k)) σ i := rfl

/-- realness of a coefficient from conjugate-invariance of the polynomial. -/
lemma coeff_re_of_conjPoly {P : Polynomial ℂ} (h : conjPoly P = P) (j : ℕ) :
    P.coeff j = (((P.coeff j).re : ℝ) : ℂ) := by
  have hc : (conjPoly P).coeff j = P.coeff j := by rw [h]
  unfold conjPoly at hc
  rw [Polynomial.coeff_map] at hc
  apply Complex.ext
  · simp
  · have him : (P.coeff j).im = 0 := (Complex.conj_eq_iff_im.mp hc)
    simp [him]

/-- rows are conjugate-invariant (hence real). -/
lemma rowPoly_conj {n : ℕ} {α : Fin n → ℂ} (cp : ConjPair α)
    {q : Fin n → Polynomial ℂ} (hconjq : ∀ i, conjPoly (q i) = q (cp.σ i)) (i : Fin n) :
    conjPoly (rowPoly q cp.σ i) = rowPoly q cp.σ i := by
  classical
  unfold rowPoly
  by_cases h1 : cp.σ i = i
  · rw [if_pos h1]
    calc
      conjPoly (q i) = q (cp.σ i) := hconjq i
      _ = q i := by rw [h1]
  · rw [if_neg h1]
    by_cases h2 : i < cp.σ i
    · rw [if_pos h2]
      calc
        conjPoly (q i + q (cp.σ i)) = conjPoly (q i) + conjPoly (q (cp.σ i)) := conjPoly_add _ _
        _ = q (cp.σ i) + q (cp.σ (cp.σ i)) := by rw [hconjq i, hconjq (cp.σ i)]
        _ = q (cp.σ i) + q i := by rw [cp.hσ2 i]
        _ = q i + q (cp.σ i) := by ring
    · rw [if_neg h2]
      calc
        conjPoly (Polynomial.C Complex.I * (q i - q (cp.σ i)))
            = conjPoly (Polynomial.C Complex.I) * conjPoly (q i - q (cp.σ i)) := conjPoly_mul _ _
        _ = Polynomial.C (-Complex.I) * conjPoly (q i - q (cp.σ i)) := by
            rw [conjPoly_C]
            simp
        _ = Polynomial.C (-Complex.I) * (q (cp.σ i) - q (cp.σ (cp.σ i))) := by
            rw [conjPoly_sub, hconjq i, hconjq (cp.σ i)]
        _ = Polynomial.C (-Complex.I) * (q (cp.σ i) - q i) := by rw [cp.hσ2 i]
        _ = Polynomial.C Complex.I * (q i - q (cp.σ i)) := by
            rw [Polynomial.C_neg]
            ring

lemma qrow_conj (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ) (cp : ConjPair α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (i : Fin n) : conjPoly (qrow Q α cp.σ i) = qrow Q α cp.σ i := by
  rw [qrow_eq]
  exact rowPoly_conj cp (q := fun k => qDiv Q (α k))
    (hconjq := fun k => conjPoly_qDiv Q α cp hfac k) i

/-- row coefficients are real. -/
lemma qrow_coeff_re (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ) (cp : ConjPair α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (i : Fin n) (j : ℕ) :
    (qrow Q α cp.σ i).coeff j = (((qrow Q α cp.σ i).coeff j).re : ℂ) := by
  exact coeff_re_of_conjPoly (qrow_conj Q α cp hfac i) j

/-- row coefficient expressed through the q-expansion coefficients. -/
lemma sum_indicator_mul {n : ℕ} (c : Fin n → ℂ) (a : Fin n) :
    (∑ k : Fin n, (if k = a then 1 else 0 : ℂ) * c k) = c a := by
  classical
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    simp [hba]
  · intro hni
    simp at hni

lemma sum_indicator_real {n : ℕ} (a : Fin n) :
    (∑ k : Fin n, (if k = a then 1 else 0 : ℝ)) = 1 := by
  classical
  rw [Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    simp [hba]
  · intro hni
    simp at hni

lemma sum_add_indicator {n : ℕ} (c : Fin n → ℂ) (a b : Fin n) :
    (∑ k : Fin n, ((if k = a then 1 else 0 : ℂ) + (if k = b then 1 else 0)) * c k)
      = (∑ k : Fin n, (if k = a then 1 else 0 : ℂ) * c k)
          + ∑ k : Fin n, (if k = b then 1 else 0 : ℂ) * c k := by
  calc
    (∑ k : Fin n, ((if k = a then 1 else 0 : ℂ) + (if k = b then 1 else 0)) * c k)
        = ∑ k : Fin n, ((if k = a then 1 else 0 : ℂ) * c k + (if k = b then 1 else 0 : ℂ) * c k) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
    _ = (∑ k : Fin n, (if k = a then 1 else 0 : ℂ) * c k)
        + ∑ k : Fin n, (if k = b then 1 else 0 : ℂ) * c k := by
            rw [Finset.sum_add_distrib]

lemma sum_sub_indicator {n : ℕ} (c : Fin n → ℂ) (a b : Fin n) :
    (∑ k : Fin n, ((if k = a then 1 else 0 : ℂ) - (if k = b then 1 else 0)) * c k)
      = (∑ k : Fin n, (if k = a then 1 else 0 : ℂ) * c k)
          - ∑ k : Fin n, (if k = b then 1 else 0 : ℂ) * c k := by
  calc
    (∑ k : Fin n, ((if k = a then 1 else 0 : ℂ) - (if k = b then 1 else 0)) * c k)
        = ∑ k : Fin n, ((if k = a then 1 else 0 : ℂ) * c k - (if k = b then 1 else 0 : ℂ) * c k) := by
            apply Finset.sum_congr rfl
            intro k hk
            ring
    _ = (∑ k : Fin n, (if k = a then 1 else 0 : ℂ) * c k)
        - ∑ k : Fin n, (if k = b then 1 else 0 : ℂ) * c k := by
            rw [Finset.sum_sub_distrib]

lemma rowPoly_coeff_eq_qcoef_sum {n : ℕ} (q : Fin n → Polynomial ℂ) (σ : Fin n → Fin n)
    (i : Fin n) (j : ℕ) :
    (rowPoly q σ i).coeff j = ∑ k : Fin n, qcoef σ i k * (q k).coeff j := by
  classical
  unfold rowPoly
  by_cases h1 : σ i = i
  · rw [if_pos h1]
    have hq : ∀ k : Fin n, qcoef σ i k = (if k = i then 1 else 0 : ℂ) := by
      intro k
      unfold qcoef
      rw [if_pos h1]
    calc
      (q i).coeff j = ∑ k : Fin n, (if k = i then 1 else 0 : ℂ) * (q k).coeff j := by
        rw [← sum_indicator_mul (fun k => (q k).coeff j) i]
      _ = ∑ k : Fin n, qcoef σ i k * (q k).coeff j := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hq k]
  · rw [if_neg h1]
    by_cases h2 : i < σ i
    · rw [if_pos h2]
      have hq : ∀ k : Fin n, qcoef σ i k =
          ((if k = i then 1 else 0 : ℂ) + (if k = σ i then 1 else 0)) := by
        intro k
        unfold qcoef
        rw [if_neg h1, if_pos h2]
      rw [Polynomial.coeff_add]
      calc
        (q i).coeff j + (q (σ i)).coeff j
            = (∑ k : Fin n, (if k = i then 1 else 0 : ℂ) * (q k).coeff j)
                + ∑ k : Fin n, (if k = σ i then 1 else 0 : ℂ) * (q k).coeff j := by
                  rw [← sum_indicator_mul (fun k => (q k).coeff j) i,
                      ← sum_indicator_mul (fun k => (q k).coeff j) (σ i)]
        _ = ∑ k : Fin n,
            ((if k = i then 1 else 0 : ℂ) + (if k = σ i then 1 else 0)) * (q k).coeff j := by
              exact (sum_add_indicator (fun k => (q k).coeff j) i (σ i)).symm
        _ = ∑ k : Fin n, qcoef σ i k * (q k).coeff j := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [hq k]
    · rw [if_neg h2]
      have hq : ∀ k : Fin n, qcoef σ i k =
          Complex.I * ((if k = i then 1 else 0 : ℂ) - (if k = σ i then 1 else 0)) := by
        intro k
        unfold qcoef
        rw [if_neg h1, if_neg h2]
      rw [Polynomial.coeff_C_mul (q i - q (σ i))]
      rw [Polynomial.coeff_sub]
      have hinner : (q i).coeff j - (q (σ i)).coeff j =
          ∑ k : Fin n, ((if k = i then 1 else 0 : ℂ) - (if k = σ i then 1 else 0)) * (q k).coeff j := by
        rw [← sum_indicator_mul (fun k => (q k).coeff j) i,
            ← sum_indicator_mul (fun k => (q k).coeff j) (σ i)]
        exact (sum_sub_indicator (fun k => (q k).coeff j) i (σ i)).symm
      calc
        Complex.I * ((q i).coeff j - (q (σ i)).coeff j)
            = Complex.I * (∑ k : Fin n,
                ((if k = i then 1 else 0 : ℂ) - (if k = σ i then 1 else 0)) * (q k).coeff j) := by
                rw [hinner]
        _ = ∑ k : Fin n, Complex.I *
            (((if k = i then 1 else 0 : ℂ) - (if k = σ i then 1 else 0)) * (q k).coeff j) := by
                rw [Finset.mul_sum]
        _ = ∑ k : Fin n, qcoef σ i k * (q k).coeff j := by
                apply Finset.sum_congr rfl
                intro k hk
                rw [hq k]
                ring

lemma qrow_coeff_eq_qcoef_sum (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ)
    (σ : Fin n → Fin n) (i : Fin n) (j : ℕ) :
    (qrow Q α σ i).coeff j = ∑ k : Fin n, qcoef σ i k * (qDiv Q (α k)).coeff j := by
  rw [qrow_eq]
  exact rowPoly_coeff_eq_qcoef_sum (q := fun k => qDiv Q (α k)) σ i j

private lemma norm_one_indicator_le {n : ℕ} (a : Fin n) (k : Fin n) :
    ‖(if k = a then 1 else 0 : ℂ)‖ ≤ (if k = a then 1 else 0 : ℝ) := by
  classical
  by_cases hka : k = a
  · rw [hka]
    simp
  · simp [hka]

private lemma norm_add_ind_le {n : ℕ} (σ : Fin n → Fin n) (i : Fin n) (h1 : ¬ σ i = i)
    (k : Fin n) :
    ‖((if k = i then 1 else 0 : ℂ) + (if k = σ i then 1 else 0))‖
      ≤ (if k = i then 1 else 0 : ℝ) + (if k = σ i then 1 else 0 : ℝ) := by
  classical
  by_cases hki : k = i
  · rw [hki]
    have hne : i ≠ σ i := by exact fun h => h1 h.symm
    simp [hne]
  · by_cases hkσ : k = σ i
    · rw [hkσ]
      simp [h1]
    · simp [hki, hkσ]

private lemma norm_I_sub_le {n : ℕ} (σ : Fin n → Fin n) (i : Fin n) (h1 : ¬ σ i = i)
    (k : Fin n) :
    ‖Complex.I * ((if k = i then 1 else 0 : ℂ) - (if k = σ i then 1 else 0))‖
      ≤ (if k = i then 1 else 0 : ℝ) + (if k = σ i then 1 else 0 : ℝ) := by
  classical
  by_cases hki : k = i
  · rw [hki]
    have hne : i ≠ σ i := by exact fun h => h1 h.symm
    simp [hne]
  · by_cases hkσ : k = σ i
    · rw [hkσ]
      simp [h1]
    · simp [hki, hkσ]

/-- each row uses at most two q's:  ℓ₁ bound. -/
lemma qcoef_sum_norm_le_two {n : ℕ} (σ : Fin n → Fin n) (i : Fin n) :
    (∑ k : Fin n, ‖qcoef σ i k‖) ≤ 2 := by
  classical
  by_cases h1 : σ i = i
  · have hq : ∀ k : Fin n, qcoef σ i k = (if k = i then 1 else 0 : ℂ) := by
      intro k
      unfold qcoef
      rw [if_pos h1]
    calc
      (∑ k : Fin n, ‖qcoef σ i k‖)
          = ∑ k : Fin n, ‖(if k = i then 1 else 0 : ℂ)‖ := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [hq k]
      _ ≤ ∑ k : Fin n, (if k = i then 1 else 0 : ℝ) := by
              apply Finset.sum_le_sum
              intro k hk
              exact norm_one_indicator_le i k
      _ = 1 := sum_indicator_real i
      _ ≤ 2 := by norm_num
  · by_cases h2 : i < σ i
    · have hq : ∀ k : Fin n, qcoef σ i k =
          ((if k = i then 1 else 0 : ℂ) + (if k = σ i then 1 else 0)) := by
        intro k
        unfold qcoef
        rw [if_neg h1, if_pos h2]
      calc
        (∑ k : Fin n, ‖qcoef σ i k‖)
            = ∑ k : Fin n, ‖((if k = i then 1 else 0 : ℂ) + (if k = σ i then 1 else 0))‖ := by
                apply Finset.sum_congr rfl
                intro k hk
                rw [hq k]
        _ ≤ ∑ k : Fin n, ((if k = i then 1 else 0 : ℝ) + (if k = σ i then 1 else 0 : ℝ)) := by
                apply Finset.sum_le_sum
                intro k hk
                exact norm_add_ind_le σ i h1 k
        _ = (∑ k : Fin n, (if k = i then 1 else 0 : ℝ))
            + (∑ k : Fin n, (if k = σ i then 1 else 0 : ℝ)) := by
                rw [Finset.sum_add_distrib]
        _ = 2 := by rw [sum_indicator_real i, sum_indicator_real (σ i)]; norm_num
    · have hq : ∀ k : Fin n, qcoef σ i k =
          Complex.I * ((if k = i then 1 else 0 : ℂ) - (if k = σ i then 1 else 0)) := by
        intro k
        unfold qcoef
        rw [if_neg h1, if_neg h2]
      calc
        (∑ k : Fin n, ‖qcoef σ i k‖)
            = ∑ k : Fin n, ‖Complex.I * ((if k = i then 1 else 0 : ℂ) - (if k = σ i then 1 else 0))‖ := by
                apply Finset.sum_congr rfl
                intro k hk
                rw [hq k]
        _ ≤ ∑ k : Fin n, ((if k = i then 1 else 0 : ℝ) + (if k = σ i then 1 else 0 : ℝ)) := by
                apply Finset.sum_le_sum
                intro k hk
                exact norm_I_sub_le σ i h1 k
        _ = (∑ k : Fin n, (if k = i then 1 else 0 : ℝ))
            + (∑ k : Fin n, (if k = σ i then 1 else 0 : ℝ)) := by
                rw [Finset.sum_add_distrib]
        _ = 2 := by rw [sum_indicator_real i, sum_indicator_real (σ i)]; norm_num

end Rows


/-! ## Row evaluations, linear independence and the determinant -/

section Indep

/-- Each quotient-row has degree at most `n−1`. -/
lemma qrow_natDegree_le (Q : Polynomial ℤ) {n : ℕ} (hQ0 : Q ≠ 0) (α : Fin n → ℂ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (σ : Fin n → Fin n) (i : Fin n) : (qrow Q α σ i).natDegree ≤ n - 1 := by
  classical
  unfold qrow rowPoly
  by_cases h1 : σ i = i
  · rw [if_pos h1]
    rw [qDiv_natDegree Q hQ0 α hfac i]
  · rw [if_neg h1]
    by_cases h2 : i < σ i
    · rw [if_pos h2]
      calc
        (qDiv Q (α i) + qDiv Q (α (σ i))).natDegree
            ≤ max (qDiv Q (α i)).natDegree (qDiv Q (α (σ i))).natDegree :=
              Polynomial.natDegree_add_le _ _
        _ ≤ max (n - 1) (n - 1) := by
              rw [qDiv_natDegree Q hQ0 α hfac i, qDiv_natDegree Q hQ0 α hfac (σ i)]
        _ ≤ n - 1 := by simp
    · rw [if_neg h2]
      calc
        (Polynomial.C Complex.I * (qDiv Q (α i) - qDiv Q (α (σ i)))).natDegree
            ≤ (qDiv Q (α i) - qDiv Q (α (σ i))).natDegree := by
              rw [Polynomial.natDegree_C_mul (a := Complex.I) (a0 := Complex.I_ne_zero)]
        _ ≤ max (qDiv Q (α i)).natDegree (qDiv Q (α (σ i))).natDegree :=
              Polynomial.natDegree_sub_le _ _
        _ ≤ max (n - 1) (n - 1) := by
              rw [qDiv_natDegree Q hQ0 α hfac i, qDiv_natDegree Q hQ0 α hfac (σ i)]
        _ ≤ n - 1 := by simp

/-- A polynomial of degree `< n` is determined by its first `n` coefficients
(needs `1 ≤ n`; vacuous for `n = 0`). -/
lemma poly_eq_sum_coeff_fin {n : ℕ} (hn : 1 ≤ n) (P : Polynomial ℂ)
    (hdeg : P.natDegree ≤ n - 1) :
    P = ∑ j : Fin n, Polynomial.C (P.coeff j.val) * Polynomial.X ^ j.val := by
  classical
  apply Polynomial.ext
  intro m
  by_cases hm : m < n
  · let j : Fin n := ⟨m, hm⟩
    have hg0 : ∀ b : Fin n, b ∈ (Finset.univ : Finset (Fin n)) → b ≠ j →
        (Polynomial.C (P.coeff b.val) * Polynomial.X ^ b.val).coeff m = 0 := by
      intro b hb hbj
      have hbv : b.val ≠ m := by
        intro hv
        apply hbj
        exact Fin.ext hv
      rw [Polynomial.coeff_C_mul (Polynomial.X ^ b.val)]
      rw [Polynomial.coeff_X_pow]
      have hmne : m ≠ b.val := fun h => hbv h.symm
      simp [hmne]
    have hsum : (∑ k : Fin n, (Polynomial.C (P.coeff k.val) * Polynomial.X ^ k.val).coeff m)
        = (Polynomial.C (P.coeff j.val) * Polynomial.X ^ j.val).coeff m := by
      exact Finset.sum_eq_single (s := (Finset.univ : Finset (Fin n)))
        (f := fun k : Fin n => (Polynomial.C (P.coeff k.val) * Polynomial.X ^ k.val).coeff m)
        j hg0 (by intro hj; exact False.elim (hj (Finset.mem_univ j)))
    have hgj : (Polynomial.C (P.coeff j.val) * Polynomial.X ^ j.val).coeff m = P.coeff m := by
      have hjv : j.val = m := rfl
      rw [Polynomial.coeff_C_mul (Polynomial.X ^ j.val)]
      rw [Polynomial.coeff_X_pow]
      simp [hjv]
    rw [coeff_fintype_sum]
    rw [hsum]
    exact hgj.symm
  · have hmge : n ≤ m := le_of_not_gt hm
    have h0 : P.coeff m = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (by
      have hn' : n - 1 < n := Nat.sub_lt (lt_of_lt_of_le zero_lt_one hn) zero_lt_one
      omega))
    have h0' : ∀ k : Fin n, (Polynomial.C (P.coeff k.val) * Polynomial.X ^ k.val).coeff m = 0 := by
      intro k
      have hkv : k.val < m := lt_of_lt_of_le k.isLt hmge
      rw [Polynomial.coeff_C_mul (Polynomial.X ^ k.val)]
      rw [Polynomial.coeff_X_pow]
      have hmne : m ≠ k.val := ne_of_gt hkv
      simp [hmne]
    rw [h0]
    rw [coeff_fintype_sum]
    simp [h0']

/-- The evaluation of a `qrow` vanishes at a root outside its orbit. -/
lemma qrow_eval_zero_of_out (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (σ : Fin n → Fin n) {i k : Fin n} (hik : k ≠ i) (hikσ : k ≠ σ i) :
    (qrow Q α σ i).eval (α k) = 0 := by
  classical
  unfold qrow rowPoly
  by_cases h1 : σ i = i
  · rw [if_pos h1]
    exact qDiv_eval_ne Q α hfac hik
  · rw [if_neg h1]
    by_cases h2 : i < σ i
    · rw [if_pos h2]
      simp [qDiv_eval_ne Q α hfac hik, qDiv_eval_ne Q α hfac hikσ]
    · rw [if_neg h2]
      simp [qDiv_eval_ne Q α hfac hik, qDiv_eval_ne Q α hfac hikσ]

/-- evaluation of the row at a real root: nonzero at itself. -/
lemma qrow_eval_real_self (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (σ : Fin n → Fin n) {i : Fin n} (hi : σ i = i) :
    (qrow Q α σ i).eval (α i) = (qDiv Q (α i)).eval (α i) := by
  unfold qrow rowPoly
  rw [if_pos hi]

lemma eval_sum_mul {ι : Type*} [Fintype ι] (t : ι → ℂ) (P : ι → Polynomial ℂ) (x : ℂ) :
    (∑ i, Polynomial.C (t i) * P i).eval x = ∑ i, t i * (P i).eval x := by
  classical
  simp [Polynomial.eval_finsetSum]

lemma sum_eq_two {ι : Type*} [Fintype ι] [DecidableEq ι] (f : ι → ℂ) {a b : ι}
    (hab : a ≠ b) (h0 : ∀ j : ι, j ≠ a → j ≠ b → f j = 0) :
    (∑ j : ι, f j) = f a + f b := by
  classical
  have hsub : (∑ x ∈ ({a, b} : Finset ι), f x) = ∑ x ∈ (Finset.univ : Finset ι), f x := by
    refine Finset.sum_subset ?_ ?_
    · intro x hx
      simp at hx
      exact Finset.mem_univ x
    · intro x hx hx2
      have ha : x ≠ a := by
        intro hxa
        apply hx2
        simp [hxa]
      have hb : x ≠ b := by
        intro hxb
        apply hx2
        simp [hxb]
      exact h0 x ha hb
  calc
    (∑ j : ι, f j) = ∑ x ∈ ({a, b} : Finset ι), f x := by
        rw [← hsub]
    _ = f a + f b := by
        exact Finset.sum_pair (f := f) hab

/-- For `i < σ i`, the row at `i` evaluated at `α i` is `qDiv(α i)(α i)`. -/
lemma qrow_lt_self (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (σ : Fin n → Fin n) {i : Fin n} (h2 : i < σ i) :
    (qrow Q α σ i).eval (α i) = (qDiv Q (α i)).eval (α i) := by
  classical
  unfold qrow rowPoly
  have h1 : σ i ≠ i := by
    intro h
    exact (ne_of_lt h2) h.symm
  rw [if_neg h1, if_pos h2]
  simp [qDiv_eval_ne Q α hfac (ne_of_lt h2)]

/-- For `i < σ i`, the row at `σ i` evaluated at `α i`. -/
lemma qrow_lt_sigma_eval (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (cp : ConjPair α) {i : Fin n} (h2 : i < cp.σ i) :
    (qrow Q α cp.σ (cp.σ i)).eval (α i) = (-Complex.I) * (qDiv Q (α i)).eval (α i) := by
  classical
  unfold qrow rowPoly
  have h1 : cp.σ (cp.σ i) ≠ cp.σ i := by
    intro h
    exact (ne_of_lt h2) (cp.σ_bijective.1 h.symm)
  have h3 : ¬ cp.σ i < cp.σ (cp.σ i) := by
    intro h
    have : cp.σ i < i := by simpa [cp.hσ2 i] using h
    exact lt_asymm h2 this
  rw [if_neg h1, if_neg h3, cp.hσ2 i]
  simp [qDiv_eval_ne Q α hfac (ne_of_lt h2)]

/-- For `i < σ i`, the row at `i` evaluated at `α (σ i)`. -/
lemma qrow_lt_at_sigma (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (σ : Fin n → Fin n) {i : Fin n} (h2 : i < σ i) :
    (qrow Q α σ i).eval (α (σ i)) = (qDiv Q (α (σ i))).eval (α (σ i)) := by
  classical
  unfold qrow rowPoly
  have h1 : σ i ≠ i := by
    intro h
    exact (ne_of_lt h2) h.symm
  rw [if_neg h1, if_pos h2]
  simp [qDiv_eval_ne Q α hfac (by exact (ne_of_lt h2).symm)]

/-- For `i < σ i`, the row at `σ i` evaluated at `α (σ i)`. -/
lemma qrow_lt_sigma_at_sigma (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (cp : ConjPair α) {i : Fin n} (h2 : i < cp.σ i) :
    (qrow Q α cp.σ (cp.σ i)).eval (α (cp.σ i)) =
      Complex.I * (qDiv Q (α (cp.σ i))).eval (α (cp.σ i)) := by
  classical
  unfold qrow rowPoly
  have h1 : cp.σ (cp.σ i) ≠ cp.σ i := by
    intro h
    exact (ne_of_lt h2) (cp.σ_bijective.1 h.symm)
  have h3 : ¬ cp.σ i < cp.σ (cp.σ i) := by
    intro h
    have : cp.σ i < i := by simpa [cp.hσ2 i] using h
    exact lt_asymm h2 this
  rw [if_neg h1, if_neg h3, cp.hσ2 i]
  simp [qDiv_eval_ne Q α hfac (by exact (ne_of_lt h2).symm)]

lemma qrow_pair_zero_lt (Q : Polynomial ℤ) {n : ℕ} (hQ0 : Q ≠ 0) (α : Fin n → ℂ)
    (hαinj : Function.Injective α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (cp : ConjPair α) {lam : Fin n → ℂ} {i : Fin n} (hord : i < cp.σ i)
    (h1 : (∑ j : Fin n, lam j * (qrow Q α cp.σ j).eval (α i)) = 0)
    (h2 : (∑ j : Fin n, lam j * (qrow Q α cp.σ j).eval (α (cp.σ i))) = 0) :
    lam i = 0 ∧ lam (cp.σ i) = 0 := by
  classical
  let f1 : Fin n → ℂ := fun j => lam j * (qrow Q α cp.σ j).eval (α i)
  let f2 : Fin n → ℂ := fun j => lam j * (qrow Q α cp.σ j).eval (α (cp.σ i))
  have hne : i ≠ cp.σ i := ne_of_lt hord
  have hvan1 : ∀ j : Fin n, j ≠ i → j ≠ cp.σ i → f1 j = 0 := by
    intro j hj1 hj2
    have hz : (qrow Q α cp.σ j).eval (α i) = 0 := by
      refine qrow_eval_zero_of_out Q α hfac cp.σ ?_ ?_
      · exact hj1.symm
      · intro h
        apply hj2
        calc
          j = cp.σ (cp.σ j) := (cp.hσ2 j).symm
          _ = cp.σ i := by rw [h.symm]
    simp [f1, hz]
  have hvan2 : ∀ j : Fin n, j ≠ i → j ≠ cp.σ i → f2 j = 0 := by
    intro j hj1 hj2
    have hz : (qrow Q α cp.σ j).eval (α (cp.σ i)) = 0 := by
      refine qrow_eval_zero_of_out Q α hfac cp.σ ?_ ?_
      · exact hj2.symm
      · intro h
        exact hj1 (cp.σ_bijective.1 h.symm)
    simp [f2, hz]
  have hs1 : (∑ j : Fin n, f1 j) = f1 i + f1 (cp.σ i) :=
    sum_eq_two (f := f1) hne hvan1
  have hs2 : (∑ j : Fin n, f2 j) = f2 i + f2 (cp.σ i) :=
    sum_eq_two (f := f2) hne hvan2
  have he1 : f1 i + f1 (cp.σ i) = 0 := by
    rw [← hs1]
    exact h1
  have he2 : f2 i + f2 (cp.σ i) = 0 := by
    rw [← hs2]
    exact h2
  have hρi : (qDiv Q (α i)).eval (α i) ≠ 0 := qDiv_eval_self_ne_zero Q α hQ0 hαinj hfac i
  have hρs : (qDiv Q (α (cp.σ i))).eval (α (cp.σ i)) ≠ 0 :=
    qDiv_eval_self_ne_zero Q α hQ0 hαinj hfac (cp.σ i)
  have heq1 : (lam i - Complex.I * lam (cp.σ i)) * (qDiv Q (α i)).eval (α i) = 0 := by
    have hf1i : f1 i = lam i * (qDiv Q (α i)).eval (α i) := by
      simp [f1, qrow_lt_self Q α hfac cp.σ hord]
    have hf1s : f1 (cp.σ i) = lam (cp.σ i) * ((-Complex.I) * (qDiv Q (α i)).eval (α i)) := by
      simp [f1, qrow_lt_sigma_eval Q α hfac cp hord]
    rw [hf1i, hf1s] at he1
    -- lam i * ρ + lam σ * (-I ρ) = 0  →  (lam i - I lam σ)·ρ = 0
    linear_combination (norm := ring) he1
  have heq2 : (lam i + Complex.I * lam (cp.σ i)) * (qDiv Q (α (cp.σ i))).eval (α (cp.σ i)) = 0 := by
    have hf2i : f2 i = lam i * (qDiv Q (α (cp.σ i))).eval (α (cp.σ i)) := by
      simp [f2, qrow_lt_at_sigma Q α hfac cp.σ hord]
    have hf2s : f2 (cp.σ i) = lam (cp.σ i) * (Complex.I * (qDiv Q (α (cp.σ i))).eval (α (cp.σ i))) := by
      simp [f2, qrow_lt_sigma_at_sigma Q α hfac cp hord]
    rw [hf2i, hf2s] at he2
    linear_combination (norm := ring) he2
  have hfac1 : lam i - Complex.I * lam (cp.σ i) = 0 :=
    (mul_eq_zero.mp heq1).resolve_right hρi
  have hfac2 : lam i + Complex.I * lam (cp.σ i) = 0 :=
    (mul_eq_zero.mp heq2).resolve_right hρs
  have hsum0 : (2 : ℂ) * lam i = 0 := by
    -- (λi - Iλs) + (λi + Iλs) = 0
    have h := congrArg (fun x => x) (by
      -- hfac1 + hfac2
      have h12 : (lam i - Complex.I * lam (cp.σ i)) + (lam i + Complex.I * lam (cp.σ i)) = 0 := by
        rw [hfac1, hfac2]
        ring
      exact h12)
    linear_combination (norm := ring) h
  have hlami : lam i = 0 := by
    exact (mul_eq_zero.mp hsum0).resolve_left (by norm_num : (2 : ℂ) ≠ 0)
  have hIs : Complex.I * lam (cp.σ i) = 0 := by
    have : lam i - Complex.I * lam (cp.σ i) = 0 := hfac1
    rw [hlami] at this
    simpa using this
  have hlams : lam (cp.σ i) = 0 :=
    (mul_eq_zero.mp hIs).resolve_left Complex.I_ne_zero
  exact ⟨hlami, hlams⟩

/-- Any ℂ-combination of quotient rows that vanishes as a polynomial has all
coefficients zero: the rows are ℂ-linearly independent. -/
lemma qrow_linearIndependent_poly (Q : Polynomial ℤ) {n : ℕ} (hQ0 : Q ≠ 0)
    (α : Fin n → ℂ) (hαinj : Function.Injective α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (cp : ConjPair α) :
    ∀ lam : Fin n → ℂ, (∑ i : Fin n, Polynomial.C (lam i) * qrow Q α cp.σ i) = 0 → ∀ i, lam i = 0 := by
  classical
  intro lam hsum i
  have hev : ∀ k : Fin n, (∑ j : Fin n, lam j * (qrow Q α cp.σ j).eval (α k)) = 0 := by
    intro k
    have hz := congrArg (fun P : Polynomial ℂ => P.eval (α k)) hsum
    have hz1 : (∑ j : Fin n, (Polynomial.C (lam j) * qrow Q α cp.σ j).eval (α k)) = 0 := by
      -- move eval inside the sum
      simpa [eval_sum_mul] using hz
    -- hmm: eval_sum_mul directly gives eval (Σ C(lam)qrow) = Σ lam·(qrow.eval); use it:
    simpa [Polynomial.eval_mul] using hz1
  by_cases hri : cp.σ i = i
  · -- real root: evaluate at α i
    have he := hev i
    let f : Fin n → ℂ := fun j => lam j * (qrow Q α cp.σ j).eval (α i)
    have hvan : ∀ j : Fin n, j ≠ i → f j = 0 := by
      intro j hj
      have hz : (qrow Q α cp.σ j).eval (α i) = 0 := by
        refine qrow_eval_zero_of_out Q α hfac cp.σ ?_ ?_
        · exact hj.symm
        · intro h
          apply hj
          calc
            j = cp.σ (cp.σ j) := (cp.hσ2 j).symm
            _ = cp.σ i := by rw [h]
            _ = i := hri
      simp [f, hz]
    have hs : (∑ j : Fin n, f j) = f i :=
      Finset.sum_eq_single (s := (Finset.univ : Finset (Fin n))) (f := f) i
        (by intro b hb hbi; exact hvan b hbi)
        (by intro hni; exact False.elim (hni (Finset.mem_univ i)))
    have hfi : f i = 0 := by
      rw [← hs]
      exact he
    have hρ : (qDiv Q (α i)).eval (α i) ≠ 0 := qDiv_eval_self_ne_zero Q α hQ0 hαinj hfac i
    have heq : lam i * (qDiv Q (α i)).eval (α i) = 0 := by
      simpa [f, qrow_eval_real_self Q α hfac cp.σ hri] using hfi
    exact (mul_eq_zero.mp heq).resolve_right hρ
  · -- non-real root: its orbit is a pair
    have hne : cp.σ i ≠ i := hri
    have htri : i < cp.σ i ∨ cp.σ i < i := lt_or_gt_of_ne hne.symm
    rcases htri with hord | hgt
    · have hz := qrow_pair_zero_lt Q hQ0 α hαinj hfac cp (lam := lam) hord (hev i) (hev (cp.σ i))
      exact hz.1
    · -- apply the pair lemma to the index σ i (which is < σ(σ i) = i)
      have hord' : cp.σ i < cp.σ (cp.σ i) := by
        simpa [cp.hσ2 i] using hgt
      have hz := qrow_pair_zero_lt Q hQ0 α hαinj hfac cp (lam := lam) hord'
        (hev (cp.σ i)) (hev (cp.σ (cp.σ i)))
      -- hz : lam (σ i) = 0 ∧ lam (σ (σ i)) = 0 ; σ(σ i) = i
      simpa [cp.hσ2 i] using hz.2


/-- A real linear relation among the rows forces all coefficients to vanish. -/
lemma qrowMat_rows_zero_of_sum (Q : Polynomial ℤ) {n : ℕ} (hQ0 : Q ≠ 0)
    (α : Fin n → ℂ) (hαinj : Function.Injective α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (cp : ConjPair α) :
    ∀ t : Fin n → ℝ, (∑ i : Fin n, t i • (qrowMat Q α cp.σ) i) = 0 → ∀ i, t i = 0 := by
  classical
  intro t ht i
  have hpoly : (∑ j : Fin n, Polynomial.C ((t j : ℂ)) * qrow Q α cp.σ j) = 0 := by
    apply Polynomial.ext
    intro m
    by_cases hm : m < n
    · let j0 : Fin n := ⟨m, hm⟩
      have hmv : j0.val = m := rfl
      have hc : ∀ j : Fin n, (qrow Q α cp.σ j).coeff m = (((qrowMat Q α cp.σ) j j0 : ℝ) : ℂ) := by
        intro j
        dsimp [qrowMat]
        rw [hmv]
        exact qrow_coeff_re Q α cp hfac j m
      have hcv : (∑ j : Fin n, (t j : ℝ) * ((qrowMat Q α cp.σ) j j0 : ℝ)) = 0 := by
        have hv := congrArg (fun v : Fin n → ℝ => v j0) ht
        simpa using hv
      have hcast : (∑ j : Fin n, (t j : ℂ) * (qrow Q α cp.σ j).coeff m)
          = ((∑ j : Fin n, (t j : ℝ) * ((qrowMat Q α cp.σ) j j0 : ℝ)) : ℂ) := by
          calc
            (∑ j : Fin n, (t j : ℂ) * (qrow Q α cp.σ j).coeff m)
                = ∑ j : Fin n, (t j : ℂ) * (((qrowMat Q α cp.σ) j j0 : ℝ) : ℂ) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    rw [hc j]
            _ = ((∑ j : Fin n, (t j : ℝ) * ((qrowMat Q α cp.σ) j j0 : ℝ)) : ℂ) := by
                    simpa using (map_sum (algebraMap ℝ ℂ)
                      (fun j : Fin n => (t j : ℝ) * ((qrowMat Q α cp.σ) j j0 : ℝ)) Finset.univ)
      have hcast : (∑ j : Fin n, (t j : ℂ) * (qrow Q α cp.σ j).coeff m)
          = ((∑ j : Fin n, (t j : ℝ) * ((qrowMat Q α cp.σ) j j0 : ℝ)) : ℂ) := by
          calc
            (∑ j : Fin n, (t j : ℂ) * (qrow Q α cp.σ j).coeff m)
                = ∑ j : Fin n, (t j : ℂ) * (((qrowMat Q α cp.σ) j j0 : ℝ) : ℂ) := by
                    apply Finset.sum_congr rfl
                    intro j hj
                    rw [hc j]
            _ = ((∑ j : Fin n, (t j : ℝ) * ((qrowMat Q α cp.σ) j j0 : ℝ)) : ℂ) := by
                    simpa using (map_sum (algebraMap ℝ ℂ)
                      (fun j : Fin n => (t j : ℝ) * ((qrowMat Q α cp.σ) j j0 : ℝ)) Finset.univ)
      have hzero_coeff' : (∑ j : Fin n, (t j : ℂ) * (qrow Q α cp.σ j).coeff m) = 0 := by
        calc
          (∑ j : Fin n, (t j : ℂ) * (qrow Q α cp.σ j).coeff m)
              = ((∑ j : Fin n, (t j : ℝ) * ((qrowMat Q α cp.σ) j j0 : ℝ)) : ℂ) := hcast
          _ = 0 := by simpa using congrArg (fun x : ℝ => (x : ℂ)) hcv
      have hzero_coeff : (∑ j : Fin n, Polynomial.C ((t j : ℂ)) * qrow Q α cp.σ j).coeff m = 0 := by
        rw [coeff_fintype_sum]
        simpa [Polynomial.coeff_C_mul] using hzero_coeff'
      simpa using hzero_coeff
    · have hmge : n ≤ m := le_of_not_gt hm
      rw [coeff_fintype_sum]
      have hz : ∀ j : Fin n, (qrow Q α cp.σ j).coeff m = 0 := by
        intro j
        have hd : (qrow Q α cp.σ j).natDegree ≤ n - 1 := qrow_natDegree_le Q hQ0 α hfac cp.σ j
        have hn1 : 1 ≤ n := by
          exact lt_of_lt_of_le (lt_of_le_of_lt (Nat.zero_le j.val) j.isLt) (Nat.le_refl n)
        have hnlt : n - 1 < m := by omega
        exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hd hnlt)
      simp [Polynomial.coeff_C_mul, hz]
  have hli := qrow_linearIndependent_poly Q hQ0 α hαinj hfac cp (fun j => (t j : ℂ)) hpoly
  have hti : (t i : ℂ) = 0 := hli i
  exact Complex.ofReal_eq_zero.mp hti

/-- The row matrix is nonsingular. -/
lemma qrowMat_det_ne_zero (Q : Polynomial ℤ) {n : ℕ} (hQ0 : Q ≠ 0)
    (α : Fin n → ℂ) (hαinj : Function.Injective α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (cp : ConjPair α) : (qrowMat Q α cp.σ).det ≠ 0 := by
  classical
  have hrows : LinearIndependent ℝ (fun i : Fin n => (qrowMat Q α cp.σ) i) := by
    rw [Fintype.linearIndependent_iffₛ]
    intro f g hfg
    have hsub : (∑ i, (f i - g i) • (qrowMat Q α cp.σ) i) = 0 := by
      calc
        (∑ i : Fin n, (f i - g i) • (qrowMat Q α cp.σ) i)
            = (∑ i : Fin n, f i • (qrowMat Q α cp.σ) i)
                - ∑ i : Fin n, g i • (qrowMat Q α cp.σ) i := by
                  calc
                    (∑ i : Fin n, (f i - g i) • (qrowMat Q α cp.σ) i)
                        = ∑ i : Fin n, (f i • (qrowMat Q α cp.σ) i - g i • (qrowMat Q α cp.σ) i) := by
                            apply Finset.sum_congr rfl
                            intro i hi
                            simp [sub_smul]
                    _ = (∑ i : Fin n, f i • (qrowMat Q α cp.σ) i)
                        - ∑ i : Fin n, g i • (qrowMat Q α cp.σ) i := by
                            rw [Finset.sum_sub_distrib]
        _ = 0 := by rw [hfg]; simp
    have hzero := qrowMat_rows_zero_of_sum Q hQ0 α hαinj hfac cp (fun i => f i - g i) hsub
    intro i
    have hd : f i - g i = 0 := hzero i
    linarith
  have hcols : LinearIndependent ℝ (fun i : Fin n => (qrowMat Q α cp.σ).transpose.col i) := by
    simpa [Matrix.col] using hrows
  have hns : (qrowMat Q α cp.σ).transpose.Nonsingular :=
    Matrix.Nonsingular.of_linearIndependent_col hcols
  have hdetT : (qrowMat Q α cp.σ).transpose.det ≠ 0 := by
    exact (Matrix.nonsingular_iff_det_ne_zero).mp hns
  simpa using hdetT


/-- The dual evaluation `Σ_j d_j · coeff j (qDiv (α i))`. -/
noncomputable def qdotVal {n : ℕ} (Q : Polynomial ℤ) (α : Fin n → ℂ) (d : Fin n → ℤ)
    (i : Fin n) : ℂ :=
  ∑ j : Fin n, ((d j : ℂ) * (qDiv Q (α i)).coeff j.val)

/-- The dual evaluation of a row. -/
noncomputable def rdotVal {n : ℕ} (Q : Polynomial ℤ) (α : Fin n → ℂ) (cp : ConjPair α)
    (d : Fin n → ℤ) (i : Fin n) : ℂ :=
  ∑ j : Fin n, ((d j : ℂ) * (qrow Q α cp.σ i).coeff j.val)

lemma cvalc_eq_qdot (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (d : Fin n → ℤ) (i : Fin n) :
    cvalc Q α d i = qdotVal Q α d i := by
  unfold cvalc qdotVal
  apply Finset.sum_congr rfl
  intro j hj
  rw [qDiv_eq_qic Q α hfac i]
  rw [Polynomial.coeff_C_mul (qic α i)]

/-- `d_j` are real: conjugation commutes with the dot. -/
lemma qdot_sigma (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ) (cp : ConjPair α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (d : Fin n → ℤ) (i : Fin n) :
    qdotVal Q α d (cp.σ i) = (starRingEnd ℂ) (qdotVal Q α d i) := by
  unfold qdotVal
  calc
    (∑ j : Fin n, (d j : ℂ) * (qDiv Q (α (cp.σ i))).coeff j.val)
        = ∑ j : Fin n, (d j : ℂ) * (starRingEnd ℂ) ((qDiv Q (α i)).coeff j.val) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hq := conjPoly_qDiv Q α cp hfac i
            have hc := congrArg (fun P : Polynomial ℂ => P.coeff j.val) hq
            unfold conjPoly at hc
            rw [Polynomial.coeff_map] at hc
            rw [hc]
    _ = (starRingEnd ℂ) (∑ j : Fin n, (d j : ℂ) * (qDiv Q (α i)).coeff j.val) := by
            calc
              (∑ j : Fin n, (d j : ℂ) * (starRingEnd ℂ) ((qDiv Q (α i)).coeff j.val))
                  = ∑ j : Fin n, (starRingEnd ℂ) ((d j : ℂ) * (qDiv Q (α i)).coeff j.val) := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      simp
              _ = (starRingEnd ℂ) (∑ j : Fin n, (d j : ℂ) * (qDiv Q (α i)).coeff j.val) := by
                      simpa using (map_sum (starRingEnd ℂ)
                        (fun j : Fin n => (d j : ℂ) * (qDiv Q (α i)).coeff j.val) Finset.univ).symm

lemma rdot_eq_real_cast (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ) (cp : ConjPair α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (d : Fin n → ℤ) (i : Fin n) :
    rdotVal Q α cp d i =
      ((∑ j : Fin n, (qrowMat Q α cp.σ) i j * (d j : ℝ)) : ℂ) := by
  unfold rdotVal
  calc
    (∑ j : Fin n, (d j : ℂ) * (qrow Q α cp.σ i).coeff j.val)
        = ∑ j : Fin n, (d j : ℂ) * (((qrowMat Q α cp.σ) i j : ℝ) : ℂ) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hre := qrow_coeff_re Q α cp hfac i j.val
            rw [hre]
            simp [qrowMat]
    _ = ((∑ j : Fin n, (qrowMat Q α cp.σ) i j * (d j : ℝ)) : ℂ) := by
            trans ∑ j : Fin n, (((qrowMat Q α cp.σ) i j * (d j : ℝ) : ℝ) : ℂ)
            · apply Finset.sum_congr rfl
              intro j hj
              simp [mul_comm]
            · simpa using (map_sum (algebraMap ℝ ℂ)
                (fun j : Fin n => (qrowMat Q α cp.σ) i j * (d j : ℝ)) Finset.univ).symm

lemma qrow_eq_qDiv_of_real (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ)
    (cp : ConjPair α) {i : Fin n} (hi : cp.σ i = i) :
    qrow Q α cp.σ i = qDiv Q (α i) := by
  unfold qrow rowPoly
  rw [if_pos hi]

lemma rdot_eq_qdot_of_real (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ) (cp : ConjPair α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (d : Fin n → ℤ) {i : Fin n} (hi : cp.σ i = i) :
    rdotVal Q α cp d i = qdotVal Q α d i := by
  unfold rdotVal qdotVal
  apply Finset.sum_congr rfl
  intro j hj
  rw [qrow_eq_qDiv_of_real Q α cp hi]

/-- For `i < σ i` the row at `i` is the sum of the two quotients. -/
lemma qrow_lt_add (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ) (cp : ConjPair α)
    {i : Fin n} (hord : i < cp.σ i) :
    qrow Q α cp.σ i = qDiv Q (α i) + qDiv Q (α (cp.σ i)) := by
  classical
  unfold qrow rowPoly
  have h1 : ¬ cp.σ i = i := by
    intro h
    exact (ne_of_lt hord) h.symm
  rw [if_neg h1, if_pos hord]

/-- For `i < σ i` the row at `σ i` is `I·(q_{σ i} − q_i)`. -/
lemma qrow_lt_sigma_sub (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ) (cp : ConjPair α)
    {i : Fin n} (hord : i < cp.σ i) :
    qrow Q α cp.σ (cp.σ i) = Polynomial.C Complex.I * (qDiv Q (α (cp.σ i)) - qDiv Q (α i)) := by
  classical
  unfold qrow rowPoly
  have h1 : ¬ cp.σ (cp.σ i) = cp.σ i := by
    intro h
    exact (ne_of_lt hord) (cp.σ_bijective.1 h.symm)
  have h3 : ¬ cp.σ i < cp.σ (cp.σ i) := by
    intro h
    have : cp.σ i < i := by simpa [cp.hσ2 i] using h
    exact lt_asymm hord this
  rw [if_neg h1, if_neg h3, cp.hσ2 i]

lemma rdot_sum_of_lt (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ) (cp : ConjPair α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (d : Fin n → ℤ) {i : Fin n} (hord : i < cp.σ i) :
    rdotVal Q α cp d i = qdotVal Q α d i + qdotVal Q α d (cp.σ i) := by
  unfold rdotVal qdotVal
  calc
    (∑ j : Fin n, (d j : ℂ) * (qrow Q α cp.σ i).coeff j.val)
        = (∑ j : Fin n, (d j : ℂ) * (qDiv Q (α i) + qDiv Q (α (cp.σ i))).coeff j.val) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [qrow_lt_add Q α cp hord]
    _ = (∑ j : Fin n, (d j : ℂ) * ((qDiv Q (α i)).coeff j.val + (qDiv Q (α (cp.σ i))).coeff j.val)) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Polynomial.coeff_add]
    _ = (∑ j : Fin n, (d j : ℂ) * (qDiv Q (α i)).coeff j.val)
        + ∑ j : Fin n, (d j : ℂ) * (qDiv Q (α (cp.σ i))).coeff j.val := by
            trans ∑ j : Fin n, ((d j : ℂ) * (qDiv Q (α i)).coeff j.val
                + (d j : ℂ) * (qDiv Q (α (cp.σ i))).coeff j.val)
            · apply Finset.sum_congr rfl
              intro j hj
              ring
            · rw [Finset.sum_add_distrib]

lemma rdot_sigma_sub_of_lt (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ) (cp : ConjPair α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (d : Fin n → ℤ) {i : Fin n} (hord : i < cp.σ i) :
    rdotVal Q α cp d (cp.σ i) = Complex.I * (qdotVal Q α d (cp.σ i) - qdotVal Q α d i) := by
  unfold rdotVal qdotVal
  calc
    (∑ j : Fin n, (d j : ℂ) * (qrow Q α cp.σ (cp.σ i)).coeff j.val)
        = (∑ j : Fin n, (d j : ℂ) * (Polynomial.C Complex.I * (qDiv Q (α (cp.σ i)) - qDiv Q (α i))).coeff j.val) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [qrow_lt_sigma_sub Q α cp hord]
    _ = (∑ j : Fin n, (d j : ℂ) * (Complex.I * ((qDiv Q (α (cp.σ i))).coeff j.val - (qDiv Q (α i)).coeff j.val))) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Polynomial.coeff_C_mul (qDiv Q (α (cp.σ i)) - qDiv Q (α i))]
            rw [Polynomial.coeff_sub]
    _ = Complex.I * (∑ j : Fin n, (d j : ℂ) * (qDiv Q (α (cp.σ i))).coeff j.val
        - ∑ j : Fin n, (d j : ℂ) * (qDiv Q (α i)).coeff j.val) := by
            calc
              (∑ j : Fin n, (d j : ℂ) * (Complex.I * ((qDiv Q (α (cp.σ i))).coeff j.val - (qDiv Q (α i)).coeff j.val)))
                  = ∑ j : Fin n, Complex.I * ((d j : ℂ) * ((qDiv Q (α (cp.σ i))).coeff j.val - (qDiv Q (α i)).coeff j.val)) := by
                      apply Finset.sum_congr rfl
                      intro j hj
                      ring
              _ = Complex.I * (∑ j : Fin n, (d j : ℂ) * ((qDiv Q (α (cp.σ i))).coeff j.val - (qDiv Q (α i)).coeff j.val)) := by
                      rw [Finset.mul_sum]
              _ = Complex.I * ((∑ j : Fin n, (d j : ℂ) * (qDiv Q (α (cp.σ i))).coeff j.val)
                  - ∑ j : Fin n, (d j : ℂ) * (qDiv Q (α i)).coeff j.val) := by
                      apply congrArg (fun x : ℂ => Complex.I * x)
                      calc
                        (∑ j : Fin n, (d j : ℂ) * ((qDiv Q (α (cp.σ i))).coeff j.val - (qDiv Q (α i)).coeff j.val))
                            = ∑ j : Fin n, ((d j : ℂ) * (qDiv Q (α (cp.σ i))).coeff j.val
                                - (d j : ℂ) * (qDiv Q (α i)).coeff j.val) := by
                                apply Finset.sum_congr rfl
                                intro j hj
                                ring
                        _ = (∑ j : Fin n, (d j : ℂ) * (qDiv Q (α (cp.σ i))).coeff j.val)
                            - ∑ j : Fin n, (d j : ℂ) * (qDiv Q (α i)).coeff j.val := by
                                rw [Finset.sum_sub_distrib]

lemma add_conj_re (v : ℂ) : v + (starRingEnd ℂ) v = ((2 * v.re : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [Complex.conj_re]
    try ring
  · simp [Complex.conj_im]
    try ring

lemma I_sub_conj_im (v : ℂ) : Complex.I * ((starRingEnd ℂ) v - v) = ((2 * v.im : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [Complex.conj_re, Complex.conj_im]
    try ring
  · simp [Complex.conj_re, Complex.conj_im]
    try ring

lemma real_abs_two {x : ℝ} (h : (1 / 2 : ℝ) ≤ |x|) : (1 : ℝ) ≤ |2 * x| := by
  have htwo : (1 : ℝ) ≤ 2 * |x| := by nlinarith [h]
  rw [abs_mul, abs_of_pos]
  · simpa using htwo
  · norm_num

lemma re_or_im_abs_ge_half {v : ℂ} (hv : 1 ≤ ‖v‖) :
    (1 / 2 : ℝ) ≤ |v.re| ∨ (1 / 2 : ℝ) ≤ |v.im| := by
  by_contra h
  push_neg at h
  have h1 : v.re ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    have hlt : |v.re| < (1 / 2 : ℝ) := h.1
    exact (sq_lt_sq.mpr (by simpa using hlt))
  have h2 : v.im ^ 2 < (1 / 2 : ℝ) ^ 2 := by
    have hlt : |v.im| < (1 / 2 : ℝ) := h.2
    exact (sq_lt_sq.mpr (by simpa using hlt))
  have hsq : v.re * v.re + v.im * v.im < 1 := by
    nlinarith [h1, h2]
  have hnormSq : Complex.normSq v < 1 := by
    rw [Complex.normSq_apply]
    exact hsq
  have hnorm : ‖v‖ ^ 2 < 1 := by
    rw [Complex.normSq_eq_norm_sq] at hnormSq
    exact hnormSq
  have hge : 1 ≤ ‖v‖ ^ 2 := by
    have hpos : 0 ≤ ‖v‖ := norm_nonneg v
    have hm : (1 : ℝ) * 1 ≤ ‖v‖ * ‖v‖ := mul_le_mul hv hv (by norm_num) hpos
    simpa [pow_two] using hm
  nlinarith

/-- from `1 ≤ ‖v‖` (v := the quotient-dot at `i`) and the row dots, one of the
two rows of the pair sees `d`. -/
lemma dual_row_of_pair_lt (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ) (cp : ConjPair α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (d : Fin n → ℤ) (hd : d ≠ 0) {i : Fin n} (hord : i < cp.σ i)
    (hv : 1 ≤ ‖qdotVal Q α d i‖) :
    (1 : ℝ) ≤ ‖rdotVal Q α cp d i‖ ∨ (1 : ℝ) ≤ ‖rdotVal Q α cp d (cp.σ i)‖ := by
  have hreim := re_or_im_abs_ge_half (v := qdotVal Q α d i) hv
  rcases hreim with hre | him
  · left
    have hvsum : rdotVal Q α cp d i = qdotVal Q α d i + qdotVal Q α d (cp.σ i) :=
      rdot_sum_of_lt Q α cp hfac d hord
    have hconj : qdotVal Q α d (cp.σ i) = (starRingEnd ℂ) (qdotVal Q α d i) :=
      qdot_sigma Q α cp hfac d i
    have hval : rdotVal Q α cp d i = ((2 * (qdotVal Q α d i).re : ℝ) : ℂ) := by
      calc
        rdotVal Q α cp d i = qdotVal Q α d i + qdotVal Q α d (cp.σ i) := hvsum
        _ = qdotVal Q α d i + (starRingEnd ℂ) (qdotVal Q α d i) := by rw [hconj]
        _ = ((2 * (qdotVal Q α d i).re : ℝ) : ℂ) := add_conj_re _
    have hnorm : ‖rdotVal Q α cp d i‖ = |2 * (qdotVal Q α d i).re| := by
      rw [hval]
      exact Cwnorm.norm_ofReal (2 * (qdotVal Q α d i).re)
    rw [hnorm]
    exact real_abs_two hre
  · right
    have hvsum : rdotVal Q α cp d (cp.σ i) =
        Complex.I * (qdotVal Q α d (cp.σ i) - qdotVal Q α d i) :=
      rdot_sigma_sub_of_lt Q α cp hfac d hord
    have hconj : qdotVal Q α d (cp.σ i) = (starRingEnd ℂ) (qdotVal Q α d i) :=
      qdot_sigma Q α cp hfac d i
    have hval : rdotVal Q α cp d (cp.σ i) = ((2 * (qdotVal Q α d i).im : ℝ) : ℂ) := by
      calc
        rdotVal Q α cp d (cp.σ i)
            = Complex.I * (qdotVal Q α d (cp.σ i) - qdotVal Q α d i) := hvsum
        _ = Complex.I * ((starRingEnd ℂ) (qdotVal Q α d i) - qdotVal Q α d i) := by rw [hconj]
        _ = ((2 * (qdotVal Q α d i).im : ℝ) : ℂ) := I_sub_conj_im _
    have hnorm : ‖rdotVal Q α cp d (cp.σ i)‖ = |2 * (qdotVal Q α d i).im| := by
      rw [hval]
      exact Cwnorm.norm_ofReal (2 * (qdotVal Q α d i).im)
    rw [hnorm]
    exact real_abs_two him

/-- The complex row-dot has modulus equal to the real row-dot. -/
lemma rdot_norm_eq_abs (Q : Polynomial ℤ) {n : ℕ} (α : Fin n → ℂ) (cp : ConjPair α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (d : Fin n → ℤ) (i : Fin n) :
    ‖rdotVal Q α cp d i‖ =
      |∑ j : Fin n, (qrowMat Q α cp.σ) i j * (d j : ℝ)| := by
  let realdot : ℝ := ∑ j : Fin n, (qrowMat Q α cp.σ) i j * (d j : ℝ)
  have hEq : (realdot : ℂ) = rdotVal Q α cp d i := by
    dsimp [realdot]
    simpa using (rdot_eq_real_cast Q α cp hfac d i).symm
  calc
    ‖rdotVal Q α cp d i‖ = ‖(realdot : ℂ)‖ := by rw [← hEq]
    _ = |realdot| := Cwnorm.norm_ofReal realdot

lemma qrowMat_dual_condition (Q : Polynomial ℤ) {n : ℕ} (hn : 1 ≤ n) (hQ0 : Q ≠ 0)
    (hQn : Q.natDegree = n) (α : Fin n → ℂ) (hαinj : Function.Injective α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (cp : ConjPair α) :
    ∀ d : Fin n → ℤ, d ≠ 0 →
      ∃ i : Fin n, (1 : ℝ) ≤ |∑ j : Fin n, (qrowMat Q α cp.σ) i j * (d j : ℝ)| := by
  classical
  intro d hd
  have hgen := general_dual hn Q hQ0 hQn α hαinj hfac d hd
  rcases hgen with ⟨i0, hi0⟩
  have hv : 1 ≤ ‖qdotVal Q α d i0‖ := by
    have hi0' : 1 ≤ ‖cvalc Q α d i0‖ := hi0
    rw [cvalc_eq_qdot Q α hfac d i0] at hi0'
    exact hi0' 
  by_cases hreal : cp.σ i0 = i0
  · -- real root: the row at i0 is q_{i0}
    refine ⟨i0, ?_⟩
    have hn : ‖rdotVal Q α cp d i0‖ = ‖qdotVal Q α d i0‖ := by
      rw [rdot_eq_qdot_of_real Q α cp hfac d hreal]
    rw [← rdot_norm_eq_abs Q α cp hfac d i0]
    rw [hn]
    exact hv
  · -- non-real: use the pair
    have hne : cp.σ i0 ≠ i0 := hreal
    have htri := lt_or_gt_of_ne hne.symm
    rcases htri with hlt | hgt
    · have hz := dual_row_of_pair_lt Q α cp hfac d hd hlt hv
      rcases hz with hl | hr
      · refine ⟨i0, ?_⟩
        rw [← rdot_norm_eq_abs Q α cp hfac d i0]
        exact hl
      · refine ⟨cp.σ i0, ?_⟩
        rw [← rdot_norm_eq_abs Q α cp hfac d (cp.σ i0)]
        exact hr
    · -- σ i0 < i0
      have hord' : cp.σ i0 < cp.σ (cp.σ i0) := by
        simpa [cp.hσ2 i0] using hgt
      have hv' : 1 ≤ ‖qdotVal Q α d (cp.σ i0)‖ := by
        have hq := qdot_sigma Q α cp hfac d i0
        have hnorm : ‖(starRingEnd ℂ) (qdotVal Q α d i0)‖ = ‖qdotVal Q α d i0‖ := by
          simp
        rw [hq]
        simpa [hnorm] using hv
      have hz := dual_row_of_pair_lt Q α cp hfac d hd hord' hv'
      rcases hz with hl | hr
      · refine ⟨cp.σ i0, ?_⟩
        rw [← rdot_norm_eq_abs Q α cp hfac d (cp.σ i0)]
        exact hl
      · refine ⟨i0, ?_⟩
        rw [← rdot_norm_eq_abs Q α cp hfac d i0]
        simpa [cp.hσ2 i0] using hr

end Indep


/-! ## Lattice covering and the assembly -/

section Cover

lemma cast_sum_into {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    ((∑ i : ι, a i : ℝ) : ℂ) = ∑ i : ι, (a i : ℂ) := by
  simpa using (map_sum (algebraMap ℝ ℂ) a Finset.univ)

lemma sum_swap {ι κ : Type*} [Fintype ι] [Fintype κ] (a : ι → κ → ℂ) :
    (∑ k : κ, ∑ i : ι, a i k) = ∑ i : ι, ∑ k : κ, a i k := by
  calc
    (∑ k : κ, ∑ i : ι, a i k) = ∑ k ∈ (Finset.univ : Finset κ), ∑ i ∈ (Finset.univ : Finset ι), a i k := rfl
    _ = ∑ i ∈ (Finset.univ : Finset ι), ∑ k ∈ (Finset.univ : Finset κ), a i k := by
        rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ k : κ, a i k := rfl

lemma sum_swap_r {ι κ : Type*} [Fintype ι] [Fintype κ] (a : ι → κ → ℝ) :
    (∑ k : κ, ∑ i : ι, a i k) = ∑ i : ι, ∑ k : κ, a i k := by
  calc
    (∑ k : κ, ∑ i : ι, a i k) = ∑ k ∈ (Finset.univ : Finset κ), ∑ i ∈ (Finset.univ : Finset ι), a i k := rfl
    _ = ∑ i ∈ (Finset.univ : Finset ι), ∑ k ∈ (Finset.univ : Finset κ), a i k := by
        rw [Finset.sum_comm]
    _ = ∑ i : ι, ∑ k : κ, a i k := rfl

lemma norm_sum_bound {ι : Type*} [Fintype ι] (f : ι → ℂ) :
    ‖∑ i : ι, f i‖ ≤ ∑ i : ι, ‖f i‖ := by
  simpa using (norm_sum_le (s := (Finset.univ : Finset ι)) f)


lemma covering_real (Q : Polynomial ℤ) {n : ℕ} (hn : 1 ≤ n) (hQ0 : Q ≠ 0)
    (hQn : Q.natDegree = n) (α : Fin n → ℂ) (hαinj : Function.Injective α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (cp : ConjPair α) :
    ∀ p : Fin n → ℝ, ∃ (r : Fin n → ℤ) (β : Fin n → ℝ),
      (∀ j : Fin n, (∑ i : Fin n, β i * (qrowMat Q α cp.σ) i j) = p j - (r j : ℝ)) ∧
      (∑ i : Fin n, |β i|) ≤ (n : ℝ) ^ (100 : ℝ) := by
  classical
  let B : Matrix (Fin n) (Fin n) ℝ := qrowMat Q α cp.σ
  have hB : B.det ≠ 0 := by
    dsimp [B]
    exact qrowMat_det_ne_zero Q hQ0 α hαinj hfac cp
  have hdual : CoverLemma.DualCondition B := by
    intro d hd
    have hd' := qrowMat_dual_condition Q hn hQ0 hQn α hαinj hfac cp d hd
    rcases hd' with ⟨i, hi⟩
    exact ⟨i, hi⟩
  rcases (Submission.GeoCore.geo_core n hn B hB hdual) with ⟨C0, hC0pos, hC0le, hcover⟩
  intro p
  rcases hcover p with ⟨β, hz, hβ⟩
  let r : Fin n → ℤ := fun i => Classical.choose (hz i)
  refine ⟨r, β, ?_, ?_⟩
  · intro j
    have hspec := Classical.choose_spec (hz j)
    have hS : (∑ i : Fin n, β i * B i j) = (∑ i : Fin n, B i j * β i) := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [hS]
    change (∑ i : Fin n, B i j * β i) = p j - (↑(Classical.choose (hz j) : ℤ) : ℝ)
    linarith
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hmono : (n : ℝ) ^ C0 ≤ (n : ℝ) ^ (100 : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le hn1 hC0le
    exact le_trans hβ hmono

/-- Covering in the quotient basis, with the conversion of real rows into the
complex quotients. -/
lemma covering_qbasis (Q : Polynomial ℤ) {n : ℕ} (hn : 1 ≤ n) (hQ0 : Q ≠ 0)
    (hQn : Q.natDegree = n) (α : Fin n → ℂ) (hαinj : Function.Injective α)
    (hfac : Q.map (algebraMap ℤ ℂ) =
      Polynomial.C ((Q.leadingCoeff : ℂ)) * ∏ i : Fin n, (X - Polynomial.C (α i)))
    (cp : ConjPair α) :
    ∀ p : Fin n → ℝ, ∃ (r : Fin n → ℤ) (γ : Fin n → ℂ),
      (∀ j : Fin n, ((p j - (r j : ℝ)) : ℂ) =
          ∑ i : Fin n, γ i * (qDiv Q (α i)).coeff j.val) ∧
      (∑ i : Fin n, ‖γ i‖) ≤ 2 * (n : ℝ) ^ (100 : ℝ) := by
  classical
  intro p
  rcases covering_real Q hn hQ0 hQn α hαinj hfac cp p with ⟨r, β, hcov, hβ⟩
  let γ : Fin n → ℂ := fun k => ∑ i : Fin n, (β i : ℂ) * qcoef cp.σ i k
  refine ⟨r, γ, ?_, ?_⟩
  · intro j
    -- 1) complexify the real covering identity
    have hc := congrArg (fun x : ℝ => (x : ℂ)) (hcov j)
    have hcastsum : ((∑ i : Fin n, β i * ((qrowMat Q α cp.σ) i j : ℝ)) : ℂ)
        = ∑ i : Fin n, (β i : ℂ) * (((qrowMat Q α cp.σ) i j : ℝ) : ℂ) := by
          simpa using (map_sum (algebraMap ℝ ℂ)
            (fun i : Fin n => β i * ((qrowMat Q α cp.σ) i j : ℝ)) Finset.univ).symm
    have hmain : ((p j - (r j : ℝ)) : ℂ)
        = ∑ i : Fin n, (β i : ℂ) * (qrow Q α cp.σ i).coeff j.val := by
          calc
            ((p j - (r j : ℝ)) : ℂ)
                = ((∑ i : Fin n, β i * ((qrowMat Q α cp.σ) i j : ℝ)) : ℂ) := by
                    simpa using hc.symm
            _ = ∑ i : Fin n, (β i : ℂ) * (((qrowMat Q α cp.σ) i j : ℝ) : ℂ) := hcastsum
            _ = ∑ i : Fin n, (β i : ℂ) * (qrow Q α cp.σ i).coeff j.val := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    congr 1
                    have hre := qrow_coeff_re Q α cp hfac i j.val
                    rw [hre]
                    simp [qrowMat]
    -- 2) the rows are q-combinations: coefficient identity of the γ-expansion
    have hrows : ∀ i : Fin n, (qrow Q α cp.σ i).coeff j.val
        = ∑ k : Fin n, qcoef cp.σ i k * (qDiv Q (α k)).coeff j.val :=
        fun i => qrow_coeff_eq_qcoef_sum Q α cp.σ i j.val
    calc
      ((p j - (r j : ℝ)) : ℂ)
          = ∑ i : Fin n, (β i : ℂ) * (qrow Q α cp.σ i).coeff j.val := hmain
      _ = ∑ i : Fin n, (β i : ℂ) * (∑ k : Fin n, qcoef cp.σ i k * (qDiv Q (α k)).coeff j.val) := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [hrows i]
      _ = ∑ k : Fin n, (∑ i : Fin n, (β i : ℂ) * qcoef cp.σ i k) * (qDiv Q (α k)).coeff j.val := by
              calc
                (∑ i : Fin n, (β i : ℂ) * (∑ k : Fin n, qcoef cp.σ i k * (qDiv Q (α k)).coeff j.val))
                    = ∑ i : Fin n, (∑ k : Fin n, (β i : ℂ) * qcoef cp.σ i k * (qDiv Q (α k)).coeff j.val) := by
                        apply Finset.sum_congr rfl
                        intro i hi
                        rw [Finset.mul_sum]
                        apply Finset.sum_congr rfl
                        intro k hk
                        ring
                _ = ∑ k : Fin n, (∑ i : Fin n, (β i : ℂ) * qcoef cp.σ i k * (qDiv Q (α k)).coeff j.val) := by
                        rw [sum_swap (fun (i k : Fin n) => (β i : ℂ) * qcoef cp.σ i k * (qDiv Q (α k)).coeff j.val)]
                _ = ∑ k : Fin n, (∑ i : Fin n, (β i : ℂ) * qcoef cp.σ i k) * (qDiv Q (α k)).coeff j.val := by
                        apply Finset.sum_congr rfl
                        intro k hk
                        rw [Finset.sum_mul]
      _ = ∑ i : Fin n, γ i * (qDiv Q (α i)).coeff j.val := by rfl
  · have hbound : (∑ k : Fin n, ‖γ k‖) ≤ 2 * (∑ i : Fin n, |β i|) := by
      calc
        (∑ k : Fin n, ‖γ k‖)
            = ∑ k : Fin n, ‖∑ i : Fin n, (β i : ℂ) * qcoef cp.σ i k‖ := rfl
        _ ≤ ∑ k : Fin n, (∑ i : Fin n, ‖(β i : ℂ) * qcoef cp.σ i k‖) := by
              apply Finset.sum_le_sum
              intro k hk
              exact norm_sum_bound (fun i : Fin n => (β i : ℂ) * qcoef cp.σ i k)
        _ = ∑ i : Fin n, ∑ k : Fin n, ‖(β i : ℂ) * qcoef cp.σ i k‖ := by
              rw [sum_swap_r (fun (i k : Fin n) => ‖(β i : ℂ) * qcoef cp.σ i k‖)]
        _ ≤ ∑ i : Fin n, |β i| * 2 := by
              apply Finset.sum_le_sum
              intro i hi
              calc
                (∑ k : Fin n, ‖(β i : ℂ) * qcoef cp.σ i k‖)
                    ≤ ∑ k : Fin n, ‖(β i : ℂ)‖ * ‖qcoef cp.σ i k‖ := by
                        apply Finset.sum_le_sum
                        intro k hk
                        rw [norm_mul]
                    _ = ∑ k : Fin n, |β i| * ‖qcoef cp.σ i k‖ := by
                        apply Finset.sum_congr rfl
                        intro k hk
                        rw [Cwnorm.norm_ofReal]
                    _ = |β i| * (∑ k : Fin n, ‖qcoef cp.σ i k‖) := by
                        rw [Finset.mul_sum]
                    _ ≤ |β i| * 2 := by
                        exact mul_le_mul_of_nonneg_left (qcoef_sum_norm_le_two cp.σ i) (abs_nonneg (β i))
        _ = 2 * (∑ i : Fin n, |β i|) := by
              rw [← Finset.sum_mul]
              ring
    calc
      (∑ k : Fin n, ‖γ k‖) ≤ 2 * (∑ i : Fin n, |β i|) := hbound
      _ ≤ 2 * (n : ℝ) ^ (100 : ℝ) := by
            exact mul_le_mul_of_nonneg_left hβ (by norm_num)


/-- The integer polynomial with coefficient vector `r` (degree `< n`). -/
noncomputable def intPoly {n : ℕ} (r : Fin n → ℤ) : Polynomial ℤ :=
  ∑ j : Fin n, Polynomial.C (r j) * Polynomial.X ^ (j.val : ℕ)

lemma intPoly_coeff_ge {n : ℕ} (r : Fin n → ℤ) {m : ℕ} (hm : n ≤ m) :
    (intPoly r).coeff m = 0 := by
  classical
  calc
    (intPoly r).coeff m = ∑ j : Fin n, (Polynomial.C (r j) * Polynomial.X ^ (j.val : ℕ)).coeff m := by
      unfold intPoly
      simp
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      rw [Polynomial.coeff_C_mul (Polynomial.X ^ (j.val : ℕ))]
      rw [Polynomial.coeff_X_pow]
      have hmne : m ≠ j.val := by omega
      simp [hmne]

lemma intPoly_coeff_lt {n : ℕ} (r : Fin n → ℤ) (j0 : Fin n) :
    (intPoly r).coeff j0.val = r j0 := by
  classical
  have hterm : ∀ j : Fin n, j ≠ j0 →
      (Polynomial.C (r j) * Polynomial.X ^ (j.val : ℕ)).coeff j0.val = 0 := by
    intro j hj
    have hjv : j.val ≠ j0.val := by
      intro hv
      apply hj
      exact Fin.ext hv
    rw [Polynomial.coeff_C_mul (Polynomial.X ^ (j.val : ℕ))]
    rw [Polynomial.coeff_X_pow]
    have hmne : j0.val ≠ j.val := fun h => hjv h.symm
    simp [hmne]
  have hsum : (∑ j : Fin n, (Polynomial.C (r j) * Polynomial.X ^ (j.val : ℕ)).coeff j0.val)
      = (Polynomial.C (r j0) * Polynomial.X ^ (j0.val : ℕ)).coeff j0.val := by
    exact Finset.sum_eq_single (s := (Finset.univ : Finset (Fin n)))
      (f := fun j : Fin n => (Polynomial.C (r j) * Polynomial.X ^ (j.val : ℕ)).coeff j0.val)
      j0 (by intro b hb hbj; exact hterm b hbj)
      (by intro hj; exact False.elim (hj (Finset.mem_univ j0)))
  calc
    (intPoly r).coeff j0.val = ∑ j : Fin n, (Polynomial.C (r j) * Polynomial.X ^ (j.val : ℕ)).coeff j0.val := by
      unfold intPoly
      simp
    _ = (Polynomial.C (r j0) * Polynomial.X ^ (j0.val : ℕ)).coeff j0.val := hsum
    _ = r j0 := by
      rw [Polynomial.coeff_C_mul (Polynomial.X ^ (j0.val : ℕ))]
      rw [Polynomial.coeff_X_pow]
      simp

lemma intPoly_natDegree {n : ℕ} (hn : 1 ≤ n) (r : Fin n → ℤ) : (intPoly r).natDegree ≤ n - 1 := by
  rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
  intro N hN
  have hge : n ≤ N := by omega
  exact intPoly_coeff_ge r hge

lemma zmap_map_eq (R : Polynomial ℤ) : (zmap R).map (algebraMap ℝ ℂ) = R.map (algebraMap ℤ ℂ) := by
  unfold zmap
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_map, Polynomial.coeff_map]
  norm_num

lemma smul_eq_C_mul {R : Type*} [CommSemiring R] (c : R) (P : Polynomial R) :
    c • P = Polynomial.C c * P := by
  apply Polynomial.ext
  intro n
  rw [Polynomial.coeff_C_mul P]
  simp

lemma poly_eq_of_coeff_fin_eq {n : ℕ} (hn : 1 ≤ n) {P Q : Polynomial ℂ}
    (hP : P.natDegree ≤ n - 1) (hQ : Q.natDegree ≤ n - 1)
    (h : ∀ j : Fin n, P.coeff j.val = Q.coeff j.val) : P = Q := by
  apply Polynomial.ext
  intro m
  by_cases hm : m < n
  · exact h ⟨m, hm⟩
  · have hmge : n ≤ m := le_of_not_gt hm
    have hP0 : P.coeff m = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hP (by omega))
    have hQ0 : Q.coeff m = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hQ (by omega))
    rw [hP0, hQ0]


lemma D_le_sq (n : ℕ) (hn : 2 ≤ n) : ((2 * max n n : ℕ) : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) := by
  have hnn : (2 * max n n : ℕ) = (2 * n : ℕ) := by rw [max_self]
  rw [hnn, Nat.cast_mul]
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have h2 : (2 : ℝ) * (n : ℝ) ≤ (n : ℝ) * (n : ℝ) := mul_le_mul_of_nonneg_right hnR hn0
  rw [Real.rpow_two]
  rw [pow_two]
  exact h2

lemma pow_bound (n : ℕ) (hn : 2 ≤ n) (CR : ℝ) (hCR0 : 0 ≤ CR) :
    2 * (n : ℝ) ^ (100 : ℝ) * ((2 * max n n : ℕ) : ℝ) ^ CR ≤ (n : ℝ) ^ (102 + 2 * CR) := by
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hnpos : 0 < (n : ℝ) := by positivity
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 1 ≤ n)
  have hD : ((2 * max n n : ℕ) : ℝ) ≤ (n : ℝ) ^ (2 : ℝ) := D_le_sq n hn
  have hD0 : 0 ≤ ((2 * max n n : ℕ) : ℝ) := by positivity
  have hDCR : ((2 * max n n : ℕ) : ℝ) ^ CR ≤ (n : ℝ) ^ (2 * CR) := by
    calc
      ((2 * max n n : ℕ) : ℝ) ^ CR ≤ ((n : ℝ) ^ (2 : ℝ)) ^ CR := Real.rpow_le_rpow hD0 hD hCR0
      _ = (n : ℝ) ^ (2 * CR) := by
          rw [Real.rpow_mul hn0 (2 : ℝ) CR]
  have h2n : 2 * (n : ℝ) ^ (100 : ℝ) ≤ (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (100 : ℝ) := by
    exact mul_le_mul_of_nonneg_right
      (by simpa [Real.rpow_one] using (by exact_mod_cast hn : (2 : ℝ) ≤ (n : ℝ)))
      (Real.rpow_nonneg hn0 (100 : ℝ))
  have hmul1 : (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (100 : ℝ) = (n : ℝ) ^ ((1 : ℝ) + (100 : ℝ)) := by
    exact (Real.rpow_add hnpos (1 : ℝ) (100 : ℝ)).symm
  have hmul2 : (n : ℝ) ^ ((1 : ℝ) + (100 : ℝ)) * (n : ℝ) ^ (2 * CR)
      = (n : ℝ) ^ (((1 : ℝ) + 100) + 2 * CR) := by
    exact (Real.rpow_add hnpos ((1 : ℝ) + 100) (2 * CR)).symm
  calc
    2 * (n : ℝ) ^ (100 : ℝ) * ((2 * max n n : ℕ) : ℝ) ^ CR
        ≤ (n : ℝ) ^ (1 : ℝ) * (n : ℝ) ^ (100 : ℝ) * (n : ℝ) ^ (2 * CR) := by
            exact mul_le_mul h2n hDCR (Real.rpow_nonneg hD0 CR) (by positivity)
    _ = (n : ℝ) ^ ((1 : ℝ) + (100 : ℝ)) * (n : ℝ) ^ (2 * CR) := by
            rw [hmul1]
    _ = (n : ℝ) ^ (((1 : ℝ) + 100) + 2 * CR) := by
            rw [hmul2]
    _ ≤ (n : ℝ) ^ (102 + 2 * CR) := by
            exact Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num)

end Cover

/-- The theorem (Smith `thm:adjust` + `cor:adjust`, root-data form). -/
theorem adjust_lemma : ∃ Cadj : ℝ, 0 < Cadj ∧
    ∀ n : ℕ, 2 ≤ n → ∀ (Q : Polynomial ℤ), Q ≠ 0 → Q.natDegree = n →
      ∀ α : Fin n → ℂ, Function.Injective α →
        Q.map (algebraMap ℤ ℂ) =
            Polynomial.C ((Q.leadingCoeff : ℂ)) *
              ∏ i : Fin n, (Polynomial.X - Polynomial.C (α i)) →
          ∀ P : Polynomial ℝ, P.natDegree ≤ n - 1 →
            ∃ (R : Polynomial ℤ) (β : Fin n → ℂ),
              R.natDegree ≤ n - 1 ∧
                (P.map (algebraMap ℝ ℂ) - (zmap R).map (algebraMap ℝ ℂ) =
                  ∑ i : Fin n, β i • qDiv Q (α i)) ∧
                (∑ i : Fin n, ‖β i‖) ≤ (n : ℝ) ^ Cadj ∧
                wnorm n (P - zmap R) ≤ (n : ℝ) ^ Cadj * wnorm n (zmap Q) := by
  classical
  rcases Submission.RemezComplex.complex_remez with ⟨CR, hCRpos, hCRprop⟩
  let Cadj : ℝ := 102 + 2 * CR
  refine ⟨Cadj, ?_, ?_⟩
  · dsimp [Cadj]
    nlinarith [hCRpos]
  · intro n hn2 Q hQ0 hQn α hαinj hfac P hdegP
    have hn : 1 ≤ n := by omega
    have hCR0 : 0 ≤ CR := le_of_lt hCRpos
    let cp : ConjPair α := conjPairOf Q α hQ0 hαinj hfac
    let p : Fin n → ℝ := fun j => P.coeff j.val
    rcases covering_qbasis Q hn hQ0 hQn α hαinj hfac cp p with ⟨r, β, hβcov, hβ1⟩
    let R : Polynomial ℤ := intPoly r
    have hRdeg : R.natDegree ≤ n - 1 := intPoly_natDegree hn r
    -- polynomial identity, coefficient-wise
    have hpoly : P.map (algebraMap ℝ ℂ) - (zmap R).map (algebraMap ℝ ℂ)
        = ∑ i : Fin n, β i • qDiv Q (α i) := by
      apply poly_eq_of_coeff_fin_eq hn
      · -- degree of LHS
        calc
          (P.map (algebraMap ℝ ℂ) - (zmap R).map (algebraMap ℝ ℂ)).natDegree
              ≤ max (P.map (algebraMap ℝ ℂ)).natDegree ((zmap R).map (algebraMap ℝ ℂ)).natDegree :=
                  Polynomial.natDegree_sub_le _ _
          _ ≤ max (n - 1) (n - 1) := by
                have h1 : (P.map (algebraMap ℝ ℂ)).natDegree ≤ n - 1 := by
                  rw [Polynomial.natDegree_map_eq_of_injective (f := algebraMap ℝ ℂ) Complex.ofReal_injective P]
                  exact hdegP
                have h2 : ((zmap R).map (algebraMap ℝ ℂ)).natDegree ≤ n - 1 := by
                  rw [zmap_map_eq R]
                  rw [Polynomial.natDegree_map_eq_of_injective (f := algebraMap ℤ ℂ) Int.cast_injective R]
                  exact hRdeg
                exact max_le (le_trans h1 (le_max_left _ _)) (le_trans h2 (le_max_right _ _))
          _ ≤ n - 1 := by simp
      · -- degree of RHS: coefficients beyond n-1 vanish
        rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
        intro m hm
        have hge : n ≤ m := by omega
        rw [coeff_fintype_sum]
        apply Finset.sum_eq_zero
        intro i hi
        rw [smul_eq_C_mul]
        rw [Polynomial.coeff_C_mul (qDiv Q (α i))]
        have hz : (qDiv Q (α i)).coeff m = 0 := qDiv_coeff_ge Q hQ0 α hfac i m hge
        simp [hz]
      · -- coefficients agree on Fin n
        intro j
        calc
          (P.map (algebraMap ℝ ℂ) - (zmap R).map (algebraMap ℝ ℂ)).coeff j.val
              = (P.map (algebraMap ℝ ℂ)).coeff j.val - ((zmap R).map (algebraMap ℝ ℂ)).coeff j.val := by
                  rw [Polynomial.coeff_sub]
          _ = (P.coeff j.val : ℂ) - ((zmap R).map (algebraMap ℝ ℂ)).coeff j.val := by simp
          _ = (P.coeff j.val : ℂ) - (R.coeff j.val : ℂ) := by
                  have hz := zmap_map_eq R
                  rw [hz]
                  simp
          _ = ((p j - (r j : ℝ)) : ℂ) := by
                  dsimp [p]
                  rw [intPoly_coeff_lt r j]
          _ = ∑ i : Fin n, β i * (qDiv Q (α i)).coeff j.val := hβcov j
          _ = (∑ i : Fin n, β i • qDiv Q (α i)).coeff j.val := by
                  rw [coeff_fintype_sum]
                  apply Finset.sum_congr rfl
                  intro i hi
                  rw [smul_eq_C_mul]
                  rw [Polynomial.coeff_C_mul (qDiv Q (α i))]
    -- ℓ₁ bound
    have hβ2 : (∑ i : Fin n, ‖β i‖) ≤ (n : ℝ) ^ Cadj := by
      have hb1 : (∑ i : Fin n, ‖β i‖) ≤ 2 * (n : ℝ) ^ (100 : ℝ) := hβ1
      have hD : (1 : ℝ) ≤ ((2 * max n n : ℕ) : ℝ) ^ CR := by
        have hD1 : (1 : ℝ) ≤ ((2 * max n n : ℕ) : ℝ) := by
          have hnn : (2 * max n n : ℕ) = (2 * n : ℕ) := by rw [max_self]
          rw [hnn]
          exact_mod_cast (by omega : 1 ≤ 2 * n)
        exact Real.one_le_rpow hD1 hCR0
      have hpb := pow_bound n hn2 CR hCR0
      calc
        (∑ i : Fin n, ‖β i‖) ≤ 2 * (n : ℝ) ^ (100 : ℝ) := hβ1
        _ ≤ 2 * (n : ℝ) ^ (100 : ℝ) * ((2 * max n n : ℕ) : ℝ) ^ CR := by
              simpa [mul_comm] using le_mul_of_one_le_left (by positivity : 0 ≤ 2 * (n : ℝ) ^ (100 : ℝ)) hD
        _ ≤ (n : ℝ) ^ (102 + 2 * CR) := hpb
        _ = (n : ℝ) ^ Cadj := by rfl
    -- weighted norm bound
    have hQc : cwnorm n (Q.map (algebraMap ℤ ℂ)) = wnorm n (zmap Q) := by
      rw [← zmap_map_eq Q, cwnorm_map_eq_wnorm n (zmap Q)]
    have hqbound : ∀ i : Fin n,
        cwnorm n (qDiv Q (α i)) ≤ ((2 * max n n : ℕ) : ℝ) ^ CR * cwnorm n (Q.map (algebraMap ℤ ℂ)) := by
      intro i
      have hdegQc : (Q.map (algebraMap ℤ ℂ)).natDegree = n := Qc_natDegree Q hQn
      have hroot : (Q.map (algebraMap ℤ ℂ)).eval (α i) = 0 := alpha_root Q α hfac i
      rcases (hCRprop n n (by omega) (Q.map (algebraMap ℤ ℂ)) hdegQc (α i) hroot) with ⟨Q', hfacQ', hbound⟩
      have hqdiv : qDiv Q (α i) = Q' := by
        calc
          qDiv Q (α i) = (Q.map (algebraMap ℤ ℂ)) /ₘ (Polynomial.X - Polynomial.C (α i)) := rfl
          _ = ((Polynomial.X - Polynomial.C (α i)) * Q') /ₘ (Polynomial.X - Polynomial.C (α i)) := by rw [hfacQ']
          _ = Q' := Polynomial.mul_divByMonic_cancel_left Q' (Polynomial.monic_X_sub_C (α i))
      rw [hqdiv]
      exact hbound
    have hnormC : cwnorm n ((P - zmap R).map (algebraMap ℝ ℂ))
        ≤ (n : ℝ) ^ Cadj * wnorm n (zmap Q) := by
      have hmap : (P - zmap R).map (algebraMap ℝ ℂ)
          = ∑ i : Fin n, β i • qDiv Q (α i) := by
            rw [Polynomial.map_sub, hpoly]
      calc
        cwnorm n ((P - zmap R).map (algebraMap ℝ ℂ))
            = cwnorm n (∑ i : Fin n, β i • qDiv Q (α i)) := by rw [hmap]
        _ ≤ ∑ i : Fin n, ‖β i‖ * cwnorm n (qDiv Q (α i)) := by
              have h1 := cwnorm_sum_le n (Finset.univ : Finset (Fin n))
                (fun i : Fin n => β i • qDiv Q (α i))
              calc
                cwnorm n (∑ i : Fin n, β i • qDiv Q (α i))
                    = cwnorm n (∑ i ∈ (Finset.univ : Finset (Fin n)), β i • qDiv Q (α i)) := rfl
                _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin n)), cwnorm n (β i • qDiv Q (α i)) := h1
                _ = ∑ i : Fin n, cwnorm n (β i • qDiv Q (α i)) := rfl
                _ ≤ ∑ i : Fin n, ‖β i‖ * cwnorm n (qDiv Q (α i)) := by
                    apply Finset.sum_le_sum
                    intro i hi
                    rw [cwnorm_smul n (β i) (qDiv Q (α i))]
        _ ≤ (∑ i : Fin n, ‖β i‖) * (((2 * max n n : ℕ) : ℝ) ^ CR * cwnorm n (Q.map (algebraMap ℤ ℂ))) := by
              -- common factor: Σ x_i·y_i with y_i ≤ D·Z:
              calc
                (∑ i : Fin n, ‖β i‖ * cwnorm n (qDiv Q (α i)))
                    ≤ ∑ i : Fin n, ‖β i‖ * (((2 * max n n : ℕ) : ℝ) ^ CR * cwnorm n (Q.map (algebraMap ℤ ℂ))) := by
                        apply Finset.sum_le_sum
                        intro i hi
                        exact mul_le_mul_of_nonneg_left (hqbound i) (norm_nonneg (β i))
                _ = (∑ i : Fin n, ‖β i‖) * (((2 * max n n : ℕ) : ℝ) ^ CR * cwnorm n (Q.map (algebraMap ℤ ℂ))) := by
                        rw [← Finset.sum_mul]
        _ ≤ (2 * (n : ℝ) ^ (100 : ℝ)) * (((2 * max n n : ℕ) : ℝ) ^ CR * cwnorm n (Q.map (algebraMap ℤ ℂ))) := by
              exact mul_le_mul_of_nonneg_right hβ1
                (mul_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ ((2 * max n n : ℕ) : ℝ)) CR)
                  (cwnorm_nonneg n (Q.map (algebraMap ℤ ℂ))))
        _ = 2 * (n : ℝ) ^ (100 : ℝ) * ((2 * max n n : ℕ) : ℝ) ^ CR * cwnorm n (Q.map (algebraMap ℤ ℂ)) := by ring
        _ ≤ (n : ℝ) ^ (102 + 2 * CR) * cwnorm n (Q.map (algebraMap ℤ ℂ)) := by
              exact mul_le_mul_of_nonneg_right (pow_bound n hn2 CR hCR0) (cwnorm_nonneg n (Q.map (algebraMap ℤ ℂ)))
        _ = (n : ℝ) ^ Cadj * wnorm n (zmap Q) := by rw [← hQc]
    have hnorm : wnorm n (P - zmap R) ≤ (n : ℝ) ^ Cadj * wnorm n (zmap Q) := by
      rw [← cwnorm_map_eq_wnorm n (P - zmap R)]
      exact hnormC
    refine ⟨R, β, hRdeg, hpoly, hβ2, hnorm⟩

end Submission.AdjustLemma
