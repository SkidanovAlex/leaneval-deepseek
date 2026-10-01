import Mathlib
import Submission.Work.LinnikAreas.Setup
import Submission.Work.LinnikAreas.Assembly
import Submission.Work.LinnikAreas.FarBoundOfDensity
import Submission.Work.LinnikAreas.FamilyZeroDensitySplitting
import Submission.Work.LinnikAreas.ClassIdentity

/-!
# The far-zero bound from Jutila's log-free bound and Montgomery's density theorem

`Work.LinnikAreas.FarBoundOfDensity` derives Heath-Brown's Lemma 13.2 (`FarBoundHyp`) from the
*full* family zero-density estimate `FamilyZeroDensityHyp` (Heath-Brown's (1.4)), which is
log-free on the whole near-line range `(12/5+ε)(1-σ) < 1+ε`.

This module re-runs the same dyadic shell decomposition of the far-zero mass, but *shell by
shell*, so that the log-free requirement is confined to the shells of *small* `λ = (1-β)·𝓛`.

Recall the decomposition: a far zero with `m = ⌊λ⌋` and `|γ|·𝓛 ≤ 2^k` contributes at most
`32·e^{-(49/10)m}·(1/4)^k` times the multiplicity, so the total far mass is bounded by

`32 Σ_m e^{-4.9 m} Σ_k (1/4)^k [R ≤ 2^k, m ≤ 2^k] · cellMult L S m k`,

where `cellMult L S m k` is the total multiplicity of the pairs `(χ,ρ)` in the cell
`λ ∈ [m, m+1)`, `|γ|𝓛 ≤ 2^k`.  The cell is then estimated by

* **(branch 1)** `(m+1) ≤ 𝓛/5`, i.e. `σ = 1 - (m+1)/𝓛 ≥ 4/5`: **Jutila's log-free bound for the
  non-principal characters**, `Σ_{χ ≠ 1} N(σ,T,χ) ≤ C (qT)^{(2+ε)(1-σ)}`
  (`FamilyZeroDensityJutilaNP`, defined in this file — *not* the all-character strengthening
  `FamilyZeroDensityJutila`, which at `σ = 4/5` would contain the density hypothesis for `ζ` and
  is therefore not a theorem of the literature; see the comment above `FamilyZeroDensityJutilaNP`);
* **(branch 2)** `𝓛/5 < (m+1) ≤ 5𝓛/12`, i.e. `7/12 ≤ σ ≤ 4/5`: **Montgomery's density theorem**
  `Σ_χ N(σ,T,χ) ≤ C (qT)^{(12/5+ε)(1-σ)} (log qT)^B`, where a *logarithmic power is harmless*
  (`FamilyZeroDensityMontgomery`, defined below): the `m`-sum over this branch is
  `≪ q^{-0.49}`, which kills every fixed power of `log q`;
* **(branch 3)** `(m+1) > 5𝓛/12`, i.e. `σ < 7/12`: the σ-blind count
  (`finset_sum_le_trivial`), the `m`-sum being `≪ q^{-2.04}`.

The point of the rewrite is that **branch 1** is the only place where a logarithmic factor is
fatal (its `m`-sum is `O(1)`, so a factor `(log q)^B` would survive), while **branch 2** starts
only at `m+1 > 𝓛/5`, where `Σ_m e^{-4.9m} q^{(12/5)(m+1)/𝓛} ≍ e^{-2.5·𝓛/5} = q^{-1/2}`.  Thus
Heath-Brown's (1.4) — log-free on the *whole* near-line range — may be replaced by the pair
(Jutila log-free on `σ ≥ 4/5`) + (Montgomery, logarithmic power allowed, on `σ ≤ 4/5`), which is
the split obtained by differencing the paper's two attributions.  Compare remark (c) in
`Submission/Work/LinnikAreas/FamilyZeroDensitySplitting`.

## Robustness of the constant `12/5` in `FamilyZeroDensityMontgomery`

The proof of `FarBoundHyp_of_jutila_and_montgomery` (in `Submission/Work/LinnikAreas/FarBoundJM`)
uses the Montgomery hypothesis only through two requirements on the exponent coefficient `c` of
`Σ_χ N(σ,T,χ) ≤ C(qT)^{c(1-σ)}(log qT)^B`:

* `c·(5/12) ≤ 3/2` on the middle branch (the exponent must fit `cell_k_sum_density`), i.e.
  `c ≤ 18/5 = 3.6`;
* `c < 4.9 = L - 2K` (the `m`-sum must converge geometrically).

Both hold for `c = 12/5 + ε` (the paper's (1.4)) and equally for `c = 3`, which is the value
supplied by the `c = 3/(2−σ) ≤ 3` form of Montgomery's density theorem (Iwaniec–Kowalski
Theorem 10.4).  The only reason the constant `2451/1000 = 12/5 + 1/1000 + 1/20` appears in
`cellBoundJM` and `MsumBranch2` is the absorption of the logarithm (`(log y) ≤ 100·y^{1/100}`,
using `1/(1-σ) ≤ 5` on the middle branch).  If the density input is only available with the
coefficient `3`, the following three one-line changes are all that is needed:

* `cellBoundJM`: middle branch `2451/1000 ↦ 3051/1000`;
* `JMAux.MsumBranch2`: same substitution, with the bound `30000·CM/(R^{9/10}q^{19/40})`
  replaced by `30000·CM/(R^{7/10}q^{37/100})` (there `A = 3.05`, so `2 - 5A/12 = 0.729` and
  `(4.9-A)/5 = 0.37`);
* the constants in `msum_boundJM`/`finset_boundJM` accordingly.

## The split point `σ = 4/5`

The split is at `λ = (m+1) = 𝓛/5`, i.e. `σ = 4/5`, which is exactly the point at which the
paper's own attribution of (1.4) separates "a log-free bound of Jutila" from "a result of
Huxley".  It is *forced* by the geometry in the following sense:

* on the shells `λ ≤ 𝓛/5` the `m`-sum `Σ_m e^{-4.9m} q^{c(m+1)/𝓛} ≍ Σ_m e^{-(4.9-c)m}` is
  bounded independently of `q`, so any fixed power of `log q` in the density estimate would
  survive the limit `q → ∞` (with `R = R(ε)` fixed) — hence the estimate must be *log-free*
  there;
* on the shells `λ > 𝓛/5` the same `m`-sum is `≍ q^{-(4.9-c)/5}`, which kills every fixed power
  of `log q`, so a logarithmic power is harmless — this is why Montgomery's theorem (with a
  logarithm) suffices on `σ ≤ 4/5`.

Two remarks for the reader who has to *prove* the two Props.

* The split point can be moved: replacing `𝓛/5` by `t₀𝓛` for any **constant** `t₀ ∈ (0,1/5]`
  (in `cellBoundJM`'s first test, and correspondingly in `JMAux.MsumBranch2`'s `hs1`, where the
  decay becomes `q^{-(4.9-A)t₀}`) would let `FamilyZeroDensityJutila` be replaced by the
  *weaker* statement that the estimate be log-free only for `σ ≥ 1 - t₀`, at the cost of
  requiring the Montgomery-type estimate (logarithm allowed) on `σ ≤ 1 - t₀` rather than only
  on `σ ≤ 4/5`.  A *non-constant* `t₀` (for instance the range `λ ≤ (1/3)logloglog q` of
  Heath-Brown's §11 zero detector) does **not** work: `q^{-(4.9-c)t₀}` with `t₀ = o(1)` fails to
  kill `(log q)^B`.
* `FamilyZeroDensityJutilaNP` is **verbatim** the statement of Jutila's log-free theorem in the
  form in which Heath-Brown quotes his source for (1.4), and it is the statement targeted by the
  shared chapter (`Work.ZeroDensity.Jutila.jutilaNonPrincipal`).  Its all-character
  strengthening `FamilyZeroDensityJutila` is *not* a theorem at `σ = 4/5` (it contains the
  density hypothesis for `ζ` there), so the far-zero argument — whose mass only involves
  non-principal characters — consumes the non-principal form; the point of the pair
  (Jutila, Montgomery) is that it is *strictly weaker* than (1.4), so it is an easier target.

## Main results

* `FarBoundHyp_of_jutila_and_montgomery : FamilyZeroDensityJutila → FamilyZeroDensityMontgomery
  → FarBoundHyp`;
* `area2_of_jutila_montgomery : FamilyZeroDensityJutila → FamilyZeroDensityMontgomery →
  Work.LinnikContract.Area2`.
-/

open DirichletCharacter Complex
open scoped Classical BigOperators
noncomputable section

namespace Work.LinnikAreas

open Work.LinnikContract

/-- **Montgomery's density theorem (logarithmic-power form), `σ ≤ 4/5`.**

For every `ε > 0` and every `B > 0` there is `C > 0` such that for all `q ≥ 2`, all `σ ≤ 4/5`
and all `T ≥ 1`,

`Σ_χ N(σ,T,χ) ≤ C·(qT)^{(12/5+ε)(1-σ)}·(log qT)^B`.

This is Heath-Brown's `(1.4)` *with a logarithmic power allowed*, and only in the range
`σ ≤ 4/5` (the range covered by Huxley's `12/5` bound, which Montgomery's large-sieve method
supplies).  It is implied by `FamilyZeroDensityHuxley` (take `B = 0`), and it is *strictly
weaker*: the shells `λ ≥ 𝓛/5` of the far-zero mass can absorb any fixed power of `log q`. -/
def FamilyZeroDensityMontgomery : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ B : ℝ, 0 < B → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), 0 ≤ σ → σ ≤ (4:ℝ)/5 → 1 ≤ T →
      (∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T)
        ≤ C * ((q:ℝ) * T) ^ (((12:ℝ)/5 + ε) * (1 - σ)) * (Real.log ((q:ℝ) * T)) ^ B

/-- **The three-branch cell bound.**  `cellBoundJM q CJ CM c0 L m k` is the bound for the
multiplicity sum over the cell `λ ∈ [m,m+1)`, `|γ|𝓛 ≤ 2^k`:

* `(m+1) ≤ L/5` (`σ ≥ 4/5`): Jutila's log-free bound, exponent `2+1/1000`;
* `L/5 < (m+1) ≤ 5L/12` (`7/12 ≤ σ ≤ 4/5`): Montgomery's density theorem in its `12/5` form
  (Heath-Brown's (1.4)), a logarithmic power being allowed (see `FamilyZeroDensityMontgomery`);
  the *sharper* (and strictly weaker) variant `cellBoundJMsh` below uses the coefficient
  `2551/1000 = 2.551`, which is all that the estimates of the literature require;
* `(m+1) > 5L/12`: the σ-blind uniform ball count.

Note `2.001/5 ≤ 0.4002` and `2.451·5/12 ≤ 1.0213`, both `≤ 3/2`, which is exactly the
`k`-sum hypothesis of `cell_k_sum_density`. -/
def cellBoundJM (q : ℕ) (CJ CM c0 L : ℝ) (m k : ℕ) : ℝ :=
  if ((m:ℝ) + 1) ≤ L/5 then
    CJ * ((q:ℝ) * (2:ℝ)^k) ^ ((2 + 1/1000) * (((m:ℝ) + 1)/L))
  else if ((m:ℝ) + 1) ≤ (5/12)*L then
    CM * ((q:ℝ) * (2:ℝ)^k) ^ ((2451/1000) * (((m:ℝ) + 1)/L))
  else
    (q:ℝ) * c0 * (4 + (2:ℝ)^k) * (Real.log (7 + (2:ℝ)^k) + Real.log (q:ℝ) + 2)

/-- **The sharper three-branch cell bound** (parallel to `cellBoundJM`).

Identical to `cellBoundJM` except that the middle branch uses the density coefficient
`2551/1000 = 2.551` instead of `2451/1000 = 2.451`.  This is the form in which the far-zero
argument needs *only* a log-free estimate with a coefficient `> 5/2` on `σ ∈ [7/12, 4/5]`
(`FamilyZeroDensityMesh`), a statement implied by the *sharp* form `3(1-σ)/(2-σ)+ε` of
Montgomery's density theorem (`FamilyZeroDensityMesh_of_montgomerySharp`) as well as by
Heath-Brown's `12/5` form (`FamilyZeroDensityMesh_of_montgomery`).  Note that
`2.551·1021/5000 ≤ 0.521 ≤ 11/10`, so the `k`-sum hypothesis of `CellLayerKsum` is still met,
and `2.551 < 49/10 = L - 2K`, so the `m`-sums still converge geometrically.  Two further
differences from `cellBoundJM`:

* the middle branch ends at `λ = (1021/5000)𝓛` (instead of `(5/12)𝓛`), so the middle-range input
  `FamilyZeroDensityMesh` is needed only on `σ ∈ [1 - 1021/5000, 4/5] = [0.7958, 0.8]`;
* the third branch instantiates the σ-blind count `finset_sum_le_trivial` at the **scaled**
  height `T = 2^k/𝓛` (legitimate: the zeros of the cell satisfy `|γ|𝓛 ≤ 2^k`), giving
  `q·c₀·(4 + 2^k/𝓛)·(log(7 + 2^k/𝓛) + log q + 2)`.  Its `k`-sum is `Θ(c₀·q/𝓛)` rather than
  `Θ(c₀·q·log q)`, and the accompanying `m`-sum (`msum_branch3sc`) is `≍ c₀·q^{-0.00058}/𝓛`;
  this is what allows the σ-blind shells to start at `λ = (1021/5000)𝓛`. -/
def cellBoundJMsh (q : ℕ) (CJ CM c0 L : ℝ) (m k : ℕ) : ℝ :=
  if ((m:ℝ) + 1) ≤ L/5 then
    CJ * ((q:ℝ) * (2:ℝ)^k) ^ ((2 + 1/1000) * (((m:ℝ) + 1)/L))
  else if ((m:ℝ) + 1) ≤ (1021/5000)*L then
    CM * ((q:ℝ) * (2:ℝ)^k) ^ ((2551/1000) * (((m:ℝ) + 1)/L))
  else
    (q:ℝ) * c0 * (4 + (2:ℝ)^k / L) * (Real.log (7 + (2:ℝ)^k / L) + Real.log (q:ℝ) + 2)

/-- **The genuinely new range of Montgomery's theorem.**  The σ-blind family count of the
workspace (`Work.LinnikAreas.FamilyZeroCountTrivial`) settles `FamilyZeroDensityMontgomery` on
`σ ≤ 7/12` (where the exponent `(12/5+ε)(1-σ)` is at least `1+ε`), so Montgomery's theorem is
only needed on the interval `[7/12, 4/5]` — the range where the density estimate genuinely beats
the trivial count, and the range where the far-zero shells actually live. -/
def FamilyZeroDensityMontgomeryMid : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ B : ℝ, 0 < B → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (7:ℝ)/12 ≤ σ → σ ≤ (4:ℝ)/5 → 1 ≤ T →
      (∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T)
        ≤ C * ((q:ℝ) * T) ^ (((12:ℝ)/5 + ε) * (1 - σ)) * (Real.log ((q:ℝ) * T)) ^ B

/-- **`FamilyZeroDensityMontgomery` follows from `FamilyZeroDensityHuxley`.**  This is what makes
the pair (Jutila, Montgomery) *strictly weaker* than the pair (Jutila, Huxley): allowing the
logarithmic power is a genuine relaxation, since `(log qT)^B ≥ (log 2)^B > 0` only weakens the
right-hand side. -/
theorem FamilyZeroDensityMontgomery_of_huxley (hh : FamilyZeroDensityHuxley) :
    FamilyZeroDensityMontgomery := by
  intro ε hε B hB
  obtain ⟨C, hCpos, hC⟩ := hh ε hε
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨C / (Real.log 2)^B, by positivity, ?_⟩
  intro q hq _inst σ T hσ0 hσ hT
  have hq2 : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
  have hb : (2:ℝ) ≤ (q:ℝ) * T := by nlinarith
  have hb1 : (1:ℝ) ≤ (q:ℝ) * T := by linarith
  have hbase0 : (0:ℝ) ≤ (q:ℝ) * T := by linarith
  have h1 := hC q hq σ T hσ0 hσ hT
  refine le_trans h1 ?_
  have hlog : Real.log 2 ≤ Real.log ((q:ℝ) * T) := Real.log_le_log (by norm_num) hb
  have hp : (Real.log 2) ^ B ≤ (Real.log ((q:ℝ) * T)) ^ B :=
    Real.rpow_le_rpow hlog2pos.le hlog hB.le
  have hpow : (0:ℝ) ≤ ((q:ℝ) * T) ^ (((12:ℝ)/5 + ε) * (1 - σ)) := Real.rpow_nonneg hbase0 _
  have hCeq : C ≤ (C / (Real.log 2)^B) * (Real.log 2)^B := by
    rw [div_mul_cancel₀]
    exact ne_of_gt (Real.rpow_pos_of_pos hlog2pos B)
  calc C * ((q:ℝ) * T) ^ (((12:ℝ)/5 + ε) * (1 - σ))
      ≤ ((C / (Real.log 2)^B) * (Real.log 2)^B) * ((q:ℝ) * T) ^ (((12:ℝ)/5 + ε) * (1 - σ)) :=
        mul_le_mul_of_nonneg_right hCeq hpow
    _ ≤ ((C / (Real.log 2)^B) * (Real.log ((q:ℝ) * T)) ^ B)
          * ((q:ℝ) * T) ^ (((12:ℝ)/5 + ε) * (1 - σ)) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hp (by positivity)) hpow
    _ = C / (Real.log 2)^B * ((q:ℝ) * T) ^ (((12:ℝ)/5 + ε) * (1 - σ))
          * (Real.log ((q:ℝ) * T)) ^ B := by ring

/-- The dyadic layer indicator `1{R ≤ 2^k and m ≤ 2^k}`. -/
def cellLayer (R : ℕ) (m k : ℕ) : ℝ :=
  if (R:ℝ) ≤ (2:ℝ)^k ∧ (m:ℝ) ≤ (2:ℝ)^k then 1 else 0

/-- The **weighted far mass** over a finite set of pairs `(χ,ρ)`: the kernel weights of those
pairs that are non-principal and lie outside the box `InBox q R`. -/
def farMassSum {q : ℕ} [NeZero q] (R : ℕ) (L : ℝ)
    (S : Finset (DirichletCharacter ℂ q × ℂ)) : ℝ :=
  ∑ z ∈ S, (if z.1 = 1 then 0 else if InBox q (R:ℝ) z.2 then 0
    else (zeroMult z.1 z.2 : ℝ) * ‖Hk (11/2) (3/10) ((1 - z.2) * L)‖)

/-- The sub-finset of the pairs of `S` that are non-principal, outside the box, and have
nonzero multiplicity. -/
def farPairs {q : ℕ} [NeZero q] (R : ℕ) (S : Finset (DirichletCharacter ℂ q × ℂ)) :
    Finset (DirichletCharacter ℂ q × ℂ) :=
  (S.filter (fun z => z.1 ≠ 1 ∧ ¬ InBox q (R:ℝ) z.2)).filter
    (fun z => zeroMult z.1 z.2 ≠ 0)

end Work.LinnikAreas

namespace Work.LinnikAreas

open Work.LinnikContract

/-- **The sharp (multiplicative-large-sieve) form of Montgomery's density theorem.**
For every `ε > 0` and `B > 0` there is `C > 0` with
`Σ_χ N(σ,T,χ) ≤ C·(qT)^{3(1-σ)/(2-σ)+ε}·(log qT)^B` for all `q ≥ 2`, `σ ≥ 1/2` and `T ≥ 1`.
This is the shape of `Work.ZeroDensity.MontgomerySharp` (Iwaniec–Kowalski, Theorem 10.4), and it
is the *sharp* exponent `3/(2-σ) ≤ 3` supplied by the multiplicative large sieve, as opposed to
the `12/5` coefficient of Heath-Brown's (1.4)/Huxley. -/
def FamilyZeroDensityMontgomerySharp : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ B : ℝ, 0 < B → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (1:ℝ)/2 ≤ σ → σ ≤ 1 → 1 ≤ T →
      (∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T)
        ≤ C * ((q:ℝ) * T) ^ (3 * (1 - σ) / (2 - σ) + ε) * (Real.log ((q:ℝ) * T)) ^ B

/-- **The log-free middle-range input** — the *only* density statement the far-zero argument
needs beyond Jutila's log-free bound and the σ-blind count.

For every `ε > 0` there is `C > 0` with `Σ_χ N(σ,T,χ) ≤ C·(qT)^{(51/20+ε)(1-σ)}` for all
`q ≥ 2`, `1 - 1021/5000 ≤ σ ≤ 4/5` and `T ≥ 1`.

The lower end of the range is not a loss: the far-zero decomposition consumes this estimate
*only* on the middle branch `𝓛/5 < (m+1) ≤ (1021/5000)𝓛`, i.e. on `λ = (m+1) ∈ (𝓛/5, 0.2042𝓛]`,
which is exactly `σ ∈ [1 - 1021/5000, 4/5]` (see `cellBoundJMsh` and `CellMultLeBoundJMsh`); on
the shells below that interval the log-free Jutila input is used, and above it the σ-blind count.
Stating the input on the wider range `[1/2, 4/5]` would therefore be an unnecessary strengthening —
which matters, because on `[1/2, 4/5]` the *principal* character would require a `ζ` density
estimate with exponent `51/20` (`= 2.55`), while on the window actually used it is supplied by
Huxley's classical `ζ` bound (`3/(3σ-1) ≤ 51/20` for `σ ≥ 0.7255`).  This is *strictly weaker* than either form of
Montgomery's theorem used in the literature: the coefficient `51/20 = 2.55` is larger than
Huxley's `12/5 = 2.4` (so `FamilyZeroDensityMontgomery` implies it, see below) and larger than
the sharp `3/(2-σ) ≤ 5/2`, but still smaller than `49/10 = L - 2K` — which is exactly what the
geometric `m`-sum of the far-zero mass needs, and what makes the shells `λ ≥ 𝓛/5` absorb *any*
fixed power of `log q`.  Log-freeness (rather than a logarithmic power) is what makes the
statement directly usable as the hypothesis of `cellBoundJM`'s middle branch. -/
def FamilyZeroDensityMesh : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (1:ℝ) - 1021/5000 ≤ σ → σ ≤ (4:ℝ)/5 → 1 ≤ T →
      (∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T)
        ≤ C * ((q:ℝ) * T) ^ (((51:ℝ)/20 + ε) * (1 - σ))

/-- `(log y)^B ≤ (B/η)^B·y^η` for `y ≥ 1`, `B, η > 0` (from `log y ≤ y^a/a` with `a = η/B`). -/
lemma log_rpow_le_const_mul_rpow {B η y : ℝ} (hB : 0 < B) (hη : 0 < η) (hy : 1 ≤ y) :
    (Real.log y) ^ B ≤ (B/η) ^ B * y ^ η := by
  have hy0 : (0:ℝ) < y := lt_of_lt_of_le one_pos hy
  have ha : (0:ℝ) < η/B := div_pos hη hB
  have h1 : Real.log y ≤ y ^ (η/B) / (η/B) := Real.log_le_rpow_div hy0.le ha
  have h2 : y ^ (η/B) / (η/B) = (B/η) * y ^ (η/B) := by field_simp
  rw [h2] at h1
  have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy
  have h3 : (Real.log y) ^ B ≤ ((B/η) * y ^ (η/B)) ^ B := Real.rpow_le_rpow hlog0 h1 hB.le
  refine le_trans h3 (le_of_eq ?_)
  have hnn : (0:ℝ) ≤ y := le_of_lt hy0
  rw [Real.mul_rpow (by positivity) (Real.rpow_nonneg hnn _)]
  congr 1
  rw [← Real.rpow_mul hnn]
  congr 1
  field_simp

/-- **The multiplicative (`12/5`) log-power form implies the middle-range input.**
This is the bridge that keeps the previous reduction (Jutila + `FamilyZeroDensityMontgomery`)
available.  The logarithmic power is absorbed by the *slack*
`51/20 - 12/5 = 3/20` in the exponent, using `1 - σ ≥ 1/5`. -/
theorem FamilyZeroDensityMesh_of_montgomery (hm : FamilyZeroDensityMontgomery) :
    FamilyZeroDensityMesh := by
  intro ε hε
  obtain ⟨C, hC, hM⟩ := hm (1/1000) (by norm_num) 1 (by norm_num)
  refine ⟨100 * C, by positivity, ?_⟩
  intro q hq _inst σ T hσ7 hσ4 hT
  have hbase1 : (1:ℝ) ≤ (q:ℝ) * T := by
    have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    nlinarith
  have hbase0 : (0:ℝ) ≤ (q:ℝ) * T := by linarith
  have hlog : Real.log ((q:ℝ) * T) ≤ 100 * ((q:ℝ) * T) ^ ((1:ℝ)/100) := by
    have h := Real.log_le_rpow_div hbase0 (by norm_num : (0:ℝ) < (1:ℝ)/100)
    rw [div_eq_mul_inv] at h
    have h100 : (((1:ℝ)/100)⁻¹) = 100 := by norm_num
    linarith [h, h100]
  have h15 : (1:ℝ)/5 ≤ 1 - σ := by linarith
  have hσ0 : (0:ℝ) ≤ σ := by linarith
  have hexp : ((12:ℝ)/5 + 1/1000) * (1 - σ) + 1/100
      ≤ ((51:ℝ)/20 + ε) * (1 - σ) := by
    have h6 : (1:ℝ)/100 + (1/1000) * (1 - σ) ≤ (3/20) * (1 - σ) := by
      have h1 : (1:ℝ)/100 + 1/1000 ≤ (3/20 : ℝ) * (1/5) := by norm_num
      have h2 : (1/1000:ℝ) * (1 - σ) ≤ 1/1000 := by nlinarith
      have h3 : (3/20 : ℝ) * (1/5) ≤ (3/20) * (1 - σ) := by nlinarith
      linarith
    have h7 : (0:ℝ) ≤ ε * (1 - σ) := mul_nonneg hε.le (by linarith)
    nlinarith [h6, h7]
  have hmain := hM q hq σ T (by linarith) hσ4 hT
  have hstep1 : (∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T)
      ≤ C * ((q:ℝ) * T) ^ (((12:ℝ)/5 + 1/1000) * (1 - σ)) * (Real.log ((q:ℝ) * T)) ^ (1:ℝ) := hmain
  have hlog0 : 0 ≤ Real.log ((q:ℝ) * T) := Real.log_nonneg hbase1
  have hstep2 : C * ((q:ℝ) * T) ^ (((12:ℝ)/5 + 1/1000) * (1 - σ)) * (Real.log ((q:ℝ) * T)) ^ (1:ℝ)
      ≤ C * ((q:ℝ) * T) ^ (((12:ℝ)/5 + 1/1000) * (1 - σ)) * (100 * ((q:ℝ) * T) ^ ((1:ℝ)/100)) := by
    have hpow : (Real.log ((q:ℝ) * T)) ^ (1:ℝ) = Real.log ((q:ℝ) * T) := Real.rpow_one _
    rw [hpow]
    have hC' : (0:ℝ) ≤ C * ((q:ℝ) * T) ^ (((12:ℝ)/5 + 1/1000) * (1 - σ)) := by positivity
    exact mul_le_mul_of_nonneg_left hlog hC'
  have hbasepos : (0:ℝ) < (q:ℝ) * T := lt_of_lt_of_le one_pos hbase1
  have hstep3 : C * ((q:ℝ) * T) ^ (((12:ℝ)/5 + 1/1000) * (1 - σ)) * (100 * ((q:ℝ) * T) ^ ((1:ℝ)/100))
      = 100 * C * ((q:ℝ) * T) ^ (((12:ℝ)/5 + 1/1000) * (1 - σ) + 1/100) := by
    rw [show C * ((q:ℝ) * T) ^ (((12:ℝ)/5 + 1/1000) * (1 - σ)) * (100 * ((q:ℝ) * T) ^ ((1:ℝ)/100))
        = 100 * C * (((q:ℝ) * T) ^ (((12:ℝ)/5 + 1/1000) * (1 - σ)) * ((q:ℝ) * T) ^ ((1:ℝ)/100)) by
      ring]
    rw [← Real.rpow_add hbasepos]
  have hstep4 : 100 * C * ((q:ℝ) * T) ^ (((12:ℝ)/5 + 1/1000) * (1 - σ) + 1/100)
      ≤ 100 * C * ((q:ℝ) * T) ^ (((51:ℝ)/20 + ε) * (1 - σ)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le hbase1 hexp
  linarith [hstep1, hstep2, hstep3, hstep4]

/-- **The sharp Montgomery exponent implies the middle-range input.**
Since `3/(2-σ) ≤ 3/(2-4/5) = 5/2 ≤ 51/20` on `σ ≤ 4/5`, the sharp form of Montgomery's theorem
supplies the middle-range input; the slack `51/20 - 5/2 = 1/20` absorbs the logarithmic power
(`(log y)^B ≤ (200B)^B·y^{1/200}`, using `1 - σ ≥ 1/5`). -/
theorem FamilyZeroDensityMesh_of_montgomerySharp (hm : FamilyZeroDensityMontgomerySharp) :
    FamilyZeroDensityMesh := by
  intro ε hε
  obtain ⟨C, hC, hM⟩ := hm (1/500) (by norm_num) 1 (by norm_num)
  refine ⟨200 * C, by positivity, ?_⟩
  intro q hq _inst σ T hσ7 hσ4 hT
  have hbase1 : (1:ℝ) ≤ (q:ℝ) * T := by
    have : (2:ℝ) ≤ (q:ℝ) := by exact_mod_cast hq
    nlinarith
  have hbase0 : (0:ℝ) ≤ (q:ℝ) * T := by linarith
  have hlog : Real.log ((q:ℝ) * T) ≤ 200 * ((q:ℝ) * T) ^ ((1:ℝ)/200) := by
    have h := Real.log_le_rpow_div hbase0 (by norm_num : (0:ℝ) < (1:ℝ)/200)
    rw [div_eq_mul_inv] at h
    have h200 : (((1:ℝ)/200)⁻¹) = 200 := by norm_num
    linarith [h, h200]
  have h15 : (1:ℝ)/5 ≤ 1 - σ := by linarith
  have hden : (0:ℝ) < 2 - σ := by linarith
  have hcoef : 3 / (2 - σ) ≤ (5:ℝ)/2 := by
    rw [div_le_iff₀ hden]; linarith
  have hexp : 3 * (1 - σ) / (2 - σ) + 1/500 + 1/200 ≤ ((51:ℝ)/20 + ε) * (1 - σ) := by
    have heq : 3 * (1 - σ) / (2 - σ) = (3 / (2 - σ)) * (1 - σ) := by ring
    rw [heq]
    have h1 : (3 / (2 - σ)) * (1 - σ) ≤ (5/2) * (1 - σ) :=
      mul_le_mul_of_nonneg_right hcoef (by linarith)
    have h2 : (0:ℝ) ≤ ε * (1 - σ) := mul_nonneg hε.le (by linarith)
    have h4 : (7/1000 : ℝ) ≤ (1/20) * (1 - σ) := by nlinarith [h15]
    have h5 : (51:ℝ)/20 * (1 - σ) = (5/2) * (1 - σ) + (1/20) * (1 - σ) := by ring
    linarith [h1, h2, h4, h5]
  have hmain := hM q hq σ T (by linarith) (by linarith) hT
  have hstep2 : C * ((q:ℝ) * T) ^ (3 * (1 - σ) / (2 - σ) + 1/500) * (Real.log ((q:ℝ) * T)) ^ (1:ℝ)
      ≤ C * ((q:ℝ) * T) ^ (3 * (1 - σ) / (2 - σ) + 1/500) * (200 * ((q:ℝ) * T) ^ ((1:ℝ)/200)) := by
    have hpow : (Real.log ((q:ℝ) * T)) ^ (1:ℝ) = Real.log ((q:ℝ) * T) := Real.rpow_one _
    rw [hpow]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  have hbasepos : (0:ℝ) < (q:ℝ) * T := lt_of_lt_of_le one_pos hbase1
  have hstep3 : C * ((q:ℝ) * T) ^ (3 * (1 - σ) / (2 - σ) + 1/500) * (200 * ((q:ℝ) * T) ^ ((1:ℝ)/200))
      = 200 * C * ((q:ℝ) * T) ^ (3 * (1 - σ) / (2 - σ) + 1/500 + 1/200) := by
    rw [show C * ((q:ℝ) * T) ^ (3 * (1 - σ) / (2 - σ) + 1/500) * (200 * ((q:ℝ) * T) ^ ((1:ℝ)/200))
        = 200 * C * (((q:ℝ) * T) ^ (3 * (1 - σ) / (2 - σ) + 1/500) * ((q:ℝ) * T) ^ ((1:ℝ)/200)) by
      ring]
    rw [← Real.rpow_add hbasepos]
  have hstep4 : 200 * C * ((q:ℝ) * T) ^ (3 * (1 - σ) / (2 - σ) + 1/500 + 1/200)
      ≤ 200 * C * ((q:ℝ) * T) ^ (((51:ℝ)/20 + ε) * (1 - σ)) := by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le hbase1 hexp
  linarith [hmain, hstep2, hstep3, hstep4]

/-! ## The non-principal form of Jutila's bound (the form the far-zero mass consumes)

The far-zero mass `Σ_{χ ≠ 1} farSum χ` involves **non-principal** characters only, so the family
zero-density estimate that bounds it need only be stated for the non-principal characters.  This
is not a cosmetic point: the *all-character* version `FamilyZeroDensityJutila`
(`Σ_{χ mod q} N(σ,T,χ) ≤ C·(qT)^{(2+ε)(1-σ)}` on `σ ≥ 4/5`) contains `N(σ,T,χ₀)` for the
**principal** character, i.e. at `σ = 4/5` a zero-density estimate for `ζ` with exponent `2`.
That is the density hypothesis for `ζ` at `σ = 4/5`, which is **not known**: Huxley's bound
gives the exponent `3/(2-σ) = 5/2` at `σ = 4/5`, and the Guth–Maynard exponent `30/13` is
available only for `σ ≥ 9/10`.  So `FamilyZeroDensityJutila` is *not* a theorem of the
literature, while `FamilyZeroDensityJutilaNP` below is **verbatim** Jutila's log-free theorem for
the non-principal characters — exactly the statement targeted in the shared chapter
`Submission/Work/ZeroDensity` as `Work.ZeroDensity.Jutila.jutilaNonPrincipal`, and the form in
which Heath-Brown quotes his source for (1.4).  Every consumer of the far-zero argument in this
development therefore takes the non-principal form. -/

/-- **Jutila's log-free bound, non-principal characters**:
`Σ_{χ ≠ 1} N(σ,T,χ) ≤ C·(qT)^{(2+ε)(1-σ)}` for `σ ≥ 4/5`, **log-free** (no power of `log qT`).
Verbatim the statement of `Work.ZeroDensity.Jutila.jutilaNonPrincipal`. -/
def FamilyZeroDensityJutilaNP : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (4 : ℝ)/5 ≤ σ → σ ≤ 1 → 1 ≤ T →
      (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
          Work.LinnikAreas.zeroCountIn χ σ T)
        ≤ C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ))

/-- The **all-character** form of Jutila's bound implies the non-principal form: simply discard
the `χ = 1` term.  This is the direction in which the non-principal statement is *weaker*; the
converse is the (open) principal-character statement discussed in the comment above. -/
theorem FamilyZeroDensityJutilaNP_of_jutila (h : FamilyZeroDensityJutila) :
    FamilyZeroDensityJutilaNP := by
  intro ε hε
  obtain ⟨C, hC, hC'⟩ := h ε hε
  refine ⟨C, hC, ?_⟩
  intro q hq _inst σ T hσ hσ1 hT
  refine le_trans
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset (1) Finset.univ)
      (fun χ _ _ => Work.LinnikAreas.zeroCountIn_nonneg χ σ T)) ?_
  exact hC' q hq σ T hσ hσ1 hT

/-- **Alignment with the shared chapter.**  The statement proved in `Submission/Work/ZeroDensity`
as `Work.ZeroDensity.Jutila.jutilaNonPrincipal` — written out verbatim here — *is*
`FamilyZeroDensityJutilaNP`, so the chapter's target closes the non-principal Jutila input of
Area 2 by this identity. -/
theorem familyZeroDensityJutilaNP_of_chapter
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
      ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (4 : ℝ)/5 ≤ σ → σ ≤ 1 → 1 ≤ T →
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q),
            Work.LinnikAreas.zeroCountIn χ σ T)
          ≤ C * ((q : ℝ) * T) ^ ((2 + ε) * (1 - σ))) :
    FamilyZeroDensityJutilaNP := h

/-! ## The *crude* log-free input: the coefficient is not the difficulty

Area 2's low-`λ` branch needs a log-free family estimate on a **constant** `σ`-interval, but it
uses it only through the geometric `m`-sum `e^c Σ_m e^{-(4.9-c)m} = O(1)`, which converges for
**every** `c < 49/10 = 4.9`, and through the dyadic `k`-sum, which converges as soon as
`c(m+1)/𝓛 ≤ c/5 < 2`.  So a *crude* log-free estimate — with any coefficient below `4.9`, say
`24/5 = 4.8` — serves Area 2 exactly as well as Jutila's sharp `c = 2` (only the constants and
the threshold `q₀` change).  This is the input to target if the sharp theorem is hard: the
difficulty is the *log-free constant-range* shape, not the coefficient.

The two statements below are the crude forms.  `FamilyZeroDensityJutilaCrude` is stated on
Jutila's range `σ ≥ 4/5` and fills branch 1 of the far-zero decomposition; the *wide* form
`FamilyZeroDensityJutilaCrudeWide` is stated on `σ ≥ 1 - 1021/5000`, the `σ`-range of the whole
low-`λ` region (its `λ`-threshold `1021/5000 > 1/4.9 = 0.204081…` is exactly the threshold at
which the σ-blind count starts to decay), and proving it closes `area2` with **one** input and no
mid-range estimate at all. -/

/-- **The crude log-free family estimate** (non-principal characters, exponent coefficient
`24/5 = 4.8`): `Σ_{χ ≠ 1} N(σ,T,χ) ≤ C·(qT)^{(24/5+ε)(1-σ)}` for `q ≥ 2`, `σ ≥ 4/5`, `T ≥ 1`.
Weaker than Jutila's `c = 2` in the coefficient, but still *log-free* and on a constant
`σ`-range — which is all the far-zero argument needs. -/
def FamilyZeroDensityJutilaCrude : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (4 : ℝ)/5 ≤ σ → σ ≤ 1 → 1 ≤ T →
      (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), zeroCountIn χ σ T)
        ≤ C * ((q : ℝ) * T) ^ (((24 : ℝ)/5 + ε) * (1 - σ))

/-- **The *wide-range* crude log-free estimate**: the same statement on
`σ ≥ 1 - 1021/5000 = 0.7958`, the `σ`-range of the *whole* low-`λ` branch of the far-zero
decomposition (its `λ`-threshold `1021/5000 > 1/4.9` is the branch-3 threshold of the σ-blind
count).  Proving this single statement closes `Work.LinnikAreas.area2` with **no** mid-range
input at all; see `Submission/Work/LinnikAreas/NOTE_area2_principal_character.md`, §7. -/
def FamilyZeroDensityJutilaCrudeWide : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧
    ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ), (1 : ℝ) - 1021/5000 ≤ σ → σ ≤ 1 → 1 ≤ T →
      (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), zeroCountIn χ σ T)
        ≤ C * ((q : ℝ) * T) ^ (((24 : ℝ)/5 + ε) * (1 - σ))

/-- The sharp non-principal Jutila input implies the crude one on the same range (the exponent
`2 + ε ≤ 24/5 + ε` only weakens the right-hand side). -/
theorem FamilyZeroDensityJutilaCrude_of_jutilaNP (h : FamilyZeroDensityJutilaNP) :
    FamilyZeroDensityJutilaCrude := by
  intro ε hε
  obtain ⟨C, hC, hC'⟩ := h ε hε
  refine ⟨C, hC, ?_⟩
  intro q hq _inst σ T hσ hσ1 hT
  have hbase : (1 : ℝ) ≤ (q : ℝ) * T := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  refine le_trans (hC' q hq σ T hσ hσ1 hT) (mul_le_mul_of_nonneg_left ?_ hC.le)
  refine Real.rpow_le_rpow_of_exponent_le hbase ?_
  nlinarith

/-- The wide crude input implies the narrow one (its `σ`-range is larger). -/
theorem FamilyZeroDensityJutilaCrude_of_wide (h : FamilyZeroDensityJutilaCrudeWide) :
    FamilyZeroDensityJutilaCrude := by
  intro ε hε
  obtain ⟨C, hC, hC'⟩ := h ε hε
  refine ⟨C, hC, ?_⟩
  intro q hq _inst σ T hσ hσ1 hT
  exact hC' q hq σ T (by linarith) hσ1 hT

/-! ## The decomposition of the family count over primitive conductors

The far-zero mass only involves non-principal characters.  Every such character mod `q` is
induced from a unique primitive character of a *conductor* `d ∣ q` (Mathlib:
`DirichletCharacter.changeLevel_primitiveCharacter`, `conductor_dvd_level`,
`primitiveCharacter_changeLevel_apply`, `changeLevel_injective`), and `zeroCountIn χ σ T` counts
the zeros of the completed `L`-function of the *primitive* character inducing `χ` — so the
non-principal family count at level `q` is *exactly* the sum of the primitive family counts at the
levels `d ∣ q`, `d ≥ 2`:

`famSumNP q σ T = Σ_{d ∈ q.divisors.erase 1} primFamSum d σ T`.

This is the exact form of the "sum over the divisors" step.  It is also the reason that this step
**cannot** be used to transfer a *log-free, multiplicative-in-`ε`* estimate from primitive
characters to characters of level `q`: an estimate at level `d` transfers with the factor
`Σ_{d|q}(d/q)^{A} ≤ τ(q)` (with `A = (c+ε)(1-σ)`), which tends to `τ(q)` as `A → 0` — i.e. as
`σ → 1`, while the right-hand side of the target tends to the constant `C`; and `τ(q)` is
unbounded.  See `Work.LinnikAreas.NOTE_area2_principal_character.md` §6. -/

/-- The **non-principal family zero count** at level `q`. -/
def famSumNP (q : ℕ) [NeZero q] (σ T : ℝ) : ℝ :=
  ∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), zeroCountIn χ σ T

/-- The **primitive family zero count** at level `d` (zero for `d = 0`, where there are no
characters). -/
def primFamSum (d : ℕ) (σ T : ℝ) : ℝ :=
  if h : d = 0 then 0 else by
    haveI : NeZero d := ⟨h⟩
    exact ∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ d => χ.IsPrimitive),
      zeroCountIn χ σ T

/-- **The wide crude input follows from the two sharp inputs** (non-principal Jutila on
`σ ≥ 4/5` together with the log-free mid-range estimate `FamilyZeroDensityMesh` on
`σ ∈ [1 - 1021/5000, 4/5]`).

On `σ ≥ 4/5` the sharp input gives `(2+ε)(1-σ) ≤ (24/5+ε)(1-σ)` directly; on the strip
`σ ≤ 4/5` the mid-range input gives `(51/20+ε)(1-σ) ≤ (24/5+ε)(1-σ)` (as `51/20 = 2.55 < 4.8`),
and its sum over *all* characters dominates the non-principal one.  Hence the single-input route
to `FarBoundHyp` (`FarBoundOfJutilaCrudeWide`) is available as soon as the fleet's two sharp
targets are; but the wide crude statement can also be attacked directly, which is the cheaper
route to Area 2. -/
theorem FamilyZeroDensityJutilaCrudeWide_of_jutilaNP_and_mesh
    (hj : FamilyZeroDensityJutilaNP) (hm : FamilyZeroDensityMesh) :
    FamilyZeroDensityJutilaCrudeWide := by
  intro ε hε
  obtain ⟨CJ, hCJ, hJ⟩ := hj ε hε
  obtain ⟨CM, hCM, hM⟩ := hm ε hε
  refine ⟨max CJ CM, lt_max_of_lt_left hCJ, ?_⟩
  intro q hq _inst σ T hσ hσ1 hT
  have hbase : (1 : ℝ) ≤ (q : ℝ) * T := by
    have : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hbase0 : (0 : ℝ) ≤ (q : ℝ) * T := le_trans zero_le_one hbase
  have hNPreal : (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), zeroCountIn χ σ T)
      ≤ ∑ χ : DirichletCharacter ℂ q, zeroCountIn χ σ T :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset (1) Finset.univ)
      (fun χ _ _ => zeroCountIn_nonneg χ σ T)
  rcases le_total σ ((4 : ℝ)/5) with h45 | h45
  · -- on the strip σ ≤ 4/5: the mid-range (all-character) estimate
    have hmesh := hM q hq σ T hσ h45 hT
    have hexp : ((51:ℝ)/20 + ε) * (1 - σ) ≤ ((24:ℝ)/5 + ε) * (1 - σ) := by
      have h1 : (51:ℝ)/20 ≤ (24:ℝ)/5 := by norm_num
      have h2 : (0:ℝ) ≤ 1 - σ := by linarith
      nlinarith
    refine le_trans (le_trans hNPreal hmesh) ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hbase hexp) hCM.le) ?_
    exact mul_le_mul_of_nonneg_right (le_max_right CJ CM)
      (Real.rpow_nonneg hbase0 _)
  · -- on σ ≥ 4/5: the sharp non-principal estimate
    have hJ' := hJ q hq σ T h45 hσ1 hT
    have hexp : (2 + ε) * (1 - σ) ≤ ((24:ℝ)/5 + ε) * (1 - σ) := by
      have h2 : (0:ℝ) ≤ 1 - σ := by linarith
      nlinarith
    refine le_trans hJ' ?_
    refine le_trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hbase hexp) hCJ.le) ?_
    exact mul_le_mul_of_nonneg_right (le_max_left CJ CM)
      (Real.rpow_nonneg hbase0 _)

/-- **Area 2's gap from the *unified* log-free estimate** (`JUTILA_UNIFIED_LEAD.md` §3,
`Work.ZeroDensity.LogFree.logFreeNP (3979/5000) 4`).

The content of that estimate is written out verbatim here as a hypothesis, so that no import of
the (in-progress) unified chapter is needed:
`Σ_{χ ≠ 1} N(σ,T,χ) ≤ C·(qT)^{4(1-σ)}` on `σ ≥ 3979/5000 = 1 - 1021/5000`.  It implies the
crude wide-range input `FamilyZeroDensityJutilaCrudeWide`, because `4 ≤ 24/5 + ε` and `qT ≥ 1`.
(Definitionally it *is* `logFreeNP (3979/5000) 4`, through
`famCountNP q σ T = Σ_{χ ∈ univ.erase 1} zCount χ σ T` and `zCount = zeroCountIn`; the same
bridge is also proved in `Submission/Work/ZeroDensity/LogFree/logFreeNPInstances.lean`, and
`Work.LinnikAreas.LogFreeNPWiring` records the identification.) -/
theorem FamilyZeroDensityJutilaCrudeWide_of_logFreeNP
    (h : ∃ C : ℝ, 0 < C ∧ ∀ q : ℕ, 2 ≤ q → ∀ [NeZero q] (σ T : ℝ),
      (3979 / 5000 : ℝ) ≤ σ → σ ≤ 1 → 1 ≤ T →
        (∑ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ q), zeroCountIn χ σ T)
          ≤ C * ((q : ℝ) * T) ^ (4 * (1 - σ))) :
    FamilyZeroDensityJutilaCrudeWide := by
  intro ε hε
  obtain ⟨C, hC, hh⟩ := h
  refine ⟨C, hC, ?_⟩
  intro q hq _inst σ T hσ hσ1 hT
  have hσ' : (3979 / 5000 : ℝ) ≤ σ := by
    have heq : (3979 / 5000 : ℝ) = 1 - 1021 / 5000 := by norm_num
    rw [heq]; exact hσ
  have hbase : (1 : ℝ) ≤ (q : ℝ) * T := by
    have h2 : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
    nlinarith
  have hexp : 4 * (1 - σ) ≤ ((24 : ℝ)/5 + ε) * (1 - σ) := by
    have h0 : (0 : ℝ) ≤ 1 - σ := by linarith
    nlinarith [hε, h0]
  exact le_trans (hh q hq σ T hσ' hσ1 hT)
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hbase hexp) (le_of_lt hC))

end Work.LinnikAreas
