import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB1Cube.ConeC.BoseFixB1S_boxPairCount_eq_sum_compT
import Submission.Work.BoseFixB1S.HopDefs
import Submission.Work.BoseFixB1S.fsPSpectralB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.hopAmgmB1` — the AM–GM rung of FS's completion of squares

Holder: the same agent that holds `Submission/Work/BoseFixB1S/perBoxFWeightB1.lean`.

## What this file is

FS's proof of `lm:appinteractionestimate` (`Papers/fournais_solovej/final_v2.tex`
l.3726–3740, display between `eq:Q3+Q4CS` and `eq:BQwQleq`) is the **one** remaining analytic step
of the whole project (see `NOTES_crux_boxCrossLower.md` §3, `FINDING_boxJointCore_route.md` §3,
`FINDING_S290_boxCrossJointGen_audit.md` §3).  In the fleet's own vocabulary the step is:

* the proved expansion `Work.BoseFixB1S.boxCrossExpansionB1S` writes the *centred* cross part as a
  sum over **hopping pairs** `p ∈ hopPairSet i` (parent `ψ_p = boxCompT V A p.1 p.2 Φ`, child
  `ψ_{c_i(p)}`, coefficient `|p.1| − 1 − μV`) of the pairings
  `∫ ψ_{c_i(p)} · δ(xᵢ) · ψ_p` with the **centred fibre** `δ = fib − M₁/V`;
* FS then complete the square *per hopping pair* with the operator weights
  `(n₀^{1/2} ± (μV)^{1/2})²`, which in this vocabulary is the pointwise atom of
  `Work.BoseFixB1.a0SquareCompletion` — already transported to the hop coefficient by
  `Work.BoseFixB1S.two_mul_mul_sub_one_sub_ge_sqrt` (`Submission/Work/BoseFixB1S/fsPSpectralB1.lean`).

This module supplies the *abstract* AM–GM step that turns the hop expansion into the two FS
supplies, with the **constants free** (the target `(★★)` has an existential `C`):

    (t − 1 − m)·I  ≥  − 5·(t + 1 + m)·(A + B)        whenever  |I| ≤ √(A·B),

which is FS's μ-line completion with `t = |p.1|`, `m = μV`, and the two *supplies* identified as

* (Q-side) `A = ∫ ψ_{c_i(p)}²·|δ(xᵢ)|` — bounded by the *uniform* fibre bound `fib ≤ C·a` and
  `|δ| ≤ fib + κ`, hence by `C·a·∫ψ²`;
* (P-side) `B = ∫ ψ_p²·|δ(xᵢ)|` — for the **parent** `ψ_p` this is *exact*: `ψ_p` lies in
  `Range(P_{B,i})`, so the fibre sandwich `Work.BoseFixB1S.fibreSandwichB1` gives
  `∫ψ_p²·fib(xᵢ) = κ∫ψ_p²`, hence `B ≤ 2κ∫ψ_p²` with `κ = M₁/V` — the `M₁G`/`pcb` supply.

The centring is indispensable (it is what produces the hop expansion at all: `M_δ` acts as `0` on
`Range(P_{B,i})`), and it costs nothing quantitatively: `|fib − κ| ≤ fib + κ`.

⚠ Do **not** try to keep the *sharp* weights `(√(t+1) ± √m)²` together with a **signed** fibre: the
sharp atom is only valid for a nonnegative weight (multiplying by the *sign* of `δ` destroys
Cauchy–Schwarz).  The coarse constants `5`/`10` below are exactly this trade; they are free.

## Contents

* `two_mul_mul_sub_one_sub_ge_abs` — the pointwise |weight|-weighted completion (both signs);
* `hopAmgm_term` — the paired (integrated) form with the two supplies;
* `hopAmgm_sum` — the `Finset` form over a general hopping-pair family;
* `hopAmgm_hopPairSet` — the same at `hopPairSet i`, with the coefficient dictionary
  `t = |p.1|`, `m = μ·V`.
-/

noncomputable section

open scoped BigOperators Real

namespace Work.BoseFixB1S

/-! ## 1. The pointwise completion with a signed weight -/

/-- **The shifted square completion with a *signed* weight** (the form the hop expansion needs).

For `t, m ≥ 0` and reals `x, y, d`,

    2·x·y·d·(t − 1 − m) ≥ −10·(t + 1 + m)·(x² + y²)·|d| .

The sharp (unsigned) version is `Work.BoseFixB1S.two_mul_mul_sub_one_sub_ge_sqrt` (with the
FS-weights `(√(t+1) ± √m)²` and the `2/2` corrections); the extra factor `10` here is precisely
the price of the *sign* of `d`: for `d ≥ 0` we use the sharp atom (`(√(t+1)+√m)² ≤ 2(t+1+m)`),
for `d < 0` we only need `|t−1−m| ≤ t+1+m`. -/
theorem two_mul_mul_sub_one_sub_ge_abs (t m x y d : ℝ) (ht : 0 ≤ t) (hm : 0 ≤ m) :
    2 * x * y * d * (t - 1 - m) ≥ -10 * (t + 1 + m) * (x ^ 2 + y ^ 2) * |d| := by
  have hS : (Real.sqrt (t + 1) + Real.sqrt m) ^ 2 ≤ 2 * (t + 1 + m) := by
    have h1 : Real.sqrt (t + 1) ^ 2 = t + 1 := Real.sq_sqrt (by linarith)
    have h2 : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm
    nlinarith [sq_nonneg (Real.sqrt (t + 1) - Real.sqrt m), h1, h2]
  have hP : (Real.sqrt (t + 1) - Real.sqrt m) ^ 2 ≤ 2 * (t + 1 + m) := by
    have h1 : Real.sqrt (t + 1) ^ 2 = t + 1 := Real.sq_sqrt (by linarith)
    have h2 : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm
    nlinarith [sq_nonneg (Real.sqrt (t + 1) + Real.sqrt m), h1, h2]
  have htm : 1 ≤ t + 1 + m := by linarith
  by_cases hd : 0 ≤ d
  · -- `d ≥ 0`: multiply the sharp atom by `d`
    have hmain := two_mul_mul_sub_one_sub_ge_sqrt t m x y ht hm
    have hc1 : 4 * (Real.sqrt (t + 1) + Real.sqrt m) ^ 2 + 2 ≤ 10 * (t + 1 + m) := by
      nlinarith [hS]
    have hc2 : (1 / 4) * (Real.sqrt (t + 1) - Real.sqrt m) ^ 2 + 2 ≤ 10 * (t + 1 + m) := by
      nlinarith [hP]
    have hq1 : (4 * (Real.sqrt (t + 1) + Real.sqrt m) ^ 2 + 2) * x ^ 2 * d
        ≤ 10 * (t + 1 + m) * x ^ 2 * d :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc1 (sq_nonneg x)) hd
    have hq2 : ((1 / 4) * (Real.sqrt (t + 1) - Real.sqrt m) ^ 2 + 2) * y ^ 2 * d
        ≤ 10 * (t + 1 + m) * y ^ 2 * d :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc2 (sq_nonneg y)) hd
    rw [abs_of_nonneg hd]
    nlinarith [hmain, hq1, hq2]
  · -- `d < 0`: an *upper* bound on `2xy(t−1−m)` is what is needed
    have hdneg : d < 0 := not_le.mp hd
    have hxy : 2 * x * y ≤ x ^ 2 + y ^ 2 := by nlinarith [sq_nonneg (x - y)]
    have hup : 2 * x * y * (t - 1 - m) ≤ (x ^ 2 + y ^ 2) * (t + 1 + m) := by
      have h1 : 2 * x * y * (t - 1 - m) ≤ |2 * x * y * (t - 1 - m)| := le_abs_self _
      have h2a : |2 * x * y| ≤ x ^ 2 + y ^ 2 := by
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg (x - y), sq_nonneg (x + y)]
      have h2b : |t - 1 - m| ≤ t + 1 + m := by
        rw [abs_le]
        constructor <;> linarith
      have h2 : |2 * x * y * (t - 1 - m)| ≤ (x ^ 2 + y ^ 2) * (t + 1 + m) := by
        rw [abs_mul]
        exact mul_le_mul h2a h2b (abs_nonneg _) (by nlinarith [sq_nonneg x, sq_nonneg y])
      linarith
    have hC : 0 ≤ (x ^ 2 + y ^ 2) * (t + 1 + m) :=
      mul_nonneg (add_nonneg (sq_nonneg x) (sq_nonneg y)) (by linarith)
    have hkey : (-d) * (2 * x * y * (t - 1 - m))
        ≤ (x ^ 2 + y ^ 2) * (t + 1 + m) * (-d) := by
      have := mul_le_mul_of_nonneg_left hup (neg_nonneg.mpr hdneg.le)
      nlinarith [this]
    have hneg : 2 * x * y * d * (t - 1 - m) = -((-d) * (2 * x * y * (t - 1 - m))) := by ring
    rw [hneg, abs_of_neg hdneg]
    nlinarith [hkey, hC, hdneg]

/-! ## 2. The paired form: the two supplies -/

/-- **The AM–GM step in the paired (integrated) form.**  With `|I| ≤ √(A·B)` (the Cauchy–Schwarz
bound on the hop pairing, with the two `|δ|`-weighted masses), the hop coefficient `t − 1 − m` can
be paid by

    (t − 1 − m)·I ≥ −5·(t + 1 + m)·(A + B) ,

i.e. by `5(t+1+m)` times the *sum* of the two masses.  With `t = |p.1|` and `m = μV` this is FS's
`−4(n₀^{1/2}+(μV)^{1/2})²(…Q-side…) − ¼((n₀+1)^{1/2}−(μV)^{1/2})²(…P-side…)` up to the free
constant (the whole target `(★★)` has an existential `C`). -/
theorem hopAmgm_term {t m A B I : ℝ} (ht : 0 ≤ t) (hm : 0 ≤ m) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hI : |I| ≤ Real.sqrt (A * B)) :
    (t - 1 - m) * I ≥ -5 * (t + 1 + m) * (A + B) := by
  have h1 : (t - 1 - m) * I ≥ -|t - 1 - m| * |I| := by
    have h := neg_abs_le ((t - 1 - m) * I)
    rw [abs_mul] at h
    linarith
  have h2 : |t - 1 - m| * |I| ≤ |t - 1 - m| * Real.sqrt (A * B) :=
    mul_le_mul_of_nonneg_left hI (abs_nonneg _)
  have h3 : |t - 1 - m| ≤ 10 * (t + 1 + m) := by
    have : 1 ≤ t + 1 + m := by linarith
    rw [abs_le]
    constructor <;> linarith
  have h4 : Real.sqrt (A * B) ≤ (A + B) / 2 := by
    have hs : Real.sqrt (A * B) ^ 2 = A * B := Real.sq_sqrt (by positivity)
    have hnn : 0 ≤ A + B := by linarith
    have hsq : 4 * (Real.sqrt (A * B)) ^ 2 ≤ (A + B) ^ 2 := by
      nlinarith [sq_nonneg (A - B), hs]
    nlinarith [sq_nonneg (Real.sqrt (A * B) - (A + B) / 2), Real.sqrt_nonneg (A * B),
      hsq, hnn, hs]
  have h5 : |t - 1 - m| * Real.sqrt (A * B) ≤ 10 * (t + 1 + m) * ((A + B) / 2) := by
    calc |t - 1 - m| * Real.sqrt (A * B) ≤ (10 * (t + 1 + m)) * Real.sqrt (A * B) :=
          mul_le_mul_of_nonneg_right h3 (Real.sqrt_nonneg _)
      _ ≤ (10 * (t + 1 + m)) * ((A + B) / 2) :=
          mul_le_mul_of_nonneg_left h4 (by linarith)
  linarith

/-! ## 3. The `Finset` form -/

/-- **The AM–GM step summed over a hopping-pair family.**  For any finite index set `s` of hopping
pairs with coefficients `t p − 1 − m` and pairings `I p` obeying the Cauchy–Schwarz bound
`|I p| ≤ √(A p · B p)`, the whole sum is paid by `5` times the `(t+1+m)`-weighted sum of the two
masses. -/
theorem hopAmgm_sum {ι : Type*} (s : Finset ι) (t : ι → ℝ) (m : ℝ) (A B I : ι → ℝ)
    (ht : ∀ p ∈ s, 0 ≤ t p) (hm : 0 ≤ m) (hA : ∀ p ∈ s, 0 ≤ A p) (hB : ∀ p ∈ s, 0 ≤ B p)
    (hI : ∀ p ∈ s, |I p| ≤ Real.sqrt (A p * B p)) :
    ∑ p ∈ s, (t p - 1 - m) * I p
      ≥ -5 * ∑ p ∈ s, (t p + 1 + m) * (A p + B p) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun p hp => ?_
  have h := hopAmgm_term (t := t p) (m := m) (A := A p) (B := B p) (I := I p)
    (ht p hp) hm (hA p hp) (hB p hp) (hI p hp)
  linarith

/-- **The AM–GM step at the hopping-pair set of a slot**, with the coefficient dictionary
`t = |p.1|`, `m = μ·V`.

`hopPairSet i` is the set of disjoint pairs `(S,T)` with `i ∈ S`
(`Submission/Work/BoseFixB1S/HopDefs.lean`), i.e. exactly the index set of the hop expansion of
`Work.BoseFixB1S.boxCrossExpansionB1S`

    (V/2)(boxCrossPart − 2μ·Σᵢ∫qᵢfib(xᵢ)pᵢ) = ΣᵢΣ_{p∈hopPairSet i}(|p.1|−1−μV)∫ψ_{c_i(p)}δ(xᵢ)ψ_p .

The `A`-slot carries the *child* mass (`ψ_{c_i(p)}`, an excited block: bounded by the uniform fibre
bound), the `B`-slot the *parent* mass (`ψ_p`, a flat block: the sandwich turns the fibre weight
into the constant `κ = M₁/V`). -/
theorem hopAmgm_hopPairSet {N : ℕ} (i : Fin N) (μ V : ℝ) (hμVnn : 0 ≤ μ * V)
    {A B I : Finset (Fin N) × Finset (Fin N) → ℝ}
    (hA : ∀ p ∈ hopPairSet i, 0 ≤ A p) (hB : ∀ p ∈ hopPairSet i, 0 ≤ B p)
    (hI : ∀ p ∈ hopPairSet i, |I p| ≤ Real.sqrt (A p * B p)) :
    ∑ p ∈ hopPairSet i, ((p.1.card : ℝ) - 1 - μ * V) * I p
      ≥ -5 * ∑ p ∈ hopPairSet i, ((p.1.card : ℝ) + 1 + μ * V) * (A p + B p) :=
  hopAmgm_sum (hopPairSet i) (fun p => (p.1.card : ℝ)) (μ * V) A B I
    (fun _ _ => Nat.cast_nonneg _) hμVnn hA hB hI

/-! ## 4. The block moments of the demand, in the corpus's scalars

The AM–GM step above produces, on the **P-side** (the `B`-slot, the *parent* blocks `ψ_p`), the
weighted mass sum

`Σ_p |p.1|·(√(|p.1|+1) − √(μV))²·∫ψ_p²`   resp.   `Σ_p |p.1|·(|p.1| + 1 + μV)·∫ψ_p²`

over the three-way joint components `ψ_p = boxCompT V A p.1 p.2 Φ` (the extra factor `|p.1|` is the
`Σ_{i ∈ p.1}` from the hop index set).  These are *exactly* the corpus's scalars:

* `Σ_p |p.1|·∫ψ_p² = boxFlatCount = S` (`boxFlatCount_eq_sum_compT`), and
* `Σ_p |p.1|·(|p.1|−1)·∫ψ_p² = boxPairCount = Pc` (`boxPairCount_eq_sum_compT`),

so the second moment is the sum of the two:

    Σ_p |p.1|²·∫ψ_p² = Pc + S ,

and the *cubic* demand of the AM–GM is

    Σ_p |p.1|·(|p.1| + 1 + μV)·∫ψ_p² = Pc + (2 + μV)·S .

This is what makes the `M₁G`-slot of `(★★)` — `(M₁/V²)[¼(S+1−μV)² + μV]`, with `pcb` carrying
`½(M₂/V²)Pc − ½(M₁/V²)(S²−S)` — the *right* supply for the P-side: both are combinations of
`S`, `Pc` at the two degrees. -/

/-- **The second block moment is `boxPairCount + boxFlatCount`**: the demand `Σ|S|²∫Θ²` of the
AM–GM step, in the corpus's scalars.  (`Σ|S|²∫Θ² = Σ|S|(|S|−1)∫Θ² + Σ|S|∫Θ² = Pc + S`.) -/
theorem flatPieceRT_secondMoment_eq {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hVeq : V = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    (∑ p ∈ Work.BoseFixB1.disjPairs N, (p.1.card : ℝ) ^ 2 *
        ∫ x in Submission.BoseGases.abox N ℓ,
          (boxCompT V A p.1 p.2 Φ x) ^ 2)
      = boxPairCount V ℓ A Φ + boxFlatCount V ℓ A Φ := by
  have h2 := boxPairCount_eq_sum_compT (N := N) (ℓ := ℓ) (volA := V) hℓ hV hA hVeq hAc hΦc
  have h1 := boxFlatCount_eq_sum_compT (N := N) (ℓ := ℓ) (volA := V) hℓ hV hA hVeq hAc hΦc
  rw [h2, h1, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  ring

end Work.BoseFixB1S
