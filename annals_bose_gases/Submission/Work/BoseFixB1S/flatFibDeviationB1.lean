import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.boxMass_pos_of_goodSet
import Submission.Work.BoseFixB1.measurable_w1Fibre
import Submission.Work.BoseFixB1B.fibreDeviation_le_ae
import Submission.Work.BoseFixB1S.Gen.integrableOn_w1Fibre_dlBox
import Submission.Work.BoseFixB1S.fibreDeviation_factor
import Submission.Work.BoseFixB1S.integrableOn_chiSmallB_pow_dlBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.flatFibDeviationB1` — the exact fibre-deviation identity of the flat ledger

The ledger of the flat branch (`Work.BoseFixB1S.perBoxF_of_ledger_sharp`,
`Work.BoseFixB1.Up.perBoxF_of_ledger_delta`) consumes the "fibre row"

    `(fib)`   `μ·flatFibSum ≤ μ·W₁·τ·‖Φ‖² + Efib`,   `W₁ = w1MassB`, `τ = flatTau`.

This file isolates the *exact* content of that row.  With

    `fib(z) := w1Fibre ℓ (wSmall1Pair h M ℓ d u) z`   (the `y`-fibre of the localised kernel)
    `χ     := chiSmallB M ℓ d u`
    `κ     := chiMass M ℓ d u = ∫χ²`
    `W₁    := w1MassB h M ℓ d u = ∬wSmall1Pair`,
    `δ(z)  := fib(z) − (W₁/κ)·χ(z)²`   (**the deviation kernel**)

the row is *exactly* the statement `μ·∫Φ²Σᵢδ(xᵢ) ≤ Efib`:

* `fibDelta_sub_tauN` — the identity
  `flatFibSum − W₁·flatTau·normB = ∫_{abox}Φ²·Σᵢδ(xᵢ)`, valid whenever `normB ≠ 0`;
* `fibDelta_eq_zero_of_notMem_dlBox` — `δ` is supported in the sliding box `dlBox ℓ d u`
  (immediate from the PROVED factorisation `fibreDeviation_factor`);
* `fibDelta_mean_zero` — `∫_{dlBox}δ = 0`, the mean-zero property on which every
  Poincaré/amplitude estimate of the row rests;
* `flatFibDeviation_le` — the resulting deviation bound
  `∫Φ²Σδ ≤ D·(n₊ + 2·√(n₊·√S))` (an application of the PROVED
  `Work.BoseFixB1B.fibreDeviation_le`), and the two-term row
  `μ(flatFibSum − W₁·τ·N) ≤ μ·D·(Q + 2√Q√S)`.

## Why the identity matters (and which form of the row is *not* provable)

`fibDelta_sub_tauN` shows that the fibre row carries **no** information about the state's
density profile beyond `Σᵢδ(xᵢ)`: the "mean-field value" `μW₁τN` is exactly the `χ²`-weighted
average of the fibre, so the two cancel identically.  The residual is therefore a sum of
mean-zero one-body observables, and the only sharp estimates available are the amplitude ones
(`fibreDeviation_le`), which are linear in the *occupancy* `chiSum`, not in the `χ²`-weight `S`
(see `FINDING_flatFibDeviationB1.md` for the quantitative obstruction of the `D·S` branch of
the AM–GM split and for the payers that remain).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1S

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The deviation kernel `δ = fib − (W₁/κ)χ²` -/

/-- **The deviation kernel of the fibre row**: the difference between the `y`-fibre of the
localised kernel `wSmall1Pair` and its `χ²`-weighted mean value.  By
`Work.BoseFixB1S.fibreDeviation_factor` it factors as `χ·u` with
`u(z) = (K⋆χ)(z) − (W₁/κ)·χ(z)`, where `K` is the localised scattering kernel. -/
noncomputable def fibDelta {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ) (ℓ d : ℝ) (u : E3) :
    E3 → ℝ :=
  fun z => w1Fibre ℓ (wSmall1Pair h M ℓ d u) z
    - (w1MassB h M ℓ d u / chiMass M ℓ d u) * (chiSmallB M ℓ d u z) ^ 2

/-- **`δ` vanishes off the sliding box.**  Immediate from the PROVED
`fibreDeviation_factor`: the fibre is `χ(z)·(⋯)`, so it dies where `χ` does, and the second
term of `δ` is a multiple of `χ(z)²`. -/
theorem fibDelta_eq_zero_of_notMem_dlBox {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ}
    (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) {z : E3}
    (hz : z ∉ dlBox ℓ d u) : fibDelta h M ℓ d u z = 0 := by
  have hχ : chiSmallB M ℓ d u z = 0 := chiSmallB_eq_zero_of_notMem_dlBox hM hℓ hd u hz
  unfold fibDelta
  rw [fibreDeviation_factor h M ℓ d hℓ u z, hχ]
  ring

/-- **The factorisation of `δ`**: `δ = χ·u` with the state-free profile
`u(z) = (K⋆χ)(z) − (W₁/κ)·χ(z)`. -/
theorem fibDelta_eq_chi_mul {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (M : ℕ) (ℓ d : ℝ)
    (hℓ : 0 < ℓ) (u z : E3) :
    fibDelta h M ℓ d u z
      = chiSmallB M ℓ d u z
        * ((∫ y : E3, (wSmallScaled M (ℓ * d) (g0 v h) (z - y) / convScale ℓ (z - y))
              * chiSmallB M ℓ d u y)
            - (w1MassB h M ℓ d u / chiMass M ℓ d u) * chiSmallB M ℓ d u z) := by
  unfold fibDelta
  rw [fibreDeviation_factor h M ℓ d hℓ u z]
  ring

/-! ## 2. A slot-linear integral identity -/

/-- **Splitting `∫Φ²Σ(f − c·g)`.**  For integrable slot sums, the deviation of a sum of
one-body observables from a multiple of another is the difference of the two separate
integrals.  This is the pure integration step of the fibre row: with `f = fib`,
`g = χ²`, `c = W₁/κ` it converts `∫Φ²Σδ` into the ledger's combination
`flatFibSum − (W₁/κ)·flatScountB`. -/
theorem integralOn_sub_const_mul_sum {ℓ : ℝ} {n : ℕ} {f g : E3 → ℝ} {c : ℝ}
    {Φ : X n → ℝ}
    (hf : IntegrableOn (fun x : X n => (Φ x) ^ 2 * ∑ i : Fin n, f (x i)) (abox n ℓ))
    (hg : IntegrableOn (fun x : X n => (Φ x) ^ 2 * ∑ i : Fin n, g (x i)) (abox n ℓ)) :
    (∫ x in abox n ℓ, (Φ x) ^ 2 * ∑ i : Fin n, (f (x i) - c * g (x i)))
      = (∫ x in abox n ℓ, (Φ x) ^ 2 * ∑ i : Fin n, f (x i))
        - c * (∫ x in abox n ℓ, (Φ x) ^ 2 * ∑ i : Fin n, g (x i)) := by
  have hpt : ∀ x : X n, (Φ x) ^ 2 * ∑ i : Fin n, (f (x i) - c * g (x i))
      = (Φ x) ^ 2 * (∑ i : Fin n, f (x i)) - c * ((Φ x) ^ 2 * (∑ i : Fin n, g (x i))) := by
    intro x
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [show (∫ x in abox n ℓ, (Φ x) ^ 2 * ∑ i : Fin n, (f (x i) - c * g (x i)))
      = ∫ x in abox n ℓ,
          ((Φ x) ^ 2 * (∑ i : Fin n, f (x i)) - c * ((Φ x) ^ 2 * (∑ i : Fin n, g (x i)))) from
    integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_sub hf (hg.const_mul c), integral_const_mul]

/-! ## 3. The exact identity of the fibre row -/

/-- **The fibre row is exactly the deviation `∫Φ²Σδ`.**  With `κ = chiMass`, `W₁ = w1MassB`
and `δ = fibDelta`,

    `flatFibSum − W₁·flatTau·‖Φ‖² = ∫_{abox}Φ²·Σᵢδ(xᵢ)`.

The mean-field value `W₁·τ·‖Φ‖² = (W₁/κ)·flatScountB` is the `χ²`-weighted average of the
fibre, so the two cancel identically: the whole content of the fibre row is the deviation of
the *signed* sum `Σᵢδ(xᵢ)` from zero.  The integrability hypotheses are those of the two
integrals appearing in the ledger (`flatFibSum`'s and `flatScountB`'s). -/
theorem fibDelta_sub_tauN {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ} {u : E3}
    (Φ : X n → ℝ) (hN : flatMass (pL v μ) Φ ≠ 0)
    (hfib : IntegrableOn (fun x : X n =>
        (Φ x) ^ 2 * ∑ i : Fin n,
          w1Fibre (pL v μ) (wSmall1Pair h (pM v μ) (pL v μ) (pD v μ) u) (x i))
        (abox n (pL v μ)))
    (hχ : IntegrableOn (fun x : X n =>
        (Φ x) ^ 2 * ∑ i : Fin n,
          (chiSmallB (pM v μ) (pL v μ) (pD v μ) u (x i)) ^ 2)
        (abox n (pL v μ))) :
    flatFibSum h (pM v μ) (pL v μ) (pD v μ) u Φ
      - w1MassB h (pM v μ) (pL v μ) (pD v μ) u
        * flatTau (pM v μ) (pL v μ) (pD v μ) u Φ * normB v μ n Φ
      = ∫ x in abox n (pL v μ), (Φ x) ^ 2
          * ∑ i : Fin n, fibDelta h (pM v μ) (pL v μ) (pD v μ) u (x i) := by
  -- `flatTau·normB = flatScountB/chiMass`
  have hnorm : normB v μ n Φ = flatMass (pL v μ) Φ := rfl
  have hτ : flatTau (pM v μ) (pL v μ) (pD v μ) u Φ * normB v μ n Φ
      = flatScountB (pM v μ) (pL v μ) (pD v μ) u Φ / chiMass (pM v μ) (pL v μ) (pD v μ) u := by
    rw [flatTau, hnorm, div_mul_eq_mul_div, mul_div_mul_right _ _ hN]
  have hτ2 : w1MassB h (pM v μ) (pL v μ) (pD v μ) u
        * flatTau (pM v μ) (pL v μ) (pD v μ) u Φ * normB v μ n Φ
      = w1MassB h (pM v μ) (pL v μ) (pD v μ) u
        * (flatScountB (pM v μ) (pL v μ) (pD v μ) u Φ
            / chiMass (pM v μ) (pL v μ) (pD v μ) u) := by
    rw [mul_assoc, hτ]
  rw [hτ2, flatFibSum, flatScountB]
  simp only [nCountB]
  -- the linear combination, pulled into a single integral
  rw [show w1MassB h (pM v μ) (pL v μ) (pD v μ) u
        * ((∫ x in abox n (pL v μ), (Φ x) ^ 2 * ∑ i : Fin n,
              chiSmallB (pM v μ) (pL v μ) (pD v μ) u (x i) ^ 2)
            / chiMass (pM v μ) (pL v μ) (pD v μ) u)
      = (w1MassB h (pM v μ) (pL v μ) (pD v μ) u
          / chiMass (pM v μ) (pL v μ) (pD v μ) u)
        * (∫ x in abox n (pL v μ), (Φ x) ^ 2 * ∑ i : Fin n,
              chiSmallB (pM v μ) (pL v μ) (pD v μ) u (x i) ^ 2) from by
    rw [div_mul_eq_mul_div, mul_div_assoc]]
  rw [← integralOn_sub_const_mul_sum (f := fun z : E3 =>
        ∫ y in acube (pL v μ), wSmall1Pair h (pM v μ) (pL v μ) (pD v μ) u z y)
      (g := fun z : E3 => (chiSmallB (pM v μ) (pL v μ) (pD v μ) u z) ^ 2)
      (c := w1MassB h (pM v μ) (pL v μ) (pD v μ) u
        / chiMass (pM v μ) (pL v μ) (pD v μ) u) hfib hχ]
  simp only [fibDelta, w1Fibre]

/-! ## 4. The mean-zero property of `δ` -/

/-- **`δ` has mean zero on the sliding box.**  `∫_{B(u)}δ = ∫_{B(u)}fib − (W₁/κ)∫_{B(u)}χ²
= W₁ − (W₁/κ)·κ = 0`, by the PROVED mass identities
`Work.BoseFixB1S.fibreMass_eq_w1MassB` and `Work.BoseFixB1S.chiMass_eq_setIntegral_dlBox`.

The hypothesis `hκ : chiMass ≠ 0` is not redundant *at this level*: for the fully degenerate
boxes (`χ_{B(u)} ≡ 0`, i.e. `χ² < 1/2`-disjoint from the bump's support) both `chiMass` and
`w1MassB` vanish and the conclusion is still true, but the algebra below needs the split, and
`PerBoxF` is trivial there (`W₁ = 0` kills both the `F`-slot and the background).  The two
integrability hypotheses are those on which the mass identities rest; they are discharged from
`1 ≤ M` and the regime facts by the sibling `fibDelta_mean_zero_of_adm`. -/
theorem fibDelta_mean_zero {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3)
    (hκ : chiMass M ℓ d u ≠ 0)
    (hfib : IntegrableOn (fun z : E3 => w1Fibre ℓ (wSmall1Pair h M ℓ d u) z) (dlBox ℓ d u))
    (hχint : IntegrableOn (fun z : E3 => (chiSmallB M ℓ d u z) ^ 2) (dlBox ℓ d u)) :
    ∫ z in dlBox ℓ d u, fibDelta h M ℓ d u z = 0 := by
  have hw1 : ∫ z in dlBox ℓ d u, w1Fibre ℓ (wSmall1Pair h M ℓ d u) z
      = w1MassB h M ℓ d u := by
    have hpoint : ∀ z : E3, w1Fibre ℓ (wSmall1Pair h M ℓ d u) z
        = ∫ y : E3, wSmall1Pair h M ℓ d u z y := by
      intro z
      rw [w1Fibre]
      exact MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun y hy => by
        rw [wSmall1Pair, wSmallPair, chiSmallB_eq_zero_of_notMem_acube hℓ u hy, mul_zero])
    rw [show (∫ z in dlBox ℓ d u, w1Fibre ℓ (wSmall1Pair h M ℓ d u) z)
        = ∫ z in dlBox ℓ d u, (∫ y : E3, wSmall1Pair h M ℓ d u z y) from
      integral_congr_ae (Filter.Eventually.of_forall hpoint)]
    exact fibreMass_eq_w1MassB hM hℓ hd u
  have hκ' : ∫ z in dlBox ℓ d u, (chiSmallB M ℓ d u z) ^ 2 = chiMass M ℓ d u :=
    chiMass_eq_setIntegral_dlBox hM hℓ hd u
  simp only [fibDelta]
  rw [integral_sub hfib (hχint.const_mul _), integral_const_mul, hw1, hκ']
  rw [div_mul_cancel₀ _ hκ, sub_self]

/-! ## 5. The deviation bound and the fibre row -/

/-- **The fibre deviation bound**: the PROVED `Work.BoseFixB1B.fibreDeviation_le_ae` applied to
the deviation kernel `δ = fibDelta`, whose support and mean are supplied by
`fibDelta_eq_zero_of_notMem_dlBox` and `fibDelta_mean_zero`. -/
theorem flatFibDeviation_le {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M)
    {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (u : E3) (hV : 0 < boxMass ℓ d u)
    (hκ : chiMass M ℓ d u ≠ 0)
    (hfibint : IntegrableOn (fun z : E3 => w1Fibre ℓ (wSmall1Pair h M ℓ d u) z) (dlBox ℓ d u))
    (hχint : IntegrableOn (fun z : E3 => (chiSmallB M ℓ d u z) ^ 2) (dlBox ℓ d u))
    {n : ℕ} {Φ : X n → ℝ} (hΦc : Continuous Φ)
    (hδmeas : ∀ i : Fin n, MeasureTheory.AEStronglyMeasurable
      (fun x : X n => fibDelta h M ℓ d u (x i))
      ((MeasureTheory.volume : MeasureTheory.Measure (X n)).restrict (abox n ℓ)))
    {D : ℝ} (hD : ∀ z : E3, |fibDelta h M ℓ d u z| ≤ D) :
    (∫ x in abox n ℓ, (Φ x) ^ 2 * ∑ i : Fin n, fibDelta h M ℓ d u (x i))
      ≤ D * (Work.UBBInputs8.cnPlusBoxInd ℓ (dlBox ℓ d u) (boxMass ℓ d u) Φ
              + 2 * Real.sqrt (Work.UBBInputs8.cnPlusBoxInd ℓ (dlBox ℓ d u) (boxMass ℓ d u) Φ)
                  * Real.sqrt (boxFlatCount (boxMass ℓ d u) ℓ (dlBox ℓ d u) Φ)) := by
  have hAc : dlBox ℓ d u ⊆ acube ℓ := dlBox_subset_acube ℓ d u
  refine Work.BoseFixB1B.fibreDeviation_le_ae (N := n) (ℓ := ℓ)
    (V := boxMass ℓ d u) hℓ hV (measurableSet_dlBox ℓ d u) hAc hδmeas
    (fun z hz => fibDelta_eq_zero_of_notMem_dlBox h hM hℓ hd u hz)
    (fibDelta_mean_zero h hM hℓ hd u hκ hfibint hχint) hD hΦc

/-- **The fibre row of the flat ledger, in the deviation form.**  Combining the exact identity
`fibDelta_sub_tauN` with the deviation bound `flatFibDeviation_le`:

    `μ·(flatFibSum − W₁·τ·‖Φ‖²) ≤ μ·D·(n₊ + 2√(n₊)·√(boxFlatCount))`.

This is the *whole* analytic content of the row: no mean-field cancellation is left.  The
residual question — which of the available payers can absorb the right-hand side with an
`n`-free constant — is analysed in `FINDING_flatFibDeviationB1.md`. -/
theorem flatFib_row_deviation {v : E3 → ℝ} {h : Work.UBB.ScatSol v}
    {μ : ℝ} (hμ : 0 ≤ μ) (hM : 1 ≤ pM v μ) {n : ℕ} {u : E3} (hℓ : 0 < pL v μ) (hd : 0 < pD v μ)
    (hV : 0 < boxMass (pL v μ) (pD v μ) u)
    (hκ : chiMass (pM v μ) (pL v μ) (pD v μ) u ≠ 0)
    {Φ : X n → ℝ} (hΦc : Continuous Φ)
    (hN : flatMass (pL v μ) Φ ≠ 0)
    (hfibint : IntegrableOn (fun x : X n => (Φ x) ^ 2 * ∑ i : Fin n,
        w1Fibre (pL v μ) (wSmall1Pair h (pM v μ) (pL v μ) (pD v μ) u) (x i)) (abox n (pL v μ)))
    (hχint : IntegrableOn (fun x : X n => (Φ x) ^ 2 * ∑ i : Fin n,
        (chiSmallB (pM v μ) (pL v μ) (pD v μ) u (x i)) ^ 2) (abox n (pL v μ)))
    (hfibintz : IntegrableOn (fun z : E3 => w1Fibre (pL v μ)
        (wSmall1Pair h (pM v μ) (pL v μ) (pD v μ) u) z)
        (dlBox (pL v μ) (pD v μ) u))
    (hχintz : IntegrableOn (fun z : E3 => (chiSmallB (pM v μ) (pL v μ) (pD v μ) u z) ^ 2)
        (dlBox (pL v μ) (pD v μ) u))
    (hδmeas : ∀ i : Fin n, MeasureTheory.AEStronglyMeasurable
      (fun x : X n => fibDelta h (pM v μ) (pL v μ) (pD v μ) u (x i))
      ((MeasureTheory.volume : MeasureTheory.Measure (X n)).restrict (abox n (pL v μ))))
    {D : ℝ} (hD : ∀ z : E3, |fibDelta h (pM v μ) (pL v μ) (pD v μ) u z| ≤ D) :
    μ * (flatFibSum h (pM v μ) (pL v μ) (pD v μ) u Φ
        - w1MassB h (pM v μ) (pL v μ) (pD v μ) u
          * flatTau (pM v μ) (pL v μ) (pD v μ) u Φ * normB v μ n Φ)
      ≤ μ * (D * (Work.UBBInputs8.cnPlusBoxInd (pL v μ) (dlBox (pL v μ) (pD v μ) u)
                (boxMass (pL v μ) (pD v μ) u) Φ
              + 2 * Real.sqrt (Work.UBBInputs8.cnPlusBoxInd (pL v μ) (dlBox (pL v μ) (pD v μ) u)
                    (boxMass (pL v μ) (pD v μ) u) Φ)
                  * Real.sqrt (boxFlatCount (boxMass (pL v μ) (pD v μ) u) (pL v μ)
                      (dlBox (pL v μ) (pD v μ) u) Φ))) := by
  have hid := fibDelta_sub_tauN (h := h) (μ := μ) (u := u) (Φ := Φ) hN hfibint hχint
  have hbd := flatFibDeviation_le (M := pM v μ) h hM hℓ hd u hV hκ hfibintz hχintz hΦc hδmeas hD
  rw [hid]
  exact mul_le_mul_of_nonneg_left hbd hμ

/-! ## 6. The row arithmetic: which payers absorb the deviation

The deviation bound of §5 leaves the right-hand side `μ·D·(Q + 2√Q√S)`.  This section records the
pure-real fact that it *is* absorbable by the Δ-augmented budget's own payers — the kinetic/`ε_T`
slot `K·μ·a·Q` for the `Q`-part, and the slack `W₁·(τ−μ)²N` resp. the pair-condensate surplus
`Δ = ½(W₂−W₁)(τ²N+V)` for the `S`-part — **provided** the two *state-free* ratio inputs

    `W₁ ≥ (64/7)·D·κ`   and   `W₂ − W₁ ≥ 32·D·κ`   (`κ = chiMass`, `D = sup|δ|`)

hold.  These are *ratio* statements about the bump `χ`, the kernel `K` and the potential `v` alone;
they are the correct replacement of the **false** absolute lower bound
`W₁ ≥ c·(a v)·κ` of `Work.BoseFixB1.w1MassB_ge_const_mul_chiMass` (refuted at grazing boxes, where
`W₁ = 0` *and* `D = 0`, so the ratio survives).  Note that `τ ≥ μ/2` and `τ < 2μ/1` are handled by
`Δ`, and only the low-density regime `τ < μ/2` uses the slack: **no `n`-free error constant is
needed**, which is why the quantifier order of `PerBoxFlatFree` is not an obstruction here. -/

/-- **The arithmetic of the fibre row.**  With `S = τ·κ·N` (the definition of the mean smooth
density `τ = scountB/(κ‖Φ‖²)`) and the two state-free ratio inputs, the whole fibre deviation is
absorbed by `2D/a` times the kinetic slot, half the slack and half the pair-condensate surplus. -/
theorem fibRowArith {μ D a Q S κ W₁ W₂ τ N V Δ : ℝ}
    (hμ : 0 < μ) (ha : 0 < a) (hD : 0 ≤ D) (hQ : 0 ≤ Q) (hS : 0 ≤ S)
    (hκ : 0 < κ) (hN : 0 < N) (hV : 0 ≤ V)
    (hSτ : S = τ * κ * N) (hΔnn : 0 ≤ Δ)
    (hW₁ : (64 / 7) * D * κ ≤ W₁)
    (hW₂ : 32 * D * κ ≤ W₂ - W₁)
    (hΔ : Δ = (1 / 2) * (W₂ - W₁) * (τ ^ 2 * N + V)) :
    μ * (D * (Q + 2 * Real.sqrt Q * Real.sqrt S))
      ≤ (2 * D / a) * (μ * a * Q)
        + (1 / 2) * W₁ * ((τ - μ) ^ 2 * N * (7 / 16) + V / 4) + (1 / 2) * Δ := by
  have hDκ : 0 ≤ D * κ := mul_nonneg hD hκ.le
  have hτ0 : 0 ≤ τ := by
    have h1 : 0 ≤ τ * κ * N := by rw [← hSτ]; exact hS
    by_contra hlt
    push_neg at hlt
    have h2 : τ * κ * N < 0 := by
      have h3 : τ * κ < 0 := mul_neg_of_neg_of_pos hlt hκ
      exact mul_neg_of_neg_of_pos h3 hN
    linarith
  have hW₁0 : 0 ≤ W₁ := le_trans (by nlinarith [hDκ]) hW₁
  have hsqrt : 2 * Real.sqrt Q * Real.sqrt S ≤ Q + S := by
    nlinarith [sq_nonneg (Real.sqrt Q - Real.sqrt S), Real.sq_sqrt hQ, Real.sq_sqrt hS]
  -- the `Q`-slot is paid by `(2D/a)·μ·a·Q`, with equality
  have hQeq : μ * (D * (2 * Q)) = (2 * D / a) * (μ * a * Q) := by
    field_simp
  -- the `S`-slot: the slack in the low-density regime, `Δ` above it
  have hSpart : μ * (D * S)
      ≤ (1 / 2) * W₁ * ((τ - μ) ^ 2 * N * (7 / 16) + V / 4) + (1 / 2) * Δ := by
    rw [hSτ]
    by_cases hcase : τ < μ / 2
    · -- low density: the slack
      have hA : μ * (D * (τ * κ * N)) ≤ μ * (D * (μ / 2 * κ * N)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_of_lt hcase) hκ.le) hN.le) hD) hμ.le
      have hB : (1 / 2) * W₁ * (μ ^ 2 / 4 * N * (7 / 16))
          ≤ (1 / 2) * W₁ * ((τ - μ) ^ 2 * N * (7 / 16) + V / 4) := by
        have h5 : μ / 2 ≤ μ - τ := by linarith
        have h6 : 0 ≤ μ / 2 := by linarith
        have h7 : μ / 2 * (μ / 2) ≤ (μ - τ) * (μ - τ) := mul_self_le_mul_self h6 h5
        have h2 : μ ^ 2 / 4 * N * (7 / 16) ≤ (τ - μ) ^ 2 * N * (7 / 16) := by
          have h8 : μ ^ 2 / 4 = μ / 2 * (μ / 2) := by ring
          have h9 : (μ - τ) * (μ - τ) = (τ - μ) ^ 2 := by ring
          rw [h8, ← h9]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h7 hN.le) (by norm_num)
        have h3 : 0 ≤ (1 / 2) * W₁ := by positivity
        have h10 : (τ - μ) ^ 2 * N * (7 / 16)
            ≤ (τ - μ) ^ 2 * N * (7 / 16) + V / 4 := by linarith [hV]
        exact mul_le_mul_of_nonneg_left (by linarith) h3
      have hC : μ * (D * (μ / 2 * κ * N))
          ≤ (1 / 2) * W₁ * (μ ^ 2 / 4 * N * (7 / 16)) := by
        have h6 := mul_le_mul_of_nonneg_right hW₁
          (show (0:ℝ) ≤ μ ^ 2 / 4 * N * (7 / 16) by positivity)
        have h8 : μ * (D * (μ / 2 * κ * N))
            = (1 / 2) * (((64 / 7) * D * κ) * (μ ^ 2 / 4 * N * (7 / 16))) := by
          field_simp
          ring
        have h9 : (1 / 2) * (W₁ * (μ ^ 2 / 4 * N * (7 / 16)))
            = (1 / 2) * W₁ * (μ ^ 2 / 4 * N * (7 / 16)) := by ring
        rw [h8, ← h9]
        exact mul_le_mul_of_nonneg_left h6 (by norm_num)
      linarith [hA, hB, hC]
    · -- density at least `μ/2`: the pair-condensate surplus
      push_neg at hcase
      have hμτ : μ ≤ 8 * τ := by nlinarith [hcase, hτ0]
      have hkey : μ * (D * (τ * κ * N)) ≤ 8 * D * κ * (τ ^ 2 * N) := by
        have h9 : μ * (D * κ * τ * N) ≤ (8 * τ) * (D * κ * τ * N) :=
          mul_le_mul_of_nonneg_right hμτ (by positivity)
        nlinarith [h9]
      have hΔbig : 8 * D * κ * (τ ^ 2 * N) ≤ (1 / 2) * Δ := by
        rw [hΔ]
        have hW2nn : 0 ≤ W₂ - W₁ := by linarith [hW₂, hDκ]
        have h10 : (W₂ - W₁) * (τ ^ 2 * N) ≤ (W₂ - W₁) * (τ ^ 2 * N + V) :=
          mul_le_mul_of_nonneg_left (by linarith [hV]) hW2nn
        have h11 : (32 * D * κ) * (τ ^ 2 * N) ≤ (W₂ - W₁) * (τ ^ 2 * N) :=
          mul_le_mul_of_nonneg_right hW₂ (by positivity)
        nlinarith [h10, h11]
      have hother : (0:ℝ) ≤ (1 / 2) * W₁ * ((τ - μ) ^ 2 * N * (7 / 16) + V / 4) := by
        have h12 : (0:ℝ) ≤ (τ - μ) ^ 2 * N * (7 / 16) + V / 4 := by positivity
        exact mul_nonneg (by positivity) h12
      linarith [hkey, hΔbig, hother]
  have hmain : μ * (D * (Q + 2 * Real.sqrt Q * Real.sqrt S)) ≤ μ * (D * (2 * Q + S)) := by
    have h1 : D * (Q + 2 * Real.sqrt Q * Real.sqrt S) ≤ D * (Q + (Q + S)) :=
      mul_le_mul_of_nonneg_left (by linarith) hD
    exact mul_le_mul_of_nonneg_left (by linarith) hμ.le
  have hsplit : μ * (D * (2 * Q + S)) = μ * (D * (2 * Q)) + μ * (D * S) := by ring
  rw [hsplit] at hmain
  linarith [hmain, hQeq, hSpart]

/-- **The arithmetic of the fibre row with a *count comparison* instead of the identity
`S = τ·κ·N`.**  This is the form the corpus's rows actually have: the PROVED
`fibreDeviation_le_ae` measures the deviation with the *box-projected* count `S = boxFlatCount`,
while the ledger's mean smooth density `τ` is `flatScountB/(κ‖Φ‖²)`; the two are related by a *state*
count comparison `S ≤ Cs·τκN` (with `Cs` a free constant, absorbed into the two ratio inputs).
Nothing else changes: the `Q`-slot is still paid by `(2D/a)·μaQ` and the `S`-slot by the slack /
the pair-condensate surplus, with the ratio constants inflated by `Cs`. -/
theorem fibRowArith_le {μ D a Q S κ W₁ W₂ τ N V Δ Cs : ℝ}
    (hμ : 0 < μ) (ha : 0 < a) (hD : 0 ≤ D) (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hCs : 0 ≤ Cs)
    (hκ : 0 < κ) (hN : 0 < N) (hV : 0 ≤ V) (hτ0 : 0 ≤ τ) (hΔnn : 0 ≤ Δ)
    (hSτ : S ≤ Cs * (τ * κ * N))
    (hW₁ : (64 / 7) * Cs * D * κ ≤ W₁)
    (hW₂ : 32 * Cs * D * κ ≤ W₂ - W₁)
    (hΔ : Δ = (1 / 2) * (W₂ - W₁) * (τ ^ 2 * N + V)) :
    μ * (D * (Q + 2 * Real.sqrt Q * Real.sqrt S))
      ≤ (2 * D / a) * (μ * a * Q)
        + (1 / 2) * W₁ * ((τ - μ) ^ 2 * N * (7 / 16) + V / 4) + (1 / 2) * Δ := by
  have hCsD : 0 ≤ Cs * D := mul_nonneg hCs hD
  have hCκ : 0 ≤ Cs * D * κ := mul_nonneg hCsD hκ.le
  have hsqrt : 2 * Real.sqrt Q * Real.sqrt S ≤ Q + S := by
    nlinarith [sq_nonneg (Real.sqrt Q - Real.sqrt S), Real.sq_sqrt hQ, Real.sq_sqrt hS]
  have hQeq : μ * (D * (2 * Q)) = (2 * D / a) * (μ * a * Q) := by
    field_simp
  -- the `S`-slot, at the inflated coefficient `Cs·D`
  have hSpart : μ * (D * S)
      ≤ (1 / 2) * W₁ * ((τ - μ) ^ 2 * N * (7 / 16) + V / 4) + (1 / 2) * Δ := by
    have hstep : μ * (D * S) ≤ μ * (D * (Cs * (τ * κ * N))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSτ hD) hμ.le
    have hred : μ * (D * (Cs * (τ * κ * N))) = μ * ((Cs * D) * (τ * κ * N)) := by ring
    rw [hred] at hstep
    have hcore : μ * ((Cs * D) * (τ * κ * N))
        ≤ (1 / 2) * W₁ * ((τ - μ) ^ 2 * N * (7 / 16) + V / 4) + (1 / 2) * Δ := by
      by_cases hcase : τ < μ / 2
      · -- low density: the slack
        have hA : μ * ((Cs * D) * (τ * κ * N)) ≤ μ * ((Cs * D) * (μ / 2 * κ * N)) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (le_of_lt hcase) hκ.le) hN.le) hCsD) hμ.le
        have hB : (1 / 2) * W₁ * (μ ^ 2 / 4 * N * (7 / 16))
            ≤ (1 / 2) * W₁ * ((τ - μ) ^ 2 * N * (7 / 16) + V / 4) := by
          have h5 : μ / 2 ≤ μ - τ := by linarith
          have h6 : 0 ≤ μ / 2 := by linarith
          have h7 : μ / 2 * (μ / 2) ≤ (μ - τ) * (μ - τ) := mul_self_le_mul_self h6 h5
          have h2 : μ ^ 2 / 4 * N * (7 / 16) ≤ (τ - μ) ^ 2 * N * (7 / 16) := by
            have h8 : μ ^ 2 / 4 = μ / 2 * (μ / 2) := by ring
            have h9 : (μ - τ) * (μ - τ) = (τ - μ) ^ 2 := by ring
            rw [h8, ← h9]
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h7 hN.le) (by norm_num)
          have h3 : 0 ≤ (1 / 2) * W₁ := by
            have h14 : (0:ℝ) ≤ W₁ := le_trans (by positivity) hW₁
            positivity
          have h10 : (τ - μ) ^ 2 * N * (7 / 16)
              ≤ (τ - μ) ^ 2 * N * (7 / 16) + V / 4 := by linarith [hV]
          exact mul_le_mul_of_nonneg_left (by linarith) h3
        have hC : μ * ((Cs * D) * (μ / 2 * κ * N))
            ≤ (1 / 2) * W₁ * (μ ^ 2 / 4 * N * (7 / 16)) := by
          have h6 := mul_le_mul_of_nonneg_right hW₁
            (show (0:ℝ) ≤ μ ^ 2 / 4 * N * (7 / 16) by positivity)
          have h8 : μ * ((Cs * D) * (μ / 2 * κ * N))
              = (1 / 2) * (((64 / 7) * Cs * D * κ) * (μ ^ 2 / 4 * N * (7 / 16))) := by
            field_simp
            ring
          have h9 : (1 / 2) * (W₁ * (μ ^ 2 / 4 * N * (7 / 16)))
              = (1 / 2) * W₁ * (μ ^ 2 / 4 * N * (7 / 16)) := by ring
          rw [h8, ← h9]
          exact mul_le_mul_of_nonneg_left h6 (by norm_num)
        linarith [hA, hB, hC]
      · -- density at least `μ/2`: the pair-condensate surplus
        push_neg at hcase
        have hμτ : μ ≤ 8 * τ := by nlinarith [hcase, hτ0]
        have hkey : μ * ((Cs * D) * (τ * κ * N)) ≤ 8 * (Cs * D) * κ * (τ ^ 2 * N) := by
          have h9 : μ * (Cs * D * κ * τ * N) ≤ (8 * τ) * (Cs * D * κ * τ * N) :=
            mul_le_mul_of_nonneg_right hμτ (by positivity)
          nlinarith [h9]
        have hΔbig : 8 * (Cs * D) * κ * (τ ^ 2 * N) ≤ (1 / 2) * Δ := by
          rw [hΔ]
          have hW2nn : 0 ≤ W₂ - W₁ := by linarith [hW₂, hCκ]
          have h10 : (W₂ - W₁) * (τ ^ 2 * N) ≤ (W₂ - W₁) * (τ ^ 2 * N + V) :=
            mul_le_mul_of_nonneg_left (by linarith [hV]) hW2nn
          have h11 : (32 * Cs * D * κ) * (τ ^ 2 * N) ≤ (W₂ - W₁) * (τ ^ 2 * N) :=
            mul_le_mul_of_nonneg_right hW₂ (by positivity)
          nlinarith [h10, h11]
        have hother : (0:ℝ) ≤ (1 / 2) * W₁ * ((τ - μ) ^ 2 * N * (7 / 16) + V / 4) := by
          have h12 : (0:ℝ) ≤ (τ - μ) ^ 2 * N * (7 / 16) + V / 4 := by positivity
          have h13 : (0:ℝ) ≤ W₁ := le_trans (by positivity) hW₁
          exact mul_nonneg (by positivity) h12
        linarith [hkey, hΔbig, hother]
    linarith [hstep, hcore]
  have hmain : μ * (D * (Q + 2 * Real.sqrt Q * Real.sqrt S)) ≤ μ * (D * (2 * Q + S)) := by
    have h1 : D * (Q + 2 * Real.sqrt Q * Real.sqrt S) ≤ D * (Q + (Q + S)) :=
      mul_le_mul_of_nonneg_left (by linarith) hD
    exact mul_le_mul_of_nonneg_left (by linarith) hμ.le
  have hsplit : μ * (D * (2 * Q + S)) = μ * (D * (2 * Q)) + μ * (D * S) := by ring
  rw [hsplit] at hmain
  linarith [hmain, hQeq, hSpart]

/-! ## 7. The side conditions of the row, at FS's regime

The row `flatFib_row_deviation` carries four side conditions (the a.e. measurability of the slot
maps of `δ`, the integrability of the fibre and of `χ²` on the sliding box, and the integrability
of the `χ²`-weighted count on the ambient box).  All four are *ambient* facts — they do not depend
on the ledger — and all four are available in the corpus; this section packages them. -/

/-- **The four side conditions of the fibre row** at FS's regime (`R ≤ ℓd/16`, `R ≤ ℓ·chiR0`),
for an arbitrary continuous state.  Conjuncts 1–3 are the corpus's
`Work.BoseFixB1.measurable_w1Fibre`, `Work.BoseFixB1S.Gen.integrableOn_w1Fibre_dlBox` and
`Work.BoseFixB1S.integrableOn_chiSmallB_pow_dlBox` (plus the continuity of `χ`); conjunct 4 is
integrability of a continuous function on the compact box `abox n ℓ`. -/
theorem flatFibDeviation_side_conditions {v : E3 → ℝ} (h : Work.UBB.ScatSol v) {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R0) (hR0 : 0 < R0) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R0 ≤ ℓ * d / 16) (hRχ : R0 ≤ Submission.BoseGases.chiR0 * ℓ)
    (u : E3) {n : ℕ} {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    (∀ i : Fin n, MeasureTheory.AEStronglyMeasurable
        (fun x : Submission.BoseGases.X n => fibDelta h M ℓ d u (x i))
        ((MeasureTheory.volume : MeasureTheory.Measure (Submission.BoseGases.X n)).restrict
          (Submission.BoseGases.abox n ℓ)))
    ∧ MeasureTheory.IntegrableOn (fun z : E3 => Submission.BoseGases.w1Fibre ℓ
        (Submission.BoseGases.wSmall1Pair h M ℓ d u) z) (Submission.BoseGases.dlBox ℓ d u)
    ∧ MeasureTheory.IntegrableOn (fun z : E3 => (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2)
        (Submission.BoseGases.dlBox ℓ d u)
    ∧ MeasureTheory.IntegrableOn (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * ∑ i : Fin n,
        (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2)
        (Submission.BoseGases.abox n ℓ) := by
  have hχcont : Continuous (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z) := by
    rw [show (fun z : E3 => Submission.BoseGases.chiSmallB M ℓ d u z)
        = fun z => Submission.BoseGases.chiScale ℓ z
            * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • z - u) from by
      funext z; rw [Submission.BoseGases.chiSmallB]]
    exact (Submission.BoseGases.chiScale_continuous ℓ).mul
      ((Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop))
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    have hfib : Measurable (fun z : E3 => Submission.BoseGases.w1Fibre ℓ
        (Submission.BoseGases.wSmall1Pair h M ℓ d u) z) :=
      Work.BoseFixB1.measurable_w1Fibre hv_supp hR0 hv hvrad hv1 h hM hℓ hd u
    have hδm : Measurable (fibDelta h M ℓ d u) := by
      have h2 : Measurable (fun z : E3 => (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2) :=
        (hχcont.pow 2).measurable
      have h3 : Measurable (fun z : E3 => (Work.BoseFixB1.w1MassB h M ℓ d u
          / Work.SmallBoxSliding.chiMass M ℓ d u) * (Submission.BoseGases.chiSmallB M ℓ d u z) ^ 2) :=
        h2.const_mul _
      unfold fibDelta
      exact hfib.sub h3
    exact ((hδm.comp (continuous_apply i).measurable).aestronglyMeasurable).mono_measure
      Measure.restrict_le_self
  · exact Work.BoseFixB1S.Gen.integrableOn_w1Fibre_dlBox hv_supp hR0 hv hvrad hv1 h hM hℓ hd
      hR (by rwa [mul_comm] at hRχ) u
  · exact Work.BoseFixB1S.integrableOn_chiSmallB_pow_dlBox hM hℓ hd u 2
  · have hcont : Continuous (fun x : Submission.BoseGases.X n => (Φ x) ^ 2 * ∑ i : Fin n,
        (Submission.BoseGases.chiSmallB M ℓ d u (x i)) ^ 2) := by
      refine (hΦc.pow 2).mul (continuous_finsetSum _ ?_)
      intro i _
      exact (hχcont.comp (continuous_apply i)).pow 2
    exact hcont.continuousOn.integrableOn_compact (abox_compact n hℓ)



/-! ## 8. The row at the target's vocabulary (`Adm`, `BoxState`, `goodSet`)

The assembly of `flatFib_row_deviation` + `fibRowArith_le` + `flatFibDeviation_side_conditions` at
FS's parameters.  Two *state-level* inputs remain visible, and they are the honest residual of this
chapter:

* `hcount` — the **count comparison** `boxFlatCount ≤ Cs·(τκN)` between the *box-projected* count
  (which the deviation bound carries) and the *smooth* count (which defines `τ`).  This is the
  precise location of the chapter's count cap;
* `hD` + the two **ratio inputs** `hW₁`, `hW₂` — see the FINDING §6 for their state-free proof.

Everything else is proved: the identity `fibDelta_sub_tauN`, the deviation bound
`fibDelta_le_ae`/`flatFib_row_deviation`, the arithmetic `fibRowArith_le`, the four side
conditions `flatFibDeviation_side_conditions`, and the regime/nondegeneracy plumbing. -/
theorem flatFib_row_adm {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    {ε₀ μ : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ)
    (hreg : R ≤ Work.BoseFixB1.pL v μ * Work.BoseFixB1.pD v μ / 16
      ∧ R ≤ Work.BoseFixB1.pL v μ * Submission.BoseGases.chiR0)
    {n : ℕ} {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))}
    {u : E3} (hu : u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ)
    (hN : Work.BoseFixB1.flatMass (Work.BoseFixB1.pL v μ) (Φ : Submission.BoseGases.X n → ℝ) ≠ 0)
    (hκ : Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u ≠ 0)
    {D Cs : ℝ} (hD : ∀ z : E3, |fibDelta h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
        (Work.BoseFixB1.pD v μ) u z| ≤ D)
    (hCs : 0 ≤ Cs)
    (hcount : Work.BoseFixB1S.boxFlatCount
        (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
        (Work.BoseFixB1.pL v μ) (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ)
          (Work.BoseFixB1.pD v μ) u) (Φ : Submission.BoseGases.X n → ℝ)
      ≤ Cs * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
          * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)))
    (hW₁ : (64 / 7) * Cs * D * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ)
        (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u
        ≤ Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u)
    (hW₂ : 32 * Cs * D * Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ)
        (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u
        ≤ Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u
          - Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u) :
    μ * (Work.BoseFixB1.flatFibSum h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
            (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
          - Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u
            * Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ)
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
      ≤ (2 * D / (_root_.BoseGases.a v))
          * (μ * (_root_.BoseGases.a v)
              * Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.pL v μ)
                  (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                  (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
                  (Φ : Submission.BoseGases.X n → ℝ))
        + (1 / 2) * Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
              (Work.BoseFixB1.pD v μ) u
            * ((Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) - μ) ^ 2
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) * (7 / 16)
              + Work.BoseFixB1.Up.flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u / 4)
        + (1 / 2) * ((1 / 2) * (Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ)
                (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u
              - Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                  (Work.BoseFixB1.pD v μ) u)
            * (Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
                    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              + Work.BoseFixB1.Up.flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)) := by
  obtain ⟨hR16, hRχ⟩ := hreg
  have hμ : 0 < μ := hAdm.1
  have ha : 0 < _root_.BoseGases.a v := hav
  have hℓ : 0 < Work.BoseFixB1.pL v μ := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < Work.BoseFixB1.pD v μ := Work.BoseFixB1.adm_d_pos hAdm
  have hM1 : 1 ≤ Work.BoseFixB1.pM v μ := by
    change 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
    rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  have hΦc : Continuous (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff.continuous
  set kappa : ℝ := Work.SmallBoxSliding.chiMass (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
    (Work.BoseFixB1.pD v μ) u with hkdef
  set W1 : ℝ := Work.BoseFixB1.w1MassB h (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
    (Work.BoseFixB1.pD v μ) u with hW1def
  set W2 : ℝ := Work.BoseFixB1.flatPairMass v (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
    (Work.BoseFixB1.pD v μ) u with hW2def
  set N : ℝ := Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) with hNdef
  set S : ℝ := Work.BoseFixB1S.boxFlatCount
    (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
    (Work.BoseFixB1.pL v μ) (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ)
      (Work.BoseFixB1.pD v μ) u) (Φ : Submission.BoseGases.X n → ℝ) with hSdef
  set tau : ℝ := Work.BoseFixB1.flatTau (Work.BoseFixB1.pM v μ) (Work.BoseFixB1.pL v μ)
    (Work.BoseFixB1.pD v μ) u (Φ : Submission.BoseGases.X n → ℝ) with htdef
  set V : ℝ := Work.BoseFixB1.Up.flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u with hVdef
  set Q : ℝ := Work.UBBInputs8.cnPlusBoxInd (Work.BoseFixB1.pL v μ)
    (Submission.BoseGases.dlBox (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
    (Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u)
    (Φ : Submission.BoseGases.X n → ℝ) with hQdef
  obtain ⟨hδmeas, hfibintz, hχintz, hχint⟩ :=
    flatFibDeviation_side_conditions h hv_supp hR hv hvrad hv1 hM1 hℓ hd hR16
      (by rwa [mul_comm] at hRχ) u hΦc
  have hfibint := Work.BoseFixB1.integrableOn_fibSumIntegrand (h := h) hv_supp hR hv hvrad hM1
    hℓ hd hR16 hRχ u hΦc
  have hVpos : 0 < Work.SmallBoxSliding.boxMass (Work.BoseFixB1.pL v μ) (Work.BoseFixB1.pD v μ) u :=
    Work.BoseFixB1.boxMass_pos_of_goodSet hℓ hd hμ hu
  have hrow := flatFib_row_deviation (h := h) (u := u) (μ := μ) hμ.le hM1 hℓ hd hVpos hκ hΦc hN
    hfibint hχint hfibintz hχintz hδmeas (D := D) hD
  have hDnn : 0 ≤ D := le_trans (abs_nonneg _) (hD 0)
  have hQnn : 0 ≤ Q := by
    rw [hQdef, Work.UBBInputs8.cnPlusBoxInd]
    exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  have hSnn : 0 ≤ S := by
    rw [hSdef, Work.BoseFixB1S.boxFlatCount]
    exact Finset.sum_nonneg fun i _ => integral_nonneg fun x => sq_nonneg _
  have hNpos : 0 < N := by
    rw [hNdef]
    exact lt_of_le_of_ne (Work.BoseFixB1.normB_nonneg _) (Ne.symm hN)
  have hκpos : 0 < kappa := by
    rw [hkdef]
    exact lt_of_le_of_ne (Work.SmallBoxSliding.chiMass_nonneg _ _ _ _) (Ne.symm hκ)
  have hVnn : 0 ≤ V := by
    rw [hVdef]; exact Work.BoseFixB1.Up.flatVar_nonneg hΦc hNpos u
  have hτ0 : 0 ≤ tau := by
    rw [htdef, Work.BoseFixB1.flatTau]
    refine div_nonneg ?_ ?_
    · rw [Work.BoseFixB1.flatScountB]
      exact integral_nonneg fun x => mul_nonneg (sq_nonneg _)
        (Finset.sum_nonneg fun i _ => sq_nonneg _)
    · exact mul_nonneg (Work.SmallBoxSliding.chiMass_nonneg _ _ _ _)
        (by rw [Work.BoseFixB1.flatMass]
            exact integral_nonneg fun x => sq_nonneg _)
  have hcount' : S ≤ Cs * (tau * kappa * N) := by
    have hnm : Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        = Work.BoseFixB1.flatMass (Work.BoseFixB1.pL v μ) (Φ : Submission.BoseGases.X n → ℝ) := rfl
    rw [hSdef, hNdef, htdef, hkdef] at hcount ⊢
    simpa only [hnm] using hcount
  have hΔnn : 0 ≤ (1 / 2) * (W2 - W1) * (tau ^ 2 * N + V) := by
    have hW2nn : 0 ≤ W2 - W1 := by
      have h1 : 32 * Cs * D * kappa ≤ W2 - W1 := by rw [hW2def, hW1def, hkdef]; exact hW₂
      exact le_trans (by positivity) h1
    have h2 : (0:ℝ) ≤ tau ^ 2 * N + V := by positivity
    positivity
  have hW1' : (64 / 7) * Cs * D * kappa ≤ W1 := by rw [hW1def, hkdef]; exact hW₁
  have hW2' : 32 * Cs * D * kappa ≤ W2 - W1 := by rw [hW2def, hW1def, hkdef]; exact hW₂
  have harith := fibRowArith_le (μ := μ) (D := D) (a := _root_.BoseGases.a v) (Q := Q) (S := S)
    (κ := kappa) (W₁ := W1) (W₂ := W2) (τ := tau) (N := N) (V := V)
    (Δ := (1 / 2) * (W2 - W1) * (tau ^ 2 * N + V)) (Cs := Cs)
    hμ ha hDnn hQnn hSnn hCs hκpos hNpos hVnn hτ0 hΔnn hcount' hW1' hW2' rfl
  rw [← hQdef, ← hSdef, ← htdef, ← hNdef, ← hW1def] at hrow
  exact le_trans hrow harith

end Work.BoseFixB1S