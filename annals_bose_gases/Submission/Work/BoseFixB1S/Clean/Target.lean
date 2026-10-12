import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.BoxQ0Value
import Submission.Work.BoseFixB1.q0word_localised_value
import Submission.Work.BoseFixB1S.Clean.SubA2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.Clean

open _root_.BoseGases Submission.BoseGases Work.UBB
open Work.SmallBoxSliding
open Work.UBBInputs8
open Work.BoseFixB1S.Q0C

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
## The exact slack of the box-projected `A₀` step (proved here)

The target below is FS `lm:appinteractionestimate` at FS's own box projections with the pairing
`A₂` displayed.  Two ingredients of any proof of it are established *here*:

* `a0MainLocBox_slack` — the pure-real identity
  `a0MainLocBox V μ M₁ S = −μ(M₁/V)S − M₁G + ½(M₁/V²)(S² − S)` with
  `G = ¼(S/V−μ)² + (S/V+μ)/(2V) + 1/(4V²)`;
* `boxQ0_sub_a0MainLocBox_eq` / `boxM1G_le_boxQ0_sub_a0MainLocBox` — the *exact* value of the
  `A₀`-slack at the box projections (on top of the proved rung 2 `boxQ0_value`),

    `boxQ0 − a0MainLocBox = M₁·G + ½(M₂/V²)·boxPairCount − ½(M₁/V²)(S² − S) ≥ M₁·G ≥ 0`,

  the quantitative strengthening of the proved rung 3 (`boxQ0_ge_a0MainBox` gives only `≥ 0`).
  `M₁·G` is precisely the budget FS's proof consumes (the `¼(ρ₀−μ)²` square pays the `Q₁`-μ-line
  and the `PPQω`-term; the `½(M₂/V²)Pc` term pays the `P`-projected pair masses).
-/

/-- **The pure-real slack identity of the box-projected `A₀` step.**  For `V > 0`,

    a0MainLocBox V μ M₁ S
      = −μ(M₁/V)S − M₁G + ½(M₁/V²)(S² − S) ,  G := ¼(S/V − μ)² + (S/V + μ)/(2V) + 1/(4V²) . -/
lemma a0MainLocBox_slack (V μ M1 S : ℝ) (hV : 0 < V) :
    a0MainLocBox V μ M1 S
      = - μ * (M1 / V) * S
        - M1 * ((1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V) + 1 / (4 * V ^ 2))
        + (1 / 2) * (M1 / V ^ 2) * (S ^ 2 - S) := by
  unfold a0MainLocBox
  field_simp
  ring

/-- **The exact value of the `A₀`-slack at the box projections** (rung 2 `boxQ0_value` plus
`a0MainLocBox_slack`): `boxQ0 − a0MainLocBox = M₁·G + ½(M₂/V²)·boxPairCount − ½(M₁/V²)(S² − S)`. -/
theorem boxQ0_sub_a0MainLocBox_eq {N : ℕ} {ℓ volA μ : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w1 w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw2i : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        w2 p.1 p.2) ((MeasureTheory.volume : MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))).restrict (A ×ˢ A)))
    (hfib : MeasureTheory.IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.w1Fibre ℓ w1 z) A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    Work.BoseFixB1S.boxQ0 volA ℓ μ A w1 w2 Φ
        - a0MainLocBox volA μ (Work.BoseFixB1S.boxM1 ℓ A w1)
            (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ)
      = Work.BoseFixB1S.boxM1 ℓ A w1 *
          ((1 / 4) * (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ / volA - μ) ^ 2
            + (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ / volA + μ) / (2 * volA)
            + 1 / (4 * volA ^ 2))
        + (1 / 2) * (Work.BoseFixB1S.boxM2 volA A w2 / volA ^ 2)
            * Work.BoseFixB1S.boxPairCount volA ℓ A Φ
        - (1 / 2) * (Work.BoseFixB1S.boxM1 ℓ A w1 / volA ^ 2)
            * (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ ^ 2
                - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ) := by
  rw [boxQ0_value (N := N) hℓ hvol hA hvolA hAc hw2i hfib hΦc,
    a0MainLocBox_slack volA μ (Work.BoseFixB1S.boxM1 ℓ A w1)
      (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ) hvol]
  ring

/-- **The quantitative slack of the `A₀` step**: under `0 ≤ M₁ ≤ M₂`, `0 ≤ boxPairCount` and the
box Cauchy–Schwarz `S² − S ≤ boxPairCount`, `M₁·G(ρ₀) ≤ boxQ0 − a0MainLocBox`. -/
theorem boxM1G_le_boxQ0_sub_a0MainLocBox {N : ℕ} {ℓ volA μ : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w1 w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw2i : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        w2 p.1 p.2) ((MeasureTheory.volume : MeasureTheory.Measure
          (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3))).restrict (A ×ˢ A)))
    (hfib : MeasureTheory.IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.w1Fibre ℓ w1 z) A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (hM1nn : 0 ≤ Work.BoseFixB1S.boxM1 ℓ A w1)
    (hM2 : Work.BoseFixB1S.boxM1 ℓ A w1 ≤ Work.BoseFixB1S.boxM2 volA A w2)
    (hPcnn : 0 ≤ Work.BoseFixB1S.boxPairCount volA ℓ A Φ)
    (hcS2 : Work.BoseFixB1S.boxFlatCount volA ℓ A Φ * Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
        - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ
        ≤ Work.BoseFixB1S.boxPairCount volA ℓ A Φ) :
    Work.BoseFixB1S.boxM1 ℓ A w1 *
        ((1 / 4) * (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ / volA - μ) ^ 2
          + (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ / volA + μ) / (2 * volA)
          + 1 / (4 * volA ^ 2))
      ≤ Work.BoseFixB1S.boxQ0 volA ℓ μ A w1 w2 Φ
        - a0MainLocBox volA μ (Work.BoseFixB1S.boxM1 ℓ A w1)
            (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ) := by
  have hid := boxQ0_sub_a0MainLocBox_eq (N := N) (ℓ := ℓ) (volA := volA) (μ := μ)
    (A := A) (w1 := w1) (w2 := w2) (Φ := Φ) hℓ hvol hA hvolA hAc hw2i hfib hΦc
  have hsq : Work.BoseFixB1S.boxFlatCount volA ℓ A Φ ^ 2
      - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ ≤ Work.BoseFixB1S.boxPairCount volA ℓ A Φ := by
    simpa only [sq] using hcS2
  have hV2 : (0 : ℝ) < volA ^ 2 := by positivity
  have hcoef : (0 : ℝ) ≤ (1 / 2) * (Work.BoseFixB1S.boxM1 ℓ A w1 / volA ^ 2) := by positivity
  have h2 : Work.BoseFixB1S.boxM1 ℓ A w1 / volA ^ 2
      ≤ Work.BoseFixB1S.boxM2 volA A w2 / volA ^ 2 :=
    div_le_div_of_nonneg_right hM2 (le_of_lt hV2)
  have hb : (1 / 2) * (Work.BoseFixB1S.boxM1 ℓ A w1 / volA ^ 2)
        * Work.BoseFixB1S.boxPairCount volA ℓ A Φ
      ≤ (1 / 2) * (Work.BoseFixB1S.boxM2 volA A w2 / volA ^ 2)
        * Work.BoseFixB1S.boxPairCount volA ℓ A Φ := by
    nlinarith [hPcnn, h2, hcoef]
  have hc : (1 / 2) * (Work.BoseFixB1S.boxM1 ℓ A w1 / volA ^ 2)
        * (Work.BoseFixB1S.boxFlatCount volA ℓ A Φ ^ 2
            - Work.BoseFixB1S.boxFlatCount volA ℓ A Φ)
      ≤ (1 / 2) * (Work.BoseFixB1S.boxM1 ℓ A w1 / volA ^ 2)
        * Work.BoseFixB1S.boxPairCount volA ℓ A Φ :=
    mul_le_mul_of_nonneg_left hsq hcoef
  linarith [hid, hb, hc]

/-! ## The exact minimisation in the four-`Q` variable (FS `eq:Q3+Q4CS`, proved here)

For one ordered pair `(i,j)` with `A := P_iP_jΦ`, `B := P_iQ_jΦ`, `C := Q_iP_jΦ`,
`D := Q_iQ_jΦ`, `T := A+B+C` and the kernels `w₁ = w(1−ω)`, `w₂ = w₁(1+ω)`, the pair's
contribution to `boxQ1 + frag₁ + frag₂ + boxQ3 + boxQ4` is

    2BAw₂ + BCw₂ + B²w₂ + 2BDw₁ + ½(D + ωT)²w ,

and this is the *exact* square-completion

    = w·(D + ωT + 2B(1−ω))²/2 + w₁·(2AB + (1−ω)B(C−B)) ,

i.e. minimising in `D` (the only quantity carrying a `Q₄`-square) is *lossless*: the residual is
the manifest square `w(D + ωT + 2B(1−ω))²/2 ≥ 0` (`w ≥ 0`), and what survives is FS's displayed
leftover `2ABw₁ + (1−ω)B(C−B)w₁`. -/
theorem q4_pair_dmin_identity {A B C D om w w1 w2 : ℝ}
    (h1 : w1 = w * (1 - om)) (h2 : w2 = w1 * (1 + om)) :
    2 * B * A * w2 + B * C * w2 + B ^ 2 * w2 + 2 * B * D * w1
        + (1 / 2) * (D + om * (A + B + C)) ^ 2 * w
      = w * (D + om * (A + B + C) + 2 * B * (1 - om)) ^ 2 / 2
        + w1 * (2 * A * B + (1 - om) * B * (C - B)) := by
  rw [h2, h1]
  ring

/-! ## The value identities of FS's `eq:Q1n0` (proved here)

FS's rewriting of `Q₁^{ren,1}` (`final_v2.tex` l.1105–1120) rests on the fact that `P_{B,i}` is the
rank-one projection onto the `A`-constants in slot `i`: a *one-slot* function sandwiched between two
`P_i`'s collapses to its box average, `P_i·g(x_i)·P_i = (⦵_A g)·P_i` (`boxPInd_sandwich`), hence
`Σ_i P_i g(x_i) P_i = (⦵_A g)·n₀` (`boxPInd_sandwich_sum`, `n₀ = Σ_iP_i`).  Combining with the
definitional identity `P_i + Q_i = 1_{A,i}·` (`Work.BoseFixB1S.boxProjOps_add`) gives

    A_p + B_p = P_i(1_{A,j}Φ) ,   A_p + C_p = P_j(1_{A,i}Φ)     (A = P_iP_jΦ, B = P_iQ_jΦ, C = Q_iP_jΦ)

(`boxPInd_pair_eq` gives `A_p` in closed form), i.e. the two-slot patterns split into a *mean* and a
*fluctuation of the slot mean* — the structure that lets the `A²`- and `B²`-demands share the single
payer `½(M₂/V²)Pc` instead of competing for it. -/

/-- **The sandwiched one-slot value identity** `P_i·g(x_i)·P_i = (⦵_A g)·P_i`, pointwise. -/
theorem boxPInd_sandwich (volA : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    {N : ℕ} (i : Fin N) (g : EuclideanSpace ℝ (Fin 3) → ℝ) (Ψ : Submission.BoseGases.X N → ℝ)
    (x : Submission.BoseGases.X N) :
    boxPInd volA A i (fun y => g (y i) * boxPInd volA A i Ψ y) x
      = ((1 / volA) * ∫ z in A, g z) * boxPInd volA A i Ψ x := by
  set c : ℝ := ∫ w in A, Ψ (Function.update x i w) with hc
  simp only [boxPInd, Function.update_idem, Function.update_self]
  have h1 : (∫ z in A, g z * ((1 / volA) * c * A.indicator (fun _ => (1 : ℝ)) z))
      = ((1 / volA) * c) * (∫ z in A, g z) := by
    rw [show (fun z : EuclideanSpace ℝ (Fin 3) =>
          g z * ((1 / volA) * c * A.indicator (fun _ => (1 : ℝ)) z))
        = fun z => A.indicator (fun z => g z * ((1 / volA) * c)) z from by
      funext z
      by_cases hz : z ∈ A
      · rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz]; ring
      · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]; ring]
    rw [MeasureTheory.setIntegral_indicator hA, Set.inter_self,
      MeasureTheory.integral_mul_const]
    ring
  rw [h1]
  ring

/-- **`Σ_i P_i g(x_i) P_i = (⦵_A g)·n₀`** — the summed value identity. -/
theorem boxPInd_sandwich_sum (volA : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    {N : ℕ} (g : EuclideanSpace ℝ (Fin 3) → ℝ) (Ψ : Submission.BoseGases.X N → ℝ)
    (x : Submission.BoseGases.X N) :
    (∑ i : Fin N, boxPInd volA A i (fun y => g (y i) * boxPInd volA A i Ψ y) x)
      = ((1 / volA) * ∫ z in A, g z) * (∑ i : Fin N, boxPInd volA A i Ψ x) := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => boxPInd_sandwich volA hA i g Ψ x

/-- **`A_p = P_iP_jΦ` in closed form** (distinct slots): the two-slot mean times the two box
indicators. -/
theorem boxPInd_pair_eq (volA : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))} {N : ℕ} {i j : Fin N}
    (hij : i ≠ j) (Ψ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    boxPInd volA A i (boxPInd volA A j Ψ) x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j)
        * ((1 / volA ^ 2) * ∫ z in A, ∫ w in A,
            Ψ (Function.update (Function.update x i z) j w)) := by
  have hupd : ∀ z : EuclideanSpace ℝ (Fin 3),
      Function.update x i z j = x j := fun z => Function.update_of_ne (Ne.symm hij) z x
  simp only [boxPInd, hupd]
  rw [show (fun z : EuclideanSpace ℝ (Fin 3) =>
        (1 / volA) * (∫ w in A, Ψ (Function.update (Function.update x i z) j w))
          * A.indicator (fun _ => (1 : ℝ)) (x j))
      = fun z => A.indicator (fun _ => (1 : ℝ)) (x j)
        * ((1 / volA) * (∫ w in A, Ψ (Function.update (Function.update x i z) j w))) from by
    funext z; ring]
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- **`P_iΦ` in explicit form**: the box indicator times the `i`-slot mean. -/
theorem boxPInd_eq (volA : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))} {N : ℕ} (i : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    boxPInd volA A i Φ x
      = A.indicator (fun _ => (1 : ℝ)) (x i)
        * ((1 / volA) * ∫ z in A, Φ (Function.update x i z)) := by
  unfold boxPInd; ring

/-- **`Q_iΦ` in explicit form** (`Q_i = 1_{A,i} − P_i`). -/
theorem boxQInd_eq (volA : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))} {N : ℕ} (i : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    boxQInd volA A i Φ x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x
        - A.indicator (fun _ => (1 : ℝ)) (x i)
          * ((1 / volA) * ∫ z in A, Φ (Function.update x i z)) := by
  unfold boxQInd
  rw [boxPInd_eq]

/-- **The `A`-pattern in normalised form**: for distinct slots,
`A_p = P_iP_jΦ = 1_A(x_i)1_A(x_j)·⦵_A⦵_AΦ`. -/
theorem boxPInd_pair_eq_indicator (volA : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))} {N : ℕ}
    {i j : Fin N} (hij : i ≠ j) (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    boxPInd volA A i (boxPInd volA A j Φ) x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j)
        * ((1 / volA) * ∫ z in A, (1 / volA) * ∫ w in A,
            Φ (Function.update (Function.update x i z) j w)) := by
  rw [boxPInd_pair_eq volA hij]
  rw [show (1 / volA ^ 2) * ∫ z in A, ∫ w in A,
        Φ (Function.update (Function.update x i z) j w)
      = (1 / volA) * ∫ z in A, (1 / volA) * ∫ w in A,
          Φ (Function.update (Function.update x i z) j w) from by
    rw [show (∫ z in A, (1 / volA) * ∫ w in A,
          Φ (Function.update (Function.update x i z) j w))
        = (1 / volA) * ∫ z in A, ∫ w in A,
            Φ (Function.update (Function.update x i z) j w) from
      MeasureTheory.integral_const_mul (1 / volA) _]
    ring]

private theorem indicator_abs_le_one (A : Set (EuclideanSpace ℝ (Fin 3)))
    (y : EuclideanSpace ℝ (Fin 3)) :
    |A.indicator (fun _ => (1 : ℝ)) y| ≤ 1 := by
  by_cases hy : y ∈ A
  · simp [Set.indicator_of_mem hy]
  · simp [Set.indicator_of_notMem hy]

/-- **The pattern split at the box projections.**  For distinct slots `i ≠ j`,

    P_iP_jΦ + P_iQ_jΦ = P_i(1_{A,j}Φ) = 1_A(x_i)·1_A(x_j)·φ̄_i ,

i.e. the two slots carrying (`P_j`, `Q_j`) collapse under the `i`-slot mean `P_i`, leaving the
*i-slot mean of `1_{A,j}Φ`*.  (The companion identity `A_p + C_p = P_j(1_{A,i}Φ)` is the same
statement with the slots swapped.)  Together with `Work.BoseFixB1.boxPInd_pair_eq_indicator`
(`A_p = 1_A1_A·Φ̄_{ij}`) this expresses the two-slot patterns through the slot means
`A_p = Φ̄_{ij}`, `B_p = φ̄_i − Φ̄_{ij}` — the first half of FS's `eq:Q1n0`.

The only non-formal ingredient is the *integrability* of `z ↦ (P_jΦ)(x|i↦z)` and
`z ↦ (Q_jΦ)(x|i↦z)` along the updated configuration (needed to split `∫(P_jΦ + Q_jΦ)`); it is
supplied by continuity of `Φ` together with `Work.BoseFixB1S.Q0C.abs_boxPInd_le`. -/
theorem boxPInd_pair_add_boxQInd {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (volume : Measure (EuclideanSpace ℝ (Fin 3))).real A)
    {i j : Fin N} (hij : i ≠ j)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {x : Submission.BoseGases.X N} (hx : x ∈ Submission.BoseGases.abox N ℓ) :
    boxPInd volA A i (boxPInd volA A j Φ) x + boxPInd volA A i (boxQInd volA A j Φ) x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j)
        * ((1 / volA) * ∫ z in A, Φ (Function.update x i z)) := by
  have hPQ : ∀ y : Submission.BoseGases.X N,
      boxPInd volA A j Φ y + boxQInd volA A j Φ y
        = A.indicator (fun _ => (1 : ℝ)) (y j) * Φ y := by
    intro y
    rw [boxQInd_eq, boxPInd_eq]
    ring
  have hupd : ∀ z : EuclideanSpace ℝ (Fin 3), Function.update x i z j = x j :=
    fun z => Function.update_of_ne (Ne.symm hij) z x
  obtain ⟨BP, hBP0, hBP⟩ := abs_boxPInd_le (volA := volA) hℓ hvol hA hAc hvolA j hΦc
  obtain ⟨BΦ, hBΦ⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox N ℓ) (f := Φ) hΦc.continuousOn
  have hBΦ0 : 0 ≤ BΦ := le_trans (norm_nonneg _) (hBΦ _ (zero_mem_abox hℓ.le))
  have hfin : (volume : Measure (EuclideanSpace ℝ (Fin 3))) A ≠ ∞ :=
    ne_of_lt (volume_A_lt_top hℓ hAc)
  have hχ : |A.indicator (fun _ => (1 : ℝ)) (x j)| ≤ 1 := indicator_abs_le_one A (x j)
  have hP_exp : (fun z : EuclideanSpace ℝ (Fin 3) => boxPInd volA A j Φ (Function.update x i z))
      = fun z => A.indicator (fun _ => (1 : ℝ)) (x j)
          * ((1 / volA) * ∫ w in A, Φ (Function.update (Function.update x i z) j w)) := by
    funext z
    rw [boxPInd_eq]
    rw [hupd z]
  have hQ_exp : (fun z : EuclideanSpace ℝ (Fin 3) => boxQInd volA A j Φ (Function.update x i z))
      = fun z => A.indicator (fun _ => (1 : ℝ)) (x j) * Φ (Function.update x i z)
          - A.indicator (fun _ => (1 : ℝ)) (x j)
            * ((1 / volA) * ∫ w in A, Φ (Function.update (Function.update x i z) j w)) := by
    funext z
    rw [boxQInd_eq, hupd z]
  have hsm_int : StronglyMeasurable (fun z : EuclideanSpace ℝ (Fin 3) => ∫ w in A,
      Φ (Function.update (Function.update x i z) j w)) := by
    have hsm : StronglyMeasurable (Function.uncurry (fun (z : EuclideanSpace ℝ (Fin 3))
        (w : EuclideanSpace ℝ (Fin 3)) =>
        Φ (Function.update (Function.update x i z) j w))) := by
      have hmap : Measurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Function.update (Function.update x i p.1) j p.2) := by fun_prop
      exact (hΦc.measurable.comp hmap).stronglyMeasurable
    exact StronglyMeasurable.integral_prod_right
      (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A) hsm
  have hIntP : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
      boxPInd volA A j Φ (Function.update x i z)) A := by
    have haesm : AEStronglyMeasurable (fun z : EuclideanSpace ℝ (Fin 3) =>
        boxPInd volA A j Φ (Function.update x i z))
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A) := by
      rw [hP_exp]
      exact ((stronglyMeasurable_const.mul (hsm_int.const_mul (1 / volA))).aestronglyMeasurable)
    refine MeasureTheory.Integrable.mono' (g := fun _ : EuclideanSpace ℝ (Fin 3) => BP)
      (MeasureTheory.integrableOn_const (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
        (s := A) (C := BP) hfin) haesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict hA] with z hz
    rw [Real.norm_eq_abs]
    exact hBP _ (update_mem_abox hAc hx i hz)
  have hIntQ : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
      boxQInd volA A j Φ (Function.update x i z)) A := by
    rw [hQ_exp]
    have h1 : IntegrableOn (fun z : EuclideanSpace ℝ (Fin 3) =>
        A.indicator (fun _ => (1 : ℝ)) (x j) * Φ (Function.update x i z)) A := by
      have haesm : AEStronglyMeasurable (fun z : EuclideanSpace ℝ (Fin 3) =>
          A.indicator (fun _ => (1 : ℝ)) (x j) * Φ (Function.update x i z))
          ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A) :=
        (stronglyMeasurable_const.mul
          (hΦc.measurable.comp (measurable_update x)).stronglyMeasurable).aestronglyMeasurable
      refine MeasureTheory.Integrable.mono' (g := fun _ : EuclideanSpace ℝ (Fin 3) => BΦ)
        (MeasureTheory.integrableOn_const (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
          (s := A) (C := BΦ) hfin) haesm ?_
      filter_upwards [MeasureTheory.self_mem_ae_restrict hA] with z hz
      rw [Real.norm_eq_abs, abs_mul]
      calc |A.indicator (fun _ => (1 : ℝ)) (x j)| * |Φ (Function.update x i z)|
          ≤ 1 * BΦ := by
            refine mul_le_mul hχ ?_ (abs_nonneg _) (by norm_num)
            simpa only [Real.norm_eq_abs] using hBΦ _ (update_mem_abox hAc hx i hz)
        _ = BΦ := one_mul BΦ
    refine h1.sub ?_
    have haesm : AEStronglyMeasurable (fun z : EuclideanSpace ℝ (Fin 3) =>
        A.indicator (fun _ => (1 : ℝ)) (x j)
          * ((1 / volA) * ∫ w in A, Φ (Function.update (Function.update x i z) j w)))
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict A) :=
      ((stronglyMeasurable_const.mul (hsm_int.const_mul (1 / volA))).aestronglyMeasurable)
    refine MeasureTheory.Integrable.mono' (g := fun _ : EuclideanSpace ℝ (Fin 3) => BP)
      (MeasureTheory.integrableOn_const (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
        (s := A) (C := BP) hfin) haesm ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict hA] with z hz
    rw [Real.norm_eq_abs]
    rw [← congrFun hP_exp z]
    exact hBP _ (update_mem_abox hAc hx i hz)
  calc boxPInd volA A i (boxPInd volA A j Φ) x + boxPInd volA A i (boxQInd volA A j Φ) x
      = A.indicator (fun _ => (1 : ℝ)) (x i)
          * ((1 / volA) * ∫ z in A, boxPInd volA A j Φ (Function.update x i z))
        + A.indicator (fun _ => (1 : ℝ)) (x i)
          * ((1 / volA) * ∫ z in A, boxQInd volA A j Φ (Function.update x i z)) := by
        rw [boxPInd_eq, boxPInd_eq]
    _ = A.indicator (fun _ => (1 : ℝ)) (x i)
          * ((1 / volA) * ((∫ z in A, boxPInd volA A j Φ (Function.update x i z))
            + (∫ z in A, boxQInd volA A j Φ (Function.update x i z)))) := by
        ring
    _ = A.indicator (fun _ => (1 : ℝ)) (x i)
          * ((1 / volA) * ∫ z in A, (boxPInd volA A j Φ (Function.update x i z)
            + boxQInd volA A j Φ (Function.update x i z))) := by
        rw [← MeasureTheory.integral_add hIntP hIntQ]
    _ = A.indicator (fun _ => (1 : ℝ)) (x i)
          * ((1 / volA) * ∫ z in A,
              A.indicator (fun _ => (1 : ℝ)) (x j) * Φ (Function.update x i z)) := by
        congr 2
        apply MeasureTheory.integral_congr_ae
        filter_upwards with z
        rw [hPQ (Function.update x i z), hupd z]
    _ = A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j)
          * ((1 / volA) * ∫ z in A, Φ (Function.update x i z)) := by
        rw [MeasureTheory.integral_const_mul]
        ring


/-- **The companion pattern split**: `A_p + C_p = P_j(1_{A,i}Φ)`, i.e. the two `P_j`-slots carrying
(`P_i`, `Q_i`) collapse under the `j`-slot mean — this one is *definitional* (`Q_i = 1_{A,i}· − P_i`
`+ P_i`), so unlike its partner it needs no integrability. -/
theorem boxPInd_pair_add_QInd_pair (volA : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))} {N : ℕ}
    {i j : Fin N} (hij : i ≠ j) (Φ : Submission.BoseGases.X N → ℝ)
    (x : Submission.BoseGases.X N) :
    boxPInd volA A i (boxPInd volA A j Φ) x + boxQInd volA A i (boxPInd volA A j Φ) x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j)
        * ((1 / volA) * ∫ w in A, Φ (Function.update x j w)) := by
  have h1 : boxPInd volA A i (boxPInd volA A j Φ) x
      + boxQInd volA A i (boxPInd volA A j Φ) x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * boxPInd volA A j Φ x := by
    rw [boxQInd_eq, boxPInd_eq]
    ring
  rw [h1, boxPInd_eq]
  ring


/-- **The `B`-pattern in terms of the slot means** (distinct slots, `x ∈ abox N ℓ`):

    B_p = P_iQ_jΦ = 1_A(x_i)·1_A(x_j)·( φ̄_i − Φ̄_{ij} ) ,

with `φ̄_i = ⦵_A(Φ(·|i↦·))` and `Φ̄_{ij} = ⦵_A⦵_A(Φ(·|i↦·|j↦·))`.  Combined with
`boxPInd_pair_eq_indicator` (`A_p = 1_A1_A·Φ̄_{ij}`) and the definitional companion
`boxPInd_pair_add_QInd_pair` (`A_p + C_p = 1_A1_A·φ̄_j`, hence `C_p = 1_A1_A(φ̄_j − Φ̄_{ij})`), this
expresses **all four two-slot patterns through the two slot means** — FS's `eq:Q1n0` collapse, and
the reason the `A²`- and `B²`-demands can share the single payer `½(M₂/V²)Pc` (the `B`-pattern is a
*conditional variance*). -/
theorem boxPInd_QInd_eq_mean {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (volume : Measure (EuclideanSpace ℝ (Fin 3))).real A)
    {i j : Fin N} (hij : i ≠ j)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {x : Submission.BoseGases.X N} (hx : x ∈ Submission.BoseGases.abox N ℓ) :
    boxPInd volA A i (boxQInd volA A j Φ) x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j)
        * (((1 / volA) * ∫ z in A, Φ (Function.update x i z))
            - (1 / volA) * ∫ z in A, (1 / volA) * ∫ w in A,
                Φ (Function.update (Function.update x i z) j w)) := by
  have hsum := boxPInd_pair_add_boxQInd (N := N) (ℓ := ℓ) (volA := volA) (A := A)
    (i := i) (j := j) (Φ := Φ) (x := x) hℓ hvol hA hAc hvolA hij hΦc hx
  have hA' := boxPInd_pair_eq_indicator (volA := volA) (A := A) hij Φ x
  have hsplit : boxPInd volA A i (boxQInd volA A j Φ) x
      = (boxPInd volA A i (boxPInd volA A j Φ) x + boxPInd volA A i (boxQInd volA A j Φ) x)
        - boxPInd volA A i (boxPInd volA A j Φ) x := by ring
  rw [hsplit, hsum, hA']
  ring


/-- **The `C`-pattern in terms of the slot means**: `C_p = Q_iP_jΦ = 1_A1_A·(φ̄_j − Φ̄_{ij})` — the
slot-swapped partner of `boxPInd_QInd_eq_mean`. -/
theorem boxQInd_PInd_eq_mean (volA : ℝ) {A : Set (EuclideanSpace ℝ (Fin 3))} {N : ℕ}
    {i j : Fin N} (hij : i ≠ j) (Φ : Submission.BoseGases.X N → ℝ)
    (x : Submission.BoseGases.X N) :
    boxQInd volA A i (boxPInd volA A j Φ) x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j)
        * (((1 / volA) * ∫ w in A, Φ (Function.update x j w))
            - (1 / volA) * ∫ z in A, (1 / volA) * ∫ w in A,
                Φ (Function.update (Function.update x i z) j w)) := by
  have hsum := boxPInd_pair_add_QInd_pair (volA := volA) (A := A) hij Φ x
  have hA' := boxPInd_pair_eq_indicator (volA := volA) (A := A) hij Φ x
  have hsplit : boxQInd volA A i (boxPInd volA A j Φ) x
      = (boxPInd volA A i (boxPInd volA A j Φ) x + boxQInd volA A i (boxPInd volA A j Φ) x)
        - boxPInd volA A i (boxPInd volA A j Φ) x := by ring
  rw [hsplit, hsum, hA']
  ring

/-- **The `ι² = ι` collapse** (pure real): the pair indicator `ι = 1_A(x_i)1_A(x_j)` takes the
values `0,1`, so the leftover `2A·B + (1−ω)(B·C − B²)` — with the three patterns collapsed to the
slot means `A = ι·m`, `B = ι·(n−m)`, `C = ι·(p−m)` — is `ι` times the mean bracket. -/
theorem pair_leftover_reduce {ι m n p om : ℝ} (hι : ι * ι = ι) :
    2 * (ι * m) * (ι * (n - m))
        + (1 - om) * ((ι * (n - m)) * (ι * (p - m)) - (ι * (n - m)) ^ 2)
      = ι * (2 * m * (n - m) + (1 - om) * (n - m) * ((p - m) - (n - m))) := by
  have h2 : ∀ X : ℝ, ι * (ι * X) = ι * X := by
    intro X
    rw [← mul_assoc, hι]
  calc 2 * (ι * m) * (ι * (n - m))
        + (1 - om) * ((ι * (n - m)) * (ι * (p - m)) - (ι * (n - m)) ^ 2)
      = ι * (ι * (2 * m * (n - m) + (1 - om) * (n - m) * ((p - m) - (n - m)))) := by ring
    _ = ι * (2 * m * (n - m) + (1 - om) * (n - m) * ((p - m) - (n - m))) := h2 _

/-- **The leftover at a pair, in terms of the slot means** — FS's `eq:Q1n0` collapse applied to
the object `L` of the cross half.  With

    A_p = P_iP_jΦ = ι·Φ̄_{ij} ,  B_p = P_iQ_jΦ = ι·(φ̄_i − Φ̄_{ij}) ,  C_p = Q_iP_jΦ = ι·(φ̄_j − Φ̄_{ij})
    ι := 1_A(x_i)·1_A(x_j) ,  Φ̄_{ij} = ⦵⦵Φ ,  φ̄_i = ⦵_A(Φ(·|i↦·)) ,  φ̄_j = ⦵_A(Φ(·|j↦·)) ,

(the three identities proved above),

    2·A_pB_p + (1−ω)(B_pC_p − B_p²)
      = ι·( 2·Φ̄_{ij}(φ̄_i − Φ̄_{ij}) + (1−ω)(φ̄_i − Φ̄_{ij})((φ̄_j − Φ̄_{ij}) − (φ̄_i − Φ̄_{ij})) ) .

This is the *pointwise* half of the `(i,j)`-slot factorisation of `L`: the four patterns are gone,
and only the slot means (and the two indicators) remain, so the remaining work is the *integral*
statement (the `(x_i,x_j)`-slots meeting the kernel `w₁`) — where the `φ̄`'s dependence on the
*other* slot (unlike `Φ̄_{ij}`, which depends on neither) produces the fibre-weighted means. -/
theorem pair_leftover_eq_means {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (volume : Measure (EuclideanSpace ℝ (Fin 3))).real A)
    {i j : Fin N} (hij : i ≠ j)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {x : Submission.BoseGases.X N} (hx : x ∈ Submission.BoseGases.abox N ℓ) (om : ℝ) :
    2 * boxPInd volA A i (boxPInd volA A j Φ) x * boxPInd volA A i (boxQInd volA A j Φ) x
        + (1 - om) * (boxPInd volA A i (boxQInd volA A j Φ) x
              * boxQInd volA A i (boxPInd volA A j Φ) x
            - boxPInd volA A i (boxQInd volA A j Φ) x ^ 2)
      = (A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j))
        * (2 * ((1 / volA) * ∫ z in A, (1 / volA) * ∫ w in A,
                  Φ (Function.update (Function.update x i z) j w))
              * (((1 / volA) * ∫ z in A, Φ (Function.update x i z))
                  - (1 / volA) * ∫ z in A, (1 / volA) * ∫ w in A,
                      Φ (Function.update (Function.update x i z) j w))
            + (1 - om)
              * (((1 / volA) * ∫ z in A, Φ (Function.update x i z))
                  - (1 / volA) * ∫ z in A, (1 / volA) * ∫ w in A,
                      Φ (Function.update (Function.update x i z) j w))
              * ((((1 / volA) * ∫ w in A, Φ (Function.update x j w))
                    - (1 / volA) * ∫ z in A, (1 / volA) * ∫ w in A,
                        Φ (Function.update (Function.update x i z) j w))
                  - (((1 / volA) * ∫ z in A, Φ (Function.update x i z))
                      - (1 / volA) * ∫ z in A, (1 / volA) * ∫ w in A,
                          Φ (Function.update (Function.update x i z) j w)))) := by
  have hApat := boxPInd_pair_eq_indicator (volA := volA) (A := A) hij Φ x
  have hBpat := boxPInd_QInd_eq_mean (N := N) (ℓ := ℓ) (volA := volA) (A := A)
    (i := i) (j := j) (Φ := Φ) (x := x) hℓ hvol hA hAc hvolA hij hΦc hx
  have hCpat := boxQInd_PInd_eq_mean (volA := volA) (A := A) hij Φ x
  have hι : (A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j))
      * (A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j))
      = A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j) := by
    by_cases hi : x i ∈ A <;> by_cases hj : x j ∈ A <;>
      simp [Set.indicator_of_mem, Set.indicator_of_notMem, hi, hj]
  rw [hApat, hBpat, hCpat]
  exact pair_leftover_reduce hι

/-- **The pairwise sum of the leftover, in terms of the slot means** (the integral-level form of
`pair_leftover_eq_means`).  For every kernel `w₁ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ` and continuous `Φ`,

    Σ_p ∫_{abox N ℓ} w₁(x_p)(2A_pB_p + (1−ω_p)(B_pC_p − B_p²))
      = Σ_p ∫_{abox N ℓ} w₁(x_p)·ι_p·( 2Φ̄_p(φ̄_p − Φ̄_p) + (1−ω_p)(φ̄_p − Φ̄_p)((φ̄'_p − Φ̄_p) − (φ̄_p − Φ̄_p)) )

with `A_p = P_{p.1}P_{p.2}Φ`, `B_p = P_{p.1}Q_{p.2}Φ`, `C_p = Q_{p.1}P_{p.2}Φ`, `ω_p = om(x_p)`,
`ι_p = 1_A(x_{p.1})1_A(x_{p.2})` and the slot means as displayed.  No integrability hypothesis is
needed: the identity is a.e. equality of integrands, which `integral_congr_ae` transports through
the (Bochner) integral unconditionally. -/
theorem pairSum_leftover_eq_means {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (volume : Measure (EuclideanSpace ℝ (Fin 3))).real A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    (w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ)
    (om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) :
    (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
        w1 (x p.1) (x p.2)
          * (2 * boxPInd volA A p.1 (boxPInd volA A p.2 Φ) x
                * boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x
              + (1 - om (x p.1) (x p.2))
                * (boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x
                    * boxQInd volA A p.1 (boxPInd volA A p.2 Φ) x
                  - boxPInd volA A p.1 (boxQInd volA A p.2 Φ) x ^ 2)))
      = (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
          w1 (x p.1) (x p.2)
            * ((A.indicator (fun _ => (1 : ℝ)) (x p.1)
                  * A.indicator (fun _ => (1 : ℝ)) (x p.2))
              * (2 * ((1 / volA) * ∫ z in A, (1 / volA) * ∫ w in A,
                      Φ (Function.update (Function.update x p.1 z) p.2 w))
                    * (((1 / volA) * ∫ z in A, Φ (Function.update x p.1 z))
                        - (1 / volA) * ∫ z in A, (1 / volA) * ∫ w in A,
                            Φ (Function.update (Function.update x p.1 z) p.2 w))
                  + (1 - om (x p.1) (x p.2))
                    * (((1 / volA) * ∫ z in A, Φ (Function.update x p.1 z))
                        - (1 / volA) * ∫ z in A, (1 / volA) * ∫ w in A,
                            Φ (Function.update (Function.update x p.1 z) p.2 w))
                    * ((((1 / volA) * ∫ w in A, Φ (Function.update x p.2 w))
                          - (1 / volA) * ∫ z in A, (1 / volA) * ∫ w in A,
                              Φ (Function.update (Function.update x p.1 z) p.2 w))
                        - (((1 / volA) * ∫ z in A, Φ (Function.update x p.1 z))
                            - (1 / volA) * ∫ z in A, (1 / volA) * ∫ w in A,
                                Φ (Function.update (Function.update x p.1 z) p.2 w)))))) := by
  refine Finset.sum_congr rfl fun p hp => ?_
  have hne : p.1 ≠ p.2 := by
    have hp' := hp
    simp only [Submission.BoseGases.pairSet, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp'
    exact hp'
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
  exact congrArg (fun t => w1 (x p.1) (x p.2) * t)
    (pair_leftover_eq_means (N := N) (ℓ := ℓ) (volA := volA) (A := A) (i := p.1) (j := p.2)
      (Φ := Φ) hℓ hvol hA hAc hvolA hne hΦc hx (om (x p.1) (x p.2)))

/-- **Step (i)(b): the `(i,j)`-slot transport of the pair integral, reduced to the slot means.**
For a fixed ordered pair of distinct slots (packaged as `i : Fin (p+2)` and `j' : Fin (p+1)`), the
pair integral of the leftover `2A_pB_p + (1−ω)(B_pC_p − B_p²)` over `abox (p+2) ℓ` equals the
integral over `((y,z), r2)` of the kernel `w₁(y,z)` times the two indicators times the *mean
bracket*, with the three slot means evaluated at the insertion

    Φ̄ = ⦵_A⦵_A Ψ(·|i↦·|j↦·) ,   φ̄_i = ⦵_A Ψ(·|i↦·) ,   φ̄_j = ⦵_A Ψ(·|j↦·)

written in the corpus's `ins2`-vocabulary.  This is `abox_peel2_transport` followed by the a.e.
pointwise identity `pair_leftover_eq_means` at the insertion (whose membership is
`ins2_mem_abox`) together with the update-identifications `ins2_update_i`/`ins2_update_succ`. -/
theorem pair_integral_reduce {p : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    (hvolA : volA = (volume : Measure (EuclideanSpace ℝ (Fin 3))).real A)
    (i : Fin (p + 2)) (j' : Fin (p + 1))
    {Ψ : Submission.BoseGases.X (p + 2) → ℝ} (hΨc : Continuous Ψ)
    (w1 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ) :
    (∫ x in Submission.BoseGases.abox (p + 2) ℓ,
        w1 (x i) (x (i.succAbove j'))
          * (2 * boxPInd volA A i (boxPInd volA A (i.succAbove j') Ψ) x
                * boxPInd volA A i (boxQInd volA A (i.succAbove j') Ψ) x
              + (1 - om (x i) (x (i.succAbove j')))
                * (boxPInd volA A i (boxQInd volA A (i.succAbove j') Ψ) x
                    * boxQInd volA A i (boxPInd volA A (i.succAbove j') Ψ) x
                  - boxPInd volA A i (boxQInd volA A (i.succAbove j') Ψ) x ^ 2)))
      = ∫ q : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × Submission.BoseGases.X p,
          w1 q.1.1 q.1.2
            * ((A.indicator (fun _ => (1 : ℝ)) q.1.1 * A.indicator (fun _ => (1 : ℝ)) q.1.2)
              * (2 * ((1 / volA) * ∫ u in A, (1 / volA) * ∫ w in A,
                        Ψ (ins2 i j' u w q.2))
                    * (((1 / volA) * ∫ u in A, Ψ (ins2 i j' u q.1.2 q.2))
                        - (1 / volA) * ∫ u in A, (1 / volA) * ∫ w in A,
                            Ψ (ins2 i j' u w q.2))
                  + (1 - om q.1.1 q.1.2)
                    * (((1 / volA) * ∫ u in A, Ψ (ins2 i j' u q.1.2 q.2))
                        - (1 / volA) * ∫ u in A, (1 / volA) * ∫ w in A,
                            Ψ (ins2 i j' u w q.2))
                    * ((((1 / volA) * ∫ u in A, Ψ (ins2 i j' q.1.1 u q.2))
                          - (1 / volA) * ∫ u in A, (1 / volA) * ∫ w in A,
                              Ψ (ins2 i j' u w q.2))
                        - (((1 / volA) * ∫ u in A, Ψ (ins2 i j' u q.1.2 q.2))
                            - (1 / volA) * ∫ u in A, (1 / volA) * ∫ w in A,
                                Ψ (ins2 i j' u w q.2)))))
          ∂(((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
                (Submission.BoseGases.acube ℓ)).prod
              ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
                (Submission.BoseGases.acube ℓ))).prod
            ((volume : Measure (Submission.BoseGases.X p)).restrict
              (Submission.BoseGases.abox p ℓ)) := by
  have hq1 : ∀ᵐ q ∂(((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ)).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ))).prod
        ((volume : Measure (Submission.BoseGases.X p)).restrict
          (Submission.BoseGases.abox p ℓ)), q.1.1 ∈ Submission.BoseGases.acube ℓ
          ∧ q.1.2 ∈ Submission.BoseGases.acube ℓ := by
    refine (MeasureTheory.Measure.ae_prod_iff_ae_ae
      (μ := ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ)).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)))
      (ν := (volume : Measure (Submission.BoseGases.X p)).restrict
        (Submission.BoseGases.abox p ℓ))
      (p := fun q : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) ×
          Submission.BoseGases.X p => q.1.1 ∈ Submission.BoseGases.acube ℓ
            ∧ q.1.2 ∈ Submission.BoseGases.acube ℓ) ?_).2 ?_
    · exact ((Submission.BoseGases.acube_measurable ℓ).prod
        (Submission.BoseGases.acube_measurable ℓ)).preimage measurable_fst
    · filter_upwards [ae_mem_prod_restrict (Submission.BoseGases.acube_measurable ℓ)] with x hx
      exact Filter.Eventually.of_forall (fun y => hx)
  have hq2 : ∀ᵐ q ∂(((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ)).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ))).prod
        ((volume : Measure (Submission.BoseGases.X p)).restrict
          (Submission.BoseGases.abox p ℓ)), q.2 ∈ Submission.BoseGases.abox p ℓ := by
    refine (MeasureTheory.Measure.ae_prod_iff_ae_ae
      (μ := ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
        (Submission.BoseGases.acube ℓ)).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).restrict
          (Submission.BoseGases.acube ℓ)))
      (ν := (volume : Measure (Submission.BoseGases.X p)).restrict
        (Submission.BoseGases.abox p ℓ))
      (p := fun q : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) ×
          Submission.BoseGases.X p => q.2 ∈ Submission.BoseGases.abox p ℓ) ?_).2 ?_
    · exact (abox_measurable p ℓ).preimage measurable_snd
    · exact Filter.Eventually.of_forall
        (fun x => MeasureTheory.self_mem_ae_restrict (abox_measurable p ℓ))
  rw [abox_peel2_transport hℓ i j']
  apply MeasureTheory.integral_congr_ae
  filter_upwards [hq1, hq2] with q hq hq2
  have hmemins : ins2 i j' q.1.1 q.1.2 q.2 ∈ Submission.BoseGases.abox (p + 2) ℓ :=
    ins2_mem_abox (A := Submission.BoseGases.acube ℓ) (fun _ hy => hy) i j' hq.1 hq.2 hq2
  rw [ins2_apply_i, ins2_apply_succ]
  rw [congrArg (fun t => w1 q.1.1 q.1.2 * t)
    (pair_leftover_eq_means (N := p + 2) (ℓ := ℓ) (volA := volA) (A := A) (i := i)
      (j := i.succAbove j') (Φ := Ψ) hℓ hvol hA hAc hvolA (Fin.succAbove_ne i j').symm hΨc hmemins
      (om q.1.1 q.1.2))]
  simp only [ins2_apply_i, ins2_apply_succ, ins2_update_i, ins2_update_succ]

local notation "𝔼3" => EuclideanSpace ℝ (Fin 3)

/-! ## The per-pair objects

`Work.BoseFixB1.pairFive`, `Work.BoseFixB1.pairBlock` and the exact unordered-pair identity
`Work.BoseFixB1.pairFive_add_swap` (FS's "*the first term of `eq:Q3+Q4CS` cancels the second line
of `eq:Q1n0`*", done as an identity) now live **below** this module, in
`Submission.Work.BoseFixB1.PairBlockCore`, so that the modules proving the sum-level reduction
`Work.BoseFixB1S.boxQSumSubA2Block` can be imported *by* this file (a statement about this file's
objects that is proved in a module importing this file cannot be used here: import cycle). -/

/-- **The manifest square is non-negative** (PROVED here; this is step (i) of the assembly in
`FINDING_boxQSum_reduction_sign_and_sharp_constant.md` §1).

`boxSqPart` is `½Σ_{p∈pairSet}∫(D_p+s_p+ω_pA_p)²w`; the integrand is a square times the pair
kernel `w = wSmallPair M ℓ d u v`, which is `≥ 0` pointwise for `0 ≤ v`, so each integral is
`≥ 0`.  No continuity, and no integrability hypothesis is needed
(`MeasureTheory.integral_nonneg`). -/
private lemma wSmallPair_nonneg_local {v : 𝔼3 → ℝ} (hv : 0 ≤ v) (M : ℕ) (ℓ d : ℝ)
    (u x y : 𝔼3) : 0 ≤ Submission.BoseGases.wSmallPair M ℓ d u v x y := by
  rw [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled,
    Submission.BoseGases.convScaleSmall]
  refine mul_nonneg
    (mul_nonneg (Submission.BoseGases.chiSmallB_nonneg M ℓ d u x) ?_)
    (Submission.BoseGases.chiSmallB_nonneg M ℓ d u y)
  refine div_nonneg (div_nonneg (hv _) ?_) (Submission.BoseGases.convScale_nonneg ℓ _)
  rw [Submission.BoseGases.conv3Small]
  exact integral_nonneg fun w =>
    mul_nonneg (Submission.BoseGases.chiSmall_nonneg M w)
      (Submission.BoseGases.chiSmall_nonneg M (_ - w))

theorem boxSqPart_nonneg {v : 𝔼3 → ℝ} (hv : 0 ≤ v) {M : ℕ} {ℓ d : ℝ}
    (u : 𝔼3) (om : 𝔼3 → 𝔼3 → ℝ) {N : ℕ} (Φ : Submission.BoseGases.X N → ℝ) :
    0 ≤ boxSqPart (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
        (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.wSmallPair M ℓ d u v) om Φ := by
  unfold boxSqPart pairSq
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun p _ => ?_)
  exact MeasureTheory.integral_nonneg fun x =>
    mul_nonneg (sq_nonneg _) (wSmallPair_nonneg_local hv M ℓ d u (x p.1) (x p.2))

/-! ## The pure-real core of the assembly

Once the sum-level reduction `Work.BoseFixB1S.boxQSum_sub_boxA2_blockSum` and the square/cross
split `Work.BoseFixB1.boxSqPart_add_boxCrossPart_eq_blockSum` have been applied, the target is
*exactly* the pure-real inequality below — with `Sqp = boxSqPart`, `L = boxCrossPart`,
`P`, `Q` the two one-slot `μ`-objects and `G` the `A₀`-defect.  Its proof uses only

* `0 ≤ Sq` (the manifest square, `boxSqPart_nonneg`),
* the analytic bound `L + M₁G + Ca(μ+S/V)n₊ ≥ 2μP + μQ` (the *lower* bound on the cross term),
* `hcS2` (`S²−S ≤ Pc`) and `0 ≤ M₁ ≤ M₂` (which make the remaining `Pc`-block `≥ 0`).

This is step (iv) of `FINDING_boxQSum_reduction_sign_and_sharp_constant.md` §4. -/
theorem boxArithCore {V μ M₁ M₂ S Pc nq C aa Sqp L P Q : ℝ}
    (hV : 0 < V) (hM1 : 0 ≤ M₁) (hM2 : M₁ ≤ M₂) (hPc : 0 ≤ Pc)
    (hcS2 : S * S - S ≤ Pc) (hSqp : 0 ≤ Sqp)
    (hcross : L + M₁ * ((1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V) + 1 / (4 * V ^ 2))
      + C * aa * (μ + S / V) * nq ≥ 2 * μ * P + μ * Q) :
    0 ≤ Sqp + L + M₁ * ((1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V) + 1 / (4 * V ^ 2))
      + (1 / 2) * (M₂ / V ^ 2) * Pc - (1 / 2) * (M₁ / V ^ 2) * (S ^ 2 - S)
      + C * aa * (μ + S / V) * nq - 2 * μ * P - μ * Q := by
  have hV2 : (0 : ℝ) < V ^ 2 := pow_pos hV 2
  have hcS2' : S ^ 2 - S ≤ Pc := by simpa only [sq] using hcS2
  have hstep : (0 : ℝ) ≤ (1 / 2) * (M₂ / V ^ 2) * Pc - (1 / 2) * (M₁ / V ^ 2) * (S ^ 2 - S) := by
    have h1 : (1 / 2) * (M₁ / V ^ 2) * (S ^ 2 - S) ≤ (1 / 2) * (M₁ / V ^ 2) * Pc :=
      mul_le_mul_of_nonneg_left hcS2' (by positivity)
    have h2 : (1 / 2) * (M₁ / V ^ 2) * Pc ≤ (1 / 2) * (M₂ / V ^ 2) * Pc :=
      mul_le_mul_of_nonneg_right
        (by have := div_le_div_of_nonneg_right hM2 (le_of_lt hV2); linarith) hPc
    linarith
  have hmain : (0 : ℝ) ≤ Sqp + (L + M₁ * ((1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V)
        + 1 / (4 * V ^ 2)) + C * aa * (μ + S / V) * nq - (2 * μ * P + μ * Q))
      + ((1 / 2) * (M₂ / V ^ 2) * Pc - (1 / 2) * (M₁ / V ^ 2) * (S ^ 2 - S)) :=
    add_nonneg (add_nonneg hSqp (by linarith [hcross])) hstep
  linarith [hmain]


/-! ## The assembly lemma: the target from the four pieces

`boxTarget_of_pieces` is the *final step* of the target's proof and is PROVED here.  It takes the
four concrete facts the rest of the team provides —

* `hred` — the sum-level reduction `Work.BoseFixB1S.boxQSum_sub_boxA2_blockSum` (R1),
* `hsplit` — the square/cross split `Work.BoseFixB1.boxSqPart_add_boxCrossPart_eq_blockSum`,
* `hslack` — the exact `A₀`-slack `Work.BoseFixB1.boxQ0_sub_a0MainLocBox_eq` (R2),
* `hcross` — the **analytic bound (♦)** `boxCrossPart + M₁G + Ca(μ+S/V)n₊ ≥ 2μP + μQ`
  (delegated: `Work.BoseFixB1.boxCrossLower`),
* `hsq` — `0 ≤ boxSqPart` (PROVED: `boxSqPart_nonneg`),

and concludes the target's inequality, the only remaining arithmetic being that of
`boxArithCore`. -/
theorem boxTarget_of_pieces {V μ M₁ M₂ S Pc nq C aa Sqp L P Q Q0 A2 Qsum a0 : ℝ}
    (hV : 0 < V) (hM1 : 0 ≤ M₁) (hM2 : M₁ ≤ M₂) (hPc : 0 ≤ Pc)
    (hcS2 : S * S - S ≤ Pc) (hSqp : 0 ≤ Sqp)
    (hred : Qsum - A2 + (2 * μ * P + μ * Q) = Q0 + (Sqp + L))
    (hslack : Q0 - a0 = M₁ * ((1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V) + 1 / (4 * V ^ 2))
        + (1 / 2) * (M₂ / V ^ 2) * Pc - (1 / 2) * (M₁ / V ^ 2) * (S ^ 2 - S))
    (hcross : L + M₁ * ((1 / 4) * (S / V - μ) ^ 2 + (S / V + μ) / (2 * V) + 1 / (4 * V ^ 2))
      + C * aa * (μ + S / V) * nq ≥ 2 * μ * P + μ * Q) :
    a0 + A2 - C * aa * (μ + S / V) * nq ≤ Qsum := by
  have hcore := boxArithCore hV hM1 hM2 hPc hcS2 hSqp hcross
  linarith [hred, hslack, hcore]

/-! ## The target

**How to finish the proof** (every ingredient except the last is PROVED; see
`FINDING_boxQSum_reduction_sign_and_sharp_constant.md`).  With
`V := boxMass ℓ d u`, `A := dlBox ℓ d u`, `w := wSmallPair M ℓ d u v`,
`w₁ := wSmall1Pair h M ℓ d u`, `w₂ := wSmallPair M ℓ d u (g2 v h)`, `om := omC (choose h)`:

1. `obtain ⟨C, hC0, hC⟩ := Work.BoseFixB1.boxCrossLower (the analytic core (♦))`, then
   `refine ⟨C, hC0, ?_⟩` and `intro` all the target's variables;
2. `obtain ⟨hint0, hint1, hint2, hint3, hint4, hintBlk⟩ :=
   Work.BoseFixB1.boxFragmentsIntegrable ...` (the six `IntegrableOn` hypotheses of (R1));
3. `obtain ⟨hBlk, hSq, hCr⟩ := Work.BoseFixB1.boxPairBlockIntegrable ...` (the three
   `IntegrableOn` hypotheses of the split);
4. `obtain ⟨hW2i, hFib⟩ := Work.BoseFixB1.boxQ0SlackIntegrable ...` (the two `IntegrableOn`
   hypotheses of (R2));
5. (R1) `Work.BoseFixB1S.boxQSum_sub_boxA2_blockSum`, (R2)
   `Work.BoseFixB1.boxQ0_sub_a0MainLocBox_eq`, the split
   `Work.BoseFixB1.boxSqPart_add_boxCrossPart_eq_blockSum`, `Work.BoseFixB1.boxSqPart_nonneg`,
   the pointwise kernel identities (`Work.BoseFixB1.wSmall1Pair_eq_mul`,
   `Work.BoseFixB1.wSmallPair_g2_eq_mul`, plus `Work.BoseGases.wSmallPair_sym`/`conv3Small_symm`
   for `hwsym`/`homsym`);
6. finish with `Work.BoseFixB1.boxTarget_of_pieces` at
   `Qsum := boxQSum ...`, `A2 := boxA2 ...`, `Q0 := boxQ0 ...`,
   `a0 := a0MainLocBox V μ M₁ S`, `Sqp := boxSqPart ...`, `L := boxCrossPart ...`,
   `S := boxFlatCount ...`, `Pc := boxPairCount ...`, `nq := boxQCount ...`,
   `P` and `Q` the two `μ`-sums, `aa := a v`.

The only step not yet available is (♦) (`boxCrossLower`, delegated); everything else is
complete and machine-checked in this workspace. -/


end Work.BoseFixB1.Clean
