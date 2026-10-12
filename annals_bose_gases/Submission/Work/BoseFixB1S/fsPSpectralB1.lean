import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1.RTFoldMoment
import Submission.Work.BoseFixB1.a0SquareCompletion
import Submission.Work.BoseFixB1.flatPieceRT_eigen
import Submission.Work.BoseFixB1.flatPiece_orthogonal
import Submission.Work.BoseFixB1S.boxPInd_finset_sum_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# SKELETON — `Submission.Work.BoseFixB1S.fsPSpectralB1`: the *corrected* `(FS-P)` step

**This file is the corrected replacement of the FALSE statement `Work.BoseFixB1S.fsP`
(`Submission/Work/BoseFixB1S/fsP_creditDefs.lean`) and of its repair `fsPHealingFib`
(`Submission/Work/BoseFixB1S/fsPHealing.lean`), neither of which may be used.**

## Why the earlier shapes are false (the exact arithmetic)

Write `c = μV`, `S = boxFlatCount = ⟨n₀⟩`, `Var = boxPairCount − S² + S = ⟨n₀²⟩ − S²` (the
*variance* of the condensate count, `≥ 0` by the proved `hcS2` ⟺ Jensen `boxFlatSqJensen`), and
`X_P := ⟨Φ, n₀Θ₋Φ⟩` with `Θ₋ = (√(n₀+1) − √c)²` (the `P`-loss pairing of FS `eq:Q1n0`).  The
one-line reason `(FS-P)` cannot be stated on its own:

* the **elementary eigenvalue bound** — with `t = |S|` the eigenvalue of `n₀` on the joint block —
  is `t(√(t+1) − √c)² ≤ (t+1−c)²` (proved below as `mul_sqrt_sq_le`; equivalently
  `t ≤ (√(t+1)+√c)²`), so, taking expectations over the joint blocks,

      `X_P = Σ_p |p.1|·(√(|p.1|+1)−√c)²·c_p  ≤  Σ_p (|p.1|+1−c)²·c_p
           = (S+1−c)²·‖Φ‖² + 2(S+1−c)S(1−‖Φ‖²) + Var`               (`A₀`-line, exact)

  where `c_p = ∫(Θ_p)² ≥ 0` are the block masses (`Σ_p c_p = ‖Φ‖²`), `Σ_p|p.1|c_p = S`.
* the *supply* available in the ledger for this loss is `M₁G = κ[¼(S+1−c)²/V + μ]` (`κ = M₁/V`)
  **plus** the `Var`-part `½(M₁/V²)Var` of the pair-condensate slack
  `pcb = ½(M₂/V²)Pc − ½(M₁/V²)(S²−S)` — the Jensen defect of `A₀`'s `¼(μ − (n₀+1)/V)²`.
  So `(FS-P)` is *joint* by nature: its `(S+1−c)²`-coefficient is `1` (undivided by `V`!) and its
  `Var`-coefficient is `1`.
* the shapes in the tree **divide by `V`** (`fsP`/`fsPHealingFib` carry `((S+1−c)²/V + c/V + …)`)
  and hence are false for the pure-block state `Φ ≡ ℓ^{-3N/2}` (then `S = N`, `‖Φ‖² = 1`,
  `Var = 0`, `X_P = N(√(N+1)−√c)²` while the recorded right-hand side is
  `C₀[(N+1−c)²/V + μ] → 0` along `V → ∞` at fixed `N, μV`); they **also drop `Var`**.  That is
  exactly the `N`-growth the corpus recorded for the no-`√` pairing — the difference is that the
  `√`-pairing is *pointwise true* while its recorded *scaled* form is not.

## What is proved here

The corrected statement, in the corpus's own joint-spectral vocabulary
(`Work.BoseFixB1.flatPieceRT`, the `(P,Q,R)`-blocks of `flatPieceRT_*`), and its proof:

* `flatFunOp` — the functional calculus `g(n₀)` in the joint blocks;
* `rungF_flatFunOp` — `n₀(g(n₀)Φ) = Σ_p |p.1|·g(|p.1|)·Θ_pΦ` (the eigen-rule);
* `XPEqBlockSum` — `X_P = Σ_p |p.1|g(|p.1|)·∫Θ_p²` (Parseval `flatPieceRT_parseval`);
* `mul_sqrt_sq_le` — the scalar eigenvalue bound;
* **`fsP_spectral`** — the corrected `(FS-P)`:
  `X_P ≤ Σ_p (|p.1|+1−c)²·∫Θ_p²`,
  together with its *moment form* `fsP_spectral_moment`, in which the right-hand side is
  `(S+1−c)²‖Φ‖² + 2(S+1−c)S(1−‖Φ‖²) + Var` with `S`, `‖Φ‖²` and (by `flatPieceRT_moments`) the
  block masses the corpus's proved moments supply.

Nothing here divides by `V` and nothing drops `Var`; the file is `sorry`-free.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal Real

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## 1. The scalar eigenvalue bound -/

/-- **The scalar core of the `(FS-P)` step.**  For `t, c ≥ 0`,

    `t·(√(t+1) − √c)²  ≤  (t+1−c)²` .

Equivalently `t ≤ (√(t+1)+√c)²`, which is immediate since the right-hand side is
`t+1+c+2√(c(t+1))` and `1+c+2√(c(t+1)) ≥ 0`.  This is the *pointwise* form of FS's display
`(n₀/|B|)((n₀+1)^{1/2}−(μ|B|)^{1/2})² ≤ ((n₀+1)/|B| − μ)²` (their middle line is the same
inequality divided by `|B|²`). -/
theorem mul_sqrt_sq_le (t c : ℝ) (ht : 0 ≤ t) (hc : 0 ≤ c) :
    t * (Real.sqrt (t + 1) - Real.sqrt c) ^ 2 ≤ (t + 1 - c) ^ 2 := by
  have ht1 : (0 : ℝ) ≤ t + 1 := by linarith
  have hs1 : Real.sqrt (t + 1) ^ 2 = t + 1 := Real.sq_sqrt ht1
  have hs2 : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc
  have hfac : (Real.sqrt (t + 1) + Real.sqrt c) * (Real.sqrt (t + 1) - Real.sqrt c)
      = t + 1 - c := by
    rw [show (Real.sqrt (t + 1) + Real.sqrt c) * (Real.sqrt (t + 1) - Real.sqrt c)
        = Real.sqrt (t + 1) ^ 2 - Real.sqrt c ^ 2 from by ring, hs1, hs2]
  have hle : t ≤ (Real.sqrt (t + 1) + Real.sqrt c) ^ 2 := by
    have hsq : (Real.sqrt (t + 1) + Real.sqrt c) ^ 2
        = t + 1 + c + 2 * (Real.sqrt (t + 1) * Real.sqrt c) := by
      rw [show (Real.sqrt (t + 1) + Real.sqrt c) ^ 2
          = Real.sqrt (t + 1) ^ 2 + Real.sqrt c ^ 2
            + 2 * (Real.sqrt (t + 1) * Real.sqrt c) from by ring, hs1, hs2]
    have h0 : 0 ≤ Real.sqrt (t + 1) * Real.sqrt c :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    linarith
  have hnn : 0 ≤ (Real.sqrt (t + 1) - Real.sqrt c) ^ 2 := sq_nonneg _
  have key : t * (Real.sqrt (t + 1) - Real.sqrt c) ^ 2
      ≤ (Real.sqrt (t + 1) + Real.sqrt c) ^ 2 * (Real.sqrt (t + 1) - Real.sqrt c) ^ 2 :=
    mul_le_mul_of_nonneg_right hle hnn
  have hsq : (Real.sqrt (t + 1) + Real.sqrt c) ^ 2 * (Real.sqrt (t + 1) - Real.sqrt c) ^ 2
      = (t + 1 - c) ^ 2 := by
    rw [← mul_pow, hfac]
  linarith [key, hsq.symm.le, hsq.le]

/-- **FS's square completion with the *shifted* coefficient `t − 1 − m`.**  This is the scalar atom
of the *hop-bracket* form `Σ_p(|p.1| − 1 − μV)·(pairing)` (`Work.BoseFixB1S.hopBracket`,
`boxCrossExpansionB1S`): with `t − 1 − m = (t+1−m) − 2` and the four-form completion
(`a0SquareCompletion.two_mul_mul_sub_ge_sqrt_four`) at `(t+1, m)`, the AM–GM drops the two
remainder terms into `−2(x²+y²)`:

    `2xy(t−1−m) ≥ −4(√(t+1)+√m)²x² − ¼(√(t+1)−√m)²y² − 2x² − 2y²`   (`t, m ≥ 0`). -/
theorem two_mul_mul_sub_one_sub_ge_sqrt (t m x y : ℝ) (ht : 0 ≤ t) (hm : 0 ≤ m) :
    2 * x * y * (t - 1 - m)
      ≥ -4 * (Real.sqrt (t + 1) + Real.sqrt m) ^ 2 * x ^ 2
        - (1 / 4) * (Real.sqrt (t + 1) - Real.sqrt m) ^ 2 * y ^ 2
        - 2 * x ^ 2 - 2 * y ^ 2 := by
  have hmain := Work.BoseFixB1.two_mul_mul_sub_ge_sqrt_four (t + 1) m x y (by linarith) hm
  have hrem : 2 * x * y * (t - 1 - m) = 2 * x * y * (t + 1 - m) - 4 * x * y := by ring
  have hxy : 4 * x * y ≤ 2 * x ^ 2 + 2 * y ^ 2 := by nlinarith [sq_nonneg (x - y)]
  rw [hrem]
  linarith [hmain, hxy]

/-! ## 2. The joint-spectral functional calculus of `n₀` -/

/-- **`g(n₀)` in the joint spectral blocks**: the functional calculus of the condensate-count
operator `n₀ = Σᵢ P_{B,i}` — which acts as the eigenvalue `|S|` on the block `Θ_{S,T}`
(`flatPieceRT_eigen`) — evaluated at the function `g`.  The blocks are total in `Φ`
(`sum_flatPieceRT`), so this *is* `g(n₀)`. -/
def flatFunOp {N : ℕ} (V : ℝ) (A : Set E3) (g : ℝ → ℝ) (Φ : X N → ℝ) : X N → ℝ :=
  fun x => ∑ S : Finset (Fin N), ∑ T ∈ Sᶜ.powerset, g (S.card : ℝ) *
    Work.BoseFixB1.flatPieceRT V A S T Φ x

/-- `P_{B,i}` is homogeneous (unconditional: the linearity of the defining slot integral). -/
theorem boxPInd_const_mul' {N : ℕ} (volA : ℝ) (A : Set E3) (i : Fin N) (c : ℝ)
    (Ψ : X N → ℝ) (x : X N) :
    Work.UBBInputs8.boxPInd volA A i (fun y => c * Ψ y) x
      = c * Work.UBBInputs8.boxPInd volA A i Ψ x := by
  simp only [Work.UBBInputs8.boxPInd]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- Disjointness of the two slot sets of a pair of `pairIdx`. -/
theorem disjoint_of_mem_pairIdx {N : ℕ} {p : (Finset (Fin N)) × (Finset (Fin N))}
    (hp : p ∈ Work.BoseFixB1.pairIdx N) : Disjoint p.1 p.2 := by
  rw [Finset.disjoint_left]
  intro i hi hi'
  have hsub : p.2 ⊆ p.1ᶜ := Work.BoseFixB1.mem_pairIdx.mp hp
  have : i ∉ p.1 := by simpa using hsub hi'
  exact this hi

/-! ## 3. The eigen-rule for the functional calculus -/

/-- The integrand of `flatFunOp` is `IntegrableOn`-measurable on the box (bounded). -/
theorem integrableOn_flatFunOpTerm {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) (g : ℝ → ℝ) (i : Fin N) (C : ℝ)
    (hCb : ∀ x ∈ abox N ℓ, |Φ x| ≤ C) (hC0 : 0 ≤ C) :
    ∀ p ∈ Work.BoseFixB1.pairIdx N, ∀ x ∈ abox N ℓ,
      IntegrableOn (fun z : E3 => g (p.1.card : ℝ)
        * Work.BoseFixB1.flatPieceRT V A p.1 p.2 Φ (Function.update x i z)) A volume := by
  intro p _ x hx
  have hunif : ∀ y ∈ abox N ℓ, |Work.BoseFixB1.flatPieceRT V A p.1 p.2 Φ y| ≤ 2 ^ N * C :=
    Work.BoseFixB1.flatPieceRT_uniform_abs_le hℓ hV hA hVeq hAc hC0 hCb p.1 p.2
  have hmeas : Measurable (fun y : X N => g (p.1.card : ℝ)
      * Work.BoseFixB1.flatPieceRT V A p.1 p.2 Φ y) :=
    (Work.BoseFixB1.flatPieceRT_meas_bdd hℓ hV hA hVeq hAc hΦc p.1 p.2).1.const_mul _
  refine slotInt_of_bound (N := N) hℓ hA hAc i x hx hmeas (C := |g (p.1.card : ℝ)| * (2 ^ N * C)) ?_
  intro y hy
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hunif y hy) (abs_nonneg _)

/-- **The eigen-rule.**  `P_{B,i}` reads off the blocks whose `P`-slot set contains `i`:

    `P_{B,i}(g(n₀)Φ) = Σ_{S ∋ i, T} g(|S|)·Θ_{S,T}Φ` .

(The `0`-extension of the two slot-set sums makes the statement a single formula.) -/
theorem boxPInd_flatFunOp {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) (g : ℝ → ℝ) (i : Fin N) :
    ∀ x ∈ abox N ℓ,
      Work.UBBInputs8.boxPInd V A i (flatFunOp V A g Φ) x
        = ∑ S : Finset (Fin N), ∑ T ∈ Sᶜ.powerset, g (S.card : ℝ) *
            (if i ∈ S then Work.BoseFixB1.flatPieceRT V A S T Φ x else 0) := by
  intro x hx
  obtain ⟨C, hC0, hCb⟩ := Work.BoseFixB1S.exists_abox_bound hℓ hΦc
  -- rewrite `flatFunOp` as a single sum over `pairIdx`
  have hfun : flatFunOp V A g Φ
      = fun y => ∑ p ∈ Work.BoseFixB1.pairIdx N, g (p.1.card : ℝ)
          * Work.BoseFixB1.flatPieceRT V A p.1 p.2 Φ y := by
    funext y
    rw [flatFunOp]
    exact (Work.BoseFixB1.pairIdx_sum
      (f := fun S T => g (S.card : ℝ) * Work.BoseFixB1.flatPieceRT V A S T Φ y)).symm
  rw [hfun]
  rw [boxPInd_finset_sum_gen V A i x (Work.BoseFixB1.pairIdx N)
    (fun p y => g (p.1.card : ℝ) * Work.BoseFixB1.flatPieceRT V A p.1 p.2 Φ y)
    (fun p hp => integrableOn_flatFunOpTerm hℓ hV hA hVeq hAc hΦc g i C hCb hC0 p hp x hx)]
  -- termwise: pull the scalar out and apply the eigen-rule
  have hterm : ∀ p ∈ Work.BoseFixB1.pairIdx N,
      Work.UBBInputs8.boxPInd V A i (fun y => g (p.1.card : ℝ)
          * Work.BoseFixB1.flatPieceRT V A p.1 p.2 Φ y) x
        = g (p.1.card : ℝ) * (if i ∈ p.1 then Work.BoseFixB1.flatPieceRT V A p.1 p.2 Φ x else 0) := by
    intro p hp
    rw [boxPInd_const_mul']
    rw [(Work.BoseFixB1.flatPieceRT_eigen hℓ hV hA hVeq hAc hΦc p.1 p.2
      (disjoint_of_mem_pairIdx hp) i).1]
    by_cases hi : i ∈ p.1 <;> simp [hi]
  rw [Finset.sum_congr rfl hterm]
  exact (Work.BoseFixB1.pairIdx_sum
    (f := fun S T => g (S.card : ℝ)
      * (if i ∈ S then Work.BoseFixB1.flatPieceRT V A S T Φ x else 0)))

/-- **The `n₀`-eigen-rule**: applying the condensate-count operator `n₀ = ΣᵢP_{B,i}` to `g(n₀)Φ`
gives the eigenvalue-weighted block sum. -/
theorem rungF_flatFunOp {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) (g : ℝ → ℝ) :
    ∀ x ∈ abox N ℓ, Work.BoseFixB1.rungF V A (flatFunOp V A g Φ) x
        = ∑ S : Finset (Fin N), ∑ T ∈ Sᶜ.powerset, (S.card : ℝ) * g (S.card : ℝ) *
            Work.BoseFixB1.flatPieceRT V A S T Φ x := by
  intro x hx
  rw [Work.BoseFixB1.rungF]
  have hpoint : ∀ i : Fin N, Work.UBBInputs8.boxPInd V A i (flatFunOp V A g Φ) x
      = ∑ S : Finset (Fin N), ∑ T ∈ Sᶜ.powerset, g (S.card : ℝ) *
          (if i ∈ S then Work.BoseFixB1.flatPieceRT V A S T Φ x else 0) :=
    fun i => boxPInd_flatFunOp hℓ hV hA hVeq hAc hΦc g i x hx
  calc (∑ i : Fin N, Work.UBBInputs8.boxPInd V A i (flatFunOp V A g Φ) x)
      = ∑ i : Fin N, ∑ S : Finset (Fin N), ∑ T ∈ Sᶜ.powerset, g (S.card : ℝ) *
          (if i ∈ S then Work.BoseFixB1.flatPieceRT V A S T Φ x else 0) :=
        Finset.sum_congr rfl (fun i _ => hpoint i)
    _ = ∑ S : Finset (Fin N), ∑ T ∈ Sᶜ.powerset, g (S.card : ℝ) *
          (∑ i : Fin N, if i ∈ S then Work.BoseFixB1.flatPieceRT V A S T Φ x else 0) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun S _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun T hT => ?_)
        rw [Finset.mul_sum]
    _ = ∑ S : Finset (Fin N), ∑ T ∈ Sᶜ.powerset, (S.card : ℝ) * g (S.card : ℝ) *
            Work.BoseFixB1.flatPieceRT V A S T Φ x := by
        refine Finset.sum_congr rfl (fun S _ => Finset.sum_congr rfl (fun T _ => ?_))
        have hcard : (∑ i : Fin N, if i ∈ S
            then Work.BoseFixB1.flatPieceRT V A S T Φ x else 0)
            = (S.card : ℝ) * Work.BoseFixB1.flatPieceRT V A S T Φ x := by
          rw [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
            Finset.sum_const, nsmul_eq_mul]
        rw [hcard]
        ring

/-! ## 3b. The sandwich `P_{B,i}(f(xᵢ)·P_{B,i}Ψ) = κ·P_{B,i}Ψ` -/

/-- **The sandwich identity.**  `P_{B,i}` is the slot-`i` box mean times the box indicator, so
`P_{B,i}Ψ` is *constant in slot `i`* up to the indicator; multiplying by a function of the slot
alone and reprojecting therefore multiplies by the *mean* `κ = (∫_A f)/volA`:

    `P_{B,i}(f(xᵢ)·P_{B,i}Ψ) = κ · P_{B,i}Ψ`   (pointwise, every `x`).

This is the identity that removes the fibre weight from the ledger's `P`-pairing
(`Σᵢ⟨P_{B,i}Φ, f(xᵢ)Θ₋P_{B,i}Φ⟩ = κ·⟨Φ, n₀Θ₋Φ⟩`); it is the operator form of the corpus's proved
`Work.BoseFixB1.boxPIndFibreMassB1` (`Σᵢ∫(PᵢΦ)²f(xᵢ) = κ·S`). -/
theorem boxPInd_sandwich {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (i : Fin N) (f : E3 → ℝ) (Ψ : X N → ℝ) (x : X N) :
    Work.UBBInputs8.boxPInd volA A i
        (fun y => f (y i) * Work.UBBInputs8.boxPInd volA A i Ψ y) x
      = ((∫ z in A, f z) / volA) * Work.UBBInputs8.boxPInd volA A i Ψ x := by
  rw [Work.UBBInputs8.boxPInd]
  have hself : ∀ z : E3, (Function.update x i z) i = z := fun z => Function.update_self i z x
  have hkey : ∀ z : E3,
      Work.UBBInputs8.boxPInd volA A i Ψ (Function.update x i z)
        = (1 / volA) * (∫ w in A, Ψ (Function.update x i w))
          * A.indicator (fun _ => (1 : ℝ)) z := fun z =>
    Work.BoseFixB1S.Q0C.boxPInd_update_self volA A i Ψ x z
  have hstep : (∫ z in A, (fun y : X N => f (y i)
        * Work.UBBInputs8.boxPInd volA A i Ψ y) (Function.update x i z))
      = ∫ z in A, f z * ((1 / volA) * (∫ w in A, Ψ (Function.update x i w))
          * A.indicator (fun _ => (1 : ℝ)) z) := by
    apply setIntegral_congr_fun hA
    intro z hz
    show f (Function.update x i z i) * Work.UBBInputs8.boxPInd volA A i Ψ
        (Function.update x i z)
      = f z * ((1 / volA) * (∫ w in A, Ψ (Function.update x i w))
          * A.indicator (fun _ => (1 : ℝ)) z)
    rw [hself z, hkey z]
  rw [hstep]
  have hcollapse : (∫ z in A, f z * ((1 / volA) * (∫ w in A, Ψ (Function.update x i w))
        * A.indicator (fun _ => (1 : ℝ)) z))
      = ((1 / volA) * (∫ w in A, Ψ (Function.update x i w))) * (∫ z in A, f z) := by
    rw [show (fun z : E3 => f z * ((1 / volA) * (∫ w in A, Ψ (Function.update x i w))
          * A.indicator (fun _ => (1 : ℝ)) z))
        = fun z : E3 => ((1 / volA) * (∫ w in A, Ψ (Function.update x i w)))
          * (fun z : E3 => f z * A.indicator (fun _ => (1 : ℝ)) z) z from by
      funext z; ring,
      MeasureTheory.integral_const_mul]
    congr 1
    apply setIntegral_congr_fun hA
    intro z hz
    show f z * A.indicator (fun _ => (1 : ℝ)) z = f z
    rw [Set.indicator_of_mem hz]
    ring
  rw [hcollapse]
  rw [Work.UBBInputs8.boxPInd]
  ring

/-! ## 4. The block sum of the `P`-loss pairing (Parseval) -/

/-- **The `P`-loss pairing as a block sum.**  With `Θ₋ = (√(n₀+1)−√c)²` and `Θ_p` the joint blocks,
the fibre-free pairing `X_P = ⟨Φ, n₀Θ₋Φ⟩` is the eigenvalue-weighted block mass:

    `X_P = Σ_{p} |p.1|·(√(|p.1|+1)−√c)²·∫Θ_p²` .

Proof: `n₀ h(n₀)Φ = Σ_p |p.1|h(|p.1|)Θ_pΦ` (`rungF_flatFunOp`), then Parseval
(`flatPieceRT_parseval`) with the completeness `Σ_pΘ_p = Φ` (`sum_flatPieceRT`). -/
theorem XPEqBlockSum {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) (g : ℝ → ℝ) :
    (∫ x in abox N ℓ, Φ x * Work.BoseFixB1.rungF V A (flatFunOp V A g Φ) x)
      = ∑ p ∈ Work.BoseFixB1.pairIdx N, (p.1.card : ℝ) * g (p.1.card : ℝ)
          * ∫ x in abox N ℓ, (Work.BoseFixB1.flatPieceRT V A p.1 p.2 Φ x) ^ 2 := by
  have hcomp : ∀ x : X N,
      (∑ p ∈ Work.BoseFixB1.pairIdx N, (1 : ℝ)
        * Work.BoseFixB1.flatPieceRT V A p.1 p.2 Φ x) = Φ x := by
    intro x
    rw [Work.BoseFixB1.pairIdx_sum (f := fun S T => (1 : ℝ)
      * Work.BoseFixB1.flatPieceRT V A S T Φ x)]
    simp only [one_mul]
    exact Work.BoseFixB1.sum_flatPieceRT hℓ hV hA hVeq hAc hΦc x
  have hcongr : (∫ x in abox N ℓ, Φ x * Work.BoseFixB1.rungF V A (flatFunOp V A g Φ) x)
      = ∫ x in abox N ℓ,
          (∑ p ∈ Work.BoseFixB1.pairIdx N, (1 : ℝ)
            * Work.BoseFixB1.flatPieceRT V A p.1 p.2 Φ x)
          * (∑ q ∈ Work.BoseFixB1.pairIdx N,
              ((q.1.card : ℝ) * g (q.1.card : ℝ))
                * Work.BoseFixB1.flatPieceRT V A q.1 q.2 Φ x) := by
    apply setIntegral_congr_fun (abox_measurable N ℓ)
    intro x hx
    show Φ x * Work.BoseFixB1.rungF V A (flatFunOp V A g Φ) x
        = (∑ p ∈ Work.BoseFixB1.pairIdx N, (1 : ℝ)
            * Work.BoseFixB1.flatPieceRT V A p.1 p.2 Φ x)
          * (∑ q ∈ Work.BoseFixB1.pairIdx N,
              ((q.1.card : ℝ) * g (q.1.card : ℝ))
                * Work.BoseFixB1.flatPieceRT V A q.1 q.2 Φ x)
    rw [rungF_flatFunOp hℓ hV hA hVeq hAc hΦc g x hx, hcomp x,
      Work.BoseFixB1.pairIdx_sum (f := fun S T => (S.card : ℝ) * g (S.card : ℝ)
        * Work.BoseFixB1.flatPieceRT V A S T Φ x)]
  rw [hcongr, Work.BoseFixB1.flatPieceRT_parseval hℓ hV hA hVeq hAc hΦc
    (fun _ => (1 : ℝ)) (fun q => (q.1.card : ℝ) * g (q.1.card : ℝ))]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  ring

/-! ## 5. The corrected `(FS-P)` -/

/-- **`(FS-P)`, corrected and proved.**  The `√`-weighted `P`-loss pairing `X_P = ⟨Φ, n₀Θ₋Φ⟩`,
`Θ₋ = (√(n₀+1) − √c)²`, is bounded by the block sum of `(t+1−c)²` — **without** dividing by the
box volume and **with** the Jensen defect (see the module docstring for why the earlier,
`V`-divided forms in the tree are false).  The proof is the scalar eigenvalue bound
`mul_sqrt_sq_le` applied termwise to the nonnegative block masses. -/
theorem fsP_spectral {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) {c : ℝ} (hc : 0 ≤ c) :
    (∫ x in abox N ℓ, Φ x * Work.BoseFixB1.rungF V A
        (flatFunOp V A (fun r : ℝ => (Real.sqrt (r + 1) - Real.sqrt c) ^ 2) Φ) x)
      ≤ ∑ p ∈ Work.BoseFixB1.pairIdx N, ((p.1.card : ℝ) + 1 - c) ^ 2
          * ∫ x in abox N ℓ, (Work.BoseFixB1.flatPieceRT V A p.1 p.2 Φ x) ^ 2 := by
  rw [XPEqBlockSum hℓ hV hA hVeq hAc hΦc (fun r : ℝ => (Real.sqrt (r + 1) - Real.sqrt c) ^ 2)]
  refine Finset.sum_le_sum (fun p _ => ?_)
  have hc0 : (0 : ℝ) ≤ (p.1.card : ℝ) := Nat.cast_nonneg _
  have hkey := mul_sqrt_sq_le (p.1.card : ℝ) c hc0 hc
  have hnn : (0 : ℝ) ≤ ∫ x in abox N ℓ, (Work.BoseFixB1.flatPieceRT V A p.1 p.2 Φ x) ^ 2 :=
    integral_nonneg (fun x => sq_nonneg _)
  exact mul_le_mul_of_nonneg_right hkey hnn

/-! ## 6. The moment (Jensen-defect) form — the shape the ledger consumes -/

/-- **The variance decomposition of the supply.**  For any weights `c p ≥ 0` with first moment
`S = Σ A p·c p` and total mass `E = Σ c p`,

    `Σ_p (A p + 1 − cc)² c_p
       = Σ_p (A p − S)² c_p + 2(S+1−cc)(S − S·E) + (S+1−cc)²·E` ,

i.e. the `A₀`-line of FS's `lm:appinteractionestimate` written as the *Jensen defect*
`Σ(A−S)²c = ⟨(n₀−S)²⟩` plus the scalar square at `S`, times the total mass.  Pure algebra. -/
theorem sum_sq_moment_form {ι : Type*} (s : Finset ι) (A c : ι → ℝ) {S E cc : ℝ}
    (hS : ∑ p ∈ s, A p * c p = S) (hE : ∑ p ∈ s, c p = E) :
    (∑ p ∈ s, (A p + 1 - cc) ^ 2 * c p)
      = (∑ p ∈ s, (A p - S) ^ 2 * c p)
        + 2 * (S + 1 - cc) * (S - S * E) + (S + 1 - cc) ^ 2 * E := by
  have hexp : ∀ p : ι, (A p + 1 - cc) ^ 2 * c p
      = (A p - S) ^ 2 * c p + 2 * (S + 1 - cc) * ((A p - S) * c p)
        + (S + 1 - cc) ^ 2 * c p := by
    intro p; ring
  have hcross : (∑ p ∈ s, (A p - S) * c p) = S - S * E := by
    rw [Finset.sum_congr rfl (fun p _ => by ring : ∀ p ∈ s, (A p - S) * c p
      = A p * c p - S * c p), Finset.sum_sub_distrib, hS, ← Finset.mul_sum, hE]
  rw [Finset.sum_congr rfl (fun p _ => hexp p), Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hcross, hE]

/-- **`(FS-P)`, in the moment form the ledger consumes.**  With `S = boxFlatCount` (the first
moment, `flatPieceRT_moments_one`), `E = ∫Φ²` (the zeroth moment, `flatPieceRT_moments_zero`) and
`Var = Σ_p(|p.1|−S)²c_p`, the corrected `(FS-P)` reads

    `X_P ≤ Var + 2(S+1−c)(S − S·E) + (S+1−c)²·E` .

Both summands beyond the manifest `(S+1−c)²E` are exactly what the earlier statements dropped:
the `Var`-term is the Jensen defect supplied by the pair-condensate slack `pcb`, and the
`S(1−E)`-term vanishes in the normalised case `E = 1`. -/
theorem fsP_spectral_var {N : ℕ} {ℓ V : ℝ} (hℓ : 0 < ℓ) (hV : 0 < V)
    {A : Set E3} (hA : MeasurableSet A) (hVeq : V = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) {Φ : X N → ℝ} (hΦc : Continuous Φ) {c : ℝ} (hc : 0 ≤ c) :
    (∫ x in abox N ℓ, Φ x * Work.BoseFixB1.rungF V A
        (flatFunOp V A (fun r : ℝ => (Real.sqrt (r + 1) - Real.sqrt c) ^ 2) Φ) x)
      ≤ (∑ p ∈ Work.BoseFixB1.pairIdx N,
            ((p.1.card : ℝ) - (∑ q ∈ Work.BoseFixB1.pairIdx N, (q.1.card : ℝ)
              * ∫ x in abox N ℓ, (Work.BoseFixB1.flatPieceRT V A q.1 q.2 Φ x) ^ 2)) ^ 2
            * ∫ x in abox N ℓ, (Work.BoseFixB1.flatPieceRT V A p.1 p.2 Φ x) ^ 2)
        + 2 * ((∑ q ∈ Work.BoseFixB1.pairIdx N, (q.1.card : ℝ)
              * ∫ x in abox N ℓ, (Work.BoseFixB1.flatPieceRT V A q.1 q.2 Φ x) ^ 2) + 1 - c)
          * ((∑ q ∈ Work.BoseFixB1.pairIdx N, (q.1.card : ℝ)
              * ∫ x in abox N ℓ, (Work.BoseFixB1.flatPieceRT V A q.1 q.2 Φ x) ^ 2)
            - (∑ q ∈ Work.BoseFixB1.pairIdx N, (q.1.card : ℝ)
              * ∫ x in abox N ℓ, (Work.BoseFixB1.flatPieceRT V A q.1 q.2 Φ x) ^ 2)
              * (∑ q ∈ Work.BoseFixB1.pairIdx N,
                  ∫ x in abox N ℓ, (Work.BoseFixB1.flatPieceRT V A q.1 q.2 Φ x) ^ 2))
        + ((∑ q ∈ Work.BoseFixB1.pairIdx N, (q.1.card : ℝ)
              * ∫ x in abox N ℓ, (Work.BoseFixB1.flatPieceRT V A q.1 q.2 Φ x) ^ 2) + 1 - c) ^ 2
          * (∑ q ∈ Work.BoseFixB1.pairIdx N,
              ∫ x in abox N ℓ, (Work.BoseFixB1.flatPieceRT V A q.1 q.2 Φ x) ^ 2) := by
  refine le_trans (fsP_spectral hℓ hV hA hVeq hAc hΦc hc) ?_
  exact le_of_eq (sum_sq_moment_form (Work.BoseFixB1.pairIdx N)
    (fun p => (p.1.card : ℝ))
    (fun p => ∫ x in abox N ℓ, (Work.BoseFixB1.flatPieceRT V A p.1 p.2 Φ x) ^ 2)
    rfl rfl)

end Work.BoseFixB1S
