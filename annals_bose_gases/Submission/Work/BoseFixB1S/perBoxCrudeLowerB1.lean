import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseFixB1S.boxFlatSqJensen
import Submission.Work.BoseFixB1S.gapAbsorbB1
import Submission.Work.BoseFixB1S.locCountLeWeightedCount
import Submission.Work.BoseFixB1S.perBoxCrudeLower_goodSet_of_perBoxFLow
import Submission.Work.BoseFixB1S.sbWord_nonneg_of_normB_eq_zero
import Submission.Work.BoseFixR.box_collected_holds
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory

/-! ## 1. The FS-faithful box projections: the algebra used by the localised potsplit

`Work.UBBInputs8.boxPInd volA A i` is FS's `P_{B,i}` (the rank-one projection onto the
`A`-constants, carrying the indicator `1_A`) and `boxQInd volA A i = 1_A(xᵢ)· − boxPInd` its
complement.  The two facts below are what `PotWords.potsplit_pair_pointwise` uses; they hold
*definitionally* (the second from three instances of the first). -/

/-- `P + Q = 1_A(xᵢ)·` — the defining decomposition of the FS-faithful box projections. -/
theorem boxProjOps_add {volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))} {N : ℕ} (i : Fin N)
    (Φ : Submission.BoseGases.X N → ℝ) (x : Submission.BoseGases.X N) :
    Work.UBBInputs8.boxPInd volA A i Φ x + Work.UBBInputs8.boxQInd volA A i Φ x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * Φ x := by
  rw [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
  ring

/-- **The two-slot pattern identity** on the box: the four products of the projections in the
slots `i ≠ j` sum to the product of the indicators times the state.  (Pure algebra from
`boxProjOps_add`, applied at `Φ`, at `P_jΦ` and at `Q_jΦ`.) -/
theorem boxProjOps_pattern {volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))} {N : ℕ}
    (i j : Fin N) (hij : i ≠ j) (Φ : Submission.BoseGases.X N → ℝ)
    (x : Submission.BoseGases.X N) :
    Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      + Work.UBBInputs8.boxPInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
      + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxPInd volA A j Φ) x
      + Work.UBBInputs8.boxQInd volA A i (Work.UBBInputs8.boxQInd volA A j Φ) x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j) * Φ x := by
  have h2 := boxProjOps_add (volA := volA) (A := A) j Φ x
  have h3 := boxProjOps_add (volA := volA) (A := A) i
    (Work.UBBInputs8.boxPInd volA A j Φ) x
  have h4 := boxProjOps_add (volA := volA) (A := A) i
    (Work.UBBInputs8.boxQInd volA A j Φ) x
  have e1 : A.indicator (fun _ => (1 : ℝ)) (x i) * Work.UBBInputs8.boxPInd volA A j Φ x
      + A.indicator (fun _ => (1 : ℝ)) (x i) * Work.UBBInputs8.boxQInd volA A j Φ x
      = A.indicator (fun _ => (1 : ℝ)) (x i) * A.indicator (fun _ => (1 : ℝ)) (x j) * Φ x := by
    rw [← mul_add, h2]
    ring
  linarith [h3, h4, e1]

end Work.BoseFixB1S

namespace Work.BoseFixB1S

open MeasureTheory

noncomputable section

/-! ## 2. The pieces of the assembly, and the assembly itself

The assembly below reduces the target to **three** named inputs, each a statement about the
*localised* word at FS's parameters (`ℓ = sideAt μ (a v)`, `M`, `d` from `paramsAt`):

* `PayB1 h ξ` — the **payment** FS `l.4083` needs (the crude reading of the corpus's
  "kernel/word comparison at the count"; `BoseFixB1S/PerBoxPayB1` is its `ξ = 1` instance,
  and the two mechanisms of `FINDING_perBoxCrudeB1.md` §3 deliver it for *every* fixed `ξ`,
  since their constants are free): the chemical-potential count `μ(a v)·Σ_i∫Φ²χ_{B(u)}(x_i)`
  is dominated by half the localised pair term plus the localised spectral kinetic, up to the
  gap-count and the allowance.
* `WordBoundB1 h ξ` — the **potential-word bound** `qLHSwordB ≥ −ξμ(a v)·count + ½·pair`,
  which is what the *proved* linear fibre bound `Work.BoseFixB1B.fibre_chiB_le` (with
  constant `ξ·(a v)`) gives once the configuration integral is split.
* `GapAbsB1` — the **gap absorption**: `tbGapCoeff (dℓ) ε_T ≥ K μ(a v)` for every fixed `K`,
  by taking the diluteness threshold small (the ratio is `t^{−13/1292}/(2(1+π⁻²)) → ∞`).

Taking `ξ` to be the fibre constant makes the pair and kinetic terms cancel **exactly** in the
assembly, leaving the allowance. -/

/-- The localised count `Σ_i ∫ Φ² χ_{B(u)}(x_i)`. -/
def locCount (M : ℕ) (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
    (Φ x) ^ 2 * Submission.BoseGases.chiSmallB M ℓ d u (x i)

/-- The localised pair term `Σ_{p ∈ pairSet n} ∫ Φ² w_{B(u)}(x_{p.1},x_{p.2})`. -/
def locPair (v : EuclideanSpace ℝ (Fin 3) → ℝ) (M : ℕ) (ℓ d : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  ∑ p ∈ Submission.BoseGases.pairSet n, ∫ x in Submission.BoseGases.abox n ℓ,
    (Φ x) ^ 2 * Submission.BoseGases.wSmallPair M ℓ d u v (x p.1) (x p.2)

/-- The localised spectral kinetic word of `sbKin`. -/
def kinLoc (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) (M : ℕ)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  Work.UBBInputs8.tBwordKinInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (Submission.BoseGases.chiB (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) Φ

/-- The localised excited count `n₊(B(u))`. -/
def nPlusLoc (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) : ℝ :=
  Work.UBBInputs8.cnPlusBoxInd (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) Φ

/-- The gap coefficient `tbGapCoeff (dℓ) ε_T` at FS's parameters. -/
def gapCoeffAt (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ) : ℝ :=
  Work.SmallBoxTBWord.tbGapCoeff
    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT

/-- The target's allowance shape at FS's parameters. -/
def allowance (v : EuclideanSpace ℝ (Fin 3) → ℝ) (μ : ℝ)
    (u : EuclideanSpace ℝ (Fin 3)) : ℝ :=
  μ ^ 2 * (_root_.BoseGases.a v)
      * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
    + μ * (_root_.BoseGases.a v)

/-- **The payment** (PAY) at the fixed coefficient `ξ`.  (The requester's `PerBoxPayB1` is the
`ξ = 1` instance; the mechanisms of `FINDING_perBoxCrudeB1.md` §3 give it for every fixed `ξ`,
their constants being free.) -/
def PayB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (ξ : ℝ) : Prop :=
  ∃ ε₀ K C : ℝ, 0 < ε₀ ∧ 0 ≤ K ∧ 0 ≤ C ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        ξ * (μ * (_root_.BoseGases.a v))
            * locCount (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)
          ≤ (1 / 2) * locPair v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)
            + kinLoc v μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
                (Φ : Submission.BoseGases.X n → ℝ)
            + K * (μ * (_root_.BoseGases.a v))
                * nPlusLoc v μ u (Φ : Submission.BoseGases.X n → ℝ)
            + C * allowance v μ u * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)

/-- **The potential-word bound** at the fixed coefficient `ξ`: the localised potential word
dominates `−ξμ(a v)·count + ½·pair`.  This is the configuration-integral split of
`Work.SmallBoxSliding.qLHSwordB`, with the chemical-potential line bounded by the *proved*
linear fibre bound `Work.BoseFixB1B.fibre_chiB_le` (with constant `ξ·(a v)`). -/
def WordBoundB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (ξ : ℝ) : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        -(ξ * (μ * (_root_.BoseGases.a v)))
              * locCount (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                  (Φ : Submission.BoseGases.X n → ℝ)
          + (1 / 2) * locPair v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)
        ≤ Work.SmallBoxSliding.qLHSwordB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ u (Φ : Submission.BoseGases.X n → ℝ)

/-- **The gap absorption**: for every fixed `K ≥ 0`, the definitional gap coefficient beats
`K μ(a v)` once the diluteness threshold is small (`tbGapCoeff (dℓ) ε_T / (μ(a v)) =
t^{−13/1292}/(2(1+π⁻²)) → ∞`). -/
def GapAbsB1 (v : EuclideanSpace ℝ (Fin 3) → ℝ) : Prop :=
  ∀ K : ℝ, 0 ≤ K → ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        K * (μ * (_root_.BoseGases.a v)) * nPlusLoc v μ u (Φ : Submission.BoseGases.X n → ℝ)
          ≤ gapCoeffAt v μ * nPlusLoc v μ u (Φ : Submission.BoseGases.X n → ℝ)

/-- `GapAbsB1` is proved: it is the delegated `Work.BoseFixB1S.gapAbsorbB1`
(`Submission/Work/BoseFixB1S/gapAbsorbB1.lean`), whose statement is this one with the two
localised abbreviations unfolded. -/
theorem gapAbsB1_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hav : 0 < _root_.BoseGases.a v) :
    GapAbsB1 v := by
  intro K hK
  obtain ⟨ε₀, hε₀, h⟩ := Work.BoseFixB1S.gapAbsorbB1 (v := v) hav K hK
  exact ⟨ε₀, hε₀, fun μ hAdm n Φ u => by simpa only [nPlusLoc, gapCoeffAt] using h μ hAdm n Φ u⟩

/-- **The assembly.**  The payment (at the fibre constant `ξ`), the potential-word bound and
the gap absorption give the crude per-`u` bound, with the allowance constant of the payment:
`sbWord = gap·n₊ + kin + qLHSwordB`, the word bound and the payment cancel `½·pair` and `kin`
*exactly*, and the gap absorption kills the `K μ(a v)n₊` term. -/
theorem perBoxCrudeLower_of_pieces {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {ξ : ℝ} (hξ : 0 ≤ ξ) (hpay : PayB1 h ξ) (hword : WordBoundB1 h ξ) (hgap : GapAbsB1 v) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          -(C * allowance v μ u) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  obtain ⟨εp, K, C, hεp, hK, hC, hpay'⟩ := hpay
  obtain ⟨εw, hεw, hword'⟩ := hword
  obtain ⟨εg, hεg, hgap'⟩ := hgap K hK
  refine ⟨min εp (min εw εg), C, lt_min hεp (lt_min hεw hεg), hC, ?_⟩
  intro μ hAdm n Φ u
  have hAdmP : Work.BoseBoxFix.Adm v εp μ :=
    Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmW : Work.BoseBoxFix.Adm v εw μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hAdmG : Work.BoseBoxFix.Adm v εg μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_right _ _))
  have hp := hpay' μ hAdmP n Φ u
  have hw := hword' μ hAdmW n Φ u
  have hg := hgap' μ hAdmG n Φ u
  have hsplit : Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)
      = gapCoeffAt v μ * nPlusLoc v μ u (Φ : Submission.BoseGases.X n → ℝ)
        + kinLoc v μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
            (Φ : Submission.BoseGases.X n → ℝ)
        + Work.SmallBoxSliding.qLHSwordB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ u
            (Φ : Submission.BoseGases.X n → ℝ) := rfl
  have hneg : -(C * allowance v μ u) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      = -(C * allowance v μ u * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) := by
    ring
  rw [hneg, hsplit]
  linarith [hp, hw, hg]

/-- **The assembly, with the gap input discharged**: the payment and the potential-word bound
alone give the target's conclusion (the gap absorption is the delegated, proved
`gapAbsorbB1`). -/
theorem perBoxCrudeLower_of_pay_word {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {ξ : ℝ} (hav : 0 < _root_.BoseGases.a v) (hξ : 0 ≤ ξ) (hpay : PayB1 h ξ)
    (hword : WordBoundB1 h ξ) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
          (u : EuclideanSpace ℝ (Fin 3)),
          -(C * allowance v μ u) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
            ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) :=
  perBoxCrudeLower_of_pieces hξ hpay hword (gapAbsB1_holds hav)

/-! ## 2b. The `IsLowB`-aware residual: the *local count bound*

`PayB1` of §2 cannot be the last word, because it is an **unconditional** per-box statement and
it is *false as stated*: at the `u` at which the two windows of the word disagree — `chiB` (the
window of `sbKin`) is **ball**-based and dies on the sliding cube there, while `chiSmallB` (the
window of `sbPot`) is **cube**-based and is alive — the spectral column of `sbKin` vanishes
identically while the "hole" state `Φ_δ = 1_{B(u)}·∏_{i<j}(1−η_δ(x_i−x_j))` kills the pair term
exactly and keeps the `χ_{B(u)}`-count `≍ n`.  Hence `sbWord ≈ −8πμ(a v)·n·‖Φ‖²` there, which
beats the allowance `C(μ²(a v)·chiMass + μ(a v))‖Φ‖²` for every fixed `C` (this is the verdict of
`FINDING_perBoxCrudeB1.md`; the same witness refutes `BoseFixB1S/PerBoxPayB1`).

**The target is *not* refuted by that witness.**  `IsLowB` is a statement about the **big** box
`Λ = acube ℓ`, and the witness is concentrated in a sub-box of `Λ`: its *big-box* excited count
`cnPlus(Λ) = Σᵢ∫(Q^{(Λ)}_iΦ)²` is `≍ n‖Φ‖²`, so its big-box word is

    wordB ≥ tbGapCoeff (dℓ)ε_T·cnPlus(Λ) − 8πμ(a v)n‖Φ‖² ≈ (μ a t^{−13/1292} − 8πμ a)n‖Φ‖² > 0 ,

far *above* the (negative) level `ℓ³·Theta (a v) J μ·‖Φ‖²` of `IsLowB`.  So such a state is not
low, and the target's hypotheses are exactly what rules the witness out.

What survives — and what the target actually needs — is therefore the following IsLowB-aware
statement: **a low state has bounded local `χ_{B(u)}`-mass** (FS `eq:apriorinn+` read at the
sliding box).  Its two mechanisms:

* every particle that is *localised* in a sub-region of `Λ` costs the big-box gap
  `≍ μ a t^{−13/1292}` (it is `Λ`-excited, so it enters `cnPlus(Λ)` with weight `≍ 1`), while the
  `IsLowB` budget at `J ≥ lhyC` is `4πμ²aℓ³J(μa³)^{1/2}`; since `μℓ³ ≍ t^{−0.514}` and
  `t^{13/1292}` is a *constant* far larger than `1` in FS's regime, this gives
  `cnPlus(Λ) ≤ C(1 + n·t^{13/1292})`;
* the pair term of the *coherent* part gives the mean-field window `n ≤ Cμℓ³` (FS's first window,
  here only up to the free constant `C`, which is all the crude bound needs);
* consequently `locCount ≤ C·(cnPlus(Λ) + n·|B(u)|/|Λ|) ≤ C(μ·chiMass + 1)·‖Φ‖²`.

The statement below is the residual *in the exact form the assembly consumes*.  **Caveat on the
two slots** (see `FINDING_perBoxCrudeLowerB1_status.md` §9.7): the *honest* local count bound is
`locCount ≤ C(μ·∫χ_{B(u)} + 1)‖Φ‖²`; the form below *replaces* `∫χ_{B(u)}` (the `L¹`-mass) by
`chiMass = ∫χ_{B(u)}²` (the `L²`-mass), because that is the quantity the target's allowance
carries.  This is the *stronger* requirement `n ≤ Cμℓ³·(∫χ²/∫χ)`, which on the interior is the
honest window `n ≤ Cμℓ³` (there `χ_{B(u)}` is a normalised bump, `∫χ²/∫χ ≍ 1`) and in the band is
weaker than the (astronomically slack) window the band reduction needs.  The compatible
Cauchy–Schwarz split of `locCount` is `BoseFixB1S/locCount_le_coherentSplitV2` (delegated) and
the excited-mass estimate is `BoseFixB1S/excitedMass_le_cnPlusBoxInd` (delegated). -/
def LowBoxCount {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) : Prop :=
  ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
    ∀ J : ℝ, Work.UBB.lhyC ≤ J → ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
        (u : EuclideanSpace ℝ (Fin 3)),
        Work.BoseBoxFix.IsLowB v h J μ n Φ →
        locCount (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ)
          ≤ C * (μ * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u + 1)
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)

/-- The localised pair kernel is nonnegative for `v ≥ 0` (the two cut-offs, the numerator and
the two convolution denominators are all `≥ 0`; `x / 0 = 0` covers the vanishing denominators). -/
theorem sbPairKernel_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v) (M : ℕ) (ℓ d : ℝ)
    (u x y : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Submission.BoseGases.wSmallPair M ℓ d u v x y := by
  rw [Submission.BoseGases.wSmallPair, Submission.BoseGases.wSmallScaled,
    Submission.BoseGases.convScaleSmall]
  refine mul_nonneg (mul_nonneg (Submission.BoseGases.chiSmallB_nonneg M ℓ d u x) ?_)
    (Submission.BoseGases.chiSmallB_nonneg M ℓ d u y)
  refine div_nonneg (div_nonneg (hv _) ?_) (Submission.BoseGases.convScale_nonneg ℓ _)
  rw [Submission.BoseGases.conv3Small]
  exact integral_nonneg fun w =>
    mul_nonneg (Submission.BoseGases.chiSmall_nonneg M w)
      (Submission.BoseGases.chiSmall_nonneg M (_ - w))

/-- The localised pair term is nonnegative. -/
theorem locPair_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} (hv : 0 ≤ v) {M : ℕ} {ℓ d : ℝ}
    {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ) :
    0 ≤ locPair v M ℓ d u Φ := by
  rw [locPair]
  refine Finset.sum_nonneg fun p _ => integral_nonneg fun x => ?_
  exact mul_nonneg (sq_nonneg _) (sbPairKernel_nonneg hv M ℓ d u (x p.1) (x p.2))

/-- The localised kinetic word is nonnegative: `sbKin = tBwordBInd` at FS's parameters. -/
theorem sbKin_nonneg {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {M : ℕ}
    {u : EuclideanSpace ℝ (Fin 3)} {n : ℕ} (Φ : Submission.BoseGases.X n → ℝ)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hε : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT) :
    0 ≤ Work.BoseFixB1.sbKin (v := v) μ M u Φ := by
  rw [Work.BoseFixB1.sbKin]
  exact Work.UBBInputs9.A.tBwordBInd_nonneg hℓ hε u Φ

/-- The box norm is nonnegative. -/
theorem normB_nonneg' {v : EuclideanSpace ℝ (Fin 3) → ℝ} (μ : ℝ) (n : ℕ)
    (Φ : Submission.BoseGases.X n → ℝ) :
    0 ≤ Work.BoseBoxFix.normB v μ n Φ := by
  rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
  exact integral_nonneg fun x => sq_nonneg _

/-- **The arithmetic core of the IsLowB-aware assembly.**  Dropping the two nonnegative slots
(the kinetic `kin` and the pair term `lp`), the word bound and the local count bound give the
target's inequality, with the allowance constant `ξ·C₀`. -/
theorem lowCount_arith {sw kin qw loc lp nB V μ a ξ C₀ : ℝ}
    (hξ : 0 ≤ ξ) (ha : 0 ≤ a) (hμ : 0 ≤ μ) (hV : 0 ≤ V) (hnB : 0 ≤ nB)
    (hk : 0 ≤ kin) (hlp : 0 ≤ lp)
    (hw : -(ξ * (μ * a)) * loc + (1 / 2) * lp ≤ qw)
    (hlc : loc ≤ C₀ * (μ * V + 1) * nB)
    (hsw : sw = kin + qw) :
    -(ξ * C₀ * (μ ^ 2 * a * V + μ * a)) * nB ≤ sw := by
  have hξμa : 0 ≤ ξ * (μ * a) := mul_nonneg hξ (mul_nonneg hμ ha)
  have h1 : -(ξ * (μ * a)) * loc ≤ qw := by linarith
  have h2 : -(ξ * (μ * a)) * (C₀ * (μ * V + 1) * nB) ≤ -(ξ * (μ * a)) * loc := by
    have hm := mul_le_mul_of_nonneg_left hlc hξμa
    linarith
  have h3 : -(ξ * C₀ * (μ ^ 2 * a * V + μ * a)) * nB
      = -(ξ * (μ * a)) * (C₀ * (μ * V + 1) * nB) := by ring
  rw [h3]
  linarith [h1, h2, hk, hsw]

/-- **The assembly of the target from the local count bound.**  The potential-word bound (§2,
delivered by the proved `fibreWordB1Fix`) and the local count bound alone give the target's
conclusion: the word splits as `sbWord = sbKin + qLHSwordB` and both the kinetic (`sbKin ≥ 0`)
and the pair term (`locPair ≥ 0`) may be dropped, so

    sbWord ≥ −ξμ(a v)·locCount ≥ −ξC₀(μ²(a v)·chiMass + μ(a v))·‖Φ‖² .

(The gap absorption and the payment are *not* needed on this route.) -/
theorem perBoxCrudeLower_of_lowCount {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {J : ℝ} (hJ : Work.UBB.lhyC ≤ J) (hv : 0 ≤ v) (hav : 0 < _root_.BoseGases.a v)
    {ξ : ℝ} (hξ : 0 ≤ ξ)
    (hlow : LowBoxCount h) (hword : WordBoundB1 h ξ) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
          ∀ u : EuclideanSpace ℝ (Fin 3),
            -(C * (μ ^ 2 * (_root_.BoseGases.a v)
                  * Work.SmallBoxSliding.chiMass
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                  + μ * (_root_.BoseGases.a v)))
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by
  obtain ⟨εl, C₀, hεl, hC₀, hlow'⟩ := hlow
  obtain ⟨εw, hεw, hword'⟩ := hword
  refine ⟨min εl εw, ξ * C₀, lt_min hεl hεw, mul_nonneg hξ hC₀, ?_⟩
  intro μ hAdm hJK n Φ hlowΦ u
  have hAdml : Work.BoseBoxFix.Adm v εl μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hAdmw : Work.BoseBoxFix.Adm v εw μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hμ : 0 ≤ μ := le_of_lt hAdm.1
  have hV : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hlp : 0 ≤ locPair v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ) :=
    locPair_nonneg hv Φ
  have hk : 0 ≤ Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      u (Φ : Submission.BoseGases.X n → ℝ) :=
    sbKin_nonneg (v := v) Φ (Work.BoseFixB1.adm_ell_pos hAdm)
      (Work.BoseFixB1.adm_eT_bounds hAdm).1
  have hnb : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
    normB_nonneg' μ n (Φ : Submission.BoseGases.X n → ℝ)
  have hsw : Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)
      = Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
          (Φ : Submission.BoseGases.X n → ℝ)
        + Work.SmallBoxSliding.qLHSwordB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ u
            (Φ : Submission.BoseGases.X n → ℝ) := rfl
  exact lowCount_arith (sw := Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ))
    (kin := Work.BoseFixB1.sbKin (v := v) μ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M u
      (Φ : Submission.BoseGases.X n → ℝ))
    (qw := Work.SmallBoxSliding.qLHSwordB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ u (Φ : Submission.BoseGases.X n → ℝ))
    (loc := locCount (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ))
    (lp := locPair v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u (Φ : Submission.BoseGases.X n → ℝ))
    (nB := Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
    (V := Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (a := _root_.BoseGases.a v) (ξ := ξ) (C₀ := C₀)
    hξ (le_of_lt hav) hμ hV hnb hk hlp (hword' μ hAdmw n Φ u)
    (hlow' J hJ μ hAdml hJK n Φ u hlowΦ) hsw

/-! ## 3. The box-word rungs of the payment (PAY)

The pieces below are the first rungs of the *potential-side* chain (FS
`lm:appinteractionestimate`) at the **box** projections of `BoseFixB1S/BoxQWords`:
`P_{B,i} + Q_{B,i} = 1_A(xᵢ)·`, the five-word decomposition `boxQSum`, the
mean-field floor of `boxQ0` and the manifest square `boxQ4`.  They are the
ingredients the assembly of `PayB1` consumes (see
`FINDING_perBoxCrudeLowerB1_status.md` §6). -/

/-- `boxQCount` is definitionally the corpus's `cnPlusBoxInd`, i.e. FS's excited
count `n₊(B)` at the localised box. -/
theorem boxQCount_eq_cnPlusBoxInd {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (Φ : Submission.BoseGases.X N → ℝ) :
    boxQCount volA ℓ A Φ = Work.UBBInputs8.cnPlusBoxInd ℓ A volA Φ := rfl

/-- **Completion of squares, homogeneous form.**  If `F² − F·I ≤ I·T` (the sharp mean-field
Jensen with the mass `I`), `I ≥ 0`, `T ≥ 0` and `a > 0`, then `a·T − b·F ≥ −I(a+b)²/(4a)`.
This is the pure-real step that turns the mean-field square into a payable floor. -/
theorem quadFloorHom (a b F T I : ℝ) (ha : 0 < a) (hT : 0 ≤ T) (hI : 0 ≤ I)
    (hJ : F ^ 2 - F * I ≤ I * T) :
    -(I * ((a + b) ^ 2 / (4 * a))) ≤ a * T - b * F := by
  rcases eq_or_lt_of_le hI with h0 | hpos
  · have hle : F ^ 2 ≤ 0 := by
      rw [← h0] at hJ
      linarith
    have hF : F = 0 := by nlinarith [sq_nonneg F]
    rw [← h0, hF]
    simpa using mul_nonneg ha.le hT
  · have h1 : F ^ 2 ≤ I * T + F * I := by linarith
    have h2 : a ^ 2 * F ^ 2 ≤ a ^ 2 * (I * T + F * I) :=
      mul_le_mul_of_nonneg_left h1 (sq_nonneg a)
    have h3 : 0 ≤ (2 * a * F - I * (a + b)) ^ 2 := sq_nonneg _
    have hkey : 0 ≤ I * (4 * a ^ 2 * T - 4 * a * F * b + I * (a + b) ^ 2) := by
      nlinarith [h2, h3]
    have hkey' : 0 ≤ 4 * a ^ 2 * T - 4 * a * F * b + I * (a + b) ^ 2 :=
      nonneg_of_mul_nonneg_right hkey hpos
    have h4a : 0 < 4 * a := by linarith
    have hmain : -(I * (a + b) ^ 2) ≤ 4 * a * (a * T - b * F) := by nlinarith [hkey']
    have heq : -(I * ((a + b) ^ 2 / (4 * a))) = (-(I * (a + b) ^ 2)) / (4 * a) := by
      field_simp
    rw [heq, div_le_iff₀ h4a]
    linarith [hmain]

/-- **The unnormalised `boxQ0` identity**: `boxQ0` is the mean-field combination of the flat and
pair counts.  (`boxQ0Square` states the same identity for `∫Φ² = 1`; the homogeneity is what
removes that hypothesis, so that the identity can be applied to an arbitrary state.) -/
theorem boxQ0_identity {N : ℕ} {ℓ μ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {w1 w2 : (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ}
    (hw2 : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      w2 p.1 p.2) (MeasureTheory.volume.restrict (A ×ˢ A)))
    (hw1 : MeasureTheory.IntegrableOn (Submission.BoseGases.w1Fibre ℓ w1) A)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    boxQ0 volA ℓ μ A w1 w2 Φ
      = (1 / 2) * (boxM2 volA A w2 / volA ^ 2) * boxPairCount volA ℓ A Φ
        - μ * (boxM1 ℓ A w1 / volA) * boxFlatCount volA ℓ A Φ := by
  have hpair : ∀ p ∈ Submission.BoseGases.pairSet N,
      (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2
            * w2 (x p.1) (x p.2))
        = (boxM2 volA A w2 / volA ^ 2) *
          (∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2) :=
    fun p hp => Q0C.pair_value hℓ hvol hA hvolA hAc (Finset.mem_filter.mp hp).2 hw2 hΦc
  have hone : ∀ i : Fin N,
      (∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i))
        = (boxM1 ℓ A w1 / volA) *
          (∫ x in Submission.BoseGases.abox N ℓ, (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) :=
    fun i => Q0C.one_value hℓ hvol hA hvolA hAc i hw1 hΦc
  have hsum1 :
      (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2
            * w2 (x p.1) (x p.2))
        = (boxM2 volA A w2 / volA ^ 2) *
          (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun p hp => hpair p hp)
  have hsum2 :
      (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
          (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2 * Submission.BoseGases.w1Fibre ℓ w1 (x i))
        = (boxM1 ℓ A w1 / volA) *
          (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
            (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => hone i)
  simp only [boxQ0, boxPairCount, boxFlatCount]
  rw [hsum1, hsum2]
  ring

/-- **The payable floor of `boxQ0`** (homogeneous form): the condensate count `boxFlatCount` is
paid by the *completion of the mean-field square*, giving

    `−(∫Φ²)·(μ²M₁²/(2M₂) + μM₁/(2V) + M₂/(8V²)) ≤ boxQ0`,

where `M₁ = boxM1 ℓ A w1`, `M₂ = boxM2 volA A w2`, `V = volA`.  The mass bounds
(`M₂ ≥ M₁`, `M₁ ≤ Ca·chiMass`, `M₂ ≤ Ca·chiMass`, `μV ≥ 1`) then turn the bracket into the
allowance shape `C(μ²a·chiMass + μa)`.  Unlike `boxQ0Square` this needs **no** normalisation
hypothesis on `Φ`. -/
theorem boxQ0FloorPayable {N : ℕ} {ℓ μ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ) (hμ : 0 ≤ μ)
    {w1 w2 : (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ}
    (hw2 : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      w2 p.1 p.2) (MeasureTheory.volume.restrict (A ×ˢ A)))
    (hw1 : MeasureTheory.IntegrableOn (Submission.BoseGases.w1Fibre ℓ w1) A)
    (hM2 : 0 < boxM2 volA A w2)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    -((∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2)
        * (μ ^ 2 * (boxM1 ℓ A w1) ^ 2 / (2 * boxM2 volA A w2)
          + μ * (boxM1 ℓ A w1) / (2 * volA)
          + boxM2 volA A w2 / (8 * volA ^ 2)))
      ≤ boxQ0 volA ℓ μ A w1 w2 Φ := by
  have hid := boxQ0_identity (ℓ := ℓ) (μ := μ) (volA := volA) hℓ hvol hA hvolA hAc hw2 hw1 hΦc
  have hjensen := boxFlatSqJensen (N := N) hℓ hvol hA hvolA hAc (Φ := Φ) hΦc
  have hI0 : 0 ≤ ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2 :=
    integral_nonneg fun x => sq_nonneg _
  have hT0 : 0 ≤ boxPairCount volA ℓ A Φ := by
    rw [boxPairCount]
    exact Finset.sum_nonneg fun p _ => integral_nonneg fun x => sq_nonneg _
  have hapos : 0 < (1 / 2) * (boxM2 volA A w2 / volA ^ 2) := by
    have : 0 < boxM2 volA A w2 / volA ^ 2 := div_pos hM2 (by positivity)
    linarith
  have hstep := quadFloorHom ((1 / 2) * (boxM2 volA A w2 / volA ^ 2))
    (μ * (boxM1 ℓ A w1 / volA)) (boxFlatCount volA ℓ A Φ) (boxPairCount volA ℓ A Φ)
    (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) hapos hT0 hI0 hjensen
  have hfloor : -(((1 / 2) * (boxM2 volA A w2 / volA ^ 2) + μ * (boxM1 ℓ A w1 / volA)) ^ 2
        / (4 * ((1 / 2) * (boxM2 volA A w2 / volA ^ 2))))
      = -(μ ^ 2 * (boxM1 ℓ A w1) ^ 2 / (2 * boxM2 volA A w2)
          + μ * (boxM1 ℓ A w1) / (2 * volA) + boxM2 volA A w2 / (8 * volA ^ 2)) := by
    have hV : volA ≠ 0 := ne_of_gt hvol
    have hM : boxM2 volA A w2 ≠ 0 := ne_of_gt hM2
    field_simp
    ring
  have hfloor2 : (μ ^ 2 * (boxM1 ℓ A w1) ^ 2 / (2 * boxM2 volA A w2)
        + μ * (boxM1 ℓ A w1) / (2 * volA) + boxM2 volA A w2 / (8 * volA ^ 2))
      = ((1 / 2) * (boxM2 volA A w2 / volA ^ 2) + μ * (boxM1 ℓ A w1 / volA)) ^ 2
          / (4 * ((1 / 2) * (boxM2 volA A w2 / volA ^ 2))) := by linarith [hfloor]
  rw [hid, hfloor2]
  exact hstep

/-- **`boxQ4` is a manifest square**: for a pointwise nonnegative two-body kernel `w` the four-`Q`
bracket contributes nonnegatively. -/
theorem boxQ4_nonneg {N : ℕ} {ℓ volA : ℝ} {A : Set (EuclideanSpace ℝ (Fin 3))}
    {w om : (EuclideanSpace ℝ (Fin 3)) → (EuclideanSpace ℝ (Fin 3)) → ℝ}
    (hw : ∀ x y : EuclideanSpace ℝ (Fin 3), 0 ≤ w x y)
    (Φ : Submission.BoseGases.X N → ℝ) : 0 ≤ boxQ4 volA ℓ A w om Φ := by
  rw [boxQ4]
  refine mul_nonneg (by norm_num) (Finset.sum_nonneg fun p _ => ?_)
  exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (hw _ _)

/-- **The cutoff is dominated by its box indicator**: `chiSmallB M ℓ d u` is supported in
`dlBox ℓ d u` and bounded by the constant `chiSupAbs·chiSmallDecay M·2^{−M}`.  This is the
hypothesis `hχ` of the count split (`BoseFixB1S/locCountLeWeightedCount`). -/
theorem chiSmallB_le_dlBox (M : ℕ) (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (u x : EuclideanSpace ℝ (Fin 3)) :
    Submission.BoseGases.chiSmallB M ℓ d u x
      ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M * (1 / 2) ^ M)
        * (Submission.BoseGases.dlBox ℓ d u).indicator (fun _ => (1 : ℝ)) x := by
  rcases em (x ∈ Submission.BoseGases.dlBox ℓ d u) with hx | hx
  · rw [Set.indicator_of_mem hx, mul_one]
    have hd0 : 0 < ℓ * d := mul_pos hℓ hd
    have hdec := Submission.BoseGases.chiSmallB_slab_decay (M := M) hM hℓ hd u x ⟨0, by norm_num⟩
    have hmax : (max (ℓ * d / 2 - |(x - (ℓ * d) • u).ofLp (0 : Fin 3)|) 0 / (ℓ * d)) ^ M
        ≤ ((1 : ℝ) / 2) ^ M := by
      have hab : 0 ≤ |(x - (ℓ * d) • u).ofLp (0 : Fin 3)| := abs_nonneg _
      have hle : max (ℓ * d / 2 - |(x - (ℓ * d) • u).ofLp (0 : Fin 3)|) 0 ≤ ℓ * d / 2 := by
        refine max_le ?_ ?_
        · linarith
        · positivity
      have h2 : max (ℓ * d / 2 - |(x - (ℓ * d) • u).ofLp (0 : Fin 3)|) 0 / (ℓ * d) ≤ 1 / 2 := by
        rw [div_le_iff₀ hd0]
        linarith
      have h3 : 0 ≤ max (ℓ * d / 2 - |(x - (ℓ * d) • u).ofLp (0 : Fin 3)|) 0 / (ℓ * d) :=
        div_nonneg (le_max_right _ _) hd0.le
      exact pow_le_pow_left₀ h3 h2 M
    have h4 : 0 ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M :=
      mul_nonneg Submission.BoseGases.chiSupAbs_nonneg (Submission.BoseGases.chiSmallDecay_nonneg M)
    calc Submission.BoseGases.chiSmallB M ℓ d u x
        ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M *
            (max (ℓ * d / 2 - |(x - (ℓ * d) • u).ofLp (0 : Fin 3)|) 0 / (ℓ * d)) ^ M :=
          le_trans (le_abs_self _) (by simpa using hdec)
      _ ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
            * ((1 : ℝ) / 2) ^ M :=
          mul_le_mul_of_nonneg_left hmax h4
  · rw [Set.indicator_of_notMem hx, mul_zero]
    have hne : Submission.BoseGases.chiSmallB M ℓ d u x = 0 := by
      by_contra hne
      exact hx (Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hne)
    rw [hne]

/-- **The allowance arithmetic.**  The mean-field floor's bracket is dominated by the allowance
shape `K²(μ²a·chiMass + μa)` once the mass bounds (`M₁ ≤ Ka·chiMass`, `M₁ ≤ M₂`,
`M₂ ≤ Ka·chiMass`) and the regime relations `1 ≤ μV`, `chiMass ≤ KV` hold.  This is the step
that turns `boxQ0FloorPayable` into a bound of the shape the target's right-hand side uses. -/
theorem floor_le_allowance {μ a M1 M2 V chiMass I K : ℝ}
    (hK : 1 ≤ K) (ha : 0 ≤ a) (hμ : 0 ≤ μ) (hV : 0 < V) (hchi : 0 ≤ chiMass)
    (hI : 0 ≤ I) (hM1 : 0 ≤ M1) (hM2pos : 0 < M2)
    (hM1le : M1 ≤ K * a * chiMass) (hM1M2 : M1 ≤ M2) (hM2le : M2 ≤ K * a * chiMass)
    (hμV : 1 ≤ μ * V) (hchiV : chiMass ≤ K * V) :
    I * (μ ^ 2 * M1 ^ 2 / (2 * M2) + μ * M1 / (2 * V) + M2 / (8 * V ^ 2))
      ≤ K ^ 2 * (μ ^ 2 * a * chiMass + μ * a) * I := by
  have hinv : 1 / V ≤ μ := by
    rw [div_le_iff₀ hV]
    linarith [hμV]
  have hKa : 0 ≤ K * a := mul_nonneg (le_trans zero_le_one hK) ha
  have hA0 : 0 ≤ K * a * chiMass := mul_nonneg hKa hchi
  have t1 : μ ^ 2 * M1 ^ 2 / (2 * M2) ≤ μ ^ 2 * (K * a * chiMass) / 2 := by
    have hsq : M1 ^ 2 ≤ (K * a * chiMass) * M2 := by nlinarith [hM1, hM1M2, hM1le, hM2pos.le]
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * M2) (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hsq, hμ]
  have t2 : μ * M1 / (2 * V) ≤ μ ^ 2 * (K * a * chiMass) / 2 := by
    have hle : μ * M1 / (2 * V) ≤ μ * (K * a * chiMass) / (2 * V) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hM1le hμ) (by positivity : (0 : ℝ) ≤ 2 * V)
    refine le_trans hle ?_
    have hmuKa : 0 ≤ μ * (K * a * chiMass) := mul_nonneg hμ hA0
    have key : (2 : ℝ) ≤ μ * (2 * V) := by linarith [hμV]
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * V) (by norm_num : (0 : ℝ) < 2)]
    nlinarith [hmuKa, key]
  have t3 : M2 / (8 * V ^ 2) ≤ K ^ 2 * (μ * a) := by
    have h1 : M2 / (8 * V ^ 2) ≤ (K * a * chiMass) / (8 * V ^ 2) :=
      div_le_div_of_nonneg_right hM2le (by positivity : (0 : ℝ) ≤ 8 * V ^ 2)
    have h2 : (K * a * chiMass) / (8 * V ^ 2) ≤ (K * a) * (K * V) / (8 * V ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hchiV hKa) (by positivity : (0 : ℝ) ≤ 8 * V ^ 2)
    have h3 : (K * a) * (K * V) / (8 * V ^ 2) ≤ K ^ 2 * (μ * a) := by
      have hVne : V ≠ 0 := ne_of_gt hV
      have e : (K * a) * (K * V) / (8 * V ^ 2) = K ^ 2 * a / (8 * V) := by
        field_simp
      rw [e, div_le_iff₀ (by positivity : (0 : ℝ) < 8 * V)]
      have hKa2 : 0 ≤ K ^ 2 * a := mul_nonneg (sq_nonneg K) ha
      have key : (1 : ℝ) ≤ μ * V * 8 := by linarith [hμV]
      nlinarith [hKa2, key]
    linarith [h1, h2, h3]
  have hmain : μ ^ 2 * M1 ^ 2 / (2 * M2) + μ * M1 / (2 * V) + M2 / (8 * V ^ 2)
      ≤ K ^ 2 * (μ ^ 2 * a * chiMass + μ * a) := by
    have e1 : μ ^ 2 * (K * a * chiMass) / 2 ≤ K * (μ ^ 2 * a * chiMass) := by
      have h : 0 ≤ μ ^ 2 * a * chiMass := mul_nonneg (mul_nonneg (sq_nonneg μ) ha) hchi
      nlinarith [hA0, hμ, h]
    have e2 : K * (μ ^ 2 * a * chiMass) ≤ K ^ 2 * (μ ^ 2 * a * chiMass) := by
      have h : 0 ≤ μ ^ 2 * a * chiMass := mul_nonneg (mul_nonneg (sq_nonneg μ) ha) hchi
      nlinarith [h, hK]
    have e3 : K ^ 2 * (μ * a) ≤ K ^ 2 * (μ ^ 2 * a * chiMass + μ * a) := by
      have h : 0 ≤ μ ^ 2 * a * chiMass := mul_nonneg (mul_nonneg (sq_nonneg μ) ha) hchi
      have h2 : 0 ≤ K ^ 2 := sq_nonneg K
      nlinarith [h, h2]
    linarith [t1, t2, t3, e1, e2, e3]
  calc I * (μ ^ 2 * M1 ^ 2 / (2 * M2) + μ * M1 / (2 * V) + M2 / (8 * V ^ 2))
      = (μ ^ 2 * M1 ^ 2 / (2 * M2) + μ * M1 / (2 * V) + M2 / (8 * V ^ 2)) * I := by ring
    _ ≤ K ^ 2 * (μ ^ 2 * a * chiMass + μ * a) * I := mul_le_mul_of_nonneg_right hmain hI

/-- **The payable `boxQ0` floor at the sliding box**, in the allowance shape: this packages
`boxQ0FloorPayable` (the mean-field floor) with `floor_le_allowance` (the mass/regime
arithmetic), at `A = dlBox ℓ d u`, `volA = boxMass ℓ d u`.  The hypotheses
`0 < boxMass`, `1 ≤ μ·boxMass`, `chiMass ≤ K·boxMass` are the FS regime facts (they hold for
`u` in the sliding interior; at a *far* `u` the box is empty and every quantity below vanishes,
so the case must be split off by the caller — see `FINDING_perBoxCrudeLowerB1_status.md` §5). -/
theorem boxQ0_floor_allowance {N : ℕ} {ℓ μ : ℝ} (hℓ : 0 < ℓ) {d : ℝ}
    {u : EuclideanSpace ℝ (Fin 3)} {a chiMass K : ℝ}
    (hμ : 0 ≤ μ) (ha : 0 ≤ a) (hchi : 0 ≤ chiMass) (hK : 1 ≤ K)
    (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    (hμV : 1 ≤ μ * Work.SmallBoxSliding.boxMass ℓ d u)
    (hchiV : chiMass ≤ K * Work.SmallBoxSliding.boxMass ℓ d u)
    {w1 w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (hw2 : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      w2 p.1 p.2) (MeasureTheory.volume.restrict
        (Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u)))
    (hw1 : MeasureTheory.IntegrableOn (Submission.BoseGases.w1Fibre ℓ w1)
      (Submission.BoseGases.dlBox ℓ d u))
    (hM1le : boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u) w1
      ≤ K * a * chiMass)
    (hM1M2 : boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u) w1
      ≤ boxM2 (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u) w2)
    (hM2le : boxM2 (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u) w2
      ≤ K * a * chiMass)
    (hM2pos : 0 < boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.dlBox ℓ d u) w2)
    (hM1nn : 0 ≤ boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u) w1)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    -(K ^ 2 * (μ ^ 2 * a * chiMass + μ * a))
        * (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2)
      ≤ boxQ0 (Work.SmallBoxSliding.boxMass ℓ d u) ℓ μ (Submission.BoseGases.dlBox ℓ d u)
          w1 w2 Φ := by
  have hvolA : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.measureReal_def]
  have hA : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hfloor := boxQ0FloorPayable (N := N) (ℓ := ℓ) (μ := μ)
    (volA := Work.SmallBoxSliding.boxMass ℓ d u)
    hℓ hvol hA hvolA (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u) hμ hw2 hw1 hM2pos hΦc
  have hallow := floor_le_allowance (μ := μ) (a := a)
    (M1 := boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u) w1)
    (M2 := boxM2 (Work.SmallBoxSliding.boxMass ℓ d u) (Submission.BoseGases.dlBox ℓ d u) w2)
    (V := Work.SmallBoxSliding.boxMass ℓ d u) (chiMass := chiMass)
    (I := ∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2) (K := K)
    hK ha hμ hvol hchi (integral_nonneg fun x => sq_nonneg _) hM1nn hM2pos hM1le hM1M2 hM2le hμV hchiV
  have hgoal : -(K ^ 2 * (μ ^ 2 * a * chiMass + μ * a))
        * (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2)
      = -(K ^ 2 * (μ ^ 2 * a * chiMass + μ * a)
        * (∫ x in Submission.BoseGases.abox N ℓ, (Φ x) ^ 2)) := by ring
  rw [hgoal]
  exact le_trans (neg_le_neg hallow) hfloor

/-! ## 4. Scalar homogeneity of the box words (the tool for the homogeneity repair)

Every box word is *quadratic* in the state: `boxFlatCount`, `boxPairCount`, `boxQCount` and the
five words `boxQ0 … boxQ4` (hence `boxQSum`) are homogeneous of degree 2 in `Φ`.  This is the
tool that pulls a box-projection statement back from the normalised case `∫Φ² = 1` to an
arbitrary state; it is exactly what the four refuted intermediate statements of the sibling area
lack (see `FINDING_perBoxCrudeLowerB1_status.md` §6.2). -/



/-- The box condensate projection is linear. -/
theorem boxPInd_constSmul (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) {N : ℕ}
    (i : Fin N) (t : ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    Work.UBBInputs8.boxPInd volA A i (fun x => t * Φ x)
      = fun x => t * Work.UBBInputs8.boxPInd volA A i Φ x := by
  funext x
  simp only [Work.UBBInputs8.boxPInd]
  rw [MeasureTheory.integral_const_mul]
  ring

/-- The box excited projection is linear. -/
theorem boxQInd_constSmul (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3))) {N : ℕ}
    (i : Fin N) (t : ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    Work.UBBInputs8.boxQInd volA A i (fun x => t * Φ x)
      = fun x => t * Work.UBBInputs8.boxQInd volA A i Φ x := by
  funext x
  simp only [Work.UBBInputs8.boxQInd, boxPInd_constSmul]
  ring

/-- Scaling of the square integrand. -/
theorem integral_sq_constSmul {N : ℕ} (ℓ t : ℝ) (f : Submission.BoseGases.X N → ℝ) :
    (∫ x in Submission.BoseGases.abox N ℓ, (t * f x) ^ 2)
      = t ^ 2 * ∫ x in Submission.BoseGases.abox N ℓ, (f x) ^ 2 := by
  rw [show (fun x : Submission.BoseGases.X N => (t * f x) ^ 2)
      = fun x => t ^ 2 * (f x) ^ 2 from by funext x; ring]
  rw [MeasureTheory.integral_const_mul]

/-- Scaling of the square-times-weight integrand. -/
theorem integral_sq_mul_constSmul {N : ℕ} (ℓ t : ℝ) (f g : Submission.BoseGases.X N → ℝ) :
    (∫ x in Submission.BoseGases.abox N ℓ, (t * f x) ^ 2 * g x)
      = t ^ 2 * ∫ x in Submission.BoseGases.abox N ℓ, (f x) ^ 2 * g x := by
  rw [show (fun x : Submission.BoseGases.X N => (t * f x) ^ 2 * g x)
      = fun x => t ^ 2 * ((f x) ^ 2 * g x) from by funext x; ring]
  rw [MeasureTheory.integral_const_mul]

/-- The two-slot projection scaling used by `boxPairCount` and `boxQ0`. -/
theorem boxPP_constSmul {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (p : Fin N × Fin N) (t : ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    Work.UBBInputs8.boxPInd volA A p.1
        (Work.UBBInputs8.boxPInd volA A p.2 (fun x => t * Φ x))
      = fun x => t * Work.UBBInputs8.boxPInd volA A p.1
          (Work.UBBInputs8.boxPInd volA A p.2 Φ) x := by
  rw [boxPInd_constSmul, boxPInd_constSmul]

/-- The mixed two-slot projection scalings. -/
theorem boxPQ_constSmul {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (p : Fin N × Fin N) (t : ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    Work.UBBInputs8.boxPInd volA A p.1
        (Work.UBBInputs8.boxQInd volA A p.2 (fun x => t * Φ x))
      = fun x => t * Work.UBBInputs8.boxPInd volA A p.1
          (Work.UBBInputs8.boxQInd volA A p.2 Φ) x := by
  rw [boxQInd_constSmul, boxPInd_constSmul]

/-- The mixed two-slot projection scalings. -/
theorem boxQP_constSmul {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (p : Fin N × Fin N) (t : ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    Work.UBBInputs8.boxQInd volA A p.2
        (Work.UBBInputs8.boxPInd volA A p.1 (fun x => t * Φ x))
      = fun x => t * Work.UBBInputs8.boxQInd volA A p.2
          (Work.UBBInputs8.boxPInd volA A p.1 Φ) x := by
  rw [boxPInd_constSmul, boxQInd_constSmul]

/-- The mixed two-slot projection scaling with the slots in the other order. -/
theorem boxPQsymm_constSmul {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (p : Fin N × Fin N) (t : ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    Work.UBBInputs8.boxPInd volA A p.2
        (Work.UBBInputs8.boxQInd volA A p.1 (fun x => t * Φ x))
      = fun x => t * Work.UBBInputs8.boxPInd volA A p.2
          (Work.UBBInputs8.boxQInd volA A p.1 Φ) x := by
  rw [boxQInd_constSmul, boxPInd_constSmul]

/-- The two-`Q` projection scaling. -/
theorem boxQQ_constSmul {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (p : Fin N × Fin N) (t : ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    Work.UBBInputs8.boxQInd volA A p.2
        (Work.UBBInputs8.boxQInd volA A p.1 (fun x => t * Φ x))
      = fun x => t * Work.UBBInputs8.boxQInd volA A p.2
          (Work.UBBInputs8.boxQInd volA A p.1 Φ) x := by
  rw [boxQInd_constSmul, boxQInd_constSmul]

/-- The `PP` projection scaling with the slots in the other order. -/
theorem boxPPsymm_constSmul {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (p : Fin N × Fin N) (t : ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    Work.UBBInputs8.boxPInd volA A p.2
        (Work.UBBInputs8.boxPInd volA A p.1 (fun x => t * Φ x))
      = fun x => t * Work.UBBInputs8.boxPInd volA A p.2
          (Work.UBBInputs8.boxPInd volA A p.1 Φ) x := by
  rw [boxPInd_constSmul, boxPInd_constSmul]

/-- The same with the slots in the other order. -/
theorem boxQQsymm_constSmul {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (p : Fin N × Fin N) (t : ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    Work.UBBInputs8.boxQInd volA A p.1
        (Work.UBBInputs8.boxQInd volA A p.2 (fun x => t * Φ x))
      = fun x => t * Work.UBBInputs8.boxQInd volA A p.1
          (Work.UBBInputs8.boxQInd volA A p.2 Φ) x := by
  rw [boxQInd_constSmul, boxQInd_constSmul]

/-- Scaling of a product integrand. -/
theorem integral_mul_constSmul {N : ℕ} (ℓ t : ℝ) (f g h : Submission.BoseGases.X N → ℝ) :
    (∫ x in Submission.BoseGases.abox N ℓ, (t * f x) * (t * g x) * h x)
      = t ^ 2 * ∫ x in Submission.BoseGases.abox N ℓ, f x * g x * h x := by
  rw [show (fun x : Submission.BoseGases.X N => (t * f x) * (t * g x) * h x)
      = fun x => t ^ 2 * (f x * g x * h x) from by funext x; ring]
  rw [MeasureTheory.integral_const_mul]

/-- Scalar homogeneity of the flat count. -/
theorem boxFlatCount_constSmul {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (t : ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    boxFlatCount volA ℓ A (fun x => t * Φ x) = t ^ 2 * boxFlatCount volA ℓ A Φ := by
  simp only [boxFlatCount, boxPInd_constSmul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    integral_sq_constSmul ℓ t (Work.UBBInputs8.boxPInd volA A i Φ)

/-- Scalar homogeneity of the pair-condensate count. -/
theorem boxPairCount_constSmul {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (t : ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    boxPairCount volA ℓ A (fun x => t * Φ x) = t ^ 2 * boxPairCount volA ℓ A Φ := by
  simp only [boxPairCount]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [boxPP_constSmul]
  exact integral_sq_constSmul ℓ t
    (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ))

/-- Scalar homogeneity of the excited count. -/
theorem boxQCount_constSmul {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    (t : ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    boxQCount volA ℓ A (fun x => t * Φ x) = t ^ 2 * boxQCount volA ℓ A Φ := by
  simp only [boxQCount, boxQInd_constSmul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ =>
    integral_sq_constSmul ℓ t (Work.UBBInputs8.boxQInd volA A i Φ)

/-- Scalar homogeneity of the `Q₀` word. -/
theorem boxQ0_constSmul {N : ℕ} (volA ℓ μ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    {w1 w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (t : ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    boxQ0 volA ℓ μ A w1 w2 (fun x => t * Φ x)
      = t ^ 2 * boxQ0 volA ℓ μ A w1 w2 Φ := by
  simp only [boxQ0]
  have h1 : (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A p.1
        (Work.UBBInputs8.boxPInd volA A p.2 (fun x => t * Φ x)) x) ^ 2 * w2 (x p.1) (x p.2))
      = t ^ 2 * (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x) ^ 2
          * w2 (x p.1) (x p.2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [boxPP_constSmul]
    exact integral_sq_mul_constSmul ℓ t
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ))
      (fun x => w2 (x p.1) (x p.2))
  have h2 : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A i (fun x => t * Φ x) x) ^ 2
        * Submission.BoseGases.w1Fibre ℓ w1 (x i))
      = t ^ 2 * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A i Φ x) ^ 2
          * Submission.BoseGases.w1Fibre ℓ w1 (x i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [boxPInd_constSmul]
    exact integral_sq_mul_constSmul ℓ t (Work.UBBInputs8.boxPInd volA A i Φ)
      (fun x => Submission.BoseGases.w1Fibre ℓ w1 (x i))
  rw [h1, h2]
  ring

/-- Scalar homogeneity of the `Q₁` word. -/
theorem boxQ1_constSmul {N : ℕ} (volA ℓ μ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    {w1 w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (t : ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    boxQ1 volA ℓ μ A w1 w2 (fun x => t * Φ x) = t ^ 2 * boxQ1 volA ℓ μ A w1 w2 Φ := by
  simp only [boxQ1]
  have h1 : (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A p.1
        (Work.UBBInputs8.boxQInd volA A p.2 (fun x => t * Φ x)) x)
        * (Work.UBBInputs8.boxPInd volA A p.1
          (Work.UBBInputs8.boxPInd volA A p.2 (fun x => t * Φ x)) x)
        * w2 (x p.1) (x p.2))
      = t ^ 2 * (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
          * w2 (x p.1) (x p.2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [boxPQ_constSmul, boxPP_constSmul]
    exact integral_mul_constSmul ℓ t
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ))
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ))
      (fun x => w2 (x p.1) (x p.2))
  have h2 : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxQInd volA A i (fun x => t * Φ x) x)
        * (Work.UBBInputs8.boxPInd volA A i (fun x => t * Φ x) x)
        * Submission.BoseGases.w1Fibre ℓ w1 (x i))
      = t ^ 2 * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd volA A i Φ x)
          * (Work.UBBInputs8.boxPInd volA A i Φ x)
          * Submission.BoseGases.w1Fibre ℓ w1 (x i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [boxQInd_constSmul, boxPInd_constSmul]
    exact integral_mul_constSmul ℓ t (Work.UBBInputs8.boxQInd volA A i Φ)
      (Work.UBBInputs8.boxPInd volA A i Φ)
      (fun x => Submission.BoseGases.w1Fibre ℓ w1 (x i))
  rw [h1, h2]
  ring

/-- Scalar homogeneity of the `Q₂` word. -/
theorem boxQ2_constSmul {N : ℕ} (volA ℓ μ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    {w1 w2 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (t : ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    boxQ2 volA ℓ μ A w1 w2 (fun x => t * Φ x) = t ^ 2 * boxQ2 volA ℓ μ A w1 w2 Φ := by
  simp only [boxQ2]
  have h1 : (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A p.1
        (Work.UBBInputs8.boxQInd volA A p.2 (fun x => t * Φ x)) x)
        * (Work.UBBInputs8.boxPInd volA A p.2
          (Work.UBBInputs8.boxQInd volA A p.1 (fun x => t * Φ x)) x)
        * w2 (x p.1) (x p.2))
      = t ^ 2 * (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w2 (x p.1) (x p.2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [boxPQ_constSmul, boxPQsymm_constSmul]
    exact integral_mul_constSmul ℓ t
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ))
      (Work.UBBInputs8.boxPInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ))
      (fun x => w2 (x p.1) (x p.2))
  have h2 : (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A p.1
        (Work.UBBInputs8.boxQInd volA A p.2 (fun x => t * Φ x)) x)
        * (Work.UBBInputs8.boxQInd volA A p.2
          (Work.UBBInputs8.boxPInd volA A p.1 (fun x => t * Φ x)) x)
        * w2 (x p.1) (x p.2))
      = t ^ 2 * (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ) x)
          * w2 (x p.1) (x p.2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [boxPQ_constSmul, boxQP_constSmul]
    exact integral_mul_constSmul ℓ t
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ))
      (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxPInd volA A p.1 Φ))
      (fun x => w2 (x p.1) (x p.2))
  have h3 : (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxQInd volA A i (fun x => t * Φ x) x) ^ 2
        * Submission.BoseGases.w1Fibre ℓ w1 (x i))
      = t ^ 2 * (∑ i : Fin N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxQInd volA A i Φ x) ^ 2
          * Submission.BoseGases.w1Fibre ℓ w1 (x i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [boxQInd_constSmul]
    exact integral_sq_mul_constSmul ℓ t (Work.UBBInputs8.boxQInd volA A i Φ)
      (fun x => Submission.BoseGases.w1Fibre ℓ w1 (x i))
  have h4 : (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A p.1
        (Work.UBBInputs8.boxPInd volA A p.2 (fun x => t * Φ x)) x)
        * (Work.UBBInputs8.boxQInd volA A p.2
          (Work.UBBInputs8.boxQInd volA A p.1 (fun x => t * Φ x)) x)
        * w1 (x p.1) (x p.2))
      = t ^ 2 * (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w1 (x p.1) (x p.2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [boxPP_constSmul, boxQQ_constSmul]
    exact integral_mul_constSmul ℓ t
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxPInd volA A p.2 Φ))
      (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ))
      (fun x => w1 (x p.1) (x p.2))
  rw [h1, h2, h3, h4]
  ring

/-- Scalar homogeneity of the `Q₃` word. -/
theorem boxQ3_constSmul {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    {w1 : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (t : ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    boxQ3 volA ℓ A w1 (fun x => t * Φ x) = t ^ 2 * boxQ3 volA ℓ A w1 Φ := by
  simp only [boxQ3]
  have h1 : (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
      (Work.UBBInputs8.boxPInd volA A p.1
        (Work.UBBInputs8.boxQInd volA A p.2 (fun x => t * Φ x)) x)
        * (Work.UBBInputs8.boxQInd volA A p.2
          (Work.UBBInputs8.boxQInd volA A p.1 (fun x => t * Φ x)) x)
        * w1 (x p.1) (x p.2))
      = t ^ 2 * (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
        (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ) x)
          * (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ) x)
          * w1 (x p.1) (x p.2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [boxPQ_constSmul, boxQQ_constSmul]
    exact integral_mul_constSmul ℓ t
      (Work.UBBInputs8.boxPInd volA A p.1 (Work.UBBInputs8.boxQInd volA A p.2 Φ))
      (Work.UBBInputs8.boxQInd volA A p.2 (Work.UBBInputs8.boxQInd volA A p.1 Φ))
      (fun x => w1 (x p.1) (x p.2))
  rw [h1]
  ring

/-- Scalar homogeneity of the `Q₄` bracket (pointwise form). -/
theorem boxQ4B_constSmul {N : ℕ} (volA : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    {om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (t : ℝ) (Φ : Submission.BoseGases.X N → ℝ) (p : Fin N × Fin N) (x : Submission.BoseGases.X N) :
    boxQ4B (N := N) volA A om (fun y => t * Φ y) p x = t * boxQ4B (N := N) volA A om Φ p x := by
  simp only [boxQ4B, boxQQ_constSmul, boxQQsymm_constSmul, boxPP_constSmul, boxPPsymm_constSmul,
    boxPQ_constSmul, boxPQsymm_constSmul, boxQP_constSmul]
  ring

/-- Scalar homogeneity of the `Q₄` word. -/
theorem boxQ4_constSmul {N : ℕ} (volA ℓ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    {w om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (t : ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    boxQ4 volA ℓ A w om (fun x => t * Φ x) = t ^ 2 * boxQ4 volA ℓ A w om Φ := by
  simp only [boxQ4]
  have h1 : (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
      (boxQ4B (N := N) volA A om (fun y => t * Φ y) p x) ^ 2 * w (x p.1) (x p.2))
      = t ^ 2 * (∑ p ∈ Submission.BoseGases.pairSet N, ∫ x in Submission.BoseGases.abox N ℓ,
        (boxQ4B (N := N) volA A om Φ p x) ^ 2 * w (x p.1) (x p.2)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hpt : ∀ x : Submission.BoseGases.X N,
        (boxQ4B (N := N) volA A om (fun y => t * Φ y) p x) ^ 2 * w (x p.1) (x p.2)
          = t ^ 2 * ((boxQ4B (N := N) volA A om Φ p x) ^ 2 * w (x p.1) (x p.2)) := by
      intro x
      rw [boxQ4B_constSmul (N := N) (volA := volA) (A := A) (om := om) (t := t) (Φ := Φ)
        (p := p) x]
      ring
    rw [show (∫ x in Submission.BoseGases.abox N ℓ,
          (boxQ4B (N := N) volA A om (fun y => t * Φ y) p x) ^ 2 * w (x p.1) (x p.2))
        = ∫ x in Submission.BoseGases.abox N ℓ,
            t ^ 2 * ((boxQ4B (N := N) volA A om Φ p x) ^ 2 * w (x p.1) (x p.2)) from by
          apply integral_congr_ae
          filter_upwards with x
          exact hpt x]
    rw [MeasureTheory.integral_const_mul]
  rw [h1]
  ring

/-- **The five-word sum is homogeneous of degree 2.**  This is the tool that pulls a
box-projection statement back from the normalised case `∫Φ² = 1` to an arbitrary state. -/
theorem boxQSum_constSmul {N : ℕ} (volA ℓ μ : ℝ) (A : Set (EuclideanSpace ℝ (Fin 3)))
    {w w1 w2 om : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℝ}
    (t : ℝ) (Φ : Submission.BoseGases.X N → ℝ) :
    boxQSum volA ℓ μ A w w1 w2 om (fun x => t * Φ x)
      = t ^ 2 * boxQSum volA ℓ μ A w w1 w2 om Φ := by
  simp only [boxQSum, boxQ0_constSmul, boxQ1_constSmul, boxQ2_constSmul, boxQ3_constSmul,
    boxQ4_constSmul]
  ring

/-- **The localised count split at the sliding box**: `locCount ≤ K·(boxFlatCount + boxQCount)`
with the explicit constant `K = chiSupAbs·chiSmallDecay M·2^{−M}`.  This packages
`chiSmallB_le_dlBox` with the child `locCountLeWeightedCount`; it is the rung of `PayB1` that
turns the chemical-potential count into the condensate-plus-excited counts. -/
theorem locCount_le_boxCount {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {d : ℝ} (hd : 0 < d)    {u : EuclideanSpace ℝ (Fin 3)} {M : ℕ} (hM : 1 ≤ M)
    (hvol : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ) :
    locCount M ℓ d u Φ
      ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M * (1 / 2) ^ M)
        * (boxFlatCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ
            + boxQCount (Work.SmallBoxSliding.boxMass ℓ d u) ℓ
              (Submission.BoseGases.dlBox ℓ d u) Φ) := by
  have hvolA : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ d u)).toReal := by
    rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.measureReal_def]
  have hK : 0 ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M
      * (1 / 2) ^ M :=
    mul_nonneg (mul_nonneg Submission.BoseGases.chiSupAbs_nonneg
      (Submission.BoseGases.chiSmallDecay_nonneg M)) (by positivity)
  have hmain := locCountLeWeightedCount (N := N) (ℓ := ℓ)
    (volA := Work.SmallBoxSliding.boxMass ℓ d u)
    (K := Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M * (1 / 2) ^ M)
    (A := Submission.BoseGases.dlBox ℓ d u) (M := M) (d := d) (u := u)
    hℓ hvol (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u) hvolA
    (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u) hK
    (fun x => chiSmallB_le_dlBox M hM hℓ hd u x) hΦc
  simpa only [locCount] using hmain

end

end Work.BoseFixB1S

namespace Work.BoseFixB1S

/-! ## 3. The final assembly (the `u`-cover) — session 12

The target quantifies over *all* `u : ℝ³`, while the machinery of the chapter is stated on the
three regions of the sliding geometry: the interior `I₋` (where FS's `thm:smallbox` is applied at
`μ`), the bad band (FS `eq:badset`), and the complement of the sliding cube (`farSet`, where the
localised cut-off vanishes and the word is nonnegative).  Both of the first two regions consume
hypotheses in *exactly* the target's shape (`CrudeIneqAt`), so the cover below turns them into the
target's conclusion with `ε₀ = min` and `C = max`.

Consumers on disk that supply the two hypotheses (see `FINDING_perBoxCrudeLowerB1_status.md` §19):
`perBoxCrudeLower_of_perBoxF` (interior, from the F-weighted per-box bound `PerBoxF`) and
`BandPerBoxCrudeB1` / `bandPerBoxCrude_of_inputs` (band, from the low-state count window). -/

/-- The target's per-`u` inequality, as a predicate. -/
def CrudeIneqAt {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (μ C : ℝ)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (u : EuclideanSpace ℝ (Fin 3)) : Prop :=
  -(C * (μ ^ 2 * (_root_.BoseGases.a v)
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        + μ * (_root_.BoseGases.a v)))
    * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
  ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)

/-- `CrudeIneqAt` is monotone in its constant (the bracket and the norm are nonnegative). -/
theorem CrudeIneqAt.mono {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ C C' : ℝ} {n : ℕ} {Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))}
    {u : EuclideanSpace ℝ (Fin 3)} (hCC : C ≤ C') (hC : 0 ≤ C) (hμ : 0 ≤ μ)
    (ha : 0 ≤ _root_.BoseGases.a v) (hb : CrudeIneqAt h μ C Φ u) : CrudeIneqAt h μ C' Φ u := by
  have hV : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
    Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hbr : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v)
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        + μ * (_root_.BoseGases.a v) :=
    add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha) hV) (mul_nonneg hμ ha)
  have hN : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
    normB_nonneg' μ n (Φ : Submission.BoseGases.X n → ℝ)
  have hstep : C' * (μ ^ 2 * (_root_.BoseGases.a v)
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        + μ * (_root_.BoseGases.a v))
      ≥ C * (μ ^ 2 * (_root_.BoseGases.a v)
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        + μ * (_root_.BoseGases.a v)) :=
    mul_le_mul_of_nonneg_right hCC hbr
  have : -(C' * (μ ^ 2 * (_root_.BoseGases.a v)
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        + μ * (_root_.BoseGases.a v)))
      * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      ≤ -(C * (μ ^ 2 * (_root_.BoseGases.a v)
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        + μ * (_root_.BoseGases.a v)))
      * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    have := mul_le_mul_of_nonneg_right hstep hN
    linarith
  exact le_trans this hb

/-- **The word is nonnegative whenever the localised cut-off vanishes identically.**

If `χ_{B(u)} ≡ 0` then the localised *potential* word vanishes identically
(`Work.BoseFixR.qLHSwordB_eq_zero_of_chiB_zero`, whose two-body kernel
`wSmallPair M ℓ d u v x y = χ_{B(u)}(x)·W(x−y)·χ_{B(u)}(y)` carries one factor of the cut-off per
variable) while the *kinetic* word is nonnegative
(`Work.UBBInputs9.A.tBwordBInd_nonneg`), so `sbWord = sbKin ≥ 0`.

This **strictly generalises** `Work.BoseFixR.sbWord_nonneg_off_cube`: the hypothesis `u ∉ sCube`
(far set) only *implies* `χ_{B(u)} ≡ 0`, because `χ_{B(u)} = chiScale ℓ · chiSmall M((ℓd)⁻¹•· − u)`
has the *ball* `ball(0, ℓ/2)` as its first factor and the translated cube `dlBox ℓ d u` as its
second, so `χ_{B(u)} ≡ 0` holds exactly when those two sets are disjoint — a strictly larger region
than `(sCube)ᶜ` (a box contained in a *corner* of `acube ℓ` meets `acube ℓ` but misses
`ball(0, ℓ/2)`).  On that region the target's inequality is trivial. -/
theorem sbWord_nonneg_of_chiSmallB_eq_zero
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {ε₀ μ : ℝ}
    (hadm : Work.BoseBoxFix.Adm v ε₀ μ) {n : ℕ} {u : EuclideanSpace ℝ (Fin 3)}
    (hχ : ∀ x : EuclideanSpace ℝ (Fin 3),
      Submission.BoseGases.chiSmallB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x = 0)
    (Φ : Submission.BoseGases.X n → ℝ) :
    0 ≤ Work.BoseFixB1.sbWord h μ u Φ := by
  have hz : Work.BoseFixB1.sbPot h μ u Φ = 0 :=
    Work.BoseFixR.qLHSwordB_eq_zero_of_chiB_zero (v := v) (h := h) hχ Φ
  rw [Work.BoseFixB1.sbWord, hz, add_zero]
  exact Work.UBBInputs9.A.tBwordBInd_nonneg (Work.BoseFixB1.adm_ell_pos hadm)
    (Work.BoseFixB1.adm_eT_bounds hadm).1 u Φ

/-- **The `chiMass = 0` case of the target's inequality.**

`chiMass M ℓ d u = ∫_x χ_{B(u)}(x)² dx` vanishes exactly when the two factors of the localised
cut-off have disjoint supports (the ball `ball(0, ℓ/2)` misses the translated cube `dlBox ℓ d u`).
Since `χ_{B(u)}²` is continuous and compactly supported, a vanishing integral forces
`χ_{B(u)} ≡ 0`, and `sbWord_nonneg_of_chiSmallB_eq_zero` then gives `sbWord ≥ 0` — so the target's
inequality (whose left-hand side is `≤ 0` there) holds with `C` arbitrary.

This removes the whole `{chiMass = 0}` region from the two atoms the target is reduced to: every
filed producer of the good-set / bad-set bounds needs to cover only `{u : 0 < chiMass … u}`, which
is the region where the localised kernels are genuinely alive. -/
theorem sbWord_nonneg_of_chiMass_eq_zero
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {ε₀ μ : ℝ}
    (hadm : Work.BoseBoxFix.Adm v ε₀ μ) {n : ℕ} {u : EuclideanSpace ℝ (Fin 3)}
    (h0 : Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u = 0)
    (Φ : Submission.BoseGases.X n → ℝ) :
    0 ≤ Work.BoseFixB1.sbWord h μ u Φ := by
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hadm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hadm
  have hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.M_eq_mValue]; norm_num [Work.BoseBox.mValue]
  refine sbWord_nonneg_of_chiSmallB_eq_zero hadm (fun x => ?_) Φ
  have hcont : Continuous (fun y : EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.chiSmallB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u y) ^ 2) :=
    (Submission.BoseGases.chiSmallB_continuous
      (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) hM hℓ hd u).pow 2
  have hcs : HasCompactSupport (fun y : EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.chiSmallB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u y) ^ 2) := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Metric.closedBall 0 (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
      (isCompact_closedBall 0 _) ?_
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hy' : Submission.BoseGases.chiSmallB
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u y ≠ 0 := by
      intro hh; exact hy (by simp [hh])
    have hb := Submission.BoseGases.chiSmallB_support_big_box
      (M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M) hM
      (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) hℓ (u := u) (x := y) hy'
    have h2 : ‖y‖ ^ 2 ≤ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      have h3 : ∀ j : Fin 3,
          ‖y.ofLp j‖ ^ 2 ≤ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v) / 2) ^ 2 := fun j => by
        rw [Real.norm_eq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hb j) 2
      calc ∑ j, ‖y.ofLp j‖ ^ 2
          ≤ ∑ _j : Fin 3, (Work.BoseBox.sideAt μ (_root_.BoseGases.a v) / 2) ^ 2 :=
            Finset.sum_le_sum (fun j _ => h3 j)
        _ = 3 * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v) / 2) ^ 2 := by simp
        _ ≤ (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 2 := by nlinarith [hℓ]
    nlinarith [norm_nonneg y, h2]
  have hint : MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.chiSmallB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u y) ^ 2) :=
    Continuous.integrable_of_hasCompactSupport hcont hcs
  have hnn : 0 ≤ fun y : EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.chiSmallB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u y) ^ 2 := fun y => sq_nonneg _
  have hz : (fun y : EuclideanSpace ℝ (Fin 3) =>
      (Submission.BoseGases.chiSmallB (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u y) ^ 2)
      =ᵐ[MeasureTheory.volume] 0 := by
    have h := (MeasureTheory.integral_eq_zero_iff_of_nonneg hnn hint).mp ?_
    · exact h
    · simpa only [Work.SmallBoxSliding.chiMass_def] using h0
  have heq := MeasureTheory.Measure.eq_of_ae_eq hz hcont continuous_const
  have hx := congrFun heq x
  simpa using hx

/-- **The cover of the sliding geometry**: every `u` lies in the interior, in the bad band, or
outside the sliding cube (the far set, where the localised cut-off vanishes). -/
theorem interior_or_band_or_offCube {ℓ d μ : ℝ} (u : EuclideanSpace ℝ (Fin 3)) :
    u ∈ Work.SmallBoxSliding.interiorSet ℓ d μ ∨ u ∈ Work.SmallBoxSliding.bandSet ℓ d μ
      ∨ u ∈ (Work.BoseFixR.sCube ℓ d)ᶜ := by
  by_cases h1 : ∀ j : Fin 3,
      |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d) - 2 * μ ^ (-1 / 3 : ℝ)
  · exact Or.inl h1
  · push_neg at h1
    obtain ⟨j, hj⟩ := h1
    by_cases h2 : ∀ j : Fin 3, |((ℓ * d) • u).ofLp j| ≤ (1 / 2) * ℓ * (1 + d)
    · refine Or.inr (Or.inl ?_)
      simp only [Work.SmallBoxSliding.bandSet, Set.mem_setOf_eq]
      exact ⟨⟨j, le_of_lt hj⟩, h2⟩
    · push_neg at h2
      obtain ⟨j', hj'⟩ := h2
      refine Or.inr (Or.inr ?_)
      intro hmem
      simp only [Work.BoseFixR.sCube, Set.mem_setOf_eq] at hmem
      exact absurd (hmem j') (not_le_of_gt hj')

/-- **The three-case assembly of the target.**  If the target's inequality holds on the interior
`I₋` (with `(ε₁, C₁)`) and on the bad band (with `(ε₂, C₂)`), then it holds for *every* `u` with
`ε₀ = min ε₁ ε₂` and `C = max C₁ C₂`: the off-cube case is the proved
`Work.BoseFixR.sbWord_nonneg_off_cube` against the (nonpositive) left-hand side. -/
theorem perBoxCrudeLower_of_interior_band
    {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {J : ℝ}
    (ha : 0 ≤ _root_.BoseGases.a v)
    (hint : ∃ ε₁ C₁ : ℝ, 0 < ε₁ ∧ 0 ≤ C₁ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₁ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
            ∀ u ∈ Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
              CrudeIneqAt h μ C₁ Φ u)
    (hband : ∃ ε₂ C₂ : ℝ, 0 < ε₂ ∧ 0 ≤ C₂ ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₂ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
            ∀ u ∈ Work.SmallBoxSliding.bandSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
              CrudeIneqAt h μ C₂ Φ u) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
            ∀ u : EuclideanSpace ℝ (Fin 3), CrudeIneqAt h μ C Φ u := by
  obtain ⟨ε₁, C₁, hε₁, hC₁, hp1⟩ := hint
  obtain ⟨ε₂, C₂, hε₂, hC₂, hp2⟩ := hband
  refine ⟨min ε₁ ε₂, max C₁ C₂, lt_min hε₁ hε₂, le_trans hC₁ (le_max_left _ _), ?_⟩
  intro μ hAdm hJK n Φ hlow u
  have hA1 : Work.BoseBoxFix.Adm v ε₁ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
  have hA2 : Work.BoseBoxFix.Adm v ε₂ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
  have hμ : 0 ≤ μ := (Work.BoseFixB1.adm_mu_pos hAdm).le
  rcases interior_or_band_or_offCube (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (d := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) (μ := μ) u with hu1 | hu2 | hu3
  · exact CrudeIneqAt.mono (le_max_left _ _) hC₁ hμ ha (hp1 μ hA1 hJK n Φ hlow u hu1)
  · exact CrudeIneqAt.mono (le_max_right _ _) hC₂ hμ ha (hp2 μ hA2 hJK n Φ hlow u hu2)
  · -- off the sliding cube the cut-off vanishes: `sbWord ≥ 0`, and the left side is `≤ 0`
    have hsw : 0 ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) :=
      Work.BoseFixR.sbWord_nonneg_off_cube (v := v) (h := h) hA1 hu3
        (Φ : Submission.BoseGases.X n → ℝ)
    have hV : 0 ≤ Work.SmallBoxSliding.chiMass
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
      Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
    have hbr : 0 ≤ μ ^ 2 * (_root_.BoseGases.a v)
          * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          + μ * (_root_.BoseGases.a v) :=
      add_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha) hV) (mul_nonneg hμ ha)
    have hN : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
      normB_nonneg' μ n (Φ : Submission.BoseGases.X n → ℝ)
    have hCmax : 0 ≤ max C₁ C₂ := le_trans hC₁ (le_max_left _ _)
    have : -(max C₁ C₂ * (μ ^ 2 * (_root_.BoseGases.a v)
          * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          + μ * (_root_.BoseGases.a v)))
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) ≤ 0 := by
      have := mul_nonneg (mul_nonneg hCmax hbr) hN
      linarith
    exact le_trans this hsw

/-- **The target from the two frontier atoms** (filed as `Work.BoseFixB1B.PerBoxFLow` and
`Work.BoseFixB1B.OffGoodCrudeLow`): the interior half is the proved child
`perBoxCrudeLower_goodSet_of_perBoxFLow` and the complement is the second atom; the trivial
`goodSet ∪ goodSetᶜ` split and the two degenerate (`normB = 0`) cases are handled by
`sbWord_nonneg_of_normB_eq_zero` and `CrudeIneqAt.mono`.  This isolates the node's entire
remaining content in those two atoms. -/
theorem perBoxCrudeLowerB1_of_atoms {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J)
    (hF : ∃ ε₁ c₁ C₁ : ℝ, 0 < ε₁ ∧ 0 < c₁ ∧ 0 ≤ C₁ ∧ Work.BoseFixB1B.PerBoxFLow v h R J c₁ C₁ ε₁)
    (hOff : ∃ ε₂ C₂ : ℝ, 0 < ε₂ ∧ 0 ≤ C₂ ∧ Work.BoseFixB1B.OffGoodCrudeLow v h J C₂ ε₂) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
            ∀ u : EuclideanSpace ℝ (Fin 3),
              CrudeIneqAt h μ C Φ u := by
  obtain ⟨ε₁, c₁, C₁, hε₁, hc₁, hC₁, hFL⟩ := hF
  obtain ⟨ε₂, C₂, hε₂, hC₂, hOff'⟩ := hOff
  obtain ⟨εin, Cin, hεin, hCin, hint⟩ :=
    perBoxCrudeLower_goodSet_of_perBoxFLow (v := v) h hv hv1 hvrad hR hv_supp hav hJ
      hε₁ hc₁ hC₁ hFL
  refine ⟨min εin ε₂, max Cin C₂, ?_, ?_, ?_⟩
  · exact lt_min hεin hε₂
  · exact le_trans hCin (le_max_left Cin C₂)
  · intro μ hAdm hJK n Φ hlow u
    have hAin : Work.BoseBoxFix.Adm v εin μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
    have hAoff : Work.BoseBoxFix.Adm v ε₂ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
    have hμ : 0 ≤ μ := (Work.BoseFixB1.adm_mu_pos hAdm).le
    have ha : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
    have hV : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
      Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
    have hN : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
      normB_nonneg' μ n (Φ : Submission.BoseGases.X n → ℝ)
    have hzero : -(max Cin C₂ * (μ ^ 2 * (_root_.BoseGases.a v)
          * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
          + μ * (_root_.BoseGases.a v)))
        * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) = 0 → True :=
      fun _ => trivial
    by_cases hmem : u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ
    · by_cases hn : 0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      · exact CrudeIneqAt.mono (le_max_left Cin C₂) hCin hμ ha
          (hint μ hAin hJK n Φ hn hlow u hmem)
      · have h0 : Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) = 0 := by
          linarith
        have hsw := Work.BoseFixB1S.sbWord_nonneg_of_normB_eq_zero (v := v) (h := h) hAin u h0
        have hz : -(max Cin C₂ * (μ ^ 2 * (_root_.BoseGases.a v)
              * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              + μ * (_root_.BoseGases.a v)))
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) = 0 := by
          simp [h0]
        exact le_trans (le_of_eq hz) hsw
    · by_cases hn : 0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      · exact CrudeIneqAt.mono (le_max_right Cin C₂) hC₂ hμ ha
          (hOff' μ hAoff hJK n Φ hn hlow u hmem)
      · have h0 : Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) = 0 := by
          linarith
        have hsw := Work.BoseFixB1S.sbWord_nonneg_of_normB_eq_zero (v := v) (h := h) hAoff u h0
        have hz : -(max Cin C₂ * (μ ^ 2 * (_root_.BoseGases.a v)
              * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              + μ * (_root_.BoseGases.a v)))
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) = 0 := by
          simp [h0]
        exact le_trans (le_of_eq hz) hsw

/-- **The `chiMass > 0`-restricted bad-set atom.**  `Work.BoseFixB1B.OffGoodCrudeLow` with the
extra hypothesis `0 < chiMass(u)`: the crude per-box lower bound is required only where the
localised kernels are genuinely alive.  This is *strictly weaker* than the filed atom, and it is
equivalent to it modulo the `chiMass = 0` case, which is proved outright here
(`sbWord_nonneg_of_chiMass_eq_zero`). -/
def OffGoodCrudePos (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (J : ℝ)
    (C ε₀ : ℝ) : Prop :=
  ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
    J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
    ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
      0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) →
      Work.BoseBoxFix.IsLowB v h J μ n Φ →
      ∀ u : EuclideanSpace ℝ (Fin 3),
        u ∉ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ →
        0 < Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u →
        -(C * (μ ^ 2 * (_root_.BoseGases.a v)
                * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              + μ * (_root_.BoseGases.a v)))
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
          ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ)

/-- **The target from the `chiMass > 0`-restricted atom.**  Same assembly as
`perBoxCrudeLowerB1_of_atoms`, but the bad-set half is only demanded where the localised cut-off
is alive: at the `u ∉ goodSet` with `chiMass(u) = 0` the word is nonnegative
(`sbWord_nonneg_of_chiMass_eq_zero`), so the target's inequality is trivial there. -/
theorem perBoxCrudeLowerB1_of_atoms_pos {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v}
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J)
    (hF : ∃ ε₁ c₁ C₁ : ℝ, 0 < ε₁ ∧ 0 < c₁ ∧ 0 ≤ C₁ ∧ Work.BoseFixB1B.PerBoxFLow v h R J c₁ C₁ ε₁)
    (hOff : ∃ ε₂ C₂ : ℝ, 0 < ε₂ ∧ 0 ≤ C₂ ∧ OffGoodCrudePos v h J C₂ ε₂) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
            ∀ u : EuclideanSpace ℝ (Fin 3),
              CrudeIneqAt h μ C Φ u := by
  obtain ⟨ε₁, c₁, C₁, hε₁, hc₁, hC₁, hFL⟩ := hF
  obtain ⟨ε₂, C₂, hε₂, hC₂, hOff'⟩ := hOff
  obtain ⟨εin, Cin, hεin, hCin, hint⟩ :=
    perBoxCrudeLower_goodSet_of_perBoxFLow (v := v) h hv hv1 hvrad hR hv_supp hav hJ
      hε₁ hc₁ hC₁ hFL
  refine ⟨min εin ε₂, max Cin C₂, ?_, ?_, ?_⟩
  · exact lt_min hεin hε₂
  · exact le_trans hCin (le_max_left Cin C₂)
  · intro μ hAdm hJK n Φ hlow u
    have hAin : Work.BoseBoxFix.Adm v εin μ := Work.BoseFixB1.Adm.mono hAdm (min_le_left _ _)
    have hAoff : Work.BoseBoxFix.Adm v ε₂ μ := Work.BoseFixB1.Adm.mono hAdm (min_le_right _ _)
    have hμ : 0 ≤ μ := (Work.BoseFixB1.adm_mu_pos hAdm).le
    have ha : 0 ≤ _root_.BoseGases.a v := le_of_lt hav
    have hV : 0 ≤ Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
      Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
    have hN : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
      normB_nonneg' μ n (Φ : Submission.BoseGases.X n → ℝ)
    by_cases hmem : u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ
    · by_cases hn : 0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
      · exact CrudeIneqAt.mono (le_max_left Cin C₂) hCin hμ ha
          (hint μ hAin hJK n Φ hn hlow u hmem)
      · have h0 : Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) = 0 := by
          linarith
        have hsw := Work.BoseFixB1S.sbWord_nonneg_of_normB_eq_zero (v := v) (h := h) hAin u h0
        have hz : -(max Cin C₂ * (μ ^ 2 * (_root_.BoseGases.a v)
              * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              + μ * (_root_.BoseGases.a v)))
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) = 0 := by
          simp [h0]
        exact le_trans (le_of_eq hz) hsw
    · by_cases hχ0 : Work.SmallBoxSliding.chiMass
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u = 0
      · have hsw := sbWord_nonneg_of_chiMass_eq_zero (v := v) (h := h) hAoff hχ0
          (Φ : Submission.BoseGases.X n → ℝ)
        have hz : -(max Cin C₂ * (μ ^ 2 * (_root_.BoseGases.a v)
              * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              + μ * (_root_.BoseGases.a v)))
            * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) ≤ 0 := by
          rw [hχ0, mul_zero, zero_add]
          have h1 : 0 ≤ max Cin C₂ * (μ * _root_.BoseGases.a v) :=
            mul_nonneg (le_trans hCin (le_max_left _ _)) (mul_nonneg hμ ha)
          have := mul_nonneg h1 hN
          linarith
        exact le_trans hz hsw
      · have hχpos : 0 < Work.SmallBoxSliding.chiMass
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
          lt_of_le_of_ne hV (Ne.symm hχ0)
        by_cases hn : 0 < Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
        · exact CrudeIneqAt.mono (le_max_right Cin C₂) hC₂ hμ ha
            (hOff' μ hAoff hJK n Φ hn hlow u hmem hχpos)
        · have h0 : Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) = 0 := by
            linarith
          have hsw := Work.BoseFixB1S.sbWord_nonneg_of_normB_eq_zero (v := v) (h := h) hAoff u h0
          have hz : -(max Cin C₂ * (μ ^ 2 * (_root_.BoseGases.a v)
                * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                + μ * (_root_.BoseGases.a v)))
              * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) = 0 := by
            simp [h0]
          exact le_trans (le_of_eq hz) hsw

theorem perBoxCrudeLowerB1 {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) {J : ℝ} (hJ : Work.UBB.lhyC ≤ J) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
        J ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3 →
        ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
          Work.BoseBoxFix.IsLowB v h J μ n Φ →
            ∀ u : EuclideanSpace ℝ (Fin 3),
              -(C * (μ ^ 2 * (_root_.BoseGases.a v)
                    * Work.SmallBoxSliding.chiMass
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                    + μ * (_root_.BoseGases.a v)))
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                ≤ Work.BoseFixB1.sbWord h μ u (Φ : Submission.BoseGases.X n → ℝ) := by sorry
-- NOTE (session 11): this target is NOT the unconditional crude bound, and `IsLowB` is
-- load-bearing.  The sibling nodes `crudeBoundFresh`, `flatArmSliding`, `condensedArmSliding`,
-- `PerBoxWordCrudeHigh`, `SlabCondensedHalf` are the same statement WITHOUT `IsLowB`, and a
-- delegated prover has now (session 11) refuted the pair-alive branch of that chain with a
-- corner-box family `Φ = ∏ h(xᵢ)` (`chiB ≡ 0` there kills `sbKin`; the smooth window
-- `chiSmallB ≈ χ(·/ℓ)` is `O(d^M)`-suppressed at the corner of `Λ`, and `fibSum` carries two of
-- those factors while `pairSum` carries four): the deficit there is `≈ σ²(μ c₁ n − c₂ n²/V)`,
-- an `n`-linear debit against an `n`-free allowance.  See
-- `FINDING_perBoxCrudeLowerB1_status.md` §18 for the state of the question and for why the
-- `IsLowB`-aware route (`LowBoxCount` + `perBoxCrudeLower_of_lowCount`, both in this file) is
-- the only one consistent with the refutations.

end Work.BoseFixB1S
