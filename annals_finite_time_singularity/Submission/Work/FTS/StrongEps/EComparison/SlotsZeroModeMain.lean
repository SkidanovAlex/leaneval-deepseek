/-
# `SlotsZeroModeMain` — the zero-mode weak ODE of a homogeneous `bslOp`-solution

This module carries the proof of `Work.FTS.StrongEps.EComparison.SlotsZeroModeODE`
(the statement itself lives in the sibling file `SlotsZeroModeODE.lean`).

## The mathematics

`Φ` solves `bslOp α Φ = 0` on the open quadrant `Q0 = (0,∞) × (0,π/2)` and `Φ/sin 2θ` is in the
weighted space `ℋ⁶`; the angular Dirichlet eigenfunctions `e_m = eFam m` of `Lzero` (eigenvalue
`lam m = 2m(2m+5)`, self-adjoint weight `cos θ dθ`) give the mode coefficients

  `S_m(z) = ∫_θ Φ(z,θ)·e_m(θ)·cos θ dθ`.

The claim is that `S_m` solves the radial Euler equation `α²z²S_m'' + α(5+α)zS_m' = (lam m)S_m`
in the weak sense against the self-adjoint weight `z^((5-α)/α)`, and lies in `L²(z^{-4})`.

## The route

The weight `z^((5-α)/α)·cos θ` is exactly the weight of the *proved* integration-by-parts
identity `Work.EllipticEst.ModalSolution.bslOp_ibp`, but that identity is only available for test
functions `φ` which are compactly supported *inside* `Q0`, whereas the test function we need is
`ρ(z)·e_m(θ)` (`ρ` compactly supported in `(0,∞)`, `e_m` not vanishing at `θ = 0`).  We therefore
pair `bslOp α Φ = 0` against the *cut-off* test functions

  `ρ(z)·(χ_n(θ)·e_m(θ))`,   `χ_n = angCut n`   (`χ_n = 1` off the layer, `0` off `[δ_n, π/2-δ_n]`),

which are admissible; the identity reads

  `0 = ∫_{Q0} Φ·(bslOp (ρ⊗(χ_n e_m)))·wgt = ∫_{Q0} Φ·(1-angCut n)·(bslOp Ψ)·wgt - ∫_{Q0} Φ·ρ·comm_n·wgt`

with `Ψ = ρ ⊗ e_m` and `comm_n = [Lzero, χ_n](e_m)`.  Both correction terms are supported in the
two boundary layers, of widths `2δ_n`, and the `ℋ⁶`-membership gives
`∫_{layer} |Φ| ≲ √(sliceEnergy Φ z)·δ_n^{(3+η)/2}`; hence both tend to `0` and

  `∫_{Q0} Φ·(bslOp α (ρ⊗e_m))·(z^((5-α)/α)cos θ) = 0`,

which is the claim after Fubini, `eFam_Lzero` and the self-adjointness of the radial operator.

## Contents

* `L2Facts` / `CutFacts` — the statements of the two delegated modules (`SlotsZeroModeL2`,
  `SlotsZeroCutoff`), so that this file can be developed and compiled independently of them;
* the localisation of a compactly supported `ρ` to a box `[a,b] ⊆ (0,∞)`;
* `modeTest m ρ n = ρ ⊗ (angCut n · e_m)` and its smoothness/compact-support properties;
* `perN_zero` — the `bslOp_ibp` identity for the cut-off test functions;
* `key_set` — the vanishing of the pairing of `Φ` with `bslOp α (ρ ⊗ e_m)`;
* `key_eq_target` — Fubini identification of that pairing with the target iterated integral.
-/
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.Defs
import Submission.Work.FTS.PhiStar.Gegenbauer.eFam_Lzero
import Submission.Work.FTS.PhiStar.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.EllipticEst.ModalSolution.bslOp_ibp
import Submission.Work.FTS.ClassC.psiTrunc_uncurry_smooth
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EComparison

set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## The facts supplied by the two delegated modules -/

/-- **The `ℋ⁶`-weighted consequences of `hHk`** (verbatim the conclusion of
`Work.FTS.StrongEps.EComparison.SlotsZeroModeL2`). -/
def L2Facts (α : ℝ) (Φ : ℝ → ℝ → ℝ) : Prop :=
  (∀ m : ℕ,
    MeasureTheory.LocallyIntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) (Set.Ioi 0) ∧
    MeasureTheory.IntegrableOn (fun z => (∫ θ in Work.Spaces.Iθ,
      Φ z θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ * Real.cos θ) ^ 2 * z ^ (-4 : ℝ))
      (Set.Ioi 0)) ∧
  (∀ z ∈ Set.Ioi (0 : ℝ),
    MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Ioi (0 : ℝ),
    ∫ θ in Work.Spaces.Iθ, |Φ z θ| ≤ C * Real.sqrt (sliceEnergy Φ z)) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ z ∈ Set.Ioi (0 : ℝ), ∀ δ ∈ Set.Ioc (0 : ℝ) (π / 4),
    (∫ θ in Set.Ioo 0 δ, |Φ z θ|
        ≤ C * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2)) ∧
    (∫ θ in Set.Ioo (π / 2 - δ) (π / 2), |Φ z θ|
        ≤ C * Real.sqrt (sliceEnergy Φ z) * δ ^ ((3 + Work.Spaces.eta) / 2))) ∧
  (∀ a b : ℝ, 0 < a → a ≤ b →
    MeasureTheory.IntegrableOn (fun z => Real.sqrt (sliceEnergy Φ z)) (Set.Icc a b)) ∧
  (∀ a b : ℝ, 0 < a → a ≤ b →
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
      Φ z θ ^ 2 * rootWeight θ) (Set.Icc a b)) ∧
  (∀ a b : ℝ, 0 < a → a ≤ b →
    MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|) (Set.Icc a b))

/-- **The facts about the shrinking cut-off** (verbatim the conclusion of
`Work.FTS.StrongEps.EComparison.SlotsZeroCutoff`). -/
def CutFacts (m : ℕ) : Prop :=
  (∀ n k : ℕ, ContDiff ℝ k (angCut n)) ∧
  (∀ n : ℕ, tsupport (angCut n) ⊆ Set.Icc (delta n) (π / 2 - delta n)) ∧
  (∀ θ : ℝ, 0 < θ → θ < π / 2 → ∀ᶠ n in atTop, angCut n θ = 1) ∧
  (∀ n : ℕ, ∀ θ : ℝ, 0 ≤ angCut n θ ∧ angCut n θ ≤ 1) ∧
  (∀ n : ℕ, 0 < delta n) ∧
  Tendsto delta atTop (𝓝 0) ∧
  (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, ∀ θ : ℝ, 0 < θ → θ < π / 2 →
    |Work.FTS.EllipticEst.Lzero1 (fun t => angCut n t * Work.FTS.PhiStar.Gegenbauer.eFam m t) θ
        - angCut n θ * Work.FTS.EllipticEst.Lzero1 (Work.FTS.PhiStar.Gegenbauer.eFam m) θ|
      ≤ C / delta n * layerInd n θ)

/-! ## Elementary accessors of the cut-off data -/

lemma CutFacts.delta_pos {m : ℕ} (h : CutFacts m) (n : ℕ) : 0 < delta n := h.2.2.2.2.1 n

lemma CutFacts.tsupport_subset {m : ℕ} (h : CutFacts m) (n : ℕ) :
    tsupport (angCut n) ⊆ Set.Icc (delta n) (π / 2 - delta n) := h.2.1 n

lemma CutFacts.bounds {m : ℕ} (h : CutFacts m) (n : ℕ) (θ : ℝ) :
    0 ≤ angCut n θ ∧ angCut n θ ≤ 1 := h.2.2.2.1 n θ

/-- `angCut n` vanishes at and beyond the left end of its support. -/
lemma CutFacts.eq_zero_of_le_delta {m : ℕ} (h : CutFacts m) (n : ℕ) {θ : ℝ}
    (hθ : θ ≤ delta n) : angCut n θ = 0 := by
  have hd := h.delta_pos n
  have h1 : θ / delta n - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hd]; exact hθ
  simp only [angCut, Real.smoothTransition.zero_of_nonpos h1, zero_mul]

/-- `angCut n` vanishes at and beyond the right end of its support. -/
lemma CutFacts.eq_zero_of_ge {m : ℕ} (h : CutFacts m) (n : ℕ) {θ : ℝ}
    (hθ : π / 2 - delta n ≤ θ) : angCut n θ = 0 := by
  have hd := h.delta_pos n
  have h1 : (π / 2 - θ) / delta n - 1 ≤ 0 := by
    rw [sub_nonpos, div_le_one hd]; linarith
  simp only [angCut, Real.smoothTransition.zero_of_nonpos h1, mul_zero]

/-- `angCut n` vanishes off its (closed) support interval. -/
lemma CutFacts.vanishes_off_tsupport {m : ℕ} (h : CutFacts m) (n : ℕ) {θ : ℝ}
    (hθ : θ ∉ tsupport (angCut n)) : angCut n θ = 0 :=
  image_eq_zero_of_notMem_tsupport hθ

/-- `angCut n = 1` off the layer. -/
lemma CutFacts.eq_one_off_layer {m : ℕ} (h : CutFacts m) (n : ℕ) {θ : ℝ}
    (hθ1 : 2 * delta n ≤ θ) (hθ2 : θ ≤ π / 2 - 2 * delta n) : angCut n θ = 1 := by
  have hd := h.delta_pos n
  have h1 : (1 : ℝ) ≤ θ / delta n - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hd]; linarith
  have h2 : (1 : ℝ) ≤ (π / 2 - θ) / delta n - 1 := by
    rw [le_sub_iff_add_le, le_div_iff₀ hd]; linarith
  simp only [angCut, Real.smoothTransition.one_of_one_le h1,
    Real.smoothTransition.one_of_one_le h2, mul_one]

/-! ## Localisation of a compactly supported radial function -/

/-- A compactly supported function on `(0,∞)` is supported in an interval `[a,b] ⊆ (0,∞)`. -/
theorem exists_Icc_of_tsupport_subset {ρ : ℝ → ℝ} (hρc : HasCompactSupport ρ)
    (hρs : tsupport ρ ⊆ Set.Ioi 0) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ tsupport ρ ⊆ Set.Icc a b := by
  rcases eq_empty_or_nonempty (tsupport ρ) with h | h
  · exact ⟨1, 1, by norm_num, le_rfl, by rw [h]; exact Set.empty_subset _⟩
  · obtain ⟨x, hx, hmin⟩ := hρc.isCompact.exists_isMinOn h continuous_id.continuousOn
    obtain ⟨y, hy, hmax⟩ := hρc.isCompact.exists_isMaxOn h continuous_id.continuousOn
    exact ⟨x, y, hρs hx, (isMinOn_iff.mp hmin) y hy,
      fun z hz => ⟨(isMinOn_iff.mp hmin) z hz, (isMaxOn_iff.mp hmax) z hz⟩⟩

/-- Integrability on the open quadrant of a function which is continuous on a compact box
contained in `Q0` and vanishes outside it. -/
theorem integrableOn_Q0_of_box {f : ℝ × ℝ → ℝ} {a b c d : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : 0 < c) (hcd : c ≤ d) (hd : d < π / 2)
    (hvan : ∀ p : ℝ × ℝ, p ∉ Set.Icc a b ×ˢ Set.Icc c d → f p = 0)
    (hcont : ContinuousOn f (Set.Icc a b ×ˢ Set.Icc c d)) :
    MeasureTheory.IntegrableOn f Work.FTS.EllipticEst.Q0 := by
  have hKsub : Set.Icc a b ×ˢ Set.Icc c d ⊆ Work.FTS.EllipticEst.Q0 := fun p hp =>
    Work.FTS.EllipticEst.mem_Q0.mpr
      ⟨lt_of_lt_of_le ha hp.1.1, lt_of_lt_of_le hc hp.2.1, lt_of_le_of_lt hp.2.2 hd⟩
  have hKcomp : IsCompact (Set.Icc a b ×ˢ Set.Icc c d) := isCompact_Icc.prod isCompact_Icc
  have hKint : IntegrableOn f (Set.Icc a b ×ˢ Set.Icc c d) :=
    hcont.integrableOn_compact hKcomp
  have hsupp : Function.support f ⊆ Set.Icc a b ×ˢ Set.Icc c d := fun p hp =>
    by_contra fun h => hp (hvan p h)
  exact (hKint.mono_set (Set.inter_subset_right.trans hsupp)).of_inter_support
    Work.FTS.EllipticEst.isOpen_Q0.measurableSet

/-! ## `bslOp` of a smooth function is continuous on the open quadrant -/

theorem continuousOn_bslOp_of_smoothOpen {α : ℝ} {ψ : ℝ → ℝ → ℝ}
    (hψ : Work.FTS.EllipticEst.SmoothOpen ψ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.bslOp α ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := (hψ.pzIter 2).continuousOn
  have h2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := (hψ.pz).continuousOn
  have h3 : ContinuousOn (fun p : ℝ × ℝ => Work.Elliptic.Lzero ψ p.1 p.2)
      Work.FTS.EllipticEst.Q0 := Work.EllipticEst.ModalSolution.continuousOn_Lzero hψ
  have hz : ContinuousOn (fun p : ℝ × ℝ => p.1) Work.FTS.EllipticEst.Q0 := continuousOn_fst
  have h4 : ContinuousOn (fun p : ℝ × ℝ => -(α ^ 2 * p.1 ^ 2)) Work.FTS.EllipticEst.Q0 :=
    (continuousOn_const.mul (hz.pow 2)).neg
  have h5 : ContinuousOn (fun p : ℝ × ℝ => α * (5 + α) * p.1) Work.FTS.EllipticEst.Q0 :=
    continuousOn_const.mul hz
  have hmain : ContinuousOn (fun p : ℝ × ℝ =>
      -(α ^ 2 * p.1 ^ 2) * Work.Spaces.pzIter 2 ψ p.1 p.2
        - (α * (5 + α) * p.1) * Work.Spaces.pz ψ p.1 p.2
        + Work.Elliptic.Lzero ψ p.1 p.2) Work.FTS.EllipticEst.Q0 :=
    ((h4.mul h1).sub (h5.mul h2)).add h3
  simpa only [Work.Elliptic.bslOp_apply] using hmain

theorem continuousOn_weight (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => bslWeight α p) Work.FTS.EllipticEst.Q0 := by
  refine ContinuousOn.mul ?_ ?_
  · exact continuousOn_fst.rpow_const
      (fun p hp => Or.inl (ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1))
  · exact (Real.continuous_cos.comp continuous_snd).continuousOn

/-! ## The cut-off test functions -/

/-- The cut-off test function `ρ(z)·(χ_n(θ)·e_m(θ))`. -/
def modeTest (m : ℕ) (ρ : ℝ → ℝ) (n : ℕ) : ℝ → ℝ → ℝ :=
  fun z θ => ρ z * (angCut n θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)

@[simp] lemma modeTest_apply (m n : ℕ) (ρ : ℝ → ℝ) (z θ : ℝ) :
    modeTest m ρ n z θ = ρ z * (angCut n θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ) := rfl

lemma modeTest_uncurry (m n : ℕ) (ρ : ℝ → ℝ) :
    Function.uncurry (modeTest m ρ n)
      = fun p : ℝ × ℝ => ρ p.1
          * (angCut n p.2 * Work.FTS.PhiStar.Gegenbauer.eFam m p.2) := rfl

theorem modeTest_contDiff {m n : ℕ} {ρ : ℝ → ℝ} (hρ : ∀ k : ℕ, ContDiff ℝ k ρ)
    (hCut : CutFacts m) : ∀ k : ℕ, ContDiff ℝ k (Function.uncurry (modeTest m ρ n)) := by
  intro k
  rw [modeTest_uncurry]
  exact ((hρ k).comp contDiff_fst).mul
    (((hCut.1 n k).comp contDiff_snd).mul
      ((Work.FTS.ClassC.contDiff_eFam_nat m k).comp contDiff_snd))

theorem modeTest_hasCompactSupport {m n : ℕ} {ρ : ℝ → ℝ} (hρc : HasCompactSupport ρ)
    (hCut : CutFacts m) : HasCompactSupport (Function.uncurry (modeTest m ρ n)) := by
  rw [modeTest_uncurry]
  refine HasCompactSupport.of_support_subset_isCompact
    (K := tsupport ρ ×ˢ Set.Icc (delta n) (π / 2 - delta n))
    (hρc.isCompact.prod isCompact_Icc) ?_
  intro p hp
  have hmem : Function.uncurry (modeTest m ρ n) p ≠ 0 := Function.mem_support.mp hp
  have hρp : ρ p.1 ≠ 0 := fun h => hmem (by simp only [modeTest_uncurry, h, zero_mul, mul_zero])
  have hχp : angCut n p.2 ≠ 0 := fun h => hmem (by simp only [modeTest_uncurry, h, zero_mul, mul_zero])
  exact ⟨subset_tsupport _ (Function.mem_support.mpr hρp),
    hCut.tsupport_subset n (subset_tsupport _ (Function.mem_support.mpr hχp))⟩

theorem modeTest_tsupport_subset_Q0 {m n : ℕ} {ρ : ℝ → ℝ} (hρs : tsupport ρ ⊆ Set.Ioi 0)
    (hCut : CutFacts m) :
    tsupport (Function.uncurry (modeTest m ρ n)) ⊆ Work.FTS.EllipticEst.Q0 := by
  have hsupp : Function.support (Function.uncurry (modeTest m ρ n))
      ⊆ tsupport ρ ×ˢ tsupport (angCut n) := by
    intro p hp
    have hmem : Function.uncurry (modeTest m ρ n) p ≠ 0 := Function.mem_support.mp hp
    have hρp : ρ p.1 ≠ 0 := fun h => hmem (by simp only [modeTest_uncurry, h, zero_mul, mul_zero])
    have hχp : angCut n p.2 ≠ 0 := fun h => hmem (by simp only [modeTest_uncurry, h, zero_mul, mul_zero])
    exact ⟨subset_tsupport _ (Function.mem_support.mpr hρp),
      subset_tsupport _ (Function.mem_support.mpr hχp)⟩
  have hclosed : IsClosed (tsupport ρ ×ˢ tsupport (angCut n)) :=
    IsClosed.prod (isClosed_tsupport _) (isClosed_tsupport _)
  refine (closure_minimal hsupp hclosed).trans ?_
  intro p hp
  refine Work.FTS.EllipticEst.mem_Q0.mpr ⟨hρs hp.1, ?_, ?_⟩
  · exact lt_of_lt_of_le (hCut.delta_pos n) (hCut.tsupport_subset n hp.2).1
  · exact lt_of_le_of_lt (hCut.tsupport_subset n hp.2).2
      (by linarith [hCut.delta_pos n] : π / 2 - delta n < π / 2)


/-! ## The algebra of the cut-off difference -/

/-- The commutator of the angular operator with the cut-off. -/
def comm (m n : ℕ) (θ : ℝ) : ℝ :=
  Work.FTS.EllipticEst.Lzero1 (fun t => angCut n t * Work.FTS.PhiStar.Gegenbauer.eFam m t) θ
    - angCut n θ * Work.FTS.EllipticEst.Lzero1 (Work.FTS.PhiStar.Gegenbauer.eFam m) θ

/-- `bslOp` on the pure mode `ρ ⊗ e_m`. -/
lemma bslOp_sepMode {α : ℝ} {ρ : ℝ → ℝ} {m : ℕ} {z θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    Work.Elliptic.bslOp α (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) z θ
      = (Work.FTS.PhiStar.Gegenbauer.lam m * ρ z - radOp α ρ z)
          * Work.FTS.PhiStar.Gegenbauer.eFam m θ := by
  rw [Work.FTS.PhiStar.bslOp_sep, Lzero1_eFam m hcos, radOp]
  have hiter : iteratedDeriv 2 ρ z = deriv (deriv ρ) z := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  rw [hiter]
  ring

/-- `bslOp` on the cut-off test function splits as `χ_n·bslOp Ψ + ρ·comm_n`. -/
lemma bslOp_modeTest {α : ℝ} {ρ : ℝ → ℝ} {m n : ℕ} {z θ : ℝ} (hcos : Real.cos θ ≠ 0) :
    Work.Elliptic.bslOp α (modeTest m ρ n) z θ
      = angCut n θ * Work.Elliptic.bslOp α
          (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) z θ
        + ρ z * comm m n θ := by
  change Work.Elliptic.bslOp α
      (fun z θ => ρ z * (angCut n θ * Work.FTS.PhiStar.Gegenbauer.eFam m θ)) z θ
      = angCut n θ * Work.Elliptic.bslOp α
          (fun z θ => ρ z * Work.FTS.PhiStar.Gegenbauer.eFam m θ) z θ
        + ρ z * comm m n θ
  rw [Work.FTS.PhiStar.bslOp_sep, Work.FTS.PhiStar.bslOp_sep]
  have hiter : iteratedDeriv 2 ρ z = deriv (deriv ρ) z := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  simp only [comm, hiter]
  ring

/-! ## Bounds -/

/-- `|ρ|` is bounded by a constant times the indicator of a box containing its support. -/
theorem exists_bound_abs_rho {ρ : ℝ → ℝ} (hρ : ∀ k : ℕ, ContDiff ℝ k ρ) {a b : ℝ}
    (hsub : tsupport ρ ⊆ Set.Icc a b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, |ρ z| ≤ C * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    ((hρ 0).continuous.continuousOn (s := Set.Icc a b))
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  by_cases hz : z ∈ Set.Icc a b
  · have h1 : |ρ z| ≤ C := by
      have h2 := hC z hz
      rwa [Real.norm_eq_abs] at h2
    rw [Set.indicator_of_mem hz, mul_one]
    exact h1.trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem hz, mul_zero,
      image_eq_zero_of_notMem_tsupport (fun h => hz (hsub h)), abs_zero]

/-- The weight `z^((5-α)/α)·cos θ` is bounded on a compact box of radii. -/
theorem exists_bound_bslWeight {α : ℝ} {a b : ℝ} (ha : 0 < a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : ℝ × ℝ, p.1 ∈ Set.Icc a b → |bslWeight α p| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_id.rpow_const (fun z hz =>
      Or.inl (ne_of_gt (lt_of_lt_of_le ha hz.1))))
  refine ⟨max C 0, le_max_right _ _, fun p hp => ?_⟩
  have h1 : |p.1 ^ ((5 - α) / α)| ≤ C := by
    have h2 := hC p.1 hp
    rwa [Real.norm_eq_abs] at h2
  calc |bslWeight α p| = |p.1 ^ ((5 - α) / α)| * |Real.cos p.2| := by rw [bslWeight, abs_mul]
    _ ≤ max C 0 * 1 := mul_le_mul (h1.trans (le_max_left _ _)) (Real.abs_cos_le_one p.2)
        (abs_nonneg _) (le_max_right _ _)
    _ = max C 0 := mul_one _

end Work.FTS.StrongEps.EComparison
