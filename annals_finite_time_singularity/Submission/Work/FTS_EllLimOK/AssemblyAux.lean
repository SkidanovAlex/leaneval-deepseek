/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.AssemblyAux` — the vocabulary and the local lemmas of the `ClosedCompact` assembly

This module collects what the assembly of `ClosedCompact_of_localBound` needs *before* the two
analytic inputs (the Arzelà–Ascoli extraction and the passing of the elliptic equation to the
limit) are used:

* `lhsfun` — the expression of `bslOp α Ψ` through the tower entries `F c d = D_z^c D_θ^d Ψ`
  (the shape of the sibling module `BslOp_tower`);
* `LimInputs` — the six analytic inputs, isolated as the fields of a structure so that the
  assembly can be checked independently of the modules proving them;
* the locality of the iterated operators `D_θ^i`, `D_z^j`, `mixed j i` on open sets;
* `decay_of_wt_bound` — the growth bound of `LocalBound` (with its `1/(1+z)` far-field factor)
  forces the decay `Ψ → 0` at `z → ∞`;
* `tendsto_lhsfun` — `lhsfun` is continuous in its five tower entries, i.e. the formula for
  `bslOp` passes to pointwise limits of the jets (the engine of the limit equation).

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS_EllLimOK.LimDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The right-hand side of the tower formula for `bslOp` -/

/-- The expression for `bslOp α Ψ` in terms of the tower entries `F c d = D_z^c D_θ^d Ψ`
(`c + d ≤ 2`): the content of `BslOp_tower`. -/
def lhsfun (α : ℝ) (F : ℕ → ℕ → ℝ → ℝ → ℝ) (z θ : ℝ) : ℝ :=
  -(α ^ 2) * (F 2 0 z θ - F 1 0 z θ) - (α * (5 + α)) * F 1 0 z θ
    - (F 0 2 z θ - 2 * Real.cos (2 * θ) * F 0 1 z θ) / (Real.sin (2 * θ)) ^ 2
    + Real.tan θ * (F 0 1 z θ / Real.sin (2 * θ))
    + (Real.tan θ ^ 2 - 5) * F 0 0 z θ

/-! ## The six analytic inputs -/

/-- The six analytic inputs of the assembly, in the shape in which the sibling modules prove them.
(Fields: uniform bounds/equicontinuity of the order-`≤ 2` jet family from `LocalBound`; the tower
relations of the limits; the tower relations of a single smooth function; the identification of the
limits with the mixed derivatives of the bottom entry; `C²` of the bottom entry; the `bslOp`-formula
in terms of the tower.) -/
structure LimInputs : Prop where
  /-- Uniform boundedness and uniform equicontinuity of the six order-`≤ 2` jets on compacta. -/
  extract : ∀ {C : ℝ} {G : ℕ → ℝ → ℝ → ℝ},
    (∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n)) →
    (∀ (n : ℕ) (j i : ℕ), j + i ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      |Work.Spaces.mixed j i (G n) z θ| ≤ C * wt z θ) →
    (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 → ∃ C' : ℝ,
        ∀ (n : ℕ) (p : ℝ × ℝ), p ∈ K → ‖fam6 G n p‖ ≤ C') ∧
      (∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 → ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ) (p : ℝ × ℝ), p ∈ K → ∀ q : ℝ × ℝ, q ∈ K →
          dist p q < δ → ‖fam6 G n p - fam6 G n q‖ < ε)
  /-- The tower relations of the limits along a locally uniformly convergent jet family. -/
  tower : ∀ {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} {F : ℕ → ℕ → ℝ → ℝ → ℝ},
    (∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n)) →
    (∀ (c d : ℕ), c + d ≤ 2 → TendstoLocallyUniformlyOn
      (fun n p => Work.Spaces.mixed c d (G (φ n)) p.1 p.2)
      (fun p => F c d p.1 p.2) Filter.atTop Work.FTS.EllipticEst.Q0) →
    (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z) ∧
      (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ)
  /-- The tower relations of a single smooth function. -/
  smoothTower : ∀ {G : ℝ → ℝ → ℝ}, Work.FTS.EllipticEst.SmoothOpen G →
    (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun z' : ℝ => Work.Spaces.mixed c d G z' θ)
          (Work.Spaces.mixed (c + 1) d G z θ / z) z) ∧
      (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        HasDerivAt (fun θ' : ℝ => Work.Spaces.mixed c d G z θ')
          (Work.Spaces.mixed c (d + 1) G z θ / Real.sin (2 * θ)) θ)
  /-- The identification of the tower entries with the mixed derivatives of the bottom entry. -/
  identify : ∀ {F : ℕ → ℕ → ℝ → ℝ → ℝ},
    (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z) →
    (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ) →
    ∀ (c d : ℕ), c + d ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      F c d z θ = Work.Spaces.mixed c d (F 0 0) z θ
  /-- `C²` of the bottom entry of the tower. -/
  c2 : ∀ {F : ℕ → ℕ → ℝ → ℝ → ℝ},
    (∀ (c d : ℕ), c + d ≤ 2 → ContinuousOn (fun p : ℝ × ℝ => F c d p.1 p.2)
      Work.FTS.EllipticEst.Q0) →
    (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z) →
    (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ) →
    ContDiffOn ℝ 2 (Function.uncurry (F 0 0)) Work.FTS.EllipticEst.Q0
  /-- The formula for `bslOp` in terms of the tower. -/
  bsl : ∀ (α : ℝ) {Ψ : ℝ → ℝ → ℝ} {F : ℕ → ℕ → ℝ → ℝ → ℝ},
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 → Ψ z θ = F 0 0 z θ) →
    (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z) →
    (∀ (c d : ℕ), c + d ≤ 1 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ) →
    ∀ {z θ : ℝ}, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      Work.Elliptic.bslOp α Ψ z θ = lhsfun α F z θ

/-! ## Locality of the iterated operators -/

lemma DthIter_congrOn_Q0 {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DthIter i f))
      (Function.uncurry (Work.Spaces.DthIter i g)) V := by
  induction i with
  | zero => exact h
  | succ i ih =>
    intro p hp
    show Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter i f) p.1 p.2
        = Real.sin (2 * p.2) * Work.Spaces.pth (Work.Spaces.DthIter i g) p.1 p.2
    rw [Work.Spaces.pth_congr_of_isOpen hV ih hp]

lemma DzIter_congrOn_Q0 {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (j : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.DzIter j f))
      (Function.uncurry (Work.Spaces.DzIter j g)) V := by
  induction j with
  | zero => exact h
  | succ j ih =>
    intro p hp
    show p.1 * Work.Spaces.pz (Work.Spaces.DzIter j f) p.1 p.2
        = p.1 * Work.Spaces.pz (Work.Spaces.DzIter j g) p.1 p.2
    rw [Work.Spaces.pz_congr_of_isOpen hV ih hp]

lemma mixed_congrOn_Q0 {f g : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry f) (Function.uncurry g) V) (j i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.mixed j i f))
      (Function.uncurry (Work.Spaces.mixed j i g)) V := by
  intro p hp
  have h1 : Set.EqOn (Function.uncurry (Work.Spaces.DthIter i f))
      (Function.uncurry (Work.Spaces.DthIter i g)) V := DthIter_congrOn_Q0 hV h i
  have h2 := DzIter_congrOn_Q0 hV h1 j hp
  simpa only [Work.Spaces.mixed] using h2

/-! ## Decay from the growth bound -/

/-- The growth bound of `LocalBound` (with the far-field factor `1/(1+z)`) forces `u → 0` at
`z → ∞`, for any `u` bounded by `C · wt`. -/
lemma decay_of_wt_bound {C θ : ℝ} (hC : 0 ≤ C) (hθ0 : 0 < θ) (hθ1 : θ < π / 2)
    {u : ℝ → ℝ} (hbd : ∀ z, 0 < z → |u z| ≤ C * wt z θ) :
    Tendsto u Filter.atTop (𝓝 0) := by
  have hKpos : 0 < 1 / (θ * (π / 2 - θ)) := one_div_pos.mpr (mul_pos hθ0 (by linarith))
  have hKnn : 0 ≤ 1 / (θ * (π / 2 - θ)) := le_of_lt hKpos
  rw [tendsto_atTop_nhds]
  intro U h0U hUo
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hUo.mem_nhds h0U)
  refine ⟨max 1 (C * (2 + 1 / (θ * (π / 2 - θ))) / ε + 1), fun z hz => hball ?_⟩
  have hz1 : (1 : ℝ) ≤ z := le_trans (le_max_left _ _) hz
  have hzpos : 0 < z := lt_of_lt_of_le one_pos hz1
  have hzbig : C * (2 + 1 / (θ * (π / 2 - θ))) / ε < z := by
    have h' := le_trans (le_max_right _ _) hz
    linarith
  have h1 : |u z| ≤ C * wt z θ := hbd z hzpos
  have h2 : C * wt z θ ≤ C * (2 + 1 / (θ * (π / 2 - θ))) / z := by
    have hstep : 1 + 1 / z + 1 / (θ * (π / 2 - θ)) ≤ 2 + 1 / (θ * (π / 2 - θ)) := by
      have hz1' : 1 / z ≤ 1 := by
        rw [div_le_one hzpos]
        linarith
      linarith
    calc C * wt z θ = C * ((1 + 1 / z + 1 / (θ * (π / 2 - θ))) / (1 + z)) := by rw [wt]
      _ ≤ C * ((2 + 1 / (θ * (π / 2 - θ))) / (1 + z)) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hstep (by linarith)) hC
      _ = C * (2 + 1 / (θ * (π / 2 - θ))) / (1 + z) := by rw [mul_div_assoc]
      _ ≤ C * (2 + 1 / (θ * (π / 2 - θ))) / z :=
          div_le_div_of_nonneg_left (mul_nonneg hC (by linarith)) hzpos (by linarith)
  have h3 : C * (2 + 1 / (θ * (π / 2 - θ))) / z < ε := by
    rw [div_lt_iff₀ hzpos]
    rw [div_lt_iff₀ hε] at hzbig
    linarith
  rw [Metric.mem_ball, Real.dist_eq, sub_zero]
  exact lt_of_le_of_lt (le_trans h1 h2) h3

/-! ## The limit of the tower formula -/

/-- `lhsfun` is continuous in its five tower entries: the formula of `BslOp_tower` passes to
pointwise limits of the jets.  The tower `F n` is the jet tower of the `n`-th member of a sequence,
`G` the tower of the limit. -/
lemma tendsto_lhsfun {α : ℝ} {F : ℕ → ℕ → ℕ → ℝ → ℝ → ℝ} {G : ℕ → ℕ → ℝ → ℝ → ℝ} {z θ : ℝ}
    (h20 : Tendsto (fun n => F n 2 0 z θ) Filter.atTop (𝓝 (G 2 0 z θ)))
    (h10 : Tendsto (fun n => F n 1 0 z θ) Filter.atTop (𝓝 (G 1 0 z θ)))
    (h02 : Tendsto (fun n => F n 0 2 z θ) Filter.atTop (𝓝 (G 0 2 z θ)))
    (h01 : Tendsto (fun n => F n 0 1 z θ) Filter.atTop (𝓝 (G 0 1 z θ)))
    (h00 : Tendsto (fun n => F n 0 0 z θ) Filter.atTop (𝓝 (G 0 0 z θ))) :
    Tendsto (fun n => lhsfun α (F n) z θ) Filter.atTop (𝓝 (lhsfun α G z θ)) := by
  simp only [lhsfun]
  exact ((((((h20.sub h10).const_mul (-(α ^ 2))).sub
    (h10.const_mul (α * (5 + α)))).sub
    (((h02.sub (h01.const_mul (2 * Real.cos (2 * θ)))).div_const
      ((Real.sin (2 * θ)) ^ 2)))).add
    ((h01.div_const (Real.sin (2 * θ))).const_mul (Real.tan θ))).add
    (h00.const_mul (Real.tan θ ^ 2 - 5)))

end Work.FTS_EllLimOK
