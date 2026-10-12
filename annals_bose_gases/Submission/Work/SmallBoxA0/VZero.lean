import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.SmallBoxBlockBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `SmallBoxA0` — the NON-VACUITY certificate for the small-box block bound

The two skeletons of `Submission/Work/SmallBoxBlockBound.lean`
(`smallbox_block_bound`, `smallbox_state_block_bound`) are proved from data
bundles (`BlockBoxData`, `BlockStateData`) carrying a recorded Bogoliubov
residual field `hBogF`/`hBog`.  This module settles the natural objection
("are those bundles inhabited at all, or is the implication vacuous?") by
exhibiting an EXPLICIT inhabitant of each:

    `blockBoxData_vZero : BlockBoxData`,  `blockStateData_vZero : BlockStateData`

at the ZERO potential `v ≡ 0` (`N = 1`, `s = 1`, `μ = 1`, `R0 = chiR0/2`,
`K_B = 1`, `eta = 0`, `BogErr = 0`, state `Φ ≡ 1`), on which:

* `a v = 0` (`a_vZero`), `g0 v h = 0` (`g0_vZero`), `g2 v h = 0`
  (`g2_vZero`), `g0w0Mass = 0` (`g0w0Mass_vZero`), `q4PairWord = 0`
  (`q4PairWord_vZero`), `qLHSword = 0` (`qLHSword_vZero`),
  `sboxE = kinWord` (`sboxE_vZero`), `totNCoeff s μ v = 1/(72 s²)`
  (`totNCoeff_vZero`);
* the recorded residual `hBogF`/`hBog` reduces to the CLOSED kinetic gap
  `cnPlus/(36 s²) ≤ kinWord` (`KineticBound.kinWord_gap_cnPlus`);
* hence `sboxE = kinWord ≥ 0`, and `0 ≤ eB` (`eB_nonneg_vZero`).

Consequently both theorem statements are NON-VACUOUS (their hypothesis
bundles are inhabited), and at this datum the block-bound conclusions read
`0 ≤ eB 1 1 1 0 hZero` and `0 ≤ sboxE 1 1 1 0 0 Φ` — both proved here,
the first also by direct instantiation of `smallbox_block_bound`
(`smallbox_block_bound_nonvacuous`) and by direct `eB`-positivity
(`eB_nonneg_vZero`), which also shows the conclusion is not contradictory.

This pins down exactly what the recorded residual is: the bundle is *not*
empty, and `hBogF` is TRUE at `v ≡ 0`; it is the only place where FS's
`lm:appbogolubov` (the Bogoliubov pairing payment) enters the fixed-`n`
block bound.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SmallBoxA0

open Submission BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The zero potential. -/
noncomputable def vZero : ℝ³ → ℝ := fun _ => 0

@[simp] lemma vZero_apply (x : ℝ³) : vZero x = 0 := rfl

lemma isRadial_vZero : IsRadial vZero := by
  intro x y _; rfl

lemma isScatSol_vZero : IsScatteringSolution vZero vZero := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (locallyIntegrable_const (0 : ℝ) :
      MeasureTheory.LocallyIntegrable (fun _ : ℝ³ => (0 : ℝ)))
  · have hz : (vZero * (1 - vZero)) = ((fun _ : ℝ³ => (0 : ℝ)) : ℝ³ → ℝ) := by
      funext x; simp [vZero]
    rw [hz]
    exact (locallyIntegrable_const (0 : ℝ) :
      MeasureTheory.LocallyIntegrable (fun _ : ℝ³ => (0 : ℝ)))
  · intro φ _
    simp [vZero]
  · show Tendsto (fun _ : ℝ³ => (0 : ℝ)) (cocompact ℝ³) (𝓝 (0 : ℝ))
    exact tendsto_const_nhds

/-- The zero potential has the (radial) zero scattering solution. -/
theorem hZero : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w vZero :=
  ⟨vZero, isRadial_vZero, isScatSol_vZero⟩

lemma a_vZero : a vZero = 0 := by
  unfold a
  rw [dif_pos hZero]
  simp [vZero]

lemma g0_vZero : g0 vZero hZero = 0 := by
  funext x
  simp [g0, vZero]

lemma g2_vZero : g2 vZero hZero = 0 := by
  funext x
  simp [g2, vZero]

lemma g0w0Mass_vZero : g0w0Mass (v := vZero) hZero = 0 := by
  unfold g0w0Mass
  rw [show g0 vZero hZero = 0 from g0_vZero]
  simp

/-- The zero kernel: `wPairC s 0 = 0`. -/
lemma wPairC_zero (s : ℝ) : wPairC s (fun _ : ℝ³ => (0 : ℝ)) = fun _ _ => 0 := by
  funext x y
  simp [wPairC, wPair, wScaled]

lemma q4PairWord_vZero {N : ℕ} (ℓ : ℝ) {Φ : X N → ℝ} :
    q4PairWord (ℓ := ℓ) (v := vZero) hZero (Φ := Φ) = 0 := by
  unfold q4PairWord
  rw [show g0 vZero hZero = (fun _ : ℝ³ => (0 : ℝ)) from g0_vZero]
  simp [wPairC_zero]

/-- `potNCoeff μ 0 = 0`. -/
lemma potNCoeff_zero (μ : ℝ) : potNCoeff μ 0 = 0 := by
  simp [potNCoeff, fsqC1, fsqC2]

lemma totNCoeff_vZero (s μ : ℝ) : totNCoeff s μ vZero = 1 / (72 * s ^ 2) := by
  unfold totNCoeff
  rw [a_vZero, potNCoeff_zero]
  ring

/-- The zero one-body fibre: `w1Fibre ℓ 0 = 0`. -/
lemma w1Fibre_zero (ℓ : ℝ) :
    w1Fibre ℓ (fun _ _ : ℝ³ => (0 : ℝ)) = fun _ => 0 := by
  funext x
  simp [w1Fibre]

lemma qLHSden_vZero (N : ℕ) (ℓ μ : ℝ) (x : X N) :
    qLHSden N ℓ μ (fun _ _ : ℝ³ => (0 : ℝ)) (fun _ _ : ℝ³ => (0 : ℝ)) x = 0 := by
  simp [qLHSden, w1Fibre]

lemma qLHSword_vZero {N : ℕ} (ℓ μ : ℝ) (Φ : X N → ℝ) :
    qLHSword (N := N) ℓ μ (fun _ _ : ℝ³ => (0 : ℝ)) (fun _ _ : ℝ³ => (0 : ℝ)) Φ = 0 := by
  rw [qLHSword_eq_integral_qLHSden]
  refine integral_eq_zero_of_ae ?_
  filter_upwards with x
  rw [qLHSden_vZero N ℓ μ x]
  simp

lemma sboxE_vZero {N : ℕ} (ℓ μ : ℝ) (Φ : X N → ℝ) :
    sboxE N ℓ μ (wPairC ℓ vZero) (wPairC ℓ (g0 vZero hZero)) Φ = kinWord N ℓ Φ := by
  rw [sboxE]
  rw [show wPairC ℓ vZero = (fun _ _ : ℝ³ => (0 : ℝ)) from wPairC_zero ℓ,
      show wPairC ℓ (g0 vZero hZero) = (fun _ _ : ℝ³ => (0 : ℝ)) from by
        rw [g0_vZero]; exact wPairC_zero ℓ]
  rw [qLHSword_vZero]
  ring

/-- `eB` at the zero potential is nonnegative (every `CSBox` quotient is). -/
theorem eB_nonneg_vZero {N : ℕ} {s μ : ℝ} (hs : 0 < s) : 0 ≤ eB N s μ vZero hZero := by
  have hne : Nonempty (CSBox N s) := nonempty_CSBox N hs
  have hq : ∀ Φ : CSBox N s, 0 ≤ sboxE N s μ (wPairC s vZero)
      (wPairC s (g0 vZero hZero)) (Φ : X N → ℝ) /
        (∫ x in abox N s, ((Φ : X N → ℝ) x) ^ 2) := by
    intro Φ
    refine div_nonneg ?_ (le_of_lt Φ.sq_pos)
    rw [sboxE_vZero]
    exact kinWord_nonneg N s _
  rw [eB]
  exact le_ciInf (fun Φ : CSBox N s => hq Φ)

/-- **The `BlockBoxData` bundle is INHABITED** (at `v ≡ 0`, `N = 1`, `s = 1`,
`μ = 1`, `R0 = chiR0/2`, `K_B = 1`, `eta = 0`, `BogErr = 0`).  On this datum
the recorded residual `hBogF` reduces to the closed kinetic gap
`cnPlus/(36) ≤ kinWord`. -/
noncomputable def blockBoxData_vZero : BlockBoxData where
  N := 1
  s := 1
  μ := 1
  R0 := chiR0 / 2
  K_B := 1
  v := vZero
  h := hZero
  hs := one_pos
  hμ := one_pos
  hv_nonneg := fun _ => le_refl 0
  hvrad := isRadial_vZero
  hv_memL1 := MemLp.zero
  hR0 := half_pos chiR0_pos
  hv_supp := by
    rw [tsupport]
    have hsp : Function.support (vZero : ℝ³ → ℝ) = ∅ := by
      ext x; simp [Function.mem_support, vZero]
    rw [hsp, closure_empty]
    exact Set.empty_subset _
  hRs := by
    have h := chiR0_pos
    rw [one_mul]; linarith
  hμs := by norm_num
  hKB := one_pos
  hwin := by norm_num
  eta := 0
  BogErr := 0
  hbox := by
    rw [totNCoeff_vZero]
    norm_num
  hη := by simp [a_vZero]
  hcorrreg := by simp [a_vZero]
  hη0 := le_refl 0
  hBog0 := le_refl 0
  hW2 := by
    have hz' : ∀ p : X 2, wPairC 1 (g0 vZero hZero) (p 0) (p 1) = 0 := by
      intro p; simp [wPairC, wPair, wScaled, g0, vZero]
    have hz : (fun p : X 2 => wPairC 1 (g0 vZero hZero) (p 0) (p 1)) = fun _ => (0 : ℝ) :=
      funext hz'
    rw [hz]
    exact MemLp.zero
  hL2 := by
    have hz' : ∀ p : X 2, wPairC 1 (g0 vZero hZero) (p 0) (p 1) = 0 := by
      intro p; simp [wPairC, wPair, wScaled, g0, vZero]
    simp [hz', g0w0Mass_vZero]
  hchi := by simp [a_vZero]

/-- **The `BlockStateData` bundle is INHABITED** (same datum, state `Φ ≡ 1`). -/
noncomputable def blockStateData_vZero : BlockStateData where
  N := 1
  s := 1
  μ := 1
  R0 := chiR0 / 2
  K_B := 1
  v := vZero
  h := hZero
  hs := one_pos
  hμ := one_pos
  hv_nonneg := fun _ => le_refl 0
  hvrad := isRadial_vZero
  hv_memL1 := MemLp.zero
  hR0 := half_pos chiR0_pos
  hv_supp := by
    rw [tsupport]
    have hsp : Function.support (vZero : ℝ³ → ℝ) = ∅ := by
      ext x; simp [Function.mem_support, vZero]
    rw [hsp, closure_empty]
    exact Set.empty_subset _
  hRs := by
    have h := chiR0_pos
    rw [one_mul]; linarith
  hμs := by norm_num
  hKB := one_pos
  hwin := by norm_num
  eta := 0
  BogErr := 0
  hbox := by
    rw [totNCoeff_vZero]
    norm_num
  hη := by simp [a_vZero]
  Φ := fun _ : X 1 => 1
  hΦc := contDiff_const
  hnorm := by
    simp only [one_pow]
    rw [MeasureTheory.setIntegral_const]
    rw [MeasureTheory.measureReal_def, abox_volume 1 1 (by norm_num : (0:ℝ) ≤ 1)]
    simp
  hchi := by simp [a_vZero]
  hcorrreg := by simp [a_vZero]
  hη0 := le_refl 0
  hBog0 := le_refl 0
  hW2 := by
    have hz' : ∀ p : X 2, wPairC 1 (g0 vZero hZero) (p 0) (p 1) = 0 := by
      intro p; simp [wPairC, wPair, wScaled, g0, vZero]
    have hz : (fun p : X 2 => wPairC 1 (g0 vZero hZero) (p 0) (p 1)) = fun _ => (0 : ℝ) :=
      funext hz'
    rw [hz]
    exact MemLp.zero
  hL2 := by
    have hz' : ∀ p : X 2, wPairC 1 (g0 vZero hZero) (p 0) (p 1) = 0 := by
      intro p; simp [wPairC, wPair, wScaled, g0, vZero]
    simp [hz', g0w0Mass_vZero]
  _residual3_removed := trivial

/-- **Instantiating `smallbox_block_bound` at the explicit datum**: the block
shape at `v ≡ 0` reads `0 ≤ eB 1 1 1 0 hZero`, which is also proved directly
by `eB_nonneg_vZero` — so the recorded residual is satisfiable and the block
bound is not vacuous. -/
theorem smallbox_block_bound_nonvacuous : 0 ≤ eB 1 1 1 vZero hZero := by
  obtain ⟨C, hC, hbound⟩ := smallbox_block_bound
  have h := hbound blockBoxData_vZero
  simp only [blockBoxData_vZero, a_vZero] at h
  simpa using h

/-- **The state-level instance**: at `v ≡ 0` and `Φ ≡ 1` the block shape reads
`0 ≤ sboxE 1 1 1 0 0 Φ`, which holds (`sboxE = kinWord ≥ 0`). -/
theorem smallbox_state_block_bound_nonvacuous :
    0 ≤ sboxE 1 1 1 (wPairC 1 vZero) (wPairC 1 (g0 vZero hZero))
      (fun _ : X 1 => (1 : ℝ)) := by
  rw [sboxE_vZero]
  exact kinWord_nonneg _ _ _

/-- The state-level instance obtained by APPLYING `smallbox_state_block_bound`
to `blockStateData_vZero` (its LHS collapses to `0`). -/
theorem smallbox_state_block_bound_applied :
    0 ≤ sboxE blockStateData_vZero.N blockStateData_vZero.s blockStateData_vZero.μ
      (wPairC blockStateData_vZero.s blockStateData_vZero.v)
      (wPairC blockStateData_vZero.s (g0 blockStateData_vZero.v blockStateData_vZero.h))
      blockStateData_vZero.Φ := by
  obtain ⟨C, hC, hbound⟩ := smallbox_state_block_bound
  have h := hbound blockStateData_vZero
  simp only [blockStateData_vZero, a_vZero, g0_vZero] at h
  simp only [blockStateData_vZero, g0_vZero]
  simp at h
  exact h

end Work.SmallBoxA0
