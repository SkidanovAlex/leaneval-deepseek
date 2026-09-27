import Mathlib
import Submission.Work.Drive.collapseTransport
import Submission.Work.Drive.odd_ncard_loopFamMeet_iff

/-!
# T5 of the radial-collapse transport: the diameter loop and the core loop have the same parity

The radial collapse (`Submission/Work/Drive/collapseTransport.lean`) computes the transport
`n_P ≡ ε_Q · ε_R` (Hugelmeyer's Lemma 2) of the chain route.  At the collapsed end `s = 1` the
collapsed plane is the *core loop*, and the radial fibre over a core point is a **diameter** of the
sheet; the last analytic step of the transport is therefore the comparison of the parity of

* `diamMeet Q t W` — the meets of the **diameter loop** `σ ↦ (1 - 2σ) · e^{iπt}` with the chain `W`,
* `arcMeet Q t W` — the meets of the **half-circle loop** `σ ↦ e^{iπ(t+σ)}` with `W`,
* `coreMeet Q c P` — the meets of the **core loop** `σ ↦ e^{iπσ}` with the clamped sweep of the
  plane presentation `P`,

which the lead's design writes as two applications of the proved loop-deformation engine
`Work.Drive.odd_ncard_loopFamMeet_iff`.

This file delivers both, *with the two deformation families made explicit*:

* `diamFam Q t p = diamInterp Q t (p 0) (p 1)` — the straight-line interpolation from the diameter
  loop (the slice `p 0 = 0`) to the half-circle loop (the slice `p 0 = 1`);
* `arcFam Q t p = arcRot Q t (p 0) (p 1)` — the rotation of the half-circle loop, from the angle `t`
  (the slice `p 0 = 0`) to the angle `0` (the slice `p 0 = 1`).

For both families the engine's *closedness* clause `hloop` is **not** an extra hypothesis: it is the
chart's seam clause `Q (-z) = Q z` on the unit circle (`diamInterp_loop`, `arcRot_loop`).  What remains
is the engine's stock regularity data (`hseam` the seam invariance of the chain, `havoid` the
avoidance of the two slice faces of the chain, `htrans` the transversality of the meet, `hface` the
one-face crossing at a boundary meet), transcribed for the two concrete families — this is exactly the
form the lead's design asks for, and it is what the admissibility (chart-shift / `linCapping`
perturbation of the sweeps) has to supply downstream.

## The two identifications of the meet sets

`loopFamMeet L W t` is the meet set of the family `L` at the *family parameter* `t` with the chain
`W`; for our two families the parameter is the first square coordinate, so the bijection
`p ↦ (p.1 1, p.2)` identifies the `0`- and `1`-slices with the concrete meet sets:

| slice | `diamFam` | `arcFam` |
| ----- | --------- | -------- |
| `p 0 = 0` | `diamMeet Q t W` | `arcMeet Q t W` |
| `p 0 = 1` | `arcMeet Q t W`  | `arcMeet Q 0 W = coreMeet Q c P` |

the last entry by `Work.Drive.arcMeet_zero_eq_coreMeet`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

noncomputable section

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace

/-! ## The two families -/

/-- **The diameter-to-half-circle family**: the straight-line interpolation `diamInterp` of the two
loops, as a map on the square (first coordinate = interpolation parameter, second = loop parameter). -/
def diamFam (Q : ℂ → CappingSpace) (t : ℝ) : EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  fun p => diamInterp Q t (p 0) (p 1)

/-- **The rotation family**: `arcRot Q t`, as a map on the square. -/
def arcFam (Q : ℂ → CappingSpace) (t : ℝ) : EuclideanSpace ℝ (Fin 2) → CappingSpace :=
  fun p => arcRot Q t (p 0) (p 1)

@[simp] lemma diamFam_mk2 (Q : ℂ → CappingSpace) (t a σ : ℝ) :
    diamFam Q t (mk2 a σ) = diamInterp Q t a σ := rfl

@[simp] lemma arcFam_mk2 (Q : ℂ → CappingSpace) (t a σ : ℝ) :
    arcFam Q t (mk2 a σ) = arcRot Q t a σ := rfl

/-! ## The four slices as the concrete meet sets

All four are `Set.ncard_congr` along `p ↦ (p.1 1, p.2)`; the only content is reading off the
definitions (`diamInterp_zero/_one`, `arcRot_zero/_one`). -/

/-- The `p 0 = 0` slice of the diameter family is the diameter meet. -/
theorem diamMeet_ncard_eq_loopFamMeet_zero (Q : ℂ → CappingSpace) (t : ℝ)
    (W : EuclideanSpace ℝ (Fin 3) → CappingSpace) :
    (diamMeet Q t W).ncard = (loopFamMeet (diamFam Q t) W 0).ncard := by
  refine Set.ncard_congr (fun q _ => (mk2 0 q.1, q.2)) ?_ ?_ ?_
  · intro q hq
    rw [diamMeet, Set.mem_ofPred_eq] at hq
    obtain ⟨hq1, hq2, hq3⟩ := hq
    rw [loopFamMeet, Set.mem_ofPred_eq]
    refine ⟨?_, ?_, hq2, ?_⟩
    · rw [Submission.Drive.unitBox, Set.mem_ofPred_eq]
      intro i
      fin_cases i <;> simp [mk2, hq1]
    · simp [mk2]
    · change diamInterp Q t 0 q.1 = W q.2
      rw [diamInterp_zero]
      exact hq3
  · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ _ _ h
    injection h with h1 h2
    have h3 : x₁ = x₂ := by
      have h4 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) h1
      simpa using h4
    exact Prod.ext h3 h2
  · intro p hp
    rw [loopFamMeet, Set.mem_ofPred_eq] at hp
    obtain ⟨hp1, hp0, hp2, hpe⟩ := hp
    refine ⟨(p.1 1, p.2), ?_, ?_⟩
    · rw [diamMeet, Set.mem_ofPred_eq]
      refine ⟨hp1 1, hp2, ?_⟩
      have he : diamInterp Q t 0 (p.1 1) = W p.2 := by
        rw [← hp0]; exact hpe
      rwa [diamInterp_zero] at he
    · have hpt : mk2 0 (p.1 1) = p.1 := by
        ext i
        fin_cases i <;> simp [mk2, hp0]
      simp [hpt]

/-- The `p 0 = 1` slice of the diameter family is the half-circle meet. -/
theorem loopFamMeet_one_eq_arcMeet (Q : ℂ → CappingSpace) (t : ℝ)
    (W : EuclideanSpace ℝ (Fin 3) → CappingSpace) :
    (loopFamMeet (diamFam Q t) W 1).ncard = (arcMeet Q t W).ncard := by
  refine Set.ncard_congr (fun p _ => (p.1 1, p.2)) ?_ ?_ ?_
  · intro p hp
    rw [loopFamMeet, Set.mem_ofPred_eq] at hp
    obtain ⟨hp1, hp0, hp2, hpe⟩ := hp
    rw [arcMeet, Set.mem_ofPred_eq]
    refine ⟨hp1 1, hp2, ?_⟩
    have he : diamInterp Q t 1 (p.1 1) = W p.2 := by
      rw [← hp0]; exact hpe
    rwa [diamInterp_one] at he
  · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ha₁ ha₂ h
    injection h with h1 h2
    have hx₁ : x₁ 0 = 1 := ha₁.2.1
    have hx₂ : x₂ 0 = 1 := ha₂.2.1
    have h3 : x₁ = x₂ := by
      rw [← mk2_eta x₁, ← mk2_eta x₂]
      have e1 : x₁ 0 = x₂ 0 := by rw [hx₁, hx₂]
      have e2 : x₁ 1 = x₂ 1 := by simpa using h1
      rw [e1, e2]
    exact Prod.ext h3 h2
  · intro q hq
    rw [arcMeet, Set.mem_ofPred_eq] at hq
    obtain ⟨hq1, hq2, hq3⟩ := hq
    refine ⟨(mk2 1 q.1, q.2), ?_, ?_⟩
    · rw [loopFamMeet, Set.mem_ofPred_eq]
      refine ⟨?_, ?_, hq2, ?_⟩
      · rw [Submission.Drive.unitBox, Set.mem_ofPred_eq]
        intro i
        fin_cases i <;> simp [mk2, hq1]
      · simp [mk2]
      · change diamInterp Q t 1 q.1 = W q.2
        rw [diamInterp_one]
        exact hq3
    · simp [mk2]

/-- The `p 0 = 0` slice of the rotation family is the half-circle meet. -/
theorem arcMeet_ncard_eq_loopFamMeet_zero (Q : ℂ → CappingSpace) (t : ℝ)
    (W : EuclideanSpace ℝ (Fin 3) → CappingSpace) :
    (arcMeet Q t W).ncard = (loopFamMeet (arcFam Q t) W 0).ncard := by
  refine Set.ncard_congr (fun q _ => (mk2 0 q.1, q.2)) ?_ ?_ ?_
  · intro q hq
    rw [arcMeet, Set.mem_ofPred_eq] at hq
    obtain ⟨hq1, hq2, hq3⟩ := hq
    rw [loopFamMeet, Set.mem_ofPred_eq]
    refine ⟨?_, ?_, hq2, ?_⟩
    · rw [Submission.Drive.unitBox, Set.mem_ofPred_eq]
      intro i
      fin_cases i <;> simp [mk2, hq1]
    · simp [mk2]
    · change arcRot Q t 0 q.1 = W q.2
      rw [arcRot_zero]
      exact hq3
  · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ _ _ h
    injection h with h1 h2
    have h3 : x₁ = x₂ := by
      have h4 := congrArg (fun z : EuclideanSpace ℝ (Fin 2) => z 1) h1
      simpa using h4
    exact Prod.ext h3 h2
  · intro p hp
    rw [loopFamMeet, Set.mem_ofPred_eq] at hp
    obtain ⟨hp1, hp0, hp2, hpe⟩ := hp
    refine ⟨(p.1 1, p.2), ?_, ?_⟩
    · rw [arcMeet, Set.mem_ofPred_eq]
      refine ⟨hp1 1, hp2, ?_⟩
      have he : arcRot Q t 0 (p.1 1) = W p.2 := by
        rw [← hp0]; exact hpe
      rwa [arcRot_zero] at he
    · have hpt : mk2 0 (p.1 1) = p.1 := by
        ext i
        fin_cases i <;> simp [mk2, hp0]
      simp [hpt]

/-- The `p 0 = 1` slice of the rotation family is the half-circle meet at angle `0`. -/
theorem loopFamMeet_one_eq_arcMeet_zero (Q : ℂ → CappingSpace) (t : ℝ)
    (W : EuclideanSpace ℝ (Fin 3) → CappingSpace) :
    (loopFamMeet (arcFam Q t) W 1).ncard = (arcMeet Q 0 W).ncard := by
  refine Set.ncard_congr (fun p _ => (p.1 1, p.2)) ?_ ?_ ?_
  · intro p hp
    rw [loopFamMeet, Set.mem_ofPred_eq] at hp
    obtain ⟨hp1, hp0, hp2, hpe⟩ := hp
    rw [arcMeet, Set.mem_ofPred_eq]
    refine ⟨hp1 1, hp2, ?_⟩
    have he : arcRot Q t 1 (p.1 1) = W p.2 := by
      rw [← hp0]; exact hpe
    rwa [arcRot_one] at he
  · rintro ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ ha₁ ha₂ h
    injection h with h1 h2
    have hx₁ : x₁ 0 = 1 := ha₁.2.1
    have hx₂ : x₂ 0 = 1 := ha₂.2.1
    have h3 : x₁ = x₂ := by
      rw [← mk2_eta x₁, ← mk2_eta x₂]
      have e1 : x₁ 0 = x₂ 0 := by rw [hx₁, hx₂]
      have e2 : x₁ 1 = x₂ 1 := by simpa using h1
      rw [e1, e2]
    exact Prod.ext h3 h2
  · intro q hq
    rw [arcMeet, Set.mem_ofPred_eq] at hq
    obtain ⟨hq1, hq2, hq3⟩ := hq
    refine ⟨(mk2 1 q.1, q.2), ?_, ?_⟩
    · rw [loopFamMeet, Set.mem_ofPred_eq]
      refine ⟨?_, ?_, hq2, ?_⟩
      · rw [Submission.Drive.unitBox, Set.mem_ofPred_eq]
        intro i
        fin_cases i <;> simp [mk2, hq1]
      · simp [mk2]
      · change arcRot Q t 1 q.1 = W q.2
        rw [arcRot_one]
        exact hq3
    · simp [mk2]

/-! ## The two parity comparisons -/

/-- **T5(a): the diameter meet and the half-circle meet have the same parity.**  The engine is applied
to the explicit interpolation family `diamFam Q t`; its closedness clause is the chart's seam clause.
All the regularity data is carried as the explicit hypotheses `hseam`/`havoid`/`htrans`/`hface`. -/
theorem odd_ncard_diamMeet_iff_arcMeet (Q : ℂ → CappingSpace) (t : ℝ)
    (W : EuclideanSpace ℝ (Fin 3) → CappingSpace)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hL : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (diamFam Q t))
    (hN : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hseam : ∀ x : EuclideanSpace ℝ (Fin 3), onSeam x → W (seamInv x) = W x)
    (havoid : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      diamFam Q t u = W x → x ∈ Submission.Drive.unitBox 2 → (x 2 = 0 ∨ x 2 = 1) → False)
    (htrans : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      diamFam Q t u = W x →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) (diamFam Q t) u).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) W x).toLinearMap = ⊤)
    (hface : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      diamFam Q t u = W x →
      u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
      (u ∈ Submission.Drive.unitBoxBdry 1 ∨ x ∈ Submission.Drive.unitBoxBdry 2) →
      (∃ i : Fin 2, (u i = 0 ∨ u i = 1) ∧ (∀ j : Fin 2, j ≠ i → u j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) (diamFam Q t) u σ = mfderiv (𝓡 3) (𝓡 4) W x τ ∧ σ i ≠ 0)
        ∨ (∃ j : Fin 3, (x j = 0 ∨ x j = 1) ∧ (∀ k : Fin 3, k ≠ j → x k ∈ Set.Ioo (0 : ℝ) 1) ∧
            (∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) ∧
            ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
              mfderiv (𝓡 2) (𝓡 4) (diamFam Q t) u σ = mfderiv (𝓡 3) (𝓡 4) W x τ ∧ τ j ≠ 0)) :
    Odd (diamMeet Q t W).ncard ↔ Odd (arcMeet Q t W).ncard := by
  have hloop : ∀ a ∈ Set.Icc (0 : ℝ) 1, diamFam Q t (mk2 a 0) = diamFam Q t (mk2 a 1) := by
    intro a _
    show diamInterp Q t a 0 = diamInterp Q t a 1
    exact (diamInterp_loop hQseam t a).symm
  have he := odd_ncard_loopFamMeet_iff CappingSpace (diamFam Q t) W hL hN hloop hseam havoid
    htrans hface
  rw [diamMeet_ncard_eq_loopFamMeet_zero Q t W, ← loopFamMeet_one_eq_arcMeet Q t W]
  exact he

/-- **T5(b): the half-circle meet at angle `t` and the design's core count have the same parity.**
The engine is applied to the explicit rotation family `arcFam Q t`, whose `p 0 = 1` slice is the
half-circle loop at angle `0` — i.e. the core loop of the chart, by `arcMeet_zero_eq_coreMeet`. -/
theorem odd_ncard_arcMeet_iff_core (Q : ℂ → CappingSpace) (t c : ℝ)
    (P : EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (hQseam : ∀ z : ℂ, ‖z‖ = 1 → Q (-z) = Q z)
    (hL : ContMDiff (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (arcFam Q t))
    (hN : ContMDiff (𝓡 3) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (clampedSweep c (fun s => 1 - s) P))
    (hseam : ∀ x : EuclideanSpace ℝ (Fin 3), onSeam x →
      clampedSweep c (fun s => 1 - s) P (seamInv x) = clampedSweep c (fun s => 1 - s) P x)
    (havoid : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      arcFam Q t u = clampedSweep c (fun s => 1 - s) P x → x ∈ Submission.Drive.unitBox 2 →
      (x 2 = 0 ∨ x 2 = 1) → False)
    (htrans : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      arcFam Q t u = clampedSweep c (fun s => 1 - s) P x →
      LinearMap.range (mfderiv (𝓡 2) (𝓡 4) (arcFam Q t) u).toLinearMap ⊔
        LinearMap.range (mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x).toLinearMap = ⊤)
    (hface : ∀ (u : EuclideanSpace ℝ (Fin 2)) (x : EuclideanSpace ℝ (Fin 3)),
      arcFam Q t u = clampedSweep c (fun s => 1 - s) P x →
      u ∈ Submission.Drive.unitBox 1 → x ∈ Submission.Drive.unitBox 2 →
      (u ∈ Submission.Drive.unitBoxBdry 1 ∨ x ∈ Submission.Drive.unitBoxBdry 2) →
      (∃ i : Fin 2, (u i = 0 ∨ u i = 1) ∧ (∀ j : Fin 2, j ≠ i → u j ∈ Set.Ioo (0 : ℝ) 1) ∧
          (∀ j : Fin 3, x j ∈ Set.Ioo (0 : ℝ) 1) ∧
          ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
            mfderiv (𝓡 2) (𝓡 4) (arcFam Q t) u σ
              = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x τ ∧ σ i ≠ 0)
        ∨ (∃ j : Fin 3, (x j = 0 ∨ x j = 1) ∧ (∀ k : Fin 3, k ≠ j → x k ∈ Set.Ioo (0 : ℝ) 1) ∧
            (∀ i : Fin 2, u i ∈ Set.Ioo (0 : ℝ) 1) ∧
            ∃ (σ : EuclideanSpace ℝ (Fin 2)) (τ : EuclideanSpace ℝ (Fin 3)),
              mfderiv (𝓡 2) (𝓡 4) (arcFam Q t) u σ
                = mfderiv (𝓡 3) (𝓡 4) (clampedSweep c (fun s => 1 - s) P) x τ ∧ τ j ≠ 0)) :
    Odd (arcMeet Q t (clampedSweep c (fun s => 1 - s) P)).ncard
      ↔ Odd (coreSideCount Q c P) := by
  have hloop : ∀ a ∈ Set.Icc (0 : ℝ) 1, arcFam Q t (mk2 a 0) = arcFam Q t (mk2 a 1) := by
    intro a _
    show arcRot Q t a 0 = arcRot Q t a 1
    exact (arcRot_loop hQseam t a).symm
  have he := odd_ncard_loopFamMeet_iff CappingSpace (arcFam Q t)
    (clampedSweep c (fun s => 1 - s) P) hL hN hloop hseam havoid htrans hface
  change Odd (arcMeet Q t (clampedSweep c (fun s => 1 - s) P)).ncard
      ↔ Odd ((coreMeet Q c P).ncard)
  rw [arcMeet_ncard_eq_loopFamMeet_zero, ← arcMeet_zero_eq_coreMeet,
    ← loopFamMeet_one_eq_arcMeet_zero]
  exact he

end

end Work.Drive
