/-
# The transport of the DeTurck operator to the B3 components (general form)

`Work.Diff.STE.B3.transport_deTurck_general` is the residual form of the transport identity that the
B3 layer of the short-time-existence proof needs: on the closed `2σ j`-ball the localised component
`D.R j (P h)` of the DeTurck operator of a section `h` equals

  `∑_{pq} A z p q * ∂_p∂_q (D.R j h a b) z + Ψ (z, M z, ∂M z) a b`,

with `M z = D.mat j h · · z` the `g₀`-orthonormal-frame chart matrix of `h` and `∂M` its first jet,
`A` a smooth, `1`-periodic, symmetric, `lam'`-elliptic coefficient matrix, and `Ψ` a smooth function
of the *state* `(z, M z, ∂M z)`.  The constants `lam'`, `C` (bounding the `pdVec`-jets of `A` up to
order `k` and of the composite `Ψ (·, M ·, ∂M ·)` up to order `k` on the ball) are *uniform in* `h`:
they depend only on the B3 data `D`, `k` and the pinching constants `lam`, `K`.

## The architecture of the proof (all inputs except the assembly are already proved)

* the identity itself is `Work.Diff.STE.B3.transport_identity` (proved): it gives
  `D.R j (P h) a b z = ∑ tmGKi (z, M z) pq * ∂_p∂_q (D.R j h a b) z + tmPsi (z, M z, ∂M z) a b`
  on the closed `2σ j`-ball, given the principal-part input `hSec` (discharged by
  `Work.Diff.STE.B3.transport_Mf_second`), the identification `hGam` of the clamped inverse with the
  honest inverse of the coordinate-frame chart matrix on the ball (discharged by the window estimate
  `clamp_eq_inv_of_det_mem` plus `Work.Diff.STE.B3.tmGK_eq_Gf`), and `hNom`
  (`Work.Diff.STE.B3.tmNom_tame`);
* `A` is `tmA φ lam' γ` with `γ = tmGKi (z, M z)`; its symmetry, ellipticity, smoothness and
  periodicity come from `Work.Diff.STE.B3.tmA_props` and its `pdVec`-jet bound up to order `k` from
  `Work.Diff.STE.B3.tmA_jet_bound` (the jet bound on `γ` on the support of `φ` is
  `Work.Diff.STE.B3.compJetBoundB3` applied to the state function `tmGKi`, with the chart-matrix jet
  bounds `Work.Diff.STE.B3.mat_jet_bound_enlarged`);
* `Ψ` is `χ * tmPsi` with `χ` a fixed bump equal to `1` on the closed `2σ j`-ball; its smoothness is
  `Work.Diff.STE.B3.tmPsi_state_contDiffOn` (plus the "smooth on an open set times a bump supported
  there" argument) and the composite jet bound is again `compJetBoundB3`
  (`Work.Diff.STE.B3.mat_jet_bound_enlarged` supplying the jet bounds of `M`).

The file also records the auxiliary facts about the *fixed* data that make the constants uniform in
`h`: the enlarged ball on which the frame matrix is invertible, the two-sided bounds for the
background chart matrix, and the window estimate for the clamped inverse.
-/
import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.EXT.Basic
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.TransportAux
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.B3.Mf_matrix_eq_of_target
import Submission.Work.Diff.STE.B3.chartMatOf_posDef
import Submission.Work.Diff.STE.B3.det_Mf_metric_ne_zero
import Submission.Work.Diff.STE.B3.quadForm_bounds
import Submission.Work.Diff.STE.B3.CoeffDefs
import Submission.Work.Diff.STE.B3.tmGK_eq_Gf
import Submission.Work.Diff.STE.B3.tmNom_tame
import Submission.Work.Diff.STE.B3.tmA_props
import Submission.Work.Diff.STE.B3.transport_tame_ball
import Submission.Work.Diff.STE.B3.transport_tame_identity
import Submission.Work.Diff.STE.B3.transport_Mf_second
import Submission.Work.Diff.STE.B3.transport_exists_cutoff
import Submission.Work.Diff.STE.B3.compJetBoundB3
import Submission.Work.Diff.STE.B3.tmA_jet_bound
import Submission.Work.Diff.STE.B3.tmGKi_state_contDiffOn
import Submission.Work.Diff.STE.B3.tmPsi_state_contDiffOn
import Submission.Work.Diff.STE.B3.mat_jet_bound_enlarged
import Submission.Work.Diff.STE.Lead.Gal.GardDefs
import Submission.Work.Diff.STE.flat.compact_iteratedFDeriv_bound
import Submission.Work.Diff.STE.B3.DeTurckAux2
import Submission.Work.Diff.STE.B3.tmA_props_weak
import Submission.Work.Diff.STE.B3.window_clamp
import Submission.Work.Diff.STE.B3.transport_tame_assemble
import Submission.Work.Diff.STE.B3.det_bounds_of_quadForm

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.STE.B3

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

noncomputable section


/-! ## 1. The enlarged ball on which all the fixed data are non-degenerate -/

/-- The preimage of the chart target under `flatToE` is open. -/
theorem transport_deTurck_general
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M) (k : ℕ) :
    ∀ (lam K : ℝ), 0 < lam → 0 < K →
      ∃ (lam' C : ℝ), 0 < lam' ∧ 0 ≤ C ∧
        ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
          (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
          (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
          (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
          (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
          (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
          (hjet : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (m : ℕ) (hm : m ≤ k + 1)
            (β : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
            ‖z‖ ≤ 2 * D.σ i →
            ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K),
          ∀ j : ι₀,
            ∃ (A : (Fin (Module.finrank ℝ E) → ℝ) → Fin (Module.finrank ℝ E) →
                 Fin (Module.finrank ℝ E) → ℝ)
              (Psi : ((Fin (Module.finrank ℝ E) → ℝ) ×
                  (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) ×
                  (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
                    Fin (Module.finrank ℝ E) → ℝ)) →
                Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ),
              (∀ z p q, A z p q = A z q p) ∧
              (∀ z (ξ : Fin (Module.finrank ℝ E) → ℝ),
                lam' * ∑ i, (ξ i) ^ 2 ≤ ∑ p, ∑ q, A z p q * ξ p * ξ q) ∧
              (∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin (Module.finrank ℝ E))
                (z : Fin (Module.finrank ℝ E) → ℝ) (p q : Fin (Module.finrank ℝ E)),
                ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  ((A y p q : ℝ) : ℂ)) z‖ ≤ C) ∧
              ContDiff ℝ ((⊤ : ENat) : WithTop ENat) A ∧
              Work.Diff.STE.Periodic1 A ∧
              ContDiff ℝ ((⊤ : ENat) : WithTop ENat) Psi ∧
              (∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin (Module.finrank ℝ E))
                (z : Fin (Module.finrank ℝ E) → ℝ)
                (a b : Fin (Module.finrank ℝ E)), ‖z‖ ≤ 2 * D.σ j →
                ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  ((Psi (y, (fun c d => D.mat j h c d y),
                      (fun c d r => Work.Diff.STE.pdR r (D.mat j h c d) y)) a b : ℝ) : ℂ)) z‖
                  ≤ C) ∧
              ∀ (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
                ‖z‖ ≤ 2 * D.σ j →
                D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b z
                  = (∑ p, ∑ q,
                      A z p q * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h a b)) z)
                    + Psi (z, (fun c d => D.mat j h c d z),
                        (fun c d r => Work.Diff.STE.pdR r (D.mat j h c d) z)) a b := by
  intro lam K hlam hK
  by_cases hne : Nonempty ι₀
  · haveI : Nonempty ι₀ := hne
    -- ### The per-chart packages
    --
    -- For a fixed chart `j` the constants of the construction depend only on `D`, `k`, `lam`, `K`
    -- (never on the section), because every input is chosen before the section is introduced:
    -- * `Work.Diff.STE.B3.mat_jet_bound_enlarged` gives a chart- and section-independent bound `Cmf`
    --   for the `pdVec`-jets of the orthonormal-frame chart matrix on the enlarged balls,
    -- * `Work.Diff.STE.B3.region_all` gives `δ₀` with the enlarged balls inside the chart target and
    --   with the frame matrix invertible,
    -- * `Work.Diff.STE.B3.G0f_form_bounds` / `FfT_form_bounds` give the uniform two-sided bounds for
    --   the background chart matrix and for the frame-change dual,
    -- * `Work.Diff.STE.B3.gamma_elliptic_ta` gives the ellipticity constant of
    --   `γ = tmGKi (z, Mf z)`, `Work.Diff.STE.B3.compJetBoundB3` gives its `pdVec`-jet bound `Kr` on
    --   the enlarged ball (via the state function `(z, V) ↦ tmGKi z V p q`, whose smoothness is
    --   `Work.Diff.STE.B3.tmGKi_state_contDiffOn`, and the ellipticity of `u = Mf` from
    --   `Work.Diff.STE.B3.Mf_loewner`),
    -- * `Work.Diff.STE.B3.tmA_props` and `Work.Diff.STE.B3.tmA_jet_bound` then give the coefficient
    --   matrix `A := tmA φ lam' γ`; `Work.Diff.STE.B3.tmA_eq_of_one` identifies it with `γ` on the
    --   closed `2σ j`-ball,
    -- * `Work.Diff.STE.B3.contDiff_mul_cutoff` and `compJetBoundB3` give the residual
    --   `Ψ := (z, V, W) ↦ φ z * tmPsi z V W`, and `Work.Diff.STE.B3.transport_identity` (with
    --   `window_clamp` for its `hGam`, `transport_Mf_second` for `hSec` and `tmNom_tame` for `hNom`)
    --   gives the identity.
    have hper : ∀ j : ι₀, ∃ (lam' C : ℝ), 0 < lam' ∧ 0 ≤ C ∧
        (∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
          (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
          (hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
          (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
          (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
          (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
          (hjet : ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (m : ℕ) (hm : m ≤ k + 1)
            (β : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
            ‖z‖ ≤ 2 * D.σ i →
            ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K),
          ∃ (A : (Fin (Module.finrank ℝ E) → ℝ) → Fin (Module.finrank ℝ E) →
               Fin (Module.finrank ℝ E) → ℝ)
            (Psi : ((Fin (Module.finrank ℝ E) → ℝ) ×
                (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) ×
                (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
                  Fin (Module.finrank ℝ E) → ℝ)) →
              Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ),
            (∀ z p q, A z p q = A z q p) ∧
            (∀ z (ξ : Fin (Module.finrank ℝ E) → ℝ),
              lam' * ∑ i, (ξ i) ^ 2 ≤ ∑ p, ∑ q, A z p q * ξ p * ξ q) ∧
            (∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin (Module.finrank ℝ E))
              (z : Fin (Module.finrank ℝ E) → ℝ) (p q : Fin (Module.finrank ℝ E)),
              ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                ((A y p q : ℝ) : ℂ)) z‖ ≤ C) ∧
            ContDiff ℝ ((⊤ : ENat) : WithTop ENat) A ∧
            Work.Diff.STE.Periodic1 A ∧
            ContDiff ℝ ((⊤ : ENat) : WithTop ENat) Psi ∧
            (∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin (Module.finrank ℝ E))
              (z : Fin (Module.finrank ℝ E) → ℝ)
              (a b : Fin (Module.finrank ℝ E)), ‖z‖ ≤ 2 * D.σ j →
              ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                ((Psi (y, (fun c d => D.mat j h c d y),
                    (fun c d r => Work.Diff.STE.pdR r (D.mat j h c d) y)) a b : ℝ) : ℂ)) z‖
                ≤ C) ∧
            ∀ (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
              ‖z‖ ≤ 2 * D.σ j →
              D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) a b z
                = (∑ p, ∑ q,
                    A z p q * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h a b)) z)
                  + Psi (z, (fun c d => D.mat j h c d z),
                      (fun c d r => Work.Diff.STE.pdR r (D.mat j h c d) z)) a b) := by
      intro j
      -- ## 1. The fixed data of the construction (all independent of the section `h`)
      obtain ⟨δm, Cmf, hδmp, hCmfn, hMfjet⟩ :=
        mat_jet_bound_enlarged (I := I) (M := M) D k K hK
      obtain ⟨δ₀, hδ₀p, hregion₀⟩ := region_all (I := I) (M := M) D
      set δ : ℝ := min δm (min δ₀ 1) with hδdef
      have hδp : 0 < δ := lt_min hδmp (lt_min hδ₀p one_pos)
      have hδδm : δ ≤ δm := min_le_left _ _
      have hδδ₀ : δ ≤ δ₀ := le_trans (min_le_right _ _) (min_le_left _ _)
      have hδ1 : δ ≤ 1 := le_trans (min_le_right _ _) (min_le_right _ _)
      have hregionδ : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δ →
          (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target ∧
            (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0) :=
        fun z hz => hregion₀ j z (le_trans hz (by linarith))
      obtain ⟨mlo, Mhi, hmlop, hMhinn, hG0b⟩ :=
        G0f_form_bounds (I := I) (M := M) D j (δ₀ := δ) hregionδ
      obtain ⟨eps, Cf, hepsp, hCfnn, hFfb⟩ :=
        FfT_form_bounds (I := I) (M := M) D j (δ₀ := δ) hregionδ
      have hlamE : 0 < mlo * eps := mul_pos hmlop hepsp
      have hlamJ : 0 < (lam * mlo) * eps := mul_pos (mul_pos hlam hmlop) hepsp
      obtain ⟨cE, hcEp, hEll⟩ := gamma_elliptic_ta (I := I) (M := M) D lam K hlam hK j δ
      obtain ⟨a, b, ha, hab, hWin⟩ := window_clamp (I := I) (M := M) D lam K hlam hK
      -- ## 2. The radii
      set R : ℝ := 2 * D.σ j + δ / 4 with hRdef
      set R' : ℝ := 2 * D.σ j + δ / 2 with hR'def
      have hRR' : R < R' := by rw [hRdef, hR'def]; linarith
      have h2σR' : 2 * D.σ j < R' := by rw [hR'def]; linarith
      have hRle : R ≤ 1 / 2 := by rw [hRdef]; have h := D.hσ2 j; linarith
      have hRleδ : R ≤ 2 * D.σ j + δ := by rw [hRdef]; linarith
      have hR'leδ : R' ≤ 2 * D.σ j + δ := by rw [hR'def]; linarith
      have hRreg : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ < R' →
          (Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target ∧
            (Matrix.of (Ff (I := I) (M := M) D j z)).det ≠ 0) :=
        fun z hz => hregionδ z (le_trans (le_of_lt hz) hR'leδ)
      -- ## 3. The cutoff `φ` (equal to `1` on the ball of radius `2σⱼ + δ/8`, supported in `ball 0 R`)
      obtain ⟨φ, hφsm, hφnn, hφle1, hφone, hφts⟩ := exists_cutoff_le_one
        (Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ / 8))
        (Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) R)
        (isCompact_closedBall _ _) Metric.isOpen_ball
        (fun z hz => by
          rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
          rw [Metric.mem_ball, dist_eq_norm, sub_zero, hRdef]
          linarith)
      have hφsupp : Function.support φ ⊆ Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) R :=
        fun z hz => hφts (subset_tsupport φ hz)
      have hφtgt : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j → φ z = 1 := by
        intro z hz
        refine hφone z ?_
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        linarith
      have hφtsc : tsupport φ ⊆ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) R := by
        intro z hz
        have h := hφts hz
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at h
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
        exact le_of_lt h
      obtain ⟨Mφ, hMφnn, hMφjet⟩ := phi_jets_bound φ hφsm hφtsc k
      -- ## 4. The determinant bump `κ`
      set bl : ℝ := ((lam * mlo) * eps) ^ (Module.finrank ℝ E) with hbldef
      set bu : ℝ := max ((Cmf * ((Module.finrank ℝ E : ℕ) : ℝ)) ^ (Module.finrank ℝ E)) 1 with hbudef
      have hblpos : 0 < bl := pow_pos hlamJ _
      have hbupos : 0 < bu := lt_of_lt_of_le one_pos (le_max_right _ _)
      set ρ : ℝ := min bl bu / 4 with hρdef
      have hρpos : 0 < ρ := by rw [hρdef]; exact div_pos (lt_min hblpos hbupos) (by norm_num)
      have hrInpos : 0 < |bu - bl| / 2 + ρ := by
        have := abs_nonneg (bu - bl); linarith
      have hrInlt : |bu - bl| / 2 + ρ < |bu - bl| / 2 + ρ + ρ := by linarith
      set β : ContDiffBump ((bl + bu) / 2) :=
        ⟨|bu - bl| / 2 + ρ, |bu - bl| / 2 + ρ + ρ, hrInpos, hrInlt⟩ with hβdef
      have hβsub : (bl + bu) / 2 - (|bu - bl| / 2 + ρ + ρ) = min bl bu / 2 := by
        rw [hρdef]
        rcases le_total bl bu with h | h
        · rw [abs_of_nonneg (by linarith), min_eq_left h]; ring_nf
        · rw [abs_of_nonpos (by linarith), min_eq_right h]; ring_nf
      have hβoutpos : 0 < (bl + bu) / 2 - (|bu - bl| / 2 + ρ + ρ) := by
        rw [hβsub]; exact half_pos (lt_min hblpos hbupos)
      set κ : (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) → ℝ := fun V => β ((Matrix.of V).det) with hκdef
      have hκsm : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) κ := by
        rw [hκdef]
        exact β.contDiff.comp (det_entry_contDiff (n := Module.finrank ℝ E))
      have hκsupp : tsupport κ ⊆ {V : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ | 0 < (Matrix.of V).det} := by
        have hclosed : IsClosed {V : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ |
            (bl + bu) / 2 - (|bu - bl| / 2 + ρ + ρ) ≤ (Matrix.of V).det} :=
          isClosed_le continuous_const (Continuous.matrix_det continuous_id)
        have hrOut : β.rOut = |bu - bl| / 2 + ρ + ρ := by rw [hβdef]
        have hsub : Function.support κ ⊆ {V : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ |
            (bl + bu) / 2 - (|bu - bl| / 2 + ρ + ρ) ≤ (Matrix.of V).det} := by
          intro V hV
          have hV2 : (Matrix.of V).det ∈ Function.support β := by
            rw [hκdef] at hV
            simpa only [Function.mem_support] using hV
          have hV3 : (Matrix.of V).det ∈ tsupport β := subset_tsupport β hV2
          rw [ContDiffBump.tsupport_eq, Metric.mem_closedBall, Real.dist_eq, hrOut] at hV3
          have h4 : (bl + bu) / 2 - (Matrix.of V).det ≤ |bu - bl| / 2 + ρ + ρ :=
            (abs_sub_le_iff.mp hV3).2
          show (bl + bu) / 2 - (|bu - bl| / 2 + ρ + ρ) ≤ (Matrix.of V).det
          have h5 : (bl + bu) / 2 ≤ (Matrix.of V).det + (|bu - bl| / 2 + ρ + ρ) := by
            rw [← add_comm ((|bu - bl| / 2 + ρ + ρ)) ((Matrix.of V).det)]
            exact sub_le_iff_le_add.mp h4
          exact sub_le_iff_le_add.mpr h5
        have hmain := hclosed.closure_subset_iff.mpr hsub
        refine fun V hV => hβoutpos.trans_le (hmain hV)
      -- ## 5. The uniform jet bound for the coefficient family `γ = tmGKi (z, Mf z)`
      obtain ⟨Cγ, hCγnn, hCγ⟩ := tmGKi_comp_jets_bound (I := I) (M := M) D j a b ha hab hRR'
        hRreg hlamJ hCmfn k
      obtain ⟨Ct, hCtnn, hCt⟩ :=
        tmA_jet_bound (n := Module.finrank ℝ E) R cE Cγ Mφ hRle hcEp hCγnn hMφnn k
      -- ## 6. The uniform jet bound for the residual `Ψ`
      have hΦΨ : ∀ af bf : Fin (Module.finrank ℝ E), ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
          (fun w : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) => ((φ w.1 * κ w.2.1 * tmPsi (I := I) (M := M) D j a b ha hab w.1 w.2.1
            (fun i j' c => w.2.2 c i j') af bf : ℝ) : ℂ))
          {w : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) | ‖w.1‖ < R' ∧ (Matrix.of w.2.1).det ≠ 0} := by
        intro af bf
        have ht : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
            (fun w : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) => fun i j' c => w.2.2 c i j') := by fun_prop
        have hlin : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
            (fun w : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) => (w.1, w.2.1, (fun i j' c => w.2.2 c i j'))) :=
          ContDiff.prodMk contDiff_fst (ContDiff.prodMk (contDiff_fst.comp contDiff_snd) ht)
        have hmap : MapsTo (fun w : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) => (w.1, w.2.1, (fun i j' c => w.2.2 c i j')))
            {w : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) | ‖w.1‖ < R' ∧ (Matrix.of w.2.1).det ≠ 0}
            {w : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) | Work.Diff.STE.flatToE (I := I) (D.x₀ j) w.1
                ∈ (extChartAt I (D.x₀ j)).target ∧
              (Matrix.of (Ff (I := I) (M := M) D j w.1)).det ≠ 0 ∧
              (Matrix.of w.2.1).det ≠ 0} :=
          fun w hw => ⟨(hRreg w.1 hw.1).1, (hRreg w.1 hw.1).2, hw.2⟩
        have hψ : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
            (fun w : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) => tmPsi (I := I) (M := M) D j a b ha hab w.1 w.2.1
              (fun i j' c => w.2.2 c i j') af bf)
            {w : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) | ‖w.1‖ < R' ∧ (Matrix.of w.2.1).det ≠ 0} :=
          ((tmPsi_state_contDiffOn (I := I) (M := M) D j a b ha hab af bf).comp
            hlin.contDiffOn hmap).congr (fun w _ => rfl)
        have hχ : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
            (fun w : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) => φ w.1 * κ w.2.1) :=
          (hφsm.comp contDiff_fst).mul (hκsm.comp (contDiff_fst.comp contDiff_snd))
        exact (Complex.ofRealCLM.contDiff.comp_contDiffOn (hχ.contDiffOn.mul hψ)).congr
          (fun w _ => rfl)
      have hCψe : ∀ af bf : Fin (Module.finrank ℝ E), ∃ C : ℝ, 0 ≤ C ∧
          ∀ (u : (Fin (Module.finrank ℝ E) → ℝ) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ),
            (∀ s t : Fin (Module.finrank ℝ E), ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
              (fun z : Fin (Module.finrank ℝ E) → ℝ => u z s t) {z : Fin (Module.finrank ℝ E) → ℝ | ‖z‖ < R'}) →
            (∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ < R' → ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
              ((lam * mlo) * eps) * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ j', u z i j' * ξ i * ξ j') →
            (∀ (m : ℕ) (hm : m ≤ k + 1) (β' : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ) (s t : Fin (Module.finrank ℝ E)),
              ‖z‖ < R' →
              ‖Work.Diff.STE.pdVec m β' (fun y : Fin (Module.finrank ℝ E) → ℝ => ((u y s t : ℝ) : ℂ)) z‖ ≤ Cmf) →
            ∀ (m : ℕ) (hm : m ≤ k) (β' : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j →
              ‖Work.Diff.STE.pdVec m β' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                ((φ y * κ (u y) * tmPsi (I := I) (M := M) D j a b ha hab y (u y)
                  (fun i j' c => Work.Diff.STE.pdR c (fun w : Fin (Module.finrank ℝ E) → ℝ => u w i j') y)
                  af bf : ℝ) : ℂ)) z‖ ≤ C := by
        intro af bf
        obtain ⟨C, hC0, hC⟩ := compJetBoundB3 (n := Module.finrank ℝ E) (k := k)
          (fun z V W => ((φ z * κ V * tmPsi (I := I) (M := M) D j a b ha hab z V
            (fun i j' c => W c i j') af bf : ℝ) : ℂ)) (2 * D.σ j) R' h2σR' (hΦΨ af bf)
          ((lam * mlo) * eps) Cmf hlamJ hCmfn
        exact ⟨C, hC0, hC⟩
      choose Cψf hCψf using hCψe
      set Cψ : ℝ := ∑ af : Fin (Module.finrank ℝ E), ∑ bf : Fin (Module.finrank ℝ E), Cψf af bf with hCψdef
      have hCψnn : 0 ≤ Cψ := Finset.sum_nonneg (fun a _ => Finset.sum_nonneg (fun b _ => (hCψf a b).1))
      have hCψle : ∀ af bf : Fin (Module.finrank ℝ E), Cψf af bf ≤ Cψ := by
        intro af bf
        have h1 : Cψf af bf ≤ ∑ bf' : Fin (Module.finrank ℝ E), Cψf af bf' :=
          Finset.single_le_sum (fun a _ => (hCψf af a).1) (Finset.mem_univ bf)
        have h2 : (∑ bf' : Fin (Module.finrank ℝ E), Cψf af bf') ≤ Cψ := by
          rw [hCψdef]
          exact Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => (hCψf a b).1))
            (Finset.mem_univ af)
        linarith
      -- ## 7. The final constants
      have hCnn : 0 ≤ max Cγ (max Cψ Ct) := le_trans hCγnn (le_max_left _ _)
      have hCψC : Cψ ≤ max Cγ (max Cψ Ct) := le_trans (le_max_left _ _) (le_max_right _ _)
      have hCtC : Ct ≤ max Cγ (max Cψ Ct) := le_trans (le_max_right _ _) (le_max_right _ _)
      refine ⟨cE / 2, max Cγ (max Cψ Ct), by positivity, hCnn, ?_⟩
      -- ## 8. The per-section construction
      intro h hsym hpos hsmooth hell hub hjet
      -- the Mf data
      have hu_sm : ∀ s t : Fin (Module.finrank ℝ E), ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
          (fun z : Fin (Module.finrank ℝ E) → ℝ => Mf (I := I) (M := M) D h j z s t) {z : Fin (Module.finrank ℝ E) → ℝ | ‖z‖ < R'} := by
        intro s t z hz
        exact (mat_contDiffAt_of_chartData (I := I) (M := M) D h hsmooth j s t z
          (hregionδ z (le_trans (le_of_lt hz) hR'leδ)).1).contDiffWithinAt
      have hMfLoewner : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j + δ →
          ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          ((lam * mlo) * eps) * ∑ i, (ξ i) ^ 2
            ≤ ∑ i, ∑ kk, Mf (I := I) (M := M) D h j z i kk * ξ i * ξ kk :=
        fun z hz => Mf_loewner (I := I) (M := M) D h j (δ₀ := δ) hregionδ (mul_pos hlam hmlop).le
          hepsp.le
          (fun z hz ξ => (Gf_loewner (I := I) (M := M) D h j (δ₀ := δ) (δ := δ) le_rfl hlam hK
            hell hub (fun z hz ξ => (hG0b z hz ξ).1) (fun z hz ξ => (hG0b z hz ξ).2) z hz ξ).1)
          (fun z hz ξ => (hFfb z hz ξ).1) z hz
      have hu_ell : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ < R' → ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          ((lam * mlo) * eps) * ∑ i, (ξ i) ^ 2
            ≤ ∑ i, ∑ kk, Mf (I := I) (M := M) D h j z i kk * ξ i * ξ kk :=
        fun z hz => hMfLoewner z (le_trans (le_of_lt hz) hR'leδ)
      have hu_jet : ∀ (m : ℕ) (hm : m ≤ k + 1) (β' : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ) (s t : Fin (Module.finrank ℝ E)),
          ‖z‖ < R' →
          ‖Work.Diff.STE.pdVec m β' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((Mf (I := I) (M := M) D h j y s t : ℝ) : ℂ)) z‖ ≤ Cmf :=
        fun m hm β' z s t hz => hMfjet h hsym hsmooth hjet j s t m hm β' z
          (by linarith [le_of_lt hz, hR'leδ, hδδm])
      -- the composite coefficient family
      set γ : (Fin (Module.finrank ℝ E) → ℝ) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun z p q =>
        tmGKi (I := I) (M := M) D j a b ha hab z (Mf (I := I) (M := M) D h j z) p q with hγdef
      have hγsymm : ∀ z : Fin (Module.finrank ℝ E) → ℝ, z ∈ Metric.ball 0 R → ∀ p q, γ z p q = γ z q p := by
        intro z hz p q
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
        have h := tmGKi_symm (I := I) (M := M) D j a b ha hab z
          (Mf (I := I) (M := M) D h j z) (fun p q => hsym (D.pt j z) _ _) p q
        simpa only [hγdef] using h
      have hγpos : ∀ z : Fin (Module.finrank ℝ E) → ℝ, z ∈ Metric.ball 0 R → ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          cE * ∑ p, (ξ p) ^ 2 ≤ ∑ p, ∑ q, γ z p q * ξ p * ξ q := by
        intro z hz ξ
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
        have h := hEll a b ha hab h hsym hell hub hregionδ z
          (le_trans (le_of_lt hz) hRleδ) ξ
        simpa only [hγdef] using h
      have hγs : ∀ p q, ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
          (fun w => γ w p q) (Metric.ball 0 R) := by
        intro p q
        have h := tmGKi_comp_Mf_contDiffOn D h hsmooth j a b ha hab
          (fun z hz => hregionδ z (le_trans (le_of_lt hz) hRleδ)) p q
        simpa only [hγdef] using h
      have hγjet : ∀ (m : ℕ) (hm : m ≤ k) (β' : Fin m → Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ) (p q : Fin (Module.finrank ℝ E)),
          z ∈ Metric.ball 0 R →
          ‖Work.Diff.STE.pdVec m β' (fun y : Fin (Module.finrank ℝ E) → ℝ => ((γ y p q : ℝ) : ℂ)) z‖ ≤ Cγ := by
        intro m hm β' z p q hz
        rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hz
        have hh := hCγ (fun z s t => Mf (I := I) (M := M) D h j z s t) hu_sm hu_ell hu_jet
          m hm β' z (le_of_lt hz) p q
        simpa only [hγdef] using hh
      -- the coefficient matrix and its clauses
      set A : (Fin (Module.finrank ℝ E) → ℝ) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := tmA φ (cE / 2) γ with hAdef
      have hApw := (tmA_props_weak (n := Module.finrank ℝ E) R cE hRle hcEp) φ γ (cE / 2)
        (by positivity) (by linarith) hφsm hφnn hφle1 hφts hγs hγsymm hγpos
      have hAsym : ∀ z p q, A z p q = A z q p := by
        intro z p q
        simpa only [hAdef] using hApw.1 z p q
      have hAell : ∀ z ξ : Fin (Module.finrank ℝ E) → ℝ,
          (cE / 2) * ∑ p, (ξ p) ^ 2 ≤ ∑ p, ∑ q, A z p q * ξ p * ξ q := by
        intro z ξ
        simpa only [hAdef] using hApw.2.1 z ξ
      have hAsm : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) A := by
        simpa only [hAdef] using hApw.2.2.1
      have hAper : Work.Diff.STE.Periodic1 A := by
        simpa only [hAdef] using hApw.2.2.2
      have hAjet : ∀ (m : ℕ) (hm : m ≤ k) (β' : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ) (p q : Fin (Module.finrank ℝ E)),
          ‖Work.Diff.STE.pdVec m β' (fun y : Fin (Module.finrank ℝ E) → ℝ => ((A y p q : ℝ) : ℂ)) z‖ ≤ Ct := by
        intro m hm β' z p q
        have h := hCt φ γ (cE / 2) (by positivity) (by linarith) hφsm hφnn hφle1 hMφjet hφts
          hγs hγsymm hγpos hγjet m hm β' z p q
        simpa only [hAdef] using h
      -- the residual
      set Ψ : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ := fun w af bf =>
        φ w.1 * κ w.2.1 * tmPsi (I := I) (M := M) D j a b ha hab w.1 w.2.1 w.2.2 af bf
        with hΨdef
      have hΨsm : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) Ψ := by
        refine contDiff_pi' (fun af => contDiff_pi' (fun bf => ?_))
        have hχ : ContDiff ℝ ((⊤ : ENat) : WithTop ENat)
            (fun p : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) => φ p.1 * κ p.2) :=
          (hφsm.comp contDiff_fst).mul (hκsm.comp contDiff_snd)
        set U : Set ((Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ)) :=
          {p | Work.Diff.STE.flatToE (I := I) (D.x₀ j) p.1 ∈ (extChartAt I (D.x₀ j)).target ∧
            ‖p.1‖ < R' ∧ (Matrix.of p.2).det ≠ 0} with hUdef
        have hUo : IsOpen U := by
          have ho1 : IsOpen {p : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) |
              Work.Diff.STE.flatToE (I := I) (D.x₀ j) p.1 ∈ (extChartAt I (D.x₀ j)).target} :=
            IsOpen.preimage ((Work.Diff.STE.contDiff_flatToE (I := I) (D.x₀ j)).continuous.comp
              continuous_fst) (isOpen_extChartAt_target (I := I) (D.x₀ j))
          have ho2 : IsOpen {p : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) | ‖p.1‖ < R'} :=
            IsOpen.preimage (continuous_norm.comp continuous_fst) isOpen_Iio
          have ho3 : IsOpen {p : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) | (Matrix.of p.2).det ≠ 0} :=
            IsOpen.preimage (Continuous.matrix_det continuous_snd) isOpen_ne
          have hset : {p : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) |
                Work.Diff.STE.flatToE (I := I) (D.x₀ j) p.1 ∈ (extChartAt I (D.x₀ j)).target ∧
                  ‖p.1‖ < R' ∧ (Matrix.of p.2).det ≠ 0}
              = {p : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) | Work.Diff.STE.flatToE (I := I) (D.x₀ j) p.1
                    ∈ (extChartAt I (D.x₀ j)).target} ∩
                ({p : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) | ‖p.1‖ < R'} ∩ {p : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) | (Matrix.of p.2).det ≠ 0}) := by
            ext p
            simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
          rw [hUdef, hset]
          exact ho1.inter (ho2.inter ho3)
        have hψ : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
            (fun w : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) => tmPsi (I := I) (M := M) D j a b ha hab w.1 w.2.1 w.2.2 af bf)
            ((fun w : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) => (w.1, w.2.1)) ⁻¹' U) := by
          refine (tmPsi_state_contDiffOn (I := I) (M := M) D j a b ha hab af bf).mono ?_
          intro w hw
          simp only [hUdef, Set.mem_preimage, Set.mem_setOf_eq] at hw
          obtain ⟨h1, h2, h3⟩ := hw
          exact ⟨h1, (hRreg w.1 h2).2, h3⟩
        have hsupp : tsupport (fun p : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) => φ p.1 * κ p.2) ⊆ U := by
          intro p hp
          have h1 : p ∈ tsupport (fun p : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) => φ p.1) :=
            closure_mono (fun q hq => by
              simp only [Function.mem_support, mul_ne_zero_iff] at hq; exact hq.1) hp
          have h2 : p ∈ tsupport (fun p : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) => κ p.2) :=
            closure_mono (fun q hq => by
              simp only [Function.mem_support, mul_ne_zero_iff] at hq; exact hq.2) hp
          have hz1 : p.1 ∈ tsupport φ :=
            ((isClosed_tsupport φ).preimage continuous_fst).closure_subset_iff.mpr
              (fun q hq => subset_tsupport φ (by simpa [Function.mem_support] using hq)) h1
          have hz2 : p.2 ∈ tsupport κ :=
            ((isClosed_tsupport κ).preimage continuous_snd).closure_subset_iff.mpr
              (fun q hq => subset_tsupport κ (by simpa [Function.mem_support] using hq)) h2
          have hlin : ‖p.1‖ < R := by
            have hh := hφts hz1
            rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hh
            exact hh
          rw [hUdef]
          simp only [Set.mem_setOf_eq]
          exact ⟨(hregionδ p.1 (le_trans (le_of_lt (lt_trans hlin hRR')) hR'leδ)).1,
            lt_trans hlin hRR', ne_of_gt (hκsupp hz2)⟩
        rw [hΨdef]
        exact contDiff_mul_cutoff_real (pr := fun w : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) => (w.1, w.2.1)) (χ := fun p =>
          φ p.1 * κ p.2) (ψ := fun w : (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) =>
            tmPsi (I := I) (M := M) D j a b ha hab w.1 w.2.1 w.2.2 af bf) (U := U)
          (ContDiff.prodMk contDiff_fst (contDiff_fst.comp contDiff_snd)) hχ hUo hψ hsupp
      have hκone : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j →
          κ (Mf (I := I) (M := M) D h j z) = 1 := by
        intro z hz
        have hsymM : ∀ p q, (Matrix.of (Mf (I := I) (M := M) D h j z)) p q
            = (Matrix.of (Mf (I := I) (M := M) D h j z)) q p := by
          intro p q
          simp only [Matrix.of_apply]
          exact hsym (D.pt j z) _ _
        have hentry : ∀ p q : Fin (Module.finrank ℝ E), |Mf (I := I) (M := M) D h j z p q| ≤ Cmf := by
          intro p q
          have hh := hMfjet h hsym hsmooth hjet j p q 0 (Nat.zero_le (k + 1))
            (Fin.elim0 : Fin 0 → Fin (Module.finrank ℝ E)) z (le_trans hz (by linarith))
          rw [pdVec_zero_eq] at hh
          simpa only [Complex.norm_real, Real.norm_eq_abs, Mf] using hh
        obtain ⟨hlo, hhi⟩ := det_bounds_of_quadForm
          (Matrix.of (Mf (I := I) (M := M) D h j z)) hsymM hlamJ.le
          (fun ξ => hMfLoewner z (le_trans hz (by linarith)) ξ)
          (fun ξ => form_le_of_entries (fun p q => Mf (I := I) (M := M) D h j z p q)
            hCmfn hentry ξ)
        have hblo : bl ≤ (Matrix.of (Mf (I := I) (M := M) D h j z)).det := by
          simpa only [hbldef] using hlo
        have hbhi : (Matrix.of (Mf (I := I) (M := M) D h j z)).det ≤ bu := by
          refine le_trans hhi ?_
          simpa only [Fintype.card_fin] using le_max_left ((Cmf * ((Module.finrank ℝ E : ℕ) : ℝ))
            ^ (Module.finrank ℝ E)) (1 : ℝ)
        have hmem : (Matrix.of (Mf (I := I) (M := M) D h j z)).det ∈
            Metric.closedBall ((bl + bu) / 2) (|bu - bl| / 2 + ρ) := by
          rw [Metric.mem_closedBall, Real.dist_eq, abs_sub_le_iff]
          constructor
          · have h1 : (Matrix.of (Mf (I := I) (M := M) D h j z)).det - (bl + bu) / 2
                ≤ |bu - bl| / 2 := by
              have h2 : (Matrix.of (Mf (I := I) (M := M) D h j z)).det - (bl + bu) / 2
                  ≤ (bu - bl) / 2 := by linarith
              exact le_trans h2 (div_le_div_of_nonneg_right (le_abs_self _) (by norm_num))
            linarith [hρpos]
          · have h1 : (bl + bu) / 2 - (Matrix.of (Mf (I := I) (M := M) D h j z)).det
                ≤ |bu - bl| / 2 := by
              have h2 : (bl + bu) / 2 - (Matrix.of (Mf (I := I) (M := M) D h j z)).det
                  ≤ (bu - bl) / 2 := by linarith
              exact le_trans h2 (div_le_div_of_nonneg_right (le_abs_self _) (by norm_num))
            linarith [hρpos]
        rw [hκdef]
        apply ContDiffBump.one_of_mem_closedBall
        exact hmem
      have hκone' : ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ j →
          κ (fun c d => D.mat j h c d z) = 1 := fun z hz => hκone z hz
      have hΨjet : ∀ (m : ℕ) (hm : m ≤ k) (β' : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
          ‖z‖ ≤ 2 * D.σ j → ∀ af bf : Fin (Module.finrank ℝ E),
          ‖Work.Diff.STE.pdVec m β' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((Ψ (y, (fun c d => D.mat j h c d y),
                (fun c d r => Work.Diff.STE.pdR r (D.mat j h c d) y)) af bf : ℝ) : ℂ)) z‖
            ≤ Cψ := by
        intro m hm β' z hz af bf
        have h' := (hCψf af bf).2 (fun z c d => D.mat j h c d z) hu_sm hu_ell hu_jet m hm β' z hz
        have h'' : ‖Work.Diff.STE.pdVec m β' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((Ψ (y, (fun c d => D.mat j h c d y),
                (fun c d r => Work.Diff.STE.pdR r (D.mat j h c d) y)) af bf : ℝ) : ℂ)) z‖
            ≤ Cψf af bf := by
          simpa only [hΨdef, Mf] using h'
        exact le_trans h'' (hCψle af bf)
      have hid : ∀ (af bf : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j →
          D.R j (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ h hsym hpos hsmooth) af bf z
            = (∑ p, ∑ q, A z p q
                * Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (D.R j h af bf)) z)
              + Ψ (z, (fun c d => D.mat j h c d z),
                  (fun c d r => Work.Diff.STE.pdR r (D.mat j h c d) z)) af bf := by
        intro af bf z hz
        have hGam : ∀ (z' : Fin (Module.finrank ℝ E) → ℝ), ‖z'‖ ≤ 2 * D.σ j → ∀ c d : Fin (Module.finrank ℝ E),
            tmGKi (I := I) (M := M) D j a b ha hab z' (fun p q => D.mat j h p q z') c d
              = tmGfi (I := I) (M := M) D h j z' c d := by
          intro z' hz' c d
          exact congrFun (congrFun (hWin h hsym hell hub j z' hz').2 c) d
        have h1 := tm_identity_clause (I := I) (M := M) D hLC h hsym hpos hsmooth j af bf
          φ hφsm hφtgt R hRle hφsupp (by linarith [D.hσ j]) (cE / 2) a b ha hab hGam z hz
        have hAc : ∀ p q : Fin (Module.finrank ℝ E), A z p q
            = tmA φ (cE / 2) (tmGfi (I := I) (M := M) D h j) z p q := by
          intro p q
          have hρ : (2 : ℝ) * D.σ j ≤ R := by rw [hRdef]; linarith [hδp]
          have h3 : γ z p q = tmGfi (I := I) (M := M) D h j z p q := by
            rw [hγdef]
            exact hGam z hz p q
          rw [hAdef]
          rw [tmA_eq_of_one (n := Module.finrank ℝ E) φ γ hRle hρ hφsupp
            (fun w hw => hφtgt w hw) hz p q, h3]
          exact (tmA_eq_of_one (n := Module.finrank ℝ E) φ
            (tmGfi (I := I) (M := M) D h j) hRle hρ hφsupp
            (fun w hw => hφtgt w hw) hz p q).symm
        have hΨid : Ψ (z, (fun c d => D.mat j h c d z),
              (fun c d r => Work.Diff.STE.pdR r (D.mat j h c d) z)) af bf
            = φ z * tmPsi (I := I) (M := M) D j a b ha hab z
                (fun c d => D.mat j h c d z)
                (fun c d r => Work.Diff.STE.pdR r (D.mat j h c d) z) af bf := by
          simp only [hΨdef]
          rw [hκone' z hz]
          ring
        rw [h1, hΨid]
        congr 1
        · refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
          rw [hAc p q]
      exact ⟨A, Ψ, hAsym, hAell,
        fun m hm β' z p q => le_trans (hAjet m hm β' z p q) hCtC,
        hAsm, hAper, hΨsm,
        fun m hm β' z af bf hz => le_trans (hΨjet m hm β' z hz af bf) hCψC,
        hid⟩
    choose lam' C hlam' hC hbody using hper
    refine ⟨Finset.univ.inf' Finset.univ_nonempty lam', Finset.univ.sup' Finset.univ_nonempty C,
      ?_, ?_, ?_⟩
    · exact (Finset.lt_inf'_iff Finset.univ_nonempty).mpr fun i _ => hlam' i
    · obtain ⟨j₀⟩ := hne
      exact le_trans (hC j₀) (Finset.le_sup' C (Finset.mem_univ j₀))
    · intro h hsym hpos hsmooth hell hub hjet j
      obtain ⟨A, Psi, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hbody j h hsym hpos hsmooth hell hub hjet
      exact ⟨A, Psi, h1,
        fun z ξ => le_trans (mul_le_mul_of_nonneg_right
          (Finset.inf'_le lam' (Finset.mem_univ j))
          (Finset.sum_nonneg fun i _ => sq_nonneg _)) (h2 z ξ),
        fun m hm β z p q => le_trans (h3 m hm β z p q) (Finset.le_sup' C (Finset.mem_univ j)),
        h4, h5, h6,
        fun m hm β z a b hz =>
          le_trans (h7 m hm β z a b hz) (Finset.le_sup' C (Finset.mem_univ j)),
        h8⟩
  · refine ⟨1, 0, one_pos, le_refl 0, ?_⟩
    intro h hsym hpos hsmooth hell hub hjet j
    exact (hne ⟨j⟩).elim


end

end Work.Diff.STE.B3
