import Mathlib
import Submission.Work.Diff.STE.Lead.deTurck_bound
import Submission.Work.Diff.STE.Lead.GalTame.BNorm_J_le_any
import Submission.Work.Diff.STE.Lead.GalTame.J_pointwise_le_any
import Submission.Work.Diff.STE.Lead.Gal.Prelude
import Submission.Work.Diff.STE.Lead.Gal.Prelude2
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv
import Submission.Work.Diff.STE.B3.BNorm_le_ENormB_unif
import Submission.Work.Diff.STE.Lead.pointwise_le_sqrt_BNorm_uniform
import Submission.Work.Diff.STE.Lead.GalTame.galVF2_coeff_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

/-! ## The pointwise (velocity) bound for the span-form Galerkin field

`galVF2_velocity_bound`: on the trap `{galE D k₀ ε c ≤ B} ∩ {J ρ ε (galState D ε c) ≥ (1/4) g₀}` the
*value* `genMap D ε (galVF2 … c) y u v` of the span-form field is bounded by

  `C (1+B)² √(g₀(u,u)) √(g₀(v,v))`

with a constant `C` uniform in `ε ∈ (0, ε₁]`.

ROUTE (as implemented).  On the trap the foreground `u~ := D.J ρ ε (galState D ε c)` is positive
definite, so `galVF2` is the honest coefficient field of the DeTurck tensor and
`genMap D ε (galVF2 c) = D.J ρ ε (P u~)` (`Work.Diff.STE.Lead.genMap_galVF2`).  The pointwise bound
is then exactly the Friedrichs-mollifier pointwise propagation
`Work.Diff.STE.Lead.GalTame.J_pointwise_le_any` of the pointwise DeTurck bound
`Work.Diff.STE.Lead.deTurck_bound`: the latter needs (i) `D.BNorm k₀ u~ ≤ BdeT` (from
`BNorm_J_le_any` and `BNorm_le_ENormB_unif` applied to the energy hypothesis) and (ii) the upper
pinching `u~ ≤ K g₀` (from the uniform Sobolev pointwise bound
`Work.Diff.STE.Lead.pointwise_le_sqrt_BNorm_uniform`).  Finally `1 + BdeT ≤ (1 + C_J C_B)(1+B)`
absorbs the ε-uniform constant into the announced `(1+B)²`. -/

/-- The background metric `g₀` is positive semidefinite on the diagonal. -/
private lemma smet_inner_nn {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {g : Submission.Diff.SMet I M} {x : M} (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  by_cases hv : v = 0
  · subst hv; simp
  · exact (g.pos x v hv).le

theorem galVF2_velocity_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless] [CompactSpace M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (hLC : Submission.Diff.LCSmooth I M)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) (g₀.inner))
    (k₀ : ℕ) (hk₀ : Module.finrank ℝ E + 12 < 2 * k₀) (B : ℝ) (hB : 0 ≤ B)
    (ε₁ : ℝ) (hε₁ : 0 < ε₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) ε₁, ∀ (hε : 0 < ε)
      (c : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ),
      Work.Diff.STE.Lead.galE D k₀ ε c ≤ B →
      (∀ (x : M) (v : TangentSpace I x),
        (1 / 4 : ℝ) * g₀.inner x v v
          ≤ (D.J ρ ε (Submission.Diff.STEGal.galState D ε c)) x v v) →
      ∀ (y : M) (u v : TangentSpace I y),
        |Work.Diff.STE.D.genMap (I := I) (M := M) D ε
          (Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 c) y u v|
          ≤ C * (1 + B) * (1 + B) * Real.sqrt (g₀.inner y u u) * Real.sqrt (g₀.inner y v v)
:= by
  classical
  -- `k₀ > finrank/2`: the Sobolev index condition, in the two forms used below.
  have hk2 : Fintype.card (Fin (Module.finrank ℝ E)) < 2 * k₀ := by
    rw [Fintype.card_fin]; omega
  -- The constants, all independent of `ε` and of the coefficient vector `c`.
  obtain ⟨C_B, hC_B_nn, hBnd_EN⟩ :=
    Work.Diff.STE.B3.BNorm_le_ENormB_unif (I := I) (M := M) D k₀
  obtain ⟨C_J, hC_J_nn, hJN⟩ :=
    Work.Diff.STE.Lead.GalTame.BNorm_J_le_any (I := I) (M := M) D ρ hρ k₀ ε₁ hε₁
  obtain ⟨C_Jp, hC_Jp_nn, hJpl⟩ :=
    Work.Diff.STE.Lead.GalTame.J_pointwise_le_any (I := I) (M := M) D ρ hρ hρ0 hρs ε₁ hε₁
  obtain ⟨d₀, hd₀pos, hd₀le⟩ :=
    Work.Diff.STE.B3.dens_lower_bound (I := I) (M := M) D
      (fun i => Work.Diff.STE.B3.densGood (I := I) (M := M) D i)
  obtain ⟨C_u, hC_u_nn, hpu⟩ :=
    Work.Diff.STE.Lead.pointwise_le_sqrt_BNorm_uniform (I := I) (M := M) D k₀ hk2
      ⟨d₀, hd₀pos, hd₀le⟩
  -- `BdeT` dominates `D.BNorm k₀ u~` for every admissible `ε, c`.
  set BdeT : ℝ := C_J * (C_B * B) with hBdeT
  have hBdeT_nn : 0 ≤ BdeT := by
    rw [hBdeT]; exact mul_nonneg hC_J_nn (mul_nonneg hC_B_nn hB)
  -- The upper pinching constant of `u~`.
  set K : ℝ := C_u * Real.sqrt BdeT with hK
  obtain ⟨C_P, hC_P_nn, hPbound⟩ :=
    (Work.Diff.STE.Lead.deTurck_bound (I := I) (M := M) D hLC k₀ hk₀ (1 / 4) K
      (by norm_num)).1
  set KP : ℝ := C_P * (1 + BdeT) ^ 2 with hKP
  have hKP_nn : 0 ≤ KP := by
    rw [hKP]; exact mul_nonneg hC_P_nn (sq_nonneg _)
  refine ⟨C_Jp * C_P * (1 + C_J * C_B) ^ 2,
    mul_nonneg (mul_nonneg hC_Jp_nn hC_P_nn) (sq_nonneg _), ?_⟩
  intro ε hεIoc hε c hgalE hpinch
  have hεpos : 0 < ε := hεIoc.1
  have hεle : ε ≤ ε₁ := hεIoc.2
  -- The foreground is positive definite (the trap hypothesis), so `galVF2` is the honest
  -- coefficient field of its DeTurck tensor.
  have hpos_u : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < (D.J ρ ε (galState D ε c)) x v v := by
    intro x v hv
    have h1 : 0 < g₀.inner x v v := g₀.pos x v hv
    have h2 := hpinch x v
    linarith
  rw [genMap_galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 c hpos_u]
  -- Abbreviate the DeTurck tensor of the foreground.
  set F : Work.Diff.STE.Bil (I := I) (M := M) :=
    Work.Diff.STE.D.deTurckSec hLC g₀ (D.J ρ ε (galState D ε c))
      (isSymm_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c)) hpos_u
      (chartData_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c)) with hF
  -- Smoothness and periodicity of the localised components of the foreground.
  have hRc : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.R i (galState D ε c) a b) :=
    fun i a b => Work.Diff.STE.B3.R_contDiff_of_chartData D (galState D ε c)
      (chartData_galState D ε hg c) i a b
  have hlev : ((k₀ : ℕ) : (WithTop ℕ∞)) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
    simpa using (le_top : ((k₀ : ℕ) : WithTop ℕ∞) ≤ ⊤)
  -- `D.BNorm k₀ (galState D ε c) ≤ C_B * B`.
  have hbn_gal : D.BNorm k₀ (galState D ε c) ≤ C_B * B := by
    have h1 := hBnd_EN (galState D ε c)
      (fun i a b =>
        (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i (galState D ε c) a b
          (hRc i a b)).1.of_le hlev)
      (fun i a b =>
        (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i (galState D ε c) a b
          (hRc i a b)).2)
    calc D.BNorm k₀ (galState D ε c)
        ≤ C_B * (D.ENormB k₀ (galState D ε c) + D.ENormB 0 (galState D ε c)) := h1
      _ = C_B * galE D k₀ ε c := by rw [galE]
      _ ≤ C_B * B := mul_le_mul_of_nonneg_left hgalE hC_B_nn
  -- `D.BNorm k₀ u~ ≤ BdeT`.
  have hbn_u : D.BNorm k₀ (D.J ρ ε (galState D ε c)) ≤ BdeT := by
    have h1 := hJN ε ⟨hεpos, hεle⟩ (galState D ε c) hRc
    calc D.BNorm k₀ (D.J ρ ε (galState D ε c))
        ≤ C_J * D.BNorm k₀ (galState D ε c) := h1
      _ ≤ C_J * (C_B * B) := mul_le_mul_of_nonneg_left hbn_gal hC_J_nn
      _ = BdeT := hBdeT.symm
  -- Smoothness/periodicity of the components of the foreground `u~`.
  have hsm_u : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i (D.J ρ ε (galState D ε c)) a b) :=
    fun i a b => (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i
      (D.J ρ ε (galState D ε c)) a b
      (Work.Diff.STE.B3.R_contDiff_of_chartData D (D.J ρ ε (galState D ε c))
        (chartData_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c)) i a b)).1
  have hper_u : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Periodic1 (D.Rper i (D.J ρ ε (galState D ε c)) a b) :=
    fun i a b => (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i
      (D.J ρ ε (galState D ε c)) a b
      (Work.Diff.STE.B3.R_contDiff_of_chartData D (D.J ρ ε (galState D ε c))
        (chartData_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c)) i a b)).2
  -- The upper pinching of the foreground `u~ ≤ K g₀`, from the uniform Sobolev pointwise bound.
  have hub : ∀ (x : M) (v : TangentSpace I x),
      (D.J ρ ε (galState D ε c)) x v v ≤ K * g₀.inner x v v := by
    intro x v
    have hpt := hpu (D.J ρ ε (galState D ε c)) hsm_u hper_u x v v
    have hsq : Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) = g₀.inner x v v :=
      Real.mul_self_sqrt (smet_inner_nn (I := I) (g := g₀) v)
    have hsqrt := Real.sqrt_le_sqrt hbn_u
    calc (D.J ρ ε (galState D ε c)) x v v
        ≤ |(D.J ρ ε (galState D ε c)) x v v| := le_abs_self _
      _ ≤ C_u * Real.sqrt (D.BNorm k₀ (D.J ρ ε (galState D ε c)))
            * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) := hpt
      _ ≤ C_u * Real.sqrt BdeT * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hsqrt hC_u_nn) (Real.sqrt_nonneg _))
            (Real.sqrt_nonneg _)
      _ = C_u * Real.sqrt BdeT
            * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) := by ring
      _ = K * g₀.inner x v v := by rw [hK, hsq]
  -- The pointwise bound on the DeTurck tensor `P u~`.
  have hFbound : ∀ (y : M) (a b : TangentSpace I y),
      |F y a b| ≤ KP * Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b) := by
    intro y a b
    have happ : F y a b = Work.Diff.STE.DeTurck.deTurckOp
        (Work.Diff.STE.D.smetOf (D.J ρ ε (galState D ε c))
          (isSymm_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c)) hpos_u
          (chartData_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c))) g₀ y a b := by
      rw [hF]
      exact Work.Diff.STE.D.deTurckSec_apply (I := I) (M := M) hLC g₀
        (D.J ρ ε (galState D ε c))
        (isSymm_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c)) hpos_u
        (chartData_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c)) y a b
    rw [happ]
    have hres := hPbound BdeT (D.J ρ ε (galState D ε c))
      (isSymm_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c)) hpos_u
      (chartData_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c))
      hbn_u hpinch hub y a b
    calc |Work.Diff.STE.DeTurck.deTurckOp
            (Work.Diff.STE.D.smetOf (D.J ρ ε (galState D ε c))
              (isSymm_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c)) hpos_u
              (chartData_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c))) g₀ y a b|
        ≤ C_P * (1 + BdeT) ^ 2 * Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b) := hres
      _ = KP * Real.sqrt (g₀.inner y a a) * Real.sqrt (g₀.inner y b b) := by
          rw [hKP]
  -- The coefficient identity `C_Jp * KP ≤ C_Jp * C_P * (1 + C_J C_B)^2 * (1+B)^2`.
  have hfac : C_Jp * KP
      ≤ (C_Jp * C_P * (1 + C_J * C_B) ^ 2) * (1 + B) * (1 + B) := by
    rw [hKP]
    have h1 : (1 : ℝ) + C_J * (C_B * B) ≤ (1 + C_J * C_B) * (1 + B) := by
      nlinarith [hC_J_nn, hC_B_nn, hB]
    have h2 : (0 : ℝ) ≤ 1 + C_J * (C_B * B) := by nlinarith [hC_J_nn, hC_B_nn, hB]
    have h4 : (1 + C_J * (C_B * B)) ^ 2 ≤ ((1 + C_J * C_B) * (1 + B)) ^ 2 :=
      pow_le_pow_left₀ h2 h1 2
    calc C_Jp * (C_P * (1 + C_J * (C_B * B)) ^ 2)
        = C_Jp * C_P * (1 + C_J * (C_B * B)) ^ 2 := by ring
      _ ≤ C_Jp * C_P * ((1 + C_J * C_B) * (1 + B)) ^ 2 :=
          mul_le_mul_of_nonneg_left h4 (mul_nonneg hC_Jp_nn hC_P_nn)
      _ = C_Jp * C_P * (1 + C_J * C_B) ^ 2 * (1 + B) * (1 + B) := by ring
  -- The final pointwise propagation through the Friedrichs mollifier.
  intro y u v
  refine (hJpl ε hεIoc F KP hKP_nn hFbound y u v).trans ?_
  calc C_Jp * KP * Real.sqrt (g₀.inner y u u) * Real.sqrt (g₀.inner y v v)
      ≤ ((C_Jp * C_P * (1 + C_J * C_B) ^ 2) * (1 + B) * (1 + B))
          * Real.sqrt (g₀.inner y u u) * Real.sqrt (g₀.inner y v v) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hfac (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    _ = (C_Jp * C_P * (1 + C_J * C_B) ^ 2) * (1 + B) * (1 + B)
          * Real.sqrt (g₀.inner y u u) * Real.sqrt (g₀.inner y v v) := rfl

end Work.Diff.STE.Lead.GalTame
