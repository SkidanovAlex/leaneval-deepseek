import Mathlib
import Submission.Work.Diff.STE.Lead.deTurck_bound
import Submission.Work.Diff.STE.Lead.GalTame.BNorm_J_le_any
import Submission.Work.Diff.STE.Lead.GalTame.J_pointwise_le_any
import Submission.Work.Diff.STE.Lead.GalTame.J_upper_bound_any
import Submission.Work.Diff.STE.Lead.Gal.Prelude
import Submission.Work.Diff.STE.Lead.Gal.Prelude2
import Submission.Work.Diff.STE.B3.BNorm_le_ENormB_unif
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv
import Submission.Work.Diff.STE.Lead.pointwise_le_sqrt_BNorm_uniform

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

/-! ## Auxiliary lemmas for `galVF2_coeff_bound`

The proof of the target runs on the coefficient side: the value `galVF2 … c` is (on the positivity
region) the coefficient family `galCoeff D ρ ε (P u~)` of the DeTurck tensor `P u~` of the
foreground `u~ = D.J ρ ε (galState D ε c)`, and every entry of `galCoeff` is half a `scoeff` of a
localised chart component of `P u~`.  The two auxiliary lemmas below are the two ends of the chain:

* `norm_le_of_forall_abs_le` — the sup norm of a coefficient vector is bounded by `C` as soon as all
  its entries are;
* `scoeff_abs_le_sup` — a Fourier coefficient of the truncation of a cube-supported function is
  bounded by the sup norm of that function (no continuity needed; `abs_scoeff_le` in
  `B3/abs_scoeff_le.lean` has the same conclusion but assumes continuity, which the DeTurck tensor
  does not obviously have). -/

/-- **The sup norm on a finite product of `ℝ`s**: it suffices to bound every entry. -/
private lemma norm_le_of_forall_abs_le {α : Type*} [Fintype α] (f : α → ℝ) {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ a, |f a| ≤ C) : ‖f‖ ≤ C :=
  (pi_norm_le_iff_of_nonneg hC).mpr fun a => by
    simpa [Real.norm_eq_abs] using h a

/-- **The mode coefficients of a cube-supported function are bounded by its sup norm.**  For a
function `f` supported in the half-open cube `(-1/2,1/2]ⁿ` and with `|f| ≤ C`, every coefficient
`scoeff n ρ ε f q` of its Friedrichs truncation is bounded by `C` in modulus, for *any* `ε` and any
multiplier `ρ` with `‖ρ‖ ≤ 1` (no restriction on `ε`, and no regularity of `f`).

The proof is the two-step chain `scoeff = ± re/im (trunc …)` and `|ρ (ε • m)| ≤ 1` ⟹
`|scoeff| ≤ ‖perCoeff …‖ ≤ C`, using `B3.abs_scoeff_perCoeffN_norm_le` (the wrapping argument for
the periodisation) for the last step. -/
private lemma scoeff_abs_le_sup {n : ℕ} (ρ : (Fin n → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (ε : ℝ) (f : (Fin n → ℝ) → ℝ)
    (hfs : Function.support f ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioc (-(1 / 2 : ℝ)) (1 / 2)))
    (C : ℝ) (hC : 0 ≤ C) (hfC : ∀ z, |f z| ≤ C) (q : Work.Diff.STE.B3.QIdx n ε) :
    |Work.Diff.STE.B3.scoeff n ρ ε f q| ≤ C := by
  have hb : ‖Work.Diff.STE.B3.perCoeffN n f q.1.1‖ ≤ C :=
    Work.Diff.STE.B3.abs_scoeff_perCoeffN_norm_le f hfs C hfC q.1.1
  have hre : |(Work.Diff.STE.B3.perCoeffN n f q.1.1).re| ≤ C :=
    (Complex.abs_re_le_norm _).trans hb
  have him : |(Work.Diff.STE.B3.perCoeffN n f q.1.1).im| ≤ C :=
    (Complex.abs_im_le_norm _).trans hb
  have hρ1 : |ρ (ε • fun i => ((q.1.1 i : ℤ) : ℝ))| ≤ 1 := by
    simpa [Real.norm_eq_abs] using hρ (ε • fun i => ((q.1.1 i : ℤ) : ℝ))
  have htrre : (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeffN n f) q.1.1).re
      = ρ (ε • fun i => ((q.1.1 i : ℤ) : ℝ))
        * (Work.Diff.STE.B3.perCoeffN n f q.1.1).re := by
    simp [Work.Diff.STE.trunc]
  have htrim : (Work.Diff.STE.trunc ρ ε (Work.Diff.STE.B3.perCoeffN n f) q.1.1).im
      = ρ (ε • fun i => ((q.1.1 i : ℤ) : ℝ))
        * (Work.Diff.STE.B3.perCoeffN n f q.1.1).im := by
    simp [Work.Diff.STE.trunc]
  cases hq : q.2
  · unfold Work.Diff.STE.B3.scoeff
    rw [hq]
    simp only [Bool.cond_false]
    rw [htrre, abs_mul]
    exact (mul_le_mul_of_nonneg_right hρ1 (abs_nonneg _)).trans (by simpa using hre)
  · unfold Work.Diff.STE.B3.scoeff
    rw [hq]
    simp only [Bool.cond_true]
    rw [htrim, abs_neg, abs_mul]
    exact (mul_le_mul_of_nonneg_right hρ1 (abs_nonneg _)).trans (by simpa using him)

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

/-! `galVF2_coeff_bound`: the span-form Galerkin vector field `galVF2` is bounded in the coefficient
sup-norm on the "trap" `{galE D k₀ ε c ≤ B} ∩ {J ρ ε (galState D ε c) ≥ (1/4) g₀}`, with a constant
uniform in `ε ∈ (0, ε₁]` (any `ε₁ > 0`).

ROUTE (as implemented).  Write `u~ := D.J ρ ε (galState D ε c)`.  Every entry of the
coefficient vector `galVF2 hLC D ρ ε hε hρ0 c` is (the `0` branch or) half a `jFamilyCoeff`, i.e. a
`Work.Diff.STE.B3.scoeff` of a chart component `D.R i (P u~) a b` of the DeTurck tensor
`P u~ = Work.Diff.STE.D.deTurckSec hLC g₀ u~ …`, so
`|scoeff ρ ε f q| ≤ sup |f|` (the last because `f` is supported in the open cube, see
`scoeff_abs_le_sup`) and it is enough to bound `P u~` pointwise.

`Work.Diff.STE.Lead.deTurck_bound` (first conjunct, hypotheses `hk₀`, `lam = 1/4`, `K`) gives
`|P u~ x u' v'| ≤ C (1 + B₁)² √(g₀ u' u') √(g₀ v' v')` for `B₁ := D.BNorm k₀ u~`, provided the
lower pinching `(1/4) g₀ ≤ u~` (the trap hypothesis) and an upper pinching `u~ ≤ K g₀`, which follows
from the Sobolev pointwise bound `Work.Diff.STE.Lead.pointwise_le_sqrt_BNorm_uniform` applied to
`h := u~` (its constant is uniform in the section).  Finally
`D.BNorm k₀ u~ ≤ C · D.BNorm k₀ (galState D ε c) ≤ C' · (D.ENormB k₀ + D.ENormB 0) (galState D ε c)
= C' · galE D k₀ ε c ≤ C' B` by `Diff/STE/Lead/GalTame/BNorm_J_le_any` and
`Work.Diff.STE.B3.BNorm_le_ENormB_unif` (in `deTurck_limit`).  `ChartData (galState D ε c)` is
`Work.Diff.STE.Lead.chartData_galState` (needs `hg`); the symmetry/positivity proof arguments of
`deTurckSec` are the canonical ones produced by `galVF2_of_pos`, so no transport is needed. -/

theorem galVF2_coeff_bound
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
      ‖Work.Diff.STE.Lead.galVF2 (I := I) (M := M) hLC D ρ ε hε hρ0 c‖ ≤ C := by
  classical
  -- `k₀ > finrank/2`: the Sobolev index condition, in the two forms used below.
  have hk2 : Fintype.card (Fin (Module.finrank ℝ E)) < 2 * k₀ := by
    rw [Fintype.card_fin]; omega
  -- The constants, all independent of `ε` and of the coefficient vector `c`.
  obtain ⟨C_B, hC_B_nn, hBnd_EN⟩ :=
    Work.Diff.STE.B3.BNorm_le_ENormB_unif (I := I) (M := M) D k₀
  obtain ⟨C_J, hC_J_nn, hJN⟩ :=
    Work.Diff.STE.Lead.GalTame.BNorm_J_le_any (I := I) (M := M) D ρ hρ k₀ ε₁ hε₁
  obtain ⟨d₀, hd₀pos, hd₀le⟩ :=
    Work.Diff.STE.B3.dens_lower_bound (I := I) (M := M) D
      (fun i => Work.Diff.STE.B3.densGood (I := I) (M := M) D i)
  obtain ⟨C_u, hC_u_nn, hpu⟩ :=
    Work.Diff.STE.Lead.pointwise_le_sqrt_BNorm_uniform (I := I) (M := M) D k₀ hk2
      ⟨d₀, hd₀pos, hd₀le⟩
  obtain ⟨c_dens, C_dens, hc_dens_pos, hC_dens_pos, hdens_sigma⟩ :=
    Work.Diff.STE.B3.dens_bound_sigma (I := I) (M := M) D
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
  set Cf : ℝ := (1 / 2) * Real.sqrt C_dens * KP with hCf
  have hCf_nn : 0 ≤ Cf := by
    rw [hCf, hKP]
    exact mul_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))
      (mul_nonneg hC_P_nn (sq_nonneg _))
  refine ⟨Cf, hCf_nn, ?_⟩
  intro ε hεIoc hε c hgalE hpinch
  obtain ⟨hεpos, hεle⟩ := hεIoc
  -- The foreground is positive definite (the trap hypothesis), so `galVF2` is the honest
  -- coefficient field of its DeTurck tensor.
  have hpos_u : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < (D.J ρ ε (galState D ε c)) x v v := by
    intro x v hv
    have h1 : 0 < g₀.inner x v v := g₀.pos x v hv
    have h2 := hpinch x v
    linarith
  rw [galVF2_of_pos (I := I) (M := M) hLC D ρ ε hε hρ0 c hpos_u]
  -- Abbreviate the DeTurck tensor of the foreground.
  set F : Work.Diff.STE.Bil (I := I) (M := M) :=
    Work.Diff.STE.D.deTurckSec hLC g₀ (D.J ρ ε (galState D ε c))
      (isSymm_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c)) hpos_u
      (chartData_J D ρ ε hε hρ0 (galState D ε c) (isSymm_galState D ε c)) with hF
  -- Smoothness and periodicity of the localised components of the foreground and of `g₀`.
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
  -- The sup bound on the localised chart components of `P u~`.
  have hRle : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (w : Fin (Module.finrank ℝ E) → ℝ), |D.R i F a b w| ≤ Real.sqrt C_dens * KP :=
    fun i a b w => Work.Diff.STE.Lead.R_abs_le D F KP C_dens hKP_nn hC_dens_pos
      (fun i z hz => (hdens_sigma i z hz).2) hFbound i a b w
  -- Every coefficient of `galCoeff D ρ ε F` is bounded by `Cf`.
  have hcomp : ∀ z : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε,
      |galCoeff D ρ ε F z| ≤ Cf := by
    intro z
    have hsc : |Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
        (D.R z.1 F z.2.1 z.2.2.1) z.2.2.2| ≤ Real.sqrt C_dens * KP := by
      refine scoeff_abs_le_sup ρ hρ ε (D.R z.1 F z.2.1 z.2.2.1) ?_ (Real.sqrt C_dens * KP)
        (mul_nonneg (Real.sqrt_nonneg _) hKP_nn) ?_ z.2.2.2
      · intro w hw
        have h1 := Work.Diff.STE.B3Data.R_support D z.1 F z.2.1 z.2.2.1 hw
        rw [Set.mem_pi] at h1 ⊢
        exact fun j _ => Set.Ioo_subset_Ioc_self (h1 j (Set.mem_univ j))
      · exact hRle z.1 z.2.1 z.2.2.1
    simp only [galCoeff, Work.Diff.STE.B3.jFamilyCoeff, abs_mul]
    rw [abs_of_pos (show (0 : ℝ) < 1 / 2 by norm_num)]
    calc (1 / 2) * |Work.Diff.STE.B3.scoeff (Module.finrank ℝ E) ρ ε
          (D.R z.1 F z.2.1 z.2.2.1) z.2.2.2|
        ≤ (1 / 2) * (Real.sqrt C_dens * KP) :=
          mul_le_mul_of_nonneg_left hsc (by norm_num)
      _ = Cf := by rw [hCf]; ring
  exact norm_le_of_forall_abs_le (galCoeff D ρ ε F) hCf_nn hcomp

end Work.Diff.STE.Lead.GalTame
