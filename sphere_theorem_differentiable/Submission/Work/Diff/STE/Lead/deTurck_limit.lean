import Mathlib
import Submission.Diff.STEGal
import Submission.Work.Diff.STE.flat.exists_subseq_uniform
import Submission.Work.Diff.STE.star_seriesFun
import Submission.Work.Diff.STE.flat.fourierCoeff_seriesFun
import Submission.Work.Diff.STE.Lead.seriesFun_re_contDiff_periodic
import Submission.Work.Diff.STE.Lead.transfer_tendsto
import Submission.Work.Diff.STE.Lead.transfer_CSq_le
import Submission.Work.Diff.STE.Lead.chartData_sum_Rstar
import Submission.Work.Diff.STE.B3.Pointwise
import Submission.Work.Diff.STE.B3.dens_bound_sigma
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.B3.Rstar_R_eq_zeta_sq_free
import Submission.Work.Diff.STE.D.ChartData_Rstar
import Submission.Work.Diff.STE.B3.STruncR_CSq_le
import Submission.Work.Diff.STE.B3.BNorm_J_sub_le
import Submission.Work.Diff.STE.Lead.coeffFun_bound_and_decay
import Submission.Work.Diff.STE.Lead.BNorm_tendsto_of_coeff_tendsto
import Submission.Work.Diff.STE.Lead.BNorm_le_of_coeff_tendsto
import Submission.Work.Diff.STE.Lead.smet_pos_of_BNorm_tendsto
import Submission.Work.Diff.STE.Lead.sub_eq_integral_of_hasDerivWithinAt
import Submission.Work.Diff.STE.Lead.galState_lipschitz
import Submission.Work.Diff.STE.Lead.coeffFun_lipschitz_of_ode
import Submission.Work.Diff.STE.Lead.hasDerivWithinAt_of_sub_eq_integral
import Submission.Work.Diff.STE.Lead.deTurck_bound
import Submission.Work.Diff.STE.Lead.galState_J_props
import Submission.Work.Diff.STE.Lead.BNorm_zero_le_of_pointwise
import Submission.Work.Diff.STE.Lead.fourierCoeff_le_sqrt_BNorm
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv
import Submission.Work.Diff.STE.B3.transport_Rres_contDiffOn
import Submission.Work.Diff.STE.Lead.limit_positivity
import Submission.Work.Diff.STE.Lead.J_pointwise_le
import Submission.Work.Diff.STE.B3.dens_lower_bound
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.Lead.limit_coeff_hasDerivWithinAt
import Submission.Work.Diff.STE.Lead.pointwise_hasDerivWithinAt_of_coeff
import Submission.Work.Diff.STE.Lead.coeff_tendsto_galRHS
import Submission.Work.Diff.STE.Lead.fourierCoeff_vs_aemeasurable
import Submission.Work.Diff.STE.Lead.jointSmooth_of_solves_deTurck
import Submission.Work.Diff.STE.Lead.deTurckVec_jointField_within
import Submission.Work.Diff.STE.Lead.continuous_deTurckSec_R
import Submission.Work.Diff.STE.Lead.continuous_fourierCoeff_deTurckSec
import Submission.Work.Diff.STE.Lead.coeff_decay_of_BNorm_le
import Submission.Work.Diff.STE.Lead.mat_jet_uniform_bound
import Submission.Work.Diff.STE.Lead.pointwise_le_sqrt_BNorm_uniform
import Submission.Work.Diff.STE.Lead.BNorm_deTurckSec_le
import Submission.Work.Diff.STE.Lead.BNorm_add_le
import Submission.Work.Diff.STE.Lead.isSymm_of_BNorm_tendsto
import Submission.Work.Diff.STE.Lead.BNorm_continuous_of_coeff_lipschitz
import Submission.Work.Diff.STE.B3.mat_jet_bound_of_energy
import Submission.Work.Diff.STE.B3.Pair

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 4000000

/-! Guidance from the project lead (the requester):

CONTEXT: last layer of short_time_existence (owner H10, Diff/STE). The lead dispatched these pieces top-level so they run in parallel.
Vocabulary: Submission/Work/Diff/STE/B3/Comp.lean (R, Rper, CPair, BPair, BNorm, Rstar, STruncR, J), B3/Data.lean (B3Data: x₀, χ, ζ, e, dens,
psi), D/* (Galerkin, genMap, jSym, addSec, deTurckSec, ChartData, smetOf), and the lead's Submission/Diff/STEGal.lean (galState, IsGalSol,
GalUniform). REUSE the PROVED Layer A toolkit (Submission/Work/Diff/STE/*.lean; LayerA.lean lists it): CSq_trunc_le,
CSq_trunc_sub_le, friedrichs_commutator, CSq_period_comp_arg_le, CSq_conv_tame_le, CSq_comp_le, garding_vec_uniform,
gronwall_linear_bound, norm_seriesFun_le (Sobolev), CSq_tail_le (compactness), eq_zero_of_fourierCoeff_eq_zero, BPair_J_self,
BPair_Rstar, J_finite_rank, R_Rstar_expansion2 (chart transfer). Read DESIGN.md (sessions 6–8) first. Do not re-prove anything listed.
If a statement here is false as stated (e.g. a missing hypothesis on ρ or on B3Data), declare_false with the precise reason; the lead fixes it.
ROUTE (deTurck_limit: ε → 0 limit, uniqueness, identification of the equation).
1. From GalUniform: for each ε a solution u_ε on [0,τ₀] with ε-uniform BNorm k bounds for every k and ∂ₜu_ε bounded in BNorm (k−2)
   (the equation). Compactness: CSq_tail_le (Rellich on the torus) plus the time-Lipschitz bound give a subsequence converging in
   C([0,τ₀]; BNorm k) for every k (diagonal argument, or Cauchy via uniqueness).
2. Uniqueness for the limit equation ∂ₜu = P(u) (the DeTurck system: scalar principal part, so the L² energy of the difference of two
   smooth solutions obeys Grönwall). Hence the whole family converges and the limit u is unique.
3. The limit is C^∞ in x (all levels bounded, Sobolev) and C^∞ in t (time derivatives expressed through x-derivatives by the
   equation). It is positive (lam margin), with ChartData. Package it with smetOf as G t; G 0 = g₀ (u_ε(0) = g₀).
   JointSmooth G (Icc 0 τ) with τ := τ₀.
4. Pass to the limit in IsGalSol: J → id (hJT) and J P(J u_ε) → P(u) in every level, so ∂ₜu = P(u) = deTurckSec(u).
   The DeTurck identity deTurckSec = −2Ric + L_{W(u)} u with W = DeTurck.deTurckVec u g₀ is the spec of D/deTurckCLM.lean
   (Classical.choose_spec) together with the proved C1 bridge (Man/chartNonlin_eq_pPhiJet, deTurck.chartLieMat_eq_lieJet,
   EXT.chartRicMat_ricPhi). This gives the displayed HasDerivWithinAt (the Lie derivative written with lcOf, torsion-free).
5. W smooth on Icc 0 τ × M: deTurckVec is a smooth expression in the jets of G (chart components deTurckChartComp).
File 1–5 as separate exact sub-lemmas at once.
-/

namespace Work.Diff.STE.Lead

set_option maxHeartbeats 32000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg Submission.Diff.STEGal
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **The Galerkin family extracted from `GalUniform`**, indexed by `m : ℕ` with
`ε m = ε₀ / (m + 2) → 0` (so `ε m ∈ (0, ε₀]`), together with the uniform `BNorm` estimates and
the positivity margin.  This is the sequence along which the `ε → 0⁺` limit is taken. -/
theorem exists_gal_family
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hLC : LCSmooth I M)
    (hGU : GalUniform hLC D ρ) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∃ lam : ℝ, 0 < lam ∧ ∃ B : ℕ → ℝ,
      ∀ m : ℕ,
        ∃ c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) (ε₀ / ((m : ℝ) + 2)) → ℝ),
          IsGalSol hLC D ρ (ε₀ / ((m : ℝ) + 2)) τ₀ c ∧
            (∀ t ∈ Icc (0 : ℝ) τ₀,
              (∀ k : ℕ, D.BNorm k (galState D (ε₀ / ((m : ℝ) + 2)) (c t)) ≤ B k) ∧
              ∀ (x : M) (v : TangentSpace I x),
                lam * g₀.inner x v v
                  ≤ (D.J ρ (ε₀ / ((m : ℝ) + 2))
                      (galState D (ε₀ / ((m : ℝ) + 2)) (c t))) x v v) := by
  obtain ⟨ε₀, hε₀, τ₀, hτ₀, lam, hlam, B, hB⟩ := hGU
  refine ⟨ε₀, hε₀, τ₀, hτ₀, lam, hlam, B, fun m => ?_⟩
  have hpos : (0 : ℝ) < ((m : ℝ) + 2) := by positivity
  have h1 : (1 : ℝ) ≤ ((m : ℝ) + 2) := by
    have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    linarith
  have hmpos : (0 : ℝ) < ε₀ / ((m : ℝ) + 2) := div_pos hε₀ hpos
  have hmle : ε₀ / ((m : ℝ) + 2) ≤ ε₀ := by
    rw [div_le_iff₀ hpos]
    exact le_mul_of_one_le_right hε₀.le h1
  exact hB (ε₀ / ((m : ℝ) + 2)) ⟨hmpos, hmle⟩

/-- **The coefficient functions of the components** — the objects the compactness step runs on:
for the state `u m t`, the entry `(a,b)` of the chart-`i` localised component, and the frequency
`μ`, the Fourier coefficient `fourierCoeff (D.Rper i (u m t) a b) μ`. -/
noncomputable def coeffFun
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ)
    (m : ℕ) (t : ℝ) : ℂ :=
  Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ

/-- **The diagonal extraction `φ` of the compactness step** (the coefficient half of
`exists_subseq_coeff_limit`, independent of the equations): a uniformly bounded and uniformly
Lipschitz-in-`t` family of coefficient functions has a subsequence along which every coefficient
function converges uniformly on `[0, τ₀)`.  This is `Work.Diff.STE.flat.exists_subseq_uniform`
applied to the index type `ι₀ × n × n × ℤⁿ` of `(chart, matrix entry, frequency)`. -/
theorem exists_subseq_coeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (τ₀ : ℝ)
    (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M)) (hτ : 0 < τ₀)
    (Lb Ll : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℤ) → ℝ)
    (hLb : ∀ i a b μ, 0 ≤ Lb i a b μ) (hLl : ∀ i a b μ, 0 ≤ Ll i a b μ)
    (hbdd : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ)
      (m : ℕ) (t : ℝ), t ∈ Ico (0 : ℝ) τ₀ →
        ‖coeffFun (I := I) (M := M) D u i a b μ m t‖ ≤ Lb i a b μ)
    (hlip : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ)
      (m : ℕ), ∀ t ∈ Ico (0 : ℝ) τ₀, ∀ t' ∈ Ico (0 : ℝ) τ₀,
        ‖coeffFun (I := I) (M := M) D u i a b μ m t
          - coeffFun (I := I) (M := M) D u i a b μ m t'‖ ≤ Ll i a b μ * |t - t'|) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ∃ g : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
          (Fin (Module.finrank ℝ E) → ℤ) → ℝ → ℂ,
        ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
          TendstoUniformlyOn
            (fun (m : ℕ) (t : ℝ) => coeffFun (I := I) (M := M) D u i a b μ (φ m) t)
            (g i a b μ) Filter.atTop (Ico (0 : ℝ) τ₀) := by
  classical
  obtain ⟨φ, hφ, g, hg⟩ := Work.Diff.STE.flat.exists_subseq_uniform
    (ι := ι₀ × Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E) ×
      (Fin (Module.finrank ℝ E) → ℤ)) hτ
    (fun p => max (Lb p.1 p.2.1 p.2.2.1 p.2.2.2) (Ll p.1 p.2.1 p.2.2.1 p.2.2.2))
    (fun p => le_trans (hLb p.1 p.2.1 p.2.2.1 p.2.2.2) (le_max_left _ _))
    (fun m p t => coeffFun (I := I) (M := M) D u p.1 p.2.1 p.2.2.1 p.2.2.2 m t)
    (fun p m t ht => le_trans (hbdd p.1 p.2.1 p.2.2.1 p.2.2.2 m t ht) (le_max_left _ _))
    (fun p m t ht t' ht' => le_trans (hlip p.1 p.2.1 p.2.2.1 p.2.2.2 m t ht t' ht')
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (abs_nonneg _)))
  exact ⟨φ, hφ, fun i a b μ t => g (i, a, b, μ) t, fun i a b μ => hg (i, a, b, μ)⟩

/-- The **component families of the limit**: the Fourier series of the coefficient limits `g`
(the objects whose smoothness is `contDiff_seriesFun` applied to the rapid decay `hdec`). -/
noncomputable def limComp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀]
    (g : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℤ) → ℝ → ℂ) (i : ι₀) (t : ℝ) :
    Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → (Fin (Module.finrank ℝ E) → ℝ) → ℝ :=
  fun a b z => (Work.Diff.STE.seriesFun (fun μ => g i a b μ t) z).re

/-- The **limit section** of the compactness step: the reconstruction of `limComp` in the charts. -/
noncomputable def limSect
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (g : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℤ) → ℝ → ℂ) (t : ℝ) :
    Work.Diff.STE.Bil (I := I) (M := M) :=
  ∑ i : ι₀, D.Rstar i (limComp (I := I) (M := M) g i t)

/-- **The real part of a `ℂ`-number fixed by conjugation, as a complex number.** -/
lemma ofReal_re_of_star_self {w : ℂ} (hw : star w = w) : ((w.re : ℝ) : ℂ) = w := by
  rw [Work.Diff.STE.B3.ofReal_re_eq, hw]
  ring

/-- **Conjugation commutes with the integral over the unit cube.** -/
lemma star_integral_unitCube {n : ℕ} (g : (Fin n → ℝ) → ℂ) :
    star (∫ x in Work.Diff.STE.unitCube, g x)
      = ∫ x in Work.Diff.STE.unitCube, star (g x) := by
  have h := integral_conj (f := g)
    (μ := MeasureTheory.volume.restrict (Work.Diff.STE.unitCube (ι := Fin n)))
  simpa only [Complex.star_def] using h.symm

/-- **The periodised component is real-valued** (it is a lattice sum of complexified real
numbers), so it is fixed by complex conjugation. -/
lemma Rper_star_self
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (i : ι₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (a b : Fin (Module.finrank ℝ E))
    (z : Fin (Module.finrank ℝ E) → ℝ) :
    star (D.Rper i h a b z) = D.Rper i h a b z := by
  have hrepr : D.Rper i h a b z = ((∑' m : Fin (Module.finrank ℝ E) → ℤ,
      D.R i h a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ) := by
    show (∑' m : Fin (Module.finrank ℝ E) → ℤ,
      ((D.R i h a b (z + Work.Diff.STE.iVec m) : ℝ) : ℂ)) = _
    rw [Complex.ofReal_tsum]
  rw [hrepr]
  exact Complex.conj_ofReal _

/-- **Conjugate symmetry of the Fourier coefficients of a real-valued function.** -/
lemma star_fourierCoeff_of_star_self {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    (hf : ∀ z, star (f z) = f z) (μ : Fin n → ℤ) :
    star (Work.Diff.STE.fourierCoeff f μ) = Work.Diff.STE.fourierCoeff f (-μ) := by
  rw [Work.Diff.STE.fourierCoeff, star_integral_unitCube]
  rw [Work.Diff.STE.fourierCoeff]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show star (Work.Diff.STE.fourierExp (-μ) x * f x)
    = Work.Diff.STE.fourierExp (-(-μ)) x * f x
  rw [star_mul, star_fourierExp, hf x]
  ring

/-- **Conjugate symmetry of the coefficient functions of a section** (the periodised component is
real-valued). -/
lemma coeffFun_star_neg
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ)
    (m : ℕ) (t : ℝ) :
    star (coeffFun (I := I) (M := M) D u i a b μ m t)
      = coeffFun (I := I) (M := M) D u i a b (-μ) m t :=
  star_fourierCoeff_of_star_self (fun z => Rper_star_self (I := I) (M := M) D i (u m t) a b z) μ

/-- **The Fourier coefficient of the real part of a Fourier series**.  For a conjugate-symmetric
coefficient family `c`, the real part `Re (seriesFun c)` is `seriesFun c` itself, so its
coefficients are the `c k`. -/
lemma fourierCoeff_seriesFun_re {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : (ι → ℤ) → ℂ) (hc : Summable (fun k => ‖c k‖))
    (hcs : ∀ k : ι → ℤ, star (c (-k)) = c k) (ν : ι → ℤ) :
    Work.Diff.STE.fourierCoeff
      (fun z => (((Work.Diff.STE.seriesFun c z).re : ℝ) : ℂ)) ν = c ν := by
  have hreal : ∀ z : ι → ℝ,
      ((Work.Diff.STE.seriesFun c z).re : ℝ) = Work.Diff.STE.seriesFun c z := by
    intro z
    have hfix : star (Work.Diff.STE.seriesFun c z) = Work.Diff.STE.seriesFun c z := by
      rw [Work.Diff.STE.star_seriesFun c hc z]
      exact tsum_congr fun k => by
        show star (c (-k)) * Work.Diff.STE.fourierExp k z = c k * Work.Diff.STE.fourierExp k z
        rw [hcs k]
    exact ofReal_re_of_star_self hfix
  have hfun : (fun z : ι → ℝ => (((Work.Diff.STE.seriesFun c z).re : ℝ) : ℂ))
      = Work.Diff.STE.seriesFun c := funext hreal
  rw [hfun]
  exact Work.Diff.STE.flat.fourierCoeff_seriesFun c hc ν

/-- **The localised component is additive over finite sums of sections.** -/
lemma R_finset_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (X : ι₀ → Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) :
    D.R i (∑ j, X j) a b = ∑ j, D.R i (X j) a b := by
  funext z
  simp only [Work.Diff.STE.B3Data.R, Work.Diff.STE.B3Data.mat, Finset.sum_apply,
    ContinuousLinearMap.sum_apply, Finset.mul_sum]

/-- **The Fourier coefficients of the periodised component are additive in the section.** -/
lemma fourierCoeff_Rper_finset_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (X : ι₀ → Work.Diff.STE.Bil (I := I) (M := M)) (i : ι₀)
    (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ)
    (hsm : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (D.R i (X j) a b)) :
    Work.Diff.STE.fourierCoeff (D.Rper i (∑ j, X j) a b) μ
      = ∑ j, Work.Diff.STE.fourierCoeff (D.Rper i (X j) a b) μ := by
  have hsm_sum : ContDiff ℝ (⊤ : ℕ∞) (D.R i (∑ j, X j) a b) := by
    have h : D.R i (∑ j, X j) a b = fun x => ∑ j, D.R i (X j) a b x := by
      rw [R_finset_sum]
      funext x
      exact Finset.sum_apply x Finset.univ (fun j => D.R i (X j) a b)
    rw [h]
    exact ContDiff.sum (s := Finset.univ) (fun j _ => hsm j)
  rw [Work.Diff.STE.Lead.Rper_fourierCoeff_eq_integral D _ i a b μ hsm_sum]
  have hpt : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
      Work.Diff.STE.fourierExp (-μ) z * ((D.R i (∑ j, X j) a b z : ℝ) : ℂ)
        = ∑ j, Work.Diff.STE.fourierExp (-μ) z * ((D.R i (X j) a b z : ℝ) : ℂ) := by
    intro z
    rw [R_finset_sum, Finset.sum_apply, Complex.ofReal_sum, Finset.mul_sum]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpt),
    MeasureTheory.integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [Work.Diff.STE.Lead.Rper_fourierCoeff_eq_integral D _ i a b μ (hsm j)]
  · intro j _
    refine ((Work.Diff.STE.Lead.integrable_R_ofReal D (X j) i a b (hsm j)).mul_bdd
      ((Work.Diff.STE.continuous_fourierExp (-μ)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => by rw [Work.Diff.STE.norm_fourierExp])).congr
      (Filter.Eventually.of_forall fun z => mul_comm _ _)

/-- **`R_j^*` of the real part of the periodisation is `R_j^*` of the component.**  The point is
that `R_j^*` only evaluates its argument at the flat coordinates `coord (x₀ j) p`, and on the
support of the weight `ζ j` those lie in the open unit cube, where the periodisation agrees with
the component. -/
lemma Rstar_Rper_re_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) :
    D.Rstar j (fun a b z => (D.Rper j h a b z).re)
      = D.Rstar j (fun a b z => D.R j h a b z) := by
  funext p
  ext X Y
  rw [Work.Diff.STE.B3.Rstar_apply, Work.Diff.STE.B3.Rstar_apply]
  by_cases hz : D.ζ j p = 0
  · simp only [hz, zero_mul]
  · have hcoord := D.hζsupp j p hz
    have hcube : ∀ k : Fin (Module.finrank ℝ E),
        Work.Diff.STE.coord (I := I) (D.x₀ j) p k ∈ Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) := by
      intro k
      have h1 : |Work.Diff.STE.coord (I := I) (D.x₀ j) p k|
          ≤ ‖Work.Diff.STE.coord (I := I) (D.x₀ j) p‖ := by
        simpa only [Real.norm_eq_abs] using
          norm_le_pi_norm (Work.Diff.STE.coord (I := I) (D.x₀ j) p) k
      have hlt : ‖Work.Diff.STE.coord (I := I) (D.x₀ j) p‖ < 1 / 2 := by
        have h2 := D.hσ2 j
        linarith [hcoord.2]
      have h2 : |Work.Diff.STE.coord (I := I) (D.x₀ j) p k| < 1 / 2 :=
        lt_of_le_of_lt h1 hlt
      exact ⟨by linarith [(abs_lt.mp h2).1], by linarith [(abs_lt.mp h2).2]⟩
    congr 1
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [Work.Diff.STE.B3Data.Rper_eq_R D j h a b hcube, Complex.ofReal_re]

/-- **The Fourier coefficient of the real part of a periodised component is the coefficient of the
component** (the periodisation of a real-valued function is real-valued). -/
lemma coeffFun_re_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ)
    (m : ℕ) (t : ℝ) :
    Work.Diff.STE.fourierCoeff (fun z => (((D.Rper i (u m t) a b z).re : ℝ) : ℂ)) μ
      = coeffFun (I := I) (M := M) D u i a b μ m t := by
  have h : (fun z => (((D.Rper i (u m t) a b z).re : ℝ) : ℂ)) = D.Rper i (u m t) a b :=
    funext fun z => ofReal_re_of_star_self (Rper_star_self (I := I) (M := M) D i (u m t) a b z)
  rw [h]
  rfl

/-- **The Fourier coefficients of `limComp`** (the real part of the limit series) are the limit
coefficients `g`, provided the latter are conjugate-symmetric. -/
lemma limComp_fourierCoeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀]
    (g : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℤ) → ℝ → ℂ)
    (τ₀ : ℝ)
    (hgcs : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ) (t : ℝ), t ∈ Ico (0 : ℝ) τ₀ →
        star (g i a b (-μ) t) = g i a b μ t)
    (hdec : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ) (t : ℝ), t ∈ Ico (0 : ℝ) τ₀ →
        ‖g i a b μ t‖ * (Work.Diff.STE.wt μ) ^ M ≤ C)
    (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ) (t : ℝ)
    (ht : t ∈ Ico (0 : ℝ) τ₀) :
    Work.Diff.STE.fourierCoeff
      (fun z => (((limComp (I := I) (M := M) g i t a b z : ℝ) : ℂ))) μ = g i a b μ t := by
  set N : ℕ := Module.finrank ℝ E + 1 with hN
  obtain ⟨C, hC, hCb⟩ := hdec N
  have hmaj : Summable (fun ν : Fin (Module.finrank ℝ E) → ℤ =>
      C * ((Work.Diff.STE.wt ν) ^ N)⁻¹) := by
    simpa only [zpow_neg, zpow_natCast] using
      (Work.Diff.STE.summable_wt_zpow (ι := Fin (Module.finrank ℝ E)) N
        (by simp only [Fintype.card_fin]; omega)).mul_left C
  have hle : ∀ ν : Fin (Module.finrank ℝ E) → ℤ,
      ‖g i a b ν t‖ ≤ C * ((Work.Diff.STE.wt ν) ^ N)⁻¹ := by
    intro ν
    have h := hCb i a b ν t ht
    have hw : 0 < (Work.Diff.STE.wt ν) ^ N := pow_pos (Work.Diff.STE.wt_pos ν) N
    have h2 : ‖g i a b ν t‖ ≤ C / (Work.Diff.STE.wt ν) ^ N :=
      (le_div_iff₀ hw).mpr h
    rwa [div_eq_mul_inv] at h2
  exact fourierCoeff_seriesFun_re (fun ν => g i a b ν t)
    (Summable.of_nonneg_of_le (fun ν => norm_nonneg _) hle hmaj)
    (fun ν => hgcs i a b ν t ht) μ

/-- **Closing `hT`: the interface of `exists_limit_section` without the transfer hypothesis.**

The transfer-continuity hypothesis of `exists_limit_section` is supplied internally, for each
`t ∈ Ico 0 τ₀`, by `Work.Diff.STE.Lead.transfer_tendsto` (applied to the *periodisations* of the
components, which agree with the components on the support of `ζ j`), the transfer estimate
`Work.Diff.STE.Lead.transfer_CSq_le`, and the two extra inputs: the *decay* of the coefficients of
the sequence (`hdecM`, from the uniform `BNorm` bounds) and the *conjugate symmetry* of the limit
coefficient family (`hgcs`, from the fact that the sequence's components are real-valued). -/
theorem exists_limit_section_closed
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (τ₀ : ℝ)
    (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (φ : ℕ → ℕ)
    (g : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℤ) → ℝ → ℂ)
    (hCD : ∀ (m : ℕ) (t : ℝ), t ∈ Ico (0 : ℝ) τ₀ →
      Work.Diff.STE.D.ChartData (I := I) (M := M) (u m t))
    (hgcs : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ) (t : ℝ), t ∈ Ico (0 : ℝ) τ₀ →
        star (g i a b (-μ) t) = g i a b μ t)
    (hdec : ∀ M : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ) (t : ℝ), t ∈ Ico (0 : ℝ) τ₀ →
        ‖g i a b μ t‖ * (Work.Diff.STE.wt μ) ^ M ≤ C)
    (hdecM : ∀ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ) (t : ℝ), t ∈ Ico (0 : ℝ) τ₀ →
        ‖coeffFun (I := I) (M := M) D u i a b μ m t‖ * (Work.Diff.STE.wt μ) ^ K ≤ C)
    (hconv : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      TendstoUniformlyOn
        (fun (m : ℕ) (t : ℝ) => coeffFun (I := I) (M := M) D u i a b μ (φ m) t)
        (g i a b μ) Filter.atTop (Ico (0 : ℝ) τ₀)) :
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ) (t : ℝ),
        t ∈ Ico (0 : ℝ) τ₀ →
        Work.Diff.STE.fourierCoeff
          (D.Rper i (limSect (I := I) (M := M) D g t) a b) μ = g i a b μ t := by
  classical
  intro i a b μ t ht
  -- ### smoothness and periodicity of the two families of component functions, at time `t`
  have hsmS : ∀ (m : ℕ) (j : ι₀) (c d : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (fun z => (D.Rper j (u (φ m) t) c d z).re) := by
    intro m j c d
    exact Complex.reCLM.contDiff.comp
      (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D j (u (φ m) t) c d
        (Work.Diff.STE.B3.R_contDiff_of_chartData D _ (hCD (φ m) t ht) j c d)).1
  have hperS : ∀ (m : ℕ) (j : ι₀) (c d : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.Periodic1 (fun z => (D.Rper j (u (φ m) t) c d z).re) := by
    intro m j c d x y
    refine congrArg Complex.re ?_
    exact (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D j (u (φ m) t) c d
      (Work.Diff.STE.B3.R_contDiff_of_chartData D _ (hCD (φ m) t ht) j c d)).2 x y
  have hsmL : ∀ (j : ι₀) (c d : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (limComp (I := I) (M := M) g j t c d) :=
    fun j c d => (Work.Diff.STE.Lead.seriesFun_re_contDiff_periodic
      (I := I) (M := M) τ₀ g hdec j c d t ht).1
  have hperL : ∀ (j : ι₀) (c d : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.Periodic1 (limComp (I := I) (M := M) g j t c d) :=
    fun j c d => (Work.Diff.STE.Lead.seriesFun_re_contDiff_periodic
      (I := I) (M := M) τ₀ g hdec j c d t ht).2
  -- ### the transfer step: `Rper i (Rstar j (periodised component))` converges coefficientwise
  have hstep : ∀ j : ι₀,
      Filter.Tendsto (fun m : ℕ => Work.Diff.STE.fourierCoeff
          (D.Rper i (D.Rstar j (fun c d z => (D.Rper j (u (φ m) t) c d z).re)) a b) μ)
        Filter.atTop
        (nhds (Work.Diff.STE.fourierCoeff
          (D.Rper i (D.Rstar j (limComp (I := I) (M := M) g j t)) a b) μ)) := by
    intro j
    refine Work.Diff.STE.Lead.transfer_tendsto (I := I) (M := M) D i j a b μ
      (fun m c d z => (D.Rper j (u (φ m) t) c d z).re)
      (limComp (I := I) (M := M) g j t)
      (fun m c d => hsmS m j c d) (fun m c d => hperS m j c d)
      (fun c d => hsmL j c d) (fun c d => hperL j c d)
      (fun k hk => Work.Diff.STE.Lead.transfer_CSq_le (I := I) (M := M) D i j a b k hk)
      ?_ ?_
    · intro K
      obtain ⟨C₁, hC₁, hC₁b⟩ := hdecM K
      obtain ⟨C₂, hC₂, hC₂b⟩ := hdec K
      refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun m c d ν => ⟨?_, ?_⟩⟩
      · rw [coeffFun_re_eq]
        exact le_trans (hC₁b (φ m) j c d ν t ht) (le_max_left _ _)
      · rw [limComp_fourierCoeff (I := I) (M := M) g τ₀ hgcs hdec j c d ν t ht]
        exact le_trans (hC₂b j c d ν t ht) (le_max_right _ _)
    · intro c d ν
      have hfun : (fun m : ℕ => Work.Diff.STE.fourierCoeff
            (fun z => (((D.Rper j (u (φ m) t) c d z).re : ℝ) : ℂ)) ν)
          = fun m : ℕ => coeffFun (I := I) (M := M) D u j c d ν (φ m) t :=
        funext fun m => coeffFun_re_eq (I := I) (M := M) D u j c d ν (φ m) t
      rw [hfun]
      rw [limComp_fourierCoeff (I := I) (M := M) g τ₀ hgcs hdec j c d ν t ht]
      exact (hconv j c d ν).tendsto_at ht
  -- ### linearity of the Fourier coefficient over the finite sum of the reconstruction
  have h1 : ∀ m : ℕ,
      Work.Diff.STE.fourierCoeff (D.Rper i (u (φ m) t) a b) μ
        = ∑ j, Work.Diff.STE.fourierCoeff
            (D.Rper i (D.Rstar j (fun c d z => (D.Rper j (u (φ m) t) c d z).re)) a b) μ := by
    intro m
    have hsum_eq : (∑ j : ι₀, D.Rstar j (fun c d z => (D.Rper j (u (φ m) t) c d z).re))
        = u (φ m) t := by
      conv_rhs => rw [← Work.Diff.STE.B3.Rstar_R_eq_id D (u (φ m) t)]
      exact Finset.sum_congr rfl fun j _ => Rstar_Rper_re_eq (I := I) (M := M) D j (u (φ m) t)
    conv_lhs => rw [← hsum_eq]
    refine fourierCoeff_Rper_finset_sum D _ i a b μ (fun j => ?_)
    exact Work.Diff.STE.B3.R_contDiff_of_chartData D _
      (Work.Diff.STE.D.ChartData_Rstar D j _ (fun c d => hsmS m j c d)) i a b
  have h2 : Work.Diff.STE.fourierCoeff
      (D.Rper i (limSect (I := I) (M := M) D g t) a b) μ
        = ∑ j, Work.Diff.STE.fourierCoeff
            (D.Rper i (D.Rstar j (limComp (I := I) (M := M) g j t)) a b) μ := by
    refine fourierCoeff_Rper_finset_sum D _ i a b μ (fun j => ?_)
    exact Work.Diff.STE.B3.R_contDiff_of_chartData D _
      (Work.Diff.STE.D.ChartData_Rstar D j _ (fun c d => hsmL j c d)) i a b
  -- ### passing to the limit
  have h3 : Filter.Tendsto (fun m : ℕ => ∑ j : ι₀, Work.Diff.STE.fourierCoeff
      (D.Rper i (D.Rstar j (fun c d z => (D.Rper j (u (φ m) t) c d z).re)) a b) μ)
      Filter.atTop (nhds (∑ j : ι₀, Work.Diff.STE.fourierCoeff
        (D.Rper i (D.Rstar j (limComp (I := I) (M := M) g j t)) a b) μ)) :=
    tendsto_finsetSum Finset.univ fun j _ => hstep j
  have hA : Filter.Tendsto
      (fun m : ℕ => Work.Diff.STE.fourierCoeff (D.Rper i (u (φ m) t) a b) μ)
      Filter.atTop (nhds (g i a b μ t)) :=
    (hconv i a b μ).tendsto_at ht
  have hB : Filter.Tendsto
      (fun m : ℕ => Work.Diff.STE.fourierCoeff (D.Rper i (u (φ m) t) a b) μ)
      Filter.atTop (nhds (∑ j : ι₀, Work.Diff.STE.fourierCoeff
        (D.Rper i (D.Rstar j (limComp (I := I) (M := M) g j t)) a b) μ)) := by
    refine h3.congr' (Filter.Eventually.of_forall fun m => ?_)
    exact (h1 m).symm
  rw [h2]
  exact tendsto_nhds_unique hB hA

/-- **Compactness step (reduction).**  A sequence of bilinear-form families that is uniformly bounded
in every composite level `BNorm k` and whose component Fourier coefficients are uniformly Lipschitz in
`t` (a constant `L i a b μ` per index, uniform in the sequence) admits a subsequence `φ` and a limit
family `U` such that, for every `t ∈ [0, τ₀)`, the states converge to `U t` in every `BNorm k`
(hence the coefficients converge, uniformly in `t`, to the coefficients of `U`), while `U` inherits
the `BNorm` bounds, the positivity margin and `ChartData`.

The Lipschitz hypothesis is the one supplied later by `deTurck_bound` (via the ODE satisfied by the
Galerkin states); the proof of this statement is the diagonal Arzelà–Ascoli
(`Work.Diff.STE.flat.exists_subseq_uniform`) together with the tail bound
`Work.Diff.STE.CSq_tail_le` on the ℓ² tails and the identification `R_i (U t) =` the coefficientwise
limit (`B3/Recon.lean`, `B3/CSq_period_comp_arg_le_isOpen.lean`). -/
theorem exists_subseq_coeff_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (τ₀ lam : ℝ) (hτ₀ : 0 < τ₀) (B : ℕ → ℝ) (hB : ∀ k : ℕ, 0 ≤ B k)
    (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hCD : ∀ (m : ℕ) (t : ℝ), Work.Diff.STE.D.ChartData (I := I) (M := M) (u m t))
    (hsmet0 : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (hBnd : ∀ (m : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) τ₀ → ∀ k : ℕ, D.BNorm k (u m t) ≤ B k)
    (hpos : ∀ (m : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) τ₀ → ∀ (x : M) (v : TangentSpace I x),
      lam * g₀.inner x v v ≤ (u m t) x v v)
    (L : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℤ) → ℝ)
    (hL : ∀ i a b μ, 0 ≤ L i a b μ)
    (hLip : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ)
      (m : ℕ), ∀ t ∈ Ico (0 : ℝ) τ₀, ∀ t' ∈ Ico (0 : ℝ) τ₀,
      ‖coeffFun (I := I) (M := M) D u i a b μ m t
        - coeffFun (I := I) (M := M) D u i a b μ m t'‖ ≤ L i a b μ * |t - t'|)
    (hdens : ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ 2 * D.σ i → d₀ ≤ D.dens i z) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ U : ℝ → Work.Diff.STE.Bil (I := I) (M := M),
      (∀ t ∈ Ico (0 : ℝ) τ₀, ∀ k : ℕ, D.BNorm k (U t) ≤ B k) ∧
      (∀ t ∈ Ico (0 : ℝ) τ₀, ∀ (x : M) (v : TangentSpace I x),
        lam * g₀.inner x v v ≤ (U t) x v v) ∧
      (∀ t ∈ Ico (0 : ℝ) τ₀, Work.Diff.STE.D.ChartData (I := I) (M := M) (U t)) ∧
      (∀ t ∈ Ico (0 : ℝ) τ₀, ∀ k : ℕ,
        Filter.Tendsto (fun m : ℕ => D.BNorm k (u (φ m) t - U t)) Filter.atTop (nhds 0)) ∧
      (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
        TendstoUniformlyOn
          (fun (m : ℕ) (t : ℝ) => coeffFun (I := I) (M := M) D u i a b μ (φ m) t)
          (fun (t : ℝ) => coeffFun (I := I) (M := M) D (fun _ : ℕ => U) i a b μ 0 t)
          Filter.atTop (Ico (0 : ℝ) τ₀)) := by
  classical
  -- smoothness and periodicity of the components of the sequence
  have hsm : ∀ (m : ℕ) (t : ℝ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i (u m t) a b) := fun m t i a b =>
    (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i (u m t) a b
      (Work.Diff.STE.B3.R_contDiff_of_chartData D _ (hCD m t) i a b)).1
  have hper : ∀ (m : ℕ) (t : ℝ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.Periodic1 (D.Rper i (u m t) a b) := fun m t i a b =>
    (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i (u m t) a b
      (Work.Diff.STE.B3.R_contDiff_of_chartData D _ (hCD m t) i a b)).2
  -- coefficient bounds and rapid decay for the sequence
  obtain ⟨hbdd0, hdec0⟩ :=
    Work.Diff.STE.Lead.coeffFun_bound_and_decay (I := I) (M := M) D τ₀ B u hsm hper hBnd (hB 0)
  -- the diagonal extraction of a subsequence and of the coefficient limits
  obtain ⟨φ, hφ, g, hg⟩ := exists_subseq_coeff (I := I) (M := M) D τ₀ u hτ₀
    (fun _ _ _ _ => Real.sqrt (B 0)) L (fun _ _ _ _ => Real.sqrt_nonneg _) hL
    (fun i a b μ m t ht => hbdd0 i a b μ m t ⟨ht.1, ht.2.le⟩)
    (fun i a b μ m t ht t' ht' => hLip i a b μ m t ht t' ht')
  -- the limit coefficient family is rapidly decaying, uniformly in `t`
  have hdecg : ∀ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ) (t : ℝ), t ∈ Ico (0 : ℝ) τ₀ →
        ‖g i a b μ t‖ * (Work.Diff.STE.wt μ) ^ K ≤ C := by
    intro K
    refine ⟨Real.sqrt (B (2 * K)), Real.sqrt_nonneg _, fun i a b μ t ht => ?_⟩
    have hlim : Filter.Tendsto (fun m : ℕ =>
        ‖coeffFun (I := I) (M := M) D u i a b μ (φ m) t‖ * (Work.Diff.STE.wt μ) ^ K)
        Filter.atTop (nhds (‖g i a b μ t‖ * (Work.Diff.STE.wt μ) ^ K)) :=
      (((hg i a b μ).tendsto_at ht).norm.mul_const _)
    exact le_of_tendsto hlim (Filter.Eventually.of_forall fun m =>
      hdec0 K i a b μ (φ m) t ⟨ht.1, ht.2.le⟩)
  -- conjugate symmetry of the limit coefficient family
  have hgcs : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ) (t : ℝ), t ∈ Ico (0 : ℝ) τ₀ →
        star (g i a b (-μ) t) = g i a b μ t := by
    intro i a b μ t ht
    have h2 : Filter.Tendsto
        (fun m : ℕ => coeffFun (I := I) (M := M) D u i a b (-(-μ)) (φ m) t)
        Filter.atTop (nhds (g i a b (-(-μ)) t)) := (hg i a b (-(-μ))).tendsto_at ht
    have h1 : Filter.Tendsto
        (fun m : ℕ => star (coeffFun (I := I) (M := M) D u i a b (-μ) (φ m) t))
        Filter.atTop (nhds (star (g i a b (-μ) t))) :=
      ((hg i a b (-μ)).tendsto_at ht).star
    rw [funext (fun m => coeffFun_star_neg (I := I) (M := M) D u i a b (-μ) (φ m) t)] at h1
    simpa only [neg_neg] using tendsto_nhds_unique h1 h2
  -- the coefficient decay of the sequence on `Ico`
  have hdecM : ∀ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ) (t : ℝ), t ∈ Ico (0 : ℝ) τ₀ →
        ‖coeffFun (I := I) (M := M) D u i a b μ m t‖ * (Work.Diff.STE.wt μ) ^ K ≤ C :=
    fun K => ⟨Real.sqrt (B (2 * K)), Real.sqrt_nonneg _,
      fun m i a b μ t ht => hdec0 K i a b μ m t ⟨ht.1, ht.2.le⟩⟩
  have hdecM' : ∀ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (t : ℝ), t ∈ Ico (0 : ℝ) τ₀ →
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ‖ * (Work.Diff.STE.wt μ) ^ K ≤ C := by
    intro K
    obtain ⟨C, hC, hCb⟩ := hdecM K
    exact ⟨C, hC, fun m t ht i a b μ => hCb m i a b μ t ht⟩
  -- the coefficients of the limit section
  have hUcoeff := exists_limit_section_closed (I := I) (M := M) D τ₀ u φ g
    (fun m t _ => hCD m t) hgcs hdecg hdecM hg
  -- the junk extension of the limit family off the interval, so that all the "for every `t`"
  -- hypotheses of the auxiliary lemmas are available
  set U' : ℝ → Work.Diff.STE.Bil (I := I) (M := M) :=
    fun t => if t ∈ Ico (0 : ℝ) τ₀ then limSect (I := I) (M := M) D g t else g₀.inner with hU'def
  have hU'eq : ∀ t ∈ Ico (0 : ℝ) τ₀, U' t = limSect (I := I) (M := M) D g t :=
    fun t ht => dif_pos ht
  have hcdL : ∀ t ∈ Ico (0 : ℝ) τ₀, Work.Diff.STE.D.ChartData (I := I) (M := M)
      (limSect (I := I) (M := M) D g t) := fun t ht => by
    have heq : limSect (I := I) (M := M) D g t
        = fun p => ∑ i : ι₀, D.Rstar i
            (fun a b z => limComp (I := I) (M := M) g i t a b z) p := by
      funext p
      rw [limSect, Finset.sum_apply]
    rw [heq]
    exact
      (Work.Diff.STE.Lead.chartData_sum_Rstar (I := I) (M := M) D
        (fun i z a b => limComp (I := I) (M := M) g i t a b z)
        (fun i a b => (Work.Diff.STE.Lead.seriesFun_re_contDiff_periodic (I := I) (M := M)
          τ₀ g hdecg i a b t ht).1)
        (fun i a b => (Work.Diff.STE.Lead.seriesFun_re_contDiff_periodic (I := I) (M := M)
          τ₀ g hdecg i a b t ht).2))
  have hsmU : ∀ (t : ℝ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i (U' t) a b) := by
    intro t i a b
    by_cases ht : t ∈ Ico (0 : ℝ) τ₀
    · rw [hU'eq t ht]
      exact (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i _ a b
        (Work.Diff.STE.B3.R_contDiff_of_chartData D _ (hcdL t ht) i a b)).1
    · rw [show U' t = g₀.inner from dif_neg ht]
      exact (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i g₀.inner a b
        (Work.Diff.STE.B3.R_contDiff_of_chartData D _ hsmet0 i a b)).1
  have hperU : ∀ (t : ℝ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.Periodic1 (D.Rper i (U' t) a b) := by
    intro t i a b
    by_cases ht : t ∈ Ico (0 : ℝ) τ₀
    · rw [hU'eq t ht]
      exact (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i _ a b
        (Work.Diff.STE.B3.R_contDiff_of_chartData D _ (hcdL t ht) i a b)).2
    · rw [show U' t = g₀.inner from dif_neg ht]
      exact (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i g₀.inner a b
        (Work.Diff.STE.B3.R_contDiff_of_chartData D _ hsmet0 i a b)).2
  have hdecU : ∀ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ), t ∈ Ico (0 : ℝ) τ₀ →
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (U' t) a b) μ‖ * (Work.Diff.STE.wt μ) ^ K ≤ C := by
    intro K
    obtain ⟨C, hC, hCb⟩ := hdecg K
    exact ⟨C, hC, fun t ht i a b μ => by
      rw [hU'eq t ht, hUcoeff i a b μ t ht]
      exact hCb i a b μ t ht⟩
  have hconvU' : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      TendstoUniformlyOn
        (fun (m : ℕ) (t : ℝ) => Work.Diff.STE.fourierCoeff (D.Rper i (u (φ m) t) a b) μ)
        (fun (t : ℝ) => Work.Diff.STE.fourierCoeff (D.Rper i (U' t) a b) μ)
        Filter.atTop (Ico (0 : ℝ) τ₀) := by
    intro i a b μ
    refine TendstoUniformlyOn.congr_right (hg i a b μ) fun t ht => ?_
    rw [hU'eq t ht, hUcoeff i a b μ t ht]
  have hdecMφ : ∀ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (t : ℝ), t ∈ Ico (0 : ℝ) τ₀ →
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (u (φ m) t) a b) μ‖
        * (Work.Diff.STE.wt μ) ^ K ≤ C := by
    intro K
    obtain ⟨C, hC, hCb⟩ := hdecM' K
    exact ⟨C, hC, fun m t ht i a b μ => hCb (φ m) t ht i a b μ⟩
  have hstrong : ∀ t ∈ Ico (0 : ℝ) τ₀, ∀ k : ℕ,
      Filter.Tendsto (fun m : ℕ => D.BNorm k (u (φ m) t - U' t)) Filter.atTop (nhds 0) :=
    Work.Diff.STE.Lead.BNorm_tendsto_of_coeff_tendsto (I := I) (M := M) D τ₀
      (fun m => u (φ m)) U'
      (fun m t i a b => hsm (φ m) t i a b) (fun m t i a b => hper (φ m) t i a b)
      hsmU hperU hdecMφ hdecU hconvU'
  have hBndU' : ∀ t ∈ Ico (0 : ℝ) τ₀, ∀ k : ℕ, D.BNorm k (U' t) ≤ B k :=
    Work.Diff.STE.Lead.BNorm_le_of_coeff_tendsto (I := I) (M := M) D τ₀ B hB
      (fun m => u (φ m)) U'
      (fun m t ht k => hBnd (φ m) t ⟨ht.1, ht.2.le⟩ k) hdecMφ hdecU hconvU'
  have hposU' : ∀ t ∈ Ico (0 : ℝ) τ₀, ∀ (x : M) (v : TangentSpace I x),
      lam * g₀.inner x v v ≤ U' t x v v :=
    Work.Diff.STE.Lead.smet_pos_of_BNorm_tendsto (I := I) (M := M) D τ₀ lam
      (Module.finrank ℝ E + 1) (by simp only [Fintype.card_fin]; omega)
      (fun m => u (φ m)) U'
      (fun m t i a b => hsm (φ m) t i a b) (fun m t i a b => hper (φ m) t i a b)
      hsmU hperU hdens (fun m t ht x v => hpos (φ m) t ⟨ht.1, ht.2.le⟩ x v) hstrong
  refine ⟨φ, hφ, fun t => limSect (I := I) (M := M) D g t, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht k
    show D.BNorm k (limSect (I := I) (M := M) D g t) ≤ B k
    rw [← hU'eq t ht]
    exact hBndU' t ht k
  · intro t ht x v
    show lam * g₀.inner x v v ≤ limSect (I := I) (M := M) D g t x v v
    rw [← hU'eq t ht]
    exact hposU' t ht x v
  · intro t ht
    show Work.Diff.STE.D.ChartData (I := I) (M := M) (limSect (I := I) (M := M) D g t)
    exact hcdL t ht
  · intro t ht k
    refine (hstrong t ht k).congr' (Filter.Eventually.of_forall fun m => ?_)
    rw [hU'eq t ht]
  · intro i a b μ
    refine TendstoUniformlyOn.congr_right (hg i a b μ) fun t ht => ?_
    exact (hUcoeff i a b μ t ht).symm

/-- **The compactness step, without the positivity hypothesis.**  Same statement and proof as
`exists_subseq_coeff_limit`, but the positivity margin is dropped: the Galerkin state
`galState D ε (c t)` itself need not be positive definite (only its Friedrichs mollifier
`D.J ρ ε` is, by `GalUniform`), so the sequee fed to the compactness argument carries no
positivity hypothesis, and the positivity of the limit is recovered separately from the
mollified sequence (`smet_pos_of_BNorm_tendsto`). -/
theorem exists_subseq_coeff_limit_noPos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (τ₀ : ℝ) (hτ₀ : 0 < τ₀) (B : ℕ → ℝ) (hB : ∀ k : ℕ, 0 ≤ B k)
    (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hCD : ∀ (m : ℕ) (t : ℝ), Work.Diff.STE.D.ChartData (I := I) (M := M) (u m t))
    (hsmet0 : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (hBnd : ∀ (m : ℕ) (t : ℝ), t ∈ Icc (0 : ℝ) τ₀ → ∀ k : ℕ, D.BNorm k (u m t) ≤ B k)
    (L : ι₀ → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
      (Fin (Module.finrank ℝ E) → ℤ) → ℝ)
    (hL : ∀ i a b μ, 0 ≤ L i a b μ)
    (hLip : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ)
      (m : ℕ), ∀ t ∈ Ico (0 : ℝ) τ₀, ∀ t' ∈ Ico (0 : ℝ) τ₀,
      ‖coeffFun (I := I) (M := M) D u i a b μ m t
        - coeffFun (I := I) (M := M) D u i a b μ m t'‖ ≤ L i a b μ * |t - t'|)
    (hdens : ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ 2 * D.σ i → d₀ ≤ D.dens i z) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ U : ℝ → Work.Diff.STE.Bil (I := I) (M := M),
      (∀ t ∈ Ico (0 : ℝ) τ₀, ∀ k : ℕ, D.BNorm k (U t) ≤ B k) ∧
      (∀ t ∈ Ico (0 : ℝ) τ₀, Work.Diff.STE.D.ChartData (I := I) (M := M) (U t)) ∧
      (∀ t ∈ Ico (0 : ℝ) τ₀, ∀ k : ℕ,
        Filter.Tendsto (fun m : ℕ => D.BNorm k (u (φ m) t - U t)) Filter.atTop (nhds 0)) ∧
      (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
        TendstoUniformlyOn
          (fun (m : ℕ) (t : ℝ) => coeffFun (I := I) (M := M) D u i a b μ (φ m) t)
          (fun (t : ℝ) => coeffFun (I := I) (M := M) D (fun _ : ℕ => U) i a b μ 0 t)
          Filter.atTop (Ico (0 : ℝ) τ₀)) := by
  classical
  -- smoothness and periodicity of the components of the sequence
  have hsm : ∀ (m : ℕ) (t : ℝ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i (u m t) a b) := fun m t i a b =>
    (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i (u m t) a b
      (Work.Diff.STE.B3.R_contDiff_of_chartData D _ (hCD m t) i a b)).1
  have hper : ∀ (m : ℕ) (t : ℝ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.Periodic1 (D.Rper i (u m t) a b) := fun m t i a b =>
    (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i (u m t) a b
      (Work.Diff.STE.B3.R_contDiff_of_chartData D _ (hCD m t) i a b)).2
  -- coefficient bounds and rapid decay for the sequence
  obtain ⟨hbdd0, hdec0⟩ :=
    Work.Diff.STE.Lead.coeffFun_bound_and_decay (I := I) (M := M) D τ₀ B u hsm hper hBnd (hB 0)
  -- the diagonal extraction of a subsequence and of the coefficient limits
  obtain ⟨φ, hφ, g, hg⟩ := exists_subseq_coeff (I := I) (M := M) D τ₀ u hτ₀
    (fun _ _ _ _ => Real.sqrt (B 0)) L (fun _ _ _ _ => Real.sqrt_nonneg _) hL
    (fun i a b μ m t ht => hbdd0 i a b μ m t ⟨ht.1, ht.2.le⟩)
    (fun i a b μ m t ht t' ht' => hLip i a b μ m t ht t' ht')
  -- the limit coefficient family is rapidly decaying, uniformly in `t`
  have hdecg : ∀ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ) (t : ℝ), t ∈ Ico (0 : ℝ) τ₀ →
        ‖g i a b μ t‖ * (Work.Diff.STE.wt μ) ^ K ≤ C := by
    intro K
    refine ⟨Real.sqrt (B (2 * K)), Real.sqrt_nonneg _, fun i a b μ t ht => ?_⟩
    have hlim : Filter.Tendsto (fun m : ℕ =>
        ‖coeffFun (I := I) (M := M) D u i a b μ (φ m) t‖ * (Work.Diff.STE.wt μ) ^ K)
        Filter.atTop (nhds (‖g i a b μ t‖ * (Work.Diff.STE.wt μ) ^ K)) :=
      (((hg i a b μ).tendsto_at ht).norm.mul_const _)
    exact le_of_tendsto hlim (Filter.Eventually.of_forall fun m =>
      hdec0 K i a b μ (φ m) t ⟨ht.1, ht.2.le⟩)
  -- conjugate symmetry of the limit coefficient family
  have hgcs : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ) (t : ℝ), t ∈ Ico (0 : ℝ) τ₀ →
        star (g i a b (-μ) t) = g i a b μ t := by
    intro i a b μ t ht
    have h2 : Filter.Tendsto
        (fun m : ℕ => coeffFun (I := I) (M := M) D u i a b (-(-μ)) (φ m) t)
        Filter.atTop (nhds (g i a b (-(-μ)) t)) := (hg i a b (-(-μ))).tendsto_at ht
    have h1 : Filter.Tendsto
        (fun m : ℕ => star (coeffFun (I := I) (M := M) D u i a b (-μ) (φ m) t))
        Filter.atTop (nhds (star (g i a b (-μ) t))) :=
      ((hg i a b (-μ)).tendsto_at ht).star
    rw [funext (fun m => coeffFun_star_neg (I := I) (M := M) D u i a b (-μ) (φ m) t)] at h1
    simpa only [neg_neg] using tendsto_nhds_unique h1 h2
  -- the coefficient decay of the sequence on `Ico`
  have hdecM : ∀ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ) (t : ℝ), t ∈ Ico (0 : ℝ) τ₀ →
        ‖coeffFun (I := I) (M := M) D u i a b μ m t‖ * (Work.Diff.STE.wt μ) ^ K ≤ C :=
    fun K => ⟨Real.sqrt (B (2 * K)), Real.sqrt_nonneg _,
      fun m i a b μ t ht => hdec0 K i a b μ m t ⟨ht.1, ht.2.le⟩⟩
  have hdecM' : ∀ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (t : ℝ), t ∈ Ico (0 : ℝ) τ₀ →
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (u m t) a b) μ‖ * (Work.Diff.STE.wt μ) ^ K ≤ C := by
    intro K
    obtain ⟨C, hC, hCb⟩ := hdecM K
    exact ⟨C, hC, fun m t ht i a b μ => hCb m i a b μ t ht⟩
  -- the coefficients of the limit section
  have hUcoeff := exists_limit_section_closed (I := I) (M := M) D τ₀ u φ g
    (fun m t _ => hCD m t) hgcs hdecg hdecM hg
  -- the junk extension of the limit family off the interval, so that all the "for every `t`"
  -- hypotheses of the auxiliary lemmas are available
  set U' : ℝ → Work.Diff.STE.Bil (I := I) (M := M) :=
    fun t => if t ∈ Ico (0 : ℝ) τ₀ then limSect (I := I) (M := M) D g t else g₀.inner with hU'def
  have hU'eq : ∀ t ∈ Ico (0 : ℝ) τ₀, U' t = limSect (I := I) (M := M) D g t :=
    fun t ht => dif_pos ht
  have hcdL : ∀ t ∈ Ico (0 : ℝ) τ₀, Work.Diff.STE.D.ChartData (I := I) (M := M)
      (limSect (I := I) (M := M) D g t) := fun t ht => by
    have heq : limSect (I := I) (M := M) D g t
        = fun p => ∑ i : ι₀, D.Rstar i
            (fun a b z => limComp (I := I) (M := M) g i t a b z) p := by
      funext p
      rw [limSect, Finset.sum_apply]
    rw [heq]
    exact
      (Work.Diff.STE.Lead.chartData_sum_Rstar (I := I) (M := M) D
        (fun i z a b => limComp (I := I) (M := M) g i t a b z)
        (fun i a b => (Work.Diff.STE.Lead.seriesFun_re_contDiff_periodic (I := I) (M := M)
          τ₀ g hdecg i a b t ht).1)
        (fun i a b => (Work.Diff.STE.Lead.seriesFun_re_contDiff_periodic (I := I) (M := M)
          τ₀ g hdecg i a b t ht).2))
  have hsmU : ∀ (t : ℝ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i (U' t) a b) := by
    intro t i a b
    by_cases ht : t ∈ Ico (0 : ℝ) τ₀
    · rw [hU'eq t ht]
      exact (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i _ a b
        (Work.Diff.STE.B3.R_contDiff_of_chartData D _ (hcdL t ht) i a b)).1
    · rw [show U' t = g₀.inner from dif_neg ht]
      exact (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i g₀.inner a b
        (Work.Diff.STE.B3.R_contDiff_of_chartData D _ hsmet0 i a b)).1
  have hperU : ∀ (t : ℝ) (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.Periodic1 (D.Rper i (U' t) a b) := by
    intro t i a b
    by_cases ht : t ∈ Ico (0 : ℝ) τ₀
    · rw [hU'eq t ht]
      exact (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i _ a b
        (Work.Diff.STE.B3.R_contDiff_of_chartData D _ (hcdL t ht) i a b)).2
    · rw [show U' t = g₀.inner from dif_neg ht]
      exact (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i g₀.inner a b
        (Work.Diff.STE.B3.R_contDiff_of_chartData D _ hsmet0 i a b)).2
  have hdecU : ∀ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ), t ∈ Ico (0 : ℝ) τ₀ →
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (U' t) a b) μ‖ * (Work.Diff.STE.wt μ) ^ K ≤ C := by
    intro K
    obtain ⟨C, hC, hCb⟩ := hdecg K
    exact ⟨C, hC, fun t ht i a b μ => by
      rw [hU'eq t ht, hUcoeff i a b μ t ht]
      exact hCb i a b μ t ht⟩
  have hconvU' : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      TendstoUniformlyOn
        (fun (m : ℕ) (t : ℝ) => Work.Diff.STE.fourierCoeff (D.Rper i (u (φ m) t) a b) μ)
        (fun (t : ℝ) => Work.Diff.STE.fourierCoeff (D.Rper i (U' t) a b) μ)
        Filter.atTop (Ico (0 : ℝ) τ₀) := by
    intro i a b μ
    refine TendstoUniformlyOn.congr_right (hg i a b μ) fun t ht => ?_
    rw [hU'eq t ht, hUcoeff i a b μ t ht]
  have hdecMφ : ∀ K : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (t : ℝ), t ∈ Ico (0 : ℝ) τ₀ →
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (u (φ m) t) a b) μ‖
        * (Work.Diff.STE.wt μ) ^ K ≤ C := by
    intro K
    obtain ⟨C, hC, hCb⟩ := hdecM' K
    exact ⟨C, hC, fun m t ht i a b μ => hCb (φ m) t ht i a b μ⟩
  have hstrong : ∀ t ∈ Ico (0 : ℝ) τ₀, ∀ k : ℕ,
      Filter.Tendsto (fun m : ℕ => D.BNorm k (u (φ m) t - U' t)) Filter.atTop (nhds 0) :=
    Work.Diff.STE.Lead.BNorm_tendsto_of_coeff_tendsto (I := I) (M := M) D τ₀
      (fun m => u (φ m)) U'
      (fun m t i a b => hsm (φ m) t i a b) (fun m t i a b => hper (φ m) t i a b)
      hsmU hperU hdecMφ hdecU hconvU'
  have hBndU' : ∀ t ∈ Ico (0 : ℝ) τ₀, ∀ k : ℕ, D.BNorm k (U' t) ≤ B k :=
    Work.Diff.STE.Lead.BNorm_le_of_coeff_tendsto (I := I) (M := M) D τ₀ B hB
      (fun m => u (φ m)) U'
      (fun m t ht k => hBnd (φ m) t ⟨ht.1, ht.2.le⟩ k) hdecMφ hdecU hconvU'
  refine ⟨φ, hφ, fun t => limSect (I := I) (M := M) D g t, ?_, ?_, ?_, ?_⟩
  · intro t ht k
    show D.BNorm k (limSect (I := I) (M := M) D g t) ≤ B k
    rw [← hU'eq t ht]
    exact hBndU' t ht k
  · intro t ht
    show Work.Diff.STE.D.ChartData (I := I) (M := M) (limSect (I := I) (M := M) D g t)
    exact hcdL t ht
  · intro t ht k
    refine (hstrong t ht k).congr' (Filter.Eventually.of_forall fun m => ?_)
    rw [hU'eq t ht]
  · intro i a b μ
    refine TendstoUniformlyOn.congr_right (hg i a b μ) fun t ht => ?_
    exact (hUcoeff i a b μ t ht).symm


/-! ## Uniform bounds along the Galerkin family

The last layer of the proof needs two uniform bounds, both obtained by the **sup route** — no
energy estimate of the Galerkin scheme is used, and in particular
`Work.Diff.STE.Lead.Gal.gardingAssembly` (whose pointwise order-`(k+1)` `hjet` hypothesis is not
instantiable) must NOT be imported.  The route is:

* `ENormB_le_BNorm_uniform` — the physical energy of a section is controlled by its composite norm,
  with a constant depending only on the dimension (so uniformly in the section); proved from
  `ENormSq_le_CSq_of_contDiff_periodic` and the periodisation smoothness
  `B3.Rper_contDiff_periodic_of_R_contDiff` (both axiom-clean);

* `BNorm_deTurckSec_le` (delegated) — the composite norm of the DeTurck operator of a pinched
  section with bounded `BNorm` is bounded uniformly over the class.  The route is the *pointwise*
  DeTurck bound `Work.Diff.STE.Lead.deTurck_bound` (proved: a pointwise bound on
  `deTurckOp (smetOf h) g₀ x u v`, together with the continuity of the DeTurck operator in the
  section), the mollifier bounds `Work.Diff.STE.Lead.J_pointwise_le` and
  `Work.Diff.STE.B3.STruncR_sup_le` (both proved), and the transport identity of the tame layer.

This is what turns the a priori `BNorm k` bounds of the Galerkin family into a *pointwise* bound for
the right-hand side of the Galerkin ODE, hence (with `coeffFun_lipschitz_of_ode` and
`Work.Diff.STE.Lead.smet_pos_of_BNorm_tendsto`) into the compactness and the positivity of the
limit. -/

/-- **`ENormB` is controlled by `BNorm`, uniformly in the section.** -/
theorem ENormB_le_BNorm_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b)),
      D.ENormB k h ≤ C * D.BNorm k h := by
  obtain ⟨C, hC, hCb⟩ :=
    Work.Diff.STE.ENormSq_le_CSq_of_contDiff_periodic (ι := Fin (Module.finrank ℝ E)) k
  refine ⟨C, hC, fun h hsm => ?_⟩
  have hRp : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i h a b) ∧ Work.Diff.STE.Periodic1 (D.Rper i h a b) :=
    fun i a b =>
      Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D i h a b (hsm i a b)
  simp only [Work.Diff.STE.B3Data.ENormB, Work.Diff.STE.B3Data.BNorm]
  calc ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Work.Diff.STE.ENormSq k (D.Rper i h a b)
      ≤ ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        C * Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b)) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
          Finset.sum_le_sum fun b _ => ?_
        exact hCb _ (hRp i a b).1 (hRp i a b).2
    _ = C * ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]

/-- **`BNorm ≤ C (ENormB + ENormB 0)`, uniformly in the section** (the `ENormB` version of
`BNorm_le_ENormB` with the constant hoisted outside the quantifier). -/
theorem BNorm_le_ENormB_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        ContDiff ℝ k (D.Rper i h a b))
      (hper : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        Work.Diff.STE.Periodic1 (D.Rper i h a b)),
      D.BNorm k h ≤ C * (D.ENormB k h + D.ENormB 0 h) := by
  obtain ⟨C, hC, hCb⟩ := Work.Diff.STE.CSq_le_ENormSq (ι := Fin (Module.finrank ℝ E)) k
  refine ⟨C, hC, fun h hsm hper => ?_⟩
  have hterm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b))
        ≤ C * (Work.Diff.STE.ENormSq k (D.Rper i h a b)
          + Work.Diff.STE.ENormSq 0 (D.Rper i h a b)) :=
    fun i a b => hCb _ (hsm i a b) (hper i a b)
  simp only [Work.Diff.STE.B3Data.BNorm, Work.Diff.STE.B3Data.ENormB]
  calc ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b))
      ≤ ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
        C * (Work.Diff.STE.ENormSq k (D.Rper i h a b)
          + Work.Diff.STE.ENormSq 0 (D.Rper i h a b)) := by
        refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
          Finset.sum_le_sum fun b _ => ?_
        exact hterm i a b
    _ = C * (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          (Work.Diff.STE.ENormSq k (D.Rper i h a b)
            + Work.Diff.STE.ENormSq 0 (D.Rper i h a b))) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.mul_sum]
    _ = C * (∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          Work.Diff.STE.ENormSq k (D.Rper i h a b)
        + ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          Work.Diff.STE.ENormSq 0 (D.Rper i h a b)) := by
        congr 1
        refine (Finset.sum_congr rfl fun i _ => ?_).trans Finset.sum_add_distrib
        refine (Finset.sum_congr rfl fun a _ => ?_).trans Finset.sum_add_distrib
        exact Finset.sum_add_distrib

/-- **`g₀` is positive semidefinite on the diagonal.** -/
lemma smet_inner_nonneg {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    {g₀ : SMet I M} {x : M} (v : TangentSpace I x) : 0 ≤ g₀.inner x v v := by
  by_cases hv : v = 0
  · subst hv; simp
  · exact (g₀.pos x v hv).le

/-- **The Friedrichs mollifier preserves the upper pinching bound**, up to a constant: a section
that is dominated by the background metric keeps its mollified version dominated, with a constant
depending only on `D`, `ρ` and the level `k`.  This is `pointwise_le_sqrt_BNorm_uniform` applied to
`D.J ρ ε h` together with the uniform bound `BNorm k (D.J ρ ε h) ≤ C BNorm k h` (`hJN`). -/
theorem J_upper_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (k : ℕ) (hk : Fintype.card (Fin (Module.finrank ℝ E)) < 2 * k)
    (hdens : ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ 2 * D.σ i → d₀ ≤ D.dens i z)
    (hJN : (∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
        Work.Diff.STE.D.ChartData (I := I) (M := M) h → D.BNorm k (D.J ρ ε h) ≤ C * D.BNorm k h)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
      (h : Work.Diff.STE.Bil (I := I) (M := M))
      (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
      (Bnd : ℝ) (hBnd : 0 ≤ Bnd) (hB : D.BNorm k h ≤ Bnd)
      (x : M) (v : TangentSpace I x),
      (D.J ρ ε h) x v v ≤ C * Real.sqrt Bnd * g₀.inner x v v := by
  obtain ⟨C1, hC1, hC1b⟩ :=
    Work.Diff.STE.Lead.pointwise_le_sqrt_BNorm_uniform (I := I) (M := M) D k hk hdens
  obtain ⟨C2, hC2, hC2b⟩ := hJN k
  refine ⟨C1 * Real.sqrt C2, by positivity, fun ε hε h hsm Bnd hBnd hB x v => ?_⟩
  have hCh : Work.Diff.STE.D.ChartData (I := I) (M := M) (D.J ρ ε h) :=
    Work.Diff.STE.Lead.chartData_J_props (I := I) (M := M) D ρ hρ ε h hsm
  have hsmJ : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i (D.J ρ ε h) a b) := fun i a b =>
    (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D i _ a b
      (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D _ hCh i a b)).1
  have hperJ : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.Periodic1 (D.Rper i (D.J ρ ε h) a b) := fun i a b =>
    (Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff (I := I) (M := M) D i _ a b
      (Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D _ hCh i a b)).2
  have h1 := hC1b (D.J ρ ε h) hsmJ hperJ x v v
  have h2 := hC2b ε hε h hsm
  have h3 : Real.sqrt (D.BNorm k (D.J ρ ε h)) ≤ Real.sqrt (C2 * Bnd) :=
    Real.sqrt_le_sqrt (le_trans h2 (mul_le_mul_of_nonneg_left hB hC2))
  have h4 : Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) = g₀.inner x v v :=
    Real.mul_self_sqrt (smet_inner_nonneg (I := I) (g₀ := g₀) v)
  calc (D.J ρ ε h) x v v
      ≤ |(D.J ρ ε h) x v v| := le_abs_self _
    _ ≤ C1 * Real.sqrt (D.BNorm k (D.J ρ ε h)) * Real.sqrt (g₀.inner x v v)
          * Real.sqrt (g₀.inner x v v) := h1
    _ ≤ C1 * Real.sqrt (C2 * Bnd) * Real.sqrt (g₀.inner x v v)
          * Real.sqrt (g₀.inner x v v) := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left h3 hC1) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
    _ = C1 * Real.sqrt (C2 * Bnd)
          * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) := by ring
    _ = (C1 * Real.sqrt C2) * Real.sqrt Bnd * g₀.inner x v v := by
        rw [Real.sqrt_mul hC2, Real.mul_self_sqrt (smet_inner_nonneg (I := I) (g₀ := g₀) v)]
        ring

/-- **The Friedrichs mollifier preserves the upper pinching bound for a family of sections with a
uniform composite-norm bound.**  This is the upper-bound hypothesis (`hub`) of `deTurck_bound` for
the Galerkin state, whose lower bound `lam g₀ ≤ D.J ρ ε (galState …)` is the `GalUniform`
hypothesis itself. -/
theorem J_sandwich
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (k : ℕ) (hk : Fintype.card (Fin (Module.finrank ℝ E)) < 2 * k)
    (hdens : ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ 2 * D.σ i → d₀ ≤ D.dens i z)
    (hJN : (∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
        Work.Diff.STE.D.ChartData (I := I) (M := M) h → D.BNorm k (D.J ρ ε h) ≤ C * D.BNorm k h))
    (B : ℕ → ℝ) (hB : ∀ k : ℕ, 0 ≤ B k)
    (u : Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) u)
    (hBnd : D.BNorm k u ≤ B k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (x : M) (v : TangentSpace I x),
      (D.J ρ ε u) x v v ≤ K * g₀.inner x v v := by
  obtain ⟨C, _hC, hCb⟩ := J_upper_bound (I := I) (M := M) D ρ hρ k hk hdens hJN
  refine ⟨C * Real.sqrt (B k), by positivity, fun ε hε x v => hCb ε hε u hsm (B k) (hB k) hBnd x v⟩

/-- **The pointwise bound for the right-hand side of the Galerkin ODE on the mollified state.**
`Work.Diff.STE.Lead.deTurck_bound` (part 1) bounds the DeTurck operator of a pinched section; here it
is specialised to the section `D.J ρ ε u`, whose positivity comes from the Galerkin confinement and
whose upper pinching comes from `J_sandwich`. -/
theorem deTurckSec_mollified_pointwise_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless] [CompactSpace M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hLC : LCSmooth I M) (k : ℕ) (hk : Module.finrank ℝ E + 12 < 2 * k)
    (lam K : ℝ) (hlam : 0 < lam)
    (ε B₁ : ℝ) (u : Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : Work.Diff.STE.D.ChartData (I := I) (M := M) u)
    (hsym : Work.Diff.STE.D.IsSymm (I := I) u)
    (hposJ : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < (D.J ρ ε u) x v v)
    (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ (D.J ρ ε u) x v v)
    (hub : ∀ (x : M) (v : TangentSpace I x), (D.J ρ ε u) x v v ≤ K * g₀.inner x v v)
    (hBnd : D.BNorm k (D.J ρ ε u) ≤ B₁) (hB₁ : 0 ≤ B₁) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (y : M) (u' v' : TangentSpace I y),
      |Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (D.J ρ ε u)
          (fun x a b => Work.Diff.STE.Lead.isSymm_J_props (I := I) (M := M) D ρ ε u hsym x a b)
          hposJ
          (Work.Diff.STE.Lead.chartData_J_props (I := I) (M := M) D ρ hρ ε u hsm) y u' v'|
        ≤ C * (1 + B₁) ^ 2 * Real.sqrt (g₀.inner y u' u') * Real.sqrt (g₀.inner y v' v') := by
  obtain ⟨C, hC, hCb⟩ :=
    (Work.Diff.STE.Lead.deTurck_bound (I := I) (M := M) D hLC k hk lam K hlam).1
  refine ⟨C, hC, fun y u' v' => ?_⟩
  simp only [Work.Diff.STE.D.deTurckSec_apply]
  exact hCb B₁ (D.J ρ ε u)
    (fun x a b => (Work.Diff.STE.Lead.isSymm_J_props (I := I) (M := M) D ρ ε u hsym x a b))
    hposJ (Work.Diff.STE.Lead.chartData_J_props (I := I) (M := M) D ρ hρ ε u hsm)
    hBnd hell hub y u' v'

/-- **The level-`0` coefficient bound for the Friedrichs mollifier of a pointwise bounded section**
(inlined here, since any lemma about `coeffFun` stated in a separate module would create an import
cycle with this file). -/
theorem coeffFun_mollified_le
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hJN : (∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
      ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
        Work.Diff.STE.D.ChartData (I := I) (M := M) h → D.BNorm k (D.J ρ ε h) ≤ C * D.BNorm k h)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ) (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
      (X : Work.Diff.STE.Bil (I := I) (M := M)) (K : ℝ) (hK : 0 ≤ K)
      (hX : ∀ (y : M) (u v : TangentSpace I y),
        |X y u v| ≤ K * Real.sqrt (g₀.inner y u u) * Real.sqrt (g₀.inner y v v))
      (hsmX : Work.Diff.STE.D.ChartData (I := I) (M := M) X)
      (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      ‖coeffFun (I := I) (M := M) D (fun (_ : ℕ) (_ : ℝ) => D.J ρ ε X) i a b μ (0 : ℕ) (0 : ℝ)‖
        ≤ C * K := by
  obtain ⟨CJ, hCJ0, hCJb⟩ := hJN 0
  obtain ⟨CL1, hCL10, hCL1b⟩ :=
    Work.Diff.STE.Lead.fourierCoeff_le_sqrt_BNorm (I := I) (M := M) D
  obtain ⟨CL2, hCL20, hCL2b⟩ :=
    Work.Diff.STE.Lead.BNorm_zero_le_of_pointwise (I := I) (M := M) D
  refine ⟨max 1 (CL1 * Real.sqrt (CJ * CL2)), le_trans zero_le_one (le_max_left _ _), ?_⟩
  intro ε hε X K hK hX hsmX i a b μ
  have hsmY : Work.Diff.STE.D.ChartData (I := I) (M := M) (D.J ρ ε X) :=
    Work.Diff.STE.Lead.chartData_J_props (I := I) (M := M) D ρ hρ ε X hsmX
  have h1 : ‖Work.Diff.STE.fourierCoeff (D.Rper i (D.J ρ ε X) a b) μ‖
      ≤ CL1 * Real.sqrt (D.BNorm 0 (D.J ρ ε X)) := hCL1b (D.J ρ ε X) hsmY i a b μ
  have hJ : D.BNorm 0 (D.J ρ ε X) ≤ CJ * D.BNorm 0 X := hCJb ε hε X hsmX
  have hX2 : D.BNorm 0 X ≤ CL2 * K ^ 2 := hCL2b X K hK hX hsmX
  have h3 : Real.sqrt (D.BNorm 0 (D.J ρ ε X)) ≤ Real.sqrt (CJ * (CL2 * K ^ 2)) :=
    Real.sqrt_le_sqrt (le_trans hJ (mul_le_mul_of_nonneg_left hX2 hCJ0))
  have h4 : Real.sqrt (CJ * (CL2 * K ^ 2)) = Real.sqrt (CJ * CL2) * K := by
    rw [show CJ * (CL2 * K ^ 2) = (CJ * CL2) * K ^ 2 by ring,
      Real.sqrt_mul (mul_nonneg hCJ0 hCL20), Real.sqrt_sq hK]
  change ‖Work.Diff.STE.fourierCoeff (D.Rper i (D.J ρ ε X) a b) μ‖
      ≤ max 1 (CL1 * Real.sqrt (CJ * CL2)) * K
  calc ‖Work.Diff.STE.fourierCoeff (D.Rper i (D.J ρ ε X) a b) μ‖
      ≤ CL1 * Real.sqrt (D.BNorm 0 (D.J ρ ε X)) := h1
    _ ≤ CL1 * Real.sqrt (CJ * (CL2 * K ^ 2)) := mul_le_mul_of_nonneg_left h3 hCL10
    _ = (CL1 * Real.sqrt (CJ * CL2)) * K := by rw [h4]; ring
    _ ≤ max 1 (CL1 * Real.sqrt (CJ * CL2)) * K :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hK

theorem gal_limit_data_of
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless] [CompactSpace M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y, 2 < ∑ i, (y i) ^ 2 → ρ y = 0) (hρs : ContDiff ℝ (⊤ : ENat) ρ)
    (hρ1 : ρ 0 = 1)
    (hLC : LCSmooth I M)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (hJN : (∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
        ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
        Work.Diff.STE.D.ChartData (I := I) (M := M) h → D.BNorm k (D.J ρ ε h) ≤ C * D.BNorm k h))
    (hJpw : (∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), ε ∈ Set.Ioc (0 : ℝ) 1 →
      ∀ (X : Work.Diff.STE.Bil (I := I) (M := M)) (K : ℝ), 0 ≤ K →
      (∀ (y : M) (u v : TangentSpace I y),
        |X y u v| ≤ K * Real.sqrt (g₀.inner y u u) * Real.sqrt (g₀.inner y v v)) →
      ∀ (x : M) (u v : TangentSpace I x),
        |(D.J ρ ε X) x u v| ≤ C * K * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)))
    (hGU : GalUniform hLC D ρ) :
    ∃ (τ₀ lam L : ℝ) (B : ℕ → ℝ) (ε : ℕ → ℝ)
      (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M)),
      0 < τ₀ ∧ 0 < lam ∧ 0 ≤ L ∧ (∀ k, 0 ≤ B k) ∧
      (∀ m, ε m ∈ Set.Ioc (0 : ℝ) 1) ∧ Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      (∀ m : ℕ, ∃ c : ℝ → Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) (ε m) → ℝ,
        IsGalSol hLC D ρ (ε m) τ₀ c ∧ (∀ t : ℝ, u m t = galState D (ε m) (c t))) ∧
      (∀ m t, Work.Diff.STE.D.ChartData (I := I) (M := M) (u m t)) ∧
      (∀ m t, t ∈ Set.Icc (0 : ℝ) τ₀ → ∀ k, D.BNorm k (u m t) ≤ B k) ∧
      (∀ m t, t ∈ Set.Icc (0 : ℝ) τ₀ → ∀ (x : M) (v : TangentSpace I x),
        lam * g₀.inner x v v ≤ (D.J ρ (ε m) (u m t)) x v v) ∧
      (∀ m t, t ∈ Set.Icc (0 : ℝ) τ₀ → ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
        0 < (D.J ρ (ε m) (u m t)) x v v) ∧
      (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ) (m : ℕ),
        ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ t' ∈ Set.Ico (0 : ℝ) τ₀,
        ‖coeffFun (I := I) (M := M) D u i a b μ m t
          - coeffFun (I := I) (M := M) D u i a b μ m t'‖ ≤ L * |t - t'|) := by
  classical
  obtain ⟨ε₀, hε₀, τ₀, hτ₀, lam, hlam, B₀, hB₀⟩ := hGU
  set ε₁ : ℝ := min ε₀ 1 with hε₁def
  have hε₁pos : 0 < ε₁ := lt_min hε₀ one_pos
  have hε₁le1 : ε₁ ≤ 1 := min_le_right _ _
  have hε₁leε₀ : ε₁ ≤ ε₀ := min_le_left _ _
  set ε : ℕ → ℝ := fun m => ε₁ / ((m : ℝ) + 2) with hεdef
  have hεden : ∀ m : ℕ, (0 : ℝ) < (m : ℝ) + 2 := fun m => by positivity
  have hεpos : ∀ m, 0 < ε m := fun m => div_pos hε₁pos (hεden m)
  have hεlem : ∀ m, ε m ≤ ε₁ := by
    intro m
    rw [hεdef, div_le_iff₀ (hεden m)]
    have h1 : (1 : ℝ) ≤ (m : ℝ) + 2 := by
      have h0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      linarith
    exact le_mul_of_one_le_right hε₁pos.le h1
  have hεmem0 : ∀ m, ε m ∈ Set.Ioc (0 : ℝ) ε₀ :=
    fun m => ⟨hεpos m, le_trans (hεlem m) hε₁leε₀⟩
  have hεmem1 : ∀ m, ε m ∈ Set.Ioc (0 : ℝ) 1 :=
    fun m => ⟨hεpos m, le_trans (hεlem m) hε₁le1⟩
  have hεtend : Filter.Tendsto ε Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun m : ℕ => ((m : ℝ) + 2)) Filter.atTop Filter.atTop :=
      Filter.tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop
    have h1 : Filter.Tendsto (fun m : ℕ => (((m : ℝ) + 2))⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp h0
    have h2 : ε = fun m : ℕ => ε₁ * (((m : ℝ) + 2))⁻¹ := by
      funext m; rw [hεdef]; ring
    rw [h2]
    simpa using h1.const_mul ε₁
  have hc : ∀ m : ℕ, ∃ cc : ℝ → Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) (ε m) → ℝ,
      IsGalSol hLC D ρ (ε m) τ₀ cc ∧
      ∀ t ∈ Set.Icc (0 : ℝ) τ₀, (∀ k : ℕ, D.BNorm k (galState D (ε m) (cc t)) ≤ B₀ k) ∧
        ∀ (x : M) (v : TangentSpace I x),
          lam * g₀.inner x v v ≤ (D.J ρ (ε m) (galState D (ε m) (cc t))) x v v :=
    fun m => hB₀ (ε m) (hεmem0 m)
  choose c hcsol hcprop using hc
  set u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M) :=
    fun m t => galState D (ε m) (c m t) with hudef
  have hu : ∀ m t, u m t = galState D (ε m) (c m t) := fun m t => rfl
  have huCD : ∀ m t, Work.Diff.STE.D.ChartData (I := I) (M := M) (u m t) := by
    intro m t
    rw [hu]
    exact (galState_J_props (I := I) (M := M) D ρ hg hρ (ε m) (hεpos m) (c m t)).2.1
  have huBnd : ∀ m t, t ∈ Set.Icc (0 : ℝ) τ₀ → ∀ k, D.BNorm k (u m t) ≤ max (B₀ k) 0 := by
    intro m t ht k
    rw [hu]
    exact le_trans ((hcprop m t ht).1 k) (le_max_left _ _)
  have huEll : ∀ m t, t ∈ Set.Icc (0 : ℝ) τ₀ → ∀ (x : M) (v : TangentSpace I x),
      lam * g₀.inner x v v ≤ (D.J ρ (ε m) (u m t)) x v v := by
    intro m t ht x v
    rw [hu]
    exact (hcprop m t ht).2 x v
  have huPos : ∀ m t, t ∈ Set.Icc (0 : ℝ) τ₀ → ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < (D.J ρ (ε m) (u m t)) x v v := by
    intro m t ht x v hv
    exact lt_of_lt_of_le (mul_pos hlam (g₀.pos x v hv)) (huEll m t ht x v)
  -- ### the uniform bound of the right-hand side
  set B : ℕ → ℝ := fun k => max (B₀ k) 0 with hBdef
  have hB : ∀ k, 0 ≤ B k := fun k => le_max_right _ _
  set k : ℕ := Module.finrank ℝ E + 13 with hkdef
  have hkA : Module.finrank ℝ E + 12 < 2 * k := by rw [hkdef]; omega
  have hkB : Fintype.card (Fin (Module.finrank ℝ E)) < 2 * k := by
    rw [Fintype.card_fin, hkdef]; omega
  have hdensL : ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ 2 * D.σ i → d₀ ≤ D.dens i z :=
    Work.Diff.STE.B3.dens_lower_bound (I := I) (M := M) D
      (fun i => Work.Diff.STE.B3.densGood (I := I) (M := M) D i)
  obtain ⟨C_ub, hC_ub, hC_ubb⟩ :=
    J_upper_bound (I := I) (M := M) D ρ hρ k hkB hdensL hJN
  have hK0 : 0 ≤ C_ub * Real.sqrt (B k) := mul_nonneg hC_ub (Real.sqrt_nonneg _)
  obtain ⟨C_P, hC_P, hCPb⟩ :=
    (deTurck_bound (I := I) (M := M) D hLC k hkA lam (C_ub * Real.sqrt (B k)) hlam).1
  obtain ⟨C_JN, hC_JN, hCJNb⟩ := hJN k
  set Cf : ℝ := C_P * (1 + C_JN * B k) ^ 2 with hCfdef
  have hCf0 : 0 ≤ Cf := by rw [hCfdef]; positivity
  obtain ⟨C_J, hC_J, hCJb⟩ := hJpw
  -- the pointwise bound of the right-hand side
  have hvs : ∀ (m : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) τ₀)
      (x : M) (u₀ v : TangentSpace I x),
      |(D.J ρ (ε m) (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (D.J ρ (ε m) (u m t))
          (fun x a b => (galState_J_props (I := I) (M := M) D ρ hg hρ (ε m) (hεpos m)
            (c m t)).2.2.1 x a b)
          (fun x v hv => huPos m t ht x v hv)
          ((galState_J_props (I := I) (M := M) D ρ hg hρ (ε m) (hεpos m)
            (c m t)).2.2.2))) x u₀ v|
        ≤ (C_J * Cf) * Real.sqrt (g₀.inner x u₀ u₀) * Real.sqrt (g₀.inner x v v) := by
    intro m t ht x u₀ v
    have hJsymm : Work.Diff.STE.D.IsSymm (I := I)
        (D.J ρ (ε m) (u m t)) := by
      rw [hu]
      exact (galState_J_props (I := I) (M := M) D ρ hg hρ (ε m) (hεpos m) (c m t)).2.2.1
    have hJsm : Work.Diff.STE.D.ChartData (I := I) (M := M) (D.J ρ (ε m) (u m t)) := by
      rw [hu]
      exact (galState_J_props (I := I) (M := M) D ρ hg hρ (ε m) (hεpos m) (c m t)).2.2.2
    have hJbnd : D.BNorm k (D.J ρ (ε m) (u m t)) ≤ C_JN * B k := by
      have h1 := hCJNb (ε m) (hεmem1 m) (u m t) (huCD m t)
      exact le_trans h1 (mul_le_mul_of_nonneg_left (huBnd m t ht k) hC_JN)
    have hXbd : ∀ (y : M) (u' v' : TangentSpace I y),
        |(Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (D.J ρ (ε m) (u m t))
            (fun x a b => hJsymm x a b) (fun x v hv => huPos m t ht x v hv) hJsm) y u' v'|
          ≤ Cf * Real.sqrt (g₀.inner y u' u') * Real.sqrt (g₀.inner y v' v') := by
      intro y u' v'
      have hub : ∀ (x : M) (v : TangentSpace I x),
          (D.J ρ (ε m) (u m t)) x v v ≤ (C_ub * Real.sqrt (B k)) * g₀.inner x v v :=
        fun x v => hC_ubb (ε m) (hεmem1 m) (u m t) (huCD m t) (B k) (hB k) (huBnd m t ht k) x v
      have h := hCPb (C_JN * B k) (D.J ρ (ε m) (u m t)) (fun x a b => hJsymm x a b)
        (fun x v hv => huPos m t ht x v hv) hJsm hJbnd (huEll m t ht) hub y u' v'
      have heq : (1 + C_JN * B k) ^ 2 = (1 + C_JN * B k) ^ 2 := rfl
      calc |(Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (D.J ρ (ε m) (u m t))
              (fun x a b => hJsymm x a b) (fun x v hv => huPos m t ht x v hv) hJsm) y u' v'|
          = |Work.Diff.STE.DeTurck.deTurckOp
              (Work.Diff.STE.D.smetOf (I := I) (D.J ρ (ε m) (u m t)) (fun x a b => hJsymm x a b)
                (fun x v hv => huPos m t ht x v hv) hJsm) g₀ y u' v'| := by
            rw [Work.Diff.STE.D.deTurckSec_apply]
        _ ≤ (C_P * (1 + C_JN * B k) ^ 2) * Real.sqrt (g₀.inner y u' u')
              * Real.sqrt (g₀.inner y v' v') := h
        _ = Cf * Real.sqrt (g₀.inner y u' u') * Real.sqrt (g₀.inner y v' v') := by
            rw [hCfdef]
    have hJsym_eq : Work.Diff.STE.D.IsSymm (I := I)
        (D.J ρ (ε m) (u m t)) := hJsymm
    -- apply the mollifier bound
    have hmain := hCJb (ε m) (hεmem1 m)
      (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (D.J ρ (ε m) (u m t))
        (fun x a b => (galState_J_props (I := I) (M := M) D ρ hg hρ (ε m) (hεpos m)
          (c m t)).2.2.1 x a b)
        (fun x v hv => huPos m t ht x v hv)
        ((galState_J_props (I := I) (M := M) D ρ hg hρ (ε m) (hεpos m) (c m t)).2.2.2))
      Cf hCf0 hXbd x u₀ v
    calc |(D.J ρ (ε m) (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (D.J ρ (ε m) (u m t))
            (fun x a b => (galState_J_props (I := I) (M := M) D ρ hg hρ (ε m) (hεpos m)
              (c m t)).2.2.1 x a b)
            (fun x v hv => huPos m t ht x v hv)
            ((galState_J_props (I := I) (M := M) D ρ hg hρ (ε m) (hεpos m)
              (c m t)).2.2.2))) x u₀ v|
        ≤ C_J * Cf * Real.sqrt (g₀.inner x u₀ u₀) * Real.sqrt (g₀.inner x v v) := hmain
      _ = (C_J * Cf) * Real.sqrt (g₀.inner x u₀ u₀) * Real.sqrt (g₀.inner x v v) := by ring
  -- ### hLip
  have hode : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) τ₀ → ∀ (x : M) (u₀ v : TangentSpace I x),
      ∃ R : ℝ, HasDerivWithinAt (fun s : ℝ => u m s x u₀ v) R (Set.Icc (0 : ℝ) τ₀) t ∧
        |R| ≤ (C_J * Cf) * Real.sqrt (g₀.inner x u₀ u₀) * Real.sqrt (g₀.inner x v v) := by
    intro m t ht x u₀ v
    refine ⟨_, ?_, hvs m t ht x u₀ v⟩
    have hJsymm : Work.Diff.STE.D.IsSymm (I := I) (D.J ρ (ε m) (u m t)) := by
      rw [hu]
      exact (galState_J_props (I := I) (M := M) D ρ hg hρ (ε m) (hεpos m) (c m t)).2.2.1
    have hJsm : Work.Diff.STE.D.ChartData (I := I) (M := M) (D.J ρ (ε m) (u m t)) := by
      rw [hu]
      exact (galState_J_props (I := I) (M := M) D ρ hg hρ (ε m) (hεpos m) (c m t)).2.2.2
    have h := (hcsol m).2.2 t ht (fun x a b => hJsymm x a b) hJsm
      (fun x v hv => huPos m t ht x v hv) x u₀ v
    have hux : u m t = galState D (ε m) (c m t) := hu m t
    simpa only [hux] using h
  obtain ⟨L, hL0, hLip⟩ := coeffFun_lipschitz_of_ode (I := I) (M := M) D τ₀ (C_J * Cf) hτ₀
    (mul_nonneg hC_J hCf0) u huCD hode
  exact ⟨τ₀, lam, L, B, ε, u, hτ₀, hlam, hL0, hB, hεmem1, hεtend,
    fun m => ⟨c m, hcsol m, fun t => hu m t⟩, huCD, huBnd, huEll, huPos,
    (fun i a b μ m t ht t' ht' => hLip m i a b μ t ht t' ht')⟩

/-- **The Galerkin family with the Lipschitz bound, unconditional.**  This is
`Work.Diff.STE.Lead.gal_limit_data_of` with its hypothesis `hJpw` discharged by the PROVED
`Work.Diff.STE.Lead.J_pointwise_le`. -/
theorem gal_limit_data
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless] [CompactSpace M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y, 2 < ∑ i, (y i) ^ 2 → ρ y = 0) (hρs : ContDiff ℝ (⊤ : ENat) ρ)
    (hρ1 : ρ 0 = 1)
    (hLC : LCSmooth I M)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (hJN : (∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1,
        ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
        Work.Diff.STE.D.ChartData (I := I) (M := M) h → D.BNorm k (D.J ρ ε h) ≤ C * D.BNorm k h))
    (hGU : GalUniform hLC D ρ) :
    ∃ (τ₀ lam L : ℝ) (B : ℕ → ℝ) (ε : ℕ → ℝ)
      (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M)),
      0 < τ₀ ∧ 0 < lam ∧ 0 ≤ L ∧ (∀ k, 0 ≤ B k) ∧
      (∀ m, ε m ∈ Set.Ioc (0 : ℝ) 1) ∧ Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      (∀ m : ℕ, ∃ c : ℝ → Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) (ε m) → ℝ,
        IsGalSol hLC D ρ (ε m) τ₀ c ∧ (∀ t : ℝ, u m t = galState D (ε m) (c t))) ∧
      (∀ m t, Work.Diff.STE.D.ChartData (I := I) (M := M) (u m t)) ∧
      (∀ m t, t ∈ Set.Icc (0 : ℝ) τ₀ → ∀ k, D.BNorm k (u m t) ≤ B k) ∧
      (∀ m t, t ∈ Set.Icc (0 : ℝ) τ₀ → ∀ (x : M) (v : TangentSpace I x),
        lam * g₀.inner x v v ≤ (D.J ρ (ε m) (u m t)) x v v) ∧
      (∀ m t, t ∈ Set.Icc (0 : ℝ) τ₀ → ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
        0 < (D.J ρ (ε m) (u m t)) x v v) ∧
      (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ) (m : ℕ),
        ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ t' ∈ Set.Ico (0 : ℝ) τ₀,
        ‖coeffFun (I := I) (M := M) D u i a b μ m t
          - coeffFun (I := I) (M := M) D u i a b μ m t'‖ ≤ L * |t - t'|) :=
  gal_limit_data_of (I := I) (M := M) D ρ hρ hρ0 hρs hρ1 hLC hg hJN
    (J_pointwise_le (I := I) (M := M) D ρ hρ hρ0 hρs) hGU

theorem gal_subsequence
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1) (hρ1 : ρ 0 = 1)
    (hρs : ContDiff ℝ (⊤ : ENat) ρ)
    (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (τ₀ lam L : ℝ) (hτ₀ : 0 < τ₀) (hlam : 0 < lam) (hL : 0 ≤ L)
    (B : ℕ → ℝ) (hB : ∀ k, 0 ≤ B k)
    (ε : ℕ → ℝ) (hε : ∀ m, ε m ∈ Set.Ioc (0 : ℝ) 1)
    (hε0 : Filter.Tendsto ε Filter.atTop (nhds 0))
    (u : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (huCD : ∀ (m : ℕ) (t : ℝ), Work.Diff.STE.D.ChartData (I := I) (M := M) (u m t))
    (huBnd : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) τ₀ → ∀ k : ℕ, D.BNorm k (u m t) ≤ B k)
    (huEll : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) τ₀ → ∀ (x : M) (v : TangentSpace I x),
      lam * g₀.inner x v v ≤ (D.J ρ (ε m) (u m t)) x v v)
    (hLip : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ)
      (m : ℕ), ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ t' ∈ Set.Ico (0 : ℝ) τ₀,
      ‖coeffFun (I := I) (M := M) D u i a b μ m t
        - coeffFun (I := I) (M := M) D u i a b μ m t'‖ ≤ L * |t - t'|) :
    ∃ (φ : ℕ → ℕ) (U : ℝ → Work.Diff.STE.Bil (I := I) (M := M)),
      StrictMono φ ∧
      (∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ k : ℕ, D.BNorm k (U t) ≤ B k) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) τ₀, Work.Diff.STE.D.ChartData (I := I) (M := M) (U t)) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ (x : M) (v : TangentSpace I x),
        lam * g₀.inner x v v ≤ (U t) x v v) ∧
      (∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ k : ℕ,
        Filter.Tendsto (fun m : ℕ => D.BNorm k (u (φ m) t - U t)) Filter.atTop (nhds 0)) ∧
      (∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
        TendstoUniformlyOn
          (fun (m : ℕ) (t : ℝ) => coeffFun (I := I) (M := M) D u i a b μ (φ m) t)
          (fun (t : ℝ) => coeffFun (I := I) (M := M) D (fun _ : ℕ => U) i a b μ 0 t)
          Filter.atTop (Set.Ico (0 : ℝ) τ₀)) := by
  classical
  obtain ⟨d₀, hd₀pos, hd₀b⟩ :=
    Work.Diff.STE.B3.dens_lower_bound (I := I) (M := M) D
      (fun i => Work.Diff.STE.B3.densGood (I := I) (M := M) D i)
  have hdens : ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ (i : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ),
      ‖z‖ ≤ 2 * D.σ i → d₀ ≤ D.dens i z := ⟨d₀, hd₀pos, hd₀b⟩
  obtain ⟨φ, hφ, U, hUB, hUC, hUconv, hUc⟩ :=
    exists_subseq_coeff_limit_noPos (I := I) (M := M) D τ₀ hτ₀ B hB u huCD hg huBnd
      (fun _ _ _ _ => L) (fun _ _ _ _ => hL) hLip hdens
  refine ⟨φ, U, hφ, hUB, hUC, ?_, hUconv, hUc⟩
  -- positivity of the limit, from `limit_positivity` applied to the subsequence
  -- (the auxiliary lemma wants `ChartData (U t)` for *every* real `t`; use a junk extension)
  set U' : ℝ → Work.Diff.STE.Bil (I := I) (M := M) :=
    fun t => if t ∈ Set.Ico (0 : ℝ) τ₀ then U t else g₀.inner with hU'def
  have hU'eq : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, U' t = U t := fun t ht => dif_pos ht
  have hCDU' : ∀ t : ℝ, Work.Diff.STE.D.ChartData (I := I) (M := M) (U' t) := by
    intro t
    by_cases ht : t ∈ Set.Ico (0 : ℝ) τ₀
    · rw [hU'eq t ht]; exact hUC t ht
    · rw [show U' t = g₀.inner from dif_neg ht]; exact hg
  have hposU' : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ (x : M) (v : TangentSpace I x),
      lam * g₀.inner x v v ≤ (U' t) x v v :=
    limit_positivity (I := I) (M := M) D ρ hρ1 hρ hρs τ₀ lam hτ₀ hlam
      (Module.finrank ℝ E + 1) (by rw [Fintype.card_fin]; omega) hdens
      (fun m => u (φ m)) (fun m t => huCD (φ m) t) (fun m => ε (φ m))
      (fun m => hε (φ m)) (hε0.comp hφ.tendsto_atTop) B hB
      (fun m t ht k => huBnd (φ m) t ht k) (fun m t ht x v => huEll (φ m) t ht x v) U' hCDU'
      (fun t ht k => by rw [hU'eq t ht]; exact hUconv t ht k)
  intro t ht x v
  rw [← hU'eq t ht]
  exact hposU' t ht x v

lemma smetOf_congr_of_eq
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {h h' : Work.Diff.STE.Bil (I := I) (M := M)} (he : h = h')
    (p1 : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    (p2 : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v)
    (p3 : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (q1 : ∀ (x : M) (u v : TangentSpace I x), h' x u v = h' x v u)
    (q2 : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h' x v v)
    (q3 : Work.Diff.STE.D.ChartData (I := I) (M := M) h') :
    (Work.Diff.STE.D.smetOf (I := I) h p1 p2 p3 : SMet I M)
      = Work.Diff.STE.D.smetOf (I := I) h' q1 q2 q3 := by
  subst he
  simp only [Work.Diff.STE.D.smetOf]

theorem deTurck_limit
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [T2Space M] [I.Boundaryless] [CompactSpace M]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (ρ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ) (hρ : ∀ y, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : Fin (Module.finrank ℝ E) → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρ1 : ρ 0 = 1)
    (hLC : LCSmooth I M) (hLV : LCVariation I M) (hg : Work.Diff.STE.D.ChartData (I := I) (M := M) g₀.inner)
    (hJN : (∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ ε ∈ Set.Ioc (0 : ℝ) 1, ∀ h : Work.Diff.STE.Bil (I := I) (M := M),
        Work.Diff.STE.D.ChartData (I := I) (M := M) h → D.BNorm k (D.J ρ ε h) ≤ C * D.BNorm k h))
    (hJT : (∀ (k : ℕ) (h : Work.Diff.STE.Bil (I := I) (M := M)), Work.Diff.STE.D.ChartData (I := I) (M := M) h →
        Filter.Tendsto (fun ε => D.BNorm k (D.J ρ ε h - h)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)))
    (hGU : GalUniform hLC D ρ) :
    ∃ τ : ℝ, 0 < τ ∧ ∃ G : ℝ → SMet I M, G 0 = g₀ ∧ JointSmooth G (Icc 0 τ) ∧
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) I.tangent ∞
        (fun p : ℝ × M ↦ (⟨p.2, Work.Diff.STE.DeTurck.deTurckVec (G p.1) g₀ p.2⟩ : TangentBundle I M))
        (Icc 0 τ ×ˢ univ) ∧
      ∀ t ∈ Ico 0 τ, ∀ (x : M) (u v : TangentSpace I x),
        HasDerivWithinAt (fun s ↦ (G s).inner x u v)
          (-2 * ricAt (lcOf (G t)) x u v
            + (G t).inner x (lcOf (G t) (fun y ↦ Work.Diff.STE.DeTurck.deTurckVec (G t) g₀ y) x u) v
            + (G t).inner x u (lcOf (G t) (fun y ↦ Work.Diff.STE.DeTurck.deTurckVec (G t) g₀ y) x v))
          (Ico 0 τ) t := by
  classical
  obtain ⟨τ₀, lam, L, B, ε, u, hτ₀, hlam, hL, hB, hε, hε0, hgal, huCD, huBnd, huEll, huPos, hLip⟩ :=
    gal_limit_data (I := I) (M := M) D ρ hρ hρ0 hρs hρ1 hLC hg hJN hGU
  obtain ⟨φ, U, hφ, hUB, hUC, hUp, hUconv, hUc⟩ :=
    gal_subsequence (I := I) (M := M) D ρ hρ hρ1 hρs hg τ₀ lam L hτ₀ hlam hL B hB ε hε hε0
      u huCD huBnd huEll hLip
  -- symmetry and positivity of every slice `U t`
  have hsymU : ∀ t ∈ Set.Ico (0:ℝ) τ₀, ∀ (x : M) (p q : TangentSpace I x),
      (U t) x p q = (U t) x q p := by
    intro t ht x p q
    have hsymm : ∀ (m : ℕ) (x : M) (p q : TangentSpace I x),
        u (φ m) t x p q = u (φ m) t x q p := by
      intro m x p q
      obtain ⟨c, _hsol, huc⟩ := hgal (φ m)
      rw [huc t]
      exact Work.Diff.STE.D.isSymm_addSec_genMap (I := I) (M := M) (ι₀ := ι₀) (g₀ := g₀)
        D (ε (φ m)) (c t) x p q
    exact isSymm_of_BNorm_tendsto (I := I) (M := M) D (fun m => u (φ m) t) (U t) id
      (fun m => huCD (φ m) t) (hUC t ht) hsymm (fun k => hUconv t ht k) x p q
  have hposU : ∀ t ∈ Set.Ico (0:ℝ) τ₀, ∀ (x : M) (v : TangentSpace I x), v ≠ 0 →
      0 < (U t) x v v := by
    intro t ht x v hv
    have h1 : 0 < lam * g₀.inner x v v := mul_pos hlam ((g₀.pos x v hv))
    exact lt_of_lt_of_le h1 (hUp t ht x v)
  -- the junk extension of `U` (so that the `∀ t` hypotheses of the delegated lemmas are met)
  set Uj : ℝ → Work.Diff.STE.Bil (I := I) (M := M) :=
    fun t => if t ∈ Set.Ico (0:ℝ) τ₀ then U t else g₀.inner with hUjdef
  have hUjeq : ∀ t ∈ Set.Ico (0:ℝ) τ₀, Uj t = U t := fun t ht => dif_pos ht
  have hUjCD : ∀ t : ℝ, Work.Diff.STE.D.ChartData (I := I) (M := M) (Uj t) := by
    intro t
    by_cases ht : t ∈ Set.Ico (0:ℝ) τ₀
    · rw [hUjeq t ht]; exact hUC t ht
    · rw [show Uj t = g₀.inner from dif_neg ht]; exact hg
  have hUjB : ∀ t ∈ Set.Ico (0:ℝ) τ₀, ∀ k : ℕ, D.BNorm k (Uj t) ≤ B k := by
    intro t ht k
    rw [hUjeq t ht]; exact hUB t ht k
  -- ((3)) `hdecU`: rapid decay of the Fourier coefficients of the limit
  have hdecU : ∀ M₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0:ℝ) τ₀,
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (U t) a b) μ‖ * (Work.Diff.STE.wt μ) ^ M₀ ≤ C := by
    intro M₀
    obtain ⟨C, hC0, hCb⟩ :=
      coeff_decay_of_BNorm_le (I := I) (M := M) D τ₀ Uj hUjCD B hB hUjB M₀
    exact ⟨C, hC0, fun t ht i a b μ => by rw [← hUjeq t ht]; exact hCb t ht i a b μ⟩
  -- ((7a)) a uniform pointwise upper bound for the limit, from `BNorm` bounds
  have hKup : ∃ K₀ : ℝ, 0 < K₀ ∧ ∀ t ∈ Set.Ico (0:ℝ) τ₀, ∀ (x : M) (v : TangentSpace I x),
      (U t) x v v ≤ K₀ * g₀.inner x v v := by
    obtain ⟨d₀, hd₀pos, hd₀⟩ := Work.Diff.STE.B3.dens_lower_bound (I := I) (M := M) D
      (fun i => Work.Diff.STE.B3.densGood (I := I) (M := M) D i)
    have hk : Fintype.card (Fin (Module.finrank ℝ E)) < 2 * (Module.finrank ℝ E + 1) := by
      rw [Fintype.card_fin]; omega
    obtain ⟨C, hC0, hCb⟩ := pointwise_le_sqrt_BNorm_uniform (I := I) (M := M) D
      (Module.finrank ℝ E + 1) hk ⟨d₀, hd₀pos, hd₀⟩
    refine ⟨max (C * Real.sqrt (B (Module.finrank ℝ E + 1))) 1, ?_,
      fun t ht x v => ?_⟩
    · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    · by_cases hv : v = 0
      · subst hv
        simp
      · have hcd : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
            ContDiff ℝ (⊤ : ℕ∞) (D.Rper i (U t) a b) :=
          fun i a b => (Work.Diff.STE.Lead.Rper_contDiff_and_periodic (I := I) (M := M) D (U t)
            (hUC t ht) i a b).1
        have hper : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
            Work.Diff.STE.Periodic1 (D.Rper i (U t) a b) :=
          fun i a b => (Work.Diff.STE.Lead.Rper_contDiff_and_periodic (I := I) (M := M) D (U t)
            (hUC t ht) i a b).2
        have hb := hCb (U t) hcd hper x v v
        have hgv : 0 ≤ g₀.inner x v v := (g₀.pos x v hv).le
        have hsq : Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) = g₀.inner x v v :=
          Real.mul_self_sqrt hgv
        have hrt : Real.sqrt (D.BNorm (Module.finrank ℝ E + 1) (U t))
            ≤ Real.sqrt (B (Module.finrank ℝ E + 1)) :=
          Real.sqrt_le_sqrt (hUB t ht _)
        have hle : |(U t) x v v| ≤ C * Real.sqrt (B (Module.finrank ℝ E + 1))
            * g₀.inner x v v := by
          have hd : 0 ≤ Real.sqrt (g₀.inner x v v) := Real.sqrt_nonneg _
          calc |(U t) x v v|
              ≤ C * Real.sqrt (D.BNorm (Module.finrank ℝ E + 1) (U t))
                * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) := hb
            _ ≤ C * Real.sqrt (B (Module.finrank ℝ E + 1))
                * Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v) :=
                mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrt hC0) hd) hd
            _ = C * Real.sqrt (B (Module.finrank ℝ E + 1))
                * (Real.sqrt (g₀.inner x v v) * Real.sqrt (g₀.inner x v v)) := by ring
            _ = C * Real.sqrt (B (Module.finrank ℝ E + 1)) * g₀.inner x v v := by
                rw [Real.mul_self_sqrt hgv]
        calc (U t) x v v ≤ |(U t) x v v| := le_abs_self _
          _ ≤ C * Real.sqrt (B (Module.finrank ℝ E + 1)) * g₀.inner x v v := hle
          _ ≤ max (C * Real.sqrt (B (Module.finrank ℝ E + 1))) 1 * g₀.inner x v v :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hgv
  obtain ⟨K₀, hK₀pos, hK₀b⟩ := hKup
  -- `Uj` has symmetry / positivity / the upper pinch at EVERY time
  have hUjsym : ∀ (t : ℝ) (x : M) (p q : TangentSpace I x), Uj t x p q = Uj t x q p := by
    intro t x p q
    by_cases ht : t ∈ Set.Ico (0:ℝ) τ₀
    · rw [hUjeq t ht]; exact hsymU t ht x p q
    · rw [show Uj t = g₀.inner from dif_neg ht]; exact g₀.symm x p q
  have hUjpos : ∀ (t : ℝ) (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < Uj t x v v := by
    intro t x v hv
    by_cases ht : t ∈ Set.Ico (0:ℝ) τ₀
    · rw [hUjeq t ht]; exact hposU t ht x v hv
    · rw [show Uj t = g₀.inner from dif_neg ht]; exact g₀.pos x v hv
  have hUjup : ∀ t ∈ Set.Ico (0:ℝ) τ₀, ∀ (x : M) (v : TangentSpace I x),
      Uj t x v v ≤ K₀ * g₀.inner x v v := by
    intro t ht x v
    rw [hUjeq t ht]; exact hK₀b t ht x v
  -- the DeTurck operator of the limit
  set W : ℝ → Work.Diff.STE.Bil (I := I) (M := M) :=
    fun t => Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (Uj t) (hUjsym t) (hUjpos t) (hUjCD t)
    with hWdef
  -- ((7b)) the uniform jet bound needed by `BNorm_deTurckSec_le`, from `mat_jet_bound_of_energy`
  have hjet : ∀ k : ℕ, ∃ K : ℝ, 0 < K ∧ ∀ t ∈ Set.Ico (0:ℝ) τ₀,
      ∀ (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (m : ℕ) (hm : m ≤ k + 1)
        (β : Fin m → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
        ‖z‖ ≤ 2 * D.σ i →
        ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((D.mat i (Uj t) c d y : ℝ) : ℂ)) z‖ ≤ K := by
    intro k
    obtain ⟨C, hC0, hCb⟩ := Work.Diff.STE.B3.mat_jet_bound_of_energy (I := I) (M := M) D
      (Module.finrank ℝ E + 2 * (k + 1) + 2)
    obtain ⟨C₁, hC₁0, hC₁b⟩ := ENormB_le_BNorm_uniform (I := I) (M := M) D
      (Module.finrank ℝ E + 2 * (k + 1) + 2)
    refine ⟨max (C * (1 + Real.sqrt (C₁ * B (Module.finrank ℝ E + 2 * (k + 1) + 2)))) 1,
      lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
    intro t ht i c d m hm β z hz
    have hcdR : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
        ContDiff ℝ (⊤ : ℕ∞) (D.R i (Uj t) a b) := fun i a b =>
      Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D (Uj t) (hUjCD t) i a b
    have he : D.ENormB (Module.finrank ℝ E + 2 * (k + 1) + 2) (Uj t)
        ≤ C₁ * B (Module.finrank ℝ E + 2 * (k + 1) + 2) := by
      refine le_trans (hC₁b (Uj t) hcdR) ?_
      exact mul_le_mul_of_nonneg_left (hUjB t ht _) hC₁0
    have hmk : 2 * m + Module.finrank ℝ E
        < 2 * (Module.finrank ℝ E + 2 * (k + 1) + 2) := by omega
    have h1 := hCb (Uj t) (hUjCD t) i c d m hmk β z hz
    have h2 : Real.sqrt (D.ENormB (Module.finrank ℝ E + 2 * (k + 1) + 2) (Uj t))
        ≤ Real.sqrt (C₁ * B (Module.finrank ℝ E + 2 * (k + 1) + 2)) := Real.sqrt_le_sqrt he
    calc ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((D.mat i (Uj t) c d y : ℝ) : ℂ)) z‖
        ≤ C * (1 + Real.sqrt (D.ENormB (Module.finrank ℝ E + 2 * (k + 1) + 2) (Uj t))) := h1
      _ ≤ C * (1 + Real.sqrt (C₁ * B (Module.finrank ℝ E + 2 * (k + 1) + 2))) := by
          exact mul_le_mul_of_nonneg_left (by linarith) hC0
      _ ≤ max (C * (1 + Real.sqrt (C₁ * B (Module.finrank ℝ E + 2 * (k + 1) + 2)))) 1 :=
          le_max_left _ _
  -- ((7c)) uniform `BNorm` bounds on the DeTurck operator of the limit, at every level
  have hWB : ∃ CW : ℕ → ℝ, (∀ k : ℕ, 0 ≤ CW k) ∧
      ∀ t ∈ Set.Ico (0:ℝ) τ₀, ∀ k : ℕ, D.BNorm k (W t) ≤ CW k := by
    have hstep : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0:ℝ) τ₀,
        D.BNorm k (W t) ≤ C := by
      intro k
      obtain ⟨KJ, hKJpos, hKJ⟩ := hjet k
      set K : ℝ := max K₀ KJ with hKdef
      have hKpos : 0 < K := lt_of_lt_of_le hK₀pos (le_max_left _ _)
      obtain ⟨C, hC0, hCb⟩ := BNorm_deTurckSec_le (I := I) (M := M) D hLC k B hB lam K hlam hKpos
      refine ⟨C, hC0, fun t ht => ?_⟩
      rw [hWdef]
      refine hCb (Uj t) (hUjsym t) (hUjpos t) (hUjCD t) (fun j => hUjB t ht j) ?_ ?_ ?_
      · intro x v
        rw [hUjeq t ht]
        exact hUp t ht x v
      · intro x v
        by_cases hv : v = 0
        · subst hv; simp
        · have hgv : 0 ≤ g₀.inner x v v := (g₀.pos x v hv).le
          exact le_trans (hUjup t ht x v)
            (mul_le_mul_of_nonneg_right (le_max_left _ _) hgv)
      · intro i c d m hm β z hz
        exact le_trans (hKJ t ht i c d m hm β z hz) (le_max_right _ _)
    choose CW hCW using hstep
    exact ⟨CW, fun k => (hCW k).1, fun t ht k => (hCW k).2 t ht⟩
  -- ((7d)) the `ℓ¹` majorant of the coefficients of `W t`
  have hWsum : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ∃ g : (Fin (Module.finrank ℝ E) → ℤ) → ℝ, Summable g ∧ ∀ t ∈ Set.Ico (0:ℝ) τ₀,
        ∀ μ : Fin (Module.finrank ℝ E) → ℤ,
        ‖Work.Diff.STE.fourierCoeff (D.Rper i (W t) a b) μ‖ ≤ g μ := by
    obtain ⟨CW, hCW0, hCWb⟩ := hWB
    -- enlarge the constant family so that it also covers the endpoint `t = τ₀`
    set CWe : ℕ → ℝ := fun k => max (CW k) (D.BNorm k (W τ₀)) with hCWedef
    have hCWe0 : ∀ k : ℕ, 0 ≤ CWe k := fun k =>
      le_trans (hCW0 k) (le_max_left _ _)
    have hCWeb : ∀ t ∈ Set.Icc (0:ℝ) τ₀, ∀ k : ℕ, D.BNorm k (W t) ≤ CWe k := by
      intro t ht k
      rcases lt_or_eq_of_le ht.2 with hlt | heq
      · exact le_trans (hCWb t ⟨ht.1, hlt⟩ k) (le_max_left _ _)
      · subst heq
        exact le_max_right _ _
    have hk : Fintype.card (Fin (Module.finrank ℝ E))
        < 2 * (Module.finrank ℝ E + 1) := by rw [Fintype.card_fin]; omega
    have hsumm : Summable (fun μ : Fin (Module.finrank ℝ E) → ℤ =>
        Real.sqrt (CWe (2 * (Module.finrank ℝ E + 1)))
          / (Work.Diff.STE.wt μ) ^ (Module.finrank ℝ E + 1)) := by
      have h1 : Summable (fun μ : Fin (Module.finrank ℝ E) → ℤ =>
          Real.sqrt (CWe (2 * (Module.finrank ℝ E + 1)))
            * (Work.Diff.STE.wt μ) ^ (-(((Module.finrank ℝ E + 1 : ℕ)) : ℤ))) :=
        Summable.mul_left _ (Work.Diff.STE.summable_wt_zpow (Module.finrank ℝ E + 1) hk)
      refine h1.congr (fun μ => ?_)
      rw [zpow_neg, zpow_natCast, div_eq_mul_inv]
    intro i a b
    obtain ⟨hC'0, hC'b⟩ := coeffFun_bound_and_decay (I := I) (M := M) D τ₀ CWe
      (fun _ : ℕ => W)
      (fun m t' i a b => (Work.Diff.STE.Lead.Rper_contDiff_and_periodic (I := I) (M := M) D (W t')
        (by
          rw [hWdef]
          exact Work.Diff.STE.B3.chartData_deTurckSec (I := I) (M := M) hLC (Uj t')
            (hUjsym t') (hUjpos t') (hUjCD t')) i a b).1)
      (fun m t' i a b => (Work.Diff.STE.Lead.Rper_contDiff_and_periodic (I := I) (M := M) D (W t')
        (by
          rw [hWdef]
          exact Work.Diff.STE.B3.chartData_deTurckSec (I := I) (M := M) hLC (Uj t')
            (hUjsym t') (hUjpos t') (hUjCD t')) i a b).2)
      (fun m t' ht' k => hCWeb t' ht' k) (hCWe0 0)
    refine ⟨fun μ => Real.sqrt (CWe (2 * (Module.finrank ℝ E + 1)))
        / (Work.Diff.STE.wt μ) ^ (Module.finrank ℝ E + 1), hsumm, fun t ht μ => ?_⟩
    have h := hC'b (Module.finrank ℝ E + 1) i a b μ 0 t
      (⟨ht.1, le_of_lt ht.2⟩ : t ∈ Set.Icc (0:ℝ) τ₀)
    have hwt : 0 < (Work.Diff.STE.wt μ) ^ (Module.finrank ℝ E + 1) :=
      pow_pos (Work.Diff.STE.wt_pos μ) _
    rw [le_div_iff₀ hwt]
    simpa using h
  -- ((8)) `BNorm`-continuity of the limit in time
  have hcont : ∀ t ∈ Set.Ico (0:ℝ) τ₀, ∀ k : ℕ,
      Filter.Tendsto (fun σ : ℝ => D.BNorm k (U σ - U t))
        (nhdsWithin t (Set.Ico (0:ℝ) τ₀)) (nhds 0) :=
    BNorm_continuous_of_coeff_lipschitz (I := I) (M := M) D τ₀ B hB L hL
      (fun m => u (φ m)) U (fun m t => huCD (φ m) t) (fun t ht => hUC t ht)
      (fun m t ht k => huBnd (φ m) t ht k) hUB
      (fun i a b μ m t ht t' ht' => hLip i a b μ (φ m) t ht t' ht') hUc
  have hcontj : ∀ t ∈ Set.Ico (0:ℝ) τ₀, ∀ k : ℕ,
      Filter.Tendsto (fun σ : ℝ => D.BNorm k (Uj σ - Uj t))
        (nhdsWithin t (Set.Ico (0:ℝ) τ₀)) (nhds 0) := by
    intro t ht k
    refine (hcont t ht k).congr' ?_
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    rw [hUjeq σ hσ, hUjeq t ht]
  -- ((9)) the uniform pointwise bound on the DeTurck operator of the limit
  have hdb : ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0:ℝ) τ₀, ∀ (x : M) (u v : TangentSpace I x),
      |Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (Uj t) (hUjsym t) (hUjpos t) (hUjCD t) x u v|
        ≤ C * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) := by
    have hk : Module.finrank ℝ E + 12 < 2 * (Module.finrank ℝ E + 14) := by omega
    obtain ⟨⟨C, hC0, hCb⟩, _⟩ :=
      deTurck_bound (I := I) (M := M) D hLC (Module.finrank ℝ E + 14) hk lam K₀ hlam
    refine ⟨C * (1 + B (Module.finrank ℝ E + 14)) ^ 2, mul_nonneg hC0 (by positivity), ?_⟩
    intro t ht x u v
    rw [Work.Diff.STE.D.deTurckSec_apply]
    exact hCb (B (Module.finrank ℝ E + 14)) (Uj t) (hUjsym t) (hUjpos t) (hUjCD t)
      (hUjB t ht _) (fun x' v' => by rw [hUjeq t ht]; exact hUp t ht x' v')
      (fun x' v' => hUjup t ht x' v') x u v
  -- ((10)) continuity in time of the coefficients of the DeTurck operator of the limit
  have hcontW : ∀ t ∈ Set.Ico (0:ℝ) τ₀, ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ),
      ContinuousWithinAt (fun σ : ℝ =>
        Work.Diff.STE.fourierCoeff (D.Rper i (W σ) a b) μ) (Set.Ico (0:ℝ) τ₀) t := by
    obtain ⟨Cdb, hCdb0, hCdbb⟩ := hdb
    intro t ht i a b μ
    refine continuous_fourierCoeff_deTurckSec (I := I) (M := M) D hLC τ₀ B hB lam
      (max K₀ Cdb) hlam (lt_of_lt_of_le hK₀pos (le_max_left _ _)) Uj hUjCD hUjsym hUjpos hUjB
      ?_ ?_ ?_ hcontj i a b μ t ht
    · intro σ hσ x v
      rw [hUjeq σ hσ]; exact hUp σ hσ x v
    · intro σ hσ x v
      by_cases hv : v = 0
      · subst hv; simp
      · have hgv : 0 ≤ g₀.inner x v v := (g₀.pos x v hv).le
        exact le_trans (hUjup σ hσ x v)
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hgv)
    · intro σ hσ x u v
      calc |Work.Diff.STE.D.deTurckSec (I := I) hLC g₀ (Uj σ) (hUjsym σ) (hUjpos σ) (hUjCD σ) x u v|
          ≤ Cdb * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) := hCdbb σ hσ x u v
        _ ≤ max K₀ Cdb * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.sqrt_nonneg _))
              (Real.sqrt_nonneg _)
  -- ###### STEP 11: the per-`m` Galerkin coefficients, the velocity sections and their ODE
  choose cf hcfsol hcfu using hgal
  have hgalJ : ∀ (m : ℕ) (t : ℝ),
      Work.Diff.STE.D.IsSymm (I := I) (galState D (ε m) (cf m t)) ∧
      Work.Diff.STE.D.ChartData (I := I) (M := M) (galState D (ε m) (cf m t)) ∧
      Work.Diff.STE.D.IsSymm (I := I) (D.J ρ (ε m) (galState D (ε m) (cf m t))) ∧
      Work.Diff.STE.D.ChartData (I := I) (M := M)
        (D.J ρ (ε m) (galState D (ε m) (cf m t))) :=
    fun m t => galState_J_props (I := I) (M := M) D ρ hg hρ (ε m) (hε m).1 (cf m t)
  have hsymJ : ∀ (m : ℕ) (t : ℝ),
      Work.Diff.STE.D.IsSymm (I := I) (D.J ρ (ε m) (galState D (ε m) (cf m t))) :=
    fun m t => (hgalJ m t).2.2.1
  have hsmJ : ∀ (m : ℕ) (t : ℝ), Work.Diff.STE.D.ChartData (I := I) (M := M)
      (D.J ρ (ε m) (galState D (ε m) (cf m t))) := fun m t => (hgalJ m t).2.2.2
  have hsymg : ∀ (m : ℕ) (t : ℝ),
      Work.Diff.STE.D.IsSymm (I := I) (galState D (ε m) (cf m t)) :=
    fun m t => (hgalJ m t).1
  have hCDg : ∀ (m : ℕ) (t : ℝ),
      Work.Diff.STE.D.ChartData (I := I) (M := M) (galState D (ε m) (cf m t)) :=
    fun m t => (hgalJ m t).2.1
  set vs : ℕ → ℝ → Work.Diff.STE.Bil (I := I) (M := M) := fun m t =>
    if ht : t ∈ Set.Icc (0 : ℝ) τ₀ then
      D.J ρ (ε m) (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀
        (D.J ρ (ε m) (galState D (ε m) (cf m t))) (fun x a b => hsymJ m t x a b)
        (fun x v hv => by rw [← hcfu m t]; exact huPos m t ht x v hv) (hsmJ m t))
    else 0 with hvsdef
  have hvseq : ∀ (m : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) τ₀),
      vs m t = D.J ρ (ε m) (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀
        (D.J ρ (ε m) (galState D (ε m) (cf m t))) (fun x a b => hsymJ m t x a b)
        (fun x v hv => by rw [← hcfu m t]; exact huPos m t ht x v hv) (hsmJ m t)) := by
    intro m t ht
    rw [hvsdef]
    exact dif_pos ht
  have hode : ∀ (m : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) τ₀ →
      ∀ (x : M) (u₀ v : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => u m s x u₀ v) (vs m t x u₀ v) (Set.Icc (0 : ℝ) τ₀) t := by
    intro m t ht x u₀ v
    rw [hvseq m t ht]
    have h := (hcfsol m).2.2 t ht (hsymJ m t) (hsmJ m t)
      (fun x v hv => by rw [← hcfu m t]; exact huPos m t ht x v hv) x u₀ v
    simpa only [hcfu] using h
  -- ###### the uniform pointwise bound on the velocities
  obtain ⟨d₀, hd₀pos, hd₀b⟩ := Work.Diff.STE.B3.dens_lower_bound (I := I) (M := M) D
    (fun i => Work.Diff.STE.B3.densGood (I := I) (M := M) D i)
  have hg₀nn : ∀ (x : M) (v : TangentSpace I x), 0 ≤ g₀.inner x v v := by
    intro x v
    by_cases hv : v = 0
    · subst hv; simp
    · exact (g₀.pos x v hv).le
  have hkA : Module.finrank ℝ E + 12 < 2 * (Module.finrank ℝ E + 13) := by omega
  have hkB : Fintype.card (Fin (Module.finrank ℝ E)) < 2 * (Module.finrank ℝ E + 13) := by
    rw [Fintype.card_fin]; omega
  obtain ⟨C_ub, hC_ub, hC_ubb⟩ := J_upper_bound (I := I) (M := M) D ρ hρ
    (Module.finrank ℝ E + 13) hkB ⟨d₀, hd₀pos, hd₀b⟩ hJN
  obtain ⟨C_JN, hC_JN, hCJNb⟩ := hJN (Module.finrank ℝ E + 13)
  obtain ⟨C_P, hC_P, hCPb⟩ :=
    (deTurck_bound (I := I) (M := M) D hLC (Module.finrank ℝ E + 13) hkA lam
      (C_ub * Real.sqrt (B (Module.finrank ℝ E + 13))) hlam).1
  set Cf : ℝ := C_P * (1 + C_JN * B (Module.finrank ℝ E + 13)) ^ 2 with hCfdef
  have hCf0 : 0 ≤ Cf := by rw [hCfdef]; positivity
  obtain ⟨C_J, hC_J, hCJb⟩ := J_pointwise_le (I := I) (M := M) D ρ hρ hρ0 hρs
  have hvsb : ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (t : ℝ), t ∈ Set.Icc (0 : ℝ) τ₀ →
      ∀ (x : M) (u₀ v : TangentSpace I x),
      |vs m t x u₀ v| ≤ C * Real.sqrt (g₀.inner x u₀ u₀) * Real.sqrt (g₀.inner x v v) := by
    refine ⟨C_J * Cf, mul_nonneg hC_J hCf0, fun m t ht x u₀ v => ?_⟩
    rw [hvseq m t ht]
    have hhub : ∀ (x' : M) (v' : TangentSpace I x'),
        (D.J ρ (ε m) (galState D (ε m) (cf m t))) x' v' v'
          ≤ (C_ub * Real.sqrt (B (Module.finrank ℝ E + 13))) * g₀.inner x' v' v' :=
      fun x' v' => by
        rw [← hcfu m t]
        exact hC_ubb (ε m) (hε m) (u m t) (huCD m t) (B (Module.finrank ℝ E + 13))
          (hB _) (huBnd m t ht _) x' v'
    have hXbound : ∀ (y : M) (u' v' : TangentSpace I y),
        |Work.Diff.STE.D.deTurckSec (I := I) hLC g₀
          (D.J ρ (ε m) (galState D (ε m) (cf m t))) (fun x a b => hsymJ m t x a b)
          (fun x v hv => by rw [← hcfu m t]; exact huPos m t ht x v hv) (hsmJ m t) y u' v'|
          ≤ Cf * Real.sqrt (g₀.inner y u' u') * Real.sqrt (g₀.inner y v' v') := by
      intro y u' v'
      have h := hCPb (C_JN * B (Module.finrank ℝ E + 13))
        (D.J ρ (ε m) (galState D (ε m) (cf m t))) (fun x a b => hsymJ m t x a b)
        (fun x v hv => by rw [← hcfu m t]; exact huPos m t ht x v hv) (hsmJ m t)
        (by
          rw [← hcfu m t]
          exact le_trans (hCJNb (ε m) (hε m) (u m t) (huCD m t))
            (mul_le_mul_of_nonneg_left (huBnd m t ht _) hC_JN))
        (fun x v => by rw [← hcfu m t]; exact huEll m t ht x v)
        (fun x v => hhub x v) y u' v'
      calc |Work.Diff.STE.D.deTurckSec (I := I) hLC g₀
            (D.J ρ (ε m) (galState D (ε m) (cf m t))) (fun x a b => hsymJ m t x a b)
            (fun x v hv => by rw [← hcfu m t]; exact huPos m t ht x v hv) (hsmJ m t) y u' v'|
          = |Work.Diff.STE.DeTurck.deTurckOp
              (Work.Diff.STE.D.smetOf (I := I)
                (D.J ρ (ε m) (galState D (ε m) (cf m t))) (fun x a b => hsymJ m t x a b)
                (fun x v hv => by rw [← hcfu m t]; exact huPos m t ht x v hv)
                (hsmJ m t)) g₀ y u' v'| := by
            simp only [Work.Diff.STE.D.deTurckSec_apply]
        _ ≤ (C_P * (1 + C_JN * B (Module.finrank ℝ E + 13)) ^ 2)
              * Real.sqrt (g₀.inner y u' u') * Real.sqrt (g₀.inner y v' v') := h
        _ = Cf * Real.sqrt (g₀.inner y u' u') * Real.sqrt (g₀.inner y v' v') := by
            rw [hCfdef]
    exact hCJb (ε m) (hε m) (Work.Diff.STE.D.deTurckSec (I := I) hLC g₀
      (D.J ρ (ε m) (galState D (ε m) (cf m t))) (fun x a b => hsymJ m t x a b)
      (fun x v hv => by rw [← hcfu m t]; exact huPos m t ht x v hv) (hsmJ m t))
      Cf hCf0 hXbound x u₀ v
  -- ###### `hvsmeas`: a.e.-measurability of the coefficients of the velocities
  have hvsmeas : ∀ (m : ℕ) (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ),
      AEMeasurable (fun σ : ℝ => Work.Diff.STE.fourierCoeff (D.Rper i (vs m σ) a b) μ)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict (Set.Icc (0 : ℝ) τ₀)) :=
    fun m i a b μ => Work.Diff.STE.Lead.fourierCoeff_vs_aemeasurable (I := I) (M := M) D hτ₀
      (u m) (vs m) (fun t => huCD m t) (fun t ht x u₀ v => hode m t ht x u₀ v) i a b μ
  -- ###### the `BNorm`-convergence of the velocities of the Galerkin family
  have hconvj : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ k : ℕ,
      Filter.Tendsto (fun m : ℕ => D.BNorm k (u (φ m) t - Uj t)) Filter.atTop (nhds 0) := by
    intro t ht k
    refine (hUconv t ht k).congr' ?_
    filter_upwards with m
    rw [hUjeq t ht]
  -- ###### additivity of the Friedrichs mollifier in the section
  have hJadd_loc : ∀ (m : ℕ) (t : ℝ) (X : Work.Diff.STE.Bil (I := I) (M := M))
      (hCDX : Work.Diff.STE.D.ChartData (I := I) (M := M) X)
      (hsymX : Work.Diff.STE.D.IsSymm (I := I) X),
      D.J ρ (ε m) (galState D (ε m) (cf m t)) =
        D.J ρ (ε m) (galState D (ε m) (cf m t) - X) + D.J ρ (ε m) X := by
    intro m t X hCDX hsymX
    have hab : (galState D (ε m) (cf m t) - X) + X = galState D (ε m) (cf m t) :=
      sub_add_cancel (galState D (ε m) (cf m t)) X
    have h := Work.Diff.STE.Lead.J_add' (I := I) (M := M) D ρ (ε m) (hε m).1 hρ0
      (galState D (ε m) (cf m t) - X) X
      (Work.Diff.STE.Lead.ChartData_sub (I := I) (M := M) _ _ (hCDg m t) hCDX)
      hCDX (Work.Diff.STE.Lead.IsSymm_sub (I := I) (M := M) (hsymg m t) hsymX) hsymX
    exact (congrArg (fun Z => D.J ρ (ε m) Z) hab).symm.trans h
  -- the periodised components whose `BNorm` appears in the triangle inequality
  have hRper1 : ∀ (t : ℝ) (m : ℕ), ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i (D.J ρ (ε (φ m))
        (galState D (ε (φ m)) (cf (φ m) t) - Uj t)) a b) := fun t m i a b =>
    (Work.Diff.STE.Lead.Rper_contDiff_and_periodic (I := I) (M := M) D _
      (Work.Diff.STE.Lead.chartData_J_props (I := I) (M := M) D ρ hρ (ε (φ m)) _
        (Work.Diff.STE.Lead.ChartData_sub (I := I) (M := M) _ _
          (hCDg (φ m) t) (hUjCD t))) i a b).1
  have hRper2 : ∀ (t : ℝ) (m : ℕ), ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.Rper i (D.J ρ (ε (φ m)) (Uj t) - Uj t) a b) := fun t m i a b =>
    (Work.Diff.STE.Lead.Rper_contDiff_and_periodic (I := I) (M := M) D _
      (Work.Diff.STE.Lead.ChartData_sub (I := I) (M := M) _ _
        (Work.Diff.STE.Lead.chartData_J_props (I := I) (M := M) D ρ hρ (ε (φ m)) (Uj t)
          (hUjCD t)) (hUjCD t)) i a b).1
  -- ###### STEP 12: `hcv`, the convergence of the coefficients of the velocities
  have hconvJ : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ k : ℕ,
      Filter.Tendsto (fun m : ℕ => D.BNorm k
        (D.J ρ (ε (φ m)) (galState D (ε (φ m)) (cf (φ m) t)) - Uj t))
        Filter.atTop (nhds 0) := by
    intro t ht k
    obtain ⟨C_k, _hC_k, hC_kb⟩ := hJN k
    -- step 1: `BNorm k (J (h - U)) → 0`
    have hstep1 : Filter.Tendsto (fun m : ℕ => D.BNorm k
        (D.J ρ (ε (φ m)) (galState D (ε (φ m)) (cf (φ m) t) - Uj t)))
        Filter.atTop (nhds 0) := by
      have hbnd : ∀ m : ℕ, D.BNorm k
          (D.J ρ (ε (φ m)) (galState D (ε (φ m)) (cf (φ m) t) - Uj t))
          ≤ C_k * D.BNorm k (galState D (ε (φ m)) (cf (φ m) t) - Uj t) := by
        intro m
        exact hC_kb (ε (φ m)) (hε (φ m))
          (galState D (ε (φ m)) (cf (φ m) t) - Uj t)
          (Work.Diff.STE.Lead.ChartData_sub (I := I) (M := M) _ _
            (hCDg (φ m) t) (hUjCD t))
      have hzero : Filter.Tendsto (fun m : ℕ =>
          D.BNorm k (galState D (ε (φ m)) (cf (φ m) t) - Uj t)) Filter.atTop (nhds 0) := by
        refine (hconvj t ht k).congr' ?_
        filter_upwards with m
        rw [← hcfu (φ m) t]
      exact squeeze_zero (fun m => D.BNorm_nonneg k _)
        (fun m => hbnd m) (by simpa using hzero.const_mul C_k)
    -- step 2: `J U - U → 0`
    have hstep2 : Filter.Tendsto (fun m : ℕ => D.BNorm k
        (D.J ρ (ε (φ m)) (Uj t) - Uj t)) Filter.atTop (nhds 0) :=
      (hJT k (Uj t) (hUjCD t)).comp (by
        rw [tendsto_nhdsWithin_iff]
        exact ⟨hε0.comp hφ.tendsto_atTop, Filter.Eventually.of_forall fun m => (hε (φ m)).1⟩)
    -- combine with the triangle inequality
    have hlim : Filter.Tendsto (fun m : ℕ =>
        2 * D.BNorm k (D.J ρ (ε (φ m)) (galState D (ε (φ m)) (cf (φ m) t) - Uj t))
        + 2 * D.BNorm k (D.J ρ (ε (φ m)) (Uj t) - Uj t)) Filter.atTop (nhds 0) := by
      have h1 : Filter.Tendsto (fun m : ℕ =>
          2 * D.BNorm k (D.J ρ (ε (φ m)) (galState D (ε (φ m)) (cf (φ m) t) - Uj t)))
          Filter.atTop (nhds 0) := by simpa using hstep1.const_mul 2
      have h2 : Filter.Tendsto (fun m : ℕ =>
          2 * D.BNorm k (D.J ρ (ε (φ m)) (Uj t) - Uj t)) Filter.atTop (nhds 0) := by
        simpa using hstep2.const_mul 2
      simpa using h1.add h2
    refine squeeze_zero (fun m => D.BNorm_nonneg k _) (fun m => ?_) hlim
    have heq : D.J ρ (ε (φ m)) (galState D (ε (φ m)) (cf (φ m) t)) - Uj t
        = (D.J ρ (ε (φ m)) (galState D (ε (φ m)) (cf (φ m) t) - Uj t))
          + (D.J ρ (ε (φ m)) (Uj t) - Uj t) := by
      rw [hJadd_loc (φ m) t (Uj t) (hUjCD t) (hUjsym t)]
      abel
    rw [heq]
    exact Work.Diff.STE.Lead.BNorm_add_le (I := I) (M := M) D k _ _ (hRper1 t m) (hRper2 t m)
  -- ###### the coefficient convergence, from `coeff_tendsto_galRHS`
  set Kc : ℝ := max (max (C_ub * Real.sqrt (B (Module.finrank ℝ E + 13))) K₀) 1 with hKcdef
  have hKcpos : 0 < Kc := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hcv : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ),
      Filter.Tendsto (fun m : ℕ => Work.Diff.STE.fourierCoeff (D.Rper i (vs (φ m) t) a b) μ)
        Filter.atTop (nhds (Work.Diff.STE.fourierCoeff (D.Rper i (W t) a b) μ)) := by
    intro t ht i a b μ
    have htI : t ∈ Set.Icc (0 : ℝ) τ₀ := ⟨ht.1, ht.2.le⟩
    have hA := Work.Diff.STE.Lead.coeff_tendsto_galRHS (I := I) (M := M) D ρ hρ hρ0 hLC hJN hJT
      τ₀ hτ₀ B hB lam Kc hlam hKcpos
      (fun m => ε (φ m)) (fun m => hε (φ m)) (hε0.comp hφ.tendsto_atTop)
      (fun m => D.J ρ (ε (φ m)) (galState D (ε (φ m)) (cf (φ m) t))) (Uj t)
      (fun m => hsmJ (φ m) t) (hUjCD t) (hconvJ t ht)
      (fun m x v => by rw [← hcfu (φ m) t]; exact huEll (φ m) t htI x v)
      (fun x v => by rw [hUjeq t ht]; exact hUp t ht x v)
      (fun m x v => by
        rw [← hcfu (φ m) t]
        exact le_trans (hC_ubb (ε (φ m)) (hε (φ m)) (u (φ m) t) (huCD (φ m) t)
          (B (Module.finrank ℝ E + 13)) (hB _) (huBnd (φ m) t htI _) x v)
          (mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _))
            (hg₀nn x v)))
      (fun x v => le_trans (hUjup t ht x v)
        (mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) (le_max_left _ _))
          (hg₀nn x v)))
      (fun m x u v => hsymJ (φ m) t x u v)
      (fun m x v hv => by rw [← hcfu (φ m) t]; exact huPos (φ m) t htI x v hv)
      (hUjsym t) (hUjpos t) i a b μ
    -- identify the left-hand side with `vs (φ m) t`
    refine hA.congr' (Filter.Eventually.of_forall fun m => ?_)
    simp only [hvseq (φ m) t htI]
  -- ###### STEP 13: the coefficient equation and the pointwise equation
  have hWCD : ∀ t : ℝ, Work.Diff.STE.D.ChartData (I := I) (M := M) (W t) := fun t =>
    Work.Diff.STE.B3.chartData_deTurckSec (I := I) (M := M) (g₀ := g₀) hLC (Uj t)
      (hUjsym t) (hUjpos t) (hUjCD t)
  have hWcont : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (z : Fin (Module.finrank ℝ E) → ℝ),
      ContinuousWithinAt (fun σ : ℝ => D.R i (W σ) a b z) (Set.Ico (0 : ℝ) τ₀) t := by
    intro t ht i a b z
    rw [hWdef]
    exact Work.Diff.STE.Lead.continuous_deTurckSec_R (I := I) (M := M) D hLC τ₀ B hB lam K₀ hlam
      hK₀pos Uj hUjCD hUjsym hUjpos hUjB
      (fun σ hσ x v => by rw [hUjeq σ hσ]; exact hUp σ hσ x v) hUjup hcontj i a b z t ht
  have hdecUj : ∀ M₀ : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ico (0 : ℝ) τ₀,
      ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)) (μ : Fin (Module.finrank ℝ E) → ℤ),
      ‖Work.Diff.STE.fourierCoeff (D.Rper i (Uj t) a b) μ‖ * (Work.Diff.STE.wt μ) ^ M₀ ≤ C := by
    intro M₀
    obtain ⟨C, hC0, hCb⟩ := hdecU M₀
    exact ⟨C, hC0, fun t ht i a b μ => by rw [hUjeq t ht]; exact hCb t ht i a b μ⟩
  have hcoeff : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E))
      (μ : Fin (Module.finrank ℝ E) → ℤ),
      HasDerivWithinAt (fun s : ℝ => Work.Diff.STE.fourierCoeff (D.Rper i (Uj s) a b) μ)
        (Work.Diff.STE.fourierCoeff (D.Rper i (W t) a b) μ) (Set.Ico (0 : ℝ) τ₀) t :=
    Work.Diff.STE.Lead.limit_coeff_hasDerivWithinAt (I := I) (M := M) D τ₀ hτ₀ φ u vs Uj W
      (fun m t => huCD m t) (fun t => hUjCD t) hode hvsb hvsmeas hconvj hcv hcontW
  have hpoint : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ (x : M) (u₀ v : TangentSpace I x),
      HasDerivWithinAt (fun s : ℝ => (Uj s) x u₀ v) ((W t) x u₀ v)
        (Set.Ico (0 : ℝ) τ₀) t :=
    Work.Diff.STE.Lead.pointwise_hasDerivWithinAt_of_coeff (I := I) (M := M) D τ₀ hτ₀ Uj W
      (fun t => hUjCD t) (fun t => hWCD t) hdecUj hWsum hcoeff hWcont
  -- ###### STEP 14: the initial value `U 0 = g₀.inner`
  have hgal0 : ∀ m : ℕ, galState D (ε m) (cf m 0) = g₀.inner := by
    intro m
    rw [(hcfsol m).1]
    have hz : Work.Diff.STE.D.genMap (I := I) (M := M) D (ε m)
        (0 : Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) (ε m) → ℝ) = 0 := by
      rw [Work.Diff.STE.D.genMap]
      apply Finset.sum_eq_zero
      intro z _
      ext x u v
      simp
    show Work.Diff.STE.D.addSec (I := I) g₀
      (Work.Diff.STE.D.genMap (I := I) (M := M) D (ε m) 0) = g₀.inner
    rw [hz]
    ext x u v
    simp [Work.Diff.STE.D.addSec]
  have hu0 : ∀ m : ℕ, u m 0 = g₀.inner := by
    intro m
    rw [hcfu m 0]
    exact hgal0 m
  have hU0 : U 0 = g₀.inner := by
    have h0 : (0 : ℝ) ∈ Set.Ico (0 : ℝ) τ₀ := ⟨le_refl 0, hτ₀⟩
    have hconst : ∀ k : ℕ, D.BNorm k (g₀.inner - U 0) = 0 := by
      intro k
      have h := hUconv 0 h0 k
      have hev : (fun m : ℕ => D.BNorm k (u (φ m) 0 - U 0))
          = (fun _ : ℕ => D.BNorm k (g₀.inner - U 0)) := by
        funext m
        rw [hu0 (φ m)]
      rw [hev] at h
      exact tendsto_nhds_unique tendsto_const_nhds h
    have hcd : Work.Diff.STE.D.ChartData (I := I) (M := M) (g₀.inner - U 0) :=
      Work.Diff.STE.Lead.ChartData_sub (I := I) (M := M) _ _ hg (hUC 0 h0)
    obtain ⟨C₀, _hC₀, hC₀b⟩ := pointwise_le_sqrt_BNorm_uniform (I := I) (M := M) D
      (Module.finrank ℝ E + 1) (by rw [Fintype.card_fin]; omega) ⟨d₀, hd₀pos, hd₀b⟩
    have hpt : ∀ (x : M) (u₀ v : TangentSpace I x), (g₀.inner - U 0) x u₀ v = 0 := by
      intro x u₀ v
      have hcdR : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          ContDiff ℝ (⊤ : ℕ∞) (D.Rper i (g₀.inner - U 0) a b) := fun i a b =>
        (Work.Diff.STE.Lead.Rper_contDiff_and_periodic (I := I) (M := M) D _ hcd i a b).1
      have hper : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
          Work.Diff.STE.Periodic1 (D.Rper i (g₀.inner - U 0) a b) := fun i a b =>
        (Work.Diff.STE.Lead.Rper_contDiff_and_periodic (I := I) (M := M) D _ hcd i a b).2
      have hb := hC₀b (g₀.inner - U 0) hcdR hper x u₀ v
      have hzero : D.BNorm (Module.finrank ℝ E + 1) (g₀.inner - U 0) = 0 := hconst _
      have hle : |(g₀.inner - U 0) x u₀ v| ≤ 0 := by
        refine le_trans hb ?_
        rw [hzero, Real.sqrt_zero]
        simp
      exact abs_eq_zero.mp (le_antisymm hle (abs_nonneg _))
    ext x u₀ v
    have h2 : g₀.inner x u₀ v - U 0 x u₀ v = 0 := by
      have h3 := hpt x u₀ v
      simpa using h3
    linarith [h2]
  -- ###### STEP 15: the joint smoothness of the section and of the DeTurck field
  have hUj0eq : Uj 0 = g₀.inner := by
    rw [hUjeq 0 ⟨le_refl 0, hτ₀⟩, hU0]
  have hsubIco : Set.Icc (0 : ℝ) (τ₀ / 2) ⊆ Set.Ico (0 : ℝ) τ₀ := fun t ht =>
    ⟨ht.1, lt_of_le_of_lt ht.2 (by linarith)⟩
  have hsubIcoIcc : Set.Ico (0 : ℝ) (τ₀ / 2) ⊆ Set.Ico (0 : ℝ) τ₀ := fun t ht =>
    ⟨ht.1, lt_trans ht.2 (by linarith)⟩
  have hJSl : Submission.Diff.JointSmooth
      (fun t : ℝ => Work.Diff.STE.D.smetOf (I := I) (Uj t) (hUjsym t) (hUjpos t) (hUjCD t))
      (Set.Ico (0 : ℝ) τ₀) :=
    Work.Diff.STE.Lead.jointSmooth_of_solves_deTurck (I := I) (M := M) D hLC hg τ₀ hτ₀ Uj B hB
      hUjsym hUjpos hUjCD hUjB hcontj
      (fun t ht x u₀ v => by
        simpa only [hWdef] using hpoint t ht x u₀ v)
  set G : ℝ → SMet I M :=
    fun t => Work.Diff.STE.D.smetOf (I := I) (Uj t) (hUjsym t) (hUjpos t) (hUjCD t) with hGdef
  have hJS : JointSmooth G (Set.Icc 0 (τ₀ / 2)) := by
    rw [hGdef]
    exact ContMDiffOn.mono hJSl (Set.prod_mono hsubIco (Subset.refl _))
  have hJF0 : Work.Diff.EXT.JointField
      (fun t => Work.Diff.STE.DeTurck.deTurckVec
        (Work.Diff.STE.D.smetOf (I := I) (Uj t) (hUjsym t) (hUjpos t) (hUjCD t)) g₀)
      (Set.prod (Set.Ico (0 : ℝ) τ₀) (Set.univ : Set M)) :=
    Work.Diff.STE.Lead.deTurckVec_jointField_within (I := I) (M := M) hLC
      (fun t => Work.Diff.STE.D.smetOf (I := I) (Uj t) (hUjsym t) (hUjpos t) (hUjCD t)) g₀ τ₀
      (by
        refine (Work.Diff.EXT.jointMet_prod (I := I) (M := M)
          (fun t : ℝ => Work.Diff.STE.D.smetOf (I := I) (Uj t) (hUjsym t) (hUjpos t) (hUjCD t))
          (Set.Ico (0 : ℝ) τ₀)).mpr ?_
        exact hJSl)
  have hJF : ContMDiffOn (𝓘(ℝ, ℝ).prod I) I.tangent ∞
      (fun p : ℝ × M =>
        (⟨p.2, Work.Diff.STE.DeTurck.deTurckVec (G p.1) g₀ p.2⟩ : TangentBundle I M))
      (Set.Icc 0 (τ₀ / 2) ×ˢ (univ : Set M)) := by
    rw [hGdef]
    exact hJF0.mono (fun p hp => ⟨hsubIco hp.1, hp.2⟩)
  -- ###### assembly
  refine ⟨τ₀ / 2, by positivity, G, ?_, hJS, hJF, ?_⟩
  · rw [hGdef]
    show Work.Diff.STE.D.smetOf (I := I) (Uj 0) (hUjsym 0) (hUjpos 0) (hUjCD 0) = g₀
    exact smetOf_congr_of_eq (I := I) (M := M) hUj0eq (hUjsym 0) (hUjpos 0) (hUjCD 0)
      g₀.symm g₀.pos hg
  · intro t ht x u₀ v
    rw [hGdef]
    simpa only [hWdef, Work.Diff.STE.D.deTurckSec_apply, Work.Diff.STE.D.smetOf_inner,
      Work.Diff.STE.DeTurck.deTurckOp_apply, Work.Diff.STE.DeTurck.lieMet, add_assoc]
      using (hpoint t (hsubIcoIcc ht) x u₀ v).mono hsubIcoIcc



end Work.Diff.STE.Lead
