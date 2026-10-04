import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.Lead.Gal.lowJetBoundGal
import Submission.Work.Diff.STE.Lead.Gal.nresSmooth
import Submission.Work.Diff.STE.B3.LowJetAux
import Submission.Work.Diff.STE.B3.tmNom_aux
import Submission.Work.Diff.STE.B3.CompSmooth
import Submission.Work.Diff.STE.B3.densGood
import Submission.Work.Diff.STE.B3.BPairDefs
import Submission.Work.Diff.STE.B3.Pointwise
import Submission.Work.Diff.STE.Lead.Gal.gardLeibnizLocal
import Submission.Work.Diff.STE.Lead.Gal.gardJet_holds
import Submission.Work.Diff.STE.flat.compact_iteratedFDeriv_bound
import Submission.Work.Diff.STE.flat.det_ne_zero_of_quadForm_le
import Submission.Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv
import Submission.Work.Diff.STE.CSq_periodization_le_of_sup_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The residual data `Ψ`: a smooth, compactly supported representative of the transport residual

The Galerkin scheme of Layer D needs the lower-order residual of the transport identity
(`Work.Diff.STE.B3.residualLow`, represented by the *nominal* residual
`Work.Diff.STE.B3.nres` applied to the orthonormal-frame chart matrix `Mf` and its first jet) in the
form of a **globally smooth, compactly supported** function of the flat coordinate whose jets of
order `≤ k` are bounded by a constant *uniform in the admissible section* `h`, and which agrees with
the residual on the closed `2σ j`-ball.

The construction is

`Ψ a b z = nres D j z (Mf D h j z) (∂Mf D h j z) a b · ρ j z`,

where `ρ j` is a smooth bump which is `1` on the closed `σ j`-ball and whose support lies in the open
`(3/2)σ j`-ball.  The three facts that make this work are

* **the nominal residual vanishes on the closed exterior of the `σ j`-ball**
  (`nres_eq_zero_of_sigma_le`): every term of its body carries the weight
  `wf = ψ_j √dens_j = χ_j · (ζ_j ∘ pt_j) · √dens_j` or one of its first two partial derivatives, and
  these vanish for `‖z‖ ≥ σ j` (`ψ` vanishes by `norm_lt_sigma_of_psi_ne_zero`, and its derivatives
  vanish at the sphere `‖z‖ = σ j` because `wf` is smooth there and vanishes identically on the open
  exterior);
* **the identification of the residual with the nominal residual on the `2σ j`-ball**
  (`Work.Diff.STE.B3.pdVec_residualLow_eq_nres`, proved with the transport identity);
* **the uniform jet bound for the residual**
  (`Work.Diff.STE.Lead.Gal.transport_low_jet_bound_uniform`), which is the composition estimate
  `compJetBoundLoc` applied to the smoothness of `nres` in the state variable
  (`Work.Diff.STE.Lead.Gal.nresSmooth`), and
* **the smoothness of the composite** `z ↦ nres D j z (Mf z) (∂Mf z) a b` on the open
  `2σ j`-ball, which combines `nresC_contDiffOn` with the smoothness `Mf_contDiffOn_gal` of the
  chart matrix.

The jet bound of the *product* with the bump is then the local Leibniz estimate
`Work.Diff.STE.Lead.Gal.gardLeibnizLocal`.
-/

namespace Work.Diff.STE.Lead.Gal

open Filter
open scoped Topology

/-- The index type of all component computations. -/
abbrev IdxT (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] : Type _ :=
  Fin (Module.finrank ℝ E)

section Aux

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

local notation "Idx" => Fin (Module.finrank ℝ E)

/-! ## 1. Vanishing on the sphere from vanishing on the open exterior -/

/-- **A function continuous at `z`, vanishing on the open exterior of the ball of radius `σ`,
vanishes at `z` as soon as `‖z‖ ≥ σ`.**  If `‖z‖ > σ` this is the hypothesis; at the sphere
`‖z‖ = σ` one lets a point of the exterior tend to `z` (the exterior accumulates at `z` because
`z ≠ 0`). -/
lemma eq_zero_of_continuousAt_of_sigma_le {σ : ℝ} (hσ : 0 < σ)
    {f : (Fin (Module.finrank ℝ E) → ℝ) → ℝ}
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : σ ≤ ‖z‖)
    (hzero : ∀ y : Fin (Module.finrank ℝ E) → ℝ, σ < ‖y‖ → f y = 0)
    (hf : ContinuousAt f z) : f z = 0 := by
  by_cases hlt : σ < ‖z‖
  · exact hzero z hlt
  · have hzeq : ‖z‖ = σ := le_antisymm (not_lt.mp hlt) hz
    have hzpos : 0 < ‖z‖ := by rw [hzeq]; exact hσ
    -- the open exterior accumulates at `z`
    have hcl : z ∈ closure {y : Fin (Module.finrank ℝ E) → ℝ | σ < ‖y‖} := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      have hden : (0 : ℝ) < 2 * ‖z‖ + 1 := by positivity
      have hpos : 0 < ε / (2 * ‖z‖ + 1) := div_pos hε hden
      have hfac : (1 : ℝ) < 1 + ε / (2 * ‖z‖ + 1) := by linarith
      have hfac0 : (0 : ℝ) < 1 + ε / (2 * ‖z‖ + 1) := by linarith
      refine ⟨(1 + ε / (2 * ‖z‖ + 1)) • z, ?_, ?_⟩
      · show σ < ‖(1 + ε / (2 * ‖z‖ + 1)) • z‖
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos hfac0]
        calc σ = 1 * ‖z‖ := by rw [one_mul]; exact hzeq.symm
          _ < (1 + ε / (2 * ‖z‖ + 1)) * ‖z‖ := mul_lt_mul_of_pos_right hfac hzpos
      · rw [dist_comm, dist_eq_norm]
        have hsub : (1 + ε / (2 * ‖z‖ + 1)) • z - z = (ε / (2 * ‖z‖ + 1)) • z := by
          rw [add_smul, one_smul, add_sub_cancel_left]
        rw [hsub, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
        calc ε / (2 * ‖z‖ + 1) * ‖z‖ < ε / (2 * ‖z‖ + 1) * (2 * ‖z‖ + 1) :=
              mul_lt_mul_of_pos_left (by linarith) hpos
          _ = ε := by field_simp
    haveI hne : (𝓝[{y : Fin (Module.finrank ℝ E) → ℝ | σ < ‖y‖}] z).NeBot :=
      mem_closure_iff_nhdsWithin_neBot.mp hcl
    have h1 : Tendsto f (𝓝[{y : Fin (Module.finrank ℝ E) → ℝ | σ < ‖y‖}] z) (𝓝 (f z)) :=
      hf.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto f (𝓝[{y : Fin (Module.finrank ℝ E) → ℝ | σ < ‖y‖}] z) (𝓝 0) := by
      have hev : f =ᶠ[𝓝[{y : Fin (Module.finrank ℝ E) → ℝ | σ < ‖y‖}] z] fun _ => (0 : ℝ) := by
        filter_upwards [self_mem_nhdsWithin] with y hy
        exact hzero y hy
      exact tendsto_const_nhds.congr' hev.symm
    exact tendsto_nhds_unique h1 h2

/-- The topological support of the complexification of a real-valued function. -/
lemma tsupport_ofReal_eq (f : (Idx → ℝ) → ℝ) :
    tsupport (fun z => ((f z : ℝ) : ℂ)) = tsupport f := by
  simp only [tsupport, Function.support, ne_eq, Complex.ofReal_eq_zero]

/-! ## 2. The weight is smooth on the chart target, and its derivatives vanish on the closed
exterior of the `σ j`-ball -/

/-! ## 2. The localised weight vanishes on the closed exterior of the `σ j`-ball -/

/-- The localised weight `ψ_j = χ_j · (ζ_j ∘ pt_j)` vanishes outside the open `σ j`-ball. -/
lemma psi_eq_zero_of_sigma_le_gal (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Idx → ℝ} (hz : D.σ j ≤ ‖z‖) : D.psi j z = 0 := by
  by_contra h
  exact absurd (Work.Diff.STE.B3.norm_lt_sigma_of_psi_ne_zero (D := D) h) (not_lt.mpr hz)

/-- The weight `wf = ψ_j √dens_j` vanishes on the closed exterior of the `σ j`-ball. -/
lemma wf_eq_zero_of_sigma_le_gal (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Idx → ℝ} (hz : D.σ j ≤ ‖z‖) :
    Work.Diff.STE.B3.wf (I := I) (M := M) D j z = 0 := by
  simp only [Work.Diff.STE.B3.wf, psi_eq_zero_of_sigma_le_gal (I := I) (M := M) D j hz, zero_mul]

/-- The weight vanishes on a neighbourhood of a point of the open exterior of the `σ j`-ball. -/
lemma wf_eventuallyEq_zero_gal (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Idx → ℝ} (hz : D.σ j < ‖z‖) :
    Work.Diff.STE.B3.wf (I := I) (M := M) D j =ᶠ[𝓝 z] 0 := by
  have hU : {y : Idx → ℝ | D.σ j < ‖y‖} ∈ 𝓝 z :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hz
  filter_upwards [hU] with y hy
  exact wf_eq_zero_of_sigma_le_gal (I := I) (M := M) D j (le_of_lt hy)

/-- The first partial derivatives of the weight vanish on the open exterior of the `σ j`-ball. -/
lemma pdR_wf_eq_zero_gal (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Idx → ℝ} (hz : D.σ j < ‖z‖) (p : Idx) :
    Work.Diff.STE.pdR p (Work.Diff.STE.B3.wf (I := I) (M := M) D j) z = 0 := by
  rw [Work.Diff.STE.pdR, (wf_eventuallyEq_zero_gal (I := I) (M := M) D j hz).fderiv_eq]
  simp

/-- The first partial derivatives of the weight vanish on a neighbourhood of a point of the open
exterior. -/
lemma pdR_wf_eventuallyEq_zero_gal (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Idx → ℝ} (hz : D.σ j < ‖z‖) (p : Idx) :
    Work.Diff.STE.pdR p (Work.Diff.STE.B3.wf (I := I) (M := M) D j) =ᶠ[𝓝 z] 0 := by
  have hU : {y : Idx → ℝ | D.σ j < ‖y‖} ∈ 𝓝 z :=
    (isOpen_lt continuous_const continuous_norm).mem_nhds hz
  filter_upwards [hU] with y hy
  exact pdR_wf_eq_zero_gal (I := I) (M := M) D j hy p

/-- The second partial derivatives of the weight vanish on the open exterior of the `σ j`-ball. -/
lemma pdR2_wf_eq_zero_gal (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Idx → ℝ} (hz : D.σ j < ‖z‖) (p q : Idx) :
    Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (Work.Diff.STE.B3.wf (I := I) (M := M) D j)) z = 0 := by
  rw [Work.Diff.STE.pdR, (pdR_wf_eventuallyEq_zero_gal (I := I) (M := M) D j hz q).fderiv_eq]
  simp

/-- **The residual vanishes pointwise on the open exterior of the `σ j`-ball**: every term of
`residualLow` carries the weight `wf = ψ_j √dens_j` or one of its first two partial derivatives. -/
lemma residualLow_eq_zero_of_sigma_lt_gal (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    {z : Idx → ℝ} (hz : D.σ j < ‖z‖) (a b : Idx) :
    Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b = 0 := by
  simp only [Work.Diff.STE.B3.residualLow,
    wf_eq_zero_of_sigma_le_gal (I := I) (M := M) D j (le_of_lt hz),
    pdR_wf_eq_zero_gal (I := I) (M := M) D j hz,
    pdR2_wf_eq_zero_gal (I := I) (M := M) D j hz,
    zero_mul, mul_zero, Finset.sum_const_zero, sub_zero, add_zero]

/-- The weight `wf = ψ_j · √dens_j` is `C^∞` at every point whose flat coordinate lies in the chart
target: `ψ_j` is globally smooth (`B3Data.psi_contDiff`) and `√dens_j` is smooth on the target
(`B3Data.sqrt_dens_contDiffAt`). -/
lemma wf_contDiffAt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ}
    (hz : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target) :
    ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (Work.Diff.STE.B3.wf (I := I) (M := M) D j) z := by
  have hpsi : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) (D.psi j) z :=
    (D.psi_contDiff j).contDiffAt
  have hdens : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (fun z => Real.sqrt (D.dens j z)) z :=
    D.sqrt_dens_contDiffAt j (Work.Diff.STE.B3.densGood (I := I) (M := M) D j) hz
  change ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
    (fun z => D.psi j z * Real.sqrt (D.dens j z)) z
  exact hpsi.mul hdens

/-- The first partial derivatives of the weight vanish on the closed exterior of the `σ j`-ball. -/
lemma pdR_wf_eq_zero_of_sigma_le (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : D.σ j ≤ ‖z‖) (p : Idx) :
    Work.Diff.STE.pdR p (Work.Diff.STE.B3.wf (I := I) (M := M) D j) z = 0 := by
  by_cases hlt : D.σ j < ‖z‖
  · exact pdR_wf_eq_zero_gal (I := I) (M := M) D j hlt p
  · have hσ := D.hσ j
    have htarget : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target :=
      D.htarget j z (by
        have hzeq : ‖z‖ = D.σ j := le_antisymm (not_lt.mp hlt) hz
        rw [hzeq]
        linarith)
    refine eq_zero_of_continuousAt_of_sigma_le (f := fun y => Work.Diff.STE.pdR p
      (Work.Diff.STE.B3.wf (I := I) (M := M) D j) y) hσ hz
      (fun y hy => pdR_wf_eq_zero_gal (I := I) (M := M) D j hy p) ?_
    have h1 : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fderiv ℝ (Work.Diff.STE.B3.wf (I := I) (M := M) D j)) z :=
      (wf_contDiffAt (I := I) (M := M) D j htarget).fderiv_right (by simp)
    have h2 := h1.clm_apply (contDiffAt_const (c := (Pi.single p (1 : ℝ) : Idx → ℝ)))
    change ContinuousAt (fun y => (fderiv ℝ (Work.Diff.STE.B3.wf (I := I) (M := M) D j) y)
      (Pi.single p (1 : ℝ))) z
    exact h2.continuousAt

/-- The second partial derivatives of the weight vanish on the closed exterior of the `σ j`-ball. -/
lemma pdR2_wf_eq_zero_of_sigma_le (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : D.σ j ≤ ‖z‖) (p q : Idx) :
    Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (Work.Diff.STE.B3.wf (I := I) (M := M) D j)) z = 0 := by
  by_cases hlt : D.σ j < ‖z‖
  · exact pdR2_wf_eq_zero_gal (I := I) (M := M) D j hlt p q
  · have hσ := D.hσ j
    have htarget : Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target :=
      D.htarget j z (by
        have hzeq : ‖z‖ = D.σ j := le_antisymm (not_lt.mp hlt) hz
        rw [hzeq]
        linarith)
    refine eq_zero_of_continuousAt_of_sigma_le (f := fun y => Work.Diff.STE.pdR p
      (Work.Diff.STE.pdR q (Work.Diff.STE.B3.wf (I := I) (M := M) D j)) y) hσ hz
      (fun y hy => pdR2_wf_eq_zero_gal (I := I) (M := M) D j hy p q) ?_
    have h0 : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (Work.Diff.STE.pdR q (Work.Diff.STE.B3.wf (I := I) (M := M) D j)) z := by
      have h2 : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
          (fderiv ℝ (Work.Diff.STE.B3.wf (I := I) (M := M) D j)) z :=
        (wf_contDiffAt (I := I) (M := M) D j htarget).fderiv_right (by simp)
      have h3 := h2.clm_apply (contDiffAt_const (c := (Pi.single q (1 : ℝ) : Idx → ℝ)))
      change ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fun y => (fderiv ℝ (Work.Diff.STE.B3.wf (I := I) (M := M) D j) y)
          (Pi.single q (1 : ℝ))) z
      exact h3
    have h1 : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fderiv ℝ (Work.Diff.STE.pdR q (Work.Diff.STE.B3.wf (I := I) (M := M) D j))) z :=
      h0.fderiv_right (by simp)
    have h4 := h1.clm_apply (contDiffAt_const (c := (Pi.single p (1 : ℝ) : Idx → ℝ)))
    change ContinuousAt (fun y => (fderiv ℝ (Work.Diff.STE.pdR q
      (Work.Diff.STE.B3.wf (I := I) (M := M) D j)) y) (Pi.single p (1 : ℝ))) z
    exact h4.continuousAt

set_option maxHeartbeats 1000000 in
/-- **The nominal residual vanishes on the closed exterior of the `σ j`-ball**: every term of its
body carries the weight or one of its first two partial derivatives. -/
lemma nres_eq_zero_of_sigma_le (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : D.σ j ≤ ‖z‖)
    (V : Idx → Idx → ℝ) (dV : Idx → Idx → Idx → ℝ) (a b : Idx) :
    Work.Diff.STE.B3.nres (I := I) (M := M) D j z V dV a b = 0 := by
  have h1 : Work.Diff.STE.B3.wf (I := I) (M := M) D j z = 0 :=
    wf_eq_zero_of_sigma_le_gal (I := I) (M := M) D j hz
  have h2 : ∀ p : Idx, Work.Diff.STE.pdR p (Work.Diff.STE.B3.wf (I := I) (M := M) D j) z = 0 :=
    fun p => pdR_wf_eq_zero_of_sigma_le (I := I) (M := M) D j hz p
  have h3 : ∀ p q : Idx,
      Work.Diff.STE.pdR p (Work.Diff.STE.pdR q (Work.Diff.STE.B3.wf (I := I) (M := M) D j)) z
        = 0 :=
    fun p q => pdR2_wf_eq_zero_of_sigma_le (I := I) (M := M) D j hz p q
  simp only [Work.Diff.STE.B3.nres, Work.Diff.STE.B3.body, h1, h2, h3, zero_mul, mul_zero,
    Finset.sum_const_zero, sub_zero, add_zero]

/-! ## 3. Smoothness of the composite `z ↦ nres D j z (Mf z) (∂Mf z) a b` -/

/-- **Ellipticity of the orthonormal-frame chart matrix** in the `ℓ²` form: in a `g₀`-orthonormal
frame the quadratic form of the chart matrix of `h` is the diagonal value `h(e_ξ, e_ξ)` at the
vector `e_ξ = Σ ξ_a e_a`, whose `g₀`-length squared is `Σ ξ_a²`. -/
lemma Mf_elliptic_gal (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u) (lam : ℝ)
    (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
    (j : ι₀) {z : Idx → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j) (ξ : Idx → ℝ) :
    lam * ∑ a, (ξ a) ^ 2 ≤ ∑ a, ∑ b,
      Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z a b * ξ a * ξ b := by
  have hON : Submission.Diff.IsONFrame g₀ (D.pt j z) (fun a => D.e j a (D.pt j z)) :=
    D.heON j z hz
  set v : TangentSpace I (D.pt j z) := ∑ a, ξ a • D.e j a (D.pt j z) with hv
  have hexp : ∑ a, ∑ b, Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z a b * ξ a * ξ b
      = h (D.pt j z) v v := by
    rw [hv]
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply,
      smul_eq_mul, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => ?_))
    simp only [Work.Diff.STE.B3.Mf, Work.Diff.STE.B3Data.mat]
    rw [hsym (D.pt j z) (D.e j b (D.pt j z)) (D.e j a (D.pt j z))]
    ring
  have hcoef : ∀ a : Idx,
      g₀.inner (D.pt j z) v (D.e j a (D.pt j z)) = ξ a := by
    intro a
    rw [hv]
    simp only [map_sum, ContinuousLinearMap.sum_apply, map_smul, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    rw [Finset.sum_eq_single a]
    · rw [hON a a, if_pos rfl, mul_one]
    · intro b _ hb
      rw [hON b a, if_neg hb, mul_zero]
    · intro ha
      exact absurd (Finset.mem_univ a) ha
  have hinner : g₀.inner (D.pt j z) v v = ∑ a, (ξ a) ^ 2 := by
    rw [← D.sum_inner_sq j hON v]
    exact Finset.sum_congr rfl (fun a _ => by rw [hcoef a])
  rw [hexp, ← hinner]
  exact hell (D.pt j z) v

/-- The orthonormal-frame chart matrix of an admissible section is nonsingular: its quadratic form
dominates `lam * ‖·‖²` with `lam > 0`. -/
lemma det_Mf_ne_zero (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
    (j : ι₀) {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j) (a b : Idx) :
    (Matrix.of (Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z)).det ≠ 0 := by
  have hquad : ∀ ξ : Idx → ℝ,
      lam * ∑ i, (ξ i) ^ 2 ≤ ∑ i, ∑ k, (Matrix.of (Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z))
        i k * ξ i * ξ k := by
    intro ξ
    simpa only [Matrix.of_apply] using Mf_elliptic_gal (I := I) (M := M) D h hsym lam hell j hz ξ
  exact Work.Diff.STE.flat.det_ne_zero_of_quadForm_le _ hlam hquad

/-- **Smoothness of the orthonormal-frame chart matrix on the open `2σ j`-ball.** -/
lemma Mf_contDiffOn_gal (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀) (a b : Idx) :
    ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat)
      (fun z : Idx → ℝ => Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z a b)
      {z : Idx → ℝ | ‖z‖ < 2 * D.σ j} := by
  have hsm : ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) (D.matChart j h a b)
      (extChartAt I (D.x₀ j)).target :=
    Work.Diff.STE.Lead.Gal.matChart_contDiffOn_chartData (I := I) (M := M) D h hsmooth j a b
  have hmap : Set.MapsTo (Work.Diff.STE.flatToE (I := I) (D.x₀ j))
      {z : Idx → ℝ | ‖z‖ < 2 * D.σ j} (extChartAt I (D.x₀ j)).target :=
    fun z hz => D.htarget j z (le_of_lt hz)
  have hcomp := hsm.comp
    (Work.Diff.STE.contDiff_flatToE (I := I) (x₀ := D.x₀ j)).contDiffOn hmap
  refine hcomp.congr (fun z _ => ?_)
  rfl

/-- **The jets of the residual are the jets of the nominal residual along the chart matrix**: on the
closed `2σ j`-ball the residual is the nominal residual evaluated at the orthonormal-frame chart
matrix and its first jet, so their iterated partial derivatives agree. -/
lemma pdVec_residualLow_eq_nres_gal (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    {z : Idx → ℝ} (hz : ‖z‖ ≤ 2 * D.σ j)
    (m : ℕ) (β : Fin m → Idx) (a b : Idx) :
    Work.Diff.STE.pdVec m β (fun y : Idx → ℝ =>
        ((Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j y a b : ℝ) : ℂ)) z
      = Work.Diff.STE.pdVec m β (fun y : Idx → ℝ =>
          ((Work.Diff.STE.B3.nres (I := I) (M := M) D j y
            (Work.Diff.STE.B3.Mf (I := I) (M := M) D h j y)
            (fun c i j' : Idx => Work.Diff.STE.pdR c (fun w : Idx → ℝ =>
              Work.Diff.STE.B3.Mf (I := I) (M := M) D h j w i j') y) a b : ℝ) : ℂ)) z := by
  refine Work.Diff.STE.csqp_pdVec_congr β ?_
  filter_upwards [Work.Diff.STE.B3.tmNom_eventually_mem_target (D := D) j (D.htarget j z hz),
    Work.Diff.STE.B3.tmNom_eventually_det_Ff_ne_zero (D := D) j hz] with y hy hdy
  rw [Work.Diff.STE.B3.residualLow_eq_nres_of_target (I := I) (M := M) D h hsmooth j hy hdy a b]
  rfl

/-- The iterated partial derivatives of a function vanishing on a neighbourhood of a point vanish. -/
lemma pdVec_eq_zero_of_eventuallyEq_zero_gal {n : ℕ} {f : (Fin n → ℝ) → ℂ} {y : Fin n → ℝ}
    (hy : f =ᶠ[𝓝 y] (fun _ => 0)) (m : ℕ) (β : Fin m → Fin n) :
    Work.Diff.STE.pdVec m β f y = 0 := by
  rw [Work.Diff.STE.csqp_pdVec_congr (l := β) hy]
  exact congrFun (Work.Diff.STE.Lead.Gal.pdVec_zero_fun m β) y

/-- **The state map `z ↦ (z, Mf z, ∂Mf z)` is smooth at every point of the open `2σ j`-ball.** -/
lemma state_contDiffAt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h) (j : ι₀)
    {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ < 2 * D.σ j) :
    ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        (y, Work.Diff.STE.B3.Mf (I := I) (M := M) D h j y,
          fun c a b => Work.Diff.STE.pdR c (fun w : Fin (Module.finrank ℝ E) → ℝ =>
            Work.Diff.STE.B3.Mf (I := I) (M := M) D h j w a b) y)) z := by
  have hball : {z' : Idx → ℝ | ‖z'‖ < 2 * D.σ j} ∈ 𝓝 z :=
    (isOpen_lt continuous_norm continuous_const).mem_nhds hz
  have hMf : ∀ a b : Idx, ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (fun y => Work.Diff.STE.B3.Mf (I := I) (M := M) D h j y a b) z :=
    fun a b => (Mf_contDiffOn_gal (I := I) (M := M) D h hsmooth j a b).contDiffAt hball
  have hdMf : ∀ c a b : Idx, ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (fun y => Work.Diff.STE.pdR c (fun w : Fin (Module.finrank ℝ E) → ℝ =>
        Work.Diff.STE.B3.Mf (I := I) (M := M) D h j w a b) y) z := by
    intro c a b
    have h1 : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
        (fderiv ℝ (fun y => Work.Diff.STE.B3.Mf (I := I) (M := M) D h j y a b)) z :=
      (hMf a b).fderiv_right (by simp)
    have h2 := h1.clm_apply (contDiffAt_const (c := (Pi.single c (1 : ℝ) : Idx → ℝ)))
    simpa only [Work.Diff.STE.pdR] using h2
  have h1 : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (fun y : Fin (Module.finrank ℝ E) → ℝ => y) z := contDiffAt_id
  have h2 : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (fun y => Work.Diff.STE.B3.Mf (I := I) (M := M) D h j y) z :=
    contDiffAt_pi.mpr (fun a => contDiffAt_pi.mpr (fun b => hMf a b))
  have h3 : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (fun y => fun c a b => Work.Diff.STE.pdR c (fun w : Fin (Module.finrank ℝ E) → ℝ =>
        Work.Diff.STE.B3.Mf (I := I) (M := M) D h j w a b) y) z :=
    contDiffAt_pi.mpr (fun c => contDiffAt_pi.mpr (fun a => contDiffAt_pi.mpr (fun b =>
      hdMf c a b)))
  exact h1.prodMk (h2.prodMk h3)

/-- **The composite `z ↦ nres D j z (Mf z) (∂Mf z) a b` is smooth at every point of the open
`2σ j`-ball**, being the nominal residual (which is smooth on its state domain) composed with the
smooth state map. -/
lemma nresComp_contDiffAt (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M))
    (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
    (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
    {lam : ℝ} (hlam : 0 < lam)
    (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
    (j : ι₀) (a b : Idx) {z : Fin (Module.finrank ℝ E) → ℝ} (hz : ‖z‖ < 2 * D.σ j) :
    ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (fun y : Fin (Module.finrank ℝ E) → ℝ => ((Work.Diff.STE.B3.nres (I := I) (M := M) D j y
        (Work.Diff.STE.B3.Mf (I := I) (M := M) D h j y)
        (Work.Diff.STE.B3.dMf (I := I) (M := M) D h j y) a b : ℝ) : ℂ)) z := by
  have hσ := D.hσ j
  have hmem : (z, Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z,
      Work.Diff.STE.B3.dMf (I := I) (M := M) D h j z) ∈
      {q : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
        ‖q.1‖ < 2 * D.σ j ∧ (Matrix.of q.2.1).det ≠ 0} :=
    ⟨hz, det_Mf_ne_zero (I := I) (M := M) D h hsym hlam hell j (le_of_lt hz) a b⟩
  have hcontdet : Continuous (fun q : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) =>
      (Matrix.of q.2.1).det) := by
    fun_prop
  have hopen : IsOpen {q : (Idx → ℝ) × (Idx → Idx → ℝ) × (Idx → Idx → Idx → ℝ) |
      ‖q.1‖ < 2 * D.σ j ∧ (Matrix.of q.2.1).det ≠ 0} := by
    refine IsOpen.inter ?_ ?_
    · exact (isOpen_lt continuous_fst.norm continuous_const).preimage continuous_id
    · exact (isOpen_ne).preimage hcontdet
  have hΦ : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat)
      (Work.Diff.STE.B3.nresC (I := I) (M := M) D j a b)
      (z, Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z,
        Work.Diff.STE.B3.dMf (I := I) (M := M) D h j z) :=
    ((Work.Diff.STE.Lead.Gal.nresSmooth (I := I) (M := M) D j a b).mono (fun q hq =>
        ⟨D.htarget j q.1 (le_of_lt hq.1), Work.Diff.STE.B3.det_Ff_ne_zero (I := I) (M := M) D j (le_of_lt hq.1),
          hq.2⟩)).contDiffAt (hopen.mem_nhds hmem)
  have hstate := state_contDiffAt (I := I) (M := M) D h hsmooth j hz
  have hcomp := hΦ.comp z hstate
  refine hcomp.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq ?_)
  funext y
  rfl

theorem residualDataPsi
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) :
    ∀ (lam K : ℝ), 0 < lam → 0 < K →
      ∃ CR : ℝ, 0 ≤ CR ∧
        ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
          (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
          (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
          (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
          (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
          (hjet : ∀ (i : ι₀) (m : ℕ) (hm : m ≤ k + 1)
            (β : Fin m → Fin (Module.finrank ℝ E))
            (z : Fin (Module.finrank ℝ E) → ℝ) (c d : Fin (Module.finrank ℝ E)),
            ‖z‖ ≤ 2 * D.σ i →
            ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K),
          ∀ (j : ι₀),
            ∃ Ψ : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
                (Fin (Module.finrank ℝ E) → ℝ) → ℂ,
              (∀ a b, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (Ψ a b)) ∧
              (∀ a b, Function.support (Ψ a b) ⊆
                Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (D.σ j)) ∧
              (∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin (Module.finrank ℝ E))
                (z : Fin (Module.finrank ℝ E) → ℝ) (a b : Fin (Module.finrank ℝ E)),
                ‖Work.Diff.STE.pdVec m β (Ψ a b) z‖ ≤ CR) ∧
              (∀ (a b : Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
                ‖z‖ ≤ 2 * D.σ j →
                Ψ a b z
                  = ((Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b : ℝ) : ℂ))
    := by
  intro lam K hlam hK
  -- the uniform jet bound for the residual (the composition estimate)
  obtain ⟨Cjet, hCjet0, hCjet⟩ :=
    Work.Diff.STE.Lead.Gal.transport_low_jet_bound_uniform (I := I) (M := M) D k lam K hlam hK
  -- the localising bump and its jet bound, per chart
  have hbump : ∀ j : ι₀, ∃ (ρ : (IdxT E → ℝ) → ℝ) (B : ℝ), 0 ≤ B ∧
      ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun z => ((ρ z : ℝ) : ℂ)) ∧
      (∀ z : IdxT E → ℝ, ‖z‖ ≤ D.σ j → ρ z = 1) ∧
      tsupport ρ ⊆ Metric.closedBall (0 : IdxT E → ℝ) ((3 / 2) * D.σ j) ∧
      (∀ (m : ℕ), m ≤ k → ∀ (β : Fin m → IdxT E) (z : IdxT E → ℝ),
        ‖Work.Diff.STE.pdVec m β (fun y => ((ρ y : ℝ) : ℂ)) z‖ ≤ B) := by
    intro j
    have hσ := D.hσ j
    let ρ : ContDiffBump (0 : IdxT E → ℝ) := ⟨D.σ j, (3 / 2) * D.σ j, hσ, by linarith⟩
    have hsm : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (fun z : IdxT E → ℝ => ((ρ z : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp ρ.contDiff
    obtain ⟨B, hB0, hB⟩ := Work.Diff.STE.flat.compact_iteratedFDeriv_bound
      (fun z : IdxT E → ℝ => ((ρ z : ℝ) : ℂ)) isOpen_univ hsm.contDiffOn
      (isCompact_closedBall (0 : IdxT E → ℝ) ((3 / 2) * D.σ j)) (Set.subset_univ _) k
    refine ⟨ρ, B, hB0, hsm, ?_, ?_, ?_⟩
    · intro z hz
      exact ρ.one_of_mem_closedBall (by rwa [Metric.mem_closedBall, dist_zero_right])
    · rw [ρ.tsupport_eq]
    · intro m hm β z
      by_cases hzt : z ∈ tsupport (fun y : IdxT E → ℝ => ((ρ y : ℝ) : ℂ))
      · have hzle : ‖z‖ ≤ (3 / 2) * D.σ j := by
          have h2 : z ∈ tsupport (ρ : (IdxT E → ℝ) → ℝ) := by
            rwa [tsupport_ofReal_eq ρ] at hzt
          have h3 : z ∈ Metric.closedBall (0 : IdxT E → ℝ) ((3 / 2) * D.σ j) := by
            rwa [ρ.tsupport_eq] at h2
          rwa [Metric.mem_closedBall, dist_zero_right] at h3
        rw [Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv m _ hsm z β]
        refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
        have hprod : ∏ t : Fin m, ‖(Pi.single (β t) (1 : ℝ) : IdxT E → ℝ)‖ = 1 := by
          simp [Pi.norm_single]
        rw [hprod, mul_one]
        exact hB z (by rwa [Metric.mem_closedBall, dist_zero_right]) m hm
      · have hzero : (fun y : IdxT E → ℝ => ((ρ y : ℝ) : ℂ)) =ᶠ[𝓝 z] (fun _ => 0) := by
          have hc : (tsupport (fun y : IdxT E → ℝ => ((ρ y : ℝ) : ℂ)))ᶜ ∈ 𝓝 z :=
            (isClosed_tsupport _).isOpen_compl.mem_nhds hzt
          filter_upwards [hc] with y hy
          rw [image_eq_zero_of_notMem_tsupport hy]
        rw [Work.Diff.STE.csqp_pdVec_congr (l := β) hzero,
          Work.Diff.STE.Lead.Gal.pdVec_zero_fun m β]
        simpa using hB0
  choose ρ B hB0 hρsm hρ1 hρtsup hBjets using hbump
  refine ⟨∑ j : ι₀, (2 : ℝ) ^ (k + 1) * (Cjet + 1) * (B j + 1), ?_, ?_⟩
  · refine Finset.sum_nonneg (fun j _ => ?_)
    exact mul_nonneg (mul_nonneg (by positivity) (by linarith [hCjet0])) (by linarith [hB0 j])
  · intro h hsym hsmooth hell hub hjet j
    set Gc : IdxT E → IdxT E → (IdxT E → ℝ) → ℂ := fun a b z =>
      ((Work.Diff.STE.B3.nres (I := I) (M := M) D j z
        (Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z)
        (Work.Diff.STE.B3.dMf (I := I) (M := M) D h j z) a b : ℝ) : ℂ) with hGc
    have hterm : ∀ j' : ι₀, 0 ≤ (2 : ℝ) ^ (k + 1) * (Cjet + 1) * (B j' + 1) :=
      fun j' => mul_nonneg (mul_nonneg (by positivity) (by linarith [hCjet0]))
        (by linarith [hB0 j'])
    have hCRj : (2 : ℝ) ^ (k + 1) * (Cjet + 1) * (B j + 1)
        ≤ ∑ j' : ι₀, (2 : ℝ) ^ (k + 1) * (Cjet + 1) * (B j' + 1) :=
      Finset.single_le_sum (fun j' _ => hterm j') (Finset.mem_univ j)
    -- the bump lies in the ball of radius `(3/2) σ j`
    have hballρ : tsupport (fun y : IdxT E → ℝ => ((ρ j y : ℝ) : ℂ))
        ⊆ Metric.closedBall (0 : IdxT E → ℝ) ((3 / 2) * D.σ j) := by
      rw [tsupport_ofReal_eq (ρ j)]
      exact hρtsup j
    refine ⟨fun a b z => Gc a b z * ((ρ j z : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
    · -- the function is smooth
      intro a b
      rw [contDiff_iff_contDiffAt]
      intro z
      by_cases hzt : z ∈ tsupport (fun y : IdxT E → ℝ => ((ρ j y : ℝ) : ℂ))
      · have hzle : ‖z‖ ≤ (3 / 2) * D.σ j := by
          have h3 := hballρ hzt
          rwa [Metric.mem_closedBall, dist_zero_right] at h3
        have hz2 : ‖z‖ < 2 * D.σ j := by have := D.hσ j; linarith
        exact (nresComp_contDiffAt (I := I) (M := M) D h hsmooth hsym hlam hell j a b hz2).mul
          (hρsm j).contDiffAt
      · have hzero : (fun y : IdxT E → ℝ => Gc a b y * ((ρ j y : ℝ) : ℂ)) =ᶠ[𝓝 z]
            (fun _ => 0) := by
          have hc : (tsupport (fun y : IdxT E → ℝ => ((ρ j y : ℝ) : ℂ)))ᶜ ∈ 𝓝 z :=
            (isClosed_tsupport _).isOpen_compl.mem_nhds hzt
          filter_upwards [hc] with y hy
          rw [image_eq_zero_of_notMem_tsupport hy]
          simp
        exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hzero
    · -- the support lies in the open `σ j`-ball
      intro a b z hz
      rw [Function.mem_support] at hz
      change Gc a b z * ((ρ j z : ℝ) : ℂ) ≠ 0 at hz
      rw [Metric.mem_ball, dist_zero_right]
      by_contra hge
      have hpos : D.σ j ≤ ‖z‖ := not_lt.mp hge
      have hG0 : Gc a b z = 0 := by
        have h := nres_eq_zero_of_sigma_le (I := I) (M := M) D j hpos
          (Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z)
          (Work.Diff.STE.B3.dMf (I := I) (M := M) D h j z) a b
        rw [hGc]
        simpa only [Complex.ofReal_zero] using congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) h
      rw [hG0, zero_mul] at hz
      exact hz rfl
    · -- the jet bound
      intro m hm β z a b
      by_cases hzt : z ∈ tsupport (fun y : IdxT E → ℝ => ((ρ j y : ℝ) : ℂ))
      · have hzle : ‖z‖ ≤ (3 / 2) * D.σ j := by
          have h3 := hballρ hzt
          rwa [Metric.mem_closedBall, dist_zero_right] at h3
        have hz2 : ‖z‖ ≤ 2 * D.σ j := by have := D.hσ j; linarith
        have hG : ContDiffAt ℝ ((⊤ : ENat) : WithTop ENat) (fun y => Gc a b y) z :=
          nresComp_contDiffAt (I := I) (M := M) D h hsmooth hsym hlam hell j a b
            (lt_of_le_of_lt hzle (by have := D.hσ j; linarith))
        have hA : ∀ (m' : ℕ), m' ≤ k → ∀ β' : Fin m' → IdxT E,
            ‖Work.Diff.STE.pdVec m' β' (fun y => Gc a b y) z‖ ≤ Cjet := by
          intro m' hm' β'
          have hb := hCjet h hsym hsmooth hell hub hjet j m' hm' β' z a b hz2
          rw [pdVec_residualLow_eq_nres_gal (I := I) (M := M) D h hsmooth j hz2 m' β' a b] at hb
          change ‖Work.Diff.STE.pdVec m' β' (fun y : IdxT E → ℝ =>
            ((Work.Diff.STE.B3.nres (I := I) (M := M) D j y
              (Work.Diff.STE.B3.Mf (I := I) (M := M) D h j y)
              (fun c i j' => Work.Diff.STE.pdR c (fun w : IdxT E → ℝ =>
                Work.Diff.STE.B3.Mf (I := I) (M := M) D h j w i j') y) a b : ℝ) : ℂ)) z‖ ≤ Cjet
          exact hb
        have hb := gardLeibnizLocal (F := fun y => Gc a b y)
          (G := fun y : IdxT E → ℝ => ((ρ j y : ℝ) : ℂ)) (A := Cjet) (B := B j) (z := z)
          hCjet0 (hB0 j) hG (hρsm j).contDiffAt hA
          (fun m' hm' β' => hBjets j m' hm' β' z) m hm β
        exact hb.trans hCRj
      · have hzero : (fun y : IdxT E → ℝ => Gc a b y * ((ρ j y : ℝ) : ℂ)) =ᶠ[𝓝 z]
            (fun _ => 0) := by
          have hc : (tsupport (fun y : IdxT E → ℝ => ((ρ j y : ℝ) : ℂ)))ᶜ ∈ 𝓝 z :=
            (isClosed_tsupport _).isOpen_compl.mem_nhds hzt
          filter_upwards [hc] with y hy
          rw [image_eq_zero_of_notMem_tsupport hy]
          simp
        rw [Work.Diff.STE.csqp_pdVec_congr (l := β) hzero,
          Work.Diff.STE.Lead.Gal.pdVec_zero_fun m β]
        simpa using Finset.sum_nonneg (fun j' _ => hterm j')
    · -- the identity on the closed `2σ j`-ball
      intro a b z hz2
      change Gc a b z * ((ρ j z : ℝ) : ℂ)
        = ((Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b : ℝ) : ℂ)
      by_cases hzσ : ‖z‖ ≤ D.σ j
      · have hρ : ρ j z = 1 := hρ1 j z hzσ
        have hid : Gc a b z
            = ((Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b : ℝ) : ℂ) := by
          rw [hGc]
          simp only [Work.Diff.STE.B3.dMf]
          exact (congrArg (fun r : ℝ => ((r : ℝ) : ℂ))
            (Work.Diff.STE.B3.residualLow_eq_nres (I := I) (M := M) D h hsmooth j hz2 a b)).symm
        rw [hρ, Complex.ofReal_one, mul_one, hid]
      · have hlt : D.σ j < ‖z‖ := not_le.mp hzσ
        have hG0 : Gc a b z = 0 := by
          have h := nres_eq_zero_of_sigma_le (I := I) (M := M) D j (le_of_lt hlt)
            (Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z)
            (Work.Diff.STE.B3.dMf (I := I) (M := M) D h j z) a b
          rw [hGc]
          simpa only [Complex.ofReal_zero] using congrArg (fun r : ℝ => ((r : ℝ) : ℂ)) h
        have hR0 : Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j z a b = 0 :=
          residualLow_eq_zero_of_sigma_lt_gal (I := I) (M := M) D h j hlt a b
        rw [hG0, hR0, Complex.ofReal_zero, zero_mul]

end Aux

end Work.Diff.STE.Lead.Gal
