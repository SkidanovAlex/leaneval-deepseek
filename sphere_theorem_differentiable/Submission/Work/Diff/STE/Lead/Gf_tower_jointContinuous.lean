/-
# Joint continuity of the jet tower of the coordinate-frame chart matrix `Gf`

Let `D` be the Layer B3 data, `U : ℝ → Bil` a family of sections whose localised chart matrices are
smooth (`ChartData`) and such that at every `t ∈ Ico 0 τ` the *difference* sections converge to `0`
in every `D.BNorm k`.  Then for every chart `i`, matrix entry `(a,b)` and multi-index `β` of length
`m`, the jet tower

  `(t, z) ↦ ∂^β (Gf D (U t) i · a b) z`

is continuous on `Ico 0 τ × ball c ρ`, where `ball c ρ` is any Euclidean ball whose radius plus
centre norm is strictly less than `2 σ i` (so that it lies inside the flat chart ball on which `Gf`
is the honest chart matrix).

The mathematical content is the same as in the sibling `jetTower_jointContinuous`, but for the
*coordinate-frame* chart matrix `Gf` (which is the unknown of the flat chart PDE) rather than for
the `g₀`-orthonormal-frame chart matrix `D.mat`:

* `Gf D h i · a b` is the chart matrix of `h` in the coordinate frame of the chart at `x₀ i`, i.e.
  `h (pt i z) (∂_a) (∂_b)` with `∂_a = frameVector (x₀ i) (bB a)`;
* the *m*-th jet of the chart matrix is homogeneous of degree `1` in the section, with a bound in
  terms of the physical energy `D.ENormB k₀` (`matJet_hom`), and `D.ENormB k₀ ≤ C · D.BNorm k₀`
  uniformly in the section (`ENormB_le_BNorm_uniform`);
* the jets of `Gf` are controlled by those of `D.mat` through the frame change
  `Gf = Finvf · Mf · Finvfᵀ` and the reconstruction of `Gf` in the `g₀`-orthonormal frames
  (`Gf_jet_bound_ball_noSym`), whose constants are independent of the section.

The two `ε`-`δ` halves of the proof are the same as in `jetTower_jointContinuous`: the time direction
is controlled *uniformly in the space variable* by the difference estimate, and the space direction
at a fixed time by the smoothness of `Gf` on the (open) region where the chart is genuine.
-/
import Mathlib
import Submission.Work.Diff.STE.Lead.JointSmoothKit
import Submission.Work.Diff.STE.Lead.jetTower_jointContinuous
import Submission.Work.Diff.STE.B3.bg_window_aux
import Submission.Work.Diff.STE.Lead.Gal.transportExistsAUniformGal
import Submission.Work.Diff.STE.Lead.GfJoint.matJet_hom
import Submission.Work.Diff.STE.Lead.GfJoint.Gf_jet_bound_ball_noSym

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff BigOperators Topology
open Set Filter Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

/-! ## 1. The physical energy is controlled by the Fourier-side norm, uniformly in the section -/

/-- **The physical energy is controlled by the Fourier-side norm, uniformly in the section.** -/
private theorem ENormB_le_BNorm_uniform
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M)),
      Work.Diff.STE.D.ChartData (I := I) (M := M) h → D.ENormB k h ≤ C * D.BNorm k h := by
  obtain ⟨C, hC, hmain⟩ :=
    Work.Diff.STE.ENormSq_le_CSq_of_contDiff_periodic (ι := Fin (Module.finrank ℝ E)) k
  refine ⟨C, hC, fun h hh => ?_⟩
  have hRsm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      ContDiff ℝ (⊤ : ℕ∞) (D.R i h a b) := fun i a b =>
    Work.Diff.STE.B3.R_contDiff_of_chartData (I := I) (M := M) D h hh i a b
  have hterm : ∀ (i : ι₀) (a b : Fin (Module.finrank ℝ E)),
      Work.Diff.STE.ENormSq k (D.Rper i h a b)
        ≤ C * Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b)) := by
    intro i a b
    obtain ⟨hcd, hper⟩ :=
      Work.Diff.STE.B3.Rper_contDiff_periodic_of_R_contDiff D i h a b (hRsm i a b)
    exact hmain (D.Rper i h a b) hcd hper
  calc D.ENormB k h
      = ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          Work.Diff.STE.ENormSq k (D.Rper i h a b) := rfl
    _ ≤ ∑ i : ι₀, ∑ a : Fin (Module.finrank ℝ E), ∑ b : Fin (Module.finrank ℝ E),
          C * Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff (D.Rper i h a b)) :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun a _ =>
          Finset.sum_le_sum fun b _ => hterm i a b
    _ = C * D.BNorm k h := by
        simp only [Work.Diff.STE.B3Data.BNorm, Finset.mul_sum]

/-! ## 2. Iterated partial derivatives of locally smooth functions -/

/-- A partial derivative of a function smooth at a point is smooth at that point. -/
private lemma contDiffAt_pd {n : ℕ} {f : (Fin n → ℝ) → ℂ} {z : Fin n → ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f z) (j : Fin n) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.STE.pd j f) z := by
  have h1 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ f) z :=
    hf.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h2 : ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun x : Fin n → ℝ => (fderiv ℝ f x) (Pi.single j (1 : ℝ))) z := by fun_prop
  exact h2

/-- Iterated partial derivatives of a function smooth at a point are smooth at that point. -/
private lemma contDiffAt_pdList {n : ℕ} {f : (Fin n → ℝ) → ℂ} {z : Fin n → ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f z) (L : List (Fin n)) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.STE.pdList L f) z := by
  induction L with
  | nil => simpa only [Work.Diff.STE.pdList, List.foldr_nil] using hf
  | cons a L ih =>
    have h : Work.Diff.STE.pdList (a :: L) f = Work.Diff.STE.pd a (Work.Diff.STE.pdList L f) := by
      simp only [Work.Diff.STE.pdList, List.foldr_cons]
    rw [h]
    exact contDiffAt_pd ih a

/-- The `m`-th jet tower of a function smooth at a point is smooth at that point. -/
private lemma contDiffAt_pdVec {n m : ℕ} {f : (Fin n → ℝ) → ℂ} {z : Fin n → ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f z) (β : Fin m → Fin n) :
    ContDiffAt ℝ (⊤ : ℕ∞) (Work.Diff.STE.pdVec m β f) z := by
  have h : Work.Diff.STE.pdVec m β f = Work.Diff.STE.pdList (List.ofFn β) f := rfl
  rw [h]
  exact contDiffAt_pdList hf _

/-- Consequently the jet tower is continuous in the flat coordinate. -/
private lemma continuousAt_pdVec_of_contDiffAt {n m : ℕ} {f : (Fin n → ℝ) → ℂ} {z : Fin n → ℝ}
    (hf : ContDiffAt ℝ (⊤ : ℕ∞) f z) (β : Fin m → Fin n) :
    ContinuousAt (fun z' => Work.Diff.STE.pdVec m β f z') z :=
  (contDiffAt_pdVec hf β).continuousAt

/-- The `m`-th jet of the difference of two real-valued functions. -/
private lemma pdVec_ofReal_sub {n m : ℕ} (f g : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ)
    (β : Fin m → Fin n) (hf : ContDiffAt ℝ (⊤ : ℕ∞) f z) (hg : ContDiffAt ℝ (⊤ : ℕ∞) g z) :
    Work.Diff.STE.pdVec m β (fun y => (((f y - g y : ℝ)) : ℂ)) z
      = Work.Diff.STE.pdVec m β (fun y => ((f y : ℝ) : ℂ)) z
        - Work.Diff.STE.pdVec m β (fun y => ((g y : ℝ) : ℂ)) z := by
  have hfg : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => f y - g y) z := hf.sub hg
  have h4 : (fun y => f y - g y) = f - g := rfl
  have h3 : iteratedFDeriv ℝ m (fun y => f y - g y) z
      = iteratedFDeriv ℝ m f z - iteratedFDeriv ℝ m g z := by
    rw [h4]
    exact iteratedFDeriv_sub_apply (𝕜 := ℝ)
      (hf.of_le (WithTop.coe_le_coe.mpr le_top))
      (hg.of_le (WithTop.coe_le_coe.mpr le_top))
  rw [Work.Diff.STE.B3.pdVec_ofReal_eq hfg m β,
    Work.Diff.STE.B3.pdVec_ofReal_eq hf m β,
    Work.Diff.STE.B3.pdVec_ofReal_eq hg m β, h3]
  simp only [sub_apply, Complex.ofReal_sub]

/-! ## 3. The main reduction

The three numerical inputs (`hGf`, `hMat`, `hEN`) are the outputs of the sibling jet-bound lemmas;
everything else is the two-variable `ε`-`δ` argument. -/

private theorem Gf_tower_main
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (τ : ℝ) (hτ : 0 < τ) (U : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : ∀ t : ℝ, Work.Diff.STE.D.ChartData (I := I) (M := M) (U t))
    (hcont : ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ k : ℕ,
      Filter.Tendsto (fun σ : ℝ => D.BNorm k (U σ - U t))
        (nhdsWithin t (Set.Ico (0 : ℝ) τ)) (nhds 0))
    (i : ι₀) (c : Fin (Module.finrank ℝ E) → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hball : ‖c‖ + ρ < 2 * D.σ i)
    (m : ℕ) (β : Fin m → Fin (Module.finrank ℝ E)) (a b : Fin (Module.finrank ℝ E))
    (δ : ℝ) (hδ : 0 < δ)
    (htgtδ : ∀ (j : ι₀) (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + δ →
      Work.Diff.STE.flatToE (I := I) (D.x₀ j) z ∈ (extChartAt I (D.x₀ j)).target)
    (k₀ : ℕ) (hk₀ : ∀ m' : ℕ, m' ≤ m + 1 → 2 * m' + Module.finrank ℝ E < 2 * k₀)
    (hGf : ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (K : ℝ) (hK : 0 ≤ K)
        (hjet : ∀ (i : ι₀) (m' : ℕ) (hm' : m' ≤ m + 1)
          (β : Fin m' → Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ) (c d : Fin (Module.finrank ℝ E)),
          ‖z‖ ≤ 2 * D.σ i →
          ‖Work.Diff.STE.pdVec m' β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K),
        ∀ (j : ι₀) (m' : ℕ) (hm' : m' ≤ m) (β : Fin m' → Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ) (a b : Fin (Module.finrank ℝ E)),
          ‖z‖ ≤ 2 * D.σ j + δ →
          ‖Work.Diff.STE.pdVec m' β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b : ℝ) : ℂ)) z‖ ≤ C * K)
    (hMat : ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (m' : ℕ)
        (hm' : 2 * m' + Module.finrank ℝ E < 2 * k₀)
        (β : Fin m' → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
        ‖z‖ ≤ 2 * D.σ i →
        ‖Work.Diff.STE.pdVec m' β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ C * Real.sqrt (D.ENormB k₀ h))
    (hEN : ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : Work.Diff.STE.Bil (I := I) (M := M)),
        Work.Diff.STE.D.ChartData (I := I) (M := M) h → D.ENormB k₀ h ≤ C * D.BNorm k₀ h) :
    ContinuousOn (fun p : ℝ × (Fin (Module.finrank ℝ E) → ℝ) =>
        Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((Work.Diff.STE.B3.Gf (I := I) (M := M) D (U p.1) i y a b : ℝ) : ℂ)) p.2)
      (Set.Ico (0 : ℝ) τ ×ˢ Metric.ball c ρ) := by
  classical
  obtain ⟨CG, hCGnn, hCGb⟩ := hGf
  obtain ⟨CM, hCMnn, hCMb⟩ := hMat
  obtain ⟨C₁, hC₁nn, hC₁b⟩ := hEN
  set F : ℝ × (Fin (Module.finrank ℝ E) → ℝ) → ℂ := fun p =>
    Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      ((Work.Diff.STE.B3.Gf (I := I) (M := M) D (U p.1) i y a b : ℝ) : ℂ)) p.2 with hFdef
  -- the open (flat) region on which the chart at `x₀ i` is genuine
  have hopenReg : IsOpen {z : Fin (Module.finrank ℝ E) → ℝ |
      Work.Diff.STE.flatToE (I := I) (D.x₀ i) z ∈ (extChartAt I (D.x₀ i)).target} :=
    (isOpen_extChartAt_target (I := I) (D.x₀ i)).preimage
      (contDiff_flatToE (I := I) (x₀ := D.x₀ i)).continuous
  -- the two-point estimate, uniform in the space variable on the `2σ i`-ball
  have hkey : ∀ (s t : ℝ), s ∈ Set.Ico (0 : ℝ) τ → t ∈ Set.Ico (0 : ℝ) τ →
      ∀ z : Fin (Module.finrank ℝ E) → ℝ, ‖z‖ ≤ 2 * D.σ i →
      ‖F (s, z) - F (t, z)‖ ≤ CG * CM * Real.sqrt (C₁ * D.BNorm k₀ (U s - U t)) := by
    intro s t hs ht z hz
    have hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) (U s - U t) :=
      ChartData_sub (U s) (U t) (hsm s) (hsm t)
    have hjet : ∀ (i' : ι₀) (m' : ℕ) (hm' : m' ≤ m + 1)
        (β' : Fin m' → Fin (Module.finrank ℝ E))
        (z' : Fin (Module.finrank ℝ E) → ℝ) (cc dd : Fin (Module.finrank ℝ E)),
        ‖z'‖ ≤ 2 * D.σ i' →
        ‖Work.Diff.STE.pdVec m' β' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((D.mat i' (U s - U t) cc dd y : ℝ) : ℂ)) z'‖
          ≤ CM * Real.sqrt (D.ENormB k₀ (U s - U t)) := by
      intro i' m' hm' β' z' cc dd hz'
      exact hCMb (U s - U t) hsmooth i' cc dd m' (hk₀ m' hm') β' z' hz'
    have hstep1 : ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((Work.Diff.STE.B3.Gf (I := I) (M := M) D (U s - U t) i y a b : ℝ) : ℂ)) z‖
        ≤ CG * (CM * Real.sqrt (D.ENormB k₀ (U s - U t))) :=
      hCGb (U s - U t) hsmooth (CM * Real.sqrt (D.ENormB k₀ (U s - U t)))
        (mul_nonneg hCMnn (Real.sqrt_nonneg _)) hjet i m (le_refl m) β z a b
        (by have hσ := D.hσ i; linarith)
    -- the section `U s - U t` and the difference of the two jet towers
    have hzmem : Work.Diff.STE.flatToE (I := I) (D.x₀ i) z
        ∈ (extChartAt I (D.x₀ i)).target := D.htarget i z hz
    have hcs : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          Work.Diff.STE.B3.Gf (I := I) (M := M) D (U s) i y a b) z :=
      (Work.Diff.STE.Lead.Gal.Gf_contDiffOn_target D (U s) (hsm s) i a b).contDiffAt
        (hopenReg.mem_nhds hzmem)
    have hct : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          Work.Diff.STE.B3.Gf (I := I) (M := M) D (U t) i y a b) z :=
      (Work.Diff.STE.Lead.Gal.Gf_contDiffOn_target D (U t) (hsm t) i a b).contDiffAt
        (hopenReg.mem_nhds hzmem)
    have hdiff : (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((Work.Diff.STE.B3.Gf (I := I) (M := M) D (U s - U t) i y a b : ℝ) : ℂ))
        = fun y : Fin (Module.finrank ℝ E) → ℝ =>
            (((Work.Diff.STE.B3.Gf (I := I) (M := M) D (U s) i y a b
              - Work.Diff.STE.B3.Gf (I := I) (M := M) D (U t) i y a b : ℝ)) : ℂ) := by
      rfl
    have hsub : Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((Work.Diff.STE.B3.Gf (I := I) (M := M) D (U s - U t) i y a b : ℝ) : ℂ)) z
        = F (s, z) - F (t, z) := by
      rw [hdiff, hFdef]
      exact pdVec_ofReal_sub _ _ z β hcs hct
    rw [← hsub]
    refine hstep1.trans ?_
    have hsq : Real.sqrt (D.ENormB k₀ (U s - U t))
        ≤ Real.sqrt (C₁ * D.BNorm k₀ (U s - U t)) := Real.sqrt_le_sqrt (hC₁b _ hsmooth)
    calc CG * (CM * Real.sqrt (D.ENormB k₀ (U s - U t)))
        ≤ CG * (CM * Real.sqrt (C₁ * D.BNorm k₀ (U s - U t))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hCMnn) hCGnn
      _ = CG * CM * Real.sqrt (C₁ * D.BNorm k₀ (U s - U t)) := by ring
  rw [ContinuousOn]
  intro p₀ hp₀
  obtain ⟨ht₀, hz₀ball⟩ := hp₀
  have hz₀ : ‖p₀.2‖ ≤ 2 * D.σ i := by
    have h1 : ‖p₀.2 - c‖ < ρ := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hz₀ball
    have h2 : ‖p₀.2‖ ≤ ‖p₀.2 - c‖ + ‖c‖ := by
      calc ‖p₀.2‖ = ‖(p₀.2 - c) + c‖ := by rw [sub_add_cancel]
        _ ≤ ‖p₀.2 - c‖ + ‖c‖ := norm_add_le _ _
    linarith
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  -- the time direction: uniform in space
  have hlim : Filter.Tendsto
      (fun σ : ℝ => CG * CM * Real.sqrt (C₁ * D.BNorm k₀ (U σ - U p₀.1)))
      (nhdsWithin p₀.1 (Set.Ico (0 : ℝ) τ)) (nhds 0) := by
    have hc : ContinuousAt (fun x : ℝ => Real.sqrt (C₁ * x)) 0 :=
      ContinuousAt.sqrt (continuousAt_const.mul continuousAt_id)
    have h3 := hc.tendsto.comp (hcont p₀.1 ht₀ k₀)
    have h4 := h3.const_mul (CG * CM)
    simpa using h4
  have hev : ∀ᶠ σ in nhdsWithin p₀.1 (Set.Ico (0 : ℝ) τ),
      CG * CM * Real.sqrt (C₁ * D.BNorm k₀ (U σ - U p₀.1)) < ε / 2 := by
    have h := (Metric.tendsto_nhds.mp hlim) (ε / 2) (by linarith)
    refine h.mono fun σ hσ => ?_
    rw [Real.dist_eq, sub_zero] at hσ
    exact lt_of_le_of_lt (le_abs_self _) hσ
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ := hev
  -- the space direction at the fixed time
  have hz₀mem : Work.Diff.STE.flatToE (I := I) (D.x₀ i) p₀.2
      ∈ (extChartAt I (D.x₀ i)).target := D.htarget i p₀.2 hz₀
  have hcpt : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Fin (Module.finrank ℝ E) → ℝ =>
      ((Work.Diff.STE.B3.Gf (I := I) (M := M) D (U p₀.1) i y a b : ℝ) : ℂ)) p₀.2 :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp p₀.2
      ((Work.Diff.STE.Lead.Gal.Gf_contDiffOn_target D (U p₀.1) (hsm p₀.1) i a b).contDiffAt
        (hopenReg.mem_nhds hz₀mem))
  have hcz : ContinuousAt (fun z : Fin (Module.finrank ℝ E) → ℝ =>
      Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
        ((Work.Diff.STE.B3.Gf (I := I) (M := M) D (U p₀.1) i y a b : ℝ) : ℂ)) z) p₀.2 :=
    continuousAt_pdVec_of_contDiffAt hcpt β
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ := Metric.continuousAt_iff.mp hcz (ε / 2) (by linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
  intro p hp hdist
  obtain ⟨hp1, hp2⟩ := hp
  rw [Prod.dist_eq] at hdist
  have hσlt : dist p.1 p₀.1 < δ₁ :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_left _ _) hdist) (min_le_left _ _)
  have hzlt : dist p.2 p₀.2 < δ₂ :=
    lt_of_lt_of_le (lt_of_le_of_lt (le_max_right _ _) hdist) (min_le_right _ _)
  have hz2 : ‖p.2‖ ≤ 2 * D.σ i := by
    have h1 : ‖p.2 - c‖ < ρ := by
      simpa only [Metric.mem_ball, dist_eq_norm] using hp2
    have h2 : ‖p.2‖ ≤ ‖p.2 - c‖ + ‖c‖ := by
      calc ‖p.2‖ = ‖(p.2 - c) + c‖ := by rw [sub_add_cancel]
        _ ≤ ‖p.2 - c‖ + ‖c‖ := norm_add_le _ _
    linarith
  have h1 : ‖F (p.1, p.2) - F (p₀.1, p.2)‖ < ε / 2 :=
    lt_of_le_of_lt (hkey p.1 p₀.1 hp1 ht₀ p.2 hz2) (hδ₁ hσlt hp1)
  have h2 : ‖F (p₀.1, p.2) - F (p₀.1, p₀.2)‖ < ε / 2 := by
    have h := hδ₂ hzlt
    rw [dist_eq_norm] at h
    simpa only [hFdef] using h
  rw [dist_eq_norm]
  have hsplit : F p - F p₀
      = (F (p.1, p.2) - F (p₀.1, p.2)) + (F (p₀.1, p.2) - F (p₀.1, p₀.2)) := by
    have hp' : p = (p.1, p.2) := rfl
    have hp₀' : p₀ = (p₀.1, p₀.2) := rfl
    rw [hp', hp₀']
    ring
  rw [hsplit]
  calc ‖(F (p.1, p.2) - F (p₀.1, p.2)) + (F (p₀.1, p.2) - F (p₀.1, p₀.2))‖
      ≤ ‖F (p.1, p.2) - F (p₀.1, p.2)‖ + ‖F (p₀.1, p.2) - F (p₀.1, p₀.2)‖ :=
        norm_add_le _ _
    _ < ε := by linarith

/-! ## 4. The target -/

theorem Gf_tower_jointContinuous
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (τ : ℝ) (hτ : 0 < τ) (U : ℝ → Work.Diff.STE.Bil (I := I) (M := M))
    (hsm : ∀ t : ℝ, Work.Diff.STE.D.ChartData (I := I) (M := M) (U t))
    (B : ℕ → ℝ) (hB : ∀ k : ℕ, 0 ≤ B k)
    (hUB : ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ k : ℕ, D.BNorm k (U t) ≤ B k)
    (hcont : ∀ t ∈ Set.Ico (0 : ℝ) τ, ∀ k : ℕ,
      Filter.Tendsto (fun σ : ℝ => D.BNorm k (U σ - U t))
        (nhdsWithin t (Set.Ico (0 : ℝ) τ)) (nhds 0))
    (i : ι₀) (c : Fin (Module.finrank ℝ E) → ℝ) (ρ : ℝ) (hρ : 0 < ρ)
    (hball : ‖c‖ + ρ < 2 * D.σ i)
    (m : ℕ) (β : Fin m → Fin (Module.finrank ℝ E)) (a b : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun p : ℝ × (Fin (Module.finrank ℝ E) → ℝ) =>
        Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((Work.Diff.STE.B3.Gf (I := I) (M := M) D (U p.1) i y a b : ℝ) : ℂ)) p.2)
      (Set.Ico (0 : ℝ) τ ×ˢ Metric.ball c ρ) := by
  classical
  obtain ⟨δ, mlo, Mhi, hδpos, hmlopos, hMhipos, htgtδ, hlo, hhi⟩ :=
    Work.Diff.STE.B3.bg_window_aux (I := I) (M := M) D
  set k₀ : ℕ := m + Module.finrank ℝ E + 2 with hk₀def
  have hk₀ : ∀ m' : ℕ, m' ≤ m + 1 → 2 * m' + Module.finrank ℝ E < 2 * k₀ := by
    intro m' hm'
    rw [hk₀def]
    omega
  -- the three jet/energy bounds of the sibling modules
  have key : ∃ (CG CM C₁ : ℝ), 0 ≤ CG ∧ 0 ≤ CM ∧ 0 ≤ C₁ ∧
      (∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (K : ℝ) (hK : 0 ≤ K)
        (hjet : ∀ (i : ι₀) (m' : ℕ) (hm' : m' ≤ m + 1)
          (β : Fin m' → Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ) (c d : Fin (Module.finrank ℝ E)),
          ‖z‖ ≤ 2 * D.σ i →
          ‖Work.Diff.STE.pdVec m' β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K),
        ∀ (j : ι₀) (m' : ℕ) (hm' : m' ≤ m) (β : Fin m' → Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ) (a b : Fin (Module.finrank ℝ E)),
          ‖z‖ ≤ 2 * D.σ j + δ →
          ‖Work.Diff.STE.pdVec m' β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b : ℝ) : ℂ)) z‖ ≤ CG * K) ∧
      (∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (i : ι₀) (c d : Fin (Module.finrank ℝ E)) (m' : ℕ)
        (hm' : 2 * m' + Module.finrank ℝ E < 2 * k₀)
        (β : Fin m' → Fin (Module.finrank ℝ E)) (z : Fin (Module.finrank ℝ E) → ℝ),
        ‖z‖ ≤ 2 * D.σ i →
        ‖Work.Diff.STE.pdVec m' β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ CM * Real.sqrt (D.ENormB k₀ h)) ∧
      (∀ (h : Work.Diff.STE.Bil (I := I) (M := M)),
        Work.Diff.STE.D.ChartData (I := I) (M := M) h → D.ENormB k₀ h ≤ C₁ * D.BNorm k₀ h) := by
    obtain ⟨CM, hCMnn, hCMb⟩ :=
      Work.Diff.STE.Lead.GfJoint.matJet_hom (I := I) (M := M) D k₀
    obtain ⟨C₁, hC₁nn, hC₁b⟩ := ENormB_le_BNorm_uniform (I := I) (M := M) D k₀
    obtain ⟨CG, hCGnn, hCGb⟩ : ∃ C : ℝ, 0 ≤ C ∧
        ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
        (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
        (K : ℝ) (hK : 0 ≤ K)
        (hjet : ∀ (i : ι₀) (m' : ℕ) (hm' : m' ≤ m + 1)
          (β : Fin m' → Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ) (c d : Fin (Module.finrank ℝ E)),
          ‖z‖ ≤ 2 * D.σ i →
          ‖Work.Diff.STE.pdVec m' β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((D.mat i h c d y : ℝ) : ℂ)) z‖ ≤ K),
        ∀ (j : ι₀) (m' : ℕ) (hm' : m' ≤ m) (β : Fin m' → Fin (Module.finrank ℝ E))
          (z : Fin (Module.finrank ℝ E) → ℝ) (a b : Fin (Module.finrank ℝ E)),
          ‖z‖ ≤ 2 * D.σ j + δ →
          ‖Work.Diff.STE.pdVec m' β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y a b : ℝ) : ℂ)) z‖ ≤ C * K := by
      -- `Work.Diff.STE.Lead.GfJoint.Gf_jet_bound_ball_noSym D m δ hδpos htgtδ`
      exact Work.Diff.STE.Lead.GfJoint.Gf_jet_bound_ball_noSym (I := I) (M := M) D m δ hδpos htgtδ
    exact ⟨CG, CM, C₁, hCGnn, hCMnn, hC₁nn, hCGb, hCMb, hC₁b⟩
  obtain ⟨CG, CM, C₁, hCGnn, hCMnn, hC₁nn, hCGb, hCMb, hC₁b⟩ := key
  exact Gf_tower_main D τ hτ U hsm hcont i c ρ hρ hball m β a b δ hδpos htgtδ k₀ hk₀
    ⟨CG, hCGnn, hCGb⟩ ⟨CM, hCMnn, hCMb⟩ ⟨C₁, hC₁nn, hC₁b⟩

end Work.Diff.STE.Lead
