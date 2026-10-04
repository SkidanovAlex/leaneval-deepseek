import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.transport_contDiffOn_inv_entry
import Submission.Work.Diff.STE.B3.LowJetDefs
import Submission.Work.Diff.STE.B3.LowJetAux
import Submission.Work.Diff.STE.B3.norm_iteratedFDerivWithin_le_pi
import Submission.Work.Diff.STE.B3.norm_iteratedFDerivWithin_le_tuple3
import Submission.Work.Diff.STE.B3.iteratedFDeriv_le_of_pdVec
import Submission.Work.Diff.STE.B3.iteratedFDeriv_fderiv_le_of_pdVec
import Submission.Work.Diff.STE.B3.nres_jet_bound_compact_v2
import Submission.Work.Diff.STE.B3.Mf_sandwich
import Submission.Work.Diff.STE.B3.nresC_contDiffOn
import Submission.Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
  {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}

noncomputable section

local notation "Idx" => Fin (Module.finrank ℝ E)

theorem pdVec_zero_germ {ι : Type*} [Fintype ι] [DecidableEq ι] (l : Fin 0 → ι)
    (f : (ι → ℝ) → ℂ) : Work.Diff.STE.pdVec 0 l f = f := by
  rw [Work.Diff.STE.pdVec, Work.Diff.STE.pdList, List.ofFn_zero, List.foldr_nil]

theorem pdVec_congr_germ {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f g : (ι → ℝ) → ℂ} {x : ι → ℝ} (h : f =ᶠ[nhds x] g) (m : ℕ) (l : Fin m → ι) :
    Work.Diff.STE.pdVec m l f x = Work.Diff.STE.pdVec m l g x := by
  have hpd : ∀ (k : ℕ) (l : Fin (k + 1) → ι) (u : (ι → ℝ) → ℂ),
      Work.Diff.STE.pdVec (k + 1) l u
        = Work.Diff.STE.pd (l 0) (Work.Diff.STE.pdVec k (Fin.tail l) u) := by
    intro k l u
    have h0 : List.ofFn l = l 0 :: List.ofFn (Fin.tail l) := by
      conv_lhs => rw [← Fin.cons_self_tail l]
      rw [List.ofFn_cons]
    simp only [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]
    rw [h0, List.foldr_cons]
  suffices H : ∀ m (l : Fin m → ι),
      Work.Diff.STE.pdVec m l f =ᶠ[nhds x] Work.Diff.STE.pdVec m l g by
    exact (H m l).eq_of_nhds
  intro m
  induction m with
  | zero =>
      intro l
      rw [pdVec_zero_germ l f, pdVec_zero_germ l g]
      exact h
  | succ k ih =>
      intro l
      rw [hpd k l f, hpd k l g]
      have hfd : fderiv ℝ (Work.Diff.STE.pdVec k (Fin.tail l) f)
          =ᶠ[nhds x] fderiv ℝ (Work.Diff.STE.pdVec k (Fin.tail l) g) :=
        Filter.EventuallyEq.fderiv (𝕜 := ℝ) (ih (Fin.tail l))
      filter_upwards [hfd] with y hy
      change fderiv ℝ (Work.Diff.STE.pdVec k (Fin.tail l) f) y (Pi.single (l 0) 1)
        = fderiv ℝ (Work.Diff.STE.pdVec k (Fin.tail l) g) y (Pi.single (l 0) 1)
      rw [hy]


lemma fderiv_ofReal_comp {n : ℕ} (f : (Fin n → ℝ) → ℝ) (z v : Fin n → ℝ) :
    fderiv ℝ (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) z v
      = ((fderiv ℝ f z v : ℝ) : ℂ) := by
  by_cases hf : DifferentiableAt ℝ f z
  · have h1 : HasFDerivAt (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ))
        ((Complex.ofRealCLM : ℝ →L[ℝ] ℂ).comp (fderiv ℝ f z)) z :=
      Complex.ofRealCLM.hasFDerivAt.comp z hf.hasFDerivAt
    rw [h1.fderiv]
    rfl
  · have h2 : fderiv ℝ f z = 0 := fderiv_zero_of_not_differentiableAt hf
    rw [h2]
    have h3 : ¬ DifferentiableAt ℝ (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) z := by
      intro hc
      refine hf ?_
      have h4 : DifferentiableAt ℝ (fun y : Fin n → ℝ => Complex.re (((f y : ℝ) : ℂ))) z :=
        Complex.reCLM.differentiableAt.comp z hc
      simpa using h4
    rw [fderiv_zero_of_not_differentiableAt h3]
    simp

lemma exists_bump_subset {n : ℕ} {U : Set (Fin n → ℝ)} (hU : IsOpen U) {z : Fin n → ℝ}
    (hz : z ∈ U) :
    ∃ (φ : (Fin n → ℝ) → ℝ) (r : ℝ), ContDiff ℝ (⊤ : ℕ∞) φ ∧ 0 ≤ φ ∧ 0 < r ∧
      (∀ y : Fin n → ℝ, ‖y - z‖ ≤ r → φ y = 1) ∧ tsupport φ ⊆ U := by
  obtain ⟨ε, hεpos, hεsub⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz)
  let ρ : ContDiffBump z := ⟨ε / 4, ε / 2, by linarith, by linarith⟩
  have hrIn : ρ.rIn = ε / 4 := rfl
  have hrOut : ρ.rOut = ε / 2 := rfl
  refine ⟨ρ, ρ.rIn, ρ.contDiff, fun x => ρ.nonneg, by rw [hrIn]; linarith, ?_, ?_⟩
  · intro y hy
    refine ρ.one_of_mem_closedBall ?_
    rw [Metric.mem_closedBall, dist_eq_norm]
    rw [hrIn] at hy
    exact hy
  · intro y hy
    refine hεsub ?_
    have h1 : y ∈ Metric.closedBall z (ε / 2) := by
      rw [ρ.tsupport_eq] at hy
      exact hy
    rw [Metric.mem_closedBall, dist_eq_norm] at h1
    rw [Metric.mem_ball, dist_eq_norm]
    linarith

lemma contDiff_mul_of_contDiffOn {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
    {ψ : E' → ℝ} {f : E' → ℂ} {U : Set E'}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hf : ContDiffOn ℝ (⊤ : ℕ∞) f U)
    (hU : IsOpen U) (hsub : tsupport ψ ⊆ U) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ((ψ x : ℝ) : ℂ) * f x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ tsupport ψ
  · have h1 : ContDiffAt ℝ (⊤ : ℕ∞) f x := hf.contDiffAt (hU.mem_nhds (hsub hx))
    have h2 : ContDiffAt ℝ (⊤ : ℕ∞) (fun y => ((ψ y : ℝ) : ℂ)) x :=
      Complex.ofRealCLM.contDiff.contDiffAt.comp x hψ.contDiffAt
    exact h2.mul h1
  · have h0 : ∀ᶠ y in nhds x, ψ y = 0 := by
      have hc : (tsupport ψ)ᶜ ∈ nhds x :=
        (isClosed_tsupport ψ).isOpen_compl.mem_nhds hx
      filter_upwards [hc] with y hy
      by_contra hne
      exact hy (subset_closure (Function.mem_support.mpr hne))
    refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
    filter_upwards [h0] with y hy
    simp [hy]

/-- The `pd`-partial derivative of a complexified real function is the complexification of `pdR`. -/
lemma pd_ofReal_comp {n : ℕ} (c : Fin n) (f : (Fin n → ℝ) → ℝ) (z : Fin n → ℝ) :
    Work.Diff.STE.pd c (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) z
      = ((Work.Diff.STE.pdR c f z : ℝ) : ℂ) :=
  fderiv_ofReal_comp f z (Pi.single c 1)

/-- The first iterated partial derivative vector of order one is the single partial derivative. -/
lemma pdVec_one_eq_pd {n : ℕ} (c : Fin n) (f : (Fin n → ℝ) → ℂ) :
    Work.Diff.STE.pdVec 1 (fun _ : Fin 1 => c) f = Work.Diff.STE.pd c f := by
  have h : List.ofFn (fun _ : Fin 1 => c) = [c] := rfl
  simp only [Work.Diff.STE.pdVec, Work.Diff.STE.pdList, h, List.foldr_cons, List.foldr_nil]

/-- The norm of a real number viewed in `ℂ`. -/
lemma norm_ofReal_eq_abs' (x : ℝ) : ‖((x : ℝ) : ℂ)‖ = |x| := by
  rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq_eq_abs]

/-- The jet of the identity map is bounded by `1` in order `≥ 1`. -/
lemma norm_iteratedFDeriv_id_le_one {n : ℕ} {i : ℕ} (h1 : 1 ≤ i) (z : Fin n → ℝ) :
    ‖iteratedFDeriv ℝ i (fun y : Fin n → ℝ => y) z‖ ≤ 1 := by
  have hfd : fderiv ℝ (fun y : Fin n → ℝ => y)
      = fun _ => (1 : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ)) := by
    funext x
    exact fderiv_id
  rcases Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0) with ⟨j, rfl⟩
  cases j with
  | zero =>
      rw [norm_iteratedFDeriv_one, hfd]
      exact ContinuousLinearMap.norm_id_le
  | succ j =>
      rw [← norm_iteratedFDeriv_fderiv (f := fun y : Fin n → ℝ => y) (n := j + 1) (x := z)]
      rw [hfd, iteratedFDeriv_const_of_ne (by omega : j + 1 ≠ 0)]
      simp

end


local notation "Idx" => Fin (Module.finrank ℝ E)

theorem transport_low_jet_bound_uniform
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (k : ℕ) :
    ∀ (lam K : ℝ), 0 < lam → 0 < K →
      ∃ C : ℝ, 0 ≤ C ∧
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
          ∀ (j : ι₀) (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin (Module.finrank ℝ E))
            (z : Fin (Module.finrank ℝ E) → ℝ) (a b : Fin (Module.finrank ℝ E)),
            ‖z‖ ≤ 2 * D.σ j →
            ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((Work.Diff.STE.B3.residualLow (I := I) (M := M) D h j y a b : ℝ) : ℂ)) z‖ ≤ C := by
  classical
  obtain ⟨C1, hC1nn, hC1⟩ := iteratedFDeriv_le_of_pdVec (n := Module.finrank ℝ E) (M := k + 1)
  obtain ⟨C2, hC2nn, hC2⟩ := iteratedFDeriv_fderiv_le_of_pdVec (n := Module.finrank ℝ E) (M := k)
  intro lam K hlam hK
  choose Co hCo0 hCo using fun j : ι₀ =>
    nres_jet_bound_compact_v2 (I := I) (M := M) D j k lam K hlam hK
  obtain ⟨D0, hD0ge1, hD0geC1, hD0geC2⟩ : ∃ D0 : ℝ, 1 ≤ D0 ∧ C1 * K ≤ D0 ∧ C2 * K ≤ D0 :=
    ⟨max 1 (max (C1 * K) (C2 * K)), le_max_left _ _,
      le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  have hD0nn : 0 ≤ D0 := le_trans zero_le_one hD0ge1
  refine ⟨∑ j : ι₀, ∑ m ∈ Finset.range (k + 1), (m.factorial : ℝ) * Co j * D0 ^ m, ?_, ?_⟩
  · refine Finset.sum_nonneg (fun j _ => Finset.sum_nonneg (fun m _ => ?_))
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCo0 j)) (pow_nonneg hD0nn m)
  · intro h hsym hsmooth hell hub hjet j m hm β z a b hz
    obtain ⟨hsymm, hellip, hentry, hdetM⟩ :=
      Mf_sandwich (I := I) (M := M) D j lam K hlam hK h hsym hell hub z hz
    set F : (Fin (Module.finrank ℝ E) → ℝ) → (Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) × (Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ) :=
      fun y => (y, Mf (I := I) (M := M) D h j y, dMf (I := I) (M := M) D h j y)
      with hFdef
    set Uz : Set (Fin (Module.finrank ℝ E) → ℝ) := {y | F y ∈ lowJetDom (I := I) (M := M) D j} with hUzdef
    have hmem_iff : ∀ y : Fin (Module.finrank ℝ E) → ℝ, y ∈ Uz ↔
        (Work.Diff.STE.flatToE (I := I) (D.x₀ j) y ∈ (extChartAt I (D.x₀ j)).target ∧
          (Matrix.of (Ff (I := I) (M := M) D j y)).det ≠ 0 ∧
          (Matrix.of (Mf (I := I) (M := M) D h j y)).det ≠ 0) :=
      fun y => Iff.rfl
    have hUz_open : IsOpen Uz := by
      rw [isOpen_iff_mem_nhds]
      intro y hy
      obtain ⟨hy1, hy2, hy3⟩ := (hmem_iff y).mp hy
      have h1 : ∀ᶠ w in nhds y,
          Work.Diff.STE.flatToE (I := I) (D.x₀ j) w ∈ (extChartAt I (D.x₀ j)).target :=
        ((isOpen_extChartAt_target (I := I) (D.x₀ j)).preimage
          (Work.Diff.STE.contDiff_flatToE (I := I) (x₀ := D.x₀ j)).continuous).mem_nhds hy1
      have h2 : ∀ᶠ w in nhds y,
          (Matrix.of (Ff (I := I) (M := M) D j w)).det ≠ 0 :=
        (tmNom_det_ContDiffAt (X := fun w : Fin (Module.finrank ℝ E) → ℝ =>
            Matrix.of (Ff (I := I) (M := M) D j w))
          (fun p q => Ff_contDiffAt (I := I) (M := M) D j p q hy1)).continuousAt.eventually_ne hy2
      have h3 : ∀ᶠ w in nhds y,
          (Matrix.of (Mf (I := I) (M := M) D h j w)).det ≠ 0 :=
        (tmNom_det_ContDiffAt (X := fun w : Fin (Module.finrank ℝ E) → ℝ =>
            Matrix.of (Mf (I := I) (M := M) D h j w))
          (fun p q => contDiffAt_pi.mp (contDiffAt_pi.mp
            (Mf_pi_contDiffAt_of_target (I := I) (M := M) D h hsmooth j hy1) p) q)
            ).continuousAt.eventually_ne hy3
      filter_upwards [h1, h2, h3] with w hw1 hw2 hw3
      exact (hmem_iff w).mpr ⟨hw1, hw2, hw3⟩
    have hzUz : z ∈ Uz :=
      (hmem_iff z).mpr ⟨D.htarget j z hz, det_Ff_ne_zero (I := I) (M := M) D j hz, hdetM⟩
    have hF_smooth : ContDiffOn ℝ (⊤ : ℕ∞) F Uz := by
      intro y hy
      have hy1 : Work.Diff.STE.flatToE (I := I) (D.x₀ j) y ∈ (extChartAt I (D.x₀ j)).target :=
        ((hmem_iff y).mp hy).1
      have h := state_contDiffAt_of_target (I := I) (M := M) D h hsmooth j hy1
      simpa only [hFdef] using h.contDiffWithinAt
    have hMapsTo : MapsTo F Uz (lowJetDom (I := I) (M := M) D j) := fun y hy => hy
    have hFz_ball : F z ∈ lowJetBall (I := I) (M := M) D j lam K := by
      refine ⟨hz, ?_, ?_, ?_, ?_⟩
      · intro af bf; exact hsymm af bf
      · intro ξ; exact hellip ξ
      · intro af bf; exact hentry af bf
      · intro c af bf
        have h1 := hjet j 1 (by omega) (fun _ : Fin 1 => c) z af bf hz
        rw [pdVec_one_eq_pd c, pd_ofReal_comp c (fun y => D.mat j h af bf y) z,
          norm_ofReal_eq_abs'] at h1
        simpa only [hFdef, dMf, Mf] using h1
    have hC : ∀ i : ℕ, i ≤ m →
        ‖iteratedFDerivWithin ℝ i (nresC (I := I) (M := M) D j a b)
          (lowJetDom (I := I) (M := M) D j) (F z)‖ ≤ Co j :=
      fun i hi => hCo j a b (F z) hFz_ball i (le_trans hi hm)
    have hMf_bound : ∀ i : ℕ, i ≤ k →
        ‖iteratedFDerivWithin ℝ i (fun y : Fin (Module.finrank ℝ E) → ℝ => Mf (I := I) (M := M) D h j y) Uz z‖
          ≤ C1 * K := by
      intro i hi
      have hMf_sm := Mf_pi_contDiffAt_of_target (I := I) (M := M) D h hsmooth j (D.htarget j z hz)
      have hinner : ∀ af : Fin (Module.finrank ℝ E),
          ‖iteratedFDerivWithin ℝ i (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            Mf (I := I) (M := M) D h j y af) Uz z‖ ≤ C1 * K := by
        intro af
        refine norm_iteratedFDerivWithin_le_pi (A := C1 * K) (mul_nonneg hC1nn hK.le)
          hUz_open.uniqueDiffOn hzUz ?_ ?_
        · exact (contDiffAt_pi.mp hMf_sm af).contDiffWithinAt
        · intro bf
          have hpd := hC1 (fun y : Fin (Module.finrank ℝ E) → ℝ => D.mat j h af bf y) z K hK.le
            (Mf_contDiffAt_of_target (I := I) (M := M) D h hsmooth j af bf (D.htarget j z hz))
            (fun mm hmm γ => hjet j mm hmm γ z af bf hz) i (by omega)
          rw [show iteratedFDerivWithin ℝ i (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                Mf (I := I) (M := M) D h j y af bf) Uz z
              = iteratedFDeriv ℝ i (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                Mf (I := I) (M := M) D h j y af bf) z from
            iteratedFDerivWithin_of_isOpen i hUz_open hzUz]
          exact hpd
      refine norm_iteratedFDerivWithin_le_pi (A := C1 * K) (mul_nonneg hC1nn hK.le)
        hUz_open.uniqueDiffOn hzUz ?_ hinner
      exact hMf_sm.contDiffWithinAt
    have hdMf_bound : ∀ i : ℕ, i ≤ k →
        ‖iteratedFDerivWithin ℝ i (fun y : Fin (Module.finrank ℝ E) → ℝ => dMf (I := I) (M := M) D h j y) Uz z‖
          ≤ C2 * K := by
      intro i hi
      have hdMf_sm : ContDiffAt ℝ (⊤ : ℕ∞)
          (fun y : Fin (Module.finrank ℝ E) → ℝ => dMf (I := I) (M := M) D h j y) z :=
        contDiffAt_pi.mpr (fun c => contDiffAt_pi.mpr (fun af => contDiffAt_pi.mpr (fun bf =>
          dMf_contDiffAt_of_target (I := I) (M := M) D h hsmooth j c af bf (D.htarget j z hz))))
      have hinner2 : ∀ c : Fin (Module.finrank ℝ E),
          ‖iteratedFDerivWithin ℝ i (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            dMf (I := I) (M := M) D h j y c) Uz z‖ ≤ C2 * K := by
        intro c
        have hc_sm : ContDiffAt ℝ (⊤ : ℕ∞)
            (fun y : Fin (Module.finrank ℝ E) → ℝ => dMf (I := I) (M := M) D h j y c) z :=
          contDiffAt_pi.mp hdMf_sm c
        have hinner3 : ∀ af : Fin (Module.finrank ℝ E),
            ‖iteratedFDerivWithin ℝ i (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              dMf (I := I) (M := M) D h j y c af) Uz z‖ ≤ C2 * K := by
          intro af
          refine norm_iteratedFDerivWithin_le_pi (A := C2 * K) (mul_nonneg hC2nn hK.le)
            hUz_open.uniqueDiffOn hzUz ?_ ?_
          · exact (contDiffAt_pi.mp hc_sm af).contDiffWithinAt
          · intro bf
            have hpd := hC2 (fun y : Fin (Module.finrank ℝ E) → ℝ => D.mat j h af bf y) z c K hK.le
              (Mf_contDiffAt_of_target (I := I) (M := M) D h hsmooth j af bf (D.htarget j z hz))
              (fun mm hmm γ => hjet j mm hmm γ z af bf hz) i (by omega)
            rw [show iteratedFDerivWithin ℝ i (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  dMf (I := I) (M := M) D h j y c af bf) Uz z
                = iteratedFDeriv ℝ i (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  dMf (I := I) (M := M) D h j y c af bf) z from
              iteratedFDerivWithin_of_isOpen i hUz_open hzUz]
            exact hpd
        refine norm_iteratedFDerivWithin_le_pi (A := C2 * K) (mul_nonneg hC2nn hK.le)
          hUz_open.uniqueDiffOn hzUz ?_ hinner3
        exact hc_sm.contDiffWithinAt
      refine norm_iteratedFDerivWithin_le_pi (A := C2 * K) (mul_nonneg hC2nn hK.le)
        hUz_open.uniqueDiffOn hzUz ?_ hinner2
      exact hdMf_sm.contDiffWithinAt
    have hD : ∀ i : ℕ, 1 ≤ i → i ≤ m →
        ‖iteratedFDerivWithin ℝ i F Uz z‖ ≤ D0 ^ i := by
      intro i hi1 him
      have hik : i ≤ k := le_trans him hm
      have hid : ‖iteratedFDerivWithin ℝ i (fun y : Fin (Module.finrank ℝ E) → ℝ => y) Uz z‖
          ≤ D0 ^ i := by
        have hid0 := norm_iteratedFDeriv_id_le_one hi1 z
        rw [show iteratedFDerivWithin ℝ i (fun y : Fin (Module.finrank ℝ E) → ℝ => y) Uz z
              = iteratedFDeriv ℝ i (fun y : Fin (Module.finrank ℝ E) → ℝ => y) z from
            iteratedFDerivWithin_of_isOpen i hUz_open hzUz]
        exact le_trans hid0 (one_le_pow₀ hD0ge1)
      have h2 := hMf_bound i hik
      have h3 := hdMf_bound i hik
      have hbd2 : C1 * K ≤ D0 ^ i := le_trans hD0geC1 (le_self_pow₀ hD0ge1 (by omega : i ≠ 0))
      have hbd3 : C2 * K ≤ D0 ^ i := le_trans hD0geC2 (le_self_pow₀ hD0ge1 (by omega : i ≠ 0))
      have hid' : ‖iteratedFDerivWithin ℝ i (fun y : Fin (Module.finrank ℝ E) → ℝ => y) Uz z‖
          ≤ D0 ^ i := hid
      have h2' : ‖iteratedFDerivWithin ℝ i (fun y : Fin (Module.finrank ℝ E) → ℝ => Mf (I := I) (M := M) D h j y)
          Uz z‖ ≤ D0 ^ i := le_trans h2 hbd2
      have h3' : ‖iteratedFDerivWithin ℝ i (fun y : Fin (Module.finrank ℝ E) → ℝ => dMf (I := I) (M := M) D h j y)
          Uz z‖ ≤ D0 ^ i := le_trans h3 hbd3
      have htuple := norm_iteratedFDerivWithin_le_tuple3
        (F₁ := fun y : Fin (Module.finrank ℝ E) → ℝ => y)
        (F₂ := fun y : Fin (Module.finrank ℝ E) → ℝ => Mf (I := I) (M := M) D h j y)
        (F₃ := fun y : Fin (Module.finrank ℝ E) → ℝ => dMf (I := I) (M := M) D h j y)
        (A := D0 ^ i) (pow_nonneg hD0nn i) hUz_open.uniqueDiffOn hzUz
        (by simpa only [hFdef] using hF_smooth.contDiffWithinAt hzUz) hid' h2' h3'
      simpa only [hFdef] using htuple
    have hCcont : ContDiffOn ℝ (⊤ : ℕ∞) (nresC (I := I) (M := M) D j a b)
        (lowJetDom (I := I) (M := M) D j) :=
      nresC_contDiffOn (I := I) (M := M) D j a b
    have hcomp := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (n := m) (N := (⊤ : ℕ∞))
      (g := nresC (I := I) (M := M) D j a b) (f := F)
      (s := Uz) (t := lowJetDom (I := I) (M := M) D j) (x := z)
      (C := Co j) (D := D0) hCcont hF_smooth (by simp : ((m : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞))
      (isOpen_lowJetDom (I := I) (M := M) D j).uniqueDiffOn hUz_open.uniqueDiffOn
      hMapsTo hzUz hC hD
    obtain ⟨φ, r, hφsm, hφnn, hrpos, hφ1, hφsup⟩ := exists_bump_subset hUz_open hzUz
    have hGlob_sm : ContDiff ℝ (⊤ : ℕ∞)
        (fun y : Fin (Module.finrank ℝ E) → ℝ => ((φ y : ℝ) : ℂ) * (nresC (I := I) (M := M) D j a b (F y))) :=
      contDiff_mul_of_contDiffOn hφsm (hCcont.comp hF_smooth hMapsTo) hUz_open hφsup
    have hevφ : ∀ᶠ y in nhds z, φ y = 1 := by
      filter_upwards [Metric.ball_mem_nhds z hrpos] with y hy
      refine hφ1 y (le_of_lt ?_)
      rwa [Metric.mem_ball, dist_eq_norm] at hy
    have hevG : (fun y : Fin (Module.finrank ℝ E) → ℝ => ((residualLow (I := I) (M := M) D h j y a b : ℝ) : ℂ))
        =ᶠ[nhds z] (fun y => ((φ y : ℝ) : ℂ) * (nresC (I := I) (M := M) D j a b (F y))) := by
      filter_upwards [hevφ, hUz_open.mem_nhds hzUz] with y hyφ hyU
      have hyid : residualLow (I := I) (M := M) D h j y a b
          = nres (I := I) (M := M) D j y (Mf (I := I) (M := M) D h j y)
              (dMf (I := I) (M := M) D h j y) a b :=
        residualLow_eq_nres_of_target (I := I) (M := M) D h hsmooth j
          ((hmem_iff y).mp hyU).1 ((hmem_iff y).mp hyU).2.1 a b
      rw [hyφ, hyid]
      simp only [Complex.ofReal_one, one_mul, hFdef, nresC]
    have hev2 : (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          ((φ y : ℝ) : ℂ) * (nresC (I := I) (M := M) D j a b (F y)))
        =ᶠ[nhds z] (fun y : Fin (Module.finrank ℝ E) → ℝ =>
          nresC (I := I) (M := M) D j a b (F y)) := by
      filter_upwards [hevφ] with y hy
      rw [hy]
      simp
    calc ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((residualLow (I := I) (M := M) D h j y a b : ℝ) : ℂ)) z‖
        = ‖Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((φ y : ℝ) : ℂ) * (nresC (I := I) (M := M) D j a b (F y))) z‖ :=
          congrArg (fun x : ℂ => ‖x‖) (pdVec_congr_germ hevG m β)
      _ = ‖iteratedFDeriv ℝ m (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((φ y : ℝ) : ℂ) * (nresC (I := I) (M := M) D j a b (F y))) z
              (fun i => Pi.single (β i) 1)‖ := by
          rw [Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv m _ hGlob_sm z β]
      _ ≤ ‖iteratedFDeriv ℝ m (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            ((φ y : ℝ) : ℂ) * (nresC (I := I) (M := M) D j a b (F y))) z‖ := by
          refine ContinuousMultilinearMap.le_opNorm _ _
            |>.trans_eq ?_
          rw [Finset.prod_eq_one (fun i _ => ?_), mul_one]
          simp [Pi.norm_single]
      _ = ‖iteratedFDeriv ℝ m (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            nresC (I := I) (M := M) D j a b (F y)) z‖ := by
          rw [(Filter.EventuallyEq.iteratedFDeriv (𝕜 := ℝ) hev2 m).eq_of_nhds]
      _ = ‖iteratedFDerivWithin ℝ m (fun y : Fin (Module.finrank ℝ E) → ℝ =>
            nresC (I := I) (M := M) D j a b (F y)) Uz z‖ := by
          rw [iteratedFDerivWithin_of_isOpen m hUz_open hzUz]
      _ ≤ (m.factorial : ℝ) * Co j * D0 ^ m := hcomp
      _ ≤ ∑ j' : ι₀, ∑ m' ∈ Finset.range (k + 1), (m'.factorial : ℝ) * Co j' * D0 ^ m' := by
        have hterm : (m.factorial : ℝ) * Co j * D0 ^ m ≤
            ∑ m' ∈ Finset.range (k + 1), (m'.factorial : ℝ) * Co j * D0 ^ m' :=
          Finset.single_le_sum (fun m' _ => mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCo0 j))
            (pow_nonneg hD0nn m')) (Finset.mem_range.mpr (by omega))
        have hsum : (∑ m' ∈ Finset.range (k + 1), (m'.factorial : ℝ) * Co j * D0 ^ m') ≤
            ∑ j' : ι₀, ∑ m' ∈ Finset.range (k + 1), (m'.factorial : ℝ) * Co j' * D0 ^ m' :=
          Finset.single_le_sum
            (f := fun j' => ∑ m' ∈ Finset.range (k + 1),
              (m'.factorial : ℝ) * Co j' * D0 ^ m')
            (fun j' _ => Finset.sum_nonneg (fun m' _ =>
              mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hCo0 j')) (pow_nonneg hD0nn m')))
            (Finset.mem_univ j)
        exact le_trans hterm hsum

end Work.Diff.STE.B3
