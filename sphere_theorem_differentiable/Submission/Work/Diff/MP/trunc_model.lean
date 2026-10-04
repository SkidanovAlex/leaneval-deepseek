import Mathlib
import Submission.Work.Diff.MP.TruncDefs
import Submission.Work.Diff.MP.Basic
import Submission.Work.Diff.MP.Defs
import Submission.Work.Diff.MP.TruncKit
import Submission.Work.Diff.MP.LM_aux
import Submission.Work.Diff.MP.SqrtC
import Submission.Work.Diff.GE.uhlenbeck_defs
import Submission.Work.Diff.GE.matrix_sqrt_family_kit
import Submission.Work.Diff.GE.uhlenbeck_frame_kit
import Submission.Work.Diff.GE.rmP_jointSmoothNoCompact
import Submission.Work.Diff.EXT.contMDiffAt_metric_pairing
import Submission.Work.Diff.GE.curvbasic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The truncated (local) maximum principle

The main target of this file is `Work.Diff.MP.trunc_model`; the matrix-square-root machinery
(`sqrtC`, `sqrtC_orthogonal`) and the two-sided tube lemma live in
`Submission.Work.Diff.MP.SqrtC`.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology Matrix
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Filter

set_option maxHeartbeats 8000000

namespace Work.Diff.MP

/-! ## Helper lemmas for the chart regularity of the frame family

Properties (2) and (3) of `trunc_model` are proved by working in the chart `extChartAt I x` at the
base point.  The lemmas below are the general (chart-independent) ingredients: the chart lift of a
jointly smooth scalar function, the uniform first-order expansion in the `frobDist` metric, the
`C^1`-regularity of `sqrtC ∘ Ring.inverse` at `1`, and the identification of the time-derivative of
the `sqrtC`-inverse-square-root of the metric matrix with the Ricci matrix. -/

/-- **Chart lift.**  If `Φ : ℝ × M → ℝ` is jointly `C^∞` at `(t, x)`, then its representative in the
chart at `x` is `C^∞` at `(t, extChartAt I x x)`. -/
theorem chart_lift_contDiffAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
    {Φ : ℝ × M → ℝ} {t : ℝ} {x : M}
    (hΦ : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ Φ (t, x)) :
    ContDiffAt ℝ ∞ (fun p : ℝ × E => Φ (p.1, (extChartAt I x).symm p.2))
      (t, (extChartAt I x) x) := by
  set c : E → M := fun u => (extChartAt I x).symm u with hc
  set u₀ : E := (extChartAt I x) x with hu₀
  have hcu : c u₀ = x := by
    rw [hc, hu₀]
    exact (extChartAt I x).left_inv (mem_extChartAt_source x)
  have hc_smooth : ContMDiffAt 𝓘(ℝ, E) I ∞ c u₀ := by
    have h := contMDiffWithinAt_extChartAt_symm_range_self (I := I) (x := x) (n := ∞)
    rw [ModelWithCorners.Boundaryless.range_eq_univ, contMDiffWithinAt_univ] at h
    simpa only [hc, hu₀] using h
  have hσ : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × E => (p.1, c p.2)) (t, u₀) :=
    contMDiffAt_fst.prodMk (hc_smooth.comp (t, u₀) contMDiffAt_snd)
  have hpt : (fun p : ℝ × E => (p.1, c p.2)) (t, u₀) = (t, x) := by
    show (t, c u₀) = (t, x)
    rw [hcu]
  have hΨm : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × E => Φ (p.1, c p.2)) (t, u₀) :=
    ContMDiffAt.comp_of_eq hΦ hσ hpt
  have h' : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × E => Φ (p.1, c p.2)) (t, u₀) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hΨm
  have hfin := contMDiffAt_iff_contDiffAt.mp h'
  simpa only [hc, hu₀] using hfin

/-- The Frobenius norm is bounded by the `ℓ^∞`-operator-size constant times the instance norm. -/
theorem frobNorm_le_max_mul_norm (n : ℕ) (R : Curv4 n) :
    frobNorm R ≤ max 1 ((n : ℝ) ^ 2) * ‖R‖ :=
  calc frobNorm R ≤ (n : ℝ) ^ 2 * ‖R‖ := frobNorm_le_mul_norm R
    _ ≤ max 1 ((n : ℝ) ^ 2) * ‖R‖ :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg R)

/-- **Uniform first-order expansion in the Frobenius metric.**  For a `C^1` function `Ψ` on
`ℝ × E`, the one-step expansion `Ψ(t+h,z) ≈ Ψ(t,z) + h·∂₁Ψ(t,z)` holds uniformly on a compact set
`K`, in the sense of `frobDist`. -/
theorem frob_uniform_expansion
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    {Ψ : ℝ × E → Curv4 n} {t e : ℝ} (he : 0 < e) {K : Set E} (hK : IsCompact K)
    (hΨ : ∀ p ∈ Set.prod (Set.Icc t (t + e)) K, ContDiffAt ℝ 1 Ψ p) :
    ∀ ε' > 0, ∃ δ' > 0, δ' ≤ e ∧ ∀ h : ℝ, 0 < h → h ≤ δ' → ∀ z ∈ K,
      frobDist (Ψ (t + h, z))
        (Ψ (t, z) + h • ((fderiv ℝ Ψ (t, z)) (1, 0))) ≤ ε' * h := by
  intro ε' hε'
  set C : ℝ := max 1 ((n : ℝ) ^ 2) with hC
  have hCpos : 0 < C := lt_of_lt_of_le one_pos (le_max_left _ _)
  set dF : ℝ → E → Curv4 n := fun s z => (fderiv ℝ Ψ (s, z)) (1, 0) with hdFdef
  have hcont : ContinuousOn (fun p : ℝ × E => dF p.1 p.2)
      (Set.prod (Set.Icc t (t + e)) K) := by
    have h1 : ContinuousOn (fun p : ℝ × E => fderiv ℝ Ψ p)
        (Set.prod (Set.Icc t (t + e)) K) := by
      intro p hp
      exact ((hΨ p hp).continuousAt_fderiv (by norm_num)).continuousWithinAt
    have h2 : ContinuousOn (fun p : ℝ × E => (fderiv ℝ Ψ p) (1, 0))
        (Set.prod (Set.Icc t (t + e)) K) :=
      h1.clm_apply continuousOn_const
    rw [hdFdef]
    exact h2
  have hderiv : ∀ z ∈ K, ∀ s ∈ Set.Ico t (t + e),
      HasDerivAt (fun s' : ℝ => Ψ (s', z)) (dF s z) s := by
    intro z hz s hs
    have hp : (s, z) ∈ Set.prod (Set.Icc t (t + e)) K := ⟨⟨hs.1, le_of_lt hs.2⟩, hz⟩
    have hd : DifferentiableAt ℝ Ψ (s, z) := (hΨ (s, z) hp).differentiableAt (by norm_num)
    have hc : HasFDerivAt (fun s' : ℝ => (s', z)) (ContinuousLinearMap.inl ℝ ℝ E) s :=
      hasFDerivAt_prodMk_left (𝕜 := ℝ) s z
    have h3 : HasDerivAt (fun s' : ℝ => Ψ (s', z))
        (((fderiv ℝ Ψ (s, z)).comp (ContinuousLinearMap.inl ℝ ℝ E)) 1) s :=
      (hd.hasFDerivAt.comp s hc).hasDerivAt
    rw [hdFdef]
    convert h3 using 1
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply]
  have hdF : ∀ ε > 0, ∃ η > 0, ∀ z ∈ K, ∀ s ∈ Set.Icc t (t + e),
      |s - t| < η → ‖dF s z - dF t z‖ ≤ ε :=
    Work.Diff.MP.LM.LM_uniform_slice (K := K) hK dF he.le hcont
  obtain ⟨δ', hδ'pos, hδ'e, hmain⟩ :=
    Work.Diff.MP.LM.LM_uniform_expansion (K := K) hK (fun s z => Ψ (s, z)) dF he
      hderiv hdF (ε' / C) (div_pos hε' hCpos)
  refine ⟨δ', hδ'pos, hδ'e, fun h hh hh' z hz => ?_⟩
  have h1 : ‖Ψ (t + h, z) - (Ψ (t, z) + h • dF t z)‖ ≤ ε' / C * h := hmain h hh hh' z hz
  have h2 : frobNorm (Ψ (t + h, z) - (Ψ (t, z) + h • ((fderiv ℝ Ψ (t, z)) (1, 0)))) ≤ ε' * h := by
    have hnorm := frobNorm_le_max_mul_norm n
      (Ψ (t + h, z) - (Ψ (t, z) + h • ((fderiv ℝ Ψ (t, z)) (1, 0))))
    rw [← hC] at hnorm
    have h3 : ‖Ψ (t + h, z) - (Ψ (t, z) + h • ((fderiv ℝ Ψ (t, z)) (1, 0)))‖ ≤ ε' / C * h := by
      rw [hdFdef] at h1
      exact h1
    have h4 : C * ‖Ψ (t + h, z) - (Ψ (t, z) + h • ((fderiv ℝ Ψ (t, z)) (1, 0)))‖
        ≤ C * (ε' / C * h) := mul_le_mul_of_nonneg_left h3 hCpos.le
    have h5 : C * (ε' / C * h) = ε' * h := by field_simp
    linarith [hnorm, h4, h5]
  simpa only [frobDist] using h2

/-- **`sqrtC ∘ Ring.inverse` is `C^1`.** -/
theorem contDiffAt_sqrtC_inverse {n : ℕ} {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {A : X → Matrix (Fin n) (Fin n) ℝ} {p₀ : X}
    (hA : ContDiffAt ℝ 1 A p₀) (hA1 : A p₀ = 1) :
    ContDiffAt ℝ 1 (fun p => sqrtC n (Ring.inverse (A p))) p₀ := by
  have hone : Ring.inverse (A p₀) = (1 : Matrix (Fin n) (Fin n) ℝ) := by
    rw [hA1, Ring.inverse_one]
  have hbase : ContDiffAt ℝ 1
      (Ring.inverse : Matrix (Fin n) (Fin n) ℝ → Matrix (Fin n) (Fin n) ℝ) (A p₀) := by
    rw [hA1]
    simpa using (contDiffAt_ringInverse (𝕜 := ℝ) (n := (1 : ℕ∞ω))
      (1 : (Matrix (Fin n) (Fin n) ℝ)ˣ))
  have h1 : ContDiffAt ℝ 1 (fun p => Ring.inverse (A p)) p₀ := hbase.comp p₀ hA
  have hsq : ContDiffAt ℝ 1 (sqrtC n) (Ring.inverse (A p₀)) := by
    rw [hone]
    exact sqrtC_contDiffAt n
  exact hsq.comp p₀ h1

/-- **The time-derivative of `sqrtC (Ring.inverse (metricMat ·))` at the base time is the Ricci
matrix.** -/
theorem sqrtC_metricMat_hasDerivWithinAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
    (G : ℝ → SMet I M) (T : ℝ) (hflow : IsRicciFlow G T)
    (t : ℝ) (ht : t ∈ Set.Ico 0 T) (x : M)
    (u : Fin (Module.finrank ℝ E) → TangentSpace I x) (hu : IsONFrame (G t) x u) :
    HasDerivWithinAt
      (fun s : ℝ => sqrtC (Module.finrank ℝ E)
        (Ring.inverse (Work.Diff.GE.metricMat G x u s)))
      (Work.Diff.GE.ricMat (G t) x u) (Set.Ico 0 T) t := by
  have hM : Work.Diff.GE.metricMat G x u t = 1 := Work.Diff.GE.metricMat_eq_one G x u t hu
  have hdiff : HasDerivWithinAt (Work.Diff.GE.metricMat G x u)
      ((-2 : ℝ) • Work.Diff.GE.ricMat (G t) x u) (Set.Ico 0 T) t :=
    Work.Diff.GE.metricMat_hasDerivWithinAt G T hflow t ht x u
  have h := (Work.Diff.GE.sqrt_family_abstract
      (𝔸 := Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
      (Work.Diff.GE.metricMat G x u) ((-2 : ℝ) • Work.Diff.GE.ricMat (G t) x u) t T
      hM hdiff).2.2.2
  have hfun : (fun s : ℝ => Work.Diff.GE.sqrtNear
        (𝔸 := Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)
        (Ring.inverse (Work.Diff.GE.metricMat G x u s)))
      = (fun s : ℝ => sqrtC (Module.finrank ℝ E)
        (Ring.inverse (Work.Diff.GE.metricMat G x u s))) := by
    funext s
    exact (sqrtC_eq_sqrtNear_apply (Module.finrank ℝ E)
      (Ring.inverse (Work.Diff.GE.metricMat G x u s))).symm
  rw [hfun] at h
  have hderiv_eq : (-(1 / 2) : ℝ) • ((-2 : ℝ) • Work.Diff.GE.ricMat (G t) x u)
      = Work.Diff.GE.ricMat (G t) x u := by
    rw [smul_smul]
    norm_num
  rwa [hderiv_eq] at h

/-- The level comparison `1 ≤ ∞`. -/
theorem one_le_infty_lev : (1 : ℕ∞ω) ≤ ∞ := by
  exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)

/-- **Chart lift at an evaluation point.**  If `Φ : ℝ × M → ℝ` is jointly `C^∞` at `(t, y)` and `y`
lies in the chart at `x`, then its representative in the chart at `x` is `C^∞` at `(t, χ y)`. -/
theorem chart_lift_contDiffAt_at
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [I.Boundaryless]
    {Φ : ℝ × M → ℝ} {t : ℝ} {x y : M} (hy : y ∈ (chartAt H x).source)
    (hΦ : ContMDiffAt (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ Φ (t, y)) :
    ContDiffAt ℝ ∞ (fun p : ℝ × E => Φ (p.1, (extChartAt I x).symm p.2))
      (t, (extChartAt I x) y) := by
  set c : E → M := fun u => (extChartAt I x).symm u with hc
  have hysrc : y ∈ (extChartAt I x).source := by rwa [extChartAt_source]
  have hcy : (extChartAt I x) y ∈ (extChartAt I x).target :=
    (extChartAt I x).map_source hysrc
  have hcs : ContMDiffAt 𝓘(ℝ, E) I ∞ c ((extChartAt I x) y) :=
    (contMDiffOn_extChartAt_symm (I := I) (x := x) (n := ∞)).contMDiffAt
      ((isOpen_extChartAt_target (I := I) x).mem_nhds hcy)
  have hσ : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) (𝓘(ℝ, ℝ).prod I) ∞
      (fun p : ℝ × E => (p.1, c p.2)) (t, (extChartAt I x) y) :=
    contMDiffAt_fst.prodMk (hcs.comp (t, (extChartAt I x) y) contMDiffAt_snd)
  have hpt : (fun p : ℝ × E => (p.1, c p.2)) (t, (extChartAt I x) y) = (t, y) := by
    show (t, c ((extChartAt I x) y)) = (t, y)
    rw [hc]
    exact Prod.ext rfl ((extChartAt I x).left_inv hysrc)
  have hΨm : ContMDiffAt (𝓘(ℝ, ℝ).prod 𝓘(ℝ, E)) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × E => Φ (p.1, c p.2)) (t, (extChartAt I x) y) :=
    ContMDiffAt.comp_of_eq hΦ hσ hpt
  have h' : ContMDiffAt 𝓘(ℝ, ℝ × E) 𝓘(ℝ, ℝ) ∞
      (fun p : ℝ × E => Φ (p.1, c p.2)) (t, (extChartAt I x) y) := by
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod]
    exact hΨm
  have hfin := contMDiffAt_iff_contDiffAt.mp h'
  simpa only [hc] using hfin

/-- Hamilton's quadratic term `Q` is continuous. -/
theorem continuous_Q (n : ℕ) : Continuous (Submission.Diff.Alg.Q : Curv4 n → Curv4 n) := by
  unfold Submission.Diff.Alg.Q
  fun_prop

theorem trunc_model
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M] [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) (hCE : Submission.Diff.CurvEvolution I M)
    (hLP : Submission.Diff.LapRmFrameParallel I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    {F : ℝ → Set (Submission.Diff.Alg.Curv4 (Module.finrank ℝ E))}
    (hF : Submission.Diff.Alg.IsInvariantFamily F)
    {ρ₁ ϱ Λ ε : ℝ} (hρ₁ : ∀ s ∈ Set.Ico 0 T, ∀ x : M,
      Work.Diff.MP.frobNorm (Submission.Diff.rmC (G s) x) ≤ ρ₁)
    (hϱ : 0 < ϱ) (hρϱ : ρ₁ + 1 ≤ ϱ) (hΛ : 0 < Λ) (hε : 0 < ε) (hεΛ : ε ≤ 1 / (2 * Λ))
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτT : τ < T) (hεT : τ + ε ≤ T)
    {C : ℝ} (hC : 0 ≤ C)
    (hQlip : ∀ R S : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E),
      Work.Diff.MP.frobNorm R ≤ 2 * ϱ → Work.Diff.MP.frobNorm S ≤ 2 * ϱ →
      Work.Diff.MP.frobDist (Submission.Diff.Alg.Q R) (Submission.Diff.Alg.Q S)
        ≤ C * Work.Diff.MP.frobDist R S) :
    ∀ t ∈ Set.Ioo τ (τ + ε), ∀ x : M,
      ∃ (δ : ℝ) (_ : 0 < δ) (_ : t + δ ≤ T) (U : Set M) (_ : U ∈ nhds x)
        (Rl dRl : ℝ → M → Submission.Diff.Alg.Curv4 (Module.finrank ℝ E)),
        (∀ s ∈ Set.Icc t (t + δ), ∀ y ∈ U,
          Work.Diff.MP.truncDist G F (fun s => Work.Diff.MP.growRad ϱ Λ (s - τ)) s y
            = Work.Diff.MP.frobInfDist (Rl s y) (Work.Diff.MP.truncFam F ϱ Λ τ s)) ∧
        ContinuousOn (fun p : ℝ × M => (Rl p.1 p.2, dRl p.1 p.2))
          (Set.prod (Set.Icc t (t + δ)) U) ∧
        (∀ ε' > 0, ∃ δ' > 0, ∀ h : ℝ, 0 < h → h ≤ δ' → ∀ y ∈ U,
          Work.Diff.MP.frobDist (Rl (t + h) y)
            (Rl t y + h • (dRl t y + Submission.Diff.Alg.Q (Rl t y))) ≤ ε' * h) ∧
        (∀ ℓ : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E), Work.Diff.MP.frobNorm ℓ ≤ 1 →
          (∀ z ∈ U, Work.Diff.MP.frobDot ℓ (Rl t z) ≤ Work.Diff.MP.frobDot ℓ (Rl t x)) →
          Work.Diff.MP.frobDot ℓ (dRl t x) ≤ 0) ∧
        (∀ y ∈ U, ∀ S ∈ Work.Diff.MP.truncFam F ϱ Λ τ t,
          Work.Diff.MP.frobDist (Submission.Diff.Alg.Q (Rl t y)) (Submission.Diff.Alg.Q S)
            ≤ C * Work.Diff.MP.frobDist (Rl t y) S) := by
  classical
  intro t ht x
  -- ## Basic facts about the time `t`
  have ht0 : 0 < t := lt_of_le_of_lt hτ0 ht.1
  have htT : t < T := lt_of_lt_of_le ht.2 hεT
  have htIco : t ∈ Set.Ico (0 : ℝ) T := ⟨le_of_lt ht0, htT⟩
  -- ## The reference orthonormal frame field, from the Laplacian contract
  obtain ⟨Ef, hEfx, hEfsm, hEfON, hLPid⟩ :=
    hLP (G t) x (onFrame (G t) x) (Work.Diff.GE.isONFrame_onFrame (G t) x)
  -- ## The square-root frame built from `Ef`
  let Γ : ℝ → M → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun s y i j => (G s).inner y (Ef i y) (Ef j y)
  let P : ℝ → M → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun s y => sqrtC (Module.finrank ℝ E) (Ring.inverse (Γ s y))
  let e : ℝ → Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y :=
    fun s i y => ∑ a, P s y a i • Ef a y
  let Rl : ℝ → M → Submission.Diff.Alg.Curv4 (Module.finrank ℝ E) :=
    fun s y => rmFrame (G s) y (fun i => e s i y)
  let dRl : ℝ → M → Submission.Diff.Alg.Curv4 (Module.finrank ℝ E) :=
    fun s y => deriv (fun σ : ℝ => Rl σ y) s - Submission.Diff.Alg.Q (Rl s y)
  -- ## A neighbourhood of `x` on which `Ef` is orthonormal for `G t`, inside the chart at `x`
  have hchnhds : (chartAt H x).source ∈ 𝓝 x :=
    (chartAt H x).open_source.mem_nhds (mem_chart_source H x)
  obtain ⟨U₀, hU₀sub, hU₀open, hxU₀⟩ := _root_.mem_nhds_iff.mp (Filter.inter_mem hEfON hchnhds)
  obtain ⟨U, hUc, hxintU, hUsubU₀⟩ := exists_compact_subset hU₀open hxU₀
  have hUx : U ∈ 𝓝 x :=
    Filter.mem_of_superset (isOpen_interior.mem_nhds hxintU) interior_subset
  have hxU : x ∈ U := interior_subset hxintU
  have hsource : ∀ y ∈ U, IsONFrame (G t) y (fun i => Ef i y) :=
    fun y hy => (hU₀sub (hUsubU₀ hy)).1
  have hUchart : ∀ y ∈ U, y ∈ (chartAt H x).source :=
    fun y hy => (hU₀sub (hUsubU₀ hy)).2
  have hΓty : ∀ y ∈ U, Γ t y = 1 := by
    intro y hy
    ext i j
    simpa [Γ, Matrix.one_apply] using hsource y hy i j
  -- ## The neighbourhood of `1` on which the square-root construction is `C¹` and orthogonalises
  obtain ⟨V₀, hV₀mem, hV₀orth⟩ := sqrtC_orthogonal (Module.finrank ℝ E)
  have hInvC1 : ContDiffAt ℝ 1 (Ring.inverse : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ → Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ) 1 :=
    contDiffAt_ringInverse (𝕜 := ℝ) (n := (1 : ℕ∞ω))
      (1 : (Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)ˣ)
  obtain ⟨u₁, hu₁mem, hu₁on⟩ := (contDiffWithinAt_iff_contDiffOn_nhds
    (n := (1 : ℕ∞ω)) (by norm_num)).mp hInvC1
  obtain ⟨v₁, hv₁sub, hv₁open, h1v₁⟩ := _root_.mem_nhds_iff.mp
    (by simpa [nhdsWithin_univ] using hu₁mem)
  have hv₁on : ContDiffOn ℝ 1 (Ring.inverse : Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ → Matrix (Fin (Module.finrank ℝ E))
      (Fin (Module.finrank ℝ E)) ℝ) v₁ := hu₁on.mono hv₁sub
  obtain ⟨u₂, hu₂mem, hu₂on⟩ := (contDiffWithinAt_iff_contDiffOn_nhds
    (n := (1 : ℕ∞ω)) (by norm_num)).mp (sqrtC_contDiffAt (Module.finrank ℝ E))
  obtain ⟨v₂, hv₂sub, hv₂open, h1v₂⟩ := _root_.mem_nhds_iff.mp
    (by simpa [nhdsWithin_univ] using hu₂mem)
  have hv₂on : ContDiffOn ℝ 1 (sqrtC (Module.finrank ℝ E)) v₂ := hu₂on.mono hv₂sub
  set V : Set (Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) :=
    V₀ ∩ v₁ ∩ (Ring.inverse ⁻¹' v₂) with hVdef
  have hVmem : V ∈ 𝓝 (1 : Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ) := by
    refine Filter.inter_mem (Filter.inter_mem hV₀mem ?_) ?_
    · exact hv₁open.mem_nhds h1v₁
    · exact (hasFDerivAt_ringInverse (𝕜 := ℝ)
        (1 : (Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ)ˣ)).continuousAt
        |>.preimage_mem_nhds (by simpa using hv₂open.mem_nhds h1v₂)
  obtain ⟨Vopen, hVopensub, hVopen_open, h1Vopen⟩ := _root_.mem_nhds_iff.mp hVmem
  -- ## Continuity of `Γ` on boxes inside `J × M`
  have hΓat : ∀ s ∈ Set.Ioo (t / 2) T, ∀ y : M,
      ContinuousAt (fun p : ℝ × M => Γ p.1 p.2) (s, y) := by
    intro s hs y
    change ContinuousAt (fun p : ℝ × M => fun (i : Fin (Module.finrank ℝ E)) =>
      fun (j : Fin (Module.finrank ℝ E)) => Γ p.1 p.2 i j) (s, y)
    have hJ : IsOpen (Set.Ioo (t / 2) T) := isOpen_Ioo
    have hGJ : Submission.Diff.JointSmooth G (Set.Ioo (t / 2) T) :=
      hflow.1.mono (fun p hp => ⟨⟨by linarith [hp.1.1, ht0], hp.1.2⟩, trivial⟩)
    rw [continuousAt_pi]
    intro i
    rw [continuousAt_pi]
    intro j
    have h := Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M) hJ hGJ hs
      (x := y) (Y := Ef i) (Z := Ef j) ((hEfsm i).contMDiffAt) ((hEfsm j).contMDiffAt)
    simpa only [Γ] using h.continuousAt
  -- ## The time window on which `Γ` lands in `V`
  set δ₁ : ℝ := min (t / 4) ((T - t) / 2) with hδ₁def
  have hδ₁pos : 0 < δ₁ := lt_min (by linarith) (by linarith)
  have hΓcont : ContinuousOn (fun p : ℝ × M => Γ p.1 p.2)
      (Set.Icc (t - δ₁) (t + δ₁) ×ˢ U) := by
    intro p hp
    have hp1 : p.1 ∈ Set.Ioo (t / 2) T := by
      have h1 := hp.1.1
      have h2 := hp.1.2
      rw [hδ₁def] at h1 h2
      exact ⟨by linarith [min_le_left (t / 4) ((T - t) / 2), h1, ht0],
        by linarith [min_le_right (t / 4) ((T - t) / 2), h2, htT]⟩
    exact (hΓat p.1 hp1 p.2).continuousWithinAt
  obtain ⟨η, hηpos, hη⟩ := exists_pos_forall_mem_of_isCompact_two
    (a := t - δ₁) (b := t + δ₁) (t := t) (f := fun s y => Γ s y)
    hVopen_open hUc (by linarith [hδ₁pos]) (by linarith [hδ₁pos]) hΓcont
    (fun y hy => by rw [hΓty y hy]; exact h1Vopen)
  -- ## The final `δ`
  set c : ℝ := 1 / 2 - Λ * (t - τ) with hcdef
  have hcpos : 0 < c := by
    have h1 : Λ * (t - τ) < Λ * ε := mul_lt_mul_of_pos_left (by linarith [ht.1, ht.2]) hΛ
    have h2 : Λ * ε ≤ 1 / 2 := by
      calc Λ * ε ≤ Λ * (1 / (2 * Λ)) := mul_le_mul_of_nonneg_left hεΛ (le_of_lt hΛ)
        _ = 1 / 2 := by field_simp
    rw [hcdef]; linarith
  set δ : ℝ := min (η / 2) (min (δ₁ / 4) (min (c / Λ) ((T - t) / 2))) with hδdef
  have hδpos : 0 < δ :=
    lt_min (by linarith) (lt_min (by linarith) (lt_min (div_pos hcpos hΛ) (by linarith)))
  have hδleη : δ ≤ η := le_trans (min_le_left _ _) (by linarith)
  have hδleη2 : δ ≤ η / 2 := min_le_left _ _
  have hδle₁ : δ ≤ δ₁ := le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (by linarith))
  have hδle₁4 : δ ≤ δ₁ / 4 := le_trans (min_le_right _ _) (min_le_left _ _)
  have hδlec : δ ≤ c / Λ := le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδT : t + δ ≤ T := by
    have h : δ ≤ (T - t) / 2 :=
      le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    linarith
  -- on the box the metric matrix lies in `V`
  have hΓV : ∀ s ∈ Set.Icc t (t + δ), ∀ y ∈ U, Γ s y ∈ V := by
    intro s hs y hy
    have hsI : s ∈ Set.Icc (t - δ₁) (t + δ₁) :=
      ⟨by linarith [hs.1, hδ₁pos], by linarith [hs.2, hδle₁]⟩
    have hst : |s - t| ≤ η := by
      rw [abs_of_nonneg (by linarith [hs.1])]
      linarith [hs.2, hδleη]
    exact hVopensub (hη s hsI hst y hy)
  have hΓV2 : ∀ σ ∈ Set.Icc (t - δ₁) (t + δ₁), |σ - t| ≤ η → ∀ y ∈ U, Γ σ y ∈ V :=
    fun σ hσ hst y hy => hVopensub (hη σ hσ hst y hy)
  -- ## The frame is orthonormal
  have hΓsymm : ∀ s y, Matrix.transpose (Γ s y) = Γ s y := by
    intro s y
    ext a b
    show Γ s y b a = Γ s y a b
    simp only [Γ]
    exact ((G s).symm y (Ef a y) (Ef b y)).symm
  have hON_general : ∀ s y, Γ s y ∈ V → Submission.Diff.IsONFrame (G s) y (fun i => e s i y) := by
    intro s y hVsz
    have hkey : Matrix.transpose (P s y) * Γ s y * P s y = 1 :=
      hV₀orth (Γ s y) hVsz.1.1 (hΓsymm s y)
    intro a b
    show (G s).inner y (∑ i, P s y i a • Ef i y) (∑ j, P s y j b • Ef j y)
      = if a = b then 1 else 0
    have hL : (G s).inner y (∑ i, P s y i a • Ef i y) (∑ j, P s y j b • Ef j y)
        = ∑ i, ∑ j, P s y i a * P s y j b * Γ s y i j := by
      have hA : (G s).inner y (∑ i, P s y i a • Ef i y)
          = ∑ i, P s y i a • (G s).inner y (Ef i y) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
      have h2 : ∀ (w : TangentSpace I y),
          (G s).inner y (∑ i, P s y i a • Ef i y) w
            = ∑ i, P s y i a * (G s).inner y (Ef i y) w := by
        intro w
        rw [hA, ContinuousLinearMap.sum_apply]
        exact Finset.sum_congr rfl fun i _ =>
          by rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
      have h3 : ∀ (i : Fin (Module.finrank ℝ E)),
          (G s).inner y (Ef i y) (∑ j, P s y j b • Ef j y)
            = ∑ j, P s y j b * (G s).inner y (Ef i y) (Ef j y) := by
        intro i
        rw [map_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]
      simp only [h2, h3, Γ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    have hR : (Matrix.transpose (P s y) * Γ s y * P s y) a b
        = ∑ i, ∑ j, P s y i a * P s y j b * Γ s y i j := by
      rw [Matrix.mul_apply]
      have hstep : ∀ c, (Matrix.transpose (P s y) * Γ s y) a c
          = ∑ b, P s y b a * Γ s y b c := by
        intro c
        rw [Matrix.mul_apply]
        exact Finset.sum_congr rfl fun b _ => by rw [Matrix.transpose_apply]
      simp only [hstep, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [hL, ← hR, hkey, Matrix.one_apply]
  have hON : ∀ s ∈ Set.Icc t (t + δ), ∀ y ∈ U,
      Submission.Diff.IsONFrame (G s) y (fun i => e s i y) :=
    fun s hs y hy => hON_general s y (hΓV s hs y hy)
  have hON2 : ∀ σ ∈ Set.Icc (t - δ₁) (t + δ₁), |σ - t| ≤ η → ∀ y ∈ U,
      Submission.Diff.IsONFrame (G σ) y (fun i => e σ i y) :=
    fun σ hσ hst y hy => hON_general σ y (hΓV2 σ hσ hst y hy)
  -- ## The frame at time `t` is `Ef`
  have het : ∀ y ∈ U, ∀ i, e t i y = Ef i y := by
    intro y hy i
    have h1 : P t y = 1 := by
      show sqrtC (Module.finrank ℝ E) (Ring.inverse (Γ t y)) = 1
      rw [hΓty y hy, Ring.inverse_one, sqrtC_one]
    show (∑ a, P t y a i • Ef a y) = Ef i y
    rw [h1]
    simp [Matrix.one_apply]
  -- ## Property (1): the distance is computed in this frame
  have hdist : ∀ s ∈ Set.Icc t (t + δ), ∀ y ∈ U,
      Work.Diff.MP.truncDist G F (fun s => Work.Diff.MP.growRad ϱ Λ (s - τ)) s y
        = Work.Diff.MP.frobInfDist (Rl s y) (Work.Diff.MP.truncFam F ϱ Λ τ s) := by
    intro s hs y hy
    have hrot : ∀ A ∈ Matrix.orthogonalGroup (Fin (Module.finrank ℝ E)) ℝ,
        ∀ R ∈ F s ∩ Work.Diff.MP.frobBall (Work.Diff.MP.growRad ϱ Λ (s - τ)),
        Submission.Diff.Alg.rot A R ∈ F s ∩ Work.Diff.MP.frobBall (Work.Diff.MP.growRad ϱ Λ (s - τ)) :=
      fun A hA R hR =>
        ⟨hF.2.2.2.1 s A hA R hR.1, (Work.Diff.MP.mem_frobBall_rot A hA).mpr hR.2⟩
    show frobInfDist (Submission.Diff.rmC (G s) y)
        (F s ∩ Work.Diff.MP.frobBall (Work.Diff.MP.growRad ϱ Λ (s - τ)))
      = frobInfDist (rmFrame (G s) y (fun i => e s i y))
        (F s ∩ Work.Diff.MP.frobBall (Work.Diff.MP.growRad ϱ Λ (s - τ)))
    exact (Work.Diff.MP.frobInfDist_rmFrame_eq (I := I) (M := M) hLC (G s) y _
      hrot (fun i => e s i y) (hON s hs y hy)).symm
  -- ## Property (5): the `Q`-Lipschitz bound
  have hQbound : ∀ y ∈ U, ∀ S ∈ Work.Diff.MP.truncFam F ϱ Λ τ t,
      Work.Diff.MP.frobDist (Submission.Diff.Alg.Q (Rl t y)) (Submission.Diff.Alg.Q S)
        ≤ C * Work.Diff.MP.frobDist (Rl t y) S := by
    intro y hy S hS
    have ht_box : t ∈ Set.Icc t (t + δ) := ⟨le_rfl, by linarith [hδpos]⟩
    have hONty := hON t ht_box y hy
    have hnormR : Work.Diff.MP.frobNorm (Rl t y)
        = Work.Diff.MP.frobNorm (Submission.Diff.rmC (G t) y) := by
      obtain ⟨A, hA, hAe⟩ := Work.Diff.GE.onFrame_orthogonal_change (G t) y (onFrame (G t) y)
        (fun i => e t i y) (Work.Diff.GE.isONFrame_onFrame (G t) y) hONty
      have hrot := Work.Diff.GE.rmFrame_eq_rot hLC (G t) y (onFrame (G t) y)
        (fun i => e t i y) A hAe
      show Work.Diff.MP.frobNorm (rmFrame (G t) y (fun i => e t i y)) = _
      rw [hrot, Work.Diff.MP.frobNorm_rot A hA]
      rfl
    have h1 : Work.Diff.MP.frobNorm (Rl t y) ≤ 2 * ϱ := by
      rw [hnormR]
      have h := hρ₁ t htIco y
      linarith
    have h2 : Work.Diff.MP.frobNorm S ≤ 2 * ϱ := by
      rw [Work.Diff.MP.truncFam_eq] at hS
      have hS' : Work.Diff.MP.frobNorm S ≤ Work.Diff.MP.growRad ϱ Λ (t - τ) :=
        Work.Diff.MP.frobBall_mem.mp hS.2
      have hgr : Work.Diff.MP.growRad ϱ Λ (t - τ) ≤ 2 * ϱ := by
        rw [Work.Diff.MP.growRad]
        have hden : (1 / 2 : ℝ) ≤ 1 - Λ * (t - τ) := by
          have hc := hcpos
          rw [hcdef] at hc
          linarith
        have hdenpos : 0 < 1 - Λ * (t - τ) := by linarith
        rw [div_le_iff₀ hdenpos]
        calc ϱ ≤ 2 * ϱ * (1 / 2 : ℝ) := by linarith
          _ ≤ 2 * ϱ * (1 - Λ * (t - τ)) := mul_le_mul_of_nonneg_left hden (by positivity)
      linarith
    exact hQlip (Rl t y) S h1 h2
  -- ## The time-derivative of `Rl · x` at `t`: the Uhlenbeck evolution at the base point
  --
  -- `CurvEvolution` (contract CE) computes the time-derivative of the curvature in any family of
  -- orthonormal frames whose velocity at `t` is the Ricci endomorphism.  The square-root frame
  -- `s ↦ e s x` has this property at `t` (its metric matrix is `1` there), so its curvature has
  -- derivative `lapRmFrame + Q` at `t`, and this is the value of `dRl t x`.
  obtain ⟨ufam, hufamON, hufamderiv⟩ :=
    Work.Diff.GE.uhlenbeck_frame_kit hLC G T hflow t htIco x
  set ρ : ℝ := min (η / 2) (δ₁ / 2) with hρdef
  have hρpos : 0 < ρ := lt_min (by linarith [hηpos]) (by linarith [hδ₁pos])
  have hρleη : ρ ≤ η := le_trans (min_le_left _ _) (by linarith)
  have hρleδ : ρ ≤ δ₁ := le_trans (min_le_right _ _) (by linarith)
  have htρ : t ∈ Set.Ioo (t - ρ) (t + ρ) := ⟨by linarith, by linarith⟩
  let eE : ℝ → Fin (Module.finrank ℝ E) → E := fun s i => (e s i x : E)
  let efam : ℝ → Fin (Module.finrank ℝ E) → E :=
    fun s i => if s ∈ Set.Ioo (t - ρ) (t + ρ) then eE s i else ufam s i
  have hefam_t : efam t = fun i => (Ef i x : TangentSpace I x) := by
    funext i
    show (if t ∈ Set.Ioo (t - ρ) (t + ρ) then eE t i else ufam t i) = (Ef i x : TangentSpace I x)
    by_cases h : t ∈ Set.Ioo (t - ρ) (t + ρ)
    · rw [if_pos h]
      exact het x hxU i
    · exact absurd htρ h
  -- the velocity of the square-root frame at the base time
  have hPderiv : HasDerivWithinAt (fun s : ℝ => P s x)
      (Work.Diff.GE.ricMat (G t) x (fun i => Ef i x)) (Set.Ico 0 T) t :=
    sqrtC_metricMat_hasDerivWithinAt G T hflow t htIco x (fun i => Ef i x) (hsource x hxU)
  have hvel : ∀ i, HasDerivWithinAt (fun s : ℝ => eE s i)
      ((∑ j, ricAt (lcOf (G t)) x (e t i x) (e t j x) • e t j x : TangentSpace I x) : E)
      (Set.Ico 0 T) t := by
    intro i
    have hentry : ∀ a b, HasDerivWithinAt (fun s : ℝ => P s x a b)
        (Work.Diff.GE.ricMat (G t) x (fun i => Ef i x) a b) (Set.Ico 0 T) t :=
      fun a b => Work.Diff.GE.hasDerivWithinAt_entry hPderiv a b
    have h1 := Work.Diff.GE.hasDerivWithinAt_frameFromMatrix (T := T) (t := t) (x := x)
      (u := fun i => Ef i x) hentry i
    have h2 : (∑ j, Work.Diff.GE.ricMat (G t) x (fun i => Ef i x) j i • Ef j x)
        = (∑ j, ricAt (lcOf (G t)) x (e t i x) (e t j x) • e t j x : TangentSpace I x) := by
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Work.Diff.GE.ricMat_apply, het x hxU i, het x hxU j,
        ← Work.Diff.GE.ricAt_symm_kit hLC (G t) x (Ef i x) (Ef j x)]
    rw [h2] at h1
    exact h1
  have hvel' : ∀ i, HasDerivAt (fun s : ℝ => efam s i)
      ((∑ j, ricAt (lcOf (G t)) x (efam t i) (efam t j) • efam t j : TangentSpace I x) : E) t := by
    intro i
    have hIco : Set.Ico (0 : ℝ) T ∈ 𝓝 t :=
      mem_of_superset (isOpen_Ioo.mem_nhds ⟨ht0, htT⟩) (fun x hx => ⟨hx.1.le, hx.2⟩)
    have hbase := (hvel i).hasDerivAt hIco
    have hev : (fun s : ℝ => efam s i) =ᶠ[𝓝 t] (fun s : ℝ => eE s i) := by
      filter_upwards [isOpen_Ioo.mem_nhds htρ] with s hs
      show (if s ∈ Set.Ioo (t - ρ) (t + ρ) then eE s i else ufam s i) = eE s i
      rw [if_pos hs]
    have hval1 : ((∑ j, ricAt (lcOf (G t)) x (efam t i) (efam t j) • efam t j : TangentSpace I x) : E)
        = ((∑ j, ricAt (lcOf (G t)) x (Ef i x) (Ef j x) • Ef j x : TangentSpace I x) : E) := by
      simp only [hefam_t]
      try rfl
    have hval2 : ((∑ j, ricAt (lcOf (G t)) x (e t i x) (e t j x) • e t j x : TangentSpace I x) : E)
        = ((∑ j, ricAt (lcOf (G t)) x (Ef i x) (Ef j x) • Ef j x : TangentSpace I x) : E) := by
      refine congrArg (fun v : TangentSpace I x => (v : E)) ?_
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [het x hxU i, het x hxU j]
    rw [hval2] at hbase
    rw [hval1]
    exact hbase.congr_of_eventuallyEq hev
  have hONefam : ∀ s ∈ Set.Ioo 0 T, Submission.Diff.IsONFrame (G s) x (efam s) := by
    intro s hs
    by_cases hcase : s ∈ Set.Ioo (t - ρ) (t + ρ)
    · have hsI : s ∈ Set.Icc (t - δ₁) (t + δ₁) :=
        ⟨by linarith [hcase.1, hρleδ], by linarith [hcase.2, hρleδ]⟩
      have hst : |s - t| ≤ η := by
        have h3 : |s - t| < ρ := by
          rw [abs_lt]
          exact ⟨by linarith [hcase.1], by linarith [hcase.2]⟩
        linarith [hρleη]
      have h := hON2 s hsI hst x hxU
      have hfun : efam s = fun i => e s i x := by
        funext i
        show (if s ∈ Set.Ioo (t - ρ) (t + ρ) then eE s i else ufam s i) = e s i x
        rw [if_pos hcase]
      rw [hfun]
      exact h
    · have h := hufamON s ⟨hs.1.le, hs.2⟩
      have hfun : efam s = fun i => ufam s i := by
        funext i
        show (if s ∈ Set.Ioo (t - ρ) (t + ρ) then eE s i else ufam s i) = ufam s i
        rw [if_neg hcase]
      rw [hfun]
      exact h
  have hevol := hCE G T hflow t ⟨ht0, htT⟩ x efam hONefam (fun i => hvel' i)
  have heveq : (fun s : ℝ => rmFrame (G s) x (efam s)) =ᶠ[𝓝 t] (fun s : ℝ => Rl s x) := by
    filter_upwards [isOpen_Ioo.mem_nhds htρ] with s hs
    show rmFrame (G s) x (efam s) = rmFrame (G s) x (fun i => e s i x)
    congr 1
    funext i
    show (if s ∈ Set.Ioo (t - ρ) (t + ρ) then eE s i else ufam s i) = e s i x
    rw [if_pos hs]
  have hslice : HasDerivAt (fun s : ℝ => Rl s x)
      (lapRmFrame (G t) x (fun i => Ef i x) + Submission.Diff.Alg.Q (Rl t x)) t := by
    have h := hevol.congr_of_eventuallyEq heveq.symm
    simp only [hefam_t] at h
    have hRt : rmFrame (G t) x (fun i => Ef i x) = Rl t x := by
      show rmFrame (G t) x (fun i => Ef i x) = rmFrame (G t) x (fun i => e t i x)
      congr 1
      funext i
      exact (het x hxU i).symm
    rwa [hRt] at h
  have hdRl_t : dRl t x = lapRmFrame (G t) x (fun i => Ef i x) := by
    show deriv (fun σ : ℝ => Rl σ x) t - Submission.Diff.Alg.Q (Rl t x)
      = lapRmFrame (G t) x (fun i => Ef i x)
    rw [hslice.deriv]
    abel
  -- ## Property (4): the spatial maximum principle
  have hmax : ∀ ℓ : Submission.Diff.Alg.Curv4 (Module.finrank ℝ E),
      Work.Diff.MP.frobNorm ℓ ≤ 1 →
      (∀ z ∈ U, Work.Diff.MP.frobDot ℓ (Rl t z) ≤ Work.Diff.MP.frobDot ℓ (Rl t x)) →
      Work.Diff.MP.frobDot ℓ (dRl t x) ≤ 0 := by
    intro ℓ _ hmaxℓ
    have hdRlx : dRl t x = lapRmFrame (G t) x (fun i => Ef i x) := hdRl_t
    have hLP' : laplAt (G t)
          (fun y : M => Work.Diff.MP.frobDot ℓ (rmFrame (G t) y (fun i => Ef i y))) x
        = Work.Diff.MP.frobDot ℓ (lapRmFrame (G t) x (fun i => Ef i x)) := by
      have h := hLPid (Work.Diff.MP.LM.frobDotCLM ℓ)
      simpa only [Work.Diff.MP.LM.frobDotCLM_apply, hEfx] using h
    rw [hdRlx, ← hLP']
    refine Work.Diff.MP.LM.laplAt_nonpos_of_isLocalMax (G t)
      (fun y : M => Work.Diff.MP.frobDot ℓ (rmFrame (G t) y (fun i => Ef i y))) ?_ x ?_
    · simpa only [Work.Diff.MP.LM.frobDotCLM_apply] using
        Work.Diff.MP.LM.contMDiff_ell_rmFrame (I := I) (M := M) hLC (G t)
          (Work.Diff.MP.LM.frobDotCLM ℓ) Ef hEfsm
    · filter_upwards [hUx] with z hz
      have h1 : rmFrame (G t) z (fun i => Ef i z) = Rl t z := by
        show rmFrame (G t) z (fun i => Ef i z) = rmFrame (G t) z (fun i => e t i z)
        congr 1
        funext i
        exact (het z hz i).symm
      have h2 : rmFrame (G t) x (fun i => Ef i x) = Rl t x := by
        show rmFrame (G t) x (fun i => Ef i x) = rmFrame (G t) x (fun i => e t i x)
        congr 1
        funext i
        exact (het x hxU i).symm
      rw [h1, h2]
      exact hmaxℓ z hz
  -- ## Properties (2) and (3): continuity and the uniform one-step estimate
  --
  -- Both are proved by reading `Rl` in the chart `χ := extChartAt I x` at the base point (see the
  -- ROUTE note just below).  The one *formal* trap of this workspace is that `Matrix` carries the
  -- `Ge`-area `ℓ^∞`-operator norm instance `Work.Diff.GE.matrixInstNormedRing`, which is *not*
  -- the Pi norm: `contDiffAt_pi` therefore does not apply to matrix-valued functions.  The
  -- workaround used below is to assemble the matrix-valued `C¹`-statement of the chart metric
  -- matrix `Γ'` from its entries with `Work.Diff.GE.matrix_eq_sum_singles`, `ContDiffAt.sum` and
  -- `ContDiffAt.smul_const`, and to extract entries with `Work.Diff.GE.matEntryCLM`.
  -- ## Properties (2) and (3): the chart reading of `Rl` and `dRl`
  --
  -- Write `χ := extChartAt I x`.  In the chart, `Rl` is the explicit function
  --   `Ψ (s, z) = rot ((sqrtC (Ring.inverse (Γ (s, z))))ᵀ) (Rm (s, z))`,
  -- where `Γ (s,z)_{ij} = (G s).inner (χ.symm z) (Ef i (χ.symm z)) (Ef j (χ.symm z))` and
  -- `Rm (s,z) = rmFrame (G s) (χ.symm z) Ef`.  Every ingredient is jointly `C^∞` (resp. `C¹`) on
  -- the box: the joint smoothness of the metric pairing and of `rmP` at the manifold level, pushed
  -- to the chart by `chart_lift_contDiffAt_at`, and `sqrtC ∘ Ring.inverse` by the chain rule.
  -- Consequently `Ψ` is `C¹` on the box, so `Rl` and `dRl` are continuous there, and the uniform
  -- one-step estimate follows from the mean value theorem (`frob_uniform_expansion`).
  have hχcont : ContinuousOn (fun y : M => (extChartAt I x) y) U :=
    (contMDiffOn_extChartAt (I := I) (x := x) (n := ∞)).continuousOn.mono
      (fun y hy => by simpa only [extChartAt_source] using hUchart y hy)
  have hKc : IsCompact ((extChartAt I x) '' U) := hUc.image_of_continuousOn hχcont
  have hleft : ∀ y ∈ U, (extChartAt I x).symm ((extChartAt I x) y) = y :=
    fun y hy => (extChartAt I x).left_inv (by simpa only [extChartAt_source] using hUchart y hy)
  have hGJ : Submission.Diff.JointSmooth G (Set.Ioo (t / 2) T) :=
    hflow.1.mono (fun p hp => ⟨⟨by linarith [hp.1.1, ht0], hp.1.2⟩, trivial⟩)
  have hσIoo : ∀ {σ : ℝ}, σ ∈ Set.Icc (t - δ₁) (t + δ₁) → σ ∈ Set.Ioo (t / 2) T := by
    intro σ hσ
    rw [hδ₁def] at hσ
    exact ⟨by linarith [hσ.1, min_le_left (t / 4) ((T - t) / 2), ht0],
      by linarith [hσ.2, min_le_right (t / 4) ((T - t) / 2), htT]⟩
  -- the chart representatives
  let Γ' : ℝ × E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun q => Γ q.1 ((extChartAt I x).symm q.2)
  let P' : ℝ × E → Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ :=
    fun q => sqrtC (Module.finrank ℝ E) (Ring.inverse (Γ' q))
  let Rm' : ℝ × E → Curv4 (Module.finrank ℝ E) :=
    fun q => rmFrame (G q.1) ((extChartAt I x).symm q.2) (fun i => Ef i ((extChartAt I x).symm q.2))
  let Ψ : ℝ × E → Curv4 (Module.finrank ℝ E) :=
    fun q => rot (Matrix.transpose (P' q)) (Rm' q)
  -- the scalar chart lifts
  have hscal : ∀ (σ : ℝ) (hσ : σ ∈ Set.Ioo (t / 2) T) (y : M) (hy : y ∈ U)
      (i j : Fin (Module.finrank ℝ E)),
      ContDiffAt ℝ ∞ (fun q : ℝ × E => (G q.1).inner ((extChartAt I x).symm q.2)
        (Ef i ((extChartAt I x).symm q.2)) (Ef j ((extChartAt I x).symm q.2)))
        (σ, (extChartAt I x) y) := by
    intro σ hσ y hy i j
    refine chart_lift_contDiffAt_at (I := I) (x := x) (y := y) (hUchart y hy)
      (Φ := fun p : ℝ × M => (G p.1).inner p.2 (Ef i p.2) (Ef j p.2)) ?_
    exact Work.Diff.EXT.contMDiffAt_metric_pairing (I := I) (M := M) isOpen_Ioo hGJ hσ
      (x := y) (Y := Ef i) (Z := Ef j) ((hEfsm i).contMDiffAt) ((hEfsm j).contMDiffAt)
  have hΓ'sm : ∀ (σ : ℝ) (hσ : σ ∈ Set.Ioo (t / 2) T) (y : M) (hy : y ∈ U),
      ContDiffAt ℝ 1 Γ' (σ, (extChartAt I x) y) := by
    intro σ hσ y hy
    have hS : ContDiffAt ℝ 1 (fun q : ℝ × E =>
        ∑ a, ∑ b, (Γ' q a b) • Matrix.single a b (1 : ℝ)) (σ, (extChartAt I x) y) := by
      refine ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ => ?_))
      exact ((hscal σ hσ y hy a b).of_le one_le_infty_lev).smul_const (Matrix.single a b (1 : ℝ))
    refine hS.congr_of_eventuallyEq ?_
    filter_upwards with q
    exact Work.Diff.GE.matrix_eq_sum_singles (Γ' q)
  have hRm'sm : ∀ (σ : ℝ) (hσ : σ ∈ Set.Ioo (t / 2) T) (y : M) (hy : y ∈ U),
      ContDiffAt ℝ 1 Rm' (σ, (extChartAt I x) y) := by
    intro σ hσ y hy
    refine contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => contDiffAt_pi.mpr (fun k =>
      contDiffAt_pi.mpr (fun l => ?_))))
    have hJ := Work.Diff.GE.rmP_jointSmoothNoCompact (I := I) (M := M) hLC isOpen_Ioo hGJ hσ y
      (A := Ef i) (B := Ef j) (C := Ef k) (D := Ef l)
      (hEfsm i) (hEfsm j) (hEfsm k) (hEfsm l)
    exact (chart_lift_contDiffAt_at (I := I) (x := x) (y := y) (hUchart y hy)
      (Φ := fun p : ℝ × M => Submission.Diff.rmP (G p.1) p.2 (Ef i p.2) (Ef j p.2)
        (Ef k p.2) (Ef l p.2)) hJ).of_le one_le_infty_lev
  have hP'sm : ∀ (σ : ℝ) (hσ : σ ∈ Set.Ioo (t / 2) T) (y : M) (hy : y ∈ U)
      (hV : Γ σ y ∈ V), ContDiffAt ℝ 1 P' (σ, (extChartAt I x) y) := by
    intro σ hσ y hy hV
    have hΓsm := hΓ'sm σ hσ y hy
    have heq : Γ' (σ, (extChartAt I x) y) = Γ σ y := by
      show Γ σ ((extChartAt I x).symm ((extChartAt I x) y)) = Γ σ y
      rw [hleft y hy]
    -- `Γ σ y` is a unit: its determinant is non-zero by the orthogonality relation
    have hunit : IsUnit (Γ σ y) := by
      have hkey : Matrix.transpose (P σ y) * Γ σ y * P σ y = 1 :=
        hV₀orth (Γ σ y) hV.1.1 (hΓsymm σ y)
      rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
      intro hdet
      have h1 : Matrix.det (Matrix.transpose (P σ y) * Γ σ y * P σ y) = 1 := by
        rw [hkey, Matrix.det_one]
      rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hdet] at h1
      simp at h1
    obtain ⟨u, hu⟩ := hunit
    have hbase : ContDiffAt ℝ 1 (Ring.inverse : Matrix (Fin (Module.finrank ℝ E))
        (Fin (Module.finrank ℝ E)) ℝ → Matrix (Fin (Module.finrank ℝ E))
        (Fin (Module.finrank ℝ E)) ℝ) (Γ' (σ, (extChartAt I x) y)) := by
      have hb : ContDiffAt ℝ 1 (Ring.inverse : Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ → Matrix (Fin (Module.finrank ℝ E))
          (Fin (Module.finrank ℝ E)) ℝ) (Γ σ y) := by
        rw [← hu]
        exact contDiffAt_ringInverse (𝕜 := ℝ) (n := (1 : ℕ∞ω)) u
      rwa [heq]
    have hinv : ContDiffAt ℝ 1 (fun q : ℝ × E => Ring.inverse (Γ' q))
        (σ, (extChartAt I x) y) := hbase.comp _ hΓsm
    have hmem : Ring.inverse (Γ' (σ, (extChartAt I x) y)) ∈ v₂ := by
      rw [heq]
      exact hV.2
    exact ContDiffAt.comp (σ, (extChartAt I x) y)
      (hv₂on.contDiffAt (hv₂open.mem_nhds hmem)) hinv
  have hΨ'sm : ∀ (σ : ℝ) (hσ : σ ∈ Set.Ioo (t / 2) T) (y : M) (hy : y ∈ U)
      (hV : Γ σ y ∈ V), ContDiffAt ℝ 1 Ψ (σ, (extChartAt I x) y) := by
    intro σ hσ y hy hV
    have hΓsm := hΓ'sm σ hσ y hy
    have hPsm := hP'sm σ hσ y hy hV
    have hRsm := hRm'sm σ hσ y hy
    have hentry : ∀ a b : Fin (Module.finrank ℝ E),
        ContDiffAt ℝ 1 (fun q : ℝ × E => P' q a b) (σ, (extChartAt I x) y) := by
      intro a b
      have hL : ContDiffAt ℝ 1 (Work.Diff.GE.matEntryCLM a b :
          Matrix (Fin (Module.finrank ℝ E)) (Fin (Module.finrank ℝ E)) ℝ → ℝ)
          (P' (σ, (extChartAt I x) y)) :=
        ((Work.Diff.GE.matEntryCLM a b).contDiff.contDiffAt).of_le one_le_infty_lev
      exact (hL.comp _ hPsm).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun q => rfl))
    have hRentry : ∀ a b c d : Fin (Module.finrank ℝ E),
        ContDiffAt ℝ 1 (fun q : ℝ × E => Rm' q a b c d) (σ, (extChartAt I x) y) := by
      intro a b c d
      have h1 := (contDiffAt_pi.mp hRsm) a
      have h2 := (contDiffAt_pi.mp h1) b
      have h3 := (contDiffAt_pi.mp h2) c
      exact (contDiffAt_pi.mp h3) d
    refine contDiffAt_pi.mpr (fun i => contDiffAt_pi.mpr (fun j => contDiffAt_pi.mpr (fun k =>
      contDiffAt_pi.mpr (fun l => ?_))))
    show ContDiffAt ℝ 1 (fun q : ℝ × E => ∑ a, ∑ b, ∑ c, ∑ d,
      P' q a i * P' q b j * P' q c k * P' q d l * Rm' q a b c d) (σ, (extChartAt I x) y)
    refine ContDiffAt.sum (fun a _ => ContDiffAt.sum (fun b _ => ContDiffAt.sum (fun c _ =>
      ContDiffAt.sum (fun d _ => ?_))))
    exact ((((hentry a i).mul (hentry b j)).mul (hentry c k)).mul (hentry d l)).mul
      (hRentry a b c d)
  -- the identification `Rl s y = Ψ (s, χ y)`
  have hΨ_pt : ∀ (σ : ℝ) (y : M) (hy : y ∈ U), Ψ (σ, (extChartAt I x) y) = Rl σ y := by
    intro σ y hy
    have h := Work.Diff.GE.rmFrame_eq_rot (I := I) (M := M) hLC (G σ) y (fun i => Ef i y)
      (fun i => e σ i y) (Matrix.transpose (P' (σ, (extChartAt I x) y)))
      (fun i => by
        show e σ i y = ∑ j, (Matrix.transpose (sqrtC (Module.finrank ℝ E)
          (Ring.inverse (Γ σ ((extChartAt I x).symm ((extChartAt I x) y)))))) i j • Ef j y
        rw [show (extChartAt I x).symm ((extChartAt I x) y) = y from hleft y hy]
        rfl)
    show rot (Matrix.transpose (P' (σ, (extChartAt I x) y)))
        (rmFrame (G σ) ((extChartAt I x).symm ((extChartAt I x) y))
          (fun i => Ef i ((extChartAt I x).symm ((extChartAt I x) y))))
      = rmFrame (G σ) y (fun i => e σ i y)
    rw [show (extChartAt I x).symm ((extChartAt I x) y) = y from hleft y hy]
    exact h.symm
  -- the box of the chart
  have hboxσ : ∀ {σ : ℝ}, σ ∈ Set.Icc t (t + δ) → σ ∈ Set.Icc (t - δ₁) (t + δ₁) := fun hσ =>
    ⟨by linarith [hσ.1, hδle₁4, hδ₁pos], by linarith [hσ.2, hδle₁4]⟩
  have hboxt : ∀ {σ : ℝ}, σ ∈ Set.Icc t (t + δ) → |σ - t| ≤ η := fun hσ => by
    rw [abs_of_nonneg (by linarith [hσ.1])]; linarith [hσ.2, hδleη]
  -- continuity of `Rl`
  have hΨcont_box : ContinuousOn Ψ (Set.prod (Set.Icc t (t + δ)) ((extChartAt I x) '' U)) := by
    intro q hq
    obtain ⟨σ, z⟩ := q
    obtain ⟨y, hyU, rfl⟩ := hq.2
    exact ((hΨ'sm σ (hσIoo (hboxσ hq.1)) y hyU (hΓV2 σ (hboxσ hq.1) (hboxt hq.1) y hyU)).continuousAt
      ).continuousWithinAt
  have hRlcont : ContinuousOn (fun p : ℝ × M => Rl p.1 p.2)
      (Set.prod (Set.Icc t (t + δ)) U) := by
    have hchart : ContinuousOn (fun p : ℝ × M => (p.1, (extChartAt I x) p.2))
        (Set.prod (Set.Icc t (t + δ)) U) :=
      continuousOn_fst.prodMk (hχcont.comp continuousOn_snd (fun p hp => hp.2))
    have hmap : Set.MapsTo (fun p : ℝ × M => (p.1, (extChartAt I x) p.2))
        (Set.prod (Set.Icc t (t + δ)) U)
        (Set.prod (Set.Icc t (t + δ)) ((extChartAt I x) '' U)) :=
      fun p hp => ⟨hp.1, ⟨p.2, hp.2, rfl⟩⟩
    refine (hΨcont_box.comp hchart hmap).congr (fun p hp => ?_)
    exact (hΨ_pt p.1 p.2 hp.2).symm
  -- the slice derivative in the chart
  have hderiv_eq : ∀ (s : ℝ) (hs : s ∈ Set.Icc t (t + δ)) (y : M) (hy : y ∈ U),
      deriv (fun σ : ℝ => Rl σ y) s = (fderiv ℝ Ψ (s, (extChartAt I x) y)) (1, 0) := by
    intro s hs y hy
    have hev : (fun σ : ℝ => Rl σ y) =ᶠ[𝓝 s] (fun σ : ℝ => Ψ (σ, (extChartAt I x) y)) := by
      filter_upwards [isOpen_Ioo.mem_nhds (show s ∈ Set.Ioo (s - δ) (s + δ) from
        ⟨by linarith [hδpos], by linarith [hδpos]⟩)] with σ _
      exact (hΨ_pt σ y hy).symm
    have hd : DifferentiableAt ℝ Ψ (s, (extChartAt I x) y) :=
      (hΨ'sm s (hσIoo (hboxσ hs)) y hy (hΓV2 s (hboxσ hs) (hboxt hs) y hy)).differentiableAt
        (by norm_num)
    have h1 : HasFDerivAt (fun σ : ℝ => (σ, (extChartAt I x) y)) (ContinuousLinearMap.inl ℝ ℝ E) s :=
      hasFDerivAt_prodMk_left (𝕜 := ℝ) s ((extChartAt I x) y)
    have h2 : HasDerivAt (fun σ : ℝ => Ψ (σ, (extChartAt I x) y))
        ((fderiv ℝ Ψ (s, (extChartAt I x) y)) (1, 0)) s := by
      have h := (hd.hasFDerivAt.comp s h1).hasDerivAt
      have hv : (((fderiv ℝ Ψ (s, (extChartAt I x) y)).comp
            (ContinuousLinearMap.inl ℝ ℝ E)) 1)
          = (fderiv ℝ Ψ (s, (extChartAt I x) y)) (1, 0) := by
        show (fderiv ℝ Ψ (s, (extChartAt I x) y))
          ((ContinuousLinearMap.inl ℝ ℝ E) 1) = (fderiv ℝ Ψ (s, (extChartAt I x) y)) (1, 0)
        rw [ContinuousLinearMap.inl_apply]
      rwa [hv] at h
    rw [(h2.congr_of_eventuallyEq hev).deriv]
  -- continuity of `dRl`
  have hdRlcont : ContinuousOn (fun p : ℝ × M => dRl p.1 p.2)
      (Set.prod (Set.Icc t (t + δ)) U) := by
    have hfderiv : ContinuousOn (fderiv ℝ Ψ)
        (Set.prod (Set.Icc t (t + δ)) ((extChartAt I x) '' U)) := by
      intro q hq
      obtain ⟨σ, z⟩ := q
      obtain ⟨y, hyU, rfl⟩ := hq.2
      exact ((hΨ'sm σ (hσIoo (hboxσ hq.1)) y hyU (hΓV2 σ (hboxσ hq.1) (hboxt hq.1) y hyU)).continuousAt_fderiv
        (by norm_num)).continuousWithinAt
    have hchart : ContinuousOn (fun p : ℝ × M => (p.1, (extChartAt I x) p.2))
        (Set.prod (Set.Icc t (t + δ)) U) :=
      continuousOn_fst.prodMk (hχcont.comp continuousOn_snd (fun p hp => hp.2))
    have hmap : Set.MapsTo (fun p : ℝ × M => (p.1, (extChartAt I x) p.2))
        (Set.prod (Set.Icc t (t + δ)) U)
        (Set.prod (Set.Icc t (t + δ)) ((extChartAt I x) '' U)) :=
      fun p hp => ⟨hp.1, ⟨p.2, hp.2, rfl⟩⟩
    have hfirst : ContinuousOn (fun p : ℝ × M => (fderiv ℝ Ψ (p.1, (extChartAt I x) p.2)) (1, 0))
        (Set.prod (Set.Icc t (t + δ)) U) :=
      (hfderiv.comp hchart hmap).clm_apply continuousOn_const
    have hQ : ContinuousOn (fun p : ℝ × M => Submission.Diff.Alg.Q (Rl p.1 p.2))
        (Set.prod (Set.Icc t (t + δ)) U) :=
      (continuous_Q (Module.finrank ℝ E)).comp_continuousOn hRlcont
    refine (hfirst.sub hQ).congr (fun p hp => ?_)
    show deriv (fun σ : ℝ => Rl σ p.2) p.1 - Submission.Diff.Alg.Q (Rl p.1 p.2)
      = (fderiv ℝ Ψ (p.1, (extChartAt I x) p.2)) (1, 0) - Submission.Diff.Alg.Q (Rl p.1 p.2)
    rw [hderiv_eq p.1 hp.1 p.2 hp.2]
  have hcont : ContinuousOn (fun p : ℝ × M => (Rl p.1 p.2, dRl p.1 p.2))
      (Set.prod (Set.Icc t (t + δ)) U) := hRlcont.prodMk hdRlcont
  -- ## Property (3): the uniform one-step estimate, from the mean value theorem in the chart
  have hbox : ∀ q ∈ Set.prod (Set.Icc t (t + δ)) ((extChartAt I x) '' U), ContDiffAt ℝ 1 Ψ q := by
    intro q hq
    obtain ⟨σ, z⟩ := q
    obtain ⟨y, hyU, rfl⟩ := hq.2
    exact hΨ'sm σ (hσIoo (hboxσ hq.1)) y hyU (hΓV2 σ (hboxσ hq.1) (hboxt hq.1) y hyU)
  have hexp : ∀ ε' > 0, ∃ δ' > 0, ∀ h : ℝ, 0 < h → h ≤ δ' → ∀ y ∈ U,
      Work.Diff.MP.frobDist (Rl (t + h) y)
        (Rl t y + h • (dRl t y + Submission.Diff.Alg.Q (Rl t y))) ≤ ε' * h := by
    intro ε' hε'
    obtain ⟨δ', hδ'pos, _, hmain⟩ :=
      frob_uniform_expansion (Ψ := Ψ) (t := t) (e := δ) hδpos hKc hbox ε' hε'
    refine ⟨δ', hδ'pos, fun h hh hh' y hy => ?_⟩
    have h1 := hmain h hh hh' ((extChartAt I x) y) ⟨y, hy, rfl⟩
    have htbox : t ∈ Set.Icc t (t + δ) := ⟨le_rfl, by linarith [hδpos]⟩
    have h2 : (fderiv ℝ Ψ (t, (extChartAt I x) y)) (1, 0)
        = dRl t y + Submission.Diff.Alg.Q (Rl t y) := by
      rw [← hderiv_eq t htbox y hy]
      show deriv (fun σ : ℝ => Rl σ y) t
        = (deriv (fun σ : ℝ => Rl σ y) t - Submission.Diff.Alg.Q (Rl t y))
          + Submission.Diff.Alg.Q (Rl t y)
      abel
    rw [hΨ_pt (t + h) y hy, hΨ_pt t y hy, h2] at h1
    exact h1
  exact ⟨δ, hδpos, hδT, U, hUx, Rl, dRl, hdist, hcont, hexp, hmax, hQbound⟩

end Work.Diff.MP
