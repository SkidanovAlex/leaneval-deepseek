import ChallengeDeps
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.Have
import Mathlib.Analysis.RCLike.Inner
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Submission.BoxMeas
import Submission.Bridge
import Submission.FilterFacts
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
Layer 1: the finite-volume ground-state energy.

For `N` particles in a box of side `L` with potential `v`, the (Dirichlet) ground-state
energy is the infimum of the Rayleigh quotients over `CInfty0Box N L`.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped NNReal ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

local notation "Δ[" i "]" => partialLaplacian i

local notation "⟪" f ", " g "⟫_["N "," L"]" => ∫ x in box N L, f x * g x

local notation "‖" f "‖_["N "," L"]" => √ ⟪f,f⟫_[N,L]

/-- The kinetic energy of `Ψ` in the box (no division by the norm). -/
noncomputable def kineticEnergy (N : ℕ) (L : ℝ) (Ψ : CInfty0Box N L) : ℝ :=
  ∑ i : Fin N, ∫ x in box N L, (Ψ : (Fin N → ℝ³) → ℝ) x * (- Δ[i] (Ψ : (Fin N → ℝ³) → ℝ)) x

/-- The interaction energy of `Ψ` in the box. -/
noncomputable def interactionEnergy (N : ℕ) (L : ℝ) (v : ℝ³ → ℝ) (Ψ : CInfty0Box N L) : ℝ :=
  ∫ x in box N L, ((Ψ : (Fin N → ℝ³) → ℝ) x) ^ 2 *
    (∑ ⟨i, j⟩ ∈ {(i, j) : Fin N × Fin N | i < j}, v (x i - x j))

/-- The (Dirichlet) ground-state energy of `N` particles in a box of side `L`. -/
noncomputable def boxEnergy (N : ℕ) (L : ℝ) (v : ℝ³ → ℝ) : ℝ :=
  ⨅ Ψ : CInfty0Box N L, ⟪(Ψ : (Fin N → ℝ³) → ℝ), 𝓗 N v (Ψ : (Fin N → ℝ³) → ℝ)⟫_[N,L] /
    ‖(Ψ : (Fin N → ℝ³) → ℝ)‖_[N,L] ^ 2

/- ## Smoothness and measure-theoretic support

A `CInfty0Box N L` function is `C^∞` on the whole ambient space (it is `C^∞`
inside the box and identically zero in a neighbourhood of the boundary), and all
the integrands that occur below are continuous, compactly supported functions,
hence integrable on the box.
-/

abbrev X (N : ℕ) := Fin N → EuclideanSpace ℝ (Fin 3)

lemma box_closed {N : ℕ} (L : ℝ) : IsClosed (box N L) := by
  rw [show box N L = ⋂ i : Fin N, ⋂ k : Fin 3,
      (fun x : X N => (x i) k) ⁻¹' (Set.Icc 0 L) by ext x; simp [box]]
  exact isClosed_iInter (fun i => isClosed_iInter (fun k =>
    (continuous_iff_isClosed.mp (by fun_prop : Continuous fun x : X N => (x i) k)) _ isClosed_Icc))

lemma eucl_norm_le_of_coord_le {L : ℝ} {y : EuclideanSpace ℝ (Fin 3)} (hL : 0 ≤ L)
    (hy : ∀ k, (y k) ∈ Set.Icc 0 L) : ‖y‖ ≤ Real.sqrt 3 * L := by
  have hb : 0 ≤ Real.sqrt 3 * L := by positivity
  apply le_of_sq_le_sq
  · rw [EuclideanSpace.real_norm_sq_eq]
    calc
      ∑ k : Fin 3, (y k) ^ 2 ≤ ∑ k : Fin 3, L ^ 2 := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        have hyk0 : 0 ≤ y k := (hy k).1
        have hyk1 : y k ≤ L := (hy k).2
        refine (sq_le_sq.mpr ?_)
        rw [abs_of_nonneg hyk0, abs_of_nonneg hL]
        exact hyk1
      _ = 3 * L ^ 2 := by norm_num
      _ = (Real.sqrt 3 * L) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : 0 ≤ (3 : ℝ))]
  · exact hb

lemma norm_le_of_mem_box {N : ℕ} {L : ℝ} {x : X N} (hL : 0 ≤ L) (hx : x ∈ box N L) :
    ‖x‖ ≤ Real.sqrt 3 * L := by
  rw [Pi.norm_def]
  have hc0 : 0 ≤ Real.sqrt 3 * L := by positivity
  let c : ℝ≥0 := ⟨Real.sqrt 3 * L, hc0⟩
  have hc : (c : ℝ) = Real.sqrt 3 * L := rfl
  rw [← hc]
  exact_mod_cast (Finset.sup_le_iff.mpr (fun i hi => by
    exact eucl_norm_le_of_coord_le hL (fun k => hx i k)))

lemma box_bounded {N : ℕ} {L : ℝ} (hL : 0 < L) : Bornology.IsBounded (box N L) := by
  rw [Metric.isBounded_iff]
  refine ⟨2 * (Real.sqrt 3 * L), ?_⟩
  intro x hx y hy
  have hxle : ‖x‖ ≤ Real.sqrt 3 * L := norm_le_of_mem_box hL.le hx
  have hyle : ‖y‖ ≤ Real.sqrt 3 * L := norm_le_of_mem_box hL.le hy
  calc
    dist x y = ‖x - y‖ := by rw [dist_eq_norm]
    _ ≤ ‖x‖ + ‖y‖ := norm_sub_le x y
    _ ≤ Real.sqrt 3 * L + (Real.sqrt 3 * L) := by exact add_le_add hxle hyle
    _ = 2 * (Real.sqrt 3 * L) := by ring

lemma box_compact {N : ℕ} {L : ℝ} (hL : 0 < L) : IsCompact (box N L) := by
  exact (Metric.isCompact_iff_isClosed_bounded).mpr ⟨box_closed L, box_bounded hL⟩

lemma psi_support_interior {N : ℕ} {L : ℝ} (Ψ : CInfty0Box N L) :
    Function.support (Ψ : X N → ℝ) ⊆ interior (box N L) := by
  intro x hx
  exact Ψ.support (subset_tsupport (Ψ : X N → ℝ) hx)

lemma psi_eq_zero_of_not_mem_interior {N : ℕ} {L : ℝ} (Ψ : CInfty0Box N L)
    {x : X N} (hx : x ∉ interior (box N L)) : (Ψ : X N → ℝ) x = 0 := by
  have hx2 : x ∉ tsupport (Ψ : X N → ℝ) := by
    intro h
    exact hx (Ψ.support h)
  exact image_eq_zero_of_notMem_tsupport hx2

lemma psi_support_box {N : ℕ} {L : ℝ} (Ψ : CInfty0Box N L) :
    Function.support (Ψ : X N → ℝ) ⊆ box N L := by
  exact psi_support_interior Ψ |>.trans interior_subset

lemma psi_contDiff {N : ℕ} {L : ℝ} (Ψ : CInfty0Box N L) : ContDiff ℝ ∞ (Ψ : X N → ℝ) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x ∈ interior (box N L)
  · have hb : box N L ∈ 𝓝 x := by
      have h1 : interior (box N L) ∈ 𝓝 x := (isOpen_interior.mem_nhds hx)
      exact Filter.mem_of_superset h1 interior_subset
    exact Ψ.contDiff.contDiffAt hb
  · have hzero : (Ψ : X N → ℝ) =ᶠ[𝓝 x] 0 := by
      have hx2 : x ∉ tsupport (Ψ : X N → ℝ) := by
        intro h
        exact hx (Ψ.support h)
      exact notMem_tsupport_iff_eventuallyEq.mp hx2
    exact ContDiffAt.congr_of_eventuallyEq
      (contDiff_const.contDiffAt : ContDiffAt ℝ ∞ (fun _ : X N => (0 : ℝ)) x) hzero

lemma tsupport_compact_of_box {N : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L) :
    IsCompact (tsupport (Ψ : X N → ℝ)) := by
  exact IsCompact.of_isClosed_subset (box_compact hL) (isClosed_tsupport _) (by
    exact closure_minimal (psi_support_box Ψ) (box_closed L))

lemma hasCompactSupport_Ψ {N : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L) :
    HasCompactSupport (Ψ : X N → ℝ) := tsupport_compact_of_box hL Ψ

/- The kinetic integrand `x ↦ Ψ x · (−Δ[i]Ψ x)` is integrable on the box. -/
lemma psi_contDiff_two {N : ℕ} {L : ℝ} (Ψ : CInfty0Box N L) : ContDiff ℝ 2 (Ψ : X N → ℝ) := by
  have h : (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) :=
    WithTop.coe_le_coe.mpr (by exact (le_top : (2 : ℕ∞) ≤ ⊤))
  exact (psi_contDiff Ψ).of_le h

/-- The `k`-coordinate second directional derivative of `f` along direction `coordDir N i k`,
as a smooth (hence continuous) function of the base point. -/
lemma secondDir_contDiff {N : ℕ} (i : Fin N) (k : Fin 3) {f : X N → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun x : X N =>
      (fderiv ℝ (fun z : X N => fderiv ℝ f z (coordDir N i k)) x) (coordDir N i k)) := by
  -- h₀(z) := fderiv f z (coordDir N i k) is C^∞; its derivative applied to the direction is C^∞.
  let u : X N := coordDir N i k
  have hf1 : ContDiff ℝ ∞ (fderiv ℝ f) := ContDiff.fderiv_right (m := ∞) hf (by simp)
  have heval : ContDiff ℝ ∞ (fun (L : X N →L[ℝ] ℝ) => L u) := by
    exact ((ContinuousLinearMap.apply (𝕜 := ℝ) (Fₗ := ℝ) u : (X N →L[ℝ] ℝ) →L[ℝ] ℝ).contDiff)
  have h0 : ContDiff ℝ ∞ (fun z : X N => fderiv ℝ f z u) := by
    simpa [Function.comp_def] using heval.comp hf1
  have hd : ContDiff ℝ ∞ (fderiv ℝ (fun z : X N => fderiv ℝ f z u)) :=
    ContDiff.fderiv_right (m := ∞) h0 (by simp)
  have hfinal : ContDiff ℝ ∞ (fun x : X N => (fderiv ℝ (fun z : X N => fderiv ℝ f z u) x) u) := by
    simpa [Function.comp_def] using heval.comp hd
  simpa [u] using hfinal

/-- `Δ[i]Ψ` is continuous. -/
lemma continuous_partialLaplacian {N : ℕ} {L : ℝ} (Ψ : CInfty0Box N L) (i : Fin N) :
    Continuous (fun x : X N => partialLaplacian i (Ψ : X N → ℝ) x) := by
  have hbridge := partialLaplacian_eq_sum_secondDir N i (f := (Ψ : X N → ℝ)) (psi_contDiff_two Ψ)
  -- hbridge : partialLaplacian i Ψ = fun x => ∑ k, ...
  rw [hbridge]
  -- continuous of a finite sum of continuous functions
  refine continuous_finsetSum (s := Finset.univ) (f := fun k x =>
    (fderiv ℝ (fun z : X N => fderiv ℝ (Ψ : X N → ℝ) z (coordDir N i k)) x) (coordDir N i k)) ?_
  intro k hk
  exact (secondDir_contDiff i k (psi_contDiff Ψ)).continuous

lemma integrableOn_kinetic_term {N : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L) (i : Fin N) :
    IntegrableOn (fun x : X N => (Ψ : X N → ℝ) x * (-(partialLaplacian i (Ψ : X N → ℝ) x)))
      (box N L) volume := by
  -- whole-space integrability of the (continuous, compactly supported) integrand
  have hcont : Continuous (fun x : X N => (Ψ : X N → ℝ) x * (-(partialLaplacian i (Ψ : X N → ℝ) x))) := by
    exact (psi_contDiff Ψ).continuous.mul (continuous_partialLaplacian Ψ i).neg
  have hcs : HasCompactSupport (fun x : X N => (Ψ : X N → ℝ) x * (-(partialLaplacian i (Ψ : X N → ℝ) x))) := by
    exact (hasCompactSupport_Ψ hL Ψ).mul_right
  have hint : Integrable (fun x : X N => (Ψ : X N → ℝ) x * (-(partialLaplacian i (Ψ : X N → ℝ) x))) volume := by
    exact Continuous.integrable_of_hasCompactSupport hcont hcs
  exact (integrableOn_iff_integrable_of_support_subset
    (f := fun x : X N => (Ψ : X N → ℝ) x * (-(partialLaplacian i (Ψ : X N → ℝ) x)))
    (s := box N L) (μ := volume)
    (by
      intro x hx
      apply psi_support_box Ψ
      intro hzero
      apply hx
      simp [hzero])).mpr hint

/-/-- The interaction energy is nonnegative for `v ≥ 0`. -/
lemma interactionEnergy_nonneg {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hv : 0 ≤ v)
    (Ψ : CInfty0Box N L) : 0 ≤ interactionEnergy N L v Ψ := by
  unfold interactionEnergy
  apply integral_nonneg
  intro x
  exact mul_nonneg (sq_nonneg _)
    (Finset.sum_nonneg (s := (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)))
      (f := fun p : Fin N × Fin N => v (x p.1 - x p.2)) (fun p hp => hv (x p.1 - x p.2)))

/-- The interaction integrand, pointwise. -/
noncomputable def intIntegrand (N : ℕ) (L : ℝ) (v : ℝ³ → ℝ) (Ψ : CInfty0Box N L) :
    X N → ℝ := fun x =>
      ((Ψ : X N → ℝ) x) ^ 2 *
        (∑ p ∈ (Finset.univ.filter (fun p : Fin N × Fin N => p.1 < p.2)), v (x p.1 - x p.2))

/-- The kinetic integrand, pointwise. -/
noncomputable def kinIntegrand (N : ℕ) (L : ℝ) (Ψ : CInfty0Box N L) : X N → ℝ := fun x =>
  ∑ i : Fin N, (Ψ : X N → ℝ) x * (-(partialLaplacian i (Ψ : X N → ℝ) x))

/-- Continuity of the first directional derivative `x ↦ fderiv f x u`. -/
lemma firstDir_contDiff {N : ℕ} {f : X N → ℝ} (hf : ContDiff ℝ ∞ f) (u : X N) :
    ContDiff ℝ ∞ (fun x : X N => fderiv ℝ f x u) := by
  have hf1 : ContDiff ℝ ∞ (fderiv ℝ f) := ContDiff.fderiv_right (m := ∞) hf (by simp)
  exact ((ContinuousLinearMap.apply (𝕜 := ℝ) (Fₗ := ℝ) u : (X N →L[ℝ] ℝ) →L[ℝ] ℝ).contDiff).comp hf1

/-- Continuity of the second directional derivative
`x ↦ (fderiv (fun z ↦ fderiv f z u) x) u`. -/
lemma secondDir_contDiff_u {N : ℕ} {f : X N → ℝ} (hf : ContDiff ℝ ∞ f) (u : X N) :
    ContDiff ℝ ∞ (fun x : X N => (fderiv ℝ (fun z : X N => fderiv ℝ f z u) x) u) := by
  have h0 : ContDiff ℝ ∞ (fun z : X N => fderiv ℝ f z u) := firstDir_contDiff hf u
  have hd : ContDiff ℝ ∞ (fderiv ℝ (fun z : X N => fderiv ℝ f z u)) :=
    ContDiff.fderiv_right (m := ∞) h0 (by simp)
  exact ((ContinuousLinearMap.apply (𝕜 := ℝ) (Fₗ := ℝ) u : (X N →L[ℝ] ℝ) →L[ℝ] ℝ).contDiff).comp hd

/-- A continuous compactly-supported function is integrable. -/
lemma integrable_cont_hcs {N : ℕ} {f : X N → ℝ} (hcont : Continuous f) (hcs : HasCompactSupport f) :
    Integrable f volume := Continuous.integrable_of_hasCompactSupport hcont hcs

/-- The compact support of `x ↦ fderiv f x u` is contained in that of `f`. -/
lemma tsupport_firstDir_subset {N : ℕ} {f : X N → ℝ} (u : X N) :
    tsupport (fun x : X N => fderiv ℝ f x u) ⊆ tsupport f := by
  have hs : Function.support (fun x : X N => fderiv ℝ f x u) ⊆ tsupport f := by
    intro x hx
    by_contra hx2
    have hz : fderiv ℝ f x = 0 := fderiv_of_notMem_tsupport ℝ hx2
    exact hx (by simp [hz])
  exact closure_minimal hs (isClosed_tsupport f)

/-- The compact support of the second directional derivative is contained in that of `f`. -/
lemma tsupport_secondDir_subset {N : ℕ} {f : X N → ℝ} (u : X N) :
    tsupport (fun x : X N =>
      fderiv ℝ (fun z : X N => fderiv ℝ f z u) x u) ⊆ tsupport f := by
  have hs : Function.support (fun x : X N =>
      fderiv ℝ (fun z : X N => fderiv ℝ f z u) x u) ⊆ tsupport f := by
    intro x hx
    have hx2 : x ∈ tsupport (fun z : X N => fderiv ℝ f z u) := by
      by_contra hx3
      have hz : fderiv ℝ (fun z : X N => fderiv ℝ f z u) x = 0 :=
        fderiv_of_notMem_tsupport ℝ hx3
      exact hx (by simp [hz])
    exact tsupport_firstDir_subset u hx2
  exact closure_minimal hs (isClosed_tsupport f)

/-- Integration by parts in the whole space, twice, makes the kinetic core nonnegative:
`∫ Ψ·(−D²_uΨ) = ∫ (D_uΨ)² ≥ 0`. -/
lemma wholeSpace_dir2_nonneg {N : ℕ} {f : X N → ℝ} {u : X N} (hf : ContDiff ℝ ∞ f)
    (hcs : HasCompactSupport f) :
    0 ≤ ∫ x, f x * (-(fderiv ℝ (fun z : X N => fderiv ℝ f z u) x u)) := by
  let g : X N → ℝ := fun z => fderiv ℝ f z u
  have hg_cd : ContDiff ℝ ∞ g := by
    dsimp [g]
    exact firstDir_contDiff hf u
  have hg_c : Continuous g := hg_cd.continuous
  have hf_c : Continuous f := hf.continuous
  have hD2_cd : ContDiff ℝ ∞ (fun x : X N => fderiv ℝ g x u) := by
    dsimp [g]
    exact secondDir_contDiff_u hf u
  have hD2_c : Continuous (fun x : X N => fderiv ℝ g x u) := hD2_cd.continuous
  have hg_hcs : HasCompactSupport g := by
    exact IsCompact.of_isClosed_subset hcs (isClosed_tsupport g) (by
      simpa [g] using (tsupport_firstDir_subset (f := f) u))
  have hD2_hcs : HasCompactSupport (fun x : X N => fderiv ℝ g x u) := by
    exact IsCompact.of_isClosed_subset hcs (isClosed_tsupport (fun x : X N => fderiv ℝ g x u)) (by
      simpa [g] using (tsupport_secondDir_subset (f := f) u))
  -- products: continuous and compactly supported
  have hfg_c : Continuous (fun x : X N => f x * g x) := hf_c.mul hg_c
  have hfg_h : HasCompactSupport (fun x : X N => f x * g x) := hcs.mul_right
  have hfg : Integrable (fun x : X N => f x * g x) volume :=
    integrable_cont_hcs hfg_c hfg_h
  have hfD2_c : Continuous (fun x : X N => f x * fderiv ℝ g x u) := hf_c.mul hD2_c
  have hfD2_h : HasCompactSupport (fun x : X N => f x * fderiv ℝ g x u) := hcs.mul_right
  have hfD2 : Integrable (fun x : X N => f x * fderiv ℝ g x u) volume :=
    integrable_cont_hcs hfD2_c hfD2_h
  have hgg_c : Continuous (fun x : X N => fderiv ℝ f x u * g x) := hg_c.mul hg_c
  have hgg_h : HasCompactSupport (fun x : X N => fderiv ℝ f x u * g x) := hg_hcs.mul_right
  have hgg : Integrable (fun x : X N => fderiv ℝ f x u * g x) volume :=
    integrable_cont_hcs hgg_c hgg_h
  have hf_diff : ∀ x ∈ tsupport g, DifferentiableAt ℝ f x := fun x hx =>
    hf.differentiable (by norm_num) x
  have hg_diff : ∀ x ∈ tsupport f, DifferentiableAt ℝ g x := fun x hx =>
    hg_cd.differentiable (by norm_num) x
  have hmain := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable (f := f) (g := g) (v := u)
    (μ := volume) hgg hfD2 hfg hf_diff hg_diff
  have hgoal : (∫ x, f x * (-(fderiv ℝ (fun z : X N => fderiv ℝ f z u) x u))) = ∫ x, (g x) ^ 2 := by
    calc
      (∫ x, f x * (-(fderiv ℝ (fun z : X N => fderiv ℝ f z u) x u)))
          = ∫ x, -(f x * fderiv ℝ g x u) := by
            apply integral_congr_ae
            filter_upwards with x
            dsimp [g]
            ring
      _ = -(∫ x, f x * fderiv ℝ g x u) := by rw [integral_neg]
      _ = ∫ x, (g x) ^ 2 := by
            rw [hmain]
            calc
              -(-(∫ x, fderiv ℝ f x u * g x)) = ∫ x, fderiv ℝ f x u * g x := by simp
              _ = ∫ x, (g x) ^ 2 := by
                    apply integral_congr_ae
                    filter_upwards with x
                    dsimp [g]
                    rw [pow_two]
  rw [hgoal]
  exact integral_nonneg (fun x => sq_nonneg (g x))

/-- A single particle term of the kinetic energy is nonnegative (box integral, own notation). -/
lemma boxInt_kinetic_term_nonneg {N : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L) (i : Fin N) :
    0 ≤ (∫ x in box N L, (Ψ : X N → ℝ) x * (-(partialLaplacian i (Ψ : X N → ℝ) x))) := by
  have hconv : (∫ x in box N L, (Ψ : X N → ℝ) x * (-(partialLaplacian i (Ψ : X N → ℝ) x)))
      = ∫ x, (Ψ : X N → ℝ) x * (-(partialLaplacian i (Ψ : X N → ℝ) x)) := by
    exact setIntegral_eq_integral_of_forall_compl_eq_zero (by
      intro x hx
      have hz : (Ψ : X N → ℝ) x = 0 := psi_eq_zero_of_not_mem_interior Ψ (by
        intro hxint
        exact hx (interior_subset hxint))
      simp [hz])
  rw [hconv]
  have hbr := partialLaplacian_eq_sum_secondDir N i (f := (Ψ : X N → ℝ)) (psi_contDiff_two Ψ)
  have hpoint : (fun x : X N => (Ψ : X N → ℝ) x * (-(partialLaplacian i (Ψ : X N → ℝ) x)))
      = fun x : X N => ∑ k : Fin 3,
          (Ψ : X N → ℝ) x * (-(fderiv ℝ
            (fun z : X N => fderiv ℝ (Ψ : X N → ℝ) z (coordDir N i k)) x) (coordDir N i k)) := by
    funext x
    have hbrx : partialLaplacian i (Ψ : X N → ℝ) x =
        ∑ k : Fin 3, (fderiv ℝ (fun z : X N => fderiv ℝ (Ψ : X N → ℝ) z (coordDir N i k)) x)
          (coordDir N i k) := by
      simpa using congrFun hbr x
    rw [hbrx]
    rw [← Finset.sum_neg_distrib, Finset.mul_sum]
  rw [hpoint]
  rw [integral_finsetSum (s := Finset.univ) (μ := volume)
    (f := fun (k : Fin 3) (x : X N) => (Ψ : X N → ℝ) x * (-(fderiv ℝ
      (fun z : X N => fderiv ℝ (Ψ : X N → ℝ) z (coordDir N i k)) x) (coordDir N i k)))]
  · exact Finset.sum_nonneg (fun k hk =>
      wholeSpace_dir2_nonneg (f := (Ψ : X N → ℝ)) (u := coordDir N i k) (psi_contDiff Ψ)
        (hasCompactSupport_Ψ hL Ψ))
  · intro k hk
    have hS_cd : ContDiff ℝ ∞ (fun x : X N => (fderiv ℝ
        (fun z : X N => fderiv ℝ (Ψ : X N → ℝ) z (coordDir N i k)) x) (coordDir N i k)) :=
      secondDir_contDiff_u (psi_contDiff Ψ) (coordDir N i k)
    have hcont : Continuous (fun x : X N => (Ψ : X N → ℝ) x * (-(fderiv ℝ
        (fun z : X N => fderiv ℝ (Ψ : X N → ℝ) z (coordDir N i k)) x) (coordDir N i k))) :=
      (psi_contDiff Ψ).continuous.mul hS_cd.continuous.neg
    have hcs : HasCompactSupport (fun x : X N => (Ψ : X N → ℝ) x * (-(fderiv ℝ
        (fun z : X N => fderiv ℝ (Ψ : X N → ℝ) z (coordDir N i k)) x) (coordDir N i k))) :=
      (hasCompactSupport_Ψ hL Ψ).mul_right
    exact Continuous.integrable_of_hasCompactSupport hcont hcs

/-- The box integral of the pointwise kinetic integrand is the sum over particles. -/
lemma boxInt_kinIntegrand_eq_sum (N : ℕ) {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L) :
    (∫ x in box N L, kinIntegrand N L Ψ x) =
      ∑ i : Fin N, ∫ x in box N L, (Ψ : X N → ℝ) x * (-(partialLaplacian i (Ψ : X N → ℝ) x)) := by
  unfold kinIntegrand
  rw [integral_finsetSum (s := Finset.univ) (μ := volume.restrict (box N L))
    (f := fun i x => (Ψ : X N → ℝ) x * (-(partialLaplacian i (Ψ : X N → ℝ) x)))
    (fun i hi => integrableOn_kinetic_term hL Ψ i)]

/-- The kinetic energy form is nonnegative: `∫ Ψ·(-ΔΨ) ≥ 0` for admissible `Ψ`
(supported strictly inside the box). -/
lemma kineticEnergy_nonneg {N : ℕ} {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L) :
    0 ≤ kineticEnergy N L Ψ := by
  unfold kineticEnergy
  exact Finset.sum_nonneg (fun i hi => boxInt_kinetic_term_nonneg hL Ψ i)


lemma numerator_integrand_eq (N : ℕ) (L : ℝ) (v : ℝ³ → ℝ) (Ψ : CInfty0Box N L) :
    (fun x : X N => (Ψ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x)
      = kinIntegrand N L Ψ + intIntegrand N L v Ψ := by
  funext x
  unfold _root_.BoseGases.𝓗 kinIntegrand intIntegrand
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
  · rw [← Finset.sum_mul]
    ring

/-- The box-integral of the kinetic integrand equals the kinetic energy. -/
lemma boxInt_kinIntegrand (N : ℕ) {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L) :
    (∫ x in box N L, kinIntegrand N L Ψ x) = kineticEnergy N L Ψ := by
  unfold kinIntegrand kineticEnergy
  rw [integral_finsetSum (s := Finset.univ) (μ := volume.restrict (box N L))
    (f := fun i x => (Ψ : X N → ℝ) x * (-(partialLaplacian i (Ψ : X N → ℝ) x)))
    (fun i hi => integrableOn_kinetic_term hL Ψ i)]
  rfl

/-- The box-integral of the interaction integrand equals the interaction energy. -/
lemma boxInt_intIntegrand (N : ℕ) (L : ℝ) (v : ℝ³ → ℝ) (Ψ : CInfty0Box N L) :
    (∫ x in box N L, intIntegrand N L v Ψ x) = interactionEnergy N L v Ψ := by
  unfold intIntegrand interactionEnergy
  rfl

lemma integrableOn_kinIntegrand (N : ℕ) {L : ℝ} (hL : 0 < L) (Ψ : CInfty0Box N L) :
    IntegrableOn (kinIntegrand N L Ψ) (box N L) volume := by
  -- finite sum of integrable functions
  unfold kinIntegrand
  exact integrable_finsetSum (s := Finset.univ) (μ := volume.restrict (box N L))
    (f := fun i x => (Ψ : X N → ℝ) x * (-(partialLaplacian i (Ψ : X N → ℝ) x)))
    (fun i hi => integrableOn_kinetic_term hL Ψ i)

/- Energy decomposition.  The expectation of the Hamiltonian of an admissible state is the sum
of the kinetic and the interaction energy, provided the interaction integrand is integrable on
the box.

(As stated in the original decomposition of this file this identity is *not* provable for an
arbitrary potential `v : ℝ³ → ℝ`: without the extra hypothesis the interaction integrand need
not even be measurable, and the two sides of the identity may differ by a conventional zero.
The usual applications have `v` locally integrable, in which case the hypothesis holds.) -/
lemma energy_decomposition (N : ℕ) (L : ℝ) (v : ℝ³ → ℝ) (Ψ : CInfty0Box N L)
    (hL : 0 < L) (hint : IntegrableOn (intIntegrand N L v Ψ) (box N L) volume) :
    (∫ x in box N L, (Ψ : (Fin N → ℝ³) → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : (Fin N → ℝ³) → ℝ) x) =
      kineticEnergy N L Ψ + interactionEnergy N L v Ψ := by
  have hkinInt := integrableOn_kinIntegrand N hL Ψ
  calc
    (∫ x in box N L, (Ψ : (Fin N → ℝ³) → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : (Fin N → ℝ³) → ℝ) x)
        = ∫ x in box N L, (kinIntegrand N L Ψ + intIntegrand N L v Ψ) x := by
          rw [numerator_integrand_eq]
    _ = (∫ x in box N L, kinIntegrand N L Ψ x) + ∫ x in box N L, intIntegrand N L v Ψ x := by
          exact integral_add (μ := volume.restrict (box N L)) hkinInt hint
    _ = kineticEnergy N L Ψ + interactionEnergy N L v Ψ := by
          rw [boxInt_kinIntegrand N hL Ψ, boxInt_intIntegrand N L v Ψ]

/-- If the kinetic energy of every state is nonnegative, then so is the box energy. -/
lemma boxEnergy_nonneg_of {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v)
    (hkin : ∀ Ψ : CInfty0Box N L, 0 ≤ kineticEnergy N L Ψ) :
    0 ≤ boxEnergy N L v := by
  have hnonneg : ∀ Ψ : CInfty0Box N L,
      0 ≤ ⟪(Ψ : (Fin N → ℝ³) → ℝ), 𝓗 N v (Ψ : (Fin N → ℝ³) → ℝ)⟫_[N,L] /
        ‖(Ψ : (Fin N → ℝ³) → ℝ)‖_[N,L] ^ 2 := by
    intro Ψ
    have hnum : 0 ≤ (∫ x in box N L, (Ψ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x) := by
      by_cases hint : IntegrableOn (intIntegrand N L v Ψ) (box N L) volume
      · -- both integrands integrable: split
        have hkinInt := integrableOn_kinIntegrand N hL Ψ
        have h1 : (∫ x in box N L, (Ψ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x)
            = kineticEnergy N L Ψ + interactionEnergy N L v Ψ := by
          calc
            (∫ x in box N L, (Ψ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x)
                = ∫ x in box N L, (kinIntegrand N L Ψ + intIntegrand N L v Ψ) x := by
                  rw [numerator_integrand_eq]
            _ = (∫ x in box N L, kinIntegrand N L Ψ x) + ∫ x in box N L, intIntegrand N L v Ψ x := by
                  exact integral_add (μ := volume.restrict (box N L)) hkinInt hint
            _ = kineticEnergy N L Ψ + interactionEnergy N L v Ψ := by
                  rw [boxInt_kinIntegrand N hL Ψ, boxInt_intIntegrand N L v Ψ]
        rw [h1]
        exact add_nonneg (hkin Ψ) (interactionEnergy_nonneg hv Ψ)
      · -- interaction integrand not integrable: the numerator is 0
        have hkinInt := integrableOn_kinIntegrand N hL Ψ
        have hnot : ¬ IntegrableOn (fun x : X N =>
            (kinIntegrand N L Ψ x) + (intIntegrand N L v Ψ x)) (box N L) volume := by
          intro hsum
          apply hint
          -- intIntegrand = (kin + int) - kin pointwise
          have hsub : IntegrableOn (fun x : X N =>
              (kinIntegrand N L Ψ x + intIntegrand N L v Ψ x) - kinIntegrand N L Ψ x)
              (box N L) volume := IntegrableOn.sub hsum hkinInt
          convert hsub using 1
          funext x
          ring
        have hzero : (∫ x in box N L, (Ψ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x) = 0 := by
          calc
            (∫ x in box N L, (Ψ : X N → ℝ) x * _root_.BoseGases.𝓗 N v (Ψ : X N → ℝ) x)
                = ∫ x in box N L, (kinIntegrand N L Ψ + intIntegrand N L v Ψ) x := by
                  rw [numerator_integrand_eq]
            _ = 0 := by
                  exact integral_undef (μ := volume.restrict (box N L)) hnot
        rw [hzero]
    apply div_nonneg hnum (sq_nonneg _)
  by_cases hne : Nonempty (CInfty0Box N L)
  · haveI := hne
    unfold boxEnergy
    exact le_ciInf hnonneg
  · haveI : IsEmpty (CInfty0Box N L) := ⟨fun a => hne ⟨a⟩⟩
    unfold boxEnergy
    simp

/-- If the box energy density tends to `x` along the joint filter, then `e ρ v = x`. -/
lemma e_eq_tendsto_boxEnergy {ρ : ℝ} {v : ℝ³ → ℝ} {x : ℝ} (hρ : 0 ≤ ρ)
    (h : Tendsto (fun (p : ℝ × ℕ) => p.1 ^ (-3 : ℤ) * boxEnergy p.2 p.1 v)
      (jointFilter ρ) (𝓝 x)) : e ρ v = x := by
  haveI : (jointFilter ρ).NeBot := jointFilter_neBot hρ
  dsimp [e, boxEnergy]
  exact Filter.Tendsto.limUnder_eq h


/-- The box ground-state energy is nonnegative for `0 ≤ v`. -/
lemma boxEnergy_nonneg {N : ℕ} {L : ℝ} {v : ℝ³ → ℝ} (hL : 0 < L) (hv : 0 ≤ v) :
    0 ≤ boxEnergy N L v := by
  exact boxEnergy_nonneg_of hL hv (fun Ψ => kineticEnergy_nonneg hL Ψ)

end BoseGases

end Submission