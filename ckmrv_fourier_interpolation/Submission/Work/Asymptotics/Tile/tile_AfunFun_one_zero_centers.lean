import Mathlib
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Asymptotics.KfunClear_vanish_of_phiPair
import Submission.Work.Asymptotics.continuous_AfunFun
import Submission.Work.Asymptotics.FlatMiddleAux
import Submission.Work.Asymptotics.Kfun_principal_part_z_lip
import Submission.Work.Kernels.Kernels

noncomputable section

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology
open Metric Filter Complex

namespace Work.Asymptotics.Tile

open Work.Kernels

/-! ## Elementary facts about the `S`-action -/

/-- The coefficient of `S • τ`. -/
lemma coe_S_smul' (τ : ℍ) : ((ModularGroup.S • τ : ℍ) : ℂ) = (-(τ : ℂ))⁻¹ := by
  rw [UpperHalfPlane.modular_S_smul]

/-- `S` is an involution on `ℍ`. -/
lemma S_smul_S_smul' (τ : ℍ) : ModularGroup.S • (ModularGroup.S • τ) = τ := by
  refine UpperHalfPlane.ext ?_
  rw [coe_S_smul', coe_S_smul']
  simp

/-! ## Vanishing transfer from `KfunClear` to `AfunFun` -/

/-- Since `KfunClear = Δ(τ)Δ(z)^e · AfunFun` and `Δ` never vanishes, a zero of the cleared kernel
is a zero of `AfunFun`. -/
lemma AfunFun_eq_zero_of_KfunClear_eq_zero (ℓ : LogLambdaData) (d : ℕ) (τ z : ℍ)
    (h : KfunClear ℓ d τ z = 0) : AfunFun ℓ d τ z = 0 := by
  rw [KfunClear_eq_mul_AfunFun ℓ d τ z] at h
  exact (mul_eq_zero.mp h).resolve_left
    (mul_ne_zero (ClassicalFacts.DeltaFun_ne_zero τ)
      (pow_ne_zero _ (ClassicalFacts.DeltaFun_ne_zero z)))

/-! ## A uniform bound for `AfunFun` on a fixed Euclidean box -/

/-- The Euclidean box `{‖x‖ ≤ R, c ≤ Im x} ⊆ ℂ` is compact. -/
lemma isCompact_box_im (R c : ℝ) : IsCompact {x : ℂ | ‖x‖ ≤ R ∧ c ≤ x.im} := by
  have hcl : IsClosed {x : ℂ | ‖x‖ ≤ R ∧ c ≤ x.im} :=
    (isClosed_le continuous_norm continuous_const).inter
      (isClosed_le continuous_const Complex.continuous_im)
  refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨hcl, ?_⟩
  exact (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset
    (fun x hx => by rw [Metric.mem_closedBall, dist_zero_right]; exact hx.1)

/-- Uniform bound for the cleared value function `AfunFun` on a product of two compact
Euclidean boxes of the upper half plane. -/
lemma exists_bound_AfunFun_box (ℓ : LogLambdaData) (d : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ τ w : ℍ, ‖(τ : ℂ)‖ ≤ 3 → (1 / 100 : ℝ) ≤ τ.im →
      ‖(w : ℂ)‖ ≤ 9 → (1 / 100 : ℝ) ≤ w.im → ‖AfunFun ℓ d τ w‖ ≤ M := by
  have h₁ : IsCompact {x : ℂ | ‖x‖ ≤ 3 ∧ (1 / 100 : ℝ) ≤ x.im} := isCompact_box_im 3 (1 / 100)
  have h₂ : IsCompact {x : ℂ | ‖x‖ ≤ 9 ∧ (1 / 100 : ℝ) ≤ x.im} := isCompact_box_im 9 (1 / 100)
  have hb₁ : ∀ u ∈ {x : ℂ | ‖x‖ ≤ 3 ∧ (1 / 100 : ℝ) ≤ x.im}, 0 < u.im := fun u hu => by
    have := hu.2
    linarith
  have hb₂ : ∀ u ∈ {x : ℂ | ‖x‖ ≤ 9 ∧ (1 / 100 : ℝ) ≤ x.im}, 0 < u.im := fun u hu => by
    have := hu.2
    linarith
  have hpair : ContinuousOn (fun p : ℂ × ℂ =>
      (UpperHalfPlane.ofComplex p.1, UpperHalfPlane.ofComplex p.2))
      ({x : ℂ | ‖x‖ ≤ 3 ∧ (1 / 100 : ℝ) ≤ x.im} ×ˢ
        {x : ℂ | ‖x‖ ≤ 9 ∧ (1 / 100 : ℝ) ≤ x.im}) :=
    ((continuousOn_ofComplex_im_pos.mono hb₁).comp
        continuous_fst.continuousOn (fun p hp => hp.1)).prodMk
      ((continuousOn_ofComplex_im_pos.mono hb₂).comp
        continuous_snd.continuousOn (fun p hp => hp.2))
  obtain ⟨B₀, hB₀⟩ := (h₁.prod h₂).exists_bound_of_continuousOn
    ((continuous_AfunFun ℓ d).continuousOn.comp hpair (fun p _ => Set.mem_univ _))
  refine ⟨max B₀ 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun τ w hτ hτim hw hwim => ?_⟩
  have h1 : ‖AfunFun ℓ d τ w‖ =
      ‖AfunFun ℓ d (UpperHalfPlane.ofComplex (τ : ℂ)) (UpperHalfPlane.ofComplex (w : ℂ))‖ := by
    rw [UpperHalfPlane.ofComplex_apply, UpperHalfPlane.ofComplex_apply]
  rw [h1]
  exact le_trans (hB₀ ((τ : ℂ), (w : ℂ)) ⟨⟨hτ, hτim⟩, ⟨hw, hwim⟩⟩) (le_max_left _ _)

/-! ## The box bounds for `S • σ` -/

/-- For `σ` in the box `{|Re| ≤ 1, 2 ≤ Im ≤ 6}`, the `S`-translate satisfies
`‖S • σ‖ ≤ 1/2` and `Im (S • σ) ≥ 1/100`; moreover `‖σ‖ ≤ 7`. -/
lemma S_smul_box_bounds (σ : ℍ) (hre : |σ.re| ≤ 1) (him2 : 2 ≤ σ.im) (him6 : σ.im ≤ 6) :
    ‖((ModularGroup.S • σ : ℍ) : ℂ)‖ ≤ 1 / 2 ∧ (1 / 100 : ℝ) ≤ (ModularGroup.S • σ).im ∧
      ‖(σ : ℂ)‖ ≤ 7 ∧ ‖(σ : ℂ)‖ ^ 2 ≤ 37 := by
  obtain ⟨hre1, hre2⟩ := abs_le.mp hre
  have hσim : 0 < σ.im := σ.im_pos
  have hnorm2 : ‖(σ : ℂ)‖ ^ 2 ≤ 37 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    nlinarith
  have hnorm7 : ‖(σ : ℂ)‖ ≤ 7 := by
    nlinarith [norm_nonneg (σ : ℂ)]
  have hge2 : 2 ≤ ‖(σ : ℂ)‖ := by
    calc (2 : ℝ) ≤ σ.im := him2
      _ = |(σ : ℂ).im| := by rw [UpperHalfPlane.coe_im, abs_of_pos hσim]
      _ ≤ ‖(σ : ℂ)‖ := Complex.abs_im_le_norm _
  have hcoenorm : ‖((ModularGroup.S • σ : ℍ) : ℂ)‖ = 1 / ‖(σ : ℂ)‖ := by
    rw [coe_S_smul', norm_inv, norm_neg, one_div]
  have him_S : (ModularGroup.S • σ).im = σ.im / ‖(σ : ℂ)‖ ^ 2 := Work.Asymptotics.im_S σ
  refine ⟨?_, ?_, hnorm7, hnorm2⟩
  · rw [hcoenorm]
    exact one_div_le_one_div_of_le (by norm_num) hge2
  · rw [him_S, le_div_iff₀ (by positivity)]
    nlinarith

/-! ## The main one-zero bound -/

/-- **The uniform one-zero bound for `AfunFun` at the three moving centres `m + σ`.**

For `σ` in the box `{|Re| ≤ 1, 2 ≤ Im ≤ 6}`, `n = ±1` and `m ∈ {-1,0,1}`, the holomorphic
function `z ↦ AfunFun ℓ d (n + S•σ) z` vanishes at the centre `m + σ` (hypothesis `hvanish`
transported through `KfunClear = Δτ Δz^e · AfunFun`, using `S • (S • σ) = σ`), hence is bounded
by a constant times the distance to that centre on a fixed ball.  Since the centre moves with
`σ`, one needs the one-zero lemma `Work.Asymptotics.KL.one_zero_apply` (in `FlatMiddleAux.lean`,
equivalently the copies in `KaxisMid/exists_local_bound_coincidence.lean`) together with a
uniform bound for `AfunFun` on the compact set of `(τ,z)`-pairs: `τ = n +ᵥ (S • σ)` lies in
`{‖τ‖ ≤ 3, 1/100 ≤ Im τ ≤ 3}` (since `‖S•σ‖ = ‖σ‖⁻¹ ≤ 1/2` and `Im (S•σ) = σ.im/‖σ‖² ∈ [2/37, 3/2]`
for `σ` in the box) and the ball of radius `1/2` about `m + σ` lies in
`{‖z‖ ≤ 9, 1/100 ≤ Im z ≤ 9}`.  Take `r = 1/2` and `δ = 1/4`, `C = 4M`. -/
theorem tile_AfunFun_one_zero_centers (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24)
    (hvanish : ∀ (n m : ℤ), (n = 1 ∨ n = -1) → (m = -1 ∨ m = 0 ∨ m = 1) →
      ∀ σ : UpperHalfPlane,
        Work.Kernels.KfunClear ℓ d ((n : ℝ) +ᵥ σ) ((m : ℝ) +ᵥ (ModularGroup.S • σ)) = 0) :
    ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧
      ∀ (σ : UpperHalfPlane), |σ.re| ≤ 1 → 2 ≤ σ.im → σ.im ≤ 6 →
        ∀ (n m : ℤ), (n = 1 ∨ n = -1) → (m = -1 ∨ m = 0 ∨ m = 1) →
          ∀ z : UpperHalfPlane,
            ‖(z : ℂ) - (((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ)‖ ≤ δ →
              ‖Work.Asymptotics.AfunFun ℓ d ((n : ℝ) +ᵥ (ModularGroup.S • σ)) z‖
                ≤ C * ‖(z : ℂ) - (((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ)‖ := by
  obtain ⟨M, hM0, hMb⟩ := exists_bound_AfunFun_box ℓ d
  refine ⟨1 / 8, 4 * M, by norm_num, by positivity, ?_⟩
  intro σ hre him2 him6 n m hn hm z hz
  obtain ⟨hSnorm, hSim, hσ7, -⟩ := S_smul_box_bounds σ hre him2 him6
  have hnabs : |(n : ℝ)| = 1 := by rcases hn with h | h <;> (rw [h]; norm_num)
  have hmabs : |(m : ℝ)| ≤ 1 := by rcases hm with h | h | h <;> (rw [h]; norm_num)
  have hτnorm : ‖(((n : ℝ) +ᵥ (ModularGroup.S • σ) : UpperHalfPlane) : ℂ)‖ ≤ 3 := by
    rw [UpperHalfPlane.coe_vadd]
    calc ‖((n : ℝ) : ℂ) + ((ModularGroup.S • σ : ℍ) : ℂ)‖
        ≤ ‖((n : ℝ) : ℂ)‖ + ‖((ModularGroup.S • σ : ℍ) : ℂ)‖ := norm_add_le _ _
      _ = |(n : ℝ)| + ‖((ModularGroup.S • σ : ℍ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 1 + 1 / 2 := by rw [hnabs]; linarith
      _ ≤ 3 := by norm_num
  have hτim : (1 / 100 : ℝ) ≤ ((n : ℝ) +ᵥ (ModularGroup.S • σ) : UpperHalfPlane).im := by
    rw [UpperHalfPlane.vadd_im]
    exact hSim
  have hcim2 : (2 : ℝ) ≤ ((m : ℝ) +ᵥ σ : UpperHalfPlane).im := by
    rw [UpperHalfPlane.vadd_im]; exact him2
  have hcnorm : ‖(((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ)‖ ≤ 8 := by
    rw [UpperHalfPlane.coe_vadd]
    calc ‖((m : ℝ) : ℂ) + (σ : ℂ)‖ ≤ ‖((m : ℝ) : ℂ)‖ + ‖(σ : ℂ)‖ := norm_add_le _ _
      _ = |(m : ℝ)| + ‖(σ : ℂ)‖ := by rw [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ 1 + 7 := by linarith
      _ ≤ 8 := by norm_num
  have hbd : ∀ w : ℍ, ‖(w : ℂ) - (((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ)‖ ≤ 1 / 2 →
      ‖AfunFun ℓ d ((n : ℝ) +ᵥ (ModularGroup.S • σ)) w‖ ≤ M := by
    intro w hw
    have hwnorm : ‖(w : ℂ)‖ ≤ 9 := by
      have hsplit : (w : ℂ) = ((w : ℂ) - (((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ))
          + (((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ) := by ring
      rw [hsplit]
      calc ‖((w : ℂ) - (((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ))
            + (((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ)‖
          ≤ ‖(w : ℂ) - (((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ)‖
            + ‖(((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ)‖ := norm_add_le _ _
        _ ≤ 9 := by linarith
    have hwim : (1 / 100 : ℝ) ≤ w.im := by
      have h1 : |w.im - (((m : ℝ) +ᵥ σ : UpperHalfPlane)).im|
          ≤ ‖(w : ℂ) - (((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ)‖ := by
        have h2 : ((w : ℂ) - (((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ)).im
            = w.im - (((m : ℝ) +ᵥ σ : UpperHalfPlane)).im := by
          simp only [Complex.sub_im, UpperHalfPlane.coe_im]
        have h3 := Complex.abs_im_le_norm
          ((w : ℂ) - (((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ))
        rwa [h2] at h3
      have h4 : -(1 / 2 : ℝ) ≤ w.im - (((m : ℝ) +ᵥ σ : UpperHalfPlane)).im :=
        (abs_le.mp (le_trans h1 hw)).1
      linarith
    exact hMb ((n : ℝ) +ᵥ (ModularGroup.S • σ)) w hτnorm hτim hwnorm hwim
  have hz0 : AfunFun ℓ d ((n : ℝ) +ᵥ (ModularGroup.S • σ)) ((m : ℝ) +ᵥ σ) = 0 := by
    have hv := hvanish n m hn hm (ModularGroup.S • σ)
    rw [S_smul_S_smul'] at hv
    exact AfunFun_eq_zero_of_KfunClear_eq_zero ℓ d _ _ hv
  have hone := one_zero_apply (c := ((m : ℝ) +ᵥ σ : UpperHalfPlane)) (r := 1 / 2) (M := M)
    (mdifferentiable_AfunFun_snd ℓ d hd ((n : ℝ) +ᵥ (ModularGroup.S • σ))) (by norm_num)
    (by linarith) hbd (w₀ := ((m : ℝ) +ᵥ σ : UpperHalfPlane))
    (by rw [sub_self, norm_zero]; norm_num) hz0
  have hmain := hone z (by linarith)
  have hconst : 2 * M / (1 / 2) = 4 * M := by ring
  rw [hconst] at hmain
  exact hmain

end Work.Asymptotics.Tile

