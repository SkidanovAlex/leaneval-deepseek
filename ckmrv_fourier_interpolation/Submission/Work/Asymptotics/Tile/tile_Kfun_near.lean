import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Kernels
import Submission.Work.Kernels.KernelFacts.KPlus_T2
import Submission.Work.Kernels.KernelFacts.KPlus_S_add
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Asymptotics.KfunClear_vanish_of_phiPair
import Submission.Work.Asymptotics.continuous_AfunFun
import Submission.Work.Asymptotics.Kaxis_tile_aux
import Submission.Work.Asymptotics.MiddleRange.exists_bound_Kfun_of_coincidence
import Submission.Work.Asymptotics.Tile.tile_orbit_classification
import Submission.Work.Asymptotics.Tile.tile_jDiff_linear_compact
import Submission.Work.Asymptotics.Tile.tile_jprime_ne_zero_im_ge_two
import Submission.Work.Asymptotics.Tile.tile_AfunFun_one_zero_centers

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup Matrix
open scoped MatrixGroups UpperHalfPlane

/-!
# The kernel `Kfun` at the cusp-`±1` tiles, compact side

This file proves `Work.Asymptotics.Tile.tile_Kfun_near`: for `w` in the cusp-`0` neighbourhood
`E = KEpsilon` with `Im (S • w) ≤ 6`, the CKMRV kernel `K^{(d)}` is bounded on the contour points
`i t`, `1 ≤ t ≤ 3`, by an absolute constant.

The proof is a compactness argument in the parameter `σ = S • w ∈ {|Re σ| ≤ 1, 2 ≤ Im σ ≤ 6}`
together with the cusp-`±1` tile facts:

* the kernel identity `K^{(d)}(τ,z)·(j τ - j z) = AfunFun τ z` off the coincidence locus
  (`Work.Asymptotics.Kfun_mul_slope_eq_AfunFun`);
* the classification of the coincidences `j σ = j (i t)` with `2 ≤ Im σ`, `t ∈ [1,3]`: they force
  `σ = m + i t`, `m ∈ {-1,0,1}` (`Work.Asymptotics.Tile.tile_orbit_classification`);
* the vanishing of the cleared kernel at the three centres `m + σ` (`hvanish`), which makes
  `z ↦ AfunFun (n + S • σ) z` vanish there and yields, through the one-zero bound
  `Work.Asymptotics.KL.one_zero_apply` (`Work.Asymptotics.Tile.tile_AfunFun_one_zero_centers`), a
  bound linear in the distance to the centre; combined with the uniform linear lower bound for `j`
  (`Work.Asymptotics.Tile.tile_jDiff_linear_compact`) this bounds the quotient
  `AfunFun/(j τ - j z)`.

The three regions are:

* coincidence (`j τ = j z`): `Work.Asymptotics.MiddleRange.exists_bound_Kfun_of_coincidence`;
* near one of the centres `m + σ`: the one-zero estimate divided by the linear lower bound;
* far from all three centres: the uniform bound for `AfunFun` on the compact parameter set divided
  by the uniform separation of `j σ` and `j z` (`exists_far_separation` below, which uses
  `tile_orbit_classification` for the non-vanishing).
-/

noncomputable section

/-! ## The compact boxes -/

/-- The compact `σ`-box `{|Re| ≤ 1, 2 ≤ Im ≤ 6}` on the compact side of the cusp-`±1` tiles. -/
def nearBoxS : Set UpperHalfPlane :=
  {σ : UpperHalfPlane | |σ.re| ≤ 1 ∧ 2 ≤ σ.im ∧ σ.im ≤ 6}

/-- The `τ`-box: contains all `n +ᵥ (S • σ)` for `σ ∈ nearBoxS` and `n = ±1`. -/
def nearBoxT : Set UpperHalfPlane :=
  {τ : UpperHalfPlane | ‖(τ : ℂ)‖ ≤ 2 ∧ 1 / 100 ≤ τ.im ∧ τ.im ≤ 3}

/-- The `z`-box: contains the contour points `i t` (`1 ≤ t ≤ 3`) and the one-zero balls. -/
def nearBoxZ : Set UpperHalfPlane :=
  {z : UpperHalfPlane | ‖(z : ℂ)‖ ≤ 9 ∧ 1 / 100 ≤ z.im ∧ z.im ≤ 9}

/-- The box containing the three centres `m + σ`, `m ∈ {-1,0,1}`. -/
def nearBoxP : Set UpperHalfPlane :=
  {ρ : UpperHalfPlane | |ρ.re| ≤ 2 ∧ 2 ≤ ρ.im ∧ ρ.im ≤ 6}

/-- The segment `i [1,3]` of the imaginary axis. -/
def nearSeg13 : Set UpperHalfPlane :=
  {z : UpperHalfPlane | z.re = 0 ∧ 1 ≤ z.im ∧ z.im ≤ 3}

/-! ## Compactness of the boxes

The metric on `ℍ` is the hyperbolic one, so compactness of the Euclidean boxes is proved on the
image in `ℂ` (a closed and bounded set of the Euclidean plane) and transported back along the
embedding `UpperHalfPlane.coe`. -/

private lemma isCompact_boxC_reIm (a b R : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hR : 0 ≤ R) :
    IsCompact {x : ℂ | |x.re| ≤ a ∧ b ≤ x.im ∧ x.im ≤ R} := by
  refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
  · have h1 : IsClosed {x : ℂ | |x.re| ≤ a} :=
      isClosed_le (continuous_abs.comp Complex.continuous_re) continuous_const
    have h2 : IsClosed {x : ℂ | b ≤ x.im} :=
      isClosed_le continuous_const Complex.continuous_im
    have h3 : IsClosed {x : ℂ | x.im ≤ R} :=
      isClosed_le Complex.continuous_im continuous_const
    have h : {x : ℂ | |x.re| ≤ a ∧ b ≤ x.im ∧ x.im ≤ R}
        = {x : ℂ | |x.re| ≤ a} ∩ {x : ℂ | b ≤ x.im} ∩ {x : ℂ | x.im ≤ R} := by
      ext x; simp [and_assoc]
    rw [h]; exact (h1.inter h2).inter h3
  · refine (Metric.isBounded_closedBall (x := 0) (r := a + R)).subset ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    have hsq : ‖x‖ ^ 2 = x.re ^ 2 + x.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]; ring
    have him2 : x.im ^ 2 ≤ R ^ 2 := by nlinarith [hx.2.1, hx.2.2, hb]
    have hre2 : x.re ^ 2 ≤ a ^ 2 := by
      have h := abs_le.mp hx.1
      nlinarith [h.1, h.2]
    have hle : ‖x‖ ^ 2 ≤ (a + R) ^ 2 := by
      nlinarith [hsq, him2, hre2, ha, hR, norm_nonneg x]
    have h3 := Real.sqrt_le_sqrt hle
    rwa [Real.sqrt_sq (norm_nonneg x), Real.sqrt_sq (by linarith)] at h3

private lemma isCompact_boxC_norm (R b c : ℝ) (hb : 0 ≤ b) :
    IsCompact {x : ℂ | ‖x‖ ≤ R ∧ b ≤ x.im ∧ x.im ≤ c} := by
  refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
  · have h1 : IsClosed {x : ℂ | ‖x‖ ≤ R} :=
      isClosed_le continuous_norm continuous_const
    have h2 : IsClosed {x : ℂ | b ≤ x.im} :=
      isClosed_le continuous_const Complex.continuous_im
    have h3 : IsClosed {x : ℂ | x.im ≤ c} :=
      isClosed_le Complex.continuous_im continuous_const
    have h : {x : ℂ | ‖x‖ ≤ R ∧ b ≤ x.im ∧ x.im ≤ c}
        = {x : ℂ | ‖x‖ ≤ R} ∩ {x : ℂ | b ≤ x.im} ∩ {x : ℂ | x.im ≤ c} := by
      ext x; simp [and_assoc]
    rw [h]; exact (h1.inter h2).inter h3
  · exact (Metric.isBounded_closedBall (x := 0) (r := R)).subset
      (fun x hx => by rw [Metric.mem_closedBall, dist_zero_right]; exact hx.1)

private lemma isCompact_boxC_seg :
    IsCompact {x : ℂ | x.re = 0 ∧ 1 ≤ x.im ∧ x.im ≤ 3} := by
  refine Metric.isCompact_iff_isClosed_bounded.mpr ⟨?_, ?_⟩
  · have h1 : IsClosed {x : ℂ | x.re = 0} :=
      isClosed_eq Complex.continuous_re continuous_const
    have h2 : IsClosed {x : ℂ | 1 ≤ x.im} :=
      isClosed_le continuous_const Complex.continuous_im
    have h3 : IsClosed {x : ℂ | x.im ≤ 3} :=
      isClosed_le Complex.continuous_im continuous_const
    have h : {x : ℂ | x.re = 0 ∧ 1 ≤ x.im ∧ x.im ≤ 3}
        = {x : ℂ | x.re = 0} ∩ {x : ℂ | 1 ≤ x.im} ∩ {x : ℂ | x.im ≤ 3} := by
      ext x; simp [and_assoc]
    rw [h]; exact (h1.inter h2).inter h3
  · refine (Metric.isBounded_closedBall (x := 0) (r := 3)).subset ?_
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    have hcoe : x = Complex.I * (x.im : ℂ) := by
      have h : (x.im : ℂ) * Complex.I = x := by
        have h0 := (Complex.re_add_im x).symm
        rw [hx.1, Complex.ofReal_zero, zero_add] at h0
        exact h0.symm
      exact h.symm.trans (mul_comm _ _)
    rw [hcoe, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (le_trans (by norm_num) hx.2.1)]
    exact hx.2.2

private lemma isCompact_of_coe_image {K : Set UpperHalfPlane} {s : Set ℂ}
    (hs : IsCompact s) (h : (UpperHalfPlane.coe '' K) = s) : IsCompact K :=
  (UpperHalfPlane.isEmbedding_coe.isCompact_iff).mpr (by rw [h]; exact hs)

lemma isCompact_nearBoxS : IsCompact nearBoxS := by
  refine isCompact_of_coe_image (isCompact_boxC_reIm 1 2 6 (by norm_num) (by norm_num)
    (by norm_num)) ?_
  ext x; constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨hz.1, hz.2.1, hz.2.2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨x, by linarith⟩, ⟨h1, h2, h3⟩, rfl⟩

lemma isCompact_nearBoxP : IsCompact nearBoxP := by
  refine isCompact_of_coe_image (isCompact_boxC_reIm 2 2 6 (by norm_num) (by norm_num)
    (by norm_num)) ?_
  ext x; constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨hz.1, hz.2.1, hz.2.2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨x, by linarith⟩, ⟨h1, h2, h3⟩, rfl⟩

lemma isCompact_nearBoxT : IsCompact nearBoxT := by
  refine isCompact_of_coe_image (isCompact_boxC_norm 2 (1 / 100) 3 (by norm_num)) ?_
  ext x; constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨hz.1, hz.2.1, hz.2.2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨x, by linarith⟩, ⟨h1, h2, h3⟩, rfl⟩

lemma isCompact_nearBoxZ : IsCompact nearBoxZ := by
  refine isCompact_of_coe_image (isCompact_boxC_norm 9 (1 / 100) 9 (by norm_num)) ?_
  ext x; constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨hz.1, hz.2.1, hz.2.2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨x, by linarith⟩, ⟨h1, h2, h3⟩, rfl⟩

lemma isCompact_nearSeg13 : IsCompact nearSeg13 := by
  refine isCompact_of_coe_image isCompact_boxC_seg ?_
  ext x; constructor
  · rintro ⟨z, hz, rfl⟩; exact ⟨hz.1, hz.2.1, hz.2.2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨x, by linarith⟩, ⟨h1, h2, h3⟩, rfl⟩

/-! ## Membership in the boxes -/

/-- `j` is unchanged by the translation `n +ᵥ ·` for `n = ±1`. -/
lemma jInvariantFun_vadd_int_one (n : ℤ) (hn : n = 1 ∨ n = -1) (w : UpperHalfPlane) :
    Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ w) = Work.Kernels.jInvariantFun w := by
  rcases hn with h | h
  · subst h
    push_cast
    exact Work.Kernels.KernelFacts.jInvariantFun_vadd_one w
  · subst h
    push_cast
    have h1 := Work.Kernels.KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ w)
    rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ w) = w by rw [← add_vadd]; norm_num] at h1
    exact h1.symm

/-- The three centres `m +ᵥ σ`, `m ∈ {-1,0,1}`, of `σ ∈ nearBoxS` lie in `nearBoxP`. -/
lemma vadd_mem_nearBoxP {σ : UpperHalfPlane} (hσ : σ ∈ nearBoxS) {m : ℤ}
    (hm : m = -1 ∨ m = 0 ∨ m = 1) : ((m : ℝ) +ᵥ σ) ∈ nearBoxP := by
  obtain ⟨h1, h2, h3⟩ := hσ
  have hre : ((m : ℝ) +ᵥ σ).re = (m : ℝ) + σ.re := by
    rw [← UpperHalfPlane.coe_re (z := ((m : ℝ) +ᵥ σ)), UpperHalfPlane.coe_vadd]
    simp
  have him : ((m : ℝ) +ᵥ σ).im = σ.im := UpperHalfPlane.vadd_im _ _
  refine ⟨?_, ?_, ?_⟩
  · rw [hre]
    rcases hm with h | h | h
    · subst h; push_cast; rw [abs_le] at h1 ⊢; constructor <;> linarith
    · subst h; push_cast; rw [abs_le] at h1 ⊢; constructor <;> linarith
    · subst h; push_cast; rw [abs_le] at h1 ⊢; constructor <;> linarith
  · rw [him]; exact h2
  · rw [him]; exact h3

/-- `n +ᵥ (S • σ)` lies in `nearBoxT` for `σ ∈ nearBoxS` and `n = ±1`. -/
lemma vadd_S_mem_nearBoxT (n : ℤ) (hn : n = 1 ∨ n = -1) {σ : UpperHalfPlane}
    (hσ : σ ∈ nearBoxS) : ((n : ℝ) +ᵥ (ModularGroup.S • σ)) ∈ nearBoxT := by
  obtain ⟨h1, h2, h3⟩ := hσ
  set τ : UpperHalfPlane := (n : ℝ) +ᵥ (ModularGroup.S • σ) with hτdef
  have hτcoe : (τ : ℂ) = (n : ℂ) + ((ModularGroup.S • σ : UpperHalfPlane) : ℂ) := by
    rw [hτdef, UpperHalfPlane.coe_vadd, Complex.ofReal_intCast]
  have hτim : τ.im = (ModularGroup.S • σ).im := by rw [hτdef, UpperHalfPlane.vadd_im]
  have hsq : ‖(σ : ℂ)‖ ^ 2 = σ.re ^ 2 + σ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
    ring
  have hre : σ.re ^ 2 ≤ 1 := by
    have h := abs_le.mp h1
    nlinarith [h.1, h.2]
  have him2 : σ.im ^ 2 ≤ 36 := by nlinarith
  have hσnorm : (2 : ℝ) ≤ ‖(σ : ℂ)‖ := by
    have h : (2 : ℝ) ^ 2 ≤ ‖(σ : ℂ)‖ ^ 2 := by nlinarith [hsq, h2]
    nlinarith [norm_nonneg (σ : ℂ), h]
  have hσnorm37 : ‖(σ : ℂ)‖ ^ 2 ≤ 37 := by nlinarith [hsq, hre, him2]
  have hScoe : ((ModularGroup.S • σ : UpperHalfPlane) : ℂ) = -((σ : ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
  have hSnorm : ‖((ModularGroup.S • σ : UpperHalfPlane) : ℂ)‖ = (‖(σ : ℂ)‖)⁻¹ := by
    rw [hScoe, norm_neg, norm_inv]
  have hSim : (ModularGroup.S • σ).im = σ.im / ‖(σ : ℂ)‖ ^ 2 :=
    Work.Asymptotics.im_S_smul_eq σ
  have hS1 : (‖(σ : ℂ)‖)⁻¹ ≤ 1 / 2 := by
    have h := (inv_le_inv₀ (by linarith : (0 : ℝ) < ‖(σ : ℂ)‖)
      (by norm_num : (0 : ℝ) < 2)).mpr hσnorm
    have h2 : (2 : ℝ)⁻¹ = 1 / 2 := by norm_num
    rwa [h2] at h
  have hnn : ‖(n : ℂ)‖ = 1 := by
    rw [Complex.norm_intCast]
    rcases hn with h | h <;> (rw [h]; norm_num)
  have hpos37 : 0 < ‖(σ : ℂ)‖ ^ 2 := by positivity
  have h4 : (4 : ℝ) ≤ ‖(σ : ℂ)‖ ^ 2 := by nlinarith [hσnorm, norm_nonneg (σ : ℂ)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hτcoe]
    calc ‖(n : ℂ) + ((ModularGroup.S • σ : UpperHalfPlane) : ℂ)‖
        ≤ ‖(n : ℂ)‖ + ‖((ModularGroup.S • σ : UpperHalfPlane) : ℂ)‖ := norm_add_le _ _
      _ = 1 + (‖(σ : ℂ)‖)⁻¹ := by rw [hnn, hSnorm]
      _ ≤ 2 := by linarith
  · rw [hτim, hSim, le_div_iff₀ hpos37]
    nlinarith
  · rw [hτim, hSim, div_le_iff₀ hpos37]
    nlinarith

/-- The contour points `i t`, `1 ≤ t ≤ 3`, lie in `nearBoxZ`. -/
lemma imagAxis_mem_nearBoxZ {t : ℝ} (ht : 0 < t) (h1 : 1 ≤ t) (h3 : t ≤ 3) :
    Work.Kernels.imagAxis t ht ∈ nearBoxZ := by
  have hcoe : ((Work.Kernels.imagAxis t ht : UpperHalfPlane) : ℂ) = (t : ℂ) * Complex.I := rfl
  have him : (Work.Kernels.imagAxis t ht).im = t := by simp [Work.Kernels.imagAxis]
  refine ⟨?_, ?_, ?_⟩
  · rw [hcoe, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht]
    linarith
  · rw [him]; linarith
  · rw [him]; linarith

/-! ## A uniform bound for `AfunFun` on the compact parameter set -/

lemma exists_bound_AfunFun_nearBox (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) :
    ∃ M : ℝ, 0 < M ∧ ∀ τ ∈ nearBoxT, ∀ z ∈ nearBoxZ,
      ‖Work.Asymptotics.AfunFun ℓ d τ z‖ ≤ M := by
  obtain ⟨C, hC⟩ := (isCompact_nearBoxT.prod isCompact_nearBoxZ).exists_bound_of_continuousOn
    ((Work.Asymptotics.continuous_AfunFun ℓ d).continuousOn)
  refine ⟨max C 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro τ hτ z hz
  exact le_trans (hC (τ, z) ⟨hτ, hz⟩) (le_max_left _ _)

/-! ## Uniform separation of `j` far from the three centres -/

/-- The parameter set of the "far" region: `σ ∈ nearBoxS`, `z ∈ nearSeg13` and `z` at distance
at least `δ` from each of the three centres `m + σ`, `m ∈ {-1,0,1}` (written in `ℂ`). -/
private def nearFarSet (δ : ℝ) : Set (UpperHalfPlane × UpperHalfPlane) :=
  {p | p.1 ∈ nearBoxS} ∩ {p | p.2 ∈ nearSeg13} ∩
    {p | δ ≤ ‖(p.2 : ℂ) - ((-1 : ℂ) + (p.1 : ℂ))‖} ∩
    {p | δ ≤ ‖(p.2 : ℂ) - ((0 : ℂ) + (p.1 : ℂ))‖} ∩
    {p | δ ≤ ‖(p.2 : ℂ) - ((1 : ℂ) + (p.1 : ℂ))‖}

private lemma mem_nearFarSet {δ : ℝ} {p : UpperHalfPlane × UpperHalfPlane} :
    p ∈ nearFarSet δ ↔ p.1 ∈ nearBoxS ∧ p.2 ∈ nearSeg13 ∧
      δ ≤ ‖(p.2 : ℂ) - ((-1 : ℂ) + (p.1 : ℂ))‖ ∧
      δ ≤ ‖(p.2 : ℂ) - ((0 : ℂ) + (p.1 : ℂ))‖ ∧
      δ ≤ ‖(p.2 : ℂ) - ((1 : ℂ) + (p.1 : ℂ))‖ := by
  unfold nearFarSet
  constructor
  · intro h
    exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩
  · intro h
    exact ⟨⟨⟨⟨h.1, h.2.1⟩, h.2.2.1⟩, h.2.2.2.1⟩, h.2.2.2.2⟩

set_option maxHeartbeats 8000000 in
/-- **Uniform separation of `j σ` and `j z` far from the three centres.**

For `σ ∈ nearBoxS` and `z` on the segment `{Re = 0, 1 ≤ Im ≤ 3}` at distance at least `δ > 0`
from each of the three centres `m + σ`, `m ∈ {-1,0,1}`, the `j`-values of `σ` and `z` are
separated by a positive constant depending only on `δ`.

Compactness of the parameter set together with `tile_orbit_classification` (a coincidence
`j σ = j z` forces `z = m + σ` for some `m ∈ {-1,0,1}`, contradicting the distance conditions)
gives the non-vanishing; the minimum of the continuous function `‖j σ - j z‖` over the closed
parameter set is then positive. -/
lemma exists_far_separation (δ : ℝ) (hδ : 0 < δ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (σ z : UpperHalfPlane),
      σ ∈ nearBoxS → z.re = 0 → 1 ≤ z.im → z.im ≤ 3 →
      δ ≤ ‖(z : ℂ) - ((-1 : ℂ) + (σ : ℂ))‖ →
      δ ≤ ‖(z : ℂ) - ((0 : ℂ) + (σ : ℂ))‖ →
      δ ≤ ‖(z : ℂ) - ((1 : ℂ) + (σ : ℂ))‖ →
      c ≤ ‖Work.Kernels.jInvariantFun σ - Work.Kernels.jInvariantFun z‖ := by
  set S : Set (UpperHalfPlane × UpperHalfPlane) := nearFarSet δ with hSdef
  have hdistcont : ∀ m : ℂ, Continuous (fun p : UpperHalfPlane × UpperHalfPlane =>
      ‖(p.2 : ℂ) - (m + (p.1 : ℂ))‖) := by
    intro m
    exact ((UpperHalfPlane.continuous_coe.comp continuous_snd).sub
      (continuous_const.add (UpperHalfPlane.continuous_coe.comp continuous_fst))).norm
  have hclosed : IsClosed S := by
    rw [hSdef]
    unfold nearFarSet
    exact ((((isCompact_nearBoxS.isClosed.preimage continuous_fst).inter
      (isCompact_nearSeg13.isClosed.preimage continuous_snd)).inter
      (isClosed_le continuous_const (hdistcont (-1)))).inter
      (isClosed_le continuous_const (hdistcont 0))).inter
      (isClosed_le continuous_const (hdistcont 1))
  have hsub : S ⊆ nearBoxS ×ˢ nearSeg13 := by
    intro p hp
    rw [hSdef, mem_nearFarSet] at hp
    exact ⟨hp.1, hp.2.1⟩
  have hcomp : IsCompact S :=
    (isCompact_nearBoxS.prod isCompact_nearSeg13).of_isClosed_subset hclosed hsub
  have hno : ∀ p ∈ S, Work.Kernels.jInvariantFun p.1
      ≠ Work.Kernels.jInvariantFun p.2 := by
    intro p hp heq
    rw [hSdef, mem_nearFarSet] at hp
    obtain ⟨hσ, hz, hd1, hd0, hd1'⟩ := hp
    have hzre : (p.2 : ℂ).re = 0 := by rw [UpperHalfPlane.coe_re]; exact hz.1
    have hz_eq : p.2 = Work.Kernels.imagAxis p.2.im p.2.im_pos :=
      eq_imagAxis_of_re_eq_zero' hzre
    have heq' : Work.Kernels.jInvariantFun p.1
        = Work.Kernels.jInvariantFun (Work.Kernels.imagAxis p.2.im p.2.im_pos) :=
      heq.trans (congrArg Work.Kernels.jInvariantFun hz_eq.symm).symm
    obtain ⟨m, hm, hmz⟩ := tile_orbit_classification hσ.1 hσ.2.1 p.2.im p.2.im_pos hz.2.1 hz.2.2
      heq'
    have hz_eq2 : p.2 = ((-m : ℤ) : ℝ) +ᵥ p.1 := by
      rw [← hz_eq] at hmz
      refine UpperHalfPlane.ext ?_
      have h1 : (p.1 : ℂ) = ((m : ℝ) : ℂ) + (p.2 : ℂ) := by
        have h := congrArg (fun t : UpperHalfPlane => (t : ℂ)) hmz
        rwa [UpperHalfPlane.coe_vadd] at h
      rw [UpperHalfPlane.coe_vadd, h1]
      push_cast
      ring
    have hneg : (-m) = -1 ∨ (-m) = 0 ∨ (-m) = 1 := by
      rcases hm with h | h | h <;> simp [h]
    have hdall : ∀ k : ℤ, (k = -1 ∨ k = 0 ∨ k = 1) →
        δ ≤ ‖(p.2 : ℂ) - ((k : ℂ) + (p.1 : ℂ))‖ := by
      intro k hk
      rcases hk with h | h | h
      · subst h; simpa using hd1
      · subst h; simpa using hd0
      · subst h; simpa using hd1'
    have hdist := hdall (-m) hneg
    have hzero : ‖(p.2 : ℂ) - (((-m : ℤ) : ℂ) + (p.1 : ℂ))‖ = 0 := by
      have hzcoe : (p.2 : ℂ) = (((-m : ℤ) : ℝ) : ℂ) + (p.1 : ℂ) := by
        rw [← UpperHalfPlane.coe_vadd]
        exact congrArg (fun t : UpperHalfPlane => (t : ℂ)) hz_eq2
      rw [hzcoe, Complex.ofReal_intCast, sub_self, norm_zero]
    rw [hzero] at hdist
    linarith [hδ, hdist]
  have hjC : Continuous Work.Kernels.jInvariantFun :=
    Work.Asymptotics.MiddleRange.continuous_jInvariantFun
  set F : UpperHalfPlane × UpperHalfPlane → ℝ :=
    fun q => ‖Work.Kernels.jInvariantFun q.1 - Work.Kernels.jInvariantFun q.2‖ with hFdef
  have hcont : Continuous F := by
    rw [hFdef]
    exact ((hjC.comp continuous_fst).sub (hjC.comp continuous_snd)).norm
  rcases Set.eq_empty_or_nonempty S with hempty | hne
  · refine ⟨1, one_pos, fun σ z hσ hz h1 h3 hd1 hd0 hd1' => ?_⟩
    exfalso
    have hmem : ((σ, z) : UpperHalfPlane × UpperHalfPlane) ∈ S := by
      rw [hSdef, mem_nearFarSet]
      exact ⟨hσ, ⟨hz, h1, h3⟩, hd1, hd0, hd1'⟩
    rw [hempty] at hmem
    exact hmem
  · obtain ⟨p, hpS, hmin⟩ := hcomp.exists_isMinOn (f := F) hne hcont.continuousOn
    refine ⟨F p, norm_pos_iff.mpr (sub_ne_zero.mpr (hno p hpS)), ?_⟩
    intro σ z hσ hz h1 h3 hd1 hd0 hd1'
    have hmem : ((σ, z) : UpperHalfPlane × UpperHalfPlane) ∈ S := by
      rw [hSdef, mem_nearFarSet]
      exact ⟨hσ, ⟨hz, h1, h3⟩, hd1, hd0, hd1'⟩
    have hle := hmin hmem
    exact hle

/-! ## The main theorem -/

set_option maxHeartbeats 8000000 in
theorem tile_Kfun_near (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (hvanish : ∀ (n m : ℤ), (n = 1 ∨ n = -1) → (m = -1 ∨ m = 0 ∨ m = 1) → ∀ σ : UpperHalfPlane,
      Work.Kernels.KfunClear ℓ d ((n : ℝ) +ᵥ σ) ((m : ℝ) +ᵥ (ModularGroup.S • σ)) = 0) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (w : UpperHalfPlane), w ∈ Work.Asymptotics.KEpsilon → (ModularGroup.S • w).im ≤ 6 →
      ∀ n : ℤ, (n = 1 ∨ n = -1) → ∀ (t : ℝ) (ht : 0 < t), 1 ≤ t → t ≤ 3 →
        ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖ ≤ C := by
  -- the five inputs
  obtain ⟨δ₁, C₁, hδ₁, hC₁, hone⟩ := tile_AfunFun_one_zero_centers ℓ d hd hvanish
  obtain ⟨c₂, δ₂, hc₂, hδ₂, hlin⟩ :=
    tile_jDiff_linear_compact isCompact_nearBoxP
      (fun ρ hρ => tile_jprime_ne_zero_im_ge_two ρ hρ.2.1)
  obtain ⟨M, hM, hAbound⟩ := exists_bound_AfunFun_nearBox ℓ d
  obtain ⟨c₃, hc₃, hfar⟩ := exists_far_separation (min δ₁ δ₂) (lt_min hδ₁ hδ₂)
  obtain ⟨C_c, hC_c, hcoin⟩ :=
    Work.Asymptotics.MiddleRange.exists_bound_Kfun_of_coincidence ℓ d hd
      isCompact_nearBoxT isCompact_nearBoxZ
  -- the constant
  have hCmax : 0 < max 1 (max C_c (max (C₁ / c₂) (M / c₃))) :=
    lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hCcle : C_c ≤ max 1 (max C_c (max (C₁ / c₂) (M / c₃))) :=
    le_trans (le_max_left _ _) (le_max_of_le_right le_rfl)
  have hC₁le : C₁ / c₂ ≤ max 1 (max C_c (max (C₁ / c₂) (M / c₃))) :=
    le_trans (le_max_left _ _)
      (le_trans (le_max_of_le_right le_rfl) (le_max_of_le_right le_rfl))
  have hMle : M / c₃ ≤ max 1 (max C_c (max (C₁ / c₂) (M / c₃))) :=
    le_trans (le_max_right _ _)
      (le_trans (le_max_of_le_right le_rfl) (le_max_of_le_right le_rfl))
  refine ⟨max 1 (max C_c (max (C₁ / c₂) (M / c₃))), hCmax, ?_⟩
  intro w hwE hsim n hn t ht h1 h3
  set σ : UpperHalfPlane := ModularGroup.S • w with hσdef
  have hw_eq : w = ModularGroup.S • σ := by rw [hσdef, S_smul_S_smul]
  have hσD : σ ∈ Work.Asymptotics.DomainD := Work.Asymptotics.S_smul_mem_DomainD hwE.1
  have hσbox : σ ∈ nearBoxS :=
    ⟨le_of_lt (abs_lt.mpr ⟨hσD.1, hσD.2.1⟩), hwE.2, hsim⟩
  set z : UpperHalfPlane := Work.Kernels.imagAxis t ht with hzdef
  have hzbox : z ∈ nearBoxZ := imagAxis_mem_nearBoxZ ht h1 h3
  have hzre : z.re = 0 := by rw [hzdef]; simp [Work.Kernels.imagAxis]
  have hzim : z.im = t := by rw [hzdef]; simp [Work.Kernels.imagAxis]
  have hτbox : ((n : ℝ) +ᵥ (ModularGroup.S • σ)) ∈ nearBoxT := vadd_S_mem_nearBoxT n hn hσbox
  have hjτ : Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ (ModularGroup.S • σ))
      = Work.Kernels.jInvariantFun σ := by
    rw [jInvariantFun_vadd_int_one n hn (ModularGroup.S • σ),
      Work.Kernels.KernelFacts.jInvariantFun_S_smul]
  have harg : ((n : ℝ) +ᵥ w) = ((n : ℝ) +ᵥ (ModularGroup.S • σ)) := by rw [hw_eq]
  rw [harg]
  -- `j (m + σ) = j τ` for the three centres
  have hjρ : ∀ m : ℤ, (m = -1 ∨ m = 0 ∨ m = 1) →
      Work.Kernels.jInvariantFun ((m : ℝ) +ᵥ σ)
        = Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ (ModularGroup.S • σ)) := by
    intro m hm
    rw [hjτ]
    rcases hm with h | h | h
    · subst h
      exact jInvariantFun_vadd_int_one (-1) (Or.inr rfl) σ
    · subst h
      simp
    · subst h
      exact jInvariantFun_vadd_int_one 1 (Or.inl rfl) σ
  rcases eq_or_ne (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ (ModularGroup.S • σ)))
      (Work.Kernels.jInvariantFun z) with hj | hj
  · exact le_trans (hcoin ((n : ℝ) +ᵥ (ModularGroup.S • σ)) z hτbox hzbox hj) hCcle
  · -- the master identity
    have hid := Work.Asymptotics.Kfun_mul_slope_eq_AfunFun ℓ d hd
      ((n : ℝ) +ᵥ (ModularGroup.S • σ)) z hj
    have hnorm_eq : ‖Work.Kernels.Kfun ℓ d ((n : ℝ) +ᵥ (ModularGroup.S • σ)) z‖
        = ‖Work.Asymptotics.AfunFun ℓ d ((n : ℝ) +ᵥ (ModularGroup.S • σ)) z‖
          / ‖Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ (ModularGroup.S • σ))
              - Work.Kernels.jInvariantFun z‖ := by
      rw [eq_div_iff (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hj)), ← hid, norm_mul]
    by_cases hnear : ∃ m : ℤ, (m = -1 ∨ m = 0 ∨ m = 1) ∧
        ‖(z : ℂ) - (((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ)‖ ≤ min δ₁ δ₂
    · obtain ⟨m, hm, hdist⟩ := hnear
      have hδm₁ : ‖(z : ℂ) - (((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ)‖ ≤ δ₁ :=
        le_trans hdist (min_le_left _ _)
      have hδm₂ : ‖(z : ℂ) - (((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ)‖ ≤ δ₂ :=
        le_trans hdist (min_le_right _ _)
      have hpos : 0 < ‖(z : ℂ) - (((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ)‖ := by
        rcases eq_or_lt_of_le
          (norm_nonneg ((z : ℂ) - (((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ))) with h0 | h0
        · exfalso
          apply hj
          have hzeq : z = ((m : ℝ) +ᵥ σ) := by
            refine UpperHalfPlane.ext ?_
            have hz' := norm_eq_zero.mp h0.symm
            exact sub_eq_zero.mp hz'
          rw [hzeq]
          exact (hjρ m hm).symm
        · exact h0
      have hone' : ‖Work.Asymptotics.AfunFun ℓ d ((n : ℝ) +ᵥ (ModularGroup.S • σ)) z‖
          ≤ C₁ * ‖(z : ℂ) - (((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ)‖ :=
        hone σ hσbox.1 hσbox.2.1 hσbox.2.2 n m hn hm z hδm₁
      have hlin' : c₂ * ‖(z : ℂ) - (((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ)‖
          ≤ ‖Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ (ModularGroup.S • σ))
              - Work.Kernels.jInvariantFun z‖ := by
        have hl := hlin ((m : ℝ) +ᵥ σ) (vadd_mem_nearBoxP hσbox hm) z hδm₂
        rw [hjρ m hm,
          norm_sub_rev (Work.Kernels.jInvariantFun z)
            (Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ (ModularGroup.S • σ)))] at hl
        exact hl
      rw [hnorm_eq]
      calc ‖Work.Asymptotics.AfunFun ℓ d ((n : ℝ) +ᵥ (ModularGroup.S • σ)) z‖
            / ‖Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ (ModularGroup.S • σ))
                - Work.Kernels.jInvariantFun z‖
          ≤ (C₁ * ‖(z : ℂ) - (((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ)‖)
            / (c₂ * ‖(z : ℂ) - (((m : ℝ) +ᵥ σ : UpperHalfPlane) : ℂ)‖) :=
            div_le_div₀ (by positivity) hone' (by positivity) hlin'
        _ = C₁ / c₂ := by
            rw [mul_div_mul_right _ _ (ne_of_gt hpos)]
        _ ≤ max 1 (max C_c (max (C₁ / c₂) (M / c₃))) := hC₁le
    · push_neg at hnear
      have hfar' : c₃ ≤ ‖Work.Kernels.jInvariantFun σ - Work.Kernels.jInvariantFun z‖ :=
        hfar σ z hσbox hzre (by rw [hzim]; exact h1) (by rw [hzim]; exact h3)
          (by
            have h := hnear (-1) (Or.inl rfl)
            rw [UpperHalfPlane.coe_vadd, Complex.ofReal_intCast] at h
            push_cast at h
            exact le_of_lt h)
          (by
            have h := hnear 0 (Or.inr (Or.inl rfl))
            rw [UpperHalfPlane.coe_vadd, Complex.ofReal_intCast] at h
            push_cast at h
            exact le_of_lt h)
          (by
            have h := hnear 1 (Or.inr (Or.inr rfl))
            rw [UpperHalfPlane.coe_vadd, Complex.ofReal_intCast] at h
            push_cast at h
            exact le_of_lt h)
      have hfar'' : c₃ ≤ ‖Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ (ModularGroup.S • σ))
          - Work.Kernels.jInvariantFun z‖ := by rw [hjτ]; exact hfar'
      have hAb := hAbound _ hτbox _ hzbox
      rw [hnorm_eq]
      calc ‖Work.Asymptotics.AfunFun ℓ d ((n : ℝ) +ᵥ (ModularGroup.S • σ)) z‖
            / ‖Work.Kernels.jInvariantFun ((n : ℝ) +ᵥ (ModularGroup.S • σ))
                - Work.Kernels.jInvariantFun z‖
          ≤ M / c₃ := div_le_div₀ (le_of_lt hM) hAb hc₃ hfar''
        _ ≤ max 1 (max C_c (max (C₁ / c₂) (M / c₃))) := hMle

end

end Work.Asymptotics.Tile
