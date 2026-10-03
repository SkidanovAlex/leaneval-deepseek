/-
# The small-scale estimate: the Rademacher--Menshov reduction of Section 8

This module formalises the *reduction step* of Section 8 of Krause--Mirek--Tao, *Pointwise
ergodic theorems for non-conventional bilinear polynomial averages*, Annals 195 (2022) —
the passage from the two-dimensional Rademacher--Menshov inequality (their Lemma `2drm`) and its
bilinear corollary (their Corollary `rm-bil`) to the small-scale model estimate
`(other-small-2)`.

The mathematical content of `(other-small-2)` is this.  One is given a family
`(B(f_N, g_N))_{N ∈ I_sml}` of bilinear expressions, where the *bilinear operator* `B` is
**independent of the scale `N`**, while the two arguments `f_N = T_{φ_N} F`, `g_N = T_{ψ_N} G`
depend on `N` through a family of linear Fourier multiplier operators `T` (additive in the
symbol).  Corollary `rm-bil` then bounds the `V²`-variational norm of the family by the
supremum, over all choices of Rademacher signs `ε_k, ε'_k ∈ [-1,1]`, of the *single* expression
obtained by applying `B` to the randomised combinations
`∑_k ε_k (f_{k+1} - f_k) = T_{∑_k ε_k • (φ_{k+1} - φ_k)} F`,
`∑_k ε'_k (g_{k+1} - g_k) = T_{∑_k ε'_k • (ψ_{k+1} - ψ_k)} G`
— the point being that linearity of `T` in the symbol turns the randomised combination of the
family into a *single* multiplier applied to a randomised cut-off.  Hence a uniform single-scale
bound on `B(T_{φ_*}F, T_{ψ_*}G)` for all randomised cut-offs `φ_*, ψ_*` gives the small-scale
model estimate.

## Status of the inputs

The Rademacher--Menshov inequalities themselves (`2drm`, `rm-bil`) are being proved by the
colleague owning `Submission/Work/Analysis/Variation/`.  Since that API is not yet available, the
bilinear corollary is taken here as an **explicit hypothesis** (`RademacherMenshovBilinear`,
matching the shape of `Work.Analysis.Variation.rademacher_menshov_bilinear`) and the reduction
*below* it is proved; nothing is postulated as an axiom.

## Main definitions and results

* `RademacherMenshovBilinear B μ q` : the paper's Corollary `rm-bil`, as an explicit hypothesis;
* `Tm_finset_sum_smul` : linearity of the multiplier family in its symbol;
* `smallScale_variational_le` : the Section 8 reduction: `rm-bil` + a uniform randomised
  single-scale bound imply the `V²` small-scale model estimate;
* `variationalNorm_mono_of_two_le` : `V^r ≤ V^2` for `r ≥ 2`, which passes the `V²` estimate to
  the exponents `r > 2` used in the paper.
-/
import Mathlib
import Submission.VarNorm
import Submission.Work.Analysis.Paraproduct.WithLp_toLp_norm_mono
import Submission.Port.Aesm

set_option autoImplicit false

open scoped BigOperators ENNReal NNReal
open Finset MeasureTheory

namespace Work.Analysis.Paraproduct

noncomputable section

variable {𝓧 : Type*} [MeasurableSpace 𝓧]

/-- **The paper's Corollary `rm-bil`** (Rademacher--Menshov for bilinear forms), as an explicit
hypothesis: for a bilinear operator `B` *independent of the index* and any two families
`u, v : ℕ → 𝓧 → ℂ`,

`‖ (B(u k, v k))_k ‖_{L^q(𝓧; V²)} ≤ ⟨log K⟩²  sup_{ε, ε'} ‖ B(∑_k ε_k (u(k+1) - u k),
∑_k ε'_k (v(k+1) - v k)) ‖_{L^q(𝓧)}`,

the supremum running over `ε_k, ε'_k ∈ ℂ` with `‖ε_k‖ ≤ 1`, `‖ε'_k‖ ≤ 1`.  (The paper states the
loss as `⟨log K⟩^{max(2,2/q)}`; we record the case of interest `q ≥ 2`, where it is
`⟨log K⟩²`, and pad the logarithm so that the bound is valid for `K = 0, 1` as well.) -/
def RademacherMenshovBilinear (B : (𝓧 → ℂ) → (𝓧 → ℂ) → (𝓧 → ℂ)) (μ : Measure 𝓧)
    (q : ℝ≥0∞) : Prop :=
  ∀ (K : ℕ) (u v : ℕ → 𝓧 → ℂ),
    eLpNorm (fun x => PointwiseErgodicTheorems.variationalNorm 2 (fun k => B (u (k + 1)) (v (k + 1)) x))
        q μ
      ≤ ((Nat.log 2 K + 2 : ℕ) : ℝ≥0∞) ^ (2 : ℕ) *
        ⨆ (s : {ε : ℕ → ℂ // ∀ k, ‖ε k‖ ≤ 1} × {ε' : ℕ → ℂ // ∀ k, ‖ε' k‖ ≤ 1}),
          eLpNorm (fun x => B (fun y => ∑ k ∈ Finset.range K, s.1.1 k * (u (k + 1) y - u k y))
              (fun y => ∑ k ∈ Finset.range K, s.2.1 k * (v (k + 1) y - v k y)) x) q μ

/-- **Linearity of the multiplier family in its symbol.**  A `ℂ`-linear multiplier family
`T : (ℝ → ℂ) → (𝓧 → ℂ) → (𝓧 → ℂ)` (additive and homogeneous in the symbol) satisfies
`T (∑_k c_k • ξ_k) F = ∑_k c_k • T (ξ_k) F`. -/
theorem Tm_finset_sum_smul (Tm : (ℝ → ℂ) → (𝓧 → ℂ) → (𝓧 → ℂ))
    (hTm_add : ∀ (φ ψ : ℝ → ℂ) (F : 𝓧 → ℂ), Tm (φ + ψ) F = Tm φ F + Tm ψ F)
    (hTm_smul : ∀ (c : ℂ) (φ : ℝ → ℂ) (F : 𝓧 → ℂ), Tm (fun ξ => c * φ ξ) F = c • Tm φ F)
    {ι : Type*} (s : Finset ι) (c : ι → ℂ) (ξ : ι → ℝ → ℂ) (F : 𝓧 → ℂ) :
    Tm (∑ k ∈ s, fun ξ' => c k * ξ k ξ') F = ∑ k ∈ s, c k • Tm (ξ k) F := by
  classical
  induction s using Finset.induction with
  | empty =>
      simp only [Finset.sum_empty]
      have h : Tm 0 F = Tm 0 F + Tm 0 F := by simpa using hTm_add 0 0 F
      have h' : Tm 0 F + Tm 0 F = Tm 0 F + 0 := by rw [add_zero]; exact h.symm
      exact add_left_cancel h'
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, hTm_add, hTm_smul, ih]

/-- **The Section 8 reduction.**  Let `B` be a bilinear operator and `T` a `ℂ`-linear family of
Fourier multipliers, both independent of the scale.  If the single-scale expression
`B(T_{φ_*} F, T_{ψ_*} G)` is uniformly bounded for all randomised cut-offs
`φ_* = ∑_k ε_k • (φ_{k+1} - φ_k)`, `ψ_* = ∑_k ε'_k • (ψ_{k+1} - ψ_k)` with `‖ε_k‖, ‖ε'_k‖ ≤ 1`,
then the `V²`-variational norm of the model tuple `(B(T_{φ_{k+1}} F, T_{ψ_{k+1}} G))_k` is
bounded by `⟨log K⟩² · C`.  This is exactly the reduction performed in Section 8 of
Krause--Mirek--Tao between Corollary `rm-bil` and the small-scale model estimate
`(other-small-2)`: the point is that the randomised combination of the model tuple
`∑_k ε_k (T_{φ_{k+1}} F - T_{φ_k} F)` collapses, by linearity of `T` in its symbol, to the single
multiplier `T_{∑_k ε_k • (φ_{k+1} - φ_k)} F` — so that a uniform single-scale bound for
randomised cut-offs controls the whole small-scale tuple. -/
theorem smallScale_variational_le {μ : Measure 𝓧} {q : ℝ≥0∞}
    {B : (𝓧 → ℂ) → (𝓧 → ℂ) → (𝓧 → ℂ)} (hRM : RademacherMenshovBilinear B μ q)
    (Tm : (ℝ → ℂ) → (𝓧 → ℂ) → (𝓧 → ℂ))
    (hTm_add : ∀ (φ ψ : ℝ → ℂ) (F : 𝓧 → ℂ), Tm (φ + ψ) F = Tm φ F + Tm ψ F)
    (hTm_smul : ∀ (c : ℂ) (φ : ℝ → ℂ) (F : 𝓧 → ℂ), Tm (fun ξ => c * φ ξ) F = c • Tm φ F)
    {K : ℕ} {F G : 𝓧 → ℂ} {φ ψ : ℕ → ℝ → ℂ} {C : ℝ≥0∞}
    (hSS : ∀ s : {ε : ℕ → ℂ // ∀ k, ‖ε k‖ ≤ 1} × {ε' : ℕ → ℂ // ∀ k, ‖ε' k‖ ≤ 1},
      eLpNorm (fun x => B (Tm (∑ k ∈ Finset.range K, fun ξ => s.1.1 k * (φ (k + 1) ξ - φ k ξ)) F)
          (Tm (∑ k ∈ Finset.range K, fun ξ => s.2.1 k * (ψ (k + 1) ξ - ψ k ξ)) G) x) q μ ≤ C) :
    eLpNorm (fun x => PointwiseErgodicTheorems.variationalNorm 2
        (fun k => B (Tm (φ (k + 1)) F) (Tm (ψ (k + 1)) G) x)) q μ
      ≤ ((Nat.log 2 K + 2 : ℕ) : ℝ≥0∞) ^ (2 : ℕ) * C := by
  classical
  have hsub : ∀ (χ χ' : ℝ → ℂ) (F : 𝓧 → ℂ),
      Tm (fun ξ => χ ξ - χ' ξ) F = Tm χ F - Tm χ' F := by
    intro χ χ' F
    have h := hTm_add (fun ξ => χ ξ - χ' ξ) χ' F
    have hχ : (fun ξ => χ ξ - χ' ξ) + χ' = χ := by
      funext ξ
      exact sub_add_cancel _ _
    rw [hχ] at h
    exact (sub_eq_iff_eq_add.mpr h).symm
  have hcomb : ∀ (c : ℕ → ℂ) (χ : ℕ → ℝ → ℂ) (F : 𝓧 → ℂ),
      (fun y => ∑ k ∈ Finset.range K, c k * (Tm (χ (k + 1)) F y - Tm (χ k) F y))
        = Tm (∑ k ∈ Finset.range K, fun ξ => c k * (χ (k + 1) ξ - χ k ξ)) F := by
    intro c χ F
    rw [Tm_finset_sum_smul Tm hTm_add hTm_smul (Finset.range K) c
      (fun k => fun ξ => χ (k + 1) ξ - χ k ξ) F]
    funext y
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [hsub (χ (k + 1)) (χ k) F]
    simp only [Pi.sub_apply]
  have hlog : (0 : ℝ≥0∞) ≤ ((Nat.log 2 K + 2 : ℕ) : ℝ≥0∞) ^ (2 : ℕ) := bot_le
  have hRM' := hRM K (fun k => Tm (φ k) F) (fun k => Tm (ψ k) G)
  refine hRM'.trans (mul_le_mul_of_nonneg_left (iSup_le fun s => ?_) hlog)
  rw [hcomb (fun k => s.1.1 k) φ F, hcomb (fun k => s.2.1 k) ψ G]
  exact hSS s


/-- **`V^r ≤ V²` for `r ≥ 2`.**  On the counting-measure (un-normalised `ℓ^r`) convention of the
paper's variational seminorm, the second term of the variational norm is *antitone* in the
exponent: `varPart r a ≤ varPart 2 a` whenever `r ≥ 2`.  This is the elementary
`ℓ^r`-monotonicity `WithLp_toLp_norm_mono`, lifted through the supremum defining `varPart`, and
it is what passes a `V²`-bound (as produced by Corollary `rm-bil`) to the exponents `r > 2` used
in the paper. -/
theorem varPart_mono_of_two_le {r : ℝ≥0} (hr : (2 : ℝ≥0) ≤ r) (a : ℕ → ℂ) :
    Submission.PointwiseErgodicTheorems.varPart r a ≤ Submission.PointwiseErgodicTheorems.varPart 2 a := by
  refine iSup_le fun J => iSup_le fun N => iSup_le fun hN => ?_
  refine le_trans ?_ (le_iSup_of_le J (le_iSup_of_le N (le_iSup_of_le hN le_rfl)))
  exact ENNReal.ofReal_le_ofReal (WithLp_toLp_norm_mono (r := r) hr _)

/-- **`V^r ≤ V²` for `r ≥ 2`**, in the form of the paper's variational norm
`variationalNorm r a = sup_n ‖a n‖ + V^r(a)`. -/
theorem variationalNorm_mono_of_two_le {r : ℝ≥0} (hr : (2 : ℝ≥0) ≤ r) (a : ℕ → ℂ) :
    PointwiseErgodicTheorems.variationalNorm r a
      ≤ PointwiseErgodicTheorems.variationalNorm 2 a := by
  rw [Submission.PointwiseErgodicTheorems.variationalNorm_eq_add,
    Submission.PointwiseErgodicTheorems.variationalNorm_eq_add]
  exact add_le_add le_rfl (varPart_mono_of_two_le hr a)

end

end Work.Analysis.Paraproduct
