/-
# The `r`-seminorm bound for the CKMRV contour transform on the cusp tiles `±1 + E`

CKMRV (Cohn--Kumar--Miller--Radchenko--Viazovska, Ann. of Math. 196 (2022)) prove, in §5.2, the
moderate growth of the `r`-seminorms of `F₂ = kernelTransform K` near *each* of the four cusps
`-1, 0, 1, ∞` of the fundamental domain `𝒟` of `Γ(2)`.  The cusp `∞` tile is the funnel
`𝓕 = {τ ∈ 𝒟 : 2 ≤ Im τ}`, the cusp `0` tile is `E = S(𝓕)` (`Work.Asymptotics.KEpsilon`), and
the cusps `±1` tiles are the translates `±1 + E`.

This file states the bound on the tiles `±1 + E`:

  `∀ k l, ∃ C N ≥ 0, ∀ w ∈ E, ∀ r : |r|^k ‖∂_r^l (fun s => kernelTransform K (±1 + w) s) r‖
      ≤ C (scale w)^N`,

which is the input consumed by `Work.Asymptotics.funnel_seminorm_slashed` (the cusp-`±1` cases of
the slashed funnel bound).  The two ingredients of its proof are available in the repository:

* the exact pole structure at the translate pole `z = τ ∓ 1`: `Work.Asymptotics.
  Kfun_principal_part_z_lip` gives, for `τ` near `n + i s₀` (`n = ±1`),
  `‖K(τ,z)(z - (τ - n)) - n/(2π)‖ ≤ C‖z - (τ - n)‖` (`Res_{z=τ∓1}K(τ,z∓1) = ∓1/(2π)`,
  Theorem 4.9(3)); the remaining *signed* integral is the model (Plemelj) integral
  `∫_0^∞ e^{-a t}/(t - t₀) dt`, whose uniform bound is `Work.Asymptotics.model_integral_inv_bound`
  (this is where the logarithmic divergence of the *norm* integral is cancelled);
* the divisor `Δ(z)(j τ - j z)` at a cusp-`±1` point `τ = ±1 + w` equals the divisor at the
  cusp-`0` point `w` (`Δ`, `j` are `T`-invariant, `Work.Asymptotics.growthPrefactor_vadd_one`
  below), so all the divisor lower bounds of the cusp-`0` tile apply verbatim.
-/
/-
## How to prove `cuspTile_seminorm` (route found, not yet formalised)

The cusp-`±1` tiles are *not* accessible from the funnel bound by a change of variables: the
transform `σ ↦ kernelTransform K σ r` is not modular.  They are, however, accessible from the
funnel bound together with the compact bound, through the two *homogeneous* functional equations
satisfied by `K` (both proved in `Work.Residues.ResidueTheoremK`):

* `Kfun_T2 :  (T-I)²K = 0`, i.e. `K(τ+2,z) - 2K(τ+1,z) + K(τ,z) = 0`;
* `Kfun_slash_S_T2 :  S(T-I)²K = 0`, i.e. `(K|^τS)(τ+2) - 2(K|^τS)(τ+1) + (K|^τS)(τ) = 0`.

Both identities integrate in `z` against `e^{-πr²t}` (the integrands are pointwise equal), so the
transform `G(σ,r) = kernelTransform K σ r` and its `S`-slash satisfy the same second-difference
relations *wherever the three integrals converge*; together with the monotonicity of convergence
in `|r|` (`integrableOn_kaxis_exp_mono_abs`, so the convergence set is a threshold in `|r|`) and
the fact that the naive Bochner integral is `0` off that set, this transfers to the `r`-seminorms.

The geometry then closes the argument for a funnel point `τ ∈ 𝓕` with `Re τ > 0`:

* `(S(T-I)²K)` evaluated at `σ := S·τ` relates `(G|^τS)(σ) = j(S,σ)^{-d/2} G(τ,·)`
  (the *funnel* value, known), `(G|^τS)(σ+2)` at the point `-1/(σ+2) = -τ/(2τ-1)`, and the
  middle value `(G|^τS)(σ+1)` at `-1/(σ+1) = τ/(1-τ) = -1 + 1/(1-τ)`, which is exactly the
  cusp-`(-1)` tile point `-1 + w` with `w = 1/(1-τ) = S·(τ-1) ∈ E` (because `τ - 1 ∈ 𝓕`).
  The two "ends" of the ladder are known: the funnel one by `kernelTransform_seminorm_funnel`
  and the one at `-τ/(2τ-1)`, which lies in the *other* cusp-`0` tile `S T⁻¹𝓕` and is covered by
  the compact bound (that tile is `E` on `Im ≥ 2` and a compact subset of `ℍ` below it).
  Hence the middle value — the cusp-`(-1)` tile bound — follows.

* `(T-I)²K` at `w ∈ E` then gives the cusp-`1` tile value from the cusp-`(-1)` one and the
  (known) value at `w`: `G(w+1) = 2G(w) - G(w-1)`.

So `cuspTile_seminorm` follows from the funnel bound, the compact bound
(`Work.Asymptotics.KhatFunnel.kernelTransform_seminorm_on_compact_clean`) and the two
second-difference relations above, with the threshold/junk bookkeeping of
`Work.Asymptotics.kernelTransform_seminorm_of_layer`.

## Status of the ladder route (corrected)

Pieces 1--3 below are proved: the two second-difference relations `(T-I)²K = 0` and
`S(T-I)²K = 0` hold for the naive contour transform wherever the three integrals converge, and
the divisor of a cusp-`±1` point `n + w` equals that of the cusp-`0` point `w` (so all the
cusp-`0` divisor estimates apply to the cusp-`±1` tiles), together with the scale comparison
`scale (n + w) ≤ 3 scale w` and the far-field bound `norm_Kaxis_cuspTile_le`.

**Correction to the route sketched above.**  The ladder relation at `σ = S·τ` does *not* by
itself close the argument: its two ends are `G(τ)` (funnel, known) and `G(-τ/(2τ-1))`, and the
second point lies **outside** the closure `𝒟̄` of the fundamental domain (for `τ = 10i` it is
`≈ -0.5 + 0.025i`, inside the excluded disc `|z + 1/2| < 1/2`), because `-τ/(2τ-1) = γ'·τ` with
γ' = [[-1,0],[2,-1]] ∈ Γ(2).  So the compact bound does not apply there, and the transform is not
Γ(2)-invariant, so this end is *not* a known quantity.  The remaining content of
`cuspTile_seminorm` is therefore genuinely the paper's cusp-`±1` analysis: the pole
decomposition `K(σ,z) = (±1/2π)/(z - (σ ∓ 1)) + (bounded remainder)` of
`Work.Asymptotics.Kfun_principal_part_z_lip`, the signed (Plemelj) model integral
`Work.Asymptotics.model_integral_inv_bound` cancelling the logarithmic divergence of the norm
integral, and the far-field bound `norm_Kaxis_cuspTile_le` above.
-/

import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Residues.ResidueTheoremK
import Submission.Work.Asymptotics.Instances
import Submission.Work.Rigidity.Diff
import Submission.Work.Asymptotics.PropagateDefs

noncomputable section

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle Topology

namespace Work.Asymptotics

open Work.Kernels


/-! ## Piece 1: the second-difference relation `(T-I)²K = 0` at the level of the transform

`Work.Residues.Kfun_T2` says that the kernel is annihilated by `(T-I)²` in the `τ`-variable,
pointwise in the second variable.  Integrating that identity against `e^{-πr²t}` gives the same
second-difference relation for the naive contour transform `r ↦ kernelTransform K τ r`, wherever
the three integrals converge.  This is the first ingredient of the ladder route to the cusp-`±1`
tiles (see the roadmap at the top of this file).
-/

/-- **(T-I)²K = 0 on the contour**: `K(τ+2,it) - 2K(τ+1,it) + K(τ,it) = 0`. -/
lemma Kaxis_T2_Kfun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ) (t : ℝ) :
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((2 : ℝ) +ᵥ τ) t
      - 2 * Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ τ) t
      + Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t = 0 := by
  by_cases ht : 0 < t
  · have h := congr_fun (Work.Residues.Kfun_T2 ℓ d hd (Work.Kernels.imagAxis t ht)) τ
    simp only [Work.Kernels.T2op, Pi.zero_apply] at h
    simpa only [Work.Kernels.Kaxis, dif_pos ht] using h
  · simp only [Work.Kernels.Kaxis, dif_neg ht]
    ring

/-- **The second-difference relation for the naive contour transform.**  If the three contour
integrands are integrable at `r`, then

  `kernelTransform K (τ+2) r - 2 · kernelTransform K (τ+1) r + kernelTransform K τ r = 0`.

(Off the convergence set the Bochner integral is `0`, so the relation holds trivially there; the
hypotheses spell out the convergence range explicitly.) -/
lemma kernelTransform_T2_of_integrable (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : ℍ) (r : ℝ)
    (h1 : MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((2 : ℝ) +ᵥ τ) t *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0))
    (h2 : MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ τ) t *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0))
    (h3 : MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0)) :
    Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((2 : ℝ) +ᵥ τ) r
      - 2 * Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ τ) r
      + Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r = 0 := by
  set f : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((2 : ℝ) +ᵥ τ) t *
      Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hf
  set g : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ τ) t *
      Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hg
  set h : ℝ → ℂ := fun t => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t *
      Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hh
  have hzero : (fun t : ℝ => f t - 2 * g t + h t) = fun _ : ℝ => (0 : ℂ) := by
    funext t
    have hK := Kaxis_T2_Kfun ℓ d hd τ t
    simp only [hf, hg, hh]
    linear_combination Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) * hK
  have h2i : MeasureTheory.IntegrableOn (fun t : ℝ => 2 * g t) (Set.Ioi 0) := h2.const_mul 2
  have hsplit : (∫ t in Set.Ioi 0, f t - 2 * g t + h t)
      = (∫ t in Set.Ioi 0, f t) - 2 * (∫ t in Set.Ioi 0, g t)
        + (∫ t in Set.Ioi 0, h t) := by
    have hA : (∫ t in Set.Ioi 0, (f t - 2 * g t : ℂ))
        = (∫ t in Set.Ioi 0, f t) - (∫ t in Set.Ioi 0, 2 * g t) :=
      MeasureTheory.integral_sub h1 h2i
    have hB : (∫ t in Set.Ioi 0, (2 * g t : ℂ)) = 2 * (∫ t in Set.Ioi 0, g t) := by
      simpa using MeasureTheory.integral_const_mul
        (μ := MeasureTheory.volume.restrict (Set.Ioi 0)) (2 : ℂ) g
    have hC : (∫ t in Set.Ioi 0, ((f t - 2 * g t) + h t : ℂ))
        = (∫ t in Set.Ioi 0, (f t - 2 * g t : ℂ)) + (∫ t in Set.Ioi 0, h t) :=
      MeasureTheory.integral_add (h1.sub h2i) h3
    rw [hC, hA, hB]
  have hInt : (∫ t in Set.Ioi 0, f t - 2 * g t + h t) = 0 := by
    rw [hzero]
    simp
  have hfactor : Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((2 : ℝ) +ᵥ τ) r
      - 2 * Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) ((1 : ℝ) +ᵥ τ) r
      + Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r
      = 4 * Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2 *
        ((∫ t in Set.Ioi 0, f t) - 2 * (∫ t in Set.Ioi 0, g t)
          + (∫ t in Set.Ioi 0, h t)) := by
    simp only [Work.Kernels.kernelTransform, hf, hg, hh]
    ring
  rw [hfactor, ← hsplit, hInt, mul_zero]



/-! ## Piece 2: the same relation for `S(T-I)²K = 0`

`Work.Residues.Kaxis_Kfun_slash_S_T2` is the pointwise annihilation of the kernel on the contour by
the second generator `S(T-I)²` of `𝓘`.  Unpacking it with `S2op_apply_eq` gives the pointwise
second-difference relation for the `S`-slash of the contour kernel, which is the second ingredient
of the ladder route (it is the relation used at `σ = S·τ`, whose two "ends" are known).
-/

/-- **`S(T-I)²K = 0` on the contour, pointwise:**
`X(τ+2) - 2X(τ+1) + X(τ) = 0` for `X(σ) = j(S,σ)^{-d/2} K(S·σ, it)`. -/
lemma Kaxis_slash_S_T2_Kfun (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : ℍ) (t : ℝ) :
    ((fun σ : ℍ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t) ∣[((d : ℤ) / 2)] ModularGroup.S) ((2 : ℝ) +ᵥ τ)
      - 2 * (((fun σ : ℍ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t) ∣[((d : ℤ) / 2)] ModularGroup.S) ((1 : ℝ) +ᵥ τ))
      + ((fun σ : ℍ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t) ∣[((d : ℤ) / 2)] ModularGroup.S) τ = 0 := by
  have h := congr_fun (Work.Residues.Kaxis_Kfun_slash_S_T2 ℓ d hd t) τ
  rw [show Work.Kernels.slash ((d : ℤ) / 2) (Work.Kernels.R_S * (Work.Kernels.R_T - 1) ^ 2)
        (fun σ : ℍ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t)
      = S2op ((d : ℤ) / 2) (fun σ : ℍ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t)
      from rfl] at h
  rw [S2op_apply_eq] at h
  exact h

/-- The `S`-slash of the contour kernel, written out with the factor of automorphy. -/
lemma slash_S_Kaxis_apply (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (σ : ℍ) (t : ℝ) :
    ((fun σ : ℍ => Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) σ t) ∣[((d : ℤ) / 2)] ModularGroup.S) σ
      = Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (ModularGroup.S • σ) t
        * (Work.Kernels.jFun ModularGroup.S (σ : ℂ)) ^ (-((d : ℤ) / 2)) :=
  Work.Kernels.slash_apply' _ _ _ σ

/-- **The second-difference relation for the `S`-slash of the naive contour transform.**
Where the three integrals converge,

  `j(S,τ+2)^{-d/2} G(S·(τ+2)) - 2 j(S,τ+1)^{-d/2} G(S·(τ+1)) + j(S,τ)^{-d/2} G(S·τ) = 0`,

with `G(σ) = kernelTransform K σ r`.  This is the ladder relation used at the cusp-`(-1)` tile. -/
lemma kernelTransform_slash_S_T2_of_integrable (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) (τ : ℍ) (r : ℝ)
    (h0 : MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (ModularGroup.S • τ) t *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0))
    (h1 : MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) t *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0))
    (h2 : MeasureTheory.IntegrableOn (fun t : ℝ =>
      Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (ModularGroup.S • ((2 : ℝ) +ᵥ τ)) t *
        Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0)) :
    (Work.Kernels.jFun ModularGroup.S (((2 : ℝ) +ᵥ τ : ℍ) : ℂ)) ^ (-((d : ℤ) / 2)) *
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) (ModularGroup.S • ((2 : ℝ) +ᵥ τ)) r
      - 2 * ((Work.Kernels.jFun ModularGroup.S (((1 : ℝ) +ᵥ τ : ℍ) : ℂ)) ^ (-((d : ℤ) / 2)) *
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) r)
      + (Work.Kernels.jFun ModularGroup.S (τ : ℂ)) ^ (-((d : ℤ) / 2)) *
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) (ModularGroup.S • τ) r = 0 := by
  set c : ℍ → ℂ := fun σ => (Work.Kernels.jFun ModularGroup.S (σ : ℂ)) ^ (-((d : ℤ) / 2)) with hc
  set f : ℍ → ℝ → ℂ := fun σ t =>
    Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) (ModularGroup.S • σ) t *
      Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) with hf
  have hzero : (fun t : ℝ => c ((2 : ℝ) +ᵥ τ) * f ((2 : ℝ) +ᵥ τ) t
      - 2 * (c ((1 : ℝ) +ᵥ τ) * f ((1 : ℝ) +ᵥ τ) t) + c τ * f τ t) = fun _ : ℝ => (0 : ℂ) := by
    funext t
    have hK := Kaxis_slash_S_T2_Kfun ℓ d hd τ t
    rw [slash_S_Kaxis_apply, slash_S_Kaxis_apply, slash_S_Kaxis_apply] at hK
    simp only [hc, hf]
    linear_combination Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ))) * hK
  -- the integral of the pointwise relation
  have hInt : (∫ t in Set.Ioi 0, c ((2 : ℝ) +ᵥ τ) * f ((2 : ℝ) +ᵥ τ) t
      - 2 * (c ((1 : ℝ) +ᵥ τ) * f ((1 : ℝ) +ᵥ τ) t) + c τ * f τ t) = 0 := by
    rw [hzero]; simp
  -- pull the three constants out of the integrals
  have hsplit : (∫ t in Set.Ioi 0, c ((2 : ℝ) +ᵥ τ) * f ((2 : ℝ) +ᵥ τ) t
      - 2 * (c ((1 : ℝ) +ᵥ τ) * f ((1 : ℝ) +ᵥ τ) t) + c τ * f τ t)
      = c ((2 : ℝ) +ᵥ τ) * (∫ t in Set.Ioi 0, f ((2 : ℝ) +ᵥ τ) t)
        - 2 * (c ((1 : ℝ) +ᵥ τ) * (∫ t in Set.Ioi 0, f ((1 : ℝ) +ᵥ τ) t))
        + c τ * (∫ t in Set.Ioi 0, f τ t) := by
    have hi0 : MeasureTheory.Integrable
        (fun t : ℝ => c ((2 : ℝ) +ᵥ τ) * f ((2 : ℝ) +ᵥ τ) t)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
      simpa only [hf] using h2.const_mul (c ((2 : ℝ) +ᵥ τ))
    have hi1 : MeasureTheory.Integrable
        (fun t : ℝ => c ((1 : ℝ) +ᵥ τ) * f ((1 : ℝ) +ᵥ τ) t)
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
      simpa only [hf] using h1.const_mul (c ((1 : ℝ) +ᵥ τ))
    have hi2 : MeasureTheory.Integrable
        (fun t : ℝ => c τ * f τ t) (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
      simpa only [hf] using h0.const_mul (c τ)
    have h2i : MeasureTheory.Integrable
        (fun t : ℝ => 2 * (c ((1 : ℝ) +ᵥ τ) * f ((1 : ℝ) +ᵥ τ) t))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
      simpa only [mul_assoc] using hi1.const_mul 2
    have hA : (∫ t in Set.Ioi 0, (c ((2 : ℝ) +ᵥ τ) * f ((2 : ℝ) +ᵥ τ) t
          - 2 * (c ((1 : ℝ) +ᵥ τ) * f ((1 : ℝ) +ᵥ τ) t) : ℂ))
        = (∫ t in Set.Ioi 0, c ((2 : ℝ) +ᵥ τ) * f ((2 : ℝ) +ᵥ τ) t)
          - (∫ t in Set.Ioi 0, 2 * (c ((1 : ℝ) +ᵥ τ) * f ((1 : ℝ) +ᵥ τ) t)) :=
      MeasureTheory.integral_sub hi0 h2i
    have hB : (∫ t in Set.Ioi 0, (2 * (c ((1 : ℝ) +ᵥ τ) * f ((1 : ℝ) +ᵥ τ) t) : ℂ))
        = 2 * (∫ t in Set.Ioi 0, c ((1 : ℝ) +ᵥ τ) * f ((1 : ℝ) +ᵥ τ) t) := by
      simpa only [mul_assoc] using MeasureTheory.integral_const_mul
        (μ := MeasureTheory.volume.restrict (Set.Ioi 0)) (2 : ℂ)
        (fun t : ℝ => c ((1 : ℝ) +ᵥ τ) * f ((1 : ℝ) +ᵥ τ) t)
    have hC : (∫ t in Set.Ioi 0, ((c ((2 : ℝ) +ᵥ τ) * f ((2 : ℝ) +ᵥ τ) t
          - 2 * (c ((1 : ℝ) +ᵥ τ) * f ((1 : ℝ) +ᵥ τ) t)) + c τ * f τ t : ℂ))
        = (∫ t in Set.Ioi 0, (c ((2 : ℝ) +ᵥ τ) * f ((2 : ℝ) +ᵥ τ) t
            - 2 * (c ((1 : ℝ) +ᵥ τ) * f ((1 : ℝ) +ᵥ τ) t) : ℂ))
          + (∫ t in Set.Ioi 0, c τ * f τ t) :=
      MeasureTheory.integral_add (hi0.sub h2i) hi2
    have hD : (∫ t in Set.Ioi 0, (c ((2 : ℝ) +ᵥ τ) * f ((2 : ℝ) +ᵥ τ) t : ℂ))
        = c ((2 : ℝ) +ᵥ τ) * (∫ t in Set.Ioi 0, f ((2 : ℝ) +ᵥ τ) t) := by
      simpa using MeasureTheory.integral_const_mul
        (μ := MeasureTheory.volume.restrict (Set.Ioi 0)) (c ((2 : ℝ) +ᵥ τ)) (f ((2 : ℝ) +ᵥ τ))
    have hF : (∫ t in Set.Ioi 0, (c ((1 : ℝ) +ᵥ τ) * f ((1 : ℝ) +ᵥ τ) t : ℂ))
        = c ((1 : ℝ) +ᵥ τ) * (∫ t in Set.Ioi 0, f ((1 : ℝ) +ᵥ τ) t) := by
      simpa using MeasureTheory.integral_const_mul
        (μ := MeasureTheory.volume.restrict (Set.Ioi 0)) (c ((1 : ℝ) +ᵥ τ)) (f ((1 : ℝ) +ᵥ τ))
    have hE : (∫ t in Set.Ioi 0, (c τ * f τ t : ℂ))
        = c τ * (∫ t in Set.Ioi 0, f τ t) := by
      simpa using MeasureTheory.integral_const_mul
        (μ := MeasureTheory.volume.restrict (Set.Ioi 0)) (c τ) (f τ)
    rw [hC, hA, hB, hD, hF, hE]
  have hfactor : (Work.Kernels.jFun ModularGroup.S (((2 : ℝ) +ᵥ τ : ℍ) : ℂ)) ^ (-((d : ℤ) / 2)) *
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) (ModularGroup.S • ((2 : ℝ) +ᵥ τ)) r
      - 2 * ((Work.Kernels.jFun ModularGroup.S (((1 : ℝ) +ᵥ τ : ℍ) : ℂ)) ^ (-((d : ℤ) / 2)) *
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) (ModularGroup.S • ((1 : ℝ) +ᵥ τ)) r)
      + (Work.Kernels.jFun ModularGroup.S (τ : ℂ)) ^ (-((d : ℤ) / 2)) *
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) (ModularGroup.S • τ) r
      = 4 * Complex.sin (Real.pi * (r : ℂ) ^ 2 / 2) ^ 2 *
        (c ((2 : ℝ) +ᵥ τ) * (∫ t in Set.Ioi 0, f ((2 : ℝ) +ᵥ τ) t)
          - 2 * (c ((1 : ℝ) +ᵥ τ) * (∫ t in Set.Ioi 0, f ((1 : ℝ) +ᵥ τ) t))
          + c τ * (∫ t in Set.Ioi 0, f τ t)) := by
    simp only [Work.Kernels.kernelTransform, hc, hf]
    ring
  rw [hfactor, ← hsplit, hInt, mul_zero]

/-! ## `T`-invariance of the divisor and of the kernel's `τ`-atoms -/

/-- `Δ` is invariant under `τ ↦ τ + 1`. -/
lemma DeltaFun_vadd_one' (τ : ℍ) : DeltaFun ((1 : ℝ) +ᵥ τ) = DeltaFun τ :=
  KernelFacts.DeltaFun_vadd_one τ

/-- `j` is invariant under `τ ↦ τ + 1`. -/
lemma jInvariantFun_vadd_one' (τ : ℍ) : jInvariantFun ((1 : ℝ) +ᵥ τ) = jInvariantFun τ :=
  KernelFacts.jInvariantFun_vadd_one τ

/-- **The divisor at the cusp-`±1` tiles is the divisor at the cusp-`0` tile.**  For `n = ±1`,
`Δ(z)(j(n + w) - j z) = Δ(z)(j w - j z)`: the translate `w ↦ n + w` changes neither `Δ` nor
`j`.  Consequently every lower bound for the cusp-`0` divisor applies to the tiles `±1 + E`,
which is what makes the far-from-the-pole estimates of the tiles `±1 + E` reduce to those of
`E`. -/
lemma growthPrefactor_vadd_one (d : ℕ) (w z : ℍ) :
    growthPrefactor d ((1 : ℝ) +ᵥ w) z = growthPrefactor d w z := by
  simp only [growthPrefactor, DeltaFun_vadd_one' w, jInvariantFun_vadd_one' w]

lemma growthPrefactor_vadd_neg_one (d : ℕ) (w z : ℍ) :
    growthPrefactor d ((-1 : ℝ) +ᵥ w) z = growthPrefactor d w z := by
  have h1 := growthPrefactor_vadd_one d ((-1 : ℝ) +ᵥ w) z
  rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ w) = w from by
    rw [vadd_vadd, add_neg_cancel, zero_vadd]] at h1
  exact h1.symm

lemma growthPrefactor_vadd_of (d : ℕ) (w z : ℍ) {n : ℤ} (hn : n = 1 ∨ n = -1) :
    growthPrefactor d ((n : ℝ) +ᵥ w) z = growthPrefactor d w z := by
  rcases hn with h | h
  · subst h; simpa using growthPrefactor_vadd_one d w z
  · subst h; simpa using growthPrefactor_vadd_neg_one d w z

/-! ## Piece 4: the divisor transfer and the far field of the cusp-`±1` tiles -/

/-- `j` is unchanged by an integer translate. -/
lemma jInvariantFun_vadd_neg_one' (τ : ℍ) :
    jInvariantFun ((-1 : ℝ) +ᵥ τ) = jInvariantFun τ := by
  have h1 := jInvariantFun_vadd_one' ((-1 : ℝ) +ᵥ τ)
  rw [show (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ from by
    rw [vadd_vadd, add_neg_cancel, zero_vadd]] at h1
  exact h1.symm

lemma jInvariantFun_vadd_of (w : ℍ) {n : ℤ} (hn : n = 1 ∨ n = -1) :
    jInvariantFun ((n : ℝ) +ᵥ w) = jInvariantFun w := by
  rcases hn with h | h
  · subst h; simpa using jInvariantFun_vadd_one' w
  · subst h; simpa using jInvariantFun_vadd_neg_one' w

/-- The `scale` of an integer translate is comparable to the `scale` of the point. -/
lemma scale_vadd_int_le (w : ℍ) {n : ℤ} (hn : n = 1 ∨ n = -1) :
    Work.Kernels.scale ((n : ℝ) +ᵥ w) ≤ 3 * Work.Kernels.scale w := by
  have him : ((n : ℝ) +ᵥ w : ℍ).im = w.im := Work.Rigidity.im_vadd (n : ℝ) w
  have hnorm : ‖(((n : ℝ) +ᵥ w : ℍ) : ℂ)‖ ≤ ‖(w : ℂ)‖ + 1 := by
    rw [UpperHalfPlane.coe_vadd]
    calc ‖(n : ℂ) + (w : ℂ)‖ ≤ ‖(n : ℂ)‖ + ‖(w : ℂ)‖ := norm_add_le _ _
      _ = ‖(w : ℂ)‖ + 1 := by
          rw [show ‖(n : ℂ)‖ = 1 from by rcases hn with h | h <;> (subst h; norm_num)]
          ring
  have hx : 0 ≤ (w.im)⁻¹ := inv_nonneg.mpr w.im_pos.le
  have hwn : 0 ≤ ‖(w : ℂ)‖ := norm_nonneg _
  rw [Work.Kernels.scale, Work.Kernels.scale, him]
  linarith

/-- **The far-field bound at the cusp-`±1` tiles.**  The divisor of a cusp-`±1` point `n + w`
(`n = ±1`, `w ∈ E`) is the divisor of `w` (`growthPrefactor_vadd_of`), so the divisor form of the
concrete contour bound (`Work.Asymptotics.norm_Kaxis_Kfun_le`) transfers verbatim to the cusp-`±1`
tiles: away from the coincidence `j w = j(it)` the kernel is bounded by a polynomial divided by
the cusp-`0` divisor. -/
lemma norm_Kaxis_cuspTile_le (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {w : ℍ} {n : ℤ} (hn : n = 1 ∨ n = -1) {t : ℝ} (ht : 0 < t)
    (hJ : Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht)) :
    ∃ α N M : ℝ, 0 ≤ α ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t‖
        ≤ α * (Work.Kernels.scale w) ^ N
            * (Work.Kernels.scale (Work.Kernels.imagAxis t ht)) ^ M
          / ‖Work.Kernels.growthPrefactor d w (Work.Kernels.imagAxis t ht)‖ := by
  have hb : ∃ α N M : ℝ, 0 ≤ α ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) ((n : ℝ) +ᵥ w) t‖
        ≤ α * (Work.Kernels.scale ((n : ℝ) +ᵥ w)) ^ N
            * (Work.Kernels.scale (Work.Kernels.imagAxis t ht)) ^ M
          / ‖Work.Kernels.growthPrefactor d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)‖ :=
    Work.Asymptotics.norm_Kaxis_Kfun_le (ℓ := ℓ) (d := d) hd ht
      (by rw [jInvariantFun_vadd_of w hn]; exact hJ)
  obtain ⟨α, N, M, hα, hN, hM, hbd⟩ := hb
  have hg : Work.Kernels.growthPrefactor d ((n : ℝ) +ᵥ w) (Work.Kernels.imagAxis t ht)
      = Work.Kernels.growthPrefactor d w (Work.Kernels.imagAxis t ht) :=
    growthPrefactor_vadd_of d w _ hn
  rw [hg] at hbd
  refine ⟨α * 3 ^ N, N, M, mul_nonneg hα (Real.rpow_nonneg (by norm_num) N), hN, hM, ?_⟩
  refine le_trans hbd (div_le_div_of_nonneg_right ?_ (norm_nonneg _))
  have hs : Work.Kernels.scale ((n : ℝ) +ᵥ w) ^ N ≤ 3 ^ N * Work.Kernels.scale w ^ N := by
    have h := Real.rpow_le_rpow (le_trans (by norm_num) (Work.Kernels.one_le_scale _))
      (scale_vadd_int_le w hn) hN
    rwa [Real.mul_rpow (by norm_num) (le_trans (by norm_num) (Work.Kernels.one_le_scale w))] at h
  have hS : (0 : ℝ) ≤ Work.Kernels.scale (Work.Kernels.imagAxis t ht) ^ M :=
    Real.rpow_nonneg
      (le_trans (by norm_num) (Work.Kernels.one_le_scale (Work.Kernels.imagAxis t ht))) M
  calc α * Work.Kernels.scale ((n : ℝ) +ᵥ w) ^ N
        * Work.Kernels.scale (Work.Kernels.imagAxis t ht) ^ M
      ≤ α * (3 ^ N * Work.Kernels.scale w ^ N)
        * Work.Kernels.scale (Work.Kernels.imagAxis t ht) ^ M :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hα) hS
    _ = α * 3 ^ N * Work.Kernels.scale w ^ N
        * Work.Kernels.scale (Work.Kernels.imagAxis t ht) ^ M := by ring


end Work.Asymptotics
