import Mathlib
import Submission.Work.Diff.STE.FlatPDE
import Submission.Work.Diff.STE.flat.level_aux
import Submission.Work.Diff.STE.flat.nonlin_coeff_bound
import Submission.Work.Diff.STE.flat.seriesFunM_eq_sum
import Submission.Work.Diff.STE.pd_seriesFun

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `Work.Diff.STE.flat.nonlin_bound_short`

The uniform short-time `ℓ¹` bound for the Fourier coefficients of the nonlinearity
`x ↦ Φ (x, jet of seriesFunM (c t) at x)` along a Galerkin solution `c` of the flat DeTurck
system.

## What is proved here

`nonlin_bound_short` says: there are `Λ ≥ 0` and `τ > 0`, depending only on `n`, `Φ`, `k`, `lam`
and `E`, such that for *every* `Tc > 0`, every Galerkin order `N` and every coefficient family
`c : ℝ → (Fin n → ℤ) → MatC n` which

* is supported in the box `box n N` at every time,
* satisfies the Galerkin ODE `∂_t c (t, k') = fourierCoeff (Φ ∘ jet) k'` on `[0, Tc)`,
* has level-`j` coefficient energy `CSqM j (c t) ≤ E` for all `j ≤ k` and `t ∈ [0, Tc)`,
* has a positive definite metric matrix at time `0` with ellipticity constant `lam`,

one has, for every `t ∈ [0, min τ Tc)` and every entry `(i,j)`,

`Summable (fun m => ‖fourierCoeff (Φ ∘ jet) m‖)` and `∑' m, ‖…‖ ≤ Λ`,

i.e. the Fourier coefficients of the nonlinearity have a *uniform* `ℓ¹` bound on a short time
interval, independently of `N` and of the data.

## The proof

At a *single* time `t` the statement is the sibling lemma `nonlin_coeff_bound`
(`Submission/Work/Diff/STE/flat/nonlin_coeff_bound.lean`), which requires the elliptic constant
`lam / 2` (rather than `lam`) at that time, together with the energy bound and the box support.

The passage from "elliptic at time `0`" to "(lam/2)-elliptic on a short interval" is the
*self-consistent* (bootstrap) argument which is the mathematical content of this file:

* if the metric matrix is `(lam/2)`-elliptic on `[0, t]`, then by `nonlin_coeff_bound` the
  nonlinearity has `ℓ¹`-norm at most `Λ` on `[0, t]`; the Galerkin ODE then bounds the time
  derivative of the metric matrix by `Λ`, hence the metric matrix moves by at most `n Λ t` in the
  quadratic-form sense (`nbs_quadForm_time_sub`), hence — by the slack built into the choice of
  `τ` — it is still `(3 lam / 4)`-elliptic on `[0, t]`;
* `(lam/2)`-ellipticity is an *open* condition in time (the coefficient family is continuous at
  every interior time, `nbs_uniform_cont`), so it extends a little beyond `t`.

Formally: the supremum of the set of times up to which `(lam/2)`-ellipticity holds is shown to be
the right endpoint of the interval.
-/

set_option maxHeartbeats 1000000

open MeasureTheory BigOperators
open Filter
open scoped Topology

namespace Work.Diff.STE.flat

open Work.Diff.STE.Flat

noncomputable section

variable {n : ℕ}

/-- The quadratic form of the *real part* of a matrix: `∑ i, ∑ j, (reMat A) i j vᵢ vⱼ`. -/
def nbsQ (A : MatC n) (v : Fin n → ℝ) : ℝ := ∑ i, ∑ j, reMat A i j * v i * v j

@[simp] lemma nbsQ_apply (A : MatC n) (v : Fin n → ℝ) :
    nbsQ A v = ∑ i, ∑ j, reMat A i j * v i * v j := rfl

/-- The ellipticity predicate: the quadratic form of the metric matrix at time `σ` dominates
`a * ∑ᵢ vᵢ²`. -/
abbrev nbsEll (c : ℝ → (Fin n → ℤ) → MatC n) (a : ℝ) (σ : ℝ) : Prop :=
  ∀ (x : Fin n → ℝ) (v : Fin n → ℝ), a * ∑ i, (v i) ^ 2 ≤ nbsQ (seriesFunM (c σ) x) v

/-- **Lipschitz comparison of quadratic forms.**  If the entries of `A - A'` are bounded by `M`,
then the two quadratic forms differ by at most `n · M · ∑ vᵢ²`. -/
lemma nbs_quadForm_sub_le (A A' : MatC n) (v : Fin n → ℝ) {M : ℝ} (hM : 0 ≤ M)
    (hd : ∀ i j, ‖A i j - A' i j‖ ≤ M) :
    nbsQ A v - nbsQ A' v ≤ (n : ℝ) * M * ∑ i, (v i) ^ 2 := by
  rw [nbsQ, nbsQ]
  have hdiff : ∑ i, ∑ j, reMat A i j * v i * v j - ∑ i, ∑ j, reMat A' i j * v i * v j
      = ∑ i, ∑ j, reMat (A - A') i j * v i * v j := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [reMat_apply, Pi.sub_apply, Complex.sub_re]
    ring
  rw [hdiff]
  have h1 : ∑ i : Fin n, ∑ j : Fin n, reMat (A - A') i j * v i * v j
      ≤ ∑ i : Fin n, ∑ j : Fin n, M * (|v i| * |v j|) := by
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have hre : |reMat (A - A') i j| ≤ M := by
      calc |reMat (A - A') i j| = |((A - A') i j).re| := rfl
        _ ≤ ‖(A - A') i j‖ := Complex.abs_re_le_norm _
        _ ≤ M := hd i j
    calc reMat (A - A') i j * v i * v j
        ≤ |reMat (A - A') i j * v i * v j| := le_abs_self _
      _ = |reMat (A - A') i j| * (|v i| * |v j|) := by
            rw [abs_mul, abs_mul]; ring
      _ ≤ M * (|v i| * |v j|) := mul_le_mul_of_nonneg_right hre (by positivity)
  have h2 : ∑ i : Fin n, ∑ j : Fin n, M * (|v i| * |v j|)
      = M * ((∑ i, |v i|) ^ 2) := by
    rw [sq, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
  have h3 : ((∑ i, |v i|) ^ 2) ≤ (n : ℝ) * ∑ i, (v i) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := fun i : Fin n => |v i|)
    simpa [Finset.card_univ, Fintype.card_fin, sq_abs] using h
  calc ∑ i : Fin n, ∑ j : Fin n, reMat (A - A') i j * v i * v j
      ≤ ∑ i : Fin n, ∑ j : Fin n, M * (|v i| * |v j|) := h1
    _ = M * ((∑ i, |v i|) ^ 2) := h2
    _ ≤ M * ((n : ℝ) * ∑ i, (v i) ^ 2) := mul_le_mul_of_nonneg_left h3 hM
    _ = (n : ℝ) * M * ∑ i, (v i) ^ 2 := by ring

/-- **The time derivative of the entries of the metric matrix**, computed from the Galerkin ODE
as the finite sum of the box Fourier coefficients of the nonlinearity. -/
lemma nbs_hasDerivAt_seriesFunM {n N : ℕ} {Tc : ℝ} (c : ℝ → (Fin n → ℤ) → MatC n)
    (g : ℝ → (Fin n → ℤ) → MatC n) (hc : ∀ t k', k' ∉ box n N → c t k' = 0)
    (hd : ∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ k' ∈ box n N, ∀ i j,
      HasDerivAt (fun σ => c σ k' i j) (g t k' i j) t)
    (x : Fin n → ℝ) (i j : Fin n) {t : ℝ} (ht : t ∈ Set.Ico (0 : ℝ) Tc) :
    HasDerivAt (fun σ => seriesFunM (c σ) x i j)
      (∑ m : box n N, g t m.1 i j * fourierExp m.1 x) t := by
  classical
  have hcongr : (fun σ => seriesFunM (c σ) x i j)
      = fun σ => ∑ m : box n N, c σ m.1 i j * fourierExp m.1 x := by
    funext σ
    exact seriesFunM_eq_sum (c σ) (hc σ) x i j
  rw [hcongr]
  exact HasDerivAt.fun_sum fun m _ => (hd t ht m.1 m.2 i j).mul_const (fourierExp m.1 x)

/-- **The Lipschitz bound in time.**  If the box Fourier coefficients of the nonlinearity are
summable with `ℓ¹`-norm at most `Λ` on `[0,τ]`, then the entries of `seriesFunM` are
`Λ`-Lipschitz in time on `[0,τ]`. -/
lemma nbs_lipschitz_of_l1_bound {n N : ℕ} {Tc : ℝ} (c : ℝ → (Fin n → ℤ) → MatC n)
    (g : ℝ → (Fin n → ℤ) → MatC n) (hc : ∀ t k', k' ∉ box n N → c t k' = 0)
    (hd : ∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ k' ∈ box n N, ∀ i j,
      HasDerivAt (fun σ => c σ k' i j) (g t k' i j) t)
    {Λ τ : ℝ} (hτ : τ < Tc) (hΛ : 0 ≤ Λ)
    (hbdd : ∀ t ∈ Set.Icc (0 : ℝ) τ, ∀ i j,
      Summable (fun m : Fin n → ℤ => ‖g t m i j‖) ∧
      (∑' m : Fin n → ℤ, ‖g t m i j‖) ≤ Λ)
    (x : Fin n → ℝ) (i j : Fin n) :
    ∀ t ∈ Set.Icc (0 : ℝ) τ,
      ‖seriesFunM (c t) x i j - seriesFunM (c 0) x i j‖ ≤ Λ * t := by
  intro t ht
  have hdiff : ∀ σ ∈ Set.Icc (0 : ℝ) τ,
      DifferentiableAt ℝ (fun s => seriesFunM (c s) x i j) σ := by
    intro σ hσ
    exact (nbs_hasDerivAt_seriesFunM c g hc hd x i j
      ⟨hσ.1, lt_of_le_of_lt hσ.2 hτ⟩).differentiableAt
  have hderiv : ∀ σ ∈ Set.Icc (0 : ℝ) τ,
      ‖deriv (fun s => seriesFunM (c s) x i j) σ‖ ≤ Λ := by
    intro σ hσ
    rw [(nbs_hasDerivAt_seriesFunM c g hc hd x i j ⟨hσ.1, lt_of_le_of_lt hσ.2 hτ⟩).deriv]
    calc ‖∑ m : box n N, g σ m.1 i j * fourierExp m.1 x‖
        ≤ ∑ m : box n N, ‖g σ m.1 i j * fourierExp m.1 x‖ := norm_sum_le _ _
      _ = ∑ m : box n N, ‖g σ m.1 i j‖ := by
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [norm_mul, Work.Diff.STE.norm_fourierExp, mul_one]
      _ = ∑ m ∈ box n N, ‖g σ m i j‖ := Finset.sum_attach (box n N) (fun m => ‖g σ m i j‖)
      _ ≤ ∑' m : Fin n → ℤ, ‖g σ m i j‖ :=
          Summable.sum_le_tsum (box n N) (fun m _ => norm_nonneg _) (hbdd σ hσ i j).1
      _ ≤ Λ := (hbdd σ hσ i j).2
  have h := Convex.norm_image_sub_le_of_norm_deriv_le hdiff hderiv (convex_Icc 0 τ)
    (Set.left_mem_Icc.mpr (by linarith [ht.1, ht.2] : (0 : ℝ) ≤ τ)) ht
  simpa [Real.norm_eq_abs, abs_of_nonneg ht.1] using h

/-- **Comparison of the quadratic forms at time `t` and at time `0`.** -/
lemma nbs_quadForm_time_sub {n N : ℕ} {Tc Λ τ : ℝ} (hΛ : 0 ≤ Λ) (hτ0 : 0 ≤ τ) (hτ : τ < Tc)
    (c : ℝ → (Fin n → ℤ) → MatC n) (g : ℝ → (Fin n → ℤ) → MatC n)
    (hc : ∀ t k', k' ∉ box n N → c t k' = 0)
    (hd : ∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ k' ∈ box n N, ∀ i j,
      HasDerivAt (fun σ => c σ k' i j) (g t k' i j) t)
    (hbdd : ∀ t ∈ Set.Icc (0 : ℝ) τ, ∀ i j,
      Summable (fun m : Fin n → ℤ => ‖g t m i j‖) ∧
      (∑' m : Fin n → ℤ, ‖g t m i j‖) ≤ Λ)
    (x : Fin n → ℝ) (v : Fin n → ℝ) :
    nbsQ (seriesFunM (c 0) x) v - nbsQ (seriesFunM (c τ) x) v
      ≤ (n : ℝ) * (Λ * τ) * ∑ i, (v i) ^ 2 := by
  refine nbs_quadForm_sub_le _ _ v (mul_nonneg hΛ hτ0) ?_
  intro i j
  have h := nbs_lipschitz_of_l1_bound c g hc hd hτ hΛ hbdd x i j τ ⟨hτ0, le_rfl⟩
  simpa [norm_sub_rev] using h

/-- **Uniform-in-`x` continuity of the metric matrix at a time where the coefficient family is
continuous.**  The bound is *uniform in the space variable* `x`, which is what makes the
quadratic-form comparison work pointwise. -/
lemma nbs_uniform_cont {n N : ℕ} (c : ℝ → (Fin n → ℤ) → MatC n) (z : ℝ)
    (hc : ∀ k' ∈ box n N, ∀ (i j : Fin n), ContinuousAt (fun σ => c σ k' i j) z)
    (hsupp : ∀ (σ : ℝ) (k' : Fin n → ℤ), k' ∉ box n N → c σ k' = 0) :
    ∀ ε > 0, ∃ δ > 0, ∀ σ, |σ - z| < δ → ∀ (x : Fin n → ℝ) (i j : Fin n),
      ‖seriesFunM (c σ) x i j - seriesFunM (c z) x i j‖ ≤ ε := by
  intro ε hε
  -- the single auxiliary scalar quantity whose convergence controls everything
  have hinner : ∀ m : box n N,
      Tendsto (fun σ => ∑ i, ∑ j, ‖c σ m.1 i j - c z m.1 i j‖) (𝓝 z) (𝓝 0) := by
    intro m
    have hi : ∀ i : Fin n,
        Tendsto (fun σ => ∑ j, ‖c σ m.1 i j - c z m.1 i j‖) (𝓝 z) (𝓝 0) := by
      intro i
      have hj : ∀ j : Fin n,
          Tendsto (fun σ => ‖c σ m.1 i j - c z m.1 i j‖) (𝓝 z) (𝓝 0) := by
        intro j
        have h0 : Tendsto (fun σ => c σ m.1 i j) (𝓝 z) (𝓝 (c z m.1 i j)) := hc m.1 m.2 i j
        have h1 : Tendsto (fun σ => c σ m.1 i j - c z m.1 i j) (𝓝 z) (𝓝 0) := by
          have hsub := h0.sub_const (c z m.1 i j)
          simpa using hsub
        simpa using h1.norm
      simpa using tendsto_finsetSum Finset.univ (fun j _ => hj j)
    simpa using tendsto_finsetSum Finset.univ (fun i _ => hi i)
  have hD : Tendsto (fun σ => ∑ m : box n N, ∑ i, ∑ j, ‖c σ m.1 i j - c z m.1 i j‖)
      (𝓝 z) (𝓝 0) := by
    simpa using tendsto_finsetSum Finset.univ (fun m _ => hinner m)
  have hEv : ∀ᶠ σ in 𝓝 z,
      (∑ m : box n N, ∑ i, ∑ j, ‖c σ m.1 i j - c z m.1 i j‖) < ε :=
    (tendsto_order.1 hD).2 ε hε
  obtain ⟨δ, hδ0, hδ⟩ := Metric.eventually_nhds_iff.mp hEv
  refine ⟨δ, hδ0, fun σ hσ x i j => ?_⟩
  have hσz : dist σ z < δ := by rw [Real.dist_eq]; exact hσ
  have hDlt : (∑ m : box n N, ∑ i', ∑ j', ‖c σ m.1 i' j' - c z m.1 i' j'‖) < ε :=
    hδ (y := σ) hσz
  calc ‖seriesFunM (c σ) x i j - seriesFunM (c z) x i j‖
      = ‖∑ m : box n N, (c σ m.1 i j - c z m.1 i j) * fourierExp m.1 x‖ := by
        rw [seriesFunM_eq_sum (c σ) (hsupp σ) x i j,
          seriesFunM_eq_sum (c z) (hsupp z) x i j, ← Finset.sum_sub_distrib]
        congr 1
        exact Finset.sum_congr rfl fun m _ => by ring
    _ ≤ ∑ m : box n N, ‖(c σ m.1 i j - c z m.1 i j) * fourierExp m.1 x‖ := norm_sum_le _ _
    _ = ∑ m : box n N, ‖c σ m.1 i j - c z m.1 i j‖ := by
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [norm_mul, Work.Diff.STE.norm_fourierExp, mul_one]
    _ ≤ ∑ m : box n N, ∑ i', ∑ j', ‖c σ m.1 i' j' - c z m.1 i' j'‖ := by
        refine Finset.sum_le_sum fun m _ => ?_
        have h2 : ‖c σ m.1 i j - c z m.1 i j‖
            ≤ ∑ j' : Fin n, ‖c σ m.1 i j' - c z m.1 i j'‖ :=
          Finset.single_le_sum (f := fun j' => ‖c σ m.1 i j' - c z m.1 i j'‖)
            (fun j' _ => norm_nonneg _) (Finset.mem_univ j)
        have h1 : (∑ j' : Fin n, ‖c σ m.1 i j' - c z m.1 i j'‖)
            ≤ ∑ i' : Fin n, ∑ j' : Fin n, ‖c σ m.1 i' j' - c z m.1 i' j'‖ :=
          Finset.single_le_sum
            (f := fun i' => ∑ j' : Fin n, ‖c σ m.1 i' j' - c z m.1 i' j'‖)
            (fun i' _ => Finset.sum_nonneg fun j' _ => norm_nonneg _)
            (Finset.mem_univ i)
        exact le_trans h2 h1
    _ ≤ ε := le_of_lt hDlt

/-- Continuity (in the filter sense) of the entries of the metric matrix at a time where the
coefficient family is continuous. -/
lemma nbs_tendsto_seriesFunM {n N : ℕ} {c : ℝ → (Fin n → ℤ) → MatC n} {z : ℝ}
    (hc : ∀ k' ∈ box n N, ∀ (i j : Fin n), ContinuousAt (fun σ => c σ k' i j) z)
    (hsupp : ∀ (σ : ℝ) (k' : Fin n → ℤ), k' ∉ box n N → c σ k' = 0)
    (x : Fin n → ℝ) (i j : Fin n) :
    Tendsto (fun σ => seriesFunM (c σ) x i j) (𝓝 z) (𝓝 (seriesFunM (c z) x i j)) := by
  have hcongr : (fun σ => seriesFunM (c σ) x i j)
      = fun σ => ∑ m : box n N, c σ m.1 i j * fourierExp m.1 x := by
    funext σ
    exact seriesFunM_eq_sum (c σ) (hsupp σ) x i j
  rw [hcongr, seriesFunM_eq_sum (c z) (hsupp z) x i j]
  exact tendsto_finsetSum Finset.univ
    (fun m _ => (hc m.1 m.2 i j).mul_const (fourierExp m.1 x))

/-- Continuity of the quadratic form of the metric matrix at such a time. -/
lemma nbs_tendsto_quadForm {n N : ℕ} {c : ℝ → (Fin n → ℤ) → MatC n} {z : ℝ}
    (hc : ∀ k' ∈ box n N, ∀ (i j : Fin n), ContinuousAt (fun σ => c σ k' i j) z)
    (hsupp : ∀ (σ : ℝ) (k' : Fin n → ℤ), k' ∉ box n N → c σ k' = 0)
    (x : Fin n → ℝ) (v : Fin n → ℝ) :
    Tendsto (fun σ => nbsQ (seriesFunM (c σ) x) v) (𝓝 z)
      (𝓝 (nbsQ (seriesFunM (c z) x) v)) := by
  unfold nbsQ
  refine tendsto_finsetSum Finset.univ fun i _ => ?_
  refine tendsto_finsetSum Finset.univ fun j _ => ?_
  have h1 : Tendsto (fun σ => seriesFunM (c σ) x i j) (𝓝 z) (𝓝 (seriesFunM (c z) x i j)) :=
    nbs_tendsto_seriesFunM hc hsupp x i j
  have h2 : Tendsto (fun σ => (seriesFunM (c σ) x i j).re) (𝓝 z)
      (𝓝 ((seriesFunM (c z) x i j).re)) :=
    Complex.continuous_re.continuousAt.comp h1
  exact (h2.mul_const (v i)).mul_const (v j)

theorem nonlin_bound_short {n : ℕ} (hn : 1 ≤ n)
    (Φ : (Fin n → ℝ) × Work.Diff.STE.Flat.Jet n → Work.Diff.STE.Flat.MatC n)
    (hshape : Work.Diff.STE.Flat.IsDeTurckNonlin Φ)
    (k : ℕ) (hk : Fintype.card (Fin n) + 4 < 2 * k)
    (lam : ℝ) (hlam : 0 < lam) (E : ℝ) (hE : 0 ≤ E) :
    ∃ (Λ : ℝ) (τ : ℝ), 0 ≤ Λ ∧ 0 < τ ∧
      ∀ (Tc : ℝ) (hc : 0 < Tc) (N : ℕ) (c : ℝ → (Fin n → ℤ) → Work.Diff.STE.Flat.MatC n),
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ k' ∈ Work.Diff.STE.Flat.box n N, ∀ (i j : Fin n),
          HasDerivAt (fun σ => c σ k' i j)
            (Work.Diff.STE.fourierCoeff (fun x =>
              Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x) i j) k') t) →
        (∀ (t : ℝ) (k' : Fin n → ℤ), k' ∉ Work.Diff.STE.Flat.box n N → c t k' = 0) →
        (∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ j ≤ k,
          Work.Diff.STE.Flat.CSqM j (c t) ≤ E) →
        (∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
          lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
            Work.Diff.STE.Flat.reMat (Work.Diff.STE.Flat.seriesFunM (c 0) x) i j * v i * v j) →
        ∀ t ∈ Set.Ico (0 : ℝ) (min τ Tc), ∀ i j : Fin n,
          Summable (fun m : Fin n → ℤ => ‖Work.Diff.STE.fourierCoeff
            (fun x => Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x) i j) m‖) ∧
          (∑' m : Fin n → ℤ, ‖Work.Diff.STE.fourierCoeff
            (fun x => Φ (x, Work.Diff.STE.Flat.jetM (Work.Diff.STE.Flat.seriesFunM (c t)) x) i j) m‖) ≤ Λ := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := nonlin_coeff_bound hn Φ hshape k hk lam hlam E hE
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnRpos : (0 : ℝ) < (n : ℝ) := by linarith
  set K : ℝ := (n : ℝ) * max Λ 1 with hKdef
  have hKpos : 0 < K := by
    rw [hKdef]
    exact mul_pos hnRpos (by linarith [le_max_right Λ 1])
  have hτpos : 0 < lam / (4 * K) := by positivity
  refine ⟨Λ, lam / (4 * K), hΛ0, hτpos, ?_⟩
  intro Tc hc N c hderiv hsupp henergy hell0
  let τ₀ : ℝ := min (lam / (4 * K)) Tc
  let g : ℝ → (Fin n → ℤ) → MatC n :=
    fun σ k' i j => fourierCoeff (fun x => Φ (x, jetM (seriesFunM (c σ)) x) i j) k'
  have hτ0l : τ₀ ≤ lam / (4 * K) := min_le_left (lam / (4 * K)) Tc
  have hτ0r : τ₀ ≤ Tc := min_le_right (lam / (4 * K)) Tc
  have hderiv' : ∀ t ∈ Set.Ico (0 : ℝ) Tc, ∀ k' ∈ box n N, ∀ i j,
      HasDerivAt (fun σ => c σ k' i j) (g t k' i j) t :=
    fun t ht k' hk' i j => hderiv t ht k' hk' i j
  -- `(lam/2)`-ellipticity at time `0`
  have hQ0 : nbsEll c (lam / 2) 0 := by
    intro x v
    have h0 : lam * ∑ i, (v i) ^ 2 ≤ nbsQ (seriesFunM (c 0) x) v := by
      simpa [nbsQ] using hell0 x v
    have hsq : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    calc (lam / 2) * ∑ i, (v i) ^ 2 ≤ lam * ∑ i, (v i) ^ 2 :=
          mul_le_mul_of_nonneg_right (by linarith) hsq
      _ ≤ nbsQ (seriesFunM (c 0) x) v := h0
  -- (A) at a single time, `(lam/2)`-ellipticity gives the `ℓ¹` bound (the sibling lemma)
  have hQl1 : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, nbsEll c (lam / 2) t → ∀ i j,
      Summable (fun m : Fin n → ℤ => ‖g t m i j‖) ∧
      (∑' m : Fin n → ℤ, ‖g t m i j‖) ≤ Λ := by
    intro t ht hQ i j
    have htTc : t ∈ Set.Ico (0 : ℝ) Tc := ⟨ht.1, lt_of_lt_of_le ht.2 hτ0r⟩
    refine hΛ N (c t) (hsupp t) (fun j hj => henergy t htTc j hj) ?_ i j
    exact fun x v => by simpa [nbsQ] using hQ x v
  -- (B) `(lam/2)`-ellipticity on `[0,t]` bounds the quadratic form at `t` by `(3 lam/4) ‖v‖²`
  have hquad_le : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, (∀ σ ∈ Set.Icc (0 : ℝ) t, nbsEll c (lam / 2) σ) →
      ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
        (3 * lam / 4) * ∑ i, (v i) ^ 2 ≤ nbsQ (seriesFunM (c t) x) v := by
    intro t ht hQ x v
    have htTc : t < Tc := lt_of_lt_of_le ht.2 hτ0r
    have hbdd : ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ i j,
        Summable (fun m : Fin n → ℤ => ‖g s m i j‖) ∧
        (∑' m : Fin n → ℤ, ‖g s m i j‖) ≤ Λ := by
      intro s hs i j
      exact hQl1 s ⟨hs.1, lt_of_le_of_lt hs.2 ht.2⟩ (hQ s hs) i j
    have hcomp := nbs_quadForm_time_sub (N := N) (Tc := Tc) (Λ := Λ) (τ := t)
      hΛ0 ht.1 htTc c g hsupp hderiv' hbdd x v
    have hell : lam * ∑ i, (v i) ^ 2 ≤ nbsQ (seriesFunM (c 0) x) v := by
      simpa [nbsQ] using hell0 x v
    have hsq : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have htK : t ≤ lam / (4 * K) := le_trans (le_of_lt ht.2) hτ0l
    have h2 : (n : ℝ) * (Λ * t) * ∑ i, (v i) ^ 2 ≤ (lam / 4) * ∑ i, (v i) ^ 2 := by
      have htl : Λ * t ≤ max Λ 1 * t := mul_le_mul_of_nonneg_right (le_max_left _ _) ht.1
      have h3 : (n : ℝ) * (Λ * t) ≤ K * t := by
        rw [hKdef]
        calc (n : ℝ) * (Λ * t) ≤ (n : ℝ) * (max Λ 1 * t) :=
              mul_le_mul_of_nonneg_left htl (le_of_lt hnRpos)
          _ = ((n : ℝ) * max Λ 1) * t := by ring
      have h4 : K * t ≤ lam / 4 := by
        calc K * t ≤ K * (lam / (4 * K)) := mul_le_mul_of_nonneg_left htK (le_of_lt hKpos)
          _ = lam / 4 := by field_simp
      exact mul_le_mul_of_nonneg_right (le_trans h3 h4) hsq
    have hkey : (3 * lam / 4) * ∑ i, (v i) ^ 2
        = lam * ∑ i, (v i) ^ 2 - (lam / 4) * ∑ i, (v i) ^ 2 := by ring
    linarith [hcomp, hell, h2, hkey]
  -- (C) continuity of the coefficient family inside `[0, τ₀)`
  have hcontc : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, ∀ k' ∈ box n N, ∀ i j,
      ContinuousAt (fun σ => c σ k' i j) t := by
    intro t ht k' hk' i j
    exact (hderiv t ⟨ht.1, lt_of_lt_of_le ht.2 hτ0r⟩ k' hk' i j).continuousAt
  -- (D) `(lam/2)`-ellipticity on `[0,t]` extends a little to the right of `t`
  have hopen : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, (∀ σ ∈ Set.Icc (0 : ℝ) t, nbsEll c (lam / 2) σ) →
      ∃ ε > 0, ∀ σ ∈ Set.Icc (0 : ℝ) (t + ε), nbsEll c (lam / 2) σ := by
    intro t ht hQ
    obtain ⟨δ, hδ0, hδ⟩ := nbs_uniform_cont (N := N) c t
      (fun k' hk' i j => hcontc t ht k' hk' i j) hsupp (lam / (8 * (n : ℝ))) (by positivity)
    refine ⟨δ / 2, by positivity, fun σ hσ x v => ?_⟩
    rcases le_or_gt σ t with hσt | hσt
    · have h1 := hquad_le σ ⟨hσ.1, lt_of_le_of_lt hσt ht.2⟩
        (fun ρ hρ => hQ ρ ⟨hρ.1, le_trans hρ.2 hσt⟩) x v
      have hsq : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      have h2 := mul_le_mul_of_nonneg_right (by linarith : lam / 2 ≤ 3 * lam / 4) hsq
      linarith [h1, h2]
    · have hquadt := hquad_le t ht hQ x v
      have hM : ∀ i j, ‖seriesFunM (c t) x i j - seriesFunM (c σ) x i j‖
          ≤ lam / (8 * (n : ℝ)) := by
        intro i j
        rw [norm_sub_rev]
        refine hδ σ ?_ x i j
        rw [abs_of_pos (by linarith : (0 : ℝ) < σ - t)]
        linarith [hσ.2, hδ0]
      have hcomp := nbs_quadForm_sub_le (seriesFunM (c t) x) (seriesFunM (c σ) x) v
        (by positivity : (0 : ℝ) ≤ lam / (8 * (n : ℝ))) hM
      have hcoef : (n : ℝ) * (lam / (8 * (n : ℝ))) = lam / 8 := by field_simp
      have hstep : (n : ℝ) * (lam / (8 * (n : ℝ))) * ∑ i, (v i) ^ 2
          ≤ (lam / 8) * ∑ i, (v i) ^ 2 := by rw [hcoef]
      have hsq : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
      have hkey : (3 * lam / 4) * ∑ i, (v i) ^ 2 - (lam / 8) * ∑ i, (v i) ^ 2
          = (5 * lam / 8) * ∑ i, (v i) ^ 2 := by ring
      have h5 : (5 * lam / 8) * ∑ i, (v i) ^ 2 ≤ nbsQ (seriesFunM (c σ) x) v := by
        linarith [hquadt, hcomp, hstep, hkey]
      have h6 := mul_le_mul_of_nonneg_right (by linarith : lam / 2 ≤ 5 * lam / 8) hsq
      linarith [h5, h6]
  -- the supremum argument
  have hmain : ∀ t ∈ Set.Ico (0 : ℝ) τ₀, nbsEll c (lam / 2) t := by
    by_contra hcon
    simp only [not_forall, not_le, nbsEll] at hcon
    obtain ⟨t₀, ht₀, ht₀Q⟩ := hcon
    let Z : Set ℝ := {s | 0 ≤ s ∧ s < τ₀ ∧ ∃ (x : Fin n → ℝ) (v : Fin n → ℝ),
      nbsQ (seriesFunM (c s) x) v < (lam / 2) * ∑ i, (v i) ^ 2}
    have ht₀Z : t₀ ∈ Z := ⟨ht₀.1, ht₀.2, ht₀Q⟩
    have hZne : Z.Nonempty := ⟨t₀, ht₀Z⟩
    have hbdd : BddBelow Z := ⟨0, fun s hs => hs.1⟩
    have hzle : sInf Z ≤ t₀ := csInf_le hbdd ht₀Z
    have hz0 : 0 ≤ sInf Z := le_csInf hZne fun b hb => hb.1
    have hzlt : sInf Z < τ₀ := lt_of_le_of_lt hzle ht₀.2
    have hQbelow : ∀ σ ∈ Set.Ico (0 : ℝ) (sInf Z), nbsEll c (lam / 2) σ := by
      intro σ hσ
      by_contra hσQ
      have hmem : σ ∈ Z := ⟨hσ.1, lt_trans hσ.2 hzlt,
        by simpa only [nbsEll, not_forall, not_le] using hσQ⟩
      have hle : sInf Z ≤ σ := csInf_le hbdd hmem
      linarith [hσ.2]
    have hQz : nbsEll c (lam / 2) (sInf Z) := by
      rcases eq_or_lt_of_le hz0 with hz00 | hzpos
      · rw [← hz00]; exact hQ0
      · intro x v
        have hev : ∀ᶠ σ in 𝓝[<] (sInf Z),
            (3 * lam / 4) * ∑ i, (v i) ^ 2 ≤ nbsQ (seriesFunM (c σ) x) v := by
          rw [eventually_nhdsWithin_iff]
          filter_upwards [isOpen_Ioi.mem_nhds hzpos] with σ hσpos hσlt
          exact hquad_le σ ⟨le_of_lt hσpos, lt_trans hσlt hzlt⟩
            (fun ρ hρ => hQbelow ρ ⟨hρ.1, lt_of_le_of_lt hρ.2 hσlt⟩) x v
        have htend := nbs_tendsto_quadForm (N := N) (c := c) (z := sInf Z)
          (fun k' hk' i j => hcontc (sInf Z) ⟨hz0, hzlt⟩ k' hk' i j) hsupp x v
        have hlim := ge_of_tendsto (htend.mono_left nhdsWithin_le_nhds) hev
        have hsq : 0 ≤ ∑ i, (v i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
        have h2 := mul_le_mul_of_nonneg_right (by linarith : lam / 2 ≤ 3 * lam / 4) hsq
        linarith [hlim, h2]
    -- a time in `Z` close to the infimum, and the continuity bound there
    obtain ⟨δ, hδ0, hδ⟩ := nbs_uniform_cont (N := N) c (sInf Z)
      (fun k' hk' i j => hcontc (sInf Z) ⟨hz0, hzlt⟩ k' hk' i j) hsupp
      (lam / (8 * (n : ℝ))) (by positivity)
    obtain ⟨s, hsZ, hsz⟩ := (csInf_lt_iff hbdd hZne).mp
      (show sInf Z < sInf Z + δ by linarith)
    have hszd : |s - sInf Z| < δ := by
      have hsge : sInf Z ≤ s := csInf_le hbdd hsZ
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ s - sInf Z)]
      linarith
    obtain ⟨x₀, v₀, hv₀⟩ := hsZ.2.2
    have hsquad : (3 * lam / 4) * ∑ i, (v₀ i) ^ 2
        ≤ nbsQ (seriesFunM (c (sInf Z)) x₀) v₀ :=
      hquad_le (sInf Z) ⟨hz0, hzlt⟩
        (fun σ hσ => by
          rcases lt_or_eq_of_le hσ.2 with h | h
          · exact hQbelow σ ⟨hσ.1, h⟩
          · rw [h]; exact hQz) x₀ v₀
    have hscont : nbsQ (seriesFunM (c (sInf Z)) x₀) v₀ - nbsQ (seriesFunM (c s) x₀) v₀
        ≤ (n : ℝ) * (lam / (8 * (n : ℝ))) * ∑ i, (v₀ i) ^ 2 := by
      refine nbs_quadForm_sub_le _ _ v₀ (by positivity) ?_
      intro i j
      rw [norm_sub_rev]
      exact hδ s hszd x₀ i j
    have hcoef : (n : ℝ) * (lam / (8 * (n : ℝ))) = lam / 8 := by field_simp
    have hstep : (n : ℝ) * (lam / (8 * (n : ℝ))) * ∑ i, (v₀ i) ^ 2
        ≤ (lam / 8) * ∑ i, (v₀ i) ^ 2 := by rw [hcoef]
    have hkey : (3 * lam / 4) * ∑ i, (v₀ i) ^ 2 - (lam / 8) * ∑ i, (v₀ i) ^ 2
        = (5 * lam / 8) * ∑ i, (v₀ i) ^ 2 := by ring
    have hbig : (5 * lam / 8) * ∑ i, (v₀ i) ^ 2 ≤ nbsQ (seriesFunM (c s) x₀) v₀ := by
      linarith [hsquad, hscont, hstep, hkey]
    have hlt : (5 * lam / 8) * ∑ i, (v₀ i) ^ 2 < (lam / 2) * ∑ i, (v₀ i) ^ 2 :=
      lt_of_le_of_lt hbig hv₀
    have hsq : 0 ≤ ∑ i, (v₀ i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hpos : 0 < ∑ i, (v₀ i) ^ 2 := by
      rcases eq_or_lt_of_le hsq with h | h
      · rw [← h] at hlt; simp at hlt
      · exact h
    nlinarith [hlt, hpos, hlam]
  intro t ht i j
  exact hQl1 t ht (hmain t ht) i j

end

end Work.Diff.STE.flat
