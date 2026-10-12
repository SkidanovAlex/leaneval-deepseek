import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Submission.KineticChild
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Many-body localization (IMS) with explicit error — the 3D lift

This is the 3D / N-particle lift of `Submission.Localize` (whose 1D core proved
`ims_identity`, `kin_whole_le_pieces`, `kin_pieces_le_whole_add_err`).  Here the
configuration space is `X N = Fin N → EuclideanSpace ℝ (Fin 3)`, a state is a
smooth function `f : X N → ℝ`, and the localizing cutoffs are smooth functions
`χ j : ℝ³ → ℝ` applied to the coordinate of a *single particle* `i : Fin N`
(the Bridge-slice machinery of `Submission.KineticChild` supplies the
directional derivatives `fderiv ℝ f x (kcDir N i k)` along the unit direction
`kcDir N i k`, and `kcStdBasis k` is the corresponding basis vector of the
one-particle space).

The results:

  * `coord_fderiv` — the slice chain rule: differentiating `y ↦ χ (y i)` along
    `kcDir N i k` gives `fderiv ℝ χ (x i) (kcStdBasis k)`;
  * `slice_deriv_cutoff` — the derivative of the localized state
    `y ↦ χ (y i) · f y` (product rule + slice chain rule);
  * `pu_sum_fderiv_zero` — differentiating the partition-of-unity identity
    `Σⱼ (χⱼ x)² = 1` gives `Σⱼ χⱼ(x)·∂_k χⱼ(x) = 0` (cross-term cancellation);
  * `ims_pointwise_manybody` — the pointwise IMS identity for particle `i`:
        Σⱼ Σₖ (∂_{ik}(χⱼ(x_i)·f))² = Σₖ (∂_{ik}f)² + f²·Σⱼ Σₖ (∂ₖχⱼ(x_i))²;
  * `ims_manybody_identity` — the integrated version over `box N L` (the exact
    identity with the explicit localization error on the right);
  * `ims_pieces_ge_whole` — splitting never lowers the total kinetic:
        Σⱼ Σₖ ∫ (∂_{ik}(χⱼ(x_i)·f))² ≥ Σₖ ∫ (∂_{ik}f)²;
  * `ims_pieces_le_whole_err` — the explicit-error direction: the split kinetic
    exceeds the whole by exactly `∫ f²·ΣⱼΣₖ(∂ₖχⱼ(x_i))²`, and hence by at most
    `C·∫f²` when `C` bounds that error density pointwise.

These are the building blocks of every cell / bracketing argument (LY, FS):
localizing a state into cells costs kinetic energy at most
`∫ f²·Σⱼ|∇χⱼ(x_i)|²`, concentrated in the seams of the partition.
-/

namespace Submission

open _root_.BoseGases
open _root_.BoseGases.CInfty0Box
set_option autoImplicit false

namespace BoseGases

open Filter Metric MeasureTheory Laplacian
open scoped ContDiff Topology Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Directional derivative along a line: `fderiv g x v` is the derivative of the
one-dimensional restriction `t ↦ g (x + t • v)` at `0`. -/
private lemma ims_fderiv_eq_lineDeriv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} (x v : E) (hg : DifferentiableAt ℝ g x) :
    fderiv ℝ g x v = deriv (fun t : ℝ => g (x + t • v)) 0 := by
  let p : ℝ → E := fun t => x + t • v
  have hp0 : p 0 = x := by simp [p]
  have hp : HasDerivAt p v 0 := by
    dsimp [p]
    simp
    simpa using (HasDerivAt.smul_const (𝕜 := ℝ) (𝕜' := ℝ) (F := E) (hasDerivAt_id (0 : ℝ)) v)
  have hg' : HasFDerivAt g (fderiv ℝ g x) x := hg.hasFDerivAt
  have hc : HasDerivAt (g ∘ p) (fderiv ℝ g x v) 0 := by
    exact HasFDerivAt.comp_hasDerivAt_of_eq (f := p) (x := 0) (y := x) hg' hp hp0.symm
  have hd : deriv (fun t : ℝ => g (x + t • v)) 0 = fderiv ℝ g x v := by
    simpa [p, Function.comp_def] using hc.deriv
  exact hd.symm

/-- The direction `kcDir N i k` moves particle `i` by the standard basis vector. -/
private lemma ims_kcDir_apply_eq (N : ℕ) (i : Fin N) (k : Fin 3) :
    (kcDir N i k) i = kcStdBasis k := by
  simp [kcDir]

/-- Pure algebra for the many-body IMS identity: expanding the square and summing
over `j`, `k` reduces the cross terms to zero via the differentiated partition of
unity `Σⱼ aⱼ·bⱼₖ = 0`, and the `cₖ²`-coefficient is `Σⱼ aⱼ² = 1`. -/
private lemma ims_sq_sum_identity {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ι → ℝ) (b : ι → κ → ℝ) (c : κ → ℝ) (m : ℝ)
    (ha : (∑ j : ι, (a j)^2) = 1) (hb : ∀ k : κ, (∑ j : ι, a j * b j k) = 0) :
    (∑ j : ι, ∑ k : κ, (a j * c k + b j k * m)^2) =
      (∑ k : κ, (c k)^2) + (m^2) * (∑ j : ι, ∑ k : κ, (b j k)^2) := by
  have h1 : (∑ j : ι, ∑ k : κ, (a j)^2 * (c k)^2) = ∑ k : κ, (c k)^2 := by
    calc
      (∑ j : ι, ∑ k : κ, (a j)^2 * (c k)^2)
          = ∑ j : ι, (a j)^2 * (∑ k : κ, (c k)^2) := by
            refine Finset.sum_congr rfl (fun j hj => ?_)
            rw [Finset.mul_sum]
      _ = (∑ j : ι, (a j)^2) * (∑ k : κ, (c k)^2) := by rw [Finset.sum_mul]
      _ = 1 * (∑ k : κ, (c k)^2) := by rw [ha]
      _ = (∑ k : κ, (c k)^2) := by ring
  have h2 : (∑ j : ι, ∑ k : κ, 2 * (a j * c k) * (b j k * m)) = 0 := by
    calc
      (∑ j : ι, ∑ k : κ, 2 * (a j * c k) * (b j k * m))
          = ∑ k : κ, ∑ j : ι, 2 * (a j * c k) * (b j k * m) := by rw [Finset.sum_comm]
      _ = ∑ k : κ, (2 * m * c k) * (∑ j : ι, a j * b j k) := by
            refine Finset.sum_congr rfl (fun k hk => ?_)
            calc
              (∑ j : ι, 2 * (a j * c k) * (b j k * m))
                  = ∑ j : ι, (2 * m * c k) * (a j * b j k) := by
                    refine Finset.sum_congr rfl (fun j hj => by ring)
              _ = (2 * m * c k) * (∑ j : ι, a j * b j k) := by rw [← Finset.mul_sum]
      _ = ∑ k : κ, (2 * m * c k) * 0 := by
            refine Finset.sum_congr rfl (fun k hk => ?_)
            rw [hb k]
      _ = 0 := by simp
  have h3 : (∑ j : ι, ∑ k : κ, (b j k)^2 * m^2) =
      m^2 * (∑ j : ι, ∑ k : κ, (b j k)^2) := by
    calc
      (∑ j : ι, ∑ k : κ, (b j k)^2 * m^2)
          = ∑ j : ι, (∑ k : κ, (b j k)^2) * m^2 := by
            refine Finset.sum_congr rfl (fun j hj => ?_)
            rw [← Finset.sum_mul]
      _ = (∑ j : ι, ∑ k : κ, (b j k)^2) * m^2 := by rw [← Finset.sum_mul]
      _ = m^2 * (∑ j : ι, ∑ k : κ, (b j k)^2) := by ring
  have hexp : (∑ j : ι, ∑ k : κ, (a j * c k + b j k * m)^2) =
      (∑ j : ι, ∑ k : κ, ((a j)^2 * (c k)^2 + 2 * (a j * c k) * (b j k * m) + (b j k)^2 * m^2)) := by
    refine Finset.sum_congr rfl (fun j hj => ?_)
    refine Finset.sum_congr rfl (fun k hk => ?_)
    ring
  rw [hexp]
  have hsplit : (∑ j : ι, ∑ k : κ, ((a j)^2 * (c k)^2 + 2 * (a j * c k) * (b j k * m) + (b j k)^2 * m^2)) =
      (∑ j : ι, ∑ k : κ, (a j)^2 * (c k)^2) +
      (∑ j : ι, ∑ k : κ, 2 * (a j * c k) * (b j k * m)) +
      (∑ j : ι, ∑ k : κ, (b j k)^2 * m^2) := by
    simp [Finset.sum_add_distrib, add_assoc]
  rw [hsplit, h1, h2, h3]
  ring

/-- A continuous function is integrable on the compact box `box N L` when `L > 0`. -/
private lemma ims_box_cont_integrableOn {N : ℕ} {L : ℝ} (hL : 0 < L)
    {g : X N → ℝ} (hg : Continuous g) : IntegrableOn g (box N L) volume := by
  exact hg.continuousOn.integrableOn_compact (box_compact hL)

/-- Slice chain rule: differentiating `y ↦ χ (y i)` along the direction `v`
moves the derivative onto `χ` and applies it to the `i`-component `v i`. -/
lemma coord_fderiv {N : ℕ} (i : Fin N) {χ : ℝ³ → ℝ} (hχ : ContDiff ℝ 1 χ) (x : X N)
    (v : X N) :
    fderiv ℝ (fun y : X N => χ (y i)) x v = fderiv ℝ χ (x i) (v i) := by
  have hcomp : ContDiff ℝ 1 (fun y : X N => χ (y i)) := by
    have hpi : ContDiff ℝ 1 (fun y : X N => y i) := by
      simpa using (contDiff_apply ℝ (EuclideanSpace ℝ (Fin 3)) (n := 1) (ι := Fin N) i)
    exact hχ.comp hpi
  have hdiff : DifferentiableAt ℝ (fun y : X N => χ (y i)) x :=
    hcomp.differentiable (by norm_num) x
  rw [ims_fderiv_eq_lineDeriv (g := (fun y : X N => χ (y i))) x v hdiff]
  have hpath : (fun t : ℝ => χ ((x + t • v) i)) = fun t : ℝ => χ (x i + t • (v i)) := by
    funext t
    congr 1
  rw [hpath]
  have hdiffχ : DifferentiableAt ℝ χ (x i) := (hχ.differentiable (by norm_num)) (x i)
  exact (ims_fderiv_eq_lineDeriv (g := χ) (x := x i) (v := v i) hdiffχ).symm

/-- The derivative of the localised state `y ↦ χ (y i) · f y` along the
coordinate direction `kcDir N i k` (product rule + slice chain rule). -/
lemma slice_deriv_cutoff {N : ℕ} (i : Fin N) (k : Fin 3) {χ : ℝ³ → ℝ}
    (hχ : ContDiff ℝ 1 χ) {f : X N → ℝ} (hf : ContDiff ℝ 1 f) (x : X N) :
    fderiv ℝ (fun y : X N => χ (y i) * f y) x (kcDir N i k) =
      χ (x i) * fderiv ℝ f x (kcDir N i k) + fderiv ℝ χ (x i) (kcStdBasis k) * f x := by
  let g : X N → ℝ := fun y => χ (y i)
  have hg : DifferentiableAt ℝ g x := by
    have hc : ContDiff ℝ 1 g := by
      dsimp [g]
      have hpi : ContDiff ℝ 1 (fun y : X N => y i) := by
        simpa using (contDiff_apply ℝ (EuclideanSpace ℝ (Fin 3)) (n := 1) (ι := Fin N) i)
      exact hχ.comp hpi
    exact hc.differentiable (by norm_num) x
  have hf' : DifferentiableAt ℝ f x := (hf.differentiable (by norm_num)) x
  calc
    fderiv ℝ (fun y : X N => χ (y i) * f y) x (kcDir N i k)
        = fderiv ℝ (g * f) x (kcDir N i k) := by
          dsimp [g]
          rfl
    _ = (g x • fderiv ℝ f x + f x • fderiv ℝ g x) (kcDir N i k) := by
          rw [fderiv_mul hg hf']
    _ = g x * fderiv ℝ f x (kcDir N i k) + f x * fderiv ℝ g x (kcDir N i k) := by
          simp
    _ = χ (x i) * fderiv ℝ f x (kcDir N i k) + fderiv ℝ χ (x i) (kcStdBasis k) * f x := by
          dsimp [g]
          rw [coord_fderiv i hχ x (kcDir N i k), ims_kcDir_apply_eq]
          ring

/-- Differentiating the partition of unity `Σⱼ (χⱼ x)² = 1` kills the cross
terms: `Σⱼ χⱼ(x)·∂_k χⱼ(x) = 0` for every basis direction `k`. -/
lemma pu_sum_fderiv_zero {ι : Type*} [Fintype ι] {χ : ι → ℝ³ → ℝ}
    (hχ : ∀ j : ι, ContDiff ℝ 1 (χ j)) (x : ℝ³) (k : Fin 3)
    (hpu : ∀ y : ℝ³, ∑ j : ι, (χ j y) ^ 2 = 1) :
    ∑ j : ι, (χ j x) * (fderiv ℝ (χ j) x (kcStdBasis k)) = 0 := by
  let w : ℝ³ := kcStdBasis k
  have hdiff : ∀ j : ι, DifferentiableAt ℝ (χ j) x := fun j =>
    (hχ j).differentiable (by norm_num) x
  have hdiff_sq : ∀ j : ι, DifferentiableAt ℝ (fun y : ℝ³ => (χ j y) ^ 2) x := fun j =>
    (hdiff j).pow 2
  have hpow_j : ∀ j : ι, fderiv ℝ (fun y : ℝ³ => (χ j y) ^ 2) x w =
      2 * (χ j x) * (fderiv ℝ (χ j) x w) := by
    intro j
    have hEq : (fun y : ℝ³ => (χ j y) ^ 2) = fun y : ℝ³ => (χ j y) * (χ j y) := by
      funext y
      rw [pow_two]
    calc
      fderiv ℝ (fun y : ℝ³ => (χ j y) ^ 2) x w
          = fderiv ℝ (fun y : ℝ³ => (χ j y) * (χ j y)) x w := by
            rw [hEq]
      _ = (χ j x • fderiv ℝ (χ j) x + χ j x • fderiv ℝ (χ j) x) w := by
            change (fderiv ℝ (χ j * χ j) x) w =
              (χ j x • fderiv ℝ (χ j) x + χ j x • fderiv ℝ (χ j) x) w
            rw [fderiv_mul (hdiff j) (hdiff j)]
      _ = χ j x * (fderiv ℝ (χ j) x w) + χ j x * (fderiv ℝ (χ j) x w) := by simp
      _ = 2 * (χ j x) * (fderiv ℝ (χ j) x w) := by ring
  let φ : ℝ³ → ℝ := fun y => ∑ j : ι, (χ j y) ^ 2
  have hφ : φ = fun _ : ℝ³ => 1 := by
    funext y
    dsimp [φ]
    exact hpu y
  have h0 : fderiv ℝ φ x w = 0 := by
    rw [hφ]
    simp
  have hfdsum : fderiv ℝ φ x = ∑ j : ι, fderiv ℝ (fun y : ℝ³ => (χ j y) ^ 2) x := by
    dsimp [φ]
    rw [fderiv_fun_sum (u := Finset.univ) (A := fun j : ι => fun y : ℝ³ => (χ j y) ^ 2)
      (by intro j hj; exact hdiff_sq j)]
  have happ : fderiv ℝ φ x w = (∑ j : ι, fderiv ℝ (fun y : ℝ³ => (χ j y) ^ 2) x) w := by
    rw [hfdsum]
  have htot : (∑ j : ι, fderiv ℝ (fun y : ℝ³ => (χ j y) ^ 2) x w) = 0 := by
    calc
      (∑ j : ι, fderiv ℝ (fun y : ℝ³ => (χ j y) ^ 2) x w)
          = (∑ j : ι, fderiv ℝ (fun y : ℝ³ => (χ j y) ^ 2) x) w := by
            rw [← sum_apply]
      _ = fderiv ℝ φ x w := happ.symm
      _ = 0 := h0
  have hrew : (∑ j : ι, fderiv ℝ (fun y : ℝ³ => (χ j y) ^ 2) x w) =
      ∑ j : ι, 2 * (χ j x) * (fderiv ℝ (χ j) x w) := by
    refine Finset.sum_congr rfl (fun j hj => hpow_j j)
  have htot2 : (∑ j : ι, 2 * (χ j x) * (fderiv ℝ (χ j) x w)) = 0 := by
    rw [← hrew]
    exact htot
  have hfac : (∑ j : ι, 2 * (χ j x) * (fderiv ℝ (χ j) x w)) =
      2 * (∑ j : ι, (χ j x) * (fderiv ℝ (χ j) x w)) := by
    calc
      (∑ j : ι, 2 * (χ j x) * (fderiv ℝ (χ j) x w))
          = ∑ j : ι, 2 * ((χ j x) * (fderiv ℝ (χ j) x w)) := by
            refine Finset.sum_congr rfl (fun j hj => by ring)
      _ = 2 * (∑ j : ι, (χ j x) * (fderiv ℝ (χ j) x w)) := by
            rw [← Finset.mul_sum]
  have h2 : 2 * (∑ j : ι, (χ j x) * (fderiv ℝ (χ j) x w)) = 0 := by
    rw [← hfac]
    exact htot2
  have hT : (∑ j : ι, (χ j x) * (fderiv ℝ (χ j) x w)) = 0 := by
    nlinarith
  simpa [w] using hT

/-- The pointwise many-body IMS identity for particle `i`: with cutoffs
`χⱼ` on the coordinate of particle `i` and `Σⱼ (χⱼ x)² = 1`,
    Σⱼ Σₖ (∂_{ik}(χⱼ(x_i)·f))² = Σₖ (∂_{ik}f)² + f² · Σⱼ Σₖ (∂ₖχⱼ(x_i))². -/
lemma ims_pointwise_manybody {N : ℕ} {ι : Type*} [Fintype ι] (i : Fin N)
    {f : X N → ℝ} (hf : ContDiff ℝ 1 f) {x : X N}
    (χ : ι → ℝ³ → ℝ) (hχ : ∀ j : ι, ContDiff ℝ 1 (χ j))
    (hpu : ∀ y : ℝ³, ∑ j : ι, (χ j y) ^ 2 = 1) :
    (∑ j : ι, ∑ k : Fin 3,
        (fderiv ℝ (fun y : X N => χ j (y i) * f y) x (kcDir N i k)) ^ 2) =
      (∑ k : Fin 3, (fderiv ℝ f x (kcDir N i k)) ^ 2) +
        ((f x) ^ 2) * (∑ j : ι, ∑ k : Fin 3,
          (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2) := by
  have ht : ∀ (j : ι) (k : Fin 3),
      fderiv ℝ (fun y : X N => χ j (y i) * f y) x (kcDir N i k) =
        χ j (x i) * fderiv ℝ f x (kcDir N i k) +
          fderiv ℝ (χ j) (x i) (kcStdBasis k) * f x := by
    intro j k
    exact slice_deriv_cutoff i k (hχ j) hf x
  calc
    (∑ j : ι, ∑ k : Fin 3,
        (fderiv ℝ (fun y : X N => χ j (y i) * f y) x (kcDir N i k)) ^ 2)
        = ∑ j : ι, ∑ k : Fin 3,
            (χ j (x i) * fderiv ℝ f x (kcDir N i k) +
              fderiv ℝ (χ j) (x i) (kcStdBasis k) * f x)^2 := by
          refine Finset.sum_congr rfl (fun j hj => ?_)
          refine Finset.sum_congr rfl (fun k hk => ?_)
          rw [ht j k]
    _ = (∑ k : Fin 3, (fderiv ℝ f x (kcDir N i k)) ^ 2) +
          ((f x) ^ 2) * (∑ j : ι, ∑ k : Fin 3,
            (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2) := by
          exact ims_sq_sum_identity (a := fun j : ι => χ j (x i))
            (b := fun j : ι => fun k : Fin 3 => fderiv ℝ (χ j) (x i) (kcStdBasis k))
            (c := fun k : Fin 3 => fderiv ℝ f x (kcDir N i k))
            (m := f x)
            (by
              exact hpu (x i))
            (by
              intro k
              exact pu_sum_fderiv_zero hχ (x i) k hpu)

/-- The integrated many-body IMS identity over the box: the total kinetic
energy of the pieces `χⱼ(x_i)·f` equals the kinetic energy of `f` plus the
explicit localization error `∫ f²·ΣⱼΣₖ(∂ₖχⱼ(x_i))²`. -/
lemma ims_manybody_identity {N : ℕ} {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L)
    (i : Fin N) {f : X N → ℝ} (hf : ContDiff ℝ ∞ f)
    (χ : ι → ℝ³ → ℝ) (hχ : ∀ j : ι, ContDiff ℝ ∞ (χ j))
    (hpu : ∀ y : ℝ³, ∑ j : ι, (χ j y) ^ 2 = 1) :
    (∑ j : ι, ∑ k : Fin 3, ∫ x in box N L,
        (fderiv ℝ (fun y : X N => χ j (y i) * f y) x (kcDir N i k)) ^ 2) =
      (∑ k : Fin 3, ∫ x in box N L, (fderiv ℝ f x (kcDir N i k)) ^ 2) +
        (∑ j : ι, ∫ x in box N L, ((f x) ^ 2) *
          ∑ k : Fin 3, (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2) := by
  let T : ι → Fin 3 → X N → ℝ := fun j k x =>
    (fderiv ℝ (fun y : X N => χ j (y i) * f y) x (kcDir N i k)) ^ 2
  let A : Fin 3 → X N → ℝ := fun k x => (fderiv ℝ f x (kcDir N i k)) ^ 2
  let C : ι → X N → ℝ := fun j x => ((f x) ^ 2) *
    ∑ k : Fin 3, (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2
  have hf1 : ContDiff ℝ 1 f := hf.of_le (by norm_num)
  have hχ1 : ∀ j : ι, ContDiff ℝ 1 (χ j) := fun j => (hχ j).of_le (by norm_num)
  have hgjm : ∀ j : ι, ContDiff ℝ ∞ (fun y : X N => χ j (y i) * f y) := by
    intro j
    have hc : ContDiff ℝ ∞ (fun y : X N => χ j (y i)) := by
      have hpi : ContDiff ℝ ∞ (fun y : X N => y i) := by
        simpa using (contDiff_apply ℝ (EuclideanSpace ℝ (Fin 3)) (n := ∞) (ι := Fin N) i)
      simpa [Function.comp_def] using (hχ j).comp hpi
    exact hc.mul hf
  have hTcont : ∀ j k, Continuous (T j k) := by
    intro j k
    dsimp [T]
    exact (firstDir_contDiff (hgjm j) (kcDir N i k)).continuous.pow 2
  have hAcont : ∀ k, Continuous (A k) := by
    intro k
    dsimp [A]
    exact (firstDir_contDiff hf (kcDir N i k)).continuous.pow 2
  have hBz : ∀ j k, Continuous (fun x : X N => fderiv ℝ (χ j) (x i) (kcStdBasis k)) := by
    intro j k
    have hfdj : ContDiff ℝ ∞ (fderiv ℝ (χ j)) := ContDiff.fderiv_right (m := ∞) (hχ j) (by simp)
    have heval : ContDiff ℝ ∞ (fun (L : ℝ³ →L[ℝ] ℝ) => L (kcStdBasis k)) := by
      exact ((ContinuousLinearMap.apply (𝕜 := ℝ) (Fₗ := ℝ) (kcStdBasis k) : (ℝ³ →L[ℝ] ℝ) →L[ℝ] ℝ).contDiff)
    have hz : ContDiff ℝ ∞ (fun z : ℝ³ => fderiv ℝ (χ j) z (kcStdBasis k)) := by
      simpa [Function.comp_def] using heval.comp hfdj
    have hpi : Continuous (fun x : X N => x i) := continuous_apply i
    exact (hz.continuous.comp hpi)
  have hBcont : ∀ j k, Continuous (fun x : X N => (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2) := by
    intro j k
    exact (hBz j k).pow 2
  have hCcont : ∀ j, Continuous (C j) := by
    intro j
    dsimp [C]
    refine (hf.continuous.pow 2).mul ?_
    refine continuous_finsetSum (s := Finset.univ) (f := fun (k : Fin 3) (x : X N) =>
      (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2) ?_
    intro k hk
    exact hBcont j k
  have hI_T : ∀ j k, IntegrableOn (T j k) (box N L) volume := fun j k =>
    ims_box_cont_integrableOn hL (hTcont j k)
  have hI_A : ∀ k, IntegrableOn (A k) (box N L) volume := fun k =>
    ims_box_cont_integrableOn hL (hAcont k)
  have hI_C : ∀ j, IntegrableOn (C j) (box N L) volume := fun j =>
    ims_box_cont_integrableOn hL (hCcont j)
  have hI_A_sum : IntegrableOn (fun x : X N => ∑ k : Fin 3, A k x) (box N L) volume := by
    refine ims_box_cont_integrableOn hL ?_
    refine continuous_finsetSum (s := Finset.univ) (f := fun (k : Fin 3) (x : X N) => A k x) ?_
    intro k hk
    exact hAcont k
  have hI_C_sum : IntegrableOn (fun x : X N => ∑ j : ι, C j x) (box N L) volume := by
    refine ims_box_cont_integrableOn hL ?_
    refine continuous_finsetSum (s := Finset.univ) (f := fun (j : ι) (x : X N) => C j x) ?_
    intro j hj
    exact hCcont j
  have hI_Tj : ∀ j : ι, IntegrableOn (fun x : X N => ∑ k : Fin 3, T j k x) (box N L) volume := by
    intro j
    refine ims_box_cont_integrableOn hL ?_
    refine continuous_finsetSum (s := Finset.univ) (f := fun (k : Fin 3) (x : X N) => T j k x) ?_
    intro k hk
    exact hTcont j k
  have hpt : (fun x : X N => ∑ j : ι, ∑ k : Fin 3, T j k x) =
      fun x : X N => (∑ k : Fin 3, A k x) + (∑ j : ι, C j x) := by
    funext x
    calc
      (∑ j : ι, ∑ k : Fin 3, T j k x)
          = (∑ k : Fin 3, A k x) + ((f x) ^ 2) * (∑ j : ι, ∑ k : Fin 3,
              (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2) := by
            dsimp [T, A]
            exact ims_pointwise_manybody i hf1 (x := x) χ hχ1 hpu
      _ = (∑ k : Fin 3, A k x) + (∑ j : ι, C j x) := by
            dsimp [C]
            rw [Finset.mul_sum]
  have hLHS : (∑ j : ι, ∑ k : Fin 3, ∫ x in box N L, T j k x) =
      ∫ x in box N L, (∑ j : ι, ∑ k : Fin 3, T j k x) := by
    calc
      (∑ j : ι, ∑ k : Fin 3, ∫ x in box N L, T j k x)
          = ∑ j : ι, ∫ x in box N L, (∑ k : Fin 3, T j k x) := by
            refine Finset.sum_congr rfl (fun j hj => ?_)
            rw [integral_finsetSum (s := Finset.univ) (μ := volume.restrict (box N L))
              (f := fun k : Fin 3 => T j k) (fun k hk => hI_T j k)]
      _ = ∫ x in box N L, (∑ j : ι, ∑ k : Fin 3, T j k x) := by
            rw [integral_finsetSum (s := Finset.univ) (μ := volume.restrict (box N L))
              (f := fun j : ι => fun x : X N => ∑ k : Fin 3, T j k x) (fun j hj => hI_Tj j)]
  have hRHS : (∑ k : Fin 3, ∫ x in box N L, A k x) + (∑ j : ι, ∫ x in box N L, C j x) =
      ∫ x in box N L, (∑ k : Fin 3, A k x) + (∑ j : ι, C j x) := by
    calc
      (∑ k : Fin 3, ∫ x in box N L, A k x) + (∑ j : ι, ∫ x in box N L, C j x)
          = (∫ x in box N L, ∑ k : Fin 3, A k x) + (∫ x in box N L, ∑ j : ι, C j x) := by
            congr 1
            · rw [integral_finsetSum (s := Finset.univ) (μ := volume.restrict (box N L))
                (f := fun k : Fin 3 => A k) (fun k hk => hI_A k)]
            · rw [integral_finsetSum (s := Finset.univ) (μ := volume.restrict (box N L))
                (f := fun j : ι => C j) (fun j hj => hI_C j)]
      _ = ∫ x in box N L, (∑ k : Fin 3, A k x) + (∑ j : ι, C j x) := by
            rw [← integral_add (μ := volume.restrict (box N L)) hI_A_sum hI_C_sum]
  change (∑ j : ι, ∑ k : Fin 3, ∫ x in box N L, T j k x) =
      (∑ k : Fin 3, ∫ x in box N L, A k x) + (∑ j : ι, ∫ x in box N L, C j x)
  calc
    (∑ j : ι, ∑ k : Fin 3, ∫ x in box N L, T j k x)
        = ∫ x in box N L, (∑ j : ι, ∑ k : Fin 3, T j k x) := hLHS
    _ = ∫ x in box N L, (∑ k : Fin 3, A k x) + (∑ j : ι, C j x) := by
          rw [hpt]
    _ = (∑ k : Fin 3, ∫ x in box N L, A k x) + (∑ j : ι, ∫ x in box N L, C j x) := hRHS.symm

/-- Splitting never lowers the total kinetic energy of particle `i`:
`Σⱼ Σₖ ∫(∂_{ik}(χⱼ(x_i)·f))² ≥ Σₖ ∫(∂_{ik}f)²`. -/
lemma ims_pieces_ge_whole {N : ℕ} {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L)
    (i : Fin N) {f : X N → ℝ} (hf : ContDiff ℝ ∞ f)
    (χ : ι → ℝ³ → ℝ) (hχ : ∀ j : ι, ContDiff ℝ ∞ (χ j))
    (hpu : ∀ y : ℝ³, ∑ j : ι, (χ j y) ^ 2 = 1) :
    (∑ k : Fin 3, ∫ x in box N L, (fderiv ℝ f x (kcDir N i k)) ^ 2) ≤
      ∑ j : ι, ∑ k : Fin 3, ∫ x in box N L,
        (fderiv ℝ (fun y : X N => χ j (y i) * f y) x (kcDir N i k)) ^ 2 := by
  have hmain := ims_manybody_identity hL i hf χ hχ hpu
  let err : ℝ := ∑ j : ι, ∫ x in box N L, ((f x) ^ 2) *
      ∑ k : Fin 3, (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2
  have herr_nonneg : 0 ≤ err := by
    dsimp [err]
    apply Finset.sum_nonneg
    intro j hj
    apply integral_nonneg
    intro x
    exact mul_nonneg (sq_nonneg (f x))
      (Finset.sum_nonneg (fun k hk => sq_nonneg _))
  nlinarith

/-- The explicit-error direction: the split kinetic energy exceeds the whole
one by at most `C·∫f²` when `C` bounds the error density
`ΣⱼΣₖ(∂ₖχⱼ(x_i))²` pointwise on the box. -/
lemma ims_pieces_le_whole_err {N : ℕ} {ι : Type*} [Fintype ι] {L : ℝ} (hL : 0 < L)
    (i : Fin N) {f : X N → ℝ} (hf : ContDiff ℝ ∞ f)
    (χ : ι → ℝ³ → ℝ) (hχ : ∀ j : ι, ContDiff ℝ ∞ (χ j))
    (hpu : ∀ y : ℝ³, ∑ j : ι, (χ j y) ^ 2 = 1)
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x : X N, x ∈ box N L →
      (∑ j : ι, ∑ k : Fin 3, (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2) ≤ C) :
    (∑ j : ι, ∑ k : Fin 3, ∫ x in box N L,
        (fderiv ℝ (fun y : X N => χ j (y i) * f y) x (kcDir N i k)) ^ 2) ≤
      (∑ k : Fin 3, ∫ x in box N L, (fderiv ℝ f x (kcDir N i k)) ^ 2) +
        C * (∫ x in box N L, ((f x) ^ 2)) := by
  have hmain := ims_manybody_identity hL i hf χ hχ hpu
  let g : ι → X N → ℝ := fun j x => ((f x) ^ 2) *
      ∑ k : Fin 3, (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2
  let E : X N → ℝ := fun x => ∑ j : ι, g j x
  let F : X N → ℝ := fun x => C * ((f x) ^ 2)
  have hE_eq : E = fun x : X N => ((f x) ^ 2) *
      (∑ j : ι, ∑ k : Fin 3, (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2) := by
    funext x
    dsimp [E, g]
    rw [← Finset.mul_sum]
  have hgcont : ∀ j : ι, Continuous (g j) := by
    intro j
    dsimp [g]
    refine (hf.continuous.pow 2).mul ?_
    refine continuous_finsetSum (s := Finset.univ)
      (f := fun (k : Fin 3) (x : X N) => (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2) ?_
    intro k hk
    have hfdj : ContDiff ℝ ∞ (fderiv ℝ (χ j)) := ContDiff.fderiv_right (m := ∞) (hχ j) (by simp)
    have heval : ContDiff ℝ ∞ (fun (L : ℝ³ →L[ℝ] ℝ) => L (kcStdBasis k)) := by
      exact ((ContinuousLinearMap.apply (𝕜 := ℝ) (Fₗ := ℝ) (kcStdBasis k) : (ℝ³ →L[ℝ] ℝ) →L[ℝ] ℝ).contDiff)
    have hz : ContDiff ℝ ∞ (fun z : ℝ³ => fderiv ℝ (χ j) z (kcStdBasis k)) := by
      simpa [Function.comp_def] using heval.comp hfdj
    have hpi : Continuous (fun x : X N => x i) := continuous_apply i
    exact ((hz.continuous.comp hpi).pow 2)
  have hEcont : Continuous E := by
    dsimp [E]
    refine continuous_finsetSum (s := Finset.univ) (f := fun (j : ι) (x : X N) => g j x) ?_
    intro j hj
    exact hgcont j
  have hFcont : Continuous F := by
    dsimp [F]
    exact continuous_const.mul (hf.continuous.pow 2)
  have hI_E : IntegrableOn E (box N L) volume := ims_box_cont_integrableOn hL hEcont
  have hI_F : IntegrableOn F (box N L) volume := ims_box_cont_integrableOn hL hFcont
  have hI_g : ∀ j, IntegrableOn (g j) (box N L) volume := fun j =>
    ims_box_cont_integrableOn hL (hgcont j)
  have hpt_le : (fun x : X N => ∑ j : ι, g j x) ≤ᵐ[volume.restrict (box N L)]
      fun x : X N => C * ((f x) ^ 2) := by
    refine (ae_restrict_mem (box_measurable N L)).mono ?_
    intro x hx
    calc
      (∑ j : ι, g j x)
          = ∑ j : ι, (f x) ^ 2 * (∑ k : Fin 3, (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2) := by
            dsimp [g]
      _ = (f x) ^ 2 * (∑ j : ι, ∑ k : Fin 3, (fderiv ℝ (χ j) (x i) (kcStdBasis k)) ^ 2) := by
            rw [← Finset.mul_sum]
      _ ≤ (f x) ^ 2 * C := mul_le_mul_of_nonneg_left (hC x hx) (sq_nonneg (f x))
      _ = C * (f x) ^ 2 := by ring
  have herr : (∑ j : ι, ∫ x in box N L, g j x) ≤ C * (∫ x in box N L, (f x) ^ 2) := by
    calc
      (∑ j : ι, ∫ x in box N L, g j x)
          = ∫ x in box N L, (∑ j : ι, g j x) := by
            rw [integral_finsetSum (s := Finset.univ) (μ := volume.restrict (box N L))
              (f := fun j : ι => g j) (fun j hj => hI_g j)]
      _ ≤ ∫ x in box N L, C * ((f x) ^ 2) := by
            refine MeasureTheory.integral_mono_ae (μ := volume.restrict (box N L))
              (f := fun x : X N => ∑ j : ι, g j x)
              (g := fun x : X N => C * ((f x) ^ 2)) ?_ ?_ ?_
            · exact hI_E
            · exact hI_F
            · exact hpt_le
      _ = C * (∫ x in box N L, (f x) ^ 2) := by
            rw [MeasureTheory.integral_const_mul C (fun x : X N => (f x) ^ 2)]
  have hC0' : 0 ≤ C := hC0
  nlinarith [hmain, herr, hC0']

end BoseGases

end Submission
