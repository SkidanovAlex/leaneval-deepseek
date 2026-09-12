import Submission.ModelArc
import Submission.ExpTwoPoint
import Submission.ExpLocalDiffeo
import Submission.ExpFieldLip
import Mathlib

/-!
# Child task: uniform model normal ball (analytic core)

Prove the theorem `Submission.Model.uniform_normal_ball_aux` below (replace the placeholder).
You may add any helper lemmas in this file.  Build with `lake build Submission.ArcNB`.

## Setting
`g : E → Bilin E` is C³ with each `g x` invertible symmetric positive definite
(hypotheses hg/hinv/hsym/hpos).  `Φ : E×E → ℝ → E×E` is a flow of the geodesic field
`odeField g` with the following *uniform per-base* properties over bases `b ∈ ball x₀ ρu`:

  hPerBase : ∀ b ∈ ball x₀ ρu, ∀ z ∈ closedBall (b,0) 1,
       Φ z 0 = z ∧ (∀ t ∈ Icc (-τf) τf, HasDerivAt (Φ z) (odeField g (Φ z t)) t)
       ∧ (∀ t : ℝ, Φ z t ∈ closedBall (b,0) 2)
  hLip :    ∀ t ∈ Icc (-τf) τf, ∀ b ∈ ball x₀ ρu,
       LipschitzOnWith Lf (fun z => Φ z t) (closedBall (b,0) 1)

## Goal
There exist `ρB > 0, δu > 0, τu > 0` with `ρB ≤ ρu`, `δu ≤ τu`, `2 * τu ≤ τf`, such that for
every base `b ∈ ball x₀ ρB` and every velocity `v ∈ ball 0 δu` (with `τu⁻¹ • v` the flow
data), the exponential-ray minimality holds: every C¹ curve `c : [0,1] → E` with
`c 0 = b`, `c 1 = expOf b Φ τu v`, staying inside `ball b δu`, satisfies
`Real.sqrt ((g b) v v) ≤ mgLength g c 0 1`.

## Suggested proof (mirror `Submission.Model.model_normal_ball`)
For each base `b ∈ ball x₀ ρB` (all radii global, chosen once):
1. Field bounds: `field_fderiv_bound g hg hinv (x₀,0) (ρu + 2) (by positivity)` gives
   `K0 ≥ 0` with `‖fderiv (odeField g) p‖ ≤ K0` for `p ∈ closedBall (x₀,0) (ρu+2)`; use
   `closedBall (b,0) 2 ⊆ closedBall (x₀,0) (ρu+2)` for `b ∈ ball x₀ ρu` (norm triangle).
2. Uniform C¹ of the flow map in data (copy `flow_map_contDiffOn`, ModelExpC1.lean line 1546,
   with this fixed K0 bound instead of the per-base `field_fderiv_bound`): from the per-base
   clauses and `hLip` derive
   `∃ τc > 0, δc ≤ 1/8` with `∀ b ∈ ball x₀ ρu : ∀ t ∈ Icc (-τc) τc :
      ContDiffOn ℝ 1 (fun z => Φ z t) (ball (b,0) δc) ∧
      ContinuousOn (fun z => fderiv ℝ (fun w => Φ w t) z) (ball (b,0) δc)`.
   (Copy the proof of `flow_map_contDiffOn`: it invokes `flow_fderiv_contOn` and
   `flow_fderiv_ballpoint` (both in ModelExpC1.lean) whose K0/hK inputs you supply from the
   fixed region bound; the formulas for τ/δ only involve Tf, K0 and basis norms of E×E.)
3. Pick `τu ≤ min τc (τf/8)` positive and `exp_b v := expOf b Φ τu v`.
   * `exp_b 0 = b`: `flow_rest_point` at the rest point `(b,0)`.
   * `ContDiffOn ℝ 1 exp_b (ball 0 ρE)` with `ρE := τu * δc / 2`, via
     `exp_contDiffOn_ball` (ModelNormalBall.lean line 254) with the radius-1 clauses of `Φ`
     at base b.
   * `HasFDerivAt exp_b id 0`: `expOf_hasFDerivAt_id` (ModelNormalBall.lean line 528).
   * invertible fderiv on a uniform ball: use the TWO-POINT ESTIMATE below instead of
     `exp_fderiv_invertible_on` (whose radius is per-base only).  For
     `H z := (Φ z τu).1 - z.1 - τu • z.2` show `‖H z₁ - H z₂‖ ≤ (τu/4) * ‖z₁ - z₂‖` for
     `zᵢ` in a fixed neighbourhood of `(x₀,0)`; this is where the ONLY genuinely analytic
     new work is: choose the neighbourhood so small (bounded base-ball ρB and velocity ball)
     that the difference quotient of the flow-map derivative is controlled; then the
     two-point estimate `‖(exp_b u - exp_b v) - (u - v)‖ ≤ κ * ‖u - v‖` (κ < 1) follows with
     `z_u := (b, τu⁻¹ • u)`.  Alternatively prove directly that
     `‖fderiv exp_b v - id‖ ≤ 1/2` on `ball 0 ρi` (uniform) using the continuity of
     `z ↦ fderiv (fun w => Φ w τu) z` on `ball (x₀,0) δc` and the canonical derivative at the
     rest point `(x₀,0)` provided by `Submission.Model.rest_flow_deriv_affine`
     (proved in Submission.ArcModel; import Submission.ArcModel for it, or prove an
     equivalent statement yourself via `flow_fderiv_canonical` from ModelDerivId.lean with the
     affine Jacobian) — then use `clm_invertible_of_near_id`.
4. Diffeomorphism/inverse data with explicit uniform balls: from the two-point estimate
   apply `Submission.ExpLocalDiffeo.exp_local_diffeomorphism_of_estimates`
   (import Submission.ExpLocalDiffeo) giving `U,V` (with `U = ball 0 ρE`,
   `V = exp '' U`, and `ball b ((1-κ)ρE) ⊆ V`) and an inverse `inv` with
   `inv (exp v) = v` for `v ∈ U`, `exp (inv y) = y` for `y ∈ V`.  Also get
   `ContDiffOn ℝ 1 exp U` (already), and for each `y ∈ V` get differentiability of `inv` at `y`
   from the inverse-function theorem per point: `fderiv ℝ exp (inv y)` is invertible
   (near-id), so `ContDiffAt ℝ 1 inv y` (use the pattern of
   `Submission.DiffeoInv.contDiffAt_symm_of_invDerivOpen`? it is private; instead use
   `HasStrictFDerivAt.to_localInverse`/`ContDiffAt.to_localInverse` on `exp` at `inv y` and
   uniqueness of the inverse on `V`).
5. Radial (Gauss) bound at base b: copy the `hFb` proof of `model_normal_ball`
   (Submission/ModelNormalBall.lean, lines ~1010-1100): for `y ∈ V` (use `ball b δu` with
   `δu` small enough that `ball b δu ⊆ V`), `v := inv y`, applying
   `radial_bound_main` (ModelNormalBall.lean line 587) with the fixed K0/τ/δ constants and
   `hvin : (b, τ⁻¹ • v) ∈ ball (b,0) (1/4)` (smallness from `‖v‖ < ρS ≤ τ/8`).  All the
   per-base hypotheses of `radial_bound_main`/`gauss_pair` are exactly the radius-1 flow
   clauses from `hPerBase` + region bound `hK`.
6. Assemble minimality with `Submission.Model.radial_minimality`
   (Submission/MinimalityWrap.lean), exactly as in `model_normal_ball`'s tail: with
   `U := ball 0 ρE`, `V := ball b δu`, `inv`, `hFcont/hFdiff/hFb` from step 5, get the
   staying-curve minimality, then restrict to the stated conclusion (choose
   `δu ≤ (1-κ)*ρE/2` etc.).

The statement is:
-/
open ContinuousLinearMap
open scoped ContDiff Topology BigOperators
open Set Metric Filter
open MeasureTheory intervalIntegral

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 3000000


/-! ## Helper lemmas -/

/-- The geodesic field is Lipschitz on the closed ball of radius `R` around `z₀`, uniformly
over the radius (parameterised version of `field_lipschitzOn`). -/
lemma field_lipschitzOn_r (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (z₀ : E × E) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : NNReal, LipschitzOnWith K (odeField g) (closedBall z₀ R) := by
  let V : (E × E) → (E × E) := odeField g
  have hV1 : ContDiff ℝ 1 V := by
    rw [contDiff_iff_contDiffAt]
    intro p
    rcases p with ⟨x, v⟩
    simpa [V] using odeField_contDiffAt g hg hinv x v
  have hfcont : Continuous (fderiv ℝ V) := hV1.continuous_fderiv (by norm_num : (1 : ℕ∞ω) ≠ 0)
  let S : Set (E × E) := closedBall z₀ R
  have hScomp : IsCompact S := by
    dsimp [S]
    exact isCompact_closedBall z₀ R
  have hSne : S.Nonempty := by
    refine ⟨z₀, ?_⟩
    dsimp [S]
    simpa using hR
  have hnormOn : ContinuousOn (fun x : E × E => ‖fderiv ℝ V x‖) S := hfcont.norm.continuousOn
  rcases hScomp.exists_isMaxOn hSne hnormOn with ⟨xm, hxm, hmax⟩
  let K : NNReal := ⟨‖fderiv ℝ V xm‖, norm_nonneg _⟩
  have hKbnd : ∀ x ∈ S, ‖fderiv ℝ V x‖ ≤ (K : ℝ) := by
    intro x hx
    calc
      ‖fderiv ℝ V x‖ ≤ ‖fderiv ℝ V xm‖ := hmax hx
      _ = (K : ℝ) := rfl
  refine ⟨K, ?_⟩
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro x hx y hy
  have hdiff : ∀ q ∈ S, DifferentiableAt ℝ V q := fun q _ =>
    (hV1.differentiable (by norm_num : (1 : ℕ∞ω) ≠ 0)).differentiableAt
  have hsub := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := V) hdiff hKbnd
    (convex_closedBall z₀ R) hx hy
  have hnorm : ‖V y - V x‖ ≤ (K : ℝ) * ‖y - x‖ := by
    simpa [V, S] using hsub
  simpa [dist_eq_norm, norm_sub_rev] using hnorm

/-- For `b` in the `ρu`-ball around `x₀`, the radius-2 data ball around `(b,0)` is inside the
radius-(ρu+2) ball around `(x₀,0)`. -/
lemma closedBall_b0_subset (x₀ : E) {ρu : ℝ} (hρu : 0 < ρu) {b : E} (hb : b ∈ ball x₀ ρu) :
    closedBall (b, (0 : E)) 2 ⊆ closedBall (x₀, (0 : E)) (ρu + 2) := by
  let z0 : E × E := (x₀, (0 : E))
  let zb : E × E := (b, (0 : E))
  intro p hp
  rw [mem_closedBall, dist_eq_norm] at hp ⊢
  have hb' : ‖b - x₀‖ < ρu := by
    have hd : dist b x₀ < ρu := mem_ball.mp hb
    simpa [dist_eq_norm] using hd
  have h1 : ‖p - z0‖ ≤ ‖p - zb‖ + ‖zb - z0‖ :=
    norm_sub_le_norm_sub_add_norm_sub p zb z0
  have h2 : ‖zb - z0‖ = ‖b - x₀‖ := by
    dsimp [z0, zb]
    simp
  have h3 : ‖p - zb‖ ≤ 2 := by
    dsimp [zb]
    simpa [dist_eq_norm] using hp
  have hb'' : ‖b - x₀‖ ≤ ρu := le_of_lt hb'
  nlinarith


/-- Uniform (in the base point `b`) `C^1`-in-data regularity of the time-`t` slice maps of the
flow: the constants `τ,δ` depend only on the global data (`τf`, `Lf`, `K0`). -/
lemma uniform_flow_c1 (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) (ρu τf : ℝ) (hρu : 0 < ρu) (hτf : 0 < τf)
    (Lf : NNReal) (Φ : E × E → ℝ → E × E)
    (hPerBase : ∀ b ∈ ball x₀ ρu, ∀ z ∈ closedBall (b, 0) 1, Φ z 0 = z ∧
       (∀ t ∈ Icc (-τf) τf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
       (∀ t : ℝ, Φ z t ∈ closedBall (b, 0) 2))
    (hLip : ∀ t ∈ Icc (-τf) τf, ∀ b ∈ ball x₀ ρu,
       LipschitzOnWith Lf (fun z => Φ z t) (closedBall (b, 0) 1))
    {K0 : ℝ} (hK0 : 0 ≤ K0)
    (hK : ∀ p ∈ closedBall (x₀, 0) (ρu + 2), ‖fderiv ℝ (odeField g) p‖ ≤ K0) :
    ∃ τ > 0, τ ≤ τf / 8 ∧ ∃ δ > 0, δ ≤ 1 / 8 ∧
      ∀ b ∈ ball x₀ ρu, ∀ t ∈ Icc (-τ) τ,
        ContDiffOn ℝ 1 (fun z : E × E => Φ z t) (ball (b, 0) δ) ∧
        ContinuousOn (fun z : E × E => fderiv ℝ (fun w => Φ w t) z) (ball (b, 0) δ) := by
  classical
  let B : ℝ := ∑ i : Fin (Module.finrank ℝ (E × E)), ‖(Module.finBasis ℝ (E × E)) i‖
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg (fun i hi => norm_nonneg _)
  have hBi (i : Fin (Module.finrank ℝ (E × E))) : ‖(Module.finBasis ℝ (E × E)) i‖ ≤ B := by
    dsimp [B]
    exact Finset.single_le_sum (fun j hj => norm_nonneg _) (Finset.mem_univ i)
  let τ : ℝ := min (τf / 8) (1 / (4 * (K0 + 1) * (B + 1)))
  have hτ : 0 < τ := by
    dsimp [τ]
    have hpos : 0 < 4 * (K0 + 1) * (B + 1) := by nlinarith [hB, hK0]
    exact lt_min (by positivity : 0 < τf / 8) (one_div_pos.mpr hpos)
  have hτle : τ ≤ τf / 8 := by
    dsimp [τ]
    exact min_le_left _ _
  have hτTf : 4 * τ ≤ τf := by
    dsimp [τ]
    have hle : min (τf / 8) (1 / (4 * (K0 + 1) * (B + 1))) ≤ τf / 8 := min_le_left _ _
    nlinarith
  have hUb : ∀ i : Fin (Module.finrank ℝ (E × E)),
      4 * (K0 + 1) * (‖(Module.finBasis ℝ (E × E)) i‖ + 1) * τ ≤ 1 := by
    intro i
    have hτle2 : τ ≤ 1 / (4 * (K0 + 1) * (B + 1)) := by
      dsimp [τ]
      exact min_le_right _ _
    have hpos : 0 < 4 * (K0 + 1) * (B + 1) := by nlinarith [hB, hK0]
    have hmain : 4 * (K0 + 1) * (B + 1) * τ ≤ 1 := by
      calc
        4 * (K0 + 1) * (B + 1) * τ ≤ 4 * (K0 + 1) * (B + 1) * (1 / (4 * (K0 + 1) * (B + 1))) := by
          exact mul_le_mul_of_nonneg_left hτle2 (by nlinarith [hB, hK0])
        _ = 1 := by field_simp [hpos.ne']
    have h1 : 4 * (K0 + 1) * (‖(Module.finBasis ℝ (E × E)) i‖ + 1) ≤ 4 * (K0 + 1) * (B + 1) := by
      have hle2 : ‖(Module.finBasis ℝ (E × E)) i‖ + 1 ≤ B + 1 := by linarith [hBi i]
      exact mul_le_mul_of_nonneg_left hle2 (by nlinarith [hK0])
    have hpos2 : 0 ≤ τ := le_of_lt hτ
    calc
      4 * (K0 + 1) * (‖(Module.finBasis ℝ (E × E)) i‖ + 1) * τ ≤ 4 * (K0 + 1) * (B + 1) * τ := by
        exact mul_le_mul_of_nonneg_right h1 hpos2
      _ ≤ 1 := hmain
  let δ : ℝ := 1 / 8
  have hδ0 : 0 < δ := by norm_num
  have hδ14 : δ ≤ 1 / 4 := by norm_num
  have hδ12 : δ ≤ 1 / 2 := by norm_num
  have hδ8 : δ ≤ 1 / 8 := by norm_num
  refine ⟨τ, hτ, hτle, δ, hδ0, hδ8, ?_⟩
  intro b hb t ht
  have hbK (p : E × E) (hp : p ∈ closedBall (b, (0 : E)) 2) :
      ‖fderiv ℝ (odeField g) p‖ ≤ K0 := by
    exact hK p (closedBall_b0_subset x₀ hρu hb hp)
  have hbΦ₀ : ∀ z ∈ closedBall (b, (0 : E)) 1, Φ z 0 = z ∧
       (∀ t : ℝ, t ∈ Icc (-τf) τf → HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
       (∀ t : ℝ, Φ z t ∈ closedBall (b, (0 : E)) 2) := by
    intro z hz
    exact hPerBase b hb z hz
  have hbLip : ∀ t : ℝ, t ∈ Icc (-τf) τf →
       LipschitzOnWith Lf (fun z => Φ z t) (closedBall (b, (0 : E)) 1) := by
    intro s hs
    exact hLip s hs b hb
  have hcontd : ContinuousOn (fun z : E × E => fderiv ℝ (fun w => Φ w t) z) (ball (b, (0 : E)) δ) := by
    exact flow_fderiv_contOn g hg hinv (b, (0 : E)) τf hτf Lf Φ
      (by intro z hz; exact hbΦ₀ z hz) (by intro s hs; exact hbLip s hs)
      hK0 (by intro p hp; exact hbK p hp) (τ := τ) hτ hτTf (δ := δ) hδ0 hδ14 hUb t ht
  have hU2pos : 0 < 2 * τ := by positivity
  have hU2Tf : 2 * τ ≤ τf / 2 := by nlinarith [hτTf, hτf]
  have hUb2 : ∀ i : Fin (Module.finrank ℝ (E × E)),
      2 * (K0 + 1) * (‖(Module.finBasis ℝ (E × E)) i‖ + 1) * (2 * τ) ≤ 1 := by
    intro i
    have h := hUb i
    convert h using 1
    ring
  have hbp := flow_fderiv_ballpoint g hg hinv (b, (0 : E)) τf hτf Lf Φ
      (by intro z hz; exact hbΦ₀ z hz) (by intro s hs; exact hbLip s hs) hK0
      (by intro p hp; exact hbK p hp) (δ := δ) hδ0 hδ12 (U := 2 * τ) hU2pos hU2Tf hUb2
  let f : E × E → E × E := fun z => Φ z t
  have ht2 : t ∈ Icc (-(2 * τ / 2)) (2 * τ / 2) := by
    constructor <;> nlinarith [ht.1, ht.2]
  have hDiff : DifferentiableOn ℝ f (ball (b, (0 : E)) δ) := by
    intro x hx
    rcases hbp x hx t ht2 with ⟨J, hJ0, hJd, hJadd, hJsmul, L, hLfd, hLval⟩
    exact (hLfd.differentiableAt).differentiableWithinAt
  have hContW : ContinuousOn (fun y => fderivWithin ℝ f (ball (b, (0 : E)) δ) y)
      (ball (b, (0 : E)) δ) := by
    have hcontD := hcontd
    refine hcontD.congr ?_
    intro y hy
    rcases hbp y hy t ht2 with ⟨J, hJ0, hJd, hJadd, hJsmul, L, hLfd, hLval⟩
    have hdy : DifferentiableAt ℝ f y := hLfd.differentiableAt
    change fderivWithin ℝ f (ball (b, (0 : E)) δ) y = fderiv ℝ (fun w => Φ w t) y
    rw [fderivWithin_eq_fderiv (isOpen_ball.uniqueDiffWithinAt hy) hdy]
  have hfinal : ContDiffOn ℝ 1 (fun z : E × E => Φ z t) (ball (b, (0 : E)) δ) := by
    apply contDiffOn_one_of (g0 := f) (s := ball (b, (0 : E)) δ) hDiff hContW
  exact ⟨by simpa [f] using hfinal, hcontd⟩


/-- Version of `exp_local_diffeomorphism_of_estimates` with *explicit* balls and explicit
covering and inverse laws, as needed for uniform base data. -/
lemma exp_est_local_diffeomorphism_ball (exp : E → E) (b : E) (ρ κ : ℝ)
    (hρ : 0 < ρ) (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hexp0 : exp 0 = b)
    (hest : ∀ ⦃u v : E⦄, u ∈ closedBall (0 : E) ρ → v ∈ closedBall (0 : E) ρ →
      ‖(exp u - exp v) - (u - v)‖ ≤ κ * ‖u - v‖) :
    ∃ inv : E → E,
      (∀ v : E, v ∈ ball (0 : E) ρ → inv (exp v) = v) ∧
      (∀ y : E, y ∈ exp '' ball (0 : E) ρ → inv y ∈ ball (0 : E) ρ ∧ exp (inv y) = y) ∧
      (∀ u v : E, u ∈ ball (0 : E) ρ → v ∈ ball (0 : E) ρ → exp u = exp v → u = v) ∧
      (ball b ((1 - κ) * ρ) ⊆ exp '' ball (0 : E) ρ) := by
  classical
  have hcover : ball b ((1 - κ) * ρ) ⊆ exp '' ball (0 : E) ρ :=
    Submission.ExpLocalDiffeo.exp_ball_subset_image exp b ρ κ hρ hκ0 hκ1 hexp0 hest
  have hinj0 : ∀ u v : E, u ∈ ball (0 : E) ρ → v ∈ ball (0 : E) ρ → exp u = exp v → u = v := by
    intro u v hu hv huv
    have huB : u ∈ closedBall (0 : E) ρ := ball_subset_closedBall hu
    have hvB : v ∈ closedBall (0 : E) ρ := ball_subset_closedBall hv
    have hneg : (exp u - exp v) - (u - v) = -((u : E) - (v : E)) := by
      simp [huv]
    have hk : ‖(u : E) - (v : E)‖ ≤ κ * ‖(u : E) - (v : E)‖ := by
      calc
        ‖(u : E) - (v : E)‖ = ‖-((u : E) - (v : E))‖ := by rw [norm_neg]
        _ = ‖(exp u - exp v) - (u - v)‖ := by rw [hneg]
        _ ≤ κ * ‖(u : E) - (v : E)‖ := hest huB hvB
    have hnorm0 : ‖(u : E) - (v : E)‖ = 0 := by
      have hle : (1 - κ) * ‖(u : E) - (v : E)‖ ≤ 0 := by nlinarith [hk]
      nlinarith [hle, hκ1, norm_nonneg ((u : E) - (v : E))]
    exact sub_eq_zero.mp (norm_eq_zero.mp hnorm0)
  let inv : E → E := fun y => if h : y ∈ exp '' ball (0 : E) ρ then Classical.choose h else 0
  have hinv1 : ∀ y : E, y ∈ exp '' ball (0 : E) ρ → inv y ∈ ball (0 : E) ρ ∧ exp (inv y) = y := by
    intro y hy
    have hc := Classical.choose_spec hy
    constructor
    · dsimp [inv]
      rw [dif_pos hy]
      exact hc.1
    · dsimp [inv]
      rw [dif_pos hy]
      exact hc.2
  have hinv2 : ∀ v : E, v ∈ ball (0 : E) ρ → inv (exp v) = v := by
    intro v hv
    have hmem : exp v ∈ exp '' ball (0 : E) ρ := by exact ⟨v, hv, rfl⟩
    have hc := Classical.choose_spec hmem
    have hval : (Classical.choose hmem : E) = v := by
      exact hinj0 (Classical.choose hmem) v hc.1 hv (hc.2)
    dsimp [inv]
    rw [dif_pos hmem]
    exact hval
  exact ⟨inv, hinv2, hinv1, hinj0, hcover⟩


/-- The inverse `inv` of a `C¹` map `exp` with invertible derivatives on `ball 0 ρE`, which is a
two-sided inverse on `ball 0 ρE` / its image, is `C¹` at any point of the image. -/
lemma contDiffAt_inv_of_twoPoint (exp : E → E) {ρE : ℝ} (hρE : 0 < ρE)
    (hC : ContDiffOn ℝ 1 exp (ball (0 : E) ρE))
    (hInvD : ∀ v ∈ ball (0 : E) ρE, ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ exp v)
    {inv : E → E}
    (hInv2 : ∀ v : E, v ∈ ball (0 : E) ρE → inv (exp v) = v)
    (hInv1 : ∀ y : E, y ∈ exp '' ball (0 : E) ρE → inv y ∈ ball (0 : E) ρE ∧ exp (inv y) = y)
    {y : E} (hy : y ∈ exp '' ball (0 : E) ρE) :
    ContDiffAt ℝ 1 inv y := by
  rcases hInv1 y hy with ⟨hvy, hyeq⟩
  have hcv : ContDiffAt ℝ 1 exp (inv y) := hC.contDiffAt (isOpen_ball.mem_nhds hvy)
  rcases hInvD (inv y) hvy with ⟨e, he⟩
  have hfd : HasFDerivAt exp (fderiv ℝ exp (inv y)) (inv y) :=
    (hcv.differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)).hasFDerivAt
  have hfv : HasFDerivAt exp ((e : E →L[ℝ] E)) (inv y) := by simpa [he] using hfd
  have hstrict : HasStrictFDerivAt exp ((e : E →L[ℝ] E)) (inv y) :=
    hcv.hasStrictFDerivAt' hfv (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hp_left : ∀ᶠ x in 𝓝 (inv y), inv (exp x) = x := by
    filter_upwards [isOpen_ball.mem_nhds hvy] with x hx
    exact hInv2 x hx
  have huniq : ∀ᶠ z in 𝓝 (exp (inv y)),
      inv z = HasStrictFDerivAt.localInverse exp e (inv y) hstrict z :=
    HasStrictFDerivAt.localInverse_unique hstrict hp_left
  have hlinv : ContDiffAt ℝ 1 (HasStrictFDerivAt.localInverse exp e (inv y) hstrict)
      (exp (inv y)) :=
    ContDiffAt.to_localInverse hcv hfv (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hlinv' : ContDiffAt ℝ 1 (HasStrictFDerivAt.localInverse exp e (inv y) hstrict) y := by
    simpa [hyeq] using hlinv
  have hconv : ∀ᶠ z in 𝓝 y, inv z = HasStrictFDerivAt.localInverse exp e (inv y) hstrict z := by
    simpa [hyeq] using huniq
  exact hlinv'.congr_of_eventuallyEq hconv

theorem uniform_normal_ball_aux (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (hpos : ∀ x u : E, u ≠ 0 → 0 < (g x) u u)
    (x₀ : E) (ρu τf : ℝ) (hρu : 0 < ρu) (hτf : 0 < τf)
    (Lf : NNReal) (Φ : E × E → ℝ → E × E)
    (hPerBase : ∀ b ∈ ball x₀ ρu, ∀ z ∈ closedBall (b, 0) 1, Φ z 0 = z ∧
       (∀ t ∈ Icc (-τf) τf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
       (∀ t : ℝ, Φ z t ∈ closedBall (b, 0) 2))
    (hLip : ∀ t ∈ Icc (-τf) τf, ∀ b ∈ ball x₀ ρu,
       LipschitzOnWith Lf (fun z => Φ z t) (closedBall (b, 0) 1)) :
    ∃ ρB δu τu : ℝ, 0 < ρB ∧ 0 < δu ∧ 0 < τu ∧ ρB ≤ ρu ∧ δu ≤ τu ∧ 2 * τu ≤ τf ∧
      ∀ b ∈ ball x₀ ρB,
        ∀ v ∈ ball (0 : E) δu,
          (∀ c : ℝ → E, c 0 = b → c 1 = expOf b Φ τu v →
            (∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 c O) →
            (∀ s ∈ Icc (0 : ℝ) 1, c s ∈ ball b δu) →
            Real.sqrt ((g b) v v) ≤ mgLength g c 0 1) := by
  classical
  -- ------------ global constants (uniform over all bases) ------------
  rcases field_fderiv_bound g hg hinv (x₀, (0 : E)) (ρu + 2) (by linarith) with ⟨K0, hK0, hKbig⟩
  have hKbig' : ∀ p ∈ closedBall (x₀, (0 : E)) (ρu + 2), ‖fderiv ℝ (odeField g) p‖ ≤ K0 := hKbig
  rcases field_lipschitzOn_r g hg hinv (x₀, (0 : E)) (ρu + 2) (by linarith) with ⟨Kf, hKfBig⟩
  rcases uniform_flow_c1 g hg hinv x₀ ρu τf hρu hτf Lf Φ hPerBase hLip hK0 hKbig' with
    ⟨τc, hτc0, hτcτf8, δc, hδc0, hδc8, hcd⟩
  let S : ℝ := Finset.univ.sum (fun i : Fin (Module.finrank ℝ (E × E)) =>
    (‖Module.finBasis ℝ (E × E) i‖ + 1))
  have hS0 : 0 ≤ S := Finset.sum_nonneg (by intro i hi; positivity)
  let M : ℝ := S + 1
  have hMpos : 0 < M := by dsimp [M]; linarith
  have hK0p : 0 < K0 + 1 := by linarith
  have hKf0 : 0 ≤ (Kf : ℝ) := by exact_mod_cast (Kf : NNReal).2
  have hLf0 : 0 ≤ (Lf : ℝ) := by exact_mod_cast (Lf : NNReal).2
  have hKf1 : 0 < (Kf : ℝ) + 1 := by linarith
  have hLf1 : 0 < (Lf : ℝ) + 1 := by linarith
  let τu : ℝ := min τc (min (τf / 8) (min (1 / (8 * (K0 + 1) * M))
    (1 / (4 * ((Kf : ℝ) + 1) * ((Lf : ℝ) + 1)))))
  have hτu0 : 0 < τu := by
    dsimp [τu]
    positivity
  have hτuτc : τu ≤ τc := by
    dsimp [τu]
    exact min_le_left _ _
  have hτuτf8 : τu ≤ τf / 8 := by
    dsimp [τu]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hτuDen1 : τu ≤ 1 / (8 * (K0 + 1) * M) := by
    dsimp [τu]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hτuDen2 : τu ≤ 1 / (4 * ((Kf : ℝ) + 1) * ((Lf : ℝ) + 1)) := by
    dsimp [τu]
    exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have h2τuτf : 2 * τu ≤ τf := by nlinarith [hτuτf8]
  have hτuτf : τu < τf := by nlinarith [hτuτf8, hτf]
  have h4τuτf : 4 * τu ≤ τf := by nlinarith [hτuτf8]
  have hBM (i : Fin (Module.finrank ℝ (E × E))) :
      ‖Module.finBasis ℝ (E × E) i‖ + 1 ≤ M := by
    dsimp [M]
    have h1 : ‖Module.finBasis ℝ (E × E) i‖ + 1 ≤ S := by
      dsimp [S]
      refine Finset.single_le_sum (s := Finset.univ)
        (f := fun j : Fin (Module.finrank ℝ (E × E)) => ‖Module.finBasis ℝ (E × E) j‖ + 1) ?_ ?_
      · intro j hj
        positivity
      · simp
    linarith
  have hUb : ∀ i : Fin (Module.finrank ℝ (E × E)),
      4 * (K0 + 1) * (‖(Module.finBasis ℝ (E × E)) i‖ + 1) * τu ≤ 1 := by
    intro i
    have hnonneg : 0 ≤ 4 * (K0 + 1) * M := by positivity
    have hpos2 : 0 ≤ τu := le_of_lt hτu0
    have hBMi : ‖Module.finBasis ℝ (E × E) i‖ + 1 ≤ M := hBM i
    have hm1 : 4 * (K0 + 1) * (‖(Module.finBasis ℝ (E × E)) i‖ + 1) ≤ 4 * (K0 + 1) * M := by
      exact mul_le_mul_of_nonneg_left hBMi (by positivity)
    have hm : 4 * (K0 + 1) * (‖(Module.finBasis ℝ (E × E)) i‖ + 1) * τu
        ≤ 4 * (K0 + 1) * M * τu := by
      exact mul_le_mul_of_nonneg_right hm1 hpos2
    have hm2 : 4 * (K0 + 1) * M * τu ≤ 1 := by
      calc
        4 * (K0 + 1) * M * τu ≤ 4 * (K0 + 1) * M * (1 / (8 * (K0 + 1) * M)) :=
          mul_le_mul_of_nonneg_left hτuDen1 hnonneg
        _ = 1 / 2 := by
          field_simp [hK0p.ne', hMpos.ne']
          ring
        _ ≤ 1 := by norm_num
    exact le_trans hm hm2
  have hκ0 : 0 ≤ (Kf : ℝ) * (Lf : ℝ) * τu := by positivity
  have hκ14 : (Kf : ℝ) * (Lf : ℝ) * τu ≤ 1 / 4 := by
    have hle : (Kf : ℝ) * (Lf : ℝ) ≤ ((Kf : ℝ) + 1) * ((Lf : ℝ) + 1) := by nlinarith
    have hdenpos : 0 < 4 * ((Kf : ℝ) + 1) * ((Lf : ℝ) + 1) := by positivity
    have hpos3 : 0 ≤ (Kf : ℝ) * (Lf : ℝ) := mul_nonneg hKf0 hLf0
    have hc0 : 0 ≤ 1 / (4 * ((Kf : ℝ) + 1) * ((Lf : ℝ) + 1)) := by positivity
    calc
      (Kf : ℝ) * (Lf : ℝ) * τu
          ≤ (Kf : ℝ) * (Lf : ℝ) * (1 / (4 * ((Kf : ℝ) + 1) * ((Lf : ℝ) + 1))) := by
            exact mul_le_mul_of_nonneg_left hτuDen2 hpos3
      _ ≤ ((Kf : ℝ) + 1) * ((Lf : ℝ) + 1) * (1 / (4 * ((Kf : ℝ) + 1) * ((Lf : ℝ) + 1))) := by
            exact mul_le_mul_of_nonneg_right hle hc0
      _ = 1 / 4 := by
            field_simp [hdenpos.ne']
  have hκ1 : (Kf : ℝ) * (Lf : ℝ) * τu < 1 := by nlinarith [hκ14]
  let ρE : ℝ := τu * δc / 2
  have hρE : 0 < ρE := by dsimp [ρE]; positivity
  have hρEτu : ρE ≤ τu := by
    dsimp [ρE]
    have h1 : δc / 2 ≤ 1 := by
      have hδc2 : δc ≤ 2 := by linarith [hδc8]
      nlinarith
    nlinarith [h1, hτu0]
  let ρB : ℝ := ρu
  have hρB : 0 < ρB := by dsimp [ρB]; exact hρu
  have hρBρu : ρB ≤ ρu := le_rfl
  let δu : ℝ := ρE / 4
  have hδu : 0 < δu := by dsimp [δu]; positivity
  have hδuτu : δu ≤ τu := by
    dsimp [δu]
    have h1 : ρE ≤ 4 * τu := by
      dsimp [ρE]
      have hδc8' : δc / 2 ≤ 8 := by nlinarith [hδc8]
      nlinarith [hδc8', hτu0]
    nlinarith
  have hδuρE : δu ≤ ρE := by dsimp [δu]; linarith
  have hδuκρE : δu ≤ (1 - (Kf : ℝ) * (Lf : ℝ) * τu) * ρE := by
    dsimp [δu]
    have h : (3 / 4 : ℝ) * ρE ≤ (1 - (Kf : ℝ) * (Lf : ℝ) * τu) * ρE := by
      have hκ' : (Kf : ℝ) * (Lf : ℝ) * τu ≤ 1 / 4 := hκ14
      nlinarith [hρE]
    have h2 : ρE / 4 ≤ (3 / 4 : ℝ) * ρE := by nlinarith [hρE]
    exact le_trans h2 h
  have hρEτu_le2 : (2 : ℝ) * τu ≤ τf := h2τuτf
  -- ------------- witnesses -------------
  refine ⟨ρB, δu, τu, hρB, hδu, hτu0, hρBρu, hδuτu, h2τuτf, ?_⟩
  intro b hb v hv c hc0 hc1 hcO hcStay
  -- per-base instantiation of the flow hypotheses
  have hPerB : ∀ z ∈ closedBall (b, (0 : E)) 1, Φ z 0 = z ∧
       (∀ t ∈ Icc (-τf) τf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
       (∀ t : ℝ, Φ z t ∈ closedBall (b, (0 : E)) 2) := by
    intro z hz
    exact hPerBase b hb z hz
  have hLipB : ∀ t ∈ Icc (-τf) τf,
       LipschitzOnWith Lf (fun z => Φ z t) (closedBall (b, (0 : E)) 1) := by
    intro t ht
    exact hLip t ht b hb
  have hKb : ∀ p ∈ closedBall (b, (0 : E)) 2, ‖fderiv ℝ (odeField g) p‖ ≤ K0 := by
    intro p hp
    exact hKbig p (closedBall_b0_subset x₀ hρu hb hp)
  have hKfb : LipschitzOnWith Kf (odeField g) (closedBall (b, (0 : E)) 2) := by
    exact hKfBig.mono (closedBall_b0_subset x₀ hρu hb)
  let expb : E → E := expOf b Φ τu
  have hcdb : ∀ t ∈ Icc (-τc) τc, ContDiffOn ℝ 1 (fun z : E × E => Φ z t) (ball (b, (0 : E)) δc) := by
    intro t ht
    exact (hcd b hb t ht).1
  have hExpC1 : ContDiffOn ℝ 1 expb (ball (0 : E) ρE) := by
    dsimp [expb, ρE]
    exact exp_contDiffOn_ball g hg hinv b Φ (τ := τu) (τc := τc) (δc := δc) hcdb hδc0 hτu0 hτuτc
  have hΦ2b : ∀ z ∈ closedBall (b, (0 : E)) 1, Φ z 0 = z ∧
      ∀ t ∈ Icc (-τf) τf, HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
    intro z hz
    exact ⟨(hPerB z hz).1, (hPerB z hz).2.1⟩
  have hExp0 : expb (0 : E) = b := by
    dsimp [expb]
    have hτmem : τu ∈ Ioo (-τf) τf := by
      constructor
      · linarith [hτu0, hτf]
      · exact hτuτf
    have hrest := flow_rest_point g hg hinv hτf (x₀ := b) (Φ := Φ) hΦ2b τu hτmem
    simpa [expOf] using congrArg Prod.fst hrest
  have hExpId : HasFDerivAt expb (ContinuousLinearMap.id ℝ E) (0 : E) := by
    dsimp [expb]
    exact expOf_hasFDerivAt_id g hg hinv b (Tf := τf) hτf Φ hΦ2b (τ := τu) hτu0 hτuτf
      (ρ := ρE) hρE (by simpa [expb] using hExpC1)
  -- two-point expansion bound of `expb` (uniform data of the flow)
  have hΦtu : ∀ z ∈ closedBall (b, (0 : E)) 1, Φ z 0 = z ∧
      ∀ t ∈ Icc (-τu) τu, HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
    intro z hz
    constructor
    · exact (hPerB z hz).1
    · intro t ht
      have ht' : t ∈ Icc (-τf) τf := by
        constructor <;> linarith [ht.1, ht.2, hτuτf]
      exact (hPerB z hz).2.1 t ht'
  have hContb : ∀ z ∈ closedBall (b, (0 : E)) 1, ∀ t ∈ Icc (0 : ℝ) τu,
      Φ z t ∈ closedBall (b, (0 : E)) 2 := by
    intro z hz t ht
    exact (hPerB z hz).2.2 t
  have hLipb : ∀ t ∈ Icc (-τu) τu,
      LipschitzOnWith Lf (fun z => Φ z t) (closedBall (b, (0 : E)) 1) := by
    intro t ht
    have ht' : t ∈ Icc (-τf) τf := by
      constructor <;> linarith [ht.1, ht.2, hτuτf]
    exact hLipB t ht'
  have hexpf (u : E) : expb u = (Φ (b, (1 / τu) • u) τu).1 := by
    have hs : (τu⁻¹ : ℝ) • u = (1 / τu) • u := by rw [inv_eq_one_div]
    dsimp [expb]
    rw [expOf, hs]
  have htp : ∀ u v : E, u ∈ closedBall (0 : E) τu → v ∈ closedBall (0 : E) τu →
      ‖(expb u - expb v) - (u - v)‖ ≤ (Kf : ℝ) * (Lf : ℝ) * τu * ‖u - v‖ := by
    intro u v hu hv
    have hh := exp_two_point_bound g hg hinv b (ρ := τu) hτu0 Lf Kf Φ hΦtu hContb hLipb hKfb u v hu hv
    simpa [hexpf, mul_assoc] using hh
  -- the estimate on the small velocity ball
  have hclE : closedBall (0 : E) ρE ⊆ closedBall (0 : E) τu := closedBall_subset_closedBall hρEτu
  have hest : ∀ ⦃u v : E⦄, u ∈ closedBall (0 : E) ρE → v ∈ closedBall (0 : E) ρE →
      ‖(expb u - expb v) - (u - v)‖ ≤ (Kf : ℝ) * (Lf : ℝ) * τu * ‖u - v‖ := by
    intro u v hu hv
    exact htp u v (hclE hu) (hclE hv)
  rcases exp_est_local_diffeomorphism_ball expb b ρE ((Kf : ℝ) * (Lf : ℝ) * τu) hρE hκ0 hκ1 hExp0 hest
    with ⟨invb, hInv2b, hInv1b, hInjb, hCoverb⟩
  -- derivative of expb is near the identity on ball 0 ρE
  have hfdNear (v : E) (hv : v ∈ ball (0 : E) ρE) :
      ‖fderiv ℝ expb v - ContinuousLinearMap.id ℝ E‖ ≤ (Kf : ℝ) * (Lf : ℝ) * τu := by
    let G : E → E := expb - (fun z : E => z)
    have hde : DifferentiableAt ℝ expb v := by
      exact (hExpC1.contDiffAt (isOpen_ball.mem_nhds hv)).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
    have hdid : HasFDerivAt (fun z : E => z) (ContinuousLinearMap.id ℝ E) v := hasFDerivAt_id v
    have hdG : HasFDerivAt G (fderiv ℝ expb v - ContinuousLinearMap.id ℝ E) v := by
      change HasFDerivAt (expb - (fun z : E => z)) (fderiv ℝ expb v - ContinuousLinearMap.id ℝ E) v
      exact hde.hasFDerivAt.sub hdid
    have hvτ : v ∈ ball (0 : E) τu := by
      exact ball_subset_ball hρEτu hv
    have hlip' : ∀ᶠ x in 𝓝 v, ‖G x - G v‖ ≤ (Kf : ℝ) * (Lf : ℝ) * τu * ‖x - v‖ := by
      filter_upwards [isOpen_ball.mem_nhds hvτ] with x hx
      have hxτ : x ∈ ball (0 : E) τu := hx
      have hxτ' : x ∈ closedBall (0 : E) τu := ball_subset_closedBall hxτ
      have hvτ' : v ∈ closedBall (0 : E) τu := ball_subset_closedBall hvτ
      have hb' := htp x v hxτ' hvτ'
      have heq : expb x - x - (expb v - v) = (expb x - expb v) - (x - v) := by abel
      simpa [G, heq] using hb'
    have hfdG : ‖fderiv ℝ expb v - ContinuousLinearMap.id ℝ E‖ ≤ (Kf : ℝ) * (Lf : ℝ) * τu :=
      hdG.le_of_lip' hκ0 hlip'
    exact hfdG
  have hInvDb : ∀ v ∈ ball (0 : E) ρE, ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ expb v := by
    intro v hv
    have hlt : ‖fderiv ℝ expb v - ContinuousLinearMap.id ℝ E‖ < 1 := by
      have hle := hfdNear v hv
      linarith [hκ14]
    exact clm_invertible_of_near_id (fderiv ℝ expb v) hlt

  -- domain of staying curves and C¹-ness of the inverse on it
  have hVcov : ball b δu ⊆ expb '' ball (0 : E) ρE := by
    exact Subset.trans (ball_subset_ball hδuκρE) hCoverb
  have hContAtInv (y : E) (hyV : y ∈ ball b δu) : ContDiffAt ℝ 1 invb y := by
    exact contDiffAt_inv_of_twoPoint expb hρE hExpC1 hInvDb hInv2b hInv1b (hVcov hyV)
  let V : Set E := ball b δu
  let F : E → ℝ := fun z : E => Real.sqrt ((g b) (invb z) (invb z))
  have hFcont : ContinuousOn F V := by
    intro y hyV
    have hc1 : ContDiffAt ℝ 1 invb y := hContAtInv y hyV
    have hc : ContinuousAt (fun z : E => Real.sqrt ((g b) (invb z) (invb z))) y :=
      radialComp_continuousAt (B := g b) (inv := invb) y hc1.continuousAt
    have hc' : ContinuousAt F y := by simpa [F] using hc
    exact hc'.continuousWithinAt
  have hFdiff : ∀ y ∈ V, y ≠ b → DifferentiableAt ℝ F y := by
    intro y hyV hyne
    have hc1 : ContDiffAt ℝ 1 invb y := hContAtInv y hyV
    have hinv0 : invb y ≠ 0 := by
      intro hz
      apply hyne
      have hy' : expb (invb y) = y := (hInv1b y (hVcov hyV)).2
      rw [← hy', hz, hExp0]
    have hposval : 0 < ((g b) (invb y)) (invb y) := hpos b (invb y) hinv0
    have hd := radialComp_differentiableAt (B := g b) (inv := invb) y hc1 hposval
    simpa [F] using hd
  -- radial (Gauss) bound, with the uniform constants
  have hFb : ∀ y ∈ V, y ≠ b → ∀ X : E, ‖(fderiv ℝ F y) X‖ ≤ mgSpeed g y X := by
    intro y hyV hyne X
    have hyExp : y ∈ expb '' ball (0 : E) ρE := hVcov hyV
    have hvU : invb y ∈ ball (0 : E) ρE := (hInv1b y hyExp).1
    have hvexp : expb (invb y) = y := (hInv1b y hyExp).2
    let v : E := invb y
    have hvb : v ∈ ball (0 : E) ρE := hvU
    have hvexp' : expb v = y := by simpa [v] using hvexp
    have hvne : v ≠ 0 := by
      intro hz
      apply hyne
      rw [← hvexp', hz]
      exact hExp0
    have hvE : ‖v‖ < ρE := by
      have hd : dist v 0 < ρE := mem_ball.mp hvb
      simpa [dist_eq_norm] using hd
    have hvin : (b, τu⁻¹ • v) ∈ ball (b, (0 : E)) (1 / 4) := by
      have hρ4 : ρE < τu / 4 := by
        dsimp [ρE]
        have hδ : δc / 2 < 1 / 4 := by
          have hδc4 : δc ≤ 1 / 4 := by linarith [hδc8]
          nlinarith [hδc4, hδc0]
        nlinarith [hδ, hτu0]
      have hvlt : ‖v‖ < τu / 4 := lt_of_lt_of_le hvE (le_of_lt hρ4)
      rw [mem_ball, dist_eq_norm]
      have hnorm : ‖(b, τu⁻¹ • v) - (b, (0 : E))‖ = ‖τu⁻¹ • v‖ := by simp
      rw [hnorm]
      have hposτ : 0 < τu⁻¹ := by positivity
      have hsmul : ‖τu⁻¹ • v‖ ≤ τu⁻¹ * ‖v‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hposτ)]
      have h2 : τu⁻¹ * ‖v‖ < 1 / 4 := by
        have hle : τu⁻¹ * ‖v‖ < τu⁻¹ * (τu / 4) :=
          mul_lt_mul_of_pos_left hvlt hposτ
        have hstep : τu⁻¹ * (τu / 4) = 1 / 4 := by
          field_simp [ne_of_gt hτu0]
        rw [hstep] at hle
        exact hle
      exact lt_of_le_of_lt hsmul h2
    rcases fderiv_exp_surj (ρ := ρE) hρE v hvb hInvDb X with ⟨W, hXW⟩
    let R : E → ℝ := fun z : E => Real.sqrt ((g b) z z)
    have hFR : ∀ x ∈ ball (0 : E) ρE, F (expb x) = R x := by
      intro x hxU
      dsimp [F, R]
      rw [hInv2b x hxU]
    have hFyD : DifferentiableAt ℝ F (expb v) := by
      have hyE : expb v ≠ b := by rw [hvexp']; exact hyne
      have hmem : expb v ∈ V := by rw [hvexp']; exact hyV
      exact hFdiff (expb v) hmem hyE
    have hExpD : DifferentiableAt ℝ expb v := by
      have hcv : ContDiffAt ℝ 1 expb v := hExpC1.contDiffAt (isOpen_ball.mem_nhds hvb)
      exact hcv.differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
    have hRD : DifferentiableAt ℝ R v := by
      have hd := radialComp_differentiableAt (B := g b) (inv := fun z : E => z) v
        (by
          have hcv : ContDiffAt ℝ 1 (fun z : E => z) v :=
            (contDiff_id : ContDiff ℝ 1 (fun z : E => z)).contDiffAt
          exact hcv) (by simpa using hpos b v hvne)
      simpa [R] using hd
    have hdcomp := fderiv_comp_eq_on_open (F := F) (R := R) (exp := expb) (U := ball (0 : E) ρE)
      isOpen_ball hvb hFR hFyD hExpD hRD
    have hval : (fderiv ℝ F y) X = (fderiv ℝ R v) W := by
      calc
        (fderiv ℝ F y) X = (fderiv ℝ F (expb v)) ((fderiv ℝ expb v) W) := by rw [← hvexp', hXW]
        _ = ((fderiv ℝ F (expb v)).comp (fderiv ℝ expb v)) W := rfl
        _ = (fderiv ℝ R v) W := by rw [hdcomp]
    have hb := radial_bound_main g hg hinv hsym hpos b (Tf := τf) hτf (Lf := Lf) (Φ := Φ)
      hPerB hLipB (K0 := K0) hK0 hKb (δ := (1 / 4 : ℝ)) (by norm_num) (by norm_num)
      (τ := τu) hτu0 h4τuτf hUb (v := v) (W := W) hvin hvne
    have hbX : ‖(fderiv ℝ R v) W‖ ≤ Real.sqrt ((g y) X X) := by
      have h1 : ‖(fderiv ℝ R v) W‖ ≤
          Real.sqrt ((g (expOf b Φ τu v)) ((fderiv ℝ (expOf b Φ τu)) v W)
            ((fderiv ℝ (expOf b Φ τu)) v W)) := by
        simpa [R] using hb
      have hXeq : (fderiv ℝ (expOf b Φ τu)) v W = X := by
        simpa [expb] using hXW
      have hyeq : expOf b Φ τu v = y := by
        simpa [expb] using hvexp'
      rw [hXeq] at h1
      rw [hyeq] at h1
      simpa using h1
    have hmain : ‖(fderiv ℝ F y) X‖ ≤ Real.sqrt ((g y) X X) := by
      rw [hval]
      exact hbX
    simpa [mgSpeed] using hmain
  -- hypotheses for the generic radial minimality wrapper
  have hFeq : (radialCoord g b invb) = F := by
    funext z
    simp [F, radialCoord]
  have hFRC_cont : ContinuousOn (radialCoord g b invb) V := by
    simpa [hFeq] using hFcont
  have hFRC_diff : ∀ y ∈ V, y ≠ b → DifferentiableAt ℝ (radialCoord g b invb) y := by
    intro y hy hne
    have hd := hFdiff y hy hne
    simpa [hFeq] using hd
  have hFRC_b : ∀ y ∈ V, y ≠ b → ∀ X : E,
      ‖(fderiv ℝ (radialCoord g b invb) y) X‖ ≤ mgSpeed g y X := by
    intro y hy hne X
    have hd := hFb y hy hne X
    simpa [hFeq] using hd
  have hU0 : (0 : E) ∈ ball (0 : E) ρE := by simpa using hρE
  have hVb : b ∈ V := by
    dsimp [V]
    simpa using hδu
  have hinj0 : ∀ v ∈ ball (0 : E) ρE, expb v = b → v = 0 := by
    intro v hv hx0
    have h0U' : (0 : E) ∈ ball (0 : E) ρE := hU0
    have heq : expb v = expb (0 : E) := by simpa [hExp0] using hx0
    exact hInjb v (0 : E) hv h0U' heq
  have hMinb : ∀ v ∈ ball (0 : E) ρE, ∀ c : ℝ → E,
      c 0 = b → c 1 = expb v →
      (∃ O : Set ℝ, IsOpen O ∧ Icc (0 : ℝ) 1 ⊆ O ∧ ContDiffOn ℝ 1 c O) →
      (∀ s ∈ Icc (0 : ℝ) 1, c s ∈ V) →
      Real.sqrt ((g b) v v) ≤ mgLength g c 0 1 := by
    intro v hv c hc0 hc1 hcO hcV
    exact radial_minimality g hg hinv hsym hpos b (exp := expb) (inv := invb)
      (U := ball (0 : E) ρE) (V := V) hExp0 hU0 hInv2b hinj0 hVb hFRC_cont hFRC_diff hFRC_b
      v hv c hc0 hc1 hcO hcV
  have hvρE : v ∈ ball (0 : E) ρE := ball_subset_ball hδuρE hv
  exact hMinb v hvρE c hc0 hc1 hcO hcStay

end
end Submission.Model
