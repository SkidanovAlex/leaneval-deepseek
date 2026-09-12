import Submission.Model
import Submission.ModelCore
import Submission.ModelFlowCont
import Submission.ModelVarFrechet
import Submission.ModelVarConv
import Submission.ModelDerivId
import Submission.ModelJacobi
import Submission.ModelJacLin
import Submission.ModelUniq
import Submission.ModelExp
import Submission.ModelAlg
import Submission.ModelScale
import Submission.ExpCore
import Submission.ModelExpDiffeo2
import Mathlib

/-!
# The geodesic-flow exponential map is C¹ on a neighbourhood of zero (rigid statement)

Theorem: `Submission.Model.exp_c1`.

## Motivation

`Submission.ModelExpDiffeo2.flow_exp_local_diffeomorphism` gives an exponential map
`exp : E → E` (built from the genuine geodesic flow `Φ` of the field `odeField g`) with
`exp 0 = x₀`, ray agreement `exp (t • w) = (Φ (x₀, w) t).1` for metric-unit `w`, and
`HasFDerivAt exp id 0`, but NO regularity beyond differentiability at `0`.  For the genuine
Riemannian normal-coordinate theory (radial coordinate 1-Lipschitz, local minimality of radial
geodesics, local rigidity of locally-linear curves) we need `exp` to be **C¹ on a full
neighbourhood of 0** with invertible derivative there.  The inverse function theorem then turns
this into a C¹ local diffeomorphism with C¹ inverse.

## Concrete statement (rigid; keep the name)

    theorem exp_c1 (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
        (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
        (x₀ : E) :
        ∃ ρ > 0, ∃ Φ : E × E → ℝ → E × E,
          (∀ z ∈ closedBall (x₀, 0) 2, Φ z 0 = z ∧
             ∀ t ∈ Ioo (-ρ) ρ, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
          ∃ exp : E → E,
            exp 0 = x₀ ∧
            (∀ w : E, (g x₀) w w = 1 → ∀ t ∈ Ioo (-ρ) ρ,
               exp (t • w) = (Φ (x₀, w) t).1) ∧
            HasFDerivAt exp (ContinuousLinearMap.id ℝ E) 0 ∧
            ContDiffOn ℝ 1 exp (ball 0 ρ) ∧
            (∀ v ∈ ball 0 ρ, ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ exp v)

## Proof route

1. Destructure `Submission.ExpCore.flow_exp_core g hg hinv x₀`, obtaining `ρ₀ > 0`, a flow `Φ₀`
   on `closedBall (x₀,0) 1` (times `Icc (-(2*ρ₀)) (2*ρ₀)`), with the exponential
   `exp₀ v := (Φ₀ (x₀, (1/ρ₀) • v) ρ₀).1` (`exp₀ 0 = x₀`, `HasFDerivAt exp₀ id 0`, and the
   local-diffeomorphism clause).  Use this `exp₀` as the witness `exp` (as in
   `flow_exp_local_diffeomorphism`).  All clauses except `ContDiffOn` and the derivative-
   invertibility clause come from the same construction as `flow_exp_local_diffeomorphism`
   (copy its argument to assemble `Φ`/`exp` and prove the flow/ray/differential clauses).

2. **Core analytic content — `ContDiffOn ℝ 1 exp₀ (ball 0 ρ)`.**  Reduce to a uniform
   regularity statement for `Φ₀` in its first argument: for `z₀' := (x₀, 0)` there is `δ > 0`
   with, for every `t ∈ Icc (-ρ₀) ρ₀`,
   `ContDiffOn ℝ 1 (fun z => Φ₀ z t) (closedBall z₀' δ)`.
   The `ContDiffOn 1` is proved via `contDiffOn_iff` (or per point): every point of the ball
   has a total derivative — this is the per-point differentiability of `flow_fderiv_canonical`
   (ModelDerivId) applied at each centre `z̄ ∈ closedBall z₀' δ` — and the derivative map
   `z ↦ fderiv (fun z' => Φ₀ z' t) z` is continuous.
   *Differentiability at each point*: instantiate `ModelDerivId.flow_fderiv_canonical` (or
   `ModelVarFrechet.variation_frechet`) at centre `z̄` with the same global flow `Φ₀`, whose
   hypothesis `hΦ₀ : ∀ z ∈ closedBall z̄ 1, ...` follows from the core flow property since
   `closedBall z̄ 1 ⊆ closedBall (x₀,0) 1` for `‖z̄ - (x₀,0)‖ < 1` (choose δ < 1).  Use the
   canonical family `J` of `ModelVarFrechet.canonical_solutions`/`ModelJacobi.linearized_exists`
   (with `J w t` linear-additive in `w` from `ModelJacLin.linearized_linear`).
   *Continuity of the derivative*: the derivative at `z̄` is the linearized solution
   `J_{z̄}(t)` along the geodesic from `z̄` (`ModelDerivId.flow_deriv_eq_linearized`).  Prove a
   Gronwall estimate: for `z₁, z₂ ∈ closedBall z₀' δ`,
   `‖J_{z₁} t - J_{z₂} t‖ ≤ C · ‖z₁ - z₂‖` uniformly in `t ∈ Icc (-ρ₀) ρ₀`.  Both `J_{zᵢ}`
   solve the linear ODE `d/dt X = A_{zᵢ}(t) X` with
   `A_{zᵢ}(t) := fderiv ℝ (odeField g) (Φ₀ zᵢ t)`.  Bound
   `‖A_{z₁}(t) - A_{z₂}(t)‖ ≤ Lip(fderiv (odeField g)) · ‖Φ₀ z₁ t - Φ₀ z₂ t‖`
   (use `ModelJacLin.fderiv_odeField_continuous` for global continuity of `fderiv (odeField g)`
   and the Lipschitz-in-data estimate of the flow — `ModelFlowCont.flow_lipschitz` or the
   `hLip` clause of `flow_exp_core`), then apply Mathlib's Gronwall lemmas for linear ODEs
   (see `Mathlib/Analysis/ODE/Gronwall.lean`) to the difference `J_{z₁} - J_{z₂}`.  This gives
   the continuity (indeed Lipschitz-ness) of `z ↦ fderiv (fun z' => Φ₀ z' t) z`.

3. **Push to exp₀.** `exp₀ v = (Φ₀ (x₀, (1/ρ₀) • v) ρ₀).1`; the map
   `v ↦ (x₀, (1/ρ₀) • v)` is affine (its derivative is the linear map `u ↦ (0, (1/ρ₀) • u)`).
   Compose the C¹-in-data statement with this affine map and the continuous linear projection
   `(·).1` to get `ContDiffOn ℝ 1 exp₀ (ball 0 ρ)` for `ρ := min (ρ₀/2) (ρ₀·δ/2)`-style radius.

4. **Derivative invertibility on a (smaller) ball.**  `fderiv ℝ exp v` is a continuous
   function of `v` (from C¹); at `v = 0` it is `ContinuousLinearMap.id ℝ E`, an equivalence.
   The set of invertible continuous linear maps is open (Mathlib: search
   `ContinuousLinearMap.isUnit`, `exists_linearEquiv`/`Units`, Neumann series
   `ContinuousLinearMap.inverse`); conclude that on a smaller ball `ball 0 ρ' ⊆ ball 0 ρ` the
   derivative `fderiv ℝ exp v` is a continuous linear equivalence.  State the final theorem with
   that smaller `ρ'` (so `ball 0 ρ' ⊆ ball 0 ρ` must be kept explicit in the proof).

## Hints

* Everything is inside `namespace Submission.Model`; qualify imported lemmas when needed.
* `E` is finite-dimensional (`[FiniteDimensional ℝ E]`), so compactness arguments and
  `ContinuousLinearMap` norm bounds apply; norms on `E × E` are the product norm.
* Mind that `ContDiffOn ℝ 1 f s` requires, on `s`: continuity of `f`, existence of `fderiv f x`
  at each `x ∈ s`, and continuity of `x ↦ fderiv f x`.  Lemmas like
  `contDiffOn_iff_continuousOn_fderiv` may help.
* The `odeField`/`accel`/`Bilin` names need the `Submission.Model.` prefix outside the
  namespace; inside it is fine.
* Do NOT change the statement of `exp_c1`.  You may add any helper definitions/lemmas.
  No `placeholder`/`placeholder`/new `placeholder` may remain in the file.
-/

open ContinuousLinearMap
open scoped ContDiff Topology BigOperators
open Set Metric Module

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section


set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- uniform bound of `‖fderiv (odeField g)‖` on a closed ball -/
lemma field_fderiv_bound (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (z₀ : E × E) (R : ℝ) (hR : 0 ≤ R) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ p ∈ closedBall z₀ R, ‖fderiv ℝ (odeField g) p‖ ≤ K := by
  classical
  have hcont : Continuous (fun p : E × E => fderiv ℝ (odeField g) p) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact (odeField_contDiffAt g hg hinv p.1 p.2).continuousAt_fderiv (by norm_num)
  rcases (isCompact_closedBall z₀ R).exists_isMaxOn ⟨z₀, by simpa using hR⟩ hcont.norm.continuousOn with
    ⟨xm, hxm, hmax⟩
  refine ⟨‖fderiv ℝ (odeField g) xm‖, norm_nonneg _, ?_⟩
  intro p hp
  exact hmax hp

/-- uniform bound of `‖odeField g‖` on a closed ball -/
lemma field_value_bound (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (z₀ : E × E) (R : ℝ) (hR : 0 ≤ R) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p ∈ closedBall z₀ R, ‖odeField g p‖ ≤ M := by
  classical
  have hcont : Continuous (fun p : E × E => odeField g p) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact (odeField_contDiffAt g hg hinv p.1 p.2).continuousAt
  rcases (isCompact_closedBall z₀ R).exists_isMaxOn ⟨z₀, by simpa using hR⟩ hcont.norm.continuousOn with
    ⟨xm, hxm, hmax⟩
  refine ⟨‖odeField g xm‖, norm_nonneg _, ?_⟩
  intro p hp
  exact hmax hp

/-- The linearized IVP along a base geodesic has a solution on the input window `T`, provided the
global fderiv bound and the window-size constraint hold. -/
lemma linearized_exists_window (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) {Tf : ℝ} (hTf : 0 < Tf)
    {c vel : ℝ → E} {w : E × E} {K0 : ℝ}
    (hc : ∀ t ∈ Ioo (-Tf) Tf, HasDerivAt c (vel t) t)
    (hv : ∀ t ∈ Ioo (-Tf) Tf,
      HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t)
    (hK : ∀ t ∈ Icc (-Tf) Tf, ‖fderiv ℝ (odeField g) (c t, vel t)‖ ≤ K0)
    (hK0 : 0 ≤ K0) {T : ℝ} (hTpos : 0 < T) (hTltTf : T < Tf)
    (hTbound : 2 * (K0 + 1) * (‖w‖ + 1) * T ≤ 1) :
    ∃ J : ℝ → E × E,
      J 0 = w ∧
      (∀ t ∈ Ioo (-T) T,
        HasDerivAt J ((fderiv ℝ (odeField g)) (c t, vel t) (J t)) t) := by
  let z : ℝ → E × E := fun t => (c t, vel t)
  have hz (t : ℝ) (ht : t ∈ Ioo (-Tf) Tf) :
      HasDerivAt z (odeField g (z t)) t := by
    dsimp [z]
    exact ((hc t ht).prodMk (hv t ht)).congr_deriv (by simp [odeField])
  have h0 : (0 : ℝ) ∈ Ioo (-Tf) Tf := by
    constructor <;> linarith
  have hdf (p : E × E) : ContinuousAt (fderiv ℝ (odeField g)) p := by
    exact (odeField_contDiffAt g hg hinv p.1 p.2).continuousAt_fderiv (by norm_num)
  have hcontD : Continuous (fderiv ℝ (odeField g)) := by
    rw [continuous_iff_continuousAt]
    intro p
    exact hdf p
  let L : ℝ → (E × E) →L[ℝ] (E × E) := fun t => fderiv ℝ (odeField g) (z t)
  let Kb : ℝ := K0 + 1
  have hKb0 : 0 ≤ Kb := by dsimp [Kb]; positivity
  have hKbpos : 0 < Kb := by dsimp [Kb]; linarith
  let Lb : ℝ := Kb * (‖w‖ + 1)
  have hLbpos : 0 < Lb := by
    dsimp [Lb]
    exact mul_pos hKbpos (by positivity)
  have hTmul : Lb * T ≤ 1 := by
    have h1 : (2 : ℝ) * Lb * T ≤ 1 * 2 := by
      -- from hTbound: 2 * Kb * (‖w‖+1) * T ≤ 1
      nlinarith [hTbound]
    nlinarith
  have hzcontOn : ContinuousOn z (Icc (-T) T) := by
    intro t ht
    have htI : t ∈ Ioo (-Tf) Tf := by
      constructor
      · linarith [ht.1, hTltTf]
      · linarith [ht.2, hTltTf]
    exact (hz t htI).continuousAt.continuousWithinAt
  have hLcontOn : ContinuousOn L (Icc (-T) T) := by
    have hc1 : ContinuousOn (fun t => fderiv ℝ (odeField g) (z t)) (Icc (-T) T) :=
      hcontD.comp_continuousOn hzcontOn
    simpa [L] using hc1
  have hnormI (t : ℝ) (ht : t ∈ Icc (-T) T) : ‖L t‖ ≤ Kb := by
    have ht' : t ∈ Icc (-Tf) Tf := by
      constructor
      · exact le_trans (neg_le_neg (le_of_lt hTltTf)) ht.1
      · exact le_trans ht.2 (le_of_lt hTltTf)
    dsimp [Kb]
    linarith [hK t ht']
  let F : ℝ → (E × E) → (E × E) := fun t J => L t J
  let Knn : NNReal := ⟨Kb, hKb0⟩
  let Lbnn : NNReal := ⟨Lb, le_of_lt hLbpos⟩
  have hmem0 : (0 : ℝ) ∈ Icc (-T) T := by
    constructor <;> linarith
  have hpl : IsPicardLindelof F (tmin := -T) (tmax := T) ⟨0, hmem0⟩ w (1 : NNReal) 0 Lbnn Knn := by
    refine IsPicardLindelof.mk ?lipschitzOnWith ?continuousOn ?norm_le ?mul_max_le
    · intro t ht
      have hKle : ‖L t‖₊ ≤ Knn := by
        dsimp [Knn]
        exact_mod_cast hnormI t ht
      have hlip : LipschitzOnWith Knn (L t) (closedBall w (1 : ℝ)) :=
        ((L t).lipschitz.weaken hKle).lipschitzOnWith
      simpa [F] using hlip
    · intro J hJ
      have heval : Continuous (fun A : (E × E) →L[ℝ] (E × E) => A J) := by
        fun_prop
      have h : ContinuousOn (fun t => (L t) J) (Icc (-T) T) := heval.comp_continuousOn hLcontOn
      simpa [F] using h
    · intro t ht J hJ
      have hdist : dist J w ≤ 1 := by simpa using hJ
      have hnormJ : ‖J‖ ≤ ‖w‖ + 1 := by
        calc
          ‖J‖ = ‖(J - w) + w‖ := by abel_nf
          _ ≤ ‖J - w‖ + ‖w‖ := norm_add_le _ _
          _ = dist J w + ‖w‖ := by rw [← dist_eq_norm J w]
          _ ≤ ‖w‖ + 1 := by linarith
      have hb1 : ‖L t J‖ ≤ ‖L t‖ * ‖J‖ := (L t).le_opNorm J
      have hb2 : ‖L t‖ * ‖J‖ ≤ Kb * ‖J‖ :=
        mul_le_mul_of_nonneg_right (hnormI t ht) (norm_nonneg J)
      have hb3 : Kb * ‖J‖ ≤ Kb * (‖w‖ + 1) :=
        mul_le_mul_of_nonneg_left hnormJ hKb0
      have hb4 : Kb * (‖w‖ + 1) = Lb := by dsimp [Lb]
      have hb5 : ‖L t J‖ ≤ Lb := by
        calc
          ‖L t J‖ ≤ ‖L t‖ * ‖J‖ := hb1
          _ ≤ Kb * ‖J‖ := hb2
          _ ≤ Kb * (‖w‖ + 1) := hb3
          _ = Lb := hb4
      dsimp [F, Lbnn]
      exact hb5
    · simp
      dsimp [Lbnn]
      change Lb * T ≤ (1 : ℝ)
      exact hTmul
  rcases hpl.exists_eq_forall_mem_Icc_hasDerivWithinAt₀ with ⟨J, hJ0, hJd⟩
  refine ⟨J, ?_, ?_⟩
  · simpa using hJ0
  · intro t ht
    have htIcc : t ∈ Icc (-T) T := Ioo_subset_Icc_self ht
    have hd := hJd t htIcc
    have hdAt : HasDerivAt J (F t (J t)) t := hd.hasDerivAt (Icc_mem_nhds ht.1 ht.2)
    simpa [F, L, z] using hdAt
lemma uniform_lin_est_r (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (z₀ : E × E) (r : ℝ) (hr : 0 < r) (Tf : ℝ) (hTf : 0 < Tf)
    (Lf : NNReal) (Φ : (E × E) → ℝ → (E × E))
    (hΦ₀ : ∀ z ∈ closedBall z₀ r, Φ z 0 = z ∧
       ∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t)
    (hLip : ∀ t ∈ Icc (-Tf) Tf, LipschitzOnWith Lf (fun z => Φ z t) (closedBall z₀ r))
    (Tj : ℝ) (hTj : 0 < Tj) (hTjTf : Tj < Tf)
    (J : (E × E) → ℝ → (E × E))
    (hJ0 : ∀ w : E × E, J w 0 = w)
    (hJd : ∀ w : E × E, ∀ t ∈ Ioo (-Tj) Tj,
        HasDerivAt (J w) ((fderiv ℝ (odeField g)) (Φ z₀ t) (J w t)) t)
    {T : ℝ} (hTpos : 0 < T) (hTltTj : T < Tj) (hTltTf : T < Tf) :
    (∀ η > 0, ∃ h₀ > 0, ∀ w : E × E, ‖w‖ ≤ 1 →
      ∀ h : ℝ, h ≠ 0 → |h| < h₀ → z₀ + h • w ∈ closedBall z₀ r →
      ∀ t ∈ Icc (-T) T,
        ‖(1 / h) • (Φ (z₀ + h • w) t - Φ z₀ t) - J w t‖ ≤ η) := by
  let F := E × E
  let V : F → F := odeField g
  let cur : ℝ → F := fun t => Φ z₀ t
  have hz₀mem : z₀ ∈ closedBall z₀ r := by simpa [dist_eq_norm] using hr.le
  have hcur (t : ℝ) (ht : t ∈ Icc (-Tf) Tf) : HasDerivAt cur (V (cur t)) t := by
    simpa [cur, V] using (hΦ₀ z₀ hz₀mem).2 t ht
  have hTfIcc : Icc (-T) T ⊆ Icc (-Tf) Tf := by
    intro t ht
    constructor
    · exact le_trans (neg_le_neg (le_of_lt hTltTf)) ht.1
    · exact le_trans ht.2 (le_of_lt hTltTf)
  have hTjIoo : Icc (-T) T ⊆ Ioo (-Tj) Tj := by
    intro t ht
    constructor
    · exact lt_of_lt_of_le (neg_lt_neg hTltTj) ht.1
    · exact lt_of_le_of_lt ht.2 hTltTj
  have hcurCont : ContinuousOn cur (Icc (-T) T) := by
    intro t ht
    exact (hcur t (hTfIcc ht)).continuousAt.continuousWithinAt
  have hfdcont : Continuous (fderiv ℝ V) := by
    have hV1 : ContDiff ℝ 1 V := by
      rw [contDiff_iff_contDiffAt]
      intro p
      rcases p with ⟨x, v⟩
      simpa [V] using odeField_contDiffAt g hg hinv x v
    exact hV1.continuous_fderiv (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hnormCont : ContinuousOn (fun t => ‖fderiv ℝ V (cur t)‖) (Icc (-T) T) :=
    hfdcont.norm.comp_continuousOn hcurCont
  have hIccN : (Icc (-T) T).Nonempty := ⟨0, by constructor <;> linarith⟩
  rcases (isCompact_Icc : IsCompact (Icc (-T) T)).exists_isMaxOn hIccN hnormCont with
    ⟨tm, htm, hmaxT⟩
  let K : ℝ := ‖fderiv ℝ V (cur tm)‖
  have hK0 : 0 ≤ K := norm_nonneg _
  have hKb (t : ℝ) (ht : t ∈ Icc (-T) T) : ‖fderiv ℝ V (cur t)‖ ≤ K := by
    simpa [K] using hmaxT ht
  have hTay (ε : ℝ) (hε : 0 < ε) : ∃ δ > 0, ∀ t ∈ Icc (-T) T, ∀ y : F,
      y ∈ closedBall (cur t) δ →
      ‖V y - V (cur t) - (fderiv ℝ V (cur t)) (y - cur t)‖ ≤ ε * ‖y - cur t‖ := by
    have hc0cont : ContinuousOn (fun t : ℝ => (cur t).1) (Icc (-T) T) :=
      (continuous_fst.comp_continuousOn hcurCont)
    have hv0cont : ContinuousOn (fun t : ℝ => (cur t).2) (Icc (-T) T) :=
      (continuous_snd.comp_continuousOn hcurCont)
    rcases odeField_taylor_error g hg hinv hTpos hc0cont hv0cont ε hε with ⟨δ, hδ, hh⟩
    refine ⟨δ, hδ, ?_⟩
    intro t ht y hy
    simpa [V] using hh t ht y hy
  intro η hη
  have hgronCont : Continuous (fun ε : ℝ => gronwallBound 0 K ε T) := gronwallBound_continuous_ε 0 K T
  rcases Metric.continuousAt_iff.mp hgronCont.continuousAt η hη with ⟨c₀, hc₀, hc₀bd⟩
  let s : ℝ := (Lf : ℝ)
  have hs0 : 0 ≤ s := by dsimp [s]; positivity
  let εt : ℝ := c₀ / (2 * (s + 1))
  have hεt0 : 0 < εt := by dsimp [εt]; positivity
  let c : ℝ := εt * s
  have hc0 : 0 ≤ c := by dsimp [c]; positivity
  have hcclt : c < c₀ := by
    dsimp [c, εt]
    have hpos : 0 < 2 * (s + 1) := by positivity
    calc
      c₀ / (2 * (s + 1)) * s ≤ c₀ / (2 * (s + 1)) * (s + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt (by positivity))
      _ = c₀ / 2 := by field_simp [hpos.ne']
      _ < c₀ := by linarith
  have hc₀ltη : gronwallBound 0 K c T < η := by
    have hdist : dist c 0 < c₀ := by
      simpa [Real.dist_eq, sub_zero, abs_of_nonneg hc0]
    have hb := hc₀bd hdist
    rw [gronwallBound_ε0_δ0] at hb
    have hb' : |gronwallBound 0 K c T| < η := by simpa [Real.dist_eq] using hb
    exact (abs_lt.mp hb').2
  rcases hTay εt hεt0 with ⟨δt, hδt0, hTayδ⟩
  let h₀ : ℝ := δt / (s + 1)
  have hh₀ : 0 < h₀ := by
    dsimp [h₀]
    positivity
  refine ⟨h₀, hh₀, ?_⟩
  intro w hw h hhne hhlt hzmem
  let zh : ℝ → F := fun u => Φ (z₀ + h • w) u
  let q : ℝ → F := fun u => (1 / h) • (zh u - cur u)
  let D : ℝ → F := fun u => q u - J w u
  have hnorm_smul_div (v : F) : ‖(1 / h) • v‖ = ‖v‖ / |h| := by
    rw [norm_smul]
    rw [Real.norm_eq_abs, abs_div, abs_one]
    field_simp [abs_ne_zero.mpr hhne]
  have hLips (x : ℝ) (hx : x ∈ Icc (-T) T) : ‖zh x - cur x‖ ≤ s * |h| := by
    have hxTf : x ∈ Icc (-Tf) Tf := hTfIcc hx
    have hLipx : LipschitzOnWith Lf (fun z => Φ z x) (closedBall z₀ r) := hLip x hxTf
    calc
      ‖zh x - cur x‖ = dist (Φ (z₀ + h • w) x) (Φ z₀ x) := by
        simp [zh, cur, dist_eq_norm]
      _ ≤ (Lf : ℝ) * dist (z₀ + h • w) z₀ :=
        hLipx.dist_le_mul (z₀ + h • w) hzmem z₀ hz₀mem
      _ = (Lf : ℝ) * ‖h • w‖ := by rw [dist_eq_norm]; simp
      _ ≤ (Lf : ℝ) * |h| := by
        rw [norm_smul, Real.norm_eq_abs]
        have hmul : |h| * ‖w‖ ≤ |h| := by
          simpa using mul_le_mul_of_nonneg_left hw (abs_nonneg h)
        exact mul_le_mul_of_nonneg_left hmul (Lf : NNReal).2
      _ = s * |h| := by simp [s]
  have hsδ (x : ℝ) (hx : x ∈ Icc (-T) T) : ‖zh x - cur x‖ ≤ δt := by
    have hb1 : s * |h| ≤ s * h₀ := by
      exact mul_le_mul_of_nonneg_left (le_of_lt hhlt) hs0
    have hb2 : s * h₀ ≤ δt := by
      dsimp [h₀]
      have hpos : 0 < s + 1 := by positivity
      calc
        s * (δt / (s + 1)) = (s * δt) / (s + 1) := by ring
        _ ≤ δt := by
          rw [div_le_iff₀ hpos]
          nlinarith [hδt0.le]
    exact le_trans (hLips x hx) (le_trans hb1 hb2)
  have hper (x : ℝ) (hx : x ∈ Icc (-T) T) :
      ∃ gx : F, HasDerivAt D gx x ∧ ‖gx‖ ≤ K * ‖D x‖ + c := by
    let A : F →L[ℝ] F := fderiv ℝ V (cur x)
    let R : F := V (zh x) - V (cur x) - A (zh x - cur x)
    have hxTf : x ∈ Icc (-Tf) Tf := hTfIcc hx
    have hderzh : HasDerivAt zh (V (zh x)) x := by
      simpa [zh, V] using (hΦ₀ (z₀ + h • w) hzmem).2 x hxTf
    have hdercur : HasDerivAt cur (V (cur x)) x := hcur x hxTf
    have hdq0' : HasDerivAt (fun u : ℝ => (1 / h) • (zh u - cur u))
        ((1 / h) • (V (zh x) - V (cur x))) x :=
      (hderzh.sub hdercur).const_smul (1 / h)
    have hdq0 : HasDerivAt q ((1 / h) • (V (zh x) - V (cur x))) x := by
      simpa [q] using hdq0'
    have hdq : HasDerivAt q (A (q x) + (1 / h) • R) x := by
      apply hdq0.congr_deriv
      have hR : V (zh x) - V (cur x) = A (zh x - cur x) + R := by
        dsimp [R]
        abel
      calc
        (1 / h) • (V (zh x) - V (cur x)) = (1 / h) • (A (zh x - cur x) + R) := by rw [hR]
        _ = (1 / h) • A (zh x - cur x) + (1 / h) • R := by rw [smul_add]
        _ = A ((1 / h) • (zh x - cur x)) + (1 / h) • R := by rw [map_smul]
        _ = A (q x) + (1 / h) • R := rfl
    have hJx : HasDerivAt (J w) ((fderiv ℝ V) (cur x) (J w x)) x := by
      have hJt := hJd w x (hTjIoo hx)
      simpa [V, cur] using hJt
    have hDx : HasDerivAt (fun u : ℝ => q u - J w u)
        ((A (q x) + (1 / h) • R) - A (J w x)) x := (hdq.sub hJx)
    refine ⟨(A (q x) + (1 / h) • R) - A (J w x), ?_, ?_⟩
    · simpa [D] using hDx
    · have hAK : ‖A‖ ≤ K := by
        simpa [A] using hKb x hx
      have hb1 : ‖A (q x) - A (J w x)‖ ≤ K * ‖D x‖ := by
        calc
          ‖A (q x) - A (J w x)‖ = ‖A (q x - J w x)‖ := by rw [map_sub]
          _ ≤ ‖A‖ * ‖q x - J w x‖ := A.le_opNorm (q x - J w x)
          _ ≤ K * ‖q x - J w x‖ := mul_le_mul_of_nonneg_right hAK (norm_nonneg _)
          _ = K * ‖D x‖ := rfl
      have hb2 : ‖(1 / h) • R‖ ≤ c := by
        calc
          ‖(1 / h) • R‖ = ‖R‖ / |h| := hnorm_smul_div R
          _ ≤ (εt * ‖zh x - cur x‖) / |h| := by
            apply div_le_div_of_nonneg_right ?_ (abs_pos.mpr hhne).le
            have hT := hTayδ x hx (zh x) (by
              rw [mem_closedBall, dist_eq_norm]
              exact hsδ x hx)
            simpa [R, A] using hT
          _ ≤ (εt * (s * |h|)) / |h| := by
            apply div_le_div_of_nonneg_right ?_ (abs_pos.mpr hhne).le
            exact mul_le_mul_of_nonneg_left (hLips x hx) (le_of_lt hεt0)
          _ = εt * s := by
            field_simp [abs_ne_zero.mpr hhne]
          _ = c := rfl
      have hdec : (A (q x) + (1 / h) • R) - A (J w x) =
          (A (q x) - A (J w x)) + (1 / h) • R := by abel
      rw [hdec]
      exact le_trans (norm_add_le (A (q x) - A (J w x)) ((1 / h) • R)) (by nlinarith)
  let fp : ℝ → F := fun x => if hx : x ∈ Icc (-T) T then (hper x hx).choose else 0
  have hfp (x : ℝ) (hx : x ∈ Ico 0 T) : HasDerivAt D (fp x) x ∧ ‖fp x‖ ≤ K * ‖D x‖ + c := by
    have hxI : x ∈ Icc (-T) T := ⟨by linarith [hx.1, hTpos], le_of_lt hx.2⟩
    rw [show fp x = (hper x hxI).choose by
      unfold fp
      rw [dif_pos hxI]]
    exact (hper x hxI).choose_spec
  have hDcont : ContinuousOn D (Icc 0 T) := by
    intro x hx
    have hxI : x ∈ Icc (-T) T := ⟨by linarith [hx.1, hTpos], hx.2⟩
    exact (hper x hxI).choose_spec.1.continuousAt.continuousWithinAt
  have hD0 : D 0 = 0 := by
    dsimp [D, q, zh, cur]
    rw [(hΦ₀ (z₀ + h • w) hzmem).1, (hΦ₀ z₀ hz₀mem).1]
    have hsw : (1 / h) • (h • w) = w := by
      rw [smul_smul]
      have hmul : (1 / h) * h = 1 := by field_simp [hhne]
      rw [hmul, one_smul]
    have hstep : (1 / h) • (z₀ + h • w - z₀) = w := by
      have hz : z₀ + h • w - z₀ = h • w := by abel
      rw [hz]
      exact hsw
    rw [hstep, hJ0 w]
    simp
  have hpos (u : ℝ) (hu : u ∈ Icc 0 T) : ‖D u‖ ≤ gronwallBound 0 K c u := by
    have hderw : ∀ x ∈ Ico 0 T, HasDerivWithinAt D (fp x) (Ici x) x := by
      intro x hx
      exact (hfp x hx).1.hasDerivWithinAt
    have hbndw : ∀ x ∈ Ico 0 T, ‖fp x‖ ≤ K * ‖D x‖ + c := by
      intro x hx
      exact (hfp x hx).2
    have hres := norm_le_gronwallBound_of_norm_deriv_right_le (f := D) (f' := fp)
      (δ := 0) (K := K) (ε := c) (a := 0) (b := T)
      hDcont hderw (by rw [hD0]; simp) hbndw
    simpa using hres u hu
  have hEpIcc (s : ℝ) (hs : s ∈ Icc 0 T) :
      ∃ gx : F, HasDerivAt (fun r => D (-r)) gx s ∧ ‖gx‖ ≤ K * ‖(fun r => D (-r)) s‖ + c := by
    have hxI : -s ∈ Icc (-T) T := ⟨by linarith [hs.2], by linarith [hs.1, hTpos]⟩
    rcases hper (-s) hxI with ⟨gx, hder, hbnd⟩
    refine ⟨-(gx), ?_, ?_⟩
    · have hnegd : HasDerivAt (fun r : ℝ => -r) (-1 : ℝ) s := hasDerivAt_neg s
      change HasDerivAt (D ∘ Neg.neg) (-(gx)) s
      simpa using hder.scomp s hnegd
    · simpa [norm_neg] using hbnd
  let gp : ℝ → F := fun s => if hs : s ∈ Icc 0 T then (hEpIcc s hs).choose else 0
  have hgp (s : ℝ) (hs : s ∈ Ico 0 T) :
      HasDerivAt (fun r => D (-r)) (gp s) s ∧ ‖gp s‖ ≤ K * ‖(fun r => D (-r)) s‖ + c := by
    have hsI : s ∈ Icc 0 T := ⟨hs.1, le_of_lt hs.2⟩
    rw [show gp s = (hEpIcc s hsI).choose by
      unfold gp
      rw [dif_pos hsI]]
    exact (hEpIcc s hsI).choose_spec
  have hEcont : ContinuousOn (fun r => D (-r)) (Icc 0 T) := by
    intro s hs
    exact (hEpIcc s hs).choose_spec.1.continuousAt.continuousWithinAt
  have hneg (u : ℝ) (hu : u ∈ Icc (-T) 0) : ‖D u‖ ≤ gronwallBound 0 K c (-u) := by
    have hb1 : ∀ s ∈ Ico 0 T, HasDerivWithinAt (fun r => D (-r)) (gp s) (Ici s) s := by
      intro s hs
      exact (hgp s hs).1.hasDerivWithinAt
    have hb2 : ∀ s ∈ Ico 0 T, ‖gp s‖ ≤ K * ‖(fun r => D (-r)) s‖ + c := by
      intro s hs
      exact (hgp s hs).2
    have hres := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := (fun r => D (-r))) (f' := gp) (δ := 0) (K := K) (ε := c) (a := 0) (b := T)
      hEcont hb1 (by simp [hD0]) hb2
    have huI : -u ∈ Icc 0 T := ⟨by linarith [hu.2], by linarith [hu.1]⟩
    have hb := hres (-u) huI
    simpa using hb
  have hDfin (u : ℝ) (hu : u ∈ Icc (-T) T) : ‖D u‖ ≤ η := by
    have hm : Monotone (gronwallBound 0 K c) := gronwallBound_mono (by norm_num) hc0 hK0
    by_cases hu0 : 0 ≤ u
    · have hb := hpos u ⟨hu0, hu.2⟩
      exact le_trans (le_trans hb (hm hu.2)) (le_of_lt hc₀ltη)
    · have hb := hneg u ⟨hu.1, le_of_not_ge hu0⟩
      have hmt : -u ≤ T := by linarith [hu.1]
      exact le_trans (le_trans hb (hm hmt)) (le_of_lt hc₀ltη)
  intro t ht
  simpa [D, q, zh] using hDfin t ht
lemma flow_fderiv_canonical_r (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (z₀ : E × E) (r : ℝ) (hr : 0 < r) (Tf : ℝ) (hTf : 0 < Tf)
    (Lf : NNReal) (Φ : (E × E) → ℝ → (E × E))
    (hΦ₀ : ∀ z ∈ closedBall z₀ r, Φ z 0 = z ∧
       ∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t)
    (hLip : ∀ t ∈ Icc (-Tf) Tf, LipschitzOnWith Lf (fun z => Φ z t) (closedBall z₀ r))
    (Tj : ℝ) (hTj : 0 < Tj) (hTjTf : Tj < Tf)
    (J : (E × E) → ℝ → (E × E))
    (hJ0 : ∀ w : E × E, J w 0 = w)
    (hJd : ∀ w : E × E, ∀ t ∈ Ioo (-Tj) Tj,
        HasDerivAt (J w) ((fderiv ℝ (odeField g)) (Φ z₀ t) (J w t)) t)
    (hJadd : ∀ t : ℝ, ∀ (a b : E × E), J (a + b) t = J a t + J b t)
    (hJsmul : ∀ t : ℝ, ∀ (a : E × E) (c : ℝ), J (c • a) t = c • J a t)
    {T : ℝ} (hTpos : 0 < T) (hTltTj : T < Tj) (hTltTf : T < Tf) :
    ∀ t ∈ Icc (-T) T,
      ∃ L : E × E →L[ℝ] E × E,
        HasFDerivAt (fun z => Φ z t) L z₀ ∧ ∀ w : E × E, L w = J w t := by
  have hEst := uniform_lin_est_r g hg hinv z₀ r hr Tf hTf Lf Φ hΦ₀ hLip Tj hTj hTjTf J hJ0 hJd
    (T := T) hTpos hTltTj hTltTf
  intro t ht
  let L : (E × E) →ₗ[ℝ] (E × E) :=
    { toFun := fun w => J w t
      map_add' := fun a b => hJadd t a b
      map_smul' := fun c a => hJsmul t a c }
  let Lclm : (E × E) →L[ℝ] (E × E) := LinearMap.toContinuousLinearMap L
  refine ⟨Lclm, ?_, ?_⟩
  · rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    apply Asymptotics.IsLittleO.of_bound
    intro c hc
    rcases hEst c hc with ⟨h₀, hh₀, hEst'⟩
    let ρ : ℝ := min h₀ r
    have hρ : 0 < ρ := by dsimp [ρ]; exact lt_min hh₀ hr
    filter_upwards [Metric.ball_mem_nhds (0 : E × E) hρ] with v hv
    have hv_lt : ‖v‖ < ρ := by
      simpa [Real.dist_eq] using (mem_ball.mp hv)
    by_cases hv0 : v = 0
    · subst v
      have hL0 : Lclm 0 = 0 := by
        dsimp [Lclm]
        exact (L : (E × E) →ₗ[ℝ] (E × E)).map_zero
      simp [hL0]
    · have hnorm_ne : ‖v‖ ≠ 0 := by
        intro h
        exact hv0 (norm_eq_zero.mp h)
      have hpos : 0 < ‖v‖ := norm_pos_iff.mpr hv0
      let w : E × E := (‖v‖⁻¹) • v
      have hw_norm : ‖w‖ ≤ 1 := by
        dsimp [w]
        have hnw : ‖(‖v‖⁻¹) • v‖ = ‖v‖⁻¹ * ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (le_of_lt hpos)]
        rw [hnw]
        have hc' : ‖v‖⁻¹ * ‖v‖ = 1 := by field_simp [hnorm_ne]
        simpa [hc']
      have hvs : v = (‖v‖ : ℝ) • w := by
        dsimp [w]
        rw [smul_smul]
        have hmul : (‖v‖ : ℝ) * (‖v‖⁻¹) = 1 := by field_simp [hnorm_ne]
        rw [hmul, one_smul]
      have hhlt : |‖v‖| < h₀ := by
        have hle : ‖v‖ < h₀ := by
          exact lt_of_lt_of_le hv_lt (min_le_left h₀ r)
        simpa [abs_of_nonneg (le_of_lt hpos)] using hle
      have hmem : z₀ + (‖v‖ : ℝ) • w ∈ closedBall z₀ r := by
        rw [mem_closedBall, dist_eq_norm]
        have hle1 : ‖(‖v‖ : ℝ) • w‖ ≤ r := by
          have hnw : ‖(‖v‖ : ℝ) • w‖ = ‖v‖ * ‖w‖ := by
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hpos)]
          rw [hnw]
          have hm : ‖v‖ * ‖w‖ ≤ ‖v‖ * 1 := mul_le_mul_of_nonneg_left hw_norm (le_of_lt hpos)
          have hle2 : ‖v‖ ≤ r := by
            exact le_trans (le_of_lt hv_lt) (min_le_right h₀ r)
          calc
            ‖v‖ * ‖w‖ ≤ ‖v‖ * 1 := hm
            _ = ‖v‖ := by ring
            _ ≤ r := hle2
        calc
          ‖(z₀ + (‖v‖ : ℝ) • w) - z₀‖ = ‖(‖v‖ : ℝ) • w‖ := by simp
          _ ≤ r := hle1
      have hb := hEst' w hw_norm (‖v‖) hnorm_ne hhlt hmem t ht
      have hb0 : ‖(‖v‖⁻¹) • (Φ (z₀ + (‖v‖ : ℝ) • w) t - Φ z₀ t) - J w t‖ ≤ c := by
        simpa [one_div] using hb
      have hb' : ‖Φ (z₀ + (‖v‖ : ℝ) • w) t - Φ z₀ t - (‖v‖ : ℝ) • (J w t)‖ ≤ ‖v‖ * c :=
        norm_unscale_le (X := Φ (z₀ + (‖v‖ : ℝ) • w) t - Φ z₀ t) (Y := J w t)
          (r := ‖v‖) (c := c) hpos hb0
      have hJv : (‖v‖ : ℝ) • (J w t) = J v t := by
        rw [← hJsmul t w (‖v‖)]
        congr 1
        exact hvs.symm
      have hb'' : ‖Φ (z₀ + v) t - Φ z₀ t - J v t‖ ≤ c * ‖v‖ := by
        rw [← hvs] at hb'
        rw [hJv] at hb'
        have hmul : ‖v‖ * c = c * ‖v‖ := by ring
        rwa [hmul] at hb'
      have hLv : Lclm v = J v t := by
        dsimp [Lclm, L]
      simpa [hLv] using hb''
  · intro u
    dsimp [Lclm, L]

/-- Solutions of the linearized (Jacobi) equation along a base geodesic segment, for *all*
initial data `w`, on one common (input) time window, linear in `w`. -/
lemma canonical_solutions_uni (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (Tf : ℝ) (hTf : 0 < Tf)
    {c vel : ℝ → E} {K0 : ℝ} (hK0 : 0 ≤ K0)
    (hc : ∀ t ∈ Ioo (-Tf) Tf, HasDerivAt c (vel t) t)
    (hv : ∀ t ∈ Ioo (-Tf) Tf,
      HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t)
    (hK : ∀ t ∈ Icc (-Tf) Tf, ‖fderiv ℝ (odeField g) (c t, vel t)‖ ≤ K0)
    {U : ℝ} (hUpos : 0 < U) (hUltTf : U < Tf)
    (hUb : ∀ i : Fin (finrank ℝ (E × E)),
      2 * (K0 + 1) * (‖(finBasis ℝ (E × E)) i‖ + 1) * U ≤ 1) :
    ∃ J : (E × E) → ℝ → (E × E),
      (∀ w : E × E, J w 0 = w) ∧
      (∀ w : E × E, ∀ t ∈ Ioo (-U) U,
        HasDerivAt (J w) ((fderiv ℝ (odeField g)) (c t, vel t) (J w t)) t) ∧
      (∀ t : ℝ, ∀ (a b : E × E), J (a + b) t = J a t + J b t) ∧
      (∀ t : ℝ, ∀ (a : E × E) (d : ℝ), J (d • a) t = d • J a t) := by
  classical
  let ι := Fin (finrank ℝ (E × E))
  let b : Basis ι ℝ (E × E) := finBasis ℝ (E × E)
  have hper (i : ι) : ∃ J : ℝ → E × E,
      J 0 = b i ∧
        (∀ t ∈ Ioo (-U) U,
          HasDerivAt J ((fderiv ℝ (odeField g)) (c t, vel t) (J t)) t) := by
    have hTbound : 2 * (K0 + 1) * (‖b i‖ + 1) * U ≤ 1 := by
      simpa [b] using hUb i
    rcases linearized_exists_window g hg hinv (hTf := hTf) hc hv hK hK0 (T := U) hUpos hUltTf
      hTbound with ⟨J, hJ0, hJd⟩
    exact ⟨J, hJ0, hJd⟩
  let sol (i : ι) : {J : ℝ → E × E // J 0 = b i ∧
        (∀ t ∈ Ioo (-U) U,
          HasDerivAt J ((fderiv ℝ (odeField g)) (c t, vel t) (J t)) t)} := by
    let J0 : ℝ → E × E := Classical.choose (hper i)
    have hspec : J0 0 = b i ∧
        (∀ t ∈ Ioo (-U) U, HasDerivAt J0 ((fderiv ℝ (odeField g)) (c t, vel t) (J0 t)) t) :=
      Classical.choose_spec (hper i)
    exact ⟨J0, hspec⟩
  let solJ : ι → ℝ → E × E := fun i => (sol i).1
  have hsolJ0 (i : ι) : solJ i 0 = b i := by
    simpa [solJ] using (sol i).2.1
  have hsolJd (i : ι) (t : ℝ) (ht : t ∈ Ioo (-U) U) :
      HasDerivAt (solJ i) ((fderiv ℝ (odeField g)) (c t, vel t) (solJ i t)) t := by
    simpa [solJ] using (sol i).2.2 t ht
  have hsum_repr (f : ι → E × E) (w : E × E) :
      (b.constr ℝ f) w = ∑ i : ι, (b.repr w i) • f i := by
    simp
  let J : (E × E) → ℝ → (E × E) := fun w y => (b.constr ℝ (fun i => solJ i y)) w
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · intro w
    dsimp [J]
    have hfam : (fun i : ι => solJ i 0) = (fun i : ι => b i) := by
      funext i
      exact hsolJ0 i
    rw [hfam]
    rw [Basis.constr_apply]
    rw [Finsupp.sum_fintype (b.repr w) (fun i a => a • b i) (by intro i; simp)]
    exact b.sum_repr w
  · intro w t ht
    have hder_i (i : ι) : HasDerivAt (fun y : ℝ => (b.repr w i) • solJ i y)
        ((b.repr w i) • ((fderiv ℝ (odeField g)) (c t, vel t) (solJ i t))) t := by
      exact (hsolJd i t ht).const_smul (b.repr w i)
    have hsum := HasDerivAt.sum (u := (Finset.univ : Finset ι)) (fun i hi => hder_i i)
    have heq : (fun y : ℝ => ∑ i : ι, (b.repr w i) • solJ i y) =ᶠ[𝓝 t]
        (∑ i : ι, fun y => (b.repr w i) • solJ i y) := by
      filter_upwards with y
      simp
    have hmain : HasDerivAt (fun y : ℝ => ∑ i : ι, (b.repr w i) • solJ i y)
        (∑ i : ι, (b.repr w i) • ((fderiv ℝ (odeField g)) (c t, vel t) (solJ i t))) t :=
      hsum.congr_of_eventuallyEq heq
    have hcurve : (fun y : ℝ => (b.constr ℝ (fun i => solJ i y)) w) =ᶠ[𝓝 t]
        (fun y : ℝ => ∑ i : ι, (b.repr w i) • solJ i y) := by
      filter_upwards with y
      rw [hsum_repr]
    have hmain' : HasDerivAt (fun y : ℝ => (b.constr ℝ (fun i => solJ i y)) w)
        (∑ i : ι, (b.repr w i) • ((fderiv ℝ (odeField g)) (c t, vel t) (solJ i t))) t :=
      hmain.congr_of_eventuallyEq hcurve
    have hderA : (fderiv ℝ (odeField g)) (c t, vel t) (∑ i : ι, (b.repr w i) • solJ i t) =
        (∑ i : ι, (b.repr w i) • ((fderiv ℝ (odeField g)) (c t, vel t) (solJ i t))) := by
      calc
        (fderiv ℝ (odeField g)) (c t, vel t) (∑ i : ι, (b.repr w i) • solJ i t)
            = ∑ i : ι, (fderiv ℝ (odeField g)) (c t, vel t) ((b.repr w i) • solJ i t) := by
              simp [map_sum]
        _ = ∑ i : ι, (b.repr w i) • ((fderiv ℝ (odeField g)) (c t, vel t) (solJ i t)) := by
              simp [map_smul]
    have hder : (∑ i : ι, (b.repr w i) • ((fderiv ℝ (odeField g)) (c t, vel t) (solJ i t))) =
        (fderiv ℝ (odeField g)) (c t, vel t) (J w t) := by
      dsimp [J]
      rw [hsum_repr]
      exact hderA.symm
    exact hmain'.congr_deriv hder
  · intro t u v
    dsimp [J]
    exact (b.constr ℝ (fun i => solJ i t)).map_add u v
  · intro t u d
    dsimp [J]
    exact (b.constr ℝ (fun i => solJ i t)).map_smul d u

/-- At every point `zbar` of a (small) ball around `z₀` the time-`t` data-map of the flow is
differentiable, uniformly in `t` on a window: the derivative is given by the canonical family of
linearized solutions along the base trajectory from `zbar`. -/
lemma flow_fderiv_ballpoint (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (z₀ : E × E) (Tf : ℝ) (hTf : 0 < Tf)
    (Lf : NNReal) (Φ : E × E → ℝ → E × E)
    (hΦ₀ : ∀ z ∈ closedBall z₀ 1, Φ z 0 = z ∧
       (∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
       (∀ t : ℝ, Φ z t ∈ closedBall z₀ 2))
    (hLip : ∀ t ∈ Icc (-Tf) Tf, LipschitzOnWith Lf (fun z => Φ z t) (closedBall z₀ 1))
    {K0 : ℝ} (hK0 : 0 ≤ K0)
    (hK : ∀ p ∈ closedBall z₀ 2, ‖fderiv ℝ (odeField g) p‖ ≤ K0)
    {δ : ℝ} (hδ0 : 0 < δ) (hδ12 : δ ≤ 1 / 2)
    {U : ℝ} (hUpos : 0 < U) (hUTf : U ≤ Tf / 2)
    (hUb : ∀ i : Fin (finrank ℝ (E × E)),
      2 * (K0 + 1) * (‖(finBasis ℝ (E × E)) i‖ + 1) * U ≤ 1) :
    ∀ zbar ∈ ball z₀ δ, ∀ t ∈ Icc (-(U / 2)) (U / 2),
      ∃ J : E × E → ℝ → E × E,
        (∀ w : E × E, J w 0 = w) ∧
        (∀ w : E × E, ∀ s ∈ Ioo (-U) U,
          HasDerivAt (J w) ((fderiv ℝ (odeField g)) (Φ zbar s) (J w s)) s) ∧
        (∀ s : ℝ, ∀ a b : E × E, J (a + b) s = J a s + J b s) ∧
        (∀ s : ℝ, ∀ a : E × E, ∀ d : ℝ, J (d • a) s = d • J a s) ∧
        ∃ L : E × E →L[ℝ] E × E,
          HasFDerivAt (fun z => Φ z t) L zbar ∧ ∀ w : E × E, L w = J w t := by
  classical
  intro zbar hzδ t ht
  let r : ℝ := 1 / 2
  have hr : 0 < r := by norm_num
  have hzδ_le : ‖zbar - z₀‖ < δ := by
    simpa [dist_eq_norm] using (mem_ball.mp hzδ)
  have hsub : closedBall zbar r ⊆ closedBall z₀ 1 := by
    intro z hz
    have hdz : ‖z - zbar‖ ≤ r := by
      simpa [dist_eq_norm] using (mem_closedBall.mp hz)
    have hd : ‖z - z₀‖ ≤ 1 := by
      calc
        ‖z - z₀‖ = ‖(z - zbar) + (zbar - z₀)‖ := by abel
        _ ≤ ‖z - zbar‖ + ‖zbar - z₀‖ := norm_add_le (z - zbar) (zbar - z₀)
        _ ≤ r + δ := add_le_add hdz (le_of_lt hzδ_le)
        _ ≤ 1 := by dsimp [r] at *; nlinarith
    simpa [dist_eq_norm] using hd
  have hz₀1 : zbar ∈ closedBall z₀ 1 := by
    have hzr : zbar ∈ closedBall zbar r := by simpa using hr.le
    exact hsub hzr
  have hΦr : ∀ z ∈ closedBall zbar r, Φ z 0 = z ∧
       ∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
    intro z hz
    have hz1 := hsub hz
    exact ⟨(hΦ₀ z hz1).1, (hΦ₀ z hz1).2.1⟩
  have hCont2 (z : E × E) (hz : z ∈ closedBall zbar r) (t : ℝ) : Φ z t ∈ closedBall z₀ 2 := by
    exact (hΦ₀ z (hsub hz)).2.2 t
  have hLipr : ∀ t ∈ Icc (-Tf) Tf, LipschitzOnWith Lf (fun z => Φ z t) (closedBall zbar r) := by
    intro t ht
    exact (hLip t ht).mono hsub
  have hsplit := split_flow_geodesic g hg hinv zbar hTf (closedBall zbar r) Φ hΦr
    (z := zbar) (hz := by simpa using hr.le)
  let c : ℝ → E := fun s => (Φ zbar s).1
  let vel : ℝ → E := fun s => (Φ zbar s).2
  have hc (t : ℝ) (ht : t ∈ Ioo (-Tf) Tf) : HasDerivAt c (vel t) t := by
    simpa [c, vel] using hsplit.1 t ht
  have hv (t : ℝ) (ht : t ∈ Ioo (-Tf) Tf) :
      HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t := by
    simpa [c, vel] using hsplit.2 t ht
  have hKbase (t : ℝ) (ht : t ∈ Icc (-Tf) Tf) : ‖fderiv ℝ (odeField g) (c t, vel t)‖ ≤ K0 := by
    have hmem : Φ zbar t ∈ closedBall z₀ 2 := by
      have hzr : zbar ∈ closedBall zbar r := by simpa using hr.le
      exact hCont2 zbar hzr t
    have hval : (c t, vel t) = Φ zbar t := by
      dsimp [c, vel]
    rw [hval]
    exact hK (Φ zbar t) hmem
  have hUltTf : U < Tf := by
    linarith
  rcases canonical_solutions_uni g hg hinv Tf hTf (c := c) (vel := vel) (K0 := K0) hK0 hc hv hKbase
    (U := U) hUpos hUltTf hUb with ⟨J, hJ0, hJd, hJadd, hJsmul⟩
  have hJd' (w : E × E) (s : ℝ) (hs : s ∈ Ioo (-U) U) :
      HasDerivAt (J w) ((fderiv ℝ (odeField g)) (Φ zbar s) (J w s)) s := by
    have h := hJd w s hs
    have hval : (c s, vel s) = Φ zbar s := by
      dsimp [c, vel]
    simpa [hval] using h
  have hU2pos : 0 < U / 2 := by positivity
  have hU2ltU : U / 2 < U := by linarith
  have hU2ltTf : U / 2 < Tf := by linarith
  have hff := flow_fderiv_canonical_r g hg hinv zbar r hr Tf hTf Lf Φ hΦr hLipr U hUpos hUltTf
    J hJ0 hJd' hJadd hJsmul (T := U / 2) hU2pos hU2ltU hU2ltTf
  rcases hff t ht with ⟨L, hLfd, hLval⟩
  exact ⟨J, hJ0, hJd', hJadd, hJsmul, L, hLfd, hLval⟩

lemma growth_bound_raw {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {X : ℝ → F} {X' : ℝ → F} {τ K0 δ : ℝ} (hτ : 0 < τ) (hK0 : 0 ≤ K0) (hδ0 : 0 ≤ δ)
    (hX0 : ‖X 0‖ ≤ δ)
    (hder : ∀ s ∈ Icc (-τ) τ, HasDerivAt X (X' s) s)
    (hb : ∀ s ∈ Icc (-τ) τ, ‖X' s‖ ≤ K0 * ‖X s‖) :
    ∀ t ∈ Icc (-τ) τ, ‖X t‖ ≤ δ * Real.exp (K0 * τ) := by
  have hmain (u : ℝ) (hu : u ∈ Icc 0 τ) : ‖X u‖ ≤ gronwallBound δ K0 0 u := by
    have hXcont : ContinuousOn X (Icc 0 τ) := by
      intro s hs
      have hs' : s ∈ Icc (-τ) τ := by constructor <;> linarith [hs.1, hs.2, hτ]
      exact (hder s hs').continuousAt.continuousWithinAt
    have hderw : ∀ x ∈ Ico 0 τ, HasDerivWithinAt X (X' x) (Ici x) x := by
      intro x hx
      have hx' : x ∈ Icc (-τ) τ := by constructor <;> linarith [hx.1, hx.2, hτ]
      exact (hder x hx').hasDerivWithinAt
    have hbndw : ∀ x ∈ Ico 0 τ, ‖X' x‖ ≤ K0 * ‖X x‖ + 0 := by
      intro x hx
      have hx' : x ∈ Icc (-τ) τ := by constructor <;> linarith [hx.1, hx.2, hτ]
      simpa using hb x hx'
    have hres := norm_le_gronwallBound_of_norm_deriv_right_le (f := X) (f' := X')
      (δ := δ) (K := K0) (ε := 0) (a := 0) (b := τ) hXcont hderw hX0 hbndw
    simpa using hres u hu
  have htoe (u : ℝ) (hu : 0 ≤ u) (hut : u ≤ τ) :
      gronwallBound δ K0 0 u ≤ δ * Real.exp (K0 * τ) := by
    rw [gronwallBound_ε0]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_monotone (mul_le_mul_of_nonneg_left hut hK0)) hδ0
  have hpos (u : ℝ) (hu : u ∈ Icc 0 τ) : ‖X u‖ ≤ δ * Real.exp (K0 * τ) := by
    exact le_trans (hmain u hu) (htoe u hu.1 hu.2)
  -- negative times via reflection
  have hneg (u : ℝ) (hu : u ∈ Icc (-τ) 0) : ‖X u‖ ≤ δ * Real.exp (K0 * τ) := by
    let Y : ℝ → F := X ∘ Neg.neg
    let Y' : ℝ → F := fun r => -(X' (-r))
    have hY0 : ‖Y 0‖ ≤ δ := by simpa [Y] using hX0
    have hYder : ∀ s ∈ Icc (-τ) τ, HasDerivAt Y (Y' s) s := by
      intro s hs
      have hds : -s ∈ Icc (-τ) τ := by constructor <;> linarith [hs.1, hs.2, hτ]
      have hd := hder (-s) hds
      have hnegd : HasDerivAt (fun r : ℝ => -r) (-1) s := hasDerivAt_neg s
      have hc : HasDerivAt (X ∘ Neg.neg) (-(X' (-s))) s := by
        simpa using (hd.scomp s hnegd)
      simpa [Y, Y'] using hc
    have hYb : ∀ s ∈ Icc (-τ) τ, ‖Y' s‖ ≤ K0 * ‖Y s‖ := by
      intro s hs
      have hb' := hb (-s) (by constructor <;> linarith [hs.1, hs.2, hτ])
      simpa [Y, Y'] using hb'
    have hYmain (u : ℝ) (hu : u ∈ Icc 0 τ) : ‖Y u‖ ≤ gronwallBound δ K0 0 u := by
      have hYcont : ContinuousOn Y (Icc 0 τ) := by
        intro s hs
        have hs' : s ∈ Icc (-τ) τ := by constructor <;> linarith [hs.1, hs.2, hτ]
        exact (hYder s hs').continuousAt.continuousWithinAt
      have hderw : ∀ x ∈ Ico 0 τ, HasDerivWithinAt Y (Y' x) (Ici x) x := by
        intro x hx
        have hx' : x ∈ Icc (-τ) τ := by constructor <;> linarith [hx.1, hx.2, hτ]
        exact (hYder x hx').hasDerivWithinAt
      have hbndw : ∀ x ∈ Ico 0 τ, ‖Y' x‖ ≤ K0 * ‖Y x‖ + 0 := by
        intro x hx
        have hx' : x ∈ Icc (-τ) τ := by constructor <;> linarith [hx.1, hx.2, hτ]
        simpa using hYb x hx'
      have hres := norm_le_gronwallBound_of_norm_deriv_right_le (f := Y) (f' := Y')
        (δ := δ) (K := K0) (ε := 0) (a := 0) (b := τ) hYcont hderw hY0 hbndw
      simpa using hres u hu
    have hu' : -u ∈ Icc 0 τ := ⟨by linarith [hu.2, hτ], by linarith [hu.1, hτ]⟩
    have hb' := hYmain (-u) hu'
    change ‖X (-(-u))‖ ≤ gronwallBound δ K0 0 (-u) at hb'
    simpa using le_trans hb' (htoe (-u) (by linarith [hu.2, hτ]) (by linarith [hu.1, hτ]))
  intro t ht
  by_cases ht0 : 0 ≤ t
  · exact hpos t ⟨ht0, ht.2⟩
  · exact hneg t ⟨ht.1, le_of_not_ge ht0⟩

/-- Bounding the growth of a solution of the linearized equation. -/
lemma lin_sol_norm_bound (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) {z : ℝ → E × E} {J : ℝ → E × E} {w : E × E}
    {τ K0 : ℝ} (hτ : 0 < τ) (hK0 : 0 ≤ K0) (hw : ‖w‖ ≤ 1)
    (hJ : J 0 = w ∧ ∀ s ∈ Icc (-τ) τ,
        HasDerivAt J ((fderiv ℝ (odeField g)) (z s) (J s)) s)
    (hK : ∀ s ∈ Icc (-τ) τ, ‖fderiv ℝ (odeField g) (z s)‖ ≤ K0) :
    ∀ t ∈ Icc (-τ) τ, ‖J t‖ ≤ Real.exp (K0 * τ) := by
  have hX0 : ‖J 0‖ ≤ 1 := by
    rw [hJ.1]
    simpa using hw
  have hb (s : ℝ) (hs : s ∈ Icc (-τ) τ) :
      ‖(fderiv ℝ (odeField g)) (z s) (J s)‖ ≤ K0 * ‖J s‖ := by
    exact ((fderiv ℝ (odeField g)) (z s)).le_opNorm (J s) |>.trans
      (mul_le_mul_of_nonneg_right (hK s hs) (norm_nonneg (J s)))
  have hb' := growth_bound_raw (F := E × E) (X := J)
    (X' := fun s => (fderiv ℝ (odeField g)) (z s) (J s)) (τ := τ) (K0 := K0) (δ := 1)
    hτ hK0 zero_le_one hX0 hJ.2 hb
  intro t ht
  have hres := hb' t ht
  simpa using hres

/-- Gronwall bound for the difference of two linearized solutions along nearby base curves. -/
lemma lin_sol_diff_bound (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) {z₁ z₂ : ℝ → E × E} {J₁ J₂ : ℝ → E × E} {w : E × E}
    {τ K0 ε : ℝ} (hτ : 0 < τ) (hK0 : 0 ≤ K0) (hε0 : 0 ≤ ε) (hw : ‖w‖ ≤ 1)
    (hJ₁ : J₁ 0 = w ∧ ∀ s ∈ Icc (-τ) τ,
        HasDerivAt J₁ ((fderiv ℝ (odeField g)) (z₁ s) (J₁ s)) s)
    (hJ₂ : J₂ 0 = w ∧ ∀ s ∈ Icc (-τ) τ,
        HasDerivAt J₂ ((fderiv ℝ (odeField g)) (z₂ s) (J₂ s)) s)
    (hK₁ : ∀ s ∈ Icc (-τ) τ, ‖fderiv ℝ (odeField g) (z₁ s)‖ ≤ K0)
    (hK₂ : ∀ s ∈ Icc (-τ) τ, ‖fderiv ℝ (odeField g) (z₂ s)‖ ≤ K0)
    (hdiff : ∀ s ∈ Icc (-τ) τ,
      ‖fderiv ℝ (odeField g) (z₁ s) - fderiv ℝ (odeField g) (z₂ s)‖ ≤ ε) :
    ∀ t ∈ Icc (-τ) τ, ‖J₁ t - J₂ t‖ ≤ gronwallBound 0 K0 (ε * Real.exp (K0 * τ)) τ := by
  intro t ht
  let D : ℝ → E × E := J₁ - J₂
  let εf : ℝ := ε * Real.exp (K0 * τ)
  have hεf0 : 0 ≤ εf := by
    dsimp [εf]
    exact mul_nonneg hε0 (Real.exp_nonneg (K0 * τ))
  have hD0 : D 0 = 0 := by
    simp [D, hJ₁.1, hJ₂.1]
  have hJ2bnd : ∀ s ∈ Icc (-τ) τ, ‖J₂ s‖ ≤ Real.exp (K0 * τ) :=
    lin_sol_norm_bound g hg hinv (z := z₂) (J := J₂) (w := w) hτ hK0 hw hJ₂ hK₂
  have hper (x : ℝ) (hx : x ∈ Icc (-τ) τ) :
      ∃ gx : E × E, HasDerivAt D gx x ∧ ‖gx‖ ≤ K0 * ‖D x‖ + εf := by
    let A₁ : E × E →L[ℝ] E × E := fderiv ℝ (odeField g) (z₁ x)
    let A₂ : E × E →L[ℝ] E × E := fderiv ℝ (odeField g) (z₂ x)
    have hd1 : HasDerivAt J₁ (A₁ (J₁ x)) x := by
      have h := hJ₁.2 x hx
      simpa [A₁] using h
    have hd2 : HasDerivAt J₂ (A₂ (J₂ x)) x := by
      have h := hJ₂.2 x hx
      simpa [A₂] using h
    have hdD : HasDerivAt D (A₁ (J₁ x) - A₂ (J₂ x)) x := by
      simpa [D] using hd1.sub hd2
    have hdecomp : A₁ (J₁ x) - A₂ (J₂ x) = A₁ (D x) + ((A₁ - A₂) (J₂ x)) := by
      have hlin : A₁ (J₁ x) - A₁ (J₂ x) = A₁ ((J₁ - J₂) x) := by
        simp [map_sub]
      have hforce : A₁ (J₂ x) - A₂ (J₂ x) = (A₁ - A₂) (J₂ x) := by
        change A₁ (J₂ x) - A₂ (J₂ x) = A₁ (J₂ x) - A₂ (J₂ x)
        rfl
      calc
        A₁ (J₁ x) - A₂ (J₂ x) = (A₁ (J₁ x) - A₁ (J₂ x)) + (A₁ (J₂ x) - A₂ (J₂ x)) := by abel
        _ = A₁ ((J₁ - J₂) x) + ((A₁ - A₂) (J₂ x)) := by rw [hlin, hforce]
        _ = A₁ (D x) + ((A₁ - A₂) (J₂ x)) := by rfl
    have hD' : HasDerivAt D (A₁ (D x) + ((A₁ - A₂) (J₂ x))) x := hdD.congr_deriv hdecomp
    have hK₁x : ‖A₁‖ ≤ K0 := by simpa [A₁] using hK₁ x hx
    have hb1 : ‖A₁ (D x)‖ ≤ K0 * ‖D x‖ := by
      calc
        ‖A₁ (D x)‖ ≤ ‖A₁‖ * ‖D x‖ := A₁.le_opNorm (D x)
        _ ≤ K0 * ‖D x‖ := mul_le_mul_of_nonneg_right hK₁x (norm_nonneg (D x))
    have hbJ2 : ‖J₂ x‖ ≤ Real.exp (K0 * τ) := hJ2bnd x hx
    have hbforce : ‖(A₁ - A₂) (J₂ x)‖ ≤ εf := by
      have h₁ : ‖(A₁ - A₂) (J₂ x)‖ ≤ ‖A₁ - A₂‖ * ‖J₂ x‖ := (A₁ - A₂).le_opNorm (J₂ x)
      have h₂ : ‖A₁ - A₂‖ ≤ ε := by simpa [A₁, A₂] using hdiff x hx
      have h₄ : ‖A₁ - A₂‖ * ‖J₂ x‖ ≤ ε * Real.exp (K0 * τ) :=
        mul_le_mul h₂ hbJ2 (norm_nonneg (J₂ x)) hε0
      have h₅ : ε * Real.exp (K0 * τ) ≤ εf := by simp [εf]
      exact le_trans (le_trans h₁ h₄) h₅
    refine ⟨A₁ (D x) + ((A₁ - A₂) (J₂ x)), hD', ?_⟩
    calc
      ‖A₁ (D x) + ((A₁ - A₂) (J₂ x))‖ ≤ ‖A₁ (D x)‖ + ‖(A₁ - A₂) (J₂ x)‖ := norm_add_le _ _
      _ ≤ K0 * ‖D x‖ + εf := add_le_add hb1 hbforce
  let fp : ℝ → E × E := fun x => if hx : x ∈ Icc (-τ) τ then (hper x hx).choose else 0
  have hfp (x : ℝ) (hx : x ∈ Ico 0 τ) : HasDerivAt D (fp x) x ∧ ‖fp x‖ ≤ K0 * ‖D x‖ + εf := by
    have hxI : x ∈ Icc (-τ) τ := ⟨by linarith [hx.1, hτ], by linarith [hx.2, hτ]⟩
    rw [show fp x = (hper x hxI).choose by
      unfold fp
      rw [dif_pos hxI]]
    exact (hper x hxI).choose_spec
  have hDcont : ContinuousOn D (Icc 0 τ) := by
    intro x hx
    have hxI : x ∈ Icc (-τ) τ := ⟨by linarith [hx.1, hτ], by linarith [hx.2, hτ]⟩
    exact (hper x hxI).choose_spec.1.continuousAt.continuousWithinAt
  have hpos (u : ℝ) (hu : u ∈ Icc 0 τ) : ‖D u‖ ≤ gronwallBound 0 K0 εf u := by
    have hderw : ∀ x ∈ Ico 0 τ, HasDerivWithinAt D (fp x) (Ici x) x := by
      intro x hx
      exact (hfp x hx).1.hasDerivWithinAt
    have hbndw : ∀ x ∈ Ico 0 τ, ‖fp x‖ ≤ K0 * ‖D x‖ + εf := by
      intro x hx
      exact (hfp x hx).2
    have hres := norm_le_gronwallBound_of_norm_deriv_right_le (f := D) (f' := fp)
      (δ := 0) (K := K0) (ε := εf) (a := 0) (b := τ)
      hDcont hderw (by rw [hD0]; simp) hbndw
    simpa using hres u hu
  have hEpIcc (s : ℝ) (hs : s ∈ Icc 0 τ) :
      ∃ gx : E × E, HasDerivAt (fun r => D (-r)) gx s ∧ ‖gx‖ ≤ K0 * ‖(fun r => D (-r)) s‖ + εf := by
    have hxI : -s ∈ Icc (-τ) τ := ⟨by linarith [hs.2, hτ], by linarith [hs.1, hτ]⟩
    rcases hper (-s) hxI with ⟨gx, hder, hbnd⟩
    refine ⟨-(gx), ?_, ?_⟩
    · have hnegd : HasDerivAt (fun r : ℝ => -r) (-1 : ℝ) s := hasDerivAt_neg s
      change HasDerivAt (D ∘ Neg.neg) (-(gx)) s
      simpa using hder.scomp s hnegd
    · simpa [norm_neg] using hbnd
  let gp : ℝ → E × E := fun s => if hs : s ∈ Icc 0 τ then (hEpIcc s hs).choose else 0
  have hgp (s : ℝ) (hs : s ∈ Ico 0 τ) :
      HasDerivAt (fun r => D (-r)) (gp s) s ∧ ‖gp s‖ ≤ K0 * ‖(fun r => D (-r)) s‖ + εf := by
    have hsI : s ∈ Icc 0 τ := ⟨hs.1, le_of_lt hs.2⟩
    rw [show gp s = (hEpIcc s hsI).choose by
      unfold gp
      rw [dif_pos hsI]]
    exact (hEpIcc s hsI).choose_spec
  have hEcont : ContinuousOn (fun r => D (-r)) (Icc 0 τ) := by
    intro s hs
    exact (hEpIcc s hs).choose_spec.1.continuousAt.continuousWithinAt
  have hneg (u : ℝ) (hu : u ∈ Icc (-τ) 0) : ‖D u‖ ≤ gronwallBound 0 K0 εf (-u) := by
    have hb1 : ∀ s ∈ Ico 0 τ, HasDerivWithinAt (fun r => D (-r)) (gp s) (Ici s) s := by
      intro s hs
      exact (hgp s hs).1.hasDerivWithinAt
    have hb2 : ∀ s ∈ Ico 0 τ, ‖gp s‖ ≤ K0 * ‖(fun r => D (-r)) s‖ + εf := by
      intro s hs
      exact (hgp s hs).2
    have hres := norm_le_gronwallBound_of_norm_deriv_right_le
      (f := (fun r => D (-r))) (f' := gp) (δ := 0) (K := K0) (ε := εf) (a := 0) (b := τ)
      hEcont hb1 (by simp [hD0]) hb2
    have huI : -u ∈ Icc 0 τ := ⟨by linarith [hu.2, hτ], by linarith [hu.1, hτ]⟩
    have hb := hres (-u) huI
    simpa using hb
  have hDfin (u : ℝ) (hu : u ∈ Icc (-τ) τ) : ‖D u‖ ≤ gronwallBound 0 K0 εf τ := by
    have hm : Monotone (gronwallBound 0 K0 εf) := gronwallBound_mono (by norm_num) hεf0 hK0
    by_cases hu0 : 0 ≤ u
    · have hb := hpos u ⟨hu0, hu.2⟩
      exact le_trans (le_trans hb (hm hu.2)) (le_rfl)
    · have hb := hneg u ⟨hu.1, le_of_not_ge hu0⟩
      have hmt : -u ≤ τ := by linarith [hu.1, hτ]
      exact le_trans (le_trans hb (hm hmt)) (le_rfl)
  have hb := hDfin t ht
  change ‖D t‖ ≤ gronwallBound 0 K0 (ε * Real.exp (K0 * τ)) τ
  simpa [εf] using hb

/-- nonnegativity of the Gronwall bound -/
lemma gronwallBound_nonneg_of (δ K ε x : ℝ) (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hε : 0 ≤ ε) (hx : 0 ≤ x) : 0 ≤ gronwallBound δ K ε x := by
  by_cases hK0 : K = 0
  · rw [hK0]
    simp [gronwallBound]
    nlinarith
  · rw [gronwallBound_of_K_ne_0 hK0]
    have hE1 : 0 ≤ Real.exp (K * x) - 1 := by
      have h1 : 1 ≤ Real.exp (K * x) := by
        rw [← Real.exp_zero]
        exact Real.exp_monotone (by nlinarith)
      linarith
    have hKpos : 0 < K := lt_of_le_of_ne hK (Ne.symm hK0)
    have h2 : 0 ≤ ε / K * (Real.exp (K * x) - 1) := by
      exact mul_nonneg (div_nonneg hε (le_of_lt hKpos)) hE1
    have h1' : 0 ≤ δ * Real.exp (K * x) := mul_nonneg hδ (Real.exp_nonneg _)
    nlinarith

/-- ContDiffOn `1` implies the fderiv map is continuous (open set, generic source). -/
lemma contDiffOn_one_cont_fderiv {E₀ F : Type*} [NormedAddCommGroup E₀] [NormedSpace ℝ E₀]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E₀ → F} {s : Set E₀} (hs : IsOpen s) (h : ContDiffOn ℝ 1 f s) :
    ContinuousOn (fun y : E₀ => fderiv ℝ f y) s := by
  simpa using h.continuousOn_fderiv_of_isOpen hs (by norm_num : (1 : ℕ∞ω) ≤ 1)

/-- The derivative of the data-map is continuous on a ball around `z₀`, uniformly in time on a
window. -/
lemma flow_fderiv_contOn (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (z₀ : E × E) (Tf : ℝ) (hTf : 0 < Tf)
    (Lf : NNReal) (Φ : E × E → ℝ → E × E)
    (hΦ₀ : ∀ z ∈ closedBall z₀ 1, Φ z 0 = z ∧
       (∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
       (∀ t : ℝ, Φ z t ∈ closedBall z₀ 2))
    (hLip : ∀ t ∈ Icc (-Tf) Tf, LipschitzOnWith Lf (fun z => Φ z t) (closedBall z₀ 1))
    {K0 : ℝ} (hK0 : 0 ≤ K0)
    (hK : ∀ p ∈ closedBall z₀ 2, ‖fderiv ℝ (odeField g) p‖ ≤ K0)
    {τ δ : ℝ} (hτ : 0 < τ) (hτTf : 4 * τ ≤ Tf) (hδ0 : 0 < δ) (hδ14 : δ ≤ 1 / 4)
    (hUb : ∀ i : Fin (finrank ℝ (E × E)),
      4 * (K0 + 1) * (‖(finBasis ℝ (E × E)) i‖ + 1) * τ ≤ 1) :
    ∀ t ∈ Icc (-τ) τ,
      ContinuousOn (fun z : E × E => fderiv ℝ (fun w => Φ w t) z) (ball z₀ δ) := by
  classical
  intro t ht
  have hτ2 : 2 * τ ≤ Tf / 2 := by nlinarith [hτTf, hTf]
  have hτTf2 : τ ≤ Tf / 2 := by nlinarith [hτTf, hTf]
  have hUb2 : ∀ i : Fin (finrank ℝ (E × E)),
      2 * (K0 + 1) * (‖(finBasis ℝ (E × E)) i‖ + 1) * (2 * τ) ≤ 1 := by
    intro i
    have h := hUb i
    convert h using 1
    ring
  have hbp := flow_fderiv_ballpoint g hg hinv z₀ Tf hTf Lf Φ hΦ₀ hLip hK0 hK
    (δ := (1 / 4 : ℝ)) (by norm_num : 0 < (1 / 4 : ℝ)) (by norm_num : (1 / 4 : ℝ) ≤ 1 / 2)
    (U := 2 * τ) (by positivity : 0 < 2 * τ) hτ2 hUb2
  let A : E × E → (E × E) →L[ℝ] (E × E) := fun p => fderiv ℝ (odeField g) p
  have hAcont : Continuous A := by
    rw [continuous_iff_continuousAt]
    intro p
    exact (odeField_contDiffAt g hg hinv p.1 p.2).continuousAt_fderiv (by norm_num)
  have hAuc : UniformContinuousOn A (closedBall z₀ 2) :=
    IsCompact.uniformContinuousOn_of_continuous (isCompact_closedBall z₀ 2) hAcont.continuousOn
  have hTfIcc : Icc (-τ) τ ⊆ Icc (-Tf) Tf := by
    intro s hs
    constructor <;> nlinarith [hs.1, hs.2, hτTf, hτ, hTf]
  have hball14 : ball z₀ δ ⊆ ball z₀ (1 / 4 : ℝ) := ball_subset_ball (by linarith)
  rw [Metric.continuousOn_iff]
  intro zbar0 hz0 ε hε
  rcases Metric.continuousAt_iff.mp (gronwallBound_continuous_ε 0 K0 τ).continuousAt ε hε with
    ⟨c₀, hc₀, hc₀bd⟩
  let εA : ℝ := c₀ / (2 * (Real.exp (K0 * τ) + 1))
  have hεA0 : 0 < εA := by
    dsimp [εA]
    positivity
  have hεAe : εA * Real.exp (K0 * τ) < c₀ := by
    dsimp [εA]
    have hpos : 0 < 2 * (Real.exp (K0 * τ) + 1) := by
      nlinarith [Real.exp_nonneg (K0 * τ)]
    have hle : (Real.exp (K0 * τ)) / (2 * (Real.exp (K0 * τ) + 1)) < 1 := by
      rw [div_lt_one hpos]
      nlinarith [Real.exp_nonneg (K0 * τ)]
    calc
      (c₀ / (2 * (Real.exp (K0 * τ) + 1))) * Real.exp (K0 * τ)
          = c₀ * (Real.exp (K0 * τ) / (2 * (Real.exp (K0 * τ) + 1))) := by
            field_simp [hpos.ne']
      _ < c₀ * 1 := mul_lt_mul_of_pos_left hle hc₀
      _ = c₀ := by ring
  rcases (Metric.uniformContinuousOn_iff_le.mp hAuc) εA hεA0 with ⟨δuc, hδuc0, hδuc⟩
  let ρ : ℝ := min (δuc / ((Lf : ℝ) + 1)) (1 / 2)
  have hρ0 : 0 < ρ := by
    dsimp [ρ]
    have hden : 0 < (Lf : ℝ) + 1 := by positivity
    exact lt_min (div_pos hδuc0 hden) (by norm_num)
  have hz0c1 : zbar0 ∈ closedBall z₀ 1 := by
    have hlt : ‖zbar0 - z₀‖ < δ := by simpa [dist_eq_norm] using (mem_ball.mp hz0)
    have hle1 : ‖zbar0 - z₀‖ ≤ 1 := by linarith [hδ14]
    simpa [dist_eq_norm] using hle1
  refine ⟨ρ, hρ0, ?_⟩
  intro zbar hzball hzρ
  have hltρ : ‖zbar - zbar0‖ < ρ := by simpa [dist_eq_norm] using hzρ
  have hz0lt : ‖zbar0 - z₀‖ < δ := by simpa [dist_eq_norm] using (mem_ball.mp hz0)
  have hzc1 : zbar ∈ closedBall z₀ 1 := by
    have hd : ‖zbar - z₀‖ = ‖(zbar - zbar0) + (zbar0 - z₀)‖ := by abel
    have hle1 : ‖zbar - z₀‖ ≤ 1 := by
      calc
        ‖zbar - z₀‖ = ‖(zbar - zbar0) + (zbar0 - z₀)‖ := hd
        _ ≤ ‖zbar - zbar0‖ + ‖zbar0 - z₀‖ := norm_add_le _ _
        _ ≤ ρ + δ := by
          have h1 : ‖zbar - zbar0‖ ≤ ρ := le_of_lt hltρ
          have h2 : ‖zbar0 - z₀‖ ≤ δ := le_of_lt hz0lt
          linarith
        _ ≤ 1 := by
          have hρ12 : ρ ≤ 1 / 2 := by dsimp [ρ]; exact min_le_right _ _
          nlinarith [hδ14]
    simpa [dist_eq_norm] using hle1
  have hzbar_14 : zbar ∈ ball z₀ (1 / 4 : ℝ) := hball14 hzball
  have hz0_14 : zbar0 ∈ ball z₀ (1 / 4 : ℝ) := hball14 hz0
  have ht2 : t ∈ Icc (-(2 * τ / 2)) (2 * τ / 2) := by
    constructor <;> nlinarith [ht.1, ht.2]
  rcases hbp zbar hzbar_14 t ht2 with
    ⟨J₁, hJ₁0, hJ₁d, hJ₁add, hJ₁smul, L₁, hL₁fd, hL₁val⟩
  rcases hbp zbar0 hz0_14 t ht2 with
    ⟨J₀, hJ₀c0, hJ₀d, hJ₀add, hJ₀smul, L₀, hL₀fd, hL₀val⟩
  have hFzbar : fderiv ℝ (fun w => Φ w t) zbar = L₁ := hL₁fd.fderiv
  have hFzbar0 : fderiv ℝ (fun w => Φ w t) zbar0 = L₀ := hL₀fd.fderiv
  let G : ℝ := gronwallBound 0 K0 (εA * Real.exp (K0 * τ)) τ
  have hG0 : 0 ≤ G := by
    dsimp [G]
    exact gronwallBound_nonneg_of 0 K0 (εA * Real.exp (K0 * τ)) τ (by norm_num) hK0
      (mul_nonneg (le_of_lt hεA0) (Real.exp_nonneg _)) (le_of_lt hτ)
  have hGε : G < ε := by
    have hx0 : 0 ≤ εA * Real.exp (K0 * τ) := mul_nonneg (le_of_lt hεA0) (Real.exp_nonneg _)
    have hd : dist (εA * Real.exp (K0 * τ)) 0 < c₀ := by
      rw [Real.dist_eq]
      rw [sub_zero]
      rw [abs_of_nonneg hx0]
      exact hεAe
    have hb := hc₀bd hd
    have hz : gronwallBound 0 K0 0 τ = 0 := by simpa using gronwallBound_ε0_δ0 K0 τ
    have hb' : |gronwallBound 0 K0 (εA * Real.exp (K0 * τ)) τ - gronwallBound 0 K0 0 τ| < ε := by
      simpa [Real.dist_eq] using hb
    rw [hz] at hb'
    have hb'' : |G| < ε := by simpa [G] using hb'
    exact (abs_lt.mp hb'').2
  have hunit (w : E × E) (hw : ‖w‖ ≤ 1) : ‖L₁ w - L₀ w‖ ≤ G := by
    have hsup (s : ℝ) (hs : s ∈ Icc (-τ) τ) :
        ‖fderiv ℝ (odeField g) (Φ zbar s) - fderiv ℝ (odeField g) (Φ zbar0 s)‖ ≤ εA := by
      have hLipS : LipschitzOnWith Lf (fun z => Φ z s) (closedBall z₀ 1) := hLip s (hTfIcc hs)
      have hd1 : dist (Φ zbar s) (Φ zbar0 s) ≤ (Lf : ℝ) * dist zbar zbar0 :=
        hLipS.dist_le_mul zbar hzc1 zbar0 hz0c1
      have hLfδ : (Lf : ℝ) * ‖zbar - zbar0‖ ≤ δuc := by
        have hρle : ρ ≤ δuc / ((Lf : ℝ) + 1) := by dsimp [ρ]; exact min_le_left _ _
        have hden : 0 < (Lf : ℝ) + 1 := by positivity
        have hle2 : (Lf : ℝ) * ρ ≤ δuc := by
          calc
            (Lf : ℝ) * ρ ≤ (Lf : ℝ) * (δuc / ((Lf : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_left hρle (Lf : NNReal).2
            _ ≤ δuc := by
              have hdiv : (Lf : ℝ) * (δuc / ((Lf : ℝ) + 1)) = ((Lf : ℝ) * δuc) / ((Lf : ℝ) + 1) := by
                field_simp [hden.ne']
              rw [hdiv]
              rw [div_le_iff₀ hden]
              nlinarith [(Lf : NNReal).2]
        have hlt1 : (Lf : ℝ) * ‖zbar - zbar0‖ ≤ (Lf : ℝ) * ρ :=
          mul_le_mul_of_nonneg_left (le_of_lt hltρ) (Lf : NNReal).2
        exact le_trans hlt1 hle2
      have hd1' : dist (Φ zbar s) (Φ zbar0 s) ≤ δuc := by
        calc
          dist (Φ zbar s) (Φ zbar0 s) ≤ (Lf : ℝ) * dist zbar zbar0 := hd1
          _ = (Lf : ℝ) * ‖zbar - zbar0‖ := by rw [dist_eq_norm]
          _ ≤ δuc := hLfδ
      have hc2 : Φ zbar s ∈ closedBall z₀ 2 := (hΦ₀ zbar hzc1).2.2 s
      have hc0 : Φ zbar0 s ∈ closedBall z₀ 2 := (hΦ₀ zbar0 hz0c1).2.2 s
      have hb := hδuc (Φ zbar s) hc2 (Φ zbar0 s) hc0 hd1'
      simpa [A, dist_eq_norm] using hb
    have hJ₁w : J₁ w 0 = w ∧ ∀ s ∈ Icc (-τ) τ,
        HasDerivAt (J₁ w) ((fderiv ℝ (odeField g)) (Φ zbar s) (J₁ w s)) s := by
      constructor
      · exact hJ₁0 w
      · intro s hs
        have hsU : s ∈ Ioo (-(2 * τ)) (2 * τ) := by
          constructor <;> nlinarith [hs.1, hs.2, hτ]
        exact hJ₁d w s hsU
    have hJ₀w : J₀ w 0 = w ∧ ∀ s ∈ Icc (-τ) τ,
        HasDerivAt (J₀ w) ((fderiv ℝ (odeField g)) (Φ zbar0 s) (J₀ w s)) s := by
      constructor
      · exact hJ₀c0 w
      · intro s hs
        have hsU : s ∈ Ioo (-(2 * τ)) (2 * τ) := by
          constructor <;> nlinarith [hs.1, hs.2, hτ]
        exact hJ₀d w s hsU
    have hK₁' (s : ℝ) (hs : s ∈ Icc (-τ) τ) :
        ‖fderiv ℝ (odeField g) (Φ zbar s)‖ ≤ K0 := by
      exact hK (Φ zbar s) ((hΦ₀ zbar hzc1).2.2 s)
    have hK₀' (s : ℝ) (hs : s ∈ Icc (-τ) τ) :
        ‖fderiv ℝ (odeField g) (Φ zbar0 s)‖ ≤ K0 := by
      exact hK (Φ zbar0 s) ((hΦ₀ zbar0 hz0c1).2.2 s)
    have hbd := lin_sol_diff_bound g hg hinv (z₁ := fun s => Φ zbar s) (z₂ := fun s => Φ zbar0 s)
      (J₁ := J₁ w) (J₂ := J₀ w) (w := w) hτ hK0 (le_of_lt hεA0) hw hJ₁w hJ₀w hK₁' hK₀' hsup
    have hres := hbd t ht
    have hval1 : L₁ w = J₁ w t := hL₁val w
    have hval0 : L₀ w = J₀ w t := hL₀val w
    exact (by simpa [G, hval1, hval0] using hres)
  have hop : ‖L₁ - L₀‖ ≤ G := by
    rw [ContinuousLinearMap.opNorm_le_iff hG0]
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · have hnxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx
      let w : E × E := (‖x‖⁻¹ : ℝ) • x
      have hw1 : ‖w‖ ≤ 1 := by
        dsimp [w]
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (le_of_lt hnxpos),
          inv_mul_cancel₀ (ne_of_gt hnxpos)]
      have hb := hunit w hw1
      have hlin : (L₁ - L₀) x = (‖x‖ : ℝ) • ((L₁ - L₀) w) := by
        dsimp [w]
        rw [← map_smul (L₁ - L₀) (‖x‖) ((‖x‖⁻¹ : ℝ) • x)]
        congr 1
        rw [smul_smul]
        have hmul : (‖x‖ : ℝ) * (‖x‖⁻¹ : ℝ) = 1 := by
          field_simp [ne_of_gt hnxpos]
        rw [hmul, one_smul]
      calc
        ‖(L₁ - L₀) x‖ = ‖(‖x‖ : ℝ) • ((L₁ - L₀) w)‖ := by rw [hlin]
        _ = ‖x‖ * ‖(L₁ - L₀) w‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hnxpos)]
        _ ≤ ‖x‖ * G := mul_le_mul_of_nonneg_left hb (le_of_lt hnxpos)
        _ = G * ‖x‖ := by ring
  calc
    dist (fderiv ℝ (fun w => Φ w t) zbar) (fderiv ℝ (fun w => Φ w t) zbar0)
        = ‖fderiv ℝ (fun w => Φ w t) zbar - fderiv ℝ (fun w => Φ w t) zbar0‖ := by
          rw [dist_eq_norm]
    _ = ‖L₁ - L₀‖ := by rw [hFzbar, hFzbar0]
    _ ≤ G := hop
    _ < ε := hGε

/-- ContDiffOn `1` from differentiability and continuity of the fderiv-within. -/
lemma contDiffOn_one_of (g0 : E × E → E × E) (s : Set (E × E)) (h1 : DifferentiableOn ℝ g0 s)
    (h2 : ContinuousOn (fun y => fderivWithin ℝ g0 s y) s) : ContDiffOn ℝ 1 g0 s := by
  apply contDiffOn_succ_of_fderivWithin (n := 0) h1
  · intro h
    norm_num at h
  · simpa [contDiffOn_zero] using h2

/-- ContDiffOn of `ContDiffOn 1` data-map restricts under composition with the first projection. -/
lemma contDiffOn_one_fst_comp {f : E × E → E × E} (s : Set (E × E))
    (h : ContDiffOn ℝ 1 f s) : ContDiffOn ℝ 1 (fun z : E × E => (f z).1) s := by
  have hfst : ContDiffOn ℝ 1 (fun w : E × E => w.1) univ := by
    have hc : ContDiff ℝ 1 (fun w : E × E => w.1) := by
      exact ContinuousLinearMap.contDiff (ContinuousLinearMap.fst ℝ E E)
    exact hc.contDiffOn
  have hmap : Set.MapsTo f s univ := by intro z hz; trivial
  simpa [Function.comp_def] using (ContDiffOn.comp hfst h hmap)

/-- ContDiffOn of the affine data map -/
lemma contDiffOn_data_affine (x₀ : E) (τ ρ : ℝ) :
    ContDiffOn ℝ 1 (fun v : E => (x₀, (1 / τ) • v)) (ball 0 ρ) := by
  have hconst : ContDiffOn ℝ 1 (fun v : E => x₀) (ball 0 ρ) := contDiff_const.contDiffOn
  have hlin : ContDiffOn ℝ 1 (fun v : E => (1 / τ) • v) (ball 0 ρ) := by
    have h : ContDiff ℝ 1 (fun v : E => (1 / τ) • v) := by
      exact (((1 / τ) • (ContinuousLinearMap.id ℝ E)) : E →L[ℝ] E).contDiff
    exact h.contDiffOn
  exact ContDiffOn.prodMk hconst hlin

/-- membership of (x₀, u) in the radius-one data ball -/
lemma mem_data_ball (x₀ : E) (u : E) (hu : ‖u‖ ≤ 1) : (x₀, u) ∈ closedBall (x₀, (0 : E)) 1 := by
  rw [mem_closedBall, dist_eq_norm]
  have h : ‖(x₀, u) - (x₀, (0 : E))‖ = ‖u‖ := by simp
  rw [h]
  exact hu

/-- the base point is at rest under the flow -/
lemma rest_point_fixed (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) {τ : ℝ} (hτ : 0 < τ)
    (Φc : E × E → ℝ → E × E)
    (hΦc : ∀ z ∈ closedBall (x₀, (0 : E)) 1, Φc z 0 = z ∧
       ∀ t ∈ Icc (-τ) τ, HasDerivAt (Φc z) (odeField g (Φc z t)) t)
    {s : ℝ} (hs : s ∈ Ioo (-τ) τ) :
    Φc (x₀, 0) s = (x₀, 0) := by
  have hfr := flow_rest_point g hg hinv hτ (x₀ := x₀) (Φ := Φc) hΦc
  exact hfr s hs

/-- Scaling identity for the flow exponential: exp(t • w) = flow(x₀, w)(t). -/
lemma exp_ray_scaling (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) {T : ℝ} (hT : 0 < T)
    (Φc : E × E → ℝ → E × E)
    (hΦc : ∀ z ∈ closedBall (x₀, (0 : E)) 1, Φc z 0 = z ∧
       ∀ s ∈ Icc (-T) T, HasDerivAt (Φc z) (odeField g (Φc z s)) s)
    (w : E) (hw : ‖w‖ ≤ 1) {a : ℝ} (ha : |a| ≤ 1) (ha0 : a ≠ 0)
    {t : ℝ} (ht : t ∈ Ioo (-T) T) :
    (Φc (x₀, a • w) t).1 = (Φc (x₀, w) (a * t)).1 := by
  have hz1 : (x₀, w) ∈ closedBall (x₀, 0) 1 := mem_data_ball x₀ w hw
  have haw : ‖a • w‖ ≤ 1 := by
    rw [norm_smul, Real.norm_eq_abs]
    have hle : |a| * ‖w‖ ≤ 1 * 1 := by
      exact mul_le_mul ha hw (norm_nonneg w) (by norm_num)
    simpa using hle
  have hz2 : (x₀, a • w) ∈ closedBall (x₀, 0) 1 := mem_data_ball x₀ (a • w) haw
  have hsplit1 := split_flow_geodesic g hg hinv (x₀, 0) hT (closedBall (x₀, 0) 1) Φc
    (fun z hz => ⟨(hΦc z hz).1, (hΦc z hz).2⟩) (z := (x₀, w)) hz1
  have hsplit2 := split_flow_geodesic g hg hinv (x₀, 0) hT (closedBall (x₀, 0) 1) Φc
    (fun z hz => ⟨(hΦc z hz).1, (hΦc z hz).2⟩) (z := (x₀, a • w)) hz2
  let c₁ : ℝ → E := fun u => (Φc (x₀, w) u).1
  let vel₁ : ℝ → E := fun u => (Φc (x₀, w) u).2
  let c₂ : ℝ → E := fun u => (Φc (x₀, a • w) u).1
  let vel₂ : ℝ → E := fun u => (Φc (x₀, a • w) u).2
  have hc₁ (s : ℝ) (hs : s ∈ Ioo (-T) T) : HasDerivAt c₁ (vel₁ s) s := by
    simpa [c₁, vel₁] using hsplit1.1 s hs
  have hv₁ (s : ℝ) (hs : s ∈ Ioo (-T) T) :
      HasDerivAt vel₁ (accel (g (c₁ s)) (fderiv ℝ g (c₁ s)) (vel₁ s)) s := by
    simpa [c₁, vel₁] using hsplit1.2 s hs
  have hc₂ (s : ℝ) (hs : s ∈ Ioo (-T) T) : HasDerivAt c₂ (vel₂ s) s := by
    simpa [c₂, vel₂] using hsplit2.1 s hs
  have hv₂ (s : ℝ) (hs : s ∈ Ioo (-T) T) :
      HasDerivAt vel₂ (accel (g (c₂ s)) (fderiv ℝ g (c₂ s)) (vel₂ s)) s := by
    simpa [c₂, vel₂] using hsplit2.2 s hs
  have hc₁0 : c₁ 0 = x₀ := by
    simpa [c₁] using (congrArg Prod.fst (hΦc (x₀, w) hz1).1)
  have hv₁0 : vel₁ 0 = w := by
    simpa [vel₁] using (congrArg Prod.snd (hΦc (x₀, w) hz1).1)
  have hc₂0 : c₂ 0 = x₀ := by
    simpa [c₂] using (congrArg Prod.fst (hΦc (x₀, a • w) hz2).1)
  have hv₂0 : vel₂ 0 = a • w := by
    simpa [vel₂] using (congrArg Prod.snd (hΦc (x₀, a • w) hz2).1)
  have hscaling := flow_scaling (g := g) (hg := hg) (hinv := hinv) (ε₁ := T) (ε₂ := T)
    (hε₁ := hT) (hε₂ := hT) (c₁ := c₁) (vel₁ := vel₁) (c₂ := c₂) (vel₂ := vel₂)
    (x := x₀) (v := w) (s := a) (hs := ha0)
    (hc₁ := hc₁0) (hv₁ := hv₁0) (hc₂ := hc₂0) (hv₂ := hv₂0)
    (hc₁d := hc₁) (hv₁d := hv₁) (hc₂d := hc₂) (hv₂d := hv₂)
  have hAbs : 0 < |a| := abs_pos.mpr ha0
  have hle : T ≤ T / |a| := by
    rw [le_div_iff₀ hAbs]
    nlinarith [ha, hT]
  have hmin : min T (T / |a|) = T := min_eq_left hle
  have ht' : t ∈ Ioo (-min T (T / |a|)) (min T (T / |a|)) := by
    constructor
    · rw [hmin]
      exact ht.1
    · rw [hmin]
      exact ht.2
  have hsc := hscaling t ht'
  have hmain : c₂ t = c₁ (a * t) := hsc.1
  calc
    (Φc (x₀, a • w) t).1 = c₂ t := by rfl
    _ = c₁ (a * t) := hmain
    _ = (Φc (x₀, w) (a * t)).1 := by rfl

/-- the derivative of the flow-exponential at zero is the identity -/
lemma exp_fderiv_zero_id (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (x₀ : E) {T0 τ : ℝ} (hT0 : 0 < T0) (hτ : 0 < τ)
    (hτT0 : τ < T0)
    (Φc : E × E → ℝ → E × E)
    (hΦc : ∀ z ∈ closedBall (x₀, (0 : E)) 1, Φc z 0 = z ∧
       ∀ t ∈ Icc (-T0) T0, HasDerivAt (Φc z) (odeField g (Φc z t)) t)
    (hrest : Φc (x₀, 0) τ = (x₀, 0))
    {ρ : ℝ} (hρ : 0 < ρ)
    (exp : E → E) (hexp : exp = fun v => (Φc (x₀, (1 / τ) • v) τ).1)
    (hC : ContDiffOn ℝ 1 exp (ball 0 ρ)) :
    HasFDerivAt exp (ContinuousLinearMap.id ℝ E) 0 := by
  classical
  have h0mem : (0 : E) ∈ ball 0 ρ := by simpa using hρ
  have hContAt : ContDiffAt ℝ 1 exp (0 : E) :=
    hC.contDiffAt (by simpa [ball, dist_eq_norm] using (isOpen_ball.mem_nhds h0mem))
  have hDiffAt : DifferentiableAt ℝ exp 0 :=
    hContAt.differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hL0 : HasFDerivAt exp (fderiv ℝ exp 0) 0 := hDiffAt.hasFDerivAt
  let E₀ : E →L[ℝ] E := fderiv ℝ exp 0
  have hEunit (u : E) (hu : ‖u‖ ≤ 1) : E₀ u = u := by
    have hcurve : HasDerivAt (fun h : ℝ => h • u) u (0 : ℝ) := by
      simpa using ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const u)
    have hL0at : HasFDerivAt exp E₀ ((0 : ℝ) • u) := by
      simpa [E₀, zero_smul] using hL0
    have hpE : HasDerivAt (fun h : ℝ => exp (h • u)) (E₀ u) (0 : ℝ) := by
      have hcomp := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := E) (E := E)
        (f := fun h : ℝ => h • u) (f' := u) (0 : ℝ) hL0at hcurve
      simpa [Function.comp_def] using hcomp
    let q : ℝ → E := fun h => (Φc (x₀, u) h).1
    have hmem_u : (x₀, u) ∈ closedBall (x₀, 0) 1 := mem_data_ball x₀ u hu
    have hq0 : HasDerivAt (fun h : ℝ => Φc (x₀, u) h) (odeField g (x₀, u)) (0 : ℝ) := by
      have hh := (hΦc (x₀, u) hmem_u).2 0 (by constructor <;> linarith)
      have hΦ0 : Φc (x₀, u) 0 = (x₀, u) := (hΦc (x₀, u) hmem_u).1
      refine hh.congr_deriv ?_
      rw [hΦ0]
    have hqd : HasDerivAt q u (0 : ℝ) := by
      have hf := hq0.hasFDerivAt.fst.hasDerivAt
      have hval : (odeField g (x₀, u)).1 = u := by simp [odeField]
      simpa [q, hval] using hf
    have hpq : (fun h : ℝ => exp (h • u)) =ᶠ[𝓝 (0 : ℝ)] q := by
      have hpos : 0 < min τ 1 / 2 := by positivity
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hpos] with h hh
      have hlt : |h| < min τ 1 / 2 := by
        simpa [Real.dist_eq] using (mem_ball.mp hh)
      by_cases hh0 : h = 0
      · have hp0 : exp 0 = x₀ := by
          rw [hexp]
          simp [hrest]
        have hq0v : q 0 = x₀ := by
          have hΦ0 : Φc (x₀, u) 0 = (x₀, u) := (hΦc (x₀, u) hmem_u).1
          simp [q, hΦ0]
        simp [hh0, hp0, hq0v]
      · have hltτ : |h| < τ := by
          have hle' : min τ 1 ≤ τ := min_le_left τ 1
          have hb : (min τ 1) / 2 < τ := by nlinarith [hle', hτ]
          exact lt_of_lt_of_le hlt (le_of_lt hb)
        have hs : |h / τ| ≤ 1 := by
          rw [abs_div, abs_of_pos hτ]
          exact (div_le_one hτ).mpr (le_of_lt hltτ)
        have hne : h / τ ≠ 0 := by
          intro hz
          apply hh0
          have hh0' : h = (h / τ) * τ := by field_simp [hτ.ne']
          rw [hh0', hz, zero_mul]
        have ht : τ ∈ Ioo (-T0) T0 := by constructor <;> linarith
        have hsc := exp_ray_scaling g hg hinv x₀ hT0 Φc hΦc u hu (a := h / τ) hs hne (t := τ) ht
        have hleft : exp (h • u) = (Φc (x₀, (h / τ) • u) τ).1 := by
          rw [hexp]
          change (Φc (x₀, (1 / τ) • (h • u)) τ).1 = (Φc (x₀, (h / τ) • u) τ).1
          have harg : (1 / τ) • (h • u) = (h / τ) • u := by
            rw [smul_smul]
            congr 1
            field_simp [hτ.ne']
          have hpair : ((x₀, (1 / τ) • (h • u)) : E × E) = (x₀, (h / τ) • u) := by
            apply Prod.ext
            · rfl
            · exact harg
          exact congrArg (fun z : E × E => (Φc z τ).1) hpair
        have hright : (Φc (x₀, (h / τ) • u) τ).1 = q h := by
          have hfac : (h / τ) * τ = h := by field_simp [hτ.ne']
          simpa [q, hfac] using hsc
        exact hleft.trans hright
    have hpq' : HasDerivAt (fun h : ℝ => exp (h • u)) u (0 : ℝ) :=
      hqd.congr_of_eventuallyEq hpq
    exact HasDerivAt.unique hpE hpq'
  have hEid : E₀ = ContinuousLinearMap.id ℝ E := by
    apply ContinuousLinearMap.ext
    intro u
    by_cases hu : u = 0
    · simp [hu, E₀, map_zero]
    · have hnu : ‖u‖ ≠ 0 := by intro h; exact hu (norm_eq_zero.mp h)
      let w : E := (‖u‖⁻¹ : ℝ) • u
      have hwn : ‖w‖ ≤ 1 := by
        dsimp [w]
        rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_nonneg (norm_nonneg u),
          inv_mul_cancel₀ hnu]
      have hEw : E₀ w = w := hEunit w hwn
      have huu : u = (‖u‖ : ℝ) • w := by
        dsimp [w]
        rw [smul_smul]
        have hmul : (‖u‖ : ℝ) * (‖u‖⁻¹ : ℝ) = 1 := by field_simp [hnu]
        rw [hmul, one_smul]
      calc
        E₀ u = E₀ ((‖u‖ : ℝ) • w) := by rw [← huu]
        _ = (‖u‖ : ℝ) • E₀ w := by rw [map_smul]
        _ = (‖u‖ : ℝ) • w := by rw [hEw]
        _ = u := huu.symm
  have hfin : HasFDerivAt exp (E₀) 0 := by simpa [E₀] using hL0
  simpa [hEid] using hfin

/-- a continuous linear self-map within operator distance `< 1` of the identity is invertible -/
lemma clm_invertible_of_near_id (f : E →L[ℝ] E)
    (hc : ‖f - ContinuousLinearMap.id ℝ E‖ < 1) : f.IsInvertible := by
  classical
  let id1 : E →L[ℝ] E := ContinuousLinearMap.id ℝ E
  have hc1 : 0 < 1 - ‖f - id1‖ := by
    have h : ‖f - id1‖ < 1 := by simpa [id1] using hc
    linarith
  have hnorm (x : E) : ‖f x‖ ≥ (1 - ‖f - id1‖) * ‖x‖ := by
    have hx : x = f x - (f - id1) x := by
      simp [id1]
    have h1 : ‖x‖ ≤ ‖f x‖ + ‖(f - id1) x‖ := by
      calc
        ‖x‖ = ‖f x - (f - id1) x‖ := by rw [← hx]
        _ ≤ ‖f x‖ + ‖(f - id1) x‖ := norm_sub_le _ _
    have h2 : ‖(f - id1) x‖ ≤ ‖f - id1‖ * ‖x‖ := (f - id1).le_opNorm x
    nlinarith
  have hinjF : Function.Injective (fun x : E => f x) := by
    intro x y hxy
    let z : E := x - y
    have hxy' : f x = f y := hxy
    have hfz : f z = 0 := by
      dsimp [z]
      rw [map_sub, hxy', sub_self]
    have hnz : ‖f z‖ = 0 := by rw [hfz]; simp
    have hlb := hnorm z
    have hzle : ‖z‖ ≤ 0 := by nlinarith
    have hz0 : z = 0 := norm_eq_zero.mp (le_antisymm hzle (norm_nonneg z))
    dsimp [z] at hz0
    exact sub_eq_zero.mp hz0
  have hinjL : Function.Injective (f : E →ₗ[ℝ] E) := by
    intro x y hxy
    apply hinjF
    simpa using hxy
  have hsurjL : Function.Surjective (f : E →ₗ[ℝ] E) :=
    (LinearMap.injective_iff_surjective).mp hinjL
  have hb : Function.Bijective (f : E →ₗ[ℝ] E) := ⟨hinjL, hsurjL⟩
  let eₗ : E ≃ₗ[ℝ] E := LinearEquiv.ofBijective (f : E →ₗ[ℝ] E) hb
  let e : E ≃L[ℝ] E := eₗ.toContinuousLinearEquiv
  refine ⟨e, ?_⟩
  ext x
  simpa [e, eₗ]

/-- The data-map of the flow is C¹ on a small ball around `z₀`, uniformly in time on a window. -/
lemma flow_map_contDiffOn (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (z₀ : E × E) (Tf : ℝ) (hTf : 0 < Tf)
    (Lf : NNReal) (Φ : E × E → ℝ → E × E)
    (hΦ₀ : ∀ z ∈ closedBall z₀ 1, Φ z 0 = z ∧
       (∀ t ∈ Icc (-Tf) Tf, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
       (∀ t : ℝ, Φ z t ∈ closedBall z₀ 2))
    (hLip : ∀ t ∈ Icc (-Tf) Tf, LipschitzOnWith Lf (fun z => Φ z t) (closedBall z₀ 1)) :
    ∃ τ > 0, τ ≤ Tf / 8 ∧ ∃ δ > 0, δ ≤ 1 / 8 ∧
      (∀ t ∈ Icc (-τ) τ, ContDiffOn ℝ 1 (fun z : E × E => Φ z t) (ball z₀ δ)) ∧
      (∀ t ∈ Icc (-τ) τ, ContinuousOn (fun z : E × E => fderiv ℝ (fun w => Φ w t) z) (ball z₀ δ)) := by
  classical
  rcases field_fderiv_bound g hg hinv z₀ 2 (by norm_num) with ⟨K0, hK0, hK⟩
  let B : ℝ := ∑ i : Fin (finrank ℝ (E × E)), ‖(finBasis ℝ (E × E)) i‖
  have hB : 0 ≤ B := by
    dsimp [B]
    exact Finset.sum_nonneg (fun i hi => norm_nonneg _)
  have hBi (i : Fin (finrank ℝ (E × E))) : ‖(finBasis ℝ (E × E)) i‖ ≤ B := by
    dsimp [B]
    exact Finset.single_le_sum (fun j hj => norm_nonneg _) (Finset.mem_univ i)
  let τ : ℝ := min (Tf / 8) (1 / (4 * (K0 + 1) * (B + 1)))
  have hτ : 0 < τ := by
    dsimp [τ]
    have hpos : 0 < 4 * (K0 + 1) * (B + 1) := by nlinarith [hB, hK0]
    exact lt_min (by positivity : 0 < Tf / 8) (one_div_pos.mpr hpos)
  have hτle : τ ≤ Tf / 8 := by
    dsimp [τ]
    exact min_le_left _ _
  have hτTf : 4 * τ ≤ Tf := by
    dsimp [τ]
    have hle : min (Tf / 8) (1 / (4 * (K0 + 1) * (B + 1))) ≤ Tf / 8 := min_le_left _ _
    nlinarith
  have hUb : ∀ i : Fin (finrank ℝ (E × E)),
      4 * (K0 + 1) * (‖(finBasis ℝ (E × E)) i‖ + 1) * τ ≤ 1 := by
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
    have h1 : 4 * (K0 + 1) * (‖(finBasis ℝ (E × E)) i‖ + 1) ≤ 4 * (K0 + 1) * (B + 1) := by
      have hle2 : ‖(finBasis ℝ (E × E)) i‖ + 1 ≤ B + 1 := by linarith [hBi i]
      exact mul_le_mul_of_nonneg_left hle2 (by nlinarith [hK0])
    have hpos2 : 0 ≤ τ := le_of_lt hτ
    calc
      4 * (K0 + 1) * (‖(finBasis ℝ (E × E)) i‖ + 1) * τ ≤ 4 * (K0 + 1) * (B + 1) * τ := by
        exact mul_le_mul_of_nonneg_right h1 hpos2
      _ ≤ 1 := hmain
  let δ : ℝ := 1 / 8
  have hδ0 : 0 < δ := by norm_num
  have hδ14 : δ ≤ 1 / 4 := by norm_num
  have hδ12 : δ ≤ 1 / 2 := by norm_num
  have hδ8 : δ ≤ 1 / 8 := by norm_num
  have hcontd := flow_fderiv_contOn g hg hinv z₀ Tf hTf Lf Φ hΦ₀ hLip hK0 hK hτ hτTf hδ0 hδ14 hUb
  have hU2pos : 0 < 2 * τ := by positivity
  have hU2Tf : 2 * τ ≤ Tf / 2 := by nlinarith [hτTf, hTf]
  have hUb2 : ∀ i : Fin (finrank ℝ (E × E)),
      2 * (K0 + 1) * (‖(finBasis ℝ (E × E)) i‖ + 1) * (2 * τ) ≤ 1 := by
    intro i
    have h := hUb i
    convert h using 1
    ring
  have hbp := flow_fderiv_ballpoint g hg hinv z₀ Tf hTf Lf Φ hΦ₀ hLip hK0 hK
    (δ := δ) hδ0 hδ12 (U := 2 * τ) hU2pos hU2Tf hUb2
  refine ⟨τ, hτ, hτle, δ, hδ0, hδ8, ?_, ?_⟩
  · intro t ht
    let f : E × E → E × E := fun z => Φ z t
    have ht2 : t ∈ Icc (-(2 * τ / 2)) (2 * τ / 2) := by
      constructor <;> nlinarith [ht.1, ht.2]
    have hDiff : DifferentiableOn ℝ f (ball z₀ δ) := by
      intro x hx
      rcases hbp x hx t ht2 with ⟨J, hJ0, hJd, hJadd, hJsmul, L, hLfd, hLval⟩
      exact (hLfd.differentiableAt).differentiableWithinAt
    have hContW : ContinuousOn (fun y => fderivWithin ℝ f (ball z₀ δ) y) (ball z₀ δ) := by
      have hcontD := hcontd t ht
      refine hcontD.congr ?_
      intro y hy
      rcases hbp y hy t ht2 with ⟨J, hJ0, hJd, hJadd, hJsmul, L, hLfd, hLval⟩
      have hdy : DifferentiableAt ℝ f y := hLfd.differentiableAt
      change fderivWithin ℝ f (ball z₀ δ) y = fderiv ℝ (fun w => Φ w t) y
      rw [fderivWithin_eq_fderiv (isOpen_ball.uniqueDiffWithinAt hy) hdy]
    have hfinal : ContDiffOn ℝ 1 (fun z : E × E => Φ z t) (ball z₀ δ) := by
      apply contDiffOn_one_of (g0 := f) (s := ball z₀ δ) hDiff hContW
    simpa [f] using hfinal
  · intro t ht
    exact hcontd t ht


/-- the flow-exponential is a local C¹ diffeo-type map at zero with invertible derivative -/
theorem exp_c1 (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (x₀ : E) :
    ∃ ρ > 0, ∃ Φ : E × E → ℝ → E × E,
      (∀ z ∈ closedBall (x₀, 0) 2, Φ z 0 = z ∧
         ∀ t ∈ Ioo (-ρ) ρ, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
      ∃ exp : E → E,
        exp 0 = x₀ ∧
        (∀ w : E, (g x₀) w w = 1 → ∀ t ∈ Ioo (-ρ) ρ,
           exp (t • w) = (Φ (x₀, w) t).1) ∧
        HasFDerivAt exp (ContinuousLinearMap.id ℝ E) 0 ∧
        ContDiffOn ℝ 1 exp (ball 0 ρ) ∧
        (∀ v ∈ ball 0 ρ, ∃ e : E ≃L[ℝ] E, (e : E →L[ℝ] E) = fderiv ℝ exp v) := by
  classical
  let z₀ : E × E := (x₀, 0)
  rcases flow_unit_ball_cont g hg hinv z₀ with ⟨T0, hT0, L0, Φc, hΦcall, hLipc⟩
  rcases flow_map_contDiffOn g hg hinv z₀ T0 hT0 L0 Φc (fun z hz => hΦcall z hz) hLipc with
    ⟨τc, hτcAnd⟩
  rcases hτcAnd with ⟨hτc, hτcLeRest⟩
  rcases hτcLeRest with ⟨hτc_le, restδ⟩
  rcases restδ with ⟨δc, hδcAnd⟩
  rcases hδcAnd with ⟨hδc0, hδcLeRest⟩
  rcases hδcLeRest with ⟨hδc8, hδBoth⟩
  rcases hδBoth with ⟨hCdiff, hDdiff⟩
  have hτT0 : τc < T0 := by nlinarith [hτc_le, hT0]
  let exp : E → E := fun v => (Φc (x₀, (1 / τc) • v) τc).1
  have hΦc0 : ∀ z ∈ closedBall (x₀, 0) 1, Φc z 0 = z ∧
      ∀ t ∈ Icc (-T0) T0, HasDerivAt (Φc z) (odeField g (Φc z t)) t := by
    intro z hz
    exact ⟨(hΦcall z hz).1, (hΦcall z hz).2.1⟩
  have hτI0 : τc ∈ Ioo (-T0) T0 := by constructor <;> linarith
  have hrest : Φc (x₀, 0) τc = (x₀, 0) :=
    rest_point_fixed g hg hinv x₀ hT0 Φc hΦc0 hτI0
  have hexp0 : exp 0 = x₀ := by
    simp [exp, hrest]
  let ρ₀ : ℝ := τc * δc / 2
  have hρ₀ : 0 < ρ₀ := by dsimp [ρ₀]; positivity
  have hτc_in : τc ∈ Icc (-τc) τc := by constructor <;> linarith
  have hFc : ContDiffOn ℝ 1 (fun z : E × E => Φc z τc) (ball z₀ δc) := hCdiff τc hτc_in
  have hH : ContDiffOn ℝ 1 (fun z : E × E => (Φc z τc).1) (ball z₀ δc) :=
    contDiffOn_one_fst_comp (ball z₀ δc) hFc
  have hAf : ContDiffOn ℝ 1 (fun v : E => (x₀, (1 / τc) • v)) (ball 0 ρ₀) :=
    contDiffOn_data_affine x₀ τc ρ₀
  have hAfmap : Set.MapsTo (fun v : E => (x₀, (1 / τc) • v)) (ball 0 ρ₀) (ball z₀ δc) := by
    intro v hv
    have hlt : ‖v‖ < ρ₀ := by simpa [dist_eq_norm] using (mem_ball.mp hv)
    have hnorm : ‖(x₀, (1 / τc) • v) - z₀‖ < δc := by
      have hnorm' : ‖(1 / τc) • v‖ < δc := by
        have h1 : ‖(1 / τc) • v‖ ≤ (1 / τc) * ‖v‖ := by
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / τc)]
        have h2 : (1 / τc) * ‖v‖ < δc := by
          have hltρ : ‖v‖ < τc * δc / 2 := by simpa [ρ₀] using hlt
          have hle1 : (1 / τc) * ‖v‖ ≤ (1 / τc) * (τc * δc / 2) := by
            exact mul_le_mul_of_nonneg_left (le_of_lt hltρ) (by positivity : 0 ≤ 1 / τc)
          have heq2 : (1 / τc) * (τc * δc / 2) = δc / 2 := by field_simp [hτc.ne']
          have hlt2 : δc / 2 < δc := by nlinarith [hδc0]
          calc
            (1 / τc) * ‖v‖ ≤ (1 / τc) * (τc * δc / 2) := hle1
            _ = δc / 2 := heq2
            _ < δc := hlt2
        exact lt_of_le_of_lt h1 h2
      have hd : ‖(x₀, (1 / τc) • v) - z₀‖ = ‖(1 / τc) • v‖ := by
        simp [z₀]
      rw [hd]
      exact hnorm'
    rw [mem_ball, dist_eq_norm]
    exact hnorm
  have hAfon : ContDiffOn ℝ 1 exp (ball 0 ρ₀) := by
    have hcomp := ContDiffOn.comp hH hAf hAfmap
    simpa [exp, Function.comp_def] using hcomp
  have hder0 : HasFDerivAt exp (ContinuousLinearMap.id ℝ E) 0 :=
    exp_fderiv_zero_id g hg hinv x₀ hT0 hτc hτT0 Φc hΦc0 hrest hρ₀ exp rfl hAfon
  have hfderiv0 : fderiv ℝ exp 0 = ContinuousLinearMap.id ℝ E := hder0.fderiv
  have hDerivCont : ContinuousOn (fun v : E => fderiv ℝ exp v) (ball 0 ρ₀) :=
    contDiffOn_one_cont_fderiv isOpen_ball hAfon
  have h0b : (0 : E) ∈ ball 0 ρ₀ := by simpa using hρ₀
  have hCont0 : ContinuousAt (fun v : E => fderiv ℝ exp v) 0 :=
    hDerivCont.continuousAt (by simpa [ball, dist_eq_norm] using (isOpen_ball.mem_nhds h0b))
  rcases Metric.continuousAt_iff.mp hCont0 (1 / 2 : ℝ) (by norm_num) with ⟨ρi, hρi0, hρi⟩
  let ρinv : ℝ := min ρ₀ (ρi / 2)
  have hρinv : 0 < ρinv := by
    dsimp [ρinv]
    exact lt_min hρ₀ (div_pos hρi0 (by norm_num))
  rcases geodesic_flow g hg hinv z₀ with ⟨Tg, hTgpos, Cg, hCg0, Φg, hΦgall⟩
  have hΦg : ∀ z ∈ closedBall z₀ 2, Φg z 0 = z ∧
      ∀ t ∈ Icc (-Tg) Tg, HasDerivAt (Φg z) (odeField g (Φg z t)) t := hΦgall.1
  let Tc : ℝ := min T0 Tg
  have hTc : 0 < Tc := by dsimp [Tc]; exact lt_min hT0 hTgpos
  have hTcT0 : Tc ≤ T0 := by dsimp [Tc]; exact min_le_left _ _
  have hTcTg : Tc ≤ Tg := by dsimp [Tc]; exact min_le_right _ _
  let Φ : E × E → ℝ → E × E := fun z t =>
    if hz1 : z ∈ closedBall z₀ 1 then Φc z t
    else if hz2 : z ∈ closedBall z₀ 2 then Φg z t
    else (exp (t • z.2), 0)
  have hΦ2 : ∀ z ∈ closedBall z₀ 2, Φ z 0 = z ∧
      ∀ t ∈ Icc (-Tc) Tc, HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
    intro z hz
    by_cases hz1 : z ∈ closedBall z₀ 1
    · have hfun : Φ z = Φc z := by
        funext s
        dsimp [Φ]
        rw [if_pos hz1]
      constructor
      · rw [hfun]
        exact (hΦcall z hz1).1
      · intro t ht
        have ht' : t ∈ Icc (-T0) T0 := by
          constructor <;> nlinarith [ht.1, ht.2, hTcT0]
        rw [hfun]
        exact (hΦcall z hz1).2.1 t ht'
    · have hfun : Φ z = Φg z := by
        funext s
        dsimp [Φ]
        rw [if_neg hz1]
        have hz2' : z ∈ closedBall z₀ 2 := hz
        rw [if_pos hz2']
      constructor
      · rw [hfun]
        exact (hΦg z hz).1
      · intro t ht
        have ht' : t ∈ Icc (-Tg) Tg := by
          constructor <;> nlinarith [ht.1, ht.2, hTcTg]
        rw [hfun]
        exact (hΦg z hz).2 t ht'
  let ρ : ℝ := min ρinv (min (Tc / 2) (τc / 2)) / 2
  have hρ : 0 < ρ := by
    dsimp [ρ]
    have h1 : 0 < min ρinv (min (Tc / 2) (τc / 2)) :=
      lt_min hρinv (lt_min (by positivity) (by positivity))
    positivity
  have hρle₀ : ρ ≤ ρ₀ := by
    dsimp [ρ]
    have h1 : min ρinv (min (Tc / 2) (τc / 2)) ≤ ρinv := min_le_left _ _
    have h2 : ρinv ≤ ρ₀ := by dsimp [ρinv]; exact min_le_left _ _
    nlinarith
  have hρlt_T : 4 * ρ ≤ Tc := by
    dsimp [ρ]
    have h1 : min ρinv (min (Tc / 2) (τc / 2)) ≤ Tc / 2 := by
      exact le_trans (min_le_right ρinv (min (Tc / 2) (τc / 2))) (min_le_left _ _)
    nlinarith
  refine ⟨ρ, hρ, Φ, ?_, exp, ?_, ?_, ?_, ?_⟩
  · intro z hz
    constructor
    · exact (hΦ2 z hz).1
    · intro t ht
      have htI : t ∈ Icc (-Tc) Tc := by
        constructor <;> nlinarith [ht.1, ht.2, hρlt_T, hρ]
      exact (hΦ2 z hz).2 t htI
  · exact hexp0
  · intro w hwunit t ht
    by_cases hw2 : ‖w‖ ≤ 2
    · have htabs : |t| < min (τc / 2) Tc := by
        have h1 : |t| < ρ := abs_lt.mpr ht
        have hb : ρ < min (τc / 2) Tc := by
          have hb1 : ρ ≤ (min (Tc / 2) (τc / 2)) / 2 := by
            dsimp [ρ]
            exact div_le_div_of_nonneg_right (min_le_right ρinv (min (Tc / 2) (τc / 2)))
              (by norm_num : (0 : ℝ) ≤ 2)
          have hb2 : (min (Tc / 2) (τc / 2)) / 2 < min (τc / 2) Tc := by
            have hA : min (Tc / 2) (τc / 2) / 2 < τc / 2 := by
              have hx : min (Tc / 2) (τc / 2) ≤ τc / 2 := min_le_right (Tc / 2) (τc / 2)
              nlinarith [hx, hτc]
            have hB : min (Tc / 2) (τc / 2) / 2 < Tc := by
              have hx : min (Tc / 2) (τc / 2) ≤ Tc / 2 := min_le_left (Tc / 2) (τc / 2)
              nlinarith [hx, hTc]
            rw [lt_min_iff]
            exact ⟨hA, hB⟩
          exact lt_of_le_of_lt hb1 hb2
        exact lt_of_lt_of_le h1 (le_of_lt hb)
      have hray := ray_agreement_core g hg hinv x₀ τc hτc T0 hT0 (by linarith) Φc
        (fun z hz => ⟨(hΦcall z hz).1, (hΦcall z hz).2.1⟩) Tc hTc Φ hΦ2 hrest w hw2 htabs
      simpa [exp] using hray
    · have hnm1 : (x₀, w) ∉ closedBall z₀ 1 := by
        intro hm
        have hd' : ‖w‖ = dist (x₀, w) (x₀, 0) := by simp [dist_eq_norm]
        have hm' : dist (x₀, w) (x₀, 0) ≤ 1 := by simpa [z₀] using (mem_closedBall.mp hm)
        have hd : ‖w‖ ≤ 1 := by rw [hd']; exact hm'
        exact hw2 (le_trans hd (by norm_num))
      have hnm2 : (x₀, w) ∉ closedBall z₀ 2 := by
        intro hm
        have hd' : ‖w‖ = dist (x₀, w) (x₀, 0) := by simp [dist_eq_norm]
        have hm' : dist (x₀, w) (x₀, 0) ≤ 2 := by simpa [z₀] using (mem_closedBall.mp hm)
        have hd : ‖w‖ ≤ 2 := by rw [hd']; exact hm'
        exact hw2 hd
      dsimp [Φ]
      rw [if_neg hnm1, if_neg hnm2]
  · exact hder0
  · constructor
    · exact hAfon.mono (ball_subset_ball hρle₀)
    · intro v hv
      have hlt : ‖v‖ < ρ := by simpa [dist_eq_norm] using (mem_ball.mp hv)
      have hb : ρ < ρi := by
        have hb1 : ρ ≤ ρinv / 2 := by
          dsimp [ρ]
          exact div_le_div_of_nonneg_right (min_le_left ρinv (min (Tc / 2) (τc / 2)))
            (by norm_num : (0 : ℝ) ≤ 2)
        have hρinvle : ρinv ≤ ρi / 2 := by dsimp [ρinv]; exact min_le_right _ _
        nlinarith [hρi0, hρinvle, hb1]
      have hvv : dist v 0 < ρi := by
        have hd : dist v 0 = ‖v‖ := by simp [dist_eq_norm]
        rw [hd]
        exact lt_trans hlt hb
      have hnear : dist (fderiv ℝ exp v) (fderiv ℝ exp 0) < 1 / 2 := hρi hvv
      have hnear' : ‖fderiv ℝ exp v - ContinuousLinearMap.id ℝ E‖ < 1 := by
        have h1 : ‖fderiv ℝ exp v - fderiv ℝ exp 0‖ < 1 / 2 := by
          simpa [dist_eq_norm] using hnear
        have h2 : ‖fderiv ℝ exp v - ContinuousLinearMap.id ℝ E‖ < 1 / 2 := by
          simpa [hfderiv0] using h1
        linarith
      exact clm_invertible_of_near_id (fderiv ℝ exp v) hnear'

end
end Submission.Model
