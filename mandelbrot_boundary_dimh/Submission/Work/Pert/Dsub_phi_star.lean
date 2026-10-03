import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.MaxDom
import Submission.Work.Pert.AsmDefs
import Submission.Work.Pert.discgate
import Submission.Work.Pert.small_of_nearOn
import Submission.Work.Pert.SmallData
import Submission.Work.Pert.Tau0TauCSharp
import Submission.Work.Pert.tau0_tauC_close
import Submission.Work.Pert.exists_tauC_gate_ge_fixed
import Submission.Work.Pert.DphiP_open
import Submission.Work.Pert.PertCoordClose
import Submission.Work.Pert.scale_lattice
import Submission.Work.PertU.inj_of_deriv_close
import Submission.Work.Pert.deriv_tau0_coordP_bounds
import Submission.Work.Pert.goodP_of_mem_Dphi
import Submission.Work.Pert.coordP_level_eq
import Submission.Work.Pert.deriv_Phi_close_on_gate
import Submission.Work.Pert.image_cover
import Submission.Work.Pert.closedBall_subset_Qm
import Submission.Work.Interfaces.FatouNarrow
import Submission.Work.Interfaces.Fatou

/-!
# PERT · `Work.Pert.Dsub_phi_star`

`(4.2.5)` for the perturbed coordinate: for large `η` there is a neighbourhood of `f₀` (of the
form `NearOn f₀ f Df L δ₀`, with `L`, `δ₀` depending on `η`) such that every perturbation carries
a Fatou coordinate `Φm` of `F = liftF u σ α` on the gate `Qm ξ₁ α` for which the maximal-domain
coordinate `coordP f Df (tauC σ α) Φm (Qm ξ₁ α)` satisfies, on `Dsm η ∪ Dsm (-η)`:

* `Dsm (±η) ⊆ Dφ` and `coordP` is injective on each disc;
* `‖τ₀ (coordP w) − w‖ ≤ |η|/40` (`φ*_f = τ₀ ∘ φ_f ≈ id`, Shishikura (4.2.5));
* `1/2 < ‖(τ₀ ∘ coordP)'‖ < 2`.

## Assembly plan (all ingredients on disk; §-labels refer to `NOTES_pert2_findings.md`)

Fix `η ≥ η₁` and put `K := 2 ^ 20 * (C + 1)`, `ρ := min (r₀ / 2) (1 / (K * η))`,
`L := closedBall 0 ρ`, `δ₀ := ρ ^ 2 / (K * η)`, where `r₀, C` come from
`Work.Pert.small_of_nearOn hd` (`closedBall 0 r₀ ⊆ D₀`).  Then for each perturbation:

1. **smallness** (`Work.Pert.small_of_nearOn`): `‖u 0 − 1‖ ≤ 1/1024`, `‖α‖ η ≤ 10⁻⁶`,
   `‖σ‖ ≤ C δ₀ / ρ`; also `σ ≠ 0` from `α ≠ 0` and `‖α‖ ≤ 1/2`.
2. **the gate point** `‖τ_f‖ ≥ 1/(4η)` (`Work.Pert.exists_tauC_gate_ge` at `z = (−ξ₁−1, 0)`) gives
   `rr ≥ 1/(4η)` from the hypothesis `tauC σ α '' Qm ⊆ ball 0 rr`.
3. **Φm** (`Work.Pert.exists_fatouCoord_near_id`): a Fatou coordinate of `F` on `Qm` with
   `‖Φm z − z‖ ≤ η/100` on the discs and `Dsm (±η) ⊆ Φm '' Qm`.
4. **`D_sub`**: `GoodP` with level `0` (`hcov`).
5. **injectivity**: on `Dsm (±η)`, `mIdxP = 0` and `coordP w = tauC σ α (invOn Φm Qm w)`; equal
   values force `ζ₁ − ζ₂ ∈ (1/α)ℤ` (`Work.Pert.tauC_eq_iff`) with `‖ζ₁ − ζ₂‖ < 1/‖α‖`
   (`Work.Pert.tauC_inj_of_dist_lt`), so `ζ₁ = ζ₂` and `w₁ = w₂`.
6. **`φ_star_close`**: the preimage `ζ` of `w` coming from `image_cover`
   (`Work.Pert.image_cover` with `z₀ = w`, `r ≥ 4‖Φm w − w‖`) lies in the discs, so
   `‖ζ − w‖ ≤ η/100`; then `τ₀ (τ_f ζ) ≈ ζ` (`Work.Pert.tau0_tauC_close`) and the triangle
   inequality gives `|η|/40`.  NOTE: one must use a *drift* bound `≤ η/1000` (or the distance
   form of the `∃ ζ` clause) so that `r` can be taken below `η/40`; the
   `exists_fatouCoord_near_id` statement with `η/100` only gives `r = η/25`.
7. **`φ_star_deriv`** (`Work.Pert.deriv_tau0_coordP_bounds`): locally
   `coordP = tauC σ α ∘ (local inverse of Φm)`, whence
   `(τ₀ ∘ coordP)' = −2πi α e^{−2πiαζ} / (σ Φm' ζ) ≈ u 0`.
-/

namespace Work.Pert

open scoped Topology


/-! ## Assembly helpers -/

/-- `NearOn` is monotone: shrinking the required set and relaxing the tolerance. -/
lemma nearOn_mono {f₀ f : ℂ → ℂ} {Df L L' : Set ℂ} {δ δ' : ℝ}
    (h : MandelDim.NearOn f₀ f Df L δ) (hL : L' ⊆ L) (hδ : δ ≤ δ') :
    MandelDim.NearOn f₀ f Df L' δ' :=
  ⟨h.1, hL.trans h.2.1, h.2.2.1, fun z hz => lt_of_lt_of_le (h.2.2.2 z (hL hz)) hδ⟩

/-- A point of the gate image sits at level `0`: the minimal level is `0` and the value of
`coordP` is the seed `τ (Φ⁻¹ w)`.  (`goodP_of_mem_image` makes the level condition vacuous, and
`mIdxP_le` shows `0` is minimal.) -/
lemma level_zero_of_mem_image {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ} {w : ℂ}
    (hinj : Set.InjOn Φ Q) (hw : w ∈ Φ '' Q) :
    mIdxP f Df τ Φ Q w = 0 ∧ coordP f Df τ Φ Q w = τ (invOn Φ Q w) := by
  have hgood : GoodP f Df τ Φ Q w := goodP_of_mem_image hw
  have hwit : w - ((0 : ℕ) : ℂ) ∈ Φ '' Q ∧
      ∀ j : ℕ, j < (0 : ℕ) → f^[j] (seedP τ Φ Q (w - ((0 : ℕ) : ℂ))) ∈ Df :=
    ⟨by simpa using hw, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
  have hle : mIdxP f Df τ Φ Q w ≤ 0 := mIdxP_le hgood hwit
  have h0 : mIdxP f Df τ Φ Q w = 0 := Nat.le_zero.mp hle
  refine ⟨h0, ?_⟩
  rw [coordP_self, h0]
  simp [seedP]

/-- **Cauchy/mean-value step of the assembly.**  If a map `Φc` is holomorphic on the fattened discs
`closedBall (±iη) (3η/10)` and is within `η/70` of the identity there, then on the (convex) discs
`Dsm (±η)` the `η/20`-balls around the points of `Dsm` still lie in the fattened discs, so Cauchy's
estimate on `k := Φc − id` gives `‖deriv Φc w − 1‖ ≤ (η/70)/(η/20) = 2/7 < 1/2`; hence
`1/2 < ‖deriv Φc w‖ < 2` and, by `Work.PertU.inj_of_deriv_close`, `Φc` is injective on each disc. -/
lemma deriv_and_inj_of_close {Φc : ℂ → ℂ} {η : ℝ} (hη : 0 < η)
    (hclose : ∀ w ∈ Metric.closedBall (Complex.I * (η : ℂ)) (3 * η / 10) ∪
        Metric.closedBall (-(Complex.I * (η : ℂ))) (3 * η / 10),
      DifferentiableAt ℂ Φc w ∧ ‖Φc w - w‖ ≤ η / 70) :
    (∀ w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η),
      1 / 2 < ‖deriv Φc w‖ ∧ ‖deriv Φc w‖ < 2) ∧
    Set.InjOn Φc (MandelDim.Dsm η) ∧ Set.InjOn Φc (MandelDim.Dsm (-η)) := by
  have h20 : (0 : ℝ) < η / 20 := by linarith
  have habs : |η| = η := abs_of_pos hη
  -- the fattened discs contain the `η/20`-ball around every point of `Dsm (η)` and `Dsm (-η)`
  have hsub : ∀ w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η), ∀ z ∈ Metric.closedBall w (η / 20),
      z ∈ Metric.closedBall (Complex.I * (η : ℂ)) (3 * η / 10) ∪
        Metric.closedBall (-(Complex.I * (η : ℂ))) (3 * η / 10) := by
    intro w hw z hz
    rw [Metric.mem_closedBall] at hz
    rcases hw with hw | hw
    · left
      rw [MandelDim.Dsm, Metric.mem_closedBall, habs] at hw
      have := dist_triangle z w (Complex.I * (η : ℂ))
      rw [Metric.mem_closedBall]
      linarith
    · right
      rw [MandelDim.Dsm, Metric.mem_closedBall, abs_neg, habs, Complex.ofReal_neg, mul_neg] at hw
      have := dist_triangle z w (-(Complex.I * (η : ℂ)))
      rw [Metric.mem_closedBall]
      linarith
  -- Cauchy's estimate for `k = Φc - id` on the ball of radius `η/20`
  have hbound : ∀ w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η), ‖deriv Φc w - 1‖ ≤ 2 / 7 := by
    intro w hw
    have hdiff : ∀ z ∈ Metric.closedBall w (η / 20), DifferentiableAt ℂ Φc z :=
      fun z hz => (hclose z (hsub w hw z hz)).1
    have hC : ∀ z ∈ Metric.sphere w (η / 20), ‖(fun y : ℂ => Φc y - y) z‖ ≤ η / 70 :=
      fun z hz => (hclose z (hsub w hw z (Metric.sphere_subset_closedBall hz))).2
    have hdc : DiffContOnCl ℂ (Φc - id) (Metric.ball w (η / 20)) := by
      refine ⟨fun z hz => ((hdiff z (Metric.ball_subset_closedBall hz)).sub
        differentiableAt_id).differentiableWithinAt, ?_⟩
      refine (continuousOn_of_forall_continuousAt ?_).mono Metric.closure_ball_subset_closedBall
      intro z hz
      exact ((hdiff z hz).sub differentiableAt_id).continuousAt
    have h := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := w) (R := η / 20)
      (C := η / 70) h20 hdc hC
    have hval : deriv (Φc - id) w = deriv Φc w - 1 := by
      rw [deriv_sub (hdiff w (Metric.mem_closedBall_self h20.le)) differentiableAt_id, deriv_id]
    have hq : (η / 70) / (η / 20) = 2 / 7 := by field_simp; ring
    calc ‖deriv Φc w - 1‖ = ‖deriv (Φc - id) w‖ := by rw [← hval]
      _ ≤ (η / 70) / (η / 20) := h
      _ = 2 / 7 := hq
  have hder1 : ∀ w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η),
      1 / 2 < ‖deriv Φc w‖ ∧ ‖deriv Φc w‖ < 2 := by
    intro w hw
    have hb := hbound w hw
    have h2 := abs_norm_sub_norm_le (deriv Φc w) (1 : ℂ)
    rw [norm_one] at h2
    constructor <;> linarith [abs_le.mp h2]
  refine ⟨hder1, ?_, ?_⟩
  · refine Work.PertU.inj_of_deriv_close (C := MandelDim.Dsm η) ?_ ?_ ?_
    · rw [MandelDim.Dsm]; exact convex_closedBall _ _
    · intro z hz
      exact (hclose z (hsub z (Or.inl hz) z
        (Metric.mem_closedBall_self (by linarith : (0:ℝ) ≤ η / 20)))).1
    · intro z hz; exact le_trans (hbound z (Or.inl hz)) (by norm_num)
  · refine Work.PertU.inj_of_deriv_close (C := MandelDim.Dsm (-η)) ?_ ?_ ?_
    · rw [MandelDim.Dsm]; exact convex_closedBall _ _
    · intro z hz
      exact (hclose z (hsub z (Or.inr hz) z
        (Metric.mem_closedBall_self (by linarith : (0:ℝ) ≤ η / 20)))).1
    · intro z hz; exact le_trans (hbound z (Or.inr hz)) (by norm_num)

/-- `τ₀` is injective off `0`. -/
lemma injOn_tau0 : Set.InjOn MandelDim.tau0 {z : ℂ | z ≠ 0} := by
  intro x hx y hy hxy
  have hx0 : x ≠ 0 := hx
  have hy0 : y ≠ 0 := hy
  simp only [MandelDim.tau0] at hxy
  rw [div_eq_div_iff hx0 hy0] at hxy
  simpa using hxy.symm

/-- Injectivity transfers back through a composition whose *outer* map is injective. -/
lemma injOn_of_comp_inj {τ Φ : ℂ → ℂ} {S : Set ℂ} (hτ : Set.InjOn τ {z | z ≠ 0})
    (h : Set.InjOn (fun w => τ (Φ w)) S) (hne : ∀ w ∈ S, Φ w ≠ 0) : Set.InjOn Φ S := by
  intro x hx y hy hxy
  refine h hx hy ?_
  show τ (Φ x) = τ (Φ y)
  rw [hxy]

/-- `D_sub`: the coverage of the discs by `Φ '' Q` puts them at level `0` of the maximal domain. -/
lemma Dsub_of_cover {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ} {η : ℝ}
    (hcov : ∀ w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η), ∃ ζ ∈ Q, Φ ζ = w) :
    MandelDim.Dsm η ∪ MandelDim.Dsm (-η) ⊆ DphiP f Df τ Φ Q := by
  intro w hw
  obtain ⟨ζ, hζ, hΦ⟩ := hcov w hw
  exact goodP_of_mem_image ⟨ζ, hζ, hΦ⟩

/-- The star clause: at level `0` (coverage + `level_zero_of_mem_image`) `coordP` is `τ (Φ⁻¹ w)`,
so the crux's star form transfers verbatim. -/
lemma star_of_cover {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ} {η : ℝ}
    (hinj : Set.InjOn Φ Q)
    (hcov : ∀ w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η), ∃ ζ ∈ Q, Φ ζ = w)
    (hstar : ∀ w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η), ∀ ζ ∈ Q, Φ ζ = w →
      ‖MandelDim.tau0 (τ ζ) - w‖ ≤ η / 40) :
    ∀ w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η),
      ‖MandelDim.tau0 (coordP f Df τ Φ Q w) - w‖ ≤ η / 40 := by
  intro w hw
  obtain ⟨ζ, hζQ, hΦζ⟩ := hcov w hw
  have hlev := level_zero_of_mem_image (f := f) (Df := Df) (τ := τ) (Φ := Φ) (Q := Q) hinj
    ⟨ζ, hζQ, hΦζ⟩
  rw [hlev.2]
  have heq : invOn Φ Q w = ζ := invOn_eq hinj ⟨ζ, hζQ, hΦζ⟩ hζQ hΦζ
  rw [heq]
  exact hstar w hw ζ hζQ hΦζ

/-! ## Assembly plan (details and constants: `Submission/Work/Pert/NOTES_Dsub_phi_star.md`)

The proof is assembled from three delegated pieces, all of which are now on disk or in flight:

* `Work.Pert.SmallData` (PROVED): with `ρ := min (r₀/2) (1/(10^6*η))`, `L := closedBall 0 ρ`,
  `δ₀ := ρ^2/(10^6*η)` it turns `NearOn f₀ f Df L δ₀` + the data into
  `‖u 0 − 1‖ ≤ 1/1024`, `1/(4η) ≤ rr`, `2π‖α‖η ≤ 1/64`.
* `Work.Pert.PertCoordClose` (in flight, the crux): gives `Φm` with `IsFatouCoordOn F Φm Q`, the
  coverage `∀ w ∈ closedBall (±iη) (3η/10), ∃ ζ ∈ Q, Φm ζ = w`, and the star form
  `∀ ζ ∈ Q, Φm ζ = w → ‖τ₀ (τ_f ζ) − w‖ ≤ η/70`.
* `Work.Pert.Tau0TauCSharp` (in flight): the sharp chart comparison needed for the injections.

Then: `D_sub` from the coverage at level `0` (`goodP_of_mem_image`); the star clause directly from
the crux (at level `0`, `coordP w = seedP … w = τ_f (Φm⁻¹ w)`); the derivative clause and the
injections from Cauchy's estimate on the ball of radius `η/16` around `w ∈ Dsm(±η)` (inside the
crux's region), which bounds the derivative of `k := (τ₀ ∘ coordP) − id` by `8/35 < 1/2`, and
`Work.PertU.inj_of_deriv_close`.  The *trap* recorded in the notes: the raw
`NearTranslationL1` constant `1/32` is far too weak (`≳ 2η/31` against a budget of `η/40`). -/



/-! ## Differentiability of the coordinate `τ₀ ∘ φ_f` on the gate image

The last clause of the target (`‖(τ₀ ∘ φ_f)'‖ ∈ (1/2, 2)`) is obtained from Cauchy's estimate
applied to `(τ₀ ∘ φ_f) - id`, so it needs `τ₀ ∘ φ_f` to be *holomorphic* on the fattened discs.
At a point `w` of the gate image `Φ '' Q` the maximal-domain coordinate is at level `0`
(`level_zero_of_mem_image`), and `Φ` is locally invertible there
(`Work.Pert.invOn_eventuallyEq_localInverse`), so `φ_f = τ ∘ (local inverse of Φ)` is holomorphic;
the only non-trivial input is that the seed map `τ = τC σ α` is differentiable at the preimage,
which holds because the gate misses the lattice `ℤ/α` (`Work.Pert.scale_lattice`).
-/

/-! ### `τ_f` is differentiable on the gate -/

/-- `exp (-(2πi α w)) ≠ 1` on the gate `Qm ξ₁ α`.  `Work.Pert.scale_lattice` shows that every point
of the gate keeps a lattice distance `ξ₁/2` from `ℤ/α`; if the exponential were `1` then
`α w = -n` for some `n : ℤ`, i.e. `w = (-n)/α`, contradicting that. -/
theorem exp_neg_ne_one_of_mem_Qm {α : ℂ} {ξ₁ : ℝ} (hξ₁ : 0 < ξ₁) (hα : MandelDim.InF1 α)
    {w : ℂ} (hw : w ∈ Work.Pert.Qm ξ₁ α) :
    Complex.exp (-(2 * Real.pi * Complex.I * α * w)) ≠ 1 := by
  have hαre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hα
  have hαne : α ≠ 0 := by
    intro h0
    rw [h0] at hαre
    simp only [Complex.zero_re] at hαre
    exact absurd hαre (lt_irrefl 0)
  intro h
  have hfac : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (by norm_num) ?_) Complex.I_ne_zero
    exact_mod_cast Real.pi_ne_zero
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have h4 : (2 * Real.pi * Complex.I) * (-(α * w)) = (2 * Real.pi * Complex.I) * (n : ℂ) := by
    rw [mul_comm (2 * Real.pi * Complex.I) (n : ℂ)]
    calc (2 * Real.pi * Complex.I) * (-(α * w)) = -(2 * Real.pi * Complex.I * α * w) := by ring
      _ = (n : ℂ) * (2 * Real.pi * Complex.I) := hn
  have h5 : -(α * w) = (n : ℂ) := mul_left_cancel₀ hfac h4
  have h6 : α * w = -(n : ℂ) := by linear_combination -h5
  have h7 : w = -((n : ℂ) / α) := by
    have hgoal : w = (-(n : ℂ)) / α := by
      rw [eq_div_iff hαne]
      linear_combination h6
    rw [hgoal]; ring
  have hlat := (Work.Pert.scale_lattice hξ₁ hα).2 hw (-n)
  have h8 : w - ((-n : ℤ) : ℂ) / α = 0 := by
    rw [show ((-n : ℤ) : ℂ) = -(n : ℂ) by simp, neg_div, h7]; ring
  rw [h8, norm_zero] at hlat
  linarith

/-- `τ_f = τC σ α` is differentiable at every point of the gate `Qm ξ₁ α`. -/
theorem differentiableAt_tauC_of_mem_Qm {σ α : ℂ} {ξ₁ : ℝ} (hξ₁ : 0 < ξ₁)
    (hα : MandelDim.InF1 α) {w : ℂ} (hw : w ∈ Work.Pert.Qm ξ₁ α) :
    DifferentiableAt ℂ (Work.Pert.tauC σ α) w := by
  have hE := exp_neg_ne_one_of_mem_Qm hξ₁ hα hw
  have hne : (1 : ℂ) - Complex.exp (-(2 * Real.pi * Complex.I * α * w)) ≠ 0 :=
    fun h => hE (sub_eq_zero.mp h).symm
  have hlin : DifferentiableAt ℂ (fun y : ℂ => -(2 * Real.pi * Complex.I * α * y)) w := by
    have h1 : DifferentiableAt ℂ (fun y : ℂ => (2 * Real.pi * Complex.I * α) * y) w :=
      (differentiableAt_const (c := 2 * Real.pi * Complex.I * α)).mul differentiableAt_id
    exact h1.neg
  have hexp : DifferentiableAt ℂ
      (fun y : ℂ => Complex.exp (-(2 * Real.pi * Complex.I * α * y))) w :=
    Complex.differentiableAt_exp.comp w hlin
  have hden : DifferentiableAt ℂ
      (fun y : ℂ => 1 - Complex.exp (-(2 * Real.pi * Complex.I * α * y))) w :=
    (differentiableAt_const (1 : ℂ)).sub hexp
  have hfinal : DifferentiableAt ℂ
      (fun y : ℂ => σ / (1 - Complex.exp (-(2 * Real.pi * Complex.I * α * y)))) w :=
    (differentiableAt_const (σ : ℂ)).div hden hne
  rw [show Work.Pert.tauC σ α
      = fun y : ℂ => σ / (1 - Complex.exp (-(2 * Real.pi * Complex.I * α * y))) from rfl]
  exact hfinal

/-! ### The maximal-domain coordinate near the gate image -/

/-- On the gate image `Φ '' Q`, the maximal-domain coordinate `coordP f Df τ Φ Q` agrees near `w`
with the seed `seedP τ Φ Q = τ ∘ Φ⁻¹` (the level is `0` on an open neighbourhood). -/
theorem coordP_eventuallyEq_seedP {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q : Set ℂ}
    (hinj : Set.InjOn Φ Q) (hQimg : IsOpen (Φ '' Q)) {w : ℂ} (hw : w ∈ Φ '' Q) :
    Work.Pert.coordP f Df τ Φ Q =ᶠ[𝓝 w] Work.Pert.seedP τ Φ Q := by
  filter_upwards [hQimg.mem_nhds hw] with u hu
  obtain ⟨-, hc⟩ := level_zero_of_mem_image (f := f) (Df := Df) (τ := τ) (Φ := Φ) (Q := Q) hinj hu
  rw [hc]
  rfl

/-- **`coordP` is differentiable at the points of the gate image.**  With `ζ₀ := Φ⁻¹ w ∈ Q`,
`invOn_eventuallyEq_localInverse` supplies a holomorphic local inverse `g` of `Φ` at `w`; near `w`
the level is `0` (the image `Φ '' Q` is open), so
`coordP f Df τ Φ Q = τ (invOn Φ Q ·) = τ (g ·) = τ ∘ g` there, and `τ ∘ g` is differentiable at `w`
because `τ` is differentiable at `g w = ζ₀`. -/
theorem differentiableAt_coordP_of_mem_image {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ}
    {Q : Set ℂ} {w : ℂ} (hQ : IsOpen Q) (hΦ : DifferentiableOn ℂ Φ Q) (hinj : Set.InjOn Φ Q)
    (hQimg : IsOpen (Φ '' Q)) (hw : w ∈ Φ '' Q) (hder : deriv Φ (invOn Φ Q w) ≠ 0)
    (hτ : DifferentiableAt ℂ τ (invOn Φ Q w)) :
    DifferentiableAt ℂ (Work.Pert.coordP f Df τ Φ Q) w := by
  obtain ⟨ζ₀, hζ₀, hΦζ₀⟩ := hw
  have hinv : invOn Φ Q w = ζ₀ := invOn_eq hinj ⟨ζ₀, hζ₀, hΦζ₀⟩ hζ₀ hΦζ₀
  rw [hinv] at hder hτ
  obtain ⟨g, hga, hg0, hge⟩ := invOn_eventuallyEq_localInverse hQ hΦ hinj hζ₀ hder
  rw [hΦζ₀] at hge
  have hgw : g w = ζ₀ := by rw [← hΦζ₀]; exact hg0
  have hev : Work.Pert.coordP f Df τ Φ Q =ᶠ[𝓝 w] fun u => τ (g u) := by
    filter_upwards [hQimg.mem_nhds (show w ∈ Φ '' Q from ⟨ζ₀, hζ₀, hΦζ₀⟩), hge] with u hu hgu
    obtain ⟨-, hc⟩ :=
      level_zero_of_mem_image (f := f) (Df := Df) (τ := τ) (Φ := Φ) (Q := Q) hinj hu
    rw [hc]
    show τ (invOn Φ Q u) = τ (g u)
    rw [hgu hu]
  have hdiff : DifferentiableAt ℂ (fun u => τ (g u)) w := by
    have hτg : DifferentiableAt ℂ τ (g w) := by rw [hgw]; exact hτ
    have hgw' : DifferentiableAt ℂ g w := by rw [← hΦζ₀]; exact hga.differentiableAt
    exact hτg.comp w hgw'
  exact hev.differentiableAt_iff.mpr hdiff

/-- `τ₀ ∘ coordP` is differentiable at the points of the gate image (composition of the
differentiable `coordP` with `τ₀`, which is differentiable off `0`). -/
theorem differentiableAt_tau0_coordP_of_mem_image {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ}
    {Q : Set ℂ} {w : ℂ} (hQ : IsOpen Q) (hΦ : DifferentiableOn ℂ Φ Q) (hinj : Set.InjOn Φ Q)
    (hQimg : IsOpen (Φ '' Q)) (hw : w ∈ Φ '' Q) (hder : deriv Φ (invOn Φ Q w) ≠ 0)
    (hτ : DifferentiableAt ℂ τ (invOn Φ Q w)) (hne : Work.Pert.coordP f Df τ Φ Q w ≠ 0) :
    DifferentiableAt ℂ
      (fun u => MandelDim.tau0 (Work.Pert.coordP f Df τ Φ Q u)) w := by
  have h := differentiableAt_coordP_of_mem_image (f := f) (Df := Df) hQ hΦ hinj hQimg hw hder hτ
  have h2 : DifferentiableAt ℂ
      (fun u => (-1 : ℂ) * (Work.Pert.coordP f Df τ Φ Q u)⁻¹) w :=
    (h.inv hne).const_mul (-1)
  rw [show (fun u => MandelDim.tau0 (Work.Pert.coordP f Df τ Φ Q u))
      = fun u => (-1 : ℂ) * (Work.Pert.coordP f Df τ Φ Q u)⁻¹ from by
    funext u; simp [MandelDim.tau0, div_eq_mul_inv]]
  exact h2

/-! ### Elementary bounds -/

/-- `τ₀ z = -1/z` has modulus `1/‖z‖` (with the convention `1/0 = 0`). -/
private lemma norm_tau0 (z : ℂ) : ‖MandelDim.tau0 z‖ = 1 / ‖z‖ := by
  rw [MandelDim.tau0, norm_div, norm_neg, norm_one]

/-- If `‖τ₀ (g w) - w‖ ≤ η/70` with `η > 0` and `‖w‖ ≥ 7η/10` then `g w ≠ 0`. -/
private lemma ne_zero_of_tau0_close {y w : ℂ} {η : ℝ} (hη : 0 < η)
    (hstar : ‖MandelDim.tau0 y - w‖ ≤ η / 70) (hwn : 7 * η / 10 ≤ ‖w‖) : y ≠ 0 := by
  intro h0
  have h2 : |‖MandelDim.tau0 y‖ - ‖w‖| ≤ η / 70 :=
    le_trans (abs_norm_sub_norm_le _ _) hstar
  have h3 : ‖w‖ - η / 70 ≤ ‖MandelDim.tau0 y‖ := by
    have := (abs_le.mp h2).1
    linarith
  have h4 : (0 : ℝ) < ‖MandelDim.tau0 y‖ := by
    have he : 7 * η / 10 - η / 70 = 24 * η / 35 := by ring
    have h5 : (0 : ℝ) < 24 * η / 35 := by positivity
    linarith
  rw [h0, norm_tau0, norm_zero] at h4
  exact absurd h4 (by norm_num)

/-- A point of a closed ball is at least `‖c‖ - r` away from the origin. -/
private lemma norm_ge_of_mem_closedBall {c w : ℂ} {r : ℝ}
    (hw : w ∈ Metric.closedBall c r) : ‖c‖ - r ≤ ‖w‖ := by
  rw [Metric.mem_closedBall, dist_eq_norm] at hw
  have h1 : ‖c‖ ≤ ‖w - c‖ + ‖w‖ := by
    calc ‖c‖ = ‖(c - w) + w‖ := by ring_nf
      _ ≤ ‖c - w‖ + ‖w‖ := norm_add_le _ _
      _ = ‖w - c‖ + ‖w‖ := by rw [norm_sub_rev]
  linarith

/-- On the small discs `Dsm (±η)` the modulus is at least `7η/10`. -/
private lemma norm_ge_seven_of_mem_dsm {η : ℝ} (hη : 0 < η) {w : ℂ}
    (hw : w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η)) : 7 * η / 10 ≤ ‖w‖ := by
  have hnormI : ‖Complex.I * (η : ℂ)‖ = η := by
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
  rcases hw with hw | hw
  · rw [MandelDim.Dsm] at hw
    have h := norm_ge_of_mem_closedBall hw
    rw [hnormI, abs_of_pos hη] at h
    linarith
  · rw [MandelDim.Dsm] at hw
    have h := norm_ge_of_mem_closedBall hw
    have hc : ‖Complex.I * ((-η : ℝ) : ℂ)‖ = η := by
      rw [Complex.ofReal_neg, mul_neg, norm_neg, hnormI]
    rw [hc, abs_neg, abs_of_pos hη] at h
    linarith

/-- On the fattened discs `closedBall (±iη) (3η/10)` the modulus is at least `7η/10`. -/
private lemma norm_ge_seven_of_mem_fattened {η : ℝ} (hη : 0 < η) {w : ℂ}
    (hw : w ∈ Metric.closedBall (Complex.I * (η : ℂ)) (3 * η / 10) ∪
      Metric.closedBall (-(Complex.I * (η : ℂ))) (3 * η / 10)) : 7 * η / 10 ≤ ‖w‖ := by
  rcases hw with hw | hw
  · have h := norm_ge_of_mem_closedBall hw
    have hc : ‖Complex.I * (η : ℂ)‖ = η := by
      rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hη]
    rw [hc] at h
    linarith
  · have h := norm_ge_of_mem_closedBall hw
    have hc : ‖-(Complex.I * (η : ℂ))‖ = η := by
      rw [norm_neg, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos hη]
    rw [hc] at h
    linarith

/-- `Dsm (±η)` is contained in the fattened discs `closedBall (±iη) (3η/10)`. -/
private lemma Dsm_subset_fattened {η : ℝ} (hη : 0 < η) :
    MandelDim.Dsm η ∪ MandelDim.Dsm (-η) ⊆
      Metric.closedBall (Complex.I * (η : ℂ)) (3 * η / 10) ∪
        Metric.closedBall (-(Complex.I * (η : ℂ))) (3 * η / 10) := by
  intro w hw
  have hrad : |η| / 4 ≤ 3 * η / 10 := by rw [abs_of_pos hη]; linarith
  rcases hw with hw | hw
  · left
    rw [MandelDim.Dsm] at hw
    exact Metric.closedBall_subset_closedBall hrad hw
  · right
    rw [MandelDim.Dsm] at hw
    have hc : Complex.I * ((-η : ℝ) : ℂ) = -(Complex.I * (η : ℂ)) := by
      rw [Complex.ofReal_neg, mul_neg]
    rw [hc] at hw
    refine Metric.closedBall_subset_closedBall ?_ hw
    rw [abs_neg, abs_of_pos hη]
    linarith

/-- The star bound on a covered set transfers to the maximal-domain coordinate (at level `0`). -/
theorem tau0_coordP_close_of_cover {f : ℂ → ℂ} {Df : Set ℂ} {τ Φ : ℂ → ℂ} {Q S : Set ℂ}
    {c : ℝ} (hinj : Set.InjOn Φ Q)
    (hcov : ∀ w ∈ S, ∃ ζ ∈ Q, Φ ζ = w)
    (hstar : ∀ w ∈ S, ∀ ζ ∈ Q, Φ ζ = w → ‖MandelDim.tau0 (τ ζ) - w‖ ≤ c) :
    ∀ w ∈ S, ‖MandelDim.tau0 (Work.Pert.coordP f Df τ Φ Q w) - w‖ ≤ c := by
  intro w hw
  obtain ⟨ζ, hζQ, hΦζ⟩ := hcov w hw
  obtain ⟨-, hc⟩ :=
    level_zero_of_mem_image (f := f) (Df := Df) (τ := τ) (Φ := Φ) (Q := Q) hinj ⟨ζ, hζQ, hΦζ⟩
  rw [hc]
  have heq : invOn Φ Q w = ζ := invOn_eq hinj ⟨ζ, hζQ, hΦζ⟩ hζQ hΦζ
  rw [heq]
  exact hstar w hw ζ hζQ hΦζ

/-- Arithmetic of the `(ρ, δ₀)` regime of the assembly: with
`ρ = min (r₀/2) (1/(10^6 η))` and `δ₀ ≤ ρ²/(10^6 η)`, all the smallness hypotheses of
`Work.Pert.SmallData` hold. -/
private lemma regime_arith {r₀ η ρ δ₀ : ℝ} (hr₀ : 0 < r₀) (hη : 1 ≤ η) (hδ₀ : 0 < δ₀)
    (hρ : ρ = min (r₀ / 2) (1 / (10 ^ 6 * η))) (hle : δ₀ ≤ ρ ^ 2 / (10 ^ 6 * η)) :
    0 < ρ ∧ ρ ≤ r₀ ∧ ρ ≤ 1 / 100 ∧ 2 * δ₀ ≤ ρ ∧ 65536 * δ₀ ≤ ρ ^ 2 ∧
      262144 * η * δ₀ ≤ ρ := by
  have hηpos : (0 : ℝ) < η := lt_of_lt_of_le zero_lt_one hη
  have hden : (0 : ℝ) < 10 ^ 6 * η := by positivity
  have hρpos : 0 < ρ := by
    rw [hρ]; exact lt_min (by linarith) (by positivity)
  have hρr₀ : ρ ≤ r₀ := by
    rw [hρ]; linarith [min_le_left (r₀ / 2) (1 / (10 ^ 6 * η))]
  have hρ100 : ρ ≤ 1 / 100 := by
    rw [hρ]
    refine le_trans (min_le_right _ _) ?_
    refine one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 100) ?_
    nlinarith [hη]
  have hρη : ρ ≤ η := by linarith
  have hρ1 : ρ ≤ 1 := by linarith
  have h2δ : 2 * δ₀ ≤ ρ := by
    have h1 : 2 * δ₀ ≤ 2 * (ρ ^ 2 / (10 ^ 6 * η)) := by linarith
    have h2 : 2 * (ρ ^ 2 / (10 ^ 6 * η)) ≤ ρ := by
      rw [← mul_div_assoc, div_le_iff₀ hden]
      nlinarith [hρη, hρpos]
    linarith
  have h655 : 65536 * δ₀ ≤ ρ ^ 2 := by
    have h1 : 65536 * δ₀ ≤ 65536 * (ρ ^ 2 / (10 ^ 6 * η)) := by linarith
    have h2 : 65536 * (ρ ^ 2 / (10 ^ 6 * η)) ≤ ρ ^ 2 := by
      rw [← mul_div_assoc, div_le_iff₀ hden]
      nlinarith [hη, sq_nonneg ρ]
    linarith
  have h262 : 262144 * η * δ₀ ≤ ρ := by
    have h1 : 262144 * η * δ₀ ≤ 262144 * η * (ρ ^ 2 / (10 ^ 6 * η)) :=
      mul_le_mul_of_nonneg_left hle (by positivity)
    have heq : 262144 * η * (ρ ^ 2 / (10 ^ 6 * η)) = ((262144 : ℝ) / 10 ^ 6) * ρ ^ 2 := by
      rw [← mul_div_assoc, div_eq_iff (by positivity : ((10 : ℝ) ^ 6) * η ≠ 0)]
      ring
    have h2 : ((262144 : ℝ) / 10 ^ 6) * ρ ^ 2 ≤ ρ := by
      have hc : ((262144 : ℝ) / 10 ^ 6) ≤ 1 := by norm_num
      nlinarith [hρ1, hρpos]
    linarith [h1, heq, h2]
  exact ⟨hρpos, hρr₀, hρ100, h2δ, h655, h262⟩

theorem Dsub_phi_star {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hF : MandelDim.FatouStatement) (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ η₁ : ℝ, 0 < η₁ ∧ ∀ η : ℝ, η₁ ≤ η →
    ∃ L : Set ℂ, IsCompact L ∧ L ⊆ D₀ ∧ ∃ δ₀ : ℝ, 0 < δ₀ ∧
      ∀ (f : ℂ → ℂ) (Df : Set ℂ) (ξ₁ rr : ℝ) (u : ℂ → ℂ) (σ α : ℂ),
        (hξ₁ : 0 < ξ₁) →
        MandelDim.NearOn f₀ f Df L δ₀ → f 0 = 0 → MandelDim.InF1 (MandelDim.rotOf f) →
        α = MandelDim.rotOf f → 0 < rr →
        DifferentiableOn ℂ u (Metric.ball 0 rr) →
        (∀ z ∈ Metric.ball 0 rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2) →
        (∀ z ∈ Metric.ball 0 rr, f z = z + z * (z - σ) * u z) →
        1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α) →
        (∀ z ∈ Work.Pert.Qm ξ₁ α, Work.Pert.tauC σ α z ∈ Metric.ball 0 rr) →
        2 * ξ₁ < η → η / 2 + 2 * ξ₁ < (1 / α).re →
        MandelDim.QAdm (some ((ξ₁ : ℂ) - 1 / α)) (some (-(ξ₁ : ℂ))) →
        MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm ξ₁ α) →
        ∃ Φm : ℂ → ℂ,
          MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm ξ₁ α) ∧
          MandelDim.Dsm η ∪ MandelDim.Dsm (-η) ⊆
            Work.Pert.DphiP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm ξ₁ α) ∧
          Set.InjOn (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm ξ₁ α))
            (MandelDim.Dsm η) ∧
          Set.InjOn (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm ξ₁ α))
            (MandelDim.Dsm (-η)) ∧
          (∀ w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η),
            ‖MandelDim.tau0 (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm ξ₁ α) w) - w‖
              ≤ |η| / 40) ∧
          (∀ w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η),
            1 / 2 < ‖deriv (fun u : ℂ =>
              MandelDim.tau0 (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm ξ₁ α) u)) w‖ ∧
            ‖deriv (fun u : ℂ =>
              MandelDim.tau0 (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm ξ₁ α) u)) w‖
              < 2) := by
  obtain ⟨r₀, hr₀pos, hr₀sub, hSmall⟩ := SmallData hd
  obtain ⟨η₁c, hη₁cpos, hCrux⟩ := PertCoordClose d hF hd
  refine ⟨max η₁c 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), fun η hη => ?_⟩
  have hηc : η₁c ≤ η := le_trans (le_max_left _ _) hη
  have hη1 : (1 : ℝ) ≤ η := le_trans (le_max_right _ _) hη
  have hηpos : (0 : ℝ) < η := lt_of_lt_of_le zero_lt_one hη1
  obtain ⟨Lc, hLccomp, hLcsub, δ₀c, hδ₀cpos, hCruxη⟩ := hCrux η hηc
  set ρ : ℝ := min (r₀ / 2) (1 / (10 ^ 6 * η)) with hρdef
  set δ₀ : ℝ := min δ₀c (ρ ^ 2 / (10 ^ 6 * η)) with hδ₀def
  have hδ₀le : δ₀ ≤ ρ ^ 2 / (10 ^ 6 * η) := by rw [hδ₀def]; exact min_le_right _ _
  have hδ₀c_le : δ₀ ≤ δ₀c := by rw [hδ₀def]; exact min_le_left _ _
  have hδ₀pos : 0 < δ₀ := lt_min hδ₀cpos (by positivity)
  have hρr₀₂ : ρ ≤ r₀ / 2 := by rw [hρdef]; exact min_le_left _ _
  obtain ⟨hρpos, hρr₀, hρ100, h2δ₀, hreg1, hreg2⟩ :=
    regime_arith hr₀pos hη1 hδ₀pos hρdef hδ₀le
  refine ⟨Lc ∪ Metric.closedBall (0 : ℂ) (r₀ / 2),
    hLccomp.union (isCompact_closedBall (0 : ℂ) (r₀ / 2)),
    Set.union_subset hLcsub
      (fun z hz =>
        hr₀sub (Metric.closedBall_subset_closedBall (by linarith : r₀ / 2 ≤ r₀) hz)),
    δ₀, hδ₀pos, ?_⟩
  intro f Df ξ₁ rr u σ α hξ₁ hNear hf0 hInF1 hαeq hrr0 hudiff hubnd hform heq htauC h2ξ hRe
    hQAdm hL1
  have hInF1α : MandelDim.InF1 α := by rw [hαeq]; exact hInF1
  -- ## the `NearOn` hypotheses for `SmallData` and for the crux
  have hNearBall : MandelDim.NearOn f₀ f Df (Metric.closedBall (0 : ℂ) ρ) δ₀ :=
    nearOn_mono hNear
      (fun z hz => Or.inr (Metric.closedBall_subset_closedBall hρr₀₂ hz)) le_rfl
  have hNearLc : MandelDim.NearOn f₀ f Df Lc δ₀c :=
    nearOn_mono hNear Set.subset_union_left hδ₀c_le
  obtain ⟨hu0, hrr, hαη⟩ := hSmall (ρ := ρ) (δ₀ := δ₀) (η := η) (rr := rr) (ξ₁ := ξ₁)
    (f := f) (Df := Df) (u := u) (σ := σ) (α := α)
    hρpos hρr₀ hρ100 hδ₀pos h2δ₀ hrr0 hηpos hξ₁ h2ξ hreg1 hreg2 hNearBall hf0 hudiff hubnd hform
    heq hInF1 hαeq htauC hQAdm
  obtain ⟨Φm, hFC, hcovstar⟩ := hCruxη f Df ξ₁ rr u σ α hξ₁ h2ξ hRe hαη hu0 hrr hNearLc hf0
    hInF1 hαeq hrr0 hudiff hubnd hform heq htauC hQAdm hL1
  -- ## structural facts about `Φm` on the gate
  have hQopen : IsOpen (Work.Pert.Qm ξ₁ α) :=
    Work.Fatou.Qreg.isOpen_Qreg (some ((ξ₁ : ℂ) - 1 / α)) (some (-(ξ₁ : ℂ)))
  have hΦdiff : DifferentiableOn ℂ Φm (Work.Pert.Qm ξ₁ α) := hFC.1
  have hinj : Set.InjOn Φm (Work.Pert.Qm ξ₁ α) := hFC.2.1
  have hder_all : ∀ z ∈ Work.Pert.Qm ξ₁ α, deriv Φm z ≠ 0 :=
    Work.Parab.inversion.deriv_ne_zero_of_injOn hQopen hΦdiff hinj
  have hQimg : IsOpen (Φm '' Work.Pert.Qm ξ₁ α) :=
    isOpen_image_of_deriv_ne_zero hQopen hΦdiff hder_all
  have hcov : ∀ w ∈ MandelDim.Dsm η ∪ MandelDim.Dsm (-η),
      ∃ ζ ∈ Work.Pert.Qm ξ₁ α, Φm ζ = w :=
    fun w hw => (hcovstar w (Dsm_subset_fattened hηpos hw)).1
  have hDsm_sub := Dsm_subset_fattened (η := η) hηpos
  have hstarFat : ∀ w ∈ Metric.closedBall (Complex.I * (η : ℂ)) (3 * η / 10) ∪
      Metric.closedBall (-(Complex.I * (η : ℂ))) (3 * η / 10),
      ‖MandelDim.tau0
        (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm ξ₁ α) w) - w‖
        ≤ η / 70 :=
    tau0_coordP_close_of_cover (f := f) (Df := Df) (τ := Work.Pert.tauC σ α) (Φ := Φm)
      (Q := Work.Pert.Qm ξ₁ α) (c := η / 70) hinj
      (fun w hw => (hcovstar w hw).1)
      (fun w hw ζ hζ hΦζ => (hcovstar w hw).2 ζ hζ hΦζ)
  -- ## differentiability of `τ₀ ∘ coordP` on the fattened discs
  have hclose : ∀ w ∈ Metric.closedBall (Complex.I * (η : ℂ)) (3 * η / 10) ∪
      Metric.closedBall (-(Complex.I * (η : ℂ))) (3 * η / 10),
      DifferentiableAt ℂ (fun u => MandelDim.tau0
          (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm ξ₁ α) u)) w ∧
        ‖MandelDim.tau0
          (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm ξ₁ α) w) - w‖
          ≤ η / 70 := by
    intro w hw
    obtain ⟨ζ₀, hζ₀, hΦζ₀⟩ := (hcovstar w hw).1
    have hζmem : invOn Φm (Work.Pert.Qm ξ₁ α) w ∈ Work.Pert.Qm ξ₁ α :=
      invOn_mem ⟨ζ₀, hζ₀, hΦζ₀⟩
    have hder : deriv Φm (invOn Φm (Work.Pert.Qm ξ₁ α) w) ≠ 0 := hder_all _ hζmem
    have hτ : DifferentiableAt ℂ (Work.Pert.tauC σ α)
        (invOn Φm (Work.Pert.Qm ξ₁ α) w) :=
      differentiableAt_tauC_of_mem_Qm hξ₁ hInF1α hζmem
    have hcoord : Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm ξ₁ α) w
        = Work.Pert.tauC σ α ζ₀ := by
      obtain ⟨-, hc⟩ := level_zero_of_mem_image (f := f) (Df := Df)
        (τ := Work.Pert.tauC σ α) (Φ := Φm) (Q := Work.Pert.Qm ξ₁ α) hinj ⟨ζ₀, hζ₀, hΦζ₀⟩
      rw [hc, invOn_eq hinj ⟨ζ₀, hζ₀, hΦζ₀⟩ hζ₀ hΦζ₀]
    have hne : Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm ξ₁ α) w ≠ 0 := by
      rw [hcoord]
      exact ne_zero_of_tau0_close hηpos ((hcovstar w hw).2 ζ₀ hζ₀ hΦζ₀)
        (norm_ge_seven_of_mem_fattened hηpos hw)
    exact ⟨differentiableAt_tau0_coordP_of_mem_image hQopen hΦdiff hinj hQimg
      ⟨ζ₀, hζ₀, hΦζ₀⟩ hder hτ hne, hstarFat w hw⟩
  obtain ⟨hderiv, hinj1, hinj2⟩ :=
    deriv_and_inj_of_close (Φc := fun u => MandelDim.tau0
      (Work.Pert.coordP f Df (Work.Pert.tauC σ α) Φm (Work.Pert.Qm ξ₁ α) u)) hηpos hclose
  refine ⟨Φm, hFC, Dsub_of_cover hcov, ?_, ?_, ?_, ?_⟩
  · refine injOn_of_comp_inj injOn_tau0 hinj1 (fun w hw => ?_)
    exact ne_zero_of_tau0_close hηpos (hstarFat w (hDsm_sub (Or.inl hw)))
      (norm_ge_seven_of_mem_dsm hηpos (Or.inl hw))
  · refine injOn_of_comp_inj injOn_tau0 hinj2 (fun w hw => ?_)
    exact ne_zero_of_tau0_close hηpos (hstarFat w (hDsm_sub (Or.inr hw)))
      (norm_ge_seven_of_mem_dsm hηpos (Or.inr hw))
  · have h := star_of_cover (f := f) (Df := Df) (τ := Work.Pert.tauC σ α) (Φ := Φm)
      (Q := Work.Pert.Qm ξ₁ α) hinj hcov (fun w hw ζ hζ hΦζ =>
        le_trans ((hcovstar w (hDsm_sub hw)).2 ζ hζ hΦζ) (by linarith))
    simpa only [abs_of_pos hηpos] using h
  · exact hderiv

end Work.Pert
