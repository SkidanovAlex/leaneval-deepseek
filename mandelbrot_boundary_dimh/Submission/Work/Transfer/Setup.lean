import Mathlib
import Submission.Work.Interfaces.Basic

/-!
# Setup for the area-transfer argument (`Work.Transfer`)

This file provides the vocabulary shared by the pieces of the proof of
`Work.Transfer.transfer` (Shishikura, *Hausdorff dimension of the boundary of the
Mandelbrot set and Julia sets*, Lemma 3.2 / MSS Lemma III.2 analogue):

* `critOrbit m c = (Tc c)^[m] c`, the `m`-th point of the critical orbit
  (`critOrbit m c = (Tc c)^[m+1] 0`), with its basic calculus;
* `MotionData`, the bundle of properties of the holomorphic motion `π` supplied by
  `MandelDim.MotionStatement`;
* `codeOf`, a (classical) choice of code realising the critical orbit as a point of the
  limit set, and `HitSet`, the set of parameters where the critical value hits the limit set;
* a few elementary analytic lemmas (Cauchy estimate, Lipschitz bound) and the "escaping
  parameter" facts used in the later steps.
-/

open LeanEval.Dynamics.MandelbrotBoundary
open Set Metric Filter Topology
open Classical

noncomputable section

namespace Work.Transfer

/-! ## The critical orbit -/

/-- The critical orbit: `critOrbit j c = (Tc c)^[j] c`.  Note `critOrbit j c = (Tc c)^[j+1] 0`. -/
def critOrbit (j : ℕ) (c : ℂ) : ℂ := (Tc c)^[j] c

@[simp] theorem critOrbit_zero (c : ℂ) : critOrbit 0 c = c := rfl

theorem critOrbit_succ (j : ℕ) (c : ℂ) : critOrbit (j + 1) c = (critOrbit j c) ^ 2 + c := by
  simp only [critOrbit, Tc, Function.iterate_succ_apply']

theorem critOrbit_eq_iterate_zero (j : ℕ) (c : ℂ) : critOrbit j c = (Tc c)^[j + 1] 0 := by
  induction j with
  | zero => simp [critOrbit, Tc]
  | succ j ih =>
    calc critOrbit (j + 1) c = (critOrbit j c) ^ 2 + c := critOrbit_succ j c
      _ = Tc c (critOrbit j c) := rfl
      _ = Tc c ((Tc c)^[j + 1] 0) := by rw [ih]
      _ = (Tc c)^[j + 1 + 1] 0 := (Function.iterate_succ_apply' (Tc c) (j + 1) 0).symm

theorem critOrbit_iterate_apply (j k : ℕ) (c : ℂ) :
    (Tc c)^[k] (critOrbit j c) = critOrbit (k + j) c := by
  rw [critOrbit, critOrbit, ← Function.iterate_add_apply]

theorem differentiable_critOrbit (j : ℕ) : Differentiable ℂ (critOrbit j) := by
  induction j with
  | zero => exact differentiable_id
  | succ j ih =>
    have heq : critOrbit (j + 1) = fun c : ℂ => (critOrbit j c) ^ 2 + c :=
      funext fun c => critOrbit_succ j c
    rw [heq]
    exact (ih.pow 2).add differentiable_id

theorem continuous_critOrbit (j : ℕ) : Continuous (critOrbit j) :=
  (differentiable_critOrbit j).continuous

theorem differentiableOn_critOrbit (j : ℕ) (s : Set ℂ) : DifferentiableOn ℂ (critOrbit j) s :=
  (differentiable_critOrbit j).differentiableOn

/-- The critical orbit is bounded and Lipschitz on any ball (elementary induction; no Cauchy
estimates needed). -/
theorem critOrbit_bound_lip {c₀ : ℂ} {ρ : ℝ} (hρ : 0 < ρ) (j : ℕ) :
    ∃ (B D : ℝ), 0 ≤ B ∧ 0 ≤ D ∧
      (∀ z ∈ ball c₀ ρ, ‖critOrbit j z‖ ≤ B) ∧
      (∀ z ∈ ball c₀ ρ, ∀ w ∈ ball c₀ ρ, ‖critOrbit j z - critOrbit j w‖ ≤ D * ‖z - w‖) := by
  induction j with
  | zero =>
    refine ⟨‖c₀‖ + ρ, 1, by positivity, one_pos.le, ?_, ?_⟩
    · intro z hz
      have h1 : ‖z‖ ≤ ‖z - c₀‖ + ‖c₀‖ := by simpa using norm_add_le (z - c₀) c₀
      have h2 : ‖z - c₀‖ < ρ := by simpa [dist_eq_norm] using hz
      change ‖z‖ ≤ ‖c₀‖ + ρ
      linarith
    · intro z _ w _
      change ‖z - w‖ ≤ 1 * ‖z - w‖
      rw [one_mul]
  | succ j ih =>
    obtain ⟨B, D, hB, hD, hbnd, hlip⟩ := ih
    have hS : 0 ≤ ‖c₀‖ + ρ := by positivity
    have hD' : 0 ≤ 2 * B * D + 1 := by nlinarith [mul_nonneg hB hD]
    refine ⟨B ^ 2 + (‖c₀‖ + ρ), 2 * B * D + 1, by positivity, hD', ?_, ?_⟩
    · intro z hz
      have h2 : ‖(critOrbit j z) ^ 2 + z‖ ≤ ‖critOrbit j z‖ ^ 2 + ‖z‖ := by
        calc ‖(critOrbit j z) ^ 2 + z‖ ≤ ‖(critOrbit j z) ^ 2‖ + ‖z‖ := norm_add_le _ _
          _ = ‖critOrbit j z‖ ^ 2 + ‖z‖ := by rw [norm_pow]
      have h3 : ‖critOrbit j z‖ ^ 2 ≤ B ^ 2 := by
        have := hbnd z hz
        nlinarith [norm_nonneg (critOrbit j z)]
      have h4 : ‖z‖ ≤ ‖c₀‖ + ρ := by
        have h5 : ‖z‖ ≤ ‖z - c₀‖ + ‖c₀‖ := by simpa using norm_add_le (z - c₀) c₀
        have h6 : ‖z - c₀‖ < ρ := by simpa [dist_eq_norm] using hz
        linarith
      rw [critOrbit_succ]
      linarith
    · intro z hz w hw
      have h1 : critOrbit (j + 1) z - critOrbit (j + 1) w
          = (critOrbit j z - critOrbit j w) * (critOrbit j z + critOrbit j w) + (z - w) := by
        rw [critOrbit_succ, critOrbit_succ]; ring
      rw [h1]
      have h2 : ‖critOrbit j z - critOrbit j w‖ ≤ D * ‖z - w‖ := hlip z hz w hw
      have h3 : ‖critOrbit j z + critOrbit j w‖ ≤ 2 * B := by
        have h4 : ‖critOrbit j z + critOrbit j w‖ ≤ ‖critOrbit j z‖ + ‖critOrbit j w‖ :=
          norm_add_le _ _
        have h5 := hbnd z hz
        have h6 := hbnd w hw
        linarith
      have h7 : 0 ≤ ‖z - w‖ := norm_nonneg _
      have h8 : 0 ≤ D * ‖z - w‖ := mul_nonneg hD h7
      have h9 : ‖critOrbit j z - critOrbit j w‖ * ‖critOrbit j z + critOrbit j w‖
          ≤ (D * ‖z - w‖) * (2 * B) := mul_le_mul h2 h3 (norm_nonneg _) h8
      calc ‖(critOrbit j z - critOrbit j w) * (critOrbit j z + critOrbit j w) + (z - w)‖
          ≤ ‖(critOrbit j z - critOrbit j w) * (critOrbit j z + critOrbit j w)‖ + ‖z - w‖ :=
            norm_add_le _ _
        _ = ‖critOrbit j z - critOrbit j w‖ * ‖critOrbit j z + critOrbit j w‖ + ‖z - w‖ := by
            rw [norm_mul]
        _ ≤ (D * ‖z - w‖) * (2 * B) + ‖z - w‖ := by linarith
        _ = (2 * B * D + 1) * ‖z - w‖ := by ring

/-! ## Motion data (the output of `MandelDim.MotionStatement`, bundled) -/

/-- The bundle of properties of the holomorphic motion of the IFS at `c₀` provided by
`MandelDim.MotionStatement`: base point, holomorphy and injectivity in the parameter, equivariance
with respect to the inverse branches, bounded forward orbits, uniform contraction in the code,
Lipschitz dependence in the parameter, and Hölder dependence in the parameter with exponent `a`. -/
structure MotionData (c₀ : ℂ) (N : ℕ) (τ : Fin N → ℂ → ℂ) (n : Fin N → ℕ) (p : ℂ)
    (ρ a : ℝ) (π : ℂ → (ℕ → Fin N) → ℂ) : Prop where
  base : ∀ ω : ℕ → Fin N, π c₀ ω = MandelDim.codingPt τ p ω
  diff : ∀ ω : ℕ → Fin N, DifferentiableOn ℂ (fun c => π c ω) (ball c₀ ρ)
  inj : ∀ c ∈ ball c₀ ρ, Function.Injective (π c)
  equiv : ∀ c ∈ ball c₀ ρ, ∀ ω : ℕ → Fin N,
    (Tc c)^[n (ω 0)] (π c ω) = π c (fun k => ω (k + 1))
  orbBdd : ∃ B : ℝ, ∀ c ∈ ball c₀ ρ, ∀ ω : ℕ → Fin N, ∀ j : ℕ, ‖(Tc c)^[j] (π c ω)‖ ≤ B
  contract : ∃ C θ : ℝ, 0 ≤ θ ∧ θ < 1 ∧ ∀ c ∈ ball c₀ ρ, ∀ k : ℕ, ∀ ω ω' : ℕ → Fin N,
    (∀ j < k, ω j = ω' j) → ‖π c ω - π c ω'‖ ≤ C * θ ^ k
  lipschitz : ∃ L : ℝ, ∀ c ∈ ball c₀ ρ, ∀ c' ∈ ball c₀ ρ, ∀ ω : ℕ → Fin N,
    ‖π c ω - π c' ω‖ ≤ L * ‖c - c'‖
  holder : ∃ C : ℝ, ∀ c ∈ ball c₀ ρ, ∀ c' ∈ ball c₀ ρ, ∀ ω ω' : ℕ → Fin N,
    ‖π c ω - π c ω'‖ ≤ C * ‖π c' ω - π c' ω'‖ ^ a

/-! ## Elementary facts about the frontier of `Mandelbrot` -/

/-- Every ball around a point of the frontier of `Mandelbrot` contains a parameter outside
`Mandelbrot`. -/
theorem exists_not_mem_ball_of_frontier {c₀ : ℂ} (hc₀ : c₀ ∈ frontier Mandelbrot) {ρ : ℝ}
    (hρ : 0 < ρ) : ∃ c ∈ ball c₀ ρ, c ∉ Mandelbrot := by
  rw [frontier_eq_closure_inter_closure] at hc₀
  have h : c₀ ∈ closure Mandelbrotᶜ := hc₀.2
  rw [Metric.mem_closure_iff] at h
  obtain ⟨c, hc, hdist⟩ := h ρ hρ
  exact ⟨c, by rwa [mem_ball, dist_comm], hc⟩

/-- The frontier of `Mandelbrot` is contained in `Mandelbrot`. -/
theorem frontier_subset_mandelbrot (hM : MandelDim.MsetStatement) :
    frontier Mandelbrot ⊆ Mandelbrot := by
  rw [frontier_eq_closure_inter_closure]
  intro c hc
  rw [hM.1.closure_eq] at hc
  exact hc.1

/-! ## Coding of a critical value by a word -/

/-- A classical choice of a word `w` with `critOrbit m c = π c w`, if such a word exists
(otherwise the constant word `0`). -/
def codeOf {N : ℕ} [NeZero N] (m : ℕ) (π : ℂ → (ℕ → Fin N) → ℂ) (c : ℂ) : ℕ → Fin N :=
  if h : ∃ w : ℕ → Fin N, critOrbit m c = π c w then Classical.choose h else fun _ => 0

theorem codeOf_spec {N : ℕ} [NeZero N] (m : ℕ) (π : ℂ → (ℕ → Fin N) → ℂ) (c : ℂ)
    (h : ∃ w : ℕ → Fin N, critOrbit m c = π c w) :
    critOrbit m c = π c (codeOf m π c) := by
  rw [codeOf, dif_pos h]
  exact Classical.choose_spec h

theorem codeOf_eq {N : ℕ} [NeZero N] (m : ℕ) (π : ℂ → (ℕ → Fin N) → ℂ) {c : ℂ} {w : ℕ → Fin N}
    (hinj : Function.Injective (π c)) (h : critOrbit m c = π c w) : codeOf m π c = w :=
  hinj ((codeOf_spec m π c ⟨w, h⟩).symm.trans h)

/-- The set of parameters in `ball c₁ ρ₁` whose critical value `critOrbit m c` is realised by the
limit set with a code in `W`. -/
def HitSet {N : ℕ} (m : ℕ) (c₁ : ℂ) (ρ₁ : ℝ) (π : ℂ → (ℕ → Fin N) → ℂ)
    (W : Set (ℕ → Fin N)) : Set ℂ :=
  {c | c ∈ ball c₁ ρ₁ ∧ ∃ w ∈ W, critOrbit m c = π c w}

/-- Membership in `cylinder ((List.range k).map w)` is agreement with `w` on the first `k`
letters. -/
theorem mem_cylinder_map_range {N : ℕ} (w : ℕ → Fin N) (k : ℕ) {ω : ℕ → Fin N} :
    ω ∈ MandelDim.cylinder ((List.range k).map w) ↔ ∀ j < k, ω j = w j := by
  constructor
  · intro h j hj
    have hj' : j < ((List.range k).map w).length := by simpa using hj
    have := h j hj'
    simpa using this
  · intro h j hj
    have hjk : j < k := by simpa using hj
    simpa using h j hjk

/-! ## Cauchy estimate and Lipschitz bounds for a bounded holomorphic family -/

/-- A holomorphic function bounded by `M` on `ball c R` is Lipschitz with constant `2 * M / R` on
the half-ball `ball c (R/2)`. -/
theorem lipschitz_of_norm_le_ball {f : ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R) (hM0 : 0 ≤ M)
    (hf : DifferentiableOn ℂ f (ball c R)) (hM : ∀ z ∈ ball c R, ‖f z‖ ≤ M) :
    ∀ z ∈ ball c (R / 2), ∀ w ∈ ball c (R / 2), ‖f z - f w‖ ≤ (2 * M / R) * ‖z - w‖ := by
  intro z hz w hw
  have hsub : ball c (R / 2) ⊆ ball c R := by
    intro u hu
    rw [mem_ball, dist_eq_norm] at hu ⊢
    linarith
  have hderiv : ∀ u ∈ ball c (R / 2), ‖deriv f u‖ ≤ 2 * M / R := by
    intro u hu
    have huR : ‖u - c‖ < R / 2 := by rw [mem_ball, dist_eq_norm] at hu; exact hu
    have hsub' : closedBall u (R / 2) ⊆ ball c R := by
      intro v hv
      rw [mem_closedBall, dist_eq_norm] at hv
      rw [mem_ball, dist_eq_norm]
      have h1 : ‖v - c‖ ≤ ‖v - u‖ + ‖u - c‖ := by
        calc ‖v - c‖ = ‖(v - u) + (u - c)‖ := by ring_nf
          _ ≤ ‖v - u‖ + ‖u - c‖ := norm_add_le _ _
      linarith
    have hd : DiffContOnCl ℂ f (ball u (R / 2)) :=
      DifferentiableOn.diffContOnCl_ball (U := ball c R) hf hsub'
    have hC : ∀ v ∈ sphere u (R / 2), ‖f v‖ ≤ M := fun v hv => hM v (hsub' (sphere_subset_closedBall hv))
    have := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (c := u) (R := R / 2) (C := M)
      (f := f) (by linarith) hd hC
    calc ‖deriv f u‖ ≤ M / (R / 2) := this
      _ = 2 * M / R := by ring
  have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := ball c (R / 2))
    (C := 2 * M / R)
    (fun u hu => hf.differentiableAt (isOpen_ball.mem_nhds (hsub hu))) hderiv
    (convex_ball c (R / 2)) hw hz
  linarith [hmvt]

/-- The same Lipschitz bound, uniformly in a family of holomorphic functions. -/
theorem family_lipschitz_of_norm_le_ball {F : ℕ → ℂ → ℂ} {c : ℂ} {R M : ℝ} (hR : 0 < R)
    (hM0 : 0 ≤ M) (hF : ∀ j, DifferentiableOn ℂ (F j) (ball c R))
    (hM : ∀ j z, z ∈ ball c R → ‖F j z‖ ≤ M) :
    ∀ j, ∀ z ∈ ball c (R / 2), ∀ w ∈ ball c (R / 2), ‖F j z - F j w‖ ≤ (2 * M / R) * ‖z - w‖ :=
  fun j => lipschitz_of_norm_le_ball hR hM0 (hF j) (fun z hz => hM j z hz)

/-! ## Escaping parameters versus bounded orbits -/

/-- If some point of the critical orbit has a bounded forward orbit, then the parameter lies in
`Mandelbrot`. -/
theorem mem_mandelbrot_of_bound_orbit {N : ℕ} (hM : MandelDim.MsetStatement) {c : ℂ} {m : ℕ}
    {w : ℕ → Fin N} {π : ℂ → (ℕ → Fin N) → ℂ} {B : ℝ}
    (hB : ∀ j : ℕ, ‖(Tc c)^[j] (π c w)‖ ≤ B) (heq : critOrbit m c = π c w) :
    c ∈ Mandelbrot := by
  refine ⟨max B (∑ i ∈ Finset.range (m + 2), ‖(Tc c)^[i] 0‖), fun n => ?_⟩
  rcases lt_or_ge n (m + 2) with hn | hn
  · have h1 : ‖(Tc c)^[n] 0‖ ≤ ∑ i ∈ Finset.range (m + 2), ‖(Tc c)^[i] 0‖ :=
      Finset.single_le_sum (f := fun i => ‖(Tc c)^[i] 0‖) (fun i _ => norm_nonneg _)
        (Finset.mem_range.2 hn)
    exact h1.trans (le_max_right _ _)
  · have h1 : (Tc c)^[n - (m + 1)] ((Tc c)^[m + 1] 0) = (Tc c)^[n] 0 := by
      rw [← Function.iterate_add_apply, Nat.sub_add_cancel (show m + 1 ≤ n by omega)]
    rw [← h1, ← critOrbit_eq_iterate_zero m c, heq]
    exact le_trans (hB (n - (m + 1))) (le_max_left _ _)

/-- At an escaping parameter, the critical value is never a point of the limit set. -/
theorem critOrbit_ne_pi_of_not_mem {N : ℕ} (hM : MandelDim.MsetStatement) {c : ℂ}
    (hc : c ∉ Mandelbrot) {m : ℕ} {w : ℕ → Fin N} {π : ℂ → (ℕ → Fin N) → ℂ} {B : ℝ}
    (hB : ∀ j : ℕ, ‖(Tc c)^[j] (π c w)‖ ≤ B) : critOrbit m c ≠ π c w :=
  fun heq => hc (mem_mandelbrot_of_bound_orbit hM hB heq)

/-- Step 2 of the transfer argument: for the fixed `m` of the hit, the function
`c ↦ critOrbit m c - π c w` is never identically zero on `ball c₀ ρ`. -/
theorem exists_critOrbit_ne_pi {N : ℕ} (hM : MandelDim.MsetStatement) {c₀ : ℂ}
    (hc₀ : c₀ ∈ frontier Mandelbrot) {τ : Fin N → ℂ → ℂ} {n : Fin N → ℕ} {p : ℂ} {ρ a : ℝ}
    {π : ℂ → (ℕ → Fin N) → ℂ} (hρ : 0 < ρ) (hMD : MotionData c₀ N τ n p ρ a π) (m : ℕ)
    (w : ℕ → Fin N) : ∃ z ∈ ball c₀ ρ, critOrbit m z ≠ π z w := by
  obtain ⟨z, hz, hzM⟩ := exists_not_mem_ball_of_frontier hc₀ hρ
  obtain ⟨B, hB⟩ := hMD.orbBdd
  exact ⟨z, hz, critOrbit_ne_pi_of_not_mem hM hzM (fun j => hB z hz w j)⟩

end Work.Transfer

end
