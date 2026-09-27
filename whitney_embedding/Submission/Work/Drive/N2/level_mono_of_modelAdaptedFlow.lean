import Mathlib
import Submission.Work.Drive.N2.exists_modelAdapted_levelFlow_chartODE
import Submission.Work.Drive.N2.modelFlowDefs

/-!
# The level determines the point for a model-adapted flow

`Work.Drive.N2.level_mono_of_modelAdaptedFlow`: on the orbits of the model-adapted level flow of
`Work.Drive.N2.exists_modelAdapted_levelFlow_chartODE` the value of `f` determines the point.

The flow raises `f` at unit speed off the model balls (`hlevel`) and, on the chart region `C i`, its
chart coordinates solve the model ODE (`hODE`), whose chart level `chartQ` rises at rate
`2 * ‖u‖ ^ 2 * chartMult (r i) (‖u‖ ^ 2) ∈ [0, 1]`.

The proof has three steps.

* The orbit function `g = f ∘ Φ (·, y)` is `C¹` (`hΦsm` and `hf` are smooth), its derivative is
  `2 * β * (u₀ ^ 2 + u₁ ^ 2) ≥ 0` inside a model ball (`hODE`), is `1` at points at which the orbit
  avoids the model balls (`hlevel`), and the set where the derivative is `≥ 0` is closed; the
  elementary closure argument then gives `0 ≤ deriv g` everywhere, so `g` is non-decreasing.
* If `g s = g t` with `s ≤ t` then `g` is constant on `[s, t]`, hence `deriv g = 0` on `(s, t)`.  At
  such a point the orbit must lie in a model ball: off the model balls the derivative is `1` (if the
  orbit avoids the balls near the point) or the point is a limit of points of model balls, in which
  case the vanishing of the derivative at those points bounds the chart norm by `r ^ 2 / 2` and the
  bound passes to the limit.
* Consequently the orbit is locally constant on the right at every `σ ∈ [s, t)`: the vanishing of
  the derivative inside the model ball `i` forces the chart velocity to vanish at every interior
  point of the piece (the factor `chartMult` is `> 0` exactly outside the core `‖u‖ ^ 2 ≤ r ^ 2 / 2`),
  and the chart coordinates are constant there by the mean value theorem.  The supremum argument then
  shows that the orbit is constant on the whole of `[s, t]`.

The symmetric case `t ≤ s` follows by restarting the orbit at `Φ (t, y)` (`hΦcomp`).
-/

namespace Work.Drive.N2

open scoped Manifold ContDiff Topology
open Set Function Filter

variable {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]

set_option maxHeartbeats 2000000

/-! ## Elementary bricks -/

/-- The model ball of a chart is open. -/
lemma levelMono_isOpen_modelBall (φ : OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (r : ℝ) : IsOpen (modelBall φ r) := by
  have h : modelBall φ r = φ.source ∩ φ ⁻¹' Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r := by
    ext y
    simp only [modelBall, mem_ofPred_eq, mem_inter_iff, mem_preimage, Metric.mem_ball,
      dist_eq_norm, sub_zero]
  rw [h]
  exact φ.isOpen_inter_preimage Metric.isOpen_ball

/-- The sum of the squares of the two coordinates of a point of `ℝ²`. -/
lemma levelMono_coord_sq (u : EuclideanSpace ℝ (Fin 2)) :
    (u 0) ^ 2 + (u 1) ^ 2 = (‖u‖ : ℝ) ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  norm_num [Fin.sum_univ_two]

/-- **The level law, restarted at an arbitrary time.**  If the orbit piece over `[τ₁, τ₂]` avoids
all model balls, then `f` rises at unit speed over it. -/
lemma levelMono_levelLaw {f : M → ℝ} {Φ : ℝ × M → M}
    (hΦcomp : ∀ (a b : ℝ) (y : M), Φ (a, Φ (b, y)) = Φ (a + b, y))
    {ι : Type*} (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2))) (r : ι → ℝ)
    (hlevel : ∀ (y : M) (t : ℝ), (∀ i, y ∉ modelBall (φ i) (r i)) →
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), ∀ i, Φ (u, y) ∉ modelBall (φ i) (r i)) →
      f (Φ (t, y)) = f y + t)
    {y : M} {τ₁ τ₂ : ℝ} (hτ : τ₁ ≤ τ₂)
    (hav : ∀ u ∈ Set.Icc τ₁ τ₂, ∀ i, Φ (u, y) ∉ modelBall (φ i) (r i)) :
    f (Φ (τ₂, y)) = f (Φ (τ₁, y)) + (τ₂ - τ₁) := by
  have h0 : min 0 (τ₂ - τ₁) = 0 := min_eq_left (by linarith)
  have h1 : max 0 (τ₂ - τ₁) = τ₂ - τ₁ := max_eq_right (by linarith)
  have hbase : ∀ i, Φ (τ₁, y) ∉ modelBall (φ i) (r i) := fun i => hav τ₁ ⟨le_rfl, hτ⟩ i
  have hmain := hlevel (Φ (τ₁, y)) (τ₂ - τ₁) hbase (fun u hu i => by
    rw [h0, h1] at hu
    have hu' : u + τ₁ ∈ Set.Icc τ₁ τ₂ := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    rw [hΦcomp u τ₁ y]
    exact hav (u + τ₁) hu' i)
  have hpt : Φ (τ₂ - τ₁, Φ (τ₁, y)) = Φ (τ₂, y) := by
    rw [hΦcomp (τ₂ - τ₁) τ₁ y, show τ₂ - τ₁ + τ₁ = τ₂ by ring]
  rw [hpt] at hmain
  exact hmain

/-- **The chart ODE, restarted at an arbitrary time.** -/
lemma levelMono_ode {Φ : ℝ × M → M}
    (hΦcomp : ∀ (a b : ℝ) (y : M), Φ (a, Φ (b, y)) = Φ (a + b, y))
    {ι : Type*} (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (s₁ s₂ : ι → ℝ) (β : ι → ℝ → ℝ) {C : ι → Set M}
    (hode : ∀ (i : ι) (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∈ C i) →
      HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 0)
          (β i (‖φ i (Φ (t, y))‖ ^ 2) * (s₁ i * φ i (Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 1)
          (β i (‖φ i (Φ (t, y))‖ ^ 2) * (s₂ i * φ i (Φ (t, y)) 1)) t)
    {y : M} {τ₁ τ₂ : ℝ} (hτ : τ₁ ≤ τ₂) (i : ι)
    (hav : ∀ u ∈ Set.Icc τ₁ τ₂, Φ (u, y) ∈ C i) :
    HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 0)
        (β i (‖φ i (Φ (τ₂, y))‖ ^ 2) * (s₁ i * φ i (Φ (τ₂, y)) 0)) τ₂ ∧
    HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 1)
        (β i (‖φ i (Φ (τ₂, y))‖ ^ 2) * (s₂ i * φ i (Φ (τ₂, y)) 1)) τ₂ := by
  have h0 : min 0 (τ₂ - τ₁) = 0 := min_eq_left (by linarith)
  have h1 : max 0 (τ₂ - τ₁) = τ₂ - τ₁ := max_eq_right (by linarith)
  have hmem : ∀ u ∈ Set.Icc (min 0 (τ₂ - τ₁)) (max 0 (τ₂ - τ₁)),
      Φ (u, Φ (τ₁, y)) ∈ C i := by
    intro u hu
    rw [h0, h1] at hu
    have hu' : u + τ₁ ∈ Set.Icc τ₁ τ₂ := ⟨by linarith [hu.1], by linarith [hu.2]⟩
    rw [hΦcomp u τ₁ y]
    exact hav (u + τ₁) hu'
  have hpt : Φ (τ₂ - τ₁, Φ (τ₁, y)) = Φ (τ₂, y) := by
    rw [hΦcomp (τ₂ - τ₁) τ₁ y, show τ₂ - τ₁ + τ₁ = τ₂ by ring]
  obtain ⟨hd0, hd1⟩ := hode i (Φ (τ₁, y)) (τ₂ - τ₁) hmem
  rw [hpt] at hd0 hd1
  have hshift0 : ∀ x : ℝ,
      (fun s : ℝ => φ i (Φ (s, Φ (τ₁, y))) 0) (-τ₁ + x) = φ i (Φ (x, y)) 0 := by
    intro x
    show φ i (Φ (-τ₁ + x, Φ (τ₁, y))) 0 = φ i (Φ (x, y)) 0
    rw [hΦcomp (-τ₁ + x) τ₁ y, show -τ₁ + x + τ₁ = x by ring]
  have hshift1 : ∀ x : ℝ,
      (fun s : ℝ => φ i (Φ (s, Φ (τ₁, y))) 1) (-τ₁ + x) = φ i (Φ (x, y)) 1 := by
    intro x
    show φ i (Φ (-τ₁ + x, Φ (τ₁, y))) 1 = φ i (Φ (x, y)) 1
    rw [hΦcomp (-τ₁ + x) τ₁ y, show -τ₁ + x + τ₁ = x by ring]
  constructor
  · have h0'' : HasDerivAt (fun s : ℝ => φ i (Φ (s, Φ (τ₁, y))) 0)
        (β i (‖φ i (Φ (τ₂, y))‖ ^ 2) * (s₁ i * φ i (Φ (τ₂, y)) 0)) (-τ₁ + τ₂) := by
      rw [show -τ₁ + τ₂ = τ₂ - τ₁ by ring]; exact hd0
    have h := HasDerivAt.comp_const_add (𝕜 := ℝ) (-τ₁) τ₂ h0''
    simpa only [hshift0] using h
  · have h1'' : HasDerivAt (fun s : ℝ => φ i (Φ (s, Φ (τ₁, y))) 1)
        (β i (‖φ i (Φ (τ₂, y))‖ ^ 2) * (s₂ i * φ i (Φ (τ₂, y)) 1)) (-τ₁ + τ₂) := by
      rw [show -τ₁ + τ₂ = τ₂ - τ₁ by ring]; exact hd1
    have h := HasDerivAt.comp_const_add (𝕜 := ℝ) (-τ₁) τ₂ h1''
    simpa only [hshift1] using h

/-- The chain rule for `chartQ` along a curve solving the chart ODE. -/
lemma levelMono_hasDerivAt_chartQ {Φ : ℝ × M → M}
    {ι : Type*} (i : ι) (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (s₁ s₂ : ι → ℝ) (β : ℝ) {y : M} {τ : ℝ}
    (hsgn : (s₁ i = 1 ∨ s₁ i = -1) ∧ (s₂ i = 1 ∨ s₂ i = -1))
    (h0 : HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 0)
        (β * (s₁ i * φ i (Φ (τ, y)) 0)) τ)
    (h1 : HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 1)
        (β * (s₂ i * φ i (Φ (τ, y)) 1)) τ) :
    HasDerivAt (fun σ : ℝ => chartQ (φ i) (s₁ i) (s₂ i) (Φ (σ, y)))
      (2 * β * ((φ i (Φ (τ, y)) 0) ^ 2 + (φ i (Φ (τ, y)) 1) ^ 2)) τ := by
  have hp0 := (h0.pow 2).const_mul (s₁ i)
  have hp1 := (h1.pow 2).const_mul (s₂ i)
  have hsum := hp0.add hp1
  have hs1 : s₁ i * s₁ i = 1 := by rcases hsgn.1 with h | h <;> rw [h] <;> norm_num
  have hs2 : s₂ i * s₂ i = 1 := by rcases hsgn.2 with h | h <;> rw [h] <;> norm_num
  have hfun : (fun σ : ℝ => chartQ (φ i) (s₁ i) (s₂ i) (Φ (σ, y)))
      = fun σ : ℝ => s₁ i * (φ i (Φ (σ, y)) 0) ^ 2 + s₂ i * (φ i (Φ (σ, y)) 1) ^ 2 := rfl
  rw [hfun]
  have hval : s₁ i * (2 * (φ i (Φ (τ, y)) 0) ^ (2 - 1) * (β * (s₁ i * φ i (Φ (τ, y)) 0)))
      + s₂ i * (2 * (φ i (Φ (τ, y)) 1) ^ (2 - 1) * (β * (s₂ i * φ i (Φ (τ, y)) 1)))
      = 2 * β * ((φ i (Φ (τ, y)) 0) ^ 2 + (φ i (Φ (τ, y)) 1) ^ 2) := by
    have h21 : (2 : ℕ) - 1 = 1 := rfl
    simp only [h21, pow_one]
    linear_combination (2 * (φ i (Φ (τ, y)) 0) ^ 2 * β) * hs1
      + (2 * (φ i (Φ (τ, y)) 1) ^ 2 * β) * hs2
  exact hval ▸ hsum

/-- **Vanishing chart velocity.**  Inside a model ball, if `chartMult` times the chart level rate
vanishes, then the chart coordinates have derivative zero. -/
lemma levelMono_vel_zero_of_mul_zero {Φ : ℝ × M → M}
    (hΦcont : Continuous Φ)
    (hΦcomp : ∀ (a b : ℝ) (y : M), Φ (a, Φ (b, y)) = Φ (a + b, y))
    {ι : Type*} (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (s₁ s₂ r : ι → ℝ) (C : ι → Set M) (hCball : ∀ i, modelBall (φ i) (r i) ⊆ C i)
    (hode : ∀ (i : ι) (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∈ C i) →
      HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 0)
          (chartMult (r i) (‖φ i (Φ (t, y))‖ ^ 2) * (s₁ i * φ i (Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 1)
          (chartMult (r i) (‖φ i (Φ (t, y))‖ ^ 2) * (s₂ i * φ i (Φ (t, y)) 1)) t)
    {y : M} {i : ι} {τ : ℝ}
    (hsgn : (s₁ i = 1 ∨ s₁ i = -1) ∧ (s₂ i = 1 ∨ s₂ i = -1))
    (hb : Φ (τ, y) ∈ modelBall (φ i) (r i))
    (hmul : chartMult (r i) (‖φ i (Φ (τ, y))‖ ^ 2)
      * ((φ i (Φ (τ, y)) 0) ^ 2 + (φ i (Φ (τ, y)) 1) ^ 2) = 0) :
    HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 0) 0 τ ∧
    HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 1) 0 τ := by
  have hu0 : (φ i (Φ (τ, y))) 0 = 0 ∨ chartMult (r i) (‖φ i (Φ (τ, y))‖ ^ 2) = 0 := by
    rcases mul_eq_zero.mp hmul with h | h
    · exact Or.inr h
    · refine Or.inl ?_
      have hsq : ((φ i (Φ (τ, y))) 0) ^ 2 = 0 := by
        nlinarith [h, sq_nonneg ((φ i (Φ (τ, y))) 1)]
      exact sq_eq_zero_iff.mp hsq
  have hu1 : (φ i (Φ (τ, y))) 1 = 0 ∨ chartMult (r i) (‖φ i (Φ (τ, y))‖ ^ 2) = 0 := by
    rcases mul_eq_zero.mp hmul with h | h
    · exact Or.inr h
    · refine Or.inl ?_
      have hsq : ((φ i (Φ (τ, y))) 1) ^ 2 = 0 := by
        nlinarith [h, sq_nonneg ((φ i (Φ (τ, y))) 0)]
      exact sq_eq_zero_iff.mp hsq
  have hcoord0 : ∀ c : ℝ,
      chartMult (r i) (‖φ i (Φ (τ, y))‖ ^ 2) * (c * φ i (Φ (τ, y)) 0) = 0 := by
    intro c
    rcases hu0 with h | h
    · rw [h, mul_zero, mul_zero]
    · rw [h, zero_mul]
  have hcoord1 : ∀ c : ℝ,
      chartMult (r i) (‖φ i (Φ (τ, y))‖ ^ 2) * (c * φ i (Φ (τ, y)) 1) = 0 := by
    intro c
    rcases hu1 with h | h
    · rw [h, mul_zero, mul_zero]
    · rw [h, zero_mul]
  have hγ : Continuous fun σ : ℝ => Φ (σ, y) :=
    hΦcont.comp (continuous_id.prodMk continuous_const)
  obtain ⟨ε, hε, hεsub⟩ := Metric.eventually_nhds_iff.mp
    (hγ.continuousAt.preimage_mem_nhds ((levelMono_isOpen_modelBall (φ i) (r i)).mem_nhds hb))
  set δ : ℝ := min ε 1 / 2 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]; exact div_pos (lt_min hε one_pos) two_pos
  have hδε : δ < ε := by
    have h1 : min ε 1 ≤ ε := min_le_left _ _
    rw [hδdef]; linarith
  have hle : τ - δ ≤ τ := by linarith
  have hav : ∀ u ∈ Set.Icc (τ - δ) τ, Φ (u, y) ∈ C i := by
    intro u hu
    exact hCball i (hεsub (by
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith [hu.1, hu.2, hδε]))
  obtain ⟨hd0, hd1⟩ := levelMono_ode hΦcomp φ s₁ s₂ (fun i => chartMult (r i)) hode hle i hav
  exact ⟨by simpa [hcoord0 (s₁ i)] using hd0, by simpa [hcoord1 (s₂ i)] using hd1⟩

/-- A function on an interval whose derivative vanishes at every interior point (and which is
continuous on the interval) is constant. -/
lemma levelMono_const_of_hasDerivAt_zero {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn g (Set.Icc a b))
    (hderiv : ∀ σ ∈ Set.Ioo a b, HasDerivAt g 0 σ) : g b = g a := by
  have hdiff : DifferentiableOn ℝ g (interior (Set.Icc a b)) := by
    intro σ hσ
    rw [interior_Icc] at hσ
    exact (hderiv σ hσ).differentiableAt.differentiableWithinAt
  have hnn : ∀ σ ∈ interior (Set.Icc a b), 0 ≤ deriv g σ := by
    intro σ hσ
    rw [interior_Icc] at hσ
    have h := (hderiv σ hσ).deriv
    rw [h]
  have hmono1 := monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont hdiff hnn
  have hle0 : ∀ σ ∈ interior (Set.Icc a b), 0 ≤ deriv (fun s : ℝ => -g s) σ := by
    intro σ hσ
    rw [interior_Icc] at hσ
    have h : deriv (fun s : ℝ => -g s) σ = 0 := by simpa using ((hderiv σ hσ).neg).deriv
    rw [h]
  have hdiff2 : DifferentiableOn ℝ (fun s : ℝ => -g s) (interior (Set.Icc a b)) := by
    intro σ hσ
    rw [interior_Icc] at hσ
    exact (hderiv σ hσ).neg.differentiableAt.differentiableWithinAt
  have hmono2 := monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont.neg hdiff2 hle0
  exact le_antisymm
    (by have := hmono2 ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab; simpa using this)
    (hmono1 ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab)

/-- The `Icc` form of `levelMono_const_of_hasDerivAt_zero`. -/
lemma levelMono_const_on_Icc_of_hasDerivAt_zero {g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn g (Set.Icc a b))
    (hderiv : ∀ σ ∈ Set.Ioo a b, HasDerivAt g 0 σ) :
    ∀ σ ∈ Set.Icc a b, g σ = g a := by
  intro σ hσ
  rcases lt_or_ge σ a with h | h
  · rw [le_antisymm (le_of_lt h) hσ.1]
  · exact levelMono_const_of_hasDerivAt_zero h (hcont.mono (Set.Icc_subset_Icc le_rfl hσ.2))
      (fun z hz => hderiv z ⟨hz.1, hz.2.trans_le hσ.2⟩)

/-! ## The target -/

theorem level_mono_of_modelAdaptedFlow {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (f : M → ℝ)
    (hf : ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) (modelWithCornersSelf ℝ ℝ)
      ((⊤ : ℕ∞) : WithTop ℕ∞) f)
    {ι : Type*} [Fintype ι]
    (x : ι → M) (φ : ι → OpenPartialHomeomorph M (EuclideanSpace ℝ (Fin 2)))
    (s₁ s₂ r : ι → ℝ) (hr : ∀ i, 0 < r i)
    (hsgn : ∀ i, (s₁ i = 1 ∨ s₁ i = -1) ∧ (s₂ i = 1 ∨ s₂ i = -1))
    (hval : ∀ i y, y ∈ (φ i).source →
      f y = f (x i) + Work.Drive.N2.chartQ (φ i) (s₁ i) (s₂ i) y)
    (C : ι → Set M) (hCsub : ∀ i, C i ⊆ (φ i).source)
    (hCcl : ∀ i, closure (C i) ⊆ (φ i).source)
    (hCball : ∀ i, Work.Drive.N2.modelBall (φ i) (r i) ⊆ C i)
    (Φ : ℝ × M → M)
    (hΦsm : ContMDiff ((modelWithCornersSelf ℝ ℝ).prod
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (hΦ0 : ∀ y, Φ (0, y) = y)
    (hΦcomp : ∀ a b y, Φ (a, Φ (b, y)) = Φ (a + b, y))
    (hlevel : ∀ (y : M) (t : ℝ), (∀ i, y ∉ Work.Drive.N2.modelBall (φ i) (r i)) →
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), ∀ i,
        Φ (u, y) ∉ Work.Drive.N2.modelBall (φ i) (r i)) →
      f (Φ (t, y)) = f y + t)
    (hODE : ∀ (i : ι) (y : M) (t : ℝ),
      (∀ u ∈ Set.Icc (min 0 t) (max 0 t), Φ (u, y) ∈ C i) →
      HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 0)
        (Work.Drive.N2.chartMult (r i) (‖φ i (Φ (t, y))‖ ^ 2) * (s₁ i * φ i (Φ (t, y)) 0)) t ∧
      HasDerivAt (fun σ : ℝ => φ i (Φ (σ, y)) 1)
        (Work.Drive.N2.chartMult (r i) (‖φ i (Φ (t, y))‖ ^ 2) * (s₂ i * φ i (Φ (t, y)) 1)) t) :
    ∀ (y : M) (s t : ℝ), f (Φ (s, y)) = f (Φ (t, y)) → Φ (s, y) = Φ (t, y) := by
  have hΦcont : Continuous Φ := hΦsm.continuous
  have hfcont : Continuous f := hf.continuous
  -- the level function along an orbit is `C¹`
  have hFcd : ∀ y : M, ContDiff ℝ 1 (fun σ : ℝ => f (Φ (σ, y))) := by
    intro y
    have hcur : ContMDiff (modelWithCornersSelf ℝ ℝ)
        ((modelWithCornersSelf ℝ ℝ).prod (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))))
        ((⊤ : ℕ∞) : WithTop ℕ∞) (fun σ : ℝ => (σ, y)) :=
      ContMDiff.prodMk contMDiff_id contMDiff_const
    have h1 : ContMDiff (modelWithCornersSelf ℝ ℝ)
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun σ : ℝ => Φ (σ, y)) := hΦsm.comp hcur
    have h2 : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ)
        ((⊤ : ℕ∞) : WithTop ℕ∞) (fun σ : ℝ => f (Φ (σ, y))) := hf.comp h1
    have h3 : ContMDiff (modelWithCornersSelf ℝ ℝ) (modelWithCornersSelf ℝ ℝ) (1 : ℕ)
        (fun σ : ℝ => f (Φ (σ, y))) := (contMDiff_infty.mp h2) 1
    have h4 : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (fun σ : ℝ => f (Φ (σ, y))) :=
      (contMDiff_iff_contDiff).mp h3
    simpa using h4
  -- the derivative inside a model ball
  have hderiv_ball : ∀ (y : M) (i : ι) (τ : ℝ),
      Φ (τ, y) ∈ Work.Drive.N2.modelBall (φ i) (r i) →
      deriv (fun σ : ℝ => f (Φ (σ, y))) τ
        = 2 * Work.Drive.N2.chartMult (r i) (‖φ i (Φ (τ, y))‖ ^ 2)
          * ((φ i (Φ (τ, y)) 0) ^ 2 + (φ i (Φ (τ, y)) 1) ^ 2) := by
    intro y i τ hb
    have hγ : Continuous fun σ : ℝ => Φ (σ, y) :=
      hΦcont.comp (continuous_id.prodMk continuous_const)
    have hnhds : (fun σ : ℝ => Φ (σ, y)) ⁻¹'
        Work.Drive.N2.modelBall (φ i) (r i) ∈ 𝓝 τ :=
      hγ.continuousAt.preimage_mem_nhds ((levelMono_isOpen_modelBall (φ i) (r i)).mem_nhds hb)
    obtain ⟨ε, hε, hεsub⟩ := Metric.eventually_nhds_iff.mp hnhds
    set δ : ℝ := min ε 1 / 2 with hδdef
    have hδpos : 0 < δ := by
      rw [hδdef]; exact div_pos (lt_min hε one_pos) two_pos
    have hδε : δ < ε := by
      have h1 : min ε 1 ≤ ε := min_le_left _ _
      rw [hδdef]; linarith
    have hle : τ - δ ≤ τ := by linarith
    have hav : ∀ u ∈ Set.Icc (τ - δ) τ, Φ (u, y) ∈ C i := by
      intro u hu
      exact hCball i (hεsub (by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [hu.1, hu.2, hδε]))
    obtain ⟨hd0, hd1⟩ := levelMono_ode hΦcomp φ s₁ s₂ (fun i => chartMult (r i)) hODE hle i hav
    have hQderiv := levelMono_hasDerivAt_chartQ i φ s₁ s₂
      (chartMult (r i) (‖φ i (Φ (τ, y))‖ ^ 2)) (hsgn i) hd0 hd1
    have hev : (fun σ : ℝ => f (Φ (σ, y)))
        =ᶠ[𝓝 τ] (fun σ : ℝ => f (x i) + chartQ (φ i) (s₁ i) (s₂ i) (Φ (σ, y))) := by
      filter_upwards [hnhds] with σ hσ
      rw [hval i (Φ (σ, y)) hσ.1]
    have hmain : HasDerivAt (fun σ : ℝ => f (Φ (σ, y)))
        (2 * chartMult (r i) (‖φ i (Φ (τ, y))‖ ^ 2)
          * ((φ i (Φ (τ, y)) 0) ^ 2 + (φ i (Φ (τ, y)) 1) ^ 2)) τ :=
      (hQderiv.const_add (f (x i))).congr_of_eventuallyEq hev
    exact hmain.deriv
  -- the derivative at points at which the orbit avoids the model balls
  have hderiv_one : ∀ (y : M) (τ : ℝ),
      (∀ᶠ σ in 𝓝 τ, ∀ i, Φ (σ, y) ∉ Work.Drive.N2.modelBall (φ i) (r i)) →
      deriv (fun σ : ℝ => f (Φ (σ, y))) τ = 1 := by
    intro y τ hav
    obtain ⟨ε, hε, hεsub⟩ := Metric.eventually_nhds_iff.mp hav
    have hev : (fun σ : ℝ => f (Φ (σ, y))) =ᶠ[𝓝 τ] (fun σ : ℝ => f (Φ (τ, y)) + (σ - τ)) := by
      filter_upwards [Metric.ball_mem_nhds τ hε] with σ hσ
      have hd : dist σ τ < ε := hσ
      have hdb : -(ε) < σ - τ ∧ σ - τ < ε := by
        rw [Real.dist_eq] at hd; exact abs_lt.mp hd
      rcases le_total τ σ with hle | hle
      · have hsub : ∀ u ∈ Set.Icc τ σ, dist u τ < ε := by
          intro u hu
          rw [Real.dist_eq, abs_lt]
          constructor <;> linarith [hu.1, hu.2, hε, hdb.1, hdb.2]
        exact levelMono_levelLaw hΦcomp φ r hlevel hle (fun u hu i => hεsub (hsub u hu) i)
      · have hsub : ∀ u ∈ Set.Icc σ τ, dist u τ < ε := by
          intro u hu
          rw [Real.dist_eq, abs_lt]
          constructor <;> linarith [hu.1, hu.2, hε, hdb.1, hdb.2]
        have h := levelMono_levelLaw hΦcomp φ r hlevel hle (fun u hu i => hεsub (hsub u hu) i)
        linarith
    have h1 : HasDerivAt (fun σ : ℝ => f (Φ (τ, y)) + (σ - τ)) 1 τ :=
      ((hasDerivAt_id τ).sub_const τ).const_add (f (Φ (τ, y)))
    exact (h1.congr_of_eventuallyEq hev).deriv
  -- the derivative is nonnegative everywhere
  have hderiv_nonneg : ∀ (y : M) (τ : ℝ), 0 ≤ deriv (fun σ : ℝ => f (Φ (σ, y))) τ := by
    intro y τ
    by_contra hcon
    rw [not_le] at hcon
    have hclosed : IsClosed {σ : ℝ | 0 ≤ deriv (fun σ : ℝ => f (Φ (σ, y))) σ} :=
      isClosed_le continuous_const ((hFcd y).continuous_deriv (by norm_num))
    have hmem : τ ∈ closure {σ : ℝ | 0 ≤ deriv (fun σ : ℝ => f (Φ (σ, y))) σ} := by
      rw [Metric.mem_closure_iff]
      intro ρ hρ
      by_cases h1 : Φ (τ, y) ∈ ⋃ i, Work.Drive.N2.modelBall (φ i) (r i)
      · obtain ⟨i, hi⟩ := mem_iUnion.mp h1
        refine ⟨τ, ?_, by simpa using hρ⟩
        change 0 ≤ deriv (fun σ : ℝ => f (Φ (σ, y))) τ
        rw [hderiv_ball y i τ hi]
        have ha : (0 : ℝ) ≤ 2 * chartMult (r i) (‖φ i (Φ (τ, y))‖ ^ 2) :=
          mul_nonneg (by norm_num) (chartMult_nonneg _ _)
        have hb : (0 : ℝ) ≤ (φ i (Φ (τ, y)) 0) ^ 2 + (φ i (Φ (τ, y)) 1) ^ 2 := by positivity
        exact mul_nonneg ha hb
      · by_cases h2 : ∃ σ : ℝ, dist σ τ < ρ ∧ Φ (σ, y) ∈ ⋃ i, Work.Drive.N2.modelBall (φ i) (r i)
        · obtain ⟨σ, hσ, hσ'⟩ := h2
          obtain ⟨i, hi⟩ := mem_iUnion.mp hσ'
          refine ⟨σ, ?_, by rw [dist_comm]; exact hσ⟩
          change 0 ≤ deriv (fun σ : ℝ => f (Φ (σ, y))) σ
          rw [hderiv_ball y i σ hi]
          have ha : (0 : ℝ) ≤ 2 * chartMult (r i) (‖φ i (Φ (σ, y))‖ ^ 2) :=
            mul_nonneg (by norm_num) (chartMult_nonneg _ _)
          have hb : (0 : ℝ) ≤ (φ i (Φ (σ, y)) 0) ^ 2 + (φ i (Φ (σ, y)) 1) ^ 2 := by positivity
          exact mul_nonneg ha hb
        · push_neg at h2
          refine ⟨τ, ?_, by simpa using hρ⟩
          have hav : ∀ᶠ σ in 𝓝 τ, ∀ i, Φ (σ, y) ∉ Work.Drive.N2.modelBall (φ i) (r i) := by
            refine Filter.eventually_of_mem (Metric.ball_mem_nhds τ hρ) ?_
            intro σ hσ i hi
            exact h2 σ hσ (mem_iUnion.mpr ⟨i, hi⟩)
          change 0 ≤ deriv (fun σ : ℝ => f (Φ (σ, y))) τ
          rw [hderiv_one y τ hav]
          norm_num
    exact absurd (hclosed.closure_subset hmem) (not_le.mpr hcon)
  -- monotonicity along orbits
  have hmono_all : ∀ y : M, Monotone (fun σ : ℝ => f (Φ (σ, y))) := by
    intro y
    exact monotone_of_deriv_nonneg ((hFcd y).differentiable (by norm_num)) (hderiv_nonneg y)
  -- the forward case
  have key : ∀ (y : M) (s t : ℝ), s ≤ t → f (Φ (s, y)) = f (Φ (t, y)) → Φ (s, y) = Φ (t, y) := by
    intro y s t hst hft
    rcases hst.eq_or_lt with h | hlt
    · rw [h]
    have hγ : Continuous fun σ : ℝ => Φ (σ, y) :=
      hΦcont.comp (continuous_id.prodMk continuous_const)
    have hmono := hmono_all y
    have hconst : ∀ σ ∈ Set.Icc s t, f (Φ (σ, y)) = f (Φ (s, y)) := by
      intro σ hσ
      refine le_antisymm ?_ (hmono hσ.1)
      rw [hft]
      exact hmono hσ.2
    have hderiv0 : ∀ σ ∈ Set.Ioo s t, deriv (fun σ : ℝ => f (Φ (σ, y))) σ = 0 := by
      intro σ hσ
      have hev : (fun τ : ℝ => f (Φ (τ, y))) =ᶠ[𝓝 σ] (fun _ => f (Φ (s, y))) := by
        filter_upwards [isOpen_Ioo.mem_nhds hσ] with τ hτ
        exact hconst τ ⟨le_of_lt hτ.1, le_of_lt hτ.2⟩
      exact ((hasDerivAt_const σ _).congr_of_eventuallyEq hev).deriv
    -- inside a model ball, vanishing derivative bounds the chart norm by `r ^ 2 / 2`
    have hcore : ∀ (k : ι) (τ : ℝ), Φ (τ, y) ∈ Work.Drive.N2.modelBall (φ k) (r k) →
        deriv (fun σ : ℝ => f (Φ (σ, y))) τ = 0 →
        (‖φ k (Φ (τ, y))‖ : ℝ) ^ 2 ≤ (r k) ^ 2 / 2 := by
      intro k τ hb hd
      have hprod : chartMult (r k) (‖φ k (Φ (τ, y))‖ ^ 2)
          * ((φ k (Φ (τ, y)) 0) ^ 2 + (φ k (Φ (τ, y)) 1) ^ 2) = 0 := by
        rw [hderiv_ball y k τ hb] at hd
        rcases mul_eq_zero.mp hd with h | h
        · rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' (by norm_num)
          · rw [h', zero_mul]
        · rw [h, mul_zero]
      rw [levelMono_coord_sq] at hprod
      by_contra hlt
      rw [not_le] at hlt
      have hψ0 : (‖φ k (Φ (τ, y))‖ : ℝ) ^ 2 = 0 := by
        rcases mul_eq_zero.mp hprod with h | h
        · exact absurd h (ne_of_gt (chartMult_pos (hr k) hlt))
        · exact h
      have hpos : (0 : ℝ) < (r k) ^ 2 / 2 := by
        have h1 : (0 : ℝ) < (r k) ^ 2 := pow_pos (hr k) 2
        linarith
      nlinarith
    -- inside a model ball, vanishing derivative kills the chart velocity
    have hvel : ∀ (k : ι) (τ : ℝ), Φ (τ, y) ∈ Work.Drive.N2.modelBall (φ k) (r k) →
        deriv (fun σ : ℝ => f (Φ (σ, y))) τ = 0 →
        HasDerivAt (fun σ : ℝ => φ k (Φ (σ, y)) 0) 0 τ ∧
        HasDerivAt (fun σ : ℝ => φ k (Φ (σ, y)) 1) 0 τ := by
      intro k τ hb hd
      have hmul : chartMult (r k) (‖φ k (Φ (τ, y))‖ ^ 2)
          * ((φ k (Φ (τ, y)) 0) ^ 2 + (φ k (Φ (τ, y)) 1) ^ 2) = 0 := by
        rw [hderiv_ball y k τ hb] at hd
        rcases mul_eq_zero.mp hd with h | h
        · rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' (by norm_num)
          · rw [h', zero_mul]
        · rw [h, mul_zero]
      exact levelMono_vel_zero_of_mul_zero hΦcont hΦcomp φ s₁ s₂ r C hCball hODE (hsgn k) hb hmul
    -- every interior point of `(s, t)` lies in a model ball
    have hball : ∀ σ ∈ Set.Ioo s t, ∃ i : ι,
        Φ (σ, y) ∈ Work.Drive.N2.modelBall (φ i) (r i) := by
      intro σ hσ
      by_contra hcon
      push_neg at hcon
      by_cases hav : ∃ δ > 0, ∀ u ∈ Set.Icc σ (σ + δ),
          ∀ i, Φ (u, y) ∉ Work.Drive.N2.modelBall (φ i) (r i)
      · -- the orbit avoids the model balls on a right neighbourhood: the level law
        obtain ⟨δ, hδ, havoid⟩ := hav
        set δ' : ℝ := min δ (t - σ) / 2 with hδ'def
        have hδ'pos : 0 < δ' := by
          have h1 : 0 < min δ (t - σ) := lt_min hδ (by linarith [hσ.2])
          rw [hδ'def]; positivity
        have hδ'lt : δ' < δ := by
          have h1 : min δ (t - σ) ≤ δ := min_le_left _ _
          rw [hδ'def]; linarith
        have hδ't : σ + δ' < t := by
          have h1 : min δ (t - σ) ≤ t - σ := min_le_right _ _
          rw [hδ'def]; linarith
        have havoid' : ∀ u ∈ Set.Icc σ (σ + δ'),
            ∀ i, Φ (u, y) ∉ Work.Drive.N2.modelBall (φ i) (r i) := by
          intro u hu i hi
          exact havoid u ⟨hu.1, le_trans hu.2 (by linarith [hδ'lt])⟩ i hi
        have hlaw := levelMono_levelLaw hΦcomp φ r hlevel
          (le_add_of_nonneg_right (le_of_lt hδ'pos)) havoid'
        have hc1 := hconst σ ⟨le_of_lt hσ.1, le_of_lt hσ.2⟩
        have hc2 := hconst (σ + δ') ⟨by linarith [hσ.1, hδ'pos], le_of_lt hδ't⟩
        rw [add_sub_cancel_left] at hlaw
        linarith
      · -- the orbit meets the model balls arbitrarily close on the right
        push_neg at hav
        have hacc : σ ∈ closure (⋃ i : ι, ((fun u : ℝ => Φ (u, y)) ⁻¹'
            Work.Drive.N2.modelBall (φ i) (r i)) ∩ Set.Ioi σ) := by
          rw [Metric.mem_closure_iff]
          intro ε hε
          obtain ⟨u, huIcc, i, hi⟩ := hav (ε / 2) (by linarith)
          have hu_ne : u ≠ σ := by
            intro h; rw [h] at hi; exact hcon i hi
          have hu_gt : σ < u := lt_of_le_of_ne huIcc.1 (Ne.symm hu_ne)
          have hd : dist σ u < ε := by
            rw [dist_comm, Real.dist_eq, abs_of_nonneg (by linarith [huIcc.1])]
            linarith [huIcc.2]
          exact ⟨u, mem_iUnion.mpr ⟨i, mem_inter (mem_preimage.mpr hi) hu_gt⟩, hd⟩
        obtain ⟨k, hk⟩ : ∃ k : ι, σ ∈ closure (((fun u : ℝ => Φ (u, y)) ⁻¹'
            Work.Drive.N2.modelBall (φ k) (r k)) ∩ Set.Ioi σ) := by
          rw [closure_iUnion_of_finite] at hacc
          exact mem_iUnion.mp hacc
        have hsrc : Φ (σ, y) ∈ (φ k).source := by
          refine hCcl k (closure_mono (hCball k) ?_)
          rw [mem_closure_iff_nhds] at hk ⊢
          intro V hV
          obtain ⟨u, huV, huB⟩ := hk ((fun u : ℝ => Φ (u, y)) ⁻¹' V)
            (hγ.continuousAt.preimage_mem_nhds hV)
          exact ⟨Φ (u, y), huV, huB.1⟩
        have hbound : (‖φ k (Φ (σ, y))‖ : ℝ) ^ 2 ≤ (r k) ^ 2 / 2 := by
          by_contra hb'
          rw [not_le] at hb'
          have hcomp : ContinuousAt (fun u : ℝ => φ k (Φ (u, y))) σ :=
            ContinuousAt.comp (x := σ) (f := fun u : ℝ => Φ (u, y))
              ((φ k).continuousAt hsrc) hγ.continuousAt
          have hcontψ : ContinuousAt (fun u : ℝ => (‖φ k (Φ (u, y))‖ : ℝ) ^ 2) σ :=
            (ContinuousAt.comp (x := σ) (f := fun u : ℝ => φ k (Φ (u, y)))
              continuous_norm.continuousAt hcomp).pow 2
          have hnb : (fun u : ℝ => (‖φ k (Φ (u, y))‖ : ℝ) ^ 2) ⁻¹'
              (Set.Ioi ((r k) ^ 2 / 2)) ∈ 𝓝 σ :=
            hcontψ.preimage_mem_nhds (isOpen_Ioi.mem_nhds hb')
          rw [mem_closure_iff_nhds] at hk
          obtain ⟨σ', hσ'V, hσ'B⟩ := hk (Set.Iio t ∩
            (fun u : ℝ => (‖φ k (Φ (u, y))‖ : ℝ) ^ 2) ⁻¹' (Set.Ioi ((r k) ^ 2 / 2)))
            (Filter.inter_mem (isOpen_Iio.mem_nhds hσ.2) hnb)
          have hbig : (r k) ^ 2 / 2 < (‖φ k (Φ (σ', y))‖ : ℝ) ^ 2 := hσ'V.2
          have hsmall := hcore k σ' hσ'B.1 (hderiv0 σ' ⟨hσ.1.trans hσ'B.2, hσ'V.1⟩)
          linarith
        exact hcon k ⟨hsrc, by
          have h2 : (‖φ k (Φ (σ, y))‖ : ℝ) ^ 2 < (r k) ^ 2 := by
            have hpos : (0 : ℝ) < (r k) ^ 2 := pow_pos (hr k) 2
            linarith
          nlinarith [norm_nonneg (φ k (Φ (σ, y))), hr k, h2]⟩
    -- the chart coordinates are constant on an interval inside one model ball
    have hcoord_local : ∀ (i : ι) (a b : ℝ), a ≤ b →
        (∀ u ∈ Set.Icc a b, Φ (u, y) ∈ Work.Drive.N2.modelBall (φ i) (r i)) →
        (∀ u ∈ Set.Ioo a b, u ∈ Set.Ioo s t) →
        ∀ j : Fin 2, φ i (Φ (b, y)) j = φ i (Φ (a, y)) j := by
      intro i a b hab hmem hint j
      have hcont_j : ContinuousOn (fun u : ℝ => φ i (Φ (u, y)) j) (Set.Icc a b) := by
        have hβ : ContinuousOn (fun u : ℝ => φ i (Φ (u, y))) (Set.Icc a b) := by
          intro u hu
          have hsrc : Φ (u, y) ∈ (φ i).source := (hmem u hu).1
          exact (ContinuousAt.comp (x := u) (f := fun z : ℝ => Φ (z, y))
            ((φ i).continuousAt hsrc) hγ.continuousAt).continuousWithinAt
        have hg : Continuous (fun v : EuclideanSpace ℝ (Fin 2) => v j) :=
          PiLp.continuous_apply (p := 2) (β := fun _ : Fin 2 => ℝ) j
        exact ContinuousOn.comp hg.continuousOn hβ (fun z _ => mem_univ _)
      have hderiv_j : ∀ u ∈ Set.Ioo a b,
          HasDerivAt (fun z : ℝ => φ i (Φ (z, y)) j) 0 u := by
        intro u hu
        obtain ⟨h0, h1⟩ := hvel i u (hmem u ⟨le_of_lt hu.1, le_of_lt hu.2⟩) (hderiv0 u (hint u hu))
        fin_cases j
        · exact h0
        · exact h1
      exact levelMono_const_on_Icc_of_hasDerivAt_zero hab hcont_j hderiv_j b ⟨hab, le_rfl⟩
    -- every interior point is a point of local constancy
    have hloc : ∀ σ ∈ Set.Ioo s t, ∃ ε > 0,
        ∀ σ' ∈ Set.Ioo (σ - ε) (σ + ε), Φ (σ', y) = Φ (σ, y) := by
      intro σ hσ
      obtain ⟨i, hi⟩ := hball σ hσ
      have hJopen : IsOpen ({u : ℝ | u ∈ Set.Ioo s t} ∩
          (fun u : ℝ => Φ (u, y)) ⁻¹' Work.Drive.N2.modelBall (φ i) (r i)) :=
        isOpen_Ioo.inter ((levelMono_isOpen_modelBall (φ i) (r i)).preimage hγ)
      obtain ⟨ε, hε, hεsub⟩ := Metric.eventually_nhds_iff.mp (hJopen.mem_nhds ⟨hσ, hi⟩)
      refine ⟨ε, hε, ?_⟩
      intro σ' hσ'
      have hdist : dist σ' σ < ε := by
        rw [Real.dist_eq, abs_lt]
        exact ⟨by linarith [hσ'.1], by linarith [hσ'.2]⟩
      have hJσ' := hεsub hdist
      rcases le_total σ σ' with hle | hle
      · have hmemI : ∀ u ∈ Set.Icc σ σ', Φ (u, y) ∈ Work.Drive.N2.modelBall (φ i) (r i) := by
          intro u hu
          exact (hεsub (by
            rw [Real.dist_eq, abs_lt]
            constructor <;> linarith [hu.1, hu.2, hσ'.1, hσ'.2])).2
        have hintI : ∀ u ∈ Set.Ioo σ σ', u ∈ Set.Ioo s t := by
          intro u hu
          exact ⟨by linarith [hσ.1, hu.1], by linarith [hJσ'.1.2, hu.2]⟩
        exact (φ i).injOn (hmemI σ' ⟨hle, le_rfl⟩).1 (hmemI σ ⟨le_rfl, hle⟩).1
          (PiLp.ext fun j => hcoord_local i σ σ' hle hmemI hintI j)
      · have hmemI : ∀ u ∈ Set.Icc σ' σ, Φ (u, y) ∈ Work.Drive.N2.modelBall (φ i) (r i) := by
          intro u hu
          exact (hεsub (by
            rw [Real.dist_eq, abs_lt]
            constructor <;> linarith [hu.1, hu.2, hσ'.1, hσ'.2])).2
        have hintI : ∀ u ∈ Set.Ioo σ' σ, u ∈ Set.Ioo s t := by
          intro u hu
          exact ⟨by linarith [hσ.1, hJσ'.1.1, hu.1], by linarith [hσ.2, hu.2]⟩
        exact ((φ i).injOn (hmemI σ ⟨hle, le_rfl⟩).1 (hmemI σ' ⟨le_rfl, hle⟩).1
          (PiLp.ext fun j => hcoord_local i σ' σ hle hmemI hintI j)).symm
    -- the orbit is constant on the open interval
    have hconst_int : ∀ σ ∈ Set.Ioo s t, ∀ σ' ∈ Set.Ioo s t, Φ (σ, y) = Φ (σ', y) := by
      haveI : PreconnectedSpace ↥(Set.Ioo s t) := Subtype.preconnectedSpace isPreconnected_Ioo
      have hlf : IsLocallyConstant (fun σ : ↥(Set.Ioo s t) => Φ ((σ : ℝ), y)) := by
        rw [IsLocallyConstant.iff_eventually_eq]
        intro σ
        obtain ⟨ε, hε, hεsub⟩ := hloc σ σ.2
        refine Filter.eventually_of_mem
          (continuous_subtype_val.continuousAt.preimage_mem_nhds
            (Metric.ball_mem_nhds (σ : ℝ) hε)) ?_
        intro σ' hσ'
        have hd : dist (σ' : ℝ) (σ : ℝ) < ε := hσ'
        rw [Real.dist_eq] at hd
        exact hεsub σ' ⟨by linarith [(abs_lt.mp hd).1], by linarith [(abs_lt.mp hd).2]⟩
      intro σ hσ σ' hσ'
      exact hlf.apply_eq_of_preconnectedSpace ⟨σ, hσ⟩ ⟨σ', hσ'⟩
    obtain ⟨σ₀, hσ₀⟩ : ∃ σ : ℝ, σ ∈ Set.Ioo s t := ⟨(s + t) / 2, ⟨by linarith, by linarith⟩⟩
    have hconst₀ : ∀ σ ∈ Set.Ioo s t, Φ (σ, y) = Φ (σ₀, y) := fun σ hσ => hconst_int σ hσ σ₀ hσ₀
    -- the left endpoint
    have hs_eq : Φ (s, y) = Φ (σ₀, y) := by
      set ψ := chartAt (EuclideanSpace ℝ (Fin 2)) (Φ (s, y)) with hψ
      have hmem_src : Φ (s, y) ∈ ψ.source := mem_chart_source _ _
      have hlim : Tendsto (fun σ : ℝ => ψ (Φ (σ, y))) (𝓝[>] s) (𝓝 (ψ (Φ (s, y)))) :=
        ((ContinuousAt.comp (x := s) (f := fun σ : ℝ => Φ (σ, y))
          (ψ.continuousAt hmem_src) hγ.continuousAt).tendsto).mono_left nhdsWithin_le_nhds
      have hmemIoo : Set.Ioo s t ∈ 𝓝[>] s := by
        have h1 : Set.Ioi s ∈ 𝓝[>] s := self_mem_nhdsWithin
        have h2 : Set.Iio t ∈ 𝓝[>] s := nhdsWithin_le_nhds (isOpen_Iio.mem_nhds hlt)
        rw [show Set.Ioo s t = Set.Ioi s ∩ Set.Iio t from rfl]
        exact Filter.inter_mem h1 h2
      have hev : (fun σ : ℝ => ψ (Φ (σ, y))) =ᶠ[𝓝[>] s] (fun _ => ψ (Φ (σ₀, y))) := by
        refine Filter.eventually_of_mem hmemIoo ?_
        intro σ hσ
        show ψ (Φ (σ, y)) = ψ (Φ (σ₀, y))
        rw [hconst₀ σ hσ]
      have hlim' : Tendsto (fun σ : ℝ => ψ (Φ (σ, y))) (𝓝[>] s) (𝓝 (ψ (Φ (σ₀, y)))) :=
        Tendsto.congr' hev.symm tendsto_const_nhds
      have hψeq : ψ (Φ (σ₀, y)) = ψ (Φ (s, y)) := tendsto_nhds_unique hlim' hlim
      have hsrc₀ : Φ (σ₀, y) ∈ ψ.source := by
        obtain ⟨η, hη, hηsub⟩ := Metric.eventually_nhds_iff.mp
          (hγ.continuousAt.preimage_mem_nhds ((ψ.open_source).mem_nhds hmem_src))
        set σ' : ℝ := s + min η (t - s) / 2 with hσ'def
        have hminpos : 0 < min η (t - s) := lt_min hη (by linarith)
        have hσ'Ioo : σ' ∈ Set.Ioo s t := ⟨by linarith, by
          have h1 : min η (t - s) ≤ t - s := min_le_right _ _
          linarith⟩
        have hdist : dist σ' s < η := by
          rw [Real.dist_eq, abs_of_nonneg (by linarith : (0 : ℝ) ≤ σ' - s)]
          have h1 : min η (t - s) ≤ η := min_le_left _ _
          linarith
        rw [← hconst₀ σ' hσ'Ioo]
        exact hηsub hdist
      exact (ψ.injOn hsrc₀ hmem_src hψeq).symm
    -- the right endpoint
    have ht_eq : Φ (t, y) = Φ (σ₀, y) := by
      set ψ := chartAt (EuclideanSpace ℝ (Fin 2)) (Φ (t, y)) with hψ
      have hmem_src : Φ (t, y) ∈ ψ.source := mem_chart_source _ _
      have hlim : Tendsto (fun σ : ℝ => ψ (Φ (σ, y))) (𝓝[<] t) (𝓝 (ψ (Φ (t, y)))) :=
        ((ContinuousAt.comp (x := t) (f := fun σ : ℝ => Φ (σ, y))
          (ψ.continuousAt hmem_src) hγ.continuousAt).tendsto).mono_left nhdsWithin_le_nhds
      have hmemIoo : Set.Ioo s t ∈ 𝓝[<] t := by
        have h1 : Set.Ioi s ∈ 𝓝[<] t := nhdsWithin_le_nhds (isOpen_Ioi.mem_nhds hlt)
        have h2 : Set.Iio t ∈ 𝓝[<] t := self_mem_nhdsWithin
        rw [show Set.Ioo s t = Set.Ioi s ∩ Set.Iio t from rfl]
        exact Filter.inter_mem h1 h2
      have hev : (fun σ : ℝ => ψ (Φ (σ, y))) =ᶠ[𝓝[<] t] (fun _ => ψ (Φ (σ₀, y))) := by
        refine Filter.eventually_of_mem hmemIoo ?_
        intro σ hσ
        show ψ (Φ (σ, y)) = ψ (Φ (σ₀, y))
        rw [hconst₀ σ hσ]
      have hlim' : Tendsto (fun σ : ℝ => ψ (Φ (σ, y))) (𝓝[<] t) (𝓝 (ψ (Φ (σ₀, y)))) :=
        Tendsto.congr' hev.symm tendsto_const_nhds
      have hψeq : ψ (Φ (σ₀, y)) = ψ (Φ (t, y)) := tendsto_nhds_unique hlim' hlim
      have hsrc₀ : Φ (σ₀, y) ∈ ψ.source := by
        obtain ⟨η, hη, hηsub⟩ := Metric.eventually_nhds_iff.mp
          (hγ.continuousAt.preimage_mem_nhds ((ψ.open_source).mem_nhds hmem_src))
        set σ' : ℝ := t - min η (t - s) / 2 with hσ'def
        have hminpos : 0 < min η (t - s) := lt_min hη (by linarith)
        have hσ'Ioo : σ' ∈ Set.Ioo s t := ⟨by
          have h1 : min η (t - s) ≤ t - s := min_le_right _ _
          linarith, by linarith⟩
        have hdist : dist σ' t < η := by
          rw [Real.dist_eq, abs_of_nonpos (by linarith : σ' - t ≤ 0)]
          have h1 : min η (t - s) ≤ η := min_le_left _ _
          linarith
        rw [← hconst₀ σ' hσ'Ioo]
        exact hηsub hdist
      exact (ψ.injOn hsrc₀ hmem_src hψeq).symm
    exact hs_eq.trans ht_eq.symm
  intro y s t hft
  rcases le_total s t with h | h
  · exact key y s t h hft
  · have h2 := key (Φ (t, y)) 0 (s - t) (by linarith) ?_
    · rw [hΦ0, hΦcomp (s - t) t y, show s - t + t = s by ring] at h2
      exact h2.symm
    · rw [hΦ0, hΦcomp (s - t) t y, show s - t + t = s by ring]
      exact hft.symm

end Work.Drive.N2
