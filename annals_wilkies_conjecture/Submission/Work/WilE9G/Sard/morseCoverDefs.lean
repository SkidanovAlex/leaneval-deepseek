import Mathlib
import Submission.Work.WilE9G.Sard.morseDefs

/-!
# Chart covers (vocabulary for Morse's criticality theorem)

A *chart cover* of a set `B` inside an ambient open set `R` is a countable family of chart data
`c i` (`Work.WilE9G.Sard.ChartDatum`, Morse's class `K_n`: a `C¹`, distance-non-decreasing
parametrisation of a ball) together with pieces `A i ⊆ B ∩ c i '' ball` covering `B`, such that all
the images of the *closed* balls stay inside `R`, and such that every function of a prescribed class
`P` is flat of the appropriate order along each piece, in the coordinates of the chart.

This is the conclusion of Morse's Theorem 3.7 in the "parametrisation" form used to state
`Work.WilE9G.Sard.morseCriticality`.  The extra parameter `R` (the ambient open set) is not part of
the final statement: it is needed to carry out the inductive proof inside open subsets of `ℝ^d`
(the parametrisation of a level set is only defined, and only `C^s`, on an open set).

The elementary lemmas below (a `C¹` map on a ball has a locally bounded derivative; flatness of the
coefficients of a differential gives flatness of the differential; the coefficient functions of a
`C^s` function are `C^{s-1}` on an open set) are the analytic inputs of the *upgrade* step
(Morse's Lemma 3.2) of the induction.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

namespace Work.WilE9G.Sard

open Set Metric Filter
open scoped Topology

noncomputable section

/-- A chart cover of a set `B` inside the ambient open set `R`, with flatness for the class of
functions `P`.  (This is a `Prop`: the whole point is the *existence* of a countable family.) -/
def ChartCover (s d : ℕ) (R B : Set (Fin d → ℝ)) (P : ((Fin d → ℝ) → ℝ) → Prop) : Prop :=
  ∃ (ι : Type) (_ : Countable ι) (c : ι → ChartDatum d) (A : ι → Set (Fin d → ℝ)),
    (∀ i, (c i).γ '' Metric.closedBall (c i).base (c i).rad ⊆ R) ∧
    (∀ i, A i ⊆ B) ∧
    (B ⊆ ⋃ i, A i) ∧
    (∀ i, A i ⊆ (c i).γ '' Metric.ball (c i).base (c i).rad) ∧
    (∀ G, P G → ∀ i, ∀ u ∈ Metric.ball (c i).base (c i).rad,
      (c i).γ u ∈ A i → FlatAt (fun v => G ((c i).γ v)) s u)

namespace ChartCover

variable {s d : ℕ} {R B B₁ B₂ B' : Set (Fin d → ℝ)} {P P' : ((Fin d → ℝ) → ℝ) → Prop}

/-- Change the class of functions for which flatness is claimed. -/
theorem mono (h : ChartCover s d R B P) (hPP' : ∀ G, P' G → P G) :
    ChartCover s d R B P' := by
  obtain ⟨ι, hcnt, c, A, h1, h2, h3, h4, h5⟩ := h
  exact ⟨ι, hcnt, c, A, h1, h2, h3, h4,
    fun G hG i u hu hgu => h5 G (hPP' G hG) i u hu hgu⟩

/-- The same cover, with the covered set shrunk (the pieces are intersected with `B'`). -/
theorem restrict (h : ChartCover s d R B P) (hB' : B' ⊆ B) : ChartCover s d R B' P := by
  obtain ⟨ι, hcnt, c, A, h1, h2, h3, h4, h5⟩ := h
  refine ⟨ι, hcnt, c, fun i => A i ∩ B', h1, ?_, ?_, ?_, ?_⟩
  · exact fun i => Set.inter_subset_right
  · intro y hy
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (h3 (hB' hy))
    exact Set.mem_iUnion.mpr ⟨i, hi, hy⟩
  · exact fun i => Set.inter_subset_left.trans (h4 i)
  · exact fun G hG i u hu hgu => h5 G hG i u hu hgu.1

/-- Union of two chart covers (the pieces are those of the two covers). -/
theorem union (h₁ : ChartCover s d R B₁ P) (h₂ : ChartCover s d R B₂ P)
    (hB₁ : B₁ ⊆ B) (hB₂ : B₂ ⊆ B) (hB : B ⊆ B₁ ∪ B₂) : ChartCover s d R B P := by
  obtain ⟨ι₁, hc₁, c₁, A₁, hi₁, hs₁, hcv₁, him₁, hf₁⟩ := h₁
  obtain ⟨ι₂, hc₂, c₂, A₂, hi₂, hs₂, hcv₂, him₂, hf₂⟩ := h₂
  refine ⟨ι₁ ⊕ ι₂, ?_, (fun i => match i with | Sum.inl a => c₁ a | Sum.inr a => c₂ a),
    (fun i => match i with | Sum.inl a => A₁ a | Sum.inr a => A₂ a), ?_, ?_, ?_, ?_, ?_⟩
  · haveI := hc₁
    haveI := hc₂
    infer_instance
  · intro i
    cases i with
    | inl a => exact hi₁ a
    | inr a => exact hi₂ a
  · intro i
    cases i with
    | inl a => exact (hs₁ a).trans hB₁
    | inr a => exact (hs₂ a).trans hB₂
  · intro y hy
    rcases hB hy with hy | hy
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcv₁ hy)
      exact Set.mem_iUnion.mpr ⟨Sum.inl i, hi⟩
    · obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcv₂ hy)
      exact Set.mem_iUnion.mpr ⟨Sum.inr i, hi⟩
  · intro i
    cases i with
    | inl a => exact him₁ a
    | inr a => exact him₂ a
  · intro G hG i u hu hgu
    cases i with
    | inl a => exact hf₁ G hG a u hu hgu
    | inr a => exact hf₂ G hG a u hu hgu

end ChartCover

/-! ## Elementary analytic inputs -/

/-- The operator norm of `L : ℝ^d → ℝ` is bounded by the sum of the absolute values of its
coefficients. -/
lemma norm_le_sum_coeff' {d : ℕ} (L : (Fin d → ℝ) →L[ℝ] ℝ) :
    ‖L‖ ≤ ∑ a : Fin d, ‖L (Pi.single a 1)‖ := by
  refine L.opNorm_le_bound (M := ∑ a : Fin d, ‖L (Pi.single a 1)‖) (by positivity) (fun v => ?_)
  have hv : v = ∑ a : Fin d, v a • (Pi.single a (1 : ℝ) : Fin d → ℝ) := by
    funext j
    rw [Finset.sum_apply]
    simp [Pi.single_apply, Finset.mem_univ]
  have h1 : L v = ∑ a : Fin d, v a • L (Pi.single a 1) := by
    conv_lhs => rw [hv]
    rw [map_sum]
    simp
  calc ‖L v‖ = ‖∑ a : Fin d, v a • L (Pi.single a 1)‖ := by rw [h1]
    _ ≤ ∑ a : Fin d, ‖v a • L (Pi.single a 1)‖ := norm_sum_le _ _
    _ = ∑ a : Fin d, ‖v a‖ * ‖L (Pi.single a 1)‖ := by simp [norm_smul]
    _ ≤ ∑ a : Fin d, ‖v‖ * ‖L (Pi.single a 1)‖ := by
      refine Finset.sum_le_sum (fun a _ => ?_)
      exact mul_le_mul_of_nonneg_right (norm_le_pi_norm v a) (norm_nonneg _)
    _ = (∑ a : Fin d, ‖L (Pi.single a 1)‖) * ‖v‖ := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun a _ => by ring)

/-- Flatness of the differential of a scalar function follows from the flatness of its
coefficients.  (For `d = 0` the differential vanishes identically.) -/
lemma flatAt_fderiv_scalar_of_coeffs {d r s : ℕ}
    {γ : (Fin r → ℝ) → (Fin d → ℝ)} {u : Fin r → ℝ} {G : (Fin d → ℝ) → ℝ}
    (h : ∀ a : Fin d, FlatAt (fun z => fderiv ℝ G (γ z) (Pi.single a 1)) s u) :
    FlatAt (fun z => fderiv ℝ G (γ z)) s u := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    intro ε hε
    refine ⟨1, one_pos, fun y _ => ?_⟩
    have hzero : fderiv ℝ G (γ y) = 0 := by
      ext v
      rw [Subsingleton.elim v 0, map_zero, zero_apply]
    simp only [hzero, norm_zero]
    positivity
  · intro ε hε
    set C : ℝ := (d : ℝ) with hCdef
    have hCpos : 0 < C := by rw [hCdef]; positivity
    have hε' : 0 < ε / C := div_pos hε hCpos
    choose ρ hρpos hρ using fun a : Fin d => h a (ε / C) hε'
    haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
    obtain ⟨a₀, ha₀⟩ := Finite.exists_min ρ
    refine ⟨ρ a₀, hρpos a₀, fun y hy => ?_⟩
    calc ‖fderiv ℝ G (γ y)‖
        ≤ ∑ a : Fin d, ‖fderiv ℝ G (γ y) (Pi.single a 1)‖ := norm_le_sum_coeff' _
      _ ≤ ∑ _a : Fin d, (ε / C) * ‖y - u‖ ^ s := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        exact hρ a y (le_trans hy (ha₀ a))
      _ = C * ((ε / C) * ‖y - u‖ ^ s) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
      _ = ε * ‖y - u‖ ^ s := by
        field_simp

/-- A map which is `C¹` on a closed ball has a locally bounded derivative at every point of the
open ball, and a small ball around that point on which it is (ambiently) differentiable and on
which the derivative is bounded; that small ball is contained in the original closed ball. -/
lemma exists_fderiv_norm_bound {t d : ℕ} {γ : (Fin t → ℝ) → (Fin d → ℝ)} {base : Fin t → ℝ}
    {rad : ℝ} (hγ : ContDiffOn ℝ 1 γ (Metric.closedBall base rad)) (hrad : 0 < rad)
    {u : Fin t → ℝ} (hu : u ∈ Metric.ball base rad) :
    ∃ L ρ : ℝ, 0 ≤ L ∧ 0 < ρ ∧ Metric.closedBall u ρ ⊆ Metric.closedBall base rad ∧
      (∀ z, ‖z - u‖ ≤ ρ → DifferentiableAt ℝ γ z) ∧
      (∀ z, ‖z - u‖ ≤ ρ → ‖fderiv ℝ γ z‖ ≤ L) := by
  have hub : ‖u - base‖ < rad := by
    rw [Metric.mem_ball, dist_eq_norm] at hu; exact hu
  set δ : ℝ := rad - ‖u - base‖ with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith
  have hbound2 : ∀ z, ‖z - base‖ ≤ ‖z - u‖ + ‖u - base‖ := by
    intro z
    have h3 := norm_add_le (z - u) (u - base)
    have he : (z - u) + (u - base) = z - base := by abel
    rwa [he] at h3
  have hmem : ∀ z, ‖z - u‖ ≤ δ / 2 → z ∈ Metric.ball base rad := by
    intro z hz
    rw [Metric.mem_ball, dist_eq_norm]
    rw [hδdef] at hz
    linarith [hbound2 z]
  have hnhds : ∀ z, ‖z - u‖ ≤ δ / 2 → Metric.closedBall base rad ∈ 𝓝 z := fun z hz =>
    Filter.mem_of_superset (IsOpen.mem_nhds Metric.isOpen_ball (hmem z hz))
      Metric.ball_subset_closedBall
  have hball : ∀ z, ‖z - u‖ ≤ δ / 2 → ContDiffAt ℝ 1 γ z := fun z hz =>
    hγ.contDiffAt (hnhds z hz)
  have hcont : ContinuousOn (fderiv ℝ γ) (Metric.closedBall u (δ / 2)) := by
    intro z hz
    have hzu : ‖z - u‖ ≤ δ / 2 := by
      rw [Metric.mem_closedBall, dist_eq_norm] at hz; exact hz
    exact ((hball z hzu).continuousAt_fderiv (by norm_num)).continuousWithinAt
  obtain ⟨C, hC⟩ := (isCompact_closedBall u (δ / 2)).exists_bound_of_continuousOn hcont
  refine ⟨max C 0, δ / 2, le_max_right _ _, by linarith, ?_, ?_, ?_⟩
  · intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz ⊢
    rw [hδdef] at hz
    linarith [hbound2 z]
  · intro z hz
    exact (hball z hz).differentiableAt (by norm_num)
  · intro z hz
    exact (hC z (by rwa [Metric.mem_closedBall, dist_eq_norm])).trans (le_max_left _ _)

/-- The coefficient functions of the derivative of a `C^s` function on an open set are `C^{s-1}`
on that set. -/
lemma contDiffOn_fderiv_coord {d s : ℕ} {R : Set (Fin d → ℝ)} (hR : IsOpen R) (hs : 1 ≤ s)
    {G : (Fin d → ℝ) → ℝ} (hG : ContDiffOn ℝ s G R) (j : Fin d) :
    ContDiffOn ℝ (s - 1) (fun y => fderiv ℝ G y (Pi.single j 1)) R := by
  have hcast : (1 : WithTop ℕ∞) + ((s - 1 : ℕ) : WithTop ℕ∞) = ((s : ℕ) : WithTop ℕ∞) := by
    rw [← Nat.cast_one, ← Nat.cast_add]
    congr 1
    omega
  have hle : ((s - 1 : ℕ) : WithTop ℕ∞) + (1 : WithTop ℕ∞) ≤ ((s : ℕ) : WithTop ℕ∞) := by
    rw [add_comm]
    exact le_of_eq hcast
  have hfd : ContDiffOn ℝ (s - 1) (fderiv ℝ G) R := hG.fderiv_of_isOpen hR hle
  exact hfd.clm_apply contDiffOn_const

/-- The identity chart datum. -/
def ChartDatum.id (d : ℕ) (x : Fin d → ℝ) (r : ℝ) (hr : 0 < r) : ChartDatum d where
  t := d
  γ := fun y => y
  base := x
  rad := r
  rad_pos := hr
  contdiffOn := contDiff_id.contDiffOn
  expanding := fun _ _ _ _ => le_rfl

/-- Composing an expanding `C¹` parametrisation (defined on the open set `V`) with a chart datum
whose closed-ball image lies in `V` gives a chart datum in the ambient space. -/
def ChartDatum.comp {e d : ℕ} {V : Set (Fin e → ℝ)} {Ψ : (Fin e → ℝ) → (Fin d → ℝ)}
    (hΨ : ContDiffOn ℝ 1 Ψ V) (hΨexp : ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ dist (Ψ x) (Ψ y))
    (φ : ChartDatum e) (hφV : φ.γ '' Metric.closedBall φ.base φ.rad ⊆ V) : ChartDatum d :=
  { t := φ.t
    γ := Ψ ∘ φ.γ
    base := φ.base
    rad := φ.rad
    rad_pos := φ.rad_pos
    contdiffOn := hΨ.comp φ.contdiffOn (fun x hx => hφV ⟨x, hx, rfl⟩)
    expanding := fun x hx y hy => (φ.expanding x hx y hy).trans
      (hΨexp (φ.γ x) (hφV ⟨x, hx, rfl⟩) (φ.γ y) (hφV ⟨y, hy, rfl⟩)) }

/-- An expanding map is injective on any set on which it is expanding. -/
lemma injOn_of_expanding {α β : Type*} [MetricSpace α] [PseudoMetricSpace β]
    {f : α → β} {V : Set α} (h : ∀ x ∈ V, ∀ y ∈ V, dist x y ≤ dist (f x) (f y)) :
    Set.InjOn f V := by
  intro a ha b hb hab
  have h1 : dist a b ≤ dist (f a) (f b) := h a ha b hb
  rw [hab, dist_self] at h1
  exact eq_of_dist_eq_zero (le_antisymm h1 dist_nonneg)

end

end Work.WilE9G.Sard
