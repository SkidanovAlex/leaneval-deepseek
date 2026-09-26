import Mathlib
import Submission.Work.Smooth.SphereJordan.exists_half_spans_defs
import Submission.Work.Smooth.SphereJordan.planeArcSetup
import Submission.Work.Smooth.SphereJordan.RiemannSphere
import Submission.Work.Smooth.SphereJordan.planeThetaSpans
import Submission.Work.Smooth.SphereJordan.thetaSpansOfPlane

/-!
# `Work.Smooth.SphereJordan.thetaTwoComponentsSpansH`

The complement of a theta graph on the Riemann sphere — two disjoint embedded closed discs joined by
two disjoint arcs with interior off the discs — consists of exactly two non-empty open preconnected
sets, and the closure of each is the image of an injective continuous map of the model disc.
-/

namespace Work.Smooth.SphereJordan

noncomputable section

open Set

/-! ## Lemma A: an open preconnected set with frontier a simple closed curve is one of its two
sides. -/

/-- **Lemma A.**  Let `c` be a simple closed plane curve with a Jordan separation datum
`h : PlaneSeparation c` (unbounded side `h.U`, bounded side `h.V`), and let `W` be a non-empty
open, preconnected and bounded set with frontier the trace of `c`.  Then `W` is the bounded side
`h.V`.

The proof: `W` avoids the trace (it is open and its frontier is the trace), so it lies on one side.
If `W ⊆ h.U`, then `ℂ = closure h.V ∪ closure W` (every point of `h.U` is in `closure W`, because
`h.U` is preconnected and so cannot meet both `closure W` and its complement), but both closures are
bounded — contradicting the unboundedness of `ℂ`. -/
theorem planeSeparation_eq_of_frontier {c : Work.Smooth.Jordan.PlaneCurve}
    (h : Work.Smooth.Jordan.PlaneSeparation c) {W : Set ℂ} (hWo : IsOpen W)
    (hWp : IsPreconnected W) (hWe : W.Nonempty) (hWb : Bornology.IsBounded W)
    (hWf : frontier W = c.trace) : W = h.V := by
  -- `W` avoids the trace
  have hWsub : W ⊆ c.traceᶜ := by
    intro x hx
    have hx' : x ∉ frontier W := by
      intro hxf
      rw [frontier] at hxf
      exact hxf.2 (by rw [hWo.interior_eq]; exact hx)
    rwa [hWf] at hx'
  -- the two sides avoid the trace
  have hVsub : h.V ⊆ c.traceᶜ := fun z hz => by
    rw [← h.union_eq]; exact Or.inr hz
  have hUsub : h.U ⊆ c.traceᶜ := fun z hz => by
    rw [← h.union_eq]; exact Or.inl hz
  -- the key point: a preconnected open set meeting `W` cannot meet both `closure W` and its
  -- complement
  have key : ∀ {X : Set ℂ}, IsPreconnected X → IsOpen X → X ⊆ c.traceᶜ → (X ∩ W).Nonempty →
      X ⊆ closure W ∨ X ⊆ Wᶜ := by
    intro X hXp hXo hXt hXW
    refine (isPreconnected_iff_subset_of_disjoint_closed.mp hXp (closure W) Wᶜ
      isClosed_closure hWo.isClosed_compl ?_ ?_).imp id id
    · intro x hx
      rcases em (x ∈ closure W) with h | h
      · exact Or.inl h
      · exact Or.inr fun hxW => h (subset_closure hxW)
    · rw [← not_nonempty_iff_eq_empty]
      rintro ⟨x, hxX, hxW, hxnW⟩
      have hxfr : x ∈ frontier W := by
        rw [frontier]; exact ⟨hxW, fun h => hxnW (interior_subset h)⟩
      rw [hWf] at hxfr
      exact hXt hxX hxfr
  rcases Work.Smooth.Jordan.plane_separation_preconnected_subset h hWp hWsub with hU | hV
  swap
  · -- `W ⊆ h.V`; then `W = h.V`
    refine Set.Subset.antisymm hV ?_
    by_contra hcon
    obtain ⟨y, hyV, hyW⟩ := Set.not_subset.mp hcon
    have hWne : (h.V ∩ W).Nonempty := hWe.mono fun x hx => ⟨hV hx, hx⟩
    rcases key h.preconn_V h.isOpen_V hVsub hWne with h1 | h1
    · -- `h.V ⊆ closure W`, so `h.V ⊆ W ∪ frontier W = W ∪ trace`
      have hsub : h.V ⊆ W ∪ c.trace := by
        intro z hz
        have hz' := h1 hz
        rwa [closure_eq_self_union_frontier, hWf] at hz'
      rcases hsub hyV with hy | hy
      · exact hyW hy
      · exact hVsub hyV hy
    · obtain ⟨z, hz⟩ := hWe
      exact (h1 (hV hz)) hz
  · -- the unbounded case is impossible
    exfalso
    have hUcl : h.U ⊆ closure W := by
      obtain ⟨z, hz⟩ := hWe
      rcases key h.preconn_U h.isOpen_U hUsub ⟨z, hU hz, hz⟩ with h1 | h1
      · exact h1
      · exact absurd hz (h1 (hU hz))
    have hcover : (Set.univ : Set ℂ) ⊆ closure h.V ∪ closure W := by
      intro x _
      rcases em (x ∈ c.traceᶜ) with hx | hx
      · rw [← h.union_eq] at hx
        rcases hx with hx | hx
        · exact Or.inr (hUcl hx)
        · exact Or.inl (subset_closure hx)
      · have hxf : x ∈ frontier W := by
          rw [← hWf] at hx
          simpa using hx
        exact Or.inr (frontier_subset_closure hxf)
    have hVb : Bornology.IsBounded (closure h.V) := h.bounded_V.closure
    have hWbc : Bornology.IsBounded (closure W) := hWb.closure
    obtain ⟨C₁, hC₁⟩ := Metric.isBounded_iff.mp hVb
    obtain ⟨C₂, hC₂⟩ := Metric.isBounded_iff.mp hWbc
    obtain ⟨y₁, hy₁⟩ := h.nonempty_V
    obtain ⟨y₂, hy₂⟩ := hWe
    have hC1nn : (0:ℝ) ≤ C₁ := by
      have h := hC₁ (subset_closure hy₁) (subset_closure hy₁)
      simpa using h
    have hC2nn : (0:ℝ) ≤ C₂ := by
      have h := hC₂ (subset_closure hy₂) (subset_closure hy₂)
      simpa using h
    set R : ℝ := C₁ + C₂ + dist y₁ 0 + dist y₂ 0 + 1 with hR
    have hRpos : 0 < R := by
      have h1 : (0:ℝ) ≤ dist y₁ 0 := dist_nonneg
      have h2 : (0:ℝ) ≤ dist y₂ 0 := dist_nonneg
      rw [hR]; linarith
    have hx : ((R : ℝ) : ℂ) ∈ closure h.V ∪ closure W := hcover (Set.mem_univ _)
    have hnorm : ‖(((R : ℝ)) : ℂ)‖ = R := by
      simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos]
    have htri : ∀ (u v : ℂ), ‖u‖ ≤ dist u v + ‖v‖ := by
      intro u v
      calc ‖u‖ = dist u 0 := by rw [dist_eq_norm, sub_zero]
        _ ≤ dist u v + dist v 0 := dist_triangle _ _ _
        _ = dist u v + ‖v‖ := by simp only [dist_eq_norm, sub_zero]
    rcases hx with hx | hx
    · have h5 : dist (((R:ℝ)):ℂ) y₁ ≤ C₁ := hC₁ hx (subset_closure hy₁)
      have hy1n : ‖y₁‖ = dist y₁ 0 := by rw [dist_eq_norm, sub_zero]
      have h6 : ‖(((R:ℝ)):ℂ)‖ ≤ C₁ + dist y₁ 0 := by
        have h := htri (((R:ℝ)):ℂ) y₁
        rw [hy1n] at h
        linarith
      rw [hnorm, hR] at h6
      have h7 : (0:ℝ) ≤ dist y₁ 0 := dist_nonneg
      have h8 : (0:ℝ) ≤ dist y₂ 0 := dist_nonneg
      linarith
    · have h5 : dist (((R:ℝ)):ℂ) y₂ ≤ C₂ := hC₂ hx (subset_closure hy₂)
      have hy2n : ‖y₂‖ = dist y₂ 0 := by rw [dist_eq_norm, sub_zero]
      have h6 : ‖(((R:ℝ)):ℂ)‖ ≤ C₂ + dist y₂ 0 := by
        have h := htri (((R:ℝ)):ℂ) y₂
        rw [hy2n] at h
        linarith
      rw [hnorm, hR] at h6
      have h7 : (0:ℝ) ≤ dist y₂ 0 := dist_nonneg
      have h8 : (0:ℝ) ≤ dist y₁ 0 := dist_nonneg
      linarith


/-! ## The reduction map `ℝ → [0, 2π)` and the gluing of four arcs -/

/-- Reduction of a real number modulo `2π` into `[0, 2π)`. -/
private def perPt (τ : ℝ) : ℝ := τ - (⌊τ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi)

theorem two_pi_pos : (0 : ℝ) < 2 * Real.pi := by positivity

theorem perPt_mem (τ : ℝ) : perPt τ ∈ Set.Ico (0 : ℝ) (2 * Real.pi) := by
  have hpos := two_pi_pos
  refine ⟨?_, ?_⟩
  · have := (le_div_iff₀ hpos).mp (Int.floor_le (τ / (2 * Real.pi)))
    rw [perPt]; linarith
  · have := (div_lt_iff₀ hpos).mp (Int.lt_floor_add_one (τ / (2 * Real.pi)))
    rw [perPt]; linarith

theorem perPt_self {τ : ℝ} (hτ : τ ∈ Set.Ico (0 : ℝ) (2 * Real.pi)) : perPt τ = τ := by
  have hpos := two_pi_pos
  have h0 : ⌊τ / (2 * Real.pi)⌋ = 0 := by
    rw [Int.floor_eq_iff]
    refine ⟨?_, ?_⟩
    · simpa using div_nonneg hτ.1 hpos.le
    · have h1 : τ / (2 * Real.pi) < 1 := by rw [div_lt_one hpos]; exact hτ.2
      simpa using h1
  rw [perPt, h0]; norm_num

private theorem perPt_shift (τ : ℝ) : perPt (τ + 2 * Real.pi) = perPt τ := by
  have h : ⌊(τ + 2 * Real.pi) / (2 * Real.pi)⌋ = ⌊τ / (2 * Real.pi)⌋ + 1 := by
    rw [add_div, div_self (by positivity : (2 * Real.pi) ≠ 0)]
    exact Int.floor_add_one _
  rw [perPt, perPt, h]; push_cast; ring

/-- Clamping of a real number to the interval `[0,1]`. -/
def clamp (x : ℝ) : ℝ := max 0 (min 1 x)

theorem clamp_mem (x : ℝ) : clamp x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem continuous_clamp : Continuous clamp :=
  continuous_const.max (continuous_const.min continuous_id)

theorem clamp_eq {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : clamp x = x := by
  rw [clamp, min_eq_right h1, max_eq_right h0]

/-- The **unfolded** four-arc loop: on the parameter interval `[0, 2π]` it traverses the four arcs
`A`, `B`, `C`, `D` in order, each on a quarter of the period. -/
def fourLoop (A B C D : C(Set.Icc (0 : ℝ) 1, ℂ)) (σ : ℝ) : ℂ :=
  if σ ≤ Real.pi / 2 then A ⟨clamp (σ / (Real.pi / 2)), clamp_mem _⟩
  else if σ ≤ Real.pi then B ⟨clamp ((σ - Real.pi / 2) / (Real.pi / 2)), clamp_mem _⟩
  else if σ ≤ 3 * Real.pi / 2 then C ⟨clamp ((σ - Real.pi) / (Real.pi / 2)), clamp_mem _⟩
  else D ⟨clamp ((σ - 3 * Real.pi / 2) / (Real.pi / 2)), clamp_mem _⟩

/-- The **four-arc curve** obtained by gluing the arcs `A B C D` into a `2π`-periodic loop. -/
def fourCurve (A B C D : C(Set.Icc (0 : ℝ) 1, ℂ)) : ℝ → ℂ :=
  fun τ => fourLoop A B C D (perPt τ)

theorem fourCurve_periodic (A B C D : C(Set.Icc (0 : ℝ) 1, ℂ)) :
    Function.Periodic (fourCurve A B C D) (2 * Real.pi) := by
  intro τ
  rw [fourCurve, fourCurve, perPt_shift]

theorem arcParA {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ Real.pi / 2) :
    x / (Real.pi / 2) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨div_nonneg h0 (by positivity),
    by rw [div_le_one (by positivity)]; exact h1⟩

theorem arcParB {x : ℝ} (h0 : Real.pi / 2 ≤ x) (h1 : x ≤ Real.pi) :
    (x - Real.pi / 2) / (Real.pi / 2) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨div_nonneg (by linarith [Real.pi_pos]) (by positivity),
    by rw [div_le_one (by positivity)]; linarith⟩

theorem arcParC {x : ℝ} (h0 : Real.pi ≤ x) (h1 : x ≤ 3 * Real.pi / 2) :
    (x - Real.pi) / (Real.pi / 2) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨div_nonneg (by linarith [Real.pi_pos]) (by positivity),
    by rw [div_le_one (by positivity)]; linarith⟩

theorem arcParD {x : ℝ} (h0 : 3 * Real.pi / 2 ≤ x) (h1 : x < 2 * Real.pi) :
    (x - 3 * Real.pi / 2) / (Real.pi / 2) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨div_nonneg (by linarith [Real.pi_pos]) (by positivity),
    by rw [div_le_one (by positivity)]; linarith⟩

theorem fourCurve_eq_A (A B C D : C(Set.Icc (0 : ℝ) 1, ℂ)) {τ : ℝ}
    (h0 : 0 ≤ perPt τ) (h1 : perPt τ ≤ Real.pi / 2) :
    fourCurve A B C D τ = A ⟨perPt τ / (Real.pi / 2), arcParA h0 h1⟩ := by
  rw [fourCurve, fourLoop, if_pos h1]
  congr 1
  exact Subtype.ext (clamp_eq (div_nonneg h0 (by positivity))
    (by rw [div_le_one (by positivity)]; exact h1))

theorem fourCurve_eq_B (A B C D : C(Set.Icc (0 : ℝ) 1, ℂ))
    (hAB : A ⟨1, by norm_num⟩ = B ⟨0, by norm_num⟩) {τ : ℝ}
    (h0 : Real.pi / 2 ≤ perPt τ) (h1 : perPt τ ≤ Real.pi) :
    fourCurve A B C D τ = B ⟨(perPt τ - Real.pi / 2) / (Real.pi / 2), arcParB h0 h1⟩ := by
  rw [fourCurve, fourLoop]
  rcases eq_or_lt_of_le h0 with heq | hlt
  · have hσ : perPt τ = Real.pi / 2 := heq.symm
    rw [if_pos heq.symm.le]
    have hL' : clamp (perPt τ / (Real.pi / 2)) = 1 := by
      rw [hσ, div_self (by positivity : Real.pi / 2 ≠ 0)]
      exact clamp_eq zero_le_one le_rfl
    have hR' : (perPt τ - Real.pi / 2) / (Real.pi / 2) = 0 := by
      rw [hσ, sub_self, zero_div]
    have hL : (⟨clamp (perPt τ / (Real.pi / 2)), clamp_mem _⟩ : Set.Icc (0 : ℝ) 1) =
        ⟨1, by norm_num⟩ := Subtype.ext hL'
    have hR : (⟨(perPt τ - Real.pi / 2) / (Real.pi / 2), arcParB h0 h1⟩ : Set.Icc (0 : ℝ) 1) =
        ⟨0, by norm_num⟩ := Subtype.ext hR'
    rw [hL, hR]
    exact hAB
  · rw [if_neg (not_le.mpr hlt), if_pos h1]
    congr 1
    exact Subtype.ext (clamp_eq (div_nonneg (by linarith [Real.pi_pos]) (by positivity))
      (by rw [div_le_one (by positivity)]; linarith))

theorem fourCurve_eq_C (A B C D : C(Set.Icc (0 : ℝ) 1, ℂ))
    (hBC : B ⟨1, by norm_num⟩ = C ⟨0, by norm_num⟩) {τ : ℝ}
    (h0 : Real.pi ≤ perPt τ) (h1 : perPt τ ≤ 3 * Real.pi / 2) :
    fourCurve A B C D τ = C ⟨(perPt τ - Real.pi) / (Real.pi / 2), arcParC h0 h1⟩ := by
  rw [fourCurve, fourLoop]
  rcases eq_or_lt_of_le h0 with heq | hlt
  · have hσ : perPt τ = Real.pi := heq.symm
    rw [if_neg (by linarith [Real.pi_pos] : ¬ (perPt τ ≤ Real.pi / 2)), if_pos heq.symm.le]
    have hL' : clamp ((perPt τ - Real.pi / 2) / (Real.pi / 2)) = 1 := by
      rw [hσ, show Real.pi - Real.pi / 2 = Real.pi / 2 from by ring,
        div_self (by positivity : Real.pi / 2 ≠ 0)]
      exact clamp_eq zero_le_one le_rfl
    have hR' : (perPt τ - Real.pi) / (Real.pi / 2) = 0 := by
      rw [hσ, sub_self, zero_div]
    have hL : (⟨clamp ((perPt τ - Real.pi / 2) / (Real.pi / 2)), clamp_mem _⟩ :
        Set.Icc (0 : ℝ) 1) = ⟨1, by norm_num⟩ := Subtype.ext hL'
    have hR : (⟨(perPt τ - Real.pi) / (Real.pi / 2), arcParC h0 h1⟩ : Set.Icc (0 : ℝ) 1) =
        ⟨0, by norm_num⟩ := Subtype.ext hR'
    rw [hL, hR]
    exact hBC
  · rw [if_neg (by linarith [Real.pi_pos] : ¬ (perPt τ ≤ Real.pi / 2)),
      if_neg (not_le.mpr hlt), if_pos h1]
    congr 1
    exact Subtype.ext (clamp_eq (div_nonneg (by linarith [Real.pi_pos]) (by positivity))
      (by rw [div_le_one (by positivity)]; linarith))

theorem fourCurve_eq_D (A B C D : C(Set.Icc (0 : ℝ) 1, ℂ))
    (hCD : C ⟨1, by norm_num⟩ = D ⟨0, by norm_num⟩) {τ : ℝ}
    (h0 : 3 * Real.pi / 2 ≤ perPt τ) :
    fourCurve A B C D τ =
      D ⟨(perPt τ - 3 * Real.pi / 2) / (Real.pi / 2),
        arcParD h0 (perPt_mem τ).2⟩ := by
  rw [fourCurve, fourLoop]
  rcases eq_or_lt_of_le h0 with heq | hlt
  · have hσ : perPt τ = 3 * Real.pi / 2 := heq.symm
    rw [if_neg (by linarith [Real.pi_pos] : ¬ (perPt τ ≤ Real.pi / 2)),
      if_neg (by linarith [Real.pi_pos] : ¬ (perPt τ ≤ Real.pi)), if_pos heq.symm.le]
    have hL' : clamp ((perPt τ - Real.pi) / (Real.pi / 2)) = 1 := by
      rw [hσ, show 3 * Real.pi / 2 - Real.pi = Real.pi / 2 from by ring,
        div_self (by positivity : Real.pi / 2 ≠ 0)]
      exact clamp_eq zero_le_one le_rfl
    have hR' : (perPt τ - 3 * Real.pi / 2) / (Real.pi / 2) = 0 := by
      rw [hσ, sub_self, zero_div]
    have hL : (⟨clamp ((perPt τ - Real.pi) / (Real.pi / 2)), clamp_mem _⟩ :
        Set.Icc (0 : ℝ) 1) = ⟨1, by norm_num⟩ := Subtype.ext hL'
    have hR : (⟨(perPt τ - 3 * Real.pi / 2) / (Real.pi / 2), arcParD h0 (perPt_mem τ).2⟩ :
        Set.Icc (0 : ℝ) 1) = ⟨0, by norm_num⟩ := Subtype.ext hR'
    rw [hL, hR]
    exact hCD
  · rw [if_neg (by linarith [Real.pi_pos] : ¬ (perPt τ ≤ Real.pi / 2)),
      if_neg (by linarith [Real.pi_pos] : ¬ (perPt τ ≤ Real.pi)),
      if_neg (not_le.mpr hlt)]
    congr 1
    exact Subtype.ext (clamp_eq (div_nonneg (by linarith [Real.pi_pos]) (by positivity))
      (by rw [div_le_one (by positivity)]
          linarith [Real.pi_pos, (perPt_mem τ).2]))

theorem perPt_int (k : ℤ) (τ : ℝ) : perPt (τ + (k : ℝ) * (2 * Real.pi)) = perPt τ := by
  have h : ⌊(τ + (k : ℝ) * (2 * Real.pi)) / (2 * Real.pi)⌋ = ⌊τ / (2 * Real.pi)⌋ + k := by
    rw [add_div, mul_div_cancel_right₀ _ (by positivity : (2 * Real.pi) ≠ 0),
      Int.floor_add_intCast]
  rw [perPt, perPt, h]; push_cast; ring

theorem clamp_zero : clamp (0 : ℝ) = 0 := clamp_eq le_rfl zero_le_one

theorem clamp_one : clamp (1 : ℝ) = 1 := clamp_eq zero_le_one le_rfl

theorem continuous_fourCurve (A B C D : C(Set.Icc (0 : ℝ) 1, ℂ))
    (hAB : A ⟨1, by norm_num⟩ = B ⟨0, by norm_num⟩)
    (hBC : B ⟨1, by norm_num⟩ = C ⟨0, by norm_num⟩)
    (hCD : C ⟨1, by norm_num⟩ = D ⟨0, by norm_num⟩)
    (hDA : D ⟨1, by norm_num⟩ = A ⟨0, by norm_num⟩) :
    Continuous (fourCurve A B C D) := by
  have hA : ContinuousOn (fourLoop A B C D) (Set.Icc (0:ℝ) (Real.pi / 2)) := by
    refine ContinuousOn.congr
      (f := fun σ : ℝ => A ⟨clamp (σ / (Real.pi / 2)), clamp_mem _⟩) ?_ ?_
    · exact (A.continuous.comp ((continuous_clamp.comp (by fun_prop :
        Continuous fun σ : ℝ => σ / (Real.pi / 2))).subtype_mk _)).continuousOn
    · intro σ hσ
      show fourLoop A B C D σ = A ⟨clamp (σ / (Real.pi / 2)), clamp_mem _⟩
      rw [fourLoop, if_pos hσ.2]
  have hB : ContinuousOn (fourLoop A B C D) (Set.Icc (Real.pi / 2) Real.pi) := by
    refine ContinuousOn.congr
      (f := fun σ : ℝ => B ⟨clamp ((σ - Real.pi / 2) / (Real.pi / 2)), clamp_mem _⟩) ?_ ?_
    · exact (B.continuous.comp ((continuous_clamp.comp (by fun_prop :
        Continuous fun σ : ℝ => (σ - Real.pi / 2) / (Real.pi / 2))).subtype_mk _)).continuousOn
    · intro σ hσ
      show fourLoop A B C D σ = B ⟨clamp ((σ - Real.pi / 2) / (Real.pi / 2)), clamp_mem _⟩
      rcases eq_or_lt_of_le hσ.1 with heq | hlt
      · rw [← heq, fourLoop, if_pos le_rfl]
        simp only [div_self (by positivity : Real.pi / 2 ≠ 0), sub_self, zero_div,
          clamp_zero, clamp_one]
        exact hAB
      · rw [fourLoop, if_neg (not_le.mpr hlt), if_pos hσ.2]
  have hC : ContinuousOn (fourLoop A B C D) (Set.Icc Real.pi (3 * Real.pi / 2)) := by
    refine ContinuousOn.congr
      (f := fun σ : ℝ => C ⟨clamp ((σ - Real.pi) / (Real.pi / 2)), clamp_mem _⟩) ?_ ?_
    · exact (C.continuous.comp ((continuous_clamp.comp (by fun_prop :
        Continuous fun σ : ℝ => (σ - Real.pi) / (Real.pi / 2))).subtype_mk _)).continuousOn
    · intro σ hσ
      show fourLoop A B C D σ = C ⟨clamp ((σ - Real.pi) / (Real.pi / 2)), clamp_mem _⟩
      rcases eq_or_lt_of_le hσ.1 with heq | hlt
      · rw [← heq, fourLoop, if_neg (by linarith [Real.pi_pos] : ¬ (Real.pi ≤ Real.pi / 2)),
          if_pos le_rfl]
        simp only [div_self (by positivity : Real.pi / 2 ≠ 0), sub_self, zero_div,
          clamp_zero, clamp_one, show (Real.pi : ℝ) - Real.pi / 2 = Real.pi / 2 from by ring]
        exact hBC
      · rw [fourLoop, if_neg (by linarith [hlt, Real.pi_pos] : ¬ (σ ≤ Real.pi / 2)),
          if_neg (not_le.mpr hlt), if_pos hσ.2]
  have hD : ContinuousOn (fourLoop A B C D) (Set.Icc (3 * Real.pi / 2) (2 * Real.pi)) := by
    refine ContinuousOn.congr
      (f := fun σ : ℝ => D ⟨clamp ((σ - 3 * Real.pi / 2) / (Real.pi / 2)), clamp_mem _⟩) ?_ ?_
    · exact (D.continuous.comp ((continuous_clamp.comp (by fun_prop :
        Continuous fun σ : ℝ => (σ - 3 * Real.pi / 2) / (Real.pi / 2))).subtype_mk _)).continuousOn
    · intro σ hσ
      show fourLoop A B C D σ = D ⟨clamp ((σ - 3 * Real.pi / 2) / (Real.pi / 2)), clamp_mem _⟩
      rcases eq_or_lt_of_le hσ.1 with heq | hlt
      · rw [← heq, fourLoop,
          if_neg (by linarith [Real.pi_pos] : ¬ (3 * Real.pi / 2 ≤ Real.pi / 2)),
          if_neg (by linarith [Real.pi_pos] : ¬ (3 * Real.pi / 2 ≤ Real.pi)), if_pos le_rfl]
        simp only [div_self (by positivity : Real.pi / 2 ≠ 0), sub_self, zero_div,
          clamp_zero, clamp_one, show (3 * Real.pi / 2 : ℝ) - Real.pi = Real.pi / 2 from by ring]
        exact hCD
      · rw [fourLoop, if_neg (by linarith [hlt, Real.pi_pos] : ¬ (σ ≤ Real.pi / 2)),
          if_neg (by linarith [hlt, Real.pi_pos] : ¬ (σ ≤ Real.pi)),
          if_neg (not_le.mpr hlt)]
  have h12 := hA.union_of_isClosed hB isClosed_Icc isClosed_Icc
  rw [Icc_union_Icc_eq_Icc (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2)
    (by linarith [Real.pi_pos] : Real.pi / 2 ≤ Real.pi)] at h12
  have h34 := hC.union_of_isClosed hD isClosed_Icc isClosed_Icc
  rw [Icc_union_Icc_eq_Icc (by linarith [Real.pi_pos] : Real.pi ≤ 3 * Real.pi / 2)
    (by linarith [Real.pi_pos] : 3 * Real.pi / 2 ≤ 2 * Real.pi)] at h34
  have h1234 := h12.union_of_isClosed h34 isClosed_Icc isClosed_Icc
  rw [Icc_union_Icc_eq_Icc (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi)
    (by linarith [Real.pi_pos] : Real.pi ≤ 2 * Real.pi)] at h1234
  have hjoin : fourLoop A B C D 0 = fourLoop A B C D (2 * Real.pi) := by
    have h1 : fourLoop A B C D 0 = A ⟨0, by norm_num⟩ := by
      rw [fourLoop, if_pos (by linarith [Real.pi_pos] : (0:ℝ) ≤ Real.pi / 2)]
      simp only [zero_div, clamp_zero]
    have h2 : fourLoop A B C D (2 * Real.pi) = D ⟨1, by norm_num⟩ := by
      rw [fourLoop, if_neg (by linarith [Real.pi_pos] : ¬ ((2 * Real.pi : ℝ) ≤ Real.pi / 2)),
        if_neg (by linarith [Real.pi_pos] : ¬ ((2 * Real.pi : ℝ) ≤ Real.pi)),
        if_neg (by linarith [Real.pi_pos] : ¬ ((2 * Real.pi : ℝ) ≤ 3 * Real.pi / 2))]
      simp only [show (2 * Real.pi - 3 * Real.pi / 2) / (Real.pi / 2) = 1 from
        (div_eq_one_iff_eq (by positivity : Real.pi / 2 ≠ 0)).mpr (by ring), clamp_one]
    rw [h1, h2, hDA]
  have hshift : ∀ k : ℤ, ContinuousOn (fun t : ℝ => fourLoop A B C D (perPt t))
      (Set.Icc ((k : ℝ) * (2 * Real.pi)) ((k : ℝ) * (2 * Real.pi) + 2 * Real.pi)) := by
    intro k
    refine ContinuousOn.congr (f := fun t : ℝ =>
      fourLoop A B C D (t - (k : ℝ) * (2 * Real.pi))) ?_ ?_
    · refine h1234.comp (by fun_prop) ?_
      intro x hx
      rw [Set.mem_Icc] at hx ⊢
      exact ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
    · intro x hx
      rw [Set.mem_Icc] at hx
      simp only []
      have hx' : x - (k : ℝ) * (2 * Real.pi) ∈ Set.Icc (0:ℝ) (2 * Real.pi) :=
        ⟨by linarith [hx.1], by linarith [hx.2, Real.pi_pos]⟩
      rcases lt_or_eq_of_le hx'.2 with hlt | heq
      · have hpi : perPt (x - (k : ℝ) * (2 * Real.pi)) = x - (k : ℝ) * (2 * Real.pi) :=
          perPt_self ⟨hx'.1, hlt⟩
        have hrel : perPt x = perPt (x - (k : ℝ) * (2 * Real.pi)) := by
          have h1 := perPt_int (-k) x
          rw [show x + ((-k : ℤ) : ℝ) * (2 * Real.pi) = x - (k : ℝ) * (2 * Real.pi) by
            push_cast; ring] at h1
          exact h1.symm
        rw [hrel, hpi]
      · have hx2 : x = (k : ℝ) * (2 * Real.pi) + 2 * Real.pi := by linarith [heq]
        have hrel : perPt x = 0 := by
          have := perPt_int (-k) x
          rw [show x + ((-k : ℤ) : ℝ) * (2 * Real.pi) = 2 * Real.pi by
            rw [hx2]; push_cast; ring] at this
          rw [← this, perPt, div_self (by positivity : (2:ℝ) * Real.pi ≠ 0),
            show ⌊(1:ℝ)⌋ = 1 from Int.floor_one]
          norm_num
        rw [hrel, heq]; exact hjoin
  rw [continuous_iff_continuousAt]
  intro τ
  set k : ℤ := ⌊τ / (2 * Real.pi)⌋ with hk
  have hper : perPt τ = τ - (k : ℝ) * (2 * Real.pi) := by rw [perPt, hk]
  have hmem : τ ∈ Set.Icc ((k:ℝ) * (2 * Real.pi)) ((k:ℝ) * (2 * Real.pi) + 2 * Real.pi) := by
    rw [Set.mem_Icc]
    exact ⟨by linarith [hper, (perPt_mem τ).1], by linarith [hper, (perPt_mem τ).2]⟩
  have hupper : τ < (k:ℝ) * (2 * Real.pi) + 2 * Real.pi := by
    linarith [hper, (perPt_mem τ).2]
  by_cases hτ : τ = (k:ℝ) * (2 * Real.pi)
  · have hk1 : (((k-1 : ℤ)) : ℝ) = (k : ℝ) - 1 := by push_cast; ring
    have hI1 : ((((k-1 : ℤ)) : ℝ) * (2 * Real.pi)) + 2 * Real.pi = (k:ℝ) * (2*Real.pi) := by
      rw [hk1]; ring
    have hU : ContinuousOn (fun t : ℝ => fourLoop A B C D (perPt t))
        (Set.Icc (((k-1:ℤ):ℝ) * (2*Real.pi)) ((k:ℝ) * (2*Real.pi) + 2 * Real.pi)) := by
      have h := (hshift (k-1)).union_of_isClosed (hshift k) isClosed_Icc isClosed_Icc
      rw [hI1] at h
      rwa [Icc_union_Icc_eq_Icc (by rw [hk1]; linarith [Real.pi_pos])
        (by linarith [Real.pi_pos])] at h
    have hlt1 : (((k-1:ℤ):ℝ) * (2*Real.pi)) < τ := by
      rw [hτ, hk1]; nlinarith [Real.pi_pos]
    have hlt2 : τ < (k:ℝ) * (2*Real.pi) + 2 * Real.pi := by
      rw [hτ]; linarith [Real.pi_pos]
    have hmem' : τ ∈ Set.Icc (((k-1:ℤ):ℝ) * (2*Real.pi)) ((k:ℝ) * (2*Real.pi) + 2 * Real.pi) :=
      ⟨le_of_lt hlt1, le_of_lt hlt2⟩
    have hnb : Set.Icc (((k-1:ℤ):ℝ) * (2*Real.pi)) ((k:ℝ) * (2*Real.pi) + 2 * Real.pi) ∈ nhds τ :=
      Filter.mem_of_superset (isOpen_Ioo.mem_nhds ⟨hlt1, hlt2⟩) Ioo_subset_Icc_self
    exact ContinuousWithinAt.continuousAt (hU.continuousWithinAt hmem') hnb
  · have hlt : (k:ℝ) * (2 * Real.pi) < τ := lt_of_le_of_ne hmem.1 (Ne.symm hτ)
    have hint : τ ∈ interior (Set.Icc ((k:ℝ) * (2 * Real.pi))
        ((k:ℝ) * (2 * Real.pi) + 2 * Real.pi)) := by
      rw [interior_Icc]; exact ⟨hlt, hupper⟩
    exact ContinuousWithinAt.continuousAt ((hshift k).continuousWithinAt hmem)
      (Filter.mem_of_superset (isOpen_interior.mem_nhds hint) interior_subset)

/-- The four-arc curve as a plane curve. -/
def fourPlaneCurve (A B C D : C(Set.Icc (0 : ℝ) 1, ℂ))
    (hAB : A ⟨1, by norm_num⟩ = B ⟨0, by norm_num⟩)
    (hBC : B ⟨1, by norm_num⟩ = C ⟨0, by norm_num⟩)
    (hCD : C ⟨1, by norm_num⟩ = D ⟨0, by norm_num⟩)
    (hDA : D ⟨1, by norm_num⟩ = A ⟨0, by norm_num⟩) : Work.Smooth.Jordan.PlaneCurve :=
  ⟨fourCurve A B C D, continuous_fourCurve A B C D hAB hBC hCD hDA,
    fourCurve_periodic A B C D⟩

theorem fourPlaneCurve_apply (A B C D : C(Set.Icc (0 : ℝ) 1, ℂ))
    (hAB : A ⟨1, by norm_num⟩ = B ⟨0, by norm_num⟩)
    (hBC : B ⟨1, by norm_num⟩ = C ⟨0, by norm_num⟩)
    (hCD : C ⟨1, by norm_num⟩ = D ⟨0, by norm_num⟩)
    (hDA : D ⟨1, by norm_num⟩ = A ⟨0, by norm_num⟩) (τ : ℝ) :
    (fourPlaneCurve A B C D hAB hBC hCD hDA).γ τ = fourCurve A B C D τ := rfl


/-- The trace of the four-arc curve is the union of the images of the four arcs. -/
theorem fourPlaneCurveTrace (A B C D : C(Set.Icc (0 : ℝ) 1, ℂ))
    (hAB : A ⟨1, by norm_num⟩ = B ⟨0, by norm_num⟩)
    (hBC : B ⟨1, by norm_num⟩ = C ⟨0, by norm_num⟩)
    (hCD : C ⟨1, by norm_num⟩ = D ⟨0, by norm_num⟩)
    (hDA : D ⟨1, by norm_num⟩ = A ⟨0, by norm_num⟩) :
    (fourPlaneCurve A B C D hAB hBC hCD hDA).trace =
      Set.range A ∪ Set.range B ∪ Set.range C ∪ Set.range D := by
  ext x
  constructor
  · rintro ⟨τ, rfl⟩
    rw [fourPlaneCurve_apply]
    have hp := perPt_mem τ
    by_cases h : perPt τ ≤ Real.pi / 2
    · exact Or.inl (Or.inl (Or.inl ⟨⟨perPt τ / (Real.pi / 2), arcParA hp.1 h⟩,
        (fourCurve_eq_A A B C D hp.1 h).symm⟩))
    · have h' : Real.pi / 2 ≤ perPt τ := le_of_lt (not_le.mp h)
      by_cases h2 : perPt τ ≤ Real.pi
      · exact Or.inl (Or.inl (Or.inr ⟨⟨(perPt τ - Real.pi / 2) / (Real.pi / 2), arcParB h' h2⟩,
          (fourCurve_eq_B A B C D hAB h' h2).symm⟩))
      · have h2' : Real.pi ≤ perPt τ := le_of_lt (not_le.mp h2)
        by_cases h3 : perPt τ ≤ 3 * Real.pi / 2
        · exact Or.inl (Or.inr ⟨⟨(perPt τ - Real.pi) / (Real.pi / 2), arcParC h2' h3⟩,
            (fourCurve_eq_C A B C D hBC h2' h3).symm⟩)
        · exact Or.inr ⟨⟨(perPt τ - 3 * Real.pi / 2) / (Real.pi / 2),
            arcParD (le_of_lt (not_le.mp h3)) hp.2⟩,
            (fourCurve_eq_D A B C D hCD (le_of_lt (not_le.mp h3))).symm⟩
  · intro hx
    simp only [Set.mem_union, or_assoc] at hx
    rcases hx with hA | hB | hC | hD
    · -- the `A` case
      rcases hA with ⟨u, hu⟩
      rw [← hu]
      refine ⟨(u : ℝ) * (Real.pi / 2), ?_⟩
      have h0 : 0 ≤ (u : ℝ) * (Real.pi / 2) := mul_nonneg u.2.1 (by positivity)
      have h1 : (u : ℝ) * (Real.pi / 2) ≤ Real.pi / 2 := by nlinarith [u.2.2, Real.pi_pos]
      have h2 : (u : ℝ) * (Real.pi / 2) < 2 * Real.pi := by nlinarith [u.2.2, Real.pi_pos]
      have hp : perPt ((u : ℝ) * (Real.pi / 2)) = (u : ℝ) * (Real.pi / 2) :=
        perPt_self ⟨h0, h2⟩
      rw [fourPlaneCurve_apply,
        fourCurve_eq_A A B C D (by rw [hp]; exact h0) (by rw [hp]; exact h1)]
      congr 1
      apply Subtype.ext
      show perPt ((u:ℝ) * (Real.pi / 2)) / (Real.pi / 2) = (u:ℝ)
      rw [hp, mul_div_cancel_right₀ _ (by positivity : Real.pi / 2 ≠ 0)]
    · -- the `B` case
      rcases hB with ⟨u, hu⟩
      rw [← hu]
      refine ⟨Real.pi / 2 + (u : ℝ) * (Real.pi / 2), ?_⟩
      have h0 : Real.pi / 2 ≤ Real.pi / 2 + (u : ℝ) * (Real.pi / 2) := by
        nlinarith [u.2.1, Real.pi_pos]
      have h1 : Real.pi / 2 + (u : ℝ) * (Real.pi / 2) ≤ Real.pi := by
        nlinarith [u.2.2, Real.pi_pos]
      have h2 : Real.pi / 2 + (u : ℝ) * (Real.pi / 2) < 2 * Real.pi := by
        nlinarith [u.2.2, Real.pi_pos]
      have hp : perPt (Real.pi / 2 + (u : ℝ) * (Real.pi / 2)) =
          Real.pi / 2 + (u : ℝ) * (Real.pi / 2) :=
        perPt_self ⟨by linarith [Real.pi_pos], h2⟩
      rw [fourPlaneCurve_apply,
        fourCurve_eq_B A B C D hAB (by rw [hp]; exact h0) (by rw [hp]; exact h1)]
      congr 1
      apply Subtype.ext
      show (perPt (Real.pi / 2 + (u:ℝ) * (Real.pi/2)) - Real.pi / 2) / (Real.pi / 2) = (u:ℝ)
      rw [hp, show Real.pi / 2 + (u:ℝ) * (Real.pi/2) - Real.pi / 2 =
        (u:ℝ) * (Real.pi/2) by ring,
        mul_div_cancel_right₀ _ (by positivity : Real.pi / 2 ≠ 0)]
    · -- the `C` case
      rcases hC with ⟨u, hu⟩
      rw [← hu]
      refine ⟨Real.pi + (u : ℝ) * (Real.pi / 2), ?_⟩
      have h0 : Real.pi ≤ Real.pi + (u : ℝ) * (Real.pi / 2) := by
        nlinarith [u.2.1, Real.pi_pos]
      have h1 : Real.pi + (u : ℝ) * (Real.pi / 2) ≤ 3 * Real.pi / 2 := by
        nlinarith [u.2.2, Real.pi_pos]
      have h2 : Real.pi + (u : ℝ) * (Real.pi / 2) < 2 * Real.pi := by
        nlinarith [u.2.2, Real.pi_pos]
      have hp : perPt (Real.pi + (u : ℝ) * (Real.pi / 2)) =
          Real.pi + (u : ℝ) * (Real.pi / 2) :=
        perPt_self ⟨by linarith [Real.pi_pos], h2⟩
      rw [fourPlaneCurve_apply,
        fourCurve_eq_C A B C D hBC (by rw [hp]; exact h0) (by rw [hp]; exact h1)]
      congr 1
      apply Subtype.ext
      show (perPt (Real.pi + (u:ℝ) * (Real.pi/2)) - Real.pi) / (Real.pi / 2) = (u:ℝ)
      rw [hp, show Real.pi + (u:ℝ) * (Real.pi/2) - Real.pi = (u:ℝ) * (Real.pi/2) by ring,
        mul_div_cancel_right₀ _ (by positivity : Real.pi / 2 ≠ 0)]
    · -- the `D` case
      rcases hD with ⟨u, hu⟩
      rw [← hu]
      rcases eq_or_lt_of_le u.2.2 with hu1 | hu1
      · have hu' : u = ⟨1, by norm_num⟩ := Subtype.ext hu1
        refine ⟨0, ?_⟩
        have hp : perPt (0:ℝ) = 0 := perPt_self ⟨le_rfl, two_pi_pos⟩
        have hp1 : (0:ℝ) ≤ perPt 0 := hp.ge
        have hp2 : perPt (0:ℝ) ≤ Real.pi / 2 := by linarith [hp, Real.pi_pos]
        rw [fourPlaneCurve_apply, fourCurve_eq_A A B C D hp1 hp2, hu', hDA]
        congr 1
        apply Subtype.ext
        show perPt (0:ℝ) / (Real.pi / 2) = (0:ℝ)
        rw [hp]
        exact zero_div _
      · refine ⟨3 * Real.pi / 2 + (u : ℝ) * (Real.pi / 2), ?_⟩
        have h1 : 3 * Real.pi / 2 + (u : ℝ) * (Real.pi / 2) < 2 * Real.pi := by
          nlinarith [hu1, Real.pi_pos]
        have hp : perPt (3 * Real.pi / 2 + (u : ℝ) * (Real.pi / 2)) =
            3 * Real.pi / 2 + (u : ℝ) * (Real.pi / 2) :=
          perPt_self ⟨by nlinarith [u.2.1, Real.pi_pos], h1⟩
        rw [fourPlaneCurve_apply,
          fourCurve_eq_D A B C D hCD (by rw [hp]; nlinarith [u.2.1, Real.pi_pos])]
        congr 1
        apply Subtype.ext
        show (perPt (3 * Real.pi / 2 + (u:ℝ) * (Real.pi/2)) - 3 * Real.pi / 2) /
          (Real.pi/2) = (u:ℝ)
        rw [hp, show 3 * Real.pi / 2 + (u:ℝ) * (Real.pi/2) - 3 * Real.pi / 2 =
          (u:ℝ) * (Real.pi/2) by ring,
          mul_div_cancel_right₀ _ (by positivity : Real.pi / 2 ≠ 0)]


/-! ## Linear helpers for the four-arc curve -/

theorem div_pi2_eq {a b : ℝ} (h : a / (Real.pi / 2) = b / (Real.pi / 2)) : a = b := by
  have hpi : (Real.pi / 2 : ℝ) ≠ 0 := by positivity
  field_simp at h; linarith

theorem div_pi2_eq_one {a : ℝ} (h : a / (Real.pi / 2) = 1) : a = Real.pi / 2 := by
  have hpi : (Real.pi / 2 : ℝ) ≠ 0 := by positivity
  field_simp at h; linarith

theorem div_pi2_eq_zero {a : ℝ} (h : a / (Real.pi / 2) = 0) : a = 0 := by
  have hpi : (Real.pi / 2 : ℝ) ≠ 0 := by positivity
  field_simp at h; linarith

theorem sub_div_pi2_eq {a b : ℝ}
    (h : (a - Real.pi / 2) / (Real.pi / 2) = (b - Real.pi / 2) / (Real.pi / 2)) : a = b := by
  have hpi : (Real.pi / 2 : ℝ) ≠ 0 := by positivity
  field_simp at h; linarith

theorem sub_div_pi2_eq_zero {a : ℝ} (h : (a - Real.pi / 2) / (Real.pi / 2) = 0) :
    a = Real.pi / 2 := by
  have hpi : (Real.pi / 2 : ℝ) ≠ 0 := by positivity
  field_simp at h; linarith

theorem sub_div_pi2_eq_one {a : ℝ} (h : (a - Real.pi / 2) / (Real.pi / 2) = 1) :
    a = Real.pi := by
  have hpi : (Real.pi / 2 : ℝ) ≠ 0 := by positivity
  field_simp at h; linarith

theorem sub_pi_div_pi2_eq {a b : ℝ}
    (h : (a - Real.pi) / (Real.pi / 2) = (b - Real.pi) / (Real.pi / 2)) : a = b := by
  have hpi : (Real.pi / 2 : ℝ) ≠ 0 := by positivity
  field_simp at h; linarith

theorem sub_pi_div_pi2_eq_zero {a : ℝ} (h : (a - Real.pi) / (Real.pi / 2) = 0) :
    a = Real.pi := by
  have hpi : (Real.pi / 2 : ℝ) ≠ 0 := by positivity
  field_simp at h; linarith

theorem sub_pi_div_pi2_eq_one {a : ℝ} (h : (a - Real.pi) / (Real.pi / 2) = 1) :
    a = 3 * Real.pi / 2 := by
  have hpi : (Real.pi / 2 : ℝ) ≠ 0 := by positivity
  field_simp at h; linarith

theorem sub3_div_pi2_eq {a b : ℝ}
    (h : (a - 3 * Real.pi / 2) / (Real.pi / 2) = (b - 3 * Real.pi / 2) / (Real.pi / 2)) :
    a = b := by
  have hpi : (Real.pi / 2 : ℝ) ≠ 0 := by positivity
  field_simp at h; linarith

theorem sub3_div_pi2_eq_zero {a : ℝ} (h : (a - 3 * Real.pi / 2) / (Real.pi / 2) = 0) :
    a = 3 * Real.pi / 2 := by
  have hpi : (Real.pi / 2 : ℝ) ≠ 0 := by positivity
  field_simp at h; linarith

theorem sub3_div_pi2_eq_one {a : ℝ} (h : (a - 3 * Real.pi / 2) / (Real.pi / 2) = 1) :
    a = 2 * Real.pi := by
  have hpi : (Real.pi / 2 : ℝ) ≠ 0 := by positivity
  field_simp at h; linarith

theorem div_pi2_eq_self {a b : ℝ} (ha : a = b) : a / (Real.pi / 2) = b / (Real.pi / 2) := by
  rw [ha]

/-- Junction helper: if `X p = Y q` and `p` is the right endpoint of `X`, then `q` is the left
endpoint of `Y`. -/
theorem junction_eq_zero {X Y : C(Set.Icc (0 : ℝ) 1, ℂ)} (hY : Function.Injective Y)
    {p q : Set.Icc (0 : ℝ) 1} (heq : X p = Y q) (hp : p = ⟨1, by norm_num⟩)
    (hXY : X ⟨1, by norm_num⟩ = Y ⟨0, by norm_num⟩) : q = ⟨0, by norm_num⟩ := by
  have hX1 : X p = X ⟨1, by norm_num⟩ := congrArg X hp
  have : Y q = Y ⟨0, by norm_num⟩ := by rw [← heq, hX1]; exact hXY
  exact hY this




/-- Junction helper: if `X p = Y q` and `q` is the left endpoint of `Y`, then `p` is the right
endpoint of `X`. -/
theorem junction_eq_one {X Y : C(Set.Icc (0 : ℝ) 1, ℂ)} (hX : Function.Injective X)
    {p q : Set.Icc (0 : ℝ) 1} (heq : X p = Y q) (hq : q = ⟨0, by norm_num⟩)
    (hXY : X ⟨1, by norm_num⟩ = Y ⟨0, by norm_num⟩) : p = ⟨1, by norm_num⟩ := by
  have hY0 : Y q = Y ⟨0, by norm_num⟩ := congrArg Y hq
  have : X p = X ⟨1, by norm_num⟩ := by rw [heq, hY0]; exact hXY.symm
  exact hX this

/-- **The four-arc curve is simple** when the arcs are injective and pairwise disjoint except at
the junctions. -/
theorem fourPlaneCurveSimplicity (A B C D : C(Set.Icc (0 : ℝ) 1, ℂ))
    (hAB : A ⟨1, by norm_num⟩ = B ⟨0, by norm_num⟩)
    (hBC : B ⟨1, by norm_num⟩ = C ⟨0, by norm_num⟩)
    (hCD : C ⟨1, by norm_num⟩ = D ⟨0, by norm_num⟩)
    (hDA : D ⟨1, by norm_num⟩ = A ⟨0, by norm_num⟩)
    (hA : Function.Injective A) (hB : Function.Injective B)
    (hC : Function.Injective C) (hD : Function.Injective D)
    (hAB' : ∀ u u' : Set.Icc (0 : ℝ) 1, A u = B u' → u = ⟨1, by norm_num⟩)
    (hBC' : ∀ u u' : Set.Icc (0 : ℝ) 1, B u = C u' → u = ⟨1, by norm_num⟩)
    (hCD' : ∀ u u' : Set.Icc (0 : ℝ) 1, C u = D u' → u = ⟨1, by norm_num⟩)
    (hDA' : ∀ u u' : Set.Icc (0 : ℝ) 1, D u = A u' → u' = ⟨0, by norm_num⟩)
    (hAC : ∀ u u' : Set.Icc (0 : ℝ) 1, A u ≠ C u')
    (hBD : ∀ u u' : Set.Icc (0 : ℝ) 1, B u ≠ D u') :
    (fourPlaneCurve A B C D hAB hBC hCD hDA).IsSimple := by
  intro τ hτ τ' hτ' heq
  have hpt : perPt τ = τ := perPt_self hτ
  have hpt' : perPt τ' = τ' := perPt_self hτ'
  have hfin : perPt τ = perPt τ' → τ = τ' := by
    intro hh; rw [← hpt, ← hpt']; exact hh
  have hq : ∀ σ ∈ Set.Ico (0 : ℝ) (2 * Real.pi),
      σ ≤ Real.pi / 2 ∨ (Real.pi / 2 ≤ σ ∧ σ ≤ Real.pi) ∨
      (Real.pi ≤ σ ∧ σ ≤ 3 * Real.pi / 2) ∨ (3 * Real.pi / 2 ≤ σ) := by
    intro σ hσ
    by_cases h : σ ≤ Real.pi / 2
    · exact Or.inl h
    · have h' : Real.pi / 2 ≤ σ := le_of_lt (not_le.mp h)
      by_cases h2 : σ ≤ Real.pi
      · exact Or.inr (Or.inl ⟨h', h2⟩)
      · have h2' : Real.pi ≤ σ := le_of_lt (not_le.mp h2)
        by_cases h3 : σ ≤ 3 * Real.pi / 2
        · exact Or.inr (Or.inr (Or.inl ⟨h2', h3⟩))
        · exact Or.inr (Or.inr (Or.inr (le_of_lt (not_le.mp h3))))
  rw [fourPlaneCurve_apply, fourPlaneCurve_apply] at heq
  rcases hq τ hτ with h1 | h1 | h1 | h1 <;> rcases hq τ' hτ' with h2 | h2 | h2 | h2
  · -- A / A
    rw [fourCurve_eq_A A B C D (by rw [hpt]; exact hτ.1) (by rw [hpt]; exact h1),
      fourCurve_eq_A A B C D (by rw [hpt']; exact hτ'.1) (by rw [hpt']; exact h2)] at heq
    exact hfin (div_pi2_eq (congrArg Subtype.val (hA heq)))
  · -- A / B
    rw [fourCurve_eq_A A B C D (by rw [hpt]; exact hτ.1) (by rw [hpt]; exact h1),
      fourCurve_eq_B A B C D hAB (by rw [hpt']; exact h2.1)
        (by rw [hpt']; exact h2.2)] at heq
    have hp := hAB' _ _ heq
    have hq0 := junction_eq_zero hB heq hp hAB
    exact hfin (by rw [div_pi2_eq_one (congrArg Subtype.val hp),
      sub_div_pi2_eq_zero (congrArg Subtype.val hq0)])
  · -- A / C
    rw [fourCurve_eq_A A B C D (by rw [hpt]; exact hτ.1) (by rw [hpt]; exact h1),
      fourCurve_eq_C A B C D hBC (by rw [hpt']; exact h2.1)
        (by rw [hpt']; exact h2.2)] at heq
    exact absurd heq (hAC _ _)
  · -- A / D
    rw [fourCurve_eq_A A B C D (by rw [hpt]; exact hτ.1) (by rw [hpt]; exact h1),
      fourCurve_eq_D A B C D hCD (by rw [hpt']; exact h2)] at heq
    have hq0 := hDA' _ _ heq.symm
    have hp1 := junction_eq_one hD heq.symm hq0 hDA
    exact absurd (sub3_div_pi2_eq_one (congrArg Subtype.val hp1))
      (by linarith [(perPt_mem τ').2])
  · -- B / A
    rw [fourCurve_eq_B A B C D hAB (by rw [hpt]; exact h1.1) (by rw [hpt]; exact h1.2),
      fourCurve_eq_A A B C D (by rw [hpt']; exact hτ'.1) (by rw [hpt']; exact h2)] at heq
    have hp := hAB' _ _ heq.symm
    have hq0 := junction_eq_zero hB heq.symm hp hAB
    exact hfin (by rw [div_pi2_eq_one (congrArg Subtype.val hp),
      sub_div_pi2_eq_zero (congrArg Subtype.val hq0)])
  · -- B / B
    rw [fourCurve_eq_B A B C D hAB (by rw [hpt]; exact h1.1) (by rw [hpt]; exact h1.2),
      fourCurve_eq_B A B C D hAB (by rw [hpt']; exact h2.1)
        (by rw [hpt']; exact h2.2)] at heq
    exact hfin (sub_div_pi2_eq (congrArg Subtype.val (hB heq)))
  · -- B / C
    rw [fourCurve_eq_B A B C D hAB (by rw [hpt]; exact h1.1) (by rw [hpt]; exact h1.2),
      fourCurve_eq_C A B C D hBC (by rw [hpt']; exact h2.1)
        (by rw [hpt']; exact h2.2)] at heq
    have hp := hBC' _ _ heq
    have hq0 := junction_eq_zero hC heq hp hBC
    exact hfin (by rw [sub_div_pi2_eq_one (congrArg Subtype.val hp),
      sub_pi_div_pi2_eq_zero (congrArg Subtype.val hq0)])
  · -- B / D
    rw [fourCurve_eq_B A B C D hAB (by rw [hpt]; exact h1.1) (by rw [hpt]; exact h1.2),
      fourCurve_eq_D A B C D hCD (by rw [hpt']; exact h2)] at heq
    exact absurd heq (hBD _ _)
  · -- C / A
    rw [fourCurve_eq_C A B C D hBC (by rw [hpt]; exact h1.1) (by rw [hpt]; exact h1.2),
      fourCurve_eq_A A B C D (by rw [hpt']; exact hτ'.1) (by rw [hpt']; exact h2)] at heq
    exact absurd heq.symm (hAC _ _)
  · -- C / B
    rw [fourCurve_eq_C A B C D hBC (by rw [hpt]; exact h1.1) (by rw [hpt]; exact h1.2),
      fourCurve_eq_B A B C D hAB (by rw [hpt']; exact h2.1)
        (by rw [hpt']; exact h2.2)] at heq
    have hp := hBC' _ _ heq.symm
    have hq0 := junction_eq_zero hC heq.symm hp hBC
    exact hfin (by rw [sub_div_pi2_eq_one (congrArg Subtype.val hp),
      sub_pi_div_pi2_eq_zero (congrArg Subtype.val hq0)])
  · -- C / C
    rw [fourCurve_eq_C A B C D hBC (by rw [hpt]; exact h1.1) (by rw [hpt]; exact h1.2),
      fourCurve_eq_C A B C D hBC (by rw [hpt']; exact h2.1)
        (by rw [hpt']; exact h2.2)] at heq
    exact hfin (sub_pi_div_pi2_eq (congrArg Subtype.val (hC heq)))
  · -- C / D
    rw [fourCurve_eq_C A B C D hBC (by rw [hpt]; exact h1.1) (by rw [hpt]; exact h1.2),
      fourCurve_eq_D A B C D hCD (by rw [hpt']; exact h2)] at heq
    have hp := hCD' _ _ heq
    have hq0 := junction_eq_zero hD heq hp hCD
    exact hfin (by rw [sub_pi_div_pi2_eq_one (congrArg Subtype.val hp),
      sub3_div_pi2_eq_zero (congrArg Subtype.val hq0)])
  · -- D / A
    rw [fourCurve_eq_D A B C D hCD (by rw [hpt]; exact h1),
      fourCurve_eq_A A B C D (by rw [hpt']; exact hτ'.1) (by rw [hpt']; exact h2)] at heq
    have hq0 := hDA' _ _ heq
    have hp1 := junction_eq_one hD heq hq0 hDA
    exact absurd (sub3_div_pi2_eq_one (congrArg Subtype.val hp1))
      (by linarith [(perPt_mem τ).2])
  · -- D / B
    rw [fourCurve_eq_D A B C D hCD (by rw [hpt]; exact h1),
      fourCurve_eq_B A B C D hAB (by rw [hpt']; exact h2.1)
        (by rw [hpt']; exact h2.2)] at heq
    exact absurd heq.symm (hBD _ _)
  · -- D / C
    rw [fourCurve_eq_D A B C D hCD (by rw [hpt]; exact h1),
      fourCurve_eq_C A B C D hBC (by rw [hpt']; exact h2.1)
        (by rw [hpt']; exact h2.2)] at heq
    have hp := hCD' _ _ heq.symm
    have hq0 := junction_eq_zero hD heq.symm hp hCD
    exact hfin (by rw [sub_pi_div_pi2_eq_one (congrArg Subtype.val hp),
      sub3_div_pi2_eq_zero (congrArg Subtype.val hq0)])
  · -- D / D
    rw [fourCurve_eq_D A B C D hCD (by rw [hpt]; exact h1),
      fourCurve_eq_D A B C D hCD (by rw [hpt']; exact h2)] at heq
    exact hfin (sub3_div_pi2_eq (congrArg Subtype.val (hD heq)))

/-! ## The target theorem -/

theorem thetaTwoComponentsSpansH
    (h : Work.Smooth.SphereJordan.PlaneHypothesis)
    {D₁ D₂ : Set Work.Smooth.SphereJordan.RiemannSphere}
    (hD₁ : ∃ f : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.RiemannSphere),
      Function.Injective f ∧ Set.range f = D₁)
    (hD₂ : ∃ g : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.RiemannSphere),
      Function.Injective g ∧ Set.range g = D₂)
    (hdisj : Disjoint D₁ D₂)
    (α β : C(Set.Icc (0 : ℝ) 1, Work.Smooth.SphereJordan.RiemannSphere))
    (hαinj : Function.Injective α) (hβinj : Function.Injective β)
    (hα₀ : α ⟨0, by norm_num⟩ ∈ D₁) (hα₁ : α ⟨1, by norm_num⟩ ∈ D₂)
    (hβ₀ : β ⟨0, by norm_num⟩ ∈ D₁) (hβ₁ : β ⟨1, by norm_num⟩ ∈ D₂)
    (hαint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → α t ∉ D₁ ∪ D₂)
    (hβint : ∀ t : Set.Icc (0 : ℝ) 1, (t : ℝ) ∈ Set.Ioo 0 1 → β t ∉ D₁ ∪ D₂)
    (hsep : ∀ s t : Set.Icc (0 : ℝ) 1, (s : ℝ) ∈ Set.Ioo 0 1 → (t : ℝ) ∈ Set.Ioo 0 1 →
      α s ≠ β t)
    (hαβ₀ : α ⟨0, by norm_num⟩ ≠ β ⟨0, by norm_num⟩)
    (hαβ₁ : α ⟨1, by norm_num⟩ ≠ β ⟨1, by norm_num⟩) :
    ∃ P₁ P₂ : Set Work.Smooth.SphereJordan.RiemannSphere,
      P₁.Nonempty ∧ P₂.Nonempty ∧ IsOpen P₁ ∧ IsOpen P₂ ∧ Disjoint P₁ P₂ ∧
      P₁ ∪ P₂ = Set.univ \ (D₁ ∪ D₂ ∪ Set.range α ∪ Set.range β) ∧
      IsPreconnected P₁ ∧ IsPreconnected P₂ ∧
      (∃ Φ : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.RiemannSphere),
        Function.Injective Φ ∧ Set.range Φ = closure P₁) ∧
      (∃ Ψ : C(Work.Smooth.SphereJordan.Disc, Work.Smooth.SphereJordan.RiemannSphere),
        Function.Injective Ψ ∧ Set.range Ψ = closure P₂) :=
  thetaSpansOfPlane h
    (fun {D₁ D₂} hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep hαβ₀ hαβ₁ =>
      planeThetaSpans h hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep
        hαβ₀ hαβ₁)
    hD₁ hD₂ hdisj α β hαinj hβinj hα₀ hα₁ hβ₀ hβ₁ hαint hβint hsep hαβ₀ hαβ₁

end

end Work.Smooth.SphereJordan
