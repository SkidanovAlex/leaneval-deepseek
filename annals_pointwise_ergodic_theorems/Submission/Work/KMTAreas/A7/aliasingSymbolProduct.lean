import Mathlib
import Submission.Work.Analysis.IonescuWainger.Symbol
import Submission.Work.BourgainPlan.IonescuWainger.FreqArc

/-!
# The aliasing symbol product: `Σ c a · m(xi - a)` collapses to a single term

Let `A ⊆ 𝕋` be a finite set of frequencies whose arcs `a + [-2ε, 2ε]`, `a ∈ A`, are *separated*:
a point of `𝕋` lies in at most one of them.  Let `mt` be a symbol which equals `1` on the arc
`[-ε, ε]` at `0` and which can only be nonzero inside `[-2ε, 2ε]`, and let `pt` be a symbol which
can only be nonzero inside `[-ε, ε]`.  Then for every `xi : 𝕋`

  `(Σ_{a∈A} c a · mt (xi - a)) · (Σ_{a∈A} pt (xi - a)) = Σ_{a∈A} c a · pt (xi - a)`.

This is the elementary "aliasing" step of the single-scale Ionescu–Wainger analysis: because the
arcs are separated, at most one summand of each of the two sums on the left can be nonzero at the
frequency `xi`; at that summand `mt` takes the value `1`, so the two sums multiply as stated.
(If no `a ∈ A` has `xi - a` in the `ε`-arc at `0`, both sides vanish.)

The two auxiliary lemmas below are the elementary translations between membership of `xi - a` in
the arc at `0` and membership of `xi` in the arc centred at `a`, and the monotonicity of an arc in
its radius.
-/

namespace Work.KMTAreas.A7

/-- `xi - a` lies in the arc of radius `ε` centred at `0` iff `xi` lies in the arc of radius `ε`
centred at `a`. -/
lemma sub_mem_arcSet_zero_iff (xi a : Work.Analysis.IonescuWainger.Circle) (ε : ℝ) :
    xi - a ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 ε ↔
      xi ∈ Work.BourgainPlan.IonescuWainger.arcSet a ε := by
  constructor
  · rintro ⟨θ', hθ', hx⟩
    rw [zero_add] at hx
    exact ⟨θ', hθ', by rw [← hx]; simp⟩
  · rintro ⟨θ', hθ', hx⟩
    exact ⟨θ', hθ', by rw [hx, zero_add]; simp⟩

/-- An arc grows with its radius. -/
lemma arcSet_mono {ε δ : ℝ} (h : ε ≤ δ) (α : Work.Analysis.IonescuWainger.Circle) :
    Work.BourgainPlan.IonescuWainger.arcSet α ε ⊆
      Work.BourgainPlan.IonescuWainger.arcSet α δ :=
  fun _ ⟨θ, hθ, hξ⟩ => ⟨θ, le_trans hθ h, hξ⟩

theorem aliasingSymbolProduct (A : Finset Work.Analysis.IonescuWainger.Circle) (eps : ℝ) (heps : 0 < eps)
    (c : Work.Analysis.IonescuWainger.Circle → ℂ)
    (mt pt : Work.Analysis.IonescuWainger.Circle → ℂ)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, ∀ th : Work.Analysis.IonescuWainger.Circle,
      th ∈ Work.BourgainPlan.IonescuWainger.arcSet a (2 * eps) →
      th ∈ Work.BourgainPlan.IonescuWainger.arcSet b (2 * eps) → a = b)
    (hm1 : ∀ th : Work.Analysis.IonescuWainger.Circle,
      th ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 eps → mt th = 1)
    (hms : ∀ th : Work.Analysis.IonescuWainger.Circle, mt th ≠ 0 →
      th ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 (2 * eps))
    (hp : ∀ th : Work.Analysis.IonescuWainger.Circle, pt th ≠ 0 →
      th ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 eps)
    (xi : Work.Analysis.IonescuWainger.Circle) :
    (∑ a ∈ A, c a * mt (xi - a)) * (∑ a ∈ A, pt (xi - a))
      = ∑ a ∈ A, c a * pt (xi - a) := by
  by_cases h : ∃ a ∈ A, xi - a ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 eps
  · -- some `a0 ∈ A` has `xi - a0` in the arc of radius `eps`; it is the only contributing index
    obtain ⟨a0, ha0A, ha0⟩ := h
    have hmt_a0 : mt (xi - a0) = 1 := hm1 _ ha0
    -- `xi` lies in the arc of radius `2 * eps` centred at `a0`
    have hxi_a0 : xi ∈ Work.BourgainPlan.IonescuWainger.arcSet a0 (2 * eps) :=
      (sub_mem_arcSet_zero_iff xi a0 (2 * eps)).mp
        (arcSet_mono (by linarith) 0 ha0)
    -- every other index contributes nothing to either sum
    have key : ∀ a ∈ A, a ≠ a0 → mt (xi - a) = 0 ∧ pt (xi - a) = 0 := by
      intro a haA hne
      have hm : mt (xi - a) ≠ 0 → xi ∈ Work.BourgainPlan.IonescuWainger.arcSet a (2 * eps) :=
        fun hmm => (sub_mem_arcSet_zero_iff xi a (2 * eps)).mp (hms _ hmm)
      have hq : pt (xi - a) ≠ 0 → xi ∈ Work.BourgainPlan.IonescuWainger.arcSet a (2 * eps) :=
        fun hpp => (sub_mem_arcSet_zero_iff xi a (2 * eps)).mp
          (arcSet_mono (by linarith) 0 (hp _ hpp))
      have hz1 : mt (xi - a) = 0 := by
        by_contra hmm
        exact hne (hsep a haA a0 ha0A xi (hm hmm) hxi_a0)
      have hz2 : pt (xi - a) = 0 := by
        by_contra hpp
        exact hne (hsep a haA a0 ha0A xi (hq hpp) hxi_a0)
      exact ⟨hz1, hz2⟩
    have hL : (∑ a ∈ A, c a * mt (xi - a)) = c a0 := by
      rw [Finset.sum_eq_single a0 (fun b hb hne => by rw [(key b hb hne).1, mul_zero])
        (fun hna => absurd ha0A hna)]
      rw [hmt_a0, mul_one]
    have hS : (∑ a ∈ A, pt (xi - a)) = pt (xi - a0) := by
      rw [Finset.sum_eq_single a0 (fun b hb hne => (key b hb hne).2)
        (fun hna => absurd ha0A hna)]
    have hR : (∑ a ∈ A, c a * pt (xi - a)) = c a0 * pt (xi - a0) := by
      rw [Finset.sum_eq_single a0 (fun b hb hne => by rw [(key b hb hne).2, mul_zero])
        (fun hna => absurd ha0A hna)]
    rw [hL, hS, hR]
  · -- no index contributes at all: both sides vanish
    have hpt : ∀ a ∈ A, pt (xi - a) = 0 := by
      intro a ha
      by_contra hne
      exact h ⟨a, ha, hp _ hne⟩
    have h1 : (∑ a ∈ A, pt (xi - a)) = 0 := Finset.sum_eq_zero (fun a ha => hpt a ha)
    have h2 : (∑ a ∈ A, c a * pt (xi - a)) = 0 :=
      Finset.sum_eq_zero (fun a ha => by rw [hpt a ha, mul_zero])
    rw [h1, h2, mul_zero]

end Work.KMTAreas.A7
