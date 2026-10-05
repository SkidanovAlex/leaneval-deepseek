import Mathlib
import Submission.Work.RPB1a.Caratheodory.Brouwer.exists_exp_shift
import Submission.Work.RPB1a.Caratheodory.Brouwer.exp_arc_cover
import Submission.Work.RPB1a.Caratheodory.Brouwer.exp_arc_inter

namespace Work.RPB1a.Caratheodory.Brouwer

/-- **Splitting an embedded circle into two arcs.**

For a continuous injective `γ : Circle → ℂ` whose range contains `-1` and `1`, there are two
continuous paths `P`, `Q : ℝ → ℂ` (parametrised on `[-1,1]`, both running from `-1` to `1`,
injective on `[-1,1]`) whose images are exactly the two halves of `range γ` cut at `-1` and `1`:
their union is `range γ` and they meet exactly in the two endpoints `{-1, 1}`.

Concretely, `t ↦ γ (Circle.exp t)` is `2π`-periodic and injective on `[0, 2π)`, so after shifting the
parameter to send `-1` to the parameter `0`, and calling `t₁ ∈ (0, 2π)` a parameter with
`γ (Circle.exp t₁) = 1`, one may take `P s = γ (Circle.exp (t₁ (s+1)/2))` and
`Q s = γ (Circle.exp (t₁ + (2π - t₁)(1-s)/2))`. -/
theorem exists_jordan_arcs (γ : Circle → ℂ) (hγ : Continuous γ) (hinj : Function.Injective γ)
    (hm1 : (-1 : ℂ) ∈ Set.range γ) (h1 : (1 : ℂ) ∈ Set.range γ) :
    ∃ P Q : ℝ → ℂ, Continuous P ∧ Continuous Q ∧
      P (-1) = -1 ∧ P 1 = 1 ∧ Q (-1) = -1 ∧ Q 1 = 1 ∧
      Set.InjOn P (Set.Icc (-1 : ℝ) 1) ∧ Set.InjOn Q (Set.Icc (-1 : ℝ) 1) ∧
      (∀ t ∈ Set.Icc (-1 : ℝ) 1, P t ∈ Set.range γ) ∧
      (∀ t ∈ Set.Icc (-1 : ℝ) 1, Q t ∈ Set.range γ) ∧
      Set.range γ = P '' Set.Icc (-1 : ℝ) 1 ∪ Q '' Set.Icc (-1 : ℝ) 1 ∧
      P '' Set.Icc (-1 : ℝ) 1 ∩ Q '' Set.Icc (-1 : ℝ) 1 = {-1, 1} := by
  -- `-1` and `1` are attained at distinct points `a`, `b` of the circle.
  obtain ⟨a, ha⟩ := hm1
  obtain ⟨b, hb⟩ := h1
  have hab : a ≠ b := by
    intro h
    rw [h, hb] at ha
    norm_num at ha
  -- Parametrise the arc from `a` to `b` by angles in `[t0, t0 + t1]`, `0 < t1 < 2π`.
  obtain ⟨t0, t1, ht0, ht1, ht1pos, ht1lt⟩ := exists_exp_shift a b hab
  refine ⟨fun s => γ (Circle.exp (t0 + t1 * (s + 1) / 2)),
          fun s => γ (Circle.exp (t0 + t1 + (2 * Real.pi - t1) * (1 - s) / 2)),
          ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `P` is continuous.
    exact hγ.comp (Circle.exp.continuous.comp (by fun_prop))
  · -- `Q` is continuous.
    exact hγ.comp (Circle.exp.continuous.comp (by fun_prop))
  · -- `P (-1) = -1`.
    show γ (Circle.exp (t0 + t1 * ((-1 : ℝ) + 1) / 2)) = -1
    rw [show t0 + t1 * ((-1 : ℝ) + 1) / 2 = t0 by ring, ht0, ha]
  · -- `P 1 = 1`.
    show γ (Circle.exp (t0 + t1 * ((1 : ℝ) + 1) / 2)) = 1
    rw [show t0 + t1 * ((1 : ℝ) + 1) / 2 = t0 + t1 by ring, ht1, hb]
  · -- `Q (-1) = -1`.
    show γ (Circle.exp (t0 + t1 + (2 * Real.pi - t1) * (1 - (-1 : ℝ)) / 2)) = -1
    rw [show t0 + t1 + (2 * Real.pi - t1) * (1 - (-1 : ℝ)) / 2 = t0 + 2 * Real.pi by ring,
        Circle.exp_add_two_pi, ht0, ha]
  · -- `Q 1 = 1`.
    show γ (Circle.exp (t0 + t1 + (2 * Real.pi - t1) * (1 - (1 : ℝ)) / 2)) = 1
    rw [show t0 + t1 + (2 * Real.pi - t1) * (1 - (1 : ℝ)) / 2 = t0 + t1 by ring, ht1, hb]
  · -- `P` is injective on `[-1,1]`: the angle `t0 + t1*(s+1)/2` stays in an interval of
    -- length `t1 < 2π`, on which `Circle.exp` is injective, and the affine reparametrisation
    -- is injective because `t1 ≠ 0`.
    intro s hs s' hs' heq
    have hu : t0 + t1 * (s + 1) / 2 ∈ Set.Icc t0 (t0 + t1) := by
      constructor <;> nlinarith [hs.1, hs.2, ht1pos]
    have hu' : t0 + t1 * (s' + 1) / 2 ∈ Set.Icc t0 (t0 + t1) := by
      constructor <;> nlinarith [hs'.1, hs'.2, ht1pos]
    have hexp : Circle.exp (t0 + t1 * (s + 1) / 2) = Circle.exp (t0 + t1 * (s' + 1) / 2) :=
      hinj heq
    have hpar := Circle.exp_injOn_Icc (a := t0) (b := t0 + t1) (by linarith) hu hu' hexp
    nlinarith [hpar, ht1pos]
  · -- `Q` is injective on `[-1,1]`: same argument, with the interval
    -- `[t0 + t1, t0 + 2π]` of length `2π - t1 < 2π`.
    intro s hs s' hs' heq
    have hu : t0 + t1 + (2 * Real.pi - t1) * (1 - s) / 2
        ∈ Set.Icc (t0 + t1) (t0 + 2 * Real.pi) := by
      constructor <;> nlinarith [hs.1, hs.2, ht1lt]
    have hu' : t0 + t1 + (2 * Real.pi - t1) * (1 - s') / 2
        ∈ Set.Icc (t0 + t1) (t0 + 2 * Real.pi) := by
      constructor <;> nlinarith [hs'.1, hs'.2, ht1lt]
    have hexp : Circle.exp (t0 + t1 + (2 * Real.pi - t1) * (1 - s) / 2)
        = Circle.exp (t0 + t1 + (2 * Real.pi - t1) * (1 - s') / 2) := hinj heq
    have hpar := Circle.exp_injOn_Icc (a := t0 + t1) (b := t0 + 2 * Real.pi)
      (by linarith) hu hu' hexp
    nlinarith [hpar, ht1lt]
  · -- Every value of `P` lies on the curve.
    intro t ht
    exact Set.mem_range.mpr ⟨Circle.exp (t0 + t1 * (t + 1) / 2), rfl⟩
  · -- Every value of `Q` lies on the curve.
    intro t ht
    exact Set.mem_range.mpr ⟨Circle.exp (t0 + t1 + (2 * Real.pi - t1) * (1 - t) / 2), rfl⟩
  · -- The two arcs cover the whole curve.
    ext y
    constructor
    · intro hy
      rw [Set.mem_range] at hy
      obtain ⟨c, rfl⟩ := hy
      rcases exp_arc_cover t0 t1 ht1pos ht1lt c with ⟨s, hs, hsc⟩ | ⟨s, hs, hsc⟩
      · left
        refine ⟨s, hs, ?_⟩
        show γ (Circle.exp (t0 + t1 * (s + 1) / 2)) = γ c
        have hc : Circle.exp (t0 + t1 * (s + 1) / 2) = c := hsc
        rw [hc]
      · right
        refine ⟨s, hs, ?_⟩
        show γ (Circle.exp (t0 + t1 + (2 * Real.pi - t1) * (1 - s) / 2)) = γ c
        have hc : Circle.exp (t0 + t1 + (2 * Real.pi - t1) * (1 - s) / 2) = c := hsc
        rw [hc]
    · intro hy
      rcases hy with ⟨s, hs, rfl⟩ | ⟨s, hs, rfl⟩
      · exact Set.mem_range.mpr ⟨Circle.exp (t0 + t1 * (s + 1) / 2), rfl⟩
      · exact Set.mem_range.mpr ⟨Circle.exp (t0 + t1 + (2 * Real.pi - t1) * (1 - s) / 2), rfl⟩
  · -- The two arcs meet exactly in the two endpoints.
    ext y
    constructor
    · intro hy
      rw [Set.mem_inter_iff] at hy
      obtain ⟨⟨s, hs, hPs⟩, ⟨s', hs', hQs⟩⟩ := hy
      -- Retype the two equalities so that the parameters are explicit.
      have hPs' : γ (Circle.exp (t0 + t1 * (s + 1) / 2)) = y := hPs
      have hQs' : γ (Circle.exp (t0 + t1 + (2 * Real.pi - t1) * (1 - s') / 2)) = y := hQs
      have heqp : Circle.exp (t0 + t1 * (s + 1) / 2)
          = Circle.exp (t0 + t1 + (2 * Real.pi - t1) * (1 - s') / 2) :=
        hinj (by rw [hPs', hQs'])
      rw [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases exp_arc_inter t0 t1 s s' ht1pos ht1lt hs hs' heqp with h | h
      · left
        rw [← hPs', h, ht0, ha]
      · right
        rw [← hPs', h, ht1, hb]
    · intro hy
      rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · -- `-1` is attained by both arcs at the common endpoint `s = -1`.
        rw [Set.mem_inter_iff]
        refine ⟨⟨-1, by norm_num, ?_⟩, ⟨-1, by norm_num, ?_⟩⟩
        · show γ (Circle.exp (t0 + t1 * ((-1 : ℝ) + 1) / 2)) = -1
          rw [show t0 + t1 * ((-1 : ℝ) + 1) / 2 = t0 by ring, ht0, ha]
        · show γ (Circle.exp (t0 + t1 + (2 * Real.pi - t1) * (1 - (-1 : ℝ)) / 2)) = -1
          rw [show t0 + t1 + (2 * Real.pi - t1) * (1 - (-1 : ℝ)) / 2 = t0 + 2 * Real.pi by ring,
              Circle.exp_add_two_pi, ht0, ha]
      · -- `1` is attained by both arcs at the common endpoint `s = 1`.
        rw [Set.mem_inter_iff]
        refine ⟨⟨1, by norm_num, ?_⟩, ⟨1, by norm_num, ?_⟩⟩
        · show γ (Circle.exp (t0 + t1 * ((1 : ℝ) + 1) / 2)) = 1
          rw [show t0 + t1 * ((1 : ℝ) + 1) / 2 = t0 + t1 by ring, ht1, hb]
        · show γ (Circle.exp (t0 + t1 + (2 * Real.pi - t1) * (1 - (1 : ℝ)) / 2)) = 1
          rw [show t0 + t1 + (2 * Real.pi - t1) * (1 - (1 : ℝ)) / 2 = t0 + t1 by ring, ht1, hb]

end Work.RPB1a.Caratheodory.Brouwer
