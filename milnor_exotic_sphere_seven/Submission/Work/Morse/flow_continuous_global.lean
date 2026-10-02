import Mathlib
import Submission.Work.Morse.flow_basic

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Morse

open scoped Manifold ContDiff Topology

/-- A one-parameter family satisfying the group law and continuous on the strip `Ioo (-ε) ε × M` is
jointly continuous on all of `ℝ × M`. -/
theorem flow_continuous_global {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    {ε : ℝ} (hε : 0 < ε) {Φ : ℝ → M → M}
    (hgroup : ∀ s t x, Φ (s + t) x = Φ s (Φ t x))
    (hstrip : ContinuousOn (Function.uncurry Φ) (Set.Ioo (-ε) ε ×ˢ Set.univ)) :
    Continuous (Function.uncurry Φ) := by
  -- Continuity in the space variable for times inside the strip.
  have hslice : ∀ a ∈ Set.Ioo (-ε) ε, Continuous (fun x : M => Φ a x) := by
    intro a ha
    have h := hstrip.comp_continuous (continuous_const.prodMk continuous_id)
      (fun x => ⟨ha, Set.mem_univ x⟩)
    refine h.congr (fun x => ?_)
    simp [Function.uncurry_apply_pair]
  -- Continuity in the space variable for every time, by writing `t` as `N` equal small steps.
  have hxcont : ∀ t : ℝ, Continuous (fun x : M => Φ t x) := by
    intro t
    obtain ⟨N, hN1, hN2⟩ : ∃ N : ℕ, 1 ≤ N ∧ |t| < (N : ℝ) * ε := by
      refine ⟨⌊|t| / ε⌋₊ + 1, by omega, ?_⟩
      have h : |t| / ε < ((⌊|t| / ε⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast
        exact Nat.lt_floor_add_one _
      rw [div_lt_iff₀ hε] at h
      linarith
    set a : ℝ := t / N with ha
    have hNpos : (0 : ℝ) < N := by
      have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
      linarith
    have hNa : (N : ℝ) * a = t := by
      rw [ha, ← mul_div_assoc]
      exact mul_div_cancel_left₀ t (ne_of_gt hNpos)
    have habs : |a| < ε := by
      have hNabs : |(N : ℝ)| = (N : ℝ) := abs_of_nonneg (by positivity)
      rw [ha, abs_div, hNabs, div_lt_iff₀ hNpos]
      linarith [hN2, mul_comm (N : ℝ) ε]
    have hamem : a ∈ Set.Ioo (-ε) ε := abs_lt.mp habs
    have hga : Continuous (fun x : M => Φ a x) := hslice a hamem
    have hiter : ∀ k : ℕ, 1 ≤ k → ∀ x : M,
        Φ ((k : ℝ) * a) x = (fun y : M => Φ a y)^[k] x :=
      Nat.le_induction (m := 1)
        (P := fun k _ => ∀ x : M, Φ ((k : ℝ) * a) x = (fun y : M => Φ a y)^[k] x)
        (by intro x; simp)
        (fun k hk ih x => by
          have hcast : (((k + 1 : ℕ)) : ℝ) * a = (k : ℝ) * a + a := by push_cast; ring
          rw [hcast, hgroup, ih, Function.iterate_add_apply, Function.iterate_one])
    have hfinal : (fun x : M => Φ t x) = (fun y : M => Φ a y)^[N] := by
      funext x
      rw [← hNa]
      exact hiter N hN1 x
    rw [hfinal]
    exact hga.iterate N
  -- Joint continuity at an arbitrary point `(t₀, x₀)`, by translation to time `0`.
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, x₀⟩
  have hucont : Continuous (fun q : ℝ × M => (q.1 - t₀, Φ t₀ q.2)) :=
    (continuous_fst.sub continuous_const).prodMk ((hxcont t₀).comp continuous_snd)
  have hopen : Set.Ioo (-ε) ε ×ˢ (Set.univ : Set M) ∈ 𝓝 ((t₀ - t₀ : ℝ), Φ t₀ x₀) :=
    IsOpen.mem_nhds (isOpen_Ioo.prod isOpen_univ)
      ⟨by rw [sub_self]; exact ⟨by linarith, hε⟩, Set.mem_univ _⟩
  have hcont0 : ContinuousAt (Function.uncurry Φ) ((t₀ - t₀ : ℝ), Φ t₀ x₀) :=
    hstrip.continuousAt hopen
  have hcomp : ContinuousAt
      (Function.uncurry Φ ∘ (fun q : ℝ × M => (q.1 - t₀, Φ t₀ q.2))) (t₀, x₀) :=
    hcont0.comp (f := fun q : ℝ × M => (q.1 - t₀, Φ t₀ q.2)) (x := (t₀, x₀))
      hucont.continuousAt
  have heq : Function.uncurry Φ ∘ (fun q : ℝ × M => (q.1 - t₀, Φ t₀ q.2)) =
      Function.uncurry Φ := by
    funext q
    obtain ⟨t, x⟩ := q
    simp only [Function.comp_apply, Function.uncurry_apply_pair]
    rw [← hgroup (t - t₀) t₀ x, sub_add_cancel]
  rw [heq] at hcomp
  exact hcomp

end Work.Morse
