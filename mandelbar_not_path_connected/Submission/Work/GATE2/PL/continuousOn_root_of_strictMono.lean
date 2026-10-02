import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.GATE2.PL

/-- If a jointly continuous family `T s z` is strictly increasing in `z` for every `s ∈ S`,
and `t s` is a root of `T s · = y` for `s ∈ S`, then `t` is continuous on `S`.

The proof is the implicit function theorem in this strictly monotone setting: for `s ∈ S` and
`ε > 0`, continuity of `T` at `(s, t s + ε)` and `(s, t s - ε)` gives a neighbourhood of `s`
on which `T x (t s - ε) < y < T x (t s + ε)`; strict monotonicity of `T x` then traps
`t x` strictly between `t s - ε` and `t s + ε`. -/
theorem continuousOn_root_of_strictMono {T : ℝ → ℝ → ℝ} {S : Set ℝ} {y : ℝ} {t : ℝ → ℝ}
    (hmono : ∀ s ∈ S, StrictMono (T s))
    (hcont : ∀ s ∈ S, ∀ z : ℝ, ContinuousAt (fun p : ℝ × ℝ => T p.1 p.2) (s, z))
    (ht : ∀ s ∈ S, T s (t s) = y) : ContinuousOn t S := by
  intro s hs
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set u := t s with hu
  have hTs : T s u = y := by rw [hu]; exact ht s hs
  have hsmono : StrictMono (T s) := hmono s hs
  have hplus : y < T s (u + ε) := by
    rw [← hTs]; exact hsmono (by linarith)
  have hminus : T s (u - ε) < y := by
    rw [← hTs]; exact hsmono (by linarith)
  -- Continuity of `T` at `(s, u + ε)` gives a `δ₁`: to the right of `u` the values exceed `y`.
  obtain ⟨δ₁, hδ₁pos, hδ₁⟩ :=
    (Metric.continuousAt_iff.mp (hcont s hs (u + ε))) ((T s (u + ε) - y) / 2) (by linarith)
  have hstep₁ : ∀ x, dist x s < δ₁ → y < T x (u + ε) := by
    intro x hx
    have hd : dist ((x, u + ε) : ℝ × ℝ) (s, u + ε) < δ₁ := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]; exact hx
    have h := hδ₁ hd
    have h' : dist (T x (u + ε)) (T s (u + ε)) < (T s (u + ε) - y) / 2 := h
    rw [Real.dist_eq] at h'
    have h2 := (abs_lt.mp h').1
    linarith
  -- Continuity of `T` at `(s, u - ε)` gives a `δ₂`: to the left of `u` the values fall below `y`.
  obtain ⟨δ₂, hδ₂pos, hδ₂⟩ :=
    (Metric.continuousAt_iff.mp (hcont s hs (u - ε))) ((y - T s (u - ε)) / 2) (by linarith)
  have hstep₂ : ∀ x, dist x s < δ₂ → T x (u - ε) < y := by
    intro x hx
    have hd : dist ((x, u - ε) : ℝ × ℝ) (s, u - ε) < δ₂ := by
      rw [Prod.dist_eq, dist_self, max_eq_left dist_nonneg]; exact hx
    have h := hδ₂ hd
    have h' : dist (T x (u - ε)) (T s (u - ε)) < (y - T s (u - ε)) / 2 := h
    rw [Real.dist_eq] at h'
    have h2 := (abs_lt.mp h').2
    linarith
  refine ⟨min δ₁ δ₂, lt_min hδ₁pos hδ₂pos, ?_⟩
  intro x hxS hxδ
  have hxδ₁ : dist x s < δ₁ := lt_of_lt_of_le hxδ (min_le_left _ _)
  have hxδ₂ : dist x s < δ₂ := lt_of_lt_of_le hxδ (min_le_right _ _)
  have h1 : T x (u - ε) < y := hstep₂ x hxδ₂
  have h2 : y < T x (u + ε) := hstep₁ x hxδ₁
  have hxmono : StrictMono (T x) := hmono x hxS
  have htx : T x (t x) = y := ht x hxS
  have hlow : u - ε < t x := (hxmono.lt_iff_lt).mp (by rw [htx]; linarith)
  have hhigh : t x < u + ε := (hxmono.lt_iff_lt).mp (by rw [htx]; linarith)
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

end Work.GATE2.PL
