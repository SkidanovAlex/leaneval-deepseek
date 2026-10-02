/-
Copyright: subproject `Submission/Work/Implosion/` of `mandelbar_not_path_connected`.

# The transit-phase blow-up `π/‖a‖` (HS §4, Prop. 4.6 and its remark)

`Disp.lean` shows that, in the Écalle coordinate, one iterate of the local normal
form `f(ζ) = ζ + (ζ²−a²)h(ζ)` displaces the coordinate `u` by

  `Φ(u) = (log(1+A₁) − log(1+A₂))/(2a)`,   `‖Φ(u) + 1‖ ≤ ε + 4‖a‖(1+ε)²`,

i.e. it is the translation `u ↦ u − 1` up to `δ := ε + 4‖a‖(1+ε)²`.

This file draws the quantitative consequence that Hubbard–Schleicher use to show
that parameter rays do not land: **the number of iterates needed to traverse the
Écalle cylinder from one end to the other blows up like `π/‖a‖`**.  Indeed the
punctures (ends) of the cylinder are the points `u ∈ (πi/a)ℤ`, successive ones
being `π/‖a‖` apart (`norm_period`); with unit speed and per-step error `δ`, the
travel time across `π/‖a‖` lies between `π/(‖a‖(1+δ))` and `π/(‖a‖(1−δ))`.
-/
import Submission.Work.Implosion.Disp

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Implosion

open Complex

/-! ## The lifted orbit in the Écalle cylinder -/

/-- The **model orbit** in the Écalle coordinate: `u_{n+1} = u_n + Φ(u_n)`.  Its
`n`-th point has the same multiplier `e^{2a·}` as the `n`-th iterate of `f`, by
`modelMap_eq_modelDisp_add_lattice`. -/
noncomputable def modelOrbit (a : ℂ) (h : ℂ → ℂ) (n : ℕ) (u : ℂ) : ℂ :=
  (fun v : ℂ => v + modelDisp a h v)^[n] u

theorem modelOrbit_eq_transitMap (a : ℂ) (h : ℂ → ℂ) (n : ℕ) (u : ℂ) :
    modelOrbit a h n u = (transitMap a h)^[n] u := rfl

@[simp] theorem modelOrbit_zero (a : ℂ) (h : ℂ → ℂ) (u : ℂ) : modelOrbit a h 0 u = u := rfl

theorem modelOrbit_succ (a : ℂ) (h : ℂ → ℂ) (n : ℕ) (u : ℂ) :
    modelOrbit a h (n + 1) u = modelOrbit a h n u + modelDisp a h (modelOrbit a h n u) := by
  simp only [modelOrbit, Function.iterate_succ_apply']

/-- The higher iterate of the model map. -/
noncomputable def modelMapOrbit (a : ℂ) (h : ℂ → ℂ) (n : ℕ) (u : ℂ) : ℂ :=
  (modelMap a h)^[n] u

/-! ## Cumulative displacement bounds -/

/-- The `n`-th point of the model orbit is `u − n` up to `n·δ`. -/
theorem norm_modelOrbit_sub_le (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (δ : ℝ) :
    ∀ n : ℕ, (∀ k : ℕ, k < n → ‖modelDisp a h (modelOrbit a h k u) + 1‖ ≤ δ) →
      ‖modelOrbit a h n u - (u - n)‖ ≤ n * δ := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ m ih =>
      intro hδ
      have hstep : ‖modelDisp a h (modelOrbit a h m u) + 1‖ ≤ δ := hδ m (Nat.lt_succ_self m)
      have hprev : ∀ k : ℕ, k < m → ‖modelDisp a h (modelOrbit a h k u) + 1‖ ≤ δ :=
        fun k hk => hδ k (Nat.lt_trans hk (Nat.lt_succ_self m))
      have hrec := ih hprev
      rw [modelOrbit_succ]
      have hdecomp : modelOrbit a h m u + modelDisp a h (modelOrbit a h m u) - (u - ↑(m + 1))
          = (modelOrbit a h m u - (u - ↑m)) + (modelDisp a h (modelOrbit a h m u) + 1) := by
        push_cast; ring
      rw [hdecomp]
      calc ‖(modelOrbit a h m u - (u - ↑m)) + (modelDisp a h (modelOrbit a h m u) + 1)‖
          ≤ ‖modelOrbit a h m u - (u - ↑m)‖ + ‖modelDisp a h (modelOrbit a h m u) + 1‖ :=
            norm_add_le _ _
        _ ≤ ↑m * δ + δ := add_le_add hrec hstep
        _ = ↑(m + 1) * δ := by push_cast; ring

/-- The real part of the `n`-th point of the model orbit is `Re u − n` up to `n·δ`. -/
theorem re_modelOrbit_le (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (δ : ℝ) :
    ∀ n : ℕ, (∀ k : ℕ, k < n → ‖modelDisp a h (modelOrbit a h k u) + 1‖ ≤ δ) →
      (modelOrbit a h n u).re ≤ u.re - n * (1 - δ) := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ m ih =>
      intro hδ
      have hstep := hδ m (Nat.lt_succ_self m)
      have hprev : ∀ k : ℕ, k < m → ‖modelDisp a h (modelOrbit a h k u) + 1‖ ≤ δ :=
        fun k hk => hδ k (Nat.lt_trans hk (Nat.lt_succ_self m))
      have hrec := ih hprev
      have hre : (modelDisp a h (modelOrbit a h m u)).re ≤ -1 + δ := by
        have := abs_le.1 (Complex.abs_re_le_norm
          (modelDisp a h (modelOrbit a h m u) + 1))
        simp at this
        linarith [this.2]
      rw [modelOrbit_succ, Complex.add_re]
      push_cast
      nlinarith [hrec, hre]

/-- The real part of the `n`-th point of the model orbit is `Re u − n` up to `n·δ`. -/
theorem re_modelOrbit_ge (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (δ : ℝ) :
    ∀ n : ℕ, (∀ k : ℕ, k < n → ‖modelDisp a h (modelOrbit a h k u) + 1‖ ≤ δ) →
      u.re - n * (1 + δ) ≤ (modelOrbit a h n u).re := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ m ih =>
      intro hδ
      have hstep := hδ m (Nat.lt_succ_self m)
      have hprev : ∀ k : ℕ, k < m → ‖modelDisp a h (modelOrbit a h k u) + 1‖ ≤ δ :=
        fun k hk => hδ k (Nat.lt_trans hk (Nat.lt_succ_self m))
      have hrec := ih hprev
      have hre : -1 - δ ≤ (modelDisp a h (modelOrbit a h m u)).re := by
        have := abs_le.1 (Complex.abs_re_le_norm
          (modelDisp a h (modelOrbit a h m u) + 1))
        simp at this
        linarith [this.1]
      rw [modelOrbit_succ, Complex.add_re]
      push_cast
      nlinarith [hrec, hre]

/-! ## The transit phase -/

/-- The punctures of the Écalle cylinder are spaced `π/‖a‖` in the coordinate `u`. -/
theorem norm_period (a : ℂ) (_ha : a ≠ 0) :
    ‖Real.pi * I / a‖ = Real.pi / ‖a‖ := by
  rw [norm_div, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, mul_one]

/-- **The transit phase blows up like `π/‖a‖` (lower bound).**  If a point of the
model orbit has moved by the distance `π/‖a‖` between two consecutive punctures,
then at least `π/(‖a‖(1+δ))` iterates were needed. -/
theorem transit_phase_lower (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (δ : ℝ) (ha : a ≠ 0)
    (hδ0 : 0 ≤ δ) {n : ℕ}
    (hδ : ∀ k : ℕ, k < n → ‖modelDisp a h (modelOrbit a h k u) + 1‖ ≤ δ)
    (hcross : (modelOrbit a h n u).re ≤ u.re - Real.pi / ‖a‖) :
    Real.pi / (‖a‖ * (1 + δ)) ≤ (n : ℝ) := by
  have hge := re_modelOrbit_ge a h u δ n hδ
  have hna : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha
  have h1 : Real.pi / ‖a‖ ≤ (n : ℝ) * (1 + δ) := by linarith
  have h2 : Real.pi ≤ (n : ℝ) * (1 + δ) * ‖a‖ := by
    rw [div_le_iff₀ hna] at h1; linarith
  rw [div_le_iff₀ (mul_pos hna (by linarith))]
  nlinarith [h2]

/-- **The transit phase blows up like `π/‖a‖` (upper bound).**  After
`π/(‖a‖(1−δ))` iterates the orbit has crossed the whole cylinder. -/
theorem transit_phase_upper (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (δ : ℝ) (ha : a ≠ 0)
    (_hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {n : ℕ}
    (hδ : ∀ k : ℕ, k < n → ‖modelDisp a h (modelOrbit a h k u) + 1‖ ≤ δ)
    (hn : Real.pi / (‖a‖ * (1 - δ)) ≤ (n : ℝ)) :
    (modelOrbit a h n u).re ≤ u.re - Real.pi / ‖a‖ := by
  have hle := re_modelOrbit_le a h u δ n hδ
  have hna : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr ha
  have hden : (0 : ℝ) < ‖a‖ * (1 - δ) := mul_pos hna (by linarith)
  have h2 : Real.pi ≤ (n : ℝ) * (1 - δ) * ‖a‖ := by
    rw [div_le_iff₀ hden] at hn; linarith
  have h3 : Real.pi / ‖a‖ ≤ (n : ℝ) * (1 - δ) := by
    rw [div_le_iff₀ hna]; linarith
  linarith

/-! ## The headline: transit phase `≈ π/‖a‖` with the explicit `Disp` error -/

/-- **The transit-phase blow-up `π/‖a‖`, with the explicit error of `Disp.lean`.**
If along the model orbit the Écalle point stays in `‖ζ‖ ≤ ρ ≤ ‖a‖`, where
`‖h − 1‖ ≤ ε`, then one iterate displaces the coordinate by `−1` up to
`δ = ε + 4‖a‖(1+ε)²`; hence crossing the `π/‖a‖` between two consecutive punctures
of the Écalle cylinder requires at least `π/(‖a‖(1+δ))` iterates.  This is the
Hubbard–Schleicher "egg-beater": the transit phase blows up as `‖a‖ → 0`. -/
theorem transit_phase_blowup (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (ρ ε : ℝ) (ha : a ≠ 0)
    (hρ : 0 ≤ ρ) (hε0 : 0 ≤ ε) (hερ : (ρ + ‖a‖) * (1 + ε) ≤ 1 / 2) (hρa : ρ ≤ ‖a‖)
    (hreg : ∀ k : ℕ, ‖ecalPt a (modelOrbit a h k u)‖ ≤ ρ)
    (hh : ∀ ζ : ℂ, ‖ζ‖ ≤ ρ → ‖h ζ - 1‖ ≤ ε) {n : ℕ}
    (hcross : (modelOrbit a h n u).re ≤ u.re - Real.pi / ‖a‖) :
    Real.pi / (‖a‖ * (1 + (ε + 4 * ‖a‖ * (1 + ε) ^ 2))) ≤ (n : ℝ) := by
  refine transit_phase_lower a h u (ε + 4 * ‖a‖ * (1 + ε) ^ 2) ha ?_ ?_ hcross
  · have hna : (0 : ℝ) ≤ ‖a‖ := norm_nonneg a
    nlinarith [sq_nonneg (1 + ε)]
  · intro k _
    exact norm_modelDisp_add_one_le_small a h (modelOrbit a h k u) ρ ε ha hρ hε0 hερ hρa
      (hreg k) hh

/-! ## Every orbit crosses every vertical line -/

/-- **Every model orbit crosses every vertical line** `Re u = x`: the transit map
decreases the Écalle phase by at least `1 − δ` at every step.  Together with
`modelOrbit_slab_at_most_once` this says that the slab `x ≤ Re u < x + W` is a
genuine fundamental domain (HS Prop. 4.1–4.2) in the Écalle coordinate. -/
theorem modelOrbit_eventually_lt (a : ℂ) (h : ℂ → ℂ) (u : ℂ) (δ x : ℝ) (hδ1 : δ < 1)
    (hδ : ∀ k : ℕ, ‖modelDisp a h (modelOrbit a h k u) + 1‖ ≤ δ) :
    ∃ n : ℕ, (modelOrbit a h n u).re < x := by
  refine ⟨⌈(u.re - x) / (1 - δ)⌉₊ + 1, ?_⟩
  have hpos : (0 : ℝ) < 1 - δ := by linarith
  have hle := re_modelOrbit_le a h u δ (⌈(u.re - x) / (1 - δ)⌉₊ + 1) (fun k _ => hδ k)
  have hceil : (u.re - x) / (1 - δ) ≤ (⌈(u.re - x) / (1 - δ)⌉₊ : ℝ) := Nat.le_ceil _
  have hmul : u.re - x < ((⌈(u.re - x) / (1 - δ)⌉₊ : ℝ) + 1) * (1 - δ) := by
    rw [div_le_iff₀ hpos] at hceil
    nlinarith [hceil, hpos]
  push_cast at hle
  linarith

end Work.Implosion
