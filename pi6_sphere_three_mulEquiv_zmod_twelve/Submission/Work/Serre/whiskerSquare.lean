import Mathlib

namespace Work.Serre

open scoped unitInterval

/-- The `whisker square` lemma: if `Q : I × I → X` is a square whose left and bottom edges are
degenerate at `x₀`, whose right edge is the loop `γ` and whose top edge is the loop `δ`, then
`γ` and `δ` are homotopic rel basepoint.

Geometrically: the boundary of `Q` is the loop `γ ⬝ δ⁻¹` (the remaining two edges are constant),
which is null-homotopic because it bounds the square `Q`; hence `γ ≃ δ`.

The homotopy is written down explicitly: we use the "L"-shaped part `Γ = {s = 0} ∪ {t = 0}` of the
square, on which `Q` is constantly `x₀`, and sweep the right edge onto the top edge through the
"fan" of straight segments joining the L to the corner `(1,1)`. -/
theorem whiskerSquare {X : Type} [TopologicalSpace X] {x₀ : X} (Q : C(unitInterval × unitInterval, X))
    (hbot : ∀ s : unitInterval, Q (s, 0) = x₀) (hleft : ∀ t : unitInterval, Q (0, t) = x₀)
    (γ δ : Path x₀ x₀) (hγ : ∀ t : unitInterval, Q (1, t) = γ t)
    (hδ : ∀ s : unitInterval, Q (s, 1) = δ s) :
    Path.Homotopic γ δ := by
  -- The "L" is parametrised by `P y = (max 0 (1 - 2y), max 0 (2y - 1))`, running from
  -- `(1,0)` (at `y = 0`) to `(0,1)` (at `y = 1`) through the corner `(0,0)` (at `y = 1/2`).
  have hP1mem : ∀ y : unitInterval, max 0 (1 - 2 * (y : ℝ)) ∈ Set.Icc (0:ℝ) 1 := by
    intro y
    refine ⟨le_max_left _ _, max_le zero_le_one ?_⟩
    linarith [unitInterval.nonneg y]
  have hP2mem : ∀ y : unitInterval, max 0 (2 * (y : ℝ) - 1) ∈ Set.Icc (0:ℝ) 1 := by
    intro y
    refine ⟨le_max_left _ _, max_le zero_le_one ?_⟩
    linarith [unitInterval.le_one y]
  have hSmem : ∀ p : unitInterval × unitInterval,
      (1 - (p.2 : ℝ)) * max 0 (1 - 2 * (p.1 : ℝ)) + (p.2 : ℝ) ∈ Set.Icc (0:ℝ) 1 := by
    intro p
    have h1 := hP1mem p.1
    have h0 := unitInterval.nonneg p.2
    have h2 := unitInterval.le_one p.2
    constructor <;> nlinarith [h1.1, h1.2, h0, h2]
  have hVmem : ∀ p : unitInterval × unitInterval,
      (1 - (p.2 : ℝ)) * max 0 (2 * (p.1 : ℝ) - 1) + (p.2 : ℝ) ∈ Set.Icc (0:ℝ) 1 := by
    intro p
    have h1 := hP2mem p.1
    have h0 := unitInterval.nonneg p.2
    have h2 := unitInterval.le_one p.2
    constructor <;> nlinarith [h1.1, h1.2, h0, h2]
  have hSc : Continuous fun p : unitInterval × unitInterval =>
      (1 - (p.2 : ℝ)) * max 0 (1 - 2 * (p.1 : ℝ)) + (p.2 : ℝ) := by
    have hA : Continuous fun p : unitInterval × unitInterval => (1 : ℝ) - 2 * (p.1 : ℝ) :=
      continuous_const.sub (continuous_const.mul (continuous_subtype_val.comp continuous_fst))
    have hB : Continuous fun p : unitInterval × unitInterval => max (0:ℝ) (1 - 2 * (p.1 : ℝ)) :=
      continuous_const.max hA
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul hB).add
      (continuous_subtype_val.comp continuous_snd)
  have hVc : Continuous fun p : unitInterval × unitInterval =>
      (1 - (p.2 : ℝ)) * max 0 (2 * (p.1 : ℝ) - 1) + (p.2 : ℝ) := by
    have hA : Continuous fun p : unitInterval × unitInterval => 2 * (p.1 : ℝ) - 1 :=
      (continuous_const.mul (continuous_subtype_val.comp continuous_fst)).sub continuous_const
    have hB : Continuous fun p : unitInterval × unitInterval => max (0:ℝ) (2 * (p.1 : ℝ) - 1) :=
      continuous_const.max hA
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul hB).add
      (continuous_subtype_val.comp continuous_snd)
  -- The "fan" map of the square to itself: it sends the L to itself and sweeps the right edge to
  -- the top edge.
  let Ψ : unitInterval × unitInterval → unitInterval × unitInterval := fun p =>
    (⟨(1 - (p.2 : ℝ)) * max 0 (1 - 2 * (p.1 : ℝ)) + (p.2 : ℝ), hSmem p⟩,
     ⟨(1 - (p.2 : ℝ)) * max 0 (2 * (p.1 : ℝ) - 1) + (p.2 : ℝ), hVmem p⟩)
  have hΨc : Continuous Ψ := Continuous.prodMk (hSc.subtype_mk hSmem) (hVc.subtype_mk hVmem)
  have hΨfst : ∀ p : unitInterval × unitInterval,
      ((Ψ p).1 : ℝ) = (1 - (p.2 : ℝ)) * max 0 (1 - 2 * (p.1 : ℝ)) + (p.2 : ℝ) := fun p => rfl
  have hΨsnd : ∀ p : unitInterval × unitInterval,
      ((Ψ p).2 : ℝ) = (1 - (p.2 : ℝ)) * max 0 (2 * (p.1 : ℝ) - 1) + (p.2 : ℝ) := fun p => rfl
  have hHc : Continuous fun p : unitInterval × unitInterval => Q (Ψ p) := Q.continuous.comp hΨc
  -- pointwise descriptions of `Ψ` on the four sides
  have hΨ0 : ∀ t : unitInterval, ((Ψ (0, t)).1 : ℝ) = 1 ∧ ((Ψ (0, t)).2 : ℝ) = (t : ℝ) := by
    intro t
    constructor
    · rw [hΨfst]; norm_num
    · rw [hΨsnd]; norm_num
  have hΨ1 : ∀ t : unitInterval, ((Ψ (1, t)).1 : ℝ) = (t : ℝ) ∧ ((Ψ (1, t)).2 : ℝ) = 1 := by
    intro t
    constructor
    · rw [hΨfst]; norm_num
    · rw [hΨsnd]; norm_num
  have hΨy0 : ∀ y : unitInterval, ((Ψ (y, 0)).1 : ℝ) = max 0 (1 - 2*(y:ℝ)) ∧
      ((Ψ (y, 0)).2 : ℝ) = max 0 (2*(y:ℝ) - 1) := by
    intro y
    constructor
    · rw [hΨfst]; norm_num
    · rw [hΨsnd]; norm_num
  have hΨy1 : ∀ y : unitInterval, ((Ψ (y, 1)).1 : ℝ) = 1 ∧ ((Ψ (y, 1)).2 : ℝ) = 1 := by
    intro y
    constructor
    · rw [hΨfst]; norm_num
    · rw [hΨsnd]; norm_num
  -- the product of the two coordinates of the L vanishes
  have hPprod : ∀ y : unitInterval, max 0 (1 - 2*(y:ℝ)) * max 0 (2*(y:ℝ) - 1) = 0 := by
    intro y
    rcases le_total (y:ℝ) (1/2) with h | h
    · rw [max_eq_left (by linarith : (2:ℝ)*(y:ℝ) - 1 ≤ 0)]
      ring
    · rw [max_eq_left (by linarith : (1:ℝ) - 2*(y:ℝ) ≤ 0)]
      ring
  -- `Q` vanishes as soon as one coordinate vanishes
  have hQmul : ∀ a b : unitInterval, (a:ℝ) * (b:ℝ) = 0 → Q (a,b) = x₀ := by
    intro a b hab
    rcases mul_eq_zero.mp hab with h | h
    · have ha : a = 0 := Subtype.ext (by simpa using h)
      rw [ha]; exact hleft b
    · have hb : b = 0 := Subtype.ext (by simpa using h)
      rw [hb]; exact hbot a
  have hH_y0 : ∀ y : unitInterval, Q (Ψ (y,0)) = x₀ := by
    intro y
    refine hQmul _ _ ?_
    rw [(hΨy0 y).1, (hΨy0 y).2]
    exact hPprod y
  have hH_y1 : ∀ y : unitInterval, Q (Ψ (y,1)) = x₀ := by
    intro y
    have h : Ψ (y,1) = ((1:unitInterval), (1:unitInterval)) := by
      ext <;> simp [hΨy1 y]
    rw [h]
    exact (hγ 1).trans γ.target
  have hH_0 : ∀ t : unitInterval, Q (Ψ (0,t)) = γ t := by
    intro t
    have h : Ψ (0,t) = ((1:unitInterval), t) := by
      ext <;> simp [hΨ0 t]
    rw [h]; exact hγ t
  have hH_1 : ∀ t : unitInterval, Q (Ψ (1,t)) = δ t := by
    intro t
    have h : Ψ (1,t) = (t, (1:unitInterval)) := by
      ext <;> simp [hΨ1 t]
    rw [h]; exact hδ t
  refine ⟨⟨⟨fun p => Q (Ψ p), hHc⟩, hH_0, hH_1⟩, ?_⟩
  intro y x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl
  · show Q (Ψ (y, 0)) = γ 0
    rw [hH_y0 y, γ.source]
  · show Q (Ψ (y, 1)) = γ 1
    rw [hH_y1 y, γ.target]

end Work.Serre
