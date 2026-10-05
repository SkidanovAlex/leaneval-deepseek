import Mathlib

/-!
# Extending a periodic slab function to a global smooth function

We construct, given a function `S` on the open slab `(-1,2) × ℝ × (-ρ₀,ρ₀)` which is `C^8`
there, periodic in the second variable, and vanishing on `ρ = 0` for `τ ∈ [0,1]`, a global
`C^8` function `S'` which is again periodic in `t`, vanishes on `ρ = 0` everywhere, and agrees
with `S` on the strip `[0,1] × ℝ × (-ρ₀/2, ρ₀/2)`.

The construction is `S' = Θ - Θ(·,·,0)` where `Θ = θ(τ)·ψ(ρ)·S`, with `θ` a smooth bump equal
to `1` near `[0,1]` and `0` near the boundary of `(-1,2)`, and `ψ` a smooth bump equal to `1`
near `[-ρ₀/2,ρ₀/2]` and `0` near the boundary of `(-ρ₀,ρ₀)`.  Since the support of `θψ` is a
compact subset of the open slab, `Θ` is globally `C^8`; it vanishes at `ρ = 0` outside `[0,1]`
and equals `S` on the strip (where `S(·,·,0) = 0`).
-/

namespace Work.RPB.B5

open scoped ContDiff

noncomputable section

/-- A smooth bump in the `τ`-variable: equal to `1` on `[-1/2, 3/2]` and to `0`
outside `(-3/4, 7/4)`. -/
def theta (τ : ℝ) : ℝ :=
  Real.smoothTransition (4 * τ + 3) * Real.smoothTransition (7 - 4 * τ)

/-- A smooth bump in the `ρ`-variable: equal to `1` on `[-3ρ₀/4, 3ρ₀/4]` and to `0`
outside `(-7ρ₀/8, 7ρ₀/8)`. -/
def psi (ρ₀ ρ : ℝ) : ℝ :=
  Real.smoothTransition (8 * ρ / ρ₀ + 7) * Real.smoothTransition (7 - 8 * ρ / ρ₀)

/-- The globally-defined cutoff version of `S`, `Θ τ t ρ = θ(τ) ψ(ρ) S τ t ρ`. -/
def Theta (S : ℝ → ℝ → ℝ → ℝ) (ρ₀ : ℝ) (z : ℝ × (ℝ × ℝ)) : ℝ :=
  theta z.1 * psi ρ₀ z.2.2 * S z.1 z.2.1 z.2.2

theorem theta_contDiff : ContDiff ℝ 8 theta := by unfold theta; fun_prop

theorem theta_eq_one {τ : ℝ} (h : τ ∈ Set.Icc (0 : ℝ) 1) : theta τ = 1 := by
  obtain ⟨h1, h2⟩ := h
  unfold theta
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.one_of_one_le (by linarith), mul_one]

theorem theta_eq_zero_of_le {τ : ℝ} (h : τ ≤ -3 / 4) : theta τ = 0 := by
  have hz : Real.smoothTransition (4 * τ + 3) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  unfold theta
  rw [hz, zero_mul]

theorem theta_eq_zero_of_ge {τ : ℝ} (h : 7 / 4 ≤ τ) : theta τ = 0 := by
  have hz : Real.smoothTransition (7 - 4 * τ) = 0 :=
    Real.smoothTransition.zero_of_nonpos (by linarith)
  unfold theta
  rw [hz, mul_zero]

theorem psi_contDiff (ρ₀ : ℝ) : ContDiff ℝ 8 (psi ρ₀) := by unfold psi; fun_prop

theorem psi_eq_one {ρ₀ ρ : ℝ} (hρ₀ : 0 < ρ₀)
    (h : ρ ∈ Set.Icc (-3 * ρ₀ / 4) (3 * ρ₀ / 4)) : psi ρ₀ ρ = 1 := by
  obtain ⟨h1, h2⟩ := h
  have hA : (1 : ℝ) ≤ 8 * ρ / ρ₀ + 7 := by
    have : (-6 : ℝ) ≤ 8 * ρ / ρ₀ := by rw [le_div_iff₀ hρ₀]; linarith
    linarith
  have hB : (1 : ℝ) ≤ 7 - 8 * ρ / ρ₀ := by
    have : 8 * ρ / ρ₀ ≤ (6 : ℝ) := by rw [div_le_iff₀ hρ₀]; linarith
    linarith
  unfold psi
  rw [Real.smoothTransition.one_of_one_le hA, Real.smoothTransition.one_of_one_le hB, mul_one]

theorem psi_eq_zero_of_le {ρ₀ ρ : ℝ} (hρ₀ : 0 < ρ₀) (h : ρ ≤ -7 * ρ₀ / 8) :
    psi ρ₀ ρ = 0 := by
  have hz : 8 * ρ / ρ₀ + 7 ≤ 0 := by
    have h' : 8 * ρ / ρ₀ ≤ (-7 : ℝ) := by rw [div_le_iff₀ hρ₀]; linarith
    linarith
  unfold psi
  rw [Real.smoothTransition.zero_of_nonpos hz, zero_mul]

theorem psi_eq_zero_of_ge {ρ₀ ρ : ℝ} (hρ₀ : 0 < ρ₀) (h : 7 * ρ₀ / 8 ≤ ρ) :
    psi ρ₀ ρ = 0 := by
  have hz : 7 - 8 * ρ / ρ₀ ≤ 0 := by
    have h' : (7 : ℝ) ≤ 8 * ρ / ρ₀ := by rw [le_div_iff₀ hρ₀]; linarith
    linarith
  unfold psi
  rw [Real.smoothTransition.zero_of_nonpos hz, mul_zero]

/-- The open slab `(-1,2) × ℝ × (-ρ₀,ρ₀)` on which `S` is `C^8`, with the middle factor
type-annotated so that it is an unambiguous `Set ℝ`. -/
theorem isOpen_slab (ρ₀ : ℝ) :
    IsOpen ((Set.Ioo (-1) 2 : Set ℝ) ×ˢ (Set.univ : Set ℝ) ×ˢ Set.Ioo (-ρ₀) ρ₀) :=
  (isOpen_Ioo (a := (-1 : ℝ)) (b := 2)).prod
    ((isOpen_univ (X := ℝ)).prod (isOpen_Ioo (a := -ρ₀) (b := ρ₀)))

/-- `Θ` is globally `C^8`: it is a product of smooth cutoffs with `S`, and the cutoffs are
supported in a compact subset of the open slab where `S` is `C^8`; where the cutoffs vanish,
`Θ` is locally zero. -/
theorem Theta_contDiff (S : ℝ → ℝ → ℝ → ℝ) (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀)
    (hS : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2)
        (Set.Ioo (-1) 2 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀)) :
    ContDiff ℝ 8 (Theta S ρ₀) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases h1 : z.1 < -3 / 4
  · have hmem : {w : ℝ × (ℝ × ℝ) | w.1 < -3 / 4} ∈ nhds z :=
      (isOpen_lt continuous_fst continuous_const).mem_nhds h1
    have hev : Theta S ρ₀ =ᶠ[nhds z] (fun _ => (0 : ℝ)) := by
      filter_upwards [hmem] with w hw
      simp only [Theta]
      rw [theta_eq_zero_of_le hw.le, zero_mul, zero_mul]
    exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
  · by_cases h2 : 7 / 4 < z.1
    · have hmem : {w : ℝ × (ℝ × ℝ) | 7 / 4 < w.1} ∈ nhds z :=
        (isOpen_lt continuous_const continuous_fst).mem_nhds h2
      have hev : Theta S ρ₀ =ᶠ[nhds z] (fun _ => (0 : ℝ)) := by
        filter_upwards [hmem] with w hw
        simp only [Theta]
        rw [theta_eq_zero_of_ge hw.le, zero_mul, zero_mul]
      exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
    · by_cases h3 : z.2.2 < -7 * ρ₀ / 8
      · have hmem : {w : ℝ × (ℝ × ℝ) | w.2.2 < -7 * ρ₀ / 8} ∈ nhds z :=
          (isOpen_lt (continuous_snd.comp continuous_snd) continuous_const).mem_nhds h3
        have hev : Theta S ρ₀ =ᶠ[nhds z] (fun _ => (0 : ℝ)) := by
          filter_upwards [hmem] with w hw
          simp only [Theta]
          rw [psi_eq_zero_of_le hρ₀ hw.le, mul_zero, zero_mul]
        exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
      · by_cases h4 : 7 * ρ₀ / 8 < z.2.2
        · have hmem : {w : ℝ × (ℝ × ℝ) | 7 * ρ₀ / 8 < w.2.2} ∈ nhds z :=
            (isOpen_lt continuous_const (continuous_snd.comp continuous_snd)).mem_nhds h4
          have hev : Theta S ρ₀ =ᶠ[nhds z] (fun _ => (0 : ℝ)) := by
            filter_upwards [hmem] with w hw
            simp only [Theta]
            rw [psi_eq_zero_of_ge hρ₀ hw.le, mul_zero, zero_mul]
          exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq hev
        · have h1' : -3 / 4 ≤ z.1 := not_lt.mp h1
          have h2' : z.1 ≤ 7 / 4 := not_lt.mp h2
          have h3' : -7 * ρ₀ / 8 ≤ z.2.2 := not_lt.mp h3
          have h4' : z.2.2 ≤ 7 * ρ₀ / 8 := not_lt.mp h4
          have hzmem : z ∈ (Set.Ioo (-1) 2 : Set ℝ) ×ˢ (Set.univ : Set ℝ)
              ×ˢ Set.Ioo (-ρ₀) ρ₀ := by
            simp only [Set.mem_prod, Set.mem_Ioo, Set.mem_univ, true_and]
            refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> linarith [hρ₀]
          have hS' : ContDiffAt ℝ 8 (fun w : ℝ × (ℝ × ℝ) => S w.1 w.2.1 w.2.2) z :=
            hS.contDiffAt ((isOpen_slab ρ₀).mem_nhds hzmem)
          have hθ : ContDiffAt ℝ 8 (fun w : ℝ × (ℝ × ℝ) => theta w.1) z :=
            (by unfold theta; fun_prop :
              ContDiff ℝ 8 (fun w : ℝ × (ℝ × ℝ) => theta w.1)).contDiffAt
          have hψ : ContDiffAt ℝ 8 (fun w : ℝ × (ℝ × ℝ) => psi ρ₀ w.2.2) z :=
            (by unfold psi; fun_prop :
              ContDiff ℝ 8 (fun w : ℝ × (ℝ × ℝ) => psi ρ₀ w.2.2)).contDiffAt
          show ContDiffAt ℝ 8 (fun x : ℝ × (ℝ × ℝ) =>
            theta x.1 * psi ρ₀ x.2.2 * S x.1 x.2.1 x.2.2) z
          exact (hθ.mul hψ).mul hS'

theorem slabGlobalExtendPeriodic (S : ℝ → ℝ → ℝ → ℝ) (ρ₀ : ℝ) (hρ₀ : 0 < ρ₀)
    (hS : ContDiffOn ℝ 8 (fun z : ℝ × (ℝ × ℝ) => S z.1 z.2.1 z.2.2)
        (Set.Ioo (-1) 2 ×ˢ Set.univ ×ˢ Set.Ioo (-ρ₀) ρ₀))
    (hper : ∀ τ t ρ, S τ (t + 2 * Real.pi) ρ = S τ t ρ)
    (h0 : ∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t, S τ t 0 = 0) :
    ∃ S' : ℝ → ℝ → ℝ → ℝ,
      ContDiff ℝ 8 (fun z : ℝ × (ℝ × ℝ) => S' z.1 z.2.1 z.2.2) ∧
      (∀ τ t ρ, S' τ (t + 2 * Real.pi) ρ = S' τ t ρ) ∧
      (∀ τ t, S' τ t 0 = 0) ∧
      (∀ τ ∈ Set.Icc (0 : ℝ) 1, ∀ t ρ, |ρ| < ρ₀ / 2 → S' τ t ρ = S τ t ρ) := by
  refine ⟨fun τ t ρ => Theta S ρ₀ (τ, (t, ρ)) - Theta S ρ₀ (τ, (t, 0)), ?_, ?_, ?_, ?_⟩
  · exact (Theta_contDiff S ρ₀ hρ₀ hS).sub
      ((Theta_contDiff S ρ₀ hρ₀ hS).comp (by fun_prop))
  · intro τ t ρ
    have hper' : ∀ τ t ρ, Theta S ρ₀ (τ, (t + 2 * Real.pi, ρ)) = Theta S ρ₀ (τ, (t, ρ)) := by
      intro τ t ρ
      simp only [Theta]
      rw [hper τ t ρ]
    show Theta S ρ₀ (τ, (t + 2 * Real.pi, ρ)) - Theta S ρ₀ (τ, (t + 2 * Real.pi, 0))
        = Theta S ρ₀ (τ, (t, ρ)) - Theta S ρ₀ (τ, (t, 0))
    rw [hper' τ t ρ, hper' τ t 0]
  · intro τ t
    show Theta S ρ₀ (τ, (t, 0)) - Theta S ρ₀ (τ, (t, 0)) = 0
    rw [sub_self]
  · intro τ hτ t ρ hρ
    have hψ : psi ρ₀ ρ = 1 := by
      apply psi_eq_one hρ₀
      rw [abs_lt] at hρ
      exact ⟨by linarith [hρ₀, hρ.1], by linarith [hρ₀, hρ.2]⟩
    show Theta S ρ₀ (τ, (t, ρ)) - Theta S ρ₀ (τ, (t, 0)) = S τ t ρ
    have h1 : Theta S ρ₀ (τ, (t, ρ)) = S τ t ρ := by
      simp only [Theta, theta_eq_one hτ, hψ, one_mul]
    have h2 : Theta S ρ₀ (τ, (t, 0)) = 0 := by
      simp only [Theta, theta_eq_one hτ]
      rw [h0 τ hτ t, mul_zero]
    rw [h1, h2, sub_zero]

end

end Work.RPB.B5
