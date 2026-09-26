import Mathlib
import Submission.Work.Smooth.Morse.Defs

/-!
# A positive lower bound for the descent rate on a critical-free level band

The descent field of the chapter,
`Work.Smooth.Morse.descentField ψ g p = -((1 + (∂₁G)² + (∂₂G)²)⁻¹) • (∂₁G, ∂₂G)` (with
`G = pullback ψ g`), decreases the level of `G` at the rate

`Work.Smooth.Morse.descentRate ψ g p = ((∂₁G)² + (∂₂G)²) / (1 + (∂₁G)² + (∂₂G)²)`,

which vanishes exactly at the critical points of `G`.  On a band of levels `{a ≤ G ≤ b}` all of
whose values are regular, the parameter-plane band therefore contains no critical point, and being
a closed, `2πℤ²`-invariant subset of the parameter plane it is "compact modulo the period
lattice": it is the full preimage of a closed subset of the compact surface `F = ψ(standard
torus)`.  Hence `descentRate` --- continuous because `g` is `C¹` --- attains a positive minimum
there:

`∃ δ > 0, ∀ q, pullback ψ g q ∈ [a, b] → δ ≤ descentRate ψ g q`.

This is the quantitative input which turns the *local* non-vanishing of the gradient on a
critical-free band into a *uniform* positive rate of descent along the flow (see
`Submission.Work.Smooth.Morse.Flow.pullback_flow_descends_of_eta`).

## Implementation

Everything is done in the parameter plane, using `2πℤ²`-periodicity of `pullback ψ g` (hence of
its derivative, of the two coordinate derivatives and of `descentRate`) together with the fact
that every parameter can be shifted by an element of the lattice into the fundamental square
`[0, 2π] × [0, 2π]`.
-/

namespace Work.Smooth.Morse.Flow

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-! ## The vanishing of the derivative and of the two coordinate derivatives -/

/-- A continuous linear functional on the parameter plane is determined by its two coordinate
derivatives: `L (x, y) = x * L (1, 0) + y * L (0, 1)`. -/
lemma clm_pair_apply (L : (ℝ × ℝ) →L[ℝ] ℝ) (x y : ℝ) :
    L (x, y) = x * L (1, 0) + y * L (0, 1) := by
  have hv : (x, y) = x • ((1 : ℝ), (0 : ℝ)) + y • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [hv, map_add, map_smul, map_smul]
  simp

/-- The derivative of `G = pullback ψ g` vanishes exactly where both coordinate derivatives
vanish. -/
lemma fderiv_pullback_eq_zero_iff (ψ : Submission.Diffeo) (g : R3 → ℝ) (p : ℝ × ℝ) :
    fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p = 0 ↔
      Work.Smooth.Morse.partialD₁ ψ g p = 0 ∧ Work.Smooth.Morse.partialD₂ ψ g p = 0 := by
  constructor
  · intro h
    exact ⟨by simp [Work.Smooth.Morse.partialD₁, h],
      by simp [Work.Smooth.Morse.partialD₂, h]⟩
  · rintro ⟨h1, h2⟩
    apply ContinuousLinearMap.ext
    rintro ⟨x, y⟩
    simp only [Work.Smooth.Morse.partialD₁, Work.Smooth.Morse.partialD₂] at h1 h2
    rw [clm_pair_apply (fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p) x y, h1, h2]
    simp

/-- **The descent rate is positive at every regular point**: where the derivative of `G` does not
vanish, the rational expression defining `descentRate` has a positive numerator. -/
lemma descentRate_pos_of_fderiv_ne_zero (ψ : Submission.Diffeo) (g : R3 → ℝ) {p : ℝ × ℝ}
    (hp : fderiv ℝ (Work.Smooth.Morse.pullback ψ g) p ≠ 0) :
    0 < Work.Smooth.Morse.descentRate ψ g p := by
  have hne : Work.Smooth.Morse.partialD₁ ψ g p ≠ 0 ∨
      Work.Smooth.Morse.partialD₂ ψ g p ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hp ((fderiv_pullback_eq_zero_iff ψ g p).mpr ⟨hc.1, hc.2⟩)
  have hnum : 0 < (Work.Smooth.Morse.partialD₁ ψ g p) ^ 2 +
      (Work.Smooth.Morse.partialD₂ ψ g p) ^ 2 := by
    rcases hne with h | h
    · nlinarith [sq_nonneg (Work.Smooth.Morse.partialD₂ ψ g p), sq_pos_of_ne_zero h]
    · nlinarith [sq_nonneg (Work.Smooth.Morse.partialD₁ ψ g p), sq_pos_of_ne_zero h]
  unfold Work.Smooth.Morse.descentRate
  exact div_pos hnum (by positivity)

/-- Continuity of the descent rate, for `g` of class `C¹`. -/
lemma continuous_descentRate (ψ : Submission.Diffeo) {g : R3 → ℝ} (hg : ContDiff ℝ 1 g) :
    Continuous (Work.Smooth.Morse.descentRate ψ g) := by
  have hfd : Continuous (fderiv ℝ (Work.Smooth.Morse.pullback ψ g)) :=
    (Work.Smooth.Morse.pullback_contDiff_one ψ hg).continuous_fderiv one_ne_zero
  have hd1 : Continuous (Work.Smooth.Morse.partialD₁ ψ g) := by
    unfold Work.Smooth.Morse.partialD₁
    exact hfd.clm_apply continuous_const
  have hd2 : Continuous (Work.Smooth.Morse.partialD₂ ψ g) := by
    unfold Work.Smooth.Morse.partialD₂
    exact hfd.clm_apply continuous_const
  have hnum : Continuous (fun p : ℝ × ℝ => (Work.Smooth.Morse.partialD₁ ψ g p) ^ 2 +
      (Work.Smooth.Morse.partialD₂ ψ g p) ^ 2) := (hd1.pow 2).add (hd2.pow 2)
  have hden : Continuous (fun p : ℝ × ℝ => 1 + (Work.Smooth.Morse.partialD₁ ψ g p) ^ 2 +
      (Work.Smooth.Morse.partialD₂ ψ g p) ^ 2) :=
    (continuous_const.add (hd1.pow 2)).add (hd2.pow 2)
  unfold Work.Smooth.Morse.descentRate
  exact hnum.div hden (fun p => by positivity)

/-! ## Periodicity in the parameter plane -/

/-- **The parametrisation is invariant under the period lattice `2πℤ²`.** -/
lemma param_add_lattice (ψ : Submission.Diffeo) (q : ℝ × ℝ) (k l : ℤ) :
    Work.Smooth.Morse.param ψ (q.1 + (k : ℝ) * (2 * Real.pi), q.2 + (l : ℝ) * (2 * Real.pi)) =
      Work.Smooth.Morse.param ψ q := by
  have hperθ : Function.Periodic
      (fun θ : ℝ => Work.Core.torusMap θ (q.2 + (l : ℝ) * (2 * Real.pi))) (2 * Real.pi) :=
    fun θ => Work.Core.torusMap_add_two_pi_left θ _
  have hperφ : Function.Periodic (fun φ : ℝ => Work.Core.torusMap q.1 φ) (2 * Real.pi) :=
    fun φ => Work.Core.torusMap_add_two_pi_right q.1 φ
  have h1 : Work.Core.torusMap (q.1 + (k : ℝ) * (2 * Real.pi))
        (q.2 + (l : ℝ) * (2 * Real.pi)) = Work.Core.torusMap q.1 q.2 :=
    ((hperθ.int_mul k) q.1).trans ((hperφ.int_mul l) q.2)
  show ψ (Work.Core.torusMap (q.1 + (k : ℝ) * (2 * Real.pi))
      (q.2 + (l : ℝ) * (2 * Real.pi))) = ψ (Work.Core.torusMap q.1 q.2)
  rw [h1]

/-- **`G = pullback ψ g` is invariant under the period lattice `2πℤ²`.** -/
lemma pullback_add_lattice (ψ : Submission.Diffeo) (g : R3 → ℝ) (q : ℝ × ℝ) (k l : ℤ) :
    Work.Smooth.Morse.pullback ψ g (q.1 + (k : ℝ) * (2 * Real.pi), q.2 + (l : ℝ) * (2 * Real.pi)) =
      Work.Smooth.Morse.pullback ψ g q := by
  simp only [Work.Smooth.Morse.pullback]
  rw [param_add_lattice ψ q k l]

/-- **The derivative of an invariant function is invariant.**  If `f (x + (c₁, c₂)) = f x` for
all `x`, then `fderiv ℝ f` is invariant under the same shift. -/
lemma fderiv_pair_shift_of_invariant {f : ℝ × ℝ → ℝ} {c₁ c₂ : ℝ}
    (h : ∀ x : ℝ × ℝ, f (x.1 + c₁, x.2 + c₂) = f x) (x : ℝ × ℝ) :
    fderiv ℝ f (x.1 + c₁, x.2 + c₂) = fderiv ℝ f x := by
  have hper : ∀ y : ℝ × ℝ, f (y + (c₁, c₂)) = f y := by
    intro y
    rw [show y + (c₁, c₂) = (y.1 + c₁, y.2 + c₂) from Prod.ext rfl rfl]
    exact h y
  have h1 : (fun y : ℝ × ℝ => f (y + (c₁, c₂))) = f := funext hper
  have h2 : fderiv ℝ (fun y : ℝ × ℝ => f (y + (c₁, c₂))) x =
      fderiv ℝ f (x + (c₁, c₂)) := fderiv_comp_add_right (c₁, c₂)
  rw [h1] at h2
  rw [show x + (c₁, c₂) = (x.1 + c₁, x.2 + c₂) from Prod.ext rfl rfl] at h2
  exact h2.symm

/-- **The derivative of `G = pullback ψ g` is invariant under the period lattice.** -/
lemma fderiv_pullback_add_lattice (ψ : Submission.Diffeo) (g : R3 → ℝ) (q : ℝ × ℝ)
    (k l : ℤ) :
    fderiv ℝ (Work.Smooth.Morse.pullback ψ g)
        (q.1 + (k : ℝ) * (2 * Real.pi), q.2 + (l : ℝ) * (2 * Real.pi)) =
      fderiv ℝ (Work.Smooth.Morse.pullback ψ g) q :=
  fderiv_pair_shift_of_invariant (fun x => pullback_add_lattice ψ g x k l) q

/-- **The coordinate derivative `∂₁G` is invariant under the period lattice.** -/
lemma partialD₁_add_lattice (ψ : Submission.Diffeo) (g : R3 → ℝ) (q : ℝ × ℝ) (k l : ℤ) :
    Work.Smooth.Morse.partialD₁ ψ g
        (q.1 + (k : ℝ) * (2 * Real.pi), q.2 + (l : ℝ) * (2 * Real.pi)) =
      Work.Smooth.Morse.partialD₁ ψ g q := by
  unfold Work.Smooth.Morse.partialD₁
  rw [fderiv_pullback_add_lattice]

/-- **The coordinate derivative `∂₂G` is invariant under the period lattice.** -/
lemma partialD₂_add_lattice (ψ : Submission.Diffeo) (g : R3 → ℝ) (q : ℝ × ℝ) (k l : ℤ) :
    Work.Smooth.Morse.partialD₂ ψ g
        (q.1 + (k : ℝ) * (2 * Real.pi), q.2 + (l : ℝ) * (2 * Real.pi)) =
      Work.Smooth.Morse.partialD₂ ψ g q := by
  unfold Work.Smooth.Morse.partialD₂
  rw [fderiv_pullback_add_lattice]

/-- **The descent rate is invariant under the period lattice.** -/
lemma descentRate_add_lattice (ψ : Submission.Diffeo) (g : R3 → ℝ) (q : ℝ × ℝ) (k l : ℤ) :
    Work.Smooth.Morse.descentRate ψ g
        (q.1 + (k : ℝ) * (2 * Real.pi), q.2 + (l : ℝ) * (2 * Real.pi)) =
      Work.Smooth.Morse.descentRate ψ g q := by
  unfold Work.Smooth.Morse.descentRate
  rw [partialD₁_add_lattice ψ g q k l, partialD₂_add_lattice ψ g q k l]

/-! ## Shifting a parameter into the fundamental square -/

/-- Every real number can be shifted by an integer multiple of `2π` into `[0, 2π]`. -/
lemma exists_int_shift_mem_Icc (x : ℝ) :
    ∃ k : ℤ, x + (k : ℝ) * (2 * Real.pi) ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := by
  have hπ : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨-⌊x / (2 * Real.pi)⌋, ?_⟩
  have hx : x + ((-⌊x / (2 * Real.pi)⌋ : ℤ) : ℝ) * (2 * Real.pi) =
      (2 * Real.pi) * Int.fract (x / (2 * Real.pi)) := by
    rw [Int.fract]; push_cast; field_simp; ring
  rw [hx]
  exact ⟨mul_nonneg hπ.le (Int.fract_nonneg _),
    mul_le_of_le_one_right hπ.le (Int.fract_lt_one _).le⟩

/-! ## The lower bound -/

theorem exists_descentRate_lower_bound (ψ : Submission.Diffeo) {g : LeanEval.KnotTheory.PardonDistortion.R3 → ℝ} (hg : ContDiff ℝ 1 g) {a b : ℝ} (hab : a ≤ b) (hreg : ∀ t ∈ Set.Icc a b, Work.Smooth.Morse.IsRegularValue ψ g t) : ∃ δ : ℝ, 0 < δ ∧ ∀ q : ℝ × ℝ, Work.Smooth.Morse.pullback ψ g q ∈ Set.Icc a b → δ ≤ Work.Smooth.Morse.descentRate ψ g q := by
  -- `hab` is not needed by the argument below (when `b < a` the band `{a ≤ G ≤ b}` is empty and
  -- the statement is vacuous anyway); it is recorded for completeness.
  have _hab : a ≤ b := hab
  have hrate : Continuous (Work.Smooth.Morse.descentRate ψ g) := continuous_descentRate ψ hg
  have hGcont : Continuous (Work.Smooth.Morse.pullback ψ g) :=
    (Work.Smooth.Morse.pullback_contDiff_one ψ hg).continuous
  -- The band of parameters whose level lies in `[a, b]`, and its part in the fundamental square.
  set B : Set (ℝ × ℝ) :=
    {q : ℝ × ℝ | Work.Smooth.Morse.pullback ψ g q ∈ Set.Icc a b} with hB
  set K : Set (ℝ × ℝ) :=
    B ∩ (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) with hK
  have hclosed : IsClosed B := by
    rw [hB]
    exact isClosed_Icc.preimage hGcont
  have hKcompact : IsCompact K := by
    rw [hK]
    exact (isCompact_Icc.prod isCompact_Icc).inter_left hclosed
  by_cases hne : K.Nonempty
  · -- The band meets the fundamental square: take the minimum of the descent rate there.
    obtain ⟨q₀, hq₀K, hmin⟩ := hKcompact.exists_isMinOn hne hrate.continuousOn
    have hq₀B : Work.Smooth.Morse.pullback ψ g q₀ ∈ Set.Icc a b := by
      have := hq₀K.1
      rwa [hB] at this
    refine ⟨Work.Smooth.Morse.descentRate ψ g q₀, ?_, ?_⟩
    · exact descentRate_pos_of_fderiv_ne_zero ψ g
        ((Work.Smooth.Morse.isRegularValue_iff ψ g _).mp (hreg _ hq₀B) q₀ rfl)
    · intro q hq
      obtain ⟨k, hk⟩ := exists_int_shift_mem_Icc q.1
      obtain ⟨l, hl⟩ := exists_int_shift_mem_Icc q.2
      have hq'B : Work.Smooth.Morse.pullback ψ g
          (q.1 + (k : ℝ) * (2 * Real.pi), q.2 + (l : ℝ) * (2 * Real.pi)) ∈ Set.Icc a b := by
        rw [pullback_add_lattice ψ g q k l]
        exact hq
      have hq'K : (q.1 + (k : ℝ) * (2 * Real.pi), q.2 + (l : ℝ) * (2 * Real.pi)) ∈ K := by
        rw [hK, hB]
        exact ⟨hq'B, hk, hl⟩
      have h1 : Work.Smooth.Morse.descentRate ψ g q₀ ≤ Work.Smooth.Morse.descentRate ψ g
          (q.1 + (k : ℝ) * (2 * Real.pi), q.2 + (l : ℝ) * (2 * Real.pi)) := hmin hq'K
      rwa [descentRate_add_lattice ψ g q k l] at h1
  · -- The band misses the fundamental square, hence it is empty: the statement is vacuous.
    refine ⟨1, one_pos, fun q hq => ?_⟩
    exfalso
    apply hne
    obtain ⟨k, hk⟩ := exists_int_shift_mem_Icc q.1
    obtain ⟨l, hl⟩ := exists_int_shift_mem_Icc q.2
    refine ⟨(q.1 + (k : ℝ) * (2 * Real.pi), q.2 + (l : ℝ) * (2 * Real.pi)), ?_⟩
    rw [hK, hB]
    refine ⟨?_, hk, hl⟩
    show Work.Smooth.Morse.pullback ψ g
      (q.1 + (k : ℝ) * (2 * Real.pi), q.2 + (l : ℝ) * (2 * Real.pi)) ∈ Set.Icc a b
    rw [pullback_add_lattice ψ g q k l]
    exact hq

end

end Work.Smooth.Morse.Flow
