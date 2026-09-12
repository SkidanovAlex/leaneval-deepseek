import Mathlib

/-!
# Good times for a nonnegative energy: the abstract time-selection step

This module isolates the *abstract* content of the "time selection" step of de Saxcé's §3:
the energy `t ↦ Σᵢ (Δc_t(i))²` is nonnegative, and `⟨ċ_t, c_t⟩` is half its derivative, so
there are arbitrarily large `t` with `⟨ċ_t, c_t⟩ ≥ −1`; otherwise the energy decreases at
rate `≥ 1` forever, contradicting nonnegativity.

The point of the abstract formulation is that **no differentiability assumption on the
energy is needed**.  We only use that the energy is continuous and nonnegative; the conclusion
is the *local right-slope* form `HasLocalSlopeGe E t c`:

  `∃ ε > 0, ∀ s ∈ [t, t+ε], E s ≥ E t − c (s − t)`,

which is what the downstream argument consumes: at such a `t`, combined with the *local
affine structure* of the polygon (which the flow provides through the max-norm data, see
`Submission.Work.Lattice.MaxNormFlow`), one obtains a bound on the weighted slope sum.

The existence statement is proved by considering `F := E + c·id`: since `F` is continuous and
grows at least linearly, `F` has arbitrarily large points of *right-local minimum*
(`exists_rightLocalMin_of_le`); at such a point the local right-slope of `E` is `≥ −c`.

All declarations are Mathlib-only and sorry-free.
Module `Submission.Work.Lattice.GoodTime`, namespace `Submission.GoodTime`.
-/

noncomputable section

open Set
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Submission.GoodTime

/-- **`HasLocalSlopeGe E t c`**: the function `E` does not decrease faster than slope `c` to
the right of `t`, on a one-sided neighbourhood of `t`. -/
def HasLocalSlopeGe (E : ℝ → ℝ) (t c : ℝ) : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Set.Icc t (t + ε), E t - c * (s - t) ≤ E s

/-- **Right-local minima of a continuous function growing at least linearly.**

If `F` is continuous on `ℝ` and `c·t ≤ F t` everywhere for some `c > 0` (in particular
`F t → +∞`), then for every `A` there is `t ≥ A` which is a *right-local minimum* of `F`:
`F t ≤ F s` for all `s ∈ [t, t+ε]`, for some `ε > 0`. -/
theorem exists_rightLocalMin_of_le (F : ℝ → ℝ) (hcont : Continuous F) {c : ℝ} (hc : 0 < c)
    (hF : ∀ t : ℝ, c * t ≤ F t) (A : ℝ) :
    ∃ t : ℝ, A ≤ t ∧ ∃ ε : ℝ, 0 < ε ∧ ∀ s ∈ Set.Icc t (t + ε), F t ≤ F s := by
  classical
  set N : ℕ := Nat.ceil (max A 0) with hN
  have hNA : A ≤ (N : ℝ) := le_trans (le_max_left A 0) (Nat.le_ceil _)
  by_contra hcon
  push Not at hcon
  -- `hcon : ∀ t, A ≤ t → ∀ ε > 0, ∃ s ∈ Icc t (t+ε), F s < F t`
  have hmin : ∀ n : ℕ, ∃ x : ℝ, x ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1) ∧
      ∀ y ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1), F x ≤ F y := by
    intro n
    have hne : (Set.Icc (n : ℝ) ((n : ℝ) + 1)).Nonempty :=
      ⟨(n : ℝ), le_refl _, by linarith⟩
    exact isCompact_Icc.exists_isMinOn hne hcont.continuousOn
  choose x hxmem hxmin using hmin
  -- the minimiser is the right endpoint
  have hxend : ∀ n : ℕ, N ≤ n → x n = (n : ℝ) + 1 := by
    intro n hn
    rcases lt_or_eq_of_le (hxmem n).2 with hlt | heq
    · exfalso
      have hAx : A ≤ x n := le_trans hNA (le_trans (by exact_mod_cast hn) (hxmem n).1)
      obtain ⟨s, hs, hxs⟩ := hcon (x n) hAx (((n : ℝ) + 1 - x n) / 2) (by linarith)
      have hs1 : (n : ℝ) ≤ s := le_trans (hxmem n).1 hs.1
      have hs2 : s ≤ (n : ℝ) + 1 := by linarith [hs.2]
      have := hxmin n s ⟨hs1, hs2⟩
      linarith
    · exact heq
  -- hence `F` is non-increasing along the integers from `N` on
  have hdec : ∀ m : ℕ, F ((N : ℝ) + m) ≤ F (N : ℝ) := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
        have hstep : F (((N + k : ℕ) : ℝ) + 1) ≤ F ((N + k : ℕ) : ℝ) := by
          have h1 := hxmin (N + k) ((N + k : ℕ) : ℝ) ⟨le_refl _, by linarith⟩
          rwa [hxend (N + k) (Nat.le_add_right N k)] at h1
        have e1 : (((N + k : ℕ) : ℝ) + 1) = (N : ℝ) + (k : ℝ) + 1 := by push_cast; ring
        have e2 : (((N + k : ℕ) : ℝ)) = (N : ℝ) + (k : ℝ) := by push_cast; ring
        have e3 : ((N : ℝ) + ((k + 1 : ℕ) : ℝ)) = (N : ℝ) + (k : ℝ) + 1 := by push_cast; ring
        rw [e1, e2] at hstep
        rw [e3]
        exact le_trans hstep ih
  -- but `F` grows at least linearly
  obtain ⟨m, hm⟩ := exists_nat_gt (max (F (N : ℝ)) 0 / c)
  have hmc : F (N : ℝ) < c * (m : ℝ) := by
    have h1 : max (F (N : ℝ)) 0 / c < (m : ℝ) := hm
    have h2 : max (F (N : ℝ)) 0 < c * (m : ℝ) := by
      have h3 : c * (max (F (N : ℝ)) 0 / c) < c * (m : ℝ) :=
        mul_lt_mul_of_pos_left h1 hc
      rw [mul_div_cancel₀ _ (ne_of_gt hc)] at h3
      exact h3
    exact lt_of_le_of_lt (le_max_left _ _) h2
  have h1 := hdec m
  have h2 : c * ((N : ℝ) + (m : ℝ)) ≤ F ((N : ℝ) + m) := hF _
  have hcm : c * (m : ℝ) ≤ c * ((N : ℝ) + (m : ℝ)) := by
    have : (0 : ℝ) ≤ (N : ℝ) := by positivity
    nlinarith
  linarith

/-- **The good time.**  If `E` is continuous and nonnegative on `ℝ` and `c > 0`, then for
every `A` there is `t ≥ A` with `HasLocalSlopeGe E t c`. -/
theorem exists_hasLocalSlopeGe_of_nonneg (E : ℝ → ℝ) (hcont : Continuous E)
    (hE : ∀ t : ℝ, 0 ≤ E t) {c : ℝ} (hc : 0 < c) (A : ℝ) :
    ∃ t : ℝ, A ≤ t ∧ HasLocalSlopeGe E t c := by
  have hF : ∀ t : ℝ, c * t ≤ E t + c * t := fun t => by linarith [hE t]
  obtain ⟨t, htA, ε, hε, hloc⟩ :=
    exists_rightLocalMin_of_le (fun t => E t + c * t) (hcont.add (continuous_id.const_mul c))
      hc hF A
  refine ⟨t, htA, ε, hε, fun s hs => ?_⟩
  have h := hloc s hs
  linarith

/-- **Half-line form.**  If `E` is continuous on `[0,∞)` and nonnegative there, then for every
`A ≥ 0` there is `t ≥ A` with `HasLocalSlopeGe E t c`.  (Extend `E` to `ℝ` by constancy on
`(−∞,0]` and apply the full-line statement.) -/
theorem exists_hasLocalSlopeGe_of_nonneg_Ici (E : ℝ → ℝ) (hcont : ContinuousOn E (Set.Ici 0))
    (hE : ∀ t : ℝ, 0 ≤ t → 0 ≤ E t) {c : ℝ} (hc : 0 < c) {A : ℝ} (hA : 0 ≤ A) :
    ∃ t : ℝ, A ≤ t ∧ HasLocalSlopeGe E t c := by
  set E' : ℝ → ℝ := fun t => E (max t 0) with hE'
  have hcontmax : Continuous fun t : ℝ => max t 0 := continuous_id.max continuous_const
  have hcont' : Continuous E' := by
    have h := hcont.comp_continuous hcontmax (fun t => le_max_right t 0)
    simpa [hE', Function.comp_def] using h
  have hE'0 : ∀ t : ℝ, 0 ≤ E' t := fun t => hE _ (le_max_right t 0)
  obtain ⟨t, htA, h⟩ := exists_hasLocalSlopeGe_of_nonneg E' hcont' hE'0 hc A
  refine ⟨t, htA, ?_⟩
  obtain ⟨ε, hε, hloc⟩ := h
  refine ⟨ε, hε, fun s hs => ?_⟩
  have ht0 : 0 ≤ t := le_trans hA htA
  have hs0 : 0 ≤ s := le_trans ht0 hs.1
  have h1 : E' s = E s := by simp [hE', max_eq_left hs0]
  have h2 : E' t = E t := by simp [hE', max_eq_left ht0]
  have := hloc s hs
  rwa [h1, h2] at this

/-! ## The energy of a family of slopes -/

/-- The energy `∑ᵢ (Λ t i)²` of a time-dependent family of slopes. -/
def energy {d : ℕ} (Λ : ℝ → Fin d → ℝ) (t : ℝ) : ℝ := ∑ i, (Λ t i) ^ 2

lemma energy_nonneg {d : ℕ} (Λ : ℝ → Fin d → ℝ) (t : ℝ) : 0 ≤ energy Λ t :=
  Finset.sum_nonneg fun i _ => sq_nonneg (Λ t i)

lemma energy_continuous {d : ℕ} (Λ : ℝ → Fin d → ℝ) (hΛ : ∀ i, Continuous fun t => Λ t i) :
    Continuous (energy Λ) :=
  continuous_finsetSum _ fun i _ => (hΛ i).pow 2

/-- The exact expansion of the energy difference for a locally affine family. -/
lemma energy_sub_eq {d : ℕ} (Λ : ℝ → Fin d → ℝ) {t ε s : ℝ} (hs : s ∈ Set.Icc t (t + ε))
    (r : Fin d → ℝ) (haff : ∀ u ∈ Set.Icc t (t + ε), ∀ i : Fin d, Λ u i = Λ t i + (u - t) * r i) :
    energy Λ s - energy Λ t =
      (s - t) * (2 * ∑ i, Λ t i * r i) + (s - t) ^ 2 * ∑ i, (r i) ^ 2 := by
  simp only [energy]
  rw [← Finset.sum_sub_distrib]
  have hterm : ∀ i : Fin d,
      (Λ s i) ^ 2 - (Λ t i) ^ 2 =
        ((s - t) * (2 * (Λ t i * r i)) + (s - t) ^ 2 * (r i) ^ 2) := by
    intro i
    rw [haff s hs i]
    ring
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  rw [Finset.sum_add_distrib]
  congr 1
  · rw [← Finset.mul_sum]
    congr 1
    rw [← Finset.mul_sum]
  · rw [← Finset.mul_sum]

/-- **Local affine structure gives a local right-slope bound for the energy.** -/
theorem hasLocalSlopeGe_energy_of_affine {d : ℕ} (Λ : ℝ → Fin d → ℝ) {t ε : ℝ}
    (hε : 0 < ε) (r : Fin d → ℝ)
    (haff : ∀ s ∈ Set.Icc t (t + ε), ∀ i : Fin d, Λ s i = Λ t i + (s - t) * r i) :
    HasLocalSlopeGe (energy Λ) t (-(2 * ∑ i, Λ t i * r i)) := by
  refine ⟨ε, hε, fun s hs => ?_⟩
  have hexp := energy_sub_eq Λ hs r haff
  have hsq : 0 ≤ (s - t) ^ 2 * ∑ i, (r i) ^ 2 :=
    mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
  linarith

/-- **The conclusion consumed downstream.**  At a good time (in the sense
`HasLocalSlopeGe (energy Λ) t 2`), if the slopes are locally affine with local slopes `r`,
then the weighted sum `∑ i, Λ t i * r i` is bounded below by `−3/2`.

The numeric constant is not optimal; it only has to be uniform, and it is: the argument takes
the step small enough that the quadratic remainder `(s−t)·∑ᵢrᵢ²` is at most `1`. -/
theorem sum_mul_ge_of_good_of_affine {d : ℕ} (Λ : ℝ → Fin d → ℝ) {t ε : ℝ}
    (hε : 0 < ε) (r : Fin d → ℝ)
    (haff : ∀ s ∈ Set.Icc t (t + ε), ∀ i : Fin d, Λ s i = Λ t i + (s - t) * r i)
    (hgood : HasLocalSlopeGe (energy Λ) t 2) :
    -(3 / 2) ≤ ∑ i, Λ t i * r i := by
  obtain ⟨ε', hε'pos, hloc⟩ := hgood
  set D : ℝ := ∑ i, (r i) ^ 2 with hD
  have hD0 : 0 ≤ D := by rw [hD]; exact Finset.sum_nonneg fun i _ => sq_nonneg _
  set δ : ℝ := min (min ε ε') (1 / (D + 1)) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min hε hε'pos) (by positivity)
  have hδε : δ ≤ ε := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδε' : δ ≤ ε' := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_right _ _)
  -- instantaneous form: `2 ∑ + δ·D ≥ −2`
  have hinst : -2 ≤ 2 * ∑ i, Λ t i * r i + δ * D := by
    have hst1 : t + δ / 2 ∈ Set.Icc t (t + ε) := ⟨by linarith, by linarith⟩
    have hst2 : t + δ / 2 ∈ Set.Icc t (t + ε') := ⟨by linarith, by linarith⟩
    have hexp := energy_sub_eq Λ hst1 r haff
    have hlow := hloc (t + δ / 2) hst2
    have hsum : ∑ i, (r i) ^ 2 = D := rfl
    rw [hsum] at hexp
    have hs : (0 : ℝ) < δ / 2 := by linarith
    have hsub : t + δ / 2 - t = δ / 2 := by ring
    rw [hsub] at hexp
    have key : 2 * ∑ i, Λ t i * r i + δ / 2 * D ≥ -2 := by nlinarith [hexp, hlow, hs]
    have hmono : δ / 2 * D ≤ δ * D := by nlinarith [hD0, hδpos]
    linarith
  -- `δ · D ≤ 1`
  have hkey : δ * D ≤ 1 := by
    by_cases hDz : D = 0
    · rw [hDz, mul_zero]; norm_num
    · have hDpos : 0 < D := lt_of_le_of_ne hD0 (Ne.symm hDz)
      have hle : δ ≤ 1 / D := by
        rw [hδdef]
        refine le_trans (min_le_right _ _) ?_
        exact one_div_le_one_div_of_le hDpos (by linarith)
      have := mul_le_mul_of_nonneg_right hle hD0
      rwa [div_mul_cancel₀ _ (ne_of_gt hDpos)] at this
  linarith

end Submission.GoodTime
