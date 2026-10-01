import Mathlib
import Submission.Commons.Analysis.ExponentialSums.second_derivative_test
import Submission.Commons.Analysis.Integral.interval_integral_between_consts

open Complex Filter MeasureTheory
open scoped Real BigOperators Topology Filter Interval
set_option autoImplicit false
set_option maxHeartbeats 0

namespace Commons.Analysis.ExponentialSums

/-! # Correlation (per-shift) bound for the van der Corput third derivative test

Let `f` be `C³` on `[a, a+M]` with two-sided third-derivative control
`l ≤ f''' ≤ α·l` on the open interval `(a, a+M)`.  For a shift `t : ℕ` with
`1 ≤ t < M` we bound the *correlation sum* over a single window

    C_t := Σ_{a < n ≤ a + (M−t)} e(2πi·(f(n+t) − f(n)))

by applying the second-derivative test to the differenced phase
`g(x) := f(x + t) − f(x)`, whose second derivative is
`g''(x) = f''(x+t) − f''(x) = ∫_x^{x+t} f'''` and therefore lies between
`t·l` and `t·(α·l)`:

    |C_t| ≤ C(α)·( (M−t)·√(t·l) + 1/√(t·l) )

with `C(α) > 0` depending only on `α` (uniform in `a, M, f, t, l`).

The support lemmas below (`corr_*`) are the real-analysis content: the value
identity for the second derivative of a shifted finite difference, the FTC
identity `f''(y+h) − f''(y) = ∫_y^{y+h} f'''`, the integral sandwich on a
closed interval, and the two-sided `g''`-control they combine into.
-/

noncomputable section

/-- First-derivative identity for a shifted finite difference: when `f` is
differentiable at both `x` and `x + h`, one has
`deriv (fun t ↦ f (t+h) − f t) x = deriv f (x+h) − deriv f x`. -/
private lemma corr_deriv_add_const_sub (f : ℝ → ℝ) {h x : ℝ}
    (hdxh : DifferentiableAt ℝ f (x + h)) (hdx : DifferentiableAt ℝ f x) :
    deriv (fun t : ℝ => f (t + h) - f t) x = deriv f (x + h) - deriv f x := by
  have hA : HasDerivAt (fun t : ℝ => f (t + h)) (deriv f (x + h)) x :=
    (hdxh.hasDerivAt).comp_add_const x h
  have hB : HasDerivAt f (deriv f x) x := hdx.hasDerivAt
  exact (hA.sub hB).deriv

/-- **Value identity** (second-derivative level): for `f` of class `C³` on the
open interval `(a,b)` containing `y` and `y+h`,
`deriv (deriv (fun x ↦ f (x+h) − f x)) y = f''(y+h) − f''(y)`. -/
private lemma corr_diff_second_deriv_value {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContDiffOn ℝ 3 f (Set.Ioo a b)) {y h : ℝ}
    (hy : y ∈ Set.Ioo a b) (hyh : y + h ∈ Set.Ioo a b) :
    deriv (deriv (fun x : ℝ => f (x + h) - f x)) y =
      deriv (deriv f) (y + h) - deriv (deriv f) y := by
  let S : Set ℝ := Set.Ioo a b
  let g : ℝ → ℝ := fun x : ℝ => f (x + h) - f x
  let k : ℝ → ℝ := fun x : ℝ => deriv f (x + h) - deriv f x
  have hSopen : IsOpen S := by
    dsimp [S]
    exact isOpen_Ioo
  -- `f` is differentiable on `S` (first level) and `deriv f` is differentiable
  -- on `S` (second level), both consequences of the `C³` hypothesis on the open set.
  have hdiff_f : DifferentiableOn ℝ f S := by
    exact ContDiffOn.differentiableOn hf (by norm_num)
  have hdf1 : ContDiffOn ℝ 2 (deriv f) S := by
    exact ContDiffOn.deriv_of_isOpen hf hSopen (by norm_num)
  have hdiff_df : DifferentiableOn ℝ (deriv f) S := by
    exact ContDiffOn.differentiableOn hdf1 (by norm_num)
  have hdy2 : DifferentiableAt ℝ (deriv f) y :=
    hdiff_df.differentiableAt (IsOpen.mem_nhds hSopen hy)
  have hdyh2 : DifferentiableAt ℝ (deriv f) (y + h) :=
    hdiff_df.differentiableAt (IsOpen.mem_nhds hSopen hyh)
  -- differentiate `x ↦ deriv f (x + h) − deriv f x` at `y`
  have hA : HasDerivAt (fun x : ℝ => deriv f (x + h)) (deriv (deriv f) (y + h)) y :=
    (hdyh2.hasDerivAt).comp_add_const y h
  have hB : HasDerivAt (deriv f) (deriv (deriv f) y) y := hdy2.hasDerivAt
  have hk : HasDerivAt k (deriv (deriv f) (y + h) - deriv (deriv f) y) y := by
    exact hA.sub hB
  -- the first-level identity holds pointwise for `x` close to `y` (both `x`
  -- and `x + h` stay in the open interval `S`)
  have hpre : (fun x : ℝ => x + h) ⁻¹' S ∈ 𝓝 y := by
    apply ContinuousAt.preimage_mem_nhds
    · exact continuousAt_id.add continuousAt_const
    · exact IsOpen.mem_nhds hSopen hyh
  have hdgk : (deriv g) =ᶠ[𝓝 y] k := by
    filter_upwards [IsOpen.mem_nhds hSopen hy, hpre] with x hxS hxS_h
    have hdx : DifferentiableAt ℝ f x :=
      hdiff_f.differentiableAt (IsOpen.mem_nhds hSopen hxS)
    have hdxh : DifferentiableAt ℝ f (x + h) :=
      hdiff_f.differentiableAt (IsOpen.mem_nhds hSopen hxS_h)
    simpa [g, k] using corr_deriv_add_const_sub f hdxh hdx
  calc
    deriv (deriv g) y = deriv k y := hdgk.deriv_eq
    _ = deriv (deriv f) (y + h) - deriv (deriv f) y := hk.deriv

/-- **FTC identity**: `f''(y+h) − f''(y) = ∫_y^{y+h} f'''` for `f` of class
`C³` on the open interval `(a,b)` containing `y, y+h`, with `0 ≤ h`. -/
private lemma corr_ftc_third_deriv {f : ℝ → ℝ} {a b : ℝ}
    (hf : ContDiffOn ℝ 3 f (Set.Ioo a b)) {y h : ℝ}
    (hy : y ∈ Set.Ioo a b) (hyh : y + h ∈ Set.Ioo a b) (hh : 0 ≤ h) :
    (∫ x in y..(y + h), deriv (deriv (deriv f)) x) =
      deriv (deriv f) (y + h) - deriv (deriv f) y := by
  let S : Set ℝ := Set.Ioo a b
  have hSopen : IsOpen S := by
    dsimp [S]
    exact isOpen_Ioo
  have hdf1 : ContDiffOn ℝ 2 (deriv f) S := by
    exact ContDiffOn.deriv_of_isOpen hf hSopen (by norm_num)
  have hdd1 : ContDiffOn ℝ 1 (deriv (deriv f)) S := by
    exact ContDiffOn.deriv_of_isOpen hdf1 hSopen (by norm_num)
  have hyyh : y ≤ y + h := by linarith
  -- `[y, y+h] ⊆ (a,b)`: `a < y ≤ x` and `x ≤ y+h < b`
  have hsub : Set.Icc y (y + h) ⊆ S := by
    intro x hx
    rw [Set.mem_Icc] at hx
    dsimp [S]
    constructor
    · exact lt_of_lt_of_le hy.1 hx.1
    · exact lt_of_le_of_lt hx.2 hyh.2
  have hcont : ContDiffOn ℝ 1 (deriv (deriv f)) (Set.Icc y (y + h)) := hdd1.mono hsub
  exact intervalIntegral.integral_deriv_of_contDiffOn_Icc hcont hyyh

/-- **Integral sandwich on a closed interval** (`u ≤ v`): pointwise
`c ≤ g ≤ d` on `[u, v]` implies `c·(v−u) ≤ ∫_u^v g ≤ d·(v−u)`. -/
private lemma corr_integral_between_consts_Icc {g : ℝ → ℝ} {c d u v : ℝ} (huv : u ≤ v)
    (hg : ∀ x : ℝ, x ∈ Set.Icc u v → c ≤ g x ∧ g x ≤ d)
    (hgi : IntervalIntegrable g MeasureTheory.volume u v) :
    c * (v - u) ≤ ∫ x in u..v, g x ∧ ∫ x in u..v, g x ≤ d * (v - u) := by
  constructor
  · have hlow : (∫ x in u..v, c) ≤ (∫ x in u..v, g x) := by
      refine intervalIntegral.integral_mono_on huv ?_ hgi ?_
      · exact ContinuousOn.intervalIntegrable_of_Icc huv continuousOn_const
      · intro x hx
        exact (hg x hx).1
    rw [intervalIntegral.integral_const, smul_eq_mul] at hlow
    have hmul : c * (v - u) = (v - u) * c := by ring
    rw [hmul]
    exact hlow
  · have hup : (∫ x in u..v, g x) ≤ (∫ x in u..v, d) := by
      refine intervalIntegral.integral_mono_on huv hgi ?_ ?_
      · exact ContinuousOn.intervalIntegrable_of_Icc huv continuousOn_const
      · intro x hx
        exact (hg x hx).2
    rw [intervalIntegral.integral_const, smul_eq_mul] at hup
    have hmul : (v - u) * d = d * (v - u) := by ring
    rw [← hmul]
    exact hup

/-- **Two-sided second-derivative control of the differenced phase.**  For `f`
`C³` on the open interval `(a, b)` with `λ ≤ f''' ≤ α·λ` pointwise and
`y, y + h ∈ (a, b)`, `h ≥ 0`:

    h·λ ≤ deriv (deriv (fun x => f (x + h) − f x)) y ≤ h·(α·λ). -/
theorem corr_diff_phase_two_sided {f : ℝ → ℝ} {α l : ℝ} (hα : 1 ≤ α) (hl0 : 0 < l)
    {a b : ℝ} (hf : ContDiffOn ℝ 3 f (Set.Ioo a b))
    (hppp : ∀ x : ℝ, x ∈ Set.Ioo a b →
      l ≤ deriv (deriv (deriv f)) x ∧ deriv (deriv (deriv f)) x ≤ α * l)
    {y h : ℝ} (hy : y ∈ Set.Ioo a b) (hyh : y + h ∈ Set.Ioo a b) (hh : 0 ≤ h) :
    h * l ≤ deriv (deriv (fun x : ℝ => f (x + h) - f x)) y ∧
      deriv (deriv (fun x : ℝ => f (x + h) - f x)) y ≤ h * (α * l) := by
  let S : Set ℝ := Set.Ioo a b
  let g : ℝ → ℝ := fun x : ℝ => f (x + h) - f x
  have hSopen : IsOpen S := by
    dsimp [S]
    exact isOpen_Ioo
  have hyyh : y ≤ y + h := by linarith
  have hsub : Set.Icc y (y + h) ⊆ S := by
    intro x hx
    rw [Set.mem_Icc] at hx
    dsimp [S]
    constructor
    · exact lt_of_lt_of_le hy.1 hx.1
    · exact lt_of_le_of_lt hx.2 hyh.2
  -- `f'''` is continuous on the interval `[y, y+h]`, hence integrable there
  have hdf1 : ContDiffOn ℝ 2 (deriv f) S := by
    exact ContDiffOn.deriv_of_isOpen hf hSopen (by norm_num)
  have hdd1 : ContDiffOn ℝ 1 (deriv (deriv f)) S := by
    exact ContDiffOn.deriv_of_isOpen hdf1 hSopen (by norm_num)
  have hcont3 : ContinuousOn (deriv (deriv (deriv f))) S := by
    exact ContDiffOn.continuousOn_deriv_of_isOpen hdd1 hSopen le_rfl
  have hcont3I : ContinuousOn (deriv (deriv (deriv f))) (Set.Icc y (y + h)) := hcont3.mono hsub
  have hgi : IntervalIntegrable (deriv (deriv (deriv f))) MeasureTheory.volume y (y + h) := by
    exact hcont3I.intervalIntegrable_of_Icc hyyh
  -- the two-sided third-derivative control transfers from `(a,b)` to `[y, y+h]`
  have hb : ∀ x : ℝ, x ∈ Set.Icc y (y + h) →
      l ≤ deriv (deriv (deriv f)) x ∧ deriv (deriv (deriv f)) x ≤ α * l := by
    intro x hx
    exact hppp x (hsub hx)
  -- sandwich the integral:  l*h ≤ ∫_y^{y+h} f''' ≤ (α*l)*h
  have hsand := corr_integral_between_consts_Icc (g := deriv (deriv (deriv f))) (c := l)
    (d := α * l) hyyh hb hgi
  -- FTC:  ∫_y^{y+h} f''' = f''(y+h) − f''(y)
  have hFTC : (∫ x in y..(y + h), deriv (deriv (deriv f)) x) =
      deriv (deriv f) (y + h) - deriv (deriv f) y :=
    corr_ftc_third_deriv hf hy hyh hh
  -- value identity:  deriv (deriv g) y = f''(y+h) − f''(y)
  have hval : deriv (deriv g) y = deriv (deriv f) (y + h) - deriv (deriv f) y := by
    simpa [g] using corr_diff_second_deriv_value hf hy hyh
  constructor
  · have hlo := hsand.1
    rw [hFTC] at hlo
    have hsub2 : (y + h) - y = h := by ring
    rw [hsub2] at hlo
    rw [hval]
    nlinarith
  · have hup := hsand.2
    rw [hFTC] at hup
    have hsub2 : (y + h) - y = h := by ring
    rw [hsub2] at hup
    rw [hval]
    nlinarith

/-- **Correlation (per-shift) bound.**  For `f` `C³` on `[a, a+M]` with the
two-sided control `l ≤ f''' ≤ α·l` on the open `(a, a+M)`, and a shift
`t : ℕ` with `1 ≤ t < M`:

    |Σ_{a<n≤a+(M−t)} e(2πi·(f(n+t) − f(n)))| ≤ C(α)·( (M−t)·√(t·l) + 1/√(t·l) )

with `C(α) > 0` depending only on `α`. -/
theorem correlation_shift_bound {α : ℝ} (hα : 1 ≤ α) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {a : ℤ} {M : ℕ} (_hM : 1 ≤ M) (f : ℝ → ℝ) {l : ℝ} (_hl : 0 < l)
        (_hf : ContDiffOn ℝ 3 f (Set.Icc (a : ℝ) ((a : ℝ) + (M : ℝ))))
        (_hppp : ∀ x : ℝ, x ∈ Set.Ioo (a : ℝ) ((a : ℝ) + (M : ℝ)) →
          l ≤ deriv (deriv (deriv f)) x ∧ deriv (deriv (deriv f)) x ≤ α * l)
        (t : ℕ) (ht1 : 1 ≤ t) (htM : t < M),
        ‖∑ n ∈ Finset.Icc (a + 1) (a + ((M - t : ℕ) : ℤ)),
            Complex.exp (((2 * Real.pi * (f ((n : ℝ) + (t : ℝ)) - f (n : ℝ)) : ℝ) : ℂ) * Complex.I)‖
          ≤ C * ((((M - t : ℕ) : ℝ) * Real.sqrt ((t : ℝ) * l)) +
              (Real.sqrt ((t : ℝ) * l))⁻¹) := by
  obtain ⟨C₂, hC₂pos, hC₂⟩ := second_derivative_test (B := α) hα
  refine ⟨C₂, hC₂pos, ?_⟩
  intro a M hM f l hl hf hppp t ht1 htM
  let N : ℕ := M - t
  let g : ℝ → ℝ := fun x : ℝ => f (x + (t : ℝ)) - f x
  let r : ℝ := (t : ℝ) * l
  have hN1 : 1 ≤ N := by
    dsimp [N]
    omega
  have htR : 0 < (t : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le zero_lt_one ht1)
  have htR0 : 0 ≤ (t : ℝ) := le_of_lt htR
  have hr : 0 < r := by
    dsimp [r]
    exact mul_pos htR hl
  -- the short window `[a, a+N]` and its `t`-translate `[a+t, a+N+t]` both lie
  -- inside the `C³`-domain `[a, a+M]` (since `N + t = M`)
  have hNM : (N : ℝ) ≤ (M : ℝ) := by
    dsimp [N]
    exact_mod_cast Nat.sub_le M t
  have hsub_nat : (N : ℝ) + (t : ℝ) = (M : ℝ) := by
    dsimp [N]
    rw [Nat.cast_sub (le_of_lt htM)]
    ring
  -- `f` is `C³` on the open ambient `(a, a+M)` (restriction of `hf`)
  have hFopen : ContDiffOn ℝ 3 f (Set.Ioo (a : ℝ) ((a : ℝ) + (M : ℝ))) := by
    refine hf.mono ?_
    intro x hx
    rw [Set.mem_Ioo] at hx
    rw [Set.mem_Icc]
    exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  -- `g` is `C²` on the real window `[a, a+N]`: both pieces `x ↦ f x` and
  -- `x ↦ f (x + t)` land in the `C³`-domain `[a, a+M]`.
  have hg2 : ContDiffOn ℝ 2 g (Set.Icc (a : ℝ) ((a : ℝ) + (N : ℝ))) := by
    let W : Set ℝ := Set.Icc (a : ℝ) ((a : ℝ) + (M : ℝ))
    have hWsub : Set.Icc (a : ℝ) ((a : ℝ) + (N : ℝ)) ⊆ W := by
      intro x hx
      rw [Set.mem_Icc] at hx ⊢
      constructor
      · exact hx.1
      · linarith [hNM]
    have hf2 : ContDiffOn ℝ 2 f (Set.Icc (a : ℝ) ((a : ℝ) + (N : ℝ))) :=
      (ContDiffOn.of_le hf (by norm_num)).mono hWsub
    let T : ℝ → ℝ := fun x : ℝ => x + (t : ℝ)
    have hT : ContDiffOn ℝ 3 T (Set.Icc (a : ℝ) ((a : ℝ) + (N : ℝ))) := by
      have h : ContDiff ℝ 3 (fun x : ℝ => x + (t : ℝ)) := by
        simpa using (ContDiff.add contDiff_id contDiff_const (𝕜 := ℝ) (n := (3 : ℕ∞)))
      exact h.contDiffOn
    have hTmap : Set.MapsTo T (Set.Icc (a : ℝ) ((a : ℝ) + (N : ℝ))) W := by
      intro x hx
      rw [Set.mem_Icc] at hx ⊢
      dsimp [T]
      constructor <;> linarith [hsub_nat, htR0]
    have hfT : ContDiffOn ℝ 3 (f ∘ T) (Set.Icc (a : ℝ) ((a : ℝ) + (N : ℝ))) :=
      ContDiffOn.comp hf hT hTmap
    have hfT2 : ContDiffOn ℝ 2 (f ∘ T) (Set.Icc (a : ℝ) ((a : ℝ) + (N : ℝ))) :=
      ContDiffOn.of_le hfT (by norm_num)
    have hsub : ContDiffOn ℝ 2 (fun x : ℝ => f (T x) - f x)
        (Set.Icc (a : ℝ) ((a : ℝ) + (N : ℝ))) :=
      ContDiffOn.sub hfT2 hf2
    simpa [g, T, Function.comp_def] using hsub
  -- two-sided second-derivative control of `g` on the *open* window
  -- `(a, a+N)`: apply `corr_diff_phase_two_sided` with ambient `(a, a+M)`,
  -- using that both `x` and `x + t` are strictly interior points of `(a, a+M)`.
  have hpp : ∀ x : ℝ, x ∈ Set.Ioo (a : ℝ) ((a : ℝ) + (N : ℝ)) →
      r ≤ deriv (deriv g) x ∧ deriv (deriv g) x ≤ α * r := by
    intro x hx
    rw [Set.mem_Ioo] at hx
    have hy : x ∈ Set.Ioo (a : ℝ) ((a : ℝ) + (M : ℝ)) := by
      rw [Set.mem_Ioo]
      constructor
      · exact hx.1
      · linarith [hNM]
    have hyh : x + (t : ℝ) ∈ Set.Ioo (a : ℝ) ((a : ℝ) + (M : ℝ)) := by
      rw [Set.mem_Ioo]
      constructor
      · linarith
      · linarith [hsub_nat]
    have htwo := corr_diff_phase_two_sided (f := f) (α := α) (l := l) hα hl
      (a := (a : ℝ)) (b := (a : ℝ) + (M : ℝ)) hFopen hppp
      (y := x) (h := (t : ℝ)) hy hyh htR0
    dsimp [g, r]
    constructor
    · simpa using htwo.1
    · simpa [mul_assoc, mul_left_comm, mul_comm] using htwo.2
  -- the second-derivative test on `g` (ratio `α`, second-derivative bound
  -- `(t:ℝ)·l = r`) returns exactly the required bound on the per-shift sum.
  have hres := hC₂ (a := a) (N := N) hN1 g (r := r) hr hg2 hpp
  simpa [g, r, N] using hres

end

end Commons.Analysis.ExponentialSums
