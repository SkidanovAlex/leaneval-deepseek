import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Submission.CubicChi
import Submission.Work.BoseB7AK.Q2Gram.torus_lift
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7AK.Q2Gram.Defs` — the objects of the `χ²` Fourier-sum computation

This module sets up the objects used in `Work.BoseB7AK.Q2Gram.chiSq_fourier_sum`:

* `gE`/`g1` — the function `χ(x)²`, seen as a complex-valued function on `ℝ³` respectively on the
  coordinate space `Fin 3 → ℝ`;
* `kv`/`lat` — a lattice vector `n : Fin 3 → ℤ` as a point of `Fin 3 → ℝ` respectively of `ℝ³`;
* `F` — its **periodization** `F y = ∑'_n χ(y+n)²`;
* `P` — the induced continuous function on the unit torus `𝕋³ = (ℝ/ℤ)³`
  (`P ∘ q = F`, from `torus_lift`).

The lemmas proved here are the elementary properties used downstream:
`chi` vanishes at distance `≥ 1/2` from the origin, the periodization is summable / continuous /
`ℤ³`-periodic, `F 0 = χ(0)²`, and on the unit cube `(-1/2,1/2]³` the periodization reduces to `χ²`
(only the `n = 0` translate survives).
-/

noncomputable section

open MeasureTheory Complex Filter Topology
open scoped BigOperators

namespace Work.BoseB7AK.Q2Gram

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- A lattice vector `n : Fin 3 → ℤ` as a point of the coordinate space `Fin 3 → ℝ`. -/
def kv (n : Fin 3 → ℤ) : Fin 3 → ℝ := fun i => (n i : ℝ)

/-- A lattice vector `n : Fin 3 → ℤ` as a point of `ℝ³`. -/
def lat (n : Fin 3 → ℤ) : E3 := WithLp.toLp 2 (kv n)

/-- `χ(x)²` as a complex-valued function on `ℝ³`. -/
def gE (x : E3) : ℂ := Complex.ofReal ((Submission.BoseGases.chi x) ^ 2)

/-- `χ(x)²` as a complex-valued function on `Fin 3 → ℝ`. -/
def g1 (y : Fin 3 → ℝ) : ℂ := gE (WithLp.toLp 2 y)

/-- The periodization `F y = ∑'_n χ(y+n)²` of `χ²`. -/
def F (y : Fin 3 → ℝ) : ℂ := ∑' n : Fin 3 → ℤ, g1 (y + kv n)

/-! ## `χ` vanishes on the sphere of radius `1/2` -/

lemma chiBump_zero_of_half_le_norm (x : E3) (hx : (1 / 2 : ℝ) ≤ ‖x‖) :
    Submission.BoseGases.chiBase x = 0 := by
  have h : Submission.BoseGases.chiBump.rOut ≤ dist x 0 := by
    rw [dist_eq_norm, sub_zero]
    simpa [Submission.BoseGases.chiBump] using hx
  simpa [Submission.BoseGases.chiBase] using
    (Submission.BoseGases.chiBump.zero_of_le_dist h)

/-- `χ` vanishes at distance `≥ 1/2` from the origin. -/
lemma chi_zero_of_half_le_norm (x : E3) (hx : (1 / 2 : ℝ) ≤ ‖x‖) :
    Submission.BoseGases.chi x = 0 := by
  rw [Submission.BoseGases.chi, chiBump_zero_of_half_le_norm x hx, zero_div]

/-- A coordinate of a point of `ℝ³` is bounded by its norm. -/
lemma abs_apply_le_norm (x : E3) (i : Fin 3) : |x i| ≤ ‖x‖ := by
  have h := PiLp.norm_apply_le x i
  simpa [Real.norm_eq_abs] using h

/-- `χ²` vanishes at every point having a coordinate of modulus `≥ 1/2`. -/
lemma g1_zero_of_abs_coord (y : Fin 3 → ℝ) (i : Fin 3) (h : (1 / 2 : ℝ) ≤ |y i|) :
    g1 y = 0 := by
  have hle : (1 / 2 : ℝ) ≤ ‖WithLp.toLp 2 y‖ := by
    refine h.trans ?_
    have h2 := abs_apply_le_norm (WithLp.toLp 2 y) i
    rwa [WithLp.ofLp_toLp] at h2
  simp [g1, gE, chi_zero_of_half_le_norm _ hle]

/-- `χ²` vanishes at distance `≥ 1/2` (Euclidean norm) from the origin. -/
lemma g1_zero_of_half_le_norm (y : Fin 3 → ℝ) (h : (1 / 2 : ℝ) ≤ ‖WithLp.toLp 2 y‖) :
    g1 y = 0 := by
  simp [g1, gE, chi_zero_of_half_le_norm _ h]

lemma g1_continuous : Continuous g1 := by
  have h1 : Continuous (fun y : Fin 3 → ℝ => (Submission.BoseGases.chi (WithLp.toLp 2 y)) ^ 2) :=
    (Submission.BoseGases.chi_continuous.comp (PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℝ))).pow 2
  exact Complex.continuous_ofReal.comp h1

lemma g1_even (y : Fin 3 → ℝ) : g1 (-y) = g1 y := by
  simp only [g1, gE, WithLp.toLp_neg, Submission.BoseGases.chi_even]


/-- `χ²` in the complex-valued form used downstream. -/
lemma gE_apply (x : E3) : gE x = Complex.ofReal ((Submission.BoseGases.chi x) ^ 2) := rfl

lemma g1_apply (y : Fin 3 → ℝ) :
    g1 y = Complex.ofReal ((Submission.BoseGases.chi (WithLp.toLp 2 y)) ^ 2) := rfl

/-! ## Summability of the periodization -/

/-- Each summand of the periodization vanishes off a finite set depending only on `y`. -/
lemma F_summable (y : Fin 3 → ℝ) : Summable (fun n : Fin 3 → ℤ => g1 (y + kv n)) := by
  classical
  set K : Fin 3 → ℤ := fun i => ⌈|y i| + 1⌉ with hK
  refine summable_of_ne_finset_zero
    (s := Fintype.piFinset (fun i : Fin 3 => Finset.Icc (-(K i)) (K i))) ?_
  intro n hn
  rw [Fintype.mem_piFinset] at hn
  push Not at hn
  obtain ⟨i, hi⟩ := hn
  rw [Finset.mem_Icc] at hi
  have hcases : (K i : ℤ) < n i ∨ n i < -(K i) := by
    by_contra hcon
    rw [not_or] at hcon
    exact hi ⟨not_lt.mp hcon.2, not_lt.mp hcon.1⟩
  refine g1_zero_of_abs_coord (y + kv n) i ?_
  have hKi : |y i| + 1 ≤ (K i : ℝ) := Int.le_ceil _
  have hni : (K i : ℝ) < |(n i : ℝ)| := by
    rcases hcases with h | h
    · have h' : (K i : ℝ) < (n i : ℝ) := by exact_mod_cast h
      exact lt_of_lt_of_le h' (le_abs_self _)
    · have h' : ((n i : ℤ) : ℝ) < -(K i : ℝ) := by exact_mod_cast h
      have h2 : (K i : ℝ) < (-(n i : ℤ) : ℝ) := by linarith
      simpa using lt_of_lt_of_le h2 (le_abs_self _)
  have hstep : |(n i : ℝ)| - |y i| ≤ |y i + (n i : ℝ)| := by
    have h := abs_sub_abs_le_abs_sub ((n i : ℝ)) (-(y i))
    rw [abs_neg, sub_neg_eq_add] at h
    simpa [add_comm] using h
  have : (1 / 2 : ℝ) ≤ |y i + (n i : ℝ)| := by linarith
  simpa [kv, Pi.add_apply] using this

/-! ## Continuity, periodicity, and values of the periodization -/

lemma F_continuous : Continuous F := by
  classical
  rw [continuous_iff_continuousAt]
  intro y₀
  set K : Fin 3 → ℤ := fun i => ⌈|y₀ i| + 2⌉ with hK
  set S : Finset (Fin 3 → ℤ) := Fintype.piFinset (fun i : Fin 3 => Finset.Icc (-(K i)) (K i))
    with hS
  have hfin : Continuous (fun y : Fin 3 → ℝ => ∑ n ∈ S, g1 (y + kv n)) := by
    refine continuous_finsetSum _ (fun n _ => ?_)
    exact g1_continuous.comp (continuous_id.add continuous_const)
  have hnb : ∀ᶠ y : Fin 3 → ℝ in 𝓝 y₀, ∀ i : Fin 3, |y i - y₀ i| < 1 := by
    rw [Filter.eventually_all]
    intro i
    have hcont : Continuous (fun y : Fin 3 → ℝ => |y i - y₀ i|) :=
      ((continuous_apply i).sub continuous_const).abs
    exact (isOpen_lt hcont continuous_const).mem_nhds (by simp)
  refine hfin.continuousAt.congr ?_
  filter_upwards [hnb] with y hy
  rw [F, tsum_eq_sum (s := S) (fun n hn => ?_)]
  rw [Fintype.mem_piFinset] at hn
  push Not at hn
  obtain ⟨i, hi⟩ := hn
  rw [Finset.mem_Icc] at hi
  have hcases : (K i : ℤ) < n i ∨ n i < -(K i) := by
    by_contra hcon
    rw [not_or] at hcon
    exact hi ⟨not_lt.mp hcon.2, not_lt.mp hcon.1⟩
  refine g1_zero_of_abs_coord (y + kv n) i ?_
  have hKi : |y₀ i| + 2 ≤ (K i : ℝ) := Int.le_ceil _
  have hni : (K i : ℝ) < |(n i : ℝ)| := by
    rcases hcases with h | h
    · have h' : (K i : ℝ) < (n i : ℝ) := by exact_mod_cast h
      exact lt_of_lt_of_le h' (le_abs_self _)
    · have h' : ((n i : ℤ) : ℝ) < -(K i : ℝ) := by exact_mod_cast h
      have h2 : (K i : ℝ) < (-(n i : ℤ) : ℝ) := by linarith
      simpa using lt_of_lt_of_le h2 (le_abs_self _)
  have hyi : |y i| < |y₀ i| + 1 := by
    have h := abs_sub_abs_le_abs_sub (y i) (y₀ i)
    have h' : |y i| - |y₀ i| ≤ |y i - y₀ i| := h
    have := hy i
    linarith
  have hstep : |(n i : ℝ)| - |y i| ≤ |y i + (n i : ℝ)| := by
    have h := abs_sub_abs_le_abs_sub ((n i : ℝ)) (-(y i))
    rw [abs_neg, sub_neg_eq_add] at h
    simpa [add_comm] using h
  have : (1 / 2 : ℝ) ≤ |y i + (n i : ℝ)| := by linarith
  simpa [kv, Pi.add_apply] using this

/-- The periodization is invariant under the `ℤ³`-action. -/
lemma F_periodic (k : Fin 3 → ℤ) (y : Fin 3 → ℝ) : F (y + kv k) = F y := by
  have h1 : (fun n : Fin 3 → ℤ => g1 (y + kv k + kv n)) =
      fun n : Fin 3 → ℤ => g1 (y + kv (n + k)) := by
    funext n
    have hadd : y + kv k + kv n = y + kv (n + k) := by
      funext i
      simp only [Pi.add_apply, kv]
      push_cast
      ring
    rw [hadd]
  rw [F, F, h1]
  exact Equiv.tsum_eq (Equiv.addRight k) (fun n : Fin 3 → ℤ => g1 (y + kv n))

lemma F_zero : F 0 = g1 0 := by
  rw [F]
  simp only [zero_add]
  rw [tsum_eq_single 0 (fun n hn => ?_)]
  · congr 1
    funext i
    simp [kv]
  · obtain ⟨i, hi⟩ : ∃ i : Fin 3, n i ≠ 0 := by
      by_contra h
      push Not at h
      exact hn (funext h)
    refine g1_zero_of_abs_coord (kv n) i ?_
    have h1 : (1 : ℤ) ≤ |n i| := by
      have hpos : 0 < |n i| := abs_pos.mpr hi
      omega
    have h2 : (1 : ℝ) ≤ |(n i : ℝ)| := by exact_mod_cast h1
    simp only [kv]
    linarith

/-- On the half-open unit cube `(-1/2,1/2]³` only the `n = 0` translate survives, so `F = χ²`. -/
lemma F_eq_of_mem_cube (y : Fin 3 → ℝ) (hy : ∀ i : Fin 3, y i ∈ Set.Ioc (-(1 / 2)) (1 / 2)) :
    F y = g1 y := by
  rw [F]
  rw [tsum_eq_single 0 (fun n hn => ?_)]
  · congr 1
    funext i
    simp [kv]
  · obtain ⟨i, hi⟩ : ∃ i : Fin 3, n i ≠ 0 := by
      by_contra h
      push Not at h
      exact hn (funext h)
    refine g1_zero_of_abs_coord (y + kv n) i ?_
    have hyi : |y i| ≤ (1 / 2 : ℝ) := by
      have h := hy i
      rw [Set.mem_Ioc] at h
      rw [abs_le]
      exact ⟨h.1.le, h.2⟩
    have hni : (1 : ℝ) ≤ |(n i : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |n i| := by
        have hpos : 0 < |n i| := abs_pos.mpr hi
        omega
      exact_mod_cast h1
    have hstep : |(n i : ℝ)| - |y i| ≤ |y i + (n i : ℝ)| := by
      have h := abs_sub_abs_le_abs_sub ((n i : ℝ)) (-(y i))
      rw [abs_neg, sub_neg_eq_add] at h
      simpa [add_comm] using h
    simp only [Pi.add_apply, kv]
    linarith

/-! ## The torus function `P` -/

/-- The continuous function on `𝕋³` whose lift to `ℝ³` is the periodization `F`. -/
noncomputable def P : UnitAddTorus (Fin 3) → ℂ :=
  (torus_lift F F_continuous F_periodic).choose

lemma P_continuous : Continuous P := (torus_lift F F_continuous F_periodic).choose_spec.1

lemma P_apply (y : Fin 3 → ℝ) : P (fun i => (y i : UnitAddCircle)) = F y :=
  (torus_lift F F_continuous F_periodic).choose_spec.2 y

end Work.BoseB7AK.Q2Gram
