import Mathlib
import Submission.ArcFamily
import Submission.S5_defs
import Submission.TrigObservation
import Submission.PeriodicLemma
import Submission.Consts
import Submission.S5H
import Submission.S5Tele
import Submission.S5sinc_num
import Submission.S5si_bounds

/-! Section 5 (paper arXiv:1907.09464v1 §5): bounds on the polynomial
`ŝ_α(θ0) = Σ_r ê_r(α)·sin((2r+1)θ0)` over the quadrant.

We prove:

  (LOW)   θ0 ∈ [0,π/2], θ0 in the union of the family intervals
          ⇒  (3/5)·K·√n  ≤  |ŝ(θ0)| ;
  (HIGH)  θ0 ∈ [0,π/2]   ⇒  |ŝ(θ0)| ≤ 8·K·√n . -/

noncomputable section
open scoped BigOperators
open MeasureTheory

set_option autoImplicit false

namespace Submission
namespace S5

/-! Kernel objects. -/

/-- quadrant left cut `100π/n` -/
def qA (n : ℕ) : ℝ := (100 : ℝ) * Real.pi / (n : ℝ)

/-- quadrant right cut `π/2 − 100π/n` -/
def qB (n : ℕ) : ℝ := Real.pi / 2 - (100 : ℝ) * Real.pi / (n : ℝ)

/-- `4·Σ_{r<n} sin((2r+1)θ)·sin((2r+1)θ0)` -/
def ker4 (n : ℕ) (θ θ0 : ℝ) : ℝ :=
  4 * (∑ r ∈ Finset.range n, oddSin r θ * oddSin r θ0)

/-- Dirichlet kernel `sin(2n(θ−θ0))/sin(θ−θ0)` (Lean division at `θ=θ0`) -/
def dirK (n : ℕ) (θ0 θ : ℝ) : ℝ :=
  Real.sin (2 * (n : ℝ) * (θ - θ0)) / Real.sin (θ - θ0)

/-- second Dirichlet term `sin(2n(θ+θ0))/sin(θ+θ0)` -/
def dirK2 (n : ℕ) (θ0 θ : ℝ) : ℝ :=
  Real.sin (2 * (n : ℝ) * (θ + θ0)) / Real.sin (θ + θ0)

/-- linearised kernel `sin(2n(θ−θ0))/(θ−θ0)` (Lean division at `θ=θ0`) -/
def linK (n : ℕ) (θ0 θ : ℝ) : ℝ :=
  Real.sin (2 * (n : ℝ) * (θ - θ0)) / (θ - θ0)

/-- `H(u) = 1/sin u − 1/u` -/
def Hf (u : ℝ) : ℝ := S5H.H u

/-- `qB n = π/2 − qA n` -/
lemma qB_eq (n : ℕ) : qB n = Real.pi / 2 - qA n := by
  unfold qB qA
  ring


/-! ===================== geometry ===================== -/

/-- n ≥ 1 from the hypothesis -/
lemma n_ge_one {n : ℕ} (hn : 2 ^ 16 ≤ n) : 1 ≤ n := le_trans (by norm_num) hn

/-- (n : ℝ) > 0 -/
lemma nR_pos {n : ℕ} (hn : 2 ^ 16 ≤ n) : 0 < (n : ℝ) := by
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (n_ge_one hn)
  nlinarith

/-- (n : ℝ) ≥ 2^16 -/
lemma nR_ge_pow {n : ℕ} (hn : 2 ^ 16 ≤ n) : (2 ^ 16 : ℝ) ≤ (n : ℝ) := by
  exact_mod_cast hn

/-- `100π/n < π/4` for n ≥ 2^16 -/
lemma qA_lt_pi_div_four {n : ℕ} (hn : 2 ^ 16 ≤ n) : qA n < Real.pi / 4 := by
  have hn0 : 0 < (n : ℝ) := nR_pos hn
  have hnbig : (400 : ℝ) < (n : ℝ) := by
    have hn' : (2 ^ 16 : ℝ) ≤ (n : ℝ) := nR_ge_pow hn
    norm_num at hn' ⊢
    linarith
  have hden : (100 : ℝ) / (n : ℝ) < 1 / 4 := by
    rw [div_lt_iff₀ hn0]
    nlinarith
  have hπ : 0 < Real.pi := Real.pi_pos
  have hprod : (100 : ℝ) / (n : ℝ) * Real.pi < (1 / 4) * Real.pi :=
    mul_lt_mul_of_pos_right hden hπ
  unfold qA
  convert hprod using 1 <;> field_simp [ne_of_gt hn0]

/-- `100π/n ≤ π/4` -/
lemma qA_le_pi_div_four {n : ℕ} (hn : 2 ^ 16 ≤ n) : qA n ≤ Real.pi / 4 :=
  (qA_lt_pi_div_four hn).le

/-- `qA n ≤ π/2` -/
lemma qA_le_pi_div_two {n : ℕ} (hn : 2 ^ 16 ≤ n) : qA n ≤ Real.pi / 2 := by
  linarith [qA_le_pi_div_four hn, Real.pi_pos]

/-- `qA n > 0` -/
lemma qA_pos {n : ℕ} (hn : 2 ^ 16 ≤ n) : 0 < qA n := by
  unfold qA
  positivity

/-- `qA n < qB n`, `0 < qB n`, `qB n < π/2` -/
lemma qB_bounds {n : ℕ} (hn : 2 ^ 16 ≤ n) :
    qA n < qB n ∧ 0 < qB n ∧ qB n < Real.pi / 2 := by
  have hqA : qA n < Real.pi / 4 := qA_lt_pi_div_four hn
  have hqA0 : 0 < qA n := qA_pos hn
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [qB_eq]
  constructor
  · nlinarith [hqA, hpi]
  · constructor
    · nlinarith [hqA0]
    · nlinarith [hqA0]

/-- arcs start at ≥ qA -/
lemma arc_lo_ge_qA {n N : ℕ} (hn : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N) :
    qA n ≤ (F.arc i).lo := by
  unfold qA Family.Grid.lo
  have hp : (100 : ℝ) ≤ ((F.arc i).p : ℝ) := by exact_mod_cast (F.far_left i)
  have hn0 : 0 ≤ (n : ℝ) := (nR_pos hn).le
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hp hpi) hn0

/-- arcs end at ≤ qB -/
lemma arc_hi_le_qB {n N : ℕ} (hn : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N) :
    (F.arc i).hi ≤ qB n := by
  unfold qB Family.Grid.hi
  have hfar : 2 * (F.arc i).q + 200 ≤ (n : ℤ) := F.far_right i
  have hcast : ((2 * (F.arc i).q + 200 : ℤ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hfar
  have hq : ((F.arc i).q : ℝ) ≤ ((n : ℝ) - 200) / 2 := by
    have : (2 : ℝ) * ((F.arc i).q : ℝ) + 200 ≤ (n : ℝ) := by
      norm_num at hcast ⊢
      exact hcast
    linarith
  have hn0 : 0 < (n : ℝ) := nR_pos hn
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  calc
    ((F.arc i).q : ℝ) * Real.pi / (n : ℝ)
        ≤ ((((n : ℝ) - 200) / 2) * Real.pi) / (n : ℝ) := by
          exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hq hpi) hn0.le
    _ = Real.pi / 2 - (100 : ℝ) * Real.pi / (n : ℝ) := by
      field_simp [ne_of_gt hn0]
      ring

/-- arcs are non-degenerate with lo < hi -/
lemma arc_lo_lt_hi {n N : ℕ} (hn : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N) :
    (F.arc i).lo < (F.arc i).hi := by
  have hsub : (F.arc i).hi - (F.arc i).lo = ((F.arc i).len : ℝ) * Real.pi / (n : ℝ) :=
    Family.Grid.hi_sub_lo (F.arc i) (by linarith [n_ge_one hn])
  have hlen : (1 : ℝ) ≤ ((F.arc i).len : ℝ) := by
    have : 1 ≤ (F.arc i).len := by
      have : (F.arc i).p + 1 ≤ (F.arc i).q := Int.add_one_le_iff.mpr (F.arc i).hlt
      unfold Family.Grid.len
      omega
    exact_mod_cast this
  have hn0 : 0 < (n : ℝ) := nR_pos hn
  have hpos : 0 < (F.arc i).hi - (F.arc i).lo := by
    rw [hsub]
    positivity
  linarith

/-- arcs lie within (0, π/2) -/
lemma arc_in_quadrant {n N : ℕ} (hn : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N) :
    (0 : ℝ) < (F.arc i).lo ∧ (F.arc i).hi < Real.pi / 2 := by
  constructor
  · exact lt_of_lt_of_le (qA_pos hn) (arc_lo_ge_qA hn F i)
  · exact lt_of_le_of_lt (arc_hi_le_qB hn F i) (qB_bounds hn).2.2

/-- grid length of an arc: `∃ m ≤ 6, hi−lo = m·π/n` -/
lemma arc_len_multiple {n N : ℕ} (hn : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N) :
    ∃ m : ℕ, m ≤ 6 ∧ (F.arc i).hi - (F.arc i).lo = (m : ℝ) * Real.pi / (n : ℝ) := by
  let z : ℤ := (F.arc i).len
  have hz1 : 1 ≤ z := by
    have : (F.arc i).p + 1 ≤ (F.arc i).q := Int.add_one_le_iff.mpr (F.arc i).hlt
    unfold z Family.Grid.len
    omega
  have hz0 : 0 ≤ z := by linarith
  let m : ℕ := z.toNat
  have hmz : (m : ℤ) = z := Int.toNat_of_nonneg hz0
  have hmzR : (m : ℝ) = (z : ℝ) := by exact_mod_cast hmz
  refine ⟨m, ?mle, ?hid⟩
  · have hz6 : z ≤ 6 := by
      unfold z
      exact F.len_le i
    have hm6 : (m : ℕ) ≤ 6 := by
      have : (m : ℤ) ≤ 6 := by simpa [m, hmz] using hz6
      exact_mod_cast this
    exact hm6
  · rw [Family.Grid.hi_sub_lo (F.arc i) (by linarith [n_ge_one hn])]
    rw [hmzR]

/-- length ≤ 6π/n -/
lemma arc_len_le_six {n N : ℕ} (hn : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N) :
    (F.arc i).hi - (F.arc i).lo ≤ 6 * Real.pi / (n : ℝ) := by
  rcases arc_len_multiple hn F i with ⟨m, hm6, hm⟩
  have hn0 : 0 ≤ (n : ℝ) := (nR_pos hn).le
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  calc
    (F.arc i).hi - (F.arc i).lo = (m : ℝ) * Real.pi / (n : ℝ) := hm
    _ ≤ 6 * Real.pi / (n : ℝ) := by
      have hmR : (m : ℝ) ≤ 6 := by exact_mod_cast hm6
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hmR hpi) hn0

/-- if `q i < p j` then the intervals are at least π/n apart -/
lemma arc_hi_le_lo_sub {n N : ℕ} (hn : 2 ^ 16 ≤ n) (F : Family.Quad n N) {i j : Fin N}
    (hij : (F.arc i).q < (F.arc j).p) :
    (F.arc i).hi ≤ (F.arc j).lo - Real.pi / (n : ℝ) := by
  have hpq : (1 : ℤ) ≤ (F.arc j).p - (F.arc i).q := by omega
  have hpR : (1 : ℝ) ≤ ((F.arc j).p : ℝ) - ((F.arc i).q : ℝ) := by exact_mod_cast hpq
  have hn0 : 0 < (n : ℝ) := nR_pos hn
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  calc
    (F.arc i).hi = ((F.arc i).q : ℝ) * Real.pi / (n : ℝ) := rfl
    _ ≤ (((F.arc j).p : ℝ) - 1) * Real.pi / (n : ℝ) := by
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (by linarith) hpi) hn0.le
    _ = (F.arc j).lo - Real.pi / (n : ℝ) := by
      unfold Family.Grid.lo
      field_simp [ne_of_gt hn0]

/-- pairwise separation in terms of real endpoints -/
lemma arc_sep {n N : ℕ} (hn : 2 ^ 16 ≤ n) (F : Family.Quad n N) {i j : Fin N} (hij : i ≠ j) :
    (F.arc i).hi < (F.arc j).lo ∨ (F.arc j).hi < (F.arc i).lo := by
  rcases F.sep hij with h | h
  · left
    have hcast : ((F.arc i).q : ℝ) < ((F.arc j).p : ℝ) := by exact_mod_cast h
    unfold Family.Grid.hi Family.Grid.lo
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hcast Real.pi_pos) (nR_pos hn)
  · right
    have hcast : ((F.arc j).q : ℝ) < ((F.arc i).p : ℝ) := by exact_mod_cast h
    unfold Family.Grid.hi Family.Grid.lo
    exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_right hcast Real.pi_pos) (nR_pos hn)

/-- for `i ≠ i0`, arc `i` is at distance ≥ π/n on the left or on the right of i0 -/
lemma arc_left_or_right {n N : ℕ} (hn : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i0 i : Fin N)
    (h : i ≠ i0) :
    (F.arc i).hi ≤ (F.arc i0).lo - Real.pi / (n : ℝ) ∨
      (F.arc i0).hi + Real.pi / (n : ℝ) ≤ (F.arc i).lo := by
  rcases F.sep h with hlt | hlt
  · left
    exact arc_hi_le_lo_sub hn F hlt
  · right
    have hg := arc_hi_le_lo_sub hn F hlt
    linarith




/-! ============= integral utilities (a.e. single point) ============= -/

/-- integrals agree when the integrands agree off a single point on `[a,b]` -/
lemma integral_congr_eqOn_singleton {a b c : ℝ} {f g : ℝ → ℝ} (hab : a ≤ b)
    (h : ∀ x ∈ Set.Icc a b, x ≠ c → f x = g x) :
    (∫ x in a..b, f x) = ∫ x in a..b, g x := by
  apply intervalIntegral.integral_congr_ae (μ := volume)
  rw [MeasureTheory.ae_iff]
  apply measure_mono_null (s := {x | ¬(x ∈ Set.uIoc a b → f x = g x)}) (t := {c})
  · intro x hx
    by_contra hxc
    apply hx
    intro hmem
    have hmem' : x ∈ Set.Icc a b := by
      have hsub : Set.uIoc a b ⊆ Set.Icc a b := by
        rw [← Set.uIcc_of_le hab]
        exact Set.uIoc_subset_uIcc
      exact hsub hmem
    exact h x hmem' hxc
  · exact Real.volume_singleton (a := c)

/-- `sin u ≠ 0` when `u ≠ 0`, `|u| < π` -/
lemma sin_ne_zero_of_abs_lt_pi {u : ℝ} (hu0 : u ≠ 0) (hu : |u| < Real.pi) : Real.sin u ≠ 0 := by
  intro hs
  rcases Real.sin_eq_zero_iff.mp hs with ⟨k, hk⟩
  have hk0 : k = 0 := by
    by_contra hk0
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
      exact_mod_cast this
    have hkabs : |u| = |(k : ℝ)| * Real.pi := by
      rw [← hk, abs_mul, abs_of_pos Real.pi_pos]
    have hbig : Real.pi ≤ |u| := by
      rw [hkabs]
      nlinarith [mul_le_mul_of_nonneg_right hk1 (le_of_lt Real.pi_pos)]
    nlinarith
  subst k
  simp at hk
  exact hu0 hk.symm

/-- continuous extension kernel `2n·sinc(2n u)/sinc u` -/
def DK1 (n : ℕ) (θ0 θ : ℝ) : ℝ :=
  2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * (θ - θ0)) / Real.sinc (θ - θ0)

/-- second Dirichlet term (no singularity on the quadrant) -/
def DK2 (n : ℕ) (θ0 θ : ℝ) : ℝ :=
  Real.sin (2 * (n : ℝ) * (θ + θ0)) / Real.sin (θ + θ0)

/-- linearised continuous kernel `2n·sinc(2n(θ−θ0))` -/
def LK (n : ℕ) (θ0 θ : ℝ) : ℝ := 2 * (n : ℝ) * Real.sinc (2 * (n : ℝ) * (θ - θ0))

/-- `sinc u ≠ 0` when `|u| ≤ π/2` -/
lemma sinc_ne_zero_of_abs_le_pi_div_two {u : ℝ} (hu : |u| ≤ Real.pi / 2) : Real.sinc u ≠ 0 := by
  by_cases hu0 : u = 0
  · simp [hu0]
  · have hpi : 0 < Real.pi := Real.pi_pos
    rw [Real.sinc_of_ne_zero hu0]
    exact div_ne_zero (sin_ne_zero_of_abs_lt_pi hu0 (by linarith)) hu0

/-- arcs: `θ ∈ [lo,hi]`, θ0 in quadrant ⇒ θ in (0,π/2), |θ−θ0|<π/2, θ+θ0 ∈ (0,π), sin(θ+θ0)>0 -/
lemma arc_theta_domain {n N : ℕ} (hn : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N)
    {θ0 θ : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2)
    (hθ : θ ∈ Set.Icc (F.arc i).lo (F.arc i).hi) :
    (0 : ℝ) < θ ∧ θ < Real.pi / 2 ∧ |θ - θ0| < Real.pi / 2 ∧
      (0 < θ + θ0 ∧ θ + θ0 < Real.pi ∧ 0 < Real.sin (θ + θ0)) := by
  have harc := arc_in_quadrant hn F i
  have hlo : (F.arc i).lo ≤ θ := hθ.1
  have hhi : θ ≤ (F.arc i).hi := hθ.2
  have hθ0 : 0 < θ := lt_of_lt_of_le harc.1 hlo
  have hθ1 : θ < Real.pi / 2 := lt_of_le_of_lt hhi harc.2
  have hu1 : -(Real.pi / 2) < θ - θ0 := by linarith
  have hu2 : θ - θ0 < Real.pi / 2 := by linarith
  have hsum_lo : 0 < θ + θ0 := by linarith
  have hsum_hi : θ + θ0 < Real.pi := by linarith
  constructor
  · exact hθ0
  constructor
  · exact hθ1
  constructor
  · rw [abs_lt]
    exact ⟨hu1, hu2⟩
  · exact ⟨hsum_lo, hsum_hi, Real.sin_pos_of_pos_of_lt_pi hsum_lo hsum_hi⟩

/-- `ker4 = DK1 − DK2` off `θ0` on an arc -/
lemma ker4_eq_DK (n : ℕ) (hn : 1 ≤ n) {θ0 θ : ℝ} (h : θ ≠ θ0)
    (hu : |θ - θ0| < Real.pi / 2) (hsum0 : 0 < θ + θ0) (hsumπ : θ + θ0 < Real.pi) :
    ker4 n θ θ0 = DK1 n θ0 θ - DK2 n θ0 θ := by
  have hu0 : θ - θ0 ≠ 0 := by intro hh; apply h; linarith
  have hs : Real.sin (θ - θ0) ≠ 0 := sin_ne_zero_of_abs_lt_pi hu0 (by linarith)
  have hs2 : Real.sin (θ + θ0) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi hsum0 hsumπ).ne'
  have hk := Trig.odd_sine_kernel n θ θ0 hs hs2
  have hk4 : ker4 n θ θ0 =
      4 * (∑ r ∈ Finset.range n,
        Real.sin (((2 * (r : ℕ) + 1 : ℕ) : ℝ) * θ) *
        Real.sin (((2 * (r : ℕ) + 1 : ℕ) : ℝ) * θ0)) := by
    unfold ker4
    apply congrArg (fun t : ℝ => 4 * t)
    apply Finset.sum_congr rfl
    intro r hr
    unfold oddSin freq
    congr 1 <;> push_cast <;> ring
  rw [← hk4] at hk
  have hd1 : Real.sin (2 * (n : ℝ) * (θ - θ0)) / Real.sin (θ - θ0) = DK1 n θ0 θ := by
    unfold DK1
    rw [Real.sinc_of_ne_zero (mul_ne_zero (by positivity : (2 * (n : ℝ)) ≠ 0) hu0)]
    rw [Real.sinc_of_ne_zero hu0]
    field_simp [hs, hu0]
  have hd2 : Real.sin (2 * (n : ℝ) * (θ + θ0)) / Real.sin (θ + θ0) = DK2 n θ0 θ := rfl
  rw [hd1, hd2] at hk
  exact hk

/-- per-arc integral identity `∫ ker4 = ∫ DK1 − ∫ DK2` (θ0 in quadrant) -/
lemma arc_integral_ker (n N : ℕ) (hn : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    (∫ θ in (F.arc i).lo..(F.arc i).hi, ker4 n θ θ0)
      = (∫ θ in (F.arc i).lo..(F.arc i).hi, DK1 n θ0 θ)
        - (∫ θ in (F.arc i).lo..(F.arc i).hi, DK2 n θ0 θ) := by
  have hab : (F.arc i).lo ≤ (F.arc i).hi := (arc_lo_lt_hi hn F i).le
  have hinteq : (∫ θ in (F.arc i).lo..(F.arc i).hi, ker4 n θ θ0)
      = ∫ θ in (F.arc i).lo..(F.arc i).hi, (DK1 n θ0 θ - DK2 n θ0 θ) := by
    apply integral_congr_eqOn_singleton (a := (F.arc i).lo) (b := (F.arc i).hi) (c := θ0) hab
    intro θ hθmem hθne
    rcases arc_theta_domain hn F i hθ0a hθ0b hθmem with ⟨_, _, hu, hsum⟩
    exact ker4_eq_DK n (n_ge_one hn) hθne hu hsum.1 hsum.2.1
  have hc1 : ContinuousOn (DK1 n θ0) (Set.Icc (F.arc i).lo (F.arc i).hi) := by
    unfold DK1
    apply ContinuousOn.div
    · apply ContinuousOn.mul
      · exact continuousOn_const
      · exact (Real.continuous_sinc.comp (continuous_const.mul (Continuous.sub continuous_id continuous_const))).continuousOn
    · exact (Real.continuous_sinc.comp (Continuous.sub continuous_id continuous_const)).continuousOn
    · intro x hx
      exact sinc_ne_zero_of_abs_le_pi_div_two (by
        rcases arc_theta_domain hn F i hθ0a hθ0b hx with ⟨_, _, hu, _⟩
        exact hu.le)
  have hc2 : ContinuousOn (DK2 n θ0) (Set.Icc (F.arc i).lo (F.arc i).hi) := by
    unfold DK2
    apply ContinuousOn.div
    · exact (Real.continuous_sin.comp (continuous_const.mul (Continuous.add continuous_id continuous_const))).continuousOn
    · exact (Real.continuous_sin.comp (Continuous.add continuous_id continuous_const)).continuousOn
    · intro x hx
      rcases arc_theta_domain hn F i hθ0a hθ0b hx with ⟨_, _, _, hsum⟩
      exact hsum.2.2.ne'
  have hi1 : IntervalIntegrable (DK1 n θ0) volume (F.arc i).lo (F.arc i).hi :=
    ContinuousOn.intervalIntegrable_of_Icc hab hc1
  have hi2 : IntervalIntegrable (DK2 n θ0) volume (F.arc i).lo (F.arc i).hi :=
    ContinuousOn.intervalIntegrable_of_Icc hab hc2
  rw [hinteq]
  rw [intervalIntegral.integral_sub hi1 hi2]




/-! ============= finite-sum / integral interchange ============= -/

/-- continuity of a finite sum of continuous functions on an interval -/
lemma continuousOn_sum_range {a b : ℝ} (n : ℕ) (h : ℕ → ℝ → ℝ)
    (hcont : ∀ r, ContinuousOn (h r) (Set.Icc a b)) :
    ContinuousOn (fun θ : ℝ => ∑ r ∈ Finset.range n, h r θ) (Set.Icc a b) := by
  induction n with
  | zero =>
      simp
      exact continuousOn_const
  | succ n ih =>
      simp_rw [Finset.sum_range_succ]
      exact ih.add (hcont n)

/-- sum of integrals = integral of (finite) sum, continuous integrands -/
lemma sum_integral_lin (a b : ℝ) (hab : a ≤ b) (n : ℕ) (h : ℕ → ℝ → ℝ)
    (hcont : ∀ r, ContinuousOn (h r) (Set.Icc a b)) :
    (∑ r ∈ Finset.range n, ∫ θ in a..b, h r θ) = ∫ θ in a..b, (∑ r ∈ Finset.range n, h r θ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have h1 : IntervalIntegrable (fun θ : ℝ => ∑ r ∈ Finset.range n, h r θ) volume a b :=
        ContinuousOn.intervalIntegrable_of_Icc hab (continuousOn_sum_range n h hcont)
      have h2 : IntervalIntegrable (fun θ : ℝ => h n θ) volume a b :=
        ContinuousOn.intervalIntegrable_of_Icc hab (hcont n)
      calc
        (∑ r ∈ Finset.range (n + 1), ∫ θ in a..b, h r θ)
            = (∑ r ∈ Finset.range n, ∫ θ in a..b, h r θ) + ∫ θ in a..b, h n θ := by
                simp_rw [Finset.sum_range_succ]
        _ = (∫ θ in a..b, (∑ r ∈ Finset.range n, h r θ)) + ∫ θ in a..b, h n θ := by rw [ih]
        _ = ∫ θ in a..b, ((∑ r ∈ Finset.range n, h r θ) + h n θ) := by
                rw [intervalIntegral.integral_add h1 h2]
        _ = ∫ θ in a..b, (∑ r ∈ Finset.range (n + 1), h r θ) := by
                simp_rw [Finset.sum_range_succ]



/-! ============= sHat as a sum over arcs ============= -/

/-- `4·Σ_r sin·sin` written with 4 inside the sum -/
def K4i (n : ℕ) (θ θ0 : ℝ) : ℝ := ∑ r ∈ Finset.range n, 4 * (oddSin r θ * oddSin r θ0)

lemma K4i_eq_ker4 (n : ℕ) (θ θ0 : ℝ) : K4i n θ θ0 = ker4 n θ θ0 := by
  unfold K4i ker4
  rw [Finset.mul_sum]

lemma per_r_identity (n : ℕ) (K : ℝ) (a b : ℝ) (r : ℕ) (θ0 : ℝ) :
    K * Real.sqrt (n : ℝ) * ∫ θ in a..b, 4 * (oddSin r θ * oddSin r θ0)
      = (4 * K * Real.sqrt (n : ℝ) * ∫ θ in a..b, oddSin r θ) * oddSin r θ0 := by
  rw [intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_mul_const]
  ring

lemma sum_mul_factor (n : ℕ) (α : ℝ) (X : ℕ → ℝ) :
    (∑ r ∈ Finset.range n, α * X r) = α * (∑ r ∈ Finset.range n, X r) := by
  rw [Finset.mul_sum]

lemma arc_sum_identity0 (n : ℕ) (K : ℝ) (a b : ℝ) (hab : a ≤ b) (θ0 : ℝ) :
    (∑ r ∈ Finset.range n, (4 * K * Real.sqrt (n : ℝ) * ∫ θ in a..b, oddSin r θ) * oddSin r θ0)
      = K * Real.sqrt (n : ℝ) * (∫ θ in a..b, K4i n θ θ0) := by
  calc
    (∑ r ∈ Finset.range n, (4 * K * Real.sqrt (n : ℝ) * ∫ θ in a..b, oddSin r θ) * oddSin r θ0)
        = ∑ r ∈ Finset.range n,
            K * Real.sqrt (n : ℝ) * ∫ θ in a..b, 4 * (oddSin r θ * oddSin r θ0) := by
            apply Finset.sum_congr rfl
            intro r hr
            exact (per_r_identity n K a b r θ0).symm
    _ = K * Real.sqrt (n : ℝ) * (∑ r ∈ Finset.range n,
          ∫ θ in a..b, 4 * (oddSin r θ * oddSin r θ0)) := by
          exact sum_mul_factor n (K * Real.sqrt (n : ℝ))
            (fun r => ∫ θ in a..b, 4 * (oddSin r θ * oddSin r θ0))
    _ = K * Real.sqrt (n : ℝ) * (∫ θ in a..b, K4i n θ θ0) := by
          have hs : (∑ r ∈ Finset.range n, ∫ θ in a..b, 4 * (oddSin r θ * oddSin r θ0))
              = ∫ θ in a..b, (∑ r ∈ Finset.range n, 4 * (oddSin r θ * oddSin r θ0)) :=
                sum_integral_lin a b hab n (fun r θ => 4 * (oddSin r θ * oddSin r θ0))
                  (by intro r; unfold oddSin freq; fun_prop)
          rw [hs]
          congr 2

lemma arc_sum_identity (n : ℕ) (K : ℝ) (a b : ℝ) (hab : a ≤ b) (α θ0 : ℝ) :
    (∑ r ∈ Finset.range n, (α * (4 * K * Real.sqrt (n : ℝ) * ∫ θ in a..b, oddSin r θ)) * oddSin r θ0)
      = α * K * Real.sqrt (n : ℝ) * (∫ θ in a..b, K4i n θ θ0) := by
  calc
    (∑ r ∈ Finset.range n, (α * (4 * K * Real.sqrt (n : ℝ) * ∫ θ in a..b, oddSin r θ)) * oddSin r θ0)
        = ∑ r ∈ Finset.range n,
            α * ((4 * K * Real.sqrt (n : ℝ) * ∫ θ in a..b, oddSin r θ) * oddSin r θ0) := by
            apply Finset.sum_congr rfl
            intro r hr
            ring
    _ = α * (∑ r ∈ Finset.range n, (4 * K * Real.sqrt (n : ℝ) * ∫ θ in a..b, oddSin r θ) * oddSin r θ0) := by
            exact sum_mul_factor n α (fun r => (4 * K * Real.sqrt (n : ℝ) * ∫ θ in a..b, oddSin r θ) * oddSin r θ0)
    _ = α * (K * Real.sqrt (n : ℝ) * (∫ θ in a..b, K4i n θ θ0)) := by
          rw [arc_sum_identity0 n K a b hab θ0]
    _ = α * K * Real.sqrt (n : ℝ) * (∫ θ in a..b, K4i n θ θ0) := by
          ring

/-- sHat equals K√n times the sum over arcs of the ker4 integral -/
lemma sHat_eq_sum_arcs (n N : ℕ) (K : ℝ) (F : Family.Quad n N) (α : Fin N → ℝ) (θ0 : ℝ) :
    sHat n N K F α θ0 =
      K * Real.sqrt (n : ℝ) *
        (∑ i : Fin N, α i * (∫ θ in (F.arc i).lo..(F.arc i).hi, ker4 n θ θ0)) := by
  calc
    sHat n N K F α θ0 = ∑ r ∈ Finset.range n,
        (∑ i : Fin N, α i * (4 * K * Real.sqrt (n : ℝ) * ∫ θ in (F.arc i).lo..(F.arc i).hi, oddSin r θ)) * oddSin r θ0 := by
        unfold sHat ehat vec
        rfl
    _ = ∑ i : Fin N, ∑ r ∈ Finset.range n,
          (α i * (4 * K * Real.sqrt (n : ℝ) * ∫ θ in (F.arc i).lo..(F.arc i).hi, oddSin r θ)) * oddSin r θ0 := by
        simp_rw [Finset.sum_mul]
        rw [Finset.sum_comm]
    _ = K * Real.sqrt (n : ℝ) *
        (∑ i : Fin N, α i * (∫ θ in (F.arc i).lo..(F.arc i).hi, K4i n θ θ0)) := by
        have hstep : (∑ i : Fin N, ∑ r ∈ Finset.range n,
              (α i * (4 * K * Real.sqrt (n : ℝ) * ∫ θ in (F.arc i).lo..(F.arc i).hi, oddSin r θ)) * oddSin r θ0)
            = ∑ i : Fin N, α i * K * Real.sqrt (n : ℝ) *
                (∫ θ in (F.arc i).lo..(F.arc i).hi, K4i n θ θ0) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact arc_sum_identity n K (F.arc i).lo (F.arc i).hi (Family.Grid.lo_le_hi (F.arc i)) (α i) θ0
        calc
          (∑ i : Fin N, ∑ r ∈ Finset.range n,
              (α i * (4 * K * Real.sqrt (n : ℝ) * ∫ θ in (F.arc i).lo..(F.arc i).hi, oddSin r θ)) * oddSin r θ0)
              = ∑ i : Fin N, α i * K * Real.sqrt (n : ℝ) *
                  (∫ θ in (F.arc i).lo..(F.arc i).hi, K4i n θ θ0) := hstep
          _ = K * Real.sqrt (n : ℝ) *
              (∑ i : Fin N, α i * (∫ θ in (F.arc i).lo..(F.arc i).hi, K4i n θ θ0)) := by
              have hpull : (∑ i : Fin N, α i * K * Real.sqrt (n : ℝ) *
                    (∫ θ in (F.arc i).lo..(F.arc i).hi, K4i n θ θ0))
                  = K * Real.sqrt (n : ℝ) *
                      (∑ i : Fin N, α i * (∫ θ in (F.arc i).lo..(F.arc i).hi, K4i n θ θ0)) := by
                  calc
                    (∑ i : Fin N, α i * K * Real.sqrt (n : ℝ) * (∫ θ in (F.arc i).lo..(F.arc i).hi, K4i n θ θ0))
                        = ∑ i : Fin N, K * Real.sqrt (n : ℝ) * (α i * (∫ θ in (F.arc i).lo..(F.arc i).hi, K4i n θ θ0)) := by
                            apply Finset.sum_congr rfl
                            intro i hi
                            ring
                    _ = K * Real.sqrt (n : ℝ) * (∑ i : Fin N, α i * (∫ θ in (F.arc i).lo..(F.arc i).hi, K4i n θ θ0)) := by
                            rw [Finset.mul_sum]
              exact hpull
    _ = K * Real.sqrt (n : ℝ) *
        (∑ i : Fin N, α i * (∫ θ in (F.arc i).lo..(F.arc i).hi, ker4 n θ θ0)) := by
        congr 1
        apply Finset.sum_congr rfl
        intro i hi
        apply congrArg (fun t : ℝ => α i * t)
        apply intervalIntegral.integral_congr
        intro θ hθ
        exact K4i_eq_ker4 n θ θ0



/-! ============= shifted periodic lemma ============= -/

/-- monotone version with phase-shifted kernel `sin(2n(θ−θ0))` -/
lemma monotone_sin_shifted (n : ℕ) (hn : 1 ≤ n) (a b θ0 : ℝ) (hab : a ≤ b)
    (h : ℝ → ℝ) (hcont : ContinuousOn h (Set.Icc a b))
    (hmono : ∀ (x y : ℝ), x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y → h x ≤ h y)
    (hmul : ∃ m : ℕ, b - a = (m : ℝ) * Real.pi / n) :
    |∫ θ in a..b, h θ * Real.sin (2 * (n : ℝ) * (θ - θ0))| ≤ |h b - h a| / n := by
  let f : ℝ → ℝ := fun u => h (u + θ0) * Real.sin (2 * (n : ℝ) * u)
  have hT : (∫ x in a..b, f (x - θ0)) = ∫ u in (a - θ0)..(b - θ0), f u := by
    simpa [f, sub_eq_add_neg] using
      (intervalIntegral.integral_comp_add_right (f := f) (-θ0))
  have hsub : (∫ θ in a..b, h θ * Real.sin (2 * (n : ℝ) * (θ - θ0)))
      = ∫ u in (a - θ0)..(b - θ0), f u := by
    rw [← hT]
    apply intervalIntegral.integral_congr
    intro θ hθ
    dsimp [f]
    ring_nf
  have hab' : a - θ0 ≤ b - θ0 := by linarith
  have hmul' : ∃ m : ℕ, (b - θ0) - (a - θ0) = (m : ℝ) * Real.pi / n := by
    rcases hmul with ⟨m, hm⟩
    refine ⟨m, ?_⟩
    linarith
  have hcont' : ContinuousOn (fun u : ℝ => h (u + θ0)) (Set.Icc (a - θ0) (b - θ0)) := by
    have htrans : ContinuousOn (fun u : ℝ => u + θ0) (Set.Icc (a - θ0) (b - θ0)) := by
      fun_prop
    have hmap : Set.MapsTo (fun u : ℝ => u + θ0) (Set.Icc (a - θ0) (b - θ0)) (Set.Icc a b) := by
      intro x hx
      constructor <;> linarith [hx.1, hx.2]
    have hc := hcont.comp htrans hmap
    simpa [Function.comp_def] using hc
  have hmono' : ∀ (x y : ℝ), x ∈ Set.Icc (a - θ0) (b - θ0) → y ∈ Set.Icc (a - θ0) (b - θ0) →
      x ≤ y → h (x + θ0) ≤ h (y + θ0) := by
    intro x y hx hy hxy
    have hx1 : x + θ0 ∈ Set.Icc a b := by constructor <;> linarith [hx.1, hx.2]
    have hy1 : y + θ0 ∈ Set.Icc a b := by constructor <;> linarith [hy.1, hy.2]
    exact hmono (x + θ0) (y + θ0) hx1 hy1 (by linarith)
  have hbnd := Periodic.monotone_sin_integral_bound n hn hab' (fun u : ℝ => h (u + θ0))
    hcont' hmono' hmul'
  rw [hsub]
  simpa [f] using hbnd

/-- antitone version with phase-shifted kernel `sin(2n(θ−θ0))` -/
lemma antitone_sin_shifted (n : ℕ) (hn : 1 ≤ n) (a b θ0 : ℝ) (hab : a ≤ b)
    (h : ℝ → ℝ) (hcont : ContinuousOn h (Set.Icc a b))
    (hanti : ∀ (x y : ℝ), x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y → h y ≤ h x)
    (hmul : ∃ m : ℕ, b - a = (m : ℝ) * Real.pi / n) :
    |∫ θ in a..b, h θ * Real.sin (2 * (n : ℝ) * (θ - θ0))| ≤ |h b - h a| / n := by
  have hmono_neg : ∀ (x y : ℝ), x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y →
      (-h) x ≤ (-h) y := by
    intro x y hx hy hxy
    exact neg_le_neg (hanti x y hx hy hxy)
  have hbnd := monotone_sin_shifted n hn a b θ0 hab (fun θ : ℝ => -h θ) hcont.neg hmono_neg hmul
  have hrew2 : (∫ θ in a..b, (-h θ) * Real.sin (2 * (n : ℝ) * (θ - θ0)))
      = - (∫ θ in a..b, h θ * Real.sin (2 * (n : ℝ) * (θ - θ0))) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro θ hθ
    ring
  calc
    |∫ θ in a..b, h θ * Real.sin (2 * (n : ℝ) * (θ - θ0))|
        = |∫ θ in a..b, (-h θ) * Real.sin (2 * (n : ℝ) * (θ - θ0))| := by
          rw [hrew2, abs_neg]
    _ ≤ |((-h) b) - ((-h) a)| / n := hbnd
    _ = |h b - h a| / n := by
          have hneg : ((-h) b) - ((-h) a) = -(h b - h a) := by
            simp [Pi.neg_apply]
            ring
          rw [hneg, abs_neg]




/-! ============= Claim 2: replace Dir1 by the linear kernel ============= -/

/-- `Hf` is continuous and monotone on `[−π/2,π/2]` (from S5H). -/
lemma Hf_contMono :
    ContinuousOn Hf (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) ∧
      MonotoneOn Hf (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) := by
  exact S5H.H_contMono

/-- `DK1` expressed with division -/
lemma DK1_eq_div (n : ℕ) (hn1 : 1 ≤ n) {θ0 θ : ℝ} (h : θ ≠ θ0)
    (hu : |θ - θ0| < Real.pi / 2) :
    DK1 n θ0 θ = Real.sin (2 * (n : ℝ) * (θ - θ0)) / Real.sin (θ - θ0) := by
  have hpi : 0 < Real.pi := Real.pi_pos
  have hu0 : θ - θ0 ≠ 0 := by intro hh; apply h; linarith
  have hn0 : (2 * (n : ℝ)) ≠ 0 := by
    have : 0 < (n : ℝ) := by exact_mod_cast hn1
    positivity
  have h2nu : 2 * (n : ℝ) * (θ - θ0) ≠ 0 := mul_ne_zero hn0 hu0
  have hsinu : Real.sin (θ - θ0) ≠ 0 := sin_ne_zero_of_abs_lt_pi hu0 (by linarith [hpi])
  unfold DK1
  rw [Real.sinc_of_ne_zero h2nu]
  rw [Real.sinc_of_ne_zero hu0]
  field_simp [hsinu, hu0, h2nu, hn0]

/-- `LK` expressed with division -/
lemma LK_eq_div (n : ℕ) (hn1 : 1 ≤ n) {θ0 θ : ℝ} (h : θ ≠ θ0) :
    LK n θ0 θ = Real.sin (2 * (n : ℝ) * (θ - θ0)) / (θ - θ0) := by
  have hu0 : θ - θ0 ≠ 0 := by intro hh; apply h; linarith
  have hn0 : (2 * (n : ℝ)) ≠ 0 := by
    have : 0 < (n : ℝ) := by exact_mod_cast hn1
    positivity
  have h2nu : 2 * (n : ℝ) * (θ - θ0) ≠ 0 := mul_ne_zero hn0 hu0
  unfold LK
  rw [Real.sinc_of_ne_zero h2nu]
  field_simp [hu0, h2nu, hn0]

/-- pointwise identity `DK1 − LK = sin(2n u)·Hf(u)` for `u = θ−θ0` on arcs -/
lemma dk1_sub_lk (n : ℕ) (hn1 : 1 ≤ n) {θ0 θ : ℝ} (h : θ ≠ θ0) (hu : |θ - θ0| < Real.pi / 2) :
    DK1 n θ0 θ - LK n θ0 θ =
      Real.sin (2 * (n : ℝ) * (θ - θ0)) * Hf (θ - θ0) := by
  rw [DK1_eq_div n hn1 h hu, LK_eq_div n hn1 h]
  unfold Hf S5H.H
  ring

/-- per-arc bound: `|A_i − C_i| ≤ |Hf(hi−θ0) − Hf(lo−θ0)|/n` -/
lemma arc_DK1_LK_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    |(∫ θ in (F.arc i).lo..(F.arc i).hi, DK1 n θ0 θ)
        - (∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ)|
      ≤ |Hf ((F.arc i).hi - θ0) - Hf ((F.arc i).lo - θ0)| / n := by
  have hab : (F.arc i).lo ≤ (F.arc i).hi := (arc_lo_lt_hi hn16 F i).le
  have hc1 : ContinuousOn (DK1 n θ0) (Set.Icc (F.arc i).lo (F.arc i).hi) := by
    unfold DK1
    apply ContinuousOn.div
    · apply ContinuousOn.mul
      · exact continuousOn_const
      · exact (Real.continuous_sinc.comp (continuous_const.mul (Continuous.sub continuous_id continuous_const))).continuousOn
    · exact (Real.continuous_sinc.comp (Continuous.sub continuous_id continuous_const)).continuousOn
    · intro x hx
      exact sinc_ne_zero_of_abs_le_pi_div_two (by
        rcases arc_theta_domain hn16 F i hθ0a hθ0b hx with ⟨_, _, hu, _⟩
        exact hu.le)
  have hcL : ContinuousOn (LK n θ0) (Set.Icc (F.arc i).lo (F.arc i).hi) := by
    unfold LK
    have hc_sinc : ContinuousOn (fun θ : ℝ => Real.sinc (2 * (n : ℝ) * (θ - θ0)))
        (Set.Icc (F.arc i).lo (F.arc i).hi) :=
      (Real.continuous_sinc.comp (continuous_const.mul (Continuous.sub continuous_id continuous_const))).continuousOn
    exact ContinuousOn.mul continuousOn_const hc_sinc
  have hi1 : IntervalIntegrable (DK1 n θ0) volume (F.arc i).lo (F.arc i).hi :=
    ContinuousOn.intervalIntegrable_of_Icc hab hc1
  have hiL : IntervalIntegrable (LK n θ0) volume (F.arc i).lo (F.arc i).hi :=
    ContinuousOn.intervalIntegrable_of_Icc hab hcL
  have hAC : (∫ θ in (F.arc i).lo..(F.arc i).hi, DK1 n θ0 θ)
        - (∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ)
      = ∫ θ in (F.arc i).lo..(F.arc i).hi, (DK1 n θ0 θ - LK n θ0 θ) := by
    rw [intervalIntegral.integral_sub hi1 hiL]
  have hinteq : (∫ θ in (F.arc i).lo..(F.arc i).hi, (DK1 n θ0 θ - LK n θ0 θ))
      = ∫ θ in (F.arc i).lo..(F.arc i).hi,
          Hf (θ - θ0) * Real.sin (2 * (n : ℝ) * (θ - θ0)) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    change DK1 n θ0 θ - LK n θ0 θ = Hf (θ - θ0) * Real.sin (2 * (n : ℝ) * (θ - θ0))
    by_cases hθeq : θ = θ0
    · subst θ
      simp [DK1, LK, Hf]
    · have hmem : θ ∈ Set.Icc (F.arc i).lo (F.arc i).hi := by
        rw [Set.uIcc_of_le hab] at hθ
        exact hθ
      rcases arc_theta_domain hn16 F i hθ0a hθ0b hmem with ⟨_, _, hu, _⟩
      rw [dk1_sub_lk n (n_ge_one hn16) hθeq hu]
      ring
  rw [hAC, hinteq]
  rcases arc_len_multiple hn16 F i with ⟨m, hm6, hm⟩
  have hbnd := monotone_sin_shifted n (n_ge_one hn16) (F.arc i).lo (F.arc i).hi θ0 hab
    (fun θ : ℝ => Hf (θ - θ0)) ?hcont ?hmono ⟨m, hm⟩
  · simpa using hbnd
  · have hcont0 : ContinuousOn Hf (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :=
      (Hf_contMono).1
    have htrans : ContinuousOn (fun θ : ℝ => θ - θ0) (Set.Icc (F.arc i).lo (F.arc i).hi) := by
      fun_prop
    have hmap : Set.MapsTo (fun θ : ℝ => θ - θ0) (Set.Icc (F.arc i).lo (F.arc i).hi)
        (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) := by
      intro x hx
      rcases arc_theta_domain hn16 F i hθ0a hθ0b hx with ⟨_, _, hu, _⟩
      rw [Set.mem_Icc]
      constructor <;> linarith [(abs_lt.mp hu).1, (abs_lt.mp hu).2]
    have hc := hcont0.comp htrans hmap
    simpa [Function.comp_def] using hc
  · have hmonoH : MonotoneOn Hf (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) := (Hf_contMono).2
    intro x y hx hy hxy
    have hx0 : x - θ0 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      rcases arc_theta_domain hn16 F i hθ0a hθ0b hx with ⟨_, _, hu, _⟩
      rw [Set.mem_Icc]
      constructor <;> linarith [(abs_lt.mp hu).1, (abs_lt.mp hu).2]
    have hy0 : y - θ0 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      rcases arc_theta_domain hn16 F i hθ0a hθ0b hy with ⟨_, _, hu, _⟩
      rw [Set.mem_Icc]
      constructor <;> linarith [(abs_lt.mp hu).1, (abs_lt.mp hu).2]
    exact hmonoH hx0 hy0 (by linarith)


/-- value of Hf at π/2 -/
lemma Hf_pi_div_two : Hf (Real.pi / 2) = 1 - 2 / Real.pi := by
  simpa [Hf] using S5H.H_pi_div_two

/-- value of Hf at -π/2 -/
lemma Hf_neg_pi_div_two : Hf (-(Real.pi / 2)) = -(1 - 2 / Real.pi) := by
  simpa [Hf] using S5H.H_neg_pi_div_two

/-- two-point oscillation bound: u ≤ x ≤ y ≤ v implies Hf(y)−Hf(x) ≤ Hf(v)−Hf(u) -/
lemma Hf_osc_le {u v : ℝ} (hu : u ≤ v) (huv : u ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
    (hvv : v ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2))
    {x y : ℝ} (hx : x ∈ Set.Icc u v) (hy : y ∈ Set.Icc u v) (hxy : x ≤ y) :
    Hf y - Hf x ≤ Hf v - Hf u := by
  have hmono : MonotoneOn Hf (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) := (Hf_contMono).2
  have hsub : Set.Icc u v ⊆ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
    intro z hz
    constructor <;> linarith [hu, huv.1, huv.2, hvv.1, hvv.2, hz.1, hz.2]
  have hx' : x ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := hsub hx
  have hy' : y ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := hsub hy
  have hux : Hf u ≤ Hf x := hmono huv hx' (by linarith [hx.1])
  have hvy : Hf y ≤ Hf v := hmono hy' hvv (by linarith [hy.2])
  have hxy' : Hf x ≤ Hf y := hmono hx' hy' hxy
  linarith

/-- Claim 2: `Σ_i |A_i − C_i| ≤ 1/50` -/
lemma claim2_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    (∑ i : Fin N, |(∫ θ in (F.arc i).lo..(F.arc i).hi, DK1 n θ0 θ)
        - (∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ)|) ≤ 1 / 50 := by
  -- telescoping bound over all arcs inside [qA, qB]
  have hqA0 : qA n ≤ qB n := (qB_bounds hn16).1.le
  have hmonoH : MonotoneOn Hf (Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) := (Hf_contMono).2
  have hmonoShift : MonotoneOn (fun θ : ℝ => Hf (θ - θ0)) (Set.Icc (qA n) (qB n)) := by
    intro x hx y hy hxy
    have hx0 : x - θ0 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      rw [Set.mem_Icc]
      constructor <;> linarith [hx.1, hx.2, qA_lt_pi_div_four hn16 |>.le, qB_bounds hn16 |>.1.le, qB_bounds hn16 |>.2.2, hθ0a, hθ0b, qA_pos hn16]
    have hy0 : y - θ0 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      rw [Set.mem_Icc]
      constructor <;> linarith [hy.1, hy.2, qA_lt_pi_div_four hn16 |>.le, qB_bounds hn16 |>.1.le, qB_bounds hn16 |>.2.2, hθ0a, hθ0b, qA_pos hn16]
    exact hmonoH hx0 hy0 (by linarith)
  have htele : (∑ i : Fin N, |Hf ((F.arc i).hi - θ0) - Hf ((F.arc i).lo - θ0)|)
      ≤ |Hf (qB n - θ0) - Hf (qA n - θ0)| := by
    have hh := S5Tele.sum_var_le_mono (s := Finset.univ) (lo := fun i : Fin N => (F.arc i).lo)
      (hi := fun i : Fin N => (F.arc i).hi) (A := qA n) (B := qB n) hqA0
      (hA := fun i hi => arc_lo_ge_qA hn16 F i)
      (hB := fun i hi => arc_hi_le_qB hn16 F i)
      (hle := fun i hi => Family.Grid.lo_le_hi (F.arc i))
      (hsep := fun i hi j hj hij =>
        (arc_sep hn16 F hij).elim
          (fun hlt => Or.inl (le_of_lt hlt))
          (fun hlt => Or.inr (le_of_lt hlt)))
      (h := fun θ : ℝ => Hf (θ - θ0)) hmonoShift
    simpa using hh
  have hosc : |Hf (qB n - θ0) - Hf (qA n - θ0)| ≤ 2 * (1 - 2 / Real.pi) := by
    have hu : qA n - θ0 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      rw [Set.mem_Icc]
      constructor <;> linarith [qA_lt_pi_div_four hn16 |>.le, qB_bounds hn16 |>.1.le, qB_bounds hn16 |>.2.2, hθ0a, hθ0b, qA_pos hn16]
    have hv : qB n - θ0 ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2) := by
      rw [Set.mem_Icc]
      constructor <;> linarith [qA_lt_pi_div_four hn16 |>.le, qB_bounds hn16 |>.1.le, qB_bounds hn16 |>.2.2, hθ0a, hθ0b, qA_pos hn16]
    have hle1 : Hf (qA n - θ0) ≤ Hf (qB n - θ0) := hmonoH hu hv (by linarith [qB_bounds hn16 |>.1.le])
    have hb1 : Hf (qB n - θ0) ≤ Hf (Real.pi / 2) := hmonoH hv
      (by rw [Set.mem_Icc]; constructor <;> linarith [Real.pi_pos]) (by linarith [hθ0b, qB_bounds hn16 |>.2.2])
    have ha1 : Hf (-(Real.pi / 2)) ≤ Hf (qA n - θ0) := hmonoH
      (by rw [Set.mem_Icc]; constructor <;> linarith [Real.pi_pos]) hu (by linarith [hθ0a, qA_pos hn16])
    rw [abs_of_nonneg (sub_nonneg.mpr hle1)]
    have hval : Hf (Real.pi / 2) - Hf (-(Real.pi / 2)) = 2 * (1 - 2 / Real.pi) := by
      rw [Hf_pi_div_two, Hf_neg_pi_div_two]
      ring
    linarith
  have hper : (1 / n) * (2 * (1 - 2 / Real.pi)) ≤ 1 / 50 := by
    have hnpos : 0 < (n : ℝ) := nR_pos hn16
    have hbig : (100 : ℝ) ≤ (n : ℝ) := by
      have h' : (2 ^ 16 : ℝ) ≤ (n : ℝ) := nR_ge_pow hn16
      norm_num at h' ⊢
      linarith
    have h2pi : 2 * (1 - 2 / Real.pi) ≤ 2 := by
      have h2p : (0 : ℝ) ≤ 2 / Real.pi := by positivity
      nlinarith
    calc
      (1 / n) * (2 * (1 - 2 / Real.pi)) ≤ (1 / n) * 2 := by
            exact mul_le_mul_of_nonneg_left h2pi (by positivity)
      _ = 2 / n := by ring
      _ ≤ 1 / 50 := by
            rw [div_le_div_iff₀ hnpos (by norm_num : (0:ℝ) < 50)]
            nlinarith
  calc
    (∑ i : Fin N, |(∫ θ in (F.arc i).lo..(F.arc i).hi, DK1 n θ0 θ)
        - (∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ)|)
        ≤ ∑ i : Fin N, (|Hf ((F.arc i).hi - θ0) - Hf ((F.arc i).lo - θ0)| / n) := by
            apply Finset.sum_le_sum
            intro i hi
            exact arc_DK1_LK_bound n N hn16 F i hθ0a hθ0b
    _ = (1 / n) * (∑ i : Fin N,
        |Hf ((F.arc i).hi - θ0) - Hf ((F.arc i).lo - θ0)|) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i hi
            ring
    _ ≤ (1 / n) * |Hf (qB n - θ0) - Hf (qA n - θ0)| := by
            exact mul_le_mul_of_nonneg_left htele (by positivity)
    _ ≤ (1 / n) * (2 * (1 - 2 / Real.pi)) := by
            exact mul_le_mul_of_nonneg_left hosc (by positivity)
    _ ≤ 1 / 50 := hper




/-! ============= Claim 3: far intervals sum ≤ 2/π ============= -/

/-- if an arc exists then n ≠ 0 -/
lemma n_ne_zero_of_arc {n N : ℕ} (F : Family.Quad n N) (i : Fin N) : n ≠ 0 := by
  intro hn0
  have hfar : 2 * (F.arc i).q + 200 ≤ (0 : ℤ) := by subst n; exact F.far_right i
  have hp : 100 ≤ (F.arc i).p := F.far_left i
  have hlt : (F.arc i).p < (F.arc i).q := (F.arc i).hlt
  omega

/-- `1/t` reverses on positives: `0 < a ≤ b ⇒ 1/b ≤ 1/a` -/
lemma inv_rev_of_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : (1 / b) ≤ 1 / a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  rw [div_le_div_iff₀ hb ha]
  simpa using hab

/-- pointwise `LK = (1/(θ−θ0))·sin(2n(θ−θ0))` for θ ≠ θ0 -/
lemma LK_eq_inv (n : ℕ) {θ0 θ : ℝ} (h : θ ≠ θ0) :
    LK n θ0 θ = (1 / (θ - θ0)) * Real.sin (2 * (n : ℝ) * (θ - θ0)) := by
  have hu0 : θ - θ0 ≠ 0 := by intro hh; apply h; linarith
  by_cases hn : n = 0
  · subst n
    simp [LK]
  · have hn0 : (2 * (n : ℝ)) ≠ 0 := by
      have : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn)
      positivity
    have h2nu : 2 * (n : ℝ) * (θ - θ0) ≠ 0 := mul_ne_zero hn0 hu0
    unfold LK
    rw [Real.sinc_of_ne_zero h2nu]
    field_simp [hu0]

/-- antitone of `1/(θ−θ0)` on a far arc (either side) -/
lemma inv_sub_anti (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N)
    {θ0 : ℝ}
    (hfar : (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ) ∨ θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo) :
    ∀ (x y : ℝ), x ∈ Set.Icc (F.arc i).lo (F.arc i).hi → y ∈ Set.Icc (F.arc i).lo (F.arc i).hi →
      x ≤ y → 1 / (y - θ0) ≤ 1 / (x - θ0) := by
  intro x y hx hy hxy
  rcases hfar with hleft | hright
  · have hyv : y < θ0 := by
      have : y ≤ θ0 - Real.pi / (n : ℝ) := le_trans hy.2 hleft
      have hpos : 0 < Real.pi / (n : ℝ) := by
        have hn0 : n ≠ 0 := n_ne_zero_of_arc F i
        have : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
        positivity
      linarith
    have hyx : 1 / (y - θ0) ≤ 1 / (x - θ0) := by
      have hyz : y - θ0 ≠ 0 := by linarith
      have hxz : x - θ0 ≠ 0 := by linarith
      have hfrac : 1 / (y - θ0) - 1 / (x - θ0) = (x - y) / ((y - θ0) * (x - θ0)) := by
        field_simp [hyz, hxz]
        ring
      have hden : 0 < (y - θ0) * (x - θ0) := mul_pos_of_neg_of_neg (by linarith) (by linarith)
      have hle0 : 1 / (y - θ0) - 1 / (x - θ0) ≤ 0 := by
        rw [hfrac]
        exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
      linarith
    exact hyx
  · have hxpos : 0 < x - θ0 := by
      have : θ0 + Real.pi / (n : ℝ) ≤ x := le_trans hright hx.1
      have hpos : 0 < Real.pi / (n : ℝ) := by
        have hn0 : n ≠ 0 := n_ne_zero_of_arc F i
        have : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
        positivity
      linarith
    have hab : x - θ0 ≤ y - θ0 := by linarith
    exact inv_rev_of_pos hxpos hab

/-- per-arc bound for a far arc -/
lemma arc_LK_far_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2)
    (hfar : (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ) ∨ θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo) :
    |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|
      ≤ |1 / ((F.arc i).hi - θ0) - 1 / ((F.arc i).lo - θ0)| / n := by
  have hab : (F.arc i).lo ≤ (F.arc i).hi := (arc_lo_lt_hi hn16 F i).le
  have hθne : ∀ θ ∈ Set.Icc (F.arc i).lo (F.arc i).hi, θ ≠ θ0 := by
    intro θ hθ heq
    rcases hfar with hleft | hright
    · have : θ ≤ θ0 - Real.pi / (n : ℝ) := le_trans hθ.2 hleft
      have hpos : 0 < Real.pi / (n : ℝ) := by
        have hn0 : n ≠ 0 := n_ne_zero_of_arc F i
        have : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
        positivity
      linarith
    · have : θ0 + Real.pi / (n : ℝ) ≤ θ := le_trans hright hθ.1
      have hpos : 0 < Real.pi / (n : ℝ) := by
        have hn0 : n ≠ 0 := n_ne_zero_of_arc F i
        have : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
        positivity
      linarith
  have hinteq : (∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ)
      = ∫ θ in (F.arc i).lo..(F.arc i).hi,
          (1 / (θ - θ0)) * Real.sin (2 * (n : ℝ) * (θ - θ0)) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    change LK n θ0 θ = (1 / (θ - θ0)) * Real.sin (2 * (n : ℝ) * (θ - θ0))
    have hmem : θ ∈ Set.Icc (F.arc i).lo (F.arc i).hi := by
        rw [Set.uIcc_of_le hab] at hθ
        exact hθ
    exact LK_eq_inv n (hθne θ hmem)
  rw [hinteq]
  rcases arc_len_multiple hn16 F i with ⟨m, hm6, hm⟩
  have hbnd := antitone_sin_shifted n (n_ge_one hn16) (F.arc i).lo (F.arc i).hi θ0 hab
    (fun θ : ℝ => 1 / (θ - θ0)) ?hcont ?hanti ⟨m, hm⟩
  · simpa using hbnd
  · have htrans : ContinuousOn (fun θ : ℝ => θ - θ0) (Set.Icc (F.arc i).lo (F.arc i).hi) := by
      fun_prop
    have hne : ∀ x ∈ Set.Icc (F.arc i).lo (F.arc i).hi, (fun θ : ℝ => θ - θ0) x ≠ 0 := by
      intro x hx
      exact sub_ne_zero.mpr (hθne x hx)
    exact (continuousOn_const.div htrans hne)
  · exact inv_sub_anti n N hn16 F i hfar



/-! ============= Claim 1: Σ |Dir2-arc integrals| ≤ 1/50 ============= -/

/-- monotone sin on [0, π/2] -/
lemma sin_mono_on_left : MonotoneOn Real.sin (Set.Icc 0 (Real.pi / 2)) := by
  exact Real.monotoneOn_sin.mono (by intro x hx; constructor <;> linarith [hx.1, hx.2])

/-- sin(π − x) = sin x -/
lemma sin_pi_sub_eq (x : ℝ) : Real.sin (Real.pi - x) = Real.sin x := by
  rw [Real.sin_sub]
  simp

/-- `sin(θ+θ0) ≥ sin(100π/n) > 0` on quadrant arcs -/
lemma arc_sin_sum_lower (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N)
    {θ0 θ : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2)
    (hθ : θ ∈ Set.Icc (F.arc i).lo (F.arc i).hi) :
    Real.sin (qA n) ≤ Real.sin (θ + θ0) := by
  have hinc : MonotoneOn Real.sin (Set.Icc 0 (Real.pi / 2)) := sin_mono_on_left
  have hqA0 : 0 ≤ qA n := (qA_pos hn16).le
  have hqA2 : qA n ≤ Real.pi / 2 := qA_le_pi_div_two hn16
  have hmem_qA : qA n ∈ Set.Icc 0 (Real.pi / 2) := ⟨hqA0, hqA2⟩
  have hθ1 : qA n ≤ θ := le_trans (arc_lo_ge_qA hn16 F i) hθ.1
  have hθ2 : θ ≤ qB n := le_trans hθ.2 (arc_hi_le_qB hn16 F i)
  by_cases hm : θ + θ0 ≤ Real.pi / 2
  · have hle : qA n ≤ θ + θ0 := by linarith
    have hmem2 : θ + θ0 ∈ Set.Icc 0 (Real.pi / 2) := by
      constructor <;> linarith [hθ0a, hθ1]
    exact hinc hmem_qA hmem2 hle
  · -- θ+θ0 ∈ (π/2, π): use symmetry
    have ht_lt : θ + θ0 < Real.pi := by
      have hb : qB n < Real.pi / 2 := (qB_bounds hn16).2.2
      have : θ + θ0 ≤ qB n + θ0 := by linarith
      linarith [hb, hθ0b]
    have hsum_le : θ + θ0 ≤ Real.pi - qA n := by
      rw [qB_eq] at hθ2
      linarith [hθ0b]
    let t : ℝ := θ + θ0
    have ht1 : Real.pi - t ≤ Real.pi / 2 := by
      dsimp [t]
      linarith
    have ht0 : 0 ≤ Real.pi - t := by
      dsimp [t]
      linarith
    have hle2 : qA n ≤ Real.pi - t := by
      dsimp [t]
      linarith
    have hmem2 : Real.pi - t ∈ Set.Icc 0 (Real.pi / 2) := ⟨ht0, ht1⟩
    have hmain : Real.sin (qA n) ≤ Real.sin (Real.pi - t) := hinc hmem_qA hmem2 hle2
    have hsym : Real.sin (Real.pi - t) = Real.sin t := sin_pi_sub_eq t
    dsimp [t] at hsym
    linarith

/-- `1/sin(θ+θ0) ≤ 1/sin(qA)` and `sin(θ+θ0) > 0` on arcs -/
lemma arc_sin_inv_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N)
    {θ0 θ : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2)
    (hθ : θ ∈ Set.Icc (F.arc i).lo (F.arc i).hi) :
    1 / Real.sin (θ + θ0) ≤ 1 / Real.sin (qA n) ∧ 0 < Real.sin (θ + θ0) := by
  have hpos : 0 < Real.sin (qA n) := by
    have hq : 0 < qA n := qA_pos hn16
    have hq2 : qA n < Real.pi / 2 := lt_trans (qA_lt_pi_div_four hn16) (by linarith [Real.pi_pos])
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hq]) (by linarith [hq2, Real.pi_pos])
  have hs : Real.sin (qA n) ≤ Real.sin (θ + θ0) := arc_sin_sum_lower n N hn16 F i hθ0a hθ0b hθ
  have hst : 0 < Real.sin (θ + θ0) := lt_of_lt_of_le hpos hs
  constructor
  · exact inv_rev_of_pos hpos hs
  · exact hst


/-- at most one arc contains any given point -/
lemma one_arc_contains {n N : ℕ} (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    (c : ℝ) : ∀ i j : Fin N, c ∈ Set.Icc (F.arc i).lo (F.arc i).hi →
      c ∈ Set.Icc (F.arc j).lo (F.arc j).hi → i = j := by
  intro i j hi hj
  by_contra hij
  rcases arc_sep hn16 F hij with hlt | hlt
  · have : (F.arc i).hi < c := lt_of_lt_of_le hlt hj.1
    exact (not_lt_of_ge hi.2) this
  · have : (F.arc j).hi < c := lt_of_lt_of_le hlt hi.1
    exact (not_lt_of_ge hj.2) this


/-! ============= Lemma si consumption ============= -/


/-! ============= Assembly ============= -/

/-- per-arc C and the T-sums -/
def arcC (n : ℕ) (θ0 : ℝ) (a b : ℝ) : ℝ := ∫ θ in a..b, LK n θ0 θ

/-- `T(θ0) = Σ_i α_i ∫_{I_i} ker4` -/
def Tθ (n N : ℕ) (F : Family.Quad n N) (α : Fin N → ℝ) (θ0 : ℝ) : ℝ :=
  ∑ i : Fin N, α i * (∫ θ in (F.arc i).lo..(F.arc i).hi, ker4 n θ θ0)

/-- sHat = K√n·T -/
lemma sHat_eq_T (n N : ℕ) (K : ℝ) (F : Family.Quad n N) (α : Fin N → ℝ) (θ0 : ℝ) :
    sHat n N K F α θ0 = K * Real.sqrt (n : ℝ) * Tθ n N F α θ0 := by
  rw [Tθ, sHat_eq_sum_arcs]

/-- T(θ0) = Σ_i α_i(∫ DK1 − ∫ DK2) over the arcs (θ0 in quadrant) -/
lemma Tθ_eq_sum (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (α : Fin N → ℝ)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    Tθ n N F α θ0 =
      ∑ i : Fin N, α i * ((∫ θ in (F.arc i).lo..(F.arc i).hi, DK1 n θ0 θ)
        - (∫ θ in (F.arc i).lo..(F.arc i).hi, DK2 n θ0 θ)) := by
  unfold Tθ
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  exact arc_integral_ker n N hn16 F i hθ0a hθ0b

/-- identity `A − B = C + (A − C) − B` used to split T -/
lemma arc_split (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    (∫ θ in (F.arc i).lo..(F.arc i).hi, DK1 n θ0 θ)
      - (∫ θ in (F.arc i).lo..(F.arc i).hi, DK2 n θ0 θ)
      = arcC n θ0 (F.arc i).lo (F.arc i).hi
        + ((∫ θ in (F.arc i).lo..(F.arc i).hi, DK1 n θ0 θ)
            - (∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ))
        - (∫ θ in (F.arc i).lo..(F.arc i).hi, DK2 n θ0 θ) := by
  unfold arcC
  ring


/-! ======= geometry for near/far ======= -/

/-- θ0 ∈ arc i0 ⇒ other arcs are far (distance ≥ π/n) -/
lemma erase_mem_far (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i0 : Fin N)
    {θ0 : ℝ} (hmem : θ0 ∈ Set.Icc (F.arc i0).lo (F.arc i0).hi) :
    ∀ i ∈ (Finset.univ.erase i0),
      (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ) ∨ θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo := by
  intro i hi
  have hine : i ≠ i0 := (Finset.mem_erase.mp hi).1
  rcases arc_left_or_right hn16 F i0 i hine with hlt | hlt
  · left
    -- hi_i ≤ lo_{i0} − π/n ≤ θ0 − π/n
    have h1 : (F.arc i).hi ≤ (F.arc i0).lo - Real.pi / (n : ℝ) := hlt
    linarith [hmem.1]
  · right
    -- θ0 + π/n ≤ hi_{i0} + π/n ≤ lo_i
    have h1 : (F.arc i0).hi + Real.pi / (n : ℝ) ≤ (F.arc i).lo := hlt
    linarith [hmem.2]

/-- θ0 ∈ arc i0 ⇒ i0 is not far on either side -/
lemma i0_near (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i0 : Fin N)
    {θ0 : ℝ} (hmem : θ0 ∈ Set.Icc (F.arc i0).lo (F.arc i0).hi) :
    ¬ (F.arc i0).hi ≤ θ0 - Real.pi / (n : ℝ) ∧ ¬ θ0 + Real.pi / (n : ℝ) ≤ (F.arc i0).lo := by
  have hpi : 0 < Real.pi / (n : ℝ) := by
    have hn0 : n ≠ 0 := n_ne_zero_of_arc F i0
    have : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
    positivity
  constructor
  · intro h
    have : θ0 ≤ θ0 - Real.pi / (n : ℝ) := le_trans hmem.2 h
    linarith
  · intro h
    have : θ0 + Real.pi / (n : ℝ) ≤ θ0 := le_trans h hmem.1
    linarith

/-- non-negativity of all the per-arc |·| quantities -/
lemma abs_arcC_nonneg (n N : ℕ) (θ0 : ℝ) (i : Fin N) (F : Family.Quad n N) :
    0 ≤ |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ| := abs_nonneg _

/-- colored coefficients have |α| = 1 -/
lemma coloring_abs {ι : Type*} {α : ι → ℝ} (hα : IsColoring α) (i : ι) : |α i| = 1 := by
  rcases hα i with h | h
  · rw [h, abs_one]
  · rw [h, abs_neg, abs_one]


/-! ======= wiring up Lemma si ======= -/

/-- `∫ LK` over `[a,b]` equals the `LinInt` of SiBounds (pointwise equality) -/
lemma arcC_eq_LinInt (n : ℕ) (a b θ0 : ℝ) :
    (∫ θ in a..b, LK n θ0 θ) = SiBounds.LinInt n a b θ0 := by
  unfold SiBounds.LinInt
  apply intervalIntegral.integral_congr
  intro θ hθ
  unfold LK
  by_cases h : θ - θ0 = 0
  · simp [h]
  · by_cases hn0 : n = 0
    · subst n
      simp [h]
    · have hnpos : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
      have h2n0 : (2 * (n : ℝ)) ≠ 0 := by positivity
      rw [Real.sinc_of_ne_zero (mul_ne_zero h2n0 h)]
      simp [h]
      field_simp [h]

/-- near interval containing θ0: lower bound -/
lemma si_in_lower {n N : ℕ} (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N)
    {θ0 : ℝ} (hmem : θ0 ∈ Set.Icc (F.arc i).lo (F.arc i).hi) :
    (4 / 3 : ℝ) ≤ ∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ := by
  rw [arcC_eq_LinInt]
  have hlen : (F.arc i).q - (F.arc i).p ≤ 6 := by
    simpa [Family.Grid.len] using F.len_le i
  have hq : (F.arc i).p < (F.arc i).q := (F.arc i).hlt
  exact SiBounds.si_inside_lower n (n_ge_one hn16) (F.arc i).p (F.arc i).q hq hlen θ0
    (by simpa [Family.Grid.lo] using hmem.1)
    (by simpa [Family.Grid.hi] using hmem.2)

/-- near interval containing θ0: upper bound -/
lemma si_in_upper {n N : ℕ} (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N)
    {θ0 : ℝ} (hmem : θ0 ∈ Set.Icc (F.arc i).lo (F.arc i).hi) :
    (∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ) ≤ 4 := by
  rw [arcC_eq_LinInt]
  have hlen : (F.arc i).q - (F.arc i).p ≤ 6 := by
    simpa [Family.Grid.len] using F.len_le i
  have hq : (F.arc i).p < (F.arc i).q := (F.arc i).hlt
  exact SiBounds.si_inside_upper n (n_ge_one hn16) (F.arc i).p (F.arc i).q hq hlen θ0
    (by simpa [Family.Grid.lo] using hmem.1)
    (by simpa [Family.Grid.hi] using hmem.2)

/-- interval not containing θ0: `|∫ LK| ≤ 2` -/
lemma si_out_abs {n N : ℕ} (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N)
    {θ0 : ℝ} (hout : θ0 ≤ (F.arc i).lo ∨ (F.arc i).hi ≤ θ0) :
    |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ| ≤ 2 := by
  rw [arcC_eq_LinInt]
  have hlen : (F.arc i).q - (F.arc i).p ≤ 6 := by
    simpa [Family.Grid.len] using F.len_le i
  have hq : (F.arc i).p < (F.arc i).q := (F.arc i).hlt
  have hlo : θ0 ≤ (F.arc i).p * Real.pi / (n : ℝ) ∨ (F.arc i).q * Real.pi / (n : ℝ) ≤ θ0 := by
    simpa [Family.Grid.lo, Family.Grid.hi] using hout
  change |SiBounds.LinInt n ((F.arc i).p * Real.pi / (n : ℝ)) ((F.arc i).q * Real.pi / (n : ℝ)) θ0| ≤ 2
  have hl := SiBounds.si_outside_lower n (n_ge_one hn16) (F.arc i).p (F.arc i).q hq hlen θ0 hlo
  have hu := SiBounds.si_outside_upper n (n_ge_one hn16) (F.arc i).p (F.arc i).q hq hlen θ0 hlo
  have h21 : (-2 : ℝ) ≤ -1 := by norm_num
  exact abs_le.mpr ⟨by linarith, hu⟩


end S5
end Submission

/-! The following three blocks (namespaces S5C1, S5C3L, S5C3R) were developed
in the companion files S5c1.lean, S5c3L.lean, S5c3R.lean and are reproduced
here so that this module is self-contained. -/

/- local `∑ x in s` notation (this mathlib revision only has `∑ x ∈ s`) -/
syntax "∑ " ident " in " term ", " term : term
macro_rules
  | `(∑ $x in $s, $b) => `(∑ $x ∈ $s, $b)

namespace Submission
namespace S5C1
/-- `c = π/2 − θ0`: the split point where `sin(θ+θ0)` is maximal. -/
def cVal (θ0 : ℝ) : ℝ := Real.pi / 2 - θ0

/-- `g(θ) = 1/sin(θ+θ0)`. -/
def gInv (θ0 : ℝ) (θ : ℝ) : ℝ := 1 / Real.sin (θ + θ0)

/-- value of `g` at the split point: `1/sin(π/2) = 1` -/
lemma gInv_c (θ0 : ℝ) : gInv θ0 (cVal θ0) = 1 := by
  unfold gInv cVal
  have harg : (Real.pi / 2 - θ0) + θ0 = Real.pi / 2 := by ring
  rw [harg, Real.sin_pi_div_two]
  norm_num

/-- `θ0` and quadrant endpoints lie in the quadrant -/
lemma theta0_quad {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    θ0 ∈ Set.Icc 0 (Real.pi / 2) := by
  exact ⟨hθ0a, hθ0b⟩

/-- `sin` is monotone increasing on `[0, π/2]` -/
lemma sin_mono_left : MonotoneOn Real.sin (Set.Icc 0 (Real.pi / 2)) :=
  S5.sin_mono_on_left

/-- `sin` is monotone decreasing on `[π/2, π]` -/
lemma sin_anti_right : AntitoneOn Real.sin (Set.Icc (Real.pi / 2) Real.pi) := by
  intro x hx y hy hxy
  have hx1 : 0 ≤ Real.pi - x := by linarith [hx.2]
  have hx2 : Real.pi - x ≤ Real.pi / 2 := by linarith [hx.1]
  have hy1 : 0 ≤ Real.pi - y := by linarith [hy.2]
  have hy2 : Real.pi - y ≤ Real.pi / 2 := by linarith [hy.1]
  have hle : Real.pi - y ≤ Real.pi - x := by linarith
  have hsin : Real.sin (Real.pi - y) ≤ Real.sin (Real.pi - x) := by
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hx2 hle
  simpa [Real.sin_pi_sub] using hsin

/-- `sin(θ+θ0) ≤ 1` -/
lemma sin_add_le_one (θ θ0 : ℝ) : Real.sin (θ + θ0) ≤ 1 := Real.sin_le_one _

/-- `g(qA) ≥ 0` (indeed > 0): `qA + θ0 ∈ (0, π)` -/
lemma gInv_qA_pos (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ} (hθ0a : 0 ≤ θ0)
    (hθ0b : θ0 ≤ Real.pi / 2) : 0 < gInv θ0 (S5.qA n) := by
  unfold gInv
  have h1 : 0 < S5.qA n + θ0 := by linarith [S5.qA_pos hn16]
  have h2 : S5.qA n + θ0 < Real.pi := by
    have hq : S5.qA n ≤ Real.pi / 4 := S5.qA_le_pi_div_four hn16
    linarith [hθ0b, Real.pi_pos]
  have hs : 0 < Real.sin (S5.qA n + θ0) := Real.sin_pos_of_pos_of_lt_pi h1 h2
  exact one_div_pos.mpr hs

/-- `g(qB) > 0`: `qB + θ0 ∈ (0, π)` -/
lemma gInv_qB_pos (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ} (hθ0a : 0 ≤ θ0)
    (hθ0b : θ0 ≤ Real.pi / 2) : 0 < gInv θ0 (S5.qB n) := by
  unfold gInv
  have h1 : 0 < S5.qB n + θ0 := by
    have hq : 0 < S5.qB n := (S5.qB_bounds hn16).2.1
    linarith
  have h2 : S5.qB n + θ0 < Real.pi := by
    have hq : S5.qB n < Real.pi / 2 := (S5.qB_bounds hn16).2.2
    linarith [hθ0b]
  have hs : 0 < Real.sin (S5.qB n + θ0) := Real.sin_pos_of_pos_of_lt_pi h1 h2
  exact one_div_pos.mpr hs

/-- `qA + θ0 ∈ (0, π/2]` when `qA ≤ c` -/
lemma qA_add_theta0_le_pi_div_two (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ}
    (hq : S5.qA n ≤ cVal θ0) : S5.qA n + θ0 ≤ Real.pi / 2 := by
  dsimp [cVal] at hq
  linarith

/-- `sin(qA + θ0) ≥ sin(qA)`, for `θ0 ∈ [0, π/2]`, `n ≥ 2^16` -/
lemma sin_qA_add_ge_sin_qA (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ}
    (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    Real.sin (S5.qA n) ≤ Real.sin (S5.qA n + θ0) := by
  let q : ℝ := S5.qA n
  have hq0 : 0 ≤ q := (S5.qA_pos hn16).le
  have hq4 : q ≤ Real.pi / 4 := S5.qA_le_pi_div_four hn16
  by_cases hm : q + θ0 ≤ Real.pi / 2
  · exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) hm (by linarith [hθ0a])
  · have hle_pi : q + θ0 < Real.pi := by linarith [hq4, hθ0b, Real.pi_pos]
    have hsym : Real.sin (q + θ0) = Real.sin (Real.pi - (q + θ0)) := by
      rw [Real.sin_pi_sub]
    rw [hsym]
    exact Real.sin_le_sin_of_le_of_le_pi_div_two
      (by linarith) (by linarith) (by nlinarith [hq4, hθ0b, hq0])

/-- `sin(qB + θ0) ≥ sin(qA)`, for `θ0 ∈ [0, π/2]`, `n ≥ 2^16` -/
lemma sin_qB_add_ge_sin_qA (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ}
    (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    Real.sin (S5.qA n) ≤ Real.sin (S5.qB n + θ0) := by
  let q : ℝ := S5.qA n
  have hq0 : 0 ≤ q := (S5.qA_pos hn16).le
  have hq4 : q ≤ Real.pi / 4 := S5.qA_le_pi_div_four hn16
  have hrew : S5.qB n + θ0 = (θ0 - q) + Real.pi / 2 := by
    dsimp [q]
    rw [S5.qB_eq]
    ring
  rw [hrew, Real.sin_add_pi_div_two]
  have hc2 : Real.cos (Real.pi / 2 - q) ≤ Real.cos (θ0 - q) := by
    by_cases hq : θ0 ≤ q
    · have hc1 : Real.cos (q - θ0) = Real.cos (θ0 - q) := by
        rw [show q - θ0 = -(θ0 - q) by ring]
        rw [Real.cos_neg]
      rw [← hc1]
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      · linarith
      · nlinarith [hq4, Real.pi_pos]
      · nlinarith [hq4, hθ0a]
    · apply Real.cos_le_cos_of_nonneg_of_le_pi
      · linarith
      · nlinarith [hq0, Real.pi_pos]
      · linarith [hθ0b]
  have hgoal : Real.sin q ≤ Real.cos (θ0 - q) := by
    simpa [Real.cos_pi_div_two_sub] using hc2
  dsimp [q] at hgoal
  exact hgoal

/-- `sin(qA) > 0` -/
lemma sin_qA_pos (n : ℕ) (hn16 : 2 ^ 16 ≤ n) : 0 < Real.sin (S5.qA n) := by
  have h1 : 0 < S5.qA n := S5.qA_pos hn16
  have h2 : S5.qA n < Real.pi := lt_trans (S5.qA_lt_pi_div_four hn16) (by linarith [Real.pi_pos])
  exact Real.sin_pos_of_pos_of_lt_pi h1 h2

/-- `sin(qA) ≥ 200/n` -/
lemma sin_qA_ge (n : ℕ) (hn16 : 2 ^ 16 ≤ n) : (200 : ℝ) / (n : ℝ) ≤ Real.sin (S5.qA n) := by
  have hq0 : 0 ≤ S5.qA n := (S5.qA_pos hn16).le
  have hq2 : S5.qA n ≤ Real.pi / 2 := S5.qA_le_pi_div_two hn16
  have hm := Real.mul_le_sin hq0 hq2  -- (2/π)·qA ≤ sin qA
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (S5.n_ge_one hn16))
  unfold S5.qA at hm ⊢
  convert hm using 1
  field_simp [hn0, Real.pi_ne_zero]
  ring

/-- `1/sin(qA) ≤ n/200` -/
lemma inv_sin_qA_le (n : ℕ) (hn16 : 2 ^ 16 ≤ n) :
    1 / Real.sin (S5.qA n) ≤ (n : ℝ) / 200 := by
  have hsq : 0 < Real.sin (S5.qA n) := sin_qA_pos n hn16
  have hn0 : 0 < (n : ℝ) := S5.nR_pos hn16
  rw [div_le_div_iff₀ (by positivity : (0:ℝ) < Real.sin (S5.qA n)) (by norm_num : (0:ℝ) < 200)]
  have h := sin_qA_ge n hn16
  have hle : (200 : ℝ) ≤ Real.sin (S5.qA n) * (n : ℝ) := (div_le_iff₀ hn0).mp h
  nlinarith

/-- `g(qA) ≤ 1/sin(qA)` -/
lemma gInv_qA_le (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ} (hθ0a : 0 ≤ θ0)
    (hθ0b : θ0 ≤ Real.pi / 2) : gInv θ0 (S5.qA n) ≤ 1 / Real.sin (S5.qA n) := by
  have hs : 0 < Real.sin (S5.qA n) := sin_qA_pos n hn16
  have hle : Real.sin (S5.qA n) ≤ Real.sin (S5.qA n + θ0) := sin_qA_add_ge_sin_qA n hn16 hθ0a hθ0b
  unfold gInv
  exact S5.inv_rev_of_pos hs hle

/-- `g(qB) ≤ 1/sin(qA)` -/
lemma gInv_qB_le (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ} (hθ0a : 0 ≤ θ0)
    (hθ0b : θ0 ≤ Real.pi / 2) : gInv θ0 (S5.qB n) ≤ 1 / Real.sin (S5.qA n) := by
  have hs : 0 < Real.sin (S5.qA n) := sin_qA_pos n hn16
  have hle : Real.sin (S5.qA n) ≤ Real.sin (S5.qB n + θ0) := sin_qB_add_ge_sin_qA n hn16 hθ0a hθ0b
  unfold gInv
  exact S5.inv_rev_of_pos hs hle

/-- `1/sin(qA) ≤ n/200` combined with g: `g(qA)/n ≤ 1/200` -/
lemma gInv_qA_div_n_le (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ} (hθ0a : 0 ≤ θ0)
    (hθ0b : θ0 ≤ Real.pi / 2) : gInv θ0 (S5.qA n) / (n : ℝ) ≤ 1 / 200 := by
  have hn0 : 0 < (n : ℝ) := S5.nR_pos hn16
  calc
    gInv θ0 (S5.qA n) / (n : ℝ) ≤ (1 / Real.sin (S5.qA n)) / (n : ℝ) := by
      exact div_le_div_of_nonneg_right (gInv_qA_le n hn16 hθ0a hθ0b) hn0.le
    _ ≤ ((n : ℝ) / 200) / (n : ℝ) := by
      exact div_le_div_of_nonneg_right (inv_sin_qA_le n hn16) hn0.le
    _ = 1 / 200 := by
      field_simp [ne_of_gt hn0]

/-- `g(qB)/n ≤ 1/200` -/
lemma gInv_qB_div_n_le (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ} (hθ0a : 0 ≤ θ0)
    (hθ0b : θ0 ≤ Real.pi / 2) : gInv θ0 (S5.qB n) / (n : ℝ) ≤ 1 / 200 := by
  have hn0 : 0 < (n : ℝ) := S5.nR_pos hn16
  calc
    gInv θ0 (S5.qB n) / (n : ℝ) ≤ (1 / Real.sin (S5.qA n)) / (n : ℝ) := by
      exact div_le_div_of_nonneg_right (gInv_qB_le n hn16 hθ0a hθ0b) hn0.le
    _ ≤ ((n : ℝ) / 200) / (n : ℝ) := by
      exact div_le_div_of_nonneg_right (inv_sin_qA_le n hn16) hn0.le
    _ = 1 / 200 := by
      field_simp [ne_of_gt hn0]

/-- `12π/n ≤ 1/100` for `n ≥ 2^16` -/
lemma twelve_pi_div_n_le (n : ℕ) (hn16 : 2 ^ 16 ≤ n) : 12 * Real.pi / (n : ℝ) ≤ 1 / 100 := by
  have hn0 : 0 < (n : ℝ) := S5.nR_pos hn16
  have hbig : (1200 * Real.pi : ℝ) ≤ (n : ℝ) := by
    have h' : (2 ^ 16 : ℝ) ≤ (n : ℝ) := S5.nR_ge_pow hn16
    have h1200 : (1200 * Real.pi : ℝ) ≤ 2 ^ 16 := by
      have h4 : Real.pi ≤ 4 := Real.pi_le_four
      norm_num
      nlinarith
    linarith
  rw [div_le_div_iff₀ hn0 (by norm_num : (0:ℝ) < 100)]
  nlinarith


/-- absolute value of the second Dirichlet arc-integral -/
def Iabs (n N : ℕ) (F : Family.Quad n N) (θ0 : ℝ) (i : Fin N) : ℝ :=
  |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.DK2 n θ0 θ|

/-- `DK2 = (1/sin(θ+θ0)) · sin(2n(θ+θ0))` pointwise -/
lemma DK2_eq (n : ℕ) (θ0 θ : ℝ) :
    S5.DK2 n θ0 θ = gInv θ0 θ * Real.sin (2 * (n : ℝ) * (θ + θ0)) := by
  unfold S5.DK2 gInv
  ring

/-- `sin(θ+θ0)` is continuous and nonzero on an arc -/
lemma continuousOn_sin_add_arc (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    (i : Fin N) {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    ContinuousOn (fun θ : ℝ => Real.sin (θ + θ0))
      (Set.Icc (F.arc i).lo (F.arc i).hi) := by
  exact (Real.continuous_sin.comp (Continuous.add continuous_id continuous_const)).continuousOn

/-- `gInv θ0` is continuous on an arc -/
lemma continuousOn_gInv_arc (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    (i : Fin N) {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    ContinuousOn (gInv θ0) (Set.Icc (F.arc i).lo (F.arc i).hi) := by
  unfold gInv
  have hne : ∀ x ∈ Set.Icc (F.arc i).lo (F.arc i).hi, Real.sin (x + θ0) ≠ 0 := by
    intro x hx
    exact (S5.arc_sin_inv_bound n N hn16 F i hθ0a hθ0b hx).2.ne'
  exact ContinuousOn.div continuousOn_const (continuousOn_sin_add_arc n N hn16 F i hθ0a hθ0b) hne

/-- `gInv θ0` antitone on `[qA, c]` -/
lemma gInv_antitone_low (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ} (hθ0a : 0 ≤ θ0) :
    AntitoneOn (gInv θ0) (Set.Icc (S5.qA n) (cVal θ0)) := by
  intro x hx y hy hxy
  have hx0 : 0 < x + θ0 := by linarith [hx.1, S5.qA_pos hn16, hθ0a]
  have hy2 : y + θ0 ≤ Real.pi / 2 := by
    dsimp [cVal] at hy
    linarith [hy.2]
  have hxpi : x + θ0 < Real.pi := by linarith [hy2, hxy, Real.pi_pos]
  have hleSin : Real.sin (x + θ0) ≤ Real.sin (y + θ0) := by
    exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [hx0, Real.pi_pos]) hy2 (by linarith)
  have hpos : 0 < Real.sin (x + θ0) :=
    Real.sin_pos_of_pos_of_lt_pi hx0 hxpi
  unfold gInv
  exact S5.inv_rev_of_pos hpos hleSin

/-- `gInv θ0` monotone on `[c, qB]` -/
lemma gInv_monotone_high (n : ℕ) (hn16 : 2 ^ 16 ≤ n) {θ0 : ℝ} (hθ0b : θ0 ≤ Real.pi / 2) :
    MonotoneOn (gInv θ0) (Set.Icc (cVal θ0) (S5.qB n)) := by
  intro x hx y hy hxy
  have hqA0 : 0 < S5.qA n := S5.qA_pos hn16
  have hqBpi : S5.qB n + θ0 ≤ Real.pi - S5.qA n := by
    rw [S5.qB_eq]
    linarith [hθ0b]
  have hxlow : Real.pi / 2 ≤ x + θ0 := by
    dsimp [cVal] at hx
    linarith [hx.1]
  have hylow : Real.pi / 2 ≤ y + θ0 := by linarith [hxlow, hxy]
  have hyhi : y + θ0 < Real.pi := by
    dsimp [cVal] at hy
    linarith [hy.2, hqBpi, hqA0]
  have hxhi : x + θ0 < Real.pi := by linarith [hyhi, hxy]
  have hleSin : Real.sin (y + θ0) ≤ Real.sin (x + θ0) := by
    apply sin_anti_right
    · exact ⟨hxlow, hxhi.le⟩
    · exact ⟨hylow, hyhi.le⟩
    · linarith
  have hpos : 0 < Real.sin (y + θ0) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hylow, Real.pi_pos]) hyhi
  unfold gInv
  exact S5.inv_rev_of_pos hpos hleSin

/-- LOW arc: `sin` monotone on the arc (g antitone) ⇒ per-arc bound -/
lemma arc_DK2_low_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2)
    (hLOW : (F.arc i).hi ≤ cVal θ0) :
    |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.DK2 n θ0 θ|
      ≤ (gInv θ0 (F.arc i).lo - gInv θ0 (F.arc i).hi) / (n : ℝ) := by
  let a : ℝ := (F.arc i).lo
  let b : ℝ := (F.arc i).hi
  have hab : a ≤ b := by dsimp [a, b]; exact (S5.arc_lo_lt_hi hn16 F i).le
  rcases S5.arc_len_multiple hn16 F i with ⟨m, hm6, hm⟩
  have hantiOnArc : AntitoneOn (gInv θ0) (Set.Icc a b) := by
    refine (gInv_antitone_low n hn16 hθ0a).mono ?_
    intro x hx
    dsimp [a, b] at hx
    exact ⟨le_trans (S5.arc_lo_ge_qA hn16 F i) hx.1, le_trans hx.2 hLOW⟩
  have hcont : ContinuousOn (gInv θ0) (Set.Icc a b) := by
    dsimp [a, b]
    exact continuousOn_gInv_arc n N hn16 F i hθ0a hθ0b
  have hanti : ∀ (x y : ℝ), x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y →
      gInv θ0 y ≤ gInv θ0 x := by
    intro x y hx hy hxy
    exact hantiOnArc hx hy hxy
  have hbnd := S5.antitone_sin_shifted n (S5.n_ge_one hn16) a b (-θ0) hab (gInv θ0)
    hcont hanti ⟨m, by dsimp [a, b]; exact hm⟩
  have hI : (∫ θ in a..b, S5.DK2 n θ0 θ)
      = ∫ θ in a..b, gInv θ0 θ * Real.sin (2 * (n : ℝ) * (θ + θ0)) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    exact DK2_eq n θ0 θ
  have hanti_ab : gInv θ0 b ≤ gInv θ0 a := by
    exact hantiOnArc (by dsimp [a, b]; exact ⟨le_rfl, hab⟩) (by dsimp [a, b]; exact ⟨hab, le_rfl⟩) hab
  have habs : |gInv θ0 b - gInv θ0 a| = gInv θ0 a - gInv θ0 b := by
    rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hanti_ab)]
  have hsub : (gInv θ0 a - gInv θ0 b) / (n : ℝ) ≤
      (gInv θ0 (F.arc i).lo - gInv θ0 (F.arc i).hi) / (n : ℝ) := by
    exact le_of_eq (by dsimp [a, b])
  have hbnd' : |∫ θ in a..b, S5.DK2 n θ0 θ|
      ≤ (gInv θ0 a - gInv θ0 b) / (n : ℝ) := by
    rw [hI]
    calc
      |∫ θ in a..b, gInv θ0 θ * Real.sin (2 * (n : ℝ) * (θ + θ0))|
          = |∫ θ in a..b, gInv θ0 θ * Real.sin (2 * (n : ℝ) * (θ - (-θ0)))| := by
            apply congrArg (fun t : ℝ => |t|)
            apply intervalIntegral.integral_congr
            intro θ hθ
            ring
      _ ≤ |gInv θ0 b - gInv θ0 a| / (n : ℝ) := hbnd
      _ = (gInv θ0 a - gInv θ0 b) / (n : ℝ) := by rw [habs]
  exact le_trans (by simpa [a, b] using hbnd') hsub

/-- HIGH arc: `sin` antitone on the arc (g monotone) ⇒ per-arc bound -/
lemma arc_DK2_high_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2)
    (hHIGH : cVal θ0 ≤ (F.arc i).lo) :
    |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.DK2 n θ0 θ|
      ≤ (gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo) / (n : ℝ) := by
  let a : ℝ := (F.arc i).lo
  let b : ℝ := (F.arc i).hi
  have hab : a ≤ b := by dsimp [a, b]; exact (S5.arc_lo_lt_hi hn16 F i).le
  rcases S5.arc_len_multiple hn16 F i with ⟨m, hm6, hm⟩
  have hmonoOnArc : MonotoneOn (gInv θ0) (Set.Icc a b) := by
    refine (gInv_monotone_high n hn16 hθ0b).mono ?_
    intro x hx
    dsimp [a, b] at hx
    exact ⟨le_trans hHIGH hx.1, le_trans hx.2 (S5.arc_hi_le_qB hn16 F i)⟩
  have hcont : ContinuousOn (gInv θ0) (Set.Icc a b) := by
    dsimp [a, b]
    exact continuousOn_gInv_arc n N hn16 F i hθ0a hθ0b
  have hmono : ∀ (x y : ℝ), x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y →
      gInv θ0 x ≤ gInv θ0 y := by
    intro x y hx hy hxy
    exact hmonoOnArc hx hy hxy
  have hbnd := S5.monotone_sin_shifted n (S5.n_ge_one hn16) a b (-θ0) hab (gInv θ0)
    hcont hmono ⟨m, by dsimp [a, b]; exact hm⟩
  have hI : (∫ θ in a..b, S5.DK2 n θ0 θ)
      = ∫ θ in a..b, gInv θ0 θ * Real.sin (2 * (n : ℝ) * (θ + θ0)) := by
    apply intervalIntegral.integral_congr
    intro θ hθ
    exact DK2_eq n θ0 θ
  have hmono_ab : gInv θ0 a ≤ gInv θ0 b := by
    exact hmonoOnArc (by dsimp [a, b]; exact ⟨le_rfl, hab⟩) (by dsimp [a, b]; exact ⟨hab, le_rfl⟩) hab
  have habs : |gInv θ0 b - gInv θ0 a| = gInv θ0 b - gInv θ0 a := by
    exact abs_of_nonneg (sub_nonneg.mpr hmono_ab)
  have hsub : (gInv θ0 b - gInv θ0 a) / (n : ℝ) ≤
      (gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo) / (n : ℝ) := by
    exact le_of_eq (by dsimp [a, b])
  have hbnd' : |∫ θ in a..b, S5.DK2 n θ0 θ|
      ≤ (gInv θ0 b - gInv θ0 a) / (n : ℝ) := by
    rw [hI]
    calc
      |∫ θ in a..b, gInv θ0 θ * Real.sin (2 * (n : ℝ) * (θ + θ0))|
          = |∫ θ in a..b, gInv θ0 θ * Real.sin (2 * (n : ℝ) * (θ - (-θ0)))| := by
            apply congrArg (fun t : ℝ => |t|)
            apply intervalIntegral.integral_congr
            intro θ hθ
            ring
      _ ≤ |gInv θ0 b - gInv θ0 a| / (n : ℝ) := hbnd
      _ = (gInv θ0 b - gInv θ0 a) / (n : ℝ) := by rw [habs]
  exact le_trans (by simpa [a, b] using hbnd') hsub

/-- if `u` is within `π/3` of `π/2` then `sin u ≥ 1/2` -/
lemma sin_ge_one_half {u : ℝ} (hu : |u - Real.pi / 2| ≤ Real.pi / 3) :
    (1 / 2 : ℝ) ≤ Real.sin u := by
  by_cases hle : u ≤ Real.pi / 2
  · have hw0 : 0 ≤ Real.pi / 2 - u := sub_nonneg.mpr hle
    have hw : Real.pi / 2 - u ≤ Real.pi / 3 := by
      have habs : |u - Real.pi / 2| = Real.pi / 2 - u := by
        rw [abs_sub_comm, abs_of_nonneg hw0]
      linarith [hu, habs]
    have hsin : Real.sin u = Real.cos (Real.pi / 2 - u) := by
      rw [Real.cos_pi_div_two_sub]
    rw [hsin]
    have hc : Real.cos (Real.pi / 3) ≤ Real.cos (Real.pi / 2 - u) := by
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      · linarith [hw0]
      · linarith [hw, Real.pi_pos]
      · exact hw
    simpa [Real.cos_pi_div_three] using hc
  · have hgt : Real.pi / 2 < u := lt_of_not_ge hle
    have hw0 : 0 ≤ u - Real.pi / 2 := sub_nonneg.mpr hgt.le
    have hw : u - Real.pi / 2 ≤ Real.pi / 3 := by
      have habs : |u - Real.pi / 2| = u - Real.pi / 2 := abs_of_nonneg hw0
      linarith [hu, habs]
    have hsin : Real.sin u = Real.cos (u - Real.pi / 2) := by
      rw [← Real.sin_add_pi_div_two (u - Real.pi / 2)]
      congr 1
      ring
    rw [hsin]
    have hc : Real.cos (Real.pi / 3) ≤ Real.cos (u - Real.pi / 2) := by
      apply Real.cos_le_cos_of_nonneg_of_le_pi
      · linarith [hw0]
      · linarith [hw, Real.pi_pos]
      · exact hw
    simpa [Real.cos_pi_div_three] using hc

/-- point `θ` between `a` and `c` and `c` between `a` and `b`: `|θ−c| ≤ b−a` -/
lemma abs_sub_c_le_len {c a b θ : ℝ} (hac : a < c) (hcb : c < b)
    (hθl : a ≤ θ) (hθr : θ ≤ b) : |θ - c| ≤ b - a := by
  by_cases hθc : θ ≤ c
  · have habs : |θ - c| = c - θ := by
      rw [abs_of_nonpos (sub_nonpos.mpr hθc), neg_sub]
    rw [habs]
    linarith
  · have hcθ : c ≤ θ := le_of_not_ge hθc
    have habs : |θ - c| = θ - c := abs_of_nonneg (sub_nonneg.mpr hcθ)
    rw [habs]
    linarith

/-- `DK2` continuous on an arc -/
lemma continuousOn_DK2_arc (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    (i : Fin N) {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    ContinuousOn (S5.DK2 n θ0) (Set.Icc (F.arc i).lo (F.arc i).hi) := by
  unfold S5.DK2
  have hne : ∀ x ∈ Set.Icc (F.arc i).lo (F.arc i).hi, Real.sin (x + θ0) ≠ 0 := by
    intro x hx
    exact (S5.arc_sin_inv_bound n N hn16 F i hθ0a hθ0b hx).2.ne'
  refine ContinuousOn.div ?_ (continuousOn_sin_add_arc n N hn16 F i hθ0a hθ0b) hne
  fun_prop


/-- MID (straddling) arc: crude bound `2·(hi−lo) ≤ 12π/n` -/
lemma arc_DK2_mid_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i : Fin N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2)
    (hmid : (F.arc i).lo < cVal θ0 ∧ cVal θ0 < (F.arc i).hi) :
    |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.DK2 n θ0 θ| ≤ 12 * Real.pi / (n : ℝ) := by
  let a : ℝ := (F.arc i).lo
  let b : ℝ := (F.arc i).hi
  have hab : a ≤ b := by dsimp [a, b]; exact (S5.arc_lo_lt_hi hn16 F i).le
  have h6 : b - a ≤ 6 * Real.pi / (n : ℝ) := by
    dsimp [a, b]
    exact S5.arc_len_le_six hn16 F i
  have hn0 : 0 < (n : ℝ) := S5.nR_pos hn16
  have h6pi : 6 * Real.pi / (n : ℝ) ≤ Real.pi / 3 := by
    have hn18 : (18 : ℝ) ≤ (n : ℝ) := by
      have h' : (2 ^ 16 : ℝ) ≤ (n : ℝ) := S5.nR_ge_pow hn16
      norm_num at h' ⊢
      linarith
    rw [div_le_div_iff₀ hn0 (by norm_num : (0:ℝ) < 3)]
    nlinarith [mul_le_mul_of_nonneg_right hn18 Real.pi_pos.le]
  have hpoint : ∀ θ ∈ Set.Icc a b, |S5.DK2 n θ0 θ| ≤ 2 := by
    intro θ hθ
    have hsub : |θ - cVal θ0| ≤ b - a := by
      exact abs_sub_c_le_len hmid.1 hmid.2 hθ.1 hθ.2
    have hdist : |(θ + θ0) - Real.pi / 2| ≤ b - a := by
      have harg : (θ + θ0) - Real.pi / 2 = θ - cVal θ0 := by
        dsimp [cVal]
        ring
      simpa [harg] using hsub
    have hdist3 : |(θ + θ0) - Real.pi / 2| ≤ Real.pi / 3 := le_trans hdist (le_trans h6 h6pi)
    have h12 : (1 / 2 : ℝ) ≤ Real.sin (θ + θ0) := sin_ge_one_half hdist3
    have hpos : 0 < Real.sin (θ + θ0) := lt_of_lt_of_le (by norm_num) h12
    have h1 : |Real.sin (2 * (n : ℝ) * (θ + θ0))| ≤ 1 := Real.abs_sin_le_one _
    have hlow : 1 / Real.sin (θ + θ0) ≤ 2 := by
      have h12p : 0 < (1 / 2 : ℝ) := by norm_num
      have h' : (Real.sin (θ + θ0))⁻¹ ≤ 2 := by
        have h'' := one_div_le_one_div_of_le h12p h12
        norm_num at h''
        simpa using h''
      simpa using h'
    unfold S5.DK2
    rw [abs_div]
    rw [abs_of_pos hpos]
    calc
      |Real.sin (2 * (n : ℝ) * (θ + θ0))| / Real.sin (θ + θ0)
          ≤ 1 / Real.sin (θ + θ0) := div_le_div_of_nonneg_right h1 hpos.le
      _ ≤ 2 := hlow
  have hc1 : ContinuousOn (S5.DK2 n θ0) (Set.Icc a b) := by
    dsimp [a, b]
    exact continuousOn_DK2_arc n N hn16 F i hθ0a hθ0b
  have hI : IntervalIntegrable (S5.DK2 n θ0) volume a b :=
    ContinuousOn.intervalIntegrable_of_Icc hab hc1
  have hIabs : IntervalIntegrable (fun θ : ℝ => |S5.DK2 n θ0 θ|) volume a b := hI.abs
  have hI2 : IntervalIntegrable (fun θ : ℝ => (2 : ℝ)) volume a b := by
    exact (continuousOn_const : ContinuousOn (fun _ : ℝ => (2 : ℝ)) (Set.Icc a b)).intervalIntegrable_of_Icc hab
  have hle1 : |∫ θ in a..b, S5.DK2 n θ0 θ| ≤ ∫ θ in a..b, |S5.DK2 n θ0 θ| :=
    intervalIntegral.abs_integral_le_integral_abs hab
  have hle2 : (∫ θ in a..b, |S5.DK2 n θ0 θ|) ≤ ∫ θ in a..b, (2 : ℝ) := by
    exact intervalIntegral.integral_mono_on hab hIabs hI2 hpoint
  have hle3 : (∫ θ in a..b, (2 : ℝ)) ≤ 12 * Real.pi / (n : ℝ) := by
    rw [intervalIntegral.integral_const]
    rw [smul_eq_mul]
    have hcalc : 6 * Real.pi / (n : ℝ) * 2 = 12 * Real.pi / (n : ℝ) := by
      field_simp [ne_of_gt hn0]
      ring
    calc
      (b - a) * 2 ≤ 6 * Real.pi / (n : ℝ) * 2 :=
        mul_le_mul_of_nonneg_right h6 (by norm_num : (0:ℝ) ≤ 2)
      _ = 12 * Real.pi / (n : ℝ) := hcalc
  exact le_trans hle1 (le_trans hle2 hle3)

/-- LOW arcs (entirely left of `c`): total ≤ `g(qA)/n` -/
lemma low_sum_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    (∑ i : Fin N, if (F.arc i).hi ≤ cVal θ0 then Iabs n N F θ0 i else 0)
      ≤ gInv θ0 (S5.qA n) / (n : ℝ) := by
  classical
  let Plo : Fin N → Prop := fun i => (F.arc i).hi ≤ cVal θ0
  have hn0 : 0 < (n : ℝ) := S5.nR_pos hn16
  by_cases hq : cVal θ0 < S5.qA n
  · have hset : (Finset.univ.filter Plo) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i hi hp
      have hlt : (F.arc i).lo < (F.arc i).hi := S5.arc_lo_lt_hi hn16 F i
      have hlo : S5.qA n ≤ (F.arc i).lo := S5.arc_lo_ge_qA hn16 F i
      dsimp [Plo] at hp
      linarith
    have hpos : 0 ≤ gInv θ0 (S5.qA n) := (gInv_qA_pos n hn16 hθ0a hθ0b).le
    calc
      (∑ i : Fin N, if Plo i then Iabs n N F θ0 i else 0)
          = ∑ i ∈ (Finset.univ.filter Plo), Iabs n N F θ0 i := by
            rw [Finset.sum_filter]
      _ = 0 := by simp [hset]
      _ ≤ gInv θ0 (S5.qA n) / (n : ℝ) := by exact div_nonneg hpos hn0.le
  · have hq' : S5.qA n ≤ cVal θ0 := le_of_not_gt hq
    have htele : (∑ i ∈ (Finset.univ.filter Plo),
        |gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo|)
        ≤ |gInv θ0 (cVal θ0) - gInv θ0 (S5.qA n)| := by
      exact S5Tele.sum_var_le_anti (s := Finset.univ.filter Plo)
        (lo := fun i : Fin N => (F.arc i).lo) (hi := fun i : Fin N => (F.arc i).hi)
        (A := S5.qA n) (B := cVal θ0) hq'
        (hA := fun i hi => S5.arc_lo_ge_qA hn16 F i)
        (hB := fun i hi => (Finset.mem_filter.mp hi).2)
        (hle := fun i hi => Family.Grid.lo_le_hi (F.arc i))
        (hsep := fun i hi j hj hij =>
          (S5.arc_sep hn16 F hij).elim (fun h => Or.inl (le_of_lt h)) (fun h => Or.inr (le_of_lt h)))
        (h := gInv θ0) (gInv_antitone_low n hn16 hθ0a)
    have hantiAB : gInv θ0 (cVal θ0) ≤ gInv θ0 (S5.qA n) := by
      exact gInv_antitone_low n hn16 hθ0a ⟨le_rfl, hq'⟩ ⟨hq', le_rfl⟩ hq'
    have hgpos : 0 ≤ gInv θ0 (cVal θ0) := by rw [gInv_c θ0]; norm_num
    have habs : |gInv θ0 (cVal θ0) - gInv θ0 (S5.qA n)|
        = gInv θ0 (S5.qA n) - gInv θ0 (cVal θ0) := by
      rw [abs_of_nonpos (sub_nonpos.mpr hantiAB)]
      ring
    have hle1 : |gInv θ0 (cVal θ0) - gInv θ0 (S5.qA n)| ≤ gInv θ0 (S5.qA n) := by
      rw [habs]
      linarith
    calc
      (∑ i : Fin N, if Plo i then Iabs n N F θ0 i else 0)
          = ∑ i ∈ (Finset.univ.filter Plo), Iabs n N F θ0 i := by
            rw [Finset.sum_filter]
      _ ≤ ∑ i ∈ (Finset.univ.filter Plo),
            |gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo| / (n : ℝ) := by
            apply Finset.sum_le_sum
            intro i hi
            have hanti_i : gInv θ0 (F.arc i).hi ≤ gInv θ0 (F.arc i).lo := by
              have harc : AntitoneOn (gInv θ0) (Set.Icc (F.arc i).lo (F.arc i).hi) := by
                refine (gInv_antitone_low n hn16 hθ0a).mono ?_
                intro x hx
                exact ⟨le_trans (S5.arc_lo_ge_qA hn16 F i) hx.1, le_trans hx.2 (Finset.mem_filter.mp hi).2⟩
              exact harc ⟨le_rfl, (S5.arc_lo_lt_hi hn16 F i).le⟩
                ⟨(S5.arc_lo_lt_hi hn16 F i).le, le_rfl⟩ (S5.arc_lo_lt_hi hn16 F i).le
            have habs_i : |gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo|
                = gInv θ0 (F.arc i).lo - gInv θ0 (F.arc i).hi := by
              rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr hanti_i)]
            calc
              Iabs n N F θ0 i
                  ≤ (gInv θ0 (F.arc i).lo - gInv θ0 (F.arc i).hi) / (n : ℝ) :=
                    arc_DK2_low_bound n N hn16 F i hθ0a hθ0b (Finset.mem_filter.mp hi).2
              _ = |gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo| / (n : ℝ) := by rw [habs_i]
      _ = (∑ i ∈ (Finset.univ.filter Plo),
            |gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo|) / (n : ℝ) := by
            rw [Finset.sum_div]
      _ ≤ |gInv θ0 (cVal θ0) - gInv θ0 (S5.qA n)| / (n : ℝ) := by
            exact div_le_div_of_nonneg_right htele hn0.le
      _ ≤ gInv θ0 (S5.qA n) / (n : ℝ) := by
            exact div_le_div_of_nonneg_right hle1 hn0.le

/-- HIGH arcs (entirely right of `c`): total ≤ `g(qB)/n` -/
lemma high_sum_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    (∑ i : Fin N, if cVal θ0 ≤ (F.arc i).lo then Iabs n N F θ0 i else 0)
      ≤ gInv θ0 (S5.qB n) / (n : ℝ) := by
  classical
  let Phi : Fin N → Prop := fun i => cVal θ0 ≤ (F.arc i).lo
  have hn0 : 0 < (n : ℝ) := S5.nR_pos hn16
  by_cases hq : S5.qB n < cVal θ0
  · have hset : (Finset.univ.filter Phi) = ∅ := by
      apply Finset.filter_eq_empty_iff.mpr
      intro i hi hp
      have hlt : (F.arc i).lo < (F.arc i).hi := S5.arc_lo_lt_hi hn16 F i
      have hhi : (F.arc i).hi ≤ S5.qB n := S5.arc_hi_le_qB hn16 F i
      dsimp [Phi] at hp
      linarith
    have hpos : 0 ≤ gInv θ0 (S5.qB n) := (gInv_qB_pos n hn16 hθ0a hθ0b).le
    calc
      (∑ i : Fin N, if Phi i then Iabs n N F θ0 i else 0)
          = ∑ i ∈ (Finset.univ.filter Phi), Iabs n N F θ0 i := by
            rw [Finset.sum_filter]
      _ = 0 := by simp [hset]
      _ ≤ gInv θ0 (S5.qB n) / (n : ℝ) := by exact div_nonneg hpos hn0.le
  · have hq' : cVal θ0 ≤ S5.qB n := le_of_not_gt hq
    have htele : (∑ i ∈ (Finset.univ.filter Phi),
        |gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo|)
        ≤ |gInv θ0 (S5.qB n) - gInv θ0 (cVal θ0)| := by
      exact S5Tele.sum_var_le_mono (s := Finset.univ.filter Phi)
        (lo := fun i : Fin N => (F.arc i).lo) (hi := fun i : Fin N => (F.arc i).hi)
        (A := cVal θ0) (B := S5.qB n) hq'
        (hA := fun i hi => (Finset.mem_filter.mp hi).2)
        (hB := fun i hi => S5.arc_hi_le_qB hn16 F i)
        (hle := fun i hi => Family.Grid.lo_le_hi (F.arc i))
        (hsep := fun i hi j hj hij =>
          (S5.arc_sep hn16 F hij).elim (fun h => Or.inl (le_of_lt h)) (fun h => Or.inr (le_of_lt h)))
        (h := gInv θ0) (gInv_monotone_high n hn16 hθ0b)
    have hmonoAB : gInv θ0 (cVal θ0) ≤ gInv θ0 (S5.qB n) := by
      exact gInv_monotone_high n hn16 hθ0b ⟨le_rfl, hq'⟩ ⟨hq', le_rfl⟩ hq'
    have hgpos : 0 ≤ gInv θ0 (cVal θ0) := by rw [gInv_c θ0]; norm_num
    have habs : |gInv θ0 (S5.qB n) - gInv θ0 (cVal θ0)|
        = gInv θ0 (S5.qB n) - gInv θ0 (cVal θ0) := by
      exact abs_of_nonneg (sub_nonneg.mpr hmonoAB)
    have hle1 : |gInv θ0 (S5.qB n) - gInv θ0 (cVal θ0)| ≤ gInv θ0 (S5.qB n) := by
      rw [habs]
      linarith
    calc
      (∑ i : Fin N, if Phi i then Iabs n N F θ0 i else 0)
          = ∑ i ∈ (Finset.univ.filter Phi), Iabs n N F θ0 i := by
            rw [Finset.sum_filter]
      _ ≤ ∑ i ∈ (Finset.univ.filter Phi),
            |gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo| / (n : ℝ) := by
            apply Finset.sum_le_sum
            intro i hi
            have hmono_i : gInv θ0 (F.arc i).lo ≤ gInv θ0 (F.arc i).hi := by
              have harc : MonotoneOn (gInv θ0) (Set.Icc (F.arc i).lo (F.arc i).hi) := by
                refine (gInv_monotone_high n hn16 hθ0b).mono ?_
                intro x hx
                exact ⟨le_trans (Finset.mem_filter.mp hi).2 hx.1, le_trans hx.2 (S5.arc_hi_le_qB hn16 F i)⟩
              exact harc ⟨le_rfl, (S5.arc_lo_lt_hi hn16 F i).le⟩
                ⟨(S5.arc_lo_lt_hi hn16 F i).le, le_rfl⟩ (S5.arc_lo_lt_hi hn16 F i).le
            have habs_i : |gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo|
                = gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo := by
              exact abs_of_nonneg (sub_nonneg.mpr hmono_i)
            calc
              Iabs n N F θ0 i
                  ≤ (gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo) / (n : ℝ) :=
                    arc_DK2_high_bound n N hn16 F i hθ0a hθ0b (Finset.mem_filter.mp hi).2
              _ = |gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo| / (n : ℝ) := by rw [habs_i]
      _ = (∑ i ∈ (Finset.univ.filter Phi),
            |gInv θ0 (F.arc i).hi - gInv θ0 (F.arc i).lo|) / (n : ℝ) := by
            rw [Finset.sum_div]
      _ ≤ |gInv θ0 (S5.qB n) - gInv θ0 (cVal θ0)| / (n : ℝ) := by
            exact div_le_div_of_nonneg_right htele hn0.le
      _ ≤ gInv θ0 (S5.qB n) / (n : ℝ) := by
            exact div_le_div_of_nonneg_right hle1 hn0.le

/-- MID (at most one straddling) arcs: total ≤ `12π/n` -/
lemma mid_sum_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    (∑ i : Fin N, if (F.arc i).lo < cVal θ0 ∧ cVal θ0 < (F.arc i).hi
        then Iabs n N F θ0 i else 0) ≤ 12 * Real.pi / (n : ℝ) := by
  classical
  let Pmid : Fin N → Prop := fun i => (F.arc i).lo < cVal θ0 ∧ cVal θ0 < (F.arc i).hi
  let midSet : Finset (Fin N) := Finset.univ.filter Pmid
  have hcard : midSet.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    refine S5.one_arc_contains hn16 F (cVal θ0) a b ?_ ?_
    · exact ⟨(Finset.mem_filter.mp ha).2.1.le, (Finset.mem_filter.mp ha).2.2.le⟩
    · exact ⟨(Finset.mem_filter.mp hb).2.1.le, (Finset.mem_filter.mp hb).2.2.le⟩
  have hper : ∀ i ∈ midSet, Iabs n N F θ0 i ≤ 12 * Real.pi / (n : ℝ) := by
    intro i hi
    exact arc_DK2_mid_bound n N hn16 F i hθ0a hθ0b (Finset.mem_filter.mp hi).2
  have hM0 : 0 ≤ 12 * Real.pi / (n : ℝ) := by positivity
  have hsum : (∑ i ∈ midSet, Iabs n N F θ0 i) ≤ 12 * Real.pi / (n : ℝ) := by
    by_cases hne : midSet = ∅
    · simp [hne, hM0]
    · have hnonempty : midSet.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
      rcases hnonempty with ⟨a, ha⟩
      have hsingle : ∀ b ∈ midSet, b = a := by
        intro b hb
        exact (Finset.card_le_one.mp hcard) b hb a ha
      have hsum_a : (∑ i ∈ midSet, Iabs n N F θ0 i) = Iabs n N F θ0 a := by
        apply Finset.sum_eq_single a
        · intro b hb hba
          have : b = a := hsingle b hb
          exact False.elim (hba this)
        · intro ha_not
          exact False.elim (ha_not ha)
      rw [hsum_a]
      exact hper a ha
  calc
    (∑ i : Fin N, if Pmid i then Iabs n N F θ0 i else 0)
        = ∑ i ∈ (Finset.univ.filter Pmid), Iabs n N F θ0 i := by
          rw [Finset.sum_filter]
    _ ≤ 12 * Real.pi / (n : ℝ) := hsum

/-- Claim 1 -/
theorem claim1_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    (∑ i : Fin N, |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.DK2 n θ0 θ|) ≤ 1 / 50 := by
  classical
  change (∑ i : Fin N, Iabs n N F θ0 i) ≤ 1 / 50
  let Plo : Fin N → Prop := fun i => (F.arc i).hi ≤ cVal θ0
  let Phi : Fin N → Prop := fun i => cVal θ0 ≤ (F.arc i).lo
  let Pmid : Fin N → Prop := fun i => (F.arc i).lo < cVal θ0 ∧ cVal θ0 < (F.arc i).hi
  have htri : ∀ i : Fin N, Plo i ∨ Phi i ∨ Pmid i := by
    intro i
    by_cases h1 : (F.arc i).hi ≤ cVal θ0
    · exact Or.inl h1
    · have hc_hi : cVal θ0 < (F.arc i).hi := lt_of_not_ge h1
      by_cases h2 : cVal θ0 ≤ (F.arc i).lo
      · exact Or.inr (Or.inl h2)
      · have hc_lo : (F.arc i).lo < cVal θ0 := lt_of_not_ge h2
        exact Or.inr (Or.inr ⟨hc_lo, hc_hi⟩)
  have hx12 : ∀ i : Fin N, Plo i → ¬ Phi i := by
    intro i hp hq
    have hlt : (F.arc i).lo < (F.arc i).hi := S5.arc_lo_lt_hi hn16 F i
    linarith
  have hx13 : ∀ i : Fin N, Plo i → ¬ Pmid i := by
    intro i hp hq
    dsimp [Plo, Pmid] at hp hq
    linarith
  have hx23 : ∀ i : Fin N, Phi i → ¬ Pmid i := by
    intro i hp hq
    dsimp [Phi, Pmid] at hp hq
    linarith
  have hdecomp : (∑ i : Fin N, Iabs n N F θ0 i)
      = (∑ i : Fin N, if Plo i then Iabs n N F θ0 i else 0)
      + (∑ i : Fin N, if Phi i then Iabs n N F θ0 i else 0)
      + (∑ i : Fin N, if Pmid i then Iabs n N F θ0 i else 0) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases h1 : Plo i
    · have hn2 : ¬ Phi i := hx12 i h1
      have hn3 : ¬ Pmid i := hx13 i h1
      simp [h1, hn2, hn3]
    · by_cases h2 : Phi i
      · have hn1 : ¬ Plo i := h1
        have hn3 : ¬ Pmid i := hx23 i h2
        simp [hn1, h2, hn3]
      · have h3 : Pmid i := by
          rcases htri i with h | h | h
          · exact False.elim (h1 h)
          · exact False.elim (h2 h)
          · exact h
        simp [h1, h2, h3]
  have hL : (∑ i : Fin N, if Plo i then Iabs n N F θ0 i else 0)
      ≤ gInv θ0 (S5.qA n) / (n : ℝ) := by
    simpa [Plo] using low_sum_bound n N hn16 F hθ0a hθ0b
  have hH : (∑ i : Fin N, if Phi i then Iabs n N F θ0 i else 0)
      ≤ gInv θ0 (S5.qB n) / (n : ℝ) := by
    simpa [Phi] using high_sum_bound n N hn16 F hθ0a hθ0b
  have hM : (∑ i : Fin N, if Pmid i then Iabs n N F θ0 i else 0)
      ≤ 12 * Real.pi / (n : ℝ) := by
    simpa [Pmid] using mid_sum_bound n N hn16 F hθ0a hθ0b
  calc
    (∑ i : Fin N, Iabs n N F θ0 i)
        = (∑ i : Fin N, if Plo i then Iabs n N F θ0 i else 0)
          + (∑ i : Fin N, if Phi i then Iabs n N F θ0 i else 0)
          + (∑ i : Fin N, if Pmid i then Iabs n N F θ0 i else 0) := hdecomp
    _ ≤ gInv θ0 (S5.qA n) / (n : ℝ) + gInv θ0 (S5.qB n) / (n : ℝ)
        + 12 * Real.pi / (n : ℝ) := by
          linarith
    _ ≤ 1 / 200 + 1 / 200 + 1 / 100 := by
          have hA : gInv θ0 (S5.qA n) / (n : ℝ) ≤ 1 / 200 := gInv_qA_div_n_le n hn16 hθ0a hθ0b
          have hB : gInv θ0 (S5.qB n) / (n : ℝ) ≤ 1 / 200 := gInv_qB_div_n_le n hn16 hθ0a hθ0b
          have hC : 12 * Real.pi / (n : ℝ) ≤ 1 / 100 := twelve_pi_div_n_le n hn16
          linarith
    _ = 1 / 50 := by norm_num
end S5C1
namespace S5C3L
/-- `1/(θ−θ0)` is antitone while `θ < θ0`: `x ≤ y < θ0 ⟹ 1/(y−θ0) ≤ 1/(x−θ0)` -/
lemma inv_sub_anti_left {θ0 x y : ℝ} (hxy : x ≤ y) (hy : y < θ0) :
    1 / (y - θ0) ≤ 1 / (x - θ0) := by
  have hx0 : x - θ0 ≠ 0 := by linarith
  have hy0 : y - θ0 ≠ 0 := by linarith
  have hfrac : 1 / (y - θ0) - 1 / (x - θ0) = (x - y) / ((y - θ0) * (x - θ0)) := by
    field_simp [hy0, hx0]
    ring
  have hden : 0 < (y - θ0) * (x - θ0) := by
    have hyneg : y - θ0 < 0 := by linarith
    have hxneg : x - θ0 < 0 := by linarith
    exact mul_pos_of_neg_of_neg hyneg hxneg
  have hle0 : 1 / (y - θ0) - 1 / (x - θ0) ≤ 0 := by
    rw [hfrac]
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hden.le
  linarith

/-- Claim 3 (left side) -/
theorem left_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    (∑ i in (Finset.univ.filter (fun i : Fin N => (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ))),
        |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.LK n θ0 θ|)
      ≤ 1 / Real.pi := by
  classical
  let h : ℝ → ℝ := fun θ => 1 / (θ - θ0)
  let B : ℝ := θ0 - Real.pi / (n : ℝ)
  let P : Fin N → Prop := fun i => (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ)
  let s : Finset (Fin N) := Finset.univ.filter P
  have hnpos : 0 < (n : ℝ) := S5.nR_pos hn16
  have hB_lt_θ0 : B < θ0 := by
    have hπn : 0 < Real.pi / (n : ℝ) := by positivity
    dsimp [B]
    linarith
  have hper : ∀ i : Fin N, i ∈ s → (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ) := by
    intro i hi
    have hmem : i ∈ Finset.univ.filter P := by
      simpa [s, P] using hi
    exact (Finset.mem_filter.mp hmem).2
  change (∑ i ∈ s, |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.LK n θ0 θ|) ≤ 1 / Real.pi
  by_cases hS : s = ∅
  · rw [hS]
    simp
    simpa using (Real.pi_pos.le : (0 : ℝ) ≤ Real.pi)
  · have hsNE : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    rcases hsNE with ⟨i0, hi0mem⟩
    have hPi0 : (F.arc i0).hi ≤ θ0 - Real.pi / (n : ℝ) := (Finset.mem_filter.mp hi0mem).2
    have hAB : S5.qA n ≤ B := by
      have h1 := S5.arc_lo_ge_qA hn16 F i0        -- qA ≤ lo i0
      have h2 := Family.Grid.lo_le_hi (F.arc i0)  -- lo i0 ≤ hi i0
      dsimp [B]
      linarith
    have hanti : AntitoneOn h (Set.Icc (S5.qA n) B) := by
      intro x hx y hy hxy
      dsimp [h]
      exact inv_sub_anti_left (θ0 := θ0) hxy (by linarith [hy.2, hB_lt_θ0])
    have htele : (∑ i ∈ s, |h ((F.arc i).hi) - h ((F.arc i).lo)|) ≤
        |h B - h (S5.qA n)| := by
      have hh := S5Tele.sum_var_le_anti (s := s) (lo := fun i : Fin N => (F.arc i).lo)
        (hi := fun i : Fin N => (F.arc i).hi) (A := S5.qA n) (B := B) hAB
        (hA := fun i hi => S5.arc_lo_ge_qA hn16 F i)
        (hB := hper)
        (hle := fun i hi => Family.Grid.lo_le_hi (F.arc i))
        (hsep := fun i hi j hj hij =>
          (S5.arc_sep hn16 F hij).elim
            (fun hlt => Or.inl (le_of_lt hlt))
            (fun hlt => Or.inr (le_of_lt hlt)))
        (h := h) hanti
      simpa using hh
    have hsum_step : (∑ i ∈ s,
          |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.LK n θ0 θ|)
        ≤ ∑ i ∈ s, |h ((F.arc i).hi) - h ((F.arc i).lo)| / (n : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hfar : (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ) ∨
          θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo := Or.inl (hper i hi)
      have hb := S5.arc_LK_far_bound n N hn16 F i hθ0a hθ0b hfar
      simpa [h] using hb
    have hval : |h B - h (S5.qA n)| = h (S5.qA n) - h B := by
      rw [abs_sub_comm]
      apply abs_of_nonneg
      rw [sub_nonneg]
      dsimp [h]
      exact inv_sub_anti_left (θ0 := θ0) (x := S5.qA n) (y := B) hAB (by linarith [hB_lt_θ0])
    have hA_le_0 : 1 / (S5.qA n - θ0) ≤ 0 := by
      have hden : S5.qA n - θ0 < 0 := by
        have hAB' : S5.qA n ≤ θ0 - Real.pi / (n : ℝ) := by
          dsimp [B] at hAB
          exact hAB
        have hπn : 0 < Real.pi / (n : ℝ) := by positivity
        linarith
      rw [div_le_iff_of_neg hden]
      norm_num
    have hB_val : 1 / (B - θ0) = - (n : ℝ) / Real.pi := by
      have hπn : Real.pi / (n : ℝ) ≠ 0 :=
        div_ne_zero (ne_of_gt Real.pi_pos) (ne_of_gt hnpos)
      dsimp [B]
      field_simp [hπn]
      ring
    have hfin : h (S5.qA n) - h B ≤ (n : ℝ) / Real.pi := by
      dsimp [h]
      calc
        1 / (S5.qA n - θ0) - 1 / (B - θ0)
            = 1 / (S5.qA n - θ0) + (n : ℝ) / Real.pi := by
                rw [hB_val]
                ring
        _ ≤ 0 + (n : ℝ) / Real.pi := by
                exact add_le_add hA_le_0 (le_rfl : (n : ℝ) / Real.pi ≤ (n : ℝ) / Real.pi)
        _ = (n : ℝ) / Real.pi := by ring
    have habs_le : |h B - h (S5.qA n)| ≤ (n : ℝ) / Real.pi := by
      rw [hval]
      exact hfin
    have hdiv : |h B - h (S5.qA n)| / (n : ℝ) ≤ 1 / Real.pi := by
      calc
        |h B - h (S5.qA n)| / (n : ℝ) ≤ ((n : ℝ) / Real.pi) / (n : ℝ) :=
          div_le_div_of_nonneg_right habs_le (le_of_lt hnpos)
        _ = 1 / Real.pi := by field_simp [ne_of_gt hnpos]
    calc
      (∑ i ∈ s, |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.LK n θ0 θ|)
          ≤ ∑ i ∈ s, |h ((F.arc i).hi) - h ((F.arc i).lo)| / (n : ℝ) := hsum_step
      _ = (∑ i ∈ s, |h ((F.arc i).hi) - h ((F.arc i).lo)|) / (n : ℝ) := by
          rw [← Finset.sum_div]
      _ ≤ |h B - h (S5.qA n)| / (n : ℝ) :=
          div_le_div_of_nonneg_right htele (le_of_lt hnpos)
      _ ≤ 1 / Real.pi := hdiv
end S5C3L
namespace S5C3R
/-- `1/(θ−θ0)` is antitone while `θ0 < θ`: `θ0 < x ≤ y ⟹ 1/(y−θ0) ≤ 1/(x−θ0)` -/
lemma inv_sub_anti_right {θ0 x y : ℝ} (hx0 : 0 < x - θ0) (hxy : x ≤ y) :
    1 / (y - θ0) ≤ 1 / (x - θ0) := by
  exact S5.inv_rev_of_pos hx0 (by linarith)

/-- Claim 3 (right side) -/
theorem right_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    (∑ i in (Finset.univ.filter (fun i : Fin N => θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo)),
        |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.LK n θ0 θ|)
      ≤ 1 / Real.pi := by
  classical
  let h : ℝ → ℝ := fun θ => 1 / (θ - θ0)
  let A : ℝ := θ0 + Real.pi / (n : ℝ)
  let P : Fin N → Prop := fun i => θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo
  let s : Finset (Fin N) := Finset.univ.filter P
  have hnpos : 0 < (n : ℝ) := S5.nR_pos hn16
  have hπn_pos : 0 < Real.pi / (n : ℝ) := by
    exact div_pos Real.pi_pos hnpos
  have hper : ∀ i : Fin N, i ∈ s → θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo := by
    intro i hi
    have hmem : i ∈ Finset.univ.filter P := by
      simpa [s] using hi
    exact (Finset.mem_filter.mp hmem).2
  change (∑ i ∈ s, |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.LK n θ0 θ|) ≤ 1 / Real.pi
  by_cases hS : s = ∅
  · rw [hS]
    simp
    simpa using (Real.pi_pos.le : (0 : ℝ) ≤ Real.pi)
  · have hsNE : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    rcases hsNE with ⟨i0, hi0mem⟩
    have hPi0 : θ0 + Real.pi / (n : ℝ) ≤ (F.arc i0).lo := hper i0 hi0mem
    have hAB : A ≤ S5.qB n := by
      have h1 := S5.arc_hi_le_qB hn16 F i0        -- hi i0 ≤ qB n
      have h2 := Family.Grid.lo_le_hi (F.arc i0)  -- lo i0 ≤ hi i0
      dsimp [A]
      linarith
    have hA_lo : ∀ i ∈ s, A ≤ (F.arc i).lo := by
      intro i hi
      have hp := hper i hi
      dsimp [A]
      exact hp
    have hanti : AntitoneOn h (Set.Icc A (S5.qB n)) := by
      intro x hx y hy hxy
      dsimp [h]
      have hxA : A ≤ x := hx.1
      have hxpos : 0 < x - θ0 := by
        dsimp [A] at hxA
        linarith
      exact inv_sub_anti_right (θ0 := θ0) hxpos hxy
    have htele : (∑ i ∈ s, |h ((F.arc i).hi) - h ((F.arc i).lo)|) ≤
        |h (S5.qB n) - h A| := by
      have hh := S5Tele.sum_var_le_anti (s := s) (lo := fun i : Fin N => (F.arc i).lo)
        (hi := fun i : Fin N => (F.arc i).hi) (A := A) (B := S5.qB n) hAB
        (hA := hA_lo)
        (hB := fun i hi => S5.arc_hi_le_qB hn16 F i)
        (hle := fun i hi => Family.Grid.lo_le_hi (F.arc i))
        (hsep := fun i hi j hj hij =>
          (S5.arc_sep hn16 F hij).elim
            (fun hlt => Or.inl (le_of_lt hlt))
            (fun hlt => Or.inr (le_of_lt hlt)))
        (h := h) hanti
      simpa using hh
    have hsum_step : (∑ i ∈ s,
          |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.LK n θ0 θ|)
        ≤ ∑ i ∈ s, |h ((F.arc i).hi) - h ((F.arc i).lo)| / (n : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      have hfar : (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ) ∨
          θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo := Or.inr (hper i hi)
      have hb := S5.arc_LK_far_bound n N hn16 F i hθ0a hθ0b hfar
      simpa [h] using hb
    have hA_mθ0 : A - θ0 = Real.pi / (n : ℝ) := by
      dsimp [A]
      ring
    have hA_mθ0_pos : 0 < A - θ0 := by
      rw [hA_mθ0]
      exact hπn_pos
    have hA_val : 1 / (A - θ0) = (n : ℝ) / Real.pi := by
      rw [hA_mθ0]
      exact one_div_div Real.pi (n : ℝ)
    have hqB_mθ0_pos : 0 < S5.qB n - θ0 := by
      have h1 : Real.pi / (n : ℝ) ≤ S5.qB n - θ0 := by
        have hAB' : A ≤ S5.qB n := hAB
        dsimp [A] at hAB'
        linarith
      exact lt_of_lt_of_le hπn_pos h1
    have hqB_inv_nonneg : 0 ≤ 1 / (S5.qB n - θ0) :=
      div_nonneg (by norm_num) (le_of_lt hqB_mθ0_pos)
    have hfin : h A - h (S5.qB n) ≤ (n : ℝ) / Real.pi := by
      dsimp [h]
      calc
        1 / (A - θ0) - 1 / (S5.qB n - θ0)
            = (n : ℝ) / Real.pi - 1 / (S5.qB n - θ0) := by rw [hA_val]
        _ ≤ (n : ℝ) / Real.pi - 0 := sub_le_sub_left hqB_inv_nonneg ((n : ℝ) / Real.pi)
        _ = (n : ℝ) / Real.pi := by ring
    have hmon : h (S5.qB n) ≤ h A := by
      dsimp [h]
      exact S5.inv_rev_of_pos hA_mθ0_pos (by linarith)
    have hval : |h (S5.qB n) - h A| = h A - h (S5.qB n) := by
      rw [abs_sub_comm]
      exact abs_of_nonneg (sub_nonneg.mpr hmon)
    have habs_le : |h (S5.qB n) - h A| ≤ (n : ℝ) / Real.pi := by
      rw [hval]
      exact hfin
    have hdiv : |h (S5.qB n) - h A| / (n : ℝ) ≤ 1 / Real.pi := by
      calc
        |h (S5.qB n) - h A| / (n : ℝ) ≤ ((n : ℝ) / Real.pi) / (n : ℝ) :=
          div_le_div_of_nonneg_right habs_le (le_of_lt hnpos)
        _ = 1 / Real.pi := by field_simp [ne_of_gt hnpos]
    calc
      (∑ i ∈ s, |∫ θ in (F.arc i).lo..(F.arc i).hi, S5.LK n θ0 θ|)
          ≤ ∑ i ∈ s, |h ((F.arc i).hi) - h ((F.arc i).lo)| / (n : ℝ) := hsum_step
      _ = (∑ i ∈ s, |h ((F.arc i).hi) - h ((F.arc i).lo)|) / (n : ℝ) := by
          rw [← Finset.sum_div]
      _ ≤ |h (S5.qB n) - h A| / (n : ℝ) :=
          div_le_div_of_nonneg_right htele (le_of_lt hnpos)
      _ ≤ 1 / Real.pi := hdiv
end S5C3R
end Submission

namespace Submission
namespace S5


/-! ============= Final theorems ============= -/

/-- `|Σ f + Σ g| ≥ |Σ f| - |Σ g|` -/
lemma abs_sum_sub_ge {ι : Type*} [Fintype ι] (f g : ι → ℝ) :
    |(∑ i : ι, (f i + g i))| ≥ |(∑ i : ι, f i)| - |(∑ i : ι, g i)| := by
  have hsum : (∑ i : ι, f i) + (∑ i : ι, g i) = ∑ i : ι, (f i + g i) := by
    simp [Finset.sum_add_distrib]
  have habs : |∑ i : ι, f i| ≤ |∑ i : ι, (f i + g i)| + |∑ i : ι, g i| := by
    calc
      |∑ i : ι, f i| = |(∑ i : ι, (f i + g i)) + (-(∑ i : ι, g i))| := by
          rw [← hsum]
          congr 1
          ring
      _ ≤ |∑ i : ι, (f i + g i)| + |∑ i : ι, g i| := by
          simpa using (abs_add_le ((∑ i : ι, (f i + g i))) (-(∑ i : ι, g i)))
  linarith

/-- `|Σ f + Σ g + Σ h| ≥ |Σ f| − |Σ g| − |Σ h|` -/
lemma abs_sum_add_sub_ge {ι : Type*} [Fintype ι] (f g h : ι → ℝ) :
    |(∑ i : ι, ((f i + g i) + h i))| ≥ |(∑ i : ι, f i)| - |(∑ i : ι, g i)| - |(∑ i : ι, h i)| := by
  have h2 := abs_sum_sub_ge (fun i : ι => f i + g i) h
  have h1 := abs_sum_sub_ge f g
  linarith

/-- sum of a weighted difference `Σ (α_i x_i + α_i y_i)` rewrites -/
lemma sum_alpha_add {N : ℕ} (α x y : Fin N → ℝ) :
    (∑ i : Fin N, (α i * x i + α i * y i)) = (∑ i : Fin N, α i * x i) + (∑ i : Fin N, α i * y i) := by
  rw [← Finset.sum_add_distrib]

/-- split T into the C/e/B parts -/
lemma Tθ_split (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (α : Fin N → ℝ)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    Tθ n N F α θ0 =
      (∑ i : Fin N, α i * (∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ))
      + (∑ i : Fin N, α i * ((∫ θ in (F.arc i).lo..(F.arc i).hi, DK1 n θ0 θ)
          - (∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ)))
      - (∑ i : Fin N, α i * (∫ θ in (F.arc i).lo..(F.arc i).hi, DK2 n θ0 θ)) := by
  calc
    Tθ n N F α θ0
        = ∑ i : Fin N, α i * ((∫ θ in (F.arc i).lo..(F.arc i).hi, DK1 n θ0 θ)
          - (∫ θ in (F.arc i).lo..(F.arc i).hi, DK2 n θ0 θ)) := Tθ_eq_sum n N hn16 F α hθ0a hθ0b
    _ = ∑ i : Fin N, α i * (arcC n θ0 (F.arc i).lo (F.arc i).hi
          + ((∫ θ in (F.arc i).lo..(F.arc i).hi, DK1 n θ0 θ)
            - (∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ))
          - (∫ θ in (F.arc i).lo..(F.arc i).hi, DK2 n θ0 θ)) := by
        apply Finset.sum_congr rfl
        intro i hi
        congr 1
        exact arc_split n N hn16 F i hθ0a hθ0b
    _ = (∑ i : Fin N, (α i * (arcC n θ0 (F.arc i).lo (F.arc i).hi)
          + α i * ((∫ θ in (F.arc i).lo..(F.arc i).hi, DK1 n θ0 θ)
            - (∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ))
          - α i * (∫ θ in (F.arc i).lo..(F.arc i).hi, DK2 n θ0 θ))) := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
    _ = (∑ i : Fin N, α i * (arcC n θ0 (F.arc i).lo (F.arc i).hi))
        + (∑ i : Fin N, α i * ((∫ θ in (F.arc i).lo..(F.arc i).hi, DK1 n θ0 θ)
            - (∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ)))
        - (∑ i : Fin N, α i * (∫ θ in (F.arc i).lo..(F.arc i).hi, DK2 n θ0 θ)) := by
        -- Σ (x + y − z) = Σx + Σy − Σz
        rw [Finset.sum_sub_distrib]
        rw [← Finset.sum_add_distrib]



/-- triangle inequality for sums: `|Σ f| ≤ Σ |f|` -/
lemma abs_sum_le_sum_abs {ι : Type*} [Fintype ι] (f : ι → ℝ) :
    |∑ i : ι, f i| ≤ ∑ i : ι, |f i| := by
  simpa using (Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset ι)) (f := f))

/-- the far-filter sum splits into the left- and right-filter sums -/
lemma far_sum_split (n N : ℕ) (F : Family.Quad n N) {θ0 : ℝ} (f : Fin N → ℝ) :
    (∑ i ∈ (Finset.univ.filter (fun i : Fin N =>
        (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ) ∨ θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo)), f i)
      = (∑ i ∈ (Finset.univ.filter (fun i : Fin N => (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ))), f i)
      + (∑ i ∈ (Finset.univ.filter (fun i : Fin N => θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo)), f i) := by
  classical
  let P : Fin N → Prop := fun i => (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ)
  let Q : Fin N → Prop := fun i => θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo
  have hpq : ∀ i, ¬ (P i ∧ Q i) := by
    intro i h
    rcases h with ⟨hp, hq⟩
    have hn0 : n ≠ 0 := n_ne_zero_of_arc F i
    have hpi : 0 < Real.pi / (n : ℝ) := by
      have : 0 < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero hn0)
      positivity
    have hle1 : (F.arc i).hi + Real.pi / (n : ℝ) ≤ (F.arc i).lo := by linarith
    have hle2 : (F.arc i).lo ≤ (F.arc i).hi := Family.Grid.lo_le_hi (F.arc i)
    linarith
  have hdisj : Disjoint (Finset.univ.filter P) (Finset.univ.filter Q) := by
    rw [Finset.disjoint_left]
    intro i hiP hiQ
    exact (hpq i) ⟨(Finset.mem_filter.mp hiP).2, (Finset.mem_filter.mp hiQ).2⟩
  have hunion : Finset.univ.filter (fun i => P i ∨ Q i) =
      (Finset.univ.filter P) ∪ (Finset.univ.filter Q) := by
    ext i
    constructor
    · intro h
      have hi : P i ∨ Q i := (Finset.mem_filter.mp h).2
      rcases hi with hp | hq
      · exact Finset.mem_union.mpr (Or.inl (by simpa [P] using (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hp⟩)))
      · exact Finset.mem_union.mpr (Or.inr (by simpa [Q] using (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hq⟩)))
    · intro h
      rcases Finset.mem_union.mp h with h | h
      · exact (Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inl (by simpa [P] using (Finset.mem_filter.mp h).2)⟩)
      · exact (Finset.mem_filter.mpr ⟨Finset.mem_univ i, Or.inr (by simpa [Q] using (Finset.mem_filter.mp h).2)⟩)
  -- rewrite the left sum as a union of filters then split
  have hleft : (∑ i ∈ (Finset.univ.filter (fun i => P i ∨ Q i)), f i)
      = (∑ i ∈ (Finset.univ.filter (fun i => P i)), f i) + (∑ i ∈ (Finset.univ.filter (fun i => Q i)), f i) := by
    rw [hunion]
    rw [Finset.sum_union hdisj]
  -- P and Q are defs of the predicates in the goal
  simpa [P, Q] using hleft

/-- erasing i0 is contained in the far filter (θ0 ∈ arc i0) -/
lemma erase_subset_far (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i0 : Fin N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2)
    (hmem : θ0 ∈ Set.Icc (F.arc i0).lo (F.arc i0).hi) :
    (Finset.univ.erase i0) ⊆ (Finset.univ.filter (fun i : Fin N =>
        (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ) ∨ θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo)) := by
  classical
  intro i hi
  have hfar := erase_mem_far n N hn16 F i0 hmem i hi
  exact (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hfar⟩)

/-- `Σ_{i ≠ i0}|C_i| ≤ 2/π` when θ0 ∈ arc i0 -/
lemma erase_C_sum_le (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (i0 : Fin N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2)
    (hmem : θ0 ∈ Set.Icc (F.arc i0).lo (F.arc i0).hi) :
    (∑ i ∈ (Finset.univ.erase i0), |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|)
      ≤ 2 / Real.pi := by
  classical
  have hpart : (∑ i ∈ (Finset.univ.erase i0), |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|)
      ≤ ∑ i ∈ (Finset.univ.filter (fun i : Fin N =>
          (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ) ∨ θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo)),
          |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ| := by
    exact Finset.sum_le_sum_of_subset_of_nonneg (erase_subset_far n N hn16 F i0 hθ0a hθ0b hmem)
      (by intro i hi hmem; exact abs_nonneg _)
  calc
    (∑ i ∈ (Finset.univ.erase i0), |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|)
        ≤ ∑ i ∈ (Finset.univ.filter (fun i : Fin N =>
            (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ) ∨ θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo)),
            |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ| := hpart
    _ = (∑ i ∈ (Finset.univ.filter (fun i : Fin N => (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ))),
            |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|)
        + (∑ i ∈ (Finset.univ.filter (fun i : Fin N => θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo)),
            |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|) := by
        exact far_sum_split n N F (fun i => |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|)
    _ ≤ 1 / Real.pi + 1 / Real.pi := by
        exact add_le_add (S5C3L.left_bound n N hn16 F hθ0a hθ0b)
          (S5C3R.right_bound n N hn16 F hθ0a hθ0b)
    _ = 2 / Real.pi := by ring

/-- `|a + b| ≥ |a| − |b|` -/
lemma abs_add_ge_sub (a b : ℝ) : |a + b| ≥ |a| - |b| := by
  have h := abs_add_le a b
  have h2 : |a| ≤ |a + b| + |b| := by
    have h3 : |a| = |(a + b) + (-b)| := by
      congr 1
      ring
    rw [h3]
    simpa using (abs_add_le (a + b) (-b))
  linarith

/-- extracting the i0 term from a colored weighted sum -/
lemma sumC_single_ge (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (α : Fin N → ℝ)
    (hα : IsColoring α) (i0 : Fin N) {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2)
    (hmem : θ0 ∈ Set.Icc (F.arc i0).lo (F.arc i0).hi) :
    (4 / 3 : ℝ) - 2 / Real.pi ≤
      |∑ i : Fin N, α i * (∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ)| := by
  let C : Fin N → ℝ := fun i => ∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ
  let R : Fin N → ℝ := fun i => ∑ j ∈ (Finset.univ.erase i), (α j * C j)
  have hmain0 : |∑ i : Fin N, α i * C i| ≥ |α i0 * C i0| - |∑ j ∈ (Finset.univ.erase i0), α j * C j| := by
    -- Σ = α_{i0} C_{i0} + Σ_{erase}
    have hsplit0 : (∑ i : Fin N, α i * C i) = α i0 * C i0 + (∑ j ∈ (Finset.univ.erase i0), α j * C j) := by
      classical
      have hsa := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin N)))
        (f := fun x : Fin N => α x * C x) (a := i0) (Finset.mem_univ i0)
      rw [← hsa]
      ring
    rw [hsplit0]
    exact abs_add_ge_sub (α i0 * C i0) (∑ j ∈ (Finset.univ.erase i0), α j * C j)
  have hC0 : |α i0 * C i0| = |C i0| := by
    rw [abs_mul]
    have hαabs : |α i0| = 1 := coloring_abs hα i0
    rw [hαabs, one_mul]
  have hlower : (4 / 3 : ℝ) ≤ |C i0| := by
    have hlow' : (4 / 3 : ℝ) ≤ C i0 := by
      dsimp [C]
      exact si_in_lower hn16 F i0 hmem
    have hpos : 0 ≤ C i0 := by linarith
    rw [abs_of_nonneg hpos]
    exact hlow'
  have herase : |∑ j ∈ (Finset.univ.erase i0), α j * C j| ≤ 2 / Real.pi := by
    calc
      |∑ j ∈ (Finset.univ.erase i0), α j * C j|
          ≤ ∑ j ∈ (Finset.univ.erase i0), |α j * C j| := by
            exact Finset.abs_sum_le_sum_abs (s := (Finset.univ.erase i0)) (f := fun j => α j * C j)
      _ = ∑ j ∈ (Finset.univ.erase i0), |C j| := by
          apply Finset.sum_congr rfl
          intro j hj
          rw [abs_mul]
          rw [coloring_abs hα j, one_mul]
      _ ≤ 2 / Real.pi := by
          dsimp [C]
          exact erase_C_sum_le n N hn16 F i0 hθ0a hθ0b hmem
  have hcalc : |α i0 * C i0| - |∑ j ∈ (Finset.univ.erase i0), α j * C j| ≥ 4 / 3 - 2 / Real.pi := by
    linarith
  -- get the α-part back to the actual sum with C defined
  dsimp [C] at hmain0
  linarith

/-- |Tθ| ≥ 3/5 when θ0 lies in arc i0 -/
lemma Tθ_low (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (α : Fin N → ℝ)
    (hα : IsColoring α) {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2)
    (i0 : Fin N) (hmem : θ0 ∈ Set.Icc (F.arc i0).lo (F.arc i0).hi) :
    (3 / 5 : ℝ) ≤ |Tθ n N F α θ0| := by
  let C : Fin N → ℝ := fun i => ∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ
  let e : Fin N → ℝ := fun i => (∫ θ in (F.arc i).lo..(F.arc i).hi, DK1 n θ0 θ)
      - (∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ)
  let B : Fin N → ℝ := fun i => ∫ θ in (F.arc i).lo..(F.arc i).hi, DK2 n θ0 θ
  have hsplit := Tθ_split n N hn16 F α hθ0a hθ0b
  -- identity Tθ = Σ (αC + αe − αB)
  have hT : Tθ n N F α θ0 = (∑ i : Fin N, (α i * C i + α i * e i - α i * B i)) := by
    dsimp [C, e, B]
    rw [hsplit]
    -- show Σ(αC+αe−αB) = ΣαC + Σαe − ΣαB
    rw [Finset.sum_sub_distrib]
    rw [← Finset.sum_add_distrib]
  -- absolute value of a sum of three terms ≥ |ΣαC| − |Σαe| − |ΣαB|
  have hmain : |Tθ n N F α θ0| ≥
      |∑ i : Fin N, α i * C i| - |∑ i : Fin N, α i * e i| - |∑ i : Fin N, α i * B i| := by
    rw [hT]
    have hge := abs_sum_add_sub_ge (fun i : Fin N => α i * C i) (fun i => α i * e i) (fun i => -(α i * B i))
    -- |Σ(−αB)| = |ΣαB|
    have hh : |∑ i : Fin N, -(α i * B i)| = |∑ i : Fin N, α i * B i| := by
      have hneq : (∑ i : Fin N, -(α i * B i)) = -(∑ i : Fin N, α i * B i) := by
        simp [Finset.sum_neg_distrib]
      rw [hneq, abs_neg]
    have hge' : |(∑ i : Fin N, (α i * C i + α i * e i + -(α i * B i)))| ≥
        |∑ i : Fin N, α i * C i| - |∑ i : Fin N, α i * e i| - |∑ i : Fin N, α i * B i| := by
      rw [hh] at hge
      simpa using hge
    exact hge'
  -- bound the two error sums by 1/50 each, and the C-sum from below
  have hB : |∑ i : Fin N, α i * B i| ≤ 1 / 50 := by
    calc
      |∑ i : Fin N, α i * B i| ≤ ∑ i : Fin N, |α i * B i| := by
            simpa using (Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset (Fin N))) (f := fun i => α i * B i))
      _ = ∑ i : Fin N, |B i| := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [abs_mul, coloring_abs hα i, one_mul]
      _ ≤ 1 / 50 := by
            dsimp [B]
            exact S5C1.claim1_bound n N hn16 F hθ0a hθ0b
  have he : |∑ i : Fin N, α i * e i| ≤ 1 / 50 := by
    calc
      |∑ i : Fin N, α i * e i| ≤ ∑ i : Fin N, |α i * e i| := by
            simpa using (Finset.abs_sum_le_sum_abs (s := (Finset.univ : Finset (Fin N))) (f := fun i => α i * e i))
      _ = ∑ i : Fin N, |e i| := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [abs_mul, coloring_abs hα i, one_mul]
      _ ≤ 1 / 50 := by
            dsimp [e]
            exact claim2_bound n N hn16 F hθ0a hθ0b
  have hC : |∑ i : Fin N, α i * C i| ≥ 4 / 3 - 2 / Real.pi := by
    dsimp [C]
    exact sumC_single_ge n N hn16 F α hα i0 hθ0a hθ0b hmem
  -- numeric combination
  have hnum : (4 / 3 : ℝ) - 2 / Real.pi - 1 / 50 - 1 / 50 ≥ 3 / 5 := by
    have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    have h2p : (2 / Real.pi : ℝ) ≤ 2 / 3 := by
      have hpi0 : 0 < Real.pi := Real.pi_pos
      rw [div_le_div_iff₀ hpi0 (by norm_num : (0:ℝ) < 3)]
      nlinarith
    have : (4/3:ℝ) - 2/Real.pi - 1/50 - 1/50 ≥ (4/3:ℝ) - 2/3 - 1/25 := by linarith
    linarith
  have hfin : |Tθ n N F α θ0| ≥ (4 / 3 : ℝ) - 2 / Real.pi - 1 / 50 - 1 / 50 := by
    linarith
  linarith


/-- `i` is near θ0 (within π/n) -/
def isNear (n : ℕ) (θ0 : ℝ) (hi lo : ℝ) : Prop :=
  θ0 - Real.pi / (n : ℝ) < hi ∧ lo < θ0 + Real.pi / (n : ℝ)


/-- an arc not containing θ0 lies entirely left or right of θ0 -/
lemma arc_left_or_right_of_not_mem (n N : ℕ) (F : Family.Quad n N) {θ0 : ℝ}
    (i : Fin N) (hno : θ0 ∉ Set.Icc (F.arc i).lo (F.arc i).hi) :
    (F.arc i).hi < θ0 ∨ θ0 < (F.arc i).lo := by
  by_cases h1 : θ0 < (F.arc i).lo
  · right; exact h1
  · left
    have hlo : (F.arc i).lo ≤ θ0 := le_of_not_gt h1
    have hhi : ¬ θ0 ≤ (F.arc i).hi := by
      intro h
      exact hno ⟨hlo, h⟩
    exact lt_of_not_ge hhi


/-- at most one near arc lies entirely left of θ0 -/
lemma left_near_at_most_one (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    {θ0 : ℝ} :
    ∀ i j : Fin N, i ≠ j →
      isNear n θ0 (F.arc i).hi (F.arc i).lo → isNear n θ0 (F.arc j).hi (F.arc j).lo →
      ¬ ((F.arc i).hi < θ0 ∧ (F.arc j).hi < θ0) := by
  intro i j hij ni nj hboth
  rcases hboth with ⟨hLi, hLj⟩
  rcases arc_left_or_right hn16 F j i hij with hlt | hlt
  · -- i left of j: hi_i ≤ lo_j − π/n
    have hθlo : θ0 < (F.arc j).lo := by linarith [ni.1, hlt]
    have hle : (F.arc j).lo ≤ (F.arc j).hi := Family.Grid.lo_le_hi (F.arc j)
    have : (F.arc j).hi < θ0 := hLj
    linarith
  · -- j left of i: hi_j + π/n ≤ lo_i
    have hθlo : θ0 < (F.arc i).lo := by linarith [nj.1, hlt]
    have hle : (F.arc i).lo ≤ (F.arc i).hi := Family.Grid.lo_le_hi (F.arc i)
    have : (F.arc i).hi < θ0 := hLi
    linarith

/-- at most one near arc lies entirely right of θ0 -/
lemma right_near_at_most_one (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    {θ0 : ℝ} :
    ∀ i j : Fin N, i ≠ j →
      isNear n θ0 (F.arc i).hi (F.arc i).lo → isNear n θ0 (F.arc j).hi (F.arc j).lo →
      ¬ (θ0 < (F.arc i).lo ∧ θ0 < (F.arc j).lo) := by
  intro i j hij ni nj hboth
  rcases hboth with ⟨hRi, hRj⟩
  rcases arc_left_or_right hn16 F j i hij with hlt | hlt
  · -- i left of j: hi_i ≤ lo_j − π/n
    -- i right of θ0: θ0 < lo_i ≤ hi_i ≤ lo_j − π/n; near(j): lo_j < θ0 + π/n
    have hθ : θ0 < (F.arc i).lo := hRi
    have hle : (F.arc i).lo ≤ (F.arc i).hi := Family.Grid.lo_le_hi (F.arc i)
    have : (F.arc i).hi ≤ (F.arc j).lo - Real.pi / (n : ℝ) := hlt
    have hnear : (F.arc j).lo < θ0 + Real.pi / (n : ℝ) := nj.2
    linarith
  · -- j left of i: hi_j + π/n ≤ lo_i
    have hθ : θ0 < (F.arc j).lo := hRj
    have hle : (F.arc j).lo ≤ (F.arc j).hi := Family.Grid.lo_le_hi (F.arc j)
    have hnear : (F.arc i).lo < θ0 + Real.pi / (n : ℝ) := ni.2
    -- hi_j + π/n ≤ lo_i and hi_j ≥ lo_j > θ0: θ0 + π/n < lo_i
    linarith


/-- at most two arcs are within π/n of a point that is in no arc -/
lemma near_le_two (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) {θ0 : ℝ}
    (hno : ∀ i : Fin N, θ0 ∉ Set.Icc (F.arc i).lo (F.arc i).hi) :
    ∀ i j k : Fin N,
      isNear n θ0 (F.arc i).hi (F.arc i).lo → isNear n θ0 (F.arc j).hi (F.arc j).lo →
      isNear n θ0 (F.arc k).hi (F.arc k).lo → i = j ∨ i = k ∨ j = k := by
  intro i j k ni nj nk
  by_contra hd
  have hij : i ≠ j := by intro h; apply hd; left; exact h
  have hik : i ≠ k := by intro h; apply hd; right; left; exact h
  have hjk : j ≠ k := by intro h; apply hd; right; right; exact h
  have hsi := arc_left_or_right_of_not_mem n N F i (hno i)
  have hsj := arc_left_or_right_of_not_mem n N F j (hno j)
  have hsk := arc_left_or_right_of_not_mem n N F k (hno k)
  rcases hsi with li | ri
  · rcases hsj with lj | rj
    · exact (left_near_at_most_one n N hn16 F i j hij ni nj) ⟨li, lj⟩
    · rcases hsk with lk | rk
      · exact (left_near_at_most_one n N hn16 F i k hik ni nk) ⟨li, lk⟩
      · exact (right_near_at_most_one n N hn16 F j k hjk nj nk) ⟨rj, rk⟩
  · rcases hsj with lj | rj
    · rcases hsk with lk | rk
      · exact (left_near_at_most_one n N hn16 F j k hjk nj nk) ⟨lj, lk⟩
      · exact (right_near_at_most_one n N hn16 F i k hik ni nk) ⟨ri, rk⟩
    · exact (right_near_at_most_one n N hn16 F i j hij ni nj) ⟨ri, rj⟩


/-- far-filter sum of |C_i| ≤ 2/π -/
lemma farC_sum_le (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    (∑ i ∈ (Finset.univ.filter (fun i : Fin N =>
        (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ) ∨ θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo)),
        |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|)
      ≤ 2 / Real.pi := by
  classical
  calc
    (∑ i ∈ (Finset.univ.filter (fun i : Fin N =>
        (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ) ∨ θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo)),
        |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|)
        = (∑ i ∈ (Finset.univ.filter (fun i : Fin N => (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ))),
            |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|)
        + (∑ i ∈ (Finset.univ.filter (fun i : Fin N => θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo)),
            |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|) := by
        exact far_sum_split n N F (fun i => |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|)
    _ ≤ 1 / Real.pi + 1 / Real.pi := by
        exact add_le_add (S5C3L.left_bound n N hn16 F hθ0a hθ0b)
          (S5C3R.right_bound n N hn16 F hθ0a hθ0b)
    _ = 2 / Real.pi := by ring

/-- `Σ_i |C_i| ≤ 4 + 2/π` -/
lemma sumC_bound (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N)
    {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    (∑ i : Fin N, |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|) ≤ 4 + 2 / Real.pi := by
  classical
  by_cases hc : ∃ i0 : Fin N, θ0 ∈ Set.Icc (F.arc i0).lo (F.arc i0).hi
  · rcases hc with ⟨i0, hmem⟩
    have hsplit : (∑ i : Fin N, |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|)
        = |∫ θ in (F.arc i0).lo..(F.arc i0).hi, LK n θ0 θ|
          + (∑ i ∈ (Finset.univ.erase i0), |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|) := by
      have hsa := Finset.sum_erase_add (s := (Finset.univ : Finset (Fin N)))
        (f := fun i : Fin N => |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|)
        (a := i0) (Finset.mem_univ i0)
      rw [← hsa]
      ring
    rw [hsplit]
    have h4 : |∫ θ in (F.arc i0).lo..(F.arc i0).hi, LK n θ0 θ| ≤ 4 := by
      have hpos : 0 ≤ ∫ θ in (F.arc i0).lo..(F.arc i0).hi, LK n θ0 θ := by
        have hlo : (4 / 3 : ℝ) ≤ ∫ θ in (F.arc i0).lo..(F.arc i0).hi, LK n θ0 θ := si_in_lower hn16 F i0 hmem
        linarith
      rw [abs_of_nonneg hpos]
      exact si_in_upper hn16 F i0 hmem
    have h2 : (∑ i ∈ (Finset.univ.erase i0), |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|) ≤ 2 / Real.pi :=
      erase_C_sum_le n N hn16 F i0 hθ0a hθ0b hmem
    linarith
  · have hno : ∀ i : Fin N, θ0 ∉ Set.Icc (F.arc i).lo (F.arc i).hi := by
      intro i hi
      exact hc ⟨i, hi⟩
    -- split the sum into far (≤ 2/π) and near arcs; near arcs have |C| ≤ 2 and there are at most two
    let sFar : Finset (Fin N) := Finset.univ.filter (fun i : Fin N =>
        (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ) ∨ θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo)
    let sNear : Finset (Fin N) := Finset.univ.filter (fun i : Fin N => ¬
        ((F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ) ∨ θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo))
    have hpart : (∑ i : Fin N, |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|)
        = (∑ i ∈ sFar, |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|)
        + (∑ i ∈ sNear, |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|) := by
      -- sFar ∪ sNear = univ, disjoint
      have hdisj : Disjoint sFar sNear := by
        rw [Finset.disjoint_left]
        intro i hiFar hiNear
        exact (Finset.mem_filter.mp hiNear).2 (Finset.mem_filter.mp hiFar).2
      have hunion : sFar ∪ sNear = Finset.univ := by
        ext i
        constructor
        · intro h; exact Finset.mem_univ i
        · intro h
          by_cases hf : (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ) ∨ θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo
          · exact Finset.mem_union.mpr (Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hf⟩))
          · exact Finset.mem_union.mpr (Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hf⟩))
      calc
        (∑ i : Fin N, |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|)
            = ∑ i ∈ (sFar ∪ sNear), |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ| := by
                rw [hunion]
            _ = (∑ i ∈ sFar, |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|)
              + (∑ i ∈ sNear, |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|) := by
                rw [Finset.sum_union hdisj]
    rw [hpart]
    have hFar : (∑ i ∈ sFar, |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|) ≤ 2 / Real.pi := by
      dsimp [sFar]
      exact farC_sum_le n N hn16 F hθ0a hθ0b
    have hNearSum : (∑ i ∈ sNear, |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|) ≤ 4 := by
      -- each near arc has |C| ≤ 2 (since none contains θ0) and there are at most two
      -- For each near arc, si_out_abs applies:
      have hNear_abs : ∀ i ∈ sNear, |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ| ≤ 2 := by
        intro i hi
        have hnf : ¬ ((F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ) ∨ θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo) :=
          (Finset.mem_filter.mp hi).2
        -- since θ0 ∉ arc, si_out_abs applies:
        apply si_out_abs hn16 F i
        -- need hout: θ0 ≤ lo ∨ hi ≤ θ0
        have hs := arc_left_or_right_of_not_mem n N F i (hno i)
        rcases hs with hlt | hgt
        · right; exact hlt.le
        · left; exact hgt.le
      -- bound the sum by 2 * (number of near arcs) ≤ 4; number of near arcs ≤ 2
      have hnum : ∀ i j k : Fin N, i ∈ sNear → j ∈ sNear → k ∈ sNear → i = j ∨ i = k ∨ j = k := by
        intro i j k hsi hsj hsk
        have hni : isNear n θ0 (F.arc i).hi (F.arc i).lo := by
          have hnf : ¬ ((F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ) ∨ θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo) := (Finset.mem_filter.mp hsi).2
          by_cases h1 : (F.arc i).hi ≤ θ0 - Real.pi / (n : ℝ)
          · exact False.elim (hnf (Or.inl h1))
          · by_cases h2 : θ0 + Real.pi / (n : ℝ) ≤ (F.arc i).lo
            · exact False.elim (hnf (Or.inr h2))
            · have hh : θ0 - Real.pi / (n : ℝ) < (F.arc i).hi := lt_of_not_ge h1
              have hh2 : (F.arc i).lo < θ0 + Real.pi / (n : ℝ) := lt_of_not_ge h2
              exact ⟨hh, hh2⟩
        have hnj : isNear n θ0 (F.arc j).hi (F.arc j).lo := by
          have hnf : ¬ ((F.arc j).hi ≤ θ0 - Real.pi / (n : ℝ) ∨ θ0 + Real.pi / (n : ℝ) ≤ (F.arc j).lo) := (Finset.mem_filter.mp hsj).2
          by_cases h1 : (F.arc j).hi ≤ θ0 - Real.pi / (n : ℝ)
          · exact False.elim (hnf (Or.inl h1))
          · by_cases h2 : θ0 + Real.pi / (n : ℝ) ≤ (F.arc j).lo
            · exact False.elim (hnf (Or.inr h2))
            · exact ⟨lt_of_not_ge h1, lt_of_not_ge h2⟩
        have hnk : isNear n θ0 (F.arc k).hi (F.arc k).lo := by
          have hnf : ¬ ((F.arc k).hi ≤ θ0 - Real.pi / (n : ℝ) ∨ θ0 + Real.pi / (n : ℝ) ≤ (F.arc k).lo) := (Finset.mem_filter.mp hsk).2
          by_cases h1 : (F.arc k).hi ≤ θ0 - Real.pi / (n : ℝ)
          · exact False.elim (hnf (Or.inl h1))
          · by_cases h2 : θ0 + Real.pi / (n : ℝ) ≤ (F.arc k).lo
            · exact False.elim (hnf (Or.inr h2))
            · exact ⟨lt_of_not_ge h1, lt_of_not_ge h2⟩
        exact near_le_two n N hn16 F hno i j k hni hnj hnk
      -- sum over sNear of quantities ≤ 2, with card ≤ 2
      have hsum2 : (∑ i ∈ sNear, |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|) ≤ 2 * (sNear.card : ℝ) := by
        calc
          (∑ i ∈ sNear, |∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ|)
              ≤ ∑ i ∈ sNear, 2 := by
                  apply Finset.sum_le_sum
                  intro i hi
                  exact hNear_abs i hi
          _ = 2 * (sNear.card : ℝ) := by
              rw [Finset.sum_const]
              simp [nsmul_eq_mul]
              ring
      have hcard : sNear.card ≤ 2 := by
        by_contra hc'
        have hbig : 3 ≤ sNear.card := by omega
        have h1 : 1 ≤ sNear.card := by omega
        have ha : ∃ a, a ∈ sNear := Finset.card_pos.mp (by omega)
        rcases ha with ⟨a, ha⟩
        have hb_ : 1 ≤ (sNear.erase a).card := by
          rw [Finset.card_erase_of_mem ha]
          omega
        have hb : ∃ b, b ∈ sNear.erase a := Finset.card_pos.mp hb_
        rcases hb with ⟨b, hb2⟩
        have hbS : b ∈ sNear := (Finset.mem_erase.mp hb2).2
        have hba : b ≠ a := (Finset.mem_erase.mp hb2).1
        have hc_ : 1 ≤ ((sNear.erase a).erase b).card := by
          rw [Finset.card_erase_of_mem hb2]
          rw [Finset.card_erase_of_mem ha]
          omega
        have hce : ∃ c, c ∈ (sNear.erase a).erase b := Finset.card_pos.mp hc_
        rcases hce with ⟨c, hc3⟩
        have hcS : c ∈ sNear := (Finset.mem_erase.mp (Finset.mem_erase.mp hc3).2).2
        have hca : c ≠ a := (Finset.mem_erase.mp (Finset.mem_erase.mp hc3).2).1
        have hcb : c ≠ b := (Finset.mem_erase.mp hc3).1
        rcases hnum a b c ha hbS hcS with h | h | h
        · exact hba h.symm
        · exact hca h.symm
        · exact hcb h.symm
      have h2 : 2 * (sNear.card : ℝ) ≤ 4 := by
        have : (sNear.card : ℝ) ≤ 2 := by exact_mod_cast hcard
        nlinarith
      linarith
    linarith



/-- |Tθ| ≤ 8 when θ0 is in the quadrant -/
lemma Tθ_high (n N : ℕ) (hn16 : 2 ^ 16 ≤ n) (F : Family.Quad n N) (α : Fin N → ℝ)
    (hα : IsColoring α) {θ0 : ℝ} (hθ0a : 0 ≤ θ0) (hθ0b : θ0 ≤ Real.pi / 2) :
    |Tθ n N F α θ0| ≤ 8 := by
  let C : Fin N → ℝ := fun i => ∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ
  let e : Fin N → ℝ := fun i => (∫ θ in (F.arc i).lo..(F.arc i).hi, DK1 n θ0 θ)
      - (∫ θ in (F.arc i).lo..(F.arc i).hi, LK n θ0 θ)
  let B : Fin N → ℝ := fun i => ∫ θ in (F.arc i).lo..(F.arc i).hi, DK2 n θ0 θ
  have hsplit := Tθ_split n N hn16 F α hθ0a hθ0b
  have hT : Tθ n N F α θ0 = (∑ i : Fin N, (α i * C i + α i * e i - α i * B i)) := by
    dsimp [C, e, B]
    rw [hsplit]
    rw [Finset.sum_sub_distrib]
    rw [← Finset.sum_add_distrib]
  have htri : |Tθ n N F α θ0| ≤
      |∑ i : Fin N, α i * C i| + |∑ i : Fin N, α i * e i| + |∑ i : Fin N, α i * B i| := by
    have h1 : |∑ i : Fin N, (α i * C i + α i * e i - α i * B i)|
        ≤ |∑ i : Fin N, (α i * C i + α i * e i)| + |∑ i : Fin N, α i * B i| := by
      have hs : (∑ i : Fin N, (α i * C i + α i * e i - α i * B i))
          = (∑ i : Fin N, (α i * C i + α i * e i)) - (∑ i : Fin N, α i * B i) := by
        rw [Finset.sum_sub_distrib]
      rw [hs]
      simpa [sub_eq_add_neg, abs_neg] using
        (abs_add_le (∑ i : Fin N, (α i * C i + α i * e i)) (-(∑ i : Fin N, α i * B i)))
    have h2 : |∑ i : Fin N, (α i * C i + α i * e i)|
        ≤ |∑ i : Fin N, α i * C i| + |∑ i : Fin N, α i * e i| := by
      have hs2 : (∑ i : Fin N, (α i * C i + α i * e i))
          = (∑ i : Fin N, α i * C i) + (∑ i : Fin N, α i * e i) := by
        rw [← Finset.sum_add_distrib]
      rw [hs2]
      exact abs_add_le (∑ i : Fin N, α i * C i) (∑ i : Fin N, α i * e i)
    calc
      |Tθ n N F α θ0| = |∑ i : Fin N, (α i * C i + α i * e i - α i * B i)| := by rw [hT]
      _ ≤ |∑ i : Fin N, (α i * C i + α i * e i)| + |∑ i : Fin N, α i * B i| := h1
      _ ≤ |∑ i : Fin N, α i * C i| + |∑ i : Fin N, α i * e i| + |∑ i : Fin N, α i * B i| := by
          exact add_le_add h2 (le_refl (|∑ i : Fin N, α i * B i|))
  have hB : |∑ i : Fin N, α i * B i| ≤ 1 / 50 := by
    calc
      |∑ i : Fin N, α i * B i| ≤ ∑ i : Fin N, |α i * B i| := abs_sum_le_sum_abs (fun i => α i * B i)
      _ = ∑ i : Fin N, |B i| := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [abs_mul, coloring_abs hα i, one_mul]
      _ ≤ 1 / 50 := by
            dsimp [B]
            exact S5C1.claim1_bound n N hn16 F hθ0a hθ0b
  have he : |∑ i : Fin N, α i * e i| ≤ 1 / 50 := by
    calc
      |∑ i : Fin N, α i * e i| ≤ ∑ i : Fin N, |α i * e i| := abs_sum_le_sum_abs (fun i => α i * e i)
      _ = ∑ i : Fin N, |e i| := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [abs_mul, coloring_abs hα i, one_mul]
      _ ≤ 1 / 50 := by
            dsimp [e]
            exact claim2_bound n N hn16 F hθ0a hθ0b
  have hC : |∑ i : Fin N, α i * C i| ≤ 4 + 2 / Real.pi := by
    calc
      |∑ i : Fin N, α i * C i| ≤ ∑ i : Fin N, |α i * C i| := abs_sum_le_sum_abs (fun i => α i * C i)
      _ = ∑ i : Fin N, |C i| := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [abs_mul, coloring_abs hα i, one_mul]
      _ ≤ 4 + 2 / Real.pi := by
            dsimp [C]
            exact sumC_bound n N hn16 F hθ0a hθ0b
  have hnum : (4 : ℝ) + 2 / Real.pi + 1 / 50 + 1 / 50 ≤ 8 := by
    have hpi : (3 : ℝ) ≤ Real.pi := Real.pi_gt_three.le
    have h2p : (2 / Real.pi : ℝ) ≤ 2 / 3 := by
      have hpi0 : 0 < Real.pi := Real.pi_pos
      rw [div_le_div_iff₀ hpi0 (by norm_num : (0 : ℝ) < 3)]
      nlinarith
    have h1 : (4 : ℝ) + 2 / Real.pi + 1 / 50 + 1 / 50 ≤ 4 + (2 : ℝ) / 3 + 1 / 25 := by
      linarith
    have h2 : 4 + (2 : ℝ) / 3 + 1 / 25 ≤ 8 := by norm_num
    linarith
  linarith

/-- Lower bound `|ŝ| ≥ (3/5)·K·√n` on the union of the arcs (quadrant). -/
theorem sHat_lower (n N : ℕ) (hn : 2 ^ 16 ≤ n) (K : ℝ) (hK0 : 0 ≤ K)
    (F : Family.Quad n N) (α : Fin N → ℝ) (hα : IsColoring α) :
    ∀ θ0 : ℝ, θ0 ∈ Set.Icc 0 (Real.pi / 2) → θ0 ∈ F.union →
      (3 / 5 : ℝ) * K * Real.sqrt (n : ℝ) ≤ |sHat n N K F α θ0| := by
  intro θ0 hθ0 hunion
  rcases hθ0 with ⟨hθ0a, hθ0b⟩
  rw [Family.Quad.union_def] at hunion
  rcases hunion with ⟨i0, hlo, hhi⟩
  have hmem : θ0 ∈ Set.Icc (F.arc i0).lo (F.arc i0).hi := ⟨hlo, hhi⟩
  have hlow := Tθ_low n N hn F α hα hθ0a hθ0b i0 hmem
  have hsq : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hKsq : 0 ≤ K * Real.sqrt (n : ℝ) := mul_nonneg hK0 hsq
  have hs : sHat n N K F α θ0 = K * Real.sqrt (n : ℝ) * Tθ n N F α θ0 := sHat_eq_T n N K F α θ0
  rw [hs, abs_mul, abs_of_nonneg hKsq]
  calc
    (3 / 5 : ℝ) * K * Real.sqrt (n : ℝ) = (K * Real.sqrt (n : ℝ)) * (3 / 5 : ℝ) := by ring
    _ ≤ (K * Real.sqrt (n : ℝ)) * |Tθ n N F α θ0| := mul_le_mul_of_nonneg_left hlow hKsq

/-- Upper bound `|ŝ| ≤ 8·K·√n` on the quadrant. -/
theorem sHat_upper (n N : ℕ) (hn : 2 ^ 16 ≤ n) (K : ℝ) (hK0 : 0 ≤ K)
    (F : Family.Quad n N) (α : Fin N → ℝ) (hα : IsColoring α) :
    ∀ θ0 : ℝ, θ0 ∈ Set.Icc 0 (Real.pi / 2) →
      |sHat n N K F α θ0| ≤ 8 * K * Real.sqrt (n : ℝ) := by
  intro θ0 hθ0
  rcases hθ0 with ⟨hθ0a, hθ0b⟩
  have hhigh := Tθ_high n N hn F α hα hθ0a hθ0b
  have hsq : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hKsq : 0 ≤ K * Real.sqrt (n : ℝ) := mul_nonneg hK0 hsq
  have hs : sHat n N K F α θ0 = K * Real.sqrt (n : ℝ) * Tθ n N F α θ0 := sHat_eq_T n N K F α θ0
  rw [hs, abs_mul, abs_of_nonneg hKsq]
  calc
    (K * Real.sqrt (n : ℝ)) * |Tθ n N F α θ0| ≤ (K * Real.sqrt (n : ℝ)) * 8 := by
        exact mul_le_mul_of_nonneg_left hhigh hKsq
    _ = 8 * K * Real.sqrt (n : ℝ) := by ring
