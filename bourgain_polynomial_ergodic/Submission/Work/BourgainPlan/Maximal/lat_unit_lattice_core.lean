import Mathlib
import Submission.Work.BourgainPlan.Maximal.subtwoLatDefs
import Submission.Work.IonescuWainger.young_count_lp
import Submission.Work.Maximal.mstWide_defs

/-!
# The unit-lattice maximal bound for band-`1/4` functions

`lat_unit_lattice_core`: given the pointwise domination of the centred Hardy--Littlewood maximal
function of a continuous band-`1/4` integrable `H` by the centred discrete maximal function of its
lattice values plus a lattice convolution with the kernel `latKernel u = (1+|u|)^{-2}`, and given
the `ℓ^r`-boundedness (`r > 1`) of the centred discrete maximal function on `ℤ`, we deduce the
**unit-lattice `ℓ^r` bound**: for every real shift `s`,

`∑'_x (hlMax ‖H‖ (x - s))^r ≤ C^r ∑'_x ‖H x‖^r`,

with `C` independent of `H` and `s`.

The only extra ingredient is that the *sampled* kernel `j ↦ latKernel (x - s - j)` is dominated by
the shift-independent, summable majorant `latKernelMajorant`, whose `ℓ¹` mass is finite; the
convolution step is the discrete Young inequality `Work.IonescuWainger.young_count_lp` and the
discrete maximal-function step is the hypothesis `hDisc`.
-/

namespace Work.BourgainPlan.Maximal

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

/-- The summable lattice majorant of the sampling kernel `latKernel u = (1+|u|)^{-2}`: for every
real shift `φ ∈ [0,1)` and every `k : ℤ`, `latKernel (k - φ) ≤ latKernelMajorant k`, and
`latKernelMajorant` is summable over `ℤ`. -/
def latKernelMajorant (k : ℤ) : ENNReal :=
  ENNReal.ofReal ((1 + max 0 (|(k : ℝ)| - 1)) ^ (-2 : ℝ))

/-- The sampled kernel is dominated by the shift-independent majorant. -/
lemma latKernelMajorant_sub_le (k : ℤ) {φ : ℝ} (hφ0 : 0 ≤ φ) (hφ1 : φ < 1) :
    latKernel ((k : ℝ) - φ) ≤ latKernelMajorant k := by
  have key : max 0 (|(k : ℝ)| - 1) ≤ |(k : ℝ) - φ| := by
    rcases le_or_gt k 0 with hk | hk
    · have hkR : (k : ℝ) ≤ 0 := by exact_mod_cast hk
      rw [abs_of_nonpos hkR, abs_of_nonpos (by linarith : (k : ℝ) - φ ≤ 0)]
      exact max_le (by linarith) (by linarith)
    · have hk1 : (1 : ℤ) ≤ k := by omega
      have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ)),
        abs_of_nonneg (by linarith : (0 : ℝ) ≤ (k : ℝ) - φ)]
      exact max_le (by linarith) (by linarith)
  have hpos : (0 : ℝ) < 1 + max 0 (|(k : ℝ)| - 1) := by
    have := le_max_left (0 : ℝ) (|(k : ℝ)| - 1); linarith
  have hle : (1 + max 0 (|(k : ℝ)| - 1)) ≤ 1 + |(k : ℝ) - φ| := by linarith
  calc latKernel ((k : ℝ) - φ) = ENNReal.ofReal ((1 + |(k : ℝ) - φ|) ^ (-2 : ℝ)) := rfl
    _ ≤ ENNReal.ofReal ((1 + max 0 (|(k : ℝ)| - 1)) ^ (-2 : ℝ)) :=
        ENNReal.ofReal_mono (Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num))
    _ = latKernelMajorant k := rfl

/-- A summable upper bound for the majorant's symbol. -/
lemma latKernelMajorant_le_aux (k : ℤ) :
    (1 + max 0 (|(k : ℝ)| - 1)) ^ (-2 : ℝ)
      ≤ ((|(k : ℝ)|) ^ (2 : ℝ))⁻¹ + ((|(k : ℝ) + 1|) ^ (2 : ℝ))⁻¹ := by
  rcases eq_or_ne k 0 with hk0 | hk0
  · rw [hk0]; norm_num
  · have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have h : (1 : ℤ) ≤ |k| := Int.one_le_abs hk0
      rw [← Int.cast_abs (R := ℝ) (a := k)]
      exact_mod_cast h
    have hmax : max 0 (|(k : ℝ)| - 1) = |(k : ℝ)| - 1 := max_eq_right (by linarith)
    rw [hmax, show 1 + (|(k : ℝ)| - 1) = |(k : ℝ)| by ring]
    rw [Real.rpow_neg (by linarith : (0 : ℝ) ≤ |(k : ℝ)|)]
    have hpos : (0 : ℝ) ≤ ((|(k : ℝ) + 1|) ^ (2 : ℝ))⁻¹ := by positivity
    linarith

/-- The shift-independent majorant of the sampled kernel is summable. -/
lemma summable_latKernelMajorant :
    Summable (fun k : ℤ => (1 + max 0 (|(k : ℝ)| - 1)) ^ (-2 : ℝ)) := by
  have hsum : Summable (fun k : ℤ => ((|(k : ℝ)|) ^ (2 : ℝ))⁻¹ + ((|(k : ℝ) + 1|) ^ (2 : ℝ))⁻¹) := by
    have h1 : Summable (fun k : ℤ => ((|(k : ℝ)|) ^ (2 : ℝ))⁻¹) := by
      have h := (Real.summable_one_div_int_add_rpow 0 2).mpr (by norm_num : (1 : ℝ) < 2)
      simpa [one_div] using h
    have h2 : Summable (fun k : ℤ => ((|(k : ℝ) + 1|) ^ (2 : ℝ))⁻¹) := by
      have h := (Real.summable_one_div_int_add_rpow 1 2).mpr (by norm_num : (1 : ℝ) < 2)
      simpa [one_div] using h
    exact h1.add h2
  refine Summable.of_nonneg_of_le (fun k => Real.rpow_nonneg (by positivity) _) (fun k => ?_) hsum
  exact latKernelMajorant_le_aux k

lemma latKernelMajorant_tsum_ne_top :
    (∑' k : ℤ, latKernelMajorant k) ≠ ⊤ := by
  simpa [latKernelMajorant] using Summable.tsum_ofReal_ne_top summable_latKernelMajorant

/-- Convolution with a kernel is symmetric on `ℤ`. -/
lemma tsum_mul_comm_sub (u v : ℤ → ENNReal) (m : ℤ) :
    (∑' j : ℤ, u j * v (m - j)) = ∑' j : ℤ, v j * u (m - j) := by
  have hsub : ∀ c : ℤ, m - (m - c) = c := fun c => by ring
  let e : ℤ ≃ ℤ := ⟨fun c => m - c, fun c => m - c, by intro c; simp, by intro c; simp⟩
  have h := Equiv.tsum_eq e (fun i : ℤ => u i * v (m - i))
  have hc : ∀ c : ℤ, e c = m - c := fun c => rfl
  simp only [hc, hsub] at h
  rw [← h]
  exact tsum_congr fun c => mul_comm (u (m - c)) (v c)

/-- `(a+b)^r ≤ 2^r (a^r + b^r)` in `ℝ≥0∞` for `r ≥ 0`. -/
lemma add_rpow_le_two_rpow_mul (a b : ENNReal) {r : ℝ} (hr : 0 ≤ r) :
    (a + b) ^ r ≤ (2 : ENNReal) ^ r * (a ^ r + b ^ r) := by
  have h1 : a + b ≤ (2 : ENNReal) * max a b := by
    rw [two_mul]
    exact add_le_add (le_max_left a b) (le_max_right a b)
  have h2 : (max a b) ^ r ≤ a ^ r + b ^ r := by
    rcases max_choice a b with h | h
    · rw [h]; exact le_add_right le_rfl
    · rw [h]; exact le_add_left le_rfl
  calc (a + b) ^ r ≤ ((2 : ENNReal) * max a b) ^ r := ENNReal.rpow_le_rpow h1 hr
    _ = (2 : ENNReal) ^ r * (max a b) ^ r := ENNReal.mul_rpow_of_nonneg _ _ hr
    _ ≤ (2 : ENNReal) ^ r * (a ^ r + b ^ r) := mul_le_mul_right h2 _

/-- `x ↦ ⌊x - s⌋` is a bijection of `ℤ` for every real `s`. -/
lemma floor_sub_bijective (s : ℝ) : Function.Bijective (fun x : ℤ => ⌊(x : ℝ) - s⌋) := by
  have hmono : StrictMono (fun x : ℤ => ⌊(x : ℝ) - s⌋) := by
    intro x y hxy
    have h1 : ((x : ℤ) : ℝ) + 1 ≤ (y : ℝ) := by
      have h : x + 1 ≤ y := by omega
      exact_mod_cast h
    have h2 : ((x : ℝ) - s) + ((1 : ℤ) : ℝ) ≤ (y : ℝ) - s := by
      push_cast; linarith
    have h3 : ⌊((x : ℝ) - s) + ((1 : ℤ) : ℝ)⌋ ≤ ⌊(y : ℝ) - s⌋ := Int.floor_mono h2
    rw [Int.floor_add_intCast] at h3
    change ⌊(x : ℝ) - s⌋ < ⌊(y : ℝ) - s⌋
    omega
  refine ⟨hmono.injective, ?_⟩
  intro n
  refine ⟨n + ⌈s⌉, ?_⟩
  have hc0 : (0 : ℝ) ≤ (⌈s⌉ : ℝ) - s := by
    have := Int.le_ceil s; linarith
  have hc1 : (⌈s⌉ : ℝ) - s < 1 := by
    have := Int.ceil_lt_add_one s; linarith
  have hfl : ⌊((⌈s⌉ : ℤ) : ℝ) - s⌋ = 0 := by
    rw [Int.floor_eq_zero_iff]
    exact ⟨hc0, hc1⟩
  calc ⌊(((n + ⌈s⌉ : ℤ)) : ℝ) - s⌋
      = ⌊(n : ℝ) + (((⌈s⌉ : ℤ) : ℝ) - s)⌋ := by
        congr 1
        push_cast
        ring
    _ = n + ⌊((⌈s⌉ : ℤ) : ℝ) - s⌋ := Int.floor_intCast_add n _
    _ = n := by rw [hfl]; ring

theorem lat_unit_lattice_core {r : ℝ} (hr : 1 < r)
    (hKernel : ∃ Cc : ℝ, 0 < Cc ∧ ∀ (H : ℝ → ℂ), Continuous H → MeasureTheory.Integrable H →
      (∀ ξ : ℝ, 1 / 4 < |ξ| → FourierTransform.fourier H ξ = 0) → ∀ t : ℝ,
      Work.Maximal.mstHlMax (fun y : ℝ => ENNReal.ofReal ‖H y‖) t
        ≤ ENNReal.ofReal Cc *
            (Work.BourgainPlan.Maximal.latDiscMaxC (fun j : ℤ => ‖H (j : ℝ)‖ₑ) ⌊t⌋
              + ∑' j : ℤ, ‖H (j : ℝ)‖ₑ * Work.BourgainPlan.Maximal.latKernel (t - (j : ℝ))))
    (hDisc : ∃ Cd : ℝ, 0 < Cd ∧ ∀ (a : ℤ → ENNReal),
      ∫⁻ x : ℤ, (Work.BourgainPlan.Maximal.latDiscMaxC a x) ^ r ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal Cd * ∫⁻ x : ℤ, (a x) ^ r ∂MeasureTheory.Measure.count) :
    ∃ C : ℝ, 0 < C ∧ ∀ (H : ℝ → ℂ), Continuous H → MeasureTheory.Integrable H →
      (∀ ξ : ℝ, 1 / 4 < |ξ| → FourierTransform.fourier H ξ = 0) → ∀ s : ℝ,
      (∑' x : ℤ, (Work.Maximal.mstHlMax (fun y : ℝ => ENNReal.ofReal ‖H y‖) ((x : ℝ) - s)) ^ r)
        ≤ ENNReal.ofReal (C ^ r) *
          ∑' x : ℤ, ENNReal.ofReal (‖H (x : ℝ)‖ ^ r) := by
  obtain ⟨Cc, hCcpos, hKernel⟩ := hKernel
  obtain ⟨Cd, hCdpos, hDisc⟩ := hDisc
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hr0 : 0 ≤ r := le_of_lt hrpos
  have hr1 : 1 ≤ r := le_of_lt hr
  have hMne : (∑' k : ℤ, latKernelMajorant k) ≠ ⊤ := latKernelMajorant_tsum_ne_top
  set M : ENNReal := ∑' k : ℤ, latKernelMajorant k with hMdef
  have hMne' : M ≠ ⊤ := by rw [hMdef]; exact hMne
  have hMr : M ^ r = ENNReal.ofReal (M.toReal ^ r) := by
    conv_lhs => rw [← ENNReal.ofReal_toReal hMne']
    exact ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg hr0
  set A : ℝ := Cc ^ r * 2 ^ r * (Cd + M.toReal ^ r) with hAdef
  have hAp : 0 < A := by
    rw [hAdef]
    have h3 : (0 : ℝ) < Cd + M.toReal ^ r := by
      have hnn : (0 : ℝ) ≤ M.toReal ^ r := Real.rpow_nonneg ENNReal.toReal_nonneg r
      linarith
    positivity
  refine ⟨A ^ (1 / r), Real.rpow_pos_of_pos hAp _, ?_⟩
  have hCpow : (A ^ (1 / r)) ^ r = A := by
    rw [← Real.rpow_mul hAp.le (1 / r) r, show (1 / r) * r = 1 by field_simp, Real.rpow_one]
  intro H hHc hH1 hband s
  set a : ℤ → ENNReal := fun j => ‖H (j : ℝ)‖ₑ with ha
  set D : ℤ → ENNReal := fun n => latDiscMaxC a n with hD
  set K : ℝ → ENNReal := fun t => ∑' j : ℤ, a j * latKernel (t - (j : ℝ)) with hK
  have hpt : ∀ t : ℝ, Work.Maximal.mstHlMax (fun y : ℝ => ENNReal.ofReal ‖H y‖) t
      ≤ ENNReal.ofReal Cc * (D ⌊t⌋ + K t) := by
    intro t
    simpa only [ha, hD, hK] using hKernel H hHc hH1 hband t
  have hstep : ∀ x : ℤ,
      (Work.Maximal.mstHlMax (fun y : ℝ => ENNReal.ofReal ‖H y‖) ((x : ℝ) - s)) ^ r
        ≤ ENNReal.ofReal (Cc ^ r) * (2 : ENNReal) ^ r
            * ((D ⌊(x : ℝ) - s⌋) ^ r + (K ((x : ℝ) - s)) ^ r) := by
    intro x
    calc (Work.Maximal.mstHlMax (fun y : ℝ => ENNReal.ofReal ‖H y‖) ((x : ℝ) - s)) ^ r
        ≤ (ENNReal.ofReal Cc * (D ⌊(x : ℝ) - s⌋ + K ((x : ℝ) - s))) ^ r :=
          ENNReal.rpow_le_rpow (hpt _) hr0
      _ = (ENNReal.ofReal Cc) ^ r * (D ⌊(x : ℝ) - s⌋ + K ((x : ℝ) - s)) ^ r :=
          ENNReal.mul_rpow_of_nonneg _ _ hr0
      _ = ENNReal.ofReal (Cc ^ r) * (D ⌊(x : ℝ) - s⌋ + K ((x : ℝ) - s)) ^ r := by
          rw [ENNReal.ofReal_rpow_of_nonneg (le_of_lt hCcpos) hr0]
      _ ≤ ENNReal.ofReal (Cc ^ r)
            * ((2 : ENNReal) ^ r * ((D ⌊(x : ℝ) - s⌋) ^ r + (K ((x : ℝ) - s)) ^ r)) :=
          mul_le_mul_right (add_rpow_le_two_rpow_mul _ _ hr0) _
      _ = ENNReal.ofReal (Cc ^ r) * (2 : ENNReal) ^ r
            * ((D ⌊(x : ℝ) - s⌋) ^ r + (K ((x : ℝ) - s)) ^ r) := by rw [mul_assoc]
  have hsum : (∑' x : ℤ,
        (Work.Maximal.mstHlMax (fun y : ℝ => ENNReal.ofReal ‖H y‖) ((x : ℝ) - s)) ^ r)
      ≤ ENNReal.ofReal (Cc ^ r) * (2 : ENNReal) ^ r
          * ((∑' x : ℤ, (D ⌊(x : ℝ) - s⌋) ^ r) + (∑' x : ℤ, (K ((x : ℝ) - s)) ^ r)) := by
    calc (∑' x : ℤ,
          (Work.Maximal.mstHlMax (fun y : ℝ => ENNReal.ofReal ‖H y‖) ((x : ℝ) - s)) ^ r)
        ≤ ∑' x : ℤ, ENNReal.ofReal (Cc ^ r) * (2 : ENNReal) ^ r
            * ((D ⌊(x : ℝ) - s⌋) ^ r + (K ((x : ℝ) - s)) ^ r) := ENNReal.tsum_le_tsum hstep
      _ = ENNReal.ofReal (Cc ^ r) * (2 : ENNReal) ^ r
            * ∑' x : ℤ, ((D ⌊(x : ℝ) - s⌋) ^ r + (K ((x : ℝ) - s)) ^ r) := by
          rw [ENNReal.tsum_mul_left]
      _ = ENNReal.ofReal (Cc ^ r) * (2 : ENNReal) ^ r
            * ((∑' x : ℤ, (D ⌊(x : ℝ) - s⌋) ^ r) + (∑' x : ℤ, (K ((x : ℝ) - s)) ^ r)) := by
          rw [ENNReal.tsum_add]
  let eσ : ℤ ≃ ℤ := Equiv.ofBijective (fun x : ℤ => ⌊(x : ℝ) - s⌋) (floor_sub_bijective s)
  have hDsum : (∑' x : ℤ, (D ⌊(x : ℝ) - s⌋) ^ r) = ∑' n : ℤ, (D n) ^ r :=
    eσ.tsum_eq (fun n : ℤ => (D n) ^ r)
  have hDbound : (∑' n : ℤ, (D n) ^ r) ≤ ENNReal.ofReal Cd * ∑' n : ℤ, (a n) ^ r := by
    have h := hDisc a
    simp only [MeasureTheory.lintegral_count] at h
    simpa [hD] using h
  have hKbound : (∑' x : ℤ, (K ((x : ℝ) - s)) ^ r) ≤ M ^ r * ∑' n : ℤ, (a n) ^ r := by
    set n0 : ℤ := ⌊s⌋ with hn0
    set φ : ℝ := s - (n0 : ℝ) with hφdef
    have hφ0 : 0 ≤ φ := by
      rw [hφdef]
      have := Int.floor_le s
      linarith
    have hφ1 : φ < 1 := by
      rw [hφdef]
      have := Int.lt_floor_add_one s
      linarith
    have hptK : ∀ x : ℤ, K ((x : ℝ) - s) ≤ ∑' j : ℤ, latKernelMajorant j * a ((x - n0) - j) := by
      intro x
      have h1 : K ((x : ℝ) - s) ≤ ∑' j : ℤ, a j * latKernelMajorant ((x - n0) - j) := by
        simp only [hK]
        refine ENNReal.tsum_le_tsum (fun j => ?_)
        have hcast : (x : ℝ) - s - (j : ℝ) = (((x - n0) - j : ℤ) : ℝ) - φ := by
          rw [hφdef]; push_cast; ring
        rw [hcast]
        exact mul_le_mul_right (latKernelMajorant_sub_le ((x - n0) - j) hφ0 hφ1) (a j)
      rwa [tsum_mul_comm_sub a latKernelMajorant (x - n0)] at h1
    calc (∑' x : ℤ, (K ((x : ℝ) - s)) ^ r)
        ≤ ∑' x : ℤ, ((∑' j : ℤ, latKernelMajorant j * a ((x - n0) - j))) ^ r :=
          ENNReal.tsum_le_tsum (fun x => ENNReal.rpow_le_rpow (hptK x) hr0)
      _ = ∑' m : ℤ, ((∑' j : ℤ, latKernelMajorant j * a (m - j))) ^ r :=
          (Equiv.subRight n0).tsum_eq
            (fun m : ℤ => ((∑' j : ℤ, latKernelMajorant j * a (m - j))) ^ r)
      _ ≤ M ^ r * ∑' m : ℤ, (a m) ^ r := by
          rw [hMdef]
          exact Work.IonescuWainger.young_count_lp hr1 latKernelMajorant a
  have hmid : (∑' x : ℤ, (D ⌊(x : ℝ) - s⌋) ^ r) + (∑' x : ℤ, (K ((x : ℝ) - s)) ^ r)
      ≤ ENNReal.ofReal Cd * (∑' n : ℤ, (a n) ^ r) + M ^ r * (∑' n : ℤ, (a n) ^ r) := by
    rw [hDsum]
    exact add_le_add hDbound hKbound
  have h2r : (2 : ENNReal) ^ r = ENNReal.ofReal ((2 : ℝ) ^ r) := by
    rw [← ENNReal.ofReal_ofNat 2]
    exact ENNReal.ofReal_rpow_of_nonneg (by norm_num) hr0
  have hconst : ENNReal.ofReal (Cc ^ r) * (2 : ENNReal) ^ r * (ENNReal.ofReal Cd + M ^ r)
      = ENNReal.ofReal A := by
    have h1 : ENNReal.ofReal (Cc ^ r) * (2 : ENNReal) ^ r = ENNReal.ofReal (Cc ^ r * 2 ^ r) := by
      rw [h2r, ← ENNReal.ofReal_mul (Real.rpow_nonneg hCcpos.le r)]
    have h2 : ENNReal.ofReal Cd + M ^ r = ENNReal.ofReal (Cd + M.toReal ^ r) := by
      rw [hMr, ENNReal.ofReal_add (le_of_lt hCdpos) (Real.rpow_nonneg ENNReal.toReal_nonneg r)]
    rw [h1, h2, ← ENNReal.ofReal_mul
      (mul_nonneg (Real.rpow_nonneg hCcpos.le r) (Real.rpow_nonneg (by norm_num) r))]
  calc (∑' x : ℤ,
        (Work.Maximal.mstHlMax (fun y : ℝ => ENNReal.ofReal ‖H y‖) ((x : ℝ) - s)) ^ r)
      ≤ ENNReal.ofReal (Cc ^ r) * (2 : ENNReal) ^ r
          * ((∑' x : ℤ, (D ⌊(x : ℝ) - s⌋) ^ r) + (∑' x : ℤ, (K ((x : ℝ) - s)) ^ r)) := hsum
    _ ≤ ENNReal.ofReal (Cc ^ r) * (2 : ENNReal) ^ r
          * (ENNReal.ofReal Cd * (∑' n : ℤ, (a n) ^ r) + M ^ r * (∑' n : ℤ, (a n) ^ r)) :=
        mul_le_mul_right hmid _
    _ = ENNReal.ofReal (Cc ^ r) * (2 : ENNReal) ^ r
          * ((ENNReal.ofReal Cd + M ^ r) * (∑' n : ℤ, (a n) ^ r)) := by rw [add_mul]
    _ = ENNReal.ofReal A * (∑' n : ℤ, (a n) ^ r) := by
        rw [← mul_assoc (ENNReal.ofReal (Cc ^ r) * (2 : ENNReal) ^ r)
          (ENNReal.ofReal Cd + M ^ r) (∑' n : ℤ, (a n) ^ r), hconst]
    _ = ENNReal.ofReal ((A ^ (1 / r)) ^ r) * (∑' n : ℤ, (a n) ^ r) := by rw [hCpow]
    _ = ENNReal.ofReal ((A ^ (1 / r)) ^ r) * ∑' x : ℤ, ENNReal.ofReal (‖H (x : ℝ)‖ ^ r) := by
        have hS : (∑' n : ℤ, (a n) ^ r) = ∑' n : ℤ, ENNReal.ofReal (‖H (n : ℝ)‖ ^ r) :=
          tsum_congr (fun n => by
            rw [show a n = ENNReal.ofReal ‖H (n : ℝ)‖ by simp [ha, enorm_eq_nnnorm]]
            exact ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) hr0)
        rw [hS]

end

end Work.BourgainPlan.Maximal
