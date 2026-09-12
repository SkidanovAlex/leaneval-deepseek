import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Tactic.NormNum.RealSqrt

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace Commons.Measure.Resonance

/-! # The resonance arc measure estimate

For `0 < ρ ≤ |y|` and `0 ≤ α`, the Lebesgue measure of the set of `t ∈ [−1/ρ, 1/ρ]` where
`1 − cos (t·y) ≤ α` is at most `C · √α / ρ` for a universal constant `C`.

## Proof sketch

*Small `α` (`α < 1/2`).*  From `1 − cos u ≤ α` one gets `|u − 2πk| ≤ 2√α` for some integer `k`
(lemma `dist_lattice_le_of_one_sub_cos_le` below), so the set is covered by the "arcs"
`|t·|y| − 2πk| ≤ 2√α`.  At most `O(|y|/ρ)` of these arcs meet the window `[−1/ρ, 1/ρ]`, and
each has length `4√α/|y|`, giving the total measure bound `O(√α/ρ)`.

*Large `α` (`1/2 ≤ α`).*  The whole window has measure `2/ρ ≤ C√α/ρ`.
-/

/-! ## Part I: elementary trigonometry -/

/-- `1 − cos(2θ) = 2 sin² θ`. -/
lemma one_sub_cos_two_mul_sq (θ : ℝ) : 1 - Real.cos (2 * θ) = 2 * Real.sin θ ^ 2 := by
  rw [Real.cos_two_mul]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- For `|u| ≤ 1`, `2 sin² u ≥ u²`. -/
lemma sin_sq_ge_half_sq {u : ℝ} (hu : |u| ≤ 1) : (2 : ℝ) * Real.sin u ^ 2 ≥ u ^ 2 := by
  have hnonneg : (5 / 6 : ℝ) * |u| ≤ |Real.sin u| := by
    have h56 : ∀ {v : ℝ}, 0 ≤ v → v ≤ 1 → (5 / 6 : ℝ) * v ≤ Real.sin v := by
      intro v hv0 hv1
      have hsub := Real.sin_ge_sub_cube hv0
      have hge : (5 / 6 : ℝ) * v ≤ v - v ^ 3 / 6 := by nlinarith [sq_nonneg v, hv1]
      exact le_trans hge hsub
    by_cases hu0 : 0 ≤ u
    · have h1 : (5 / 6 : ℝ) * u ≤ Real.sin u := h56 hu0 (by nlinarith [abs_le.mp hu])
      have hpos : 0 ≤ Real.sin u := by nlinarith [h1, hu0]
      calc
        (5 / 6 : ℝ) * |u| = (5 / 6 : ℝ) * u := by rw [abs_of_nonneg hu0]
        _ ≤ Real.sin u := h1
        _ = |Real.sin u| := (abs_of_nonneg hpos).symm
    · have hu0' : u ≤ 0 := le_of_not_ge hu0
      let w := -u
      have hw0 : 0 ≤ w := by dsimp [w]; linarith
      have hw1 : w ≤ 1 := by dsimp [w]; nlinarith [abs_le.mp hu]
      have h1 : (5 / 6 : ℝ) * w ≤ Real.sin w := h56 hw0 hw1
      have hpos : 0 ≤ Real.sin w := by nlinarith [h1, hw0]
      calc
        (5 / 6 : ℝ) * |u| = (5 / 6 : ℝ) * w := by dsimp [w]; rw [abs_of_neg]; linarith
        _ ≤ Real.sin w := h1
        _ = |Real.sin u| := by
          have hs : Real.sin u = -Real.sin w := by
            dsimp [w]
            rw [Real.sin_neg]
            ring
          rw [hs, abs_neg]
          exact (abs_of_nonneg hpos).symm
  have hsq0 : ((5 / 6 : ℝ) * u) ^ 2 ≤ Real.sin u ^ 2 := by
    exact sq_le_sq.mpr (by simpa [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 5 / 6)] using hnonneg)
  have hsq : (25 / 36 : ℝ) * u ^ 2 ≤ Real.sin u ^ 2 := by nlinarith [hsq0]
  nlinarith

/-- `x²/4 ≤ 1 − cos x` for `|x| ≤ 2`. -/
lemma one_sub_cos_ge_sq_div_four {x : ℝ} (hx : |x| ≤ 2) : x ^ 2 / 4 ≤ 1 - Real.cos x := by
  have hx2 : |x / 2| ≤ 1 := by
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    simpa using hx
  have h := sin_sq_ge_half_sq (u := x / 2) hx2
  have hc : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
    have hc' := one_sub_cos_two_mul_sq (θ := x / 2)
    rw [show 2 * (x / 2) = x by ring] at hc'
    exact hc'
  rw [hc]
  nlinarith

/-- `1/2 ≤ sin 1`. -/
lemma sin_one_ge_half : (1 / 2 : ℝ) ≤ Real.sin 1 := by
  have h₁ : (Real.pi / 6 : ℝ) < (1 : ℝ) := by
    rw [div_lt_one (by norm_num : (0 : ℝ) < 6)]
    linarith [Real.pi_lt_four]
  have hy : (1 : ℝ) ≤ Real.pi / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    linarith [Real.pi_gt_three]
  have hlt : Real.sin (Real.pi / 6) < Real.sin 1 := by
    exact Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith [Real.pi_pos]) hy h₁
  have hsin : Real.sin (Real.pi / 6) = 1 / 2 := by norm_num [Real.sin_pi_div_six]
  linarith

/-- sine is monotone on `[0, π/2]`. -/
lemma sin_mono_Icc {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ Real.pi / 2) (hab : a ≤ b) :
    Real.sin a ≤ Real.sin b := by
  rcases lt_or_eq_of_le hab with hab' | hab'
  · exact le_of_lt (Real.sin_lt_sin_of_lt_of_le_pi_div_two (by linarith) hb hab')
  · rw [hab']

/-- For `2 ≤ |w| ≤ π`, `1/2 ≤ 1 − cos w`. -/
lemma one_sub_cos_ge_half_of_two_le_abs {w : ℝ} (hw₂ : (2 : ℝ) ≤ |w|) (hwπ : |w| ≤ Real.pi) :
    (1 / 2 : ℝ) ≤ 1 - Real.cos w := by
  have hwπ2 : |w| / 2 ≤ Real.pi / 2 := div_le_div_of_nonneg_right hwπ (by norm_num)
  have h₁ : (1 : ℝ) ≤ |w| / 2 := by nlinarith
  have hsin : (1 / 2 : ℝ) ≤ Real.sin (|w| / 2) := by
    have hs := sin_mono_Icc (a := 1) (b := |w| / 2) (by norm_num) hwπ2 h₁
    exact le_trans sin_one_ge_half hs
  have hcos : Real.cos w = Real.cos |w| := by
    by_cases hw : 0 ≤ w
    · rw [abs_of_nonneg hw]
    · rw [abs_of_neg (lt_of_not_ge hw), Real.cos_neg]
  rw [hcos]
  have hc : 1 - Real.cos |w| = 2 * Real.sin (|w| / 2) ^ 2 := by
    have hc' := one_sub_cos_two_mul_sq (θ := |w| / 2)
    rw [show 2 * (|w| / 2) = |w| by ring] at hc'
    exact hc'
  rw [hc]
  nlinarith [sq_nonneg (Real.sin (|w| / 2) - 1 / 2)]

/-- Every real number is within `π` of an integer multiple of `2π`. -/
lemma exists_int_mul_two_pi_dist_le (w : ℝ) :
    ∃ k : ℤ, |w - (2 * Real.pi) * (k : ℝ)| ≤ Real.pi := by
  let k : ℤ := Int.floor (w / (2 * Real.pi) + 1 / 2)
  have h₀ : (k : ℝ) ≤ w / (2 * Real.pi) + 1 / 2 := Int.floor_le _
  have h₁ : w / (2 * Real.pi) + 1 / 2 < (k : ℝ) + 1 := Int.lt_floor_add_one _
  have h2p : (0 : ℝ) < 2 * Real.pi := by positivity
  refine ⟨k, ?_⟩
  rw [abs_le]
  constructor
  · have hmul : (2 * Real.pi) * (k : ℝ) ≤ w + Real.pi := by
      calc
        (2 * Real.pi) * (k : ℝ) ≤ (2 * Real.pi) * (w / (2 * Real.pi) + 1 / 2) :=
          mul_le_mul_of_nonneg_left h₀ (le_of_lt h2p)
        _ = w + Real.pi := by
          have hcancel : (2 * Real.pi) * (w / (2 * Real.pi)) = w := by
            rw [mul_div_cancel₀ w h2p.ne']
          rw [mul_add, hcancel]
          ring
    linarith
  · have hmul2 : w + Real.pi ≤ (2 * Real.pi) * ((k : ℝ) + 1) := by
      have h := mul_lt_mul_of_pos_left h₁ h2p
      have hcancel : (2 * Real.pi) * (w / (2 * Real.pi) + 1 / 2) = w + Real.pi := by
        have hc : (2 * Real.pi) * (w / (2 * Real.pi)) = w := by
          rw [mul_div_cancel₀ w h2p.ne']
        rw [mul_add, hc]
        ring
      rw [hcancel] at h
      have h' : w + Real.pi ≤ (2 * Real.pi) * ((k : ℝ) + 1) := le_of_lt h
      simpa [mul_add, add_mul, mul_comm, mul_left_comm, mul_assoc] using h'
    calc
      w - (2 * Real.pi) * (k : ℝ) ≤ Real.pi := by nlinarith

/-- `cos` is `2π`-periodic with integer period. -/
lemma cos_sub_int_mul_two_pi (w : ℝ) (k : ℤ) :
    Real.cos (w - (2 * Real.pi) * (k : ℝ)) = Real.cos w := by
  rw [Real.cos_sub, mul_comm (2 * Real.pi) (k : ℝ), Real.cos_int_mul_two_pi]
  have hsin : Real.sin ((k : ℝ) * (2 * Real.pi)) = 0 := by
    simpa using (Real.sin_add_int_mul_two_pi (x := 0) (n := k))
  rw [hsin]
  ring

/-- Sublevel containment: if `1 − cos w ≤ α < 1/2` then `w` is within `2√α` of a multiple
of `2π`. -/
lemma dist_lattice_le_of_one_sub_cos_le {w α : ℝ} (hα₀ : 0 ≤ α) (hα₁ : α < 1 / 2)
    (hw : 1 - Real.cos w ≤ α) : ∃ k : ℤ, |w - (2 * Real.pi) * (k : ℝ)| ≤ 2 * Real.sqrt α := by
  rcases exists_int_mul_two_pi_dist_le w with ⟨k, hk⟩
  let u : ℝ := w - (2 * Real.pi) * (k : ℝ)
  have hcos : Real.cos u = Real.cos w := by
    simpa [u] using cos_sub_int_mul_two_pi w k
  by_cases hsmall : |u| ≤ 2
  · have hq := one_sub_cos_ge_sq_div_four (x := u) hsmall
    have hα : u ^ 2 / 4 ≤ α := by
      calc
        u ^ 2 / 4 ≤ 1 - Real.cos u := hq
        _ = 1 - Real.cos w := by rw [hcos]
        _ ≤ α := hw
    have hsq : u ^ 2 ≤ (2 * Real.sqrt α) ^ 2 := by
      have h4 : (2 * Real.sqrt α) ^ 2 = 4 * α := by
        rw [mul_pow, Real.sq_sqrt hα₀]
        norm_num
      rw [h4]
      nlinarith
    have hu0 : (0 : ℝ) ≤ 2 * Real.sqrt α := by positivity
    have hu : |u| ≤ 2 * Real.sqrt α := abs_le_of_sq_le_sq hsq hu0
    exact ⟨k, by simpa [u] using hu⟩
  · have hbig : (2 : ℝ) ≤ |u| := le_of_lt (lt_of_not_ge hsmall)
    have hlb := one_sub_cos_ge_half_of_two_le_abs (w := u) hbig (by simpa [u] using hk)
    have hc : 1 - Real.cos w ≥ 1 / 2 := by
      have : 1 / 2 ≤ 1 - Real.cos u := hlb
      rwa [hcos] at this
    linarith

/-- `cos (t·y) = cos (t·|y|)` — cosine is even. -/
lemma cos_mul_eq_cos_mul_abs (t y : ℝ) : Real.cos (t * y) = Real.cos (t * |y|) := by
  by_cases hy : 0 ≤ y
  · rw [abs_of_nonneg hy]
  · have hy' : y ≤ 0 := le_of_not_ge hy
    rw [abs_of_nonpos hy']
    rw [show t * (-y) = -(t * y) by ring, Real.cos_neg]

/-! ## Part II: volume of intervals and arcs -/

/-- Real Lebesgue measure of `Icc (c − r) (c + r)` is `2r` (for `0 ≤ r`). -/
lemma volume_Icc_center_real (c r : ℝ) (hr : 0 ≤ r) :
    volume.real (Set.Icc (c - r) (c + r)) = 2 * r := by
  rw [Real.volume_real_Icc_of_le]
  · ring_nf
  · nlinarith

/-- Real measure of the `β`-neighbourhood `{t | |t·Y − c| ≤ β}` is `2β/Y` (`0 < Y`, `0 ≤ β`). -/
lemma volume_abs_mul_le_real (Y c β : ℝ) (hY : 0 < Y) (hβ : 0 ≤ β) :
    volume.real {t : ℝ | |t * Y - c| ≤ β} = 2 * β / Y := by
  have hset : {t : ℝ | |t * Y - c| ≤ β} = Set.Icc ((c - β) / Y) ((c + β) / Y) := by
    ext t
    change |t * Y - c| ≤ β ↔ (c - β) / Y ≤ t ∧ t ≤ (c + β) / Y
    rw [abs_le]
    constructor
    · intro ht
      constructor
      · exact (div_le_iff₀ hY).mpr (by linarith)
      · exact (le_div_iff₀ hY).mpr (by linarith)
    · intro ht
      have h1 : c - β ≤ t * Y := (div_le_iff₀ hY).1 ht.1
      have h2 : t * Y ≤ c + β := (le_div_iff₀ hY).1 ht.2
      constructor <;> linarith
  rw [hset]
  have hle : (c - β) / Y ≤ (c + β) / Y := by
    exact div_le_div_of_nonneg_right (by linarith) (le_of_lt hY)
  rw [Real.volume_real_Icc_of_le hle]
  field_simp [hY.ne']
  ring

lemma volume_abs_mul_le_toReal (Y c β : ℝ) (hY : 0 < Y) (hβ : 0 ≤ β) :
    (volume {t : ℝ | |t * Y - c| ≤ β}).toReal = 2 * β / Y := by
  rw [← measureReal_def]
  exact volume_abs_mul_le_real Y c β hY hβ

/-! ## Part III: counting arcs -/

/-- card of `Icc (-N) N` (`0 ≤ N`), as integers. -/
lemma card_Icc_neg_self (N : ℤ) (hN : 0 ≤ N) : ((Finset.Icc (-N) N).card : ℤ) = 2 * N + 1 := by
  rw [Int.card_Icc_of_le]
  · ring
  · omega

/-- For `|(k:ℝ)| ≤ x` and `x < N`, `k ∈ Icc (−N) N`. -/
lemma mem_Icc_of_abs_le_of_lt {N k : ℤ} {x : ℝ} (hk : |(k : ℝ)| ≤ x) (hx : x < (N : ℝ)) :
    k ∈ Finset.Icc (-N) N := by
  have hk' : |(k : ℝ)| ≤ (N : ℝ) := le_trans hk (le_of_lt hx)
  have hkz : |k| ≤ N := by exact_mod_cast hk'
  rw [Finset.mem_Icc]
  exact abs_le.mp hkz

/-- Number of relevant arcs: for `1 ≤ L` and `0 ≤ β ≤ 2`, the arcs indexed by
`k ∈ Icc (−N) N` with `N := ⌊(L+β)/2π⌋ + 1` number at most `4L` (as real numbers). -/
lemma card_arcs_le_four_mul_L (L β : ℝ) (hL1 : 1 ≤ L) (hβ0 : 0 ≤ β) (hβ : β ≤ 2) :
    let x : ℝ := (L + β) / (2 * Real.pi)
    let N : ℤ := Int.floor x + 1
    ((Finset.Icc (-N) N).card : ℝ) ≤ 4 * L := by
  dsimp
  let x : ℝ := (L + β) / (2 * Real.pi)
  let N : ℤ := Int.floor x + 1
  have hxN : (N : ℝ) ≤ x + 1 := by
    dsimp [N]
    push_cast
    have h := Int.floor_le x
    linarith
  have hN0 : 0 ≤ N := by
    dsimp [N]
    have hx0 : 0 ≤ x := by
      dsimp [x]
      exact div_nonneg (by linarith) (by positivity)
    have hf0 : 0 ≤ Int.floor x := Int.floor_nonneg.mpr hx0
    omega
  have hcard := card_Icc_neg_self N hN0
  have h2x : 2 * x + 3 = (L + β) / Real.pi + 3 := by
    dsimp [x]
    field_simp [show (2 * Real.pi : ℝ) ≠ 0 by
      exact mul_ne_zero (by norm_num) Real.pi_ne_zero]
  calc
    ((Finset.Icc (-N) N).card : ℝ) = (2 * N + 1 : ℝ) := by exact_mod_cast hcard
    _ ≤ 2 * x + 3 := by nlinarith [hxN]
    _ = (L + β) / Real.pi + 3 := h2x
    _ ≤ 4 * L := by
      have hπpos : 0 < Real.pi := Real.pi_pos
      have hprod : L + β ≤ (4 * L - 3) * Real.pi := by
        nlinarith [hL1, hβ, Real.pi_gt_three]
      have hdiv : (L + β) / Real.pi ≤ 4 * L - 3 := (div_le_iff₀ hπpos).mpr hprod
      linarith

/-! ## Part IV: the main estimate -/

/-- real-valued measure estimate for the resonance set (universal constant `64`) -/
lemma arc_measure_real {ρ Y α : ℝ} (hρ : 0 < ρ) (hρY : ρ ≤ Y) (hα₀ : 0 ≤ α) :
    volume.real {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - Real.cos (t * Y) ≤ α} ≤ 64 * Real.sqrt α / ρ := by
  have hY : 0 < Y := lt_of_lt_of_le hρ hρY
  let S : Set ℝ := {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - Real.cos (t * Y) ≤ α}
  have hmain : volume.real S ≤ 64 * Real.sqrt α / ρ := by
    by_cases hαlt : α < 1 / 2
    · -- small α: cover by arcs of half-width β := 2√α around the zeros 2πk/Y
      let β : ℝ := 2 * Real.sqrt α
      have hβ0 : 0 ≤ β := by dsimp [β]; positivity
      have hβ2 : β ≤ 2 := by
        dsimp [β]
        have hα12 : α ≤ 1 / 2 := le_of_lt hαlt
        have hsqrt : Real.sqrt α ≤ Real.sqrt (1 / 2) := Real.sqrt_le_sqrt hα12
        have hs12 : Real.sqrt (1 / 2) ≤ 1 := by
          rw [← Real.sqrt_one]
          exact Real.sqrt_le_sqrt (by norm_num)
        nlinarith
      let L : ℝ := Y / ρ
      have hL1 : 1 ≤ L := by
        dsimp [L]
        exact (one_le_div hρ).2 hρY
      let x : ℝ := (L + β) / (2 * Real.pi)
      have hxpos : 0 ≤ x := by
        dsimp [x]
        exact div_nonneg (by nlinarith) (by positivity)
      let N : ℤ := Int.floor x + 1
      have hxNlt : x < (N : ℝ) := by
        dsimp [N]
        push_cast
        exact Int.lt_floor_add_one x
      have hN0 : 0 ≤ N := by
        dsimp [N]
        have hf : 0 ≤ Int.floor x := Int.floor_nonneg.mpr hxpos
        omega
      let F : Finset ℤ := Finset.Icc (-N) N
      have hFcard : (F.card : ℝ) ≤ 4 * L := by
        simpa [F, N, x] using (card_arcs_le_four_mul_L L β hL1 hβ0 hβ2)
      let arc : ℤ → Set ℝ := fun k => {t : ℝ | |t * Y - (2 * Real.pi) * (k : ℝ)| ≤ β}
      -- volume of one arc (ENNReal value)
      have hvolarc : ∀ k : ℤ, volume (arc k) = ENNReal.ofReal (2 * β / Y) := by
        intro k
        let c : ℝ := (2 * Real.pi) * (k : ℝ)
        have hset : arc k = Set.Icc ((c - β) / Y) ((c + β) / Y) := by
          ext t
          dsimp [arc]
          change |t * Y - c| ≤ β ↔ (c - β) / Y ≤ t ∧ t ≤ (c + β) / Y
          rw [abs_le]
          constructor
          · intro ht
            constructor
            · exact (div_le_iff₀ hY).mpr (by linarith)
            · exact (le_div_iff₀ hY).mpr (by linarith)
          · intro ht
            have h1 : c - β ≤ t * Y := (div_le_iff₀ hY).1 ht.1
            have h2 : t * Y ≤ c + β := (le_div_iff₀ hY).1 ht.2
            constructor <;> linarith
        rw [hset, Real.volume_Icc]
        congr 1
        field_simp [hY.ne']
        ring
      -- S is covered by the arcs indexed by F
      have hsubS : S ⊆ ⋃ k ∈ F, arc k := by
        intro t ht
        have htS : |t| ≤ 1 / ρ ∧ 1 - Real.cos (t * Y) ≤ α := by simpa [S] using ht
        rcases htS with ⟨htw, htcos⟩
        rcases dist_lattice_le_of_one_sub_cos_le (w := t * Y) hα₀ hαlt htcos with ⟨k0, hk0⟩
        have hk0b : |t * Y - (2 * Real.pi) * (k0 : ℝ)| ≤ β := by simpa [β] using hk0
        have htwL : |t * Y| ≤ L := by
          dsimp [L]
          calc
            |t * Y| = |t| * Y := by rw [abs_mul, abs_of_nonneg (le_of_lt hY)]
            _ ≤ (1 / ρ) * Y := mul_le_mul_of_nonneg_right htw (le_of_lt hY)
            _ = Y / ρ := by ring
        have hk0x : |(k0 : ℝ)| ≤ x := by
          dsimp [x]
          have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
          have htri : |(2 * Real.pi) * (k0 : ℝ)| ≤ |t * Y| + |t * Y - (2 * Real.pi) * (k0 : ℝ)| := by
            have h := abs_add_le (t * Y) ((2 * Real.pi) * (k0 : ℝ) - t * Y)
            calc
              |(2 * Real.pi) * (k0 : ℝ)| = |t * Y + ((2 * Real.pi) * (k0 : ℝ) - t * Y)| := by congr 1; ring
              _ ≤ |t * Y| + |(2 * Real.pi) * (k0 : ℝ) - t * Y| := h
              _ = |t * Y| + |t * Y - (2 * Real.pi) * (k0 : ℝ)| := by rw [abs_sub_comm]
          have hk0L : |(2 * Real.pi) * (k0 : ℝ)| ≤ L + β := by nlinarith [htwL, hk0b, htri]
          exact (le_div_iff₀ h2π).mpr (by
            have hm : (2 * Real.pi) * |(k0 : ℝ)| ≤ L + β := by
              rwa [abs_mul, abs_of_pos h2π] at hk0L
            simpa [mul_comm] using hm)
        have hk0F : k0 ∈ F := by
          exact mem_Icc_of_abs_le_of_lt (N := N) (hk := hk0x) (hx := hxNlt)
        have htarc : t ∈ arc k0 := by simpa [arc] using hk0b
        exact Set.mem_biUnion hk0F htarc
      -- finiteness of the covering union
      have hfin_union : volume (⋃ k ∈ F, arc k) ≠ ⊤ := by
        refine MeasureTheory.measure_biUnion_ne_top (s := (F : Set ℤ)) (f := arc) (hs := F.finite_toSet) ?_
        intro k hk
        rw [hvolarc k]
        exact ENNReal.ofReal_lt_top.ne
      -- real measure chain
      have hsum : (∑ k ∈ F, volume.real (arc k)) = (F.card : ℝ) * (2 * β / Y) := by
        calc
          (∑ k ∈ F, volume.real (arc k)) = ∑ k ∈ F, (2 * β / Y) := by
            refine Finset.sum_congr rfl ?_
            intro k hk
            exact volume_abs_mul_le_real Y ((2 * Real.pi) * (k : ℝ)) β hY hβ0
          _ = (F.card : ℝ) * (2 * β / Y) := by simp
      have hmeasure : volume.real S ≤ (F.card : ℝ) * (2 * β / Y) := by
        calc
          volume.real S ≤ volume.real (⋃ k ∈ F, arc k) := measureReal_mono hsubS hfin_union
          _ ≤ ∑ k ∈ F, volume.real (arc k) := MeasureTheory.measureReal_biUnion_finset_le F arc
          _ = (F.card : ℝ) * (2 * β / Y) := hsum
      have hpos : 0 ≤ 2 * β / Y := by positivity
      have hcardb : (F.card : ℝ) * (2 * β / Y) ≤ (4 * L) * (2 * β / Y) :=
        mul_le_mul_of_nonneg_right hFcard hpos
      have hb2 : (4 * L) * (2 * β / Y) = 16 * Real.sqrt α / ρ := by
        dsimp [L, β]
        field_simp [hρ.ne', hY.ne']
        ring
      have hb3 : 16 * Real.sqrt α / ρ ≤ 64 * Real.sqrt α / ρ := by
        refine div_le_div_of_nonneg_right ?_ (le_of_lt hρ)
        nlinarith [Real.sqrt_nonneg α]
      calc
        volume.real S ≤ (F.card : ℝ) * (2 * β / Y) := hmeasure
        _ ≤ (4 * L) * (2 * β / Y) := hcardb
        _ = 16 * Real.sqrt α / ρ := hb2
        _ ≤ 64 * Real.sqrt α / ρ := hb3
    · -- big alpha: the whole window suffices
      have hα12 : (1 / 2 : ℝ) ≤ α := le_of_not_gt hαlt
      have hwinvol : volume.real (Set.Icc (-(1 / ρ)) (1 / ρ)) = 2 / ρ := by
        have hset : Set.Icc (-(1 / ρ)) (1 / ρ) = Set.Icc (0 - (1 / ρ)) (0 + (1 / ρ)) := by
          congr 1 <;> ring
        rw [hset]
        rw [volume_Icc_center_real (0 : ℝ) (1 / ρ) (le_of_lt (one_div_pos.mpr hρ))]
        ring
      calc
        volume.real S ≤ volume.real (Set.Icc (-(1 / ρ)) (1 / ρ)) := by
          refine measureReal_mono ?_ ?_
          · intro t ht
            rw [Set.mem_Icc]
            have htS : |t| ≤ 1 / ρ ∧ 1 - Real.cos (t * Y) ≤ α := by simpa [S] using ht
            have htw : |t| ≤ 1 / ρ := htS.1
            constructor <;> nlinarith [abs_le.mp htw]
          · rw [Real.volume_Icc]
            exact ENNReal.ofReal_lt_top.ne
        _ = 2 / ρ := hwinvol
        _ ≤ 64 * Real.sqrt α / ρ := by
          refine div_le_div_of_nonneg_right ?_ (le_of_lt hρ)
          have hs12 : Real.sqrt (1 / 2) ≤ Real.sqrt α := Real.sqrt_le_sqrt hα12
          have hhalf : (1 / 2 : ℝ) ≤ Real.sqrt (1 / 2) := by
            exact (Real.le_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 (by norm_num)
          nlinarith
  simpa [S] using hmain

/-- The resonance arc measure estimate. -/
lemma arc_measure :
    ∃ C : ℝ, 0 < C ∧
      ∀ (ρ y α : ℝ), 0 < ρ → ρ ≤ |y| → 0 ≤ α →
        (volume {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - Real.cos (t * y) ≤ α}).toReal ≤
          C * Real.sqrt α / ρ := by
  refine ⟨64, by norm_num, ?_⟩
  intro ρ y α hρ hyρ hα₀
  have hcos : ∀ t : ℝ, Real.cos (t * y) = Real.cos (t * |y|) := by
    intro t
    exact cos_mul_eq_cos_mul_abs t y
  have hcos' : ∀ t : ℝ, 1 - Real.cos (t * y) = 1 - Real.cos (t * |y|) := by
    intro t
    rw [hcos t]
  have hset : {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - Real.cos (t * y) ≤ α} =
              {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - Real.cos (t * |y|) ≤ α} := by
    ext t
    change (|t| ≤ 1 / ρ ∧ 1 - Real.cos (t * y) ≤ α) ↔
           (|t| ≤ 1 / ρ ∧ 1 - Real.cos (t * |y|) ≤ α)
    rw [hcos' t]
  rw [hset]
  change volume.real {t : ℝ | |t| ≤ 1 / ρ ∧ 1 - Real.cos (t * |y|) ≤ α} ≤ 64 * Real.sqrt α / ρ
  exact arc_measure_real (ρ := ρ) (Y := |y|) hρ hyρ hα₀

end Commons.Measure.Resonance