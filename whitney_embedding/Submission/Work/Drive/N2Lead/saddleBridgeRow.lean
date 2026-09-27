import Mathlib
import Submission.Work.Drive.N2Lead.mobiusGeomDefs
import Submission.Work.Drive.N2Lead.mobius_lowerProfile

namespace Work.Drive.N2Lead

open scoped ContDiff Topology
open Set Filter

noncomputable section

/-! ## Auxiliary lemmas for the bridge row `hoff`

The bridge row says that a parameter `t` of the packet's angle function `Θ` which is **not** in a
`ℤ`-orbit of one of the two arc parametrisations must have `Θ t` in the bridge zone
`dist (φ, πℤ) ≤ φE`, `φE = mobiusPhiE ηs m`.  The proof decomposes as:

* `bridgeRow_mobiusPhiE_eq_arctan`: the endpoint of the arc range is the upper arc angle at `w = m`,
  `φE = π/2 - (1/2) arctan (m/η)`;
* `theta_add_int`: the integer-shift law `Θ (t + k) = Θ t + 2 π k` of a `1`-periodic-up-to-`2π`
  function;
* `exists_arcAngleU` / `exists_arcAngleL`: the intermediate value theorem, giving the exact arc
  ranges `[φE, π - φE]` and `[-π + φE, -φE]` of the two angle maps. -/

/-- `cos (arctan (b/a)) = a / √(a² + b²)` for `a > 0`. -/
lemma bridgeRow_cos_arctan_div {a : ℝ} (ha : 0 < a) (b : ℝ) :
    Real.cos (Real.arctan (b / a)) = a / Real.sqrt (a ^ 2 + b ^ 2) := by
  have hS : Real.sqrt (a ^ 2 + b ^ 2) ≠ 0 := ne_of_gt (Real.sqrt_pos_of_pos (by positivity))
  have ha0 : a ≠ 0 := ne_of_gt ha
  rw [Real.cos_arctan]
  have h1 : (1 : ℝ) + (b / a) ^ 2 = (a ^ 2 + b ^ 2) / a ^ 2 := by field_simp
  have h2 : Real.sqrt (1 + (b / a) ^ 2) = Real.sqrt (a ^ 2 + b ^ 2) / a := by
    rw [h1, Real.sqrt_div (show (0 : ℝ) ≤ a ^ 2 + b ^ 2 by positivity), Real.sqrt_sq_eq_abs,
      abs_of_pos ha]
  rw [h2]; field_simp

/-- **The endpoint of the arc range.**  For `η, m > 0` the argument of the square root
`√(-η + i m)` is the upper arc angle at `w = m`:
`mobiusPhiE η m = π/2 - (1/2) arctan (m/η)`. -/
lemma bridgeRow_mobiusPhiE_eq_arctan {η m : ℝ} (hη : 0 < η) (hm : 0 < m) :
    mobiusPhiE η m = Real.pi / 2 - (1 / 2) * Real.arctan (m / η) := by
  obtain ⟨hcos, hpos, hlt⟩ := leadProfile_phiE hη hm
  have hcos2 : Real.cos (2 * (Real.pi / 2 - (1 / 2) * Real.arctan (m / η)))
      = Real.cos (2 * mobiusPhiE η m) := by
    rw [hcos]
    have h2 : 2 * (Real.pi / 2 - (1 / 2) * Real.arctan (m / η))
        = Real.pi - Real.arctan (m / η) := by ring
    rw [h2, Real.cos_pi_sub, bridgeRow_cos_arctan_div hη m, leadProfileC1, neg_div]
  have h1 : 2 * (Real.pi / 2 - (1 / 2) * Real.arctan (m / η)) ∈ Set.Icc 0 Real.pi := by
    have hx0 : 0 < Real.arctan (m / η) := Real.arctan_pos.mpr (div_pos hm hη)
    have hx1 : Real.arctan (m / η) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
    constructor <;> linarith [Real.pi_pos]
  have h2 : 2 * mobiusPhiE η m ∈ Set.Icc 0 Real.pi := by
    constructor <;> linarith [hpos, hlt, Real.pi_pos]
  have hinj := Real.strictAntiOn_cos.injOn h1 h2 hcos2
  linarith

/-- **The integer-shift law** of a function with `Θ (t + 1) = Θ t + 2 π`:
`Θ (t + k) = Θ t + 2 π k` for every `k : ℤ`. -/
lemma theta_add_int {Θ : ℝ → ℝ} (hΘper : ∀ t : ℝ, Θ (t + 1) = Θ t + 2 * Real.pi) :
    ∀ (k : ℤ) (t : ℝ), Θ (t + k) = Θ t + 2 * Real.pi * k := by
  set g : ℝ → ℝ := fun t => Θ t - t * (2 * Real.pi) with hg
  have hgper : Function.Periodic g 1 := by
    intro x
    simp only [hg]
    rw [hΘper x]
    ring
  intro k t
  have h := hgper.int_mul k t
  simp only [hg, mul_one] at h
  rw [add_mul] at h
  linear_combination h

/-- **The upper arc range.**  For `v` in `[φE, π - φE]` there is `w ∈ [-m, m]` with
`π/2 - (1/2) arctan (w/η) = v`. -/
lemma exists_arcAngleU {η m v : ℝ} (hη : 0 < η) (hm : 0 < m)
    (hv : v ∈ Set.Icc (mobiusPhiE η m) (Real.pi - mobiusPhiE η m)) :
    ∃ w ∈ Set.Icc (-m) m, Real.pi / 2 - (1 / 2) * Real.arctan (w / η) = v := by
  have hφ : mobiusPhiE η m = Real.pi / 2 - (1 / 2) * Real.arctan (m / η) :=
    bridgeRow_mobiusPhiE_eq_arctan hη hm
  have harm : Real.arctan ((-m) / η) = -Real.arctan (m / η) := by
    rw [show (-m) / η = -(m / η) by ring, Real.arctan_neg]
  have hcont : ContinuousOn (fun w : ℝ => Real.pi / 2 - (1 / 2) * Real.arctan (w / η))
      (Set.Icc (-m) m) := by fun_prop
  have h1 : (fun w : ℝ => Real.pi / 2 - (1 / 2) * Real.arctan (w / η)) m ≤ v := by
    show Real.pi / 2 - (1 / 2) * Real.arctan (m / η) ≤ v
    rw [← hφ]; exact hv.1
  have h2 : v ≤ (fun w : ℝ => Real.pi / 2 - (1 / 2) * Real.arctan (w / η)) (-m) := by
    show v ≤ Real.pi / 2 - (1 / 2) * Real.arctan ((-m) / η)
    rw [harm]
    have hh : Real.pi / 2 - (1 / 2) * -Real.arctan (m / η)
        = Real.pi - mobiusPhiE η m := by rw [hφ]; ring
    rw [hh]; exact hv.2
  have hmem : v ∈ Set.Icc ((fun w : ℝ => Real.pi / 2 - (1 / 2) * Real.arctan (w / η)) m)
      ((fun w : ℝ => Real.pi / 2 - (1 / 2) * Real.arctan (w / η)) (-m)) := ⟨h1, h2⟩
  obtain ⟨w, hw, hwv⟩ := intermediate_value_Icc' (by linarith : (-m : ℝ) ≤ m) hcont hmem
  exact ⟨w, hw, hwv⟩

/-- **The lower arc range.**  For `v` in `[-π + φE, -φE]` there is `w ∈ [-m, m]` with
`-(π/2) - (1/2) arctan (w/η) = v`. -/
lemma exists_arcAngleL {η m v : ℝ} (hη : 0 < η) (hm : 0 < m)
    (hv : v ∈ Set.Icc (-(Real.pi - mobiusPhiE η m)) (-(mobiusPhiE η m))) :
    ∃ w ∈ Set.Icc (-m) m, -(Real.pi / 2) - (1 / 2) * Real.arctan (w / η) = v := by
  have hφ : mobiusPhiE η m = Real.pi / 2 - (1 / 2) * Real.arctan (m / η) :=
    bridgeRow_mobiusPhiE_eq_arctan hη hm
  have harm : Real.arctan ((-m) / η) = -Real.arctan (m / η) := by
    rw [show (-m) / η = -(m / η) by ring, Real.arctan_neg]
  have hcont : ContinuousOn (fun w : ℝ => -(Real.pi / 2) - (1 / 2) * Real.arctan (w / η))
      (Set.Icc (-m) m) := by fun_prop
  have h1 : (fun w : ℝ => -(Real.pi / 2) - (1 / 2) * Real.arctan (w / η)) m ≤ v := by
    show -(Real.pi / 2) - (1 / 2) * Real.arctan (m / η) ≤ v
    have hh : -(Real.pi / 2) - (1 / 2) * Real.arctan (m / η)
        = -(Real.pi - mobiusPhiE η m) := by rw [hφ]; ring
    rw [hh]; exact hv.1
  have h2 : v ≤ (fun w : ℝ => -(Real.pi / 2) - (1 / 2) * Real.arctan (w / η)) (-m) := by
    show v ≤ -(Real.pi / 2) - (1 / 2) * Real.arctan ((-m) / η)
    rw [harm]
    have hh : -(Real.pi / 2) - (1 / 2) * -Real.arctan (m / η)
        = -(mobiusPhiE η m) := by rw [hφ]; ring
    rw [hh]; exact hv.2
  have hmem : v ∈ Set.Icc ((fun w : ℝ => -(Real.pi / 2) - (1 / 2) * Real.arctan (w / η)) m)
      ((fun w : ℝ => -(Real.pi / 2) - (1 / 2) * Real.arctan (w / η)) (-m)) := ⟨h1, h2⟩
  obtain ⟨w, hw, hwv⟩ := intermediate_value_Icc' (by linarith : (-m : ℝ) ≤ m) hcont hmem
  exact ⟨w, hw, hwv⟩

end

open scoped ContDiff Topology in
open Set Filter in
/-- **The bridge row `hoff` of the saddle packet.**  If `Θ` is the packet's `1`-periodic angle
function (`StrictMono`, `Θ (t + 1) = Θ t + 2 π`) with the two arc prescriptions on `τU '' [-m, m]`
and `τL '' [-m, m]`, and the radial profile `r` satisfies the bridge bound
`√(ηs² + m²) ≤ r φ ^ 2` on the bridge zone `dist (φ, πℤ) ≤ φE = mobiusPhiE ηs m`, then every
parameter `t` outside the `ℤ`-orbits of the two arc ranges has `c₀ + 2 ηs < r (Θ t) ^ 2`.

The reason: `φU '' [-m, m]` is exactly the arc range `[φE, π - φE]` and
`φL '' [-m, m] = [-π + φE, -φE]`; a parameter outside the `ℤ`-orbits would, by the prescriptions and
the injectivity of `Θ` modulo its period, put `Θ t` in one of those two ranges, so its class mod `π`
lies in the bridge zone.  This is the row `hoff` of `Work.Drive.N2Lead.saddlePacketRows`. -/
theorem saddleBridgeRow {ηs m c₀ : ℝ} (hηs : 0 < ηs) (hm : 0 < m)
    {r Θ τU τL : ℝ → ℝ}
    (hΘmono : StrictMono Θ) (hΘper : ∀ t : ℝ, Θ (t + 1) = Θ t + 2 * Real.pi)
    (hΘU : ∀ w ∈ Set.Icc (-m) m, Θ (τU w) = Real.pi / 2 - (1 / 2) * Real.arctan (w / ηs))
    (hΘL : ∀ w ∈ Set.Icc (-m) m, Θ (τL w) = -(Real.pi / 2) - (1 / 2) * Real.arctan (w / ηs))
    (hbridge : ∀ (φ : ℝ) (k : ℤ), |φ - k * Real.pi| ≤ Work.Drive.N2Lead.mobiusPhiE ηs m →
      Real.sqrt (ηs ^ 2 + m ^ 2) ≤ r φ ^ 2)
    (hnum : c₀ + 2 * ηs < Real.sqrt (ηs ^ 2 + m ^ 2)) :
    ∀ t : ℝ, (∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-m) m → t ≠ τU w + k) →
      (∀ (w : ℝ) (k : ℤ), w ∈ Set.Icc (-m) m → t ≠ τL w + k) → c₀ + 2 * ηs < r (Θ t) ^ 2 := by
  intro t hU hL
  set φ : ℝ := Θ t with hφdef
  have hinj : Function.Injective Θ := hΘmono.injective
  have hshift := theta_add_int hΘper
  have hEpos : 0 < mobiusPhiE ηs m := (leadProfile_phiE hηs hm).2.1
  -- The bridge zone, stated for the local `φ = Θ t`
  have hkey : ∃ k : ℤ, |φ - k * Real.pi| ≤ mobiusPhiE ηs m := by
    by_contra hcon
    push_neg at hcon
    set n : ℤ := ⌊φ / Real.pi⌋ with hn
    have hnle : (n : ℝ) * Real.pi ≤ φ := by
      have h := Int.floor_le (φ / Real.pi)
      rw [← hn] at h
      calc (n : ℝ) * Real.pi ≤ (φ / Real.pi) * Real.pi :=
            mul_le_mul_of_nonneg_right h Real.pi_pos.le
        _ = φ := by rw [div_mul_cancel₀ _ (ne_of_gt Real.pi_pos)]
    have hnlt : φ < ((n : ℝ) + 1) * Real.pi := by
      have h := Int.lt_floor_add_one (φ / Real.pi)
      rw [← hn] at h
      have h' : φ / Real.pi < ((n + 1 : ℤ) : ℝ) := by push_cast; exact h
      calc φ = (φ / Real.pi) * Real.pi := by rw [div_mul_cancel₀ _ (ne_of_gt Real.pi_pos)]
        _ < ((n + 1 : ℤ) : ℝ) * Real.pi := mul_lt_mul_of_pos_right h' Real.pi_pos
        _ = ((n : ℝ) + 1) * Real.pi := by push_cast; ring
    -- `n π + φE < φ < (n+1) π - φE`
    have hE1 : mobiusPhiE ηs m < φ - n * Real.pi := by
      by_contra hle
      push_neg at hle
      have h0 : 0 ≤ φ - n * Real.pi := by linarith [hnle]
      have h0' : -mobiusPhiE ηs m ≤ φ - n * Real.pi := by linarith [hEpos]
      exact absurd (hcon n) (not_lt.mpr (abs_le.mpr ⟨h0', hle⟩))
    have hE2 : φ - n * Real.pi < Real.pi - mobiusPhiE ηs m := by
      by_contra hle
      push_neg at hle
      have hup : ((n + 1 : ℤ) : ℝ) * Real.pi - φ ≤ mobiusPhiE ηs m := by
        have h1 : ((n + 1 : ℤ) : ℝ) * Real.pi = (n : ℝ) * Real.pi + Real.pi := by
          push_cast; ring
        rw [h1]; linarith
      have hnonneg : 0 ≤ ((n + 1 : ℤ) : ℝ) * Real.pi - φ := by
        have h1 : ((n + 1 : ℤ) : ℝ) * Real.pi = (n : ℝ) * Real.pi + Real.pi := by
          push_cast; ring
        rw [h1]; linarith
      have hneg : -mobiusPhiE ηs m ≤ ((n + 1 : ℤ) : ℝ) * Real.pi - φ := by
        linarith [hEpos, hup]
      have habs : |φ - ((n + 1 : ℤ) : ℝ) * Real.pi| ≤ mobiusPhiE ηs m := by
        rw [abs_sub_comm]; exact abs_le.mpr ⟨hneg, hup⟩
      exact absurd (hcon (n + 1)) (not_lt.mpr habs)
    -- the class of `φ` modulo `2π` is either in the upper or in the lower arc range
    rcases Int.even_or_odd n with hev | hod
    · obtain ⟨j, hj⟩ := hev
      have hjn : n = 2 * j := by rw [hj]; ring
      have hv : φ - 2 * (j : ℝ) * Real.pi ∈
          Set.Icc (mobiusPhiE ηs m) (Real.pi - mobiusPhiE ηs m) := by
        have hnx : (n : ℝ) * Real.pi = 2 * (j : ℝ) * Real.pi := by
          rw [hjn]; push_cast; ring
        constructor
        · rw [← hnx]; linarith
        · rw [← hnx]; linarith
      obtain ⟨w, hw, hwu⟩ := exists_arcAngleU hηs hm hv
      have hΘw : Θ (τU w) = φ - 2 * (j : ℝ) * Real.pi := by rw [hΘU w hw, hwu]
      have hΘtj : Θ (t - (j : ℝ)) = φ - 2 * (j : ℝ) * Real.pi := by
        have h := hshift j (t - (j : ℝ))
        have htxt : (t - ((j : ℤ) : ℝ)) + ((j : ℤ) : ℝ) = t := by ring
        rw [htxt] at h
        rw [← hφdef] at h
        have h2 : Θ (t - ((j : ℤ) : ℝ)) = φ - 2 * Real.pi * ((j : ℤ) : ℝ) := by linarith
        rw [h2]; ring
      have heq : τU w = t - (j : ℝ) := hinj (by rw [hΘw, hΘtj])
      exact absurd (by rw [heq]; ring : t = τU w + (j : ℝ)) (hU w j hw)
    · obtain ⟨j, hj⟩ := hod
      have hjn : n = 2 * j + 1 := hj
      have hv : φ - 2 * (j + 1 : ℤ) * Real.pi ∈
          Set.Icc (-(Real.pi - mobiusPhiE ηs m)) (-(mobiusPhiE ηs m)) := by
        have hnx : (n : ℝ) * Real.pi = 2 * (j : ℝ) * Real.pi + Real.pi := by
          rw [hjn]; push_cast; ring
        have hkey' : φ - 2 * ((j + 1 : ℤ) : ℝ) * Real.pi
            = φ - (n : ℝ) * Real.pi - Real.pi := by
          rw [hnx]; push_cast; ring
        constructor
        · rw [hkey']; linarith
        · rw [hkey']; linarith
      obtain ⟨w, hw, hwv⟩ := exists_arcAngleL hηs hm hv
      have hΘw : Θ (τL w) = φ - 2 * ((j + 1 : ℤ) : ℝ) * Real.pi := by rw [hΘL w hw, hwv]
      have hΘtj : Θ (t - ((j + 1 : ℤ) : ℝ)) = φ - 2 * ((j + 1 : ℤ) : ℝ) * Real.pi := by
        have h := hshift (j + 1) (t - ((j + 1 : ℤ) : ℝ))
        have htxt : (t - ((j + 1 : ℤ) : ℝ)) + ((j + 1 : ℤ) : ℝ) = t := by ring
        rw [htxt] at h
        rw [← hφdef] at h
        have h2 : Θ (t - ((j + 1 : ℤ) : ℝ)) = φ - 2 * Real.pi * ((j + 1 : ℤ) : ℝ) := by
          linarith
        rw [h2]; ring
      have heq : τL w = t - ((j + 1 : ℤ) : ℝ) := hinj (by rw [hΘw, hΘtj])
      exact absurd (by rw [heq]; ring : t = τL w + ((j + 1 : ℤ) : ℝ)) (hL w (j + 1) hw)
  obtain ⟨k, hk⟩ := hkey
  exact lt_of_lt_of_le hnum (hbridge (Θ t) k (by rw [← hφdef]; exact hk))

end Work.Drive.N2Lead
