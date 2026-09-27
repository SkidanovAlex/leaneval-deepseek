import Mathlib
import Submission.Work.Drive.N2Lead.saddleBridgeRow

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter
open Work.Drive.N2Lead

/-! ## Auxiliary: the *open* arc ranges

`saddleBridgeRow.lean` proves the exact arc ranges of the two angle maps on the **closed** arc
`[-m, m]`: `[φE, π - φE]` (upper) and `[-π + φE, -φE]` (lower), `φE = mobiusPhiE η m`.  The coverage
row of the upper saddle certificate (`arcRangeOrBridgeZone`) is stated with the **open** arcs
`Ioo (-m) m` and the **closed** bridge zone `dist (·, πℤ) ≤ φE`; the difference is exactly the four
endpoints, whose angle images are `±φE`, `π ∓ φE` and which the bridge zone covers.

The two lemmas below upgrade the closed ranges to the open ones: strictly inside the range the
pre-image of the endpoint cannot be the endpoint `w = ±m`. -/

/-- The upper arc map `w ↦ π/2 - (1/2) arctan (w/η)` restricted to the **open** arc has image
exactly the open interval `(φE, π - φE)`. -/
lemma exists_arcAngleU_Ioo {η m v : ℝ} (hη : 0 < η) (hm : 0 < m)
    (hv : v ∈ Set.Ioo (mobiusPhiE η m) (Real.pi - mobiusPhiE η m)) :
    ∃ w ∈ Set.Ioo (-m) m, Real.pi / 2 - (1 / 2) * Real.arctan (w / η) = v := by
  obtain ⟨w, hw, hwu⟩ := exists_arcAngleU hη hm ⟨le_of_lt hv.1, le_of_lt hv.2⟩
  have hφ : mobiusPhiE η m = Real.pi / 2 - (1 / 2) * Real.arctan (m / η) :=
    bridgeRow_mobiusPhiE_eq_arctan hη hm
  have hne_m : w ≠ m := by
    intro hwm
    have h1 : Real.pi / 2 - (1 / 2) * Real.arctan (w / η) = mobiusPhiE η m := by
      rw [hwm, hφ]
    linarith [hv.1, hwu, h1]
  have hne_negm : w ≠ -m := by
    intro hwm
    have harm : Real.arctan ((-m) / η) = -Real.arctan (m / η) := by
      rw [show (-m) / η = -(m / η) by ring, Real.arctan_neg]
    have h1 : Real.pi / 2 - (1 / 2) * Real.arctan (w / η) = Real.pi - mobiusPhiE η m := by
      rw [hwm, harm, hφ]; ring
    linarith [hv.2, hwu, h1]
  exact ⟨w, ⟨lt_of_le_of_ne hw.1 (Ne.symm hne_negm), lt_of_le_of_ne hw.2 hne_m⟩, hwu⟩

/-- The lower arc map `w ↦ -(π/2) - (1/2) arctan (w/η)` restricted to the **open** arc has image
exactly the open interval `(-(π - φE), -φE)`. -/
lemma exists_arcAngleL_Ioo {η m v : ℝ} (hη : 0 < η) (hm : 0 < m)
    (hv : v ∈ Set.Ioo (-(Real.pi - mobiusPhiE η m)) (-(mobiusPhiE η m))) :
    ∃ w ∈ Set.Ioo (-m) m, -(Real.pi / 2) - (1 / 2) * Real.arctan (w / η) = v := by
  obtain ⟨w, hw, hwu⟩ := exists_arcAngleL hη hm ⟨le_of_lt hv.1, le_of_lt hv.2⟩
  have hφ : mobiusPhiE η m = Real.pi / 2 - (1 / 2) * Real.arctan (m / η) :=
    bridgeRow_mobiusPhiE_eq_arctan hη hm
  have hne_m : w ≠ m := by
    intro hwm
    have h1 : -(Real.pi / 2) - (1 / 2) * Real.arctan (w / η)
        = -(Real.pi - mobiusPhiE η m) := by
      rw [hwm, hφ]; ring
    linarith [hv.1, hwu, h1]
  have hne_negm : w ≠ -m := by
    intro hwm
    have harm : Real.arctan ((-m) / η) = -Real.arctan (m / η) := by
      rw [show (-m) / η = -(m / η) by ring, Real.arctan_neg]
    have h1 : -(Real.pi / 2) - (1 / 2) * Real.arctan (w / η) = -(mobiusPhiE η m) := by
      rw [hwm, harm, hφ]; ring
    linarith [hv.2, hwu, h1]
  exact ⟨w, ⟨lt_of_le_of_ne hw.1 (Ne.symm hne_negm), lt_of_le_of_ne hw.2 hne_m⟩, hwu⟩

open scoped Manifold ContDiff Topology in
open Set Filter in
/-- **The coverage row of the upper saddle certificate.**  On the marked component of the anchor
level, every parameter `t` of the packet's polar curve `t ↦ cE3 (r (Θ t) exp (i Θ t))` either lies in
the `ℤ`-orbit of one of the two **open** pinned arcs `τU '' Ioo (-m) m`, `τL '' Ioo (-m) m`, or its
angle `Θ t` lies in the closed **bridge zone** `dist (Θ t, πℤ) ≤ φE = mobiusPhiE η m`.

The two arc ranges have `Θ`-images `[φE, π - φE]` (upper) and `[-π + φE, -φE]` (lower), and the
bridge zones cover `[kπ - φE, kπ + φE]`; the union of all of them is the whole line, the endpoints
`Θ = ±φE, π ∓ φE` of the closed arc ranges lying in the bridge zone. -/
theorem arcRangeOrBridgeZone {η m : ℝ} (hη : 0 < η) (hm : 1 < m)
    {τU τL Θ : ℝ → ℝ}
    (hΘmono : StrictMono Θ)
    (hΘper : ∀ t : ℝ, Θ (t + 1) = Θ t + 2 * Real.pi)
    (hΘU : ∀ w ∈ Set.Icc (-m) m,
      Θ (τU w) = Real.pi / 2 - (1 / 2) * Real.arctan (w / η))
    (hΘL : ∀ w ∈ Set.Icc (-m) m,
      Θ (τL w) = -(Real.pi / 2) - (1 / 2) * Real.arctan (w / η))
    (t : ℝ) :
    (∃ w ∈ Set.Ioo (-m) m, ∃ k : ℤ, t = τU w + k) ∨
      (∃ w ∈ Set.Ioo (-m) m, ∃ k : ℤ, t = τL w + k) ∨
      (∃ k : ℤ, |Θ t - k * Real.pi| ≤ Work.Drive.N2Lead.mobiusPhiE η m) := by
  have hm0 : 0 < m := lt_trans zero_lt_one hm
  by_cases hC : ∃ k : ℤ, |Θ t - k * Real.pi| ≤ mobiusPhiE η m
  · exact Or.inr (Or.inr hC)
  · push Not at hC
    have hinj : Function.Injective Θ := hΘmono.injective
    have hshift := theta_add_int hΘper
    have hEpos : 0 < mobiusPhiE η m := (leadProfile_phiE hη hm0).2.1
    set φ : ℝ := Θ t with hφdef
    set n : ℤ := ⌊φ / Real.pi⌋ with hn
    -- the two neighbours of `φ` on the lattice `πℤ`
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
    -- the strict version of the two bridge inequalities, because we are outside the bridge zone
    have hE1 : mobiusPhiE η m < φ - (n : ℝ) * Real.pi := by
      by_contra hle
      push Not at hle
      have habs : |φ - (n : ℝ) * Real.pi| ≤ mobiusPhiE η m :=
        abs_le.mpr ⟨by linarith [hnle, hEpos], hle⟩
      exact absurd (by rw [hφdef]; exact hC n) (not_lt.mpr habs)
    have hE2 : φ - (n : ℝ) * Real.pi < Real.pi - mobiusPhiE η m := by
      by_contra hle
      push Not at hle
      have hup : ((n + 1 : ℤ) : ℝ) * Real.pi - φ ≤ mobiusPhiE η m := by
        have h1 : ((n + 1 : ℤ) : ℝ) * Real.pi = (n : ℝ) * Real.pi + Real.pi := by
          push_cast; ring
        rw [h1]; linarith
      have hnonneg : 0 ≤ ((n + 1 : ℤ) : ℝ) * Real.pi - φ := by
        have h1 : ((n + 1 : ℤ) : ℝ) * Real.pi = (n : ℝ) * Real.pi + Real.pi := by
          push_cast; ring
        rw [h1]; linarith
      have hneg : -mobiusPhiE η m ≤ ((n + 1 : ℤ) : ℝ) * Real.pi - φ := by
        linarith [hEpos, hup]
      have habs : |φ - ((n + 1 : ℤ) : ℝ) * Real.pi| ≤ mobiusPhiE η m := by
        rw [abs_sub_comm]; exact abs_le.mpr ⟨hneg, hup⟩
      exact absurd (by rw [hφdef]; exact hC (n + 1)) (not_lt.mpr habs)
    -- the class of `φ` modulo `2π` lies in the upper or in the lower OPEN arc range
    rcases Int.even_or_odd n with hev | hod
    · obtain ⟨j, hj⟩ := hev
      have hjn : n = 2 * j := by rw [hj]; ring
      have hv : φ - 2 * (j : ℝ) * Real.pi ∈
          Set.Ioo (mobiusPhiE η m) (Real.pi - mobiusPhiE η m) := by
        have hnx : ((n : ℤ) : ℝ) * Real.pi = 2 * (j : ℝ) * Real.pi := by
          rw [hjn]; push_cast; ring
        constructor
        · rw [← hnx]; linarith
        · rw [← hnx]; linarith
      obtain ⟨w, hw, hwu⟩ := exists_arcAngleU_Ioo hη hm0 hv
      have hΘw : Θ (τU w) = φ - 2 * (j : ℝ) * Real.pi := by
        rw [hΘU w (Ioo_subset_Icc_self hw), hwu]
      have hΘtj : Θ (t - (j : ℝ)) = φ - 2 * (j : ℝ) * Real.pi := by
        have h := hshift j (t - (j : ℝ))
        have htxt : (t - ((j : ℤ) : ℝ)) + ((j : ℤ) : ℝ) = t := by ring
        rw [htxt] at h
        rw [← hφdef] at h
        have h2 : Θ (t - ((j : ℤ) : ℝ)) = φ - 2 * Real.pi * ((j : ℤ) : ℝ) := by linarith
        rw [h2]; ring
      have heq : τU w = t - (j : ℝ) := hinj (by rw [hΘw, hΘtj])
      exact Or.inl ⟨w, hw, j, by rw [heq]; ring⟩
    · obtain ⟨j, hj⟩ := hod
      have hjn : n = 2 * j + 1 := hj
      have hv : φ - 2 * ((j + 1 : ℤ) : ℝ) * Real.pi ∈
          Set.Ioo (-(Real.pi - mobiusPhiE η m)) (-(mobiusPhiE η m)) := by
        have hnx : ((n : ℤ) : ℝ) * Real.pi = 2 * (j : ℝ) * Real.pi + Real.pi := by
          rw [hjn]; push_cast; ring
        have hkey' : φ - 2 * ((j + 1 : ℤ) : ℝ) * Real.pi
            = φ - (n : ℝ) * Real.pi - Real.pi := by
          rw [hnx]; push_cast; ring
        constructor
        · rw [hkey']; linarith
        · rw [hkey']; linarith
      obtain ⟨w, hw, hwv⟩ := exists_arcAngleL_Ioo hη hm0 hv
      have hΘw : Θ (τL w) = φ - 2 * ((j + 1 : ℤ) : ℝ) * Real.pi := by
        rw [hΘL w (Ioo_subset_Icc_self hw), hwv]
      have hΘtj : Θ (t - ((j + 1 : ℤ) : ℝ)) = φ - 2 * ((j + 1 : ℤ) : ℝ) * Real.pi := by
        have h := hshift (j + 1) (t - ((j + 1 : ℤ) : ℝ))
        have htxt : (t - ((j + 1 : ℤ) : ℝ)) + ((j + 1 : ℤ) : ℝ) = t := by ring
        rw [htxt] at h
        rw [← hφdef] at h
        have h2 : Θ (t - ((j + 1 : ℤ) : ℝ)) = φ - 2 * Real.pi * ((j + 1 : ℤ) : ℝ) := by
          linarith
        rw [h2]; ring
      have heq : τL w = t - ((j + 1 : ℤ) : ℝ) := hinj (by rw [hΘw, hΘtj])
      exact Or.inr (Or.inl ⟨w, hw, j + 1, by rw [heq]; ring⟩)

end Work.Drive.N2Lead
