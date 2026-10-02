import Mathlib
import Submission.Work.LandLeaves.Snail.barrierDefs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The left frontier of the barrier tends to `-∞`

Main result: `leftCross_tendsto_atBot` (see the statement at the bottom).
-/

open Filter Set
open scoped Topology

namespace Work.LandLeaves.Snail

/-- **The imaginary part of the path grows at least linearly.**  Once the path is inside the
half plane `{Re < X₀}`, one unit of time raises its imaginary part by at least `c.im / 2`.
Consequently, on a sufficiently deep left half plane whose imaginary part is bounded below,
`Im (P t) ≥ m + (t - t₀ - 1) * (c.im / 2)` for every `t ≥ t₀`. -/
theorem im_lower_bound_linear {F : ℂ → ℂ} {P : ℝ → ℂ} {c : ℂ} {T X₀ t₀ : ℝ}
    (hc_im : 0 < c.im)
    (hheight : ∀ Z : ℂ, Z.re < X₀ → Z.im + c.im / 2 ≤ (F Z).im)
    (hPinv : ∀ t ∈ Set.Ici T, F (P t) = P (t + 1))
    (hPc : ContinuousOn P (Set.Ici T)) (htT : T ≤ t₀)
    (hPt : ∀ t : ℝ, t₀ ≤ t → (P t).re < X₀) :
    ∃ m : ℝ, (∀ u : ℝ, u ∈ Set.Icc t₀ (t₀ + 1) → m ≤ (P u).im) ∧
      (∀ t : ℝ, t₀ ≤ t → m + (t - t₀ - 1) * (c.im / 2) ≤ (P t).im) := by
  have hc2 : 0 < c.im / 2 := by linarith
  have hcont : ContinuousOn (fun u : ℝ => (P u).im) (Set.Icc t₀ (t₀ + 1)) := by
    have h1 : ContinuousOn P (Set.Icc t₀ (t₀ + 1)) :=
      hPc.mono (fun u hu => le_trans htT hu.1)
    simpa [Function.comp_def] using Complex.continuous_im.comp_continuousOn h1
  obtain ⟨x, _hxmem, hxmin⟩ :=
    (isCompact_Icc (a := t₀) (b := t₀ + 1)).exists_isMinOn
      ⟨t₀, le_rfl, by linarith⟩ hcont
  refine ⟨(P x).im, fun u hu => hxmin hu, ?_⟩
  intro t ht
  have htnn : 0 ≤ t - t₀ := by linarith
  set n : ℕ := Nat.floor (t - t₀) with hn
  have hnle : (n : ℝ) ≤ t - t₀ := Nat.floor_le htnn
  have hnlt : t - t₀ < (n : ℝ) + 1 := Nat.lt_floor_add_one (t - t₀)
  have hs1 : t₀ ≤ t - (n : ℝ) := by linarith
  have hs2 : t - (n : ℝ) ≤ t₀ + 1 := by linarith
  have hmin : (P x).im ≤ (P (t - (n : ℝ))).im := hxmin ⟨hs1, hs2⟩
  have hgw : (P (t - (n : ℝ))).im + (n : ℝ) * (c.im / 2) ≤ (P t).im := by
    have := path_height_growth hheight hPinv htT hPt hs1 n
    rwa [show t - (n : ℝ) + (n : ℝ) = t by ring] at this
  have hn' : t - t₀ - 1 < (n : ℝ) := by linarith
  have hmul : (t - t₀ - 1) * (c.im / 2) < (n : ℝ) * (c.im / 2) :=
    mul_lt_mul_of_pos_right hn' hc2
  linarith

theorem leftCross_tendsto_atBot {F : ℂ → ℂ} {P : ℝ → ℂ} {c : ℂ} {T X₀ t₀ : ℝ}
    (hc_im : 0 < c.im) (hPc : ContinuousOn P (Set.Ici T)) (htT : T ≤ t₀)
    (hheight : ∀ Z : ℂ, Z.re < X₀ → Z.im + c.im / 2 ≤ (F Z).im)
    (hPinv : ∀ t ∈ Set.Ici T, F (P t) = P (t + 1))
    (hPt : ∀ t : ℝ, t₀ ≤ t → (P t).re < X₀)
    (hPre : Filter.Tendsto (fun t : ℝ => (P t).re) Filter.atTop Filter.atBot) :
    ∀ M : ℝ, ∃ H : ℝ, ∀ h : ℝ, H ≤ h → Work.LandLeaves.Snail.leftCross P t₀ h < M := by
  intro M
  have hc2 : 0 < c.im / 2 := by linarith
  -- a threshold beyond which the real part is already below `M`
  obtain ⟨t₁, ht₁⟩ : ∃ t₁ : ℝ, ∀ t : ℝ, t₁ ≤ t → (P t).re < M := by
    have h : ∀ᶠ t in Filter.atTop, (P t).re ≤ M - 1 :=
      hPre.eventually (Filter.mem_atBot (M - 1))
    rw [Filter.eventually_atTop] at h
    obtain ⟨t₁, ht₁⟩ := h
    exact ⟨t₁, fun t ht => by linarith [ht₁ t ht]⟩
  -- a base time `s ≥ t₁`, still `≥ t₀`
  obtain ⟨N, hN⟩ : ∃ N : ℕ, t₁ ≤ t₀ + (N : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_ge (t₁ - t₀)
    exact ⟨N, by linarith⟩
  set s : ℝ := t₀ + (N : ℝ) with hs
  have hs_t0 : t₀ ≤ s := by rw [hs]; exact le_add_of_nonneg_right (Nat.cast_nonneg N)
  have hs_t1 : t₁ ≤ s := by rw [hs]; exact hN
  -- the linear lower bound on the imaginary part
  obtain ⟨m, hm1, hm2⟩ := im_lower_bound_linear (F := F) (P := P) (c := c) (T := T)
    (X₀ := X₀) (t₀ := t₀) hc_im hheight hPinv hPc htT hPt
  have hm_le : ∀ t : ℝ, t₀ ≤ t → m ≤ (P t).im := by
    intro t ht
    rcases lt_or_ge t (t₀ + 1) with hcase | hcase
    · exact hm1 t ⟨ht, le_of_lt hcase⟩
    · have hpos : 0 ≤ (t - t₀ - 1) * (c.im / 2) :=
        mul_nonneg (by linarith) (le_of_lt hc2)
      linarith [hm2 t ht]
  refine ⟨(P s).im, ?_⟩
  intro h hh
  have hzgrowth : ∀ n : ℕ, (P s).im + (n : ℝ) * (c.im / 2) ≤ (P (s + (n : ℝ))).im :=
    fun n => path_height_growth hheight hPinv htT hPt hs_t0 n
  -- the heights at integer times are unbounded
  have hex : ∃ n : ℕ, h < (P (s + (n : ℝ))).im := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((h - (P s).im) / (c.im / 2))
    refine ⟨n, ?_⟩
    have h1 : h - (P s).im < (n : ℝ) * (c.im / 2) := by
      rw [div_lt_iff₀ hc2] at hn; exact hn
    linarith [hzgrowth n]
  -- least integer time at which the height exceeds `h`
  obtain ⟨k, hk_spec, hk_min⟩ :
      ∃ k : ℕ, h < (P (s + (k : ℝ))).im ∧
        (∀ j : ℕ, j < k → ¬ (h < (P (s + (j : ℝ))).im)) := by
    refine ⟨Nat.find hex, Nat.find_spec hex, ?_⟩
    intro j hj
    exact Nat.find_min hex hj
  have hk_pos : 1 ≤ k := by
    rw [Nat.one_le_iff_ne_zero]
    intro h0
    rw [h0] at hk_spec
    simp only [Nat.cast_zero, add_zero] at hk_spec
    linarith
  have hk_prev : (P (s + (((k - 1 : ℕ)) : ℝ))).im ≤ h := by
    have hlt : k - 1 < k := Nat.sub_one_lt (Nat.pos_iff_ne_zero.mp hk_pos)
    exact not_lt.mp (hk_min (k - 1) hlt)
  have hcast : (((k - 1 : ℕ)) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk_pos]; norm_num
  -- interval where the intermediate value occurs
  have hk1_nonneg : (0 : ℝ) ≤ (k : ℝ) - 1 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk_pos
    linarith
  have hs_le_a : s ≤ s + ((k : ℝ) - 1) := by linarith
  have hab : s + ((k : ℝ) - 1) ≤ s + (k : ℝ) := by linarith
  have hcontP : ContinuousOn P (Set.Icc (s + ((k : ℝ) - 1)) (s + (k : ℝ))) :=
    hPc.mono (fun u hu => le_trans htT (le_trans hs_t0 (le_trans hs_le_a hu.1)))
  have hcont : ContinuousOn (fun t : ℝ => (P t).im)
      (Set.Icc (s + ((k : ℝ) - 1)) (s + (k : ℝ))) := by
    simpa [Function.comp_def] using Complex.continuous_im.comp_continuousOn hcontP
  have hmem_val : h ∈ Set.Icc ((fun t : ℝ => (P t).im) (s + ((k : ℝ) - 1)))
      ((fun t : ℝ => (P t).im) (s + (k : ℝ))) := by
    constructor
    · show (P (s + ((k : ℝ) - 1))).im ≤ h
      rw [← hcast]; exact hk_prev
    · show h ≤ (P (s + (k : ℝ))).im
      exact le_of_lt hk_spec
  obtain ⟨t, ht_mem, ht_eq⟩ := intermediate_value_Icc hab hcont hmem_val
  have ht_ge_s : s ≤ t := le_trans hs_le_a ht_mem.1
  have ht_ge_t0 : t₀ ≤ t := le_trans hs_t0 ht_ge_s
  have ht_ge_t1 : t₁ ≤ t := le_trans hs_t1 ht_ge_s
  have ht_re : (P t).re < M := ht₁ t ht_ge_t1
  have ht_im : (P t).im = h := ht_eq
  -- the point `P t` witnesses membership
  have hPt_S : (P t).re ∈
      (fun W : ℂ => W.re) '' (pathTail P t₀ ∩ {W : ℂ | W.im = h}) :=
    ⟨P t, ⟨⟨t, ht_ge_t0, rfl⟩, ht_im⟩, rfl⟩
  -- the relevant set of real parts is bounded below
  have hge_m : m ≤ h := le_trans (hm_le s hs_t0) hh
  have htb_ge : t₀ ≤ t₀ + 1 + (h - m) / (c.im / 2) := by
    have : 0 ≤ (h - m) / (c.im / 2) := div_nonneg (by linarith) (le_of_lt hc2)
    linarith
  have hcross : ∀ u : ℝ, t₀ ≤ u → (P u).im = h →
      u ≤ t₀ + 1 + (h - m) / (c.im / 2) := by
    intro u hu hueq
    have hlin := hm2 u hu
    rw [hueq] at hlin
    have h1 : (u - t₀ - 1) * (c.im / 2) ≤ h - m := by linarith
    have h2 : u - t₀ - 1 ≤ (h - m) / (c.im / 2) := (le_div_iff₀ hc2).mpr h1
    linarith
  have hbdd : BddBelow ((fun W : ℂ => W.re) '' (pathTail P t₀ ∩ {W : ℂ | W.im = h})) := by
    have hcontR : ContinuousOn (fun u : ℝ => (P u).re)
        (Set.Icc t₀ (t₀ + 1 + (h - m) / (c.im / 2))) := by
      have h1 : ContinuousOn P (Set.Icc t₀ (t₀ + 1 + (h - m) / (c.im / 2))) :=
        hPc.mono (fun u hu => le_trans htT hu.1)
      simpa [Function.comp_def] using Complex.continuous_re.comp_continuousOn h1
    obtain ⟨x, _hxmem, hxmin⟩ :=
      (isCompact_Icc (a := t₀) (b := t₀ + 1 + (h - m) / (c.im / 2))).exists_isMinOn
        ⟨t₀, le_rfl, htb_ge⟩ hcontR
    refine ⟨(P x).re, ?_⟩
    rintro y ⟨W, hW, rfl⟩
    obtain ⟨hWtail, hWim⟩ := hW
    rw [pathTail] at hWtail
    obtain ⟨u, hu, rfl⟩ := hWtail
    exact hxmin ⟨hu, hcross u hu hWim⟩
  have hne : ((fun W : ℂ => W.re) '' (pathTail P t₀ ∩ {W : ℂ | W.im = h})).Nonempty :=
    ⟨_, hPt_S⟩
  have := (csInf_lt_iff hbdd hne).mpr ⟨(P t).re, hPt_S, ht_re⟩
  simpa only [leftCross] using this

end Work.LandLeaves.Snail
