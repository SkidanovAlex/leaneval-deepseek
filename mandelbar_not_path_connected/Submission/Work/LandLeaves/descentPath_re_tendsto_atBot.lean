import Mathlib
import Submission.Work.LandLeaves.chart_descent_bound
import Submission.Work.LandLeaves.chart_descent_step

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter

/-- **The descent along a path converging to a parabolic fixed point.**  Let `H` be a germ at `0`
with `‖H z - z - c z^r‖ ≤ A ‖z‖^(r+1)` for `‖z‖ < ρ`, where `c ≠ 0` and `r ≥ 2`, and let
`q : ℝ → ℂ` be a continuous path with `q t ≠ 0`, `q (t+1) = H (q t)` and `q t → 0` as `t → +∞`.
Then in the descent chart `Z w = 1 / (((r:ℂ)-1) * c * w^(r-1))` the real part of `Z (q t)` tends
to `-∞`.

Hint. `Work.LandLeaves.chart_descent_bound` gives `R > 0`, `M ≥ 0` with
`‖Z (H w) - (Z w - 1)‖ ≤ M ‖Z w‖^(-1/(r-1))` whenever `R ≤ ‖Z w‖`; here `H 0 = 0` follows from
`happrox` at `z = 0`.  Since `q t → 0`, for `t ≥ S` one has `‖Z (q t)‖ ≥ max R (2M)^(r-1)`, hence
`Re (Z (q (t+1))) ≤ Re (Z (q t)) - 1/2`; iterating, `Re (Z (q (s-n))) ≥ Re (Z (q s)) + n/2`
whenever `s - n ≥ S`.  If `Re (Z (q s)) ≥ K` happened for arbitrarily large `s`, then with
`n = ⌊s - S⌋` one would get times `s_m ∈ [S, S+1)` with `Re (Z (q s_m)) → +∞`; as
`Re (Z w) ≤ ‖Z w‖ = 1/(((r-1)|c|)‖w‖^(r-1))`, this forces `‖q s_m‖ → 0`, and compactness of
`[S, S+1]` together with continuity of `q` then yields `s*` with `q s* = 0`, contradicting the
hypothesis. -/
theorem descentPath_re_tendsto_atBot {H : ℂ → ℂ} {c : ℂ} {r : ℕ} (hr : 2 ≤ r) (hc : c ≠ 0)
    (happrox : ∃ ρ : ℝ, 0 < ρ ∧ ∃ A : ℝ, 0 ≤ A ∧
      ∀ z : ℂ, ‖z‖ < ρ → ‖H z - z - c * z ^ r‖ ≤ A * ‖z‖ ^ (r + 1))
    {q : ℝ → ℂ} (hqc : ContinuousOn q (Set.Ici 0))
    (hqne : ∀ t ∈ Set.Ici (0 : ℝ), q t ≠ 0)
    (hshift : ∀ t ∈ Set.Ici (0 : ℝ), q (t + 1) = H (q t))
    (hlim : Filter.Tendsto q Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun t : ℝ => (1 / (((r : ℂ) - 1) * c * (q t) ^ (r - 1))).re)
      Filter.atTop Filter.atBot := by
  obtain ⟨ρ, hρ, A, hA, happ⟩ := happrox
  have hr1 : 1 ≤ r := by omega
  have hn1 : 1 ≤ r - 1 := by omega
  have hcastC : (((r - 1 : ℕ)) : ℂ) = (r : ℂ) - 1 := by
    rw [Nat.cast_sub hr1, Nat.cast_one]
  have hrm1 : ((r : ℂ) - 1) ≠ 0 := by
    rw [← hcastC]
    exact_mod_cast (by omega : r - 1 ≠ 0)
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hcApos : 0 < ‖c‖ + A := by linarith
  -- `H 0 = 0`
  have hH0 : H 0 = 0 := by
    have h := happ 0 (by simpa using hρ)
    have hzr : (0 : ℂ) ^ r = 0 := zero_pow (by omega)
    have hzr1 : ‖(0 : ℂ)‖ ^ (r + 1) = 0 := by
      rw [norm_zero]; exact zero_pow (Nat.succ_ne_zero r)
    rw [hzr, hzr1, mul_zero] at h
    exact norm_le_zero_iff.mp (by simpa using h)
  -- the linearisation constant and the radius of `chart_descent_step`
  set C : ℝ := A / ‖c‖ + (4 : ℝ) ^ (r - 1) * (‖c‖ + A) ^ 2 / ((((r - 1 : ℕ)) : ℝ) * ‖c‖)
    with hC
  have hCnn : 0 ≤ C := by
    rw [hC]
    have hden : (0 : ℝ) < (((r - 1 : ℕ)) : ℝ) * ‖c‖ := by
      have h' : (0 : ℝ) < (((r - 1 : ℕ)) : ℝ) := by
        exact_mod_cast (by omega : 0 < r - 1)
      exact mul_pos h' hcpos
    have h1 : 0 ≤ A / ‖c‖ := div_nonneg hA (le_of_lt hcpos)
    have h2 : 0 ≤ (4 : ℝ) ^ (r - 1) * (‖c‖ + A) ^ 2 / ((((r - 1 : ℕ)) : ℝ) * ‖c‖) :=
      div_nonneg (mul_nonneg (by positivity) (sq_nonneg _)) (le_of_lt hden)
    linarith
  set δ : ℝ := min (ρ / 2) (min 1 (min (1 / (2 * (‖c‖ + A))) (1 / (2 * (C + 1)))))
    with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    refine lt_min (by linarith) (lt_min one_pos (lt_min ?_ ?_))
    · exact one_div_pos.mpr (by linarith)
    · exact one_div_pos.mpr (by linarith)
  have hδle1 : δ ≤ 1 := by
    rw [hδ]
    exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hδB : (‖c‖ + A) * δ ≤ 1 / 2 := by
    have hle : δ ≤ 1 / (2 * (‖c‖ + A)) := by
      rw [hδ]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
    calc (‖c‖ + A) * δ ≤ (‖c‖ + A) * (1 / (2 * (‖c‖ + A))) :=
          mul_le_mul_of_nonneg_left hle (le_of_lt hcApos)
      _ = 1 / 2 := by
          rw [mul_one_div, div_eq_iff (by linarith : (2 * (‖c‖ + A)) ≠ 0)]
          ring
  have hδC : C * δ ≤ 1 / 2 := by
    have hle : δ ≤ 1 / (2 * (C + 1)) := by
      rw [hδ]
      exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
    have h2 : (0 : ℝ) < 2 * (C + 1) := by linarith
    calc C * δ ≤ C * (1 / (2 * (C + 1))) := mul_le_mul_of_nonneg_left hle hCnn
      _ ≤ 1 / 2 := by
          rw [mul_one_div, div_le_iff₀ h2]
          linarith
  have hδltρ : δ < ρ := by
    have h : δ ≤ ρ / 2 := by rw [hδ]; exact min_le_left _ _
    linarith
  have happ' : ∀ z : ℂ, ‖z‖ ≤ δ →
      ‖H z - z - c * z ^ ((r - 1) + 1)‖ ≤ A * ‖z‖ ^ ((r - 1) + 2) := by
    intro z hz
    have hzlt : ‖z‖ < ρ := lt_of_le_of_lt hz hδltρ
    have h1 : (r - 1) + 1 = r := by omega
    have h2 : (r - 1) + 2 = r + 1 := by omega
    rw [h1, h2]
    exact happ z hzlt
  have hstep := chart_descent_step (r - 1) hn1 c hc A hA H δ hδpos hδle1 hδB happ'
  have hstep' : ∀ z : ℂ, z ≠ 0 → ‖z‖ ≤ δ →
      ‖1 / (((r : ℂ) - 1) * c * (H z) ^ (r - 1))
        - (1 / (((r : ℂ) - 1) * c * z ^ (r - 1)) - 1)‖ ≤ C * ‖z‖ := by
    intro z hz hzd
    have h := hstep z hz hzd
    rw [hcastC] at h
    rw [hC]
    exact h
  -- the chart coordinate along the path
  set g : ℝ → ℝ := fun t => (1 / (((r : ℂ) - 1) * c * (q t) ^ (r - 1))).re with hg
  have hnormlim : Tendsto (fun t : ℝ => ‖q t‖) atTop (nhds 0) := by
    simpa using hlim.norm
  obtain ⟨S₁, hS₁⟩ := eventually_atTop.mp (hnormlim.eventually (eventually_lt_nhds hδpos))
  set S₀ : ℝ := max S₁ 0 with hS₀def
  have hS₀0 : 0 ≤ S₀ := le_max_right _ _
  have hS₁S₀ : S₁ ≤ S₀ := le_max_left _ _
  have hS₁' : ∀ t : ℝ, S₀ ≤ t → ‖q t‖ < δ := fun t ht => hS₁ t (le_trans hS₁S₀ ht)
  -- one step of the descent along the path
  have hdesc : ∀ t : ℝ, S₀ ≤ t → g (t + 1) ≤ g t - 1 / 2 := by
    intro t ht
    have ht0 : (0 : ℝ) ≤ t := le_trans hS₀0 ht
    have htIci : t ∈ Set.Ici (0 : ℝ) := ht0
    have hqtne : q t ≠ 0 := hqne t htIci
    have hqtδ : ‖q t‖ ≤ δ := le_of_lt (hS₁' t ht)
    have hb := hstep' (q t) hqtne hqtδ
    rw [← hshift t htIci] at hb
    have hC1 : C * ‖q t‖ ≤ 1 / 2 := le_trans (mul_le_mul_of_nonneg_left hqtδ hCnn) hδC
    have hb1 : ‖1 / (((r : ℂ) - 1) * c * (q (t + 1)) ^ (r - 1))
        - (1 / (((r : ℂ) - 1) * c * (q t) ^ (r - 1)) - 1)‖ ≤ 1 / 2 := le_trans hb hC1
    have hre := Complex.re_le_norm (1 / (((r : ℂ) - 1) * c * (q (t + 1)) ^ (r - 1))
        - (1 / (((r : ℂ) - 1) * c * (q t) ^ (r - 1)) - 1))
    simp only [Complex.sub_re, Complex.one_re] at hre
    rw [hg]
    linarith
  -- iteration: the real part drops linearly
  have hiter : ∀ n : ℕ, ∀ t : ℝ, S₀ ≤ t → g (t + (n : ℝ)) ≤ g t - (n : ℝ) / 2 := by
    intro n
    induction n with
    | zero => intro t ht; simp
    | succ k ih =>
        intro t ht
        have htk : S₀ ≤ t + (k : ℝ) := by
          have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
          linarith
        have h1 : g ((t + (k : ℝ)) + 1) ≤ g (t + (k : ℝ)) - 1 / 2 := hdesc (t + (k : ℝ)) htk
        have h2 : g (t + (k : ℝ)) ≤ g t - (k : ℝ) / 2 := ih t ht
        have heq : t + ((k + 1 : ℕ) : ℝ) = (t + (k : ℝ)) + 1 := by push_cast; ring
        have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
        rw [heq, hcast]
        linarith
  -- boundedness of the chart coordinate on the first unit interval
  have hqcont : ContinuousOn q (Set.Icc S₀ (S₀ + 1)) :=
    hqc.mono (Set.Icc_subset_Ici_self.trans (Set.Ici_subset_Ici.mpr hS₀0))
  have hZcont : ContinuousOn (fun z : ℂ => 1 / (((r : ℂ) - 1) * c * z ^ (r - 1)))
      {z : ℂ | z ≠ 0} := by
    have hpoly : Continuous (fun z : ℂ => (((r : ℂ) - 1) * c) * z ^ (r - 1)) :=
      continuous_const.mul (continuous_id.pow (r - 1))
    refine continuousOn_const.div hpoly.continuousOn ?_
    intro z hz
    exact mul_ne_zero (mul_ne_zero hrm1 hc) (pow_ne_zero _ hz)
  have hmaps : Set.MapsTo q (Set.Icc S₀ (S₀ + 1)) {z : ℂ | z ≠ 0} := by
    intro t ht
    exact hqne t (le_trans hS₀0 ht.1)
  have hgcont : ContinuousOn g (Set.Icc S₀ (S₀ + 1)) := by
    rw [hg]
    exact Complex.continuous_re.comp_continuousOn (hZcont.comp hqcont hmaps)
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ t ∈ Set.Icc S₀ (S₀ + 1), g t ≤ B := by
    have hcpt : IsCompact (g '' Set.Icc S₀ (S₀ + 1)) :=
      isCompact_Icc.image_of_continuousOn hgcont
    obtain ⟨B, hB⟩ := hcpt.bddAbove
    exact ⟨B, fun t ht => (mem_upperBounds.mp hB) (g t) ⟨t, ht, rfl⟩⟩
  -- the limit
  have hgt : Tendsto g atTop atBot := by
    rw [tendsto_atBot]
    intro K
    obtain ⟨n, hn⟩ := exists_nat_gt (2 * (B - K))
    rw [eventually_atTop]
    refine ⟨S₀ + (n : ℝ) + 1, fun t ht => ?_⟩
    have htS : S₀ ≤ t := by linarith
    have htn : (n : ℝ) + 1 ≤ t - S₀ := by linarith
    set m : ℕ := Nat.floor (t - S₀) with hm
    have hmle : (m : ℝ) ≤ t - S₀ := by
      rw [hm]; exact Nat.floor_le (by linarith)
    have hmlt : t - S₀ < (m : ℝ) + 1 := by
      rw [hm]; exact Nat.lt_floor_add_one _
    have hmn : n ≤ m := by
      rw [hm]; exact Nat.le_floor (by linarith)
    set θ : ℝ := t - S₀ - (m : ℝ) with hθ
    have hθS : S₀ ≤ S₀ + θ := by rw [hθ]; linarith
    have hθmem : S₀ + θ ∈ Set.Icc S₀ (S₀ + 1) := by
      refine ⟨?_, ?_⟩
      · rw [hθ]; linarith
      · rw [hθ]; linarith
    have htm : t = S₀ + θ + (m : ℝ) := by rw [hθ]; ring
    have hstep1 : g t ≤ g (S₀ + θ) - (m : ℝ) / 2 := by
      have h1 := hiter m (S₀ + θ) hθS
      rw [← htm] at h1
      exact h1
    have hBθ : g (S₀ + θ) ≤ B := hB (S₀ + θ) hθmem
    have hnm : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hmn
    have hK : B - (m : ℝ) / 2 ≤ K := by linarith
    linarith
  exact hgt

end Work.LandLeaves
