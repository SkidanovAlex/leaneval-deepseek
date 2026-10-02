import Mathlib
import Submission.Work.LandLeaves.tendsto_normRatio_sub

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.LandLeaves

open Filter Asymptotics Set
open scoped Topology

/-- The direction of a curve `Γ` which is strictly contracted by `F` lies in the closed sector
`Re ((c/lam) * d^n) ≤ 0`, where `F w = lam * w + c * w^(n+1) + o(w^(n+1))` with `‖lam‖ = 1`.
Hint: `tendsto_normRatio_sub` (same directory) gives
`‖F w‖/‖w‖ - 1 - ((c/lam) * w^n).re = o(‖w‖^n)`, so on the curve
`Re ((c/lam) * u(t)^n) ≤ o(1)` where `u t = Γ t / ‖Γ t‖`; pass to the limit along a sequence
`t_k → 0` with `u(t_k) → d`, which exists by `hd`. -/
theorem sector_bound {F : ℂ → ℂ} {lam c : ℂ} {n : ℕ} (hn : 1 ≤ n) (hlam : ‖lam‖ = 1)
    (hExp : (fun w : ℂ => F w - lam * w - c * w ^ (n + 1)) =o[𝓝 0] (fun w : ℂ => w ^ (n + 1)))
    {Γ : ℝ → ℂ} {δ₀ : ℝ} (hδ₀ : 0 < δ₀) (hΓc : ContinuousOn Γ (Set.Ioc 0 δ₀))
    (hΓt : Tendsto Γ (𝓝[>] (0:ℝ)) (𝓝 0)) (hΓne : ∀ t ∈ Set.Ioc 0 δ₀, Γ t ≠ 0)
    (hdec : ∀ t ∈ Set.Ioc 0 δ₀, ‖F (Γ t)‖ < ‖Γ t‖)
    {d : ℂ} (hd : ∀ δ ∈ Set.Ioc (0:ℝ) δ₀, d ∈ closure ((fun t => Γ t / ‖Γ t‖) '' Set.Ioc (0:ℝ) δ)) :
    ((c / lam) * d ^ n).re ≤ 0 := by
  -- The second-order remainder in the modulus-ratio expansion.
  set g : ℂ → ℝ := fun w => (‖F w‖ / ‖w‖ - 1 - ((c / lam) * w ^ n).re) / ‖w‖ ^ n with hgdef
  have hgapply : ∀ w : ℂ, g w = (‖F w‖ / ‖w‖ - 1 - ((c / lam) * w ^ n).re) / ‖w‖ ^ n := by
    intro w; simp only [hgdef]
  have hgt : Tendsto g (𝓝[≠] (0:ℂ)) (𝓝 0) := by
    rw [hgdef]
    exact tendsto_normRatio_sub hn hlam hExp
  -- ### Step 1: a sequence `t k → 0⁺` with `Γ (t k)/‖Γ (t k)‖ → d`.
  have hex : ∀ k : ℕ, ∃ t : ℝ,
      t ∈ Set.Ioc (0:ℝ) (min (δ₀ / 2) (1 / ((k : ℝ) + 1))) ∧
        dist (Γ t / ‖Γ t‖) d < 1 / ((k : ℝ) + 1) := by
    intro k
    have hεk : (0 : ℝ) < 1 / ((k : ℝ) + 1) := by positivity
    have hδk_pos : (0 : ℝ) < min (δ₀ / 2) (1 / ((k : ℝ) + 1)) := lt_min (by linarith) hεk
    have hδk_lt : min (δ₀ / 2) (1 / ((k : ℝ) + 1)) < δ₀ :=
      lt_of_le_of_lt (min_le_left _ _) (by linarith)
    obtain ⟨y, hy, hyd⟩ := Metric.mem_closure_iff.mp
      (hd (min (δ₀ / 2) (1 / ((k : ℝ) + 1))) ⟨hδk_pos, le_of_lt hδk_lt⟩) _ hεk
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨t, ht, ?_⟩
    dsimp only at hty
    rw [hty]
    exact dist_comm d y ▸ hyd
  let t : ℕ → ℝ := fun k => Classical.choose (hex k)
  have ht : ∀ k : ℕ, t k ∈ Set.Ioc (0:ℝ) (min (δ₀ / 2) (1 / ((k : ℝ) + 1))) ∧
      dist (Γ (t k) / ‖Γ (t k)‖) d < 1 / ((k : ℝ) + 1) :=
    fun k => Classical.choose_spec (hex k)
  have ht_mem : ∀ k : ℕ, t k ∈ Set.Ioc (0 : ℝ) δ₀ := by
    intro k
    have h1 : 0 < t k := (ht k).1.1
    have h2 : t k ≤ δ₀ / 2 := le_trans (ht k).1.2 (min_le_left _ _)
    exact ⟨h1, le_of_lt (lt_of_le_of_lt h2 (by linarith))⟩
  have ht_tend : Tendsto t atTop (𝓝 (0 : ℝ)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (f := fun k => dist (t k) 0) (g := fun k => 1 / ((k : ℝ) + 1))
      (fun k => dist_nonneg) (fun k => ?_) ?_
    · rw [Real.dist_eq, sub_zero, abs_of_pos (ht_mem k).1]
      exact le_trans (ht k).1.2 (min_le_right _ _)
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hu_tend : Tendsto (fun k => Γ (t k) / ‖Γ (t k)‖) atTop (𝓝 d) := by
    rw [tendsto_iff_dist_tendsto_zero]
    refine squeeze_zero (f := fun k => dist (Γ (t k) / ‖Γ (t k)‖) d)
      (g := fun k => 1 / ((k : ℝ) + 1)) (fun k => dist_nonneg) (fun k => le_of_lt (ht k).2) ?_
    · exact tendsto_one_div_add_atTop_nhds_zero_nat
  have ht' : Tendsto t atTop (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨ht_tend, Filter.Eventually.of_forall fun k => (ht_mem k).1⟩
  have hΓseq_tend : Tendsto (fun k => Γ (t k)) atTop (𝓝[≠] (0 : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hΓt.comp ht', Filter.Eventually.of_forall fun k => ?_⟩
    simpa using hΓne (t k) (ht_mem k)
  -- ### Step 2: pointwise inequality along the curve.
  have hineq : ∀ k : ℕ,
      ((c / lam) * (Γ (t k) / ‖Γ (t k)‖) ^ n).re + g (Γ (t k)) < 0 := by
    intro k
    set w : ℂ := Γ (t k) with hwdef
    have hw : w ≠ 0 := hΓne (t k) (ht_mem k)
    have hwnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
    have hnorm_cast : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact norm_ne_zero_iff.mpr hw
    have hwcancel : ((‖w‖ : ℝ) : ℂ) * (w / ‖w‖) = w := mul_div_cancel₀ w hnorm_cast
    have hpow : ((c / lam) * w ^ n).re = ‖w‖ ^ n * ((c / lam) * (w / ‖w‖) ^ n).re := by
      have h1 : (c / lam) * w ^ n = ((‖w‖ ^ n : ℝ) : ℂ) * ((c / lam) * (w / ‖w‖) ^ n) := by
        conv_lhs => rw [← hwcancel]
        rw [mul_pow, ← Complex.ofReal_pow]
        ring
      rw [h1, Complex.re_ofReal_mul]
    have hgval : ‖w‖ ^ n * g w = ‖F w‖ / ‖w‖ - 1 - ((c / lam) * w ^ n).re := by
      rw [mul_comm, hgapply w]
      exact div_mul_cancel₀ _ (pow_ne_zero n (norm_ne_zero_iff.mpr hw))
    have hRneg : ‖F w‖ / ‖w‖ - 1 < 0 := by
      rw [sub_lt_zero, div_lt_one hwnorm]
      exact hdec (t k) (ht_mem k)
    have hpn : (0 : ℝ) < ‖w‖ ^ n := pow_pos hwnorm n
    have hkey : ‖w‖ ^ n * (((c / lam) * (w / ‖w‖) ^ n).re + g w) < 0 := by
      have h1 : ‖w‖ ^ n * (((c / lam) * (w / ‖w‖) ^ n).re + g w)
          = ((c / lam) * w ^ n).re + (‖F w‖ / ‖w‖ - 1 - ((c / lam) * w ^ n).re) := by
        rw [mul_add, ← hpow, hgval]
      rw [h1]
      have h2 : ((c / lam) * w ^ n).re + (‖F w‖ / ‖w‖ - 1 - ((c / lam) * w ^ n).re)
          = ‖F w‖ / ‖w‖ - 1 := by ring
      rw [h2]
      exact hRneg
    have hkey0 : ‖w‖ ^ n * (((c / lam) * (w / ‖w‖) ^ n).re + g w) < ‖w‖ ^ n * 0 := by
      rw [mul_zero]; exact hkey
    exact lt_of_mul_lt_mul_left hkey0 hpn.le
  -- ### Step 3: pass to the limit.
  have hlim : Tendsto
      (fun k => ((c / lam) * (Γ (t k) / ‖Γ (t k)‖) ^ n).re + g (Γ (t k))) atTop
      (𝓝 (((c / lam) * d ^ n).re)) := by
    have hcont : Continuous (fun z : ℂ => ((c / lam) * z ^ n).re) := by fun_prop
    have h1 : Tendsto (fun k => ((c / lam) * (Γ (t k) / ‖Γ (t k)‖) ^ n).re) atTop
        (𝓝 (((c / lam) * d ^ n).re)) := (hcont.tendsto d).comp hu_tend
    have h2 : Tendsto (fun k => g (Γ (t k))) atTop (𝓝 0) := hgt.comp hΓseq_tend
    simpa using h1.add h2
  exact le_of_tendsto' hlim (fun k => le_of_lt (hineq k))

end Work.LandLeaves
