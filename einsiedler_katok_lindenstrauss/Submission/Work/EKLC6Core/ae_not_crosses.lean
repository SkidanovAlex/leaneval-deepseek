import Mathlib
import Submission.Work.EKLC6Core.ae_ball_in_atom

/-!
# `Work.EKLC6Core.ae_not_crosses` — the uncrossed orbit scale

For an `A`-invariant probability `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, an exponent vector `t`, a rate
`α > 0`, and a finite family `P : Fin N → Set X₃` whose boundary is `μ`-thin in the sense that
the `η`-neighbourhood of `⋃ i, frontier (P i)` (in the `G`-action) has mass `≤ c η`, there is for
`μ`-a.e. `x` a single (random) scale `δ > 0` such that *no* time `n` is crossed:

    ¬ Crosses P (δ · exp(-α n)) (aDiag t ^ n • x)      for all `n`.

This is the "uncrossed orbit" half of Pisa Lemma 7.31: it is exactly the Borel–Cantelli part of
`ae_ball_in_atom`, isolated from the contraction estimate `hcontr` used there.

## Proof

* Since `μ (Nbd P η) ≤ c η` and `Nbd P (500 e^{-α n})` has mass `≤ (500 c) e^{-α n}`, the
  Borel–Cantelli lemma (`measure_iInter_iUnion_exp_eq_zero`) applied along the `a`-orbit
  (`a = aDiag t • ·`, which preserves `μ`) yields a.e. `x` a time `N₀` after which the orbit never
  enters `Nbd P (500 e^{-α n})`.
* For every single time `n` one knows that a.e. point is uncrossed at *some* positive scale
  (`G = ⋃ k {y | ¬ Crosses P (1/(k+801)) y}` is conull, since its complement is contained in
  `Nbd P (500/(k+801))`, of mass `≤ 500 c/(k+801) → 0`).
* Taking the minimum of the finitely many relevant scales for `n < max N₀ n₀` and `1` gives one
  `δ > 0`; for large `n` one has `δ e^{-α n} ≤ e^{-α n} ≤ 1/800` and `crossing_mem` plus the
  Borel–Cantelli statement finish the job.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

theorem ae_not_crosses {t : Fin 3 → ℝ} {α : ℝ} (hα : 0 < α)
    {μ : MeasureTheory.Measure Work.EKLContract.X3} [MeasureTheory.IsProbabilityMeasure μ]
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    {N : ℕ} (P : Fin N → Set Work.EKLContract.X3) (c : ℝ) (hc : 0 < c)
    (hPthin : ∀ η : ℝ, 0 < η →
      μ (Work.EKLC6Core.Nbd P η) ≤ ENNReal.ofReal (c * η)) :
    ∀ᵐ x ∂μ, ∃ δ : ℝ, 0 < δ ∧ ∀ (n : ℕ),
      ¬ Work.EKLC6Core.Crosses P (δ * Real.exp (-(α * ↑n)))
        (Work.EKLContract.aDiag t ^ n • x) := by
  classical
  set a : X3 → X3 := fun y => aDiag t • y with ha
  have hamp : MeasurePreserving a μ μ := by rw [ha]; exact hmp
  have hNbd : ∀ η : ℝ, 0 < η → μ (Nbd P η) ≤ ENNReal.ofReal (c * η) := hPthin
  -- `n₀` with `exp (-(α n)) ≤ 1/800` for `n ≥ n₀`
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ∀ n ≥ n₀, Real.exp (-(α * (n : ℝ))) ≤ 1 / 800 := by
    have hbase0 : (0 : ℝ) ≤ Real.exp (-α) := Real.exp_nonneg _
    have hbase1 : Real.exp (-α) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
    have htend : Tendsto (fun n : ℕ => Real.exp (-α) ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hbase0 hbase1
    have htend' : Tendsto (fun n : ℕ => Real.exp (-(α * (n : ℝ)))) atTop (𝓝 0) := by
      refine htend.congr' ?_
      filter_upwards with n
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    have hev : ∀ᶠ n : ℕ in atTop, Real.exp (-(α * (n : ℝ))) < 1 / 800 :=
      htend'.eventually (isOpen_Iio.mem_nhds (by norm_num))
    obtain ⟨n₁, hn₁⟩ := eventually_atTop.mp hev
    exact ⟨n₁, fun n hn => le_of_lt (hn₁ n hn)⟩
  -- measurable hulls of the thin neighbourhoods along the geometric scale
  choose T hTsub hTmeas hTμ using fun n : ℕ =>
    MeasureTheory.exists_measurable_superset μ (Nbd P (500 * Real.exp (-(α * (n : ℝ)))))
  have hTbound : ∀ n : ℕ,
      μ (T n) ≤ ENNReal.ofReal ((c * 500) * Real.exp (-(α * (n : ℝ)))) := by
    intro n
    rw [hTμ n]
    refine le_trans (hNbd _ (by positivity)) (ENNReal.ofReal_le_ofReal ?_)
    exact le_of_eq (by ring)
  have hAbound : ∀ n : ℕ,
      μ (a^[n] ⁻¹' T n) ≤ ENNReal.ofReal ((c * 500) * Real.exp (-(α * (n : ℝ)))) := by
    intro n
    rw [(hamp.iterate n).measure_preimage (hTmeas n).nullMeasurableSet]
    exact hTbound n
  have hBC : μ (⋂ N' : ℕ, ⋃ n ≥ N', (a^[n] ⁻¹' T n)) = 0 :=
    measure_iInter_iUnion_exp_eq_zero μ (fun n => a^[n] ⁻¹' T n) (by positivity) hα hAbound
  have hBCae : ∀ᵐ x ∂μ, ∃ N₀ : ℕ, ∀ n ≥ N₀, x ∉ a^[n] ⁻¹' T n := by
    rw [MeasureTheory.ae_iff]
    have hset : {x : X3 | ¬ ∃ N₀ : ℕ, ∀ n ≥ N₀, x ∉ a^[n] ⁻¹' T n}
        = ⋂ N' : ℕ, ⋃ n ≥ N', (a^[n] ⁻¹' T n) := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
      push Not
      constructor
      · intro h N'
        obtain ⟨n, hn⟩ := h N'
        exact ⟨n, hn.1, hn.2⟩
      · intro h N'
        obtain ⟨n, hn1, hn2⟩ := h N'
        exact ⟨n, hn1, hn2⟩
    rw [hset]
    exact hBC
  -- the scale at which a.e. point is uncrossed (the "good" set)
  set G : Set X3 := ⋃ k : ℕ, {y : X3 | ¬ Crosses P (1 / ((k : ℝ) + 801)) y} with hG
  have hcross_of_not_mem : ∀ k : ℕ, ∀ y : X3, y ∉ G → Crosses P (1 / ((k : ℝ) + 801)) y := by
    intro k y hy
    by_contra hcon
    refine hy ?_
    rw [hG]
    exact Set.mem_iUnion.mpr ⟨k, hcon⟩
  have hGsub : ∀ k : ℕ, Gᶜ ⊆ Nbd P (500 * (1 / ((k : ℝ) + 801))) := by
    intro k y hy
    refine crossing_mem (by positivity) ?_ (hcross_of_not_mem k y hy)
    refine one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 800) ?_
    linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
  have hGnull : μ Gᶜ = 0 := by
    refine eq_zero_of_forall_le_ofReal fun ε hε => ?_
    obtain ⟨k, hk⟩ : ∃ k : ℕ, c * (500 / ((k : ℝ) + 801)) ≤ ε := by
      obtain ⟨m, hm⟩ := exists_nat_ge (c * 500 / ε + 1)
      refine ⟨m, ?_⟩
      have h1 : c * 500 / ε + 1 ≤ (m : ℝ) := hm
      have h2 : c * 500 / ε ≤ (m : ℝ) := by linarith
      have h3 : c * 500 ≤ (m : ℝ) * ε := by
        rw [div_le_iff₀ hε] at h2; linarith
      have h4 : c * (500 / ((m : ℝ) + 801)) ≤ ε := by
        rw [mul_div_assoc']
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 801)]
        nlinarith [h3, (Nat.cast_nonneg m : (0 : ℝ) ≤ (m : ℝ)),
          (show (0 : ℝ) ≤ c * 500 by positivity)]
      exact h4
    refine le_trans (measure_mono (hGsub k)) ?_
    refine le_trans (hNbd _ (by positivity)) (ENNReal.ofReal_le_ofReal ?_)
    rw [show c * (500 * (1 / ((k : ℝ) + 801))) = c * (500 / ((k : ℝ) + 801)) by ring]
    exact hk
  -- a.e. point is in `G` at every time
  have hGae : ∀ᵐ x ∂μ, ∀ n : ℕ, a^[n] x ∈ G := by
    rw [MeasureTheory.ae_iff]
    have hset : {x : X3 | ¬ ∀ n : ℕ, a^[n] x ∈ G} = ⋃ n, a^[n] ⁻¹' Gᶜ := by
      ext x
      simp only [Set.mem_ofPred_eq, not_forall, Set.mem_iUnion, Set.mem_preimage,
        Set.mem_compl_iff]
    rw [hset]
    obtain ⟨Z, hZG, hZmeas, hZμ⟩ := MeasureTheory.exists_measurable_superset μ Gᶜ
    have hZ0 : μ Z = 0 := by rw [hZμ]; exact hGnull
    have hterm : ∀ n : ℕ, μ (a^[n] ⁻¹' Z) = 0 := fun n => by
      rw [(hamp.iterate n).measure_preimage hZmeas.nullMeasurableSet, hZ0]
    refine le_antisymm ?_ bot_le
    calc μ (⋃ n, a^[n] ⁻¹' Gᶜ)
        ≤ ∑' n : ℕ, μ (a^[n] ⁻¹' Gᶜ) := measure_iUnion_le _
      _ ≤ ∑' n : ℕ, μ (a^[n] ⁻¹' Z) :=
          ENNReal.tsum_le_tsum fun n => measure_mono (Set.preimage_mono hZG)
      _ = 0 := by rw [show (fun n : ℕ => μ (a^[n] ⁻¹' Z)) = fun _ => 0 from funext hterm,
          tsum_zero]
  -- assembly
  filter_upwards [hBCae, hGae] with x hxBC hxG
  obtain ⟨N₀, hN₀⟩ := hxBC
  have hxG' : ∀ n : ℕ, ∃ k : ℕ, ¬ Crosses P (1 / ((k : ℝ) + 801)) (a^[n] x) := by
    intro n
    have h := hxG n
    rw [hG, Set.mem_iUnion] at h
    simpa only [Set.mem_ofPred_eq] using h
  choose kn hkn using hxG'
  have hknpos : ∀ n : ℕ, 0 < 1 / ((kn n : ℝ) + 801) := fun n => by positivity
  -- the minimum of the finitely many relevant scales
  obtain ⟨n₁, -, hn₁min⟩ := Finset.exists_min_image (Finset.range (max N₀ n₀ + 1))
    (fun n : ℕ => (1 / ((kn n : ℝ) + 801)) * Real.exp (α * n))
    ⟨0, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.zero_le _))⟩
  set δ : ℝ := min 1 ((1 / ((kn n₁ : ℝ) + 801)) * Real.exp (α * n₁)) with hδ
  have hδpos : 0 < δ := by
    rw [hδ]
    exact lt_min one_pos (mul_pos (hknpos n₁) (Real.exp_pos _))
  have hδ1 : δ ≤ 1 := by rw [hδ]; exact min_le_left _ _
  have hδle : ∀ n < max N₀ n₀ + 1,
      δ ≤ (1 / ((kn n : ℝ) + 801)) * Real.exp (α * n) := by
    intro n hn
    rw [hδ]
    exact le_trans (min_le_right _ _) (hn₁min n (Finset.mem_range.mpr hn))
  refine ⟨δ, hδpos, ?_⟩
  -- the scale at time `n` is never crossed
  have hfine : ∀ n : ℕ, ¬ Crosses P (δ * Real.exp (-(α * (n : ℝ)))) ((fun z : X3 => aDiag t • z)^[n] x) := by
    intro n
    rcases lt_or_ge n (max N₀ n₀ + 1) with hn | hn
    · -- early times
      have hle : δ ≤ (1 / ((kn n : ℝ) + 801)) * Real.exp (α * n) := hδle n hn
      have hscale : δ * Real.exp (-(α * (n : ℝ))) ≤ 1 / ((kn n : ℝ) + 801) := by
        have h2 : δ * Real.exp (-(α * (n : ℝ))) ≤
            ((1 / ((kn n : ℝ) + 801)) * Real.exp (α * n)) * Real.exp (-(α * (n : ℝ))) :=
          mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
        have h3 : Real.exp (α * n) * Real.exp (-(α * (n : ℝ))) = 1 := by
          rw [← Real.exp_add]
          ring_nf
          exact Real.exp_zero
        calc δ * Real.exp (-(α * (n : ℝ)))
            ≤ ((1 / ((kn n : ℝ) + 801)) * Real.exp (α * n)) *
                Real.exp (-(α * (n : ℝ))) := h2
          _ = 1 / ((kn n : ℝ) + 801) := by rw [mul_assoc, h3, mul_one]
      exact fun hc' => hkn n (Crosses_mono hscale hc')
    · -- late times
      have hnm : max N₀ n₀ ≤ n := by omega
      have hN0n : N₀ ≤ n := le_trans (le_max_left _ _) hnm
      have hn0n : n₀ ≤ n := le_trans (le_max_right _ _) hnm
      have hnotT : a^[n] x ∉ T n := fun hc' => hN₀ n hN0n hc'
      have hnotN : a^[n] x ∉ Nbd P (500 * Real.exp (-(α * (n : ℝ)))) :=
        fun hc' => hnotT (hTsub n hc')
      have hexp : Real.exp (-(α * (n : ℝ))) ≤ 1 / 800 := hn₀ n hn0n
      have hexppos : 0 < Real.exp (-(α * (n : ℝ))) := Real.exp_pos _
      have hscale : δ * Real.exp (-(α * (n : ℝ))) ≤ Real.exp (-(α * (n : ℝ))) := by
        nlinarith [Real.exp_pos (-(α * (n : ℝ)))]
      exact fun hc' => hnotN (crossing_mem hexppos hexp (Crosses_mono hscale hc'))
  intro n
  rw [← iterate_smul_eq]
  exact hfine n

end Work.EKLC6Core

end
