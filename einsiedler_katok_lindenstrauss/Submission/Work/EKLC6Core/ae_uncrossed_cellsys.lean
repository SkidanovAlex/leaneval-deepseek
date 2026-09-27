import Mathlib
import Submission.Work.EKLC6Core.CellSysDefs
import Submission.Work.EKLC6Core.ae_ball_in_atom
import Submission.Work.EKLC6Core.measure_iInter_iUnion_exp_eq_zero

/-!
# `Work.EKLC6Core.ae_uncrossed_cellsys` — the cell system is uncrossed at the geometric scale

For an `A`-invariant probability `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, an exponent vector `t`, a
`CellSys` `S` (a countable family `Q` of pairwise disjoint small open cells covering a conull
set, whose thin-boundary constants give
`μ (⋃ k, VThickX η (frontier (Q k))) ≤ S.C · η ^ S.θ` with `S.θ > 0`), and any geometric rate
`rate ∈ (0,1)`: for `μ`-a.e. `x` there is `N` such that for every `n ≥ N` and every `k` with
`aDiag t ^ n • x ∈ Q k`, every `v ∈ V (C · rate ^ n)` keeps `aDiag t ^ n • x` inside `Q k`.

This is the "uncrossed cell system" statement: the cells of `S` are uncrossed at the geometric
scale `C · rate ^ n` along the orbit of a.e. point.

## Proof

The argument is the Borel–Cantelli tracking argument of `ae_not_crosses`, adapted to an infinite
family of cells.

* If `aDiag t ^ n • x` is crossed at scale `τ = C · rate ^ n ≤ 1/800` by the single cell `Q k`
  (i.e. some `v ∈ V τ` moves it out of `Q k`), then by `crossing_mem` it lies in
  `VThickX (500 τ) (frontier (Q k))`, hence in `⋃ k, VThickX (500 τ) (frontier (Q k))`, whose mass
  is at most `S.C · (500 τ) ^ S.θ = (S.C · (500 C) ^ S.θ) · (rate ^ S.θ) ^ n` — a geometric
  quantity, summable in `n` since `rate ^ S.θ < 1`.
* Taking measurable supersets `T n` of those thickened boundaries and applying the geometric
  Borel–Cantelli lemma (`geometric_borel_cantelli`) along the `aDiag t`-orbit (which preserves
  `μ`) yields a.e. `x` a time `N` after which the orbit never enters `T n`.
* For `n ≥ N` the scale is in the small range where `crossing_mem` applies, so no `v ∈ V τ` can
  move `aDiag t ^ n • x` out of the cell it sits in.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **Geometric Borel–Cantelli.**  If the measures of a sequence of sets are bounded by
`ofReal (c * r ^ n)` with `r < 1`, then the limsup (`⋂ N ⋃ n ≥ N`) is null. -/
theorem geometric_borel_cantelli {α : Type*} [MeasurableSpace α] (μ : MeasureTheory.Measure α)
    (A : ℕ → Set α) {c r : ℝ} (hc : 0 ≤ c) (hr0 : 0 ≤ r) (hr1 : r < 1)
    (h : ∀ n : ℕ, μ (A n) ≤ ENNReal.ofReal (c * r ^ n)) :
    μ (⋂ N : ℕ, ⋃ n ≥ N, A n) = 0 := by
  have hsumm : Summable (fun n : ℕ => c * r ^ n) :=
    (summable_geometric_of_lt_one hr0 hr1).mul_left c
  have hnn : ∀ n : ℕ, 0 ≤ c * r ^ n := fun n => mul_nonneg hc (pow_nonneg hr0 n)
  have hfin : ∑' n : ℕ, ENNReal.ofReal (c * r ^ n) < ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn hsumm]
    exact ENNReal.ofReal_lt_top
  have hne : ∑' n : ℕ, μ (A n) ≠ ∞ :=
    ne_top_of_le_ne_top (ne_of_lt hfin) (ENNReal.tsum_le_tsum h)
  have hlim : limsup A atTop = ⋂ N : ℕ, ⋃ n ≥ N, A n := by
    rw [Filter.limsup_eq_iInf_iSup_of_nat]
    rfl
  rw [← hlim]
  exact MeasureTheory.measure_limsup_atTop_eq_zero hne

/-- Crossing a single cell `s` at a small scale `τ` forces the crossed point into the
`(500 τ)`-thickened boundary of `s`.  This is `crossing_mem` applied to the one-element family
`fun _ : Fin 1 => s`. -/
theorem crossed_mem_VThickX {s : Set X3} {τ : ℝ} (hτ : 0 < τ) (hτle : τ ≤ 1 / 800) {y : X3}
    (hy : Crosses (fun _ : Fin 1 => s) τ y) : y ∈ VThickX (500 * τ) (frontier s) := by
  have h := crossing_mem (P := fun _ : Fin 1 => s) hτ hτle hy
  rw [Nbd] at h
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h
  simpa [VThickX] using hi

theorem ae_uncrossed_cellsys {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (S : Work.EKLC6Core.CellSys μ (Work.EKLC6Core.Uminus t))
    (rate : ℝ) (hrate0 : 0 < rate) (hrate1 : rate < 1) (C : ℝ) (hC : 0 < C) :
    ∀ᵐ x ∂μ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℕ,
      ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x ∈ S.Q k →
      ∀ v : Work.EKLContract.SL3, v ∈ Work.EKLContract.V (C * rate ^ n) →
        v • (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x) ∈ S.Q k := by
  classical
  -- the ratio at which the geometric Borel–Cantelli argument runs
  have hrnn : 0 ≤ rate ^ S.θ := Real.rpow_nonneg hrate0.le S.θ
  have hrlt : rate ^ S.θ < 1 := Real.rpow_lt_one hrate0.le hrate1 S.hθ0
  have hKnn : 0 ≤ S.C * (500 * C) ^ S.θ :=
    mul_nonneg S.hC0 (Real.rpow_nonneg (by positivity) S.θ)
  -- combined thinness bound in geometric form
  have hpow : ∀ n : ℕ, (500 * (C * rate ^ n)) ^ S.θ = (500 * C) ^ S.θ * (rate ^ S.θ) ^ n := by
    intro n
    rw [show 500 * (C * rate ^ n) = (500 * C) * rate ^ n by ring,
      Real.mul_rpow (show (0 : ℝ) ≤ 500 * C by positivity)
        (show (0 : ℝ) ≤ rate ^ n by positivity)]
    congr 1
    rw [← Real.rpow_natCast rate n, ← Real.rpow_mul hrate0.le (n : ℝ) S.θ,
      show (n : ℝ) * S.θ = S.θ * (n : ℝ) by ring, Real.rpow_mul hrate0.le S.θ (n : ℝ),
      Real.rpow_natCast]
  -- beyond some time the crossing scale is in the range where `crossing_mem` applies
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ∀ n ≥ n₀, C * rate ^ n ≤ 1 / 800 := by
    have htend : Tendsto (fun n : ℕ => rate ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hrate0.le hrate1
    have htend2 : Tendsto (fun n : ℕ => C * rate ^ n) atTop (𝓝 (C * 0)) :=
      htend.const_mul C
    rw [mul_zero] at htend2
    have hev : ∀ᶠ n : ℕ in atTop, C * rate ^ n < 1 / 800 :=
      htend2.eventually (isOpen_Iio.mem_nhds (by norm_num))
    obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.mp hev
    exact ⟨n₁, fun n hn => le_of_lt (hn₁ n hn)⟩
  -- measurable hulls of the thickened boundaries
  choose U hUsub hUmeas hUμ using fun n : ℕ =>
    MeasureTheory.exists_measurable_superset μ
      (⋃ k, VThickX (500 * (C * rate ^ n)) (frontier (S.Q k)))
  set T : ℕ → Set X3 := fun n => if n₀ ≤ n then U n else ∅ with hT
  have hTmeas : ∀ n, MeasurableSet (T n) := by
    intro n
    rw [hT]
    by_cases h : n₀ ≤ n <;> simp [h, hUmeas n]
  have hTsub : ∀ n, n₀ ≤ n →
      (⋃ k, VThickX (500 * (C * rate ^ n)) (frontier (S.Q k))) ⊆ T n := by
    intro n hn
    rw [hT]
    simp only [if_pos hn]
    exact hUsub n
  have hTbound : ∀ n : ℕ,
      μ (T n) ≤ ENNReal.ofReal ((S.C * (500 * C) ^ S.θ) * (rate ^ S.θ) ^ n) := by
    intro n
    rw [hT]
    dsimp only
    split_ifs with hn
    · rw [hUμ n]
      refine le_trans (S.hthin (500 * (C * rate ^ n)) (by positivity))
        (ENNReal.ofReal_le_ofReal ?_)
      rw [hpow n]
      exact le_of_eq (by ring)
    · simp
  -- geometric Borel–Cantelli along the orbit
  have hBC : μ (⋂ N' : ℕ, ⋃ n ≥ N',
      (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) ⁻¹' T n)) = 0 := by
    refine geometric_borel_cantelli μ
      (fun n => ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) ⁻¹' T n)
      hKnn hrnn hrlt ?_
    intro n
    rw [(hmp.iterate n).measure_preimage (hTmeas n).nullMeasurableSet]
    exact hTbound n
  have hBCae : ∀ᵐ x ∂μ, ∃ N' : ℕ, ∀ n ≥ N',
      x ∉ ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) ⁻¹' T n := by
    rw [MeasureTheory.ae_iff]
    have hset : {x : Work.EKLContract.X3 | ¬ ∃ N' : ℕ, ∀ n ≥ N',
          x ∉ ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) ⁻¹' T n}
        = ⋂ N' : ℕ, ⋃ n ≥ N',
            (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) ⁻¹' T n) := by
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
  -- assembly
  filter_upwards [hBCae] with x hxBC
  obtain ⟨N', hN'⟩ := hxBC
  refine ⟨max N' n₀, ?_⟩
  intro n hn k hk v hv
  have hn0 : n₀ ≤ n := le_trans (le_max_right _ _) hn
  have hN'n : N' ≤ n := le_trans (le_max_left _ _) hn
  have hnotT : ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x ∉ T n := by
    intro hmem
    exact hN' n hN'n hmem
  by_contra hcon
  have hτpos : 0 < C * rate ^ n := by positivity
  have hτle : C * rate ^ n ≤ 1 / 800 := hn₀ n hn0
  have hcross : Crosses (fun _ : Fin 1 => S.Q k) (C * rate ^ n)
      (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x) :=
    ⟨0, v, hv, Or.inl ⟨hk, hcon⟩⟩
  have hmem : ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x ∈
      VThickX (500 * (C * rate ^ n)) (frontier (S.Q k)) :=
    crossed_mem_VThickX hτpos hτle hcross
  exact hnotT (hTsub n hn0 (Set.mem_iUnion.mpr ⟨k, hmem⟩))

end Work.EKLC6Core

end
