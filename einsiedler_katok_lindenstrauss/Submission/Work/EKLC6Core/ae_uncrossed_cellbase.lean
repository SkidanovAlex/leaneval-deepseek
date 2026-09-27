import Mathlib
import Submission.Work.EKLC6Core.PlaqueCellDefs
import Submission.Work.EKLC6Core.ae_uncrossed_cellsys

/-!
# `Work.EKLC6Core.ae_uncrossed_cellbase` — the raw cell family is uncrossed at the geometric scale

For an `aDiag t`-invariant probability `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, an exponent vector `t`, and a
countable family `Q` of cells whose union of frontiers is thin in the sense

`μ (⋃ k, VThickX η (frontier (Q k))) ≤ C η ^ θ`  (`C ≥ 0`, `θ > 0`),

for `μ`-a.e. `x` there is `N` such that for every `n ≥ N` and every `k` with
`aDiag t ^ n • x ∈ Q k`, every `v ∈ V (C' rate ^ n)` keeps `aDiag t ^ n • x` inside `Q k`.

Compared with `Work.EKLC6Core.ae_uncrossed_cellsys` (which is stated for a `CellSys`, i.e. for a
cell family packaged together with its thinness constants and with the unused goodness field
`hgood`), the statement here only needs the raw cell data `Q` together with the thinness
hypothesis, which is precisely what a `CellBase` provides (`hthin` is a *hypothesis* here, and no
injectivity/goodness of the centres is used at all).  Indeed the Borel–Cantelli tracking argument
of `ae_ball_in_atom` uses nothing but `Q` and `hthin`, so we prove the general raw version
`ae_uncrossed_of_thin_frontier` and deduce the requested statement from it.

## Proof of the raw version

* Beyond a time `n₀` the crossing scale `C' rate ^ n` is `≤ 1/800`, where `crossing_mem` applies:
  if `aDiag t ^ n • x` is crossed by the single cell `Q k` at that scale, then it lies in
  `VThickX (500 (C' rate ^ n)) (frontier (Q k)) ⊆ ⋃ k, VThickX (500 (C' rate ^ n)) (frontier (Q k))`.
* That set is thin: its mass is at most
  `C (500 (C' rate ^ n)) ^ θ = (C (500 C') ^ θ) (rate ^ θ) ^ n`, a geometric quantity summable in
  `n` because `rate ^ θ < 1`.
* Taking measurable supersets `T n` of those thickened unions and applying the geometric
  Borel–Cantelli lemma along the `aDiag t`-orbit (which preserves `μ`) gives a.e. `x` a time `N`
  after which the orbit never enters `T n`.  For `n ≥ N` no `v ∈ V (C' rate ^ n)` can move
  `aDiag t ^ n • x` out of the cell it lies in.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLC6Core

open Work.EKLContract

/-- **Uncrossed raw cell family.**  If the `η`-collars of the union of the frontiers of a
countable family `Q` of subsets of `X₃` have mass `≤ C η ^ θ` with `C ≥ 0`, `θ > 0`, then along
the `aDiag t`-orbit of `μ`-a.e. `x` the orbit points stay `C' rate ^ n`-deep inside whichever
member of `Q` they lie in. -/
theorem ae_uncrossed_of_thin_frontier {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (Q : ℕ → Set Work.EKLContract.X3) (C θ : ℝ) (hC : 0 ≤ C) (hθ : 0 < θ)
    (hthin : ∀ η : ℝ, 0 < η →
      μ (⋃ k, Work.EKLC6Core.VThickX η (frontier (Q k)))
        ≤ ENNReal.ofReal (C * η ^ θ))
    (rate : ℝ) (hrate0 : 0 < rate) (hrate1 : rate < 1) (C' : ℝ) (hC' : 0 < C') :
    ∀ᵐ x ∂μ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℕ,
      ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x ∈ Q k →
      ∀ v : Work.EKLContract.SL3, v ∈ Work.EKLContract.V (C' * rate ^ n) →
        v • (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x) ∈ Q k := by
  classical
  -- the ratio at which the geometric Borel–Cantelli argument runs
  have hrnn : 0 ≤ rate ^ θ := Real.rpow_nonneg hrate0.le θ
  have hrlt : rate ^ θ < 1 := Real.rpow_lt_one hrate0.le hrate1 hθ
  have hKnn : 0 ≤ C * (500 * C') ^ θ :=
    mul_nonneg hC (Real.rpow_nonneg (by positivity) θ)
  -- thinness in geometric form
  have hpow : ∀ n : ℕ, (500 * (C' * rate ^ n)) ^ θ = (500 * C') ^ θ * (rate ^ θ) ^ n := by
    intro n
    rw [show 500 * (C' * rate ^ n) = (500 * C') * rate ^ n by ring,
      Real.mul_rpow (show (0 : ℝ) ≤ 500 * C' by positivity)
        (show (0 : ℝ) ≤ rate ^ n by positivity)]
    congr 1
    rw [← Real.rpow_natCast rate n, ← Real.rpow_mul hrate0.le (n : ℝ) θ,
      show (n : ℝ) * θ = θ * (n : ℝ) by ring, Real.rpow_mul hrate0.le θ (n : ℝ),
      Real.rpow_natCast]
  -- beyond some time the crossing scale is in the range where `crossing_mem` applies
  obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℕ, ∀ n ≥ n₀, C' * rate ^ n ≤ 1 / 800 := by
    have htend : Tendsto (fun n : ℕ => rate ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hrate0.le hrate1
    have htend2 : Tendsto (fun n : ℕ => C' * rate ^ n) atTop (𝓝 (C' * 0)) :=
      htend.const_mul C'
    rw [mul_zero] at htend2
    have hev : ∀ᶠ n : ℕ in atTop, C' * rate ^ n < 1 / 800 :=
      htend2.eventually (isOpen_Iio.mem_nhds (by norm_num))
    obtain ⟨n₁, hn₁⟩ := Filter.eventually_atTop.mp hev
    exact ⟨n₁, fun n hn => le_of_lt (hn₁ n hn)⟩
  -- measurable hulls of the thickened boundaries
  choose U hUsub hUmeas hUμ using fun n : ℕ =>
    MeasureTheory.exists_measurable_superset μ
      (⋃ k, VThickX (500 * (C' * rate ^ n)) (frontier (Q k)))
  set T : ℕ → Set X3 := fun n => if n₀ ≤ n then U n else ∅ with hT
  have hTmeas : ∀ n, MeasurableSet (T n) := by
    intro n
    rw [hT]
    by_cases h : n₀ ≤ n <;> simp [h, hUmeas n]
  have hTsub : ∀ n, n₀ ≤ n →
      (⋃ k, VThickX (500 * (C' * rate ^ n)) (frontier (Q k))) ⊆ T n := by
    intro n hn
    rw [hT]
    simp only [if_pos hn]
    exact hUsub n
  have hTbound : ∀ n : ℕ,
      μ (T n) ≤ ENNReal.ofReal ((C * (500 * C') ^ θ) * (rate ^ θ) ^ n) := by
    intro n
    rw [hT]
    dsimp only
    split_ifs with hn
    · rw [hUμ n]
      refine le_trans (hthin (500 * (C' * rate ^ n)) (by positivity))
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
  have hτpos : 0 < C' * rate ^ n := by positivity
  have hτle : C' * rate ^ n ≤ 1 / 800 := hn₀ n hn0
  have hcross : Crosses (fun _ : Fin 1 => Q k) (C' * rate ^ n)
      (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x) :=
    ⟨0, v, hv, Or.inl ⟨hk, hcon⟩⟩
  have hmem : ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x ∈
      VThickX (500 * (C' * rate ^ n)) (frontier (Q k)) :=
    crossed_mem_VThickX hτpos hτle hcross
  exact hnotT (hTsub n hn0 (Set.mem_iUnion.mpr ⟨k, hmem⟩))

theorem ae_uncrossed_cellbase {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] (t : Fin 3 → ℝ)
    (hmp : MeasureTheory.MeasurePreserving
      (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) μ μ)
    (S : Work.EKLC6Core.CellBase μ (Work.EKLC6Core.Uminus t))
    (C θ : ℝ) (hC : 0 ≤ C) (hθ : 0 < θ)
    (hthin : ∀ η : ℝ, 0 < η →
      μ (⋃ k, Work.EKLC6Core.VThickX η (frontier (S.Q k))) ≤ ENNReal.ofReal (C * η ^ θ))
    (rate : ℝ) (hrate0 : 0 < rate) (hrate1 : rate < 1) (C' : ℝ) (hC' : 0 < C') :
    ∀ᵐ x ∂μ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℕ,
      ((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x ∈ S.Q k →
      ∀ v : Work.EKLContract.SL3, v ∈ Work.EKLContract.V (C' * rate ^ n) →
        v • (((fun y : Work.EKLContract.X3 => Work.EKLContract.aDiag t • y)^[n]) x) ∈ S.Q k := by
  exact ae_uncrossed_of_thin_frontier (μ := μ) t hmp S.Q C θ hC hθ hthin rate hrate0 hrate1 C' hC'

end Work.EKLC6Core

end
