/-
# The off-band part of the mixed-range §6 comparison, at bounded height

Target: `Work.Analysis.LoMixedPorts.offBandBoundedHeight`.

On the guard but *outside* the band the §6 model-approximation error
`mainPartTuple - loMixedTuple` of the mixed range `(0,l₂)` is only `O(1)` per scale, and the
off-band condition `¬ loBandCond` bounds the scale `N = ⌊a n⌋` from above as soon as the height
`lcL 0 l₂ k₁ k₂ = max (max 0 l₂) (max k₁ k₂)` is bounded by a constant `B`:

`loBandCond ρ P l₂ k₁ k₂ N` is `max k₁ k₂ + 1 + 2 · loMixedU ρ d l₂ k₁ k₂ ≤ Log N`, and with
`l₂, k₁, k₂ ≤ B` the window `loMixedU` is bounded by `U = loMixedU ρ d B B B`, so the failure of
the band condition gives `Log N < B + 1 + 2U`, hence `N ≤ 2^{B+1+2U}`.  Thus only finitely many
lacunary scales can contribute, and the crude single-scale `ℓ² × ℓ² → ℓ¹` bounds
(`Work.KMTAreas.A7.OffBandVarpPieceLp`, `Work.KMTAreas.A7.OffBandLoMixedOpHolds`, both at
`p₁ = p₂ = 2`) plus the spike decomposition of the variational norm
(`eLpNorm_variationalNorm_le_sum`) give the estimate, with the constant absorbing the number of
scales `≈ nBound Λ (B+1+2U)`.

This is the `(p₁,p₂) = (2,2)` / bounded-height specialisation of the off-band estimate; unlike
`Work.KMTAreas.A7.LoMixedOffBandHolds` it needs neither the deep input `AreaA1` nor the smallness
assumption `ρ ≤ 1/(4C₀)` — the bound on the height `lcL` replaces the latter.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.OffBandVarpPieceLp
import Submission.Work.KMTAreas.A7.OffBandLoMixedOpHolds

namespace Work.Analysis.LoMixedPorts

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTContract Work.Analysis.EndVar Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier
open Work.KMTAreas.A7

/-! ## The auxiliary scale is monotone, and the window is bounded by the height bound -/

/-- `uScale ρ ·` is monotone in its second argument (reproved here, so that the import closure
stays light: the version in `A7/goodRegime.lean` sits on the whole A6 pipeline). -/
private lemma uScale_monoAux {ρ : ℝ} (hρ : 0 ≤ ρ) {L B : ℕ} (hLB : L ≤ B) :
    Work.KMTAreas.A7.uScale ρ L ≤ Work.KMTAreas.A7.uScale ρ B := by
  have h1 : (2 : ℝ) ^ (2 * ρ * (L : ℝ)) ≤ (2 : ℝ) ^ (2 * ρ * (B : ℝ)) := by
    rw [Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)]
    have hL' : (L : ℝ) ≤ (B : ℝ) := by exact_mod_cast hLB
    nlinarith
  have h2 : ⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ ≤ ⌊(2 : ℝ) ^ (2 * ρ * (B : ℝ))⌋ := Int.floor_mono h1
  have h3 : Work.KMTAreas.A7.uScale ρ L = (⌊(2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋).toNat := by
    simp [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount]
  have h4 : Work.KMTAreas.A7.uScale ρ B = (⌊(2 : ℝ) ^ (2 * ρ * (B : ℝ))⌋).toNat := by
    simp [Work.KMTAreas.A7.uScale, Work.Analysis.EndVar.scaleCount]
  rw [h3, h4]
  exact Int.toNat_le_toNat h2

/-- The repaired window `loMixedU ρ d l₂ k₁ k₂` is bounded by its value at `(B,B,B)` whenever
`l₂, k₁, k₂ ≤ B`. -/
private lemma loMixedU_le_of_le (ρ : ℝ) (hρ : 0 ≤ ρ) (d B l₂ k₁ k₂ : ℕ)
    (hl₂ : l₂ ≤ B) (hk₁ : k₁ ≤ B) (hk₂ : k₂ ≤ B) :
    Work.KMTAreas.A7.loMixedU ρ d l₂ k₁ k₂ ≤ Work.KMTAreas.A7.loMixedU ρ d B B B := by
  have hBB2 : B ≤ max (max 0 B) (max B B) :=
    le_trans (le_max_right 0 B) (le_max_left _ _)
  have hmax : max (max 0 l₂) (max k₁ k₂) ≤ max (max 0 B) (max B B) :=
    max_le (max_le (Nat.zero_le _) (le_trans hl₂ hBB2))
      (max_le (le_trans hk₁ hBB2) (le_trans hk₂ hBB2))
  have h1 : Work.KMTAreas.A7.uScale ρ (max (max 0 l₂) (max k₁ k₂))
      ≤ Work.KMTAreas.A7.uScale ρ (max (max 0 B) (max B B)) := uScale_monoAux hρ hmax
  have h2 : d * l₂ + 3 ≤ d * B + 3 := Nat.add_le_add_right (Nat.mul_le_mul_left d hl₂) 3
  simp only [Work.KMTAreas.A7.loMixedU]
  exact max_le (le_trans h1 (le_max_left _ _)) (le_trans h2 (le_max_right _ _))

/-! ## The off-band regime at bounded height -/

/-- **Bounded height forces the off band to live at bounded scale.**  For fixed `ρ ≥ 0` and a bound
`B` on `lcL 0 l₂ k₁ k₂`, the failure of the band condition implies that `l₂, k₁, k₂`, `Log N` and
`N` itself are all bounded by `max 1 (B + 1 + 2·loMixedU ρ d B B B)`. -/
private lemma offBandRegimeAux (P : Polynomial ℤ) (ρ : ℝ) (hρ : 0 ≤ ρ) (B : ℕ) :
    ∃ B' : ℕ, 1 ≤ B' ∧ ∀ l₂ k₁ k₂ N : ℕ,
      Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ ≤ B →
      ¬ Work.KMTAreas.A7.loBandCond ρ P l₂ k₁ k₂ N →
      l₂ ≤ B' ∧ k₁ ≤ B' ∧ k₂ ≤ B' ∧ (Work.Analysis.EndVar.logN N).toNat ≤ B' ∧ N ≤ 2 ^ B' := by
  set U : ℕ := Work.KMTAreas.A7.loMixedU ρ P.natDegree B B B with hU
  refine ⟨max 1 (B + 1 + 2 * U), le_max_left _ _, ?_⟩
  intro l₂ k₁ k₂ N hlc hoff
  have hl₂ : l₂ ≤ B := by
    have h : l₂ ≤ Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ := by
      rw [Work.KMTPlan.A6.lcL]
      exact le_trans (le_max_right 0 l₂) (le_max_left _ _)
    exact le_trans h hlc
  have hk₁ : k₁ ≤ B := by
    have h : k₁ ≤ Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ := by
      rw [Work.KMTPlan.A6.lcL]
      exact le_trans (le_max_left k₁ k₂) (le_max_right _ _)
    exact le_trans h hlc
  have hk₂ : k₂ ≤ B := by
    have h : k₂ ≤ Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ := by
      rw [Work.KMTPlan.A6.lcL]
      exact le_trans (le_max_right k₁ k₂) (le_max_right _ _)
    exact le_trans h hlc
  have hUle : Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂ ≤ U := by
    rw [hU]
    exact loMixedU_le_of_le ρ hρ P.natDegree B l₂ k₁ k₂ hl₂ hk₁ hk₂
  have hloglt : (Work.Analysis.EndVar.logN N).toNat
      < max k₁ k₂ + 1 + 2 * Work.KMTAreas.A7.loMixedU ρ P.natDegree l₂ k₁ k₂ := by
    have h := hoff
    unfold Work.KMTAreas.A7.loBandCond at h
    exact not_le.mp h
  have hlog2 : (Work.Analysis.EndVar.logN N).toNat ≤ B + 2 * U := by omega
  have hNle : N ≤ 2 ^ (B + 1 + 2 * U) := by
    have hlogNeq : (Work.Analysis.EndVar.logN N).toNat = Nat.log 2 (max N 2) := by
      simp [Work.Analysis.EndVar.logN]
    have hpow : N ≤ 2 ^ ((Work.Analysis.EndVar.logN N).toNat + 1) := by
      have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (max N 2)
      rw [← hlogNeq] at h
      exact le_trans (le_max_left N 2) (le_of_lt h)
    exact le_trans hpow (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega))
  have hBB' : B ≤ max 1 (B + 1 + 2 * U) :=
    le_trans (Nat.le_add_right B 1)
      (le_trans (Nat.le_add_right (B + 1) (2 * U)) (le_max_right 1 _))
  refine ⟨le_trans hl₂ hBB', le_trans hk₁ hBB', le_trans hk₂ hBB', by omega, ?_⟩
  exact le_trans hNle (Nat.pow_le_pow_right (by norm_num : 0 < 2) (le_max_right 1 _))

/-! ## The two end-point exponents -/

private lemma two_inv_sum_le_one : (2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹ ≤ 1 := by
  rw [ENNReal.inv_two_add_inv_two]

private lemma two_inv_sum_inv_eq_one : ((2 : ENNReal)⁻¹ + (2 : ENNReal)⁻¹)⁻¹ = 1 := by
  rw [ENNReal.inv_two_add_inv_two, inv_one]

/-! ## Elementary `ℝ≥0∞` arithmetic -/

/-- `4 · (c · Y) = (4c) · Y` for `ofReal` constants. -/
private lemma four_mul_ofReal_mul (c : ℝ) (Y : ENNReal) :
    (4 : ENNReal) * (ENNReal.ofReal c * Y) = ENNReal.ofReal (4 * c) * Y := by
  have h4 : (4 : ENNReal) = ENNReal.ofReal (4 : ℝ) := (ENNReal.ofReal_ofNat 4).symm
  rw [h4, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]

/-- A scalar comparison of `NNReal`-valued constants, transported to `ℝ≥0∞`. -/
private lemma nNReal_mul_le_of_scalar {m : ℝ} {K : NNReal} (hKm : m ≤ (K : ℝ))
    (Y : ENNReal) : ENNReal.ofReal m * Y ≤ (K : ENNReal) * Y := by
  rw [← ENNReal.ofReal_coe_nnreal (p := K)]
  exact mul_le_mul' (ENNReal.ofReal_le_ofReal hKm) le_rfl

/-! ## The target -/

theorem offBandBoundedHeight (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (B : ℕ) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ m, 1 ≤ a m) →
        Work.KMTPlan.A6.lcL 0 l₂ k₁ k₂ ≤ B → (k₁ = 0 ∨ k₂ = 0) → 1 ≤ l₂ →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ =>
              if Work.KMTAreas.A7.loGuard ρ C₀ a 0 l₂ k₁ k₂ n
                ∧ ¬ Work.KMTAreas.A7.loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) then
                Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
                  - Work.KMTAreas.A7.loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x
              else 0)) 1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  classical
  have hr1 : (1 : NNReal) ≤ r := le_trans (by norm_num) (le_of_lt hr)
  have hρnn : (0 : ℝ) ≤ ρ := le_of_lt hρ
  -- the bounded-height regime
  obtain ⟨B', hB'1, hreg⟩ := offBandRegimeAux P ρ hρnn B
  -- the two crude single-scale bounds, at `p₁ = p₂ = 2`
  obtain ⟨Cv, hCvpos, hCv⟩ := OffBandVarpPieceLp P 2 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) two_inv_sum_le_one ρ hρ hρ1 B'
  obtain ⟨Cm, hCmpos, hCm⟩ := OffBandLoMixedOpHolds P hd 2 2 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) two_inv_sum_le_one ρ hρ hρ1 B'
  have hCv' : ∀ (l₂ k₁ k₂ N : ℕ) (f g : ℤ → ℂ), l₂ ≤ B' → k₁ ≤ B' → k₂ ≤ B' →
      (Work.Analysis.EndVar.logN N).toNat ≤ B' →
      MeasureTheory.eLpNorm (fun x : ℤ =>
          Work.Analysis.EndVar.varpPiece (Work.KMTContract.kmtPj ρ) P P.natDegree (N : NNReal)
            f g 0 l₂ k₁ k₂ x) 1 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal Cv *
            (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count *
              MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) := by
    intro l₂ k₁ k₂ N f g h1 h2 h3 h4
    have h := hCv l₂ k₁ k₂ N f g h1 h2 h3 h4
    rwa [two_inv_sum_inv_eq_one] at h
  have hCm' : ∀ (l₂ k₁ k₂ N : ℕ) (f g : ℤ → ℂ), l₂ ≤ B' → k₁ ≤ B' → k₂ ≤ B' → 1 ≤ N →
      N ≤ 2 ^ B' →
      MeasureTheory.eLpNorm (Work.KMTAreas.A7.loMixedOp ρ P N l₂ k₁ k₂ f g) 1
          MeasureTheory.Measure.count
        ≤ ENNReal.ofReal Cm *
            (MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count *
              MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) := by
    intro l₂ k₁ k₂ N f g h1 h2 h3 h4 h5
    have h := hCm l₂ k₁ k₂ N f g h1 h2 h3 h4 h5
    rwa [two_inv_sum_inv_eq_one] at h
  have hc2 : (0 : ℝ) < 2 * (Cv + Cm) := by linarith
  set Kfun : NNReal → NNReal := fun Λ =>
    ⟨max 1 (4 * ((nBound Λ B' + 1 : ℕ) : ℝ) * (2 * (Cv + Cm))),
      le_trans zero_le_one (le_max_left (1 : ℝ) _)⟩ with hKfun
  refine ⟨Kfun, ?_⟩
  intro a Λ l₂ k₁ k₂ f g hΛ ha ha1 hlcL hk h1l₂
  have hKval : (Kfun Λ : ℝ)
      = max 1 (4 * ((nBound Λ B' + 1 : ℕ) : ℝ) * (2 * (Cv + Cm))) := by
    rw [hKfun]
    rfl
  set M : ℕ := nBound Λ B' + 1 with hM
  set A : ENNReal := MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count with hA
  set Bv : ENNReal := MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count with hBv
  set u : ℕ → ℤ → ℂ := fun n x =>
    if loGuard ρ C₀ a 0 l₂ k₁ k₂ n ∧ ¬ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n)) then
      mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x
    else 0 with hu
  change MeasureTheory.eLpNorm (fun x : ℤ => variationalNorm r (fun n : ℕ => u n x))
      1 MeasureTheory.Measure.count ≤
    (Kfun Λ : ENNReal) * A * Bv
  -- the off-band family is supported on finitely many scales
  have hsupp : ∀ n : ℕ, n ∉ Finset.range M → u n = 0 := by
    intro n hn
    have hn' : M ≤ n := by simpa [Finset.mem_range] using hn
    have hgate : ¬ (loGuard ρ C₀ a 0 l₂ k₁ k₂ n
        ∧ ¬ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n))) := by
      rintro ⟨hg, hoff⟩
      have hb := hreg l₂ k₁ k₂ (Nat.floor (a n)) hlcL hoff
      have hgt : 2 ^ B' < Nat.floor (a n) :=
        floor_a_gt hΛ ha ha1 B' (by rw [hM] at hn'; omega)
      have := hb.2.2.2.2
      omega
    funext x
    simp only [hu, if_neg hgate, Pi.zero_apply]
  -- the crude per-scale bound
  have hper : ∀ n ∈ Finset.range M,
      4 * MeasureTheory.eLpNorm (u n) 1 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (8 * (Cv + Cm)) * (A * Bv) := by
    intro n _
    have hsub : MeasureTheory.eLpNorm (u n) 1 MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (2 * (Cv + Cm)) * (A * Bv) := by
      by_cases hg : loGuard ρ C₀ a 0 l₂ k₁ k₂ n
          ∧ ¬ loBandCond ρ P l₂ k₁ k₂ (Nat.floor (a n))
      · have hguard := hg.1
        have hoff := hg.2
        have hb := hreg l₂ k₁ k₂ (Nat.floor (a n)) hlcL hoff
        obtain ⟨hl₂B, hk₁B, hk₂B, hlogB, hNB⟩ := hb
        have hb1 := hCv' l₂ k₁ k₂ (Nat.floor (a n)) f g hl₂B hk₁B hk₂B hlogB
        have hN1 : 1 ≤ Nat.floor (a n) := Nat.le_floor (by simpa using ha1 n)
        have hb2 := hCm' l₂ k₁ k₂ (Nat.floor (a n)) f g hl₂B hk₁B hk₂B hN1 hNB
        have hmain : mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n
            = varpPiece (kmtPj ρ) P P.natDegree (((Nat.floor (a n) : ℕ)) : NNReal)
                f g 0 l₂ k₁ k₂ := by
          funext y
          rw [mainPartTuple_apply, if_pos hguard]
          simp only [varpPiece, AhalfR, Nat.floor_natCast]
        have hmodel : loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n
            = loMixedOp ρ P (Nat.floor (a n)) l₂ k₁ k₂ f g := by
          funext x
          simp only [loMixedTuple, if_pos hguard]
        have hunfold : u n = fun x : ℤ =>
            mainPartTuple ρ P C₀ a f g 0 l₂ k₁ k₂ n x
              - loMixedTuple ρ P C₀ a f g l₂ k₁ k₂ n x := by
          funext x
          simp only [hu, if_pos hg]
        rw [hunfold, hmain, hmodel, hA, hBv]
        refine (eLpNorm_sub_le le_rfl).trans ?_
        refine (add_le_add hb1 hb2).trans ?_
        rw [← add_mul]
        refine mul_le_mul' ?_ le_rfl
        rw [← ENNReal.ofReal_add hCvpos.le hCmpos.le]
        exact ENNReal.ofReal_le_ofReal (by linarith)
      · have hunfold : u n = 0 := by
          funext x
          simp only [hu, if_neg hg, Pi.zero_apply]
        rw [hunfold, hA, hBv]
        simp
    calc 4 * MeasureTheory.eLpNorm (u n) 1 MeasureTheory.Measure.count
        ≤ 4 * (ENNReal.ofReal (2 * (Cv + Cm)) * (A * Bv)) :=
          mul_le_mul' le_rfl hsub
      _ = ENNReal.ofReal (8 * (Cv + Cm)) * (A * Bv) := by
          rw [four_mul_ofReal_mul,
            show (4 : ℝ) * (2 * (Cv + Cm)) = 8 * (Cv + Cm) from by ring]
  -- the `ℓ¹`-of-`L^p` spike bound
  have hsum1 := eLpNorm_variationalNorm_le_sum (μ := Measure.count) (r := r)
    (p := (1 : ENNReal)) hr1 le_rfl (s := Finset.range M) hsupp
    (fun n _ => (measurable_of_countable (u n)).aestronglyMeasurable)
  refine hsum1.trans ?_
  have hsum2 : ∑ n ∈ Finset.range M, 4 * MeasureTheory.eLpNorm (u n) 1 MeasureTheory.Measure.count
      ≤ ∑ _n ∈ Finset.range M, ENNReal.ofReal (8 * (Cv + Cm)) * (A * Bv) :=
    Finset.sum_le_sum (fun n hn => hper n hn)
  refine hsum2.trans ?_
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  -- `M · (8(Cv+Cm)) ≤ K(Λ)`
  have hscalar : ((M : ℕ) : ℝ) * (8 * (Cv + Cm)) ≤ (Kfun Λ : ℝ) := by
    rw [hKval, hM]
    have heq : ((nBound Λ B' + 1 : ℕ) : ℝ) * (8 * (Cv + Cm))
        = 4 * ((nBound Λ B' + 1 : ℕ) : ℝ) * (2 * (Cv + Cm)) := by ring
    rw [heq]
    exact le_max_right _ _
  have hMle : (M : ENNReal) * ENNReal.ofReal (8 * (Cv + Cm)) ≤ (Kfun Λ : ENNReal) := by
    rw [← ENNReal.ofReal_natCast M, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ (M : ℝ))]
    simpa using nNReal_mul_le_of_scalar hscalar (1 : ENNReal)
  -- reassociate and conclude
  have hstep : (M : ENNReal) * (ENNReal.ofReal (8 * (Cv + Cm)) * (A * Bv))
      = ((M : ENNReal) * ENNReal.ofReal (8 * (Cv + Cm))) * (A * Bv) := (mul_assoc _ _ _).symm
  rw [hstep]
  refine (mul_le_mul' hMle le_rfl).trans ?_
  exact le_of_eq (mul_assoc _ _ _).symm

end

end Work.Analysis.LoMixedPorts
