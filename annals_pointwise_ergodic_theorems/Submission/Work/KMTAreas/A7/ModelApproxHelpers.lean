/-
# The lacunary summability bookkeeping for `ModelApprox`

The pointwise model approximation of §6 gives, at each lacunary scale `N = ⌊a n⌋`, an error
`≤ C(Λ) · w(L) · N⁻¹ · ‖f‖ ‖g‖`; the passage to the variational norm is by the `ℓ¹`-bound
`V^r(u) ≤ ∑_n 4‖u n‖` (`Work.KMTAreas.A7.VarNormTsumLp`), and the resulting sum
`∑_n N_n⁻¹` is small because the index set `I^{l,k₁,k₂}` forces `N ≥ 2^{2^{L/C₀}}`
(`invFloorSum_le`) while the lacunary scales grow geometrically.  This module records the
elementary estimates of that summation.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.ModelApproxAux

set_option autoImplicit false

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems
open Submission.PointwiseErgodicTheorems

/-- `⌊x⌋ ≥ x/2` for `x ≥ 1`. -/
lemma floor_ge_half {x : NNReal} (h : 1 ≤ x) : (x : ℝ) / 2 ≤ ((Nat.floor x : ℕ) : ℝ) := by
  rcases lt_or_ge (2:ℝ) (x : ℝ) with h2 | h2
  · have h1 : (x : ℝ) < ((Nat.floor x : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
    linarith
  · have hpos : 0 < Nat.floor x := (Nat.floor_pos (R := ℝ)).mpr h
    have h1 : (1 : ℝ) ≤ ((Nat.floor x : ℕ) : ℝ) := by exact_mod_cast hpos
    linarith

/-- The termwise decay of the reciprocal floors along a `Λ`-lacunary sequence:
`⌊a n⌋⁻¹ ≤ 2 Λ^{-n}`. -/
lemma inv_floor_le (Λ : NNReal) (hΛ : 1 < Λ) (a : ℕ → NNReal)
    (ha : Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) (n : ℕ) :
    (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ ≤ 2 * ((Λ : ℝ)⁻¹) ^ n := by
  have hpow : (Λ : ℝ) ^ n ≤ (a n : ℝ) := by
    exact_mod_cast Work.Analysis.EndVar.pow_le_of_lacunary hΛ ha ha1 n
  have hpowpos : (0 : ℝ) < (Λ : ℝ) ^ n := by
    have h1 : (0 : ℝ) < (Λ : ℝ) := by positivity
    positivity
  have han1 : (1 : ℝ) ≤ (a n : ℝ) := by exact_mod_cast ha1 n
  have hfl := floor_ge_half (x := a n) (ha1 n)
  have hhalf : (0 : ℝ) < (a n : ℝ) / 2 := by linarith
  have hfpos : (0 : ℝ) < ((Nat.floor (a n) : ℕ) : ℝ) := by
    have hpos : 0 < Nat.floor (a n) := (Nat.floor_pos (R := ℝ)).mpr (ha1 n)
    exact_mod_cast hpos
  calc (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ = 1 / (((Nat.floor (a n) : ℕ)) : ℝ) := (one_div _).symm
    _ ≤ 1 / ((a n : ℝ) / 2) := one_div_le_one_div_of_le hhalf hfl
    _ = 2 / (a n : ℝ) := by rw [one_div_div]
    _ ≤ 2 / (Λ : ℝ) ^ n :=
        div_le_div_of_nonneg_left (by norm_num) hpowpos hpow
    _ = 2 * ((Λ : ℝ)⁻¹) ^ n := by rw [inv_pow]; ring

/-- Summability of the reciprocal floors along a lacunary sequence. -/
lemma summable_invFloor (Λ : NNReal) (hΛ : 1 < Λ) (a : ℕ → NNReal)
    (ha : Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) :
    Summable (fun n : ℕ => (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) := by
  have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hnorm : ‖(Λ : ℝ)⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < (Λ:ℝ)⁻¹)]
    rw [inv_lt_one₀ (by positivity : (0:ℝ) < (Λ:ℝ))]
    linarith
  have hgeom : Summable (fun n : ℕ => 2 * ((Λ : ℝ)⁻¹) ^ n) :=
    Summable.mul_left 2 (summable_geometric_of_norm_lt_one hnorm)
  exact Summable.of_nonneg_of_le (fun n => by positivity) (fun n => inv_floor_le Λ hΛ a ha ha1 n)
    hgeom

/-- The full lacunary sum of the reciprocal floors: `∑_n ⌊a n⌋⁻¹ ≤ 2Λ/(Λ-1)`. -/
lemma tsum_inv_floor_le (Λ : NNReal) (hΛ : 1 < Λ) (a : ℕ → NNReal)
    (ha : Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n) :
    ∑' n : ℕ, (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ ≤ 2 * (Λ : ℝ) / ((Λ : ℝ) - 1) := by
  have hΛR : (1 : ℝ) < (Λ : ℝ) := by exact_mod_cast hΛ
  have hnorm : ‖(Λ : ℝ)⁻¹‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity : (0:ℝ) < (Λ:ℝ)⁻¹)]
    rw [inv_lt_one₀ (by positivity : (0:ℝ) < (Λ:ℝ))]
    linarith
  have hgeom : Summable (fun n : ℕ => 2 * ((Λ : ℝ)⁻¹) ^ n) :=
    Summable.mul_left 2 (summable_geometric_of_norm_lt_one hnorm)
  have hsum := (summable_invFloor Λ hΛ a ha ha1).tsum_le_tsum
    (fun n => inv_floor_le Λ hΛ a ha ha1 n) hgeom
  have hgeo : (∑' n : ℕ, 2 * ((Λ : ℝ)⁻¹) ^ n) = 2 * (1 - (Λ:ℝ)⁻¹)⁻¹ := by
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hnorm]
  rw [hgeo] at hsum
  refine hsum.trans (le_of_eq ?_)
  have hdiv : (1 - (Λ : ℝ)⁻¹)⁻¹ = (Λ : ℝ) / ((Λ : ℝ) - 1) := by
    have hΛ0 : (Λ : ℝ) ≠ 0 := by positivity
    have hΛ1 : (Λ : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  rw [hdiv, mul_div_assoc]

open Work.Analysis.EndVar

set_option maxHeartbeats 2000000

lemma ofReal_ite (c : Prop) [Decidable c] (r : ℝ) :
    ENNReal.ofReal (if c then r else 0) = if c then ENNReal.ofReal r else 0 := by
  by_cases h : c <;> simp [h]

/-- **The summability of the model-approximation error over the lacunary scales.** -/
lemma tsum_ite_floor_le_indexSet (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (Λ : NNReal) (hΛ : 1 < Λ)
    (D : ℝ) (hD : 0 ≤ D)
    (hDbound : ∀ (L : ℕ), 1 ≤ L → ∀ (a : ℕ → NNReal),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      (∑' n : ℕ, (if L ≤ heightScale C₀ (Nat.floor (a n))
        then (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ else 0))
        ≤ D * (2:ℝ) ^ (-((2:ℝ) ^ ((L:ℝ)/(C₀:ℝ))) + 2))
    (L : ℕ) (E : ℝ) (hE : max (2 * (Λ : ℝ) / ((Λ : ℝ) - 1)) D ≤ E)
    (a : ℕ → NNReal) (ha : Lacunary Λ a) (ha1 : ∀ n, 1 ≤ a n)
    (cond : ℕ → Prop) [DecidablePred cond]
    (hcond : ∀ n, cond n → L ≤ heightScale C₀ (Nat.floor (a n))) :
    (∑' n : ℕ, (if cond n then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0))
      ≤ ENNReal.ofReal (E * (2:ℝ) ^ (-((2:ℝ) ^ ((L:ℝ)/(C₀:ℝ))) + 2)) := by
  have hsumm1 : Summable (fun n : ℕ => (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) :=
    summable_invFloor Λ hΛ a ha ha1
  have hle : ∀ n : ℕ,
      (if L ≤ heightScale C₀ (Nat.floor (a n)) then (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ else 0)
        ≤ (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ := by
    intro n; by_cases h : L ≤ heightScale C₀ (Nat.floor (a n)) <;> simp [h]
  have hsumm2 : Summable (fun n : ℕ =>
      if L ≤ heightScale C₀ (Nat.floor (a n)) then (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ else 0) :=
    hsumm1.of_nonneg_of_le (fun n => by split_ifs <;> positivity) hle
  have hA : (∑' n : ℕ, (if cond n then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0))
      ≤ (∑' n : ℕ, (if L ≤ heightScale C₀ (Nat.floor (a n))
          then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0)) :=
    ENNReal.tsum_le_tsum (fun n => by
      by_cases hc : cond n
      · rw [if_pos hc, if_pos (hcond n hc)]
      · rw [if_neg hc]; exact bot_le)
  have hB : (∑' n : ℕ, (if L ≤ heightScale C₀ (Nat.floor (a n))
        then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0))
      ≤ ENNReal.ofReal (E * (2:ℝ) ^ (-((2:ℝ) ^ ((L:ℝ)/(C₀:ℝ))) + 2)) := by
    by_cases hL : L = 0
    · subst hL
      have hsimple : (∑' n : ℕ, (if 0 ≤ heightScale C₀ (Nat.floor (a n))
            then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0))
          = ∑' n : ℕ, ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) :=
        tsum_congr (fun n => by rw [if_pos (Nat.zero_le _)])
      rw [hsimple, (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsumm1).symm]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : (∑' n : ℕ, (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) ≤ 2 * (Λ : ℝ)/((Λ : ℝ) - 1) :=
        tsum_inv_floor_le Λ hΛ a ha ha1
      have h2 : 2 * (Λ : ℝ)/((Λ : ℝ) - 1) ≤ max (2 * (Λ : ℝ)/((Λ : ℝ) - 1)) D :=
        le_max_left (2 * (Λ : ℝ)/((Λ : ℝ) - 1)) D
      have hE0 : (0:ℝ) ≤ E :=
        le_trans (le_trans hD (le_max_right (2 * (Λ : ℝ)/((Λ : ℝ) - 1)) D)) hE
      have h4 : ((2:ℝ) ^ (-((2:ℝ) ^ (((0:ℕ):ℝ)/(C₀:ℝ))) + 2)) = 2 := by
        have h0 : ((2:ℝ) ^ (((0:ℕ):ℝ)/(C₀:ℝ))) = 1 := by simp
        rw [h0]; norm_num
      rw [h4, mul_comm E 2]
      linarith
    · have hL1 : 1 ≤ L := Nat.one_le_iff_ne_zero.mpr hL
      have hcongr : (∑' n : ℕ, (if L ≤ heightScale C₀ (Nat.floor (a n))
            then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0))
          = ∑' n : ℕ, ENNReal.ofReal (if L ≤ heightScale C₀ (Nat.floor (a n))
              then (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ else 0) :=
        tsum_congr (fun n => (ofReal_ite _ _).symm)
      rw [hcongr, (ENNReal.ofReal_tsum_of_nonneg (fun n => by split_ifs <;> positivity) hsumm2).symm]
      refine ENNReal.ofReal_le_ofReal ?_
      refine (hDbound L hL1 a ha ha1).trans ?_
      exact mul_le_mul_of_nonneg_right
        (le_trans (le_max_right (2 * (Λ : ℝ)/((Λ : ℝ) - 1)) D) hE) (by positivity)
  exact hA.trans hB

/-- **`ModelApprox` from its four inputs.** -/
theorem modelApprox_of_inputs (P : Polynomial ℤ) (p₁ p₂ : ENNReal) (hdeg : 2 ≤ P.natDegree)
    (hA1 : Work.KMTContract.AreaA1) (hp₁ : 1 < p₁) (htp₁ : p₁ < ⊤) (hp₂ : 1 < p₂)
    (htp₂ : p₂ < ⊤) (hsum : p₁⁻¹ + p₂⁻¹ ≤ 1)
    (hcore : ModelApproxCoreStatement P p₁ p₂ hdeg hA1 hp₁ htp₁ hp₂ htp₂ hsum)
    (hvar : ∀ {r : NNReal} {p : ENNReal}, 1 ≤ r → 1 ≤ p → ∀ u : ℕ → ℤ → ℂ,
      MeasureTheory.eLpNorm (fun x : ℤ =>
          PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x))
        p MeasureTheory.Measure.count
      ≤ ∑' n : ℕ, 4 * MeasureTheory.eLpNorm (fun x : ℤ => u n x) p MeasureTheory.Measure.count)
    (hinv : ∀ (C₀ : ℕ), 1 ≤ C₀ → ∀ (Λ : NNReal), 1 < Λ → ∃ D : ℝ, 0 ≤ D ∧
      ∀ (L : ℕ), 1 ≤ L → ∀ (a : ℕ → NNReal),
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        (∑' n : ℕ, (if L ≤ heightScale C₀ (Nat.floor (a n))
          then (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ else 0))
          ≤ D * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2))
    (hwt : ∀ (A ρ L D : ℝ) (C₀ : ℕ), 0 ≤ A → 0 < ρ → 1 ≤ C₀ → ρ ≤ 1 / (4 * (C₀ : ℝ)) →
      0 ≤ D → 0 ≤ L →
      (1 + L) ^ A * (2 : ℝ) ^ (A * (2 : ℝ) ^ (ρ * L)) * D
          * (2 : ℝ) ^ (-((2 : ℝ) ^ (L / (C₀ : ℝ))) + 2)
        ≤ (8 * max D 1 * (2 : ℝ) ^ (A * A ^ ((1 : ℝ) / 3) + 4))
          * ((1 + L) ^ (A + 2) * (2 : ℝ) ^ ((A + 2) * ρ * L)))
    : ∀ (C₀ : ℕ) (r : NNReal), 1 ≤ C₀ → (2 : NNReal) < r →
      ∃ c : ℝ, 0 ≤ c ∧ ∃ ρ₀ : ℝ, 0 < ρ₀ ∧
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
          ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
            1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
            MeasureTheory.eLpNorm (fun x : ℤ =>
                PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
                  Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
                    - Work.KMTAreas.A7.modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
              (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
            ≤ (K Λ : ENNReal) * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight c ρ l₁ l₂ k₁ k₂) *
                MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count *
                MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count := by
  classical
  obtain ⟨A, hA, ρc, hρc, hcore'⟩ := hcore
  intro C₀ r hC₀ hr
  have hC₀' : (0 : ℕ) < C₀ := lt_of_lt_of_le Nat.zero_lt_one hC₀
  have h1r : (1 : NNReal) ≤ r := le_trans (by norm_num) hr.le
  have hp : (1 : ENNReal) ≤ (p₁⁻¹ + p₂⁻¹)⁻¹ := ENNReal.one_le_inv.mpr hsum
  refine ⟨A + 2, by linarith, min ρc (1 / (4 * (C₀ : ℝ))), lt_min hρc (by positivity), ?_⟩
  intro ρ hρ hρle
  have hρc' : ρ ≤ ρc := le_trans hρle (min_le_left _ _)
  have hρ4 : ρ ≤ 1 / (4 * (C₀ : ℝ)) := le_trans hρle (min_le_right _ _)
  obtain ⟨C, hC⟩ := hcore' ρ hρ hρc'
  -- the summability constant `D` (from `hinv`) and the relaxed constant `E`
  set D : NNReal → ℝ :=
    fun Λ => if h : 1 < Λ then Classical.choose (hinv C₀ hC₀ Λ h) else 0 with hD
  have hD0 : ∀ Λ : NNReal, 0 ≤ D Λ := by
    intro Λ
    by_cases h : 1 < Λ
    · rw [hD]; simp only [dif_pos h]
      exact (Classical.choose_spec (hinv C₀ hC₀ Λ h)).1
    · rw [hD]; simp [h]
  have hDb : ∀ (Λ : NNReal), 1 < Λ → ∀ (L : ℕ), 1 ≤ L → ∀ (a : ℕ → NNReal),
      PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
      (∑' n : ℕ, (if L ≤ heightScale C₀ (Nat.floor (a n))
        then (((Nat.floor (a n) : ℕ)) : ℝ)⁻¹ else 0))
        ≤ D Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ ((L : ℝ) / (C₀ : ℝ))) + 2) := by
    intro Λ hΛ L hL a ha ha1
    rw [hD]; simp only [dif_pos hΛ]
    exact (Classical.choose_spec (hinv C₀ hC₀ Λ hΛ)).2 L hL a ha ha1
  set E : NNReal → ℝ := fun Λ => max (2 * (Λ : ℝ) / ((Λ : ℝ) - 1)) (D Λ) with hE
  have hE0 : ∀ Λ : NNReal, 0 ≤ E Λ := by
    intro Λ
    have h := hD0 Λ
    rw [hE]
    exact le_trans h (le_max_right (2 * (Λ : ℝ) / ((Λ : ℝ) - 1)) (D Λ))
  have hE1 : ∀ (Λ : NNReal), 1 < Λ → max (2 * (Λ : ℝ) / ((Λ : ℝ) - 1)) (D Λ) ≤ E Λ :=
    fun Λ _ => le_of_eq rfl
  -- the constant of the final bound
  set Kcf : NNReal → ℝ := fun Λ => 8 * max (E Λ) 1 * (2 : ℝ) ^ (A * A ^ ((1 : ℝ) / 3) + 4) with hKcf
  set Kfun : NNReal → NNReal := fun Λ => 4 * C Λ * NNReal.mk (Kcf Λ) (by positivity) with hKfun
  refine ⟨Kfun, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1
  set Kc : ℝ := Kcf Λ with hKc
  -- the family of errors
  set u : ℕ → ℤ → ℂ := fun n x =>
    Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
      - Work.KMTAreas.A7.modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x with hu
  set A₁ : ENNReal := MeasureTheory.eLpNorm f p₁ MeasureTheory.Measure.count with hA₁
  set B₁ : ENNReal := MeasureTheory.eLpNorm g p₂ MeasureTheory.Measure.count with hB₁
  set Xe : ENNReal := (C Λ : ENNReal)
      * ENNReal.ofReal (Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂) * A₁ * B₁ with hXe
  set w : ℝ := Work.KMTAreas.A7.modelWeight A ρ l₁ l₂ k₁ k₂ with hw
  set Lr : ℝ := lmaxR l₁ l₂ k₁ k₂ with hLr
  set S : ℝ := E Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ (Lr / (C₀ : ℝ))) + 2) with hS
  have hLr0 : 0 ≤ Lr := by rw [hLr]; exact lmaxR_nonneg l₁ l₂ k₁ k₂
  have hS0 : 0 ≤ S := by
    rw [hS]
    exact mul_nonneg (hE0 Λ) (by positivity)
  -- the guard of the two tuples, and the fact that the error vanishes off it
  set Gc : ℕ → Prop := fun n =>
      inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n))
      ∧ splitCut ρ (max (max l₁ l₂) (max k₁ k₂)) < Nat.floor (a n)
      ∧ mainRegime ρ k₁ k₂ (Nat.floor (a n)) with hGc
  have hzero : ∀ n : ℕ, ¬ Gc n → u n = 0 := by
    intro n hg
    funext x
    rw [hu]
    simp only [Work.KMTAreas.A7.mainPartTuple, Work.KMTAreas.A7.modelTuple]
    rw [if_neg hg, if_neg hg]
    simp
  have hlhs : MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ =>
          Work.KMTAreas.A7.mainPartTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x
            - Work.KMTAreas.A7.modelTuple ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      = MeasureTheory.eLpNorm (fun x : ℤ =>
        PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => u n x))
        (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count := by
    apply congrArg (fun F => MeasureTheory.eLpNorm F (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count)
    funext x
    apply congrArg (fun G => PointwiseErgodicTheorems.variationalNorm r G)
    funext n
    rw [hu]
  rw [hlhs]
  -- (1) the variational norm is bounded by the `ℓ¹`-sum of the single-scale errors
  refine (hvar h1r hp u).trans ?_
  -- (2) the per-scale bound, in guarded form
  have hper : ∀ n : ℕ, MeasureTheory.eLpNorm (fun x : ℤ => u n x)
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count ≤ Xe * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) := by
    intro n
    have h := hC C₀ a Λ l₁ l₂ k₁ k₂ f g hC₀ hΛ ha ha1 n
    rw [hXe, hw, hA₁, hB₁]
    -- the products agree up to commutativity
    refine (h.trans (le_of_eq ?_))
    ac_rfl
  have hper' : ∀ n : ℕ, MeasureTheory.eLpNorm (fun x : ℤ => u n x)
      (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count
      ≤ if Gc n then Xe * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0 := by
    intro n
    by_cases hg : Gc n
    · rw [if_pos hg]
      refine (hper n).trans (le_of_eq ?_)
      ac_rfl
    · rw [if_neg hg, hzero n hg]
      simp
  -- (3) sum over the scales and pull out the constants
  have hstep3 : (∑' n : ℕ, 4 * MeasureTheory.eLpNorm (fun x : ℤ => u n x)
        (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count)
      ≤ 4 * Xe * (∑' n : ℕ, (if Gc n then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0)) := by
    calc (∑' n : ℕ, 4 * MeasureTheory.eLpNorm (fun x : ℤ => u n x)
          (p₁⁻¹ + p₂⁻¹)⁻¹ MeasureTheory.Measure.count)
        ≤ ∑' n : ℕ, 4 * (if Gc n then Xe * ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0) :=
          ENNReal.tsum_le_tsum (fun n => mul_le_mul' le_rfl (hper' n))
      _ = ∑' n : ℕ, (4 * Xe) * (if Gc n then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0) := by
          refine tsum_congr (fun n => ?_)
          by_cases hg : Gc n
          · rw [if_pos hg, if_pos hg]; ac_rfl
          · rw [if_neg hg, if_neg hg]; simp
      _ = (4 * Xe) * (∑' n : ℕ, (if Gc n then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0)) :=
          ENNReal.tsum_mul_left
      _ = 4 * Xe * (∑' n : ℕ, (if Gc n then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0)) := rfl
  -- (4) the lacunary sum bound
  have hcond : ∀ n : ℕ, Gc n → max (max l₁ l₂) (max k₁ k₂) ≤ heightScale C₀ (Nat.floor (a n)) := by
    intro n hg
    have h1 : inIndexSet C₀ (max (l₁ : ℤ) (l₂ : ℤ)) (k₁ : ℤ) (k₂ : ℤ) (Nat.floor (a n)) := hg.1
    rw [inIndexSet] at h1
    have h2 : max (l₁ : ℤ) (l₂ : ℤ) ≤ ((heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := h1.1
    have h3 : (k₁ : ℤ) ≤ ((heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := h1.2.1
    have h4 : (k₂ : ℤ) ≤ ((heightScale C₀ (Nat.floor (a n)) : ℕ) : ℤ) := h1.2.2
    omega
  have hstep4 : (∑' n : ℕ, (if Gc n then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0))
      ≤ ENNReal.ofReal S := by
    have hexp : ((max (max l₁ l₂) (max k₁ k₂) : ℕ) : ℝ) / (C₀ : ℝ) = Lr / (C₀ : ℝ) := by
      rw [hLr, lmaxR, Work.Analysis.EndVar.lmax]
      have hcast : ((max (max l₁ l₂) (max k₁ k₂) : ℕ) : ℝ) / (C₀ : ℝ)
          = (((max (max (l₁ : ℤ) (l₂ : ℤ)) (max (k₁ : ℤ) (k₂ : ℤ))) : ℤ) : ℝ) / (C₀ : ℝ) := by
        congr 1
        rw [Nat.cast_max, Nat.cast_max]
        push_cast
        rfl
      rw [hcast]
    have hmain := tsum_ite_floor_le_indexSet C₀ hC₀ Λ hΛ (D Λ) (hD0 Λ) (fun L hL a ha ha1 =>
        hDb Λ hΛ L hL a ha ha1) (max (max l₁ l₂) (max k₁ k₂)) (E Λ) (hE1 Λ hΛ) a ha ha1 Gc hcond
    rw [hexp] at hmain
    rw [hS]
    exact hmain
  -- (5) the weight arithmetic
  have hwt_inst := hwt A ρ Lr (E Λ) C₀ hA hρ hC₀ hρ4 (hE0 Λ) hLr0
  have hwt' : w * S ≤ Kc * Work.KMTAreas.A7.lossWeight (A + 2) ρ l₁ l₂ k₁ k₂ := by
    rw [hw, hS, hKc, hKcf, hLr]
    rw [Work.KMTAreas.A7.modelWeight, Work.KMTAreas.A7.lossWeight]
    have h_assoc : (1 + lmaxR l₁ l₂ k₁ k₂) ^ A
          * (2 : ℝ) ^ (A * (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂))
          * (E Λ * (2 : ℝ) ^ (-((2 : ℝ) ^ ((lmaxR l₁ l₂ k₁ k₂) / (C₀ : ℝ))) + 2))
        = ((1 + lmaxR l₁ l₂ k₁ k₂) ^ A
          * (2 : ℝ) ^ (A * (2 : ℝ) ^ (ρ * lmaxR l₁ l₂ k₁ k₂))) * (E Λ)
          * (2 : ℝ) ^ (-((2 : ℝ) ^ ((lmaxR l₁ l₂ k₁ k₂) / (C₀ : ℝ))) + 2) := by ring
    rw [h_assoc]
    exact hwt_inst
  -- (6) assemble
  have hofReal : ENNReal.ofReal w * ENNReal.ofReal S = ENNReal.ofReal (w * S) :=
    (ENNReal.ofReal_mul (modelWeight_nonneg A ρ hA l₁ l₂ k₁ k₂)).symm
  have hbound : ENNReal.ofReal (w * S) ≤ ENNReal.ofReal (Kc * Work.KMTAreas.A7.lossWeight (A + 2) ρ l₁ l₂ k₁ k₂) :=
    ENNReal.ofReal_le_ofReal hwt'
  have hKval : (Kfun Λ : ENNReal) = 4 * (C Λ : ENNReal) * ENNReal.ofReal Kc := by
    rw [hKfun, hKc]
    rw [ENNReal.coe_mul, ENNReal.coe_mul, ENNReal.coe_ofNat,
      (ENNReal.ofReal_coe_nnreal (p := (NNReal.mk (Kcf Λ) (by positivity)))).symm]
    rfl
  refine (hstep3.trans ?_)
  have hsum5 : 4 * Xe * (∑' n : ℕ, (if Gc n then ENNReal.ofReal ((((Nat.floor (a n) : ℕ)) : ℝ)⁻¹) else 0))
      ≤ 4 * Xe * ENNReal.ofReal S := mul_le_mul' le_rfl hstep4
  refine hsum5.trans ?_
  calc 4 * Xe * ENNReal.ofReal S
      = 4 * ((C Λ : ENNReal) * ENNReal.ofReal w * A₁ * B₁) * ENNReal.ofReal S := by rw [hXe, hw]
    _ = 4 * (C Λ : ENNReal) * (ENNReal.ofReal w * ENNReal.ofReal S) * A₁ * B₁ := by ac_rfl
    _ = 4 * (C Λ : ENNReal) * ENNReal.ofReal (w * S) * A₁ * B₁ := by rw [hofReal]
    _ ≤ 4 * (C Λ : ENNReal) * ENNReal.ofReal (Kc * Work.KMTAreas.A7.lossWeight (A + 2) ρ l₁ l₂ k₁ k₂) * A₁ * B₁ :=
        mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hbound) le_rfl) le_rfl
    _ = 4 * (C Λ : ENNReal) * (ENNReal.ofReal Kc * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (A + 2) ρ l₁ l₂ k₁ k₂)) * A₁ * B₁ := by
        rw [ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ Kc)]
    _ = 4 * (C Λ : ENNReal) * ENNReal.ofReal Kc * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (A + 2) ρ l₁ l₂ k₁ k₂) * A₁ * B₁ := by ac_rfl
    _ = (Kfun Λ : ENNReal)
        * ENNReal.ofReal (Work.KMTAreas.A7.lossWeight (A + 2) ρ l₁ l₂ k₁ k₂) * A₁ * B₁ := by
        rw [hKval]

end

end Work.KMTAreas.A7
