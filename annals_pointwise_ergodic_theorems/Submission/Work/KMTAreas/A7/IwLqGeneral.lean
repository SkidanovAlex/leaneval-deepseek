import Mathlib
import Submission.Work.KMTAreas.A7.Split

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-- The frequency circle `ℝ/ℤ` (the same type as `Work.Analysis.IonescuWainger.Circle` and
`Work.Analysis.IWMultiplier.Circle`; the name is disambiguated because both namespaces are open
here). -/
abbrev Freq : Type := AddCircle (1 : ℝ)

noncomputable section

/-! ## Lemma `iw-prop`(i) at an arbitrary exponent

The Ionescu--Wainger multiplier theorem (area `A1` of the contract) gives the `ℓ^q` bound for the
IW projection `T^{≤l}_φ` only at the exponents `q ∈ 2ℕ ∪ (2ℕ)'`.  The paper's Remark `rem:1`(iv)
recovers *every* exponent `1 < q < ∞` by interpolating between two of those, the constant of the
iw-multiplier theorem participating through the continuous multiplier norm `‖T_φ‖_{L^q(ℝ)}`.

This file carries out that interpolation in the form needed by the area-`A7` development: for a
Schwartz symbol `Φ` supported in the arc `ℝ_{≤k}` whose continuous multiplier is bounded on
`L^q(ℝ)`, `1 < q`, by a single constant `M` (for `Φ` and for its conjugate `star ∘ Φ`), the IW
projection is bounded on `ℓ^p(ℤ)` at every `1 < p < ∞` with constant `C ⟨l⟩ M`, `C = C_{ρ,p}`.

The bookkeeping is organised so that the interpolated constant `C` is an explicit function
(`iwConst`) of the even-exponent constants `Ce` of area `A1` and of `p` alone. -/

/-! ## The conjugate of a Schwartz function, and periodisation -/

/-- The complex conjugate `x ↦ star (Φ x)` of a Schwartz function, as a `SchwartzMap`. -/
noncomputable def starSchwartz (Φ : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  SchwartzMap.postcompCLM (𝕜 := ℝ) Complex.conjCLE.toContinuousLinearMap Φ

@[simp] lemma starSchwartz_coe (Φ : SchwartzMap ℝ ℂ) :
    (starSchwartz Φ : ℝ → ℂ) = fun x => star (Φ x) := by
  ext x
  simp [starSchwartz, SchwartzMap.postcompCLM_apply]

lemma starSchwartz_apply (Φ : SchwartzMap ℝ ℂ) (x : ℝ) : starSchwartz Φ x = star (Φ x) :=
  congrFun (starSchwartz_coe Φ) x

lemma starSchwartz_ne_zero {Φ : SchwartzMap ℝ ℂ} {x : ℝ} (h : starSchwartz Φ x ≠ 0) :
    Φ x ≠ 0 := by
  rw [starSchwartz_apply] at h
  intro h0
  exact h (by simp [h0])

/-- Conjugating commutes with periodisation: the conjugate of the periodisation of `φ` is the
periodisation of the conjugate of `φ`. -/
lemma periodize_star (φ : ℝ → ℂ) (ξ : Freq) :
    star (periodize (fun x => star (φ x)) ξ) = periodize φ ξ := by
  simp only [periodize]
  rw [tsum_star]
  exact tsum_congr (fun j => star_star _)

/-- The exponent `ENNReal.ofReal ((2k : ℕ) : ℝ)` is the even natural exponent `2k`. -/
lemma ofReal_two_mul (k : ℕ) : ENNReal.ofReal ((2 * k : ℕ) : ℝ) = ((2 * k : ℕ) : ℝ≥0∞) :=
  ENNReal.ofReal_natCast _

/-! ## Interpolation of the exponent -/

/-- The interpolation exponent attached to the pair `(a,b)` and the point `p`: for `0 < a < b` and
`a ≤ p ≤ b` it satisfies `1/p = (1-θ)/a + θ/b` with `θ ∈ [0,1]`. -/
noncomputable def interpTheta (a b p : ℝ) : ℝ := (a⁻¹ - p⁻¹) / (a⁻¹ - b⁻¹)

/-- **The interpolation exponent, explicitly.**  For `0 < a < b` and `a ≤ p ≤ b`,
`θ = interpTheta a b p` lies in `[0,1]` and `1/p = (1-θ)/a + θ/b`. -/
lemma interpTheta_mem {a b p : ℝ} (ha : 0 < a) (hab : a < b) (hap : a ≤ p) (hpb : p ≤ b) :
    0 ≤ interpTheta a b p ∧ interpTheta a b p ≤ 1 ∧
      p⁻¹ = (1 - interpTheta a b p) * a⁻¹ + interpTheta a b p * b⁻¹ := by
  have hp_pos : 0 < p := lt_of_lt_of_le ha hap
  have hb_pos : 0 < b := lt_trans ha hab
  have hden_pos : 0 < a⁻¹ - b⁻¹ := by
    have h : b⁻¹ < a⁻¹ := by
      rw [inv_lt_inv₀ hb_pos ha]
      exact hab
    linarith
  have hnum_nonneg : 0 ≤ a⁻¹ - p⁻¹ := by
    have h : p⁻¹ ≤ a⁻¹ := by
      rw [inv_le_inv₀ hp_pos ha]
      exact hap
    linarith
  have hnum_le : a⁻¹ - p⁻¹ ≤ a⁻¹ - b⁻¹ := by
    have h : b⁻¹ ≤ p⁻¹ := by
      rw [inv_le_inv₀ hb_pos hp_pos]
      exact hpb
    linarith
  refine ⟨?_, ?_, ?_⟩
  · exact div_nonneg hnum_nonneg hden_pos.le
  · rw [interpTheta, div_le_one hden_pos]
    linarith
  · have hkey : interpTheta a b p * (a⁻¹ - b⁻¹) = a⁻¹ - p⁻¹ := by
      rw [interpTheta]
      exact div_mul_cancel₀ _ hden_pos.ne'
    calc p⁻¹ = a⁻¹ - (a⁻¹ - p⁻¹) := by ring
      _ = a⁻¹ - (interpTheta a b p * (a⁻¹ - b⁻¹)) := by rw [hkey]
      _ = (1 - interpTheta a b p) * a⁻¹ + interpTheta a b p * b⁻¹ := by ring

/-- **The interpolation constant.**  Riesz--Thorin interpolation of two bounds of the shape
`C * a * M` produces again a bound of that shape. -/
lemma rpow_mul_const (C₀ C₁ a M : ℝ≥0) (ha : a ≠ 0) (θ : ℝ) :
    (C₀ * a * M) ^ (1 - θ) * (C₁ * a * M) ^ θ = (C₀ ^ (1 - θ) * C₁ ^ θ) * a * M := by
  by_cases hM : M = 0
  · subst hM
    simp only [mul_zero]
    rcases eq_or_ne θ 0 with hθ | hθ
    · subst hθ
      simp [NNReal.rpow_zero, NNReal.zero_rpow (by norm_num : (1 : ℝ) ≠ 0)]
    · rw [NNReal.zero_rpow hθ, mul_zero]
  · have ha1 : a ^ (1 - θ) * a ^ θ = a := by
      rw [← NNReal.rpow_add ha, show 1 - θ + θ = 1 by ring, NNReal.rpow_one]
    have hM1 : M ^ (1 - θ) * M ^ θ = M := by
      rw [← NNReal.rpow_add hM, show 1 - θ + θ = 1 by ring, NNReal.rpow_one]
    simp only [NNReal.mul_rpow]
    rw [show C₀ ^ (1 - θ) * a ^ (1 - θ) * M ^ (1 - θ) * (C₁ ^ θ * a ^ θ * M ^ θ)
        = (C₀ ^ (1 - θ) * C₁ ^ θ) * (a ^ (1 - θ) * a ^ θ) * (M ^ (1 - θ) * M ^ θ) by ring,
      ha1, hM1]

/-- **One Riesz--Thorin step.**  Two bounds of the shape `C * a * M` at the exponents `q₀, q₁`
interpolate to a bound of the same shape at every intermediate exponent. -/
lemma iwLqBound_of_pair {A : Finset Freq} {Ψ : Freq → ℂ} {p q₀ q₁ : ℝ}
    {C₀ C₁ a M : ℝ≥0} {θ : ℝ}
    (h₀ : IWLqBound A Ψ (ENNReal.ofReal q₀) (C₀ * a * M))
    (h₁ : IWLqBound A Ψ (ENNReal.ofReal q₁) (C₁ * a * M))
    (hq₀ : 1 < q₀) (hq₁ : 1 < q₁) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (hp : 0 < p)
    (heq : p⁻¹ = (1 - θ) * q₀⁻¹ + θ * q₁⁻¹) (ha : a ≠ 0) :
    IWLqBound A Ψ (ENNReal.ofReal p) ((C₀ ^ (1 - θ) * C₁ ^ θ) * a * M) := by
  have h0 : (0 : ℝ) < q₀ := lt_trans zero_lt_one hq₀
  have h1 : (0 : ℝ) < q₁ := lt_trans zero_lt_one hq₁
  have hq₀' : 1 ≤ (ENNReal.ofReal q₀).toReal := by
    rw [ENNReal.toReal_ofReal h0.le]
    exact hq₀.le
  have hq₁' : 1 ≤ (ENNReal.ofReal q₁).toReal := by
    rw [ENNReal.toReal_ofReal h1.le]
    exact hq₁.le
  have heq' : (ENNReal.ofReal p).toReal⁻¹
      = (1 - θ) * (ENNReal.ofReal q₀).toReal⁻¹ + θ * (ENNReal.ofReal q₁).toReal⁻¹ := by
    rw [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal h0.le, ENNReal.toReal_ofReal h1.le]
    exact heq
  refine IWLqBound.mono (IWLqBound_interpolation A Ψ h₀ h₁ hθ0 hθ1 hq₀' hq₁' heq') ?_
  exact le_of_eq (rpow_mul_const C₀ C₁ a M ha θ)

/-! ## The interpolated constant, and the bound at every exponent -/

/-- The constant obtained by interpolating between the even-exponent constants `Ce` at the
exponent `p ≥ 2`: the pair `(4/3, 4)` for `p ≤ 4`, the pair of consecutive even exponents
`(2⌊p/2⌋, 2⌊p/2⌋+2)` for `p > 4`. -/
noncomputable def evenConst (Ce : ℕ → ℝ≥0) (p : ℝ) : ℝ≥0 :=
  if p ≤ 4 then Ce 2 ^ (1 - interpTheta (4 / 3) 4 p) * Ce 2 ^ interpTheta (4 / 3) 4 p
  else
    Ce ⌊p / 2⌋₊ ^ (1 - interpTheta (((2 * ⌊p / 2⌋₊ : ℕ) : ℝ))
          (((2 * (⌊p / 2⌋₊ + 1) : ℕ) : ℝ)) p)
      * Ce (⌊p / 2⌋₊ + 1) ^ (interpTheta (((2 * ⌊p / 2⌋₊ : ℕ) : ℝ))
          (((2 * (⌊p / 2⌋₊ + 1) : ℕ) : ℝ)) p)

/-- The constant at every exponent `p > 1`: `evenConst` at `p` for `p ≥ 2`, and at the dual
exponent `p/(p-1)` for `1 < p < 2` (where the dualisation `IWLqBound_of_dual` does not change the
constant). -/
noncomputable def iwConst (Ce : ℕ → ℝ≥0) (p : ℝ) : ℝ≥0 :=
  if 2 ≤ p then evenConst Ce p else evenConst Ce (p / (p - 1))

lemma evenConst_pos {Ce : ℕ → ℝ≥0} (hCe : ∀ k : ℕ, 2 ≤ k → 0 < Ce k) {p : ℝ} (_hp : 2 ≤ p) :
    0 < evenConst Ce p := by
  rw [evenConst]
  by_cases hp4 : p ≤ 4
  · rw [if_pos hp4]
    exact mul_pos (NNReal.rpow_pos (hCe 2 (by norm_num)))
      (NNReal.rpow_pos (hCe 2 (by norm_num)))
  · rw [if_neg hp4]
    have h4 : 4 < p := lt_of_not_ge hp4
    have hk : 2 ≤ ⌊p / 2⌋₊ :=
      Nat.le_floor (by linarith : (2 : ℝ) ≤ p / 2)
    exact mul_pos (NNReal.rpow_pos (hCe _ hk)) (NNReal.rpow_pos (hCe _ (by omega)))

/-- **From the even exponents to `p ≥ 2`.**  If both a symbol `Ψ` and its conjugate `Ψ'` satisfy
the Ionescu--Wainger `ℓ^{2k}` bound for every `k ≥ 2` with constant `Ce k * a * M`, then `Ψ`
satisfies the `ℓ^p` bound with constant `evenConst Ce p * a * M`. -/
lemma iwLqBound_of_fixed {A : Finset Freq} {Ψ Ψ' : Freq → ℂ} {a M : ℝ≥0} {Ce : ℕ → ℝ≥0}
    (_hCe : ∀ k : ℕ, 2 ≤ k → 0 < Ce k) (hconj : ∀ ξ, star (Ψ' ξ) = Ψ ξ)
    (hunif : ∀ k : ℕ, 2 ≤ k →
      IWLqBound A Ψ (ENNReal.ofReal ((2 * k : ℕ) : ℝ)) (Ce k * a * M) ∧
      IWLqBound A Ψ' (ENNReal.ofReal ((2 * k : ℕ) : ℝ)) (Ce k * a * M))
    (ha : a ≠ 0) {p : ℝ} (hp : 2 ≤ p) :
    IWLqBound A Ψ (ENNReal.ofReal p) (evenConst Ce p * a * M) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  rw [evenConst]
  by_cases hp4 : p ≤ 4
  · rw [if_pos hp4]
    obtain ⟨hθ0, hθ1, hθeq⟩ :=
      interpTheta_mem (a := 4 / 3) (b := 4) (p := p) (by norm_num) (by norm_num)
        (by linarith) hp4
    have hb4 : IWLqBound A Ψ (ENNReal.ofReal (4 : ℝ)) (Ce 2 * a * M) := by
      simpa using (hunif 2 (by norm_num)).1
    have hb4' : IWLqBound A Ψ' (ENNReal.ofReal (4 : ℝ)) (Ce 2 * a * M) := by
      simpa using (hunif 2 (by norm_num)).2
    have hq4 : 1 < (ENNReal.ofReal (4 : ℝ)).toReal := by
      rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    have hdual := IWLqBound_of_dual A Ψ' hb4' hq4
    have hexp43 : (ENNReal.ofReal (4 : ℝ)).toReal / ((ENNReal.ofReal (4 : ℝ)).toReal - 1)
        = 4 / 3 := by
      rw [ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    rw [hexp43, funext hconj] at hdual
    exact iwLqBound_of_pair (q₀ := 4 / 3) (q₁ := 4) (C₀ := Ce 2) (C₁ := Ce 2) hdual hb4
      (by norm_num : (1 : ℝ) < 4 / 3) (by norm_num : (1 : ℝ) < 4) hθ0 hθ1 hp0 hθeq ha
  · rw [if_neg hp4]
    have h4 : 4 < p := lt_of_not_ge hp4
    have hk : 2 ≤ ⌊p / 2⌋₊ :=
      Nat.le_floor (by linarith : (2 : ℝ) ≤ p / 2)
    have hq₀p : ((2 * ⌊p / 2⌋₊ : ℕ) : ℝ) ≤ p := by
      have h := Nat.floor_le (show (0 : ℝ) ≤ p / 2 by linarith)
      push_cast
      linarith
    have hpq₁ : p ≤ ((2 * (⌊p / 2⌋₊ + 1) : ℕ) : ℝ) := by
      have h := Nat.lt_floor_add_one (p / 2)
      push_cast
      linarith
    have hq₀1 : (1 : ℝ) < ((2 * ⌊p / 2⌋₊ : ℕ) : ℝ) := by
      have h : (2 : ℝ) ≤ ((2 * ⌊p / 2⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast (show 2 ≤ 2 * ⌊p / 2⌋₊ by omega)
      linarith
    have hq₁1 : (1 : ℝ) < ((2 * (⌊p / 2⌋₊ + 1) : ℕ) : ℝ) := by
      have h : (2 : ℝ) ≤ ((2 * (⌊p / 2⌋₊ + 1) : ℕ) : ℝ) := by
        exact_mod_cast (show 2 ≤ 2 * (⌊p / 2⌋₊ + 1) by omega)
      linarith
    obtain ⟨hθ0, hθ1, hθeq⟩ :=
      interpTheta_mem (a := ((2 * ⌊p / 2⌋₊ : ℕ) : ℝ))
        (b := ((2 * (⌊p / 2⌋₊ + 1) : ℕ) : ℝ)) (p := p)
        (by positivity) (by push_cast; linarith) hq₀p hpq₁
    exact iwLqBound_of_pair (q₀ := ((2 * ⌊p / 2⌋₊ : ℕ) : ℝ))
      (q₁ := ((2 * (⌊p / 2⌋₊ + 1) : ℕ) : ℝ))
      (C₀ := Ce ⌊p / 2⌋₊) (C₁ := Ce (⌊p / 2⌋₊ + 1))
      (hunif _ hk).1 (hunif _ (by omega)).1 hq₀1 hq₁1 hθ0 hθ1 hp0 hθeq ha

/-- **From the even exponents to every exponent `p > 1`.**  For `1 < p < 2` the bound is obtained
by applying the case `p' = p/(p-1) ≥ 2` to the conjugate symbol and dualising back. -/
lemma iwLqBound_of_fixed_all {A : Finset Freq} {Ψ Ψ' : Freq → ℂ} {a M : ℝ≥0}
    {Ce : ℕ → ℝ≥0} (_hCe : ∀ k : ℕ, 2 ≤ k → 0 < Ce k)
    (hconj : ∀ ξ, star (Ψ' ξ) = Ψ ξ)
    (hunif : ∀ k : ℕ, 2 ≤ k →
      IWLqBound A Ψ (ENNReal.ofReal ((2 * k : ℕ) : ℝ)) (Ce k * a * M) ∧
      IWLqBound A Ψ' (ENNReal.ofReal ((2 * k : ℕ) : ℝ)) (Ce k * a * M))
    (ha : a ≠ 0) {p : ℝ} (hp : 1 < p) :
    IWLqBound A Ψ (ENNReal.ofReal p) (iwConst Ce p * a * M) := by
  rw [iwConst]
  by_cases h2 : 2 ≤ p
  · rw [if_pos h2]
    exact iwLqBound_of_fixed _hCe hconj hunif ha h2
  · rw [if_neg h2]
    have hp2 : p < 2 := lt_of_not_ge h2
    have hp'2 : 2 ≤ p / (p - 1) := by
      rw [le_div_iff₀ (by linarith : (0 : ℝ) < p - 1)]
      linarith
    have hp'pos : 0 < p / (p - 1) := lt_of_lt_of_le (by norm_num) hp'2
    have hconj' : ∀ ξ, star (Ψ ξ) = Ψ' ξ := by
      intro ξ
      rw [← hconj ξ, star_star]
    have hunif' : ∀ k : ℕ, 2 ≤ k →
        IWLqBound A Ψ' (ENNReal.ofReal ((2 * k : ℕ) : ℝ)) (Ce k * a * M) ∧
        IWLqBound A Ψ (ENNReal.ofReal ((2 * k : ℕ) : ℝ)) (Ce k * a * M) := by
      intro k hk
      exact ⟨(hunif k hk).2, (hunif k hk).1⟩
    have hb := iwLqBound_of_fixed _hCe hconj' hunif' ha hp'2
    have hq' : 1 < (ENNReal.ofReal (p / (p - 1))).toReal := by
      rw [ENNReal.toReal_ofReal hp'pos.le]
      exact lt_of_lt_of_le (by norm_num) hp'2
    have hdual := IWLqBound_of_dual A Ψ' hb hq'
    have hexp : (ENNReal.ofReal (p / (p - 1))).toReal / ((ENNReal.ofReal (p / (p - 1))).toReal - 1)
        = p := by
      rw [ENNReal.toReal_ofReal hp'pos.le]
      have h1 : p - 1 ≠ 0 := by linarith
      have hb : p / (p - 1) - 1 = 1 / (p - 1) := by
        field_simp
        ring_nf
      rw [hb, div_div_div_cancel_right₀ h1 p 1]
      simp
    rw [hexp, funext hconj] at hdual
    exact hdual

theorem IwLqGeneral (hA1 : Work.KMTContract.AreaA1) :
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧
      ∀ (p : ℝ), 1 < p → ∃ C : NNReal, 0 < C ∧
        ∀ (l : ℕ) (k : ℤ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k →
        ∀ (Φ : SchwartzMap ℝ ℂ) (M : NNReal),
          (∀ x, Φ x ≠ 0 → x ∈ Work.Analysis.IonescuWainger.realArc k) →
          (∀ (q : ℝ), 1 < q →
            Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal q) (Φ : ℝ → ℂ) M) →
          (∀ (q : ℝ), 1 < q → Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal q)
            (fun x => star (Φ x)) M) →
          Work.Analysis.IWMultiplier.IWLqBound (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
            (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ)) (ENNReal.ofReal p)
            (C * Work.Analysis.IWMultiplier.angleBracket l * M) := by
  intro ρ hρ hρ1
  rw [Work.KMTContract.areaA1_iff] at hA1
  obtain ⟨Cρ, hCρ, _hNA, hevenA1⟩ := hA1 ρ hρ hρ1
  -- separate the even-exponent constants of area `A1`
  have hsep : ∀ k : ℕ, ∃ C : ℝ≥0, (2 ≤ k → 0 < C) ∧
      (2 ≤ k → ∀ (l : ℕ) (k' : ℤ), GoodMajorArcs ρ Cρ l k' → ∀ (φ : SchwartzMap ℝ ℂ),
        (∀ x, φ x ≠ 0 → x ∈ realArc k') → ∀ (M : ℝ≥0),
        IsLqMultiplierBound (((2 * k : ℕ) : ℝ≥0∞)) (φ : ℝ → ℂ) M →
        IWLqBound (iwArithFreqs ρ l) (periodize (φ : ℝ → ℂ)) (((2 * k : ℕ) : ℝ≥0∞))
          (C * angleBracket l * M)) := by
    intro k
    by_cases hk : 2 ≤ k
    · obtain ⟨C, hC, hb⟩ := hevenA1 k hk
      exact ⟨C, fun _ => hC, fun _ => hb⟩
    · exact ⟨1, fun h => absurd h hk, fun h => absurd h hk⟩
  choose Ce hCe using hsep
  have hCepos : ∀ k : ℕ, 2 ≤ k → 0 < Ce k := fun k hk => (hCe k).1 hk
  have hCeb : ∀ (k : ℕ) (_hk : 2 ≤ k) (l : ℕ) (k' : ℤ), GoodMajorArcs ρ Cρ l k' →
      ∀ (φ : SchwartzMap ℝ ℂ), (∀ x, φ x ≠ 0 → x ∈ realArc k') → ∀ (M : ℝ≥0),
      IsLqMultiplierBound (((2 * k : ℕ) : ℝ≥0∞)) (φ : ℝ → ℂ) M →
      IWLqBound (iwArithFreqs ρ l) (periodize (φ : ℝ → ℂ)) (((2 * k : ℕ) : ℝ≥0∞))
        (Ce k * angleBracket l * M) := fun k hk => (hCe k).2 hk
  refine ⟨Cρ, hCρ, fun p hp => ?_⟩
  refine ⟨iwConst Ce p, ?_, ?_⟩
  · rw [iwConst]
    by_cases h2 : 2 ≤ p
    · rw [if_pos h2]
      exact evenConst_pos hCepos h2
    · rw [if_neg h2]
      have hp2 : p < 2 := lt_of_not_ge h2
      have hp'2 : 2 ≤ p / (p - 1) := by
        rw [le_div_iff₀ (by linarith : (0 : ℝ) < p - 1)]
        linarith
      exact evenConst_pos hCepos hp'2
  · intro l k hgood Φ M hsupp hΦM hstarM
    have hunif : ∀ k' : ℕ, 2 ≤ k' →
        IWLqBound (iwArithFreqs ρ l) (periodize (Φ : ℝ → ℂ))
          (ENNReal.ofReal ((2 * k' : ℕ) : ℝ)) (Ce k' * angleBracket l * M) ∧
        IWLqBound (iwArithFreqs ρ l) (periodize (fun x => star (Φ x)))
          (ENNReal.ofReal ((2 * k' : ℕ) : ℝ)) (Ce k' * angleBracket l * M) := by
      intro k' hk'
      have hpow : (1 : ℝ) < ((2 * k' : ℕ) : ℝ) := by
        exact_mod_cast (show 1 < 2 * k' by omega)
      constructor
      · have hM' : IsLqMultiplierBound (((2 * k' : ℕ) : ℝ≥0∞)) (Φ : ℝ → ℂ) M := by
          have h := hΦM ((2 * k' : ℕ) : ℝ) hpow
          rwa [ofReal_two_mul] at h
        have h := hCeb k' hk' l k hgood Φ hsupp M hM'
        rwa [← ofReal_two_mul k'] at h
      · have hM' : IsLqMultiplierBound (((2 * k' : ℕ) : ℝ≥0∞))
            ((starSchwartz Φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) M := by
          rw [starSchwartz_coe]
          have h := hstarM ((2 * k' : ℕ) : ℝ) hpow
          rwa [ofReal_two_mul] at h
        have hsupp' : ∀ x, starSchwartz Φ x ≠ 0 → x ∈ realArc k :=
          fun x hx => hsupp x (starSchwartz_ne_zero hx)
        have h := hCeb k' hk' l k hgood (starSchwartz Φ) hsupp' M hM'
        rw [starSchwartz_coe] at h
        rwa [← ofReal_two_mul k'] at h
    exact iwLqBound_of_fixed_all hCepos
      (fun ξ => periodize_star (Φ : ℝ → ℂ) ξ) hunif (ne_of_gt (angleBracket_pos l)) hp

end

end Work.KMTAreas.A7
