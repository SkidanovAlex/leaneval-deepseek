import Mathlib
import Submission.Work.KMTContract.Areas
import Submission.Work.KMTPlan.A6.iwConvEqIwOpSetMemlp
import Submission.Work.KMTAreas.A4.fourierZCoeFnEqTsum
import Submission.Work.KMTAreas.A4.iwSymbolSetNegEq

/-!
# The Ionescu–Wainger projection fixes its own major arcs

Let `ρ ∈ (0,1]`, `Cρ ≥ 2` and let `(l,k)` have good major arcs
(`GoodMajorArcs ρ Cρ l k`, i.e. `k ≤ -Cρ 2^{ρl}`), with the arcs non-aliasing
(`NonAliasing k (iwArithFreqs ρ l)`).  Then the Ionescu–Wainger projection
`kmtProj ρ l k = Π_{≤l,≤k}` acts as the identity on every `ψ ∈ ℓ¹(ℤ)` whose
`ℤ`-Fourier transform is supported in the major arcs `majorArc ρ l (k-1)`:

`kmtProj ρ l k ψ = ψ`.

This is the "the projection does not lose anything supported on its own arcs"
step of §5 of Krause–Mirek–Tao (used when the alternate inverse theorem `lip`
returns a major-arc function `F`).

## The two ingredients

* **The symbol is `1` on the arcs.**  For `ξ = α₀ + θ₀ ∈ majorArc ρ l (k-1)`, the
  term `α = α₀` of `iwSymbolSet A Φ ξ = ∑_{α ∈ A} Φ (ξ - α)` contributes
  `Φ(θ₀) = 1` (the periodised cutoff `η_{≤k}` equals `1` on `ℝ_{≤k-1}`), and every
  other term vanishes: if `Φ(ξ - α) ≠ 0` then `ξ - α` has a real representative `θ'`
  with `|θ'| < 2^k`, whence `α + θ' = α₀ + θ₀` with `θ', θ₀ ∈ ℝ_{≤k}` and
  non-aliasing forces `α = α₀`.
* **The `ℓ²`-Fourier transform agrees with the pointwise one.**  For `ψ ∈ ℓ¹ ⊆ ℓ²`
  the `L²`-Fourier transform `fourierZ ⟨ψ,_⟩` is a.e. the absolutely convergent
  series `∑_x ψ x · e_x`, i.e. the `ℤ`-Fourier transform `ZFourier` evaluated at the
  reflected frequency; the projection is the multiplier with symbol
  `iwSymbolSet A (periodize (etaCut kmtEta k))`, and since that symbol is `1` on the
  support of `ZFourier ψ`, the multiplier fixes `fourierZ ψ`.

## Main result

* `Work.KMTAreas.A4.kmtProjEqSelf`
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A4

open MeasureTheory Filter
open scoped BigOperators ENNReal NNReal
open Work.Analysis.IonescuWainger
open Work.KMTContract (kmtEta kmtEta_zero kmtEta_one kmtBump norm_kmtEta_le kmtEta_neg)

noncomputable section

/-! ## Elementary facts about the cutoff `η_{≤k}` -/

/-- `η_{≤k}` vanishes as soon as `2^k ≤ |y|`. -/
private lemma etaCut_kmtEta_eq_zero {k : ℤ} {y : ℝ} (h : (2 : ℝ) ^ k ≤ |y|) :
    etaCut kmtEta k y = 0 := by
  rw [etaCut]
  refine kmtEta_zero ?_
  rw [abs_div, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) k)]
  rw [one_le_div (zpow_pos (by norm_num : (0 : ℝ) < 2) k)]
  exact h

/-- **The periodisation is trivial on the support of the cutoff.**  For `k ≤ -1` and
`|x| ≤ 1/2`, `periodize (η_{≤k})` at `(x : ℝ/ℤ)` is `η_{≤k}(x)`: every other integer
translate of `x` lies at distance `≥ 1/2 ≥ 2^k` from the origin, where the cutoff vanishes. -/
private lemma periodize_etaCut_coe_eq {k : ℤ} (hk : k ≤ -1) {x : ℝ} (hx : |x| ≤ 1 / 2) :
    periodize (etaCut kmtEta k) ((x : ℝ) : Work.Analysis.IonescuWainger.Circle)
      = etaCut kmtEta k x := by
  have hterm : ∀ n : ℤ, n ≠ 0 → etaCut kmtEta k (x + (n : ℝ)) = 0 := by
    intro n hn
    refine etaCut_kmtEta_eq_zero ?_
    have hk2 : (2 : ℝ) ^ k ≤ 1 / 2 := by
      have h := zpow_le_zpow_right₀ (show (1 : ℝ) ≤ 2 by norm_num) hk
      norm_num at h
      linarith
    have hcases : (n : ℝ) ≤ -1 ∨ 1 ≤ (n : ℝ) := by
      have h : n ≤ -1 ∨ 1 ≤ n := by omega
      rcases h with h | h
      · exact Or.inl (by exact_mod_cast h)
      · exact Or.inr (by exact_mod_cast h)
    have hxle : x ≤ 1 / 2 := (abs_le.mp hx).2
    have hxge : -(1 / 2) ≤ x := (abs_le.mp hx).1
    have hpos : (1 : ℝ) / 2 ≤ |x + (n : ℝ)| := by
      rcases hcases with h | h
      · rw [abs_of_nonpos (by linarith : x + (n : ℝ) ≤ 0)]
        linarith
      · rw [abs_of_nonneg (by linarith : 0 ≤ x + (n : ℝ))]
        linarith
    linarith
  calc periodize (etaCut kmtEta k) ((x : ℝ) : Work.Analysis.IonescuWainger.Circle)
      = ∑' n : ℤ, etaCut kmtEta k (x + (n : ℝ)) := Work.KMTContract.periodizeCoeEqTsum _ _
    _ = etaCut kmtEta k (x + ((0 : ℤ) : ℝ)) :=
        tsum_eq_single (f := fun n : ℤ => etaCut kmtEta k (x + (n : ℝ))) 0 hterm
    _ = etaCut kmtEta k x := by simp

/-- **Every point of the support of the periodised cutoff is a translate of a real point of
`(-2^k, 2^k)`.**  If `periodize (η_{≤k})` does not vanish at `ξ`, then `ξ = (θ : ℝ/ℤ)` for a
real `θ` with `|θ| < 2^k`. -/
private lemma exists_coe_eq_periodize_etaCut_ne_zero {k : ℤ}
    {ξ : Work.Analysis.IonescuWainger.Circle}
    (h : periodize (etaCut kmtEta k) ξ ≠ 0) :
    ∃ θ : ℝ, (θ : Work.Analysis.IonescuWainger.Circle) = ξ ∧ |θ| < (2 : ℝ) ^ k := by
  set x : ℝ := (AddCircle.equivIco (1 : ℝ) 0 ξ).val with hxdef
  have hxeq : (x : Work.Analysis.IonescuWainger.Circle) = ξ := by
    rw [hxdef]; exact AddCircle.coe_equivIco
  have hne : ∃ n : ℤ, etaCut kmtEta k (x + (n : ℝ)) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    refine h ?_
    have hper : periodize (etaCut kmtEta k) ξ
        = ∑' n : ℤ, etaCut kmtEta k (x + (n : ℝ)) := by
      rw [← hxeq]
      exact Work.KMTContract.periodizeCoeEqTsum _ _
    rw [hper]
    have h0 : (fun n : ℤ => etaCut kmtEta k (x + (n : ℝ))) = fun _ => (0 : ℂ) :=
      funext fun n => hcon n
    rw [h0, tsum_zero]
  obtain ⟨n, hn⟩ := hne
  refine ⟨x + (n : ℝ), ?_, ?_⟩
  · have hnc : (((n : ℝ)) : Work.Analysis.IonescuWainger.Circle) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]
      exact ⟨n, by simp⟩
    rw [AddCircle.coe_add, hxeq, hnc, add_zero]
  · by_contra hcon
    push_neg at hcon
    exact hn (etaCut_kmtEta_eq_zero hcon)

/-! ## The symbol is `1` on its own major arcs -/

/-- **The Ionescu–Wainger symbol is `1` on the major arcs.**  Let `(l,k)` have good major arcs
with `Cρ ≥ 2`, `ρ > 0`, and let the arithmetic frequencies be non-aliasing at scale `k`.  Then
the symbol `ξ ↦ ∑_{α ∈ (ℚ/ℤ)_{≤l}} η_{≤k}(ξ - α)` equals `1` at every `ξ` of the major arc
`majorArc ρ l (k-1)`.

The proof is the argument of §5 discussed in the module docstring: the term `α = α₀` of the
decomposition `ξ = α₀ + θ₀` contributes `1`, and any other nonvanishing term would produce a
second point `(θ', β)` with `β + θ' = α₀ + θ₀`, `θ', θ₀ ∈ ℝ_{≤k}`, contradicting non-aliasing. -/
theorem iwSymbolSet_eq_one_of_mem_majorArc {ρ Cρ : ℝ} {l : ℕ} {k : ℤ}
    (hlk : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k) (hCρ : 2 ≤ Cρ) (hρ : 0 < ρ)
    (hNA : Work.Analysis.IonescuWainger.NonAliasing k
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)) :
    ∀ ξ ∈ Work.Analysis.InverseTheory.majorArc ρ l (k - 1),
      iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)) ξ = 1 := by
  have hk2 : (k : ℝ) ≤ -2 := by
    have hS : (1 : ℝ) ≤ (2 : ℝ) ^ (ρ * (l : ℝ)) :=
      Real.one_le_rpow (by norm_num) (by positivity)
    have hmul : 2 * 1 ≤ Cρ * (2 : ℝ) ^ (ρ * (l : ℝ)) :=
      mul_le_mul hCρ hS (by norm_num) (by linarith)
    have hg : (k : ℝ) ≤ -Cρ * (2 : ℝ) ^ (ρ * (l : ℝ)) := hlk
    nlinarith
  have hkpow : (2 : ℝ) ^ k ≤ 1 / 4 := by
    have h := zpow_le_zpow_right₀ (show (1 : ℝ) ≤ 2 by norm_num)
      (show k ≤ (-2 : ℤ) by exact_mod_cast hk2)
    norm_num at h
    linarith
  have hk1 : k ≤ -1 := by
    have h : k ≤ -2 := by exact_mod_cast hk2
    omega
  have hkpowm : (2 : ℝ) ^ (k - 1) = (2 : ℝ) ^ k / 2 := by
    rw [zpow_sub_one₀ (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  intro ξ hξ
  obtain ⟨α₀, hα₀, θ₀, hθ₀, hξeq⟩ := Work.Analysis.InverseTheory.mem_majorArc.mp hξ
  rw [Work.Analysis.InverseTheory.mem_realFreqInterval] at hθ₀
  have hθ₀abs : |θ₀| ≤ (2 : ℝ) ^ (k - 1) := abs_le.mpr hθ₀
  have hθ₀mem : θ₀ ∈ realArc k := by
    rw [realArc, Set.mem_Icc]
    have hmono : (2 : ℝ) ^ (k - 1) ≤ (2 : ℝ) ^ k :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    constructor <;> linarith [abs_le.mp hθ₀abs]
  have hθ₀half : |θ₀| ≤ 1 / 2 := by
    have : (2 : ℝ) ^ (k - 1) ≤ 1 / 2 := by rw [hkpowm]; linarith
    linarith
  rw [iwSymbolSet_apply]
  refine (Finset.sum_eq_single α₀ ?_ ?_).trans ?_
  · intro β hβ hβne
    by_contra hb
    obtain ⟨θ', hθ'eq, hθ'lt⟩ := exists_coe_eq_periodize_etaCut_ne_zero hb
    have hθ'mem : θ' ∈ realArc k := by
      rw [realArc, Set.mem_Icc]
      exact ⟨(abs_le.mp (le_of_lt hθ'lt)).1, (abs_le.mp (le_of_lt hθ'lt)).2⟩
    have heq : β + ((θ' : ℝ) : Work.Analysis.IonescuWainger.Circle)
        = α₀ + ((θ₀ : ℝ) : Work.Analysis.IonescuWainger.Circle) := by
      rw [hθ'eq, hξeq]; abel
    exact hβne (hNA β hβ α₀ hα₀ θ' hθ'mem θ₀ hθ₀mem heq).1
  · intro hnot; exact absurd hα₀ hnot
  · have hsub : ξ - α₀ = ((θ₀ : ℝ) : Work.Analysis.IonescuWainger.Circle) := by
      rw [hξeq]; abel
    rw [hsub, periodize_etaCut_coe_eq hk1 hθ₀half, etaCut]
    refine kmtEta_one ?_
    rw [abs_div, abs_of_pos (zpow_pos (by norm_num : (0 : ℝ) < 2) k),
      div_le_iff₀ (zpow_pos (by norm_num : (0 : ℝ) < 2) k)]
    rw [show (1 / 2) * (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) by rw [hkpowm]; ring]
    exact hθ₀abs

/-! ## `ℓ¹ ⊆ ℓ²` -/

/-- A summable sequence of norms gives an `ℓ²` sequence. -/
theorem memℓp_two_of_summable_norm {ψ : ℤ → ℂ} (h : Summable fun x : ℤ => ‖ψ x‖) :
    Memℓp ψ 2 := by
  rw [memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat]
  have hle : ∀ x : ℤ, ‖ψ x‖ ≤ ∑' y : ℤ, ‖ψ y‖ :=
    fun x => h.le_tsum x (fun _ _ => norm_nonneg _)
  refine Summable.of_nonneg_of_le (fun x => by positivity) (fun x => ?_)
    (h.mul_left (∑' y : ℤ, ‖ψ y‖))
  have h0 := norm_nonneg (ψ x)
  calc ‖ψ x‖ ^ (2 : ℝ) = ‖ψ x‖ * ‖ψ x‖ := by rw [Real.rpow_two]; ring
    _ ≤ (∑' y : ℤ, ‖ψ y‖) * ‖ψ x‖ := mul_le_mul_of_nonneg_right (hle x) h0

/-! ## The main result -/

/-- **The Ionescu–Wainger projection `Π_{≤l,≤k} = kmtProj ρ l k` fixes every `ℓ¹` function whose
`ℤ`-Fourier transform is supported in its own major arcs `majorArc ρ l (k-1)`**, for good major
arcs with `Cρ ≥ 2` and non-aliasing at scale `k`. -/
theorem kmtProjEqSelf {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {Cρ : ℝ} (hCρ : 2 ≤ Cρ)
    (hNonAl : ∀ (l : ℕ) (k : ℤ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k →
      Work.Analysis.IonescuWainger.NonAliasing k (Work.Analysis.IonescuWainger.iwArithFreqs ρ l))
    {l : ℕ} {k : ℤ} (hlk : Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k)
    {ψ : ℤ → ℂ} (hψ : Summable fun x : ℤ => ‖ψ x‖)
    (hsupp : Work.Analysis.InverseTheory.FourierSupportIn ψ
      (Work.Analysis.InverseTheory.majorArc ρ l (k - 1))) :
    Work.KMTContract.kmtProj ρ l k ψ = ψ := by
  have hψ2 : Memℓp ψ 2 := memℓp_two_of_summable_norm hψ
  set F : L2Z := ⟨ψ, hψ2⟩ with hF
  have hFcoe : ⇑F = ψ := rfl
  have hηmeas : Measurable (etaCut kmtEta k) :=
    (Complex.continuous_ofReal.measurable.comp
      ((kmtBump.contDiff (n := 1)).continuous.measurable)).comp (measurable_id.div_const _)
  have hΦ : MemLp (periodize (etaCut kmtEta k)) ⊤ circleMeasure :=
    memLp_periodize hηmeas (R := (2 : ℝ) ^ k) (by positivity)
      (fun x hx => etaCut_kmtEta_eq_zero (le_of_lt hx))
      (fun x => norm_kmtEta_le (x / (2 : ℝ) ^ k))
  have hσ : MemLp (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))) ⊤ circleMeasure :=
    Work.Analysis.IWMultiplier.memLp_iwSymbolSet _ hΦ
  have hkey := iwSymbolSet_eq_one_of_mem_majorArc hlk hCρ hρ (hNonAl l k hlk)
  have hae : ⇑(fourierZ F) =ᵐ[circleMeasure]
      fun ξ => Work.Analysis.InverseTheory.ZFourier ψ (-ξ) := by
    rw [hF]
    exact fourierZCoeFnEqTsum hψ hψ2
  have hpoint : ∀ ξ : Work.Analysis.IonescuWainger.Circle,
      iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)) ξ
          * Work.Analysis.InverseTheory.ZFourier ψ (-ξ)
        = Work.Analysis.InverseTheory.ZFourier ψ (-ξ) := by
    intro ξ
    by_cases hmem : -ξ ∈ Work.Analysis.InverseTheory.majorArc ρ l (k - 1)
    · have h1 : iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)) ξ = 1 := by
        rw [← iwSymbolSetNegEq ρ l k ξ]
        exact hkey (-ξ) hmem
      rw [h1, one_mul]
    · rw [hsupp (-ξ) hmem, mul_zero]
  have hfix : hσ.toLp (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k))) • fourierZ F
      = fourierZ F := by
    refine Lp.ext ?_
    have h1 : ⇑(hσ.toLp (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)))
          • fourierZ F)
        =ᵐ[circleMeasure] fun ξ =>
          iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)) ξ
            * Work.Analysis.InverseTheory.ZFourier ψ (-ξ) := by
      filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := 2) (r := 2)
          (hσ.toLp (iwSymbolSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)))) (fourierZ F),
        MemLp.coeFn_toLp hσ, hae] with ξ h1 h2 h3
      rw [h1, Pi.smul_apply', h2, h3, smul_eq_mul]
    filter_upwards [h1, hae] with ξ h1 h2
    rw [h1, h2, hpoint ξ]
  have hop : iwOpSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)) hσ F = F := by
    refine fourierZ.injective ?_
    exact (fourierZ_multiplierOf (iwSymbolSet (iwArithFreqs ρ l)
      (periodize (etaCut kmtEta k))) hσ F).trans hfix
  have hconv : Work.Analysis.IWMultiplier.iwConv (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)) ψ
      = ⇑(iwOpSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)) hσ F) := by
    rw [← hFcoe]
    exact Work.KMTPlan.A6.iwConvEqIwOpSetMemlp hσ F
  funext n
  have h1 : Work.KMTContract.kmtProj ρ l k ψ n
      = ⇑(iwOpSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta k)) hσ F) n := by
    show Work.Analysis.IWMultiplier.iwConv (iwArithFreqs ρ l)
      (periodize (etaCut kmtEta k)) ψ n = _
    rw [hconv]
  rw [h1, hop]

end

end Work.KMTAreas.A4
