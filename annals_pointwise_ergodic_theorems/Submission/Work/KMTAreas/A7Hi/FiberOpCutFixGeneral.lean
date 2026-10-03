import Mathlib
import Submission.Work.KMTAreas.A7.fiberOpTex_eq_fiberOp_self_bdd

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTAreas.A7Hi

open MeasureTheory Finset
open scoped BigOperators

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

noncomputable section

/-! ## Elementary arc geometry -/

open Work.BourgainPlan.IonescuWainger in
/-- The difference of two points of the arcs `[-r₁,r₁]` and `[-r₂,r₂]` at `0` is bounded by
`r₁ + r₂`. -/
lemma arcSet_sub_norm_le {r₁ r₂ : ℝ} {x y : Circ}
    (hx : x ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 r₁)
    (hy : y ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 r₂) : ‖x - y‖ ≤ r₁ + r₂ := by
  obtain ⟨θ₁, hθ₁, hx'⟩ := hx
  obtain ⟨θ₂, hθ₂, hy'⟩ := hy
  have hsub : x - y = ((θ₁ - θ₂ : ℝ) : Circ) := by
    rw [hx', hy', zero_add, zero_add]
    exact (AddCircle.coe_sub (1 : ℝ) θ₁ θ₂).symm
  rw [hsub]
  calc ‖((θ₁ - θ₂ : ℝ) : Circ)‖ ≤ |θ₁ - θ₂| :=
        Work.BourgainPlan.IonescuWainger.norm_circle_coe_le_abs _
    _ ≤ |θ₁| + |θ₂| := abs_sub _ _
    _ ≤ r₁ + r₂ := add_le_add hθ₁ hθ₂

/-- Any circle point has norm at most `1/2`, the diameter of `ℝ/ℤ`. -/
lemma norm_le_half (x : Circ) : ‖x‖ ≤ 1 / 2 := by
  simpa using AddCircle.norm_le_half_period (1 : ℝ) (x := x) (by norm_num)

/-! ## The aliasing product identity with the sharp separation `4ε` -/

/-- **The aliasing product identity with separation `4ε`.**  This is the sharpened form of
`Work.KMTAreas.A7.aliasingSymbolProduct`: because the pivot term `ξ - a₀` lies in the arc of
radius `ε` (not only `2ε`), a separation of `4ε` already forces the collapse. -/
theorem plateau_mul_of_sep_four (A : Finset Circ) (eps : ℝ) (heps : 0 < eps)
    (c : Circ → ℂ) (mt pt : Circ → ℂ)
    (hsep : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → 4 * eps ≤ ‖a - b‖)
    (hm1 : ∀ th : Circ, th ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 eps → mt th = 1)
    (hms : ∀ th : Circ, mt th ≠ 0 → th ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 (2 * eps))
    (hp : ∀ th : Circ, pt th ≠ 0 → th ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 eps)
    (xi : Circ) :
    (∑ a ∈ A, c a * mt (xi - a)) * (∑ a ∈ A, pt (xi - a))
      = ∑ a ∈ A, c a * pt (xi - a) := by
  by_cases h : ∃ a ∈ A, xi - a ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 eps
  · obtain ⟨a₀, ha₀A, ha₀⟩ := h
    have hmt_a0 : mt (xi - a₀) = 1 := hm1 _ ha₀
    have key : ∀ a ∈ A, a ≠ a₀ → mt (xi - a) = 0 ∧ pt (xi - a) = 0 := by
      intro a haA hne
      have hz1 : mt (xi - a) = 0 := by
        by_contra hmm
        have h2 : xi - a ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 (2 * eps) := hms _ hmm
        have h3 : (xi - a) - (xi - a₀) = a₀ - a := by abel
        have h1 : ‖a₀ - a‖ ≤ 2 * eps + eps := by
          rw [← h3]; exact arcSet_sub_norm_le h2 ha₀
        have h4 := hsep a haA a₀ ha₀A hne
        rw [norm_sub_rev] at h4
        linarith
      have hz2 : pt (xi - a) = 0 := by
        by_contra hpp
        have h2 : xi - a ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 eps := hp _ hpp
        have h3 : (xi - a) - (xi - a₀) = a₀ - a := by abel
        have h1 : ‖a₀ - a‖ ≤ eps + eps := by
          rw [← h3]; exact arcSet_sub_norm_le h2 ha₀
        have h4 := hsep a haA a₀ ha₀A hne
        rw [norm_sub_rev] at h4
        linarith
      exact ⟨hz1, hz2⟩
    have hL : (∑ a ∈ A, c a * mt (xi - a)) = c a₀ := by
      rw [Finset.sum_eq_single a₀ (fun b hb hne => by rw [(key b hb hne).1, mul_zero])
        (fun hna => absurd ha₀A hna)]
      rw [hmt_a0, mul_one]
    have hS : (∑ a ∈ A, pt (xi - a)) = pt (xi - a₀) := by
      rw [Finset.sum_eq_single a₀ (fun b hb hne => (key b hb hne).2)
        (fun hna => absurd ha₀A hna)]
    have hR : (∑ a ∈ A, c a * pt (xi - a)) = c a₀ * pt (xi - a₀) := by
      rw [Finset.sum_eq_single a₀ (fun b hb hne => by rw [(key b hb hne).2, mul_zero])
        (fun hna => absurd ha₀A hna)]
    rw [hL, hS, hR]
  · have hpt : ∀ a ∈ A, pt (xi - a) = 0 := by
      intro a ha
      by_contra hne
      exact h ⟨a, ha, hp _ hne⟩
    have h1 : (∑ a ∈ A, pt (xi - a)) = 0 := Finset.sum_eq_zero (fun a ha => hpt a ha)
    have h2 : (∑ a ∈ A, c a * pt (xi - a)) = 0 :=
      Finset.sum_eq_zero (fun a ha => by rw [hpt a ha, mul_zero])
    rw [h1, h2, mul_zero]

/-- The symbol-level collapse, in the form used by the Ionescu--Wainger calculus. -/
theorem iwSymbolSet_plateau_mul_four {A : Finset Circ} {eps : ℝ} (heps : 0 < eps)
    {M Φ : Circ → ℂ}
    (hm1 : ∀ th : Circ, th ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 eps → M th = 1)
    (hms : ∀ th : Circ, M th ≠ 0 → th ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 (2 * eps))
    (hna : ∀ a ∈ A, ∀ b ∈ A, a ≠ b → 4 * eps ≤ ‖a - b‖)
    (hΦ : ∀ th : Circ, Φ th ≠ 0 → th ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 eps) :
    ∀ ζ : Circ, Work.Analysis.IonescuWainger.iwSymbolSet A M ζ
      * Work.Analysis.IonescuWainger.iwSymbolSet A Φ ζ
      = Work.Analysis.IonescuWainger.iwSymbolSet A Φ ζ := by
  intro ζ
  have h := plateau_mul_of_sep_four A eps heps (fun _ => 1) M Φ hna hm1 hms hΦ ζ
  simpa [Work.Analysis.IonescuWainger.iwSymbolSet] using h

/-! ## The `δ ≤ 1/8` bound forced by the separation hypothesis -/

/-- **The separation hypothesis forces `δ ≤ 1/8`.**  For `l ≥ 1` the IW arithmetic frequency set
`(ℚ/ℤ)_{≤l}` contains the two distinct points `0` and `1/2` (because `2 ∈ P_{≤l}`), and two
distinct points of the circle are at distance at most `1/2`; so `4δ ≤ 1/2`. -/
theorem delta_le_eighth_of_sep (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) (hl : 1 ≤ l)
    (δ : ℝ)
    (hsep : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
      ∀ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l, α ≠ β → 4 * δ ≤ ‖α - β‖) :
    δ ≤ 1 / 8 := by
  have h2l : (2 : ℕ) ≤ 2 ^ l := by
    calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl
  have htwo : (2 : ℕ) ∈ Work.Analysis.IonescuWainger.iwP ρ l := by
    rw [Work.Analysis.IonescuWainger.mem_iwP]
    by_cases hl0 : l ≤ Work.Analysis.IonescuWainger.iwC0 ρ
    · exact Or.inl ⟨hl0, by norm_num, h2l⟩
    · exact Or.inr ⟨not_le.mp hl0,
        Work.Analysis.IonescuWainger.iwPconcrete_contains_range hρ hρ1 (le_of_lt (not_le.mp hl0))
          (by norm_num) h2l⟩
  have hbeta : (((1 : ℝ) / (2 : ℝ)) : Circ) ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l := by
    rw [Work.Analysis.IonescuWainger.mem_iwArithFreqs]
    exact ⟨2, htwo, by
      simpa using Work.Analysis.IonescuWainger.nsmul_div_eq_zero (q := 2) (a := 1)
        (by norm_num)⟩
  have hzero : (0 : Circ) ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l := by
    rw [Work.Analysis.IonescuWainger.mem_iwArithFreqs]
    exact ⟨1, Work.Analysis.IonescuWainger.one_mem_iwP ρ l, by simp⟩
  have hβ0 : (((1 : ℝ) / (2 : ℝ)) : Circ) ≠ 0 := by
    intro hcon
    rw [AddCircle.coe_eq_zero_iff] at hcon
    obtain ⟨z, hz⟩ := hcon
    have hz' : (z : ℝ) = 1 / 2 := by
      have h := hz
      rw [zsmul_eq_mul, mul_one] at h
      exact h
    have h2 : ((2 * z : ℤ) : ℝ) = 1 := by
      push_cast
      rw [hz']
      norm_num
    have h2' : (2 * z : ℤ) = 1 := by exact_mod_cast h2
    omega
  have hne : (0 : Circ) ≠ (((1 : ℝ) / (2 : ℝ)) : Circ) := Ne.symm hβ0
  have h1 := hsep 0 hzero (((1 : ℝ) / (2 : ℝ)) : Circ) hbeta hne
  rw [zero_sub, norm_neg] at h1
  have h2 : ‖(((1 : ℝ) / (2 : ℝ)) : Circ)‖ ≤ 1 / 2 := by
    calc ‖(((1 : ℝ) / (2 : ℝ)) : Circ)‖ ≤ |(1 : ℝ) / 2| :=
          Work.BourgainPlan.IonescuWainger.norm_circle_coe_le_abs _
      _ = 1 / 2 := by norm_num
  linarith

/-! ## The plateau transfer for periodisations -/

/-- If `m` is `1` on `[-δ,δ]` and vanishes off `[-2δ,2δ]` with `δ < 1/3`, then `periodize m`
equals `1` on the image of `[-δ,δ]`. -/
lemma periodize_eq_one_of_support {m : ℝ → ℂ} {δ : ℝ} (hδ : 0 < δ) (hδ3 : δ < 1 / 3)
    (h0 : ∀ θ : ℝ, 2 * δ < |θ| → m θ = 0) (h1 : ∀ θ : ℝ, |θ| ≤ δ → m θ = 1)
    {ξ : Circ} (hξ : ξ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ) :
    Work.Analysis.IonescuWainger.periodize m ξ = 1 := by
  obtain ⟨θ, hθ, hξθ⟩ := hξ
  have hξθ' : (θ : Circ) = ξ := by rw [hξθ, zero_add]
  rw [← hξθ', Work.KMTContract.periodizeCoeEqTsum]
  rw [tsum_eq_single 0 (fun k hk => ?_)]
  · simpa using h1 θ hθ
  · apply h0
    have hk1 : (1 : ℝ) ≤ |((k : ℤ) : ℝ)| := by
      have h1k : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
      calc (1 : ℝ) = ((1 : ℤ) : ℝ) := by norm_num
        _ ≤ ((|k| : ℤ) : ℝ) := by exact_mod_cast h1k
        _ = |((k : ℤ) : ℝ)| := by rw [Int.cast_abs]
    have htri : |((k : ℤ) : ℝ)| ≤ |θ + (k : ℝ)| + |θ| := by
      have hsum := abs_add_le (θ + (k : ℝ)) (-θ)
      have heq : θ + (k : ℝ) + -θ = (k : ℝ) := by ring
      rwa [heq, abs_neg] at hsum
    linarith

/-- A nonvanishing periodisation detects a real representative in the support (re-exported in
the form needed below). -/
lemma periodize_support_mem_arcSet {m : ℝ → ℂ} {δ : ℝ}
    (hsupp : ∀ y : ℝ, m y ≠ 0 → |y| ≤ δ) {ξ : Circ}
    (h : Work.Analysis.IonescuWainger.periodize m ξ ≠ 0) :
    ξ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ :=
  Work.KMTAreas.A7.fiberOpTex_periodize_ne_zero_mem_arcSet hsupp h

/-! ## The plateau identity for the IW convolution at separation `4δ` -/

/-- **The wide-cut identity with the sharp separation `4δ`**: the fibre at residue `0` of the
multiplier `m` fixes the exact-height projection `Tex ρ l φ f`. -/
theorem iwConv_comp_plateau_four (ρ : ℝ) (l : ℕ) (m : ℝ → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hm : MeasureTheory.Integrable m)
    (hmsum : Summable (fun j : ℤ => Work.KMTAreas.A7.cw m j))
    (hm1 : ∀ ξ : Circ, ξ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ →
      Work.Analysis.IonescuWainger.periodize m ξ = 1)
    (hms : ∀ ξ : Circ, Work.Analysis.IonescuWainger.periodize m ξ ≠ 0 →
      ξ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 (2 * δ))
    (hna : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
      ∀ β ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l, α ≠ β → 4 * δ ≤ ‖α - β‖)
    (φ : ℝ → ℂ) (hφ : MeasureTheory.Integrable φ)
    (hφsum : Summable (fun j : ℤ => Work.KMTAreas.A7.cw φ j))
    (hφpacket : ∀ ξ : Circ, Work.Analysis.IonescuWainger.periodize φ ξ ≠ 0 →
      ξ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ)
    (f : ℤ → ℂ) (hf : ∃ B : ℝ, ∀ y : ℤ, ‖f y‖ ≤ B) :
    Work.Analysis.IWMultiplier.iwConv (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
        (Work.Analysis.IonescuWainger.periodize m) (Work.KMTAreas.A7.Tex ρ l φ f)
      = Work.KMTAreas.A7.Tex ρ l φ f := by
  obtain ⟨B, hB⟩ := hf
  have hMint : MeasureTheory.Integrable (Work.Analysis.IonescuWainger.periodize m)
      Work.Analysis.IonescuWainger.circleMeasure :=
    Work.KMTPlan.A6.IntegrablePeriodize hm
  have hPint : MeasureTheory.Integrable (Work.Analysis.IonescuWainger.periodize φ)
      Work.Analysis.IonescuWainger.circleMeasure :=
    Work.KMTPlan.A6.IntegrablePeriodize hφ
  have hSint : MeasureTheory.Integrable
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
        (Work.Analysis.IonescuWainger.periodize m)) Work.Analysis.IonescuWainger.circleMeasure :=
    Work.KMTAreas.A7.integrable_iwSymbolSet _ hMint
  have hTint : MeasureTheory.Integrable
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
        (Work.Analysis.IonescuWainger.periodize φ)) Work.Analysis.IonescuWainger.circleMeasure :=
    Work.KMTAreas.A7.integrable_iwSymbolSet _ hPint
  have hgate : ∀ ζ : Circ,
      Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
          (Work.Analysis.IonescuWainger.periodize m) ζ
        * Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
          (Work.Analysis.IonescuWainger.periodize φ) ζ
      = Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
          (Work.Analysis.IonescuWainger.periodize φ) ζ :=
    iwSymbolSet_plateau_mul_four (A := Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l) hδ
      hm1 hms hna hφpacket
  have hFGint : MeasureTheory.Integrable (fun ξ : Circ =>
      Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
          (Work.Analysis.IonescuWainger.periodize m) ξ
        * Work.Analysis.IonescuWainger.iwSymbolSet
            (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
          (Work.Analysis.IonescuWainger.periodize φ) ξ) Work.Analysis.IonescuWainger.circleMeasure :=
    hTint.congr (Filter.Eventually.of_forall (fun ξ => (hgate ξ).symm))
  have hMs0 : Summable (fun j : ℤ => ‖fourierCoeff (Work.Analysis.IonescuWainger.periodize m) j‖) :=
    hmsum.norm.congr (fun j => by rw [Work.KMTAreas.A7.fourierCoeff_periodize_eq_cw hm j])
  have hPs0 : Summable (fun j : ℤ => ‖fourierCoeff (Work.Analysis.IonescuWainger.periodize φ) j‖) :=
    hφsum.norm.congr (fun j => by rw [Work.KMTAreas.A7.fourierCoeff_periodize_eq_cw hφ j])
  have hMs : Summable (fun j : ℤ => fourierCoeff
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
        (Work.Analysis.IonescuWainger.periodize m)) j) :=
    (Work.KMTAreas.A7.summable_norm_fourierCoeff_iwSymbolSet _ hMint hMs0).of_norm
  have hPs : Summable (fun j : ℤ => fourierCoeff
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
        (Work.Analysis.IonescuWainger.periodize φ)) j) :=
    (Work.KMTAreas.A7.summable_norm_fourierCoeff_iwSymbolSet _ hPint hPs0).of_norm
  have hMs' : Summable (fun j : ℤ => ‖fourierCoeff
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
        (Work.Analysis.IonescuWainger.periodize m)) j‖) := hMs.norm
  have hPs' : Summable (fun j : ℤ => ‖fourierCoeff
      (Work.Analysis.IonescuWainger.iwSymbolSet (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
        (Work.Analysis.IonescuWainger.periodize φ)) j‖) := hPs.norm
  have Kaprod : ∀ p : ℤ, ∑' j : ℤ,
        fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet
          (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
          (Work.Analysis.IonescuWainger.periodize m)) j
          * fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet
              (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
              (Work.Analysis.IonescuWainger.periodize φ)) (p - j)
      = fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet
          (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
          (Work.Analysis.IonescuWainger.periodize φ)) p := by
    intro p
    rw [← Work.KMTAreas.A7.fourierCoeff_mul_l1 hSint hTint hFGint hMs hPs p]
    exact congrFun (fourierCoeff_congr_ae (Filter.Eventually.of_forall hgate)) p
  have hcomp : Work.Analysis.IWMultiplier.iwConv (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
      (Work.Analysis.IonescuWainger.periodize m) (Work.KMTAreas.A7.Tex ρ l φ f)
      = Work.KMTAreas.A7.Tex ρ l φ f := by
    funext n
    have hR : Work.KMTAreas.A7.Tex ρ l φ f n = ∑' j : ℤ,
        fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet
          (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
          (Work.Analysis.IonescuWainger.periodize φ)) j * f (n - j) := by
      rw [Work.KMTAreas.A7.Tex]
      exact Work.KMTAreas.A7.iwConv_eq_tsum_fourierCoeff _ _ _ _
    calc Work.Analysis.IWMultiplier.iwConv (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
          (Work.Analysis.IonescuWainger.periodize m) (Work.KMTAreas.A7.Tex ρ l φ f) n
        = ∑' j : ℤ, fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet
              (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
              (Work.Analysis.IonescuWainger.periodize m)) j
            * (Work.Analysis.IWMultiplier.iwConv (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
                (Work.Analysis.IonescuWainger.periodize φ) f) (n - j) :=
          Work.KMTAreas.A7.iwConv_eq_tsum_fourierCoeff _ _ _ _
      _ = ∑' j : ℤ, fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet
              (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
              (Work.Analysis.IonescuWainger.periodize m)) j
            * (∑' i : ℤ, fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet
                (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
                (Work.Analysis.IonescuWainger.periodize φ)) i
                * f (n - j - i)) :=
          tsum_congr (fun j => by rw [Work.KMTAreas.A7.iwConv_eq_tsum_fourierCoeff])
      _ = ∑' p : ℤ, (∑' j : ℤ,
              fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet
                (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
                (Work.Analysis.IonescuWainger.periodize m)) j
                * fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet
                    (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
                    (Work.Analysis.IonescuWainger.periodize φ)) (p - j))
            * f (n - p) :=
          Work.KMTAreas.A7.tsum_conv_conv
            (a := fun j : ℤ => fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet
                (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
                (Work.Analysis.IonescuWainger.periodize m)) j)
            (b := fun i : ℤ => fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet
                (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
                (Work.Analysis.IonescuWainger.periodize φ)) i)
            (u := f) (C := B) hMs' hPs' hB n
      _ = ∑' p : ℤ, fourierCoeff (Work.Analysis.IonescuWainger.iwSymbolSet
              (Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l)
              (Work.Analysis.IonescuWainger.periodize φ)) p
            * f (n - p) :=
          tsum_congr (fun p => by rw [Kaprod p])
      _ = Work.KMTAreas.A7.Tex ρ l φ f n := hR.symm
  exact hcomp

/-! ## The `l = 0` case -/

/-- For `l = 0` the exact-height frequency set is empty, so the fibre vanishes identically. -/
lemma fiberOp_zero_eq_zero (ρ : ℝ) (m : ℝ → ℂ) (u : ℤ → ℂ) :
    Work.KMTAreas.A7.fiberOp ρ 0 m 0 u = 0 := by
  have hA : Work.Analysis.IonescuWainger.iwArithFreqsNew ρ 0 = ∅ := by
    rw [Work.Analysis.IonescuWainger.iwArithFreqsNew]
    exact Finset.sdiff_self _
  funext x
  simp only [Work.KMTAreas.A7.fiberOp, hA, Finset.sum_empty, zero_mul, tsum_zero,
    Pi.zero_apply]

/-! ## The main theorem -/

theorem FiberOpCutFixGeneral (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ)
    (m' : ℝ → ℂ) (δ : ℝ) (hδ : 0 < δ)
    (hm'int : MeasureTheory.Integrable m')
    (hm'sum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw m' j‖))
    (hm'supp : ∀ θ : ℝ, 2 * δ < |θ| → m' θ = 0)
    (hm'one : ∀ θ : ℝ, |θ| ≤ δ → m' θ = 1)
    (hsep : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l,
      ∀ β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l, α ≠ β → 4 * δ ≤ ‖α - β‖)
    (φ : ℝ → ℂ) (hφ : MeasureTheory.Integrable φ)
    (hφsum : Summable (fun j : ℤ => ‖Work.KMTAreas.A7.cw φ j‖))
    (hφsupp : ∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ δ)
    (f : ℤ → ℂ) (hf : ∃ C : ℝ, ∀ x : ℤ, ‖f x‖ ≤ C) :
    Work.KMTAreas.A7.fiberOp ρ l m' 0 (Work.KMTAreas.A7.Tex ρ l φ f)
      = Work.KMTAreas.A7.Tex ρ l φ f := by
  by_cases hl : l = 0
  · subst hl
    rw [show Work.KMTAreas.A7.Tex ρ 0 φ f = Work.KMTAreas.A7.fiberOp ρ 0 φ 0 f from
      (Work.KMTAreas.A7.fiberOp_zero_eq_iwConv ρ 0 φ hφ f).symm]
    rw [fiberOp_zero_eq_zero ρ m' (Work.KMTAreas.A7.fiberOp ρ 0 φ 0 f),
      fiberOp_zero_eq_zero ρ φ f]
  · have hl1 : 1 ≤ l := Nat.one_le_iff_ne_zero.mpr hl
    have hδ8 : δ ≤ 1 / 8 := delta_le_eighth_of_sep ρ hρ hρ1 l hl1 δ hsep
    have hδ3 : δ < 1 / 3 := by linarith
    have hm'supp' : ∀ y : ℝ, m' y ≠ 0 → |y| ≤ 2 * δ := fun y hy => by
      by_contra hcon
      exact hy (hm'supp y (lt_of_not_ge hcon))
    have hm1' : ∀ ξ : Circ, ξ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ →
        Work.Analysis.IonescuWainger.periodize m' ξ = 1 :=
      fun ξ hξ => periodize_eq_one_of_support hδ hδ3 hm'supp hm'one hξ
    have hms' : ∀ ξ : Circ, Work.Analysis.IonescuWainger.periodize m' ξ ≠ 0 →
        ξ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 (2 * δ) :=
      fun ξ hξ => periodize_support_mem_arcSet hm'supp' hξ
    have hφpacket' : ∀ ξ : Circ, Work.Analysis.IonescuWainger.periodize φ ξ ≠ 0 →
        ξ ∈ Work.BourgainPlan.IonescuWainger.arcSet 0 δ :=
      fun ξ hξ => periodize_support_mem_arcSet hφsupp hξ
    have hna4 : ∀ α ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l,
        ∀ β ∈ Work.Analysis.IonescuWainger.iwArithFreqsNew ρ l, α ≠ β → 4 * δ ≤ ‖α - β‖ :=
      fun α hα β hβ hne =>
        hsep α (Finset.mem_sdiff.mp hα).1 β (Finset.mem_sdiff.mp hβ).1 hne
    rw [Work.KMTAreas.A7.fiberOp_zero_eq_iwConv ρ l m' hm'int (Work.KMTAreas.A7.Tex ρ l φ f)]
    exact iwConv_comp_plateau_four ρ l m' δ hδ hm'int hm'sum.of_norm hm1' hms' hna4 φ hφ
      hφsum.of_norm hφpacket' f hf

end

end Work.KMTAreas.A7Hi
