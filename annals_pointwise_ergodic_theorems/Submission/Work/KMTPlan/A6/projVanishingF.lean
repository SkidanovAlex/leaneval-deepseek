import Mathlib
import Submission.Work.KMTAreas.A7.Basic
import Submission.Work.KMTPlan.A6.iwConvEqIwOpSetMemlp
import Submission.Work.KMTPlan.A6.memlpOfMemLpCount
import Submission.Work.KMTPlan.A6.multiplierOfSub

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

/-- The circle `R/Z`, disambiguated from Mathlib's `Circle`. -/
abbrev Circle := Work.Analysis.IonescuWainger.Circle

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger
open Work.Analysis.IWMultiplier
open Work.KMTContract
open Work.Analysis.EndVar

noncomputable section

/-! ## Support of the periodisation, for an arbitrary set of reals -/

/-- If `phi` vanishes off a set `S` of reals, then so does its periodisation: a nonzero value of
`periodize phi xi` exhibits a real representative `theta` in `S` of `xi`. -/
theorem periodize_ne_zero {S : Set ℝ} {φ : ℝ → ℂ} (hφ : ∀ x, φ x ≠ 0 → x ∈ S)
    (hsum : ∀ x : ℝ, Summable fun j : ℤ => φ (x + j)) {ξ : Circle}
    (h : periodize φ ξ ≠ 0) : ∃ θ ∈ S, (θ : Circle) = ξ := by
  obtain ⟨j, hj⟩ : ∃ j : ℤ, φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + j) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine h ?_
    unfold periodize
    have h0 : (fun k : ℤ => φ ((AddCircle.equivIco (1 : ℝ) 0 ξ).val + k)) = fun _ : ℤ => (0 : ℂ) :=
      funext hcon
    rw [h0, tsum_zero]
  refine ⟨(AddCircle.equivIco (1 : ℝ) 0 ξ).val + j, hφ _ hj, ?_⟩
  have hxc : ((AddCircle.equivIco (1 : ℝ) 0 ξ).val : Circle) = ξ := by simp
  have hjc : ((j : ℝ) : Circle) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨j, by simp⟩
  rw [AddCircle.coe_add, hxc, hjc, add_zero]

/-! ## The annulus of the difference of two rescaled cutoffs -/

lemma etaCut_eq_one_of_le (a : ℤ) {x : ℝ} (h : |x| ≤ (2 : ℝ) ^ (a - 1)) :
    etaCut kmtEta a x = 1 := by
  rw [etaCut]
  refine kmtEta_one ?_
  have hpos : (0 : ℝ) < (2 : ℝ) ^ a := zpow_pos (by norm_num) a
  have hval : (2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ a = 1 / 2 := by
    rw [← zpow_sub₀ (show (2 : ℝ) ≠ 0 by norm_num) (a - 1) a,
      show (a - 1) - a = -1 by ring]
    norm_num
  calc |x / (2 : ℝ) ^ a| = |x| / (2 : ℝ) ^ a := by rw [abs_div, abs_of_pos hpos]
    _ ≤ (2 : ℝ) ^ (a - 1) / (2 : ℝ) ^ a := div_le_div_of_nonneg_right h (le_of_lt hpos)
    _ = 1 / 2 := hval

lemma etaCut_eq_zero_of_ge (a : ℤ) {x : ℝ} (h : (2 : ℝ) ^ a ≤ |x|) :
    etaCut kmtEta a x = 0 := by
  rw [etaCut]
  refine kmtEta_zero ?_
  have hpos : (0 : ℝ) < (2 : ℝ) ^ a := zpow_pos (by norm_num) a
  calc (1 : ℝ) ≤ |x| / (2 : ℝ) ^ a := by
        rw [one_le_div hpos]; exact h
    _ = |x / (2 : ℝ) ^ a| := by rw [abs_div, abs_of_pos hpos]

/-- The rescaled cutoffs at the scales `a` and `a - 1` are both `1` on `[-2^{a-2}, 2^{a-2}]` and
both `0` off `[-2^{a+1}, 2^{a+1}]`; hence their difference is supported in the annulus
`2^{a-2} < |x| ≤ 2^{a+1}`. -/
theorem etaCut_sub_support (a : ℤ) (x : ℝ)
    (h : etaCut kmtEta a x - etaCut kmtEta (a - 1) x ≠ 0) :
    (2 : ℝ) ^ (a - 2) < |x| ∧ |x| ≤ (2 : ℝ) ^ (a + 1) := by
  constructor
  · by_contra hx
    rw [not_lt] at hx
    refine h ?_
    have h1 : etaCut kmtEta a x = 1 := by
      refine etaCut_eq_one_of_le a ?_
      exact le_trans hx (zpow_le_zpow_right₀ (by norm_num) (by omega))
    have h2 : etaCut kmtEta (a - 1) x = 1 := by
      refine etaCut_eq_one_of_le (a - 1) ?_
      rw [show a - 1 - 1 = a - 2 by ring]
      exact hx
    rw [h1, h2, sub_self]
  · by_contra hx
    rw [not_le] at hx
    refine h ?_
    have h1 : etaCut kmtEta a x = 0 := by
      refine etaCut_eq_zero_of_ge a ?_
      exact le_trans (zpow_le_zpow_right₀ (by norm_num) (by omega : a ≤ a + 1)) (le_of_lt hx)
    have h2 : etaCut kmtEta (a - 1) x = 0 := by
      refine etaCut_eq_zero_of_ge (a - 1) ?_
      exact le_trans (zpow_le_zpow_right₀ (by norm_num) (by omega : a - 1 ≤ a + 1)) (le_of_lt hx)
    rw [h1, h2, sub_self]

/-! ## Monotonicity of the non-aliasing property -/

theorem NonAliasing.mono {k k' : ℤ} (hk : k ≤ k') {A B : Finset Circle} (hBA : B ⊆ A)
    (hA : NonAliasing k' A) : NonAliasing k B := by
  intro α hα β hβ θ hθ θ' hθ' heq
  exact hA α (hBA hα) β (hBA hβ) θ (realArc_mono hk hθ) θ' (realArc_mono hk hθ') heq

/-! ## Linear operations on the IW symbol -/

theorem iwSymbolSet_sub (A : Finset Circle) (Φ Ψ : Circle → ℂ) :
    iwSymbolSet A (Φ - Ψ) = iwSymbolSet A Φ - iwSymbolSet A Ψ := by
  funext ξ
  simp only [iwSymbolSet, Pi.sub_apply]
  rw [Finset.sum_sub_distrib]

/-! ## Vanishing of a product of IW symbols whose arcs are separated -/

/-- **Vanishing of a product of two IW symbols.**  Suppose that `Phi` is supported in the arc
`[-2^k, 2^k]`, that `Psi` is supported in the annulus `2^{k'-2} < |theta| ≤ 2^{k'+1}` (in the
sense that every nonzero value of `Psi` has such a representative), that the union of the
frequency sets `A ∪ B` is non-aliasing at the scale `K ≥ max k (k'+1)`, and that either
`A ∩ B = ∅` or `k + 2 ≤ k'`.  Then `iwSymbolSet B Phi * iwSymbolSet A Psi = 0`.

A nonzero term `Phi (xi - beta) * Psi (xi - alpha)` of the product exhibits representatives
`theta₁` in the arc and `theta₂` in the annulus, both of which lie in the arc of scale `K`, with
`alpha + theta₂ = beta + theta₁`; non-aliasing forces `alpha = beta` *and* `theta₂ = theta₁`.
If `A ∩ B = ∅` this is already a contradiction; otherwise `2^{k'-2} < |theta₂| = |theta₁| ≤ 2^k`
contradicts `k + 2 ≤ k'`. -/
theorem iwSymbolSet_mul_eq_zero {K k k' : ℤ} {A B : Finset Circle} {Φ Ψ : Circle → ℂ}
    (hNA : NonAliasing K (A ∪ B)) (hk : k ≤ K) (hk' : k' + 1 ≤ K)
    (hΦ : SupportedInArc k Φ)
    (hΨ : ∀ ζ : Circle, Ψ ζ ≠ 0 →
      ∃ θ : ℝ, (θ : Circle) = ζ ∧ (2 : ℝ) ^ (k' - 2) < |θ| ∧ |θ| ≤ (2 : ℝ) ^ (k' + 1))
    (hcase : (∀ α ∈ A, α ∉ B) ∨ k + 2 ≤ k') :
    iwSymbolSet B Φ * iwSymbolSet A Ψ = 0 := by
  funext ξ
  simp only [Pi.mul_apply, iwSymbolSet, Pi.zero_apply]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_eq_zero (fun β hβ => Finset.sum_eq_zero (fun α hα => ?_))
  by_contra hne
  obtain ⟨h1ne, h2ne⟩ := mul_ne_zero_iff.mp hne
  obtain ⟨θ₁, hθ₁, hθ₁eq⟩ := hΦ (ξ - β) h1ne
  obtain ⟨θ₂, hθ₂eq, hθ₂lo, hθ₂hi⟩ := hΨ (ξ - α) h2ne
  have hmem1 : θ₁ ∈ realArc K := realArc_mono hk hθ₁
  have hmem2 : θ₂ ∈ realArc K := by
    rw [realArc, Set.mem_Icc]
    obtain ⟨l, u⟩ := abs_le.mp hθ₂hi
    have hle : (2 : ℝ) ^ (k' + 1) ≤ (2 : ℝ) ^ K := zpow_le_zpow_right₀ (by norm_num) hk'
    exact ⟨by linarith, by linarith⟩
  have hsum : α + (θ₂ : Circle) = β + (θ₁ : Circle) := by
    rw [hθ₂eq, hθ₁eq]; abel
  obtain ⟨hαβ, hθθ⟩ :=
    hNA α (Finset.mem_union_left _ hα) β (Finset.mem_union_right _ hβ) θ₂ hmem2 θ₁ hmem1 hsum
  rcases hcase with hd | hk''
  · exact hd α hα (hαβ ▸ hβ)
  · have h2 : |θ₂| ≤ (2 : ℝ) ^ k := by rw [hθθ]; exact abs_le.mpr hθ₁
    have h3 : (2 : ℝ) ^ (k' - 2) < (2 : ℝ) ^ k := lt_of_lt_of_le hθ₂lo h2
    have h4 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ (k' - 2) :=
      zpow_le_zpow_right₀ (by norm_num) (by omega)
    linarith

/-! ## `L^inf`-membership and support of the periodised cutoffs -/

theorem memLp_periodize_etaCut (k : ℤ) :
    MemLp (periodize (etaCut kmtEta k)) ⊤ circleMeasure :=
  memLp_periodize (φ := etaCut kmtEta k) (Work.KMTAreas.A7.contDiff_etaCut k).continuous.measurable
    (R := (2 : ℝ) ^ k) (C := 1) (le_of_lt (zpow_pos (by norm_num) k))
    (fun x hx => Work.KMTAreas.A7.etaCut_eq_zero_of_le (k := k) (θ := x) (le_of_lt hx))
    (fun x => Work.KMTAreas.A7.norm_etaCut_le_one k x)

theorem supportedInArc_periodize_etaCut (k : ℤ) :
    SupportedInArc k (periodize (etaCut kmtEta k)) :=
  supportedInArc_periodize (fun _ hx => Work.KMTAreas.A7.etaCut_ne_zero_mem_realArc k hx)
    (Work.KMTAreas.A7.summable_etaCut_shift k)

theorem memLp_iwSymbolSet_etaCut (A : Finset Circle) (k : ℤ) :
    MemLp (iwSymbolSet A (periodize (etaCut kmtEta k))) ⊤ circleMeasure :=
  Work.Analysis.IWMultiplier.memLp_iwSymbolSet A (memLp_periodize_etaCut k)

/-! ## Additivity of the periodisation -/

theorem periodize_sub {φ ψ : ℝ → ℂ} (hφ : ∀ x : ℝ, Summable fun j : ℤ => φ (x + j))
    (hψ : ∀ x : ℝ, Summable fun j : ℤ => ψ (x + j)) :
    periodize (φ - ψ) = periodize φ - periodize ψ := by
  funext ξ
  simp only [periodize, Pi.sub_apply]
  rw [(hφ _).tsum_sub (hψ _)]

/-! ## Vanishing of a composition of two IW-type multipliers -/

theorem lp_smul_eq_zero {f g : Circle → ℂ} (hf : MemLp f ⊤ circleMeasure)
    (hg : MemLp g ⊤ circleMeasure) (hfg : ∀ ξ, f ξ * g ξ = 0) :
    hf.toLp f • hg.toLp g = 0 := by
  have h1 : hf.toLp f • hg.toLp g =ᵐ[circleMeasure] (fun _ : Circle => (0 : ℂ)) := by
    filter_upwards [Lp.coeFn_lpSMul (p := ⊤) (q := ⊤) (r := ⊤) (hf.toLp f) (hg.toLp g),
      MemLp.coeFn_toLp hf, MemLp.coeFn_toLp hg] with ξ h1 h2 h3
    simp only [h1, h2, h3, smul_eq_mul, Pi.mul_apply, hfg]
  exact Lp.ext (h1.trans (Lp.coeFn_zero ℂ ⊤ circleMeasure).symm)

theorem multiplier_zero_apply (F : L2Z) :
    multiplier (0 : Lp ℂ ⊤ circleMeasure) F = 0 := by
  have h := fourierZ_multiplier (0 : Lp ℂ ⊤ circleMeasure) F
  rw [Lp.zero_smul] at h
  have h2 : multiplier (0 : Lp ℂ ⊤ circleMeasure) F
      = fourierZ.symm (fourierZ (multiplier (0 : Lp ℂ ⊤ circleMeasure) F)) :=
    (fourierZ.symm_apply_apply _).symm
  rw [h2, h, map_zero]

theorem multiplier_comp_eq_zero {m m' : Lp ℂ ⊤ circleMeasure} (h : m • m' = 0) :
    (multiplier m).comp (multiplier m') = 0 := by
  ext F
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.zero_apply]
  rw [multiplier_comp, h, multiplier_zero_apply]

theorem multiplierOf_congr {f g : Circle → ℂ} (hf : MemLp f ⊤ circleMeasure)
    (hg : MemLp g ⊤ circleMeasure) (h : f = g) :
    multiplierOf f hf = multiplierOf g hg := by
  have htoLp : hf.toLp f = hg.toLp g :=
    MemLp.toLp_congr hf hg (Filter.Eventually.of_forall fun x => by rw [h])
  simp only [multiplierOf, htoLp]

/-! ## The projections as continuous linear maps on `l^2(Z)` -/

/-- The Ionescu--Wainger projection `Pi_{<=l,<=c}` of section 5 as a continuous linear map on
`l^2(Z)`, with the canonical boundedness proof of its symbol. -/
def projCLM (ρ : ℝ) (l : ℕ) (c : ℤ) : L2Z →L[ℂ] L2Z :=
  iwOpSet (iwArithFreqs ρ l) (periodize (etaCut kmtEta c))
    (memLp_iwSymbolSet_etaCut (iwArithFreqs ρ l) c)

/-- **The frequency set of the projection of exact height `l`**: `A_l \ A_{l-1}` for `l ≥ 1`, and
`A_0` for `l = 0`, where the projection `Pi_{0,<=c}` is not written as a difference. -/
def newFreqs (ρ : ℝ) (l : ℕ) : Finset Circle :=
  if l = 0 then iwArithFreqs ρ 0 else iwArithFreqs ρ l \ iwArithFreqs ρ (l - 1)

theorem newFreqs_subset (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l : ℕ) :
    newFreqs ρ l ⊆ iwArithFreqs ρ l := by
  unfold newFreqs
  by_cases hl : l = 0
  · rw [if_pos hl, hl]
  · rw [if_neg hl]; intro x hx; exact (Finset.mem_sdiff.mp hx).1

/-! ## Vanishing of the product of the outer symbol with the piece symbol -/

/-- **The piece symbol is annihilated by the outer symbol.**  Let `logN N = Log N`,
`Anew = newFreqs ρ l1`, and let `Psi = Phi_a - Phi_{a-1}` be the difference of the two rescaled
cutoffs at the scales `a = -Log N + k1` and `a - 1`.  Under the case hypothesis
`L < l1 or L + 2 <= k1`, the hypothesis `hw : max k1 L + 2 <= Log N` and the non-aliasing
hypothesis at the scale `max k1 L - Log N + 1` for the frequency set `A_{l1} ∪ A_L`, the product
of the symbol `iwSymbolSet A_L Phi_{kL}` of the outer projection with the symbol
`iwSymbolSet Anew Psi` of the piece vanishes identically. -/
theorem symbolVanishingF (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l₁ k₁ L N : ℕ)
    (hk₁ : 1 ≤ k₁) (hcase : L < l₁ ∨ L + 2 ≤ k₁)
    (hw : max (k₁ : ℤ) (L : ℤ) + 2 ≤ Work.Analysis.EndVar.logN N)
    (hNA : NonAliasing (max (k₁ : ℤ) (L : ℤ) - Work.Analysis.EndVar.logN N + 1)
      (iwArithFreqs ρ l₁ ∪ iwArithFreqs ρ L)) :
    iwSymbolSet (iwArithFreqs ρ L)
        (periodize (etaCut kmtEta (-(Work.Analysis.EndVar.logN N) + (L : ℤ))))
      * iwSymbolSet (newFreqs ρ l₁)
          (periodize (etaCut kmtEta (-(Work.Analysis.EndVar.logN N) + (k₁ : ℤ)))
            - periodize (etaCut kmtEta (-(Work.Analysis.EndVar.logN N) + (k₁ : ℤ) - 1))) = 0 := by
  set a : ℤ := -(Work.Analysis.EndVar.logN N) + (k₁ : ℤ) with ha
  set K : ℤ := max (k₁ : ℤ) (L : ℤ) - Work.Analysis.EndVar.logN N + 1 with hK
  have hle_κL : -(Work.Analysis.EndVar.logN N) + (L : ℤ) ≤ K := by rw [hK]; omega
  have hle_a : a + 1 ≤ K := by rw [hK, ha]; omega
  have hsupp : ∀ ζ : Circle,
      (periodize (etaCut kmtEta a) - periodize (etaCut kmtEta (a - 1))) ζ ≠ 0 →
      ∃ θ : ℝ, (θ : Circle) = ζ ∧ (2 : ℝ) ^ (a - 2) < |θ| ∧ |θ| ≤ (2 : ℝ) ^ (a + 1) := by
    intro ζ hζ
    have hsumm : ∀ x : ℝ, Summable fun j : ℤ =>
        (etaCut kmtEta a - etaCut kmtEta (a - 1)) (x + j) :=
      fun x => (Work.KMTAreas.A7.summable_etaCut_shift a x).sub
        (Work.KMTAreas.A7.summable_etaCut_shift (a - 1) x)
    have hζ' : periodize (etaCut kmtEta a - etaCut kmtEta (a - 1)) ζ ≠ 0 := by
      rw [periodize_sub (Work.KMTAreas.A7.summable_etaCut_shift a)
        (Work.KMTAreas.A7.summable_etaCut_shift (a - 1))]
      exact hζ
    obtain ⟨θ, hθS, hθeq⟩ := periodize_ne_zero
      (S := {x : ℝ | (2 : ℝ) ^ (a - 2) < |x| ∧ |x| ≤ (2 : ℝ) ^ (a + 1)})
      (φ := etaCut kmtEta a - etaCut kmtEta (a - 1))
      (fun x hx => etaCut_sub_support a x hx) hsumm (ξ := ζ) hζ'
    exact ⟨θ, hθeq, hθS.1, hθS.2⟩
  have hNAsub : NonAliasing K (newFreqs ρ l₁ ∪ iwArithFreqs ρ L) :=
    NonAliasing.mono le_rfl (fun x hx => by
      rcases Finset.mem_union.mp hx with h | h
      · exact Finset.mem_union_left _ (newFreqs_subset ρ hρ hρ1 l₁ h)
      · exact Finset.mem_union_right _ h) hNA
  have hcase' : (∀ α ∈ newFreqs ρ l₁, α ∉ iwArithFreqs ρ L)
      ∨ (-(Work.Analysis.EndVar.logN N) + (L : ℤ)) + 2 ≤ a := by
    rcases hcase with h | h
    · left
      intro α hα hαL
      have hl₁ : l₁ ≠ 0 := by omega
      have hL : L ≤ l₁ - 1 := by omega
      have hmem := Finset.mem_sdiff.mp (by rwa [newFreqs, if_neg hl₁] at hα)
      exact hmem.2 (iwArithFreqs_mono hρ hρ1 hL hαL)
    · right
      rw [ha]; omega
  exact iwSymbolSet_mul_eq_zero hNAsub hle_κL hle_a
    (supportedInArc_periodize_etaCut _) hsupp hcase'


/-! ## The vanishing of the outer projection applied to the piece -/

/-- The frequency set of the piece and its two symbols: the piece `F^{0,l₁,k₁}_N f` has symbol
`iwSymbolSet (newFreqs ρ l₁) Ψ` with `Ψ = Φ_a - Φ_b` the difference of the rescaled cutoffs at
the scales `a = -Log N + k₁` and `b = a - 1`. -/
theorem symbolVanishingF' (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l₁ k₁ L N : ℕ)
    (hk₁ : 1 ≤ k₁) (hcase : L < l₁ ∨ L + 2 ≤ k₁)
    (hw : max (k₁ : ℤ) (L : ℤ) + 2 ≤ Work.Analysis.EndVar.logN N)
    (hNA : NonAliasing (max (k₁ : ℤ) (L : ℤ) - Work.Analysis.EndVar.logN N + 1)
      (iwArithFreqs ρ l₁ ∪ iwArithFreqs ρ L)) :
    iwSymbolSet (iwArithFreqs ρ L)
        (periodize (etaCut kmtEta (-(Work.Analysis.EndVar.logN N) + (L : ℤ))))
      * iwSymbolSet (newFreqs ρ l₁)
          (periodize (etaCut kmtEta (-(Work.Analysis.EndVar.logN N) + (k₁ : ℤ)))
            - periodize (etaCut kmtEta (-(Work.Analysis.EndVar.logN N) + ((k₁ : ℤ) - 1)))) = 0 := by
  have h := symbolVanishingF ρ hρ hρ1 l₁ k₁ L N hk₁ hcase hw hNA
  rwa [show -(Work.Analysis.EndVar.logN N) + (k₁ : ℤ) - 1
      = -(Work.Analysis.EndVar.logN N) + ((k₁ : ℤ) - 1) by ring] at h

/-! ## The target -/

theorem projVanishingF (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (l₁ k₁ L N : ℕ) (f : ℤ → ℂ)
    (hk₁ : 1 ≤ k₁) (hcase : L < l₁ ∨ L + 2 ≤ k₁)
    (hw : max (k₁ : ℤ) (L : ℤ) + 2 ≤ Work.Analysis.EndVar.logN N)
    (hNA : Work.Analysis.IonescuWainger.NonAliasing
      (max (k₁ : ℤ) (L : ℤ) - Work.Analysis.EndVar.logN N + 1)
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ ∪ Work.Analysis.IonescuWainger.iwArithFreqs ρ L))
    (hf : MemLp f 2 Measure.count) :
    Work.KMTContract.kmtProj ρ L (-(Work.Analysis.EndVar.logN N) + (L : ℤ))
      (Work.Analysis.EndVar.Fpiece (Work.KMTContract.kmtPj ρ) 0 l₁ (k₁ : ℤ) N f) = 0 := by
  have hfℓ : Memℓp f 2 := memlpOfMemLpCount (by norm_num) (by norm_num) hf
  set F : L2Z := ⟨f, hfℓ⟩ with hFdef
  have hFcoe : ⇑F = f := rfl
  have hbr : ∀ (l : ℕ) (c : ℤ), kmtProj ρ l c f = ⇑(projCLM ρ l c F) := by
    intro l c
    rw [← hFcoe]
    exact iwConvEqIwOpSetMemlp (memLp_iwSymbolSet_etaCut (iwArithFreqs ρ l) c) F
  set a : ℤ := -(logN N) + (k₁ : ℤ) with ha
  set b : ℤ := -(logN N) + ((k₁ : ℤ) - 1) with hb
  set cL : ℤ := -(logN N) + (L : ℤ) with hcL
  have hpiece : Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) N f
      = piExact (kmtPj ρ) l₁ a f - piExact (kmtPj ρ) l₁ b f := by
    rw [Fpiece_eq, piece_of_ne (Pj := kmtPj ρ) (l := l₁) (κ := fun s => -(logN N) + s)
      (s := (k₁ : ℤ)) (f := f) (by simp only [Nat.cast_zero, neg_zero]; omega), ha, hb]
  have hsym := symbolVanishingF' ρ hρ hρ1 l₁ k₁ L N hk₁ hcase hw hNA
  set Ψ : Circle → ℂ := periodize (etaCut kmtEta a) - periodize (etaCut kmtEta b) with hΨdef
  have hΨmem : MemLp Ψ ⊤ circleMeasure :=
    (memLp_periodize_etaCut a).sub (memLp_periodize_etaCut b)
  rcases eq_or_ne l₁ 0 with hl₁ | hl₁
  · subst hl₁
    have hLk : L + 2 ≤ k₁ := by omega
    have hnew0 : newFreqs ρ 0 = iwArithFreqs ρ 0 := by unfold newFreqs; rw [if_pos rfl]
    have hdiffA : ∀ c : ℤ, projCLM ρ 0 c
        = multiplierOf (iwSymbolSet (newFreqs ρ 0) (periodize (etaCut kmtEta c)))
            (memLp_iwSymbolSet (newFreqs ρ 0) (memLp_periodize_etaCut c)) := by
      intro c
      rw [show projCLM ρ 0 c
          = multiplierOf (iwSymbolSet (iwArithFreqs ρ 0) (periodize (etaCut kmtEta c)))
              (memLp_iwSymbolSet_etaCut (iwArithFreqs ρ 0) c) from rfl]
      exact multiplierOf_congr _ _ (by rw [hnew0])
    have hT : projCLM ρ 0 a - projCLM ρ 0 b
        = multiplierOf (iwSymbolSet (newFreqs ρ 0) Ψ)
            (memLp_iwSymbolSet (newFreqs ρ 0) hΨmem) := by
      have h12 : MemLp (iwSymbolSet (newFreqs ρ 0) (periodize (etaCut kmtEta a))
          - iwSymbolSet (newFreqs ρ 0) (periodize (etaCut kmtEta b))) ⊤ circleMeasure :=
        (memLp_iwSymbolSet (newFreqs ρ 0) (memLp_periodize_etaCut a)).sub
          (memLp_iwSymbolSet (newFreqs ρ 0) (memLp_periodize_etaCut b))
      rw [hdiffA a, hdiffA b, ← multiplierOfSub _ _ h12]
      refine multiplierOf_congr h12 _ ?_
      rw [hΨdef, iwSymbolSet_sub]
    have hTF : Fpiece (kmtPj ρ) 0 0 (k₁ : ℤ) N f
        = ⇑((projCLM ρ 0 a - projCLM ρ 0 b) F) := by
      rw [hpiece, piExact, if_pos rfl, piExact, if_pos rfl]
      simp only [kmtPj_proj]
      rw [hbr 0 a, hbr 0 b]
      rfl
    have hkill : (projCLM ρ L cL).comp (multiplierOf (iwSymbolSet (newFreqs ρ 0) Ψ)
        (memLp_iwSymbolSet (newFreqs ρ 0) hΨmem)) = 0 := by
      have hsymA := hsym
      rw [hΨdef] at hsymA
      have hsl : ((memLp_iwSymbolSet_etaCut (iwArithFreqs ρ L) cL).toLp
            (iwSymbolSet (iwArithFreqs ρ L) (periodize (etaCut kmtEta cL))))
          • ((memLp_iwSymbolSet (newFreqs ρ 0) hΨmem).toLp
              (iwSymbolSet (newFreqs ρ 0) (periodize (etaCut kmtEta a)
                - periodize (etaCut kmtEta b)))) = 0 :=
        lp_smul_eq_zero _ _ (fun ξ => congrFun hsymA ξ)
      exact multiplier_comp_eq_zero hsl
    calc kmtProj ρ L cL (Fpiece (kmtPj ρ) 0 0 (k₁ : ℤ) N f)
        = iwConv (iwArithFreqs ρ L) (periodize (etaCut kmtEta cL))
            (⇑((projCLM ρ 0 a - projCLM ρ 0 b) F)) := by rw [hTF, kmtProj]
      _ = ⇑(projCLM ρ L cL ((projCLM ρ 0 a - projCLM ρ 0 b) F)) :=
            iwConvEqIwOpSetMemlp (memLp_iwSymbolSet_etaCut (iwArithFreqs ρ L) cL) _
      _ = ⇑((projCLM ρ L cL).comp (projCLM ρ 0 a - projCLM ρ 0 b) F) := rfl
      _ = ⇑((projCLM ρ L cL).comp (multiplierOf (iwSymbolSet (newFreqs ρ 0) Ψ)
              (memLp_iwSymbolSet (newFreqs ρ 0) hΨmem)) F) := by
            rw [hT]
      _ = 0 := by rw [hkill]; rfl
  · have hSdiff : ∀ c : ℤ, iwSymbolSet (iwArithFreqs ρ l₁) (periodize (etaCut kmtEta c))
          - iwSymbolSet (iwArithFreqs ρ (l₁ - 1)) (periodize (etaCut kmtEta c))
        = iwSymbolSet (newFreqs ρ l₁) (periodize (etaCut kmtEta c)) := by
      intro c
      have h1 : iwSymbolSet (iwArithFreqs ρ l₁) (periodize (etaCut kmtEta c))
          = iwSymbolSet (iwArithFreqs ρ (l₁ - 1)) (periodize (etaCut kmtEta c))
            + iwSymbolSet (iwArithFreqs ρ l₁ \ iwArithFreqs ρ (l₁ - 1))
              (periodize (etaCut kmtEta c)) :=
        iwSymbolSet_sdiff _ _ (iwArithFreqs_mono hρ hρ1 (Nat.pred_le l₁)) _
      have h2 : iwArithFreqs ρ l₁ \ iwArithFreqs ρ (l₁ - 1) = newFreqs ρ l₁ := by
        unfold newFreqs; rw [if_neg hl₁]
      rw [h1, h2]; abel
    have hdiff : ∀ c : ℤ, projCLM ρ l₁ c - projCLM ρ (l₁ - 1) c
        = multiplierOf (iwSymbolSet (newFreqs ρ l₁) (periodize (etaCut kmtEta c)))
            (memLp_iwSymbolSet (newFreqs ρ l₁) (memLp_periodize_etaCut c)) := by
      intro c
      have h12 : MemLp (iwSymbolSet (iwArithFreqs ρ l₁) (periodize (etaCut kmtEta c))
          - iwSymbolSet (iwArithFreqs ρ (l₁ - 1)) (periodize (etaCut kmtEta c)))
          ⊤ circleMeasure :=
        (memLp_iwSymbolSet_etaCut (iwArithFreqs ρ l₁) c).sub
          (memLp_iwSymbolSet_etaCut (iwArithFreqs ρ (l₁ - 1)) c)
      rw [show projCLM ρ l₁ c - projCLM ρ (l₁ - 1) c
            = multiplierOf (iwSymbolSet (iwArithFreqs ρ l₁) (periodize (etaCut kmtEta c)))
                (memLp_iwSymbolSet_etaCut (iwArithFreqs ρ l₁) c)
              - multiplierOf (iwSymbolSet (iwArithFreqs ρ (l₁ - 1)) (periodize (etaCut kmtEta c)))
                (memLp_iwSymbolSet_etaCut (iwArithFreqs ρ (l₁ - 1)) c) from rfl,
          ← multiplierOfSub _ _ h12]
      exact multiplierOf_congr h12 _ (hSdiff c)
    have hT : projCLM ρ l₁ a - projCLM ρ (l₁ - 1) a - (projCLM ρ l₁ b - projCLM ρ (l₁ - 1) b)
        = multiplierOf (iwSymbolSet (newFreqs ρ l₁) Ψ)
            (memLp_iwSymbolSet (newFreqs ρ l₁) hΨmem) := by
      have h12 : MemLp (iwSymbolSet (newFreqs ρ l₁) (periodize (etaCut kmtEta a))
          - iwSymbolSet (newFreqs ρ l₁) (periodize (etaCut kmtEta b))) ⊤ circleMeasure :=
        (memLp_iwSymbolSet (newFreqs ρ l₁) (memLp_periodize_etaCut a)).sub
          (memLp_iwSymbolSet (newFreqs ρ l₁) (memLp_periodize_etaCut b))
      rw [hdiff a, hdiff b, ← multiplierOfSub _ _ h12]
      refine multiplierOf_congr h12 _ ?_
      rw [hΨdef, iwSymbolSet_sub]
    have hTF : Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) N f
        = ⇑((projCLM ρ l₁ a - projCLM ρ (l₁ - 1) a
            - (projCLM ρ l₁ b - projCLM ρ (l₁ - 1) b)) F) := by
      rw [hpiece, piExact, if_neg hl₁, piExact, if_neg hl₁]
      simp only [kmtPj_proj]
      rw [hbr l₁ a, hbr (l₁ - 1) a, hbr l₁ b, hbr (l₁ - 1) b]
      rfl
    have hkill : (projCLM ρ L cL).comp (multiplierOf (iwSymbolSet (newFreqs ρ l₁) Ψ)
        (memLp_iwSymbolSet (newFreqs ρ l₁) hΨmem)) = 0 := by
      have hsl : ((memLp_iwSymbolSet_etaCut (iwArithFreqs ρ L) cL).toLp
            (iwSymbolSet (iwArithFreqs ρ L) (periodize (etaCut kmtEta cL))))
          • ((memLp_iwSymbolSet (newFreqs ρ l₁) hΨmem).toLp
              (iwSymbolSet (newFreqs ρ l₁) (periodize (etaCut kmtEta a)
                - periodize (etaCut kmtEta b)))) = 0 := by
        refine lp_smul_eq_zero _ _ (fun ξ => ?_)
        have h := congrFun hsym ξ
        rwa [hΨdef] at h
      show (multiplier ((memLp_iwSymbolSet_etaCut (iwArithFreqs ρ L) cL).toLp
        (iwSymbolSet (iwArithFreqs ρ L) (periodize (etaCut kmtEta cL))))).comp
          (multiplier ((memLp_iwSymbolSet (newFreqs ρ l₁) hΨmem).toLp
            (iwSymbolSet (newFreqs ρ l₁) Ψ))) = 0
      exact multiplier_comp_eq_zero hsl
    calc kmtProj ρ L cL (Fpiece (kmtPj ρ) 0 l₁ (k₁ : ℤ) N f)
        = iwConv (iwArithFreqs ρ L) (periodize (etaCut kmtEta cL))
            (⇑((projCLM ρ l₁ a - projCLM ρ (l₁ - 1) a
              - (projCLM ρ l₁ b - projCLM ρ (l₁ - 1) b)) F)) := by rw [hTF, kmtProj]
      _ = ⇑(projCLM ρ L cL ((projCLM ρ l₁ a - projCLM ρ (l₁ - 1) a
              - (projCLM ρ l₁ b - projCLM ρ (l₁ - 1) b)) F)) :=
            iwConvEqIwOpSetMemlp (memLp_iwSymbolSet_etaCut (iwArithFreqs ρ L) cL) _
      _ = ⇑((projCLM ρ L cL).comp (projCLM ρ l₁ a - projCLM ρ (l₁ - 1) a
              - (projCLM ρ l₁ b - projCLM ρ (l₁ - 1) b)) F) := rfl
      _ = ⇑((projCLM ρ L cL).comp (multiplierOf (iwSymbolSet (newFreqs ρ l₁) Ψ)
              (memLp_iwSymbolSet (newFreqs ρ l₁) hΨmem)) F) := by
            rw [hT]
      _ = 0 := by rw [hkill]; rfl

end

end Work.KMTPlan.A6
