/-
# The §6 collapse identity `symC - symM = symD` (Area A6)

This module proves `Work.KMTPlan.A6.symC_sub_symM_eq_symD`: the symbol of the *difference* of the
concrete clamped column and the model column is the fibre sum `symD` of the paper's `M₀`.

The structure of the proof is the paper's `mod-approx` collapse:

* the concrete symbol `symC` is, by Fourier inversion (`SymSeq_iwKernel_cont`), the product
  `(∑_{γ₁} Φ₁(·-γ₁))·(∑_{γ₂} Φ₂(·-γ₂))·avg` of the two periodised bumps with the discrete average
  `halfSym`, which unwinds (`periodizeCoeEqTsum`) into the fibre double sum over the aliasing
  representatives; the discrete average is invariant under the shift `-γ + m`
  (`weylAvg_shift_eq_halfSym`);
* the model symbol `symM` is the `t`-integral of the arithmetic symbol times the two modulated IW
  symbols; on each `t` the two modulated symbols collapse to their spike by non-aliasing
  (`symp_collapse_pointwise`), and the `t`-integral of the product of the modulated bumps is
  `mTilde` against the bumps (`integral_periodize_modulated_bumps`);
* the arithmetic symbol is Poisson-summated (`symSeq2_arithKerM_eq`) into the periodisations of the
  tensor windows;
* subtracting and using `M0 = weylAvg - mZ·mTilde` gives `symD`.

The four analytic inputs are the lemmas `symC_eq_fibre_sum`, `weylAvg_shift_eq_halfSym`,
`symSeq2_arithKerM_eq` and `integral_periodize_modulated_bumps`; the file first proves the
*assembly* `symC_sub_symM_eq_symD_assembly` from them, and then the target theorem.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.weylAvg_shift_eq_halfSym
import Submission.Work.KMTPlan.A6.mZ_period_eq
import Submission.Work.KMTAreas.A7.liftCollapse
import Submission.Work.KMTAreas.A7.FiberL2Defs

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform
open Work.Analysis.IonescuWainger
open Work.KMTAreas.A7

noncomputable section

local notation "Circ" => Work.Analysis.IonescuWainger.Circle

/-! ## 1. Elementary facts on the frequency arcs and non-aliasing -/

/-- The frequency arcs are monotone in the scale. -/
lemma symp_realArc_mono {k₁ k₂ : ℤ} (h : k₁ ≤ k₂) : realArc k₁ ⊆ realArc k₂ := by
  intro θ hθ
  rw [realArc, Set.mem_Icc] at hθ ⊢
  have hpow : (2 : ℝ) ^ k₁ ≤ (2 : ℝ) ^ k₂ := by
    rw [← Real.rpow_intCast, ← Real.rpow_intCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by exact_mod_cast h)
  constructor <;> linarith [hθ.1, hθ.2]

/-- Membership of `realArc k` gives `|θ| < 1/2` when `2^k < 1/2`. -/
lemma symp_abs_lt_half_of_mem_realArc {k : ℤ} {θ : ℝ} (hθ : θ ∈ realArc k)
    (hk : (2 : ℝ) ^ k < 1 / 2) : |θ| < 1 / 2 := by
  rw [realArc, Set.mem_Icc] at hθ
  rw [abs_lt]
  exact ⟨by linarith [hθ.1, hk], by linarith [hθ.2, hk]⟩

/-- Non-aliasing at a larger scale implies non-aliasing at a smaller one. -/
lemma symp_NonAliasing_of_le {k k' : ℤ} (h : k' ≤ k) {A : Finset Circ}
    (hNA : NonAliasing k A) : NonAliasing k' A :=
  fun α hα β hβ θ hθ θ' hθ' hEq =>
    hNA α hα β hβ θ (symp_realArc_mono h hθ) θ' (symp_realArc_mono h hθ') hEq

/-- Non-aliasing restricts to subsets. -/
lemma symp_NonAliasing_subset {k : ℤ} {A B : Finset Circ} (h : NonAliasing k B)
    (hAB : A ⊆ B) : NonAliasing k A :=
  fun α hα β hβ θ hθ θ' hθ' hEq => h α (hAB hα) β (hAB hβ) θ hθ θ' hθ' hEq

/-- The exact-height frequencies at level `l` are contained in `(ℚ/ℤ)_{≤l}`. -/
lemma symp_diffFreqs_subset (ρ : ℝ) (l : ℕ) : diffFreqs ρ l ⊆ iwArithFreqs ρ l := by
  rcases eq_or_ne l 0 with h | h
  · subst h
    rw [diffFreqs, if_pos rfl]
  · rw [diffFreqs, if_neg h]
    exact Finset.sdiff_subset

/-- The `[0,1)`-representative of an element of the circle is a representative. -/
lemma symp_gamR_coe (γ : Circ) : ((gamR γ : ℝ) : Circ) = γ := by
  rw [gamR]
  exact AddCircle.coe_equivIco

/-! ## 2. The pointwise diagonal collapse -/

/-- **The pointwise collapse of a window against a bump.**  Let `A` be non-aliasing at scale `k`,
let `Φ` be supported in `realArc kΦ`, `Ψ` in `realArc kΨ`, with `kΦ, kΨ ≤ k`, and let `Ψ ≡ 1` on
`realArc kΦ`.  Then for `α, β ∈ A` the product `Ψ (ξ - α) * Φ (ξ - β)` vanishes unless `α = β`,
where it is `Φ (ξ - β)`. -/
lemma symp_collapse_pointwise {A : Finset Circ} {kΦ kΨ k : ℤ} (hkΦ : kΦ ≤ k) (hkΨ : kΨ ≤ k)
    (hNA : NonAliasing k A) {Φ Ψ : Circ → ℂ} (hΦ : SupportedInArc kΦ Φ)
    (hΨ : SupportedInArc kΨ Ψ) (hflat : ∀ θ : ℝ, θ ∈ realArc kΦ → Ψ (θ : Circ) = 1)
    {α β : Circ} (hα : α ∈ A) (hβ : β ∈ A) (ξ : Circ) :
    Ψ (ξ - α) * Φ (ξ - β) = if β = α then Φ (ξ - β) else 0 := by
  by_cases h : β = α
  · rw [if_pos h]
    rcases eq_or_ne (Φ (ξ - β)) 0 with h0 | hne
    · rw [h0, mul_zero]
    · have h1 : Ψ (ξ - β) = 1 := by
        obtain ⟨θ, hθ, hθξ⟩ := hΦ (ξ - β) hne
        rw [← hθξ]
        exact hflat θ hθ
      rw [← h, h1, one_mul]
  · rw [if_neg h]
    by_contra hc
    obtain ⟨hΨne, hΦne⟩ := mul_ne_zero_iff.mp hc
    obtain ⟨θ₁, hθ₁, hθ₁ξ⟩ := hΨ (ξ - α) hΨne
    obtain ⟨θ₂, hθ₂, hθ₂ξ⟩ := hΦ (ξ - β) hΦne
    have e1 : α + ((θ₁ : ℝ) : Circ) = ξ := by rw [hθ₁ξ]; abel
    have e2 : β + ((θ₂ : ℝ) : Circ) = ξ := by rw [hθ₂ξ]; abel
    exact h (hNA α hα β hβ θ₁ (symp_realArc_mono hkΨ hθ₁) θ₂ (symp_realArc_mono hkΦ hθ₂)
      (e1.trans e2.symm)).1.symm

/-! ## 3. The collapse inside finite sums -/

/-- One variable of the collapse: a bump times a window-absorption. -/
lemma symp_mul_sum_eq_of_collapse {X : Finset Circ} {Ψ Φ : Circ → ℂ} {ξ : Circ}
    (h : ∀ α ∈ X, ∀ β ∈ X, Ψ (ξ - α) * Φ (ξ - β) = if β = α then Φ (ξ - β) else 0)
    {α : Circ} (hα : α ∈ X) :
    Ψ (ξ - α) * (∑ β ∈ X, Φ (ξ - β)) = Φ (ξ - α) := by
  rw [Finset.mul_sum]
  rw [Finset.sum_congr rfl fun β hβ => h α hα β hβ]
  rw [Finset.sum_ite_eq' X α (fun β => Φ (ξ - β)), if_pos hα]

/-- **The weighted collapse inside the finite sums of the model side.** -/
lemma symp_sum_collapse (X Y : Finset Circ) (c : Circ → Circ → ℂ) (Ψ₁ Φ₁ Ψ₂ Φ₂ : Circ → ℂ)
    (ξ η : Circ)
    (h₁ : ∀ α ∈ X, ∀ β ∈ X, Ψ₁ (ξ - α) * Φ₁ (ξ - β) = if β = α then Φ₁ (ξ - β) else 0)
    (h₂ : ∀ α ∈ Y, ∀ β ∈ Y, Ψ₂ (η - α) * Φ₂ (η - β) = if β = α then Φ₂ (η - β) else 0) :
    (∑ α₁ ∈ X, ∑ α₂ ∈ Y, c α₁ α₂ * Ψ₁ (ξ - α₁) * Ψ₂ (η - α₂))
        * (∑ β₁ ∈ X, Φ₁ (ξ - β₁)) * (∑ β₂ ∈ Y, Φ₂ (η - β₂))
      = ∑ β₁ ∈ X, ∑ β₂ ∈ Y, c β₁ β₂ * Φ₁ (ξ - β₁) * Φ₂ (η - β₂) := by
  have hstep : (∑ α₁ ∈ X, ∑ α₂ ∈ Y, c α₁ α₂ * Ψ₁ (ξ - α₁) * Ψ₂ (η - α₂))
        * (∑ β₁ ∈ X, Φ₁ (ξ - β₁)) * (∑ β₂ ∈ Y, Φ₂ (η - β₂))
      = ∑ α₁ ∈ X, ∑ α₂ ∈ Y, c α₁ α₂
          * (Ψ₁ (ξ - α₁) * (∑ β₁ ∈ X, Φ₁ (ξ - β₁)))
          * (Ψ₂ (η - α₂) * (∑ β₂ ∈ Y, Φ₂ (η - β₂))) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α₁ _ => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α₂ _ => ?_
    ring
  rw [hstep]
  have hinner : ∀ α₁ ∈ X, ∀ α₂ ∈ Y,
      c α₁ α₂ * (Ψ₁ (ξ - α₁) * (∑ β₁ ∈ X, Φ₁ (ξ - β₁)))
          * (Ψ₂ (η - α₂) * (∑ β₂ ∈ Y, Φ₂ (η - β₂)))
        = c α₁ α₂ * Φ₁ (ξ - α₁) * Φ₂ (η - α₂) := by
    intro α₁ hα₁ α₂ hα₂
    rw [symp_mul_sum_eq_of_collapse h₁ hα₁, symp_mul_sum_eq_of_collapse h₂ hα₂]
  rw [Finset.sum_congr rfl fun α₁ hα₁ => Finset.sum_congr rfl fun α₂ hα₂ => hinner α₁ hα₁ α₂ hα₂]


/-! ## 4. Support radii of the bumps (needed for the continuity in `t` of the integrand) -/

/-- `2^{-m} < 1/2` for every `m ≥ 2`. -/
lemma symp_rpow_neg_lt_half {m : ℤ} (hm : 2 ≤ m) : (2 : ℝ) ^ (-m) < 1 / 2 := by
  have h1 : (2 : ℝ) ^ (-m) ≤ (2 : ℝ) ^ (-(2 : ℤ)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_intCast]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have h2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    push_cast
    linarith
  have h2 : (2 : ℝ) ^ (-(2 : ℤ)) = 1 / 4 := by norm_num
  rw [h2] at h1
  linarith

/-- The canonical lift of a point of `[-1/2, 1/2)` is the point itself. -/
lemma symp_lift_coe_eq_self {θ : ℝ} (hθ : |θ| < 1 / 2) : lift ((θ : ℝ) : Circ) = θ := by
  by_cases h : 0 ≤ θ
  · exact Work.KMTAreas.A7.lift_eq_of_lt rfl h (abs_lt.mp hθ).2
  · have hmem : θ ∈ Set.Ico (-(1 / 2) : ℝ) (-(1 / 2) + 1) := by
      rw [Set.mem_Ico]
      exact ⟨le_of_lt (abs_lt.mp hθ).1, by linarith⟩
    have h := AddCircle.equivIco_coe_of_mem (p := (1 : ℝ)) (a := -(1 / 2)) (y := θ) hmem
    rw [lift]
    exact h

/-- From `|2^L ξ| < 1`, `|ξ| ≤ 2^{-L}` (integral exponents). -/
lemma symp_abs_le_zpow_of {L : ℤ} {ξ : ℝ} (h : |(2 : ℝ) ^ L * ξ| < 1) :
    |ξ| ≤ (2 : ℝ) ^ (-L) := by
  have h1 : |(2 : ℝ) ^ ((L : ℤ) : ℝ) * ξ| < 1 := by rwa [Real.rpow_intCast]
  have h2 := abs_le_of_rpow_mul_lt_one (L := (L : ℝ)) (k := 0) (by simpa using h1)
  rwa [show (2 : ℝ) ^ (((0 : ℕ) : ℝ) - (L : ℝ)) = (2 : ℝ) ^ (-L) by
        rw [show (((0 : ℕ) : ℝ) - (L : ℝ)) = ((-L : ℤ) : ℝ) by push_cast; ring,
          Real.rpow_intCast]] at h2

/-- **Support of `φ_N`**: radius at most `2^{-(2u+1)}` in the regime `k₁ + 2u + 1 ≤ Log N`. -/
lemma symp_varphiN_support_le (N k₁ u : ℕ)
    (h : k₁ + 2 * u + 1 ≤ (Work.Analysis.EndVar.logN N).toNat) :
    ∀ x : ℝ, varphiN N k₁ x ≠ 0 → |x| ≤ (2 : ℝ) ^ (-(2 * (u : ℤ) + 1)) := by
  intro x hx
  have h1 : ((k₁ : ℤ) + 2 * (u : ℤ) + 1) ≤ Work.Analysis.EndVar.logN N := by
    have h2 : ((k₁ + 2 * u + 1 : ℕ) : ℤ) ≤ ((Work.Analysis.EndVar.logN N).toNat : ℤ) := by
      exact_mod_cast h
    rw [Int.toNat_of_nonneg (by unfold Work.Analysis.EndVar.logN; exact Int.natCast_nonneg _)] at h2
    push_cast at h2
    linarith
  have h3 : (2 : ℝ) ^ ((k₁ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))
      ≤ (2 : ℝ) ^ ((-(2 * (u : ℤ) + 1) : ℤ) : ℝ) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have h4 : (k₁ : ℝ) + 2 * (u : ℝ) + 1 ≤ (Work.Analysis.EndVar.logN N : ℝ) := by
      exact_mod_cast h1
    push_cast
    linarith
  rw [Real.rpow_intCast] at h3
  exact le_trans (varphiN_support N k₁ x hx) h3

/-- **Support of `φ̃_N`**: radius at most `2^{d(k-Log N)}`. -/
lemma symp_varphitildeN_support (d N k : ℕ) (ξ : ℝ) (h : varphitildeN d N k ξ ≠ 0) :
    |ξ| ≤ (2 : ℝ) ^ ((d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := by
  have key : ∀ a : ℝ, Work.KMTContract.kmtEta ((2 : ℝ) ^ a * ξ) ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-a) := by
    intro a ha
    have hlt : ¬ (1 ≤ |(2 : ℝ) ^ a * ξ|) := fun hc => ha (Work.KMTContract.kmtEta_zero hc)
    have h1 : |(2 : ℝ) ^ a * ξ| < 1 := lt_of_not_ge hlt
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (by norm_num) _)] at h1
    have h2 := abs_le_of_rpow_mul_lt_one (L := a) (k := 0) (by simpa using h1)
    simpa only [Nat.cast_zero, zero_sub] using h2
  by_cases hk : k = 0
  · subst hk
    rw [varphitildeN, if_pos rfl] at h
    have h1 := key ((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ)) h
    calc |ξ| ≤ (2 : ℝ) ^ (-((d : ℝ) * (Work.Analysis.EndVar.logN N : ℝ))) := h1
      _ = (2 : ℝ) ^ ((d : ℝ) * (((0 : ℕ) : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := by
          congr 1
          push_cast
          ring
  · rw [varphitildeN, if_neg hk] at h
    have hbor : Work.KMTContract.kmtEta
          ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * ξ) ≠ 0
        ∨ Work.KMTContract.kmtEta
          ((2 : ℝ) ^ ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) * ξ) ≠ 0 := by
      by_contra hc
      push Not at hc
      exact h (by rw [hc.1, hc.2, sub_zero])
    rcases hbor with h1 | h1
    · have h2 := key ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) h1
      rwa [show -((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)))
          = (d : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) by ring] at h2
    · have h2 := key ((d : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ) + 1)) h1
      refine le_trans h2 ?_
      refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
      have hd0 : (0 : ℝ) ≤ (d : ℝ) := by positivity
      nlinarith

/-- **Support of `φ̃_N`**: radius at most `2^{-(2du+1)}` in the regime `k₂ + 2u + 1 ≤ Log N`
and `d ≥ 1`. -/
lemma symp_varphitildeN_support_le (d N k₂ u : ℕ) (hd : 1 ≤ d)
    (h : k₂ + 2 * u + 1 ≤ (Work.Analysis.EndVar.logN N).toNat) :
    ∀ x : ℝ, varphitildeN d N k₂ x ≠ 0 →
      |x| ≤ (2 : ℝ) ^ (-((d : ℤ) * 2 * (u : ℤ) + 1)) := by
  intro x hx
  have h1 : ((k₂ : ℤ) + 2 * (u : ℤ) + 1) ≤ Work.Analysis.EndVar.logN N := by
    have h2 : ((k₂ + 2 * u + 1 : ℕ) : ℤ) ≤ ((Work.Analysis.EndVar.logN N).toNat : ℤ) := by
      exact_mod_cast h
    rw [Int.toNat_of_nonneg (by unfold Work.Analysis.EndVar.logN; exact Int.natCast_nonneg _)] at h2
    push_cast at h2
    linarith
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h3 : (2 : ℝ) ^ ((d : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)))
      ≤ (2 : ℝ) ^ ((-((d : ℤ) * 2 * (u : ℤ) + 1) : ℤ) : ℝ) := by
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have h4 : (k₂ : ℝ) + 2 * (u : ℝ) + 1 ≤ (Work.Analysis.EndVar.logN N : ℝ) := by
      exact_mod_cast h1
    have hk : (k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ) ≤ -(2 * (u : ℝ) + 1) := by linarith
    have hstep : (d : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))
        ≤ (d : ℝ) * (-(2 * (u : ℝ) + 1)) := mul_le_mul_of_nonneg_left hk (by linarith)
    push_cast
    nlinarith [hstep]
  rw [Real.rpow_intCast] at h3
  exact le_trans (symp_varphitildeN_support d N k₂ x hx) h3

/-- `eeC` is continuous. -/
lemma symp_continuous_eeC : Continuous eeC := by unfold eeC; fun_prop

/-- **The integrand of the model side is continuous in `t`** (`φ`-factor). -/
lemma symp_continuous_periodize_varphiNt (N k₁ u : ℕ) (hu : 1 ≤ u)
    (h : k₁ + 2 * u + 1 ≤ (Work.Analysis.EndVar.logN N).toNat) (ξ : Circ) :
    Continuous fun t : ℝ => periodize (varphiNt N k₁ t) ξ := by
  have hw : (2 : ℝ) ^ (-(2 * (u : ℤ) + 1)) < 1 / 2 :=
    symp_rpow_neg_lt_half (by omega)
  have hφ := symp_varphiN_support_le N k₁ u h
  have hpt : ∀ t : ℝ, periodize (varphiNt N k₁ t) ξ
      = varphiN N k₁ (lift ξ) * eeC ((N : ℝ) * t * lift ξ) := by
    intro t
    show periodize (fun x : ℝ => varphiN N k₁ x * ee ((N : ℝ) * t * x)) ξ
      = varphiN N k₁ (lift ξ) * eeC ((N : ℝ) * t * lift ξ)
    exact periodize_mul_eq_lift (φ := varphiN N k₁)
      (f := fun x : ℝ => ee ((N : ℝ) * t * x)) hw hφ ξ
  rw [show (fun t : ℝ => periodize (varphiNt N k₁ t) ξ)
      = fun t : ℝ => varphiN N k₁ (lift ξ) * eeC ((N : ℝ) * t * lift ξ) from funext hpt]
  exact continuous_const.mul (symp_continuous_eeC.comp (by fun_prop))

/-- **The integrand of the model side is continuous in `t`** (`φ̃`-factor). -/
lemma symp_continuous_periodize_varphitildeNt (P : Polynomial ℤ) (d N k₂ u : ℕ) (hd : 1 ≤ d)
    (hu : 1 ≤ u) (h : k₂ + 2 * u + 1 ≤ (Work.Analysis.EndVar.logN N).toNat) (ξ : Circ) :
    Continuous fun t : ℝ => periodize (varphitildeNt P d N k₂ t) ξ := by
  have hw : (2 : ℝ) ^ (-((d : ℤ) * 2 * (u : ℤ) + 1)) < 1 / 2 := by
    refine symp_rpow_neg_lt_half ?_
    have hd1 : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
    have hu0 : (1 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu
    nlinarith
  have hφ := symp_varphitildeN_support_le d N k₂ u hd h
  have hcont : Continuous fun t : ℝ => PevalR P ((N : ℝ) * t) := by
    unfold PevalR
    exact (P.map (Int.castRingHom ℝ)).continuous.comp (by fun_prop)
  have hpt : ∀ t : ℝ, periodize (varphitildeNt P d N k₂ t) ξ
      = varphitildeN d N k₂ (lift ξ) * eeC (PevalR P ((N : ℝ) * t) * lift ξ) := by
    intro t
    show periodize (fun x : ℝ => varphitildeN d N k₂ x * ee (PevalR P ((N : ℝ) * t) * x)) ξ
      = varphitildeN d N k₂ (lift ξ) * eeC (PevalR P ((N : ℝ) * t) * lift ξ)
    exact periodize_mul_eq_lift (φ := varphitildeN d N k₂)
      (f := fun x : ℝ => ee (PevalR P ((N : ℝ) * t) * x)) hw hφ ξ
  rw [show (fun t : ℝ => periodize (varphitildeNt P d N k₂ t) ξ)
      = fun t : ℝ => varphitildeN d N k₂ (lift ξ) * eeC (PevalR P ((N : ℝ) * t) * lift ξ)
      from funext hpt]
  exact continuous_const.mul (symp_continuous_eeC.comp (hcont.mul continuous_const))

/-- **Interval integrability of the integrand of the model side.** -/
lemma symp_intervalIntegrable_periodize_mul (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree)
    (N k₁ k₂ u : ℕ) (hu : 1 ≤ u)
    (h₁ : k₁ + 2 * u + 1 ≤ (Work.Analysis.EndVar.logN N).toNat)
    (h₂ : k₂ + 2 * u + 1 ≤ (Work.Analysis.EndVar.logN N).toNat) (β₁ β₂ : Circ) :
    IntervalIntegrable (fun t : ℝ => periodize (varphiNt N k₁ t) β₁
        * periodize (varphitildeNt P P.natDegree N k₂ t) β₂) volume (1 / 2) 1 :=
  ((symp_continuous_periodize_varphiNt N k₁ u hu h₁ β₁).mul
    (symp_continuous_periodize_varphitildeNt P P.natDegree N k₂ u hd hu h₂ β₂)).intervalIntegrable _ _

/-- `uScale` is at least `1`. -/
lemma symp_one_le_uScale (ρ : ℝ) (hρ : 0 ≤ ρ) (L : ℕ) : 1 ≤ uScale ρ L := by
  rw [uScale, Work.Analysis.EndVar.scaleCount]
  have h1 : (1 : ℤ) ≤ ⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ := by
    rw [Int.le_floor]
    have h2 : (1 : ℝ) ≤ (2 : ℝ) ^ (2 * ρ * (L : ℝ)) := by
      rw [← Real.rpow_zero]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by positivity)
    simpa using h2
  have h3 : ((⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋).toNat : ℤ)
      = ⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋ :=
    Int.toNat_of_nonneg (le_trans zero_le_one h1)
  have h4 : (1 : ℤ) ≤ ((⌊(1 : ℝ) * (2 : ℝ) ^ (2 * ρ * (L : ℝ))⌋).toNat : ℤ) := by
    rw [h3]
    exact h1
  exact_mod_cast h4

/-! ## 4bis. The arcs of the periodised bumps and windows -/

/-- A periodisation of a narrow bump is supported in the corresponding arc. -/
lemma symp_supportedInArc_periodize {φ : ℝ → ℂ} {k : ℤ} {w : ℝ} (hw : w < 1 / 2)
    (hφ : ∀ x : ℝ, φ x ≠ 0 → |x| ≤ w) (hk : w ≤ (2 : ℝ) ^ k) :
    SupportedInArc k (periodize φ) := by
  intro ξ hξ
  rw [periodize_eq_lift hw hφ ξ] at hξ
  refine ⟨lift ξ, ?_, Work.KMTAreas.A7.lift_coe ξ⟩
  rw [realArc, Set.mem_Icc]
  have h := hφ _ hξ
  exact ⟨by linarith [neg_abs_le (lift ξ), h, hk], by linarith [le_abs_self (lift ξ), h, hk]⟩

/-- `2^{-2u} < 1/2` for `u ≥ 1`. -/
lemma symp_zpow_two_lt_half {u : ℕ} (hu : 1 ≤ u) : (2 : ℝ) ^ (-(2 * (u : ℤ))) < 1 / 2 := by
  have hle : (2 : ℝ) ^ (-(2 * (u : ℤ))) ≤ (2 : ℝ) ^ (-(2 : ℤ)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_intCast]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hu2 : (2 : ℝ) ≤ 2 * (u : ℝ) := by
      have : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
      linarith
    push_cast
    linarith
  have h2 : (2 : ℝ) ^ (-(2 : ℤ)) = 1 / 4 := by norm_num
  rw [h2] at hle
  linarith

/-- **Support of `mStarF u`**: the window is supported in `realArc (-(2u))`. -/
lemma symp_mStarF_support' (u : ℕ) :
    ∀ x : ℝ, mStarF u x ≠ 0 → |x| ≤ (2 : ℝ) ^ (-(2 * (u : ℤ))) := by
  intro x hx
  have hval : mStarF u x = Work.KMTContract.kmtEta ((2 : ℝ) ^ (2 * (u : ℤ)) * x) := by
    unfold mStarF
    rw [etaCut]
    rw [show (x / (2 : ℝ) ^ (-(2 * (u : ℤ)))) = (2 : ℝ) ^ (2 * (u : ℤ)) * x by
      rw [zpow_neg, div_inv_eq_mul, mul_comm]]
  rw [hval] at hx
  exact symp_abs_le_zpow_of (by
    have hlt : ¬ (1 ≤ |(2 : ℝ) ^ (2 * (u : ℤ)) * x|) := fun hc => hx (Work.KMTContract.kmtEta_zero hc)
    exact lt_of_not_ge hlt)

/-- **Flatness of `mStarF u`**: the window is `1` on `realArc (-(2u+1))`. -/
lemma symp_mStarF_eq_one' (u : ℕ) {θ : ℝ} (hθ : θ ∈ realArc (-(2 * (u : ℤ) + 1))) :
    mStarF u θ = 1 := by
  have hval : mStarF u θ = Work.KMTContract.kmtEta ((2 : ℝ) ^ (2 * (u : ℤ)) * θ) := by
    unfold mStarF
    rw [etaCut]
    rw [show (θ / (2 : ℝ) ^ (-(2 * (u : ℤ)))) = (2 : ℝ) ^ (2 * (u : ℤ)) * θ by
      rw [zpow_neg, div_inv_eq_mul, mul_comm]]
  rw [hval]
  refine Work.KMTContract.kmtEta_one ?_
  have h2 : (2 : ℝ) ^ (-(2 * (u : ℤ) + 1)) = ((2 : ℝ) ^ (2 * (u : ℤ)))⁻¹ / 2 := by
    rw [show (-(2 * (u : ℤ) + 1)) = -(2 * (u : ℤ)) + (-1) by ring, zpow_add₀ (by norm_num),
      zpow_neg, zpow_neg, zpow_one, div_eq_mul_inv]
  rw [realArc, Set.mem_Icc] at hθ
  rw [h2] at hθ
  have hp : (0 : ℝ) < (2 : ℝ) ^ (2 * (u : ℤ)) := zpow_pos (by norm_num) _
  rw [abs_mul, abs_of_pos hp]
  have hθabs : |θ| ≤ ((2 : ℝ) ^ (2 * (u : ℤ)))⁻¹ / 2 := abs_le.mpr ⟨hθ.1, hθ.2⟩
  calc (2 : ℝ) ^ (2 * (u : ℤ)) * |θ|
      ≤ (2 : ℝ) ^ (2 * (u : ℤ)) * (((2 : ℝ) ^ (2 * (u : ℤ)))⁻¹ / 2) :=
        mul_le_mul_of_nonneg_left hθabs hp.le
    _ = 1 / 2 := by field_simp

/-- `periodize (mStarF u)` is `1` on `realArc (-(2u+1))`. -/
lemma symp_periodize_mStarF_eq_one (u : ℕ) (hu : 1 ≤ u) {θ : ℝ}
    (hθ : θ ∈ realArc (-(2 * (u : ℤ) + 1))) : periodize (mStarF u) (θ : Circ) = 1 := by
  rw [periodize_eq_lift (symp_zpow_two_lt_half hu) (symp_mStarF_support' u) (θ : Circ)]
  rw [symp_lift_coe_eq_self (θ := θ) (by
    have h1 : (2 : ℝ) ^ (-(2 * (u : ℤ) + 1)) < 1 / 2 := symp_rpow_neg_lt_half (by omega)
    exact symp_abs_lt_half_of_mem_realArc hθ h1)]
  exact symp_mStarF_eq_one' u hθ

/-- **Support of `mStargF d u`**: the window is supported in `realArc (-(2du))`. -/
lemma symp_mStargF_support' (d u : ℕ) :
    ∀ x : ℝ, mStargF d u x ≠ 0 → |x| ≤ (2 : ℝ) ^ (-((d : ℤ) * 2 * (u : ℤ))) := by
  intro x hx
  have hval : mStargF d u x = Work.KMTContract.kmtEta ((2 : ℝ) ^ ((d : ℤ) * 2 * (u : ℤ)) * x) := by
    unfold mStargF
    rw [etaCut]
    rw [show (x / (2 : ℝ) ^ (-((d : ℤ) * 2 * (u : ℤ))))
        = (2 : ℝ) ^ ((d : ℤ) * 2 * (u : ℤ)) * x by rw [zpow_neg, div_inv_eq_mul, mul_comm]]
  rw [hval] at hx
  exact symp_abs_le_zpow_of (by
    have hlt : ¬ (1 ≤ |(2 : ℝ) ^ ((d : ℤ) * 2 * (u : ℤ)) * x|) :=
      fun hc => hx (Work.KMTContract.kmtEta_zero hc)
    exact lt_of_not_ge hlt)

/-- **Flatness of `mStargF d u`**: the window is `1` on `realArc (-(2du+1))`. -/
lemma symp_mStargF_eq_one' (d u : ℕ) {θ : ℝ}
    (hθ : θ ∈ realArc (-((d : ℤ) * 2 * (u : ℤ) + 1))) : mStargF d u θ = 1 := by
  have hval : mStargF d u θ = Work.KMTContract.kmtEta ((2 : ℝ) ^ ((d : ℤ) * 2 * (u : ℤ)) * θ) := by
    unfold mStargF
    rw [etaCut]
    rw [show (θ / (2 : ℝ) ^ (-((d : ℤ) * 2 * (u : ℤ))))
        = (2 : ℝ) ^ ((d : ℤ) * 2 * (u : ℤ)) * θ by rw [zpow_neg, div_inv_eq_mul, mul_comm]]
  rw [hval]
  refine Work.KMTContract.kmtEta_one ?_
  have h2 : (2 : ℝ) ^ (-((d : ℤ) * 2 * (u : ℤ) + 1))
      = ((2 : ℝ) ^ ((d : ℤ) * 2 * (u : ℤ)))⁻¹ / 2 := by
    rw [show (-((d : ℤ) * 2 * (u : ℤ) + 1)) = -((d : ℤ) * 2 * (u : ℤ)) + (-1) by ring,
      zpow_add₀ (by norm_num), zpow_neg, zpow_neg, zpow_one, div_eq_mul_inv]
  rw [realArc, Set.mem_Icc] at hθ
  rw [h2] at hθ
  have hp : (0 : ℝ) < (2 : ℝ) ^ ((d : ℤ) * 2 * (u : ℤ)) := zpow_pos (by norm_num) _
  rw [abs_mul, abs_of_pos hp]
  have hθabs : |θ| ≤ ((2 : ℝ) ^ ((d : ℤ) * 2 * (u : ℤ)))⁻¹ / 2 := abs_le.mpr ⟨hθ.1, hθ.2⟩
  calc (2 : ℝ) ^ ((d : ℤ) * 2 * (u : ℤ)) * |θ|
      ≤ (2 : ℝ) ^ ((d : ℤ) * 2 * (u : ℤ)) * (((2 : ℝ) ^ ((d : ℤ) * 2 * (u : ℤ)))⁻¹ / 2) :=
        mul_le_mul_of_nonneg_left hθabs hp.le
    _ = 1 / 2 := by field_simp

/-- `2^{-2du} < 1/2` for `d ≥ 1`, `u ≥ 1`. -/
lemma symp_zpow_two_d_lt_half {d u : ℕ} (hd : 1 ≤ d) (hu : 1 ≤ u) :
    (2 : ℝ) ^ (-((d : ℤ) * 2 * (u : ℤ))) < 1 / 2 := by
  have hle : (2 : ℝ) ^ (-((d : ℤ) * 2 * (u : ℤ))) ≤ (2 : ℝ) ^ (-(2 : ℤ)) := by
    rw [← Real.rpow_intCast, ← Real.rpow_intCast]
    refine Real.rpow_le_rpow_of_exponent_le (by norm_num) ?_
    have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
    have huR : (1 : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu
    push_cast
    nlinarith
  have h2 : (2 : ℝ) ^ (-(2 : ℤ)) = 1 / 4 := by norm_num
  rw [h2] at hle
  linarith

/-- `periodize (mStargF d u)` is `1` on `realArc (-(2du+1))`. -/
lemma symp_periodize_mStargF_eq_one (d u : ℕ) (hd : 1 ≤ d) (hu : 1 ≤ u) {θ : ℝ}
    (hθ : θ ∈ realArc (-((d : ℤ) * 2 * (u : ℤ) + 1))) :
    periodize (mStargF d u) (θ : Circ) = 1 := by
  rw [periodize_eq_lift (symp_zpow_two_d_lt_half hd hu) (symp_mStargF_support' d u) (θ : Circ)]
  rw [symp_lift_coe_eq_self (θ := θ) (by
    have h1 : (2 : ℝ) ^ (-((d : ℤ) * 2 * (u : ℤ) + 1)) < 1 / 2 := by
      refine symp_rpow_neg_lt_half ?_
      have hd1 : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
      have hu1 : (1 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu
      nlinarith
    exact symp_abs_lt_half_of_mem_realArc hθ h1)]
  exact symp_mStargF_eq_one' d u hθ

/-- `periodize (varphiNt N k₁ t)` is supported in `realArc (-(2u+1))`. -/
lemma symp_supportedInArc_periodize_varphiNt (N k₁ u : ℕ) (hu : 1 ≤ u)
    (h : k₁ + 2 * u + 1 ≤ (Work.Analysis.EndVar.logN N).toNat) (t : ℝ) :
    SupportedInArc (-(2 * (u : ℤ) + 1)) (periodize (varphiNt N k₁ t)) :=
  symp_supportedInArc_periodize (symp_rpow_neg_lt_half (by omega))
    (fun x hx => symp_varphiN_support_le N k₁ u h x (fun h0 => hx (by simp [varphiNt, h0])))
    le_rfl

/-- `periodize (varphitildeNt P d N k₂ t)` is supported in `realArc (-(2du+1))`. -/
lemma symp_supportedInArc_periodize_varphitildeNt (P : Polynomial ℤ) (d N k₂ u : ℕ)
    (hd : 1 ≤ d) (hu : 1 ≤ u)
    (h : k₂ + 2 * u + 1 ≤ (Work.Analysis.EndVar.logN N).toNat) (t : ℝ) :
    SupportedInArc (-((d : ℤ) * 2 * (u : ℤ) + 1)) (periodize (varphitildeNt P d N k₂ t)) :=
  symp_supportedInArc_periodize (symp_rpow_neg_lt_half (by
      have hd1 : (1 : ℤ) ≤ (d : ℤ) := by exact_mod_cast hd
      have hu1 : (1 : ℤ) ≤ (u : ℤ) := by exact_mod_cast hu
      nlinarith))
    (fun x hx => symp_varphitildeN_support_le d N k₂ u hd h x
      (fun h0 => hx (by simp [varphitildeNt, h0])))
    le_rfl

/-! ## 5. The arithmetic modulus `perQ` against `arithQ`, and `mZ` -/

/-- The fibre period `perQ γ₁ γ₂` divides the common denominator `arithQ ρ (max l₁ l₂)`. -/
lemma symp_perQ_dvd_arithQ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) {l₁ l₂ : ℕ}
    {γ₁ γ₂ : Circ} (h₁ : γ₁ ∈ diffFreqs ρ l₁) (h₂ : γ₂ ∈ diffFreqs ρ l₂) :
    perQ γ₁ γ₂ ∣ arithQ ρ (max l₁ l₂) := by
  have hm₁ : γ₁ ∈ iwArithFreqs ρ (max l₁ l₂) :=
    iwArithFreqs_mono hρ hρ1 (le_max_left l₁ l₂) (symp_diffFreqs_subset ρ l₁ h₁)
  have hm₂ : γ₂ ∈ iwArithFreqs ρ (max l₁ l₂) :=
    iwArithFreqs_mono hρ hρ1 (le_max_right l₁ l₂) (symp_diffFreqs_subset ρ l₂ h₂)
  refine Nat.lcm_dvd ?_ ?_
  · exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr (arithQ_nsmul_eq_zero hm₁)
  · exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr (arithQ_nsmul_eq_zero hm₂)

/-- **`mZ` is independent of the choice of the (killing) modulus.** -/
lemma symp_mZ_eq_perQ (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (P : Polynomial ℤ) (l₁ l₂ : ℕ)
    {γ₁ γ₂ : Circ} (h₁ : γ₁ ∈ diffFreqs ρ l₁) (h₂ : γ₂ ∈ diffFreqs ρ l₂) :
    mZ P (arithQ ρ (max l₁ l₂)) γ₁ γ₂ = mZ P (perQ γ₁ γ₂) γ₁ γ₂ := by
  have hdvd := symp_perQ_dvd_arithQ ρ hρ hρ1 h₁ h₂
  have hq : 0 < arithQ ρ (max l₁ l₂) := arithQ_pos ρ (max l₁ l₂)
  have hq' : 0 < perQ γ₁ γ₂ := Nat.pos_of_dvd_of_pos hdvd hq
  have hm₁ : γ₁ ∈ iwArithFreqs ρ (max l₁ l₂) :=
    iwArithFreqs_mono hρ hρ1 (le_max_left l₁ l₂) (symp_diffFreqs_subset ρ l₁ h₁)
  have hm₂ : γ₂ ∈ iwArithFreqs ρ (max l₁ l₂) :=
    iwArithFreqs_mono hρ hρ1 (le_max_right l₁ l₂) (symp_diffFreqs_subset ρ l₂ h₂)
  refine mZ_period_eq P hq hq' (arithQ_nsmul_eq_zero hm₁) (arithQ_nsmul_eq_zero hm₂) ?_ ?_
  · exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (Nat.dvd_lcm_left _ _)
  · exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (Nat.dvd_lcm_right _ _)

/-! ## 6. Norm bounds for the factors of the fibre terms -/

/-- `‖mTilde P N ξ₁ ξ₂‖ ≤ 1`. -/
lemma symp_norm_mTilde_le_one (P : Polynomial ℤ) (N : ℕ) (ξ₁ ξ₂ : ℝ) :
    ‖mTilde P N ξ₁ ξ₂‖ ≤ 1 := by
  rw [mTilde]
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := (1 / 2 : ℝ)) (b := 1) (C := 1)
    (f := fun t : ℝ => ee (ξ₁ * (N : ℝ) * t + ξ₂ * PevalR P ((N : ℝ) * t)))
    (fun t _ => by rw [norm_ee])
  have h2 : (1 : ℝ) * |1 - 1 / 2| ≤ 1 := by norm_num
  linarith

/-- `‖mZ P q γ₁ γ₂‖ ≤ 1`. -/
lemma symp_norm_mZ_le_one (P : Polynomial ℤ) (q : ℕ) (γ₁ γ₂ : Circ) :
    ‖mZ P q γ₁ γ₂‖ ≤ 1 := by
  rcases eq_or_ne q 0 with hq | hq
  · subst hq; simp [mZ]
  · rw [mZ, norm_mul]
    have h1 : ‖∑ n ∈ Finset.range q, fourier (T := 1) (n : ℤ) γ₁ * fourier (T := 1) (P.eval (n : ℤ)) γ₂‖
        ≤ (q : ℝ) := by
      calc ‖∑ n ∈ Finset.range q, fourier (T := 1) (n : ℤ) γ₁ * fourier (T := 1) (P.eval (n : ℤ)) γ₂‖
          ≤ ∑ n ∈ Finset.range q, ‖fourier (T := 1) (n : ℤ) γ₁ * fourier (T := 1) (P.eval (n : ℤ)) γ₂‖ :=
            norm_sum_le _ _
        _ = (q : ℝ) := by
            rw [Finset.sum_congr rfl (fun n _ => by rw [norm_mul, norm_fourier_one, norm_fourier_one, mul_one])]
            simp
    have h2 : ‖((q : ℂ))⁻¹‖ = (q : ℝ)⁻¹ := by rw [norm_inv, Complex.norm_natCast]
    rw [h2]
    calc (q : ℝ)⁻¹ * ‖∑ n ∈ Finset.range q, fourier (T := 1) (n : ℤ) γ₁ * fourier (T := 1) (P.eval (n : ℤ)) γ₂‖
        ≤ (q : ℝ)⁻¹ * (q : ℝ) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 1 := by field_simp

/-- `‖weylAvg P N γ₁ γ₂ ξ₁ ξ₂‖ ≤ 2` for `N ≥ 1`. -/
lemma symp_norm_weylAvg_le_two (P : Polynomial ℤ) (N : ℕ) (hN : 1 ≤ N)
    (γ₁ γ₂ : Circ) (ξ₁ ξ₂ : ℝ) : ‖weylAvg P N γ₁ γ₂ ξ₁ ξ₂‖ ≤ 2 := by
  rw [weylAvg, norm_mul]
  have h1 : ‖∑ n ∈ Finset.Ioc (N / 2) N, momPhase P N γ₁ γ₂ ξ₁ ξ₂ (n : ℤ)‖ ≤ (N : ℝ) + 1 := by
    calc ‖∑ n ∈ Finset.Ioc (N / 2) N, momPhase P N γ₁ γ₂ ξ₁ ξ₂ (n : ℤ)‖
        ≤ ∑ n ∈ Finset.Ioc (N / 2) N, ‖momPhase P N γ₁ γ₂ ξ₁ ξ₂ (n : ℤ)‖ := norm_sum_le _ _
      _ = ((Finset.Ioc (N / 2) N).card : ℝ) := by
          have hterm : ∀ n : ℕ, ‖momPhase P N γ₁ γ₂ ξ₁ ξ₂ (n : ℤ)‖ = 1 := by
            intro n
            rw [momPhase, norm_mul, norm_mul, norm_fourier_one, norm_fourier_one, norm_ee,
              mul_one, mul_one]
          rw [Finset.sum_congr rfl (fun n _ => hterm n)]
          simp
      _ ≤ (N : ℝ) + 1 := by
          have hcard : (Finset.Ioc (N / 2) N).card ≤ (Finset.range (N + 1)).card :=
            Finset.card_le_card fun x hx =>
              Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_Ioc.mp hx).2)
          calc ((Finset.Ioc (N / 2) N).card : ℝ)
              ≤ ((Finset.range (N + 1)).card : ℝ) := by exact_mod_cast hcard
            _ = (N : ℝ) + 1 := by simp
  have h2 : ‖((N : ℂ))⁻¹‖ = (N : ℝ)⁻¹ := by rw [norm_inv, Complex.norm_natCast]
  rw [h2]
  have h3 : (N : ℝ)⁻¹ * ((N : ℝ) + 1) ≤ 2 := by
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hinv : (N : ℝ)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ hN0]
      exact_mod_cast hN
    have hsplit : (N : ℝ)⁻¹ * ((N : ℝ) + 1) = 1 + (N : ℝ)⁻¹ := by field_simp
    rw [hsplit]
    linarith
  calc (N : ℝ)⁻¹ * ‖∑ n ∈ Finset.Ioc (N / 2) N, momPhase P N γ₁ γ₂ ξ₁ ξ₂ (n : ℤ)‖
      ≤ (N : ℝ)⁻¹ * ((N : ℝ) + 1) := by
        refine mul_le_mul_of_nonneg_left h1 ?_
        positivity
    _ ≤ 2 := h3

/-! ## 7. The double-`tsum` difference and the sequence-symbol dictionary -/

/-- **The difference of two double `tsum`s is the double `tsum` of the differences**, with the
summability verified through two summable majorants `φ`, `ψ` (one for each variable). -/
lemma symp_tsum_tsum_sub_of_bound {a b : ℤ → ℤ → ℂ} {φ ψ : ℤ → ℝ}
    (hφ : Summable φ) (hψ : Summable ψ)
    (ha : ∀ m₁ m₂ : ℤ, ‖a m₁ m₂‖ ≤ φ m₁ * ψ m₂)
    (hb : ∀ m₁ m₂ : ℤ, ‖b m₁ m₂‖ ≤ φ m₁ * ψ m₂) :
    (∑' m₁ : ℤ, ∑' m₂ : ℤ, a m₁ m₂) - (∑' m₁ : ℤ, ∑' m₂ : ℤ, b m₁ m₂)
      = ∑' m₁ : ℤ, ∑' m₂ : ℤ, (a m₁ m₂ - b m₁ m₂) := by
  have hA : ∀ m₁ : ℤ, Summable fun m₂ : ℤ => a m₁ m₂ := fun m₁ =>
    Summable.of_norm_bounded (hψ.mul_left (φ m₁)) (fun m₂ => ha m₁ m₂)
  have hB : ∀ m₁ : ℤ, Summable fun m₂ : ℤ => b m₁ m₂ := fun m₁ =>
    Summable.of_norm_bounded (hψ.mul_left (φ m₁)) (fun m₂ => hb m₁ m₂)
  have hAsum : Summable fun m₁ : ℤ => ∑' m₂ : ℤ, a m₁ m₂ := by
    refine Summable.of_norm_bounded (g := fun m₁ : ℤ => φ m₁ * (∑' m₂ : ℤ, ψ m₂))
      (hφ.mul_right _) (fun m₁ => ?_)
    calc ‖∑' m₂ : ℤ, a m₁ m₂‖ ≤ ∑' m₂ : ℤ, ‖a m₁ m₂‖ := norm_tsum_le_tsum_norm (hA m₁).norm
      _ ≤ ∑' m₂ : ℤ, φ m₁ * ψ m₂ :=
          (hA m₁).norm.tsum_le_tsum (fun m₂ => ha m₁ m₂) (hψ.mul_left (φ m₁))
      _ = φ m₁ * ∑' m₂ : ℤ, ψ m₂ := tsum_mul_left
  have hBsum : Summable fun m₁ : ℤ => ∑' m₂ : ℤ, b m₁ m₂ := by
    refine Summable.of_norm_bounded (g := fun m₁ : ℤ => φ m₁ * (∑' m₂ : ℤ, ψ m₂))
      (hφ.mul_right _) (fun m₁ => ?_)
    calc ‖∑' m₂ : ℤ, b m₁ m₂‖ ≤ ∑' m₂ : ℤ, ‖b m₁ m₂‖ := norm_tsum_le_tsum_norm (hB m₁).norm
      _ ≤ ∑' m₂ : ℤ, φ m₁ * ψ m₂ :=
          (hB m₁).norm.tsum_le_tsum (fun m₂ => hb m₁ m₂) (hψ.mul_left (φ m₁))
      _ = φ m₁ * ∑' m₂ : ℤ, ψ m₂ := tsum_mul_left
  rw [← hAsum.tsum_sub hBsum]
  refine tsum_congr fun m₁ => ?_
  exact ((hA m₁).tsum_sub (hB m₁)).symm

/-- Fourier inversion for the exact-height IW multiplier: the sequence symbol of `tmKer ρ l φ` is
the IW symbol of the periodisation of `φ` (`SymSeq_iwKernel_cont`). -/
lemma symp_symSeq_tmKer_eq (ρ : ℝ) (l : ℕ) (φ : ℝ → ℂ) (hφ : Integrable φ)
    (hper : Continuous (periodize φ)) (hsum : Summable fun p : ℤ => ‖cw φ p‖) (x : ℝ) :
    symSeq (tmKer ρ l φ) x = ∑ γ ∈ diffFreqs ρ l, periodize φ ((x : ℝ) - γ) :=
  SymSeq_iwKernel_cont ρ l φ hφ hper hsum x

/-- Splitting the difference of two double sums. -/
lemma symp_sum_sum_sub (X Y : Finset Circ) (f g : Circ → Circ → ℂ) :
    (∑ a ∈ X, ∑ b ∈ Y, f a b) - (∑ a ∈ X, ∑ b ∈ Y, g a b)
      = ∑ a ∈ X, ∑ b ∈ Y, (f a b - g a b) := by
  have h1 : ∀ a : Circ, (∑ b ∈ Y, f a b) - (∑ b ∈ Y, g a b) = ∑ b ∈ Y, (f a b - g a b) :=
    fun a => (Finset.sum_sub_distrib (s := Y) (f := fun b => f a b) (g := fun b => g a b)).symm
  rw [← Finset.sum_sub_distrib (s := X) (f := fun a => ∑ b ∈ Y, f a b)
    (g := fun a => ∑ b ∈ Y, g a b)]
  exact Finset.sum_congr rfl fun a _ => h1 a

/-! ## 7bis. The concrete-side expansion (own copy of `symC_eq_fibre_sum`) -/

/-- A shifted periodisation is the orbit sum of the bump at the shifted variable. -/
lemma symp_periodize_sub (φ : ℝ → ℂ) (x : ℝ) (γ : Circ) :
    periodize φ (((x : ℝ) : Circ) - γ) = ∑' m : ℤ, φ (x - gamR γ + (m : ℝ)) := by
  have h : ((x : ℝ) : Circ) - γ = (((x - gamR γ) : ℝ) : Circ) := by
    conv_lhs => rw [← symp_gamR_coe γ, ← AddCircle.coe_sub]
  rw [h, symp_periodize_eq_tsum]

/-- **The concrete §6 symbol as the aliasing-fibre double sum** (own copy of the child lemma
`symC_eq_fibre_sum`, kept so that the main file does not depend on an external module). -/
theorem symp_symC_eq_fibre_sum (ρ : ℝ) (P : Polynomial ℤ) (N l₁ l₂ k₁ k₂ : ℕ) (x y : ℝ) :
    symC ρ P N l₁ l₂ k₁ k₂ x y
      = ∑ γ₁ ∈ diffFreqs ρ l₁, ∑ γ₂ ∈ diffFreqs ρ l₂, ∑' m₁ : ℤ, ∑' m₂ : ℤ,
          halfSym N P x y * varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))
            * varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ)) := by
  have h₁ := symp_symSeq_tmKer_eq ρ l₁ (varphiN N k₁) (integrable_varphiN N k₁)
    (continuous_periodize_of_hasCompactSupport _
      (contDiff_varphiN N k₁).continuous (hasCompactSupport_varphiN N k₁))
    (symp_summable_cw_varphiN N k₁) x
  have h₂ := symp_symSeq_tmKer_eq ρ l₂ (varphitildeN P.natDegree N k₂)
    ((contDiff_varphitildeN P.natDegree N k₂).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_varphitildeN P.natDegree N k₂))
    (continuous_periodize_of_hasCompactSupport _
      (contDiff_varphitildeN P.natDegree N k₂).continuous
      (hasCompactSupport_varphitildeN P.natDegree N k₂))
    (symp_summable_cw_varphitildeN P.natDegree N k₂) y
  simp only [symC]
  rw [h₁, h₂]
  have hAB : (∑ γ₁ ∈ diffFreqs ρ l₁, periodize (varphiN N k₁) ((x : ℝ) - γ₁))
      * (∑ γ₂ ∈ diffFreqs ρ l₂, periodize (varphitildeN P.natDegree N k₂) ((y : ℝ) - γ₂))
      * halfSym N P x y
      = ∑ γ₁ ∈ diffFreqs ρ l₁, ∑ γ₂ ∈ diffFreqs ρ l₂,
          (periodize (varphiN N k₁) ((x : ℝ) - γ₁)
            * periodize (varphitildeN P.natDegree N k₂) ((y : ℝ) - γ₂) * halfSym N P x y) := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun γ₁ _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
  rw [hAB]
  refine Finset.sum_congr rfl fun γ₁ _ => Finset.sum_congr rfl fun γ₂ _ => ?_
  rw [symp_periodize_sub, symp_periodize_sub]
  have hs2 : (∑' m₂ : ℤ, varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ)))
        * halfSym N P x y
      = ∑' m₂ : ℤ, varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))
          * halfSym N P x y :=
    (tsum_mul_right (f := fun m₂ : ℤ =>
      varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))) (a := halfSym N P x y)).symm
  have hs3 : (∑' m₁ : ℤ, varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ)))
        * (∑' m₂ : ℤ, varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))
          * halfSym N P x y)
      = ∑' m₁ : ℤ, varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))
          * (∑' m₂ : ℤ, varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))
            * halfSym N P x y) :=
    (tsum_mul_right (f := fun m₁ : ℤ => varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ)))
      (a := ∑' m₂ : ℤ, varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))
        * halfSym N P x y)).symm
  have hs4 : ∀ m₁ : ℤ, varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))
        * (∑' m₂ : ℤ, varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))
          * halfSym N P x y)
      = ∑' m₂ : ℤ, varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))
          * (varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ)) * halfSym N P x y) :=
    fun m₁ => (tsum_mul_left (a := varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ)))
      (f := fun m₂ : ℤ => varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))
        * halfSym N P x y)).symm
  rw [mul_assoc, hs2, hs3]
  refine tsum_congr fun m₁ => ?_
  rw [hs4 m₁]
  refine tsum_congr fun m₂ => ?_
  ring

/-! ## 7ter. The `t`-integral of the periodised modulated bumps (own copy) -/

/-- `ee (a + b) = ee a * ee b`. -/
lemma symp_ee_mul (a b : ℝ) : Work.KMTAreas.A7.ee (a + b) = Work.KMTAreas.A7.ee a * Work.KMTAreas.A7.ee b := by
  rw [Work.KMTAreas.A7.ee, Work.KMTAreas.A7.ee, Work.KMTAreas.A7.ee, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `ee` is continuous. -/
lemma symp_continuous_ee : Continuous Work.KMTAreas.A7.ee :=
  symp_continuous_eeC.congr fun z => (symp_eeC_eq_ee z).symm

/-- Membership in the window of the representatives of an orbit sum. -/
lemma symp_mem_window {R c : ℝ} {m : ℤ} (hm : |c + (m : ℝ)| ≤ R) :
    m ∈ Finset.Icc ⌈-(R + |c|)⌉ ⌊R + |c|⌋ := by
  have h1 : |((m : ℤ) : ℝ)| ≤ |c| + R := by
    have h2 := abs_sub_abs_le_abs_sub ((m : ℤ) : ℝ) (-c)
    rw [abs_neg, sub_neg_eq_add] at h2
    have h3 : |((m : ℤ) : ℝ) + c| ≤ R := by rw [add_comm]; exact hm
    linarith
  rw [Finset.mem_Icc]
  constructor
  · rw [Int.ceil_le]
    linarith [neg_abs_le ((m : ℤ) : ℝ), h1]
  · rw [Int.le_floor]
    linarith [le_abs_self ((m : ℤ) : ℝ), h1]

/-- **The `t`-integral of the two modulated periodised bumps** (own copy of the child lemma
`integral_periodize_modulated_bumps`).  The two orbit sums reduce to *finite* sums because the
bumps are compactly supported, so the exchange of the sums with the integral is a finite one. -/
theorem symp_integral_periodize_modulated_bumps (P : Polynomial ℤ) (N k₁ k₂ : ℕ)
    (β₁ β₂ : Circ) (x y : ℝ) :
    (∫ t in (1 / 2 : ℝ)..1,
        periodize (varphiNt N k₁ t) (((x : ℝ) : Circ) - β₁)
          * periodize (varphitildeNt P P.natDegree N k₂ t) (((y : ℝ) : Circ) - β₂))
      = ∑' m₁ : ℤ, ∑' m₂ : ℤ,
          mTilde P N (x - gamR β₁ + (m₁ : ℝ)) (y - gamR β₂ + (m₂ : ℝ))
            * varphiN N k₁ (x - gamR β₁ + (m₁ : ℝ))
            * varphitildeN P.natDegree N k₂ (y - gamR β₂ + (m₂ : ℝ)) := by
  obtain ⟨R₁, _, hR₁⟩ := symp_exists_abs_bound_of_hasCompactSupport (hasCompactSupport_varphiN N k₁)
  obtain ⟨R₂, _, hR₂⟩ :=
    symp_exists_abs_bound_of_hasCompactSupport (hasCompactSupport_varphitildeN P.natDegree N k₂)
  set S₁ : Finset ℤ := Finset.Icc ⌈-(R₁ + |x - gamR β₁|)⌉ ⌊R₁ + |x - gamR β₁|⌋ with hS₁
  set S₂ : Finset ℤ := Finset.Icc ⌈-(R₂ + |y - gamR β₂|)⌉ ⌊R₂ + |y - gamR β₂|⌋ with hS₂
  have hvan₁ : ∀ m : ℤ, m ∉ S₁ → varphiN N k₁ (x - gamR β₁ + (m : ℝ)) = 0 := by
    intro m hm
    refine hR₁ _ ?_
    by_contra hcon
    push Not at hcon
    exact hm (by rw [hS₁]; exact symp_mem_window hcon)
  have hvan₂ : ∀ m : ℤ, m ∉ S₂ → varphitildeN P.natDegree N k₂ (y - gamR β₂ + (m : ℝ)) = 0 := by
    intro m hm
    refine hR₂ _ ?_
    by_contra hcon
    push Not at hcon
    exact hm (by rw [hS₂]; exact symp_mem_window hcon)
  -- the pointwise value of the integrand is the finite double sum
  have hpt : ∀ t : ℝ,
      periodize (varphiNt N k₁ t) (((x : ℝ) : Circ) - β₁)
        * periodize (varphitildeNt P P.natDegree N k₂ t) (((y : ℝ) : Circ) - β₂)
      = ∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂,
          varphiNt N k₁ t (x - gamR β₁ + (m₁ : ℝ))
            * varphitildeNt P P.natDegree N k₂ t (y - gamR β₂ + (m₂ : ℝ)) := by
    intro t
    rw [symp_periodize_sub (varphiNt N k₁ t) x β₁,
      symp_periodize_sub (varphitildeNt P P.natDegree N k₂ t) y β₂]
    rw [tsum_eq_sum (s := S₁) (fun m₁ hm₁ => by
          show varphiN N k₁ (x - gamR β₁ + (m₁ : ℝ))
              * Work.KMTAreas.A7.ee ((N : ℝ) * t * (x - gamR β₁ + (m₁ : ℝ))) = 0
          rw [hvan₁ m₁ hm₁, zero_mul]),
      tsum_eq_sum (s := S₂) (fun m₂ hm₂ => by
          show varphitildeN P.natDegree N k₂ (y - gamR β₂ + (m₂ : ℝ))
              * Work.KMTAreas.A7.ee (PevalR P ((N : ℝ) * t) * (y - gamR β₂ + (m₂ : ℝ))) = 0
          rw [hvan₂ m₂ hm₂, zero_mul])]
    exact Finset.sum_mul_sum S₁ S₂ _ _
  -- continuity of a single summand in `t`
  have hcont : ∀ m₁ m₂ : ℤ, Continuous (fun t : ℝ =>
      varphiNt N k₁ t (x - gamR β₁ + (m₁ : ℝ))
        * varphitildeNt P P.natDegree N k₂ t (y - gamR β₂ + (m₂ : ℝ))) := by
    intro m₁ m₂
    have h1 : Continuous fun t : ℝ =>
        Work.KMTAreas.A7.ee ((N : ℝ) * t * (x - gamR β₁ + (m₁ : ℝ))) :=
      symp_continuous_ee.comp (by fun_prop)
    have h2 : Continuous fun t : ℝ =>
        Work.KMTAreas.A7.ee (PevalR P ((N : ℝ) * t) * (y - gamR β₂ + (m₂ : ℝ))) := by
      refine symp_continuous_ee.comp ?_
      unfold PevalR
      exact ((P.map (Int.castRingHom ℝ)).continuous.comp (by fun_prop)).mul continuous_const
    have h3 : Continuous fun t : ℝ => varphiN N k₁ (x - gamR β₁ + (m₁ : ℝ))
        * Work.KMTAreas.A7.ee ((N : ℝ) * t * (x - gamR β₁ + (m₁ : ℝ)))
        * (varphitildeN P.natDegree N k₂ (y - gamR β₂ + (m₂ : ℝ))
          * Work.KMTAreas.A7.ee (PevalR P ((N : ℝ) * t) * (y - gamR β₂ + (m₂ : ℝ)))) :=
      (continuous_const.mul h1).mul (continuous_const.mul h2)
    exact h3.congr fun t => by simp only [varphiNt, varphitildeNt]
  -- the finite exchange
  have hInt : (∫ t in (1 / 2 : ℝ)..1, ∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂,
        varphiNt N k₁ t (x - gamR β₁ + (m₁ : ℝ))
          * varphitildeNt P P.natDegree N k₂ t (y - gamR β₂ + (m₂ : ℝ)))
      = ∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂, ∫ t in (1 / 2 : ℝ)..1,
          varphiNt N k₁ t (x - gamR β₁ + (m₁ : ℝ))
            * varphitildeNt P P.natDegree N k₂ t (y - gamR β₂ + (m₂ : ℝ)) := by
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun m₁ _ => ?_
      rw [intervalIntegral.integral_finsetSum]
      intro m₂ _
      exact (hcont m₁ m₂).intervalIntegrable _ _
    · intro m₁ _
      refine Continuous.intervalIntegrable ?_ _ _
      exact continuous_finsetSum _ fun m₂ _ => hcont m₁ m₂
  -- the value of a single integral
  have hsingle : ∀ m₁ m₂ : ℤ,
      (∫ t in (1 / 2 : ℝ)..1,
          varphiNt N k₁ t (x - gamR β₁ + (m₁ : ℝ))
            * varphitildeNt P P.natDegree N k₂ t (y - gamR β₂ + (m₂ : ℝ)))
        = mTilde P N (x - gamR β₁ + (m₁ : ℝ)) (y - gamR β₂ + (m₂ : ℝ))
            * varphiN N k₁ (x - gamR β₁ + (m₁ : ℝ))
            * varphitildeN P.natDegree N k₂ (y - gamR β₂ + (m₂ : ℝ)) := by
    intro m₁ m₂
    have hfun : (fun t : ℝ => varphiNt N k₁ t (x - gamR β₁ + (m₁ : ℝ))
          * varphitildeNt P P.natDegree N k₂ t (y - gamR β₂ + (m₂ : ℝ)))
        = fun t : ℝ => varphiN N k₁ (x - gamR β₁ + (m₁ : ℝ))
            * varphitildeN P.natDegree N k₂ (y - gamR β₂ + (m₂ : ℝ))
            * Work.KMTAreas.A7.ee ((x - gamR β₁ + (m₁ : ℝ)) * (N : ℝ) * t
              + (y - gamR β₂ + (m₂ : ℝ)) * PevalR P ((N : ℝ) * t)) := by
      funext t
      simp only [varphiNt, varphitildeNt]
      rw [show varphiN N k₁ (x - gamR β₁ + (m₁ : ℝ))
            * Work.KMTAreas.A7.ee ((N : ℝ) * t * (x - gamR β₁ + (m₁ : ℝ)))
            * (varphitildeN P.natDegree N k₂ (y - gamR β₂ + (m₂ : ℝ))
              * Work.KMTAreas.A7.ee (PevalR P ((N : ℝ) * t) * (y - gamR β₂ + (m₂ : ℝ))))
          = (varphiN N k₁ (x - gamR β₁ + (m₁ : ℝ))
              * varphitildeN P.natDegree N k₂ (y - gamR β₂ + (m₂ : ℝ)))
            * (Work.KMTAreas.A7.ee ((N : ℝ) * t * (x - gamR β₁ + (m₁ : ℝ)))
              * Work.KMTAreas.A7.ee (PevalR P ((N : ℝ) * t) * (y - gamR β₂ + (m₂ : ℝ))))
          from by ring]
      rw [← symp_ee_mul]
      congr 1
      ring
    rw [hfun, intervalIntegral.integral_const_mul, mTilde]
    ring
  rw [intervalIntegral.integral_congr (fun t _ => hpt t), hInt]
  rw [Finset.sum_congr rfl (fun m₁ _ => Finset.sum_congr rfl (fun m₂ _ => hsingle m₁ m₂))]
  -- both sides are now finite sums over the same windows
  have hRHS : (∑' m₁ : ℤ, ∑' m₂ : ℤ,
        mTilde P N (x - gamR β₁ + (m₁ : ℝ)) (y - gamR β₂ + (m₂ : ℝ))
          * varphiN N k₁ (x - gamR β₁ + (m₁ : ℝ))
          * varphitildeN P.natDegree N k₂ (y - gamR β₂ + (m₂ : ℝ)))
      = ∑ m₁ ∈ S₁, ∑ m₂ ∈ S₂,
        mTilde P N (x - gamR β₁ + (m₁ : ℝ)) (y - gamR β₂ + (m₂ : ℝ))
          * varphiN N k₁ (x - gamR β₁ + (m₁ : ℝ))
          * varphitildeN P.natDegree N k₂ (y - gamR β₂ + (m₂ : ℝ)) := by
    have h₁ : (∑' m₁ : ℤ, ∑' m₂ : ℤ,
          mTilde P N (x - gamR β₁ + (m₁ : ℝ)) (y - gamR β₂ + (m₂ : ℝ))
            * varphiN N k₁ (x - gamR β₁ + (m₁ : ℝ))
            * varphitildeN P.natDegree N k₂ (y - gamR β₂ + (m₂ : ℝ)))
        = ∑ m₁ ∈ S₁, ∑' m₂ : ℤ,
          mTilde P N (x - gamR β₁ + (m₁ : ℝ)) (y - gamR β₂ + (m₂ : ℝ))
            * varphiN N k₁ (x - gamR β₁ + (m₁ : ℝ))
            * varphitildeN P.natDegree N k₂ (y - gamR β₂ + (m₂ : ℝ)) := by
      refine tsum_eq_sum (s := S₁) fun m₁ hm₁ => ?_
      have hzero : (fun m₂ : ℤ => mTilde P N (x - gamR β₁ + (m₁ : ℝ)) (y - gamR β₂ + (m₂ : ℝ))
          * varphiN N k₁ (x - gamR β₁ + (m₁ : ℝ))
          * varphitildeN P.natDegree N k₂ (y - gamR β₂ + (m₂ : ℝ))) = fun _ : ℤ => (0 : ℂ) := by
        funext m₂
        by_cases h : m₂ ∈ S₂
        · rw [hvan₁ m₁ hm₁]; ring
        · rw [hvan₂ m₂ h]; ring
      rw [hzero]
      exact tsum_zero
    rw [h₁]
    refine Finset.sum_congr rfl fun m₁ _ => ?_
    exact tsum_eq_sum (s := S₂) fun m₂ hm₂ => by rw [hvan₂ m₂ hm₂]; ring
  rw [hRHS]

/-! ## 7quater. Poisson summation for the arithmetic kernel (own copy) -/

/-- **Poisson summation for the arithmetic kernel of the §6 model operator** (own copy of the child
lemma `symSeq2_arithKerM_eq`): the symbol of the arithmetic kernel `arithKerM` is the finite
arithmetic sum over the exact-height frequencies of `m_Ẑ` times the two periodisations of the
tensor windows.

No hypothesis on the arithmetic frequencies is needed: this is a formal Fourier identity. -/
theorem symp_symSeq2_arithKerM_eq (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ k₁ k₂ : ℕ) (x y : ℝ) :
    symSeq2 (arithKerM ρ P l₁ l₂ k₁ k₂) x y
      = ∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
          mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂
            * periodize (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂))) ((x : ℝ) - α₁)
            * periodize (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂))) ((y : ℝ) - α₂) := by
  set u := uScale ρ (lcL l₁ l₂ k₁ k₂) with hu
  set d := P.natDegree with hd
  -- the one-dimensional Poisson identities, with the character spliced in
  have hQ1 : ∀ α₁ : Circ, (∑' a : ℤ, cw (mStarF u) a * fourier (T := 1) (-a) α₁
        * eeC ((a : ℝ) * x)) = periodize (mStarF u) (((x : ℝ) : Circ) - α₁) := by
    intro α₁
    rw [← symp_cw_tsum_fourier (symp_contDiff_mStarF u) (symp_hasCompactSupport_mStarF u)
      (((x : ℝ) : Circ) - α₁)]
    refine tsum_congr fun a => ?_
    rw [← fourier_coe_one' a x, mul_assoc, fourier_splice a α₁ x]
  have hQ2 : ∀ α₂ : Circ, (∑' b : ℤ, cw (mStargF d u) b * fourier (T := 1) (-b) α₂
        * eeC ((b : ℝ) * y)) = periodize (mStargF d u) (((y : ℝ) : Circ) - α₂) := by
    intro α₂
    rw [← symp_cw_tsum_fourier (symp_contDiff_mStargF d u) (symp_hasCompactSupport_mStargF d u)
      (((y : ℝ) : Circ) - α₂)]
    refine tsum_congr fun b => ?_
    rw [← fourier_coe_one' b y, mul_assoc, fourier_splice b α₂ y]
  -- the product majorant
  have hprod : Summable fun p : ℤ × ℤ => ‖cw (mStarF u) p.1‖ * ‖cw (mStargF d u) p.2‖ := by
    simpa [norm_mul] using (symp_summable_cw_mStarF u).mul_norm
      (f := fun a : ℤ => cw (mStarF u) a) (g := fun b : ℤ => cw (mStargF d u) b)
      (symp_summable_cw_mStargF d u)
  -- the bound on the arithmetic kernel
  have hbound : ∀ p : ℤ × ℤ, ‖arithKerM ρ P l₁ l₂ k₁ k₂ p.1 p.2‖
      ≤ ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ)
        * (‖cw (mStarF u) p.1‖ * ‖cw (mStargF d u) p.2‖) := by
    intro p
    have hker : ‖arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2‖
        ≤ ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) := by
      rw [arithKernelEx]
      calc ‖∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
              mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂
                * fourier (T := 1) (-p.1) α₁ * fourier (T := 1) (-p.2) α₂‖
          ≤ ∑ α₁ ∈ diffFreqs ρ l₁, ‖∑ α₂ ∈ diffFreqs ρ l₂,
              mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂
                * fourier (T := 1) (-p.1) α₁ * fourier (T := 1) (-p.2) α₂‖ := norm_sum_le _ _
        _ ≤ ∑ _α₁ ∈ diffFreqs ρ l₁, ((diffFreqs ρ l₂).card : ℝ) := by
            refine Finset.sum_le_sum fun α₁ _ => ?_
            calc ‖∑ α₂ ∈ diffFreqs ρ l₂, mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂
                    * fourier (T := 1) (-p.1) α₁ * fourier (T := 1) (-p.2) α₂‖
                ≤ ∑ α₂ ∈ diffFreqs ρ l₂, ‖mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂
                    * fourier (T := 1) (-p.1) α₁ * fourier (T := 1) (-p.2) α₂‖ := norm_sum_le _ _
              _ ≤ ∑ _α₂ ∈ diffFreqs ρ l₂, (1 : ℝ) := by
                  refine Finset.sum_le_sum fun α₂ _ => ?_
                  rw [norm_mul, norm_mul, norm_fourier_one, norm_fourier_one, mul_one, mul_one]
                  exact symp_norm_mZ_le_one P (arithQ ρ (max l₁ l₂)) α₁ α₂
              _ = ((diffFreqs ρ l₂).card : ℝ) := by simp
        _ = ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul]
    rw [arithKerM, norm_mul, norm_mul]
    calc ‖arithKernelEx ρ P (arithQ ρ (max l₁ l₂)) l₁ l₂ p.1 p.2‖
          * ‖cw (mStarF u) p.1‖ * ‖cw (mStargF d u) p.2‖
        ≤ (((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ))
            * ‖cw (mStarF u) p.1‖ * ‖cw (mStargF d u) p.2‖ := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hker (norm_nonneg _))
            (norm_nonneg _)
      _ = ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ)
            * (‖cw (mStarF u) p.1‖ * ‖cw (mStargF d u) p.2‖) := by ring
  -- absolute convergence of the two-dimensional symbol series
  have hsummand : Summable fun p : ℤ × ℤ =>
      arithKerM ρ P l₁ l₂ k₁ k₂ p.1 p.2 * eeC (p.1 * x + p.2 * y) := by
    refine Summable.of_norm_bounded (g := fun p : ℤ × ℤ =>
      ((diffFreqs ρ l₁).card : ℝ) * ((diffFreqs ρ l₂).card : ℝ)
        * (‖cw (mStarF u) p.1‖ * ‖cw (mStargF d u) p.2‖)) (hprod.mul_left _) (fun p => ?_)
    rw [norm_mul, symp_norm_eeC, mul_one]
    exact hbound p
  rw [symSeq2, ← Summable.tsum_prod hsummand]
  -- unfold the kernel into the finite sum over the exact-height frequencies
  have hswap : ∀ p : ℤ × ℤ, arithKerM ρ P l₁ l₂ k₁ k₂ p.1 p.2 * eeC (p.1 * x + p.2 * y)
      = ∑ z ∈ (diffFreqs ρ l₁).product (diffFreqs ρ l₂),
          mZ P (arithQ ρ (max l₁ l₂)) z.1 z.2
            * fourier (T := 1) (-p.1) z.1 * fourier (T := 1) (-p.2) z.2
            * cw (mStarF u) p.1 * cw (mStargF d u) p.2 * eeC (p.1 * x + p.2 * y) := by
    intro p
    rw [arithKerM, arithKernelEx, ← hu, ← hd]
    rw [show (∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
          mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-p.1) α₁
            * fourier (T := 1) (-p.2) α₂)
        = ∑ z ∈ (diffFreqs ρ l₁).product (diffFreqs ρ l₂),
          mZ P (arithQ ρ (max l₁ l₂)) z.1 z.2 * fourier (T := 1) (-p.1) z.1
            * fourier (T := 1) (-p.2) z.2 from
      (Finset.sum_product (diffFreqs ρ l₁) (diffFreqs ρ l₂) (fun z : Circ × Circ =>
        mZ P (arithQ ρ (max l₁ l₂)) z.1 z.2 * fourier (T := 1) (-p.1) z.1
          * fourier (T := 1) (-p.2) z.2)).symm]
    simp only [Finset.sum_mul]
  rw [tsum_congr hswap]
  -- the fibre double sum factorises
  have hinner : ∀ α₁ α₂ : Circ,
      (∑' p : ℤ × ℤ, mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-p.1) α₁
          * fourier (T := 1) (-p.2) α₂ * cw (mStarF u) p.1 * cw (mStargF d u) p.2
          * eeC (p.1 * x + p.2 * y))
        = mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂
          * periodize (mStarF u) (((x : ℝ) : Circ) - α₁)
          * periodize (mStargF d u) (((y : ℝ) : Circ) - α₂) := by
    intro α₁ α₂
    have hf : Summable fun a : ℤ =>
        ‖cw (mStarF u) a * fourier (T := 1) (-a) α₁ * eeC ((a : ℝ) * x)‖ := by
      refine (symp_summable_cw_mStarF u).congr (fun a => ?_)
      simp only [norm_mul, norm_fourier_one, symp_norm_eeC, mul_one]
    have hg : Summable fun b : ℤ =>
        ‖cw (mStargF d u) b * fourier (T := 1) (-b) α₂ * eeC ((b : ℝ) * y)‖ := by
      refine (symp_summable_cw_mStargF d u).congr (fun b => ?_)
      simp only [norm_mul, norm_fourier_one, symp_norm_eeC, mul_one]
    have hp_eq : ∀ p : ℤ × ℤ,
        mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂ * fourier (T := 1) (-p.1) α₁
          * fourier (T := 1) (-p.2) α₂ * cw (mStarF u) p.1 * cw (mStargF d u) p.2
          * eeC (p.1 * x + p.2 * y)
        = mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂
          * ((cw (mStarF u) p.1 * fourier (T := 1) (-p.1) α₁ * eeC ((p.1 : ℝ) * x))
            * (cw (mStargF d u) p.2 * fourier (T := 1) (-p.2) α₂
              * eeC ((p.2 : ℝ) * y))) := by
      intro p
      rw [symp_eeC_add]
      ring
    rw [tsum_congr hp_eq]
    rw [tsum_mul_left]
    rw [← tsum_mul_tsum_of_summable_norm
      (f := fun a : ℤ => cw (mStarF u) a * fourier (T := 1) (-a) α₁ * eeC ((a : ℝ) * x))
      (g := fun b : ℤ => cw (mStargF d u) b * fourier (T := 1) (-b) α₂
        * eeC ((b : ℝ) * y)) hf hg]
    rw [hQ1 α₁, hQ2 α₂]
    ring
  -- exchange the finite arithmetic sums with the double `tsum`
  rw [Summable.tsum_finsetSum (s := (diffFreqs ρ l₁).product (diffFreqs ρ l₂))
    (f := fun (z : Circ × Circ) (p : ℤ × ℤ) => mZ P (arithQ ρ (max l₁ l₂)) z.1 z.2
        * fourier (T := 1) (-p.1) z.1 * fourier (T := 1) (-p.2) z.2
        * cw (mStarF u) p.1 * cw (mStargF d u) p.2 * eeC (p.1 * x + p.2 * y))]
  · refine (Finset.sum_congr rfl fun z _ => hinner z.1 z.2).trans ?_
    exact Finset.sum_product (diffFreqs ρ l₁) (diffFreqs ρ l₂) (fun z : Circ × Circ =>
      mZ P (arithQ ρ (max l₁ l₂)) z.1 z.2
        * periodize (mStarF u) (((x : ℝ) : Circ) - z.1)
        * periodize (mStargF d u) (((y : ℝ) : Circ) - z.2))
  · intro z _
    refine Summable.of_norm_bounded (g := fun p : ℤ × ℤ =>
      ‖mZ P (arithQ ρ (max l₁ l₂)) z.1 z.2‖
        * (‖cw (mStarF u) p.1‖ * ‖cw (mStargF d u) p.2‖)) (hprod.mul_left _) (fun p => ?_)
    rw [norm_mul, norm_mul, norm_mul, norm_mul, norm_mul, norm_fourier_one, norm_fourier_one,
      symp_norm_eeC]
    exact le_of_eq (by ring)

/-! ## 8. The assembly -/

/-- **The assembly of the collapse identity.**  From the four analytic inputs
(`symC_eq_fibre_sum`, `weylAvg_shift_eq_halfSym`, `symSeq2_arithKerM_eq`,
`integral_periodize_modulated_bumps`) and the arc facts for the bumps and windows, we deduce
`symC - symM = symD`. -/
theorem symC_sub_symM_eq_symD_assembly
    (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (N l₁ l₂ k₁ k₂ : ℕ) (hN : 1 ≤ N) (x y : ℝ) (u : ℕ) (hu : u = uScale ρ (lcL l₁ l₂ k₁ k₂))
    (hC2 : max k₁ k₂ + 2 * uScale ρ (lcL l₁ l₂ k₁ k₂) + 1
      ≤ (Work.Analysis.EndVar.logN N).toNat)
    (hna : NonAliasing (-(2 * (uScale ρ (lcL l₁ l₂ k₁ k₂)) : ℤ))
      (iwArithFreqs ρ l₁ ∪ iwArithFreqs ρ l₂))
    (hC : symC ρ P N l₁ l₂ k₁ k₂ x y
      = ∑ γ₁ ∈ diffFreqs ρ l₁, ∑ γ₂ ∈ diffFreqs ρ l₂, ∑' m₁ : ℤ, ∑' m₂ : ℤ,
          halfSym N P x y * varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))
            * varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ)))
    (hW : ∀ (γ₁ γ₂ : Circ) (m₁ m₂ : ℤ),
          weylAvg P N γ₁ γ₂ (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))
            = halfSym N P x y)
    (hD1 : symSeq2 (arithKerM ρ P l₁ l₂ k₁ k₂) x y
      = ∑ α₁ ∈ diffFreqs ρ l₁, ∑ α₂ ∈ diffFreqs ρ l₂,
          mZ P (arithQ ρ (max l₁ l₂)) α₁ α₂
            * periodize (mStarF u) ((x : ℝ) - α₁)
            * periodize (mStargF P.natDegree u) ((y : ℝ) - α₂))
    (hI : ∀ β₁ β₂ : Circ,
          (∫ t in (1 / 2 : ℝ)..1,
              periodize (varphiNt N k₁ t) ((x : ℝ) - β₁)
                * periodize (varphitildeNt P P.natDegree N k₂ t) ((y : ℝ) - β₂))
          = ∑' m₁ : ℤ, ∑' m₂ : ℤ,
              mTilde P N (x - gamR β₁ + (m₁ : ℝ)) (y - gamR β₂ + (m₂ : ℝ))
                * varphiN N k₁ (x - gamR β₁ + (m₁ : ℝ))
                * varphitildeN P.natDegree N k₂ (y - gamR β₂ + (m₂ : ℝ)))
    (hFlatA : ∀ θ : ℝ, θ ∈ realArc (-(2 * (u : ℤ) + 1)) →
      periodize (mStarF u) (θ : Circ) = 1)
    (hSupA : SupportedInArc (-(2 * (u : ℤ))) (periodize (mStarF u)))
    (hFlatB : ∀ θ : ℝ, θ ∈ realArc (-((P.natDegree : ℤ) * 2 * (u : ℤ) + 1)) →
      periodize (mStargF P.natDegree u) (θ : Circ) = 1)
    (hSupB : SupportedInArc (-((P.natDegree : ℤ) * 2 * (u : ℤ)))
      (periodize (mStargF P.natDegree u)))
    (hBumpA : ∀ t : ℝ, SupportedInArc (-(2 * (u : ℤ) + 1)) (periodize (varphiNt N k₁ t)))
    (hBumpB : ∀ t : ℝ, SupportedInArc (-((P.natDegree : ℤ) * 2 * (u : ℤ) + 1))
      (periodize (varphitildeNt P P.natDegree N k₂ t))) :
    symC ρ P N l₁ l₂ k₁ k₂ x y - symM ρ P N l₁ l₂ k₁ k₂ x y
      = symD ρ P N l₁ l₂ k₁ k₂ x y := by
  subst hu
  have hu_pos : 1 ≤ uScale ρ (lcL l₁ l₂ k₁ k₂) :=
    symp_one_le_uScale ρ hρ.le (lcL l₁ l₂ k₁ k₂)
  -- regime consequences of `hC2`
  have hk₁ : k₁ + 2 * uScale ρ (lcL l₁ l₂ k₁ k₂) + 1 ≤ (Work.Analysis.EndVar.logN N).toNat := by
    omega
  have hk₂ : k₂ + 2 * uScale ρ (lcL l₁ l₂ k₁ k₂) + 1 ≤ (Work.Analysis.EndVar.logN N).toNat := by
    omega
  -- non-aliasing of the individual frequency sets
  have hNA₁ : NonAliasing (-(2 * (uScale ρ (lcL l₁ l₂ k₁ k₂)) : ℤ)) (diffFreqs ρ l₁) :=
    symp_NonAliasing_subset hna
      (Finset.Subset.trans (symp_diffFreqs_subset ρ l₁) Finset.subset_union_left)
  have hNA₂ : NonAliasing (-((P.natDegree : ℤ) * 2 * (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)))
      (diffFreqs ρ l₂) := by
    refine symp_NonAliasing_of_le ?_ (symp_NonAliasing_subset hna
      (Finset.Subset.trans (symp_diffFreqs_subset ρ l₂) Finset.subset_union_right))
    have hd1 : (1 : ℤ) ≤ (P.natDegree : ℤ) := by exact_mod_cast hd
    have hu0 : (0 : ℤ) ≤ (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ) := Int.natCast_nonneg _
    nlinarith
  -- the pointwise collapse, at every `t`, in the two variables
  have hcoll₁ : ∀ t : ℝ, ∀ α ∈ diffFreqs ρ l₁, ∀ β ∈ diffFreqs ρ l₁,
      periodize (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂))) ((x : ℝ) - α)
          * periodize (varphiNt N k₁ t) ((x : ℝ) - β)
        = if β = α then periodize (varphiNt N k₁ t) ((x : ℝ) - β) else 0 := by
    intro t α hα β hβ
    exact symp_collapse_pointwise
      (kΦ := -(2 * (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ) + 1))
      (kΨ := -(2 * (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)))
      (k := -(2 * (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)))
      (by omega) le_rfl hNA₁ (hBumpA t) hSupA hFlatA hα hβ ((x : ℝ) : Circ)
  have hcoll₂ : ∀ t : ℝ, ∀ α ∈ diffFreqs ρ l₂, ∀ β ∈ diffFreqs ρ l₂,
      periodize (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂))) ((y : ℝ) - α)
          * periodize (varphitildeNt P P.natDegree N k₂ t) ((y : ℝ) - β)
        = if β = α then periodize (varphitildeNt P P.natDegree N k₂ t) ((y : ℝ) - β) else 0 := by
    intro t α hα β hβ
    exact symp_collapse_pointwise
      (kΦ := -((P.natDegree : ℤ) * 2 * (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ) + 1))
      (kΨ := -((P.natDegree : ℤ) * 2 * (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)))
      (k := -((P.natDegree : ℤ) * 2 * (uScale ρ (lcL l₁ l₂ k₁ k₂) : ℤ)))
      (by omega) le_rfl hNA₂ (hBumpB t) hSupB hFlatB hα hβ ((y : ℝ) : Circ)
  -- the collapsed integrand of the model side
  have hcollapse : ∀ t : ℝ,
      symSeq2 (arithKerM ρ P l₁ l₂ k₁ k₂) x y
          * symSeq (tmKer ρ l₁ (varphiNt N k₁ t)) x
          * symSeq (tmKer ρ l₂ (varphitildeNt P P.natDegree N k₂ t)) y
        = ∑ β₁ ∈ diffFreqs ρ l₁, ∑ β₂ ∈ diffFreqs ρ l₂,
            mZ P (arithQ ρ (max l₁ l₂)) β₁ β₂
              * periodize (varphiNt N k₁ t) ((x : ℝ) - β₁)
              * periodize (varphitildeNt P P.natDegree N k₂ t) ((y : ℝ) - β₂) := by
    intro t
    rw [hD1,
      symp_symSeq_tmKer_eq ρ l₁ (varphiNt N k₁ t) (integrable_varphiNt N k₁ t)
        (continuous_periodize_of_hasCompactSupport _
          (contDiff_varphiNt N k₁ t).continuous (hasCompactSupport_varphiNt N k₁ t))
        (symp_summable_cw_varphiNt N k₁ t) x,
      symp_symSeq_tmKer_eq ρ l₂ (varphitildeNt P P.natDegree N k₂ t)
        (symp_integrable_varphitildeNt P P.natDegree N k₂ t)
        (continuous_periodize_of_hasCompactSupport _
          (symp_contDiff_varphitildeNt P P.natDegree N k₂ t).continuous
          (symp_hasCompactSupport_varphitildeNt P P.natDegree N k₂ t))
        (symp_summable_cw_varphitildeNt P P.natDegree N k₂ t) y]
    exact symp_sum_collapse (diffFreqs ρ l₁) (diffFreqs ρ l₂)
      (fun a b => mZ P (arithQ ρ (max l₁ l₂)) a b)
      (periodize (mStarF (uScale ρ (lcL l₁ l₂ k₁ k₂)))) (periodize (varphiNt N k₁ t))
      (periodize (mStargF P.natDegree (uScale ρ (lcL l₁ l₂ k₁ k₂))))
      (periodize (varphitildeNt P P.natDegree N k₂ t))
      ((x : ℝ) : Circ) ((y : ℝ) : Circ) (hcoll₁ t) (hcoll₂ t)
  -- expand `symM`
  have hM : symM ρ P N l₁ l₂ k₁ k₂ x y
      = ∑ β₁ ∈ diffFreqs ρ l₁, ∑ β₂ ∈ diffFreqs ρ l₂, ∑' m₁ : ℤ, ∑' m₂ : ℤ,
          mZ P (arithQ ρ (max l₁ l₂)) β₁ β₂
            * mTilde P N (x - gamR β₁ + (m₁ : ℝ)) (y - gamR β₂ + (m₂ : ℝ))
            * varphiN N k₁ (x - gamR β₁ + (m₁ : ℝ))
            * varphitildeN P.natDegree N k₂ (y - gamR β₂ + (m₂ : ℝ)) := by
    simp only [symM]
    rw [intervalIntegral.integral_congr (fun t _ => hcollapse t),
      intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun β₁ _ => ?_
      rw [intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun β₂ _ => ?_
        rw [show (fun t : ℝ => mZ P (arithQ ρ (max l₁ l₂)) β₁ β₂
              * periodize (varphiNt N k₁ t) ((x : ℝ) - β₁)
              * periodize (varphitildeNt P P.natDegree N k₂ t) ((y : ℝ) - β₂))
            = fun t : ℝ => mZ P (arithQ ρ (max l₁ l₂)) β₁ β₂
              * (periodize (varphiNt N k₁ t) ((x : ℝ) - β₁)
                * periodize (varphitildeNt P P.natDegree N k₂ t) ((y : ℝ) - β₂)) from
            funext fun t => by ring]
        rw [intervalIntegral.integral_const_mul, hI β₁ β₂, ← tsum_mul_left]
        refine tsum_congr fun m₁ => ?_
        rw [← tsum_mul_left]
        refine tsum_congr fun m₂ => ?_
        ring
      · intro β₂ _
        exact ((continuous_const.mul
            (symp_continuous_periodize_varphiNt N k₁ _ hu_pos hk₁ ((x : ℝ) - β₁))).mul
          (symp_continuous_periodize_varphitildeNt P P.natDegree N k₂ _ hd hu_pos hk₂
            ((y : ℝ) - β₂))).intervalIntegrable _ _
    · intro β₁ _
      refine Continuous.intervalIntegrable ?_ _ _
      refine continuous_finsetSum _ fun β₂ _ => ?_
      exact (continuous_const.mul
        (symp_continuous_periodize_varphiNt N k₁ _ hu_pos hk₁ ((x : ℝ) - β₁))).mul
        (symp_continuous_periodize_varphitildeNt P P.natDegree N k₂ _ hd hu_pos hk₂
          ((y : ℝ) - β₂))
  -- expand `symC` in the `weylAvg` form
  have hC' : symC ρ P N l₁ l₂ k₁ k₂ x y
      = ∑ γ₁ ∈ diffFreqs ρ l₁, ∑ γ₂ ∈ diffFreqs ρ l₂, ∑' m₁ : ℤ, ∑' m₂ : ℤ,
          weylAvg P N γ₁ γ₂ (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))
            * varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))
            * varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ)) := by
    rw [hC]
    refine Finset.sum_congr rfl fun γ₁ _ => Finset.sum_congr rfl fun γ₂ _ => ?_
    refine tsum_congr fun m₁ => tsum_congr fun m₂ => ?_
    rw [← hW γ₁ γ₂ m₁ m₂]
  -- combine
  rw [hC', hM, symD, symp_sum_sum_sub]
  refine Finset.sum_congr rfl fun γ₁ hγ₁ => Finset.sum_congr rfl fun γ₂ hγ₂ => ?_
  have hmz := symp_mZ_eq_perQ ρ hρ hρ1 P l₁ l₂ hγ₁ hγ₂
  have hφsum : Summable fun m₁ : ℤ => ‖varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))‖ :=
    (symp_summable_varphiN_orbit N k₁ (x - gamR γ₁)).norm
  have hψsum : Summable fun m₂ : ℤ => ‖varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖ :=
    (symp_summable_varphitildeN_orbit P.natDegree N k₂ (y - gamR γ₂)).norm
  have hbnd_a : ∀ m₁ m₂ : ℤ,
      ‖weylAvg P N γ₁ γ₂ (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))
        * varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))
        * varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖
      ≤ 2 * ‖varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))‖
        * ‖varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖ := by
    intro m₁ m₂
    calc ‖weylAvg P N γ₁ γ₂ (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))
          * varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))
          * varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖
        = ‖weylAvg P N γ₁ γ₂ (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))‖
          * ‖varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))‖
          * ‖varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖ := by
          rw [norm_mul, norm_mul]
      _ ≤ 2 * ‖varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))‖
          * ‖varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖ := by
          have h₁ := symp_norm_weylAvg_le_two P N hN γ₁ γ₂
            (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))
          have h₂ : (0 : ℝ) ≤ ‖varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))‖ := norm_nonneg _
          have h₃ : (0 : ℝ) ≤ ‖varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖ :=
            norm_nonneg _
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h₁ h₂) h₃
  have hbnd_b : ∀ m₁ m₂ : ℤ,
      ‖mZ P (arithQ ρ (max l₁ l₂)) γ₁ γ₂
        * mTilde P N (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))
        * varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))
        * varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖
      ≤ 2 * ‖varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))‖
        * ‖varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖ := by
    intro m₁ m₂
    calc ‖mZ P (arithQ ρ (max l₁ l₂)) γ₁ γ₂
          * mTilde P N (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))
          * varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))
          * varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖
        = ‖mZ P (arithQ ρ (max l₁ l₂)) γ₁ γ₂‖
          * ‖mTilde P N (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))‖
          * ‖varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))‖
          * ‖varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖ := by
          rw [norm_mul, norm_mul, norm_mul]
      _ ≤ 2 * ‖varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))‖
          * ‖varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖ := by
          have h₁ := symp_norm_mZ_le_one P (arithQ ρ (max l₁ l₂)) γ₁ γ₂
          have h₂ := symp_norm_mTilde_le_one P N (x - gamR γ₁ + (m₁ : ℝ))
            (y - gamR γ₂ + (m₂ : ℝ))
          have h₃ : (0 : ℝ) ≤ ‖varphiN N k₁ (x - gamR γ₁ + (m₁ : ℝ))‖ := norm_nonneg _
          have h₄ : (0 : ℝ) ≤ ‖varphitildeN P.natDegree N k₂ (y - gamR γ₂ + (m₂ : ℝ))‖ :=
            norm_nonneg _
          have h₅ : ‖mZ P (arithQ ρ (max l₁ l₂)) γ₁ γ₂‖
              * ‖mTilde P N (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ))‖ ≤ 2 := by
            nlinarith [h₁, h₂, norm_nonneg (mZ P (arithQ ρ (max l₁ l₂)) γ₁ γ₂),
              norm_nonneg (mTilde P N (x - gamR γ₁ + (m₁ : ℝ)) (y - gamR γ₂ + (m₂ : ℝ)))]
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h₅ h₃) h₄
  rw [symp_tsum_tsum_sub_of_bound (hφsum.mul_left 2) hψsum hbnd_a hbnd_b]
  refine tsum_congr fun m₁ => tsum_congr fun m₂ => ?_
  rw [M0, ← hmz]
  ring

/-! ## 9. The target theorem -/

theorem symC_sub_symM_eq_symD (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (ρ : ℝ) (hρ : 0 < ρ)
    (hρ1 : ρ ≤ 1) (N l₁ l₂ k₁ k₂ : ℕ)
    (hN : 1 ≤ N)
    (hC2 : max k₁ k₂ + 2 * Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂) + 1
      ≤ (Work.Analysis.EndVar.logN N).toNat)
    (hna : Work.Analysis.IonescuWainger.NonAliasing
      (-(2 * (Work.KMTAreas.A7.uScale ρ (Work.KMTPlan.A6.lcL l₁ l₂ k₁ k₂)) : ℤ))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ ∪ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂))
    (x y : ℝ) :
    Work.KMTPlan.A6.symC ρ P N l₁ l₂ k₁ k₂ x y - Work.KMTPlan.A6.symM ρ P N l₁ l₂ k₁ k₂ x y
      = Work.KMTPlan.A6.symD ρ P N l₁ l₂ k₁ k₂ x y := by
  have hu_pos : 1 ≤ uScale ρ (lcL l₁ l₂ k₁ k₂) := symp_one_le_uScale ρ hρ.le _
  have hk₁ : k₁ + 2 * uScale ρ (lcL l₁ l₂ k₁ k₂) + 1
      ≤ (Work.Analysis.EndVar.logN N).toNat := by omega
  have hk₂ : k₂ + 2 * uScale ρ (lcL l₁ l₂ k₁ k₂) + 1
      ≤ (Work.Analysis.EndVar.logN N).toNat := by omega
  exact symC_sub_symM_eq_symD_assembly P hd ρ hρ hρ1 N l₁ l₂ k₁ k₂ hN x y
    (uScale ρ (lcL l₁ l₂ k₁ k₂)) rfl hC2 hna
    (symp_symC_eq_fibre_sum ρ P N l₁ l₂ k₁ k₂ x y)
    (fun γ₁ γ₂ m₁ m₂ => weylAvg_shift_eq_halfSym P N γ₁ γ₂ x y m₁ m₂)
    (symp_symSeq2_arithKerM_eq ρ P l₁ l₂ k₁ k₂ x y)
    (fun β₁ β₂ => symp_integral_periodize_modulated_bumps P N k₁ k₂ β₁ β₂ x y)
    (fun θ hθ => symp_periodize_mStarF_eq_one _ hu_pos hθ)
    (symp_supportedInArc_periodize (symp_zpow_two_lt_half hu_pos) (symp_mStarF_support' _) le_rfl)
    (fun θ hθ => symp_periodize_mStargF_eq_one P.natDegree _ hd hu_pos hθ)
    (symp_supportedInArc_periodize (symp_zpow_two_d_lt_half hd hu_pos)
      (symp_mStargF_support' P.natDegree _) le_rfl)
    (fun t => symp_supportedInArc_periodize_varphiNt N k₁ _ hu_pos hk₁ t)
    (fun t => symp_supportedInArc_periodize_varphitildeNt P P.natDegree N k₂ _ hd hu_pos hk₂ t)

end

end Work.KMTPlan.A6
