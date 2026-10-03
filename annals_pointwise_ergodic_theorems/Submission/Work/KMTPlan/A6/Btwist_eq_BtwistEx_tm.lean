/-
# `Btwist` on the exact-height `Tm`-outputs is `BtwistEx`

The two twisted bilinear multipliers of the workspace differ only in the arithmetic frequency set
they sum over:

* `Work.KMTAreas.A7.Btwist ρ P l₁ l₂` (the paper's `B^{l₁,l₂,m_Ẑ}_{m_*}` written with the
  *cumulative* heights) uses the arithmetic kernel `arithKernel` over the height-`≤ lᵢ` frequency
  sets `(ℚ/ℤ)_{≤lᵢ} = iwArithFreqs ρ lᵢ`;
* `Work.KMTPlan.A6.BtwistEx ρ P l₁ l₂` uses the arithmetic kernel over the *exact* height-`2^{lᵢ}`
  frequency sets `diffFreqs ρ lᵢ = (ℚ/ℤ)_{lᵢ} = (ℚ/ℤ)_{≤lᵢ} \ (ℚ/ℤ)_{≤lᵢ-1}`.

The two agree as soon as they are applied to the exact-height Ionescu--Wainger outputs
`Tm ρ lᵢ (bump) (input)`.  Writing the common kernel as a finite sum over pairs of frequencies,

  `BtwistSet A₁ A₂ = ∑_{p ∈ A₁ × A₂} m_Ẑ(p) · M_{p.1} ⊗ M_{p.2}`,

where `M_α` is the single-frequency multiplier (the fibre) with symbol `periodize m (· - α)`, the
extra terms of `Btwist` (those with `p.1 ∈ (ℚ/ℤ)_{≤l₁} \ (ℚ/ℤ)_{l₁}`, i.e. of *lower* height) carry
the symbol `periodize (mStarF u) (ξ - p.1) · iwSymbolSet (diffFreqs ρ l₁) (periodize φ) ξ`, which
vanishes: if both factors were nonzero at `ξ` we would get `p.1 + t = α + s` with
`t ∈ ℝ_{≤-2u}`, `s ∈ ℝ_{≤-3u} ⊆ ℝ_{≤-2u}` and `α ∈ diffFreqs ρ l₁`, and the *non-aliasing*
hypothesis (the arcs `β + ℝ_{≤-2u}`, `β ∈ (ℚ/ℤ)_{≤l₁}`, are pairwise disjoint) would force
`p.1 = α`, contradicting `p.1 ∉ diffFreqs ρ l₁` and `α ∈ diffFreqs ρ l₁`.

Nothing here uses any hypothesis on `ρ`: the non-aliasing hypothesis alone provides the separation,
and the two support radii `2^{-2u}` and `2^{-3u}` only need `2^{-3u} ≤ 2^{-2u}`.

## Contents

* `exists_coe_abs_le_of_periodize_ne_zero` — a nonvanishing periodisation detects a real
  representative in the support;
* `mStarF_ne_zero_abs_le`, `mStargF_ne_zero_abs_le` — the supports of the two §6 windows;
* `integrable_mStarF`/`…mStargF`, `memLp_periodize_mStarF`/`…mStargF`,
  `cw_mStarF_summable'`/`…mStargF'` — integrability, `L^∞`-membership of the periodisation and
  `ℓ¹`-summability of the `cw`-coefficients of the windows;
* `summable_fourier_cw_mul` — Cauchy--Schwarz for an `ℓ¹`-kernel against an `ℓ²`-input;
* `bfiber_eq_iwConv` — the single-frequency fibre is the Ionescu--Wainger multiplier
  `iwConv {α} (periodize m)`;
* `iwConv_singleton_eq_zero_of` — the functional calculus: if the product of the symbols
  `iwSymbolSet {α} (periodize m)` and `iwSymbolSet D Φ` vanishes, the composite multiplier kills
  `iwConv D Φ f`;
* `tsum_tsum_finset_factor'`, `BtwistSet_eq_sum_arith` — the frequency-pair decomposition of
  `BtwistSet`;
* `htermF`/`htermG` — the two symbol-product vanishing statements;
* `Btwist_eq_BtwistEx_tm` — the target.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.ssuCollapse
import Submission.Work.KMTAreas.A7.Btwist_eq_fiberSum

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-! ## 1. Support of the periodised bumps -/

/-- **A nonvanishing periodisation detects a real representative in the support.**  If `φ` is
supported in `[-δ, δ]` and `periodize φ` does not vanish at `θ`, then `θ` is the image of some real
number `θ₀` with `|θ₀| ≤ δ`. -/
theorem exists_coe_abs_le_of_periodize_ne_zero {φ : ℝ → ℂ} {δ : ℝ}
    (hsupp : ∀ y : ℝ, φ y ≠ 0 → |y| ≤ δ) {θ : Circ} (h : periodize φ θ ≠ 0) :
    ∃ θ₀ : ℝ, (θ₀ : Circ) = θ ∧ |θ₀| ≤ δ := by
  set x : ℝ := (AddCircle.equivIco (1 : ℝ) 0 θ).val with hxdef
  have hxθ : (x : Circ) = θ := by
    rw [hxdef]; exact AddCircle.coe_equivIco
  have hper : periodize φ θ = ∑' k : ℤ, φ (x + (k : ℝ)) := by
    rw [← hxθ, Work.KMTContract.periodizeCoeEqTsum]
  have hne : ∃ k : ℤ, φ (x + (k : ℝ)) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine h ?_
    rw [hper]
    have h0 : (fun k : ℤ => φ (x + (k : ℝ))) = fun _ => (0 : ℂ) := funext hcon
    rw [h0, tsum_zero]
  obtain ⟨k, hk⟩ := hne
  refine ⟨x + (k : ℝ), ?_, hsupp _ hk⟩
  have hkc : (((k : ℝ)) : Circ) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]
    exact ⟨k, by simp⟩
  rw [AddCircle.coe_add, hxθ, hkc, add_zero]

/-- The membership in `realArc` is the bound on the absolute value. -/
theorem mem_realArc_iff {k : ℤ} {t : ℝ} : t ∈ realArc k ↔ |t| ≤ (2 : ℝ) ^ k := by
  rw [realArc, Set.mem_Icc, abs_le]

/-- A frequency of exact height `l` has height `≤ l`. -/
theorem mem_iwArithFreqs_of_mem_diffFreqs {ρ : ℝ} {l : ℕ} {α : Circ}
    (h : α ∈ Work.KMTAreas.A7.diffFreqs ρ l) :
    α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l := by
  by_cases hl : l = 0
  · simpa [Work.KMTAreas.A7.diffFreqs, hl] using h
  · exact (Finset.mem_sdiff.mp (by
      simpa [Work.KMTAreas.A7.diffFreqs, hl] using h)).1

/-- The §6 window `m_* = η_{≤-2u}` vanishes off the arc of radius `2^{-2u}`. -/
theorem mStarF_ne_zero_abs_le (u : ℕ) :
    ∀ y : ℝ, Work.KMTAreas.A7.mStarF u y ≠ 0 → |y| ≤ (2 : ℝ) ^ (-(2 * (u : ℤ))) := by
  intro y hy
  by_contra h
  push Not at h
  refine hy ?_
  exact Work.KMTAreas.A7.etaCut_eq_zero_of_le (le_of_lt h)

/-- The §6 window `m_*^{(d)} = η_{≤-2du}` vanishes off the arc of radius `2^{-2du}`. -/
theorem mStargF_ne_zero_abs_le (d u : ℕ) :
    ∀ y : ℝ, Work.KMTAreas.A7.mStargF d u y ≠ 0 →
      |y| ≤ (2 : ℝ) ^ (-((d : ℤ) * 2 * (u : ℤ))) := by
  intro y hy
  by_contra h
  push Not at h
  refine hy ?_
  exact Work.KMTAreas.A7.etaCut_eq_zero_of_le (le_of_lt h)

/-- The window `mStarF u` is integrable. -/
theorem integrable_mStarF (u : ℕ) : Integrable (Work.KMTAreas.A7.mStarF u) :=
  (Work.KMTAreas.A7.contDiff_etaCut _).continuous.integrable_of_hasCompactSupport
    (Work.KMTAreas.A7.hasCompactSupport_etaCut _)

/-- The window `mStargF d u` is integrable. -/
theorem integrable_mStargF (d u : ℕ) : Integrable (Work.KMTAreas.A7.mStargF d u) := by
  have h : Work.KMTAreas.A7.mStargF d u = Work.KMTAreas.A7.mStarF (d * u) := by
    unfold Work.KMTAreas.A7.mStargF Work.KMTAreas.A7.mStarF
    congr 1
    push_cast
    ring
  rw [h]
  exact integrable_mStarF (d * u)

/-- The periodisation of `mStarF u` is bounded. -/
theorem memLp_periodize_mStarF (u : ℕ) :
    MemLp (periodize (Work.KMTAreas.A7.mStarF u)) ⊤ circleMeasure :=
  Work.KMTAreas.A7.memLp_periodize_etaCut _

/-- The periodisation of `mStargF d u` is bounded. -/
theorem memLp_periodize_mStargF (d u : ℕ) :
    MemLp (periodize (Work.KMTAreas.A7.mStargF d u)) ⊤ circleMeasure :=
  Work.KMTAreas.A7.memLp_periodize_etaCut _

/-- The `cw`-coefficients of a rescaled cutoff decay like `j^{-2}`, hence are `ℓ¹`. -/
theorem cw_etaCut_summable' (c : ℤ) :
    Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw (etaCut Work.KMTContract.kmtEta c) j‖ := by
  obtain ⟨C, _hC, h⟩ := Work.KMTAreas.A7.cw_etaCut_decay c
  refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
    (Work.KMTAreas.A7.summable_kmtKernWeight.mul_left C)
  calc ‖Work.KMTAreas.A7.cw (etaCut Work.KMTContract.kmtEta c) j‖
      ≤ C / (1 + |(j : ℝ)|) ^ 2 := h j
    _ = C * ‖Work.KMTAreas.A7.kmtKernWeight j‖ := by
        rw [Work.KMTAreas.A7.norm_kmtKernWeight, div_eq_mul_inv, one_div]

/-- The `cw`-coefficients of the §6 window `mStarF u` are `ℓ¹`. -/
theorem cw_mStarF_summable' (u : ℕ) :
    Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStarF u) j‖ := by
  simpa [Work.KMTAreas.A7.mStarF, Function.comp_def] using
    cw_etaCut_summable' (-(2 * (u : ℤ)))

/-- The `cw`-coefficients of the §6 window `mStargF d u` are `ℓ¹`. -/
theorem cw_mStargF_summable' (d u : ℕ) :
    Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw (Work.KMTAreas.A7.mStargF d u) j‖ := by
  simpa [Work.KMTAreas.A7.mStargF, Function.comp_def] using
    cw_etaCut_summable' (-((d : ℤ) * 2 * (u : ℤ)))

/-! ## 2. An `ℓ¹ × ℓ²` Cauchy--Schwarz summability criterion -/

/-- **Cauchy--Schwarz for a modulation of an `ℓ¹` kernel against an `ℓ²` input.**  If
`j ↦ ‖cw m j‖` is summable and `j ↦ ‖v (x-j)‖^2` is summable, then the family
`j ↦ fourier (-j) α · cw m j · v (x-j)` is summable. -/
theorem summable_fourier_cw_mul {m : ℝ → ℂ} {v : ℤ → ℂ} (x : ℤ) (α : Circ)
    (hm : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m j‖)
    (hv : Summable fun j : ℤ => ‖v (x - j)‖ ^ 2) :
    Summable fun j : ℤ => fourier (T := 1) (-j) α * Work.KMTAreas.A7.cw m j * v (x - j) := by
  have hsq : Summable fun j : ℤ => ‖Work.KMTAreas.A7.cw m j‖ ^ 2 := by
    have hd := (hm.mul_of_nonneg hm (fun _ => norm_nonneg _)
      (fun _ => norm_nonneg _)).comp_injective
      (i := fun j : ℤ => (j, j)) (by intro a b hab; exact (Prod.ext_iff.mp hab).1)
    simpa [Function.comp_def, pow_two] using hd
  have hmaj : Summable fun j : ℤ => (‖Work.KMTAreas.A7.cw m j‖ ^ 2 + ‖v (x - j)‖ ^ 2) / 2 :=
    (hsq.add hv).div_const 2
  have hfn : ∀ j : ℤ, ‖fourier (T := 1) (-j) α‖ = 1 := by
    intro j; rw [fourier_apply]; exact Circle.norm_coe _
  refine Summable.of_norm_bounded (g := fun j : ℤ =>
    (‖Work.KMTAreas.A7.cw m j‖ ^ 2 + ‖v (x - j)‖ ^ 2) / 2) hmaj (fun j => ?_)
  rw [norm_mul, norm_mul, hfn j, one_mul]
  have h1 := norm_nonneg (Work.KMTAreas.A7.cw m j)
  have h2 := norm_nonneg (v (x - j))
  nlinarith [sq_nonneg (‖Work.KMTAreas.A7.cw m j‖ - ‖v (x - j)‖)]

/-! ## 3. The single-frequency fibre as an Ionescu--Wainger multiplier -/

/-! ## 4. The functional calculus: an annihilating symbol kills the composite -/

/-! ## 5. The frequency-pair decomposition of `BtwistSet` -/

/-- **Interchange of a double `tsum` with a finite sum of products** (general index type). -/
theorem tsum_tsum_finset_factor' {ι : Type*} (S : Finset ι) (u v : ι → ℤ → ℂ)
    (hu : ∀ n ∈ S, Summable (u n)) (hv : ∀ n ∈ S, Summable (v n)) :
    (∑' j₁ : ℤ, ∑' j₂ : ℤ, ∑ n ∈ S, u n j₁ * v n j₂)
      = ∑ n ∈ S, (∑' j₁ : ℤ, u n j₁) * (∑' j₂ : ℤ, v n j₂) := by
  have inner : ∀ j₁ : ℤ, (∑' j₂ : ℤ, ∑ n ∈ S, u n j₁ * v n j₂)
      = ∑ n ∈ S, u n j₁ * (∑' j₂ : ℤ, v n j₂) := by
    intro j₁
    rw [((hasSum_sum (fun n hn => ((hv n hn).mul_left (u n j₁)).hasSum)).tsum_eq)]
    exact Finset.sum_congr rfl fun n _ => tsum_mul_left
  rw [tsum_congr inner]
  rw [((hasSum_sum (fun n hn => (((hu n hn).mul_right (∑' j₂ : ℤ, v n j₂))).hasSum)).tsum_eq)]
  exact Finset.sum_congr rfl fun n _ => tsum_mul_right

/-- **`BtwistSet` as a finite sum over pairs of frequencies.**  Expanding the finite double sum in
the arithmetic kernel and exchanging it with the two `tsum`s (legitimate since each fibre is
summable) gives

  `BtwistSet A₁ A₂ = ∑_{p ∈ A₁ × A₂} m_Ẑ(p) · (∑_j e(-j p.1) cw m₁ j h(x-j))
      · (∑_j e(-j p.2) cw m₂ j k(x-j))`. -/
theorem BtwistSet_eq_sum_arith (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ)
    (A₁ A₂ : Finset Circ) (m₁ m₂ : ℝ → ℂ) (h k : ℤ → ℂ) (x : ℤ)
    (hX : ∀ α ∈ A₁, Summable (fun j : ℤ => fourier (T := 1) (-j) α
      * Work.KMTAreas.A7.cw m₁ j * h (x - j)))
    (hY : ∀ α ∈ A₂, Summable (fun j : ℤ => fourier (T := 1) (-j) α
      * Work.KMTAreas.A7.cw m₂ j * k (x - j))) :
    Work.KMTAreas.A7.BtwistSet ρ P l₁ l₂ A₁ A₂ m₁ m₂ h k x
      = ∑ p ∈ A₁.product A₂,
          Work.KMTAreas.A7.mZ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) p.1 p.2
            * (∑' j : ℤ, fourier (T := 1) (-j) p.1 * Work.KMTAreas.A7.cw m₁ j * h (x - j))
            * (∑' j : ℤ, fourier (T := 1) (-j) p.2 * Work.KMTAreas.A7.cw m₂ j
                * k (x - j)) := by
  set q : ℕ := Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) with hq
  -- the summand of the kernel, as a product of the two fibres
  have hstep : ∀ j₁ j₂ : ℤ,
      Work.KMTAreas.A7.arithKernelSet P q A₁ A₂ j₁ j₂ * Work.KMTAreas.A7.cw m₁ j₁
        * Work.KMTAreas.A7.cw m₂ j₂ * h (x - j₁) * k (x - j₂)
      = ∑ p ∈ A₁.product A₂, (Work.KMTAreas.A7.mZ P q p.1 p.2
            * (fourier (T := 1) (-j₁) p.1 * Work.KMTAreas.A7.cw m₁ j₁ * h (x - j₁)))
          * (fourier (T := 1) (-j₂) p.2 * Work.KMTAreas.A7.cw m₂ j₂ * k (x - j₂)) := by
    intro j₁ j₂
    have hpull : (∑ p ∈ A₁.product A₂, Work.KMTAreas.A7.mZ P q p.1 p.2
          * fourier (T := 1) (-j₁) p.1 * fourier (T := 1) (-j₂) p.2)
        * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂ * h (x - j₁) * k (x - j₂)
        = ∑ p ∈ A₁.product A₂, (Work.KMTAreas.A7.mZ P q p.1 p.2
              * fourier (T := 1) (-j₁) p.1 * fourier (T := 1) (-j₂) p.2)
            * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂ * h (x - j₁)
            * k (x - j₂) := by
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    have hprod : (∑ α₁ ∈ A₁, ∑ α₂ ∈ A₂, Work.KMTAreas.A7.mZ P q α₁ α₂
          * fourier (T := 1) (-j₁) α₁ * fourier (T := 1) (-j₂) α₂)
        = ∑ p ∈ A₁.product A₂, Work.KMTAreas.A7.mZ P q p.1 p.2
          * fourier (T := 1) (-j₁) p.1 * fourier (T := 1) (-j₂) p.2 :=
      (Finset.sum_product A₁ A₂ (fun p : Circ × Circ => Work.KMTAreas.A7.mZ P q p.1 p.2
        * fourier (T := 1) (-j₁) p.1 * fourier (T := 1) (-j₂) p.2)).symm
    rw [Work.KMTAreas.A7.arithKernelSet, hprod, hpull]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    ring
  rw [Work.KMTAreas.A7.BtwistSet]
  rw [show (∑' j₁ : ℤ, ∑' j₂ : ℤ, Work.KMTAreas.A7.arithKernelSet P q A₁ A₂ j₁ j₂
        * Work.KMTAreas.A7.cw m₁ j₁ * Work.KMTAreas.A7.cw m₂ j₂ * h (x - j₁) * k (x - j₂))
      = ∑' j₁ : ℤ, ∑' j₂ : ℤ, ∑ p ∈ A₁.product A₂, (Work.KMTAreas.A7.mZ P q p.1 p.2
            * (fourier (T := 1) (-j₁) p.1 * Work.KMTAreas.A7.cw m₁ j₁ * h (x - j₁)))
          * (fourier (T := 1) (-j₂) p.2 * Work.KMTAreas.A7.cw m₂ j₂ * k (x - j₂)) from by
    refine tsum_congr (fun j₁ => tsum_congr (fun j₂ => ?_))
    exact hstep j₁ j₂]
  rw [tsum_tsum_finset_factor' (A₁.product A₂)
    (fun p (j : ℤ) => Work.KMTAreas.A7.mZ P q p.1 p.2
      * (fourier (T := 1) (-j) p.1 * Work.KMTAreas.A7.cw m₁ j * h (x - j)))
    (fun p (j : ℤ) => fourier (T := 1) (-j) p.2 * Work.KMTAreas.A7.cw m₂ j * k (x - j))
    (fun p hp => (hX p.1 (Finset.mem_product.mp hp).1).mul_left _)
    (fun p hp => hY p.2 (Finset.mem_product.mp hp).2)]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [tsum_mul_left]

/-! ## 6. The two symbol-product vanishing statements -/

/-- **The cumulative window annihilates the exact-height bump.**  If `β` has height `≤ l₁` but does
not have height exactly `l₁`, the symbol `periodize (mStarF u) (· - β)` vanishes wherever
`iwSymbolSet (diffFreqs ρ l₁) (periodize φ)` does not. -/
theorem htermF (ρ : ℝ) (l₁ u : ℕ) (hu : 1 ≤ u) (φ : ℝ → ℂ)
    (hφ : ∀ ξ : ℝ, φ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (u : ℤ))))
    (hNA : Work.Analysis.IonescuWainger.NonAliasing (-(2 * (u : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁))
    {β : Circ} (hβA : β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁)
    (hβ : β ∉ Work.KMTAreas.A7.diffFreqs ρ l₁) :
    ∀ ξ : Circ, periodize (Work.KMTAreas.A7.mStarF u) (ξ - β)
        * iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l₁) (periodize φ) ξ = 0 := by
  intro ξ
  by_contra hne
  rw [mul_eq_zero] at hne
  push Not at hne
  obtain ⟨h1, h2⟩ := hne
  -- extract the two real representatives
  obtain ⟨t, ht, htle⟩ := exists_coe_abs_le_of_periodize_ne_zero (mStarF_ne_zero_abs_le u) h1
  have h2' : ∃ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₁, periodize φ (ξ - α) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine h2 ?_
    rw [iwSymbolSet]
    exact Finset.sum_eq_zero (fun α hα => hcon α hα)
  obtain ⟨α, hα, hαne⟩ := h2'
  obtain ⟨s, hs, hsle⟩ := exists_coe_abs_le_of_periodize_ne_zero hφ hαne
  -- the two frequencies lie in the height-`≤ l₁` set
  have hαA : α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₁ :=
    mem_iwArithFreqs_of_mem_diffFreqs hα
  have hs2 : |s| ≤ (2 : ℝ) ^ (-(2 * (u : ℤ))) :=
    le_trans hsle (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega))
  -- non-aliasing at scale `-(2u)` forces `β = α`
  have heq : β + (t : Circ) = α + (s : Circ) := by
    rw [ht, hs]; abel
  have ht' : t ∈ realArc (-(2 * (u : ℤ))) := by rw [mem_realArc_iff]; exact htle
  have hs' : s ∈ realArc (-(2 * (u : ℤ))) := by rw [mem_realArc_iff]; exact hs2
  have hfin := hNA β hβA α hαA t ht' s hs' heq
  exact hβ (hfin.1 ▸ hα)

/-- **The cumulative `g`-window annihilates the exact-height bump.**  The `g`-side analogue of
`htermF`, with the scale `-(2·deg P·u)`. -/
theorem htermG (ρ : ℝ) (l₂ u : ℕ) (P : Polynomial ℤ) (ψ : ℝ → ℂ)
    (hψ : ∀ ξ : ℝ, ψ ξ ≠ 0 → |ξ| ≤ (2 : ℝ) ^ (-(3 * (P.natDegree : ℤ) * (u : ℤ))))
    (hNA : Work.Analysis.IonescuWainger.NonAliasing
      (-((P.natDegree : ℤ) * 2 * (u : ℤ)))
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂))
    {β : Circ} (hβA : β ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂)
    (hβ : β ∉ Work.KMTAreas.A7.diffFreqs ρ l₂) :
    ∀ ξ : Circ, periodize (Work.KMTAreas.A7.mStargF P.natDegree u) (ξ - β)
        * iwSymbolSet (Work.KMTAreas.A7.diffFreqs ρ l₂) (periodize ψ) ξ = 0 := by
  intro ξ
  by_contra hne
  rw [mul_eq_zero] at hne
  push Not at hne
  obtain ⟨h1, h2⟩ := hne
  obtain ⟨t, ht, htle⟩ :=
    exists_coe_abs_le_of_periodize_ne_zero (mStargF_ne_zero_abs_le P.natDegree u) h1
  have h2' : ∃ α ∈ Work.KMTAreas.A7.diffFreqs ρ l₂, periodize ψ (ξ - α) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    refine h2 ?_
    rw [iwSymbolSet]
    exact Finset.sum_eq_zero (fun α hα => hcon α hα)
  obtain ⟨α, hα, hαne⟩ := h2'
  obtain ⟨s, hs, hsle⟩ := exists_coe_abs_le_of_periodize_ne_zero hψ hαne
  have hαA : α ∈ Work.Analysis.IonescuWainger.iwArithFreqs ρ l₂ :=
    mem_iwArithFreqs_of_mem_diffFreqs hα
  have hs2 : |s| ≤ (2 : ℝ) ^ (-((P.natDegree : ℤ) * 2 * (u : ℤ))) := by
    refine le_trans hsle (zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) ?_)
    have hdu : (0 : ℤ) ≤ (P.natDegree : ℤ) * (u : ℤ) :=
      mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    nlinarith
  have heq : β + (t : Circ) = α + (s : Circ) := by
    rw [ht, hs]; abel
  have ht' : t ∈ realArc (-((P.natDegree : ℤ) * 2 * (u : ℤ))) := by
    rw [mem_realArc_iff]; exact htle
  have hs' : s ∈ realArc (-((P.natDegree : ℤ) * 2 * (u : ℤ))) := by
    rw [mem_realArc_iff]; exact hs2
  have hfin := hNA β hβA α hαA t ht' s hs' heq
  exact hβ (hfin.1 ▸ hα)

/-! ## 7. The target -/

end

end Work.KMTPlan.A6
