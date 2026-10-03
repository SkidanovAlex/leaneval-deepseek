/-
# `EtaProjGeTwo`: the Ionescu--Wainger bound for the periodised KMT cutoff, all exponents `q ≥ 2`

This file proves the area-`A7` lemma `Work.KMTAreas.A7.EtaProjGeTwo`.

Area `A1` (`Work.KMTContract.AreaA1`, the frozen contract's form of the Ionescu--Wainger
multiplier theorem, MSZ3 Theorem 2.1) supplies the multiplier bound

`‖T^{≤l}_{η_{≤k}}‖_{ℓ^q(ℤ;H)} ≤ C_ρ ⟨l⟩ M`,   `q ∈ {2k₀ : k₀ ≥ 2}`,

on good major arcs, for every Schwartz symbol supported in `ℝ_{≤k}` whose *continuous* multiplier
`T_φ` is bounded on `L^q(ℝ)` by `M` — tested on `φ = η_{≤k}`, whose continuous multiplier bound is
the hypothesis `hMbound` of the statement.  The task is to extend this to **all** real exponents
`q ≥ 2` (the paper's Remark `rem:1`(iv): *"by applying (iw-mult) for `q ∈ 2ℕ ∪ (2ℕ)'` and then
interpolating we can recover good bounds for all `1 < q < ∞`"*).

The proof is the routine Riesz--Thorin step, using

* the *proved* `q = 2` case of the multiplier theorem (`IWMultiplierBound_q2_vector`, valid for
  the KMT cutoff by compact support and the pointwise bound `‖η_{≤k}‖ ≤ 1`), which anchors the
  interpolation from below;
* the *proved* interpolation `IWLqBound_interpolation`, which produces the bound at the
  intermediate exponent with constant `C₀^{1-θ} C₁^θ`;
* an even exponent `2k₀ ≥ max(q,4)` supplied by area `A1`, anchoring it from above.

Both anchors carry a factor `⟨l⟩` (the `q = 2` case `⟨l⟩·1`, the even case `C_ρ⟨l⟩M`); since
`⟨l⟩ ≥ 1`, the interpolated constant is *again* `≲ ⟨l⟩`, uniformly in `l` and `k`: the constant
`C` of the conclusion is `C_ρ'^θ · (max M 1)^θ`, where `θ = (1/2 - 1/q)/(1/2 - 1/2k₀) ∈ [0,1]`
is the interpolation exponent and `C_ρ'` the constant of the even case.

Nothing here uses the number theory of `(ℚ/ℤ)_{≤l}`: the argument is
`IWMultiplierBoundStatement_even + q = 2  ⟹  all q ≥ 2`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Basic
import Submission.Work.KMTAreas.iw_family

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped ENNReal NNReal BigOperators
open MeasureTheory

namespace Work.KMTAreas.A7

open Work.Analysis.IWMultiplier Work.Analysis.IonescuWainger

/-- **The interpolation exponent.**  For `2 ≤ p ≤ N`, `2 < N`, there is `θ ∈ [0,1]` with
`1/p = (1 - θ)/2 + θ/N`, namely `θ = (1/2 - 1/p)/(1/2 - 1/N)`.

This is the real-variable input of the Riesz--Thorin step: it says that the reciprocal
`1/p` is a convex combination of `1/2` and `1/N` as soon as `p` lies between `2` and `N`. -/
lemma interp_exp_exists {p N : ℝ} (hp2 : 2 ≤ p) (hpN : p ≤ N) (hN : 2 < N) :
    ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ p⁻¹ = (1 - θ) * (2:ℝ)⁻¹ + θ * N⁻¹ := by
  have hp_pos : 0 < p := by linarith
  have hN_pos : 0 < N := by linarith
  have hden_pos : 0 < (2:ℝ)⁻¹ - N⁻¹ := by
    have : N⁻¹ < (2:ℝ)⁻¹ := by
      rw [inv_lt_inv₀ hN_pos (by norm_num : (0:ℝ) < 2)]
      linarith
    linarith
  have hnum_nonneg : 0 ≤ (2:ℝ)⁻¹ - p⁻¹ := by
    have : p⁻¹ ≤ (2:ℝ)⁻¹ := by
      rw [inv_le_inv₀ hp_pos (by norm_num : (0:ℝ) < 2)]
      linarith
    linarith
  have hnum_le : (2:ℝ)⁻¹ - p⁻¹ ≤ (2:ℝ)⁻¹ - N⁻¹ := by
    have : N⁻¹ ≤ p⁻¹ := by
      rw [inv_le_inv₀ hN_pos hp_pos]
      exact hpN
    linarith
  refine ⟨((2:ℝ)⁻¹ - p⁻¹) / ((2:ℝ)⁻¹ - N⁻¹), div_nonneg hnum_nonneg hden_pos.le, ?_, ?_⟩
  · rw [div_le_one hden_pos]
    linarith
  · have hkey : ((2:ℝ)⁻¹ - p⁻¹) / ((2:ℝ)⁻¹ - N⁻¹) * ((2:ℝ)⁻¹ - N⁻¹) = (2:ℝ)⁻¹ - p⁻¹ :=
      div_mul_cancel₀ _ hden_pos.ne'
    calc p⁻¹ = (2:ℝ)⁻¹ - ((2:ℝ)⁻¹ - p⁻¹) := by ring
      _ = (2:ℝ)⁻¹ - (((2:ℝ)⁻¹ - p⁻¹) / ((2:ℝ)⁻¹ - N⁻¹)) * ((2:ℝ)⁻¹ - N⁻¹) := by rw [hkey]
      _ = (1 - ((2:ℝ)⁻¹ - p⁻¹) / ((2:ℝ)⁻¹ - N⁻¹)) * (2:ℝ)⁻¹
            + (((2:ℝ)⁻¹ - p⁻¹) / ((2:ℝ)⁻¹ - N⁻¹)) * N⁻¹ := by ring

/-- **The Ionescu--Wainger bound for `η_{≤k}` at every exponent `q ≥ 2`.**

Area `A1` gives the bound at the even exponents `2k₀ ≥ 4`; the proved `q = 2` case gives the anchor
at `2`; Riesz--Thorin interpolation between the two gives every real exponent `q ≥ 2`, with a
constant which is again `O(⟨l⟩)` uniformly in `l` and `k` (the `⟨l⟩`-factors of the two anchors
interpolate to a single `⟨l⟩`, because `⟨l⟩ ≥ 1`). -/
theorem EtaProjGeTwo (hA1 : Work.KMTContract.AreaA1) {M : NNReal} (hM : 0 < M)
    (hMbound : ∀ (k : ℤ) (p : ENNReal), 1 ≤ p →
      Work.Analysis.IWMultiplier.IsLqMultiplierBound p
        (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k) M) :
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∀ (q : ENNReal), 2 ≤ q → q ≠ ⊤ →
      ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
        ∀ (l : ℕ) (k : ℤ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k →
          Work.Analysis.IWMultiplier.IWLqBound (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
            (Work.Analysis.IonescuWainger.periodize
              (Work.Analysis.IonescuWainger.etaCut Work.KMTContract.kmtEta k)) q
            (C * Work.Analysis.IWMultiplier.angleBracket l) := by
  intro ρ hρ hρ1 q hq2 hqtop
  -- area `A1`: non-aliasing plus the even-exponent multiplier bound
  rw [Work.KMTContract.areaA1_iff] at hA1
  obtain ⟨Cρ₁, hCρ₁, hNA₁, heven⟩ := hA1 ρ hρ hρ1
  -- the exponent `p = q` as a real number
  set p : ℝ := q.toReal with hp
  have hq2' : (2:ℝ) ≤ p := by
    have h := ENNReal.toReal_mono hqtop (a := (2:ENNReal)) (b := q) (by simpa using hq2)
    simpa [p] using h
  -- an even exponent `2k₀ ≥ max(q,4)` above `q`
  obtain ⟨k₀, hk₀2, hpk₀⟩ : ∃ k₀ : ℕ, 2 ≤ k₀ ∧ p ≤ ((2 * k₀ : ℕ) : ℝ) := by
    refine ⟨max 2 (Nat.ceil p), le_max_left _ _, ?_⟩
    have h1 : p ≤ (Nat.ceil p : ℝ) := Nat.le_ceil p
    have h2 : (Nat.ceil p : ℝ) ≤ ((max 2 (Nat.ceil p) : ℕ) : ℝ) := by
      exact_mod_cast le_max_right (2:ℕ) (Nat.ceil p)
    have h3 : ((max 2 (Nat.ceil p) : ℕ) : ℝ) ≤ ((2 * max 2 (Nat.ceil p) : ℕ) : ℝ) := by
      exact_mod_cast (show max 2 (Nat.ceil p) ≤ 2 * max 2 (Nat.ceil p) by omega)
    linarith
  obtain ⟨Cev, hCev, hevenb⟩ := heven k₀ hk₀2
  set N₁ : ℝ := ((2 * k₀ : ℕ) : ℝ) with hN₁
  have hN₁2 : 2 < N₁ := by
    have : (2:ℝ) < ((2 * k₀ : ℕ) : ℝ) := by
      exact_mod_cast (show 2 < 2 * k₀ by omega)
    simpa [N₁] using this
  -- the interpolation exponent
  obtain ⟨θ, hθ0, hθ1, hθeq⟩ := interp_exp_exists hq2' hpk₀ hN₁2
  set M₁ : NNReal := max M 1 with hM₁
  -- the good-arcs constant of the conclusion: at least `2`, and at least the constant of `A1`
  have hNAmax : ∀ (l : ℕ) (k : ℤ), GoodMajorArcs ρ (max Cρ₁ 2) l k →
      NonAliasing k (iwArithFreqs ρ l) :=
    fun l k hk => hNA₁ l k (GoodMajorArcs.mono_const (le_max_left Cρ₁ 2) hk)
  refine ⟨max Cρ₁ 2, lt_of_lt_of_le hCρ₁ (le_max_left Cρ₁ 2), ?_⟩
  refine ⟨Cev ^ θ * M₁ ^ θ, ?_, ?_⟩
  · exact mul_pos (NNReal.rpow_pos hCev) (NNReal.rpow_pos (lt_of_lt_of_le hM (le_max_left M 1)))
  · intro l k hgood
    have hgood₁ : GoodMajorArcs ρ Cρ₁ l k := GoodMajorArcs.mono_const (le_max_left Cρ₁ 2) hgood
    -- the anchor at `q = 2`: the proved `q = 2` case with the pointwise bound `‖η_{≤k}‖ ≤ 1`
    have h2 : IWLqBound (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k)) 2
        (angleBracket l) := by
      have h := IWMultiplierBound_q2_vector (ρ := ρ) (Cρ := max Cρ₁ 2) (l := l) (k := k) hρ
        (le_max_right Cρ₁ 2) hNAmax hgood (φ := etaCut Work.KMTContract.kmtEta k)
        ((contDiff_etaCut k).continuous.measurable)
        (fun x hx => etaCut_ne_zero_mem_realArc k hx)
        (summable_etaCut_shift k) (M := 1)
        (fun x => by simpa using norm_etaCut_le_one k x)
      simpa using h
    -- the anchor at the even exponent `2k₀`, from area `A1`, with the constant upgraded to `M₁`
    have hev : IWLqBound (iwArithFreqs ρ l) (periodize (etaCut Work.KMTContract.kmtEta k))
        (((2*k₀:ℕ):ENNReal)) (Cev * angleBracket l * M₁) := by
      have hMb : IsLqMultiplierBound (((2*k₀:ℕ):ENNReal))
          ((etaCutSchwartz k : SchwartzMap ℝ ℂ) : ℝ → ℂ) M := by
        rw [etaCutSchwartz_coe]
        exact hMbound k _ (by exact_mod_cast (show 1 ≤ 2*k₀ by omega))
      have hraw := hevenb l k hgood₁ (etaCutSchwartz k)
        (fun x hx => etaCut_ne_zero_mem_realArc k
          (by rwa [etaCutSchwartz_coe] at hx)) M hMb
      rw [etaCutSchwartz_coe] at hraw
      refine IWLqBound.mono hraw ?_
      exact mul_le_mul_of_nonneg_left (le_max_left M 1) (by positivity)
    have hq₀ : 1 ≤ (2:ENNReal).toReal := by norm_num
    have hq₁ : 1 ≤ (((2*k₀:ℕ):ENNReal)).toReal := by
      rw [ENNReal.toReal_natCast]
      exact_mod_cast (show 1 ≤ 2*k₀ by omega)
    have heq : q.toReal⁻¹ = (1 - θ) * (2:ENNReal).toReal⁻¹
        + θ * (((2*k₀:ℕ):ENNReal)).toReal⁻¹ := by
      simpa [p, N₁] using hθeq
    -- Riesz--Thorin interpolation between the two anchors
    have hinterp := IWLqBound_interpolation (iwArithFreqs ρ l)
      (periodize (etaCut Work.KMTContract.kmtEta k)) h2 hev hθ0 hθ1 hq₀ hq₁ heq
    refine IWLqBound.mono hinterp ?_
    -- the two `⟨l⟩`-factors interpolate to a single one, because `⟨l⟩ ≥ 1`
    have ha0 : angleBracket l ≠ 0 := ne_of_gt (angleBracket_pos l)
    have ha : (angleBracket l) ^ (1 - θ) * (angleBracket l) ^ θ = angleBracket l := by
      rw [← NNReal.rpow_add ha0, show (1 - θ) + θ = 1 by ring, NNReal.rpow_one]
    have hconst : (angleBracket l) ^ (1 - θ) * ((Cev * angleBracket l * M₁) ^ θ)
        = (Cev ^ θ * M₁ ^ θ) * angleBracket l := by
      calc (angleBracket l) ^ (1 - θ) * ((Cev * angleBracket l * M₁) ^ θ)
          = (angleBracket l) ^ (1 - θ) * ((Cev * angleBracket l) ^ θ * M₁ ^ θ) := by
            rw [NNReal.mul_rpow]
        _ = (angleBracket l) ^ (1 - θ) * ((Cev ^ θ * (angleBracket l) ^ θ) * M₁ ^ θ) := by
            rw [NNReal.mul_rpow]
        _ = (Cev ^ θ * M₁ ^ θ) * ((angleBracket l) ^ (1 - θ) * (angleBracket l) ^ θ) := by ring
        _ = (Cev ^ θ * M₁ ^ θ) * angleBracket l := by rw [ha]
    rw [hconst]

end Work.KMTAreas.A7
