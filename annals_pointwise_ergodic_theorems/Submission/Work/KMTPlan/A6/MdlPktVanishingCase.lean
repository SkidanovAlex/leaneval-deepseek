/-
# The packet estimate of §8 at the heights where the bumps vanish at the origin

This is the case `k₁ ≥ 1` (any twist `j₁ ∈ {-1,0,1}`) or `k₁ = 0` with `j₁ = 1` of the paper's
`(lin-1)` for the `f`-side packet family `n ↦ T^{l₁}_{φ_{⌊a n⌋,k₁,t,j₁}} (Π_{l₁,≤-u}f)` of
Krause--Mirek--Tao, Annals 195 (2022), §8, in the carrier used by the A6 model tuple `mdlPart`.

In these cases the modified bump is either the annulus-supported `φ_{N,k₁}` (`k₁ ≥ 1`) or the
weighted low-frequency profile `(Nξ)φ_N` (`k₁ = 0`, `j₁ = 1`), and in both cases the signed sums
of the bumps are *pointwise* bounded by a constant depending only on the lacunarity parameter
(`Work.KMTPlan.A6.MdlLinVarphiNtjSupBound`).  Hence the Marcinkiewicz--Zygmund transfer of
uniform-in-signs `ℓ²` bounds (`Work.KMTPlan.A6.mdlVanishingCaseUnif`) applies, and the resulting
constant is absorbed into the weight `lossWeight 2 ρ l₁ l₂ k₁ k₂`.

This is the `¬(k₁ = 0 ∧ j₁ = 0)` half of `Work.KMTPlan.A6.MdlSlicePktLinF`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.MdlSliceLinF

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Work.KMTPlan.A6

open MeasureTheory
open scoped ENNReal NNReal BigOperators

/-- **The packet estimate in the cases where the bump family has bounded signed sums**: for
`k₁ ≥ 1` (any `j₁ ∈ {-1,0,1}`) and for `(k₁,j₁) = (0,1)` the clipped packet family
`n ↦ 1_{mdlCore} · Tle ρ l₁ (φ_{⌊a n⌋,k₁,j₁,t}) (mdlF ρ (uScale ρ L) l₁ f)` obeys the variational
estimate with the weight `lossWeight 2 ρ l₁ l₂ k₁ k₂`. -/
theorem MdlPktVanishingCase (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (R : NNReal) (hR : 2 < R)
    (j₁ : ℤ) (hj₁ : j₁ ∈ ({-1, 0, 1} : Finset ℤ)) :
    ∃ ρ₀ : ℝ, 0 < ρ₀ ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ ρ₀ → ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → NNReal) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₁ = 0 → j₁ = 1) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ =>
              if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
                Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ j₁ t)
                  (Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ
                    (max (max l₁ l₂) (max k₁ k₂))) l₁ f) x
              else 0)) 2 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) *
              ENNReal.ofReal (Work.KMTAreas.A7.lossWeight 2 ρ l₁ l₂ k₁ k₂) *
              MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
  classical
  refine ⟨1, one_pos, fun ρ hρ hρ1 => ?_⟩
  -- For every `Λ > 1` we have a uniform real constant.
  have hkey : ∀ Λ : NNReal, 1 < Λ → ∃ K : ℝ, 0 < K ∧
      ∀ (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f : ℤ → ℂ),
        PointwiseErgodicTheorems.Lacunary Λ a → (∀ n : ℕ, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 → (k₁ = 0 → j₁ = 1) →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm R
            (fun n : ℕ =>
              if Work.KMTPlan.A6.mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
                Work.KMTAreas.A7.Tle ρ l₁ (Work.KMTPlan.A6.varphiNtj (Nat.floor (a n)) k₁ j₁ t)
                  (Work.KMTPlan.A6.mdlF ρ (Work.KMTAreas.A7.uScale ρ
                    (max (max l₁ l₂) (max k₁ k₂))) l₁ f) x
              else 0)) 2 MeasureTheory.Measure.count
          ≤ ENNReal.ofReal K * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count := by
    intro Λ hΛ
    obtain ⟨C, hCpos, hCk, hC0⟩ := MdlLinVarphiNtjSupBound Λ hΛ
    obtain ⟨Kv, hKvpos, hKv⟩ :=
      mdlVanishingCaseUnif ρ hρ hρ1 C₀ R hR j₁ (max 1 C) (le_max_left 1 C)
    refine ⟨Kv, hKvpos, ?_⟩
    intro a l₁ l₂ k₁ k₂ t f ha ha1 ht hk
    refine hKv a Λ l₁ l₂ k₁ k₂ t f hΛ ha ha1 ?_
    intro U ω ξ
    rcases Nat.eq_zero_or_pos k₁ with h0 | hpos
    · subst h0
      obtain rfl := hk rfl
      exact le_trans (hC0 t ht a ha ha1 U ω ξ) (le_max_right 1 C)
    · exact le_trans (hCk k₁ hpos j₁ hj₁ t ht a ha ha1 U ω ξ) (le_max_right 1 C)
  let Kfun : NNReal → NNReal := fun Λ =>
    ⟨max 1 (if h : 1 < Λ then Classical.choose (hkey Λ h) else 0),
      le_trans zero_le_one (le_max_left 1 _)⟩
  refine ⟨Kfun, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t f hΛ ha ha1 ht hk
  have hKval : Classical.choose (hkey Λ hΛ) ≤ ((Kfun Λ : NNReal) : ℝ) := by
    dsimp only [Kfun]
    rw [dif_pos hΛ]
    exact le_max_right 1 _
  have hbound := (Classical.choose_spec (hkey Λ hΛ)).2 a l₁ l₂ k₁ k₂ t f ha ha1 ht hk
  exact hbound.trans
    (ofReal_mul_le_nnreal_mul_lossWeight (K := Classical.choose (hkey Λ hΛ))
      (Kn := Kfun Λ) hKval hρ.le l₁ l₂ k₁ k₂ _)
