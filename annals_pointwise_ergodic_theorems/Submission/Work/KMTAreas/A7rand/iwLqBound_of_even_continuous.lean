/-
# The Ionescu–Wainger multiplier bound at an arbitrary exponent `1 < p < ∞`,
from the even exponents

Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial averages*,
Annals of Math. 195 (2022): Appendix `iw-app` (Theorem `thm:iw`) proves the vector-valued
Ionescu–Wainger multiplier bound

  `‖T^{≤l}_φ‖_{ℓ^q(ℤ;H) → ℓ^q(ℤ;H)} ≤ C_{ρ,q} ⟨l⟩ ‖T_φ‖_{L^q(ℝ) → L^q(ℝ)}`

only for the exponents `q ∈ 2ℕ ∪ (2ℕ)'` (the deep input `[MSZ3, Theorem 2.1]`, isolated in this
workspace as `Work.Analysis.IWMultiplier.IWMultiplierBoundStatement_even`, i.e. `AreaA1`).  By
Remark `rem:1`(iv) of the paper, every exponent `1 < q < ∞` then follows by interpolation.

This file carries out that interpolation in the following form: given the *continuous* multiplier
bounds `IsLqMultiplierBound (2k₀) Φ M` and `IsLqMultiplierBound (2k₀) (star ∘ Φ) M` for the even
exponents `2k₀`, `2 ≤ k₀ ≤ K₀`, together with the numerical hypothesis
`max p (p/(p-1)) ≤ 2K₀`, the IW projection `T^{≤l}_φ` is bounded on `ℓ^p(ℤ;H)` with constant
`C ⟨l⟩ M`, `C = C_{ρ,p}` independent of `l`, `k`, `K₀` and `M`.

The scheme is the natural one.  Let `r = max p (p/(p-1))` and `k = max 2 ⌈r/2⌉₊`.  Then `k ≤ K₀`
and both `p` and its Hölder dual `p/(p-1)` lie in the interval `[(2k)', 2k]` between the dual-even
and the even exponent attached to the *single* exponent `2k`.  Area `A1` applied to `Φ` at `2k`
gives the `ℓ^{2k}` bound, and area `A1` applied to `star ∘ Φ` at `2k` followed by the discrete
duality `IWLqBound_of_dual` (the adjoint of the IW multiplier has the conjugate symbol) gives the
`ℓ^{(2k)'}` bound for the *same* symbol `periodize Φ` and the *same* constant.  Riesz–Thorin
interpolation (`IWLqBound_interpolation`) between those two endpoints then gives the bound at any
intermediate exponent — in particular at `p`.  Using a single even exponent `2k` (rather than
interpolating between two *different* even exponents) is what makes the interpolated constant
`= C_{ρ,k} ⟨l⟩ M` independent of `K₀`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.IwLqGeneral

set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7rand

open scoped ENNReal NNReal
open MeasureTheory

/-- **Exponent arithmetic.**  With `r = max p (p/(p-1))`, `p > 1`, `2 ≤ K₀` and `r ≤ 2K₀`, the
integer `k = max 2 ⌈r/2⌉₊` satisfies `2 ≤ k ≤ K₀`, both `p` and `p/(p-1)` are at most the even
exponent `2k`, and `p` is at least its Hölder dual `(2k)' = 2k/(2k-1)`.

The last two conjuncts say exactly that `p ∈ [(2k)', 2k]`, which is the interval on which the
Riesz–Thorin interpolation between the exponents `(2k)'` and `2k` is available. -/
lemma ceil_half_arith (p : ℝ) (hp : 1 < p) (K₀ : ℕ) (hK₀ : 2 ≤ K₀) (k : ℕ)
    (hk : k = max 2 ⌈max p (p / (p - 1)) / 2⌉₊)
    (hmax : max p (p / (p - 1)) ≤ 2 * (K₀ : ℝ)) :
    2 ≤ k ∧ k ≤ K₀ ∧ p ≤ 2 * (k : ℝ) ∧ p / (p - 1) ≤ 2 * (k : ℝ) ∧
      (2 * (k : ℝ)) / (2 * (k : ℝ) - 1) ≤ p := by
  have hden : (0 : ℝ) < p - 1 := by linarith
  have hkn : (⌈max p (p / (p - 1)) / 2⌉₊ : ℝ) ≤ (k : ℝ) := by
    rw [hk]
    exact_mod_cast (le_max_right (2 : ℕ) ⌈max p (p / (p - 1)) / 2⌉₊)
  have hk2' : (2 : ℝ) ≤ (k : ℝ) := by
    rw [hk]
    exact_mod_cast (le_max_left (2 : ℕ) ⌈max p (p / (p - 1)) / 2⌉₊)
  have hceil : max p (p / (p - 1)) / 2 ≤ (⌈max p (p / (p - 1)) / 2⌉₊ : ℝ) := Nat.le_ceil _
  have hpk : p ≤ 2 * (k : ℝ) := by
    have h1 : p ≤ max p (p / (p - 1)) := le_max_left _ _
    linarith
  have hp'k : p / (p - 1) ≤ 2 * (k : ℝ) := by
    have h1 : p / (p - 1) ≤ max p (p / (p - 1)) := le_max_right _ _
    linarith
  have hkK : k ≤ K₀ := by
    rw [hk]
    refine max_le hK₀ ?_
    refine Nat.ceil_le.mpr ?_
    linarith
  refine ⟨?_, hkK, hpk, hp'k, ?_⟩
  · rw [hk]; exact le_max_left _ _
  · rw [div_le_iff₀ (by linarith : (0 : ℝ) < 2 * (k : ℝ) - 1)]
    have h := (div_le_iff₀ hden).mp hp'k
    nlinarith [h]

/-- **One Riesz–Thorin step between the dual-even exponent `q₀` and the even exponent `q₁`**, with
the *same* constant `C * a * M` at both endpoints.  Riesz–Thorin interpolation gives the bound at
every intermediate exponent with the interpolated constant `(C a M)^{1-θ} (C a M)^θ`, which
`rpow_mul_const` rewrites as `(C^{1-θ} C^θ) a M = C a M`. -/
lemma IWLqBound_of_two {A : Finset (AddCircle (1 : ℝ))} {Ψ : AddCircle (1 : ℝ) → ℂ}
    {C a M : ℝ≥0} {q₀ q₁ p : ℝ} (hC : C ≠ 0) (ha : a ≠ 0)
    (hlo : Work.Analysis.IWMultiplier.IWLqBound A Ψ (ENNReal.ofReal q₀) (C * a * M))
    (hhi : Work.Analysis.IWMultiplier.IWLqBound A Ψ (ENNReal.ofReal q₁) (C * a * M))
    (hq₀ : 1 < q₀) (hq₀q₁ : q₀ < q₁) (hap : q₀ ≤ p) (hpb : p ≤ q₁) :
    Work.Analysis.IWMultiplier.IWLqBound A Ψ (ENNReal.ofReal p) (C * a * M) := by
  have hq₀pos : 0 < q₀ := lt_trans zero_lt_one hq₀
  have hq₁ : 1 < q₁ := lt_trans hq₀ hq₀q₁
  have hp0 : 0 < p := lt_of_lt_of_le hq₀pos hap
  have hmem := Work.KMTAreas.A7.interpTheta_mem (a := q₀) (b := q₁) (p := p)
    hq₀pos hq₀q₁ hap hpb
  set θ : ℝ := Work.KMTAreas.A7.interpTheta q₀ q₁ p with hθdef
  obtain ⟨hθ0, hθ1, hθeq⟩ := hmem
  have h := Work.KMTAreas.A7.iwLqBound_of_pair (q₀ := q₀) (q₁ := q₁) (p := p)
    (C₀ := C) (C₁ := C) (a := a) (M := M) (θ := θ) hlo hhi hq₀ hq₁ hθ0 hθ1 hp0 hθeq ha
  have hCeq : C ^ (1 - θ) * C ^ θ = C := by
    rw [← NNReal.rpow_add hC, show 1 - θ + θ = 1 by ring, NNReal.rpow_one]
  rwa [hCeq] at h

theorem iwLqBound_of_even_continuous (hA1 : Work.KMTContract.AreaA1) (p : ℝ) (hp : 1 < p) :
    ∀ (ρ : ℝ), 0 < ρ → ρ ≤ 1 → ∃ Cρ : ℝ, 0 < Cρ ∧ ∃ C : NNReal, 0 < C ∧
      ∀ (l : ℕ) (k : ℤ), Work.Analysis.IonescuWainger.GoodMajorArcs ρ Cρ l k →
      ∀ (Φ : SchwartzMap ℝ ℂ), (∀ x, Φ x ≠ 0 → x ∈ Work.Analysis.IonescuWainger.realArc k) →
      ∀ (K₀ : ℕ), 2 ≤ K₀ → max p (p / (p - 1)) ≤ 2 * (K₀ : ℝ) → ∀ (M : NNReal),
        (∀ k₀ : ℕ, 2 ≤ k₀ → k₀ ≤ K₀ →
          Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal ((2 * k₀ : ℕ) : ℝ))
            (Φ : ℝ → ℂ) M) →
        (∀ k₀ : ℕ, 2 ≤ k₀ → k₀ ≤ K₀ →
          Work.Analysis.IWMultiplier.IsLqMultiplierBound (ENNReal.ofReal ((2 * k₀ : ℕ) : ℝ))
            (fun x : ℝ => star (Φ x)) M) →
        Work.Analysis.IWMultiplier.IWLqBound (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
          (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ)) (ENNReal.ofReal p)
          (C * Work.Analysis.IWMultiplier.angleBracket l * M) := by
  intro ρ hρ hρ1
  rw [Work.KMTContract.areaA1_iff] at hA1
  obtain ⟨Cρ, hCρ, _hNA, hevenA1⟩ := hA1 ρ hρ hρ1
  set k₁ : ℕ := max 2 ⌈max p (p / (p - 1)) / 2⌉₊ with hk₁def
  obtain ⟨C, hCpos, hCb⟩ := hevenA1 k₁ (by rw [hk₁def]; exact le_max_left _ _)
  refine ⟨Cρ, hCρ, C, hCpos, ?_⟩
  intro l kk hgood Φ hsupp K₀ hK₀ hmax M hM hMs
  obtain ⟨hk2, hkK₀, hp2k, hp'2k, hlast⟩ := ceil_half_arith p hp K₀ hK₀ k₁ hk₁def hmax
  -- the even-exponent bounds for `Φ` and for `star ∘ Φ`, at the single exponent `2k₁`
  have htwo : Work.Analysis.IWMultiplier.IsLqMultiplierBound ((2 * k₁ : ℕ) : ℝ≥0∞)
      (Φ : ℝ → ℂ) M := by
    have h := hM k₁ hk2 hkK₀
    rwa [Work.KMTAreas.A7.ofReal_two_mul] at h
  have hbound := hCb l kk hgood Φ hsupp M htwo
  have hsupstar : ∀ x, Work.KMTAreas.A7.starSchwartz Φ x ≠ 0 →
      x ∈ Work.Analysis.IonescuWainger.realArc kk :=
    fun x hx => hsupp x (Work.KMTAreas.A7.starSchwartz_ne_zero hx)
  have htwostar : Work.Analysis.IWMultiplier.IsLqMultiplierBound ((2 * k₁ : ℕ) : ℝ≥0∞)
      ((Work.KMTAreas.A7.starSchwartz Φ : SchwartzMap ℝ ℂ) : ℝ → ℂ) M := by
    rw [Work.KMTAreas.A7.starSchwartz_coe]
    have h := hMs k₁ hk2 hkK₀
    rwa [Work.KMTAreas.A7.ofReal_two_mul] at h
  have hboundstar := hCb l kk hgood (Work.KMTAreas.A7.starSchwartz Φ) hsupstar M htwostar
  rw [Work.KMTAreas.A7.starSchwartz_coe] at hboundstar
  -- duality: the `ℓ^{(2k₁)'}` bound for `Φ` from the `ℓ^{2k₁}` bound for `star ∘ Φ`
  have hdual := Work.Analysis.IWMultiplier.IWLqBound_of_dual
    (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
    (Work.Analysis.IonescuWainger.periodize (fun x : ℝ => star ((Φ : ℝ → ℂ) x)))
    hboundstar (by rw [ENNReal.toReal_natCast]; exact_mod_cast (show 1 < 2 * k₁ by omega))
  simp only [ENNReal.toReal_natCast] at hdual
  have hsym : (fun ξ => star (Work.Analysis.IonescuWainger.periodize
      (fun x : ℝ => star ((Φ : ℝ → ℂ) x)) ξ))
      = Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ) :=
    funext (fun ξ => Work.KMTAreas.A7.periodize_star (Φ : ℝ → ℂ) ξ)
  rw [hsym] at hdual
  -- the even-exponent bound for `Φ`, in `ofReal` form
  have hhi : Work.Analysis.IWMultiplier.IWLqBound
      (Work.Analysis.IonescuWainger.iwArithFreqs ρ l)
      (Work.Analysis.IonescuWainger.periodize (Φ : ℝ → ℂ))
      (ENNReal.ofReal (((2 * k₁ : ℕ) : ℝ)))
      (C * Work.Analysis.IWMultiplier.angleBracket l * M) := by
    rw [ENNReal.ofReal_natCast]
    exact hbound
  have hQcast : ((2 * k₁ : ℕ) : ℝ) = 2 * (k₁ : ℝ) := by push_cast; ring
  refine IWLqBound_of_two (C := C) (a := Work.Analysis.IWMultiplier.angleBracket l) (M := M)
    (ne_of_gt hCpos) (ne_of_gt (Work.Analysis.IWMultiplier.angleBracket_pos l))
    hdual hhi ?_ ?_ ?_ ?_
  · rw [hQcast]
    rw [one_lt_div (by linarith : (0 : ℝ) < 2 * (k₁ : ℝ) - 1)]
    linarith
  · rw [hQcast, div_lt_iff₀ (by linarith : (0 : ℝ) < 2 * (k₁ : ℝ) - 1)]
    have hk2' : (2 : ℝ) ≤ (k₁ : ℝ) := by exact_mod_cast hk2
    nlinarith [hk2']
  · rw [hQcast]; exact hlast
  · rw [hQcast]; exact hp2k

end Work.KMTAreas.A7rand
