import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Core.geom
import Submission.Work.TMC16Core.Core.nr_ablock
import Submission.Work.TMC16Core.Core.nr_endgame
import Submission.Work.TMC16Core.NrFinal.nr_regular

/-!
# Assembly of the non-resonant case `s ≥ 1` (AJ §9, Lemma 9.4(1))
-/

namespace Work.TMC16Core.Assembly

open Work.TMC16Core
open Work.TMC16Core.Core

noncomputable section

/-- The geometry of `I2nr q n s b' y` with `b' < s ≤ 2 a'`. -/
theorem nr_case1_i2geo {q : ℕ → ℕ} {n s a' b' : ℕ} {y x : ℤ}
    (hab : a' + b' = s) (ha : s ≤ 2 * a') (hs : 1 ≤ s) (hq : 1 ≤ q (n - 1))
    (hK : 40 ≤ Knr q n s) (hx : x ∈ I2nr q n s b' y) :
    x ≤ y ∧ y ≤ x + (Knr q n s : ℤ) - 1 ∧
    (Knr q n s : ℤ) ≤ 40 * (y - x) ∧
    (Knr q n s : ℤ) ≤ 40 * ((x + (Knr q n s : ℤ) - 1) - y) ∧
    ((Knr q n s : ℝ) / 4 - 1) ≤ ((y - x : ℤ) : ℝ) ∧
    ((Knr q n s : ℝ) / 4 - 1) ≤ (((x + (Knr q n s : ℤ) - 1) - y : ℤ) : ℝ) := by
  simp only [I2nr, Finset.mem_Icc] at hx
  obtain ⟨hx1, hx2⟩ := hx
  simp only [Tnr] at hx1 hx2
  have hQ1 : (1 : ℝ) ≤ (q (n - 1) : ℝ) := by exact_mod_cast hq
  have hQR : (0 : ℝ) < (q (n - 1) : ℝ) := by linarith
  have hS1 : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hKcastZ : ((Knr q n s : ℕ) : ℤ) = 2 * (s : ℤ) * (q (n - 1) : ℤ) - 1 := by
    rw [Knr_cast q hs hq]
    simp only [Tnr]
    ring
  have hA2R : (s : ℝ) ≤ 2 * (a' : ℝ) := by exact_mod_cast ha
  have habR : (a' : ℝ) + (b' : ℝ) = (s : ℝ) := by exact_mod_cast hab
  have hbR : (b' : ℝ) ≤ (s : ℝ) := by linarith
  have hKR : ((Knr q n s : ℕ) : ℝ) = 2 * (s : ℝ) * (q (n - 1) : ℝ) - 1 := by
    have h := hKcastZ
    have h2 : (((Knr q n s : ℕ) : ℤ) : ℝ)
        = ((2 * (s : ℤ) * (q (n - 1) : ℤ) - 1 : ℤ) : ℝ) := by rw [h]
    push_cast at h2
    exact h2
  have hx1r : (y : ℝ) - (s : ℝ) * (q (n - 1) : ℝ) + 1 - (b' : ℝ) * (q (n - 1) : ℝ)
      ≤ (x : ℝ) := by
    have h := hx1
    exact_mod_cast h
  have hx2r : (x : ℝ) ≤ (y : ℝ) - (s : ℝ) * (q (n - 1) : ℝ)
      + (b' : ℝ) * (q (n - 1) : ℝ) := by
    have h := hx2
    exact_mod_cast h
  have ha1 : 1 ≤ a' := by omega
  have hA1 : (1 : ℝ) ≤ (a' : ℝ) := by exact_mod_cast ha1
  have hSQ : (20 : ℝ) ≤ (s : ℝ) * (q (n - 1) : ℝ) := by
    have h : (40 : ℤ) ≤ ((Knr q n s : ℕ) : ℤ) := by exact_mod_cast hK
    rw [hKcastZ] at h
    have h2 : (40 : ℝ) ≤ 2 * (s : ℝ) * (q (n - 1) : ℝ) - 1 := by exact_mod_cast h
    linarith
  -- key real bounds, with `Q := (q (n-1) : ℝ)`
  have keyA : (a' : ℝ) * (q (n - 1) : ℝ) ≤ (y : ℝ) - (x : ℝ) := by nlinarith [habR, hx2r, hQR]
  have keyB : (y : ℝ) - (x : ℝ) ≤ (2 * (s : ℝ) - (a' : ℝ)) * (q (n - 1) : ℝ) - 1 := by
    nlinarith [habR, hx1r, hQR]
  have hYx : ((y - x : ℤ) : ℝ) = (y : ℝ) - (x : ℝ) := by push_cast; ring
  have hXY : ((x + (Knr q n s : ℤ) - 1) - y : ℤ) = x + ((Knr q n s : ℕ) : ℤ) - 1 - y := by
    simp
  have h2r : (((x + (Knr q n s : ℤ) - 1) - y : ℤ) : ℝ)
      = (x : ℝ) + ((Knr q n s : ℕ) : ℝ) - 1 - (y : ℝ) := by
    have h := hXY; push_cast at h ⊢; linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- x ≤ y
    nlinarith [hx2r, hbR, hQR]
  · -- y ≤ x + K - 1
    have h1 : 1 ≤ (a' : ℝ) * (q (n - 1) : ℝ) := by nlinarith [hA1, hQ1]
    have h2 : (x : ℝ) + (2 * (s : ℝ) * (q (n - 1) : ℝ) - 1) - 1 ≥ (y : ℝ) := by
      nlinarith [hx1r, habR, hQR]
    have : (y : ℝ) ≤ (x : ℝ) + ((Knr q n s : ℕ) : ℝ) - 1 := by rw [hKR]; linarith
    exact_mod_cast this
  · -- K ≤ 40 (y - x)
    have h : ((Knr q n s : ℕ) : ℝ) ≤ 40 * ((y : ℝ) - (x : ℝ)) := by
      rw [hKR]; nlinarith [keyA, hA2R, hS1, hQ1, hSQ, hQR]
    have h2 : ((Knr q n s : ℤ) : ℝ) ≤ 40 * ((y - x : ℤ) : ℝ) := by
      rw [hYx]
      rw [show ((Knr q n s : ℤ) : ℝ) = ((Knr q n s : ℕ) : ℝ) by simp]
      exact h
    exact_mod_cast h2
  · -- K ≤ 40 ((x + K - 1) - y)
    have h : ((Knr q n s : ℕ) : ℝ) ≤ 40 * ((x : ℝ) + ((Knr q n s : ℕ) : ℝ) - 1 - (y : ℝ)) := by
      rw [hKR]; nlinarith [keyB, hA2R, hS1, hQ1, hSQ, hQR]
    have h2 : ((Knr q n s : ℤ) : ℝ)
        ≤ 40 * (((x + (Knr q n s : ℤ) - 1) - y : ℤ) : ℝ) := by
      rw [h2r]
      rw [show ((Knr q n s : ℤ) : ℝ) = ((Knr q n s : ℕ) : ℝ) by simp]
      exact h
    exact_mod_cast h2
  · -- K/4 - 1 ≤ y - x
    rw [hYx, hKR]
    nlinarith [keyA, hA2R, hQR]
  · -- K/4 - 1 ≤ (x + K - 1) - y
    rw [h2r, hKR]
    nlinarith [keyB, hA2R, hQR]

end

end Work.TMC16Core.Assembly

namespace Work.TMC16Core.Assembly

open Work.TMC16Core
open Work.TMC16Core.Core

noncomputable section

/-- The linear decay bookkeeping of the non-resonant case: if the two endpoint distances
`d₁, d₂` of `y` in an interval of length `K` satisfy `d₁ + d₂ = K - 1` and
`dᵢ ≥ K/4 - 1`, and the `A`-exponent deficit `εA`, the uniformity rate `ε₁` and the decay
rate `L₁` satisfy `εA + (3/4) ε₁ + L₁/4 ≤ L/4`, then the Cramer exponents decay at rate
`L₁`. -/
theorem nr1_decay {L εA ε₁ L₁ K d₁ d₂ : ℝ}
    (hL : 0 < L) (hε₁ : 0 < ε₁) (hL₁ : 0 ≤ L₁) (hL1le : L₁ ≤ L)
    (hLεA : εA ≤ L)
    (hεAub : εA + (3 / 4) * ε₁ + L₁ / 4 ≤ L / 4)
    (hK : 0 ≤ K) (hd1 : 0 ≤ d₁) (hd2 : 0 ≤ d₂) (hsum : d₁ + d₂ = K - 1)
    (hlo : K / 4 - 1 ≤ d₁) (hlo2 : K / 4 - 1 ≤ d₂) :
    (L + ε₁) * d₂ - (K + 1) * (L - εA) ≤ -L₁ * d₁ ∧
    (L + ε₁) * d₁ - (K + 1) * (L - εA) ≤ -L₁ * d₂ := by
  constructor <;> nlinarith [hεAub, hLεA, hsum, hlo, hlo2, hL, hε₁, hL₁, hL1le, hK, hd1, hd2]

/-- **The endgame of the non-resonant case `s ≥ 1`.**  An `A`-bound on `I₁`, `ε₁`-uniformity
on `I₁ ∪ I₂` (`|I₁ ∪ I₂| = K+1`) and the window geometry of `I₂` produce `IsRegularBig` for
the site `y` at rate `L₁`. -/
theorem nr_case1_endgame {α lam L εA ε₁ L₁ : ℝ} {E : ℂ} {θ : ℝ} {K : ℕ}
    {I₁ I₂ : Finset ℤ} {y : ℤ}
    (hlam : 0 < lam) (hLlog : L = Real.log lam)
    (hε₁ : 0 < ε₁) (hεA0 : 0 < εA) (hεAε₁ : ε₁ < εA) (hLεA : εA ≤ L)
    (hL : 0 < L) (hL₁ : 0 < L₁) (hL1le : L₁ ≤ L)
    (hεAub : εA + (3 / 4) * ε₁ + L₁ / 4 ≤ L / 4)
    (hK40 : 40 ≤ K)
    (hgap : 4 * ((K : ℝ) + 1) * Real.exp (L - εA)
      < Real.exp ((K : ℝ) * (εA - ε₁)))
    (hcard : (I₁ ∪ I₂).card = K + 1)
    (huni : Work.TMC16Core.Uniform ε₁
      (fun j : {j : ℤ // j ∈ I₁ ∪ I₂} =>
        θ + (((j : ℤ) : ℝ) + (((K : ℝ) - 1) / 2)) * α))
    (hA : ∀ x ∈ I₁, ‖Work.TMC16Core.pd α lam (θ + (x : ℝ) * α) E (K + 1)‖ ≤
      Real.exp (((K : ℝ) + 1) * (L - εA)))
    (hgeo : ∀ x ∈ I₂,
      x ≤ y ∧ y ≤ x + (K : ℤ) - 1 ∧
      (K : ℤ) ≤ 40 * (y - x) ∧ (K : ℤ) ≤ 40 * ((x + (K : ℤ) - 1) - y) ∧
      ((K : ℝ) / 4 - 1) ≤ ((y - x : ℤ) : ℝ) ∧
      ((K : ℝ) / 4 - 1) ≤ (((x + (K : ℤ) - 1) - y : ℤ) : ℝ))
    (hbd : ∀ n : ℕ, K / 40 ≤ n → n ≤ K → ∀ ζ : ℝ,
      ‖Work.TMC16Core.pd α lam ζ E (n + 1)‖ ≤ Real.exp ((n : ℝ) * (L + ε₁))) :
    Work.TMC16Core.IsRegularBig α lam θ E L₁ (K : ℝ) y := by
  have hK1 : 1 ≤ K := by omega
  have hKpos : (0 : ℝ) < (K : ℝ) := by exact_mod_cast (by omega : 0 < K)
  -- A site of `I₂` whose continuant strictly exceeds `e^{(K+1)(L-εA)}`.
  have hthr : ((K : ℝ)) * ((((K : ℝ) + 1) * (L - εA)) / (K : ℝ))
      ≤ (((K : ℝ)) + 1) * (L - εA) := by
    rw [mul_div_cancel₀ _ (ne_of_gt hKpos)]
  obtain ⟨x₁, hx₁I₂, hbig⟩ :=
    Work.TMC16Core.NrFinal.site_step_gen_c_lt (α := α) (lam := lam) (L := L) (εA := εA)
      (ε₁ := ε₁) (c := (((K : ℝ) + 1) * (L - εA)) / (K : ℝ)) (E := E) (θ := θ)
      (K := K) (I₁ := I₁) (I₂ := I₂)
      hlam hLlog hε₁ hεAε₁ hεA0 hgap hthr hcard huni hA
  have hlarge : Real.exp (((K : ℝ) + 1) * (L - εA))
      < ‖Work.TMC16Core.pd α lam (θ + (x₁ : ℝ) * α) E (K + 1)‖ := by
    have hcK : ((((K : ℝ) + 1) * (L - εA)) / (K : ℝ)) * (K : ℝ)
        = ((K : ℝ) + 1) * (L - εA) := by
      rw [div_mul_cancel₀ _ (ne_of_gt hKpos)]
    rwa [hcK] at hbig
  -- Geometry and the decay bookkeeping.
  obtain ⟨h1, h2, hd1, hd2, hlo1, hlo2⟩ := hgeo x₁ hx₁I₂
  have hd1' : ((K : ℤ) : ℝ) ≤ 40 * (((y - x₁ : ℤ)) : ℝ) := by exact_mod_cast hd1
  have hd2' : ((K : ℤ) : ℝ) ≤ 40 * ((((x₁ + (K : ℤ) - 1) - y : ℤ)) : ℝ) := by
    exact_mod_cast hd2
  have hsum : ((y - x₁ : ℤ) : ℝ) + (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) = (K : ℝ) - 1 := by
    push_cast; ring
  have hnn1 : (0 : ℝ) ≤ ((y - x₁ : ℤ) : ℝ) := by
    exact_mod_cast (by omega : (0 : ℤ) ≤ y - x₁)
  have hnn2 : (0 : ℝ) ≤ (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ) := by
    exact_mod_cast (by omega : (0 : ℤ) ≤ (x₁ + (K : ℤ) - 1) - y)
  have hlo1' : (K : ℝ) / 4 - 1 ≤ ((y - x₁ : ℤ) : ℝ) := by
    have : ((K : ℤ) : ℝ) = (K : ℝ) := by push_cast; ring
    linarith [hlo1]
  obtain ⟨hdec1, hdec2⟩ :=
    nr1_decay (L := L) (εA := εA) (ε₁ := ε₁) (L₁ := L₁) (K := (K : ℝ))
      (d₁ := ((y - x₁ : ℤ) : ℝ)) (d₂ := (((x₁ + (K : ℤ) - 1) - y : ℤ) : ℝ))
      hL hε₁ (le_of_lt hL₁) hL1le hLεA hεAub (by positivity) hnn1 hnn2 hsum hlo1' hlo2
  have hn₀ : K / 40 ≤ (y - x₁).toNat := by omega
  have hn₁ : K / 40 ≤ (x₁ + (K : ℤ) - 1 - y).toNat := by omega
  exact Work.TMC16Core.Core.nr_endgame (α := α) (lam := lam) (E := E) (θ := θ) (L := L)
    (ε := εA) (ε₁ := ε₁) (m := L₁) (K := K) (y := y) (j₀ := x₁)
    hL hεAε₁ hL₁ hK1 h1 h2 hd1 hd2 hn₀ hn₁ hlarge hbd hdec1 hdec2

end

end Work.TMC16Core.Assembly

namespace Work.TMC16Core.Assembly

open Work.TMC16Core
open Work.TMC16Core.Core

noncomputable section

/-- `Knr` as a real number. -/
theorem knr_castR {q : ℕ → ℕ} {n s : ℕ} (hs : 1 ≤ s) (hq : 1 ≤ q (n - 1)) :
    ((Knr q n s : ℕ) : ℝ) = 2 * (s : ℝ) * (q (n - 1) : ℝ) - 1 := by
  have h : ((Knr q n s : ℕ) : ℤ) = 2 * (s : ℤ) * (q (n - 1) : ℤ) - 1 := by
    rw [Knr_cast q hs hq]; simp only [Tnr]; ring
  have h2 : (((Knr q n s : ℕ) : ℤ) : ℝ) = ((2 * (s : ℤ) * (q (n - 1) : ℤ) - 1 : ℤ) : ℝ) :=
    by rw [h]
  push_cast at h2
  exact h2

end

end Work.TMC16Core.Assembly
