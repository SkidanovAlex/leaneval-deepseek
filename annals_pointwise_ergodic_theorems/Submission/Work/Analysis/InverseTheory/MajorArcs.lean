/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Submission.Work.Analysis.InverseTheory.Basic
import Submission.Work.Analysis.IonescuWainger.Basic

/-!
# Major arcs on the frequency circle, and the `ℤ`-Fourier transform

Krause–Mirek–Tao, *Pointwise ergodic theorems for non-conventional bilinear polynomial averages*,
Annals 195 (2022), §5–§6.  This module contains the frequency-side vocabulary of the paper:

* `realFreqInterval k` — the continuous-frequency interval `ℝ_{≤k} = [-2^k, 2^k]`;
* `majorArc ρ l k` — the Ionescu–Wainger major arcs
  `𝓜_{≤l,≤k} = π(ℝ_{≤k} × (ℚ/ℤ)_{≤l})`, where `π(θ, α) = α + θ` and `(ℚ/ℤ)_{≤l}` is the
  colleague-owned Ionescu–Wainger arithmetic-frequency set
  `Work.Analysis.IonescuWainger.iwArithFreqs ρ l` of Ionescu–Wainger height at most `2^l`;
* `majorArcNaive l k` — the *naive* major arcs `𝓜_{≤l,≤k,naive}`, defined as in §5 of the paper
  with the naive height `Height_naive(a/q) = q` instead of the Ionescu–Wainger height.  This is a
  deliberate small duplication of `Work.Analysis.IonescuWainger.naiveHeight` (which gives the naive
  height as a *function* rather than as a set); the paper's Remark `height-naive` —
  `𝓜_{≤l,≤k,naive} ⊆ 𝓜_{≤l,≤k}` — is *not* proved here, it needs the arithmetic content of
  Appendix A;
* `ZFourier f ξ = ∑_x f x e(-xξ)` — the Fourier transform of a function on `ℤ` at the frequency
  `ξ ∈ ℝ/ℤ`.  It is a `tsum`, hence total: no measurability or summability side conditions are
  needed, and for finitely supported `f` it is a finite sum;
* `FourierVanishOn f S` — the paper's "`𝓕_ℤ f` vanishes on `S`", the hypothesis of Theorem
  `improv`;
* `FourierSupportIn f S` — the paper's "`𝓕_ℤ f` is supported in `S`", the conclusion of
  Proposition `lip`.

The two frequency sets attached to the height `l` and the scale `N` that occur in Theorem
`improv` are `majorArcUpperHalf ρ N l` (`𝓜_{≤l, ≤ -Log N + l}`, for the linear shifts `n`) and
`majorArcLowerHalf ρ N d l` (`𝓜_{≤l, ≤ -dLog N + dl}`, for the shifts `P(n)`, `deg P = d`).
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators

namespace Work.Analysis.InverseTheory

open Work.Analysis.IonescuWainger

/-- The frequency circle `ℝ/ℤ`.  This is definitionally the Ionescu–Wainger colleague's
`Work.Analysis.IonescuWainger.Circle = AddCircle 1`; the local name exists because the root
namespace of Mathlib has an unrelated `Circle` (the unit circle in `ℂ`). -/
abbrev FreqCircle : Type := AddCircle (1 : ℝ)

/-! ## The frequency sets -/

/-- The continuous-frequency interval `ℝ_{≤k} = [-2^k, 2^k]` (paper §5). -/
def realFreqInterval (k : ℤ) : Set ℝ := Set.Icc (-(2 : ℝ) ^ k) ((2 : ℝ) ^ k)

@[simp] theorem mem_realFreqInterval {k : ℤ} {θ : ℝ} :
    θ ∈ realFreqInterval k ↔ -(2 : ℝ) ^ k ≤ θ ∧ θ ≤ (2 : ℝ) ^ k := Iff.rfl

theorem neg_mem_realFreqInterval {k : ℤ} {θ : ℝ} (h : θ ∈ realFreqInterval k) :
    -θ ∈ realFreqInterval k := by
  rw [mem_realFreqInterval] at h ⊢
  constructor <;> linarith [h.1, h.2]

theorem realFreqInterval_mono {k k' : ℤ} (h : k ≤ k') : realFreqInterval k ⊆ realFreqInterval k' := by
  intro θ hθ
  rw [mem_realFreqInterval] at hθ ⊢
  have h2 : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ k' := zpow_le_zpow_right₀ (by norm_num) h
  constructor <;> linarith [hθ.1, hθ.2]

/-- The Ionescu–Wainger major arcs `𝓜_{≤l,≤k} = π(ℝ_{≤k} × (ℚ/ℤ)_{≤l})`, where `π(θ, α) = α + θ`
and `(ℚ/ℤ)_{≤l} = iwArithFreqs ρ l` is the set of arithmetic frequencies of Ionescu–Wainger
height at most `2^l`. -/
def majorArc (ρ : ℝ) (l : ℕ) (k : ℤ) : Set FreqCircle :=
  {γ | ∃ α ∈ iwArithFreqs ρ l, ∃ θ ∈ realFreqInterval k, γ = α + ((θ : ℝ) : FreqCircle)}

theorem mem_majorArc {ρ : ℝ} {l : ℕ} {k : ℤ} {γ : FreqCircle} :
    γ ∈ majorArc ρ l k ↔
      ∃ α ∈ iwArithFreqs ρ l, ∃ θ ∈ realFreqInterval k, γ = α + ((θ : ℝ) : FreqCircle) := Iff.rfl

/-- The *naive* major arcs `𝓜_{≤l,≤k,naive}`: `γ = a/q + θ mod 1` with `1 ≤ q ≤ 2^l` and
`θ ∈ ℝ_{≤k}` (paper §5). -/
def majorArcNaive (l : ℕ) (k : ℤ) : Set FreqCircle :=
  {γ | ∃ q : ℕ, 1 ≤ q ∧ q ≤ 2 ^ l ∧
        ∃ a : ℕ, ∃ θ ∈ realFreqInterval k, γ = ((a : ℝ) / (q : ℝ) : FreqCircle) + ((θ : ℝ) : FreqCircle)}

theorem mem_majorArcNaive {l : ℕ} {k : ℤ} {γ : FreqCircle} :
    γ ∈ majorArcNaive l k ↔
      ∃ q : ℕ, 1 ≤ q ∧ q ≤ 2 ^ l ∧
        ∃ a : ℕ, ∃ θ ∈ realFreqInterval k,
          γ = ((a : ℝ) / (q : ℝ) : FreqCircle) + ((θ : ℝ) : FreqCircle) :=
  Iff.rfl

/-- The major arcs of Theorem `improv` (i): `𝓜_{≤l, ≤ -Log N + l}`, the frequency set attached to
the *linear* shifts `n ∈ [N]`. -/
def majorArcUpperHalf (ρ : ℝ) (N : ℕ) (l : ℕ) : Set FreqCircle :=
  majorArc ρ l ((l : ℤ) - (LogScale N : ℤ))

/-- The major arcs of Theorem `improv` (ii): `𝓜_{≤l, ≤ -dLog N + dl}`, the frequency set attached
to the shifts `P(n)`, `deg P = d`. -/
def majorArcLowerHalf (ρ : ℝ) (N : ℕ) (d : ℕ) (l : ℕ) : Set FreqCircle :=
  majorArc ρ l ((d : ℤ) * ((l : ℤ) - (LogScale N : ℤ)))

theorem majorArcUpperHalf_def (ρ : ℝ) (N : ℕ) (l : ℕ) :
    majorArcUpperHalf ρ N l = majorArc ρ l ((l : ℤ) - (LogScale N : ℤ)) := rfl

theorem majorArcLowerHalf_def (ρ : ℝ) (N : ℕ) (d : ℕ) (l : ℕ) :
    majorArcLowerHalf ρ N d l = majorArc ρ l ((d : ℤ) * ((l : ℤ) - (LogScale N : ℤ))) := rfl

/-- Monotonicity of the IW major arcs in the continuous parameter `k`, given monotonicity of the
arithmetic-frequency sets (which is a theorem of the Ionescu–Wainger colleague's area). -/
theorem majorArc_mono_of_subset {ρ : ℝ} {l l' : ℕ} {k k' : ℤ}
    (hl : iwArithFreqs ρ l ⊆ iwArithFreqs ρ l') (hk : k ≤ k') :
    majorArc ρ l k ⊆ majorArc ρ l' k' := by
  intro γ hγ
  rw [mem_majorArc] at hγ ⊢
  obtain ⟨α, hα, θ, hθ, rfl⟩ := hγ
  exact ⟨α, hl hα, θ, realFreqInterval_mono hk hθ, rfl⟩

theorem majorArcNaive_mono {l l' : ℕ} {k k' : ℤ} (hl : l ≤ l') (hk : k ≤ k') :
    majorArcNaive l k ⊆ majorArcNaive l' k' := by
  intro γ hγ
  rw [mem_majorArcNaive] at hγ ⊢
  obtain ⟨q, hq1, hq2, a, θ, hθ, rfl⟩ := hγ
  exact ⟨q, hq1, hq2.trans (Nat.pow_le_pow_right (by norm_num) hl), a, θ,
    realFreqInterval_mono hk hθ, rfl⟩

/-! ## Finitely supported functions on `ℤ` -/

/-- `f : ℤ → ℂ` is finitely supported.  This is the class of functions for which every series in
this development is a finite sum; it holds in particular for every `f` with `SupportIn f M`. -/
def FinSupp (f : ℤ → ℂ) : Prop := ∃ s : Finset ℤ, ∀ x ∉ s, f x = 0

theorem FinSupp.summable {f : ℤ → ℂ} (hf : FinSupp f) : Summable f := by
  obtain ⟨s, hs⟩ := hf
  exact summable_of_ne_finset_zero hs

theorem FinSupp.summable_mul {f : ℤ → ℂ} (hf : FinSupp f) (e : ℤ → ℂ) :
    Summable fun x : ℤ => f x * e x := by
  obtain ⟨s, hs⟩ := hf
  exact summable_of_ne_finset_zero fun x hx => by rw [hs x hx, zero_mul]

theorem FinSupp.add {f g : ℤ → ℂ} (hf : FinSupp f) (hg : FinSupp g) : FinSupp (f + g) := by
  obtain ⟨s, hs⟩ := hf; obtain ⟨t, ht⟩ := hg
  refine ⟨s ∪ t, fun x hx => ?_⟩
  simp only [Finset.mem_union, not_or] at hx
  simp [hs x hx.1, ht x hx.2]

theorem FinSupp.neg {f : ℤ → ℂ} (hf : FinSupp f) : FinSupp (-f) := by
  obtain ⟨s, hs⟩ := hf
  exact ⟨s, fun x hx => by simp [hs x hx]⟩

theorem FinSupp.smul {f : ℤ → ℂ} (c : ℂ) (hf : FinSupp f) : FinSupp (c • f) := by
  obtain ⟨s, hs⟩ := hf
  exact ⟨s, fun x hx => by simp [hs x hx]⟩

theorem FinSupp.of_supportIn {f : ℤ → ℂ} {M : ℕ} (h : SupportIn f M) : FinSupp f := by
  refine ⟨Finset.Icc (-(M : ℤ)) (M : ℤ), fun x hx => ?_⟩
  by_contra hc
  exact hx (SupportIn.mem_Icc h hc)

/-! ## The Fourier transform on `ℤ` -/

/-- The Fourier transform of `f : ℤ → ℂ` at the frequency `ξ ∈ ℝ/ℤ`:
`𝓕_ℤ f(ξ) = ∑_x f(x) e(-x ξ)`, where `e(t) = e^{2πit}`.  The series is a `tsum`, hence total;
for finitely supported `f` it is a finite sum. -/
noncomputable def ZFourier (f : ℤ → ℂ) (ξ : FreqCircle) : ℂ :=
  ∑' x : ℤ, f x * (fourier (-x) ξ : ℂ)

/-- `𝓕_ℤ f` vanishes on the frequency set `S` (hypothesis of Theorem `improv`). -/
def FourierVanishOn (f : ℤ → ℂ) (S : Set FreqCircle) : Prop := ∀ ξ ∈ S, ZFourier f ξ = 0

/-- `𝓕_ℤ f` is supported in the frequency set `S` (conclusion of Proposition `lip`). -/
def FourierSupportIn (f : ℤ → ℂ) (S : Set FreqCircle) : Prop := ∀ ξ, ξ ∉ S → ZFourier f ξ = 0

theorem FourierVanishOn.mono {f : ℤ → ℂ} {S T : Set FreqCircle} (hST : S ⊆ T)
    (h : FourierVanishOn f T) : FourierVanishOn f S := fun ξ hξ => h ξ (hST hξ)

theorem FourierSupportIn.mono {f : ℤ → ℂ} {S T : Set FreqCircle} (hST : S ⊆ T)
    (h : FourierSupportIn f S) : FourierSupportIn f T :=
  fun ξ hξ => h ξ fun hξS => hξ (hST hξS)

theorem FourierVanishOn_empty (f : ℤ → ℂ) : FourierVanishOn f ∅ := by
  intro ξ hξ; exact absurd hξ (Set.notMem_empty ξ)

theorem fourierVanishOn_compl_iff {f : ℤ → ℂ} {S : Set FreqCircle} :
    FourierVanishOn f Sᶜ ↔ FourierSupportIn f S := Iff.rfl

theorem ZFourier_add {f g : ℤ → ℂ} (hf : FinSupp f) (hg : FinSupp g) (ξ : FreqCircle) :
    ZFourier (f + g) ξ = ZFourier f ξ + ZFourier g ξ := by
  have h1 : Summable fun x : ℤ => f x * (fourier (-x) ξ : ℂ) :=
    hf.summable_mul _
  have h2 : Summable fun x : ℤ => g x * (fourier (-x) ξ : ℂ) :=
    hg.summable_mul _
  have h3 : ZFourier (f + g) ξ
      = ∑' x : ℤ, (f x * (fourier (-x) ξ : ℂ) + g x * (fourier (-x) ξ : ℂ)) := by
    rw [ZFourier]
    exact tsum_congr fun x => by rw [Pi.add_apply, add_mul]
  rw [h3, h1.tsum_add h2, ZFourier, ZFourier]

theorem ZFourier_neg (f : ℤ → ℂ) (ξ : FreqCircle) :
    ZFourier (-f) ξ = -ZFourier f ξ := by
  have h3 : ZFourier (-f) ξ
      = ∑' x : ℤ, -(f x * (fourier (-x) ξ : ℂ)) := by
    rw [ZFourier]
    exact tsum_congr fun x => by rw [Pi.neg_apply, neg_mul]
  rw [h3, tsum_neg, ZFourier]

theorem ZFourier_smul (c : ℂ) (f : ℤ → ℂ) (ξ : FreqCircle) :
    ZFourier (c • f) ξ = c * ZFourier f ξ := by
  rw [ZFourier, ZFourier, ← tsum_mul_left]
  exact tsum_congr fun x => by simp [smul_eq_mul, mul_assoc]

end Work.Analysis.InverseTheory
