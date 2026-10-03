/-
# `BtwistSet_eq_fiberSum`: the twisted bilinear multiplier as an average of fibre products,
# for an arbitrary pair of arithmetic frequency sets

This is the `Set`-analogue of `Work.KMTAreas.A7.Btwist_eq_fiberSum`: the paper's `form-1`
factorisation of the twisted bilinear multiplier of Krause--Mirek--Tao, *Pointwise ergodic
theorems for non-conventional bilinear polynomial averages*, Annals 195 (2022), §8, for an
**arbitrary** pair `(A₁,A₂)` of finite sets of circle frequencies (the instances
`Aᵢ = iwArithFreqs ρ lᵢ` and `Aᵢ = iwArithFreqsNew ρ lᵢ` are the height-`≤ l` and exact-height
readings of `FiberGeneral.lean`):

  `BtwistSet ρ P l₁ l₂ A₁ A₂ m₁ m₂ h k x
     = q⁻¹ ∑_{n₀ < q} (fiberOpSet A₁ m₁ n₀ h x) · (fiberOpPSet P A₂ m₂ n₀ k x)`,

with `q = arithQ ρ (max l₁ l₂)`.

## Structure of the proof

Exactly as in the non-`Set` version, and with no periodicity input at all: the whole arithmetic
content is the purely algebraic identity

  `arithKernelSet P q A₁ A₂ j₁ j₂ = q⁻¹ ∑_{n<q} (∑_{α₁∈A₁} e(α₁(n-j₁))) (∑_{α₂∈A₂} e(α₂(P(n)-j₂)))`

(i.e. `arithKernelSet_eq_arithCharSet` below: `mZ` is unfolded, the characters are combined with
`fourier_add`, and the two finite frequency sums are interchanged with the residue sum; the
finiteness of the sums makes all interchanges unconditional), after which the two `tsum`s are
interchanged with the finite residue sum by `tsum_tsum_finset_factor`.

The hypotheses `h₁`, `h₂` of the statement are exactly the summability of the two fibre families
at each residue, which is precisely what the second step needs.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.Btwist_eq_fiberSum

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset
open scoped ENNReal NNReal BigOperators
open Work.Analysis.IonescuWainger

/-- **Factorisation of the arithmetic kernel at an arbitrary pair of frequency sets.**  For any
modulus `q` and any finite sets `A₁, A₂` of circle frequencies,

  `arithKernelSet P q A₁ A₂ j₁ j₂
     = q⁻¹ ∑_{n<q} (∑_{α₁∈A₁} e(α₁(n-j₁))) · (∑_{α₂∈A₂} e(α₂(P(n)-j₂)))`.

The proof is the distribution of the finite sums defining `mZ` and the multiplicativity of the
additive characters `fourier`; no hypothesis on `A₁`, `A₂`, `q` or `P` is used. -/
theorem arithKernelSet_eq_arithCharSet (P : ℤ[X]) (q : ℕ)
    (A₁ A₂ : Finset Work.Analysis.IonescuWainger.Circle) (j₁ j₂ : ℤ) :
    arithKernelSet P q A₁ A₂ j₁ j₂
      = (q : ℂ)⁻¹ * ∑ n ∈ Finset.range q,
          arithCharSet A₁ ((n : ℤ) - j₁) * arithCharSet A₂ (P.eval (n : ℤ) - j₂) := by
  classical
  unfold arithKernelSet mZ arithCharSet
  have hpt : ∀ (α₁ α₂ : Work.Analysis.IonescuWainger.Circle),
      ((↑q)⁻¹ * ∑ n ∈ Finset.range q,
          (fourier (T:=1) (↑n)) α₁ * (fourier (T:=1) (eval (↑n) P)) α₂)
          * (fourier (T:=1) (-j₁)) α₁ * (fourier (T:=1) (-j₂)) α₂
        = (↑q)⁻¹ * ∑ n ∈ Finset.range q,
            (fourier (T:=1) ((↑n) - j₁)) α₁ * (fourier (T:=1) (eval (↑n) P - j₂)) α₂ := by
    intro α₁ α₂
    have hf1 : ∀ n : ℕ, (fourier (T:=1) (↑n : ℤ)) α₁ * (fourier (T:=1) (-j₁)) α₁
        = (fourier (T:=1) ((↑n : ℤ) - j₁)) α₁ := by
      intro n
      rw [show ((n:ℤ) - j₁) = (n:ℤ) + (-j₁) by ring, fourier_add]
    have hf2 : ∀ n : ℕ, (fourier (T:=1) (eval (↑n) P)) α₂ * (fourier (T:=1) (-j₂)) α₂
        = (fourier (T:=1) (eval (↑n) P - j₂)) α₂ := by
      intro n
      rw [show (eval (↑n) P - j₂) = (eval (↑n) P) + (-j₂) by ring, fourier_add]
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [← hf1 n, ← hf2 n]
    ring
  rw [Finset.sum_congr rfl (fun α₁ _ => Finset.sum_congr rfl (fun α₂ _ => hpt α₁ α₂))]
  rw [const_sum_three A₁ A₂ (Finset.range q) ((↑q)⁻¹)
      (fun α₁ α₂ n =>
        (fourier (T:=1) ((↑n:ℤ) - j₁)) α₁ * (fourier (T:=1) (eval (↑n) P - j₂)) α₂)]
  rw [Finset.mul_sum (Finset.range q) (fun n =>
      (∑ α₁ ∈ A₁, (fourier (T:=1) ((↑n:ℤ) - j₁)) α₁)
        * (∑ α₂ ∈ A₂, (fourier (T:=1) (eval (↑n) P - j₂)) α₂)) ((↑q)⁻¹)]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [Finset.sum_mul_sum A₁ A₂
      (fun α₁ => (fourier (T:=1) ((↑n:ℤ) - j₁)) α₁)
      (fun α₂ => (fourier (T:=1) (eval (↑n) P - j₂)) α₂)]
  rw [Finset.mul_sum A₁ (fun α₁ => ∑ α₂ ∈ A₂,
        (fourier (T:=1) ((↑n:ℤ) - j₁)) α₁ * (fourier (T:=1) (eval (↑n) P - j₂)) α₂) ((↑q)⁻¹)]
  rw [Finset.sum_congr rfl (fun α₁ _ => Finset.mul_sum A₂
      (fun α₂ => (fourier (T:=1) ((↑n:ℤ) - j₁)) α₁
        * (fourier (T:=1) (eval (↑n) P - j₂)) α₂) ((↑q)⁻¹))]

/-- **Fibre form of the kernel of `BtwistSet`.**  With `q = arithQ ρ (max l₁ l₂)` the kernel of the
twisted bilinear multiplier, together with its weights `cw mᵢ jᵢ` and the two test sequences, is the
average over the fibres `n ∈ ℤ/qℤ` of the products of the two one-variable arithmetic factors. -/
theorem arithKernelSet_fiberTerm (P : ℤ[X]) (q : ℕ)
    (A₁ A₂ : Finset Work.Analysis.IonescuWainger.Circle) (m₁ m₂ : ℝ → ℂ)
    (h k : ℤ → ℂ) (x j₁ j₂ : ℤ) :
    arithKernelSet P q A₁ A₂ j₁ j₂ * cw m₁ j₁ * cw m₂ j₂ * h (x - j₁) * k (x - j₂)
      = (q : ℂ)⁻¹ *
          ∑ n ∈ Finset.range q,
            (arithCharSet A₁ ((n : ℤ) - j₁) * cw m₁ j₁ * h (x - j₁))
              * (arithCharSet A₂ (P.eval (n : ℤ) - j₂) * cw m₂ j₂ * k (x - j₂)) := by
  rw [arithKernelSet_eq_arithCharSet]
  rw [show (∑ n ∈ Finset.range q,
            (arithCharSet A₁ ((n : ℤ) - j₁) * cw m₁ j₁ * h (x - j₁))
              * (arithCharSet A₂ (P.eval (n : ℤ) - j₂) * cw m₂ j₂ * k (x - j₂)))
        = (∑ n ∈ Finset.range q,
            (arithCharSet A₁ ((n : ℤ) - j₁) * arithCharSet A₂ (P.eval (n : ℤ) - j₂)))
            * (cw m₁ j₁ * cw m₂ j₂ * h (x - j₁) * k (x - j₂)) from by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring]
  ring

theorem BtwistSet_eq_fiberSum (ρ : ℝ) (P : Polynomial ℤ) (l₁ l₂ : ℕ)
    (A₁ A₂ : Finset Work.Analysis.IonescuWainger.Circle) (m₁ m₂ : ℝ → ℂ) (h k : ℤ → ℂ) (x : ℤ)
    (h₁ : ∀ n₀ : ℤ, Summable (fun j : ℤ =>
      Work.KMTAreas.A7.arithCharSet A₁ (n₀ - j) * Work.KMTAreas.A7.cw m₁ j * h (x - j)))
    (h₂ : ∀ n₀ : ℤ, Summable (fun j : ℤ =>
      Work.KMTAreas.A7.arithCharSet A₂ (Polynomial.eval n₀ P - j) * Work.KMTAreas.A7.cw m₂ j * k (x - j))) :
    Work.KMTAreas.A7.BtwistSet ρ P l₁ l₂ A₁ A₂ m₁ m₂ h k x
      = (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂) : ℂ)⁻¹ *
          ∑ n₀ ∈ Finset.range (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)),
            Work.KMTAreas.A7.fiberOpSet A₁ m₁ (n₀ : ℤ) h x
              * Work.KMTAreas.A7.fiberOpPSet P A₂ m₂ (n₀ : ℤ) k x := by
  classical
  have hfin : (∑' j₁ : ℤ, ∑' j₂ : ℤ, ∑ n ∈ Finset.range (arithQ ρ (max l₁ l₂)),
        (arithCharSet A₁ ((n : ℤ) - j₁) * cw m₁ j₁ * h (x - j₁))
          * (arithCharSet A₂ (P.eval (n : ℤ) - j₂) * cw m₂ j₂ * k (x - j₂)))
      = ∑ n₀ ∈ Finset.range (arithQ ρ (max l₁ l₂)),
          fiberOpSet A₁ m₁ (n₀ : ℤ) h x * fiberOpPSet P A₂ m₂ (n₀ : ℤ) k x := by
    rw [tsum_tsum_finset_factor (Finset.range (arithQ ρ (max l₁ l₂)))
        (fun n j => arithCharSet A₁ ((n : ℤ) - j) * cw m₁ j * h (x - j))
        (fun n j => arithCharSet A₂ (P.eval (n : ℤ) - j) * cw m₂ j * k (x - j))
        (fun n _ => h₁ (n : ℤ)) (fun n _ => h₂ (n : ℤ))]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    simp only [fiberOpSet, fiberOpPSet]
  simp only [BtwistSet]
  rw [tsum_congr (fun j₁ => tsum_congr (fun j₂ =>
    arithKernelSet_fiberTerm P (arithQ ρ (max l₁ l₂)) A₁ A₂ m₁ m₂ h k x j₁ j₂))]
  simp only [tsum_mul_left]
  rw [hfin]

end

end Work.KMTAreas.A7
