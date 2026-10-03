/-
Copyright (c) 2026 The AnnalsChallenge team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The AnnalsChallenge team
-/
import Submission.Work.Analysis.InverseTheory.MajorArcs

/-!
# The dual functions of the halved average, and the transposition identity `(transpose)`

Krause–Mirek–Tao, §6, work with trilinear forms `⟨Ã_N(f,g), h⟩` and with the two *dual functions*
obtained by transposing the averaging operation.  With the paper's averaging convention
`Ã_N^{P₁,P₂}(f,g)(x) = E_{n∈[N]} f(x+P₁(n)) g(x+P₂(n)) 1_{n>N/2}` the transposes are

`Ã_N^*(h,g)   = Ã_N^{-n, P(n)-n}(h,g)`,  `Ã_N^{**}(f,h) = Ã_N^{n-P(n), -P(n)}(f,h)`,

so that `⟨Ã_N(f,g), h⟩ = ⟨Ã_N^*(h,g), f⟩ = ⟨Ã_N^{**}(f,h), g⟩` — equation `(transpose)` of §6.
(Note that the two displayed formulas `h(x+n)g(x+n-P(n))` and `f(x+P(n)-n)h(x+P(n))` in the
paper have their signs inverted relative to its own convention; the definitions below are the
ones for which the transposition identities hold, and they are the ones used in the proofs.)

The main results of this module are

* `bilinPair_AhalfZ_expand` — the trilinear form as an explicit double sum;
* `bilinPair_AhalfZ_eq_transpose`, `bilinPair_AhalfZ_eq_transpose₂` — equation `(transpose)`;
* the auxiliary `tsum_finset_sum_of_support`, which interchanges a finite sum with a `tsum` when
  the summands vanish off a common finite set.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
open Polynomial

namespace Work.Analysis.InverseTheory

/-! ## Interchanging a finite sum with a `tsum` -/

/-- Interchange of a finite sum with a `tsum`: if `φ n ·` vanishes off the finite set `t` for every
`n ∈ s`, then `∑'_x ∑_{n∈s} φ n x = ∑_{n∈s} ∑'_x φ n x`. -/
theorem tsum_finset_sum_of_support {ι : Type*} {s : Finset ι} {t : Finset ℤ}
    {φ : ι → ℤ → ℂ} (hφ : ∀ n ∈ s, ∀ x ∉ t, φ n x = 0) :
    ∑' x : ℤ, ∑ n ∈ s, φ n x = ∑ n ∈ s, ∑' x : ℤ, φ n x := by
  have h1 : ∀ x : ℤ, x ∉ t → ∑ n ∈ s, φ n x = 0 :=
    fun x hx => Finset.sum_eq_zero fun n hn => hφ n hn x hx
  rw [tsum_eq_sum h1]
  rw [Finset.sum_congr rfl fun n hn => tsum_eq_sum (hφ n hn)]
  exact Finset.sum_comm

/-! ## The dual functions -/

/-- The first dual function (paper §6, equation `(bkhg)`):
`Ã_N^*(h,g)(x) = (1/N) ∑_{N/2 < n ≤ N} h(x - n) g(x + P(n) - n)`. -/
noncomputable def AhalfTranspose (N : ℕ) (P : Polynomial ℤ) (h g : ℤ → ℂ) (x : ℤ) : ℂ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
    h (x - (n : ℤ)) * g (x + P.eval (n : ℤ) - (n : ℤ))

/-- The second dual function (paper §6, equation `(eq:bkhf)`):
`Ã_N^{**}(f,h)(x) = (1/N) ∑_{N/2 < n ≤ N} f(x + n - P(n)) h(x - P(n))`. -/
noncomputable def AhalfTranspose₂ (N : ℕ) (P : Polynomial ℤ) (f h : ℤ → ℂ) (x : ℤ) : ℂ :=
  (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
    f (x + (n : ℤ) - P.eval (n : ℤ)) * h (x - P.eval (n : ℤ))

/-! ## The trilinear form as an explicit double sum -/

/-- `⟨Ã_N(f,g), h⟩` as an explicit double sum over `N/2 < n ≤ N` and `x ∈ ℤ`. -/
theorem bilinPair_AhalfZ_expand {f g h : ℤ → ℂ} (hh : FinSupp h) (N : ℕ) (P : Polynomial ℤ) :
    bilinPair (AhalfZ N P f g) h
      = (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          ∑' x : ℤ, f (x + (n : ℤ)) * g (x + P.eval (n : ℤ)) * h x := by
  obtain ⟨t, ht⟩ := hh
  have hpt : ∀ x : ℤ, AhalfZ N P f g x * h x
      = (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          f (x + (n : ℤ)) * g (x + P.eval (n : ℤ)) * h x := by
    intro x
    rw [AhalfZ, mul_assoc, Finset.sum_mul]
  rw [bilinPair]
  simp only [hpt]
  rw [tsum_mul_left]
  congr 1
  exact tsum_finset_sum_of_support (s := Finset.Ioc (N / 2) N) (t := t)
    (φ := fun n x => f (x + (n : ℤ)) * g (x + P.eval (n : ℤ)) * h x)
    (fun n _ x hx => by simp [ht x hx])

/-- `⟨Ã_N^*(h,g), f⟩` as an explicit double sum. -/
theorem bilinPair_AhalfTranspose_expand {h g f : ℤ → ℂ} (hh : FinSupp h) (N : ℕ)
    (P : Polynomial ℤ) :
    bilinPair (AhalfTranspose N P h g) f
      = (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          ∑' x : ℤ, h (x - (n : ℤ)) * g (x + P.eval (n : ℤ) - (n : ℤ)) * f x := by
  obtain ⟨t, ht⟩ := hh
  set T : Finset ℤ := (Finset.Ioc (N / 2) N).biUnion (fun n => t.image (fun z => z + (n : ℤ)))
  have hpt : ∀ x : ℤ, AhalfTranspose N P h g x * f x
      = (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          h (x - (n : ℤ)) * g (x + P.eval (n : ℤ) - (n : ℤ)) * f x := by
    intro x
    rw [AhalfTranspose, mul_assoc, Finset.sum_mul]
  rw [bilinPair]
  simp only [hpt]
  rw [tsum_mul_left]
  congr 1
  exact tsum_finset_sum_of_support (s := Finset.Ioc (N / 2) N) (t := T)
    (φ := fun n x => h (x - (n : ℤ)) * g (x + P.eval (n : ℤ) - (n : ℤ)) * f x)
    (fun n hn x hx => by
      have hxn : x - (n : ℤ) ∉ t := fun hmem =>
        hx (Finset.mem_biUnion.mpr ⟨n, hn, Finset.mem_image.mpr ⟨x - (n : ℤ), hmem, by ring⟩⟩)
      simp [ht _ hxn])

/-- `⟨Ã_N^{**}(f,h), g⟩` as an explicit double sum. -/
theorem bilinPair_AhalfTranspose₂_expand {f h g : ℤ → ℂ} (hg : FinSupp g) (N : ℕ)
    (P : Polynomial ℤ) :
    bilinPair (AhalfTranspose₂ N P f h) g
      = (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          ∑' x : ℤ, f (x + (n : ℤ) - P.eval (n : ℤ)) * h (x - P.eval (n : ℤ)) * g x := by
  obtain ⟨t, ht⟩ := hg
  have hpt : ∀ x : ℤ, AhalfTranspose₂ N P f h x * g x
      = (N : ℝ)⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          f (x + (n : ℤ) - P.eval (n : ℤ)) * h (x - P.eval (n : ℤ)) * g x := by
    intro x
    rw [AhalfTranspose₂, mul_assoc, Finset.sum_mul]
  rw [bilinPair]
  simp only [hpt]
  rw [tsum_mul_left]
  congr 1
  exact tsum_finset_sum_of_support (s := Finset.Ioc (N / 2) N) (t := t)
    (φ := fun n x => f (x + (n : ℤ) - P.eval (n : ℤ)) * h (x - P.eval (n : ℤ)) * g x)
    (fun n _ x hx => by simp [ht x hx])

/-! ## Change of variables in the inner sum -/

/-- Change of variables `x ↦ x - n` in the inner sum: it turns the summand of `⟨Ã_N(f,g),h⟩` into
the summand of `⟨Ã_N^*(h,g),f⟩`. -/
theorem tsum_reindex_transpose {f g h : ℤ → ℂ} (n : ℤ) (P : Polynomial ℤ) :
    (∑' x : ℤ, f (x + n) * g (x + P.eval n) * h x)
      = ∑' x : ℤ, h (x - n) * g (x + P.eval n - n) * f x := by
  rw [← (Equiv.subRight n).tsum_eq (fun x : ℤ => f (x + n) * g (x + P.eval n) * h x)]
  refine tsum_congr fun y => ?_
  rw [Equiv.subRight_apply, show y - n + n = y by ring,
    show y - n + P.eval n = y + P.eval n - n by ring]
  ring

/-- Change of variables `x ↦ x - P(n)` in the inner sum: it turns the summand of
`⟨Ã_N(f,g),h⟩` into the summand of `⟨Ã_N^{**}(f,h),g⟩`. -/
theorem tsum_reindex_transpose₂ {f g h : ℤ → ℂ} (n : ℤ) (P : Polynomial ℤ) :
    (∑' x : ℤ, f (x + n) * g (x + P.eval n) * h x)
      = ∑' x : ℤ, f (x + n - P.eval n) * h (x - P.eval n) * g x := by
  rw [← (Equiv.subRight (P.eval n)).tsum_eq
    (fun u : ℤ => f (u + n) * g (u + P.eval n) * h u)]
  refine tsum_congr fun y => ?_
  rw [Equiv.subRight_apply,
    show y - P.eval n + n = y + n - P.eval n by ring,
    show y - P.eval n + P.eval n = y by ring]
  ring

/-! ## The transposition identity `(transpose)` -/

/-- **Equation `(transpose)` of §6**, first form:
`⟨Ã_N(f,g), h⟩ = ⟨Ã_N^*(h,g), f⟩`. -/
theorem bilinPair_AhalfZ_eq_transpose {f g h : ℤ → ℂ} (_hf : FinSupp f) (_hg : FinSupp g)
    (hh : FinSupp h) (N : ℕ) (P : Polynomial ℤ) :
    bilinPair (AhalfZ N P f g) h = bilinPair (AhalfTranspose N P h g) f := by
  rw [bilinPair_AhalfZ_expand hh N P, bilinPair_AhalfTranspose_expand hh N P]
  congr 1
  exact Finset.sum_congr rfl fun n _ => tsum_reindex_transpose n P

/-- **Equation `(transpose)` of §6**, second form:
`⟨Ã_N(f,g), h⟩ = ⟨Ã_N^{**}(f,h), g⟩`. -/
theorem bilinPair_AhalfZ_eq_transpose₂ {f g h : ℤ → ℂ} (_hf : FinSupp f) (hg : FinSupp g)
    (hh : FinSupp h) (N : ℕ) (P : Polynomial ℤ) :
    bilinPair (AhalfZ N P f g) h = bilinPair (AhalfTranspose₂ N P f h) g := by
  rw [bilinPair_AhalfZ_expand hh N P, bilinPair_AhalfTranspose₂_expand hg N P]
  congr 1
  exact Finset.sum_congr rfl fun n _ => tsum_reindex_transpose₂ n P

end Work.Analysis.InverseTheory
