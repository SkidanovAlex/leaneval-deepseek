import Mathlib
import Submission.Work.HP.Defs

/-!
# `2 d + 1 ≤ N_{d,n}` for `2 ≤ n`

`NN d n` is the number of degree-`d` monomials in `n + 1` variables, i.e. the cardinality of
the subtype `Mon d n` of degree-`d` exponent vectors.  We show that for `2 ≤ n` there are at
least `2 d + 1` such monomials, by exhibiting an injection

`Fin (d+1) ⊕ Fin d → Mon d n`

namely `b ↦ x_0^{d-b} x_1^b` (for `b : Fin (d+1)`) and `c ↦ x_0^{d-1-c} x_1^c x_2`
(for `c : Fin d`).  These `(d+1) + d = 2 d + 1` monomials are pairwise distinct because their
`(x_1, x_2)`-exponents `(b, 0)` and `(c, 1)` determine the index.

This is the crude lower bound on `N_{d,n}` needed whenever a lemma wants a few more
monomials than the `6` of `six_le_NN` (which requires `2 ≤ d ≤ n`); here only `2 ≤ n` is
needed.
-/

set_option autoImplicit false

noncomputable section

open MvPolynomial Finset

namespace Work.HP.MM2

open Finsupp

/-- The element of `Mon d n` which puts the exponent `a` at position `i0`, `b` at `i1`,
`c` at `i2`, and `0` elsewhere.  The hypothesis `hs` records that the total degree is `d`. -/
private def mkMon (d n : ℕ) (i0 i1 i2 : Fin (n + 1)) (a b c : ℕ) (hs : a + b + c = d) :
    Mon d n :=
  ⟨fun i => ⟨(Finsupp.single i0 a + Finsupp.single i1 b + Finsupp.single i2 c) i, by
      have h1 : (Finsupp.single i0 a) i ≤ a := by rw [Finsupp.single_apply]; split <;> omega
      have h2 : (Finsupp.single i1 b) i ≤ b := by rw [Finsupp.single_apply]; split <;> omega
      have h3 : (Finsupp.single i2 c) i ≤ c := by rw [Finsupp.single_apply]; split <;> omega
      rw [Finsupp.add_apply, Finsupp.add_apply]
      omega⟩,
    by
      have hE : (∑ i : Fin (n + 1),
          (Finsupp.single i0 a + Finsupp.single i1 b + Finsupp.single i2 c) i) = a + b + c := by
        rw [← Finsupp.sum_fintype (Finsupp.single i0 a + Finsupp.single i1 b + Finsupp.single i2 c)
          (fun _ x => x) (by intro i; rfl)]
        rw [Finsupp.sum_add_index (by intro x hx; rfl) (by intro x hx b1 b2; rfl)]
        rw [Finsupp.sum_add_index (by intro x hx; rfl) (by intro x hx b1 b2; rfl)]
        rw [Finsupp.sum_single_index (by rfl), Finsupp.sum_single_index (by rfl),
          Finsupp.sum_single_index (by rfl)]
      rw [hE, hs]⟩

/-- The exponent of `mkMon d n i0 i1 i2 a b c hs` at `i1` is `b`. -/
private lemma mkMon_apply_i1 {d n : ℕ} {i0 i1 i2 : Fin (n + 1)} {a b c : ℕ}
    {hs : a + b + c = d} (h10 : i1 ≠ i0) (h12 : i1 ≠ i2) :
    ((mkMon d n i0 i1 i2 a b c hs).1 i1 : ℕ) = b := by
  show (Finsupp.single i0 a + Finsupp.single i1 b + Finsupp.single i2 c) i1 = b
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_of_ne h10, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne h12]
  omega

/-- The exponent of `mkMon d n i0 i1 i2 a b c hs` at `i2` is `c`. -/
private lemma mkMon_apply_i2 {d n : ℕ} {i0 i1 i2 : Fin (n + 1)} {a b c : ℕ}
    {hs : a + b + c = d} (h20 : i2 ≠ i0) (h21 : i2 ≠ i1) :
    ((mkMon d n i0 i1 i2 a b c hs).1 i2 : ℕ) = c := by
  show (Finsupp.single i0 a + Finsupp.single i1 b + Finsupp.single i2 c) i2 = c
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_of_ne h20, Finsupp.single_eq_of_ne h21,
    Finsupp.single_eq_same]
  omega

/-- For `2 ≤ n` there are at least `2 d + 1` monomials of degree `d` in `n + 1` variables,
i.e. `N_{d,n} = NN d n ≥ 2 d + 1`.  The witnesses are `x_0^{d-b} x_1^b` for `0 ≤ b ≤ d` and
`x_0^{d-1-c} x_1^c x_2` for `0 ≤ c < d`. -/
theorem NN_ge_two_mul_add_one (d n : ℕ) (hn : 2 ≤ n) : 2 * d + 1 ≤ Work.HP.NN d n := by
  let i0 : Fin (n + 1) := ⟨0, by omega⟩
  let i1 : Fin (n + 1) := ⟨1, by omega⟩
  let i2 : Fin (n + 1) := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  -- the injection: `b ↦ x_0^{d-b} x_1^b`, `c ↦ x_0^{d-1-c} x_1^c x_2`
  let g : (Fin (d + 1) ⊕ Fin d) → Mon d n := fun p =>
    match p with
    | Sum.inl b => mkMon d n i0 i1 i2 (d - b) b 0 (by have := b.2; omega)
    | Sum.inr b => mkMon d n i0 i1 i2 (d - 1 - b) b 1 (by have := b.2; omega)
  -- the tag `(x_1-exponent, x_2-exponent)` of each witness
  let tag : (Fin (d + 1) ⊕ Fin d) → ℕ × ℕ := fun p =>
    match p with
    | Sum.inl b => ((b : ℕ), 0)
    | Sum.inr b => ((b : ℕ), 1)
  have htag : ∀ p, tag p = (((g p).1 i1 : ℕ), ((g p).1 i2 : ℕ)) := by
    rintro (b | b) <;>
      simp only [tag, g, mkMon_apply_i1 (Ne.symm h01) h12,
        mkMon_apply_i2 (Ne.symm h02) (Ne.symm h12)]
  have htag_inj : Function.Injective tag := by
    rintro (b | b) (b' | b') h
    · simp only [tag, Prod.mk.injEq] at h
      exact congrArg Sum.inl (Fin.ext h.1)
    · simp only [tag, Prod.mk.injEq] at h
      omega
    · simp only [tag, Prod.mk.injEq] at h
      omega
    · simp only [tag, Prod.mk.injEq] at h
      exact congrArg Sum.inr (Fin.ext h.1)
  have hg_inj : Function.Injective g := by
    intro p q hpq
    apply htag_inj
    rw [htag p, htag q, hpq]
  have hcard : Fintype.card (Fin (d + 1) ⊕ Fin d) ≤ NN d n :=
    Fintype.card_le_of_injective g hg_inj
  have hcard' : d + 1 + d ≤ NN d n := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using hcard
  omega

end Work.HP.MM2
