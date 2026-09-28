import Mathlib
import Submission.Work.HP.Defs

/-!
# `N_{d,n} ≥ 6` for `2 ≤ d ≤ n`

The number `NN d n` of degree-`d` monomials in `n+1` variables is the cardinality of the
subtype `Mon d n` of degree-`d` exponent vectors.  For `2 ≤ d ≤ n` we exhibit an injection
`Fin 6 → Mon d n` given by the six monomials

`x^d, x^{d-1}y, x^{d-1}z, x^{d-2}y^2, x^{d-2}yz, x^{d-2}z^2`,

whose exponent vectors are distinguished by their `y`- and `z`-exponents.
-/

namespace Work.HP

open Finsupp

noncomputable section

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

/-- The six exponent vectors `x^d, x^{d-1}y, x^{d-1}z, x^{d-2}y^2, x^{d-2}yz, x^{d-2}z^2`,
indexed by `Fin 6`. -/
private def sixEx (d n : ℕ) (hd : 2 ≤ d) (i0 i1 i2 : Fin (n + 1)) : Fin 6 → Mon d n
  | 0 => mkMon d n i0 i1 i2 d 0 0 (by omega)
  | 1 => mkMon d n i0 i1 i2 (d - 1) 1 0 (by omega)
  | 2 => mkMon d n i0 i1 i2 (d - 1) 0 1 (by omega)
  | 3 => mkMon d n i0 i1 i2 (d - 2) 2 0 (by omega)
  | 4 => mkMon d n i0 i1 i2 (d - 2) 1 1 (by omega)
  | 5 => mkMon d n i0 i1 i2 (d - 2) 0 2 (by omega)

/-- The `(y,z)`-exponents of the six witnesses: `(0,0), (1,0), (0,1), (2,0), (1,1), (0,2)`. -/
private def tag : Fin 6 → ℕ × ℕ
  | 0 => (0, 0)
  | 1 => (1, 0)
  | 2 => (0, 1)
  | 3 => (2, 0)
  | 4 => (1, 1)
  | 5 => (0, 2)

/-- The `(y,z)`-exponents of `sixEx` recover `tag`. -/
private lemma sixEx_tag (d n : ℕ) (hd : 2 ≤ d) (i0 i1 i2 : Fin (n + 1))
    (h01 : i0 ≠ i1) (h02 : i0 ≠ i2) (h12 : i1 ≠ i2) (k : Fin 6) :
    (((sixEx d n hd i0 i1 i2 k).1 i1 : ℕ), ((sixEx d n hd i0 i1 i2 k).1 i2 : ℕ)) = tag k := by
  fin_cases k <;>
    simp only [sixEx, tag, mkMon_apply_i1 (Ne.symm h01) h12,
      mkMon_apply_i2 (Ne.symm h02) (Ne.symm h12)]

/-- With `2 ≤ d ≤ n` there are at least `6` monomials of degree `d` in `n + 1` variables, i.e. `N_{d,n} ≥ 6`.  Explicit witnesses: the exponent vectors of `x^d`, `x^{d-1}y`, `x^{d-1}z`, `x^{d-2}y^2`, `x^{d-2}yz`, `x^{d-2}z^2`, which are pairwise distinct (they are separated by the exponents of `y` and `z`), using that `n ≥ d ≥ 2` gives at least the three coordinate directions `0, 1, 2`. -/
theorem six_le_NN (d n : ℕ) (hd : 2 ≤ d) (hdn : d ≤ n) : 6 ≤ NN d n := by
  let i0 : Fin (n + 1) := ⟨0, by omega⟩
  let i1 : Fin (n + 1) := ⟨1, by omega⟩
  let i2 : Fin (n + 1) := ⟨2, by omega⟩
  have h01 : i0 ≠ i1 := by simp [i0, i1, Fin.ext_iff]
  have h02 : i0 ≠ i2 := by simp [i0, i2, Fin.ext_iff]
  have h12 : i1 ≠ i2 := by simp [i1, i2, Fin.ext_iff]
  have hkey := sixEx_tag d n hd i0 i1 i2 h01 h02 h12
  have hTinj : Function.Injective tag := by decide
  have hinj : Function.Injective (sixEx d n hd i0 i1 i2) := by
    intro p q hpq
    apply hTinj
    rw [← hkey p, ← hkey q, hpq]
  have h := Fintype.card_le_of_injective (sixEx d n hd i0 i1 i2) hinj
  simpa using h

end

end Work.HP
