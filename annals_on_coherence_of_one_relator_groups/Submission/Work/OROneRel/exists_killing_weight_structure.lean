/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# A "killing weight" concentrated on two prescribed letters, with a structural alternative

Given a relator `u : FreeGroup α` of norm `≥ 2`, not a proper power, all of whose letters have
nonzero exponent sum, `exists_killing_weight_structure` produces a weight `c : α → ℤ` that

* kills the relator, `cohom c u = 1` (so `∑ₓ c x * eps x u = 0`);
* is concentrated on two distinct letters `x0 ≠ y0` of `u`: `c` vanishes off `{x0, y0}`;
* takes nonzero values `cx = c x0`, `cy = c y0` there, together with Bézout data `p, q` witnessing
  that `(cx, cy)` is a primitive vector of the kernel;
* is *unimodular*: `cohom c τ = ofAdd 1` for some `τ`, so `cohom c : F α →* Multiplicative ℤ` is
  surjective;
* satisfies one of the structural alternatives `(∃ z, c z = 1)` or `c x0 ≠ c y0 ∧ c x0 ≠ - c y0`,
  which prevents the two-letter weight from collapsing to a single direction.

The last alternative is what distinguishes this statement from the earlier
`exists_killing_weight_letters`: there the weights are produced by the fixed sign convention of
`exists_weight_vector`, which can output a vector `(cx, cy) = (-1, -1)` when `eps x0 u = - eps y0 u`;
flipping the sign of the vector then puts a `+1` on one of the two letters.  The integer input to the
assembly is isolated in `exists_weight_vector_structured`.
-/
import Mathlib
import Submission.Work.OROneRel.exists_two_mem_relatorLetters_ne
import Submission.Work.OROneRel.exists_weight_vector
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.cohom_mk
import Submission.Work.OROneRel.lsig_eq_smul_wordEps

namespace Work.OROneRel

universe u

/-- For nonzero integers `m n`, there is a *primitive* vector `(cx, cy)` in the kernel of
`(x, y) ↦ x * m + y * n` with both coordinates nonzero, such that either one coordinate equals `1`
or the vector is asymmetric with respect to the two reflections `(x,y) ↦ (y,x)` and
`(x,y) ↦ (-y,x)`:

`(cx = 1 ∨ cy = 1) ∨ (cx ≠ cy ∧ cx ≠ -cy)`.

The vector is the one produced by `exists_weight_vector`, flipped in sign when necessary.  Indeed, if
the result `(cx, cy)` of `exists_weight_vector` is not already good, then `cx = cy` or `cx = -cy`
(that is, it is fixed by one of the two reflections); substituting into the kernel equation
`cx * m + cy * n = 0` and the Bézout relation `p * cx + q * cy = 1` forces `cx = ± 1`; since
`cx ≠ 1` by hypothesis, `-cx = 1`, so the flipped vector satisfies the first alternative. -/
theorem exists_weight_vector_structured {m n : ℤ} (hm : m ≠ 0) (hn : n ≠ 0) :
    ∃ (cx cy p q : ℤ), cx * m + cy * n = 0 ∧ p * cx + q * cy = 1 ∧ cx ≠ 0 ∧ cy ≠ 0 ∧
      ((cx = 1 ∨ cy = 1) ∨ (cx ≠ cy ∧ cx ≠ -cy)) := by
  obtain ⟨cx, cy, p, q, hsum, hbez⟩ := Work.OROneRel.exists_weight_vector hm hn
  -- The Bézout relation forces both coordinates to be nonzero.
  have hcx : cx ≠ 0 := by
    intro h0
    rw [h0, zero_mul, zero_add] at hsum
    have : cy = 0 := (mul_eq_zero.mp hsum).resolve_right hn
    rw [h0, this] at hbez; simp at hbez
  have hcy : cy ≠ 0 := by
    intro h0
    rw [h0, zero_mul, add_zero] at hsum
    have : cx = 0 := (mul_eq_zero.mp hsum).resolve_right hm
    rw [this, h0] at hbez; simp at hbez
  by_cases hcase : (cx = 1 ∨ cy = 1) ∨ (cx ≠ cy ∧ cx ≠ -cy)
  · exact ⟨cx, cy, p, q, hsum, hbez, hcx, hcy, hcase⟩
  · -- The vector produced by `exists_weight_vector` is not good; the flipped vector is.
    push Not at hcase
    obtain ⟨⟨hne1a, hne1b⟩, hcat⟩ := hcase
    refine ⟨-cx, -cy, -p, -q, ?_, ?_, neg_ne_zero.mpr hcx, neg_ne_zero.mpr hcy, ?_⟩
    · nlinarith [hsum]
    · nlinarith [hbez]
    · left; left
      by_cases hcc : cx = cy
      · -- `cx = cy` forces `cx * (p + q) = 1`, hence `cx = ± 1`; and `cx ≠ 1`.
        have h1 : cx * (p + q) = 1 := by subst hcc; linear_combination hbez
        rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with hc | hc
        · exact absurd hc hne1a
        · omega
      · -- `cx = -cy` forces `cx * (p - q) = 1`, hence `cx = ± 1`; and `cx ≠ 1`.
        have hc : cx = -cy := hcat hcc
        have h1 : cx * (p - q) = 1 := by subst hc; linear_combination hbez
        rcases Int.eq_one_or_neg_one_of_mul_eq_one h1 with hc' | hc'
        · exact absurd hc' hne1a
        · omega

theorem exists_killing_weight_structure {α : Type u} [Fintype α] [DecidableEq α] (u : FreeGroup α)
    (hn : 2 ≤ Work.OROneRel.relatorNorm u) (hu : ¬ Work.OROneRel.IsProperPower u)
    (hbad : ∀ x : α, x ∈ Work.OROneRel.relatorLetters u → Work.OROneRel.eps x u ≠ 0) :
    ∃ (c : α → ℤ) (x0 y0 : α) (cx cy : ℤ) (τ : FreeGroup α) (p q : ℤ),
      x0 ∈ Work.OROneRel.relatorLetters u ∧ y0 ∈ Work.OROneRel.relatorLetters u ∧ x0 ≠ y0 ∧
      cx ≠ 0 ∧ cy ≠ 0 ∧ Function.Surjective (Work.OROneRel.cohom c) ∧
      Work.OROneRel.cohom c u = 1 ∧ Work.OROneRel.cohom c τ = Multiplicative.ofAdd 1 ∧
      c x0 = cx ∧ c y0 = cy ∧ (∀ z : α, z ≠ x0 → z ≠ y0 → c z = 0) ∧
      cx * Work.OROneRel.eps x0 u + cy * Work.OROneRel.eps y0 u = 0 ∧ p * cx + q * cy = 1 ∧
      ((∃ z : α, c z = 1) ∨ (c x0 ≠ c y0 ∧ c x0 ≠ - c y0)) := by
  classical
  -- Two distinct letters of `u`; their exponent sums are nonzero by `hbad`.
  obtain ⟨x0, hx0, y0, hy0, hxy⟩ := Work.OROneRel.exists_two_mem_relatorLetters_ne u hn hu
  have hm : Work.OROneRel.eps x0 u ≠ 0 := hbad x0 hx0
  have hn' : Work.OROneRel.eps y0 u ≠ 0 := hbad y0 hy0
  -- The primitive kernel vector with the structural alternative.
  obtain ⟨cx, cy, p, q, hsum, hbez, hcx, hcy, hcond⟩ :=
    exists_weight_vector_structured hm hn'
  -- The weight `c`, concentrated on `x0` and `y0`.
  let c : α → ℤ := fun z => if z = x0 then cx else if z = y0 then cy else 0
  have hcx0 : c x0 = cx := by simp [c]
  have hcy0 : c y0 = cy := by
    show (if y0 = x0 then cx else if y0 = y0 then cy else 0) = cy
    rw [if_neg (Ne.symm hxy), if_pos rfl]
  have hc0 : ∀ z : α, z ≠ x0 → z ≠ y0 → c z = 0 := by
    intro z hza hzb
    show (if z = x0 then cx else if z = y0 then cy else 0) = 0
    rw [if_neg hza, if_neg hzb]
  have hepsx : Work.OROneRel.eps x0 u = Work.OROneRel.wordEps x0 (Work.OROneRel.wordOf u) := rfl
  have hepsy : Work.OROneRel.eps y0 u = Work.OROneRel.wordEps y0 (Work.OROneRel.wordOf u) := rfl
  refine ⟨c, x0, y0, cx, cy, FreeGroup.of x0 ^ p * FreeGroup.of y0 ^ q, p, q,
    hx0, hy0, hxy, hcx, hcy, ?_, ?_, ?_, hcx0, hcy0, hc0, hsum, hbez, ?_⟩
  · -- `cohom c` is surjective: `τ^k` has weight `k` for every `k : ℤ`.
    intro y
    obtain ⟨k, rfl⟩ := Multiplicative.ofAdd.surjective y
    refine ⟨(FreeGroup.of x0 ^ p * FreeGroup.of y0 ^ q) ^ k, ?_⟩
    rw [map_zpow, map_mul, map_zpow, map_zpow, Work.OROneRel.cohom_of, Work.OROneRel.cohom_of,
      hcx0, hcy0]
    have hcomm : cx * p + cy * q = 1 := by rw [mul_comm cx p, mul_comm cy q]; exact hbez
    rw [← Int.ofAdd_mul cx p, ← Int.ofAdd_mul cy q, ← ofAdd_add, hcomm]
    rw [← Int.ofAdd_mul 1 k]
    simp
  · -- `cohom c u = 1`, the weighted exponent sum of `u` being `cx * eps x0 u + cy * eps y0 u`.
    have h1 : Work.OROneRel.cohom c u
        = Multiplicative.ofAdd (Work.OROneRel.lsig c (Work.OROneRel.wordOf u)) := by
      conv_lhs => rw [← Work.OROneRel.mk_wordOf u]
      exact Work.OROneRel.cohom_mk c (Work.OROneRel.wordOf u)
    rw [h1, Work.OROneRel.lsig_eq_smul_wordEps c x0 y0 hxy hc0 (Work.OROneRel.wordOf u),
      ← hepsx, ← hepsy, hcx0, hcy0, hsum]
    simp
  · -- `cohom c τ = ofAdd 1`, from the Bézout relation `p * cx + q * cy = 1`.
    rw [map_mul, map_zpow, map_zpow, Work.OROneRel.cohom_of, Work.OROneRel.cohom_of, hcx0, hcy0]
    have hcomm : cx * p + cy * q = 1 := by rw [mul_comm cx p, mul_comm cy q]; exact hbez
    rw [← Int.ofAdd_mul cx p, ← Int.ofAdd_mul cy q, ← ofAdd_add, hcomm]
  · -- The structural alternative.
    rcases hcond with (h | h) | ⟨h1, h2⟩
    · left; exact ⟨x0, by rw [hcx0]; exact h⟩
    · left; exact ⟨y0, by rw [hcy0]; exact h⟩
    · right; exact ⟨by rw [hcx0, hcy0]; exact h1, by rw [hcx0, hcy0]; exact h2⟩

end Work.OROneRel
