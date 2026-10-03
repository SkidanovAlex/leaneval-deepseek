/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# A weight vector killing a relator with no letter of exponent sum zero

Given a relator `u : FreeGroup α` with `2 ≤ relatorNorm u`, `u` not a proper power, and such that
*no* letter occurring in `u` has exponent sum zero, this file produces a homomorphism
`cohom c : F α →* Multiplicative ℤ` which is **surjective** and kills `u`, together with an element
`τ` of weight `1`.  Concretely (writing `eps x u` for the exponent sum of `x` in `u`):
choose two distinct letters `x ≠ y` of `u` -- they exist because an element of `F α` involving a
single generator is a power of that generator, hence a proper power as soon as its length is `≥ 2`.
Choose integers `cx, cy, p, q` with `cx * eps x u + cy * eps y u = 0` and `p * cx + q * cy = 1`
(a kernel vector of `(eps x u, eps y u)` made primitive, e.g. `cx = eps y u / gcd`,
`cy = - eps x u / gcd`), put `c = cx` on `x`, `c = cy` on `y` and `c = 0` elsewhere, and
`τ = x ^ p * y ^ q`.  Then `cohom c u = 1` and `cohom c τ = Multiplicative.ofAdd 1`, so that
`cohom c` is onto (`τ` generates `Multiplicative ℤ`).

This is exactly the input needed to run the Magnus rewriting `rhoC` / `decor` of `MagnusGenDefs`
with respect to a *general* homomorphism `F α →* ℤ`: `c` kills `u` (so that the decorations
telescope) and has `1` in its image (so that the symbol `(x, i)` really stands for the conjugate
`τ ^ i * x * τ ^ (-i - c x)`).
-/
import Mathlib
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.MagnusRewrite
import Submission.Work.OROneRel.cohom_mk
import Submission.Work.OROneRel.lsig_eq_smul_wordEps
import Submission.Work.OROneRel.exists_two_mem_relatorLetters_ne
import Submission.Work.OROneRel.exists_weight_vector

namespace Work.OROneRel

universe u

theorem exists_covec_killing {α : Type u} (u : FreeGroup α) (hn : 2 ≤ Work.OROneRel.relatorNorm u)
    (hu : ¬ Work.OROneRel.IsProperPower u)
    (hbad : ∀ x : α, x ∈ Work.OROneRel.relatorLetters u → Work.OROneRel.eps x u ≠ 0) :
    ∃ c : α → ℤ, Function.Surjective (Work.OROneRel.cohom c) ∧ Work.OROneRel.cohom c u = 1 ∧
      ∃ τ : FreeGroup α, Work.OROneRel.cohom c τ = Multiplicative.ofAdd 1 := by
  classical
  -- Two distinct letters of `u`; both have nonzero exponent sum by `hbad`.
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_two_mem_relatorLetters_ne u hn hu
  have hm : eps x u ≠ 0 := hbad x hx
  have hn' : eps y u ≠ 0 := hbad y hy
  -- A kernel vector of `(eps x u, eps y u)` made primitive.
  obtain ⟨cx, cy, p, q, hsum, hbez⟩ := exists_weight_vector hm hn'
  let c : α → ℤ := fun z => if z = x then cx else if z = y then cy else 0
  have hcx : c x = cx := by simp [c]
  have hcy : c y = cy := by
    show (if y = x then cx else if y = y then cy else 0) = cy
    rw [if_neg (Ne.symm hxy), if_pos rfl]
  have hc0 : ∀ z : α, z ≠ x → z ≠ y → c z = 0 := by
    intro z hzx hzy
    show (if z = x then cx else if z = y then cy else 0) = 0
    rw [if_neg hzx, if_neg hzy]
  have hepsx : eps x u = wordEps x u.toWord := rfl
  have hepsy : eps y u = wordEps y u.toWord := rfl
  -- The weight of `u` under `cohom c` is `cx * eps x u + cy * eps y u`.
  have hcohom : cohom c u = Multiplicative.ofAdd (cx * eps x u + cy * eps y u) := by
    have h1 : cohom c u = Multiplicative.ofAdd (lsig c u.toWord) := by
      conv_lhs => rw [← FreeGroup.mk_toWord (x := u)]
      exact cohom_mk c u.toWord
    rw [h1, lsig_eq_smul_wordEps c x y hxy hc0 u.toWord, hepsx, hepsy, hcx, hcy]
  -- `τ = x ^ p * y ^ q` has weight `p * cx + q * cy = 1`.
  have hτ : cohom c ((FreeGroup.of x) ^ p * (FreeGroup.of y) ^ q) = Multiplicative.ofAdd 1 := by
    rw [map_mul, map_zpow, map_zpow, cohom_of, cohom_of, hcx, hcy]
    rw [← Int.ofAdd_mul cx p, ← Int.ofAdd_mul cy q, ← ofAdd_add]
    rw [mul_comm cx p, mul_comm cy q, hbez]
  refine ⟨c, ?_, ?_, ?_⟩
  · intro w
    exact ⟨((FreeGroup.of x) ^ p * (FreeGroup.of y) ^ q) ^ (w.toAdd), by
      rw [map_zpow, hτ, ← Int.ofAdd_mul (1 : ℤ) (w.toAdd)]
      simp⟩
  · rw [hcohom, hsum]
    simp
  · exact ⟨(FreeGroup.of x) ^ p * (FreeGroup.of y) ^ q, hτ⟩

end Work.OROneRel
