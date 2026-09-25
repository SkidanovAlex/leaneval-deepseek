/-
# The level of `a · x` and the annihilator at a lower level

`Eval/smulDiv_ann.lean` computes the annihilator of a torsion point `x ∈ Λ_n ∖ Λ_{n-1}` *at its own
level*: `{a : a · x = 0} = (π^n)`.  This file generalises both the annihilator statement and its
consequence to an element `z ∈ Λ_N` of *level* `m ≤ N`, with the action taken at level `N`:

  `{a : a · z = 0} = (π^m)`   and   `a · z ∈ Λ_j ↔ a ∈ (π^{m-j})`  (`j ≤ m`).

These are the statements the induction of `Eval/ltLevelIsSimple.lean` uses to convert the
`𝒪[F]`-orbit of a primitive point into its *unit* orbit: if `c = b · π x` is primitive of level `n`
then `n = n - v(b)`, so `b` is a unit.

## Main results

* `NK.LocalReciprocityLubinTate.Eval.smulDiv_eq_zero_iff_of_mem` (annihilator at level `N`);
* `NK.LocalReciprocityLubinTate.Eval.smulDiv_mem_iff_mem_span` (the level of `a · z`).
-/
import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Eval.smulDiv_ann

open scoped ValuativeRel
open Polynomial MvPowerSeries

namespace NK.LocalReciprocityLubinTate.Eval

set_option linter.style.haveILetI false

universe u

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- **The annihilator of a torsision point of level `m`, for the action at a higher level `N`.**
If `z ∈ Λ_m ∖ Λ_{m-1}` and `m ≤ N`, then `a · z = 0` (with the level-`N` action) if and only if
`a ∈ (π^m)`.

The proof is the one of `smulDiv_eq_zero_iff` at the level `m`, but with the level-`N` action: the
bridge `smulDiv_pi_pow` and the multiplicativity `smulDiv_smul2` are level-independent, so only the
primitiveness of `z` at level `m` is used. -/
theorem smulDiv_eq_zero_iff_of_mem (π : O F) (hπ : Irreducible π) (q N : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (O F) π q)
    (hpi : M.toLaw.piEndo = NK.LocalReciprocityLubinTate.piXAddXq π q)
    {z : AlgebraicClosure F} {m : ℕ}
    (hzN : z ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q N)
    (hzm : z ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q m)
    (hz' : z ∉ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q (m - 1))
    (hm : m ≤ N) (a : O F) :
    smulDiv π hπ q N hq M hzN a = 0 ↔ a ∈ Ideal.span {π ^ m} := by
  constructor
  · intro h
    rcases eq_or_ne a 0 with rfl | ha0
    · exact Ideal.zero_mem _
    · obtain ⟨j, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible ha0 hπ
      have hstep : smulDiv π hπ q N hq M hzN (π ^ j) = 0 := by
        have h2 := smulDiv_smul2 π hπ q N hq M hpi z hzN (↑u) (π ^ j)
        have h3 : smulDiv π hπ q N hq M
            (smulDiv_mem π hπ q N hq M hpi z hzN (π ^ j)) (↑u) = 0 := by
          rw [h2, ← hu]
          exact h
        exact smulDiv_unit_eq_zero π hπ q N hq M hpi _ u h3
      have hzj : z ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q j := by
        rw [NK.LocalReciprocityLubinTate.mem_LTdivisionSet_iff (π : F) q j hq,
          ← smulDiv_pi_pow π hπ q N hq M hpi z hzN j]
        exact hstep
      have hmj : m ≤ j := by
        by_contra hj
        push_neg at hj
        exact hz' (NK.LocalReciprocityLubinTate.LTdivisionSet_mono F (π : F) q hq
          (by omega) hzj)
      rw [Ideal.mem_span_singleton]
      refine ⟨↑u * π ^ (j - m), ?_⟩
      have hpowe : π ^ m * π ^ (j - m) = π ^ j := by
        rw [← pow_add, Nat.add_sub_cancel' hmj]
      rw [hu, ← hpowe]
      ring
  · intro ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    rw [mul_comm]
    rw [← smulDiv_smul2 π hπ q N hq M hpi z hzN c (π ^ m)]
    have hpown : smulDiv π hπ q N hq M hzN (π ^ m) = 0 := by
      rw [smulDiv_pi_pow π hπ q N hq M hpi z hzN m,
        NK.LocalReciprocityLubinTate.mem_LTdivisionSet_iff (π : F) q m hq] at *
      exact hzm
    rw [smulDiv_congr π hπ q N hq M _ (zero_mem_LTdivisionSet (F := F) π q N hq) hpown,
      smulDiv_zero]

/-- **The level of `a · z`.**  For `z ∈ Λ_m ∖ Λ_{m-1}` (with `m ≤ N`) and `j ≤ m`,

  `a · z ∈ Λ_j ↔ a ∈ (π^{m-j})`.

Indeed `a · z ∈ Λ_j` iff `π^j · (a · z) = 0` (the bridge), i.e. iff `(π^j a) · z = 0`
(`smulDiv_smul2`), which by the annihilator computation is `π^j a ∈ (π^m)`, i.e.
`a ∈ (π^{m-j})`. -/
theorem smulDiv_mem_iff_mem_span (π : O F) (hπ : Irreducible π) (q N : ℕ) (hq : 2 ≤ q)
    (M : LubinTateModule (O F) π q)
    (hpi : M.toLaw.piEndo = NK.LocalReciprocityLubinTate.piXAddXq π q)
    {z : AlgebraicClosure F} {m : ℕ}
    (hzN : z ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q N)
    (hzm : z ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q m)
    (hz' : z ∉ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q (m - 1))
    (hm : m ≤ N) (j : ℕ) (hj : j ≤ m) (a : O F) :
    smulDiv π hπ q N hq M hzN a
        ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q j ↔
      a ∈ Ideal.span {π ^ (m - j)} := by
  have hmem : smulDiv π hπ q N hq M hzN a
      ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q N :=
    smulDiv_mem π hπ q N hq M hpi z hzN a
  -- `a · z ∈ Λ_j` iff `π^j · (a · z) = 0`
  have hiff : smulDiv π hπ q N hq M hzN a
      ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F (π : F) q j ↔
      smulDiv π hπ q N hq M hmem (π ^ j) = 0 := by
    rw [NK.LocalReciprocityLubinTate.mem_LTdivisionSet_iff (π : F) q j hq,
      ← smulDiv_pi_pow π hπ q N hq M hpi _ hmem j]
  rw [hiff, smulDiv_smul2 π hπ q N hq M hpi z hzN (π ^ j) a]
  -- the annihilator computation at level `N` for the level-`m` point `z`
  rw [smulDiv_eq_zero_iff_of_mem π hπ q N hq M hpi hzN hzm hz' hm (π ^ j * a)]
  constructor
  · intro h
    rw [Ideal.mem_span_singleton] at h ⊢
    obtain ⟨c, hc⟩ := h
    refine ⟨c, ?_⟩
    have hpowe : π ^ m = π ^ j * π ^ (m - j) := by
      rw [← pow_add, Nat.add_sub_cancel' hj]
    rw [hpowe, mul_assoc] at hc
    exact mul_left_cancel₀ (pow_ne_zero j hπ.ne_zero) hc
  · intro h
    rw [Ideal.mem_span_singleton] at h ⊢
    obtain ⟨c, hc⟩ := h
    refine ⟨c, ?_⟩
    have hpowe : π ^ j * π ^ (m - j) = π ^ m := by
      rw [← pow_add, Nat.add_sub_cancel' hj]
    rw [← hpowe, hc, mul_assoc]

end NK.LocalReciprocityLubinTate.Eval
