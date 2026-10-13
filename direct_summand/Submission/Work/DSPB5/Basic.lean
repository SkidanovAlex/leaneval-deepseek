import Mathlib
import Submission.Work.DSMap.Mix

/-!
# DSPB5 — torsion in a perfect ring of characteristic `p` is almost zero

This module is the vocabulary and the basic API of the area `DSPB5` of the project
`direct_summand`.  It is the algebraic foundation of the node **PB5** of the MIX design
(`sources/dsmap/direct_summand_mix_design.md`, §3 "PB5 `perfect_torsion_almostZero`:
`t·x = 0 ⇒ t^{1/p^e}·x = 0`"), which is used in the blowup-acyclicity computation **M5b**
("`t^∞`-torsion in perfect rings is almost zero").

The mathematical content is the following.  If `R` is a perfect ring of characteristic `p`
(Frobenius `x ↦ xᵖ` bijective), then:

* `R` is reduced — a perfect ring has no nonzero nilpotents
  (`DSMap.Mix.isReduced_of_perfectRing`, `DSMap.Mix.instIsReducedOfPerfectRing`); this is the
  only place where perfection is used, and every other statement of the area is a consequence
  of it;
* for `t x : R` with `t * x = 0` and every `e`, the `p^e`-th root `t ^ (1/p^e)`
  (i.e. `(frobeniusEquiv R p).symm^[e] t`) still annihilates `x`
  (`DSMap.Mix.isAlmostZeroAlong_of_mul_eq_zero`, whose `e`-th instance is exactly the frozen
  `DSMap.Mix.perfect_torsion_almostZero`);
* more generally `t ^ N * x = 0` suffices for every `N`
  (`DSMap.Mix.IsAlmostZeroAlong` + `DSMap.Mix.isAlmostZeroAlong_of_pow_mul_eq_zero`), which is
  the form in which the node is consumed downstream.

## Conventions

* The `p^e`-th root of `t` is written `DSMap.Mix.pthRootPow p R e t` (a plain function; it is
  the `e`-fold iterate of the inverse Frobenius `(frobeniusEquiv R p).symm`).  The frozen
  statement spells it out as `(frobeniusEquiv R p).symm^[e] t`; the two are definitionally
  equal, and `simp only [DSMap.Mix.pthRootPow]` converts between them.
* `DSMap.Mix.IsAlmostZeroAlong p R t x` says `∀ e, pthRootPow p R e t * x = 0`: "`x` is almost
  zero along the tower of `p`-power roots of `t`".  This is the elementwise form of the notion
  `DSMap.AlmostZero` of `Submission/Work/DSMap/Map.lean` with `ϖ k = pthRootPow p R k t`.
* Everything lives in the namespace `DSMap.Mix`, next to the frozen statement it serves.
-/

namespace DSMap.Mix

universe a

/-! ## Perfection implies reducedness -/

/-- A perfect ring of characteristic `p > 1` is reduced: if `x ^ n = 0`, then also
`x ^ p ^ n = 0`, i.e. `(frobenius R p)^[n] x = 0`, and the `n`-fold iterate of the Frobenius
map is injective for a perfect ring.

(The hypothesis `1 < p` cannot be dropped: for `p = 1` the Frobenius is the identity, every
ring is perfect, and e.g. `ZMod 4` is not reduced.  For `p` prime it holds.) -/
theorem isReduced_of_perfectRing (R : Type a) [CommRing R] (p : ℕ) [ExpChar R p] (hp : 1 < p)
    [PerfectRing R p] : IsReduced R := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨n, hn⟩ := hx
  have hx0 : x ^ (p ^ n) = 0 :=
    pow_eq_zero_of_le (le_of_lt (Nat.lt_pow_self (n := n) (a := p) hp)) hn
  have h1 : (frobenius R p)^[n] x = 0 := by rw [iterate_frobenius, hx0]
  have h2 : (frobenius R p)^[n] (0 : R) = 0 := Function.iterate_fixed (map_zero _) n
  exact (injective_frobenius R p).iterate n (h1.trans h2.symm)

/-- Instance form of `isReduced_of_perfectRing` in the characteristic-`p` setting of the MIX
subtree: a perfect ring of characteristic a prime `p` is reduced.  (Low priority, so that the
ambient `NoZeroDivisors`/`Subsingleton` routes are still tried first.) -/
instance instIsReducedOfPerfectRing (R : Type a) [CommRing R] (p : ℕ) [Fact p.Prime]
    [CharP R p] [PerfectRing R p] : IsReduced R :=
  isReduced_of_perfectRing R p (Nat.Prime.one_lt Fact.out)

/-! ## The `p^e`-th root operator -/

section Root

variable (p : ℕ) (R : Type a) [CommSemiring R] [ExpChar R p] [PerfectRing R p]

/-- `pthRootPow p R e t = t ^ (1/p^e)`, the `e`-th iterate of the inverse Frobenius
automorphism of a perfect ring: `((frobeniusEquiv R p).symm)^[e] t`. -/
noncomputable def pthRootPow (e : ℕ) (t : R) : R := ((frobeniusEquiv R p).symm^[e]) t

@[simp]
lemma pthRootPow_unfold (e : ℕ) (t : R) : pthRootPow p R e t = ((frobeniusEquiv R p).symm^[e]) t :=
  rfl

@[simp]
lemma pthRootPow_zero (t : R) : pthRootPow p R 0 t = t := rfl

/-- The defining property of the root operator: `(t^{1/p^e})^{p^e} = t`. -/
@[simp]
lemma pthRootPow_pow (e : ℕ) (t : R) : pthRootPow p R e t ^ p ^ e = t :=
  iterate_frobeniusEquiv_symm_pow_p_pow R p t e

/-- Iterating the root operator. -/
lemma pthRootPow_add_apply (e₁ e₂ : ℕ) (t : R) :
    pthRootPow p R (e₁ + e₂) t = pthRootPow p R e₁ (pthRootPow p R e₂ t) := by
  simp only [pthRootPow, Function.iterate_add_apply]

/-- One step of the root tower: the next root is obtained by applying the inverse Frobenius. -/
lemma pthRootPow_succ_apply (e : ℕ) (t : R) :
    pthRootPow p R (e + 1) t = (frobeniusEquiv R p).symm (pthRootPow p R e t) := by
  simp only [pthRootPow, Function.iterate_succ_apply']

/-- **The roots of `t` form a compatible tower**: `(t^{1/p^{e+1}})^p = t^{1/p^e}`.  This is
exactly the compatibility `PerfectoidData.root` (`DSMap.PerfectoidData.ϖ (k+1)^p = ϖ k`,
`Submission/Work/DSMap/Map.lean`) of the `ϖ`-tower `k ↦ pthRootPow p R k t` attached to an
element of a perfect ring of characteristic `p`. -/
lemma pthRootPow_pow_succ (e : ℕ) (t : R) :
    pthRootPow p R (e + 1) t ^ p = pthRootPow p R e t := by
  apply (frobeniusEquiv R p).injective.iterate e
  simp only [coe_frobeniusEquiv, iterate_frobenius]
  rw [← pow_mul, ← pow_succ', pthRootPow_pow, pthRootPow_pow]

end Root

/-! ## Almost vanishing along a tower of `p`-power roots -/

section AlmostZero

variable (p : ℕ) [Fact p.Prime] (R : Type a) [CommRing R] [CharP R p] [PerfectRing R p]

/-- `x` is almost zero along the tower of `p`-power roots of `t`: every iterate of the root
operator applied to `t` annihilates `x`.  With `ϖ k := pthRootPow p R k t` this is
`ϖ k * x = 0` for all `k`, i.e. the elementwise form of `DSMap.AlmostZero ϖ _` for the cyclic
submodule generated by `x` (`Work.DSPB5.almostZero_span_singleton`,
`Work.DSPB5.almostZero_span_of_pow_mul_eq_zero`). -/
def IsAlmostZeroAlong (t x : R) : Prop := ∀ e : ℕ, pthRootPow p R e t * x = 0

theorem isAlmostZeroAlong_iff {t x : R} :
    IsAlmostZeroAlong p R t x ↔ ∀ e : ℕ, pthRootPow p R e t * x = 0 := Iff.rfl

/-- **PB5** (interface form): in a perfect ring of characteristic `p`, `t * x = 0` implies that
every `p`-power root of `t` annihilates `x`.  The `e`-th instance is the frozen
`DSMap.Mix.perfect_torsion_almostZero`; see also `DSMap.Mix.perfect_torsion_almostZero_proved`
for the copy of the frozen statement itself.

The proof: `s := t^{1/p^e}` satisfies `s ^ p^e = t`, so
`(s * x) ^ p^e = s ^ p^e * x ^ p^e = t * x * x ^ (p^e - 1) = 0`, and `R` is reduced
(`isReduced_of_perfectRing`), so `s * x = 0`. -/
theorem isAlmostZeroAlong_of_mul_eq_zero {t x : R} (h : t * x = 0) :
    IsAlmostZeroAlong p R t x := by
  haveI : IsReduced R := isReduced_of_perfectRing R p (Nat.Prime.one_lt Fact.out)
  intro e
  set s : R := pthRootPow p R e t with hs
  have hpow : s ^ p ^ e = t := by
    rw [hs]
    exact pthRootPow_pow p R e t
  have h1le : 1 ≤ p ^ e := Nat.one_le_pow e p (Nat.Prime.pos Fact.out)
  have hx : x ^ (p ^ e) = x * x ^ (p ^ e - 1) := by
    conv_lhs => rw [← Nat.sub_add_cancel h1le, pow_add, pow_one]
    rw [mul_comm]
  have hmain : (s * x) ^ (p ^ e) = 0 := by
    rw [mul_pow, hpow, hx, ← mul_assoc, h, zero_mul]
  exact eq_zero_of_pow_eq_zero hmain

/-- In a perfect ring of characteristic `p`, a compatible tower of `p`-th roots of `t`
(`ϖ 0 = t` and `ϖ (k+1) ^ p = ϖ k`, exactly the shape of the field `PerfectoidData.root` of
`DSMap.PerfectoidData`) is unique, hence equal to the tower of iterated root operators. -/
theorem rootTower_eq_pthRootPow (t : R) (ϖ : ℕ → R) (h0 : ϖ 0 = t)
    (hroot : ∀ k, ϖ (k + 1) ^ p = ϖ k) (k : ℕ) : ϖ k = pthRootPow p R k t := by
  induction k with
  | zero => rw [h0, pthRootPow_zero]
  | succ k ih =>
    apply (frobeniusEquiv R p).injective
    simp only [frobeniusEquiv_def]
    rw [hroot k, ih, ← pthRootPow_pow_succ]

/-- **PB5 in `PerfectoidData`-tower form**: if `ϖ` is a compatible tower of `p`-th roots of `t`
(as produced by the perfectoid nodes `M4`/`M5c`, cf. `DSMap.PerfectoidData.root`) and `t * x = 0`,
then every element of the tower annihilates `x`. -/
theorem isAlmostZeroAlong_of_rootTower (t x : R) (h : t * x = 0) (ϖ : ℕ → R) (h0 : ϖ 0 = t)
    (hroot : ∀ k, ϖ (k + 1) ^ p = ϖ k) (k : ℕ) : ϖ k * x = 0 := by
  rw [rootTower_eq_pthRootPow p R t ϖ h0 hroot k]
  exact isAlmostZeroAlong_of_mul_eq_zero p R h k

/-- The elements that are almost zero along the tower of `p`-power roots of `t` form an ideal of
`R`: `IsAlmostZeroAlong p R t` is closed under addition and under multiplication by arbitrary
elements of `R` (which is commutative). -/
def almostZeroIdeal (t : R) : Ideal R where
  carrier := {x | IsAlmostZeroAlong p R t x}
  add_mem' hx hy := by
    intro e
    rw [mul_add, hx e, hy e, add_zero]
  zero_mem' := by
    intro e
    rw [mul_zero]
  smul_mem' := fun c b hb => by
    intro e
    rw [smul_eq_mul, mul_left_comm, hb e, mul_zero]

@[simp]
lemma mem_almostZeroIdeal {t x : R} :
    x ∈ almostZeroIdeal p R t ↔ IsAlmostZeroAlong p R t x := Iff.rfl

/-- `IsAlmostZeroAlong` is closed under right multiplication. -/
theorem isAlmostZeroAlong_mul_right {t x : R} (hx : IsAlmostZeroAlong p R t x) (c : R) :
    IsAlmostZeroAlong p R t (x * c) := by
  intro e
  rw [← mul_assoc, hx e, zero_mul]

/-- `IsAlmostZeroAlong` is closed under left multiplication. -/
theorem isAlmostZeroAlong_mul_left {t x : R} (hx : IsAlmostZeroAlong p R t x) (c : R) :
    IsAlmostZeroAlong p R t (c * x) := by
  intro e
  rw [mul_left_comm, hx e, mul_zero]

end AlmostZero

end DSMap.Mix
