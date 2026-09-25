import Mathlib
import Submission.Work.HopfGaschutz.Defs

/-!
# `Work.ShafarevichKoch.not_relFrattiniAttainment_of_nontrivial_finiteTwoQuotient`

**Namespace** `Work.ShafarevichKoch`; module
`Submission.Work.ShafarevichKoch.not_relFrattiniAttainment_of_nontrivial_finiteTwoQuotient`.

This file machine-checks the refutation of the naive "Frattini/Nakayama" upgrade

> if `K ⊴ F` is finitely generated, `F ⧸ K` is a **nontrivial finite `2`-group**, and a finite set
> `S ⊆ K` satisfies `K ≤ ⟪S⟫^F · K²[K,F]`, then `S` may be replaced by a set `S'` with
> `S'.card ≤ S.card` which **normally generates** `K`,

i.e. the statement whose universal closure is the theorem proved here.

## The counterexample

Take the cyclic group of order `6`,

```
F = ℤ/6 = Multiplicative (ZMod 6),        K = the (unique) subgroup of order 3.
```

Then

* `K ⊴ F` is normal (the group is abelian) and `K ≅ ℤ/3`, so `K` is finitely generated;
* `F ⧸ K ≅ ℤ/2` is a **nontrivial finite `2`-group** -- so the counterexample is *not* an artefact
  of a trivial quotient (contrast `Work.ShafarevichKoch.not_relFrattiniAttainment_without_pgroup`,
  whose witness `F = K = ℤ/3` has trivial quotient);
* the squaring map of `K ≅ ℤ/3` is **bijective** (it is the inverse of cubing), so every element of
  `K` is a square of an element of `K`; hence `K = K²` and
  `Work.HopfGaschutz.relFrattini 2 K = K² ⊔ ⁅K,⊤⁆ = K`.

Take `S = ∅`.  Then `⟪∅⟫^F = ⊥` and the hypothesis of the claim reads
`K ≤ ⊥ ⊔ K²[K,F] = K`, which holds trivially.  But the conclusion would produce a finite set `S'`
with `S'.card ≤ 0`, i.e. `S' = ∅`, and `Work.HopfGaschutz.NormalGenerates K ∅` says exactly
`⟪∅⟫^F = K`, i.e. `⊥ = K` -- false because `K ≅ ℤ/3` is nontrivial.

## Why the counterexample has to look like this

The failure is caused by the **odd** part of `K`.  If `K` were a nontrivial *finite* `2`-group, then
`K²[K,⊤] ≤ Φ(K) = K²[K,K] < K` (Burnside's basis theorem), so `K ≤ K²[K,F]` would be impossible.
Enforcing `F ⧸ K` to be a nontrivial `2`-group does not remove the odd-order obstruction, because
the defect `K ⧸ ⟪S⟫^F` (here `K` itself, for `S = ∅`) still has prime-to-`2` quotients.  The
upgrade is a genuine *pro-`2`* phenomenon: there `K \hat{} ⧸ ⟪S⟫` is a compact pro-`2` group and
Nakayama over the completed group algebra `𝔽₂[[Γ]]` applies (the finite case of the same statement
is Gaschütz's theorem, `Work.HopfGaschutz.normalGeneratorNumber_eq_relFrattiniDim_of_finite_pgroup`).
-/

set_option linter.unusedVariables false

namespace Work.ShafarevichKoch

/-! The counterexample data for `not_relFrattiniAttainment_of_nontrivial_finiteTwoQuotient`:
`F = ℤ/6` together with its subgroup `K` of order `3`, inside which squaring is a bijection. -/
namespace RelFrattiniCounterexample

/-- The counterexample group `F = ℤ/6`, written multiplicatively. -/
abbrev F : Type := Multiplicative (ZMod 6)

/-- A generator `g` of the subgroup of order `3` (`g = ofAdd 2`). -/
def g : F := Multiplicative.ofAdd 2

/-- **The subgroup `K = {1, g, g²} ≅ ℤ/3` of `ℤ/6`.** -/
def K : Subgroup F where
  carrier := {1, g, g ^ 2}
  mul_mem' := by decide
  one_mem' := by decide
  inv_mem' := by decide

/-- `K` is normal: the group `ℤ/6` is abelian. -/
theorem K_normal : K.Normal := Subgroup.normal_of_isMulCommutative K

/-- The generator `g` lies in `K`. -/
theorem g_mem : g ∈ K := by
  show g ∈ ({1, g, g ^ 2} : Set F)
  simp

/-- The generator `g` is nontrivial. -/
theorem g_ne_one : g ≠ 1 := by decide

/-- `K` is nontrivial, hence `⟪∅⟫ ≠ K`. -/
theorem K_ne_bot : K ≠ ⊥ := fun hbot =>
  g_ne_one (Subgroup.mem_bot.mp (hbot ▸ g_mem))

/-- The element `ofAdd 1 ∉ K`: the class of `ofAdd 1` is the nontrivial element of `F ⧸ K ≅ ℤ/2`. -/
theorem ofAdd_one_not_mem : Multiplicative.ofAdd (1 : ZMod 6) ∉ K := by
  show Multiplicative.ofAdd (1 : ZMod 6) ∉ ({1, g, g ^ 2} : Set F)
  decide

/-- **Squaring is a bijection of `K ≅ ℤ/3`**: every element of `K` is the square of an element of
`K` (the squaring map is the inverse of the cubing map on `ℤ/3`). -/
theorem isSquare_mem : ∀ x ∈ K, ∃ k ∈ K, k ^ 2 = x := by
  show ∀ x ∈ ({1, g, g ^ 2} : Set F), ∃ k ∈ ({1, g, g ^ 2} : Set F), k ^ 2 = x
  decide

/-- Every element of `F = ℤ/6` has its square in `K = 2·(ℤ/6)`, so `F ⧸ K` has exponent `2`. -/
theorem sq_mem : ∀ x : F, x ^ 2 ∈ K := by
  show ∀ x : F, x ^ 2 ∈ ({1, g, g ^ 2} : Set F)
  decide

/-- `K` is finitely generated (it is finite). -/
theorem fg : K.FG := (Group.fg_iff_subgroup_fg K).mp (Group.fg_of_finite (G := ↥K))

/-- **`F ⧸ K` is a finite `2`-group**: it is the quotient `ℤ/6 ⧸ ⟨2⟩ ≅ ℤ/2`. -/
theorem isPGroup_quotient : IsPGroup 2 (F ⧸ K) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro x
  obtain ⟨a, rfl⟩ := QuotientGroup.mk'_surjective K x
  exact ⟨1, by
    rw [pow_one, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact sq_mem a⟩

/-- **`F ⧸ K` is nontrivial** (it is `ℤ/2`). -/
theorem nontrivial_quotient : Nontrivial (F ⧸ K) :=
  ⟨QuotientGroup.mk' K (Multiplicative.ofAdd (1 : ZMod 6)), 1, fun hc =>
    ofAdd_one_not_mem (by simpa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] using hc)⟩

/-- **`K ≤ K²[K,F]`**, i.e. `relFrattini 2 K = K`: every element of `K` is a square, and `K` is
abelian.  This is the hypothesis of the naive upgrade, with `S = ∅`. -/
theorem le_relFrattini : K ≤ Work.HopfGaschutz.relFrattini 2 K := by
  have hpp : K ≤ Work.HopfGaschutz.pPower 2 K := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := isSquare_mem x hx
    exact Subgroup.subset_closure ⟨k, hk, hkx⟩
  rw [Work.HopfGaschutz.relFrattini]
  exact hpp.trans le_sup_left

end RelFrattiniCounterexample

theorem not_relFrattiniAttainment_of_nontrivial_finiteTwoQuotient :
    ¬ (∀ (F : Type) [Group F] (K : Subgroup F) [K.Normal], K.FG →
        IsPGroup 2 (F ⧸ K) → Finite (F ⧸ K) → Nontrivial (F ⧸ K) →
        ∀ (S : Finset F), (S : Set F) ⊆ K →
        K ≤ Subgroup.normalClosure (S : Set F) ⊔ Work.HopfGaschutz.relFrattini 2 K →
        ∃ S' : Finset F, S'.card ≤ S.card ∧ Work.HopfGaschutz.NormalGenerates K S') := by
  rintro h
  -- The hypothesis of the claim holds for `F = ℤ/6`, `K = ⟨2⟩ ≅ ℤ/3` and `S = ∅`,
  -- because `⟪∅⟫^F = ⊥` and `relFrattini 2 K = K`.
  have hhyp : RelFrattiniCounterexample.K ≤
      Subgroup.normalClosure ((∅ : Finset RelFrattiniCounterexample.F) : Set RelFrattiniCounterexample.F) ⊔
        Work.HopfGaschutz.relFrattini 2 RelFrattiniCounterexample.K := by
    simpa using RelFrattiniCounterexample.le_relFrattini
  obtain ⟨S', hcard, hgen⟩ :=
    h RelFrattiniCounterexample.F RelFrattiniCounterexample.K
      RelFrattiniCounterexample.fg RelFrattiniCounterexample.isPGroup_quotient
      inferInstance RelFrattiniCounterexample.nontrivial_quotient
      (∅ : Finset RelFrattiniCounterexample.F) (by simp) hhyp
  -- But the conclusion forces `⟪S'⟫^F ≤ ⟪∅⟫^F = ⊥ = K`, contradiction.
  have hS'empty : S' = ∅ :=
    Finset.card_eq_zero.mp (Nat.le_zero.mp (by simpa using hcard))
  have hKbot : RelFrattiniCounterexample.K = ⊥ := by
    rw [← hgen, hS'empty]
    simp
  exact RelFrattiniCounterexample.K_ne_bot hKbot

end Work.ShafarevichKoch
