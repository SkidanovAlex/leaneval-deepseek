import Submission.Work.DSMap.Mix2

/-!
# DSAMR: `ModSplit` from almost acyclicity — vocabulary

Area owner: curric-46 DSAMR.  Requester: `fundmath3-direct_summand-lead` (MIX2 subtree).
Deliverable: `DSMap.Mix2.modSplit_of_almostAcyc_proved`, type-identical to the frozen
`DSMap.Mix2.modSplit_of_almostAcyc` (`Submission/Work/DSMap/Mix2.lean`, node **AMR** of
`sources/dsmap/direct_summand_mix2.md`).

## The mathematics

Let `ψ : A →+* W` be a ring map, `I ⊆ W` an ideal, `ϖ : ℕ → W` a compatible system of `p`-th roots
(`ϖ (k+1) ^ p = ϖ k`), `K` a cochain complex of `W`-modules concentrated in degrees `≥ 0` with a
coaugmentation `e : W → K⁰`, `P` a bounded-above complex of finite free `A`-modules,
`ε : A → P⁰` a cocycle and `ρ : P → K` a chain map with `ρ⁰ (ε 1) = e 1`.

**If `K` is `I`-almost acyclic relative to `e` then `ModSplit P ε ψ I (ϖ k)` holds for every `k`.**

This file contains the vocabulary of the area:

* `Work.DSAMR.AlmostAcycZ` — the (frozen) `DSMap.Mix2.AlmostAcyc` predicate for a `ℤ`-indexed
  coaugmented complex (the form in which the truncation/homotopy argument is carried out);
* `Work.DSAMR.IsAlmostAcyclic` — the same conditions stated for a bare complex (no coaugmentation):
  every "`I`-cocycle" is an "`I`-coboundary" after multiplying by `ϖ k`;
* `Work.DSAMR.pow_tower` — the arithmetic of the `ϖ`-tower.

## The proof (M3-free, homological)

The heart is `Work.DSAMR.exists_coaug_lift` (`Submission/Work/DSAMR/exists_coaug_lift.lean`): since
`P` is a bounded-above complex of free modules it is `K`-projective, and a chain map into an almost
acyclic complex is almost null-homotopic, with a loss `ϖ j ^ L` where `L` is bounded by the number of
degrees of `P` (and the quantifier order is `∃ L, ∀ j, ∃ h` — the loss is uniform in the level `j`).
The degree-zero component `h⁰ : P⁰ → W` of the homotopy satisfies, for `x` with `P.d 0 1 x = 0`,

`ϖ j ^ L • ρ⁰ x - e (h⁰ x) ∈ I • ⊤`.

Then `t x := mk (ϖ j * h⁰ x)` is an `A`-linear map `P⁰ → W ⧸ I` with `t ∘ d⁻¹ = 0` (the relation
at `x = d⁻¹ y` gives `e (h⁰ (d⁻¹ y)) ∈ I • ⊤`, and the "almost injectivity" condition of `e`
gives `ϖ j * h⁰ (d⁻¹ y) ∈ I`) and `t (ε 1) = mk (ϖ j ^ (L+1))` (the relation at `x = ε 1` gives
`e (ϖ j ^ L - h⁰ (ε 1)) ∈ I • ⊤`).  Hence `ModSplitA P ε ψ I (ϖ j ^ (L+1))` for **every** `j`; the
tower hypothesis `ϖ (m+t) ^ p ^ t = ϖ m` then recovers every prescribed value `ϖ k` by choosing
`j = k + t` with `p ^ t ≥ L + 1` and scaling the value by `ϖ j ^ (p ^ t - (L+1))`
(AM1, `Work.DSAM3.modSplitA_mul`).  There is **no fixed loss**.
-/

open CategoryTheory Limits

namespace Work.DSAMR

universe a

/-! ## The almost-acyclicity vocabulary -/

/-- The three conditions of the frozen `DSMap.Mix2.AlmostAcyc`, for a `ℤ`-indexed coaugmented
complex of `W`-modules.  (`AlmostAcyc` is stated for a `ℕ`-indexed complex, which is what `M5c`
produces; the homotopy argument is carried out on the `ℤ`-indexed extension / cone.) -/
def AlmostAcycZ {W : Type a} [CommRing W] (ϖ : ℕ → W) (I : Ideal W)
    (K : CochainComplex (ModuleCat.{a} W) ℤ) (e : ModuleCat.of W W ⟶ K.X 0) : Prop :=
  (∀ w : W, e.hom w ∈ I • (⊤ : Submodule W (K.X 0)) → ∀ k, ϖ k * w ∈ I) ∧
  (∀ z : K.X 0, (K.d 0 1).hom z ∈ I • (⊤ : Submodule W (K.X 1)) →
      ∀ k, ∃ w : W, ϖ k • z - e.hom w ∈ I • (⊤ : Submodule W (K.X 0))) ∧
  (∀ (q : ℕ) (z : K.X ((q : ℤ) + 1)),
      (K.d ((q : ℤ) + 1) ((q : ℤ) + 2)).hom z ∈
        I • (⊤ : Submodule W (K.X ((q : ℤ) + 2))) →
      ∀ k, ∃ y : K.X (q : ℤ),
        ϖ k • z - (K.d (q : ℤ) ((q : ℤ) + 1)).hom y ∈
          I • (⊤ : Submodule W (K.X ((q : ℤ) + 1))))

/-- `K` is `I`-almost acyclic with values `ϖ k`: every element whose differential lands in
`I · K^{q+1}` is an `I · K^q`-coboundary after multiplying by `ϖ k`. -/
def IsAlmostAcyclic {W : Type a} [CommRing W] (ϖ : ℕ → W) (I : Ideal W)
    (K : CochainComplex (ModuleCat.{a} W) ℤ) : Prop :=
  ∀ (q : ℤ) (z : K.X q), (K.d q (q + 1)).hom z ∈ I • (⊤ : Submodule W (K.X (q + 1))) →
    ∀ k, ∃ y : K.X (q - 1), ϖ k • z - (K.d (q - 1) q).hom y ∈ I • (⊤ : Submodule W (K.X q))

/-! ## The `ϖ`-tower arithmetic -/

/-- The iterated form of `ϖ (k+1) ^ p = ϖ k`: `ϖ (k+t) ^ p^t = ϖ k`. -/
theorem pow_tower {W : Type a} [CommRing W] (ϖ : ℕ → W) (p : ℕ)
    (hϖ : ∀ k, ϖ (k + 1) ^ p = ϖ k) : ∀ k t : ℕ, ϖ (k + t) ^ p ^ t = ϖ k := by
  intro k t
  induction t with
  | zero => simp
  | succ t ih =>
    rw [Nat.add_succ, pow_succ, mul_comm (p ^ t) p, pow_mul, hϖ (k + t), ih]

end Work.DSAMR
