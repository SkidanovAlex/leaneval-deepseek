import Mathlib
import Submission.Work.DSM2p.ConstructionPos
import Submission.Work.DSM2p.adicCompletion_ker_eval_one
import Submission.Work.DSM2p.CSIntegralClosurePos_isSMulRegular

/-!
# Frobenius surjectivity passes from `A'` to its `p`-adic completion `B`

Let `p` be prime, `A` a commutative ring with perfectoid data `P`, write `ϖ := P.ϖ 0`,
`A' := CSIntegralClosurePos A p ϖ` (the `p`-integral closure of the Česnavičius–Scholze ring
`A_∞`) and `B := CSCompletionPos A p ϖ = AdicCompletion (p) A'` (its `p`-adic completion).

This file proves that whenever every element of `A'` admits a `p`-th root modulo `(ϖ ^ p)` — the
condition `(H1)` of `DESIGN.md`, i.e. Frobenius surjectivity on the level-one reduction
`A' ⧸ pA'` — then the same holds for `B`:

* `frobSurj_completion` — the requested transfer `(H1)` from `A'` to `B`.

The argument has nothing to do with the specific ČS construction, so it is first isolated as

* `adicCompletion_frobSurj_of`: for *any* commutative ring `R` in which the Frobenius `x ↦ x ^ p`
  is surjective modulo `(p)`, the same is true of the `p`-adic completion
  `AdicCompletion (p) R` modulo `(p)`.

Indeed `B ⧸ pB ≅ R ⧸ pR` via `AdicCompletion.evalOneₐ`, whose kernel is `pB`
(`AdicCompletion.ker_evalOneₐ_eq_map`, requiring only `(p).FG`): given `x : B`, lift its class in
`R ⧸ pR` to `a : R`, find `b : R` with `a ≡ b ^ p (mod p)`, and take `y` to be the image of `b`
in `B`. Then `x - y ^ p` maps to `0` in `B ⧸ pB`, i.e. lies in `pB`.

The specialisation to the ČS construction only has to translate the ideal `(ϖ ^ p)` (generated
above by `algebraMap A ·`) into `(p)`, using `ϖ ^ p = p · v` with `v` a unit of `A` (`P.unit`).
-/

open scoped Classical

namespace Work.DSM2p

/-- **Frobenius surjectivity survives `p`-adic completion.**  If every element of `R` is a
`p`-th power modulo `(p)`, then every element of the `p`-adic completion `AdicCompletion (p) R`
is a `p`-th power modulo `(p)`.

The proof only uses that the level-one reduction `AdicCompletion (p) R → R ⧸ (p)` is surjective
with kernel `(p) · AdicCompletion (p) R` (`AdicCompletion.ker_evalOneₐ_eq_map`). -/
theorem adicCompletion_frobSurj_of (R : Type*) [CommRing R] (p : ℕ)
    (h : ∀ x : R, ∃ y : R, x - y ^ p ∈ Ideal.span {(p : R)}) :
    ∀ x : AdicCompletion (Ideal.span {(p : R)}) R, ∃ y : AdicCompletion (Ideal.span {(p : R)}) R,
      x - y ^ p ∈ Ideal.span {(p : AdicCompletion (Ideal.span {(p : R)}) R)} := by
  intro x
  -- the level-one reduction `B → R ⧸ (p)` has kernel `(p)B`
  have hker : RingHom.ker (AdicCompletion.evalOneₐ (Ideal.span {(p : R)})).toRingHom
      = Ideal.span {(p : AdicCompletion (Ideal.span {(p : R)}) R)} := by
    rw [AdicCompletion.ker_evalOneₐ_eq_map (Ideal.span {(p : R)})
      (Submodule.fg_span_singleton (p : R))]
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  -- lift the class of `x` modulo `(p)` to an element `a` of `R`
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (I := Ideal.span {(p : R)})
      ((AdicCompletion.evalOneₐ (Ideal.span {(p : R)})) x)
  -- and take a `p`-th root `b` of `a` modulo `(p)`
  obtain ⟨b, hb⟩ := h a
  have hmk : Ideal.Quotient.mk (Ideal.span {(p : R)}) a
      = (Ideal.Quotient.mk (Ideal.span {(p : R)}) b) ^ p := by
    have hz : Ideal.Quotient.mk (Ideal.span {(p : R)}) (a - b ^ p) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr hb
    rw [map_sub, map_pow] at hz
    exact sub_eq_zero.mp hz
  refine ⟨(AdicCompletion.of (Ideal.span {(p : R)}) R b :
      AdicCompletion (Ideal.span {(p : R)}) R), ?_⟩
  rw [← hker, RingHom.mem_ker]
  change (AdicCompletion.evalOneₐ (Ideal.span {(p : R)}))
      (x - (AdicCompletion.of (Ideal.span {(p : R)}) R b) ^ p) = 0
  rw [map_sub, map_pow, AdicCompletion.evalOneₐ_of, ← ha, hmk, sub_self]

-- The types `CSIntegralClosurePos A p ϖ` and `CSCompletionPos A p ϖ` are built from a fair amount
-- of structure (`pIntClosure` of a `Subring.closure` inside a localisation), so the default
-- heartbeat budget is not enough to carry out the (few) coercions below.
set_option maxHeartbeats 1600000 in
theorem frobSurj_completion (p : ℕ) [Fact p.Prime] (A : Type*) [CommRing A]
    (P : DSMap.PerfectoidData p A)
    (h : ∀ x : CSIntegralClosurePos A p (P.ϖ 0), ∃ y : CSIntegralClosurePos A p (P.ϖ 0),
      x - y ^ p ∈ Ideal.span {algebraMap A (CSIntegralClosurePos A p (P.ϖ 0)) (P.ϖ 0 ^ p)}) :
    ∀ x : CSCompletionPos A p (P.ϖ 0), ∃ y : CSCompletionPos A p (P.ϖ 0),
      x - y ^ p ∈ Ideal.span {algebraMap A (CSCompletionPos A p (P.ϖ 0)) (P.ϖ 0 ^ p)} := by
  -- `(ϖ ^ p) = (p)` in `A'`
  have hspanA : Ideal.span {algebraMap A (CSIntegralClosurePos A p (P.ϖ 0)) (P.ϖ 0 ^ p)}
      = Ideal.span {(p : CSIntegralClosurePos A p (P.ϖ 0))} := by
    obtain ⟨v, hv⟩ := P.unit
    have hkey : algebraMap A (CSIntegralClosurePos A p (P.ϖ 0)) (P.ϖ 0 ^ p)
        = (p : CSIntegralClosurePos A p (P.ϖ 0)) *
          algebraMap A (CSIntegralClosurePos A p (P.ϖ 0)) (↑v : A) := by
      rw [hv, map_mul, map_natCast]
    rw [hkey, Ideal.span_singleton_mul_right_unit (IsUnit.map _ v.isUnit)]
  -- `(ϖ ^ p) = (p)` in `B`
  have hspanB : Ideal.span {algebraMap A (CSCompletionPos A p (P.ϖ 0)) (P.ϖ 0 ^ p)}
      = Ideal.span {(p : CSCompletionPos A p (P.ϖ 0))} := by
    obtain ⟨v, hv⟩ := P.unit
    have hkey : algebraMap A (CSCompletionPos A p (P.ϖ 0)) (P.ϖ 0 ^ p)
        = (p : CSCompletionPos A p (P.ϖ 0)) *
          algebraMap A (CSCompletionPos A p (P.ϖ 0)) (↑v : A) := by
      rw [hv, map_mul, map_natCast]
    rw [hkey, Ideal.span_singleton_mul_right_unit (IsUnit.map _ v.isUnit)]
  -- `(H1)` restated with `(p)` in place of `(ϖ ^ p)`
  have h' : ∀ x : CSIntegralClosurePos A p (P.ϖ 0),
      ∃ y : CSIntegralClosurePos A p (P.ϖ 0),
      x - y ^ p ∈ Ideal.span {(p : CSIntegralClosurePos A p (P.ϖ 0))} := by
    intro x
    obtain ⟨y, hy⟩ := h x
    exact ⟨y, by rw [← hspanA]; exact hy⟩
  intro x
  obtain ⟨y, hy⟩ := adicCompletion_frobSurj_of (CSIntegralClosurePos A p (P.ϖ 0)) p h' x
  exact ⟨y, by rw [hspanB]; exact hy⟩

end Work.DSM2p
