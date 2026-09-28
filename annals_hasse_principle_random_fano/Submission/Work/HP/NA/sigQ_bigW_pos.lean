import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.NA.Setup
import Submission.Work.HP.NA.isPrimGen_prodEquivPi_iff

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `σ(a; W) > 0` for the non-Archimedean modulus `W = bigW w`

For a degree-`d` form `f_a` in `n+1` variables with integer coefficients, the
non-Archimedean density is

  `σ(a; Q) = Q^{-n} · #{b ∈ (ZMod Q)^{n+1} : b generates the unit ideal, f_a(b) = 0}`

(`Work.HP.NA.sigQ`).  The challenge hypothesis is that for every prime `p ≤ w`
the form `f_a` has a primitive zero modulo `p^{r_p(w)}`, where `r_p(w) = ⌈log_p w⌉+1`
(`Work.HP.PrimModZero`, `Work.HP.rOf`).  We show that then `σ(a; W) > 0` for
`W = ∏_{p ≤ w} p^{r_p(w)}` (`Work.HP.bigW`).

The proof is the Chinese remainder theorem.  Writing `W = ∏ᵢ Qᵢ` with
`Qᵢ = pᵢ^{r_{pᵢ}}` (pairwise coprime prime powers), `ZMod W ≃+* ∏ᵢ ZMod Qᵢ`.
Gluing the local primitive zeroes `xᵢ` of `f_a` mod `Qᵢ` along this equivalence
produces a primitive zero `b` of `f_a` mod `W` (`crt_glue_primGen`); since `σ`
counts at least this one vector, it is positive.

The `ZMod`-facing ingredients are kept here as private helper lemmas: naturality
of `fev` under ring homomorphisms and ring equivalences, its compatibility with
`π`-types, and the translation of `PrimModZero` into a primitive zero
(`IsPrimGen _ x ∧ fev _ _ x = 0`) modulo a prime power.
-/

open Finset

set_option linter.style.haveILetI false

namespace Work.HP.NA

/-- `fev` is natural in the coefficient ring: pushing coefficients and the point
through a ring homomorphism `φ` pushes `fev` through `φ`. -/
private theorem fev_map_natural {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S) (d n : ℕ)
    (a : Work.HP.Mon d n → R) (x : Fin (n + 1) → R) :
    fev d n (fun m => φ (a m)) (fun j => φ (x j)) = φ (fev d n a x) := by
  unfold fev
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m _
  rw [map_mul]
  congr 1
  unfold Work.HP.veronese
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [map_pow]

/-- The ring-equivalence form of `fev_map_natural`. -/
private theorem fev_map_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (φ : R ≃+* S) (d n : ℕ)
    (a : Work.HP.Mon d n → R) (x : Fin (n + 1) → R) :
    fev d n (fun m => φ (a m)) (fun j => φ (x j)) = φ (fev d n a x) :=
  fev_map_natural (φ : R →+* S) d n a x

/-- `fev` over a product ring, evaluated at a component `πᵢ`, is `fev` of the
components. -/
private theorem fev_apply_pi {ι : Type*} [Fintype ι] {R : ι → Type*} [∀ i, CommRing (R i)]
    (d n : ℕ) (c : Work.HP.Mon d n → (∀ i, R i)) (y : Fin (n + 1) → (∀ i, R i)) (i : ι) :
    fev d n c y i = fev d n (fun m => c m i) (fun j => y j i) := by
  simp only [fev, Work.HP.veronese, Finset.sum_apply, Finset.prod_apply,
    Pi.mul_apply, Pi.pow_apply]

/-- **CRT gluing.**  Assume `ZMod (∏ᵢ Qᵢ) ≃+* ∏ᵢ ZMod Qᵢ` (i.e. the moduli `Qᵢ`
are pairwise coprime), and suppose that for every `i` the form `f_a` has a zero
modulo `Qᵢ` whose coordinates generate the unit ideal.  Then `f_a` has a zero
modulo `∏ᵢ Qᵢ` whose coordinates generate the unit ideal. -/
private theorem crt_glue_primGen (d n : ℕ) {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : ι → ℕ)
    (hQ : Pairwise (Function.onFun Nat.Coprime Q)) (a : Work.HP.Mon d n → ℤ)
    (h : ∀ i, ∃ x : Fin (n + 1) → ZMod (Q i),
        IsPrimGen (Q i) x ∧ fev d n (fun m => (a m : ZMod (Q i))) x = 0) :
    ∃ b : Fin (n + 1) → ZMod (∏ i, Q i),
      IsPrimGen (∏ i, Q i) b ∧ fev d n (fun m => (a m : ZMod (∏ i, Q i))) b = 0 := by
  classical
  choose x hx using h
  let b : Fin (n + 1) → ZMod (∏ i, Q i) :=
    fun j => (ZMod.prodEquivPi Q hQ).symm (fun i => x i j)
  have hbe : ∀ j, ZMod.prodEquivPi Q hQ (b j) = fun i => x i j := by
    intro j; exact RingEquiv.apply_symm_apply _ _
  refine ⟨b, ?_, ?_⟩
  · rw [isPrimGen_prodEquivPi_iff Q hQ b]
    intro i
    have h1 : (fun j => ZMod.prodEquivPi Q hQ (b j) i) = x i := by
      funext j; rw [hbe j]
    rw [h1]
    exact (hx i).1
  · refine (ZMod.prodEquivPi Q hQ).injective ?_
    rw [map_zero, ← fev_map_ringEquiv (ZMod.prodEquivPi Q hQ) d n
        (fun m => (a m : ZMod (∏ i, Q i))) b]
    funext i
    rw [fev_apply_pi]
    have hc : (fun m => ZMod.prodEquivPi Q hQ ((a m : ZMod (∏ i, Q i))) i)
        = (fun m => (a m : ZMod (Q i))) := by
      funext m
      rw [ZMod.prodEquivPi_apply]
      simp
    have hx' : (fun j => ZMod.prodEquivPi Q hQ (b j) i) = x i := by
      funext j; rw [hbe j]
    rw [hc, hx']
    exact (hx i).2

/-- With integer coefficients, `fev d n a x` in `ZMod Q` is the reduction of the
[`formEval`](Work.HP.formEval) of the corresponding integer vectors. -/
private theorem fev_cast_formEval (d n Q : ℕ) (a : Work.HP.Mon d n → ℤ) (x : Fin (n + 1) → ℤ) :
    fev d n (fun m => (a m : ZMod Q)) (fun j => (x j : ZMod Q))
      = ((Work.HP.formEval d n a x : ℤ) : ZMod Q) := by
  simp only [fev, Work.HP.formEval, Work.HP.veronese]
  push_cast
  rfl

/-- In `ZMod (p ^ r)` (`r ≥ 1`, `p` prime) an integer is a unit iff `p` does not
divide it. -/
private theorem isUnit_intCast_zmod_prime_pow (p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r) (z : ℤ) :
    IsUnit ((z : ℤ) : ZMod (p ^ r)) ↔ ¬ (p : ℤ) ∣ z := by
  have h1 : IsUnit ((z : ℤ) : ZMod (p ^ r)) ↔ IsUnit ((z.natAbs : ℕ) : ZMod (p ^ r)) := by
    rcases Int.natAbs_eq z with h | h
    · rw [h, Int.cast_natCast, Int.natAbs_natCast]
    · rw [h]
      simp only [Int.cast_neg, Int.cast_natCast, Int.natAbs_neg]
      exact IsUnit.neg_iff _
  rw [h1, ZMod.isUnit_natCast_iff_not_dvd_pow hp (by omega)]
  constructor
  · intro h hd
    exact h ((Int.natAbs_dvd_natAbs).mpr hd)
  · intro h hd
    exact h ((Int.natAbs_dvd_natAbs).mp hd)

/-- A vector is primitive as soon as one of its coordinates is a unit. -/
private theorem isPrimGen_of_isUnit_coord {ι : Type*} [Fintype ι] {q : ℕ} (v : ι → ZMod q)
    (i : ι) (h : IsUnit (v i)) : IsPrimGen q v := by
  rw [IsPrimGen]
  apply top_le_iff.mp
  calc ⊤ = Ideal.span ({v i} : Set (ZMod q)) := (Ideal.span_singleton_eq_top.mpr h).symm
    _ ≤ Ideal.span (Set.range v) :=
        Ideal.span_le.mpr (by rintro x rfl; exact Ideal.subset_span (Set.mem_range_self i))

/-- A primitive zero of `f_a` modulo `p^r` in the sense of `PrimModZero` yields a
vector over `ZMod (p^r)` that is primitive and at which `fev` vanishes. -/
private theorem primModZero_to_local (d n p r : ℕ) (hp : p.Prime) (hr : 1 ≤ r)
    (a : Work.HP.Mon d n → ℤ) (h : Work.HP.PrimModZero d n a p r) :
    ∃ x : Fin (n + 1) → ZMod (p ^ r),
      IsPrimGen (p ^ r) x ∧ fev d n (fun m => (a m : ZMod (p ^ r))) x = 0 := by
  obtain ⟨y, ⟨j, hj⟩, hdvd⟩ := h
  refine ⟨fun i => (y i : ZMod (p ^ r)), ?_, ?_⟩
  · exact isPrimGen_of_isUnit_coord _ j
      ((isUnit_intCast_zmod_prime_pow p r hp hr (y j)).mpr hj)
  · rw [fev_cast_formEval]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr (by push_cast; exact hdvd)

/-- `σ(a; Q) > 0` as soon as `f_a` has *one* primitive zero modulo `Q`. -/
private theorem sigQ_pos_of_primGen (d n Q : ℕ) (hQ : 1 ≤ Q) (a : Work.HP.Mon d n → ZMod Q)
    (h : ∃ b : Fin (n + 1) → ZMod Q, IsPrimGen Q b ∧ fev d n a b = 0) :
    0 < sigQ d n Q a := by
  have hQpos : 0 < Q := lt_of_lt_of_le Nat.zero_lt_one hQ
  haveI : NeZero Q := ⟨hQpos.ne'⟩
  obtain ⟨b, hb1, hb2⟩ := h
  have hne : ({b : Fin (n + 1) → ZMod Q | Ideal.span (Set.range b) = ⊤ ∧ fev d n a b = 0}
      : Set (Fin (n + 1) → ZMod Q)).Nonempty := ⟨b, hb1, hb2⟩
  have hpos : 0 < ({b : Fin (n + 1) → ZMod Q | Ideal.span (Set.range b) = ⊤ ∧
      fev d n a b = 0} : Set (Fin (n + 1) → ZMod Q)).ncard :=
    (Set.ncard_pos (s := _)).mpr hne
  rw [sigQ]
  apply div_pos
  · exact_mod_cast hpos
  · have : (0:ℝ) < (Q:ℝ) := by exact_mod_cast hQpos
    positivity

theorem sigQ_bigW_pos (d n : ℕ) (w : ℝ) (a : Work.HP.Mon d n → ℤ)
    (ha : ∀ p : ℕ, p.Prime → (p:ℝ) ≤ w → Work.HP.PrimModZero d n a p (Work.HP.rOf p w)) :
    0 < Work.HP.NA.sigQ d n (Work.HP.bigW w) (fun m => (a m : ZMod (Work.HP.bigW w))) := by
  classical
  -- Unfold `bigW` as a product indexed by the *subtype* of primes `p ≤ w`.
  have hW : Work.HP.bigW w =
      ∏ i : ↥((Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime), i.1 ^ Work.HP.rOf i.1 w := by
    rw [Work.HP.bigW]
    exact (Finset.prod_attach _ _).symm
  rw [hW]
  refine sigQ_pos_of_primGen d n
    (∏ i : ↥((Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime), i.1 ^ Work.HP.rOf i.1 w) ?_ _ ?_
  · -- `W ≥ 1`.
    exact Finset.one_le_prod₀ (fun i _ =>
      Nat.one_le_pow _ i.1 (Nat.Prime.pos (Finset.mem_filter.mp i.2).2))
  · -- Glue the local primitive zeroes at each prime for which `p ≤ w`.
    refine crt_glue_primGen d n (fun i : ↥((Finset.range (⌊w⌋₊ + 1)).filter Nat.Prime) =>
        i.1 ^ Work.HP.rOf i.1 w) ?_ a ?_
    · -- distinct primes give coprime prime powers
      intro i j hij
      have hpi : Nat.Prime i.1 := (Finset.mem_filter.mp i.2).2
      have hpj : Nat.Prime j.1 := (Finset.mem_filter.mp j.2).2
      have hne : i.1 ≠ j.1 := fun h => hij (Subtype.ext h)
      have hcop : Nat.Coprime i.1 j.1 := (hpi.coprime_iff_not_dvd).mpr (fun hd => by
        rcases (Nat.dvd_prime hpj).mp hd with h1 | h2
        · exact hpi.ne_one h1
        · exact hne h2)
      exact hcop.pow _ _
    · intro i
      have hpi : Nat.Prime i.1 := (Finset.mem_filter.mp i.2).2
      have hi : i.1 ≤ ⌊w⌋₊ :=
        Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_filter.mp i.2).1)
      have hle : (i.1 : ℝ) ≤ w := (Nat.le_floor_iff' hpi.ne_zero).mp hi
      exact primModZero_to_local d n i.1 (Work.HP.rOf i.1 w) hpi
        (by unfold Work.HP.rOf; exact Nat.le_add_left 1 _) a
        (ha i.1 hpi hle)

end Work.HP.NA
