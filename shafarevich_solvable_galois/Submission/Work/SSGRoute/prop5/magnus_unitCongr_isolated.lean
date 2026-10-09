import Mathlib
import Submission.Work.SSGRoute.prop5.magnusFramework
import Submission.Work.SSGRoute.prop5.magnus_mem_one_add
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Isolation of the congruence filtration at the Magnus image

Let `R = FreeAssoc X ⧸ fil X N` be the truncated free associative algebra and let
`filq X N k ⊆ R` be the image of the `k`-th filtration ideal `fil X k`.  The main result of this
file is that the congruence filtration `1 + filq X N ·` is *isolated*: if the `m`-th power of the
Magnus image of `y ∈ γ_n` is `≡ 1` modulo `filq X N (n+2)` then so is the Magnus image itself.

The proof has two ingredients.

* `(1 + x)^m ≡ 1 + m x (mod filq (2(n+1)))` whenever `x ∈ filq (n+1)`:  modulo the ideal
  `filq X N (n+2)` the element `x` has square zero, and in any ring `(1+y)^m = 1 + m y` as soon as
  `y * y = 0`.  Hence `m x ∈ filq X N (n+2)`.
* The filtration pieces are torsion free: `filq X N k` is the image of `filz X k`, and `filz X k`
  is the `ℤ`-submodule of `FreeAssoc X` supported on words of length at least `k`; multiplying by a
  nonzero integer does not change the support.  As `n + 2 ≤ N`, this yields `x ∈ filq X N (n+2)`.
-/

noncomputable section

open scoped commutatorElement

namespace Work.SSGRoute.prop5

variable {X : Type*}

/-- The filtration pieces of the quotient are two-sided ideals. -/
instance filq_isTwoSided (X : Type*) (N k : ℕ) : (filq X N k).IsTwoSided :=
  Ideal.IsTwoSided.mk fun b ha => mul_mem_filq_right X N k ha b

/-! ## The support description of `filz` -/

/-- An element of `FreeAssoc X` lies in `filz X N` exactly when every word occurring in its
support has length at least `N`. -/
theorem mem_filz_iff {N : ℕ} {a : FreeAssoc X} :
    a ∈ filz X N ↔ ∀ w : FreeMonoid X, a.coeff w ≠ 0 → N ≤ w.length := by
  let T : Submodule ℤ (FreeAssoc X) :=
    { carrier := {a | ∀ w : FreeMonoid X, a.coeff w ≠ 0 → N ≤ w.length}
      zero_mem' := by
        intro w hw
        rw [MonoidAlgebra.coeff_zero, Finsupp.zero_apply] at hw
        exact absurd rfl hw
      add_mem' := by
        intro a b ha hb w hw
        rw [MonoidAlgebra.coeff_add, Finsupp.add_apply] at hw
        rcases eq_or_ne (a.coeff w) 0 with h | h
        · rw [h, zero_add] at hw; exact hb w hw
        · exact ha w h
      smul_mem' := by
        intro c a ha w hw
        rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply] at hw
        exact ha w (fun h0 => hw (by rw [h0, smul_zero])) }
  have hfilz : filz X N ≤ T := by
    rw [filz]
    refine Submodule.span_le.mpr ?_
    rintro b ⟨w, hw, rfl⟩
    intro v hv
    rw [MonoidAlgebra.coeff_single] at hv
    have hvw : v = w := by
      by_contra hne
      exact hv (Finsupp.single_eq_of_ne hne)
    subst hvw
    exact hw
  constructor
  · intro ha; exact hfilz ha
  · intro ha
    rw [← MonoidAlgebra.sum_coeff_single a]
    rw [Finsupp.sum]
    refine Submodule.sum_mem _ fun w hw => ?_
    exact single_mem_filz (ha w (Finsupp.mem_support_iff.mp hw)) (a.coeff w)

/-- The filtration pieces `filz X N` are torsion free: `m • x ∈ filz X N` with `m > 0` forces
`x ∈ filz X N`. -/
theorem filz_nsmul_mem {N m : ℕ} (hm : 0 < m) {x : FreeAssoc X}
    (h : m • x ∈ filz X N) : x ∈ filz X N := by
  rw [mem_filz_iff] at h ⊢
  intro w hw
  exact h w (by
    have : (m • x).coeff w = (m : ℤ) * x.coeff w := by
      rw [← Nat.cast_smul_eq_nsmul ℤ m x, MonoidAlgebra.coeff_smul, Finsupp.smul_apply,
        smul_eq_mul]
    rw [this]
    exact mul_ne_zero (by exact_mod_cast Nat.pos_iff_ne_zero.mp hm) hw)

/-! ## Torsion freeness of the filtration pieces of the quotient -/

/-- Membership in `filq X N k` is membership in `filz X k` modulo `fil X N`. -/
theorem mem_filq_iff {N k : ℕ} {x : FreeAssoc X ⧸ fil X N} :
    x ∈ filq X N k ↔ ∃ x' ∈ filz X k, Ideal.Quotient.mk (fil X N) x' = x := by
  rw [filq, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
  constructor
  · rintro ⟨x', hx', rfl⟩
    exact ⟨x', by rwa [fil_eq_filI] at hx', rfl⟩
  · rintro ⟨x', hx', rfl⟩
    exact ⟨x', by rwa [fil_eq_filI], rfl⟩

/-- The quotients `filq X N k` are torsion free, provided `k ≤ N`. -/
theorem filq_nsmul_mem {N k m : ℕ} (hkN : k ≤ N) (hm : 0 < m)
    {x : FreeAssoc X ⧸ fil X N} (h : m • x ∈ filq X N k) : x ∈ filq X N k := by
  obtain ⟨x', rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [mem_filq_iff] at h ⊢
  obtain ⟨w, hw, hw'⟩ := h
  have hdiff : m • x' - w ∈ filz X k := by
    have hker : m • x' - w ∈ fil X N := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_nsmul, hw', sub_self]
    have h2 : m • x' - w ∈ fil X k := fil_antitone X hkN hker
    rw [fil_eq_filI] at h2
    exact h2
  have hmx' : m • x' ∈ filz X k := by
    have h := Submodule.add_mem _ hw hdiff
    rwa [add_sub_cancel] at h
  exact ⟨x', filz_nsmul_mem hm hmx', rfl⟩

/-! ## The binomial expansion modulo the square of the ideal -/

/-- In a (not necessarily commutative) ring, `(1 + y)^m = 1 + m • y` as soon as `y * y = 0`. -/
theorem one_add_pow_eq_of_sq_zero {A : Type*} [Ring A] (y : A) (hy : y * y = 0) (m : ℕ) :
    (1 + y) ^ m = 1 + m • y := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, nsmul_eq_mul, nsmul_eq_mul, Nat.cast_succ]
    have key : (1 + (↑m : A) * y) * (1 + y)
        = 1 + (↑m : A) * y + y + (↑m : A) * (y * y) := by noncomm_ring
    rw [key, hy, mul_zero, add_zero]
    noncomm_ring

/-- The key step: if `x ≡ 0 mod filq (n+1)` and `(1 + x)^m ≡ 1 mod filq (n+2)` for some `m > 0`,
then `x ≡ 0 mod filq (n+2)`. -/
theorem mem_filq_of_one_add_pow {N n m : ℕ} (hm : 0 < m) (hkN : n + 2 ≤ N)
    {x : FreeAssoc X ⧸ fil X N} (hx : x ∈ filq X N (n + 1))
    (h : (1 + x) ^ m - 1 ∈ filq X N (n + 2)) : x ∈ filq X N (n + 2) := by
  -- `x` has square zero modulo `filq X N (n+2)`.
  have hx2 : x * x ∈ filq X N (n + 2) :=
    filq_antitone X N (by omega) (mul_mem_filq X N (n + 1) (n + 1) hx hx)
  have hmx : m • x ∈ filq X N (n + 2) := by
    -- reduce to the quotient of `R` by `filq X N (n+2)`
    have hq : Ideal.Quotient.mk (filq X N (n + 2)) ((1 + x) ^ m)
        = Ideal.Quotient.mk (filq X N (n + 2)) 1 := by
      rw [← sub_eq_zero, ← map_sub, Ideal.Quotient.eq_zero_iff_mem]
      exact h
    have hπx2 : (Ideal.Quotient.mk (filq X N (n + 2)) x) *
        (Ideal.Quotient.mk (filq X N (n + 2)) x) = 0 := by
      rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact hx2
    have hpow : (Ideal.Quotient.mk (filq X N (n + 2)) (1 + x)) ^ m = 1 := by
      rw [← map_pow, hq, map_one]
    have h1x : Ideal.Quotient.mk (filq X N (n + 2)) (1 + x)
        = 1 + Ideal.Quotient.mk (filq X N (n + 2)) x := by
      rw [map_add, map_one]
    have hmul : m • (Ideal.Quotient.mk (filq X N (n + 2)) x) = 0 := by
      have h2 := one_add_pow_eq_of_sq_zero (Ideal.Quotient.mk (filq X N (n + 2)) x) hπx2 m
      rw [h1x] at hpow
      exact add_left_cancel ((h2.symm.trans hpow).trans (add_zero 1).symm)
    have hπ0 : Ideal.Quotient.mk (filq X N (n + 2)) (m • x) = 0 := by
      rw [map_nsmul, hmul]
    rwa [Ideal.Quotient.eq_zero_iff_mem] at hπ0
  -- torsion freeness of the filtration piece
  exact filq_nsmul_mem hkN hm hmx

/-! ## The isolation theorem -/

theorem magnus_unitCongr_isolated (X : Type*) (N n m : ℕ) (hn : n + 2 ≤ N) (hm : 0 < m)
    (y : FreeGroup X) (hy : y ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries n)
    (h : (((magnus X N y) ^ m : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1 ∈
      filq X N (n + 2)) :
    ((magnus X N y : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1 ∈
      filq X N (n + 2) := by
  have hle : n + 1 ≤ N := by omega
  have hx1 : ((magnus X N y : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1
      ∈ filq X N (n + 1) := magnus_mem_one_add X N n hle y hy
  have hh : (1 + (((magnus X N y : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1)) ^ m
      - 1 ∈ filq X N (n + 2) := by
    have h1 : (1 + (((magnus X N y : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) - 1))
        = ((magnus X N y : (FreeAssoc X ⧸ fil X N)ˣ) : FreeAssoc X ⧸ fil X N) := by abel
    rw [h1, ← Units.val_pow_eq_pow_val]
    exact h
  exact mem_filq_of_one_add_pow hm hn hx1 hh

end Work.SSGRoute.prop5
