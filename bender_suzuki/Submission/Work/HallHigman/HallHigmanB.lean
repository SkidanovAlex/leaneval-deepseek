/-
Area A10 of the Feit--Thompson (odd order theorem) drive:
the statements of Hall--Higman Theorem B in the forms used by Feit--Thompson §7, together with the
consequences that can be proved without the hard part of the theorem.

The mathematical design of the proof of the order-`p` form `HallHigmanB1` is in
`Submission/Work/NOTES_LEAD_ft_hallhigman.md` (GL-core: `Work.HallHigman.GLCore.*`).

Nothing in this file is an axiom: `HallHigmanB`, `HallHigmanBsolv`, `HallHigmanB1` and
`HallHigmanBvector` are plain `Prop`s, and everything else is proved from them.
-/
import Mathlib
import Submission.Work.HallHigman.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

universe u v

namespace Work.HallHigman

open Polynomial

set_option linter.unusedVariables false

/-- **Hall--Higman Theorem B**, odd order form, for `p`-solvable groups:  if `G` is a
`p`-solvable group of odd order with `O_p(G) = 1`, and `V` is a faithful finite dimensional
`K[G]`-module with `K` of characteristic `p`, then every element `x ∈ G` of order `p ^ n` has
minimal polynomial `(X - 1) ^ (p ^ n)` on `V`. -/
def HallHigmanB (K : Type u) [Field K] (p : ℕ) [CharP K p] : Prop :=
  ∀ (G : Type v) [Group G] [Finite G], IsPSolvable p G → Odd (Nat.card G) →
    ∀ (V : FDRep K G), Function.Injective V.ρ → pCore p G = ⊥ → ∀ (x : G) (n : ℕ),
      orderOf x = p ^ n → minpoly K (V.ρ x) = (X - 1) ^ (p ^ n)

/-- **Hall--Higman Theorem B**, odd order form, for solvable groups -- the form requested for
area A10 of the drive. -/
def HallHigmanBsolv (K : Type u) [Field K] (p : ℕ) [CharP K p] : Prop :=
  ∀ (G : Type v) [Group G] [Finite G], Group.IsSolvable G → Odd (Nat.card G) →
    ∀ (V : FDRep K G), Function.Injective V.ρ → pCore p G = ⊥ → ∀ (x : G) (n : ℕ),
      orderOf x = p ^ n → minpoly K (V.ρ x) = (X - 1) ^ (p ^ n)

/-- **Hall--Higman Theorem B**, order-`p` odd order form -- the form that Feit--Thompson §7
actually consumes (see `Submission/Work/NOTES_LEAD_ft_hallhigman.md` §1):  if `G` is a finite
`p`-solvable group of odd order, `V` a faithful `K[G]`-module with `K` of characteristic `p` and
`O_p(G) = 1`, then every `x ≠ 1` satisfies `(V.ρ x - 1) ^ (p - 1) ≠ 0`.  (For a `p`-element this
says that its minimal polynomial is `(X - 1) ^ p`, i.e. that it has a Jordan block of size `p`.) -/
def HallHigmanB1 (K : Type u) [Field K] (p : ℕ) [CharP K p] : Prop :=
  ∀ (G : Type v) [Group G] [Finite G], IsPSolvable p G → Odd (Nat.card G) →
    ∀ (V : FDRep K G), Function.Injective V.ρ → pCore p G = ⊥ →
      ∀ x : G, x ≠ 1 → (V.ρ x - 1) ^ (p - 1) ≠ 0

/-- **Hall--Higman Theorem B**, odd order form, in "regular vector" shape:  the minimal polynomial
statement is equivalent to the existence, for every `x` of order `p ^ n`, of a vector on which
`(ρ x - 1) ^ (p ^ n - 1)` does not vanish, i.e. of a Jordan block of maximal possible size `p ^ n`
for `ρ x`. -/
def HallHigmanBvector (K : Type u) [Field K] (p : ℕ) [CharP K p] : Prop :=
  ∀ (G : Type v) [Group G] [Finite G], Group.IsSolvable G → Odd (Nat.card G) →
    ∀ (V : FDRep K G), Function.Injective V.ρ → pCore p G = ⊥ → ∀ (x : G) (n : ℕ),
      orderOf x = p ^ n → ∃ w : V, w ≠ 0 ∧ ((V.ρ x - 1) ^ (p ^ n - 1)) w ≠ 0

variable {K : Type u} [Field K] {p : ℕ} [CharP K p]

/-- `ρ x ^ n = ρ (x ^ n)`. -/
lemma FDRep.rho_pow {G : Type v} [Group G] (V : FDRep K G) (x : G) (n : ℕ) :
    V.ρ x ^ n = V.ρ (x ^ n) :=
  (map_pow V.ρ x n).symm

/-- The degree of `(X - 1) ^ k`. -/
lemma natDegree_X_sub_C_one_pow (k : ℕ) : ((X - C (1 : K)) ^ k).natDegree = k := by
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]

/-- The solvable group form of Theorem B follows from the `p`-solvable form once one knows that
finite solvable groups are `p`-solvable (the hypothesis `hred` here; the unconditional statement
`Work.HallHigman.isPSolvable_of_isSolvable` is provided by the area). -/
theorem HallHigmanB.toSolvable (h : HallHigmanB.{u, v} K p)
    (hred : ∀ (G : Type v) [Group G] [Finite G], Group.IsSolvable G → IsPSolvable p G) :
    HallHigmanBsolv.{u, v} K p :=
  fun G _ _ hsol hodd V hf hO x n hx => h G (hred G hsol) hodd V hf hO x n hx

/-- **Hall--Higman Theorem B**, odd order form, with the hypotheses exactly as requested for
area A10: `p ≠ 2`, `G` solvable of odd order, `V` a faithful `K[G]`-module in characteristic `p`,
`O_p(G) = 1`, and `x` of order `p ^ n`. -/
theorem hall_higman_B_odd (hB : HallHigmanBsolv.{u, v} K p) [Fact p.Prime] (hp : p ≠ 2)
    {G : Type v} [Group G] [Finite G] (hsol : Group.IsSolvable G) (hodd : Odd (Nat.card G))
    (V : FDRep K G) (hfaith : Function.Injective V.ρ) (hOp : pCore p G = ⊥) (x : G) (n : ℕ)
    (hx : orderOf x = p ^ n) : minpoly K (V.ρ x) = (X - 1) ^ (p ^ n) :=
  hB G hsol hodd V hfaith hOp x n hx

/-- For `f` an endomorphism with `minpoly K f = (X - 1) ^ q`, some vector is moved by
`(f - 1) ^ (q - 1)`: the corresponding Jordan block has size `q`. -/
theorem exists_ne_zero_apply_of_minpoly_eq_X_sub_one_pow {M : Type*} [AddCommGroup M] [Module K M]
    {f : Module.End K M} {q : ℕ} (hq : 0 < q) (h : minpoly K f = (X - 1) ^ q) :
    ∃ w : M, w ≠ 0 ∧ ((f - 1) ^ (q - 1)) w ≠ 0 := by
  by_contra hcon
  simp only [not_exists, not_and, not_not] at hcon
  have h' : minpoly K f = (X - C (1 : K)) ^ q := h
  have hzero : (f - 1) ^ (q - 1) = 0 := by
    refine LinearMap.ext fun w => ?_
    by_cases hw : w = 0
    · simp [hw]
    · exact hcon w hw
  have hdvd : minpoly K f ∣ (X - C (1 : K)) ^ (q - 1) := by
    refine minpoly.dvd K f ?_
    simpa [map_pow, map_sub, aeval_X, aeval_one] using hzero
  rw [h'] at hdvd
  have hne : ((X - C (1 : K)) ^ (q - 1)) ≠ 0 := pow_ne_zero _ (Polynomial.X_sub_C_ne_zero 1)
  have hle := Polynomial.natDegree_le_of_dvd hdvd hne
  rw [natDegree_X_sub_C_one_pow (K := K) q, natDegree_X_sub_C_one_pow (K := K) (q - 1)] at hle
  omega

/-- The "regular vector" form of Theorem B, deduced from the minimal polynomial form. -/
theorem HallHigmanBsolv.toVector (h : HallHigmanBsolv.{u, v} K p) [Fact p.Prime] :
    HallHigmanBvector.{u, v} K p :=
  fun G _ _ hsol hodd V hf hO x n hx =>
    exists_ne_zero_apply_of_minpoly_eq_X_sub_one_pow (q := p ^ n)
      (pow_pos (Nat.Prime.pos Fact.out) n)
      (h G hsol hodd V hf hO x n hx)

/-- The arithmetic core of the use of Theorem B: in characteristic `p ≠ 2`, an element of order
`p ^ n` with `n > 0` cannot have minimal polynomial `(X - 1) ^ 2`. -/
theorem minpoly_ne_sq_of_minpoly_eq_pow [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module K M]
    {f : Module.End K M} {n : ℕ} (hn : 0 < n) (hp : p ≠ 2)
    (h : minpoly K f = (X - 1) ^ (p ^ n)) : minpoly K f ≠ (X - 1) ^ 2 := by
  intro h2
  have h' : (X - C (1 : K)) ^ (p ^ n) = (X - C (1 : K)) ^ 2 := by
    have h1 : (X - C (1 : K)) ^ (p ^ n) = minpoly K f := h.symm
    have h3 : minpoly K f = (X - C (1 : K)) ^ 2 := h2
    rw [h1, h3]
  have hdeg := congrArg Polynomial.natDegree h'
  rw [natDegree_X_sub_C_one_pow (K := K), natDegree_X_sub_C_one_pow (K := K)] at hdeg
  have hp2 : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) Nat.prime_two).mp
      (hdeg ▸ dvd_pow_self p hn.ne')
  exact hp hp2

/-- **Feit--Thompson's use of Theorem B** (the step "either `O_p(G) ≠ 1` or `𝔛` contains no
element whose minimal polynomial is `(x - I) ^ 2`" in the proof of FT Lemma 7.1):  if `G` is a
solvable group of odd order, `V` a faithful `K[G]`-module in characteristic `p ≠ 2` with
`O_p(G) = 1`, then no element of `G` of `p`-power order `p ^ n` with `n > 0` has minimal polynomial
`(X - 1) ^ 2` on `V`. -/
theorem minpoly_ne_X_sub_one_sq [Fact p.Prime] (hB : HallHigmanBsolv.{u, v} K p) (hp : p ≠ 2)
    {G : Type v} [Group G] [Finite G] (hsol : Group.IsSolvable G) (hodd : Odd (Nat.card G))
    (V : FDRep K G) (hfaith : Function.Injective V.ρ) (hOp : pCore p G = ⊥) (x : G) (n : ℕ)
    (hn : 0 < n) (hx : orderOf x = p ^ n) : minpoly K (V.ρ x) ≠ (X - 1) ^ 2 :=
  fun h => minpoly_ne_sq_of_minpoly_eq_pow hn hp (hB G hsol hodd V hfaith hOp x n hx) h

/-- The same statement for `p`-solvable groups: the form needed for Feit--Thompson's Lemma 7.1. -/
theorem minpoly_ne_X_sub_one_sq_psolvable [Fact p.Prime] (hB : HallHigmanB.{u, v} K p) (hp : p ≠ 2)
    {G : Type v} [Group G] [Finite G] (hsol : IsPSolvable p G) (hodd : Odd (Nat.card G))
    (V : FDRep K G) (hfaith : Function.Injective V.ρ) (hOp : pCore p G = ⊥) (x : G) (n : ℕ)
    (hn : 0 < n) (hx : orderOf x = p ^ n) : minpoly K (V.ρ x) ≠ (X - 1) ^ 2 :=
  fun h => minpoly_ne_sq_of_minpoly_eq_pow hn hp (hB G hsol hodd V hfaith hOp x n hx) h

end Work.HallHigman
