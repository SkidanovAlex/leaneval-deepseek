import Mathlib
import Submission.Work.DSM1p.Family
import Submission.Work.DSM1p.Family.flat_closure
import Submission.Work.DSM1p.Family.stepMap_root
import Submission.Work.DSM1p.Family.stepMap_algebraMap
import Submission.Work.DSM1p.Family.of_f

/-!
# Frobenius surjectivity modulo `p` for the multi-parameter perfectoid cover

`A′ = FamCompletion R p x` is the `p`-adic completion of the multi-parameter root closure
`A_∞ = R[x₁^{1/p^∞}, …, x_d^{1/p^∞}]`, where `x : Fin d → R` generates the maximal ideal of a
complete Noetherian local ring `R` of mixed characteristic whose residue field is perfect.

**Main result** (`frobSurj`):  the `p`-th power map is surjective on `A′ ⧸ (p)`:
for every `y : A′` there is `z : A′` with `y - z ^ p ∈ Ideal.span {(p : A′)}`.

This is the "generically perfectoid" input of Bhatt's proof of the direct summand theorem
(arXiv:1608.08882, §4).

## Proof

The whole content is Frobenius surjectivity on the *closure* modulo `p`, which is proved with the
series lemma `SERHyp` (`DSMap.Gaps.area_SER`, supplied here as the hypothesis `hSER`) applied to
`R` itself — the stages of the tower need no local-structure input.

1. `frobStage`: for `a : A_n` there is `u : A_{n+1}` with `u ^ p - step a ∈ (p)`.  Write `a` as
   the image of a polynomial `P`, so that `a = ∑_m c_m · (root_n) ^ m` with `c_m = P.coeff m`.
   For each coefficient the series lemma gives `b_m ^ p = c_m + p·h_m` in the *level-one* ring
   `A_1 = R[Z]/(Z_i ^ p - x_i)`, and since `A_1 → A_{n+1}`, `Z_i ↦ (root_{n+1} i) ^ (p ^ n)` is a
   ring map (`famFrobPhi`), the element `u = ∑_m Φ(b_m) · (root_{n+1}) ^ m` satisfies
   `u ^ p ≡ step a (mod p)` — the cross terms in the `p`-th power of a sum are divisible by `p`
   (`sum_pow_sub_mem_span_p`), and `step` of the monomial `(root_n) ^ m` is the monomial
   `∏_i ((root_{n+1} i) ^ p) ^ (m i)` (`step_mk_eq_sum`).
2. `frobSurj_closure`: every element of the filtered colimit `A_∞` lies in some stage
   (`Ring.DirectLimit.exists_of`), so the stage statement descends to the colimit.
3. Finally `A′ ⧸ (p) ≅ A_∞ ⧸ (p)` via the level-one projection `AdicCompletion.evalOneₐ`, whose
   kernel is exactly `(p)`; the statement transports along it.
-/

namespace Work.DSM1p.Family

universe u

set_option maxHeartbeats 800000

/-! ## The level-one ring `A_1 = R[Z]/(Z_i ^ p - x_i)`, in the shape produced by the series lemma -/

/-- The ideal of relations of the level-one stage of the root tower. -/
noncomputable abbrev FamRootRel (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) :
    Ideal (MvPolynomial (Fin d) R) :=
  Ideal.span (Set.range fun i => MvPolynomial.X i ^ p - MvPolynomial.C (x i))

/-- The level-one stage `R[Z]/(Z_i ^ p - x_i)`.  This is the ring in which the series lemma
`SERHyp` produces its elements. -/
noncomputable abbrev FamRootBase (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) :
    Type u :=
  MvPolynomial (Fin d) R ⧸ FamRootRel R p x

/-- In the level-one ring, the `R`-scalar action coincides with multiplication by the image of the
scalar.  (On a quotient ring the `•` of the statement below is the quotient-module `SMul`, which is
only propositionally, not definitionally, the `SMul` of the algebra structure; hence this is not
`Algebra.smul_def`.) -/
theorem famRootBase_smul (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (r : R)
    (y : FamRootBase R p x) : r • y = algebraMap R (FamRootBase R p x) r * y := by
  induction y using Submodule.Quotient.induction_on with
  | _ P =>
    rw [show (Submodule.Quotient.mk P : FamRootBase R p x) =
        Ideal.Quotient.mk (FamRootRel R p x) P from rfl]
    rw [show (r • (Ideal.Quotient.mk (FamRootRel R p x) P) : FamRootBase R p x) =
        Ideal.Quotient.mk (FamRootRel R p x) (r • P) from
        (Submodule.Quotient.mk_smul (p := FamRootRel R p x) r P).symm]
    rw [show algebraMap R (FamRootBase R p x) r =
        Ideal.Quotient.mk (FamRootRel R p x) (MvPolynomial.C r) from rfl]
    rw [← map_mul]
    congr 1
    exact Algebra.smul_def r P

/-! ## The ring map `Φ : A_1 → A_{n+1}` -/

/-- The ring map from the level-one stage to the `(n+1)`-st stage sending the `p`-th root `Z_i` of
`x_i` to the `p ^ n`-th power of the `p ^ (n+1)`-st root.  It exists because
`((root_{n+1} i) ^ (p ^ n)) ^ p = (root_{n+1} i) ^ (p ^ (n+1)) = x_i`. -/
noncomputable def famFrobPhi (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (n : ℕ) :
    FamRootBase R p x →+* Work.DSM1p.FamTower R p x (n + 1) :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom (algebraMap R (Work.DSM1p.FamTower R p x (n + 1)))
      (fun i => (Work.DSM1p.FamTower.root R p x (n + 1) i) ^ (p ^ n))) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.mp ha
    rw [map_sum]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [map_mul]
    have h0 : MvPolynomial.eval₂Hom (algebraMap R (Work.DSM1p.FamTower R p x (n + 1)))
        (fun i => (Work.DSM1p.FamTower.root R p x (n + 1) i) ^ (p ^ n))
        (MvPolynomial.X i ^ p - MvPolynomial.C (x i)) = 0 := by
      rw [map_sub, map_pow, MvPolynomial.eval₂Hom_X', MvPolynomial.eval₂Hom_C]
      refine sub_eq_zero.mpr ?_
      rw [← pow_mul, show p ^ n * p = p ^ (n + 1) from (pow_succ p n).symm,
        Work.DSM1p.FamTower.root_pow]
    rw [h0, mul_zero])

/-- `Φ` is a map of `R`-algebras. -/
theorem famFrobPhi_algebraMap (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (n : ℕ)
    (r : R) :
    famFrobPhi R p x n (algebraMap R _ r) =
      algebraMap R (Work.DSM1p.FamTower R p x (n + 1)) r := by
  rw [show algebraMap R (FamRootBase R p x) r = Ideal.Quotient.mk _ (MvPolynomial.C r) from rfl,
    show famFrobPhi R p x n = Ideal.Quotient.lift _ _ _ from rfl, Ideal.Quotient.lift_mk,
    MvPolynomial.eval₂Hom_C]

/-- `Φ` sends the adjoined root to the `p ^ n`-th power of the `(n+1)`-st root. -/
theorem famFrobPhi_root (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (n : ℕ)
    (i : Fin d) :
    famFrobPhi R p x n (Ideal.Quotient.mk _ (MvPolynomial.X i)) =
      (Work.DSM1p.FamTower.root R p x (n + 1) i) ^ (p ^ n) := by
  rw [show famFrobPhi R p x n = Ideal.Quotient.lift _ _ _ from rfl, Ideal.Quotient.lift_mk,
    MvPolynomial.eval₂Hom_X']

/-! ## Monomials in the roots -/

/-- The monomial `∏_i (root_n i) ^ (m i)` in the `n`-th stage of the tower. -/
noncomputable def rootMono (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (n : ℕ)
    (m : Fin d →₀ ℕ) : Work.DSM1p.FamTower R p x n :=
  m.prod (fun i k => (Work.DSM1p.FamTower.root R p x n i) ^ k)

/-- The `p`-th power of a monomial in the roots: the exponents are multiplied by `p`. -/
theorem rootMono_pow (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (n : ℕ)
    (m : Fin d →₀ ℕ) :
    (rootMono R p x n m) ^ p =
      m.prod (fun i k => ((Work.DSM1p.FamTower.root R p x n i) ^ p) ^ k) := by
  rw [rootMono, Finsupp.prod_pow, Finsupp.prod_pow, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul, ← pow_mul, mul_comm]

/-! ## The transition map on a polynomial -/

/-- The transition map of the tower, computed on a polynomial representative of an element of the
`n`-th stage: it is obtained by evaluating the polynomial at the `p`-th powers of the roots of the
`(n+1)`-st stage. -/
theorem step_mk_eq_sum (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (n : ℕ)
    (P : MvPolynomial (Fin d) R) :
    Work.DSM1p.FamTower.step R p x n (Ideal.Quotient.mk _ P) =
      ∑ m ∈ P.support, algebraMap R (Work.DSM1p.FamTower R p x (n + 1)) (P.coeff m) *
        m.prod (fun i k => ((Work.DSM1p.FamTower.root R p x (n + 1) i) ^ p) ^ k) := by
  rw [show Work.DSM1p.FamTower.step R p x n =
      Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom (algebraMap R (Work.DSM1p.FamTower R p x (n + 1)))
        (fun i => (Work.DSM1p.FamTower.root R p x (n + 1) i) ^ p)) _ from rfl,
    Ideal.Quotient.lift_mk]
  conv_lhs => rw [MvPolynomial.as_sum P]
  rw [map_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [MvPolynomial.eval₂Hom_monomial]

/-! ## The cross terms of a `p`-th power are divisible by `p` -/

/-- **Freshman's dream modulo `p`**: the cross terms in `(x + z) ^ p` are divisible by `p`. -/
theorem add_pow_sub_mem_span_p (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime) (x z : A) :
    (x + z) ^ p - x ^ p - z ^ p ∈ Ideal.span {(p : A)} := by
  have hp0 : 0 < p := hp.pos
  have hsplit : (∑ m ∈ Finset.range p, x ^ m * z ^ (p - m) * (↑(p.choose m) : A))
      = (∑ m ∈ Finset.range (p - 1), x ^ (m + 1) * z ^ (p - (m + 1)) *
          (↑(p.choose (m + 1)) : A)) + z ^ p := by
    have h := Finset.sum_range_succ' (fun m => x ^ m * z ^ (p - m) * (↑(p.choose m) : A)) (p - 1)
    rw [show p - 1 + 1 = p from by omega] at h
    rw [h]
    simp
  have hmem : (∑ m ∈ Finset.range (p - 1), x ^ (m + 1) * z ^ (p - (m + 1)) *
      (↑(p.choose (m + 1)) : A)) ∈ Ideal.span {(p : A)} := by
    apply Ideal.sum_mem
    intro m hm
    have hm' : m < p - 1 := Finset.mem_range.mp hm
    obtain ⟨c, hc⟩ := Nat.Prime.dvd_choose_self hp (Nat.succ_ne_zero m) (by omega)
    refine Ideal.mem_span_singleton.mpr ⟨(c : A) * x ^ (m + 1) * z ^ (p - (m + 1)), ?_⟩
    rw [hc]
    push_cast
    ring
  rw [add_pow, Finset.sum_range_succ, hsplit]
  rw [show x ^ p * z ^ (p - p) * (↑(p.choose p) : A) = x ^ p by simp]
  have : (∑ m ∈ Finset.range (p - 1), x ^ (m + 1) * z ^ (p - (m + 1)) *
      (↑(p.choose (m + 1)) : A)) + z ^ p + x ^ p - x ^ p - z ^ p
      = ∑ m ∈ Finset.range (p - 1), x ^ (m + 1) * z ^ (p - (m + 1)) *
          (↑(p.choose (m + 1)) : A) := by ring
  rw [this]
  exact hmem

/-- The cross terms in the `p`-th power of a finite sum are divisible by `p`. -/
theorem sum_pow_sub_mem_span_p {ι : Type*} (A : Type u) [CommRing A] (p : ℕ) (hp : p.Prime)
    (s : Finset ι) (y : ι → A) :
    (∑ i ∈ s, y i) ^ p - ∑ i ∈ s, (y i) ^ p ∈ Ideal.span {(p : A)} := by
  classical
  induction s using Finset.induction with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty, zero_pow hp.ne_zero, sub_self]
    exact Ideal.zero_mem _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := add_pow_sub_mem_span_p A p hp (y a) (∑ i ∈ s, y i)
    have : (y a + ∑ i ∈ s, y i) ^ p - (y a ^ p + ∑ i ∈ s, y i ^ p)
        = ((y a + ∑ i ∈ s, y i) ^ p - y a ^ p - (∑ i ∈ s, y i) ^ p)
          + ((∑ i ∈ s, y i) ^ p - ∑ i ∈ s, y i ^ p) := by ring
    rw [this]
    exact Ideal.add_mem _ h1 ih

/-! ## Frobenius surjectivity on a single stage -/

/-- **Frobenius surjectivity modulo `p`, one stage up.**  For every `a` in the `n`-th stage of the
tower there is `u` in the `(n+1)`-st stage whose `p`-th power is `step a` modulo `p`.

This is the series lemma `SERHyp` applied to `R` with the system of parameters `x`, transported
along the ring map `famFrobPhi : A_1 → A_{n+1}`. -/
theorem frobStage (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (p : ℕ)
    [Fact p.Prime] (hSER : Work.DSM1p.SERHyp.{u} p)
    (hR : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    (hpm : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (hperf : ∀ y : R, ∃ μ : R, y - μ ^ p ∈ IsLocalRing.maximalIdeal R) {d : ℕ} (x : Fin d → R)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (n : ℕ) (a : Work.DSM1p.FamTower R p x n) :
    ∃ u : Work.DSM1p.FamTower R p x (n + 1),
      u ^ p - Work.DSM1p.FamTower.step R p x n a ∈
        Ideal.span {(p : Work.DSM1p.FamTower R p x (n + 1))} := by
  classical
  obtain ⟨P, hP⟩ := Ideal.Quotient.mk_surjective a
  have hser : ∀ m : Fin d →₀ ℕ, ∃ b h : FamRootBase R p x,
      b ^ p = algebraMap R (FamRootBase R p x) (P.coeff m) + (p : R) • h := fun m => by
    obtain ⟨b, h, h1, -⟩ := hSER R hR hpm hperf x hx (P.coeff m)
    exact ⟨b, h, h1⟩
  choose b hh hb using hser
  refine ⟨∑ m ∈ P.support, famFrobPhi R p x n (b m) * rootMono R p x (n + 1) m, ?_⟩
  have hcross : (∑ m ∈ P.support, famFrobPhi R p x n (b m) * rootMono R p x (n + 1) m) ^ p
      - ∑ m ∈ P.support, (famFrobPhi R p x n (b m) * rootMono R p x (n + 1) m) ^ p
      ∈ Ideal.span {(p : Work.DSM1p.FamTower R p x (n + 1))} :=
    sum_pow_sub_mem_span_p (Work.DSM1p.FamTower R p x (n + 1)) p (Fact.out : p.Prime) P.support
      (fun m => famFrobPhi R p x n (b m) * rootMono R p x (n + 1) m)
  have hterm : ∀ m, (famFrobPhi R p x n (b m) * rootMono R p x (n + 1) m) ^ p
      - algebraMap R (Work.DSM1p.FamTower R p x (n + 1)) (P.coeff m) *
        (rootMono R p x (n + 1) m) ^ p
      ∈ Ideal.span {(p : Work.DSM1p.FamTower R p x (n + 1))} := by
    intro m
    have h1 : (famFrobPhi R p x n (b m)) ^ p =
        algebraMap R (Work.DSM1p.FamTower R p x (n + 1)) (P.coeff m)
        + (p : Work.DSM1p.FamTower R p x (n + 1)) * famFrobPhi R p x n (hh m) := by
      rw [← map_pow (famFrobPhi R p x n) (b m) p, hb m, famRootBase_smul, map_add, map_mul,
        famFrobPhi_algebraMap]
      congr 1
      rw [famFrobPhi_algebraMap, map_natCast]
    rw [mul_pow, h1]
    have : (algebraMap R (Work.DSM1p.FamTower R p x (n + 1)) (P.coeff m)
        + (p : Work.DSM1p.FamTower R p x (n + 1)) * famFrobPhi R p x n (hh m))
          * (rootMono R p x (n + 1) m) ^ p
        - algebraMap R (Work.DSM1p.FamTower R p x (n + 1)) (P.coeff m) *
          (rootMono R p x (n + 1) m) ^ p
        = (p : Work.DSM1p.FamTower R p x (n + 1)) *
          (famFrobPhi R p x n (hh m) * (rootMono R p x (n + 1) m) ^ p) := by ring
    rw [this]
    exact Ideal.mem_span_singleton.mpr (dvd_mul_right _ _)
  have hstep : Work.DSM1p.FamTower.step R p x n a
      = ∑ m ∈ P.support, algebraMap R (Work.DSM1p.FamTower R p x (n + 1)) (P.coeff m) *
          (rootMono R p x (n + 1) m) ^ p := by
    rw [← hP, step_mk_eq_sum]
    exact Finset.sum_congr rfl fun m _ => by rw [← rootMono_pow]
  have hdecomp : (∑ m ∈ P.support, famFrobPhi R p x n (b m) * rootMono R p x (n + 1) m) ^ p
      - Work.DSM1p.FamTower.step R p x n a
      = ((∑ m ∈ P.support, famFrobPhi R p x n (b m) * rootMono R p x (n + 1) m) ^ p
          - ∑ m ∈ P.support, (famFrobPhi R p x n (b m) * rootMono R p x (n + 1) m) ^ p)
        + ∑ m ∈ P.support, ((famFrobPhi R p x n (b m) * rootMono R p x (n + 1) m) ^ p
            - algebraMap R (Work.DSM1p.FamTower R p x (n + 1)) (P.coeff m) *
              (rootMono R p x (n + 1) m) ^ p) := by
    rw [hstep, Finset.sum_sub_distrib]
    ring
  rw [hdecomp]
  exact Ideal.add_mem _ hcross (Ideal.sum_mem _ fun m _ => hterm m)

/-! ## The transition map `A_n → A_{n+1}` of the tower vs `stepMap` -/

/-- The single transition map `step` of the tower is a map of `R`-algebras. -/
theorem FamTower.step_algebraMap (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R)
    (n : ℕ) (r : R) :
    Work.DSM1p.FamTower.step R p x n (algebraMap R (Work.DSM1p.FamTower R p x n) r) =
      algebraMap R (Work.DSM1p.FamTower R p x (n + 1)) r := by
  rw [show algebraMap R (Work.DSM1p.FamTower R p x n) r =
      Ideal.Quotient.mk _ (MvPolynomial.C r) from rfl,
    show Work.DSM1p.FamTower.step R p x n = Ideal.Quotient.lift _ _ _ from rfl,
    Ideal.Quotient.lift_mk, MvPolynomial.eval₂Hom_C]

/-- The transition map `stepMap n (n+1) (le_succ n)` of the tower coincides with the single
transition map `step n`; it is defined through a cast of the codomain index, and the two ring maps
are compared on the image of `R` and on the adjoined roots. -/
theorem stepMap_succ_eq_step (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (n : ℕ) :
    Work.DSM1p.FamTower.stepMap R p x n (n + 1) (Nat.le_succ n) =
      Work.DSM1p.FamTower.step R p x n := by
  refine famTower_ringHom_ext R p x n (fun r => ?_) (fun i => ?_)
  · rw [stepMap_algebraMap, FamTower.step_algebraMap]
  · rw [stepMap_root, Work.DSM1p.FamTower.step_root,
      show n + 1 - n = 1 from Nat.add_sub_cancel_left n 1, pow_one]

/-- The image of a stage in the closure is independent of the level, in the form needed here:
`of (n+1) (step a) = of n a`. -/
theorem of_step (R : Type u) [CommRing R] (p : ℕ) {d : ℕ} (x : Fin d → R) (n : ℕ)
    (a : Work.DSM1p.FamTower R p x n) :
    Work.DSM1p.FamClosure.of R p x (n + 1) (Work.DSM1p.FamTower.step R p x n a) =
      Work.DSM1p.FamClosure.of R p x n a := by
  rw [← of_f R p x (Nat.le_succ n) a, stepMap_succ_eq_step]

/-! ## Frobenius surjectivity on the root closure -/

/-- **Frobenius surjectivity modulo `p` on the root closure**: every element of
`A_∞ = R[x₁^{1/p^∞}, …, x_d^{1/p^∞}]` has a `p`-th root modulo `p`. -/
theorem frobSurj_closure (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (p : ℕ)
    [Fact p.Prime] (hSER : Work.DSM1p.SERHyp.{u} p)
    (hR : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    (hpm : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (hperf : ∀ y : R, ∃ μ : R, y - μ ^ p ∈ IsLocalRing.maximalIdeal R) {d : ℕ} (x : Fin d → R)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (a : Work.DSM1p.FamClosure R p x) :
    ∃ w : Work.DSM1p.FamClosure R p x,
      w ^ p - a ∈ Ideal.span {(p : Work.DSM1p.FamClosure R p x)} := by
  obtain ⟨n, aₙ, ha⟩ := Ring.DirectLimit.exists_of a
  obtain ⟨u, hu⟩ := frobStage R p hSER hR hpm hperf x hx n aₙ
  refine ⟨Work.DSM1p.FamClosure.of R p x (n + 1) u, ?_⟩
  have hmap : Ideal.map (Work.DSM1p.FamClosure.of R p x (n + 1))
      (Ideal.span {(p : Work.DSM1p.FamTower R p x (n + 1))}) =
      Ideal.span {(p : Work.DSM1p.FamClosure R p x)} := by
    rw [Ideal.map_span, Set.image_singleton, map_natCast]
  rw [← hmap, ← map_pow, ← ha, ← of_step R p x n aₙ, ← map_sub]
  exact Ideal.mem_map_of_mem _ hu

/-! ## Frobenius surjectivity modulo `p` on the completion -/

theorem frobSurj (R : Type u) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (p : ℕ)
    [Fact p.Prime] (hSER : Work.DSM1p.SERHyp.{u} p)
    (hR : IsAdicComplete (IsLocalRing.maximalIdeal R) R)
    (hpm : (p : R) ∈ IsLocalRing.maximalIdeal R)
    (hperf : ∀ y : R, ∃ μ : R, y - μ ^ p ∈ IsLocalRing.maximalIdeal R) {d : ℕ} (x : Fin d → R)
    (hx : Ideal.span (Set.range x) = IsLocalRing.maximalIdeal R)
    (y : Work.DSM1p.FamCompletion R p x) :
    ∃ z : Work.DSM1p.FamCompletion R p x,
      y - z ^ p ∈ Ideal.span {(p : Work.DSM1p.FamCompletion R p x)} := by
  classical
  have hFG : (Ideal.span {(p : Work.DSM1p.FamClosure R p x)}).FG :=
    ⟨{(p : Work.DSM1p.FamClosure R p x)}, by simp⟩
  have hker : RingHom.ker (AdicCompletion.evalOneₐ
        (Ideal.span {(p : Work.DSM1p.FamClosure R p x)})).toRingHom =
      Ideal.span {(p : Work.DSM1p.FamCompletion R p x)} := by
    rw [AdicCompletion.ker_evalOneₐ_eq_map (Ideal.span {(p : Work.DSM1p.FamClosure R p x)}) hFG,
      Ideal.map_span, Set.image_singleton, map_natCast]
  have heval : ∀ w : Work.DSM1p.FamClosure R p x,
      AdicCompletion.evalOneₐ (Ideal.span {(p : Work.DSM1p.FamClosure R p x)})
        (algebraMap (Work.DSM1p.FamClosure R p x) (Work.DSM1p.FamCompletion R p x) w) =
      Ideal.Quotient.mk (Ideal.span {(p : Work.DSM1p.FamClosure R p x)}) w := fun w =>
    DFunLike.congr_fun
      (AdicCompletion.evalOneₐ_comp_algebraMap_eq_mk
        (Ideal.span {(p : Work.DSM1p.FamClosure R p x)})) w
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalOneₐ
    (Ideal.span {(p : Work.DSM1p.FamClosure R p x)}) y)
  obtain ⟨w, hw⟩ := frobSurj_closure R p hSER hR hpm hperf x hx a
  refine ⟨algebraMap (Work.DSM1p.FamClosure R p x) (Work.DSM1p.FamCompletion R p x) w, ?_⟩
  have key : AdicCompletion.evalOneₐ (Ideal.span {(p : Work.DSM1p.FamClosure R p x)})
      (y - (algebraMap (Work.DSM1p.FamClosure R p x)
        (Work.DSM1p.FamCompletion R p x) w) ^ p) = 0 := by
    rw [map_sub, map_pow, heval, ← ha, ← map_pow, ← map_sub,
      Ideal.Quotient.eq_zero_iff_mem, show a - w ^ p = -(w ^ p - a) from by ring,
      Ideal.neg_mem_iff]
    exact hw
  have key' : y - (algebraMap (Work.DSM1p.FamClosure R p x)
      (Work.DSM1p.FamCompletion R p x) w) ^ p ∈ RingHom.ker (AdicCompletion.evalOneₐ
        (Ideal.span {(p : Work.DSM1p.FamClosure R p x)})).toRingHom := key
  rwa [hker] at key'

end Work.DSM1p.Family
