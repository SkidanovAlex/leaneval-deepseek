import Mathlib
import Submission.Commons.Data.ZMod.card_filter_castHom_pi

/-!
# The Chinese-remainder factorisation of an affine congruence system (Green–Tao §10, eq. (ddr) step 1)

## Goal

For squarefree moduli `M i ∣ D` and the affine forms `θ_i(x) = W·(∑_j A_{ij} x_j + b_i) + 1`, the
number of solutions in `(ZMod D)^t` of the system `M i ∣ θ_i(x)` (all `i`) factorises over the
primes of `D`: for `p^e ∥ D` the number of solutions modulo `p^e` is `p^((e-1)*t)` times the number
of solutions modulo `p`, and then the CRT multiplies over the primes.

Proof sketch:
1. `ZMod.equivPi (hD : D ≠ 0) : ZMod D ≃+* Π (p : D.primeFactors), ZMod (p ^ D.factorization p)`
   (Mathlib, `Mathlib/Data/ZMod/QuotientRing.lean`) splits the modulus into prime powers.  Transport
   the filtered cardinality along the induced equivalence `(Fin t → ZMod D) ≃ (Fin t → Π ...)`
   and use `Finset.card_product` (or its `Pi`-analogue) to split the filter over the product type,
   cf. the existing commons lemma `card_filter_prod_ringEquiv` for the two-factor case.
2. For the prime-power factor: the condition `M i ∣ θ_i(x)` with `M i` squarefree means that for each
   `p | M i` only `p | θ_i(x)` matters, and `ZMod.castHom` of `θ_i(x) ∈ ZMod (p^e)` to `ZMod p` is
   `θ_i(x mod p)`.  Hence the solution set in `(ZMod p^e)^t` is the full preimage under the
   surjection `(ZMod p^e)^t → (ZMod p)^t` of the solution set modulo `p`; all fibres have size
   `p^((e-1)*t)` (`Commons.Data.ZMod.card_castHom_fiber`, then take the product over coordinates).
3. Combine: the cardinality is the product over `p ∈ D.primeFactors` of the local cardinalities.

## Notes for the prover
* `ZMod (M i)` needs no `[NeZero (M i)]`; only `Fintype (ZMod n)` needs `[NeZero n]`, which is why
  the local factor is stated through the `locCount` definition (it takes the instance explicitly).
* The product over the primes is written over `D.primeFactors.attach` so that the proof
  `Nat.prime_of_mem_primeFactors p.2` is available to build the `NeZero (p:ℕ)` instance.
* Useful existing commons lemmas: `Commons.NumberTheory.Sieve.card_affine_system_mul`
  (two coprime moduli), `Commons.Data.ZMod.card_castHom_fiber`, `Commons.Data.ZMod.card_filter_castHom_pi`.
* Keep the statement exactly as given (it is consumed by `Submission/Work/GYAvg.lean`).
-/

open Finset
open scoped BigOperators

namespace Commons.NumberTheory.Sieve

/-- A prime dividing `D` is nonzero; this lets `ZMod (p : ℕ)` and its prime powers inherit the
`NeZero` instance needed for `Fintype`. -/
instance instNeZeroCoePrimeFactors {D : ℕ} (p : D.primeFactors) : NeZero (p : ℕ) :=
  NeZero.of_pos (Nat.prime_of_mem_primeFactors p.2).pos

/-- The affine form `θ_i(x) = W·(∑_j A_{ij} x_j + b_i) + 1` interpreted in `ZMod N`. -/
def thetaMod {m t : ℕ} (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (N : ℕ)
    [NeZero N] (i : Fin m) (x : Fin t → ZMod N) : ZMod N :=
  (W : ZMod N) * ((∑ j, ((A i j : ℤ) : ZMod N) * x j) + ((b i : ℤ) : ZMod N)) + 1

/-- The local (mod-`N`) solution count of the system `N ∣ M i → θ_i(x) = 0`. -/
def locCount {m t : ℕ} (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (M : Fin m → ℕ)
    (N : ℕ) [NeZero N] : ℕ :=
  ((Finset.univ : Finset (Fin t → ZMod N)).filter
    (fun x => ∀ i, N ∣ M i → thetaMod W A b N i x = 0)).card


/-- The affine form `θ_i` evaluated at integer representatives:
`θ_i(v) = W·(∑_j A_{ij} v_j + b_i) + 1`. -/
def thetaInt {m t : ℕ} (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (i : Fin m)
    (v : Fin t → ℤ) : ℤ :=
  W * ((∑ j, A i j * v j) + b i) + 1

/-- `thetaMod` is the image of the integer form `thetaInt` under the reduction `ℤ → ZMod N`. -/
lemma thetaMod_eq_intCast {m t : ℕ} (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    {N : ℕ} [NeZero N] (i : Fin m) (x : Fin t → ZMod N) :
    thetaMod W A b N i x = ((thetaInt W A b i (fun j => (x j).val) : ℤ) : ZMod N) := by
  have hx : ∀ j, x j = ((x j).val : ZMod N) := fun j => (ZMod.natCast_zmod_val (x j)).symm
  have hsum : (∑ j, ((A i j : ℤ) : ZMod N) * x j)
      = ((∑ j, A i j * (x j).val : ℤ) : ZMod N) := by
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Int.cast_mul, Int.cast_natCast, ZMod.natCast_zmod_val]
  simp only [thetaMod, thetaInt]
  rw [hsum]
  push_cast
  ring

/-- `thetaMod` is the reduction of the integer form `thetaInt` at integer arguments. -/
lemma thetaMod_intCast {m t : ℕ} (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    {N : ℕ} [NeZero N] (i : Fin m) (v : Fin t → ℤ) :
    ((thetaInt W A b i v : ℤ) : ZMod N) = thetaMod W A b N i (fun j => ((v j : ℤ) : ZMod N)) := by
  simp only [thetaMod, thetaInt]
  push_cast
  ring

/-- `thetaMod` is natural with respect to reduction of the modulus. -/
lemma castHom_thetaMod {m t : ℕ} (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ)
    {N K : ℕ} [NeZero N] [NeZero K] (h : K ∣ N) (i : Fin m) (x : Fin t → ZMod N) :
    ZMod.castHom h (ZMod K) (thetaMod W A b N i x)
      = thetaMod W A b K i (fun j => ZMod.castHom h (ZMod K) (x j)) := by
  simp only [thetaMod, map_add, map_mul, map_natCast, map_intCast, map_one, map_sum]

/-- Vanishing of `thetaMod` after reduction of the modulus, in terms of integer divisibility. -/
lemma castHom_thetaMod_eq_zero_iff {m t : ℕ} (W : ℕ) (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) {N K : ℕ} [NeZero N] [NeZero K] (h : K ∣ N) (i : Fin m)
    (x : Fin t → ZMod N) :
    ZMod.castHom h (ZMod K) (thetaMod W A b N i x) = 0
      ↔ (K : ℤ) ∣ thetaInt W A b i (fun j => (x j).val) := by
  rw [thetaMod_eq_intCast W A b i x, map_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- For a squarefree `N`, `N ∣ a` iff every prime factor of `N` divides `a`. -/
lemma dvd_iff_forall_primeFactors_dvd {N a : ℕ} (hN : Squarefree N) :
    N ∣ a ↔ ∀ p ∈ N.primeFactors, p ∣ a := by
  constructor
  · intro h p hp
    exact (Nat.dvd_of_mem_primeFactors hp).trans h
  · intro h
    rcases eq_or_ne a 0 with rfl | ha
    · exact dvd_zero N
    · rw [← Nat.prod_primeFactors_of_squarefree hN, Nat.prod_primeFactors_dvd_iff ha]
      intro p hp
      rw [Nat.mem_primeFactors]
      exact ⟨Nat.prime_of_mem_primeFactors hp, h p hp, ha⟩

/-- Integer form of `dvd_iff_forall_primeFactors_dvd`. -/
lemma int_dvd_iff_forall_primeFactors_dvd {N : ℕ} (hN : Squarefree N) (a : ℤ) :
    (N : ℤ) ∣ a ↔ ∀ p ∈ N.primeFactors, (p : ℤ) ∣ a := by
  rw [Int.natCast_dvd, dvd_iff_forall_primeFactors_dvd hN]
  simp only [Int.natCast_dvd]

/-- The cardinality of a product of filtered types is the product of the cardinalities. -/
lemma card_filter_pi {α : Type*} [Fintype α] [DecidableEq α] {β : α → Type*}
    [∀ a, Fintype (β a)] (q : ∀ a, β a → Prop) [∀ a, DecidablePred (q a)] :
    (Finset.univ.filter (fun x : ∀ a, β a => ∀ a, q a (x a))).card
      = ∏ a, (Finset.univ.filter (q a)).card := by
  classical
  rw [← Fintype.card_subtype (fun x : ∀ a, β a => ∀ a, q a (x a))]
  calc Fintype.card {x : ∀ a, β a // ∀ a, q a (x a)}
      = Fintype.card (∀ a, {b : β a // q a b}) := Fintype.card_congr Equiv.subtypePiEquivPi
    _ = ∏ a, Fintype.card {b : β a // q a b} := Fintype.card_pi
    _ = ∏ a, (Finset.univ.filter (q a)).card := by
        apply Finset.prod_congr rfl
        intro a _
        rw [Fintype.card_subtype]

/-- Reduction of `ZMod` maps a residue to the cast of its representative. -/
lemma castHom_val {m n : ℕ} [NeZero n] (h : m ∣ n) (i : ZMod n) :
    ZMod.castHom h (ZMod m) i = (i.val : ZMod m) := by
  rw [ZMod.castHom_apply]
  exact (ZMod.natCast_val i).symm

/-- The component of the Chinese remainder equivalence is the corresponding reduction. -/
lemma equivPi_apply_eq {D : ℕ} (hD : D ≠ 0) (p : D.primeFactors)
    (h : (p : ℕ) ^ D.factorization (p : ℕ) ∣ D) (a : ZMod D) :
    ZMod.equivPi D hD a p = ZMod.castHom h (ZMod ((p : ℕ) ^ D.factorization (p : ℕ))) a := by
  have key : (Pi.evalRingHom
        (fun q : D.primeFactors => ZMod ((q : ℕ) ^ D.factorization (q : ℕ))) p).comp
        (ZMod.equivPi D hD).toRingHom
      = ZMod.castHom h (ZMod ((p : ℕ) ^ D.factorization (p : ℕ))) :=
    Subsingleton.elim _ _
  simpa using RingHom.congr_fun key a

/-- Composition of two reductions of `ZMod`. -/
lemma castHom_castHom {m n d : ℕ} (h1 : m ∣ n) (h2 : n ∣ d) (a : ZMod d) :
    ZMod.castHom h1 (ZMod m) (ZMod.castHom h2 (ZMod n) a)
      = ZMod.castHom (dvd_trans h1 h2) (ZMod m) a := by
  rw [← RingHom.comp_apply, ZMod.castHom_comp]

/-- `p ∣ p ^ e` when `p ^ e ∥ D` (`e ≥ 1`). -/
lemma dvd_self_pow_factorization {D : ℕ} (hD : D ≠ 0) (p : D.primeFactors) :
    (p : ℕ) ∣ (p : ℕ) ^ D.factorization (p : ℕ) :=
  dvd_pow_self _
    (by
      have h1 := (Nat.prime_of_mem_primeFactors p.2).dvd_iff_one_le_factorization hD |>.mp
        (Nat.dvd_of_mem_primeFactors p.2)
      omega)

/-- `p ^ e ∣ D` when `p ^ e ∥ D`. -/
lemma pow_factorization_dvd {D : ℕ} (hD : D ≠ 0) (p : D.primeFactors) :
    (p : ℕ) ^ D.factorization (p : ℕ) ∣ D := by
  have h := Finset.dvd_prod_of_mem
    (fun q : D.primeFactors => (q : ℕ) ^ D.factorization (q : ℕ)) (Finset.mem_univ p)
  rwa [← Nat.prod_primeFactors_coe_pow_factorization hD] at h

/-- The prime-local form of the condition `M i ∣ θ_i(x)`: divisibility of the integer form by
the prime `q` is equivalent to the vanishing of the reduced `thetaMod` at the prime power. -/
lemma int_dvd_thetaInt_iff {m t : ℕ} {D : ℕ} [NeZero D] (W : ℕ) (A : Fin m → Fin t → ℤ)
    (b : Fin m → ℤ) (hpe : ∀ q : D.primeFactors, (q : ℕ) ∣ (q : ℕ) ^ D.factorization (q : ℕ))
    (hNpD : ∀ q : D.primeFactors, (q : ℕ) ^ D.factorization (q : ℕ) ∣ D)
    (q : D.primeFactors) (i : Fin m) (x : Fin t → ZMod D) :
    (q : ℤ) ∣ thetaInt W A b i (fun j => (x j).val) ↔
      ZMod.castHom (hpe q) (ZMod (q : ℕ))
        (thetaMod W A b ((q : ℕ) ^ D.factorization (q : ℕ)) i
          (fun j => ZMod.equivPi D (NeZero.ne D) (x j) q)) = 0 := by
  have hcomp : ∀ j, ZMod.castHom (hpe q) (ZMod (q : ℕ))
        (ZMod.equivPi D (NeZero.ne D) (x j) q) = (((x j).val : ℤ) : ZMod (q : ℕ)) := by
    intro j
    rw [equivPi_apply_eq (NeZero.ne D) q (hNpD q), castHom_castHom, castHom_val]
    norm_cast
  have hfun : (fun j => ZMod.castHom (hpe q) (ZMod (q : ℕ))
        (ZMod.equivPi D (NeZero.ne D) (x j) q)) = (fun j => (((x j).val : ℤ) : ZMod (q : ℕ))) :=
    funext hcomp
  constructor
  · intro h
    rw [castHom_thetaMod, hfun, ← thetaMod_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd]
    exact h
  · intro h
    rw [castHom_thetaMod, hfun, ← thetaMod_intCast, ZMod.intCast_zmod_eq_zero_iff_dvd] at h
    exact h

/-- For squarefree `M i`, the condition `M i ∣ θ_i(x)` is equivalent to the conjunction, over all
primes `q ∣ D` dividing `M i`, of the corresponding condition modulo `q`, expressed through the
Chinese remainder components of `x`. -/
lemma castHom_thetaMod_eq_zero_iff_prime {m t : ℕ} (W : ℕ) {D : ℕ} [NeZero D]
    (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (M : Fin m → ℕ)
    (hM : ∀ i, M i ∣ D) (hMsq : ∀ i, Squarefree (M i)) (hMpos : ∀ i, 0 < M i)
    (hpe : ∀ q : D.primeFactors, (q : ℕ) ∣ (q : ℕ) ^ D.factorization (q : ℕ))
    (hNpD : ∀ q : D.primeFactors, (q : ℕ) ^ D.factorization (q : ℕ) ∣ D)
    (i : Fin m) (x : Fin t → ZMod D) :
    ZMod.castHom (hM i) (ZMod (M i)) (thetaMod W A b D i x) = 0 ↔
      ∀ q : D.primeFactors, (q : ℕ) ∣ M i →
        ZMod.castHom (hpe q) (ZMod (q : ℕ))
          (thetaMod W A b ((q : ℕ) ^ D.factorization (q : ℕ)) i
            (fun j => ZMod.equivPi D (NeZero.ne D) (x j) q)) = 0 := by
  haveI : NeZero (M i) := NeZero.of_pos (hMpos i)
  rw [castHom_thetaMod_eq_zero_iff W A b (hM i) i x,
    int_dvd_iff_forall_primeFactors_dvd (hMsq i)]
  constructor
  · intro h q hqM
    have hqmem : (q : ℕ) ∈ (M i).primeFactors := by
      rw [Nat.mem_primeFactors]
      exact ⟨Nat.prime_of_mem_primeFactors q.2, hqM, ne_of_gt (hMpos i)⟩
    exact (int_dvd_thetaInt_iff W A b hpe hNpD q i x).mp (h (q : ℕ) hqmem)
  · intro h p hp
    have hpD : p ∈ D.primeFactors := by
      rw [Nat.mem_primeFactors]
      exact ⟨Nat.prime_of_mem_primeFactors hp, (Nat.dvd_of_mem_primeFactors hp).trans (hM i),
        NeZero.ne D⟩
    exact (int_dvd_thetaInt_iff W A b hpe hNpD ⟨p, hpD⟩ i x).mpr
      (h ⟨p, hpD⟩ (Nat.dvd_of_mem_primeFactors hp))

/-- **The CRT factorisation of the congruence-system count.**  For squarefree moduli `M i ∣ D`, the
number of `x ∈ (ZMod D)^t` with `M i ∣ θ_i(x)` for all `i` is the product over the primes `p^e ∥ D`
of `p^((e-1)*t)` times the number of `x ∈ (ZMod p)^t` with `p ∣ M i → θ_i(x) = 0` for all `i`. -/
theorem card_system_eq_prod_primeFactors {m t : ℕ} (W D : ℕ) [NeZero D]
    (A : Fin m → Fin t → ℤ) (b : Fin m → ℤ) (M : Fin m → ℕ)
    (hM : ∀ i, M i ∣ D) (hMsq : ∀ i, Squarefree (M i)) (hMpos : ∀ i, 0 < M i) :
    ((Finset.univ : Finset (Fin t → ZMod D)).filter
        (fun x => ∀ i, ZMod.castHom (hM i) (ZMod (M i)) (thetaMod W A b D i x) = 0)).card
      = ∏ p ∈ D.primeFactors.attach,
          (p : ℕ) ^ ((D.factorization (p : ℕ) - 1) * t) *
            (@locCount m t W A b M (p : ℕ)
              (NeZero.of_pos (Nat.Prime.pos (Nat.prime_of_mem_primeFactors p.2)))) := by
  classical
  have hpe := dvd_self_pow_factorization (D := D) (NeZero.ne D)
  have hNpD := pow_factorization_dvd (D := D) (NeZero.ne D)
  -- the Chinese remainder equivalence on `t`-tuples
  let Ψ : (Fin t → ZMod D) ≃ (∀ q : D.primeFactors, Fin t → ZMod ((q : ℕ) ^ D.factorization (q : ℕ))) :=
    { toFun := fun x q j => ZMod.equivPi D (NeZero.ne D) (x j) q
      invFun := fun y j => (ZMod.equivPi D (NeZero.ne D)).symm (fun q => y q j)
      left_inv := by intro x; funext j; simp
      right_inv := by intro y; funext q j; simp }
  -- the local condition at a prime power
  let locC : (q : D.primeFactors) → (Fin t → ZMod ((q : ℕ) ^ D.factorization (q : ℕ))) → Prop :=
    fun q y => ∀ i, (q : ℕ) ∣ M i →
      ZMod.castHom (hpe q) (ZMod (q : ℕ))
        (thetaMod W A b ((q : ℕ) ^ D.factorization (q : ℕ)) i y) = 0
  have hcond : ∀ x : Fin t → ZMod D,
      ((∀ i, ZMod.castHom (hM i) (ZMod (M i)) (thetaMod W A b D i x) = 0) ↔
        (∀ q : D.primeFactors, locC q (Ψ x q))) := by
    intro x
    constructor
    · intro h q i hqM
      exact (castHom_thetaMod_eq_zero_iff_prime W A b M hM hMsq hMpos hpe hNpD i x).mp
        (h i) q hqM
    · intro h i
      exact (castHom_thetaMod_eq_zero_iff_prime W A b M hM hMsq hMpos hpe hNpD i x).mpr
        (fun q hqM => h q i hqM)
  -- step 1: split the count over the Chinese remainder components
  have hstep1 : ((Finset.univ : Finset (Fin t → ZMod D)).filter
        (fun x => ∀ i, ZMod.castHom (hM i) (ZMod (M i)) (thetaMod W A b D i x) = 0)).card
      = ∏ q : D.primeFactors, (Finset.univ.filter (locC q)).card := by
    rw [← Fintype.card_subtype (fun x : Fin t → ZMod D =>
      ∀ i, ZMod.castHom (hM i) (ZMod (M i)) (thetaMod W A b D i x) = 0)]
    rw [Fintype.card_congr (Equiv.subtypeEquiv (p := fun x : Fin t → ZMod D =>
        ∀ i, ZMod.castHom (hM i) (ZMod (M i)) (thetaMod W A b D i x) = 0)
      (q := fun y : (∀ q : D.primeFactors, Fin t → ZMod ((q : ℕ) ^ D.factorization (q : ℕ))) =>
        ∀ q, locC q (y q)) Ψ hcond)]
    rw [Fintype.card_subtype (fun y : (∀ q : D.primeFactors,
      Fin t → ZMod ((q : ℕ) ^ D.factorization (q : ℕ))) => ∀ q, locC q (y q))]
    exact card_filter_pi locC
  -- step 2: the local fibre count
  have hstep2 : ∀ q : D.primeFactors, (Finset.univ.filter (locC q)).card
      = (q : ℕ) ^ ((D.factorization (q : ℕ) - 1) * t) *
          @locCount m t W A b M (q : ℕ)
            (NeZero.of_pos (Nat.Prime.pos (Nat.prime_of_mem_primeFactors q.2))) := by
    intro q
    have hqprime := Nat.prime_of_mem_primeFactors q.2
    have hq1 : 1 ≤ D.factorization (q : ℕ) :=
      (hqprime.dvd_iff_one_le_factorization (NeZero.ne D)).mp (Nat.dvd_of_mem_primeFactors q.2)
    have hfib := Commons.Data.ZMod.card_filter_castHom_pi (m := (q : ℕ))
      (n := (q : ℕ) ^ D.factorization (q : ℕ)) (hpe q) (t := t)
      (S := fun u : Fin t → ZMod (q : ℕ) =>
        ∀ i, (q : ℕ) ∣ M i → thetaMod W A b (q : ℕ) i u = 0)
    have hfil : (Finset.univ.filter (locC q))
        = (Finset.univ.filter (fun y : Fin t → ZMod ((q : ℕ) ^ D.factorization (q : ℕ)) =>
            (fun u : Fin t → ZMod (q : ℕ) =>
              ∀ i, (q : ℕ) ∣ M i → thetaMod W A b (q : ℕ) i u = 0)
              (fun j => ZMod.castHom (hpe q) (ZMod (q : ℕ)) (y j)))) := by
      apply Finset.filter_congr
      intro y _
      simp only [locC, castHom_thetaMod W A b (hpe q)]
    have hdiv : (q : ℕ) ^ D.factorization (q : ℕ) / (q : ℕ)
        = (q : ℕ) ^ (D.factorization (q : ℕ) - 1) := by
      have hmul : (q : ℕ) ^ (D.factorization (q : ℕ) - 1) * (q : ℕ)
          = (q : ℕ) ^ D.factorization (q : ℕ) := by
        simpa using Nat.pow_sub_mul_pow (a := (q : ℕ)) hq1
      rw [← hmul, Nat.mul_div_cancel _ hqprime.pos]
    rw [hfil, hfib, hdiv, pow_mul]
    rfl
  refine Eq.trans hstep1 ?_
  refine Eq.trans (Finset.prod_congr rfl (fun q _ => hstep2 q)) ?_
  rw [Finset.univ_eq_attach]

end Commons.NumberTheory.Sieve
