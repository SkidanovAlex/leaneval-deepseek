import Mathlib
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

/-!
# `Work.MotAS.satGraphIsPrimeGen`

The ideal `(E(X₁,X₂), D(X₁,X₂)·X₀ + R(X₁,X₂)) ⊆ K[X₀,X₁,X₂]` is *prime after inverting `D`*: the
saturation `{F | ∃ N, D^N · F ∈ (E, D·X₀ + R)}` is a prime ideal, whenever `E` is irreducible and
`E ∤ D`.

The proof exhibits the saturated ideal as the kernel of a ring homomorphism into a field.  The
quotient `A := K[X₁,X₂]/(E)` is a domain (as `E` is irreducible), and in the fraction field `L`
of `A` the element `D` is invertible (`E ∤ D`).  The graph relation `D·X₀ + R = 0` then reads
`X₀ = −R/D`, so the ring homomorphism

`ψ : K[X₀,X₁,X₂] → L`,  `X₁ ↦ X₁`, `X₂ ↦ X₂`, `X₀ ↦ −σ R · (σ D)⁻¹`

has kernel precisely the saturation.  The bulk of the work is the polynomial descent lemma
`descent_aux` (an analogue of the usual "`X₂`-saturation" argument, with the polynomial variable
`X₀`), which identifies the kernel of the `(K[X₁,X₂])[X₀]`-evaluation with the saturation of
`(C D · X − C b, C E)`.
-/

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.MotAS

/-- In `R[X]`, the monomial congruence modulo `(C a * X - C b)`: for `k ≤ m`,
`C a ^ (k + n) * X ^ k ≡ C (a ^ n * b ^ k)` with `m = k + n`. -/
private lemma mono_mem {R : Type*} [CommRing R] (a b : R) :
    ∀ (k n : ℕ), Polynomial.C a ^ (k + n) * Polynomial.X ^ k -
        Polynomial.C (a ^ n * b ^ k) ∈
      Ideal.span {Polynomial.C a * Polynomial.X - Polynomial.C b} := by
  intro k
  induction k with
  | zero =>
      intro n
      have h : Polynomial.C a ^ (0 + n) * Polynomial.X ^ 0 - Polynomial.C (a ^ n * b ^ 0) = 0 := by
        rw [zero_add, pow_zero, mul_one, pow_zero, mul_one, ← map_pow, sub_self]
      rw [h]
      exact Ideal.zero_mem _
  | succ k ih =>
      intro n
      have hP : Polynomial.C a * Polynomial.X - Polynomial.C b ∈
          Ideal.span {Polynomial.C a * Polynomial.X - Polynomial.C b} :=
        Ideal.subset_span (Set.mem_singleton _)
      have hd : Polynomial.C a ^ (k + n) * Polynomial.X ^ k - Polynomial.C (a ^ n * b ^ k) ∈
          Ideal.span {Polynomial.C a * Polynomial.X - Polynomial.C b} := ih n
      have hstep : Polynomial.C a ^ (k + 1 + n) * Polynomial.X ^ (k + 1)
          = (Polynomial.C a ^ (k + n) * Polynomial.X ^ k) * (Polynomial.C a * Polynomial.X) := by
        rw [show k + 1 + n = k + n + 1 by omega, pow_succ]
        first | refl_ring1 | ring
      have hb : Polynomial.C (a ^ n * b ^ (k + 1))
          = Polynomial.C (a ^ n * b ^ k) * Polynomial.C b := by
        rw [pow_succ, show a ^ n * (b ^ k * b) = (a ^ n * b ^ k) * b by rw [← mul_assoc],
          Polynomial.C_mul]
      have key : Polynomial.C a ^ (k + 1 + n) * Polynomial.X ^ (k + 1) -
            Polynomial.C (a ^ n * b ^ (k + 1))
          = (Polynomial.C a ^ (k + n) * Polynomial.X ^ k) *
              (Polynomial.C a * Polynomial.X - Polynomial.C b)
            + Polynomial.C b * (Polynomial.C a ^ (k + n) * Polynomial.X ^ k -
                Polynomial.C (a ^ n * b ^ k)) := by
        rw [hstep, hb]
        first | refl_ring1 | ring
      rw [key]
      exact Ideal.add_mem _
        (Ideal.mul_mem_left _ (Polynomial.C a ^ (k + n) * Polynomial.X ^ k) hP)
        (Ideal.mul_mem_left _ (Polynomial.C b) hd)

/-- The congruence for an arbitrary finite sum of monomials. -/
private lemma sum_congruence {R : Type*} [CommRing R] (a b : R) :
    ∀ (s : Finset ℕ) (c : ℕ → R) (m : ℕ), (∀ k ∈ s, k ≤ m) →
      Polynomial.C a ^ m * (s.sum (fun k => Polynomial.C (c k) * Polynomial.X ^ k)) -
        Polynomial.C (s.sum (fun k => c k * a ^ (m - k) * b ^ k)) ∈
      Ideal.span {Polynomial.C a * Polynomial.X - Polynomial.C b} := by
  intro s
  induction s using Finset.induction_on with
  | empty =>
      intro c m _
      rw [Finset.sum_empty, Finset.sum_empty, mul_zero, map_zero, sub_zero]
      exact Ideal.zero_mem _
  | insert k s hk ih =>
      intro c m hm
      have hk_le : k ≤ m := hm k (Finset.mem_insert_self k s)
      have ih' : Polynomial.C a ^ m * (s.sum (fun j => Polynomial.C (c j) * Polynomial.X ^ j)) -
            Polynomial.C (s.sum (fun j => c j * a ^ (m - j) * b ^ j)) ∈
          Ideal.span {Polynomial.C a * Polynomial.X - Polynomial.C b} :=
        ih c m (fun j hj => hm j (Finset.mem_insert_of_mem hj))
      have hmono : Polynomial.C a ^ m * Polynomial.X ^ k - Polynomial.C (a ^ (m - k) * b ^ k) ∈
          Ideal.span {Polynomial.C a * Polynomial.X - Polynomial.C b} := by
        have h2 := mono_mem a b k (m - k)
        rwa [Nat.add_sub_cancel' hk_le] at h2
      have hmono' : Polynomial.C (c k) * (Polynomial.C a ^ m * Polynomial.X ^ k) -
            Polynomial.C (c k * a ^ (m - k) * b ^ k) ∈
          Ideal.span {Polynomial.C a * Polynomial.X - Polynomial.C b} := by
        have h3 := Ideal.mul_mem_left _ (Polynomial.C (c k)) hmono
        have e : Polynomial.C (c k) *
              (Polynomial.C a ^ m * Polynomial.X ^ k - Polynomial.C (a ^ (m - k) * b ^ k))
            = Polynomial.C (c k) * (Polynomial.C a ^ m * Polynomial.X ^ k) -
              Polynomial.C (c k * a ^ (m - k) * b ^ k) := by
          rw [mul_sub, ← map_mul,
            show c k * (a ^ (m - k) * b ^ k) = c k * a ^ (m - k) * b ^ k by rw [← mul_assoc]]
        rwa [e] at h3
      rw [Finset.sum_insert hk, Finset.sum_insert hk]
      have key : Polynomial.C a ^ m * (Polynomial.C (c k) * Polynomial.X ^ k +
              s.sum (fun j => Polynomial.C (c j) * Polynomial.X ^ j)) -
            Polynomial.C (c k * a ^ (m - k) * b ^ k +
              s.sum (fun j => c j * a ^ (m - j) * b ^ j))
          = (Polynomial.C (c k) * (Polynomial.C a ^ m * Polynomial.X ^ k) -
              Polynomial.C (c k * a ^ (m - k) * b ^ k)) +
            (Polynomial.C a ^ m * s.sum (fun j => Polynomial.C (c j) * Polynomial.X ^ j) -
              Polynomial.C (s.sum (fun j => c j * a ^ (m - j) * b ^ j))) := by
        rw [map_add, map_mul, map_mul]
        first | refl_ring1 | ring
      rw [key]
      exact Ideal.add_mem _ hmono' ih'

/-- The polynomial congruence: for `m ≥ f.natDegree`,
`C a ^ m * f ≡ C (∑_k f_k a ^ (m - k) b ^ k)` modulo `(C a * X - C b)`. -/
private lemma C_pow_mul_sub_sum_mem {R : Type*} [CommRing R] (a b : R) (f : Polynomial R) (m : ℕ)
    (hm : f.natDegree ≤ m) :
    Polynomial.C a ^ m * f -
      Polynomial.C (f.support.sum (fun k => f.coeff k * a ^ (m - k) * b ^ k)) ∈
      Ideal.span {Polynomial.C a * Polynomial.X - Polynomial.C b} := by
  have hf : f.support.sum (fun k => Polynomial.C (f.coeff k) * Polynomial.X ^ k) = f := by
    have h := Polynomial.sum_C_mul_X_pow_eq f
    rw [Polynomial.sum_def] at h
    exact h
  have hmem := sum_congruence a b f.support (fun k => f.coeff k) m
    (fun k hk => (Polynomial.le_natDegree_of_mem_supp k hk).trans hm)
  rwa [hf] at hmem

/-- **The polynomial descent lemma.**  Let `σ : R →+* D` with `σ a` inverted by `u`, and suppose
`σ` has kernel exactly `(G)`.  Then for the evaluation `Φ = eval₂ σ (σ b · u)`,
`Φ f = 0` holds iff some `a`-power multiple of `f` lies in `(C a * X - C b, C G)`. -/
private lemma descent_aux {R D : Type*} [CommRing R] [CommRing D] (σ : R →+* D)
    (a b G : R) (u : D) (hu : σ a * u = 1)
    (hker : ∀ x : R, σ x = 0 ↔ x ∈ Ideal.span {G}) :
    ∀ f : Polynomial R,
      Polynomial.eval₂RingHom σ (σ b * u) f = 0 ↔
        ∃ m : ℕ, Polynomial.C a ^ m * f ∈
          Ideal.span {Polynomial.C a * Polynomial.X - Polynomial.C b, Polynomial.C G} := by
  intro f
  let Φ : Polynomial R →+* D := Polynomial.eval₂RingHom σ (σ b * u)
  have hCa : Φ (Polynomial.C a) = σ a := Polynomial.eval₂_C σ (σ b * u)
  have hCG : Φ (Polynomial.C G) = 0 := by
    have h : Φ (Polynomial.C G) = σ G := Polynomial.eval₂_C σ (σ b * u)
    rw [h, (hker G).mpr (Ideal.subset_span (Set.mem_singleton G))]
  have hP : Φ (Polynomial.C a * Polynomial.X - Polynomial.C b) = 0 := by
    have hX : Φ (Polynomial.X) = σ b * u := Polynomial.eval₂_X σ (σ b * u)
    have hCb : Φ (Polynomial.C b) = σ b := Polynomial.eval₂_C σ (σ b * u)
    rw [map_sub, map_mul, hCa, hX, hCb]
    have hcomm : σ a * (σ b * u) = σ b := by
      rw [← mul_assoc, mul_comm (σ a) (σ b), mul_assoc, hu, mul_one]
    rw [hcomm, sub_self]
  -- the ideal of the conclusion is contained in `ker Φ`
  have hspan_le : Ideal.span {Polynomial.C a * Polynomial.X - Polynomial.C b, Polynomial.C G} ≤
      RingHom.ker Φ := by
    rw [Ideal.span_le]
    intro x hx
    rw [Set.mem_insert_iff] at hx
    rcases hx with hx | hx
    · subst hx
      exact RingHom.mem_ker.mpr hP
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact RingHom.mem_ker.mpr hCG
  have hsub : Ideal.span {Polynomial.C a * Polynomial.X - Polynomial.C b} ≤
      Ideal.span {Polynomial.C a * Polynomial.X - Polynomial.C b, Polynomial.C G} := by
    refine Ideal.span_le.mpr ?_
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact Ideal.subset_span (Set.mem_insert _ _)
  change Φ f = 0 ↔ _
  constructor
  · intro hf
    refine ⟨f.natDegree, ?_⟩
    have hcong := C_pow_mul_sub_sum_mem a b f f.natDegree le_rfl
    set r : R := f.support.sum (fun k => f.coeff k * a ^ (f.natDegree - k) * b ^ k) with hr
    have hmem1 : Polynomial.C a ^ f.natDegree * f - Polynomial.C r ∈
        Ideal.span {Polynomial.C a * Polynomial.X - Polynomial.C b} := by
      rw [hr]
      exact hcong
    have hmem2 : Polynomial.C a ^ f.natDegree * f - Polynomial.C r ∈
        Ideal.span {Polynomial.C a * Polynomial.X - Polynomial.C b, Polynomial.C G} :=
      hsub hmem1
    have hker1 : Φ (Polynomial.C a ^ f.natDegree * f - Polynomial.C r) = 0 :=
      RingHom.mem_ker.mp (hspan_le hmem2)
    have hbig : Φ (Polynomial.C a ^ f.natDegree * f) = 0 := by
      rw [map_mul, map_pow, hCa, hf, mul_zero]
    have hCr0 : Φ (Polynomial.C r) = 0 := by
      have h3 : Φ (Polynomial.C r) = Φ (Polynomial.C a ^ f.natDegree * f) -
          Φ (Polynomial.C a ^ f.natDegree * f - Polynomial.C r) := by
        rw [map_sub]
        first | refl_ring1 | ring
      rw [h3, hbig, hker1, sub_zero]
    have h4 : Φ (Polynomial.C r) = σ r := Polynomial.eval₂_C σ (σ b * u)
    have hr0 : σ r = 0 := by
      rw [← h4]
      exact hCr0
    have hrG : r ∈ Ideal.span {G} := (hker r).mp hr0
    have hCr : Polynomial.C r ∈ Ideal.span {Polynomial.C G} := by
      rw [Ideal.mem_span_singleton] at hrG ⊢
      exact map_dvd Polynomial.C hrG
    rw [show Ideal.span {Polynomial.C a * Polynomial.X - Polynomial.C b, Polynomial.C G}
        = Ideal.span {Polynomial.C a * Polynomial.X - Polynomial.C b} ⊔
          Ideal.span {Polynomial.C G} from
        Ideal.span_insert (Polynomial.C a * Polynomial.X - Polynomial.C b) {Polynomial.C G}]
    have heq : Polynomial.C a ^ f.natDegree * f =
        (Polynomial.C a ^ f.natDegree * f - Polynomial.C r) + Polynomial.C r := by ring
    rw [heq]
    exact Ideal.add_mem _ (Submodule.mem_sup_left hmem1) (Submodule.mem_sup_right hCr)
  · rintro ⟨m, hm⟩
    have hm2 : Φ (Polynomial.C a ^ m * f) = 0 := by
      have h := hspan_le hm
      exact RingHom.mem_ker.mp h
    rw [map_mul, map_pow, hCa] at hm2
    have hu' : σ a ^ m * u ^ m = 1 := by rw [← mul_pow, hu, one_pow]
    calc Φ f = 1 * Φ f := (one_mul _).symm
      _ = (σ a ^ m * u ^ m) * Φ f := by rw [hu']
      _ = u ^ m * (σ a ^ m * Φ f) := by ring
      _ = 0 := by rw [hm2, mul_zero]

/-- **The graph saturation is prime.**  For `E` irreducible and `E ∤ D`, the saturation

`{F ∈ K[X₀,X₁,X₂] | ∃ N, D(X₁,X₂)^N · F ∈ (E(X₁,X₂), D(X₁,X₂)·X₀ + R(X₁,X₂))}`

is a prime ideal. -/
theorem satGraphIsPrimeGen {K : Type*} [Field K]
    (E D R : MvPolynomial (Fin 2) K) (hE : Irreducible E) (hD : ¬ E ∣ D) :
    (Ideal.span {F : MvPolynomial (Fin 3) K |
        ∃ N : ℕ, (MvPolynomial.rename Fin.succ D) ^ N * F ∈
          Ideal.span {MvPolynomial.rename Fin.succ E,
            MvPolynomial.rename Fin.succ D * MvPolynomial.X 0
              + MvPolynomial.rename Fin.succ R}}).IsPrime := by
  classical
  have hE0 : E ≠ 0 := hE.ne_zero
  have hEprime : Prime E := hE.prime
  haveI hIprime : (Ideal.span {E} : Ideal (MvPolynomial (Fin 2) K)).IsPrime :=
    (Ideal.span_singleton_prime hE0).mpr hEprime
  haveI hCdom : IsDomain (MvPolynomial (Fin 2) K ⧸ Ideal.span {E}) :=
    Ideal.Quotient.isDomain (Ideal.span {E})
  haveI hDfield : Field (FractionRing (MvPolynomial (Fin 2) K ⧸ Ideal.span {E})) :=
    FractionRing.field _
  -- the quotient map `σ : K[X₁,X₂] →+* L = Frac(K[X₁,X₂]/(E))`, which has kernel `(E)`
  let σ : MvPolynomial (Fin 2) K →+*
      FractionRing (MvPolynomial (Fin 2) K ⧸ Ideal.span {E}) :=
    (algebraMap (MvPolynomial (Fin 2) K ⧸ Ideal.span {E})
        (FractionRing (MvPolynomial (Fin 2) K ⧸ Ideal.span {E}))).comp
      (Ideal.Quotient.mk (Ideal.span {E}))
  have hkerσ : ∀ x : MvPolynomial (Fin 2) K, σ x = 0 ↔ x ∈ Ideal.span {E} := by
    intro x
    change (algebraMap (MvPolynomial (Fin 2) K ⧸ Ideal.span {E})
        (FractionRing (MvPolynomial (Fin 2) K ⧸ Ideal.span {E})))
        (Ideal.Quotient.mk (Ideal.span {E}) x) = 0 ↔ x ∈ Ideal.span {E}
    rw [map_eq_zero_iff _ (IsFractionRing.injective _ _), Ideal.Quotient.eq_zero_iff_mem]
  -- `E ∤ D` makes `σ D` invertible
  have hσD : σ D ≠ 0 := by
    intro h0
    exact hD (Ideal.mem_span_singleton.mp ((hkerσ D).mp h0))
  let u : FractionRing (MvPolynomial (Fin 2) K ⧸ Ideal.span {E}) := (σ D)⁻¹
  have hu : σ D * u = 1 := mul_inv_cancel₀ hσD
  -- the abstract descent lemma, with `a := D`, `b := −R`, `G := E`
  have hdescent := descent_aux σ D (-R) E u hu hkerσ
  -- the identification `K[X₀,X₁,X₂] ≅ (K[X₁,X₂])[X₀]`
  let e : MvPolynomial (Fin 3) K ≃ₐ[K] Polynomial (MvPolynomial (Fin 2) K) :=
    MvPolynomial.finSuccEquiv K 2
  have he_rename : ∀ p : MvPolynomial (Fin 2) K,
      (e : MvPolynomial (Fin 3) K →+* Polynomial (MvPolynomial (Fin 2) K))
        (MvPolynomial.rename Fin.succ p) = Polynomial.C p := by
    have hcomp : ((e : MvPolynomial (Fin 3) K →+*
        Polynomial (MvPolynomial (Fin 2) K)).comp
        (MvPolynomial.rename Fin.succ).toRingHom) = Polynomial.C := by
      apply MvPolynomial.ringHom_ext
      · intro r
        show e ((MvPolynomial.rename Fin.succ) (MvPolynomial.C r))
            = Polynomial.C (MvPolynomial.C r)
        rw [MvPolynomial.rename_C, ← MvPolynomial.algebraMap_eq (R := K) (σ := Fin 3),
          AlgEquiv.commutes e r, ← MvPolynomial.algebraMap_eq (R := K) (σ := Fin 2)]
        exact (AlgHom.commutes (Polynomial.CAlgHom (R := K) (A := MvPolynomial (Fin 2) K)) r).symm
      · intro i
        show e ((MvPolynomial.rename Fin.succ) (MvPolynomial.X i))
            = Polynomial.C (MvPolynomial.X i)
        rw [MvPolynomial.rename_X, MvPolynomial.finSuccEquiv_X_succ]
    intro p
    exact RingHom.congr_fun hcomp p
  have heX0 : (e : MvPolynomial (Fin 3) K →+* Polynomial (MvPolynomial (Fin 2) K))
      (MvPolynomial.X 0 : MvPolynomial (Fin 3) K) = Polynomial.X := by
    simpa using MvPolynomial.finSuccEquiv_X_zero (R := K) (n := 2)
  -- the ideal `J` of the statement, and its image in the polynomial world
  set J : Ideal (MvPolynomial (Fin 3) K) :=
    Ideal.span {MvPolynomial.rename Fin.succ E,
      MvPolynomial.rename Fin.succ D * MvPolynomial.X 0 + MvPolynomial.rename Fin.succ R}
    with hJdef
  have hgen1 : (e : MvPolynomial (Fin 3) K →+* Polynomial (MvPolynomial (Fin 2) K))
      (MvPolynomial.rename Fin.succ D * MvPolynomial.X 0 + MvPolynomial.rename Fin.succ R)
      = Polynomial.C D * Polynomial.X - Polynomial.C (-R) := by
    rw [map_add, map_mul, he_rename D, heX0, he_rename R, map_neg, sub_neg_eq_add]
  have hgen2 : (e : MvPolynomial (Fin 3) K →+* Polynomial (MvPolynomial (Fin 2) K))
      (MvPolynomial.rename Fin.succ E) = Polynomial.C E := he_rename E
  have hJmap : Ideal.map (e : MvPolynomial (Fin 3) K →+*
        Polynomial (MvPolynomial (Fin 2) K)) J
      = Ideal.span {Polynomial.C D * Polynomial.X - Polynomial.C (-R), Polynomial.C E} := by
    rw [hJdef, Ideal.map_span, Set.image_pair, hgen2, hgen1]
    congr 1
    exact Set.pair_comm _ _
  -- the graph evaluation into the field `L`
  let Φ : Polynomial (MvPolynomial (Fin 2) K) →+*
      FractionRing (MvPolynomial (Fin 2) K ⧸ Ideal.span {E}) :=
    Polynomial.eval₂RingHom σ (σ (-R) * u)
  let ψ : MvPolynomial (Fin 3) K →+*
      FractionRing (MvPolynomial (Fin 2) K ⧸ Ideal.span {E}) :=
    Φ.comp (e : MvPolynomial (Fin 3) K →+* Polynomial (MvPolynomial (Fin 2) K))
  have hdescent' : ∀ f : Polynomial (MvPolynomial (Fin 2) K),
      Φ f = 0 ↔ ∃ m : ℕ, Polynomial.C D ^ m * f ∈
        Ideal.span {Polynomial.C D * Polynomial.X - Polynomial.C (-R), Polynomial.C E} :=
    fun f => hdescent f
  have hψapply : ∀ F : MvPolynomial (Fin 3) K,
      ψ F = Φ ((e : MvPolynomial (Fin 3) K →+* Polynomial (MvPolynomial (Fin 2) K)) F) :=
    fun F => rfl
  have hΦC : ∀ m : MvPolynomial (Fin 2) K, Φ (Polynomial.C m) = σ m :=
    fun m => Polynomial.eval₂_C σ (σ (-R) * u)
  have hΦX : Φ Polynomial.X = σ (-R) * u := Polynomial.eval₂_X σ (σ (-R) * u)
  -- `ψ` kills the two generators of `J`
  have hΦgen1 : Φ (Polynomial.C D * Polynomial.X - Polynomial.C (-R)) = 0 := by
    have hmul : Φ (Polynomial.C D * Polynomial.X) = σ D * (σ (-R) * u) := by
      rw [map_mul, hΦC D, hΦX]
    have hCR : Φ (Polynomial.C (-R)) = σ (-R) := hΦC (-R)
    rw [map_sub, hmul, hCR]
    have hz : σ D * (σ (-R) * u) = σ (-R) := by
      rw [← mul_assoc, mul_comm (σ D) (σ (-R)), mul_assoc, hu, mul_one]
    rw [hz, sub_self]
  have hΦgen2 : Φ (Polynomial.C E) = 0 := by
    rw [hΦC E]
    exact (hkerσ E).mpr (Ideal.subset_span (Set.mem_singleton E))
  have hψgen1 : ψ (MvPolynomial.rename Fin.succ D * MvPolynomial.X 0
      + MvPolynomial.rename Fin.succ R) = 0 := by
    rw [hψapply, hgen1]
    exact hΦgen1
  have hψgen2 : ψ (MvPolynomial.rename Fin.succ E) = 0 := by
    rw [hψapply, hgen2]
    exact hΦgen2
  have hJ_le : J ≤ RingHom.ker ψ := by
    rw [hJdef, Ideal.span_le]
    intro x hx
    rw [Set.mem_insert_iff] at hx
    rcases hx with hx | hx
    · subst hx
      exact RingHom.mem_ker.mpr hψgen2
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact RingHom.mem_ker.mpr hψgen1
  -- `ψ`'s value on `rename Fin.succ D`
  have hψD : ψ (MvPolynomial.rename Fin.succ D) = σ D := by
    rw [hψapply, he_rename D]
    exact hΦC D
  -- the kernel of `ψ` is exactly the saturation
  have hiff : ∀ F : MvPolynomial (Fin 3) K,
      ψ F = 0 ↔ ∃ N : ℕ, (MvPolynomial.rename Fin.succ D) ^ N * F ∈ J := by
    intro F
    have hpow : ∀ N : ℕ, Polynomial.C D ^ N *
        (e : MvPolynomial (Fin 3) K →+* Polynomial (MvPolynomial (Fin 2) K)) F
        = (e : MvPolynomial (Fin 3) K →+* Polynomial (MvPolynomial (Fin 2) K))
            ((MvPolynomial.rename Fin.succ D) ^ N * F) := by
      intro N
      rw [map_mul, map_pow, he_rename D]
    rw [hψapply F, hdescent' ((e : MvPolynomial (Fin 3) K →+* Polynomial (MvPolynomial (Fin 2) K)) F)]
    constructor
    · rintro ⟨m, hm⟩
      rw [hpow m, ← hJmap] at hm
      obtain ⟨x, hxJ, hx⟩ := (Ideal.mem_map_iff_of_surjective
        (e : MvPolynomial (Fin 3) K →+* Polynomial (MvPolynomial (Fin 2) K))
        e.surjective).mp hm
      exact ⟨m, by rw [← e.injective hx]; exact hxJ⟩
    · rintro ⟨N, hN⟩
      exact ⟨N, by
        rw [hpow N, ← hJmap]
        exact (Ideal.mem_map_iff_of_surjective
          (e : MvPolynomial (Fin 3) K →+* Polynomial (MvPolynomial (Fin 2) K))
          e.surjective).mpr ⟨_, hN, rfl⟩⟩
  have hS_le : Ideal.span {F : MvPolynomial (Fin 3) K |
        ∃ N : ℕ, (MvPolynomial.rename Fin.succ D) ^ N * F ∈ J} ≤ RingHom.ker ψ := by
    rw [Ideal.span_le]
    rintro F ⟨N, hN⟩
    refine RingHom.mem_ker.mpr ?_
    have hJmem : ψ ((MvPolynomial.rename Fin.succ D) ^ N * F) = 0 :=
      RingHom.mem_ker.mp (hJ_le hN)
    rw [map_mul, map_pow, hψD] at hJmem
    exact (mul_eq_zero.mp hJmem).resolve_left (pow_ne_zero N hσD)
  have hker_le : RingHom.ker ψ ≤ Ideal.span {F : MvPolynomial (Fin 3) K |
        ∃ N : ℕ, (MvPolynomial.rename Fin.succ D) ^ N * F ∈ J} := by
    intro F hF
    rw [RingHom.mem_ker] at hF
    exact Ideal.subset_span ((hiff F).mp hF)
  have hkerprime : (RingHom.ker ψ).IsPrime := RingHom.ker_isPrime ψ
  rw [le_antisymm hS_le hker_le]
  exact hkerprime

end Work.MotAS
