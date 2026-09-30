import Mathlib
import Submission.Work.BW.DefsMult
import Submission.Work.BW.RB.A4
import Submission.Work.BW.rayDeg_hyperplane
import Submission.Work.BW.rayDeg_additive
import Submission.Work.BW.rayDeg_mono
import Submission.Work.BW.rayDim_lt_of_lt
import Submission.Work.BW.rayDeg_bot
import Submission.Work.BW.multiHom_assPrime
import Submission.Work.BW.OnGPrime_iff
import Submission.Work.BW.hilb_serre_input
import Submission.Work.BW.RB.Basic
import Submission.Work.BW.RB.height_minimalPrimes_sup_span_singleton
import Submission.Work.BW.RB.maximal_height_eq_ringKrullDim
import Submission.Work.BW.RB.multiHom_minimalPrimes
import Submission.Work.BW.RB.cut_homPiece_exists
import Submission.Work.BW.RB.srelcut_rayHilb_pos
import Submission.Work.BW.RB.srelcut_diagonal_c
import Submission.Work.BW.RB.srelcut_prime_le_diagonal


set_option linter.style.haveILetI false

namespace Work.BW.RB

open MvPolynomial

noncomputable section

/-!
# The one-step cut of `Srel` by a prime

`Srel N D J = ∑_{q ∈ Min J, q admissible} length_J(q) · H(q; D)` is Philippon's `S^𝒰 H(J; D)`
(the sum of `length × rayDeg` over the minimal primes of `J` meeting the cone over
`G = G_a × G_m^N`).  The main result here is that cutting a **prime** `p` by a multihomogeneous
element `P` of multidegree exactly `D` with `P ∉ p` does not increase `Srel`:

  `Srel N D (p ⊔ (P)) ≤ Srel N D p`.

The proof has three layers.

* `srelcut_chain` (adapted from `Submission.Work.BW.RB.srelcut_rayDim_add_height_le`, re-proved here
  because that module imports the `rayHilb_final` cluster, which is incompatible with the
  `rayDeg_additive` cluster used below): along a strictly increasing chain of multihomogeneous
  primes `r < s` whose `s` avoids the diagonal monomials `∏ X_{i,0}^{t·D_i}`, the ray dimension
  drops by at least the height difference, `rayDim s + m ≤ rayDim r`.

* This yields the dimension formula `rayDim p = N + 1 - ht p` for an admissible prime
  (`rayDim_eq_card_sub_height_adm`): the upper bound comes from the chain `⊥ ≤ p`, the lower bound
  from the chain `p ≤ diagIdeal y` where `y` witnesses admissibility
  (`srelcut_prime_le_diagonal`, `diagIdeal_isPrime`, `diagIdeal_height`).

* Consequently every admissible minimal prime of `J = p ⊔ (P)` is *top-dimensional* in `J`
  (`admissible_minimalPrimes_top`: all minimal primes of `J` have height `ht p + 1`), so the sum of
  `length × rayDeg` over the admissible minimal primes is at most the corresponding sum over the
  top-dimensional minimal primes, which is `rayDeg J = rayDeg p`
  (`rayDeg_additive`, `rayDeg_hyperplane`, `srel_self_of_isPrime`).
-/




open MvPolynomial

/-!
# The "srel cut" dimension inequality

Let `R = MR N = ℂ[X_{ij}]` be the coordinate ring of `(P¹)^{N+1}` with its multigrading,
`D : Fin (N+1) →₀ ℕ` with `Dᵢ ≥ 1`, and let `r ≤ s` be multihomogeneous primes of `R` such that
none of the "diagonal" monomials `∏ᵢ X_{i,0}^{t Dᵢ}` lies in `s`.  If the heights differ by `m`,
then the ray dimensions (the degrees of the ray Hilbert polynomials, i.e. the dimensions of the
multiprojective varieties `Z(r) ⊇ Z(s)`) differ by at least `m`:

  `rayDim N D s + m ≤ rayDim N D r`.

The proof does not use the absolute dimension formula `rayDim = N+1-ht`; it uses instead the
*strict* drop `Work.BW.rayDim_lt_of_lt` along a single step of a chain of multihomogeneous primes,
and builds that chain step by step: given `r < s`, cut `r` by a multihomogeneous polynomial `P`
of multidegree `k • D` lying in `s` (multiplying a multihomogeneous component of an element of
`s \ r` by a suitable power of the "diagonal" monomial: `Work.BW.RB.cut_homPiece_exists`), and take
a minimal prime `q` of `r + (P)` contained in `s`.  Then `ht q = ht r + 1`, `q` is multihomogeneous again, and
`rayDim N D q < rayDim N D r`; induction on `m` finishes.

The hypothesis on the diagonal monomials is used twice.

* Multiplying a homogeneous component `g` of multidegree `d` of an element of `s \ r` by
  `∏ᵢ X_{i,0}^{k Dᵢ - dᵢ}` reaches the multidegree `k • D` and stays outside `r`; for this we need
  each `X_{i,0} ∉ r`.
* For every intermediate prime `q ⊆ s` the class of `∏ᵢ X_{i,0}^{t Dᵢ}` survives in `(R/q)_{tD}`,
  so `rayHilb ≥ 1` and the ray Hilbert polynomial of `q` is nonzero — which is what
  `rayDim_lt_of_lt` needs.
-/

variable {N : ℕ}

/-! ## The diagonal monomial `∏ᵢ X_{i,0}^{t Dᵢ}` -/

/-- The monomial `∏ᵢ X_{i,0}^{t Dᵢ}`, of multidegree `t • D`; it is nonzero at every point of the
chart on which all `X_{i,0} ≠ 0`. -/
noncomputable def srelDiagMono (N : ℕ) (D : Fin (N + 1) →₀ ℕ) (t : ℕ) : MR N :=
  ∏ i : Fin (N + 1), (MvPolynomial.X (i, 0) : MR N) ^ (t * D i)

/-! ## Elementary multidegree bookkeeping -/

private lemma mdeg_apply_srel (v : Fin (N + 1) × Fin 2) (i : Fin (N + 1)) :
    mdeg N v i = if v.1 = i then 1 else 0 := by
  by_cases h : v.1 = i <;> simp [mdeg, h]

private lemma sum_smul_mdeg_apply_srel (a : Fin (N + 1) → ℕ) (j : Fin (N + 1) → Fin 2)
    (i : Fin (N + 1)) :
    (∑ i' : Fin (N + 1), a i' • mdeg N (i', j i')) i = a i := by
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · rw [Finsupp.smul_apply, mdeg_apply_srel, ite_eq_left rfl, smul_eq_mul, mul_one]
  · intro i' _ hne
    rw [Finsupp.smul_apply, mdeg_apply_srel, ite_eq_right hne, smul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

/-- A positive power of an element of an ideal lies in the ideal. -/
private lemma pow_mem_of_mem_of_pos {I : Ideal (MR N)} {x : MR N} (hx : x ∈ I) {n : ℕ}
    (hn : 1 ≤ n) : x ^ n ∈ I := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  rw [pow_succ]
  exact Ideal.mul_mem_left I (x ^ k) hx

/-! ## The diagonal monomial lies in the expected multihomogeneous piece -/

private lemma srelDiagMono_mem_homPiece (D : Fin (N + 1) →₀ ℕ) (t : ℕ) :
    srelDiagMono N D t ∈ homPiece N (t • D) := by
  rw [srelDiagMono, rb_mem_homPiece_iff]
  have hhom : MvPolynomial.IsWeightedHomogeneous (mdeg N)
      (∏ i : Fin (N + 1), (MvPolynomial.X (i, 0) : MR N) ^ (t * D i))
      (∑ i : Fin (N + 1), (t * D i) • mdeg N (i, 0)) :=
    MvPolynomial.IsWeightedHomogeneous.prod Finset.univ
      (fun i : Fin (N + 1) => (MvPolynomial.X (i, 0) : MR N) ^ (t * D i))
      (fun i : Fin (N + 1) => (t * D i) • mdeg N (i, 0))
      (fun i _ => (MvPolynomial.isWeightedHomogeneous_X ℂ (mdeg N) (i, 0)).pow (t * D i))
  have hdeg : (∑ i : Fin (N + 1), (t * D i) • mdeg N (i, 0)) = t • D := by
    ext i
    rw [sum_smul_mdeg_apply_srel, Finsupp.smul_apply, smul_eq_mul]
  rwa [hdeg] at hhom

/-! ## Positivity of the ray Hilbert function, and nonvanishing of the ray polynomial -/

/-- If no diagonal monomial vanishes modulo `I`, the ray Hilbert function of `I` is positive in
every degree: the class of `∏ᵢ X_{i,0}^{t Dᵢ}` survives in `(R/I)_{tD}`. -/
private lemma rayHilb_pos_of_srelDiagMono (D : Fin (N + 1) →₀ ℕ) (I : Ideal (MR N))
    (h : ∀ t : ℕ, srelDiagMono N D t ∉ I) (t : ℕ) : 1 ≤ rayHilb N D I t := by
  have hmem : srelDiagMono N D t ∈ homPiece N (t • D) := srelDiagMono_mem_homPiece D t
  have hnot : srelDiagMono N D t ∉ I := h t
  have hneq : (Submodule.Quotient.mk (p := Submodule.comap (homPiece N (t • D)).subtype
        (I.restrictScalars ℂ)) ⟨srelDiagMono N D t, hmem⟩ :
        ↥(homPiece N (t • D)) ⧸
          Submodule.comap (homPiece N (t • D)).subtype (I.restrictScalars ℂ)) ≠ 0 := by
    intro hzero
    rw [Submodule.Quotient.mk_eq_zero] at hzero
    exact hnot (by simpa [Submodule.mem_comap] using hzero)
  haveI : Module.Finite ℂ ↥(homPiece N (t • D)) := rayHilb_finite N (t • D)
  have hnt : Nontrivial (↥(homPiece N (t • D)) ⧸
      Submodule.comap (homPiece N (t • D)).subtype (I.restrictScalars ℂ)) :=
    nontrivial_of_ne _ _ hneq
  have hpos : 0 < rayHilb N D I t := by
    rw [rayHilb]
    exact Module.finrank_pos
  omega

/-- Consequently the ray Hilbert polynomial is nonzero. -/
private lemma rayPoly_ne_zero_of_srelDiagMono (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (I : Ideal (MR N)) (hI : MultiHom N I) (h : ∀ t : ℕ, srelDiagMono N D t ∉ I) :
    rayPoly N D I ≠ 0 := by
  set q := rayPoly N D I with hqdef
  have hq : IsRayPoly N D I q := by
    rw [hqdef]
    exact isRayPoly_rayPoly (hilb_serre_input N) D hD I hI
  intro hq0
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hq
  have h1 : ((rayHilb N D I (max a 1) : ℕ) : ℚ) = q.eval ((max a 1 : ℕ) : ℚ) :=
    ha _ (le_max_left _ _)
  rw [hq0] at h1
  simp at h1
  have h2 : 1 ≤ rayHilb N D I (max a 1) := rayHilb_pos_of_srelDiagMono D I h _
  have h3 : (1 : ℚ) ≤ ((rayHilb N D I (max a 1) : ℕ) : ℚ) := by exact_mod_cast h2
  linarith

/-! ## Multihomogeneity of a principal cut -/

private lemma multiHom_sup_span_singleton {J : Ideal (MR N)} (hJ : MultiHom N J)
    {u : Fin (N + 1) →₀ ℕ} {P : MR N} (hP : P ∈ homPiece N u) :
    MultiHom N (J ⊔ Ideal.span {P}) := by
  rw [multiHom_iff_multiHomZ] at hJ ⊢
  have hPz : P ∈ pieceZ N (castF u) := by simpa [homPiece_eq_pieceZ] using hP
  exact MultiHomZ.sup hJ (MultiHomZ.span_singleton hPz)

/-! ## The one-step cut -/

/-! ## A height helper -/

/-- A finite element of `ℕ∞` is not equal to itself plus a positive natural number. -/
private lemma ne_self_add_natCast (x : ℕ∞) (hx : x ≠ ⊤) {m : ℕ} (hm : 0 < m) :
    x ≠ x + (m : ℕ∞) := by
  intro h
  have h2 : x.toNat = x.toNat + m := by
    have h3 := congrArg ENat.toNat h
    rwa [ENat.toNat_add hx (ENat.natCast_ne_top m)] at h3
  omega

/-! ## The main theorem -/

/-- **The srel-cut dimension inequality.** If `r ≤ s` are multihomogeneous primes of `MR N` whose
heights differ by `m`, and no diagonal monomial `∏ᵢ X_{i,0}^{t Dᵢ}` lies in `s`, then the ray
dimension drops by at least `m` from `r` to `s`: `rayDim N D s + m ≤ rayDim N D r`. -/
theorem srelcut_chain {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (m : ℕ) (r s : Ideal (MR N)) (hr : r.IsPrime) (hs : s.IsPrime)
    (hrm : MultiHom N r) (hsm : MultiHom N s) (hrs : r ≤ s)
    (hav : ∀ t : ℕ, (∏ i : Fin (N + 1), (MvPolynomial.X (i, 0) : MR N) ^ (t * D i)) ∉ s)
    (hht : s.height = r.height + (m : ℕ∞)) :
    rayDim N D s + m ≤ rayDim N D r := by
  classical
  have hdiag : ∀ t : ℕ, srelDiagMono N D t ∉ s := fun t => hav t
  suffices key : ∀ m : ℕ, ∀ (r s : Ideal (MR N)), r.IsPrime → s.IsPrime → MultiHom N r →
      MultiHom N s → r ≤ s → (∀ t : ℕ, srelDiagMono N D t ∉ s) →
      s.height = r.height + (m : ℕ∞) → rayDim N D s + m ≤ rayDim N D r by
    exact key m r s hr hs hrm hsm hrs hdiag hht
  intro m
  induction m with
  | zero =>
    intro r s hr hs hrm hsm hrs hdiag hht
    -- `m = 0`: the ray dimension is antitone in the ideal
    have hpolyr : ∃ q : Polynomial ℚ, IsRayPoly N D r q :=
      ⟨_, isRayPoly_rayPoly (hilb_serre_input N) D hD r hrm⟩
    have hpolys : ∃ q : Polynomial ℚ, IsRayPoly N D s q :=
      ⟨_, isRayPoly_rayPoly (hilb_serre_input N) D hD s hsm⟩
    have hle := rb_rayDim_anti hrs hpolyr hpolys
    simp only [Nat.cast_zero, add_zero] at hht
    omega
  | succ m' ih =>
    intro r s hr hs hrm hsm hrs hdiag hht
    haveI := hs
    -- the inclusion `r < s` is strict
    have hne : r ≠ s := by
      intro heq
      have hfin : s.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
      refine ne_self_add_natCast s.height hfin (Nat.succ_pos m') ?_
      rw [heq] at hht
      exact hht
    -- no `X_{i,0}` lies in `r`: otherwise the diagonal monomial would already lie in `s`
    have havr : ∀ i : Fin (N + 1), (MvPolynomial.X (i, 0) : MR N) ∉ r := by
      intro i hi
      have hnotmem :
          (∏ j : Fin (N + 1), (MvPolynomial.X (j, 0) : MR N) ^ (1 * D j)) ∉ s := by
        simpa [srelDiagMono] using hdiag 1
      have hpow : (MvPolynomial.X (i, 0) : MR N) ^ (1 * D i) ∈ s :=
        pow_mem_of_mem_of_pos (I := s) (hrs hi) (by have := hD i; omega)
      exact hnotmem ((Ideal.IsPrime.prod_mem_iff).mpr ⟨i, Finset.mem_univ i, hpow⟩)
    -- cut `r` by a multihomogeneous element of `s`
    obtain ⟨k, hk, P, hPmem, hPs, hPr⟩ :=
      cut_homPiece_exists D hD r s hr hsm (lt_of_le_of_ne hrs hne) havr
    have hcutMH : MultiHom N (r ⊔ Ideal.span {P}) := multiHom_sup_span_singleton hrm hPmem
    have hle_cut : r ⊔ Ideal.span {P} ≤ s :=
      sup_le hrs (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hPs))
    obtain ⟨q, hqmin, hqs⟩ := Ideal.exists_minimalPrimes_le (I := r ⊔ Ideal.span {P}) hle_cut
    have hqprime : q.IsPrime := hqmin.isPrime
    have hqmult : MultiHom N q := multiHom_minimalPrimes (r ⊔ Ideal.span {P}) hcutMH q hqmin
    have hqht : q.height = r.height + 1 :=
      height_minimalPrimes_sup_span_singleton r hr P hPr hqmin
    have hrq : r < q := by
      refine lt_of_le_of_ne (le_sup_left.trans hqmin.le) fun heq => ?_
      haveI := hr
      have hfin : r.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
      refine ne_self_add_natCast (m := 1) r.height hfin (by norm_num) ?_
      rw [heq] at hqht ⊢
      exact hqht
    -- the intermediate prime also has a nonvanishing ray polynomial
    have hqdiag : ∀ t : ℕ, srelDiagMono N D t ∉ q := fun t hmem => hdiag t (hqs hmem)
    have hq0 : rayPoly N D q ≠ 0 := rayPoly_ne_zero_of_srelDiagMono D hD q hqmult hqdiag
    have hdrop : rayDim N D q < rayDim N D r :=
      rayDim_lt_of_lt D hD r q hr hqprime hrm hqmult hrq hq0
    -- induction at `m'` for the pair `q ≤ s`
    have hcast : (((m' + 1 : ℕ)) : ℕ∞) = 1 + (m' : ℕ∞) := by
      rw [Nat.cast_add, Nat.cast_one]; exact add_comm _ _
    have hht' : s.height = q.height + (m' : ℕ∞) := by
      rw [hht, hqht, hcast, add_assoc]
    have ih' := ih q s hqprime hs hqmult hsm hqs hdiag hht'
    omega


lemma ringKrullDim_MR (N : ℕ) : ringKrullDim (MR N) = (((2 * (N + 1) : ℕ)) : WithBot ℕ∞) := by
  have h1 := MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite (R := ℂ)
    (ι := Fin (N + 1) × Fin 2)
  rw [ringKrullDim_eq_zero_of_field, zero_add] at h1
  have hcard : Nat.card (Fin (N + 1) × Fin 2) = 2 * (N + 1) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin,
      Nat.mul_comm]
  rw [hcard] at h1
  exact h1

/-- Heights of primes in `MR N` are at most `2(N+1)`. -/
lemma height_le_two_mul {N : ℕ} (r : Ideal (MR N)) (hr : r.IsPrime) :
    r.height ≤ ((2 * (N + 1) : ℕ) : ℕ∞) := by
  have hle : ((r.height : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim (MR N) :=
    Ideal.height_le_ringKrullDim_of_isPrime
  rw [ringKrullDim_MR N] at hle
  exact WithBot.coe_le_coe.mp hle

lemma height_ne_top {N : ℕ} (r : Ideal (MR N)) (hr : r.IsPrime) : r.height ≠ ⊤ :=
  ne_top_of_le_ne_top (ENat.coe_ne_top _) (height_le_two_mul r hr)

/-- The maximal ideal of a point. -/
lemma height_ptIdeal {N : ℕ} (y : Fin (N + 1) × Fin 2 → ℂ) :
    (ptIdeal N y).height = ((2 * (N + 1) : ℕ) : ℕ∞) := by
  have hmax : (ptIdeal N y).IsMaximal := by
    refine RingHom.ker_isMaximal_of_surjective (MvPolynomial.eval y) fun c => ⟨MvPolynomial.C c, ?_⟩
    simp
  haveI := hmax
  have h1 := maximal_height_eq_ringKrullDim (MR N) (ptIdeal N y)
  rw [ringKrullDim_MR N] at h1
  exact WithBot.coe_eq_coe.mp h1

/-- The monomial `∏ X_{i,0}^{t D_i}` is not in a prime avoiding the `X_{i,0}`. -/
lemma monoD_notMem {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (r : Ideal (MR N)) (hr : r.IsPrime)
    (hX : ∀ i : Fin (N + 1), (MvPolynomial.X (i, 0) : MR N) ∉ r) (t : ℕ) :
    (∏ i : Fin (N + 1), (MvPolynomial.X (i, 0) : MR N) ^ (t * D i)) ∉ r := by
  intro hmem
  rw [Ideal.IsPrime.prod_mem_iff] at hmem
  obtain ⟨i, -, hi⟩ := hmem
  exact hX i (hr.mem_of_pow_mem _ hi)

/-- The monomial-avoidance condition for an admissible prime. -/
lemma monoD_notMem_of_admissible {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (p : Ideal (MR N))
    (hp : p.IsPrime) (hadm : OnGPrime N p) (t : ℕ) :
    (∏ i : Fin (N + 1), (MvPolynomial.X (i, 0) : MR N) ^ (t * D i)) ∉ p :=
  monoD_notMem D p hp ((OnGPrime_iff p hp).mp hadm).1 t

/-- `Srel` at an admissible prime is its ray degree. -/
lemma srel_self_of_isPrime {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (p : Ideal (MR N)) (hp : p.IsPrime)
    (hadm : OnGPrime N p) : Srel N D p = rayDeg N D p := by
  classical
  haveI := hp
  have hpl : ((primLen p p).toNat : ℚ) = 1 := by
    rw [primLen_eq_locLenAt p p hp, locLenAt_self p hp]
    norm_num
  rw [Srel, Ideal.minimalPrimes_eq_subsingleton_self]
  simp only [Set.mem_singleton_iff]
  rw [finsum_eq_single _ p]
  · simp [hadm, hpl]
  · intro q hq
    simp [hq]

/-- `Srel` vanishes if the ray Hilbert polynomial vanishes. -/
lemma srel_eq_zero_of_rayPoly_eq_zero {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (J : Ideal (MR N)) (hJ : MultiHom N J) (h0 : rayPoly N D J = 0) : Srel N D J = 0 := by
  classical
  have hnone : ∀ q ∈ J.minimalPrimes, ¬ OnGPrime N q := by
    intro q hq hqadm
    have hqprime : q.IsPrime := hq.isPrime
    have hq0 := monoD_notMem_of_admissible D q hqprime hqadm
    have hspec : ∀ᶠ t : ℕ in Filter.atTop, rayHilb N D J t = 0 := by
      have h := isRayPoly_rayPoly (hilb_serre_input N) D hD J hJ
      rw [h0] at h
      filter_upwards [h] with t ht
      have ht' : ((rayHilb N D J t : ℕ) : ℚ) = 0 := by simpa using ht
      exact_mod_cast ht'
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hspec
    have h1 := srelcut_rayHilb_pos D hD q hqprime hq0 T
    have h2 : rayHilb N D q T ≤ rayHilb N D J T :=
      rb_rayHilb_le_rayHilb (I := J) (J := q) hq.le T
    rw [hT T le_rfl] at h2
    omega
  rw [Srel]
  refine (finsum_cond_eq_sum (fun q : Ideal (MR N) => q ∈ J.minimalPrimes ∧ OnGPrime N q)
    (∅ : Finset (Ideal (MR N))) ?_
    (fun q => ((primLen J q).toNat : ℚ) * rayDeg N D q)).trans Finset.sum_empty
  · intro a ha
    exact absurd ha.2 (hnone a ha.1)

lemma multiHom_bot_ideal : MultiHom N (⊥ : Ideal (MR N)) := by
  intro f hf d
  rw [Submodule.mem_bot] at hf
  rw [hf]
  simp

lemma rayDim_bot_eq (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i) :
    rayDim N D (⊥ : Ideal (MR N)) = N + 1 := (rayDeg_bot D hD).2.1

lemma multiHom_sup_span {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (p : Ideal (MR N)) (hpm : MultiHom N p)
    (P : MR N) (hP : P ∈ homPiece N D) : MultiHom N (p ⊔ Ideal.span {P}) := by
  have h2 : MultiHomZ N (Ideal.span {P}) := by
    refine MultiHomZ.span_singleton (u := castF D) ?_
    rw [← homPiece_eq_pieceZ]
    exact hP
  exact (multiHom_iff_multiHomZ _).mpr ((multiHom_iff_multiHomZ p).mp hpm |>.sup h2)

/-- The ray dimension of an admissible prime in terms of its height. -/
lemma rayDim_eq_card_sub_height_adm {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (p : Ideal (MR N)) (hp : p.IsPrime) (hpm : MultiHom N p) (hadm : OnGPrime N p) :
    rayDim N D p = N + 1 - p.height.toNat := by
  obtain ⟨y, hyG, hpy⟩ := hadm
  have hy0 : ∀ i : Fin (N + 1), y (i, 0) ≠ 0 := by
    intro i
    rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, h⟩
    · rw [h]; exact hyG.1
    · rw [h]; exact (hyG.2 j).1
  have hne := height_ne_top p hp
  have hpbot : (⊥ : Ideal (MR N)).IsPrime := inferInstance
  have havp := monoD_notMem_of_admissible D p hp ⟨y, hyG, hpy⟩
  have hupper : rayDim N D p ≤ N + 1 - p.height.toNat := by
    have hht : p.height = (⊥ : Ideal (MR N)).height + ((p.height.toNat : ℕ) : ℕ∞) := by
      rw [Ideal.height_bot, zero_add]
      exact (ENat.natCast_toNat hne).symm
    have h := srelcut_chain D hD p.height.toNat ⊥ p hpbot hp
      multiHom_bot_ideal hpm bot_le havp hht
    rw [rayDim_bot_eq D hD] at h
    omega
  have hcd : p ≤ diagIdeal N y := srelcut_prime_le_diagonal p hp hpm y hy0 hpy
  have hcprime : (diagIdeal N y).IsPrime := diagIdeal_isPrime N y hy0
  have hcheight : (diagIdeal N y).height = ((N + 1 : ℕ) : ℕ∞) := diagIdeal_height N y hy0
  have hcmh : MultiHom N (diagIdeal N y) := diagIdeal_multiHom N y
  have hcav : ∀ t : ℕ, (∏ i : Fin (N + 1), (MvPolynomial.X (i, 0) : MR N) ^ (t * D i))
      ∉ diagIdeal N y := fun t => diag_mono_notMem N y hy0 D t
  have hlower : N + 1 - p.height.toNat ≤ rayDim N D p := by
    have hle' : p.height.toNat ≤ N + 1 := by
      have h : p.height ≤ ((N + 1 : ℕ) : ℕ∞) := by
        rw [← hcheight]
        exact Ideal.height_mono hcd
      calc p.height.toNat ≤ (((N + 1 : ℕ) : ℕ∞)).toNat := ENat.toNat_le_toNat h (ENat.natCast_ne_top _)
        _ = N + 1 := ENat.toNat_natCast _
    have hht : (diagIdeal N y).height
        = p.height + (((N + 1) - p.height.toNat : ℕ) : ℕ∞) := by
      set k := p.height.toNat with hkdef
      have hk : ((k : ℕ) : ℕ∞) = p.height := by
        rw [hkdef]; exact ENat.natCast_toNat hne
      have hk' : k ≤ N + 1 := by rw [hkdef]; exact hle'
      rw [hcheight, ← hk, ← Nat.cast_add, Nat.add_sub_of_le hk']
    have h := srelcut_chain D hD ((N + 1) - p.height.toNat) p (diagIdeal N y)
      hp hcprime hpm hcmh hcd hcav hht
    have h0 : 0 ≤ rayDim N D (diagIdeal N y) := Nat.zero_le _
    omega
  exact le_antisymm hupper hlower

/-- Every admissible minimal prime of `p ⊔ (P)` is top-dimensional in `p ⊔ (P)`. -/
lemma admissible_minimalPrimes_top {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (p : Ideal (MR N)) (hp : p.IsPrime) (hpm : MultiHom N p)
    (P : MR N) (hP : P ∈ homPiece N D) (hPp : P ∉ p) (hadm : OnGPrime N p) :
    ∀ q ∈ (p ⊔ Ideal.span {P}).minimalPrimes, OnGPrime N q →
      rayDim N D q = rayDim N D (p ⊔ Ideal.span {P}) := by
  intro q hq hqadm
  have hJmh : MultiHom N (p ⊔ Ideal.span {P}) := multiHom_sup_span D p hpm P hP
  have hqprime : q.IsPrime := hq.isPrime
  have hqmh : MultiHom N q := by
    have hq' : q ∈ (Module.annihilator (MR N) (MR N ⧸ (p ⊔ Ideal.span {P}))).minimalPrimes := by
      rw [Ideal.annihilator_quotient]
      exact hq
    exact multiHom_assPrime (p ⊔ Ideal.span {P}) hJmh q
      (Module.associatedPrimes.minimalPrimes_annihilator_subset_associatedPrimes (MR N)
        (MR N ⧸ (p ⊔ Ideal.span {P})) hq')
  have hreg : ∀ f, P * f ∈ p → f ∈ p := by
    intro f hf
    rcases hp.mem_or_mem hf with h | h
    · exact absurd h hPp
    · exact h
  have hpnz : rayPoly N D p ≠ 0 := by
    intro h0
    have hspec : ∀ᶠ t : ℕ in Filter.atTop, rayHilb N D p t = 0 := by
      have h := isRayPoly_rayPoly (hilb_serre_input N) D hD p hpm
      rw [h0] at h
      filter_upwards [h] with t ht
      have ht' : ((rayHilb N D p t : ℕ) : ℚ) = 0 := by simpa using ht
      exact_mod_cast ht'
    obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hspec
    have hT0 : rayHilb N D p T = 0 := hT T le_rfl
    have h1 := srelcut_rayHilb_pos D hD p hp (monoD_notMem_of_admissible D p hp hadm) T
    omega
  have hle1 : rayDim N D q ≤ rayDim N D (p ⊔ Ideal.span {P}) :=
    rayDim_le_of_le (hilb_serre_input N) D hD hJmh hqmh hq.le
  have hle2 : rayDim N D (p ⊔ Ideal.span {P}) ≤ rayDim N D q := by
    by_cases hpos : 1 ≤ rayDim N D p
    swap
    · have h0p : rayDim N D p = 0 := by omega
      have hmono := rayDim_le_of_le (hilb_serre_input N) D hD hpm hJmh le_sup_left
      omega
    obtain ⟨hdimJ, _⟩ := rayDeg_hyperplane D hD p hpm P hP hreg hpnz hpos
    have h1 : rayDim N D q = N + 1 - q.height.toNat :=
      rayDim_eq_card_sub_height_adm D hD q hqprime hqmh hqadm
    have h2 : rayDim N D p = N + 1 - p.height.toNat :=
      rayDim_eq_card_sub_height_adm D hD p hp hpm hadm
    have h3 : q.height = p.height + 1 :=
      height_minimalPrimes_sup_span_singleton p hp P hPp hq
    have hne := height_ne_top p hp
    have hqt : q.height.toNat = p.height.toNat + 1 := by
      have hqht : q.height = ((p.height.toNat + 1 : ℕ) : ℕ∞) := by
        rw [h3]
        conv_lhs => rw [← ENat.natCast_toNat hne]
        rw [Nat.cast_add, Nat.cast_one]
      exact (ENat.toNat_eq_iff (by omega)).mpr hqht
    have hJd : rayDim N D (p ⊔ Ideal.span {P}) = rayDim N D p - 1 := by omega
    rw [h1, hJd, h2, hqt]
    omega
  exact le_antisymm hle1 hle2

/-- **The one-step cut by a prime.** -/
theorem srel_cut_prime {N : ℕ} (D : Fin (N + 1) →₀ ℕ) (hD : ∀ i, 1 ≤ D i)
    (p : Ideal (MR N)) (hp : p.IsPrime) (hpm : MultiHom N p)
    (P : MR N) (hP : P ∈ homPiece N D) (hPp : P ∉ p) (hadm : OnGPrime N p) :
    Srel N D (p ⊔ Ideal.span {P}) ≤ Srel N D p := by
  classical
  rw [srel_self_of_isPrime D p hp hadm]
  have hJmh : MultiHom N (p ⊔ Ideal.span {P}) := multiHom_sup_span D p hpm P hP
  have hmain : Srel N D (p ⊔ Ideal.span {P}) ≤ rayDeg N D (p ⊔ Ideal.span {P}) := by
    by_cases h0 : rayPoly N D (p ⊔ Ideal.span {P}) = 0
    · rw [srel_eq_zero_of_rayPoly_eq_zero D hD _ hJmh h0]
      exact rayDeg_nonneg D _
    · set S := (Ideal.finite_minimalPrimes_of_isNoetherianRing (MR N)
        (p ⊔ Ideal.span {P})).toFinset with hSdef
      have hS : ∀ q, q ∈ (p ⊔ Ideal.span {P}).minimalPrimes → q ∈ S :=
        fun q hq => (Set.Finite.mem_toFinset _).mpr hq
      have e1 : Srel N D (p ⊔ Ideal.span {P})
          = ∑ q ∈ S, (if (q ∈ (p ⊔ Ideal.span {P}).minimalPrimes ∧ OnGPrime N q)
              then ((primLen (p ⊔ Ideal.span {P}) q).toNat : ℚ) * rayDeg N D q else 0) := by
        rw [Srel]
        exact finsum_cond_eq_sum _ S (fun q hq => hS q hq.1) _
      have e2 : (∑ᶠ (q : Ideal (MR N)) (_ : q ∈ (p ⊔ Ideal.span {P}).minimalPrimes ∧
              rayPoly N D q ≠ 0 ∧ rayDim N D q = rayDim N D (p ⊔ Ideal.span {P})),
              ((primLen (p ⊔ Ideal.span {P}) q).toNat : ℚ) * rayDeg N D q)
          = ∑ q ∈ S, (if (q ∈ (p ⊔ Ideal.span {P}).minimalPrimes ∧ rayPoly N D q ≠ 0 ∧
                rayDim N D q = rayDim N D (p ⊔ Ideal.span {P}))
              then ((primLen (p ⊔ Ideal.span {P}) q).toNat : ℚ) * rayDeg N D q else 0) :=
        finsum_cond_eq_sum _ S (fun q hq => hS q hq.1) _
      rw [rayDeg_additive D hD _ hJmh h0, e1, e2]
      refine Finset.sum_le_sum fun q hqS => ?_
      have hqmin : q ∈ (p ⊔ Ideal.span {P}).minimalPrimes := (Set.Finite.mem_toFinset _).mp hqS
      simp only [hqmin, true_and]
      by_cases hqa : OnGPrime N q
      · rw [if_pos hqa]
        by_cases hq0 : rayPoly N D q = 0
        · rw [if_neg (by simp [hq0])]
          rw [rayDeg, hq0]
          simp
        · rw [if_pos ⟨hq0, admissible_minimalPrimes_top D hD p hp hpm P hP hPp hadm q hqmin hqa⟩]
      · rw [if_neg hqa]
        by_cases hc : (rayPoly N D q ≠ 0 ∧ rayDim N D q = rayDim N D (p ⊔ Ideal.span {P}))
        · rw [if_pos hc]
          exact mul_nonneg (by positivity) (rayDeg_nonneg D q)
        · rw [if_neg hc]
  have hdeg : rayDeg N D (p ⊔ Ideal.span {P}) ≤ rayDeg N D p := by
    by_cases hpos : 1 ≤ rayDim N D p
    · have hreg : ∀ f, P * f ∈ p → f ∈ p := by
        intro f hf
        rcases hp.mem_or_mem hf with h | h
        · exact absurd h hPp
        · exact h
      have hpnz : rayPoly N D p ≠ 0 := by
        intro h0
        have hspec : ∀ᶠ t : ℕ in Filter.atTop, rayHilb N D p t = 0 := by
          have h := isRayPoly_rayPoly (hilb_serre_input N) D hD p hpm
          rw [h0] at h
          filter_upwards [h] with t ht
          have ht' : ((rayHilb N D p t : ℕ) : ℚ) = 0 := by simpa using ht
          exact_mod_cast ht'
        obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hspec
        have hT0 : rayHilb N D p T = 0 := hT T le_rfl
        have h1 := srelcut_rayHilb_pos D hD p hp (monoD_notMem_of_admissible D p hp hadm) T
        omega
      exact le_of_eq (rayDeg_hyperplane D hD p hpm P hP hreg hpnz hpos).2
    · have h0p : rayDim N D p = 0 := by omega
      by_cases hJ0 : rayPoly N D (p ⊔ Ideal.span {P}) = 0
      · rw [rayDeg, hJ0]
        simp
        exact rayDeg_nonneg D p
      · refine rayDeg_mono D hD p (p ⊔ Ideal.span {P}) hpm hJmh le_sup_left hJ0 ?_
        have hmono := rayDim_le_of_le (hilb_serre_input N) D hD hpm hJmh le_sup_left
        omega
  exact le_trans hmain hdeg

end

end Work.BW.RB
