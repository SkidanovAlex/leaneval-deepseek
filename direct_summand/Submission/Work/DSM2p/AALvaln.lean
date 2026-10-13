import Mathlib
import Submission.Work.DSM2p.Basic
import Submission.Work.DSM1p.Perfectoid.varpi_smul_eq_zero_iff

/-!
# `Work.DSM2p.AALvaln` — the shared vocabulary of the `area_AAL` development

This module holds the *permanent shared layer* of the `area_AAL` subproject: the Česnavičius–Scholze
vocabulary of continuous valuations (`IsContinuousValuation`, `IsUnitBall`), the elementary
`PerfectoidData` facts, the tilting facts (`exists_tiltable_approx`, `untilt_hasCompatPRoots`), the
glue facts relating `R` to `L = R[1/ϖ 0]`, and the two generation hypotheses consumed by the subring
form of `nilp_lem`.

It is deliberately *separate* from `area_AAL_proved.lean`: that file states the deliverable theorem
and must be able to *import* the delegated results (`approx_lem`, `nilp_lem`, `nilp_lem_subring`),
while those results import only this vocabulary.  Keeping the vocabulary here is what makes that
dependency direction possible.
-/


/-!
# `DSM2p.area_AAL` — the analytic input of GAP 3 (Česnavičius–Scholze `approx-lem`)

This file owns the node `area_AAL` of GAP 3 (see `Submission/Work/DSMap/Gaps.lean`): every element
`P` of a perfectoid ring `R` is `p`-power close to an element `Q` admitting a *compatible system of
`p`-power roots*, in the algebraic form used by Česnavičius–Scholze.

## Road map

* `p_mem_span_varpi_pow` : `p ∈ (ϖ 0 ^ p)` (from the unit field of `PerfectoidData`).
* `eq_zero_of_mem_all_pow` : the `p`-adic separation lemma `⋂ₙ pⁿR = 0` (from `IsAdicComplete`).
* `exists_tiltable_approx` : **the elementary approximation lemma** — every `x : R` is congruent
  modulo `p` to an element that admits a compatible system of `p`-power roots.  This is proved from
  `PerfectoidData.frobSurj` (Frobenius surjectivity mod `p`), the `p`-adic completeness of `R`, and
  Mathlib's tilt API (`Perfection`, `PreTilt`, `PreTilt.untilt`, `Perfection.coeff_surjective`).

The remaining (analytic) content of `area_AAL` — the Česnavičius–Scholze `approx-lem` *estimate*
and `nilp-lem` — is developed further below.
-/

open scoped Classical

namespace Work.DSM2p

universe u

variable {p : ℕ} [Fact p.Prime]

/-! ## Elementary consequences of `PerfectoidData` -/

section Basic

variable {R : Type u} [CommRing R]

/-- `ϖ 1 ^ p = ϖ 0`. -/
theorem varpi_one_pow (QR : DSMap.PerfectoidData p R) :
    QR.ϖ 1 ^ p = QR.ϖ 0 := QR.root 0

/-- `p` is a multiple of `ϖ 0 ^ p`. -/
theorem p_mem_span_varpi_pow (QR : DSMap.PerfectoidData p R) :
    (p : R) ∈ Ideal.span {QR.ϖ 0 ^ p} := by
  obtain ⟨v, hv⟩ := QR.unit
  refine Ideal.mem_span_singleton'.2 ⟨(↑v⁻¹ : R), ?_⟩
  rw [hv, mul_comm (↑p) (↑v : R), ← mul_assoc, Units.inv_mul, one_mul]

/-- `p` is a multiple of `ϖ 0`. -/
theorem p_mem_span_varpi (QR : DSMap.PerfectoidData p R) :
    (p : R) ∈ Ideal.span {QR.ϖ 0} := by
  have h1 : QR.ϖ 0 ^ p ∈ Ideal.span {QR.ϖ 0} := by
    refine Ideal.mem_span_singleton.2 ⟨QR.ϖ 0 ^ (p - 1), ?_⟩
    rw [← pow_succ']
    congr 1
    exact (Nat.succ_pred_eq_of_pos (Fact.out : p.Prime).pos).symm
  exact (Ideal.span_le.2 (Set.singleton_subset_iff.2 h1)) (p_mem_span_varpi_pow QR)

/-- **`p`-adic separation.**  `R` is `p`-adically separated: an element lying in every `pⁿR` is
zero. -/
theorem eq_zero_of_mem_all_pow (QR : DSMap.PerfectoidData p R)
    (x : R) (h : ∀ n : ℕ, x ∈ (Ideal.span {(p : R)}) ^ n) : x = 0 := by
  haveI := DSMap.PerfectoidData.complete QR
  refine IsHausdorff.haus' (I := Ideal.span {(p : R)}) x fun n => ?_
  exact SModEq.zero.2 (by simpa using h n)

/-- If `p` is a unit then `R` is trivial. -/
theorem subsingleton_of_isUnit_p (QR : DSMap.PerfectoidData p R)
    (h : IsUnit (p : R)) : Subsingleton R := by
  have htop : Ideal.span {(p : R)} = ⊤ := Ideal.span_singleton_eq_top.2 h
  have hc : IsAdicComplete (⊤ : Ideal R) R := htop ▸ DSMap.PerfectoidData.complete QR
  exact hc.subsingleton R

end Basic

/-! ## The elementary approximation lemma -/

section Approx

variable {R : Type u} [CommRing R]

/-- **The elementary approximation lemma.**  Every element `x` of a perfectoid ring is congruent
modulo `p` to an element `Q` admitting a compatible system of `p`-power roots (`Q` is the "untilt"
of an element of the tilt, hence a `♯`-element in the sense of Česnavičius–Scholze).

The construction is the standard one: Frobenius surjectivity modulo `p` makes the `0`-th coefficient
of the tilt surjective onto `R/p`, and the untilt of any tilt element has compatible `p`-power roots
(`PreTilt.untilt_iterate_frobeniusEquiv_symm_pow`). -/
theorem exists_tiltable_approx (QR : DSMap.PerfectoidData p R)
    (hp : ¬ IsUnit (p : R)) (x : R) :
    ∃ Q : R, HasCompatPRoots p Q ∧ x - Q ∈ Ideal.span {(p : R)} := by
  haveI : Fact (¬ IsUnit (p : R)) := ⟨hp⟩
  haveI := DSMap.PerfectoidData.complete QR
  -- Frobenius is surjective on `R ⧸ (p)`
  have hF : Function.Surjective (frobenius (ModP R p) p) := by
    intro y
    obtain ⟨x₀, rfl⟩ := Ideal.Quotient.mk_surjective y
    obtain ⟨z, hz⟩ := QR.frobSurj x₀
    refine ⟨Ideal.Quotient.mk (Ideal.span {(p : R)}) z, ?_⟩
    rw [frobenius_def]
    refine Ideal.Quotient.eq.2 ?_
    have : z ^ p - x₀ ∈ Ideal.span {(p : R)} := by
      have h := neg_mem hz
      simpa [neg_sub] using h
    exact this
  -- pick the tilt element with prescribed `0`-th component
  obtain ⟨ξ, hξ⟩ : ∃ ξ : PreTilt R p,
      PreTilt.coeff 0 ξ = Ideal.Quotient.mk (Ideal.span {(p : R)}) x :=
    Perfection.coeff_surjective (R := ModP R p) (p := p) hF 0
      (Ideal.Quotient.mk (Ideal.span {(p : R)}) x)
  refine ⟨PreTilt.untilt ξ, ?_, ?_⟩
  · -- compatible system of `p`-power roots
    refine ⟨fun n => PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm^[n]) ξ), ?_, ?_⟩
    · rfl
    · intro k
      have h := PreTilt.untilt_iterate_frobeniusEquiv_symm_pow
        (((frobeniusEquiv (PreTilt R p) p).symm^[k]) ξ) 1
      simpa [Function.iterate_succ_apply', pow_one] using h
  · -- congruence modulo `p`
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    rw [map_sub, PreTilt.mk_untilt_eq_coeff_zero ξ, hξ, sub_self]

end Approx

/-! ## Compatible `p`-power roots of tilt elements -/

section UntiltRoots

variable {R : Type u} [CommRing R]

/-- **Every tilt element has compatible `p`-power roots.**  The `pⁿ`-th root of `ξ.untilt` is the
untilt of the `n`-fold inverse Frobenius translate of `ξ`. -/
theorem untilt_hasCompatPRoots [Fact (¬ IsUnit (p : R))]
    [IsAdicComplete (Ideal.span {(p : R)}) R] (ξ : PreTilt R p) :
    HasCompatPRoots p (PreTilt.untilt ξ) :=
  ⟨fun n => PreTilt.untilt (((frobeniusEquiv (PreTilt R p) p).symm^[n]) ξ), rfl, by
    intro k
    have h := PreTilt.untilt_iterate_frobeniusEquiv_symm_pow
      (((frobeniusEquiv (PreTilt R p) p).symm^[k]) ξ) 1
    simpa [Function.iterate_succ_apply', pow_one] using h⟩

end UntiltRoots

/-! ## Continuous valuations (Česnavičius–Scholze `AAL-a`)

The two remaining inputs of `area_AAL` — CS `approx-lem` (with its estimate) and CS `nilp-lem` —
are both stated for *continuous valuations* of the `ϖ`-adic topology.  Following
Česnavičius–Scholze, §1.3 ("continuity is for the `ϖ`-adic topology: `|ϖⁿ|` becomes smaller than any
element of the value group") a valuation is continuous when the values of the powers of `ϖ` become
smaller than any prescribed positive value.  We use Mathlib's `Valuation R Γ₀` (multiplicative,
nonarchimedean: `v (x + y) ≤ max (v x) (v y)`), with values in a linearly ordered commutative monoid
with zero. -/

/-- A valuation `v` on a ring `A` is **continuous** for the `ϖ`-adic topology if the values of the
powers of `ϖ` become smaller than any prescribed positive value. -/
def IsContinuousValuation {A Γ₀ : Type*} [Ring A] [LinearOrderedCommMonoidWithZero Γ₀]
    (ϖ : A) (v : Valuation A Γ₀) : Prop :=
  ∀ γ : Γ₀, γ ≠ 0 → ∃ n : ℕ, v ϖ ^ n < γ

/-- The bounding condition `|A| ≤ 1` of `approx-lem` and `nilp-lem`: `v` is `≤ 1` on the subring
generated by the given elements. -/
def IsUnitBall {A Γ₀ : Type*} [Ring A] [LinearOrderedCommMonoidWithZero Γ₀]
    (v : Valuation A Γ₀) (s : Set A) : Prop := ∀ a ∈ s, v a ≤ 1

/-- Monotonicity of `IsUnitBall` in the set. -/
theorem IsUnitBall.mono {A Γ₀ : Type*} [Ring A] [LinearOrderedCommMonoidWithZero Γ₀]
    {v : Valuation A Γ₀} {s t : Set A} (hst : s ⊆ t) (h : IsUnitBall v t) : IsUnitBall v s :=
  fun a ha => h a (hst ha)

/-! ## Elementary properties of continuous valuations -/

section ValuationLemmas

variable {A B Γ₀ : Type*} [CommRing A] [CommRing B] [LinearOrderedCommGroupWithZero Γ₀]

/-- For a continuous valuation the value of `ϖ` is `< 1`: otherwise all its powers would be
`≥ 1`, contradicting continuity. -/
theorem IsContinuousValuation.map_lt_one {ϖ : A} {v : Valuation A Γ₀}
    (hv : IsContinuousValuation ϖ v) : v ϖ < 1 := by
  obtain ⟨n, hn⟩ := hv 1 one_ne_zero
  by_contra h
  exact absurd hn (not_lt.2 (one_le_pow₀ (not_lt.1 h)))

/-- Restriction of a valuation along a ring homomorphism (a valuation, since the target is
linearly ordered and the triangle inequality is inherited). -/
def Valuation.precomp (f : A →+* B) (v : Valuation B Γ₀) : Valuation A Γ₀ where
  toMonoidWithZeroHom := v.toMonoidWithZeroHom.comp f
  map_add_le_max' := fun x y => by
    show v (f (x + y)) ≤ max (v (f x)) (v (f y))
    rw [map_add]
    exact v.map_add_le_max' (f x) (f y)

@[simp]
theorem Valuation.precomp_apply (f : A →+* B) (v : Valuation B Γ₀) (x : A) :
    (Valuation.precomp f v) x = v (f x) := rfl

/-- Continuity is preserved by restriction along a ring homomorphism. -/
theorem IsContinuousValuation.precomp {ϖ : A} (f : A →+* B) {v : Valuation B Γ₀}
    (hv : IsContinuousValuation (f ϖ) v) : IsContinuousValuation ϖ (Valuation.precomp f v) := by
  intro γ hγ
  obtain ⟨n, hn⟩ := hv γ hγ
  refine ⟨n, ?_⟩
  rw [Valuation.precomp_apply]
  exact hn

/-- The unit-ball condition is preserved by restriction along a ring homomorphism. -/
theorem IsUnitBall.precomp {v : Valuation B Γ₀} {s : Set A} (f : A →+* B)
    (hv : IsUnitBall v (f '' s)) : IsUnitBall (Valuation.precomp f v) s := by
  intro a ha
  exact hv (f a) (Set.mem_image_of_mem f ha)

/-- On the unit ball of a perfectoid ring, `p` has value `< 1`: `p = r * ϖ 0` and `v r ≤ 1`. -/
theorem Valuation.map_p_lt_one {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]
    (QR : DSMap.PerfectoidData p R) (v : Valuation R Γ₀)
    (hv : IsContinuousValuation (QR.ϖ 0) v) (hball : IsUnitBall v Set.univ) :
    v (p : R) < 1 := by
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.1 (p_mem_span_varpi QR)
  rw [← hr, map_mul]
  calc v r * v (QR.ϖ 0) ≤ 1 * v (QR.ϖ 0) :=
        mul_le_mul' (hball r (Set.mem_univ r)) le_rfl
    _ = v (QR.ϖ 0) := one_mul _
    _ < 1 := hv.map_lt_one

end ValuationLemmas

/-! ## The glue: injectivity of `R → R[1/ϖ 0]` and the intermediate subalgebras

Clauses (i)–(iii) of the target all go through `nilp_lem`, which is stated for an `A`-algebra
`B = A[1/ϖ]`.  The subrings that occur are `R` itself and the intermediate `R`-subalgebras
`R[P/ϖ 0^m]`, `R[Q/ϖ 0^m]` of `L = R[1/ϖ 0]`; here we collect the basic facts those applications
need: `ϖ 0` is a nonzerodivisor, `R → L` is injective, and the image of `R` lies in every
`R`-subalgebra of `L`. -/

section Glue

variable {R : Type u} [CommRing R] (QR : DSMap.PerfectoidData p R)

/-- `ϖ 0` is a nonzerodivisor: `ϖ 0 ^ p = p · (unit)` and `p` is a nonzerodivisor. -/
theorem isSMulRegular_varpi : IsSMulRegular R (QR.ϖ 0) :=
  DSM1p.Perfectoid.varpi_isSMulRegular QR 0

/-- **Injectivity of `R → R[1/ϖ 0]`**, because the powers of the nonzerodivisor `ϖ 0` are
nonzerodivisors. -/
theorem algebraMap_away_injective :
    Function.Injective (algebraMap R (Localization.Away (QR.ϖ 0))) := by
  have hreg : ∀ n : ℕ, IsSMulRegular R (QR.ϖ 0 ^ n) := by
    intro n
    induction n with
    | zero => intro a b hab; simpa using hab
    | succ n ih => rw [pow_succ]; exact ih.mul (isSMulRegular_varpi QR)
  intro x y hxy
  obtain ⟨c, hcx⟩ := (IsLocalization.eq_iff_exists (Submonoid.powers (QR.ϖ 0))
    (Localization.Away (QR.ϖ 0))).mp hxy
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (c : R) (QR.ϖ 0)).mp c.2
  rw [← hn] at hcx
  exact hreg n hcx

/-- The image of `R` inside an `R`-algebra lies in every subalgebra containing a given element
(used for the subalgebras `R[x]` of `L`). -/
theorem algebraMap_mem_adjoin {L : Type*} [CommRing L] [Algebra R L] {x : L} (r : R) :
    algebraMap R L r ∈ Algebra.adjoin R ({x} : Set L) :=
  (Algebra.adjoin R ({x} : Set L)).algebraMap_mem r

/-- `ϖ 0` is a nonzerodivisor on every intermediate `R`-subalgebra `A` of `L = R[1/ϖ 0]`
containing it (cancellation is inherited from `L`, where `ϖ 0` is a unit). -/
theorem isSMulRegular_subalgebra_varpi {A : Subalgebra R (Localization.Away (QR.ϖ 0))}
    (h : algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0) ∈ A) :
    IsSMulRegular A (⟨algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0), h⟩ : A) := by
  intro x y hxy
  refine Subtype.ext ?_
  have h1 : algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0) * (x : Localization.Away (QR.ϖ 0))
      = algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0)
        * (y : Localization.Away (QR.ϖ 0)) := by
    have := congrArg (fun z : A => (z : Localization.Away (QR.ϖ 0))) hxy
    simpa using this
  exact IsUnit.mul_left_cancel (IsLocalization.Away.algebraMap_isUnit (QR.ϖ 0)) h1

/-! ### The localization instance over an intermediate subalgebra

`IsLocalization.Away ⟨ϖ 0, _⟩ L` over an intermediate `R`-subalgebra `A ⊆ L`: this is the instance
that lets `nilp_lem` be applied with `A = R[P/ϖ 0^m]` and `A = R[Q/ϖ 0^m]`.  Mathlib provides no
`Algebra A L` instance for `A : Subalgebra R L` (only `Ring`/`CommRing` instances), so the algebra
structure is supplied explicitly by `RingHom.toAlgebra` of the inclusion `A → L`. -/

/- **Remaining glue step (alternative, cleaner route).**  Instead of the
`IsLocalization.Away ⟨ϖ 0, _⟩ L` instance over an intermediate `R`-subalgebra `A ⊆ L` (which forces
an explicit `Algebra A L` structure via `RingHom.toAlgebra`, and then a fight with the two
`CommSemiring` paths of `Localization.Away`), use the *subring form* of `nilp_lem`: for `A : Subring L`
with the generation hypothesis `∀ z : L, ∃ n a : A, z * ϖ 0^n = (a : L)`, which needs no `Algebra`
instance at all and is the form clauses (i)–(iii) actually consume. -/

/-- **The generation hypothesis for the subring form of `nilp_lem`.**  For an intermediate
`R`-subalgebra `R[x] ⊆ L = R[1/ϖ 0]` (encoded by its underlying `Subring`), every element of `L`
becomes an element of `R[x]` after multiplication by a power of `ϖ 0`: this is the `hgen` of
`nilp_lem_subring`, and it is exactly the `surj` field of the `R`-localization `L`. -/
theorem generates_of_adjoin (x : Localization.Away (QR.ϖ 0)) :
    ∀ z : Localization.Away (QR.ϖ 0), ∃ n : ℕ,
      ∃ a : (Algebra.adjoin R ({x} : Set (Localization.Away (QR.ϖ 0)))).toSubring,
        z * (algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0)) ^ n
          = (a : Localization.Away (QR.ϖ 0)) := by
  intro z
  obtain ⟨m, hm⟩ := IsLocalization.surj (Submonoid.powers (QR.ϖ 0)) z
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (m.2 : R) (QR.ϖ 0)).mp m.2.2
  refine ⟨n, ⟨algebraMap R _ m.1, algebraMap_mem_adjoin (x := x) m.1⟩, ?_⟩
  show z * (algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0)) ^ n
    = algebraMap R (Localization.Away (QR.ϖ 0)) m.1
  rw [← map_pow, hn]
  exact hm

/-! ### Clause (i): from the approximation estimate to `< 1` at every continuous valuation -/

/-- **Clause (i), first step.**  If `Q` satisfies the Česnavičius–Scholze estimate
`|P - Q| ≤ |p| · max(|Q|, |ϖ 0|^{pm})` at every continuous valuation of the unit ball of `R`, then
`P - Q` has value `< 1` at every such valuation: both `|Q| ≤ 1` and `|ϖ 0|^{pm} ≤ 1` hold on the
unit ball, so the estimate is bounded by `|p| < 1`.  This is the hypothesis that the subring form of
`nilp_lem` consumes for clause (i). -/
theorem diff_lt_one_of_estimate {p : ℕ} [Fact p.Prime] {R : Type*} [CommRing R]
    (QR : DSMap.PerfectoidData p R) {P Q : R} (m : ℕ)
    (h : ∀ {Γ₀ : Type u} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),
      IsContinuousValuation (QR.ϖ 0) v → IsUnitBall v Set.univ →
        v (P - Q) ≤ v (p : R) * max (v Q) (v (QR.ϖ 0) ^ (p * m))) :
    ∀ {Γ₀ : Type u} [LinearOrderedCommGroupWithZero Γ₀] (v : Valuation R Γ₀),
      IsContinuousValuation (QR.ϖ 0) v → IsUnitBall v Set.univ → v (P - Q) < 1 := by
  intro Γ₀ _ v hv hball
  have hp : v (p : R) < 1 := Valuation.map_p_lt_one QR v hv hball
  have hQ : v Q ≤ 1 := hball Q (Set.mem_univ Q)
  have hϖ : v (QR.ϖ 0) ≤ 1 := hball _ (Set.mem_univ _)
  have hpow : v (QR.ϖ 0) ^ (p * m) ≤ 1 := by
    induction p * m with
    | zero => simp
    | succ k ih =>
      rw [pow_succ]
      calc v (QR.ϖ 0) ^ k * v (QR.ϖ 0) ≤ 1 * 1 := mul_le_mul' ih hϖ
        _ = 1 := one_mul 1
  have hmax : max (v Q) (v (QR.ϖ 0) ^ (p * m)) ≤ 1 := max_le hQ hpow
  have hprod : v (p : R) * max (v Q) (v (QR.ϖ 0) ^ (p * m)) < 1 := by
    have hle : v (p : R) * max (v Q) (v (QR.ϖ 0) ^ (p * m)) ≤ v (p : R) * 1 :=
      mul_le_mul' le_rfl hmax
    rw [mul_one] at hle
    exact lt_of_le_of_lt hle hp
  exact lt_of_le_of_lt (h (Γ₀ := Γ₀) v hv hball) hprod

/-- **The generation hypothesis for the range subring of `R → L`** (the `A` used for clause (i)):
every element of `L` lies in the range of `R` after multiplying by a power of `ϖ 0`.  Again this is
just the `surj` field of the `R`-localization. -/
theorem generates_of_range :
    ∀ z : Localization.Away (QR.ϖ 0), ∃ n : ℕ,
      ∃ a : (algebraMap R (Localization.Away (QR.ϖ 0))).range,
        z * (algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0)) ^ n
          = (a : Localization.Away (QR.ϖ 0)) := by
  intro z
  obtain ⟨m, hm⟩ := IsLocalization.surj (Submonoid.powers (QR.ϖ 0)) z
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (m.2 : R) (QR.ϖ 0)).mp m.2.2
  refine ⟨n, ⟨algebraMap R _ m.1, ⟨m.1, rfl⟩⟩, ?_⟩
  show z * (algebraMap R (Localization.Away (QR.ϖ 0)) (QR.ϖ 0)) ^ n
    = algebraMap R (Localization.Away (QR.ϖ 0)) m.1
  rw [← map_pow, hn]
  exact hm

end Glue

