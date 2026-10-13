/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.RingTheory.Ideal.isPrime_sup_span_X_sub_one` (piece 0).
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Data.Finsupp.PWO
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Data.Sym.NatCard
import Mathlib.GroupTheory.CosetCover
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.NumberTheory.BernoulliPolynomials
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.MvPolynomial.Groebner
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.IrreducibleQuadratic
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.PicardGroup
import Mathlib.RingTheory.Polynomial.HilbertPoly
import Mathlib.RingTheory.Regular.IsSMulRegular
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.TotallySplit
import Submission.Work.WilE2.BzPort.P53

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.RingTheory.Ideal.isPrime_sup_span_X_sub_one ====
section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false
open MvPolynomial

namespace Commons.RingTheory.Ideal

section HomogeneousAeval

variable {k T : Type*} [CommSemiring k] [CommSemiring T] [Algebra k T] {n : ℕ}
local notation "R" => MvPolynomial (Fin (n+1)) k

theorem monomial_aeval
    [Algebra R T] [IsScalarTower k R T]
    (y : T) (hy : algebraMap R T (MvPolynomial.X 0) * y = 1)
    (s : Fin (n+1) →₀ ℕ) (c : k) :
    MvPolynomial.aeval (fun i : Fin (n+1) => if i = 0 then (1 : T) else algebraMap R T (MvPolynomial.X i) * y)
        (MvPolynomial.monomial s c)
      = algebraMap R T (MvPolynomial.monomial s c) * y ^ s.degree := by
  rw [MvPolynomial.aeval_monomial]
  have hg : ∀ i : Fin (n+1),
      (if i = 0 then (1 : T) else algebraMap R T (MvPolynomial.X i) * y)
        = algebraMap R T (MvPolynomial.X i) * y := by
    intro i
    by_cases hi : i = 0
    · subst hi
      simpa using hy.symm
    · simp only [if_neg hi]
  have hL : s.prod (fun i e => (if i = 0 then (1 : T) else algebraMap R T (MvPolynomial.X i) * y) ^ e)
      = s.prod (fun i e => (algebraMap R T (MvPolynomial.X i) * y) ^ e) :=
    Finsupp.prod_congr (fun i _ => by rw [hg i])
  rw [hL]
  rw [Finsupp.prod_pow]
  have hstep : (∏ i, (algebraMap R T (MvPolynomial.X i) * y) ^ (s i))
      = (∏ i, (algebraMap R T (MvPolynomial.X i)) ^ (s i)) * (∏ i, y ^ (s i)) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    rw [mul_pow]
  rw [hstep]
  rw [show (∏ i : Fin (n+1), y ^ (s i)) = y ^ (∑ i, s i) by
    rw [Finset.prod_pow_eq_pow_sum]]
  rw [Finsupp.degree_eq_sum]
  have hAmono : algebraMap R T (MvPolynomial.monomial s c)
      = (algebraMap k T) c * ∏ i, (algebraMap R T (MvPolynomial.X i)) ^ (s i) := by
    rw [MvPolynomial.monomial_eq]
    rw [show s.prod (fun i e => MvPolynomial.X i ^ e) = ∏ i, (MvPolynomial.X i) ^ (s i) by
      rw [Finsupp.prod_pow]]
    rw [map_mul, map_prod]
    congr 1
    · rw [MvPolynomial.C_eq_algebraMap]
      exact (IsScalarTower.algebraMap_apply k R T c).symm
    · apply Finset.prod_congr rfl
      intro i _
      rw [map_pow]
  rw [hAmono]
  ring

theorem aeval_homogeneous_eq
    [Algebra R T] [IsScalarTower k R T]
    (y : T) (hy : algebraMap R T (MvPolynomial.X 0) * y = 1)
    {f : R} {d : ℕ} (hf : f.IsHomogeneous d) :
    MvPolynomial.aeval (fun i : Fin (n+1) => if i = 0 then (1 : T) else algebraMap R T (MvPolynomial.X i) * y) f
      = algebraMap R T f * y ^ d := by
  have hdeg : ∀ v ∈ f.support, v.degree = d := by
    intro v hv
    rw [Finsupp.degree_apply]
    exact (hf.degree_eq_sum_deg_support hv).symm
  conv_lhs => rw [MvPolynomial.as_sum f]
  rw [map_sum]
  rw [Finset.sum_congr rfl (fun v hv => by rw [monomial_aeval y hy v ((f).coeff v)])]
  rw [Finset.sum_congr rfl (fun v hv => by rw [hdeg v hv])]
  rw [← Finset.sum_mul]
  congr 1
  rw [← map_sum, ← MvPolynomial.as_sum]

theorem aeval_eq_sum_homogeneousComponent
    [Algebra R T] [IsScalarTower k R T]
    (y : T) (hy : algebraMap R T (MvPolynomial.X 0) * y = 1)
    (f : R) :
    MvPolynomial.aeval (fun i : Fin (n+1) => if i = 0 then (1 : T) else algebraMap R T (MvPolynomial.X i) * y) f
      = ∑ d ∈ Finset.range (f.totalDegree + 1),
          algebraMap R T (MvPolynomial.homogeneousComponent d f) * y ^ d := by
  conv_lhs => rw [← MvPolynomial.sum_homogeneousComponent f]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [aeval_homogeneous_eq y hy (MvPolynomial.homogeneousComponent_isHomogeneous d f)]

end HomogeneousAeval

section Main
variable {k : Type*} [Field k] {n : ℕ}
local notation "R" => MvPolynomial (Fin (n+1)) k

theorem isPrime_sup_span_X_sub_one_aux
    (Q : Ideal R) [Q.IsPrime]
    (hQ : ∀ x ∈ Q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ Q)
    (hX : (MvPolynomial.X 0 : R) ∉ Q) :
    (Q ⊔ Ideal.span {(MvPolynomial.X 0 : R) - 1}).IsPrime := by
  classical
  let S := Localization.Away (MvPolynomial.X 0 : R)
  haveI hSaway : IsLocalization.Away (MvPolynomial.X 0 : R) S := inferInstance
  let y : S := IsLocalization.Away.invSelf (MvPolynomial.X 0 : R)
  have hy : algebraMap R S (MvPolynomial.X 0) * y = 1 := IsLocalization.Away.mul_invSelf _
  -- disjointness of powers of X0 from Q
  have hdisj : Disjoint (Submonoid.powers (MvPolynomial.X 0 : R) : Set R) (Q : Set R) := by
    rw [Set.disjoint_left]
    intro m hm hmQ
    obtain ⟨j, rfl⟩ := (Submonoid.mem_powers_iff m (MvPolynomial.X 0)).mp hm
    exact hX (Ideal.IsPrime.mem_of_pow_mem ‹Q.IsPrime› j hmQ)
  -- QS is prime, so S ⧸ QS is a domain
  set QS : Ideal S := Q.map (algebraMap R S) with hQSdef
  haveI hQSprime : QS.IsPrime := by
    rw [hQSdef]
    exact IsLocalization.isPrime_of_isPrime_disjoint
      (Submonoid.powers (MvPolynomial.X 0 : R)) S Q ‹Q.IsPrime› hdisj
  haveI : IsDomain (S ⧸ QS) := inferInstance
  -- the substitution map
  let ρa : R →ₐ[k] S := MvPolynomial.aeval
    (fun i : Fin (n+1) => if i = 0 then (1 : S) else algebraMap R S (MvPolynomial.X i) * y)
  let g' : R →+* (S ⧸ QS) := (Ideal.Quotient.mk QS).comp ρa.toRingHom
  -- X0 - 1 ∈ ker g'
  have hX0ker : (MvPolynomial.X 0 : R) - 1 ∈ RingHom.ker g' := by
    rw [RingHom.mem_ker]
    have h1 : ρa ((MvPolynomial.X 0 : R) - 1) = 0 := by
      rw [map_sub, map_one]
      have : ρa (MvPolynomial.X 0 : R) = 1 := by
        change MvPolynomial.aeval _ (MvPolynomial.X 0) = 1
        rw [MvPolynomial.aeval_X]
        simp
      rw [this, sub_self]
    show g' ((MvPolynomial.X 0 : R) - 1) = 0
    rw [show g' ((MvPolynomial.X 0 : R) - 1) = Ideal.Quotient.mk QS (ρa ((MvPolynomial.X 0 : R) - 1)) from rfl, h1, map_zero]
  have hspan_le : Ideal.span {(MvPolynomial.X 0 : R) - 1} ≤ RingHom.ker g' := by
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact hX0ker
  -- Q ⊆ ker g'
  have hQ_le : Q ≤ RingHom.ker g' := by
    intro q hq
    rw [RingHom.mem_ker]
    have hmem : ρa q ∈ QS := by
      have hsum : ρa q = ∑ d ∈ Finset.range (q.totalDegree + 1),
          algebraMap R S (MvPolynomial.homogeneousComponent d q) * y ^ d :=
        aeval_eq_sum_homogeneousComponent y hy q
      rw [hsum]
      apply Ideal.sum_mem
      intro d _
      exact Ideal.mul_mem_right _ QS (Ideal.mem_map_of_mem (algebraMap R S) (hQ q hq d))
    show g' q = 0
    rw [show g' q = Ideal.Quotient.mk QS (ρa q) from rfl, Ideal.Quotient.eq_zero_iff_mem.mpr hmem]
  -- ker g' ⊆ Q ⊔ span{X0 - 1}
  have hker_le : RingHom.ker g' ≤ Q ⊔ Ideal.span {(MvPolynomial.X 0 : R) - 1} := by
    intro f hf
    rw [RingHom.mem_ker] at hf
    have hmem : ρa f ∈ QS := Ideal.Quotient.eq_zero_iff_mem.mp hf
    let N := f.totalDegree
    let F : ℕ → R := fun i => MvPolynomial.homogeneousComponent i f
    set H : R := ∑ d ∈ Finset.range (N+1),
      F d * (MvPolynomial.X 0)^(N - d) with hHdef
    have hzy : y * (algebraMap R S (MvPolynomial.X 0)) = 1 := by
      rw [mul_comm]; exact hy
    have hpowy : ∀ d ≤ N, y^d * (algebraMap R S (MvPolynomial.X 0))^N
        = (algebraMap R S (MvPolynomial.X 0))^(N-d) := by
      intro d hd
      have h1 : (algebraMap R S (MvPolynomial.X 0))^N
          = (algebraMap R S (MvPolynomial.X 0))^d * (algebraMap R S (MvPolynomial.X 0))^(N-d) := by
        rw [← pow_add, Nat.add_sub_of_le hd]
      rw [h1, ← mul_assoc, ← mul_pow, hzy, one_pow, one_mul]
    have hAH : algebraMap R S H = ρa f * (algebraMap R S (MvPolynomial.X 0))^N := by
      have hsum : ρa f = ∑ d ∈ Finset.range (N + 1),
          algebraMap R S (MvPolynomial.homogeneousComponent d f) * y ^ d :=
        aeval_eq_sum_homogeneousComponent y hy f
      rw [hsum, Finset.sum_mul, hHdef]
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro d hd
      rw [Finset.mem_range] at hd
      have hdN : d ≤ N := Nat.lt_succ_iff.mp hd
      have hL : algebraMap R S (MvPolynomial.homogeneousComponent d f * (MvPolynomial.X 0)^(N - d))
          = algebraMap R S (MvPolynomial.homogeneousComponent d f)
            * (algebraMap R S (MvPolynomial.X 0))^(N-d) := by
        rw [map_mul, map_pow]
      have hR : (algebraMap R S (MvPolynomial.homogeneousComponent d f) * y^d)
            * (algebraMap R S (MvPolynomial.X 0))^N
          = algebraMap R S (MvPolynomial.homogeneousComponent d f)
            * (algebraMap R S (MvPolynomial.X 0))^(N-d) := by
        rw [mul_assoc, hpowy d hdN]
      rw [hL, hR]
    have hunder : QS.under R = Q := by
      rw [hQSdef]
      exact IsLocalization.under_map_of_isPrime_disjoint
        (Submonoid.powers (MvPolynomial.X 0 : R)) S (inferInstance : Q.IsPrime) hdisj
    have hH_mem : H ∈ Q := by
      rw [← hunder, Ideal.mem_under]
      rw [hAH]
      exact Ideal.mul_mem_right _ QS hmem
    have hf_diff : f - H ∈ Ideal.span {(MvPolynomial.X 0 : R) - 1} := by
      have hsplit : f - H = ∑ d ∈ Finset.range (N+1),
          F d * (1 - (MvPolynomial.X 0)^(N-d)) := by
        have hF : f = ∑ i ∈ Finset.range (N+1), F i := by
          change f = ∑ i ∈ Finset.range (N+1), MvPolynomial.homogeneousComponent i f
          simpa using (MvPolynomial.sum_homogeneousComponent f).symm
        calc f - H
            = (∑ i ∈ Finset.range (N+1), F i) - H := by rw [hF]
          _ = (∑ i ∈ Finset.range (N+1), F i)
                - (∑ d ∈ Finset.range (N+1), F d * (MvPolynomial.X 0)^(N-d)) := by rw [hHdef]
          _ = ∑ d ∈ Finset.range (N+1), (F d - F d * (MvPolynomial.X 0)^(N-d)) := by rw [Finset.sum_sub_distrib]
          _ = ∑ d ∈ Finset.range (N+1), F d * (1 - (MvPolynomial.X 0)^(N-d)) := by
              apply Finset.sum_congr rfl
              intro d _
              ring
      rw [hsplit]
      apply Ideal.sum_mem
      intro d _
      apply Ideal.mul_mem_left
      rw [Ideal.mem_span_singleton]
      use -(∑ i ∈ Finset.range (N-d), (MvPolynomial.X 0)^i)
      rw [← geom_sum_mul_neg (MvPolynomial.X 0) (N-d)]
      ring
    have : f = H + (f - H) := by ring
    rw [this]
    refine Ideal.add_mem _ ?_ ?_
    · exact (le_sup_left : Q ≤ Q ⊔ Ideal.span {(MvPolynomial.X 0 : R) - 1}) hH_mem
    · exact (le_sup_right : Ideal.span {(MvPolynomial.X 0 : R) - 1} ≤ Q ⊔ Ideal.span {(MvPolynomial.X 0 : R) - 1}) hf_diff
  have hker : RingHom.ker g' = Q ⊔ Ideal.span {(MvPolynomial.X 0 : R) - 1} :=
    le_antisymm hker_le (sup_le hQ_le hspan_le)
  have e : R ⧸ (Q ⊔ Ideal.span {(MvPolynomial.X 0 : R) - 1}) ≃+* ↥g'.range :=
    hker ▸ RingHom.quotientKerEquivRange g'
  let ψ : R ⧸ (Q ⊔ Ideal.span {(MvPolynomial.X 0 : R) - 1}) →+* (S ⧸ QS) :=
    (Subring.subtype g'.range).comp e.toRingHom
  have hinj : Function.Injective ψ := by
    intro a b hab
    exact e.injective (Subtype.ext hab)
  haveI : IsDomain (R ⧸ (Q ⊔ Ideal.span {(MvPolynomial.X 0 : R) - 1})) :=
    Function.Injective.isDomain ψ hinj
  exact (Ideal.Quotient.isDomain_iff_prime _).mp ‹IsDomain (R ⧸ (Q ⊔ Ideal.span {(MvPolynomial.X 0 : R) - 1}))›

end Main

/-- If `Q` is a homogeneous prime ideal of `k[X₀,…,Xₙ]` with `X₀ ∉ Q`, then the ideal
`Q + (X₀ - 1)` is prime: it is the ideal of the affine chart `X₀ = 1` of the projective
variety cut out by `Q`. -/
theorem isPrime_sup_span_X_sub_one {k : Type*} [Field k] {n : ℕ}
    (Q : Ideal (MvPolynomial (Fin (n+1)) k)) [Q.IsPrime]
    (hQ : ∀ x ∈ Q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ Q)
    (hX : (MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) ∉ Q) :
    (Q ⊔ Ideal.span {(MvPolynomial.X 0 : MvPolynomial (Fin (n+1)) k) - 1}).IsPrime :=
  isPrime_sup_span_X_sub_one_aux Q hQ hX

end Commons.RingTheory.Ideal
end


