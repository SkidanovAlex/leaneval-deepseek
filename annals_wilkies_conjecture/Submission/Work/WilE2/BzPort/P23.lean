/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.RingTheory.KrullDimension.one_le_quotient_of_ne_idealOfVars` (piece 0).
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
import Submission.Work.WilE2.BzPort.P22

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.RingTheory.KrullDimension.one_le_quotient_of_ne_idealOfVars ====
section

namespace Commons.RingTheory.KrullDimension

/-- Every element of a homogeneous prime ideal in a polynomial ring over a field has vanishing
constant coefficient, hence lies in the ideal of variables. -/
lemma le_idealOfVars_of_homogeneous_prime {k : Type*} [Field k] {m : ℕ}
    (q : Ideal (MvPolynomial (Fin m) k)) [q.IsPrime]
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q) :
    q ≤ MvPolynomial.idealOfVars (Fin m) k := by
  intro x hx
  have hc0 : (x).coeff 0 = 0 := by
    have h0 : MvPolynomial.homogeneousComponent 0 x ∈ q := hq x hx 0
    rw [MvPolynomial.homogeneousComponent_zero] at h0
    by_contra hne
    have hunit : (MvPolynomial.C (((x).coeff 0)⁻¹) : MvPolynomial (Fin m) k) *
        MvPolynomial.C ((x).coeff 0) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hne, map_one]
    have h1 : (1 : MvPolynomial (Fin m) k) ∈ q := by
      rw [← hunit]
      exact Ideal.mul_mem_left q _ h0
    exact Ideal.one_notMem q h1
  have hidV : MvPolynomial.idealOfVars (Fin m) k
      = Ideal.span (MvPolynomial.X '' (Set.univ : Set (Fin m))) := by
    rw [MvPolynomial.idealOfVars, Set.image_univ]
  rw [hidV, MvPolynomial.mem_ideal_span_X_image]
  intro d hd
  rw [MvPolynomial.mem_support_iff] at hd
  have hd0 : d ≠ 0 := by
    intro hdz
    exact hd (by rw [hdz]; exact hc0)
  obtain ⟨i, hi⟩ : ∃ i, d i ≠ 0 := by
    by_contra h
    simp only [not_exists, ne_eq, not_not] at h
    exact hd0 (Finsupp.ext h)
  exact ⟨i, Set.mem_univ i, hi⟩

theorem one_le_quotient_of_ne_idealOfVars {k : Type*} [Field k] {m : ℕ}
    (q : Ideal (MvPolynomial (Fin m) k)) [q.IsPrime]
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    (hqM : q ≠ MvPolynomial.idealOfVars (Fin m) k) :
    (1 : WithBot ℕ∞) ≤ ringKrullDim (MvPolynomial (Fin m) k ⧸ q) := by
  have hqle := le_idealOfVars_of_homogeneous_prime q hq
  -- The ideal of variables is proper.
  have hIdV_ne_top : MvPolynomial.idealOfVars (Fin m) k ≠ ⊤ := by
    intro htop
    have hle_ker : MvPolynomial.idealOfVars (Fin m) k ≤
        RingHom.ker (MvPolynomial.constantCoeff : MvPolynomial (Fin m) k →+* k) := by
      rw [MvPolynomial.idealOfVars, Ideal.span_le]
      rintro x ⟨i, rfl⟩
      simp
    have h1 : (1 : MvPolynomial (Fin m) k) ∈ MvPolynomial.idealOfVars (Fin m) k := by
      rw [htop]; exact Submodule.mem_top
    have hmem := hle_ker h1
    rw [RingHom.mem_ker] at hmem
    simp at hmem
  -- Build a prime ideal strictly above `q`, maximal above the ideal of variables.
  obtain ⟨M, hMmax, hIdVleM⟩ :=
    Ideal.exists_le_maximal (MvPolynomial.idealOfVars (Fin m) k) hIdV_ne_top
  have hqMle : q ≤ M := hqle.trans hIdVleM
  have hMne : M ≠ q := by
    intro heq
    have hle : MvPolynomial.idealOfVars (Fin m) k ≤ q := heq ▸ hIdVleM
    exact hqM (le_antisymm hqle hle)
  have hMprime : M.IsPrime := hMmax.isPrime
  let f : MvPolynomial (Fin m) k →+* (MvPolynomial (Fin m) k ⧸ q) := Ideal.Quotient.mk q
  have hker_le : RingHom.ker f ≤ M := by
    show RingHom.ker (Ideal.Quotient.mk q) ≤ M
    rw [Ideal.mk_ker]
    exact hqMle
  have hmap_prime : (M.map f).IsPrime :=
    Ideal.map_isPrime_of_surjective (f := f) Ideal.Quotient.mk_surjective (I := M)
      (H := hMprime) hker_le
  have hmap_ne_bot : M.map f ≠ ⊥ := fun h => by
    rw [Ideal.map_eq_bot_iff_le_ker (I := M) f] at h
    rw [Ideal.mk_ker] at h
    exact hMne (le_antisymm h hqMle)
  rw [ringKrullDim, Order.one_le_krullDim_iff]
  refine ⟨⟨⊥, inferInstance⟩, ⟨M.map f, hmap_prime⟩, ?_⟩
  rw [← PrimeSpectrum.asIdeal_lt_asIdeal]
  exact lt_of_le_of_ne bot_le (Ne.symm hmap_ne_bot)

end Commons.RingTheory.KrullDimension
end


