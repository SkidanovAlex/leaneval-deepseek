/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.RingTheory.Ideal.card_minimalPrimes_comap_eq` (piece 0).
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
import Submission.Work.WilE2.BzPort.P52

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.RingTheory.Ideal.card_minimalPrimes_comap_eq ====
section

set_option linter.style.haveILetI false

namespace Commons.RingTheory.Ideal

/-- If `φ : A →+* B` is surjective and `q` is a minimal prime over `I ≤ B`, then the contraction
`q.comap φ` is a minimal prime over `I.comap φ`. -/
theorem minimalPrimes_comap_of_surjective {A B : Type*} [CommSemiring A] [CommSemiring B]
    (φ : A →+* B) (hφ : Function.Surjective φ) {I q : Ideal B} (hq : q ∈ I.minimalPrimes) :
    Ideal.comap φ q ∈ (I.comap φ).minimalPrimes := by
  haveI : q.IsPrime := hq.isPrime
  refine ⟨⟨inferInstance, Ideal.comap_mono hq.le⟩, ?_⟩
  intro r hr hle
  haveI : r.IsPrime := hr.1
  obtain ⟨r₀, hr₀, hr₀le⟩ := Ideal.exists_minimalPrimes_le (I := I.comap φ) (J := r) hr.2
  obtain ⟨q₀, hq₀, hq₀eq⟩ := Ideal.exists_minimalPrimes_comap_eq φ r₀ hr₀
  have hle₀ : q₀ ≤ q :=
    (Ideal.comap_le_comap_iff_of_surjective φ hφ q₀ q).1 (by rw [hq₀eq]; exact hr₀le.trans hle)
  have hge : q ≤ q₀ := hq.2 ⟨hq₀.isPrime, hq₀.le⟩ hle₀
  have hEq : r₀ = Ideal.comap φ q := by rw [← hq₀eq, le_antisymm hle₀ hge]
  rw [hEq] at hr₀le
  exact hr₀le

theorem card_minimalPrimes_comap_eq {A B : Type*} [CommSemiring A] [CommSemiring B] (φ : A →+* B)
    (hφ : Function.Surjective φ) (I : Ideal B) :
    Nat.card {p : Ideal A // p ∈ (I.comap φ).minimalPrimes} =
      Nat.card {p : Ideal B // p ∈ I.minimalPrimes} := by
  refine Nat.card_congr ?_
  let fwd : {p : Ideal A // p ∈ (I.comap φ).minimalPrimes} →
      {p : Ideal B // p ∈ I.minimalPrimes} := fun p =>
    ⟨Classical.choose (Ideal.exists_minimalPrimes_comap_eq φ p.1 p.2),
      (Classical.choose_spec (Ideal.exists_minimalPrimes_comap_eq φ p.1 p.2)).1⟩
  have hfwd : ∀ p, Ideal.comap φ (fwd p).1 = p.1 := fun p =>
    (Classical.choose_spec (Ideal.exists_minimalPrimes_comap_eq φ p.1 p.2)).2
  refine
    { toFun := fwd
      invFun := fun q => ⟨Ideal.comap φ q.1, minimalPrimes_comap_of_surjective φ hφ q.2⟩
      left_inv := fun p => Subtype.ext (hfwd p)
      right_inv := ?_ }
  intro q
  apply Subtype.ext
  apply Ideal.comap_injective_of_surjective φ hφ
  rw [hfwd ⟨Ideal.comap φ q.1, minimalPrimes_comap_of_surjective φ hφ q.2⟩]

end Commons.RingTheory.Ideal

end


