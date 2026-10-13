/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.Algebra.MvPolynomial.sum_finrank_homogeneous_le_finrank` (piece 0).
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
import Submission.Work.WilE2.BzPort.P30

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.Algebra.MvPolynomial.sum_finrank_homogeneous_le_finrank ====
section

namespace Commons.Algebra.MvPolynomial

set_option linter.style.haveILetI false in
/-- If `I` is a graded (homogeneous) ideal of `MvPolynomial σ K` and the quotient is finite
dimensional, then for every bound `M` the sum of the `K`-dimensions of the images in the
quotient of the homogeneous pieces of degree `< M` is bounded by the dimension of the quotient.
This is the degree-independence (graded direct sum) of `MvPolynomial σ K ⧸ I`. -/
theorem finrank_sum_map_homogeneousSubmodule_le {σ K : Type*} [Field K] [Fintype σ]
    [DecidableEq σ] (I : Ideal (MvPolynomial σ K))
    (hI : ∀ (j : ℕ) (p : MvPolynomial σ K),
      p ∈ I → MvPolynomial.homogeneousComponent j p ∈ I)
    [Module.Finite K (MvPolynomial σ K ⧸ I)] (M : ℕ) :
    ∑ j : Fin M, Module.finrank K ↥(Submodule.map ((I.mkQ).restrictScalars K)
        (MvPolynomial.homogeneousSubmodule σ K j.val)) ≤
      Module.finrank K (MvPolynomial σ K ⧸ I) := by
  classical
  let S : ℕ → Submodule K (MvPolynomial σ K ⧸ I) := fun j =>
    Submodule.map ((I.mkQ).restrictScalars K) (MvPolynomial.homogeneousSubmodule σ K j)
  have hker : ∀ p : MvPolynomial σ K, (I.mkQ.restrictScalars K) p = 0 ↔ p ∈ I := by
    intro p
    rw [LinearMap.restrictScalars_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  let F : ((j : Fin M) → ↥(S j.val)) →ₗ[K] (MvPolynomial σ K ⧸ I) :=
    { toFun := fun x => ∑ j : Fin M, ((x j : ↥(S j.val)) : MvPolynomial σ K ⧸ I)
      map_add' := fun x y => by
        simp only [Pi.add_apply, Submodule.coe_add, Finset.sum_add_distrib]
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, Submodule.coe_smul, Finset.smul_sum, RingHom.id_apply] }
  have hF_apply : ∀ x, F x = ∑ j : Fin M, ((x j : ↥(S j.val)) : MvPolynomial σ K ⧸ I) :=
    fun x => rfl
  have hzero : ∀ z : (j : Fin M) → ↥(S j.val), F z = 0 → z = 0 := by
    intro z hz0
    choose t ht_mem ht_eq using fun j : Fin M => Submodule.mem_map.mp (z j).property
    have hqP : (I.mkQ.restrictScalars K) (∑ j : Fin M, t j) = 0 := by
      rw [map_sum]
      have hsum : (∑ j : Fin M, (I.mkQ.restrictScalars K) (t j))
          = ∑ j : Fin M, ((z j : ↥(S j.val)) : MvPolynomial σ K ⧸ I) :=
        Finset.sum_congr rfl (fun j _ => ht_eq j)
      rw [hsum, ← hF_apply z]; exact hz0
    have hP : (∑ j : Fin M, t j) ∈ I := (hker _).mp hqP
    funext i
    apply Subtype.ext
    show ((z i : ↥(S i.val)) : MvPolynomial σ K ⧸ I) = 0
    rw [← ht_eq i]
    apply (hker (t i)).mpr
    have h1 : (∑ j : Fin M, MvPolynomial.homogeneousComponent i.val (t j)) ∈ I := by
      have hh := hI i.val (∑ j : Fin M, t j) hP
      rwa [map_sum] at hh
    have heq : (∑ j : Fin M, MvPolynomial.homogeneousComponent i.val (t j))
        = ∑ j : Fin M, (if i.val = j.val then t j else 0) :=
      Finset.sum_congr rfl (fun j _ =>
        MvPolynomial.homogeneousComponent_of_mem (ht_mem j))
    have hsum2 : (∑ j : Fin M, (if i.val = j.val then t j else 0)) = t i := by
      rw [Fintype.sum_eq_single i]
      · simp
      · intro j hj
        rw [if_neg (fun h => hj (Fin.ext h).symm)]
    rw [heq, hsum2] at h1
    exact h1
  have hinj : Function.Injective F := by
    intro x y hxy
    have h0 : F (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hres := hzero (x - y) h0
    exact sub_eq_zero.mp hres
  haveI : ∀ j : Fin M, Module.Finite K ↥(S j.val) := fun j =>
    Module.Finite.of_fg (Submodule.FG.map ((I.mkQ).restrictScalars K)
      (MvPolynomial.homogeneousSubmodule_fg σ K j.val))
  have hle := LinearMap.finrank_le_finrank_of_injective (f := F) hinj
  rwa [Module.finrank_pi_fintype] at hle

theorem sum_finrank_homogeneous_le_finrank {k : Type*} [Field k] {m : ℕ}
    (q : Ideal (MvPolynomial (Fin m) k))
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    [Module.Finite k (MvPolynomial (Fin m) k ⧸ q)] :
    ∀ t : ℕ, (∑ u ∈ Finset.range (t + 1), Module.finrank k
      (Submodule.map (q.mkQ.restrictScalars k) (MvPolynomial.homogeneousSubmodule (Fin m) k u)))
      ≤ Module.finrank k (MvPolynomial (Fin m) k ⧸ q) := by
  intro t
  have h := finrank_sum_map_homogeneousSubmodule_le (σ := Fin m) (K := k) q
    (fun j p hp => hq p hp j) (t + 1)
  have h2 : (∑ u ∈ Finset.range (t + 1), Module.finrank k
        (Submodule.map (q.mkQ.restrictScalars k)
          (MvPolynomial.homogeneousSubmodule (Fin m) k u)))
      = ∑ j : Fin (t + 1), Module.finrank k
        (Submodule.map (q.mkQ.restrictScalars k)
          (MvPolynomial.homogeneousSubmodule (Fin m) k j.val)) :=
    (Fin.sum_univ_eq_sum_range (fun u => Module.finrank k
      (Submodule.map (q.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k u))) (t + 1)).symm
  rw [h2]
  exact h

end Commons.Algebra.MvPolynomial
end


