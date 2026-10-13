/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.RingTheory.Ideal.Hilbert.hilbert_sum_upper_bound` (piece 1).
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
import Submission.Work.WilE2.BzPort.P32

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false

attribute [local instance] Commons.Algebra.MvPolynomial.idealOfVars_isMaximal

set_option autoImplicit true

-- ==== from Submission.Commons.RingTheory.Ideal.Hilbert.hilbert_sum_upper_bound ====
section

open MvPolynomial

namespace Commons.RingTheory.Ideal.Hilbert

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## An arithmetic lemma -/

theorem sum_bound_of_recursion {H H' : ℕ → ℕ} {e : ℕ} (he : 1 ≤ e)
    (hrec : ∀ u, e ≤ u → H u ≤ H (u - e) + H' u) {n C' : ℕ}
    (h' : ∀ t : ℕ, ∑ u ∈ Finset.range (t + 1), H' u ≤ C' * (t + 1) ^ n) :
    ∃ C : ℕ, ∀ t : ℕ, ∑ u ∈ Finset.range (t + 1), H u ≤ C * (t + 1) ^ (n + 1) := by
  classical
  set B : ℕ := ∑ u ∈ Finset.range e, H u with hB
  have hmono : ∀ s t : ℕ, s ≤ t →
      ∑ u ∈ Finset.range (s + 1), H u ≤ ∑ u ∈ Finset.range (t + 1), H u := by
    intro s t hst
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro u hu; simp only [Finset.mem_range] at hu ⊢; omega
    · intro u _ _; exact Nat.zero_le _
  have hrec_sum : ∀ t, e ≤ t →
      (∑ u ∈ Finset.range (t + 1), H u)
        ≤ B + (∑ u ∈ Finset.range (t - e + 1), H u)
          + ∑ u ∈ Finset.range (t + 1), H' u := by
    intro t ht
    have hsplit : ∑ u ∈ Finset.range (t + 1), H u
        = B + ∑ j ∈ Finset.range (t + 1 - e), H (e + j) := by
      have h := Finset.sum_range_add (fun u => H u) e (t + 1 - e)
      rw [show e + (t + 1 - e) = t + 1 from by omega] at h
      rw [h, hB]
    have hrec2 : ∑ j ∈ Finset.range (t + 1 - e), H (e + j)
        ≤ (∑ j ∈ Finset.range (t + 1 - e), H j)
          + ∑ j ∈ Finset.range (t + 1 - e), H' (e + j) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_le_sum (fun j hj => ?_)
      have h2 := hrec (e + j) (by omega)
      rw [show e + j - e = j from by omega] at h2
      exact h2
    have hH' : ∑ j ∈ Finset.range (t + 1 - e), H' (e + j)
        ≤ ∑ u ∈ Finset.range (t + 1), H' u := by
      have hiff : ∑ j ∈ Finset.range (t + 1 - e), H' (e + j)
          = ∑ u ∈ Finset.Ico e (t + 1), H' u := by
        rw [Finset.sum_Ico_eq_sum_range]
      rw [hiff]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro u hu; simp only [Finset.mem_Ico, Finset.mem_range] at hu ⊢; omega
      · intro u _ _; exact Nat.zero_le _
    have hSeq : ∑ j ∈ Finset.range (t + 1 - e), H j = ∑ u ∈ Finset.range (t - e + 1), H u := by
      have : t + 1 - e = t - e + 1 := by omega
      rw [this]
    rw [hsplit]
    calc B + ∑ j ∈ Finset.range (t + 1 - e), H (e + j)
        ≤ B + ((∑ j ∈ Finset.range (t + 1 - e), H j)
            + ∑ j ∈ Finset.range (t + 1 - e), H' (e + j)) := add_le_add_right hrec2 B
      _ = B + ((∑ u ∈ Finset.range (t - e + 1), H u)
            + ∑ j ∈ Finset.range (t + 1 - e), H' (e + j)) := by rw [hSeq]
      _ ≤ B + ((∑ u ∈ Finset.range (t - e + 1), H u)
            + ∑ u ∈ Finset.range (t + 1), H' u) :=
          add_le_add_right (add_le_add_right hH' _) B
      _ = B + (∑ u ∈ Finset.range (t - e + 1), H u)
            + ∑ u ∈ Finset.range (t + 1), H' u := by ring
  have key : ∀ t, ∑ u ∈ Finset.range (t + 1), H u
      ≤ B * (t + 1) + C' * ∑ v ∈ Finset.range (t + 1), (v + 1) ^ n := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      rcases lt_or_ge t e with ht | ht
      · have h1 : ∑ u ∈ Finset.range (t + 1), H u ≤ B := by
          rw [hB]
          have := hmono t (e - 1) (by omega)
          simpa [Nat.sub_add_cancel he] using this
        have h2 : B ≤ B * (t + 1) := by
          calc B = B * 1 := (mul_one B).symm
            _ ≤ B * (t + 1) := Nat.mul_le_mul_left B (by omega)
        have h3 : 0 ≤ C' * ∑ v ∈ Finset.range (t + 1), (v + 1) ^ n := Nat.zero_le _
        linarith
      · have hlt : t - e < t := by omega
        have hIH := ih (t - e) hlt
        have hs : ∑ u ∈ Finset.range (t - e + 1), H u
            ≤ B * (t - e + 1) + C' * ∑ v ∈ Finset.range (t - e + 1), (v + 1) ^ n := hIH
        have hS := hrec_sum t ht
        have h'c := h' t
        have hpoly : (∑ v ∈ Finset.range (t - e + 1), (v + 1) ^ n) + (t + 1) ^ n
            ≤ ∑ v ∈ Finset.range (t + 1), (v + 1) ^ n := by
          have hdecomp := Finset.sum_range_add (fun v => (v + 1) ^ n) (t - e + 1) e
          rw [show t - e + 1 + e = t + 1 from by omega] at hdecomp
          rw [hdecomp]
          have hmem : e - 1 ∈ Finset.range e := by simp only [Finset.mem_range]; omega
          have hterm : ((t - e + 1 + (e - 1)) + 1) ^ n
              ≤ ∑ i ∈ Finset.range e, ((t - e + 1 + i) + 1) ^ n :=
            Finset.single_le_sum (f := fun i => ((t - e + 1 + i) + 1) ^ n)
              (fun i _ => Nat.zero_le _) hmem
          have heq : (t - e + 1 + (e - 1)) + 1 = t + 1 := by omega
          rw [heq] at hterm
          linarith
        have hBt : B * (t - e + 1) + B ≤ B * (t + 1) := by
          have : B * (t - e + 1) + B = B * (t - e + 2) := by ring
          rw [this]
          exact Nat.mul_le_mul_left B (by omega)
        have hC : C' * (∑ v ∈ Finset.range (t - e + 1), (v + 1) ^ n) + C' * (t + 1) ^ n
            ≤ C' * ∑ v ∈ Finset.range (t + 1), (v + 1) ^ n := by
          rw [← Nat.mul_add]
          exact Nat.mul_le_mul_left C' hpoly
        calc ∑ u ∈ Finset.range (t + 1), H u
            ≤ B + (∑ u ∈ Finset.range (t - e + 1), H u) + ∑ u ∈ Finset.range (t + 1), H' u := hS
          _ ≤ B + (B * (t - e + 1) + C' * ∑ v ∈ Finset.range (t - e + 1), (v + 1) ^ n)
                + C' * (t + 1) ^ n := by linarith
          _ = (B * (t - e + 1) + B) + (C' * (∑ v ∈ Finset.range (t - e + 1), (v + 1) ^ n)
                + C' * (t + 1) ^ n) := by ring
          _ ≤ B * (t + 1) + C' * ∑ v ∈ Finset.range (t + 1), (v + 1) ^ n := by linarith
  refine ⟨B + C', fun t => ?_⟩
  have h1 := key t
  have h2 : ∑ v ∈ Finset.range (t + 1), (v + 1) ^ n ≤ (t + 1) * (t + 1) ^ n := by
    calc ∑ v ∈ Finset.range (t + 1), (v + 1) ^ n
        ≤ ∑ v ∈ Finset.range (t + 1), (t + 1) ^ n := by
          apply Finset.sum_le_sum
          intro v hv
          simp only [Finset.mem_range] at hv
          exact Nat.pow_le_pow_left (by omega) n
      _ = (t + 1) * (t + 1) ^ n := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hBle : B * (t + 1) ≤ B * (t + 1) ^ (n + 1) := by
    apply Nat.mul_le_mul_left
    calc (t + 1) = (t + 1) ^ 1 := (pow_one _).symm
      _ ≤ (t + 1) ^ (n + 1) := Nat.pow_le_pow_right (by omega) (by omega)
  have hCle : C' * ∑ v ∈ Finset.range (t + 1), (v + 1) ^ n ≤ C' * (t + 1) ^ (n + 1) := by
    rw [show (t + 1) ^ (n + 1) = (t + 1) * (t + 1) ^ n from pow_succ' _ _]
    exact Nat.mul_le_mul_left C' h2
  calc ∑ u ∈ Finset.range (t + 1), H u
      ≤ B * (t + 1) + C' * ∑ v ∈ Finset.range (t + 1), (v + 1) ^ n := h1
    _ ≤ (B + C') * (t + 1) ^ (n + 1) := by
        rw [add_mul]
        exact add_le_add hBle hCle

/-! ## The main bound -/

theorem hilbert_sum_upper_bound {k : Type*} [Field k] {m : ℕ}
    (q : Ideal (MvPolynomial (Fin m) k))
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    (d : ℕ) (hd : ringKrullDim (MvPolynomial (Fin m) k ⧸ q) = (d : WithBot ℕ∞)) :
    ∃ C : ℕ, ∀ t : ℕ, (∑ u ∈ Finset.range (t + 1), Module.finrank k
        (Submodule.map (q.mkQ.restrictScalars k)
          (MvPolynomial.homogeneousSubmodule (Fin m) k u))) ≤ C * (t + 1) ^ d := by
  classical
  have key : ∀ d : ℕ, ∀ (q : Ideal (MvPolynomial (Fin m) k)),
      (∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q) →
      ringKrullDim (MvPolynomial (Fin m) k ⧸ q) ≤ (d : WithBot ℕ∞) →
      ∃ C : ℕ, ∀ t : ℕ, (∑ u ∈ Finset.range (t + 1), hilbertFun q
          (MvPolynomial.homogeneousSubmodule (Fin m) k u)) ≤ C * (t + 1) ^ d := by
    intro d
    induction d with
    | zero =>
      intro q hq hle
      haveI : IsArtinianRing k := inferInstance
      haveI : Algebra.FiniteType k (MvPolynomial (Fin m) k ⧸ q) := Algebra.FiniteType.quotient k q
      haveI hfin : Module.Finite k (MvPolynomial (Fin m) k ⧸ q) := by
        rw [Module.finite_iff_krullDimLE_zero, Ring.krullDimLE_iff]
        exact hle
      refine ⟨Module.finrank k (MvPolynomial (Fin m) k ⧸ q), fun t => ?_⟩
      have h := Commons.Algebra.MvPolynomial.sum_finrank_homogeneous_le_finrank q hq t
      simpa [hilbertFun, pow_one] using h
    | succ n ih =>
      intro q hq hle
      by_cases hcase : ringKrullDim (MvPolynomial (Fin m) k ⧸ q) ≤ ((n : ℕ) : WithBot ℕ∞)
      · obtain ⟨C, hC⟩ := ih q hq hcase
        refine ⟨C, fun t => ?_⟩
        calc (∑ u ∈ Finset.range (t + 1), hilbertFun q
                (MvPolynomial.homogeneousSubmodule (Fin m) k u))
            ≤ C * (t + 1) ^ n := hC t
          _ ≤ C * (t + 1) ^ (n + 1) :=
              Nat.mul_le_mul_left C (Nat.pow_le_pow_right (by omega) (by omega))
      · have hqne : q ≠ ⊤ := by
          intro hqt
          haveI : Subsingleton (MvPolynomial (Fin m) k ⧸ q) :=
            Ideal.Quotient.subsingleton_iff.mpr hqt
          rw [ringKrullDim_eq_bot_of_subsingleton] at hcase
          exact absurd (bot_le : (⊥ : WithBot ℕ∞) ≤ ((n : ℕ) : WithBot ℕ∞)) hcase
        have hPfin : (q.minimalPrimes : Set (Ideal (MvPolynomial (Fin m) k))).Finite :=
          Ideal.finite_minimalPrimes_of_isNoetherianRing (MvPolynomial (Fin m) k) q
        set P : Finset (Ideal (MvPolynomial (Fin m) k)) := hPfin.toFinset with hPdef
        have hPmem : ∀ p, p ∈ P ↔ p ∈ q.minimalPrimes := by
          intro p; rw [hPdef]; exact Set.Finite.mem_toFinset hPfin
        obtain ⟨e, f, hfhom, hfI, hfnot⟩ := homogeneous_prime_avoidance
          (MvPolynomial.idealOfVars (Fin m) k)
          (fun x hx j => idealOfVars_homogeneousComponent_mem hx j) P
          (fun p hp => ((hPmem p).mp hp).1.1)
          (fun p hp x hx j => minimalPrimes_homogeneousComponent_mem hq ((hPmem p).mp hp) x hx j)
          (fun p hp => by
            intro hle'
            have h0 := ringKrullDim_le_zero_of_minimalPrimes_idealOfVars_le hq ((hPmem p).mp hp) hle'
            exact hcase (le_trans h0 (show ((0:ℕ) : WithBot ℕ∞) ≤ ((n : ℕ) : WithBot ℕ∞) from by
              exact_mod_cast Nat.zero_le n)))
        have he1 : 1 ≤ e := by
          rw [Nat.one_le_iff_ne_zero]
          intro he0
          have hcoeff : f.coeff 0 = 0 := (mem_idealOfVars_iff_coeff_zero_hub f).mp hfI
          have h1 : MvPolynomial.homogeneousComponent 0 f = f :=
            MvPolynomial.homogeneousComponent_of_mem
              ((MvPolynomial.mem_homogeneousSubmodule 0 f).mpr (he0 ▸ hfhom))
          rw [MvPolynomial.homogeneousComponent_zero, hcoeff, MvPolynomial.C_0] at h1
          obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes hqne
          exact (hfnot p ((hPmem p).mpr hp)) (h1 ▸ p.zero_mem)
        have hq' : ∀ x ∈ q ⊔ Ideal.span {f}, ∀ j,
            MvPolynomial.homogeneousComponent j x ∈ q ⊔ Ideal.span {f} := by
          intro x hx j
          have hq_hom : Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k) q := by
            rw [Ideal.IsHomogeneous.iff_eq]
            refine le_antisymm (Ideal.toIdeal_homogeneousCore_le _ q) ?_
            intro y hy
            rw [← MvPolynomial.sum_homogeneousComponent y]
            refine Ideal.sum_mem _ fun j _ => ?_
            exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem
              ⟨j, MvPolynomial.homogeneousComponent_mem j y⟩ (hq y hy j)
          have hhom : Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k)
              (q ⊔ Ideal.span {f}) := hq_hom.sup (homogeneous_span_singleton hfhom)
          exact (MvPolynomial.mem_iff_homogeneousComponent_mem hhom x).mp hx j
        have hdrop : ringKrullDim (MvPolynomial (Fin m) k ⧸ (q ⊔ Ideal.span {f}))
            ≤ ((n : ℕ) : WithBot ℕ∞) := by
          exact ringKrullDim_quotient_sup_span_le q f
            (fun p hp => hfnot p ((hPmem p).mpr hp)) hle
        obtain ⟨C', hC'⟩ := ih (q ⊔ Ideal.span {f}) hq' hdrop
        have hrec : ∀ u, e ≤ u → hilbertFun q (MvPolynomial.homogeneousSubmodule (Fin m) k u)
            ≤ hilbertFun q (MvPolynomial.homogeneousSubmodule (Fin m) k (u - e))
              + hilbertFun (q ⊔ Ideal.span {f}) (MvPolynomial.homogeneousSubmodule (Fin m) k u) :=
          fun u hu => hilbertFun_recursion q hq hfhom u hu
        exact sum_bound_of_recursion he1 hrec hC'
  have := key d q hq (le_of_eq hd)
  simpa [hilbertFun] using this

end Commons.RingTheory.Ideal.Hilbert
end


