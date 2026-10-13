/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.RingTheory.Ideal.Hilbert.hilbertFun_eq_sum_hilbertFun_sup_span_X` (piece 0).
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
import Submission.Work.WilE2.BzPort.P42

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.RingTheory.Ideal.Hilbert.hilbertFun_eq_sum_hilbertFun_sup_span_X ====
section

set_option linter.style.haveILetI false

open MvPolynomial
open Commons.RingTheory.Ideal.Hilbert

namespace Commons.RingTheory.Ideal.Hilbert

lemma hilbertFun_homogeneousSubmodule_zero {k : Type*} [Field k] {m : ℕ}
    (I : Ideal (MvPolynomial (Fin m) k)) (hI : I ≠ ⊤) :
    hilbertFun I (MvPolynomial.homogeneousSubmodule (Fin m) k 0) = 1 := by
  classical
  haveI : Module.Finite k ↥(MvPolynomial.homogeneousSubmodule (Fin m) k 0) :=
    Module.Finite.of_fg (MvPolynomial.homogeneousSubmodule_fg (Fin m) k 0)
  rw [hilbertFun_eq_sub]
  have hbot : MvPolynomial.homogeneousSubmodule (Fin m) k 0 ⊓ I.restrictScalars k = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [Submodule.mem_inf] at hx
    obtain ⟨hxV, hxI⟩ := hx
    rw [MvPolynomial.homogeneousSubmodule_zero] at hxV
    obtain ⟨y, hy⟩ := Submodule.mem_one.mp hxV
    by_contra hx0
    have hy0 : y ≠ 0 := fun hyy => hx0 (by rw [← hy, hyy, map_zero])
    have hsmul : y⁻¹ • x = 1 := by
      rw [← hy, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hy0, map_one]
    have h1I : (1 : MvPolynomial (Fin m) k) ∈ I := by
      rw [← hsmul]
      exact (I.restrictScalars k).smul_mem y⁻¹ hxI
    exact hI ((Ideal.eq_top_iff_one I).mpr h1I)
  rw [hbot, MvPolynomial.homogeneousSubmodule_zero, Submodule.one_eq_span,
    finrank_span_singleton (one_ne_zero)]
  simp

lemma hilbertFun_succ {k : Type*} [Field k] {m : ℕ}
    (p : Ideal (MvPolynomial (Fin m) k)) [p.IsPrime]
    (hp : ∀ x ∈ p, ∀ j, MvPolynomial.homogeneousComponent j x ∈ p)
    {i : Fin m} (hf : MvPolynomial.X i ∉ p) (u : ℕ) :
    hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k (u+1))
      = hilbertFun p (MvPolynomial.homogeneousSubmodule (Fin m) k u)
        + hilbertFun (p ⊔ Ideal.span {MvPolynomial.X i})
            (MvPolynomial.homogeneousSubmodule (Fin m) k (u+1)) := by
  classical
  let R := MvPolynomial (Fin m) k
  let t : R := MvPolynomial.X i
  let J : Ideal R := p ⊔ Ideal.span {t}
  let V : ℕ → Submodule k R := fun j => MvPolynomial.homogeneousSubmodule (Fin m) k j
  let A : ℕ → Submodule k (R ⧸ p) := fun j => Submodule.map (p.mkQ.restrictScalars k) (V j)
  let C : ℕ → Submodule k (R ⧸ J) := fun j => Submodule.map (J.mkQ.restrictScalars k) (V j)
  change Module.finrank k ↥(A (u+1)) = Module.finrank k ↥(A u) + Module.finrank k ↥(C (u+1))
  let σ : R ⧸ p →ₗ[k] R ⧸ J := (Ideal.Quotient.factorₐ k (le_sup_left)).toLinearMap
  have hσ : ∀ x : R, σ ((p.mkQ.restrictScalars k) x) = (J.mkQ.restrictScalars k) x := by
    intro x
    simp only [Submodule.mkQ_apply, LinearMap.restrictScalars_apply, σ, AlgHom.toLinearMap_apply,
      Ideal.Quotient.factorₐ_apply]
    rw [Ideal.Quotient.mk_eq_mk, Ideal.Quotient.factor_mk]
    exact (Ideal.Quotient.mk_eq_mk x).symm
  have hC : ∀ j, C j = Submodule.map σ (A j) := by
    intro j
    apply le_antisymm
    · intro y hy
      rw [Submodule.mem_map] at hy ⊢
      obtain ⟨x, hx, rfl⟩ := hy
      exact ⟨(p.mkQ.restrictScalars k) x, ⟨x, hx, rfl⟩, (hσ x).symm⟩
    · intro y hy
      rw [Submodule.mem_map] at hy ⊢
      obtain ⟨z, hz, rfl⟩ := hy
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hz
      exact ⟨x, hx, hσ x⟩
  let mσ : R ⧸ p →ₗ[k] R ⧸ p :=
    (LinearMap.mulLeft (R ⧸ p) (Ideal.Quotient.mk p t)).restrictScalars k
  have hmσ : ∀ x, mσ x = (Ideal.Quotient.mk p t) * x := by
    intro x
    simp [mσ, LinearMap.mulLeft_apply]
  have hmσ_π : ∀ x : R, mσ ((p.mkQ.restrictScalars k) x) = (p.mkQ.restrictScalars k) (t * x) := by
    intro x
    rw [hmσ]
    simp only [Submodule.mkQ_apply, LinearMap.restrictScalars_apply]
    rw [Ideal.Quotient.mk_eq_mk]
    exact (map_mul (Ideal.Quotient.mk p) t x).symm
  have hmem : ∀ x ∈ A u, mσ x ∈ A (u+1) := by
    intro x hx
    rw [Submodule.mem_map] at hx ⊢
    obtain ⟨v, hv, rfl⟩ := hx
    refine ⟨t * v, ?_, (hmσ_π v).symm⟩
    rw [MvPolynomial.mem_homogeneousSubmodule]
    have hv' : v.IsHomogeneous u := (MvPolynomial.mem_homogeneousSubmodule u v).mp hv
    have hmul : (MvPolynomial.X i * v).IsHomogeneous (1 + u) :=
      (MvPolynomial.isHomogeneous_X k i).mul hv'
    rw [Nat.add_comm 1 u] at hmul
    exact hmul
  let f : A u →ₗ[k] A (u+1) := LinearMap.restrict mσ hmem
  have hf_apply : ∀ y : A u, ((f y : A (u+1)) : R ⧸ p) = mσ (y : R ⧸ p) := fun y => rfl
  let g : A (u+1) →ₗ[k] R ⧸ J := σ.comp (Submodule.subtype (A (u+1)))
  have hg_apply : ∀ x : A (u+1), g x = σ (x : R ⧸ p) := fun x => rfl
  have hg_range : g.range = C (u+1) := by
    rw [hC (u+1)]
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : R ⧸ p), x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hmσ_inj : ∀ z ∈ A u, mσ z = 0 → z = 0 := by
    intro z hz hz0
    obtain ⟨w, hw, hwz⟩ := Submodule.mem_map.mp hz
    have ht_w : t * w ∈ p := by
      have h1 : (p.mkQ.restrictScalars k) (t * w) = 0 := by
        rw [← hmσ_π w, hwz]
        exact hz0
      simp only [LinearMap.restrictScalars_apply, Submodule.mkQ_apply] at h1
      rw [Ideal.Quotient.mk_eq_mk] at h1
      exact Ideal.Quotient.eq_zero_iff_mem.mp h1
    have hw_p : w ∈ p := by
      rcases Ideal.IsPrime.mem_or_mem (show p.IsPrime from inferInstance) ht_w with h | h
      · exact absurd h hf
      · exact h
    rw [← hwz]
    simp only [LinearMap.restrictScalars_apply, Submodule.mkQ_apply]
    rw [Ideal.Quotient.mk_eq_mk]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hw_p
  have hf_inj : Function.Injective f := by
    intro y1 y2 h
    apply Subtype.ext
    have h' : mσ ((y1 : A u) : R ⧸ p) = mσ ((y2 : A u) : R ⧸ p) := by
      have := congrArg (fun z : A (u+1) => (z : R ⧸ p)) h
      rw [hf_apply, hf_apply] at this
      exact this
    have hmem1 : ((y1 : A u) : R ⧸ p) - ((y2 : A u) : R ⧸ p) ∈ A u :=
      (A u).sub_mem y1.property y2.property
    have h0 : mσ (((y1 : A u) : R ⧸ p) - ((y2 : A u) : R ⧸ p)) = 0 := by
      rw [map_sub, h', sub_self]
    have := hmσ_inj _ hmem1 h0
    exact sub_eq_zero.mp this
  have hg_ker : g.ker = f.range := by
    ext x
    constructor
    · intro hx
      rw [LinearMap.mem_ker] at hx
      have hgx : σ (x : R ⧸ p) = 0 := by
        have hh : g x = 0 := hx
        simpa [hg_apply] using hh
      obtain ⟨v, hv, hvx⟩ := Submodule.mem_map.mp x.property
      have hvJ : v ∈ J := by
        have h1 : (J.mkQ.restrictScalars k) v = 0 := by
          rw [← hσ v, hvx]
          exact hgx
        simp only [LinearMap.restrictScalars_apply, Submodule.mkQ_apply] at h1
        rw [Ideal.Quotient.mk_eq_mk] at h1
        exact Ideal.Quotient.eq_zero_iff_mem.mp h1
      rw [Submodule.mem_sup] at hvJ
      obtain ⟨a, ha, b, hb, hab⟩ := hvJ
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hb
      have hv_eq : v = a + t * c := by rw [← hab, ← hc]
      have hv_comp : MvPolynomial.homogeneousComponent (u+1) v = v := by
        have := MvPolynomial.homogeneousComponent_of_mem (m := u+1) hv
        simpa using this
      have htc : MvPolynomial.homogeneousComponent (u+1) (t * c)
          = t * MvPolynomial.homogeneousComponent u c := by
        rw [mul_comm t c, Commons.Algebra.MvPolynomial.homogeneousComponent_mul_of_isHomogeneous_right
          (MvPolynomial.isHomogeneous_X k i) c u, mul_comm]
      have hveq2 : v = MvPolynomial.homogeneousComponent (u+1) a
          + t * MvPolynomial.homogeneousComponent u c := by
        have := congrArg (MvPolynomial.homogeneousComponent (u+1)) hv_eq
        rw [map_add, htc, hv_comp] at this
        exact this
      have hcu_mem : MvPolynomial.homogeneousComponent u c ∈ V u := by
        rw [MvPolynomial.mem_homogeneousSubmodule]
        exact MvPolynomial.homogeneousComponent_isHomogeneous u c
      have hdiff : t * MvPolynomial.homogeneousComponent u c - v ∈ p := by
        have : t * MvPolynomial.homogeneousComponent u c - v
            = -(MvPolynomial.homogeneousComponent (u+1) a) := by
          rw [hveq2]; ring
        rw [this]
        exact p.neg_mem (hp a ha (u+1))
      have hEq : (p.mkQ.restrictScalars k) (t * MvPolynomial.homogeneousComponent u c)
          = (p.mkQ.restrictScalars k) v := by
        rw [← sub_eq_zero, ← map_sub]
        simp only [LinearMap.restrictScalars_apply, Submodule.mkQ_apply]
        rw [Ideal.Quotient.mk_eq_mk]
        exact Ideal.Quotient.eq_zero_iff_mem.mpr hdiff
      rw [LinearMap.mem_range]
      refine ⟨⟨(p.mkQ.restrictScalars k) (MvPolynomial.homogeneousComponent u c),
        Submodule.mem_map.mpr ⟨MvPolynomial.homogeneousComponent u c, hcu_mem, rfl⟩⟩, ?_⟩
      apply Subtype.ext
      rw [hf_apply, hmσ_π, hEq, hvx]
    · intro hx
      rw [LinearMap.mem_range] at hx
      obtain ⟨y, rfl⟩ := hx
      rw [LinearMap.mem_ker]
      obtain ⟨w, hw, hwv⟩ := Submodule.mem_map.mp y.property
      show σ (mσ ↑y) = 0
      rw [← hwv, hmσ_π w, hσ]
      simp only [LinearMap.restrictScalars_apply, Submodule.mkQ_apply]
      rw [Ideal.Quotient.mk_eq_mk]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.mem_sup_right (Ideal.mul_mem_right w (Ideal.span {t})
          (Ideal.mem_span_singleton_self t)))
  haveI hfinA : Module.Finite k ↥(A (u+1)) :=
    Module.Finite.of_fg (Submodule.FG.map _ (MvPolynomial.homogeneousSubmodule_fg (Fin m) k (u+1)))
  have hrank := LinearMap.finrank_range_add_finrank_ker g
  rw [hg_range, hg_ker] at hrank
  have hfr : Module.finrank k ↥(f.range) = Module.finrank k ↥(A u) :=
    LinearMap.finrank_range_of_inj hf_inj
  rw [hfr] at hrank
  omega

theorem hilbertFun_eq_sum_hilbertFun_sup_span_X {k : Type*} [Field k] {m : ℕ}
    (p : Ideal (MvPolynomial (Fin m) k)) [p.IsPrime]
    (hp : ∀ x ∈ p, ∀ j, MvPolynomial.homogeneousComponent j x ∈ p)
    {i : Fin m} (hf : MvPolynomial.X i ∉ p)
    (hK : p ⊔ Ideal.span {MvPolynomial.X i} ≠ ⊤) (u : ℕ) :
    Commons.RingTheory.Ideal.Hilbert.hilbertFun p
        (MvPolynomial.homogeneousSubmodule (Fin m) k u)
      = ∑ j ∈ Finset.range (u + 1),
          Commons.RingTheory.Ideal.Hilbert.hilbertFun (p ⊔ Ideal.span {MvPolynomial.X i})
            (MvPolynomial.homogeneousSubmodule (Fin m) k j) := by
  induction u with
  | zero =>
      rw [Finset.sum_range_one]
      rw [hilbertFun_homogeneousSubmodule_zero p (show p ≠ ⊤ from (inferInstance : p.IsPrime).ne_top),
        hilbertFun_homogeneousSubmodule_zero (p ⊔ Ideal.span {MvPolynomial.X i}) hK]
  | succ u ih =>
      rw [Finset.sum_range_succ, ← ih]
      exact hilbertFun_succ p hp hf u

end Commons.RingTheory.Ideal.Hilbert

end


