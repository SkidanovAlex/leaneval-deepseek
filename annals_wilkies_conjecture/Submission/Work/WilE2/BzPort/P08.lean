/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.RingTheory.Ideal.Hilbert.hilbertFun_bezout` (piece 0).
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
import Submission.Work.WilE2.BzPort.P07

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.RingTheory.Ideal.Hilbert.hilbertFun_bezout ====
section

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

namespace Commons.RingTheory.Ideal.Hilbert

open MvPolynomial

/-- Bezout relation for Hilbert functions: for a homogeneous ideal `I` and a homogeneous
nonzerodivisor `g` of degree `e` modulo `I`, the Hilbert function of `R ⧸ I` is the sum of
the Hilbert functions of `R ⧸ (I + (g))` and of `R ⧸ I` shifted by `e`. -/
theorem hilbertFun_bezout {k : Type*} [Field k] {m : ℕ}
    (I : Ideal (MvPolynomial (Fin m) k))
    (hI : ∀ x ∈ I, ∀ j, MvPolynomial.homogeneousComponent j x ∈ I)
    {g : MvPolynomial (Fin m) k} {e : ℕ} (hg : g.IsHomogeneous e) (hg0 : g ≠ 0)
    (hreg : IsSMulRegular (MvPolynomial (Fin m) k ⧸ I) g) (j : ℕ) (hj : e ≤ j) :
    Module.finrank k (Submodule.map ((I ⊔ Ideal.span {g}).mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k j))
      + Module.finrank k (Submodule.map (I.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k (j - e)))
      = Module.finrank k (Submodule.map (I.mkQ.restrictScalars k)
        (MvPolynomial.homogeneousSubmodule (Fin m) k j)) := by
  classical
  let J : Ideal (MvPolynomial (Fin m) k) := I ⊔ Ideal.span {g}
  let qI : MvPolynomial (Fin m) k →ₗ[k] (MvPolynomial (Fin m) k ⧸ I) := (I.mkQ).restrictScalars k
  let qJ : MvPolynomial (Fin m) k →ₗ[k] (MvPolynomial (Fin m) k ⧸ J) := (J.mkQ).restrictScalars k
  let Vj : Submodule k (MvPolynomial (Fin m) k) := MvPolynomial.homogeneousSubmodule (Fin m) k j
  let Vje : Submodule k (MvPolynomial (Fin m) k) := MvPolynomial.homogeneousSubmodule (Fin m) k (j - e)
  let A : Submodule k (MvPolynomial (Fin m) k ⧸ I) := Submodule.map qI Vje
  let B : Submodule k (MvPolynomial (Fin m) k ⧸ I) := Submodule.map qI Vj
  let C : Submodule k (MvPolynomial (Fin m) k ⧸ J) := Submodule.map qJ Vj
  change Module.finrank k C + Module.finrank k A = Module.finrank k B
  haveI : Module.Finite k A :=
    Module.Finite.of_fg (Submodule.FG.map qI (MvPolynomial.homogeneousSubmodule_fg (Fin m) k (j - e)))
  haveI : Module.Finite k B :=
    Module.Finite.of_fg (Submodule.FG.map qI (MvPolynomial.homogeneousSubmodule_fg (Fin m) k j))
  -- multiplication by g on the quotient R ⧸ I
  let bar_m : (MvPolynomial (Fin m) k ⧸ I) →ₗ[k] (MvPolynomial (Fin m) k ⧸ I) :=
    (g • (LinearMap.id : (MvPolynomial (Fin m) k ⧸ I) →ₗ[MvPolynomial (Fin m) k]
      (MvPolynomial (Fin m) k ⧸ I))).restrictScalars k
  have bar_m_apply : ∀ z, bar_m z = g • z := by
    intro z
    simp only [bar_m, LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.id_apply]
  have qI_apply : ∀ x, qI x = Ideal.Quotient.mk I x := fun x => rfl
  have qJ_apply : ∀ x, qJ x = Ideal.Quotient.mk J x := fun x => rfl
  have qI_smul : ∀ (a r : MvPolynomial (Fin m) k), qI (a * r) = a • qI r := by
    intro a r
    show Submodule.mkQ I (a * r) = a • Submodule.mkQ I r
    rw [← smul_eq_mul]
    exact map_smul (Submodule.mkQ I) a r
  have bar_m_qI : ∀ r, bar_m (qI r) = qI (g * r) := by
    intro r
    rw [bar_m_apply, qI_smul]
  have hbar_inj : Function.Injective bar_m := by
    intro x y hxy
    rw [bar_m_apply x, bar_m_apply y] at hxy
    exact hreg hxy
  -- multiplication by g maps A into B
  have hAB : ∀ x ∈ A, bar_m x ∈ B := by
    intro x hx
    rw [Submodule.mem_map] at hx ⊢
    obtain ⟨r, hr, rfl⟩ := hx
    refine ⟨g * r, ?_, (bar_m_qI r).symm⟩
    have hr' : r.IsHomogeneous (j - e) := by
      simpa only [Vje, MvPolynomial.mem_homogeneousSubmodule] using hr
    have hgr : (g * r).IsHomogeneous (e + (j - e)) := hg.mul hr'
    rw [show e + (j - e) = j from by omega] at hgr
    simpa only [Vj, MvPolynomial.mem_homogeneousSubmodule] using hgr
  -- the quotient map π : R ⧸ I → R ⧸ J
  have hIJ : I ≤ J := le_sup_left
  let π : (MvPolynomial (Fin m) k ⧸ I) →ₗ[k] (MvPolynomial (Fin m) k ⧸ J) :=
    (Ideal.Quotient.factorₐ k hIJ).toLinearMap
  have hpi_apply : ∀ x, π (qI x) = qJ x := by
    intro x
    change (Ideal.Quotient.factorₐ k hIJ) (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J x
    rw [Ideal.Quotient.factorₐ_apply, Ideal.Quotient.factor_mk]
  have hBC : ∀ x ∈ B, π x ∈ C := by
    intro x hx
    rw [Submodule.mem_map] at hx ⊢
    obtain ⟨r, hr, rfl⟩ := hx
    exact ⟨r, hr, (hpi_apply r).symm⟩
  have hbar_ker : ∀ x ∈ A, π (bar_m x) = 0 := by
    intro x hx
    rw [Submodule.mem_map] at hx
    obtain ⟨r, hr, rfl⟩ := hx
    rw [bar_m_qI, hpi_apply, qJ_apply]
    rw [Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mem_sup_right (Ideal.mul_mem_right r (Ideal.span {g}) (Ideal.mem_span_singleton_self g))
  -- inclusion of the kernel of π into B inside the image of multiplication by g
  have hker_le : π.ker ⊓ B ≤ Submodule.map bar_m A := by
    intro y hy
    rw [Submodule.mem_inf] at hy
    obtain ⟨hyker, hyB⟩ := hy
    rw [LinearMap.mem_ker] at hyker
    rw [Submodule.mem_map] at hyB
    obtain ⟨r, hrVj, hr_eq⟩ := hyB
    have hqJ : qJ r = 0 := by
      rw [← hpi_apply r, hr_eq]; exact hyker
    have hqJmk : Ideal.Quotient.mk J r = 0 := by rw [← qJ_apply r]; exact hqJ
    have hrJ : r ∈ J := Ideal.Quotient.eq_zero_iff_mem.mp hqJmk
    rw [Submodule.mem_sup] at hrJ
    obtain ⟨i, hiI, s, hs, his⟩ := hrJ
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton.mp hs
    have hrc : r = i + g * c := by rw [← his, hc]
    have hrVj' : r ∈ MvPolynomial.homogeneousSubmodule (Fin m) k j := by
      simpa only [Vj] using hrVj
    have hr_hom : MvPolynomial.homogeneousComponent j r = r := by
      have h := MvPolynomial.homogeneousComponent_of_mem (m := j) hrVj'
      simpa using h
    have hgc : MvPolynomial.homogeneousComponent j (g * c)
        = g * MvPolynomial.homogeneousComponent (j - e) c := by
      have hje : (j - e) + e = j := by omega
      calc MvPolynomial.homogeneousComponent j (g * c)
          = MvPolynomial.homogeneousComponent ((j - e) + e) (c * g) := by
            rw [mul_comm g c, hje]
        _ = MvPolynomial.homogeneousComponent (j - e) c * g :=
            Commons.Algebra.MvPolynomial.homogeneousComponent_mul_of_isHomogeneous_right hg c (j - e)
        _ = g * MvPolynomial.homogeneousComponent (j - e) c := mul_comm _ _
    have hr_eq2 : r = MvPolynomial.homogeneousComponent j i
        + g * MvPolynomial.homogeneousComponent (j - e) c := by
      have hcomp := congrArg (MvPolynomial.homogeneousComponent j) hrc
      rw [map_add, hgc, hr_hom] at hcomp
      exact hcomp
    have hc'_mem : MvPolynomial.homogeneousComponent (j - e) c ∈ Vje := by
      simp only [Vje, MvPolynomial.mem_homogeneousSubmodule]
      exact MvPolynomial.homogeneousComponent_isHomogeneous (j - e) c
    have hi_mem : MvPolynomial.homogeneousComponent j i ∈ I := hI i hiI j
    have h0 : qI (MvPolynomial.homogeneousComponent j i) = 0 := by
      rw [qI_apply, Ideal.Quotient.eq_zero_iff_mem]
      exact hi_mem
    rw [Submodule.mem_map]
    refine ⟨qI (MvPolynomial.homogeneousComponent (j - e) c), ?_, ?_⟩
    · rw [Submodule.mem_map]
      exact ⟨_, hc'_mem, rfl⟩
    · rw [bar_m_qI, ← hr_eq, hr_eq2, map_add, h0, zero_add]
  -- the two linear maps
  let f : A →ₗ[k] B := LinearMap.restrict bar_m hAB
  have hf_ker : f.ker = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    rw [LinearMap.mem_ker] at hx
    apply Subtype.ext
    have hxval : bar_m (x : MvPolynomial (Fin m) k ⧸ I) = 0 := by
      have h : ((f x : ↥B) : MvPolynomial (Fin m) k ⧸ I) = 0 := by rw [hx]; simp
      exact h
    have : (x : MvPolynomial (Fin m) k ⧸ I) = 0 :=
      hbar_inj (by rw [hxval, bar_m_apply]; simp)
    exact this
  have hfinA : Module.finrank k A = Module.finrank k f.range := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    rw [hf_ker] at h
    simp only [finrank_bot, add_zero] at h
    exact h.symm
  let hh : B →ₗ[k] C := LinearMap.restrict π hBC
  have hh_range : hh.range = ⊤ := by
    rw [Submodule.eq_top_iff']
    intro y
    rw [LinearMap.mem_range]
    have hy : (y : MvPolynomial (Fin m) k ⧸ J) ∈ Submodule.map qJ Vj := y.property
    rw [Submodule.mem_map] at hy
    obtain ⟨r, hrVj, hr_eq⟩ := hy
    refine ⟨⟨qI r, ?_⟩, ?_⟩
    · rw [Submodule.mem_map]
      exact ⟨r, hrVj, rfl⟩
    · apply Subtype.ext
      show π (qI r) = (y : MvPolynomial (Fin m) k ⧸ J)
      rw [hpi_apply r]; exact hr_eq
  have hh_ker : hh.ker = f.range := by
    apply le_antisymm
    · intro y hy
      rw [LinearMap.mem_ker] at hy
      have hyval : π (y : MvPolynomial (Fin m) k ⧸ I) = 0 := by
        have h : ((hh y : ↥C) : MvPolynomial (Fin m) k ⧸ J) = 0 := by rw [hy]; simp
        exact h
      have hyker : (y : MvPolynomial (Fin m) k ⧸ I) ∈ π.ker :=
        LinearMap.mem_ker.mpr hyval
      have hyinf : (y : MvPolynomial (Fin m) k ⧸ I) ∈ π.ker ⊓ B :=
        Submodule.mem_inf.mpr ⟨hyker, y.property⟩
      have hmem := hker_le hyinf
      rw [Submodule.mem_map] at hmem
      obtain ⟨x, hxA, hx_eq⟩ := hmem
      rw [LinearMap.mem_range]
      refine ⟨⟨x, hxA⟩, ?_⟩
      apply Subtype.ext
      exact hx_eq
    · intro y hy
      rw [LinearMap.mem_range] at hy
      obtain ⟨x, hx⟩ := hy
      rw [LinearMap.mem_ker]
      rw [← hx]
      apply Subtype.ext
      show π (bar_m (x : MvPolynomial (Fin m) k ⧸ I)) = 0
      exact hbar_ker x.val x.property
  have hkey := LinearMap.finrank_range_add_finrank_ker hh
  rw [hh_range, finrank_top, hh_ker] at hkey
  rw [← hfinA] at hkey
  exact hkey

end Commons.RingTheory.Ideal.Hilbert
end


