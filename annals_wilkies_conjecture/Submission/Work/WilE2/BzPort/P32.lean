/-
  Ported (mechanically) from the lead-supplied reuse file
  `sources/reuse/ours/annals_van_der_waerden_conjecture/Submission/Commons/RingTheory/Ideal/card_minimalPrimes_quotient_le_univ.lean`
  section `mission.Commons.RingTheory.Ideal.Hilbert.hilbert_sum_upper_bound` (piece 0).
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
import Submission.Work.WilE2.BzPort.P31

set_option maxHeartbeats 4000000
set_option linter.style.haveILetI false
set_option linter.unusedVariables false
set_option warn.classDefReducibility false



set_option autoImplicit true

-- ==== from Submission.Commons.RingTheory.Ideal.Hilbert.hilbert_sum_upper_bound ====
section

open MvPolynomial

namespace Commons.RingTheory.Ideal.Hilbert

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Membership in the irrelevant ideal -/

lemma mem_idealOfVars_iff_coeff_zero_hub {σ : Type*} {K : Type*} [Field K]
    (x : MvPolynomial σ K) :
    x ∈ MvPolynomial.idealOfVars σ K ↔ (x).coeff 0 = 0 := by
  rw [MvPolynomial.idealOfVars,
    show Set.range (MvPolynomial.X) = MvPolynomial.X '' (Set.univ : Set σ) from by simp,
    MvPolynomial.mem_ideal_span_X_image]
  constructor
  · intro h
    by_contra hc
    have hm : (0 : σ →₀ ℕ) ∈ x.support := MvPolynomial.mem_support_iff.mpr hc
    obtain ⟨i, -, hi⟩ := h 0 hm
    exact hi (by simp)
  · intro h m hm
    have hm0 : m ≠ 0 := by
      rintro rfl
      exact (MvPolynomial.mem_support_iff.mp hm) h
    obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hm0
    exact ⟨i, Set.mem_univ i, hi⟩

lemma idealOfVars_eq_ker_constantCoeff {k : Type*} [Field k] {m : ℕ} :
    MvPolynomial.idealOfVars (Fin m) k = RingHom.ker MvPolynomial.constantCoeff := by
  ext x
  rw [RingHom.mem_ker, mem_idealOfVars_iff_coeff_zero_hub, MvPolynomial.constantCoeff_eq]

def idealOfVars_isMaximal {k : Type*} [Field k] {m : ℕ} :
    (MvPolynomial.idealOfVars (Fin m) k).IsMaximal := by
  rw [idealOfVars_eq_ker_constantCoeff]
  exact RingHom.ker_isMaximal_of_surjective MvPolynomial.constantCoeff
    (fun x => ⟨MvPolynomial.C x, by simp⟩)
attribute [local instance] Commons.Algebra.MvPolynomial.idealOfVars_isMaximal

lemma idealOfVars_homogeneousComponent_mem {k : Type*} [Field k] {m : ℕ}
    {x : MvPolynomial (Fin m) k} (hx : x ∈ MvPolynomial.idealOfVars (Fin m) k) (j : ℕ) :
    MvPolynomial.homogeneousComponent j x ∈ MvPolynomial.idealOfVars (Fin m) k := by
  rw [mem_idealOfVars_iff_coeff_zero_hub] at hx ⊢
  rw [MvPolynomial.coeff_homogeneousComponent]
  have h0 : Finsupp.degree (0 : Fin m →₀ ℕ) = 0 := by simp
  rw [h0]
  by_cases hj : (0 : ℕ) = j
  · simp [hj, hx]
  · simp [hj]

/-! ## Minimal primes of a homogeneous ideal -/

theorem minimalPrimes_homogeneousComponent_mem {k : Type*} [Field k] {m : ℕ}
    {q : Ideal (MvPolynomial (Fin m) k)}
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    {p : Ideal (MvPolynomial (Fin m) k)} (hp : p ∈ q.minimalPrimes) :
    ∀ x ∈ p, ∀ j, MvPolynomial.homogeneousComponent j x ∈ p := by
  classical
  have hcore : (Ideal.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k) p).toIdeal.IsPrime :=
    hp.1.1.homogeneousCore
  have hqle : q ≤ (Ideal.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k) p).toIdeal := by
    intro x hx
    rw [← MvPolynomial.sum_homogeneousComponent x]
    refine Ideal.sum_mem _ fun j _ => ?_
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem
      ⟨j, MvPolynomial.homogeneousComponent_mem j x⟩ (hp.1.2 (hq x hx j))
  have heq : (Ideal.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k) p).toIdeal = p :=
    le_antisymm (Ideal.toIdeal_homogeneousCore_le _ p)
      (hp.2 ⟨hcore, hqle⟩ (Ideal.toIdeal_homogeneousCore_le _ p))
  intro x hx j
  rw [← heq] at hx
  have h := (MvPolynomial.mem_iff_homogeneousComponent_mem
    (HomogeneousIdeal.isHomogeneous (Ideal.homogeneousCore (MvPolynomial.homogeneousSubmodule (Fin m) k) p))
    x).mp hx j
  rwa [heq] at h

theorem minimalPrimes_le_idealOfVars_hub {k : Type*} [Field k] {m : ℕ}
    {q : Ideal (MvPolynomial (Fin m) k)}
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    {p : Ideal (MvPolynomial (Fin m) k)} (hp : p ∈ q.minimalPrimes) :
    p ≤ MvPolynomial.idealOfVars (Fin m) k := by
  intro x hx
  rw [mem_idealOfVars_iff_coeff_zero_hub]
  have hx0 : MvPolynomial.homogeneousComponent 0 x ∈ p :=
    minimalPrimes_homogeneousComponent_mem hq hp x hx 0
  rw [MvPolynomial.homogeneousComponent_zero] at hx0
  by_contra hne
  have h1 : (1 : MvPolynomial (Fin m) k) ∈ p := by
    have hmem := p.mul_mem_left (MvPolynomial.C ((x).coeff 0)⁻¹) hx0
    rwa [← MvPolynomial.C_mul, inv_mul_cancel₀ hne, MvPolynomial.C_1] at hmem
  exact hp.1.1.ne_top ((Ideal.eq_top_iff_one p).mpr h1)

/-- If a minimal prime of `q` contains the irrelevant ideal, then `ringKrullDim (S ⧸ q) ≤ 0`. -/
theorem ringKrullDim_le_zero_of_minimalPrimes_idealOfVars_le {k : Type*} [Field k] {m : ℕ}
    {q : Ideal (MvPolynomial (Fin m) k)}
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    {p : Ideal (MvPolynomial (Fin m) k)} (hp : p ∈ q.minimalPrimes)
    (hle : MvPolynomial.idealOfVars (Fin m) k ≤ p) :
    ringKrullDim (MvPolynomial (Fin m) k ⧸ q) ≤ ((0 : ℕ) : WithBot ℕ∞) := by
  have hp_le : p ≤ MvPolynomial.idealOfVars (Fin m) k := minimalPrimes_le_idealOfVars_hub hq hp
  have hp_eq : p = MvPolynomial.idealOfVars (Fin m) k := le_antisymm hp_le hle
  have hmax : ∀ J ∈ q.minimalPrimes, J.IsMaximal := by
    intro J hJ
    have hJle : J ≤ MvPolynomial.idealOfVars (Fin m) k := minimalPrimes_le_idealOfVars_hub hq hJ
    have hJle_p : J ≤ p := le_trans hJle (le_of_eq hp_eq.symm)
    have hp_le_J : p ≤ J := hp.2 ⟨hJ.1.1, hJ.1.2⟩ hJle_p
    rw [le_antisymm hJle_p hp_le_J, hp_eq]
    exact idealOfVars_isMaximal
  have h0 : Ring.KrullDimLE 0 (MvPolynomial (Fin m) k ⧸ q) :=
    Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr hmax
  exact Ring.krullDimLE_iff.mp h0

theorem homogeneous_span_singleton {k : Type*} [Field k] {m : ℕ}
    {f : MvPolynomial (Fin m) k} {e : ℕ} (hf : f.IsHomogeneous e) :
    Ideal.IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin m) k) (Ideal.span {f}) :=
  Ideal.homogeneous_span (MvPolynomial.homogeneousSubmodule (Fin m) k) {f}
    (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact ⟨e, (MvPolynomial.mem_homogeneousSubmodule e x).mpr (hx ▸ hf)⟩)

/-! ## Dimension drop by a homogeneous element -/

theorem ringKrullDim_quotient_sup_span_le {R : Type*} [CommRing R] (q : Ideal R) (f : R)
    (hqf : ∀ p ∈ q.minimalPrimes, f ∉ p) {n : ℕ}
    (hd : ringKrullDim (R ⧸ q) ≤ ((n + 1 : ℕ) : WithBot ℕ∞)) :
    ringKrullDim (R ⧸ (q ⊔ Ideal.span {f})) ≤ ((n : ℕ) : WithBot ℕ∞) := by
  have hdk : Order.krullDim ↥(PrimeSpectrum.zeroLocus (q : Set R)) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) := by
    rw [← ringKrullDim_quotient]; exact hd
  rw [ringKrullDim_quotient]
  have hsub : PrimeSpectrum.zeroLocus ((q ⊔ Ideal.span {f} : Ideal R) : Set R)
      ⊆ PrimeSpectrum.zeroLocus (q : Set R) :=
    PrimeSpectrum.zeroLocus_anti_mono (by intro x hx; exact le_sup_left (a := q) hx)
  rcases isEmpty_or_nonempty ↥(PrimeSpectrum.zeroLocus ((q ⊔ Ideal.span {f} : Ideal R) : Set R)) with hem | hne
  · rw [Order.krullDim_eq_bot]; exact bot_le
  · have h2 : (⨆ p : LTSeries ↥(PrimeSpectrum.zeroLocus ((q ⊔ Ideal.span {f} : Ideal R) : Set R)),
        ((p.length : ℕ) : ℕ∞)) ≤ ((n : ℕ) : ℕ∞) := by
      apply iSup_le
      intro l
      have hmono : StrictMono (fun x : ↥(PrimeSpectrum.zeroLocus ((q ⊔ Ideal.span {f} : Ideal R) : Set R)) =>
          (⟨x.1, hsub x.2⟩ : ↥(PrimeSpectrum.zeroLocus (q : Set R)))) := fun a b h => h
      let lq : LTSeries ↥(PrimeSpectrum.zeroLocus (q : Set R)) := l.map _ hmono
      have hlqlen : lq.length = l.length := rfl
      haveI : (lq.head.1.asIdeal).IsPrime := lq.head.1.isPrime
      have hqle : q ≤ lq.head.1.asIdeal :=
        (PrimeSpectrum.mem_zeroLocus _ _).mp lq.head.2
      obtain ⟨p0, hp0mem, hp0le⟩ := Ideal.exists_minimalPrimes_le (I := q) (J := lq.head.1.asIdeal) hqle
      have hfmem : f ∈ lq.head.1.asIdeal := by
        have h1 : (q ⊔ Ideal.span {f} : Ideal R) ≤ l.head.1.asIdeal :=
          (PrimeSpectrum.mem_zeroLocus _ _).mp l.head.2
        exact h1 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
      have hfnot : f ∉ p0 := hqf p0 hp0mem
      let P0 : PrimeSpectrum R := ⟨p0, hp0mem.1.1⟩
      have hP0mem : P0 ∈ PrimeSpectrum.zeroLocus (q : Set R) :=
        (PrimeSpectrum.mem_zeroLocus _ _).mpr hp0mem.1.2
      have hp0lt : (⟨P0, hP0mem⟩ : ↥(PrimeSpectrum.zeroLocus (q : Set R))) < lq.head := by
        refine lt_of_le_of_ne (show P0 ≤ lq.head.1 from hp0le) ?_
        intro hcon
        have h2 : p0 = lq.head.1.asIdeal := by
          simpa [P0] using congrArg (fun x : ↥(PrimeSpectrum.zeroLocus (q : Set R)) => x.1.asIdeal) hcon
        exact hfnot (h2.symm ▸ hfmem)
      let l' : LTSeries ↥(PrimeSpectrum.zeroLocus (q : Set R)) := lq.cons _ hp0lt
      have hlen : l'.length = l.length + 1 := by
        rw [RelSeries.cons_length, hlqlen]
      have hbound := Order.LTSeries.length_le_krullDim l'
      rw [hlen] at hbound
      have hbound' : l.length + 1 ≤ n + 1 := by
        exact_mod_cast hbound.trans hdk
      rw [ENat.natCast_le_natCast]
      omega
    rw [Order.krullDim_eq_iSup_length]
    exact WithBot.coe_le_coe.mpr h2

/-! ## The recursion inequality for Hilbert functions -/

theorem hilbertFun_recursion {k : Type*} [Field k] {m : ℕ}
    (q : Ideal (MvPolynomial (Fin m) k))
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    {f : MvPolynomial (Fin m) k} {e : ℕ}
    (hf : f.IsHomogeneous e) (u : ℕ) (he : e ≤ u) :
    hilbertFun q (homogeneousSubmodule (Fin m) k u)
      ≤ hilbertFun q (homogeneousSubmodule (Fin m) k (u - e))
        + hilbertFun (q ⊔ Ideal.span {f}) (homogeneousSubmodule (Fin m) k u) := by
  classical
  set q' : Ideal (MvPolynomial (Fin m) k) := q ⊔ Ideal.span {f} with hq'def
  set V : Submodule k (MvPolynomial (Fin m) k) := homogeneousSubmodule (Fin m) k u with hVdef
  set Ve : Submodule k (MvPolynomial (Fin m) k) := homogeneousSubmodule (Fin m) k (u - e) with hVedef
  set N : Submodule k (MvPolynomial (Fin m) k) := V ⊓ q.restrictScalars k with hNdef
  set M : Submodule k (MvPolynomial (Fin m) k) := V ⊓ q'.restrictScalars k with hMdef
  haveI hVfg : V.FG := by rw [hVdef]; exact homogeneousSubmodule_fg (Fin m) k u
  haveI hVfin : Module.Finite k ↥V := Module.Finite.of_fg hVfg
  haveI hVefg : Ve.FG := by rw [hVedef]; exact homogeneousSubmodule_fg (Fin m) k (u - e)
  haveI hVefin : Module.Finite k ↥Ve := Module.Finite.of_fg hVefg
  haveI hMfg : M.FG := Submodule.FG.of_le hVfg (by rw [hMdef]; exact inf_le_left)
  haveI hMfin : Module.Finite k ↥M := Module.Finite.of_fg hMfg
  haveI hNfg : N.FG := Submodule.FG.of_le hVfg (by rw [hNdef]; exact inf_le_left)
  haveI hNfin : Module.Finite k ↥N := Module.Finite.of_fg hNfg
  have hNM : N ≤ M := by
    rw [hNdef, hMdef]
    exact inf_le_inf_left V (by rw [hq'def]; exact Submodule.restrictScalars_mono k le_sup_left)
  set φ : MvPolynomial (Fin m) k →ₗ[k] (MvPolynomial (Fin m) k ⧸ q) :=
    (q.mkQ).restrictScalars k with hφdef
  set φ' : MvPolynomial (Fin m) k →ₗ[k] (MvPolynomial (Fin m) k ⧸ q') :=
    (q'.mkQ).restrictScalars k with hφ'def
  set ρ : (MvPolynomial (Fin m) k ⧸ q) →ₗ[k] (MvPolynomial (Fin m) k ⧸ q') :=
    (Ideal.Quotient.factorₐ k (le_sup_left : q ≤ q')).toLinearMap with hρdef
  have hρφ : ρ.comp φ = φ' := by
    apply LinearMap.ext
    intro x
    simp only [LinearMap.comp_apply, hφdef, hρdef, hφ'def]
    rw [show (Ideal.Quotient.factorₐ k (le_sup_left : q ≤ q')).toLinearMap
        ((q.mkQ).restrictScalars k x)
        = Ideal.Quotient.factor (le_sup_left : q ≤ q') (Ideal.Quotient.mk q x) from rfl,
      Ideal.Quotient.factor_mk]
    rfl
  haveI hφVfg : (Submodule.map φ V).FG := Submodule.FG.map φ hVfg
  haveI hφVfin : Module.Finite k ↥(Submodule.map φ V) := Module.Finite.of_fg hφVfg
  have step1 : Module.finrank k ↥(Submodule.map φ V)
      = Module.finrank k ↥(Submodule.map φ' V) + Module.finrank k ↥(Submodule.map φ V ⊓ ρ.ker) := by
    have h := Commons.RingTheory.Ideal.Hilbert.finrank_map_add_finrank_inf_ker (k := k) ρ
      (Submodule.map φ V)
    have hmap : Submodule.map ρ (Submodule.map φ V) = Submodule.map φ' V := by
      rw [← Submodule.map_comp, hρφ]
    rw [hmap] at h
    omega
  have step2 : Submodule.map φ V ⊓ ρ.ker = Submodule.map φ M := by
    apply le_antisymm
    · intro y hy
      rw [Submodule.mem_inf] at hy
      obtain ⟨hyW, hyker⟩ := hy
      rw [Submodule.mem_map] at hyW
      obtain ⟨x, hxV, rfl⟩ := hyW
      rw [LinearMap.mem_ker] at hyker
      have hxq' : x ∈ q' := by
        have h1 : Ideal.Quotient.mk q' x = 0 := by
          have h2 : φ' x = 0 := by
            rw [show φ' x = ρ (φ x) from (congrFun (congrArg DFunLike.coe hρφ) x).symm, hyker]
          rwa [hφ'def] at h2
        exact Ideal.Quotient.eq_zero_iff_mem.mp h1
      refine Submodule.mem_map.mpr ⟨x, ?_, rfl⟩
      simp only [hMdef, Submodule.mem_inf]
      exact ⟨hxV, hxq'⟩
    · rintro y ⟨x, hxM, rfl⟩
      simp only [hMdef, Submodule.mem_inf] at hxM
      obtain ⟨hxV, hxq'⟩ := hxM
      rw [Submodule.mem_inf]
      refine ⟨Submodule.mem_map.mpr ⟨x, hxV, rfl⟩, ?_⟩
      rw [LinearMap.mem_ker]
      rw [show ρ (φ x) = φ' x from congrFun (congrArg DFunLike.coe hρφ) x]
      rw [hφ'def]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hxq'
  have hφker : φ.ker = q.restrictScalars k := by
    simp only [hφdef, LinearMap.ker_restrictScalars, Submodule.ker_mkQ]
  have step3 : Module.finrank k ↥(Submodule.map φ M) = Module.finrank k ↥M - Module.finrank k ↥N := by
    have h := Commons.RingTheory.Ideal.Hilbert.finrank_map_add_finrank_inf_ker (k := k) φ M
    have hMN : M ⊓ φ.ker = N := by
      rw [hφker]
      show (M ⊓ q.restrictScalars k) = N
      rw [hMdef, hNdef]
      ext x
      simp only [Submodule.mem_inf]
      constructor
      · rintro ⟨⟨hxV, hxq'⟩, hxq⟩
        exact ⟨hxV, hxq⟩
      · rintro ⟨hxV, hxq⟩
        exact ⟨⟨hxV, (by rw [hq'def]; exact le_sup_left (a := q) (b := Ideal.span {f}) hxq)⟩, hxq⟩
    rw [hMN] at h
    omega
  have step4 : Module.finrank k ↥M - Module.finrank k ↥N
      ≤ hilbertFun q (homogeneousSubmodule (Fin m) k (u - e)) := by
    rw [hilbertFun_eq_sub, ← hVedef]
    set ψ : Ve →ₗ[k] (MvPolynomial (Fin m) k ⧸ N) :=
      { toFun := fun x => Submodule.mkQ N (f * (x : MvPolynomial (Fin m) k))
        map_add' := by intro x y; simp only [Submodule.coe_add, mul_add, map_add]
        map_smul' := by intro c x; simp only [SetLike.val_smul, mul_smul_comm, map_smul,
          RingHom.id_apply] } with hψdef
    have hψ_apply : ∀ x : Ve, ψ x = Submodule.mkQ N (f * (x : MvPolynomial (Fin m) k)) := fun x => rfl
    have hψ_range : ψ.range = Submodule.map (Submodule.mkQ N) M := by
      apply le_antisymm
      · rintro y ⟨x, rfl⟩
        refine Submodule.mem_map.mpr ⟨f * (x : MvPolynomial (Fin m) k), ?_, rfl⟩
        simp only [hMdef, Submodule.mem_inf]
        refine ⟨?_, ?_⟩
        · rw [hVdef, mem_homogeneousSubmodule]
          have hx : (x : MvPolynomial (Fin m) k).IsHomogeneous (u - e) := x.2
          have := hf.mul hx
          rwa [Nat.add_sub_cancel' he] at this
        · rw [hq'def]
          exact Ideal.mul_mem_right _ _ (Ideal.mem_sup_right (Ideal.mem_span_singleton_self f))
      · rintro y ⟨z, hzM, rfl⟩
        simp only [hMdef, Submodule.mem_inf] at hzM
        obtain ⟨hzV, hzq'⟩ := hzM
        change z.IsHomogeneous u at hzV
        have hzq'ideal : z ∈ q' := hzq'
        rw [hq'def] at hzq'ideal
        obtain ⟨a, haq, b, hb, hab⟩ := Submodule.mem_sup.mp hzq'ideal
        rw [Ideal.mem_span_singleton] at hb
        obtain ⟨c, rfl⟩ := hb
        rw [LinearMap.mem_range]
        refine ⟨⟨homogeneousComponent (u - e) c, ?_⟩, ?_⟩
        · rw [hVedef, mem_homogeneousSubmodule]
          exact homogeneousComponent_isHomogeneous _ _
        · rw [hψ_apply]
          have hdecomp : z = homogeneousComponent u a + f * homogeneousComponent (u - e) c := by
            have h1 : z = homogeneousComponent u (a + f * c) := by
              rw [← hab, homogeneousComponent_eq_self (show (a + f * c).IsHomogeneous u from by
                rw [hab]; exact hzV)]
            rw [h1, map_add]
            congr 1
            rw [mul_comm f c]
            have h2 := Commons.Algebra.MvPolynomial.homogeneousComponent_mul_of_isHomogeneous_right
              hf c (u - e)
            rw [show (u - e) + e = u from Nat.sub_add_cancel he] at h2
            rw [h2, mul_comm]
          have haN : homogeneousComponent u a ∈ N := by
            simp only [hNdef, Submodule.mem_inf]
            exact ⟨mem_homogeneousSubmodule _ _ |>.mpr (homogeneousComponent_isHomogeneous _ _),
              hq a haq u⟩
          rw [hdecomp, map_add, show Submodule.mkQ N (homogeneousComponent u a) = 0 from by
            rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]; exact haN, zero_add]
    have hrn := LinearMap.finrank_range_add_finrank_ker ψ
    rw [hψ_range] at hrn
    have hmapN : Module.finrank k ↥(Submodule.map (Submodule.mkQ N) M)
        = Module.finrank k ↥M - Module.finrank k ↥N := by
      have h := Commons.RingTheory.Ideal.Hilbert.finrank_map_add_finrank_inf_ker (k := k)
        (Submodule.mkQ N) M
      rw [Submodule.ker_mkQ, inf_eq_right.mpr hNM] at h
      omega
    rw [hmapN] at hrn
    set K0 : Submodule k ↥Ve := Submodule.comap Ve.subtype (Ve ⊓ q.restrictScalars k) with hK0
    have hK0_le : K0 ≤ ψ.ker := by
      intro x hx
      rw [hK0, Submodule.mem_comap, Submodule.mem_inf] at hx
      obtain ⟨-, hxq⟩ := hx
      rw [LinearMap.mem_ker, hψ_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      simp only [hNdef, Submodule.mem_inf]
      refine ⟨?_, ?_⟩
      · rw [mem_homogeneousSubmodule]
        have hx' : (x : MvPolynomial (Fin m) k).IsHomogeneous (u - e) := x.2
        have := hf.mul hx'
        rwa [Nat.add_sub_cancel' he] at this
      · exact Ideal.mul_mem_left q f (show (x : MvPolynomial (Fin m) k) ∈ q from hxq)
    have hfin_le : Module.finrank k ↥(Ve ⊓ q.restrictScalars k) ≤ Module.finrank k ↥ψ.ker := by
      have h1 : Module.finrank k ↥(Ve ⊓ q.restrictScalars k) = Module.finrank k ↥K0 := by
        have := Submodule.finrank_map_subtype_eq Ve K0
        rw [hK0, Submodule.map_comap_subtype, inf_eq_right.mpr inf_le_left] at this
        exact this
      rw [h1]
      exact Submodule.finrank_mono hK0_le
    omega
  have hmain : Module.finrank k ↥(Submodule.map φ V)
      ≤ Module.finrank k ↥(Submodule.map φ' V)
        + hilbertFun q (homogeneousSubmodule (Fin m) k (u - e)) := by
    rw [step1, step2, step3]
    exact Nat.add_le_add_left step4 _
  calc hilbertFun q (homogeneousSubmodule (Fin m) k u)
      = Module.finrank k ↥(Submodule.map φ V) := rfl
    _ ≤ Module.finrank k ↥(Submodule.map φ' V)
        + hilbertFun q (homogeneousSubmodule (Fin m) k (u - e)) := hmain
    _ = hilbertFun (q ⊔ Ideal.span {f}) (homogeneousSubmodule (Fin m) k u)
        + hilbertFun q (homogeneousSubmodule (Fin m) k (u - e)) := rfl
    _ = hilbertFun q (homogeneousSubmodule (Fin m) k (u - e))
        + hilbertFun (q ⊔ Ideal.span {f}) (homogeneousSubmodule (Fin m) k u) := add_comm _ _
end Commons.RingTheory.Ideal.Hilbert
end
