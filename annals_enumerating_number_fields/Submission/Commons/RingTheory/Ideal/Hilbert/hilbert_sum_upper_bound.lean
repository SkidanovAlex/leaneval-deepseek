import Mathlib.Data.Int.Star
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.GradedAlgebra.Radical
import Mathlib.RingTheory.Jacobson.Artinian
import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.PicardGroup
import Submission.Commons.RingTheory.Ideal.Hilbert.sum_coeff_le_coeff_hilbertPoly
import Submission.Commons.Algebra.MvPolynomial.homogeneousComponent_mul_of_isHomogeneous_right
import Submission.Commons.RingTheory.Ideal.Hilbert.homogeneous_prime_avoidance
import Submission.Commons.Algebra.MvPolynomial.sum_finrank_homogeneous_le_finrank

open MvPolynomial

namespace Commons.RingTheory.Ideal.Hilbert

set_option linter.style.haveILetI false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 2000000

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## Membership in the irrelevant ideal -/

lemma mem_idealOfVars_iff_coeff_zero {σ : Type*} {K : Type*} [Field K]
    (x : MvPolynomial σ K) :
    x ∈ MvPolynomial.idealOfVars σ K ↔ MvPolynomial.coeff 0 x = 0 := by
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

lemma idealOfVars_eq_ker_constantCoeff {k : Type} [Field k] {m : ℕ} :
    MvPolynomial.idealOfVars (Fin m) k = RingHom.ker MvPolynomial.constantCoeff := by
  ext x
  rw [RingHom.mem_ker, mem_idealOfVars_iff_coeff_zero, MvPolynomial.constantCoeff_eq]

instance idealOfVars_isMaximal {k : Type} [Field k] {m : ℕ} :
    (MvPolynomial.idealOfVars (Fin m) k).IsMaximal := by
  rw [idealOfVars_eq_ker_constantCoeff]
  exact RingHom.ker_isMaximal_of_surjective MvPolynomial.constantCoeff
    (fun x => ⟨MvPolynomial.C x, by simp⟩)

lemma idealOfVars_homogeneousComponent_mem {k : Type} [Field k] {m : ℕ}
    {x : MvPolynomial (Fin m) k} (hx : x ∈ MvPolynomial.idealOfVars (Fin m) k) (j : ℕ) :
    MvPolynomial.homogeneousComponent j x ∈ MvPolynomial.idealOfVars (Fin m) k := by
  rw [mem_idealOfVars_iff_coeff_zero] at hx ⊢
  rw [MvPolynomial.coeff_homogeneousComponent]
  have h0 : Finsupp.degree (0 : Fin m →₀ ℕ) = 0 := by simp
  rw [h0]
  by_cases hj : (0 : ℕ) = j
  · simp [hj, hx]
  · simp [hj]

/-! ## Minimal primes of a homogeneous ideal -/

theorem minimalPrimes_homogeneousComponent_mem {k : Type} [Field k] {m : ℕ}
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

theorem minimalPrimes_le_idealOfVars {k : Type} [Field k] {m : ℕ}
    {q : Ideal (MvPolynomial (Fin m) k)}
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    {p : Ideal (MvPolynomial (Fin m) k)} (hp : p ∈ q.minimalPrimes) :
    p ≤ MvPolynomial.idealOfVars (Fin m) k := by
  intro x hx
  rw [mem_idealOfVars_iff_coeff_zero]
  have hx0 : MvPolynomial.homogeneousComponent 0 x ∈ p :=
    minimalPrimes_homogeneousComponent_mem hq hp x hx 0
  rw [MvPolynomial.homogeneousComponent_zero] at hx0
  by_contra hne
  have h1 : (1 : MvPolynomial (Fin m) k) ∈ p := by
    have hmem := p.mul_mem_left (MvPolynomial.C (MvPolynomial.coeff 0 x)⁻¹) hx0
    rwa [← MvPolynomial.C_mul, inv_mul_cancel₀ hne, MvPolynomial.C_1] at hmem
  exact hp.1.1.ne_top ((Ideal.eq_top_iff_one p).mpr h1)

/-- If a minimal prime of `q` contains the irrelevant ideal, then `ringKrullDim (S ⧸ q) ≤ 0`. -/
theorem ringKrullDim_le_zero_of_minimalPrimes_idealOfVars_le {k : Type} [Field k] {m : ℕ}
    {q : Ideal (MvPolynomial (Fin m) k)}
    (hq : ∀ x ∈ q, ∀ j, MvPolynomial.homogeneousComponent j x ∈ q)
    {p : Ideal (MvPolynomial (Fin m) k)} (hp : p ∈ q.minimalPrimes)
    (hle : MvPolynomial.idealOfVars (Fin m) k ≤ p) :
    ringKrullDim (MvPolynomial (Fin m) k ⧸ q) ≤ ((0 : ℕ) : WithBot ℕ∞) := by
  have hp_le : p ≤ MvPolynomial.idealOfVars (Fin m) k := minimalPrimes_le_idealOfVars hq hp
  have hp_eq : p = MvPolynomial.idealOfVars (Fin m) k := le_antisymm hp_le hle
  have hmax : ∀ J ∈ q.minimalPrimes, J.IsMaximal := by
    intro J hJ
    have hJle : J ≤ MvPolynomial.idealOfVars (Fin m) k := minimalPrimes_le_idealOfVars hq hJ
    have hJle_p : J ≤ p := le_trans hJle (le_of_eq hp_eq.symm)
    have hp_le_J : p ≤ J := hp.2 ⟨hJ.1.1, hJ.1.2⟩ hJle_p
    rw [le_antisymm hJle_p hp_le_J, hp_eq]
    exact idealOfVars_isMaximal
  have h0 : Ring.KrullDimLE 0 (MvPolynomial (Fin m) k ⧸ q) :=
    Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr hmax
  exact Ring.krullDimLE_iff.mp h0

theorem homogeneous_span_singleton {k : Type} [Field k] {m : ℕ}
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

theorem hilbertFun_recursion {k : Type} [Field k] {m : ℕ}
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

theorem hilbert_sum_upper_bound {k : Type} [Field k] {m : ℕ}
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
          have hcoeff : f.coeff 0 = 0 := (mem_idealOfVars_iff_coeff_zero f).mp hfI
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