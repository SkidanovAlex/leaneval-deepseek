import Mathlib
import Submission.Work.AbVar.ProjectiveLine.isIntegral_P1
import Submission.Work.AbVar.P1Chart.Basic
import Submission.Work.AbVar.P1Chart.Cover
import Submission.Work.AbVar.P1Chart.ChartK
import Submission.Work.AbVar.P1Chart.awayX_algEquiv
import Submission.Work.AbVar.P1Chart.Smooth

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory HomogeneousLocalization MvPolynomial

universe u

namespace Work.KeyLemma.Curve

/-! ### 1. a second point of `Proj k[X₀,X₁]`, and closedness -/

lemma X0_isH {k : Type u} [Field k] :
    (Ideal.span {(MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k)}).IsHomogeneous
      (Work.AbVar.P1Grading k) := by
  apply Ideal.homogeneous_span
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨1, (MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X k 0)⟩

def x0P (k : Type u) [Field k] : ProjectiveSpectrum (Work.AbVar.P1Grading k) where
  asHomogeneousIdeal :=
    (Ideal.span {(MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k)}).homogeneousHull _
  isPrime := by
    have h := Ideal.IsHomogeneous.toIdeal_homogeneousHull_eq_self
      (I := Ideal.span {(MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k)}) (X0_isH (k:=k))
    rw [h]
    exact (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero 0)).mpr MvPolynomial.X_prime
  not_irrelevant_le := by
    intro hle
    have hx1 : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k) ∈
        HomogeneousIdeal.irrelevant (Work.AbVar.P1Grading k) :=
      HomogeneousIdeal.mem_irrelevant_of_mem (𝒜 := Work.AbVar.P1Grading k) (i := 1) (by norm_num)
        ((MvPolynomial.mem_homogeneousSubmodule 1 _).mpr (MvPolynomial.isHomogeneous_X k 1))
    have hmem : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) k) ∈
        ((Ideal.span {(MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k)}).homogeneousHull
          (Work.AbVar.P1Grading k)).toIdeal := hle hx1
    have h := Ideal.IsHomogeneous.toIdeal_homogeneousHull_eq_self
      (I := Ideal.span {(MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k)}) (X0_isH (k:=k))
    rw [h, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, hc⟩ := hmem
    exact absurd (MvPolynomial.X_dvd_X.mp ⟨c, hc⟩) (by decide)

lemma x0P_toIdeal (k : Type u) [Field k] : ((x0P k).asHomogeneousIdeal).toIdeal =
    Ideal.span {(MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k)} :=
  Ideal.IsHomogeneous.toIdeal_homogeneousHull_eq_self (X0_isH (k:=k))

lemma x0P_ne_zeroPt (k : Type u) [Field k] : x0P k ≠ Work.AbVar.ProjectiveLine.zeroPt k := by
  intro h
  have h2 : ((x0P k).asHomogeneousIdeal).toIdeal =
      ((Work.AbVar.ProjectiveLine.zeroPt k).asHomogeneousIdeal).toIdeal :=
    congrArg (fun y => y.asHomogeneousIdeal.toIdeal) h
  rw [x0P_toIdeal, Work.AbVar.ProjectiveLine.zeroPt_asHomogeneousIdeal,
      HomogeneousIdeal.toIdeal_bot] at h2
  have h3 : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) k) ∈
      (⊥ : Ideal (MvPolynomial (Fin 2) k)) := h2 ▸ Ideal.mem_span_singleton_self _
  exact MvPolynomial.X_ne_zero 0 (Ideal.mem_bot.mp h3)

lemma toIdeal_ne_bot_of_isClosed (k : Type u) [Field k]
    (x : ProjectiveSpectrum (Work.AbVar.P1Grading k))
    (hx : IsClosed ({x} : Set (ProjectiveSpectrum (Work.AbVar.P1Grading k)))) :
    x.asHomogeneousIdeal.toIdeal ≠ ⊥ := by
  intro hbot
  have hxid : x = Work.AbVar.ProjectiveLine.zeroPt k := by
    apply ProjectiveSpectrum.ext
    apply HomogeneousIdeal.ext
    rw [hbot, Work.AbVar.ProjectiveLine.zeroPt_asHomogeneousIdeal, HomogeneousIdeal.toIdeal_bot]
  subst hxid
  have hle : Work.AbVar.ProjectiveLine.zeroPt k ≤ x0P k := by
    rw [← ProjectiveSpectrum.as_ideal_le_as_ideal, Work.AbVar.ProjectiveLine.zeroPt_asHomogeneousIdeal]
    exact bot_le
  have hmem : x0P k ∈ closure ({Work.AbVar.ProjectiveLine.zeroPt k} :
      Set (ProjectiveSpectrum (Work.AbVar.P1Grading k))) :=
    (ProjectiveSpectrum.le_iff_mem_closure (Work.AbVar.P1Grading k) _ _).mp hle
  rw [hx.closure_eq, Set.mem_singleton_iff] at hmem
  exact x0P_ne_zeroPt k hmem

/-! ### 2. `AtPrime` is a domain -/

lemma atPrime_isDomain (k : Type u) [Field k]
    (x : ProjectiveSpectrum (Work.AbVar.P1Grading k)) :
    IsDomain (HomogeneousLocalization.AtPrime (Work.AbVar.P1Grading k)
      x.asHomogeneousIdeal.toIdeal) := by
  haveI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  haveI : IsDomain (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) := inferInstance
  refine Function.Injective.isDomain
    (algebraMap (HomogeneousLocalization.AtPrime (Work.AbVar.P1Grading k)
      x.asHomogeneousIdeal.toIdeal) (Localization x.asHomogeneousIdeal.toIdeal.primeCompl)) ?_
  intro a b h
  exact HomogeneousLocalization.val_injective _ (by
    simpa only [HomogeneousLocalization.algebraMap_apply] using h)

/-! ### 3. a nonzero homogeneous element of a nonzero homogeneous ideal -/

lemma exists_homog_mem (k : Type u) [Field k]
    (x : ProjectiveSpectrum (Work.AbVar.P1Grading k))
    (hP : x.asHomogeneousIdeal.toIdeal ≠ ⊥) :
    ∃ (j : ℕ) (h : MvPolynomial (Fin 2) k),
      0 < j ∧ h ≠ 0 ∧ h ∈ x.asHomogeneousIdeal.toIdeal ∧
        h ∈ Work.AbVar.P1Grading k j := by
  classical
  obtain ⟨a, ha, ha0⟩ := x.asHomogeneousIdeal.toIdeal.ne_bot_iff.mp hP
  have hI := x.asHomogeneousIdeal.isHomogeneous
  have hmem : ∀ i, (DirectSum.decompose (Work.AbVar.P1Grading k) a i :
      MvPolynomial (Fin 2) k) ∈ x.asHomogeneousIdeal.toIdeal := fun i => (hI.mem_iff).mp ha i
  have hsum := DirectSum.sum_support_decompose (Work.AbVar.P1Grading k) a
  have hex : ∃ i ∈ (DirectSum.decompose (Work.AbVar.P1Grading k) a).support,
      (DirectSum.decompose (Work.AbVar.P1Grading k) a i : MvPolynomial (Fin 2) k) ≠ 0 := by
    by_contra h
    push Not at h
    apply ha0
    rw [← hsum]
    exact Finset.sum_eq_zero fun i hi => h i hi
  obtain ⟨i, hi, hne⟩ := hex
  refine ⟨i, (DirectSum.decompose (Work.AbVar.P1Grading k) a i : MvPolynomial (Fin 2) k),
    ?_, hne, hmem i, (DirectSum.decompose (Work.AbVar.P1Grading k) a i).2⟩
  by_contra hi0
  rw [not_lt] at hi0
  obtain rfl : i = 0 := Nat.eq_zero_of_le_zero hi0
  have hmem0 : (DirectSum.decompose (Work.AbVar.P1Grading k) a 0 : MvPolynomial (Fin 2) k) ∈
      Work.AbVar.P1Chart.gr k 0 := (DirectSum.decompose (Work.AbVar.P1Grading k) a 0).2
  have hc : (DirectSum.decompose (Work.AbVar.P1Grading k) a 0 :
      MvPolynomial (Fin 2) k).coeff 0 ≠ 0 := by
    intro hc
    apply hne
    rw [Work.AbVar.P1Chart.gr_zero_eq_C (k:=k) hmem0, hc]
    simp
  have hunit : IsUnit (DirectSum.decompose (Work.AbVar.P1Grading k) a 0 :
      MvPolynomial (Fin 2) k) := by
    rw [Work.AbVar.P1Chart.gr_zero_eq_C (k:=k) hmem0]
    exact isUnit_iff_exists_inv.mpr ⟨MvPolynomial.C
      ((DirectSum.decompose (Work.AbVar.P1Grading k) a 0 : MvPolynomial (Fin 2) k).coeff 0)⁻¹, by
        rw [← MvPolynomial.C_mul, mul_inv_cancel₀ hc, MvPolynomial.C_1]⟩
  have htop : x.asHomogeneousIdeal.toIdeal = ⊤ :=
    Ideal.eq_top_of_isUnit_mem _ (hmem 0) hunit
  refine x.not_irrelevant_le (toIdeal_le_toIdeal_iff.mp ?_)
  rw [htop]
  exact le_top

/-! ### 4. the maximal ideal of `AtPrime` is nonzero -/

lemma maximalIdeal_atPrime_ne_bot (k : Type u) [Field k]
    (x : ProjectiveSpectrum (Work.AbVar.P1Grading k)) (i : Fin 2)
    (hXi : (MvPolynomial.X i : MvPolynomial (Fin 2) k) ∉ x.asHomogeneousIdeal.toIdeal)
    (hP : x.asHomogeneousIdeal.toIdeal ≠ ⊥) :
    IsLocalRing.maximalIdeal (HomogeneousLocalization.AtPrime (Work.AbVar.P1Grading k)
      x.asHomogeneousIdeal.toIdeal) ≠ ⊥ := by
  haveI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  obtain ⟨j, h, hj, hh0, hhP, hhj⟩ := exists_homog_mem k x hP
  have hXij : (MvPolynomial.X i : MvPolynomial (Fin 2) k) ^ j ∈ Work.AbVar.P1Grading k j := by
    simpa using SetLike.pow_mem_graded j (Work.AbVar.P1Chart.X_mem k i)
  have hXij_notin : ((MvPolynomial.X i : MvPolynomial (Fin 2) k) ^ j) ∉
      x.asHomogeneousIdeal.toIdeal := fun hh => hXi ((x.isPrime).mem_of_pow_mem j hh)
  let yden : ↥(x.asHomogeneousIdeal.toIdeal.primeCompl) :=
    ⟨(MvPolynomial.X i)^j, hXij_notin⟩
  let c : HomogeneousLocalization.NumDenSameDeg (Work.AbVar.P1Grading k)
      x.asHomogeneousIdeal.toIdeal.primeCompl :=
    ⟨j, ⟨h, hhj⟩, ⟨(MvPolynomial.X i)^j, hXij⟩, yden.2⟩
  let u := HomogeneousLocalization.mk c
  have hval : HomogeneousLocalization.val u =
      Localization.mk h yden := HomogeneousLocalization.val_mk c
  have hnotunit : ¬ IsUnit u := by
    rw [← HomogeneousLocalization.isUnit_iff_isUnit_val (Work.AbVar.P1Grading k)
      x.asHomogeneousIdeal.toIdeal]
    rw [hval, Localization.mk_eq_mk'_apply]
    have hiff := IsLocalization.AtPrime.isUnit_mk'_iff
        (Localization x.asHomogeneousIdeal.toIdeal.primeCompl) x.asHomogeneousIdeal.toIdeal
        h yden
    rw [hiff]
    exact fun hmem => hmem hhP
  have hne : u ≠ 0 := by
    intro hu0
    have hz : Localization.mk h yden = 0 := by
      rw [← hval, hu0, HomogeneousLocalization.val_zero]
    rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff] at hz
    obtain ⟨m, hm⟩ := hz
    rcases mul_eq_zero.mp hm with hm0 | hh
    · exact (Ideal.mem_primeCompl_iff.mp m.2) (hm0 ▸ Ideal.zero_mem _)
    · exact hh0 hh
  intro hbot
  have hmem : u ∈ IsLocalRing.maximalIdeal (HomogeneousLocalization.AtPrime
      (Work.AbVar.P1Grading k) x.asHomogeneousIdeal.toIdeal) := by
    rw [IsLocalRing.mem_maximalIdeal]
    exact hnotunit
  rw [hbot] at hmem
  exact hne (by simpa using hmem)

/-! ### 5. `AtPrime` is a localization of `Polynomial k` at a prime -/

lemma exists_ringEquiv_localization (k : Type u) [Field k]
    (x : ProjectiveSpectrum (Work.AbVar.P1Grading k)) (i : Fin 2)
    (hXi : (MvPolynomial.X i : MvPolynomial (Fin 2) k) ∉ x.asHomogeneousIdeal.toIdeal) :
    ∃ (q : Ideal (Polynomial k)) (_ : q.IsPrime),
      Nonempty (HomogeneousLocalization.AtPrime (Work.AbVar.P1Grading k)
        x.asHomogeneousIdeal.toIdeal ≃+* Localization.AtPrime q) := by
  haveI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have hxmem : x ∈ ↑(ProjectiveSpectrum.basicOpen (Work.AbVar.P1Grading k)
      (MvPolynomial.X i)) :=
    (ProjectiveSpectrum.mem_coe_basicOpen (Work.AbVar.P1Grading k) (MvPolynomial.X i) x).mpr
      (fun h => hXi ((HomogeneousIdeal.mem_iff).mpr h))
  let xx : ↥(ProjectiveSpectrum.basicOpen (Work.AbVar.P1Grading k) (MvPolynomial.X i)) :=
    ⟨x, hxmem⟩
  let A := Away (Work.AbVar.P1Grading k) (MvPolynomial.X i)
  let B := HomogeneousLocalization.AtPrime (Work.AbVar.P1Grading k) x.asHomogeneousIdeal.toIdeal
  let b : PrimeSpectrum A :=
    (ProjectiveSpectrum.Proj.toSpec (Work.AbVar.P1Grading k) (MvPolynomial.X i)).base xx
  let p : Ideal A := b.asIdeal
  have hp : p.IsPrime := b.isPrime
  haveI : p.IsPrime := hp
  letI : Algebra A B := (HomogeneousLocalization.mapId (Work.AbVar.P1Grading k)
    (Submonoid.powers_le.mpr xx.2)).toAlgebra
  haveI hloc : IsLocalization p.primeCompl B :=
    ProjectiveSpectrum.Proj.isLocalization_atPrime (Work.AbVar.P1Grading k) (MvPolynomial.X i) xx
      (Work.AbVar.P1Chart.X_mem k i) (by norm_num)
  let e : A ≃+* Polynomial k := (Work.AbVar.P1Chart.awayXAlgEquiv k i).toRingEquiv
  refine ⟨Ideal.map e p, inferInstance, ?_⟩
  refine ⟨?_⟩
  have hcomap : Ideal.comap e (Ideal.map e p) = p := Ideal.comap_map_of_bijective _ e.bijective
  have H : Submonoid.map e.toMonoidHom p.primeCompl = (Ideal.map e p).primeCompl := by
    ext y
    simp only [Submonoid.mem_map, SetLike.mem_coe]
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact fun hmem => hz (hcomap ▸ Ideal.mem_comap.mpr hmem)
    · intro hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      intro hz
      exact hy (by rw [← e.apply_symm_apply y]; exact Ideal.mem_map_of_mem e hz)
  exact IsLocalization.ringEquivOfRingEquiv (S := B)
    (Q := Localization.AtPrime (Ideal.map e p)) e H

/-! ### 6. the main theorem -/

theorem p1_stalk_isDiscreteValuationRing {k : Type u} [Field k] [AlgebraicGeometry.IsIntegral (Work.AbVar.P1 k).left]
    (x : (Work.AbVar.P1 k).left) (hx : IsClosed ({x} : Set (Work.AbVar.P1 k).left)) :
    IsDiscreteValuationRing ((Work.AbVar.P1 k).left.presheaf.stalk x) := by
  haveI : x.asHomogeneousIdeal.toIdeal.IsPrime := x.isPrime
  have hPnz : x.asHomogeneousIdeal.toIdeal ≠ ⊥ := toIdeal_ne_bot_of_isClosed k x hx
  obtain ⟨i, hXi⟩ : ∃ i : Fin 2, (MvPolynomial.X i : MvPolynomial (Fin 2) k) ∉
      x.asHomogeneousIdeal.toIdeal := by
    by_contra hcon
    push Not at hcon
    refine x.not_irrelevant_le (toIdeal_le_toIdeal_iff.mp ?_)
    refine le_trans (Work.AbVar.P1Chart.irrelevant_le_span_X k) ?_
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact hcon j
  obtain ⟨q, hq, ⟨E⟩⟩ := exists_ringEquiv_localization k x i hXi
  haveI : q.IsPrime := hq
  let B := HomogeneousLocalization.AtPrime (Work.AbVar.P1Grading k) x.asHomogeneousIdeal.toIdeal
  haveI hdom : IsDomain B := atPrime_isDomain k x
  haveI hmax : IsLocalRing.maximalIdeal B ≠ ⊥ := maximalIdeal_atPrime_ne_bot k x i hXi hPnz
  haveI hPID : IsPrincipalIdealRing B :=
    IsPrincipalIdealRing.of_surjective E.symm.toRingHom E.symm.bijective.2
  haveI hDVR : IsDiscreteValuationRing B := ⟨hmax⟩
  let ee : HomogeneousLocalization.AtPrime (Work.AbVar.P1Grading k)
        x.asHomogeneousIdeal.toIdeal ≃+* ((Work.AbVar.P1 k).left.presheaf.stalk x) :=
    (Proj.stalkIso (Work.AbVar.P1Grading k) x).symm.commRingCatIsoToRingEquiv
  exact IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing ee


end Work.KeyLemma.Curve
