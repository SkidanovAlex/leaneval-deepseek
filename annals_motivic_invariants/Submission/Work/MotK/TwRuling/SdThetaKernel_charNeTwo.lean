import Mathlib
import Submission.Work.MotK.TwRuling.SdThetaSdualT
import Submission.Work.MotK.TwRuling.SdThetaFracTop_charNeTwo
import Submission.Work.MotK.TwCensus.TrdegQuotientTwo
import Submission.Work.MotK.TwCensus.TwistFieldTGRatFuncTrdeg
import Submission.Work.MotK.TwRuling.SdualTCoeffX0
import Submission.Work.MotK.TwRuling.CoeffMapInjectivePrimeMonic

set_option linter.unusedVariables false -- v435-speed

set_option synthInstance.maxHeartbeats 400000 -- v435-synth

/-!
# `Work.MotK.TwRuling.SdThetaKernel_charNeTwo` — the `sdTheta` presentation away from char 2

`Work.MotK.TwRuling.SdThetaKernel` (the statement without the hypothesis `(2 : K) ≠ 0`) is
**FALSE in characteristic 2**: there the two ruling vectors of the twisted Klein curve are
proportional, so `sdPhi` loses its `t`-dependence and `sdR` drops to transcendence degree `<= 1`,
while `K[x]/(sdualT)` has degree `2` (see the module docstring of
`Submission/Work/MotK/TwRuling/SdThetaKernel.lean`).  The repair is the hypothesis `(2 : K) ≠ 0`,
for which the *fraction-field* input `Work.MotK.TwRuling.SdThetaFracTop_charNeTwo` is proved
(sorry-free).

This file is the repaired statement; its proof is copied verbatim from `SdThetaKernel` apart from the
one call site, and it is what `Work.MotK.TGen.SdualTClass` needs in characteristic `!= 2` (the
characteristic-2 case is handled by a different presentation
`Work.MotK.TwRuling.SdualTClass_charTwo`, because there the ruling `A + t·B` degenerates although the
fibration `kleinTwR|_{s'=0} : {s' = 0} ⇢ C_h` still has rational fibres — see
`Submission/Work/MotK/TwRuling/NOTE_charTwo_fibres.md`).

The two bricks `Work.MotK.TwRuling.SdualTDegreeX0` and
`Work.MotK.TwRuling.CoeffMapInjectiveOfPrimeMonic` are consumed; they are being replaced by the
sorry-free copies `Work.MotK.TwRuling.SdualTCoeffX0` and
`Work.MotK.TwRuling.CoeffMapInjectivePrimeMonic` (re-point this file's two call sites when those
land).
-/

set_option maxRecDepth 8000

namespace Work.MotK.TwRuling
theorem ker_aevalPoly_eq_span_charNeTwo
    {K : Type} [Field K] {A : Type} [Field A] [Algebra K A]
    (φ : Polynomial (MvPolynomial (Fin 2) K) →ₐ[K] A)
    (g : Polynomial (MvPolynomial (Fin 2) K))
    (hg : Prime g) (hmonic : g.Monic)
    (hφg : φ g = 0)
    (hinj : Function.Injective fun r : MvPolynomial (Fin 2) K => φ (Polynomial.C r)) :
    RingHom.ker (φ : Polynomial (MvPolynomial (Fin 2) K) →+* A)
      = Ideal.span {g} := by
  classical
  set R := MvPolynomial (Fin 2) K with hR
  set B := FractionRing R with hB
  let coe : R →+* A := φ.toRingHom.comp Polynomial.C
  have hcoe : ∀ r : R, coe r = φ (Polynomial.C r) := fun r => rfl
  have hinjR : Function.Injective coe := by
    intro r s h
    exact hinj (by simpa only [hcoe] using h)
  let f : B →+* A := IsFractionRing.lift (g := coe) hinjR
  have hf : ∀ r : R, f (algebraMap R B r) = φ (Polynomial.C r) := by
    intro r
    have h1 : f (algebraMap R B r) = coe r :=
      IsFractionRing.lift_algebraMap (A := R) (K := B) (L := A) (g := coe) hinjR r
    rw [h1, hcoe r]
  let ψ : Polynomial B →+* A := Polynomial.eval₂RingHom f (φ Polynomial.X)
  have hfcoe : (f.comp (algebraMap R B) : R →+* A) = coe := by
    refine RingHom.ext fun r => ?_
    rw [RingHom.comp_apply, hf r, hcoe r]
  have hφeval : Polynomial.eval₂RingHom coe (φ Polynomial.X) = φ.toRingHom := by
    refine Polynomial.ringHom_ext' ?_ ?_
    · rw [Polynomial.eval₂RingHom_comp_C]
    · rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X]
      rfl
  have hψ : ∀ p : Polynomial R, ψ (p.map (algebraMap R B)) = φ p := by
    intro p
    have h1 : ψ (p.map (algebraMap R B))
        = (Polynomial.eval₂RingHom (f.comp (algebraMap R B)) (φ Polynomial.X)) p := by
      simp only [ψ, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_map]
    rw [h1, hfcoe, hφeval]
    rfl
  have hgB_monic : (g.map (algebraMap R B)).Monic := hmonic.map _
  have hgB_irr : Irreducible (g.map (algebraMap R B)) :=
    (hmonic.irreducible_iff_irreducible_map_fraction_map).mp hg.irreducible
  have hψgB : ψ (g.map (algebraMap R B)) = 0 := by rw [hψ g, hφg]
  have hmax : (Ideal.span {g.map (algebraMap R B)}).IsMaximal :=
    (Ideal.irreducible_iff_isMaximal_span_singleton hgB_monic.ne_zero).mp hgB_irr
  have hkerψ : RingHom.ker ψ = Ideal.span {g.map (algebraMap R B)} :=
    (hmax.eq_of_le (RingHom.ker_ne_top ψ) (by
      rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, RingHom.mem_ker]
      exact hψgB)).symm
  ext p
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  constructor
  · intro hp
    have hmem : p.map (algebraMap R B) ∈ RingHom.ker ψ := by
      rw [RingHom.mem_ker, hψ p]
      exact hp
    rw [hkerψ, Ideal.mem_span_singleton] at hmem
    exact (hmonic.isPrimitive.dvd_iff_fraction_map_dvd_fraction_map B).mpr hmem
  · rintro ⟨q, rfl⟩
    simp [map_mul, hφg]


theorem SdThetaKernel_charNeTwo (K : Type) [Field K] (h2 : (2 : K) ≠ 0)
    (D : Work.MotV.KleinData K) (hD : D.Good) (h : K)
    (hh : h ≠ 0) (hG : Prime (Work.MotK.TGen.sdualT D.a D.b h)) :
    RingHom.ker (Work.MotK.TGen.sdTheta K D h)
      = Ideal.span {Work.MotK.TGen.sdualT D.a D.b h} := by
  classical
  have ha : D.a ≠ 0 := (mul_ne_zero_iff.mp hD.ab_ne).1
  have hb : D.b ≠ 0 := (mul_ne_zero_iff.mp hD.ab_ne).2
  set u : K := -(D.a ^ 5 * D.b ^ 5 * h ^ 4) with hu
  have hu_ne : u ≠ 0 := by
    rw [hu]
    exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero (pow_ne_zero 5 ha) (pow_ne_zero 5 hb))
      (pow_ne_zero 4 hh))
  set G : MvPolynomial (Fin 3) K := Work.MotK.TGen.sdualT D.a D.b h with hGdef
  set G' : MvPolynomial (Fin 3) K := MvPolynomial.C u⁻¹ * G with hG'def
  have hθG : Work.MotK.TGen.sdTheta K D h G = 0 := by
    rw [hGdef]; exact SdThetaSdualT K D hD h hh
  have hθG' : Work.MotK.TGen.sdTheta K D h G' = 0 := by
    rw [hG'def, map_mul, hθG, mul_zero]
  have hCu_mul : (MvPolynomial.C u : MvPolynomial (Fin 3) K) * MvPolynomial.C u⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hu_ne, map_one]
  have hCui_mul : (MvPolynomial.C u⁻¹ : MvPolynomial (Fin 3) K) * MvPolynomial.C u = 1 := by
    rw [← map_mul, inv_mul_cancel₀ hu_ne, map_one]
  let vu : (MvPolynomial (Fin 3) K)ˣ :=
    ⟨MvPolynomial.C u, MvPolynomial.C u⁻¹, hCu_mul, hCui_mul⟩
  have hG'prime : Prime G' := by
    have hassoc : Associated G' G :=
      ⟨vu, by
        show G' * (MvPolynomial.C u) = G
        rw [hG'def, mul_assoc, mul_comm G (MvPolynomial.C u), ← mul_assoc, ← map_mul,
          inv_mul_cancel₀ hu_ne, map_one, one_mul]⟩
    exact hassoc.prime_iff.mpr hG
  have hcoeff5 : (MvPolynomial.finSuccEquiv K 2 G).coeff 5 = MvPolynomial.C u := by
    refine MvPolynomial.ext _ _ fun m => ?_
    rw [MvPolynomial.finSuccEquiv_coeff_coeff,
      SdualTCoeffX0 K D.a D.b h 5 m le_rfl, MvPolynomial.coeff_C]
    by_cases hm : m = 0
    · subst hm
      have hL : (if 5 = 5 ∧ (0 : Fin 2 →₀ ℕ) = 0 then -(D.a ^ 5 * D.b ^ 5 * h ^ 4) else 0)
          = -(D.a ^ 5 * D.b ^ 5 * h ^ 4) := by simp
      have hR : (if (0 : Fin 2 →₀ ℕ) = 0 then u else 0) = u := by simp
      rw [hL, hR]
    · have hL : (if 5 = 5 ∧ m = 0 then -(D.a ^ 5 * D.b ^ 5 * h ^ 4) else 0) = 0 := by simp [hm]
      have h0 : ¬ ((0 : Fin 2 →₀ ℕ) = m) := fun h => hm h.symm
      rw [hL]
      simp [h0]
  have hcoeff_gt : ∀ k : ℕ, 5 < k → (MvPolynomial.finSuccEquiv K 2 G).coeff k = 0 := by
    intro k hk
    refine MvPolynomial.ext _ _ fun m => ?_
    rw [MvPolynomial.finSuccEquiv_coeff_coeff, SdualTCoeffX0 K D.a D.b h k m (by omega)]
    have hL : (if k = 5 ∧ m = 0 then -(D.a ^ 5 * D.b ^ 5 * h ^ 4) else 0) = 0 := by
      simp [show ¬ (k = 5 ∧ m = 0) by omega]
    rw [hL]
    simp
  have hnat_le : (MvPolynomial.finSuccEquiv K 2 G).natDegree ≤ 5 := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    exact hcoeff_gt N hN
  have hCu_ne : (MvPolynomial.C u : MvPolynomial (Fin 2) K) ≠ 0 :=
    fun h0 => hu_ne (MvPolynomial.C_injective (Fin 2) K (by simpa using h0))
  have hnat : (MvPolynomial.finSuccEquiv K 2 G).natDegree = 5 := by
    refine le_antisymm hnat_le (Polynomial.le_natDegree_of_ne_zero ?_)
    rw [hcoeff5]; exact hCu_ne
  set g : Polynomial (MvPolynomial (Fin 2) K) :=
    Polynomial.C (MvPolynomial.C u⁻¹) * MvPolynomial.finSuccEquiv K 2 G with hg
  have hCui_ne : (MvPolynomial.C u⁻¹ : MvPolynomial (Fin 2) K) ≠ 0 :=
    fun h0 => (inv_ne_zero hu_ne) (MvPolynomial.C_injective (Fin 2) K (by simpa using h0))
  have hgnat : g.natDegree = 5 := by
    rw [hg, Polynomial.natDegree_C_mul hCui_ne, hnat]
  have hgcoeff : g.coeff 5 = 1 := by
    rw [hg, Polynomial.coeff_C_mul, hcoeff5, ← map_mul, inv_mul_cancel₀ hu_ne, map_one]
  have hmonic : g.Monic := by
    show g.coeff g.natDegree = 1
    rw [hgnat, hgcoeff]
  have hΦC : ∀ r : K, (MvPolynomial.finSuccEquiv K 2) (MvPolynomial.C r)
      = Polynomial.C (MvPolynomial.C r) := by
    intro r
    rw [MvPolynomial.finSuccEquiv_apply, MvPolynomial.eval₂Hom_C]
    rfl
  have hg_map : (MvPolynomial.finSuccEquiv K 2) G' = g := by
    rw [hg, hG'def, map_mul, hΦC u⁻¹]
  have hg_prime : Prime g := by
    rw [← hg_map]
    exact (MulEquiv.prime_iff (MvPolynomial.finSuccEquiv K 2)).mpr hG'prime
  have hfrac : Subfield.closure (Set.range (algebraMap
      (Work.MotK.TGen.sdTheta K D h).range (Work.MotK.TGen.sdA K D h))) = ⊤ := by
    have hrange : (Work.MotK.TGen.sdTheta K D h).range = Work.MotK.TGen.sdR K D h := by
      show (MvPolynomial.aeval (Work.MotK.TGen.sdPhi K D h)).range
        = Algebra.adjoin K (Set.range (Work.MotK.TGen.sdPhi K D h))
      exact MvPolynomial.aeval_range (R := K) (f := Work.MotK.TGen.sdPhi K D h)
    rw [hrange]
    exact SdThetaFracTop_charNeTwo K h2 D hD h hh
  have htrdeg : Algebra.trdeg K (Work.MotK.TGen.sdA K D h) = 2 :=
    Work.MotK.TwCensus.TwistFieldTGRatFuncTrdeg K D hD h hh
  have hTr : ∀ (q : Ideal (MvPolynomial (Fin 2) K)), q.IsPrime → q ≠ ⊥ →
      Algebra.trdeg K (FractionRing (MvPolynomial (Fin 2) K ⧸ q)) ≤ 1 :=
    fun q hq hne => by haveI := hq; exact Work.MotK.TwCensus.TrdegQuotientTwo K q hne
  have hinj : Function.Injective fun r : MvPolynomial (Fin 2) K =>
      (Work.MotK.TGen.sdTheta K D h).comp
        (MvPolynomial.finSuccEquiv K 2).symm.toAlgHom (Polynomial.C r) := by
    have hmonic'' : (MvPolynomial.finSuccEquiv K 2 G').Monic := by
      rw [hg_map]; exact hmonic
    exact CoeffMapInjectivePrimeMonic (Work.MotK.TGen.sdTheta K D h) G'
      hG'prime hmonic'' hθG' hfrac htrdeg hTr
  have hker : RingHom.ker ((Work.MotK.TGen.sdTheta K D h).comp
      (MvPolynomial.finSuccEquiv K 2).symm.toAlgHom) = Ideal.span {g} := by
    refine ker_aevalPoly_eq_span_charNeTwo ((Work.MotK.TGen.sdTheta K D h).comp
      (MvPolynomial.finSuccEquiv K 2).symm.toAlgHom) g hg_prime hmonic ?_ ?_
    · rw [← hg_map]
      exact (congrArg (fun z => (Work.MotK.TGen.sdTheta K D h) z)
        (AlgEquiv.symm_apply_apply (MvPolynomial.finSuccEquiv K 2) G')).trans hθG'
    · exact hinj
  have hkerθ' : RingHom.ker (Work.MotK.TGen.sdTheta K D h) = Ideal.span {G'} := by
    ext f
    rw [RingHom.mem_ker, Ideal.mem_span_singleton]
    have h1 : (Work.MotK.TGen.sdTheta K D h) f
        = ((Work.MotK.TGen.sdTheta K D h).comp
            (MvPolynomial.finSuccEquiv K 2).symm.toAlgHom)
            ((MvPolynomial.finSuccEquiv K 2) f) := by
      rw [AlgHom.comp_apply]
      exact congrArg (fun z => (Work.MotK.TGen.sdTheta K D h) z)
        (AlgEquiv.symm_apply_apply (MvPolynomial.finSuccEquiv K 2) f).symm
    rw [h1, ← RingHom.mem_ker, hker, Ideal.mem_span_singleton, ← hg_map]
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨(MvPolynomial.finSuccEquiv K 2).symm c, ?_⟩
      have h2 := congrArg (MvPolynomial.finSuccEquiv K 2).symm hc
      simpa using h2
    · rintro ⟨c, hc⟩
      exact ⟨(MvPolynomial.finSuccEquiv K 2) c, by rw [hc, map_mul]⟩
  have hspan : Ideal.span {G'} = Ideal.span {G} := by
    refine le_antisymm ?_ ?_
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_span_singleton]
      exact ⟨MvPolynomial.C u⁻¹, by rw [hG'def, mul_comm]⟩
    · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_span_singleton]
      refine ⟨MvPolynomial.C u, ?_⟩
      rw [hG'def, mul_assoc, mul_comm G (MvPolynomial.C u), ← mul_assoc, ← map_mul,
        inv_mul_cancel₀ hu_ne, map_one, one_mul]
  exact hkerθ'.trans hspan


end Work.MotK.TwRuling
