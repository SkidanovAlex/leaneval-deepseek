import Mathlib
import Submission.Work.KeyLemma.Curve.genericSum
import Submission.Work.KeyLemma.Curve.ordBaseBaseField
import Submission.Work.CurveBasics.Order.kxClosure_residue_surjective
import Submission.Work.CurveBasics.Order.integralClosure_adjoin_finite_of_transcendental
import Submission.Work.Charts.place_degree_eq_one_of_isAlgClosed
import Submission.Work.CurveBasics.Order.Setup
import Submission.Work.KeyLemma.Curve.BranchSum.algClosed_subfield_le_base
import Submission.Work.CurveBasics.Order.kxPrimeOfPlace_liesOver
import Submission.Work.KeyLemma.Curve.BranchSumF.transfer

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.


namespace Work.KeyLemma.Curve.BranchSum

set_option synthInstance.maxHeartbeats 16000000
set_option maxHeartbeats 16000000
set_option linter.style.haveILetI false

universe u

/-- The composite `R → Rₚ → Rₚ ⧸ 𝔪` is surjective when `p` is a maximal ideal of `R`, stated with
the quotient map `R ⧸ p → Rₚ ⧸ 𝔪`. -/
theorem residue_comp_algebraMap_surjectiveC {R Rₚ : Type*} [CommRing R] [CommRing Rₚ]
    (p : Ideal R) [p.IsMaximal] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] :
    Function.Surjective ⇑((Ideal.Quotient.mk (IsLocalRing.maximalIdeal Rₚ)).comp
      (algebraMap R Rₚ)) := by
  intro y
  obtain ⟨x, hx⟩ := Ideal.Quotient.mk_surjective
    ((IsLocalization.AtPrime.equivQuotMaximalIdeal p Rₚ).symm y)
  refine ⟨x, ?_⟩
  rw [RingHom.comp_apply,
    ← IsLocalization.AtPrime.equivQuotMaximalIdeal_apply_mk p Rₚ x, hx]
  exact (IsLocalization.AtPrime.equivQuotMaximalIdeal p Rₚ).apply_symm_apply y

/-- The composite `R → Rₚ → Rₚ ⧸ 𝔪` is surjective when `p` is a maximal ideal of `R`. -/
theorem residue_comp_surjectiveC {R Rₚ : Type*} [CommRing R] [CommRing Rₚ]
    (p : Ideal R) [p.IsMaximal] [Algebra R Rₚ] [IsLocalization.AtPrime Rₚ p] [IsLocalRing Rₚ] :
    Function.Surjective ⇑((IsLocalRing.residue Rₚ).comp (algebraMap R Rₚ)) :=
  residue_comp_algebraMap_surjectiveC p

/-- **The residue field of `R' = (k[h]^{int}_N)_P` is `k`.**  Version of `residueFieldIso`
that also assumes the compatibility `hKE` of the `k(h)`- and `K(C)`-algebra structures on `N`;
this is what makes the scalar towers `k → k[h] → N` and `k → k(h) → N` usable. -/
theorem residueFieldIsoKE {k : Type u} [Field k] [IsAlgClosed k]
    (C : Work.CurveBasics.Curve k) (h : C.functionField) (hht : Transcendental k h)
    [FiniteDimensional ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField]
    [Algebra.IsSeparable ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField]
    {N : Type u} [Field N] [Algebra ↥(Work.KeyLemma.Curve.baseField C h) N] [Algebra k N]
    [IsScalarTower k ↥(Work.KeyLemma.Curve.baseField C h) N]
    [IsGalois ↥(Work.KeyLemma.Curve.baseField C h) N]
    [Algebra ↥C.functionField N]
    [IsScalarTower ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField N]
    [FiniteDimensional ↥(Work.KeyLemma.Curve.baseField C h) N]
    [Algebra ↥(Work.CurveBasics.Curve.ordBase C h) N]
    [IsScalarTower ↥(Work.CurveBasics.Curve.ordBase C h) ↥(Work.KeyLemma.Curve.baseField C h) N]
    (hKE : (algebraMap ↥(Work.KeyLemma.Curve.baseField C h) N)
      = (algebraMap ↥C.functionField N).comp
        (algebraMap ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField))
    (hAE : (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) N)
      = (algebraMap ↥C.functionField N).comp
        (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) ↥C.functionField))
    [IsFractionRing ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) N]
    (P : Ideal ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)) [P.IsPrime]
    [P.LiesOver (Work.CurveBasics.Curve.ordIdeal C h)]
    [Algebra k (Localization.AtPrime P)]
    [Algebra ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) (Localization.AtPrime P)]
    [IsLocalization.AtPrime (Localization.AtPrime P) P]
    [Algebra (Localization.AtPrime P) N]
    [IsScalarTower ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
      (Localization.AtPrime P) N]
    [IsScalarTower k (Localization.AtPrime P) N]
    [IsFractionRing (Localization.AtPrime P) N] :
    ∃ e : IsLocalRing.ResidueField (Localization.AtPrime P) ≃+* k,
      ∀ c : k, e (IsLocalRing.residue (Localization.AtPrime P)
        (algebraMap k (Localization.AtPrime P) c)) = c := by
  classical
  -- the canonical `OreLocalization` algebra structure on `R'`, for which the tower law applies
  letI : Algebra ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
      (Localization.AtPrime P) := OreLocalization.instAlgebra
  haveI : IsLocalization.AtPrime (Localization.AtPrime P) P := inferInstance
  have hSTalg : ∀ r : ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N),
      algebraMap (Localization.AtPrime P) N
        (algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
          (Localization.AtPrime P) r)
      = algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) N r :=
    fun r => (IsScalarTower.algebraMap_apply
      ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
      (Localization.AtPrime P) N r).symm
  have hgen : (⟨h, Algebra.subset_adjoin (Set.mem_singleton h)⟩ :
      ↥(Work.CurveBasics.Curve.ordBase C h)) = Work.CurveBasics.Curve.kxGen C h :=
    Subtype.ext rfl
  have hordIdeal_eq : Work.CurveBasics.Curve.ordIdeal C h
      = Work.CurveBasics.Curve.kxIdeal C h := by
    rw [Work.CurveBasics.Curve.ordIdeal, Work.CurveBasics.Curve.kxIdeal, hgen]
  haveI hAmax : (Work.CurveBasics.Curve.ordIdeal C h).IsMaximal := by
    rw [hordIdeal_eq]
    exact Work.CurveBasics.Order.kxIdeal_isMaximal C h hht
  haveI hPmax : P.IsMaximal :=
    Ideal.IsMaximal.of_liesOver_isMaximal P (Work.CurveBasics.Curve.ordIdeal C h)
  have hcoe : ∀ a : ↥(Work.CurveBasics.Curve.ordBase C h),
      algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) N
        (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
          ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) a)
      = algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) N a :=
    fun a => rfl
  let g : ↥(Work.CurveBasics.Curve.ordBase C h) →+* k :=
    (Work.CurveBasics.Curve.kxEvalZero C h hht).toRingHom
  have hg_apply : ∀ z : ↥(Work.CurveBasics.Curve.ordBase C h),
      g z = (Work.CurveBasics.Curve.kxEvalZero C h hht) z := fun z => rfl
  let f : k →+* IsLocalRing.ResidueField (Localization.AtPrime P) :=
    (IsLocalRing.residue (Localization.AtPrime P)).comp (algebraMap k (Localization.AtPrime P))
  let ψ : ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) →+*
      IsLocalRing.ResidueField (Localization.AtPrime P) :=
    (IsLocalRing.residue (Localization.AtPrime P)).comp
      (algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
        (Localization.AtPrime P))
  have hψsurj : Function.Surjective ψ := residue_comp_surjectiveC P
  have hψA0 : ∀ z : ↥(Work.CurveBasics.Curve.ordBase C h),
      ψ (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
        ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) z) = f (g z) := by
    intro z
    have hdiff : z - algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z)
        ∈ Work.CurveBasics.Curve.ordIdeal C h := by
      rw [hordIdeal_eq]
      change z - algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z)
        ∈ Ideal.span {Work.CurveBasics.Curve.kxGen C h}
      rw [Work.CurveBasics.Curve.kx_span_gen_eq_ker C h hht, RingHom.mem_ker]
      change (Work.CurveBasics.Curve.kxEvalZero C h hht)
        (z - algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z)) = 0
      rw [map_sub, AlgHom.commutes, ← hg_apply z]
      simp
    have hmemP : algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
        ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
        (z - algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z)) ∈ P :=
      (Ideal.mem_of_liesOver P (Work.CurveBasics.Curve.ordIdeal C h)
        (z - algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z))).mp hdiff
    have hψzero : ψ (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
        ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
        (z - algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z))) = 0 := by
      have h1 : algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
          (Localization.AtPrime P)
          (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
            ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
            (z - algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z)))
          ∈ IsLocalRing.maximalIdeal (Localization.AtPrime P) :=
        (IsLocalization.AtPrime.to_map_mem_maximal_iff (Localization.AtPrime P) P _).mpr hmemP
      have h2 : algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
          (Localization.AtPrime P)
          (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
            ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
            (z - algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z)))
          ∈ RingHom.ker (IsLocalRing.residue (Localization.AtPrime P)) := by
        rw [IsLocalRing.ker_residue]
        exact h1
      rw [RingHom.mem_ker] at h2
      show IsLocalRing.residue (Localization.AtPrime P)
        (algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
          (Localization.AtPrime P)
          (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
            ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
            (z - algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z)))) = 0
      exact h2
    have hψk : ψ (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
        ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
        (algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z))) = f (g z) := by
      have hR : algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
          (Localization.AtPrime P)
          (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
            ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
            (algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z)))
          = algebraMap k (Localization.AtPrime P) (g z) := by
        apply IsFractionRing.injective (Localization.AtPrime P) N
        rw [hSTalg (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
              ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
              (algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z)))]
        rw [hcoe (algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z))]
        rw [RingHom.congr_fun hAE (algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z))]
        simp only [RingHom.comp_apply]
        have e1 : algebraMap ↥(Work.CurveBasics.Curve.ordBase C h) ↥C.functionField
              (algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z))
            = algebraMap k ↥C.functionField (g z) :=
          IsScalarTower.algebraMap_apply k ↥(Work.CurveBasics.Curve.ordBase C h)
            ↥C.functionField (g z)
        rw [e1]
        have e2 : algebraMap k N (g z) = algebraMap ↥(Work.KeyLemma.Curve.baseField C h) N
            (algebraMap k ↥(Work.KeyLemma.Curve.baseField C h) (g z)) := by
          refine @IsScalarTower.algebraMap_apply k ↥(Work.KeyLemma.Curve.baseField C h)
            N _ _ _ _ _ _ ?_ (g z)
          assumption
        have e3 : algebraMap ↥(Work.KeyLemma.Curve.baseField C h) N
              (algebraMap k ↥(Work.KeyLemma.Curve.baseField C h) (g z))
            = algebraMap ↥C.functionField N
                (algebraMap ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField
                  (algebraMap k ↥(Work.KeyLemma.Curve.baseField C h) (g z))) :=
          RingHom.congr_fun hKE (algebraMap k ↥(Work.KeyLemma.Curve.baseField C h) (g z))
        have e4 : algebraMap ↥(Work.KeyLemma.Curve.baseField C h) ↥C.functionField
              (algebraMap k ↥(Work.KeyLemma.Curve.baseField C h) (g z))
            = algebraMap k ↥C.functionField (g z) :=
          IsScalarTower.algebraMap_apply k ↥(Work.KeyLemma.Curve.baseField C h)
            ↥C.functionField (g z)
        have e5 : algebraMap k N (g z)
            = algebraMap ↥C.functionField N (algebraMap k ↥C.functionField (g z)) :=
          e2.trans (e3.trans (congrArg (algebraMap ↥C.functionField N) e4))
        rw [← e5]
        have e6 : algebraMap k N (g z) = algebraMap (Localization.AtPrime P) N
            (algebraMap k (Localization.AtPrime P) (g z)) := by
          refine @IsScalarTower.algebraMap_apply k (Localization.AtPrime P)
            N _ _ _ _ _ _ ?_ (g z)
          assumption
        rw [← e6]
      show IsLocalRing.residue (Localization.AtPrime P)
        (algebraMap ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
          (Localization.AtPrime P)
          (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
            ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
            (algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z)))) = f (g z)
      rw [hR]
      rfl
    have hsplit : algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
        ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) z
        = algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
            ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
            (algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z))
          + algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
            ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
            (z - algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z)) := by
      have hz : algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z)
          + (z - algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z)) = z := by
        abel
      rw [← map_add, hz]
    calc ψ (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
          ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N) z)
        = ψ (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
              ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
              (algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z))
            + algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
              ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
              (z - algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z))) := by
          rw [hsplit]
      _ = ψ (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
              ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
              (algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z)))
            + ψ (algebraMap ↥(Work.CurveBasics.Curve.ordBase C h)
              ↥(integralClosure ↥(Work.CurveBasics.Curve.ordBase C h) N)
              (z - algebraMap k ↥(Work.CurveBasics.Curve.ordBase C h) (g z))) :=
          map_add _ _ _
      _ = f (g z) + 0 := by rw [hψk, hψzero]
      _ = f (g z) := by rw [add_zero]
  letI : Algebra k (IsLocalRing.ResidueField (Localization.AtPrime P)) := f.toAlgebra
  haveI hInt : Algebra.IsIntegral k (IsLocalRing.ResidueField (Localization.AtPrime P)) := by
    refine ⟨fun y => ?_⟩
    obtain ⟨n, rfl⟩ := hψsurj y
    refine IsIntegral.map_of_comp_eq g ψ ?_ (Algebra.IsIntegral.isIntegral n)
    ext z
    exact (hψA0 z).symm
  have hbij : Function.Bijective f :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
      (k := k) (K := IsLocalRing.ResidueField (Localization.AtPrime P))
  exact ⟨(RingEquiv.ofBijective f hbij).symm, fun c => RingEquiv.symm_apply_apply _ c⟩

end Work.KeyLemma.Curve.BranchSum
