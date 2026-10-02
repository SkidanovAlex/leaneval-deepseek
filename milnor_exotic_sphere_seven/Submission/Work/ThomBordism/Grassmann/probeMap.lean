import Mathlib
import Submission.Work.ThomBordism.Grassmann.probeRot

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSimpArgs false

namespace Work.ThomBordism.Grassmann

open Work.TangentClasses Work.Projective

noncomputable section

variable {k m : ℕ}

/-! ## Continuity of the unit vector and of the frame -/

theorem continuous_cxOf : Continuous (cxOf : (Fin 3 → ℂ) → E3) :=
  PiLp.continuous_toLp 2 (fun _ : Fin 3 => ℂ)

theorem continuousOn_cxUnit :
    ContinuousOn (fun v : Fin 3 → ℂ => cxUnit v) {v | v ≠ 0} := by
  refine ContinuousOn.smul (ContinuousOn.inv₀
    (f := fun v : Fin 3 → ℂ => ‖cxOf v‖) (s := {v | v ≠ 0})
    (continuous_norm.comp continuous_cxOf).continuousOn ?_) continuous_cxOf.continuousOn
  intro v hv
  exact norm_ne_zero_iff.mpr (cxOf_ne_zero hv)

theorem continuous_probeFrameRep (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) :
    Continuous (fun a : {v : Fin 3 → ℂ // v ≠ 0} => probeFrameRep k m hk hm a.1) := by
  have hcu : Continuous fun a : {v : Fin 3 → ℂ // v ≠ 0} => cxUnit a.1 :=
    continuousOn_iff_continuous_domRestrict.mp continuousOn_cxUnit
  have h0 : Continuous fun a : {v : Fin 3 → ℂ // v ≠ 0} => cxE (cxUnit a.1) :=
    cxE.continuous.comp hcu
  have h1 : Continuous fun a : {v : Fin 3 → ℂ // v ≠ 0} => cxE (Complex.I • cxUnit a.1) :=
    cxE.continuous.comp (Continuous.const_smul hcu Complex.I)
  refine continuous_pi (fun j => ?_)
  obtain ⟨p, rfl⟩ := (probeSplit k hk).surjective j
  rcases p with a' | l
  · have hfun : (fun a : {v : Fin 3 → ℂ // v ≠ 0} =>
        probeFrameRep k m hk hm a.1 (probeSplit k hk (Sum.inl a')))
        = fun a => probePairVec k m hk hm a.1 a' :=
      funext (fun a => probeFrameRep_inl k m hk hm a.1 a')
    rw [hfun]
    fin_cases a'
    · exact (probeEmb k m hk hm).continuous.comp h0
    · exact ((probeEmb k m hk hm).continuous.comp h1).neg
  · have hfun : (fun a : {v : Fin 3 → ℂ // v ≠ 0} =>
        probeFrameRep k m hk hm a.1 (probeSplit k hk (Sum.inr l)))
        = fun _ => probeTailVec k m hk l :=
      funext (fun a => probeFrameRep_inr k m hk hm a.1 l)
    rw [hfun]
    exact continuous_const

theorem continuous_probeStiefelRep (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) :
    Continuous (fun a : {v : Fin 3 → ℂ // v ≠ 0} => probeStiefelRep k m hk hm a.1 a.2) :=
  Continuous.subtype_mk (continuous_probeFrameRep k m hk hm)
    (fun a => probeFrameRep_orthonormal k m hk hm a.1 a.2)

/-! ## The probe map -/

theorem probeStiefelRep_smul_condition (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) :
    ∀ (a b : {v : Fin 3 → ℂ // v ≠ 0}) (t : ℂ), (a : Fin 3 → ℂ) = t • (b : Fin 3 → ℂ) →
      ogMk k m (probeStiefelRep k m hk hm a.1 a.2)
        = ogMk k m (probeStiefelRep k m hk hm b.1 b.2) := by
  intro a b t h
  by_cases ht : t = 0
  · rw [ht, zero_smul] at h
    exact absurd h a.2
  · have ha : a = ⟨t • (b : Fin 3 → ℂ), smul_ne_zero ht b.2⟩ := Subtype.ext h
    rw [ha]
    exact ogMk_probeStiefelRep_smul_lambda k m hk hm b.1 b.2 ht (smul_ne_zero ht b.2)

/-- **The probe map `ℂP² → G̃r_k(ℝ^{k+m})`**: the complex line of a point of `ℂP²`, read as a real
`2`-plane in `ℂ³ ⊆ ℝ^{k+m}`, together with the fixed oriented complement `(k-2)`-frame. -/
noncomputable def probeSigmaFun (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) : CP 2 → OG k m :=
  Projectivization.lift (fun v => ogMk k m (probeStiefelRep k m hk hm v.1 v.2))
    (probeStiefelRep_smul_condition k m hk hm)

theorem probeSigmaFun_mk (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m)
    (v : {v : Fin 3 → ℂ // v ≠ 0}) :
    probeSigmaFun k m hk hm (Projectivization.mk ℂ v.1 v.2)
      = ogMk k m (probeStiefelRep k m hk hm v.1 v.2) :=
  Projectivization.lift_mk _ _ v.1 v.2

theorem continuous_probeSigmaFun (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) :
    Continuous (probeSigmaFun k m hk hm) := by
  have hφ : Continuous (fun v : {v : Fin 3 → ℂ // v ≠ 0} =>
      ogMk k m (probeStiefelRep k m hk hm v.1 v.2)) :=
    (ogMk k m).continuous.comp (continuous_probeStiefelRep k m hk hm)
  have hcomp : (probeSigmaFun k m hk hm) ∘ (Projectivization.mk' ℂ :
        {v : Fin 3 → ℂ // v ≠ 0} → CP 2)
      = fun v => ogMk k m (probeStiefelRep k m hk hm v.1 v.2) := by
    funext v
    exact probeSigmaFun_mk k m hk hm v
  have hq : Topology.IsQuotientMap (Projectivization.mk' ℂ :
      {v : Fin 3 → ℂ // v ≠ 0} → CP 2) := isQuotientMap_quotient_mk'
  rw [hq.continuous_iff, hcomp]
  exact hφ

/-- The probe map as a continuous map. -/
noncomputable def probeSigma (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) : C(CP 2, OG k m) :=
  ⟨probeSigmaFun k m hk hm, continuous_probeSigmaFun k m hk hm⟩

theorem probeSigma_apply_uVec (k m : ℕ) (hk : 2 ≤ k) (hm : 4 ≤ m) (i : Fin 3) (x : CP 2)
    (hx : x ∈ Work.Projective.chartSet i) :
    probeSigma k m hk hm x = ogMk k m (probeStiefelRep k m hk hm (Work.Gen.uVec i x)
      (Work.Gen.uVec_ne_zero i x)) := by
  have h1 : x = Projectivization.mk' ℂ
      ⟨Work.Gen.uVec i x, Work.Gen.uVec_ne_zero i x⟩ :=
    (Work.Gen.cpMk_uVec i x hx).symm
  conv_lhs => rw [h1]
  exact probeSigmaFun_mk k m hk hm ⟨Work.Gen.uVec i x, Work.Gen.uVec_ne_zero i x⟩

end

end Work.ThomBordism.Grassmann
