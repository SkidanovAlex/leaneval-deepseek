import Mathlib
import Submission.Work.LerayHirsch.FibreRestrictIso
import Submission.Work.LerayHirsch.tautLine_bundleIso_of_projIso
import Submission.Work.Thom.chernClass_homeo
import Submission.Work.Thom.coreMorphism
import Submission.Work.Thom.pontryaginClass_comap

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The restriction of the tautological line bundle to a fibre

`Work.LerayHirsch.FibreRestrict` and `Work.LerayHirsch.FibreRestrictIso` compute the charts and the
transition functions of the restriction of the tautological line bundle `ℓ = ℓ(E)` of `P(E)` to a
fibre `π^{-1}(b) = ProjFibre Z b` and of the tautological line bundle `ℓ(ℂP^{m-1})` of that fibre:
both are the ratios of the fibre coordinates.  This module packages the identification as a
`Work.Thom.BundleIso`

`π_fibre^*ℓ(E) ≅ ℓ(ℂP^{m-1})`  over `ProjFibre Z b`

(`Work.LerayHirsch.nonempty_bundleIso_tautLine_fibre`), and reads off the cohomological shadow

`Work.LerayHirsch.CohMap_fibreIncl_zeta : ζ|_fibre = ζ(ℂP^{m-1})`.

The isomorphism is built with the constant-gauge ansatz of
`Submission/Work/LerayHirsch/tautLine_bundleIso_of_projIso.lean`: the fibrewise map is
multiplication by the scalar `Work.LerayHirsch.fibreCoeff` comparing the *preferred* frames (the
frame of the chart `indexAt`) of the two line bundles.  The continuity of the total-space map is
`Work.Thom.continuous_totalSpaceMap_clm`, whose chart condition is the identity
`Work.LerayHirsch.fibreCoeff_scalar_identity` — an identity between ratios of chart coordinates,
proved on representatives — communicated to `Work.LerayHirsch.continuousOn_tautCoeffCLM`, the
continuity of the transition coefficients of `ℓ`.
-/

namespace Work.LerayHirsch

open Work.TangentClasses Work.Thom

open scoped LinearAlgebra.Projectivization

noncomputable section

variable {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}

/-! ## The fibre coordinate as a plain definition -/

/-- **The fibre coordinate** of a punctured point of the realification of `Z`: its second
component, as a vector of the model fibre `ℂ^m`.  (A plain `def` rather than the
`show … from p.1.2` idiom, which cannot be re-elaborated once it is pushed into a goal by a
rewrite.) -/
def fibreVec (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) : EuclideanSpace ℂ (Fin m) :=
  p.1.2

theorem fibreVec_eq (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) :
    fibreVec Z p = (show EuclideanSpace ℂ (Fin m) from p.1.2) := rfl

theorem fibreVec_ne_zero (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) : fibreVec Z p ≠ 0 :=
  (mem_zeroComplement p.1).mp p.2

theorem fibreVec_smulPunct (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (c : ℂˣ)
    (p : ↥(zeroComplement (realification Z))) :
    fibreVec Z (smulPunct Z c p) = (c : ℂ) • fibreVec Z p :=
  smulPunct_snd Z c p

/-- The chart coordinate of the chart `indexAt b` is the fibre coordinate. -/
theorem chartCoord_indexAt_eq_fibreVec (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) {b : B} (hp : p.1.proj = b) :
    chartCoord Z (Z.indexAt b) p = fibreVec Z p := by
  rw [← realification_indexAt Z]
  exact chartCoord_indexAt_eq_snd Z b p hp

/-- The non-vanishing of a fibre coordinate is independent of the chosen lift. -/
theorem fibreVec_ne_zero_of_mkProj_eq {Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι}
    {k : Fin m} {p q : ↥(zeroComplement (realification Z))} (h : mkProj Z q = mkProj Z p)
    (hp : (fibreVec Z p) k ≠ 0) : (fibreVec Z q) k ≠ 0 :=
  fibreCoord_ne_zero_of_mkProj_eq h hp

/-! ## The punctured point of the trivial bundle attached to a punctured point of `Z` -/

/-- The punctured point of the trivial bundle `ε^m` whose fibre coordinate is the fibre coordinate
of `p`. -/
def tautPunct (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) :
    ↥(zeroComplement (realification (trivCore m))) :=
  ⟨⟨PUnit.unit, fibreVec Z p⟩, by rw [mem_zeroComplement]; exact fibreVec_ne_zero Z p⟩

/-- The chart coordinate of the tautological point attached to `p` is the fibre coordinate of
`p`. -/
theorem chartCoord_tautPunct (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (i : PUnit)
    (p : ↥(zeroComplement (realification Z))) :
    chartCoord (trivCore m) i (tautPunct Z p) = fibreVec Z p := by
  rw [fibreVec_eq]
  exact chartCoord_trivial m i (tautPunct Z p)

/-- **The identification of the two projectivisations over the fibre**: the class of the fibre
coordinate of `p`, read in `P(ε^m)`, is the class of the tautological point attached to `p`. -/
theorem projUniv_projClass_mkProj (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) :
    projUniv m (projClass Z (mkProj Z p)) = mkProj (trivCore m) (tautPunct Z p) := by
  rw [projClass_mkProj]
  exact projUniv_mkP m ⟨fibreVec Z p, fibreVec_ne_zero Z p⟩

/-- The point of the fibre of `P(E)` over `b` determined by a punctured point over `b`. -/
def fibrePt (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B)
    (p : ↥(zeroComplement (realification Z))) (hp : p.1.proj = b) : ProjFibre Z b :=
  ⟨mkProj Z p, by rw [projMap_mkProj]; exact hp⟩

@[simp] theorem fibrePt_coe (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B)
    (p : ↥(zeroComplement (realification Z))) (hp : p.1.proj = b) :
    (fibrePt Z b p hp : ProjSpace Z) = mkProj Z p := rfl

/-! ## The gauge -/

/-- **The gauge comparing the two tautological bundles on a fibre**, on a punctured point: the
ratio of the coordinates of the two *preferred* frames (the frames of the charts `indexAt`). -/
def fibreCoeffFun (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) : ℂ :=
  (fibreVec Z p) ((tautLine (trivCore m)).indexAt (projUniv m (projClass Z (mkProj Z p)))).2
    / chartCoord Z ((tautLine Z).indexAt (mkProj Z p)).1 p
        ((tautLine Z).indexAt (mkProj Z p)).2

/-- The gauge is invariant under the `ℂˣ`-action, hence descends to the projectivisation. -/
theorem fibreCoeffFun_smul (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (c : ℂˣ)
    (p : ↥(zeroComplement (realification Z))) :
    fibreCoeffFun Z (smulPunct Z c p) = fibreCoeffFun Z p := by
  have hx : mkProj Z (smulPunct Z c p) = mkProj Z p := by
    rw [mkProj_eq_iff]; exact ⟨c, rfl⟩
  simp only [fibreCoeffFun]
  rw [hx, fibreVec_smulPunct, chartCoord_smulPunct]
  rw [smul_coord, smul_coord]
  exact mul_div_mul_left _ _ (Units.ne_zero c)

/-- **The gauge**, as a function on `P(E)`. -/
def fibreCoeff (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    ProjSpace Z → ℂ :=
  Quotient.lift (fibreCoeffFun Z) (fun a b h => by
    obtain ⟨c, hc⟩ := h
    rw [← hc, fibreCoeffFun_smul])

@[simp] theorem fibreCoeff_mk (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) :
    fibreCoeff Z (mkProj Z p) = fibreCoeffFun Z p := rfl

theorem chartCoord_indexAt_tautLine_ne_zero (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) :
    chartCoord Z ((tautLine Z).indexAt (mkProj Z p)).1 p
      ((tautLine Z).indexAt (mkProj Z p)).2 ≠ 0 := by
  have h := (tautLine Z).mem_baseSet_at (mkProj Z p)
  rw [tautLine_baseSet] at h
  exact ((mem_tautBaseSet Z _ _ p).mp ((mem_tautBaseSetProj_mk Z _ p).mp h)).2

theorem fibreVec_indexAt_ne_zero (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (p : ↥(zeroComplement (realification Z))) :
    (fibreVec Z p)
      ((tautLine (trivCore m)).indexAt (projUniv m (projClass Z (mkProj Z p)))).2 ≠ 0 := by
  set idxY := (tautLine (trivCore m)).indexAt (projUniv m (projClass Z (mkProj Z p))) with hidxY
  have h := (tautLine (trivCore m)).mem_baseSet_at (projUniv m (projClass Z (mkProj Z p)))
  rw [tautLine_baseSet] at h
  rw [projUniv_projClass_mkProj] at h
  have h2 := ((mem_tautBaseSet (trivCore m) idxY.1 idxY.2 (tautPunct Z p)).mp
    ((mem_tautBaseSetProj_mk (trivCore m) idxY (tautPunct Z p)).mp h)).2
  rw [chartCoord_tautPunct] at h2
  exact h2

/-- **The gauge does not vanish.** -/
theorem fibreCoeff_ne_zero (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (x : ProjSpace Z) : fibreCoeff Z x ≠ 0 := by
  obtain ⟨p, rfl⟩ := surjective_mkProj Z x
  rw [fibreCoeff_mk]
  simp only [fibreCoeffFun]
  exact div_ne_zero (fibreVec_indexAt_ne_zero Z p) (chartCoord_indexAt_tautLine_ne_zero Z p)

/-! ## General lemmas on the transition coefficients -/

theorem tautCoeffLift_ne_zero (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    {ik jl : ι × Fin m} {x : ProjSpace Z}
    (h : x ∈ tautBaseSetProj Z ik ∩ tautBaseSetProj Z jl) : tautCoeffLift Z ik jl x ≠ 0 := by
  obtain ⟨p, rfl⟩ := surjective_mkProj Z x
  have hik : p ∈ tautBaseSet Z ik.1 ik.2 := (mem_tautBaseSetProj_mk Z ik p).mp h.1
  have hjl : p ∈ tautBaseSet Z jl.1 jl.2 := (mem_tautBaseSetProj_mk Z jl p).mp h.2
  rw [mem_tautBaseSet] at hik hjl
  rw [tautCoeffLift_mk, tautCoeff, dif_pos hik.2]
  exact div_ne_zero hjl.2 hik.2

/-- **Continuity of the transition coefficients of `ℓ`**, in scalar form. -/
theorem continuousOn_tautCoeffLift (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (ik jl : ι × Fin m) :
    ContinuousOn (fun x : ProjSpace Z => tautCoeffLift Z ik jl x)
      (tautBaseSetProj Z ik ∩ tautBaseSetProj Z jl) := by
  have hq : Topology.IsQuotientMap (mkProj Z) := isQuotientMap_quotient_mk'
  refine (Topology.IsQuotientMap.continuousOn_isOpen_iff hq
    ((isOpen_tautBaseSetProj Z ik).inter (isOpen_tautBaseSetProj Z jl))).mpr ?_
  have hpre : mkProj Z ⁻¹' (tautBaseSetProj Z ik ∩ tautBaseSetProj Z jl)
      = tautBaseSet Z ik.1 ik.2 ∩ tautBaseSet Z jl.1 jl.2 := by
    rw [Set.preimage_inter, preimage_tautBaseSetProj, preimage_tautBaseSetProj]
  rw [hpre]
  have h1 : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
      chartCoord Z ik.1 p ik.2) (tautBaseSet Z ik.1 ik.2 ∩ tautBaseSet Z jl.1 jl.2) :=
    ((by fun_prop : Continuous (fun v : EuclideanSpace ℂ (Fin m) => v ik.2)).comp_continuousOn
      ((continuousOn_chartCoord Z ik.1).mono (fun p hp => hp.1.1)))
  have h2 : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
      chartCoord Z jl.1 p jl.2) (tautBaseSet Z ik.1 ik.2 ∩ tautBaseSet Z jl.1 jl.2) :=
    ((by fun_prop : Continuous (fun v : EuclideanSpace ℂ (Fin m) => v jl.2)).comp_continuousOn
      ((continuousOn_chartCoord Z jl.1).mono (fun p hp => hp.2.1)))
  have hS : ContinuousOn (fun p : ↥(zeroComplement (realification Z)) =>
      chartCoord Z jl.1 p jl.2 / chartCoord Z ik.1 p ik.2)
      (tautBaseSet Z ik.1 ik.2 ∩ tautBaseSet Z jl.1 jl.2) :=
    h2.div h1 (fun p hp => hp.1.2)
  refine hS.congr (fun p hp => ?_)
  simp only [Function.comp_apply]
  rw [tautCoeffLift_mk, tautCoeff_eq Z ik jl p hp.1.2]

/-- The transition coefficient in the reverse direction is the inverse. -/
theorem tautCoeffLift_symm (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    {ik jl : ι × Fin m} {x : ProjSpace Z}
    (h : x ∈ tautBaseSetProj Z ik ∩ tautBaseSetProj Z jl) :
    tautCoeffLift Z jl ik x = (tautCoeffLift Z ik jl x)⁻¹ := by
  obtain ⟨p, rfl⟩ := surjective_mkProj Z x
  have hik : p ∈ tautBaseSet Z ik.1 ik.2 := (mem_tautBaseSetProj_mk Z ik p).mp h.1
  have hjl : p ∈ tautBaseSet Z jl.1 jl.2 := (mem_tautBaseSetProj_mk Z jl p).mp h.2
  rw [mem_tautBaseSet] at hik hjl
  rw [tautLine_coordChange_eq_ratio Z ik jl p hik.2,
    tautLine_coordChange_eq_ratio Z jl ik p hjl.2]
  rw [inv_div]

/-! ## The charts of the pullback of the tautological bundle of `ℂP^{m-1}` -/

/-- **The chart `(unit,k)` of the pullback of `ℓ(ℂP^{m-1})` along the class of the fibre
coordinate** consists of the fibre points having a lift whose `k`-th fibre coordinate does not
vanish. -/
theorem mem_bundleComap_tautLineP_baseSet (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (b : B) (k : Fin m) (x : ProjFibre Z b) :
    x ∈ (bundleComap (tautLineP m) (projClassFibre Z b)).baseSet (PUnit.unit, k) ↔
      ∃ p : ↥(zeroComplement (realification Z)), mkProj Z p = x.1 ∧ (fibreVec Z p) k ≠ 0 := by
  rw [bundleComap_baseSet, Set.mem_preimage]
  constructor
  · intro hx
    obtain ⟨v, hv, hvk⟩ := (mem_tautLineP_baseSet m k (projClassFibre Z b x)).mp hx
    obtain ⟨p, hp⟩ := surjective_mkProj Z x.1
    refine ⟨p, hp, ?_⟩
    have h1 : projClass Z x.1 = mkP m ⟨fibreVec Z p, fibreVec_ne_zero Z p⟩ := by
      rw [← hp]
      exact projClass_mkProj Z p
    obtain ⟨c, hc⟩ := (mkP_eq_iff (m := m)).mp (hv.trans h1)
    have hc0 : c ≠ 0 := by
      rintro rfl
      exact v.2 (by rw [zero_smul] at hc; exact hc.symm)
    intro h0
    have hvec : v.1 k = c * (fibreVec Z p) k := by rw [← hc]; rfl
    exact hvk (by rw [hvec, h0, mul_zero])
  · rintro ⟨p, hp, hk⟩
    have h1 : projClassFibre Z b x = mkP m ⟨fibreVec Z p, fibreVec_ne_zero Z p⟩ :=
      (projClassFibre_apply Z b x).trans (by
        rw [← hp]
        exact projClass_mkProj Z p)
    rw [h1]
    exact (mem_tautLineP_baseSet m k (mkP m ⟨fibreVec Z p, fibreVec_ne_zero Z p⟩)).mpr
      ⟨⟨fibreVec Z p, fibreVec_ne_zero Z p⟩, rfl, hk⟩

/-- **The containment of the charts**: a point of the fibre which lies in the chart `(unit,k)` of
`ℓ(ℂP^{m-1})` lies in the chart `(indexAt b, k)` of `ℓ(E)`. -/
theorem mem_tautBaseSetProj_indexAt_of_mem_tautLineP_baseSet
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) (k : Fin m)
    (x : ProjFibre Z b)
    (hx : x ∈ (bundleComap (tautLineP m) (projClassFibre Z b)).baseSet (PUnit.unit, k)) :
    x.1 ∈ tautBaseSetProj Z (Z.indexAt b, k) := by
  obtain ⟨p, hp, hk⟩ := (mem_bundleComap_tautLineP_baseSet Z b k x).mp hx
  have hpb : p.1.proj = b := by rw [← projMap_mkProj Z p, hp]; exact x.2
  have h2 : mkProj Z p ∈ tautBaseSetProj Z (Z.indexAt b, k) := by
    rw [mem_tautBaseSetProj_mk]
    exact ⟨by rw [hpb]; exact Z.mem_baseSet_at b,
      by rw [chartCoord_indexAt_eq_fibreVec Z p hpb]; exact hk⟩
  rwa [hp] at h2

/-! ## The scalar identities -/

/-- **The scalar identity of the forward direction**, at the preferred frames. -/
theorem fibreCoeff_scalar_identity (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (b : B) (i₁ : ι × Fin m) (i₂ : PUnit × Fin m)
    (p : ↥(zeroComplement (realification Z))) (hp : p.1.proj = b)
    (hB : chartCoord Z i₁.1 p i₁.2 ≠ 0) :
    tautCoeffLift (trivCore m)
        ((tautLine (trivCore m)).indexAt (mkProj (trivCore m) (tautPunct Z p))) i₂
        (mkProj (trivCore m) (tautPunct Z p))
      * fibreCoeffFun Z p
      * tautCoeffLift Z i₁ ((tautLine Z).indexAt (mkProj Z p)) (mkProj Z p)
      = tautCoeffLift Z i₁ (Z.indexAt b, i₂.2) (mkProj Z p) := by
  set iY := (tautLine (trivCore m)).indexAt (mkProj (trivCore m) (tautPunct Z p)) with hiY
  have hA : chartCoord Z ((tautLine Z).indexAt (mkProj Z p)).1 p
      ((tautLine Z).indexAt (mkProj Z p)).2 ≠ 0 := chartCoord_indexAt_tautLine_ne_zero Z p
  have hCyChart : (chartCoord (trivCore m) iY.1 (tautPunct Z p)) iY.2 ≠ 0 := by
    have h := (tautLine (trivCore m)).mem_baseSet_at (mkProj (trivCore m) (tautPunct Z p))
    rw [tautLine_baseSet] at h
    exact ((mem_tautBaseSet (trivCore m) iY.1 iY.2 (tautPunct Z p)).mp
      ((mem_tautBaseSetProj_mk (trivCore m) iY (tautPunct Z p)).mp h)).2
  have hCy : (fibreVec Z p) iY.2 ≠ 0 := by
    have e : (chartCoord (trivCore m) iY.1 (tautPunct Z p)) iY.2 = (fibreVec Z p) iY.2 := by
      rw [chartCoord_tautPunct]
    rwa [e] at hCyChart
  have h1 : tautCoeffLift (trivCore m) iY i₂ (mkProj (trivCore m) (tautPunct Z p))
      = (fibreVec Z p) i₂.2 / (fibreVec Z p) iY.2 := by
    rw [tautLine_coordChange_eq_ratio (trivCore m) iY i₂ (tautPunct Z p) hCyChart]
    have e1 : (chartCoord (trivCore m) i₂.1 (tautPunct Z p)) i₂.2 = (fibreVec Z p) i₂.2 := by
      rw [chartCoord_tautPunct]
    have e2 : (chartCoord (trivCore m) iY.1 (tautPunct Z p)) iY.2 = (fibreVec Z p) iY.2 := by
      rw [chartCoord_tautPunct]
    rw [e1, e2]
  have h2 : fibreCoeffFun Z p
      = (fibreVec Z p) iY.2 / chartCoord Z ((tautLine Z).indexAt (mkProj Z p)).1 p
          ((tautLine Z).indexAt (mkProj Z p)).2 := by
    simp only [fibreCoeffFun]
    rw [projUniv_projClass_mkProj]
  have h3 : tautCoeffLift Z i₁ ((tautLine Z).indexAt (mkProj Z p)) (mkProj Z p)
      = chartCoord Z ((tautLine Z).indexAt (mkProj Z p)).1 p
          ((tautLine Z).indexAt (mkProj Z p)).2 / chartCoord Z i₁.1 p i₁.2 :=
    tautLine_coordChange_eq_ratio Z i₁ ((tautLine Z).indexAt (mkProj Z p)) p hB
  have h4 : tautCoeffLift Z i₁ (Z.indexAt b, i₂.2) (mkProj Z p)
      = (fibreVec Z p) i₂.2 / chartCoord Z i₁.1 p i₁.2 := by
    rw [tautLine_coordChange_eq_ratio Z i₁ (Z.indexAt b, i₂.2) p hB]
    have e : (chartCoord Z (Z.indexAt b) p) i₂.2 = (fibreVec Z p) i₂.2 := by
      rw [chartCoord_indexAt_eq_fibreVec Z p hp]
    rw [e]
  rw [h1, h2, h3, h4]
  field_simp

/-- **The scalar identity of the inverse direction**, at the preferred frames. -/
theorem fibreCoeff_scalar_identity_inv (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (b : B) (i₁ : ι × Fin m) (i₂ : PUnit × Fin m)
    (p : ↥(zeroComplement (realification Z))) (hp : p.1.proj = b)
    (hB : chartCoord Z i₁.1 p i₁.2 ≠ 0) (hD : (fibreVec Z p) i₂.2 ≠ 0) :
    tautCoeffLift Z ((tautLine Z).indexAt (mkProj Z p)) i₁ (mkProj Z p)
      * (fibreCoeffFun Z p)⁻¹
      * tautCoeffLift (trivCore m) i₂
          ((tautLine (trivCore m)).indexAt (mkProj (trivCore m) (tautPunct Z p)))
          (mkProj (trivCore m) (tautPunct Z p))
      = (tautCoeffLift Z i₁ (Z.indexAt b, i₂.2) (mkProj Z p))⁻¹ := by
  set iY := (tautLine (trivCore m)).indexAt (mkProj (trivCore m) (tautPunct Z p)) with hiY
  have hA : chartCoord Z ((tautLine Z).indexAt (mkProj Z p)).1 p
      ((tautLine Z).indexAt (mkProj Z p)).2 ≠ 0 := chartCoord_indexAt_tautLine_ne_zero Z p
  have hCyChart : (chartCoord (trivCore m) iY.1 (tautPunct Z p)) iY.2 ≠ 0 := by
    have h := (tautLine (trivCore m)).mem_baseSet_at (mkProj (trivCore m) (tautPunct Z p))
    rw [tautLine_baseSet] at h
    exact ((mem_tautBaseSet (trivCore m) iY.1 iY.2 (tautPunct Z p)).mp
      ((mem_tautBaseSetProj_mk (trivCore m) iY (tautPunct Z p)).mp h)).2
  have hCy : (fibreVec Z p) iY.2 ≠ 0 := by
    have e : (chartCoord (trivCore m) iY.1 (tautPunct Z p)) iY.2 = (fibreVec Z p) iY.2 := by
      rw [chartCoord_tautPunct]
    rwa [e] at hCyChart
  have hDyChart : (chartCoord (trivCore m) i₂.1 (tautPunct Z p)) i₂.2 ≠ 0 := by
    have e : (chartCoord (trivCore m) i₂.1 (tautPunct Z p)) i₂.2 = (fibreVec Z p) i₂.2 := by
      rw [chartCoord_tautPunct]
    rwa [e]
  have e1 : (chartCoord (trivCore m) i₂.1 (tautPunct Z p)) i₂.2 = (fibreVec Z p) i₂.2 := by
    rw [chartCoord_tautPunct]
  have e2 : (chartCoord (trivCore m) iY.1 (tautPunct Z p)) iY.2 = (fibreVec Z p) iY.2 := by
    rw [chartCoord_tautPunct]
  have h1 : tautCoeffLift (trivCore m) i₂ iY (mkProj (trivCore m) (tautPunct Z p))
      = (fibreVec Z p) iY.2 / (fibreVec Z p) i₂.2 := by
    rw [tautLine_coordChange_eq_ratio (trivCore m) i₂ iY (tautPunct Z p) hDyChart, e1, e2]
  have h2 : fibreCoeffFun Z p
      = (fibreVec Z p) iY.2 / chartCoord Z ((tautLine Z).indexAt (mkProj Z p)).1 p
          ((tautLine Z).indexAt (mkProj Z p)).2 := by
    simp only [fibreCoeffFun]
    rw [projUniv_projClass_mkProj]
  have h3 : tautCoeffLift Z ((tautLine Z).indexAt (mkProj Z p)) i₁ (mkProj Z p)
      = chartCoord Z i₁.1 p i₁.2 / chartCoord Z ((tautLine Z).indexAt (mkProj Z p)).1 p
          ((tautLine Z).indexAt (mkProj Z p)).2 :=
    tautLine_coordChange_eq_ratio Z ((tautLine Z).indexAt (mkProj Z p)) i₁ p hA
  have h4 : tautCoeffLift Z i₁ (Z.indexAt b, i₂.2) (mkProj Z p)
      = (fibreVec Z p) i₂.2 / chartCoord Z i₁.1 p i₁.2 := by
    rw [tautLine_coordChange_eq_ratio Z i₁ (Z.indexAt b, i₂.2) p hB]
    have e : (chartCoord Z (Z.indexAt b) p) i₂.2 = (fibreVec Z p) i₂.2 := by
      rw [chartCoord_indexAt_eq_fibreVec Z p hp]
    rw [e]
  rw [h1, h2, h3, h4, inv_div, inv_div]
  field_simp

/-! ## The identities of continuous linear maps -/

/-- **The chart identity of the forward direction**: the composite of the two chart expressions is
the transition coefficient of the chart `(indexAt b, k)` of `ℓ(E)`. -/
theorem fibreCoeff_clm_identity (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (b : B) (i₁ : ι × Fin m) (i₂ : PUnit × Fin m) (x : ProjFibre Z b)
    (h₁ : x ∈ (bundleComap (tautLine Z) (fibreIncl Z b)).baseSet i₁)
    (h₂ : x ∈ (bundleComap (tautLineP m) (projClassFibre Z b)).baseSet i₂) :
    ((bundleComap (tautLineP m) (projClassFibre Z b)).coordChange
        ((bundleComap (tautLineP m) (projClassFibre Z b)).indexAt x) i₂ x).comp
      ((fibreCoeff Z x.1 • (ContinuousLinearMap.id ℂ LineFibre)).comp
        ((bundleComap (tautLine Z) (fibreIncl Z b)).coordChange i₁
          ((bundleComap (tautLine Z) (fibreIncl Z b)).indexAt x) x))
    = tautCoeffCLM Z i₁ (Z.indexAt b, i₂.2) x.1 := by
  obtain ⟨p, hp⟩ := surjective_mkProj Z x.1
  have hpb : p.1.proj = b := by rw [← projMap_mkProj Z p, hp]; exact x.2
  have hx : x = fibrePt Z b p hpb := Subtype.ext hp.symm
  subst hx
  have hB : chartCoord Z i₁.1 p i₁.2 ≠ 0 := by
    have h1 : (fibrePt Z b p hpb).1 ∈ tautBaseSetProj Z i₁ := by
      simpa only [bundleComap_baseSet, Set.mem_preimage, fibreIncl_apply, tautLine_baseSet]
        using h₁
    exact ((mem_tautBaseSet Z _ _ p).mp ((mem_tautBaseSetProj_mk Z _ p).mp h1)).2
  refine ContinuousLinearMap.ext (fun v => ?_)
  simp only [fibrePt_coe, fibreCoeff_mk, bundleComap_coordChange, bundleComap_indexAt,
    fibreIncl_apply, projClassFibre_apply, tautLineP, projUniv_projClass_mkProj,
    tautLine_coordChange, tautCoeffCLM_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  rw [smul_smul, smul_smul, fibreCoeff_scalar_identity Z b i₁ i₂ p hpb hB]

/-- **The chart identity of the inverse direction**. -/
theorem fibreCoeff_clm_identity_inv (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι)
    (b : B) (i₁ : ι × Fin m) (i₂ : PUnit × Fin m) (x : ProjFibre Z b)
    (h₁ : x ∈ (bundleComap (tautLine Z) (fibreIncl Z b)).baseSet i₁)
    (h₂ : x ∈ (bundleComap (tautLineP m) (projClassFibre Z b)).baseSet i₂) :
    ((bundleComap (tautLine Z) (fibreIncl Z b)).coordChange
        ((bundleComap (tautLine Z) (fibreIncl Z b)).indexAt x) i₁ x).comp
      (((fibreCoeff Z x.1)⁻¹ • (ContinuousLinearMap.id ℂ LineFibre)).comp
        ((bundleComap (tautLineP m) (projClassFibre Z b)).coordChange i₂
          ((bundleComap (tautLineP m) (projClassFibre Z b)).indexAt x) x))
    = (tautCoeffLift Z i₁ (Z.indexAt b, i₂.2) x.1)⁻¹ •
        (ContinuousLinearMap.id ℂ LineFibre) := by
  obtain ⟨p, hp⟩ := surjective_mkProj Z x.1
  have hpb : p.1.proj = b := by rw [← projMap_mkProj Z p, hp]; exact x.2
  have hx : x = fibrePt Z b p hpb := Subtype.ext hp.symm
  subst hx
  have hB : chartCoord Z i₁.1 p i₁.2 ≠ 0 := by
    have h1 : (fibrePt Z b p hpb).1 ∈ tautBaseSetProj Z i₁ := by
      simpa only [bundleComap_baseSet, Set.mem_preimage, fibreIncl_apply, tautLine_baseSet]
        using h₁
    exact ((mem_tautBaseSet Z _ _ p).mp ((mem_tautBaseSetProj_mk Z _ p).mp h1)).2
  have hD : (fibreVec Z p) i₂.2 ≠ 0 := by
    obtain ⟨p', hp', hk'⟩ :=
      (mem_bundleComap_tautLineP_baseSet Z b i₂.2 (fibrePt Z b p hpb)).mp h₂
    rw [fibrePt_coe] at hp'
    exact fibreVec_ne_zero_of_mkProj_eq hp'.symm hk'
  refine ContinuousLinearMap.ext (fun v => ?_)
  simp only [fibrePt_coe, fibreCoeff_mk, bundleComap_coordChange, bundleComap_indexAt,
    fibreIncl_apply, projClassFibre_apply, tautLineP, projUniv_projClass_mkProj,
    tautLine_coordChange, tautCoeffCLM_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply]
  rw [smul_smul, smul_smul, fibreCoeff_scalar_identity_inv Z b i₁ i₂ p hpb hB hD]

/-! ## The isomorphism -/

/-- **The restriction of the tautological line bundle to a fibre is the tautological line bundle of
the fibre.** -/
noncomputable def fibreLineIso (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    BundleIso (bundleComap (tautLine Z) (fibreIncl Z b))
      (bundleComap (tautLineP m) (projClassFibre Z b)) where
  hom := fun x => fibreCoeff Z x • (LinearMap.id : LineFibre →ₗ[ℂ] LineFibre)
  inv := fun x => (fibreCoeff Z x)⁻¹ • (LinearMap.id : LineFibre →ₗ[ℂ] LineFibre)
  left_inv := fun x v => by
    change (fibreCoeff Z x)⁻¹ • (fibreCoeff Z x • v) = v
    rw [smul_smul, inv_mul_cancel₀ (fibreCoeff_ne_zero Z x), one_smul]
  right_inv := fun x v => by
    change fibreCoeff Z x • ((fibreCoeff Z x)⁻¹ • v) = v
    rw [smul_smul, mul_inv_cancel₀ (fibreCoeff_ne_zero Z x), one_smul]
  continuous_hom := by
    refine (continuous_totalSpaceMap_clm _ _ (ContinuousMap.id (ProjFibre Z b))
      (fun x => fibreCoeff Z x • (ContinuousLinearMap.id ℂ LineFibre)) ?_).congr
      (fun p => rfl)
    intro i₁ i₂
    have hreg : (bundleComap (tautLine Z) (fibreIncl Z b)).baseSet i₁ ∩
        (ContinuousMap.id (ProjFibre Z b)) ⁻¹'
          (bundleComap (tautLineP m) (projClassFibre Z b)).baseSet i₂
        = (bundleComap (tautLine Z) (fibreIncl Z b)).baseSet i₁ ∩
          (bundleComap (tautLineP m) (projClassFibre Z b)).baseSet i₂ := by
      rw [ContinuousMap.coe_id, Set.preimage_id]
    rw [hreg]
    refine ContinuousOn.congr (f := fun y : ProjFibre Z b =>
      tautCoeffCLM Z i₁ (Z.indexAt b, i₂.2) y.1) ?_ ?_
    · refine (continuousOn_tautCoeffCLM Z i₁ (Z.indexAt b, i₂.2)).comp
        continuous_subtype_val.continuousOn ?_
      intro y hy
      exact ⟨by simpa only [bundleComap_baseSet, Set.mem_preimage, fibreIncl_apply,
          tautLine_baseSet] using hy.1,
        mem_tautBaseSetProj_indexAt_of_mem_tautLineP_baseSet Z b i₂.2 y hy.2⟩
    · intro y hy
      exact fibreCoeff_clm_identity Z b i₁ i₂ y hy.1 hy.2
  continuous_inv := by
    refine (continuous_totalSpaceMap_clm _ _ (ContinuousMap.id (ProjFibre Z b))
      (fun x => (fibreCoeff Z x)⁻¹ • (ContinuousLinearMap.id ℂ LineFibre)) ?_).congr
      (fun p => rfl)
    intro i₂ i₁
    have hreg : (bundleComap (tautLineP m) (projClassFibre Z b)).baseSet i₂ ∩
        (ContinuousMap.id (ProjFibre Z b)) ⁻¹'
          (bundleComap (tautLine Z) (fibreIncl Z b)).baseSet i₁
        = (bundleComap (tautLineP m) (projClassFibre Z b)).baseSet i₂ ∩
          (bundleComap (tautLine Z) (fibreIncl Z b)).baseSet i₁ := by
      rw [ContinuousMap.coe_id, Set.preimage_id]
    rw [hreg]
    refine ContinuousOn.congr (f := fun y : ProjFibre Z b =>
      (tautCoeffLift Z i₁ (Z.indexAt b, i₂.2) y.1)⁻¹ •
        (ContinuousLinearMap.id ℂ LineFibre)) ?_ ?_
    · have hcont : ContinuousOn (fun y : ProjFibre Z b =>
          tautCoeffLift Z i₁ (Z.indexAt b, i₂.2) y.1)
          ((bundleComap (tautLineP m) (projClassFibre Z b)).baseSet i₂ ∩
            (bundleComap (tautLine Z) (fibreIncl Z b)).baseSet i₁) :=
        (continuousOn_tautCoeffLift Z i₁ (Z.indexAt b, i₂.2)).comp
          continuous_subtype_val.continuousOn (fun y hy =>
            ⟨by simpa only [bundleComap_baseSet, Set.mem_preimage, fibreIncl_apply,
                tautLine_baseSet] using hy.2,
              mem_tautBaseSetProj_indexAt_of_mem_tautLineP_baseSet Z b i₂.2 y hy.1⟩)
      have hne : ∀ y ∈ ((bundleComap (tautLineP m) (projClassFibre Z b)).baseSet i₂ ∩
            (bundleComap (tautLine Z) (fibreIncl Z b)).baseSet i₁),
          tautCoeffLift Z i₁ (Z.indexAt b, i₂.2) y.1 ≠ 0 := fun y hy =>
        tautCoeffLift_ne_zero Z
          ⟨by simpa only [bundleComap_baseSet, Set.mem_preimage, fibreIncl_apply,
              tautLine_baseSet] using hy.2,
            mem_tautBaseSetProj_indexAt_of_mem_tautLineP_baseSet Z b i₂.2 y hy.1⟩
      exact (hcont.inv₀ hne).smul (continuousOn_const :
        ContinuousOn (fun _ : ProjFibre Z b =>
          (ContinuousLinearMap.id ℂ LineFibre : LineFibre →L[ℂ] LineFibre))
          ((bundleComap (tautLineP m) (projClassFibre Z b)).baseSet i₂ ∩
            (bundleComap (tautLine Z) (fibreIncl Z b)).baseSet i₁))
    · intro y hy
      exact fibreCoeff_clm_identity_inv Z b i₁ i₂ y hy.2 hy.1

/-- **The restriction of the tautological line bundle to a fibre is the tautological line bundle of
the fibre** (existence form). -/
theorem nonempty_bundleIso_tautLine_fibre
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) (b : B) :
    Nonempty (BundleIso (bundleComap (tautLine Z) (fibreIncl Z b))
      (bundleComap (tautLineP m) (projClassFibre Z b))) :=
  ⟨fibreLineIso Z b⟩

end

end Work.LerayHirsch
