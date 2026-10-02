import Mathlib
import Submission.Work.Gen.CruxDefs
import Submission.Work.LerayHirsch.SplitsOverProj
import Submission.Work.Gen.EulerToolkit

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-!
# The canonical splitting of the tautological sequence

For a complex gluing-data bundle `Z` of rank `n + 1` over a paracompact Hausdorff base `B`, the
pullback `π^*Z` of `Z` to its projectivisation `P(E) = Work.LerayHirsch.ProjSpace Z` splits as

`π^*Z ≅ ℓ ⊕ Q`,

where `ℓ = Work.LerayHirsch.tautLine Z` is the tautological line bundle and
`Q = Work.LerayHirsch.quotientBundle Z = π^*Z/ℓ` is the *canonical* quotient
(`Work.Gen.splitsCanonical`).

The splitting principle `Work.LerayHirsch.splitsOverProj_of_paracompact` proves the splitting with
an *abstract* complement: `π^*Z ≅ ℓ ⊕ Q₀` where `Q₀ = ℓ ⊗ W` and `W = σ^*(π^*E/ℂ·s)` is the
complement produced by Whitney's lemma, re-presented over the cover `ι × Fin (n+1)` of `ℓ` by
reindexing it along `τ a = (a, ((a, a.1), a.2))`.

The point of this module is that the *canonical* quotient `quotientBundle Z` works as well.  The
reindexed gluing data of `Q₀` is *identical* to that of `quotientBundle Z`:

* the base sets agree (`baseSet_twist_tau`), because the tautological section has `k`-th coordinate
  `1` on the chart `(i,k)` (`Work.LerayHirsch.localTriv_tautSectionVec`);
* the transition functions agree (`coordChange_twist_tau`): the two reciprocal line-bundle factors
  of `ℓ ⊗ ℓ^*` cancel (the coefficients `tautCoeffLift Z a a'` and `tautCoeffLift Z a' a` are
  mutually inverse), and the quotient projection of the twist reduces, via
  `Work.LerayHirsch.tautQuotient_coordChange_eq` and the scaling invariance of `quoFun`, to the
  quotient projection of `Z` along its chart coordinate.

Consequently `Work.Thom.nonempty_bundleIso_of_gauge` gives `Q₀ ≅ quotientBundle Z`, and the chain of
bundle isomorphisms of `SplitsOverProj.lean` can be re-run verbatim with `quotientBundle Z` in place
of `Q₀`.
-/

namespace Work.Gen

open Work.TangentClasses Work.Thom

noncomputable section

variable {n : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]

theorem quoFun_smul_smul {m : ℕ} (k : Fin (m + 1)) (w u : EuclideanSpace ℂ (Fin (m + 1)))
    (c d : ℂ) (hc : c ≠ 0) :
    Work.Thom.quoFun k (c • w) (d • u) = d • Work.Thom.quoFun k w u := by
  ext i
  simp only [Work.Thom.quoFun_apply, WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul]
  field_simp

theorem quoFun_smul_left {m : ℕ} (k : Fin (m + 1)) (w u : EuclideanSpace ℂ (Fin (m + 1)))
    (c : ℂ) (hc : c ≠ 0) :
    Work.Thom.quoFun k (c • w) u = Work.Thom.quoFun k w u := by
  have h := quoFun_smul_smul k w u c 1 hc
  simpa using h

abbrev auxBundle (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (n + 1))) ι)
    (σ : C(Work.LerayHirsch.ProjSpace Z,
      ↥(zeroComplement (realification (Work.LerayHirsch.tautTwist Z))))) :
    VectorBundleCore ℂ (Work.LerayHirsch.ProjSpace Z) (EuclideanSpace ℂ (Fin n))
      (((ι × Fin (n + 1)) × ι) × Fin (n + 1)) :=
  bundleComap (tautQuotient (Work.LerayHirsch.tautTwist Z)) σ

def tauMap : (ι × Fin (n + 1)) →
    (ι × Fin (n + 1)) × (((ι × Fin (n + 1)) × ι) × Fin (n + 1)) :=
  fun a => (a, ((a, a.1), a.2))

@[simp] theorem tauMap_fst (a : ι × Fin (n + 1)) : (tauMap (n := n) a).1 = a := rfl

@[simp] theorem tauMap_snd (a : ι × Fin (n + 1)) :
    (tauMap (n := n) a).2 = ((a, a.1), a.2) := rfl

theorem scl_tautLine_coordChange (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (n + 1))) ι)
    (a a' : ι × Fin (n + 1)) (x : Work.LerayHirsch.ProjSpace Z) :
    scl ((Work.LerayHirsch.tautLine Z).coordChange a a' x)
      = Work.LerayHirsch.tautCoeffLift Z a a' x := by
  rw [Work.LerayHirsch.tautLine_coordChange]
  exact Work.Gen.scl_smul_id_eq (Work.LerayHirsch.tautCoeffLift Z a a' x)

theorem tautCoeffLift_mul_recip (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (n + 1))) ι)
    {a a' : ι × Fin (n + 1)} {x : Work.LerayHirsch.ProjSpace Z}
    (hx : x ∈ Work.LerayHirsch.tautBaseSetProj Z a)
    (hx' : x ∈ Work.LerayHirsch.tautBaseSetProj Z a') :
    Work.LerayHirsch.tautCoeffLift Z a' a x * Work.LerayHirsch.tautCoeffLift Z a a' x = 1 := by
  have h := Work.LerayHirsch.tautCoeffLift_comp Z a a' a (x := x) ⟨⟨hx, hx'⟩, hx⟩
  rw [Work.LerayHirsch.tautCoeffLift_self Z a hx] at h
  exact h

section Key

variable (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (n + 1))) ι)
variable (σ : C(Work.LerayHirsch.ProjSpace Z,
    ↥(zeroComplement (realification (Work.LerayHirsch.tautTwist Z)))))
variable (hσ : ∀ x, ((σ x : ↥(zeroComplement (realification (Work.LerayHirsch.tautTwist Z)))) :
  (realification (Work.LerayHirsch.tautTwist Z)).TotalSpace).1 = x)
variable (hσv : ∀ x, ((σ x : ↥(zeroComplement (realification (Work.LerayHirsch.tautTwist Z)))) :
  (realification (Work.LerayHirsch.tautTwist Z)).TotalSpace).2
    = Work.LerayHirsch.tautSectionVec Z x)

include Z σ hσ hσv

theorem baseSet_twist_tau (a : ι × Fin (n + 1)) :
    (Work.LerayHirsch.twistCore (Work.LerayHirsch.tautLine Z) (auxBundle Z σ)).baseSet
        (tauMap (n := n) a)
      = (Work.LerayHirsch.quotientBundle Z).baseSet a := by
  rw [Work.LerayHirsch.twistCore_baseSet, Work.LerayHirsch.tautLine_baseSet, tauMap_snd,
    Work.LerayHirsch.quotientBundle_baseSet]
  ext x
  constructor
  · rintro ⟨hx, -⟩
    exact hx
  · intro hx
    exact ⟨hx, Work.LerayHirsch.mem_baseSet_bundleComap_tautQuotient Z σ hσ hσv a.1 a.2 hx⟩

theorem localTriv_auxBundle (a : ι × Fin (n + 1)) {x : Work.LerayHirsch.ProjSpace Z}
    (hx : x ∈ Work.LerayHirsch.tautBaseSetProj Z a) :
    ((Work.LerayHirsch.tautTwist Z).localTriv (a, a.1)
        ((σ x : ↥(zeroComplement (realification (Work.LerayHirsch.tautTwist Z)))) :
          (realification (Work.LerayHirsch.tautTwist Z)).TotalSpace)).2
      = Work.LerayHirsch.TautEmbed.chartRatioVec Z a.1 a.2 a.1 x := by
  have hx2 : Work.LerayHirsch.projMap Z x ∈ Z.baseSet a.1 :=
    Work.LerayHirsch.tautBaseSetProj_subset_projMap Z a.1 a.2 hx
  rw [VectorBundleCore.localTriv_apply, hσ x, hσv x]
  exact Work.LerayHirsch.tautTwist_coordChange_tautSectionVec Z (a, a.1) x hx hx2

theorem coordChange_twist_tau_apply (a a' : ι × Fin (n + 1)) (x : Work.LerayHirsch.ProjSpace Z)
    (hx : x ∈ Work.LerayHirsch.tautBaseSetProj Z a)
    (hx' : x ∈ Work.LerayHirsch.tautBaseSetProj Z a')
    (w : EuclideanSpace ℂ (Fin n)) :
    (Work.LerayHirsch.twistCore (Work.LerayHirsch.tautLine Z) (auxBundle Z σ)).coordChange
        (tauMap (n := n) a) (tauMap (n := n) a') x w
      = (Work.LerayHirsch.quotientBundle Z).coordChange a a' x w := by
  obtain ⟨p, rfl⟩ := Work.LerayHirsch.surjective_mkProj Z x
  rw [Work.LerayHirsch.mem_tautBaseSetProj_mk] at hx hx'
  have hxP : Work.LerayHirsch.mkProj Z p ∈ Work.LerayHirsch.tautBaseSetProj Z a :=
    (Work.LerayHirsch.mem_tautBaseSetProj_mk Z a p).mpr hx
  have hxP' : Work.LerayHirsch.mkProj Z p ∈ Work.LerayHirsch.tautBaseSetProj Z a' :=
    (Work.LerayHirsch.mem_tautBaseSetProj_mk Z a' p).mpr hx'
  rw [Work.LerayHirsch.twistCore_coordChange_eq, scl_tautLine_coordChange]
  rw [Work.Thom.bundleComap_coordChange, Work.Thom.tautQuotient_coordChange]
  simp only [tauMap]
  -- the right-hand side, in the same normal form
  have hR : (Work.LerayHirsch.quotientBundle Z).coordChange a a' (Work.LerayHirsch.mkProj Z p) w
      = Work.Thom.quoFun a'.2 (Work.LerayHirsch.chartCoord Z a'.1 p)
          (Z.coordChange a.1 a'.1 (Work.LerayHirsch.projMap Z (Work.LerayHirsch.mkProj Z p))
            (Work.Thom.fillFun a.2 w)) := by
    rw [Work.LerayHirsch.quotientBundle_coordChange, Work.LerayHirsch.quotientCoord_mk,
      Work.Thom.tautQuotient_coordChange, Work.LerayHirsch.projMap_mkProj]
    rfl
  rw [hR]
  -- the twist transition, expanded
  have hE : (Work.LerayHirsch.tautTwist Z).coordChange (a, a.1) (a', a'.1)
        (Work.LerayHirsch.mkProj Z p)
      = scl ((Work.LerayHirsch.tautLine Z).coordChange a' a (Work.LerayHirsch.mkProj Z p)) •
        Z.coordChange a.1 a'.1 (Work.LerayHirsch.projMap Z (Work.LerayHirsch.mkProj Z p)) := by
    rw [Work.LerayHirsch.tautTwist_coordChange, Work.Gen.dualLineCore_coordChange,
      Work.Thom.bundleComap_coordChange]
  have hchart : Work.LerayHirsch.TautEmbed.chartRatioVec Z a'.1 a'.2 a'.1
        (Work.LerayHirsch.mkProj Z p)
      = (Work.LerayHirsch.chartCoord Z a'.1 p a'.2)⁻¹ • Work.LerayHirsch.chartCoord Z a'.1 p := by
    rw [Work.LerayHirsch.TautEmbed.chartRatioVec_mk, Work.LerayHirsch.TautEmbed.chartRatioRaw,
      if_pos hx'.2]
  rw [hσ (Work.LerayHirsch.mkProj Z p), localTriv_auxBundle Z σ hσ hσv a' hxP',
    hE, smul_apply, scl_tautLine_coordChange Z a' a (Work.LerayHirsch.mkProj Z p),
    hchart, quoFun_smul_smul a'.2 (Work.LerayHirsch.chartCoord Z a'.1 p) _
      ((Work.LerayHirsch.chartCoord Z a'.1 p a'.2)⁻¹) (Work.LerayHirsch.tautCoeffLift Z a' a (Work.LerayHirsch.mkProj Z p))
      (inv_ne_zero hx'.2),
    smul_smul, mul_comm (Work.LerayHirsch.tautCoeffLift Z a a' (Work.LerayHirsch.mkProj Z p)),
    tautCoeffLift_mul_recip Z hxP hxP', one_smul]

theorem coordChange_twist_tau (a a' : ι × Fin (n + 1)) (x : Work.LerayHirsch.ProjSpace Z)
    (hx : x ∈ Work.LerayHirsch.tautBaseSetProj Z a)
    (hx' : x ∈ Work.LerayHirsch.tautBaseSetProj Z a') :
    (Work.LerayHirsch.twistCore (Work.LerayHirsch.tautLine Z) (auxBundle Z σ)).coordChange
        (tauMap (n := n) a) (tauMap (n := n) a') x
      = (Work.LerayHirsch.quotientBundle Z).coordChange a a' x :=
  ContinuousLinearMap.ext fun w => coordChange_twist_tau_apply Z σ hσ hσv a a' x hx hx' w

theorem nonempty_bundleIso_reindexCore_quotientBundle
    (hτ : ∀ x : Work.LerayHirsch.ProjSpace Z, ∃ a : ι × Fin (n + 1),
      x ∈ (Work.LerayHirsch.twistCore (Work.LerayHirsch.tautLine Z) (auxBundle Z σ)).baseSet
        (tauMap (n := n) a)) :
    Nonempty (Work.Thom.BundleIso
      (Work.Agree.reindexCore
        (Work.LerayHirsch.twistCore (Work.LerayHirsch.tautLine Z) (auxBundle Z σ))
        (tauMap (n := n)) hτ)
      (Work.LerayHirsch.quotientBundle Z)) := by
  have hbase : ∀ a : ι × Fin (n + 1),
      (Work.Agree.reindexCore
        (Work.LerayHirsch.twistCore (Work.LerayHirsch.tautLine Z) (auxBundle Z σ))
        (tauMap (n := n)) hτ).baseSet a
        = (Work.LerayHirsch.quotientBundle Z).baseSet a := by
    intro a
    rw [Work.Agree.reindexCore_baseSet, baseSet_twist_tau Z σ hσ hσv a]
  refine Work.Thom.nonempty_bundleIso_of_gauge
    (Work.Agree.reindexCore
      (Work.LerayHirsch.twistCore (Work.LerayHirsch.tautLine Z) (auxBundle Z σ))
      (tauMap (n := n)) hτ)
    (Work.LerayHirsch.quotientBundle Z)
    (fun i t b => (Work.LerayHirsch.quotientBundle Z).coordChange i t b)
    (fun i t b => (Work.LerayHirsch.quotientBundle Z).coordChange t i b)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro i i'
    rw [hbase i]
    exact (Work.LerayHirsch.quotientBundle Z).continuousOn_coordChange i i'
  · intro i i'
    rw [hbase i, Set.inter_comm]
    exact (Work.LerayHirsch.quotientBundle Z).continuousOn_coordChange i' i
  · intro i t t' b hi ht ht'
    have hiQ : b ∈ (Work.LerayHirsch.quotientBundle Z).baseSet i := by
      rw [← hbase i]; exact hi
    exact (Work.LerayHirsch.quotientBundle Z).coordChange_linear_comp i t t' b ⟨⟨hiQ, ht⟩, ht'⟩
  · intro i t i' b hi hi' ht
    have hiQ : b ∈ (Work.LerayHirsch.quotientBundle Z).baseSet i := by
      rw [← hbase i]; exact hi
    have hiQ' : b ∈ (Work.LerayHirsch.quotientBundle Z).baseSet i' := by
      rw [← hbase i']; exact hi'
    have hcc : (Work.Agree.reindexCore
        (Work.LerayHirsch.twistCore (Work.LerayHirsch.tautLine Z) (auxBundle Z σ))
        (tauMap (n := n)) hτ).coordChange i' i b
        = (Work.LerayHirsch.quotientBundle Z).coordChange i' i b :=
      coordChange_twist_tau Z σ hσ hσv i' i b hiQ' hiQ
    rw [hcc]
    exact (Work.LerayHirsch.quotientBundle Z).coordChange_linear_comp i' i t b
      ⟨⟨hiQ', hiQ⟩, ht⟩
  · intro i t t' b hi ht ht'
    have hiQ : b ∈ (Work.LerayHirsch.quotientBundle Z).baseSet i := by
      rw [← hbase i]; exact hi
    exact (Work.LerayHirsch.quotientBundle Z).coordChange_linear_comp t' t i b ⟨⟨ht', ht⟩, hiQ⟩
  · intro i t i' b hi hi' ht
    have hiQ : b ∈ (Work.LerayHirsch.quotientBundle Z).baseSet i := by
      rw [← hbase i]; exact hi
    have hiQ' : b ∈ (Work.LerayHirsch.quotientBundle Z).baseSet i' := by
      rw [← hbase i']; exact hi'
    have hcc : (Work.Agree.reindexCore
        (Work.LerayHirsch.twistCore (Work.LerayHirsch.tautLine Z) (auxBundle Z σ))
        (tauMap (n := n)) hτ).coordChange i i' b
        = (Work.LerayHirsch.quotientBundle Z).coordChange i i' b :=
      coordChange_twist_tau Z σ hσ hσv i i' b hiQ hiQ'
    rw [hcc]
    exact (Work.LerayHirsch.quotientBundle Z).coordChange_linear_comp t i i' b ⟨⟨ht, hiQ⟩, hiQ'⟩
  · intro i i' b x hb
    have hiQ : b ∈ (Work.LerayHirsch.quotientBundle Z).baseSet i := by
      rw [← hbase i]; exact hb.1
    have hcomp := (Work.LerayHirsch.quotientBundle Z).coordChange_linear_comp i i' i b
      ⟨⟨hiQ, hb.2⟩, hiQ⟩
    have hself : (Work.LerayHirsch.quotientBundle Z).coordChange i i b
        = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n)) :=
      ContinuousLinearMap.ext fun v =>
        (Work.LerayHirsch.quotientBundle Z).coordChange_self i b hiQ v
    simp only [← ContinuousLinearMap.comp_apply, hcomp, hself, ContinuousLinearMap.id_apply]
  · intro i i' b y hb
    have hiQ' : b ∈ (Work.LerayHirsch.quotientBundle Z).baseSet i' := hb.2
    have hiQ : b ∈ (Work.LerayHirsch.quotientBundle Z).baseSet i := by
      rw [← hbase i]; exact hb.1
    have hcomp := (Work.LerayHirsch.quotientBundle Z).coordChange_linear_comp i' i i' b
      ⟨⟨hiQ', hiQ⟩, hiQ'⟩
    have hself : (Work.LerayHirsch.quotientBundle Z).coordChange i' i' b
        = ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin n)) :=
      ContinuousLinearMap.ext fun v =>
        (Work.LerayHirsch.quotientBundle Z).coordChange_self i' b hiQ' v
    simp only [← ContinuousLinearMap.comp_apply, hcomp, hself, ContinuousLinearMap.id_apply]

end Key
theorem splitsCanonical {n : ℕ} {B : Type} [TopologicalSpace B] [ParacompactSpace B] [T2Space B] {ι : Type} [Fintype ι] (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin (n + 1))) ι) : Nonempty (Work.Thom.BundleIso (Work.Thom.bundleComap Z (Work.LerayHirsch.projMap Z)) (Work.Whitney.whitneySum (Work.LerayHirsch.tautLine Z) (Work.LerayHirsch.quotientBundle Z))) := by
  obtain ⟨σ, hσ, hσv⟩ := Work.LerayHirsch.exists_tautSection Z
  haveI : ParacompactSpace (Work.LerayHirsch.ProjSpace Z) :=
    Work.LerayHirsch.paracompactSpace_projSpace Z
  haveI : T2Space (Work.LerayHirsch.ProjSpace Z) := Work.LerayHirsch.t2Space_projSpace Z
  let Eps : VectorBundleCore ℂ (Work.LerayHirsch.ProjSpace Z)
      (EuclideanSpace ℂ (Fin 1)) PUnit :=
    trivialVectorBundleCore ℂ (Work.LerayHirsch.ProjSpace Z) (EuclideanSpace ℂ (Fin 1)) PUnit
  have hτ : ∀ x : Work.LerayHirsch.ProjSpace Z, ∃ a : ι × Fin (n + 1),
      x ∈ (Work.LerayHirsch.twistCore (Work.LerayHirsch.tautLine Z) (auxBundle Z σ)).baseSet
        (tauMap (n := n) a) := by
    intro x
    refine ⟨(Work.LerayHirsch.tautLine Z).indexAt x, ?_⟩
    rw [baseSet_twist_tau Z σ hσ hσv]
    have h := (Work.LerayHirsch.tautLine Z).mem_baseSet_at x
    simp only [Work.LerayHirsch.quotientBundle_baseSet, Work.LerayHirsch.tautLine_baseSet] at h ⊢
    exact h
  obtain ⟨eW⟩ := Work.Whitney.nonempty_bundleIso_of_nowhereZeroSection_of_paracompact
    (Work.LerayHirsch.tautTwist Z) σ hσ (ι₀ := PUnit)
  obtain ⟨e1⟩ := Work.LerayHirsch.nonempty_bundleIso_twist_dual (Work.LerayHirsch.tautLine Z)
    (Work.Thom.bundleComap Z (Work.LerayHirsch.projMap Z))
  obtain ⟨e2⟩ := Work.LerayHirsch.nonempty_bundleIso_twist_congr (Work.LerayHirsch.tautLine Z)
    (Work.LerayHirsch.tautTwist Z) (Work.Whitney.whitneySum (auxBundle Z σ) Eps) eW
  obtain ⟨e3⟩ := Work.LerayHirsch.nonempty_bundleIso_twist_whitneySum (Work.LerayHirsch.tautLine Z)
    (auxBundle Z σ) Eps
  obtain ⟨e4⟩ := Work.LerayHirsch.nonempty_bundleIso_twist_trivial
    (B := Work.LerayHirsch.ProjSpace Z) (ιL := ι × Fin (n + 1)) (ι₀ := PUnit)
    (Work.LerayHirsch.tautLine Z)
  obtain ⟨e5⟩ := Work.LerayHirsch.nonempty_bundleIso_whitneySum_snd
    (Work.LerayHirsch.twistCore (Work.LerayHirsch.tautLine Z) (auxBundle Z σ))
    (Work.LerayHirsch.twistCore (Work.LerayHirsch.tautLine Z) Eps)
    (Work.LerayHirsch.tautLine Z) e4
  obtain ⟨e6⟩ := Work.Whitney.nonempty_bundleIso_whitneySum_comm
    (Work.LerayHirsch.twistCore (Work.LerayHirsch.tautLine Z) (auxBundle Z σ))
    (Work.LerayHirsch.tautLine Z)
  obtain ⟨e7⟩ := nonempty_bundleIso_reindexCore_quotientBundle Z σ hσ hσv hτ
  obtain ⟨e7'⟩ := Work.Agree.nonempty_bundleIso_reindexCore_self
    (Work.LerayHirsch.twistCore (Work.LerayHirsch.tautLine Z) (auxBundle Z σ))
    (tauMap (n := n)) hτ
  obtain ⟨e8⟩ := Work.LerayHirsch.nonempty_bundleIso_whitneySum_snd
    (Work.LerayHirsch.tautLine Z)
    (Work.LerayHirsch.twistCore (Work.LerayHirsch.tautLine Z) (auxBundle Z σ))
    (Work.LerayHirsch.quotientBundle Z) (e7'.symm.trans e7)
  exact ⟨e1.symm.trans (e2.trans (e3.trans (e5.trans (e6.trans e8))))⟩

end

end Work.Gen
