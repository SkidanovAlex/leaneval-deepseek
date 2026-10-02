import Mathlib
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.Grassmann.CP4Probe.Map
import Submission.Work.ThomBordism.Grassmann.CP4Probe.Compat
import Submission.Work.ThomBordism.Grassmann.probeGauge
import Submission.Work.ThomBordism.Grassmann.cp4CupSelfNeZero
import Submission.Work.ThomBordism.Grassmann.zStd_pontryagin_ne_zero
import Submission.Work.ThomBordism.Grassmann.Probe2.p1RatNeZero_of_twoTwo
import Submission.Work.ThomBordism.Grassmann.CohMap_p2_incl
import Submission.Work.ThomBordism.Grassmann.inclusionBundleIso
import Submission.Work.Thom.pontryaginClass_comap
import Submission.Work.Thom.realSumStable
import Submission.Work.Whitney.chernClass_whitneySum_rank_zero
import Submission.Work.ThomBordism.Grassmann.p1CruxRatNeZero
import Submission.Work.ThomBordism.Grassmann.c4Aux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000

namespace Work.ThomBordism.Grassmann.LowDegree

open Work.TangentClasses
open scoped TensorProduct

noncomputable section

variable {B : Type} [TopologicalSpace B]

/-! ## Stability of the Pontryagin classes under adding a trivial real line -/

/-- **Stability of `p_i` under adding a trivial real line summand**: if `Z' ≅ Z ⊕ ε¹` then
`p_i(Z') = p_i(Z)`. -/
private theorem pontryaginClass_sumEpsR (i : ℕ) (ι₀ : Type) [Inhabited ι₀] {ι : Type} [Fintype ι]
    [Fintype ι₀] {k : ℕ} {ι' : Type} [Fintype ι']
    (Z : RealBundle B (EuclideanSpace ℝ (Fin k)) ι)
    (Z' : RealBundle B (EuclideanSpace ℝ (Fin (k + 1))) ι')
    (e : Work.Thom.BundleIso (Work.Thom.sumEpsR ι₀ Z) Z') :
    Work.Thom.pontryaginClass i Z' = Work.Thom.pontryaginClass i Z := by
  have h : Work.Thom.chernClass (k + 1) (2 * i) (Work.Thom.complexificationCore Z')
      = Work.Thom.chernClass k (2 * i) (Work.Thom.complexificationCore Z) :=
    Work.Thom.chernClass_complexification_sumEpsR ι₀ Z Z' e (2 * i)
  unfold Work.Thom.pontryaginClass
  exact congrArg (fun c => Work.Thom.cohTransport (show 2 * (2 * i) = 4 * i from by ring)
    (((-1 : ℤ) ^ i) • c)) h

/-! ## A pullback computation for `p₁²` -/

private theorem p1Sq_comap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (φ : C(X, Y))
    (x : Work.Thom.Coh ℤ 4 Y) (x' : Work.Thom.Coh ℤ 4 X)
    (h : (Work.Thom.CohMap φ ℤ 4).hom x = x') :
    (Work.Thom.CohMap φ ℤ 8).hom (Work.Cohomology.cupH' ℤ (sset Y) 4 4 x x)
      = Work.Cohomology.cupH' ℤ (sset X) 4 4 x' x' := by
  rw [Work.Cohomology.cupNaturalH ℤ (TopCat.ofHom φ) 4 4, h]

/-! ## The one-step bundle comparisons for `p₁²` and `p₂` -/

/-- The `k`-step, `p₁²`-part, for an explicit bundle isomorphism. -/
private theorem addLine_p1Sq {k m : ℕ} (φ : C(OG k m, OG (k + 1) m))
    (e : Work.Thom.BundleIso (Work.Thom.bundleComap (tautologicalBundle (k + 1) m) φ)
      (Work.Thom.sumEpsR (Fin 1) (tautologicalBundle k m))) :
    (Work.Thom.CohMap φ ℤ 8).hom (p1Sq (k + 1) m) = p1Sq k m := by
  have hnat : (Work.Thom.CohMap φ ℤ 4).hom
      (Work.Thom.pontryagin1 (tautologicalBundle (k + 1) m))
      = Work.Thom.pontryagin1 (Work.Thom.bundleComap (tautologicalBundle (k + 1) m) φ) :=
    (Work.Thom.pontryagin1_comap (tautologicalBundle (k + 1) m) φ).symm
  have hiso : Work.Thom.pontryagin1
        (Work.Thom.bundleComap (tautologicalBundle (k + 1) m) φ)
      = Work.Thom.pontryagin1 (tautologicalBundle k m) :=
    Work.Thom.pontryagin1_sumEpsR (Fin 1) (tautologicalBundle k m)
      (Work.Thom.bundleComap (tautologicalBundle (k + 1) m) φ) e.symm
  have hp1 : (Work.Thom.CohMap φ ℤ 4).hom (p1 (k + 1) m) = p1 k m := by
    rw [show p1 (k + 1) m = Work.Thom.pontryaginClass 1 (tautologicalBundle (k + 1) m)
          from rfl,
      show p1 k m = Work.Thom.pontryaginClass 1 (tautologicalBundle k m) from rfl,
      Work.Thom.pontryaginClass_one, Work.Thom.pontryaginClass_one, hnat, hiso]
  rw [show p1Sq (k + 1) m
        = Work.Cohomology.cupH' ℤ (sset (OG (k + 1) m)) 4 4 (p1 (k + 1) m) (p1 (k + 1) m)
        from rfl,
    show p1Sq k m = Work.Cohomology.cupH' ℤ (sset (OG k m)) 4 4 (p1 k m) (p1 k m) from rfl]
  exact p1Sq_comap φ (p1 (k + 1) m) (p1 k m) hp1

/-- The `k`-step, `p₂`-part, for an explicit bundle isomorphism. -/
private theorem addLine_p2 {k m : ℕ} (φ : C(OG k m, OG (k + 1) m))
    (e : Work.Thom.BundleIso (Work.Thom.bundleComap (tautologicalBundle (k + 1) m) φ)
      (Work.Thom.sumEpsR (Fin 1) (tautologicalBundle k m))) :
    (Work.Thom.CohMap φ ℤ 8).hom (p2 (k + 1) m) = p2 k m := by
  have hstab : Work.Thom.pontryaginClass 2
        (Work.Thom.bundleComap (tautologicalBundle (k + 1) m) φ)
      = Work.Thom.pontryaginClass 2 (tautologicalBundle k m) :=
    pontryaginClass_sumEpsR 2 (Fin 1) (tautologicalBundle k m)
      (Work.Thom.bundleComap (tautologicalBundle (k + 1) m) φ) e.symm
  have hnat := (Work.Thom.pontryaginClass_comap (i := 2)
    (tautologicalBundle (k + 1) m) φ).symm
  rw [show p2 (k + 1) m = Work.Thom.pontryaginClass 2 (tautologicalBundle (k + 1) m)
        from rfl,
      show p2 k m = Work.Thom.pontryaginClass 2 (tautologicalBundle k m) from rfl]
  rw [hnat, hstab]

/-- The `m`-step, `p₁²`-part, for an explicit bundle isomorphism. -/
private theorem incl_p1Sq {k m : ℕ} (φ : C(OG k m, OG k (m + 1)))
    (e : Work.Thom.BundleIso (Work.Thom.bundleComap (tautologicalBundle k (m + 1)) φ)
      (tautologicalBundle k m)) :
    (Work.Thom.CohMap φ ℤ 8).hom (p1Sq k (m + 1)) = p1Sq k m := by
  have hnat : (Work.Thom.CohMap φ ℤ 4).hom
      (Work.Thom.pontryagin1 (tautologicalBundle k (m + 1)))
      = Work.Thom.pontryagin1 (Work.Thom.bundleComap (tautologicalBundle k (m + 1)) φ) :=
    (Work.Thom.pontryagin1_comap (tautologicalBundle k (m + 1)) φ).symm
  have hiso : Work.Thom.pontryagin1
        (Work.Thom.bundleComap (tautologicalBundle k (m + 1)) φ)
      = Work.Thom.pontryagin1 (tautologicalBundle k m) :=
    Probe2.pontryagin1_eq_of_bundleIso _ _ e
  have hp1 : (Work.Thom.CohMap φ ℤ 4).hom (p1 k (m + 1)) = p1 k m := by
    rw [show p1 k (m + 1) = Work.Thom.pontryaginClass 1 (tautologicalBundle k (m + 1))
          from rfl,
      show p1 k m = Work.Thom.pontryaginClass 1 (tautologicalBundle k m) from rfl,
      Work.Thom.pontryaginClass_one, Work.Thom.pontryaginClass_one, hnat, hiso]
  rw [show p1Sq k (m + 1)
        = Work.Cohomology.cupH' ℤ (sset (OG k (m + 1))) 4 4 (p1 k (m + 1)) (p1 k (m + 1))
        from rfl,
    show p1Sq k m = Work.Cohomology.cupH' ℤ (sset (OG k m)) 4 4 (p1 k m) (p1 k m) from rfl]
  exact p1Sq_comap φ (p1 k (m + 1)) (p1 k m) hp1

/-- The `m`-step, `p₂`-part, for an explicit bundle isomorphism. -/
private theorem incl_p2 {k m : ℕ} (φ : C(OG k m, OG k (m + 1)))
    (e : Work.Thom.BundleIso (Work.Thom.bundleComap (tautologicalBundle k (m + 1)) φ)
      (tautologicalBundle k m)) :
    (Work.Thom.CohMap φ ℤ 8).hom (p2 k (m + 1)) = p2 k m := by
  have hstab : Work.Thom.pontryaginClass 2
        (Work.Thom.bundleComap (tautologicalBundle k (m + 1)) φ)
      = Work.Thom.pontryaginClass 2 (tautologicalBundle k m) :=
    incl_pontryaginClass_eq_of_bundleIso 2 e
  have hnat := (Work.Thom.pontryaginClass_comap (i := 2)
    (tautologicalBundle k (m + 1)) φ).symm
  rw [show p2 k (m + 1) = Work.Thom.pontryaginClass 2 (tautologicalBundle k (m + 1))
        from rfl,
      show p2 k m = Work.Thom.pontryaginClass 2 (tautologicalBundle k m) from rfl]
  rw [hnat, hstab]

/-- **The `k`-step**: the "add a line" map pulls both `p₁(γ)²` and `p₂(γ)` back to themselves. -/
private theorem stabilisation_addLine (k m : ℕ) :
    ∃ φ : C(OG k m, OG (k + 1) m),
      (Work.Thom.CohMap φ ℤ 8).hom (p1Sq (k + 1) m) = p1Sq k m ∧
      (Work.Thom.CohMap φ ℤ 8).hom (p2 (k + 1) m) = p2 k m := by
  obtain ⟨φ, ⟨e⟩⟩ := Probe2.addLineBundleIso k m (Fin 1)
  exact ⟨φ, addLine_p1Sq φ e, addLine_p2 φ e⟩

/-- **The `m`-step**: the ambient inclusion pulls both `p₁(γ)²` and `p₂(γ)` back to themselves. -/
private theorem stabilisation_incl (k m : ℕ) :
    ∃ φ : C(OG k m, OG k (m + 1)),
      (Work.Thom.CohMap φ ℤ 8).hom (p1Sq k (m + 1)) = p1Sq k m ∧
      (Work.Thom.CohMap φ ℤ 8).hom (p2 k (m + 1)) = p2 k m := by
  obtain ⟨φ, ⟨e⟩⟩ := inclusionBundleIso k m
  exact ⟨φ, incl_p1Sq φ e, incl_p2 φ e⟩

/-- **Stabilisation of `p₁²` and `p₂`**: for `k ≥ 2`, `m ≥ 8` there is
`Ψ : G̃r₂(ℝ¹⁰) → G̃r_k(ℝ^{k+m})` pulling `p₁²` back to `p₁²` of the base case and `p₂` back to
`p₂` of the base case. -/
private theorem chainP1SqP2 (k m : ℕ) (hk : 2 ≤ k) (hm : 8 ≤ m) :
    ∃ Ψ : C(OG 2 8, OG k m),
      (Work.Thom.CohMap Ψ ℤ 8).hom (p1Sq k m) = p1Sq 2 8 ∧
      (Work.Thom.CohMap Ψ ℤ 8).hom (p2 k m) = p2 2 8 := by
  have hstepM : ∀ (k e : ℕ), ∃ Ψ : C(OG k 8, OG k (8 + e)),
      (Work.Thom.CohMap Ψ ℤ 8).hom (p1Sq k (8 + e)) = p1Sq k 8 ∧
      (Work.Thom.CohMap Ψ ℤ 8).hom (p2 k (8 + e)) = p2 k 8 := by
    intro k e
    induction e with
    | zero =>
      refine ⟨ContinuousMap.id _, ?_, ?_⟩ <;>
        · rw [Work.Thom.CohMap_id]; rfl
    | succ e ih =>
      obtain ⟨Ψ, h1, h2⟩ := ih
      obtain ⟨φ, hφ1, hφ2⟩ := stabilisation_incl k (8 + e)
      refine ⟨φ.comp Ψ, ?_, ?_⟩
      · change (Work.Thom.CohMap (φ.comp Ψ) ℤ 8).hom (p1Sq k (8 + e + 1)) = p1Sq k 8
        rw [Work.Thom.CohMap_comp Ψ φ ℤ 8]
        change (Work.Thom.CohMap Ψ ℤ 8).hom
          ((Work.Thom.CohMap φ ℤ 8).hom (p1Sq k (8 + e + 1))) = p1Sq k 8
        rw [hφ1, h1]
      · change (Work.Thom.CohMap (φ.comp Ψ) ℤ 8).hom (p2 k (8 + e + 1)) = p2 k 8
        rw [Work.Thom.CohMap_comp Ψ φ ℤ 8]
        change (Work.Thom.CohMap Ψ ℤ 8).hom
          ((Work.Thom.CohMap φ ℤ 8).hom (p2 k (8 + e + 1))) = p2 k 8
        rw [hφ2, h2]
  have hstepK : ∀ (d m : ℕ), ∃ Ψ : C(OG 2 m, OG (2 + d) m),
      (Work.Thom.CohMap Ψ ℤ 8).hom (p1Sq (2 + d) m) = p1Sq 2 m ∧
      (Work.Thom.CohMap Ψ ℤ 8).hom (p2 (2 + d) m) = p2 2 m := by
    intro d m
    induction d with
    | zero =>
      refine ⟨ContinuousMap.id _, ?_, ?_⟩ <;>
        · rw [Work.Thom.CohMap_id]; rfl
    | succ d ih =>
      obtain ⟨Ψ, h1, h2⟩ := ih
      obtain ⟨φ, hφ1, hφ2⟩ := stabilisation_addLine (2 + d) m
      refine ⟨φ.comp Ψ, ?_, ?_⟩
      · change (Work.Thom.CohMap (φ.comp Ψ) ℤ 8).hom (p1Sq (2 + d + 1) m) = p1Sq 2 m
        rw [Work.Thom.CohMap_comp Ψ φ ℤ 8]
        change (Work.Thom.CohMap Ψ ℤ 8).hom
          ((Work.Thom.CohMap φ ℤ 8).hom (p1Sq (2 + d + 1) m)) = p1Sq 2 m
        rw [hφ1, h1]
      · change (Work.Thom.CohMap (φ.comp Ψ) ℤ 8).hom (p2 (2 + d + 1) m) = p2 2 m
        rw [Work.Thom.CohMap_comp Ψ φ ℤ 8]
        change (Work.Thom.CohMap Ψ ℤ 8).hom
          ((Work.Thom.CohMap φ ℤ 8).hom (p2 (2 + d + 1) m)) = p2 2 m
        rw [hφ2, h2]
  obtain ⟨d, rfl⟩ : ∃ d, k = 2 + d := ⟨k - 2, by omega⟩
  obtain ⟨e, rfl⟩ : ∃ e, m = 8 + e := ⟨m - 8, by omega⟩
  obtain ⟨ΨK, hK1, hK2⟩ := hstepK d (8 + e)
  obtain ⟨ΨM, hM1, hM2⟩ := hstepM 2 e
  refine ⟨ΨK.comp ΨM, ?_, ?_⟩
  · change (Work.Thom.CohMap (ΨK.comp ΨM) ℤ 8).hom (p1Sq (2 + d) (8 + e)) = p1Sq 2 8
    rw [Work.Thom.CohMap_comp ΨM ΨK ℤ 8]
    change (Work.Thom.CohMap ΨM ℤ 8).hom
      ((Work.Thom.CohMap ΨK ℤ 8).hom (p1Sq (2 + d) (8 + e))) = p1Sq 2 8
    rw [hK1, hM1]
  · change (Work.Thom.CohMap (ΨK.comp ΨM) ℤ 8).hom (p2 (2 + d) (8 + e)) = p2 2 8
    rw [Work.Thom.CohMap_comp ΨM ΨK ℤ 8]
    change (Work.Thom.CohMap ΨM ℤ 8).hom
      ((Work.Thom.CohMap ΨK ℤ 8).hom (p2 (2 + d) (8 + e))) = p2 2 8
    rw [hK2, hM2]

/-! ## The `ℂP⁴`-probe detects `p₁²` -/

private theorem probeSigma_twoEight_bundleIso :
    Nonempty (Work.Thom.BundleIso
      (Work.Thom.bundleComap (tautologicalBundle 2 8)
        (probeSigma 2 8 (by norm_num) (by norm_num))) zStd) := by
  obtain ⟨e₁⟩ := probeBundleIso_aux 2 8 (by norm_num) (by norm_num)
  haveI : Subsingleton (EuclideanSpace ℝ (Fin (2 - 2))) := by
    rw [show (2 : ℕ) - 2 = 0 from rfl]
    infer_instance
  obtain ⟨e₂⟩ := Work.Whitney.nonempty_bundleIso_sumCore_of_subsingleton
    (Work.Whitney.sumFibreR 2 (2 - 2)) zStd
    (Work.TangentClasses.RealBundle.trivial (Work.Projective.CP 2)
      (EuclideanSpace ℝ (Fin (2 - 2))) (Fin 1))
  exact ⟨e₁.trans e₂⟩

private theorem probeSigma_twoEight_p1_ne_zero :
    (Work.Thom.CohMap (probeSigma 2 8 (by norm_num) (by norm_num)) ℤ 4).hom (p1 2 8) ≠ 0 := by
  rw [show p1 2 8 = Work.Thom.pontryaginClass 1 (tautologicalBundle 2 8) from rfl,
    Work.Thom.pontryaginClass_one]
  rw [← Work.Thom.pontryagin1_comap (tautologicalBundle 2 8)
    (probeSigma 2 8 (by norm_num) (by norm_num))]
  obtain ⟨e⟩ := probeSigma_twoEight_bundleIso
  rw [Probe2.pontryagin1_eq_of_bundleIso _ _ e]
  exact zStd_pontryagin_ne_zero

/-- **The `ℂP⁴`-probe detects `p₁`**. -/
private theorem probeCP4Map_p1_ne_zero :
    (Work.Thom.CohMap probeCP4Map ℤ 4).hom (p1 2 8) ≠ 0 := by
  intro h0
  have h2 : (Work.Thom.CohMap (probeCP4Map.comp iota) ℤ 4).hom (p1 2 8) = 0 := by
    rw [Work.Thom.CohMap_comp iota probeCP4Map ℤ 4]
    change (Work.Thom.CohMap iota ℤ 4).hom
      ((Work.Thom.CohMap probeCP4Map ℤ 4).hom (p1 2 8)) = 0
    rw [h0, map_zero]
  rw [probeCP4Map_comp_iota] at h2
  exact probeSigma_twoEight_p1_ne_zero h2

/-- **The `ℂP⁴`-probe detects `p₁²`** (integrally). -/
private theorem probeCP4Map_p1Sq_ne_zero :
    (Work.Thom.CohMap probeCP4Map ℤ 8).hom (p1Sq 2 8) ≠ 0 := by
  have hEq : (Work.Thom.CohMap probeCP4Map ℤ 8).hom (p1Sq 2 8)
      = Work.Cohomology.cupH' ℤ (sset (Work.Projective.CP 4)) 4 4
          ((Work.Thom.CohMap probeCP4Map ℤ 4).hom (p1 2 8))
          ((Work.Thom.CohMap probeCP4Map ℤ 4).hom (p1 2 8)) := by
    rw [p1Sq]
    exact Work.Cohomology.cupNaturalH ℤ (TopCat.ofHom probeCP4Map) 4 4 (p1 2 8) (p1 2 8)
  rw [hEq]
  exact cp4CupSelfNeZero _ probeCP4Map_p1_ne_zero

/-- **`p₂` of a rank-two real bundle vanishes.** -/
private theorem pontryaginClass_two_eq_zero_of_rank_two {B : Type} [TopologicalSpace B] {ι : Type}
    [Fintype ι] (Z : RealBundle B (EuclideanSpace ℝ (Fin 2)) ι) :
    Work.Thom.pontryaginClass 2 Z = 0 := by
  unfold Work.Thom.pontryaginClass
  rw [Work.Thom.chernClass_eq_zero_of_lt (Work.Thom.complexificationCore Z)
    (by norm_num : 2 < 4)]
  simp

/-- **The `ℂP⁴`-probe detecting `p₁²` and killing `p₂`.** Expected full name: `Work.ThomBordism.Grassmann.LowDegree.p1SqProbe` (module `Submission.Work.ThomBordism.Grassmann.LowDegree.p1SqProbe`), in `namespace Work.ThomBordism.Grassmann.LowDegree`.

This is the map `σ = Ψ ∘ probeCP4Map` where `probeCP4Map : C(ℂP⁴, OG 2 8)` is the `ℂP⁴`-probe of `Submission/Work/ThomBordism/Grassmann/CP4Probe/Map.lean` (probe bundle `realification (tautLine 4)`) and `Ψ : C(OG 2 8, OG k m)` is a stabilisation with `Ψ^*(γ_{k,m}) ≅ γ_{2,8} ⊕ ε^{k-2}` (the chain of `CohMap_p1_addLine`/`CohMap_p1_incl` as in `chainP1Sq`). First conjunct: a port of `Work.ThomBordism.Grassmann.probeCP4_p1Sq_ne_zero` (`Submission/Work/ThomBordism/Grassmann/probeCP4_p1Sq_ne_zero.lean`) to the clash-free island: replace `import ...p1RatNeZero_of_twoTwo` by `import ...Probe2.p1RatNeZero_of_twoTwo` (giving `Probe2.CohMap_p1_addLine`, `Probe2.CohMap_p1_incl`, `Probe2.pontryagin1_eq_of_bundleIso`), and copy the (clash-free) `probeSigmaP1NeZero` proof using `Probe2.pontryagin1_eq_of_bundleIso`. The integral non-vanishing of `probeCP4Map_p1Sq_ne_zero` must be rationalised (e.g. via `P1Crux.tmul_one_ne_zero_of_iso_int` with the isomorphism `H⁸(ℂP⁴;ℤ) ≅ ℤ`, as used in `probeCP4_p1Sq_ne_zero.lean`/`p1Rat_ne_zero_via_probe.lean`). Second conjunct: `σ^*(p₂ k m) = probeCP4Map^*(p₂(γ_{2,8} ⊕ ε^{k-2})) = probeCP4Map^*(p₂(γ_{2,8})) = 0`, using naturality of `p₂` (`Work.Thom.pontryaginClass_comap`), stability of `p₂` under adding a trivial real line summand (reprove `pontryaginClass_sumEpsR` for `i = 2` from `Work.Thom.chernClass_complexification_sumEpsR`, as in `probeCP4_p2_ne_zero_of_c4.lean`), and vanishing of the top Pontryagin class of a rank-2 bundle (`Work.Thom.chernClass_eq_zero_of_lt`). Must be importable together with island A (`grassmannianLowDegreeVanishing`): do NOT import `AddLineDefs`, `AddLineGauge`, `p1RatNeZero_of_twoTwo`, `probeSigmaP1NeZero`. -/
theorem p1SqProbe (k m : ℕ) (hk : 2 ≤ k) (hm : 8 ≤ m) :
    ∃ σ : C(Work.Projective.CP 4, Work.ThomBordism.Grassmann.OG k m),
      TensorProduct.tmul ℤ (1 : ℚ)
          ((Work.Thom.CohMap σ ℤ 8).hom (Work.ThomBordism.Grassmann.p1Sq k m)) ≠ 0
      ∧ TensorProduct.tmul ℤ (1 : ℚ)
          ((Work.Thom.CohMap σ ℤ 8).hom (Work.ThomBordism.Grassmann.p2 k m)) = 0 := by
  obtain ⟨Ψ, h1, h2⟩ := chainP1SqP2 k m hk hm
  refine ⟨Ψ.comp probeCP4Map, ?_, ?_⟩
  · rw [Work.Thom.CohMap_comp probeCP4Map Ψ ℤ 8]
    change TensorProduct.tmul ℤ (1 : ℚ)
      ((Work.Thom.CohMap probeCP4Map ℤ 8).hom
        ((Work.Thom.CohMap Ψ ℤ 8).hom (Work.ThomBordism.Grassmann.p1Sq k m))) ≠ 0
    rw [h1]
    exact P1Crux.tmul_one_ne_zero_of_iso_int cp4CohEightEquiv probeCP4Map_p1Sq_ne_zero
  · rw [Work.Thom.CohMap_comp probeCP4Map Ψ ℤ 8]
    change TensorProduct.tmul ℤ (1 : ℚ)
      ((Work.Thom.CohMap probeCP4Map ℤ 8).hom
        ((Work.Thom.CohMap Ψ ℤ 8).hom (Work.ThomBordism.Grassmann.p2 k m))) = 0
    rw [h2]
    rw [show Work.ThomBordism.Grassmann.p2 2 8 = 0 from
      pontryaginClass_two_eq_zero_of_rank_two (tautologicalBundle 2 8)]
    simp


end

end Work.ThomBordism.Grassmann.LowDegree
