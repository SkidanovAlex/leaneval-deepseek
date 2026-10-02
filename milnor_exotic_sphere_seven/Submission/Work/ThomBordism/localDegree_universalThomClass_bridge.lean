import Mathlib
import Submission.Work.ThomBordism.orientedFibreGen
import Submission.Work.ThomBordism.TubeLocalDegree
import Submission.Work.ThomBordism.tautologicalClassSensitivity
import Submission.Work.ThomBordism.gtdGaussCandidate
import Submission.Work.ThomBordism.gtdU_span_top
import Submission.Work.ThomBordism.fibreRes_gtdU_canonical
import Submission.Work.ThomBordism.exists_kronH_zeroSection_fund_ne_zero
import Submission.Work.ThomBordism.localDegreeSpan
import Submission.Work.ThomBordism.thomClass_eq_smul
import Submission.Work.ThomBordism.Grassmann.Model
import Submission.Work.ThomBordism.branchSignUniformFinal
import Submission.Work.ThomBordism.localDegreeGenExists
import Submission.Work.ThomBordism.fibreRes_localDegreeClass_eq_nfGen
import Submission.Work.ThomBordism.coorientationRef
import Submission.Work.ThomBordism.stdModelGen_pm_stdThomGen
import Submission.Work.Thom.realThomClassOf_natural
import Submission.Work.ThomBordism.tautologicalBundleHoriO

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

open CategoryTheory Limits
open scoped Topology

namespace Work.ThomBordism

noncomputable section

open Work.ThomBordism.PontryaginThom Work.Tubular

/-!
# The bridge from the signed `coorFibre` localisation statement to the target

This `sorry`-free module records the exact reduction of
`Work.ThomBordism.localDegree_universalThomClass` (the target of the path
`ThomBordism/localDegree_universalThomClass`) to the *signed localisation* statements of the sibling
path (`ThomBordism/coorFibre_localDegreeClass_signed`,
`ThomBordism/canonicalGauss_isLocalDegreeClass_signed`).  It is separated from the target's own file
(which still contains a `sorry` for the target) so that it can be imported by other agents.

Contents:

* `Work.ThomBordism.exists_coorFibre_eq_smul_nfGen` — the coorientation reference `coorFibre` is a
  fixed multiple of `nfGen` (both are the `nfRead`-readings of the two *model* generators, which
  differ by a fixed sign: `Work.ThomBordism.stdModelGen_pm_stdThomGen`).  In particular the two
  conventions differ by a datum-independent sign, so a statement against one of them converts into a
  statement against the other.
* `Work.ThomBordism.fibreRes_localDegreeClass_eq_nfGen_uniform_of_coorFibre` — the signed
  `coorFibre` form of the uniform fibre restriction implies the `nfGen` form (UF2).
* `Work.ThomBordism.localDegree_universalThomClass_of_coorFibre` — UF2 gives the target
  (`localDegree_universalThomClass_of_uniformF2`, the reduction of session 41).
* `Work.ThomBordism.localDegree_universalThomClass_of_canonicalGauss_signed` — the target from the
  *signed canonical Gauss* statement (with the sign absorbed into the choice `u₀ = ±Ucan`).
-/

/-! ## The `coorFibre` form of the uniform fibre restriction

The route of the sibling path `ThomBordism/coorFibre_localDegreeClass_signed` states the uniform
fibre restriction against the *determinate* coorientation reference `Work.ThomBordism.coorFibre`
(the reading of the *explicit* model generator `Work.ThomBordism.stdModelGen` in the σ-corrected
frame), with the explicit sign `(-1)^{k(k-1)/2}`:

    IsLocalDegreeClass C g hg hR hbox U  →  nfRes E x k U = (-1)^{k(k-1)/2} • coorFibre hk E ND x.

`coorFibre` is the reading of `stdModelGen` and `nfGen` the reading of the opaque `stdThomGen`; the
two model generators differ by a *fixed* sign (`Work.ThomBordism.stdModelGen_pm_stdThomGen`, a
statement about the model pair `(ℝ^k, ℝ^k∖0)` alone, hence free of the cross-datum obstruction of
the last mile).  Consequently the `coorFibre`-form of the uniform fibre restriction *implies* the
`nfGen`-form (UF2) — with a *uniform* sign — and with `localDegree_universalThomClass_of_uniformF2`
above the target follows.

So the target depends on the single localisation statement `coorFibre_localDegreeClass_signed`: the
fibre reading of a local-degree class is the σ-corrected coorientation reference up to the universal
sign.  No frame half (A2) is needed for this route. -/

theorem localDegree_universalThomClass_of_uniformF2 (k : ℕ) (hk : 1 ≤ k)
    (hF2u : ∃ t : ℤ, (t = 1 ∨ t = -1) ∧
      ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
        (E : EmbeddingData V (8 + k))
        (ND : NormalData V k E.e)
        {ε : ℝ} (C : TubeChart E ε) (q : NormalSphSub E ε)
        (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
        (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
        (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (NormalTotal E)))
        (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
        (hg2 : ∀ y, y ∈ C.openTube →
          g (OnePoint.some y) = OnePoint.some (normalBlowUp E ε (C.inv y)))
        (U : Work.Thom.RelCoh ℤ k (TopCat.of (NormalTotal E)) (normalNonzero E)),
        IsLocalDegreeClass C g hg hR hbox U →
        ∀ x : V.pt, nfRes E x k U = t • nfGen hk E ND x) :
    ∃ u₀ : Work.Thom.ThomClass (Work.ThomBordism.Grassmann.tautologicalBundle k 10) k,
      ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
        (E : EmbeddingData V (8 + k))
        (ND : NormalData V k E.e)
        (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
          (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
        (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
          G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
        (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
          = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
        (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
          = Work.PTGeometric.padEuc k 10 (by norm_num)
              (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
        {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
        (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
        (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
        (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
        (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
        (hg2 : ∀ y, y ∈ C.openTube →
          g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))),
      Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox
        (Work.ThomBordism.gtdUWith E ND G hgm u₀) := by
  classical
  obtain ⟨s, hsm, hbr⟩ := Work.ThomBordism.branchSign_uniform_of_F2uniform k hk hF2u
  -- per datum, `s • gtdU` is the local-degree class
  have hkey : ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : EmbeddingData V (8 + k)) (ND : NormalData V k E.e)
      (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
      (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
        G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
      (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
        = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
      (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
        = Work.PTGeometric.padEuc k 10 (by norm_num)
            (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
      {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
      (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))),
      Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox
        (s • Work.ThomBordism.gtdU E ND G hgm) := by
    intro V _ E ND G hgm hbp hvec ε C q hU R hR hbox g hg hg2
    obtain ⟨Ugen, hspanUgen, hUgen⟩ :=
      Work.ThomBordism.localDegreeGenExists (V := V) (k := k) hk E C.eps_pos C q hU hR hbox g hg hg2
    have h1 : Work.ThomBordism.gtdU E ND G hgm = s • Ugen :=
      hbr E ND G hgm hbp hvec C q hU hR hbox g hg hg2 Ugen hUgen hspanUgen
    have h2 : s • Work.ThomBordism.gtdU E ND G hgm = Ugen := by
      rw [h1, smul_smul]
      rcases hsm with h | h <;> rw [h] <;> simp
    rw [h2]
    exact hUgen
  rcases hsm with h1 | h1
  · refine ⟨Work.ThomBordism.Grassmann.tautologicalThomClass k 10, ?_⟩
    intro V _ E ND G hgm hbp hvec ε C q hU R hR hbox g hg hg2
    have := hkey E ND G hgm hbp hvec C q hU hR hbox g hg hg2
    rw [h1, one_smul] at this
    rwa [Work.ThomBordism.gtdU_eq_gtdUWith] at this
  · refine ⟨Work.ThomBordism.ThomClass.neg
      (Work.ThomBordism.Grassmann.tautologicalThomClass k 10), ?_⟩
    intro V _ E ND G hgm hbp hvec ε C q hU R hR hbox g hg hg2
    have := hkey E ND G hgm hbp hvec C q hU hR hbox g hg hg2
    rw [h1, neg_one_zsmul] at this
    rw [Work.ThomBordism.gtdUWith_neg, ← Work.ThomBordism.gtdU_eq_gtdUWith]
    exact this

/-- **The coorientation reference is a fixed multiple of `nfGen`.**  `coorFibre` is the reading of
`stdModelGen` and `nfGen` the reading of `stdThomGen`; the two model generators differ by a fixed
sign (`hm`), so the same holds after the frame reading. -/
theorem exists_coorFibre_eq_smul_nfGen {k : ℕ} (hk : 1 ≤ k) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
        (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
        (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e) (x : V.pt),
        Work.ThomBordism.coorFibre hk E ND x = ε • Work.ThomBordism.nfGen hk E ND x := by
  obtain ⟨εm, hεm, hm'⟩ := Work.ThomBordism.stdModelGen_pm_stdThomGen k hk
  refine ⟨εm, hεm, ?_⟩
  intro V _inst E ND x
  rw [Work.ThomBordism.coorFibre_eq, Work.ThomBordism.nfGen_eq hk E ND x, hm']
  exact map_zsmul _ εm (Work.ThomBordism.stdThomGen k hk)

/-- **The UF2 form of the uniform fibre restriction, from the signed `coorFibre` form.** -/
theorem fibreRes_localDegreeClass_eq_nfGen_uniform_of_coorFibre (k : ℕ) (hk : 1 ≤ k)
    (hcoor : ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
      (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
      (U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)) (x : V.pt),
      Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox U →
      Work.ThomBordism.nfRes E x k U
        = (((-1 : ℤ) ^ (k * (k - 1) / 2)) • Work.ThomBordism.coorFibre (V := V) hk E ND x)) :
    ∃ t : ℤ, (t = 1 ∨ t = -1) ∧
      ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
        (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
        (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
        {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
        (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
        (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
        (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
        (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
        (hg2 : ∀ y, y ∈ C.openTube →
          g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
        (U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
          (Work.Tubular.normalNonzero E)),
        Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox U →
        ∀ x : V.pt, Work.ThomBordism.nfRes E x k U = t • Work.ThomBordism.nfGen hk E ND x := by
  obtain ⟨εm, hεm, hconv⟩ := exists_coorFibre_eq_smul_nfGen (k := k) hk
  refine ⟨((-1 : ℤ) ^ (k * (k - 1) / 2)) * εm, ?_, ?_⟩
  · have hpow : ((-1 : ℤ) ^ (k * (k - 1) / 2)) = 1 ∨ ((-1 : ℤ) ^ (k * (k - 1) / 2)) = -1 := by
      rcases Nat.even_or_odd (k * (k - 1) / 2) with h | h
      · exact Or.inl h.neg_one_pow
      · exact Or.inr h.neg_one_pow
    rcases hpow with hp | hp <;> rcases hεm with h2 | h2 <;> rw [hp, h2] <;> norm_num
  · intro V _inst E ND ε C q hU R hR hbox g hg hg2 U hUld x
    rw [hcoor E ND C q hU hR hbox g hg hg2 U x hUld, hconv E ND x, smul_smul]

/-- **The target follows from the signed `coorFibre` form of the uniform fibre restriction** — i.e.
from the single localisation statement `Work.ThomBordism.coorFibre_localDegreeClass_signed`
(together with the model comparison `hm`, a statement about `(ℝ^k, ℝ^k∖0)` alone). -/
theorem localDegree_universalThomClass_of_coorFibre (k : ℕ) (hk : 1 ≤ k)
    (hcoor : ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
      (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y)))
      (U : Work.Thom.RelCoh ℤ k (TopCat.of (Work.Tubular.NormalTotal E))
        (Work.Tubular.normalNonzero E)) (x : V.pt),
      Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox U →
      Work.ThomBordism.nfRes E x k U
        = (((-1 : ℤ) ^ (k * (k - 1) / 2)) • Work.ThomBordism.coorFibre (V := V) hk E ND x)) :
    ∃ u₀ : Work.Thom.ThomClass (Work.ThomBordism.Grassmann.tautologicalBundle k 10) k,
      ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
        (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
        (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
        (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
          (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
        (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
          G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
        (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
          = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
        (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
          = Work.PTGeometric.padEuc k 10 (by norm_num)
              (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
        {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
        (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
        (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
        (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
        (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
        (hg2 : ∀ y, y ∈ C.openTube →
          g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))),
      Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox
        (Work.ThomBordism.gtdUWith E ND G hgm u₀) :=
  localDegree_universalThomClass_of_uniformF2 k hk
    (fibreRes_localDegreeClass_eq_nfGen_uniform_of_coorFibre k hk hcoor)

/-- **The target follows from the *signed* canonical Gauss statement** — the second dispatch of the
sibling path (`canonicalGauss_isLocalDegreeClass_signed`): the ILD condition for the
`Mpun`-normalised canonical class, with the explicit sign `(-1)^{k(k-1)/2}`.  The global sign is
absorbed into the choice of `u₀` (`Ucan` or its negative), which is why the target — sign-blind — is
reachable from it. -/
theorem localDegree_universalThomClass_of_canonicalGauss_signed (k : ℕ) (hk : 1 ≤ k)
    (hcan : ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
      (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
      (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
      (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
        (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
      (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
        G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
      (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
        = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
      (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
        = Work.PTGeometric.padEuc k 10 (by norm_num)
            (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
      {ε' : ℝ} (C : Work.Tubular.TubeChart E ε') (q : Work.Tubular.NormalSphSub E ε')
      (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
      (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
      (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
      (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
      (hg2 : ∀ y, y ∈ C.openTube →
        g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε' (C.inv y))),
      Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox
        (((-1 : ℤ) ^ (k * (k - 1) / 2)) •
          Work.ThomBordism.gtdUWith E ND G hgm
            (Work.Thom.realThomClassOf hk
              (Work.ThomBordism.Grassmann.tautologicalBundle k 10)
              (tautologicalBundle_horiO k)))) :
    ∃ u₀ : Work.Thom.ThomClass (Work.ThomBordism.Grassmann.tautologicalBundle k 10) k,
      ∀ {V : Work.ThomBordism.Man8} [ConnectedSpace V.pt]
        (E : Work.ThomBordism.PontryaginThom.EmbeddingData V (8 + k))
        (ND : Work.ThomBordism.PontryaginThom.NormalData V k E.e)
        (G : C((Work.Tubular.normalBundle E ND).TotalSpace,
          (Work.ThomBordism.Grassmann.tautologicalBundle k 10).TotalSpace))
        (hgm : ∀ p ∈ Work.Thom.zeroComplement (Work.Tubular.normalBundle E ND),
          G p ∈ Work.Thom.zeroComplement (Work.ThomBordism.Grassmann.tautologicalBundle k 10))
        (hbp : ∀ p, (Work.ThomBordism.Grassmann.tautologicalBundle k 10).proj (G p)
          = Work.ThomBordism.Grassmann.padGaussFun E ND p.1)
        (hvec : ∀ p, Work.ThomBordism.Grassmann.evalVec (G p)
          = Work.PTGeometric.padEuc k 10 (by norm_num)
              (Work.Tubular.NormalTotal.vec (Work.Tubular.bundleToNormal E ND p)))
        {ε : ℝ} (C : Work.Tubular.TubeChart E ε) (q : Work.Tubular.NormalSphSub E ε)
        (hU : IsCompact C.U) {R : ℝ} (hR : 0 ≤ R)
        (hbox : ∀ y ∈ C.U, ∀ j : Fin (8 + k), |y j| < R)
        (g : C(OnePoint (Work.Tubular.Euc (8 + k)), OnePoint (Work.Tubular.NormalTotal E)))
        (hg : ∀ y, y ∉ C.openTube → g (OnePoint.some y) = OnePoint.infty)
        (hg2 : ∀ y, y ∈ C.openTube →
          g (OnePoint.some y) = OnePoint.some (Work.Tubular.normalBlowUp E ε (C.inv y))),
      Work.ThomBordism.IsLocalDegreeClass C g hg hR hbox
        (Work.ThomBordism.gtdUWith E ND G hgm u₀) := by
  rcases Nat.even_or_odd (k * (k - 1) / 2) with hpar | hpar
  · refine ⟨Work.Thom.realThomClassOf hk
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (tautologicalBundle_horiO k), ?_⟩
    intro V _inst E ND G hgm hbp hvec ε C q hU R hR hbox g hg hg2
    have := hcan E ND G hgm hbp hvec C q hU hR hbox g hg hg2
    rwa [hpar.neg_one_pow, one_smul] at this
  · refine ⟨Work.ThomBordism.ThomClass.neg (Work.Thom.realThomClassOf hk
      (Work.ThomBordism.Grassmann.tautologicalBundle k 10) (tautologicalBundle_horiO k)), ?_⟩
    intro V _inst E ND G hgm hbp hvec ε C q hU R hR hbox g hg hg2
    have := hcan E ND G hgm hbp hvec C q hU hR hbox g hg hg2
    rw [hpar.neg_one_pow, neg_one_zsmul] at this
    rw [Work.ThomBordism.gtdUWith_neg]
    exact this


end

end Work.ThomBordism
