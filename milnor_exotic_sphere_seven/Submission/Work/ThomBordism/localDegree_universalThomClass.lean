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
import Submission.Work.ThomBordism.localDegree_universalThomClass_bridge
import Submission.Work.ThomBordism.localDegree_localisation
import Submission.Work.ThomBordism.ambientFibreComparison
import Submission.Work.ThomBordism.coorFibre_fibreGenerator

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
# The universal Thom class of the tautological bundle, and the local degree

**Goal.**  `Work.ThomBordism.localDegree_universalThomClass`: there is a single Thom class `u₀` of the
tautological oriented bundle `γ_{k,10}` such that for **every** datum (closed oriented `8`-manifold
`V`, embedding `E : V ↪ ℝ^{8+k}`, normal data, Gauss candidate `G` pinned by the plane and vector
clauses, tube chart, collapse data) the pullback class `gtdUWith E ND G hgm u₀` implements the local
degree of the datum:

  `⟨x ⌣ gtdUWith …, c_C⟩ = ⟨z^*x, V.c⟩`  for all `x ∈ H⁸(ν)`.

**What this file does.**  It reduces the goal to the *uniform fibre-restriction statement* (F2u)

  `∃ t ∈ {±1}, ∀ (data) (U) (IsLocalDegreeClass U) (x), nfRes E x k U = t • nfGen hk E ND x`

(`Work.ThomBordism.fibreRes_localDegreeClass_eq_nfGen_uniform`); the reduction is
`localDegree_universalThomClass_of_uniformF2` below, and it combines

* `Work.ThomBordism.branchSign_uniform_of_F2uniform` (PROVED) — the uniform F2 gives a single sign
  `s = ±1` with `gtdU E ND G hgm = s • U` for every datum and every *generating* local-degree class,
* `Work.ThomBordism.localDegreeGenExists` (PROVED) — a generating local-degree class exists for
  every datum (`C.eps_pos` supplies the strict positivity of the tube radius), and
* `Work.ThomBordism.gtdUWith`/`ThomClass.neg` (PROVED) — the class-level form of the tautological
  Thom class: `gtdU = gtdUWith τ` and `gtdUWith (-τ) = - gtdU`.

The remaining mathematical input — the *uniformity* of the sign `t` of the fibre restriction of a
local-degree class across the data — is exactly the last-mile normalisation of the Gauss chapter
(see `Submission/Work/ThomBordism/NOTE_TIE_POLARITY.md` §7–§11 and `NOTE_SESSION39.md` §3.8); it is
*not* implied by the per-datum disjunction `Work.ThomBordism.gtdU_localDegreeExists`, because the
per-datum signs are not related by any lemma of the tree.
-/

/-! ## The reduction to three independent pieces (session 43)

`Submission/Work/ThomBordism/localDegree_localisation.lean` (this session) proves

    localDegree_universalThomClass_of_pieces :
      PieceA k → PieceP1 k → PieceP2 k hk → localDegree_universalThomClass k hk

where the three pieces (each *strictly weaker* than the target, and independent of the others) are

* **(A) `PieceA k`** — `∃ w : H⁸(ν), ⟨(zeroSection)^* w, V.c⟩ = 1`; dispatched as
  `Work.ThomBordism.exists_zeroSection_pairing_one`;
* **(P1) `PieceP1 k`** — *the localisation*: for such a `w` there is a **generator** `z` of the fibre
  pair `(ν_x, ν_x∖0)` with `⟨nfRes E x k U, z⟩ = ⟨(w ⌣ U), collapseRelK8⟩` for **all** `U`
  (equivalently: the fibre reading of a local-degree class is the geometric fibre fundamental class
  of the collapse class); dispatched as `Work.ThomBordism.fibreReading_collapseClass`;
* **(P2) `PieceP2 k hk`** — *the coorientation comparison* / the sign: the pairing of the
  coorientation reference `coorFibre hk E ND x` with that `z` is a **single** `t = ±1`, the same for
  every datum; dispatched as `Work.ThomBordism.coorFibre_fibreGenerator`.

  **WARNING (session 43).**  `Submission/Work/ThomBordism/coorFibre_fibreGenerator.lean` has no
  literal `sorry`, but its `Work.ThomBordism.coorFibre_fibreGenerator` carries **`sorryAx`**
  (`#print axioms` shows it): it proves `coorFibre_fibreGenerator_of_uniformF2 : UF2 → (P2)` and then
  applies it to the *already-sorry-carrying*
  `Work.ThomBordism.fibreRes_localDegreeClass_eq_nfGen_uniform`, so it proves nothing beyond the
  known equivalence `(P2) ⟺ UF2`.  **Do not wire the target with it** — the resulting proof would not
  be axiom-clean.  The clean route to (P2) is the project lead's round-47 CLA chain:
  `Work.ThomBordism.collapseLocalisation_ambientV2` (whose only gap is `UniformLocalClass k`, being
  worked on in `NOTE_AMBIENTV2_PLAN5.md`) together with the model contraction (d) and
  `Work.ThomBordism.sigmaTelescope_gauss` (TEL), see `NOTE_SESSION43_LOCALISATION.md`.  `(A)` and
  `(P1)` *are* axiom-clean: `Work.ThomBordism.exists_zeroSection_pairing_one` and
  `Work.ThomBordism.fibreReading_collapseClass` (`{propext, Classical.choice, Quot.sound}`).

The mathematical content of **(P2)** (the only piece that is *not* a purely homological
generality): the collapse class of the tube is, near the zero section, the *tube chart*, i.e. the
ambient identity composed with the radial blow-up `normalBlowUp E ε` (whose fibre differential at
the zero section is `1`, `blowCoeff E ε p = 1` at `vec p = 0`); hence its fibre orientation is the
*ambient* orientation of the normal space, which by **TEL**
(`Work.ThomBordism.sigmaTelescope_gauss`) is the σ-corrected Gauss frame `gframe` up to the
chart-independent sign carried by `σ` (`Work.ThomBordism.frameChange_det_eq_sigmaFS`).  So `t` is a
*convention* constant (the `Mpun`-versus-classical normalisation of the model pair
`(ℝ^k, ℝ^k∖0)`), independent of the datum — which is exactly what (P2) asserts.

All three pieces are now PROVED and axiom-clean:

* (A) `Work.ThomBordism.exists_zeroSection_pairing_one` (instantiated as `Work.ThomBordism.pieceA`),
* (P1) `Work.ThomBordism.fibreReading_collapseClass` (instantiated as `Work.ThomBordism.pieceP1`),
* (P2) `Work.ThomBordism.coorFibre_fibreGenerator`, closed along the project lead's round-48 route
  `KeyLocal ∧ (CLA) ⟹ (P2)`, with `Work.ThomBordism.KeyLocal` proved in
  `Submission/Work/ThomBordism/keyLocal.lean` and the ambient uniformisation `(CLA)`
  (`Work.ThomBordism.collapseLocalisation_ambientV2`) PROVED in
  `Submission/Work/ThomBordism/collapseLocalisation_ambientV2.lean`.

The assembly used below is therefore

    exact localDegree_universalThomClass_of_pieces k hk (pieceA k) (pieceP1 k hk)
      (coorFibre_fibreGenerator k hk)

packaged as `Work.ThomBordism.localDegree_universalThomClass_of_p2` in
`Submission/Work/ThomBordism/ambientFibreComparison.lean`, which also records the two equivalent
single-input reductions `..._of_keyLocal` and `..._of_link` (via
`Work.ThomBordism.ambientFibreLink_of_keyLocalPinned`). -/

/-- **The target follows from the uniform fibre-restriction statement (the uniform F2).** -/
theorem localDegree_universalThomClass (k : ℕ) (hk : 1 ≤ k) :
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
  -- The fibre-restriction uniformity `PieceP2` (= `Work.ThomBordism.coorFibre_fibreGenerator`,
  -- proved through the project lead's `KeyLocal` route) closes the three-piece assembly.
  Work.ThomBordism.localDegree_universalThomClass_of_p2 k hk
    (Work.ThomBordism.coorFibre_fibreGenerator k hk)

end

end Work.ThomBordism
