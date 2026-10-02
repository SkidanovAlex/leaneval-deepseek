import Submission.Work.LerayHirsch.CohMap_projMap_injective_of_LerayHirschFull
import Submission.Work.LerayHirsch.FibreBasis
import Submission.Work.LerayHirsch.FibreBasisOdd
import Submission.Work.LerayHirsch.FibreIso
import Submission.Work.LerayHirsch.FibreRestrict
import Submission.Work.LerayHirsch.FibreRestrictIso
import Submission.Work.LerayHirsch.FibreZeta
import Submission.Work.LerayHirsch.FibreZetaPow
import Submission.Work.LerayHirsch.FlagBundle
import Submission.Work.LerayHirsch.LH
import Submission.Work.LerayHirsch.LhGlueDefs
import Submission.Work.LerayHirsch.LhTermFibre
import Submission.Work.LerayHirsch.LhTwoCoverDefs
import Submission.Work.LerayHirsch.LineSum
import Submission.Work.LerayHirsch.Main
import Submission.Work.LerayHirsch.MvPieceIso
import Submission.Work.LerayHirsch.MvPieceTranslate
import Submission.Work.LerayHirsch.MvSquares
import Submission.Work.LerayHirsch.MvTM_translate
import Submission.Work.LerayHirsch.Mv_exact
import Submission.Work.LerayHirsch.Naturality
import Submission.Work.LerayHirsch.ProjIsoOfBundleIso
import Submission.Work.LerayHirsch.Punctum
import Submission.Work.LerayHirsch.Series
import Submission.Work.LerayHirsch.SplitLines
import Submission.Work.LerayHirsch.SplitsOverProj
import Submission.Work.LerayHirsch.Splitting
import Submission.Work.LerayHirsch.TautEmbedCore
import Submission.Work.LerayHirsch.TautLine
import Submission.Work.LerayHirsch.TautTwist
import Submission.Work.LerayHirsch.Twist
import Submission.Work.LerayHirsch.TwistCongr
import Submission.Work.LerayHirsch.TwistSection
import Submission.Work.LerayHirsch.TwistSumDefs
import Submission.Work.LerayHirsch.TwistUnit
import Submission.Work.LerayHirsch.WhitneyParacompact
import Submission.Work.LerayHirsch.WhitneySumAssoc
import Submission.Work.LerayHirsch.WhitneySumSnd
import Submission.Work.LerayHirsch.exists_homeo_projSpace_bundleComap_homeo
import Submission.Work.LerayHirsch.exists_punctTrivHomeo
import Submission.Work.LerayHirsch.exists_quotientBundle_descend
import Submission.Work.LerayHirsch.exists_smulPunct_of_chartCoord_eq_smul
import Submission.Work.LerayHirsch.exists_tautSection
import Submission.Work.LerayHirsch.bijective_lhMap_fibre_of_trivCore
import Submission.Work.LerayHirsch.fibreMap_bijective
import Submission.Work.LerayHirsch.kunnethCP_of_trivialBundles
import Submission.Work.LerayHirsch.lerayHirschFull_of_bundleIso
import Submission.Work.LerayHirsch.lerayHirschFull_of_isEmpty
import Submission.Work.LerayHirsch.lerayHirschFull_of_two_cover
import Submission.Work.LerayHirsch.lerayHirschGlue
import Submission.Work.LerayHirsch.lerayHirschGlueProof
import Submission.Work.LerayHirsch.lerayHirsch_of_kunnethCP
import Submission.Work.LerayHirsch.lerayHirsch_of_rank_one
import Submission.Work.LerayHirsch.lhAny_bijective_iff
import Submission.Work.LerayHirsch.lhAny_glue_comap
import Submission.Work.LerayHirsch.lhEven_of_pullback_bijective
import Submission.Work.LerayHirsch.lhMap_comap
import Submission.Work.LerayHirsch.lhOdd_of_pullback_bijective
import Submission.Work.LerayHirsch.localTriv_tautSectionVec
import Submission.Work.LerayHirsch.mv2_components
import Submission.Work.LerayHirsch.mv2_exact
import Submission.Work.LerayHirsch.nonempty_bundleIso_of_gauge_fibre_indexAt
import Submission.Work.LerayHirsch.nonempty_bundleIso_of_gauge_fibre_map
import Submission.Work.LerayHirsch.nonempty_bundleIso_tautLine_comap
import Submission.Work.LerayHirsch.nonempty_bundleIso_twist_dual
import Submission.Work.LerayHirsch.nonempty_bundleIso_twist_whitneySum
import Submission.Work.LerayHirsch.nonempty_homeo_projFibre
import Submission.Work.LerayHirsch.nonempty_homeo_projSpace_bundleComap_subtype
import Submission.Work.LerayHirsch.nonempty_homeo_projSpace_trivial
import Submission.Work.LerayHirsch.paracompactSpace_projSpace
import Submission.Work.LerayHirsch.t2Space_projSpace
import Submission.Work.LerayHirsch.tautLine_bundleIso_of_projIso
import Submission.Work.LerayHirsch.tautologicalEmbedding
import Submission.Work.LerayHirsch.whitneySumFormulaOfLerayHirsch
import Submission.Work.LerayHirsch.whitneySumFormulaPar_one_of_splitLines
import Submission.Work.LerayHirsch.whitneySumFormula_one_one_of_topClassMul
import Submission.Work.LerayHirsch.zetaPow_comap
import Submission.Work.LerayHirsch.MvAux.BiprodElem
import Submission.Work.LerayHirsch.MvAux.HonestDegree
import Submission.Work.LerayHirsch.MvAux.IsoSquare
import Submission.Work.LerayHirsch.MvAux.Ladder

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# SUBPROJECT LERAYHIRSCH: the projectivisation and the splitting principle

Single entry point: `import Submission.Work.LerayHirsch.Chapter`.

* `Punctum.lean` — the projectivisation `P(E) = (E∖0)/ℂˣ` of a complex gluing-data bundle, its
  projection `π : P(E) → B`, the chart coordinates, and the fibre `π^{-1}(b) = ℂP^{m-1}`.
* `TautLine.lean` — the tautological line bundle `ℓ ⊆ π^*E` as gluing data over `P(E)`, and the
  hyperplane class `ζ = c₁(ℓ) ∈ H²(P(E);ℤ)`.
* `LH.lean` — the Leray–Hirsch statement `LerayHirsch Z` (`H^*(P(E))` free over `H^*(B)` on
  `1, ζ, …, ζ^{m-1}`), its two named inputs `KunnethCP` (the trivial case, subproject KUNNETH) and
  `LerayHirschGlue` (the Mayer–Vietoris step), and the consequences.
* `Splitting.lean` — the Chern calculus of `ℓ`, the geometric splitting `π^*E ≅ ℓ ⊕ Q`
  (`SplitsOverProj`), the flag-bundle splitting principle, and the relation to the Whitney formula
  of `Submission/Work/Whitney/`.
* `TwistSection.lean`, `exists_tautSection.lean`, `localTriv_tautSectionVec.lean`, `TwistUnit.lean`,
  `TwistCongr.lean`, `WhitneySumSnd.lean`, `SplitsOverProj.lean` — the proof of the splitting
  principle: the tautological nowhere-zero section of `ℓ^* ⊗ π^*E`, the chart computation that makes
  Whitney's complement re-presentable over the cover `ι × Fin (m+1)` of `ℓ`, the functoriality and
  unit law of the twist, and **`Work.LerayHirsch.splitsOverProj_of_paracompact : SplitsOverProj Z`**
  over a paracompact Hausdorff base.
* `kunnethCP_of_trivialBundles.lean` — the bridge from the trivial-bundle form of Künneth
  (subproject KUNNETH) to `KunnethCP`, the single remaining input of Leray–Hirsch.
-/
