import Submission.NK.NUV2.LC.RouteB.exists_muColim_avatar
import Submission.NK.CFTLib.hilbertReciprocityCyclicAux
import Submission.NK.CFTLib.IdeleHasse.Descent.localNormSubgroup_iff_cycClass_finite
import Submission.NK.NUV2.LC.RouteB.locLevel_levelCompareOfTop
import Submission.NK.NUV2.LC.finiteSupportTwistDefs
import Submission.NK.NUV2.LC.RouteB.localUnitsLevelMap_injective
import Submission.NK.NUV2.ABHN.muColimEquivH2ProfiniteOfIsPrimitiveRoot
import Submission.NK.NUV2.LC.RouteB.LocalGaloisImport

/-!
# Import wrapper (lean) for the localisation dictionary of `exists_cyclicClassColim`

Same as `DictionaryDeps`, but avoiding the volatile `HR`-transfer subtree.  The level-independence
of the vanishing of `locUnits` should here be derived from the tower square
`NK.NUV2.LC.RouteB.unitsLevelMapTower_comp_locUnits` (`locUnits_tower_eq_zero.lean`) together with
the injectivity `NK.NUV2.LC.RouteB.localUnitsLevelMap_injective`.
-/
