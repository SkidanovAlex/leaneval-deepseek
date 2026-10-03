/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Bass--Serre theory: the interface

Import this module to get the whole `Work.ORBassSerre` area: graphs and trees, group actions on
graphs, quotient graphs, convex subsets, the cocompact-invariant-subtree result, JL Lemma 4.1,
the Nielsen--Schreier/Bass--Serre "free action on a tree" result, and the finite-presentability
results for amalgamated products and HNN extensions.

See `Submission/Work/ORBassSerre/README.md` for a guide.
-/
import Submission.Work.ORBassSerre.Tree.Basic
import Submission.Work.ORBassSerre.Tree.Convex
import Submission.Work.ORBassSerre.Tree.Convex.isConvexSet_hull
import Submission.Work.ORBassSerre.Tree.Convex.isTree_subtype
import Submission.Work.ORBassSerre.Tree.IsTreeAPI
import Submission.Work.ORBassSerre.Tree.Geodesic.qpath_eq_of_isTree
import Submission.Work.ORBassSerre.Tree.Junction.qpath_exists_cons_of_deleteBacktrack_comp
import Submission.Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced
import Submission.Work.ORBassSerre.Tree.Map.qpath_mapPath_reverse
import Submission.Work.ORBassSerre.Tree.Prefix.qpath_exists_eq_comp_of_comp_eq
import Submission.Work.ORBassSerre.Tree.Reduction.qpath_exists_isReduced
import Submission.Work.ORBassSerre.Tree.Reduction.qpath_exists_reducesTo_isReduced
import Submission.Work.ORBassSerre.Tree.Reduction.qpath_vertices_subset_of_reducesTo
import Submission.Work.ORBassSerre.Tree.Subgraph.qpath_exists_restrict
import Submission.Work.ORBassSerre.Action.Basic
import Submission.Work.ORBassSerre.Action.Cocompact
import Submission.Work.ORBassSerre.Action.Quotient
import Submission.Work.ORBassSerre.Action.Quotient.qpath_exists_lift
import Submission.Work.ORBassSerre.Action.QuotientReverse
import Submission.Work.ORBassSerre.Action.exists_invariant_cocompact_subtree
import Submission.Work.ORBassSerre.Action.isFinitelyPresented_of_isCocompact_tree
import Submission.Work.ORBassSerre.Action.fg_of_isCocompact_tree
import Submission.Work.ORBassSerre.Action.isFreeGroup_of_actsFreely_on_tree
import Submission.Work.ORBassSerre.Action.isTree_orbitV_of_normalClosure_elliptic
import Submission.Work.ORBassSerre.FP.hnn_isFinitelyPresented
import Submission.Work.ORBassSerre.FP.pushoutI_isFinitelyPresented
