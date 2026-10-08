/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: PSTAB area (fundmath3-gorenstein_walter)
-/
import Submission.OddOrder.GroupTheory.ChiefFactor
import Submission.OddOrder.GroupTheory.ElementaryAbelian
import Submission.OddOrder.GroupTheory.PRank
import Submission.OddOrder.Isaacs.Ch02_Subnormality.Main
import Submission.OddOrder.Isaacs.Ch03_SplitExtensions.Basic
import Submission.OddOrder.BG.Ch1_Preliminary.OperatorMaschke

/-!
# PSTAB: imports needed by the `p`-stability (Glauberman L6.3) chain

Aggregator module so that the lemmas of the area `PSTAB` can be requested with a single
`depends_on`, and so that the area's files do not each have to spell out the (fixed, third-party)
`Submission.OddOrder.**` modules they sit on.  Contains no declarations.
-/
