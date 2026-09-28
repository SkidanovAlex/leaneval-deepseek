import Mathlib
import Submission.Work.Serre.Csr.Defs
import Submission.Work.Serre.Csr.Base
import Submission.Work.Serre.Csr.Chain
import Submission.Work.Serre.Csr.Target
import Submission.Work.Serre.Csr.Transfer
import Submission.Work.Serre.Csr.DiscPair

/-!
# The two sides of the per-cell computation over `ℤ` and over `ℚ`

Collecting the pieces of the source-side computation: for a Serre fibration `q` over
`attachCells n Y ι f`, the relative singular homology of the pair `(q⁻¹o, q⁻¹(o ∖ {c}))` (over `ℤ`)
is the homology of the fibre of `q` over the centre `c`, shifted by `n+2`:

  `H_{k+n+2}(q⁻¹o, q⁻¹(o∖{c});ℤ) ≅ H_k(F_c;ℤ)`,

and it vanishes in degrees `< n+2`; and the same over `ℚ`, with the target side
`H_{n+2}(o, o∖{c};ℚ) ≅ ℚ` and `H_m(o, o∖{c};ℚ) = 0` for `m ≠ n+2`.
-/

set_option maxHeartbeats 1000000

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Serre.Csr

noncomputable section


/-! ## The source side over `ℤ` -/

/-- **The source side in positive degrees, over `ℤ`.** -/
theorem csrSourceIntIso (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (i : ι) (k : ℕ) :
    Nonempty (((Work.Cohomology.relChains (TopCat.of ↥(q ⁻¹' (csrOpenBall n Y ι f i)))
        {x : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) | (x : E) ∈ q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})}).homology (k + (n+2)))
      ≅ ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre q
          (csrCentre n Y ι f i)))).homology k)) := by
  obtain ⟨e1⟩ := csrSourceDiscIso n Y ι f q hq i k
  obtain ⟨e2⟩ := csrDiscChain f q hq i (1/4) (by norm_num) (by norm_num) (k + (n+2))
  obtain ⟨e3⟩ := csrTransferPair n Y ι f q i (k + (n+2))
  exact ⟨e3.symm ≪≫ e2 ≪≫ e1⟩

/-- **The source side below the dimension, over `ℤ`.** -/
theorem csrSourceInt_isZero (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (i : ι) (m : ℕ) (hm : m < n+2) :
    IsZero ((Work.Cohomology.relChains (TopCat.of ↥(q ⁻¹' (csrOpenBall n Y ι f i)))
        {x : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) | (x : E) ∈ q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})}).homology m) := by
  obtain ⟨e2⟩ := csrDiscChain f q hq i (1/4) (by norm_num) (by norm_num) m
  obtain ⟨e3⟩ := csrTransferPair n Y ι f q i m
  exact ((csrSourceDisc_isZero n Y ι f q hq i m hm).of_iso e2).of_iso e3.symm

/-! ## The source side over `ℚ` -/

/-- **The source side below the dimension, over `ℚ`.** -/
theorem csrSourceRat_isZero (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (i : ι) (m : ℕ) (hm : m < n+2) :
    IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of ↥(q ⁻¹' (csrOpenBall n Y ι f i)))
        {x : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) | (x : E) ∈ q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})}).homology m) :=
  isZero_relChainsR_rat_of_isZero_int _ _ m (csrSourceInt_isZero n Y ι f q hq i m hm)

/-- **The source side in degree `n+2`, over `ℚ`.** -/
theorem csrSourceRat_iso_ratUnit (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) {E : Type} [TopologicalSpace E]
    (q : C(E, Work.RatHurewicz.attachCells n Y ι f)) (hq : Work.StemsB.IsSerreFibration q)
    (i : ι)
    (h0 : Nonempty ((Work.Cohomology.singularChains ℚ (TopCat.of (Work.StemsB.fibre q
        (csrCentre n Y ι f i)))).homology 0 ≅ ModuleCat.of ℚ ℚ)) :
    Nonempty (((Work.StemsB.relChainsR ℚ (TopCat.of ↥(q ⁻¹' (csrOpenBall n Y ι f i)))
        {x : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) | (x : E) ∈ q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})}).homology (n+2)) ≅ ModuleCat.of ℚ ℚ) := by
  obtain ⟨eZ⟩ := csrSourceIntIso n Y ι f q hq i 0
  obtain ⟨eQ⟩ := relChainsRHomologyIsoRat (TopCat.of ↥(q ⁻¹' (csrOpenBall n Y ι f i)))
    {x : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) | (x : E) ∈ q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})} (n+2)
  have h1 : ((Work.Cohomology.relChains (TopCat.of ↥(q ⁻¹' (csrOpenBall n Y ι f i)))
      {x : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) | (x : E) ∈ q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})}).homology (n+2)) ≅
      ((Work.Cohomology.singularChains ℤ (TopCat.of (Work.StemsB.fibre q
        (csrCentre n Y ι f i)))).homology 0) :=
    (eqToIso (congrArg (fun k => (Work.Cohomology.relChains
      (TopCat.of ↥(q ⁻¹' (csrOpenBall n Y ι f i))) {x : ↥(q ⁻¹' (csrOpenBall n Y ι f i)) | (x : E) ∈ q ⁻¹' (csrOpenBall n Y ι f i \ {csrCentre n Y ι f i})}).homology k)
      (Nat.zero_add (n+2)))).symm ≪≫ eZ
  obtain ⟨eF⟩ := absHomologyIsoRat (TopCat.of (Work.StemsB.fibre q (csrCentre n Y ι f i))) 0
  exact ⟨eQ ≪≫ Work.StemsB.IntRatF.mapIso h1 ≪≫ eF.symm ≪≫ h0.some⟩

/-! ## The target side over `ℚ` -/

/-- **The target side away from degree `n+2`, over `ℚ`.** -/
theorem csrTargetRat_isZero (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) (m : ℕ) (hm : m ≠ n+2) :
    IsZero ((Work.StemsB.relChainsR ℚ (TopCat.of ↥(csrOpenBall n Y ι f i))
        {x : ↥(csrOpenBall n Y ι f i) | (x : Work.RatHurewicz.attachCells n Y ι f) ∈ csrOpenBall n Y ι f i \ {csrCentre n Y ι f i}}).homology m) :=
  isZero_relChainsR_rat_of_isZero_int _ _ m ((csrTargetPair n Y ι f i).1 m hm)

/-- **The target side in degree `n+2`, over `ℚ`.** -/
theorem csrTargetRat_iso_ratUnit (n : ℕ) (Y : Type) [TopologicalSpace Y] (ι : Type)
    (f : ι → C(Work.RatHurewicz.cellSphere n, Y)) (i : ι) :
    Nonempty (((Work.StemsB.relChainsR ℚ (TopCat.of ↥(csrOpenBall n Y ι f i))
        {x : ↥(csrOpenBall n Y ι f i) | (x : Work.RatHurewicz.attachCells n Y ι f) ∈ csrOpenBall n Y ι f i \ {csrCentre n Y ι f i}}).homology (n+2)) ≅ ModuleCat.of ℚ ℚ) :=
  relChainsR_homology_iso_ratUnit _ _ (n+2) (csrTargetPair n Y ι f i).2

end

end Work.Serre.Csr
