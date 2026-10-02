import Mathlib
import Submission.Work.ThomBordism.LeadChapter.CollarChartDefs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# S4 (`chapter_collarChart`): the collar chart of the level set at a piece

The topological content of `chapter_collarChart`: the open partial homeomorphism `ψ` of the level
model onto the collar `{z | z 0 < δ, tail z ∈ φᵢ.target}`, pinned by `ψ⁻¹ = collarPiece`, its
interior part `κ`, its boundary part `g`, and the identification of `g` with the piece chart.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open CategoryTheory Function Set Classical

namespace Work.ThomBordism.LeadChapter

open Work.PTGeometric

noncomputable section

variable {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
  {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]

section Core

variable (T : CollarData k D ι Fam)

/-- The open set of the boundary identification over the piece of the data. -/
abbrev TOfam : Set (SrcHS k) := Ofam T.G T.m T.hpow T.h T.a T.i

/-- The target of the collar chart. -/
abbrev TTgt : Set (EuclideanHalfSpace 9) := tgtC T.εcl T.a T.i

/-- **The source of the collar chart**: the points of the level set in the `δ`-collar whose downward
projection is identified with the piece `a` through the chart `i`. -/
def srcC : Set (DataLW T) :=
  {q | q.1.1.1 0 < deltaC T.εcl ∧ projPt (q.1.1) ∈ TOfam T}

theorem mem_srcC_iff {q : DataLW T} :
    q ∈ srcC T ↔ q.1.1.1 0 < deltaC T.εcl ∧ projPt (q.1.1) ∈ TOfam T := Iff.rfl

theorem isOpen_srcC : IsOpen (srcC T) := by
  have h1 : Continuous fun q : DataLW T => q.1.1.1 0 := by fun_prop
  have h2 : Continuous fun q : DataLW T => projPt (q.1.1) :=
    continuous_projPt.comp (by fun_prop : Continuous fun q : DataLW T => q.1.1)
  exact (isOpen_lt h1 continuous_const).inter ((isOpen_Ofam T.G T.m T.hpow T.h T.a T.i).preimage h2)

/-- The membership of the UaC-set in the range of `Sigma.mk`. -/
theorem UaC_mem_range {m : ℕ} {a : Fin m × ι}
    {i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)} {u : Σ c : Fin m × ι, (Fam c.2).pt}
    (hu : u ∈ UaC a i) : u ∈ Set.range (Sigma.mk a) := by
  obtain ⟨y, -, hyeq⟩ := hu
  exact ⟨y, hyeq⟩

/-- **The ambient coordinates of a point of the level set in the collar lie in the zero set.** -/
theorem mem_sourceZeroSet_ambient {q : DataLW T}
    (hq0 : q.1.1.1 0 < deltaC T.εcl) : q.1.1 ∈ sourceZeroSet T.G T.m T.hpow := by
  have hΦ : sourcePhi T.G T.m T.hpow T.hphi (q.1.1) ≤ 0 := q.1.2
  have hne : srcHf T.G T.m T.hpow (q.1.1.1) ≠ D.t₀ := by
    intro heq
    have hboth : q.1.1 ∈ {x : SrcHS k | sourcePhi T.G T.m T.hpow T.hphi x ≤ 0} ∩
        sourceBasepoint (D := D) (Fam := Fam) T.G T.m T.hpow := ⟨hΦ, heq⟩
    rw [(sourcePhi_spec T.G T.m T.hpow T.hphi).2.2.1] at hboth
    exact hboth
  have hv : vSrc T.G T.m T.hpow (q.1.1.1) = 0 := by
    rw [← T.hwv q.1 (le_trans (le_of_lt hq0) (deltaC_le_eps T.hεcl))]
    exact q.2
  rw [vSrc, dif_neg hne] at hv
  exact (T.G.core_iff_vec ⟨srcHf T.G T.m T.hpow (q.1.1.1), hne⟩).mpr hv

/-- **The downward projection of a point of the level set in the collar is a boundary zero.** -/
theorem projPt_mem_bdryDom {q : DataLW T} (hq0 : q.1.1.1 0 < deltaC T.εcl) :
    projPt (q.1.1) ∈ bdryDom T.G T.m T.hpow := by
  refine ⟨?_, projPt_apply_zero q.1.1⟩
  refine mem_sourceZeroSet_of_collarRay T.G T.m T.hpow
    (mem_sourceZeroSet_ambient T hq0) ?_ ?_ ?_
  · exact le_trans (le_of_lt hq0) (deltaC_le_half T.εcl)
  · intro j hj
    exact projPt_ofLp_ne_zero hj
  · rw [projPt_apply_zero]; norm_num

/-- **The piece point of a point of the source of the collar chart.** -/
def pieceOf (q : DataLW T) (hq : q ∈ srcC T) : (Fam T.a.2).pt :=
  fibreHomeo (Fam := Fam) T.a
    ⟨T.h ⟨projPt (q.1.1), projPt_mem_bdryDom T hq.1⟩,
      UaC_mem_range ((mem_Ofam_iff (projPt_mem_bdryDom T hq.1)).mp hq.2)⟩

theorem pieceOf_eq (q : DataLW T) (hq : q ∈ srcC T) :
    pieceOf T q hq = fibreHomeo (Fam := Fam) T.a
      ⟨T.h ⟨projPt (q.1.1), projPt_mem_bdryDom T hq.1⟩,
        UaC_mem_range ((mem_Ofam_iff (projPt_mem_bdryDom T hq.1)).mp hq.2)⟩ := rfl

theorem pieceOf_mem (q : DataLW T) (hq : q ∈ srcC T) :
    pieceOf T q hq ∈ (chartE T.a T.i).source := by
  have hx := projPt_mem_bdryDom T hq.1
  have hr := (mem_Ofam_iff hx).mp hq.2
  obtain ⟨y, hy, hyeq⟩ := hr
  have h1 : Sigma.mk T.a (pieceOf T q hq) = T.h ⟨projPt (q.1.1), hx⟩ :=
    fibreHomeo_mk (Fam := Fam) T.a _
  have h1' : (⟨T.a, pieceOf T q hq⟩ : Σ c : Fin T.m × ι, (Fam c.2).pt) = ⟨T.a, y⟩ :=
    h1.trans hyeq.symm
  have h5 : (⟨⟨T.a, pieceOf T q hq⟩, Set.mem_range_self (pieceOf T q hq)⟩ :
      ↥(Set.range (Sigma.mk (β := fun c : Fin T.m × ι => (Fam c.2).pt) T.a)))
      = ⟨⟨T.a, y⟩, Set.mem_range_self y⟩ := Subtype.ext h1'
  have h6 := congrArg (fibreHomeo (Fam := Fam) T.a) h5
  rw [fibreHomeo_apply T.a (pieceOf T q hq), fibreHomeo_apply T.a y] at h6
  rw [h6]; exact hy

/-- **The collar chart map.** -/
def toFunC (q : DataLW T) : EuclideanHalfSpace 9 :=
  if hq : q ∈ srcC T then
    hsCons (q.1.1.1 0) q.1.1.2 (chartE T.a T.i (pieceOf T q hq))
  else hsZero

theorem toFunC_apply (q : DataLW T) (hq : q ∈ srcC T) :
    toFunC T q = hsCons (q.1.1.1 0) q.1.1.2 (chartE T.a T.i (pieceOf T q hq)) := by
  rw [toFunC]
  exact dif_pos hq

theorem toFunC_apply_zero (q : DataLW T) (hq : q ∈ srcC T) :
    (toFunC T q).1 0 = q.1.1.1 0 := by
  rw [toFunC_apply T q hq, hsCons_apply_zero]

theorem tail_toFunC (q : DataLW T) (hq : q ∈ srcC T) :
    Work.PTGeometric.tail 8 (toFunC T q).1 =
      chartE T.a T.i (pieceOf T q hq) := by
  rw [toFunC_apply T q hq, tail_hsCons]

theorem toFunC_mem_tgtC (q : DataLW T) (hq : q ∈ srcC T) : toFunC T q ∈ TTgt T := by
  refine ⟨?_, ?_⟩
  · rw [toFunC_apply_zero T q hq]
    exact hq.1
  · rw [tail_toFunC T q hq]
    exact (chartE T.a T.i).map_source (pieceOf_mem T q hq)

/-- The downward projection of the collar lift is the boundary zero point. -/
theorem projPt_collarHS (z : EuclideanHalfSpace 9) :
    projPt (collarHS T z) = collBdry T z := by
  refine Subtype.ext ?_
  show Work.PTGeometric.tailVec (collarHS T z).1 = (collBdry T z).1
  rw [collarHS_coe, collarVec_tail']

/-- The boundary identification of the collar lift. -/
theorem h_collBdry (z : EuclideanHalfSpace 9) :
    T.h ⟨collBdry T z, collBdry_mem T z, collBdry_apply_zero T z⟩ =
      ⟨T.a, (chartE T.a T.i).symm (Work.PTGeometric.tail 8 z.1)⟩ := by
  refine (congrArg T.h (Subtype.ext (rfl : (collBdry T z : SrcHS k) = collBdry T z))).trans ?_
  exact T.h.apply_symm_apply ⟨T.a, (chartE T.a T.i).symm (Work.PTGeometric.tail 8 z.1)⟩

/-- **The collar lift of a point of the target lies in the source of the chart.** -/
theorem collarW_mem_srcC {z : EuclideanHalfSpace 9} (hz : z ∈ TTgt T) :
    collarW T z ∈ srcC T := by
  constructor
  · rw [collarW_apply_zero]
    rw [clampC_eq_self z.2 (le_trans (le_of_lt hz.1) (deltaC_le_min (le_of_lt T.hεcl)))]
    exact hz.1
  · have hproj : projPt ((collarW T z).1.1) = collBdry T z := by
      rw [collarW_coe, collarReg_coe]
      exact projPt_collarHS T z
    rw [hproj]
    exact (mem_Ofam_iff (x := collBdry T z)
      ⟨collBdry_mem T z, collBdry_apply_zero T z⟩).mpr (by
        rw [h_collBdry T z]
        exact ⟨(chartE T.a T.i).symm (Work.PTGeometric.tail 8 z.1),
          (chartE T.a T.i).map_target hz.2, rfl⟩)

end Core

end

end Work.ThomBordism.LeadChapter
