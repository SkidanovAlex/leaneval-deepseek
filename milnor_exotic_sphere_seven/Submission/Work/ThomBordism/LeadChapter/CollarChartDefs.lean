import Mathlib
import Submission.Work.ThomBordism.LeadChapter.Defs
import Submission.Work.PTGeometric.LevelModel
import Submission.Work.PTGeometric.SourceRegionSetupBasic
import Submission.Work.PTGeometric.mem_sourceZeroSet_of_collarRay
import Submission.Work.ThomBordism.PosAtlas.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# S4 (`chapter_collarChart`): the definitions

The collar chart of the level set at a piece, as requested in `S4_guidance.md`.  This file contains
ONLY the definitions (and their elementary lemmas); the theorem `chapter_collarChart` itself is in
`Submission/Work/ThomBordism/LeadChapter/chapter_collarChart.lean`.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open CategoryTheory Function Set

namespace Work.ThomBordism.LeadChapter

open Work.PTGeometric

noncomputable section

/-! ## (0) The ambient half-space and the head/tail split of `ℝ⁹` -/

/-- The ambient half-space of the source construction. -/
abbrev SrcHS (k : ℕ) : Type := EuclideanHalfSpace ((8 + k) + 1)

/-- The ambient vector space of the source construction. -/
abbrev SrcVS (k : ℕ) : Type := EuclideanSpace ℝ (Fin ((8 + k) + 1))

/-- The vector of `ℝ⁹` with `0`-th coordinate `t` and tail `u`. -/
def euCons (t : ℝ) (u : EuclideanSpace ℝ (Fin 8)) : EuclideanSpace ℝ (Fin 9) :=
  (EuclideanSpace.equiv (Fin 9) ℝ).symm (Fin.cons t (fun i => u i))

theorem euCons_zero (t : ℝ) (u : EuclideanSpace ℝ (Fin 8)) : euCons t u 0 = t := by
  simp [euCons]

theorem tail_euCons (t : ℝ) (u : EuclideanSpace ℝ (Fin 8)) :
    Work.PTGeometric.tail 8 (euCons t u) = u := by
  ext i
  simp [euCons, Work.PTGeometric.tail_apply]

theorem euCons_tail_self (z : EuclideanSpace ℝ (Fin 9)) :
    euCons (z 0) (Work.PTGeometric.tail 8 z) = z := by
  refine (EuclideanSpace.equiv (Fin 9) ℝ).injective ?_
  show (EuclideanSpace.equiv (Fin 9) ℝ) (euCons (z 0) (Work.PTGeometric.tail 8 z))
      = (EuclideanSpace.equiv (Fin 9) ℝ) z
  rw [show (EuclideanSpace.equiv (Fin 9) ℝ) (euCons (z 0) (Work.PTGeometric.tail 8 z))
      = Fin.cons (z 0) (fun i => (Work.PTGeometric.tail 8 z) i) from
      (EuclideanSpace.equiv (Fin 9) ℝ).apply_symm_apply _]
  funext i
  refine Fin.cases ?_ ?_ i <;> simp [Work.PTGeometric.tail_apply]

theorem continuous_euCons :
    Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin 8) => euCons p.1 p.2) := by
  change Continuous (fun p : ℝ × EuclideanSpace ℝ (Fin 8) =>
      (EuclideanSpace.equiv (Fin 9) ℝ).symm (Fin.cons p.1 (fun i => p.2 i)))
  fun_prop

/-- The point of the half-space `ℝ⁹` with `0`-th coordinate `t ≥ 0` and tail `u`. -/
def hsCons (t : ℝ) (ht : 0 ≤ t) (u : EuclideanSpace ℝ (Fin 8)) : EuclideanHalfSpace 9 :=
  ⟨euCons t u, by rw [euCons_zero]; exact ht⟩

theorem hsCons_apply_zero (t : ℝ) (ht : 0 ≤ t) (u : EuclideanSpace ℝ (Fin 8)) :
    (hsCons t ht u).1 0 = t := by
  simp [hsCons, euCons_zero]

theorem tail_hsCons (t : ℝ) (ht : 0 ≤ t) (u : EuclideanSpace ℝ (Fin 8)) :
    Work.PTGeometric.tail 8 (hsCons t ht u).1 = u := by
  simp [hsCons, tail_euCons]

theorem eq_hsCons (z : EuclideanHalfSpace 9) :
    hsCons (z.1 0) z.2 (Work.PTGeometric.tail 8 z.1) = z := by
  refine Subtype.ext ?_
  exact euCons_tail_self z.1

theorem hsCons_eq_iff {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') {u u' : EuclideanSpace ℝ (Fin 8)} :
    hsCons t ht u = hsCons t' ht' u' ↔ t = t' ∧ u = u' := by
  constructor
  · intro h
    exact ⟨by simpa [hsCons_apply_zero] using congrArg (fun v => v.1 0) h,
      by simpa [tail_hsCons] using congrArg (fun v => Work.PTGeometric.tail 8 v.1) h⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- The zero of the half-space `ℝ⁹`. -/
def hsZero : EuclideanHalfSpace 9 := hsCons 0 (le_refl 0) 0

theorem hsZero_zero : (hsZero : EuclideanHalfSpace 9).1 0 = 0 := hsCons_apply_zero 0 _ _

/-- The `ℝ⁹`-point with `0`-th coordinate `0` and tail `u`. -/
def hsTail (u : EuclideanSpace ℝ (Fin 8)) : EuclideanHalfSpace 9 := hsCons 0 (le_refl 0) u

theorem hsTail_apply_zero (u : EuclideanSpace ℝ (Fin 8)) : (hsTail u).1 0 = 0 :=
  hsCons_apply_zero 0 _ _

theorem tail_hsTail (u : EuclideanSpace ℝ (Fin 8)) :
    Work.PTGeometric.tail 8 (hsTail u).1 = u := tail_hsCons 0 _ u

theorem eq_hsTail {z : EuclideanHalfSpace 9} (h : z.1 0 = 0) :
    hsTail (Work.PTGeometric.tail 8 z.1) = z := by
  have h1 : hsTail (Work.PTGeometric.tail 8 z.1) =
      hsCons (z.1 0) z.2 (Work.PTGeometric.tail 8 z.1) := by
    refine Subtype.ext ?_
    show euCons 0 (Work.PTGeometric.tail 8 z.1) = euCons (z.1 0) (Work.PTGeometric.tail 8 z.1)
    rw [h]
  exact h1.trans (eq_hsCons z)

/-! ## (1) The fibre of the sigma type of pieces -/

section Fibre

/-- **The fibre of the piece-indexed sigma type**, as a homeomorphism. -/
def fibreHomeo {m : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (a : Fin m × ι) :
    ↥(Set.range (Sigma.mk (β := fun c : Fin m × ι => (Fam c.2).pt) a)) ≃ₜ
      (Fam a.2).pt :=
  ((Topology.IsOpenEmbedding.sigmaMk
    (σ := fun c : Fin m × ι => (Fam c.2).pt) (i := a)).isEmbedding.toHomeomorph).symm

theorem fibreHomeo_apply {m : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (a : Fin m × ι) (y : (Fam a.2).pt) :
    fibreHomeo (Fam := Fam) a ⟨⟨a, y⟩, Set.mem_range_self y⟩ = y := by
  have hf : Topology.IsEmbedding (Sigma.mk (β := fun c : Fin m × ι => (Fam c.2).pt) a) :=
    (Topology.IsOpenEmbedding.sigmaMk (σ := fun c : Fin m × ι => (Fam c.2).pt) (i := a)).isEmbedding
  have h := Topology.IsEmbedding.toHomeomorph_symm_apply hf y
  have he : (⟨⟨a, y⟩, Set.mem_range_self y⟩ :
      ↥(Set.range (Sigma.mk (β := fun c : Fin m × ι => (Fam c.2).pt) a)))
      = ⟨Sigma.mk a y, _⟩ := Subtype.ext rfl
  rw [show fibreHomeo (Fam := Fam) a = (hf.toHomeomorph).symm from rfl, he, h]

theorem fibreHomeo_mk {m : ℕ} {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8}
    (a : Fin m × ι)
    (s : ↥(Set.range (Sigma.mk (β := fun c : Fin m × ι => (Fam c.2).pt) a))) :
    Sigma.mk a (fibreHomeo (Fam := Fam) a s) = s.1 := by
  have hf : Topology.IsEmbedding (Sigma.mk (β := fun c : Fin m × ι => (Fam c.2).pt) a) :=
    (Topology.IsOpenEmbedding.sigmaMk (σ := fun c : Fin m × ι => (Fam c.2).pt) (i := a)).isEmbedding
  exact congrArg Subtype.val (Homeomorph.apply_symm_apply hf.toHomeomorph s)

end Fibre

/-! ## (2) The boundary identification domain and the collar projection -/

variable {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
  {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]

/-- **The domain of the boundary identification**: the boundary zeros of the source homotopy. -/
def bdryDom (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) : Set (SrcHS k) :=
  sourceZeroSet G m hpow ∩ {x : SrcHS k | x.1 0 = 0}

/-- **The downward collar projection**: the point of the boundary hyperplane with the same
coordinates off the `0`-th one. -/
def projPt (x : SrcHS k) : SrcHS k := ⟨tailVec x.1, by rw [tailVec_apply_zero]⟩

theorem projPt_coe (x : SrcHS k) : (projPt x).1 = tailVec x.1 := rfl

theorem projPt_apply_zero (x : SrcHS k) : (projPt x).1 0 = 0 := by
  rw [projPt_coe, tailVec_apply_zero]

theorem projPt_ofLp_ne_zero {x : SrcHS k} {j : Fin ((8 + k) + 1)} (hj : j ≠ 0) :
    (projPt x).1 j = x.1 j := by
  rw [projPt_coe, tailVec_ofLp_ne_zero hj]

theorem continuous_projPt : Continuous (@projPt k) := by
  exact Continuous.subtype_mk (f := fun x : SrcHS k => tailVec x.1)
    (continuous_tailVec.comp continuous_subtype_val) (fun x => by rw [tailVec_apply_zero])

/-! ## (3) The piece chart and the open set `O` -/

/-- The chart of the piece at the index `i`. -/
def chartE {m : ℕ} (a : Fin m × ι) (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) :
    OpenPartialHomeomorph (Fam a.2).pt (EuclideanSpace ℝ (Fin 8)) :=
  (Work.ThomBordism.FrameSigns.chartOf (Fam a.2) i).1

/-- **The open subset of the sigma type of pieces** over the piece `a`, read through the chart `i`. -/
def UaC {m : ℕ} (a : Fin m × ι) (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) :
    Set (Σ c : Fin m × ι, (Fam c.2).pt) :=
  Sigma.mk a '' (chartE a i).source

theorem isOpen_UaC {m : ℕ} (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) : IsOpen (UaC a i) :=
  (Topology.IsOpenEmbedding.sigmaMk
    (σ := fun c : Fin m × ι => (Fam c.2).pt) (i := a)).isOpenMap _ (chartE a i).open_source

/-- **The open set of the ambient half-space over the piece `a`** (the largest open set whose
boundary identification values lie over `a` with chart `i`). -/
def Ofam (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (a : Fin m × ι) (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) : Set (SrcHS k) :=
  ⋃₀ {P : Set (SrcHS k) | IsOpen P ∧
    ∀ x (hx : x ∈ bdryDom G m hpow), x ∈ P → h ⟨x, hx⟩ ∈ UaC a i}

theorem isOpen_Ofam (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1) (h : BdryId G m hpow)
    (a : Fin m × ι) (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) :
    IsOpen (Ofam G m hpow h a i) :=
  isOpen_sUnion fun _ hP => hP.1

theorem mem_Ofam_iff {G : GenuineTubeGeometry k D ι Fam} {m : ℕ}
    {hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1} {h : BdryId G m hpow}
    {a : Fin m × ι} {i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)}
    {x : SrcHS k} (hx : x ∈ bdryDom G m hpow) :
    x ∈ Ofam G m hpow h a i ↔ h ⟨x, hx⟩ ∈ UaC a i := by
  constructor
  · intro hxO
    rw [Ofam, Set.mem_sUnion] at hxO
    obtain ⟨P, hP, hxP⟩ := hxO
    exact hP.2 x hx hxP
  · intro hxU
    have hcont : Continuous h := h.continuous
    have hU : IsOpen (h ⁻¹' UaC a i) := (isOpen_UaC a i).preimage hcont
    obtain ⟨P, hP, hPeq⟩ := (isOpen_induced_iff (f := (Subtype.val :
      ↥(bdryDom G m hpow) → SrcHS k))).mp hU
    have hxP : x ∈ P := by
      have h1 : (⟨x, hx⟩ : ↥(bdryDom G m hpow)) ∈ Subtype.val ⁻¹' P := by
        rw [hPeq]
        exact hxU
      exact h1
    rw [Ofam, Set.mem_sUnion]
    refine ⟨P, ⟨hP, ?_⟩, hxP⟩
    intro y hy hyP
    have h1 : (⟨y, hy⟩ : ↥(bdryDom G m hpow)) ∈ Subtype.val ⁻¹' P := hyP
    rw [hPeq] at h1
    exact h1

/-! ## (4) The collar thickness, the target and the clamped collar lift -/

/-- The collar thickness of the chart: `min (εcl / 2) (1 / 4)`. -/
def deltaC (εcl : ℝ) : ℝ := min (εcl / 2) (1 / 4)

/-- The clamp threshold: `max (min (1 / 4) εcl) 0`. -/
def cminC (εcl : ℝ) : ℝ := max (min (1 / 4) εcl) 0

theorem deltaC_pos {εcl : ℝ} (h : 0 < εcl) : 0 < deltaC εcl :=
  lt_min (by linarith) (by norm_num)

theorem deltaC_le_eps {εcl : ℝ} (h : 0 < εcl) : deltaC εcl ≤ εcl :=
  le_trans (min_le_left _ _) (by linarith)

theorem deltaC_le_quarter (εcl : ℝ) : deltaC εcl ≤ 1 / 4 := min_le_right _ _

theorem deltaC_le_half (εcl : ℝ) : deltaC εcl ≤ 1 / 2 := by
  have := deltaC_le_quarter εcl; linarith

theorem deltaC_le_min {εcl : ℝ} (hεcl : 0 ≤ εcl) : deltaC εcl ≤ min (1 / 4) εcl :=
  le_min (min_le_right _ _) (le_trans (min_le_left _ _) (by linarith))

theorem deltaC_le_cmin (εcl : ℝ) : deltaC εcl ≤ cminC εcl := by
  by_cases h : 0 ≤ εcl
  · exact le_trans (deltaC_le_min h) (le_max_left _ _)
  · have hε : εcl < 0 := not_le.mp h
    have h1 : deltaC εcl ≤ 0 := by
      rw [deltaC, min_eq_left (by linarith : εcl / 2 ≤ 1 / 4)]
      linarith
    exact le_trans h1 (le_max_right _ _)

theorem cminC_pos {εcl : ℝ} (h : 0 < εcl) : 0 < cminC εcl :=
  lt_of_lt_of_le (lt_min (by norm_num) h) (le_max_left _ _)

theorem cminC_le_quarter (εcl : ℝ) : cminC εcl ≤ 1 / 4 :=
  max_le (min_le_left _ _) (by norm_num)

theorem cminC_le_eps {εcl : ℝ} (h : 0 < εcl) : cminC εcl ≤ εcl :=
  max_le (min_le_right _ _) (le_of_lt h)

theorem cminC_le_half (εcl : ℝ) : cminC εcl ≤ 1 / 2 := by
  have := cminC_le_quarter εcl; linarith

/-- **The target of the collar chart**: the `δ`-collar of the chart target of the piece. -/
def tgtC {m : ℕ} (εcl : ℝ) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) : Set (EuclideanHalfSpace 9) :=
  {z | z.1 0 < deltaC εcl ∧ Work.PTGeometric.tail 8 z.1 ∈ (chartE a i).target}

theorem isOpen_tgtC {m : ℕ} (εcl : ℝ) (a : Fin m × ι)
    (i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)) : IsOpen (tgtC εcl a i) := by
  have h1 : Continuous fun z : EuclideanHalfSpace 9 => z.1 0 := by fun_prop
  have h2 : Continuous fun z : EuclideanHalfSpace 9 => Work.PTGeometric.tail 8 z.1 :=
    (Work.PTGeometric.continuous_tail 8).comp continuous_subtype_val
  exact (isOpen_lt h1 continuous_const).inter ((chartE a i).open_target.preimage h2)

theorem mem_tgtC_iff {m : ℕ} {εcl : ℝ} {a : Fin m × ι}
    {i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)} {z : EuclideanHalfSpace 9} :
    z ∈ tgtC εcl a i ↔ z.1 0 < deltaC εcl ∧
      Work.PTGeometric.tail 8 z.1 ∈ (chartE a i).target := Iff.rfl

/-- The clamp of the collar coordinate. -/
def clampC (εcl : ℝ) (t : ℝ) : ℝ := min (max t 0) (cminC εcl)

theorem clampC_nonneg (εcl t : ℝ) : 0 ≤ clampC εcl t :=
  le_min (le_max_right t 0) (le_max_right _ 0)

theorem clampC_le (εcl t : ℝ) : clampC εcl t ≤ cminC εcl := min_le_right _ _

theorem clampC_le_half (εcl t : ℝ) : clampC εcl t ≤ 1 / 2 :=
  le_trans (clampC_le εcl t) (cminC_le_half εcl)

theorem clampC_le_eps {εcl : ℝ} (h : 0 < εcl) (t : ℝ) : clampC εcl t ≤ εcl :=
  le_trans (clampC_le εcl t) (cminC_le_eps h)

theorem clampC_eq_self {εcl t : ℝ} (h0 : 0 ≤ t) (ht : t ≤ min (1 / 4) εcl) :
    clampC εcl t = t := by
  rw [clampC, cminC, max_eq_left h0, min_eq_left (le_trans ht (le_max_left _ _))]

theorem continuous_clampC (εcl : ℝ) : Continuous (fun t : ℝ => clampC εcl t) := by
  rw [show (fun t : ℝ => clampC εcl t) = fun t : ℝ => min (max t 0) (cminC εcl) from rfl]
  fun_prop

/-- The (clamped) argument of the collar piece: the point of `ℝ⁹` with clamped `0`-th coordinate. -/
def collZ (εcl : ℝ) (z : EuclideanHalfSpace 9) : CofAtlas.E9 :=
  euCons (clampC εcl (z.1 0)) (Work.PTGeometric.tail 8 z.1)

theorem collZ_apply_zero (εcl : ℝ) (z : EuclideanHalfSpace 9) :
    collZ εcl z 0 = clampC εcl (z.1 0) := euCons_zero _ _

theorem tail_collZ (εcl : ℝ) (z : EuclideanHalfSpace 9) :
    Work.PTGeometric.tail 8 (collZ εcl z) = Work.PTGeometric.tail 8 z.1 :=
  tail_euCons _ _

theorem collZ_eq_self {εcl : ℝ} {z : EuclideanHalfSpace 9} (h : clampC εcl (z.1 0) = z.1 0) :
    collZ εcl z = z.1 := by
  have h2 : euCons (clampC εcl (z.1 0)) (Work.PTGeometric.tail 8 z.1) = z.1 := by
    rw [h, euCons_tail_self]
  exact h2

theorem collZ_eq_of {εcl : ℝ} {z : EuclideanHalfSpace 9} (h0 : 0 ≤ z.1 0)
    (ht : z.1 0 ≤ min (1 / 4) εcl) : collZ εcl z = z.1 :=
  collZ_eq_self (clampC_eq_self h0 ht)

theorem tailVec_eq_self_of_zero {v : SrcVS k} (h : v 0 = 0) :
    Work.PTGeometric.tailVec v = v := by
  ext i
  rcases eq_or_ne i 0 with rfl | hi
  · rw [Work.PTGeometric.tailVec_apply_zero, h]
  · rw [Work.PTGeometric.tailVec_ofLp_ne_zero hi]

/-! ## (5) The bundled data of the collar chart -/

/-- **The source region of the construction**, as an explicit subtype of the ambient half-space
(it is definitionally `(sourceRegionSetup G m hpow hphi hweak).Region`). -/
abbrev SrcM {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
    (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1)
    (hphi : SourceRegionPhiInteriorSign k (sourceZeroSet G m hpow)
      (sourceBasepoint (D := D) (Fam := Fam) G m hpow)) : Type :=
  {x : SrcHS k // sourcePhi G m hpow hphi x ≤ 0}

/-- The level set `{w = 0}`. -/
abbrev LW (G : GenuineTubeGeometry k D ι Fam) (m : ℕ)
    (hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1)
    (hphi : SourceRegionPhiInteriorSign k (sourceZeroSet G m hpow)
      (sourceBasepoint (D := D) (Fam := Fam) G m hpow))
    (w : SrcM G m hpow hphi → EuclideanSpace ℝ (Fin (k + G.mU))) : Type :=
  ↥{x : SrcM G m hpow hphi | w x = 0}

/-- **The data of the collar chart at a piece**: the source construction, the specified boundary
identification, the collar thickness and the level function (with its collar agreement). -/
structure CollarData (k : ℕ) (D : Work.ThomBordism.PontryaginThom.ThomTarget k) (ι : Type)
    [Fintype ι] (Fam : ι → Work.ThomBordism.Man8) [T2Space D.T] where
  G : GenuineTubeGeometry k D ι Fam
  m : ℕ
  hpow : (∏ i, tubeAlpha (G.rep i)) ^ m = 1
  hphi : SourceRegionPhiInteriorSign k (sourceZeroSet G m hpow)
    (sourceBasepoint (D := D) (Fam := Fam) G m hpow)
  hweak : ∀ x : SrcHS k, sourcePhi G m hpow hphi x = 0 →
    mfderiv (modelWithCornersEuclideanHalfSpace ((8 + k) + 1))
      (modelWithCornersSelf ℝ ℝ) (sourcePhi G m hpow hphi) x ≠ 0
  h : BdryId G m hpow
  a : Fin m × ι
  i : Work.ThomBordism.FrameSigns.ChartIdx (Fam a.2)
  εcl : ℝ
  hεcl : 0 < εcl
  w : SrcM G m hpow hphi → EuclideanSpace ℝ (Fin (k + G.mU))
  hwv : ∀ x : SrcM G m hpow hphi, x.1.1 0 ≤ εcl → w x = vSrc G m hpow x.1.1


/-! ## (6) The collar lift of the piece -/

section Collar

variable (T : CollarData k D ι Fam)

/-- The source region of the data. -/
abbrev DataM : Type := SrcM T.G T.m T.hpow T.hphi

/-- The level set `{w = 0}` of the data. -/
abbrev DataLW : Type := LW T.G T.m T.hpow T.hphi T.w

/-- The boundary zero point of the piece `a` through the chart `i` of the collar parameter `z`. -/
def collBdry (z : EuclideanHalfSpace 9) : SrcHS k :=
  (T.h.symm ⟨T.a, (chartE T.a T.i).symm (Work.PTGeometric.tail 8 z.1)⟩).1

theorem collBdry_mem (z : EuclideanHalfSpace 9) :
    collBdry T z ∈ sourceZeroSet T.G T.m T.hpow :=
  (T.h.symm ⟨T.a, (chartE T.a T.i).symm (Work.PTGeometric.tail 8 z.1)⟩).2.1

theorem collBdry_apply_zero (z : EuclideanHalfSpace 9) :
    (collBdry T z).1 0 = 0 :=
  (T.h.symm ⟨T.a, (chartE T.a T.i).symm (Work.PTGeometric.tail 8 z.1)⟩).2.2

theorem collBdry_coe (z : EuclideanHalfSpace 9) :
    ((collBdry T z).1 : SrcVS k) =
      (T.h.symm ⟨T.a, (chartE T.a T.i).symm (Work.PTGeometric.tail 8 z.1)⟩).1.1 := rfl

/-- The (clamped) collar lift of the piece, as a vector of `ℝ^{9+k}`. -/
def collarVec (z : EuclideanHalfSpace 9) : SrcVS k :=
  collarPiece T.G T.m T.hpow T.h T.a T.i (collZ T.εcl z)

theorem collarVec_zero (z : EuclideanHalfSpace 9) :
    collarVec T z 0 = clampC T.εcl (z.1 0) := by
  have h1 : (collZ T.εcl z) 0 = clampC T.εcl (z.1 0) := collZ_apply_zero T.εcl z
  rw [collarVec, collarPiece, h1, Work.PTGeometric.consVec_apply_zero,
    Work.PTGeometric.tailVec_apply_zero, add_zero]

theorem collarVec_nonneg (z : EuclideanHalfSpace 9) : 0 ≤ collarVec T z 0 := by
  rw [collarVec_zero]
  exact clampC_nonneg T.εcl _

theorem collarVec_tail (z : EuclideanHalfSpace 9) :
    Work.PTGeometric.tailVec (collarVec T z) =
      Work.PTGeometric.tailVec ((collBdry T z).1 : SrcVS k) := by
  rw [collarVec, collarPiece]
  exact Work.PTGeometric.tailVec_consVec _ (Work.PTGeometric.tailVec_apply_zero _)

theorem collBdry_tailVec (z : EuclideanHalfSpace 9) :
    Work.PTGeometric.tailVec ((collBdry T z).1 : SrcVS k) = ((collBdry T z).1 : SrcVS k) :=
  tailVec_eq_self_of_zero (k := k) (collBdry_apply_zero T z)

theorem collarVec_tail' (z : EuclideanHalfSpace 9) :
    Work.PTGeometric.tailVec (collarVec T z) = ((collBdry T z).1 : SrcVS k) := by
  rw [collarVec_tail, collBdry_tailVec]

theorem collarVec_ofLp_ne_zero {z : EuclideanHalfSpace 9} {j : Fin ((8 + k) + 1)}
    (hj : j ≠ 0) : collarVec T z j = ((collBdry T z).1 : SrcVS k) j := by
  rw [← Work.PTGeometric.tailVec_ofLp_ne_zero hj, collarVec_tail']

/-- The (clamped) collar lift of the piece, as a point of the ambient half-space. -/
def collarHS (z : EuclideanHalfSpace 9) : SrcHS k :=
  ⟨collarVec T z, collarVec_nonneg T z⟩

theorem collarHS_coe (z : EuclideanHalfSpace 9) : (collarHS T z).1 = collarVec T z := rfl

theorem collarHS_apply_zero (z : EuclideanHalfSpace 9) :
    (collarHS T z).1 0 = clampC T.εcl (z.1 0) :=
  collarVec_zero T z

theorem collarHS_mem (z : EuclideanHalfSpace 9) :
    collarHS T z ∈ sourceZeroSet T.G T.m T.hpow := by
  refine mem_sourceZeroSet_of_collarRay T.G T.m T.hpow (collBdry_mem T z) ?_ ?_ ?_
  · rw [collBdry_apply_zero]; norm_num
  · intro j hj
    rw [collarHS_coe, collarVec_ofLp_ne_zero T hj]
  · rw [collarHS_apply_zero]
    exact clampC_le_half T.εcl _

theorem collarHS_mem_core (z : EuclideanHalfSpace 9) :
    srcHf T.G T.m T.hpow (collarVec T z) ∈ T.G.core :=
  collarHS_mem T z

/-- **The collar lift of the piece in the source region.** -/
def collarReg (z : EuclideanHalfSpace 9) : DataM T :=
  ⟨collarHS T z, (sourcePhi_spec T.G T.m T.hpow T.hphi).2.1 (collarHS_mem T z)⟩

theorem collarReg_coe (z : EuclideanHalfSpace 9) : (collarReg T z).1 = collarHS T z := rfl

theorem collarReg_apply_zero (z : EuclideanHalfSpace 9) :
    (collarReg T z).1.1 0 = clampC T.εcl (z.1 0) :=
  collarHS_apply_zero T z

theorem vSrc_eq_zero_of_mem_core {u : SrcVS k}
    (hcore : srcHf T.G T.m T.hpow u ∈ T.G.core) :
    vSrc T.G T.m T.hpow u = 0 := by
  have hne : srcHf T.G T.m T.hpow u ≠ D.t₀ := fun hh => T.G.t0_notMem_core (hh ▸ hcore)
  rw [vSrc, dif_neg hne]
  exact (T.G.core_iff_vec ⟨srcHf T.G T.m T.hpow u, hne⟩).mp hcore

theorem w_collarReg (z : EuclideanHalfSpace 9) : T.w (collarReg T z) = 0 := by
  rw [T.hwv _ (by rw [collarReg_apply_zero]; exact clampC_le_eps T.hεcl _),
    collarReg_coe T z, collarHS_coe,
    vSrc_eq_zero_of_mem_core T (collarHS_mem_core T z)]

/-- **The collar lift of the piece in the level set `{w = 0}`.** -/
def collarW (z : EuclideanHalfSpace 9) : DataLW T :=
  ⟨collarReg T z, w_collarReg T z⟩

theorem collarW_coe (z : EuclideanHalfSpace 9) : (collarW T z).1 = collarReg T z := rfl

theorem collarW_apply_zero (z : EuclideanHalfSpace 9) :
    (collarW T z).1.1.1 0 = clampC T.εcl (z.1 0) :=
  collarReg_apply_zero T z

/-- The collar lift of the piece, in the target of the chart. -/
theorem collarW_eq_piece {z : EuclideanHalfSpace 9} (hz : z ∈ tgtC T.εcl T.a T.i) :
    (collarW T z).1.1.1 = collarPiece T.G T.m T.hpow T.h T.a T.i z.1 := by
  have h0 : 0 ≤ z.1 0 := z.2
  have ht : z.1 0 ≤ min (1 / 4) T.εcl :=
    le_trans (le_of_lt hz.1) (deltaC_le_min (le_of_lt T.hεcl))
  show collarVec T z = collarPiece T.G T.m T.hpow T.h T.a T.i z.1
  rw [collarVec, collZ_eq_of h0 ht]

end Collar

end

end Work.ThomBordism.LeadChapter

namespace Work.ThomBordism.LeadChapter

open Work.PTGeometric

noncomputable section

variable {k : ℕ} {D : Work.ThomBordism.PontryaginThom.ThomTarget k}
  {ι : Type} [Fintype ι] {Fam : ι → Work.ThomBordism.Man8} [T2Space D.T]

section MoreLemmas

/-- `consVec` is continuous in the pair `(s, u)`. -/
theorem continuous_consVec :
    Continuous (fun p : ℝ × SrcVS k => Work.PTGeometric.consVec p.1 p.2) := by
  have h : (fun p : ℝ × SrcVS k => Work.PTGeometric.consVec p.1 p.2)
      = fun p : ℝ × SrcVS k => p.2 + p.1 • (Work.PTGeometric.eZero : SrcVS k) := rfl
  rw [h]
  fun_prop

end MoreLemmas

end

end Work.ThomBordism.LeadChapter
