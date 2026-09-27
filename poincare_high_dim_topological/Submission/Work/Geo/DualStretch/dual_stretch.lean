import Mathlib
import Submission.Work.Geo.DualStretch.Basic
import Submission.Work.Geo.DualStretch.Defs
import Submission.Work.Geo.DualStretch.Local
import Submission.Work.Geo.DualStretch.coord_spec
import Submission.Work.Geo.DualStretch.carrier_spec
import Submission.Work.Geo.DualStretch.high_dom
import Submission.Work.Geo.DualStretch.taperM_props
import Submission.Work.Geo.DualStretch.massOf_sum
import Submission.Work.Geo.DualStretch.massOf_combination
import Submission.Work.Geo.DualStretch.massOf_chain
import Submission.Work.Geo.DualStretch.massOf_pos_iff
import Submission.Work.Geo.DualStretch.massG_api
import Submission.Work.Geo.DualStretch.stretch_defs
import Submission.Work.Geo.DualStretch.stretch_fix_outside
import Submission.Work.Geo.DualStretch.stretch_inv
import Submission.Work.Geo.DualStretch.stretch_inv_right
import Submission.Work.Geo.DualStretch.join_decomp
import Submission.Work.Geo.DualStretch.uOf_mem_low
import Submission.Work.Geo.DualStretch.wOf_mem_high
import Submission.Work.Geo.DualStretch.massG_of_chain_repr
import Submission.Work.Geo.DualStretch.continuousOn_rcoord
import Submission.Work.Geo.DualStretch.coord_eq_rcoord

/-!
# The Stallings/Connell dual stretch homeomorphism

This file proves `Work.Geo.DualStretch.dual_stretch`, the `G7` statement of the blueprint: for a
finite complex `P` triangulating the closed cube of radius `β`, and open sets `N₁ ⊇ Low P p`,
`N₂ ⊇ High P p`, there is a self-homeomorphism of `ℝⁿ` which is the identity outside the open cube
of radius `β`, preserves every face simplex of `P` setwise, and carries the smaller closed cube
`closedCube α` into `h '' N₁ ∪ N₂`.

The homeomorphism is the *stretch* `Work.Geo.DualStretch.stretch`: it leaves the low part `A(x)`
alone, rescales the high part `B(x)` by the taper `taperM` and renormalises.  The bulk of the file
establishes what is needed for the final argument:

* continuity of the barycentric masses `massG` and of the parts `A`, `B`, `S`;
* continuity of the stretch itself;
* the identity law `stretch_inv` of a sibling file;
* the localisation of the covering argument, where the two separating constants
  `dist (Low, P.space \ N₁)` and `dist (High, P.space \ N₂)` are positive.
-/

set_option maxHeartbeats 4000000

open Set Metric
open scoped Classical
open scoped Topology
open Filter

namespace Work.Geo.DualStretch

open _root_.PL (E Cx closedCube openCube)

variable {n : ℕ}

/-! ## Continuity of the barycentric coordinates and of the masses -/

/-- The barycentric coordinate `x ↦ coord P x v` is continuous on the polyhedron `P.space`
(it is `rcoord σ · v` on the closed simplex of each face `σ`, and these finitely many closed
simplices cover `P.space`). -/
theorem continuousOn_coord (P : PL.Cx n) (hP : P.faces.Finite) (v : PL.E n) :
    ContinuousOn (fun x : PL.E n => coord P x v) P.space := by
  classical
  haveI : Fintype {σ : Finset (PL.E n) // σ ∈ P.faces} := hP.fintype
  have hloc : LocallyFinite
      (fun σ : {σ : Finset (PL.E n) // σ ∈ P.faces} => PL.simp (σ : Finset (PL.E n))) :=
    locallyFinite_of_finite _
  have hclosed : ∀ σ : {σ : Finset (PL.E n) // σ ∈ P.faces},
      IsClosed (PL.simp (σ : Finset (PL.E n))) :=
    fun σ => (Finset.finite_toSet _).isClosed_convexHull ℝ
  have hcont : ∀ σ : {σ : Finset (PL.E n) // σ ∈ P.faces},
      ContinuousOn (fun x : PL.E n => coord P x v) (PL.simp (σ : Finset (PL.E n))) := by
    intro σ
    refine (continuousOn_rcoord (P.indep σ.2) v).congr ?_
    intro x hx
    exact coord_eq_rcoord P hP σ.2 hx v
  have hcov : (⋃ σ : {σ : Finset (PL.E n) // σ ∈ P.faces},
      PL.simp (σ : Finset (PL.E n))) = P.space := by
    apply Subset.antisymm
    · intro x hx
      rw [mem_iUnion] at hx
      obtain ⟨σ, hxσ⟩ := hx
      exact Geometry.SimplicialComplex.convexHull_subset_space σ.2 hxσ
    · intro x hx
      rw [Geometry.SimplicialComplex.mem_space_iff] at hx
      obtain ⟨σ, hσ, hxσ⟩ := hx
      exact mem_iUnion.mpr ⟨⟨σ, hσ⟩, hxσ⟩
  rw [← hcov]
  exact hloc.continuousOn_iUnion hclosed hcont

/-- Pointwise `max` of two functions continuous on a set. -/
theorem continuousOn_max_of {X : Type*} [TopologicalSpace X] {s : Set X} {f g : X → ℝ}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => max (f x) (g x)) s :=
  continuous_max.comp_continuousOn (hf.prodMk hg)

/-- Pointwise `min` of two functions continuous on a set. -/
theorem continuousOn_min_of {X : Type*} [TopologicalSpace X] {s : Set X} {f g : X → ℝ}
    (hf : ContinuousOn f s) (hg : ContinuousOn g s) :
    ContinuousOn (fun x => min (f x) (g x)) s :=
  continuous_min.comp_continuousOn (hf.prodMk hg)

/-- `minVal` of a continuous family is continuous. -/
theorem continuousOn_minVal {X : Type*} [TopologicalSpace X] {s : Finset (PL.E n)}
    {μ : X → PL.E n → ℝ} {t : Set X} (hμ : ∀ v, ContinuousOn (fun x => μ x v) t) :
    ContinuousOn (fun x => minVal s (μ x)) t := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [minVal_empty]
    exact continuousOn_const
  · have key : ∀ x, minVal s (μ x) = s.inf' hne (fun v => μ x v) := by
      intro x
      refine le_antisymm ?_ ?_
      · exact Finset.le_inf' hne _ (fun b hb => minVal_le hb)
      · obtain ⟨v0, hv0, hv0'⟩ := minVal_mem (s := s) (μ := μ x) hne
        calc s.inf' hne (fun v => μ x v) ≤ μ x v0 := Finset.inf'_le _ hv0
          _ = minVal s (μ x) := hv0'
    refine (ContinuousOn.finset_inf'_apply hne (fun i _ => hμ i)).congr ?_
    intro x _
    exact key x

/-- `maxVal` of a continuous family is continuous. -/
theorem continuousOn_maxVal {X : Type*} [TopologicalSpace X] {s : Finset (PL.E n)}
    {μ : X → PL.E n → ℝ} {t : Set X} (hμ : ∀ v, ContinuousOn (fun x => μ x v) t) :
    ContinuousOn (fun x => maxVal s (μ x)) t := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hne
  · simp only [maxVal_empty]
    exact continuousOn_const
  · have key : ∀ x, maxVal s (μ x) = s.sup' hne (fun v => μ x v) := by
      intro x
      refine le_antisymm ?_ ?_
      · obtain ⟨v0, hv0, hv0'⟩ := maxVal_mem (s := s) (μ := μ x) hne
        calc maxVal s (μ x) = μ x v0 := hv0'.symm
          _ ≤ s.sup' hne (fun v => μ x v) := Finset.le_sup' _ hv0
      · exact Finset.sup'_le hne _ (fun b hb => le_maxVal hb)
    refine (ContinuousOn.finset_sup'_apply hne (fun i _ => hμ i)).congr ?_
    intro x _
    exact key x

/-- The barycentric mass `massG P hP · τ` is continuous on the polyhedron. -/
theorem continuousOn_massG (P : PL.Cx n) (hP : P.faces.Finite) (τ : Finset (PL.E n)) :
    ContinuousOn (fun x : PL.E n => massG P hP x τ) P.space := by
  have hcoord : ∀ v : PL.E n, ContinuousOn (fun x : PL.E n => coord P x v) P.space :=
    fun v => continuousOn_coord P hP v
  have hmin : ContinuousOn (fun x => minVal τ (coord P x)) P.space :=
    continuousOn_minVal hcoord
  have hmax := continuousOn_maxVal (s := verts P hP \ τ) hcoord
  simp only [massG]
  exact continuousOn_max_of continuousOn_const (continuousOn_const.mul (hmin.sub hmax))

/-- The low part `A` is continuous on the polyhedron. -/
theorem continuousOn_AOf (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ) :
    ContinuousOn (fun x : PL.E n => AOf β p P hP x) P.space := by
  simp only [AOf]
  refine continuousOn_finsetSum _ (fun τ _ => ?_)
  split_ifs with hL
  · exact (continuousOn_massG P hP τ).smul continuousOn_const
  · exact continuousOn_const

/-- The high part `B` is continuous on the polyhedron. -/
theorem continuousOn_BOf (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ) :
    ContinuousOn (fun x : PL.E n => BOf β p P hP x) P.space := by
  simp only [BOf]
  refine continuousOn_finsetSum _ (fun τ _ => ?_)
  split_ifs with hL
  · exact continuousOn_const
  · exact (continuousOn_massG P hP τ).smul continuousOn_const

/-- The total high mass `S` is continuous on the polyhedron. -/
theorem continuousOn_SOf (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ) :
    ContinuousOn (fun x : PL.E n => SOf β p P hP x) P.space := by
  simp only [SOf]
  refine continuousOn_finsetSum _ (fun τ _ => ?_)
  split_ifs with hL
  · exact continuousOn_const
  · exact continuousOn_massG P hP τ


/-! ## Continuity of the join data and of the stretch -/

/-- `clamp01` is continuous. -/
private lemma continuous_clamp01 : Continuous (clamp01 : ℝ → ℝ) := by
  rw [show (clamp01 : ℝ → ℝ) = fun t => max 0 (min 1 t) from rfl]
  exact continuous_const.max (continuous_const.min continuous_id)

/-- The low endpoint `uOf` is continuous where the low mass does not vanish. -/
private theorem continuousOn_uOf (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ) :
    ContinuousOn (fun x : PL.E n => uOf β p P hP x)
      (P.space ∩ {x | 1 - SOf β p P hP x ≠ 0}) := by
  have hS : ContinuousOn (fun x : PL.E n => SOf β p P hP x) P.space := continuousOn_SOf P hP β p
  have h1 : ContinuousOn (fun x : PL.E n => 1 - SOf β p P hP x)
      (P.space ∩ {x | 1 - SOf β p P hP x ≠ 0}) :=
    (continuousOn_const.sub hS).mono inter_subset_left
  have h2 : ContinuousOn (fun x : PL.E n => (1 - SOf β p P hP x)⁻¹)
      (P.space ∩ {x | 1 - SOf β p P hP x ≠ 0}) :=
    h1.inv₀ (fun x hx => hx.2)
  have h3 : ContinuousOn (fun x : PL.E n => AOf β p P hP x)
      (P.space ∩ {x | 1 - SOf β p P hP x ≠ 0}) :=
    (continuousOn_AOf P hP β p).mono inter_subset_left
  have h4 : ContinuousOn (fun x : PL.E n => (1 - SOf β p P hP x)⁻¹ • AOf β p P hP x)
      (P.space ∩ {x | 1 - SOf β p P hP x ≠ 0}) := h2.smul h3
  refine h4.congr ?_
  intro x hx
  simp only [uOf]
  rw [ite_eq_right hx.2]

/-- The high endpoint `wOf` is continuous where the high mass does not vanish. -/
private theorem continuousOn_wOf (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ) :
    ContinuousOn (fun x : PL.E n => wOf β p P hP x)
      (P.space ∩ {x | SOf β p P hP x ≠ 0}) := by
  have hS : ContinuousOn (fun x : PL.E n => SOf β p P hP x) P.space := continuousOn_SOf P hP β p
  have h1 : ContinuousOn (fun x : PL.E n => SOf β p P hP x)
      (P.space ∩ {x | SOf β p P hP x ≠ 0}) := hS.mono inter_subset_left
  have h2 : ContinuousOn (fun x : PL.E n => (SOf β p P hP x)⁻¹)
      (P.space ∩ {x | SOf β p P hP x ≠ 0}) :=
    h1.inv₀ (fun x hx => hx.2)
  have h3 : ContinuousOn (fun x : PL.E n => BOf β p P hP x)
      (P.space ∩ {x | SOf β p P hP x ≠ 0}) :=
    (continuousOn_BOf P hP β p).mono inter_subset_left
  have h4 : ContinuousOn (fun x : PL.E n => (SOf β p P hP x)⁻¹ • BOf β p P hP x)
      (P.space ∩ {x | SOf β p P hP x ≠ 0}) := h2.smul h3
  refine h4.congr ?_
  intro x hx
  simp only [wOf]
  rw [ite_eq_right hx.2]

/-- The set on which the join segment varies continuously (interior of the mass range). -/
private def goodSet (β : ℝ) (p : ℕ) (P : PL.Cx n) (hP : P.faces.Finite) : Set (PL.E n) :=
  P.space ∩ {x | 0 < SOf β p P hP x ∧ SOf β p P hP x < 1}

/-- The join segment is continuous in the interior of the mass range. -/
private theorem continuousOn_segOf (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ) :
    ContinuousOn (fun x : PL.E n => segOf β p P hP x) (goodSet β p P hP) := by
  have hu : ContinuousOn (fun x : PL.E n => uOf β p P hP x) (goodSet β p P hP) :=
    (continuousOn_uOf P hP β p).mono (fun x hx => ⟨hx.1, ne_of_gt (by linarith [hx.2.2] : (0:ℝ) < 1 - SOf β p P hP x)⟩)
  have hw : ContinuousOn (fun x : PL.E n => wOf β p P hP x) (goodSet β p P hP) :=
    (continuousOn_wOf P hP β p).mono (fun x hx => ⟨hx.1, ne_of_gt hx.2.1⟩)
  have hpair : ContinuousOn (fun x : PL.E n => (uOf β p P hP x, wOf β p P hP x))
      (goodSet β p P hP) := hu.prodMk hw
  refine hpair.congr ?_
  intro x _
  rfl

/-- The taper is continuous in the interior of the mass range. -/
private theorem continuousOn_taperM (P : PL.Cx n) (hP : P.faces.Finite) (β α M : ℝ) (p : ℕ) :
    ContinuousOn (fun x : PL.E n => taperM β p P hP α M x) (goodSet β p P hP) := by
  have hseg : ContinuousOn (fun x : PL.E n => segOf β p P hP x) (goodSet β p P hP) :=
    continuousOn_segOf P hP β p
  have hinf : ContinuousOn
      (fun x : PL.E n => Metric.infDist (segOf β p P hP x) (BdrySeg β)) (goodSet β p P hP) :=
    (Metric.continuous_infDist_pt (BdrySeg β)).comp_continuousOn hseg
  have hconst : ∀ c : ℝ, ContinuousOn (fun _ : PL.E n => c) (goodSet β p P hP) :=
    fun c => continuousOn_const
  have hdiv : ContinuousOn (fun x : PL.E n =>
      Metric.infDist (segOf β p P hP x) (BdrySeg β) / ((β - α) / 2)) (goodSet β p P hP) :=
    hinf.div_const _
  have hcl : ContinuousOn (fun x : PL.E n =>
      clamp01 (Metric.infDist (segOf β p P hP x) (BdrySeg β) / ((β - α) / 2)))
      (goodSet β p P hP) := by
    have hmax : ContinuousOn (fun x : PL.E n =>
        max 0 (min 1 (Metric.infDist (segOf β p P hP x) (BdrySeg β) / ((β - α) / 2))))
        (goodSet β p P hP) :=
      continuousOn_max_of (hconst 0) (continuousOn_min_of (hconst 1) hdiv)
    exact hmax.congr (fun x _ => by simp only [clamp01])
  have hmul : ContinuousOn (fun x : PL.E n =>
      (M - 1) * clamp01 (Metric.infDist (segOf β p P hP x) (BdrySeg β) / ((β - α) / 2)))
      (goodSet β p P hP) := (hconst (M - 1)).mul hcl
  exact ((hconst 1).add hmul).congr (fun x _ => by simp only [taperM]; rfl)

/-- The total high mass is non-negative. -/
private theorem SOf_nonneg (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ) (x : PL.E n) :
    0 ≤ SOf β p P hP x := by
  rw [SOf]
  refine Finset.sum_nonneg (fun τ _ => ?_)
  split_ifs with hL
  · norm_num
  · rw [massG]; exact le_max_left _ _

/-- The renormalisation factor is at least `1` (for `1 ≤ M`). -/
private theorem one_le_denOf (P : PL.Cx n) (hP : P.faces.Finite) {β α M : ℝ} (p : ℕ)
    (hM : 1 ≤ M) (x : PL.E n) : 1 ≤ denOf β p P hP α M x := by
  rw [denOf, taperM]
  have hc0 : 0 ≤ clamp01 (Metric.infDist (segOf β p P hP x) (BdrySeg β) / ((β - α) / 2)) :=
    clamp01_nonneg _
  have hS0 : 0 ≤ SOf β p P hP x := SOf_nonneg P hP β p x
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ M - 1) hc0, mul_nonneg
    (mul_nonneg (by linarith : (0:ℝ) ≤ M - 1) hc0) hS0]

/-- The renormalisation factor is continuous in the interior of the mass range. -/
private theorem continuousOn_denOf (P : PL.Cx n) (hP : P.faces.Finite) (β α M : ℝ) (p : ℕ) :
    ContinuousOn (fun x : PL.E n => denOf β p P hP α M x) (goodSet β p P hP) := by
  have ht : ContinuousOn (fun x : PL.E n => taperM β p P hP α M x) (goodSet β p P hP) :=
    continuousOn_taperM P hP β α M p
  have hS : ContinuousOn (fun x : PL.E n => SOf β p P hP x) (goodSet β p P hP) :=
    (continuousOn_SOf P hP β p).mono inter_subset_left
  have hconst : ∀ c : ℝ, ContinuousOn (fun _ : PL.E n => c) (goodSet β p P hP) :=
    fun c => continuousOn_const
  have h1 : ContinuousOn (fun x : PL.E n => taperM β p P hP α M x - 1) (goodSet β p P hP) :=
    ht.sub (hconst 1)
  have h2 : ContinuousOn (fun x : PL.E n => (taperM β p P hP α M x - 1) * SOf β p P hP x)
      (goodSet β p P hP) := h1.mul hS
  exact ((hconst 1).add h2).congr (fun x _ => by simp only [denOf, Pi.add_apply])

/-- The stretch is continuous in the interior of the mass range. -/
private theorem continuousOn_stretch_good (P : PL.Cx n) (hP : P.faces.Finite) {β α M : ℝ}
    {p : ℕ} (hM : 1 ≤ M) :
    ContinuousOn (fun x : PL.E n => stretch P hP β p α M x) (goodSet β p P hP) := by
  have hden : ContinuousOn (fun x : PL.E n => denOf β p P hP α M x) (goodSet β p P hP) :=
    continuousOn_denOf P hP β α M p
  have hden_inv : ContinuousOn (fun x : PL.E n => (denOf β p P hP α M x)⁻¹) (goodSet β p P hP) :=
    hden.inv₀ (fun x _ => ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_denOf P hP p hM x)))
  have hA : ContinuousOn (fun x : PL.E n => AOf β p P hP x) (goodSet β p P hP) :=
    (continuousOn_AOf P hP β p).mono inter_subset_left
  have hB : ContinuousOn (fun x : PL.E n => BOf β p P hP x) (goodSet β p P hP) :=
    (continuousOn_BOf P hP β p).mono inter_subset_left
  have ht : ContinuousOn (fun x : PL.E n => taperM β p P hP α M x) (goodSet β p P hP) :=
    continuousOn_taperM P hP β α M p
  have hform : ContinuousOn (fun x : PL.E n =>
      (denOf β p P hP α M x)⁻¹ • (AOf β p P hP x + taperM β p P hP α M x • BOf β p P hP x))
      (goodSet β p P hP) := hden_inv.smul (hA.add (ht.smul hB))
  refine hform.congr ?_
  intro x hx
  exact stretch_unfold P hP hx.1



/-! ## The displacement bound and the extreme values of `SOf` -/

/-- The total high mass is at most `1`. -/
private theorem SOf_le_one' (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ) {x : PL.E n}
    (hx : x ∈ P.space) : SOf β p P hP x ≤ 1 := by
  have h1 : SOf β p P hP x ≤ ∑ τ ∈ cands P hP, massG P hP x τ := by
    rw [SOf]
    refine Finset.sum_le_sum (fun τ _ => ?_)
    split_ifs with hL
    · rw [massG]; exact le_max_left _ _
    · exact le_rfl
  calc SOf β p P hP x ≤ ∑ τ ∈ cands P hP, massG P hP x τ := h1
    _ = 1 := (massG_api P hP hx).2.1

/-- The total low mass is `1 - SOf`. -/
private theorem sum_low_massG (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ) {x : PL.E n}
    (hx : x ∈ P.space) :
    (∑ τ ∈ cands P hP, (if LowFace β p τ then massG P hP x τ else 0)) = 1 - SOf β p P hP x := by
  have hsplit : (∑ τ ∈ cands P hP, massG P hP x τ)
      = (∑ τ ∈ cands P hP, (if LowFace β p τ then massG P hP x τ else 0))
        + (∑ τ ∈ cands P hP, (if LowFace β p τ then 0 else massG P hP x τ)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    split_ifs <;> ring
  have hhigh : (∑ τ ∈ cands P hP, (if LowFace β p τ then 0 else massG P hP x τ))
      = SOf β p P hP x := rfl
  rw [hhigh, (massG_api P hP hx).2.1] at hsplit
  linarith

/-- Norm bound on the low part. -/
private theorem norm_AOf_le (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ) {x : PL.E n}
    (hx : x ∈ P.space) {K : ℝ} (hK : ∀ τ ∈ cands P hP, ‖bary τ‖ ≤ K) :
    ‖AOf β p P hP x‖ ≤ (1 - SOf β p P hP x) * K := by
  have hnn : ∀ τ : Finset (PL.E n), 0 ≤ massG P hP x τ := fun τ => le_max_left _ _
  have hnorm : ∀ τ, ‖(if LowFace β p τ then massG P hP x τ • bary τ else (0 : PL.E n))‖
      = (if LowFace β p τ then massG P hP x τ * ‖bary τ‖ else 0) := by
    intro τ
    split_ifs with hL
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hnn τ)]
    · simp
  rw [AOf]
  calc ‖∑ τ ∈ cands P hP, (if LowFace β p τ then massG P hP x τ • bary τ else 0)‖
      ≤ ∑ τ ∈ cands P hP, ‖(if LowFace β p τ then massG P hP x τ • bary τ else 0)‖ :=
        norm_sum_le _ _
    _ = ∑ τ ∈ cands P hP, (if LowFace β p τ then massG P hP x τ * ‖bary τ‖ else 0) :=
        Finset.sum_congr rfl (fun τ _ => hnorm τ)
    _ ≤ ∑ τ ∈ cands P hP, (if LowFace β p τ then massG P hP x τ * K else 0) := by
        refine Finset.sum_le_sum (fun τ hτ => ?_)
        split_ifs with hL
        · exact mul_le_mul_of_nonneg_left (hK τ hτ) (hnn τ)
        · exact le_rfl
    _ = (∑ τ ∈ cands P hP, (if LowFace β p τ then massG P hP x τ else 0)) * K := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun τ _ => ?_)
        split_ifs <;> ring
    _ = (1 - SOf β p P hP x) * K := by rw [sum_low_massG P hP β p hx]

/-- Norm bound on the high part. -/
private theorem norm_BOf_le (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ) {x : PL.E n}
    (hx : x ∈ P.space) {K : ℝ} (hK : ∀ τ ∈ cands P hP, ‖bary τ‖ ≤ K) :
    ‖BOf β p P hP x‖ ≤ SOf β p P hP x * K := by
  have hnn : ∀ τ : Finset (PL.E n), 0 ≤ massG P hP x τ := fun τ => le_max_left _ _
  have hnorm : ∀ τ, ‖(if LowFace β p τ then (0 : PL.E n) else massG P hP x τ • bary τ)‖
      = (if LowFace β p τ then 0 else massG P hP x τ * ‖bary τ‖) := by
    intro τ
    split_ifs with hL
    · simp
    · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hnn τ)]
  rw [BOf]
  calc ‖∑ τ ∈ cands P hP, (if LowFace β p τ then (0 : PL.E n) else massG P hP x τ • bary τ)‖
      ≤ ∑ τ ∈ cands P hP, ‖(if LowFace β p τ then (0 : PL.E n) else massG P hP x τ • bary τ)‖ :=
        norm_sum_le _ _
    _ = ∑ τ ∈ cands P hP, (if LowFace β p τ then 0 else massG P hP x τ * ‖bary τ‖) :=
        Finset.sum_congr rfl (fun τ _ => hnorm τ)
    _ ≤ ∑ τ ∈ cands P hP, (if LowFace β p τ then 0 else massG P hP x τ * K) := by
        refine Finset.sum_le_sum (fun τ hτ => ?_)
        split_ifs with hL
        · exact le_rfl
        · exact mul_le_mul_of_nonneg_left (hK τ hτ) (hnn τ)
    _ = (∑ τ ∈ cands P hP, (if LowFace β p τ then 0 else massG P hP x τ)) * K := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun τ _ => ?_)
        split_ifs <;> ring
    _ = SOf β p P hP x * K := rfl

/-- `cands` is nonempty whenever the polyhedron is. -/
private theorem cands_nonempty (P : PL.Cx n) (hP : P.faces.Finite) {x : PL.E n}
    (hx : x ∈ P.space) : (cands P hP).Nonempty := by
  rw [Geometry.SimplicialComplex.mem_space_iff] at hx
  obtain ⟨σ, hσ, -⟩ := hx
  exact ⟨σ, by rw [cands, Finset.mem_biUnion]; exact ⟨σ,
    (Set.Finite.mem_toFinset hP).mpr hσ, Finset.mem_powerset.mpr (le_refl σ)⟩⟩

/-- **Displacement bound for a renormalised stretch.** -/
private theorem dist_stretchM_le (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ)
    {Mb : E n → ℝ} {K C : ℝ} (hC : 0 ≤ C)
    (hden_pos : ∀ x ∈ P.space, 0 < 1 + (Mb x - 1) * SOf β p P hP x)
    (hBd : ∀ x ∈ P.space, |Mb x - 1| / (1 + (Mb x - 1) * SOf β p P hP x) ≤ C)
    (hK : ∀ τ ∈ cands P hP, ‖bary τ‖ ≤ K) :
    ∀ x ∈ P.space, dist (stretchM β p P hP Mb x) x
      ≤ C * 2 * SOf β p P hP x * (1 - SOf β p P hP x) * K := by
  intro x hx
  have hA := norm_AOf_le P hP β p hx hK
  have hB := norm_BOf_le P hP β p hx hK
  have hAB : AOf β p P hP x + BOf β p P hP x = x := AOf_add_BOf P hP hx
  set s := SOf β p P hP x with hs
  set A := AOf β p P hP x with hAdef
  set B := BOf β p P hP x with hBdef
  set t := Mb x with ht
  set d := 1 + (t - 1) * s with hd
  have hs0 : 0 ≤ s := by rw [hs]; exact SOf_nonneg P hP β p x
  have hs1 : s ≤ 1 := by rw [hs]; exact SOf_le_one' P hP β p hx
  have hd0 : 0 < d := by rw [hd]; exact hden_pos x hx
  have hA' : ‖A‖ ≤ (1 - s) * K := by rw [hAdef, hs]; exact hA
  have hB' : ‖B‖ ≤ s * K := by rw [hBdef, hs]; exact hB
  have hKnn : 0 ≤ K :=
    le_trans (norm_nonneg _) (hK _ (cands_nonempty P hP hx).choose_spec)
  have hden : stretchM β p P hP Mb x = d⁻¹ • (A + t • B) := by
    unfold stretchM
    rw [ite_eq_left hx]
  have halg : A + t • B - d • x = (1 - t) • (s • A - (1 - s) • B) := by
    rw [← hAB, hd]
    module
  have hstep : ‖s • A - (1 - s) • B‖ ≤ 2 * s * (1 - s) * K := by
    calc ‖s • A - (1 - s) • B‖ ≤ ‖s • A‖ + ‖(1 - s) • B‖ := norm_sub_le _ _
      _ = s * ‖A‖ + (1 - s) * ‖B‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hs0,
            abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - s)]
      _ ≤ s * ((1 - s) * K) + (1 - s) * (s * K) :=
          add_le_add (mul_le_mul_of_nonneg_left hA' hs0)
            (mul_le_mul_of_nonneg_left hB' (by linarith : (0:ℝ) ≤ 1 - s))
      _ = 2 * s * (1 - s) * K := by ring
  have heq : ‖d⁻¹ • (A + t • B) - x‖ = (|1 - t| / d) * ‖s • A - (1 - s) • B‖ := by
    have hdvd : d⁻¹ • (d • x) = x := by
      rw [smul_smul, inv_mul_cancel₀ (ne_of_gt hd0), one_smul]
    have step : d⁻¹ • (A + t • B) - x = d⁻¹ • ((1 - t) • (s • A - (1 - s) • B)) := by
      conv_lhs => rw [← hdvd]
      rw [← smul_sub, halg]
    rw [step, norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_inv,
      abs_of_pos hd0]
    ring
  rw [dist_eq_norm, hden, heq]
  calc (|1 - t| / d) * ‖s • A - (1 - s) • B‖
      ≤ (|1 - t| / d) * (2 * s * (1 - s) * K) :=
        mul_le_mul_of_nonneg_left hstep (div_nonneg (abs_nonneg _) (le_of_lt hd0))
    _ ≤ C * (2 * s * (1 - s) * K) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (mul_nonneg (mul_nonneg
          (by norm_num : (0:ℝ) ≤ 2) hs0) (sub_nonneg.mpr hs1)) hKnn)
        rw [abs_sub_comm]
        exact hBd x hx
    _ = C * 2 * s * (1 - s) * K := by ring

/-- `stretch` fixes the points of zero high mass. -/
private theorem stretch_eq_self_of_SOf_eq_zero {β α M : ℝ} {p : ℕ} (P : PL.Cx n)
    (hP : P.faces.Finite) {x : PL.E n} (hx : x ∈ P.space) (hS : SOf β p P hP x = 0) :
    stretch P hP β p α M x = x := by
  have hnn : ∀ τ ∈ cands P hP, 0 ≤ (if LowFace β p τ then (0:ℝ) else massG P hP x τ) := by
    intro τ _
    split_ifs with hL
    · exact le_rfl
    · exact le_max_left _ _
  have hall : ∀ τ ∈ cands P hP, (if LowFace β p τ then (0:ℝ) else massG P hP x τ) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn).mp (by rw [← SOf]; exact hS)
  have hB : BOf β p P hP x = 0 := by
    rw [BOf]
    refine Finset.sum_eq_zero (fun τ hτ => ?_)
    by_cases hL : LowFace β p τ
    · rw [if_pos hL]
    · rw [if_neg hL]
      have h := hall τ hτ
      rw [if_neg hL] at h
      rw [h, zero_smul]
  have hA : AOf β p P hP x = x := by
    have h := AOf_add_BOf (β := β) (p := p) P hP hx
    rw [hB, add_zero] at h
    exact h
  have hden : denOf β p P hP α M x = 1 := by rw [denOf, hS]; ring
  rw [stretch_unfold P hP hx, hden, hB, hA]
  simp

/-- `stretch` fixes the points of full high mass. -/
private theorem stretch_eq_self_of_SOf_eq_one {β α M : ℝ} {p : ℕ} (P : PL.Cx n)
    (hP : P.faces.Finite) (hM : 0 < M) {x : PL.E n} (hx : x ∈ P.space)
    (hS : SOf β p P hP x = 1) : stretch P hP β p α M x = x := by
  have hnn : ∀ τ ∈ cands P hP, 0 ≤ (if LowFace β p τ then massG P hP x τ else (0:ℝ)) := by
    intro τ _
    split_ifs with hL
    · exact le_max_left _ _
    · exact le_rfl
  have h0 : (∑ τ ∈ cands P hP, (if LowFace β p τ then massG P hP x τ else 0)) = 0 := by
    rw [sum_low_massG P hP β p hx, hS]; ring
  have hall : ∀ τ ∈ cands P hP, (if LowFace β p τ then massG P hP x τ else (0:ℝ)) = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h0
  have hA : AOf β p P hP x = 0 := by
    rw [AOf]
    refine Finset.sum_eq_zero (fun τ hτ => ?_)
    by_cases hL : LowFace β p τ
    · rw [if_pos hL]
      have h := hall τ hτ
      rw [if_pos hL] at h
      rw [h, zero_smul]
    · rw [if_neg hL]
  have hB : BOf β p P hP x = x := by
    have h := AOf_add_BOf (β := β) (p := p) P hP hx
    rw [hA, zero_add] at h
    exact h
  have ht : taperM β p P hP α M x ≠ 0 := ne_of_gt (taperM_pos hM p P hP x)
  have hden : denOf β p P hP α M x = taperM β p P hP α M x := by rw [denOf, hS]; ring
  rw [stretch_unfold P hP hx, hden, hA, zero_add]
  rw [smul_smul, inv_mul_cancel₀ ht, one_smul, hB]

/-! ## Bounds and continuity of the stretch and of its inverse -/

private theorem isOpen_openCube (β : ℝ) : IsOpen (PL.openCube (n := n) β) := by
  rw [show PL.openCube (n := n) β = ⋂ i : Fin n, (fun y : PL.E n => |y i|) ⁻¹' Set.Iio β
      from by ext y; simp [PL.openCube]]
  exact isOpen_iInter_of_finite fun i =>
    isOpen_Iio.preimage (continuous_abs.comp (PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) i))

private theorem isClosed_space (P : PL.Cx n) (hP : P.faces.Finite) : IsClosed P.space := by
  classical
  haveI : Fintype {σ : Finset (PL.E n) // σ ∈ P.faces} := hP.fintype
  rw [show P.space = ⋃ σ : {σ : Finset (PL.E n) // σ ∈ P.faces},
      PL.simp (σ : Finset (PL.E n)) from by
    apply Subset.antisymm
    · intro x hx
      rw [Geometry.SimplicialComplex.mem_space_iff] at hx
      obtain ⟨σ, hσ, hxσ⟩ := hx
      exact mem_iUnion.mpr ⟨⟨σ, hσ⟩, hxσ⟩
    · intro x hx
      rw [mem_iUnion] at hx
      obtain ⟨σ, hxσ⟩ := hx
      exact Geometry.SimplicialComplex.convexHull_subset_space σ.2 hxσ]
  exact isClosed_iUnion_of_finite fun σ => (Finset.finite_toSet _).isClosed_convexHull ℝ

private theorem one_le_taperM {β α M : ℝ} {p : ℕ} (P : PL.Cx n) (hP : P.faces.Finite)
    (hM : 1 ≤ M) (x : PL.E n) : 1 ≤ taperM β p P hP α M x := by
  rw [taperM]
  have hc := clamp01_nonneg (Metric.infDist (segOf β p P hP x) (BdrySeg β) / ((β - α) / 2))
  nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ M - 1) hc]

private theorem taperM_le {β α M : ℝ} {p : ℕ} (P : PL.Cx n) (hP : P.faces.Finite)
    (hM : 1 ≤ M) (x : PL.E n) : taperM β p P hP α M x ≤ M := by
  rw [taperM]
  have hc := clamp01_le_one (Metric.infDist (segOf β p P hP x) (BdrySeg β) / ((β - α) / 2))
  nlinarith [mul_le_mul_of_nonneg_left hc (by linarith : (0:ℝ) ≤ M - 1)]

private theorem abs_taperM_sub_one_le {β α M : ℝ} {p : ℕ} (P : PL.Cx n) (hP : P.faces.Finite)
    (hM : 1 ≤ M) (x : PL.E n) : |taperM β p P hP α M x - 1| ≤ M - 1 := by
  rw [taperM, add_sub_cancel_left, abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ M - 1),
    abs_of_nonneg (clamp01_nonneg _)]
  exact mul_le_of_le_one_right (by linarith) (clamp01_le_one _)

private theorem abs_invTaper_sub_one_le {β α M : ℝ} {p : ℕ} (P : PL.Cx n) (hP : P.faces.Finite)
    (hM : 1 ≤ M) (x : PL.E n) : |(taperM β p P hP α M x)⁻¹ - 1| ≤ 1 - M⁻¹ := by
  have hM0 : 0 < M := by linarith
  have ht1 : 1 ≤ taperM β p P hP α M x := one_le_taperM P hP hM x
  have htM : taperM β p P hP α M x ≤ M := taperM_le P hP hM x
  have ht0 : 0 < taperM β p P hP α M x := lt_of_lt_of_le zero_lt_one ht1
  have hge : M⁻¹ ≤ (taperM β p P hP α M x)⁻¹ := (inv_le_inv₀ hM0 ht0).mpr htM
  have hle : (taperM β p P hP α M x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht1
  rw [abs_of_nonpos (by linarith)]
  linarith

private theorem invTaper_den_pos {β α M : ℝ} {p : ℕ} (P : PL.Cx n) (hP : P.faces.Finite)
    (hM : 1 ≤ M) {x : PL.E n} (hx : x ∈ P.space) :
    0 < 1 + ((taperM β p P hP α M x)⁻¹ - 1) * SOf β p P hP x := by
  have hM0 : 0 < M := by linarith
  have ht1 : 1 ≤ taperM β p P hP α M x := one_le_taperM P hP hM x
  have hge : M⁻¹ ≤ (taperM β p P hP α M x)⁻¹ :=
    (inv_le_inv₀ hM0 (by linarith)).mpr (taperM_le P hP hM x)
  have h5' : (taperM β p P hP α M x)⁻¹ - 1 ≤ 0 := by
    have : (taperM β p P hP α M x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht1
    linarith
  have h6 : (taperM β p P hP α M x)⁻¹ - 1
      ≤ ((taperM β p P hP α M x)⁻¹ - 1) * SOf β p P hP x := by
    have h4 : SOf β p P hP x ≤ 1 := SOf_le_one' P hP β p hx
    nlinarith [mul_le_mul_of_nonpos_left h4 h5', h5']
  linarith [inv_pos.mpr hM0]

private theorem invTaper_bd {β α M : ℝ} {p : ℕ} (P : PL.Cx n) (hP : P.faces.Finite)
    (hM : 1 ≤ M) {x : PL.E n} (hx : x ∈ P.space) :
    |(taperM β p P hP α M x)⁻¹ - 1|
        / (1 + ((taperM β p P hP α M x)⁻¹ - 1) * SOf β p P hP x) ≤ M - 1 := by
  have hM0 : 0 < M := by linarith
  have h3 : |(taperM β p P hP α M x)⁻¹ - 1| ≤ 1 - M⁻¹ := abs_invTaper_sub_one_le P hP hM x
  have hden : 0 < 1 + ((taperM β p P hP α M x)⁻¹ - 1) * SOf β p P hP x :=
    invTaper_den_pos P hP hM hx
  have hge : M⁻¹ ≤ 1 + ((taperM β p P hP α M x)⁻¹ - 1) * SOf β p P hP x := by
    have ht1 : 1 ≤ taperM β p P hP α M x := one_le_taperM P hP hM x
    have hge' : M⁻¹ ≤ (taperM β p P hP α M x)⁻¹ :=
      (inv_le_inv₀ hM0 (by linarith)).mpr (taperM_le P hP hM x)
    have h5' : (taperM β p P hP α M x)⁻¹ - 1 ≤ 0 := by
      have : (taperM β p P hP α M x)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ht1
      linarith
    have h6 : (taperM β p P hP α M x)⁻¹ - 1
        ≤ ((taperM β p P hP α M x)⁻¹ - 1) * SOf β p P hP x := by
      have h4 : SOf β p P hP x ≤ 1 := SOf_le_one' P hP β p hx
      nlinarith [mul_le_mul_of_nonpos_left h4 h5', h5']
    linarith
  rw [div_le_iff₀ hden]
  have h8 : M⁻¹ * (M - 1) = 1 - M⁻¹ := by field_simp
  calc |(taperM β p P hP α M x)⁻¹ - 1| ≤ 1 - M⁻¹ := h3
    _ = M⁻¹ * (M - 1) := h8.symm
    _ ≤ (1 + ((taperM β p P hP α M x)⁻¹ - 1) * SOf β p P hP x) * (M - 1) :=
        mul_le_mul_of_nonneg_right hge (by linarith)
    _ = (M - 1) * (1 + ((taperM β p P hP α M x)⁻¹ - 1) * SOf β p P hP x) := by ring

private theorem dist_stretch_le {β α M : ℝ} {p : ℕ} (P : PL.Cx n) (hP : P.faces.Finite)
    (hM : 1 ≤ M) {K : ℝ} (hK : ∀ τ ∈ cands P hP, ‖bary τ‖ ≤ K) :
    ∀ x ∈ P.space, dist (stretch P hP β p α M x) x
      ≤ SOf β p P hP x * (1 - SOf β p P hP x) * ((M - 1) * 2 * K) := by
  intro x hx
  have hden_pos : ∀ y ∈ P.space, 0 < 1 + (taperM β p P hP α M y - 1) * SOf β p P hP y := by
    intro y hy
    have h1 : 1 ≤ taperM β p P hP α M y := one_le_taperM P hP hM y
    have h2 : 0 ≤ SOf β p P hP y := SOf_nonneg P hP β p y
    nlinarith
  have hbd : ∀ y ∈ P.space, |taperM β p P hP α M y - 1|
      / (1 + (taperM β p P hP α M y - 1) * SOf β p P hP y) ≤ M - 1 := by
    intro y hy
    have h1 : |taperM β p P hP α M y - 1| ≤ M - 1 := abs_taperM_sub_one_le P hP hM y
    have h2 : 1 ≤ 1 + (taperM β p P hP α M y - 1) * SOf β p P hP y := by
      have h2' := hden_pos y hy
      have h3 : 1 ≤ taperM β p P hP α M y := one_le_taperM P hP hM y
      have h4 : 0 ≤ SOf β p P hP y := SOf_nonneg P hP β p y
      nlinarith
    exact le_trans (div_le_self (abs_nonneg _) h2) h1
  have h := dist_stretchM_le (P := P) (hP := hP) (β := β) (p := p)
    (Mb := taperM β p P hP α M) (K := K) (C := M - 1) (by linarith) hden_pos hbd hK x hx
  calc dist (stretch P hP β p α M x) x
      = dist (stretchM β p P hP (taperM β p P hP α M) x) x := rfl
    _ ≤ (M - 1) * 2 * SOf β p P hP x * (1 - SOf β p P hP x) * K := h
    _ = SOf β p P hP x * (1 - SOf β p P hP x) * ((M - 1) * 2 * K) := by ring

private theorem dist_stretchM_invTaper_le {β α M : ℝ} {p : ℕ} (P : PL.Cx n) (hP : P.faces.Finite)
    (hM : 1 ≤ M) {K : ℝ} (hK : ∀ τ ∈ cands P hP, ‖bary τ‖ ≤ K) :
    ∀ x ∈ P.space, dist (stretchM β p P hP (fun z => (taperM β p P hP α M z)⁻¹) x) x
      ≤ SOf β p P hP x * (1 - SOf β p P hP x) * ((M - 1) * 2 * K) := by
  intro x hx
  have h := dist_stretchM_le (P := P) (hP := hP) (β := β) (p := p)
    (Mb := fun z => (taperM β p P hP α M z)⁻¹) (K := K) (C := M - 1) (by linarith)
    (fun y hy => invTaper_den_pos P hP hM hy)
    (fun y hy => invTaper_bd P hP hM hy) hK x hx
  calc dist (stretchM β p P hP (fun z => (taperM β p P hP α M z)⁻¹) x) x
      ≤ (M - 1) * 2 * SOf β p P hP x * (1 - SOf β p P hP x) * K := h
    _ = SOf β p P hP x * (1 - SOf β p P hP x) * ((M - 1) * 2 * K) := by ring

private theorem stretchM_eq_self_of_SOf_eq_zero {β : ℝ} {p : ℕ} (P : PL.Cx n)
    (hP : P.faces.Finite) {Mb : PL.E n → ℝ} {x : PL.E n} (hx : x ∈ P.space)
    (hS : SOf β p P hP x = 0) : stretchM β p P hP Mb x = x := by
  have hB : BOf β p P hP x = 0 := sfo_BOf_eq_zero_of_SOf_eq_zero P hP hS
  have hA : AOf β p P hP x = x := by
    have h := AOf_add_BOf (β := β) (p := p) P hP hx
    rw [hB, add_zero] at h
    exact h
  unfold stretchM
  rw [ite_eq_left hx, hS, mul_zero, add_zero, hB, smul_zero, add_zero, inv_one, one_smul, hA]

private theorem stretchM_eq_self_of_SOf_eq_one {β : ℝ} {p : ℕ} (P : PL.Cx n)
    (hP : P.faces.Finite) {Mb : PL.E n → ℝ} {x : PL.E n} (hx : x ∈ P.space)
    (hMb : Mb x ≠ 0) (hS : SOf β p P hP x = 1) : stretchM β p P hP Mb x = x := by
  have hA : AOf β p P hP x = 0 := sfo_AOf_eq_zero_of_SOf_eq_one P hP hx hS
  have hB : BOf β p P hP x = x := by
    have h := AOf_add_BOf (β := β) (p := p) P hP hx
    rw [hA, zero_add] at h
    exact h
  unfold stretchM
  rw [ite_eq_left hx, hS]
  rw [show (1:ℝ) + (Mb x - 1) * 1 = Mb x by ring, hA, zero_add, smul_smul,
    inv_mul_cancel₀ hMb, one_smul, hB]

private theorem continuousWithinAt_stretch_extreme {β : ℝ} {p : ℕ} (P : PL.Cx n)
    (hP : P.faces.Finite) {f : PL.E n → PL.E n} {K : ℝ}
    (hfix : ∀ x ∈ P.space, (SOf β p P hP x = 0 ∨ SOf β p P hP x = 1) → f x = x)
    (hbd : ∀ x ∈ P.space, dist (f x) x
      ≤ SOf β p P hP x * (1 - SOf β p P hP x) * K)
    {x₀ : PL.E n} (hx₀ : x₀ ∈ P.space)
    (hSx₀ : SOf β p P hP x₀ = 0 ∨ SOf β p P hP x₀ = 1) :
    ContinuousWithinAt f P.space x₀ := by
  have hfx : f x₀ = x₀ := hfix x₀ hx₀ hSx₀
  show Tendsto f (𝓝[P.space] x₀) (𝓝 (f x₀))
  rw [hfx]
  have hScont : ContinuousWithinAt (fun x => SOf β p P hP x) P.space x₀ :=
    (continuousOn_SOf P hP β p).continuousWithinAt hx₀
  have hprod : Tendsto (fun x => SOf β p P hP x * (1 - SOf β p P hP x))
      (𝓝[P.space] x₀) (𝓝 0) := by
    have h1 : Tendsto (fun x => SOf β p P hP x) (𝓝[P.space] x₀) (𝓝 (SOf β p P hP x₀)) := hScont
    have h2 : Tendsto (fun x => (1:ℝ) - SOf β p P hP x) (𝓝[P.space] x₀)
        (𝓝 ((1:ℝ) - SOf β p P hP x₀)) := continuousWithinAt_const.sub hScont
    have h := h1.mul h2
    have h0 : SOf β p P hP x₀ * (1 - SOf β p P hP x₀) = 0 := by
      rcases hSx₀ with hh | hh <;> rw [hh] <;> ring
    rwa [h0] at h
  have hmax : Tendsto (fun x => SOf β p P hP x * (1 - SOf β p P hP x) * K + dist x x₀)
      (𝓝[P.space] x₀) (𝓝 0) := by
    have h1 : Tendsto (fun x => SOf β p P hP x * (1 - SOf β p P hP x) * K)
        (𝓝[P.space] x₀) (𝓝 0) := by
      simpa using hprod.mul (tendsto_const_nhds (x := K))
    have h2 : Tendsto (fun x : PL.E n => dist x x₀) (𝓝[P.space] x₀) (𝓝 0) := by
      have hid : Tendsto (id : PL.E n → PL.E n) (𝓝[P.space] x₀) (𝓝 x₀) :=
        (Filter.tendsto_id : Tendsto (id : PL.E n → PL.E n) (𝓝 x₀) (𝓝 x₀)).mono_left inf_le_left
      have h := hid.dist (tendsto_const_nhds (x := x₀))
      simpa using h
    simpa using h1.add h2
  exact (tendsto_iff_dist_tendsto_zero (f := f) (a := x₀) (x := 𝓝[P.space] x₀)).mpr
    (squeeze_zero' (Eventually.of_forall fun x => dist_nonneg) (by
      filter_upwards [self_mem_nhdsWithin] with x hx
      calc dist (f x) x₀ ≤ dist (f x) x + dist x x₀ := dist_triangle _ _ _
        _ ≤ SOf β p P hP x * (1 - SOf β p P hP x) * K + dist x x₀ :=
            add_le_add (hbd x hx) le_rfl) hmax)

private theorem continuousOn_of_good_and_bound {β : ℝ} {p : ℕ} (P : PL.Cx n)
    (hP : P.faces.Finite) {f : PL.E n → PL.E n} {K : ℝ}
    (hgood : ContinuousOn f (goodSet β p P hP))
    (hfix : ∀ x ∈ P.space, (SOf β p P hP x = 0 ∨ SOf β p P hP x = 1) → f x = x)
    (hbd : ∀ x ∈ P.space, dist (f x) x
      ≤ SOf β p P hP x * (1 - SOf β p P hP x) * K) :
    ContinuousOn f P.space := by
  intro x₀ hx₀
  rcases eq_or_lt_of_le (SOf_nonneg P hP β p x₀) with h0 | h0
  · exact continuousWithinAt_stretch_extreme P hP hfix hbd hx₀ (Or.inl h0.symm)
  · rcases eq_or_lt_of_le (SOf_le_one' P hP β p hx₀) with h1 | h1
    · exact continuousWithinAt_stretch_extreme P hP hfix hbd hx₀ (Or.inr h1)
    · have hmem : x₀ ∈ goodSet β p P hP := ⟨hx₀, h0, h1⟩
      have hnhd : SOf β p P hP ⁻¹' (Set.Ioo 0 1) ∈ 𝓝[P.space] x₀ :=
        (continuousOn_SOf P hP β p).continuousWithinAt hx₀
          |>.preimage_mem_nhdsWithin (isOpen_Ioo.mem_nhds ⟨h0, h1⟩)
      have hmem' : goodSet β p P hP ∈ 𝓝[P.space] x₀ := by
        have h2 : (P.space : Set (PL.E n)) ∈ 𝓝[P.space] x₀ := self_mem_nhdsWithin
        have h3 : goodSet β p P hP = P.space ∩ SOf β p P hP ⁻¹' (Set.Ioo 0 1) := by
          ext x; simp [goodSet, Set.mem_Ioo, and_comm]
        rw [h3]
        exact Filter.inter_mem h2 hnhd
      exact (hgood.continuousWithinAt hmem).mono_of_mem_nhdsWithin hmem'

private theorem continuousOn_stretch {β α M : ℝ} {p : ℕ} (P : PL.Cx n) (hP : P.faces.Finite)
    (hM : 1 ≤ M) {K : ℝ} (hK : ∀ τ ∈ cands P hP, ‖bary τ‖ ≤ K) :
    ContinuousOn (fun x : PL.E n => stretch P hP β p α M x) P.space := by
  refine continuousOn_of_good_and_bound P hP (continuousOn_stretch_good P hP hM)
    (fun x hx hS => ?_) (dist_stretch_le P hP hM hK)
  rcases hS with h | h
  · exact stretchM_eq_self_of_SOf_eq_zero (Mb := taperM β p P hP α M) P hP hx h
  · exact stretchM_eq_self_of_SOf_eq_one (Mb := taperM β p P hP α M) P hP hx
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_taperM P hP hM x))) h

private theorem continuousOn_invTaper {β α M : ℝ} {p : ℕ} (P : PL.Cx n) (hP : P.faces.Finite)
    (hM : 1 ≤ M) {K : ℝ} (hK : ∀ τ ∈ cands P hP, ‖bary τ‖ ≤ K) :
    ContinuousOn (fun x : PL.E n => stretchM β p P hP (fun z => (taperM β p P hP α M z)⁻¹) x)
      P.space := by
  have hform : ContinuousOn (fun x : PL.E n =>
      (1 + ((taperM β p P hP α M x)⁻¹ - 1) * SOf β p P hP x)⁻¹ •
        (AOf β p P hP x + (taperM β p P hP α M x)⁻¹ • BOf β p P hP x))
      (goodSet β p P hP) := by
    have hA : ContinuousOn (fun x : PL.E n => AOf β p P hP x) (goodSet β p P hP) :=
      (continuousOn_AOf P hP β p).mono inter_subset_left
    have hB : ContinuousOn (fun x : PL.E n => BOf β p P hP x) (goodSet β p P hP) :=
      (continuousOn_BOf P hP β p).mono inter_subset_left
    have hS : ContinuousOn (fun x : PL.E n => SOf β p P hP x) (goodSet β p P hP) :=
      (continuousOn_SOf P hP β p).mono inter_subset_left
    have ht : ContinuousOn (fun x : PL.E n => taperM β p P hP α M x) (goodSet β p P hP) :=
      continuousOn_taperM P hP β α M p
    have htinv : ContinuousOn (fun x : PL.E n => (taperM β p P hP α M x)⁻¹) (goodSet β p P hP) :=
      ht.inv₀ (fun x _ => ne_of_gt (lt_of_lt_of_le zero_lt_one (one_le_taperM P hP hM x)))
    have hden : ContinuousOn (fun x : PL.E n =>
        1 + ((taperM β p P hP α M x)⁻¹ - 1) * SOf β p P hP x) (goodSet β p P hP) :=
      continuousOn_const.add ((htinv.sub continuousOn_const).mul hS)
    have hden_inv : ContinuousOn (fun x : PL.E n =>
        (1 + ((taperM β p P hP α M x)⁻¹ - 1) * SOf β p P hP x)⁻¹) (goodSet β p P hP) :=
      hden.inv₀ (fun x hx => ne_of_gt (invTaper_den_pos P hP hM hx.1))
    exact hden_inv.smul (hA.add (htinv.smul hB))
  have hgood : ContinuousOn
      (fun x : PL.E n => stretchM β p P hP (fun z => (taperM β p P hP α M z)⁻¹) x)
      (goodSet β p P hP) := by
    refine hform.congr (fun x hx => ?_)
    unfold stretchM
    rw [ite_eq_left hx.1]
  refine continuousOn_of_good_and_bound P hP hgood (fun x hx hS => ?_)
    (dist_stretchM_invTaper_le P hP hM hK)
  rcases hS with h | h
  · exact stretchM_eq_self_of_SOf_eq_zero (Mb := fun z => (taperM β p P hP α M z)⁻¹) P hP hx h
  · exact stretchM_eq_self_of_SOf_eq_one (Mb := fun z => (taperM β p P hP α M z)⁻¹) P hP hx
      (inv_ne_zero (ne_of_gt
        (lt_of_lt_of_le zero_lt_one (one_le_taperM P hP hM x)))) h

private theorem continuous_of_continuousOn_fix {β : ℝ} (P : PL.Cx n) (hP : P.faces.Finite)
    (hsp : P.space = closedCube β) {f : PL.E n → PL.E n}
    (hsub : ∀ x, x ∉ P.space → f x = x)
    (hcont : ContinuousOn f P.space)
    (hfix : ∀ x ∈ P.space, x ∉ PL.openCube β → f x = x) :
    Continuous f := by
  rw [Metric.continuous_iff]
  intro x₀ ε hε
  by_cases hx₀ : x₀ ∈ P.space
  · obtain ⟨δ₁, hδ₁, hδ₁'⟩ :=
      (Metric.continuousWithinAt_iff.mp (hcont.continuousWithinAt hx₀)) ε hε
    rcases eq_or_ne (f x₀) x₀ with hf | hf
    · refine ⟨min δ₁ ε, lt_min hδ₁ hε, fun y hy => ?_⟩
      have hy1 : dist y x₀ < δ₁ := lt_of_lt_of_le hy (min_le_left _ _)
      by_cases hyP : y ∈ P.space
      · exact hδ₁' hyP hy1
      · rw [hsub y hyP, hf]
        exact lt_of_lt_of_le hy (min_le_right _ _)
    · have hx₀op : x₀ ∈ PL.openCube β := by
        by_contra hc
        exact hf (hfix x₀ hx₀ hc)
      obtain ⟨ρ, hρ, hρ'⟩ := Metric.isOpen_iff.mp (isOpen_openCube (n := n) β) x₀ hx₀op
      refine ⟨min δ₁ ρ, lt_min hδ₁ hρ, fun y hy => ?_⟩
      have hy1 : dist y x₀ < δ₁ := lt_of_lt_of_le hy (min_le_left _ _)
      have hyP : y ∈ P.space := by
        have hyop : y ∈ PL.openCube β := hρ' (lt_of_lt_of_le hy (min_le_right _ _))
        rw [hsp]
        exact fun i => le_of_lt (hyop i)
      exact hδ₁' hyP hy1
  · obtain ⟨ρ, hρ, hρ'⟩ := Metric.isOpen_iff.mp
      (isClosed_space P hP).isOpen_compl x₀ hx₀
    refine ⟨min ρ ε, lt_min hρ hε, fun y hy => ?_⟩
    have hyP : y ∉ P.space := hρ' (lt_of_lt_of_le hy (min_le_left _ _))
    rw [hsub y hyP, hsub x₀ hx₀]
    exact lt_of_lt_of_le hy (min_le_right _ _)

private noncomputable def barySup (P : PL.Cx n) (hP : P.faces.Finite) : ℝ :=
  if h : (cands P hP).Nonempty then (cands P hP).sup' h (fun τ => ‖bary τ‖) else 0

private theorem le_barySup (P : PL.Cx n) (hP : P.faces.Finite) {τ : Finset (PL.E n)}
    (hτ : τ ∈ cands P hP) : ‖bary τ‖ ≤ barySup P hP := by
  rw [barySup, dite_eq_left ⟨τ, hτ⟩]
  exact Finset.le_sup' (fun τ => ‖bary τ‖) hτ

/-! ## `Low` and `High` are compact -/

private theorem isCompact_closedCube' (r : ℝ) : IsCompact (PL.closedCube (n := n) r) := by
  have h : PL.closedCube (n := n) r
      = (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)) ⁻¹'
          (Set.pi Set.univ (fun _ : Fin n => Set.Icc (-r) r)) := by
    ext x
    simp only [Set.mem_preimage, PL.closedCube, Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ,
      true_implies, Set.mem_Icc, abs_le]
    exact ⟨fun hx i => hx i, fun hx i => hx i⟩
  rw [h]
  exact (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)).isCompact_preimage.mpr
    (isCompact_univ_pi fun _ => isCompact_Icc)

private theorem isClosed_Low (P : PL.Cx n) (hP : P.faces.Finite) (p : ℕ) :
    IsClosed (Low P p) := by
  have h : Low P p = ⋃ σ ∈ (hP.toFinset.filter (fun σ => σ.card ≤ p + 1)), PL.simp σ := by
    ext x; constructor
    · rintro ⟨s, hs, hc, hxs⟩
      exact mem_iUnion₂.mpr ⟨s, Finset.mem_filter.mpr
        ⟨(Set.Finite.mem_toFinset hP).mpr hs, hc⟩, hxs⟩
    · intro hx
      obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
      exact ⟨s, (Set.Finite.mem_toFinset hP).mp (Finset.mem_filter.mp hs).1,
        (Finset.mem_filter.mp hs).2, hxs⟩
  rw [h]
  exact isClosed_biUnion_finset (fun σ _ => (Finset.finite_toSet σ).isClosed_convexHull ℝ)

private theorem isClosed_High (P : PL.Cx n) (hP : P.faces.Finite) (p : ℕ) :
    IsClosed (High P p) := by
  have h : High P p = ⋃ s ∈ highCover P hP p, PL.simp s := by
    apply Subset.antisymm (High_subset_highCover P hP p)
    intro x hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    rw [highCover, Finset.mem_image] at hs
    obtain ⟨T, hT, rfl⟩ := hs
    rw [Finset.mem_filter] at hT
    exact ⟨T, fun σ hσ => (Set.Finite.mem_toFinset hP).mp (Finset.mem_powerset.mp hT.1 hσ),
      hT.2.1, hT.2.2.1, hT.2.2.2, hxs⟩
  rw [h]
  exact isClosed_biUnion_finset (fun s _ => (Finset.finite_toSet s).isClosed_convexHull ℝ)

private theorem isCompact_Low (P : PL.Cx n) (hP : P.faces.Finite) {β : ℝ}
    (hsp : P.space = PL.closedCube β) (p : ℕ) : IsCompact (Low P p) :=
  IsCompact.of_isClosed_subset (isCompact_closedCube' β) (isClosed_Low P hP p)
    (by rw [← hsp]; exact Low_subset_space P p)

private theorem isCompact_High (P : PL.Cx n) (hP : P.faces.Finite) {β : ℝ}
    (hsp : P.space = PL.closedCube β) (p : ℕ) : IsCompact (High P p) :=
  IsCompact.of_isClosed_subset (isCompact_closedCube' β) (isClosed_High P hP p)
    (by rw [← hsp]; exact High_subset_space P p)

/-! ## The simplex-preservation -/

private theorem sum_mem_simp_carrier (P : PL.Cx n) (hP : P.faces.Finite) {x : PL.E n}
    {s : Finset (Finset (PL.E n))} {w : Finset (PL.E n) → ℝ}
    (hw0 : ∀ τ ∈ s, 0 ≤ w τ) (hw1 : ∑ τ ∈ s, w τ = 1)
    (hne : ∀ τ ∈ s, τ.Nonempty) (hsub : ∀ τ ∈ s, τ ⊆ carrier P x) :
    (∑ τ ∈ s, w τ • bary τ) ∈ PL.simp (carrier P x) :=
  Convex.sum_mem (convex_convexHull ℝ _) hw0 hw1
    (fun τ hτ => simp_mono (hsub τ hτ) (bary_mem_simp (hne τ hτ)))

private theorem massG_pos_subset_carrier' (P : PL.Cx n) (hP : P.faces.Finite) {x : PL.E n}
    (hx : x ∈ P.space) {τ : Finset (PL.E n)} (h : 0 < massG P hP x τ) :
    τ ⊆ carrier P x := by
  by_contra hsub
  exact (ne_of_gt h) ((massG_api P hP hx).2.2.2.1 τ hsub)

private theorem massG_pos_nonempty (P : PL.Cx n) (hP : P.faces.Finite) {x : PL.E n}
    (hx : x ∈ P.space) {τ : Finset (PL.E n)} (h : 0 < massG P hP x τ) : τ.Nonempty :=
  Geometry.SimplicialComplex.nonempty_of_mem_faces ((massG_api P hP hx).2.2.2.2.2 τ h)

private theorem sum_filter_low_massG (P : PL.Cx n) (hP : P.faces.Finite) {β : ℝ} {p : ℕ}
    {x : PL.E n} (hx : x ∈ P.space) :
    (∑ τ ∈ (cands P hP).filter (fun τ => LowFace β p τ ∧ 0 < massG P hP x τ),
        massG P hP x τ) = 1 - SOf β p P hP x := by
  have h1 : (∑ τ ∈ cands P hP, (if LowFace β p τ then massG P hP x τ else (0:ℝ)))
      = ∑ τ ∈ (cands P hP).filter (fun τ => LowFace β p τ), massG P hP x τ := by
    rw [Finset.sum_filter]
  rw [← sum_low_massG P hP (β := β) (p := p) hx, h1]
  refine Finset.sum_subset ?_ ?_
  · intro τ hτ
    rw [Finset.mem_filter] at hτ ⊢
    exact ⟨hτ.1, hτ.2.1⟩
  · intro τ hτ hτ'
    rw [Finset.mem_filter] at hτ
    have hz : massG P hP x τ = 0 := le_antisymm
      (not_lt.mp fun hp => hτ' (Finset.mem_filter.mpr ⟨hτ.1, hτ.2, hp⟩)) (le_max_left 0 _)
    rw [hz]

private theorem sum_filter_high_massG (P : PL.Cx n) (hP : P.faces.Finite) {β : ℝ} {p : ℕ}
    {x : PL.E n} :
    (∑ τ ∈ (cands P hP).filter (fun τ => ¬ LowFace β p τ ∧ 0 < massG P hP x τ),
        massG P hP x τ) = SOf β p P hP x := by
  have h1 : (∑ τ ∈ cands P hP, (if LowFace β p τ then (0:ℝ) else massG P hP x τ))
      = ∑ τ ∈ (cands P hP).filter (fun τ => ¬ LowFace β p τ), massG P hP x τ := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    by_cases hL : LowFace β p τ <;> simp [hL]
  rw [SOf, h1]
  refine Finset.sum_subset ?_ ?_
  · intro τ hτ
    rw [Finset.mem_filter] at hτ ⊢
    exact ⟨hτ.1, hτ.2.1⟩
  · intro τ hτ hτ'
    rw [Finset.mem_filter] at hτ
    have hz : massG P hP x τ = 0 := le_antisymm
      (not_lt.mp fun hp => hτ' (Finset.mem_filter.mpr ⟨hτ.1, hτ.2, hp⟩)) (le_max_left 0 _)
    rw [hz]

private theorem AOf_eq_sum (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ)
    {x : PL.E n} (hx : x ∈ P.space) :
    AOf β p P hP x = ∑ τ ∈ (cands P hP).filter (fun τ => LowFace β p τ ∧ 0 < massG P hP x τ),
      massG P hP x τ • bary τ := by
  rw [AOf, ← Finset.sum_filter]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro τ hτ
    rw [Finset.mem_filter] at hτ ⊢
    exact ⟨hτ.1, hτ.2.1⟩
  · intro τ hτ hτ'
    rw [Finset.mem_filter] at hτ
    have hz : massG P hP x τ = 0 := le_antisymm
      (not_lt.mp fun hp => hτ' (Finset.mem_filter.mpr ⟨hτ.1, hτ.2, hp⟩)) (le_max_left 0 _)
    rw [hz, zero_smul]

private theorem BOf_eq_sum (P : PL.Cx n) (hP : P.faces.Finite) (β : ℝ) (p : ℕ)
    {x : PL.E n} :
    BOf β p P hP x = ∑ τ ∈ (cands P hP).filter (fun τ => ¬ LowFace β p τ ∧ 0 < massG P hP x τ),
      massG P hP x τ • bary τ := by
  have h1 : BOf β p P hP x = ∑ τ ∈ (cands P hP).filter (fun τ => ¬ LowFace β p τ),
      massG P hP x τ • bary τ := by
    rw [BOf, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun τ _ => ?_)
    by_cases hL : LowFace β p τ <;> simp [hL]
  rw [h1]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro τ hτ
    rw [Finset.mem_filter] at hτ ⊢
    exact ⟨hτ.1, hτ.2.1⟩
  · intro τ hτ hτ'
    rw [Finset.mem_filter] at hτ
    have hz : massG P hP x τ = 0 := le_antisymm
      (not_lt.mp fun hp => hτ' (Finset.mem_filter.mpr ⟨hτ.1, hτ.2, hp⟩)) (le_max_left 0 _)
    rw [hz, zero_smul]

private theorem uOf_mem_simp_carrier {β : ℝ} {p : ℕ} (P : PL.Cx n) (hP : P.faces.Finite)
    {x : PL.E n} (hx : x ∈ P.space) (hS : SOf β p P hP x ≠ 1) :
    uOf β p P hP x ∈ PL.simp (carrier P x) := by
  have hne : 1 - SOf β p P hP x ≠ 0 := sub_ne_zero.mpr (Ne.symm hS)
  have hpos : 0 < 1 - SOf β p P hP x := by
    have := lt_of_le_of_ne (SOf_le_one' P hP β p hx) hS
    linarith
  have hmem : (∑ τ ∈ (cands P hP).filter (fun τ => LowFace β p τ ∧ 0 < massG P hP x τ),
        ((1 - SOf β p P hP x)⁻¹ * massG P hP x τ) • bary τ) ∈ PL.simp (carrier P x) := by
    refine sum_mem_simp_carrier P hP (fun τ hτ => ?_) ?_
      (fun τ hτ => massG_pos_nonempty P hP hx (Finset.mem_filter.mp hτ).2.2)
      (fun τ hτ => massG_pos_subset_carrier' P hP hx (Finset.mem_filter.mp hτ).2.2)
    · exact mul_nonneg (inv_nonneg.mpr (le_of_lt hpos)) (le_of_lt (Finset.mem_filter.mp hτ).2.2)
    · rw [← Finset.mul_sum, sum_filter_low_massG P hP (β := β) (p := p) hx, inv_mul_cancel₀ (ne_of_gt hpos)]
  rw [uOf, ite_eq_right hne, AOf_eq_sum P hP β p hx, Finset.smul_sum]
  convert hmem using 1
  exact Finset.sum_congr rfl (fun τ _ => by rw [smul_smul])

private theorem wOf_mem_simp_carrier {β : ℝ} {p : ℕ} (P : PL.Cx n) (hP : P.faces.Finite)
    {x : PL.E n} (hx : x ∈ P.space) (hS : SOf β p P hP x ≠ 0) :
    wOf β p P hP x ∈ PL.simp (carrier P x) := by
  have hmem : (∑ τ ∈ (cands P hP).filter (fun τ => ¬ LowFace β p τ ∧ 0 < massG P hP x τ),
        ((SOf β p P hP x)⁻¹ * massG P hP x τ) • bary τ) ∈ PL.simp (carrier P x) := by
    refine sum_mem_simp_carrier P hP (fun τ hτ => ?_) ?_
      (fun τ hτ => massG_pos_nonempty P hP hx (Finset.mem_filter.mp hτ).2.2)
      (fun τ hτ => massG_pos_subset_carrier' P hP hx (Finset.mem_filter.mp hτ).2.2)
    · exact mul_nonneg (inv_nonneg.mpr (SOf_nonneg P hP β p x))
        (le_of_lt (Finset.mem_filter.mp hτ).2.2)
    · rw [← Finset.mul_sum, sum_filter_high_massG P hP, inv_mul_cancel₀ hS]
  rw [wOf, ite_eq_right hS, BOf_eq_sum P hP β p, Finset.smul_sum]
  convert hmem using 1
  exact Finset.sum_congr rfl (fun τ _ => by rw [smul_smul])

/-! ## The stretch maps simplices into their carrier -/

private theorem stretchM_mem_simp_carrier {β : ℝ} {p : ℕ} (P : PL.Cx n) (hP : P.faces.Finite)
    {Mb : PL.E n → ℝ} {x : PL.E n} (hx : x ∈ P.space) (hMb : 0 < Mb x) :
    stretchM β p P hP Mb x ∈ PL.simp (carrier P x) := by
  by_cases hS0 : SOf β p P hP x = 0
  · rw [stretchM_eq_self_of_SOf_eq_zero (β := β) (p := p) P hP hx hS0]
    exact (carrier_spec P hP hx).2.1
  by_cases hS1 : SOf β p P hP x = 1
  · rw [stretchM_eq_self_of_SOf_eq_one (β := β) (p := p) P hP hx (ne_of_gt hMb) hS1]
    exact (carrier_spec P hP hx).2.1
  · have hSpos : 0 < SOf β p P hP x := lt_of_le_of_ne (SOf_nonneg P hP β p x) (Ne.symm hS0)
    have hSlt : SOf β p P hP x < 1 := lt_of_le_of_ne (SOf_le_one' P hP β p hx) hS1
    have hu := uOf_mem_simp_carrier P hP hx hS1
    have hw := wOf_mem_simp_carrier P hP hx hS0
    have hne1 : 1 - SOf β p P hP x ≠ 0 := sub_ne_zero.mpr (Ne.symm hS1)
    have hAu : AOf β p P hP x = (1 - SOf β p P hP x) • uOf β p P hP x := by
      rw [uOf, ite_eq_right hne1, smul_smul, mul_inv_cancel₀ hne1, one_smul]
    have hBw : BOf β p P hP x = SOf β p P hP x • wOf β p P hP x := by
      rw [wOf, ite_eq_right hS0, smul_smul, mul_inv_cancel₀ hS0, one_smul]
    have hrepr : stretchM β p P hP Mb x
        = (1 + (Mb x - 1) * SOf β p P hP x)⁻¹ •
            (AOf β p P hP x + Mb x • BOf β p P hP x) := by
      unfold stretchM; rw [ite_eq_left hx]
    rw [hrepr, hAu, hBw]
    have hden : (1:ℝ) + (Mb x - 1) * SOf β p P hP x
        = (1 - SOf β p P hP x) + Mb x * SOf β p P hP x := by ring
    have hdenpos : 0 < (1 - SOf β p P hP x) + Mb x * SOf β p P hP x :=
      add_pos_of_nonneg_of_pos (sub_nonneg.mpr (SOf_le_one' P hP β p hx)) (mul_pos hMb hSpos)
    rw [hden]
    have hsplit : ((1 - SOf β p P hP x) + Mb x * SOf β p P hP x)⁻¹ •
          ((1 - SOf β p P hP x) • uOf β p P hP x
            + Mb x • (SOf β p P hP x • wOf β p P hP x))
        = ((1 - SOf β p P hP x) / ((1 - SOf β p P hP x) + Mb x * SOf β p P hP x)) •
            uOf β p P hP x
          + (Mb x * SOf β p P hP x / ((1 - SOf β p P hP x) + Mb x * SOf β p P hP x)) •
            wOf β p P hP x := by
      module
    rw [hsplit]
    refine convex_convexHull ℝ _ hu hw
      (div_nonneg (le_of_lt (sub_pos.mpr hSlt)) (le_of_lt hdenpos))
      (div_nonneg (mul_nonneg (le_of_lt hMb) (le_of_lt hSpos)) (le_of_lt hdenpos)) ?_
    rw [← add_div]
    exact div_self (ne_of_gt hdenpos)

private theorem stretch_mem_of_mem_simp {β α M : ℝ} {p : ℕ} (P : PL.Cx n) (hP : P.faces.Finite)
    (hM : 0 < M) {s : Finset (PL.E n)} (hs : s ∈ P.faces) {x : PL.E n} (hx : x ∈ PL.simp s) :
    stretch P hP β p α M x ∈ PL.simp s :=
  simp_mono ((carrier_spec P hP (Geometry.SimplicialComplex.convexHull_subset_space hs hx)).2.2 s hs hx)
    (stretchM_mem_simp_carrier P hP (Geometry.SimplicialComplex.convexHull_subset_space hs hx)
      (taperM_pos hM p P hP x))

private theorem invTaper_mem_of_mem_simp {β α M : ℝ} {p : ℕ} (P : PL.Cx n) (hP : P.faces.Finite)
    (hM : 0 < M) {s : Finset (PL.E n)} (hs : s ∈ P.faces) {x : PL.E n} (hx : x ∈ PL.simp s) :
    stretchM β p P hP (fun z => (taperM β p P hP α M z)⁻¹) x ∈ PL.simp s :=
  simp_mono ((carrier_spec P hP (Geometry.SimplicialComplex.convexHull_subset_space hs hx)).2.2 s hs hx)
    (stretchM_mem_simp_carrier P hP (Geometry.SimplicialComplex.convexHull_subset_space hs hx)
      (inv_pos.mpr (taperM_pos hM p P hP x)))

/-- The taper equals `M` on the smaller cube. -/
private theorem taperM_eq_M_of_mem_closedCube {β α M : ℝ} {p : ℕ} (hn : 0 < n) (P : PL.Cx n)
    (hP : P.faces.Finite) (hsp : P.space = PL.closedCube β) (hαβ : α < β) (hM : 1 ≤ M)
    {x : PL.E n} (hx : x ∈ P.space) (hxα : x ∈ PL.closedCube α) :
    taperM β p P hP α M x = M := by
  obtain ⟨-, -, h3⟩ := taperM_props hn P hP hαβ hM
  refine h3 x ⟨SOf β p P hP x, ⟨SOf_nonneg P hP β p x, SOf_le_one' P hP β p hx⟩, ?_⟩
  show (1 - SOf β p P hP x) • uOf β p P hP x + SOf β p P hP x • wOf β p P hP x ∈ closedCube α
  rw [← join_decomp P hP hx]
  exact hxα

/-- Norm bound on the low endpoint. -/
private theorem norm_uOf_le {β : ℝ} {p : ℕ} (P : PL.Cx n) (hP : P.faces.Finite) {x : PL.E n}
    (hx : x ∈ P.space) {K : ℝ} (hK : ∀ τ ∈ cands P hP, ‖bary τ‖ ≤ K) :
    ‖uOf β p P hP x‖ ≤ K := by
  have hKnn : 0 ≤ K := le_trans (norm_nonneg _) (hK _ (cands_nonempty P hP hx).choose_spec)
  by_cases hS : 1 - SOf β p P hP x = 0
  · rw [uOf, ite_eq_left hS]
    simpa using hKnn
  · have hpos : 0 < 1 - SOf β p P hP x :=
      lt_of_le_of_ne (sub_nonneg.mpr (SOf_le_one' P hP β p hx)) (Ne.symm hS)
    rw [uOf, ite_eq_right hS, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr
      (le_of_lt hpos))]
    calc (1 - SOf β p P hP x)⁻¹ * ‖AOf β p P hP x‖
        ≤ (1 - SOf β p P hP x)⁻¹ * ((1 - SOf β p P hP x) * K) :=
          mul_le_mul_of_nonneg_left (norm_AOf_le P hP β p hx hK) (inv_nonneg.mpr (le_of_lt hpos))
      _ = K := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]

/-- Norm bound on the high endpoint. -/
private theorem norm_wOf_le {β : ℝ} {p : ℕ} (P : PL.Cx n) (hP : P.faces.Finite) {x : PL.E n}
    (hx : x ∈ P.space) {K : ℝ} (hK : ∀ τ ∈ cands P hP, ‖bary τ‖ ≤ K) :
    ‖wOf β p P hP x‖ ≤ K := by
  have hKnn : 0 ≤ K := le_trans (norm_nonneg _) (hK _ (cands_nonempty P hP hx).choose_spec)
  by_cases hS : SOf β p P hP x = 0
  · rw [wOf, ite_eq_left hS]
    simpa using hKnn
  · have hpos : 0 < SOf β p P hP x := lt_of_le_of_ne (SOf_nonneg P hP β p x) (Ne.symm hS)
    rw [wOf, ite_eq_right hS, norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr
      (le_of_lt hpos))]
    calc (SOf β p P hP x)⁻¹ * ‖BOf β p P hP x‖
        ≤ (SOf β p P hP x)⁻¹ * (SOf β p P hP x * K) :=
          mul_le_mul_of_nonneg_left (norm_BOf_le P hP β p hx hK) (inv_nonneg.mpr (le_of_lt hpos))
      _ = K := by rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]

/-- The high skeleton contains the points of full high mass. -/
private theorem mem_High_of_SOf_eq_one {β : ℝ} {p : ℕ} (P : PL.Cx n) (hP : P.faces.Finite)
    {x : PL.E n} (hx : x ∈ P.space) (hS : SOf β p P hP x = 1) : x ∈ High P p := by
  have hSpos : 0 < SOf β p P hP x := by rw [hS]; norm_num
  have hw := wOf_mem_high P hP hx hSpos
  have hA : AOf β p P hP x = 0 := sfo_AOf_eq_zero_of_SOf_eq_one P hP hx hS
  have hB : BOf β p P hP x = x := by
    have h := AOf_add_BOf (β := β) (p := p) P hP hx
    rw [hA, zero_add] at h
    exact h
  have hwx : wOf β p P hP x = x := by
    rw [wOf, ite_eq_right (ne_of_gt hSpos), hB, hS, inv_one, one_smul]
  rwa [← hwx]

private lemma scalar_inv_mul_sub {M S : ℝ} (hM : 1 ≤ M) (h0 : 0 < S) (h1 : S ≤ 1) :
    (1 + (M⁻¹ - 1) * S)⁻¹ * (M⁻¹ * S) = S / (M * (1 - S) + S) := by
  have hM0 : M ≠ 0 := by linarith
  have hc1 : (1:ℝ) + (M⁻¹ - 1) * S = (1 - S) + S * M⁻¹ := by ring
  have hden : M * (1 - S) + S = M * (1 + (M⁻¹ - 1) * S) := by
    rw [hc1, mul_add, show M * (S * M⁻¹) = S by
      rw [mul_comm S M⁻¹, ← mul_assoc, mul_inv_cancel₀ hM0, one_mul]]
  rw [hden, div_eq_mul_inv, mul_inv_rev]
  ring

private lemma scalar_inv_mul_mul {M S : ℝ} (hM : 1 ≤ M) (h0 : 0 < S) (h1 : S ≤ 1) :
    ((1 + (M⁻¹ - 1) * S)⁻¹ * M⁻¹) * S = S / (M * (1 - S) + S) := by
  rw [mul_assoc]
  exact scalar_inv_mul_sub hM h0 h1

private lemma scalar_inv_mul_one_sub {M S : ℝ} (hM : 1 ≤ M) (h0 : 0 < S) (h1 : S ≤ 1) :
    (1 + (M⁻¹ - 1) * S)⁻¹ * (1 - S) = 1 - S / (M * (1 - S) + S) := by
  have hM0 : M ≠ 0 := by linarith
  have hc1 : (1:ℝ) + (M⁻¹ - 1) * S = (1 - S) + S * M⁻¹ := by ring
  have hc0 : (1 - S) + S * M⁻¹ ≠ 0 := by
    rw [← hc1]
    have h4 : M⁻¹ - 1 ≤ 0 := by rw [sub_nonpos]; exact inv_le_one_of_one_le₀ hM
    have h5 : (1:ℝ) + (M⁻¹ - 1) * S ≥ M⁻¹ := by
      nlinarith [mul_le_mul_of_nonpos_left h1 h4, h4]
    have : 0 < M⁻¹ := inv_pos.mpr (by linarith)
    linarith
  have hden : M * (1 - S) + S = M * (1 + (M⁻¹ - 1) * S) := by
    rw [hc1, mul_add, show M * (S * M⁻¹) = S by
      rw [mul_comm S M⁻¹, ← mul_assoc, mul_inv_cancel₀ hM0, one_mul]]
  have hD : ((1 - S) + S * M⁻¹) * ((1 - S) + S * M⁻¹)⁻¹ = 1 := mul_inv_cancel₀ hc0
  rw [hden, div_eq_mul_inv, mul_inv_rev, hc1]
  linear_combination hD

/-- The displacement of the reciprocal-taper stretch from the low endpoint. -/
private theorem invTaper_apply_sub_uOf {β α M : ℝ} {p : ℕ} (hn : 0 < n) (P : PL.Cx n)
    (hP : P.faces.Finite) (hsp : P.space = PL.closedCube β) (hαβ : α < β) (hM : 1 ≤ M)
    {x : PL.E n} (hx : x ∈ P.space) (hxα : x ∈ PL.closedCube α)
    (hS0 : SOf β p P hP x ≠ 0) (hS1 : SOf β p P hP x ≠ 1) :
    stretchM β p P hP (fun z => (taperM β p P hP α M z)⁻¹) x - uOf β p P hP x
      = (SOf β p P hP x / (M * (1 - SOf β p P hP x) + SOf β p P hP x)) •
          (wOf β p P hP x - uOf β p P hP x) := by
  have hM0 : 0 < M := by linarith
  have htM : taperM β p P hP α M x = M :=
    taperM_eq_M_of_mem_closedCube hn P hP hsp hαβ hM hx hxα
  have hne1 : 1 - SOf β p P hP x ≠ 0 := sub_ne_zero.mpr (Ne.symm hS1)
  have hAu : AOf β p P hP x = (1 - SOf β p P hP x) • uOf β p P hP x := by
    rw [uOf, ite_eq_right hne1, smul_smul, mul_inv_cancel₀ hne1, one_smul]
  have hBw : BOf β p P hP x = SOf β p P hP x • wOf β p P hP x := by
    rw [wOf, ite_eq_right hS0, smul_smul, mul_inv_cancel₀ hS0, one_smul]
  have hab : AOf β p P hP x + BOf β p P hP x = x := AOf_add_BOf P hP hx
  unfold stretchM
  rw [ite_eq_left hx]
  simp only [htM, hAu, hBw]
  have hSpos : 0 < SOf β p P hP x := lt_of_le_of_ne (SOf_nonneg P hP β p x) (Ne.symm hS0)
  have hSle : SOf β p P hP x ≤ 1 := SOf_le_one' P hP β p hx
  have hs1 := scalar_inv_mul_mul (M := M) (S := SOf β p P hP x) hM hSpos hSle
  have hs2 := scalar_inv_mul_one_sub (M := M) (S := SOf β p P hP x) hM hSpos hSle
  rw [smul_add, smul_sub, smul_smul, smul_smul, smul_smul]
  rw [show ((1 + (M⁻¹ - 1) * SOf β p P hP x)⁻¹ * M⁻¹) * SOf β p P hP x
      = SOf β p P hP x / (M * (1 - SOf β p P hP x) + SOf β p P hP x) from
    scalar_inv_mul_mul hM hSpos hSle]
  rw [show (1 + (M⁻¹ - 1) * SOf β p P hP x)⁻¹ * (1 - SOf β p P hP x)
      = 1 - SOf β p P hP x / (M * (1 - SOf β p P hP x) + SOf β p P hP x) from
    scalar_inv_mul_one_sub hM hSpos hSle]
  module


/-- The reciprocal-taper stretch fixes the points outside the open cube. -/
private theorem invTaper_stretch_eq_self {β α M : ℝ} {p : ℕ} (P : PL.Cx n) (hP : P.faces.Finite)
    (hM : 1 ≤ M) (hsp : P.space = closedCube β) {x : PL.E n} (hx : x ∈ P.space)
    (hx' : x ∉ PL.openCube β) :
    stretchM β p P hP (fun z => (taperM β p P hP α M z)⁻¹) x = x := by
  by_cases hS0 : SOf β p P hP x = 0
  · exact stretchM_eq_self_of_SOf_eq_zero P hP hx hS0
  by_cases hS1 : SOf β p P hP x = 1
  · exact stretchM_eq_self_of_SOf_eq_one P hP hx
      (inv_ne_zero (ne_of_gt (taperM_pos (by linarith : (0:ℝ) < M) p P hP x))) hS1
  · have hbd := sfo_mem_bdryCube hsp hx hx'
    obtain ⟨i, hi⟩ := hbd
    have hseg := sfo_segOf_mem_BdrySeg hsp hx hi hS0 hS1
    have ht1 : taperM β p P hP α M x = 1 := sfo_taperM_eq_one_of_segOf_mem P hP hseg
    unfold stretchM
    rw [ite_eq_left hx]
    simp only [ht1, inv_one, sub_self, zero_mul, add_zero, one_mul, one_smul]
    exact AOf_add_BOf (β := β) (p := p) P hP hx

private theorem continuous_stretch {β α M : ℝ} {p : ℕ} (P : PL.Cx n) (hP : P.faces.Finite)
    (hM : 1 ≤ M) (hsp : P.space = closedCube β) :
    Continuous (fun x : PL.E n => stretch P hP β p α M x) :=
  continuous_of_continuousOn_fix P hP hsp
    (fun x hx => by simp only [stretch, stretchM, ite_eq_right hx])
    (continuousOn_stretch P hP hM (fun τ hτ => le_barySup P hP hτ))
    (fun x hx hx' => stretch_fix_outside P hP hM hsp hx')

private theorem continuous_stretchM_invTaper {β α M : ℝ} {p : ℕ} (P : PL.Cx n)
    (hP : P.faces.Finite) (hM : 1 ≤ M) (hsp : P.space = closedCube β) :
    Continuous (fun x : PL.E n => stretchM β p P hP (fun z => (taperM β p P hP α M z)⁻¹) x) :=
  continuous_of_continuousOn_fix P hP hsp
    (fun x hx => by simp only [stretchM, ite_eq_right hx])
    (continuousOn_invTaper P hP hM (fun τ hτ => le_barySup P hP hτ))
    (fun x hx hx' => invTaper_stretch_eq_self P hP hM hsp hx hx')



end Work.Geo.DualStretch

namespace Work.Geo.DualStretch

open _root_.PL (E Cx closedCube openCube)

private lemma mem_thickening_of_dist_lt {n : ℕ} {s : Set (PL.E n)} {δ : ℝ} {x z : PL.E n}
    (hz : z ∈ s) (hδ : 0 < δ) (h : dist x z < δ) : x ∈ Metric.thickening δ s :=
  lt_of_le_of_lt (Metric.infEDist_le_edist_of_mem hz)
    (by rw [edist_dist]; exact (ENNReal.ofReal_lt_ofReal_iff hδ).mpr h)

theorem dual_stretch {n p : ℕ} (hp : p < n) (β α : ℝ) (hα : 0 < α) (hαβ : α < β)
    (P : PL.Cx n) (hP : P.faces.Finite) (hsp : P.space = PL.closedCube β)
    (N₁ N₂ : Set (PL.E n)) (h₁ : IsOpen N₁) (h₂ : IsOpen N₂)
    (hL : Work.Geo.DualStretch.Low P p ⊆ N₁) (hH : Work.Geo.DualStretch.High P p ⊆ N₂) :
    ∃ h : PL.E n ≃ₜ PL.E n, (∀ x ∉ PL.openCube β, h x = x) ∧
      (∀ s ∈ P.faces, h '' PL.simp s = PL.simp s) ∧
      PL.closedCube α ⊆ h '' N₁ ∪ N₂ := by
  classical
  have hn : 0 < n := lt_of_le_of_lt (Nat.zero_le p) hp
  have hclαβ : PL.closedCube (n := n) α ⊆ PL.closedCube (n := n) β :=
    fun x hx i => le_trans (hx i) (le_of_lt hαβ)
  by_cases hN₁ : P.space ⊆ N₁
  · refine ⟨Homeomorph.refl (PL.E n), ?_, ?_, ?_⟩
    · intro x hx; rfl
    · intro s hs; exact Set.image_id _
    · intro x hx
      exact Or.inl (by simpa using hN₁ (by rw [hsp]; exact hclαβ hx))
  by_cases hN₂ : P.space ⊆ N₂
  · refine ⟨Homeomorph.refl (PL.E n), ?_, ?_, ?_⟩
    · intro x hx; rfl
    · intro s hs; exact Set.image_id _
    · intro x hx
      exact Or.inr (by simpa using hN₂ (by rw [hsp]; exact hclαβ hx))
  obtain ⟨δ₁, hδ₁, hth₁⟩ := (isCompact_Low P hP hsp p).exists_thickening_subset_open h₁ hL
  obtain ⟨δ₂, hδ₂, hth₂⟩ := (isCompact_High P hP hsp p).exists_thickening_subset_open h₂ hH
  have hδ₁' : 0 < δ₁ := hδ₁
  have hδ₂' : 0 < δ₂ := hδ₂
  obtain ⟨M, hM1, hMbig⟩ : ∃ M : ℝ, 1 ≤ M ∧ (2 * barySup P hP) ^ 2 / (δ₁ * δ₂) < M := by
    refine ⟨max 1 ((2 * barySup P hP) ^ 2 / (δ₁ * δ₂) + 1), le_max_left _ _, ?_⟩
    linarith [le_max_right 1 ((2 * barySup P hP) ^ 2 / (δ₁ * δ₂) + 1)]
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM1
  have hcont₁ : Continuous (fun x : PL.E n => stretch P hP β p α M x) :=
    continuous_stretch (α := α) (p := p) (M := M) P hP hM1 hsp
  have hcont₂ : Continuous (fun x : PL.E n =>
      stretchM β p P hP (fun z => (taperM β p P hP α M z)⁻¹) x) :=
    continuous_stretchM_invTaper (α := α) (p := p) (M := M) P hP hM1 hsp
  let h : PL.E n ≃ₜ PL.E n :=
    { toFun := fun x => stretch P hP β p α M x
      invFun := fun x => stretchM β p P hP (fun z => (taperM β p P hP α M z)⁻¹) x
      left_inv := fun x => by
        by_cases hx : x ∈ P.space
        · exact stretch_inv P hP hM0 hx
        · simp only [stretch, stretchM, ite_eq_right hx]
      right_inv := fun x => by
        by_cases hx : x ∈ P.space
        · exact stretch_inv_right P hP hM0 hx
        · simp only [stretch, stretchM, ite_eq_right hx]
      continuous_toFun := hcont₁
      continuous_invFun := hcont₂ }
  refine ⟨h, ?_, ?_, ?_⟩
  · intro x hx
    exact stretch_fix_outside P hP hM1 hsp hx
  · intro s hs
    apply Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact stretch_mem_of_mem_simp P hP hM0 hs hx
    · intro y hy
      refine ⟨h.symm y, ?_, h.apply_symm_apply y⟩
      exact invTaper_mem_of_mem_simp P hP hM0 hs hy
  · intro x hxcl
    have hxsp : x ∈ P.space := by rw [hsp]; exact hclαβ hxcl
    by_cases hxN₂ : x ∈ N₂
    · exact Or.inr hxN₂
    · refine Or.inl ⟨h.symm x, ?_, h.apply_symm_apply x⟩
      have hK : ∀ τ ∈ cands P hP, ‖bary τ‖ ≤ barySup P hP :=
        fun τ hτ => le_barySup P hP hτ
      have hKnn : 0 ≤ barySup P hP :=
        le_trans (norm_nonneg _) (hK _ (cands_nonempty P hP hxsp).choose_spec)
      have hsymm : h.symm x = stretchM β p P hP (fun z => (taperM β p P hP α M z)⁻¹) x := rfl
      by_cases hS0 : SOf β p P hP x = 0
      · have hx1 : SOf β p P hP x < 1 := by rw [hS0]; norm_num
        have hulow : uOf β p P hP x ∈ Low P p :=
          uOf_mem_low P hP hsp hαβ hxsp hxcl hx1
        have hux : uOf β p P hP x = x := by
          have hj : x = (1 - SOf β p P hP x) • uOf β p P hP x
              + SOf β p P hP x • wOf β p P hP x := join_decomp P hP hxsp
          rw [hS0, zero_smul, add_zero, sub_zero, one_smul] at hj
          exact hj.symm
        rw [hsymm, stretchM_eq_self_of_SOf_eq_zero P hP hxsp hS0]
        refine hth₁ (mem_thickening_of_dist_lt hulow hδ₁' ?_)
        rw [hux, dist_self]
        exact hδ₁'
      · have hS1 : SOf β p P hP x ≠ 1 := fun hh =>
          hxN₂ (hH (mem_High_of_SOf_eq_one P hP hxsp hh))
        have hSpos : 0 < SOf β p P hP x :=
          lt_of_le_of_ne (SOf_nonneg P hP β p x) (Ne.symm hS0)
        have hSlt : SOf β p P hP x < 1 :=
          lt_of_le_of_ne (SOf_le_one' P hP β p hxsp) hS1
        have hulow : uOf β p P hP x ∈ Low P p :=
          uOf_mem_low P hP hsp hαβ hxsp hxcl hSlt
        have hwhigh : wOf β p P hP x ∈ High P p := wOf_mem_high P hP hxsp hSpos
        have hjoin : x = (1 - SOf β p P hP x) • uOf β p P hP x
            + SOf β p P hP x • wOf β p P hP x := join_decomp P hP hxsp
        have hge : δ₂ ≤ dist x (wOf β p P hP x) := by
          by_contra hlt
          push Not at hlt
          exact hxN₂ (hth₂ (mem_thickening_of_dist_lt hwhigh hδ₂' hlt))
        have huw : dist (wOf β p P hP x) (uOf β p P hP x) ≤ 2 * barySup P hP := by
          rw [dist_eq_norm]
          calc ‖wOf β p P hP x - uOf β p P hP x‖
              ≤ ‖wOf β p P hP x‖ + ‖uOf β p P hP x‖ := norm_sub_le _ _
            _ ≤ barySup P hP + barySup P hP :=
                add_le_add (norm_wOf_le P hP hxsp hK) (norm_uOf_le P hP hxsp hK)
            _ = 2 * barySup P hP := by ring
        have hxw : ‖x - wOf β p P hP x‖ = (1 - SOf β p P hP x) * dist (wOf β p P hP x) (uOf β p P hP x) := by
          have hvec : x - wOf β p P hP x
              = (1 - SOf β p P hP x) • (uOf β p P hP x - wOf β p P hP x) := by
            nth_rewrite 1 [hjoin]
            module
          rw [hvec, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (sub_nonneg.mpr (le_of_lt hSlt)), dist_eq_norm, norm_sub_rev]
        have hge2 : δ₂ ≤ (1 - SOf β p P hP x) * (2 * barySup P hP) := by
          have h1 : δ₂ ≤ ‖x - wOf β p P hP x‖ := by
            have := hge
            rwa [dist_eq_norm] at this
          rw [hxw] at h1
          calc δ₂ ≤ (1 - SOf β p P hP x) * dist (wOf β p P hP x) (uOf β p P hP x) := h1
            _ ≤ (1 - SOf β p P hP x) * (2 * barySup P hP) :=
                mul_le_mul_of_nonneg_left huw (sub_nonneg.mpr (le_of_lt hSlt))
        have hDpos : 0 < M * (1 - SOf β p P hP x) + SOf β p P hP x :=
          add_pos_of_pos_of_nonneg (mul_pos hM0 (sub_pos.mpr hSlt)) (le_of_lt hSpos)
        have hcoef : SOf β p P hP x / (M * (1 - SOf β p P hP x) + SOf β p P hP x)
            ≤ (2 * barySup P hP) / (M * δ₂) := by
          rw [div_le_div_iff₀ hDpos (by positivity : (0:ℝ) < M * δ₂)]
          rw [show SOf β p P hP x * (M * δ₂) = M * SOf β p P hP x * δ₂ by ring,
            show 2 * barySup P hP * (M * (1 - SOf β p P hP x) + SOf β p P hP x)
              = 2 * barySup P hP * M * (1 - SOf β p P hP x)
                + 2 * barySup P hP * SOf β p P hP x by ring]
          have h1 : M * SOf β p P hP x * δ₂
              ≤ M * SOf β p P hP x * ((1 - SOf β p P hP x) * (2 * barySup P hP)) :=
            mul_le_mul_of_nonneg_left hge2 (by positivity)
          have h2 : M * SOf β p P hP x * ((1 - SOf β p P hP x) * (2 * barySup P hP))
              ≤ 2 * barySup P hP * M * (1 - SOf β p P hP x)
                + 2 * barySup P hP * SOf β p P hP x := by
            have h3 : SOf β p P hP x * (1 - SOf β p P hP x) ≤ 1 - SOf β p P hP x :=
              mul_le_of_le_one_left (sub_nonneg.mpr (le_of_lt hSlt)) (le_of_lt hSlt)
            have h4 : M * (SOf β p P hP x * (1 - SOf β p P hP x))
                ≤ M * (1 - SOf β p P hP x) :=
              mul_le_mul_of_nonneg_left h3 (le_of_lt hM0)
            have h5 : (M * (SOf β p P hP x * (1 - SOf β p P hP x))) * (2 * barySup P hP)
                ≤ (M * (1 - SOf β p P hP x)) * (2 * barySup P hP) :=
              mul_le_mul_of_nonneg_right h4 (by positivity)
            have h6 : (M * (1 - SOf β p P hP x)) * (2 * barySup P hP)
                ≤ 2 * barySup P hP * M * (1 - SOf β p P hP x)
                  + 2 * barySup P hP * SOf β p P hP x := by
              have h7 : (0:ℝ) ≤ 2 * barySup P hP * SOf β p P hP x := by positivity
              nlinarith [h7]
            have h8 : M * SOf β p P hP x * ((1 - SOf β p P hP x) * (2 * barySup P hP))
                = (M * (SOf β p P hP x * (1 - SOf β p P hP x))) * (2 * barySup P hP) := by ring
            rw [h8]
            linarith [h5, h6]
          linarith [h1, h2]
        have hkey := invTaper_apply_sub_uOf hn P hP hsp hαβ hM1 hxsp hxcl hS0 hS1
        have hdist : dist (h.symm x) (uOf β p P hP x)
            ≤ ((2 * barySup P hP) ^ 2) / (M * δ₂) := by
          rw [hsymm, dist_eq_norm, hkey, norm_smul, Real.norm_eq_abs,
            abs_of_nonneg (div_nonneg (le_of_lt hSpos) (le_of_lt hDpos))]
          calc SOf β p P hP x / (M * (1 - SOf β p P hP x) + SOf β p P hP x)
                * ‖wOf β p P hP x - uOf β p P hP x‖
              ≤ ((2 * barySup P hP) / (M * δ₂)) * (2 * barySup P hP) :=
                mul_le_mul hcoef huw (norm_nonneg _) (by positivity)
            _ = (2 * barySup P hP) ^ 2 / (M * δ₂) := by ring
        have hfin : (2 * barySup P hP) ^ 2 / (M * δ₂) < δ₁ := by
          rw [div_lt_iff₀ (by positivity : (0:ℝ) < M * δ₂)]
          have hb := hMbig
          rw [div_lt_iff₀ (by positivity : (0:ℝ) < δ₁ * δ₂)] at hb
          nlinarith [hb]
        exact hth₁ (mem_thickening_of_dist_lt hulow hδ₁' (lt_of_le_of_lt hdist hfin))

end Work.Geo.DualStretch
