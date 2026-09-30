import Mathlib
import Submission.Work.Serre.SkelPi.Basic

/-!
# The spider of the `1`-skeleton is contractible

`spider X pt` (see `Submission/Work/Serre/SkelPi/Basic.lean`) is the base point together with the
outer halves of all the `1`-cells of the skeleton `Skel X pt`; it is an open neighbourhood of the
base point.  This file proves that it can be contracted to the base point, by an explicit homotopy
`H z t` which runs backwards the straight leg from the base point to `z`.

The leg is written with a *single continuous formula* on the model interval, so that the descent to
the quotient `Skel X pt` needs no gluing argument: with

* `clamp u = max (-1) (min 1 u)` and
* `phi x t = (1 - t) x + t * clamp (2 x)`  (`x : D¹`, `t : I`),

one has `phi x 0 = x`, `phi (±1) t = ±1` (so `phi` respects the gluing relation of the `1`-cells),
`phi x 1 = ±1` for `|x| ≥ 1/2` (so time `1` collapses the spider to the base point) and
`|phi x t| ≥ |x| > 1/2` for `|x| > 1/2` (so the spider is preserved).
-/

open scoped Topology unitInterval

namespace Work.Serre.SkelPi

noncomputable section

/-! ## The clamped profile on the model interval -/

/-- The clamped doubling `u ↦ max (-1) (min 1 u)`. -/
def clamp (u : ℝ) : ℝ := max (-1) (min 1 u)

theorem continuous_clamp : Continuous clamp := by
  unfold clamp
  exact continuous_const.max (continuous_const.min continuous_id)

theorem clamp_le_one (u : ℝ) : clamp u ≤ 1 := max_le (by norm_num) (min_le_left _ _)

theorem neg_one_le_clamp (u : ℝ) : -1 ≤ clamp u := le_max_left _ _

theorem clamp_eq_one {u : ℝ} (h : 1 ≤ u) : clamp u = 1 := by
  rw [clamp, min_eq_left h, max_eq_right (by norm_num : (-1 : ℝ) ≤ 1)]

theorem clamp_eq_neg_one {u : ℝ} (h : u ≤ -1) : clamp u = -1 := by
  rw [clamp, min_eq_right (by linarith : u ≤ 1), max_eq_left h]

/-- The model profile on the interval, as a real number. -/
def phiVal (x : Work.Serre.cellDiskOne) (t : unitInterval) : ℝ :=
  (1 - (t : ℝ)) * (x : ℝ) + (t : ℝ) * clamp (2 * (x : ℝ))

theorem phiVal_mem (x : Work.Serre.cellDiskOne) (t : unitInterval) :
    phiVal x t ∈ Metric.closedBall (0 : ℝ) 1 := by
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero, abs_le]
  have hx : (-1 : ℝ) ≤ (x : ℝ) ∧ (x : ℝ) ≤ 1 := abs_le.mp (abs_le_one x)
  have htl : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have h1t : (0 : ℝ) ≤ 1 - (t : ℝ) := by linarith [t.2.2]
  have hc1 : clamp (2 * (x : ℝ)) ≤ 1 := clamp_le_one _
  have hc2 : -1 ≤ clamp (2 * (x : ℝ)) := neg_one_le_clamp _
  constructor
  · have h1 : (1 - (t : ℝ)) * (-1) ≤ (1 - (t : ℝ)) * (x : ℝ) :=
      mul_le_mul_of_nonneg_left hx.1 h1t
    have h2 : (t : ℝ) * (-1) ≤ (t : ℝ) * clamp (2 * (x : ℝ)) :=
      mul_le_mul_of_nonneg_left hc2 htl
    simp only [phiVal]
    nlinarith [h1, h2]
  · have h1 : (1 - (t : ℝ)) * (x : ℝ) ≤ (1 - (t : ℝ)) * 1 :=
      mul_le_mul_of_nonneg_left hx.2 h1t
    have h2 : (t : ℝ) * clamp (2 * (x : ℝ)) ≤ (t : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hc1 htl
    simp only [phiVal]
    nlinarith [h1, h2]

/-- The model profile `phi : D¹ × I → D¹`. -/
def phi (x : Work.Serre.cellDiskOne) (t : unitInterval) : Work.Serre.cellDiskOne :=
  ⟨phiVal x t, phiVal_mem x t⟩

theorem phi_apply_coe (x : Work.Serre.cellDiskOne) (t : unitInterval) :
    ((phi x t : Work.Serre.cellDiskOne) : ℝ) = phiVal x t := rfl

theorem continuous_phiVal : Continuous fun p : Work.Serre.cellDiskOne × unitInterval =>
    phiVal p.1 p.2 := by
  simp only [phiVal]
  exact ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
      (continuous_subtype_val.comp continuous_fst)).add
    ((continuous_subtype_val.comp continuous_snd).mul
      (continuous_clamp.comp (continuous_const.mul
        (continuous_subtype_val.comp continuous_fst))))

theorem continuous_phi : Continuous fun p : Work.Serre.cellDiskOne × unitInterval =>
    phi p.1 p.2 :=
  Continuous.subtype_mk continuous_phiVal (fun p => phiVal_mem p.1 p.2)

/-! ## The elementary properties of the profile -/

theorem phi_zero (x : Work.Serre.cellDiskOne) : phi x 0 = x := by
  refine Subtype.ext ?_
  show phiVal x 0 = (x : ℝ)
  simp only [phiVal]
  rw [show ((0 : unitInterval) : ℝ) = 0 from rfl]
  ring

theorem phiVal_right (x : Work.Serre.cellDiskOne) (t : unitInterval)
    (hx : (1 : ℝ) / 2 < (x : ℝ)) :
    phiVal x t = (x : ℝ) + (t : ℝ) * (1 - (x : ℝ)) := by
  simp only [phiVal]
  rw [clamp_eq_one (by linarith : (1 : ℝ) ≤ 2 * (x : ℝ))]
  ring

theorem phiVal_left (x : Work.Serre.cellDiskOne) (t : unitInterval)
    (hx : (x : ℝ) < -(1 / 2)) :
    phiVal x t = (x : ℝ) - (t : ℝ) * (1 + (x : ℝ)) := by
  simp only [phiVal]
  rw [clamp_eq_neg_one (by linarith : 2 * (x : ℝ) ≤ -1)]
  ring

/-- A boundary point of the model interval is fixed by the profile at every time. -/
theorem phi_cellSphereZeroToDiskOne (z : Work.Serre.cellSphereZero) (t : unitInterval) :
    phi (Work.Serre.cellSphereZeroToDiskOne z) t = Work.Serre.cellSphereZeroToDiskOne z := by
  refine Subtype.ext ?_
  show phiVal (Work.Serre.cellSphereZeroToDiskOne z) t
    = ((Work.Serre.cellSphereZeroToDiskOne z : Work.Serre.cellDiskOne) : ℝ)
  have hz : (z : ℝ) = 1 ∨ (z : ℝ) = -1 := by
    have h : |(z : ℝ)| = 1 := by
      have hd : dist (z : ℝ) 0 = 1 := Metric.mem_sphere.mp z.2
      rwa [Real.dist_eq, sub_zero] at hd
    rcases abs_cases (z : ℝ) with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl (by rw [h1] at h; exact h)
    · exact Or.inr (by rw [h1] at h; linarith)
  have hcoe : ((Work.Serre.cellSphereZeroToDiskOne z : Work.Serre.cellDiskOne) : ℝ) = (z : ℝ) :=
    rfl
  rcases hz with hz | hz
  · rw [phiVal, hcoe, hz, clamp_eq_one (by norm_num : (1 : ℝ) ≤ 2 * 1)]
    ring
  · rw [phiVal, hcoe, hz, clamp_eq_neg_one (by norm_num : 2 * (-1 : ℝ) ≤ -1)]
    ring

/-- **The profile preserves the shell**: on the outer halves, `phi x t` is an endpoint of the
interval or lies again in the outer halves. -/
theorem phi_mem_shellSet_or {x : Work.Serre.cellDiskOne} (hx : x ∈ shellSet) (t : unitInterval) :
    phi x t = endL ∨ phi x t = endR ∨ phi x t ∈ shellSet := by
  have hx' := hx
  simp only [shellSet, Set.mem_ofPred_eq] at hx'
  rw [Real.norm_eq_abs] at hx'
  by_cases hle : (x : ℝ) ≤ 0
  · rw [abs_of_nonpos hle] at hx'
    have hlt' : (x : ℝ) < -(1 / 2) := by linarith [hx'.1]
    have hval : phiVal x t = (x : ℝ) - (t : ℝ) * (1 + (x : ℝ)) := phiVal_left x t hlt'
    have hlow : (-1 : ℝ) ≤ (x : ℝ) - (t : ℝ) * (1 + (x : ℝ)) := by
      have h1 : (t : ℝ) * (1 + (x : ℝ)) ≤ 1 + (x : ℝ) := by
        have hpos : (0 : ℝ) ≤ 1 + (x : ℝ) := by linarith [hx'.2]
        nlinarith [t.2.2, hpos]
      linarith
    have hupp : (x : ℝ) - (t : ℝ) * (1 + (x : ℝ)) ≤ (x : ℝ) := by
      have h1 : (0 : ℝ) ≤ (t : ℝ) * (1 + (x : ℝ)) := mul_nonneg t.2.1 (by linarith [hx'.2])
      linarith
    by_cases hv : (x : ℝ) - (t : ℝ) * (1 + (x : ℝ)) = -1
    · refine Or.inl ?_
      refine Subtype.ext ?_
      show phiVal x t = ((endL : Work.Serre.cellDiskOne) : ℝ)
      rw [hval, hv, endL_coe]
    · refine Or.inr (Or.inr ?_)
      have hv' : (-1 : ℝ) < (x : ℝ) - (t : ℝ) * (1 + (x : ℝ)) :=
        lt_of_le_of_ne hlow (Ne.symm hv)
      simp only [shellSet, Set.mem_ofPred_eq]
      constructor
      · rw [show ((phi x t : Work.Serre.cellDiskOne) : ℝ)
            = (x : ℝ) - (t : ℝ) * (1 + (x : ℝ)) from hval]
        rw [Real.norm_eq_abs, abs_of_neg (by linarith)]
        linarith
      · rw [show ((phi x t : Work.Serre.cellDiskOne) : ℝ)
            = (x : ℝ) - (t : ℝ) * (1 + (x : ℝ)) from hval]
        rw [Real.norm_eq_abs, abs_of_neg (by linarith)]
        linarith
  · have hlt : (0 : ℝ) < (x : ℝ) := lt_of_not_ge hle
    rw [abs_of_pos hlt] at hx'
    have hlt' : (1 : ℝ) / 2 < (x : ℝ) := hx'.1
    have hval : phiVal x t = (x : ℝ) + (t : ℝ) * (1 - (x : ℝ)) := phiVal_right x t hlt'
    have hlow : (x : ℝ) ≤ (x : ℝ) + (t : ℝ) * (1 - (x : ℝ)) := by
      have h1 : (0 : ℝ) ≤ (t : ℝ) * (1 - (x : ℝ)) := mul_nonneg t.2.1 (by linarith [hx'.2])
      linarith
    have hupp : (x : ℝ) + (t : ℝ) * (1 - (x : ℝ)) ≤ 1 := by
      have h1 : (t : ℝ) * (1 - (x : ℝ)) ≤ 1 * (1 - (x : ℝ)) :=
        mul_le_mul_of_nonneg_right t.2.2 (by linarith [hx'.2])
      linarith
    by_cases hv : (x : ℝ) + (t : ℝ) * (1 - (x : ℝ)) = 1
    · refine Or.inr (Or.inl ?_)
      refine Subtype.ext ?_
      show phiVal x t = ((endR : Work.Serre.cellDiskOne) : ℝ)
      rw [hval, hv, endR_coe]
    · refine Or.inr (Or.inr ?_)
      have hv' : (x : ℝ) + (t : ℝ) * (1 - (x : ℝ)) < 1 := lt_of_le_of_ne hupp hv
      simp only [shellSet, Set.mem_ofPred_eq]
      constructor
      · rw [show ((phi x t : Work.Serre.cellDiskOne) : ℝ)
            = (x : ℝ) + (t : ℝ) * (1 - (x : ℝ)) from hval]
        rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith
      · rw [show ((phi x t : Work.Serre.cellDiskOne) : ℝ)
            = (x : ℝ) + (t : ℝ) * (1 - (x : ℝ)) from hval]
        rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
        linarith

/-- At time `1` the profile sends the outer halves to the boundary points of the interval. -/
theorem phi_one_of_shellSet {x : Work.Serre.cellDiskOne} (hx : x ∈ shellSet) :
    phi x 1 = endL ∨ phi x 1 = endR := by
  have hx' := hx
  simp only [shellSet, Set.mem_ofPred_eq] at hx'
  rw [Real.norm_eq_abs] at hx'
  by_cases hle : (x : ℝ) ≤ 0
  · rw [abs_of_nonpos hle] at hx'
    have hlt' : (x : ℝ) < -(1 / 2) := by linarith [hx'.1]
    refine Or.inl ?_
    refine Subtype.ext ?_
    show phiVal x 1 = ((endL : Work.Serre.cellDiskOne) : ℝ)
    rw [phiVal_left x 1 hlt', endL_coe,
      show ((1 : unitInterval) : ℝ) = 1 from rfl]
    ring
  · have hlt : (0 : ℝ) < (x : ℝ) := lt_of_not_ge hle
    rw [abs_of_pos hlt] at hx'
    have hlt' : (1 : ℝ) / 2 < (x : ℝ) := hx'.1
    refine Or.inr ?_
    refine Subtype.ext ?_
    show phiVal x 1 = ((endR : Work.Serre.cellDiskOne) : ℝ)
    rw [phiVal_right x 1 hlt', endR_coe,
      show ((1 : unitInterval) : ℝ) = 1 from rfl]
    ring

/-! ## The map on representatives and its continuity -/

/-- The map induced on the representatives of the skeleton: the old part is fixed, and the
coordinate of a cell moves by `phi`. -/
def Gfun (X : Type) [TopologicalSpace X] (pt : X) :
    (PUnit ⊕ (Σ _ : Idx X pt, Work.Serre.cellDiskOne)) × unitInterval →
      (PUnit ⊕ (Σ _ : Idx X pt, Work.Serre.cellDiskOne)) :=
  fun p => match p.1 with
    | Sum.inl u => Sum.inl u
    | Sum.inr ⟨w, x⟩ => Sum.inr ⟨w, phi x p.2⟩

theorem continuous_Gfun (X : Type) [TopologicalSpace X] (pt : X) : Continuous (Gfun X pt) := by
  have hA : Continuous fun q : PUnit × unitInterval =>
      (Sum.inl q.1 : PUnit ⊕ (Σ _ : Idx X pt, Work.Serre.cellDiskOne)) :=
    continuous_inl.comp continuous_fst
  have hB : Continuous fun q : (Σ _ : Idx X pt, (Work.Serre.cellDiskOne × unitInterval)) =>
      (Sum.inr (⟨q.1, phi q.2.1 q.2.2⟩ : Σ _ : Idx X pt, Work.Serre.cellDiskOne) :
        PUnit ⊕ (Σ _ : Idx X pt, Work.Serre.cellDiskOne)) := by
    refine continuous_inr.comp ?_
    exact @Continuous.sigma_map (Idx X pt) (Idx X pt)
      (fun _ => Work.Serre.cellDiskOne × unitInterval) (fun _ => Work.Serre.cellDiskOne)
      (fun _ => inferInstance) (fun _ => inferInstance) id (fun _ q => phi q.1 q.2)
      (fun _ => continuous_phi)
  have hG : Gfun X pt =
      (Sum.elim (fun q : PUnit × unitInterval =>
          (Sum.inl q.1 : PUnit ⊕ (Σ _ : Idx X pt, Work.Serre.cellDiskOne)))
        ((fun q : (Σ _ : Idx X pt, (Work.Serre.cellDiskOne × unitInterval)) =>
          (Sum.inr (⟨q.1, phi q.2.1 q.2.2⟩ : Σ _ : Idx X pt, Work.Serre.cellDiskOne) :
            PUnit ⊕ (Σ _ : Idx X pt, Work.Serre.cellDiskOne)))
          ∘ ⇑(Homeomorph.sigmaProdDistrib))) ∘ ⇑(Homeomorph.sumProdDistrib) := by
    funext p
    obtain ⟨q, t⟩ := p
    rcases q with u | ⟨w, x⟩ <;>
      simp [Gfun, Homeomorph.sumProdDistrib_apply, Homeomorph.sigmaProdDistrib_apply]
  rw [hG]
  exact (hA.sumElim (hB.comp Homeomorph.sigmaProdDistrib.continuous)).comp
    Homeomorph.sumProdDistrib.continuous

theorem Gfun_eqvGen (X : Type) [TopologicalSpace X] (pt : X) (t : unitInterval)
    {a b : PUnit ⊕ (Σ _ : Idx X pt, Work.Serre.cellDiskOne)}
    (h : Relation.EqvGen (Work.Serre.oneCellRel PUnit (Idx X pt)
      (Work.Serre.E3aSk.skeletonAttach X pt)) a b) :
    Relation.EqvGen (Work.Serre.oneCellRel PUnit (Idx X pt)
      (Work.Serre.E3aSk.skeletonAttach X pt)) (Gfun X pt (a, t)) (Gfun X pt (b, t)) := by
  induction h with
  | rel x y hxy =>
    obtain ⟨i, z, rfl, rfl⟩ := hxy
    refine Relation.EqvGen.rel _ _ ⟨i, z, rfl, ?_⟩
    show Sum.inr (⟨i, phi (Work.Serre.cellSphereZeroToDiskOne z) t⟩ :
      Σ _ : Idx X pt, Work.Serre.cellDiskOne)
      = Sum.inr (⟨i, Work.Serre.cellSphereZeroToDiskOne z⟩ : Σ _ : Idx X pt, Work.Serre.cellDiskOne)
    rw [phi_cellSphereZeroToDiskOne]
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-! ## The homotopy on the skeleton -/

/-- The homotopy on the skeleton, descended from `Gfun`. -/
def Kfun (X : Type) [TopologicalSpace X] (pt : X) : Skel X pt × unitInterval → Skel X pt :=
  fun p => Quotient.liftOn p.1 (fun a => Quotient.mk'' (Gfun X pt (a, p.2)))
    (fun _ _ hab => Quotient.sound (Gfun_eqvGen X pt p.2 hab))

theorem Kfun_apply_mk (X : Type) [TopologicalSpace X] (pt : X)
    (a : PUnit ⊕ (Σ _ : Idx X pt, Work.Serre.cellDiskOne)) (t : unitInterval) :
    Kfun X pt (Quotient.mk'' a, t) = Quotient.mk'' (Gfun X pt (a, t)) := rfl

theorem Kfun_apply_cellMap (X : Type) [TopologicalSpace X] (pt : X) (w : Idx X pt)
    (x : Work.Serre.cellDiskOne) (t : unitInterval) :
    Kfun X pt (cellMap X pt w x, t) = cellMap X pt w (phi x t) := by
  show Kfun X pt (Quotient.mk'' (Sum.inr (⟨w, x⟩ : Σ _ : Idx X pt, Work.Serre.cellDiskOne)), t) =
    Quotient.mk'' (Sum.inr (⟨w, phi x t⟩ : Σ _ : Idx X pt, Work.Serre.cellDiskOne))
  rw [Kfun_apply_mk]
  rfl

theorem continuous_Kfun (X : Type) [TopologicalSpace X] (pt : X) : Continuous (Kfun X pt) := by
  refine Topology.IsQuotientMap.continuous_lift_prod_left
    (X₀ := PUnit ⊕ (Σ _ : Idx X pt, Work.Serre.cellDiskOne)) (X := Skel X pt)
    (Y := unitInterval) (Z := Skel X pt) (f := Quotient.mk'') ?_ ?_
  · exact isQuotientMap_quotient_mk'
  · have h : (fun p : (PUnit ⊕ (Σ _ : Idx X pt, Work.Serre.cellDiskOne)) × unitInterval =>
        Kfun X pt (Quotient.mk'' p.1, p.2)) =
        (fun p => Quotient.mk'' (Gfun X pt (p.1, p.2))) := by
      funext p
      exact Kfun_apply_mk X pt p.1 p.2
    rw [h]
    exact continuous_quotient_mk'.comp (continuous_Gfun X pt)

/-! ## The properties of the homotopy -/

theorem Kfun_zero (X : Type) [TopologicalSpace X] (pt : X) (z : Skel X pt) :
    Kfun X pt (z, 0) = z := by
  refine Quotient.inductionOn z ?_
  intro a
  rw [Kfun_apply_mk X pt a 0]
  refine Quotient.sound ?_
  rcases a with u | ⟨w, x⟩
  · exact Relation.EqvGen.refl _
  · show Relation.EqvGen (Work.Serre.oneCellRel PUnit (Idx X pt)
        (Work.Serre.E3aSk.skeletonAttach X pt))
      (Sum.inr (⟨w, phi x 0⟩ : Σ _ : Idx X pt, Work.Serre.cellDiskOne))
      (Sum.inr (⟨w, x⟩ : Σ _ : Idx X pt, Work.Serre.cellDiskOne))
    rw [phi_zero]
    exact Relation.EqvGen.refl _

theorem Kfun_base (X : Type) [TopologicalSpace X] (pt : X) (t : unitInterval) :
    Kfun X pt (base X pt, t) = base X pt := by
  have hb : base X pt = Quotient.mk'' (Sum.inl (⟨⟩ : PUnit)) := rfl
  rw [hb, Kfun_apply_mk]
  rfl

theorem cellMap_phi_mem_spider (X : Type) [TopologicalSpace X] (pt : X) (w : Idx X pt)
    {x : Work.Serre.cellDiskOne} (hx : x ∈ shellSet) (t : unitInterval) :
    cellMap X pt w (phi x t) ∈ spider X pt := by
  rcases phi_mem_shellSet_or hx t with h | h | h
  · rw [h, cellMap_endL]; exact base_mem_spider X pt
  · rw [h, cellMap_endR]; exact base_mem_spider X pt
  · exact shell_subset_spider X pt ((mem_shell (X := X) pt).mpr ⟨w, phi x t, h, rfl⟩)

theorem cellMap_phi_one (X : Type) [TopologicalSpace X] (pt : X) (w : Idx X pt)
    {x : Work.Serre.cellDiskOne} (hx : x ∈ shellSet) :
    cellMap X pt w (phi x 1) = base X pt := by
  rcases phi_one_of_shellSet hx with h | h
  · rw [h, cellMap_endL]
  · rw [h, cellMap_endR]

theorem Kfun_mem_spider (X : Type) [TopologicalSpace X] (pt : X) {z : Skel X pt}
    (hz : z ∈ spider X pt) (t : unitInterval) : Kfun X pt (z, t) ∈ spider X pt := by
  rw [mem_spider] at hz
  rcases hz with hz | hz
  · rw [hz, Kfun_base]; exact base_mem_spider X pt
  · obtain ⟨w, x, hx, hxz⟩ := (mem_shell (X := X) pt).mp hz
    rw [← hxz, Kfun_apply_cellMap]
    exact cellMap_phi_mem_spider X pt w hx t

theorem Kfun_one_eq_base (X : Type) [TopologicalSpace X] (pt : X) {z : Skel X pt}
    (hz : z ∈ spider X pt) : Kfun X pt (z, 1) = base X pt := by
  rw [mem_spider] at hz
  rcases hz with hz | hz
  · rw [hz, Kfun_base]
  · obtain ⟨w, x, hx, hxz⟩ := (mem_shell (X := X) pt).mp hz
    rw [← hxz, Kfun_apply_cellMap]
    exact cellMap_phi_one X pt w hx

/-! ## The contraction -/

theorem spiderContraction (X : Type) [TopologicalSpace X] (pt : X) :
    ∃ H : C(↥(spider X pt) × unitInterval, Skel X pt),
      (∀ z : ↥(spider X pt), H (z, 0) = (z : Skel X pt)) ∧
      (∀ z : ↥(spider X pt), H (z, 1) = base X pt) ∧
      (∀ t : unitInterval, H (⟨base X pt, base_mem_spider X pt⟩, t) = base X pt) ∧
      (∀ (z : ↥(spider X pt)) (t : unitInterval), H (z, t) ∈ spider X pt) := by
  refine ⟨⟨fun p => Kfun X pt ((p.1 : Skel X pt), p.2), ?_⟩, ?_, ?_, ?_, ?_⟩
  · exact (continuous_Kfun X pt).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
  · intro z
    exact Kfun_zero X pt (z : Skel X pt)
  · intro z
    exact Kfun_one_eq_base X pt z.2
  · intro t
    exact Kfun_base X pt t
  · intro z t
    exact Kfun_mem_spider X pt z.2 t

end

end Work.Serre.SkelPi
