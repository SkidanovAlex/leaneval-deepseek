import Mathlib
import Submission.Work.BoxShrink.Core.Defs
import Submission.Work.BoxShrink.Core.Basic
import Submission.Work.BoxShrink.PinchOff.exists_discRegion_of_not_isEssential

/-!
# Finitely many embedded discs of the closed box covering a compact slice

`Work.BoxShrink.Core.sliceRegion P s c σ u` is the trace of the cutting plane inside Pardon's box,
on the surface of the parametrised torus `P`.  This file proves

`closedDiscsCover_of_compact`: **a compact slice is covered by the interiors of finitely many
embedded discs of the surface, each with carrier inside the closed box** — the covering statement
a covering statement for the case in which the slice is compact (the chapter `Work.PinchLemma3`
states a corresponding target in its own vocabulary of the *closed* box; the two are independent).

The two inputs are:

* `exists_discRegion_carrier_subset_open`: every point of the surface admits an embedded disc, inside
  any prescribed *open* neighbourhood of the point, whose interior contains the point.  This is a
  size-controlled version of `Work.SurgeryInvariance.DiscRegion.exists_mem_interior`, obtained from
  the same local-homeomorphism construction of the covering map `ℝ² → F`, with the disc of
  parameters chosen small enough to land inside the given neighbourhood.
* the compactness of the slice (`hcpt`), which turns the pointwise family of discs — each of whose
  interiors is open in the surface, hence arises as the trace of an open subset of `ℝ³` — into a
  finite subfamily.

Every point `x` of the slice lies in the *open* box `PBox s c σ` (the box norm at `x` is `< s`), so
the disc supplied by the first input at `x` for `V = PBox s c σ` has its carrier inside the closed
box region `P.carrier ∩ {boxNorm ≤ s}`.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **The surface inside the closed box**, `F ∩ {boxNorm c σ ≤ s}`: the closure of the region
`Work.BoxShrink.Core.boxRegion P s c σ` (which uses the open box).  Local to this file so that the
directory does not import the sibling chapter `Work.PinchLemma3` (which imports *this* chapter). -/
def closedBoxRegion (P : Work.CoreTopology.ParamTorus) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) : Set R3 :=
  P.carrier ∩ {y : R3 | Submission.boxNorm c σ y ≤ s}

@[simp] theorem mem_closedBoxRegion {P : Work.CoreTopology.ParamTorus} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {y : R3} :
    y ∈ closedBoxRegion P s c σ ↔ y ∈ P.carrier ∧ Submission.boxNorm c σ y ≤ s := Iff.rfl

/-- **A size-controlled embedded disc through a point of the surface.**  If `V` is an open subset of
`ℝ³` containing the point `x` of the surface `F = P.carrier`, then there is an embedded disc `D` of
`F` whose interior contains `x` and whose carrier lies inside `V`.

The proof repeats the construction of `Work.SurgeryInvariance.DiscRegion.exists_mem_interior`,
except that the disc of parameters is shrunk so that its image lands in `V`: the local
homeomorphism `E` of the covering map at a parameter point `p` over `x` is restricted to the open
neighbourhood `E.source ∩ E ⁻¹' V` of `p`, and the unit disc of `ℂ` is scaled into it. -/
theorem exists_discRegion_carrier_subset_open (P : Work.CoreTopology.ParamTorus)
    (V : Set R3) (hV : IsOpen V) (x : R3) (hx : x ∈ P.carrier) (hxV : x ∈ V) :
    ∃ D : Work.SurgeryInvariance.DiscRegion P, x ∈ D.interior ∧ D.carrier ⊆ V := by
  have hcov : IsCoveringMap (Work.TorusCover.psiMapToRange P.psi) :=
    Work.TorusCover.isCoveringMap_psiMapToRange_param P
  have hf : IsLocalHomeomorph (Work.TorusCover.psiMapToRange P.psi) := hcov.isLocalHomeomorph
  have hf' : IsLocalHomeomorph
      (fun q : ℝ × ℝ => (⟨P.psi q.1 q.2, P.psi_mem_carrier q.1 q.2⟩ : P.carrier)) := hf
  obtain ⟨a, b, hab⟩ := (Work.CoreTopology.ParamTorus.mem_carrier_iff P x).mp hx
  set p : ℝ × ℝ := (a, b) with hp_def
  have hp : P.psi p.1 p.2 = x := hab
  obtain ⟨E, hp_src, hE⟩ := hf' p
  have hEp : E p = (⟨x, hx⟩ : P.carrier) := by
    have h := congrFun hE p
    rw [← h]
    exact Subtype.ext hp
  have hV' : (Subtype.val ⁻¹' V : Set P.carrier) ∈ nhds (⟨x, hx⟩ : P.carrier) :=
    (hV.preimage continuous_subtype_val).mem_nhds hxV
  have hpre : (fun q : ℝ × ℝ => (E q : R3)) ⁻¹' V ∈ nhds p :=
    (E.continuousAt hp_src).preimage_mem_nhds (t := Subtype.val ⁻¹' V) (by rw [hEp]; exact hV')
  have hU : E.source ∩ (fun q : ℝ × ℝ => (E q : R3)) ⁻¹' V ∈ nhds p :=
    Filter.inter_mem (E.open_source.mem_nhds hp_src) hpre
  obtain ⟨W, hWsub, hWopen, hpW⟩ := mem_nhds_iff.mp hU
  obtain ⟨ε, hεpos, hεball⟩ := Metric.isOpen_iff.mp hWopen p hpW
  let r : ℝ := ε / 2
  have hrpos : 0 < r := by positivity
  have hrlt : r < ε := by show ε / 2 < ε; linarith
  -- the similarity of the parameter plane carrying the unit disc to the disc of radius `r` at `p`
  let Φ : ℂ → ℝ × ℝ := fun z => (p.1 + r * z.re, p.2 + r * z.im)
  have hΦcont : Continuous Φ := by fun_prop
  -- the Euclidean disc of radius `r` about `p`
  let S : Set (ℝ × ℝ) := {w | (w.1 - p.1)^2 + (w.2 - p.2)^2 < r^2}
  have hSopen : IsOpen S :=
    isOpen_lt (by fun_prop : Continuous fun w : ℝ × ℝ => (w.1 - p.1)^2 + (w.2 - p.2)^2)
      continuous_const
  have hSsub : S ⊆ W := by
    intro w hw
    apply hεball
    have hw' : (w.1 - p.1)^2 + (w.2 - p.2)^2 < r^2 := hw
    have h1 : |w.1 - p.1| < r :=
      abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg (w.2 - p.2), hw']) (le_of_lt hrpos)
    have h2 : |w.2 - p.2| < r :=
      abs_lt_of_sq_lt_sq (by nlinarith [sq_nonneg (w.1 - p.1), hw']) (le_of_lt hrpos)
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : w - p = (w.1 - p.1, w.2 - p.2) := by ext <;> simp
    rw [hsub, Prod.norm_def]
    simp only [Real.norm_eq_abs]
    exact max_lt (lt_trans h1 hrlt) (lt_trans h2 hrlt)
  -- `S` is exactly the image of the open unit disc of `ℂ` under `Φ`
  have hΦS : Φ '' {z : ℂ | ‖z‖ < 1} = S := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      simp only [S, Set.mem_ofPred_eq]
      have hz' : ‖z‖ < 1 := hz
      have hz2 : ‖z‖^2 < 1 := by
        have h : ‖z‖^2 < (1:ℝ)^2 := by
          rw [sq_lt_sq, abs_of_nonneg (norm_nonneg z), abs_one]; exact hz'
        simpa using h
      have hnorm : z.re^2 + z.im^2 = ‖z‖^2 := by
        rw [Complex.sq_norm, Complex.normSq_apply]; ring
      have hr2 : 0 < r^2 := by positivity
      have hcalc : (p.1 + r * z.re - p.1)^2 + (p.2 + r * z.im - p.2)^2
          = r^2 * (z.re^2 + z.im^2) := by ring
      rw [hcalc, hnorm]
      calc r^2 * ‖z‖^2 < r^2 * 1 := mul_lt_mul_of_pos_left hz2 hr2
        _ = r^2 := by ring
    · intro hw
      simp only [S, Set.mem_ofPred_eq] at hw
      refine ⟨⟨(w.1 - p.1)/r, (w.2 - p.2)/r⟩, ?_, ?_⟩
      · have hnorm : ‖(⟨(w.1 - p.1)/r, (w.2 - p.2)/r⟩ : ℂ)‖^2
            = ((w.1 - p.1)^2 + (w.2 - p.2)^2) / r^2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          field_simp
        have hlt : ‖(⟨(w.1 - p.1)/r, (w.2 - p.2)/r⟩ : ℂ)‖^2 < 1 := by
          rw [hnorm, div_lt_one (by positivity : (0:ℝ) < r^2)]
          simpa using hw
        have h : ‖(⟨(w.1 - p.1)/r, (w.2 - p.2)/r⟩ : ℂ)‖^2 < (1:ℝ)^2 := by simpa using hlt
        rwa [sq_lt_sq, abs_of_nonneg (norm_nonneg _), abs_one] at h
      · ext <;> simp only [Φ]
        · field_simp; ring
        · field_simp; ring
  -- the closed unit disc of parameters is mapped into `W`
  have hΦclosed : ∀ z : Metric.closedBall (0 : ℂ) 1, Φ (z : ℂ) ∈ W := by
    intro z
    apply hεball
    have hnorm : ‖(z : ℂ)‖ ≤ 1 := by
      have hz := z.2
      rw [Metric.mem_closedBall, dist_eq_norm] at hz
      simpa using hz
    have hre : |(z : ℂ).re| ≤ 1 := le_trans (Complex.abs_re_le_norm _) hnorm
    have him : |(z : ℂ).im| ≤ 1 := le_trans (Complex.abs_im_le_norm _) hnorm
    rw [Metric.mem_ball, dist_eq_norm]
    have hsub : Φ (z : ℂ) - p = (r * (z : ℂ).re, r * (z : ℂ).im) := by
      ext <;> simp [Φ]
    rw [hsub, Prod.norm_def]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos hrpos]
    exact max_lt (by nlinarith) (by nlinarith)
  -- the parametrisation of the disc
  let f : Metric.closedBall (0 : ℂ) 1 → R3 := fun z => (E (Φ (z : ℂ)) : R3)
  have hf_cont : Continuous f := by
    have h1 : Continuous fun z : Metric.closedBall (0 : ℂ) 1 => Φ (z : ℂ) :=
      hΦcont.comp continuous_subtype_val
    have h2 : Continuous (E ∘ fun z : Metric.closedBall (0 : ℂ) 1 => Φ (z : ℂ)) :=
      E.continuousOn.comp_continuous h1 (fun z => (hWsub (hΦclosed z)).1)
    exact Continuous.subtype_val h2
  have hf_inj : Function.Injective f := by
    intro z z' hzz
    have h1 : E (Φ (z : ℂ)) = E (Φ (z' : ℂ)) := Subtype.val_injective hzz
    have h2 : Φ (z : ℂ) = Φ (z' : ℂ) :=
      E.injOn (hWsub (hΦclosed z)).1 (hWsub (hΦclosed z')).1 h1
    have hre : (z : ℂ).re = (z' : ℂ).re := by
      have h := congrArg Prod.fst h2
      simp only [Φ] at h
      exact mul_left_cancel₀ (ne_of_gt hrpos) (add_left_cancel h)
    have him : (z : ℂ).im = (z' : ℂ).im := by
      have h := congrArg Prod.snd h2
      simp only [Φ] at h
      exact mul_left_cancel₀ (ne_of_gt hrpos) (add_left_cancel h)
    exact Subtype.ext (Complex.ext hre him)
  have hf_mem : ∀ z : Metric.closedBall (0 : ℂ) 1, f z ∈ P.carrier :=
    fun z => (E (Φ (z : ℂ))).2
  -- the interior of the disc is the image of the open Euclidean disc under the local inverse
  have hf_image : f '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1}
      = Subtype.val '' (E '' S) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨E (Φ (z : ℂ)), ⟨Φ (z : ℂ), by rw [← hΦS]; exact ⟨(z : ℂ), hz, rfl⟩, rfl⟩, rfl⟩
    · intro hy
      obtain ⟨u, hu, rfl⟩ := hy
      obtain ⟨v, hv, rfl⟩ := hu
      rw [← hΦS] at hv
      obtain ⟨z, hz, hzv⟩ := hv
      refine ⟨⟨z, ?_⟩, hz, ?_⟩
      · rw [Metric.mem_closedBall, dist_eq_norm]; simpa using le_of_lt hz
      · show (E (Φ z) : R3) = (E v : R3)
        rw [hzv]
  have hf_open : Work.SurgeryInvariance.IsOpenInCarrier P
      (f '' {z : Metric.closedBall (0 : ℂ) 1 | ‖(z : ℂ)‖ < 1}) := by
    rw [hf_image]
    have hEimage : IsOpen (E '' S) :=
      E.isOpen_image_of_subset_source hSopen (fun w hw => (hWsub (hSsub hw)).1)
    show IsOpen (Subtype.val ⁻¹' (Subtype.val '' (E '' S)) : Set P.carrier)
    rw [Set.preimage_image_eq _ Subtype.val_injective]
    exact hEimage
  refine ⟨{ e := ⟨f, hf_cont⟩, inj := hf_inj, mem := hf_mem, open_interior := hf_open }, ?_, ?_⟩
  -- the centre of the disc is `x`
  · refine ⟨⟨0, by simp [Metric.mem_closedBall]⟩, ?_, ?_⟩
    · simp
    · show (E (Φ (0 : ℂ)) : R3) = x
      have h0 : Φ (0 : ℂ) = p := by ext <;> simp [Φ]
      rw [h0, hEp]
  -- the carrier lies in `V`
  · intro y hy
    obtain ⟨z, rfl⟩ := hy
    exact (hWsub (hΦclosed z)).2

/-- **A compact slice is covered by finitely many discs of the closed box.**

Each point `x` of the slice lies in the open box `PBox s c σ`, so the size-controlled disc
`exists_discRegion_carrier_subset_open` at `x` for `V = PBox s c σ` has its carrier inside the
closed box region.  Its interior is open in the surface, hence the trace of an open subset of `ℝ³`
on the surface; the compactness of the slice turns this open cover into a finite one. -/
theorem closedDiscsCover_of_compact (P : Work.CoreTopology.ParamTorus) (s : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (hcpt : IsCompact (Work.BoxShrink.Core.sliceRegion P s c σ u)) :
    ∃ L : List (Work.SurgeryInvariance.DiscRegion P),
      (∀ D ∈ L, D.carrier ⊆ closedBoxRegion P s c σ) ∧
        (∀ x ∈ Work.BoxShrink.Core.sliceRegion P s c σ u, ∃ D ∈ L, x ∈ D.interior) := by
  classical
  -- the pointwise disc, inside the closed box
  have hpoint : ∀ x : {y : R3 // y ∈ Work.BoxShrink.Core.sliceRegion P s c σ u},
      ∃ D : Work.SurgeryInvariance.DiscRegion P,
        (x : R3) ∈ D.interior ∧ D.carrier ⊆ closedBoxRegion P s c σ := by
    rintro ⟨x, hx⟩
    obtain ⟨hxc, hxb, -⟩ := Work.BoxShrink.Core.mem_sliceRegion.mp hx
    obtain ⟨D, hxD, hDV⟩ := exists_discRegion_carrier_subset_open P (Submission.PBox s c σ)
      (Work.Topology.SphereSlicing.isOpen_PBox s c σ) x hxc hxb
    refine ⟨D, hxD, fun y hy => ?_⟩
    obtain ⟨z, rfl⟩ := hy
    rw [mem_closedBoxRegion]
    exact ⟨D.mem z, le_of_lt ((Submission.mem_PBox_iff s c σ _).mp (hDV ⟨z, rfl⟩))⟩
  choose D hD using hpoint
  -- each interior is the trace of an open subset of `ℝ³`
  have hopen : ∀ x : {y : R3 // y ∈ Work.BoxShrink.Core.sliceRegion P s c σ u},
      ∃ W : Set R3, IsOpen W ∧ (x : R3) ∈ W ∧
        ∀ y ∈ P.carrier, (y ∈ W ↔ y ∈ (D x).interior) := by
    intro x
    have hoi := (D x).open_interior'
    rw [Work.SurgeryInvariance.IsOpenInCarrier] at hoi
    obtain ⟨W, hWopen, hWeq⟩ := isOpen_induced_iff.mp hoi
    have hxcarrier : x.1 ∈ P.carrier := (Work.BoxShrink.Core.mem_sliceRegion.mp x.2).1
    refine ⟨W, hWopen, ?_, ?_⟩
    · have hxmem : (⟨(x : R3), hxcarrier⟩ : P.carrier) ∈
          (Subtype.val : P.carrier → R3) ⁻¹' W := by
        rw [hWeq]
        exact (hD x).1
      simpa using hxmem
    · intro y hy
      have h : (⟨y, hy⟩ : P.carrier) ∈ (Subtype.val : P.carrier → R3) ⁻¹' W ↔
          (⟨y, hy⟩ : P.carrier) ∈ (Subtype.val : P.carrier → R3) ⁻¹' (D x).interior := by
        rw [hWeq]
      exact h
  choose W hW using hopen
  have hcover : Work.BoxShrink.Core.sliceRegion P s c σ u ⊆ ⋃ x : {y : R3 //
      y ∈ Work.BoxShrink.Core.sliceRegion P s c σ u}, W x := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, (hW ⟨x, hx⟩).2.1⟩
  obtain ⟨t, ht⟩ := hcpt.elim_finite_subcover W (fun x => (hW x).1) hcover
  refine ⟨t.toList.map D, ?_, ?_⟩
  · intro D' hD'
    obtain ⟨x, -, rfl⟩ := List.mem_map.mp hD'
    exact (hD x).2
  · intro x hx
    have hxU := ht hx
    simp only [Set.mem_iUnion] at hxU
    obtain ⟨i, hi, hxi⟩ := hxU
    refine ⟨D i, List.mem_map.mpr ⟨i, Finset.mem_toList.mpr hi, rfl⟩, ?_⟩
    have hxc : x ∈ P.carrier := (Work.BoxShrink.Core.mem_sliceRegion.mp hx).1
    exact ((hW i).2.2 x hxc).mp hxi

end

end Work.BoxShrink.PinchOff
