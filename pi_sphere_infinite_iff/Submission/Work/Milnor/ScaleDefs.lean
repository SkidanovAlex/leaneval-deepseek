import Mathlib
import Submission.Work.Milnor.VBundle
import Submission.Work.Milnor.mk_to_vk
import Submission.Work.Milnor.Collar

/-!
# Fibrewise scaling of the total space of the vector bundle `ξ` over `S⁴`

`Vk k = (vData k).Glued` is the total space of the rank-`4` real vector bundle `ξ` over `S⁴`,
realised as the quotient of two copies of `MSpace8 = ℝ⁴ × ℍ` glued along `{x ≠ 0} × ℍ` by the
clutching map `vMap k (x, y) = (x/‖x‖², û⁻ᵏ y û⁻¹)`.

The clutching map is *linear in the fibre* (`vTwist_smul`), so scaling the fibre coordinate by a
real number `c` is compatible with the gluing relation and descends to a self-map

`vScale k c : Vk k → Vk k`,  `vScale k c (ιX (x, y)) = ιX (x, c • y)`, `vScale k c (ιY (x,y)) = ιY (x, c•y)`.

This is the "scalar multiplication of the vector bundle", restricted to real scalars; it satisfies
`vScale k 1 = id`, `vScale k (a*b) = vScale k a ∘ vScale k b` and multiplies the fibre norm by
`|c|`.  Its joint continuity in `(c, p)` is the technical input for the deformation retraction of
the collar `{1/2 < ν}` onto the unit sphere bundle.
-/

namespace Work.Milnor

open scoped Manifold ContDiff Topology
open Submission.Milnor
open Set

noncomputable section

/-! ## Linearity of the twist -/

/-- The twist `y ↦ qᵐ y q⁻¹` of the fibre `ℍ` is real-linear in `y`. -/
lemma vTwist_smul (m : ℤ) (q y : Quaternion ℝ) (c : ℝ) :
    vTwist m q (c • y) = c • vTwist m q y := by
  rw [vTwist, vTwist, mul_smul_comm, smul_mul_assoc]

/-! ## The scaling map on the disjoint union and its descent -/

/-- Fibrewise scaling, defined on the disjoint union of the two charts of `Vk k`. -/
def vScaleAux (k : ℤ) (c : ℝ) : MSpace8 ⊕ MSpace8 → Vk k :=
  Sum.elim (fun p => (vData k).ιX (p.1, c • p.2))
           (fun p => (vData k).ιY (p.1, c • p.2))

@[simp] lemma vScaleAux_inl (k : ℤ) (c : ℝ) (p : MSpace8) :
    vScaleAux k c (Sum.inl p) = (vData k).ιX (p.1, c • p.2) := rfl

@[simp] lemma vScaleAux_inr (k : ℤ) (c : ℝ) (p : MSpace8) :
    vScaleAux k c (Sum.inr p) = (vData k).ιY (p.1, c • p.2) := rfl

/-- Fibrewise scaling is compatible with the gluing relation of `vData k`, because the clutching
map is linear in the fibre coordinate (`vTwist_smul`). -/
theorem vScaleAux_respects (k : ℤ) (c : ℝ) {a b : MSpace8 ⊕ MSpace8}
    (h : (vData k).rel a b) : vScaleAux k c a = vScaleAux k c b := by
  rcases a with p | p <;> rcases b with q | q
  · rw [vScaleAux_inl, vScaleAux_inl, h]
  · obtain ⟨hp, hq⟩ := h
    rw [vScaleAux_inl, vScaleAux_inr, (vData k).ιX_eq_ιY_iff]
    refine ⟨mem_vOpens.mp hp, ?_⟩
    have hq' : vMap k p = q := hq
    subst hq'
    rw [vData_φ_apply, vMap]
    refine Prod.ext rfl ?_
    rw [vMap, vTwist_smul]
  · -- `a = Sum.inr p`, `b = Sum.inl q`: the membership hypothesis is about `q`
    obtain ⟨hmem, hp⟩ := h
    rw [vScaleAux_inr, vScaleAux_inl, (vData k).ιY_eq_ιX_iff]
    refine ⟨mem_vOpens.mp hmem, ?_⟩
    have hp' : vMap k q = p := hp.symm
    subst hp'
    rw [vData_φ_apply, vMap]
    refine Prod.ext rfl ?_
    rw [vMap, vTwist_smul]
  · rw [vScaleAux_inr, vScaleAux_inr, h]

/-- **Fibrewise scaling of the total space of `ξ`**: the scalar multiplication by `c ∈ ℝ`. -/
def vScale (k : ℤ) (c : ℝ) : Vk k → Vk k :=
  Quotient.lift (vScaleAux k c) (fun _ _ h => vScaleAux_respects k c h)

@[simp] theorem vScale_ιX (k : ℤ) (c : ℝ) (p : MSpace8) :
    vScale k c ((vData k).ιX p) = (vData k).ιX (p.1, c • p.2) := rfl

@[simp] theorem vScale_ιY (k : ℤ) (c : ℝ) (p : MSpace8) :
    vScale k c ((vData k).ιY p) = (vData k).ιY (p.1, c • p.2) := rfl

/-! ## The laws of the scaling action -/

@[simp] theorem vScale_one (k : ℤ) : vScale k 1 = id := by
  funext z
  refine Quotient.inductionOn z ?_
  intro a
  rcases a with p | p
  · show vScale k 1 ((vData k).ιX p) = (vData k).ιX p
    rw [vScale_ιX, one_smul]
  · show vScale k 1 ((vData k).ιY p) = (vData k).ιY p
    rw [vScale_ιY, one_smul]

theorem vScale_mul (k : ℤ) (a b : ℝ) (z : Vk k) :
    vScale k a (vScale k b z) = vScale k (a * b) z := by
  refine Quotient.inductionOn z ?_
  intro s
  rcases s with p | p
  · show vScale k a (vScale k b ((vData k).ιX p)) = vScale k (a * b) ((vData k).ιX p)
    rw [vScale_ιX, vScale_ιX, vScale_ιX, smul_smul]
  · show vScale k a (vScale k b ((vData k).ιY p)) = vScale k (a * b) ((vData k).ιY p)
    rw [vScale_ιY, vScale_ιY, vScale_ιY, smul_smul]

/-- The fibre norm scales by `|c|` under fibrewise scaling. -/
theorem fibreNormFun_vScale (k : ℤ) (c : ℝ) (z : Vk k) :
    fibreNormFun k (vScale k c z) = |c| * fibreNormFun k z := by
  refine Quotient.inductionOn z ?_
  intro s
  rcases s with p | p
  · show fibreNormFun k (vScale k c ((vData k).ιX p)) = |c| * fibreNormFun k ((vData k).ιX p)
    rw [vScale_ιX, fibreNormFun_ιX, fibreNormFun_ιX, norm_smul, Real.norm_eq_abs]
  · show fibreNormFun k (vScale k c ((vData k).ιY p)) = |c| * fibreNormFun k ((vData k).ιY p)
    rw [vScale_ιY, fibreNormFun_ιY, fibreNormFun_ιY, norm_smul, Real.norm_eq_abs]

/-! ## Continuity -/

/-- Fibrewise scaling by a fixed scalar is continuous. -/
theorem continuous_vScale (k : ℤ) (c : ℝ) : Continuous (vScale k c) := by
  have h : Continuous (vScaleAux k c) := by
    refine Continuous.sumElim ?_ ?_
    · exact (vData k).continuous_ιX.comp
        (continuous_fst.prodMk (continuous_snd.const_smul c))
    · exact (vData k).continuous_ιY.comp
        (continuous_fst.prodMk (continuous_snd.const_smul c))
  exact h.quotient_lift (fun _ _ hh => vScaleAux_respects k c hh)

/-- A function continuous on each member of an open cover is continuous. -/
theorem continuous_of_open_cover {Z Y : Type*} [TopologicalSpace Z] [TopologicalSpace Y]
    {F : Z → Y} (U V : Set Z) (hU : IsOpen U) (hV : IsOpen V) (hcov : U ∪ V = univ)
    (hFU : ContinuousOn F U) (hFV : ContinuousOn F V) : Continuous F := by
  rw [continuous_iff_continuousAt]
  intro z
  rcases (show z ∈ U ∪ V from hcov ▸ Set.mem_univ z) with hz | hz
  · exact hFU.continuousAt (hU.mem_nhds hz)
  · exact hFV.continuousAt (hV.mem_nhds hz)

/-- **Joint continuity of fibrewise scaling**: `(c, p) ↦ c • p` is continuous on `ℝ × Vk k`. -/
theorem continuous_vScale_uncurry (k : ℤ) :
    Continuous (fun z : ℝ × Vk k => vScale k z.1 z.2) := by
  set F : ℝ × Vk k → Vk k := fun z => vScale k z.1 z.2 with hF
  have hUX : IsOpen {z : ℝ × Vk k | z.2 ∈ Set.range (vData k).ιX} :=
    (vData k).isOpenMap_ιX.isOpen_range.preimage continuous_snd
  have hUY : IsOpen {z : ℝ × Vk k | z.2 ∈ Set.range (vData k).ιY} :=
    (vData k).isOpenMap_ιY.isOpen_range.preimage continuous_snd
  have hcov : {z : ℝ × Vk k | z.2 ∈ Set.range (vData k).ιX} ∪
      {z : ℝ × Vk k | z.2 ∈ Set.range (vData k).ιY} = univ := by
    rw [eq_univ_iff_forall]
    intro z
    rw [Set.mem_union]
    exact (show z.2 ∈ Set.range (vData k).ιX ∪ Set.range (vData k).ιY from by
      rw [(vData k).range_ιX_union_range_ιY]; exact Set.mem_univ z)
  have hsymmX : ContinuousOn (fun z : ℝ × Vk k => (vData k).homX.symm z.2)
      {z : ℝ × Vk k | z.2 ∈ Set.range (vData k).ιX} :=
    ((vData k).homX.continuousOn_symm).comp continuous_snd.continuousOn
      (fun z hz => by rw [(vData k).homX_target]; exact hz)
  have hsymmY : ContinuousOn (fun z : ℝ × Vk k => (vData k).homY.symm z.2)
      {z : ℝ × Vk k | z.2 ∈ Set.range (vData k).ιY} :=
    ((vData k).homY.continuousOn_symm).comp continuous_snd.continuousOn
      (fun z hz => by rw [(vData k).homY_target]; exact hz)
  have hgX : ContinuousOn (fun z : ℝ × Vk k =>
      (((vData k).homX.symm z.2).1, z.1 • ((vData k).homX.symm z.2).2))
      {z : ℝ × Vk k | z.2 ∈ Set.range (vData k).ιX} :=
    (continuous_fst.comp_continuousOn hsymmX).prodMk
      (continuous_fst.continuousOn.smul (continuous_snd.comp_continuousOn hsymmX))
  have hgY : ContinuousOn (fun z : ℝ × Vk k =>
      (((vData k).homY.symm z.2).1, z.1 • ((vData k).homY.symm z.2).2))
      {z : ℝ × Vk k | z.2 ∈ Set.range (vData k).ιY} :=
    (continuous_fst.comp_continuousOn hsymmY).prodMk
      (continuous_fst.continuousOn.smul (continuous_snd.comp_continuousOn hsymmY))
  have heqX : Set.EqOn (fun z : ℝ × Vk k => vScale k z.1 z.2)
      (fun z : ℝ × Vk k => (vData k).ιX
        (((vData k).homX.symm z.2).1, z.1 • ((vData k).homX.symm z.2).2))
      {z : ℝ × Vk k | z.2 ∈ Set.range (vData k).ιX} := by
    intro z hz
    obtain ⟨a, ha⟩ := hz
    show vScale k z.1 z.2 = (vData k).ιX
      (((vData k).homX.symm z.2).1, z.1 • ((vData k).homX.symm z.2).2)
    rw [← ha, (vData k).homX_symm_apply a]
    exact vScale_ιX k z.1 a
  have heqY : Set.EqOn (fun z : ℝ × Vk k => vScale k z.1 z.2)
      (fun z : ℝ × Vk k => (vData k).ιY
        (((vData k).homY.symm z.2).1, z.1 • ((vData k).homY.symm z.2).2))
      {z : ℝ × Vk k | z.2 ∈ Set.range (vData k).ιY} := by
    intro z hz
    obtain ⟨a, ha⟩ := hz
    show vScale k z.1 z.2 = (vData k).ιY
      (((vData k).homY.symm z.2).1, z.1 • ((vData k).homY.symm z.2).2)
    rw [← ha, (vData k).homY_symm_apply a]
    exact vScale_ιY k z.1 a
  have hX : ContinuousOn F {z : ℝ × Vk k | z.2 ∈ Set.range (vData k).ιX} :=
    (ContinuousOn.comp ((vData k).continuous_ιX.continuousOn (s := Set.univ)) hgX
      (fun _ _ => Set.mem_univ _)).congr heqX
  have hY : ContinuousOn F {z : ℝ × Vk k | z.2 ∈ Set.range (vData k).ιY} :=
    (ContinuousOn.comp ((vData k).continuous_ιY.continuousOn (s := Set.univ)) hgY
      (fun _ _ => Set.mem_univ _)).congr heqY
  exact continuous_of_open_cover _ _ hUX hUY hcov hX hY

end

end Work.Milnor
