import Mathlib
import Submission.Work.Gen.Basic
import Submission.Work.Gen.LineTensor
import Submission.Work.Thom.realification
import Submission.Work.Thom.chernClass_top_eq_zero_of_nowhereZeroSection

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

/-!
# `O(1) ⊗ O(-1) ≅ ℂ`: vanishing of the first Chern class

The tensor product of the dual tautological line bundle `O(1) = Work.Gen.tautDual n` with the
tautological line bundle `O(-1) = Work.Gen.tautLine n` over `ℂPⁿ` is the *trivial* complex line
bundle, via the canonical evaluation pairing `Λ ⊗ Λ^* ⟶ ℂ` (the identity endomorphism of the
tautological line).  Hence its first Chern class — the Euler class of the realification — vanishes:

  `c₁(O(1) ⊗ O(-1)) = 0`.

The proof is the classical one: the top Chern class of a complex bundle admitting a nowhere-zero
continuous section is zero (`Work.Thom.chernClass_top_eq_zero_of_nowhereZeroSection`), so it
suffices to exhibit the canonical nowhere-zero section of the tensor product.

In the gluing model of `Submission/Work/Gen/Basic.lean` and `Submission/Work/Gen/LineTensor.lean`
the transition function of `tensorLine (tautDual n) (tautLine n)` from the index `p` to the index
`q` is the scalar

  `γ(p,q)(x) = (z_{q₁}/z_{p₁})(z_{p₂}/z_{q₂})`

(the tautological factor contributes `z_{q₁}/z_{p₁}` and the dual factor `z_{p₂}/z_{q₂}`).  The
canonical section is the element `oneVec : ℂ¹` of the model fibre read in the *preferred*
trivialisation at the chosen index `indexAt x = (ch x, ch x)` (both components are the same chosen
chart index of `x`); its coordinate in the trivialisation at any index `i` is then

  `γ(indexAt x, i)(x) = homCoord i₁ ch x · homCoord ch i₂ x = homCoord i₁ i₂ x`,

which is precisely the coordinate `z_{i₂}/z_{i₁}` of the evaluation pairing `Λ ⊗ Λ^* ≅ ℂ` in the
trivialisations `i₁`, `i₂` of the two factors.  The identity
`homCoord i₁ ch · homCoord ch i₂ = homCoord i₁ i₂` is exactly the cocycle identity of the
homogeneous coordinates (`Work.Gen.homCoord_mul`), and it holds because `indexAt x` is *diagonal*.

Note that the model vector `oneVec` is *not* fixed by every transition function of the tensor
product (the product cocycle over the cover `Fin (n+1) × Fin (n+1)` is genuinely non-trivial), so
the standard constant-section criterion `Work.Thom.continuous_section_mk` does not apply; what is
true, and what makes the section continuous, is that its coordinate in each *fixed* trivialisation
is the continuous function `x ↦ homCoord i₁ i₂ x`.
-/

namespace Work.Gen

open Work.Projective

open scoped Topology

noncomputable section

/-! ## A continuous section out of continuous local coordinates

Continuity of a section `x ↦ ⟨x, g⟩` with a *constant* model vector `g` is local in the base: at
each point `x₀` it suffices to produce one index `i` containing `x₀` and a continuous coordinate
function `c` with `W.coordChange (W.indexAt x) i x g = c x` for all `x` in a neighbourhood. -/

/-- **Continuity of a constant-model section from local coordinates.**  If at each base point `x₀`
there is an index `i` containing `x₀`, a function `c` continuous at `x₀`, and the coordinate
identity `W.coordChange (W.indexAt x) i x g = c x` for all `x ∈ W.baseSet i`, then `x ↦ ⟨x, g⟩` is
continuous. -/
theorem continuous_section_of_coord {B : Type} [TopologicalSpace B]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (W : VectorBundleCore ℝ B F ι) (g : F)
    (h : ∀ x₀, ∃ (i : ι) (c : B → F), x₀ ∈ W.baseSet i ∧ ContinuousAt c x₀ ∧
      (∀ x, x ∈ W.baseSet i → W.coordChange (W.indexAt x) i x g = c x)) :
    Continuous (fun x => (⟨x, g⟩ : W.TotalSpace)) := by
  rw [continuous_iff_continuousAt]
  intro x₀
  obtain ⟨i, c, hx0, hc, hcoord⟩ := h x₀
  have hopen : W.baseSet i ∈ 𝓝 x₀ := (W.isOpen_baseSet i).mem_nhds hx0
  refine (W.localTriv i).continuousAt_of_comp_left ?_ ?_ ?_
  · exact continuousAt_id
  · show x₀ ∈ (W.localTriv i).baseSet
    rwa [← VectorBundleCore.baseSet_at]
  · have hev : (⇑(W.localTriv i) ∘ fun x => (⟨x, g⟩ : W.TotalSpace)) =ᶠ[𝓝 x₀]
        (fun x => (x, c x)) := by
      filter_upwards [hopen] with x hx
      rw [Function.comp_apply, VectorBundleCore.localTriv_apply]
      exact Prod.ext rfl (hcoord x hx)
    exact (continuousAt_id.prodMk hc).congr hev.symm

/-- **Continuity of a constant-model section from a family of continuous coordinates.**  This is
the form in which the tensor-product section below is used: for each index `i` the coordinate
function `c i` is continuous on `W.baseSet i`. -/
theorem continuous_section_of_coordOn {B : Type} [TopologicalSpace B]
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {ι : Type}
    (W : VectorBundleCore ℝ B F ι) (g : F) (c : ι → B → F)
    (hc : ∀ i, ContinuousOn (c i) (W.baseSet i))
    (hcoord : ∀ i x, x ∈ W.baseSet i → W.coordChange (W.indexAt x) i x g = c i x) :
    Continuous (fun x => (⟨x, g⟩ : W.TotalSpace)) := by
  refine continuous_section_of_coord W g fun x₀ => ?_
  exact ⟨W.indexAt x₀, c (W.indexAt x₀), W.mem_baseSet_at x₀,
    (hc (W.indexAt x₀)).continuousAt
      ((W.isOpen_baseSet (W.indexAt x₀)).mem_nhds (W.mem_baseSet_at x₀)),
    fun x hx => hcoord (W.indexAt x₀) x hx⟩

/-! ## The transition functions of `O(1) ⊗ O(-1)`, explicitly -/

/-- **The transition function of `O(1) ⊗ O(-1)`** from the index `p` to the index `q`: multiply by
the product of the homogeneous ratios `z_{q₁}/z_{p₁}` (dual tautological factor) and
`z_{p₂}/z_{q₂}` (tautological factor). -/
theorem tensorTaut_coordChange_eq (n : ℕ) (p q : Fin (n + 1) × Fin (n + 1)) (x : CP n) :
    (tensorLine (tautDual n) (tautLine n)).coordChange p q x =
      (homCoord n q.1 p.1 x * homCoord n p.2 q.2 x) •
        ContinuousLinearMap.id ℂ (EuclideanSpace ℂ (Fin 1)) := by
  rw [tensorLine_coordChange, tautDual_coordChange, tautLine_coordChange, scl_smul, scl_smul,
    scl_id, mul_one, mul_one]

/-- **The preferred trivialisation index is diagonal**: the two components of `indexAt x` are the
same chosen chart index of `x`. -/
theorem tensorTaut_indexAt_fst_eq_snd (n : ℕ) (x : CP n) :
    ((tensorLine (tautDual n) (tautLine n)).indexAt x).1 =
      ((tensorLine (tautDual n) (tautLine n)).indexAt x).2 := rfl

/-- **The coordinate of the canonical section in the trivialisation `i`**: reading the model
vector `oneVec` through the transition from the preferred index `indexAt x` to `i` gives the
homogeneous ratio `z_{i₂}/z_{i₁}`.  This is the cocycle identity `homCoord_mul` of the homogeneous
coordinates, together with the fact that the two components of `indexAt x` agree. -/
theorem tensorTaut_coordChange_indexAt (n : ℕ) (i : Fin (n + 1) × Fin (n + 1)) {x : CP n}
    (hx : x ∈ (tensorLine (tautDual n) (tautLine n)).baseSet i) :
    (tensorLine (tautDual n) (tautLine n)).coordChange
      ((tensorLine (tautDual n) (tautLine n)).indexAt x) i x oneVec =
      homCoord n i.1 i.2 x • oneVec := by
  rw [tensorTaut_coordChange_eq, smul_apply, ContinuousLinearMap.id_apply]
  congr 1
  have hxch : x ∈ chartSet ((tensorLine (tautDual n) (tautLine n)).indexAt x).1 := by
    have h := (tensorLine (tautDual n) (tautLine n)).mem_baseSet_at x
    rw [tensorLine_baseSet, tautDual_baseSet, tautLine_baseSet] at h
    exact h.1
  have hxc : x ∈ chartSet i.1 := by
    rw [tensorLine_baseSet, tautDual_baseSet, tautLine_baseSet] at hx; exact hx.1
  have hxd : x ∈ chartSet i.2 := by
    rw [tensorLine_baseSet, tautDual_baseSet, tautLine_baseSet] at hx; exact hx.2
  rw [← tensorTaut_indexAt_fst_eq_snd n x]
  rw [homCoord_mul i.1 ((tensorLine (tautDual n) (tautLine n)).indexAt x).1 i.2 hxc hxch hxd,
    mul_comm]

/-- **The same coordinate identity for the realification** of `O(1) ⊗ O(-1)`: the realification has
the same base sets, index map and transition functions (viewed as real-linear maps), so the
identity transfers verbatim from `Work.Gen.tensorTaut_coordChange_indexAt`. -/
theorem realification_tensorTaut_coordChange_indexAt (n : ℕ)
    (i : Fin (n + 1) × Fin (n + 1)) {x : CP n}
    (hx : x ∈ (Work.Thom.realification
      (tensorLine (tautDual n) (tautLine n))).baseSet i) :
    (Work.Thom.realification (tensorLine (tautDual n) (tautLine n))).coordChange
      ((Work.Thom.realification (tensorLine (tautDual n) (tautLine n))).indexAt x) i x oneVec =
      homCoord n i.1 i.2 x • oneVec := by
  have hcoord : (Work.Thom.realification (tensorLine (tautDual n) (tautLine n))).coordChange
      ((Work.Thom.realification (tensorLine (tautDual n) (tautLine n))).indexAt x) i x oneVec =
      (tensorLine (tautDual n) (tautLine n)).coordChange
        ((tensorLine (tautDual n) (tautLine n)).indexAt x) i x oneVec := by
    rw [Work.Thom.realification_indexAt]
    exact congrFun (Work.Thom.realification_coordChange (tensorLine (tautDual n) (tautLine n))
      ((tensorLine (tautDual n) (tautLine n)).indexAt x) i x) oneVec
  rw [hcoord]
  refine tensorTaut_coordChange_indexAt n i ?_
  rwa [Work.Thom.realification_baseSet (tensorLine (tautDual n) (tautLine n))] at hx

/-! ## The canonical nowhere-zero section of `O(1) ⊗ O(-1)` -/

/-- **The canonical section of `O(1) ⊗ O(-1)` is continuous.**  Its coordinate in the
trivialisation at the index `i = (i₁,i₂)` is `homCoord i₁ i₂ x`, the continuous homogeneous ratio,
so `Work.Gen.continuous_section_of_coordOn` applies. -/
theorem tensorTaut_section_continuous (n : ℕ) :
    Continuous (fun x => (⟨x, oneVec⟩ :
      (Work.Thom.realification (tensorLine (tautDual n) (tautLine n))).TotalSpace)) := by
  refine continuous_section_of_coordOn
    (Work.Thom.realification (tensorLine (tautDual n) (tautLine n))) oneVec
    (fun i x => homCoord n i.1 i.2 x • oneVec) ?_ ?_
  · intro i
    rw [Work.Thom.realification_baseSet, tensorLine_baseSet, tautDual_baseSet, tautLine_baseSet]
    exact ((continuousOn_homCoord (n := n) i.1 i.2).smul
      continuousOn_const).mono (fun x hx => hx.1)
  · intro i x hx
    exact realification_tensorTaut_coordChange_indexAt n i hx

/-! ## The theorem -/

/-- **`c₁(O(1) ⊗ O(-1)) = 0`**: the tensor product of the tautological line bundle of `ℂPⁿ` with
its dual is trivial, so its first Chern class (the top Chern class, i.e. the Euler class of the
realification) vanishes.  This is `Work.Thom.chernClass_top_eq_zero_of_nowhereZeroSection` applied
to the canonical nowhere-zero continuous section of the tensor product. -/
theorem TautTensorTriv (n : ℕ) :
    Work.Thom.chernClass 1 1
      (Work.Gen.tensorLine (Work.Gen.tautDual n) (Work.Gen.tautLine n)) = 0 := by
  refine Work.Thom.chernClass_top_eq_zero_of_nowhereZeroSection (m := 1) le_rfl
    (tensorLine (tautDual n) (tautLine n))
    ⟨fun x => ⟨x, oneVec⟩, tensorTaut_section_continuous n⟩ ?_ ?_
  · intro x; rfl
  · intro x; exact oneVec_ne_zero

end

end Work.Gen
