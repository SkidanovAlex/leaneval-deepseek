import Mathlib
import Submission.Work.ORVonNeumann.Rep.CosetData
import Submission.Work.ORVonNeumann.Rep.exists_rightRegular
import Submission.Work.ORVonNeumann.Rep.Orthonormal
import Submission.Work.ORVonNeumann.Rep.DenseSpan
import Submission.Work.ORVonNeumann.Rep.HilbertBasis

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORVonNeumann.Rep

variable {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G]
  [MeasurableMul G] {H : Subgroup G}

/-- **The right regular representation intertwines the coset lifts, on basis vectors.**

Writing `hpart`, `qpart` for the decomposition `g = hpart g * qpart g`, the right translation
`ρ_k` sends the lift `e q (δ_h)` of `δ_h` along the coset `H q` to the lift of `δ_{h * hpart g}`
along the coset of `g = q * k⁻¹`:

`ρ_k (e q δ_h) = E (q k⁻¹) (ρ_{(hpart (q k⁻¹))⁻¹} δ_h)`.

On vectors this is the associativity computation `(h q) k⁻¹ = h (q k⁻¹)` together with
`q k⁻¹ = hpart · qpart`. -/
theorem rightRegOp_e_deltaG (C : CosetData G H) (q : C.Q) (k : G) (h' : ↥H) :
    rightRegOp k (C.e q (deltaG h')) =
      C.E (((q : C.Q) : G) * k⁻¹)
        (rightRegOp ((C.hpart (((q : C.Q) : G) * k⁻¹))⁻¹) (deltaG h')) := by
  rw [C.e_delta, rightRegOp_deltaG]
  rw [CosetData.E, rightRegOp_deltaG, C.e_delta]
  congr 1
  rw [Subgroup.coe_mul, inv_inv]
  -- the two arguments of `δ` agree by associativity and `q * k⁻¹ = hpart * qpart`
  have hhq : (↑(C.hpart (((q : C.Q) : G) * k⁻¹)) : G)
      * ↑(C.qpart (((q : C.Q) : G) * k⁻¹)) = (↑q : G) * k⁻¹ :=
    C.hpart_mul_qpart (((q : C.Q) : G) * k⁻¹)
  calc (↑h' : G) * ↑q * k⁻¹
      = ↑h' * (↑q * k⁻¹) := mul_assoc _ _ _
    _ = ↑h' * (↑(C.hpart (((q : C.Q) : G) * k⁻¹))
          * ↑(C.qpart (((q : C.Q) : G) * k⁻¹))) := by rw [hhq]
    _ = ↑h' * ↑(C.hpart (((q : C.Q) : G) * k⁻¹))
          * ↑(C.qpart (((q : C.Q) : G) * k⁻¹)) := (mul_assoc _ _ _).symm

theorem rightRegOp_e_apply {G : Type*} [Group G] [Countable G] [MeasurableSpace G] [MeasurableSingletonClass G] [MeasurableMul G] {H : Subgroup G} (C : Work.ORVonNeumann.Rep.CosetData G H) (q : C.Q) (k : G) (y : Work.ORVonNeumann.l2 ↥H) : Work.ORVonNeumann.Rep.rightRegOp k (C.e q y) = C.E (((q : C.Q) : G) * k⁻¹) (Work.ORVonNeumann.Rep.rightRegOp ((C.hpart (((q : C.Q) : G) * k⁻¹))⁻¹) y) := by
  -- The span of the `δ_h` is dense in `ℓ²(H)`.
  have hDense :
      Dense (Submodule.span ℂ (Set.range (deltaG (G := ↥H))) : Set (Work.ORVonNeumann.l2 ↥H)) := by
    rw [Submodule.dense_iff_topologicalClosure_eq_top]
    exact le_antisymm le_top (dense_span_deltaG (G := ↥H))
  -- The two continuous linear maps agree on the dense span of the `δ_h`.
  have hfg : (rightRegOp k).comp (C.e q).toContinuousLinearMap
      = (C.E (((q : C.Q) : G) * k⁻¹)).toContinuousLinearMap.comp
          (rightRegOp ((C.hpart (((q : C.Q) : G) * k⁻¹))⁻¹)) := by
    apply ContinuousLinearMap.ext_on hDense
    rintro x ⟨h', rfl⟩
    simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
      using rightRegOp_e_deltaG C q k h'
  simpa only [ContinuousLinearMap.comp_apply, LinearIsometry.coe_toContinuousLinearMap]
    using DFunLike.congr_fun hfg y

end Work.ORVonNeumann.Rep
