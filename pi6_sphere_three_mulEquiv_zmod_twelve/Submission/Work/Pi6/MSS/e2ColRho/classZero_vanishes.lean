import Mathlib
import Submission.Work.Cohomology.cupH
import Submission.Work.Pi6.SQ.z4
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option maxHeartbeats 800000

namespace Work.Pi6.MSS.e2ColRho

open Work.Cohomology CategoryTheory

/-! ## Two elementary facts about the singular (co)chain complex of a simplicial set

The target `classZero_vanishes` below is the statement that the cohomology class of a cocycle
detects its coboundaries, evaluated on cycles: a cocycle `α` of degree `q` with vanishing class
vanishes on every `q`-cycle.  The proof is the elementwise form of
`ker (homologyπ q) = range (toCycles (prev q) q)`: a cocycle with zero class is the boundary of a
cochain, and boundaries pair to zero with cycles.

Two pieces are isolated below:

* `d_prev_apply_cycle` — the differential `d (prev q) q` of the *cochain* complex, evaluated on a
  cycle `γ` of the chain complex, is zero (because it is the transpose of the boundary `d q (q-1)`,
  and it vanishes identically in degree `0`);
* `exists_toCycles_prev_eq_of_homologyπ_eq_zero` — the kernel of `homologyπ q` is the range of
  `toCycles (prev q) q`, elementwise, in arbitrary degree.  This is
  `Work.Pi6.SQM.SIG.exists_toCycles_eq_of_homologyπ_eq_zero` without the restriction to degrees of
  the form `n + 1`; the proof is the same cokernel argument, with `ComplexShape.prev` supplied
  directly. -/

/-- The differential `d ((up ℕ).prev q) q` of the singular cochain complex, applied to an element
`y` and then evaluated at a `q`-cycle `γ` of the singular chain complex, is zero.

Indeed `((up ℕ).prev q) + 1 = q` for `q ≥ 1`, so the differential is the transpose of the boundary
`d q (q-1)`, whereas for `q = 0` it is the zero morphism by the shape of the complex. -/
lemma d_prev_apply_cycle (𝕜 : Type) [Field 𝕜] (X : SSet) (q : ℕ)
    (y : (SSetCochainComplex 𝕜 X).X ((ComplexShape.up ℕ).prev q))
    (γ : (X.chainComplex (ModuleCat.of 𝕜 𝕜)).X q)
    (hγ : (X.chainComplex (ModuleCat.of 𝕜 𝕜)).d q (q - 1) γ = 0) :
    LinearMap.applyₗ γ
      (((SSetCochainComplex 𝕜 X).d ((ComplexShape.up ℕ).prev q) q).hom y) = 0 := by
  generalize hpq : (ComplexShape.up ℕ).prev q = p at y ⊢
  rcases q with _ | q'
  · -- degree `0`: `d p 0 = 0` by the shape, since `p + 1 ≠ 0`
    have hz : (SSetCochainComplex 𝕜 X).d p 0 = 0 :=
      HomologicalComplex.shape _ p 0 (fun hr => Nat.succ_ne_zero p hr)
    rw [hz, ModuleCat.hom_zero, LinearMap.zero_apply]
    exact map_zero _
  · -- positive degree: `p = q' = q - 1`, and the differential is `cochainDiff`
    have hp : p = q' := by
      rw [← hpq]
      exact ComplexShape.prev_eq' (ComplexShape.up ℕ) (ComplexShape.up_mk q' (q' + 1) rfl)
    clear hpq
    subst p
    rw [SSetCochainComplex_d_apply]
    have hγ' : (X.chainComplex (ModuleCat.of 𝕜 𝕜)).d (q' + 1) q' γ = 0 := by simpa using hγ
    simpa only [Work.Cohomology.kronecker, LinearMap.applyₗ_apply_apply] using
      Work.Cohomology.kronecker_coboundary_cycle 𝕜 X y γ hγ'

/-- A cycle of the singular cochain complex of degree `q` whose cohomology class vanishes is the
image of the boundary map `toCycles ((up ℕ).prev q) q`: the elementwise form of
`ker (homologyπ q) = range (toCycles (prev q) q)`, in arbitrary degree `q`. -/
lemma exists_toCycles_prev_eq_of_homologyπ_eq_zero (𝕜 : Type) [Field 𝕜] (X : SSet) (q : ℕ)
    (z : (SSetCochainComplex 𝕜 X).cycles q)
    (h : ModuleCat.Hom.hom ((SSetCochainComplex 𝕜 X).homologyπ q) z = 0) :
    ∃ y : (SSetCochainComplex 𝕜 X).X ((ComplexShape.up ℕ).prev q),
      ModuleCat.Hom.hom
        ((SSetCochainComplex 𝕜 X).toCycles ((ComplexShape.up ℕ).prev q) q) y = z := by
  let T := ShortComplex.mk ((SSetCochainComplex 𝕜 X).toCycles ((ComplexShape.up ℕ).prev q) q)
    ((SSetCochainComplex 𝕜 X).homologyπ q)
    ((SSetCochainComplex 𝕜 X).toCycles_comp_homologyπ ((ComplexShape.up ℕ).prev q) q)
  have hT : T.Exact := ShortComplex.exact_of_g_is_cokernel T
    ((SSetCochainComplex 𝕜 X).homologyIsCokernel ((ComplexShape.up ℕ).prev q) q rfl)
  exact (ShortComplex.moduleCat_exact_iff T).mp hT z h

/-- If a cocycle `α` of degree `q` on a simplicial set has vanishing cohomology class, then `α`
vanishes on every `q`-cycle (a chain killed by the boundary `d q (q-1)`).  Over any commutative ring
this is the statement that the cohomology class of a cocycle detects its coboundaries; the
degree-`0` case is included (there `d 0 0 = 0`, so every `0`-chain is a cycle and the statement says
`α = 0`, which holds because `boundaries 0 = 0` and `homologyπ 0` is injective).
Available: `Work.Cohomology.iCycles_cocycleOf`, `cocycleOf`, `cohomologyClassOf`,
`Work.Pi6.SQM.SIG.exists_toCycles_eq_of_homologyπ_eq_zero` (degree `n+1` only) and
`Work.Pi6.SQ.classZeroCoboundaryR` (degree `n+1` only). -/
theorem classZero_vanishes (𝕜 : Type) [Field 𝕜] (X : SSet) (q : ℕ)
    (α : Work.Cohomology.Cochain 𝕜 X q)
    (hα : Work.Cohomology.cochainDiff 𝕜 X α = 0)
    (h0 : Work.Cohomology.cohomologyClassOf 𝕜 X α hα = 0) :
    ∀ γ : (X.chainComplex (ModuleCat.of 𝕜 𝕜)).X q,
      (X.chainComplex (ModuleCat.of 𝕜 𝕜)).d q (q - 1) γ = 0 → α γ = 0 := by
  intro γ hγ
  -- a cocycle of vanishing class is a boundary `d (prev q) q` of the cochain complex
  obtain ⟨y, hy⟩ := exists_toCycles_prev_eq_of_homologyπ_eq_zero 𝕜 X q
    (Work.Cohomology.cocycleOf 𝕜 X α hα) h0
  have hαeq : α = ((SSetCochainComplex 𝕜 X).d ((ComplexShape.up ℕ).prev q) q).hom y := by
    rw [← Work.Cohomology.iCycles_cocycleOf 𝕜 X α hα, ← hy]
    exact Work.Cohomology.iCycles_toCycles 𝕜 X ((ComplexShape.up ℕ).prev q) q y
  -- and a boundary pairs to zero with a cycle
  have key : LinearMap.applyₗ γ α = 0 := by
    rw [hαeq]
    exact d_prev_apply_cycle 𝕜 X q y γ hγ
  simpa only [LinearMap.applyₗ_apply_apply] using key

end Work.Pi6.MSS.e2ColRho
