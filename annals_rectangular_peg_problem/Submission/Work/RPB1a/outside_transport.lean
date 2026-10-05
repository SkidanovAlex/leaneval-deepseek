import Mathlib
import Submission.Work.RPB1a.isConnected_compl_of_cover

/-!
# RPB1a: `outside_transport`

Transport of the decomposition `ins ∪ out` of the complement of a curve
`Set.range γ ⊆ ℝ × ℝ` to the complex plane along the linear homeomorphism
`Complex.equivRealProdCLM.symm`, together with the two topological consequences
needed downstream: the curve lies in the closure of the complement of
`ins ∪ curve`, and the complement of the transported `ins` is connected.

The purely point-set-topological core is
`Work.RPB1a.isConnected_compl_of_cover`; here we only push the hypotheses
through the homeomorphism.
-/

namespace Work.RPB1a

theorem outside_transport (ins out : Set (ℝ × ℝ)) (γ : Circle → ℝ × ℝ) (v : ℝ → ℂ)
    (houtpc : IsPathConnected out)
    (hcover : (Set.range γ)ᶜ = ins ∪ out) (hdisj : Disjoint ins out)
    (hcl2 : closure out = out ∪ Set.range γ)
    (hrange : Set.range v = Complex.equivRealProdCLM.symm '' Set.range γ) :
    Set.range v ⊆ closure ((Complex.equivRealProdCLM.symm '' ins ∪ Set.range v)ᶜ) ∧
      IsConnected ((Complex.equivRealProdCLM.symm '' ins)ᶜ) := by
  set F := Complex.equivRealProdCLM.symm
  -- `ins` and `out` are disjoint, and so are their images.
  have hIO : Disjoint (F '' ins) (F '' out) := by
    rw [Set.disjoint_iff_inter_eq_empty]
    rw [← Set.image_inter F.injective, Set.disjoint_iff_inter_eq_empty.mp hdisj, Set.image_empty]
  -- the complement of the curve is the union of the images of `ins` and `out`.
  have hCO : F '' ins ∪ F '' out = (F '' Set.range γ)ᶜ := by
    rw [← Set.image_union, ← hcover, Set.image_compl_eq F.bijective]
  -- the transported curve is the frontier of the transported `out`.
  have himg : closure (F '' out) = F '' closure out := by
    have h := Homeomorph.image_closure F.toHomeomorph out
    rw [ContinuousLinearEquiv.coe_toHomeomorph] at h
    exact h.symm
  have hclO : closure (F '' out) = F '' out ∪ F '' Set.range γ := by
    rw [himg, hcl2, Set.image_union]
  -- `out` is path connected, hence so is its image.
  have hConn : IsConnected (F '' out) :=
    houtpc.isConnected.image F F.continuous.continuousOn
  -- apply the abstract topological core and identify `Set.range v` with the transported curve.
  obtain ⟨hsub, hconn⟩ := isConnected_compl_of_cover hCO hIO hConn hclO
  exact ⟨by rw [hrange]; exact hsub, hconn⟩

end Work.RPB1a
