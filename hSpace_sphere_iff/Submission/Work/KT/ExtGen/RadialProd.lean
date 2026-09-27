import Mathlib
import Submission.Work.KT.ExtGen.Radial

/-!
# `Work.KT.ExtGen.RadialProd` — radial normalisation on products of balls

Given linear equivalences `V ≃ₗ[ℝ] V'` and `W ≃ₗ[ℝ] W'`, the product of the radial ball maps is a
norm-preserving map `Ball (V × W) → Ball (V' × W')` (for the maximum norm), with inverse the
product of the inverse maps.  Its components are the individual radial maps, which is what makes
it compatible with the projections `prFst`, `prSnd` and hence with `pullFst`, `pullSnd`,
`smashIncl`.
-/

namespace Work.KT.ExtGen

open Work.KT

noncomputable section

section Prod

variable {V W V' W' : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V']
  [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']

/-- The product of two radial ball maps. -/
def phiBallProd (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') (z : Ball (V × W)) : Ball (V' × W') :=
  ⟨((phiBall eV (prFst V W z) : V'), (phiBall eW (prSnd V W z) : W')), by
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    exact max_le (by rw [phiBall_norm]; exact mem_closedBall_zero_iff.mp (prFst V W z).2)
                 (by rw [phiBall_norm]; exact mem_closedBall_zero_iff.mp (prSnd V W z).2)⟩

/-- The inverse of `phiBallProd`, given by the product of the inverse radial ball maps. -/
def psiBallProd (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') (z : Ball (V' × W')) : Ball (V × W) :=
  ⟨((psiBall eV (prFst V' W' z) : V), (psiBall eW (prSnd V' W' z) : W)), by
    rw [mem_closedBall_zero_iff, Prod.norm_def]
    exact max_le (by rw [psiBall_norm]; exact mem_closedBall_zero_iff.mp (prFst V' W' z).2)
                 (by rw [psiBall_norm]; exact mem_closedBall_zero_iff.mp (prSnd V' W' z).2)⟩

@[simp] lemma coe_phiBallProd (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') (z : Ball (V × W)) :
    (phiBallProd eV eW z : V' × W') =
      ((phiBall eV (prFst V W z) : V'), (phiBall eW (prSnd V W z) : W')) := rfl

@[simp] lemma coe_psiBallProd (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') (z : Ball (V' × W')) :
    (psiBallProd eV eW z : V × W) =
      ((psiBall eV (prFst V' W' z) : V), (psiBall eW (prSnd V' W' z) : W)) := rfl

@[simp] lemma prFst_phiBallProd (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') (z : Ball (V × W)) :
    prFst V' W' (phiBallProd eV eW z) = phiBall eV (prFst V W z) := rfl

@[simp] lemma prSnd_phiBallProd (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') (z : Ball (V × W)) :
    prSnd V' W' (phiBallProd eV eW z) = phiBall eW (prSnd V W z) := rfl

@[simp] lemma prFst_psiBallProd (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') (z : Ball (V' × W')) :
    prFst V W (psiBallProd eV eW z) = psiBall eV (prFst V' W' z) := rfl

@[simp] lemma prSnd_psiBallProd (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') (z : Ball (V' × W')) :
    prSnd V W (psiBallProd eV eW z) = psiBall eW (prSnd V' W' z) := rfl

/-- `phiBallProd` preserves the norm. -/
@[simp] lemma phiBallProd_norm (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') (z : Ball (V × W)) :
    ‖(phiBallProd eV eW z : V' × W')‖ = ‖(z : V × W)‖ := by
  simp only [coe_phiBallProd, Prod.norm_def, phiBall_norm]
  rfl

/-- `psiBallProd` preserves the norm. -/
@[simp] lemma psiBallProd_norm (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') (z : Ball (V' × W')) :
    ‖(psiBallProd eV eW z : V × W)‖ = ‖(z : V' × W')‖ := by
  simp only [coe_psiBallProd, Prod.norm_def, psiBall_norm]
  rfl

/-- `phiBallProd` maps the boundary to the boundary. -/
lemma phiBallProd_mem_bdry (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') {z : Ball (V × W)}
    (hz : z ∈ bdry (V × W)) : phiBallProd eV eW z ∈ bdry (V' × W') := by
  change ‖(phiBallProd eV eW z : V' × W')‖ = 1
  rw [phiBallProd_norm]; exact hz

/-- `psiBallProd` maps the boundary to the boundary. -/
lemma psiBallProd_mem_bdry (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') {z : Ball (V' × W')}
    (hz : z ∈ bdry (V' × W')) : psiBallProd eV eW z ∈ bdry (V × W) := by
  change ‖(psiBallProd eV eW z : V × W)‖ = 1
  rw [psiBallProd_norm]; exact hz

/-- `psiBallProd` is a left inverse of `phiBallProd`. -/
@[simp] lemma psiBallProd_phiBallProd (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W')
    (z : Ball (V × W)) : psiBallProd eV eW (phiBallProd eV eW z) = z := by
  apply Subtype.ext
  apply Prod.ext
  · simp only [coe_psiBallProd, prFst_phiBallProd, psiBall_phiBall]; rfl
  · simp only [coe_psiBallProd, prSnd_phiBallProd, psiBall_phiBall]; rfl

/-- `phiBallProd` is a left inverse of `psiBallProd`. -/
@[simp] lemma phiBallProd_psiBallProd (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W')
    (z : Ball (V' × W')) : phiBallProd eV eW (psiBallProd eV eW z) = z := by
  apply Subtype.ext
  apply Prod.ext
  · simp only [coe_phiBallProd, prFst_psiBallProd, phiBall_psiBall]; rfl
  · simp only [coe_phiBallProd, prSnd_psiBallProd, phiBall_psiBall]; rfl

/-- `phiBallProd` is continuous. -/
lemma continuous_phiBallProd (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') :
    Continuous (phiBallProd eV eW) := by
  refine Continuous.subtype_mk (f := fun z : Ball (V × W) =>
    ((phiBall eV (prFst V W z) : V'), (phiBall eW (prSnd V W z) : W'))) ?_ ?_
  exact Continuous.prodMk
    (continuous_subtype_val.comp ((continuous_phiBall eV).comp (prFst V W).continuous))
    (continuous_subtype_val.comp ((continuous_phiBall eW).comp (prSnd V W).continuous))

/-- `psiBallProd` is continuous. -/
lemma continuous_psiBallProd (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') :
    Continuous (psiBallProd eV eW) := by
  refine Continuous.subtype_mk (f := fun z : Ball (V' × W') =>
    ((psiBall eV (prFst V' W' z) : V), (psiBall eW (prSnd V' W' z) : W))) ?_ ?_
  exact Continuous.prodMk
    (continuous_subtype_val.comp ((continuous_psiBall eV).comp (prFst V' W').continuous))
    (continuous_subtype_val.comp ((continuous_psiBall eW).comp (prSnd V' W').continuous))

/-- `phiBallProd` as a continuous map. -/
def phiBallProdCM (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') :
    C(Ball (V × W), Ball (V' × W')) := ⟨phiBallProd eV eW, continuous_phiBallProd eV eW⟩

/-- `psiBallProd` as a continuous map. -/
def psiBallProdCM (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') :
    C(Ball (V' × W'), Ball (V × W)) := ⟨psiBallProd eV eW, continuous_psiBallProd eV eW⟩

@[simp] lemma phiBallProdCM_apply (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') (z : Ball (V × W)) :
    phiBallProdCM eV eW z = phiBallProd eV eW z := rfl

@[simp] lemma psiBallProdCM_apply (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') (z : Ball (V' × W')) :
    psiBallProdCM eV eW z = psiBallProd eV eW z := rfl

end Prod

end

end Work.KT.ExtGen
