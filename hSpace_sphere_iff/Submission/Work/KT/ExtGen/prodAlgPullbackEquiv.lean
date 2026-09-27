import Mathlib
import Submission.Work.KT.ExtGen.RadialProd

/-!
# `Work.KT.ExtGen.prodAlgPullbackEquiv`

The pullback algebra equivalence of `prodAlg` along the product radial homeomorphism
`phiBallProd`/`psiBallProd` induced by linear equivalences `V ≃ₗ[ℝ] V'`, `W ≃ₗ[ℝ] W'`.

`prodAlg V W = C((D_V/S_V) × (D_W/S_W))` is the subalgebra of `C(D_V × D_W, ℂ)` of functions
constant along `x` on the boundary of `D_V` and along `y` on the boundary of `D_W`.  Because
`psiBallProd` (resp. `phiBallProd`) preserves both coordinates (through `psiBall`/`phiBall`) and
is norm-preserving, pullback along it maps `prodAlg` into `prodAlg`, and the two directions are
mutually inverse.  This gives the algebra equivalence `prodAlg V W ≃ₐ[ℂ] prodAlg V' W'`, whose
underlying maps are literally `F ↦ F ∘ psiBallProd` and `G ↦ G ∘ phiBallProd`.
-/

set_option linter.unusedSimpArgs false

namespace Work.KT.ExtGen

open Work.KT

noncomputable section

section Prod

variable {V W V' W' : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V']
  [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']

/-- `psiBallProdCM` then `phiBallProdCM` is the identity on `Ball (V × W)`. -/
@[simp] lemma psiBallProdCM_phiBallProdCM (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W')
    (z : Ball (V × W)) : psiBallProdCM eV eW (phiBallProdCM eV eW z) = z := by
  simp

/-- `phiBallProdCM` then `psiBallProdCM` is the identity on `Ball (V' × W')`. -/
@[simp] lemma phiBallProdCM_psiBallProdCM (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W')
    (z : Ball (V' × W')) : phiBallProdCM eV eW (psiBallProdCM eV eW z) = z := by
  simp

/-- Pullback of `prodAlg` along `psiBallProdCM` lands in `prodAlg`. -/
lemma comp_psiBallProdCM_mem (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') (F : prodAlg V W) :
    (F : C(Ball (V × W), ℂ)).comp (psiBallProdCM eV eW) ∈ prodAlg V' W' := by
  refine ⟨?_, ?_⟩
  · intro z z' hz hz' h2
    have hsnd : prSnd V' W' z = prSnd V' W' z' := by apply Subtype.ext; exact h2
    have hmem1 : ‖((psiBallProd eV eW z : Ball (V × W)) : V × W).1‖ = 1 := by
      rw [coe_psiBallProd, psiBall_norm]; exact hz
    have hmem1' : ‖((psiBallProd eV eW z' : Ball (V × W)) : V × W).1‖ = 1 := by
      rw [coe_psiBallProd, psiBall_norm]; exact hz'
    have hmem2 : ((psiBallProd eV eW z : Ball (V × W)) : V × W).2 =
        ((psiBallProd eV eW z' : Ball (V × W)) : V × W).2 := by
      rw [coe_psiBallProd, coe_psiBallProd]
      exact congrArg (fun y : Ball W' => (psiBall eW y : W)) hsnd
    have key := F.2.1 (psiBallProd eV eW z) (psiBallProd eV eW z') hmem1 hmem1' hmem2
    simpa [ContinuousMap.comp_apply, psiBallProdCM_apply] using key
  · intro z z' hz hz' h1
    have hfst : prFst V' W' z = prFst V' W' z' := by apply Subtype.ext; exact h1
    have hmem2 : ‖((psiBallProd eV eW z : Ball (V × W)) : V × W).2‖ = 1 := by
      rw [coe_psiBallProd, psiBall_norm]; exact hz
    have hmem2' : ‖((psiBallProd eV eW z' : Ball (V × W)) : V × W).2‖ = 1 := by
      rw [coe_psiBallProd, psiBall_norm]; exact hz'
    have hmem1 : ((psiBallProd eV eW z : Ball (V × W)) : V × W).1 =
        ((psiBallProd eV eW z' : Ball (V × W)) : V × W).1 := by
      rw [coe_psiBallProd, coe_psiBallProd]
      exact congrArg (fun y : Ball V' => (psiBall eV y : V)) hfst
    have key := F.2.2 (psiBallProd eV eW z) (psiBallProd eV eW z') hmem2 hmem2' hmem1
    simpa [ContinuousMap.comp_apply, psiBallProdCM_apply] using key

/-- Pullback of `prodAlg` along `phiBallProdCM` lands in `prodAlg`. -/
lemma comp_phiBallProdCM_mem (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') (G : prodAlg V' W') :
    (G : C(Ball (V' × W'), ℂ)).comp (phiBallProdCM eV eW) ∈ prodAlg V W := by
  refine ⟨?_, ?_⟩
  · intro z z' hz hz' h2
    have hsnd : prSnd V W z = prSnd V W z' := by apply Subtype.ext; exact h2
    have hmem1 : ‖((phiBallProd eV eW z : Ball (V' × W')) : V' × W').1‖ = 1 := by
      rw [coe_phiBallProd, phiBall_norm]; exact hz
    have hmem1' : ‖((phiBallProd eV eW z' : Ball (V' × W')) : V' × W').1‖ = 1 := by
      rw [coe_phiBallProd, phiBall_norm]; exact hz'
    have hmem2 : ((phiBallProd eV eW z : Ball (V' × W')) : V' × W').2 =
        ((phiBallProd eV eW z' : Ball (V' × W')) : V' × W').2 := by
      rw [coe_phiBallProd, coe_phiBallProd]
      exact congrArg (fun y : Ball W => (phiBall eW y : W')) hsnd
    have key := G.2.1 (phiBallProd eV eW z) (phiBallProd eV eW z') hmem1 hmem1' hmem2
    simpa [ContinuousMap.comp_apply, phiBallProdCM_apply] using key
  · intro z z' hz hz' h1
    have hfst : prFst V W z = prFst V W z' := by apply Subtype.ext; exact h1
    have hmem2 : ‖((phiBallProd eV eW z : Ball (V' × W')) : V' × W').2‖ = 1 := by
      rw [coe_phiBallProd, phiBall_norm]; exact hz
    have hmem2' : ‖((phiBallProd eV eW z' : Ball (V' × W')) : V' × W').2‖ = 1 := by
      rw [coe_phiBallProd, phiBall_norm]; exact hz'
    have hmem1 : ((phiBallProd eV eW z : Ball (V' × W')) : V' × W').1 =
        ((phiBallProd eV eW z' : Ball (V' × W')) : V' × W').1 := by
      rw [coe_phiBallProd, coe_phiBallProd]
      exact congrArg (fun y : Ball V => (phiBall eV y : V')) hfst
    have key := G.2.2 (phiBallProd eV eW z) (phiBallProd eV eW z') hmem2 hmem2' hmem1
    simpa [ContinuousMap.comp_apply, phiBallProdCM_apply] using key

/-- The algebra equivalence `prodAlg V W ≃ₐ[ℂ] prodAlg V' W'` induced by the product radial
homeomorphism.  Its underlying maps are pullback along `psiBallProdCM` and along `phiBallProdCM`
respectively. -/
def prodAlgPullbackAlgEquiv (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') :
    prodAlg V W ≃ₐ[ℂ] prodAlg V' W' :=
  AlgEquiv.ofAlgHom
    (AlgHom.codRestrict
      ((ContinuousMap.compStarAlgHom' ℂ ℂ (psiBallProdCM eV eW)).toAlgHom.comp
        (prodAlg V W).val) (prodAlg V' W') (fun F => comp_psiBallProdCM_mem eV eW F))
    (AlgHom.codRestrict
      ((ContinuousMap.compStarAlgHom' ℂ ℂ (phiBallProdCM eV eW)).toAlgHom.comp
        (prodAlg V' W').val) (prodAlg V W) (fun G => comp_phiBallProdCM_mem eV eW G))
    (by
      apply AlgHom.ext
      intro G
      apply Subtype.ext
      apply ContinuousMap.ext
      intro x
      simp only [AlgHom.comp_apply, AlgHom.coe_id, id_eq, AlgHom.coe_comp,
        ContinuousMap.compStarAlgHom'_apply, StarAlgHom.coe_toAlgHom, AlgHom.coe_codRestrict,
        ContinuousMap.comp_apply, ContinuousMap.coe_mk, Subalgebra.coe_val, Function.comp_apply]
      exact congrArg (fun z => (G : Ball (V' × W') → ℂ) z) (phiBallProdCM_psiBallProdCM eV eW x))
    (by
      apply AlgHom.ext
      intro F
      apply Subtype.ext
      apply ContinuousMap.ext
      intro x
      simp only [AlgHom.comp_apply, AlgHom.coe_id, id_eq, AlgHom.coe_comp,
        ContinuousMap.compStarAlgHom'_apply, StarAlgHom.coe_toAlgHom, AlgHom.coe_codRestrict,
        ContinuousMap.comp_apply, ContinuousMap.coe_mk, Subalgebra.coe_val, Function.comp_apply]
      exact congrArg (fun z => (F : Ball (V × W) → ℂ) z) (psiBallProdCM_phiBallProdCM eV eW x))

theorem prodAlgPullbackEquiv (V W V' W' : Type)
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V']
    [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
    (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') :
    ∃ Φ : Work.KT.prodAlg V W ≃ₐ[ℂ] Work.KT.prodAlg V' W',
      (∀ F : Work.KT.prodAlg V W,
        (Φ F : C(Work.KT.Ball (V' × W'), ℂ)) =
          (F : C(Work.KT.Ball (V × W), ℂ)).comp (Work.KT.ExtGen.psiBallProdCM eV eW)) ∧
      (∀ G : Work.KT.prodAlg V' W',
        (Φ.symm G : C(Work.KT.Ball (V × W), ℂ)) =
          (G : C(Work.KT.Ball (V' × W'), ℂ)).comp (Work.KT.ExtGen.phiBallProdCM eV eW)) := by
  refine ⟨prodAlgPullbackAlgEquiv eV eW, ?_, ?_⟩
  · intro F
    rfl
  · intro G
    rfl

end Prod

end

end Work.KT.ExtGen
