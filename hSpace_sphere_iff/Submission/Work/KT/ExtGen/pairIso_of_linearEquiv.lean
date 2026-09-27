import Mathlib
import Submission.Work.KT.ExtGen.Basic
import Submission.Work.KT.ExtGen.Radial
import Submission.Work.KT.ExtGen.RadialProd
import Submission.Work.KT.ExtGen.prodAlgPullbackEquiv

namespace Work.KT.ExtGen

open Work.KT

noncomputable section

/-! ## Action of the projection inclusions on the underlying functions -/

variable {V W V' W' : Type}
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V']
  [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']

@[simp] lemma pullFst_coe (g : Kpair V) :
    (pullFst V W g : C(Ball (V × W), ℂ)) = (g : C(Ball V, ℂ)).comp (prFst V W) := rfl

@[simp] lemma pullSnd_coe (g : Kpair W) :
    (pullSnd V W g : C(Ball (V × W), ℂ)) = (g : C(Ball W, ℂ)).comp (prSnd V W) := rfl

@[simp] lemma smashIncl_coe (g : Kpair (V × W)) :
    (smashIncl V W g : C(Ball (V × W), ℂ)) = (g : C(Ball (V × W), ℂ)) := rfl

/-! ## Augmentation along `pairPullbackEquiv` -/

/-- The augmentation of `Kpair U'` at a point `y'` pulls back along `pairPullbackEquiv f g` to the
augmentation of `Kpair U` at `f y'`. -/
lemma pairPullbackEquiv_aug {U U' : Type} [NormedAddCommGroup U] [NormedAddCommGroup U']
    (f : C(Ball U', Ball U)) (g : C(Ball U, Ball U'))
    (hfg : ∀ y : Ball U', g (f y) = y) (hgf : ∀ x : Ball U, f (g x) = x)
    (h1 : ∀ y : Ball U', y ∈ bdry U' → f y ∈ bdry U)
    (h2 : ∀ x : Ball U, x ∈ bdry U → g x ∈ bdry U') (y' : Ball U') :
    (augPair U' y').comp (pairPullbackEquiv f g hfg hgf h1 h2).toAlgHom = augPair U (f y') := by
  ext F
  rfl

/-! ## The four algebra isomorphisms -/

/-- Pullback of `Kpair` along the radial ball homeomorphism of `eV`. -/
noncomputable def pairIsoEV (eV : V ≃ₗ[ℝ] V') : Kpair V ≃ₐ[ℂ] Kpair V' :=
  pairPullbackEquiv (psiBallCM eV) (phiBallCM eV)
    (fun y => phiBall_psiBall eV y) (fun x => psiBall_phiBall eV x)
    (fun y hy => psiBall_mem_bdry eV hy) (fun x hx => phiBall_mem_bdry eV hx)

@[simp] lemma pairIsoEV_coe (eV : V ≃ₗ[ℝ] V') (F : Kpair V) :
    (pairIsoEV eV F : C(Ball V', ℂ)) = (F : C(Ball V, ℂ)).comp (psiBallCM eV) := rfl

@[simp] lemma pairIsoEV_toAlgHom_apply (eV : V ≃ₗ[ℝ] V') (F : Kpair V) :
    ((pairIsoEV eV).toAlgHom F : C(Ball V', ℂ)) = (F : C(Ball V, ℂ)).comp (psiBallCM eV) :=
  pairIsoEV_coe eV F

/-- Pullback of `Kpair` along the radial ball homeomorphism of `eW`. -/
noncomputable def pairIsoEW (eW : W ≃ₗ[ℝ] W') : Kpair W ≃ₐ[ℂ] Kpair W' :=
  pairPullbackEquiv (psiBallCM eW) (phiBallCM eW)
    (fun y => phiBall_psiBall eW y) (fun x => psiBall_phiBall eW x)
    (fun y hy => psiBall_mem_bdry eW hy) (fun x hx => phiBall_mem_bdry eW hx)

@[simp] lemma pairIsoEW_coe (eW : W ≃ₗ[ℝ] W') (F : Kpair W) :
    (pairIsoEW eW F : C(Ball W', ℂ)) = (F : C(Ball W, ℂ)).comp (psiBallCM eW) := rfl

@[simp] lemma pairIsoEW_toAlgHom_apply (eW : W ≃ₗ[ℝ] W') (F : Kpair W) :
    ((pairIsoEW eW).toAlgHom F : C(Ball W', ℂ)) = (F : C(Ball W, ℂ)).comp (psiBallCM eW) :=
  pairIsoEW_coe eW F

/-- Pullback of `Kpair` along the product radial ball homeomorphism. -/
noncomputable def pairIsoEPi (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') :
    Kpair (V × W) ≃ₐ[ℂ] Kpair (V' × W') :=
  pairPullbackEquiv (psiBallProdCM eV eW) (phiBallProdCM eV eW)
    (fun z => phiBallProd_psiBallProd eV eW z) (fun z => psiBallProd_phiBallProd eV eW z)
    (fun z hz => psiBallProd_mem_bdry eV eW hz) (fun z hz => phiBallProd_mem_bdry eV eW hz)

@[simp] lemma pairIsoEPi_coe (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') (F : Kpair (V × W)) :
    (pairIsoEPi eV eW F : C(Ball (V' × W'), ℂ))
      = (F : C(Ball (V × W), ℂ)).comp (psiBallProdCM eV eW) := rfl

@[simp] lemma pairIsoEPi_toAlgHom_apply (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') (F : Kpair (V × W)) :
    ((pairIsoEPi eV eW).toAlgHom F : C(Ball (V' × W'), ℂ))
      = (F : C(Ball (V × W), ℂ)).comp (psiBallProdCM eV eW) :=
  pairIsoEPi_coe eV eW F

/-- Pullback of the subalgebra `prodAlg` along the product radial ball homeomorphism. -/
noncomputable def pairIsoPhi (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') :
    prodAlg V W ≃ₐ[ℂ] prodAlg V' W' :=
  Classical.choose (prodAlgPullbackEquiv V W V' W' eV eW)

@[simp] lemma pairIsoPhi_coe (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') (F : prodAlg V W) :
    (pairIsoPhi eV eW F : C(Ball (V' × W'), ℂ))
      = (F : C(Ball (V × W), ℂ)).comp (psiBallProdCM eV eW) :=
  (Classical.choose_spec (prodAlgPullbackEquiv V W V' W' eV eW)).1 F

@[simp] lemma pairIsoPhi_toAlgHom_apply (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') (F : prodAlg V W) :
    ((pairIsoPhi eV eW).toAlgHom F : C(Ball (V' × W'), ℂ))
      = (F : C(Ball (V × W), ℂ)).comp (psiBallProdCM eV eW) :=
  pairIsoPhi_coe eV eW F

lemma pairIsoPhi_symm_coe (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') (G : prodAlg V' W') :
    ((pairIsoPhi eV eW).symm G : C(Ball (V × W), ℂ))
      = (G : C(Ball (V' × W'), ℂ)).comp (phiBallProdCM eV eW) :=
  (Classical.choose_spec (prodAlgPullbackEquiv V W V' W' eV eW)).2 G

/-! ## Compatibility of `pairIsoPhi` with the projections -/

lemma pairIsoPhi_comp_pullFst (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') :
    (pairIsoPhi eV eW).toAlgHom.comp (pullFst V W) =
      (pullFst V' W').comp (pairIsoEV eV).toAlgHom := by
  apply AlgHom.ext
  intro g
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z'
  simp only [AlgHom.comp_apply, pairIsoPhi_toAlgHom_apply, pairIsoEV_toAlgHom_apply, pullFst_coe,
    ContinuousMap.comp_apply, psiBallProdCM_apply, psiBallCM_apply, prFst_psiBallProd]

lemma pairIsoPhi_comp_pullSnd (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') :
    (pairIsoPhi eV eW).toAlgHom.comp (pullSnd V W) =
      (pullSnd V' W').comp (pairIsoEW eW).toAlgHom := by
  apply AlgHom.ext
  intro g
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z'
  simp only [AlgHom.comp_apply, pairIsoPhi_toAlgHom_apply, pairIsoEW_toAlgHom_apply, pullSnd_coe,
    ContinuousMap.comp_apply, psiBallProdCM_apply, psiBallCM_apply, prSnd_psiBallProd]

lemma pairIsoPhi_comp_smashIncl (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') :
    (pairIsoPhi eV eW).toAlgHom.comp (smashIncl V W) =
      (smashIncl V' W').comp (pairIsoEPi eV eW).toAlgHom := by
  apply AlgHom.ext
  intro g
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z'
  simp only [AlgHom.comp_apply, pairIsoPhi_toAlgHom_apply, pairIsoEPi_toAlgHom_apply, smashIncl_coe,
    ContinuousMap.comp_apply]

/-! ## Augmentation lemmas for the four isomorphisms -/

lemma pairIsoEV_aug (eV : V ≃ₗ[ℝ] V') (y' : Ball V') :
    (augPair V' y').comp (pairIsoEV eV).toAlgHom = augPair V (psiBall eV y') :=
  pairPullbackEquiv_aug (psiBallCM eV) (phiBallCM eV) _ _ _ _ y'

lemma pairIsoEW_aug (eW : W ≃ₗ[ℝ] W') (y' : Ball W') :
    (augPair W' y').comp (pairIsoEW eW).toAlgHom = augPair W (psiBall eW y') :=
  pairPullbackEquiv_aug (psiBallCM eW) (phiBallCM eW) _ _ _ _ y'

lemma pairIsoEPi_aug (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') (z' : Ball (V' × W')) :
    (augPair (V' × W') z').comp (pairIsoEPi eV eW).toAlgHom
      = augPair (V × W) (psiBallProd eV eW z') :=
  pairPullbackEquiv_aug (psiBallProdCM eV eW) (phiBallProdCM eV eW) _ _ _ _ z'

/-- ROUTE (node `ext_generator`, its dependency): transport of the pair structure along linear
isomorphisms (the "change of norm and dimension" step).

Construction: a linear isomorphism `e : V ≃ₗ[ℝ] V'` between normed spaces induces the homeomorphism
of ball pairs `φ : Ball V ≅ Ball V'`, `φ x = (‖x‖ / ‖e x‖) • e x` (with `φ 0 = 0`); it is norm
preserving, so it maps `bdry V` onto `bdry V'`.  The four isomorphisms are pullbacks along induced
maps of ball pairs: `EV` from `φ_V`, `EW` from `φ_W`, `EPi` from the product map
`(x,y) ↦ (φ_V x, φ_W y)` (using `Ball (V × W) ≅ Ball V × Ball W` for the maximum norm — this
product map is itself norm preserving), and `Phi` the same construction for the subalgebra
`prodAlg`.  The compatibility equations `hfst`, `hsnd`, `hsm` are the commutativity of the relevant
projections: on the underlying balls, `pr₁ ∘ (φ_V × φ_W) = φ_V ∘ pr₁` and similarly for the second
coordinate, while `smashIncl` is just the inclusion of `Kpair` into `prodAlg` on both sides.
The augmentation conditions `hV`, `hW`, `hPi` follow from norm preservation: for
`y' ∈ bdry V'`, take `y := φ_V.symm y'` (which lies on `bdry V`, since `φ_V` preserves norms) and
check `(augPair V' y').comp EV.toAlgHom = augPair V y` on functions (both sides evaluate at
`φ_V.symm`).

`Work.KT.pairPullbackEquiv` (in `ExtGen/Basic`) builds an algebra isomorphism `Kpair U ≃ₐ[ℂ] Kpair U'`
from a pair of mutually inverse continuous maps `Ball U' → Ball U`, `Ball U → Ball U'` preserving
the boundary; the same pattern (with membership conditions as hypotheses) gives `Phi` for the
subalgebras `prodAlg`, and `pairAssocEquiv` in the same file is an example of this construction. -/
theorem pairIso_of_linearEquiv (V W V' W' : Type) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    [NormedAddCommGroup V'] [NormedSpace ℝ V'] [FiniteDimensional ℝ V']
    [NormedAddCommGroup W'] [NormedSpace ℝ W'] [FiniteDimensional ℝ W']
    (eV : V ≃ₗ[ℝ] V') (eW : W ≃ₗ[ℝ] W') : Nonempty (pairIso V W V' W') :=
  ⟨{ EV := pairIsoEV eV
     EW := pairIsoEW eW
     EPi := pairIsoEPi eV eW
     Phi := pairIsoPhi eV eW
     hfst := pairIsoPhi_comp_pullFst eV eW
     hsnd := pairIsoPhi_comp_pullSnd eV eW
     hsm := pairIsoPhi_comp_smashIncl eV eW
     hV := fun y' hy' => ⟨psiBall eV y', psiBall_mem_bdry eV hy', pairIsoEV_aug eV y'⟩
     hW := fun y' hy' => ⟨psiBall eW y', psiBall_mem_bdry eW hy', pairIsoEW_aug eW y'⟩
     hPi := fun z' hz' => ⟨psiBallProd eV eW z', psiBallProd_mem_bdry eV eW hz',
        pairIsoEPi_aug eV eW z'⟩ }⟩

end

end Work.KT.ExtGen
