import Mathlib
import Submission.Work.ATOM.ZS.NullSeqMaps
import Submission.Work.ATOM.ZS.gBig_aug_zero
import Submission.Work.ATOM.unitor_whisker_comp

namespace Work.ATOM.ZS

open CategoryTheory Limits MonoidalCategory LightCondensed

/-!
# Identity `h₅` of REFS/03 §1: `g̃ ≫ s = s_P ≫ (id_P ⊗ g)`

The two ingredients are supplied by the shared library:

* `Work.ATOM.ZS.gBig_aug_zero` — the glued null sequence has augmentation zero,
  `gBig ≫ aug = 0` (whose proof uses `Work.ATOM.epi_zmap_of_surjective`, the epimorphy of `ℤ[π]`
  for a surjection `π`, hence the uniqueness half of the descent `Work.ATOM.zdesc`);
* `Work.ATOM.unitor_whisker_comp` — the monoidal coherence `(λ_ P).inv ≫ (e ▷ P) ≫ (P ◁ g) =
  g ≫ (λ_ W).inv ≫ (e ▷ W)` (`MonoidalCategory.whisker_exchange` plus naturality of the unitor).

`g_comp_aug` transfers the augmentation vanishing from `gBig` to `g = P_homMk gBig` by cancelling
the cokernel projection `P_proj`, which is epimorphic; `sP_comp_m` is the shared coherence lemma
applied to `e₀ : 𝟙_ ⟶ P` and `g : P ⟶ ℤ[S]`.

`h_five` itself is then `qred ≫ s = sHat` (`Work.ATOM.s_spec`) together with the vanishing of the
correction term `g ≫ aug = 0` in `sHat = (𝟙 - aug ≫ [s₀]) ≫ sBig`.
-/

/-- The null sequence `g : P ⟶ ℤ[S]` has augmentation zero: `g = P_homMk ℤ[S] gBig` is obtained
from `gBig ≫ aug = 0` by cancelling the epimorphism `P_proj` (`Work.ATOM.g_spec`). -/
private theorem g_comp_aug (S : LightProfinite.{0}) [Infinite S] :
    Work.ATOM.g S ≫ Work.ATOM.aug S = 0 := by
  have hkey : LightCondensed.P_proj ≫ (Work.ATOM.g S ≫ Work.ATOM.aug S) = 0 := by
    rw [← Category.assoc, Work.ATOM.g_spec S, gBig_aug_zero S]
  have hP : Epi LightCondensed.P_proj := by
    change Epi (cokernel.π (LightCondensed.P_map))
    infer_instance
  exact hP.left_cancellation _ _ hkey

/-- `sP ≫ m = g ≫ sBig`: the shared `MonoidalCategory` coherence `Work.ATOM.unitor_whisker_comp`
applied to the unit map `e₀ : 𝟙_ ⟶ P` and the null sequence `g : P ⟶ ℤ[S]`. -/
private theorem sP_comp_m (S : LightProfinite.{0}) [Infinite S] :
    Work.ATOM.sP ≫ Work.ATOM.m S = Work.ATOM.g S ≫ Work.ATOM.sBig S := by
  show ((λ_ LightCondensed.P).inv ≫ (Work.ATOM.e0 ▷ LightCondensed.P)) ≫
      (LightCondensed.P ◁ Work.ATOM.g S) =
    Work.ATOM.g S ≫
      ((λ_ (Work.ATOM.zfree S)).inv ≫ (Work.ATOM.e0 ▷ Work.ATOM.zfree S))
  exact unitor_whisker_comp Work.ATOM.e0 (Work.ATOM.g S)

/-- **Identity `h₅` of REFS/03 §1**: `g̃ ≫ s = s_P ≫ (id_P ⊗ g)`.  Both sides send `e_j` to
`e₀ ⊗ g(e_j)`: the left side uses `qred ≫ s = sHat` (`Work.ATOM.s_spec`) and
`g ≫ aug = 0` (so that the correction term in `sHat` dies); the right side is the definition of
`s_P` (`Work.ATOM.sP`, which takes no argument `S`) combined with `Work.ATOM.m S = P ◁ g`. -/
theorem h_five (S : LightProfinite.{0}) [Infinite S] :
    Work.ATOM.gRed S ≫ Work.ATOM.s S = Work.ATOM.sP ≫ Work.ATOM.m S := by
  have h2 : Work.ATOM.g S ≫ (Work.ATOM.aug S ≫
      Work.ATOM.zmap (Work.ATOM.ptAt (Work.ATOM.levelData S).s₀)) = 0 := by
    rw [← Category.assoc, g_comp_aug S, zero_comp]
  have hstep : Work.ATOM.gRed S ≫ Work.ATOM.s S = Work.ATOM.g S ≫ Work.ATOM.sBig S := by
    rw [Work.ATOM.gRed, Category.assoc, Work.ATOM.s_spec, Work.ATOM.sHat]
    rw [← Category.assoc, Preadditive.comp_sub, Category.comp_id, h2, sub_zero]
  rw [hstep, sP_comp_m S]

end Work.ATOM.ZS
