import Mathlib
import Submission.Work.Clifford.ResSetup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Clifford.subChar_conjSub`

For a finite group `G`, a normal subgroup `N ⊴ G`, a representation `V : FDRep ℂ G` and a
`ℂ[N]`-submodule `W ≤ ResMod N V`, conjugation by `g : G` identifies `W` with `conjSub V g W`
as `ℂ`-vector spaces, and intertwines the action of `n : N` on `conjSub V g W` with the action
of `g⁻¹ n g` on `W`.  Hence the two characters agree:

`subChar V (conjSub V g W) n = subChar V W (conjHomHom g n)`.
-/

noncomputable section

open Classical
open scoped MonoidAlgebra

namespace Work.Clifford

universe u

variable {G : Type u} [Group G] [Fintype G]
variable {N : Subgroup G} [N.Normal]

/-! ### Elementary identities for the action of `G` -/

/-- The dual form of `resAct_inv`: `ρ g (ρ g⁻¹ x) = x`. -/
theorem resAct_inv' (N : Subgroup G) (V : FDRep ℂ G) (g : G) (x : ResMod N V) :
    resAct N V g (resAct N V (g⁻¹) x) = x := by
  rw [resAct_mul, mul_inv_cancel, resAct_one]

/-- Conjugation by `g` intertwines the actions of `g⁻¹ n g` and of `n`. -/
theorem resAct_conjHomHom (V : FDRep ℂ G) (g : G) (n : N) (x : ResMod N V) :
    resAct N V g (resAct N V (conjHomHom g n) x) = resAct N V n (resAct N V g x) := by
  have hg : g * ((conjHomHom g n : N) : G) = ((n : N) : G) * g := by
    rw [conjHomHom_apply]; group
  rw [resAct_mul, resAct_mul, hg]

/-! ### The two linear maps relating `W` and `conjSub V g W` -/

/-- The linear map `W → conjSub V g W` induced by the action of `g` on `ResMod N V`. -/
def conjSubLM (V : FDRep ℂ G) (g : G) (W : Submodule ℂ[N] (ResMod N V)) :
    W →ₗ[ℂ] conjSub (N := N) V g W where
  toFun w := ⟨resAct N V g (w : ResMod N V), conjSub_apply_mem (N := N) V g W w.2⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' c x := Subtype.ext (by simp)

/-- The linear map `conjSub V g W → W` induced by the action of `g⁻¹`. -/
def conjSubLMInv (V : FDRep ℂ G) (g : G) (W : Submodule ℂ[N] (ResMod N V)) :
    conjSub (N := N) V g W →ₗ[ℂ] W where
  toFun x := ⟨resAct N V (g⁻¹) (x : ResMod N V), by
    obtain ⟨w, hw, hwx⟩ := (mem_conjSub (N := N) V g W x).mp x.2
    rw [← hwx, resAct_inv]
    exact hw⟩
  map_add' x y := Subtype.ext (by simp)
  map_smul' c x := Subtype.ext (by simp)

@[simp]
theorem conjSubLM_apply (V : FDRep ℂ G) (g : G) (W : Submodule ℂ[N] (ResMod N V))
    (w : W) :
    ((conjSubLM V g W w : conjSub (N := N) V g W) : ResMod N V) =
      resAct N V g (w : ResMod N V) := rfl

@[simp]
theorem conjSubLMInv_apply (V : FDRep ℂ G) (g : G) (W : Submodule ℂ[N] (ResMod N V))
    (x : conjSub (N := N) V g W) :
    ((conjSubLMInv V g W x : W) : ResMod N V) = resAct N V (g⁻¹) (x : ResMod N V) := rfl

theorem conjSubLMInv_conjSubLM (V : FDRep ℂ G) (g : G) (W : Submodule ℂ[N] (ResMod N V))
    (w : W) : conjSubLMInv V g W (conjSubLM V g W w) = w := by
  apply Subtype.ext
  rw [conjSubLMInv_apply, conjSubLM_apply, resAct_inv]

theorem conjSubLM_conjSubLMInv (V : FDRep ℂ G) (g : G) (W : Submodule ℂ[N] (ResMod N V))
    (x : conjSub (N := N) V g W) : conjSubLM V g W (conjSubLMInv V g W x) = x := by
  apply Subtype.ext
  rw [conjSubLM_apply, conjSubLMInv_apply, resAct_inv']

/-! ### The intertwining identity -/

theorem conjSubLM_subAct (V : FDRep ℂ G) (g : G) (W : Submodule ℂ[N] (ResMod N V)) (n : N)
    (x : conjSub (N := N) V g W) :
    conjSubLM V g W (subAct V W (conjHomHom g n) (conjSubLMInv V g W x)) =
      subAct V (conjSub (N := N) V g W) n x := by
  apply Subtype.ext
  rw [conjSubLM_apply, subAct_apply, conjSubLMInv_apply, subAct_apply, resAct_conjHomHom,
    resAct_inv']

/-- Conjugation by `g` as a `ℂ`-linear equivalence `W ≃ conjSub V g W`. -/
def conjSubEquiv (V : FDRep ℂ G) (g : G) (W : Submodule ℂ[N] (ResMod N V)) :
    W ≃ₗ[ℂ] conjSub (N := N) V g W where
  toFun := conjSubLM V g W
  map_add' := (conjSubLM V g W).map_add
  map_smul' := (conjSubLM V g W).map_smul
  invFun := conjSubLMInv V g W
  left_inv := conjSubLMInv_conjSubLM V g W
  right_inv := conjSubLM_conjSubLMInv V g W

@[simp]
theorem conjSubEquiv_apply (V : FDRep ℂ G) (g : G) (W : Submodule ℂ[N] (ResMod N V))
    (w : W) :
    ((conjSubEquiv V g W w : conjSub (N := N) V g W) : ResMod N V) =
      resAct N V g (w : ResMod N V) := rfl

/-- `conjSubEquiv` conjugates the action of `g⁻¹ n g` on `W` to the action of `n` on
`conjSub V g W`. -/
theorem conjSubEquiv_conj_subAct (V : FDRep ℂ G) (g : G) (W : Submodule ℂ[N] (ResMod N V))
    (n : N) :
    (conjSubEquiv V g W).conj (subAct V W (conjHomHom g n)) =
      subAct V (conjSub (N := N) V g W) n := by
  refine LinearMap.ext fun x => ?_
  exact conjSubLM_subAct V g W n x

/-! ### The character identity -/

theorem subChar_conjSub {G : Type*} [Group G] [Fintype G] {N : Subgroup G} [N.Normal]
    (V : FDRep ℂ G) (g : G) (W : Submodule (MonoidAlgebra ℂ ↥N) (ResMod N V)) (n : N) :
    subChar V (conjSub V g W) n = subChar V W (conjHomHom g n) := by
  rw [subChar_apply, subChar_apply, ← conjSubEquiv_conj_subAct V g W n,
    LinearMap.trace_conj']

end Work.Clifford
