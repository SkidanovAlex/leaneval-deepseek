import Mathlib
import Submission.Work.HomologyMV.Model
import Submission.Work.HomologyMV.Data

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `HomologyMV/`: the concrete Mayer–Vietoris model maps

`Work.HomologyMV.allPhi k` assembles the matrices of `Data.lean`
(`φ₀, φ₁, φ₂, φ₃`, generated from `rtdata`) into a single family indexed by the degree, with the
zero map in degrees `≥ 4` (where both model groups are zero), and `wConcrete k` is the
corresponding morphism of `ModuleCat ℤ`

`wConcrete k : ModelM k ⟶ ModelN k`.

The two certificate theorems are proved in `Submission/Work/HomologyMV/wConcrete_surj.lean` and
`Submission/Work/HomologyMV/wConcrete_ker.lean`:

* `Work.HomologyMV.wConcrete_surj : SurjCert wConcrete` — `φ_k` is surjective for `k ≥ 1`,
* `Work.HomologyMV.wConcrete_ker : KernelCert wConcrete` — `ker φ_k` is `ℤ` in degree `3` and
  zero otherwise.

These are the two inputs that the assembly theorem `Work.HomologyMV.mv_homology` consumes from
the integer-linear-algebra side.
-/

namespace Work.HomologyMV

open CategoryTheory

noncomputable section

/-- The Mayer–Vietoris matrices in all degrees: `φ₀` in degree `0`, `φ₁` in degree `1`, `φ₂` in
degree `2`, `φ₃` in degree `3`, and the zero matrix in every other degree (where both model
groups are zero). -/
def allPhi : ∀ k : ℤ, Matrix (Fin (rankN k)) (Fin (rankM k)) ℤ
  | 0 => phi0Mat
  | 1 => phi1Mat
  | 2 => phi2Mat
  | 3 => phi3Mat
  | _ => 0

@[simp] theorem allPhi_zero : allPhi 0 = phi0Mat := rfl
@[simp] theorem allPhi_one : allPhi 1 = phi1Mat := rfl
@[simp] theorem allPhi_two : allPhi 2 = phi2Mat := rfl
@[simp] theorem allPhi_three : allPhi 3 = phi3Mat := rfl

/-- The concrete model map `wConcrete k = φ_k` as a morphism `ModelM k ⟶ ModelN k`. -/
def wConcrete (k : ℤ) : ModelM k ⟶ ModelN k :=
  ModuleCat.ofHom (Matrix.toLin' (allPhi k))

@[simp] theorem wConcrete_hom (k : ℤ) : (wConcrete k).hom = Matrix.toLin' (allPhi k) := rfl

@[simp] theorem wConcrete_zero : wConcrete 0 = ModuleCat.ofHom (Matrix.toLin' phi0Mat) := rfl
@[simp] theorem wConcrete_one : wConcrete 1 = ModuleCat.ofHom (Matrix.toLin' phi1Mat) := rfl
@[simp] theorem wConcrete_two : wConcrete 2 = ModuleCat.ofHom (Matrix.toLin' phi2Mat) := rfl
@[simp] theorem wConcrete_three : wConcrete 3 = ModuleCat.ofHom (Matrix.toLin' phi3Mat) := rfl

theorem rankM_eq_zero_of_ge (k : ℤ) (hk : 4 ≤ k) : rankM k = 0 :=
  rankM_eq_zero k (by omega) (by omega) (by omega) (by omega)

theorem rankN_eq_zero_of_ge (k : ℤ) (hk : 4 ≤ k) : rankN k = 0 :=
  rankN_eq_zero k (by omega) (by omega) (by omega) (by omega)

/-- The model group `ModelM k` is trivial in degrees `≥ 4`. -/
theorem subsingleton_modelM_of_ge (k : ℤ) (hk : 4 ≤ k) : Subsingleton (ModelM k) := by
  rw [ModelM, freeMod, rankM_eq_zero_of_ge k hk]
  infer_instance

/-- The model group `ModelN k` is trivial in degrees `≥ 4`. -/
theorem subsingleton_modelN_of_ge (k : ℤ) (hk : 4 ≤ k) : Subsingleton (ModelN k) := by
  rw [ModelN, freeMod, rankN_eq_zero_of_ge k hk]
  infer_instance

end

end Work.HomologyMV
