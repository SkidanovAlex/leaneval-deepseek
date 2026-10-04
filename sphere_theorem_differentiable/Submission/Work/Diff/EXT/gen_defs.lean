import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Generic definitions for the splicing lemma (area `EXT`)

`Submission/Work/Diff/EXT/pde_defs.lean` sets up the objects of the splicing lemma for functions
`ℝ × ℝⁿ → ℝᵐ`.  The target statement `Work.Diff.EXT.pde_splice_local_E` is however about
functions `ℝ × E → MatE` with `E` an arbitrary finite-dimensional real normed space, and its
hypotheses are *local* (`ContDiffOn` on an open set, `ContDiffAt` at the seam).

This file therefore contains the same objects in the generality actually needed:
`sJetG`, `tderivG`, `AseqG`, `SeqG`, `PsiG` for functions `ℝ × E → F` with `E`, `F` arbitrary real
normed spaces.  (The domain `E` is never required to be finite-dimensional by the definitions nor
by the smoothness statements; finite-dimensionality is only needed for the bump-function step.)

The definitions are the ones of `pde_defs.lean` with `Fin n → ℝ` replaced by `E` and `Fin m → ℝ`
replaced by `F`; `jet2` of `splice_defs.lean` is `sJetG` with `F = MatE`.
-/

set_option linter.unusedSectionVars false

open scoped ContDiff

namespace Work.Diff.EXT

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The space of *spatial* `2`-jets of a map `ℝ × E → F` at a point: the value, the spatial first
derivative and the spatial second derivative. -/
abbrev JG (E F : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] : Type _ :=
  F × (E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F)

noncomputable instance (priority := 3000) instJGA_AddCommMonoid : AddCommMonoid (E →L[ℝ] F) :=
  inferInstanceAs (AddCommMonoid (E →L[ℝ] F))

noncomputable instance (priority := 3000) instJGA_AddCommGroup : AddCommGroup (E →L[ℝ] F) :=
  inferInstanceAs (AddCommGroup (E →L[ℝ] F))

noncomputable instance (priority := 3000) instJGA_ModuleR : Module ℝ (E →L[ℝ] F) :=
  inferInstanceAs (Module ℝ (E →L[ℝ] F))

noncomputable instance (priority := 3000) instJGA_NormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] F) :=
  inferInstanceAs (NormedAddCommGroup (E →L[ℝ] F))

noncomputable instance (priority := 3000) instJGA_NormedSpaceR : NormedSpace ℝ (E →L[ℝ] F) :=
  inferInstanceAs (NormedSpace ℝ (E →L[ℝ] F))

noncomputable instance (priority := 3000) instJGB_AddCommMonoid :
    AddCommMonoid (E →L[ℝ] E →L[ℝ] F) :=
  inferInstanceAs (AddCommMonoid (E →L[ℝ] E →L[ℝ] F))

noncomputable instance (priority := 3000) instJGB_AddCommGroup : AddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  inferInstanceAs (AddCommGroup (E →L[ℝ] E →L[ℝ] F))

noncomputable instance (priority := 3000) instJGB_ModuleR : Module ℝ (E →L[ℝ] E →L[ℝ] F) :=
  inferInstanceAs (Module ℝ (E →L[ℝ] E →L[ℝ] F))

noncomputable instance (priority := 3000) instJGB_NormedAddCommGroup :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  inferInstanceAs (NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F))

noncomputable instance (priority := 3000) instJGB_NormedSpaceR :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) :=
  inferInstanceAs (NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F))

noncomputable instance (priority := 3000) instJGBC_AddCommMonoid :
    AddCommMonoid ((E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F)) :=
  inferInstanceAs (AddCommMonoid ((E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F)))

noncomputable instance (priority := 3000) instJGBC_AddCommGroup :
    AddCommGroup ((E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F)) :=
  inferInstanceAs (AddCommGroup ((E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F)))

noncomputable instance (priority := 3000) instJGBC_ModuleR :
    Module ℝ ((E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F)) :=
  inferInstanceAs (Module ℝ ((E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F)))

noncomputable instance (priority := 3000) instJGBC_NormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F)) :=
  inferInstanceAs (NormedAddCommGroup ((E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F)))

noncomputable instance (priority := 3000) instJGBC_NormedSpaceR :
    NormedSpace ℝ ((E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F)) :=
  inferInstanceAs (NormedSpace ℝ ((E →L[ℝ] F) × (E →L[ℝ] E →L[ℝ] F)))

noncomputable instance (priority := 3000) instJG_AddCommMonoid : AddCommMonoid (JG E F) :=
  inferInstanceAs (AddCommMonoid (JG E F))

noncomputable instance (priority := 3000) instJG_AddCommGroup : AddCommGroup (JG E F) :=
  inferInstanceAs (AddCommGroup (JG E F))

noncomputable instance (priority := 3000) instJG_ModuleR : Module ℝ (JG E F) :=
  inferInstanceAs (Module ℝ (JG E F))

noncomputable instance (priority := 3000) instJG_NormedAddCommGroup : NormedAddCommGroup (JG E F) :=
  inferInstanceAs (NormedAddCommGroup (JG E F))

noncomputable instance (priority := 3000) instJG_NormedSpaceR : NormedSpace ℝ (JG E F) :=
  inferInstanceAs (NormedSpace ℝ (JG E F))

/-- The spatial `2`-jet of a function on `ℝ × E`, as a function of the base point. -/
noncomputable def sJetG (g : ℝ × E → F) : ℝ × E → JG E F :=
  fun z => (g z, fderiv ℝ (fun y : E => g (z.1, y)) z.2,
    fderiv ℝ (fun w : E => fderiv ℝ (fun y : E => g (z.1, y)) w) z.2)

/-- The derivative of a function on `ℝ × E` in the time direction. -/
noncomputable def tderivG (g : ℝ × E → F) : ℝ × E → F :=
  fun z => deriv (fun s => g (s, z.2)) z.1

/-- `sJetG` unfolded. -/
theorem sJetG_apply (g : ℝ × E → F) (z : ℝ × E) :
    sJetG g z = (g z, fderiv ℝ (fun y : E => g (z.1, y)) z.2,
      fderiv ℝ (fun w : E => fderiv ℝ (fun y : E => g (z.1, y)) w) z.2) := rfl

/-- `tderivG` unfolded. -/
theorem tderivG_apply (g : ℝ × E → F) (z : ℝ × E) :
    tderivG g z = deriv (fun s : ℝ => g (s, z.2)) z.1 := rfl

/-- The sequence of time derivatives of the right hand side `Φ(·,Ju)` of the parabolic system
along a function `a`: `AseqG Φ a j` is `∂ₜ^j (Φ(·,J a))`. -/
noncomputable def AseqG (Φ : E × JG E F → F) (a : ℝ × E → F) : ℕ → (ℝ × E → F)
  | 0 => fun z => Φ (z.2, sJetG a z)
  | (j + 1) => tderivG (AseqG Φ a j)

/-- `SeqG Φ a 0 = a` and `SeqG Φ a (j+1) = AseqG Φ a j`. -/
noncomputable def SeqG (Φ : E × JG E F → F) (a : ℝ × E → F) : ℕ → (ℝ × E → F)
  | 0 => a
  | (j + 1) => AseqG Φ a j

/-- The universal function expressing the time derivative `∂ₜ^j (Φ(·,J u))` through the spatial
`2`-jets of `u, A₀, …, A_{j-1}`. -/
noncomputable def PsiG (Φ : E × JG E F → F) :
    (j : ℕ) → E × (Fin (j + 1) → JG E F) → F
  | 0 => fun p => Φ (p.1, p.2 0)
  | (j + 1) => fun p =>
      ∑ i : Fin (j + 1),
        (fderiv ℝ (fun q : E × (Fin (j + 1) → JG E F) => PsiG Φ j q)
          (p.1, fun k => p.2 k.castSucc)) (0, Pi.single i (p.2 i.succ))

theorem AseqG_zero (Φ : E × JG E F → F) (a : ℝ × E → F) :
    AseqG Φ a 0 = fun z => Φ (z.2, sJetG a z) := rfl

theorem AseqG_succ (Φ : E × JG E F → F) (a : ℝ × E → F) (j : ℕ) :
    AseqG Φ a (j + 1) = tderivG (AseqG Φ a j) := rfl

theorem SeqG_zero (Φ : E × JG E F → F) (a : ℝ × E → F) : SeqG Φ a 0 = a := rfl

theorem SeqG_succ (Φ : E × JG E F → F) (a : ℝ × E → F) (j : ℕ) :
    SeqG Φ a (j + 1) = AseqG Φ a j := rfl

theorem PsiG_zero (Φ : E × JG E F → F) (p : E × (Fin 1 → JG E F)) :
    PsiG Φ 0 p = Φ (p.1, p.2 0) := rfl

theorem PsiG_succ (Φ : E × JG E F → F) (j : ℕ) (p : E × (Fin (j + 2) → JG E F)) :
    PsiG Φ (j + 1) p = ∑ i : Fin (j + 1),
      (fderiv ℝ (fun q : E × (Fin (j + 1) → JG E F) => PsiG Φ j q)
        (p.1, fun k => p.2 k.castSucc)) (0, Pi.single i (p.2 i.succ)) := rfl

end Work.Diff.EXT
