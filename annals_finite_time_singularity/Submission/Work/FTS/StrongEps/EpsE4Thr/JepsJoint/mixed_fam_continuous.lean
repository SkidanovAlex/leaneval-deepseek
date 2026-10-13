/-
Copyright: work module for the Elgindi finite-time singularity project.

# Continuity of the mixed derivatives of a jointly smooth family of profiles

This file proves `Work.FTS.StrongEps.EpsE4Thr.JepsJoint.mixed_fam_continuous`: if

  `Φ (t, (z,θ)) = g z θ t`   is `C^n` for every `n` on the open set `(0,T) × Quad`,

then for all `j i : ℕ` the function

  `q ↦ D_z^j D_θ^i (fun z θ => g z θ q.1) q.2.1 q.2.2`

is continuous on `(0,T) × Quad`.  In other words, the mixed jets of the family depend
continuously on the family parameter.

## The method

The mixed operator `D_z^j D_θ^i` is a differential operator *with smooth coefficients* in the
two variables `(z,θ)`, so its value on the slice `z ↦ Φ (t, (z,θ))` at `(z,θ)` is again the
value at `(t,z,θ)` of a smooth function of the three variables.  Rather than expand `mixed` into
partial derivatives (which would be a combinatorial mess), we transport the *operators*
themselves to the product `ℝ × (ℝ × ℝ)`:

* `pzJ Φ q = ∂_z (fun z' => Φ (q.1, (z', q.2.2))) q.2.1`,
* `pthJ Φ q = ∂_θ (fun θ' => Φ (q.1, (q.2.1, θ'))) q.2.2`,
* `DzJ Φ q = q.2.1 * pzJ Φ q`,  `DthJ Φ q = sin (2 * q.2.2) * pthJ Φ q`,

and their iterates `DzIterJ`, `DthIterJ`, `mixedJ`.  Each of `pzJ`, `pthJ` is — by the chain
rule — the evaluation of the Fréchet derivative `fderiv ℝ Φ q` on a fixed direction, hence
*lowering the differentiability order by one* (`contDiffOn_pzJ`, `contDiffOn_pthJ`); multiplying
by the smooth coefficient `q.2.1` resp. `sin (2 * q.2.2)` gives `contDiffOn_DzJ`,
`contDiffOn_DthJ`, and induction gives `contDiffOn_mixedJ`:

  `ContDiffOn ℝ (n + j + i) Φ V  →  ContDiffOn ℝ n (mixedJ j i Φ) V`  for `V` open.

The remaining point is that `mixedJ` *is* `mixed` applied to the slices
(`mixedJ_apply`), which is proved by induction on `j` and `i` from the definitional identity
`pzJ Φ (t,(z,θ)) = pz (fun z θ => Φ (t,(z,θ))) z θ` (and its `θ`-analogue).

The hypothesis `hg` of the statement is already stated in the uncurried form
`q ↦ g q.2.1 q.2.2 q.1` on `(0,T) × Quad`, which is exactly the `Φ` above.
-/
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.JepsJoint

/-! ## The joint derivative operators on `ℝ × (ℝ × ℝ)` -/

/-- The `z`-partial derivative of the slice `z ↦ Φ (t, (z, θ))`, at the point `q = (t, (z, θ))`. -/
def pzJ (Φ : ℝ × (ℝ × ℝ) → ℝ) (q : ℝ × (ℝ × ℝ)) : ℝ :=
  deriv (fun z' => Φ (q.1, (z', q.2.2))) q.2.1

/-- The `θ`-partial derivative of the slice `θ ↦ Φ (t, (z, θ))`, at the point `q = (t, (z, θ))`. -/
def pthJ (Φ : ℝ × (ℝ × ℝ) → ℝ) (q : ℝ × (ℝ × ℝ)) : ℝ :=
  deriv (fun θ' => Φ (q.1, (q.2.1, θ'))) q.2.2

/-- The joint `D_z`-operator: `z · ∂_z` on the slice. -/
def DzJ (Φ : ℝ × (ℝ × ℝ) → ℝ) (q : ℝ × (ℝ × ℝ)) : ℝ := q.2.1 * pzJ Φ q

/-- The joint `D_θ`-operator: `sin (2θ) · ∂_θ` on the slice. -/
def DthJ (Φ : ℝ × (ℝ × ℝ) → ℝ) (q : ℝ × (ℝ × ℝ)) : ℝ :=
  Real.sin (2 * q.2.2) * pthJ Φ q

/-- Iterated joint `D_z`. -/
def DzIterJ : ℕ → (ℝ × (ℝ × ℝ) → ℝ) → (ℝ × (ℝ × ℝ) → ℝ)
  | 0, Φ => Φ
  | n + 1, Φ => DzJ (DzIterJ n Φ)

/-- Iterated joint `D_θ`. -/
def DthIterJ : ℕ → (ℝ × (ℝ × ℝ) → ℝ) → (ℝ × (ℝ × ℝ) → ℝ)
  | 0, Φ => Φ
  | n + 1, Φ => DthJ (DthIterJ n Φ)

/-- The joint mixed operator `D_z^j D_θ^i` applied to the family `Φ`. -/
def mixedJ (j i : ℕ) (Φ : ℝ × (ℝ × ℝ) → ℝ) : ℝ × (ℝ × ℝ) → ℝ :=
  DzIterJ j (DthIterJ i Φ)

@[simp] theorem DzIterJ_zero (Φ : ℝ × (ℝ × ℝ) → ℝ) : DzIterJ 0 Φ = Φ := rfl

@[simp] theorem DzIterJ_succ (n : ℕ) (Φ : ℝ × (ℝ × ℝ) → ℝ) :
    DzIterJ (n + 1) Φ = DzJ (DzIterJ n Φ) := rfl

@[simp] theorem DthIterJ_zero (Φ : ℝ × (ℝ × ℝ) → ℝ) : DthIterJ 0 Φ = Φ := rfl

@[simp] theorem DthIterJ_succ (n : ℕ) (Φ : ℝ × (ℝ × ℝ) → ℝ) :
    DthIterJ (n + 1) Φ = DthJ (DthIterJ n Φ) := rfl

/-! ## `pzJ`, `pthJ` are Fréchet derivatives in fixed directions -/

/-- The joint `z`-partial derivative is the Fréchet derivative in the direction `(0, (1, 0))`. -/
theorem pzJ_eq_fderiv {Φ : ℝ × (ℝ × ℝ) → ℝ} {q : ℝ × (ℝ × ℝ)}
    (h : DifferentiableAt ℝ Φ q) : pzJ Φ q = fderiv ℝ Φ q (0, (1, 0)) := by
  have hcurve : HasDerivAt (fun z' : ℝ => (q.1, (z', q.2.2))) (0, (1, 0)) q.2.1 := by
    simpa using (hasDerivAt_const (x := q.2.1) q.1).prodMk
      ((hasDerivAt_id q.2.1).prodMk (hasDerivAt_const (x := q.2.1) q.2.2))
  exact (h.hasFDerivAt.comp_hasDerivAt q.2.1 hcurve).deriv

/-- The joint `θ`-partial derivative is the Fréchet derivative in the direction `(0, (0, 1))`. -/
theorem pthJ_eq_fderiv {Φ : ℝ × (ℝ × ℝ) → ℝ} {q : ℝ × (ℝ × ℝ)}
    (h : DifferentiableAt ℝ Φ q) : pthJ Φ q = fderiv ℝ Φ q (0, (0, 1)) := by
  have hcurve : HasDerivAt (fun θ' : ℝ => (q.1, (q.2.1, θ'))) (0, (0, 1)) q.2.2 := by
    simpa using (hasDerivAt_const (x := q.2.2) q.1).prodMk
      ((hasDerivAt_const (x := q.2.2) q.2.1).prodMk (hasDerivAt_id q.2.2))
  exact (h.hasFDerivAt.comp_hasDerivAt q.2.2 hcurve).deriv

/-! ## The operators lower the differentiability order by one -/

/-- `∂_z` lowers the differentiability order by one on an open set. -/
theorem contDiffOn_pzJ {Φ : ℝ × (ℝ × ℝ) → ℝ} {n : ℕ} {V : Set (ℝ × (ℝ × ℝ))}
    (hV : IsOpen V) (h : ContDiffOn ℝ (n + 1) Φ V) : ContDiffOn ℝ n (pzJ Φ) V := by
  have hchain : ∀ q ∈ V, pzJ Φ q = fderiv ℝ Φ q (0, (1, 0)) := fun q hq =>
    pzJ_eq_fderiv
      ((h.differentiableOn (by norm_num : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ 0)).differentiableAt
        (hV.mem_nhds hq))
  have hfd : ContDiffOn ℝ n (fun q : ℝ × (ℝ × ℝ) => fderiv ℝ Φ q) V :=
    h.fderiv_of_isOpen hV (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n (fun q : ℝ × (ℝ × ℝ) => (fderiv ℝ Φ q) (0, (1, 0))) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- `∂_θ` lowers the differentiability order by one on an open set. -/
theorem contDiffOn_pthJ {Φ : ℝ × (ℝ × ℝ) → ℝ} {n : ℕ} {V : Set (ℝ × (ℝ × ℝ))}
    (hV : IsOpen V) (h : ContDiffOn ℝ (n + 1) Φ V) : ContDiffOn ℝ n (pthJ Φ) V := by
  have hchain : ∀ q ∈ V, pthJ Φ q = fderiv ℝ Φ q (0, (0, 1)) := fun q hq =>
    pthJ_eq_fderiv
      ((h.differentiableOn (by norm_num : ((n + 1 : ℕ) : WithTop ℕ∞) ≠ 0)).differentiableAt
        (hV.mem_nhds hq))
  have hfd : ContDiffOn ℝ n (fun q : ℝ × (ℝ × ℝ) => fderiv ℝ Φ q) V :=
    h.fderiv_of_isOpen hV (m := n) (by norm_num)
  have hcomp : ContDiffOn ℝ n (fun q : ℝ × (ℝ × ℝ) => (fderiv ℝ Φ q) (0, (0, 1))) V :=
    hfd.clm_apply contDiffOn_const
  exact hcomp.congr hchain

/-- `D_z` lowers the differentiability order by one on an open set. -/
theorem contDiffOn_DzJ {Φ : ℝ × (ℝ × ℝ) → ℝ} {n : ℕ} {V : Set (ℝ × (ℝ × ℝ))}
    (hV : IsOpen V) (h : ContDiffOn ℝ (n + 1) Φ V) : ContDiffOn ℝ n (DzJ Φ) V := by
  have hpz := contDiffOn_pzJ hV h
  have h1 : ContDiffOn ℝ n (fun q : ℝ × (ℝ × ℝ) => q.2.1) V := (contDiff_snd.fst).contDiffOn
  exact h1.mul hpz

/-- `D_θ` lowers the differentiability order by one on an open set. -/
theorem contDiffOn_DthJ {Φ : ℝ × (ℝ × ℝ) → ℝ} {n : ℕ} {V : Set (ℝ × (ℝ × ℝ))}
    (hV : IsOpen V) (h : ContDiffOn ℝ (n + 1) Φ V) : ContDiffOn ℝ n (DthJ Φ) V := by
  have hpth := contDiffOn_pthJ hV h
  have hsin : ContDiffOn ℝ n (fun q : ℝ × (ℝ × ℝ) => Real.sin (2 * q.2.2)) V := by
    have h2 : ContDiff ℝ n (fun q : ℝ × (ℝ × ℝ) => (2 : ℝ) * q.2.2) :=
      contDiff_const.mul (contDiff_snd.snd : ContDiff ℝ n (fun q : ℝ × (ℝ × ℝ) => q.2.2))
    exact (Real.contDiff_sin.comp h2).contDiffOn
  exact hsin.mul hpth

/-- The iterated `D_z^j` lowers the differentiability order by `j` on an open set. -/
theorem contDiffOn_DzIterJ {n : ℕ} {Φ : ℝ × (ℝ × ℝ) → ℝ} {V : Set (ℝ × (ℝ × ℝ))}
    (hV : IsOpen V) : ∀ j : ℕ, ContDiffOn ℝ (n + j) Φ V → ContDiffOn ℝ n (DzIterJ j Φ) V := by
  intro j
  induction j generalizing n with
  | zero => intro h; simpa using h
  | succ j ih =>
      intro h
      rw [DzIterJ_succ]
      exact contDiffOn_DzJ hV (ih (n := n + 1)
        (h.of_le (Nat.cast_le.mpr (by omega : n + 1 + j ≤ n + (j + 1)))))

/-- The iterated `D_θ^i` lowers the differentiability order by `i` on an open set. -/
theorem contDiffOn_DthIterJ {n : ℕ} {Φ : ℝ × (ℝ × ℝ) → ℝ} {V : Set (ℝ × (ℝ × ℝ))}
    (hV : IsOpen V) : ∀ i : ℕ, ContDiffOn ℝ (n + i) Φ V → ContDiffOn ℝ n (DthIterJ i Φ) V := by
  intro i
  induction i generalizing n with
  | zero => intro h; simpa using h
  | succ i ih =>
      intro h
      rw [DthIterJ_succ]
      exact contDiffOn_DthJ hV (ih (n := n + 1)
        (h.of_le (Nat.cast_le.mpr (by omega : n + 1 + i ≤ n + (i + 1)))))

/-- The joint mixed operator `D_z^j D_θ^i` lowers the differentiability order by `j + i`. -/
theorem contDiffOn_mixedJ {n j i : ℕ} {Φ : ℝ × (ℝ × ℝ) → ℝ} {V : Set (ℝ × (ℝ × ℝ))}
    (hV : IsOpen V) (h : ContDiffOn ℝ (n + j + i) Φ V) : ContDiffOn ℝ n (mixedJ j i Φ) V := by
  have h1 : ContDiffOn ℝ (n + j) (DthIterJ i Φ) V := contDiffOn_DthIterJ hV i h
  exact contDiffOn_DzIterJ hV j h1

/-! ## The joint operators are the ordinary ones on the slices -/

/-- `pzJ` is the ordinary `pz` of the slice. -/
theorem pzJ_apply (Φ : ℝ × (ℝ × ℝ) → ℝ) (q : ℝ × (ℝ × ℝ)) :
    pzJ Φ q = Work.Spaces.pz (fun z θ => Φ (q.1, (z, θ))) q.2.1 q.2.2 := rfl

/-- `pthJ` is the ordinary `pth` of the slice. -/
theorem pthJ_apply (Φ : ℝ × (ℝ × ℝ) → ℝ) (q : ℝ × (ℝ × ℝ)) :
    pthJ Φ q = Work.Spaces.pth (fun z θ => Φ (q.1, (z, θ))) q.2.1 q.2.2 := rfl

/-- `DzIterJ j` is the ordinary `DzIter j` of the slice. -/
theorem DzIterJ_apply (j : ℕ) (Φ : ℝ × (ℝ × ℝ) → ℝ) :
    ∀ q : ℝ × (ℝ × ℝ), DzIterJ j Φ q
      = Work.Spaces.DzIter j (fun z θ => Φ (q.1, (z, θ))) q.2.1 q.2.2 := by
  induction j with
  | zero => intro q; rfl
  | succ j ih =>
      intro q
      rw [DzIterJ_succ]
      show q.2.1 * pzJ (DzIterJ j Φ) q
        = q.2.1 * Work.Spaces.pz (Work.Spaces.DzIter j (fun z θ => Φ (q.1, (z, θ))))
            q.2.1 q.2.2
      rw [pzJ_apply]
      have hf : (fun z θ => DzIterJ j Φ (q.1, (z, θ)))
          = fun z θ => Work.Spaces.DzIter j (fun z θ => Φ (q.1, (z, θ))) z θ := by
        funext z θ; exact ih (q.1, (z, θ))
      rw [hf]

/-- `DthIterJ i` is the ordinary `DthIter i` of the slice. -/
theorem DthIterJ_apply (i : ℕ) (Φ : ℝ × (ℝ × ℝ) → ℝ) :
    ∀ q : ℝ × (ℝ × ℝ), DthIterJ i Φ q
      = Work.Spaces.DthIter i (fun z θ => Φ (q.1, (z, θ))) q.2.1 q.2.2 := by
  induction i with
  | zero => intro q; rfl
  | succ i ih =>
      intro q
      rw [DthIterJ_succ]
      show Real.sin (2 * q.2.2) * pthJ (DthIterJ i Φ) q
        = Real.sin (2 * q.2.2) * Work.Spaces.pth
            (Work.Spaces.DthIter i (fun z θ => Φ (q.1, (z, θ)))) q.2.1 q.2.2
      rw [pthJ_apply]
      have hf : (fun z θ => DthIterJ i Φ (q.1, (z, θ)))
          = fun z θ => Work.Spaces.DthIter i (fun z θ => Φ (q.1, (z, θ))) z θ := by
        funext z θ; exact ih (q.1, (z, θ))
      rw [hf]

/-- **`mixedJ` is the ordinary `mixed` of the slice.** -/
theorem mixedJ_apply (j i : ℕ) (Φ : ℝ × (ℝ × ℝ) → ℝ) :
    ∀ q : ℝ × (ℝ × ℝ), mixedJ j i Φ q
      = Work.Spaces.mixed j i (fun z θ => Φ (q.1, (z, θ))) q.2.1 q.2.2 := by
  intro q
  show DzIterJ j (DthIterJ i Φ) q = _
  rw [DzIterJ_apply j (DthIterJ i Φ) q]
  have hf : (fun z θ => DthIterJ i Φ (q.1, (z, θ)))
      = fun z θ => Work.Spaces.DthIter i (fun z θ => Φ (q.1, (z, θ))) z θ := by
    funext z θ; exact DthIterJ_apply i Φ (q.1, (z, θ))
  rw [hf]
  have heta : (fun z θ => Work.Spaces.DthIter i (fun z θ => Φ (q.1, (z, θ))) z θ)
      = Work.Spaces.DthIter i (fun z θ => Φ (q.1, (z, θ))) := by
    funext z θ; rfl
  rw [heta]
  rfl

/-! ## The main statement -/

theorem mixed_fam_continuous {g : ℝ → ℝ → ℝ → ℝ} {T : ℝ} {j i : ℕ}
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (fun q : ℝ × (ℝ × ℝ) => g q.2.1 q.2.2 q.1)
      (Set.Ioo (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad)) :
    ContinuousOn (fun q : ℝ × (ℝ × ℝ) =>
      Work.Spaces.mixed j i (fun z θ => g z θ q.1) q.2.1 q.2.2)
      (Set.Ioo (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) := by
  have hV : IsOpen (Set.Ioo (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) := by
    rw [Work.FTS.StrongEps.Quad]
    exact isOpen_Ioo.prod (isOpen_Ioi.prod isOpen_Ioo)
  have hcd : ContDiffOn ℝ 0 (mixedJ j i (fun q : ℝ × (ℝ × ℝ) => g q.2.1 q.2.2 q.1))
      (Set.Ioo (0 : ℝ) T ×ˢ Work.FTS.StrongEps.Quad) :=
    contDiffOn_mixedJ hV (hg (0 + j + i))
  refine hcd.continuousOn.congr (fun q hq => ?_)
  exact (mixedJ_apply j i (fun q : ℝ × (ℝ × ℝ) => g q.2.1 q.2.2 q.1) q).symm

end Work.FTS.StrongEps.EpsE4Thr.JepsJoint
