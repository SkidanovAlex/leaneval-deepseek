import Mathlib
import Submission.Work.Stems.Collar.Defs

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Releasing the collar

For a path `p : Path x y` in a space `X` and a finite nonempty index type `M`, the collar
construction `collar p : Ω^M X x → Ω^M X y` changes the basepoint of the based `M`-cubes of
`X` from `x` to `y` (see `Submission.Work.Stems.Collar.Defs`).

The present lemma records the effect of the collar on the *constant* loop.  Applied to
`GenLoop.const ∈ Ω^M X x`, the collar lands in `Ω^M X y` and is the loop that walks from the
boundary `y` inward along `p` towards `x` and is constant `x` on the inner cube.  The key point
is that this loop is *connected to the constant loop at `y` by an honest path in the loop
space* `Ω^M X y`: geometrically, one continuously "releases" the collar, pushing the whole
spike back out to the boundary value `y`.

Concretely, writing `δ t = delta t` for the distance of `t` to the boundary of the cube, the
homotopy is

`(s, t) ↦ p (clamp01 (1 - (1 - s) * (4 * δ t)))`.

At `s = 1` this is the collar of the constant loop, at `s = 0` it is constantly `y`, and on
the boundary of the cube (`δ t = 0`) it equals `p 1 = y` for every `s`, so every intermediate
slice is a genuine based `M`-cube in `Ω^M X y`.
-/

open scoped Topology unitInterval Topology.Homotopy
open Set Function

namespace Work.Stems.Collar

variable {M : Type*} [Fintype M] [Nonempty M]
variable {X : Type*} [TopologicalSpace X] {x y : X}

/-- On the constant loop the collar formula collapses to evaluating `p` at the clamped height
`1 - 4 δ`, because the "inner" branch of `collarFun` evaluates the constant loop to `x`, which
is also `p 0` (the clamp being `0` in the inner region). -/
lemma collar_const_apply (p : Path x y) (t : M → I) :
    collar p (GenLoop.const : Ω^ M X x) t = p (clamp01 (1 - 4 * delta t)) := by
  rw [collar_apply, collarFun]
  split_ifs with h
  · rfl
  · rw [GenLoop.const_apply, clamp01_eq_zero_iff.mpr (by linarith [not_le.mp h])]
    exact p.source.symm

/-- The uncurried "release" homotopy: at parameter `s` the height along `p` is
`1 - (1 - s) * (4 δ t)`, so that `s = 0` gives the constant map at `y` and `s = 1` gives the
collar of the constant loop. -/
noncomputable def collarReleaseFun (p : Path x y) (z : I × (M → I)) : X :=
  p (clamp01 (1 - (1 - (z.1 : ℝ)) * (4 * delta z.2)))

theorem continuous_collarReleaseFun (p : Path x y) :
    Continuous (collarReleaseFun (M := M) p) := by
  have hd : Continuous fun z : I × (M → I) => delta z.2 :=
    continuous_delta.comp continuous_snd
  have hs : Continuous fun z : I × (M → I) => (z.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hinner : Continuous fun z : I × (M → I) =>
      1 - (1 - (z.1 : ℝ)) * (4 * delta z.2) :=
    continuous_const.sub ((continuous_const.sub hs).mul (continuous_const.mul hd))
  exact p.continuous.comp (continuous_clamp01.comp hinner)

theorem collar_release {M : Type*} [Fintype M] [Nonempty M] {X : Type*} [TopologicalSpace X]
    {x y : X} (p : Path x y) :
    Nonempty (Path (Work.Stems.Collar.collar p GenLoop.const) (GenLoop.const : GenLoop M X y)) := by
  let hcurry : C(I, C(M → I, X)) :=
    ContinuousMap.curry ⟨collarReleaseFun (M := M) p, continuous_collarReleaseFun p⟩
  -- every slice of the homotopy is a based `M`-cube in `Ω^M X y`
  have hmem : ∀ s : I, hcurry s ∈ (GenLoop M X y : Set (C(M → I, X))) := by
    intro s t ht
    have hd : delta t = 0 := (delta_eq_zero_iff (M := M)).2 ht
    change collarReleaseFun (M := M) p (s, t) = y
    rw [collarReleaseFun, hd]
    simp only [mul_zero, sub_zero, clamp01_one]
    exact p.target
  refine ⟨Path.mk ⟨fun s => ⟨hcurry s, hmem s⟩,
    Continuous.subtype_mk hcurry.continuous hmem⟩ ?_ ?_⟩
  · -- at `s = 0` the family is the collar of `const`, at `s = 1` it is the constant loop
    apply GenLoop.ext; intro t
    rw [collar_const_apply]
    change collarReleaseFun (M := M) p (0, t) = p (clamp01 (1 - 4 * delta t))
    rw [collarReleaseFun]
    norm_num
  · apply GenLoop.ext; intro t
    change collarReleaseFun (M := M) p (1, t) = y
    rw [collarReleaseFun]
    norm_num

end Work.Stems.Collar
