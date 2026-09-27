import Mathlib
import Submission.Work.Drive.N2C.defs

/-!
# `N2C` A3: reversing the parametrisation of a level

Given `L : LevelCurves f b n`, the reversal `γ i x ↦ γ i (-x)` is again a
`LevelCurves f b n` (with the *same* index set `Fin n` and the same curves as images).

The rows `val`, `per`, `cover`, `disj` are immediate (`-x` ranges over `ℝ`, and `γ i`
is `1`-periodic).  The two real rows are:

* `injIco` / `modOne` — read off from `L.modOne` at the points `-x`, `-y`: if
  `γ i (-x) = γ i (-y)` then `-x = -y + k` for some `k : ℤ`, and for `x, y ∈ Ico 0 1`
  this forces `k = 0`, i.e. `x = y`;
* `ker` — the chain rule: `mfderiv (fun s => γ i (-s)) x = mfderiv (γ i) (-x) ∘SL (-1)`,
  so a kernel vector `v` of `f` at `γ i (-x)`, which is `mfderiv (γ i) (-x) t` for some `t`,
  is `mfderiv (fun s => γ i (-s)) x (-t)`.

The `mfderiv` computations are delicate because `TangentSpace 𝓘(ℝ,ℝ) x` is a *non-reducible*
type synonym for `ℝ` with its own instances; we therefore work with the transparency option
Mathlib itself uses for such lemmas (`mfderivWithin_neg`).
-/

namespace Work.Drive.N2C

open scoped Manifold ContDiff Topology
open Set

/-- The image of a reversed parametrisation is the image of the original one. -/
theorem range_neg_comp {X : Type*} (g : ℝ → X) :
    Set.range (fun x : ℝ => g (-x)) = Set.range g := by
  ext z; constructor <;> rintro ⟨x, rfl⟩ <;> exact ⟨-x, by simp⟩

set_option backward.isDefEq.respectTransparency false in
theorem levelCurves_reverse {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) ((⊤ : ENat) : WithTop ENat) M]
    {f : M → ℝ} {b : ℝ} {n : ℕ} (L : Work.Drive.N2C.LevelCurves f b n) :
    ∃ L' : Work.Drive.N2C.LevelCurves f b n,
      ∀ (i : Fin n) (x : ℝ), L'.γ i x = L.γ i (-x) := by
  refine ⟨{ γ := fun i x => L.γ i (-x)
            sm := ?_
            val := ?_
            per := ?_
            injIco := ?_
            modOne := ?_
            cover := ?_
            disj := ?_
            ker := ?_ }, ?_⟩
  · intro i
    exact (L.sm i).comp contDiff_neg.contMDiff
  · intro i x
    exact L.val i (-x)
  · intro i x
    have h := L.per i (-(x + 1))
    rw [show -(x + 1) + 1 = -x by ring] at h
    exact h.symm
  · intro i x hx y hy hxy
    obtain ⟨k, hk⟩ := L.modOne i (-x) (-y) hxy
    have hk' : (k : ℝ) = y - x := by linarith
    have hlt : (k : ℝ) < 1 := by linarith [hx.1, hy.2, hk']
    have hgt : (-1 : ℝ) < (k : ℝ) := by linarith [hy.1, hx.2, hk']
    have hk1 : (-1 : ℤ) < k := by exact_mod_cast hgt
    have hk2 : k < (1 : ℤ) := by exact_mod_cast hlt
    have hk0 : k = 0 := by omega
    have : y - x = 0 := by rw [← hk', hk0]; norm_num
    linarith
  · intro i x y h
    obtain ⟨k, hk⟩ := L.modOne i (-x) (-y) h
    exact ⟨-k, by push_cast; linarith⟩
  · intro x hx
    obtain ⟨i, t, ht⟩ := L.cover x hx
    exact ⟨i, -t, by simpa using ht⟩
  · intro i j hij
    simp only [range_neg_comp]
    exact L.disj i j hij
  · intro i x v hv
    obtain ⟨t, ht⟩ := L.ker i (-x) v hv
    refine ⟨-t, ?_⟩
    -- the derivative of the reversal, via the chain rule with `x ↦ -x`
    have hneg : HasMFDerivAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun s : ℝ => -s) x
        (- ContinuousLinearMap.id ℝ ℝ) := by
      have h' := ContinuousLinearMap.hasMFDerivAt (𝕜 := ℝ) (E := ℝ) (E' := ℝ)
        (f := - ContinuousLinearMap.id ℝ ℝ) (x := x)
      have hfun : (⇑(- ContinuousLinearMap.id ℝ ℝ) : ℝ → ℝ) = fun s => -s := by
        funext s; simp
      rwa [hfun] at h'
    have hmd1 : MDifferentiableAt 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun s : ℝ => -s) x :=
      hneg.mdifferentiableAt
    have hmd2 : MDifferentiableAt 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) (-x) :=
      (L.sm i).contMDiffAt.mdifferentiableAt (by simp)
    have happ : (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (fun s : ℝ => L.γ i (-s)) x) (-t)
        = (mfderiv 𝓘(ℝ,ℝ) (𝓡 2) (L.γ i) (-x))
            ((mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun s : ℝ => -s) x) (-t)) := by
      have h := mfderiv_comp_apply (x := x) (f := fun s : ℝ => -s) (g := L.γ i) hmd2 hmd1 (-t)
      exact h
    rw [happ]
    have harg : (mfderiv 𝓘(ℝ,ℝ) 𝓘(ℝ,ℝ) (fun s : ℝ => -s) x) (-t)
        = (t : TangentSpace 𝓘(ℝ,ℝ) (-x)) := by
      rw [hneg.mfderiv]
      change (- ContinuousLinearMap.id ℝ ℝ) (-t : ℝ) = (t : ℝ)
      simp
    rw [harg]
    exact ht
  · intro i x
    rfl

end Work.Drive.N2C
