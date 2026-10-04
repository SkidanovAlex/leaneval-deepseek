import Mathlib
import Submission.Work.Diff.STE.D.ODE
import Submission.Work.Diff.STE.D.Galerkin
import Submission.Work.Diff.STE.B3.Data

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead

theorem galState_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀) (ε τ C : ℝ) (hC : 0 ≤ C)
    (c : ℝ → (Work.Diff.STE.B3.JIdx ι₀ (Module.finrank ℝ E) ε → ℝ))
    (hder : ∀ t ∈ Set.Icc (0 : ℝ) τ, ∀ (x : M) (u v : TangentSpace I x),
      ∃ Dv : ℝ, HasDerivWithinAt (fun s : ℝ =>
          Work.Diff.STE.D.addSec (I := I) g₀
            (Work.Diff.STE.D.genMap (I := I) (M := M) D ε (c s)) x u v)
          Dv (Set.Icc (0 : ℝ) τ) t ∧
        |Dv| ≤ C * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v)) :
    ∀ t ∈ Set.Icc (0 : ℝ) τ, ∀ t' ∈ Set.Icc (0 : ℝ) τ, ∀ (x : M) (u v : TangentSpace I x),
      |Work.Diff.STE.D.addSec (I := I) g₀
          (Work.Diff.STE.D.genMap (I := I) (M := M) D ε (c t)) x u v
        - Work.Diff.STE.D.addSec (I := I) g₀
          (Work.Diff.STE.D.genMap (I := I) (M := M) D ε (c t')) x u v|
      ≤ C * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) * |t - t'| := by
  intro t ht t' ht' x u v
  classical
  -- The function whose Lipschitz constant we are bounding, and a choice of its (within-`Icc`)
  -- derivative on `Icc 0 τ`.
  let F : ℝ → ℝ := fun s => Work.Diff.STE.D.addSec (I := I) g₀
        (Work.Diff.STE.D.genMap (I := I) (M := M) D ε (c s)) x u v
  let F' : ℝ → ℝ := fun s =>
    if hs : s ∈ Set.Icc (0 : ℝ) τ then Classical.choose (hder s hs x u v) else 0
  have hF : ∀ s ∈ Set.Icc (0 : ℝ) τ, HasDerivWithinAt F (F' s) (Set.Icc (0 : ℝ) τ) s := by
    intro s hs
    have hs' : F' s = Classical.choose (hder s hs x u v) := by
      simp only [F', dif_pos hs]
    rw [hs']
    exact (Classical.choose_spec (hder s hs x u v)).1
  have hF' : ∀ s ∈ Set.Icc (0 : ℝ) τ,
      ‖F' s‖ ≤ C * Real.sqrt (g₀.inner x u u) * Real.sqrt (g₀.inner x v v) := by
    intro s hs
    have hs' : F' s = Classical.choose (hder s hs x u v) := by
      simp only [F', dif_pos hs]
    rw [hs', Real.norm_eq_abs]
    exact (Classical.choose_spec (hder s hs x u v)).2
  -- Mean value inequality on the convex set `Icc 0 τ`.
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) hF hF'
    (convex_Icc (0 : ℝ) τ) ht' ht
  simpa [F, Real.norm_eq_abs] using hmain

end Work.Diff.STE.Lead
