import Mathlib
import Submission.Work.ThomBordism.Transversality.Sard.Strat
import Submission.Work.ThomBordism.Transversality.Sard.isCriticalPoint_comp
import Submission.Work.ThomBordism.Transversality.Sard.exists_levelSet_param_smooth
import Submission.Work.ThomBordism.Transversality.Sard.volume_image_null_of_local

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The image of a critical set lying in a regular level set is null

Let `σ : ℝ^{n+1} → ℝ` be `C^∞` on an open set `V`, with `fderiv ℝ σ x ≠ 0` at every point of a set
`S ⊆ V ∩ {σ = 0}`, and let `f : ℝ^{n+1} → ℝ^m` be `C^∞` on `V` with `S` consisting of critical
points of `f`.  Then `f '' S` is Lebesgue-null.

This is the **"vanishing stratum" step** of Sard's theorem: `S` lies in the smooth hypersurface
`{σ = 0}`, and the restriction of `f` to that hypersurface is a map on an `n`-dimensional space
which is still critical on `S` (the image of the derivative of the restriction is contained in the
image of `d f`, which is proper).  So the statement follows from Sard's theorem for maps
`ℝⁿ → ℝ^m`, which is the induction hypothesis `SardEuclidOn n m`.

The proof is local: around each `x ∈ S` the level set `{σ = 0}` is parametrized by a `C^∞` map `γ`
of an open subset of `ℝⁿ` (`Sard.exists_levelSet_param_smooth`, proved via the implicit function
theorem for `(σ, projection)` and the smooth inverse function theorem on an open set,
`Sard.contDiffOn_symm_of_contDiffOn`); the critical points of `f ∘ γ` then contain the parametrized
points of `S`, so the induction hypothesis applies, and a countable covering argument
(`Sard.volume_image_null_of_local`) globalizes.

(For the same statement for *analytic* data, see `Sard.exists_levelSet_param`, which is stated with
the analytic height `ω` made explicit.)
-/

open scoped ContDiff MeasureTheory
open MeasureTheory Set

namespace Work.ThomBordism.Transversality.Sard

open Work.ThomBordism.Transversality (CInfOn IsCriticalPoint SardEuclidOn)

noncomputable section

set_option maxHeartbeats 800000

theorem levelSet_null {n m : ℕ}
    (hIH : Work.ThomBordism.Transversality.SardEuclidOn n m)
    {V : Set (EuclideanSpace ℝ (Fin (n+1)))} (hV : IsOpen V)
    {f : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin m)}
    (hf : Work.ThomBordism.Transversality.CInfOn f V)
    {σ : EuclideanSpace ℝ (Fin (n+1)) → ℝ}
    (hσ : Work.ThomBordism.Transversality.CInfOn σ V)
    {S : Set (EuclideanSpace ℝ (Fin (n+1)))} (hSV : S ⊆ V)
    (hSσ : S ⊆ {x | σ x = 0})
    (hσ' : ∀ x ∈ S, fderiv ℝ σ x ≠ 0)
    (hcrit : ∀ x ∈ S, Work.ThomBordism.Transversality.IsCriticalPoint f x) :
    MeasureTheory.volume (f '' S) = 0 := by
  classical
  -- the height of `CInfOn` is `≥ ∞` (in this workspace it *is* `∞`), so smoothness follows
  have hle : (∞ : ℕ∞ω) ≤ smoothHeight := by simp [smoothHeight]
  have hσ_at : ∀ y ∈ V, ContDiffAt ℝ ∞ σ y := fun y hy =>
    (hσ.contDiffAt (hV.mem_nhds hy)).of_le hle
  have hf_at : ∀ y ∈ V, ContDiffAt ℝ ∞ f y := fun y hy =>
    (hf.contDiffAt (hV.mem_nhds hy)).of_le hle
  refine volume_image_null_of_local fun x hxS => ?_
  obtain ⟨N, W, γ, hNopen, hxN, hNV, hWopen, h0W, hγ0, hγsm, hγN, hσγ, hcover⟩ :=
    exists_levelSet_param_smooth hV hσ_at (hSV hxS) (hSσ hxS) (hσ' x hxS)
  refine ⟨N, hNopen, hxN, ?_⟩
  have hγV : ∀ u ∈ W, γ u ∈ V := fun u hu => hNV (hγN u hu)
  have hcomp_sm : ContDiffOn ℝ ∞ (fun u => f (γ u)) W := by
    rw [hWopen.contDiffOn_iff]
    intro u hu
    exact (hf_at (γ u) (hγV u hu)).comp u (hγsm.contDiffAt (hWopen.mem_nhds hu))
  have hsub : f '' (S ∩ N) ⊆
      (fun u => f (γ u)) '' ({u | IsCriticalPoint (fun u => f (γ u)) u} ∩ W) := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨hzS, hzN⟩ := hz
    obtain ⟨u, huW, huz⟩ := hcover z hzN (hSσ hzS)
    subst huz
    exact ⟨u, ⟨isCriticalPoint_comp
        ((hf_at (γ u) (hSV hzS)).differentiableAt (by simp))
        ((hγsm.contDiffAt (hWopen.mem_nhds huW)).differentiableAt (by simp))
        (hcrit (γ u) hzS), huW⟩, rfl⟩
  exact measure_mono_null hsub (hIH (fun u => f (γ u)) W hWopen hcomp_sm)

end

end Work.ThomBordism.Transversality.Sard
