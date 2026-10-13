import Mathlib
import Submission.Work.CoreStep.StratReindexDefs
import Submission.Work.CoreStep.stratReindex_jac

namespace Work.WilE7.coreLT_succ

theorem finrank_map_reindex {N N' : ℕ} (e : Fin (0 + N) ≃ Fin (0 + N'))
    (S : WilkiesDesign.E.Stratum 0 N) (y : Fin (0 + N') → ℝ) {k : ℕ}
    (M : (Fin (0 + N') → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    (M' : (Fin (0 + N) → ℝ) →ₗ[ℝ] (Fin k → ℝ))
    (hM : ∀ v : Fin (0 + N) → ℝ, M (fun j : Fin (0 + N') => v (e.symm j)) = M' v) :
    Module.finrank ℝ ((LinearMap.ker (Work.WilE7.MainDesign.jac
        (Work.CoreStep.Stratum.reindex e S) y)).map M)
      = Module.finrank ℝ ((LinearMap.ker (Work.WilE7.MainDesign.jac S
          (fun i : Fin (0 + N) => y (e i)))).map M') := by
  -- the coordinate equivalence, as a linear equivalence `L : v ↦ v ∘ e.symm`
  let L : (Fin (0 + N) → ℝ) ≃ₗ[ℝ] (Fin (0 + N') → ℝ) := LinearEquiv.funCongrLeft ℝ ℝ e.symm
  have hLapp : ∀ v : Fin (0 + N) → ℝ, L v = (fun j : Fin (0 + N') => v (e.symm j)) :=
    fun v => rfl
  -- the Jacobian of the reindexed stratum is the Jacobian of `S` precomposed with `L`
  have hjac : ∀ v : Fin (0 + N) → ℝ,
      Work.WilE7.MainDesign.jac (Work.CoreStep.Stratum.reindex e S) y (L v)
        = Work.WilE7.MainDesign.jac S (fun i : Fin (0 + N) => y (e i)) v := by
    intro v
    rw [hLapp v]
    exact Work.CoreStep.stratReindex_jac e S y v
  -- the tangent space of the reindexed stratum is the image under `L` of the tangent space of `S`
  have hker : (LinearMap.ker (Work.WilE7.MainDesign.jac S
        (fun i : Fin (0 + N) => y (e i)))).map L.toLinearMap
      = LinearMap.ker (Work.WilE7.MainDesign.jac (Work.CoreStep.Stratum.reindex e S) y) := by
    ext w
    rw [Submodule.mem_map]
    constructor
    · rintro ⟨v, hv, rfl⟩
      have hv' : (Work.WilE7.MainDesign.jac S (fun i : Fin (0 + N) => y (e i))) v = 0 := hv
      change (Work.WilE7.MainDesign.jac (Work.CoreStep.Stratum.reindex e S) y) (L v) = 0
      rw [hjac v]
      exact hv'
    · intro hw
      have hw' : (Work.WilE7.MainDesign.jac (Work.CoreStep.Stratum.reindex e S) y) w = 0 := hw
      refine ⟨L.symm w, ?_, ?_⟩
      · change (Work.WilE7.MainDesign.jac S (fun i : Fin (0 + N) => y (e i))) (L.symm w) = 0
        rw [← hjac (L.symm w), LinearEquiv.apply_symm_apply]
        exact hw'
      · simp
  -- ... hence the two images under `M` and `M'` coincide
  have hmain : (LinearMap.ker (Work.WilE7.MainDesign.jac
        (Work.CoreStep.Stratum.reindex e S) y)).map M
      = (LinearMap.ker (Work.WilE7.MainDesign.jac S
          (fun i : Fin (0 + N) => y (e i)))).map M' := by
    rw [← hker]
    ext w
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨v, hv, rfl⟩ := hx
      exact ⟨v, hv, (hM v).symm⟩
    · rintro ⟨v, hv, rfl⟩
      exact ⟨L v, ⟨v, hv, rfl⟩, hM v⟩
  rw [hmain]

end Work.WilE7.coreLT_succ
