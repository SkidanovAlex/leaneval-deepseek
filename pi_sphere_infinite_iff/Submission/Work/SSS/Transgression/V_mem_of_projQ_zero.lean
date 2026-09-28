import Mathlib
import Submission.Work.SSS.FibreColDefs
import Submission.Work.SSS.Transgression.vzQuotAux

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SSS.Transgression

/-- If a chain `x` of `F_{k+1}` in degree `t+1` whose boundary (in `C`) lies in `F_0` (i.e.
`x ∈ Wrel ξ (k+1) (t+1)`) has vanishing class in the graded piece `(F_{k+1}/F_k)_{t+1}`, then its
boundary lies in the `k`-th step `V_k = ∂(F_k C_{t+1}) ∩ Z_t(F_0)` of the left column.  This is the
well-definedness of the transgression `d_s : Z^s_{s,t+1} → V_s/V_{s-1}`, at a single step. -/
theorem V_mem_of_projQ_zero {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C)
    (t k : ℕ) (x : (ξ.F.obj (k + 1)).X (t + 1))
    (hx : x ∈ Wrel ξ (k + 1) (t + 1)) (h0 : projQ ξ (k + 1) (t + 1) x = 0) :
    Cincl ξ (k + 1) t (dFs ξ (k + 1) (t + 1) t x) ∈ V ξ t k := by
  -- `hx` says precisely that `∂x` (computed in `C`) lies in `F_0`.
  have hx' := hx
  simp only [Wrel, Submodule.mem_comap] at hx'
  have hx'' : Cincl ξ (k + 1) t (dFs ξ (k + 1) (t + 1) t x) ∈ Fch ξ 0 t := by
    simpa using hx'
  -- The vanishing of the class of `x` in the graded piece means `x` is the image of a chain of
  -- `F_k`.
  obtain ⟨y, hy⟩ := (projQ_succ_eq_zero_iff ξ k (t + 1) x).mp h0
  have hchain : Cincl ξ (k + 1) (t + 1) x = Cincl ξ k (t + 1) y := by
    rw [← hy]
    exact Cincl_Finc_apply ξ (Nat.le_succ k) (t + 1) y
  -- Hence `∂x = ∂(incl_k y)`, which is the `C`-image of the chain `incl_k y` of `F_k`.
  have h1 : Cincl ξ (k + 1) t (dFs ξ (k + 1) (t + 1) t x) = dC C (t + 1) t (Cincl ξ k (t + 1) y) := by
    rw [Cincl_dFs_apply, hchain]
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · -- `∂x` lies in `∂(F_k) ⊆ ∂(F_k C_{t+1})`
    refine Submodule.mem_map.mpr ⟨Cincl ξ k (t + 1) y, ?_, ?_⟩
    · rw [mem_Fch]; exact ⟨y, rfl⟩
    · rw [h1]
  · -- `∂x` is a cycle of `F_0`
    refine Submodule.mem_inf.mpr ⟨?_, hx''⟩
    · rw [LinearMap.mem_ker, h1]
      exact dC_dC t (Cincl ξ k (t + 1) y)

end Work.SSS.Transgression
