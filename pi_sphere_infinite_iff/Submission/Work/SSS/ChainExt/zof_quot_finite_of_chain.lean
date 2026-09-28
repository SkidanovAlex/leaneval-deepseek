import Mathlib
import Submission.Work.SSS.FibreColDefs
import Submission.Work.SSS.FinExt.module_finite_quot_of_le

namespace Work.SSS.ChainExt

open CategoryTheory CategoryTheory.Limits

attribute [-instance] AddCommGroup.toIntModule

/-! ## Monotonicity of `Cincl`, `Fch`, `V` and `VZ`

The `s`-th step `V_s = ∂(F_sC_{t+1}) ∩ Z_t(F_0)` of the left column is increasing in `s`, because
the filtration terms are nested.  The nesting of the `Fch` is read off the compatibility
`ξ.compat h : ξ.F.map (homOfLE h) ≫ ξ.incl s' = ξ.incl s` of the filtration. -/

/-- The chain-level inclusion `F_s ⊆ F_{s'} ⊆ C` factors as `F_s → F_{s'} → C`: this is the
degree-`n` component of `ξ.compat`. -/
theorem Cincl_compat {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C) {s s' : ℕ}
    (h : s ≤ s') (n : ℕ) :
    Cincl ξ s n = Cincl ξ s' n ∘ₗ ((ξ.F.map (homOfLE h)).f n).hom := by
  have hc := congrArg (fun (φ : ξ.F.obj s ⟶ C) => (φ.f n).hom) (ξ.compat h)
  simpa only [HomologicalComplex.comp_f, ModuleCat.hom_comp, Cincl] using hc.symm

/-- The chains of `F_s` in degree `n` sit inside those of `F_{s'}` for `s ≤ s'`. -/
theorem Fch_mono {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C) {s s' : ℕ}
    (h : s ≤ s') (n : ℕ) : Fch ξ s n ≤ Fch ξ s' n := by
  intro x hx
  rw [mem_Fch] at hx ⊢
  obtain ⟨y, rfl⟩ := hx
  refine ⟨((ξ.F.map (homOfLE h)).f n) y, ?_⟩
  exact (DFunLike.congr_fun (Cincl_compat ξ h n) y).symm

/-- `V_s = ∂(F_sC_{t+1}) ∩ Z_t(F_0)` is increasing in `s`. -/
theorem V_mono {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C) (t : ℕ) :
    Monotone (V ξ t) := by
  intro s s' h
  have hmap : Submodule.map (dC C (t + 1) t) (Fch ξ s (t + 1)) ≤
      Submodule.map (dC C (t + 1) t) (Fch ξ s' (t + 1)) :=
    Submodule.map_mono (f := dC C (t + 1) t) (Fch_mono ξ h (t + 1))
  simp only [V]
  exact inf_le_inf_right (Zof ξ t) hmap

/-- `V_s`, viewed as a submodule of `Z_t(F_0)`, is increasing in `s`. -/
theorem VZ_mono {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C) (t : ℕ) :
    Monotone (VZ ξ t) := by
  intro s s' h
  simp only [VZ]
  exact Submodule.comap_mono (V_mono ξ t h)

/-- **The left-column extension chain.**  `Z_t(F_0)/V_1 = ↥(Zof ξ t) ⧸ VZ ξ t 1` is finitely
generated if `Z_t(F_0)/V_{t+1}` is and so is each step `V_s/V_{s-1} = ↥(VZ ξ t s) ⧸ VZQ ξ t s`
(`2 ≤ s ≤ t+1`).  This is the descending induction on the chain of submodules
`V_1 ⊆ V_2 ⊆ ⋯ ⊆ V_{t+1} ⊆ Z_t(F_0)`: the quotient map
`↥(Zof ξ t) ⧸ VZ ξ t s → ↥(Zof ξ t) ⧸ VZ ξ t (s+1)` is surjective with kernel
`VZ ξ t (s+1)/VZ ξ t s`, so an extension of finitely generated modules is finitely generated
(`Module.Finite` of the middle from finite kernel and finite target, applied with
`Submodule.mapQ (VZ ξ t s) (VZ ξ t (s+1)) LinearMap.id h`).  The monotonicity
`VZ ξ t s ≤ VZ ξ t s'` for `s ≤ s'` follows from `Fch ξ s n ≤ Fch ξ s' n` (which comes from
`ξ.compat`). -/
theorem zof_quot_finite_of_chain {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Filtration C) (t : ℕ)
    (hTop : Module.Finite ℤ (↥(Zof ξ t) ⧸ VZ ξ t (t + 1)))
    (hQ : ∀ s : ℕ, 2 ≤ s → s ≤ t + 1 →
      Module.Finite ℤ (↥(VZ ξ t s) ⧸ VZQ ξ t s)) :
    Module.Finite ℤ (↥(Zof ξ t) ⧸ VZ ξ t 1) := by
  -- Descending induction along `Z_t(F_0) ⊇ V_{t+1} ⊇ ⋯ ⊇ V_1`: `Z_t(F_0)/V_s` is finitely
  -- generated for every `s ≤ t+1`, starting from `s = t+1` (the hypothesis `hTop`).
  have step : ∀ k : ℕ, k ≤ t → Module.Finite ℤ (↥(Zof ξ t) ⧸ VZ ξ t (t + 1 - k)) := by
    intro k
    induction k with
    | zero =>
      intro _
      simpa using hTop
    | succ k ih =>
      intro hk
      have hle : t - k ≤ t + 1 - k := by omega
      -- the step `V_{t+1-k}/V_{t-k}` is one of the hypothesis quotients
      have hker : Module.Finite ℤ
          (↥(VZ ξ t (t + 1 - k)) ⧸
            Submodule.comap (VZ ξ t (t + 1 - k)).subtype (VZ ξ t (t - k))) := by
        have h2 : 2 ≤ t + 1 - k := by omega
        have h3 : t + 1 - k ≤ t + 1 := by omega
        have h := hQ (t + 1 - k) h2 h3
        rwa [VZQ, show t + 1 - k - 1 = t - k by omega] at h
      have hmid := Work.SSS.FinExt.module_finite_quot_of_le (VZ ξ t (t - k))
        (VZ ξ t (t + 1 - k)) (VZ_mono ξ t hle) hker (ih (by omega))
      have hgoal : t + 1 - (k + 1) = t - k := by omega
      rw [hgoal]
      exact hmid
  have h1 := step t le_rfl
  have hgoal : t + 1 - t = 1 := by omega
  rw [hgoal] at h1
  exact h1

end Work.SSS.ChainExt
