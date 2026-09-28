import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Transf.Basic
import Submission.Work.HP.BCS.Setup

namespace Work.HP.Sig2

open Work.HP.BCS

/-- In `ℝ^ι` (`ι` finite, so finite dimensional), if `W ≤ V` are `ℝ`-submodules with `W ≠ V`, then
for every prescribed `r > 0` there is a vector of `V` of Euclidean `Work.HP.rNorm` exactly `r` which
is `Work.HP.dotR`-orthogonal to all of `W`.

Intended proof: transport along `WithLp.toLp 2 : (ι → ℝ) → EuclideanSpace ℝ ι` (a linear isometry
equivalence; `Submission/Work/HP/BCS/Setup.lean` already has `inner_toE_toE`:
`inner ℝ (toE u) (toE v) = dotR v u` and `rNorm_eq_norm_toE : rNorm v = ‖toE v‖`).  In
`EuclideanSpace ℝ ι` the subspace `Wᗮ ⊓ V` has positive dimension because
`Submodule.finrank_add_inf_finrank_orthogonal` gives
`finrank ℝ W + finrank ℝ (Wᗮ ⊓ V) = finrank ℝ V` and `Submodule.finrank_lt_finrank_of_lt` gives
`finrank ℝ W < finrank ℝ V`; take a nonzero vector there and rescale it to norm `r`.
The final statement should live in namespace `Work.HP.Sig2`, i.e. its fully qualified name is
`Work.HP.Sig2.perp_norm_eq`.  (The file is `Submission/Work/HP/Sig2/perp_norm_eq.lean`.) -/
theorem perp_norm_eq {ι : Type*} [Fintype ι] {V W : Submodule ℝ (ι → ℝ)}
    (hWV : W ≤ V) (hne : W ≠ V) {r : ℝ} (hr : 0 < r) :
    ∃ u ∈ V, Work.HP.rNorm u = r ∧ ∀ w ∈ W, Work.HP.dotR u w = 0 := by
  classical
  -- The linear isometry equivalence `(ι → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ ι` given by `toE`.
  let e : (ι → ℝ) ≃ₗ[ℝ] EuclideanSpace ℝ ι := (WithLp.linearEquiv 2 ℝ (ι → ℝ)).symm
  let el : (ι → ℝ) →ₗ[ℝ] EuclideanSpace ℝ ι := e.toLinearMap
  have hel : ∀ v : ι → ℝ, el v = toE v := by
    intro v; simp [el, e, toE, WithLp.linearEquiv_symm_apply]
  have hel_eq : ∀ v : ι → ℝ, el v = e v := fun _ => rfl
  have hel_symm : ∀ y : EuclideanSpace ℝ ι, el (e.symm y) = y := by
    intro y; rw [hel_eq, LinearEquiv.apply_symm_apply]
  -- Push `W` and `V` into Euclidean space.
  have hWV' : W.map el ≤ V.map el := Submodule.map_mono hWV
  have hne' : W.map el ≠ V.map el := fun h =>
    hne (Submodule.map_injective_of_injective e.injective h)
  -- The orthogonal complement of `W` inside `V` is nontrivial.
  have hdim := Submodule.finrank_add_inf_finrank_orthogonal (𝕜 := ℝ)
    (K₁ := W.map el) (K₂ := V.map el) hWV'
  have hlt := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hWV' hne')
  have hpos : 0 < Module.finrank ℝ ↥((W.map el)ᗮ ⊓ (V.map el)) := by omega
  have hne_bot : ((W.map el)ᗮ ⊓ (V.map el)) ≠ ⊥ := by
    intro h; rw [h] at hpos; simp at hpos
  obtain ⟨x, hxS, hx0⟩ := (Submodule.ne_bot_iff _).mp hne_bot
  have hxpos : 0 < ‖x‖ := norm_pos_iff.mpr hx0
  refine ⟨e.symm ((r / ‖x‖) • x), ?_, ?_, ?_⟩
  · -- membership in `V`
    obtain ⟨v, hv, hve⟩ := (Submodule.mem_map).mp ((V.map el).smul_mem (r / ‖x‖) hxS.2)
    have h1 : e.symm ((r / ‖x‖) • x) = v := by
      apply e.injective
      rw [LinearEquiv.apply_symm_apply, ← hve]
      exact hel_eq v
    rw [h1]; exact hv
  · -- the norm is exactly `r`
    rw [rNorm_eq_norm_toE, ← hel (e.symm ((r / ‖x‖) • x)), hel_symm]
    rw [norm_smul, Real.norm_of_nonneg (div_nonneg hr.le (norm_nonneg x)),
      div_mul_cancel₀ r (norm_ne_zero_iff.mpr hx0)]
  · -- orthogonality to `W`
    intro w hw
    have hwW' : el w ∈ W.map el := ⟨w, hw, rfl⟩
    have hyorth : (r / ‖x‖) • x ∈ (W.map el)ᗮ := (W.map el)ᗮ.smul_mem (r / ‖x‖) hxS.1
    have hmem := (Submodule.mem_orthogonal' (W.map el) ((r / ‖x‖) • x)).mp hyorth
    rw [dotR_comm, ← inner_toE_toE (e.symm ((r / ‖x‖) • x)) w,
      ← hel (e.symm ((r / ‖x‖) • x)), ← hel w, hel_symm]
    exact hmem (el w) hwW'

end Work.HP.Sig2
