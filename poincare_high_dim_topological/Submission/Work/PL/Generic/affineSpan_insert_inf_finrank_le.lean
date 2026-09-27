import Mathlib
import Submission.Work.PL.Defs
import Submission.Work.PL.Generic.Basic

namespace Work.PL.Generic

open Set Metric

/-- Generic affine span: adjoining a point outside the affine span of `S ∪ W` does not increase
the dimension of the intersection with `W`.  Proof: `y ∉ S ⊔ W` implies `y -ᵥ p ∉ S.direction + W.direction`
for `p ∈ S`, whence the direction of `affineSpan (S ∪ {y}) ⊓ W` is contained in `(S.direction) ⊓ (W.direction)`
and, when `S ⊓ W = ⊥`, also `affineSpan (S ∪ {y}) ⊓ W = ⊥` (otherwise the same computation gives
`y ∈ S ⊔ W`). -/
theorem affineSpan_insert_inf_finrank_le {m : ℕ} {S W : AffineSubspace ℝ (PL.E m)} {y : PL.E m}
    (hy : y ∉ ((S ⊔ W : AffineSubspace ℝ (PL.E m)) : Set (PL.E m))) :
    Module.finrank ℝ (affineSpan ℝ ((S : Set (PL.E m)) ∪ {y}) ⊓ W).direction ≤
      max (Module.finrank ℝ (S ⊓ W).direction)
        (Module.finrank ℝ S.direction + 1 + Module.finrank ℝ W.direction -
          Module.finrank ℝ (PL.E m)) := by
  rw [Set.union_singleton]
  by_cases hSW : S ⊓ W = ⊥
  · -- `S ⊓ W = ⊥`: then `affineSpan (S ∪ {y}) ⊓ W = ⊥` as well, so the left side vanishes.
    have hTW : affineSpan ℝ (insert y (S : Set (PL.E m))) ⊓ W = ⊥ := by
      rw [← AffineSubspace.coe_eq_bot_iff, Set.eq_empty_iff_forall_notMem]
      intro z hz
      simp only [AffineSubspace.coe_inf, Set.mem_inter_iff] at hz
      obtain ⟨hzT, hzW⟩ := hz
      rcases eq_or_ne S ⊥ with hS | hS
      · -- `S = ⊥`: then `z = y`, which is not in `W` because `y ∉ S ⊔ W = W`.
        have hzT' : z ∈ (affineSpan ℝ ({y} : Set (PL.E m))) := by simpa [hS] using hzT
        rw [AffineSubspace.affineSpan_singleton, AffineSubspace.mem_singleton_iff] at hzT'
        rw [hzT'] at hzW
        exact hy ((le_sup_right : W ≤ S ⊔ W) hzW)
      · -- `S ≠ ⊥`: write `z = t • (y -ᵥ p) +ᵥ p₀` with `p₀ ∈ S`.
        obtain ⟨p, hp⟩ := (AffineSubspace.nonempty_iff_ne_bot S).mpr hS
        obtain ⟨t, p0, hp0, hzeq⟩ := (AffineSubspace.mem_affineSpan_insert_iff hp y z).mp hzT
        rcases eq_or_ne t 0 with ht | ht
        · -- `t = 0`: then `z = p₀ ∈ S`, so `z ∈ S ⊓ W = ⊥`, absurd.
          rw [ht, zero_smul, zero_vadd] at hzeq
          have hzS : z ∈ S := by rw [hzeq]; exact hp0
          have : z ∈ (⊥ : AffineSubspace ℝ (PL.E m)) := by
            rw [← hSW]
            exact (AffineSubspace.mem_inf_iff z S W).mpr ⟨hzS, hzW⟩
          exact AffineSubspace.notMem_bot ℝ (PL.E m) z this
        · -- `t ≠ 0`: then `y = t⁻¹ • (z -ᵥ p₀) +ᵥ p ∈ affineSpan (S ∪ {z}) ⊆ S ⊔ W`.
          have hy_mem : y ∈ affineSpan ℝ (insert z (S : Set (PL.E m))) := by
            rw [AffineSubspace.mem_affineSpan_insert_iff hp0]
            refine ⟨t⁻¹, p, hp, ?_⟩
            have hzp : z -ᵥ p0 = t • (y -ᵥ p) := by rw [hzeq, vadd_vsub]
            rw [hzp, smul_smul, inv_mul_cancel₀ ht, one_smul, vsub_vadd]
          have hle : affineSpan ℝ (insert z (S : Set (PL.E m))) ≤ S ⊔ W := by
            rw [affineSpan_le]
            intro w hw
            rw [Set.mem_insert_iff] at hw
            rcases hw with rfl | hwS
            · exact (le_sup_right : W ≤ S ⊔ W) hzW
            · exact (le_sup_left : S ≤ S ⊔ W) hwS
          exact hy (hle hy_mem)
    rw [hSW, hTW]
    simp
  · -- `S ⊓ W ≠ ⊥`: show `(affineSpan (S ∪ {y}) ⊓ W).direction ≤ (S ⊓ W).direction`.
    obtain ⟨r, hr⟩ := (AffineSubspace.nonempty_iff_ne_bot (S ⊓ W)).mpr hSW
    obtain ⟨hrS, hrW⟩ := (AffineSubspace.mem_inf_iff r S W).mp hr
    have hSne : S ≠ ⊥ := by intro h; exact hSW (by rw [h, bot_inf_eq])
    obtain ⟨p, hp⟩ := (AffineSubspace.nonempty_iff_ne_bot S).mpr hSne
    -- The direction of `T := affineSpan (S ∪ {y})` is `ℝ ∙ (y -ᵥ p) ⊔ S.direction`.
    have hdirT : (affineSpan ℝ (insert y (S : Set (PL.E m)))).direction
        = (ℝ ∙ (y -ᵥ p)) ⊔ S.direction := AffineSubspace.direction_affineSpan_insert hp
    -- Since `S ⊓ W ≠ ⊥`, the direction of `S ⊔ W` is `S.direction ⊔ W.direction`.
    have hdirSW : (S ⊔ W).direction = S.direction ⊔ W.direction :=
      AffineSubspace.direction_sup_eq_sup_direction hrS hrW
    -- `y -ᵥ p` is not in this direction, because `y ∉ S ⊔ W`.
    have hu : y -ᵥ p ∉ S.direction ⊔ W.direction := by
      intro hmem
      have hpSW : p ∈ (S ⊔ W : AffineSubspace ℝ (PL.E m)) := (le_sup_left : S ≤ S ⊔ W) hp
      have h2 : (y -ᵥ p) +ᵥ p ∈ (S ⊔ W : AffineSubspace ℝ (PL.E m)) :=
        (AffineSubspace.vadd_mem_iff_mem_direction (s := S ⊔ W) (y -ᵥ p) hpSW).mpr
          (hdirSW.symm ▸ hmem)
      rw [vsub_vadd] at h2
      exact hy h2
    -- Key inclusion: `T.direction ⊓ W.direction ≤ S.direction`.
    have hkey : (affineSpan ℝ (insert y (S : Set (PL.E m)))).direction ⊓ W.direction
        ≤ S.direction := by
      intro v hv
      rw [Submodule.mem_inf] at hv
      obtain ⟨hvT, hvW⟩ := hv
      rw [hdirT, Submodule.mem_sup] at hvT
      obtain ⟨c, hc, a, ha, hca⟩ := hvT
      rw [Submodule.mem_span_singleton] at hc
      obtain ⟨t, rfl⟩ := hc
      by_cases ht : t = 0
      · rw [ht, zero_smul, zero_add] at hca
        rwa [← hca]
      · -- `t ≠ 0` would give `y -ᵥ p = t⁻¹ • (v - a) ∈ S.direction ⊔ W.direction`.
        exfalso
        have hv_sub : v - a = t • (y -ᵥ p) := by rw [← hca, add_sub_cancel_right]
        have h1 : y -ᵥ p = t⁻¹ • (v - a) := by
          rw [hv_sub, smul_smul, inv_mul_cancel₀ ht, one_smul]
        have hva : v - a ∈ S.direction ⊔ W.direction :=
          Submodule.sub_mem _ ((le_sup_right : W.direction ≤ S.direction ⊔ W.direction) hvW)
            ((le_sup_left : S.direction ≤ S.direction ⊔ W.direction) ha)
        exact hu (h1 ▸ Submodule.smul_mem (S.direction ⊔ W.direction) t⁻¹ hva)
    have hdir_le : (affineSpan ℝ (insert y (S : Set (PL.E m))) ⊓ W).direction
        ≤ (S ⊓ W).direction := by
      calc (affineSpan ℝ (insert y (S : Set (PL.E m))) ⊓ W).direction
          ≤ (affineSpan ℝ (insert y (S : Set (PL.E m)))).direction ⊓ W.direction :=
            AffineSubspace.direction_inf _ _
        _ ≤ S.direction ⊓ W.direction := le_inf hkey inf_le_right
        _ = (S ⊓ W).direction := (AffineSubspace.direction_inf_of_mem hrS hrW).symm
    exact le_trans (Submodule.finrank_mono hdir_le) (le_max_left _ _)

end Work.PL.Generic
