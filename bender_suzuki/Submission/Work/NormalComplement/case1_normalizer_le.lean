/-
# Chapter III §2 (case 1): the normaliser of a two-point-fixing `U` lies in `D`

This is the elementary "case 1" step of the minimal-counterexample argument of Peterfalvi I
Ch. III §2 (p.175–176): the subgroup `U` of `W ⊓ D` (where `D = H ∩ H^t` is the two-point
stabiliser of the strongly embedded `H` and the involution `t ∉ H`) which fixes *exactly two*
points of `Ω = G ⧸ H` cannot have its normaliser inside `W` meet `H ∖ D`.

## The mathematics

`U ≤ W ⊓ D ≤ H`, so `U` fixes the point `H = 1·H` of `Ω`; `U ≤ D ≤ H^t` means `t⁻¹ u t ∈ H`
for every `u ∈ U`, i.e. `u • tH = tH`, so `U` also fixes `tH`.  The two points are distinct
(`t ∉ H`), and there are exactly two fixed points, hence

  `Fix(U) = {H, tH}`.

Now let `g ∈ N_G(U) ∩ W`.  Since `g ∈ W ≤ H`, `g` fixes `H`; and `g` normalises `U`, hence it
permutes `Fix(U) = {H, tH}`.  It cannot send `H ↦ tH` because it fixes `H`, so it fixes `tH`,
i.e. `g ∈ Stab(tH) = H^t`.  As `g ∈ H` too, `g ∈ H ∩ H^t = D`, which is the claim.

## Note on hypotheses

`hH` (strong embeddeness) and `ht` (`orderOf t = 2`) are not needed for this counting argument:
finiteness of `G` alone suffices.  They are kept because they are the ambient hypotheses of the
area's statement.
-/
import Mathlib
import Submission.Work.NormalComplement.Defs
import Submission.Work.NormalComplement.Prelim

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.unusedVariables false

namespace Work.NormalComplement

theorem case1_normalizer_le (G : Type) [Group G] [Finite G]
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H)
    {t : G} (ht : orderOf t = 2) (htH : t ∉ H)
    {W : Subgroup G} (hW : W ≤ H) {U : Subgroup G}
    (hUE : U ≤ W ⊓ Submission.Blueprint.twoPoint H t)
    (h2 : (Submission.Blueprint.fixedPts H U).ncard = 2) :
    Subgroup.normalizer (U : Set G) ⊓ W ≤ W ⊓ Submission.Blueprint.twoPoint H t := by
  -- `U ≤ H` and `U ≤ Hᵗ`
  have hUH : U ≤ H := fun u hu => hW (hUE hu).1
  have hUconj : U ≤ Submission.Blueprint.conj t H := fun u hu => (hUE hu).2.2
  -- `U` fixes the point `H = 1·H`
  have hmem1 : ((1 : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H U := by
    intro u hu
    change ((u * 1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H)
    rw [mul_one, QuotientGroup.eq]
    simpa using H.inv_mem (hUH hu)
  -- `U` fixes the point `tH`
  have hmemt : ((t : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H U := by
    intro u hu
    change ((u * t : G) : G ⧸ H) = ((t : G) : G ⧸ H)
    rw [QuotientGroup.eq]
    rcases Subgroup.mem_map.mp (hUconj hu) with ⟨h, hh, hhu⟩
    change (MulAut.conj t) h = u at hhu
    rw [MulAut.conj_apply] at hhu
    have hh' : (u * t)⁻¹ * t = h⁻¹ := by rw [← hhu]; group
    rw [hh']; exact H.inv_mem hh
  -- the two points are distinct
  have hab : ((1 : G) : G ⧸ H) ≠ ((t : G) : G ⧸ H) := by
    intro hcon
    rw [QuotientGroup.eq] at hcon
    exact htH (by simpa using hcon)
  -- hence they are *all* the fixed points
  have hfix : Submission.Blueprint.fixedPts H U
      = {((1 : G) : G ⧸ H), ((t : G) : G ⧸ H)} := by
    refine (Set.eq_of_subset_of_ncard_le ?_ ?_).symm
    · rintro ω (rfl | rfl)
      · exact hmem1
      · exact hmemt
    · rw [h2, Set.ncard_pair hab]
  intro g hg
  rw [Subgroup.mem_inf] at hg
  obtain ⟨hgN, hgW⟩ := hg
  have hgH : g ∈ H := hW hgW
  rw [Subgroup.mem_inf]
  refine ⟨hgW, ?_⟩
  rw [Submission.Blueprint.twoPoint, Subgroup.mem_inf]
  refine ⟨hgH, ?_⟩
  -- `g` maps fixed points of `U` to fixed points of `U`
  have hgfix : g • ((t : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H U := by
    intro u hu
    have hgu : g⁻¹ * u * g ∈ U := (Subgroup.mem_normalizer_iff''.mp hgN u).1 hu
    have hstep : u • (g • ((t : G) : G ⧸ H))
        = g • ((g⁻¹ * u * g) • ((t : G) : G ⧸ H)) := by
      rw [← mul_smul, ← mul_smul]
      congr 1
      group
    rw [hstep, hmemt (g⁻¹ * u * g) hgu]
  rw [hfix] at hgfix
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgfix
  rcases hgfix with hcb | hcb
  · -- `g • tH = H` would force `t ∈ H`
    change ((g * t : G) : G ⧸ H) = ((1 : G) : G ⧸ H) at hcb
    rw [QuotientGroup.eq] at hcb
    have hmem : (g * t)⁻¹ ∈ H := by simpa using hcb
    have hgt : g * t ∈ H := by simpa using H.inv_mem hmem
    have hht : t ∈ H := by have := H.mul_mem (H.inv_mem hgH) hgt; simpa using this
    exact absurd hht htH
  · -- `g • tH = tH` is exactly `g ∈ Hᵗ`
    change ((g * t : G) : G ⧸ H) = ((t : G) : G ⧸ H) at hcb
    rw [QuotientGroup.eq] at hcb
    have hmem : t⁻¹ * g⁻¹ * t ∈ H := by simpa using hcb
    have hginv : g⁻¹ ∈ Submission.Blueprint.conj t H := by
      rw [Submission.Blueprint.conj, Subgroup.mem_map]
      refine ⟨t⁻¹ * g⁻¹ * t, hmem, ?_⟩
      change (MulAut.conj t) (t⁻¹ * g⁻¹ * t) = g⁻¹
      rw [MulAut.conj_apply]; group
    simpa using (Submission.Blueprint.conj t H).inv_mem hginv

end Work.NormalComplement
