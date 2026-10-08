import Mathlib
import Submission.Work.ThmG.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmG

/-- **A point stabiliser lemma for `ThmG`.**

``D = H ∩ Hᵗ`` and ``x ∈ D`` (with the convention of the blueprint, `G ⧸ H` is the set of left
cosets and `g • uH = guH`, so a coset `uH` is fixed by `y` iff `u⁻¹ y u ∈ H`, and the stabiliser
of the coset `H` is `H`).

If `⟨x⟩` fixes exactly two points of `Ω = G ⧸ H`, then every element of `H` centralising `x`
lies in `D = H ∩ Hᵗ`.

Indeed the cosets `H` and `tH` are both fixed by `x` (`H` because `x ∈ H`, `tH` because
`x ∈ Hᵗ` means `t⁻¹ x t ∈ H`); as there are exactly two fixed points and `t ∉ H`, they are all of
them.  Now `c ∈ C_G(x) ∩ H` maps fixed points of `x` to fixed points of `x`, so `c • tH` is
`H` or `tH`.  It cannot be `H`, since `ctH = H` forces `t ∈ H`; hence `ctH = tH`, i.e.
`t⁻¹ c t ∈ H`, i.e. `c ∈ Hᵗ`. -/
theorem centralizer_le_twoPoint_of_fixedPts_card_two {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} {t x : G} (hx : x ∈ Submission.Blueprint.twoPoint H t) (hx1 : x ≠ 1)
    (h2 : (Submission.Blueprint.fixedPts H (Subgroup.zpowers x)).ncard = 2) :
    Subgroup.centralizer ({x} : Set G) ⊓ H ≤ Submission.Blueprint.twoPoint H t := by
  have hxH : x ∈ H := hx.1
  have hzH : ∀ y ∈ Subgroup.zpowers x, y ∈ H := fun y hy => Subgroup.zpowers_le.mpr hxH hy
  have hxt : x ∈ Submission.Blueprint.conj t H := hx.2
  intro c hc
  obtain ⟨hcC, hcH⟩ := hc
  have hcomm : c * x = x * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
  have hxmem : x ∈ Subgroup.centralizer ({c} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (by rw [hcomm])
  by_cases ht : t ∈ H
  · -- the two-point stabiliser is all of `H`
    have hle : H ≤ Submission.Blueprint.conj t H := by
      intro g hg
      rw [Submission.Blueprint.conj, Subgroup.mem_map]
      refine ⟨t⁻¹ * g * t, H.mul_mem (H.mul_mem (H.inv_mem ht) hg) ht, ?_⟩
      change (MulAut.conj t) (t⁻¹ * g * t) = g
      rw [MulAut.conj_apply]; group
    exact ⟨hcH, hle hcH⟩
  · -- `t ∉ H`: the cosets `H` and `tH` are exactly the two fixed points of `⟨x⟩`
    have hmem1 : ((1 : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H (Subgroup.zpowers x) := by
      rw [Submission.Blueprint.fixedPts]
      intro y hy
      have hyH : y ∈ H := hzH y hy
      change ((y * 1 : G) : G ⧸ H) = ((1 : G) : G ⧸ H)
      rw [mul_one, QuotientGroup.eq]
      simpa using H.inv_mem hyH
    have hmemt : ((t : G) : G ⧸ H) ∈ Submission.Blueprint.fixedPts H (Subgroup.zpowers x) := by
      rw [Submission.Blueprint.fixedPts]
      intro y hy
      change ((y * t : G) : G ⧸ H) = ((t : G) : G ⧸ H)
      rw [QuotientGroup.eq]
      rcases Subgroup.mem_map.mp (Subgroup.zpowers_le.mpr hxt hy) with ⟨h, hh, hhy⟩
      change (MulAut.conj t) h = y at hhy
      rw [MulAut.conj_apply] at hhy
      have hh' : (y * t)⁻¹ * t = h⁻¹ := by rw [← hhy]; group
      rw [hh']; exact H.inv_mem hh
    have hab : ((1 : G) : G ⧸ H) ≠ ((t : G) : G ⧸ H) := by
      intro hcon
      rw [QuotientGroup.eq] at hcon
      exact ht (by simpa using hcon)
    have hfix : Submission.Blueprint.fixedPts H (Subgroup.zpowers x)
        = {((1 : G) : G ⧸ H), ((t : G) : G ⧸ H)} := by
      refine (Set.eq_of_subset_of_ncard_le ?_ ?_).symm
      · rintro ω (rfl | rfl)
        · exact hmem1
        · exact hmemt
      · rw [h2, Set.ncard_pair hab]
    -- `c` fixes `tH`, since `c` preserves the fixed points of `x` and `tH` cannot go to `H`
    have hcbfix : c • ((t : G) : G ⧸ H)
        ∈ Submission.Blueprint.fixedPts H (Subgroup.zpowers x) := by
      rw [Submission.Blueprint.fixedPts]
      intro y hy
      have h1 : y ∈ Subgroup.centralizer ({c} : Set G) := Subgroup.zpowers_le.mpr hxmem hy
      have hyc : y * c = c * y := Subgroup.mem_centralizer_singleton_iff.mp h1
      rw [← mul_smul, hyc, mul_smul, hmemt y hy]
    rw [hfix] at hcbfix
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hcbfix
    rcases hcbfix with hcb | hcb
    · -- `c • tH = H` would force `t ∈ H`
      change ((c * t : G) : G ⧸ H) = ((1 : G) : G ⧸ H) at hcb
      rw [QuotientGroup.eq] at hcb
      have hmem : t⁻¹ * c⁻¹ ∈ H := by simpa using hcb
      have htinv : t⁻¹ ∈ H := by
        have hh := H.mul_mem hmem hcH
        simpa [mul_assoc] using hh
      have htH : t ∈ H := by simpa using H.inv_mem htinv
      exact absurd htH ht
    · -- `c • tH = tH` is the conclusion `c ∈ Hᵗ`
      change ((c * t : G) : G ⧸ H) = ((t : G) : G ⧸ H) at hcb
      rw [QuotientGroup.eq] at hcb
      have hmem : t⁻¹ * c⁻¹ * t ∈ H := by simpa using hcb
      have hcinv : c⁻¹ ∈ Submission.Blueprint.conj t H := by
        rw [Submission.Blueprint.conj, Subgroup.mem_map]
        refine ⟨t⁻¹ * c⁻¹ * t, hmem, ?_⟩
        change (MulAut.conj t) (t⁻¹ * c⁻¹ * t) = c⁻¹
        rw [MulAut.conj_apply]; group
      have hcfin : c ∈ Submission.Blueprint.conj t H := by
        simpa using (Submission.Blueprint.conj t H).inv_mem hcinv
      exact ⟨hcH, hcfin⟩

end Work.ThmG
