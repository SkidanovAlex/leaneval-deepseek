import Mathlib
import Submission.Work.PSU3.StageA.isSplitRankOneTransfer
import Submission.Work.PSU3.StageA.modelDataBorel
import Submission.Work.ThreePoints.P3NeBot.isStronglyEmbedded_map_of_ker_odd
import Submission.Work.Models.Abstract.ModelData
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB

/-
# Step 5, item 1: the split rank-one datum of `Y = F/Z(F)` (datum transfer)

For `F = O^{2'}(C_G(P))` with its split rank-one datum `(H, S, t)` (`H = F ⊓ H_G` in the
application) and `φ : F →* Y` an epimorphism with *central* kernel onto a simple Bender group `Y`,
the images `(H.map φ, S.map φ, φ t)` form a split rank-one datum in `Y`.

This is `Work.PSU3.StageA.isSplitRankOneTransfer` with its hypotheses reorganised: the ModelData
input `hmod` is discharged by `Work.PSU3.StageA.modelDataBorel` (every strongly embedded subgroup
of a simple Bender group is the Borel of some `ModelData`), applied to the image of `H`, which is
strongly embedded by `Work.ThreePoints.P3NeBot.isStronglyEmbedded_map_of_ker_odd` — its two side
conditions being `Odd (Nat.card φ.ker)` (`hker` + `Work.BrauerSuzuki.OddCore.oddCard_oddCore`) and
`φ.ker ≤ H`.  All other hypotheses of the transfer (strong embeddedness, `orderOf t = 2`,
`t ∉ H`, `S ≤ H`, `H ≤ N(S)`, `S ⊓ twoPoint H t = ⊥`, `S ⊔ twoPoint H t = H`) are exactly the
fields of `hS`; the transfer's `hS2 : IsPGroup 2 S` is not used by it and is therefore dropped.

⚠ Prover's note: the fact `Subgroup.center F ≤ H` for strongly embedded `H` was only a *private*
result inside `Submission/Work/PSU3/StageA/isSplitRankOneTransfer.lean`; it is re-proved here as
`center_le_of_isStronglyEmbedded` (a central `z ∉ H` would give `H ⊓ H^z = H` of odd order,
contradicting `Even (Nat.card H)`).
-/

/-- The centre of a finite group lies in every strongly embedded subgroup: a central element
`z ∉ H` would give `H ⊓ H^z = H` of odd order, contradicting `H` even. -/
private theorem center_le_of_isStronglyEmbedded {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) : Subgroup.center G ≤ H := by
  intro z hz
  by_contra hzH
  have hodd := hH.2.2 z hzH
  have hle : H ≤ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj z)) H := by
    intro x hx
    refine ⟨z⁻¹ * x * z, ?_, ?_⟩
    · have hcomm : x * z = z * x := (Subgroup.mem_center_iff.mp hz) x
      have hzx : z⁻¹ * x * z = x := by
        rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [hzx]; exact hx
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group
  have hconj : H ⊓ Subgroup.map (MulEquiv.toMonoidHom (MulAut.conj z)) H = H :=
    inf_eq_left.mpr hle
  rw [hconj] at hodd
  exact (Nat.not_even_iff_odd.mpr hodd) hH.2.1

/-- A central element of `H`, being fixed by every conjugation, lies in every conjugate of `H`. -/
private theorem center_le_conj {G : Type*} [Group G] {H : Subgroup G} {t : G}
    (h : Subgroup.center G ≤ H) : Subgroup.center G ≤ Submission.Blueprint.conj t H := by
  intro z hz
  rw [Work.Models.mem_conj_iff]
  have hzt : t⁻¹ * z * t = z := by
    have hcomm : z * t = t * z := ((Subgroup.mem_center_iff.mp hz) t).symm
    rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hzt]
  exact h hz

/-- If `ker φ ≤ D` and `S ⊓ D = ⊥`, then the images of `S` and `D` intersect trivially. -/
private theorem map_inf_eq_bot_of_inf_eq_bot {F Y : Type*} [Group F] [Group Y] (φ : F →* Y)
    {S D : Subgroup F} (hSD : S ⊓ D = ⊥) (hkerD : φ.ker ≤ D) :
    S.map φ ⊓ D.map φ = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxS, hxD⟩ := hx
  obtain ⟨s, hsS, rfl⟩ := Subgroup.mem_map.mp hxS
  obtain ⟨d, hdD, hds⟩ := Subgroup.mem_map.mp hxD
  rw [Subgroup.mem_bot]
  have hz : s⁻¹ * d ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hds, inv_mul_cancel]
  have hzD : s⁻¹ * d ∈ D := hkerD hz
  have hsD : s ∈ D := by
    have hsd : s = d * (s⁻¹ * d)⁻¹ := by group
    rw [hsd]
    exact D.mul_mem hdD (D.inv_mem hzD)
  have hsbot : s ∈ S ⊓ D := ⟨hsS, hsD⟩
  have hs1 : s = 1 := by
    have : s ∈ (⊥ : Subgroup F) := by rw [← hSD]; exact hsbot
    simpa using this
  rw [hs1, map_one]

/-- The two-point stabiliser is preserved by `φ` when `ker φ ≤ H`. -/
private theorem twoPoint_map {F Y : Type*} [Group F] [Group Y] (φ : F →* Y)
    {H : Subgroup F} {t : F} (hkerH : φ.ker ≤ H) :
    Submission.Blueprint.twoPoint (H.map φ) (φ t) = (Submission.Blueprint.twoPoint H t).map φ := by
  have h1 : Submission.Blueprint.conj (φ t) (H.map φ) = (Submission.Blueprint.conj t H).map φ :=
    (Commons.GroupTheory.Subgroup.map_conj_map φ H t).symm
  unfold Submission.Blueprint.twoPoint
  rw [h1]
  exact (Commons.GroupTheory.Subgroup.map_inf_eq_of_ker_le φ H
    (Submission.Blueprint.conj t H) hkerH).symm

/-- `φ t` is not in `H.map φ` when `ker φ ≤ H` and `t ∉ H`. -/
private theorem map_not_mem {F Y : Type*} [Group F] [Group Y] (φ : F →* Y)
    {H : Subgroup F} {t : F} (hkerH : φ.ker ≤ H) (htH : t ∉ H) :
    φ t ∉ H.map φ := by
  intro h
  obtain ⟨h', hh', heq⟩ := Subgroup.mem_map.mp h
  have hmem : h'⁻¹ * t ∈ φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, heq, inv_mul_cancel]
  have hmH : h'⁻¹ * t ∈ H := hkerH hmem
  have ht : t ∈ H := by
    have hsplit : t = h' * (h'⁻¹ * t) := by group
    rw [hsplit]
    exact H.mul_mem hh' hmH
  exact htH ht

/-- Order is preserved on an involution not in `ker φ`. -/
private theorem orderOf_map_eq_two {F Y : Type*} [Group F] [Group Y] (φ : F →* Y)
    {H : Subgroup F} {t : F} (ht : orderOf t = 2) (hkerH : φ.ker ≤ H) (htH : t ∉ H) :
    orderOf (φ t) = 2 := by
  have hdvd : orderOf (φ t) ∣ 2 := by rw [← ht]; exact orderOf_map_dvd φ t
  have hne : orderOf (φ t) ≠ 1 := by
    intro h1
    exact htH (hkerH ((MonoidHom.mem_ker).mpr (orderOf_eq_one_iff.mp h1)))
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
  · exact absurd h hne
  · exact h

/-- Normality of `S` in `H` passes to the images. -/
private theorem map_le_normalizer_map {F Y : Type*} [Group F] [Group Y] (φ : F →* Y)
    {H S : Subgroup F} (hSnorm : H ≤ Subgroup.normalizer (S : Set F)) :
    H.map φ ≤ Subgroup.normalizer ((S.map φ : Subgroup Y) : Set Y) := by
  calc H.map φ ≤ (Subgroup.normalizer (S : Set F)).map φ := Subgroup.map_mono hSnorm
    _ ≤ Subgroup.normalizer ((S.map φ : Subgroup Y) : Set Y) := Subgroup.le_normalizer_map φ

theorem isSplitRankOne_map_of_surjective {F : Type} [Group F] [Finite F]
    {H S : Subgroup F} {t : F} (hS : Submission.Blueprint.IsSplitRankOne H S t)
    (hcenter : Submission.Blueprint.oddCore F = Subgroup.center F)
    {Y : Type} [Group Y] [Finite Y] {φ : F →* Y} (hsurj : Function.Surjective φ)
    (hker : φ.ker = Subgroup.center F)
    (hY : LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y) :
    Submission.Blueprint.IsSplitRankOne (H.map φ) (S.map φ) (φ t) := by
  classical
  -- `ker φ = Z(F) ≤ H`, since `H` is strongly embedded.
  have hcenterH : Subgroup.center F ≤ H :=
    center_le_of_isStronglyEmbedded hS.stronglyEmbedded
  have hkerH : φ.ker ≤ H := by rw [hker]; exact hcenterH
  -- `ker φ ≤ D = H ⊓ H^t`: a central element is fixed, hence lies in every conjugate.
  have hkerD : φ.ker ≤ Submission.Blueprint.twoPoint H t := by
    rw [hker]
    exact le_inf hcenterH (center_le_conj (H := H) hcenterH)
  -- `ker φ` has odd order, so strong embeddedness passes to `H.map φ`.
  have hodd : Odd (Nat.card φ.ker) := by
    rw [hker, ← hcenter]
    exact Work.BrauerSuzuki.OddCore.oddCard_oddCore
  have hemb : LeanEval.GroupTheory.Defs.IsStronglyEmbedded (H.map φ) :=
    Work.ThreePoints.P3NeBot.isStronglyEmbedded_map_of_ker_odd (H := H) φ hsurj hodd hkerH
      hS.stronglyEmbedded
  -- Every strongly embedded subgroup of a simple Bender group is the Borel of some `ModelData`;
  -- that supplies the `2`-transitivity of `Y` on `Y ⧸ H.map φ`.
  obtain ⟨P, hPB⟩ := Work.PSU3.StageA.modelDataBorel hY hemb
  refine ⟨hemb, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show MulAction.IsMultiplyPretransitive Y (Y ⧸ H.map φ) 2
    rw [← hPB]; exact P.isMultiplyPretransitive_two
  · exact orderOf_map_eq_two (H := H) φ hS.invol hkerH hS.not_mem
  · exact map_not_mem (H := H) φ hkerH hS.not_mem
  · exact Subgroup.map_mono hS.le
  · exact map_le_normalizer_map (H := H) (S := S) φ hS.normal
  · rw [twoPoint_map (H := H) φ hkerH]
    exact map_inf_eq_bot_of_inf_eq_bot (S := S) (D := Submission.Blueprint.twoPoint H t) φ
      hS.inf_eq hkerD
  · rw [twoPoint_map (H := H) φ hkerH, ← Subgroup.map_sup, hS.sup_eq]

end Work.PSU3.StageB
