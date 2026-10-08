import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.ThreePoints.P3NeBot.isStronglyEmbedded_map_of_ker_odd
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.Models.Abstract.ModelData

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs

/-!
# Transfer of the split rank-one structure along a surjection

Let `φ : F →* Y` be a surjective homomorphism of finite groups with `ker φ = Z(F)`
(so `O(F) = Z(F)`); let `H ≤ F` be strongly embedded, `t ∉ H` an involution, and
`H = S ⋊ D`, `D = H ∩ H^t`, with `S ⊓ D = ⊥` and `S ⊔ D = H`.

If `H.map φ` is the Borel subgroup of a model on `Y` (hypothesis `hmod`), then
`(H.map φ, S.map φ, φ t)` is a split rank-one configuration in `Y`: strongly embedded
Borel, `2`-transitive action on `Y ⧸ H.map φ`, and `H.map φ = S.map φ ⋊ D.map φ` with
`D.map φ = twoPoint (H.map φ) (φ t)`.

The group-theoretic content is that `ker φ = Z(F) ≤ H`, so `φ` does not collapse `t`
out of the picture, and that the two-point stabiliser maps: `twoPoint (H.map φ) (φ t)`
is `(twoPoint H t).map φ` because `ker φ ≤ H`.
-/

/-- The centre of a finite group lies in every strongly embedded subgroup: a central element
`z ∉ H` would give `H ⊓ H^z = H` of odd order, contradicting `H` even. -/
private theorem center_le_of_isStronglyEmbedded {G : Type*} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsStronglyEmbedded H) : Subgroup.center G ≤ H := by
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

/-- A central element lies in every conjugate of a subgroup containing the centre. -/
private theorem center_le_conj {G : Type*} [Group G] {H : Subgroup G} {t z : G}
    (hz : z ∈ Subgroup.center G) (hzH : z ∈ H) :
    z ∈ Submission.Blueprint.conj t H := by
  rw [Work.Models.mem_conj_iff]
  have hcomm : z * t = t * z := ((Subgroup.mem_center_iff.mp hz) t).symm
  have hzt : t⁻¹ * z * t = z := by
    rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  rw [hzt]; exact hzH

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

theorem isSplitRankOneTransfer {F : Type} [Group F] [Finite F] {H : Subgroup F} {t : F}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) (ht : orderOf t = 2) (htH : t ∉ H)
    (hcenter : Submission.Blueprint.oddCore F = Subgroup.center F)
    {Y : Type} [Group Y] [Finite Y] {φ : F →* Y} (hsurj : Function.Surjective φ)
    (hker : φ.ker = Subgroup.center F)
    (hmod : ∃ P : Work.Models.ModelData Y, P.B = H.map φ)
    {S : Subgroup F} (hS2 : IsPGroup 2 S) (hSH : S ≤ H)
    (hSnorm : H ≤ Subgroup.normalizer (S : Set F))
    (hSinf : S ⊓ Submission.Blueprint.twoPoint H t = ⊥)
    (hSsup : S ⊔ Submission.Blueprint.twoPoint H t = H) :
    Submission.Blueprint.IsSplitRankOne (H.map φ) (S.map φ) (φ t) := by
  obtain ⟨P, hPB⟩ := hmod
  have hkerH : φ.ker ≤ H := by
    rw [hker]
    exact center_le_of_isStronglyEmbedded hH
  have hkerD : φ.ker ≤ Submission.Blueprint.twoPoint H t := by
    rw [hker]
    intro z hz
    exact ⟨center_le_of_isStronglyEmbedded hH hz,
      center_le_conj hz (center_le_of_isStronglyEmbedded hH hz)⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hPB]; exact P.hSemb
  · show MulAction.IsMultiplyPretransitive Y (Y ⧸ H.map φ) 2
    rw [← hPB]; exact P.isMultiplyPretransitive_two
  · exact orderOf_map_eq_two φ ht hkerH htH
  · exact map_not_mem φ hkerH htH
  · exact Subgroup.map_mono hSH
  · exact map_le_normalizer_map φ hSnorm
  · rw [twoPoint_map φ hkerH]
    exact map_inf_eq_bot_of_inf_eq_bot φ hSinf hkerD
  · rw [twoPoint_map φ hkerH, ← Subgroup.map_sup, hSsup]

end Work.PSU3.StageA
