import Mathlib
import Submission.Work.BSW.Api.card_centralizer_of_card_K_two
import Submission.Work.BSW.Api.mem_centralizer_iff
import Submission.Work.BSW.Basic

namespace Work.BSW.Cases

/-- Conjugating a centralizer: `C_G(x)^g = C_G(x^g)`.  (Mathlib only has the inclusion
`Subgroup.map_centralizer_le_centralizer_image`; for the conjugation automorphism the inclusion is
an equality.) -/
theorem map_conj_centralizer {G : Type} [Group G] (g x : G) :
    (Subgroup.centralizer ({x} : Set G)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({g * x * g⁻¹} : Set G) := by
  apply le_antisymm
  · have h1 := Subgroup.map_centralizer_le_centralizer_image ({x} : Set G)
      (MulAut.conj g).toMonoidHom
    have himg : (MulAut.conj g).toMonoidHom '' ({x} : Set G) = {g * x * g⁻¹} := by
      ext y
      simp [MulAut.conj_apply]
    rwa [himg] at h1
  · intro y hy
    rw [Subgroup.mem_map]
    refine ⟨g⁻¹ * y * g, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      rw [Subgroup.mem_centralizer_singleton_iff] at hy
      have h := congrArg (fun z => g⁻¹ * z * g) hy
      simpa [mul_assoc] using h
    · change (MulAut.conj g) (g⁻¹ * y * g) = y
      rw [MulAut.conj_apply]
      group

/-- **Bender 1974, §1**, the `|K| = 2` case: every involution `w` has `|C_G(w)| = 4` and there is a
second involution `u ≠ w` commuting with `w` (indeed `C_G(w) ≅ V₄`).

Since all involutions are conjugate (`BSWHyps2` condition (iv)), `w = t^g` for some `g`; conjugation
by `g` is an isomorphism `C_G(t) ≅ C_G(w)` (so `|C_G(w)| = |C_G(t)| = 4`, by
`Work.BSW.Api.card_centralizer_of_card_K_two`), and it sends the involution `s ∈ C_G(t)` to the
involution `u = s^g ∈ C_G(w)`, with `u ≠ w` because `s ∉ K ∋ t`. -/
theorem bswK2Involution {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2) {w : G} (hw : orderOf w = 2) :
    Nat.card ↥(Subgroup.centralizer ({w} : Set G)) = 4 ∧
      (∃ u : G, orderOf u = 2 ∧ u ≠ w ∧ u * w = w * u) := by
  -- condition (iv): `w` is conjugate to `t`.
  obtain ⟨c, hc⟩ := isConj_iff.mp (Work.BSW.involutions_conj h w hw)
  have hwg : w = c⁻¹ * t * c := by
    have h := congrArg (fun z => c⁻¹ * z * c) hc
    simpa [mul_assoc] using h
  -- conjugation by `c⁻¹` identifies `C_G(t)` with `C_G(w)`.
  have hmap : (Subgroup.centralizer ({t} : Set G)).map (MulAut.conj c⁻¹).toMonoidHom =
      Subgroup.centralizer ({w} : Set G) := by
    rw [hwg]
    simpa using map_conj_centralizer (c⁻¹) t
  have hcard : Nat.card ↥(Subgroup.centralizer ({w} : Set G)) = 4 := by
    rw [← hmap, Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective]
    exact Work.BSW.Api.card_centralizer_of_card_K_two h hk
  -- `u = s^g` is the required second involution.
  refine ⟨hcard, c⁻¹ * s * c, ?_, ?_, ?_⟩
  · have h1 : c⁻¹ * s * c = (MulAut.conj c⁻¹) s := by rw [MulAut.conj_apply, inv_inv]
    rw [h1, MulEquiv.orderOf_eq (MulAut.conj c⁻¹) s, Work.BSW.orderOf_s h]
  · intro heq
    rw [hwg] at heq
    have hst : s = t := by
      have h := congrArg (fun z => c * z * c⁻¹) heq
      simpa [mul_assoc] using h
    exact Work.BSW.s_notMem_K h (hst ▸ Work.BSW.t_mem_K h)
  · rw [hwg]
    have hst : s * t = t * s := Work.BSW.s_mul_t_eq_t_mul_s h
    calc (c⁻¹ * s * c) * (c⁻¹ * t * c)
        = c⁻¹ * (s * t) * c := by group
      _ = c⁻¹ * (t * s) * c := by rw [hst]
      _ = (c⁻¹ * t * c) * (c⁻¹ * s * c) := by group

end Work.BSW.Cases
