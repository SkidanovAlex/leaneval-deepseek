import Mathlib
import Submission.Work.BMAX.Defs
import Submission.Work.BMAX.centralizer_pResidualIn_witness_le

/-!
# BMAX — `A ≤ N_G(O_p(Z(F(A))))`

This file proves

  `Work.BMAX.le_normalizer_pCoreIn_zcenterIn_fittingIn`

i.e. that every subgroup `A ≤ G` normalises the image in `G` of the `p`-core of the centre of
its Fitting subgroup:

  `A ≤ N_G(O_p(Z(F(A))))`.

No primeness of `p` is assumed (the statement of the lemma has an arbitrary `p : ℕ`), so the
argument is phrased in terms of the definition `O_p(M) = (⨆ {N ≤ M | N ⊴ M, IsPGroup p N}).normalCore`
rather than through the library's `opCore`.

## Mathematics

The chain of containments is

  `A ≤ N_G(F(A))`   (`F(A)` is normal in `A`, hence fixed by conjugation with elements of `A`)

  `A ≤ N_G(Z(F(A)))`   (the centre is characteristic in `F(A)`)

  `A ≤ N_G(O_p(Z(F(A))))`   (`O_p` is characteristic in `Z(F(A))`).

The last step is the general fact: if `C ≤ N_G(K)` and `H` is a characteristic subgroup of the
group `↥K`, then `C` normalises the image of `H` in `G`; conjugating by `c ∈ C` induces an
automorphism `φ` of `↥K`, characteristic subgroups are fixed by automorphisms, and
`H.map K.subtype` is `H` transported along the inclusion.

The characteristicity of `O_p` is proved here for arbitrary `p` (it is the join of the *family*
of normal `p`-subgroups, a family invariant under automorphisms, and the normal core of a
characteristic subgroup is characteristic).
-/
set_option linter.style.haveILetI false

namespace Work.BMAX

open Subgroup

/-! ## 1. Characteristic subgroups -/

/-- The normal core of a characteristic subgroup is characteristic. -/
theorem characteristic_normalCore {G : Type} [Group G] {H : Subgroup G}
    (hH : H.Characteristic) : H.normalCore.Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  haveI : (H.normalCore.map φ.toMonoidHom).Normal :=
    Subgroup.Normal.map H.normalCore_normal φ.toMonoidHom φ.surjective
  refine Subgroup.normal_le_normalCore.mpr ?_
  calc H.normalCore.map φ.toMonoidHom ≤ H.map φ.toMonoidHom := Subgroup.map_mono H.normalCore_le
    _ = H := Subgroup.characteristic_iff_map_eq.mp hH φ

/-- The join of all normal `p`-subgroups of a group is characteristic: an automorphism
permutes the family it is the join of. -/
theorem characteristic_sSup_normal_isPGroup {M : Type} [Group M] (p : ℕ) :
    (sSup {N : Subgroup M | N.Normal ∧ IsPGroup p N}).Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro φ
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun N hN x hx => ?_
  rw [Subgroup.mem_comap]
  exact (le_sSup (s := {N : Subgroup M | N.Normal ∧ IsPGroup p N})
    ⟨Subgroup.Normal.map hN.1 φ.toMonoidHom φ.surjective, hN.2.map φ.toMonoidHom⟩)
    (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)

/-- `O_p(M)` is characteristic in `M`, for **every** `p : ℕ` (not only prime `p`). -/
theorem pCore_characteristic_general {M : Type} [Group M] (p : ℕ) :
    (Work.GW2.pCore p M).Characteristic := by
  rw [Work.GW2.pCore]
  exact characteristic_normalCore (characteristic_sSup_normal_isPGroup (M := M) p)

/-! ## 2. Normalizers and characteristic subgroups of a subgroup -/

/-- A subgroup `C` normalising `K` normalises the image in `G` of any subgroup `H` of `↥K`
that is characteristic in `↥K`. -/
theorem le_normalizer_map_subtype_of_characteristic {G : Type} [Group G] {K C : Subgroup G}
    {H : Subgroup ↥K} (hH : H.Characteristic)
    (h : C ≤ Subgroup.normalizer (K : Set G)) :
    C ≤ Subgroup.normalizer ((H.map K.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff] at h ⊢
  intro c hc x hx
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
  -- conjugation by `c` is an automorphism of `↥K`
  let φ : ↥K ≃* ↥K := {
    toFun := fun z => ⟨c * (z : G) * c⁻¹, h c hc z z.2⟩
    invFun := fun z => ⟨c⁻¹ * (z : G) * c, by
      have hh := h c⁻¹ (C.inv_mem hc) z z.2
      rwa [inv_inv] at hh⟩
    left_inv := by intro z; ext; simp [mul_assoc]
    right_inv := by intro z; ext; simp [mul_assoc]
    map_mul' := by intro z w; ext; simp [mul_assoc] }
  refine Subgroup.mem_map.mpr ⟨φ y, ?_, rfl⟩
  exact (Subgroup.characteristic_iff_map_le.mp hH φ) (Subgroup.mem_map.mpr ⟨y, hy, rfl⟩)

/-- `O_p(K)`, pushed into `G` along `K.subtype`, is normalised by every subgroup normalising
`K`. -/
theorem le_normalizer_pCoreIn_of_le_normalizer {G : Type} [Group G] {K C : Subgroup G}
    {p : ℕ} (h : C ≤ Subgroup.normalizer (K : Set G)) :
    C ≤ Subgroup.normalizer ((Work.GW2.pCoreIn p K : Subgroup G) : Set G) :=
  le_normalizer_map_subtype_of_characteristic (pCore_characteristic_general (M := ↥K) p) h

/-! ## 3. The theorem -/

theorem le_normalizer_pCoreIn_zcenterIn_fittingIn {G : Type} [Group G] [Finite G]
    (A : Subgroup G) (p : ℕ) :
    A ≤ Subgroup.normalizer
      ((Work.GW2.pCoreIn p (Work.GW2.zcenterIn (Work.GW2.fittingIn A)) : Subgroup G) : Set G) :=
  le_normalizer_pCoreIn_of_le_normalizer
    (le_normalizer_zcenterIn_of_le_normalizer (le_normalizer_fittingIn A))

end Work.BMAX
