import Mathlib
import Submission.Work.ZJB2.Defs

/-!
# ZJB2 leaf G4 — `existsConjSylowIn`

Glauberman 1968, p. 1120 (step (IV)): for a `p`-subgroup `U ≤ Y` and a Sylow `p`-subgroup `S`
of `G`, some conjugate `U^x ≤ S` has the property that `Y^x ∩ S` is a Sylow `p`-subgroup of
`Y^x`.

**Route.**  Put `U.subgroupOf Y` into a Sylow `T₀` of `↥Y` (`IsPGroup.exists_le_sylow`); the
image `TY = T₀.map Y.subtype` is then a maximal `p`-subgroup of `Y` (`isSylowIn_map_subtype_of_sylow`).
Extend `TY` to a Sylow `P` of `G`, and conjugate `P` onto `S` by Sylow transitivity.  Then
`Y ⊓ P = TY` by maximality of `TY` in `Y`, so `Y^x ∩ S = (Y ⊓ P)^x = TY^x`, which is Sylow
in `Y^x` because `IsSylowIn` is preserved by injective homomorphisms
(`isSylowIn_map_of_injective`).
-/

open scoped Pointwise

namespace Work.ZJB2

open Work.ZJB

/-- A Mathlib `Sylow p H` is a maximal `p`-subgroup of the whole group `H`, i.e. an
`IsSylowIn p · ⊤`. -/
theorem isSylowIn_top_of_sylow {H : Type*} [Group H] {p : ℕ} (T : Sylow p H) :
    Work.ZJB.IsSylowIn p (T : Subgroup H) ⊤ :=
  ⟨le_top, T.isPGroup', fun _ hTQ _ hQp => T.is_maximal' hQp hTQ⟩

/-- The image of `⊤ : Subgroup ↥M` under the subtype embedding is `M`. -/
theorem map_subtype_top_eq {G : Type*} [Group G] (M : Subgroup G) :
    (⊤ : Subgroup ↥M).map M.subtype = M := by
  ext x; simp [Subgroup.mem_map]

/-- `IsSylowIn` is preserved by an injective homomorphism of the ambient groups. -/
theorem isSylowIn_map_of_injective {p : ℕ} {G H : Type*} [Group G] [Group H]
    {T M : Subgroup G} (h : Work.ZJB.IsSylowIn p T M) {f : G →* H}
    (hf : Function.Injective f) :
    Work.ZJB.IsSylowIn p (T.map f) (M.map f) := by
  refine ⟨Subgroup.map_mono h.1, h.2.1.map f, ?_⟩
  intro Q hTQ hQM hQp
  -- `Q = (Q.comap f).map f` because `Q ≤ M.map f`
  have hQ'map : (Q.comap f).map f = Q := by
    apply le_antisymm
    · rintro q ⟨y, hy, rfl⟩
      exact Subgroup.mem_comap.mp hy
    · intro q hq
      obtain ⟨m, hm, hfm⟩ := Subgroup.mem_map.mp (hQM hq)
      exact ⟨m, Subgroup.mem_comap.mpr (by rw [hfm]; exact hq), hfm⟩
  -- `Q.comap f` is a `p`-subgroup of `M` containing `T`, hence equals `T`
  have key : Q.comap f = T :=
    h.2.2 (Q.comap f)
      (fun t ht => Subgroup.mem_comap.mpr (hTQ (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)))
      (fun y hy => by
        obtain ⟨m, hm, hfm⟩ := Subgroup.mem_map.mp (hQM (Subgroup.mem_comap.mp hy))
        rwa [hf hfm] at hm)
      (hQp.comap_of_injective f hf)
  rw [← hQ'map, key]

/-- A Sylow `p`-subgroup of `↥M`, viewed in `G`, is a maximal `p`-subgroup of `M`. -/
theorem isSylowIn_map_subtype_of_sylow {p : ℕ} {G : Type*} [Group G] (M : Subgroup G)
    (T : Sylow p ↥M) : Work.ZJB.IsSylowIn p ((T : Subgroup ↥M).map M.subtype) M := by
  have h := isSylowIn_map_of_injective (isSylowIn_top_of_sylow T) M.subtype_injective
  rwa [map_subtype_top_eq M] at h

theorem existsConjSylowIn (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Finite G] : Work.ZJB.ExistsConjSylowInProp p G := by
  intro S Y U hUY hUp
  -- `U.subgroupOf Y` is a `p`-subgroup of `↥Y`; take a Sylow `T₀` of `↥Y` containing it.
  have hUp' : IsPGroup p ↥(U.subgroupOf Y) :=
    hUp.of_equiv (Subgroup.subgroupOfEquivOfLe hUY).symm
  obtain ⟨T₀, hUT₀⟩ := hUp'.exists_le_sylow
  set TY : Subgroup G := (T₀ : Subgroup ↥Y).map Y.subtype with hTY
  have hTYsyl : Work.ZJB.IsSylowIn p TY Y := by
    rw [hTY]; exact isSylowIn_map_subtype_of_sylow Y T₀
  -- extend `TY` to a Sylow `P` of `G`
  obtain ⟨P, hTYP⟩ := IsPGroup.exists_le_sylow hTYsyl.2.1
  -- Sylow transitivity: `x • P = S`
  obtain ⟨x, hx⟩ := MulAction.IsPretransitive.exists_smul_eq
    (self := Sylow.isPretransitive_of_finite) P S
  have hφinj : Function.Injective (MulAut.conj x).toMonoidHom := (MulAut.conj x).injective
  have hS : (S : Subgroup G) = (P : Subgroup G).map (MulAut.conj x).toMonoidHom := by
    have h1 := congrArg (fun R : Sylow p G => (R : Subgroup G)) hx
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at h1
    exact h1.symm
  -- `Y ⊓ P = TY` by maximality of `TY` in `Y`
  have hTYle : TY ≤ Y ⊓ (P : Subgroup G) :=
    fun z hz => ⟨Subgroup.map_subtype_le _ hz, hTYP hz⟩
  have hTY_eq : Y ⊓ (P : Subgroup G) = TY :=
    hTYsyl.2.2 (Y ⊓ (P : Subgroup G)) hTYle inf_le_left
      (P.isPGroup'.to_le inf_le_right)
  have hUTY : U ≤ TY := by
    intro u hu
    have hu' : (⟨u, hUY hu⟩ : ↥Y) ∈ U.subgroupOf Y := Subgroup.mem_subgroupOf.mpr hu
    exact Subgroup.mem_map.mpr ⟨⟨u, hUY hu⟩, hUT₀ hu', rfl⟩
  refine ⟨x, ?_, ?_⟩
  · rw [hS]; exact Subgroup.map_mono (le_trans hUTY hTYP)
  · have hYsyl : Work.ZJB.IsSylowIn p (TY.map (MulAut.conj x).toMonoidHom)
        (Y.map (MulAut.conj x).toMonoidHom) :=
      isSylowIn_map_of_injective hTYsyl hφinj
    have hYPS : Y.map (MulAut.conj x).toMonoidHom ⊓ (S : Subgroup G) =
        TY.map (MulAut.conj x).toMonoidHom := by
      rw [hS, ← Subgroup.map_inf Y (P : Subgroup G) (MulAut.conj x).toMonoidHom hφinj, hTY_eq]
    rw [hYPS]; exact hYsyl

end Work.ZJB2
