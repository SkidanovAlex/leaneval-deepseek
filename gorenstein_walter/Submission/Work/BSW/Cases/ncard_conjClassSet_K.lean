import Mathlib
import Submission.Work.BSW.Char.isTISubset_Kdiff
import Submission.Work.BSW.Api.normalizer_K_eq
import Submission.Work.BSW.Api.ncard_involutions_eq_index

namespace Work.BSW.Cases

open Subgroup Work.GW2

/-- Membership in the conjugate `K^g = conjSub g K`: `z ∈ K^g ↔ ∃ k ∈ K, g * k * g⁻¹ = z`. -/
theorem mem_conjSub_K {G : Type} [Group G] {K : Subgroup G} {g z : G} :
    z ∈ Work.GW2.conjSub g K ↔ ∃ k ∈ K, g * k * g⁻¹ = z := by
  rw [Work.GW2.conjSub, Subgroup.mem_map]
  constructor
  · rintro ⟨a, ha, h⟩; exact ⟨a, ha, by rw [← h]; exact MulAut.conj_apply g a⟩
  · rintro ⟨a, ha, h⟩; exact ⟨a, ha, by show (MulAut.conj g) a = z; rw [MulAut.conj_apply]; exact h⟩

/-- The disjointness engine of the counting: if a **nonidentity** element `x ≠ 1` of `K` is
conjugate to another element `y` of `K` (`g * x * g⁻¹ = h * y * h⁻¹`), then `g` and `h` lie in the
same coset of `C_G(t)`. Equivalently — by Bender's TI condition (iii), `K ⊓ K^w = ⊥` for
`w ∉ C_G(t)` — distinct conjugates of `K` meet only in the identity. -/
theorem centralizer_of_conj_eq_mem {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K)
    {g hg x y : G} (hxK : x ∈ K) (hyK : y ∈ K) (hx1 : x ≠ 1)
    (heq : g * x * g⁻¹ = hg * y * hg⁻¹) :
    g⁻¹ * hg ∈ Subgroup.centralizer ({t} : Set G) := by
  by_contra hw
  have hbot : K ⊓ Work.GW2.conjSub (g⁻¹ * hg) K = ⊥ := Work.BSW.TI h (g⁻¹ * hg) hw
  have hxmem : x ∈ (K ⊓ Work.GW2.conjSub (g⁻¹ * hg) K : Subgroup G) := by
    refine ⟨hxK, ?_⟩
    change x ∈ Work.GW2.conjSub (g⁻¹ * hg) K
    rw [mem_conjSub_K]
    refine ⟨y, hyK, ?_⟩
    calc g⁻¹ * hg * y * (g⁻¹ * hg)⁻¹ = g⁻¹ * (hg * y * hg⁻¹) * g := by group
      _ = g⁻¹ * (g * x * g⁻¹) * g := by rw [← heq]
      _ = x := by group
  rw [hbot] at hxmem
  exact hx1 (Subgroup.mem_bot.mp hxmem)

/-- **The count of `𝒞_G(K)`.** In Bender's setting the set `𝒞_G(K)` of `G`-conjugates of the
elements of `K` is the union of the conjugates `K^g` of `K`; distinct conjugates meet only in the
identity (TI condition), and the conjugates are indexed by `G ⧸ N_G(K) = G ⧸ C_G(t)`. Hence
`|𝒞_G(K)| = 1 + [G : C_G(t)]·(|K| - 1) = 1 + #{involutions}·(|K| - 1)`. -/
theorem ncard_conjClassSet_K {G : Type} [Group G] [Finite G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) :
    (OddOrder.GroupTheory.conjClassSet (K : Set G)).ncard =
      Work.BSW.invCount G * (Nat.card ↥K - 1) + 1 := by
  classical
  let C : Subgroup G := Subgroup.centralizer ({t} : Set G)
  have hC : C = Subgroup.normalizer (K : Set G) := (Work.BSW.Api.normalizer_K_eq h).symm
  set E : Set G := OddOrder.GroupTheory.conjClassSet (K : Set G) with hE
  have h1E : (1 : G) ∈ E := by
    rw [hE]; exact OddOrder.GroupTheory.subset_conjClassSet K.one_mem
  -- The bijection `𝒞_G(K) ∖ {1} ≃ (G ⧸ C_G(t)) × (K ∖ {1})`, given by `(c, x) ↦ x^{out c}`.
  have key : Nat.card ((G ⧸ C) × ↥((K : Set G) \ {1})) = (E \ {1}).ncard := by
    rw [← Set.ncard_univ ((G ⧸ C) × ↥((K : Set G) \ {1}))]
    refine Set.ncard_congr
      (s := (Set.univ : Set ((G ⧸ C) × ↥((K : Set G) \ {1}))))
      (t := E \ {1})
      (f := fun (p : (G ⧸ C) × ↥((K : Set G) \ {1})) (_ : p ∈ Set.univ) =>
        p.1.out * (p.2 : G) * p.1.out⁻¹) ?_ ?_ ?_
    · -- the image lies in `𝒞_G(K) ∖ {1}`
      rintro ⟨c, x⟩ _
      rw [Set.mem_sdiff]
      have hx1 : (x : G) ≠ 1 := by simpa using x.2.2
      refine ⟨?_, ?_⟩
      · rw [hE]
        exact ⟨(x : G), x.2.1, c.out, rfl⟩
      · rw [Set.mem_singleton_iff]
        intro hf
        apply hx1
        calc (x : G) = c.out⁻¹ * (c.out * (x : G) * c.out⁻¹) * c.out := by group
          _ = c.out⁻¹ * 1 * c.out := by rw [hf]
          _ = 1 := by group
    · -- injectivity
      rintro ⟨c, x⟩ ⟨d, y⟩ _ _ heq
      have hx1 : (x : G) ≠ 1 := by simpa using x.2.2
      have hmem : c.out⁻¹ * d.out ∈ C :=
        centralizer_of_conj_eq_mem h x.2.1 y.2.1 hx1 heq
      have hcd : c = d := by
        have hq : (c.out : G ⧸ C) = d.out := by
          rw [QuotientGroup.eq]; exact hmem
        rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' d, hq]
      have hout : d.out = c.out := by rw [hcd]
      have hxy : (x : G) = (y : G) := by
        have h2 : c.out * (x : G) * c.out⁻¹ = c.out * (y : G) * c.out⁻¹ := by
          rw [heq, hout]
        calc (x : G) = c.out⁻¹ * (c.out * (x : G) * c.out⁻¹) * c.out := by group
          _ = c.out⁻¹ * (c.out * (y : G) * c.out⁻¹) * c.out := by rw [h2]
          _ = (y : G) := by group
      exact Prod.ext hcd (Subtype.ext hxy)
    · -- surjectivity: every `z ∈ 𝒞_G(K) ∖ {1}` is `x^{out c}` for some `x ∈ K ∖ {1}`
      rintro z hz
      rw [Set.mem_sdiff, Set.mem_singleton_iff] at hz
      obtain ⟨hzE, hz1⟩ := hz
      rw [hE, OddOrder.GroupTheory.mem_conjClassSet] at hzE
      obtain ⟨x, hxK, g, hg⟩ := hzE
      have hx1 : x ≠ 1 := by
        intro hx
        exact hz1 (by rw [← hg, hx]; group)
      let c : G ⧸ C := (g : G ⧸ C)
      let u : G := c.out⁻¹ * g
      have hu : u ∈ C := QuotientGroup.eq.mp (QuotientGroup.out_eq' c)
      have hu' : u ∈ Subgroup.normalizer (K : Set G) := hC ▸ hu
      have hx'K : u * x * u⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hu' x).mp hxK
      have hx'1 : u * x * u⁻¹ ≠ 1 := by
        intro hxx
        apply hx1
        calc x = u⁻¹ * (u * x * u⁻¹) * u := by group
          _ = 1 := by rw [hxx]; group
      refine ⟨(c, ⟨u * x * u⁻¹, ?_⟩), ?_, ?_⟩
      · rw [Set.mem_sdiff]
        exact ⟨hx'K, by simpa using hx'1⟩
      · exact Set.mem_univ _
      · show c.out * (u * x * u⁻¹) * c.out⁻¹ = z
        have e1 : c.out * u = g := by simp only [u]; group
        rw [show c.out * (u * x * u⁻¹) * c.out⁻¹ = (c.out * u) * x * (c.out * u)⁻¹ from by group,
          e1, hg]
  -- the cardinality of the index set `(G ⧸ C_G(t)) × (K ∖ {1})`
  have hcard : Nat.card ((G ⧸ C) × ↥((K : Set G) \ {1}))
      = Work.BSW.invCount G * (Nat.card ↥K - 1) := by
    rw [Nat.card_prod]
    congr 1
    · have h1 : Nat.card (G ⧸ C) = C.index := (Subgroup.index_eq_card C).symm
      rw [h1]
      rw [show C = Subgroup.centralizer ({t} : Set G) from rfl, Work.BSW.invCount]
      exact (Work.BSW.Api.ncard_involutions_eq_index h).symm
    · have e1 : Nat.card ↥((K : Set G) \ {1}) = ((K : Set G) \ {1}).ncard :=
        Nat.card_coe_set_eq ((K : Set G) \ {1})
      have h2 : (K : Set G).ncard = Nat.card ↥K := (Nat.card_coe_set_eq (K : Set G)).symm
      rw [e1, Set.ncard_sdiff (s := ({1} : Set G)) (t := (K : Set G))
          (by intro x hx; rw [Set.mem_singleton_iff] at hx; rw [hx]; exact K.one_mem),
        Set.ncard_singleton, h2]
  -- reassemble `E = {1} ⊔ (E ∖ {1})`
  have hEeq : E = insert (1 : G) (E \ {1}) := by
    rw [Set.insert_sdiff_singleton (s := E) (a := (1 : G))]
    exact (Set.insert_eq_of_mem h1E).symm
  calc E.ncard = (E \ {1}).ncard + 1 := by
        conv_lhs => rw [hEeq]
        rw [Set.ncard_insert_of_notMem (by simp)]
    _ = Work.BSW.invCount G * (Nat.card ↥K - 1) + 1 := by rw [← key, hcard]

end Work.BSW.Cases
