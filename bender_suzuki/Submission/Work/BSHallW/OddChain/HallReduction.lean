import Mathlib
import Submission.Work.BSHallW.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.Prove.HallReductionIndexP` — Peterfalvi II Ch. V §3, step (9): the Hall–Wielandt
reduction inside `N_G(A)`

Let `G` be a finite group, `p` a prime, `S` a Sylow `p`-subgroup, and `A, Z ≤ S` subgroups with
`Z ≤ A`.  Assume

* `N_G(A) ≤ N_G(Z)` (so `Z ⊴ N_G(A)`),
* `[S, S] ≤ Z` (so `S/Z` is abelian),
* `N_G(S) ≤ N_G(A)`,
* `N_G(S)` has a normal subgroup of index `p` containing `Z` (this is input **N4** of the
  surrounding argument, `Prove/step9N4`),

then `N_G(A)` has a normal subgroup of index `p`.

**Idea.**  Write `H = N_G(A)`, `K = Z` viewed inside `H`, and `Q = H/K`.  Since `H ≤ N_G(Z)`
and `[S,S] ≤ Z ≤ S ≤ H`, the image `S̄` of `S` in `Q` is an abelian Sylow `p`-subgroup.  The
abelian-Sylow case of the Hall–Wielandt transfer theorem (`Work.BSHallW.HallWielandtOddProp`
instantiated at the pair `(S̄, S̄)`, weak closure being automatic) gives

  `HasNormalIndexP p Q ↔ HasNormalIndexP p N_Q(S̄)`.

Now `N_Q(S̄) = N_G(S)/Z` because `N_G(S) ≤ N_G(A) = H`, and `N_G(S)/Z` has a normal subgroup of
index `p` by hypothesis.  Pulling the resulting subgroup of `Q` back along `H → Q` finishes the
proof.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

namespace Work.BSHallW.OddChain

open Classical

open Work.ThmF

/-- A subgroup of a finite group is weakly closed in itself: if a conjugate is contained in it,
then the two are equal (conjugation is injective, so the conjugate has the same cardinality). -/
theorem mapConj_eq_self_of_le {G : Type} [Group G] [Finite G] (H : Subgroup G) (g : G)
    (h : H.map (MulAut.conj g).toMonoidHom ≤ H) :
    H.map (MulAut.conj g).toMonoidHom = H := by
  refine Subgroup.eq_of_le_of_card_ge h ?_
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]

/-- The abelian-Sylow case of the Hall–Wielandt transfer theorem, derived from the external input
`HallWielandtOddProp` by applying it to the pair `(P, P)`: an abelian Sylow `p`-subgroup is weakly
closed in itself. -/
theorem abelianSylowHallWielandt_aux {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hHW : Work.BSHallW.HallWielandtOddProp) (P : Sylow p G)
    (hab : ∀ x ∈ (P : Subgroup G), ∀ y ∈ (P : Subgroup G), x * y = y * x) :
    Work.ThmF.HasNormalIndexP p G ↔
      Work.ThmF.HasNormalIndexP p ↥(Subgroup.normalizer (P : Set G)) :=
  hHW G p hp hp2 P (P : Subgroup G) le_rfl
    (fun g hg => mapConj_eq_self_of_le (P : Subgroup G) g hg) hab

/-- The normalizer of the image of `S` in the quotient `G ⧸ K` is the image of the normalizer of
`S` (when `K ≤ S`). -/
theorem normalizerMapQuotient_aux {G : Type} [Group G] {K : Subgroup G} [K.Normal]
    {S : Subgroup G} (hKS : K ≤ S) :
    Subgroup.normalizer ((S.map (QuotientGroup.mk' K)) : Set (G ⧸ K))
      = (Subgroup.normalizer S).map (QuotientGroup.mk' K) := by
  have hf : Function.Surjective (QuotientGroup.mk' K : G →* G ⧸ K) :=
    QuotientGroup.mk'_surjective K
  apply Subgroup.comap_injective hf
  rw [Subgroup.comap_normalizer_eq_of_surjective _ hf]
  have h1 : Subgroup.comap (QuotientGroup.mk' K : G →* G ⧸ K)
      (Subgroup.map (QuotientGroup.mk' K) S) = S := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hKS]
  rw [h1, Subgroup.comap_map_eq, QuotientGroup.ker_mk',
    sup_eq_left.mpr (hKS.trans Subgroup.le_normalizer)]

/-- The image under a quotient map of a subgroup all of whose commutators lie in the kernel is
abelian. -/
theorem mapQuotient_comm {G : Type} [Group G] {K : Subgroup G} [K.Normal] (A : Subgroup G)
    (h : ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ K) :
    ∀ x ∈ A.map (QuotientGroup.mk' K), ∀ y ∈ A.map (QuotientGroup.mk' K), x * y = y * x := by
  rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
  rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement]
  exact (QuotientGroup.eq_one_iff _).mpr (by rw [commutatorElement_def]; exact h a ha b hb)

/-- A normal subgroup of index `p` of a quotient `G ⧸ T` pulls back to a normal subgroup of index
`p` of `G`. -/
theorem hasNormalIndexP_of_quotient {G : Type} [Group G] {p : ℕ} (T : Subgroup G) [T.Normal]
    (h : Work.ThmF.HasNormalIndexP p (G ⧸ T)) : Work.ThmF.HasNormalIndexP p G := by
  obtain ⟨L, hLn, hLi⟩ := h
  exact ⟨L.comap (QuotientGroup.mk' T), hLn.comap (QuotientGroup.mk' T),
    by rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective T)]; exact hLi⟩

theorem HallReductionIndexP {G : Type} [Group G] [Finite G] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hHW : Work.BSHallW.HallWielandtOddProp)
    (S : Sylow p G) (A Z : Subgroup G)
    (hAS : A ≤ (S : Subgroup G)) (hZS : Z ≤ (S : Subgroup G)) (hZA : Z ≤ A)
    (hZnormA : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Z : Set G))
    (hSab : ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * y * x⁻¹ * y⁻¹ ∈ Z)
    (hNSle : Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ Subgroup.normalizer (A : Set G))
    (hM : ∃ M : Subgroup ↥(Subgroup.normalizer ((S : Subgroup G) : Set G)),
        M.Normal ∧ M.index = p ∧ Z.subgroupOf _ ≤ M) :
    HasNormalIndexP p ↥(Subgroup.normalizer (A : Set G)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set H : Subgroup G := Subgroup.normalizer (A : Set G) with hHdef
  -- `S ≤ H`
  have hSH : (S : Subgroup G) ≤ H := by
    rw [hHdef]; exact Subgroup.le_normalizer.trans hNSle
  have hZH : Z ≤ H := hZA.trans (hAS.trans hSH)
  -- `K = Z` inside `H`
  set K : Subgroup ↥H := Z.subgroupOf H with hKdef
  have hKnormal : K.Normal := by
    rw [hKdef, Subgroup.normal_subgroupOf_iff hZH]
    intro x y hx hy
    exact (Subgroup.le_normalizer_iff.mp hZnormA) y hy x hx
  haveI : K.Normal := hKnormal
  -- the Sylow subgroup of the quotient `H ⧸ K`
  set Sq : Sylow p (↥H ⧸ K) :=
    (S.subtype hSH).mapSurjective (QuotientGroup.mk'_surjective K) with hSqdef
  have hSqCoe : (Sq : Subgroup (↥H ⧸ K)) =
      ((S : Subgroup G).subgroupOf H).map (QuotientGroup.mk' K) := by
    rw [hSqdef, Sylow.coe_mapSurjective, Sylow.coe_subtype]
  have hKS' : K ≤ (S : Subgroup G).subgroupOf H := by
    intro x hx
    rw [hKdef, Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_subgroupOf]
    exact hZS hx
  -- `Sq` is abelian
  have hSq_ab : ∀ x ∈ (Sq : Subgroup (↥H ⧸ K)), ∀ y ∈ (Sq : Subgroup (↥H ⧸ K)),
      x * y = y * x := by
    rw [hSqCoe]
    refine mapQuotient_comm _ ?_
    intro a ha b hb
    rw [Subgroup.mem_subgroupOf] at ha hb
    rw [hKdef, Subgroup.mem_subgroupOf]
    simpa using hSab a.1 ha b.1 hb
  -- `Sq` is weakly closed in itself
  have hwc : ∀ g : ↥H ⧸ K, (Sq : Subgroup (↥H ⧸ K)).map (MulAut.conj g).toMonoidHom ≤
      (Sq : Subgroup (↥H ⧸ K)) → (Sq : Subgroup (↥H ⧸ K)).map (MulAut.conj g).toMonoidHom =
      (Sq : Subgroup (↥H ⧸ K)) :=
    fun g hg => mapConj_eq_self_of_le (Sq : Subgroup (↥H ⧸ K)) g hg
  -- Hall–Wielandt in the quotient
  have hiff := hHW (↥H ⧸ K) p hp hp2 Sq (Sq : Subgroup (↥H ⧸ K)) le_rfl hwc hSq_ab
  -- the natural map `V = N_G(S) → H ⧸ K`
  set V : Subgroup G := Subgroup.normalizer ((S : Subgroup G) : Set G) with hVdef
  have hVH : V ≤ H := by rw [hVdef, hHdef]; exact hNSle
  set ψ : ↥V →* (↥H ⧸ K) := (QuotientGroup.mk' K).comp (Subgroup.inclusion hVH) with hψdef
  have hψrange : ψ.range = (V.subgroupOf H).map (QuotientGroup.mk' K) := by
    rw [hψdef, MonoidHom.range_comp, Subgroup.inclusion_range]
  -- the normalizer in the quotient is the image of `V`
  have hNQ : Subgroup.normalizer ((Sq : Subgroup (↥H ⧸ K)) : Set (↥H ⧸ K)) = ψ.range := by
    rw [hψrange, hSqCoe, normalizerMapQuotient_aux hKS',
      ← Subgroup.subgroupOf_normalizer_eq hSH]
  -- `ψ.ker = Z` inside `V`
  obtain ⟨M, hMnorm, hMindex, hMK⟩ := hM
  have hker : ψ.ker = Z.subgroupOf V := by
    ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hv
      have h1 : QuotientGroup.mk' K (Subgroup.inclusion hVH v) = 1 := by
        simpa only [hψdef, MonoidHom.comp_apply] using hv
      have h2 : (Subgroup.inclusion hVH v : ↥H) ∈ K :=
        (QuotientGroup.eq_one_iff _).mp h1
      rw [hKdef, Subgroup.mem_subgroupOf] at h2
      simpa only [Subgroup.coe_inclusion] using h2
    · intro hv
      have h2 : (Subgroup.inclusion hVH v : ↥H) ∈ K := by
        rw [hKdef, Subgroup.mem_subgroupOf]
        simpa only [Subgroup.coe_inclusion] using hv
      have h1 : QuotientGroup.mk' K (Subgroup.inclusion hVH v) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr h2
      simpa only [hψdef, MonoidHom.comp_apply] using h1
  have hker_le_M : ψ.ker ≤ M := by
    rw [hker]; exact hMK
  -- the normal subgroup of index `p` inside `N_Q(Sq)`
  have hHNPSq : HasNormalIndexP p
      ↥(Subgroup.normalizer ((Sq : Subgroup (↥H ⧸ K)) : Set (↥H ⧸ K))) := by
    rw [hNQ]
    refine ⟨M.map ψ.rangeRestrict, hMnorm.map ψ.rangeRestrict
      (MonoidHom.rangeRestrict_surjective ψ), ?_⟩
    rw [Subgroup.index_map_eq M (MonoidHom.rangeRestrict_surjective ψ) ?_]
    · exact hMindex
    · rw [MonoidHom.ker_rangeRestrict]; exact hker_le_M
  have hHNPQ : HasNormalIndexP p (↥H ⧸ K) := hiff.mpr hHNPSq
  exact hasNormalIndexP_of_quotient K hHNPQ

end Work.BSHallW.OddChain
