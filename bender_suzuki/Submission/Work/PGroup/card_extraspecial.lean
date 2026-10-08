import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.center_eq_commutator_of_isExtraspecial

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The order of an extraspecial `p`-group

An extraspecial `p`-group `E` (FT §2: a non-abelian special `p`-group with centre of order `p`)
has order `p ^ (2 * n + 1)` for some `n ≥ 1`.

For a group `H` of nilpotency class at most two whose centre `Z` has order the prime `p`, the
commutator map descends to a non-degenerate alternating pairing `H/Z × H/Z → Z ≅ C_p` on the
elementary abelian group `H/Z`.  A non-degenerate alternating form on a finite dimensional space
has even dimension, so `|H : Z|` is a square and `|H| = p · p ^ (2m) = p ^ (2m+1)`.

This is proved below by strong induction on `|H|` (`card_eq_pow_odd_aux`): the induction step
passes to the kernel of the map `h ↦ (⁅h, x⁆, ⁅h, y⁆) : H → Z × Z`, which has index `p ^ 2`
because `x ∉ Z` can be paired with a `y` with `⁅x, y⁆ ≠ 1`, so that `⁅·, x⁆` and `⁅·, y⁆` are
independent and `H` is the product of this kernel with `⟨x, y⟩ Z`.

The extraspecial case is then a translation of the invariants of `E ≤ G` (stated inside `G` as
`centerIn E = ⁅E, E⁆` and `Nat.card (centerIn E) = p`) to the group `↥E` itself.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped Classical Pointwise commutatorElement
open Subgroup

namespace Work.PGroup

section Bridge

variable {G : Type*} [Group G] {p : ℕ}

/-- For an extraspecial `p`-subgroup `E ≤ G`, the centre of the group `↥E` is its derived
subgroup.  This is the translation to `↥E` of the defining equality `centerIn E = ⁅E, E⁆`. -/
theorem center_subtype_eq_commutator (E : Subgroup G) [Finite E]
    (hE : IsExtraspecial p E) : Subgroup.center ↥E = ⁅(⊤ : Subgroup ↥E), ⊤⁆ := by
  refine Subgroup.map_injective E.subtype_injective ?_
  rw [Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
  exact center_eq_commutator_of_isExtraspecial E hE

/-- For an extraspecial `p`-subgroup `E ≤ G` the centre of the group `↥E` has order `p`. -/
theorem card_center_subtype (E : Subgroup G) [Finite E] (hE : IsExtraspecial p E) :
    Nat.card (Subgroup.center ↥E) = p := by
  rw [← Subgroup.card_map_of_injective (f := E.subtype) E.subtype_injective]
  exact hE.2.2

end Bridge

section Abstract

/-- `h ↦ ⁅h, y⁆` as a homomorphism into a subgroup `Z` containing all commutators. -/
private def commutatorHomRight {H : Type*} [Group H] (Z : Subgroup H) (hZc : Z ≤ Subgroup.center H)
    (hcomm : ∀ a b : H, ⁅a, b⁆ ∈ Z) (y : H) : H →* Z where
  toFun h := ⟨⁅h, y⁆, hcomm h y⟩
  map_one' := by ext; simp
  map_mul' := by
    intro a b
    ext
    show ⁅a * b, y⁆ = ⁅a, y⁆ * ⁅b, y⁆
    have hb : ⁅b, y⁆ ∈ Subgroup.center H := hZc (hcomm b y)
    have ha : ⁅a, y⁆ ∈ Subgroup.center H := hZc (hcomm a y)
    rw [commutatorElement_mul_left_eq_conj_mul]
    have h1 : a * ⁅b, y⁆ * a⁻¹ = ⁅b, y⁆ := by
      rw [Subgroup.mem_center_iff.mp hb a]; group
    rw [h1, Subgroup.mem_center_iff.mp ha ⁅b, y⁆]

/-- `h ↦ ⁅x, h⁆` as a homomorphism into a subgroup `Z` containing all commutators. -/
private def commutatorHomLeft {H : Type*} [Group H] (Z : Subgroup H) (hZc : Z ≤ Subgroup.center H)
    (hcomm : ∀ a b : H, ⁅a, b⁆ ∈ Z) (x : H) : H →* Z where
  toFun h := ⟨⁅x, h⁆, hcomm x h⟩
  map_one' := by ext; simp
  map_mul' := by
    intro a b
    ext
    show ⁅x, a * b⁆ = ⁅x, a⁆ * ⁅x, b⁆
    have hb : ⁅x, b⁆ ∈ Subgroup.center H := hZc (hcomm x b)
    rw [commutatorElement_mul_right_eq_mul_conj]
    have h1 : a * ⁅x, b⁆ * a⁻¹ = ⁅x, b⁆ := by
      rw [Subgroup.mem_center_iff.mp hb a]; group
    rw [show ⁅x, a⁆ * a * ⁅x, b⁆ * a⁻¹ = ⁅x, a⁆ * (a * ⁅x, b⁆ * a⁻¹) from by group, h1]

private theorem card_eq_pow_odd_aux (p : ℕ) (hp : p.Prime) :
    ∀ n : ℕ, ∀ (H : Type*) [Group H] [Finite H] (Z : Subgroup H),
      (hZc : Z ≤ Subgroup.center H) → (hZcard : Nat.card Z = p) →
      (hcomm : ⁅(⊤ : Subgroup H), ⊤⁆ ≤ Z) → (hnd : Subgroup.center H ≤ Z) →
      Nat.card H = n → ∃ m : ℕ, Nat.card H = p ^ (2 * m + 1) := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro H _ _ Z hZc hZcard hcomm hnd hcardn
    have hcommpt : ∀ a b : H, ⁅a, b⁆ ∈ Z :=
      fun a b => Subgroup.commutator_le.mp hcomm a trivial b trivial
    by_cases htop : Z = ⊤
    · refine ⟨0, ?_⟩
      have hp' : Nat.card H = p := by
        rw [← Subgroup.card_top (G := H), ← htop, hZcard]
      rw [hp']
      norm_num
    · obtain ⟨x, hxZ⟩ : ∃ x : H, x ∉ Z := by
        by_contra hcon
        push Not at hcon
        exact htop (le_antisymm le_top fun y _ => hcon y)
      have hxcenter : x ∉ Subgroup.center H := fun hc => hxZ (hnd hc)
      have hex : ∃ y : H, ⁅x, y⁆ ≠ 1 := by
        by_contra hcon
        push Not at hcon
        exact hxcenter (Subgroup.mem_center_iff.mpr fun g =>
          (commutatorElement_eq_one_iff_mul_comm.mp (hcon g)).symm)
      obtain ⟨y, hy⟩ := hex
      set z : Z := ⟨⁅x, y⁆, hcommpt x y⟩ with hzdef
      have hz1 : z ≠ 1 := by
        rw [hzdef]
        intro hc
        exact hy (Subtype.ext_iff.mp hc)
      let φx : H →* Z := commutatorHomRight Z hZc hcommpt x
      let φy : H →* Z := commutatorHomRight Z hZc hcommpt y
      let φ : H →* Z × Z := φx.prod φy
      have hφx : φ x = (1, z) := by
        ext <;> simp [φ, φx, φy, hzdef, commutatorHomRight]
      have hφy : φ y = (z⁻¹, 1) := by
        ext <;> simp [φ, φx, φy, hzdef, commutatorHomRight, commutatorElement_inv]
      -- the subgroup generated by the two images is everything
      have hgen : Subgroup.closure ({(1, z), (z⁻¹, 1)} : Set (Z × Z)) = ⊤ := by
        haveI : Fact p.Prime := ⟨hp⟩
        have hzp : z ^ p = 1 := by
          have h := orderOf_dvd_natCard z
          rw [hZcard] at h
          exact orderOf_dvd_iff_pow_eq_one.mp h
        have hord : orderOf z = p := orderOf_eq_prime hzp hz1
        have hz : Subgroup.zpowers z = ⊤ := by
          refine Subgroup.eq_top_of_card_eq (Subgroup.zpowers z) ?_
          rw [Nat.card_zpowers, hord, hZcard]
        refine eq_top_iff.mpr fun uv _ => ?_
        obtain ⟨u, v⟩ := uv
        have hu : u ∈ Subgroup.zpowers z := by rw [hz]; trivial
        have hv : v ∈ Subgroup.zpowers z := by rw [hz]; trivial
        rw [Subgroup.mem_zpowers_iff] at hu hv
        obtain ⟨m1, hm1⟩ := hu
        obtain ⟨m2, hm2⟩ := hv
        have hmem1 : ((z⁻¹, 1) : Z × Z) ∈ Subgroup.closure ({(1, z), (z⁻¹, 1)} : Set (Z × Z)) :=
          Subgroup.subset_closure (by simp)
        have hmem2 : ((1, z) : Z × Z) ∈ Subgroup.closure ({(1, z), (z⁻¹, 1)} : Set (Z × Z)) :=
          Subgroup.subset_closure (by simp)
        have heq : ((z⁻¹, 1) : Z × Z) ^ (-m1) * ((1, z) : Z × Z) ^ m2 = ((u, v) : Z × Z) := by
          simp only [← hm1, ← hm2]
          ext <;> simp
        rw [← heq]
        exact mul_mem (Subgroup.zpow_mem _ hmem1 _) (Subgroup.zpow_mem _ hmem2 _)
      have hrange : φ.range = ⊤ := by
        refine eq_top_iff.mpr ?_
        rw [← hgen]
        refine (Subgroup.closure_le φ.range).mpr ?_
        intro w hw
        rcases hw with rfl | rfl
        · exact ⟨x, hφx⟩
        · exact ⟨y, hφy⟩
      -- for every `h` there is `w` in `⟨x, y⟩` with the same image under `φ`
      have hsurj : ∀ h : H, ∃ w ∈ Subgroup.closure ({x, y} : Set H), φ w = φ h := by
        intro h
        have hmap : Subgroup.map φ (Subgroup.closure ({x, y} : Set H)) = ⊤ := by
          rw [MonoidHom.map_closure]
          have himg : (φ '' ({x, y} : Set H)) = ({(1, z), (z⁻¹, 1)} : Set (Z × Z)) := by
            ext w
            constructor
            · rintro ⟨h', hh', rfl⟩
              rcases hh' with rfl | rfl
              · exact Or.inl hφx
              · exact Or.inr hφy
            · rintro (rfl | rfl)
              · exact ⟨x, Or.inl rfl, hφx⟩
              · exact ⟨y, Or.inr rfl, hφy⟩
          rw [himg, hgen]
        have hmem : φ h ∈ Subgroup.map φ (Subgroup.closure ({x, y} : Set H)) := by
          rw [hmap]; trivial
        rw [Subgroup.mem_map] at hmem
        obtain ⟨w, hw, hφw⟩ := hmem
        exact ⟨w, hw, hφw⟩
      -- `Z` lies in the kernel of `φ`
      have hZleC : Z ≤ φ.ker := by
        intro u hu
        rw [MonoidHom.mem_ker]
        have hx1 : ⁅u, x⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
          ((Subgroup.mem_center_iff.mp (hZc hu) x).symm)
        have hy1 : ⁅u, y⁆ = 1 := commutatorElement_eq_one_iff_mul_comm.mpr
          ((Subgroup.mem_center_iff.mp (hZc hu) y).symm)
        have e1 : φx u = 1 := Subtype.ext hx1
        have e2 : φy u = 1 := Subtype.ext hy1
        show (φx u, φy u) = (1 : Z × Z)
        rw [e1, e2]
        rfl
      have hZcard' : Nat.card (Z.subgroupOf φ.ker) = p := by
        have hmap : Subgroup.map φ.ker.subtype (Z.subgroupOf φ.ker) = Z := by
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hZleC]
        rw [← Subgroup.card_map_of_injective φ.ker.subtype_injective, hmap, hZcard]
      have hZc' : Z.subgroupOf φ.ker ≤ Subgroup.center ↥φ.ker := by
        intro u hu
        rw [Subgroup.mem_center_iff]
        intro v
        ext
        exact Subgroup.mem_center_iff.mp (hZc (Subgroup.mem_subgroupOf.mp hu)) (v : H)
      have hcomm'' : ⁅(⊤ : Subgroup ↥φ.ker), ⊤⁆ ≤ Z.subgroupOf φ.ker := by
        rw [Subgroup.commutator_le]
        intro u _ v _
        rw [Subgroup.mem_subgroupOf]
        exact Subgroup.commutator_le.mp hcomm (u : H) trivial (v : H) trivial
      have hnd' : Subgroup.center ↥φ.ker ≤ Z.subgroupOf φ.ker := by
        intro a ha
        rw [Subgroup.mem_subgroupOf]
        apply hnd
        rw [Subgroup.mem_center_iff]
        intro h
        have hφxa : φx (a : H) = 1 := by
          have h := congrArg Prod.fst (MonoidHom.mem_ker.mp a.2)
          simpa [φ] using h
        have hφya : φy (a : H) = 1 := by
          have h := congrArg Prod.snd (MonoidHom.mem_ker.mp a.2)
          simpa [φ] using h
        have hkerle : φ.ker ≤ (commutatorHomLeft Z hZc hcommpt (a : H)).ker := by
          intro c hc
          rw [MonoidHom.mem_ker]
          have hacomm : ⁅(a : H), (c : H)⁆ = 1 := by
            have h := Subgroup.mem_center_iff.mp ha (⟨c, hc⟩ : ↥φ.ker)
            exact commutatorElement_eq_one_iff_mul_comm.mpr (Subtype.ext_iff.mp h.symm)
          exact Subtype.ext hacomm
        have hxψ : x ∈ (commutatorHomLeft Z hZc hcommpt (a : H)).ker := by
          rw [MonoidHom.mem_ker]
          exact Subtype.ext (Subtype.ext_iff.mp hφxa)
        have hyψ : y ∈ (commutatorHomLeft Z hZc hcommpt (a : H)).ker := by
          rw [MonoidHom.mem_ker]
          exact Subtype.ext (Subtype.ext_iff.mp hφya)
        obtain ⟨w, hw, hφw⟩ := hsurj h
        have hψw : (commutatorHomLeft Z hZc hcommpt (a : H)) w = 1 := by
          have hle : Subgroup.closure ({x, y} : Set H) ≤ (commutatorHomLeft Z hZc hcommpt (a : H)).ker := by
            refine (Subgroup.closure_le _).mpr ?_
            intro u hu
            rcases hu with rfl | rfl
            · exact hxψ
            · exact hyψ
          exact MonoidHom.mem_ker.mp (hle hw)
        have hw1 : w⁻¹ * h ∈ (commutatorHomLeft Z hZc hcommpt (a : H)).ker := by
          apply hkerle
          rw [MonoidHom.mem_ker, map_mul, map_inv, hφw]
          group
        have hψh : (commutatorHomLeft Z hZc hcommpt (a : H)) h = 1 := by
          have h2 : (commutatorHomLeft Z hZc hcommpt (a : H)) (w * (w⁻¹ * h)) = 1 := by
            rw [map_mul, hψw, MonoidHom.mem_ker.mp hw1, mul_one]
          rwa [mul_inv_cancel_left] at h2
        exact (commutatorElement_eq_one_iff_mul_comm.mp (Subtype.ext_iff.mp hψh)).symm
      have hcard : Nat.card H = Nat.card ↥φ.ker * p ^ 2 := by
        have h1 : Nat.card ↥φ.ker * φ.ker.index = Nat.card H := Subgroup.card_mul_index φ.ker
        rw [Subgroup.index_eq_card] at h1
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv] at h1
        have h2 : Nat.card ↥φ.range = p ^ 2 := by
          rw [hrange, Subgroup.card_top, Nat.card_prod, hZcard, pow_two]
        rw [← h1, h2]
      have hkerlt : Nat.card ↥φ.ker < n := by
        rw [← hcardn, hcard]
        calc Nat.card ↥φ.ker = Nat.card ↥φ.ker * 1 := (mul_one _).symm
          _ < Nat.card ↥φ.ker * p ^ 2 :=
              Nat.mul_lt_mul_of_pos_left (by nlinarith [hp.two_le, Nat.card_pos (α := ↥φ.ker)]) Nat.card_pos
      obtain ⟨m, hm⟩ := ih (Nat.card ↥φ.ker) hkerlt ↥φ.ker (Z.subgroupOf φ.ker)
        hZc' hZcard' hcomm'' hnd' rfl
      refine ⟨m + 1, ?_⟩
      calc Nat.card H = Nat.card ↥φ.ker * p ^ 2 := hcard
        _ = p ^ (2 * m + 1) * p ^ 2 := by rw [hm]
        _ = p ^ (2 * m + 1 + 2) := (pow_add p (2 * m + 1) 2).symm
        _ = p ^ (2 * (m + 1) + 1) := by rw [show 2 * m + 1 + 2 = 2 * (m + 1) + 1 by omega]

/-- **The order of a finite group of nilpotency class at most two with centre of prime order.**
For a finite group `H` with `Z ≤ Z(H)` of order the prime `p`, `[H, H] ≤ Z` and `Z(H) ≤ Z`
(so that `Z = Z(H)`), the order of `H` is an odd power of `p`. -/
private theorem card_eq_pow_odd_of_central_subgroup_aux {H : Type*} [Group H] [Finite H] {p : ℕ}
    (hp : p.Prime) (Z : Subgroup H) (hZc : Z ≤ Subgroup.center H) (hZcard : Nat.card Z = p)
    (hcomm : ⁅(⊤ : Subgroup H), ⊤⁆ ≤ Z) (hnd : Subgroup.center H ≤ Z) :
    ∃ m : ℕ, Nat.card H = p ^ (2 * m + 1) :=
  card_eq_pow_odd_aux p hp (Nat.card H) H Z hZc hZcard hcomm hnd rfl

end Abstract

/-- **The order of an extraspecial `p`-group is `p ^ (2 * n + 1)` with `n ≥ 1`.** -/
theorem card_extraspecial {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) (E : Subgroup G)
    [Finite E] (hE : Work.PGroup.IsExtraspecial p E) :
    ∃ n : ℕ, 1 ≤ n ∧ Nat.card E = p ^ (2 * n + 1) := by
  have hZcard : Nat.card (Subgroup.center ↥E) = p := card_center_subtype E hE
  have hcenter : Subgroup.center ↥E = ⁅(⊤ : Subgroup ↥E), ⊤⁆ := center_subtype_eq_commutator E hE
  have hcomm : ⁅(⊤ : Subgroup ↥E), ⊤⁆ ≤ Subgroup.center ↥E := hcenter ▸ le_rfl
  have hnd : Subgroup.center ↥E ≤ Subgroup.center ↥E := le_rfl
  obtain ⟨m, hm⟩ :=
    card_eq_pow_odd_of_central_subgroup_aux hp (Subgroup.center ↥E) le_rfl hZcard hcomm hnd
  have hne : ¬ IsMulCommutative ↥E := hE.1
  have hcenterlt : Subgroup.center ↥E < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    exact hne (Subgroup.center_eq_top_iff.mp htop)
  have hlt : p < Nat.card ↥E := by
    have h := Subgroup.card_lt_of_lt hcenterlt
    rwa [hZcard, Subgroup.card_top] at h
  have hm1 : 1 ≤ m := by
    have hp1 : 1 < p := hp.one_lt
    have h2 : p ^ 1 < p ^ (2 * m + 1) := by rw [pow_one, ← hm]; exact hlt
    have := (Nat.pow_lt_pow_iff_right hp1).mp h2
    omega
  exact ⟨m, hm1, hm⟩

end Work.PGroup
