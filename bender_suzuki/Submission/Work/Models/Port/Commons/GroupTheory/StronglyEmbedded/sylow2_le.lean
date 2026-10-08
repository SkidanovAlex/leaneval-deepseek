import Mathlib.GroupTheory.Nilpotent

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Commons.GroupTheory.StronglyEmbedded

/-- In a finite `p`-group, every proper subgroup is properly contained in its normalizer. -/
lemma pGroup_normalizer_grows {p : ℕ} [Fact p.Prime] {H : Type*} [Group H] [Finite H]
    (hH : IsPGroup p H) {S : Subgroup H} (hS : S < ⊤) :
    ∃ g : H, g ∈ Subgroup.normalizer (S : Set H) ∧ g ∉ S := by
  haveI : Group.IsNilpotent H := hH.isNilpotent
  have hnc : NormalizerCondition H := Group.normalizerCondition_of_isNilpotent (G := H)
  have hlt : S < Subgroup.normalizer (S : Set H) := hnc S hS
  by_contra h
  have hle : Subgroup.normalizer (S : Set H) ≤ S := by
    intro g hg
    by_contra hgS
    exact h ⟨g, hg, hgS⟩
  have : S = Subgroup.normalizer (S : Set H) := le_antisymm hlt.le hle
  exact hlt.ne this

/-- If a proper subgroup `M` of the finite group `G` has even order and meets every one
of its conjugates (by elements outside `M`) in an odd-order subgroup, then some Sylow
2-subgroup of `G` lies inside `M`.

Proof sketch: pick an element `t ∈ M` of order two (Cauchy), extend the subgroup it
generates to a Sylow 2-subgroup `P` of `G`, and assume `P ⊄ M`.  Then `S := P ∩ M`
is a proper subgroup of the 2-group `P`, hence properly contained in its normalizer
inside `P`; taking `y ∈ N_P(S) \ S`, we get `y ∉ M`, while `S ≤ M ∩ M^y`, forcing
`M ∩ M^y` to have even order — contradicting the hypothesis. -/
theorem sylow2_le {G : Type*} [Group G] [Finite G] (M : Subgroup G)
    (hM : M ≠ ⊤) (hEven : Even (Nat.card M))
    (hOdd : ∀ g : G, g ∉ M → Odd (Nat.card ((M ⊓ M.map (MulAut.conj g).toMonoidHom : Subgroup G)))) :
    ∃ P : Sylow 2 G, (P : Subgroup G) ≤ M := by
  classical
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  by_contra hno
  have hnotle : ∀ P : Sylow 2 G, ¬ (P : Subgroup G) ≤ M := by
    intro P hP
    exact hno ⟨P, hP⟩
  have h2dvd : 2 ∣ Nat.card M := even_iff_two_dvd.mp hEven
  obtain ⟨t0, ht0⟩ := exists_prime_orderOf_dvd_card' (G := M) 2 h2dvd
  let t : G := (t0 : G)
  have htM : t ∈ M := t0.2
  have ht2 : orderOf t = 2 := by
    simpa [t] using (Subgroup.orderOf_coe (H := M) t0).trans ht0
  let Q : Subgroup G := Subgroup.zpowers t
  have hQpg : IsPGroup 2 Q := by
    refine IsPGroup.of_card (p := 2) (n := 1) ?_
    dsimp [Q]
    rw [Nat.card_zpowers, ht2]
  have hQleM : Q ≤ M := by
    dsimp [Q]
    exact Subgroup.zpowers_le.mpr htM
  obtain ⟨R, hQR⟩ := IsPGroup.exists_le_sylow (P := Q) hQpg
  have hRnotle : ¬ (R : Subgroup G) ≤ M := hnotle R
  let S : Subgroup G := (R : Subgroup G) ⊓ M
  have hSleM : S ≤ M := inf_le_right
  have hSleR : S ≤ (R : Subgroup G) := inf_le_left
  have hSneR : S ≠ (R : Subgroup G) := by
    intro hEq
    apply hRnotle
    intro x hx
    have hxS : x ∈ S := by
      rw [hEq]
      exact hx
    exact hSleM hxS
  have hSltR : S < (R : Subgroup G) := lt_of_le_of_ne hSleR hSneR
  let S₀ : Subgroup (R : Subgroup G) := S.subgroupOf (R : Subgroup G)
  have hS₀lt : S₀ < ⊤ := by
    refine lt_of_le_of_ne le_top ?_
    intro htop
    apply hSneR
    apply le_antisymm hSleR
    intro x hx
    have hxS₀ : (⟨x, hx⟩ : (R : Subgroup G)) ∈ S₀ := by
      rw [htop]
      trivial
    exact Subgroup.mem_subgroupOf.mp hxS₀
  have hRpg : IsPGroup 2 (R : Subgroup G) := by
    simpa using R.isPGroup'
  obtain ⟨y0, hyN0, hyS0⟩ := pGroup_normalizer_grows (H := (R : Subgroup G)) hRpg hS₀lt
  let y : G := (y0 : G)
  have hyP : y ∈ (R : Subgroup G) := y0.2
  have hbr : (Subgroup.normalizer (S : Set G)).subgroupOf (R : Subgroup G) =
      Subgroup.normalizer (S₀ : Set (R : Subgroup G)) := by
    simpa [S₀] using (Subgroup.subgroupOf_normalizer_eq (H := S) (N := (R : Subgroup G)) hSleR)
  have hyN' : y0 ∈ (Subgroup.normalizer (S : Set G)).subgroupOf (R : Subgroup G) := by
    simpa [hbr] using hyN0
  have hyN : y ∈ Subgroup.normalizer (S : Set G) := Subgroup.mem_subgroupOf.mp hyN'
  have hyS : y ∉ S := by
    intro hy
    apply hyS0
    exact Subgroup.mem_subgroupOf.mpr hy
  have hyM : y ∉ M := by
    intro hy
    apply hyS
    dsimp [S]
    exact ⟨hyP, hy⟩
  have htQ : t ∈ Q := Subgroup.mem_zpowers t
  have htR : t ∈ (R : Subgroup G) := hQR htQ
  have htS : t ∈ S := by
    dsimp [S]
    exact ⟨htR, htM⟩
  have hyN'' : t ∈ (S : Set G) ↔ y⁻¹ * t * y ∈ (S : Set G) :=
    (Subgroup.mem_set_normalizer_iff''.mp hyN) t
  have hmS : y⁻¹ * t * y ∈ S := hyN''.mp htS
  have hmM : y⁻¹ * t * y ∈ M := hSleM hmS
  let conj : Subgroup G := M.map (MulAut.conj y).toMonoidHom
  have htConj : t ∈ conj := by
    dsimp [conj]
    refine ⟨y⁻¹ * t * y, hmM, ?_⟩
    simp
    group
  have htint : t ∈ (M ⊓ conj : Subgroup G) := ⟨htM, htConj⟩
  have hoddY : Odd (Nat.card (M ⊓ conj : Subgroup G)) := by
    simpa [conj] using hOdd y hyM
  have hdiv : 2 ∣ Nat.card (M ⊓ conj : Subgroup G) := by
    have hd := Subgroup.orderOf_dvd_natCard (M ⊓ conj : Subgroup G) htint
    simpa [ht2] using hd
  exact (Nat.not_even_iff_odd.mpr hoddY) (even_iff_two_dvd.mpr hdiv)

end Commons.GroupTheory.StronglyEmbedded