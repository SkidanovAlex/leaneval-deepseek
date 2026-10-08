/-
Copyright (c) 2024. All rights reserved.

# The layer count forces exponent `2` on `P ⧸ Z(P)`

Let `V` be a finite group of order `q ^ 2` (`q = 2 ^ n`) carrying an automorphism `σ` of order
`q - 1` acting fixed-point-freely on `V ∖ {1}`.  If there are at least `q + 1` `σ`-invariant
subgroups of `V` of order `q` ("layers"), then every element of `V` is an involution.

Indeed `σ` acts with all orbits of size `q - 1`, each layer `N` has `N ∖ {1}` equal to a single
`σ`-orbit, distinct layers have disjoint non-identity parts, and the `σ`-orbit of an involution
consists of involutions; since `q` is a power of two every layer is a non-trivial `2`-group and so
contains an involution, whence all of `N ∖ {1}` consists of involutions.  Counting the disjoint
layer parts against `|V| - 1 = q ^ 2 - 1` gives at most `q + 1` layers, so the hypothesis
`q + 1 ≤ #layers` forces the layer parts to cover `V ∖ {1}`; every non-identity element then lies
in a layer and has order `2`.
-/

import Mathlib
import Submission.Work.Higman.BS.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace Work.Higman

/-- The `φ`-invariant subgroups of order `q`. -/
abbrev LayerMul (V : Type) [Group V] (q : ℕ) (φ : MulAut V) : Type _ :=
  {N : Subgroup V // (∀ v ∈ N, φ v ∈ N) ∧ Nat.card N = q}

theorem layer_elementary_aux {V : Type} [Group V] [Finite V] (q : ℕ) (σ : MulAut V)
    (hcardV : Nat.card V = q ^ 2) (hq2 : 2 ≤ q) (hq2pow : ∃ n : ℕ, q = 2 ^ n)
    (hord : orderOf σ = q - 1)
    (hfpf : ∀ k : ℕ, σ ^ k ≠ 1 → ∀ v : V, (σ ^ k) v = v → v = 1)
    (hN : q + 1 ≤ Nat.card (LayerMul V q σ)) :
    ∀ v : V, v ^ 2 = 1 := by
  classical
  letI : Fintype V := Fintype.ofFinite V
  -- ## powers of `σ` applied to a point
  have hpow_apply : ∀ (a b : ℕ) (y : V), (σ ^ a) ((σ ^ b) y) = (σ ^ (a + b)) y := by
    intro a b y
    rw [← MulAut.mul_apply, ← pow_add]
  -- ## injectivity of `i ↦ σ ^ i x` on `range (orderOf σ)`
  have hkey : ∀ x : V, x ≠ 1 → ∀ i j : ℕ, i ≤ j → j < orderOf σ →
      (σ ^ i) x = (σ ^ j) x → i = j := by
    intro x hx i j hij hj heq
    have hsub : (σ ^ (j - i)) x = x := by
      refine (σ ^ i).injective ?_
      rw [hpow_apply, Nat.add_sub_of_le hij, heq]
    rcases Nat.eq_zero_or_pos (j - i) with h0 | hpos
    · omega
    · exfalso
      have hlt : j - i < orderOf σ := lt_of_le_of_lt (Nat.sub_le j i) hj
      by_cases hc : σ ^ (j - i) = 1
      · obtain ⟨c, hc'⟩ := orderOf_dvd_iff_pow_eq_one.mpr hc
        rw [hord] at hc'
        have hc1 : 1 ≤ c := by
          rcases Nat.eq_zero_or_pos c with h0 | h
          · rw [h0, mul_zero] at hc'; omega
          · exact h
        nlinarith [hpos, hlt, hc1]
      · exact hx (hfpf (j - i) hc x hsub)
  -- ## the `σ`-orbit of a point, as a finite set
  set orb : V → Finset V := fun x => (Finset.range (orderOf σ)).image (fun i => (σ ^ i) x)
    with horbdef
  have horb_card : ∀ x : V, x ≠ 1 → (orb x).card = q - 1 := by
    intro x hx
    rw [horbdef, Finset.card_image_of_injOn ?_, Finset.card_range, hord]
    intro i hi j hj hij
    rw [Finset.mem_coe, Finset.mem_range] at hi hj
    rcases le_total i j with hle | hle
    · exact hkey x hx i j hle hj hij
    · exact (hkey x hx j i hle hi hij.symm).symm
  have horb_one_not : ∀ x : V, x ≠ 1 → (1 : V) ∉ orb x := by
    intro x hx
    rw [horbdef]
    simp only [Finset.mem_image, Finset.mem_range]
    rintro ⟨i, -, hi⟩
    have h2 : x = 1 := by
      have h3 := congrArg (fun y => (σ ^ i)⁻¹ y) hi
      simpa using h3
    exact hx h2
  have hpow_mem : ∀ (N : Subgroup V) (hNin : ∀ v ∈ N, σ v ∈ N) (i : ℕ) {x : V},
      x ∈ N → (σ ^ i) x ∈ N := by
    intro N hNin i x hx
    induction i with
    | zero => simpa using hx
    | succ i ih => rw [pow_succ', MulAut.mul_apply]; exact hNin _ ih
  have horb_sub : ∀ (N : Subgroup V) (hNin : ∀ v ∈ N, σ v ∈ N) {x : V}, x ∈ N →
      orb x ⊆ (N : Set V).toFinset := by
    intro N hNin x hx y hy
    rw [Set.mem_toFinset]
    rw [horbdef] at hy
    simp only [Finset.mem_image, Finset.mem_range] at hy
    obtain ⟨i, -, rfl⟩ := hy
    exact hpow_mem N hNin i hx
  -- ## the non-identity part of a layer is a single orbit
  have hpart_eq : ∀ N : LayerMul V q σ, ∀ x ∈ N.1, x ≠ 1 →
      (N.1 : Set V).toFinset = insert (1 : V) (orb x) := by
    intro N x hx hx1
    have hcardN : ((N.1 : Set V).toFinset).card = q := by
      rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
      exact N.2.2
    have hsub : orb x ⊆ (N.1 : Set V).toFinset := horb_sub N.1 N.2.1 hx
    have hnot : (1 : V) ∉ orb x := horb_one_not x hx1
    have hIns : insert (1 : V) (orb x) ⊆ (N.1 : Set V).toFinset := by
      intro y hy
      rw [Finset.mem_insert] at hy
      rcases hy with rfl | hy
      · rw [Set.mem_toFinset]; exact N.1.one_mem
      · exact hsub hy
    have hcard_ins : (insert (1 : V) (orb x)).card = ((N.1 : Set V).toFinset).card := by
      rw [Finset.card_insert_of_notMem hnot, horb_card x hx1, hcardN,
        Nat.sub_add_cancel (by omega : 1 ≤ q)]
    exact (Finset.eq_of_subset_of_card_le hIns (le_of_eq hcard_ins.symm)).symm
  -- ## distinct layers have disjoint non-identity parts
  set parts : LayerMul V q σ → Finset V := fun N => ((N.1 : Set V).toFinset).erase 1
    with hpartsdef
  have hparts_card : ∀ N : LayerMul V q σ, (parts N).card = q - 1 := by
    intro N
    have h1 : (1 : V) ∈ (N.1 : Set V).toFinset := by
      rw [Set.mem_toFinset]; exact N.1.one_mem
    rw [hpartsdef, Finset.card_erase_of_mem h1, Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact congrArg (· - 1) N.2.2
  have hmem_parts : ∀ (N : LayerMul V q σ) {x : V}, x ∈ parts N ↔ x ∈ N.1 ∧ x ≠ 1 := by
    intro N x
    rw [hpartsdef, Finset.mem_erase, Set.mem_toFinset]
    exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
  have hdisj : ∀ N N' : LayerMul V q σ, N ≠ N' → Disjoint (parts N) (parts N') := by
    intro N N' hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    have hxN : x ∈ N.1 ∧ x ≠ 1 := (hmem_parts N).mp hx
    have hxN' : x ∈ N'.1 ∧ x ≠ 1 := (hmem_parts N').mp hx'
    have h1 : (N.1 : Set V).toFinset = insert (1 : V) (orb x) := hpart_eq N x hxN.1 hxN.2
    have h2 : (N'.1 : Set V).toFinset = insert (1 : V) (orb x) := hpart_eq N' x hxN'.1 hxN'.2
    refine hne (Subtype.ext ?_)
    have h3 : (N.1 : Set V).toFinset = (N'.1 : Set V).toFinset := by rw [h1, h2]
    have hset : (N.1 : Set V) = (N'.1 : Set V) := Set.toFinset_inj.mp h3
    refine SetLike.ext ?_
    intro y
    exact iff_of_eq (congrArg (fun s : Set V => y ∈ s) hset)
  -- ## counting: at most `q + 1` layers
  have hmul' : (q + 1) * (q - 1) + 1 = q ^ 2 := by
    have h2 : q - 1 + 1 = q := Nat.sub_add_cancel (by omega : 1 ≤ q)
    nlinarith [h2]
  have hmul : (q + 1) * (q - 1) = q ^ 2 - 1 := by
    rw [← hmul']
    omega
  have hcard_erase : (Finset.univ.erase (1 : V)).card = q ^ 2 - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ 1), Finset.card_univ,
      ← Nat.card_eq_fintype_card, hcardV]
  have hle : Nat.card (LayerMul V q σ) * (q - 1) ≤ q ^ 2 - 1 := by
    have hbu := Finset.card_biUnion (s := (Finset.univ : Finset (LayerMul V q σ)))
      (t := parts) (fun N _ N' _ hne => hdisj N N' hne)
    rw [Finset.sum_congr rfl (fun N _ => hparts_card N), Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, smul_eq_mul] at hbu
    rw [← hbu, ← hcard_erase]
    refine Finset.card_le_card ?_
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨N, -, hxN⟩ := hx
    have h1 : x ∈ N.1 ∧ x ≠ 1 := (hmem_parts N).mp hxN
    rw [Finset.mem_erase]
    exact ⟨h1.2, Finset.mem_univ x⟩
  -- ## every non-identity element lies in a layer
  have hcover : ∀ v : V, v ≠ 1 → ∃ N : LayerMul V q σ, v ∈ N.1 := by
    intro v hv
    have hge : q ^ 2 - 1 ≤ Nat.card (LayerMul V q σ) * (q - 1) := by
      have h1 : (q + 1) * (q - 1) ≤ Nat.card (LayerMul V q σ) * (q - 1) :=
        Nat.mul_le_mul_right _ hN
      rwa [hmul] at h1
    have heq : Nat.card (LayerMul V q σ) * (q - 1) = q ^ 2 - 1 := le_antisymm hle hge
    have hbu := Finset.card_biUnion (s := (Finset.univ : Finset (LayerMul V q σ)))
      (t := parts) (fun N _ N' _ hne => hdisj N N' hne)
    rw [Finset.sum_congr rfl (fun N _ => hparts_card N), Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, smul_eq_mul, heq, ← hcard_erase] at hbu
    have hsub : (Finset.univ.biUnion parts) ⊆ Finset.univ.erase (1 : V) := by
      intro x hx
      rw [Finset.mem_biUnion] at hx
      obtain ⟨N, -, hxN⟩ := hx
      rw [Finset.mem_erase]
      exact ⟨((hmem_parts N).mp hxN).2, Finset.mem_univ x⟩
    have heq2 : (Finset.univ.biUnion parts) = Finset.univ.erase (1 : V) :=
      Finset.eq_of_subset_of_card_le hsub (le_of_eq hbu.symm)
    have hv' : v ∈ Finset.univ.biUnion parts := by rw [heq2]; simpa using hv
    rw [Finset.mem_biUnion] at hv'
    obtain ⟨N, -, hvN⟩ := hv'
    exact ⟨N, ((hmem_parts N).mp hvN).1⟩
  -- ## conclusion
  intro v
  rcases eq_or_ne v 1 with rfl | hv
  · simp
  · obtain ⟨N, hvN⟩ := hcover v hv
    obtain ⟨n, hn⟩ := hq2pow
    have hnpos : 0 < n := by
      rcases Nat.eq_zero_or_pos n with h0 | hpos
      · rw [h0, pow_zero] at hn; omega
      · exact hpos
    have h2dvd : 2 ∣ Nat.card ↥(N.1) := by
      rw [N.2.2, hn]
      exact dvd_pow_self 2 (by omega : n ≠ 0)
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2dvd
    have hz2' : z ^ 2 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
    have hz2 : ((z : ↥(N.1)) : V) ^ 2 = 1 := by
      rw [← Subgroup.coe_pow]
      exact congrArg Subtype.val hz2'
    have hz1 : ((z : ↥(N.1)) : V) ≠ 1 := by
      intro hcon
      have h1 : orderOf z = 1 := by
        have h2 : orderOf ((z : ↥(N.1)) : V) = 1 := by rw [hcon]; exact orderOf_one
        rwa [Subgroup.orderOf_coe] at h2
      omega
    have ho : (N.1 : Set V).toFinset = insert (1 : V) (orb ((z : ↥(N.1)) : V)) :=
      hpart_eq N _ z.2 hz1
    have hvz : v ∈ orb ((z : ↥(N.1)) : V) := by
      have h1 : v ∈ insert (1 : V) (orb ((z : ↥(N.1)) : V)) := by
        rw [← ho, Set.mem_toFinset]; exact hvN
      rcases Finset.mem_insert.mp h1 with h | h
      · exact absurd h hv
      · exact h
    rw [horbdef] at hvz
    simp only [Finset.mem_image, Finset.mem_range] at hvz
    obtain ⟨i, -, hi⟩ := hvz
    rw [← hi, ← map_pow, hz2, map_one]

end Work.Higman

namespace Work.Higman

section Instance

variable {P : Type} [Group P] [Finite P]

/-- **`P ⧸ Z(P)` is elementary abelian when the layer count is `≥ q + 1`.**
Instantiation of `layer_elementary_aux` at `V = P ⧸ Z(P)`. -/
theorem quotCenter_isElementary_aux (h : IsSuzuki2Grp P) {ξ : MulAut P} (hξ : FpfXi ξ)
    (hfpf : ∀ k : ℕ, ξ ^ k ≠ 1 → ∀ v : P ⧸ Subgroup.center P,
      ((quotCenterAut ξ) ^ k) v = v → v = 1)
    (hN : Nat.card ↥(Subgroup.center P) + 1 ≤
      Nat.card (LayerMul (P ⧸ Subgroup.center P) (Nat.card ↥(Subgroup.center P))
        (quotCenterAut ξ))) :
    ∀ v : P ⧸ Subgroup.center P, v ^ 2 = 1 := by
  set q := Nat.card ↥(Subgroup.center P) with hqdef
  have hcard_quot : Nat.card (P ⧸ Subgroup.center P) * q = Nat.card P := by
    rw [hqdef, ← Subgroup.index_eq_card, Subgroup.index_mul_card]
  have hcardV : Nat.card (P ⧸ Subgroup.center P) = q ^ 2 := by
    have hpos : 0 < q := by rw [hqdef]; exact Nat.card_pos
    have h3 : Nat.card (P ⧸ Subgroup.center P) * q = q ^ 2 * q := by
      rw [hcard_quot, hξ.card_cube]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos h3
  have hq2 : 2 ≤ q := by
    have h4 : 4 ≤ Nat.card (omega1 P) := h.omega1_card_ge_four
    have h5 : Nat.card (omega1 P) ≤ Nat.card ↥(Subgroup.center P) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion (h.omega1_le_center))
        (Subgroup.inclusion_injective _)
    rw [hqdef]; omega
  have hq2pow : ∃ n : ℕ, q = 2 ^ n := by
    rw [hqdef]
    exact (IsPGroup.iff_card).mp (h.isPGroup.to_subgroup (Subgroup.center P))
  have hqc : orderOf (quotCenterAut ξ) = orderOf ξ := by
    refine Nat.dvd_antisymm ?_ ?_
    · rw [orderOf_dvd_iff_pow_eq_one, quotCenterAut_pow_eq_one_iff h hξ]
      exact pow_orderOf_eq_one ξ
    · rw [orderOf_dvd_iff_pow_eq_one, ← quotCenterAut_pow_eq_one_iff h hξ]
      exact pow_orderOf_eq_one _
  have hord : orderOf (quotCenterAut ξ) = q - 1 := by rw [hqc, hξ.order, hqdef]
  have hfpf' : ∀ k : ℕ, (quotCenterAut ξ) ^ k ≠ 1 →
      ∀ v : P ⧸ Subgroup.center P, ((quotCenterAut ξ) ^ k) v = v → v = 1 := by
    intro k hk v hv
    exact hfpf k (fun hcon => hk ((quotCenterAut_pow_eq_one_iff h hξ k).mpr hcon)) v hv
  exact layer_elementary_aux q (quotCenterAut ξ) hcardV hq2 hq2pow hord hfpf' hN

end Instance

end Work.Higman
