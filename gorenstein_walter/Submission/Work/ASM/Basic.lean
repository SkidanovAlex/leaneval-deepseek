import Submission.Work.ASM.Defs

/-!
# ASM: helper lemmas for the top-level assembly (Mathlib only)

"Plumbing" lemmas of the ASM area: conjugacy of Sylow subgroups, transport of `DShape` data
across the quotient `G ⧸ O(G)`, and elimination of the degenerate cases of `DShape (G ⧸ O(G))`
for a simple non-abelian `G`.
-/

open scoped MatrixGroups Pointwise
open Subgroup

namespace Work.ASM

open Work.GW2

variable {G : Type*} [Group G] [Finite G]

/-! ## Even order from a dihedral Sylow 2-subgroup -/

omit [Finite G] in
/-- A group with a Sylow 2-subgroup isomorphic to `DihedralGroup n` has even order. -/
theorem even_card_of_dihedral_sylow (P : Sylow 2 G) {n : ℕ}
    (h : Nonempty (↥(P : Subgroup G) ≃* DihedralGroup n)) : Even (Nat.card G) := by
  obtain ⟨e⟩ := h
  have hcard : Nat.card ↥(P : Subgroup G) = 2 * n := by
    rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  rw [even_iff_two_dvd, ← Subgroup.card_mul_index (P : Subgroup G), hcard]
  exact dvd_mul_of_dvd_left (dvd_mul_right 2 n) _

/-! ## Conjugation of subgroups -/

omit [Finite G] in
/-- Conjugating a subgroup by `g` is the pointwise action of `MulAut.conj g`. -/
theorem map_conj_eq_smul (K : Subgroup G) (g : G) :
    K.map ((MulAut.conj g : MulAut G) : G →* G) = MulAut.conj g • K := by
  rw [Subgroup.pointwise_smul_def]
  congr 1

/-- The conjugated subgroup is isomorphic to the original. -/
noncomputable def conjMulEquiv (K : Subgroup G) (g : G) :
    ↥K ≃* ↥(MulAut.conj g • K) :=
  (MulEquiv.subgroupMap (MulAut.conj g) K).trans
    (MulEquiv.subgroupCongr (by
      rw [Subgroup.pointwise_smul_def]
      congr 1))

/-- `¬ IsMulCommutative` transfers along a `MulEquiv`. -/
theorem not_isMulCommutative_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : ¬ IsMulCommutative G) : ¬ IsMulCommutative H := fun hH =>
  h ⟨⟨fun a b => e.injective (by rw [map_mul, map_mul, @mul_comm' H _ hH (e a) (e b)])⟩⟩

/-! ## `DihOrCycSylow` from one dihedral Sylow 2-subgroup -/

/-- If one Sylow 2-subgroup is dihedral, all Sylow 2-subgroups are dihedral up to isomorphism,
so `DihOrCycSylow` holds. -/
theorem dihOrCycSylow_of_dihedral (P : Sylow 2 G) {n : ℕ}
    (h : Nonempty (↥(P : Subgroup G) ≃* DihedralGroup n)) : DihOrCycSylow G := by
  intro Q
  obtain ⟨e⟩ := h
  obtain ⟨g, hg⟩ : ∃ g : G, g • Q = P := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : MulAction.IsPretransitive G (Sylow 2 G) :=
      Sylow.isPretransitive_of_finite (p := 2) (G := G)
    exact MulAction.IsPretransitive.exists_smul_eq Q P
  have hmap : (Q : Subgroup G).map ((MulAut.conj g : MulAut G) : G →* G) = (P : Subgroup G) := by
    rw [map_conj_eq_smul, ← Sylow.coe_subgroup_smul, hg]
  refine Or.inr ⟨n, ⟨?_⟩⟩
  exact (MulEquiv.subgroupMap (MulAut.conj g) (Q : Subgroup G)).trans (hmap ▸ e)

/-! ## The quotient by `O(G)` when `O(G) = ⊥` -/

/-- If `O(G) = ⊥` then `G ⧸ O(G) ≃* G`. -/
noncomputable def quotientOddCoreEquiv (h : oddCore G = ⊥) : (G ⧸ oddCore G) ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot

/-! ## Normal subgroups of a quotient of a simple group -/

omit [Finite G] in
/-- Every normal subgroup of a quotient of a simple group is trivial or the whole group. -/
theorem normal_eq_bot_or_top_of_quotient [IsSimpleGroup G] (N : Subgroup G) [N.Normal]
    (K : Subgroup (G ⧸ N)) (hK : K.Normal) : K = ⊥ ∨ K = ⊤ := by
  have hkey : K = (K.comap (QuotientGroup.mk' N)).map (QuotientGroup.mk' N) := by
    rw [Subgroup.map_comap_eq, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective N),
      top_inf_eq]
  rcases Subgroup.Normal.eq_bot_or_eq_top (K.comap (QuotientGroup.mk' N)) with h | h
  · left
    rw [hkey, h, Subgroup.map_bot]
  · right
    rw [hkey, h, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective N)]

/-! ## Lattice: coatoms above a proper subgroup -/

/-- Every proper subgroup of a finite group is contained in a maximal one. -/
theorem exists_coatom_ge_of_ne_top (H : Subgroup G) (h : H ≠ ⊤) :
    ∃ K : Subgroup G, IsCoatom K ∧ H ≤ K := by
  rcases IsCoatomic.eq_top_or_exists_le_coatom H with h1 | h2
  · exact absurd h1 h
  · exact h2

/-! ## Commutativity helpers -/

theorem not_isMulCommutative_of_exists_mul_ne {H : Type*} [Group H]
    (h : ∃ a b : H, a * b ≠ b * a) : ¬ IsMulCommutative H := fun hc => by
  obtain ⟨a, b, hab⟩ := h
  exact hab (@mul_comm' H _ hc a b)

/-- A group all of whose elements have order dividing two is commutative. -/
theorem isMulCommutative_of_forall_sq_eq_one {H : Type*} [Group H]
    (h : ∀ x : H, x ^ 2 = 1) : IsMulCommutative H := by
  refine IsMulCommutative.of_comm fun a b => ?_
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h a)
  have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h b)
  have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using h (a * b))
  rw [← hab, mul_inv_rev, ha, hb]

/-! ## Elimination of the degenerate `DShape` cases -/

/-- If `G ⧸ O(G)` is a 2-group, then a simple non-abelian `G` with `O(G) = ⊥` cannot occur. -/
theorem false_of_isPGroup_oddCore_quotient [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hodd : oddCore G = ⊥)
    (hpg : IsPGroup 2 (G ⧸ oddCore G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hpg
  rw [hodd] at hk
  have hcard : Nat.card G = 2 ^ k := by
    rw [← Nat.card_congr (QuotientGroup.quotientBot (G := G)).toEquiv]
    exact hk
  have hPG : IsPGroup 2 G := IsPGroup.iff_card.mpr ⟨k, hcard⟩
  have hne : Subgroup.center G ≠ ⊥ := by
    intro hbot
    have hsub : Subsingleton (Subgroup.center G) := by
      rw [hbot]
      infer_instance
    obtain ⟨x, y, hxy⟩ := (IsPGroup.center_nontrivial hPG).exists_pair_ne
    exact hxy (hsub.elim x y)
  have htop : Subgroup.center G = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with h' | h'
    · exact absurd h' hne
    · exact h'
  obtain ⟨a, b, hab⟩ := hnonab
  refine hab ?_
  have ha : a ∈ Subgroup.center G := by rw [htop]; trivial
  exact ((Subgroup.mem_center_iff.mp ha) b).symm

omit [Finite G] in
/-- The Klein-four clause of `DShape` cannot hold for `G ⧸ O(G)` with `G` simple non-abelian
and `O(G) = ⊥`. -/
theorem false_of_fourGroup_oddCore_quotient [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (hodd : oddCore G = ⊥)
    (V : Subgroup (G ⧸ oddCore G)) (hVn : V.Normal) (hV4 : IsFourGroup V) : False := by
  rcases normal_eq_bot_or_top_of_quotient (oddCore G) V hVn with hbot | htop
  · have h1 : Nat.card V = 1 := by rw [hbot]; exact Subgroup.card_bot
    have h4 := hV4.1
    omega
  · have hQab : IsMulCommutative (G ⧸ oddCore G) := by
      refine isMulCommutative_of_forall_sq_eq_one fun x => ?_
      exact hV4.2 x (by rw [htop]; trivial)
    obtain ⟨a, b, hab⟩ := hnonab
    have e : G ≃* (G ⧸ oddCore G) := (quotientOddCoreEquiv (G := G) hodd).symm
    refine hab (e.injective ?_)
    rw [map_mul, map_mul]
    exact @mul_comm' (G ⧸ oddCore G) _ hQab (e a) (e b)

omit [Finite G] in
/-- A non-abelian simple group is not solvable. -/
theorem false_of_solvable_simple [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (h : Group.IsSolvable G) : False := by
  obtain ⟨a, b, hab⟩ := hnonab
  exact hab ((IsSimpleGroup.comm_iff_isSolvable (G := G)).mpr h a b)

end Work.ASM
