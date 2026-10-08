import Submission.Work.CORE2B.Defs

/-!
# AREA CORE2B — first API layer for the `Work.GW2` vocabulary

Elementary facts about the vocabulary of `Defs.lean` that the CORE2B leaves (Bender's
Lemmas 2.7–2.9, Theorem 2.10) and the neighbouring CORE areas need.

Nothing here uses `BenderCtx` beyond `BenderSetup_basics`, which unfolds the fields of the
setup structure.  The heavier inputs (`IsQuasisimple` ⇒ `4 ∣ |E|`, `BenderCtx` ⇒ Sylow 2 not
cyclic) are kept in `API2.lean`, which imports the Feit–Thompson closure.
-/

open scoped MatrixGroups

set_option linter.unusedVariables false

namespace Work.CORE2B

open Subgroup

/-! ## Containment in the ambient piece -/

/-- Every relative core `…In K` is contained in `K`.  (All of them are `map`s of subgroups
of `↥K` along `K.subtype`.) -/
theorem in_le_self {G : Type} [Group G] (K : Subgroup G) (p : ℕ) (π : Set ℕ) :
    Work.GW2.oddCoreIn K ≤ K ∧ Work.GW2.pCoreIn p K ≤ K ∧ Work.GW2.fittingIn K ≤ K ∧
      Work.GW2.fittingPiIn π K ≤ K ∧ Work.GW2.layerIn K ≤ K ∧ Work.GW2.fstarIn K ≤ K ∧
      Work.GW2.twoResidualIn K ≤ K := by
  refine ⟨Subgroup.map_subtype_le _, Subgroup.map_subtype_le _, Subgroup.map_subtype_le _,
    Subgroup.map_subtype_le _, Subgroup.map_subtype_le _, ?_, Subgroup.map_subtype_le _⟩
  rw [Work.GW2.fstarIn, Work.GW2.fstar, Subgroup.map_sup]
  exact sup_le (Subgroup.map_subtype_le _) (Subgroup.map_subtype_le _)

/-- `O_p(G) ≤ O(G)` for odd `p`.  (For `p` odd every finite `p`-group has odd order, so
`O_p(G)` is one of the subgroups joined in `O(G)`.) -/
theorem pCore_le_oddCore {G : Type} [Group G] [Finite G] (p : ℕ) (hp : Odd p) :
    Work.GW2.pCore p G ≤ Work.GW2.oddCore G := by
  rw [Work.GW2.pCore, Work.GW2.oddCore]
  refine Subgroup.normalCore_mono ?_
  refine sSup_le ?_
  intro N hN
  refine fun x hx => Subgroup.mem_sSup_of_mem ?_ hx
  refine ⟨hN.1, ?_⟩
  obtain ⟨n, hn⟩ := IsPGroup.exists_card_dvd_pow (G := ↥N) hN.2
  exact Odd.of_dvd_nat (Odd.pow (n := n) hp) hn

/-! ## `invSet` -/

/-- `I_K(s) ⊆ K`. -/
theorem invSet_subset {G : Type} [Group G] (K : Subgroup G) (s : G) :
    Work.GW2.invSet K s ⊆ K := fun _ hx => hx.1

/-- `1 ∈ I_K(s)`. -/
theorem one_mem_invSet {G : Type} [Group G] (K : Subgroup G) (s : G) :
    (1 : G) ∈ Work.GW2.invSet K s := ⟨K.one_mem, by simp⟩

/-! ## Four groups -/

/-- A Klein four-subgroup is commutative, all its elements are involutions, it is nontrivial,
and every element has order `1` or `2`. -/
theorem IsFourGroup_basic {G : Type} [Group G] {V : Subgroup G} (hV : Work.GW2.IsFourGroup V) :
    IsMulCommutative V ∧ (∀ v ∈ V, v⁻¹ = v) ∧ V ≠ ⊥ ∧
      (∀ v ∈ V, orderOf v = 2 ∨ v = 1) := by
  obtain ⟨hcard, hsq⟩ := hV
  have hsq' : ∀ v ∈ V, v * v = 1 := fun v hv => by
    have h := hsq v hv
    rwa [pow_two] at h
  have hcomm : ∀ a b : ↥V, a * b = b * a := by
    intro a b
    apply Subtype.ext
    have hmul : ((a : G) * b) * ((a : G) * b) = 1 :=
      hsq' ((a : G) * b) (V.mul_mem a.2 b.2)
    have hinv : ((a : G) * b)⁻¹ = (a : G) * b := inv_eq_of_mul_eq_one_right hmul
    have ha : (a : G)⁻¹ = a := inv_eq_of_mul_eq_one_right (hsq' (a : G) a.2)
    have hb : (b : G)⁻¹ = b := inv_eq_of_mul_eq_one_right (hsq' (b : G) b.2)
    calc (a : G) * b = ((a : G) * b)⁻¹ := hinv.symm
      _ = (b : G)⁻¹ * (a : G)⁻¹ := mul_inv_rev _ _
      _ = b * a := by rw [ha, hb]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨⟨fun a b : ↥V => hcomm a b⟩⟩
  · intro v hv
    exact inv_eq_of_mul_eq_one_right (hsq' v hv)
  · intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  · intro v hv
    have h2 : orderOf v ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      simpa [pow_two] using hsq' v hv
    rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h | h
    · exact Or.inr (orderOf_eq_one_iff.mp h)
    · exact Or.inl h

/-! ## The 2-residual `O²(G)` -/

/-- `O²(G)` is the smallest subgroup containing all odd-order elements. -/
theorem twoResidual_le_iff {G : Type} [Group G] (H : Subgroup G) :
    Work.GW2.twoResidual G ≤ H ↔ ∀ g : G, Odd (orderOf g) → g ∈ H := by
  rw [Work.GW2.twoResidual, Subgroup.closure_le]
  exact ⟨fun h g hg => h hg, fun h g hg => h g hg⟩

/-- Every odd-order element lies in `O²(G)`. -/
theorem mem_twoResidual_of_odd {G : Type} [Group G] {g : G} (hg : Odd (orderOf g)) :
    g ∈ Work.GW2.twoResidual G :=
  Subgroup.subset_closure hg

/-- The image of an odd-order element of `K` in `O²(K) ⊆ G`. -/
theorem mem_twoResidualIn_of_odd {G : Type} [Group G] {K : Subgroup G} {k : K}
    (hk : Odd (orderOf k)) : (k : G) ∈ Work.GW2.twoResidualIn K :=
  Subgroup.mem_map_of_mem _ (mem_twoResidual_of_odd hk)

/-! ## Unfolding the `BenderSetup` fields -/

/-- The elementary consequences of the definition of `BenderSetup`: `t` lies in `S`, `H`, `Ĥ`,
the cyclic `S₀` lies in `C(t)`, `U ≤ Ĥ`, `Ĥ ≠ ⊤`, and `t` is an involution. -/
theorem BenderSetup_basics {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    B.t ∈ (B.S : Subgroup G) ∧ B.t ∈ B.H ∧ B.t ∈ B.Hhat ∧ B.S0 ≤ B.H ∧ B.U ≤ B.Hhat ∧
      B.Hhat ≠ ⊤ ∧ B.t * B.t = 1 ∧ B.t ≠ 1 := by
  have htS : B.t ∈ (B.S : Subgroup G) := B.S0_le B.t_mem
  have htH : B.t ∈ B.H := by
    rw [Work.GW2.BenderSetup.H, Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rfl
  have htHhat : B.t ∈ B.Hhat := B.H_le_Hhat htH
  have hS0H : B.S0 ≤ B.H := by
    haveI : IsCyclic ↥B.S0 := B.S0_cyclic
    obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := ↥B.S0)
    have hgen : ∀ w : ↥B.S0, ∃ k : ℤ, z ^ k = w := fun w =>
      Subgroup.mem_zpowers_iff.mp (hz w)
    intro x hx
    rw [Work.GW2.BenderSetup.H, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    obtain ⟨i, hi⟩ := hgen ⟨x, hx⟩
    obtain ⟨j, hj⟩ := hgen ⟨B.t, B.t_mem⟩
    have key : (⟨B.t, B.t_mem⟩ : ↥B.S0) * ⟨x, hx⟩ = ⟨x, hx⟩ * ⟨B.t, B.t_mem⟩ := by
      rw [← hj, ← hi, ← zpow_add, ← zpow_add, add_comm]
    exact congrArg (fun w : ↥B.S0 => (w : G)) key
  have hUle : B.U ≤ B.H := Subgroup.map_subtype_le _
  have hUHhat : B.U ≤ B.Hhat := hUle.trans B.H_le_Hhat
  have hne : B.Hhat ≠ ⊤ := B.Hhat_coatom.ne_top
  have ht2 : B.t * B.t = 1 := by
    have h2 : orderOf B.t ∣ 2 := by simp [B.t_order]
    have h : B.t ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.mp h2
    rwa [pow_two] at h
  have ht1 : B.t ≠ 1 := by
    intro h
    have hord := B.t_order
    rw [h, orderOf_one] at hord
    norm_num at hord
  exact ⟨htS, htH, htHhat, hS0H, hUHhat, hne, ht2, ht1⟩

end Work.CORE2B
