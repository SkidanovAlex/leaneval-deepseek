import Mathlib

namespace Work.A7REC.Char

/-- Two `G`-conjugates of a subgroup `U` coincide exactly when the conjugating elements differ
by an element of the normalizer of `U`. -/
lemma map_conj_eq_iff {G : Type*} [Group G] (U : Subgroup G) (x y : G) :
    U.map (MulAut.conj x).toMonoidHom = U.map (MulAut.conj y).toMonoidHom ↔
      x⁻¹ * y ∈ Subgroup.normalizer (U : Set G) := by
  have comp_eq : ∀ a b : G,
      (MulAut.conj a).toMonoidHom.comp (MulAut.conj b).toMonoidHom =
        (MulAut.conj (a * b)).toMonoidHom := by
    intro a b
    ext u
    simp [MulAut.conj_apply, mul_assoc]
  have hone : (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G := by
    rw [MulAut.conj.map_one]; rfl
  constructor
  · intro h
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h' := congrArg (fun K : Subgroup G => K.map (MulAut.conj x⁻¹).toMonoidHom) h
    have hx : (U.map (MulAut.conj x).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom = U := by
      rw [Subgroup.map_map, comp_eq, inv_mul_cancel, hone, Subgroup.map_id]
    have hy : (U.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom
        = U.map (MulAut.conj (x⁻¹ * y)).toMonoidHom := by
      rw [Subgroup.map_map, comp_eq]
    rw [hx, hy] at h'
    exact h'.symm
  · intro h
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at h
    have step : (U.map (MulAut.conj (x⁻¹ * y)).toMonoidHom).map (MulAut.conj x).toMonoidHom
        = U.map (MulAut.conj x).toMonoidHom :=
      congrArg (fun K : Subgroup G => K.map (MulAut.conj x).toMonoidHom) h
    rw [← step, Subgroup.map_map, comp_eq, mul_inv_cancel_left]

/-- The number of distinct `T`-conjugates of `U` times the size of `T ∩ N_G(U)` equals `|T|`
(orbit–stabilizer for the conjugation action of `T` on the subgroup lattice of `G`). -/
theorem ncard_range_conj_mul_card_inf_normalizer {G : Type*} [Group G] [Finite G] (U T : Subgroup G) :
    (Set.range (fun t : ↥T => U.map (MulAut.conj (t : G)).toMonoidHom)).ncard *
      Nat.card ↥(T ⊓ Subgroup.normalizer (U : Set G)) = Nat.card ↥T := by
  let f : ↥T → Subgroup G := fun t => U.map (MulAut.conj (t : G)).toMonoidHom
  let K : Subgroup ↥T := (T ⊓ Subgroup.normalizer (U : Set G)).subgroupOf T
  have hHle : T ⊓ Subgroup.normalizer (U : Set G) ≤ T := inf_le_left
  -- The fibers of `f` are the cosets of `K`.
  have hkey : ∀ t₁ t₂ : ↥T, f t₁ = f t₂ ↔ (QuotientGroup.leftRel K) t₁ t₂ := by
    intro t₁ t₂
    rw [QuotientGroup.leftRel_apply]
    constructor
    · intro h
      have h' := (map_conj_eq_iff U (t₁ : G) (t₂ : G)).mp h
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      refine ⟨?_, ?_⟩
      · have : ((t₁⁻¹ * t₂ : ↥T) : G) = (t₁ : G)⁻¹ * (t₂ : G) := by simp
        rw [this]
        exact T.mul_mem (T.inv_mem t₁.2) t₂.2
      · have : ((t₁⁻¹ * t₂ : ↥T) : G) = (t₁ : G)⁻¹ * (t₂ : G) := by simp
        rw [this]; exact h'
    · intro h
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at h
      refine (map_conj_eq_iff U (t₁ : G) (t₂ : G)).mpr ?_
      have : ((t₁⁻¹ * t₂ : ↥T) : G) = (t₁ : G)⁻¹ * (t₂ : G) := by simp
      rw [← this]; exact h.2
  -- Hence `f` factors through the quotient `T ⧸ K`, injectively.
  let F : ↥T ⧸ K → Subgroup G := fun q => Quotient.liftOn q f (fun a b hab => (hkey a b).mpr hab)
  have hF : ∀ t : ↥T, F (QuotientGroup.mk t) = f t := by
    intro t
    exact Quotient.liftOn_mk f _ t
  have hrange : Set.range f = Set.range F := by
    have h1 : Set.range (F ∘ (QuotientGroup.mk : ↥T → ↥T ⧸ K)) = Set.range F :=
      QuotientGroup.mk_surjective.range_comp F
    have h2 : (F ∘ (QuotientGroup.mk : ↥T → ↥T ⧸ K)) = f := funext (fun t => hF t)
    rw [h2] at h1
    exact h1
  have hFinj : Function.Injective F := by
    intro q₁ q₂ hq
    obtain ⟨t₁, rfl⟩ := QuotientGroup.mk_surjective q₁
    obtain ⟨t₂, rfl⟩ := QuotientGroup.mk_surjective q₂
    rw [hF, hF] at hq
    exact Quotient.sound ((hkey t₁ t₂).mp hq)
  have hcard_range : (Set.range f).ncard = K.index := by
    rw [hrange, Set.ncard_range_of_injective hFinj]
    rfl
  have hcardK : Nat.card ↥K = Nat.card ↥(T ⊓ Subgroup.normalizer (U : Set G)) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHle).toEquiv
  change (Set.range f).ncard * Nat.card ↥(T ⊓ Subgroup.normalizer (U : Set G)) = Nat.card ↥T
  rw [hcard_range, ← hcardK, mul_comm]
  exact K.card_mul_index

end Work.A7REC.Char
