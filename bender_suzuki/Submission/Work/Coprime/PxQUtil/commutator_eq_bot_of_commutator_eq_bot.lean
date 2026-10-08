/-
The "rotation" symmetry of the two-sided condition `[Q, [P, G]] = 1` for two *commuting* groups of
automorphisms `P`, `Q` of a group `G`.

Both `FT.commutator P ⊤` and `FT.commutator Q ⊤` are abstract commutators of an operator group with
a subgroup of `G`; to compare them we embed everything into the semidirect product
`Γ = G ⋊ (P × Q)`, where the two actions combine into the action of the product (they commute by
`SMulCommClass`).  Inside `Γ` the statement becomes the classical **three subgroups lemma**
(Hall–Witt): the inclusion `⁅⁅G, P⁆, Q⁆ = 1` together with the commuting of `P` and `Q` yields
`⁅⁅G, Q⁆, P⁆ = 1`.
-/
import Mathlib
import Submission.Work.Coprime.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise
open scoped commutatorElement

namespace Work.Coprime.PxQUtil

variable {P Q G : Type*} [Group P] [Group Q] [Group G]
  [MulDistribMulAction P G] [MulDistribMulAction Q G] [SMulCommClass P Q G]

/-- The action homomorphism `P × Q →* MulAut G` obtained from two commuting actions of `P` and `Q`
on `G` (`(p, q) • g = p • (q • g)`). -/
private def pxqActionHom (P Q G : Type*) [Group P] [Group Q] [Group G]
    [MulDistribMulAction P G] [MulDistribMulAction Q G] [SMulCommClass P Q G] :
    (P × Q) →* MulAut G where
  toFun pq := MulDistribMulAction.toMulAut P G pq.1 * MulDistribMulAction.toMulAut Q G pq.2
  map_one' := by ext g; simp
  map_mul' pq rs := by
    obtain ⟨p1, q1⟩ := pq; obtain ⟨p2, q2⟩ := rs; ext g
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, MulAut.mul_apply,
      MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]
    rw [smul_comm p2 q1 (q2 • g)]

/-- The semidirect product `G ⋊ (P × Q)` for the combined action. -/
private abbrev PxQ (P Q G : Type*) [Group P] [Group Q] [Group G]
    [MulDistribMulAction P G] [MulDistribMulAction Q G] [SMulCommClass P Q G] : Type _ :=
  SemidirectProduct G (P × Q) (pxqActionHom P Q G)

/-- The embedding `G ↪ G ⋊ (P × Q)`. -/
private abbrev inlG (P Q G : Type*) [Group P] [Group Q] [Group G]
    [MulDistribMulAction P G] [MulDistribMulAction Q G] [SMulCommClass P Q G] :
    G →* PxQ P Q G := SemidirectProduct.inl (N := G) (G := P × Q) (φ := pxqActionHom P Q G)

/-- The embedding `P × Q ↪ G ⋊ (P × Q)`. -/
private abbrev inrPQ (P Q G : Type*) [Group P] [Group Q] [Group G]
    [MulDistribMulAction P G] [MulDistribMulAction Q G] [SMulCommClass P Q G] :
    (P × Q) →* PxQ P Q G := SemidirectProduct.inr (N := G) (G := P × Q) (φ := pxqActionHom P Q G)

/-- The copy of `P` inside `G ⋊ (P × Q)`. -/
private abbrev Psub (P Q G : Type*) [Group P] [Group Q] [Group G]
    [MulDistribMulAction P G] [MulDistribMulAction Q G] [SMulCommClass P Q G] :
    Subgroup (PxQ P Q G) := ((inrPQ P Q G).comp (MonoidHom.inl P Q)).range

/-- The copy of `Q` inside `G ⋊ (P × Q)`. -/
private abbrev Qsub (P Q G : Type*) [Group P] [Group Q] [Group G]
    [MulDistribMulAction P G] [MulDistribMulAction Q G] [SMulCommClass P Q G] :
    Subgroup (PxQ P Q G) := ((inrPQ P Q G).comp (MonoidHom.inr P Q)).range

/-- The copy of `G` inside `G ⋊ (P × Q)`. -/
private abbrev Gsub (P Q G : Type*) [Group P] [Group Q] [Group G]
    [MulDistribMulAction P G] [MulDistribMulAction Q G] [SMulCommClass P Q G] :
    Subgroup (PxQ P Q G) := (inlG P Q G).range

private lemma pxq_inl (p : P) (g : G) : pxqActionHom P Q G ((MonoidHom.inl P Q) p) g = p • g := by
  rw [MonoidHom.inl_apply]
  simp [pxqActionHom, MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]

private lemma pxq_inr (q : Q) (g : G) : pxqActionHom P Q G ((MonoidHom.inr P Q) q) g = q • g := by
  rw [MonoidHom.inr_apply]
  simp [pxqActionHom, MulDistribMulAction.toMulAut_apply, MulDistribMulAction.toMulEquiv_apply]

private lemma inlG_aut (m : P × Q) (g : G) :
    inlG P Q G (pxqActionHom P Q G m g) = inrPQ P Q G m * inlG P Q G g * (inrPQ P Q G m)⁻¹ := by
  simpa only [map_inv] using
    SemidirectProduct.inl_aut (N := G) (G := P × Q) (φ := pxqActionHom P Q G) m g

/-- The abstract commutator `[H, A]` (for `A` acting on `G` through a homomorphism `j` into
`P × Q`) maps, under `G ↪ G ⋊ (P × Q)`, to the subgroup commutator `⁅H, A⁆` inside the semidirect
product. -/
private lemma map_inl_commutator {A : Type*} [Group A] [MulDistribMulAction A G]
    (j : A →* (P × Q)) (hj : ∀ (a : A) (g : G), a • g = pxqActionHom P Q G (j a) g)
    (H : Subgroup G) :
    (FT.commutator A H).map (inlG P Q G)
      = ⁅H.map (inlG P Q G), ((inrPQ P Q G).comp j).range⁆ := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine FT.commutator_le ?_
    intro a x hx
    rw [Subgroup.mem_comap]
    have hv : inrPQ P Q G (j a) ∈ ((inrPQ P Q G).comp j).range :=
      MonoidHom.mem_range.mpr ⟨a, rfl⟩
    have hx1 : inlG P Q G x ∈ H.map (inlG P Q G) := Subgroup.mem_map_of_mem (inlG P Q G) hx
    have hkey : inlG P Q G (x⁻¹ * (a • x)) = ⁅(inlG P Q G x)⁻¹, inrPQ P Q G (j a)⁆ := by
      rw [map_mul, map_inv, hj a x, inlG_aut, commutatorElement_def]
      group
    rw [hkey]
    exact Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hx1) hv
  · refine Subgroup.commutator_le.mpr ?_
    intro u hu v hv
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hu
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hv
    rw [Subgroup.mem_map]
    refine ⟨x * (a • x)⁻¹, ?_, ?_⟩
    · have h : (x⁻¹)⁻¹ * (a • x⁻¹) ∈ FT.commutator A H := FT.le_commutator a (H.inv_mem hx)
      rwa [inv_inv, smul_inv'] at h
    · rw [map_mul, map_inv, hj a x, inlG_aut, commutatorElement_def, MonoidHom.comp_apply]
      group

/-- The two copies of `P` and `Q` inside `G ⋊ (P × Q)` commute. -/
private lemma Psub_comm_Qsub : ⁅Psub P Q G, Qsub P Q G⁆ = ⊥ := by
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro u hu v hv
  rw [Subgroup.mem_bot]
  obtain ⟨p, rfl⟩ := MonoidHom.mem_range.mp hu
  obtain ⟨q, rfl⟩ := MonoidHom.mem_range.mp hv
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_commutatorElement]
  have hpq : ⁅(MonoidHom.inl P Q) p, (MonoidHom.inr P Q) q⁆ = 1 := by
    rw [MonoidHom.inl_apply, MonoidHom.inr_apply]
    simp [commutatorElement_def]
  rw [hpq, map_one]

theorem commutator_eq_bot_of_commutator_eq_bot {P Q G : Type*} [Group P] [Group Q] [Group G]
    [MulDistribMulAction P G] [MulDistribMulAction Q G] [SMulCommClass P Q G]
    (h : FT.commutator Q (FT.commutator P (⊤ : Subgroup G)) = ⊥) :
    FT.commutator P (FT.commutator Q (⊤ : Subgroup G)) = ⊥ := by
  have hjP : ∀ (p : P) (g : G), p • g = pxqActionHom P Q G ((MonoidHom.inl P Q) p) g :=
    fun p g => (pxq_inl p g).symm
  have hjQ : ∀ (q : Q) (g : G), q • g = pxqActionHom P Q G ((MonoidHom.inr P Q) q) g :=
    fun q g => (pxq_inr q g).symm
  have hθP : (FT.commutator P (⊤ : Subgroup G)).map (inlG P Q G) = ⁅Gsub P Q G, Psub P Q G⁆ := by
    rw [map_inl_commutator (P := P) (Q := Q) (G := G) (MonoidHom.inl P Q) hjP ⊤,
      Subgroup.map_top]
  have hθQ : (FT.commutator Q (⊤ : Subgroup G)).map (inlG P Q G) = ⁅Gsub P Q G, Qsub P Q G⁆ := by
    rw [map_inl_commutator (P := P) (Q := Q) (G := G) (MonoidHom.inr P Q) hjQ ⊤,
      Subgroup.map_top]
  -- The hypothesis, transported into `Γ`.
  have hhyp : ⁅⁅Gsub P Q G, Psub P Q G⁆, Qsub P Q G⁆ = ⊥ := by
    have h1 := congrArg (Subgroup.map (inlG P Q G)) h
    rw [Subgroup.map_bot] at h1
    rw [map_inl_commutator (P := P) (Q := Q) (G := G) (MonoidHom.inr P Q) hjQ
      (FT.commutator P (⊤ : Subgroup G))] at h1
    rwa [hθP] at h1
  have h1 : ⁅⁅Qsub P Q G, Psub P Q G⁆, Gsub P Q G⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (Qsub P Q G) (Psub P Q G), Psub_comm_Qsub,
      Subgroup.commutator_bot_left]
  have h2 : ⁅⁅Psub P Q G, Gsub P Q G⁆, Qsub P Q G⁆ = ⊥ := by
    rw [Subgroup.commutator_comm (Psub P Q G) (Gsub P Q G)]
    exact hhyp
  -- The three subgroups lemma.
  have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate
    (H₁ := Gsub P Q G) (H₂ := Qsub P Q G) (H₃ := Psub P Q G) h1 h2
  -- Transport back along the injective embedding `G ↪ Γ`.
  have hfin : (FT.commutator P (FT.commutator Q (⊤ : Subgroup G))).map (inlG P Q G) = ⊥ := by
    rw [map_inl_commutator (P := P) (Q := Q) (G := G) (MonoidHom.inl P Q) hjP
      (FT.commutator Q (⊤ : Subgroup G)), hθQ]
    exact h3
  rw [Subgroup.map_eq_bot_iff] at hfin
  have hker : (inlG P Q G).ker = ⊥ :=
    (MonoidHom.ker_eq_bot_iff (inlG P Q G)).mpr
      (SemidirectProduct.inl_injective (φ := pxqActionHom P Q G))
  rw [hker] at hfin
  exact le_bot_iff.mp hfin

end Work.Coprime.PxQUtil
