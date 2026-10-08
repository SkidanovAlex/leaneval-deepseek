import Mathlib
import Submission.Work.Hering.InvSubgroup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Hering.Step4

open LeanEval.GroupTheory.Defs Work.Hering

/-!
# `|G| = 6 * |C_G(V)|` for `V = Inv(G) ∪ {1}` of order `4`

When `V = invSubgroup hDT h4` has cardinality `4`, the involutions of `G` are exactly the three
elements of `V \ {1}`.  The double transitivity hypothesis `hDT` therefore makes `G` act
transitively on the six ordered pairs of distinct involutions, the stabiliser of such a pair
`(a,b)` being `C_G(a) ∩ C_G(b) = C_G(⟨a,b⟩) = C_G(V)`.  Orbit–stabiliser then gives
`|G| = 6 * |C_G(V)|`.

The file fixes the `G`-set `PairInv G` of ordered pairs of distinct involutions (a subtype of
`G × G` with the diagonal conjugation action), counts it, and identifies the stabiliser of a
base point with `C_G(V)`.
-/

/-- Ordered pairs of distinct involutions of `G`, endowed below with the simultaneous conjugation
action `g • (x, y) = (g x g⁻¹, g y g⁻¹)`. -/
def PairInv (G : Type*) [Group G] : Type _ :=
  {p : G × G // orderOf p.1 = 2 ∧ orderOf p.2 = 2 ∧ p.1 ≠ p.2}

instance instSMulPairInv (G : Type*) [Group G] : SMul G (PairInv G) where
  smul g p := ⟨(g * p.1.1 * g⁻¹, g * p.1.2 * g⁻¹), by
    obtain ⟨h1, h2, h3⟩ := p.2
    exact ⟨by rw [orderOf_conj, h1], by rw [orderOf_conj, h2],
      by intro h; apply h3; have hh := congrArg (fun t => g⁻¹ * t * g) h
         simpa [mul_assoc] using hh⟩⟩

@[simp] theorem smul_fst {G : Type*} [Group G] (g : G) (p : PairInv G) :
    (g • p).1.1 = g * p.1.1 * g⁻¹ := rfl

@[simp] theorem smul_snd {G : Type*} [Group G] (g : G) (p : PairInv G) :
    (g • p).1.2 = g * p.1.2 * g⁻¹ := rfl

instance instMulActionPairInv (G : Type*) [Group G] : MulAction G (PairInv G) where
  one_smul p := by
    apply Subtype.ext; apply Prod.ext <;> simp
  mul_smul g h p := by
    apply Subtype.ext; apply Prod.ext <;> simp [mul_assoc]

/-- The number of ordered pairs of distinct elements of a finite type is `n * (n - 1)`. -/
theorem card_pair_ne {α : Type*} [Finite α] :
    Nat.card {p : α × α // p.1 ≠ p.2} = Nat.card α * Nat.card α - Nat.card α := by
  have hcompl : Nat.card {p : α × α // p.1 ≠ p.2} =
      ({p : α × α | p.1 ≠ p.2} : Set (α × α)).ncard := rfl
  rw [hcompl]
  have : ({p : α × α | p.1 ≠ p.2} : Set (α × α)) = {p : α × α | p.1 = p.2}ᶜ := rfl
  rw [this, Set.ncard_compl, Nat.card_prod]
  congr 1
  have hdiag : ({p : α × α | p.1 = p.2} : Set (α × α)).ncard = Nat.card α := by
    rw [← Nat.card_coe_set_eq]
    exact Nat.card_congr
      { toFun := fun p => p.1.1
        invFun := fun i => ⟨(i, i), rfl⟩
        left_inv := by
          rintro ⟨⟨a, b⟩, hab⟩
          have hab' : a = b := hab
          subst hab'
          rfl
        right_inv := by intro i; rfl }
  rw [hdiag]

/-- When `|V| = 4`, the involutions of `G` are exactly the three elements of `V \ {1}`. -/
theorem card_involutions_eq_three {G : Type*} [Group G] [Finite G] {hDT : DTInv G}
    {h4 : HasFourGroup G} (hV : Nat.card ↥(invSubgroup hDT h4) = 4) :
    Nat.card {x : G // x ∈ involutions G} = 3 := by
  have heq : involutions G = (invSubgroup hDT h4 : Set G) \ {1} :=
    involutions_eq_invSubgroup_diff hDT h4
  let e : {x : G // x ∈ involutions G} ≃ {v : ↥(invSubgroup hDT h4) // v ≠ 1} :=
    { toFun := fun x =>
        ⟨⟨x.1, (show x.1 ∈ (invSubgroup hDT h4 : Set G) \ {1} from by
                rw [← heq]; exact x.2).1⟩,
          fun h => ne_one_of_mem_involutions x.2 (by
            have h2 := congrArg Subtype.val h
            simpa using h2)⟩
      invFun := fun v =>
        ⟨v.1.1, by
          rw [mem_involutions]
          rcases (mem_invSubgroup hDT h4).mp v.1.2 with h | h
          · exact h
          · exact absurd (Subtype.ext h) v.2⟩
      left_inv := by intro x; rfl
      right_inv := by intro v; rfl }
  rw [Nat.card_congr e]
  have h1 : Nat.card {v : ↥(invSubgroup hDT h4) // v ≠ 1} =
      ({1}ᶜ : Set ↥(invSubgroup hDT h4)).ncard := rfl
  rw [h1, Set.ncard_compl, Set.ncard_singleton, hV]

/-- Two distinct involutions `a, b` of a group with `|V| = 4` generate `V = ⟨a, b⟩`. -/
theorem closure_pair_eq_invSubgroup {G : Type*} [Group G] [Finite G] {hDT : DTInv G}
    {h4 : HasFourGroup G} (hV : Nat.card ↥(invSubgroup hDT h4) = 4) {a b : G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) :
    Subgroup.closure ({a, b} : Set G) = invSubgroup hDT h4 := by
  have hia : a ∈ involutions G := ha
  have hib : b ∈ involutions G := hb
  have ha1 : a ≠ 1 := ne_one_of_mem_involutions hia
  have hb1 : b ≠ 1 := ne_one_of_mem_involutions hib
  have hab1 : a * b ≠ 1 := by
    intro h
    have hba : b = a := by
      have hh := congrArg (fun t => a * t) h
      simpa [← mul_assoc, sq_eq_one_of_orderOf_eq_two ha] using hh
    exact hab hba.symm
  have haba : a * b ≠ a := by
    intro h
    refine hb1 (mul_left_cancel (show a * b = a * 1 by rw [h, mul_one]))
  have habb : a * b ≠ b := by
    intro h
    refine ha1 (mul_right_cancel (show a * b = 1 * b by rw [h, one_mul]))
  have hle : Subgroup.closure ({a, b} : Set G) ≤ invSubgroup hDT h4 :=
    (Subgroup.closure_le _).mpr (by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact involutions_subset_invSubgroup hDT h4 hia
      · exact involutions_subset_invSubgroup hDT h4 hib)
  have h1not : (1 : G) ∉ insert a (insert b ({a * b} : Set G)) := by
    intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h
    · exact ha1 h.symm
    · exact hb1 h.symm
    · exact hab1 h.symm
  have hanot : a ∉ insert b ({a * b} : Set G) := by
    intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h
    · exact hab h
    · exact haba h.symm
  have hbnot : b ∉ ({a * b} : Set G) := by
    intro h
    simp only [Set.mem_singleton_iff] at h
    exact habb h.symm
  have hcard : ({1, a, b, a * b} : Set G).ncard = 4 := by
    rw [show ({1, a, b, a * b} : Set G) =
        insert (1 : G) (insert a (insert b ({a * b} : Set G))) from rfl]
    rw [Set.ncard_insert_of_notMem h1not, Set.ncard_insert_of_notMem hanot,
      Set.ncard_insert_of_notMem hbnot, Set.ncard_singleton]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [hV]
  have hsub : ({1, a, b, a * b} : Set G) ⊆
      (Subgroup.closure ({a, b} : Set G) : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
  have hle2 := Set.ncard_le_ncard hsub
  rw [hcard] at hle2
  change 4 ≤ (Subgroup.closure ({a, b} : Set G) : Set G).ncard
  exact hle2

/-- `V = invSubgroup hDT h4` has cardinality `4`, so `G` acts doubly transitively on the three
involutions and all involutions lie in `V`.  The conjugates of the ordered pair `(a,b)` of distinct
involutions are exactly the six ordered pairs of distinct involutions, and the stabiliser of
`(a,b)` is `C_G(V)`.  Hence `|G| = 6 * |C_G(V)|`. -/
theorem card_six_mul_centralizer {G : Type*} [Group G] [Finite G] {hDT : DTInv G}
    {h4 : HasFourGroup G} (hV : Nat.card ↥(invSubgroup hDT h4) = 4) :
    Nat.card G = 6 * Nat.card ↥(Subgroup.centralizer (((invSubgroup hDT h4) : Subgroup G) : Set G)) := by
  classical
  have h4' : HasFourGroup G := h4
  obtain ⟨a, b, ha, hb, hab, _hcomm⟩ := h4'
  -- the base point `(a, b)`
  let pt : PairInv G := ⟨(a, b), ha, hb, hab⟩
  -- the action is transitive: the orbit of `(a, b)` is everything
  have horbit : MulAction.orbit G pt = Set.univ := by
    apply Set.eq_univ_of_forall
    intro x
    rw [MulAction.mem_orbit_iff]
    obtain ⟨hc, hd, hcd⟩ := x.2
    obtain ⟨g, hg1, hg2⟩ :=
      hDT a b x.1.1 x.1.2 ha hb hc hd hab hcd
    refine ⟨g, ?_⟩
    apply Subtype.ext
    apply Prod.ext
    · show g * a * g⁻¹ = x.1.1
      exact hg1
    · show g * b * g⁻¹ = x.1.2
      exact hg2
  have hcard_orbit : Nat.card ↥(MulAction.orbit G pt) = Nat.card (PairInv G) := by
    rw [horbit]
    exact Nat.card_congr (Equiv.Set.univ (PairInv G))
  -- the orbit has six elements
  have hXcard : Nat.card (PairInv G) = 6 := by
    have hbij : PairInv G ≃
        {p : {x : G // x ∈ involutions G} × {x : G // x ∈ involutions G} // p.1 ≠ p.2} :=
      { toFun := fun p =>
          ⟨(⟨p.1.1, p.2.1⟩, ⟨p.1.2, p.2.2.1⟩), fun h =>
            p.2.2.2 (by simpa using congrArg Subtype.val h)⟩
        invFun := fun p =>
          ⟨(p.1.1.1, p.1.2.1), ⟨p.1.1.2, p.1.2.2, fun h => p.2 (Subtype.ext h)⟩⟩
        left_inv := by intro p; rfl
        right_inv := by intro p; rfl }
    rw [Nat.card_congr hbij, card_pair_ne, card_involutions_eq_three hV]
  -- the stabiliser of `(a, b)` is `C_G(V)`
  have hstab : Nat.card ↥(MulAction.stabilizer G pt) =
      Nat.card ↥(Subgroup.centralizer (((invSubgroup hDT h4) : Subgroup G) : Set G)) := by
    have hstab_eq : MulAction.stabilizer G pt = Subgroup.centralizer ({a, b} : Set G) := by
      ext g
      rw [MulAction.mem_stabilizer_iff, Subgroup.mem_centralizer_iff]
      constructor
      · intro hg
        have hga : g * a * g⁻¹ = a := by
          have := congrArg (fun p : PairInv G => p.1.1) hg
          simpa using this
        have hgb : g * b * g⁻¹ = b := by
          have := congrArg (fun p : PairInv G => p.1.2) hg
          simpa using this
        have h1 : g * a = a * g := mul_inv_eq_iff_eq_mul.mp hga
        have h2 : g * b = b * g := mul_inv_eq_iff_eq_mul.mp hgb
        intro h hmem
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl
        · exact h1.symm
        · exact h2.symm
      · intro hg
        have h1 : a * g = g * a := hg a (by simp)
        have h2 : b * g = g * b := hg b (by simp)
        apply Subtype.ext
        apply Prod.ext
        · show g * a * g⁻¹ = a
          rw [← h1]; group
        · show g * b * g⁻¹ = b
          rw [← h2]; group
    have hcent : Subgroup.centralizer ({a, b} : Set G) =
        Subgroup.centralizer (((invSubgroup hDT h4) : Subgroup G) : Set G) := by
      rw [← closure_pair_eq_invSubgroup hV ha hb hab, Subgroup.centralizer_closure]
    rw [hstab_eq, hcent]
  -- orbit–stabiliser
  have hkey := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup G pt)
  rw [Nat.card_prod, hcard_orbit, hXcard, hstab] at hkey
  exact hkey.symm

end Work.Hering.Step4
