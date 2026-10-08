import Mathlib
import Submission.Work.BSLit.BenderFacts2.Facts2Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BSLit.BenderFacts2

/-- The involutions of `H` and of its image under a group isomorphism have the same number. -/
theorem involutions_map_ncard_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) :
    (Submission.Blueprint.involutions (H : Set G)).ncard
      = (Submission.Blueprint.involutions (H.map e.toMonoidHom : Set G')).ncard := by
  have hset : Submission.Blueprint.involutions (H.map e.toMonoidHom : Set G')
      = e '' Submission.Blueprint.involutions (H : Set G) := by
    ext y
    constructor
    · rintro ⟨hy, hy2⟩
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      exact ⟨x, ⟨hx, by rw [← MulEquiv.orderOf_eq e x]; exact hy2⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hx2⟩, rfl⟩
      exact ⟨Subgroup.mem_map_of_mem e.toMonoidHom hx,
        by rw [MulEquiv.orderOf_eq]; exact hx2⟩
  rw [hset, Set.ncard_image_of_injective _ e.injective]

/-- **Transport of `BenderFacts2For` forward along a group isomorphism**:
`BenderFacts2For G H` implies `BenderFacts2For G' (H.map e)`.

Clause 1 goes through `∀ x ∈ H` with `∃ k, orderOf x = 2 ^ k`: pull `x' ∈ H.map e` back to
`x = e.symm x'`, transport the order condition with `MulEquiv.orderOf_eq`, and read the identity
back with `map_pow`.  In clause 2 one pulls back `u' ∈ involutions (H.map e)` and `t'` (with
`orderOf t' = 2`, `t' ∉ H.map e`) to `u = e.symm u'`, `t = e.symm t'`, applies the hypothesis, and
transports the three conclusions through the isomorphism `↥(C_G{u * t}) ≃* ↥(C_G'{u'*t'})`
(`Subgroup.equivMapOfInjective` composed with `MulEquiv.subgroupCongr` on the equality of
centralisers), using `MulEquiv.isCyclic`, `map_mul`/`map_inv` and `Nat.card_congr`; the numerical
hypothesis is transported by `involutions_map_ncard_mulEquiv`. -/
theorem benderFacts2For_map_mulEquiv_forward {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) (h : BenderFacts2For G H) :
    BenderFacts2For G' (H.map e.toMonoidHom) := by
  obtain ⟨h1, h2⟩ := h
  constructor
  · intro x' hx' hk'
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hx'
    obtain ⟨k, hk⟩ := hk'
    have hkG : ∃ j : ℕ, orderOf x = 2 ^ j :=
      ⟨k, (MulEquiv.orderOf_eq e x).symm.trans hk⟩
    have h4 := h1 x hx hkG
    rw [← map_pow, h4, map_one]
  · intro u' hu' t' ht2' htn'
    obtain ⟨hu1, hu2⟩ := hu'
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hu1
    have hu2G : orderOf u = 2 := by rw [← MulEquiv.orderOf_eq e u]; exact hu2
    set t : G := e.symm t' with ht
    have het : e t = t' := by rw [ht]; simp
    have ht2 : orderOf t = 2 := by
      rw [← MulEquiv.orderOf_eq e t, het]; exact ht2'
    have htn : t ∉ H := by
      intro htH
      apply htn'
      rw [← het]
      exact Subgroup.mem_map_of_mem e.toMonoidHom htH
    obtain ⟨hcyc, hinv, hcard⟩ := h2 u ⟨hu, hu2G⟩ t ht2 htn
    have hce : (Subgroup.centralizer ({u * t} : Set G)).map e.toMonoidHom
        = Subgroup.centralizer ({e u * t'} : Set G') := by
      rw [centralizer_map_mulEquiv e (u * t), map_mul, het]
    have hiso : ↥(Subgroup.centralizer ({u * t} : Set G))
        ≃* ↥(Subgroup.centralizer ({e u * t'} : Set G')) :=
      (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hce)
    refine ⟨(MulEquiv.isCyclic hiso).mp hcyc, ?_, ?_⟩
    · intro y hy
      have hy' : e.symm y ∈ Subgroup.centralizer ({u * t} : Set G) := by
        have hmem : y ∈ (Subgroup.centralizer ({u * t} : Set G)).map e.toMonoidHom := by
          rw [hce]; exact hy
        obtain ⟨z, hz, hze⟩ := Subgroup.mem_map.mp hmem
        have hzy : e.symm y = z := by rw [← hze]; simp
        rwa [hzy]
      have h := hinv (e.symm y) hy'
      have key : e (u * e.symm y * u⁻¹) = e ((e.symm y)⁻¹) := by rw [h]
      simpa using key
    · intro h127
      have h127' : 127 ≤ (Submission.Blueprint.involutions (H : Set G)).ncard := by
        rw [involutions_map_ncard_mulEquiv e H]; exact h127
      have h6 := hcard h127'
      have hcard_eq : Nat.card ↥(Subgroup.centralizer ({u * t} : Set G))
          = Nat.card ↥(Subgroup.centralizer ({e.toMonoidHom u * t'} : Set G')) :=
        Nat.card_congr hiso.toEquiv
      rw [← hcard_eq]; exact h6

/-- **The three clauses of `BenderFacts2For` are invariant under a group isomorphism**:
`BenderFacts2For G' (H.map e) ↔ BenderFacts2For G H`, where `BenderFacts2For` is the (unconditional
in `IsZassenhaus`) conjunction of the three clauses of `BenderModelFacts2Prop`,
`Work.BSLit.BenderFacts2.BenderFacts2For` in `Submission/Work/BSLit/BenderFacts2/Facts2Defs.lean`:

* `∀ x ∈ H, (∃ k, orderOf x = 2 ^ k) → x ^ 4 = 1` — uses `MulEquiv.orderOf_eq` and `map_pow`;
* for `u ∈ involutions H` and `t` with `orderOf t = 2`, `t ∉ H`:
  `IsCyclic ↥(centralizer {u * t})`, `∀ y ∈ centralizer {u * t}, u * y * u⁻¹ = y⁻¹`, and
  `127 ≤ (involutions H).ncard → 6 ≤ Nat.card ↥(centralizer {u * t})`.

The ingredients are `MulEquiv.orderOf_eq`, `map_pow`/`map_inv`, `Subgroup.mem_map`,
`Set.ncard_image_of_injective` (for the number of involutions), the already-proved
`Work.BSLit.BenderFacts2.centralizer_map_mulEquiv` (centraliser of the image is the image of the
centraliser), `Nat.card_congr ∘ Subgroup.equivMapOfInjective` (cardinalities) and
`MulEquiv.isCyclic` (cyclicity), all in the same isomorphism `e : G ≃* G'`. -/
theorem benderFacts2For_map_mulEquiv {G G' : Type*} [Group G] [Group G'] (e : G ≃* G')
    (H : Subgroup G) :
    BenderFacts2For G' (H.map e.toMonoidHom) ↔ BenderFacts2For G H := by
  constructor
  · intro h
    have h' := benderFacts2For_map_mulEquiv_forward e.symm (H.map e.toMonoidHom) h
    have hmap : (H.map e.toMonoidHom).map e.symm.toMonoidHom = H := by
      rw [Subgroup.map_map]
      have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by
        ext x; simp
      rw [hcomp, Subgroup.map_id]
    rw [hmap] at h'
    exact h'
  · intro h
    exact benderFacts2For_map_mulEquiv_forward e H h

end Work.BSLit.BenderFacts2
