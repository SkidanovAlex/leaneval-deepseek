import Mathlib
import Submission.Work.HopfGaschutz.Defs
import Submission.Work.HopfGaschutz.le_normalClosure_of_le_sup_relFrattini

/-!
# `Work.HopfGaschutz.closedRelationData_of_spanningModulo` -- the closed (finite-quotient) form of
the relation-rank dictionary

**Namespace** `Work.HopfGaschutz`; module
`Submission.Work.HopfGaschutz.closedRelationData_of_spanningModulo`.

The *spanning-modulo-`K^p[K,F]`* condition of the relation-rank dictionary, imposed **at every
finite `p`-group quotient** of the free group `F = FreeGroup α`, is enough to conclude that the
corresponding finite quotients see no more than the given relators.  Concretely: if for every finite
`p`-group `Q` and every `φ : F →* Q`

  `K ≤ ⟪S⟫ · K^p[K,F] · ker φ`,

then every finite `p`-group quotient `φ` of `F` that kills `S` already kills `K`.

This is the *engine of the closed dictionary*: modulo the kernel of the quotient, the defect
`K ⧸ ⟪S⟫` is a finite `p`-group, and the finite engine
(`le_normalClosure_of_le_sup_relFrattini`) applies to its image in the quotient.

## Universes

The statement quantifies over the finite `p`-groups `Q` that occur in the hypothesis and in the
conclusion *in independent universes*.  The proof therefore has to *move* the finite `p`-group
`Q` of the conclusion into the universe of the hypothesis: a finite type is small, and any finite
group is isomorphic to one carried by `ShrinkFin n` (`ULift` of a copy of `Fin n` carrying no
algebraic structure), lifted into the target universe.  The auxiliary definition `groupOfEquiv`
transports a group structure across a bijection; `ShrinkFin` is an opaque copy of `Fin n` -- opaque
because `Fin n` itself carries a `CommMonoid` structure, which would clash with the transported one.
-/

set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace Work.HopfGaschutz

open scoped commutatorElement

universe u v

/-! ## Moving a finite group into a prescribed universe -/

/-- An opaque copy of `Fin n`, carrying no algebraic structure.  (`Fin n` itself is a
`CommMonoid`, so `ULift (Fin n)` would come with a multiplication competing with the transported
one; this copy has no instances at all.) -/
inductive ShrinkFin (n : ℕ) : Type where
  | mk (i : Fin n) : ShrinkFin n

/-- The canonical bijection `Fin n ≃ ShrinkFin n`. -/
def shrinkFinEquiv (n : ℕ) : Fin n ≃ ShrinkFin n where
  toFun := ShrinkFin.mk
  invFun i := match i with | ShrinkFin.mk j => j
  left_inv := fun j => rfl
  right_inv := fun i => by cases i; rfl

instance instFintypeShrinkFin (n : ℕ) : Fintype (ShrinkFin n) :=
  Fintype.ofEquiv (Fin n) (shrinkFinEquiv n)

/-- **Transport of a group structure across a bijection.**  If `e : G ≃ H` is a bijection onto a
group `H`, then `G` carries a group structure making `e` an isomorphism (multiplication
`a * b := e.symm (e a * e b)`). -/
noncomputable def groupOfEquiv {G : Type u} {H : Type v} [Group H] (e : G ≃ H) : Group G := by
  letI : Mul G := ⟨fun a b => e.symm (e a * e b)⟩
  letI : One G := ⟨e.symm 1⟩
  letI : Inv G := ⟨fun a => e.symm (e a)⁻¹⟩
  letI : Div G := ⟨fun a b => e.symm (e a / e b)⟩
  letI : Pow G ℕ := ⟨fun a n => e.symm ((e a) ^ n)⟩
  letI : Pow G ℤ := ⟨fun a n => e.symm ((e a) ^ n)⟩
  exact Function.Injective.group e e.injective
    (by show e (e.symm 1) = (1 : H); simp)
    (fun a b => by show e (e.symm (e a * e b)) = e a * e b; simp)
    (fun a => by show e (e.symm ((e a)⁻¹)) = (e a)⁻¹; simp)
    (fun a b => by show e (e.symm (e a / e b)) = e a / e b; simp)
    (fun a n => by show e (e.symm ((e a)^n)) = (e a)^n; simp)
    (fun a n => by show e (e.symm ((e a)^n)) = (e a)^n; simp)

/-! ## The main argument -/

set_option maxHeartbeats 2000000 in
/-- The main argument, with the two universes named: the spanning hypothesis is imposed on finite
`p`-groups in the universe `u`, the conclusion is about finite `p`-groups in the universe `v`. -/
private theorem closedRelationData_aux {α : Type*} [Fintype α] {p : ℕ} [Fact p.Prime]
    {K : Subgroup (FreeGroup α)} [K.Normal] {S : Finset (FreeGroup α)}
    (hspan : ∀ (Q : Type u) [Group Q] [Fintype Q], IsPGroup p Q → ∀ φ : FreeGroup α →* Q,
      K ≤ Subgroup.normalClosure (S : Set (FreeGroup α)) ⊔ relFrattini p K ⊔ MonoidHom.ker φ) :
    ∀ (Q : Type v) [Group Q] [Fintype Q], IsPGroup p Q → ∀ φ : FreeGroup α →* Q,
      (∀ s ∈ S, φ s = 1) → K ≤ MonoidHom.ker φ := by
  classical
  intro Q _ _ hQ φ hφS
  -- the given relators lie in the kernel
  have hM : Subgroup.normalClosure (S : Set (FreeGroup α)) ≤ MonoidHom.ker φ := by
    refine Subgroup.normalClosure_le_normal ?_
    intro s hs
    exact hφS s hs
  /- Move the finite `p`-group `↥φ.range` into the universe `u`, where the spanning hypothesis
  lives. -/
  let n : ℕ := Fintype.card ↥φ.range
  let e : ULift.{u, 0} (ShrinkFin n) ≃ ↥φ.range :=
    (Equiv.ulift.trans (shrinkFinEquiv n).symm).trans (Fintype.equivFin ↥φ.range).symm
  letI : Group (ULift.{u, 0} (ShrinkFin n)) := groupOfEquiv e
  let eHom : ULift.{u, 0} (ShrinkFin n) →* ↥φ.range :=
    { toFun := e
      map_one' := by show e (e.symm 1) = (1 : ↥φ.range); simp
      map_mul' := fun a b => by show e (e.symm (e a * e b)) = e a * e b; simp }
  let eEquiv : ULift.{u, 0} (ShrinkFin n) ≃* ↥φ.range :=
    MulEquiv.ofBijective eHom ⟨e.injective, e.surjective⟩
  have hφr : ∀ x : FreeGroup α, φ x ∈ φ.range := fun x => MonoidHom.mem_range.mpr ⟨x, rfl⟩
  let φ₀ : FreeGroup α →* ↥φ.range := φ.codRestrict φ.range hφr
  let ψ : FreeGroup α →* ULift.{u, 0} (ShrinkFin n) := eEquiv.symm.toMonoidHom.comp φ₀
  -- the kernel is unchanged, and the shrunk group is a finite `p`-group on which `ψ` is onto
  have hker : MonoidHom.ker ψ = MonoidHom.ker φ := by
    rw [show ψ = eEquiv.symm.toMonoidHom.comp φ₀ from rfl,
      show φ₀ = φ.codRestrict φ.range hφr from rfl,
      MonoidHom.ker_comp_of_injective _ _ eEquiv.symm.injective,
      MonoidHom.ker_codRestrict]
  have hGp : IsPGroup p (ULift.{u, 0} (ShrinkFin n)) :=
    (hQ.to_subgroup φ.range).of_equiv eEquiv.symm
  have hsurj : Function.Surjective ψ := by
    intro y
    have hy : (eEquiv y : Q) ∈ φ.range := (eEquiv y).2
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
    refine ⟨x, ?_⟩
    have h2 : φ₀ x = eEquiv y := Subtype.ext hx
    show eEquiv.symm (φ₀ x) = y
    rw [h2, MulEquiv.symm_apply_apply]
  -- the spanning hypothesis, at the shrunk group
  have hmain : K ≤ relFrattini p K ⊔ MonoidHom.ker φ := by
    have h := hspan (ULift.{u, 0} (ShrinkFin n)) hGp ψ
    rw [hker] at h
    exact le_trans h (sup_le (sup_le (hM.trans le_sup_right) le_sup_left) le_sup_right)
  -- push the spanning statement into the shrunk group
  have hkerbot : Subgroup.map ψ (MonoidHom.ker φ) = ⊥ := by
    rw [← hker]
    exact (Subgroup.map_eq_bot_iff (MonoidHom.ker ψ) (f := ψ)).mpr le_rfl
  have hpPower : Subgroup.map ψ (pPower p K) ≤ pPower p (K.map ψ) := by
    rw [Subgroup.map_le_iff_le_comap]
    show pPower p K ≤ Subgroup.comap ψ (pPower p (Subgroup.map ψ K))
    rw [pPower, pPower, Subgroup.closure_le]
    rintro x ⟨k, hk, rfl⟩
    exact Subgroup.subset_closure ⟨ψ k, Subgroup.mem_map_of_mem ψ hk, (map_pow ψ k p).symm⟩
  have hcomm : Subgroup.map ψ ⁅K, (⊤ : Subgroup (FreeGroup α))⁆ ≤
      ⁅K.map ψ, (⊤ : Subgroup (ULift.{u, 0} (ShrinkFin n)))⁆ :=
    le_of_eq (by rw [Subgroup.map_commutator, Subgroup.map_top_of_surjective ψ hsurj])
  have hle : Subgroup.map ψ (relFrattini p K) ≤ relFrattini p (K.map ψ) := by
    have h1 : Subgroup.map ψ (relFrattini p K)
        = Subgroup.map ψ (pPower p K) ⊔ Subgroup.map ψ ⁅K, (⊤ : Subgroup (FreeGroup α))⁆ := by
      rw [relFrattini, Subgroup.map_sup]
    rw [h1, relFrattini]
    exact sup_le (hpPower.trans le_sup_left) (hcomm.trans le_sup_right)
  have hPfrat : K.map ψ ≤ relFrattini p (K.map ψ) := by
    have h := Subgroup.map_mono (f := ψ) hmain
    rw [Subgroup.map_sup, hkerbot, sup_bot_eq] at h
    exact h.trans hle
  -- the finite engine in the shrunk `p`-group
  haveI hPnorm : (K.map ψ).Normal := Subgroup.Normal.map ‹K.Normal› ψ hsurj
  have hbot : K.map ψ ≤ ⊥ := by
    have h := le_normalClosure_of_le_sup_relFrattini (G := ULift.{u, 0} (ShrinkFin n)) hGp
      (K := K.map ψ) (S := ∅) (by simp)
      (by
        rw [Finset.coe_empty, Subgroup.normalClosure_empty, bot_sup_eq]
        exact hPfrat)
    simpa only [Finset.coe_empty, Subgroup.normalClosure_empty] using h
  have hK : K ≤ MonoidHom.ker ψ := by
    rw [← Subgroup.map_eq_bot_iff]
    exact le_bot_iff.mp hbot
  rwa [hker] at hK

/-- **The closed relation data from the spanning-modulo hypothesis.**  If at every finite
`p`-group quotient `φ : FreeGroup α →* Q` the normal subgroup `K` is spanned by a finite set `S`
modulo `K^p[K,FreeGroup α]` together with `ker φ`, then every finite `p`-group quotient killing `S`
kills `K` as well. -/
theorem closedRelationData_of_spanningModulo {α : Type*} [Fintype α] {p : ℕ} [Fact p.Prime]
    {K : Subgroup (FreeGroup α)} [K.Normal] {S : Finset (FreeGroup α)}
    (hspan : ∀ (Q : Type*) [Group Q] [Fintype Q], IsPGroup p Q → ∀ φ : FreeGroup α →* Q,
      K ≤ Subgroup.normalClosure (S : Set (FreeGroup α)) ⊔ Work.HopfGaschutz.relFrattini p K ⊔
        MonoidHom.ker φ) :
    ∀ (Q : Type*) [Group Q] [Fintype Q], IsPGroup p Q → ∀ φ : FreeGroup α →* Q,
      (∀ s ∈ S, φ s = 1) → K ≤ MonoidHom.ker φ :=
  closedRelationData_aux hspan

end Work.HopfGaschutz
