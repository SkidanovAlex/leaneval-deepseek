/-
Copyright (c) 2025. All rights reserved.

# Invariants and inflation

For a normal subgroup `N ◁ G` and a `G`-module `A`, the invariants `A^N` carry an action of the
quotient `G ⧸ N` (the action of `G` on `A^N` factors through `N`, since `N` acts trivially on
`A^N`).  This gives the *inflation* maps `Hⁿ(G ⧸ N, A^N) → Hⁿ(G, A)`, `n = 1, 2`.

## Main definitions

* `Work.GroupCohomology.invariants`
* `Work.GroupCohomology.quotientEnd`, `Work.GroupCohomology.quotientDistribMulAction`
* `Work.GroupCohomology.infH1`, `Work.GroupCohomology.infH2`
-/
import Submission.Work.GroupCohomology.Functoriality
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.GroupCohomology

section Invariants

variable (G : Type u) (A : Type v) [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- The invariants `A^G` of a `G`-module `A`. -/
def invariants : AddSubgroup A where
  carrier := {a | ∀ g : G, g • a = a}
  zero_mem' := by simp
  add_mem' := by intro a b ha hb g; rw [smul_add, ha g, hb g]
  neg_mem' := by intro a ha g; rw [smul_neg, ha g]

@[simp] theorem mem_invariants (a : A) : a ∈ invariants G A ↔ ∀ g : G, g • a = a := Iff.rfl

end Invariants

section Quotient

variable {G : Type u} {A : Type v} [Group G] [AddCommGroup A] [DistribMulAction G A]
variable (N : Subgroup G) [N.Normal]

/-- The invariants `A^N` are stable under the action of `G`. -/
theorem smul_mem_invariants (hN : N.Normal) (x : invariants N A) (g : G) :
    g • (x : A) ∈ invariants N A := by
  intro n
  calc n • (g • (x : A)) = ((n : G) * g) • (x : A) := (mul_smul _ _ _).symm
    _ = (g * (g⁻¹ * (n : G) * g)) • (x : A) := by
          rw [show (n : G) * g = g * (g⁻¹ * (n : G) * g) by group]
    _ = g • ((g⁻¹ * (n : G) * g) • (x : A)) := mul_smul _ _ _
    _ = g • (x : A) := by
          congr 1
          have hmem : g⁻¹ * (n : G) * g ∈ N := by
            simpa using hN.conj_mem (n : G) n.2 g⁻¹
          exact x.2 ⟨g⁻¹ * (n : G) * g, hmem⟩

/-- The action of `G` on the invariants `A^N`. -/
noncomputable instance invariantsDistribMulAction : DistribMulAction G (invariants N A) where
  smul g x := ⟨g • (x : A), smul_mem_invariants N inferInstance x g⟩
  one_smul x := Subtype.ext (one_smul G (x : A))
  mul_smul g g' x := Subtype.ext (mul_smul g g' (x : A))
  smul_zero g := Subtype.ext (smul_zero g)
  smul_add g x y := Subtype.ext (smul_add g (x : A) (y : A))

/-- The action of `G` on the invariants `A^N`, as a homomorphism to the endomorphism monoid. -/
noncomputable def quotientEnd : (G ⧸ N) →* AddMonoid.End (invariants N A) :=
  QuotientGroup.lift N (DistribMulAction.toAddMonoidEnd G (invariants N A)) (by
    intro n hn
    ext x
    exact x.2 ⟨n, hn⟩)

@[simp] theorem quotientEnd_mk' (g : G) :
    quotientEnd N (QuotientGroup.mk' N g) = DistribMulAction.toAddMonoidEnd G (invariants N A) g :=
  QuotientGroup.lift_mk' _ _ g

/-- The action of `G ⧸ N` on the invariants `A^N`. -/
noncomputable instance quotientSMul : SMul (G ⧸ N) (invariants N A) where
  smul q x := quotientEnd N q x

@[simp] theorem quotientSMul_mk' (g : G) (x : invariants N A) :
    (QuotientGroup.mk' N g) • x = g • x := by
  show quotientEnd N (QuotientGroup.mk' N g) x = g • x
  rw [quotientEnd_mk']
  rfl

noncomputable instance quotientDistribMulAction : DistribMulAction (G ⧸ N) (invariants N A) where
  one_smul x := by
    show quotientEnd N 1 x = x
    rw [map_one]
    rfl
  mul_smul q q' x := by
    show quotientEnd N (q * q') x = quotientEnd N q (quotientEnd N q' x)
    rw [map_mul]
    rfl
  smul_zero q := map_zero (quotientEnd N q)
  smul_add q x y := map_add (quotientEnd N q) x y

end Quotient

section Inflation

variable {G : Type u} {A : Type v} [Group G] [AddCommGroup A] [DistribMulAction G A]
variable (N : Subgroup G) [N.Normal]

/-- Inflation of `1`-cocycles: `Z¹(G ⧸ N, A^N) → Z¹(G, A)`. -/
noncomputable def infCocycle1 : Z1 (G ⧸ N) (invariants N A) →+ Z1 G A where
  toFun f := ⟨fun g => (f.1 (QuotientGroup.mk' N g) : A), by
    rw [mem_Z1_iff]
    intro g h
    have hf := congrArg (Subtype.val) (f.2 (QuotientGroup.mk' N g) (QuotientGroup.mk' N h))
    simp only [map_mul, AddSubgroup.coe_add, quotientSMul_mk'] at hf
    exact hf⟩
  map_zero' := by ext g; simp
  map_add' f f' := by ext g; simp

@[simp] theorem infCocycle1_apply (f : Z1 (G ⧸ N) (invariants N A)) (g : G) :
    (infCocycle1 N f : G → A) g = (f.1 (QuotientGroup.mk' N g) : A) := rfl

/-- Inflation of `2`-cocycles: `Z²(G ⧸ N, A^N) → Z²(G, A)`. -/
noncomputable def infCocycle2 : Z2 (G ⧸ N) (invariants N A) →+ Z2 G A where
  toFun c := ⟨fun p => (c.1 (QuotientGroup.mk' N p.1, QuotientGroup.mk' N p.2) : A), by
    rw [mem_Z2_iff]
    intro g h k
    have hc := congrArg (Subtype.val)
      (c.2 (QuotientGroup.mk' N g) (QuotientGroup.mk' N h) (QuotientGroup.mk' N k))
    simp only [map_mul, AddSubgroup.coe_add, quotientSMul_mk'] at hc
    exact hc⟩
  map_zero' := by ext g; simp
  map_add' c c' := by ext g; simp

@[simp] theorem infCocycle2_apply (c : Z2 (G ⧸ N) (invariants N A)) (g h : G) :
    (infCocycle2 N c : G × G → A) (g, h) =
      (c.1 (QuotientGroup.mk' N g, QuotientGroup.mk' N h) : A) := rfl

theorem infCocycle1_d0 (a : invariants N A) :
    ((infCocycle1 N ⟨d0 (G ⧸ N) (invariants N A) a,
        d0_mem_Z1 (G ⧸ N) (invariants N A) a⟩ : Z1 G A) : G → A) =
      d0 G A (a : A) := by
  funext g
  simp only [infCocycle1_apply, d0_apply, quotientSMul_mk']
  rfl

theorem infCocycle2_d1 (f : (G ⧸ N) → invariants N A) :
    ((infCocycle2 N ⟨d1 (G ⧸ N) (invariants N A) f,
        d1_mem_Z2 (G ⧸ N) (invariants N A) f⟩ : Z2 G A) : G × G → A) =
      d1 G A (fun g => (f (QuotientGroup.mk' N g) : A)) := by
  funext g
  obtain ⟨g₁, g₂⟩ := g
  simp only [infCocycle2_apply, d1_apply, map_mul, quotientSMul_mk']
  rfl

/-- The inflation map `H¹(G ⧸ N, A^N) → H¹(G, A)`. -/
noncomputable def infH1 : H1 (G ⧸ N) (invariants N A) →+ H1 G A :=
  QuotientAddGroup.lift
    ((B1 (G ⧸ N) (invariants N A)).comap (Z1 (G ⧸ N) (invariants N A)).subtype)
    ((H1π G A).comp (infCocycle1 N)) (by
      intro x hx
      have hx' : ((x : Z1 (G ⧸ N) (invariants N A)) : (G ⧸ N) → invariants N A) ∈
          B1 (G ⧸ N) (invariants N A) := by
        simpa using (AddSubgroup.mem_comap.mp hx)
      obtain ⟨a, ha⟩ := hx'
      have hthis : ((infCocycle1 N x : Z1 G A) : G → A) ∈ B1 G A := by
        refine ⟨(a : A), ?_⟩
        funext g
        have h := congrArg (fun y : invariants N A => (y : A))
          (congrFun ha (QuotientGroup.mk' N g))
        simp only [d0_apply, quotientSMul_mk'] at h
        have h2 : ((g • a - a : invariants N A) : A) = g • (a : A) - (a : A) := rfl
        rw [h2] at h
        simpa only [infCocycle1_apply, d0_apply] using h
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, H1π, QuotientAddGroup.mk'_apply,
        QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap]
      exact hthis)

/-- The inflation map `H²(G ⧸ N, A^N) → H²(G, A)`. -/
noncomputable def infH2 : H2 (G ⧸ N) (invariants N A) →+ H2 G A :=
  QuotientAddGroup.lift
    ((B2 (G ⧸ N) (invariants N A)).comap (Z2 (G ⧸ N) (invariants N A)).subtype)
    ((H2π G A).comp (infCocycle2 N)) (by
      intro x hx
      have hx' : ((x : Z2 (G ⧸ N) (invariants N A)) : (G ⧸ N) × (G ⧸ N) → invariants N A) ∈
          B2 (G ⧸ N) (invariants N A) := by
        simpa using (AddSubgroup.mem_comap.mp hx)
      obtain ⟨f, hf⟩ := hx'
      have hthis : ((infCocycle2 N x : Z2 G A) : G × G → A) ∈ B2 G A := by
        refine ⟨fun g => (f (QuotientGroup.mk' N g) : A), ?_⟩
        funext g
        obtain ⟨g₁, g₂⟩ := g
        have h := congrArg (fun y : invariants N A => (y : A))
          (congrFun hf (QuotientGroup.mk' N g₁, QuotientGroup.mk' N g₂))
        simp only [d1_apply, quotientSMul_mk'] at h
        have h2 : ((g₁ • f (QuotientGroup.mk' N g₂) -
            f (QuotientGroup.mk' N g₁ * QuotientGroup.mk' N g₂) +
            f (QuotientGroup.mk' N g₁) : invariants N A) : A) =
            g₁ • (f (QuotientGroup.mk' N g₂) : A) - (f (QuotientGroup.mk' N g₁ * QuotientGroup.mk' N g₂) : A) +
            (f (QuotientGroup.mk' N g₁) : A) := rfl
        rw [h2] at h
        simpa only [infCocycle2_apply, d1_apply, map_mul] using h
      rw [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, H2π, QuotientAddGroup.mk'_apply,
        QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap]
      exact hthis)

theorem infH1_H1π (f : Z1 (G ⧸ N) (invariants N A)) :
    infH1 N (A := A) (H1π (G ⧸ N) (invariants N A) f) = H1π G A (infCocycle1 N f) :=
  QuotientAddGroup.lift_mk' _ _ f

theorem infH2_H2π (c : Z2 (G ⧸ N) (invariants N A)) :
    infH2 N (A := A) (H2π (G ⧸ N) (invariants N A) c) = H2π G A (infCocycle2 N c) :=
  QuotientAddGroup.lift_mk' _ _ c

end Inflation

end Work.GroupCohomology
