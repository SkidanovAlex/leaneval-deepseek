import Mathlib.FieldTheory.Normal.Defs
import Submission.Work.Tate.CoindModule
import Submission.Work.Tate.SES
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v

namespace Work.Tate

open scoped BigOperators

section Diag

variable (G : Type u) (A : Type v) [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- The "diagonal" copy of `A` in the coinduced module `G → A`, consisting of the functions
`x ↦ x • a`.  It is the image of the natural injection `A → Coind(A)`. -/
def coindDiag : AddSubgroup (G → A) where
  carrier := Set.range fun a : A => (fun x : G => x • a : G → A)
  zero_mem' := ⟨0, by funext x; simp⟩
  add_mem' := by
    rintro f g ⟨a, rfl⟩ ⟨b, rfl⟩
    exact ⟨a + b, by funext x; simp [smul_add]⟩
  neg_mem' := by
    rintro f ⟨a, rfl⟩
    exact ⟨-a, by funext x; simp⟩

/-- The diagonal submodule is normal: the ambient `G → A` is an additive commutative group.
Recorded as an explicit instance so that instance search does not have to unfold the
commutativity of `G → A` (which becomes expensive for iterated twists). -/
instance instNormalCoindDiag : (coindDiag G A).Normal where
  conj_mem n _ g := by
    have h : g + n + -g = n := by abel
    rw [h]
    assumption

theorem mem_coindDiag_iff {φ : G → A} :
    φ ∈ coindDiag G A ↔ ∃ a : A, φ = fun x : G => x • a := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := h
    exact ⟨a, ha.symm⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl⟩

theorem coindDiag_invariant (γ : G) {φ : G → A} (hφ : φ ∈ coindDiag G A) :
    γ • φ ∈ coindDiag G A := by
  obtain ⟨a, rfl⟩ := hφ
  refine ⟨γ • a, funext fun x => ?_⟩
  rw [coind_smul_eq]
  exact (mul_smul x γ a).symm

/-! ## The induced action on the quotient -/

/-- The `G`-action on the quotient `Coind(A)/A`, induced by the coinduced action: it is the
unique action with `γ • (φ + A) = (γ • φ) + A`. -/
noncomputable instance instSMulQuotDiag : SMul G ((G → A) ⧸ coindDiag G A) where
  smul γ := Quotient.map (fun φ : G → A => γ • φ) (by
    intro φ ψ h
    have hh : -φ + ψ ∈ coindDiag G A := (QuotientAddGroup.leftRel_apply).mp h
    have key : γ • (-φ + ψ) = -(γ • φ) + γ • ψ := by rw [coind_smul_add, coind_smul_neg]
    refine (QuotientAddGroup.leftRel_apply).mpr ?_
    rw [← key]
    exact coindDiag_invariant G A γ hh)

theorem quot_smul_mk (γ : G) (φ : G → A) :
    (γ • (QuotientAddGroup.mk' (coindDiag G A) φ) : (G → A) ⧸ coindDiag G A)
      = QuotientAddGroup.mk' (coindDiag G A) (γ • φ) := rfl

noncomputable instance instDistribMulActionQuotDiag :
    DistribMulAction G ((G → A) ⧸ coindDiag G A) where
  one_smul x := by
    refine QuotientAddGroup.induction_on x ?_
    intro φ
    change (1 : G) • QuotientAddGroup.mk' (coindDiag G A) φ
      = QuotientAddGroup.mk' (coindDiag G A) φ
    rw [quot_smul_mk, coind_one_smul]
  mul_smul γ δ x := by
    refine QuotientAddGroup.induction_on x ?_
    intro φ
    change (γ * δ) • QuotientAddGroup.mk' (coindDiag G A) φ
      = γ • (δ • QuotientAddGroup.mk' (coindDiag G A) φ)
    rw [quot_smul_mk, quot_smul_mk, quot_smul_mk, coind_mul_smul]
  smul_zero γ := by
    change γ • QuotientAddGroup.mk' (coindDiag G A) (0 : G → A) = 0
    rw [quot_smul_mk, coind_smul_zero]
    rfl
  smul_add γ x y := by
    refine QuotientAddGroup.induction_on x ?_
    intro φ
    refine QuotientAddGroup.induction_on y ?_
    intro ψ
    change γ • (QuotientAddGroup.mk' (coindDiag G A) φ + QuotientAddGroup.mk' (coindDiag G A) ψ)
      = γ • QuotientAddGroup.mk' (coindDiag G A) φ + γ • QuotientAddGroup.mk' (coindDiag G A) ψ
    rw [← map_add, quot_smul_mk, quot_smul_mk, quot_smul_mk, coind_smul_add, map_add]

/-- The shifted module `A^* = Coind(A)/A`. -/
abbrev coindShift : Type (max u v) := (G → A) ⧸ coindDiag G A

theorem quot_smul_mk' (γ : G) (φ : G → A) :
    (γ • (QuotientAddGroup.mk' (coindDiag G A) φ) : coindShift G A)
      = QuotientAddGroup.mk' (coindDiag G A) (γ • φ) := rfl

end Diag

section SES

variable {G : Type u} {A : Type v} [Group G] [AddCommGroup A] [DistribMulAction G A]

/-- The inclusion `A → Coind(A)`, `a ↦ (x ↦ x • a)`, as an additive homomorphism. -/
def coindUnit (G : Type u) (A : Type v) [Group G] [AddCommGroup A] [DistribMulAction G A] :
    A →+ (G → A) where
  toFun a := fun x => x • a
  map_zero' := by funext x; simp
  map_add' a b := by funext x; simp [smul_add]

@[simp] theorem coindUnit_apply (a : A) (x : G) : coindUnit G A a x = x • a := rfl

/-- The inclusion is `G`-equivariant for the coinduced action. -/
theorem coindUnit_equiv (γ : G) (a : A) : coindUnit G A (γ • a) = γ • coindUnit G A a := by
  funext x
  change x • (γ • a) = (x * γ) • a
  exact (mul_smul x γ a).symm

/-- The projection `Coind(A) → A^*`. -/
noncomputable def coindProj (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] : (G → A) →+ coindShift G A :=
  QuotientAddGroup.mk' (coindDiag G A)

theorem coindProj_equiv (γ : G) (φ : G → A) :
    coindProj G A (γ • φ) = γ • coindProj G A φ := rfl

theorem coindProj_eq_zero_iff (φ : G → A) :
    coindProj G A φ = 0 ↔ φ ∈ coindDiag G A :=
  QuotientAddGroup.eq_zero_iff φ

/-- The short exact sequence `0 → A → Coind(A) → A^* → 0`. -/
noncomputable def coindSES (G : Type u) (A : Type v) [Group G] [AddCommGroup A]
    [DistribMulAction G A] : SES G A (G → A) (coindShift G A) where
  f := coindUnit G A
  g := coindProj G A
  f_equiv := coindUnit_equiv
  g_equiv := fun γ φ => coindProj_equiv γ φ
  f_injective := by
    intro a b hab
    have h := congrFun hab 1
    simpa [coindUnit] using h
  g_surjective := QuotientAddGroup.mk'_surjective _
  range_f_eq_ker_g := by
    ext φ
    constructor
    · rintro ⟨a, rfl⟩
      rw [AddMonoidHom.mem_ker, coindProj_eq_zero_iff]
      refine ⟨a, ?_⟩
      funext x
      rw [coindUnit_apply]
    · intro hφ
      rw [AddMonoidHom.mem_ker, coindProj_eq_zero_iff] at hφ
      obtain ⟨a, ha⟩ := hφ
      refine ⟨a, funext fun x => ?_⟩
      rw [coindUnit_apply]
      exact congrFun ha x

end SES

end Work.Tate
