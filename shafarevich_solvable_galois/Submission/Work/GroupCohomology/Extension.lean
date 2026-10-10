import Mathlib.Tactic.Abel
import Mathlib.Algebra.Group.MinimalAxioms
import Mathlib.GroupTheory.GroupExtension.Defs
import Submission.Work.GroupCohomology.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v w

namespace Work.GroupCohomology

open Multiplicative

section Twisted

variable (Q : Type u) (A : Type v) [Group Q] [AddCommGroup A] [DistribMulAction Q A]

/-! ## The twisted product on `A × Q` -/

/-- The multiplication on `A × Q` twisted by a `2`-cochain `c`. -/
def twMul (c : Q × Q → A) (x y : A × Q) : A × Q :=
  (x.1 + x.2 • y.1 + c (x.2, y.2), x.2 * y.2)

/-- The inverse for the twisted multiplication twisted by a `2`-cochain `c`. -/
def twInv (c : Q × Q → A) (x : A × Q) : A × Q :=
  (-(x.2⁻¹ • x.1) - c (x.2⁻¹, x.2), x.2⁻¹)

/-- The candidate identity `(0, 1)` for the twisted multiplication. -/
def twOne : A × Q := (0, 1)

@[simp] theorem twMul_apply (c : Q × Q → A) (x y : A × Q) :
    twMul Q A c x y = (x.1 + x.2 • y.1 + c (x.2, y.2), x.2 * y.2) := rfl

@[simp] theorem twInv_apply (c : Q × Q → A) (x : A × Q) :
    twInv Q A c x = (-(x.2⁻¹ • x.1) - c (x.2⁻¹, x.2), x.2⁻¹) := rfl

@[simp] theorem twOne_apply : twOne Q A = (0, 1) := rfl

/-- The twisted multiplication is associative, for a `2`-cocycle `c`. -/
theorem twMul_assoc (c : Q × Q → A) (hc : c ∈ Z2 Q A) (x y z : A × Q) :
    twMul Q A c (twMul Q A c x y) z = twMul Q A c x (twMul Q A c y z) := by
  obtain ⟨a, q⟩ := x
  obtain ⟨b, r⟩ := y
  obtain ⟨d, s⟩ := z
  have key : c (q * r, s) = q • c (r, s) + c (q, r * s) - c (q, r) := by
    rw [← hc q r s]; abel
  refine Prod.ext ?_ ?_
  · simp only [twMul, key, smul_add, mul_smul]
    abel
  · simp only [twMul, mul_assoc]

/-- `(0, 1)` is a left identity for the twisted multiplication, when `c` is a normalized
`2`-cocycle. -/
theorem twOne_mul (c : Q × Q → A) (hc : c ∈ Z2 Q A) (h1 : c (1, 1) = 0) (x : A × Q) :
    twMul Q A c (twOne Q A) x = x := by
  obtain ⟨a, q⟩ := x
  have key : c (1, q) = 0 := by rw [Z2.map_one_fst Q A hc q, h1]
  refine Prod.ext ?_ ?_
  · simp only [twMul, twOne, key, one_smul, zero_add, add_zero]
  · simp only [twMul, twOne, one_mul]

/-- The twisted inverse is a left inverse, when `c` is a normalized `2`-cocycle. -/
theorem twInv_mul (c : Q × Q → A) (x : A × Q) :
    twMul Q A c (twInv Q A c x) x = twOne Q A := by
  obtain ⟨a, q⟩ := x
  refine Prod.ext ?_ ?_
  · simp only [twMul, twInv, twOne]
    abel
  · simp only [twMul, twInv, twOne, inv_mul_cancel]

/-- The group structure on `A × Q` with multiplication twisted by a normalized `2`-cocycle `c`. -/
noncomputable def twGroup (c : Q × Q → A) (hc : c ∈ Z2 Q A) (h1 : c (1, 1) = 0) :
    Group (A × Q) := by
  letI : Mul (A × Q) := ⟨twMul Q A c⟩
  letI : One (A × Q) := ⟨twOne Q A⟩
  letI : Inv (A × Q) := ⟨twInv Q A c⟩
  exact Group.ofLeftAxioms (twMul_assoc Q A c hc) (twOne_mul Q A c hc h1) (twInv_mul Q A c)

/-! ## Normalizing a `2`-cocycle -/

/-- The normalization `c (q, r) - c (q, 1)` of a `2`-cochain.  For a cocycle this is a cocycle,
cohomologous to `c`, which vanishes on `(1, 1)`. -/
def normCocycle (c : Q × Q → A) : Q × Q → A := fun p => c p - c (p.1, 1)

@[simp] theorem normCocycle_apply (c : Q × Q → A) (q r : Q) :
    normCocycle Q A c (q, r) = c (q, r) - c (q, 1) := rfl

theorem normCocycle_mem (c : Q × Q → A) (hc : c ∈ Z2 Q A) : normCocycle Q A c ∈ Z2 Q A := by
  rw [mem_Z2_iff]
  intro g h k
  have h1 : c (g * h, k) + c (g, h) = g • c (h, k) + c (g, h * k) := hc g h k
  have h2 : c (g * h, 1) = g • c (h, 1) := by
    rw [Z2.map_one_snd Q A hc (g * h), mul_smul, Z2.map_one_snd Q A hc h]
  simp only [normCocycle_apply, h2]
  have key : c (g * h, k) = g • c (h, k) + c (g, h * k) - c (g, h) := by
    rw [← h1]; abel
  rw [key, smul_sub]
  abel

theorem normCocycle_one (c : Q × Q → A) : normCocycle Q A c (1, 1) = 0 := by
  simp

/-- Conjugating `(a, 1)` by `(0, q)` in the twisted product gives `(q • a, 1)`: the twisted
product induces the prescribed action of `Q` on `A`. -/
theorem twConjAct (c : Q × Q → A) (hc : c ∈ Z2 Q A) (h1 : c (1, 1) = 0) (q : Q) (a : A) :
    twMul Q A c (twMul Q A c (0, q) (a, 1)) (twInv Q A c (0, q)) = (q • a, 1) := by
  have hq : c (q, 1) = 0 := by rw [Z2.map_one_snd Q A hc q, h1, smul_zero]
  have h1q : c (1, q) = 0 := by rw [Z2.map_one_fst Q A hc q, h1]
  have hqq : c (q, q⁻¹) = q • c (q⁻¹, q) := by
    have h := hc q q⁻¹ q
    rw [mul_inv_cancel, inv_mul_cancel, h1q, hq] at h
    simpa using h
  have hstep : twMul Q A c (0, q) (a, 1) = (q • a, q) := by
    refine Prod.ext ?_ ?_
    · simp only [twMul, hq, mul_one, zero_add, add_zero]
    · simp only [twMul, mul_one]
  have hinv : twInv Q A c (0, q) = (-c (q⁻¹, q), q⁻¹) := by
    refine Prod.ext ?_ ?_
    · simp only [twInv, smul_zero, neg_zero, zero_sub]
    · simp only [twInv]
  rw [hstep, hinv]
  refine Prod.ext ?_ ?_
  · simp only [twMul, hqq, mul_inv_cancel, smul_neg]
    abel
  · simp only [twMul, mul_inv_cancel]

/-! ## Group extensions of `Q` by `A` with prescribed action -/

/-- A group extension `1 → A → E → Q → 1` whose conjugation action on `A` (well defined since `A`
is abelian) is the prescribed `DistribMulAction Q A`. -/
structure Extension (Q : Type u) (A : Type v) [Group Q] [AddCommGroup A]
    [DistribMulAction Q A] where
  /-- the middle group -/
  E : Type (max u v)
  [groupE : Group E]
  /-- the underlying short exact sequence -/
  ext : GroupExtension (Multiplicative A) E Q
  /-- conjugation gives back the prescribed action on `A` -/
  conjAct_eq : ∀ (q : Q) (a : A), ∃ e : E, ext.rightHom e = q ∧
    ext.conjAct e (Multiplicative.ofAdd a) = Multiplicative.ofAdd (q • a)

namespace Extension

/-- Isomorphisms of extensions of `Q` by `A`: isomorphisms of the middle groups compatible with
the inclusions of `A` and the projections to `Q`. -/
abbrev Equiv {Q : Type u} {A : Type v} [Group Q] [AddCommGroup A] [DistribMulAction Q A]
    (X Y : Extension Q A) : Type (max u v) :=
  letI := X.groupE
  letI := Y.groupE
  X.ext.Equiv Y.ext

/-- A set-theoretic section of an extension of `Q` by `A`. -/
abbrev Section {Q : Type u} {A : Type v} [Group Q] [AddCommGroup A] [DistribMulAction Q A]
    (X : Extension Q A) : Type (max u v) :=
  letI := X.groupE
  X.ext.Section

/-- A homomorphic section (a splitting) of an extension of `Q` by `A`. -/
abbrev Splitting {Q : Type u} {A : Type v} [Group Q] [AddCommGroup A] [DistribMulAction Q A]
    (X : Extension Q A) : Type (max u v) :=
  letI := X.groupE
  X.ext.Splitting

/-- The extension attached to a normalized `2`-cocycle `c`: the set `A × Q` with the twisted
multiplication `(a, q) * (b, r) = (a + q • b + c (q, r), q * r)`. -/
noncomputable def ofNormalized (c : Q × Q → A) (hc : c ∈ Z2 Q A) (h1 : c (1, 1) = 0) :
    Extension Q A :=
  letI : Group (A × Q) := twGroup Q A c hc h1
  let S : GroupExtension (Multiplicative A) (A × Q) Q :=
    { inl :=
        { toFun := fun a => (Multiplicative.toAdd a, 1)
          map_one' := rfl
          map_mul' := by
            intro a b
            show (Multiplicative.toAdd (a * b), 1)
              = twMul Q A c (Multiplicative.toAdd a, 1) (Multiplicative.toAdd b, 1)
            refine Prod.ext ?_ ?_
            · simp only [twMul, h1, one_smul, add_zero]
              rfl
            · simp only [twMul, mul_one] }
      rightHom :=
        { toFun := Prod.snd
          map_one' := rfl
          map_mul' := fun x y => rfl }
      inl_injective := fun a b h => by
        have h' : Multiplicative.toAdd a = Multiplicative.toAdd b := (Prod.ext_iff.mp h).1
        simpa using congrArg Multiplicative.ofAdd h'
      range_inl_eq_ker_rightHom := by
        ext x
        constructor
        · rintro ⟨a, rfl⟩
          rfl
        · intro hx
          refine ⟨Multiplicative.ofAdd x.1, ?_⟩
          refine Prod.ext ?_ ?_
          · rfl
          · exact hx.symm
      rightHom_surjective := fun q => ⟨(0, q), rfl⟩ }
  { E := A × Q
    groupE := inferInstance
    ext := S
    conjAct_eq := by
      intro q a
      refine ⟨(0, q), rfl, ?_⟩
      apply S.inl_injective
      rw [GroupExtension.inl_conjAct_comm]
      exact twConjAct Q A c hc h1 q a }

/-- The group extension attached to a `2`-cocycle `c`, normalized at `(1, 1)`. -/
noncomputable def ofCocycle (c : Z2 Q A) : Extension Q A :=
  ofNormalized Q A (normCocycle Q A c) (normCocycle_mem Q A c c.2) (normCocycle_one Q A c)

@[simp] theorem ofNormalized_E (c : Q × Q → A) (hc : c ∈ Z2 Q A) (h1 : c (1, 1) = 0) :
    (ofNormalized Q A c hc h1).E = (A × Q) := rfl

@[simp] theorem ofCocycle_E (c : Z2 Q A) : (ofCocycle Q A c).E = (A × Q) := rfl

@[simp] theorem ofNormalized_groupE (c : Q × Q → A) (hc : c ∈ Z2 Q A) (h1 : c (1, 1) = 0) :
    (ofNormalized Q A c hc h1).groupE = twGroup Q A c hc h1 := rfl

@[simp] theorem ofCocycle_groupE (c : Z2 Q A) :
    (ofCocycle Q A c).groupE = twGroup Q A (normCocycle Q A c)
      (normCocycle_mem Q A c c.2) (normCocycle_one Q A c) := rfl

end Extension

end Twisted


end Work.GroupCohomology
