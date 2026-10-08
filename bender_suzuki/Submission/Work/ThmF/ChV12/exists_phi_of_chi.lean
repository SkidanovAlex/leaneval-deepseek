import Mathlib
import Submission.Work.ThmF.ChV12.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV12.exists_phi_of_chi` — Peterfalvi II, Ch. V: a linear character of `H`

In the split rank-one situation `H = Q ⋊ D`, `D = H ⊓ H^t = twoPoint H t`, every linear
character of `H` that is trivial on `Q` factors through `H ⧸ Q ≅ D`, i.e. it is the pull-back of
a linear character of `D`.  Concretely: a linear character `χ ≠ 1` of `D` which is trivial on
`K = J(D,t) = Kset H t` (so that, on the level of the quotient, it is trivial on `KQ/Q`) yields
a linear character `φ ≠ 1` of `H` with `Q ≤ ker φ` and `Kset H t ⊆ ker φ`.

The map `D × Q → H`, `(d,q) ↦ dq`, is a bijection (`splitEquiv`), and because `D` normalises `Q`
the projection onto the first factor is multiplicative: the `D`-component of a product is the
product of the `D`-components.  Hence `φ x := χ (projD x)` is a group homomorphism, and it is
trivial on `Q` and on `K`.

Everything used here is elementary; neither 2-transitivity nor strong embeddedness is needed,
only `H = Q ⋊ D` with `Q ⊴ H`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.ThmF.ChV12

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF

variable {G : Type} [Group G] {H Q : Subgroup G} {t : G}

/-! ## The two components of an element of `H` for the splitting `H = D ⋊ Q` -/

/-- `D = twoPoint H t = H ⊓ H^t` is contained in `H`; this is the corresponding inclusion on
elements. -/
def inclD (d : ↥(twoPoint H t)) : ↥H := ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩

/-- The `D`-component of `x ∈ H` under the bijection `D × Q ≃ H`. -/
noncomputable def projD (h : IsSplitRankOne H Q t) (x : ↥H) : ↥(twoPoint H t) :=
  ((splitEquiv h).symm x).1

/-- The `Q`-component of `x ∈ H` under the bijection `D × Q ≃ H`. -/
noncomputable def projQ (h : IsSplitRankOne H Q t) (x : ↥H) : ↥Q :=
  ((splitEquiv h).symm x).2

/-- The defining formula of the splitting `D × Q ≃ H`. -/
lemma splitEquiv_apply_coe (h : IsSplitRankOne H Q t) (d : ↥(twoPoint H t)) (q : ↥Q) :
    ((splitEquiv h (d, q) : ↥H) : G) = (d : G) * (q : G) := rfl

/-- `x = projD x * projQ x` in `G`. -/
lemma projD_mul_projQ (h : IsSplitRankOne H Q t) (x : ↥H) :
    ((projD h x : G) * (projQ h x : G)) = (x : G) :=
  congrArg (fun z : ↥H => (z : G)) (Equiv.apply_symm_apply (splitEquiv h) x)

lemma projD_one (h : IsSplitRankOne H Q t) : projD h 1 = 1 := by
  have h1 : splitEquiv h ((1 : ↥(twoPoint H t)), (1 : ↥Q)) = 1 := by
    apply Subtype.ext
    rw [splitEquiv_apply_coe h 1 1]
    simp
  have h2 := (Equiv.symm_apply_eq (splitEquiv h)).mpr h1.symm
  show ((splitEquiv h).symm 1).1 = 1
  rw [h2]

/-- The `D`-component of an element of `D` is itself. -/
lemma projD_inclD (h : IsSplitRankOne H Q t) (d : ↥(twoPoint H t)) :
    projD h (inclD d) = d := by
  have h1 : splitEquiv h (d, (1 : ↥Q)) = inclD d := by
    apply Subtype.ext
    rw [splitEquiv_apply_coe h d 1]
    simp [inclD]
  have h2 := (Equiv.symm_apply_eq (splitEquiv h)).mpr h1.symm
  show ((splitEquiv h).symm (inclD d)).1 = d
  rw [h2]

/-- The `D`-component of an element of `Q` is trivial. -/
lemma projD_of_mem_Q (h : IsSplitRankOne H Q t) (x : ↥H) (hx : (x : G) ∈ Q) :
    projD h x = 1 := by
  have h1 : splitEquiv h ((1 : ↥(twoPoint H t)), (⟨(x : G), hx⟩ : ↥Q)) = x := by
    apply Subtype.ext
    rw [splitEquiv_apply_coe h 1 (⟨(x : G), hx⟩ : ↥Q)]
    simp
  have h2 := (Equiv.symm_apply_eq (splitEquiv h)).mpr h1.symm
  show ((splitEquiv h).symm x).1 = 1
  rw [h2]

/-- The `D`-component of an element of `D` is itself (stated with an explicit membership
proof). -/
lemma projD_of_mem_D (h : IsSplitRankOne H Q t) (x : ↥H) (hx : (x : G) ∈ twoPoint H t) :
    projD h x = ⟨(x : G), hx⟩ := by
  have h1 : splitEquiv h ((⟨(x : G), hx⟩ : ↥(twoPoint H t)), (1 : ↥Q)) = x := by
    apply Subtype.ext
    rw [splitEquiv_apply_coe h (⟨(x : G), hx⟩ : ↥(twoPoint H t)) 1]
    simp
  have h2 := (Equiv.symm_apply_eq (splitEquiv h)).mpr h1.symm
  show ((splitEquiv h).symm x).1 = _
  rw [h2]

/-- The projection onto the `D`-component is multiplicative: here `D ≤ N_G(Q)` is used. -/
lemma projD_mul (h : IsSplitRankOne H Q t) (x y : ↥H) :
    projD h (x * y) = projD h x * projD h y := by
  have hx : (projD h x : G) * (projQ h x : G) = (x : G) := projD_mul_projQ h x
  have hy : (projD h y : G) * (projQ h y : G) = (y : G) := projD_mul_projQ h y
  have hd2 : (projD h y : G) ∈ Subgroup.normalizer (Q : Set G) :=
    split_le_normalizer_twoPoint h (projD h y).2
  have hconj : (projD h y : G)⁻¹ * (projQ h x : G) * (projD h y : G) ∈ Q :=
    ((Subgroup.mem_normalizer_iff''.mp hd2) (projQ h x : G)).mp (projQ h x).2
  have hkey : splitEquiv h (projD h x * projD h y,
      (⟨(projD h y : G)⁻¹ * (projQ h x : G) * (projD h y : G) * (projQ h y : G),
        Q.mul_mem hconj (projQ h y).2⟩ : ↥Q)) = x * y := by
    apply Subtype.ext
    rw [splitEquiv_apply_coe h (projD h x * projD h y)
      (⟨(projD h y : G)⁻¹ * (projQ h x : G) * (projD h y : G) * (projQ h y : G),
        Q.mul_mem hconj (projQ h y).2⟩ : ↥Q)]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hx, ← hy]
    group
  have h2 := (Equiv.symm_apply_eq (splitEquiv h)).mpr hkey.symm
  show ((splitEquiv h).symm (x * y)).1 = projD h x * projD h y
  rw [h2]

/-! ## The pulled-back linear character -/

/-- The linear character of `H` obtained from a linear character `χ` of `D = twoPoint H t` by
composition with the `D`-component projection, i.e. the pull-back of `χ` along the isomorphism
`H ⧸ Q ≅ D`. -/
noncomputable def phiHom (h : IsSplitRankOne H Q t) (χ : ↥(twoPoint H t) →* ℂˣ) :
    ↥H →* ℂˣ where
  toFun x := χ (projD h x)
  map_one' := by
    show χ (projD h 1) = 1
    rw [projD_one h]
    exact map_one χ
  map_mul' := by
    intro x y
    show χ (projD h (x * y)) = χ (projD h x) * χ (projD h y)
    rw [projD_mul h x y]
    exact map_mul χ _ _

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint Work.ThmF in theorem exists_phi_of_chi {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} {t : G} (h : IsSplitRankOne H Q t) (χ : ↥(twoPoint H t) →* ℂˣ) (hχ : χ ≠ 1) (hχK : ∀ x : ↥(twoPoint H t), (x : G) ∈ Kset H t → χ x = 1) : ∃ φ : ↥H →* ℂˣ, φ ≠ 1 ∧ (∀ x : ↥H, (x : G) ∈ Q → φ x = 1) ∧ (∀ x : ↥H, (x : G) ∈ Kset H t → φ x = 1) := by
  refine ⟨phiHom h χ, ?_, ?_, ?_⟩
  · intro hcontra
    apply hχ
    refine MonoidHom.ext (fun d => ?_)
    have hd : phiHom h χ (inclD d) = 1 := by
      rw [hcontra]
      rfl
    rw [show phiHom h χ (inclD d) = χ d from by
        show χ (projD h (inclD d)) = χ d
        rw [projD_inclD h d]] at hd
    exact hd
  · intro x hx
    show χ (projD h x) = 1
    rw [projD_of_mem_Q h x hx]
    exact map_one χ
  · intro x hxK
    show χ (projD h x) = 1
    rw [projD_of_mem_D h x hxK.1]
    exact hχK ⟨(x : G), hxK.1⟩ hxK

end Work.ThmF.ChV12
