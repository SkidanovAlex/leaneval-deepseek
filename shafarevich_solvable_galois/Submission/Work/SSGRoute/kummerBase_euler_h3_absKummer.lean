import Mathlib
import Submission.Work.AbsoluteKummer.Defs
import Submission.Work.AbsoluteKummer.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The third continuous cohomology `H³_c(G,M)`, and `d³ ∘ d² = 0`

The long exact sequence of a short exact sequence of discrete `G`-modules continues one step
beyond the workspace's `Work.AbsoluteKummer.H2`:

`… → H²(G,M') → H²(G,M) → H²(G,M'') → H³(G,M') → …`

and the *additivity of the Euler characteristic* used in the proof of Milne's local Euler
characteristic (ADT I.2.8) is exactly the statement that `H²(G,M) → H²(G,M'')` is onto, i.e. that
the connecting map `δ : H²(G,M'') → H³(G,M')` has the image of `H²(π)` as its kernel.  The
workspace's model stops at `H2`, so this file supplies

* `d3` — the inhomogeneous `3`-coboundary operator on `3`-cochains;
* `Z3`, `B3`, `H3` — the continuous `3`-cocycles, `3`-coboundaries and the third continuous
  cohomology, defined exactly as `AbsoluteKummer.Z2`, `B2`, `H2` one degree up;
* `d3_d2` — `d³ ∘ d² = 0`: the identity that makes `d²` of a (necessarily *non*-cocycle) lift of a
  `2`-cocycle a `3`-cocycle, and hence makes the connecting map well defined.
-/

open scoped Classical

namespace Work.SSGRoute

variable {G : Type*} [TopologicalSpace G] [Group G]

/-! ## The differential `d³` -/

/-- The inhomogeneous `3`-coboundary operator on `3`-cochains:
`d³c (g,h,k,l) = g·c(h,k,l) - c(gh,k,l) + c(g,hk,l) - c(g,h,kl) + c(g,h,k)`. -/
def d3 {A : Type*} [AddCommGroup A] [DistribMulAction G A] :
    (G × G × G → A) →+ (G × G × G × G → A) where
  toFun c p := p.1 • c (p.2.1, p.2.2.1, p.2.2.2) - c (p.1 * p.2.1, p.2.2.1, p.2.2.2)
    + c (p.1, p.2.1 * p.2.2.1, p.2.2.2) - c (p.1, p.2.1, p.2.2.1 * p.2.2.2)
    + c (p.1, p.2.1, p.2.2.1)
  map_zero' := by funext p; simp
  map_add' c c' := by
    funext p
    simp only [Pi.add_apply, smul_add]
    abel

@[simp] theorem d3_apply {A : Type*} [AddCommGroup A] [DistribMulAction G A]
    (c : G × G × G → A) (g h k l : G) :
    d3 c (g, h, k, l) = g • c (h, k, l) - c (g * h, k, l) + c (g, h * k, l)
      - c (g, h, k * l) + c (g, h, k) := rfl

/-- **`d³ ∘ d² = 0`.**  (`d²` is `Work.GroupCohomology.d2`, the differential of a `2`-cochain; the
reason this matters is that a *lift* of a `2`-cocycle along a surjection is not a cocycle, and this
identity is what makes its `d²` a `3`-cocycle.) -/
theorem d3_d2 {A : Type*} [AddCommGroup A] [DistribMulAction G A] (c : G × G → A) :
    d3 (Work.GroupCohomology.d2 G A c) = 0 := by
  funext p
  obtain ⟨g, h, k, l⟩ := p
  simp only [d3_apply, Work.GroupCohomology.d2_apply, Pi.zero_apply, smul_sub, smul_add,
    smul_neg, mul_smul, mul_assoc, neg_smul, one_smul]
  abel

/-! ## Local constancy of the differential (three variables) -/

/-- Local constancy of `x ↦ g x • f x` for a continuous `g` and a locally constant `f`.  (The
workspace's `isLocallyConstant_smul_comp` is the case `X = G × G`, `g = Prod.fst`; the degree-`3`
differential is a function of three variables, so the general form is needed.) -/
theorem isLocallyConstant_smul_comp' [IsTopologicalGroup G] {M : Type*} [AddCommGroup M]
    [DistribMulAction G M] (h : Work.AbsoluteKummer.IsDiscreteModule G M)
    {X : Type*} [TopologicalSpace X] {g : X → G} (hg : Continuous g) {f : X → M}
    (hf : Work.AbsoluteKummer.IsLocallyConstant f) :
    Work.AbsoluteKummer.IsLocallyConstant (fun x => g x • f x) := by
  intro x
  obtain ⟨W, hWo, hxW, hWc⟩ := hf x
  refine ⟨{x' | (g x)⁻¹ * g x' ∈ MulAction.stabilizer G (f x)} ∩ W, ?_, ?_, ?_⟩
  · exact ((Work.AbsoluteKummer.isOpen_smul_stabilizer h (g x) (f x)).preimage hg).inter hWo
  · exact ⟨Work.AbsoluteKummer.mem_self_smul_stabilizer (g x) (f x), hxW⟩
  · rintro x' ⟨h1, h2⟩
    show g x' • f x' = g x • f x
    rw [hWc x' h2]
    exact Work.AbsoluteKummer.smul_eq_of_mem_smul_stabilizer h1

/-- **`d²` of a locally constant `2`-cochain is locally constant.** -/
theorem isLocallyConstant_d2 [IsTopologicalGroup G] {M : Type*} [AddCommGroup M]
    [DistribMulAction G M] (h : Work.AbsoluteKummer.IsDiscreteModule G M) {c : G × G → M}
    (hc : Work.AbsoluteKummer.IsLocallyConstant c) :
    Work.AbsoluteKummer.IsLocallyConstant (Work.GroupCohomology.d2 G M c) := by
  have h1 : Work.AbsoluteKummer.IsLocallyConstant
      (fun p : G × G × G => p.1 • c (p.2.1, p.2.2)) :=
    isLocallyConstant_smul_comp' h continuous_fst
      (hc.comp (continuous_snd.fst.prodMk continuous_snd.snd))
  have h2 : Work.AbsoluteKummer.IsLocallyConstant
      (fun p : G × G × G => c (p.1 * p.2.1, p.2.2)) :=
    hc.comp ((continuous_fst.mul continuous_snd.fst).prodMk continuous_snd.snd)
  have h3 : Work.AbsoluteKummer.IsLocallyConstant
      (fun p : G × G × G => c (p.1, p.2.1 * p.2.2)) :=
    hc.comp (continuous_fst.prodMk (continuous_snd.fst.mul continuous_snd.snd))
  have h4 : Work.AbsoluteKummer.IsLocallyConstant
      (fun p : G × G × G => c (p.1, p.2.1)) :=
    hc.comp (continuous_fst.prodMk continuous_snd.fst)
  change Work.AbsoluteKummer.IsLocallyConstant (fun p : G × G × G =>
    p.1 • c (p.2.1, p.2.2) - c (p.1 * p.2.1, p.2.2) + c (p.1, p.2.1 * p.2.2)
      - c (p.1, p.2.1))
  exact ((h1.sub h2).add h3).sub h4

/-! ## The third continuous cohomology -/

section Cohom

variable (G : Type*) [TopologicalSpace G] [Group G] {M : Type*} [AddCommGroup M]
  [DistribMulAction G M]

/-- The continuous `3`-cochains `C³_c(G, M) = (G × G × G → M)`, locally constant. -/
def C3c : AddSubgroup (G × G × G → M) where
  carrier := {f | Work.AbsoluteKummer.IsLocallyConstant f}
  zero_mem' := Work.AbsoluteKummer.isLocallyConstant_const 0
  add_mem' := fun hf hg => hf.add hg
  neg_mem' := fun hf => hf.neg

/-- The continuous `3`-cocycles `Z³_c(G,M) = ker d³ ∩ C³_c(G,M)`. -/
def Z3 : AddSubgroup (G × G × G → M) :=
  (d3 (G := G) (A := M)).ker ⊓ C3c G

/-- The continuous `3`-coboundaries `B³_c(G,M) = d²(C²_c(G,M))`. -/
def B3 : AddSubgroup (G × G × G → M) :=
  AddSubgroup.map (Work.GroupCohomology.d2 G M) (Work.AbsoluteKummer.C2c G M)

/-- The third continuous cohomology `H³(G,M) = Z³_c/B³_c`. -/
abbrev H3 : Type _ :=
  (Z3 G : AddSubgroup (G × G × G → M)) ⧸ ((B3 G).comap (Z3 G).subtype)

/-- A `3`-cochain is a continuous `3`-cocycle iff it is locally constant and killed by `d³`. -/
theorem mem_Z3_iff {c : G × G × G → M} :
    c ∈ Z3 G ↔ d3 c = 0 ∧ Work.AbsoluteKummer.IsLocallyConstant c := Iff.rfl

/-- A `3`-cochain is a continuous `3`-coboundary iff it is `d²` of a locally constant
`2`-cochain. -/
theorem mem_B3_iff {c : G × G × G → M} :
    c ∈ B3 G ↔ ∃ b : G × G → M, Work.AbsoluteKummer.IsLocallyConstant b ∧
      Work.GroupCohomology.d2 G M b = c :=
  AddSubgroup.mem_map

/-- The quotient map `Z³_c(G,M) → H³(G,M)`. -/
noncomputable def H3π : (Z3 (M := M) G) →+ H3 (M := M) G :=
  QuotientAddGroup.mk' ((B3 G).comap (Z3 G).subtype)

theorem H3π_apply (c : Z3 (M := M) G) :
    H3π G c = QuotientAddGroup.mk' ((B3 G).comap (Z3 G).subtype) c := rfl

theorem H3π_eq_zero_iff (c : Z3 (M := M) G) :
    H3π G c = 0 ↔ (c : G × G × G → M) ∈ B3 G := by
  rw [H3π, QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_comap]
  rfl

end Cohom

end Work.SSGRoute
