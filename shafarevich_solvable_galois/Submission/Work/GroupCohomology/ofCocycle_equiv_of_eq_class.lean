/-
Copyright (c) 2025. All rights reserved.

# Cohomologous `2`-cocycles define equivalent extensions

The extension `Extension.ofCocycle Q A c` attached to a `2`-cocycle `c` depends, up to
isomorphism of extensions of `Q` by `A`, only on the cohomology class of `c`:

`ofCocycle_equiv_of_eq_class` : if `H2π c = H2π c'` in `H²(Q, A)`, then the two extensions
`ofCocycle Q A c` and `ofCocycle Q A c'` are equivalent.

## Strategy

* `c - c' ∈ B²(Q, A)`, say `c - c' = d¹ f` for a `1`-cochain `f`.
* For the normalizations `nc = normCocycle c`, `nc' = normCocycle c'` one computes
  `nc - nc' = d¹ g` with `g q = f q - f 1` (and `g 1 = 0`).
* If two *normalized* cocycles `c`, `c'` satisfy `c - c' = d¹ g` with `g 1 = 0`, the map
  `(a, q) ↦ (a + g q, q)` is an isomorphism of the twisted groups `twGroup Q A c ≃* twGroup Q A c'`
  fixing `A × 1` pointwise and commuting with the projections to `Q`; hence it is an
  equivalence of the associated extensions.  This is `ofNormalized_equiv_of_d1`.

## Main results

* `Work.GroupCohomology.ofNormalized_twistMulEquiv` : the twisted groups `twGroup Q A c` and
  `twGroup Q A c'` are isomorphic when `c - c' = d¹ g`.
* `Work.GroupCohomology.ofNormalized_equiv_of_d1` : the corresponding equivalence of extensions.
* `Work.GroupCohomology.ofCocycle_equiv_of_eq_class` : cohomologous cocycles give equivalent
  extensions, the statement requested.
-/
import Mathlib
import Submission.Work.GroupCohomology.Extension
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.GroupCohomology

variable (Q : Type*) (A : Type*) [Group Q] [AddCommGroup A] [DistribMulAction Q A]

/-! ## The twisted product for two cocycles differing by a coboundary -/

/-- If the `2`-cochains `c`, `c'` on `Q` differ by the coboundary of `g` (i.e. `c - c' = d¹ g`),
then `(a, q) ↦ (a + g q, q)` is an isomorphism from `A × Q` with multiplication `twMul Q A c` to
`A × Q` with multiplication `twMul Q A c'`; in other words an isomorphism
`twGroup Q A c ≃* twGroup Q A c'` of the twisted products. -/
noncomputable def ofNormalized_twistMulEquiv (c c' : Q × Q → A) (g : Q → A)
    (hg : ∀ q r : Q, d1 Q A g (q, r) = c (q, r) - c' (q, r)) :
    @MulEquiv (A × Q) (A × Q) ⟨twMul Q A c⟩ ⟨twMul Q A c'⟩ :=
  @MulEquiv.mk (A × Q) (A × Q) ⟨twMul Q A c⟩ ⟨twMul Q A c'⟩
    (Equiv.mk (fun x => (x.1 + g x.2, x.2)) (fun x => (x.1 - g x.2, x.2))
      (by intro x; obtain ⟨a, q⟩ := x; refine Prod.ext ?_ ?_ <;> simp)
      (by intro x; obtain ⟨a, q⟩ := x; refine Prod.ext ?_ ?_ <;> simp))
    (by
      intro x y
      obtain ⟨a, q⟩ := x
      obtain ⟨b, r⟩ := y
      change (a + q • b + c (q, r) + g (q * r), q * r)
        = (a + g q + q • (b + g r) + c' (q, r), q * r)
      refine Prod.ext ?_ ?_
      · have h1 := hg q r
        simp only [d1_apply] at h1
        have key : c (q, r) = c' (q, r) + (q • g r - g (q * r) + g q) := by rw [h1]; abel
        rw [key]
        simp only [smul_add]
        abel
      · rfl)

@[simp] theorem ofNormalized_twistMulEquiv_apply (c c' : Q × Q → A) (g : Q → A)
    (hg : ∀ q r : Q, d1 Q A g (q, r) = c (q, r) - c' (q, r)) (x : A × Q) :
    ofNormalized_twistMulEquiv Q A c c' g hg x = (x.1 + g x.2, x.2) := rfl

/-! ## The induced equivalence of extensions -/

/-- Two *normalized* `2`-cocycles `c`, `c'` (i.e. `c (1, 1) = 0 = c' (1, 1)`) whose difference is
the coboundary `d¹ g` of a cochain `g` vanishing at `1` define equivalent group extensions of `Q`
by `A`: the map `(a, q) ↦ (a + g q, q)` is an isomorphism of the middle groups which is the
identity on `A` and commutes with the projections to `Q`. -/
theorem ofNormalized_equiv_of_d1 (c c' : Q × Q → A) (hc : c ∈ Z2 Q A) (h1 : c (1, 1) = 0)
    (hc' : c' ∈ Z2 Q A) (h1' : c' (1, 1) = 0) (g : Q → A) (hg1 : g 1 = 0)
    (hg : ∀ q r : Q, d1 Q A g (q, r) = c (q, r) - c' (q, r)) :
    Nonempty (Extension.Equiv (Extension.ofNormalized Q A c hc h1)
      (Extension.ofNormalized Q A c' hc' h1')) := by
  let X := Extension.ofNormalized Q A c hc h1
  let Y := Extension.ofNormalized Q A c' hc' h1'
  change Nonempty (Extension.Equiv X Y)
  letI : Group X.E := X.groupE
  letI : Group Y.E := Y.groupE
  refine ⟨GroupExtension.Equiv.mk (ofNormalized_twistMulEquiv Q A c c' g hg) ?_ ?_⟩
  · ext a
    show ((Multiplicative.toAdd a + g 1, 1) : A × Q) = (Multiplicative.toAdd a, 1)
    simp [hg1]
  · ext x
    show (ofNormalized_twistMulEquiv Q A c c' g hg x).2 = x.2
    rfl

/-! ## The class of a cocycle determines the extension -/

/-- If `f` is a `1`-cochain with `d¹ f = c - c'`, then the normalizations of `c` and `c'` differ
by the coboundary of `fun q ↦ f q - f 1`, a cochain vanishing at `1`. -/
theorem normCocycle_sub_normCocycle (c c' : Q × Q → A) (f : Q → A)
    (hf : ∀ q r : Q, d1 Q A f (q, r) = c (q, r) - c' (q, r)) :
    ∀ q r : Q, d1 Q A (fun q => f q - f 1) (q, r)
      = normCocycle Q A c (q, r) - normCocycle Q A c' (q, r) := by
  intro q r
  have h1 : d1 Q A (fun q => f q - f 1) (q, r) = d1 Q A f (q, r) - q • f 1 := by
    simp only [d1_apply, smul_sub]
    abel
  have h2 : c (q, 1) - c' (q, 1) = q • f 1 := by
    have hh := hf q 1
    simp only [d1_apply, mul_one] at hh
    rw [← hh]; abel
  rw [h1, ← h2, hf q r]
  simp only [normCocycle_apply]
  abel

/-- **Cohomologous `2`-cocycles define equivalent extensions.**  If `c` and `c'` have the same
class in `H²(Q, A)`, then the extensions `Extension.ofCocycle Q A c` and
`Extension.ofCocycle Q A c'` are equivalent as extensions of `Q` by `A`. -/
theorem ofCocycle_equiv_of_eq_class {Q : Type*} {A : Type*} [Group Q] [AddCommGroup A]
    [DistribMulAction Q A] (c c' : Work.GroupCohomology.Z2 Q A)
    (h : Work.GroupCohomology.H2π Q A c = Work.GroupCohomology.H2π Q A c') :
    Nonempty (Work.GroupCohomology.Extension.Equiv
      (Work.GroupCohomology.Extension.ofCocycle Q A c)
      (Work.GroupCohomology.Extension.ofCocycle Q A c')) := by
  -- the difference `c - c'` is a coboundary
  have hmem : ((c - c' : Z2 Q A) : Q × Q → A) ∈ B2 Q A := by
    have h0 : H2π Q A (c - c') = 0 := by rw [map_sub, h, sub_self]
    rw [← AddMonoidHom.mem_ker, H2π, QuotientAddGroup.ker_mk'] at h0
    exact h0
  obtain ⟨f, hf⟩ := (mem_B2_iff Q A ((c - c' : Z2 Q A) : Q × Q → A)).mp hmem
  have hf' : ∀ q r : Q, d1 Q A f (q, r) = (c : Q × Q → A) (q, r) - (c' : Q × Q → A) (q, r) := by
    intro q r
    have := congrFun hf (q, r)
    simpa using this
  -- normalizing turns the coboundary into the coboundary of `fun q ↦ f q - f 1`
  have key := normCocycle_sub_normCocycle Q A (c : Q × Q → A) (c' : Q × Q → A) f hf'
  exact ofNormalized_equiv_of_d1 Q A (normCocycle Q A (c : Q × Q → A))
    (normCocycle Q A (c' : Q × Q → A))
    (normCocycle_mem Q A (c : Q × Q → A) c.2) (normCocycle_one Q A (c : Q × Q → A))
    (normCocycle_mem Q A (c' : Q × Q → A) c'.2) (normCocycle_one Q A (c' : Q × Q → A))
    (fun q => f q - f 1) (by simp) key

end Work.GroupCohomology
