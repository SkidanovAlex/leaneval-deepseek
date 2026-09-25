import Mathlib
import Submission.Work.HopfGaschutz.Setup
import Submission.Work.RelatorRank.CohomologyH2
import Submission.Work.ConCohomology.All
import Submission.Work.ShafarevichKoch.freeGroup_twoCocycle_is_coboundary

/-!
# `H²(FreeGroup α, 𝔽₂) = 0`

**Namespace** `Work.HopfGaschutz`; module `Submission.Work.HopfGaschutz.h2_freeGroup_subsingleton`.

This module proves `Work.HopfGaschutz.h2_freeGroup_subsingleton`: the second cohomology of a *free*
group, with trivial `𝔽₂` coefficients, vanishes.  This is the classical statement `cd(F) = 1` for a
free group, in the workspace's own continuous-cohomology language
`Work.RelatorRank.contH2 Γ = H²_cont(Γ, 𝔽₂)` of `Work.ConCohomology`: the free group carries the
*discrete* topology, so all cochains are locally constant and the continuous cohomology is the
ordinary abstract cohomology.

Mathematically, `H²(F, M) = 0` for a free group `F` and *any* coefficient module `M`, which is
proved in `Submission.Work.ShafarevichKoch.freeGroup_twoCocycle_is_coboundary`: every `2`-cocycle of
a free group is a coboundary (the extension `M ⋊ F` defined by the cocycle is split, because `F` is
free).  That file, however, states the result only at universe `0` (`{α : Type}`), whereas the
statement at issue quantifies over `α : Type*`; the free group on a large type is not equivalent to
one on a small type in general, so the lemma is *reproved* here with the universe generalised, in the
special case of the trivial `𝔽₂` coefficients which is all that is needed.

## Contents

* `ZModTwoTwist` -- the set `𝔽₂ × FreeGroup α` with the twisted multiplication
  `(a, g) * (b, h) = (a + b + c (g, h), g * h)` determined by the cocycle `c` (it is a group exactly
  because `c` is a `2`-cocycle);
* `freeGroup_zmodTwo_twoCocycle_is_coboundary` -- every `2`-cocycle on `FreeGroup α` with values in
  `𝔽₂` (trivial action, written inhomogeneously) is the coboundary of an explicit `1`-cochain;
* `h2_freeGroup_subsingleton` -- hence `H²_cont(FreeGroup α, 𝔽₂) = 0`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.HopfGaschutz

universe u

/-- The carrier of the twisted product defined by a `2`-cocycle `c` with values in `𝔽₂`: the product
type `𝔽₂ × FreeGroup α`, given a *new* name so that no other (product) group structure can be picked
up by type class search when the twisted structure is installed locally. -/
structure ZModTwoTwist (α : Type u) where
  fst : ZMod 2
  snd : FreeGroup α

/-- Two elements of `ZModTwoTwist α` are equal as soon as both coordinates are. -/
theorem zModTwoTwist_ext {α : Type u} (a b : ZModTwoTwist α) (h1 : a.fst = b.fst)
    (h2 : a.snd = b.snd) : a = b := by
  cases a with
  | mk a1 a2 =>
  cases b with
  | mk b1 b2 =>
  simp only [ZModTwoTwist.mk.injEq] at h1 h2 ⊢
  exact ⟨h1, h2⟩

/-- **Every normalised `2`-cocycle of a free group with coefficients in `𝔽₂` is a coboundary.**

Here `c : FreeGroup α × FreeGroup α → ZMod 2` satisfies the inhomogeneous cocycle identity with
*trivial* action, `c (g * h, j) + c (g, h) = c (h, j) + c (g, h * j)`, and is normalised,
`c (1, h) = 0`.

The proof exhibits the `1`-cochain: the twisted product `(a, g) * (b, h) = (a + b + c (g, h), g * h)`
on `𝔽₂ × FreeGroup α` is associative precisely because of the cocycle identity, and normalisation
makes `(0, 1)` a two-sided identity, so that it is a group `T`; the projection `T → FreeGroup α` is
split because `FreeGroup α` is free, and the first coordinate of the splitting homomorphism is the
required `1`-cochain. -/
theorem freeGroup_zmodTwo_twoCocycle_is_coboundary_aux {α : Type u}
    (c : FreeGroup α × FreeGroup α → ZMod 2)
    (hc : ∀ g h j : FreeGroup α, c (g * h, j) + c (g, h) = c (h, j) + c (g, h * j))
    (h1 : ∀ h : FreeGroup α, c (1, h) = 0) :
    ∃ x : FreeGroup α → ZMod 2, ∀ g h : FreeGroup α, x h - x (g * h) + x g = c (g, h) := by
  have hg1 : ∀ g : FreeGroup α, c (g, 1) = 0 := by
    intro g
    have h := hc g 1 1
    rw [mul_one, mul_one, h1 1, zero_add] at h
    have h' : c (g, 1) + c (g, 1) = c (g, 1) + 0 := by simpa using h
    exact add_left_cancel h'
  have hkey : ∀ g : FreeGroup α, c (g, g⁻¹) = c (g⁻¹, g) := by
    intro g
    have h := hc g g⁻¹ g
    simpa only [mul_inv_cancel, inv_mul_cancel, h1, hg1, zero_add, add_zero] using h
  let mul : ZModTwoTwist α → ZModTwoTwist α → ZModTwoTwist α :=
    fun p q => ⟨p.fst + q.fst + c (p.snd, q.snd), p.snd * q.snd⟩
  let one : ZModTwoTwist α := ⟨0, 1⟩
  let inv : ZModTwoTwist α → ZModTwoTwist α :=
    fun p => ⟨-(p.fst + c (p.snd, p.snd⁻¹)), p.snd⁻¹⟩
  letI : Mul (ZModTwoTwist α) := ⟨mul⟩
  letI : One (ZModTwoTwist α) := ⟨one⟩
  letI : Inv (ZModTwoTwist α) := ⟨inv⟩
  have hmul_fst : ∀ p q : ZModTwoTwist α,
      (p * q).fst = p.fst + q.fst + c (p.snd, q.snd) := fun p q => rfl
  have hmul_snd : ∀ p q : ZModTwoTwist α, (p * q).snd = p.snd * q.snd := fun p q => rfl
  have hone_fst : (1 : ZModTwoTwist α).fst = 0 := rfl
  have hone_snd : (1 : ZModTwoTwist α).snd = 1 := rfl
  have hinv_fst : ∀ p : ZModTwoTwist α,
      (p⁻¹).fst = -(p.fst + c (p.snd, p.snd⁻¹)) := fun p => rfl
  have hinv_snd : ∀ p : ZModTwoTwist α, (p⁻¹).snd = p.snd⁻¹ := fun p => rfl
  -- associativity is exactly the cocycle identity
  have hmul_assoc : ∀ p q r : ZModTwoTwist α, (p * q) * r = p * (q * r) := by
    rintro ⟨a, g⟩ ⟨b, h⟩ ⟨d, j⟩
    refine zModTwoTwist_ext _ _ ?_ ?_
    · simp only [hmul_fst, hmul_snd]
      have key : c (g, h) + c (g * h, j) = c (h, j) + c (g, h * j) := by
        rw [add_comm (c (g, h)) (c (g * h, j))]
        exact hc g h j
      calc a + b + c (g, h) + d + c (g * h, j)
          = (a + b + d) + (c (g, h) + c (g * h, j)) := by abel
        _ = (a + b + d) + (c (h, j) + c (g, h * j)) := by rw [key]
        _ = a + (b + d + c (h, j)) + c (g, h * j) := by abel
    · simp only [hmul_snd]
      exact mul_assoc g h j
  have hone_mul : ∀ p : ZModTwoTwist α, 1 * p = p := by
    rintro ⟨a, g⟩
    refine zModTwoTwist_ext _ _ ?_ ?_
    · simp only [hmul_fst, hone_fst, hone_snd, h1, zero_add, add_zero]
    · simp only [hmul_snd, hone_snd]
      exact one_mul g
  have hinv_mul : ∀ p : ZModTwoTwist α, p⁻¹ * p = 1 := by
    rintro ⟨a, g⟩
    refine zModTwoTwist_ext _ _ ?_ ?_
    · simp only [hmul_fst, hinv_fst, hinv_snd, hone_fst]
      rw [hkey g]
      abel
    · simp only [hmul_snd, hinv_snd, hone_snd]
      exact inv_mul_cancel g
  -- the twisted product is a group
  letI : Group (ZModTwoTwist α) := Group.ofLeftAxioms hmul_assoc hone_mul hinv_mul
  -- the projection onto the second coordinate
  let π : ZModTwoTwist α →* FreeGroup α :=
    { toFun := ZModTwoTwist.snd
      map_one' := by simp only [hone_snd]
      map_mul' := by intro p q; simp only [hmul_snd] }
  -- the splitting supplied by freeness of `FreeGroup α`
  let φ : α → ZModTwoTwist α := fun i => ⟨0, FreeGroup.of i⟩
  let s : FreeGroup α →* ZModTwoTwist α := FreeGroup.lift φ
  have hs : ∀ g : FreeGroup α, (s g).snd = g := by
    intro g
    have h := FreeGroup.lift_unique (f := FreeGroup.of) (π.comp s) (fun i => rfl) (x := g)
    simpa [π, MonoidHom.comp_apply, FreeGroup.lift_of_apply] using h
  refine ⟨fun g => -(s g).fst, fun g h => ?_⟩
  have hm : (s (g * h)).fst = (s g).fst + (s h).fst + c (g, h) := by
    have hh := congrArg ZModTwoTwist.fst (map_mul s g h)
    rw [hmul_fst, hs g, hs h] at hh
    exact hh
  change -(s h).fst - -(s (g * h)).fst + -(s g).fst = c (g, h)
  rw [hm]
  abel

/-- **Every `2`-cocycle of a free group with coefficients in `𝔽₂` is a coboundary.**

`c : FreeGroup α × FreeGroup α → ZMod 2` satisfies the inhomogeneous cocycle identity with trivial
action, `c (g * h, j) + c (g, h) = c (h, j) + c (g, h * j)`; then there is a `1`-cochain `x` with
`d¹x (g, h) = x h - x (g * h) + x g = c (g, h)`.

This is `H²(FreeGroup α, 𝔽₂) = 0` at the level of cochains, with the universe generalised (the
normalisation `c ↦ c - c (1,1)` reduces to
`freeGroup_zmodTwo_twoCocycle_is_coboundary_aux`). -/
theorem freeGroup_zmodTwo_twoCocycle_is_coboundary {α : Type u}
    (c : FreeGroup α × FreeGroup α → ZMod 2)
    (hc : ∀ g h j : FreeGroup α, c (g * h, j) + c (g, h) = c (h, j) + c (g, h * j)) :
    ∃ x : FreeGroup α → ZMod 2, ∀ g h : FreeGroup α, x h - x (g * h) + x g = c (g, h) := by
  -- `c` is constant on the first coordinate at `g = 1`
  have h1 : ∀ h : FreeGroup α, c (1, h) = c (1, 1) := by
    intro h
    have h' := hc 1 1 h
    rw [one_mul, one_mul] at h'
    exact (add_left_cancel h').symm
  let k : ZMod 2 := c (1, 1)
  let c' : FreeGroup α × FreeGroup α → ZMod 2 := fun p => c p - k
  have hc' : ∀ g h j : FreeGroup α, c' (g * h, j) + c' (g, h) = c' (h, j) + c' (g, h * j) := by
    intro g a b
    have hh := hc g a b
    have key : c' (g * a, b) + c' (g, a) - (c' (a, b) + c' (g, a * b))
        = (c (g * a, b) + c (g, a)) - (c (a, b) + c (g, a * b)) := by
      show (c (g * a, b) - k) + (c (g, a) - k) - ((c (a, b) - k) + (c (g, a * b) - k))
        = (c (g * a, b) + c (g, a)) - (c (a, b) + c (g, a * b))
      abel
    rw [← sub_eq_zero, key, hh, sub_self]
  have h1' : ∀ h : FreeGroup α, c' (1, h) = 0 := by
    intro b
    have hk : c (1, b) = k := h1 b
    show c (1, b) - k = 0
    rw [hk, sub_self]
  obtain ⟨x, hx⟩ := freeGroup_zmodTwo_twoCocycle_is_coboundary_aux c' hc' h1'
  refine ⟨fun g => x g + k, fun g h => ?_⟩
  have key : x h + k - (x (g * h) + k) + (x g + k) = (x h - x (g * h) + x g) + k := by abel
  rw [key, hx g h]
  show (c (g, h) - k) + k = c (g, h)
  abel

/-- **`H²` of a free group with coefficients in `𝔽₂` vanishes**: with the discrete topology on
`FreeGroup α`, the continuous cohomology group `H²_cont(FreeGroup α, 𝔽₂)`
(`Work.RelatorRank.contH2`, trivial action) is a subsingleton, i.e. `cd(FreeGroup α) ≤ 1`.

Every locally constant `2`-cocycle is a `2`-cocycle in the sense of
`freeGroup_zmodTwo_twoCocycle_is_coboundary` (the group is discrete, so every cochain is locally
constant), hence a coboundary, so `H²` is the quotient by all of `Z²`. -/
theorem h2_freeGroup_subsingleton (α : Type*) [TopologicalSpace (FreeGroup α)]
    [DiscreteTopology (FreeGroup α)] :
    Subsingleton (Work.RelatorRank.contH2 (FreeGroup α)) := by
  show Subsingleton (Work.ConCohomology.H2 (FreeGroup α) (ZMod 2))
  rw [QuotientAddGroup.subsingleton_iff]
  apply le_antisymm le_top
  intro z _
  rw [Work.ConCohomology.mem_B2', Work.ConCohomology.mem_B2]
  -- the cocycle identity, in the form used by `freeGroup_zmodTwo_twoCocycle_is_coboundary`
  have hcz : ∀ σ τ ρ : FreeGroup α,
      (z : FreeGroup α × FreeGroup α → ZMod 2) (σ * τ, ρ)
        + (z : FreeGroup α × FreeGroup α → ZMod 2) (σ, τ)
      = (z : FreeGroup α × FreeGroup α → ZMod 2) (τ, ρ)
        + (z : FreeGroup α × FreeGroup α → ZMod 2) (σ, τ * ρ) := by
    intro σ τ ρ
    have h := Work.ConCohomology.mem_Z2.mp z.2 σ τ ρ
    rw [show σ • ((z : FreeGroup α × FreeGroup α → ZMod 2) (τ, ρ))
          = (z : FreeGroup α × FreeGroup α → ZMod 2) (τ, ρ) from rfl] at h
    rw [← sub_eq_zero]
    have key : (z : FreeGroup α × FreeGroup α → ZMod 2) (σ * τ, ρ)
          + (z : FreeGroup α × FreeGroup α → ZMod 2) (σ, τ)
          - ((z : FreeGroup α × FreeGroup α → ZMod 2) (τ, ρ)
            + (z : FreeGroup α × FreeGroup α → ZMod 2) (σ, τ * ρ))
        = -((z : FreeGroup α × FreeGroup α → ZMod 2) (τ, ρ)
            - (z : FreeGroup α × FreeGroup α → ZMod 2) (σ * τ, ρ)
            + (z : FreeGroup α × FreeGroup α → ZMod 2) (σ, τ * ρ)
            - (z : FreeGroup α × FreeGroup α → ZMod 2) (σ, τ)) := by abel
    rw [key, h, neg_zero]
  obtain ⟨x, hx⟩ := freeGroup_zmodTwo_twoCocycle_is_coboundary
    (fun p => (z : FreeGroup α × FreeGroup α → ZMod 2) p) hcz
  refine ⟨⟨x, IsLocallyConstant.of_discrete x⟩, ?_⟩
  ext p
  obtain ⟨σ, τ⟩ := p
  rw [Work.ConCohomology.d1Hom_apply]
  show x τ - x (σ * τ) + x σ = (z : FreeGroup α × FreeGroup α → ZMod 2) (σ, τ)
  exact hx σ τ

end Work.HopfGaschutz
