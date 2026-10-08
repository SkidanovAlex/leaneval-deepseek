/-
# Matching the squaring and polar forms determines the cocycle up to a coboundary

The classification of `Work.Higman.cocycle_normal_form` is stated on the *cocycle* `b`, but what
classifies the group `TwoStep V W b` is the pair

* the **squaring form**  `Q u = b u u`          (`TwoStep.sq_eq`), and
* the **polar form**     `B u v = b u v + b v u`

(the commutator map).  Two biadditive maps with the same `Q` and the same `B` differ by an
*alternating* form, and by `Work.Higman.exists_additive_coboundary` every alternating biadditive
form on a finite `𝔽₂`-vector space is a coboundary `c u + c v + c (u + v)`.

Consequently an additive isomorphism `φ : V ≃+ 𝔽 × 𝔽` together with `ψ : W ≃+ 𝔽` which carries `Q`
and `B` of `b` to those of a two-step model `bc` immediately produces the coboundary form of the
classification:

  `ψ (b u v) = bc (φ u) (φ v) + (c (φ u) + c (φ v) + c (φ u + φ v))`.

This file proves that reduction once and for all; both the `B`, `C` and `D` disjuncts of
`cocycle_normal_form` are instances of it (with `bc = bCocycle`, `cCocycle`, `dCocycle`).
-/

import Mathlib
import Submission.Work.Higman.Q3.Defs
import Submission.Work.Higman.cocycle_setup
import Submission.Work.Higman.Family
import Submission.Work.Higman.exists_additive_coboundary

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace Work.Higman

/-- In an additive group of exponent two, `(a + c) + a = c`. -/
lemma add_add_self_eq {Z : Type*} [AddCommGroup Z] [AddExpTwo Z] (a c : Z) : (a + c) + a = c := by
  rw [add_assoc, add_comm c a, ← add_assoc, AddExpTwo.add_self, zero_add]

/-- **The cocycle is determined by its squaring form alone, up to a coboundary** (Higman 1963,
§2: "the isomorphism class of `G` is determined by `G/Φ(G)`, `Φ(G)` and the squaring map").

If additive isomorphisms `φ : V ≃+ 𝔽 × 𝔽` and `ψ : W ≃+ 𝔽` carry the *diagonal* `u ↦ b u u` of `b`
to that of a biadditive `bc : (𝔽 × 𝔽) → (𝔽 × 𝔽) → 𝔽`, then `b` agrees with `bc` up to the
coboundary `c (φ u) + c (φ v) + c (φ u + φ v)`.  No hypothesis on the polar form is needed: two
biadditive maps with the same diagonal differ by a form which is alternating (`δ u u = 0`), and
every alternating biadditive form on a finite `𝔽₂`-vector space is a coboundary. -/
theorem coboundary_of_form_match
    {V W : Type} [AddCommGroup V] [AddExpTwo V] [AddCommGroup W] [AddExpTwo W]
    [Finite V]
    {b : V → V → W} [Biadd b]
    {n : ℕ} {bc : (GaloisField 2 n × GaloisField 2 n) →
      (GaloisField 2 n × GaloisField 2 n) → GaloisField 2 n} [Biadd bc]
    (φ : V ≃+ (GaloisField 2 n × GaloisField 2 n)) (ψ : W ≃+ GaloisField 2 n)
    (hQ : ∀ u : V, ψ (b u u) = bc (φ u) (φ u)) :
    ∃ c : (GaloisField 2 n × GaloisField 2 n) → GaloisField 2 n,
      ∀ u v : V, ψ (b u v) = bc (φ u) (φ v) +
        (c (φ u) + c (φ v) + c (φ u + φ v)) := by
  classical
  let F := GaloisField 2 n
  letI : Module (ZMod 2) (F × F) :=
    AddCommGroup.zmodModule fun z => by rw [two_nsmul]; exact AddExpTwo.add_self z
  let δ : (F × F) → (F × F) → F := fun x y => bc x y + ψ (b (φ.symm x) (φ.symm y))
  have hδ1 : ∀ x y z : F × F, δ (x + y) z = δ x z + δ y z := by
    intro x y z
    have hbc := Biadd.add_left (b := bc) x y z
    have hb := Biadd.add_left (b := b) (φ.symm x) (φ.symm y) (φ.symm z)
    have hsym : φ.symm (x + y) = φ.symm x + φ.symm y := map_add φ.symm x y
    simp only [δ, hsym, hbc, hb, map_add]
    abel
  have hδ2 : ∀ x y z : F × F, δ x (y + z) = δ x y + δ x z := by
    intro x y z
    have hbc := Biadd.add_right (b := bc) x y z
    have hb := Biadd.add_right (b := b) (φ.symm x) (φ.symm y) (φ.symm z)
    have hsym : φ.symm (y + z) = φ.symm y + φ.symm z := map_add φ.symm y z
    simp only [δ, hsym, hbc, hb, map_add]
    abel
  have hδdiag : ∀ x : F × F, δ x x = 0 := by
    intro x
    have hx : φ (φ.symm x) = x := φ.apply_symm_apply x
    have h := hQ (φ.symm x)
    rw [hx] at h
    show bc x x + ψ (b (φ.symm x) (φ.symm x)) = 0
    rw [h, AddExpTwo.add_self]
  obtain ⟨f, hf⟩ := exists_additive_coboundary δ hδ1 hδ2 hδdiag
  refine ⟨f, fun u v => ?_⟩
  have h' : f (φ u + φ v) + (f (φ u) + f (φ v)) = bc (φ u) (φ v) + ψ (b u v) := by
    have h := hf (φ u) (φ v)
    simpa only [δ, φ.symm_apply_apply] using h
  have h2 : ψ (b u v) = f (φ u + φ v) + (f (φ u) + f (φ v)) + bc (φ u) (φ v) := by
    rw [h']
    exact (add_add_self_eq (bc (φ u) (φ v)) (ψ (b u v))).symm
  rw [h2, ← map_add φ u v]
  abel

end Work.Higman
