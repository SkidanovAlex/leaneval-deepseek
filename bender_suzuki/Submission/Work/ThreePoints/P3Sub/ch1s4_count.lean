import Mathlib
import Submission.Work.ThreePoints.Omega

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Counting the fixed points of `P` on `Ω_X` inside `N`

Let `H` be a subgroup of a finite group `G`, `X ≤ H`, `N ≤ N_G(X)`, and `P ≤ N`.  Assume that
`Ω_X = fixedPts H X` is exactly the `N`-orbit of the coset of `1` (the conclusion of
`Work.ThreePoints.P3Sub.ch1s4_orbit`).  Then the `N`-equivariant bijection
`↥N ⧸ (N ⊓ H) → Ω_X`, `n(N ⊓ H) ↦ n • (1 : G ⧸ H)`, identifies the fixed points of
`P.subgroupOf N` on the left with the fixed points of `P` on `Ω_X`:

`|fixedPts ((N ⊓ H).subgroupOf N) (P.subgroupOf N)| = |fixedPts H P ∩ fixedPts H X|`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints.P3Sub

open Submission.Blueprint

/-- `N_G(X)` preserves the fixed-point set `Ω_X = fixedPts H X`. -/
theorem ch1s4_count_aux {G : Type} [Group G] {H X : Subgroup G} {h : G}
    (hh : h ∈ Subgroup.normalizer (X : Set G)) {ω : G ⧸ H}
    (hω : ω ∈ Submission.Blueprint.fixedPts H X) :
    h • ω ∈ Submission.Blueprint.fixedPts H X := by
  rw [Work.ThreePoints.mem_fixedPts] at hω ⊢
  intro x hx
  have hxh : h⁻¹ * x * h ∈ X := by
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hh) x).mp hx
  calc x • (h • ω) = (x * h) • ω := by rw [mul_smul]
    _ = (h * (h⁻¹ * x * h)) • ω := by rw [show x * h = h * (h⁻¹ * x * h) from by group]
    _ = h • ((h⁻¹ * x * h) • ω) := by rw [mul_smul]
    _ = h • ω := by rw [hω _ hxh]

theorem ch1s4_count {G : Type} [Group G] [Finite G] {H X N P : Subgroup G}
    (hXH : X ≤ H)
    (hNN : N ≤ Subgroup.normalizer (X : Set G))
    (hPN : P ≤ N)
    (htrans : ∀ ω ∈ Submission.Blueprint.fixedPts H X,
      ∃ n : N, (n : G) • (QuotientGroup.mk (1 : G) : G ⧸ H) = ω) :
    (Submission.Blueprint.fixedPts ((N ⊓ H).subgroupOf N) (P.subgroupOf N)).ncard =
      ((Submission.Blueprint.fixedPts H P) ∩ (Submission.Blueprint.fixedPts H X)).ncard := by
  classical
  set B : Subgroup ↥N := (N ⊓ H).subgroupOf N with hB
  set T : Subgroup ↥N := P.subgroupOf N with hT
  have hwell : ∀ x y : ↥N, QuotientGroup.leftRel B x y →
      QuotientGroup.leftRel H (x : G) (y : G) := by
    intro x y hxy
    rw [QuotientGroup.leftRel_apply] at hxy ⊢
    rw [Subgroup.mem_subgroupOf] at hxy
    exact hxy.2
  let φ : ↥N ⧸ B → G ⧸ H := Quotient.map' (Subtype.val : ↥N → G) hwell
  have hφ : ∀ x : ↥N, φ (QuotientGroup.mk x) = QuotientGroup.mk (x : G) :=
    fun x => Quotient.map'_mk'' _ hwell x
  have hinj : Function.Injective φ := by
    intro p q hpq
    revert hpq
    refine Quotient.inductionOn' p (fun x => ?_)
    refine Quotient.inductionOn' q (fun y => ?_)
    intro hpq
    simp only [hφ] at hpq
    rw [QuotientGroup.eq] at hpq
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact ⟨(x⁻¹ * y).2, by simpa using hpq⟩
  have hsmul_base : ∀ x : ↥N,
      (x : G) • (QuotientGroup.mk (1 : G) : G ⧸ H) = QuotientGroup.mk (x : G) := by
    intro x
    rw [Work.DoubleTransitivity.smul_mk, mul_one]
  have himage : ∀ p : ↥N ⧸ B, φ p ∈ Submission.Blueprint.fixedPts H X := by
    intro p
    refine Quotient.inductionOn' p (fun x => ?_)
    rw [hφ x, ← hsmul_base x]
    exact ch1s4_count_aux (hNN x.2)
      ((Work.DoubleTransitivity.pt_mem_fixedPts_iff X H).mpr hXH)
  have hequiv : ∀ (t : ↥N) (p : ↥N ⧸ B), φ (t • p) = (t : G) • φ p := by
    intro t p
    refine Quotient.inductionOn' p (fun y => ?_)
    have h1 : t • (QuotientGroup.mk y : ↥N ⧸ B) = QuotientGroup.mk (t * y) :=
      MulAction.Quotient.smul_mk B t y
    rw [h1, hφ (t * y), hφ y, Work.DoubleTransitivity.smul_mk]
    simp only [Subgroup.coe_mul]
  have hkey : ∀ p : ↥N ⧸ B, p ∈ Submission.Blueprint.fixedPts B T ↔
      φ p ∈ Submission.Blueprint.fixedPts H P := by
    intro p
    refine Quotient.inductionOn' p (fun x => ?_)
    rw [hφ x, Work.ThreePoints.mem_fixedPts, Work.ThreePoints.mem_fixedPts]
    constructor
    · intro h q hq
      have ht : (⟨q, hPN hq⟩ : ↥N) ∈ T := by
        rw [hT]; exact Subgroup.mem_subgroupOf.mpr hq
      have hstep : ((⟨q, hPN hq⟩ : ↥N) : G) • φ (QuotientGroup.mk x) =
          φ (QuotientGroup.mk x) :=
        (hequiv (⟨q, hPN hq⟩ : ↥N) (QuotientGroup.mk x)).symm.trans
          (congrArg φ (h _ ht))
      rw [hφ x] at hstep
      simpa using hstep
    · intro h t ht
      have hq : (t : G) ∈ P := Subgroup.mem_subgroupOf.mp (hT ▸ ht)
      refine hinj ?_
      rw [hequiv t (QuotientGroup.mk x), hφ x]
      exact h (t : G) hq
  have hsurj : ∀ ω ∈ Submission.Blueprint.fixedPts H X, ∃ p : ↥N ⧸ B, φ p = ω := by
    intro ω hω
    obtain ⟨n, hn⟩ := htrans ω hω
    exact ⟨QuotientGroup.mk n, by rw [hφ n, ← hsmul_base n, hn]⟩
  refine Set.ncard_congr (s := Submission.Blueprint.fixedPts B T)
    (t := Submission.Blueprint.fixedPts H P ∩ Submission.Blueprint.fixedPts H X)
    (fun a _ => φ a) ?_ ?_ ?_
  · intro a ha
    exact ⟨(hkey a).mp ha, himage a⟩
  · intro a b ha hb hab
    exact hinj hab
  · intro b hb
    obtain ⟨p, hp⟩ := hsurj b hb.2
    exact ⟨p, (hkey p).mpr (hp ▸ hb.1), hp⟩

end Work.ThreePoints.P3Sub
