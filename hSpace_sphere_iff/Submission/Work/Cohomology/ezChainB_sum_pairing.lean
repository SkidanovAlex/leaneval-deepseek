
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# Pairing the cup product of pulled-back cocycles with the Eilenberg-Zilber chain

Let `X`, `Y` be simplicial sets, `u : C^p(X;Q)` and `v : C^q(Y;Q)` *normalized* cochains
(i.e. cochains vanishing on degenerate simplices) and `c`, `d` finitely supported chains on
`X` and `Y`.  This file proves the chain-level form of the Eilenberg-Zilber / Kunneth
computation

`<pr1*u cup pr2*v, sum_{a in c} sum_{b in d} (c a * d b) * EZ(a (x) b)> = <u,c> * <v,d>`,

where `EZ(a (x) b)` is the Eilenberg-Zilber shuffle chain `Work.Cohomology.ezChainB` and the
pairing `<-, ->` is `Submission.Cohomology.seval`.

The proof is a sum over the `(p,q)`-shuffles `A` of `{0,...,p+q-1} with p elements`:

* for `A = shuffleId p q` (all `a`-steps first) the front `p`-face of the `a`-part and the
  back `q`-face of the `b`-part are `a` and `b` themselves, and the shuffle sign is `1`, so the
  term contributes `u a * v b`;
* for every other shuffle the composite `subinterval 0 p >> shuffleMapA A hA` is not injective,
  so `X.map (shuffleMapA A hA).op a` has a degenerate front face, on which the normalized
  cochain `u` vanishes; the corresponding term of the cup product is therefore `0`.

The target theorem is `Work.Cohomology.ezChainB_sum_pairing`.
-/
import Mathlib
import Submission.Work.Cohomology.EZShuffle
import Submission.Work.Cohomology.Chains
import Submission.Work.Cohomology.Cohomology
import Submission.Work.Cohomology.Cup
import Submission.Work.Cohomology.shuffleId_card
import Submission.Work.Cohomology.shuffleSign_shuffleId
import Submission.Work.Cohomology.frontProjA_shuffleId
import Submission.Work.Cohomology.backProjB_shuffleId
import Submission.Work.Cohomology.normalized_frontProjA_eq_zero

open CategoryTheory Simplicial Opposite
open scoped MonoidalCategory

namespace Work.Cohomology

noncomputable section

open Submission.Cohomology

namespace ezB

variable {X Y : SSet.{0}}

/-- The cup product on `X (x) Y` of the pullbacks of `u` and `v` along the two projections. -/
abbrev cupPullback {p q : ℕ} (u : Cochain X ℚ p) (v : Cochain Y ℚ q) :
    Cochain (X ⊗ Y) ℚ (p + q) :=
  cupOf (X ⊗ Y) ℚ rfl (pullbackCo ℚ (SemiCartesianMonoidalCategory.fst X Y) u)
    (pullbackCo ℚ (SemiCartesianMonoidalCategory.snd X Y) v)

lemma fst_apply_tensor {n : ℕ} (x : (X ⊗ Y).obj (op ⦋n⦌)) :
    (SemiCartesianMonoidalCategory.fst X Y).app (op ⦋n⦌) x = x.1 := by
  rw [CategoryTheory.Functor.Monoidal.fst_app, SemiCartesianMonoidalCategory.fst_def]
  rfl

lemma snd_apply_tensor {n : ℕ} (x : (X ⊗ Y).obj (op ⦋n⦌)) :
    (SemiCartesianMonoidalCategory.snd X Y).app (op ⦋n⦌) x = x.2 := by
  rw [CategoryTheory.Functor.Monoidal.snd_app, SemiCartesianMonoidalCategory.snd_def]
  rfl

lemma map_map {m n k : ℕ} (f : ⦋n⦌ ⟶ ⦋m⦌) (g : ⦋m⦌ ⟶ ⦋k⦌)
    (x : X.obj (op ⦋k⦌)) :
    X.map f.op (X.map g.op x) = X.map (f ≫ g).op x := by
  rw [op_comp, Functor.map_comp]
  rfl

lemma map_id_apply {n : ℕ} (x : X.obj (op ⦋n⦌)) : X.map (𝟙 ⦋n⦌).op x = x := by simp

lemma frontOf_tensor {p q n : ℕ} (h : p + q = n) (x : (X ⊗ Y).obj (op ⦋n⦌)) :
    frontOf (X ⊗ Y) h x = (frontOf X h x.1, frontOf Y h x.2) := by
  dsimp only [frontOf]
  rw [Monoidal.tensorObj_map]
  exact CategoryTheory.tensor_apply _ _ x

lemma backOf_tensor {p q n : ℕ} (h : p + q = n) (x : (X ⊗ Y).obj (op ⦋n⦌)) :
    backOf (X ⊗ Y) h x = (backOf X h x.1, backOf Y h x.2) := by
  dsimp only [backOf]
  rw [Monoidal.tensorObj_map]
  exact CategoryTheory.tensor_apply _ _ x

lemma frontOf_staircase_fst {p q : ℕ} (A : Finset (Fin (p + q))) (hA : A.card = p)
    (a : X.obj (op ⦋p⦌)) (b : Y.obj (op ⦋q⦌)) :
    (frontOf (X ⊗ Y) (rfl : p + q = p + q) (staircase A hA a b)).1
      = frontOf X (rfl : p + q = p + q) (X.map (shuffleMapA A hA).op a) := by
  rw [frontOf_tensor]
  rfl

lemma backOf_staircase_snd {p q : ℕ} (A : Finset (Fin (p + q))) (hA : A.card = p)
    (a : X.obj (op ⦋p⦌)) (b : Y.obj (op ⦋q⦌)) :
    (backOf (X ⊗ Y) (rfl : p + q = p + q) (staircase A hA a b)).2
      = backOf Y (rfl : p + q = p + q) (Y.map (shuffleMapB A hA).op b) := by
  rw [backOf_tensor]
  rfl

lemma frontOf_map {p q : ℕ} (φ : ⦋p + q⦌ ⟶ ⦋p⦌) (a : X.obj (op ⦋p⦌)) :
    frontOf X (rfl : p + q = p + q) (X.map φ.op a)
      = X.map (SimplexCategory.subinterval 0 p (by omega) ≫ φ).op a := by
  dsimp only [frontOf]
  rw [map_map]

lemma frontOf_shuffleId {p q : ℕ} (hA : (shuffleId p q).card = p) (a : X.obj (op ⦋p⦌)) :
    frontOf X (rfl : p + q = p + q) (X.map (shuffleMapA (shuffleId p q) hA).op a) = a := by
  rw [frontOf_map, frontProjA_shuffleId hA, map_id_apply]

lemma backOf_shuffleId {p q : ℕ} (hA : (shuffleId p q).card = p) (b : Y.obj (op ⦋q⦌)) :
    backOf Y (rfl : p + q = p + q) (Y.map (shuffleMapB (shuffleId p q) hA).op b) = b := by
  dsimp only [backOf]
  rw [map_map, backProjB_shuffleId hA, map_id_apply]

/-- The cup product of the two pulled-back cochains, evaluated at the staircase simplex
`staircase A hA a b`, is the product of the evaluations of `u` and `v` at the front and back
faces of the two components. -/
lemma eval_cup_staircase {p q : ℕ} (A : Finset (Fin (p + q))) (hA : A.card = p)
    (a : X.obj (op ⦋p⦌)) (b : Y.obj (op ⦋q⦌))
    (u : Cochain X ℚ p) (v : Cochain Y ℚ q) :
    cupPullback u v (staircase A hA a b)
      = u (frontOf X (rfl : p + q = p + q) (X.map (shuffleMapA A hA).op a))
        * v (backOf Y (rfl : p + q = p + q) (Y.map (shuffleMapB A hA).op b)) := by
  simp only [cupPullback, cupOf_apply, pullbackCo_apply, fst_apply_tensor, snd_apply_tensor,
    frontOf_staircase_fst A hA a b, backOf_staircase_snd A hA a b]

/-- **The Eilenberg-Zilber pairing of a single pair of simplices.**  The cup product of the
pullbacks of a normalized `p`-cochain `u` on `X` and a normalized `q`-cochain `v` on `Y`,
evaluated on the shuffle chain `EZ(a (x) b)`, is `u a * v b`.  All the shuffles other than
`shuffleId p q` contribute `0`, because their `a`-side front `p`-face is degenerate. -/
lemma seval_cup_ezChainB {p q : ℕ} (a : X.obj (op ⦋p⦌)) (b : Y.obj (op ⦋q⦌))
    (u : Cochain X ℚ p) (v : Cochain Y ℚ q) (hnu : IsNormalized u) :
    seval (X ⊗ Y) ℚ (p + q) (cupPullback u v) (ezChainB a b) = u a * v b := by
  classical
  have hshuf : (shuffleId p q).card = p := shuffleId_card p q
  have hkey : ∀ A : {A : Finset (Fin (p + q)) // A.card = p},
      seval (X ⊗ Y) ℚ (p + q) (cupPullback u v)
        ((shuffleSign A.1 : ℚ) • Finsupp.single (staircase A.1 A.2 a b) 1)
      = if A = ⟨shuffleId p q, hshuf⟩ then u a * v b else 0 := by
    rintro ⟨A, hA⟩
    rw [LinearMap.map_smul, seval_single, one_mul, smul_eq_mul,
      eval_cup_staircase A hA a b u v]
    by_cases hne : A = shuffleId p q
    · subst hne
      rw [if_pos (Subtype.ext rfl), frontOf_shuffleId hA, backOf_shuffleId hA,
        shuffleSign_shuffleId]
      norm_num
    · rw [if_neg (fun h => hne (Subtype.ext_iff.mp h))]
      rw [frontOf_map, normalized_frontProjA_eq_zero u hnu A hA hne a]
      simp
  rw [ezChainB, map_sum]
  trans ∑ A : {A : Finset (Fin (p + q)) // A.card = p},
      if A = ⟨shuffleId p q, hshuf⟩ then u a * v b else 0
  · exact Finset.sum_congr rfl fun A _ => hkey A
  · rw [Finset.sum_ite_eq']
    simp

/-- The double sum `sum_a sum_b (f a * g b) * (u a * v b)` factors as the product of the two
pairings. -/
lemma sum_mul_sum_factor {α β : Type*} (s : Finset α) (t : Finset β)
    (f u : α → ℚ) (g v : β → ℚ) :
    ∑ a ∈ s, ∑ b ∈ t, (f a * g b) * (u a * v b)
      = (∑ a ∈ s, f a * u a) * (∑ b ∈ t, g b * v b) := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

end ezB

/-- **The Eilenberg-Zilber pairing of the tensor product of two chains.** -/
theorem ezChainB_sum_pairing {X Y : SSet.{0}} {p q : ℕ} (c : Submission.Cohomology.SChain X ℚ p)
    (d : Submission.Cohomology.SChain Y ℚ q)
    (u : Submission.Cohomology.Cochain X ℚ p) (v : Submission.Cohomology.Cochain Y ℚ q)
    (hu : u ∈ Submission.Cohomology.cycles X ℚ p)
    (hv : v ∈ Submission.Cohomology.cycles Y ℚ q)
    (hnu : Work.Cohomology.IsNormalized u) (hnv : Work.Cohomology.IsNormalized v) :
    Submission.Cohomology.seval (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ (p + q)
        (Submission.Cohomology.cupOf (CategoryTheory.MonoidalCategoryStruct.tensorObj X Y) ℚ rfl
          (Submission.Cohomology.pullbackCo ℚ
            (CategoryTheory.SemiCartesianMonoidalCategory.fst X Y) u)
          (Submission.Cohomology.pullbackCo ℚ
            (CategoryTheory.SemiCartesianMonoidalCategory.snd X Y) v))
        (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • Work.Cohomology.ezChainB a b)
      = Submission.Cohomology.seval X ℚ p u c * Submission.Cohomology.seval Y ℚ q v d := by
  show seval (X ⊗ Y) ℚ (p + q) (ezB.cupPullback u v)
      (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB a b)
    = seval X ℚ p u c * seval Y ℚ q v d
  have hL : seval (X ⊗ Y) ℚ (p + q) (ezB.cupPullback u v)
      (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezChainB a b)
      = ∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) * (u a * v b) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [LinearMap.map_smul, smul_eq_mul, ezB.seval_cup_ezChainB a b u v hnu]
  have hc : seval X ℚ p u c = ∑ a ∈ c.support, c a * u a := seval_apply X ℚ p u c
  have hd : seval Y ℚ q v d = ∑ b ∈ d.support, d b * v b := seval_apply Y ℚ q v d
  rw [hL, hc, hd]
  exact ezB.sum_mul_sum_factor c.support d.support (fun a => c a) (fun a => u a)
    (fun b => d b) (fun b => v b)

end

end Work.Cohomology
