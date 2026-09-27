/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The external product of finitely supported `ℚ`-valued functions

For `e : α →₀ ℚ` and `f : β →₀ ℚ` we define the *external product* `ezTens e f : α × β →₀ ℚ` by
`(ezTens e f) (x, y) = e x * f y`, written as a sum of single terms over the two supports.

The point of the file is `ezTens_mapDomain`: pushing an external product forward along a map which
is componentwise, `Prod.map φ ψ`, commutes with the external product,
`(ezTens e f).mapDomain (Prod.map φ ψ) = ezTens (e.mapDomain φ) (f.mapDomain ψ)`.

We also record the expansion `sbdry_eq_sum_mapDomain` of the chain boundary into a sum of
pushforwards along the face maps.
-/
import Mathlib
import Submission.Work.Cohomology.Chains

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

noncomputable section

variable {α β γ δ ι κ : Type*}

/-- The external product of two finitely supported `ℚ`-valued functions on `α` and `β`. -/
def ezTens (e : α →₀ ℚ) (f : β →₀ ℚ) : α × β →₀ ℚ :=
  e.sum fun x ex => ex • Finsupp.mapDomain (fun y => (x, y)) f

/-- Pushing a finitely supported function forward along a map is the sum of the single terms
over its support. -/
lemma mapDomain_eq_sum (F : α → γ) (e : α →₀ ℚ) :
    Finsupp.mapDomain F e = ∑ x ∈ e.support, e x • Finsupp.single (F x) 1 := by
  simp only [Finsupp.mapDomain, Finsupp.sum, Finsupp.smul_single, smul_eq_mul, mul_one]

lemma ezTens_double_sum (e : α →₀ ℚ) (f : β →₀ ℚ) :
    ezTens e f = ∑ x ∈ e.support, ∑ y ∈ f.support, (e x * f y) • Finsupp.single (x, y) 1 := by
  simp only [ezTens, Finsupp.sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mapDomain_eq_sum (F := fun y => (x, y))]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_smul]

@[simp] lemma ezTens_zero_left (f : β →₀ ℚ) : ezTens (0 : α →₀ ℚ) f = 0 := by
  rw [ezTens]
  exact Finsupp.sum_zero_index

@[simp] lemma ezTens_zero_right (e : α →₀ ℚ) : ezTens e (0 : β →₀ ℚ) = 0 := by
  simp only [ezTens, Finsupp.mapDomain_zero, smul_zero, Finsupp.sum]
  simp

lemma ezTens_single_left (x : α) (r : ℚ) (f : β →₀ ℚ) :
    ezTens (Finsupp.single x r) f = r • Finsupp.mapDomain (fun y => (x, y)) f := by
  rw [ezTens, Finsupp.sum_single_index (by simp)]

lemma ezTens_add_left (e₁ e₂ : α →₀ ℚ) (f : β →₀ ℚ) :
    ezTens (e₁ + e₂) f = ezTens e₁ f + ezTens e₂ f := by
  rw [ezTens, ezTens, ezTens,
    Finsupp.sum_add_index' (fun x => by simp) (fun x a b => by rw [add_smul])]

lemma ezTens_smul_left (r : ℚ) (e : α →₀ ℚ) (f : β →₀ ℚ) :
    ezTens (r • e) f = r • ezTens e f := by
  rw [ezTens, ezTens, Finsupp.sum_smul_index (fun x => by simp), Finsupp.smul_sum]
  refine Finsupp.sum_congr fun x hx => ?_
  simp only [smul_smul]

lemma ezTens_add_right (e : α →₀ ℚ) (f₁ f₂ : β →₀ ℚ) :
    ezTens e (f₁ + f₂) = ezTens e f₁ + ezTens e f₂ := by
  simp only [ezTens, Finsupp.mapDomain_add, Finsupp.sum, smul_add]
  rw [Finset.sum_add_distrib]

lemma ezTens_smul_right (r : ℚ) (e : α →₀ ℚ) (f : β →₀ ℚ) :
    ezTens e (r • f) = r • ezTens e f := by
  rw [ezTens, ezTens, Finsupp.smul_sum]
  refine Finsupp.sum_congr fun x hx => ?_
  rw [Finsupp.mapDomain_smul, smul_comm]

/-- `ezTens` is linear in the first argument. -/
def ezTensL (f : β →₀ ℚ) : (α →₀ ℚ) →ₗ[ℚ] (α × β →₀ ℚ) where
  toFun := fun e => ezTens e f
  map_add' := fun e₁ e₂ => ezTens_add_left e₁ e₂ f
  map_smul' := fun r e => ezTens_smul_left r e f

/-- `ezTens` is linear in the second argument. -/
def ezTensR (e : α →₀ ℚ) : (β →₀ ℚ) →ₗ[ℚ] (α × β →₀ ℚ) where
  toFun := fun f => ezTens e f
  map_add' := fun f₁ f₂ => ezTens_add_right e f₁ f₂
  map_smul' := fun r f => ezTens_smul_right r e f

lemma ezTens_sum_smul_left (s : Finset ι) (r : ι → ℚ) (e : ι → α →₀ ℚ) (f : β →₀ ℚ) :
    ezTens (∑ i ∈ s, r i • e i) f = ∑ i ∈ s, r i • ezTens (e i) f := by
  have h := map_sum (ezTensL (α := α) f) (fun i => r i • e i) s
  have h2 : ∀ i ∈ s, ezTensL (α := α) f (r i • e i) = r i • ezTensL (α := α) f (e i) :=
    fun i _ => map_smul _ _ _
  rw [Finset.sum_congr rfl h2] at h
  simpa only [ezTensL, LinearMap.coe_mk, AddHom.coe_mk] using h

lemma ezTens_sum_smul_right (s : Finset ι) (r : ι → ℚ) (f : ι → β →₀ ℚ) (e : α →₀ ℚ) :
    ezTens e (∑ i ∈ s, r i • f i) = ∑ i ∈ s, r i • ezTens e (f i) := by
  have h := map_sum (ezTensR (β := β) e) (fun i => r i • f i) s
  have h2 : ∀ i ∈ s, ezTensR (β := β) e (r i • f i) = r i • ezTensR (β := β) e (f i) :=
    fun i _ => map_smul _ _ _
  rw [Finset.sum_congr rfl h2] at h
  simpa only [ezTensR, LinearMap.coe_mk, AddHom.coe_mk] using h

/-- `mapDomain` distributes over a finite linear combination. -/
lemma mapDomain_sum_smul (F : α → γ) (s : Finset ι) (r : ι → ℚ) (y : ι → α →₀ ℚ) :
    Finsupp.mapDomain F (∑ i ∈ s, r i • y i) = ∑ i ∈ s, r i • Finsupp.mapDomain F (y i) := by
  have h := map_sum (Finsupp.lmapDomain ℚ ℚ F) (fun i => r i • y i) s
  have h2 : ∀ i ∈ s,
      Finsupp.lmapDomain ℚ ℚ F (r i • y i) = r i • Finsupp.lmapDomain ℚ ℚ F (y i) :=
    fun i _ => map_smul _ _ _
  rw [Finset.sum_congr rfl h2] at h
  simpa only [Finsupp.lmapDomain_apply] using h

theorem ezTens_mapDomain (φ : α → γ) (ψ : β → δ) (e : α →₀ ℚ) (f : β →₀ ℚ) :
    Finsupp.mapDomain (Prod.map φ ψ) (ezTens e f) =
      ezTens (Finsupp.mapDomain φ e) (Finsupp.mapDomain ψ f) := by
  induction e using Finsupp.induction_linear with
  | zero => simp
  | add e₁ e₂ ih₁ ih₂ =>
      rw [ezTens_add_left, Finsupp.mapDomain_add, ih₁, ih₂, Finsupp.mapDomain_add,
        ← ezTens_add_left]
  | single a r =>
      rw [ezTens_single_left, Finsupp.mapDomain_smul, Finsupp.mapDomain_single, ezTens_single_left]
      congr 1
      rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
      exact Finsupp.mapDomain_congr fun y _ => rfl


/-- `ezTens` with the first factor pushed forward along a map. -/
lemma ezTens_mapDomain_fst (φ : α → γ) (e : α →₀ ℚ) (f : β →₀ ℚ) :
    ezTens (Finsupp.mapDomain φ e) f
      = ∑ x ∈ e.support, e x • Finsupp.mapDomain (fun y => (φ x, y)) f := by
  rw [ezTens,
    Finsupp.sum_mapDomain_index (f := φ) (s := e)
      (h := fun x cx => cx • Finsupp.mapDomain (fun y => (x, y)) f)
      (fun x => by simp) (fun x a b => by rw [add_smul])]
  rfl

lemma ezTens_mapDomain_double_sum (φ : α → γ) (e : α →₀ ℚ) (f : β →₀ ℚ) :
    ezTens (Finsupp.mapDomain φ e) f
      = ∑ x ∈ e.support, ∑ y ∈ f.support,
          (e x * f y) • Finsupp.single (φ x, y) 1 := by
  rw [ezTens_mapDomain_fst]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [mapDomain_eq_sum (F := fun y => (φ x, y)), Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_smul]

lemma ezTens_mapDomain_snd_double_sum (ψ : β → δ) (e : α →₀ ℚ) (f : β →₀ ℚ) :
    ezTens e (Finsupp.mapDomain ψ f)
      = ∑ x ∈ e.support, ∑ y ∈ f.support,
          (e x * f y) • Finsupp.single (x, ψ y) 1 := by
  rw [ezTens, Finsupp.sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hcomp : Finsupp.mapDomain (fun y => (x, y)) (Finsupp.mapDomain ψ f)
      = Finsupp.mapDomain (fun y => (x, ψ y)) f := by
    rw [← Finsupp.mapDomain_comp (f := ψ) (g := fun y => (x, y))]
    exact Finsupp.mapDomain_congr fun y _ => rfl
  rw [hcomp, mapDomain_eq_sum (F := fun y => (x, ψ y))]
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [smul_smul]

/-- Reordering a fourfold sum: the two outer indices and the two inner indices. -/
lemma sum_sum_sum_sum_comm {α β ι κ M : Type*} [AddCommMonoid M]
    (s : Finset α) (t : Finset β) (u : Finset ι) (v : Finset κ) (F : α → β → ι → κ → M) :
    (∑ a ∈ s, ∑ b ∈ t, ∑ i ∈ u, ∑ k ∈ v, F a b i k)
      = ∑ k ∈ v, ∑ i ∈ u, ∑ a ∈ s, ∑ b ∈ t, F a b i k := by
  trans ∑ a ∈ s, ∑ i ∈ u, ∑ b ∈ t, ∑ k ∈ v, F a b i k
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
  trans ∑ a ∈ s, ∑ i ∈ u, ∑ k ∈ v, ∑ b ∈ t, F a b i k
  · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  trans ∑ i ∈ u, ∑ a ∈ s, ∑ k ∈ v, ∑ b ∈ t, F a b i k
  · rw [Finset.sum_comm]
  trans ∑ i ∈ u, ∑ k ∈ v, ∑ a ∈ s, ∑ b ∈ t, F a b i k
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  · rw [Finset.sum_comm]

/-- Pulling a scalar out of a finite sum. -/
lemma sum_smul_factor {ι M : Type*} [AddCommMonoid M] [Module ℚ M] (r : ℚ) (s : Finset ι)
    (g : ι → M) : (∑ i ∈ s, r • g i) = r • ∑ i ∈ s, g i := by
  rw [Finset.smul_sum]

/-- Pulling a scalar out of a double sum. -/
lemma sum_sum_smul_factor {α β M : Type*} [AddCommMonoid M] [Module ℚ M] (r : ℚ)
    (s : Finset α) (t : Finset β) (g : α → β → M) :
    (∑ a ∈ s, ∑ b ∈ t, r • g a b) = r • ∑ a ∈ s, ∑ b ∈ t, g a b := by
  simp only [Finset.smul_sum]


/-- A finitely supported function is the sum of its single terms. -/
lemma sum_smul_single_eq (e : α →₀ ℚ) :
    (∑ x ∈ e.support, e x • Finsupp.single x 1) = e := by
  have h1 : (∑ x ∈ e.support, e x • Finsupp.single x 1)
      = ∑ x ∈ e.support, Finsupp.single x (e x) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [h1]
  exact Finsupp.sum_single e

/-- `mapDomain` distributes over a double finite linear combination. -/
lemma mapDomain_sum_sum_smul (F : α → γ) (s : Finset ι) (t : Finset κ) (r : ι → κ → ℚ)
    (y : ι → κ → α →₀ ℚ) :
    Finsupp.mapDomain F (∑ i ∈ s, ∑ j ∈ t, r i j • y i j)
      = ∑ i ∈ s, ∑ j ∈ t, r i j • Finsupp.mapDomain F (y i j) := by
  conv_lhs => rw [← Finsupp.lmapDomain_apply ℚ ℚ F]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, Finsupp.lmapDomain_apply]

/-- The boundary of a chain, expanded as a sum of pushforwards along the face maps. -/
lemma sbdry_eq_sum_mapDomain (S : SSet.{0}) (n : ℕ)
    (c : Submission.Cohomology.SChain S ℚ (n+1)) :
    Submission.Cohomology.sbdry S ℚ n c
      = ∑ i : Fin (n+2), (-1 : ℚ) ^ (i : ℕ) • Finsupp.mapDomain (S.δ i) c := by
  rw [Submission.Cohomology.sbdry]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.lmapDomain_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Int.cast_smul_eq_zsmul ℚ]
  congr 1
  push_cast
  ring

end

end Work.Cohomology
