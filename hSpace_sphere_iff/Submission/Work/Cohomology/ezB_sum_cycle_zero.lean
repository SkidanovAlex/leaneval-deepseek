/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: hSpace_sphere_iff team

# The `b`-side of the Eilenberg–Zilber shuffle identity vanishes on cycles

`Work.Cohomology.ezB P Q a b` is the `b`-side of the boundary of the shuffle chain of
`a : X_{P+1}` and `b : Y_{Q+1}`: it is `∑ j, (-1)^j • ∑ A (sgnA A) • single (φ_A a, ψ_A (δ_j b)) 1`
where `φ_A = X.map (shA A _).op`, `ψ_A = Y.map (shB A _).op`, the sum over `A` ranging over
`{A : Finset (Fin ((P+1)+Q)) // A.card = P+1}`.

We prove here that the `(c,d)`-weighted sum of `ezB` over two chains vanishes as soon as `d` is a
cycle, `∂d = 0`.  The proof is the one sketched in the statement of the lemma, using only the
homological algebra of the external product `ezTens` from `Submission.Work.Cohomology.EZTensor`:

* `Ω(A,j) := ∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • single (φ_A a, ψ_A (Y.δ j b)) 1`
  equals `Finsupp.mapDomain (Prod.map φ_A ψ_A) (ezTens c (Finsupp.mapDomain (Y.δ j) d))`
  (`mapDomain_ezTens_mapDomain_double_sum`, which is `ezTens_mapDomain_snd_double_sum` pushed
  forward along `mapDomain`);
* hence `∑ a ∑ b (c a * d b) • ezB P Q a b = ∑ A (sgnA A) • ∑ j (-1)^j • Ω(A,j)`
  (unfold `ezB` and commute the four sums / factor the scalars; `ezB_rearrange`,
  `sum_support_support_smul_sum_index`, `sum_sum_sum_sum_comm`, `Finset.smul_sum`, `smul_smul`);
* for each `A`,
  `∑ j (-1)^j • Ω(A,j) = mapDomain F (∑ j (-1)^j • ezTens c (mapDomain (Y.δ j) d))`
  (`mapDomain_sum_smul`), which is `mapDomain F (ezTens c (∑ j (-1)^j • mapDomain (Y.δ j) d))`
  (`ezTens_sum_smul_right`), i.e. `mapDomain F (ezTens c (sbdry Y ℚ Q d))`
  (`sbdry_eq_sum_mapDomain`), i.e. `0` (`hd`, `ezTens_zero_right`, `Finsupp.mapDomain_zero`).
-/
import Mathlib
import Submission.Work.Cohomology.EZAssembly
import Submission.Work.Cohomology.EZTensor

open CategoryTheory Simplicial Opposite

namespace Work.Cohomology

noncomputable section

variable {X Y : SSet.{0}}

/-! ### The staircase point of a shuffle

`ezPoint P Q A a y` is the `(P+1+Q)`-simplex of `X ⊗ Y` obtained from the `a`-face and the
`y`-face of a `(P+1,Q)`-shuffle `A`.  It is packaged as a definition with the tensor type so that
the terms built from it live syntactically in `X ⊗ Y` rather than in the product type. -/

/-- The shuffle point of the pair of simplices `a ∈ X_{P+1}`, `y ∈ Y_Q` and the shuffle `A`. -/
def ezPoint (P Q : ℕ) (A : {A : Finset (Fin ((P+1)+Q)) // A.card = P+1})
    (a : X.obj (op ⦋P+1⦌)) (y : Y.obj (op ⦋Q⦌)) :
    (MonoidalCategoryStruct.tensorObj X Y).obj (op ⦋(P+1)+Q⦌) :=
  (X.map (shA A.1 (by have := A.2; omega)).op a,
   Y.map (shB A.1 (by have := A.2; omega)).op y)

/-- The `b`-side of the shuffle chain, expanded into the shuffle sums: this is `ezB` with the
staircase points written in the tensor type. -/
lemma ezB_eq_sum_expanded (P Q : ℕ) (a : X.obj (op ⦋P+1⦌)) (b : Y.obj (op ⦋Q+1⦌)) :
    ezB P Q a b = ∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) •
      ∑ A : {A : Finset (Fin ((P+1)+Q)) // A.card = P+1}, (sgnA A.1 : ℚ) •
        Finsupp.single (ezPoint P Q A a (Y.δ j b)) (1 : ℚ) := rfl

/-! ### Reordering a fourfold sum with scalars

The combinatorial heart of the rearrangement: the sum over `(a,b)` of a scalar `ca a * db b`
times a sum over `(j,A)` of a scalar `r j * k A` times `Z a b j A` may be reorganized as a sum
over `A` of `k A` times a sum over `j` of `r j` times a sum over `(a,b)`. -/

/-- Reordering a fourfold sum with scalars: the `(a,b)`-sums (with scalar `ca a * db b`) may be
moved inside the `(j,A)`-sums (with scalars `r j` and `k A`). -/
lemma sum_support_support_smul_sum_index {α β ι κ M : Type*} [AddCommMonoid M] [Module ℚ M]
    (s : Finset α) (t : Finset β) (J : Finset ι) (As : Finset κ)
    (ca : α → ℚ) (db : β → ℚ) (r : ι → ℚ) (k : κ → ℚ) (Z : α → β → ι → κ → M) :
    (∑ a ∈ s, ∑ b ∈ t, (ca a * db b) • (∑ j ∈ J, r j • ∑ A ∈ As, k A • Z a b j A))
      = ∑ A ∈ As, k A • (∑ j ∈ J, r j • ∑ a ∈ s, ∑ b ∈ t, (ca a * db b) • Z a b j A) := by
  have step1 : ∀ a b, (ca a * db b) • (∑ j ∈ J, r j • ∑ A ∈ As, k A • Z a b j A)
      = ∑ j ∈ J, ∑ A ∈ As, ((ca a * db b) * r j * k A) • Z a b j A := by
    intro a b
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [smul_smul]
  have step2 : ∀ A j, k A • (r j • ∑ a ∈ s, ∑ b ∈ t, (ca a * db b) • Z a b j A)
      = ∑ a ∈ s, ∑ b ∈ t, (k A * r j * (ca a * db b)) • Z a b j A := by
    intro A j
    rw [smul_smul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [smul_smul]
  calc (∑ a ∈ s, ∑ b ∈ t, (ca a * db b) • (∑ j ∈ J, r j • ∑ A ∈ As, k A • Z a b j A))
      = ∑ a ∈ s, ∑ b ∈ t, ∑ j ∈ J, ∑ A ∈ As, ((ca a * db b) * r j * k A) • Z a b j A := by
        simp only [step1]
    _ = ∑ A ∈ As, ∑ j ∈ J, ∑ a ∈ s, ∑ b ∈ t, ((ca a * db b) * r j * k A) • Z a b j A :=
        sum_sum_sum_sum_comm s t J As _
    _ = ∑ A ∈ As, ∑ j ∈ J, ∑ a ∈ s, ∑ b ∈ t, (k A * r j * (ca a * db b)) • Z a b j A := by
        refine Finset.sum_congr rfl fun A _ => Finset.sum_congr rfl fun j _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        rw [show (ca a * db b) * r j * k A = k A * r j * (ca a * db b) by ring]
    _ = ∑ A ∈ As, k A • (∑ j ∈ J, r j • ∑ a ∈ s, ∑ b ∈ t, (ca a * db b) • Z a b j A) := by
        refine Finset.sum_congr rfl fun A _ => ?_
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        exact (step2 A j).symm

/-! ### The external product against a face -/

/-- Pushing the external product `ezTens e (mapDomain χ f)` forward along a map `F` which is
applied to the pairs `(x, χ y)` identifies it with the double sum of the single terms. -/
lemma mapDomain_ezTens_mapDomain_double_sum {α β β₀ γ : Type*}
    (F : α × β₀ → γ) (χ : β → β₀) (e : α →₀ ℚ) (f : β →₀ ℚ) :
    Finsupp.mapDomain F (ezTens e (Finsupp.mapDomain χ f))
      = ∑ x ∈ e.support, ∑ y ∈ f.support, (e x * f y) • Finsupp.single (F (x, χ y)) 1 := by
  rw [ezTens_mapDomain_snd_double_sum]
  rw [Finsupp.mapDomain_finsetSum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finsupp.mapDomain_finsetSum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finsupp.mapDomain_smul, Finsupp.mapDomain_single]

/-- The alternating sum, over the faces of `d`, of the pushforward of the external product with
`c` vanishes when `d` is a cycle. -/
lemma sum_alt_mapDomain_ezTens_zero (P Q : ℕ)
    (c : Submission.Cohomology.SChain X ℚ (P+1)) (d : Submission.Cohomology.SChain Y ℚ (Q+1))
    (hd : Submission.Cohomology.sbdry Y ℚ Q d = 0)
    (F : X.obj (op ⦋P+1⦌) × Y.obj (op ⦋Q⦌) →
      (MonoidalCategoryStruct.tensorObj X Y).obj (op ⦋(P+1)+Q⦌)) :
    (∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) •
      Finsupp.mapDomain F (ezTens c (Finsupp.mapDomain (Y.δ j) d))) = 0 := by
  rw [← mapDomain_sum_smul F (Finset.univ : Finset (Fin (Q+2)))
        (fun j : Fin (Q+2) => (-1 : ℚ) ^ (j : ℕ))
        (fun j : Fin (Q+2) => ezTens c (Finsupp.mapDomain (Y.δ j) d))]
  rw [← ezTens_sum_smul_right]
  rw [← sbdry_eq_sum_mapDomain Y Q d, hd]
  simp only [ezTens_zero_right, Finsupp.mapDomain_zero]

/-- The contribution of one shuffle `A`: the alternating sum over the faces of `d` of the
weighted single terms vanishes when `d` is a cycle. -/
lemma ezB_inner_zero (P Q : ℕ)
    (c : Submission.Cohomology.SChain X ℚ (P+1)) (d : Submission.Cohomology.SChain Y ℚ (Q+1))
    (hd : Submission.Cohomology.sbdry Y ℚ Q d = 0)
    (A : {A : Finset (Fin ((P+1)+Q)) // A.card = P+1}) :
    (∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) •
      ∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) •
        Finsupp.single (ezPoint P Q A a (Y.δ j b)) (1 : ℚ)) = 0 := by
  have h : ∀ j : Fin (Q+2),
      (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) •
          Finsupp.single (ezPoint P Q A a (Y.δ j b)) (1 : ℚ))
        = Finsupp.mapDomain (fun p : X.obj (op ⦋P+1⦌) × Y.obj (op ⦋Q⦌) =>
              ezPoint P Q A p.1 p.2)
            (ezTens c (Finsupp.mapDomain (Y.δ j) d)) := by
    intro j
    rw [mapDomain_ezTens_mapDomain_double_sum]
  have h2 : (∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) •
        ∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) •
          Finsupp.single (ezPoint P Q A a (Y.δ j b)) (1 : ℚ))
      = (∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) • Finsupp.mapDomain
          (fun p : X.obj (op ⦋P+1⦌) × Y.obj (op ⦋Q⦌) => ezPoint P Q A p.1 p.2)
          (ezTens c (Finsupp.mapDomain (Y.δ j) d))) :=
    Finset.sum_congr rfl fun j _ => by rw [h j]
  rw [h2]
  exact sum_alt_mapDomain_ezTens_zero P Q c d hd
    (fun p : X.obj (op ⦋P+1⦌) × Y.obj (op ⦋Q⦌) => ezPoint P Q A p.1 p.2)

/-- `(c,d)`-weighted sum of `ezB`, rewritten as a sum over the shuffles `A`. -/
lemma ezB_rearrange (P Q : ℕ)
    (c : Submission.Cohomology.SChain X ℚ (P+1)) (d : Submission.Cohomology.SChain Y ℚ (Q+1)) :
    (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezB P Q a b)
      = ∑ A : {A : Finset (Fin ((P+1)+Q)) // A.card = P+1}, (sgnA A.1 : ℚ) •
          (∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) •
            ∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) •
              Finsupp.single (ezPoint P Q A a (Y.δ j b)) (1 : ℚ)) := by
  have h1 : (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • ezB P Q a b)
      = (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) •
          (∑ j : Fin (Q+2), (-1 : ℚ) ^ (j : ℕ) •
            ∑ A : {A : Finset (Fin ((P+1)+Q)) // A.card = P+1}, (sgnA A.1 : ℚ) •
              Finsupp.single (ezPoint P Q A a (Y.δ j b)) (1 : ℚ))) := by
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [ezB_eq_sum_expanded]
  rw [h1]
  exact sum_support_support_smul_sum_index c.support d.support Finset.univ Finset.univ c d
    (fun j : Fin (Q+2) => (-1 : ℚ) ^ (j : ℕ))
    (fun A : {A : Finset (Fin ((P+1)+Q)) // A.card = P+1} => (sgnA A.1 : ℚ))
    (fun a b j A => Finsupp.single (ezPoint P Q A a (Y.δ j b)) (1 : ℚ))

/-
The `b`-side of the Eilenberg-Zilber shuffle identity vanishes on cycles.

`Work.Cohomology.ezB P Q a b` is the `b`-side of the boundary of the shuffle chain of
`a : X_{P+1}` and `b : Y_{Q+1}`: it is `∑ j, (-1)^j • ∑ A (sgnA A) • single (φ_A a, ψ_A (δ_j b)) 1`
where `φ_A = X.map (shA A _).op`, `ψ_A = Y.map (shB A _).op`, the sum over `A` ranging over
`{A : Finset (Fin ((P+1)+Q)) // A.card = P+1}`.

The claim is that the `(c,d)`-weighted sum of `ezB` over two chains vanishes as soon as
`d` is a cycle, `∂d = 0`.  All the tools needed are in `Submission.Work.Cohomology.EZTensor`:

* `Ω(A,j) := ∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • single (φ_A a, ψ_A (Y.δ j b)) 1`
  equals `Finsupp.mapDomain (Prod.map φ_A ψ_A) (ezTens c (Finsupp.mapDomain (Y.δ j) d))`
  (`ezTens_mapDomain_snd_double_sum`, applied backwards, together with `mapDomain_sum_smul`);
* hence `∑ a ∑ b (c a * d b) • ezB P Q a b = ∑ A (sgnA A) • ∑ j (-1)^j • Ω(A,j)`
  (unfold `ezB` and commute the four sums / factor the scalars; `sum_sum_sum_sum_comm`,
  `Finset.smul_sum`, `smul_smul`);
* for each `A`, `∑ j (-1)^j • Ω(A,j) = mapDomain (Prod.map φ_A ψ_A) (∑ j (-1)^j • ezTens c (mapDomain (Y.δ j) d))`
  (`mapDomain_sum_smul`), which is `mapDomain (Prod.map φ_A ψ_A) (ezTens c (∑ j (-1)^j • mapDomain (Y.δ j) d))`
  (`ezTens_sum_smul_right`), i.e. `mapDomain (Prod.map φ_A ψ_A) (ezTens c (sbdry Y ℚ Q d))`
  (`sbdry_eq_sum_mapDomain`), i.e. `0` (`hd`, `ezTens_zero_right`, `Finsupp.mapDomain_zero`).
-/
theorem ezB_sum_cycle_zero (P Q : ℕ) {X Y : SSet.{0}}
    (c : Submission.Cohomology.SChain X ℚ (P+1)) (d : Submission.Cohomology.SChain Y ℚ (Q+1))
    (hd : Submission.Cohomology.sbdry Y ℚ Q d = 0) :
    (∑ a ∈ c.support, ∑ b ∈ d.support, (c a * d b) • Work.Cohomology.ezB P Q a b) = 0 := by
  rw [ezB_rearrange]
  refine Finset.sum_eq_zero fun A _ => ?_
  rw [smul_eq_zero]
  exact Or.inr (ezB_inner_zero P Q c d hd A)

end

end Work.Cohomology
