/-
Area DSCOH (curric-46) — the normalization comparison: the *sorting homotopy* of Stacks 01FG.

Definitions for the "first homotopy" of Stacks, Section 20.23 (Tag 01FG, Equation 20.23.6.1):
the section `semiLift` of `semiProj` (the "signed sorting" map) is homotopic to the identity of
Mathlib's unnormalized Čech complex, via

  `h(s)_{i_0…i_p} = Σ_{a=0}^{p} (-1)^a sign(σ_a) s_{i_{σ(0)}…i_{σ(a)} i_{σ_a(a)}…i_{σ_a(p)}}`

where `σ = Tuple.sort (i_0,…,i_p)` and `σ_a` agrees with `σ` on `{0,…,a-1}` and is increasing on
`{a,…,p}`.

This file sets up only the definitions and their elementary API; the (long) combinatorial
verification of the homotopy identity is in `Submission.Work.DSCOH.Norm.firstHom_matched` and
`Submission.Work.DSCOH.Norm.firstHom_leftover`.
-/
import Mathlib
import Submission.Work.DSCOH.Norm.SortSection
import Submission.Work.DSCOH.Norm.cechComplexFunctor_d_comp

namespace Work.DSCOH.Norm
open CategoryTheory Limits Opposite TopologicalSpace
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

universe u v w u'
variable {X : Type u} [TopologicalSpace X] {A : Type v} [CommRing A]
variable {ι : Type w} [LinearOrder ι] [Fintype ι]

theorem filter_card_lt {n : ℕ} (a : Fin n) :
    (Finset.univ.filter (fun j : Fin n => j.val < a.val)).card = a.val := by
  have h1 : (Finset.univ.filter (fun j : Fin n => j.val < a.val)).card
      = Fintype.card {j : Fin n // j.val < a.val} := by rw [Fintype.card_subtype]
  have h2 : Fintype.card {j : Fin n // j.val < a.val} = Fintype.card (Fin a.val) :=
    Fintype.card_congr
      { toFun := fun j => ⟨j.1.val, j.2⟩,
        invFun := fun i => ⟨⟨i.1, by omega⟩, i.2⟩,
        left_inv := by intro j; ext; simp,
        right_inv := by intro i; ext; simp }
  rw [h1, h2, Fintype.card_fin]

noncomputable def headVal {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) : Finset (Fin (k+1)) :=
  (Finset.univ.filter (fun j : Fin (k+1) => (j:ℕ) < (a:ℕ))).image (fun j => Tuple.sort x j)

lemma headVal_card {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) :
    (headVal x a).card = (a:ℕ) := by
  rw [headVal, Finset.card_image_of_injective]
  · exact filter_card_lt a
  · intro j j' h; exact (Tuple.sort x).injective h

lemma compl_card {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) :
    (headVal x a)ᶜ.card = (k+1) - (a:ℕ) := by
  rw [Finset.card_compl, headVal_card, Fintype.card_fin]

noncomputable def tailEmb {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) :
    Fin ((k+1) - (a:ℕ)) ↪o Fin (k+1) :=
  (headVal x a)ᶜ.orderEmbOfFin (compl_card x a)

lemma tailEmb_mem {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1))
    (m : Fin ((k+1) - (a:ℕ))) : (tailEmb x a m : Fin (k+1)) ∉ headVal x a :=
  Finset.mem_compl.mp (Finset.orderEmbOfFin_mem (headVal x a)ᶜ (compl_card x a) m)

noncomputable def sigmaA {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) : Fin (k+1) → Fin (k+1) :=
  fun j => if h : (j:ℕ) < (a:ℕ) then Tuple.sort x j
           else tailEmb x a ⟨(j:ℕ) - (a:ℕ), by have := j.isLt; omega⟩

lemma sigmaA_head {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) {j : Fin (k+1)}
    (hj : (j:ℕ) < (a:ℕ)) : sigmaA x a j = Tuple.sort x j := dif_pos hj

lemma sigmaA_tail {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) {j : Fin (k+1)}
    (hj : ¬ (j:ℕ) < (a:ℕ)) :
    sigmaA x a j = tailEmb x a ⟨(j:ℕ) - (a:ℕ), by have := j.isLt; omega⟩ := dif_neg hj

lemma sigmaA_tail_inj {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) {j j' : Fin (k+1)}
    (hj : ¬ (j:ℕ) < (a:ℕ)) (hj' : ¬ (j':ℕ) < (a:ℕ)) (h : sigmaA x a j = sigmaA x a j') :
    j = j' := by
  rw [sigmaA_tail x a hj, sigmaA_tail x a hj'] at h
  have h1 : (⟨(j:ℕ) - (a:ℕ), by have := j.isLt; omega⟩ : Fin ((k+1) - (a:ℕ)))
      = ⟨(j':ℕ) - (a:ℕ), by have := j'.isLt; omega⟩ := (tailEmb x a).injective h
  have h2 : (j:ℕ) - (a:ℕ) = (j':ℕ) - (a:ℕ) := by simpa using congrArg Fin.val h1
  have haj : (a:ℕ) ≤ (j:ℕ) := by omega
  have haj' : (a:ℕ) ≤ (j':ℕ) := by omega
  exact Fin.ext (by omega)

lemma sigmaA_injective {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) :
    Function.Injective (sigmaA x a) := by
  intro j j' h
  by_cases hj : (j:ℕ) < (a:ℕ)
  · by_cases hj' : (j':ℕ) < (a:ℕ)
    · rw [sigmaA_head x a hj, sigmaA_head x a hj'] at h
      exact (Tuple.sort x).injective h
    · exfalso
      rw [sigmaA_head x a hj, sigmaA_tail x a hj'] at h
      have := tailEmb_mem x a ⟨(j':ℕ) - (a:ℕ), by have := j'.isLt; omega⟩
      exact this (h ▸ Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩, rfl⟩)
  · by_cases hj' : (j':ℕ) < (a:ℕ)
    · exfalso
      rw [sigmaA_tail x a hj, sigmaA_head x a hj'] at h
      have := tailEmb_mem x a ⟨(j:ℕ) - (a:ℕ), by have := j.isLt; omega⟩
      exact this (h ▸ Finset.mem_image.mpr ⟨j', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj'⟩, rfl⟩)
    · exact sigmaA_tail_inj x a hj hj' h

lemma sigmaA_surjective {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) :
    Function.Surjective (sigmaA x a) := by
  intro v
  by_cases hv : v ∈ headVal x a
  · obtain ⟨j, hjmem, hjeq⟩ := Finset.mem_image.mp hv
    exact ⟨j, by rw [sigmaA_head x a (Finset.mem_filter.mp hjmem).2]; exact hjeq⟩
  · have hv' : v ∈ (headVal x a)ᶜ := Finset.mem_compl.mpr hv
    have hv2 : v ∈ Set.range (⇑((headVal x a)ᶜ.orderEmbOfFin (compl_card x a))) := by
      rw [Finset.range_orderEmbOfFin]; exact hv'
    obtain ⟨m, hm⟩ := hv2
    refine ⟨⟨(a:ℕ) + m.val, by have := m.isLt; omega⟩, ?_⟩
    rw [sigmaA_tail x a (by simp only [Fin.val_mk]; omega)]
    have hme : (⟨(↑a + ↑m) - ↑a, by have := m.isLt; omega⟩ : Fin ((k+1) - (a:ℕ))) = m :=
      Fin.ext (Nat.add_sub_cancel_left _ _)
    rw [hme]
    exact hm

noncomputable def sigmaAPerm {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) :
    Equiv.Perm (Fin (k+1)) :=
  Equiv.ofBijective (sigmaA x a) ⟨sigmaA_injective x a, sigmaA_surjective x a⟩

lemma sigmaAPerm_apply {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) (j : Fin (k+1)) :
    sigmaAPerm x a j = sigmaA x a j := rfl

noncomputable def signA {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) : ℤ :=
  ((Equiv.Perm.sign (sigmaAPerm x a) : ℤˣ) : ℤ)

/-! ## The tuple `zA` and the homotopy -/

/-- The `p`-th "read" of the tuple `zA a x`: the head reads `Tuple.sort x` and the tail reads the
increasing enumeration of the complement of the head values. -/
noncomputable def readA {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) : Fin (k+2) → Fin (k+1) :=
  fun p => if h : (p:ℕ) ≤ (a:ℕ) then Tuple.sort x ⟨(p:ℕ), by have := p.isLt; omega⟩
           else tailEmb x a ⟨(p:ℕ) - 1 - (a:ℕ), by have := p.isLt; omega⟩

lemma readA_head {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) {p : Fin (k+2)}
    (hp : (p:ℕ) ≤ (a:ℕ)) :
    readA x a p = Tuple.sort x ⟨(p:ℕ), by have := p.isLt; omega⟩ := dif_pos hp

lemma readA_tail {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) {p : Fin (k+2)}
    (hp : ¬ (p:ℕ) ≤ (a:ℕ)) :
    readA x a p = tailEmb x a ⟨(p:ℕ) - 1 - (a:ℕ), by have := p.isLt; omega⟩ := dif_neg hp

/-- The tuple `zA a x` on which the `a`-th term of the sorting homotopy reads `s`. -/
noncomputable def zA {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) : Fin (k+2) → ι :=
  x ∘ readA x a

@[simp] lemma zA_apply {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) (p : Fin (k+2)) :
    zA x a p = x (readA x a p) := rfl

/-- The canonical morphism `∏ᶜ (U ∘ x) ⟶ ∏ᶜ (U ∘ zA a x)` of opens. -/
noncomputable def opZ (U : ι → Opens X) {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) :
    tupleOp U x ⟶ tupleOp U (zA x a) :=
  Pi.lift fun p => Pi.π (fun j : Fin (k+1) => U (x j)) (readA x a p)

/-- The canonical restriction `tupleMod (zA a x) ⟶ tupleMod x`. -/
noncomputable def resA (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) {k : ℕ}
    (x : Fin (k+1) → ι) (a : Fin (k+1)) : tupleMod P U (zA x a) ⟶ tupleMod P U x :=
  P.map (opZ U x a).op

/-- The rank of `σ(a)` in the complement of the head values: the index at which `σ(a)` occurs in
the increasing enumeration of the complement. -/
noncomputable def rankA {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) : ℕ :=
  ((headVal x a)ᶜ.filter (fun v : Fin (k+1) => v < Tuple.sort x a)).card

lemma sortA_mem_compl {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) :
    Tuple.sort x a ∈ (headVal x a)ᶜ := by
  rw [Finset.mem_compl, headVal]
  intro hcon
  obtain ⟨j, hj, hje⟩ := Finset.mem_image.mp hcon
  rw [Finset.mem_filter] at hj
  have : j = a := (Tuple.sort x).injective hje
  omega

lemma rankA_lt {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) :
    rankA x a < (headVal x a)ᶜ.card := by
  rw [rankA]
  apply Finset.card_lt_card
  refine ⟨Finset.filter_subset _ _, fun hsub => ?_⟩
  have h1 : Tuple.sort x a ∈ (headVal x a)ᶜ.filter (fun v : Fin (k+1) => v < Tuple.sort x a) :=
    hsub (sortA_mem_compl x a)
  rw [Finset.mem_filter] at h1
  exact absurd h1.2 (lt_irrefl _)

/-- The second position at which `zA a x` reads the value `σ(a)` (the first being position `a`). -/
noncomputable def pos2A {k : ℕ} (x : Fin (k+1) → ι) (a : Fin (k+1)) : Fin (k+2) :=
  ⟨(a:ℕ) + 1 + rankA x a, by
    have := rankA_lt x a; rw [compl_card] at this; have := a.isLt; omega⟩

/-- The `n`-th term of Mathlib's unnormalized Čech complex, written as an explicit product (it is
definitionally equal to `((cechComplexFunctor U).obj P).X n`). -/
noncomputable abbrev allTerm (P : (Opens X)ᵒᵖ ⥤ ModuleCat.{max u' w, v} A) (U : ι → Opens X) (n : ℕ) :
    ModuleCat.{max u' w, v} A :=
  ∏ᶜ fun y : Fin (n+1) → ι => tupleMod P U y

/-- **The sorting homotopy** `X (k+1) ⟶ X k` (Stacks 01FG, Equation 20.23.6.1): the `x`-component
is `Σ_a (-1)^a sign(σ_a) • (π_{zA a x} ≫ resA a x)`. -/
noncomputable def firstHom [HasProducts (ModuleCat A)] (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) (k : ℕ) :
    allTerm P U (k+1) ⟶ allTerm P U k :=
  Pi.lift fun x : Fin (k+1) → ι =>
    ∑ a : Fin (k+1), ((-1 : ℤ) ^ (a : ℕ) * signA x a) •
      (Pi.π (fun y : Fin (k+2) → ι => tupleMod P U y) (zA x a) ≫ resA P U x a)

/-- The `x`-th projection of the all-tuples Čech term, with the source spelled as
`((cechComplexFunctor U).obj P).X n` (so that composites typecheck without unfolding). -/
lemma firstHom_comp_piX [HasProducts (ModuleCat A)]
    (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) (k : ℕ) (x : Fin (k+1) → ι) :
    firstHom P U k ≫ Pi.π (fun y : Fin (k+1) → ι => tupleMod P U y) x =
      ∑ a : Fin (k+1), ((-1 : ℤ) ^ (a : ℕ) * signA x a) •
        (Pi.π (fun y : Fin (k+2) → ι => tupleMod P U y) (zA x a) ≫ resA P U x a) :=
  Pi.lift_comp_π _ _

noncomputable def piX [HasProducts (ModuleCat A)] (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) (n : ℕ)
    (x : Fin (n+1) → ι) :
    allTerm P U n ⟶ tupleMod P U x :=
  Pi.π (fun y : Fin (n+1) → ι => tupleMod P U y) x

/-- The `(a,b)`-term of the expansion of `d (k+1) (k+2) ≫ firstHom (k+1)` into components, as a
morphism into the `x`-component. -/
noncomputable def dhTerm [HasProducts (ModuleCat A)] (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) {k : ℕ}
    (x : Fin (k+2) → ι) (a : Fin (k+2)) (b : Fin (k+3)) :
    allTerm P U (k+1) ⟶ tupleMod P U x :=
  ((-1 : ℤ) ^ ((a : ℕ) + (b : ℕ)) * signA x a) •
    (Pi.π (fun y : Fin (k+2) → ι => tupleMod P U y) (del (zA x a) b) ≫
      resDel P U (zA x a) b ≫ resA P U x a)

/-- The `(c,a')`-term of the expansion of `firstHom k ≫ d k (k+1)` into components, as a
morphism into the `x`-component. -/
noncomputable def hdTerm [HasProducts (ModuleCat A)] (P : (Opens X)ᵒᵖ ⥤ ModuleCat A) (U : ι → Opens X) {k : ℕ}
    (x : Fin (k+2) → ι) (c : Fin (k+2)) (a' : Fin (k+1)) :
    allTerm P U (k+1) ⟶ tupleMod P U x :=
  ((-1 : ℤ) ^ ((c : ℕ) + (a' : ℕ)) * signA (del x c) a') •
    (Pi.π (fun y : Fin (k+2) → ι => tupleMod P U y) (zA (del x c) a') ≫
      resA P U (del x c) a' ≫ resDel P U x c)

end Work.DSCOH.Norm
