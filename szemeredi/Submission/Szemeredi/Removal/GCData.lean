import Mathlib
import Submission.Szemeredi.Removal.Bundle

/-!
# Abstract data for the generalized counting lemma (Tao, §4)

This file sets up the abstract hypotheses (H1)–(H4) that the generalized counting
lemma (`gencount`) takes as input, together with the elementary product/Fubini
machinery for bundle point spaces used in the Cauchy–Schwarz step.
-/

open scoped BigOperators
open Finset
open Szemeredi.Removal.SigAlg

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Szemeredi.Removal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {V : ι → Type*} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)] [∀ i, Nonempty (V i)]

/-- Splitting the coordinates of a bundle into those of an edge `g` and the rest. -/
noncomputable def combine {κ : Type*} [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (w : (k : {k // k ∈ g}) → V (π k.val))
    (u : (k : {k // k ∉ g}) → V (π k.val)) : BPt V π :=
  fun k => if h : k ∈ g then w ⟨k, h⟩ else u ⟨k, h⟩

theorem combine_apply_mem {κ : Type*} [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (w : (k : {k // k ∈ g}) → V (π k.val))
    (u : (k : {k // k ∉ g}) → V (π k.val)) {k : κ} (hk : k ∈ g) :
    combine π g w u k = w ⟨k, hk⟩ := dif_pos hk

theorem combine_apply_notMem {κ : Type*} [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (w : (k : {k // k ∈ g}) → V (π k.val))
    (u : (k : {k // k ∉ g}) → V (π k.val)) {k : κ} (hk : k ∉ g) :
    combine π g w u k = u ⟨k, hk⟩ := dif_neg hk

theorem restrict_combine {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (w : (k : {k // k ∈ g}) → V (π k.val))
    (u : (k : {k // k ∉ g}) → V (π k.val)) :
    restrict (V := fun k => V (π k)) (combine (V := V) π g w u) g = w := by
  funext k
  exact combine_apply_mem (V := V) π g w u k.2

/-- Fubini for the average on a product type. -/
theorem avg_prod {α β : Type*} [Fintype α] [Fintype β] (g : α → β → ℝ) :
    avg (fun p : α × β => g p.1 p.2) = avg (fun a => avg (fun b => g a b)) := by
  unfold avg
  have hsum : (∑ p : α × β, g p.1 p.2) = ∑ a, ∑ b, g a b := by
    rw [show (∑ p : α × β, g p.1 p.2)
        = ∑ p ∈ (Finset.univ : Finset (α × β)), g p.1 p.2 from rfl]
    rw [← Finset.univ_product_univ, Finset.sum_product]
  rw [hsum, Fintype.card_prod]
  push_cast
  have hR : (∑ a, (∑ b, g a b) / (Fintype.card β : ℝ))
      = (∑ a, ∑ b, g a b) / (Fintype.card β : ℝ) := by
    rw [Finset.sum_div]
  rw [hR, div_div, mul_comm]

/-- Swapping the order of two averages. -/
theorem avg_swap {α β : Type*} [Fintype α] [Fintype β] (f : α → β → ℝ) :
    avg (fun a : α => avg (fun b : β => f a b))
      = avg (fun b : β => avg (fun a : α => f a b)) := by
  rw [← avg_prod (g := fun a b => f a b), ← avg_prod (g := fun b a => f a b)]
  exact (avg_equiv' (Equiv.prodComm β α) (fun p : α × β => f p.1 p.2)).symm

/-- **Triple Fubini**, second form: averaging a function of three variables over `γ × (α × β)`
equals the iterated average with the third variable outermost. -/
theorem avg3' {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℝ) :
    avg (fun q : γ × (α × β) => f q.2.1 q.2.2 q.1)
      = avg (fun c : γ => avg (fun a : α => avg (fun b : β => f a b c))) := by
  rw [avg_prod (α := γ) (β := α × β) (g := fun c q => f q.1 q.2 c)]
  congr 1
  funext c
  exact avg_prod (α := α) (β := β) (g := fun a b => f a b c)

/-- **Triple Fubini**: averaging a function of three variables over `(α × β) × γ` equals the
iterated average, with the *third* variable outermost.  Stated for an abstract function `f`
so that it can be instantiated without the elaborator ever unfolding the (large) concrete
terms. -/
theorem avg3 {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ] (f : α → β → γ → ℝ) :
    avg (fun p : (α × β) × γ => f p.1.1 p.1.2 p.2)
      = avg (fun c : γ => avg (fun a : α => avg (fun b : β => f a b c))) := by
  have h1 : avg (fun p : (α × β) × γ => f p.1.1 p.1.2 p.2)
      = avg (fun q : γ × (α × β) => f q.2.1 q.2.2 q.1) :=
    avg_equiv' (Equiv.prodComm (α × β) γ) (fun q : γ × (α × β) => f q.2.1 q.2.2 q.1)
  rw [h1]
  exact avg3' f

/-- Averaging a product of two independent functions multiplied by a constant. -/
theorem avg_avg_const_mul {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    [Nonempty α] [Nonempty β] (X : ℝ) (g : α → ℝ) (h : β → ℝ) :
    avg (fun a : α => avg (fun b : β => X * (g a * h b))) = X * avg g * avg h := by
  have h1 : ∀ a : α, avg (fun b : β => X * (g a * h b)) = (X * g a) * avg h := by
    intro a
    rw [show (fun b : β => X * (g a * h b)) = fun b => (X * g a) * h b from
      funext (fun b => by ring), avg_mul_const]
  rw [show (fun a : α => avg (fun b : β => X * (g a * h b))) = fun a => (X * g a) * avg h
    from funext h1]
  rw [show (fun a : α => (X * g a) * avg h) = fun a => avg h * (X * g a) from
    funext (fun a => mul_comm _ _), avg_mul_const]
  rw [avg_mul_const]
  ring

/-- Averaging a product of the same function, squared. -/
theorem avg_avg_const_mul_sq {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] (X : ℝ)
    (g : α → ℝ) :
    avg (fun a : α => avg (fun b : α => X * (g a * g b))) = X * (avg g) ^ 2 := by
  rw [avg_avg_const_mul]
  ring

/-- The Fubini (splitting) identity for averages over a bundle point space. -/
theorem avg_split {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (g : Finset κ)
    (f : BPt V π → ℝ) :
    avg f = avg (fun w : (k : {k // k ∈ g}) → V (π k.val) =>
      avg (fun u : (k : {k // k ∉ g}) → V (π k.val) => f (combine (V := V) π g w u))) := by
  rw [show avg f = avg (fun p : ((k : {k // k ∈ g}) → V (π k.val))
        × ((k : {k // k ∉ g}) → V (π k.val)) =>
      f ((Equiv.piEquivPiSubtypeProd (fun k : κ => k ∈ g) (fun k => V (π k))).symm p))
      from (avg_equiv' (Equiv.piEquivPiSubtypeProd (fun k : κ => k ∈ g)
        (fun k => V (π k))).symm f).symm]
  rw [show (fun p : ((k : {k // k ∈ g}) → V (π k.val))
        × ((k : {k // k ∉ g}) → V (π k.val)) =>
      f ((Equiv.piEquivPiSubtypeProd (fun k : κ => k ∈ g) (fun k => V (π k))).symm p))
      = (fun p => f (combine (V := V) π g p.1 p.2)) from rfl]
  exact avg_prod (g := fun w u => f (combine (V := V) π g w u))

/-- The "lower" set of an edge, over *all* proper subsets. -/
noncomputable def lowSetAll {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι)
    (Ag : Finset κ → Finset (BPt V π)) (g : Finset κ) : Finset (BPt V π) :=
  Finset.univ.filter (fun v => ∀ g' ⊂ g, v ∈ Ag g')

theorem mem_lowSetAll {κ : Type*} [Fintype κ] [DecidableEq κ] {π : κ → ι}
    {Ag : Finset κ → Finset (BPt V π)} {g : Finset κ} {v : BPt V π} :
    v ∈ lowSetAll π Ag g ↔ ∀ g' ⊂ g, v ∈ Ag g' := by
  classical
  simp only [lowSetAll, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The product of the indicators below `g` is the indicator of `lowSetAll`. -/
theorem prod_indicator_lowSetAll {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι)
    (Ag : Finset κ → Finset (BPt V π)) (g : Finset κ) (v : BPt V π) :
    (∏ g' ∈ Finset.univ.filter (fun g' => g' ⊂ g), indicator (Ag g') v)
      = indicator (lowSetAll π Ag g) v := by
  classical
  rw [show (∏ g' ∈ Finset.univ.filter (fun g' => g' ⊂ g), indicator (Ag g') v)
      = ∏ g' ∈ Finset.univ.filter (fun g' => g' ⊂ g),
          (if v ∈ Ag g' then (1 : ℝ) else 0) from rfl]
  rw [Commons.Data.Finset.prod_ite_one_mem]
  rw [show indicator (lowSetAll π Ag g) v
      = (if v ∈ lowSetAll π Ag g then (1 : ℝ) else 0) from rfl]
  by_cases h : v ∈ lowSetAll π Ag g
  · have h' : ∀ g' ∈ Finset.univ.filter (fun g' => g' ⊂ g), v ∈ Ag g' := fun g' hg' =>
      (mem_lowSetAll.mp h) g' (Finset.mem_filter.mp hg').2
    rw [if_pos h, if_pos h']
  · have h' : ¬ ∀ g' ∈ Finset.univ.filter (fun g' => g' ⊂ g), v ∈ Ag g' := fun hh =>
      h (mem_lowSetAll.mpr (fun g' hlt => hh g' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)))
    rw [if_neg h, if_neg h']

/-- The counting expression `Cnt G = avg ∏_{g ∈ G} 1_{A_g}`. -/
noncomputable def Cnt {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι)
    (G : Finset (Finset κ)) (Ag : Finset κ → Finset (BPt V π)) : ℝ :=
  avg (fun v => ∏ g ∈ G, indicator (Ag g) v)

/-- The abstract hypotheses (H1)–(H4) of the generalized counting lemma. -/
structure GCHyp {κ : Type*} [Fintype κ] [DecidableEq κ] (π : κ → ι) (G : Finset (Finset κ))
    (Ag : Finset κ → Finset (BPt V π)) (pg Rg : Finset κ → ℝ)
    (bg cg : Finset κ → BPt V π → ℝ) (ρ : ℝ) : Prop where
  pg_nonneg : ∀ g ∈ G, 0 ≤ pg g
  pg_le_one : ∀ g ∈ G, pg g ≤ 1
  h1 : ∀ g ∈ G, ∀ v ∈ lowSetAll π Ag g,
    indicator (Ag g) v = pg g + bg g v + cg g v
  h2 : ∀ g ∈ G, 1 / Real.log (Rg g) ≤ pg g
  h3 : ∀ g ∈ G, avg (fun v => (bg g v) ^ 2 * indicator (lowSetAll π Ag g) v)
    ≤ (1 / Rg g) * avg (indicator (lowSetAll π Ag g))
  h4 : ∀ g ∈ G, ∀ G' : Finset (Finset κ), g ∈ G' → (∀ g' ∈ G', g'.card ≤ g.card) →
    |avg (fun v => cg g v * ∏ g' ∈ G'.filter (fun g' => g' ≠ g), indicator (Ag g') v)| ≤ ρ

/-- All faces of a hypergraph: the down-closure of `Hd`. -/
noncomputable def Hall {ι : Type*} [DecidableEq ι] (Hd : Finset (Finset ι)) : Finset (Finset ι) :=
  Hd.biUnion (fun e => e.powerset)

theorem mem_Hall {ι : Type*} [DecidableEq ι] {Hd : Finset (Finset ι)} {f : Finset ι} :
    f ∈ Hall Hd ↔ ∃ e ∈ Hd, f ⊆ e := by
  simp only [Hall, Finset.mem_biUnion, Finset.mem_powerset]

theorem Hall_down {ι : Type*} [DecidableEq ι] {Hd : Finset (Finset ι)} {g f : Finset ι}
    (hg : g ∈ Hall Hd) (hf : f ⊆ g) : f ∈ Hall Hd := by
  obtain ⟨e, he, hge⟩ := mem_Hall.mp hg
  exact mem_Hall.mpr ⟨e, he, Subset.trans hf hge⟩

/-- The structural conditions on a hypergraph bundle. -/
structure IsBundle {ι : Type*} [DecidableEq ι] {κ : Type*} [DecidableEq κ]
    (Hd : Finset (Finset ι)) (π : κ → ι) (G : Finset (Finset κ)) : Prop where
  closed : ∀ g ∈ G, ∀ g' ⊆ g, g' ∈ G
  inj : ∀ g ∈ G, ∀ a ∈ g, ∀ b ∈ g, π a = π b → a = b
  img : ∀ g ∈ G, g.image π ∈ Hall Hd

end Szemeredi.Removal
