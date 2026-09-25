import Mathlib
import Submission.Work.LT.Defs

/-! Auxiliary definitions and interface lemmas for `lr_sound` (DELLM Theorem 4.5).

This file is `sorry`-free and is imported both by `lr_sound` and by the auxiliary lemmas
delegated for it.  Nothing here changes `Defs.lean`. -/

namespace Work.LT

open Classical

variable {G : Type} [Group G] {Δ : ℕ}

/-- The set of *rejecting* vertices: those whose local view of `f` is not a tensor codeword. -/
noncomputable def rejectSet [Fintype G] (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) (f : G × Fin Δ × Fin Δ → ZMod 2) :
    Finset (Fin 2 × Fin 2 × G) :=
  Finset.univ.filter (fun v : Fin 2 × Fin 2 × G =>
    lrView A B v.1 v.2.1 v.2.2 f ∉ tensorCode CA CB)

/-- The initial assignment `W₀`: at every vertex it is the true local view if that view is a
tensor codeword, and `0` otherwise. -/
noncomputable def lrW0 (A B : Fin Δ → G) (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2))
    (f : G × Fin Δ × Fin Δ → ZMod 2) : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2) :=
  fun α β g => if lrView A B α β g f ∈ tensorCode CA CB then lrView A B α β g f else 0

/-- The set of vertices where two assignments differ. -/
noncomputable def changedSet [Fintype G]
    (W W0 : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) : Finset (Fin 2 × Fin 2 × G) :=
  Finset.univ.filter (fun v : Fin 2 × Fin 2 × G => W v.1 v.2.1 v.2.2 ≠ W0 v.1 v.2.1 v.2.2)

/-- The word read off an assignment `W` at the type-`(0,0)` vertices. -/
def lrState (W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)) :
    G × Fin Δ × Fin Δ → ZMod 2 :=
  fun p => W 0 0 p.1 (p.2.1, p.2.2)

/-- The `G`-coordinate of the square seen from the vertex `(α,β,g)` at coordinates `(i,j)`. -/
def lrBase (A B : Fin Δ → G) (α β : Fin 2) (g : G) (i j : Fin Δ) : G :=
  (if α = 1 then (A i)⁻¹ else 1) * g * (if β = 1 then (B j)⁻¹ else 1)

/-- The `A`-part of `lrBase`: `(Ai)⁻¹` in the type-`1` layer, `1` in the type-`0` layer. -/
def lrG1 (A : Fin Δ → G) (α : Fin 2) (i : Fin Δ) : G :=
  if α = 1 then (A i)⁻¹ else 1

/-- The `B`-part of `lrBase`. -/
def lrG2 (B : Fin Δ → G) (β : Fin 2) (j : Fin Δ) : G :=
  if β = 1 then (B j)⁻¹ else 1

lemma lrBase_eq (A B : Fin Δ → G) (α β : Fin 2) (g : G) (i j : Fin Δ) :
    lrBase A B α β g i j = lrG1 A α i * g * lrG2 B β j := rfl

lemma lrSq_eq_base (A B : Fin Δ → G) (α β : Fin 2) (g : G) (i j : Fin Δ) :
    lrSq A B α β g i j = (lrBase A B α β g i j, i, j) := rfl

lemma lrBase_zero_zero (A B : Fin Δ → G) (g : G) (i j : Fin Δ) :
    lrBase A B 0 0 g i j = g := by
  simp [lrBase]

/-- The two endpoints of an `A`-edge agree on the row of its label. -/
lemma lrView_row (A B : Fin Δ → G) (β : Fin 2) (g : G) (i j : Fin Δ)
    (f : G × Fin Δ × Fin Δ → ZMod 2) :
    lrView A B 0 β g f (i, j) = lrView A B 1 β (A i * g) f (i, j) := by
  simp only [lrView, LinearMap.funLeft_apply, lrSq_eq_base]
  congr 1
  simp [lrBase]

/-- The two endpoints of a `B`-edge agree on the column of its label. -/
lemma lrView_col (A B : Fin Δ → G) (α : Fin 2) (g : G) (i j : Fin Δ)
    (f : G × Fin Δ × Fin Δ → ZMod 2) :
    lrView A B α 0 g f (i, j) = lrView A B α 1 (g * B j) f (i, j) := by
  simp only [lrView, LinearMap.funLeft_apply, lrSq_eq_base]
  congr 1
  rw [lrBase, lrBase]
  by_cases hα : α = 1 <;> simp [hα, mul_assoc]

lemma lrW0_mem (A B : Fin Δ → G) (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2))
    (f : G × Fin Δ × Fin Δ → ZMod 2) (α β : Fin 2) (g : G) :
    lrW0 A B CA CB f α β g ∈ tensorCode CA CB := by
  unfold lrW0
  split_ifs with h
  · exact h
  · exact zero_mem _

lemma lrW0_eq_view (A B : Fin Δ → G) (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2))
    (f : G × Fin Δ × Fin Δ → ZMod 2) (α β : Fin 2) (g : G)
    (h : lrView A B α β g f ∈ tensorCode CA CB) :
    lrW0 A B CA CB f α β g = lrView A B α β g f := by
  simp [lrW0, h]

/-- At a non-rejecting vertex the initial assignment is the true local view. -/
lemma lrW0_eq_view_of_not_mem_rejectSet [Fintype G] (A B : Fin Δ → G)
    (CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)) (f : G × Fin Δ × Fin Δ → ZMod 2)
    (v : Fin 2 × Fin 2 × G) (h : v ∉ rejectSet A B CA CB f) :
    lrW0 A B CA CB f v.1 v.2.1 v.2.2 = lrView A B v.1 v.2.1 v.2.2 f := by
  refine lrW0_eq_view A B CA CB f v.1 v.2.1 v.2.2 ?_
  by_contra hc
  exact h (by simp [rejectSet, hc])

/-- Nothing is disputed at all when the dispute count vanishes. -/
lemma not_disputeA_of_dispCount_eq_zero [Fintype G] {A B : Fin Δ → G}
    {W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)} (h : dispCount A B W = 0)
    (β : Fin 2) (g : G) (i : Fin Δ) : ¬ disputeA A W β g i := by
  have h1 : (Finset.univ.filter
      (fun p : Fin 2 × G × Fin Δ => disputeA A W p.1 p.2.1 p.2.2)).card = 0 := by
    have := h
    unfold dispCount at this
    omega
  have h2 : (Finset.univ.filter
      (fun p : Fin 2 × G × Fin Δ => disputeA A W p.1 p.2.1 p.2.2)) = ∅ :=
    Finset.card_eq_zero.mp h1
  intro hd
  have hmem : (β, g, i) ∈ (Finset.univ.filter
      (fun p : Fin 2 × G × Fin Δ => disputeA A W p.1 p.2.1 p.2.2)) := by
    simp [hd]
  rw [h2] at hmem
  simpa using hmem

lemma not_disputeB_of_dispCount_eq_zero [Fintype G] {A B : Fin Δ → G}
    {W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)} (h : dispCount A B W = 0)
    (α : Fin 2) (g : G) (j : Fin Δ) : ¬ disputeB B W α g j := by
  have h1 : (Finset.univ.filter
      (fun p : Fin 2 × G × Fin Δ => disputeB B W p.1 p.2.1 p.2.2)).card = 0 := by
    have := h
    unfold dispCount at this
    omega
  have h2 : (Finset.univ.filter
      (fun p : Fin 2 × G × Fin Δ => disputeB B W p.1 p.2.1 p.2.2)) = ∅ :=
    Finset.card_eq_zero.mp h1
  intro hd
  have hmem : (α, g, j) ∈ (Finset.univ.filter
      (fun p : Fin 2 × G × Fin Δ => disputeB B W p.1 p.2.1 p.2.2)) := by
    simp [hd]
  rw [h2] at hmem
  simpa using hmem

/-- With no disputes, the view at `(1,β,g)` agrees with the view at `(0,β,(Ai)⁻¹g)` on row `i`. -/
lemma lrW_row_eq [Fintype G] {A B : Fin Δ → G}
    {W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)}
    (h : dispCount A B W = 0) (β : Fin 2) (g : G) (i j : Fin Δ) :
    W 1 β g (i, j) = W 0 β ((A i)⁻¹ * g) (i, j) := by
  have hd := not_disputeA_of_dispCount_eq_zero (A := A) h β ((A i)⁻¹ * g) i
  simp only [disputeA, not_exists, not_not] at hd
  have := hd j
  simpa using this.symm

/-- With no disputes, the view at `(α,1,g)` agrees with the view at `(α,0,g(Bj)⁻¹)` on column `j`. -/
lemma lrW_col_eq [Fintype G] {A B : Fin Δ → G}
    {W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)}
    (h : dispCount A B W = 0) (α : Fin 2) (g : G) (i j : Fin Δ) :
    W α 1 g (i, j) = W α 0 (g * (B j)⁻¹) (i, j) := by
  have hd := not_disputeB_of_dispCount_eq_zero (B := B) h α (g * (B j)⁻¹) j
  simp only [disputeB, not_exists, not_not] at hd
  have := hd i
  simpa using this.symm

/-- With no disputes, moving from the type-`(α,β)` layer to the type-`(0,β)` layer along the
`A`-edge of label `i`. -/
lemma lrW_row_eq_base [Fintype G] {A B : Fin Δ → G}
    {W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)}
    (h : dispCount A B W = 0) (α β : Fin 2) (g : G) (i j : Fin Δ) :
    W α β g (i, j) = W 0 β (lrG1 A α i * g) (i, j) := by
  by_cases hα : α = 1
  · subst hα
    simpa [lrG1] using lrW_row_eq (B := B) h β g i j
  · have hα0 : α = 0 := by fin_cases α <;> simp_all
    subst hα0
    simp [lrG1]

/-- With no disputes, moving from the type-`(0,β)` layer to the type-`(0,0)` layer along the
`B`-edge of label `j`. -/
lemma lrW_col_eq_base [Fintype G] {A B : Fin Δ → G}
    {W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)}
    (h : dispCount A B W = 0) (β : Fin 2) (g : G) (i j : Fin Δ) :
    W 0 β g (i, j) = W 0 0 (g * lrG2 B β j) (i, j) := by
  by_cases hβ : β = 1
  · subst hβ
    simpa [lrG2] using lrW_col_eq (A := A) h 0 g i j
  · have hβ0 : β = 0 := by fin_cases β <;> simp_all
    subst hβ0
    simp [lrG2]

/-- Chain of agreements: with no disputes the whole assignment is determined by its type-`(0,0)`
entries. -/
lemma lrW_eq_base [Fintype G] {A B : Fin Δ → G}
    {W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)}
    (h : dispCount A B W = 0) (α β : Fin 2) (g : G) (i j : Fin Δ) :
    W α β g (i, j) = W 0 0 (lrBase A B α β g i j) (i, j) := by
  rw [lrW_row_eq_base h α β g i j, lrW_col_eq_base h β (lrG1 A α i * g) i j,
    lrBase_eq, lrG1, lrG2]

/-- In the no-dispute case the word read off the assignment is a codeword. -/
lemma lrState_mem_lrCode [Fintype G] {A B : Fin Δ → G}
    {CA CB : Submodule (ZMod 2) (Fin Δ → ZMod 2)}
    {W : Fin 2 → Fin 2 → G → (Fin Δ × Fin Δ → ZMod 2)}
    (hW : ∀ α β g, W α β g ∈ tensorCode CA CB) (h : dispCount A B W = 0) :
    lrState W ∈ lrCode A B CA CB := by
  rw [lrCode, Submodule.mem_iInf]
  intro α
  rw [Submodule.mem_iInf]
  intro β
  rw [Submodule.mem_iInf]
  intro g
  rw [Submodule.mem_comap]
  have hview : lrView A B α β g (lrState W) = W α β g := by
    funext ij
    obtain ⟨i, j⟩ := ij
    simp only [lrView, LinearMap.funLeft_apply, lrSq_eq_base, lrState]
    exact (lrW_eq_base h α β g i j).symm
  rw [hview]
  exact hW α β g

end Work.LT
