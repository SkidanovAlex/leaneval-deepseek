import Mathlib
import Submission.Work.Subdivision.Level

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.Subdivision

universe u

namespace PolyCW

variable (P : PolyCW.{u})

/- Helper namespace for the proof of `sdTopMod_inf_leSub`: the refinement
`sdTopMod P n E` is a coordinate submodule, spanned by the simplices whose
vertices are all of dimension `≤ n` or whose top vertex lies in `E` and has
dimension `n + 1`. -/
namespace SdTopModInf

/-- The predicate describing the basis simplices of the refined filtration
`sdTopMod P n E`: a simplex either has all vertices of dimension `≤ n`, or its
top vertex is a cell of `E` of dimension `n + 1`. -/
def pred (n : ℕ) (E : Finset P.Cell) (k : ℕ) (σ : Simplex P.Cell k) : Prop :=
  (∀ i, P.dim (σ i) ≤ n) ∨ (σ (Fin.last k) ∈ E ∧ P.dim (σ (Fin.last k)) = n + 1)

/-- `sdTopMod P n E k` is the coordinate submodule spanned by the simplices
satisfying `pred`. -/
theorem eq_span (n : ℕ) (E : Finset P.Cell) (k : ℕ) :
    sdTopMod P n E k =
      Submodule.span ℤ {y : (sdChain P).X k |
        ∃ σ : Simplex P.Cell k, pred P n E k σ ∧ y = sdElem P σ} := by
  rw [sdTopMod]
  refine le_antisymm (sup_le ?_ ?_) ?_
  · rw [sdSubMod, Submodule.span_le]
    rintro y ⟨σ, hσ, rfl⟩
    exact Submodule.subset_span ⟨σ, Or.inl hσ, rfl⟩
  · rw [Submodule.span_le]
    rintro y ⟨σ, hσ, hB, rfl⟩
    exact Submodule.subset_span ⟨σ, Or.inr ⟨hσ, hB⟩, rfl⟩
  · rw [Submodule.span_le]
    rintro y ⟨σ, hσ, rfl⟩
    rcases hσ with h1 | ⟨hA, hB⟩
    · exact Submodule.mem_sup_left (sdElem_mem_sdSubMod P h1)
    · exact Submodule.mem_sup_right (Submodule.subset_span ⟨σ, hA, hB, rfl⟩)

/-- Membership in `sdTopMod` is detected on the support of the `Finsupp`. -/
theorem support {n : ℕ} {E : Finset P.Cell} {k : ℕ} {x : (sdChain P).X k}
    (hx : x ∈ sdTopMod P n E k) : ∀ σ ∈ x.support, pred P n E k σ := by
  have hset : {y : (sdChain P).X k |
        ∃ σ : Simplex P.Cell k, pred P n E k σ ∧ y = sdElem P σ}
      = {y : (sdChain P).X k |
          ∃ b ∈ {σ : Simplex P.Cell k | pred P n E k σ}, y = Finsupp.single b 1} := by
    ext y
    constructor <;> rintro ⟨σ, hσ, rfl⟩ <;> exact ⟨σ, hσ, by simp [sdElem]⟩
  rw [eq_span P n E k, hset] at hx
  exact fun σ hσ =>
    (Finsupp.mem_span_single_one_iff (R := ℤ)
      (B := {σ : Simplex P.Cell k | pred P n E k σ})).1 hx hσ

/-- Converse of `support`: a chain supported on simplices satisfying `pred` lies
in `sdTopMod`. -/
theorem mem_of_support (n : ℕ) (E : Finset P.Cell) {k : ℕ} {x : (sdChain P).X k}
    (h : ∀ σ ∈ x.support, pred P n E k σ) : x ∈ sdTopMod P n E k := by
  have hset : {y : (sdChain P).X k |
        ∃ σ : Simplex P.Cell k, pred P n E k σ ∧ y = sdElem P σ}
      = {y : (sdChain P).X k |
          ∃ b ∈ {σ : Simplex P.Cell k | pred P n E k σ}, y = Finsupp.single b 1} := by
    ext y
    constructor <;> rintro ⟨σ, hσ, rfl⟩ <;> exact ⟨σ, hσ, by simp [sdElem]⟩
  rw [eq_span P n E k, hset]
  exact (Finsupp.mem_span_single_one_iff (R := ℤ)
    (B := {σ : Simplex P.Cell k | pred P n E k σ})).2 fun σ hσ => h σ hσ

/-- The chains with all vertices `< a`, where `P.dim a = n + 1`, lie in the
refined filtration `sdTopMod P n E`: their vertices have dimension `≤ n`. -/
theorem ltSub_le (n : ℕ) (E : Finset P.Cell) {a : P.Cell}
    (ha : P.dim a = n + 1) (k : ℕ) : ltSub P a k ≤ sdTopMod P n E k := by
  intro x hx
  refine mem_of_support P n E fun σ hσ => Or.inl fun i => ?_
  have hlt : σ i < a := ltSub_support P hx σ hσ i
  have := P.dim_lt hlt.le (ne_of_lt hlt)
  omega

end SdTopModInf

end PolyCW

theorem sdTopMod_inf_leSub (P : Work.Subdivision.PolyCW) (n : ℕ) (E : Finset P.Cell) {a : P.Cell}
    (ha : P.dim a = n + 1) (hE : a ∉ E) (k : ℕ) :
    Work.Subdivision.PolyCW.sdTopMod P n E k ⊓ Work.Subdivision.PolyCW.leSub P a k =
      Work.Subdivision.PolyCW.ltSub P a k := by
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxT, hxL⟩ := Submodule.mem_inf.mp hx
    refine PolyCW.mem_ltSub_of_support P fun σ hσ i => ?_
    have hpred := PolyCW.SdTopModInf.support P hxT σ hσ
    have hle : σ i ≤ a := PolyCW.leSub_support P hxL σ hσ i
    rcases hpred with h1 | h2
    · refine lt_of_le_of_ne hle fun heq => ?_
      have hlt : P.dim (σ i) < P.dim a := by
        have := h1 i; omega
      rw [heq] at hlt
      exact lt_irrefl _ hlt
    · have hlast_le : σ (Fin.last k) ≤ a := PolyCW.leSub_support P hxL σ hσ (Fin.last k)
      have heq : σ (Fin.last k) = a := by
        by_contra hne
        have hlt := P.dim_lt hlast_le hne
        have hd : P.dim (σ (Fin.last k)) = P.dim a := by rw [h2.2, ha]
        omega
      exact absurd (heq ▸ h2.1) hE
  · intro x hx
    exact Submodule.mem_inf.mpr
      ⟨PolyCW.SdTopModInf.ltSub_le P n E ha k hx, PolyCW.ltSub_le_leSub P a k hx⟩

end Work.Subdivision
