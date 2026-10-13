import Mathlib
import Submission.Work.WilG4c.BddSupFiniteNoI
import Submission.Work.WilG4c.BadFinsetUniform
import Submission.Work.WilG4c.graphOf_member_mem
import Submission.Work.WilG4c.iterDir_eq_iteratedFDeriv
import Submission.Work.WilG4c.hbdd_sup_finite

namespace Work.WilG4c

theorem hBdd_of_member (S : WilkiesDesign.SOMin) (hder : WilkiesDesign.SOMin.SharpDeriv S)
    (hbdd : Work.WilkG4c.BddDxHyp S) {p n r F D : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (hΩ : WilkiesDesign.CG.famGraph f ∈ S.Ω F D (p + (n + 1) + 1))
    (hY : ∀ l : Fin p → ℝ, ∀ x ∈ Work.WilkG4c.I, ∀ m : ℕ, m ≤ r →
      ∀ y ∈ WilkiesDesign.openCube n,
        ‖iteratedFDeriv ℝ m (Work.WilkG4c.slice (f l) x) y‖ ≤ 1)
    (l : Fin p → ℝ) :
    ∃ B : Finset ℝ, ∀ (L : List (Fin (n + 1))), L.length ≤ r →
      ∀ x ∈ Work.WilkG4c.I, x ∉ (B : Set ℝ) →
        BddAbove ((fun y : Fin n → ℝ =>
            |iteratedFDeriv ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
              (Work.WilkG4c.pt x y) (fun j => Pi.single (L.get j) 1)|) ''
          {y : Fin n → ℝ | y ∈ WilkiesDesign.openCube n ∧
            ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
              (Work.WilkG4c.pt x y)}) := by
  classical
  -- The graph of the member `f l` of the family is `Ω`-definable (uniformly in `l`).
  obtain ⟨K, hK⟩ := graphOf_member_mem S p n
  have hΩ' : WilkiesDesign.graphOf (f l) ∈ S.Ω (F + K) (D + K) (n + 1 + 1) :=
    hK F D f l hΩ
  have hY' : ∀ x ∈ Work.WilkG4c.I, ∀ m, m ≤ r → ∀ y ∈ WilkiesDesign.openCube n,
      ‖iteratedFDeriv ℝ m (Work.WilkG4c.slice (f l) x) y‖ ≤ 1 :=
    fun x hx m hm y hy => hY l x hx m hm y hy
  -- Finiteness of the fibre suprema, for each derivative order.
  have hs := BddSupFiniteNoI S hder hbdd (g := f l) hΩ' hY'
  -- A single exceptional finite set works for all orders simultaneously.
  obtain ⟨B, hB⟩ := BadFinsetUniform (f l) hs
  refine ⟨B, fun L hL x hx hxB => ?_⟩
  have hb := hB L hL x hx hxB
  -- On the `C^{|L|}`-locus, `iterDir` and the evaluated `iteratedFDeriv` agree, and that
  -- locus is the interior of itself.
  have himg : (Set.image (fun y : Fin n → ℝ =>
        |iteratedFDeriv ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
          (Work.WilkG4c.pt x y) (fun j => Pi.single (L.get j) 1)|)
      {y : Fin n → ℝ | y ∈ WilkiesDesign.openCube n ∧
        ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u) (Work.WilkG4c.pt x y)})
    = Set.image (fun y : Fin n → ℝ =>
        |Work.WilkG4c.iterDir L (fun u : Fin (n + 1) → ℝ => f l u) (Work.WilkG4c.pt x y)|)
      {y : Fin n → ℝ | y ∈ WilkiesDesign.openCube n ∧
        Work.WilkG4c.pt x y ∈ interior {z | ContDiffAt ℝ L.length
          (fun u : Fin (n + 1) → ℝ => f l u) z}} := by
    have hset : {y : Fin n → ℝ | y ∈ WilkiesDesign.openCube n ∧
          ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u) (Work.WilkG4c.pt x y)}
        = {y : Fin n → ℝ | y ∈ WilkiesDesign.openCube n ∧
          Work.WilkG4c.pt x y ∈ interior {z | ContDiffAt ℝ L.length
            (fun u : Fin (n + 1) → ℝ => f l u) z}} := by
      ext y
      simp only [Set.mem_setOf_eq]
      rw [hbdd_mem_interior_locus_nat L.length (fun u : Fin (n + 1) → ℝ => f l u)
        (Work.WilkG4c.pt x y)]
    rw [hset]
    exact Set.image_congr (fun y hy => by
      have hycd : ContDiffAt ℝ L.length (fun u : Fin (n + 1) → ℝ => f l u)
          (Work.WilkG4c.pt x y) :=
        (hbdd_mem_interior_locus_nat L.length (fun u : Fin (n + 1) → ℝ => f l u)
          (Work.WilkG4c.pt x y)).mp hy.2
      rw [iterDir_eq_iteratedFDeriv L (fun u : Fin (n + 1) → ℝ => f l u)
        (Work.WilkG4c.pt x y) hycd])
  rw [himg]
  exact hb

end Work.WilG4c
