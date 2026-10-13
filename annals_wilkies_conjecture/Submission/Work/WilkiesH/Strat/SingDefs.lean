import Mathlib
import Submission.Work.WilkiesH.Mfd.Defs
import Submission.Work.WilkiesH.Strat.root_index_semialgebraic
import Submission.Work.WilkiesH.Strat.root_count_semialgebraic
import Submission.Work.WilkiesH.Strat.squarefree_excision_v2
import Submission.Work.WilkiesH.Tarski.FiberDefs

/-! Auxiliary vocabulary for `Work.WilkiesH.Strat.semialg_singular_dimLE` -/

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkiesH.Strat

open WilkiesDesign WilkiesConjecture
open Work.WilkiesH
open scoped Topology

/-! ## 5b. The embedding extending a chart by one extra coordinate -/

/-- The embedding `Fin (μ+1) ↪ Fin n` extending `h : Fin μ ↪ Fin n` by the extra coordinate
`j ∉ Set.range h` (which occupies the last slot). -/
def extEmb {n μ : ℕ} (h : Fin μ ↪ Fin n) (j : Fin n) (hj : j ∉ Set.range h) :
    Fin (μ + 1) ↪ Fin n where
  toFun i := Fin.lastCases j (fun k : Fin μ => h k) i
  inj' := by
    intro a b hab
    change Fin.lastCases (motive := fun _ : Fin (μ + 1) => Fin n) j (fun k : Fin μ => h k) a
      = Fin.lastCases (motive := fun _ : Fin (μ + 1) => Fin n) j (fun k : Fin μ => h k) b at hab
    rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl <;>
      rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
    · rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc] at hab
      exact congrArg Fin.castSucc (h.injective hab)
    · rw [Fin.lastCases_castSucc, Fin.lastCases_last] at hab
      exact absurd ⟨a', hab⟩ hj
    · rw [Fin.lastCases_last, Fin.lastCases_castSucc] at hab
      exact absurd ⟨b', hab.symm⟩ hj
    · rfl

@[simp] theorem extEmb_castSucc {n μ : ℕ} (h : Fin μ ↪ Fin n) {j : Fin n}
    (hj : j ∉ Set.range h) (i : Fin μ) : extEmb h j hj i.castSucc = h i := by
  show Fin.lastCases j (fun k : Fin μ => h k) i.castSucc = h i
  rw [Fin.lastCases_castSucc]

@[simp] theorem extEmb_last {n μ : ℕ} (h : Fin μ ↪ Fin n) {j : Fin n}
    (hj : j ∉ Set.range h) : extEmb h j hj (Fin.last μ) = j := by
  show Fin.lastCases j (fun k : Fin μ => h k) (Fin.last μ) = j
  rw [Fin.lastCases_last]

theorem eval_extEmb {n μ : ℕ} (h : Fin μ ↪ Fin n) {j : Fin n} (hj : j ∉ Set.range h)
    (x : Fin n → ℝ) :
    (fun i : Fin (μ + 1) => x (extEmb h j hj i)) = Fin.snoc (x ∘ h) (x j) := by
  funext i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl <;> simp

/-! ## 5c. The fibre family of a polynomial in the `Fin.snoc` coordinates -/

/-- `preFiber G` is the family `u ↦ G(u,·)`, viewed as a polynomial in the last variable with
coefficients in `ℝ[x_1,…,x_μ]`. -/
def preFiber {μ : ℕ} (G : MvPolynomial (Fin (μ + 1)) ℝ) : Polynomial (MvPolynomial (Fin μ) ℝ) :=
  (MvPolynomial.optionEquivLeft ℝ (Fin μ)) (MvPolynomial.rename (Work.WilkiesH.Tarski.lastOption (n := μ)) G)

theorem fiberPoly_eq_map {μ : ℕ} (G : MvPolynomial (Fin (μ + 1)) ℝ) (u : Fin μ → ℝ) :
    Work.WilkiesH.Tarski.fiberPoly G u = (preFiber G).map (MvPolynomial.eval u) := rfl

theorem natDegree_fiberPoly_le {μ : ℕ} (G : MvPolynomial (Fin (μ + 1)) ℝ) (u : Fin μ → ℝ) :
    (Work.WilkiesH.Tarski.fiberPoly G u).natDegree ≤ (preFiber G).natDegree :=
  Polynomial.natDegree_map_le

/-- Some `u` at which a nonzero polynomial in `Fin μ` does not vanish. -/
theorem exists_eval_ne_zero {μ : ℕ} {P : MvPolynomial (Fin μ) ℝ} (hP : P ≠ 0) :
    ∃ u : Fin μ → ℝ, MvPolynomial.eval u P ≠ 0 := by
  by_contra h
  push_neg at h
  exact hP (MvPolynomial.funext (fun u => by simp [h u]))

/-! ## 5d. Squarefree excision in the `Fin.snoc` coordinates -/

/-- `Work.WilkiesH.Strat.squarefree_excision_v2`, transported to the `Fin.snoc` form in which the
fibre/IFT lemmas of `Work.WilkiesH.Tarski` are stated. -/
theorem squarefree_excision_snoc {μ : ℕ} (Q : MvPolynomial (Fin (μ + 1)) ℝ) (hQ : Q ≠ 0) :
    ∃ (G : MvPolynomial (Fin (μ + 1)) ℝ) (l : MvPolynomial (Fin μ) ℝ), l ≠ 0 ∧
      ∀ u : Fin μ → ℝ, MvPolynomial.eval u l ≠ 0 →
        (∀ t : ℝ, MvPolynomial.eval (Fin.snoc u t) G = 0 ↔
          MvPolynomial.eval (Fin.snoc u t) Q = 0) ∧
        (∀ t : ℝ, MvPolynomial.eval (Fin.snoc u t) G = 0 →
          MvPolynomial.eval (Fin.snoc u t) (MvPolynomial.pderiv (Fin.last μ) G) ≠ 0) := by
  classical
  have keyfun : ∀ (u : Fin μ → ℝ) (t : ℝ),
      (Sum.elim u (fun _ : Fin 1 => t)) ∘ (⇑(finSumFinEquiv : Fin μ ⊕ Fin 1 ≃ Fin (μ + 1)).symm)
        = Fin.snoc u t := by
    intro u t
    funext i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨k, rfl⟩ | rfl
    · rw [Function.comp_apply, Fin.snoc_castSucc]
      have h1 : (finSumFinEquiv : Fin μ ⊕ Fin 1 ≃ Fin (μ + 1)).symm k.castSucc = Sum.inl k := by
        rw [Equiv.symm_apply_eq]
        exact Fin.ext rfl
      rw [h1]
      rfl
    · rw [Function.comp_apply, Fin.snoc_last]
      have h1 : (finSumFinEquiv : Fin μ ⊕ Fin 1 ≃ Fin (μ + 1)).symm (Fin.last μ) = Sum.inr 0 := by
        rw [Equiv.symm_apply_eq]
        simp only [finSumFinEquiv_apply_right]
        exact Fin.ext (by simp)
      rw [h1]
      rfl
  have key : ∀ (u : Fin μ → ℝ) (t : ℝ),
      MvPolynomial.eval (Sum.elim u (fun _ : Fin 1 => t))
          (MvPolynomial.rename (⇑(finSumFinEquiv : Fin μ ⊕ Fin 1 ≃ Fin (μ + 1)).symm) Q)
        = MvPolynomial.eval (Fin.snoc u t) Q := by
    intro u t
    rw [MvPolynomial.eval_rename, keyfun u t]
  have key2fun : ∀ (u : Fin μ → ℝ) (t : ℝ),
      (Fin.snoc u t) ∘ (⇑(finSumFinEquiv : Fin μ ⊕ Fin 1 ≃ Fin (μ + 1)))
        = Sum.elim u (fun _ : Fin 1 => t) := by
    intro u t
    funext o
    rcases o with i | i
    · rw [Function.comp_apply]
      simp only [Sum.elim_inl]
      rw [finSumFinEquiv_apply_left, show Fin.castAdd 1 i = i.castSucc from rfl, Fin.snoc_castSucc]
    · rw [Function.comp_apply]
      simp only [Sum.elim_inr]
      have hi : i = 0 := Subsingleton.elim i 0
      subst hi
      have h2 : (finSumFinEquiv : Fin μ ⊕ Fin 1 ≃ Fin (μ + 1)) (Sum.inr 0) = Fin.last μ := by
        rw [finSumFinEquiv_apply_right]
        exact Fin.ext (by simp)
      rw [h2, Fin.snoc_last]
  have key2 : ∀ (u : Fin μ → ℝ) (t : ℝ) (G' : MvPolynomial (Fin μ ⊕ Fin 1) ℝ),
      MvPolynomial.eval (Fin.snoc u t)
          (MvPolynomial.rename (⇑(finSumFinEquiv : Fin μ ⊕ Fin 1 ≃ Fin (μ + 1))) G')
        = MvPolynomial.eval (Sum.elim u (fun _ : Fin 1 => t)) G' := by
    intro u t G'
    rw [MvPolynomial.eval_rename, key2fun u t]
  have hQ' : MvPolynomial.rename (⇑(finSumFinEquiv : Fin μ ⊕ Fin 1 ≃ Fin (μ + 1)).symm) Q ≠ 0 := by
    intro h
    exact hQ (MvPolynomial.rename_injective _ (Equiv.injective _) (by rw [h, map_zero]))
  obtain ⟨G', l, hl, H⟩ := squarefree_excision_v2 _ hQ'
  refine ⟨MvPolynomial.rename (⇑(finSumFinEquiv : Fin μ ⊕ Fin 1 ≃ Fin (μ + 1))) G', l, hl, ?_⟩
  intro u hu
  obtain ⟨h1, h2⟩ := H u hu
  constructor
  · intro t
    rw [key2 u t G', ← key u t]
    exact h1 t
  · intro t ht
    rw [key2 u t G'] at ht
    have hp : MvPolynomial.pderiv (Fin.last μ)
        (MvPolynomial.rename (⇑(finSumFinEquiv : Fin μ ⊕ Fin 1 ≃ Fin (μ + 1))) G')
        = MvPolynomial.rename (⇑(finSumFinEquiv : Fin μ ⊕ Fin 1 ≃ Fin (μ + 1)))
            (MvPolynomial.pderiv (Sum.inr 0) G') := by
      have hlast : (finSumFinEquiv : Fin μ ⊕ Fin 1 ≃ Fin (μ + 1)) (Sum.inr 0) = Fin.last μ := by
        rw [finSumFinEquiv_apply_right]
        ext
        simp
      rw [← hlast]
      exact MvPolynomial.pderiv_rename (Equiv.injective _) (Sum.inr 0) G'
    rw [hp, key2 u t (MvPolynomial.pderiv (Sum.inr 0) G')]
    exact h2 t ht

/-! ## 5e. The pattern pieces -/

/-- `Sel G k`: `z` is a root of `G` and exactly `k` real roots of the fibre `G (Fin.init z) ·`
lie strictly below the last coordinate of `z` (so that last coordinate is the `(k+1)`-st smallest
real root of the fibre). -/
def Sel {μ : ℕ} (G : MvPolynomial (Fin (μ + 1)) ℝ) (k : ℕ) : Set (Fin (μ + 1) → ℝ) :=
  {z | MvPolynomial.eval z G = 0 ∧
    ∃ t : Fin k → ℝ, StrictMono t ∧
      (∀ i, t i < z (Fin.last μ) ∧ MvPolynomial.eval (Fin.snoc (Fin.init z) (t i)) G = 0) ∧
      (∀ s : ℝ, s < z (Fin.last μ) → MvPolynomial.eval (Fin.snoc (Fin.init z) s) G = 0 →
        ∃ i, s = t i)}

/-- Membership in `Sel`, with the definition unfolded (cheap to rewrite with). -/
theorem mem_sel_iff {μ : ℕ} (G : MvPolynomial (Fin (μ + 1)) ℝ) (k : ℕ)
    (z : Fin (μ + 1) → ℝ) :
    z ∈ Sel G k ↔ MvPolynomial.eval z G = 0 ∧
      ∃ t : Fin k → ℝ, StrictMono t ∧
        (∀ i, t i < z (Fin.last μ) ∧ MvPolynomial.eval (Fin.snoc (Fin.init z) (t i)) G = 0) ∧
        (∀ s : ℝ, s < z (Fin.last μ) → MvPolynomial.eval (Fin.snoc (Fin.init z) s) G = 0 →
          ∃ i, s = t i) := Iff.rfl

theorem sel_isSemialgebraic {μ : ℕ} (G : MvPolynomial (Fin (μ + 1)) ℝ) (k : ℕ) :
    WilkiesConjecture.IsSemialgebraic (Sel G k) :=
  root_index_semialgebraic G

/-- `CntSet G m`: the fibre `G u ·` has exactly `m` real roots. -/
def CntSet {μ : ℕ} (G : MvPolynomial (Fin (μ + 1)) ℝ) (m : ℕ) : Set (Fin μ → ℝ) :=
  {u | ∃ t : Fin m → ℝ, StrictMono t ∧
    (∀ i, MvPolynomial.eval (Fin.snoc u (t i)) G = 0) ∧
    (∀ s : ℝ, MvPolynomial.eval (Fin.snoc u s) G = 0 → ∃ i, s = t i)}

theorem cntSet_isSemialgebraic {μ : ℕ} (G : MvPolynomial (Fin (μ + 1)) ℝ) (m : ℕ) :
    WilkiesConjecture.IsSemialgebraic (CntSet G m) :=
  root_count_semialgebraic G m

/-- Membership in `CntSet`, with the definition unfolded (cheap to rewrite with). -/
theorem mem_cntSet_iff {μ : ℕ} (G : MvPolynomial (Fin (μ + 1)) ℝ) (m : ℕ)
    (u : Fin μ → ℝ) :
    u ∈ CntSet G m ↔ ∃ t : Fin m → ℝ, StrictMono t ∧
      (∀ i, MvPolynomial.eval (Fin.snoc u (t i)) G = 0) ∧
      (∀ s : ℝ, MvPolynomial.eval (Fin.snoc u s) G = 0 → ∃ i, s = t i) := Iff.rfl

/-- The `(k,m)`-piece of `G`: points at which the last coordinate is the `(k+1)`-st smallest
real root of the fibre and that fibre has exactly `m` real roots. -/
def piece {μ : ℕ} (G : MvPolynomial (Fin (μ + 1)) ℝ) (k m : ℕ) : Set (Fin (μ + 1) → ℝ) :=
  Sel G k ∩ ((fun z : Fin (μ + 1) → ℝ => z ∘ Fin.castSucc) ⁻¹' CntSet G m)

/-- Membership in `piece`, with the definition unfolded (cheap to rewrite with). -/
theorem mem_piece_iff {μ : ℕ} (G : MvPolynomial (Fin (μ + 1)) ℝ) (k m : ℕ)
    (z : Fin (μ + 1) → ℝ) :
    z ∈ piece G k m ↔ z ∈ Sel G k ∧ z ∘ Fin.castSucc ∈ CntSet G m := Iff.rfl

/-- `Sel` for a point of the form `Fin.snoc u t`. -/
theorem mem_sel_snoc_iff {μ : ℕ} (G : MvPolynomial (Fin (μ + 1)) ℝ) (k : ℕ)
    (u : Fin μ → ℝ) (t : ℝ) :
    Fin.snoc u t ∈ Sel G k ↔ MvPolynomial.eval (Fin.snoc u t) G = 0 ∧
      ∃ t' : Fin k → ℝ, StrictMono t' ∧
        (∀ i, t' i < t ∧ MvPolynomial.eval (Fin.snoc u (t' i)) G = 0) ∧
        (∀ s : ℝ, s < t → MvPolynomial.eval (Fin.snoc u s) G = 0 → ∃ i, s = t' i) := by
  rw [mem_sel_iff]
  simp only [Fin.init_snoc, Fin.snoc_last]

/-- `piece` for a point of the form `Fin.snoc u t`. -/
theorem mem_piece_snoc_iff {μ : ℕ} (G : MvPolynomial (Fin (μ + 1)) ℝ) (k m : ℕ)
    (u : Fin μ → ℝ) (t : ℝ) :
    Fin.snoc u t ∈ piece G k m ↔ Fin.snoc u t ∈ Sel G k ∧ u ∈ CntSet G m := by
  rw [mem_piece_iff]
  have hcomp : (Fin.snoc u t) ∘ (Fin.castSucc : Fin μ → Fin (μ + 1)) = u := by
    funext i
    rw [Function.comp_apply, Fin.snoc_castSucc]
  rw [hcomp]

theorem piece_isSemialgebraic {μ : ℕ} (G : MvPolynomial (Fin (μ + 1)) ℝ) (k m : ℕ) :
    WilkiesConjecture.IsSemialgebraic (piece G k m) :=
  (sel_isSemialgebraic G k).inter
    ((cntSet_isSemialgebraic G m).preimage_comp (f := Fin.castSucc (n := μ)))


end Work.WilkiesH.Strat
