/-
  WilG4a : the pullback ("substitution of a variable by a function") atom of the `Ω`-calculus.

  The target `Work.WilG4a.pullback_graph_mem` says that if the graphs of two one-parameter
  families `φ` and `f` (each a subset of `ℝ^{p+2}`, coordinates `(l, x, y)` with `y` the value)
  are `Ω F D (p+2)`, then the graph of the composite family `fun l t => f l (φ l t)` is
  `Ω a (eval ![D,r] b) (p+2)` for some `a : ℕ` and `b : MvPolynomial (Fin 2) ℕ` depending only
  on `F` and `p`.  Concretely one may take `a = F + 2 * ((p+3) + (p+2)) + 3` and
  `b = 4 + 2 * D`, i.e. the degree bound is `2 * D + 4`.

  ## Proof outline

  Work in `ℝ^{p+3}` with the coordinate layout `(l, t, y, s)`: the first `p` coordinates are the
  parameter `l`, then `t` (the argument of the composite), then `y` (the value of the composite,
  i.e. the value of `f`), and last `s` (the value of `φ`, i.e. the argument of `f`).

  * `sigA_y : Fin (p+2) → Fin (p+3)` selects the coordinates `(l, t, s)` — the layout of
    `graphFam φ`.  Its pullback is `A₁`, imposing `s = φ l t`.
  * `sigB_y : Fin (p+2) → Fin (p+3)` selects the coordinates `(l, s, y)` — the layout of
    `graphFam f`.  Its pullback is `A₂`, imposing `y = f l s`.

  Both pullbacks are `Ω`-sets by the substitution atom `Work.WilG4c.GraphComp.subst_mem`
  (a colleague's already-proved lemma); `A₁` has format `F + 2 * ((p+3) + (p+2)) + 1` and degree
  `D + 2`.  Intersecting (`SOMin.inter`) and projecting the last coordinate `s` away
  (`SOMin.proj`) yields exactly the graph of `l, t ↦ f l (φ l t)`: the projection forgets `s`
  and the two conditions become `∃ s, s = φ l t ∧ y = f l s`, i.e. `y = f l (φ l t)`.

  The two coordinate maps `sigA_y`, `sigB_y` and their action on `Fin.snoc`-vectors are the only
  combinatorial content (`comp_sigA_aux`, `comp_sigB_aux`); the set identity is `pullback_set_eq`.
-/
import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.subst_mem
import Submission.Work.WilG4a.Bounds
import Submission.Work.WilG4c.GraphOfComp

set_option autoImplicit false
set_option linter.deprecated false
noncomputable section
open Classical
namespace Work.WilG4a

open Function

/-! ## The two coordinate maps `Fin (p+2) → Fin (p+3)` -/

/-- In the coordinate layout `(l, t, y, s)` of `ℝ^{p+3}`, `sigA_y p` selects the coordinates
`(l, t, s)`: the layout of `graphFam φ` (parameters, argument, value). -/
def sigA_y (p : ℕ) : Fin (p + 2) → Fin (p + 3) := fun j =>
  if _h : (j : ℕ) ≤ p then ⟨j, by omega⟩ else ⟨p + 2, by omega⟩

/-- In the coordinate layout `(l, t, y, s)` of `ℝ^{p+3}`, `sigB_y p` selects the coordinates
`(l, s, y)`: the layout of `graphFam f` (parameters, argument, value).  Here the value `s` of
`φ` plays the role of the argument of `f`, and the coordinate `y` is the final value. -/
def sigB_y (p : ℕ) : Fin (p + 2) → Fin (p + 3) := fun j =>
  if _h : (j : ℕ) < p then ⟨j, by omega⟩
  else if _hj : (j : ℕ) = p then ⟨p + 2, by omega⟩
  else ⟨p + 1, by omega⟩

/-! ## Pointwise normal forms for `sigA_y` and `sigB_y` -/

theorem sigA_of_le (p : ℕ) (j : Fin (p + 2)) (h : (j : ℕ) ≤ p) : sigA_y p j = Fin.castSucc j := by
  simp only [sigA_y]; rw [dif_pos h]; exact Fin.ext rfl

theorem sigA_last (p : ℕ) : sigA_y p (Fin.last (p + 1)) = Fin.last (p + 2) := by
  simp only [sigA_y]; rw [dif_neg (by simp)]; rfl

theorem sigA_castSucc (p : ℕ) (i : Fin (p + 1)) :
    sigA_y p (Fin.castSucc i) = Fin.castSucc (Fin.castSucc i) := by
  apply sigA_of_le; simp only [Fin.val_castSucc]; omega

theorem sigB_of_lt_y (p : ℕ) (j : Fin (p + 2)) (h : (j : ℕ) < p) : sigB_y p j = Fin.castSucc j := by
  simp only [sigB_y]; rw [dif_pos h]; exact Fin.ext rfl

theorem sigB_of_eq (p : ℕ) (j : Fin (p + 2)) (h : (j : ℕ) = p) : sigB_y p j = Fin.last (p + 2) := by
  simp only [sigB_y]; rw [dif_neg (by omega), dif_pos h]; exact Fin.ext rfl

theorem sigB_last (p : ℕ) : sigB_y p (Fin.last (p + 1)) = Fin.castSucc (Fin.last (p + 1)) := by
  simp only [sigB_y]; rw [dif_neg (by simp), dif_neg (by simp)]; exact Fin.ext rfl

theorem sigB_castSucc_castSucc (p : ℕ) (i : Fin p) :
    sigB_y p (Fin.castSucc (Fin.castSucc i)) = Fin.castSucc (Fin.castSucc (Fin.castSucc i)) := by
  apply sigB_of_lt_y; simp only [Fin.val_castSucc]; omega

theorem sigB_castSucc_last (p : ℕ) :
    sigB_y p (Fin.castSucc (Fin.last p)) = Fin.last (p + 2) := by
  apply sigB_of_eq; simp

/-! ## The action of `sigA_y` and `sigB_y` on `Fin.snoc`-vectors -/

/-- On the glued vector `Fin.snoc w x : Fin (p+3) → ℝ` (layout `(l, t, y, s)` with `x = s`),
the pullback along `sigA_y` keeps `(l, t)` and the value `x`, i.e. produces the layout of
`graphFam φ`. -/
theorem comp_sigA_aux (p : ℕ) (w : Fin (p + 2) → ℝ) (x : ℝ) :
    (Fin.snoc w x) ∘ sigA_y p = Fin.snoc (Fin.init w) x := by
  funext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · rw [comp_apply, sigA_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc]; rfl
  · rw [comp_apply, sigA_last, Fin.snoc_last, Fin.snoc_last]

/-- On the glued vector `Fin.snoc w x : Fin (p+3) → ℝ` (layout `(l, t, y, s)` with `x = s`),
the pullback along `sigB_y` keeps `(l, x, y)`, i.e. produces the layout of `graphFam f`. -/
theorem comp_sigB_aux (p : ℕ) (w : Fin (p + 2) → ℝ) (x : ℝ) :
    (Fin.snoc w x) ∘ sigB_y p =
      Fin.snoc (Fin.snoc (Fin.init (Fin.init w)) x) (w (Fin.last (p + 1))) := by
  funext j
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · rcases Fin.eq_castSucc_or_eq_last i with ⟨i', rfl⟩ | rfl
    · rw [comp_apply, sigB_castSucc_castSucc, Fin.snoc_castSucc, Fin.snoc_castSucc,
        Fin.snoc_castSucc]; rfl
    · rw [comp_apply, sigB_castSucc_last, Fin.snoc_last, Fin.snoc_castSucc, Fin.snoc_last]
  · rw [comp_apply, sigB_last, Fin.snoc_castSucc, Fin.snoc_last]

/-! ## The set identity -/

/-- Projecting the last coordinate `s` away from the intersection of the two pullbacks gives
exactly the graph of the composite family. -/
theorem pullback_set_eq (p : ℕ) (φ f : (Fin p → ℝ) → ℝ → ℝ) :
    WilkiesDesign.projLast ({z : Fin (p + 3) → ℝ | z ∘ sigA_y p ∈ graphFam φ} ∩
              {z : Fin (p + 3) → ℝ | z ∘ sigB_y p ∈ graphFam f})
      = graphFam (fun l t => f l (φ l t)) := by
  ext w
  constructor
  · rintro ⟨x, hx⟩
    rw [Set.mem_inter_iff] at hx
    obtain ⟨h1, h2⟩ := hx
    simp only [Set.mem_ofPred_eq] at h1 h2
    rw [comp_sigA_aux] at h1
    rw [comp_sigB_aux] at h2
    rw [← Fin.snoc_init_self (Fin.init w)] at h1
    rw [mem_graphFam_iff] at h1
    rw [mem_graphFam_iff] at h2
    have key : Fin.snoc (Fin.snoc (Fin.init (Fin.init w)) ((Fin.init w) (Fin.last p)))
        (w (Fin.last (p + 1))) ∈ graphFam (fun l t => f l (φ l t)) :=
      (mem_graphFam_iff _ _ _ _).mpr (by rw [← h1]; exact h2)
    have hv : Fin.snoc (Fin.snoc (Fin.init (Fin.init w)) ((Fin.init w) (Fin.last p)))
        (w (Fin.last (p + 1))) = w := by
      rw [Fin.snoc_init_self (Fin.init w), Fin.snoc_init_self w]
    rwa [hv] at key
  · intro hw
    set X : ℝ := φ (Fin.init (Fin.init w)) ((Fin.init w) (Fin.last p)) with hX
    have hv : w = Fin.snoc (Fin.snoc (Fin.init (Fin.init w)) ((Fin.init w) (Fin.last p)))
        (w (Fin.last (p + 1))) := by
      rw [Fin.snoc_init_self (Fin.init w), Fin.snoc_init_self w]
    have hw' : w (Fin.last (p + 1)) = f (Fin.init (Fin.init w)) X := by
      rw [hv, mem_graphFam_iff, ← hX] at hw
      exact hw
    refine ⟨X, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq]
      rw [comp_sigA_aux, ← Fin.snoc_init_self (Fin.init w)]
      exact (mem_graphFam_iff φ _ _ _).mpr hX
    · simp only [Set.mem_ofPred_eq]
      rw [comp_sigB_aux]
      exact (mem_graphFam_iff f _ _ _).mpr hw'

/-! ## The target -/

theorem pullback_graph_mem (S : WilkiesDesign.SOMin) (p : ℕ) (F : ℕ) : ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D r : ℕ) {φ f : (Fin p → ℝ) → ℝ → ℝ}, Work.WilG4a.graphFam φ ∈ S.Ω F D (p + 1 + 1) → Work.WilG4a.graphFam f ∈ S.Ω F D (p + 1 + 1) → Work.WilG4a.graphFam (fun l t => f l (φ l t)) ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1 + 1) := by
  refine ⟨F + 2 * ((p + 3) + (p + 2)) + 1 + 1 + 1,
    MvPolynomial.C 4 + MvPolynomial.C 2 * MvPolynomial.X 0, ?_⟩
  intro D r φ f hφ hf
  -- the two pullbacks are `Ω`-sets (substitution atom)
  have hA1 : {z : Fin (p + 3) → ℝ | z ∘ sigA_y p ∈ graphFam φ} ∈
      S.Ω (F + 2 * ((p + 3) + (p + 2)) + 1) (D + 2) (p + 3) :=
    Work.WilG4c.GraphComp.subst_mem S (sigA_y p) hφ
  have hA2 : {z : Fin (p + 3) → ℝ | z ∘ sigB_y p ∈ graphFam f} ∈
      S.Ω (F + 2 * ((p + 3) + (p + 2)) + 1) (D + 2) (p + 3) :=
    Work.WilG4c.GraphComp.subst_mem S (sigB_y p) hf
  -- intersect, then project the last coordinate away
  have hW : ({z : Fin (p + 3) → ℝ | z ∘ sigA_y p ∈ graphFam φ} ∩
      {z : Fin (p + 3) → ℝ | z ∘ sigB_y p ∈ graphFam f}) ∈
      S.Ω (F + 2 * ((p + 3) + (p + 2)) + 1 + 1) ((D + 2) + (D + 2)) (p + 3) :=
    Work.WilG0.Omega_inter2 hA1 hA2
  have hP := S.proj hW
  rw [pullback_set_eq] at hP
  -- degree bookkeeping: `(D+2)+(D+2) = 4 + 2*D`
  have hd : MvPolynomial.eval ![D, r]
      (MvPolynomial.C 4 + MvPolynomial.C 2 * MvPolynomial.X 0) = (D + 2) + (D + 2) := by
    simp [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_X]
    ring
  rw [← hd] at hP
  exact hP

end Work.WilG4a
