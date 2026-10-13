import Mathlib
import Submission.Work.WilC0.Basic
import Submission.Work.WilC0.Compl
import Submission.Work.Wilkies.CG.Spec

namespace Work.WilC0

set_option autoImplicit false
open FirstOrder FirstOrder.Language
open scoped FirstOrder

open WilkiesDesign (rexp)

/-- The graph hypothesis `hTerm` upgraded to an equation between two terms. -/
theorem termEq_rex
    (hTerm : ∀ {ι : Type} (t : WilkiesDesign.CG.LRc.Term ι),
      Work.WilC0.RExpExistI
        {z : (ι ⊕ Fin 1) → ℝ | z (Sum.inr (0 : Fin 1)) = t.realize (z ∘ Sum.inl)})
    {ι : Type} (t₁ t₂ : WilkiesDesign.CG.LRc.Term ι) :
    Work.WilC0.RExpExistI {z : ι → ℝ | t₁.realize z = t₂.realize z} := by
  have h1 := hTerm t₁
  have h2 := hTerm t₂
  have hI : RExpExistI
      ({z : (ι ⊕ Fin 1) → ℝ | z (Sum.inr (0 : Fin 1)) = t₁.realize (z ∘ Sum.inl)} ∩
        {z : (ι ⊕ Fin 1) → ℝ | z (Sum.inr (0 : Fin 1)) = t₂.realize (z ∘ Sum.inl)}) :=
    h1.inter h2
  refine (hI.projLast).of_eq ?_
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  constructor
  · rintro ⟨a, h1', h2'⟩
    simpa using h1'.symm.trans h2'
  · intro h
    exact ⟨t₂.realize z, by simpa using h.symm, by simp⟩

/-- Universal quantification over a fresh (last) variable, transported to the `Sum`-indexed side:
if `A ⊆ (κ ⊕ Fin (m+1)) → ℝ` is existentially definable then so is the set of `z : κ ⊕ Fin m → ℝ`
whose every extension `Sum.elim (z ∘ Sum.inl) (Fin.snoc (z ∘ Sum.inr) a)` lies in `A`. -/
theorem RExpExistI.forall_snoc {κ : Type} [Fintype κ]
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)),
      WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    {m : ℕ} {A : Set ((κ ⊕ Fin (m + 1)) → ℝ)} (hA : RExpExistI A) :
    RExpExistI {z : κ ⊕ Fin m → ℝ |
      ∀ a : ℝ, Sum.elim (z ∘ Sum.inl) (Fin.snoc (z ∘ Sum.inr) a) ∈ A} := by
  let g : κ ⊕ Fin (m + 1) → (κ ⊕ Fin m) ⊕ Fin 1 :=
    Sum.elim (fun i => Sum.inl (Sum.inl i))
      (Fin.snoc (fun j : Fin m => Sum.inl (Sum.inr j)) (Sum.inr (0 : Fin 1)))
  have hkey : ∀ (z : κ ⊕ Fin m → ℝ) (a : ℝ),
      (Sum.elim z (fun _ : Fin 1 => a)) ∘ g
        = Sum.elim (z ∘ Sum.inl) (Fin.snoc (z ∘ Sum.inr) a) := by
    intro z a
    funext q
    rcases q with i | r
    · rfl
    · rcases Fin.eq_castSucc_or_eq_last r with ⟨j, rfl⟩ | rfl
      · simp only [g, Sum.elim_inr, Fin.snoc_castSucc, Sum.elim_inl, Function.comp_apply]
      · simp only [g, Sum.elim_inr, Fin.snoc_last, Function.comp_apply]
  have hT : RExpExistI {w : (κ ⊕ Fin m) ⊕ Fin 1 → ℝ | w ∘ g ∈ A} := hA.pullback g
  refine (((hT.compl hR).projLast).compl hR).of_eq ?_
  ext z
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_exists, not_not]
  constructor
  · intro h a
    rw [← hkey z a]
    exact h a
  · intro h a
    rw [hkey z a]
    exact h a

/-- Every set defined by an `LRc`-formula `φ` with `n` free variables and `k` in-scope bound
variables is existentially definable in `ℝ_rexp`, given Gabrielov's complement hypothesis `hR` and
the graph lemma `hTerm` for terms.

The index type of the ambient tuple is `Fin n ⊕ Fin k`; `z ∘ Sum.inl` is the free-variable
valuation and `z ∘ Sum.inr` the bound-variable valuation. -/
theorem bfSet_rex
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)),
      WilkiesDesign.RExpExist X → WilkiesDesign.RExpExist Xᶜ)
    (hTerm : ∀ {ι : Type} (t : WilkiesDesign.CG.LRc.Term ι),
      Work.WilC0.RExpExistI
        {z : (ι ⊕ Fin 1) → ℝ | z (Sum.inr (0 : Fin 1)) = t.realize (z ∘ Sum.inl)})
    {n k : ℕ} (φ : WilkiesDesign.CG.LRc.BoundedFormula (Fin n) k) :
    Work.WilC0.RExpExistI
      {z : (Fin n ⊕ Fin k) → ℝ | φ.Realize (z ∘ Sum.inl) (z ∘ Sum.inr)} := by
  induction φ using FirstOrder.Language.BoundedFormula.rec with
  | falsum =>
    refine RExpExistI.empty.of_eq ?_
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false]
    exact Iff.rfl
  | equal t₁ t₂ =>
    refine (termEq_rex hTerm t₁ t₂).of_eq ?_
    ext z
    simp only [Set.mem_ofPred_eq]
    rw [show (BoundedFormula.equal t₁ t₂).Realize (z ∘ Sum.inl) (z ∘ Sum.inr) ↔
        Term.realize (Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr)) t₁ =
          Term.realize (Sum.elim (z ∘ Sum.inl) (z ∘ Sum.inr)) t₂ from Iff.rfl]
    rw [sumElim_comp_self z]
  | rel R _ =>
    rcases R with (R | R) | R <;> exact R.elim
  | imp f₁ f₂ ih1 ih2 =>
    refine ((ih1.compl hR).union ih2).of_eq ?_
    ext z
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Set.mem_union, BoundedFormula.realize_imp]
    tauto
  | all f ih =>
    refine (ih.forall_snoc hR).of_eq ?_
    ext z
    simp only [Set.mem_ofPred_eq, BoundedFormula.realize_all, sumElim_comp_inl,
      sumElim_comp_inr]

end Work.WilC0
