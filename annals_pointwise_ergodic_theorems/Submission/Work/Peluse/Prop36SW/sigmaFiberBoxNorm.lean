import Mathlib
import Submission.Work.Peluse.Prop36SW.pDirEqDir

set_option autoImplicit false

namespace Work.Peluse.Prop36SW

/-- **Cardinality of a fibre of `g` on the slot type.**  For `g : α → β` and multiplicities `k` on
`α` with fibre sums `k'`, the fibre `{x : Σ a, Fin (k a) // g x.1 = b}` has cardinality `k' b`:
the fibre splits as the sigma over the `a` with `g a = b` of the `Fin (k a)`. -/
lemma card_fiber_sigma {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (g : α → β) (k : α → ℕ) (k' : β → ℕ)
    (hk' : ∀ b, k' b = ∑ a ∈ Finset.univ.filter (fun a => g a = b), k a) :
    ∀ b : β, Fintype.card {x : (Σ a : α, Fin (k a)) // g x.1 = b} = k' b := by
  intro b
  rw [hk' b]
  have e : {x : (Σ a : α, Fin (k a)) // g x.1 = b} ≃
      (Σ a : {a : α // g a = b}, Fin (k a.1)) :=
    { toFun := fun x => ⟨⟨x.1.1, x.2⟩, x.1.2⟩
      invFun := fun y => ⟨⟨y.1.1, y.2⟩, y.1.2⟩
      left_inv := fun x => by rcases x with ⟨⟨a, i⟩, h⟩; rfl
      right_inv := fun y => by rcases y with ⟨⟨a, h⟩, i⟩; rfl }
  rw [Fintype.card_congr e, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact (Finset.sum_subtype (Finset.univ.filter (fun a : α => g a = b))
    (by intro x; simp) k).symm

/-- **The fibre-preserving splitting of the slot type.**  If the multiplicities `k'` of `β` are the
fibre sums of the multiplicities `k` of `α` along `g`, then there is a bijection
`Σ a, Fin (k a) ≃ Σ b, Fin (k' b)` carrying `⟨a, _⟩` into the fibre over `g a`. -/
lemma exists_fiber_equiv {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (g : α → β) (k : α → ℕ) (k' : β → ℕ)
    (hk' : ∀ b, k' b = ∑ a ∈ Finset.univ.filter (fun a => g a = b), k a) :
    ∃ φ : (Σ a : α, Fin (k a)) ≃ (Σ b : β, Fin (k' b)), ∀ x, (φ x).1 = g x.1 := by
  have hcardb := card_fiber_sigma g k k' hk'
  have eb : ∀ b : β, {x : (Σ a : α, Fin (k a)) // g x.1 = b} ≃ Fin (k' b) :=
    fun b => (Fintype.equivFin _).trans (finCongr (hcardb b))
  let ψ1 : (Σ a : α, Fin (k a)) ≃ (Σ b : β, {x : (Σ a : α, Fin (k a)) // g x.1 = b}) :=
    (Equiv.sigmaFiberEquiv (fun x : (Σ a : α, Fin (k a)) => g x.1)).symm
  let ψ2 : (Σ b : β, {x : (Σ a : α, Fin (k a)) // g x.1 = b}) ≃ (Σ b : β, Fin (k' b)) :=
    Equiv.sigmaCongrRight eb
  exact ⟨ψ1.trans ψ2, fun x => rfl⟩

theorem sigmaFiberBoxNorm {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (g : α → β) (k : α → ℕ) (k' : β → ℕ)
    (hk' : ∀ b, k' b = ∑ a ∈ Finset.univ.filter (fun a => g a = b), k a)
    (G : β → Finset ℤ) (S : Finset ℤ) (F : ℤ → ℂ) :
    Work.Peluse.boxNormPow (Fintype.card (Σ a : α, Fin (k a)))
        (fun i => G (g ((Fintype.equivFin (Σ a : α, Fin (k a))).symm i).1)) S F
      = Work.Peluse.boxNormPow (Fintype.card (Σ b : β, Fin (k' b)))
        (fun i => G ((Fintype.equivFin (Σ b : β, Fin (k' b))).symm i).1) S F := by
  obtain ⟨φ, hφ⟩ := exists_fiber_equiv g k k' hk'
  have hcard : Fintype.card (Σ a : α, Fin (k a)) = Fintype.card (Σ b : β, Fin (k' b)) :=
    Fintype.card_congr φ
  have main := boxNormPow_family_equiv φ (fun x : (Σ a : α, Fin (k a)) => G (g x.1))
    (Fintype.equivFin (Σ a : α, Fin (k a))) (Fintype.equivFin (Σ b : β, Fin (k' b))) hcard S F
  have hfuneq : (fun i : Fin (Fintype.card (Σ b : β, Fin (k' b))) =>
      G (g ((φ.symm ((Fintype.equivFin (Σ b : β, Fin (k' b))).symm i)).1)))
      = fun i => G ((Fintype.equivFin (Σ b : β, Fin (k' b))).symm i).1 := by
    funext i
    rw [← hφ (φ.symm ((Fintype.equivFin (Σ b : β, Fin (k' b))).symm i)),
      Equiv.apply_symm_apply]
  rw [hfuneq] at main
  exact main

end Work.Peluse.Prop36SW
