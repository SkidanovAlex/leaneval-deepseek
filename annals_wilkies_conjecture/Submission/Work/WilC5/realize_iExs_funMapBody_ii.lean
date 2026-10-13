import Mathlib
import Submission.Work.WilC5.DclMapTools

namespace Work.WilC5

open FirstOrder Language

theorem realize_iExs_funMapBody_ii {L : FirstOrder.Language} {M : Type} [L.Structure M] {γ : Type}
    (ii : γ → M) {n : ℕ} (f : L.Functions n) (x : Fin n → M)
    (φk : Fin n → L.Formula (γ ⊕ Fin 1))
    (hk : ∀ k, ∀ v : Fin 1 → M, v 0 = x k ↔ (φk k).Realize (Sum.elim ii v))
    (v : Fin 1 → M) :
    (FirstOrder.Language.Formula.iExs (Fin n) (Work.WilC5.funMapBody f φk)).Realize
        (Sum.elim ii v) ↔ v 0 = FirstOrder.Language.Structure.funMap f x := by
  rw [funMapBody, Formula.realize_iExs]
  constructor
  · rintro ⟨zs, hzs⟩
    simp only [Formula.realize_inf, Formula.realize_iInf, Formula.realize_equal, Term.realize_var,
      Term.realize_func, Formula.realize_relabel, sumElim_comp_sumElim, Sum.elim_comp_inl,
      Sum.elim_inl, Sum.elim_inr] at hzs
    obtain ⟨hφ, heq⟩ := hzs
    have hzx : zs = x := by
      funext k
      exact (hk k (fun _ => zs k)).2 (hφ k)
    rw [hzx] at heq
    exact heq
  · intro hv
    refine ⟨x, ?_⟩
    simp only [Formula.realize_inf, Formula.realize_iInf, Formula.realize_equal, Term.realize_var,
      Term.realize_func, Formula.realize_relabel, sumElim_comp_sumElim, Sum.elim_comp_inl,
      Sum.elim_inl, Sum.elim_inr]
    exact ⟨fun k => (hk k (fun _ => x k)).1 rfl, hv⟩

end Work.WilC5
