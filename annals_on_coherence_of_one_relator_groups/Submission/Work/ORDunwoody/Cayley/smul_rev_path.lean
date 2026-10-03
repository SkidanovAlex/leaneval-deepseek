import Mathlib
import Submission.Work.ORDunwoody.Basic

universe u

namespace Work.ORDunwoody.Cayley

theorem smul_rev_path {G : Type u} [Group G] {V : Type u} [MulAction G V]
    {T : Work.ORDunwoody.GTree G V} {n : ℕ} {g : G} {w : Fin (n + 1) → V}
    (hadj : ∀ k : Fin n, T.Adj (w k.castSucc) (w k.succ))
    (hinj : Function.Injective w) :
    (∀ k : Fin n,
        T.Adj ((fun j => g • w (Fin.rev j)) k.castSucc) ((fun j => g • w (Fin.rev j)) k.succ)) ∧
      Function.Injective (fun j => g • w (Fin.rev j)) := by
  refine ⟨fun k => ?_, fun a b hab => ?_⟩
  · simp only [Fin.rev_castSucc, Fin.rev_succ]
    exact T.smul_adj g (hadj (Fin.rev k)).symm
  · simp only at hab
    exact Fin.rev_injective (hinj (MulAction.injective g hab))

end Work.ORDunwoody.Cayley
