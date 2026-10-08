import Mathlib
import Submission.Work.DSTR.Defs

namespace Work.DSTR

/-- General fact: if `N ◁ G`, `n ∈ N` and `H ≤ G`, then conjugation by `n` maps `H` into
`H ⊔ N`.

Indeed, for `h ∈ H` one has the identity `n * h * n⁻¹ = h * ((h⁻¹ * n * h) * n⁻¹)`, and
`h⁻¹ * n * h ∈ N` because `N` is normal while `n⁻¹ ∈ N`, so the second factor lies in `N`.
Both factors are therefore in `H ⊔ N`. -/
theorem map_conj_le_sup_of_mem {G : Type*} [Group G] (N : Subgroup G) [hN : N.Normal]
    {n : G} (hn : n ∈ N) (H : Subgroup G) :
    Subgroup.map (MulAut.conj n).toMonoidHom H ≤ H ⊔ N := by
  rw [Subgroup.map_le_iff_le_comap]
  intro h hh
  rw [Subgroup.mem_comap]
  have heq : (MulAut.conj n).toMonoidHom h = h * (h⁻¹ * n * h * n⁻¹) := by
    show (MulAut.conj n) h = h * (h⁻¹ * n * h * n⁻¹)
    rw [MulAut.conj_apply]; group
  rw [heq]
  have hconj : h⁻¹ * n * h ∈ N := by
    simpa using Subgroup.Normal.conj_mem hN n hn h⁻¹
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hh)
    (Subgroup.mem_sup_right (N.mul_mem hconj (N.inv_mem hn)))

/-- Let `G` be finite, `N ◁ G`, `n ∈ N`.  Conjugation by `n` sends `O_p(C_G(t))` into `O_p(C_G(t)) · N`.  (The general fact is: for `H ≤ G` and `n ∈ N ◁ G`, `n·h·n⁻¹ = h·((h⁻¹·n·h)·n⁻¹)` with `h⁻¹·n·h ∈ N` and `n⁻¹ ∈ N`.) -/
theorem conj_pCoreIn_le_sup_of_mem {G : Type*} [Group G] [Finite G] (N : Subgroup G) [N.Normal] (t : G) (ht : orderOf t = 2) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) {n : G} (hn : n ∈ N) : Subgroup.map (MulAut.conj n).toMonoidHom (Work.GW2.pCoreIn p (Subgroup.centralizer ({t} : Set G))) ≤ Work.GW2.pCoreIn p (Subgroup.centralizer ({t} : Set G)) ⊔ N := by
  exact map_conj_le_sup_of_mem N hn _

end Work.DSTR
