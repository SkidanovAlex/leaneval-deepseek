import Mathlib
import Submission.Work.ORHughesFree.SylvesterRank
import Submission.Work.ORHughesFree.StarRegular
import Submission.Work.Section3.oneByOne_le_rdim_span
import Submission.Work.ORHughesFree.NaturalExtension.DualityAPI
import Submission.Work.Section3.rank_oneByOne_eq_of_span_eq

namespace Work.Section3.RkFinModel

universe u

open Work.ORHughesFree

/-- Auxiliary: the rank of `oneByOne e` is bounded by the rank of `oneByOne s` when `e = s * c`. -/
theorem rk_oneByOne_le_of_eq_mul {S : Type u} [Ring S] (ρ : SylvesterRank S) {e s : S}
    (hec : ∃ c : S, e = s * c) :
    ρ.rk 1 1 (oneByOne e) ≤ ρ.rk 1 1 (oneByOne s) := by
  obtain ⟨c, hc⟩ := hec
  rw [hc, Work.Section3.oneByOne_mul]
  exact ρ.rk_mul_le_left _ _

theorem rkcs_oneByOne_le_rdim_span_sub_proj {S : Type u} [Ring S]
    [Work.ORHughesFree.VonNeumannRegularRing S] {n : ℕ}
    (ρ : Work.ORHughesFree.SylvesterRank S)
    (E : Module.End S (Fin n → S)) (u : Fin n → S) {e s : S}
    (ψ : (Fin n → S) →ₗ[S] (Fin 1 → S))
    (hψ0 : ∀ y ∈ LinearMap.range E, ψ y = 0) (hψu : ψ u = fun _ => s)
    (hec : ∃ c : S, e = s * c) :
    ρ.rk 1 1 (Work.ORHughesFree.oneByOne e)
      ≤ Work.ORHughesFree.NaturalExtension.rdim ρ
          (Submodule.span S ({u - E u} : Set (Fin n → S))) := by
  -- `E u` lies in the range of `E`, so `ψ` annihilates it, hence `ψ (u - E u) = const s`.
  have hEu : E u ∈ LinearMap.range E := ⟨u, rfl⟩
  have hψ : ψ (u - E u) = (fun _ : Fin 1 => s) := by
    rw [map_sub, hψu, hψ0 (E u) hEu, sub_zero]
  -- Bound by `oneByOne s`, then apply the one-generator estimate.
  exact le_trans (rk_oneByOne_le_of_eq_mul ρ hec)
    (Work.Section3.oneByOne_le_rdim_span (s := s) ρ ψ (u - E u) hψ)

end Work.Section3.RkFinModel
