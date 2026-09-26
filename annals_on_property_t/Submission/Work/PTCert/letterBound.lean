import Mathlib
import Submission.Work.PTCert.OrderUnit
import Submission.Work.PTCert.LetterAPI

open OnPropertyT

namespace Work.PTCert

open Submission.FreeGroupAut

/-- For a symmetric finite set `S` of a group `G` and an element `g` that is either a member
of `S` or the identity of the group algebra, the element `2·Δ_S − star(1−g)(1−g)` is a sum of
hermitian squares.

Indeed `2·Δ_S = ∑_{s∈S} star(1−s)(1−s)` (the paper's equation (1)); subtracting the single
hermitian square of `g` leaves the sum over `S.erase g`, which is again a sum of hermitian
squares. -/
theorem isSOS_two_smul_laplacian_sub_sq {G : Type*} [Group G]
    (S : Finset G) (hsym : (S : Set G)⁻¹ = S) (g : G)
    (hg : g ∈ S ∨ MonoidAlgebra.of ℝ G g = 1) :
    Submission.RouteB.IsSOS ((2 : ℝ) • OnPropertyT.Laplacian S
      - star (1 - MonoidAlgebra.of ℝ G g) * (1 - MonoidAlgebra.of ℝ G g)) := by
  classical
  have hΔ : (2 : ℝ) • OnPropertyT.Laplacian S
      = ∑ s ∈ S, star (1 - MonoidAlgebra.of ℝ G s) * (1 - MonoidAlgebra.of ℝ G s) := by
    rw [two_smul, ← two_mul, Submission.RouteB.two_mul_laplacian_eq_sum_sq S hsym]
  rw [hΔ]
  have heq : (∑ s ∈ S, star (1 - MonoidAlgebra.of ℝ G s) * (1 - MonoidAlgebra.of ℝ G s))
      - star (1 - MonoidAlgebra.of ℝ G g) * (1 - MonoidAlgebra.of ℝ G g)
      = ∑ s ∈ S.erase g, star (1 - MonoidAlgebra.of ℝ G s) * (1 - MonoidAlgebra.of ℝ G s) := by
    by_cases hgS : g ∈ S
    · rw [← Finset.sum_erase_add S (fun s => star (1 - MonoidAlgebra.of ℝ G s)
        * (1 - MonoidAlgebra.of ℝ G s)) hgS]
      abel
    · have hof : MonoidAlgebra.of ℝ G g = 1 := hg.resolve_left hgS
      have hcg : star (1 - MonoidAlgebra.of ℝ G g) * (1 - MonoidAlgebra.of ℝ G g) = 0 := by
        rw [hof, sub_self, star_zero, zero_mul]
      rw [hcg, sub_zero, Finset.erase_eq_self.mpr hgS]
  rw [heq]
  exact Submission.RouteB.IsSOS.finset_sum _ (fun s _ =>
    ⟨{1 - MonoidAlgebra.of ℝ G s}, by rw [Finset.sum_singleton]⟩)

theorem letterBound (r k : ℕ) (hk : k < Submission.PTCert.NB1 r) : Submission.RouteB.IsSOS ((2 : ℝ) • Submission.RouteB.Edge.deltaSub r r - star (1 - MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r k)) * (1 - MonoidAlgebra.of ℝ (MulAut (FreeGroup (Fin r))) (Submission.PTCert.b1 r k))) := by
  rw [Submission.RouteB.Edge.deltaSub_top]
  by_cases hk0 : k = 0
  · subst hk0
    refine isSOS_two_smul_laplacian_sub_sq (SAutGen r) (sAutGen_symm r)
      (Submission.PTCert.b1 r 0) (Or.inr ?_)
    rw [show Submission.PTCert.b1 r 0 = 1 from by simp [Submission.PTCert.b1]]
    exact map_one _
  · have hk1 : 1 ≤ k := by omega
    have hr : 2 ≤ r := by
      have hlt : 1 < Submission.PTCert.NB1 r := by omega
      simp only [Submission.PTCert.NB1] at hlt
      have hpos : 0 < 4 * r * (r - 1) := by omega
      have hr1 : 0 < r - 1 := Nat.pos_of_mul_pos_left hpos
      omega
    exact isSOS_two_smul_laplacian_sub_sq (SAutGen r) (sAutGen_symm r)
      (Submission.PTCert.b1 r k) (Or.inl (Submission.PTCert.b1_mem_SAutGen r k hr hk1 hk))

end Work.PTCert
