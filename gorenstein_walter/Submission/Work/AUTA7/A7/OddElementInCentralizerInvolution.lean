import Mathlib

namespace Work.AUTA7.A7

/-- If `Z` is an involution different from the identity acting on `Fin 7`, then its
centralizer contains an odd permutation. Indeed, pick `x` with `Z x ≠ x`; then
`x` and `Z x` form a 2-cycle of `Z`, and the transposition `swap x (Z x)` is odd
and commutes with `Z`. -/
theorem OddElementInCentralizerInvolution {Z : Equiv.Perm (Fin 7)} (hZ : Z * Z = 1) (hZ1 : Z ≠ 1) :
    ∃ c ∈ Subgroup.centralizer ({Z} : Set (Equiv.Perm (Fin 7))), Equiv.Perm.sign c = -1 := by
  -- `Z` is not the identity, so some point is moved.
  have hne : ∃ x : Fin 7, Z x ≠ x := by
    rw [← not_forall]
    intro hall
    exact hZ1 (Equiv.ext hall)
  obtain ⟨x, hx⟩ := hne
  -- `Z` is an involution: `Z (Z p) = p` for all `p`.
  have hZZ : ∀ p : Fin 7, Z (Z p) = p := by
    intro p
    have h := DFunLike.congr_fun hZ p
    rwa [Equiv.Perm.mul_apply, Equiv.Perm.one_apply] at h
  -- The transposition of the 2-cycle `x, Z x` commutes with `Z`.
  have hcomm : Z * Equiv.swap x (Z x) = Equiv.swap x (Z x) * Z := by
    apply Equiv.ext
    intro p
    simp only [Equiv.Perm.mul_apply]
    rcases eq_or_ne p x with hpx | hpx
    · rw [hpx, Equiv.swap_apply_left, Equiv.swap_apply_right, hZZ x]
    · rcases eq_or_ne p (Z x) with hpZx | hpZx
      · rw [hpZx, Equiv.swap_apply_right, hZZ x, Equiv.swap_apply_left]
      · have hZp_ne_x : Z p ≠ x := fun hc => hpZx (by rw [← hZZ p, hc])
        have hZp_ne_Zx : Z p ≠ Z x := fun hc => hpx (by rw [← hZZ p, hc, hZZ x])
        rw [Equiv.swap_apply_of_ne_of_ne hpx hpZx,
            Equiv.swap_apply_of_ne_of_ne hZp_ne_x hZp_ne_Zx]
  refine ⟨Equiv.swap x (Z x), ?_, Equiv.Perm.sign_swap (Ne.symm hx)⟩
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  rw [hh]
  exact hcomm

end Work.AUTA7.A7
