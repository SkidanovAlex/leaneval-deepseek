import Mathlib
import Submission.Work.L62.chain
import Submission.Work.Repel.walk_of_sub

namespace Work.Repel

/-- **Derivative bound for the iterate at an integer translate.**

The chain `h` bounds `‖deriv ĥ^[j]‖` on the disc `W j` (`IsChain.deriv_bd`), with
`ĥ = R - β`.  Because `R` is `T`-equivariant on the `T`-invariant set `DR` and `W j` is
open, the *germ* of `ĥ^[j]` at a point `w ∈ W j` and at its integer translate
`u = w + k` are translates of one another: on the whole (open) disc `W j` one has
`ĥ^[j](y + k) = ĥ^[j] y + k` (`Work.Repel.chain_walk_add_int`), so `deriv` is the same at
`w` and at `w + k` (`deriv` is a local notion, and the translation `y ↦ y + k` has
derivative `1`).  Hence the bound transfers to the translate. -/
theorem deriv_iterate_shift_le {R : ℂ → ℂ} {β : ℂ} {DR : Set ℂ} {ζa ζb : ℂ} {ρ sgn C₀ C₁ C₁' : ℝ}
    {W : ℕ → Set ℂ} (h : Work.L62.IsChain R β DR ζa ζb ρ sgn C₀ C₁ C₁' W)
    (hReq : MandelDim.IsTEquivariantOn R DR) {j : ℕ} {k : ℤ} {u : ℂ}
    (hu : u ∈ (fun x : ℂ => x + ((k : ℤ) : ℂ)) '' W j) :
    ‖deriv ((fun u => R u - β)^[j]) u‖ < C₁' := by
  -- write `u` as an integer translate of a point `w` of the disc `W j`
  obtain ⟨w, hwW, hwuk⟩ := hu
  have hwu : w + ((k : ℤ) : ℂ) = u := hwuk
  -- the iterate commutes with the integer translation, on the whole open disc `W j`
  have hg : ∀ y ∈ W j, (fun u => R u - β)^[j] (y + ((k : ℤ) : ℂ))
      = (fun u => R u - β)^[j] y + ((k : ℤ) : ℂ) :=
    fun y hy => chain_walk_add_int h hReq hy j le_rfl
  -- hence the two functions agree on a neighbourhood of `w`
  have heq : (fun u => R u - β)^[j] =ᶠ[nhds w]
      (fun y => (fun u => R u - β)^[j] (y + ((k : ℤ) : ℂ)) - ((k : ℤ) : ℂ)) := by
    filter_upwards [(h.open_conn j).1.mem_nhds hwW] with y hy
    rw [hg y hy]
    ring
  -- `deriv` is local, translation-invariant, and drops additive constants
  have hkey : deriv ((fun u => R u - β)^[j]) w = deriv ((fun u => R u - β)^[j]) u := by
    rw [heq.deriv_eq, deriv_sub_const, deriv_comp_add_const, hwu]
  rw [← hkey]
  exact (h.deriv_bd j w hwW).2

end Work.Repel
