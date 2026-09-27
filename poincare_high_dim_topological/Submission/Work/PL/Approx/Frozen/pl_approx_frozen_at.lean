import Mathlib
import Submission.Work.PL.Approx.Defs
import Submission.Work.PL.Approx.Frozen.pl_approx_frozen_sub
import Submission.Work.PL.Approx.Interp.exists_interp
import Submission.Work.PL.Approx.Near.dist_lt_of_linOn
import Submission.Work.PL.Approx.Interp.eqOn_simp_of_eqOn

namespace Work.PL.Approx.Frozen

/-- Frozen PL approximation in the cube form used by the engulfing argument, stated for the
`r`-fold subdivision `S.iter r K hK` of `K`.

This is the specialisation of `pl_approx_frozen_sub` to the complex `K' := S.iter r K hK`:
the `r`-fold subdivision of `K` is finite (`Subdiv.iter_fin`) and subdivides `K`
(`Subdiv.iter_subdivides`), the frozen complex `L` is a subcomplex of it (`hLK`), and the
oscillation hypothesis is stated on the faces of `S.iter r K hK`.  In particular the resulting
map `g` is affine on every face of `S.iter r K hK` whose image under `g` meets the cube
`closedCube α`. -/
lemma pl_approx_frozen_at {N n : ℕ} (S : Subdiv N) (K : PL.Cx N) (hK : K.faces.Finite) (r : ℕ)
    (L : PL.Cx N) (hLK : PL.IsSub L (S.iter r K hK)) (f : PL.E N → PL.E n)
    (hf : ContinuousOn f K.space) (α β : ℝ) (hα : 0 < α) (hαβ : α < β) (hβ1 : β < 1)
    (ε : ℝ) (hε : 0 < ε)
    (hlinL : ∀ ρ ∈ L.faces, (∃ z ∈ PL.simp ρ, f z ∈ PL.closedCube β) →
      ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∀ z ∈ PL.simp ρ, f z = A z)
    (hosc : ∀ s ∈ (S.iter r K hK).faces, ∀ x ∈ PL.simp s, ∀ y ∈ PL.simp s,
      dist (f x) (f y) < min ε ((β - α) / 24)) :
    ∃ g : PL.E N → PL.E n, ContinuousOn g K.space ∧ (∀ x ∈ K.space, dist (g x) (f x) < ε) ∧
      (∀ x ∈ K.space, f x ∉ PL.closedCube β → g x = f x) ∧ (∀ x ∈ L.space, g x = f x) ∧
      ∀ s ∈ (S.iter r K hK).faces, (∃ x ∈ PL.simp s, g x ∈ PL.closedCube α) →
        ∃ A : PL.E N →ᵃ[ℝ] PL.E n, ∀ y ∈ PL.simp s, g y = A y := by
  exact pl_approx_frozen_sub K (S.iter r K hK) (S.iter_fin r K hK) L hLK f hf
    (S.iter_subdivides r K hK) α β hα hαβ hβ1 ε hε hlinL hosc

end Work.PL.Approx.Frozen
