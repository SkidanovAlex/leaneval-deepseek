import Mathlib
import Submission.Work.SSS.Statements

/-!
# Serre's three-for-two theorem, assembled

`Work.SSS.serreFG_of_pieces` derives `Work.PiS.SerreFGThreeForTwo` from the two inputs
`Work.SSS.PacketStatement` (convergence of the spectral sequence of a saturated filtration) and
`Work.SSS.SerreE2Statement` (the E² page of the Serre spectral sequence of a Serre fibration over a
simply connected base).  The three directions are exactly Serre's three-for-two theorem read in the
Serre class of finitely generated abelian groups; each is an induction using the corresponding edge
statement of the spectral sequence (or, for the total direction, the graded pieces of the image
filtration).
-/

set_option autoImplicit false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

theorem serreFG_of_pieces (hp : PacketStatement) (hg : SerreE2Statement) :
    Work.PiS.SerreFGThreeForTwo := by
  intro E B _ _ p e₀ hfib hconn
  obtain ⟨ξ, hbase, hE2, hfib0⟩ := hg E B p e₀ hfib hconn
  have hpack : SSPacket ξ := hp _ ξ
  refine ⟨?_, ?_, ?_⟩
  · -- total: `H_*(B)` and `H_*(F)` f.g. ⇒ `H_*(E)` f.g.
    intro N hB hF n hn
    exact hpack.total n fun s hs =>
      hE2 s (n - s) (hB s (by omega)) (hB (s - 1) (by omega)) (hF (n - s) (by omega))
  · -- base: `H_*(E)` and `H_*(F)` f.g. ⇒ `H_*(B)` f.g.
    intro N hE hF
    suffices ∀ n : ℕ, n ≤ N + 1 → Module.Finite ℤ (Work.PiS.HZ B n) from this
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      refine hbase n (hpack.base_row n (hE n (by omega)) fun r hr hr' => ?_)
      exact hE2 (n - r) (r - 1) (ih (n - r) (by omega) (by omega))
        (ih (n - r - 1) (by omega) (by omega)) (hF (r - 1) (by omega))
  · -- fibre: `H_*(B)` and `H_*(E)` f.g. ⇒ `H_*(F)` f.g.
    intro N hB hE
    suffices ∀ t : ℕ, t ≤ N → Module.Finite ℤ (Work.PiS.HZ (Work.StemsB.fibre p (p e₀)) t) from this
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro ht
      refine (hfib0 t).mpr (hpack.fibre_col t (fun r hr hr' =>
        hE2 r (t + 1 - r) (hB r (by omega)) (hB (r - 1) (by omega))
          (ih (t + 1 - r) (by omega) (by omega))) ?_)
      haveI : Module.Finite ℤ (Work.PiS.HZ E t) := hE t ht
      rw [Module.finite_def] at this
      exact Submodule.FG.of_le this le_top

end

end Work.SSS
