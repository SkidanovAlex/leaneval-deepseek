import Mathlib
import Submission.Work.ORBassSerre.Tree.Basic
import Submission.Work.ORBassSerre.Path.Reduction.deleteBacktrack_diamond

namespace Work.ORBassSerre.Path.Reduction

open Quiver

/-- `ReducesTo` is confluent: any two reducts of a path admit a common reduct.  This is Newman's
argument: `DeleteBacktrack` is terminating (it strictly decreases `length`) and locally confluent
(the diamond `deleteBacktrack_diamond`), hence confluent. -/
theorem reducesTo_join_aux {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V] :
    ∀ n : ℕ, ∀ {a b : V} (u : Quiver.Path a b), u.length ≤ n →
      ∀ v w : Quiver.Path a b, u.ReducesTo v → u.ReducesTo w →
        ∃ z : Quiver.Path a b, v.ReducesTo z ∧ w.ReducesTo z := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a b u hu v w h1 h2
    rcases Relation.ReflTransGen.cases_head h1 with hv | ⟨c, huc, hcv⟩
    · -- `u = v`: the common reduct is `w`.
      rw [← hv]
      exact ⟨w, h2, Quiver.Path.ReducesTo.refl w⟩
    rcases Relation.ReflTransGen.cases_head h2 with hw | ⟨d, hud, hdw⟩
    · -- `u = w`: the common reduct is `v`.
      rw [← hw]
      exact ⟨v, Quiver.Path.ReducesTo.refl v, Relation.ReflTransGen.head huc hcv⟩
    · -- Two nontrivial first steps: use the diamond, then the induction hypothesis three times.
      obtain ⟨z0, hcz0, hdz0⟩ := deleteBacktrack_diamond huc hud
      have hc_lt : c.length < n := by
        have := huc.length_lt
        omega
      have hd_lt : d.length < n := by
        have := hud.length_lt
        omega
      have hz0_lt : z0.length < n := by
        have := hcz0.length_le
        omega
      obtain ⟨z1, hvz1, hz0z1⟩ := ih c.length hc_lt c le_rfl v z0 hcv hcz0
      obtain ⟨z2, hz0z2, hwz2⟩ := ih d.length hd_lt d le_rfl z0 w hdz0 hdw
      obtain ⟨z3, hz1z3, hz2z3⟩ := ih z0.length hz0_lt z0 le_rfl z1 z2 hz0z1 hz0z2
      exact ⟨z3, hvz1.trans hz1z3, hwz2.trans hz2z3⟩

/-- Confluence of backtrack deletion: if `u` reduces to the reduced path `w` and also to `v`, then `v` reduces to `w`. (Proof: strong induction on the length of `u`, using the local-confluence diamond `Work.ORBassSerre.Path.Reduction.deleteBacktrack_diamond` and `Relation.ReflTransGen.cases_head`.) -/
theorem reducesTo_of_reducesTo_of_isReduced {V : Type*} [Quiver V]
    [Quiver.HasInvolutiveReverse V] {a b : V} {u v w : Quiver.Path a b} (hw : w.IsReduced)
    (h1 : u.ReducesTo w) (h2 : u.ReducesTo v) : v.ReducesTo w := by
  obtain ⟨z, hvz, hwz⟩ := reducesTo_join_aux u.length u le_rfl v w h2 h1
  -- `w` is a normal form for `DeleteBacktrack`, so the only reduct of `w` is `w` itself.
  have hzw : z = w := by
    rcases Relation.ReflTransGen.cases_head hwz with h | ⟨y, hy, _⟩
    · exact h.symm
    · exact absurd hy (hw y)
  subst hzw
  exact hvz

end Work.ORBassSerre.Path.Reduction
