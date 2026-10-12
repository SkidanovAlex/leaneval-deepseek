import Mathlib.Algebra.Algebra.Basic
import Mathlib.Data.Finsupp.SMul
import Mathlib.Data.Real.Basic
import Submission.Work.BoseB4.Ann_ann_comm
import Submission.Work.BoseB4.ModeFock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.AnnOf_ann_comm` — superposed annihilations commute

`annOf m f = Σ_l f_l · ∂/∂x_l` is a linear combination of the coordinate
annihilations `ann m l`, which commute by `Work.BoseB4.Ann_ann_comm`.  The
endomorphisms of `RealFock m` form a real algebra with pointwise scalar
multiplication, and `Commute` is stable under finite sums and scalar multiples
(`Commute.sum_left`, `Commute.sum_right`, `Commute.smul_left`,
`Commute.smul_right`), so the two superpositions commute.
-/

namespace Work.BoseB4

/-- Superposed annihilations commute: `[a(f), a(g)] = 0`. -/
theorem AnnOf_ann_comm {m : ℕ} (f g : Fin m → ℝ) :
    (Work.BoseB4.annOf m f).comp (Work.BoseB4.annOf m g)
      = (Work.BoseB4.annOf m g).comp (Work.BoseB4.annOf m f) := by
  -- `*` on `Module.End` is `comp`, so work with the ring structure (`Commute`).
  change (annOf m f) * (annOf m g) = (annOf m g) * (annOf m f)
  -- The coordinate annihilations commute.
  have hcomm : ∀ l l' : Fin m, Commute (ann m l) (ann m l') :=
    fun l l' => Ann_ann_comm l l'
  -- `annOf m f` commutes with each coordinate annihilation.
  have h1 : ∀ l' : Fin m,
      Commute (∑ l : Fin m, f l • ann m l) (ann m l') := fun l' =>
    Commute.sum_left Finset.univ (fun l : Fin m => f l • ann m l) (ann m l')
      (fun l _ => (hcomm l l').smul_left (f l))
  -- Hence `annOf m f` commutes with the superposition `annOf m g`.
  have h2 : Commute (∑ l : Fin m, f l • ann m l)
      (∑ l' : Fin m, g l' • ann m l') :=
    Commute.sum_right Finset.univ (fun l' : Fin m => g l' • ann m l')
      (∑ l : Fin m, f l • ann m l)
      (fun l' _ => (h1 l').smul_right (g l'))
  simpa only [annOf] using h2.eq

end Work.BoseB4
