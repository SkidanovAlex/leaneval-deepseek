import Mathlib
import Submission.Work.ORHughesFree.Prop51.ConclB
import Submission.Work.ORHughesFree.Prop51.conj
import Submission.Work.ORHughesFree.Prop51.treeH_coeffToP_mul_ofAdd_le

namespace Work.ORHughesFree.Prop51

/-- Strict version of the per-summand complexity bound at the level of `dlog`: if the `dlog` of
both factors is strictly below `some A` resp. `some B`, then the `dlog` of the summand
`f.1 k * (τ^k (g.1 (n - k)))` of the skew convolution product is strictly below `some (A + B)`.
(Use that `treeH` of the summand is at most the product of the `treeH`s of the factors, then
`ole_dlog_mul`, which bounds `dlog (x * y)` by `oadd (dlog x) (dlog y)`, and `olt_oadd_some`.) -/
theorem olt_dlog_coeffToP_mul_ofAdd {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Work.ORHughesFree.Prop51Data Γ P DN)
    (f g : Work.ORHughesFree.SkewLaurentSeries ↥DN) (n k : ℤ) {A B : Work.ORHughesFree.Tree}
    (hf : Work.ORHughesFree.Tree.Olt
      (Work.ORHughesFree.Tree.dlog (d.treeH (d.coeffToP (f.1 k)))) (some A))
    (hg : Work.ORHughesFree.Tree.Olt
      (Work.ORHughesFree.Tree.dlog (d.treeH (d.coeffToP (g.1 (n - k))))) (some B)) :
    Work.ORHughesFree.Tree.Olt
      (Work.ORHughesFree.Tree.dlog
        (d.treeH (d.coeffToP (f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k))))))
      (some (A + B)) := by
  -- The complexity of the summand is at most the product of the two coefficients' complexities.
  have hle := treeH_coeffToP_mul_ofAdd_le d f g n k
  -- Hence the same holds after taking `dlog`.
  have h1 : Work.ORHughesFree.Tree.Ole
      (Work.ORHughesFree.Tree.dlog
        (d.treeH (d.coeffToP (f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k))))))
      (Work.ORHughesFree.Tree.dlog
        (d.treeH (d.coeffToP (f.1 k)) * d.treeH (d.coeffToP (g.1 (n - k))))) :=
    Work.ORHughesFree.Tree.ole_dlog_of_le hle
  -- `dlog` of a product of trees is at most the `oadd` of the `dlog`s.
  have h2 := Work.ORHughesFree.Tree.ole_dlog_mul
    (d.treeH (d.coeffToP (f.1 k))) (d.treeH (d.coeffToP (g.1 (n - k))))
  have h3 := Work.ORHughesFree.Tree.ole_trans h1 h2
  -- At least one factor has `dlog` *strictly* below its bound, so `olt_oadd_some` applies.
  have hne : ¬ (Work.ORHughesFree.Tree.dlog (d.treeH (d.coeffToP (f.1 k))) = some A ∧
      Work.ORHughesFree.Tree.dlog (d.treeH (d.coeffToP (g.1 (n - k)))) = some B) := by
    rintro ⟨hA, _⟩
    exact hf.2 (by rw [hA]; exact Work.ORHughesFree.Tree.ole_refl (some A))
  exact Work.ORHughesFree.Tree.ole_olt_trans h3
    (Work.ORHughesFree.Tree.olt_oadd_some hf.1 hg.1 hne)

end Work.ORHughesFree.Prop51
