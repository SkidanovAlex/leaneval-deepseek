import Mathlib
import Submission.Work.ORHughesFree.Prop51.ConclB
import Submission.Work.ORHughesFree.Prop51.conj

namespace Work.ORHughesFree.Prop51

/-- The complexity of one summand `f.1 k * (τ^k (g.1 (n - k)))` of the skew convolution product
is bounded by the product of the complexities of the two factors.  (This is `treeH_le_mul`
together with the fact that conjugation by `Φ (t^k)` preserves the complexity, `treeH_conj_eq`,
and `conj`.) -/
theorem treeH_coeffToP_mul_ofAdd_le {Γ : Type} [Group Γ] {P : Type} [Ring P] {DN : Subring P}
    [MulSemiringAction (Multiplicative ℤ) ↥DN] (d : Work.ORHughesFree.Prop51Data Γ P DN)
    (f g : Work.ORHughesFree.SkewLaurentSeries ↥DN) (n k : ℤ) :
    Work.ORHughesFree.Tree.le
      (d.treeH (d.coeffToP (f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k)))))
      (d.treeH (d.coeffToP (f.1 k)) * d.treeH (d.coeffToP (g.1 (n - k)))) := by
  -- `coeffToP` is the inclusion `D_{N,P} ⊆ P`, hence multiplicative.
  have hcoe : d.coeffToP (f.1 k * ((Multiplicative.ofAdd k) • g.1 (n - k)))
      = d.coeffToP (f.1 k) * d.coeffToP ((Multiplicative.ofAdd k) • g.1 (n - k)) := rfl
  -- Rewrite the conjugated coefficient in `P` using the relation `tᵏ a t⁻ᵏ = τᵏ a` of `conj`.
  rw [hcoe, conj d k (g.1 (n - k))]
  have ht : d.Φ (Work.ORHughesFree.RatU.ofGroup (d.t ^ k)) ∈ d.DH := d.map_mem _
  have htn : d.Φ (Work.ORHughesFree.RatU.ofGroup (d.t ^ (-k))) ∈ d.DH := d.map_mem _
  have hf : d.coeffToP (f.1 k) ∈ d.DH := d.coeffToP_mem _
  have hg : d.coeffToP (g.1 (n - k)) ∈ d.DH := d.coeffToP_mem _
  -- The conjugated factor `Φ(tᵏ) · a · Φ(t⁻ᵏ)` has complexity at most that of `a`: both
  -- conjugating elements are units of complexity one (`treeH_ofGroup`).
  have hinner : Work.ORHughesFree.Tree.le
      (d.treeH (d.Φ (Work.ORHughesFree.RatU.ofGroup (d.t ^ k)) * d.coeffToP (g.1 (n - k)) *
        d.Φ (Work.ORHughesFree.RatU.ofGroup (d.t ^ (-k)))))
      (d.treeH (d.coeffToP (g.1 (n - k)))) := by
    have h1 : Work.ORHughesFree.Tree.le
        (d.treeH (d.Φ (Work.ORHughesFree.RatU.ofGroup (d.t ^ k)) * d.coeffToP (g.1 (n - k)) *
          d.Φ (Work.ORHughesFree.RatU.ofGroup (d.t ^ (-k)))))
        (d.treeH (d.Φ (Work.ORHughesFree.RatU.ofGroup (d.t ^ k)) * d.coeffToP (g.1 (n - k)))) := by
      have h := treeH_le_mul d (d.DH.mul_mem ht hg) htn
      rw [treeH_ofGroup d (d.t ^ (-k)), mul_one] at h
      exact h
    have h2 : Work.ORHughesFree.Tree.le
        (d.treeH (d.Φ (Work.ORHughesFree.RatU.ofGroup (d.t ^ k)) * d.coeffToP (g.1 (n - k))))
        (d.treeH (d.coeffToP (g.1 (n - k)))) := by
      have h := treeH_le_mul d ht hg
      rw [treeH_ofGroup d (d.t ^ k), one_mul] at h
      exact h
    exact Work.ORHughesFree.Tree.le_trans h1 h2
  exact Work.ORHughesFree.Tree.le_trans
    (treeH_le_mul d hf (d.DH.mul_mem (d.DH.mul_mem ht hg) htn))
    (Work.ORHughesFree.Tree.le_mul (Work.ORHughesFree.Tree.le_refl _) hinner)

end Work.ORHughesFree.Prop51
