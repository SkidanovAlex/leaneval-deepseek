import Mathlib
import Submission.Work.Coprime.thompson_PxQ
import Submission.Work.Coprime.Internal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `centralizer_of_fixed` — Thompson's `P × Q` lemma in internal (subgroup) form

`S` is a `q`-group, `R` a `q`-subgroup and `Q` a `q'`-subgroup of a finite group `G`, both
normalising `S`, with `R` and `Q` commuting elementwise.  If every element of `S` fixed by `R`
(i.e. the `R`-fixed points `C_S(R)`) is fixed by `Q`, then `Q` centralises `S`.

This is Thompson's `P × Q` lemma (`Work.Coprime.thompson_PxQ`) applied to the conjugation
actions of `R` and `Q` on `S`.  Those two actions commute precisely because `R` and `Q` commute
elementwise (`hc`); the hypothesis `hfix` is exactly the abstract fixed-point condition, and the
conclusion is translated back from an abstract `IsTrivialOn` statement through
`FT.isTrivialOn_conjAction_iff`.
-/

set_option linter.style.haveILetI false

open scoped Pointwise

namespace Work.NormalComplement.NC4

theorem centralizer_of_fixed {G : Type} [Group G] [Finite G]
    {S R Q : Subgroup G} {q : ℕ} (hq : q.Prime)
    (hRS : R ≤ Subgroup.normalizer (S : Set G)) (hQS : Q ≤ Subgroup.normalizer (S : Set G))
    (hc : ∀ r ∈ R, ∀ x ∈ Q, r * x = x * r)
    (hRp : IsPGroup q R) (hQndvd : ¬ q ∣ Nat.card Q) (hSp : IsPGroup q S)
    (hcop : Nat.Coprime (Nat.card Q) (Nat.card S))
    (hfix : ∀ y ∈ S, (∀ r ∈ R, r * y * r⁻¹ = y) → ∀ x ∈ Q, x * y * x⁻¹ = y) :
    ∀ x ∈ Q, ∀ y ∈ S, x * y * x⁻¹ = y := by
  haveI : FT.Normalizes R S := ⟨hRS⟩
  haveI : FT.Normalizes Q S := ⟨hQS⟩
  -- The conjugation actions of `R` and `Q` on `S` commute, using `hc` (they commute
  -- elementwise).
  haveI : SMulCommClass R Q S := ⟨fun r x y => by
    refine Subtype.ext ?_
    have hrx : (r : G) * (x : G) = (x : G) * (r : G) := hc r r.2 x x.2
    have h1 : (r : G) * (x : G) * (r : G)⁻¹ = (x : G) := by rw [hrx]; group
    have h2 : (r : G) * (x : G)⁻¹ * (r : G)⁻¹ = (x : G)⁻¹ := by
      have hh : ((r : G) * (x : G) * (r : G)⁻¹)⁻¹ = ((r : G) * (x : G)⁻¹ * (r : G)⁻¹) := by
        group
      rw [h1] at hh
      exact hh.symm
    simp only [FT.conj_smul_coe]
    calc (r : G) * ((x : G) * (y : G) * (x : G)⁻¹) * (r : G)⁻¹
        = ((r : G) * (x : G) * (r : G)⁻¹) * ((r : G) * (y : G) * (r : G)⁻¹)
            * ((r : G) * (x : G)⁻¹ * (r : G)⁻¹) := by group
      _ = (x : G) * ((r : G) * (y : G) * (r : G)⁻¹) * (x : G)⁻¹ := by rw [h1, h2]⟩
  -- Thompson's `P × Q` lemma with `P = R`, `Q = Q`, `G = S`.
  have htriv : FT.IsTrivialOn Q S :=
    Work.Coprime.thompson_PxQ q hq hRp hQndvd hSp hcop (fun x y hy => by
      refine Subtype.ext ?_
      have hy' : ∀ r ∈ R, r * (y : G) * r⁻¹ = (y : G) := by
        intro r hr
        have := congrArg (Subtype.val) (hy ⟨r, hr⟩)
        simpa [FT.conj_smul_coe] using this
      have := hfix (y : G) y.2 hy' (x : G) x.2
      simpa [FT.conj_smul_coe] using this)
  intro x hx y hy
  have hcomm : x * y = y * x := (FT.isTrivialOn_conjAction_iff Q S).mp htriv x hx y hy
  rw [hcomm]; group

end Work.NormalComplement.NC4
