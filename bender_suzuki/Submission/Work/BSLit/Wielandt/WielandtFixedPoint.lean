import Mathlib
import Submission.Work.BSLit.Defs
import Submission.Work.BSLit.Wielandt.wielandtFixedPoint_of_solvable
import Submission.Work.GlaubermanZJ.Main
import Submission.Work.ThompsonFrobenius.isNilpotent_of_fpf_pow

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.BSLit.WielandtFixedPoint`

Wielandt's fixed-point formula in the form used by Peterfalvi II Ch. V §3 step (4)
(`Work.ThmF.WielandtFixedPoint`, `Submission/Work/ThmF/Tools/External.lean`):

```
∀ (Q) [Group Q] [Finite Q] (p) [p.Prime] (K P : Subgroup (MulAut Q)),
  (|K| * |P|, |Q|) = 1 → K fpf on Q → C_Q(K) = 1 → |P| = p →
  P normalises K → (∀ k ∈ K, k ≠ 1 → P ⊓ P ^ k = ⊥) →
  |Q| = |C_Q(P)| ^ p
```

The proof reduces to `Work.BSLit.wielandtFixedPoint_of_solvable` (the same statement with an extra
`Group.IsSolvable Q`), and obtains solvability of `Q` from **Thompson's theorem**
(`Work.ThompsonFrobenius.isNilpotent_of_fpf_pow`, delivered): if `K ≠ ⊥` then any element of `K` of
prime order `r` is a fixed-point-free automorphism of prime order with `r ∤ |Q|`, so `Q` is
nilpotent.  That theorem is the only place where the area needs `hFT : FeitThompsonProp` (through
`Work.GlaubermanZJ.GlaubermanZJ hFT`), which is why the final statement carries `hFT` as an
argument, exactly like every other area of the blueprint.
-/

set_option autoImplicit false

namespace Work.BSLit

open Classical

/-- **Wielandt's fixed-point formula** (`Work.ThmF.WielandtFixedPoint`). -/
theorem WielandtFixedPoint (hFT : Submission.Blueprint.FeitThompsonProp) :
    Work.ThmF.WielandtFixedPoint := by
  intro Q _ _ p hp K P hcop hfpf hCK hcardP hPK hTI
  classical
  by_cases hK : K = ⊥
  · -- `K = ⊥`: `Q` is trivial, hence solvable, and the solvable case applies
    subst hK
    have htriv : ∀ q : Q, q = 1 := fun q =>
      hCK q fun k hk => by
        have hk1 : k = (1 : MulAut Q) := Subgroup.mem_bot.mp hk
        simpa using congrArg (fun f : MulAut Q => f q) hk1
    haveI : Subsingleton Q := ⟨fun a b => by rw [htriv a, htriv b]⟩
    haveI : Group.IsSolvable Q := ⟨0, Subsingleton.elim _ _⟩
    exact Work.BSLit.Wielandt.wielandtFixedPoint_of_solvable hp ⊥ P inferInstance hcop hCK
      hcardP hPK hTI
  · -- `K ≠ ⊥`: an element of `K` of prime order is a fixed-point-free automorphism of prime
    -- order coprime to `|Q|`, so Thompson's theorem makes `Q` nilpotent
    obtain ⟨x, hxK, hxne⟩ : ∃ x ∈ K, x ≠ 1 := by
      by_contra h
      apply hK
      rw [eq_bot_iff]
      intro y hy
      by_contra hy1
      exact h ⟨y, hy, hy1⟩
    have hxord : orderOf x ≠ 1 := fun h => hxne (orderOf_eq_one_iff.mp h)
    obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd hxord
    have hxpos : orderOf x ≠ 0 := (isOfFinOrder_of_finite x).orderOf_pos.ne'
    set α : MulAut Q := x ^ (orderOf x / r) with hαdef
    have hαord : orderOf α = r := by
      rw [hαdef]
      exact orderOf_pow_orderOf_div hxpos hrdvd
    have hαmem : α ∈ K := K.pow_mem hxK _
    have hαne : α ≠ 1 := by
      intro h
      exact hr.ne_one (by rw [← hαord, h, orderOf_one])
    have hαfpf : ∀ q : Q, α q = q → q = 1 := fun q hq => hfpf α hαmem hαne q hq
    have hnil : Group.IsNilpotent Q :=
      Work.ThompsonFrobenius.isNilpotent_of_fpf_pow (Work.GlaubermanZJ.GlaubermanZJ hFT)
        (Nat.card Q) Q rfl α r hr (by rw [← hαord]; exact pow_orderOf_eq_one α) hαfpf
    haveI := hnil
    exact Work.BSLit.Wielandt.wielandtFixedPoint_of_solvable hp K P inferInstance hcop hCK
      hcardP hPK hTI

end Work.BSLit
