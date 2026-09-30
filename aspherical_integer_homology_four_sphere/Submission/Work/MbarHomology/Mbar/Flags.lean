/-
# Flags of `Q̄`, their barycentres, and the orbit relation

**Work package W4** of `Submission/Work/NOTES_LEAD_eA.md` (the definitions the `Δ`-complex of `M̄`
is built from).

The `k`-simplices of the barycentric subdivision of `Q̄₀ ⊔ Q̄₁` are the pairs `(c, s)` where
`c : ZMod 2` is the copy and `s` is a strictly increasing `(k+1)`-tuple of faces of `Q̄` (a
`Work.Subdivision.Simplex QbarCW.Cell k`, i.e. a flag of `Q̄`).  The identification relation of `M̄`
acts on such a pair at the barycentre `bary s` of the flag, and this file sets up

* `FlagQ k` — the type of pairs `(c, s)`;
* `bary s` — the barycentre of the flag `s` in `Q̄` (`(k+1)⁻¹ • Σ_i posR (s i)`);
* `flagRel` — the relation `(c, s) ~ (c', s')` induced by `FoldInst.rel` at the barycentres,
  written directly in terms of `FoldInst.Ksub` at the point `bary s` (so that no membership proof
  in the subtype `Q̄` is needed);
* `flagSetoid k` — the same relation as an equivalence relation, whence the `Δ`-complex
  `mbarSd` (`Submission/Work/MbarHomology/Mbar/Sd.lean`) has
  `card k = Fintype.card (Quotient (flagSetoid k))`.

The relation is the one used in the design note: `(c,s) ≈ (c',s')` iff there is `γ ∈ Ksub (bary s)`
with `c' = c + γ₂` and `bary s' = act γ₁ (bary s)`.
-/
import Mathlib
import Submission.Work.Subdivision.OrderComplex
import Submission.Work.FoldInst.Atlas
import Submission.Work.MbarHomology.Qbar.Act

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option autoImplicit false

namespace Work.MbarHomology

open Work.Subdivision Work.ConvexCells
open scoped BigOperators

noncomputable section

/-- The flags of `Q̄` in dimension `k`, in one copy of the double cover: a copy bit and a
`k`-simplex of the order complex of the face poset of `Q̄`. -/
abbrev FlagQ (k : ℕ) : Type := ZMod 2 × Simplex QbarCW.Cell k

/-- The barycentre of a flag of `Q̄`. -/
def bary {k : ℕ} (s : Simplex QbarCW.Cell k) : E 4 :=
  ∑ i : Fin (k + 1), ((k + 1 : ℝ))⁻¹ • QbarPD.posR (s i).idx

/-- The identification relation on flags, at their barycentres: `γ ∈ Ksub (bary s)` moves the
flag, and the copy bit is changed by the second component of `γ`. -/
def flagRel {k : ℕ} (x y : FlagQ k) : Prop :=
  ∃ γ : Work.FoldInst.Gg, γ ∈ Work.FoldInst.Ksub (bary x.2) ∧
    y.1 = x.1 + γ.2 ∧ bary y.2 = Work.FoldInst.act γ.1 (bary x.2)

theorem flagRel_refl {k : ℕ} (x : FlagQ k) : flagRel x x :=
  ⟨0, (Work.FoldInst.Ksub (bary x.2)).zero_mem, by simp,
    by show bary x.2 = Work.FoldInst.act (0 : Fin 4 → ZMod 2) (bary x.2)
       rw [Work.FoldInst.act_zero]⟩

theorem flagRel_symm {k : ℕ} {x y : FlagQ k} (h : flagRel x y) : flagRel y x := by
  obtain ⟨γ, hγ, h1, h2⟩ := h
  refine ⟨γ, ?_, ?_, ?_⟩
  · rw [h2, Work.FoldInst.Ksub_act]; exact hγ
  · rw [h1, add_assoc, Work.FoldInst.ZMod2_add_self, add_zero]
  · have hgg : γ.1 + γ.1 = 0 := congrArg Prod.fst (Work.FoldInst.Gg_add_self γ)
    rw [h2, Work.FoldInst.act_add, hgg, Work.FoldInst.act_zero]

theorem flagRel_trans {k : ℕ} {x y z : FlagQ k} (h1 : flagRel x y) (h2 : flagRel y z) :
    flagRel x z := by
  obtain ⟨γ, hγ, hy1, hy2⟩ := h1
  obtain ⟨η, hη, hz1, hz2⟩ := h2
  refine ⟨η + γ, ?_, ?_, ?_⟩
  · have hyx : Work.FoldInst.Ksub (bary y.2) = Work.FoldInst.Ksub (bary x.2) := by
      rw [hy2, Work.FoldInst.Ksub_act]
    rw [← hyx] at hγ ⊢
    exact AddSubgroup.add_mem _ hη hγ
  · rw [hz1, hy1, add_assoc, add_comm γ.2 η.2]
    rfl
  · rw [hz2, hy2, Work.FoldInst.act_add]
    rfl

/-- **The orbit relation on the flags of `Q̄`**, as an equivalence relation: the `k`-simplices of
the barycentric subdivision of `M̄` are its classes. -/
def flagSetoid (k : ℕ) : Setoid (FlagQ k) where
  r := flagRel
  iseqv := ⟨fun x => flagRel_refl x, fun h => flagRel_symm h, fun h1 h2 => flagRel_trans h1 h2⟩

end

end Work.MbarHomology
