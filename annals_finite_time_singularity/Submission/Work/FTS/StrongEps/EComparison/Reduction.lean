/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EComparison/Reduction.lean`

The reduction that isolates the **single missing input** of `EpsLocal`: the free operator `E` of
the `ε`-scheme `IsEpsSol α ρ ε T Φs E g₀ g` is constrained by `hEll` only through the *elliptic
packages* `EllPkgGo`/`EllPkgK` on the class `Work.FTS.ClassC.ClassC`, and those packages give
*absolute* bounds for `E u` in terms of `u`.  The scheme needs a **difference** bound.

**What the packages see.**  The nonlinear layer consumes the stream function only through the three
*slots*

```
SlotR α F Ψ = Rop α (PhiTil α F Ψ),
SlotU α F Ψ = Uop α (PhiTil α F Ψ) / sin 2θ,
SlotV α F Ψ = Vop (PhiTil α F Ψ),
```

because `Construction.N α F Φ = 2·Rop α (PhiTil α F Φ)·F - 2·Uop α (PhiTil α F Φ)·∂_θF
- 2α·Vop (PhiTil α F Φ)·D_zF - …` (and `muDyn` uses `N` only).  So the whole right-hand side of the
scheme is a function of `(J_ε (slice g τ), Slots of E at J_ε (slice g τ))`.

**The refuted route.**  If the elliptic problem had at most one solution in the packages' class, then
`E u - E v = E (u - v)` and the packages applied to the *difference* profile `u - v` (which is again
in `ClassC`, that class being a subspace) would give the slot bounds.  That uniqueness is **false**:
`EComparison.HomClsZeroRefute.exists_counterexample`
(`Submission/Work/FTS/StrongEps/EComparison/HomClsZeroRefute.lean`, `sorry`-free) exhibits the
homogeneous mode `z^{-3/α} / cos θ`, whose three slots vanish identically (`α·(-3/α) + 3 = 0` is the
proportionality constant of all three), so the packages are blind to it.

**The surviving route, and the input it needs.**  Since the right-hand side only sees the slots, the
`Ψ`-uniqueness is not needed: what is needed is that the **slots depend only on the source**,
i.e. that every homogeneous element of the packages' class has *vanishing* slots
(`EComparison.HomClsSlotsZero`, delegated; its conclusion is deliberately restricted to the open
quadrant, the hypotheses constraining nothing outside it).  With that, and with the class closed
under differences, `E u - E v` and `E (u - v)` — both solutions with source `u - v`, both in the
class — have equal slots, and the packages evaluated at the difference profile supply the Lipschitz
slot bounds the Picard estimate consumes.

The closure of `EllPkgCls` under differences (used to put `E u - E v` in the class) is
`EComparison.EllPkgCls_sub`; its two analytic inputs are `EComparison.L12_sub_HkMem` (the `L₁₂`
additivity that makes `Theta` linear in the source) and the pointwise additivity of
`Rop`/`Uop`/`Vop`.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring.RingNF
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.ClassC.A1
import Submission.Work.Elliptic.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.StrongEps.EComparison

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-! ## The class the `hEll` packages control -/

/-- **The membership half of the two elliptic packages.**  `EllPkgCls α Ce F Ψ` records exactly the
*structural* content of `EllPkgGo α Ce F Ψ ∧ EllPkgK α _ Ce F Ψ`:
`Ψ` is `C^∞` on the open quadrant, solves the elliptic law with source `F` (Dirichlet data and
`z`-decay), and the three modulation outputs `Rop α (PhiTil α F Ψ)`, `Uop α (PhiTil α F Ψ) / sin 2θ`,
`Vop (PhiTil α F Ψ)` are of class `HQo α 6` — i.e. `C^∞` on the open quadrant *and* of honest
weighted `ℋ⁶`-size, which is exactly the slot shape of `EllPkgGo`/`EllPkgK`.

The *numeric* clauses of the packages (`Xn _ ≤ Ce * Xn _`, `HkNorm _ ≤ Ce * HkNorm _`) are
deliberately absent: they are not closed under taking differences (the constant doubles), while
every consumer of the reduction re-derives its bound from the packages at the *difference* profile. -/
def EllPkgCls (α Ce : ℝ) (F Ψ : Fn) : Prop :=
  Work.FTS.EllipticEst.SmoothOpen Ψ ∧ Work.Elliptic.IsBslSol α F Ψ ∧
    Work.FTS.VocabO.HQo α 6 (Work.Construction.Rop α (Work.Construction.PhiTil α F Ψ)) ∧
    Work.FTS.VocabO.HQo α 6 (fun z θ =>
      Work.Construction.Uop α (Work.Construction.PhiTil α F Ψ) z θ / Work.Construction.s2 θ) ∧
    Work.FTS.VocabO.HQo α 6 (Work.Construction.Vop (Work.Construction.PhiTil α F Ψ))

/-- **The three slots** through which the packages — and the scheme's right-hand side — see the
stream function.  `SlotR α F Ψ` is the `R`-slot, `SlotU α F Ψ` the `U`-slot *with the `1 / sin 2θ`
already divided in* (the shape in which `EllPkgK` bounds it), and `SlotV α F Ψ` the `V`-slot. -/
def SlotR (α : ℝ) (F Ψ : Fn) : Fn :=
  Work.Construction.Rop α (Work.Construction.PhiTil α F Ψ)

/-- The `U`-slot of the packages. -/
def SlotU (α : ℝ) (F Ψ : Fn) : Fn := fun z θ =>
  Work.Construction.Uop α (Work.Construction.PhiTil α F Ψ) z θ / Work.Construction.s2 θ

/-- The `V`-slot of the packages. -/
def SlotV (α : ℝ) (F Ψ : Fn) : Fn :=
  Work.Construction.Vop (Work.Construction.PhiTil α F Ψ)

/-- **The packages give the class.**  For every `u` of the elliptic source class `ClassC`, `hEll`
supplies `EllPkgGo α Ce u (E u)` (the elliptic law `IsBslSol α u (E u)` and the open-quadrant
smoothness) and `EllPkgK α 6 Ce u (E u)` (which carries the three `HQo α 6` slots). -/
theorem EllPkgCls_of_pkg {α Ce : ℝ} {E : Fn → Fn}
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {u : Fn} (hu : Work.FTS.ClassC.ClassC α u) : EllPkgCls α Ce u (E u) :=
  ⟨(hEll u hu).1.smooth, (hEll u hu).1.sol, (hEll u hu).2.R.1, (hEll u hu).2.U.1,
    (hEll u hu).2.V.1⟩

/-- **`ClassC` is a subspace: it is closed under subtraction.**  (`classC_add` +
`classC_smul` with `c = -1`.)  This is what lets the reduction put the *difference* profile
`u - v` in the class, i.e. apply `hEll` to it. -/
theorem classC_sub {α : ℝ} {u v : Fn} (hu : Work.FTS.ClassC.ClassC α u)
    (hv : Work.FTS.ClassC.ClassC α v) :
    Work.FTS.ClassC.ClassC α (fun z θ => u z θ - v z θ) := by
  have h : (fun z θ => u z θ - v z θ) = u + (-1 : ℝ) • v := by
    funext z θ
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [h]
  exact Work.FTS.ClassC.classC_add hu (Work.FTS.ClassC.classC_smul (-1) hv)

/-! ## The reduction -/

/-- **The reduction, in its surviving form.**  `hslot` is the (delegated, and now the *only* missing
ingredient) statement that the three slots depend only on the source — the content of
`EComparison.HomClsSlotsZero` after the closure `EComparison.EllPkgCls_sub`.  Then two elements of
the class with the same source have the same slots. -/
theorem Slots_eq_of_source_eq {α Ce : ℝ} {F Ψ₁ Ψ₂ : Fn}
    (hslot : ∀ G Φ₁ Φ₂ : Fn, EllPkgCls α Ce G Φ₁ → EllPkgCls α Ce G Φ₂ →
      SlotR α G Φ₁ = SlotR α G Φ₂ ∧ SlotU α G Φ₁ = SlotU α G Φ₂ ∧ SlotV α G Φ₁ = SlotV α G Φ₂)
    (h₁ : EllPkgCls α Ce F Ψ₁) (h₂ : EllPkgCls α Ce F Ψ₂) :
    SlotR α F Ψ₁ = SlotR α F Ψ₂ ∧ SlotU α F Ψ₁ = SlotU α F Ψ₂ ∧ SlotV α F Ψ₁ = SlotV α F Ψ₂ :=
  hslot F Ψ₁ Ψ₂ h₁ h₂

/-- **The slot comparison for the `E`-difference at a single source.**  This is the exact form the
Picard estimate consumes: the slot of `E u - E v` over the source `u - v`, identified with the slot
of `E (u - v)` — the latter being available because `hEll` applies to the difference profile
`u - v` (`ClassC` being a subspace), the former lying in the class by
`EComparison.EllPkgCls_sub`. -/
theorem E_slots_diff_eq {α Ce : ℝ} {E : Fn → Fn}
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hslot : ∀ G Φ₁ Φ₂ : Fn, EllPkgCls α Ce G Φ₁ → EllPkgCls α Ce G Φ₂ →
      SlotR α G Φ₁ = SlotR α G Φ₂ ∧ SlotU α G Φ₁ = SlotU α G Φ₂ ∧ SlotV α G Φ₁ = SlotV α G Φ₂)
    {u v : Fn} (huv : Work.FTS.ClassC.ClassC α (fun z θ => u z θ - v z θ))
    (hsub : EllPkgCls α Ce (fun z θ => u z θ - v z θ) (fun z θ => E u z θ - E v z θ)) :
    SlotR α (fun z θ => u z θ - v z θ) (fun z θ => E u z θ - E v z θ)
        = SlotR α (fun z θ => u z θ - v z θ) (E (fun z θ => u z θ - v z θ))
      ∧ SlotU α (fun z θ => u z θ - v z θ) (fun z θ => E u z θ - E v z θ)
        = SlotU α (fun z θ => u z θ - v z θ) (E (fun z θ => u z θ - v z θ))
      ∧ SlotV α (fun z θ => u z θ - v z θ) (fun z θ => E u z θ - E v z θ)
        = SlotV α (fun z θ => u z θ - v z θ) (E (fun z θ => u z θ - v z θ)) :=
  hslot (fun z θ => u z θ - v z θ) _ _ hsub (EllPkgCls_of_pkg hEll huv)

/-! ## What the reduction buys: the Lipschitz input of the Picard estimate -/

/-- **The `R`-slot Lipschitz input.**  With the slot identity in hand, the packages applied to the
difference profile give the estimate the Picard argument needs:
`HkNorm α 6 (SlotR α (u - v) (E u - E v)) ≤ Ce * HkNorm α 6 (u - v)`.  The `U`- and `V`-slots are
identical (`EllPkgK_U_diff_le`, `EllPkgK_V_diff_le`). -/
theorem EllPkgK_R_diff_le {α Ce : ℝ} {E : Fn → Fn}
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {u v : Fn} (huv : Work.FTS.ClassC.ClassC α (fun z θ => u z θ - v z θ))
    (hslot : SlotR α (fun z θ => u z θ - v z θ) (fun z θ => E u z θ - E v z θ)
        = SlotR α (fun z θ => u z θ - v z θ) (E (fun z θ => u z θ - v z θ))) :
    Work.Spaces.HkNorm α 6 (SlotR α (fun z θ => u z θ - v z θ) (fun z θ => E u z θ - E v z θ))
      ≤ Ce * Work.Spaces.HkNorm α 6 (fun z θ => u z θ - v z θ) := by
  have h := ((hEll (fun z θ => u z θ - v z θ) huv).2.R).2
  rw [hslot]
  exact h

/-- **The `U`-slot Lipschitz input** (companion of `EllPkgK_R_diff_le`). -/
theorem EllPkgK_U_diff_le {α Ce : ℝ} {E : Fn → Fn}
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {u v : Fn} (huv : Work.FTS.ClassC.ClassC α (fun z θ => u z θ - v z θ))
    (hslot : SlotU α (fun z θ => u z θ - v z θ) (fun z θ => E u z θ - E v z θ)
        = SlotU α (fun z θ => u z θ - v z θ) (E (fun z θ => u z θ - v z θ))) :
    Work.Spaces.HkNorm α 6 (SlotU α (fun z θ => u z θ - v z θ) (fun z θ => E u z θ - E v z θ))
      ≤ Ce * Work.Spaces.HkNorm α 6 (fun z θ => u z θ - v z θ) := by
  have h := ((hEll (fun z θ => u z θ - v z θ) huv).2.U).2
  rw [hslot]
  exact h

/-- **The `V`-slot Lipschitz input** (companion of `EllPkgK_R_diff_le`). -/
theorem EllPkgK_V_diff_le {α Ce : ℝ} {E : Fn → Fn}
    (hEll : ∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    {u v : Fn} (huv : Work.FTS.ClassC.ClassC α (fun z θ => u z θ - v z θ))
    (hslot : SlotV α (fun z θ => u z θ - v z θ) (fun z θ => E u z θ - E v z θ)
        = SlotV α (fun z θ => u z θ - v z θ) (E (fun z θ => u z θ - v z θ))) :
    Work.Spaces.HkNorm α 6 (SlotV α (fun z θ => u z θ - v z θ) (fun z θ => E u z θ - E v z θ))
      ≤ Ce * Work.Spaces.HkNorm α 6 (fun z θ => u z θ - v z θ) := by
  have h := ((hEll (fun z θ => u z θ - v z θ) huv).2.V).2
  rw [hslot]
  exact h

end Work.FTS.StrongEps.EComparison
