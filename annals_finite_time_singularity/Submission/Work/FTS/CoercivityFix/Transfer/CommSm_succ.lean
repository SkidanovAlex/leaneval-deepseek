/-
# `Transfer/CommSm_succ.lean` — the `CommSm`-package climbs one level under `HkIPStep`

`Transfer/CoreDefs.lean` fixes the algebraic package of the corrected transfer induction,

```
CommSm α n IP  =  congr  ∧  add (on AddOKSm)  ∧  dthC  ∧  dzC,
```

whose `add` clause takes the *finite-order* class `Q0Sm` (smoothness of the profile on the
**open** quadrant `Qd = (0,∞) × (0,π/2)`) together with `ℋⁿ`-membership, instead of the
analytic `RegQ`/`SmoothNbhd` of the clean operator's package (`Assembly.Comm2`).  The two
`Q0Sm`-classes are the right ones for the transfer because the defects `E1 α f`, `E2 α f`
are only finitely smooth (their `radA`, `radS` contain `L₁₂ f`, which stops at `C³`).

This file proves that the paper's recursion

```
HkIPStep c₁ c₂ IP = IP + c₁·IP(D_θ·, D_θ·) + c₂·IP(D_z·, D_z·)
```

inherits all four clauses **one level up**:

```
CommSm α n IP  →  CommSm α (n+1) (HkIPStep c₁ c₂ IP).
```

The two commutator clauses mention neither the level `n` nor the inner product (they are
statements about `Lhat` alone), so they are inherited **verbatim**.  The two pairing clauses
are transported through exactly the same two ingredients as in `Assembly.Comm2_succ`, with
`SmoothQuad` replaced by `Q0Sm`:

* the two derivative-**locality** facts on `Qd` — functions agreeing on the open quadrant
  have the same `D_θ` and `D_z` there (`Filter.EventuallyEq.deriv_eq`), because `Qd` is open
  in the relevant variable;
* the two derivative-**linearity** facts on `Qd` — `D_θ` and `D_z` are additive there for
  `C¹` summands, which is `Q0Sm.dth_add` / `Q0Sm.dz_add` (`Transfer/Q0Sm.lean`), and
  `deriv_add` needs nothing else;
* the **descent** of the hypotheses from level `n+1` to level `n`, which is what turns the
  level-`n` clauses of `IP` into the level-`(n+1)` clauses of `HkIPStep`:
  `Q0Sm (n+1) X → Q0Sm n X`, `Q0Sm n (D_θ X)`, `Q0Sm n (D_z X)` is `Q0Sm.mono`/`Q0Sm.dth`/
  `Q0Sm.dz`, and the corresponding `ℋ`-membership descent
  `HkMem α (n+1) X → HkMem α n X ∧ HkMem α n (D_θ X) ∧ HkMem α n (D_z X)` is
  `Transfer.HkMem_descent_Q0Sm` (which is exactly why that lemma is phrased for `Q0Sm`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.CoercivityFix.Transfer.CoreDefs
import Submission.Work.FTS.CoercivityFix.Transfer.Q0Sm
import Submission.Work.FTS.CoercivityFix.Transfer.HkMem_descent_Q0Sm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## Locality of the two derivatives on the open quadrant

Both facts are *pointwise on `Qd`*, which is the form in which the `congr` clause of
`CommSm` is stated.  (The corresponding helpers of `Assembly/Comm2_succ.lean` are `private`
there, hence re-proved here.) -/

/-- Two functions that agree on the open quadrant have the same `D_θ` there: the derivative
is local and `Qd` is open in the `θ`-variable. -/
private lemma Dth_congr_Qd {f f' : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dth f z θ = Work.Spaces.Dth f' z θ := by
  intro z θ hzθ
  have hz : z ∈ Set.Ioi (0 : ℝ) := hzθ.1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hzθ.2
  have heq : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => f' z θ') := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
    exact h z θ' ⟨hz, hθ'⟩
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [heq.deriv_eq]

/-- Two functions that agree on the open quadrant have the same `D_z` there. -/
private lemma Dz_congr_Qd {f f' : Fn}
    (h : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd → f z θ = f' z θ) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.Dz f z θ = Work.Spaces.Dz f' z θ := by
  intro z θ hzθ
  have hz : z ∈ Set.Ioi (0 : ℝ) := hzθ.1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hzθ.2
  have heq : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => f' z' θ) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
    exact h z' θ ⟨hz', hθ⟩
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [heq.deriv_eq]

/-! ## The induction step of the package -/

/-- **`CommSm` climbs one level under the paper's recursion `HkIPStep c₁ c₂`.**

The congruence clause is transported through the two derivative-locality facts above; the
additivity clause through the two derivative-linearity facts `Q0Sm.dth_add` /
`Q0Sm.dz_add` together with the descent `HkMem_descent_Q0Sm` (and `Q0Sm.mono`, `Q0Sm.dth`,
`Q0Sm.dz`) from level `n+1` to level `n`; the two commutator clauses are inherited
verbatim, since they mention neither `n` nor `IP`. -/
theorem CommSm_succ (α : ℝ) (hα : 0 < α) (n : ℕ)
    {IP : (ℝ → ℝ → ℝ) → (ℝ → ℝ → ℝ) → ℝ} {c₁ c₂ : ℝ}
    (h : Work.FTS.CoercivityFix.Transfer.CommSm α n IP) :
    Work.FTS.CoercivityFix.Transfer.CommSm α (n + 1)
      (Work.Coercivity.HkIPStep c₁ c₂ IP) := by
  refine ⟨?congr, ?add, h.dthC, h.dzC⟩
  case congr =>
    intro f f' g hfg
    have e0 := h.congr f f' g hfg
    have e1 := h.congr (Work.Spaces.Dth f) (Work.Spaces.Dth f') (Work.Spaces.Dth g)
      (Dth_congr_Qd hfg)
    have e2 := h.congr (Work.Spaces.Dz f) (Work.Spaces.Dz f') (Work.Spaces.Dz g)
      (Dz_congr_Qd hfg)
    simp only [Work.Coercivity.HkIPStep, e0, e1, e2]
  case add =>
    intro f₁ f₂ g hf
    obtain ⟨hf₁, hf₂, hg, hm₁, hm₂, hmg⟩ := hf
    -- the descent of both hypotheses from level `n + 1` to level `n`
    obtain ⟨hd₁, hd₁θ, hd₁z⟩ := HkMem_descent_Q0Sm α hα n hf₁ hm₁
    obtain ⟨hd₂, hd₂θ, hd₂z⟩ := HkMem_descent_Q0Sm α hα n hf₂ hm₂
    obtain ⟨hdg, hdgθ, hdgz⟩ := HkMem_descent_Q0Sm α hα n hg hmg
    have e0 := h.add f₁ f₂ g
      ⟨hf₁.mono (Nat.le_succ n), hf₂.mono (Nat.le_succ n), hg.mono (Nat.le_succ n),
        hd₁, hd₂, hdg⟩
    have e1 : IP (Work.Spaces.Dth (f₁ + f₂)) (Work.Spaces.Dth g)
        = IP (Work.Spaces.Dth f₁) (Work.Spaces.Dth g)
          + IP (Work.Spaces.Dth f₂) (Work.Spaces.Dth g) := by
      rw [h.congr (Work.Spaces.Dth (f₁ + f₂))
        (Work.Spaces.Dth f₁ + Work.Spaces.Dth f₂) (Work.Spaces.Dth g)
        (fun z θ hzθ =>
          Q0Sm.dth_add (hf₁.mono (by omega : 1 ≤ n + 1))
            (hf₂.mono (by omega : 1 ≤ n + 1)) z θ hzθ)]
      exact h.add (Work.Spaces.Dth f₁) (Work.Spaces.Dth f₂) (Work.Spaces.Dth g)
        ⟨hf₁.dth, hf₂.dth, hg.dth, hd₁θ, hd₂θ, hdgθ⟩
    have e2 : IP (Work.Spaces.Dz (f₁ + f₂)) (Work.Spaces.Dz g)
        = IP (Work.Spaces.Dz f₁) (Work.Spaces.Dz g)
          + IP (Work.Spaces.Dz f₂) (Work.Spaces.Dz g) := by
      rw [h.congr (Work.Spaces.Dz (f₁ + f₂))
        (Work.Spaces.Dz f₁ + Work.Spaces.Dz f₂) (Work.Spaces.Dz g)
        (fun z θ hzθ =>
          Q0Sm.dz_add (hf₁.mono (by omega : 1 ≤ n + 1))
            (hf₂.mono (by omega : 1 ≤ n + 1)) z θ hzθ)]
      exact h.add (Work.Spaces.Dz f₁) (Work.Spaces.Dz f₂) (Work.Spaces.Dz g)
        ⟨hf₁.dz, hf₂.dz, hg.dz, hd₁z, hd₂z, hdgz⟩
    simp only [Work.Coercivity.HkIPStep, e0, e1, e2]
    ring

end Work.FTS.CoercivityFix.Transfer
