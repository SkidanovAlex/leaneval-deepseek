import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseB4.CFock
import Submission.Work.BoseB4.Defs
import Submission.Work.BoseB4.RealFock
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.Split` — the mode lattice as `𝔉(ℂθ) ⊗ 𝔉(excited)`

The mode lattice's Fock space `Work.BoseB4.RealFock m = (Fin m →₀ ℕ) →₀ ℝ` has a
distinguished mode `0` (the condensate) and the remaining (`excited`) modes.  The
occupation index therefore splits,

    `(Fin m →₀ ℕ) ≅ ℕ × (excited m →₀ ℕ)`,   `α ↦ (α 0, α|_{j≠0})`,

which identifies the mode lattice with the abstract §8 picture
`Work.BoseB4.FockCore E = ℕ →₀ E` with `E := Work.BoseB4.cfock (excited m)`, the
**complex** Fock core of `CFock.lean`:

* `restOf α` — the excited part `α|_{j≠0}`;
* `idx n β` — the multi-index with `n` condensate quanta and excited part `β`;
* `fockW n β = √(n! β!)` — the weight making the Bombieri form of `RealFock` the
  ℓ² form of the complex side (`Work.BoseB4.split_inner`);
* `split` — the `ℝ`-linear isometry `RealFock m → FockCore (cfock (excited m))`.

Under `split`, the mode operators correspond as

* `ann m 0 ↔ a0` and `cre m 0 ↔ a0d` (the condensate);
* `ann m j ↔ lift (annC j)` and `cre m j ↔ lift (creC j)` for `j ≠ 0` (the
  spectators),

which is what lets FS `thm:Kafz` — proved in the abstract chapter for a finite
sum of anti-normal monomials `Work.BoseB4.monoOp` — be read on the mode lattice.
-/

noncomputable section

open scoped lp

namespace Work.BoseB4

set_option autoImplicit false

/-- The index type of the **excited** modes of the mode lattice (`j ≠ 0`). -/
abbrev Excited (m : ℕ) [NeZero m] := {j : Fin m // j ≠ 0}

/-- The multi-index factorial for an arbitrary index type. -/
noncomputable def mfacG {ι : Type*} (α : ι →₀ ℕ) : ℝ :=
  α.prod fun _ k => (k.factorial : ℝ)

/-- The excited part of a multi-index. -/
noncomputable def restOf {m : ℕ} [NeZero m] (α : Fin m →₀ ℕ) : Excited m →₀ ℕ :=
  Finsupp.subtypeDomain (fun j : Fin m => j ≠ 0) α

/-- The multi-index with `n` condensate quanta and excited part `β`. -/
noncomputable def idx {m : ℕ} [NeZero m] (n : ℕ) (β : Excited m →₀ ℕ) : Fin m →₀ ℕ :=
  Finsupp.single 0 n + Finsupp.embDomain ⟨Subtype.val, Subtype.val_injective⟩ β

/-- The Fock weight `√(n! · β!)` of the pair `(n, β)`. -/
noncomputable def fockW {m : ℕ} [NeZero m] (n : ℕ) (β : Excited m →₀ ℕ) : ℝ :=
  Real.sqrt ((n.factorial : ℝ) * mfacG β)

/-- **The mode-lattice ⟨condensate | excited⟩ split**: the `ℝ`-linear map sending a
mode-lattice state to the corresponding `ℕ →₀ cfock (excited m)`, i.e. to
`Σ_α p_α √(α 0)! (α|_{j≠0})! · e_{α 0} ⊗ |α|_{j≠0}⟩`. -/
noncomputable def split {m : ℕ} [NeZero m] : RealFock m →ₗ[ℝ] (ℕ →₀ cfock (Excited m)) :=
  Finsupp.lsum ℝ fun α : Fin m →₀ ℕ =>
    LinearMap.toSpanSingleton ℝ (ℕ →₀ cfock (Excited m))
      (Finsupp.single (α 0)
        (toCFock (Excited m) (Finsupp.single (restOf α)
          (((fockW (α 0) (restOf α) : ℝ) : ℂ)))))

end Work.BoseB4
