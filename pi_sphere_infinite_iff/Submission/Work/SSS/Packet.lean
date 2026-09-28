import Mathlib
import Submission.Work.SSS.Filtration

/-!
# The convergence packet of the Serre spectral sequence

`Work.SSS.SSPacket ξ` is the exact input that Serre's three-for-two theorem for a Serre fibration
consumes from the spectral sequence of the filtration `ξ`:

* `mono`, `bot`, `top` : the image filtration `Φ_s = im(H_n(F_s) → H_n(C))` is increasing, vanishes
  for `s < 0` and is everything in degree `n`;
* `graded` : every graded piece `Φ_s/Φ_{s-1}` is a subquotient of the E² page `E²_{s,n-s}`, read in
  the Serre class of finitely generated groups (this is the convergence `E² ⟹ H_*(C)` combined with
  `E^∞ ⊆ E²`);
* `base_row` : the bottom row of the spectral sequence: `E²_{n,0}` is finitely generated when
  `H_n(C)` is and the E² terms of the diagonal `s + t = n - 1`, `t ≥ 1`, are (the kernels of the
  higher differentials landing in the bottom row are subquotients of those);
* `fibre_col` : the left column, dually.

Everything is phrased in the *Serre class* of finitely generated abelian groups; the mathematical
content is the usual convergence theorem together with the two edge arguments.

`Work.SSS.SSPacket.total` is the "total" direction of the three-for-two theorem.
-/

set_option autoImplicit false

namespace Work.SSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {C : ChainComplex (ModuleCat ℤ) ℕ}
variable {ξ : Filtration C}

/-- The **convergence packet** of the spectral sequence of a saturated filtration `ξ` of `C`. -/
structure SSPacket (ξ : Filtration C) : Prop where
  /-- the image filtration is increasing -/
  mono : ∀ n : ℕ, Monotone (Phi ξ n)
  /-- the image filtration vanishes below `0` -/
  bot : ∀ (n : ℕ) (s : ℤ), s < 0 → Phi ξ n s = ⊥
  /-- the image filtration reaches everything in degree `n` (saturation) -/
  top : ∀ n : ℕ, Phi ξ n (n : ℤ) = ⊤
  /-- the graded pieces of the image filtration are subquotients of the E² page -/
  graded : ∀ (n s : ℕ), (s : ℤ) ≤ n → Module.Finite ℤ (E2 ξ s (n - s)) →
    (Phi ξ n ((s : ℤ) - 1)).FG → (Phi ξ n s).FG
  /-- the bottom row argument -/
  base_row : ∀ n : ℕ, Module.Finite ℤ (C.homology n) →
    (∀ r : ℕ, 2 ≤ r → r ≤ n → Module.Finite ℤ (E2 ξ (n - r) (r - 1))) →
    Module.Finite ℤ (E2 ξ n 0)
  /-- the left column argument -/
  fibre_col : ∀ t : ℕ, (∀ r : ℕ, 2 ≤ r → r ≤ t + 1 → Module.Finite ℤ (E2 ξ r (t + 1 - r))) →
    (Phi ξ t 0).FG → Module.Finite ℤ (E2 ξ 0 t)

/-- **The total direction of Serre's three-for-two theorem.** If the E² page of the filtration is
finitely generated in every total degree `n` (that is, for every `s ≤ n`), then so is `H_n(C)`. -/
theorem SSPacket.total (h : SSPacket ξ) (n : ℕ)
    (hE2 : ∀ s : ℕ, s ≤ n → Module.Finite ℤ (E2 ξ s (n - s))) :
    Module.Finite ℤ (C.homology n) := by
  have key : ∀ s : ℕ, s ≤ n → (Phi ξ n (s : ℤ)).FG := by
    intro s
    induction s with
    | zero =>
      intro _
      refine h.graded n 0 (by omega) (hE2 0 (by omega)) ?_
      rw [h.bot n (((0 : ℕ) : ℤ) - 1) (by norm_num)]
      exact Submodule.fg_bot
    | succ k ih =>
      intro hk
      have hstep := h.graded n (k + 1) (by omega) (hE2 (k + 1) hk)
      rw [show (((k + 1 : ℕ)) : ℤ) - 1 = (k : ℤ) by omega] at hstep
      exact hstep (ih (by omega))
  have htop : (⊤ : Submodule ℤ (C.homology n)).FG := by
    rw [← h.top n]
    exact key n le_rfl
  exact Module.finite_def.mpr htop

end

end Work.SSS
