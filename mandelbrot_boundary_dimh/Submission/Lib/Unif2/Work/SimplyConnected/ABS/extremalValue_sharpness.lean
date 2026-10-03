import Mathlib
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.ExtremalImports
import Submission.Lib.Unif2.Extremal
import Submission.Lib.Unif2.ExtremalInj
import Submission.Lib.Unif2.Work.SimplyConnected.ABS.extremal_maximizer_proper

/-!
# The extremal value at a second point, and its symmetry

`extremalValue p q = sup {‖h q‖ : h ∈ Submission.extremalFamily p}` is Ahlfors' `A(p,q)`.

* `extremalValue_eq_exp_neg_of_rigidity`: if the maximiser `f` at `x₀` attains the envelope `E`
  (Ahlfors' rigidity, proved decay-free in `rigidity_of_maximizer_decayfree.lean`), then the
  supremum is *attained* by `f` at every point `y ≠ x₀`:
  `A(x₀,y) = exp (-(E y))`.  This is the sharpness of the extremal problem at every point, and it
  is the first half of Ahlfors' symmetry of the Green function.
* `extremalValue_symm`: `A(p,q) = A(q,p)` — the cheap half of Ahlfors' symmetry of the Green
  function (the Möbius trick: for `h ∈ 𝔽_q`, `ψ_{h p} ∘ h ∈ 𝔽_p` evaluates at `q` to `h p`).
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

set_option linter.unusedSectionVars false

noncomputable section

open Filter Set Classical

namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x₀ : X}

/-- The set defining `extremalValue p q` is bounded above by `1`. -/
theorem bddAbove_extremalValueSet (p q : X) :
    BddAbove ((fun h : X → ℂ => ‖h q‖) '' Submission.extremalFamily p) :=
  ⟨1, by rintro _ ⟨h, hh, rfl⟩; exact hh.2.1 q⟩

/-- **The extremal value is attained by the maximiser**, given the rigidity. -/
theorem extremalValue_eq_exp_neg_of_rigidity {E : X → ℝ} {f : X → ℂ}
    (hf : f ∈ Submission.extremalFamily x₀)
    (hdom : ∀ g ∈ Submission.extremalFamily x₀, ∀ x : X, x ≠ x₀ → ‖g x‖ ≤ Real.exp (-(E x)))
    (hrig : ∀ x : X, x ≠ x₀ → ‖f x‖ = Real.exp (-(E x)))
    {y : X} (hy : y ≠ x₀) :
    extremalValue x₀ y = Real.exp (-(E y)) := by
  refine le_antisymm ?_ ?_
  · refine csSup_le (Set.Nonempty.image _ (Submission.extremalFamily_nonempty x₀)) ?_
    rintro _ ⟨g, hg, rfl⟩
    exact hdom g hg y hy
  · have hmem : ‖f y‖ ∈ (fun h : X → ℂ => ‖h y‖) '' Submission.extremalFamily x₀ :=
      ⟨f, hf, rfl⟩
    calc Real.exp (-(E y)) = ‖f y‖ := (hrig y hy).symm
      _ ≤ extremalValue x₀ y := le_csSup (bddAbove_extremalValueSet x₀ y) hmem

end Work.SimplyConnected.ABS
namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X]

/-- **Every member of the extremal family maps into the open ball.**  If `‖h x‖ = 1` for a member
`h ∈ 𝔽_p`, then `‖h‖ ≤ 1 = ‖h x‖` is a maximum of the subharmonic function `‖h‖`, so `‖h‖` is
constant, hence `h` is constant, hence `h ≡ h p = 0` and `‖h x‖ = 0`, a contradiction. -/
theorem norm_lt_one_of_mem_extremalFamily {p : X} {h : X → ℂ}
    (hh : h ∈ Submission.extremalFamily p) (x : X) : ‖h x‖ < 1 := by
  by_contra hcon
  push_neg at hcon
  have h1 : ‖h x‖ = 1 := le_antisymm (hh.2.1 x) hcon
  have hsub : Submission.SubharmonicOnX (fun z : X => ‖h z‖) Set.univ :=
    subharmonicOnX_norm_of_holomorphic hh.1
  have hmax : ∀ z : X, ‖h z‖ ≤ ‖h x‖ := by
    intro z
    rw [h1]
    exact hh.2.1 z
  have hconst : ∀ z : X, ‖h z‖ = ‖h x‖ :=
    Submission.SubharmonicOnX.eq_of_isMaxOn hsub hmax
  have hcong : ∀ z : X, h z = h x :=
    hh.1.exists_eq_const_of_norm_eq x (fun z => by rw [hconst z, hconst x])
  have hzero : ‖h x‖ = 0 := by
    rw [← hcong p, hh.2.2, norm_zero]
  rw [h1] at hzero
  norm_num at hzero

/-- **The Möbius trick: `A(q,p) ≤ A(p,q)`.**  For `h ∈ 𝔽_q`, the function `ψ_{h p} ∘ h` lies in
`𝔽_p` and takes the value `h p` at `q`, whence `‖h p‖ ≤ A(p,q)`; the sup over `h ∈ 𝔽_q` is the
claim. -/
theorem extremalValue_le_symm (p q : X) : extremalValue q p ≤ extremalValue p q := by
  classical
  refine csSup_le (Set.Nonempty.image _ (Submission.extremalFamily_nonempty q)) ?_
  rintro _ ⟨h, hh, rfl⟩
  rcases eq_or_ne (h p) 0 with hzero | hne
  · simp only [hzero, norm_zero]
    exact le_csSup (bddAbove_extremalValueSet p q) ⟨0, Submission.zero_mem_extremalFamily p, by simp⟩
  · have hlt : ‖h p‖ < 1 := norm_lt_one_of_mem_extremalFamily hh p
    set H : X → ℂ := fun z => Submission.mobiusA (h p) (h z) with hHdef
    have hHhol : Submission.HolomorphicOnX H Set.univ :=
      Submission.HolomorphicOnX.mobiusA_comp hh.1 (fun z _ => hh.2.1 z) hlt
    have hHnorm : ∀ z : X, ‖H z‖ ≤ 1 := fun z =>
      Submission.norm_mobiusA_le hlt (hh.2.1 z)
    have hHp : H p = 0 := by
      simp only [hHdef, Function.comp_apply]
      exact Submission.mobiusA_self (h p)
    have hHmem : H ∈ Submission.extremalFamily p := ⟨hHhol, hHnorm, hHp⟩
    have hHq : H q = -h p := by
      simp only [hHdef]
      rw [hh.2.2, Submission.mobiusA_apply_zero]
    have hmem : ‖H q‖ ∈ (fun g : X → ℂ => ‖g q‖) '' Submission.extremalFamily p :=
      ⟨H, hHmem, rfl⟩
    calc ‖h p‖ = ‖H q‖ := by rw [hHq, norm_neg]
      _ ≤ extremalValue p q := le_csSup (bddAbove_extremalValueSet p q) hmem

/-- **Ahlfors' symmetry of the extremal value**: `A(p,q) = A(q,p)`. -/
theorem extremalValue_symm (p q : X) : extremalValue p q = extremalValue q p :=
  le_antisymm (extremalValue_le_symm q p) (extremalValue_le_symm p q)

end Work.SimplyConnected.ABS
namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x₀ : X} {y : X}

/-- **Ahlfors' symmetry of the envelopes, one direction.**  Suppose the maximiser `f` at `x₀`
attains the envelope `E₀` off the pole (the rigidity, `rigidity_of_maximizer`), that `E₀` dominates
the extremal family at `x₀`, and that `Ey` dominates the extremal family at a second pole `y ≠ x₀`
(the Perron inequality, `Work.SimplyConnected.ABS.sweep_greenBarrier_dominates`).  Then

  `Ey x₀ ≤ E₀ y`.

This is Ahlfors' inequality `(10-4)` evaluated at the pole `x₀`: with the sharpness of `A(x₀,·)`
given by the rigidity and the symmetry `A(x₀,y) = A(y,x₀)`, the Perron inequality at `y` gives the
claim.  The *reverse* inequality needs the sharpness at `y` as well (the modulus at `y`). -/
theorem envelope_symm_le {E₀ Ey : X → ℝ} {f : X → ℂ}
    (hf : f ∈ Submission.extremalFamily x₀)
    (hdom₀ : ∀ g ∈ Submission.extremalFamily x₀, ∀ z : X, z ≠ x₀ → ‖g z‖ ≤ Real.exp (-(E₀ z)))
    (hrig : ∀ z : X, z ≠ x₀ → ‖f z‖ = Real.exp (-(E₀ z)))
    (hdomy : ∀ g ∈ Submission.extremalFamily y, ∀ z : X, z ≠ y → ‖g z‖ ≤ Real.exp (-(Ey z)))
    (hy : y ≠ x₀) : Ey x₀ ≤ E₀ y := by
  have hAy : extremalValue y x₀ ≤ Real.exp (-(Ey x₀)) := by
    refine csSup_le (Set.Nonempty.image _ (Submission.extremalFamily_nonempty y)) ?_
    rintro _ ⟨g, hg, rfl⟩
    exact hdomy g hg x₀ (Ne.symm hy)
  have hA0 : extremalValue x₀ y = Real.exp (-(E₀ y)) :=
    extremalValue_eq_exp_neg_of_rigidity (x₀ := x₀) hf hdom₀ hrig hy
  have h := hAy
  rw [extremalValue_symm y x₀, hA0] at h
  exact neg_le_neg_iff.mp (Real.exp_le_exp.mp h)

end Work.SimplyConnected.ABS
namespace Work.SimplyConnected.ABS

variable {X : Type*} [TopologicalSpace X] [T2Space X] [ConnectedSpace X]
  [SecondCountableTopology X] [ChartedSpace ℂ X]
  [IsManifold (modelWithCornersSelf ℂ ℂ) 1 X] {x₀ : X} {y : X}

/-- **Ahlfors' symmetry of the Green function, in envelope form.**  If the extremal maximiser at
`x₀` attains the envelope `E₀` (the rigidity) and the extremal maximiser at the second pole `y`
attains `Ey`, and each envelope dominates its extremal family, then

  `Ey x₀ = E₀ y`

(the classical symmetry `g(q,p) = g(p,q)` of the Green function).  Both inequalities are
`envelope_symm_le`, applied with the two poles interchanged. -/
theorem envelope_symm {E₀ Ey : X → ℝ} {f f' : X → ℂ}
    (hf : f ∈ Submission.extremalFamily x₀)
    (hdom₀ : ∀ g ∈ Submission.extremalFamily x₀, ∀ z : X, z ≠ x₀ → ‖g z‖ ≤ Real.exp (-(E₀ z)))
    (hrig : ∀ z : X, z ≠ x₀ → ‖f z‖ = Real.exp (-(E₀ z)))
    (hf' : f' ∈ Submission.extremalFamily y)
    (hdomy : ∀ g ∈ Submission.extremalFamily y, ∀ z : X, z ≠ y → ‖g z‖ ≤ Real.exp (-(Ey z)))
    (hrigy : ∀ z : X, z ≠ y → ‖f' z‖ = Real.exp (-(Ey z)))
    (hy : y ≠ x₀) : Ey x₀ = E₀ y :=
  le_antisymm
    (envelope_symm_le (x₀ := x₀) (y := y) hf hdom₀ hrig hdomy hy)
    (envelope_symm_le (x₀ := y) (y := x₀) hf' hdomy hrigy hdom₀ (Ne.symm hy))

end Work.SimplyConnected.ABS
