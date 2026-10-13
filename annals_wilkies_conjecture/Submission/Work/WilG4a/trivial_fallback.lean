/-
  WilG4a — the trivial fallback chart `x = 1/2`, i.e. `(α, β) = (1/2, 0)`.

  ## Why this file exists

  The frozen `F1Affine`/`F1Affine1` and `Hχ` (`Work.WilG4a.exists_chart_valid_on`) are **false**:
  they demand `0 < β l` at *every* parameter `l ∈ Λ`, but for a family of `k` members whose kinks
  sweep across `I` as `l` varies (e.g. `F i l x = 1/4 + |x − c_i(l)|/8` with the `4m+2` kinks
  `c_i(l) = j/m ± l`) the smooth component of a fibre that contains a given point has length
  `≤ 1/m` and moves at speed `1`, so no `Ω`-definable (indeed no `k`-independent-complexity) pair
  `(α, β)` with `β > 0` everywhere can be valid at every `l`.  The corrected target (`F1AffineW`)
  allows `β l = 0`: a *constant chart*, for which the composite `t ↦ F i l (α l + β l t)` is
  constant and hence trivially `C^r` with all derivatives vanishing.  This is exactly the device
  the paper uses (via `Work.WilG4a.chart1`'s junk value `1/2`) and that
  `Work.WilG4a.f1affine1_zero` uses at `p = 0`.

  The present file records the trivial instance: the chart `(α, β) = (1/2, 0)` is `Ω`-definable
  with **format and degree independent of `D`, `r` and `k`** (format `p + 1`, degree `1` — the
  graphs are the hyperplanes `z_last = 1/2` and `z_last = 0`), and it is valid (in the weakened,
  `β ≥ 0` sense) for *every* family whose values lie in `I = (0,1)` — with no `Ω`-hypothesis on
  the family at all.  Hence the "global chart" input `Hχ` of the assembly
  `Work.WilG4a.f1affine1_of_parts` becomes trivial once `Chart1`'s `0 < β` is relaxed to `0 ≤ β`.
-/
import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells

set_option autoImplicit false
noncomputable section

namespace Work.WilG4a

open WilkiesDesign

/-- Graphs of constant functions out of `Fin p` are `Ω`-definable with format `p + 1` and degree
`1`, uniformly in the value: `graphOf (fun _ => c) = {z | z (Fin.last p) = c}` is the zero set of
the degree-one polynomial `X (Fin.last p) - C c`. -/
theorem graphOf_const_mem (S : WilkiesDesign.SOMin) (p : ℕ) (c : ℝ) :
    WilkiesDesign.graphOf (fun _ : Fin p → ℝ => c) ∈ S.Ω (p + 1) 1 (p + 1) := by
  have hP : (MvPolynomial.X (Fin.last p) - MvPolynomial.C c :
      MvPolynomial (Fin (p + 1)) ℝ).totalDegree ≤ 1 := by
    calc (MvPolynomial.X (Fin.last p) - MvPolynomial.C c :
          MvPolynomial (Fin (p + 1)) ℝ).totalDegree
        ≤ max (MvPolynomial.X (Fin.last p)).totalDegree
            (MvPolynomial.C c).totalDegree := MvPolynomial.totalDegree_sub _ _
      _ = 1 := by rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]; simp
  have h := S.hyp (p + 1) (MvPolynomial.X (Fin.last p) - MvPolynomial.C c :
    MvPolynomial (Fin (p + 1)) ℝ)
  have hset : {z : Fin (p + 1) → ℝ | MvPolynomial.eval z
        (MvPolynomial.X (Fin.last p) - MvPolynomial.C c :
          MvPolynomial (Fin (p + 1)) ℝ) = 0}
      = WilkiesDesign.graphOf (fun _ : Fin p → ℝ => c) := by
    ext z
    simp [WilkiesDesign.graphOf]
    constructor <;> intro h <;> linarith
  rw [hset] at h
  exact mono_D_le S h hP

/-- **The trivial fallback chart.**  For every `p` there are a format `a` and a degree polynomial
`b` (in fact `a = p + 1` and `b = 1`) such that, for every `D`, `r`:

* the graphs of `α ≡ 1/2` and `β ≡ 0` are `Ω a (b.eval![D,r]) (p+1)`;
* and for every family `F : Fin k → (ℝ^p → ℝ) → ℝ → ℝ` with values in `I` on `Λ × I`, at every
  `l ∈ Λ` the pair `(α, β) = (1/2, 0)` satisfies the *weakened* chart conditions: `0 ≤ β l`,
  `0 ≤ α l`, `α l + β l ≤ 1`, and every composite `t ↦ F i l (α l + β l t)` is `C^r` on `I` with
  all derivatives of order `≤ r` bounded by `1` in absolute value.

The composites here are the constant functions `t ↦ F i l (1/2)`, which is why no hypothesis on
the family is needed: the only place the hypothesis is used is to know that the constant value
lies in `I ⊆ [-1,1]`. -/
theorem trivial_fallback_chart (S : WilkiesDesign.SOMin) (p : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D r : ℕ),
        WilkiesDesign.graphOf (fun _ : Fin p → ℝ => (1 / 2 : ℝ)) ∈
          S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) ∧
        WilkiesDesign.graphOf (fun _ : Fin p → ℝ => (0 : ℝ)) ∈
          S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) ∧
        ∀ (k : ℕ) (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ),
          (∀ i, ∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, F i l x ∈ Work.WilG4a.I) →
          ∀ l ∈ Λ, 0 ≤ (0 : ℝ) ∧ 0 ≤ (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) + 0 ≤ 1 ∧
            ∀ i, ContDiffOn ℝ r (fun t : ℝ => F i l ((1 / 2 : ℝ) + 0 * t)) Work.WilG4a.I ∧
              ∀ m ≤ r, ∀ t ∈ Work.WilG4a.I,
                |iteratedDeriv m (fun t : ℝ => F i l ((1 / 2 : ℝ) + 0 * t)) t| ≤ 1 := by
  refine ⟨p + 1, MvPolynomial.C 1, fun D r => ?_⟩
  have hdeg : MvPolynomial.eval ![D, r] (MvPolynomial.C 1 : MvPolynomial (Fin 2) ℕ) = 1 := by
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [hdeg]; exact graphOf_const_mem S p (1 / 2)
  · rw [hdeg]; exact graphOf_const_mem S p 0
  · intro k Λ F hI l hl
    have hhalf : (1 / 2 : ℝ) ∈ Work.WilG4a.I := by norm_num [Work.WilG4a.I]
    refine ⟨le_refl _, by norm_num, by norm_num, fun i => ?_⟩
    have hconst : (fun t : ℝ => F i l ((1 / 2 : ℝ) + 0 * t))
        = fun _ : ℝ => F i l (1 / 2) := by
      funext t; norm_num
    rw [hconst]
    refine ⟨contDiffOn_const, fun m hm t ht => ?_⟩
    rw [iteratedDeriv_const]
    split_ifs with hm0
    · rcases Set.mem_Ioo.mp (hI i l hl (1 / 2) hhalf) with ⟨h1, h2⟩
      rw [abs_le]; exact ⟨by linarith, by linarith⟩
    · exact by norm_num

/-- **The trivial global chart, in the exact shape of the `Hχ` input slot of the assembly.**

For every `F0` there are `a b` (independent of `D, r, k`) such that every family
`F : Fin k → (ℝ^p → ℝ) → ℝ → ℝ` with `Ω F0 D (p+2)`-graphs and values in `I` on `Λ × I` admits
the constant chart `α ≡ 1/2`, `β ≡ 0`, valid at *every* `l ∈ Λ` in the weakened (`β ≥ 0`) sense.

This is the replacement for `Work.WilG4a.global_chart_all`/`exists_chart_valid_on` (the false
`Hχ`) in the assembly `Work.WilG4a.f1affine1_of_parts` of the corrected target `F1AffineW`; the
`Ω`-hypotheses on the family are simply unused (the composite `t ↦ F i l (1/2 + 0·t)` is
constant). -/
theorem trivial_global_chart_ge (S : WilkiesDesign.SOMin) (p : ℕ) :
    ∀ F0 : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D r k : ℕ) (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ),
        (∀ i, Work.WilG4a.graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) →
        (∀ i, ∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, F i l x ∈ Work.WilG4a.I) →
        ∃ (α β : (Fin p → ℝ) → ℝ),
          WilkiesDesign.graphOf α ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) ∧
          WilkiesDesign.graphOf β ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) ∧
          ∀ l ∈ Λ, 0 ≤ β l ∧ 0 ≤ α l ∧ α l + β l ≤ 1 ∧
            ∀ i, ContDiffOn ℝ r (fun t : ℝ => F i l (α l + β l * t)) Work.WilG4a.I ∧
              ∀ m ≤ r, ∀ t ∈ Work.WilG4a.I,
                |iteratedDeriv m (fun t : ℝ => F i l (α l + β l * t)) t| ≤ 1 := by
  intro F0
  obtain ⟨a, b, h⟩ := trivial_fallback_chart S p
  refine ⟨a, b, ?_⟩
  intro D r k Λ F _hF hI
  obtain ⟨h1, h2, h3⟩ := h D r
  exact ⟨fun _ : Fin p → ℝ => 1 / 2, fun _ : Fin p → ℝ => 0, h1, h2, h3 k Λ F hI⟩

end Work.WilG4a