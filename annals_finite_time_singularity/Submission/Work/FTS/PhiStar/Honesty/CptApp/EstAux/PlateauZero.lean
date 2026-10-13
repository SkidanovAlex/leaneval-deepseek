/-
# `cutPlateauZero`: the positive-order `D`-iterates of the cut-offs vanish on the plateau

The two cut-offs of `CptApp/Defs.lean` are

  `chiR n z  = 𝕋 (n z - 1) · 𝕋 (2 - z/n)`,    `zetaR n θ = 𝕋 (n θ - 1) · 𝕋 (n (π/2 - θ) - 1)`,

with `𝕋 = Real.smoothTransition` the smooth step (`0` on `(-∞,0]`, `1` on `[1,∞)`).  Hence
`chiR n = 1` on the closed *radial plateau* `[2/n, n]` (`cutBasic.chiR_eq_one`) and
`zetaR n = 1` on the closed *angular plateau* `[2/n, π/2 - 2/n]` (`cutBasic.zetaR_eq_one`),
and this file proves that the positive-order operators `D_z = z ∂_z` (radial) and
`D_θ = sin(2θ) ∂_θ` (angular) annihilate the cut-offs there.

**The argument** (the route of `NOTES_cutBounds.md` §(c)) does *not* analyse the flatness of
`𝕋` at its endpoints.  Two facts suffice:

* the cut-off is *locally constant* `= 1` on the **open** plateau, so by locality of `deriv`
  every positive-order iterate vanishes on the open plateau; and
* each iterate `z ↦ D_z^k (fun z _ => chiR n z) z 0` (resp. `θ ↦ D_θ^k (fun _ θ => zetaR n θ) 0 θ`)
  is a `C^∞` function of the remaining variable — its recursion is `g_{k+1} = z · g_k'`
  (resp. `G_{k+1} = sin(2θ) · G_k'`), and a `C^∞` function has `C^∞` first derivative —
  hence continuous, and the closed plateau is the closure of the open one.

The two abstract lemmas `DzIter_apply_zero_of_const_on_Ioo` and
`DthIter_apply_zero_of_const_on_Ioo` below carry out this argument for an arbitrary `C^∞`
one-variable function which is constant on an open interval; the two conjuncts of
`cutPlateauZero` are then immediate instances.
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import Submission.Work.FTS.PhiStar.Honesty.CptApp.Defs
import Submission.Work.FTS.PhiStar.Honesty.CptApp.EstDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp.EstAux

theorem est_two_le_natCast_of {n : ℕ} (hn : 2 ≤ n) : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn

theorem est_natCast_pos_of {n : ℕ} (hn : 2 ≤ n) : (0 : ℝ) < (n : ℝ) := by
  have := est_two_le_natCast_of hn
  linarith


set_option autoImplicit false

/-! ## The abstract `D_z`-plateau lemma -/

/-- **`D_z`-iterates of a `θ`-independent function constant on an open interval.**

If `f : ℝ → ℝ` is `C^∞` and equal to the constant `c` on the open interval `(a,b)`, with
`a < b`, then for every `k ≥ 1` the `k`-th `D_z`-iterate of `(z,θ) ↦ f z` vanishes on the
closed interval `[a,b]` (at `θ = 0`, which is irrelevant because the function does not
depend on `θ`).

The iterates are `C^∞`, hence continuous, in `z`: the recursion is `g_{k+1} = z · g_k'` and
the derivative of a `C^∞` function is `C^∞`.  On `(a,b)` they vanish because `f` is locally
constant there; and `[a,b]` is the closure of `(a,b)`, so continuity propagates the
vanishing to the endpoints. -/
theorem DzIter_apply_zero_of_const_on_Ioo {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    {a b c : ℝ} (hab : a < b) (hc : ∀ z ∈ Set.Ioo a b, f z = c) :
    ∀ k : ℕ, 1 ≤ k → ∀ z ∈ Set.Icc a b, Work.Spaces.DzIter k (fun z _ : ℝ => f z) z 0 = 0 := by
  -- Every iterate is `C^∞` in `z`, hence continuous.
  have hcont : ∀ k : ℕ,
      Continuous (fun z : ℝ => Work.Spaces.DzIter k (fun z _ : ℝ => f z) z 0) := by
    intro k
    have hsm : ContDiff ℝ ∞ (fun z : ℝ => Work.Spaces.DzIter k (fun z _ : ℝ => f z) z 0) := by
      induction k with
      | zero => simpa using hf
      | succ k ih =>
        have hd : ContDiff ℝ ∞
            (fun z : ℝ => deriv (fun z' => Work.Spaces.DzIter k (fun z _ : ℝ => f z) z' 0) z) := by
          simpa [Function.iterate_one] using (ContDiff.iterate_deriv (𝕜 := ℝ) 1 ih)
        have hfun : (fun z : ℝ => Work.Spaces.DzIter (k + 1) (fun z _ : ℝ => f z) z 0)
            = fun z : ℝ =>
                z * deriv (fun z' => Work.Spaces.DzIter k (fun z _ : ℝ => f z) z' 0) z := rfl
        rw [hfun]
        exact contDiff_id.mul hd
    exact hsm.continuous
  -- Vanishing on the open interval, by induction on the order.
  have hopen : ∀ m : ℕ, ∀ z ∈ Set.Ioo a b,
      Work.Spaces.DzIter (m + 1) (fun z _ : ℝ => f z) z 0 = 0 := by
    intro m
    induction m with
    | zero =>
      intro z hz
      show z * deriv (fun z' => f z') z = 0
      have hev : (fun z' : ℝ => f z') =ᶠ[𝓝 z] (fun _ => c) := by
        filter_upwards [isOpen_Ioo.mem_nhds hz] with z' hz'
        exact hc z' hz'
      rw [hev.deriv_eq, deriv_const, mul_zero]
    | succ m ih =>
      intro z hz
      show z * deriv (fun z' => Work.Spaces.DzIter (m + 1) (fun z _ : ℝ => f z) z' 0) z = 0
      have hev : (fun z' : ℝ => Work.Spaces.DzIter (m + 1) (fun z _ : ℝ => f z) z' 0)
          =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hz] with z' hz'
        exact ih z' hz'
      rw [hev.deriv_eq, deriv_const, mul_zero]
  -- The closed interval is the closure of the open one.
  intro k hk z hz
  obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  subst hm
  have hclosed : IsClosed {z : ℝ | Work.Spaces.DzIter (m + 1) (fun z _ : ℝ => f z) z 0 = 0} :=
    isClosed_eq (hcont (m + 1)) continuous_const
  have hsub : Set.Ioo a b
      ⊆ {z : ℝ | Work.Spaces.DzIter (m + 1) (fun z _ : ℝ => f z) z 0 = 0} :=
    fun z hz => hopen m z hz
  have hcl := closure_minimal hsub hclosed
  rw [closure_Ioo (ne_of_lt hab)] at hcl
  exact hcl hz

/-! ## The abstract `D_θ`-plateau lemma -/

/-- **`D_θ`-iterates of a `z`-independent function constant on an open interval.**

If `g : ℝ → ℝ` is `C^∞` and equal to the constant `c` on the open interval `(a,b)`, with
`a < b`, then for every `k ≥ 1` the `k`-th `D_θ`-iterate of `(z,θ) ↦ g θ` vanishes at `z = 0`
on the closed interval `[a,b]`.

This is the angular analogue of `DzIter_apply_zero_of_const_on_Ioo`: now the recursion of the
iterates `G_k(θ) = D_θ^k (fun _ θ => g θ) 0 θ` is `G_{k+1} = sin(2θ) · G_k'`, and the extra
factor `sin(2θ)` is again `C^∞`, so `G_k` is `C^∞` and the same continuity argument applies.
(The factor vanishes at the endpoints `θ = 0, π/2` of the angular interval, but that is
irrelevant here: `D_θ` is a product, not a quotient, and `[a,b]` is a plateau away from
`0` and `π/2`.) -/
theorem DthIter_apply_zero_of_const_on_Ioo {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    {a b c : ℝ} (hab : a < b) (hc : ∀ θ ∈ Set.Ioo a b, g θ = c) :
    ∀ k : ℕ, 1 ≤ k → ∀ θ ∈ Set.Icc a b, Work.Spaces.DthIter k (fun _ θ : ℝ => g θ) 0 θ = 0 := by
  -- Every iterate is `C^∞` in `θ`, hence continuous.
  have hcont : ∀ k : ℕ,
      Continuous (fun θ : ℝ => Work.Spaces.DthIter k (fun _ θ : ℝ => g θ) 0 θ) := by
    intro k
    have hsm : ContDiff ℝ ∞ (fun θ : ℝ => Work.Spaces.DthIter k (fun _ θ : ℝ => g θ) 0 θ) := by
      induction k with
      | zero => simpa using hg
      | succ k ih =>
        have hd : ContDiff ℝ ∞
            (fun θ : ℝ => deriv (fun θ' => Work.Spaces.DthIter k (fun _ θ : ℝ => g θ) 0 θ') θ) := by
          simpa [Function.iterate_one] using (ContDiff.iterate_deriv (𝕜 := ℝ) 1 ih)
        have hsin : ContDiff ℝ ∞ (fun θ : ℝ => Real.sin (2 * θ)) := by fun_prop
        have hfun : (fun θ : ℝ => Work.Spaces.DthIter (k + 1) (fun _ θ : ℝ => g θ) 0 θ)
            = fun θ : ℝ =>
                Real.sin (2 * θ)
                  * deriv (fun θ' => Work.Spaces.DthIter k (fun _ θ : ℝ => g θ) 0 θ') θ := rfl
        rw [hfun]
        exact hsin.mul hd
    exact hsm.continuous
  -- Vanishing on the open interval, by induction on the order.
  have hopen : ∀ m : ℕ, ∀ θ ∈ Set.Ioo a b,
      Work.Spaces.DthIter (m + 1) (fun _ θ : ℝ => g θ) 0 θ = 0 := by
    intro m
    induction m with
    | zero =>
      intro θ hθ
      show Real.sin (2 * θ) * deriv (fun θ' => g θ') θ = 0
      have hev : (fun θ' : ℝ => g θ') =ᶠ[𝓝 θ] (fun _ => c) := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact hc θ' hθ'
      rw [hev.deriv_eq, deriv_const, mul_zero]
    | succ m ih =>
      intro θ hθ
      show Real.sin (2 * θ)
          * deriv (fun θ' => Work.Spaces.DthIter (m + 1) (fun _ θ : ℝ => g θ) 0 θ') θ = 0
      have hev : (fun θ' : ℝ => Work.Spaces.DthIter (m + 1) (fun _ θ : ℝ => g θ) 0 θ')
          =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
        filter_upwards [isOpen_Ioo.mem_nhds hθ] with θ' hθ'
        exact ih θ' hθ'
      rw [hev.deriv_eq, deriv_const, mul_zero]
  -- The closed interval is the closure of the open one.
  intro k hk θ hθ
  obtain ⟨m, hm⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  subst hm
  have hclosed : IsClosed {θ : ℝ | Work.Spaces.DthIter (m + 1) (fun _ θ : ℝ => g θ) 0 θ = 0} :=
    isClosed_eq (hcont (m + 1)) continuous_const
  have hsub : Set.Ioo a b
      ⊆ {θ : ℝ | Work.Spaces.DthIter (m + 1) (fun _ θ : ℝ => g θ) 0 θ = 0} :=
    fun θ hθ => hopen m θ hθ
  have hcl := closure_minimal hsub hclosed
  rw [closure_Ioo (ne_of_lt hab)] at hcl
  exact hcl hθ

/-! ## The plateau of the two cut-offs -/

theorem estPlateauZero :
    (∀ n : ℕ, 2 ≤ n → ∀ b : ℕ, 1 ≤ b → ∀ z : ℝ, 2 / (n : ℝ) ≤ z → z ≤ (n : ℝ) →
      Work.Spaces.DzIter b (fun z _ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.chiR n z) z 0 = 0) ∧
    (∀ n : ℕ, 2 ≤ n → ∀ a : ℕ, 1 ≤ a → ∀ θ : ℝ, 2 / (n : ℝ) ≤ θ
        → θ ≤ Real.pi / 2 - 2 / (n : ℝ) →
      Work.Spaces.DthIter a (fun _ θ : ℝ => Work.FTS.PhiStar.Honesty.CptApp.zetaR n θ) 0 θ = 0) := by
  constructor
  · -- the radial plateau `[2/n, n]` of `chiR n`,
    -- on whose interior `chiR n = 1` (`cutBasic.chiR_eq_one`)
    intro n hn b hb z hz1 hz2
    have hlt : 2 / (n : ℝ) < (n : ℝ) := by
      have h1 : 2 / (n : ℝ) ≤ 1 := (div_le_one (est_natCast_pos_of hn)).mpr (est_two_le_natCast_of hn)
      have h2 : (1 : ℝ) < (n : ℝ) := by
        have := est_two_le_natCast_of hn
        linarith
      linarith
    exact DzIter_apply_zero_of_const_on_Ioo (Work.FTS.PhiStar.Honesty.CptApp.contDiff_chiR_C n) hlt
      (fun z hz => chiR_eq_one hn (le_of_lt hz.1) (le_of_lt hz.2)) b hb z ⟨hz1, hz2⟩
  · -- the angular plateau `[2/n, π/2 - 2/n]` of `zetaR n`,
    -- on whose interior `zetaR n = 1` (`cutBasic.zetaR_eq_one`)
    intro n hn a ha θ hθ1 hθ2
    by_cases hn2 : n = 2
    · -- for `n = 2` the angular plateau is empty, so there is nothing to prove
      exfalso
      subst hn2
      norm_num at hθ1 hθ2
      linarith [Real.pi_lt_four]
    · have hn3 : 3 ≤ n := by omega
      have hlt : 2 / (n : ℝ) < Real.pi / 2 - 2 / (n : ℝ) := by
        have h1 : 2 / (n : ℝ) ≤ 2 / 3 := by
          rw [div_le_div_iff₀ (est_natCast_pos_of hn) (by norm_num : (0 : ℝ) < 3)]
          have : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn3
          linarith
        linarith [Real.pi_gt_three]
      exact DthIter_apply_zero_of_const_on_Ioo (Work.FTS.PhiStar.Honesty.CptApp.contDiff_zetaR_C n) hlt
        (fun θ hθ => zetaR_eq_one hn (le_of_lt hθ.1) (le_of_lt hθ.2)) a ha θ ⟨hθ1, hθ2⟩

end Work.FTS.PhiStar.Honesty.CptApp.EstAux
