import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.FstarPkg

set_option autoImplicit false

/-! ## Congruence of the `𝒲^{l,∞}`-norm

Both `WlInf` and `WlInfMem` are built out of suprema over the domain `Iz ×ˢ Iθ` of the
functions `(z+1)^k ∂_z^k f` and `(z+1)^k ∂_z^k D_θ^j f · sin(2θ)^{-α/5}/(α+sin 2θ)`.
Since `Iz = [0,∞)`, the hypothesis `∀ z, -1 < z → f z = g z` constrains `f` and `g` on the
whole domain, and on the open right half-plane `(-1,∞)` it makes all the `z`-derivatives
coincide as well (`∂_z` is local); the `θ`-derivatives need no neighbourhood because the
hypothesis already holds for *every* `θ`.  Hence all the functions whose suprema enter the
definition agree on `Iz ×ˢ Iθ` and the two norms coincide. -/

/-- A point of `Iz = [0,∞)` is `> -1`. -/
private lemma neg_one_lt_of_mem_Iz {z : ℝ} (hz : z ∈ Work.Spaces.Iz) : -1 < z := by
  have : (0 : ℝ) ≤ z := hz
  linarith

/-- Two functions which agree on the open right half-plane `(-1,∞)` have the same derivative
at every point `z > -1` (the derivative is a local notion). -/
private lemma deriv_congr_Ioi {F G : ℝ → ℝ} {z : ℝ} (hz : -1 < z)
    (h : ∀ z' : ℝ, -1 < z' → F z' = G z') : deriv F z = deriv G z :=
  Filter.EventuallyEq.deriv_eq
    (Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_Ioi hz) fun z' hz' => h z' hz')

/-- If `f` and `g` agree for every `z > -1` (and every `θ`), then so do all their iterated
plain `z`-derivatives. -/
private lemma pzIter_congr {f g : ℝ → ℝ → ℝ}
    (hfg : ∀ z, -1 < z → ∀ θ, f z θ = g z θ) (k : ℕ) :
    ∀ z, -1 < z → ∀ θ, Work.Spaces.pzIter k f z θ = Work.Spaces.pzIter k g z θ := by
  induction k with
  | zero => exact hfg
  | succ k ih =>
      intro z hz θ
      show deriv (fun z' => Work.Spaces.pzIter k f z' θ) z
        = deriv (fun z' => Work.Spaces.pzIter k g z' θ) z
      exact deriv_congr_Ioi hz fun z' hz' => ih z' hz' θ

/-- If `f` and `g` agree for every `z > -1` (and every `θ`), then so do all their iterated
plain `θ`-derivatives (at any `z > -1`). -/
private lemma pthIter_congr {f g : ℝ → ℝ → ℝ}
    (hfg : ∀ z, -1 < z → ∀ θ, f z θ = g z θ) (j : ℕ) :
    ∀ z, -1 < z → ∀ θ, Work.Spaces.pthIter j f z θ = Work.Spaces.pthIter j g z θ := by
  induction j with
  | zero => exact hfg
  | succ j ih =>
      intro z hz θ
      show deriv (fun θ' => Work.Spaces.pthIter j f z θ') θ
        = deriv (fun θ' => Work.Spaces.pthIter j g z θ') θ
      rw [funext (fun θ' => ih z hz θ')]

/-- If `f` and `g` agree for every `z > -1` (and every `θ`), then so do all their iterated
`D_θ`-derivatives (at any `z > -1`). -/
private lemma DthIter_congr {f g : ℝ → ℝ → ℝ}
    (hfg : ∀ z, -1 < z → ∀ θ, f z θ = g z θ) (j : ℕ) :
    ∀ z, -1 < z → ∀ θ, Work.Spaces.DthIter j f z θ = Work.Spaces.DthIter j g z θ := by
  induction j with
  | zero => exact hfg
  | succ j ih =>
      intro z hz θ
      show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter j f z θ') θ
        = Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter j g z θ') θ
      rw [funext (fun θ' => ih z hz θ')]

/-- The sets whose suprema define `supAbs` coincide as soon as the two functions agree on the
domain `Iz ×ˢ Iθ`. -/
private lemma supSet_congr {f g : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, f z θ = g z θ) :
    {y : ℝ | ∃ z ∈ Work.Spaces.Iz, ∃ θ ∈ Work.Spaces.Iθ, y = |f z θ|}
      = {y : ℝ | ∃ z ∈ Work.Spaces.Iz, ∃ θ ∈ Work.Spaces.Iθ, y = |g z θ|} := by
  ext y
  constructor
  · rintro ⟨z, hz, θ, hθ, rfl⟩
    exact ⟨z, hz, θ, hθ, congrArg abs (h z hz θ hθ)⟩
  · rintro ⟨z, hz, θ, hθ, rfl⟩
    exact ⟨z, hz, θ, hθ, (congrArg abs (h z hz θ hθ)).symm⟩

/-- `supAbs` only depends on the values of the function on the domain `Iz ×ˢ Iθ`. -/
private lemma supAbs_congr {f g : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, f z θ = g z θ) :
    Work.Spaces.supAbs f = Work.Spaces.supAbs g :=
  congrArg sSup (supSet_congr h)

/-- `SupFinite` only depends on the values of the function on the domain `Iz ×ˢ Iθ`. -/
private lemma SupFinite_congr {f g : ℝ → ℝ → ℝ}
    (h : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ, f z θ = g z θ) :
    Work.Spaces.SupFinite f ↔ Work.Spaces.SupFinite g := by
  unfold Work.Spaces.SupFinite
  rw [supSet_congr h]

-- Intended full name: `Work.FTS.Nonlinear.FstarPkg.WlInf_congr`
-- (declare it inside `namespace Work.FTS.Nonlinear.FstarPkg`).  `WlInf` and `WlInfMem` are
-- the `𝒲^{l,∞}`-norm and its membership predicate of `Submission/Work/Spaces/Defs.lean`; both
-- are built from `pzIter k f`, `pzIter k (DthIter j f)` evaluated at `(z,θ) ∈ Iz ×ˢ Iθ`.
theorem WlInf_congr {f g : ℝ → ℝ → ℝ}
    (hfg : ∀ z, -1 < z → ∀ θ, f z θ = g z θ) (α : ℝ) (l : ℕ) :
    Work.Spaces.WlInf α l f = Work.Spaces.WlInf α l g ∧
      (Work.Spaces.WlInfMem α l f ↔ Work.Spaces.WlInfMem α l g) := by
  -- the `z`-slots of `WlInf` agree
  have hz : ∀ k : ℕ,
      Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ)
        = Work.Spaces.supAbs (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k g z θ) := by
    intro k
    refine supAbs_congr fun z hz θ hθ => ?_
    rw [pzIter_congr hfg k z (neg_one_lt_of_mem_Iz hz) θ]
  -- the mixed `(z,θ)`-slots of `WlInf` agree
  have hm : ∀ j k : ℕ,
      Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
          * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        = Work.Spaces.supAbs (fun z θ => (z + 1) ^ k
          * Work.Spaces.pzIter k (Work.Spaces.DthIter j g) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
    intro j k
    refine supAbs_congr fun z hz θ hθ => ?_
    rw [pzIter_congr (DthIter_congr hfg j) k z (neg_one_lt_of_mem_Iz hz) θ]
  -- the corresponding `SupFinite` statements agree
  have hSFz : ∀ k : ℕ,
      Work.Spaces.SupFinite (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ)
        ↔ Work.Spaces.SupFinite (fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k g z θ) := by
    intro k
    refine SupFinite_congr fun z hz θ hθ => ?_
    rw [pzIter_congr hfg k z (neg_one_lt_of_mem_Iz hz) θ]
  have hSFm : ∀ j k : ℕ,
      Work.Spaces.SupFinite (fun z θ => (z + 1) ^ k
          * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        ↔ Work.Spaces.SupFinite (fun z θ => (z + 1) ^ k
          * Work.Spaces.pzIter k (Work.Spaces.DthIter j g) z θ
          * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) := by
    intro j k
    refine SupFinite_congr fun z hz θ hθ => ?_
    rw [pzIter_congr (DthIter_congr hfg j) k z (neg_one_lt_of_mem_Iz hz) θ]
  refine ⟨?_, ?_⟩
  · have h1 : (∑ k ∈ Finset.range (l + 1),
          Work.Spaces.supAbs fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k f z θ)
        = ∑ k ∈ Finset.range (l + 1),
          Work.Spaces.supAbs fun z θ => (z + 1) ^ k * Work.Spaces.pzIter k g z θ :=
      Finset.sum_congr rfl fun k _ => hz k
    have h2 : (∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
          if 1 ≤ j ∧ k + j ≤ l then
            Work.Spaces.supAbs fun z θ => (z + 1) ^ k
              * Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
          else 0)
        = ∑ j ∈ Finset.range (l + 1), ∑ k ∈ Finset.range (l + 1),
          if 1 ≤ j ∧ k + j ≤ l then
            Work.Spaces.supAbs fun z θ => (z + 1) ^ k
              * Work.Spaces.pzIter k (Work.Spaces.DthIter j g) z θ
              * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))
          else 0 := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      split_ifs with hc
      · exact hm j k
      · rfl
    simp only [Work.Spaces.WlInf]
    rw [h1, h2]
  · constructor
    · intro h
      exact ⟨fun k hk => (hSFz k).mp (h.1 k hk),
             fun j hj k hk hj1 hkj => (hSFm j k).mp (h.2 j hj k hk hj1 hkj)⟩
    · intro h
      exact ⟨fun k hk => (hSFz k).mpr (h.1 k hk),
             fun j hj k hk hj1 hkj => (hSFm j k).mpr (h.2 j hj k hk hj1 hkj)⟩

end Work.FTS.Nonlinear.FstarPkg
