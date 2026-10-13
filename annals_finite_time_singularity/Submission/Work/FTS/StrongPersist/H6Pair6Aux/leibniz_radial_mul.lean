import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.L12Aux
import Submission.Work.Spaces.mixed_mul_eq
import Submission.Work.FTS.OpenPkg.ProdOpen.leibniz_open_mixed
import Submission.Work.FTS.StrongPersist.H6Aux.DzdIter_mul_of_diff
import Submission.Work.FTS.StrongPersist.L3Rhs.NfkAux.FkSlots

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

open scoped Topology
open Set Filter

noncomputable section

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Auxiliary facts about the one-variable operator `Dzd u = z u'`

The radial factor `z ↦ X z` of the product `(z,θ) ↦ X z * f z θ` is `C^6` on `(0,∞)` only (it
is *not* smooth on a neighbourhood of the closed quadrant, so the derivation-like structures of
`Work.Spaces`, which are stated for `C^∞`-classes, do not apply).  Everything below is therefore
phrased for the one-variable operator `Work.Elliptic.Dzd = z ∂_z` and only asks for the
differentiability actually needed.

The link between the two-dimensional `Work.Spaces.DzIter` and the one-dimensional
`Work.Elliptic.DzdIter` is `Work.Spaces.Zop_slice` (`DzIter` is the iterate of `Zop` on the
`θ`-slice) together with the fact that `Work.Spaces.Zop` is definitionally `Work.Elliptic.Dzd`. -/

/-- The iterate `Zop^[m]` of the one-variable operator `Zop u = z u'` is `DzdIter m`. -/
private lemma Zop_iterate_eq_DzdIter (m : ℕ) (u : ℝ → ℝ) :
    Work.Spaces.Zop^[m] u = Work.Elliptic.DzdIter m u := by
  induction m with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih]; rfl

/-- The mixed derivative `D_z^m g z θ` is the one-variable `DzdIter m` of the `θ`-slice of `g`. -/
private lemma DzIter_eq_DzdIter_slice (g : ℝ → ℝ → ℝ) (m : ℕ) (z θ : ℝ) :
    Work.Spaces.DzIter m g z θ = Work.Elliptic.DzdIter m (fun z' => g z' θ) z := by
  have h := congrFun (Work.Spaces.Zop_slice m g θ) z
  rw [Zop_iterate_eq_DzdIter] at h
  exact h

/-- `DzdIter m` only depends on the values on `(0,∞)`: this is locality of the iterated
one-variable Leibniz derivative `z ∂_z`. -/
private lemma DzdIter_congr_Ioi {A B : ℝ → ℝ} (h : Set.EqOn A B (Set.Ioi 0)) (m : ℕ) :
    Set.EqOn (Work.Elliptic.DzdIter m A) (Work.Elliptic.DzdIter m B) (Set.Ioi 0) := by
  induction m with
  | zero => exact h
  | succ n ih =>
      intro z hz
      show Work.Elliptic.Dzd (Work.Elliptic.DzdIter n A) z
        = Work.Elliptic.Dzd (Work.Elliptic.DzdIter n B) z
      simp only [Work.Elliptic.Dzd]
      rw [ih.deriv isOpen_Ioi hz]

/-! ## The `D_θ`-part of the Leibniz rule -/

/-- A factor `z ↦ X z` depending only on `z` is invisible to `D_θ`: on the open quadrant,
`D_θ^a (X · f) = X · D_θ^a f`. -/
private lemma DthIter_radial_mul {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ (a : ℕ) (z θ : ℝ), 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.DthIter a (fun z θ => X z * f z θ) z θ
        = X z * Work.Spaces.DthIter a f z θ := by
  intro a
  induction a with
  | zero => intro z θ _ _ _; rfl
  | succ n ih =>
      intro z θ hz hθ0 hθ1
      have hmem : Set.Ioo 0 (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds ⟨hθ0, hθ1⟩
      have hslice : (fun θ' => Work.Spaces.DthIter n (fun z θ => X z * f z θ) z θ') =ᶠ[𝓝 θ]
          (fun θ' => X z * Work.Spaces.DthIter n f z θ') := by
        filter_upwards [hmem] with θ' hθ'
        exact ih z θ' hz hθ'.1 hθ'.2
      have hdiff : DifferentiableAt ℝ (fun θ' => Work.Spaces.DthIter n f z θ') θ :=
        (((hf.DthIter n).curry_θ hz).differentiableOn
          Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
          (isOpen_Ioo.mem_nhds ⟨hθ0, hθ1⟩)
      show Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter n
            (fun z θ => X z * f z θ) z θ') θ
        = X z * (Real.sin (2 * θ) * deriv (fun θ' => Work.Spaces.DthIter n f z θ') θ)
      rw [hslice.deriv_eq, deriv_const_mul (X z) hdiff]
      ring

/-! ## The Leibniz rule for a radial factor of class `C^6` -/

/-- **The Leibniz rule `D_z^b D_θ^a (X · f) = Σ_k C(b,k) (D_z^k X)(D_z^{b-k}D_θ^a f)`** for a
radial factor `X` which is `C^6` on `(0,∞)` and a datum `f` smooth on the open quadrant.

The angular derivatives all fall on `f`, and the radial derivatives split by the one-variable
Leibniz rule `DzdIter_mul_of_diff` applied to the `θ`-slice `z ↦ X z · f z θ`. -/
theorem leibniz_radial_mul {X : ℝ → ℝ} {f : ℝ → ℝ → ℝ}
    (hX : ContDiffOn ℝ 6 X (Set.Ioi 0)) (hf : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ (b a : ℕ), b ≤ 6 → ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.mixed b a (fun z θ => X z * f z θ) z θ
        = ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
            * (Work.Elliptic.DzdIter k X z * Work.Spaces.mixed (b - k) a f z θ) := by
  intro b a hb z θ hz hθ0 hθ1
  have hθmem : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  -- the angular part: `D_θ^a (X · f) = X · D_θ^a f` on the quadrant
  have hAgree : Set.EqOn (fun z' => Work.Spaces.DthIter a (fun z θ => X z * f z θ) z' θ)
      (fun z' => X z' * Work.Spaces.DthIter a f z' θ) (Set.Ioi 0) :=
    fun z' hz' => DthIter_radial_mul (X := X) hf a z' θ hz' hθ0 hθ1
  -- step 1: reduce `mixed b a (X·f)` to the one-variable Leibniz derivative of the slice
  have h1 : Work.Spaces.mixed b a (fun z θ => X z * f z θ) z θ
      = Work.Elliptic.DzdIter b (fun z' => X z' * Work.Spaces.DthIter a f z' θ) z := by
    change Work.Spaces.DzIter b (Work.Spaces.DthIter a (fun z θ => X z * f z θ)) z θ
      = Work.Elliptic.DzdIter b (fun z' => X z' * Work.Spaces.DthIter a f z' θ) z
    rw [DzIter_eq_DzdIter_slice]
    exact DzdIter_congr_Ioi hAgree b (Set.mem_Ioi.mpr hz)
  -- the differentiability inputs of the one-variable Leibniz rule
  have hu : ∀ j, j + 1 ≤ b → DifferentiableOn ℝ (Work.Elliptic.DzdIter j X) (Set.Ioi 0) := by
    intro j hj
    refine (Work.FTS.StrongPersist.L3Rhs.NfkAux.contDiffOn_DzdIter_of_radial (r := X) (n := 6)
      (fun m hm => hX.of_le (by exact_mod_cast hm)) (a := j) (t := 1) (by omega)).differentiableOn_one
  have hv : ∀ j, j + 1 ≤ b →
      DifferentiableOn ℝ (Work.Elliptic.DzdIter j (fun z' => Work.Spaces.DthIter a f z' θ))
        (Set.Ioi 0) := by
    intro j hj
    have hslice : DifferentiableOn ℝ (fun z' => Work.Spaces.mixed j a f z' θ) (Set.Ioi 0) :=
      ((hf.mixed j a).curry_z hθmem).differentiableOn Work.FTS.LocData.smoothOrder_ne_zero
    refine hslice.congr (fun z' hz' => ?_)
    exact (DzIter_eq_DzdIter_slice (Work.Spaces.DthIter a f) j z' θ).symm
  -- step 2: the one-variable Leibniz rule for the slice `z ↦ X z · D_θ^a f z θ`
  have h2 : Work.Elliptic.DzdIter b (fun z' => X z' * Work.Spaces.DthIter a f z' θ) z
      = ∑ k ∈ Finset.range (b + 1), (b.choose k : ℝ)
          * (Work.Elliptic.DzdIter k X z
              * Work.Elliptic.DzdIter (b - k)
                  (fun z' => Work.Spaces.DthIter a f z' θ) z) :=
    Work.FTS.StrongPersist.H6Aux.DzdIter_mul_of_diff b X
      (fun z' => Work.Spaces.DthIter a f z' θ) hu hv z (Set.mem_Ioi.mpr hz)
  rw [h1, h2]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← DzIter_eq_DzdIter_slice (Work.Spaces.DthIter a f) (b - k) z θ]
  rfl

end

end Work.FTS.StrongPersist.H6Pair6Aux
