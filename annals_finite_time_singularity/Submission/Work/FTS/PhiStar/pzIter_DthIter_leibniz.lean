import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.PhiStar.Psi0Est.Defs
import Submission.Work.FTS.H2.STFacts
import Submission.Work.FTS.NonlinRows.sqm_pz_DthIter_mul_le_4_open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology

namespace Work.FTS.PhiStar

set_option maxHeartbeats 1000000

/-! ## The Leibniz rule for `∂_z^k D_θ^j f`

Write `L = D_θ = sin(2θ) ∂_θ`.  Since `L f = (sin 2·) · ∂_θ f` and `L` is a derivation, the
`j`-th iterate of `L` applied to `f` satisfies the binomial expansion

`L^j f = ∑_{a<j} C(j-1,a) · (L^a (sin 2·)) · (L^{j-1-a} (∂_θ f))`,

because `L^j f = L^{j-1}(L f) = L^{j-1}((sin 2·)·∂_θ f)`.  The statement below is the `k`-fold
`z`-derivative of this identity; since `L^a (sin 2·)` does not depend on `z`, the `z`-derivatives
pass through the coefficients, and all the mixed `∂_z^c`-terms with `c ≥ 1` on the `sin 2·`-factor
vanish. -/

/-- `θ ↦ sin(2θ)` (viewed as a function of `(z,θ)`) is smooth on the open quadrant. -/
private theorem smoothOpen_Sfun : Work.FTS.EllipticEst.SmoothOpen Work.FTS.H2.Sfun := by
  have hsin : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => Real.sin (2 * p.2))
      Work.FTS.EllipticEst.Q0 :=
    (Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn
  exact hsin

/-- `D_θ` sends functions which do not depend on `z` to functions which do not depend on `z`. -/
private theorem Dth_zindep {u : ℝ → ℝ → ℝ} (h : ∀ z θ, u z θ = u 0 θ) (z θ : ℝ) :
    Work.Spaces.Dth u z θ = Work.Spaces.Dth u 0 θ := by
  show Real.sin (2 * θ) * Work.Spaces.pth u z θ = Real.sin (2 * θ) * Work.Spaces.pth u 0 θ
  congr 1
  show deriv (fun θ' => u z θ') θ = deriv (fun θ' => u 0 θ') θ
  congr 1
  funext θ'
  exact h z θ'

/-- Every `D_θ`-iterate of `sin 2·` is independent of `z`. -/
private theorem DthIter_Sfun_zindep (a : ℕ) (z θ : ℝ) :
    Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ
      = Work.Spaces.DthIter a Work.FTS.H2.Sfun 0 θ := by
  induction a generalizing z θ with
  | zero => rfl
  | succ a ih => exact Dth_zindep (fun z' θ' => ih z' θ') z θ

/-- Any positive `z`-derivative of `D_θ^a (sin 2·)` vanishes (the function is a function of
`θ` alone). -/
private theorem pzIter_DthIter_Sfun_eq_zero (a c : ℕ) (hc : 1 ≤ c) (z θ : ℝ) :
    Work.Spaces.pzIter c (Work.Spaces.DthIter a Work.FTS.H2.Sfun) z θ = 0 := by
  rw [Work.Spaces.pzIter_eq_iteratedDeriv]
  have hconst : (fun z' => Work.Spaces.DthIter a Work.FTS.H2.Sfun z' θ)
      = fun _ => Work.Spaces.DthIter a Work.FTS.H2.Sfun 0 θ := by
    funext z'
    exact DthIter_Sfun_zindep a z' θ
  rw [hconst, iteratedDeriv_const]
  rcases c with _ | c
  · omega
  · simp

/-- `D_θ^j f = D_θ^{j-1}((sin 2·)·∂_θ f)`: the definitional identity `D_θ f = (sin 2·)·∂_θ f`,
iterated. -/
private theorem DthIter_eq_DthIter_pred_mul (j : ℕ) (hj : 1 ≤ j) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.DthIter j f
      = Work.Spaces.DthIter (j - 1)
          (fun z θ => Work.FTS.H2.Sfun z θ * Work.Spaces.pth f z θ) := by
  rw [← Nat.sub_add_cancel hj, ← Work.Spaces.DthIter_add_right (j - 1) 1 f]
  rfl

theorem pzIter_DthIter_leibniz {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {j k : ℕ} (hj : 1 ≤ j) {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pzIter k (Work.Spaces.DthIter j f) z θ =
      ∑ a ∈ Finset.range j, ((j - 1).choose a : ℝ) *
        (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
          Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f)) z θ) := by
  have hpth : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth f) :=
    Work.FTS.EllipticEst.SmoothOpen.pth hf
  -- Write `D_θ^j f` as the `(j-1)`-st iterate of `D_θ` applied to the product `(sin 2·)·∂_θ f`.
  rw [DthIter_eq_DthIter_pred_mul j hj f,
    -- and use the Leibniz rule for `∂_z^k D_θ^{j-1}` on that product.
    Work.FTS.NonlinRows.sqo_pz_DthIter_mul_eq (k := k) (j := j - 1) (f := Work.FTS.H2.Sfun)
      (g := Work.Spaces.pth f) smoothOpen_Sfun hpth z hz θ hθ,
    Nat.sub_add_cancel hj]
  refine Finset.sum_congr rfl fun a _ => ?_
  -- Only the `c = 0` term of the inner sum survives: `D_θ^a (sin 2·)` is constant in `z`.
  have hsingle : (∑ c ∈ Finset.range (k + 1), ((j - 1).choose a : ℝ) * (k.choose c : ℝ) *
        (Work.Spaces.pzIter c (Work.Spaces.DthIter a Work.FTS.H2.Sfun) z θ *
          Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f))
            z θ))
      = ((j - 1).choose a : ℝ) *
        (Work.Spaces.DthIter a Work.FTS.H2.Sfun z θ *
          Work.Spaces.pzIter k (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f)) z θ) := by
    refine (Finset.sum_eq_single (s := Finset.range (k + 1))
      (f := fun c => ((j - 1).choose a : ℝ) * (k.choose c : ℝ) *
        (Work.Spaces.pzIter c (Work.Spaces.DthIter a Work.FTS.H2.Sfun) z θ *
          Work.Spaces.pzIter (k - c) (Work.Spaces.DthIter (j - 1 - a) (Work.Spaces.pth f))
            z θ)) 0 ?_ ?_).trans ?_
    · intro c _ hc0
      have hc1 : 1 ≤ c := Nat.one_le_iff_ne_zero.mpr hc0
      rw [pzIter_DthIter_Sfun_eq_zero a c hc1 z θ]
      ring
    · intro h0
      exact absurd (Finset.mem_range.mpr (Nat.succ_pos k)) h0
    · simp only [Nat.choose_zero_right, Nat.cast_one, Work.Spaces.pzIter_zero, Nat.sub_zero]
      ring
  exact hsingle

end Work.FTS.PhiStar
