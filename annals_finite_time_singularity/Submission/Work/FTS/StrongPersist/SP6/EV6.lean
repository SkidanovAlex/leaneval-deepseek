import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongPersist.SP6.Flat6Defs
import Submission.Work.FTS.StrongPersist.SP6.F0SixEVzR
import Submission.Work.FTS.StrongPersist.SP6.F0FiveEVzD
import Submission.Work.FTS.StrongPersist.SP6.PthEVzR

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.SP6

set_option autoImplicit false

/-!
# `FTS/StrongPersist/SP6/EV6.lean` — the order-six flat bound of the `EV`-field

`EV Y = (z/(z+1))·EVz Y = (z/(z+1))·(2(cos²θ − 2 sin²θ)·Y + sin(2θ)·∂_θY)` is the fourth of the
five fields of the `SP6` flat package.  This file proves

`FlatW 6 (EV Y) (C·(α+1)·(K + KY + KD))`

from `SmoothOpen Y`, `FlatW 7 Y K`, `Fb 6 KY Y`, `F0 6 KD (Yblk Y)`.

## The route

`FlatW 6 f M` is the pair `F0 6 M f`, `F0 5 M (∂_θf)` (`flatW6_of_F0`), so it suffices to bound
the two blocks

* `F0 6 (64·A·B₁) (EV Y)`   (`B₁` the constant of the `EVz`-block `EVzR Y`),
* `F0 5 (32·A·B₂) (∂_θ(EV Y))` (`B₂` the constant of `EVzD Y`, the candidate `∂_θ`-derivative of
  `EVzR Y`),

where `A` is the constant of `CoefBundle6s` (the radial coefficient `z/(1+z)` is `F0 6 A` and
smooth).  Both are one application of the Leibniz estimate `F0_mul` with the *radial factor*
`r = z/(1+z)`, which is `θ`-free — this is also why `∂_θ(EV Y) = r·∂_θ(EVz Y)`, the identity
`pth (EVR Y) = fun z θ => r·EVzD Y` proved below (`ev_six_pth_EVR`).

The two `EVz`-blocks are exactly the estimates of the sibling tasks, already in the workspace:
`F0SixEVzR` (`F0 6 (C₁·(K+KY)) (EVzR Y)`) and `F0FiveEVzD` (`F0 5 (C₂·(K+KY)) (EVzD Y)`), and
the product-rule identity `PthEVzR` (`∂_θ(EVzR Y) = EVzD Y`) — the `EVz`-fields are *linear* in
the two blocks `Y`, `∂_θY`, so those constants are linear in `K + KY`.

The constant bookkeeping is the elementary Lemma `ev_six_const_bound`: the `EVz`-slot constants
are evaluated at `(K, KY) ↦ (KY, K+KY)` (so that `K + KY ↦ K + 2KY ≤ 2(K+KY+KD)`), giving the
final linear constant.  Since `∃ C` is quantified before the data, `C` absorbs both `A` and the
two numerical constants `C₁`, `C₂` (through their absolute values).
-/

/-- **The constant comparison.**  If `c ≤ 128` and `256·A·(|C|+1) ≤ Cs` (with `A ≥ 0` and the
three block bounds nonnegative), then the `EVz`-slot constant `c·A·(C·(KY + (K+KY)))` is
dominated by the target constant `Cs·(α+1)·(K+KY+KD)`.  Here `KY + (K+KY) = K + 2KY ≤ 2(K+KY+KD)`
is the point where the third block `KD` enters. -/
private theorem ev_six_const_bound {A c C α K KY KD Cs : ℝ} (hA0 : 0 ≤ A) (hα : 0 ≤ α)
    (hK : 0 ≤ K) (hKY : 0 ≤ KY) (hKD : 0 ≤ KD) (hc0 : 0 ≤ c) (hc : c ≤ 128)
    (hCs : 256 * A * (|C| + 1) ≤ Cs) :
    c * A * (C * (KY + (K + KY))) ≤ Cs * (α + 1) * (K + KY + KD) := by
  have hS0 : (0 : ℝ) ≤ K + KY + KD := by linarith
  have hCabs0 : (0 : ℝ) ≤ |C| := abs_nonneg C
  have hCs0 : (0 : ℝ) ≤ Cs :=
    le_trans (mul_nonneg (mul_nonneg (by norm_num) hA0) (by linarith)) hCs
  have hX : C * (KY + (K + KY)) ≤ |C| * (2 * (K + KY + KD)) := by
    have hX1 : C * (KY + (K + KY)) ≤ |C| * (KY + (K + KY)) :=
      mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
    have hX2 : KY + (K + KY) ≤ 2 * (K + KY + KD) := by linarith
    exact le_trans hX1 (mul_le_mul_of_nonneg_left hX2 hCabs0)
  have h2S0 : (0 : ℝ) ≤ |C| * (2 * (K + KY + KD)) := mul_nonneg hCabs0 (by linarith)
  have hA0' : (0 : ℝ) ≤ 256 * A := mul_nonneg (by norm_num) hA0
  calc c * A * (C * (KY + (K + KY)))
      ≤ c * A * (|C| * (2 * (K + KY + KD))) := mul_le_mul_of_nonneg_left hX (mul_nonneg hc0 hA0)
    _ ≤ 128 * A * (|C| * (2 * (K + KY + KD))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hA0) h2S0
    _ = 256 * A * |C| * (K + KY + KD) := by ring
    _ ≤ 256 * A * (|C| + 1) * (K + KY + KD) := by
        have hle2 : |C| * (K + KY + KD) ≤ (|C| + 1) * (K + KY + KD) :=
          mul_le_mul_of_nonneg_right (by linarith) hS0
        calc 256 * A * |C| * (K + KY + KD) = (256 * A) * (|C| * (K + KY + KD)) := by ring
          _ ≤ (256 * A) * ((|C| + 1) * (K + KY + KD)) :=
              mul_le_mul_of_nonneg_left hle2 hA0'
          _ = 256 * A * (|C| + 1) * (K + KY + KD) := by ring
    _ ≤ Cs * (K + KY + KD) := mul_le_mul_of_nonneg_right hCs hS0
    _ ≤ Cs * (α + 1) * (K + KY + KD) := by
        have h1α : (1 : ℝ) ≤ α + 1 := by linarith
        calc Cs * (K + KY + KD) ≤ (Cs * (α + 1)) * (K + KY + KD) :=
              mul_le_mul_of_nonneg_right (le_mul_of_one_le_right hCs0 h1α) hS0
          _ = Cs * (α + 1) * (K + KY + KD) := by ring

/-- **`∂_θ(EVR Y) = (z/(1+z))·EVzD Y` on the open quadrant.**  The radial factor `z/(1+z)` is
`θ`-free, so the product rule degenerates to `∂_θ(r·EVzR Y) = r·∂_θ(EVzR Y)`, and the second
factor is `EVzD Y` by `PthEVzR`. -/
private theorem ev_six_pth_EVR {Y : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Y)
    (hSmoothZ : Work.FTS.EllipticEst.SmoothOpen (EVzR Y))
    (hrhos : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z))) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (EVR Y) z θ = (z / (1 + z)) * EVzD Y z θ := by
  intro z θ hz hθ hθ'
  show Work.Spaces.pth (fun z θ : ℝ => z / (1 + z) * EVzR Y z θ) z θ
    = z / (1 + z) * EVzD Y z θ
  rw [Work.FTS.PhiStar.CoreAux.Fbq_pth_mul
    (f := fun z _ : ℝ => z / (1 + z)) (g := EVzR Y) hrhos hSmoothZ z θ hz hθ hθ']
  have hr : Work.Spaces.pth (fun z _ : ℝ => z / (1 + z)) z θ = 0 := by
    show deriv (fun _ : ℝ => z / (1 + z)) θ = 0
    rw [deriv_const]
  rw [hr, zero_mul, zero_add, PthEVzR Y hsm z θ hz hθ hθ']

/-- **The order-six flat bound of the `EV`-star-field**, `EV Y = (z/(z+1))·EVz Y`.

Prove `FlatW 6 (EV Y) M` with `M := C·(α+1)·(K+KY+KD)` from `SmoothOpen Y`, `FlatW 7 Y K`,
`Fb 6 KY Y`, `F0 6 KD (Yblk Y)`; the constant must stay **linear** in `K + KY + KD`.

Import `Submission.Work.FTS.StrongPersist.SP6.Flat6Defs`: `CoefBundle6s`, `atomData`,
`EVzR`/`EVzD`, `EVR`/`EVD` and `evEVR_eq`, `flatW6_of_F0`, `FlatW_mono6`, `mono_const`,
`pth_thetaOnly`. Recommended route: prove the strong pair `F0 6 (EVR Y)` and
`F0 5 (pth (EVR Y))` (the second is `F0 5 (EVD Y)` since `z/(z+1)` is `θ`-free), where the
`EVz R`-parts are the same estimates as in the `EVz`-task (you may redo them here, or reduce to
a generic radial-factor lemma: if `F0 6 r A`, `F0 5 r A` for `r = fun z θ => z/(1+z)` and
`F0 6 (EVzR Y) B`, `F0 5 (EVzD Y) B`, then `F0_mul` gives `F0 6 (EVR Y) (32·A·B)` and
`F0 5 (EVD Y) (32·A·B)`). Then `F0_congr` + `flatW6_of_F0`. The sibling
`Submission/Work/FTS/PhiStar/CoreAux/Fb_EV_bound.lean` proves the order-**four** version of the
joint statement for `EVz` and `EV`. -/
theorem EV6 : ∃ C : ℝ, 0 < C ∧ ∀ (α K KY KD : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ α → 0 ≤ K → 0 ≤ KY → 0 ≤ KD → Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.VocabO2.FlatW 7 Y K → Work.FTS.PhiStar.Fb 6 KY Y →
    Work.FTS.PhiStar.F0 6 KD (Work.FTS.PhiStar.Yblk Y) →
    Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EV Y) (C * (α + 1) * (K + KY + KD)) := by
  obtain ⟨A, hA1, hcoef⟩ := CoefBundle6s
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA1
  obtain ⟨C₁, _hC₁pos, hC₁⟩ := F0SixEVzR
  obtain ⟨C₂, _hC₂pos, hC₂⟩ := F0FiveEVzD
  refine ⟨max 1 (256 * A * (|C₁| + |C₂| + 1)), lt_max_of_lt_left (by norm_num), ?_⟩
  intro α K KY KD Y hα hK hKY hKD hsm hW hFb _hD
  -- the two block bounds
  have hY : Work.FTS.PhiStar.F0 6 KY Y := hFb.f0
  have hPY : Work.FTS.PhiStar.F0 6 (K + KY) (Work.Spaces.pth Y) :=
    (Work.FTS.PhiStar.CoreAux.F0_six_pth_of_FlatW hW).mono le_rfl (by linarith)
  have hK0 : (0 : ℝ) ≤ K + KY := by linarith
  -- the two `EVz`-bounds (the estimates of the sibling `EVz`-tasks)
  have hZ : Work.FTS.PhiStar.F0 6 (C₁ * (KY + (K + KY))) (EVzR Y) :=
    hC₁ KY (K + KY) Y hKY hK0 hsm hY hPY
  have hZd : Work.FTS.PhiStar.F0 5 (C₂ * (KY + (K + KY))) (EVzD Y) :=
    hC₂ KY (K + KY) Y hKY hK0 hsm hY hPY
  have hZ0 : (0 : ℝ) ≤ C₁ * (KY + (K + KY)) := Work.FTS.PhiStar.CoreAux.Fbq_nonneg_of_F0 hZ
  have hZd0 : (0 : ℝ) ≤ C₂ * (KY + (K + KY)) := Work.FTS.PhiStar.CoreAux.Fbq_nonneg_of_F0 hZd
  -- the radial coefficient `z/(1+z)`
  have hrho := hcoef (fun z _ : ℝ => z / (1 + z)) (by simp [coefFun])
  have hrhos : Work.FTS.EllipticEst.SmoothOpen (fun z _ : ℝ => z / (1 + z)) := hrho.2
  have hrho5 : Work.FTS.PhiStar.F0 5 A (fun z _ : ℝ => z / (1 + z)) :=
    hrho.1.mono (by norm_num) le_rfl
  -- smoothness of the two `EVz`-blocks
  have hφs : Work.FTS.EllipticEst.SmoothOpen
      (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) :=
    (hcoef (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) (by simp [coefFun])).2
  have hσs : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.sin (2 * θ)) :=
    (hcoef (fun _ θ : ℝ => Real.sin (2 * θ)) (by simp [coefFun])).2
  have hSmoothZ : Work.FTS.EllipticEst.SmoothOpen (EVzR Y) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.add
      (Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul
        (Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul hφs 2) hsm)
      (Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul hσs hsm.pth)
  have hSmoothD : Work.FTS.EllipticEst.SmoothOpen (EVzD Y) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.congr hSmoothZ.pth (PthEVzR Y hsm)
  -- `F0 6` of `EV Y`: multiply the `EVzR`-block by the radial factor
  have h1 : Work.FTS.PhiStar.F0 6 ((2 : ℝ) ^ 6 * A * (C₁ * (KY + (K + KY))))
      (fun z θ : ℝ => (z / (1 + z)) * EVzR Y z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_mul hA0 hZ0 hrhos hSmoothZ hrho.1 hZ
  have h1a : Work.FTS.PhiStar.F0 6 (64 * A * (C₁ * (KY + (K + KY))))
      (fun z θ : ℝ => (z / (1 + z)) * EVzR Y z θ) := h1.mono le_rfl (by norm_num)
  have h1b : Work.FTS.PhiStar.F0 6 (64 * A * (C₁ * (KY + (K + KY))))
      (Work.FTS.PhiStar.EV Y) :=
    Work.FTS.PhiStar.CoreAux.F0_congr (fun z θ _ _ _ => evEVR_eq Y z θ) h1a
  -- `F0 5` of `∂_θ(EV Y)`: multiply the `EVzD`-block by the radial factor
  have h2 : Work.FTS.PhiStar.F0 5 ((2 : ℝ) ^ 5 * A * (C₂ * (KY + (K + KY))))
      (fun z θ : ℝ => (z / (1 + z)) * EVzD Y z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_mul hA0 hZd0 hrhos hSmoothD hrho5 hZd
  have h2a : Work.FTS.PhiStar.F0 5 (32 * A * (C₂ * (KY + (K + KY))))
      (fun z θ : ℝ => (z / (1 + z)) * EVzD Y z θ) := h2.mono le_rfl (by norm_num)
  have h2b : Work.FTS.PhiStar.F0 5 (32 * A * (C₂ * (KY + (K + KY))))
      (Work.Spaces.pth (EVR Y)) :=
    Work.FTS.PhiStar.CoreAux.F0_congr
      (fun z θ => ev_six_pth_EVR hsm hSmoothZ hrhos z θ) h2a
  have h2c : Work.FTS.PhiStar.F0 5 (32 * A * (C₂ * (KY + (K + KY))))
      (Work.Spaces.pth (Work.FTS.PhiStar.EV Y)) :=
    Work.FTS.PhiStar.CoreAux.F0_congr
      (pth_congr6 (fun z θ _ _ _ => evEVR_eq Y z θ)) h2b
  -- the two constant comparisons
  have hCs1 : 256 * A * (|C₁| + 1) ≤ max 1 (256 * A * (|C₁| + |C₂| + 1)) := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hA0))
      (le_max_right _ _)
    have h2' := abs_nonneg C₂
    linarith
  have hCs2 : 256 * A * (|C₂| + 1) ≤ max 1 (256 * A * (|C₁| + |C₂| + 1)) := by
    refine le_trans (mul_le_mul_of_nonneg_left ?_ (mul_nonneg (by norm_num) hA0))
      (le_max_right _ _)
    have h1' := abs_nonneg C₁
    linarith
  have hb1 := ev_six_const_bound (c := 64) (C := C₁) hA0 hα hK hKY hKD (by norm_num)
    (by norm_num) hCs1
  have hb2 := ev_six_const_bound (c := 32) (C := C₂) hA0 hα hK hKY hKD (by norm_num)
    (by norm_num) hCs2
  refine flatW6_of_F0 ?_ ?_
  · exact h1b.mono le_rfl hb1
  · exact h2c.mono le_rfl hb2

end Work.FTS.StrongPersist.SP6
