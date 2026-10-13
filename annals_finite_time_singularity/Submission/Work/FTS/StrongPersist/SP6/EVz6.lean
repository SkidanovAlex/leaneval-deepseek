import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Submission.Work.FTS.StrongPersist.SP6.Flat6Defs
import Submission.Work.FTS.StrongPersist.SP6.F0SixEVzR

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.SP6

set_option maxHeartbeats 1000000

/-! ## The two halves of the order-six bound of `EVz`

`Work.FTS.PhiStar.EVz Y = 2(cos²θ − 2 sin²θ)·Y + sin(2θ)·∂_θY` is a sum of two products of a
fixed smooth angular coefficient with one of the blocks `Y`, `∂_θY`, so it is bounded by the
bilinear flat calculus (`F0_mul` never squares the block constant).  The file `F0SixEVzR.lean`
already supplies the first half,

`∃ C, ∀ K KY Y, F0 6 K Y → F0 6 KY (∂_θY) → F0 6 (C·(K+KY)) (EVzR Y)`,

and here we add

* the pointwise identity `∂_θ(EVzR Y) = EVzD Y` on the open quadrant (product rule, plus
  `∂_θ(cos² − 2 sin²) = −3 sin 2θ` and `∂_θ(sin 2·) = 2 cos 2·` — in the form in which the
  product rule produces them, i.e. as `deriv (fun θ' => …) θ`);
* the second half `∃ C, ∀ K KY Y, F0 6 K Y → F0 6 KY (∂_θY) → F0 5 (C·(K+KY)) (EVzD Y)`.

The assembly is then `F0_congr` (`EVz Y = EVzR Y`), `flatW6_of_F0`, and the arithmetic
`mono_const` of `Flat6Defs`. -/

/-- **The `∂_θ`-identity of the reassociated `EVz`-field.**  On the open quadrant the
`θ`-derivative of `EVzR Y` is the explicit expression `EVzD Y`: the product rule applied to the
two summands `2(cos²θ − 2 sin²θ)·Y` and `sin(2θ)·∂_θY`, with `∂_θ(sin 2θ)·∂_θY` split off and
`sin(2θ)·∂_θ(∂_θY) = D_θ(∂_θY)`. -/
private theorem evz6_pth_Q0 (Y : ℝ → ℝ → ℝ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen Y) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (EVzR Y) z θ = EVzD Y z θ := by
  have hc2 : Work.FTS.EllipticEst.SmoothOpen
      (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) := by
    refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
    have h : Function.uncurry (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)
        = fun p : ℝ × ℝ => Real.cos p.2 ^ 2 - 2 * Real.sin p.2 ^ 2 := rfl
    rw [h]
    fun_prop
  have hc3 : Work.FTS.EllipticEst.SmoothOpen (fun _ θ : ℝ => Real.sin (2 * θ)) := by
    refine Work.FTS.EllipticEst.smoothOpen_of_forall fun n => ?_
    have h : Function.uncurry (fun _ θ : ℝ => Real.sin (2 * θ))
        = fun p : ℝ × ℝ => Real.sin (2 * p.2) := rfl
    rw [h]
    fun_prop
  have hs1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Y z θ) :=
    Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul
      (Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul hc2 2) hsm
  have hs2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => Real.sin (2 * θ) * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul hc3 hsm.pth
  have hd2' : deriv (fun θ' : ℝ => 2 * (Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2))
      = fun θ => 2 * deriv (fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ := by
    funext θ
    exact deriv_const_mul_field (x := θ)
      (v := fun θ' : ℝ => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) (2 : ℝ)
  intro z θ hz hθ hθ'
  let A1 : ℝ → ℝ → ℝ := fun z θ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Y z θ
  let A2 : ℝ → ℝ → ℝ := fun z θ => Real.sin (2 * θ) * Work.Spaces.pth Y z θ
  have hs1' : Work.FTS.EllipticEst.SmoothOpen A1 := hs1
  have hs2' : Work.FTS.EllipticEst.SmoothOpen A2 := hs2
  have hsplit : EVzR Y = fun z θ => A1 z θ + A2 z θ := by
    funext a b
    simp only [A1, A2, EVzR]
  have hd1 : Work.Spaces.pth A1 z θ
      = Work.Spaces.pth (fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) z θ * Y z θ
        + (2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) * Work.Spaces.pth Y z θ := by
    have h := Work.FTS.PhiStar.CoreAux.Fbq_pth_mul
      (f := fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) (g := Y)
      (Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul hc2 2) hsm z θ hz hθ hθ'
    simpa only [A1] using h
  have hd2 : Work.Spaces.pth A2 z θ
      = Work.Spaces.pth (fun z θ : ℝ => Real.sin (2 * θ)) z θ * Work.Spaces.pth Y z θ
        + Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.pth Y) z θ := by
    have h := Work.FTS.PhiStar.CoreAux.Fbq_pth_mul
      (f := fun z θ : ℝ => Real.sin (2 * θ)) (g := Work.Spaces.pth Y) hc3 hsm.pth
      z θ hz hθ hθ'
    simpa only [A2] using h
  have hsum : Work.Spaces.pth (EVzR Y) z θ
      = Work.Spaces.pth A1 z θ + Work.Spaces.pth A2 z θ := by
    rw [hsplit]
    exact Work.FTS.PhiStar.CoreAux.pth_add_Q0 (f := A1) (g := A2) hs1' hs2' z θ hz hθ hθ'
  rw [hsum, hd1, hd2,
    pth_thetaOnly (fun θ' : ℝ => 2 * (Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2)),
    hd2',
    pth_thetaOnly (fun θ' : ℝ => Real.sin (2 * θ'))]
  simp only [EVzD, Work.Spaces.Dth]
  ring

/-- **The second half of the order-six bound of `EVz`**: the `F0 5`-bound of the reassociated
`θ`-derivative `EVzD Y`, linear in the two block constants `K` (of `Y`) and `KY` (of `∂_θY`).

`EVzD Y` is the sum of four products: `(2·∂_θ(cos²−2sin²))·Y`, `(2(cos²−2sin²))·∂_θY`,
`(∂_θ sin 2·)·∂_θY` and `D_θ(∂_θY)`.  The first three are `F0_mul` of a coefficient with
constant `2A` (resp. `A`) and a block with constant `K` (resp. `KY`); the last is `F0_Dth` of
`F0 6 KY (∂_θY)`, which costs one angular order. -/
private theorem evz6_f0five : ∃ C : ℝ, 0 < C ∧ ∀ (K KY : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ K → 0 ≤ KY → Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.PhiStar.F0 6 K Y → Work.FTS.PhiStar.F0 6 KY (Work.Spaces.pth Y) →
    Work.FTS.PhiStar.F0 5 (C * (K + KY)) (EVzD Y) := by
  obtain ⟨A, hA1, hcoef⟩ := CoefBundle6s
  have hA0 : (0 : ℝ) ≤ A := le_trans zero_le_one hA1
  refine ⟨200 * A, by linarith, ?_⟩
  intro K KY Y hK hKY hsm hY hdY
  -- the three coefficient functions and their level-`5` bounds
  have hc2 := hcoef (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) (by simp [coefFun])
  have hc6 := hcoef (fun _ θ : ℝ => deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ)
    (by simp [coefFun])
  have hc7 := hcoef (fun _ θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ) (by simp [coefFun])
  have hc2' : Work.FTS.PhiStar.F0 5 A (fun _ θ : ℝ => Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) :=
    hc2.1.mono (by norm_num) le_rfl
  have hc6' : Work.FTS.PhiStar.F0 5 A
      (fun _ θ : ℝ => deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) :=
    hc6.1.mono (by norm_num) le_rfl
  have hc7' : Work.FTS.PhiStar.F0 5 A
      (fun _ θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ) :=
    hc7.1.mono (by norm_num) le_rfl
  -- the coefficients doubled by the factor `2` in `EVzD`
  have h2c6 : Work.FTS.PhiStar.F0 5 (2 * A)
      (fun z θ : ℝ => 2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (2 : ℝ) hc6'
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
    exact h
  have h2c2 : Work.FTS.PhiStar.F0 5 (2 * A)
      (fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) := by
    have h := Work.FTS.PhiStar.CoreAux.F0_const_mul (2 : ℝ) hc2'
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at h
    exact h
  have s2c6 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul hc6.2 2
  have s2c2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.const_mul hc2.2 2
  -- the blocks
  have hY5 : Work.FTS.PhiStar.F0 5 K Y := hY.mono (by norm_num) le_rfl
  have hdY5 : Work.FTS.PhiStar.F0 5 KY (Work.Spaces.pth Y) := hdY.mono (by norm_num) le_rfl
  have hddY : Work.FTS.PhiStar.F0 5 KY (Work.Spaces.Dth (Work.Spaces.pth Y)) :=
    Work.FTS.PhiStar.CoreAux.F0_Dth (n := 5) hdY
  -- the four summands
  have t1 : Work.FTS.PhiStar.F0 5 ((2 : ℝ) ^ 5 * (2 * A) * K)
      (fun z θ : ℝ => 2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ * Y z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_mul (n := 5) (mul_nonneg (by norm_num) hA0) hK s2c6 hsm
      h2c6 hY5
  have t2 : Work.FTS.PhiStar.F0 5 ((2 : ℝ) ^ 5 * (2 * A) * KY)
      (fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2)
        * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_mul (n := 5) (mul_nonneg (by norm_num) hA0) hKY s2c2 hsm.pth
      h2c2 hdY5
  have t3 : Work.FTS.PhiStar.F0 5 ((2 : ℝ) ^ 5 * A * KY)
      (fun z θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ
        * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_mul (n := 5) hA0 hKY hc7.2 hsm.pth hc7' hdY5
  -- the smoothness of the summands
  have st1 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ * Y z θ) :=
    Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul s2c6 hsm
  have st2 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul s2c2 hsm.pth
  have st3 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.Fbq_smoothOpen_mul hc7.2 hsm.pth
  have st4 : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dth (Work.Spaces.pth Y)) :=
    hsm.pth.Dth
  have st12 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => 2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ * Y z θ
        + 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.add st1 st2
  have st123 : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ : ℝ => (2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ * Y z θ
        + 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Work.Spaces.pth Y z θ)
        + deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.SmoothOpen.add st12 st3
  -- the three sums
  have h12 : Work.FTS.PhiStar.F0 5 ((2 : ℝ) ^ 5 * (2 * A) * K + (2 : ℝ) ^ 5 * (2 * A) * KY)
      (fun z θ : ℝ => 2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ * Y z θ
        + 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_add st1 st2 t1 t2
  have h123 : Work.FTS.PhiStar.F0 5
      ((2 : ℝ) ^ 5 * (2 * A) * K + (2 : ℝ) ^ 5 * (2 * A) * KY + (2 : ℝ) ^ 5 * A * KY)
      (fun z θ : ℝ => (2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ * Y z θ
        + 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Work.Spaces.pth Y z θ)
        + deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_add st12 st3 h12 t3
  have h1234 : Work.FTS.PhiStar.F0 5
      ((2 : ℝ) ^ 5 * (2 * A) * K + (2 : ℝ) ^ 5 * (2 * A) * KY + (2 : ℝ) ^ 5 * A * KY + KY)
      (fun z θ : ℝ =>
        ((2 * deriv (fun θ' => Real.cos θ' ^ 2 - 2 * Real.sin θ' ^ 2) θ * Y z θ
          + 2 * (Real.cos θ ^ 2 - 2 * Real.sin θ ^ 2) * Work.Spaces.pth Y z θ)
          + deriv (fun θ' => Real.sin (2 * θ')) θ * Work.Spaces.pth Y z θ)
        + Work.Spaces.Dth (Work.Spaces.pth Y) z θ) :=
    Work.FTS.PhiStar.CoreAux.F0_add st123 st4 h123 hddY
  -- transfer to `EVzD Y`
  have hEVzD : Work.FTS.PhiStar.F0 5
      ((2 : ℝ) ^ 5 * (2 * A) * K + (2 : ℝ) ^ 5 * (2 * A) * KY + (2 : ℝ) ^ 5 * A * KY + KY)
      (EVzD Y) :=
    Work.FTS.PhiStar.CoreAux.F0_congr (fun z θ _ _ _ => by
      simp only [EVzD, Work.Spaces.Dth]) h1234
  refine hEVzD.mono le_rfl ?_
  have hAK0 : (0 : ℝ) ≤ A * K := mul_nonneg hA0 hK
  have hAKY0 : (0 : ℝ) ≤ A * KY := mul_nonneg hA0 hKY
  have h1 : (2 : ℝ) ^ 5 * (2 * A) * K + (2 : ℝ) ^ 5 * (2 * A) * KY + (2 : ℝ) ^ 5 * A * KY + KY
      = 64 * A * K + 96 * A * KY + KY := by norm_num; ring
  rw [h1]
  nlinarith [hA1, hK, hKY, hAK0, hAKY0]

/-- **The order-six flat bound of the `EVz`-star-field.**

Prove `FlatW 6 (EVz Y) M` with `M := C·(α+1)·(K+KY+KD)` from `SmoothOpen Y`, `FlatW 7 Y K`,
`Fb 6 KY Y`, `F0 6 KD (Yblk Y)`; the constant must stay **linear** in `K + KY + KD`.

Import `Submission.Work.FTS.StrongPersist.SP6.Flat6Defs`, which provides `CoefBundle6s`
(one `A ≥ 1` with `F0 6 A c` and `SmoothOpen c` for the ten coefficient functions `coefFun`),
`atomData` (the block bounds, including `F0 5 (K+KY) (Dth (pth Y))` for the `Tblk`-slot),
`EVzR`/`EVzD` and `evzEVzR_eq`, `flatW6_of_F0`, `FlatW_mono6`, `mono_const`, `pth_thetaOnly`.
Natural route: the strong pair `F0 6 (EVzR Y)` and `F0 5 (pth (EVzR Y))` (`pth (EVzR Y) = EVzD Y`
on `Q0`, via `Fbq_pth_mul`, `deriv_cos_sq_sub`, `deriv_sin_two`), then `F0_congr` and
`flatW6_of_F0`. The sibling `Submission/Work/FTS/PhiStar/CoreAux/Fb_EV_bound.lean` proves the
order-**four** version. -/
theorem EVz6 : ∃ C : ℝ, 0 < C ∧ ∀ (α K KY KD : ℝ) (Y : ℝ → ℝ → ℝ),
    0 ≤ α → 0 ≤ K → 0 ≤ KY → 0 ≤ KD → Work.FTS.EllipticEst.SmoothOpen Y →
    Work.FTS.VocabO2.FlatW 7 Y K → Work.FTS.PhiStar.Fb 6 KY Y →
    Work.FTS.PhiStar.F0 6 KD (Work.FTS.PhiStar.Yblk Y) →
    Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EVz Y) (C * (α + 1) * (K + KY + KD)) := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := F0SixEVzR
  obtain ⟨C₂, hC₂0, hC₂⟩ := evz6_f0five
  refine ⟨2 * C₁ + 2 * C₂ + 1, by linarith, ?_⟩
  intro α K KY KD Y hα hK hKY hKD hsm hW hFb hD
  set S : ℝ := K + KY + KD with hSdef
  have hS0 : (0 : ℝ) ≤ S := by rw [hSdef]; linarith
  have hY : Work.FTS.PhiStar.F0 6 S Y := hFb.f0.mono le_rfl (by rw [hSdef]; linarith)
  have hPY : Work.FTS.PhiStar.F0 6 S (Work.Spaces.pth Y) :=
    (Work.FTS.PhiStar.CoreAux.F0_six_pth_of_FlatW hW).mono le_rfl (by rw [hSdef]; linarith)
  have hR : Work.FTS.PhiStar.F0 6 (C₁ * (S + S)) (EVzR Y) := hC₁ S S Y hS0 hS0 hsm hY hPY
  have hD5 : Work.FTS.PhiStar.F0 5 (C₂ * (S + S)) (EVzD Y) := hC₂ S S Y hS0 hS0 hsm hY hPY
  have hEVz : Work.FTS.PhiStar.F0 6 (C₁ * (S + S)) (Work.FTS.PhiStar.EVz Y) :=
    Work.FTS.PhiStar.CoreAux.F0_congr (fun z θ _ _ _ => evzEVzR_eq Y z θ) hR
  have hpth : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (Work.FTS.PhiStar.EVz Y) z θ = EVzD Y z θ := by
    intro z θ hz hθ hθ'
    rw [pth_congr6 (fun z θ _ _ _ => evzEVzR_eq Y z θ) z θ hz hθ hθ']
    exact evz6_pth_Q0 Y hsm z θ hz hθ hθ'
  have hPEVz : Work.FTS.PhiStar.F0 5 (C₂ * (S + S))
      (Work.Spaces.pth (Work.FTS.PhiStar.EVz Y)) :=
    Work.FTS.PhiStar.CoreAux.F0_congr hpth hD5
  have hSS0 : (0 : ℝ) ≤ S + S := by linarith
  have hle1 : C₁ * (S + S) ≤ (C₁ + C₂) * (S + S) :=
    mul_le_mul_of_nonneg_right (by linarith) hSS0
  have hle2 : C₂ * (S + S) ≤ (C₁ + C₂) * (S + S) :=
    mul_le_mul_of_nonneg_right (by linarith) hSS0
  have hEVz' : Work.FTS.PhiStar.F0 6 ((C₁ + C₂) * (S + S)) (Work.FTS.PhiStar.EVz Y) :=
    hEVz.mono le_rfl hle1
  have hPEVz' : Work.FTS.PhiStar.F0 5 ((C₁ + C₂) * (S + S))
      (Work.Spaces.pth (Work.FTS.PhiStar.EVz Y)) := hPEVz.mono le_rfl hle2
  have hflat : Work.FTS.VocabO2.FlatW 6 (Work.FTS.PhiStar.EVz Y) ((C₁ + C₂) * (S + S)) :=
    flatW6_of_F0 hEVz' hPEVz'
  refine FlatW_mono6 hflat ?_
  have hα1 : (1 : ℝ) ≤ α + 1 := by linarith
  have hC12 : 2 * (C₁ + C₂) ≤ 2 * C₁ + 2 * C₂ + 1 := by linarith
  calc (C₁ + C₂) * (S + S) = (2 * (C₁ + C₂)) * S := by ring
    _ ≤ ((2 * C₁ + 2 * C₂ + 1) * (α + 1)) * S := by
          apply mul_le_mul_of_nonneg_right _ hS0
          nlinarith [hα1, hC12]
    _ = (2 * C₁ + 2 * C₂ + 1) * (α + 1) * S := by ring

end Work.FTS.StrongPersist.SP6
