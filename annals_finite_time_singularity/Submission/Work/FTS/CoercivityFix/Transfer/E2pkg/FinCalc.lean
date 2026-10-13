/-
# `Transfer/E2pkg/FinCalc.lean` — finite-order calculus for the `E2`-package

The `Comm2w`-wiring of the transfer needs, for a function `G` that is only `C^k` on the open
quadrant (the defects `E1 α f`, `E2 α f` are built from `L₁₂ f`, which is smooth on `(0,∞)` but
not through `z = 0`),

* continuity of every mixed block `D_z^b D_θ^a G`, `a + b ≤ k`, on the open quadrant
  (`Assembly.BlocksCont k G`);
* additivity of the blocks on a sum `G + H` of two such functions
  (`Assembly.BlocksAdd k G H`).

The existing `Work.FTS.LocData.SmoothChain` provides the same calculus at the *infinite* order
`smoothOrder` (`SmoothQuad`); here everything is at a finite order `n : ℕ`, which is what the
defects satisfy.

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.SmoothStripDefs
import Submission.Work.FTS.CoercivityFix.Assembly.Comm2w

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Transfer.E2pkg

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The open quadrant -/

/-- The open quadrant `(0,∞) × (0,π/2)`. -/
abbrev Qd : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2)

theorem isOpen_Qd : IsOpen Qd := isOpen_Ioi.prod isOpen_Ioo

/-! ## `pth`, `Dth`, `Dz` lower the finite order by one -/

/-- The `θ`-partial derivative lowers the finite order of differentiability by one. -/
theorem contDiffOn_uncurry_pth_of_succ {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pth G)) V := by
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := (n : WithTop ℕ∞)) hV.uniqueDiffOn (by simp)
    refine h'.congr fun p hp => ?_
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (0, 1)) V := by
    simpa using hfd.clm_apply
      (contDiffOn_const : ContDiffOn ℝ n (fun _ : ℝ × ℝ => ((0, 1) : ℝ × ℝ)) V)
  refine hcomp.congr fun p hp => ?_
  have hdiff : DifferentiableAt ℝ (Function.uncurry G) p :=
    ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  simp only [Function.uncurry]
  exact (Work.Spaces.pth_eq_fderiv hdiff)

/-- The `z`-partial derivative lowers the finite order of differentiability by one. -/
theorem contDiffOn_uncurry_pz_of_succ {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pz G)) V := by
  have hfd : ContDiffOn ℝ n (fun p : ℝ × ℝ => fderiv ℝ (Function.uncurry G) p) V := by
    have h' := h.fderivWithin (m := (n : WithTop ℕ∞)) hV.uniqueDiffOn (by simp)
    refine h'.congr fun p hp => ?_
    rw [fderivWithin_of_isOpen hV hp]
  have hcomp : ContDiffOn ℝ n
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry G) p) (1, 0)) V := by
    simpa using hfd.clm_apply
      (contDiffOn_const : ContDiffOn ℝ n (fun _ : ℝ × ℝ => ((1, 0) : ℝ × ℝ)) V)
  refine hcomp.congr fun p hp => ?_
  have hdiff : DifferentiableAt ℝ (Function.uncurry G) p :=
    ((h.differentiableOn (by simp)).differentiableAt (hV.mem_nhds hp))
  simp only [Function.uncurry]
  exact (Work.Spaces.pz_eq_fderiv hdiff)

/-- `D_θ` lowers the finite order of differentiability by one. -/
theorem contDiffOn_uncurry_Dth_of_succ {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dth G)) V := by
  have hfun : Function.uncurry (Work.Spaces.Dth G)
      = fun p : ℝ × ℝ => Real.sin (2 * p.2) * Function.uncurry (Work.Spaces.pth G) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  have hsin : ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.sin (2 * p.2)) V :=
    ((Real.contDiff_sin.comp (contDiff_const.mul contDiff_snd)).contDiffOn).of_le
      (Work.Spaces.natCast_le_smoothOrder n)
  exact hsin.mul (contDiffOn_uncurry_pth_of_succ hV h)

/-- `D_z` lowers the finite order of differentiability by one. -/
theorem contDiffOn_uncurry_Dz_of_succ {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ (n + 1) (Function.uncurry G) V) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.Dz G)) V := by
  have hfun : Function.uncurry (Work.Spaces.Dz G)
      = fun p : ℝ × ℝ => p.1 * Function.uncurry (Work.Spaces.pz G) p := by
    funext p; rcases p with ⟨z, θ⟩; rfl
  rw [hfun]
  exact contDiffOn_fst.mul (contDiffOn_uncurry_pz_of_succ hV h)

/-- `D_θ^i` costs `i` orders of differentiability. -/
theorem contDiffOn_uncurry_DthIter_le {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) :
    ∀ i k : ℕ, i + k ≤ n → ContDiffOn ℝ n (Function.uncurry G) V →
      ContDiffOn ℝ k (Function.uncurry (Work.Spaces.DthIter i G)) V := by
  intro i
  induction i with
  | zero =>
      intro k hk h
      exact h.of_le (Nat.cast_le.mpr (by omega))
  | succ i ih =>
      intro k hik h
      have h1 : (i : ℕ) + (k + 1) ≤ n := by omega
      have h2 : ContDiffOn ℝ (k + 1) (Function.uncurry (Work.Spaces.DthIter i G)) V :=
        ih (k + 1) h1 h
      exact contDiffOn_uncurry_Dth_of_succ hV h2

/-- `D_z^i` costs `i` orders of differentiability. -/
theorem contDiffOn_uncurry_DzIter_le {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) :
    ∀ i k : ℕ, i + k ≤ n → ContDiffOn ℝ n (Function.uncurry G) V →
      ContDiffOn ℝ k (Function.uncurry (Work.Spaces.DzIter i G)) V := by
  intro i
  induction i with
  | zero =>
      intro k hk h
      exact h.of_le (Nat.cast_le.mpr (by omega))
  | succ i ih =>
      intro k hik h
      have h1 : (i : ℕ) + (k + 1) ≤ n := by omega
      have h2 : ContDiffOn ℝ (k + 1) (Function.uncurry (Work.Spaces.DzIter i G)) V :=
        ih (k + 1) h1 h
      exact contDiffOn_uncurry_Dz_of_succ hV h2

/-- A mixed block `D_z^b D_θ^a` costs `a + b` orders of differentiability. -/
theorem contDiffOn_uncurry_mixed_le {n : ℕ} {G : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (a b k : ℕ) (habk : a + b + k ≤ n)
    (h : ContDiffOn ℝ n (Function.uncurry G) V) :
    ContDiffOn ℝ k (Function.uncurry (Work.Spaces.mixed b a G)) V := by
  have h1 : a + (b + k) ≤ n := by rw [← Nat.add_assoc]; exact habk
  have h2 : ContDiffOn ℝ (b + k) (Function.uncurry (Work.Spaces.DthIter a G)) V :=
    contDiffOn_uncurry_DthIter_le hV a (b + k) h1 h
  exact contDiffOn_uncurry_DzIter_le hV b k le_rfl h2

/-! ## `BlocksCont` from finite-order differentiability -/

/-- A `C^n` function on the open quadrant has all its mixed blocks continuous there. -/
theorem blocksCont_of_contDiffOn {n : ℕ} {G : Fn}
    (h : ContDiffOn ℝ n (Function.uncurry G) Qd) :
    Work.FTS.CoercivityFix.Assembly.BlocksCont n G :=
  fun a b hab =>
    (contDiffOn_uncurry_mixed_le isOpen_Qd a b 0 (by omega) h).continuousOn

/-! ## Continuity of the `ℋ^k`-integrand from block continuity -/

/-- The radial weight `w` is continuous on the open quadrant. -/
private lemma continuousOn_w_Qd :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1) Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      = fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2 := by
    funext p; rfl
  rw [hfun]
  refine ContinuousOn.div ((continuousOn_const.add continuousOn_fst).pow 2)
    (continuousOn_fst.pow 2) (fun p hp => pow_ne_zero 2 (ne_of_gt hp.1))

/-- `sin(2θ)^c` is continuous on the open quadrant, for every real exponent `c`. -/
private lemma continuousOn_sinpow_Qd (c : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2)) ^ c) Qd := by
  have hsin : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2)) Qd :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn
  refine hsin.rpow_const (fun p hp => Or.inl (ne_of_gt ?_))
  exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1]) (by linarith [hp.2.2, Real.pi_pos])

/-- The product weight `W` is continuous on the open quadrant. -/
private lemma continuousOn_Wt_Qd (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2) Qd := by
  have hfun : (fun p : ℝ × ℝ => Work.Spaces.Wt α p.1 p.2)
      = fun p : ℝ × ℝ => Work.Spaces.w p.1 * (Real.sin (2 * p.2)) ^ (-(Work.Spaces.gam α / 2)) := by
    funext p; rfl
  rw [hfun]
  exact continuousOn_w_Qd.mul (continuousOn_sinpow_Qd _)

/-- **Continuity of the `ℋ^k`-integrand from block continuity.** -/
theorem continuousOn_HkIntegrand_of_blocksCont {k : ℕ} {F : Fn}
    (h : Work.FTS.CoercivityFix.Assembly.BlocksCont k F) (α : ℝ) :
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k F p.1 p.2) Qd := by
  have hdz : ∀ i ≤ k, ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.DzIter i F p.1 p.2) Qd :=
    fun i hi => h 0 i (by omega)
  have hmix : ∀ i j, 1 ≤ i → i + j ≤ k →
      ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.mixed j i F p.1 p.2) Qd :=
    fun i j hi hij => h i j hij
  simp only [Work.Spaces.HkIntegrand]
  refine ContinuousOn.add ?_ ?_
  · refine continuousOn_finsetSum (Finset.range (k + 1)) fun i hi => ?_
    have hik : i ≤ k := by simpa using Finset.mem_range.mp hi
    have hne : ∀ p ∈ Qd, (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2) ≠ 0 := by
      intro p hp
      exact ne_of_gt (Real.rpow_pos_of_pos
        (Real.sin_pos_of_pos_of_lt_pi (by linarith [hp.2.1])
          (by linarith [hp.2.2, Real.pi_pos])) _)
    exact ((hdz i hik).mul (continuousOn_w_Qd.div (continuousOn_sinpow_Qd _) hne)).pow 2
  · refine continuousOn_finsetSum (Finset.range (k + 1)) fun i hi =>
      continuousOn_finsetSum (Finset.range (k + 1)) fun j hj => ?_
    split_ifs with hc
    · exact ((hmix i j hc.1 hc.2).mul (continuousOn_Wt_Qd α)).pow 2
    · exact continuousOn_const

/-! ## Additivity of the blocks on a sum of `C^n` functions -/

/-- Two functions agreeing on an open set have the same `D_θ` there. -/
private lemma Dth_congr_of_eqOn {V : Set (ℝ × ℝ)} {f g : ℝ → ℝ → ℝ} (hV : IsOpen V)
    (h : ∀ p ∈ V, f p.1 p.2 = g p.1 p.2) :
    ∀ p ∈ V, Work.Spaces.Dth f p.1 p.2 = Work.Spaces.Dth g p.1 p.2 := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have htend : Tendsto (fun θ' : ℝ => ((z, θ') : ℝ × ℝ)) (𝓝 θ) (𝓝 (z, θ)) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto
  have hmem : (fun θ' : ℝ => f z θ') =ᶠ[𝓝 θ] (fun θ' : ℝ => g z θ') := by
    filter_upwards [htend.eventually (hV.mem_nhds hp)] with θ' hθ'
    exact h (z, θ') hθ'
  simp only [Work.Spaces.Dth, Work.Spaces.pth]
  rw [hmem.deriv_eq]

/-- Two functions agreeing on an open set have the same `D_z` there. -/
private lemma Dz_congr_of_eqOn {V : Set (ℝ × ℝ)} {f g : ℝ → ℝ → ℝ} (hV : IsOpen V)
    (h : ∀ p ∈ V, f p.1 p.2 = g p.1 p.2) :
    ∀ p ∈ V, Work.Spaces.Dz f p.1 p.2 = Work.Spaces.Dz g p.1 p.2 := by
  intro p hp
  obtain ⟨z, θ⟩ := p
  have htend : Tendsto (fun z' : ℝ => ((z', θ) : ℝ × ℝ)) (𝓝 z) (𝓝 (z, θ)) :=
    (continuousAt_id.prodMk continuousAt_const).tendsto
  have hmem : (fun z' : ℝ => f z' θ) =ᶠ[𝓝 z] (fun z' : ℝ => g z' θ) := by
    filter_upwards [htend.eventually (hV.mem_nhds hp)] with z' hz'
    exact h (z', θ) hz'
  simp only [Work.Spaces.Dz, Work.Spaces.pz]
  rw [hmem.deriv_eq]

/-- Two functions agreeing on an open set have the same `D_θ`-iterates there. -/
private lemma DthIter_congr_of_eqOn {V : Set (ℝ × ℝ)} {f g : ℝ → ℝ → ℝ} (hV : IsOpen V)
    (h : ∀ p ∈ V, f p.1 p.2 = g p.1 p.2) (i : ℕ) :
    ∀ p ∈ V, Work.Spaces.DthIter i f p.1 p.2 = Work.Spaces.DthIter i g p.1 p.2 := by
  induction i with
  | zero => exact h
  | succ i ih => exact Dth_congr_of_eqOn hV ih

/-- Two functions agreeing on an open set have the same `D_z`-iterates there. -/
private lemma DzIter_congr_of_eqOn {V : Set (ℝ × ℝ)} {f g : ℝ → ℝ → ℝ} (hV : IsOpen V)
    (h : ∀ p ∈ V, f p.1 p.2 = g p.1 p.2) (i : ℕ) :
    ∀ p ∈ V, Work.Spaces.DzIter i f p.1 p.2 = Work.Spaces.DzIter i g p.1 p.2 := by
  induction i with
  | zero => exact h
  | succ i ih => exact Dz_congr_of_eqOn hV ih

/-- `D_θ` is additive at a point where both slices are differentiable. -/
private lemma Dth_add_point {u v : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hu : DifferentiableAt ℝ (fun θ' => u p.1 θ') p.2)
    (hv : DifferentiableAt ℝ (fun θ' => v p.1 θ') p.2) :
    Work.Spaces.Dth (u + v) p.1 p.2
      = Work.Spaces.Dth u p.1 p.2 + Work.Spaces.Dth v p.1 p.2 := by
  simp only [Work.Spaces.Dth, Work.Spaces.pth, Pi.add_apply]
  rw [show (fun θ' : ℝ => u p.1 θ' + v p.1 θ')
      = (fun θ' : ℝ => u p.1 θ') + (fun θ' : ℝ => v p.1 θ') from rfl,
    deriv_add hu hv]
  ring

/-- `D_z` is additive at a point where both slices are differentiable. -/
private lemma Dz_add_point {u v : ℝ → ℝ → ℝ} {p : ℝ × ℝ}
    (hu : DifferentiableAt ℝ (fun z' => u z' p.2) p.1)
    (hv : DifferentiableAt ℝ (fun z' => v z' p.2) p.1) :
    Work.Spaces.Dz (u + v) p.1 p.2
      = Work.Spaces.Dz u p.1 p.2 + Work.Spaces.Dz v p.1 p.2 := by
  simp only [Work.Spaces.Dz, Work.Spaces.pz, Pi.add_apply]
  rw [show (fun z' : ℝ => u z' p.2 + v z' p.2)
      = (fun z' : ℝ => u z' p.2) + (fun z' : ℝ => v z' p.2) from rfl,
    deriv_add hu hv]
  ring

/-- The `θ`-slice of a `C^m` function (`m ≥ 1`) is differentiable. -/
private lemma differentiableAt_slice_theta {m : ℕ} {u : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ m (Function.uncurry u) V) (hm : 1 ≤ m) {p : ℝ × ℝ}
    (hp : p ∈ V) :
    DifferentiableAt ℝ (fun θ' => u p.1 θ') p.2 := by
  have hm0 : (m : WithTop ℕ∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hdiff : DifferentiableAt ℝ (Function.uncurry u) p :=
    ((h.differentiableOn hm0).differentiableAt (hV.mem_nhds hp))
  have hf : DifferentiableAt ℝ (fun θ' : ℝ => ((p.1, θ') : ℝ × ℝ)) p.2 :=
    (differentiableAt_const p.1).prodMk differentiableAt_id
  have hc := hdiff.comp p.2 hf
  simpa [Function.comp_def] using hc

/-- The `z`-slice of a `C^m` function (`m ≥ 1`) is differentiable. -/
private lemma differentiableAt_slice_fst {m : ℕ} {u : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h : ContDiffOn ℝ m (Function.uncurry u) V) (hm : 1 ≤ m) {p : ℝ × ℝ}
    (hp : p ∈ V) :
    DifferentiableAt ℝ (fun z' => u z' p.2) p.1 := by
  have hm0 : (m : WithTop ℕ∞) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]; omega
  have hdiff : DifferentiableAt ℝ (Function.uncurry u) p :=
    ((h.differentiableOn hm0).differentiableAt (hV.mem_nhds hp))
  have hf : DifferentiableAt ℝ (fun z' : ℝ => ((z', p.2) : ℝ × ℝ)) p.1 :=
    differentiableAt_id.prodMk (differentiableAt_const p.2)
  have hc := hdiff.comp p.1 hf
  simpa [Function.comp_def] using hc

/-- **Additivity of the `D_θ`-iterates** on an open set, for two `C^n` functions. -/
theorem DthIter_add_of_contDiffOn {n : ℕ} {f₁ f₂ : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h₁ : ContDiffOn ℝ n (Function.uncurry f₁) V)
    (h₂ : ContDiffOn ℝ n (Function.uncurry f₂) V) :
    ∀ i ≤ n, ∀ p ∈ V,
      Work.Spaces.DthIter i (f₁ + f₂) p.1 p.2
        = Work.Spaces.DthIter i f₁ p.1 p.2 + Work.Spaces.DthIter i f₂ p.1 p.2 := by
  intro i
  induction i with
  | zero => intro _ p _; rfl
  | succ i ih =>
      intro hi p hp
      have hi' : i ≤ n := by omega
      have heq : ∀ q ∈ V, Work.Spaces.DthIter i (f₁ + f₂) q.1 q.2
          = (Work.Spaces.DthIter i f₁ + Work.Spaces.DthIter i f₂) q.1 q.2 := by
        intro q hq
        have := ih hi' q hq
        simpa only [Pi.add_apply] using this
      have hc := Dth_congr_of_eqOn hV heq p hp
      have hd₁ : DifferentiableAt ℝ
          (fun θ' => Work.Spaces.DthIter i f₁ p.1 θ') p.2 :=
        differentiableAt_slice_theta hV
          (contDiffOn_uncurry_DthIter_le hV i 1 (by omega) h₁) (by norm_num) hp
      have hd₂ : DifferentiableAt ℝ
          (fun θ' => Work.Spaces.DthIter i f₂ p.1 θ') p.2 :=
        differentiableAt_slice_theta hV
          (contDiffOn_uncurry_DthIter_le hV i 1 (by omega) h₂) (by norm_num) hp
      show Work.Spaces.Dth (Work.Spaces.DthIter i (f₁ + f₂)) p.1 p.2
        = Work.Spaces.Dth (Work.Spaces.DthIter i f₁) p.1 p.2
          + Work.Spaces.Dth (Work.Spaces.DthIter i f₂) p.1 p.2
      rw [hc, Dth_add_point hd₁ hd₂]

/-- **Additivity of the `D_z`-iterates** on an open set, for two `C^n` functions. -/
theorem DzIter_add_of_contDiffOn {n : ℕ} {f₁ f₂ : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h₁ : ContDiffOn ℝ n (Function.uncurry f₁) V)
    (h₂ : ContDiffOn ℝ n (Function.uncurry f₂) V) :
    ∀ i ≤ n, ∀ p ∈ V,
      Work.Spaces.DzIter i (f₁ + f₂) p.1 p.2
        = Work.Spaces.DzIter i f₁ p.1 p.2 + Work.Spaces.DzIter i f₂ p.1 p.2 := by
  intro i
  induction i with
  | zero => intro _ p _; rfl
  | succ i ih =>
      intro hi p hp
      have hi' : i ≤ n := by omega
      have heq : ∀ q ∈ V, Work.Spaces.DzIter i (f₁ + f₂) q.1 q.2
          = (Work.Spaces.DzIter i f₁ + Work.Spaces.DzIter i f₂) q.1 q.2 := by
        intro q hq
        have := ih hi' q hq
        simpa only [Pi.add_apply] using this
      have hc := Dz_congr_of_eqOn hV heq p hp
      have hd₁ : DifferentiableAt ℝ
          (fun z' => Work.Spaces.DzIter i f₁ z' p.2) p.1 :=
        differentiableAt_slice_fst hV
          (contDiffOn_uncurry_DzIter_le hV i 1 (by omega) h₁) (by norm_num) hp
      have hd₂ : DifferentiableAt ℝ
          (fun z' => Work.Spaces.DzIter i f₂ z' p.2) p.1 :=
        differentiableAt_slice_fst hV
          (contDiffOn_uncurry_DzIter_le hV i 1 (by omega) h₂) (by norm_num) hp
      show Work.Spaces.Dz (Work.Spaces.DzIter i (f₁ + f₂)) p.1 p.2
        = Work.Spaces.Dz (Work.Spaces.DzIter i f₁) p.1 p.2
          + Work.Spaces.Dz (Work.Spaces.DzIter i f₂) p.1 p.2
      rw [hc, Dz_add_point hd₁ hd₂]

/-- **Additivity of the mixed blocks** on an open set, for two `C^n` functions. -/
theorem mixed_add_of_contDiffOn {n : ℕ} {f₁ f₂ : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) (h₁ : ContDiffOn ℝ n (Function.uncurry f₁) V)
    (h₂ : ContDiffOn ℝ n (Function.uncurry f₂) V) :
    ∀ a b : ℕ, a + b ≤ n → ∀ p ∈ V,
      Work.Spaces.mixed b a (f₁ + f₂) p.1 p.2
        = Work.Spaces.mixed b a f₁ p.1 p.2 + Work.Spaces.mixed b a f₂ p.1 p.2 := by
  intro a b hab p hp
  have hDth : ∀ q ∈ V, Work.Spaces.DthIter a (f₁ + f₂) q.1 q.2
      = (Work.Spaces.DthIter a f₁ + Work.Spaces.DthIter a f₂) q.1 q.2 := by
    intro q hq
    have := DthIter_add_of_contDiffOn hV h₁ h₂ a (by omega) q hq
    simpa only [Pi.add_apply] using this
  show Work.Spaces.DzIter b (Work.Spaces.DthIter a (f₁ + f₂)) p.1 p.2
      = Work.Spaces.DzIter b (Work.Spaces.DthIter a f₁) p.1 p.2
        + Work.Spaces.DzIter b (Work.Spaces.DthIter a f₂) p.1 p.2
  rw [show Work.Spaces.DzIter b (Work.Spaces.DthIter a (f₁ + f₂)) p.1 p.2
      = Work.Spaces.DzIter b (Work.Spaces.DthIter a f₁ + Work.Spaces.DthIter a f₂) p.1 p.2
      from DzIter_congr_of_eqOn hV hDth b p hp]
  exact DzIter_add_of_contDiffOn hV
    (contDiffOn_uncurry_DthIter_le hV a b hab h₁)
    (contDiffOn_uncurry_DthIter_le hV a b hab h₂) b le_rfl p hp

/-- **Block additivity of two `C^n` functions on the open quadrant**, in the form consumed by
`Assembly.Comm2w`. -/
theorem blocksAdd_of_contDiffOn {n : ℕ} {f₁ f₂ : Fn}
    (h₁ : ContDiffOn ℝ n (Function.uncurry f₁) Qd)
    (h₂ : ContDiffOn ℝ n (Function.uncurry f₂) Qd) :
    Work.FTS.CoercivityFix.Assembly.BlocksAdd n f₁ f₂ :=
  fun a b hab z θ hzθ => mixed_add_of_contDiffOn isOpen_Qd h₁ h₂ a b hab (z, θ) hzθ

/-! ## Subadditivity of the integrand in finite order -/

/-- At `sin(2θ) = 0` the `D_θ`-iterates of order `≥ 1` vanish. -/
private lemma DthIter_succ_eq_zero_of_sin (f : ℝ → ℝ → ℝ) {θ : ℝ} (hs : Real.sin (2 * θ) = 0)
    (m : ℕ) (z : ℝ) : Work.Spaces.DthIter (m + 1) f z θ = 0 := by
  simp only [Work.Spaces.DthIter_succ, Work.Spaces.Dth, Work.Spaces.pth, hs, zero_mul]

/-- A function whose `θ`-slice vanishes identically has vanishing `D_z`-iterates there. -/
private lemma DzIter_eq_zero_of_slice (f : ℝ → ℝ → ℝ) {θ : ℝ} (h : ∀ z, f z θ = 0) :
    ∀ (j : ℕ) (z : ℝ), Work.Spaces.DzIter j f z θ = 0 := by
  intro j
  induction j with
  | zero => exact h
  | succ n ih =>
      intro z
      have hslice : (fun z' => Work.Spaces.DzIter n f z' θ) = fun _ => (0 : ℝ) := funext ih
      simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
      rw [hslice]; simp

/-- At `sin(2θ) = 0` every mixed derivative with `i ≥ 1` vanishes. -/
private lemma mixed_eq_zero_of_sin (f : ℝ → ℝ → ℝ) {θ : ℝ} (hs : Real.sin (2 * θ) = 0)
    {j i : ℕ} (hi : 1 ≤ i) (z : ℝ) : Work.Spaces.mixed j i f z θ = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : i ≠ 0)
  simp only [Work.Spaces.mixed]
  exact DzIter_eq_zero_of_slice (Work.Spaces.DthIter (m + 1) f) (θ := θ)
    (fun z' => DthIter_succ_eq_zero_of_sin f hs m z') j z

/-- The `ℋ^k`-integrand vanishes on the angular boundary `sin(2θ) = 0`. -/
private lemma HkIntegrand_eq_zero_of_sin (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) {z θ : ℝ}
    (hs : Real.sin (2 * θ) = 0) : Work.Spaces.HkIntegrand α k f z θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  have hsin : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) = 0 := by
    rw [hs, Real.zero_rpow (by norm_num [Work.Spaces.eta])]
  have h1 : (∑ i ∈ Finset.range (k + 1),
      (Work.Spaces.DzIter i f z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hsin, div_zero, mul_zero, zero_pow (by norm_num)]
  have h2 : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
      (if 1 ≤ i ∧ i + j ≤ k
        then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) = 0 := by
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
    split_ifs with hc
    · rw [mixed_eq_zero_of_sin f hs hc.1 z, zero_mul, zero_pow (by norm_num)]
    · rfl
  rw [h1, h2, add_zero]

/-- The `ℋ^k`-integrand vanishes at `z = 0`. -/
theorem HkIntegrand_eq_zero_of_z_eq_zero (α : ℝ) (k : ℕ) (f : ℝ → ℝ → ℝ) (θ : ℝ) :
    Work.Spaces.HkIntegrand α k f 0 θ = 0 := by
  rw [Work.Spaces.HkIntegrand]
  simp [Work.Spaces.w, Work.Spaces.Wt, Work.Spaces.wTheta]

/-- `(x+y)² ≤ 2x² + 2y²` summed over a finset. -/
private lemma sum_sq_add_le {ι : Type*} (s : Finset ι) (x y : ι → ℝ) :
    (∑ i ∈ s, (x i + y i) ^ 2) ≤ 2 * (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, y i ^ 2) := by
  calc (∑ i ∈ s, (x i + y i) ^ 2)
      ≤ ∑ i ∈ s, (2 * x i ^ 2 + 2 * y i ^ 2) :=
        Finset.sum_le_sum fun i _ => by
          have h := add_sq_le (a := x i) (b := y i); linarith
    _ = 2 * (∑ i ∈ s, x i ^ 2) + 2 * (∑ i ∈ s, y i ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- The pointwise inequality, given the additivity of the iterated operators at `(z,θ)`. -/
private lemma HkIntegrand_add_le_pt (α : ℝ) (k : ℕ) (f g : ℝ → ℝ → ℝ) (z θ : ℝ)
    (hz : ∀ i, i ≤ k → Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.DzIter i f z θ + Work.Spaces.DzIter i g z θ)
    (hm : ∀ i j, 1 ≤ i → i + j ≤ k →
      Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
      = Work.Spaces.mixed j i f z θ + Work.Spaces.mixed j i g z θ) :
    Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α k f z θ
        + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  have hZ : (∑ i ∈ Finset.range (k + 1),
        (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
      ≤ 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
          + 2 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
    have h1 : (∑ i ∈ Finset.range (k + 1),
          (Work.Spaces.DzIter i (fun z θ => f z θ + g z θ) z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2)
        = ∑ i ∈ Finset.range (k + 1),
          ((Work.Spaces.DzIter i f z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
            + (Work.Spaces.DzIter i g z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))) ^ 2 := by
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hz i (by simpa using Finset.mem_range.mp hi)]; ring
    rw [h1]
    exact sum_sq_add_le _ _ _
  have hM : (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
        (if 1 ≤ i ∧ i + j ≤ k
          then (Work.Spaces.mixed j i (fun z θ => f z θ + g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
      ≤ 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i f z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          + 2 * (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
            (if 1 ≤ i ∧ i + j ≤ k
              then (Work.Spaces.mixed j i g z θ * Work.Spaces.Wt α z θ) ^ 2 else 0)) := by
    set S : Finset (ℕ × ℕ) := ((Finset.range (k + 1)) ×ˢ (Finset.range (k + 1))).filter
      (fun p => 1 ≤ p.1 ∧ p.1 + p.2 ≤ k) with hS
    have e : ∀ u : ℝ → ℝ → ℝ,
        (∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
          (if 1 ≤ i ∧ i + j ≤ k
            then (Work.Spaces.mixed j i u z θ * Work.Spaces.Wt α z θ) ^ 2 else 0))
          = ∑ p ∈ S, (Work.Spaces.mixed p.2 p.1 u z θ * Work.Spaces.Wt α z θ) ^ 2 := by
      intro u
      rw [hS, Finset.sum_filter, Finset.sum_product]
    rw [e f, e g, e (fun z θ => f z θ + g z θ)]
    have hconv : (∑ p ∈ S,
          (Work.Spaces.mixed p.2 p.1 (fun z θ => f z θ + g z θ) z θ
            * Work.Spaces.Wt α z θ) ^ 2)
        = ∑ p ∈ S, ((Work.Spaces.mixed p.2 p.1 f z θ * Work.Spaces.Wt α z θ)
            + (Work.Spaces.mixed p.2 p.1 g z θ * Work.Spaces.Wt α z θ)) ^ 2 := by
      refine Finset.sum_congr rfl fun p hp => ?_
      rw [hS, Finset.mem_filter, Finset.mem_product, Finset.mem_range,
        Finset.mem_range] at hp
      rw [hm p.1 p.2 hp.2.1 hp.2.2]; ring
    rw [hconv]
    exact sum_sq_add_le _ _ _
  simp only [Work.Spaces.HkIntegrand]
  linarith [hZ, hM]

/-- **Subadditivity of the `ℋ^k`-integrand** for two functions that are `C^k` on the open
quadrant. -/
theorem hkIntegrand_add_le_of_contDiffOn (α : ℝ) (k : ℕ) {f g : Fn}
    (hf : ContDiffOn ℝ k (Function.uncurry f) Qd)
    (hg : ContDiffOn ℝ k (Function.uncurry g) Qd) :
    ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k (f + g) z θ
        ≤ 2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ := by
  intro z hz θ hθ
  change Work.Spaces.HkIntegrand α k (fun z θ => f z θ + g z θ) z θ
      ≤ 2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ
  by_cases hz0 : z = 0
  · rw [hz0, HkIntegrand_eq_zero_of_z_eq_zero]
    have h1 := Work.Spaces.HkIntegrand_nonneg α k f 0 θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α k g 0 θ
    linarith
  by_cases hs : Real.sin (2 * θ) = 0
  · rw [HkIntegrand_eq_zero_of_sin α k (fun z θ => f z θ + g z θ) hs]
    have h1 := Work.Spaces.HkIntegrand_nonneg α k f z θ
    have h2 := Work.Spaces.HkIntegrand_nonneg α k g z θ
    linarith
  · have hzge : 0 ≤ z := by simpa only [Work.Spaces.Iz, Set.mem_Ici] using hz
    have hzpos : 0 < z := lt_of_le_of_ne hzge (Ne.symm hz0)
    have hbnd : 0 ≤ θ ∧ θ ≤ π / 2 := by simpa only [Work.Spaces.Iθ, Set.mem_Icc] using hθ
    have hθ1 : 0 < θ := by
      rcases eq_or_lt_of_le hbnd.1 with h | h
      · exact absurd (by rw [← h]; simp) hs
      · exact h
    have hθ2 : θ < π / 2 := by
      rcases lt_or_eq_of_le hbnd.2 with h | h
      · exact h
      · exact absurd (by rw [h, show (2 : ℝ) * (π / 2) = π from by ring, Real.sin_pi]) hs
    have hpq : (z, θ) ∈ Qd := ⟨hzpos, hθ1, hθ2⟩
    refine HkIntegrand_add_le_pt α k f g z θ (fun i hi => ?_) (fun i j hi hij => ?_)
    · exact DzIter_add_of_contDiffOn isOpen_Qd hf hg i hi (z, θ) hpq
    · exact mixed_add_of_contDiffOn isOpen_Qd hf hg i j hij (z, θ) hpq

/-- **`ℋ^k`-membership is preserved by addition** of two functions that are `C^k` on the open
quadrant. -/
theorem hkMem_add_of_contDiffOn (α : ℝ) (k : ℕ) {f g : Fn}
    (hf : ContDiffOn ℝ k (Function.uncurry f) Qd)
    (hg : ContDiffOn ℝ k (Function.uncurry g) Qd)
    (hmf : Work.Spaces.HkMem α k f) (hmg : Work.Spaces.HkMem α k g) :
    Work.Spaces.HkMem α k (f + g) := by
  have hfg : ContDiffOn ℝ k (Function.uncurry (f + g)) Qd := by
    have h : Function.uncurry (f + g)
        = Function.uncurry f + Function.uncurry g := by
      funext p; rcases p with ⟨z, θ⟩; rfl
    rw [h]; exact hf.add hg
  have hcont : ContinuousOn
      (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α k (f + g) p.1 p.2) Qd :=
    continuousOn_HkIntegrand_of_blocksCont (blocksCont_of_contDiffOn hfg) α
  have hbase : MeasureTheory.IntegrableOn (fun z => 2 * (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k f z θ) + 2 * (∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α k g z θ)) Work.Spaces.Iz :=
    (hmf.2.const_mul 2).add (hmg.2.const_mul 2)
  have hiff : (fun z => 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ)
      + 2 * (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k g z θ))
      =ᵐ[volume.restrict Work.Spaces.Iz]
      (fun z => ∫ θ in Work.Spaces.Iθ,
        (2 * Work.Spaces.HkIntegrand α k f z θ + 2 * Work.Spaces.HkIntegrand α k g z θ)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [MeasureTheory.integral_add ((hmf.1 z hz).const_mul 2) ((hmg.1 z hz).const_mul 2),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  refine Work.FTS.LocData.HkMem_of_majorant α k hcont
    (fun z hz => ?_) ?_ (fun z hz θ hθ => hkIntegrand_add_le_of_contDiffOn α k hf hg z hz θ hθ)
  · exact ((hmf.1 z hz).const_mul 2).add ((hmg.1 z hz).const_mul 2)
  · exact hbase.congr hiff

end Work.FTS.CoercivityFix.Transfer.E2pkg
