import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.TT.ESW.Defs
import Submission.Work.FTS.EllipticEst.remov.high_chain_sum_self
import Submission.Work.FTS.EllipticEst.remov.HkSq_step_le
import Submission.Work.FTS.EllipticEst.remov.HkSq_Dz_shift_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT.ESW

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# `source_le` — auxiliary lemmas

This module contains the verified auxiliary lemmas used by `ESW.source_le` (and by the
delegated pieces `ESW.srcA` / `ESW.srcH`): the smoothness of the data on the open quadrant, the
triangular comparison for the top plain angular derivative (`reverse_expansion_sq`), and the
pointwise/integrated top-slot bounds together with the `F`-piece `srcF`.

The top plain angular slot of the source `Gsl α F Ψ = F + α²Asl Ψ + α(5+α)·DzIter 1 Ψ` of the
sliced equation is dominated by `C·HkSq α k F`, for `k ≥ 3`, `0 < α ≤ 1/4`, under the two
level-`(k-1)` bounds on `(Asl Ψ, Bsl Ψ)` and on `(Asl (D_zΨ), Bsl (D_zΨ))`.

## Route

Write `A := Asl Ψ = z²∂_z²Ψ`, `B := Bsl Ψ = ∂_θ²Ψ`, `h := DzIter 1 Ψ = z∂_zΨ`.  Pointwise,

  `∂_θ^kG = ∂_θ^kF + α²∂_θ^kA + α(5+α)∂_θ^kh`  hence
  `(∂_θ^kG)² ≤ 3((∂_θ^kF)² + α⁴(∂_θ^kA)² + α²(5+α)²(∂_θ^kh)²)`.

* **`F`-part** (`srcF`): the plain top slot of a smooth datum is dominated pointwise (a.e. in
  `θ`) by its `H^k`-integrand (`slot_pointwise_HkIntegrand`, whose engine is the sharp chain
  `dthChain_core`: `(sin(2θ)^k ∂_θ^k v)² ≤ C Σ_{r∈Icc 1 k}(D_θ^r v)²`); the passage to the
  integral is `theta_slice_mono` + `z_integral_mono_const`, and `HkMem α k F` (a field of
  `EllWeakPos`) supplies the honesty.
* **`A`-part** (`srcA`): the same pointwise bound with `v = A` gives
  `α⁴∫∫(∂_θ^kA)²w²σ^{2k-γ} ≤ C α⁴ HkSq α k A`; the level-`k` norm of `A` is then reduced by
  `HkSq_step_le` to `HkSq α (k-1) A` (hypothesis H1), to `HkSq α (k-1) (D_z A)` (which is
  `HkSq α (k-1) (Asl (D_zΨ))`, hypothesis H2) and to the single top angular slot `Tk α k A`
  (`A_top_slot_bound`).
* **`h`-part** (`srcH`): the triangular comparison `σ^{j-2}|∂_θ^jh| ≤ K(|D_θ^{j-2}h''| +
  Σ_{r<j-2}σ^r|∂_θ^{r+2}h|)` (reading off the `r = j-2` coefficient `dthCoef (j-2) (j-2) = σ^{j-2}`
  of the exact expansion `DthIter_expansion_local`, and bounding the others by
  `DthCoef_sin_pow_bound`) expresses the `η`-weighted plain slots of `h` in terms of the
  `η`-weighted `D_θ`-slots of `h'' = ∂_θ²h = D_z B`, which are dominated by the `γ`-weighted
  slots of `B` (hypothesis H1) because `σ^{-η} ≤ σ^{-γ}` pointwise.

The `A`-part is the only place where a genuine `H^k` elliptic input is used
(`A_top_slot_bound`, a proved lemma of the sibling directory); the `h`-part is proved here by
the triangular comparison above.
-/

/-! ## Smoothness of the data on the open quadrant -/

/-- `tan` is `C^∞` on the open quadrant (its singularities are at `π/2 + ℤπ`). -/
private theorem contDiffOn_tan_snd (n : ℕ) :
    ContDiffOn ℝ n (fun p : ℝ × ℝ => Real.tan p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  intro p hp
  have hcos : Real.cos p.2 ≠ 0 :=
    ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hp.2.1, Real.pi_pos], hp.2.2⟩)
  exact (((Real.contDiffAt_tan.mpr hcos).comp p contDiffAt_snd)).contDiffWithinAt

/-- `h = D_z Ψ` is `C^∞` on the open quadrant. -/
theorem contDiffOn_dzIter_one {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (Work.Spaces.DzIter 1 Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  (Work.FTS.EllipticEst.SmoothOpen.Dz (Work.FTS.EllipticEst.smoothOpen_of_forall hΨ)).forall n

/-- `A = z²∂_z²Ψ` is `C^∞` on the open quadrant. -/
theorem contDiffOn_asl {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (Asl Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have h2 : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pzIter 2 Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    (Work.FTS.EllipticEst.SmoothOpen.pzIter
      (Work.FTS.EllipticEst.smoothOpen_of_forall hΨ) 2).forall n
  have h1 : ContDiffOn ℝ n (fun p : ℝ × ℝ => p.1 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by fun_prop
  exact (h1.mul h2).congr (fun p _ => rfl)

/-- `B = ∂_θ²Ψ` is `C^∞` on the open quadrant. -/
theorem contDiffOn_bsl {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (Bsl Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
  (Work.FTS.EllipticEst.SmoothOpen.pth
    (Work.FTS.EllipticEst.SmoothOpen.pth
      (Work.FTS.EllipticEst.smoothOpen_of_forall hΨ))).forall n

/-- `bslOp α Ψ` is `C^∞` on the open quadrant. -/
theorem contDiffOn_bslOp {α : ℝ} {Ψ : ℝ → ℝ → ℝ}
    (hΨ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry Ψ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry (Work.Elliptic.bslOp α Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  set Q : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) with hQ
  have h1 : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pzIter 2 Ψ)) Q :=
    (Work.FTS.EllipticEst.SmoothOpen.pzIter
      (Work.FTS.EllipticEst.smoothOpen_of_forall hΨ) 2).forall n
  have h2 : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pzIter 1 Ψ)) Q :=
    (Work.FTS.EllipticEst.SmoothOpen.pzIter
      (Work.FTS.EllipticEst.smoothOpen_of_forall hΨ) 1).forall n
  have h3 : ContDiffOn ℝ n (Function.uncurry Ψ) Q := hΨ n
  have h4 : ContDiffOn ℝ n (Function.uncurry (Work.Spaces.pthIter 2 Ψ)) Q :=
    (Work.FTS.EllipticEst.SmoothOpen.pth
      (Work.FTS.EllipticEst.SmoothOpen.pth
        (Work.FTS.EllipticEst.smoothOpen_of_forall hΨ))).forall n
  have h5 : Work.FTS.EllipticEst.SmoothOpen (fun z θ => Real.tan θ * Ψ z θ) :=
    Work.FTS.EllipticEst.smoothOpen_of_forall
      (fun m => (contDiffOn_tan_snd m).mul (hΨ m))
  have h6 : ContDiffOn ℝ n
      (Function.uncurry (Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ))) Q :=
    h5.pth.forall n
  have h3c : ContDiffOn ℝ n (fun p : ℝ × ℝ => (6 : ℝ) * Ψ p.1 p.2) Q :=
    contDiffOn_const.mul h3
  have h7 : ContDiffOn ℝ n (Function.uncurry (fun z θ =>
      -((α ^ 2) * z ^ 2) * Work.Spaces.pzIter 2 Ψ z θ)) Q := by
    have hp : ContDiffOn ℝ n (fun p : ℝ × ℝ => -((α ^ 2) * p.1 ^ 2)) Q := by fun_prop
    exact (hp.mul h1).congr (fun p _ => rfl)
  have h8 : ContDiffOn ℝ n (Function.uncurry (fun z θ =>
      -((α * (5 + α)) * z) * Work.Spaces.pzIter 1 Ψ z θ)) Q := by
    have hp : ContDiffOn ℝ n (fun p : ℝ × ℝ => -((α * (5 + α)) * p.1)) Q := by fun_prop
    exact (hp.mul h2).congr (fun p _ => rfl)
  have hL : ContDiffOn ℝ n (Function.uncurry (Work.Elliptic.Lzero Ψ)) Q := by
    rw [show Work.Elliptic.Lzero Ψ = fun z θ =>
        -(Work.Spaces.pthIter 2 Ψ z θ)
          + Work.Spaces.pth (fun z θ => Real.tan θ * Ψ z θ) z θ - 6 * Ψ z θ from rfl]
    exact (h4.neg.add h6).sub h3c
  have := (h7.add h8).add hL
  refine this.congr (fun p _ => ?_)
  simp only [Function.uncurry, Work.Elliptic.bslOp_apply, Work.Spaces.pzIter_succ,
    Work.Spaces.pzIter_zero]
  ring_nf

/-- `F` is `C^∞` on the open quadrant: it agrees there with `bslOp α Ψ`. -/
theorem contDiffOn_of_weak {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hwk : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) (n : ℕ) :
    ContDiffOn ℝ n (Function.uncurry F)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
  have hbs : ContDiffOn ℝ n (Function.uncurry (Work.Elliptic.bslOp α Ψ))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := contDiffOn_bslOp hwk.smooth n
  refine hbs.congr (fun p hp => ?_)
  have h := hwk.eq p.1 hp.1 p.2 hp.2.1 hp.2.2
  simp only [Function.uncurry]
  exact h.symm

/-! ## The pointwise and integrated top-slot bounds -/

/-- **The pointwise top-slot bound**: the top plain slot of a smooth datum is dominated, a.e.
in `θ`, by its `H^k`-integrand.  (`slot_pointwise_HkIntegrand` at `m = k`.) -/
theorem slot_top_le_HkIntegrand (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (v : ℝ → ℝ → ℝ), 0 < α →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry v)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      ∀ z ∈ Work.Spaces.Iz, ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        (Work.Spaces.w z) ^ 2 * ((Work.Spaces.pthIter k v z θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - Work.Spaces.gam α))
          ≤ C * Work.Spaces.HkIntegrand α k v z θ := by
  obtain ⟨C, hC, h⟩ := Work.FTS.EllipticEst.remov.selfdth.slot_pointwise_HkIntegrand k (by omega)
  exact ⟨C, hC, fun α v hα hv => h α v k le_rfl hα hv⟩

/-- **The integrated top-slot bound**: the top plain slot of a datum in `H^k` is dominated by
`HkSq α k v`. -/
theorem slot_top_integral_le (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (v : ℝ → ℝ → ℝ), 0 < α →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry v)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      Work.Spaces.HkMem α k v →
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k v z θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - Work.Spaces.gam α))
        ≤ C * Work.Spaces.HkSq α k v := by
  obtain ⟨C, hC, hpt⟩ := slot_top_le_HkIntegrand k hk
  refine ⟨C, hC, fun α v hα hv hmem => ?_⟩
  have hslice : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.w z) ^ 2 *
          ((Work.Spaces.pthIter k v z θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - Work.Spaces.gam α)))
        ≤ ∫ θ in Work.Spaces.Iθ, C * Work.Spaces.HkIntegrand α k v z θ := by
    intro z hz
    have h0 := Work.FTS.EllipticEst.remov.selfdth.theta_slice_mono (K := k) (m := k) (v := v)
      (z := z) (C := C) hC.le (hmem.1 z hz) (hpt α v hα hv z hz)
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    exact h0
  exact Work.FTS.EllipticEst.remov.selfdth.z_integral_mono_const (K := k) (m := k) (v := v)
    (C := C) hC.le hmem.2
    ((MeasureTheory.ae_restrict_mem measurableSet_Ici).mono (fun z hz => hslice z hz))

/-! ## The `F`-piece -/

theorem srcF (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter k F z θ) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (k : ℝ) - Work.Spaces.gam α))
        ≤ C * Work.Spaces.HkSq α k F := by
  obtain ⟨C, hC, h⟩ := slot_top_integral_le k hk
  exact ⟨C, hC, fun α F Ψ hα _ hwk =>
    h α F hα (contDiffOn_of_weak hwk) hwk.memF⟩

/-! ## The triangular comparison for the `h`-part -/

/-- Iterates of `∂_θ` compose. -/
theorem pthIter_add_local (m n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter (m + n) f = Work.Spaces.pthIter m (Work.Spaces.pthIter n f) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [Nat.succ_add, Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]

/-- **The triangular comparison, squared form.**  For `j ≥ 2`, on the open interval,

  `(σ^{j-2} ∂_θ^j h)² ≤ K ((D_θ^{j-2}(∂_θ²h))² + Σ_{r<j-2} (σ^r ∂_θ^{r+2}h)²)`.

It is the exact expansion `D_θ^{j-2} = Σ_r dthCoef (j-2) r · ∂_θ^r` of
`DthIter_expansion_local` solved for the top term (the coefficient of `∂_θ^j h` is
`dthCoef (j-2) (j-2) = σ^{j-2}`, `dthCoef_self`), every other coefficient being bounded by
`K σ^r` (`DthCoef_sin_pow_bound`), followed by `(a+b)² ≤ 2a²+2b²` and Cauchy–Schwarz. -/
theorem reverse_expansion_sq (j : ℕ) (hj : 2 ≤ j) :
    ∃ K : ℝ, 0 < K ∧ ∀ (f : ℝ → ℝ → ℝ) (z θ : ℝ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry (Work.Spaces.pthIter 2 f)) (z, θ)) →
      ((Real.sin (2 * θ)) ^ (j - 2) * Work.Spaces.pthIter j f z θ) ^ 2
        ≤ K * ((Work.Spaces.DthIter (j - 2) (Work.Spaces.pthIter 2 f) z θ) ^ 2
            + ∑ r ∈ Finset.range (j - 2),
                ((Real.sin (2 * θ)) ^ r * Work.Spaces.pthIter (r + 2) f z θ) ^ 2) := by
  classical
  choose Kc hKcpos hKc using fun r =>
    Work.FTS.EllipticEst.remov.selfdth.DthCoef_sin_pow_bound (j - 2) r
  have hKcNn : (0 : ℝ) ≤ ∑ r ∈ Finset.range (j - 1), Kc r :=
    Finset.sum_nonneg fun r _ => (hKcpos r).le
  set KK : ℝ := ∑ r ∈ Finset.range (j - 1), Kc r + 1 with hKK
  have hKKpos : 0 < KK := by rw [hKK]; linarith
  refine ⟨2 * KK ^ 2 * ((j : ℝ) + 2), by positivity, fun f z θ hθ hf => ?_⟩
  have hσ : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  have hσnn : 0 ≤ Real.sin (2 * θ) := hσ.le
  have hiter : ∀ r : ℕ, Work.Spaces.pthIter (r + 2) f
      = Work.Spaces.pthIter r (Work.Spaces.pthIter 2 f) := fun r => pthIter_add_local r 2 f
  have hself : Work.FTS.EllipticEst.remov.selfdth.dthCoef (j - 2) (j - 2) θ
      = (Real.sin (2 * θ)) ^ (j - 2) := by
    rw [Work.FTS.EllipticEst.remov.selfdth.dthCoef_self]
  have hexp := Work.FTS.EllipticEst.remov.selfdth.DthIter_expansion_local (j - 2)
    (Work.Spaces.pthIter 2 f) z θ hf
  rw [show j - 2 + 1 = j - 1 by omega] at hexp
  -- the expansion, solved for the top term
  have hsplit : Work.Spaces.DthIter (j - 2) (Work.Spaces.pthIter 2 f) z θ
      = (Real.sin (2 * θ)) ^ (j - 2) * Work.Spaces.pthIter j f z θ
        + ∑ r ∈ Finset.range (j - 2),
            Work.FTS.EllipticEst.remov.selfdth.dthCoef (j - 2) r θ
              * Work.Spaces.pthIter (r + 2) f z θ := by
    rw [hexp, show j - 1 = (j - 2) + 1 by omega, Finset.sum_range_succ]
    have hsum : (∑ r ∈ Finset.range (j - 2),
        Work.FTS.EllipticEst.remov.selfdth.dthCoef (j - 2) r θ
          * Work.Spaces.pthIter r (Work.Spaces.pthIter 2 f) z θ)
        = ∑ r ∈ Finset.range (j - 2),
            Work.FTS.EllipticEst.remov.selfdth.dthCoef (j - 2) r θ
              * Work.Spaces.pthIter (r + 2) f z θ :=
      Finset.sum_congr rfl fun r _ => by rw [← hiter r]
    have hlast : Work.FTS.EllipticEst.remov.selfdth.dthCoef (j - 2) (j - 2) θ
        * Work.Spaces.pthIter (j - 2) (Work.Spaces.pthIter 2 f) z θ
        = (Real.sin (2 * θ)) ^ (j - 2) * Work.Spaces.pthIter j f z θ := by
      rw [hself, ← hiter (j - 2), Nat.sub_add_cancel hj]
    rw [hsum, hlast]
    ring
  -- the key identity and the two-term bound
  set S : ℝ := ∑ r ∈ Finset.range (j - 2),
      Work.FTS.EllipticEst.remov.selfdth.dthCoef (j - 2) r θ
        * Work.Spaces.pthIter (r + 2) f z θ with hS
  set D : ℝ := Work.Spaces.DthIter (j - 2) (Work.Spaces.pthIter 2 f) z θ with hD
  have hkey : S + (Real.sin (2 * θ)) ^ (j - 2) * Work.Spaces.pthIter j f z θ = D := by
    rw [hS, hD]; linarith [hsplit]
  have hbound : ((Real.sin (2 * θ)) ^ (j - 2) * Work.Spaces.pthIter j f z θ) ^ 2
      ≤ 2 * D ^ 2 + 2 * S ^ 2 := by
    have := Work.FTS.EllipticEst.remov.selfdth.sq_sub_le_two D S
    have h : (Real.sin (2 * θ)) ^ (j - 2) * Work.Spaces.pthIter j f z θ = D - S := by
      rw [← hkey]; ring
    rw [h]
    linarith [this]
  -- Cauchy–Schwarz for `S`
  have hCS : S ^ 2 ≤ ((j : ℝ) + 2) * ∑ r ∈ Finset.range (j - 2),
      (Work.FTS.EllipticEst.remov.selfdth.dthCoef (j - 2) r θ
        * Work.Spaces.pthIter (r + 2) f z θ) ^ 2 := by
    have h := sq_sum_le_card_mul_sum_sq (s := Finset.range (j - 2))
      (f := fun r => Work.FTS.EllipticEst.remov.selfdth.dthCoef (j - 2) r θ
        * Work.Spaces.pthIter (r + 2) f z θ)
    have hcard : (((Finset.range (j - 2)).card : ℕ) : ℝ) ≤ (j : ℝ) + 2 := by
      simp only [Finset.card_range]
      have : ((j - 2 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast Nat.sub_le j 2
      linarith
    rw [hS]
    exact h.trans (mul_le_mul_of_nonneg_right hcard (Finset.sum_nonneg fun r _ => sq_nonneg _))
  -- each summand
  have hterm : ∀ r ∈ Finset.range (j - 2),
      (Work.FTS.EllipticEst.remov.selfdth.dthCoef (j - 2) r θ
          * Work.Spaces.pthIter (r + 2) f z θ) ^ 2
        ≤ KK ^ 2 * ((Real.sin (2 * θ)) ^ r * Work.Spaces.pthIter (r + 2) f z θ) ^ 2 := by
    intro r hr
    have hle : |Work.FTS.EllipticEst.remov.selfdth.dthCoef (j - 2) r θ|
        ≤ KK * (Real.sin (2 * θ)) ^ r := by
      have h1 := hKc r θ
      have h2 : |Real.sin (2 * θ)| ^ r = (Real.sin (2 * θ)) ^ r := by
        rw [abs_of_nonneg hσnn]
      rw [h2] at h1
      have h3 : Kc r ≤ KK := by
        rw [hKK]
        refine le_trans (Finset.single_le_sum (f := fun r => Kc r) (fun i _ => (hKcpos i).le) ?_)
          (by linarith)
        rw [Finset.mem_range] at hr ⊢; omega
      exact h1.trans (mul_le_mul_of_nonneg_right h3 (pow_nonneg hσnn r))
    have hsq : (Work.FTS.EllipticEst.remov.selfdth.dthCoef (j - 2) r θ) ^ 2
        ≤ (KK * (Real.sin (2 * θ)) ^ r) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) hle 2
    calc (Work.FTS.EllipticEst.remov.selfdth.dthCoef (j - 2) r θ
          * Work.Spaces.pthIter (r + 2) f z θ) ^ 2
        = (Work.FTS.EllipticEst.remov.selfdth.dthCoef (j - 2) r θ) ^ 2
            * (Work.Spaces.pthIter (r + 2) f z θ) ^ 2 := by rw [mul_pow]
      _ ≤ (KK * (Real.sin (2 * θ)) ^ r) ^ 2 * (Work.Spaces.pthIter (r + 2) f z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = KK ^ 2 * ((Real.sin (2 * θ)) ^ r * Work.Spaces.pthIter (r + 2) f z θ) ^ 2 := by ring
  have hSsum : S ^ 2 ≤ ((j : ℝ) + 2) * (KK ^ 2 * ∑ r ∈ Finset.range (j - 2),
      ((Real.sin (2 * θ)) ^ r * Work.Spaces.pthIter (r + 2) f z θ) ^ 2) := by
    refine hCS.trans ?_
    have h1 : (∑ r ∈ Finset.range (j - 2),
        (Work.FTS.EllipticEst.remov.selfdth.dthCoef (j - 2) r θ
          * Work.Spaces.pthIter (r + 2) f z θ) ^ 2)
        ≤ KK ^ 2 * ∑ r ∈ Finset.range (j - 2),
            ((Real.sin (2 * θ)) ^ r * Work.Spaces.pthIter (r + 2) f z θ) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun r hr => hterm r hr
    exact mul_le_mul_of_nonneg_left h1 (by positivity)
  refine hbound.trans ?_
  have hDD : (0 : ℝ) ≤ D ^ 2 + ∑ r ∈ Finset.range (j - 2),
      ((Real.sin (2 * θ)) ^ r * Work.Spaces.pthIter (r + 2) f z θ) ^ 2 :=
    add_nonneg (sq_nonneg _) (Finset.sum_nonneg fun r _ => sq_nonneg _)
  have hjj : (0 : ℝ) < (j : ℝ) + 2 := by
    have : (2 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
    linarith
  have hKK1 : 1 ≤ KK ^ 2 := by nlinarith [hKKpos]
  have hstep : S ^ 2 ≤ ((j : ℝ) + 2) * KK ^ 2 * (D ^ 2 + ∑ r ∈ Finset.range (j - 2),
      ((Real.sin (2 * θ)) ^ r * Work.Spaces.pthIter (r + 2) f z θ) ^ 2) := by
    have h1 : ((j : ℝ) + 2) * (KK ^ 2 * ∑ r ∈ Finset.range (j - 2),
        ((Real.sin (2 * θ)) ^ r * Work.Spaces.pthIter (r + 2) f z θ) ^ 2)
        ≤ ((j : ℝ) + 2) * KK ^ 2 * (D ^ 2 + ∑ r ∈ Finset.range (j - 2),
            ((Real.sin (2 * θ)) ^ r * Work.Spaces.pthIter (r + 2) f z θ) ^ 2) := by
      have h2 : KK ^ 2 * ∑ r ∈ Finset.range (j - 2),
          ((Real.sin (2 * θ)) ^ r * Work.Spaces.pthIter (r + 2) f z θ) ^ 2
          ≤ KK ^ 2 * (D ^ 2 + ∑ r ∈ Finset.range (j - 2),
              ((Real.sin (2 * θ)) ^ r * Work.Spaces.pthIter (r + 2) f z θ) ^ 2) := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg KK)
        linarith [sq_nonneg D]
      have := mul_le_mul_of_nonneg_left h2 (by positivity : (0:ℝ) ≤ (j : ℝ) + 2)
      linarith [this]
    linarith [hSsum, h1]
  have hfin : 2 * D ^ 2 + 2 * S ^ 2
      ≤ (2 * KK ^ 2 * ((j : ℝ) + 2)) * (D ^ 2 + ∑ r ∈ Finset.range (j - 2),
          ((Real.sin (2 * θ)) ^ r * Work.Spaces.pthIter (r + 2) f z θ) ^ 2) := by
    have h1 : 2 * S ^ 2 ≤ 2 * (((j : ℝ) + 2) * KK ^ 2 * (D ^ 2 + ∑ r ∈ Finset.range (j - 2),
        ((Real.sin (2 * θ)) ^ r * Work.Spaces.pthIter (r + 2) f z θ) ^ 2)) := by
      linarith [hstep]
    have h2 : 2 * D ^ 2 ≤ 2 * (((j : ℝ) + 2) * KK ^ 2) * D ^ 2 := by
      have h3 : 1 ≤ ((j : ℝ) + 2) * KK ^ 2 := by nlinarith [hjj, hKK1]
      nlinarith [h3, sq_nonneg D]
    nlinarith [h1, h2, hDD, hKKpos, hjj]
  exact hfin




end

end Work.FTS.EllipticEst.TT.ESW
