/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Work.H2W.slot01ZTBound` — the two `Z`-slots of the `(0,1)`-pair, in the weak class

The target

```
∃ C > 0, ∀ α F Ψ, 0 < α → α ≤ 1/4 → TT.EllWeakPos α 2 F Ψ →
  ∀ᵐ z ∂(volume.restrict Iz), 0 < z →
    (∫_θ (∂_θ (z²∂_zzΨ))² · sin(2θ)^{2-γ}  ≤ C·(∫_θ (∂_θ²(D_zΨ))²·sEta + ∫_θ (∂_θ²(D_z²Ψ))²·sEta))
  ∧ (∫_θ (∂_θ (D_zΨ))² · sin(2θ)^{2-γ} ≤ C·∫_θ (∂_θ²(D_zΨ))²·sEta)
```

bounds the two `Z`-slots of the `(0,1)`-pair (the first-derivative-in-`θ` slots of `z²∂_zzΨ` and of
`D_zΨ`) by the *second* `θ`-derivatives of `D_zΨ` and `D_z²Ψ`, weighted by `sEta = sin(2θ)^{-η}`.
Both conjuncts are the weak form of the first-order angular estimate of §H2
(`FTS.EllipticEst.H2W.weakFirstIter`):

for a slice `u` which is `C^∞` on `(0,π/2)`, continuous on `[0,π/2]`, vanishes at both endpoints and
has `(u'')²·sEta` integrable,

  `∫_θ (u')² sin(2θ)^{2-γ} ≤ C ∫_θ (u'')² sEta`      (`weakFirstIter`, `D_θu = sin 2θ · u'`).

* Second conjunct: `u := D_zΨ z ·` — continuity of the slice on `Iθ` is
  `weakSliceContinuousKit`, the endpoint values are `dz_zero_at_zero`/`dz_zero_at_pi_half`, and
  `(u'')² sEta = (∂_θ²(D_zΨ))² sEta` is honest by `dzpsi_second_sq`.
* First conjunct: `u := z²∂_zzΨ z ·` — on the open quadrant `z²∂_zzΨ = D_z²Ψ - D_zΨ`, so
  `u'' = ∂_θ²(D_z²Ψ) - ∂_θ²(D_zΨ)` there, and `(u'')² sEta` is honest by `H2W.aSliceHonest`.
  The slice is continuous on `Iθ` **almost everywhere in `z`** (this is the honest strength of the
  weak class: the pointwise statement needs one more level of `ℋ^k`-honesty); this is exactly why
  the target is an `a.e.`-in-`z` statement, and the `a.e.` continuity is proved here as
  `aeSliceContASelf` (from the `a.e.` vanishing of the two moments `F_*(D_z²F)`, `F_*(D_z⁴Ψ)`
  and the `Lzero1`-moment identity of the `z²∂_zzΨ`-slice).

The two right-hand-side slots `(∂_θ²(D_z^iΨ))²·sEta` (`i = 1, 2`) are honest for every `z > 0`
(`pth2_DzIter_one_sq`, `pth2_DzIter_two_sq`), so the `a.e.` inequality is non-vacuous.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.SliceKit
import Submission.Work.FTS.EllipticEst.H2W.weakFirstIter
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.ASliceH
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.BslZsq
import Submission.Work.FTS.EllipticEst.H2W.Slot01W.FstarDzIterFourAe
import Submission.Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.H2W

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

local notation "Iθ" => Work.Spaces.Iθ
local notation "sEta" => Work.FTS.EllipticEst.sEta
local notation "sg" => Work.Elliptic.sinCos2

variable {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}

/-! ## 1. Weight algebra -/

/-- On `Iθ` and for `0 < α ≤ 1/4`, the `ℕ`-power `sin(2θ)²` and the weight
`sGam α = sin(2θ)^{-γ}` combine into the `rpow` `sin(2θ)^{2-γ}`. -/
theorem sin_sq_mul_sGam_eq (hα : 0 < α) (hα4 : α ≤ 1 / 4) {θ : ℝ} (hθ : θ ∈ Iθ) :
    (Real.sin (2 * θ)) ^ 2 * Work.FTS.EllipticEst.sGam α θ
      = (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α) := by
  have hs : 0 ≤ Real.sin (2 * θ) := Work.FTS.EllipticEst.TT.sin_two_nonneg hθ
  have hγ0 : 0 < Work.Spaces.gam α := Work.Spaces.gam_pos hα
  have hγ2 : Work.Spaces.gam α < 2 := by rw [Work.Spaces.gam]; linarith
  rcases eq_or_lt_of_le hs with h | h
  · simp only [Work.FTS.EllipticEst.sGam, ← h]
    rw [Real.zero_rpow (by linarith : -(Work.Spaces.gam α) ≠ 0),
      Real.zero_rpow (by linarith : (2 : ℝ) - Work.Spaces.gam α ≠ 0)]
    ring
  · rw [Work.FTS.EllipticEst.sGam, ← Real.rpow_natCast (Real.sin (2 * θ)) 2,
      ← Real.rpow_add h]
    ring_nf

/-! ## 2. Honesty of the two right-hand-side slots -/

/-- `(∂_θ²(D_zΨ))²·sEta` is integrable on `Iθ`: the `i = 1` slot of `HkMem α 2 (∂_θ²Ψ)`. -/
theorem pth2_DzIter_one_sq (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 * sEta θ) Iθ :=
  (dzpsi_second_sq h hz).congr (Filter.Eventually.of_forall fun θ => rfl)

/-- `(∂_θ²(D_z²Ψ))²·sEta` is integrable on `Iθ`: the `i = 2` slot of `HkMem α 2 (∂_θ²Ψ)`. -/
theorem pth2_DzIter_two_sq (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) ^ 2 * sEta θ) Iθ := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  refine (Work.FTS.EllipticEst.remov.ws_slot_slice
    (g := Work.Spaces.pthIter 2 Ψ)
    (Work.FTS.EllipticEst.Cert.smoothOpen_pthIter_bsl hΨ 2) h.memB 2 le_rfl hz).congr ?_
  filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
  have hQ : ((z, θ) : ℝ × ℝ) ∈ Work.FTS.EllipticEst.Q0 :=
    Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩
  have hcomm := Work.EllipticEst.H2W.pthIter2_DzIter_comm hΨ 2 hQ
  change Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ
      = Work.Spaces.DzIter 2 (Work.Spaces.pthIter 2 Ψ) z θ at hcomm
  rw [← hcomm]

/-! ## 3. The slice of `D_z^j Ψ` vanishes at the two endpoints -/

/-- For a slice vanishing identically at `θ = v`, its iterated `z`-derivatives vanish there too. -/
theorem pzIter2_at_eq_zero {v : ℝ} (hv : ∀ z, Ψ z v = 0) (z : ℝ) :
    Work.Spaces.pzIter 2 Ψ z v = 0 := by
  have hfun : (fun z' : ℝ => Ψ z' v) = fun _ => (0 : ℝ) := funext fun z' => hv z'
  have h1 : (fun z' : ℝ => deriv (fun z'' : ℝ => Ψ z'' v) z') = fun _ => (0 : ℝ) := by
    funext z'
    simp only [hfun]
    exact deriv_const z' 0
  show deriv (fun z' : ℝ => deriv (fun z'' : ℝ => Ψ z'' v) z') z = 0
  rw [h1]
  exact deriv_const z 0

/-! ## 4. The pointwise identity `∂_θ²(z²∂_zzΨ) = ∂_θ²(D_z²Ψ) - ∂_θ²(D_zΨ)` -/

/-- On the open quadrant `z²∂_zzΨ = D_z²Ψ - D_zΨ`; the two sides being `C^∞` there, their second
`θ`-derivatives agree. -/
theorem pthIter2_zsq_pzIter2 {Ψ : ℝ → ℝ → ℝ} (hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π/2)) :
    Work.Spaces.pthIter 2 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') z θ
      = Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ
        - Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ := by
  have hC : ∀ j : ℕ, ContDiffOn ℝ 2 (fun t : ℝ => Work.Spaces.DzIter j Ψ z t)
      (Set.Ioo 0 (π/2)) := fun j =>
    contDiffOn_iff_forall_nat_le.mp ((hΨ.DzIter j).curry_θ hz) 2 le_top
  have hd1 : ∀ t ∈ Set.Ioo 0 (π/2), ∀ j : ℕ,
      DifferentiableAt ℝ (fun s : ℝ => Work.Spaces.DzIter j Ψ z s) t := fun t ht j =>
    ((hC j).differentiableOn (by norm_num)).differentiableAt (isOpen_Ioo.mem_nhds ht)
  have hd2 : ∀ t ∈ Set.Ioo 0 (π/2), ∀ j : ℕ,
      DifferentiableAt ℝ (fun s : ℝ => deriv (fun u : ℝ => Work.Spaces.DzIter j Ψ z u) s) t :=
    fun t ht j =>
      (((hC j).deriv_of_isOpen isOpen_Ioo (by norm_num :
          (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableOn (by norm_num)).differentiableAt
        (isOpen_Ioo.mem_nhds ht)
  -- the two slices agree near `θ`
  have hev_deriv : (fun t : ℝ => deriv (fun s : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z s) t)
      =ᶠ[𝓝 θ] (fun t : ℝ => deriv (fun s : ℝ =>
        (Work.Spaces.DzIter 2 Ψ z s - Work.Spaces.DzIter 1 Ψ z s)) t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    have h1 : (fun s : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z s)
        =ᶠ[𝓝 t] (fun s : ℝ =>
          (Work.Spaces.DzIter 2 Ψ z s - Work.Spaces.DzIter 1 Ψ z s)) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact Work.H2W.MomentAe.zsq_pzIter2_eq hΨ hz hs
    exact h1.deriv_eq
  have hev2 : (fun t : ℝ => deriv (fun s : ℝ =>
        (Work.Spaces.DzIter 2 Ψ z s - Work.Spaces.DzIter 1 Ψ z s)) t)
      =ᶠ[𝓝 θ] (fun t : ℝ => deriv (fun s : ℝ => Work.Spaces.DzIter 2 Ψ z s) t
        - deriv (fun s : ℝ => Work.Spaces.DzIter 1 Ψ z s) t) := by
    filter_upwards [isOpen_Ioo.mem_nhds hθ] with t ht
    exact deriv_sub (hd1 t ht 2) (hd1 t ht 1)
  show deriv (fun t : ℝ => deriv (fun s : ℝ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z s) t) θ
      = deriv (fun s : ℝ => deriv (fun u : ℝ => Work.Spaces.DzIter 2 Ψ z u) s) θ
        - deriv (fun s : ℝ => deriv (fun u : ℝ => Work.Spaces.DzIter 1 Ψ z u) s) θ
  rw [hev_deriv.deriv_eq, hev2.deriv_eq]
  exact deriv_sub (hd2 θ hθ 2) (hd2 θ hθ 1)

/-! ## 5. The first conjunct: the `z²∂_zzΨ`-slot -/

/-- **The `z²∂_zzΨ`-slot.**  For an `a.e.`-in-`z` continuous slice (`H2W.aeSliceContA`), the
weak first-order angular estimate applies to `u = z²∂_zzΨ z ·` and the second `θ`-derivative of
`u` splits, on the open quadrant, into `∂_θ²(D_z²Ψ) - ∂_θ²(D_zΨ)`. -/
theorem ZT_bound_A (C₁ : ℝ) (hC₁pos : 0 < C₁)
    (hC₁ : ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
      ContinuousOn u Iθ → u 0 = 0 → u (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * sEta θ) Iθ →
      (∫ θ in Iθ, (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ)
        ≤ C₁ * (∫ θ in Iθ, (deriv (fun t => deriv u t) θ) ^ 2 * sEta θ))
    {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ} (hz : 0 < z)
    (hcont : ContinuousOn (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) Iθ) :
    (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      ≤ 2 * C₁ * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
            * sEta θ)
          + (∫ θ in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) ^ 2
            * sEta θ)) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  set u : ℝ → ℝ := fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ with hu
  have hCinf : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (π/2)) := fun n =>
    contDiffOn_iff_forall_nat_le.mp
      ((Work.H2W.MomentAe.smoothOpen_zsq hΨ).curry_θ hz) n le_top
  have hzero : u 0 = 0 := by
    show z ^ 2 * Work.Spaces.pzIter 2 Ψ z 0 = 0
    rw [pzIter2_at_eq_zero h.zero z, mul_zero]
  have hpi : u (Real.pi / 2) = 0 := by
    show z ^ 2 * Work.Spaces.pzIter 2 Ψ z (Real.pi / 2) = 0
    rw [pzIter2_at_eq_zero h.pi_half z, mul_zero]
  have hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * sEta θ) Iθ := by
    refine (Work.FTS.EllipticEst.H2W.aSliceHonest α F Ψ hα hα4 h z
      (Set.mem_Ici.mpr hz.le)).congr (Filter.Eventually.of_forall fun θ => ?_)
    rfl
  -- the bound of `weakFirstIter`
  have hW := hC₁ α u hα hα4 hCinf hcont hzero hpi hint
  -- the target left-hand side is the left-hand side of `hW`
  have hL : (∫ θ in Iθ, (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      = (∫ θ in Iθ, (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ) := by
    refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
    show (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * θ) * deriv u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ
    rw [mul_pow, ← sin_sq_mul_sGam_eq hα hα4 hθ]
    ring
  -- the second `θ`-derivative of `u` splits into the two slots of `D_z²Ψ`, `D_zΨ`
  have hZ1 := pth2_DzIter_one_sq h hz
  have hZ2 := pth2_DzIter_two_sq h hz
  have hmono : (∫ θ in Iθ, (deriv (fun t => deriv u t) θ) ^ 2 * sEta θ)
      ≤ (∫ θ in Iθ, (2 * ((Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) ^ 2 * sEta θ)
          + 2 * ((Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 * sEta θ))) := by
    refine integral_mono_ae hint (hZ2.const_mul 2 |>.add (hZ1.const_mul 2)) ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    have hid : deriv (fun t => deriv u t) θ
        = Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ
          - Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ := by
      show Work.Spaces.pthIter 2 (fun z θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') z θ = _
      exact pthIter2_zsq_pzIter2 hΨ hz hθ
    have hnn : 0 ≤ sEta θ :=
      sEta_nonneg_Iθ (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    rw [hid]
    nlinarith [sq_nonneg (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ
        + Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ), hnn]
  have hsplit : (∫ θ in Iθ, (2 * ((Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) ^ 2
          * sEta θ) + 2 * ((Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 * sEta θ)))
      = 2 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) ^ 2 * sEta θ)
        + 2 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 * sEta θ) := by
    rw [integral_add (hZ2.const_mul 2) (hZ1.const_mul 2), integral_const_mul, integral_const_mul]
  rw [hL]
  calc (∫ θ in Iθ, (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ)
      ≤ C₁ * (∫ θ in Iθ, (deriv (fun t => deriv u t) θ) ^ 2 * sEta θ) := hW
    _ ≤ C₁ * (2 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) ^ 2 * sEta θ)
          + 2 * (∫ θ in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 * sEta θ)) := by
        rw [← hsplit]; exact mul_le_mul_of_nonneg_left hmono (le_of_lt hC₁pos)
    _ = 2 * C₁ * ((∫ θ in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 * sEta θ)
          + (∫ θ in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) ^ 2 * sEta θ)) := by
        ring

/-! ## 6. The second conjunct: the `D_zΨ`-slot -/

/-- **The `D_zΨ`-slot.**  The weak first-order angular estimate applied to the (everywhere
continuous) slice `u = D_zΨ z ·`, whose second `θ`-derivative is honest by `dzpsi_second_sq`. -/
theorem ZT_bound_B (C₁ : ℝ) (hC₁pos : 0 < C₁)
    (hC₁ : ∀ (α : ℝ) (u : ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      (∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) →
      ContinuousOn u Iθ → u 0 = 0 → u (Real.pi / 2) = 0 →
      MeasureTheory.IntegrableOn
        (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * sEta θ) Iθ →
      (∫ θ in Iθ, (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ)
        ≤ C₁ * (∫ θ in Iθ, (deriv (fun t => deriv u t) θ) ^ 2 * sEta θ))
    {α : ℝ} {F Ψ : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ} (hz : 0 < z) :
    (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      ≤ C₁ * (∫ θ in Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
            * sEta θ) := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  set u : ℝ → ℝ := fun θ => Work.Spaces.Dz Ψ z θ with hu
  have hCinf : ∀ n : ℕ, ContDiffOn ℝ n u (Set.Ioo 0 (π/2)) := fun n =>
    contDiffOn_iff_forall_nat_le.mp ((hΨ.Dz).curry_θ hz) n le_top
  have hcont : ContinuousOn u Iθ := (weakSliceContinuousKit α F Ψ hα hα4 h z hz).2
  have hzero : u 0 = 0 := dz_zero_at_zero h z
  have hpi : u (Real.pi / 2) = 0 := dz_zero_at_pi_half h z
  have hint : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => deriv u t) θ) ^ 2 * sEta θ) Iθ := by
    refine (dzpsi_second_sq h hz).congr (Filter.Eventually.of_forall fun θ => ?_)
    rfl
  have hW := hC₁ α u hα hα4 hCinf hcont hzero hpi hint
  have hL : (∫ θ in Iθ, (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
        * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
      = (∫ θ in Iθ, (Work.Elliptic.Dth1Iter 1 u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ) := by
    refine setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
    show (deriv u θ) ^ 2 * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α)
      = (Real.sin (2 * θ) * deriv u θ) ^ 2 * Work.FTS.EllipticEst.sGam α θ
    rw [mul_pow, ← sin_sq_mul_sGam_eq hα hα4 hθ]
    ring
  rw [hL]
  exact hW

/-- Pointwise slice identity `Lzero1 (Φ z ·) θ = G z θ + α²z²∂_z²Φ + α(5+α)D_zΦ` for a datum
whose slice equation is `bslOp α Φ z θ = G z θ`; all variables explicit so that the dependent
hypothesis elaborates without higher-order unification. -/
theorem Lzero1_slice_eq_pt (α : ℝ) (G Φ : ℝ → ℝ → ℝ) (z θ : ℝ)
    (heq : Work.Elliptic.bslOp α Φ z θ = G z θ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.FTS.EllipticEst.Lzero1 (fun t => Φ z t) θ
      = G z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Φ z θ)
        + α * (5 + α) * Work.Spaces.DzIter 1 Φ z θ := by
  have hb := Work.Elliptic.bslOp_apply α Φ z θ
  have heq' := heq
  rw [hb] at heq'
  have hL : Work.FTS.EllipticEst.Lzero1 (fun t => Φ z t) θ = Work.Elliptic.Lzero Φ z θ := rfl
  have hDz : Work.Spaces.DzIter 1 Φ z θ = z * Work.Spaces.pz Φ z θ := rfl
  rw [hL, hDz]
  linarith

/-! ## (B) `(z²∂_z²f z·)²·sEta` is integrable from the two `D_z`-slots -/

theorem zsq_pzIter2_sq_sEta {f : ℝ → ℝ → ℝ} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z : ℝ} (hz : 0 < z)
    (h1 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter 1 f z θ) ^ 2 * sEta θ) Iθ)
    (h2 : MeasureTheory.IntegrableOn (fun θ => (Work.Spaces.DzIter 2 f z θ) ^ 2 * sEta θ) Iθ) :
    MeasureTheory.IntegrableOn (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 f z θ) ^ 2 * sEta θ) Iθ := by
  refine Integrable.mono'
    (g := fun θ => 2 * ((Work.Spaces.DzIter 2 f z θ) ^ 2 * sEta θ)
      + 2 * ((Work.Spaces.DzIter 1 f z θ) ^ 2 * sEta θ))
    ((h2.const_mul 2).add (h1.const_mul 2)) ?_ ?_
  · exact Work.FTS.EllipticEst.remov.SourceBound.aesm_slice_sq_mul_sEta
      (Work.H2W.MomentAe.smoothOpen_zsq hf).continuousOn hz
  · filter_upwards [Work.H2W.MomentAe.ae_Ioo_mem] with θ hθ
    have hnn : 0 ≤ sEta θ :=
      sEta_nonneg_Iθ (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hnn)]
    have hEq : z ^ 2 * Work.Spaces.pzIter 2 f z θ
        = Work.Spaces.DzIter 2 f z θ - Work.Spaces.DzIter 1 f z θ := by
      simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
        using Work.H2W.MomentAe.zsq_pzIter2_eq hf hz hθ
    rw [hEq]
    nlinarith [sq_nonneg (Work.Spaces.DzIter 2 f z θ + Work.Spaces.DzIter 1 f z θ)]

/-! ## (C) `(Lzero1 (z²∂_z²Ψ z·))²·sEta` is integrable -/

theorem Lzero1A_sq (hα : 0 < α) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ =>
      (Work.FTS.EllipticEst.Lzero1 (fun t => z ^ 2 * Work.Spaces.pzIter 2 Ψ z t) θ) ^ 2
        * sEta θ) Iθ := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.H2W.MomentAe.smoothOpen_zsq hΨ
  have hFso : Work.FTS.EllipticEst.SmoothOpen F := smoothOpen_source h
  have hslice : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun t => z ^ 2 * Work.Spaces.pzIter 2 Ψ z t) θ
        = z ^ 2 * Work.Spaces.pzIter 2 F z θ
          + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
          + α * (5 + α) * Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ :=
    fun θ hθ => Lzero1_slice_eq_pt α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 F z θ)
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
      (Work.FTS.EllipticEst.H2W.bslOp_zsq_pzIter2 α F Ψ h.eq h.smooth z hz θ hθ.1 hθ.2) hθ
  -- the slots
  have hF1 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter 1 F z θ) ^ 2 * sEta θ) Iθ :=
    Work.FTS.EllipticEst.remov.ws_slot_slice hFso h.memF 1 (by norm_num) hz
  have hF2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter 2 F z θ) ^ 2 * sEta θ) Iθ :=
    Work.FTS.EllipticEst.remov.ws_slot_slice hFso h.memF 2 le_rfl hz
  have hA1 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
        * sEta θ) Iθ :=
    Work.FTS.EllipticEst.remov.ws_slot_slice hAso h.memA 1 (by norm_num) hz
  have hA2 : MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
        * sEta θ) Iθ :=
    Work.FTS.EllipticEst.remov.ws_slot_slice hAso h.memA 2 le_rfl hz
  have hstarF := zsq_pzIter2_sq_sEta hFso hz hF1 hF2
  have hstarA := zsq_pzIter2_sq_sEta hAso hz hA1 hA2
  -- the majorant
  refine Integrable.mono'
    (g := fun θ => 3 * ((z ^ 2 * Work.Spaces.pzIter 2 F z θ) ^ 2 * sEta θ)
      + 3 * ((α ^ 2) ^ 2
          * ((z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
            * sEta θ))
      + 3 * ((α * (5 + α)) ^ 2
          * ((Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
            * sEta θ))) ?_ ?_ ?_
  · refine ((hstarF.const_mul 3).add ((hstarA.const_mul ((α ^ 2) ^ 2)).const_mul 3)).add
      ((hA1.const_mul ((α * (5 + α)) ^ 2)).const_mul 3)
  · -- a.e. strong measurability
    have hsum : MeasureTheory.AEStronglyMeasurable (fun θ =>
        (z ^ 2 * Work.Spaces.pzIter 2 F z θ
          + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
          + α * (5 + α) * Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
        ^ 2 * sEta θ) (MeasureTheory.volume.restrict Iθ) :=
      ((((Work.FTS.EllipticEst.remov.ws_aesm_slice
            (Work.H2W.MomentAe.smoothOpen_zsq hFso) hz).add
          ((Work.FTS.EllipticEst.remov.ws_aesm_slice
            (Work.H2W.MomentAe.smoothOpen_zsq hAso) hz).const_mul (α ^ 2))).add
        ((Work.FTS.EllipticEst.remov.ws_aesm_slice hAso.Dz hz).const_mul (α * (5 + α)))).pow 2).mul
        Work.FTS.EllipticEst.remov.ws_sEta_integrableOn.aestronglyMeasurable
    refine hsum.congr ?_
    filter_upwards [Work.H2W.MomentAe.ae_Ioo_mem] with θ hθ
    rw [← hslice θ hθ]
  · filter_upwards [Work.H2W.MomentAe.ae_Ioo_mem] with θ hθ
    have hnn : 0 ≤ sEta θ :=
      sEta_nonneg_Iθ (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩)
    rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hnn), hslice θ hθ]
    have hb := sq_add_three_le (z ^ 2 * Work.Spaces.pzIter 2 F z θ)
      (α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ))
      (α * (5 + α) * Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
    calc (z ^ 2 * Work.Spaces.pzIter 2 F z θ
            + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
            + α * (5 + α) * Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
          ^ 2 * sEta θ
        ≤ 3 * ((z ^ 2 * Work.Spaces.pzIter 2 F z θ) ^ 2
            + (α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)) ^ 2
            + (α * (5 + α) * Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2)
          * sEta θ := mul_le_mul_of_nonneg_right hb hnn
      _ = 3 * ((z ^ 2 * Work.Spaces.pzIter 2 F z θ) ^ 2 * sEta θ)
          + 3 * ((α ^ 2) ^ 2
              * ((z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
                * sEta θ))
          + 3 * ((α * (5 + α)) ^ 2
              * ((Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) ^ 2
                * sEta θ)) := by ring

/-! ## (D) `(z²∂_z²Ψ z·)²` is integrable -/

theorem A_sq_integrable (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) ^ 2) Iθ := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.H2W.MomentAe.smoothOpen_zsq hΨ
  have h1 := DzIter_sq_integrableOn h hz 1 (by norm_num)
  have h2 := DzIter_sq_integrableOn h hz 2 (by norm_num)
  refine Integrable.mono'
    (g := fun θ => 2 * ((Work.Spaces.DzIter 2 Ψ z θ) ^ 2 * sEta θ)
      + 2 * ((Work.Spaces.DzIter 1 Ψ z θ) ^ 2 * sEta θ))
    ((h2.const_mul 2).add (h1.const_mul 2))
    ((Work.FTS.EllipticEst.remov.ws_aesm_slice hAso hz).pow 2) ?_
  filter_upwards [Work.H2W.MomentAe.ae_Ioo_mem] with θ hθ
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  have hEq : z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
      = Work.Spaces.DzIter 2 Ψ z θ - Work.Spaces.DzIter 1 Ψ z θ := by
    simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
      using Work.H2W.MomentAe.zsq_pzIter2_eq hΨ hz hθ
  have hone : 1 ≤ sEta θ := Work.FTS.EllipticEst.remov.one_le_sEta_Ioo hθ
  rw [hEq]
  nlinarith [sq_nonneg (Work.Spaces.DzIter 2 Ψ z θ + Work.Spaces.DzIter 1 Ψ z θ), hone]

/-! ## (E) The `Lzero1`-moment of the `A`-slice vanishes a.e. -/

theorem Lzero1A_moment_ae (hα : 0 < α) (h : Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1
        (fun t => z ^ 2 * Work.Spaces.pzIter 2 Ψ z t) θ * sg θ) = 0 := by
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.H2W.MomentAe.smoothOpen_zsq hΨ
  have hFso : Work.FTS.EllipticEst.SmoothOpen F := smoothOpen_source h
  have hmF2 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z = 0 :=
    Work.FTS.EllipticEst.H2W.Fstar_DzIter_two_F_ae α F Ψ h
  have hmA2 : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.DzIter 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z = 0 :=
    fstar_DzIter_two_zsq_ae α F Ψ h
  filter_upwards [hmF2, hmA2, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
    with z hF2z hA2z hzmem
  have hz : 0 < z := hzmem
  -- the slice identity
  have heqA : ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        = z ^ 2 * Work.Spaces.pzIter 2 F z θ :=
    fun θ hθ hθ' => Work.FTS.EllipticEst.H2W.bslOp_zsq_pzIter2 α F Ψ h.eq h.smooth z hz θ hθ hθ'
  have hslice : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun t => z ^ 2 * Work.Spaces.pzIter 2 Ψ z t) θ
        = z ^ 2 * Work.Spaces.pzIter 2 F z θ
          + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ)
          + α * (5 + α) * Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ :=
    fun θ hθ => Lzero1_slice_eq_pt α (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 F z θ)
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ (heqA θ hθ.1 hθ.2) hθ
  -- integrability of the moment products
  have hprodF : ∀ i ≤ 2, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter i F z θ * sg θ) Iθ := fun i hi =>
    (Work.FTS.EllipticEst.remov.ws_absMoment
      (Work.FTS.EllipticEst.remov.ws_aesm_slice (hFso.DzIter i) hz)
      (Work.FTS.EllipticEst.remov.ws_slot_slice hFso h.memF i hi hz)).1
  have hprodA : ∀ i ≤ 2, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter i (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ)
        Iθ := fun i hi =>
    (Work.FTS.EllipticEst.remov.ws_absMoment
      (Work.FTS.EllipticEst.remov.ws_aesm_slice (hAso.DzIter i) hz)
      (Work.FTS.EllipticEst.remov.ws_slot_slice hAso h.memA i hi hz)).1
  have hprodP : ∀ i ≤ 3, MeasureTheory.IntegrableOn
      (fun θ => Work.Spaces.DzIter i Ψ z θ * sg θ) Iθ := fun i hi =>
    (Work.H2W.MomentAe.level_bound hΨ h.memA h.memB i hi).1 z hz
  -- the a.e. identities `z²∂_z²f = D_z²f - D_zf`
  have haeF : (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 F z θ) * sg θ)
      =ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ => Work.Spaces.DzIter 2 F z θ * sg θ - Work.Spaces.DzIter 1 F z θ * sg θ) := by
    filter_upwards [Work.H2W.MomentAe.ae_Ioo_mem] with θ hθ
    have h1 : z ^ 2 * Work.Spaces.pzIter 2 F z θ
        = Work.Spaces.DzIter 2 F z θ - Work.Spaces.DzIter 1 F z θ := by
      simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
        using Work.H2W.MomentAe.zsq_pzIter2_eq hFso hz hθ
    rw [h1]; ring
  have haeA : (fun θ => (z ^ 2 * Work.Spaces.pzIter 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) * sg θ)
      =ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ => Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ
        - Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ) := by
    filter_upwards [Work.H2W.MomentAe.ae_Ioo_mem] with θ hθ
    have h1 : z ^ 2 * Work.Spaces.pzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        = Work.Spaces.DzIter 2 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          - Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ := by
      simpa only [Work.Spaces.DzIter_succ, Work.Spaces.DzIter_zero]
        using Work.H2W.MomentAe.zsq_pzIter2_eq hAso hz hθ
    rw [h1]; ring
  have haeA1 : (fun θ => Work.Spaces.DzIter 1 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
        * sg θ)
      =ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ => Work.Spaces.DzIter 3 Ψ z θ * sg θ - Work.Spaces.DzIter 2 Ψ z θ * sg θ) := by
    filter_upwards [Work.H2W.MomentAe.ae_Ioo_mem] with θ hθ
    rw [Work.H2W.MomentAe.DzIter_zsq_pzIter2_eq hΨ 1 hz hθ]
    ring
  -- the three moment conditions
  have hmG : Work.Elliptic.Fstar (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 F z θ) z = 0 := by
    rw [Work.Elliptic.Fstar, MeasureTheory.integral_congr_ae haeF,
      MeasureTheory.integral_sub (hprodF 2 le_rfl) (hprodF 1 (by norm_num))]
    change Work.Elliptic.Fstar (Work.Spaces.DzIter 2 F) z
      - Work.Elliptic.Fstar (Work.Spaces.DzIter 1 F) z = 0
    rw [hF2z, Work.FTS.EllipticEst.remov.Fstar_DzIter_one_F_ge_two (k := 2) (by norm_num) h z hz,
      sub_self]
  have hmDz : (∫ θ in Iθ, Work.Spaces.DzIter 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ) = 0 := by
    rw [MeasureTheory.integral_congr_ae haeA1,
      MeasureTheory.integral_sub (hprodP 3 (by norm_num)) (hprodP 2 (by norm_num))]
    change Work.Elliptic.Fstar (Work.Spaces.DzIter 3 Ψ) z
      - Work.Elliptic.Fstar (Work.Spaces.DzIter 2 Ψ) z = 0
    rw [Work.H2W.MomentAe.Fstar_DzIter_le_Psi α F Ψ h 3 (by norm_num) z hz,
      Work.H2W.MomentAe.Fstar_DzIter_le_Psi α F Ψ h 2 (by norm_num) z hz, sub_self]
  have hmA : (∫ θ in Iθ, (z ^ 2 * Work.Spaces.pzIter 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) * sg θ) = 0 := by
    rw [MeasureTheory.integral_congr_ae haeA,
      MeasureTheory.integral_sub (hprodA 2 le_rfl) (hprodA 1 (by norm_num))]
    change Work.Elliptic.Fstar (Work.Spaces.DzIter 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z
      - Work.Elliptic.Fstar (Work.Spaces.DzIter 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z = 0
    rw [hA2z, show Work.Elliptic.Fstar (Work.Spaces.DzIter 1
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)) z = 0 from hmDz, sub_self]
  -- the integrability of the three pieces of `sliceLzero1_moment`
  have hGint : MeasureTheory.IntegrableOn
      (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 F z θ) * sg θ) Iθ :=
    (Work.FTS.EllipticEst.remov.ws_absMoment
      (Work.FTS.EllipticEst.remov.ws_aesm_slice
        (Work.H2W.MomentAe.smoothOpen_zsq hFso) hz)
      (zsq_pzIter2_sq_sEta hFso hz
        (Work.FTS.EllipticEst.remov.ws_slot_slice hFso h.memF 1 (by norm_num) hz)
        (Work.FTS.EllipticEst.remov.ws_slot_slice hFso h.memF 2 le_rfl hz))).1
  have hAint : MeasureTheory.IntegrableOn
      (fun θ => (z ^ 2 * Work.Spaces.pzIter 2
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) * sg θ) Iθ :=
    (Work.FTS.EllipticEst.remov.ws_absMoment
      (Work.FTS.EllipticEst.remov.ws_aesm_slice
        (Work.H2W.MomentAe.smoothOpen_zsq hAso) hz)
      (zsq_pzIter2_sq_sEta hAso hz
        (Work.FTS.EllipticEst.remov.ws_slot_slice hAso h.memA 1 (by norm_num) hz)
        (Work.FTS.EllipticEst.remov.ws_slot_slice hAso h.memA 2 le_rfl hz))).1
  have hLint : MeasureTheory.IntegrableOn
      (fun θ => Work.FTS.EllipticEst.Lzero1
        (fun t => z ^ 2 * Work.Spaces.pzIter 2 Ψ z t) θ * sg θ) Iθ := by
    have hae : (fun θ => Work.FTS.EllipticEst.Lzero1
          (fun t => z ^ 2 * Work.Spaces.pzIter 2 Ψ z t) θ * sg θ)
        =ᵐ[MeasureTheory.volume.restrict Iθ]
        (fun θ => (z ^ 2 * Work.Spaces.pzIter 2 F z θ) * sg θ
          + α ^ 2 * ((z ^ 2 * Work.Spaces.pzIter 2
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ) * sg θ)
          + (α * (5 + α)) * (Work.Spaces.DzIter 1
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * sg θ)) := by
      filter_upwards [Work.H2W.MomentAe.ae_Ioo_mem] with θ hθ
      rw [hslice θ hθ]
      ring
    refine (hGint.add (hAint.const_mul (α ^ 2))).add
      ((hprodA 1 (by norm_num)).const_mul (α * (5 + α))) |>.congr hae.symm
  exact Work.H2W.sliceLzero1_moment (G := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 F z θ)
    (Φ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (z := z) hα hz heqA
    hGint hAint hLint hmG hmDz hmA

/-! ## (F) The a.e. continuity of the `A`-slice -/

theorem aeSliceContASelf : ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z →
      ContinuousOn (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) Work.Spaces.Iθ := by
  intro α F Ψ hα hα4 h
  have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hAso : Work.FTS.EllipticEst.SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    Work.H2W.MomentAe.smoothOpen_zsq hΨ
  have hae : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) Iθ := by
    filter_upwards [Lzero1A_moment_ae (F := F) hα h,
      MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hmom hzmem
    have hz : 0 < z := hzmem
    have hcd : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        (Set.Ioo 0 (Real.pi / 2)) := fun n =>
      contDiffOn_iff_forall_nat_le.mp (hAso.curry_θ hz) n le_top
    have hzero : (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) 0 = 0 := by
      show z ^ 2 * Work.Spaces.pzIter 2 Ψ z 0 = 0
      rw [pzIter2_at_eq_zero h.zero z, mul_zero]
    have hpi : (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (Real.pi / 2) = 0 := by
      show z ^ 2 * Work.Spaces.pzIter 2 Ψ z (Real.pi / 2) = 0
      rw [pzIter2_at_eq_zero h.pi_half z, mul_zero]
    have hA2 := Work.FTS.EllipticEst.H2W.aSliceHonest α F Ψ hα hα4 h z
      (Set.mem_Ici.mpr hz.le)
    have hLA := Lzero1A_sq (F := F) hα h hz
    have hAu2 := A_sq_integrable (F := F) h hz
    have hleft : Filter.Tendsto (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) :=
      Work.FTS.EllipticEst.remov.SourceBound.sliceTendstoZeroOfMoment
        (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) (hcd 2) hA2 hLA hAu2 hmom
    have hright : Filter.Tendsto (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) :=
      (Work.FTS.EllipticEst.H2W.weakSliceLimits
        (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) hcd hzero hpi hA2 hLA).2.2.1
    exact Work.H2W.continuousOn_Icc_of_limits (hAso.curry_θ hz).continuousOn
      (by
        change Filter.Tendsto (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (z ^ 2 * Work.Spaces.pzIter 2 Ψ z 0))
        rw [show z ^ 2 * Work.Spaces.pzIter 2 Ψ z 0 = 0 from hzero]
        exact hleft)
      (by
        change Filter.Tendsto (fun θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2)))
          (nhds (z ^ 2 * Work.Spaces.pzIter 2 Ψ z (Real.pi / 2)))
        rw [show z ^ 2 * Work.Spaces.pzIter 2 Ψ z (Real.pi / 2) = 0 from hpi]
        exact hright)
  rw [Work.Spaces.Iz, MeasureTheory.ae_restrict_iff' measurableSet_Ici]
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi] at hae
  filter_upwards [hae] with z hz
  intro _ hpos
  exact hz hpos


theorem slot01ZTBound : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
    Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), 0 < z →
      ((∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ' => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          ≤ C * ((∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)
              + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 2 Ψ) z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)))
      ∧ ((∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ' => Work.Spaces.Dz Ψ z θ') θ) ^ 2
          * (Real.sin (2 * θ)) ^ (2 - Work.Spaces.gam α))
          ≤ C * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.EllipticEst.H2W.weakFirstIter
  refine ⟨2 * C₁, by positivity, ?_⟩
  intro α F Ψ hα hα4 h
  filter_upwards [aeSliceContASelf α F Ψ hα hα4 h] with z hcont
  intro hz
  have hA := ZT_bound_A C₁ hC₁pos hC₁ hα hα4 h hz (hcont hz)
  have hB := ZT_bound_B C₁ hC₁pos hC₁ hα hα4 h hz
  refine ⟨hA, ?_⟩
  have hZ1nn : 0 ≤ (∫ θ in Work.Spaces.Iθ,
      (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [Work.FTS.EllipticEst.remov.ws_ae_mem_Ioo] with θ hθ
    exact mul_nonneg (sq_nonneg _)
      (sEta_nonneg_Iθ (Set.mem_Icc.mpr ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩))
  exact hB.trans (by nlinarith [hZ1nn, hC₁pos])

end

end Work.H2W
