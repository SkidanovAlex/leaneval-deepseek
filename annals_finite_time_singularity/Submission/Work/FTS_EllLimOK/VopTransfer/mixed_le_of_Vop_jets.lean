/-
Copyright: work module for the Elgindi finite-time singularity project.

# `mixed_le_of_Vop_jets` — the jet transfer from `Vop Ψ` to `Ψ`

If `Ψ` is `C^∞` on the open quadrant `(0,∞) × (0,π/2)`, if `cos s · Ψ z s → 0` as
`s → π/2⁻` for every `z > 0`, and if every mixed derivative
`D_z^j D_θ^l (Vop Ψ)` of total order `j + l ≤ 4` is bounded by `K` on the open quadrant
(where `Vop Ψ = ∂_θΨ - tan θ·Ψ`), then every mixed derivative `D_z^j D_θ^i Ψ` of total order
`j + i ≤ 4` is bounded by `C·K` with a universal constant `C`.

The proof: `cos θ · Vop Ψ = ∂_θ (cos θ · Ψ)`, so the `θ`-ODE with the boundary condition at
`π/2` reconstructs `cos θ·Ψ(z,θ) = -∫_θ^{π/2} cos s·Vop Ψ(z,s) ds`; differentiating this
identity `j ≤ 4` times in `z` (differentiation under the integral sign, valid because all the
`z`-derivatives of `Vop Ψ` are bounded) bounds all `D_z^j Ψ`.  The `θ`-derivatives follow from
the recurrence `D_θΨ = sin(2θ)·Vop Ψ + 2 sin²θ·Ψ` together with the angular Leibniz rule
`D_z^j D_θ^i (c(θ)·f) = ∑_{m ≤ i} C(i,m) (Lop^m c)(θ)·D_z^j D_θ^{i-m} f`, by induction on
the `θ`-order.

The auxiliary lemmas used here live in
`Submission/Work/FTS_EllLimOK/VopTransfer/VopJetsAux.lean`, the parametrised-integral lemma
in `.../derivUnderIntegralIoo.lean` and the angular coefficient bounds in
`.../exists_LopIter_bound.lean`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.SmoothOpenAdd
import Submission.Work.FTS_EllLimOK.Reconstruct
import Submission.Work.FTS.TransportS.flat_mixed_le
import Submission.Work.Spaces.DthIter_mul
import Submission.Work.Spaces.DzDthIterCommOn
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS_EllLimOK.VopTransfer.VopJetsAux
import Submission.Work.FTS_EllLimOK.VopTransfer.derivUnderIntegralIoo
import Submission.Work.FTS_EllLimOK.VopTransfer.exists_LopIter_bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.VopTransfer

theorem mixed_le_of_Vop_jets : ∃ C : ℝ, 0 < C ∧ ∀ (K : ℝ), 0 ≤ K → ∀ (Ψ : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.SmoothOpen Ψ →
    (∀ z ∈ Set.Ioi (0 : ℝ), Filter.Tendsto (fun s => Real.cos s * Ψ z s)
      (𝓝[<] (π / 2)) (𝓝 0)) →
    (∀ j l : ℕ, j + l ≤ 4 → ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |Work.Spaces.mixed j l (Work.Construction.Vop Ψ) z θ| ≤ K) →
    ∀ j i : ℕ, j + i ≤ 4 → ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |Work.Spaces.mixed j i Ψ z θ| ≤ C * K := by
  classical
  -- ## the universal angular coefficient bounds
  obtain ⟨A, hAnn, hAb⟩ := exists_LopIter_bound (fun θ : ℝ => Real.sin (2 * θ))
    (by intro k; fun_prop) 3
  obtain ⟨B, hBnn, hBb⟩ := exists_LopIter_bound (fun θ : ℝ => 2 * Real.sin θ ^ 2)
    (by intro k; fun_prop) 3
  have hB1 : 1 ≤ B := by
    have h := hBb 0 (by norm_num) (π / 2) ⟨by linarith [Real.pi_pos], le_refl _⟩
    simp only [Work.FTS.EllipticEst.LopIter, Function.iterate_zero, id_eq] at h
    rw [Real.sin_pi_div_two] at h
    norm_num at h
    linarith
  -- ## the level constants
  let D : ℕ → ℝ := fun n =>
    Nat.rec (motive := fun _ => ℝ) 2 (fun k Dk => (2 : ℝ) ^ k * A + B * ((2 : ℝ) ^ k * Dk)) n
  have hD0 : D 0 = 2 := rfl
  have hDs : ∀ k, D (k + 1) = (2 : ℝ) ^ k * A + B * ((2 : ℝ) ^ k * D k) := fun k => rfl
  have hDnn : ∀ n, 0 ≤ D n := by
    intro n
    induction n with
    | zero => rw [hD0]; norm_num
    | succ k ih =>
        rw [hDs k]
        have h1 : 0 ≤ (2 : ℝ) ^ k * A := mul_nonneg (by positivity) hAnn
        have h2 : 0 ≤ B * ((2 : ℝ) ^ k * D k) := mul_nonneg hBnn (mul_nonneg (by positivity) ih)
        linarith
  have hDmono : ∀ n, D n ≤ D (n + 1) := by
    intro n
    rw [hDs n]
    have h2n : (1 : ℝ) ≤ (2 : ℝ) ^ n := one_le_pow₀ (by norm_num)
    have hB2 : (1 : ℝ) ≤ (2 : ℝ) ^ n * B := one_le_mul_of_one_le_of_one_le h2n hB1
    have hAn : 0 ≤ (2 : ℝ) ^ n * A := mul_nonneg (by positivity) hAnn
    nlinarith [hDnn n, mul_le_mul_of_nonneg_right hB2 (hDnn n)]
  have hDle : ∀ m n, m ≤ n → D m ≤ D n := fun m n h =>
    (monotone_nat_of_le_succ hDmono : Monotone D) h
  refine ⟨1 + D 0 + D 1 + D 2 + D 3 + D 4, by linarith [hDnn 0, hDnn 1, hDnn 2, hDnn 3, hDnn 4],
    ?_⟩
  intro K hK Ψ hsm hbd hjets
  have hVsm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.Vop Ψ) := smoothOpen_vop hsm
  -- ## the reconstruction
  have hrec : ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Real.cos θ * Ψ z θ = -(∫ s in θ..(π / 2), Real.cos s * Work.Construction.Vop Ψ z s) := by
    intro z θ hz hθ
    have hcos : Real.cos θ ≠ 0 :=
      ne_of_gt (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩)
    have hcont : ContinuousOn (fun s : ℝ => Real.cos s * Work.Construction.Vop Ψ z s)
        (Set.Ioo θ (π / 2)) := by
      have hslice : ContinuousOn (fun s : ℝ => Work.Construction.Vop Ψ z s)
          (Set.Ioo θ (π / 2)) := by
        intro s hs
        have hs' : (z, s) ∈ Work.FTS.EllipticEst.Q0 :=
          Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, lt_trans hθ.1 hs.1, hs.2⟩
        have hc : ContinuousAt (Function.uncurry (Work.Construction.Vop Ψ)) (z, s) :=
          hVsm.continuousOn.continuousAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds hs')
        exact (hc.comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
      exact (Real.continuous_cos.continuousOn).mul hslice
    have hint : IntervalIntegrable (fun s => Real.cos s * Work.Construction.Vop Ψ z s)
        volume θ (π / 2) := by
      constructor
      · refine MeasureTheory.IntegrableOn.of_bound ?hfin ?haesm K ?hb'
        · exact measure_Ioc_lt_top
        · rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
          exact hcont.aestronglyMeasurable measurableSet_Ioo
        · rw [ae_restrict_iff' measurableSet_Ioc]
          filter_upwards [MeasureTheory.Ioo_ae_eq_Ioc (μ := volume) (a := θ) (b := π / 2)]
            with s hs
          intro hsmem
          obtain ⟨hs1, hs2⟩ := hs.mpr hsmem
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Work.FTS_EllLimOK.cos_pos_of_mem_Ioo
            ⟨lt_trans hθ.1 hs1, hs2⟩)]
          have hVk : |Work.Construction.Vop Ψ z s| ≤ K :=
            hjets 0 0 (by norm_num) z s hz ⟨lt_trans hθ.1 hs1, hs2⟩
          simpa using mul_le_mul (Real.cos_le_one s) hVk (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      · refine integrableOn_empty.mono_set ?_
        intro s hs
        rw [Set.mem_Ioc] at hs
        linarith [hs.1, hθ.2]
    have hsliceC : ContinuousAt (fun s : ℝ => Real.cos s * Ψ z s) θ := by
      have hc : ContinuousAt (Function.uncurry Ψ) (z, θ) :=
        hsm.continuousOn.continuousAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩))
      have h1 : ContinuousAt (fun s : ℝ => Ψ z s) θ :=
        hc.comp (continuousAt_const.prodMk continuousAt_id)
      exact Real.continuous_cos.continuousAt.mul h1
    have hvr := Work.FTS_EllLimOK.Vop_reconstruct (Ψ := Ψ) (z := z) (θ := θ) hθ ?_ hint ?_
      (hbd z hz)
    · rw [hvr]
      field_simp
    · intro s hs
      exact ((hsm.curry_θ hz).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds ⟨lt_trans hθ.1 hs.1, hs.2⟩) |>.hasDerivAt
    · exact hsliceC.tendsto.mono_left nhdsWithin_le_nhds
  -- ## the z-derivative chain
  have hchain : ∀ j, j ≤ 4 → ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      Work.Spaces.DzIter j (fun z θ => Real.cos θ * Ψ z θ) z θ
        = -(∫ s in θ..(π / 2),
            Real.cos s * Work.Spaces.DzIter j (Work.Construction.Vop Ψ) z s) := by
    intro j
    induction j with
    | zero => intro _ z θ hz hθ; exact hrec z θ hz hθ
    | succ j ih =>
        intro hj z θ hz hθ
        have hji : j ≤ 4 := by omega
        have hIH := ih hji
        have hEqOn : Set.EqOn
            (Function.uncurry (Work.Spaces.DzIter j (fun z θ => Real.cos θ * Ψ z θ)))
            (Function.uncurry (fun z θ => -(∫ s in θ..(π / 2),
              Real.cos s * Work.Spaces.DzIter j (Work.Construction.Vop Ψ) z s)))
            Work.FTS.EllipticEst.Q0 := by
          intro p hp
          rcases p with ⟨z', θ'⟩
          obtain ⟨hz', hθ'1, hθ'2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
          exact hIH z' θ' hz' ⟨hθ'1, hθ'2⟩
        have hpz := Work.Spaces.pz_congr_of_isOpen Work.FTS.EllipticEst.isOpen_Q0 hEqOn
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)
        -- the parametrised-differentiation input
        have hzmem : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
        have hsub : Set.Ioo (z / 2) (2 * z) ×ˢ Set.Ioo θ (π / 2)
            ⊆ Work.FTS.EllipticEst.Q0 := by
          intro p hp
          obtain ⟨hp1, hp2⟩ := hp
          exact Work.FTS.EllipticEst.mem_Q0.mpr
            ⟨by linarith [hp1.1, hz], lt_trans hθ.1 hp2.1, hp2.2⟩
        have hW : ContinuousOn
            (Function.uncurry (Work.Spaces.DzIter j (Work.Construction.Vop Ψ)))
            (Set.Ioo (z / 2) (2 * z) ×ˢ Set.Ioo θ (π / 2)) :=
          ((hVsm.DzIter j).continuousOn).mono hsub
        have hW' : ContinuousOn
            (Function.uncurry (Work.Spaces.pz (Work.Spaces.DzIter j (Work.Construction.Vop Ψ))))
            (Set.Ioo (z / 2) (2 * z) ×ˢ Set.Ioo θ (π / 2)) :=
          (((hVsm.DzIter j).pz).continuousOn).mono hsub
        have hWb : ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ s ∈ Set.Ioo θ (π / 2),
            |Work.Spaces.DzIter j (Work.Construction.Vop Ψ) x s| ≤ max K (2 * K / z) := by
          intro x hx s hs
          exact le_trans (hjets j 0 (by omega) x s (by linarith [hx.1, hz])
            ⟨lt_trans hθ.1 hs.1, hs.2⟩) (le_max_left _ _)
        have hW'b : ∀ x ∈ Set.Ioo (z / 2) (2 * z), ∀ s ∈ Set.Ioo θ (π / 2),
            |Work.Spaces.pz (Work.Spaces.DzIter j (Work.Construction.Vop Ψ)) x s|
              ≤ max K (2 * K / z) := by
          intro x hx s hs
          have hxpos : 0 < x := by linarith [hx.1, hz]
          have hDz : Work.Spaces.pz (Work.Spaces.DzIter j (Work.Construction.Vop Ψ)) x s
              = Work.Spaces.DzIter (j + 1) (Work.Construction.Vop Ψ) x s / x := by
            have h := hjets (j + 1) 0 (by omega) x s hxpos ⟨lt_trans hθ.1 hs.1, hs.2⟩
            simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz] at h ⊢
            field_simp
          rw [hDz, abs_div, abs_of_pos hxpos]
          refine le_trans (div_le_div_of_nonneg_right
            (hjets (j + 1) 0 (by omega) x s hxpos ⟨lt_trans hθ.1 hs.1, hs.2⟩) hxpos.le) ?_
          have hxle : z / 2 ≤ x := le_of_lt hx.1
          have h2 : K / x ≤ 2 * K / z := by
            have h3 : K / x ≤ K / (z / 2) :=
              div_le_div_of_nonneg_left hK (by linarith) hxle
            have h4 : K / (z / 2) = 2 * K / z := by
              field_simp
            linarith [h3, h4.le]
          exact le_trans h2 (le_max_right _ _)
        have hderiv : ∀ s ∈ Set.Ioo θ (π / 2), ∀ x ∈ Set.Ioo (z / 2) (2 * z),
            HasDerivAt (fun x' => Work.Spaces.DzIter j (Work.Construction.Vop Ψ) x' s)
              (Work.Spaces.pz (Work.Spaces.DzIter j (Work.Construction.Vop Ψ)) x s) x := by
          intro s hs x hx
          exact (hVsm.DzIter j).hasDerivAt_slice ⟨lt_trans hθ.1 hs.1, hs.2⟩
            (by linarith [hx.1, hz])
        have hDiff := derivUnderIntegralIoo (W := Work.Spaces.DzIter j (Work.Construction.Vop Ψ))
          (W' := Work.Spaces.pz (Work.Spaces.DzIter j (Work.Construction.Vop Ψ)))
          (θ := θ) (C := max K (2 * K / z)) hθ isOpen_Ioo hzmem hW hW' hWb hW'b hderiv
        have hFpz : Work.Spaces.pz (fun z θ => -(∫ s in θ..(π / 2),
              Real.cos s * Work.Spaces.DzIter j (Work.Construction.Vop Ψ) z s)) z θ
            = -(∫ s in θ..(π / 2),
                Real.cos s * Work.Spaces.pz (Work.Spaces.DzIter j (Work.Construction.Vop Ψ)) z s) := by
          have hneg := hDiff.neg
          have hfun : (fun z' : ℝ => -(∫ s in θ..(π / 2),
                Real.cos s * Work.Spaces.DzIter j (Work.Construction.Vop Ψ) z' s))
              = Neg.neg (fun z' : ℝ => ∫ s in θ..(π / 2),
                Real.cos s * Work.Spaces.DzIter j (Work.Construction.Vop Ψ) z' s) := by
            funext z'; rfl
          show deriv (fun z' : ℝ => -(∫ s in θ..(π / 2),
                Real.cos s * Work.Spaces.DzIter j (Work.Construction.Vop Ψ) z' s)) z
            = -(∫ s in θ..(π / 2), Real.cos s * deriv (fun z' : ℝ =>
                Work.Spaces.DzIter j (Work.Construction.Vop Ψ) z' s) z)
          rw [hfun]
          exact hneg.deriv
        show z * Work.Spaces.pz (Work.Spaces.DzIter j (fun z θ => Real.cos θ * Ψ z θ)) z θ
            = -(∫ s in θ..(π / 2),
                Real.cos s * Work.Spaces.DzIter (j + 1) (Work.Construction.Vop Ψ) z s)
        rw [hpz, hFpz]
        rw [show -(∫ s in θ..(π / 2),
              Real.cos s * Work.Spaces.DzIter (j + 1) (Work.Construction.Vop Ψ) z s)
            = -(∫ s in θ..(π / 2), z * (Real.cos s
                * Work.Spaces.pz (Work.Spaces.DzIter j (Work.Construction.Vop Ψ)) z s)) from by
          congr 1
          refine intervalIntegral.integral_congr fun s _ => ?_
          simp only [Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.pz]
          ring]
        rw [intervalIntegral.integral_const_mul]
        ring
  -- ## level 0
  have hbound0 : ∀ j, j ≤ 4 → ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |Work.Spaces.DzIter j Ψ z θ| ≤ 2 * K := by
    intro j hj z θ hz hθ
    have hcos := Work.FTS_EllLimOK.cos_pos_of_mem_Ioo hθ
    have h1 := hchain j hj z θ hz hθ
    have h2 : |Work.Spaces.DzIter j (fun z θ => Real.cos θ * Ψ z θ) z θ|
        ≤ K * (π / 2 - θ) := by
      rw [h1, abs_neg]
      have hkey := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := θ) (b := π / 2) (C := K)
        (f := fun s => Real.cos s * Work.Spaces.DzIter j (Work.Construction.Vop Ψ) z s) ?_
      · rw [Real.norm_eq_abs] at hkey
        rw [abs_of_pos (by linarith [hθ.2] : (0:ℝ) < π / 2 - θ)] at hkey
        exact hkey
      · intro s hs
        rw [Set.uIoc_of_le (le_of_lt hθ.2)] at hs
        obtain ⟨hs1, hs2⟩ := hs
        have hsnn : 0 ≤ Real.cos s := Real.cos_nonneg_of_mem_Icc
          ⟨by linarith [hs1, hθ.1, Real.pi_pos], hs2⟩
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hsnn]
        rcases eq_or_lt_of_le hs2 with hsp | hsp
        · rw [hsp, Real.cos_pi_div_two, zero_mul]
          exact hK
        · simpa using mul_le_mul (Real.cos_le_one s)
            (hjets j 0 (by omega) z s hz ⟨lt_trans hθ.1 hs1, hsp⟩)
            (abs_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
    have h3 : Work.Spaces.DzIter j Ψ z θ
        = Work.Spaces.DzIter j (fun z θ => Real.cos θ * Ψ z θ) z θ / Real.cos θ := by
      rw [DzIter_theta_const_mul (fun θ => Real.cos θ) Ψ j z θ hz hθ]
      field_simp
    rw [h3, abs_div, abs_of_pos hcos]
    have ht : π / 2 - θ ≤ (π / 2) * Real.cos θ := by
      have hsin : Real.sin (π / 2 - θ) = Real.cos θ := Real.sin_pi_div_two_sub θ
      have hmul := Real.mul_le_sin (x := π / 2 - θ) (by linarith [hθ.2]) (by linarith [hθ.1])
      rw [hsin] at hmul
      have h2 : (π / 2) * (2 / Real.pi * (π / 2 - θ)) = π / 2 - θ := by
        field_simp
      calc π / 2 - θ = (π / 2) * (2 / Real.pi * (π / 2 - θ)) := h2.symm
        _ ≤ (π / 2) * Real.cos θ := mul_le_mul_of_nonneg_left hmul (by linarith [Real.pi_pos])
    calc |Work.Spaces.DzIter j (fun z θ => Real.cos θ * Ψ z θ) z θ| / Real.cos θ
        ≤ K * (π / 2 - θ) / Real.cos θ := div_le_div_of_nonneg_right h2 hcos.le
      _ ≤ K * ((π / 2) * Real.cos θ) / Real.cos θ :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ht hK) hcos.le
      _ = K * (π / 2) := by field_simp
      _ ≤ 2 * K := by nlinarith [Real.pi_lt_four, hK]
  -- ## the induction on the level
  have key : ∀ n, n ≤ 4 → ∀ j, j + n ≤ 4 → ∀ z θ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
      |Work.Spaces.mixed j n Ψ z θ| ≤ D n * K := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn j hjn z θ hz hθ
      rcases Nat.eq_zero_or_pos n with hn0 | hnpos
      · subst hn0
        simp only [Work.Spaces.mixed_zero_right, hD0]
        exact hbound0 j (by omega) z θ hz hθ
      · obtain ⟨n', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
        -- coefficient bound at the level `n'`
        have hAb' : ∀ m ≤ n', ∀ θ' ∈ Work.Spaces.Iθ,
            |Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => Real.sin (2 * θ)) θ'| ≤ A :=
          fun m hm θ' hθ' => hAb m (by omega) θ' hθ'
        have hBb' : ∀ m ≤ n', ∀ θ' ∈ Work.Spaces.Iθ,
            |Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => 2 * Real.sin θ ^ 2) θ'| ≤ B :=
          fun m hm θ' hθ' => hBb m (by omega) θ' hθ'
        have hVb' : ∀ m ≤ n', ∀ z' θ', 0 < z' → θ' ∈ Set.Ioo 0 (π / 2) →
            |Work.Spaces.mixed j (n' - m) (Work.Construction.Vop Ψ) z' θ'| ≤ K :=
          fun m hm z' θ' hz' hθ' => hjets j (n' - m) (by omega) z' θ' hz' hθ'
        have hPb' : ∀ m ≤ n', ∀ z' θ', 0 < z' → θ' ∈ Set.Ioo 0 (π / 2) →
            |Work.Spaces.mixed j (n' - m) Ψ z' θ'| ≤ D (n' - m) * K :=
          fun m hm z' θ' hz' hθ' => ih (n' - m) (by omega) (by omega) j (by omega) z' θ' hz' hθ'
        have hshift : Work.Spaces.mixed j (n' + 1) Ψ z θ
            = Work.Spaces.mixed j n' (Work.Spaces.Dth Ψ) z θ := by
          simp only [Work.Spaces.mixed]
          rw [Work.FTS.TransportS.DthIter_shift]
        have hGeq : Set.EqOn (Function.uncurry (Work.Spaces.Dth Ψ))
            (Function.uncurry (fun z θ => Real.sin (2 * θ) * Work.Construction.Vop Ψ z θ
              + 2 * Real.sin θ ^ 2 * Ψ z θ)) Work.FTS.EllipticEst.Q0 := by
          intro p hp
          rcases p with ⟨z', θ'⟩
          obtain ⟨hz', hθ'1, hθ'2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
          exact Dth_eq_sfun_mul_add ⟨hθ'1, hθ'2⟩
        have hA1 : Work.FTS.EllipticEst.SmoothOpen
            (fun z θ => Real.sin (2 * θ) * Work.Construction.Vop Ψ z θ) :=
          smoothOpen_angular_mul (by fun_prop) hVsm
        have hA2 : Work.FTS.EllipticEst.SmoothOpen
            (fun z θ => 2 * Real.sin θ ^ 2 * Ψ z θ) :=
          smoothOpen_angular_mul (by fun_prop) hsm
        rw [hshift, mixed_congr_Q0 hGeq j n' z θ hz hθ,
          Work.FTS.EllipticEst.SmoothOpen.mixed_add hA1 hA2 j n' z θ hz hθ.1 hθ.2,
          mixed_angular_mul (c := fun θ : ℝ => Real.sin (2 * θ)) (by intro θ'; fun_prop)
            hVsm j n' hz hθ,
          mixed_angular_mul (c := fun θ : ℝ => 2 * Real.sin θ ^ 2) (by intro θ'; fun_prop)
            hsm j n' hz hθ]
        -- bound the two sums
        have hch : (∑ m ∈ Finset.range (n' + 1), (n'.choose m : ℝ)) = (2 : ℝ) ^ n' := by
          rw [← Nat.cast_sum, Nat.sum_range_choose, Nat.cast_pow]
          norm_num
        have hb1 : |∑ m ∈ Finset.range (n' + 1), (n'.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => Real.sin (2 * θ)) θ
              * Work.Spaces.mixed j (n' - m) (Work.Construction.Vop Ψ) z θ|
            ≤ (2 : ℝ) ^ n' * (A * K) := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          have hterm : ∀ m ∈ Finset.range (n' + 1),
              |(n'.choose m : ℝ)
                * Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => Real.sin (2 * θ)) θ
                * Work.Spaces.mixed j (n' - m) (Work.Construction.Vop Ψ) z θ|
              ≤ (n'.choose m : ℝ) * (A * K) := by
            intro m hm
            have hmle : m ≤ n' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
            have h1 : |Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => Real.sin (2 * θ)) θ| ≤ A :=
              hAb' m hmle θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
            have h2 := hVb' m hmle z θ hz hθ
            have hc : (0 : ℝ) ≤ (n'.choose m : ℝ) := Nat.cast_nonneg _
            have hAc : (n'.choose m : ℝ)
                * |Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => Real.sin (2 * θ)) θ|
                ≤ (n'.choose m : ℝ) * A := mul_le_mul_of_nonneg_left h1 hc
            rw [abs_mul, abs_mul, abs_of_nonneg hc]
            calc (n'.choose m : ℝ)
                  * |Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => Real.sin (2 * θ)) θ|
                  * |Work.Spaces.mixed j (n' - m) (Work.Construction.Vop Ψ) z θ|
                ≤ ((n'.choose m : ℝ) * A) * K :=
                  mul_le_mul hAc h2 (abs_nonneg _) (mul_nonneg hc hAnn)
              _ = (n'.choose m : ℝ) * (A * K) := by ring
          refine le_trans (Finset.sum_le_sum hterm) ?_
          rw [← Finset.sum_mul, hch]
        have hb2 : |∑ m ∈ Finset.range (n' + 1), (n'.choose m : ℝ)
              * Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => 2 * Real.sin θ ^ 2) θ
              * Work.Spaces.mixed j (n' - m) Ψ z θ|
            ≤ (2 : ℝ) ^ n' * (B * (D n' * K)) := by
          refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
          have hterm : ∀ m ∈ Finset.range (n' + 1),
              |(n'.choose m : ℝ)
                * Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => 2 * Real.sin θ ^ 2) θ
                * Work.Spaces.mixed j (n' - m) Ψ z θ|
              ≤ (n'.choose m : ℝ) * (B * (D n' * K)) := by
            intro m hm
            have hmle : m ≤ n' := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
            have h1 : |Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => 2 * Real.sin θ ^ 2) θ| ≤ B :=
              hBb' m hmle θ ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
            have h2 : |Work.Spaces.mixed j (n' - m) Ψ z θ| ≤ D n' * K :=
              le_trans (hPb' m hmle z θ hz hθ)
                (mul_le_mul_of_nonneg_right (hDle (n' - m) n' (by omega)) hK)
            have hc : (0 : ℝ) ≤ (n'.choose m : ℝ) := Nat.cast_nonneg _
            have hBc : (n'.choose m : ℝ)
                * |Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => 2 * Real.sin θ ^ 2) θ|
                ≤ (n'.choose m : ℝ) * B := mul_le_mul_of_nonneg_left h1 hc
            rw [abs_mul, abs_mul, abs_of_nonneg hc]
            calc (n'.choose m : ℝ)
                  * |Work.FTS.EllipticEst.LopIter m (fun θ : ℝ => 2 * Real.sin θ ^ 2) θ|
                  * |Work.Spaces.mixed j (n' - m) Ψ z θ|
                ≤ ((n'.choose m : ℝ) * B) * (D n' * K) :=
                  mul_le_mul hBc h2 (abs_nonneg _) (mul_nonneg hc hBnn)
              _ = (n'.choose m : ℝ) * (B * (D n' * K)) := by ring
          refine le_trans (Finset.sum_le_sum hterm) ?_
          rw [← Finset.sum_mul, hch]
        refine le_trans (abs_add_le _ _) ?_
        refine le_trans (add_le_add hb1 hb2) ?_
        have heq : (2 : ℝ) ^ n' * (A * K) + (2 : ℝ) ^ n' * (B * (D n' * K))
            = ((2 : ℝ) ^ n' * A + B * ((2 : ℝ) ^ n' * D n')) * K := by ring
        rw [hDs, heq]
  -- ## assembly
  intro j i hji z θ hz hθ
  have hi4 : i ≤ 4 := by omega
  have h1 := key i hi4 j hji z θ hz hθ
  have h2 : D i ≤ 1 + D 0 + D 1 + D 2 + D 3 + D 4 := by
    interval_cases i <;> linarith [hDnn 0, hDnn 1, hDnn 2, hDnn 3, hDnn 4]
  calc |Work.Spaces.mixed j i Ψ z θ| ≤ D i * K := h1
    _ ≤ (1 + D 0 + D 1 + D 2 + D 3 + D 4) * K := mul_le_mul_of_nonneg_right h2 hK


end Work.FTS_EllLimOK.VopTransfer
