import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.remov.slice_ang_asm
import Submission.Work.FTS.EllipticEst.remov.ang_ode_iterate
import Submission.Work.FTS.EllipticEst.remov.slice_ang_reduce
import Submission.Work.FTS.EllipticEst.remov.angSlot_le_AngRHS
import Submission.Work.FTS.EllipticEst.remov.Baux.angSum_sq_le
import Submission.Work.FTS.EllipticEst.remov.Baux.angV_ident

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AngGainFinal`: from the `v = u / cos θ` slots to the top slot of `u`

Given the weighted `v`-bounds (`v = u / cos θ`, weights `q = sin(2θ)^{2k-γ}`)

`∫_Iθ (v^{(m)})² q ≤ C₀ · AngRHS k γ u g`   for every `m ≤ k+1`

we deduce the top-order angular estimate for `u` itself,

`∫_Iθ (u^{(k+2)})² q ≤ C · AngRHS k γ u g`.

The route is pointwise and elementary: `remov.Baux.angV_ident` writes `u^{(k+2)}` as the
Leibniz sum `Σ_j C(k+1,j) sin^{(k+1-j)}(θ) v^{(j)}` minus the two lower order terms `6u^{(k)}`
and `g^{(k)}`; `remov.Baux.angSum_sq_le` bounds the square of that sum by
`(2^{k+1})²(k+2) Σ_j (v^{(j)})²` (using `|sin^{(m)}| ≤ 1`), and the square of a sum of three
terms is at most three times the sum of the squares.  At the endpoints `θ = 0, π/2` the weight
`q` vanishes, so the pointwise inequality holds on all of `Iθ` and a monotone integral
comparison finishes.
-/

namespace Work.FTS.EllipticEst.AngGainFinal

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The gain constant (it depends only on `k`). -/
noncomputable def Mk (k : ℕ) : ℝ := 3 * (((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2)) + 108

lemma Mk_pos (k : ℕ) : 0 < Mk k := by
  have h1 : 0 ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2) := by positivity
  rw [Mk]; linarith

lemma Mk_ge_three (k : ℕ) : 3 * (((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2)) ≤ Mk k := by
  have h1 : 0 ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2) := by positivity
  rw [Mk]; linarith

lemma Mk_ge_108 (k : ℕ) : (108 : ℝ) ≤ Mk k := by
  have h1 : 0 ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2) := by positivity
  rw [Mk]; linarith

lemma Mk_ge_3 (k : ℕ) : (3 : ℝ) ≤ Mk k := le_trans (by norm_num) (Mk_ge_108 k)

/-- The abstract arithmetic of the gain: a Cauchy–Schwarz bound on `Ss²` together with the
nonnegativity of the four quantities gives the pointwise bound for the square of
`Ss - 6·Uk - Gk`. -/
lemma Mk_arith (k : ℕ) {Ss Sg Uk Gk : ℝ}
    (hcs : Ss ^ 2 ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2) * Sg)
    (hSg : 0 ≤ Sg) (hUk : 0 ≤ Uk ^ 2) (hGk : 0 ≤ Gk ^ 2) :
    (Ss - 6 * Uk - Gk) ^ 2 ≤ Mk k * (Sg + Uk ^ 2 + Gk ^ 2) := by
  have hA0 : 0 ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2) := by positivity
  have e1 : (Ss - 6 * Uk - Gk) ^ 2 ≤ 3 * (Ss ^ 2 + 36 * Uk ^ 2 + Gk ^ 2) := by
    nlinarith [sq_nonneg (Ss + 6 * Uk), sq_nonneg (Ss + Gk), sq_nonneg (6 * Uk - Gk)]
  have e2 : 3 * Ss ^ 2 ≤ 3 * (((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2) * Sg) := by
    nlinarith [hcs]
  have e3 : 3 * (((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2) * Sg) ≤ Mk k * Sg := by
    have h := mul_le_mul_of_nonneg_right (Mk_ge_three k) hSg
    linarith [h]
  have e4 : 108 * Uk ^ 2 ≤ Mk k * Uk ^ 2 :=
    mul_le_mul_of_nonneg_right (Mk_ge_108 k) hUk
  have e5 : 3 * Gk ^ 2 ≤ Mk k * Gk ^ 2 :=
    mul_le_mul_of_nonneg_right (Mk_ge_3 k) hGk
  linarith [e1, e2, e3, e4, e5]

/-- **The pointwise gain.**  On `Iθ` the top derivative of `u` is controlled by the `v`-slots
plus the two lower order slots of `u` and `g`, all with the weight `q`. -/
lemma angGain_pointwise (k : ℕ) (hk : 2 ≤ k) {γ : ℝ} (hγ : γ ≤ 5 / 4) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) :
    ∀ θ ∈ Work.Spaces.Iθ,
      (iteratedDeriv (k + 2) u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
        ≤ Mk k * ((∑ j ∈ Finset.range (k + 2),
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
            + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) := by
  have hExp : 2 * (k : ℝ) - γ ≠ 0 := by
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  intro θ hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · rw [← h0]
    have hQ0 : Real.rpow (Real.sin (2 * (0 : ℝ))) (2 * (k : ℝ) - γ) = 0 := by
      rw [show Real.sin (2 * (0 : ℝ)) = 0 by norm_num [Real.sin_zero]]
      exact Real.zero_rpow hExp
    rw [hQ0]
    simp
  rcases eq_or_lt_of_le hθ.2 with hpi | hpi
  · rw [hpi]
    have hQ0 : Real.rpow (Real.sin (2 * (Real.pi / 2))) (2 * (k : ℝ) - γ) = 0 := by
      rw [show Real.sin (2 * (Real.pi / 2)) = 0 by
        rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]]
      exact Real.zero_rpow hExp
    rw [hQ0]
    simp
  · have hIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨h0, hpi⟩
    have hQnn : 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
      Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_mem_Ioo ⟨by linarith, by linarith [Real.pi_pos]⟩)) _
    have hid := Work.FTS.EllipticEst.remov.Baux.angV_ident k hu hg θ hIoo
    have hsv : Work.FTS.EllipticEst.remov.sv u = (fun t => u t / Real.cos t) := rfl
    rw [hsv] at hid
    set Ss : ℝ := ∑ j ∈ Finset.range (k + 2), ((k + 1).choose j : ℝ)
        * iteratedDeriv (k + 1 - j) Real.sin θ
        * iteratedDeriv j (fun t => u t / Real.cos t) θ with hSs
    have hcs := Work.FTS.EllipticEst.remov.Baux.angSum_sq_le k
      (fun j => iteratedDeriv j (fun t => u t / Real.cos t) θ) θ
    rw [← hSs] at hcs
    have hSgnn : 0 ≤ ∑ j ∈ Finset.range (k + 2),
        (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hmain : (iteratedDeriv (k + 2) u θ) ^ 2 ≤ Mk k *
        ((∑ j ∈ Finset.range (k + 2),
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2)
          + (iteratedDeriv k u θ) ^ 2 + (iteratedDeriv k g θ) ^ 2) := by
      rw [hid]
      exact Mk_arith k (Ss := Ss)
        (Sg := ∑ j ∈ Finset.range (k + 2),
          (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2)
        (Uk := iteratedDeriv k u θ) (Gk := iteratedDeriv k g θ)
        hcs hSgnn (sq_nonneg _) (sq_nonneg _)
    have hexp : (∑ j ∈ Finset.range (k + 2),
            (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2)
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
        = ∑ j ∈ Finset.range (k + 2),
            (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
      Finset.sum_mul _ _ _
    calc (iteratedDeriv (k + 2) u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
        ≤ (Mk k * ((∑ j ∈ Finset.range (k + 2),
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2)
            + (iteratedDeriv k u θ) ^ 2 + (iteratedDeriv k g θ) ^ 2))
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
          mul_le_mul_of_nonneg_right hmain hQnn
      _ = Mk k * ((∑ j ∈ Finset.range (k + 2),
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
            + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) := by
          rw [mul_assoc, add_mul, add_mul, hexp]

theorem AngGainFinal (k : ℕ) (hk : 2 ≤ k)
    (hV : ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ), Work.FTS.EllipticEst.remov.SliceHyp k γ u g →
        ∀ m : ℕ, m ≤ k + 1 →
          MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ
          ∧ (∫ θ in Work.Spaces.Iθ, (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
              ≤ C * Work.FTS.EllipticEst.remov.AngRHS k γ u g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ), Work.FTS.EllipticEst.remov.SliceHyp k γ u g →
      (∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ C * Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
  obtain ⟨C₀, hC₀pos, hV'⟩ := hV
  refine ⟨Mk k * (((k : ℝ) + 2) * C₀ + 2), mul_pos (Mk_pos k) ?_, ?_⟩
  · have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [hC₀pos]
  · intro γ u g hH
    have hHmem : Work.FTS.EllipticEst.remov.SliceHyp k γ u g := hH
    obtain ⟨hγ1, hγ2, hu, hcont, hu0, hupi, hg, hInt_k2, hInt_gk, hInt_high, hInt_2, hInt_1,
      hInt_0⟩ := hH
    have hIθmeas : MeasurableSet Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]; exact measurableSet_Icc
    have hslotInt : ∀ m : ℕ, m ≤ k + 1 → IntegrableOn (fun θ =>
        (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ :=
      fun m hm => (hV' γ u g hHmem m hm).1
    have hslotBnd : ∀ m : ℕ, m ≤ k + 1 → (∫ θ in Work.Spaces.Iθ,
        (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ C₀ * Work.FTS.EllipticEst.remov.AngRHS k γ u g :=
      fun m hm => (hV' γ u g hHmem m hm).2
    have huk := Work.FTS.EllipticEst.remov.angSlot_le_AngRHS k hk γ u g hγ1 hγ2 hu hcont
      hInt_gk hInt_high hInt_2 hInt_1 hInt_0 k (by omega)
    have hIntUk : IntegrableOn (fun θ => (iteratedDeriv k u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ := huk.1
    have hBndUk : (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g := huk.2
    have hBndGk : (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g :=
      Work.FTS.EllipticEst.remov.g_slot_le_angRHS k γ u g
    -- integrability of the sum of the `v`-slots
    have hIntSum : IntegrableOn (fun θ => ∑ j ∈ Finset.range (k + 2),
        (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ :=
      MeasureTheory.integrable_finsetSum (Finset.range (k + 2))
        (f := fun j θ => (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        (fun j hj => hslotInt j (by rw [Finset.mem_range] at hj; omega))
    have hIntR : IntegrableOn (fun θ => Mk k * ((∑ j ∈ Finset.range (k + 2),
            (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
          + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
        Work.Spaces.Iθ :=
      ((hIntSum.add hIntUk).add hInt_gk).const_mul (Mk k)
    -- the pointwise bound, integrated
    have hmono : (∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ ∫ θ in Work.Spaces.Iθ, Mk k * ((∑ j ∈ Finset.range (k + 2),
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
            + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) :=
      MeasureTheory.setIntegral_mono_on hInt_k2 hIntR hIθmeas
        (angGain_pointwise k hk hγ2 hu hg)
    -- evaluate the right-hand side
    have hIvs : (∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range (k + 2),
            (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        = ∑ j ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ,
            (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
      MeasureTheory.integral_finsetSum (Finset.range (k + 2))
        (fun j hj => hslotInt j (by rw [Finset.mem_range] at hj; omega))
    have hIadd : (∫ θ in Work.Spaces.Iθ, ((∑ j ∈ Finset.range (k + 2),
            (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
          + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
        = (∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range (k + 2),
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k u θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) := by
      have h1 : (∫ θ in Work.Spaces.Iθ, ((∑ j ∈ Finset.range (k + 2),
            (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
          + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
        = (∫ θ in Work.Spaces.Iθ, ((∑ j ∈ Finset.range (k + 2),
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
          + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) :=
        MeasureTheory.integral_add (hIntSum.add hIntUk) hInt_gk
      have h2 : (∫ θ in Work.Spaces.Iθ, ((∑ j ∈ Finset.range (k + 2),
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
          = (∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range (k + 2),
                (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                  * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k u θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) :=
        MeasureTheory.integral_add hIntSum hIntUk
      rw [h1, h2]
    have hval : (∫ θ in Work.Spaces.Iθ, Mk k * ((∑ j ∈ Finset.range (k + 2),
            (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
          + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
        = Mk k * ((∑ j ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ,
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k u θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))) := by
      have h1 : (∫ θ in Work.Spaces.Iθ, Mk k * ((∑ j ∈ Finset.range (k + 2),
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
            + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
          = Mk k * (∫ θ in Work.Spaces.Iθ, ((∑ j ∈ Finset.range (k + 2),
                (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                  * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
              + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
              + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))) :=
        MeasureTheory.integral_const_mul (Mk k)
          (fun θ => ((∑ j ∈ Finset.range (k + 2),
                (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                  * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
              + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
              + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
      rw [h1, hIadd, hIvs]
    -- bound the sum of the `v`-slots
    have hbndA : (∑ j ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ,
            (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ ((k + 2 : ℕ) : ℝ) * (C₀ * Work.FTS.EllipticEst.remov.AngRHS k γ u g) := by
      have h := Finset.sum_le_card_nsmul (Finset.range (k + 2))
        (fun j => ∫ θ in Work.Spaces.Iθ, (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        (C₀ * Work.FTS.EllipticEst.remov.AngRHS k γ u g)
        (fun j hj => hslotBnd j (by rw [Finset.mem_range] at hj; omega))
      simpa only [Finset.card_range, nsmul_eq_mul] using h
    calc (∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ ∫ θ in Work.Spaces.Iθ, Mk k * ((∑ j ∈ Finset.range (k + 2),
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
            + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) :=
          hmono
      _ = Mk k * ((∑ j ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ,
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k u θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))) := hval
      _ ≤ Mk k * ((((k + 2 : ℕ) : ℝ) * (C₀ * Work.FTS.EllipticEst.remov.AngRHS k γ u g))
            + Work.FTS.EllipticEst.remov.AngRHS k γ u g
            + Work.FTS.EllipticEst.remov.AngRHS k γ u g) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Mk_pos k))
          linarith [hbndA, hBndUk, hBndGk]
      _ = Mk k * (((k : ℝ) + 2) * C₀ + 2) * Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
          push_cast
          ring

end Work.FTS.EllipticEst.AngGainFinal

