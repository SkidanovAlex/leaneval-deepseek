/-
Copyright: work module for the Elgindi finite-time singularity project.

# The left half of the 1-D slice dichotomy

`0 ≤ Phi f θ₀ - ∫_0^{θ₀} σ f f''`  for `θ₀ ∈ (0, π/2)`.

Via the identity `σ f f'' = (Phi f)' - Psi f` (`slice_second_identity.lean`, `Psi f ≥ 0`) this
is the statement `A ≥ 0` for `A = lim_{ε→0}(Phi f ε + ∫_ε^{θ₀} Psi f) = Phi f θ₀ - ∫_0^{θ₀} σ f f''`.
Contrapositively: if `A < 0` then `Phi f ε ≤ -b` for all small `ε`, which is impossible by
`slice_left_bad_case`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_second_defs
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_second_identity
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_second_trunc
import Submission.Work.FTS.EllipticEst.Cores.AeStep2Aux.slice_left_bad_case

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.Cores.AeStep2Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The antitone family `t n = min (1/(n+1)) (θ₀/2)`, shrinking to `0`. -/
def shrink (θ₀ : ℝ) (n : ℕ) : ℝ := min (1 / ((n : ℝ) + 1)) (θ₀ / 2)

theorem shrink_pos {θ₀ : ℝ} (h : 0 < θ₀) (n : ℕ) : 0 < shrink θ₀ n :=
  lt_min (by positivity) (by linarith)

theorem shrink_le {θ₀ : ℝ} (n : ℕ) : shrink θ₀ n ≤ θ₀ / 2 := min_le_right _ _

theorem shrink_antitone {θ₀ : ℝ} : Antitone (shrink θ₀) := by
  intro m n hmn
  refine min_le_min ?_ le_rfl
  have hm : (0:ℝ) < (m : ℝ) + 1 := by positivity
  have hle : (m : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hmn
  exact one_div_le_one_div_of_le hm hle

theorem shrink_tendsto (θ₀ : ℝ) (hθ₀ : 0 ≤ θ₀) : Tendsto (shrink θ₀) atTop (nhds 0) := by
  have h1 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have h2 : Tendsto (fun _ : ℕ => θ₀ / 2) atTop (nhds (θ₀ / 2)) := tendsto_const_nhds
  have h3 := h1.min h2
  have h4 : min (0:ℝ) (θ₀ / 2) = 0 := min_eq_left (by linarith)
  have h3' : Tendsto (fun b : ℕ => min (1 / ((b:ℝ) + 1)) (θ₀ / 2)) atTop (nhds 0) := by
    simpa only [h4] using h3
  exact h3'

theorem shrink_iInter_eq_empty (θ₀ : ℝ) (hθ₀ : 0 ≤ θ₀) : (⋂ n : ℕ, Ioo 0 (shrink θ₀ n)) = ∅ := by
  apply le_antisymm _ (empty_subset _)
  intro x hx
  rw [mem_iInter] at hx
  have hx0 : 0 < x := (hx 0).1
  obtain ⟨N, hN⟩ := eventually_atTop.1 ((shrink_tendsto θ₀ hθ₀).eventually_lt_const hx0)
  exact absurd (hN N le_rfl) (not_lt.mpr (le_of_lt (hx N).2))

theorem integral_Ioo_shrink_tendsto_zero {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {Γ : ℝ → ℝ} (hΓ : IntegrableOn Γ (Ioo 0 θ₀)) :
    Tendsto (fun n : ℕ => ∫ θ in Ioo 0 (shrink θ₀ n), |Γ θ|) atTop (nhds 0) := by
  have hΓabs : IntegrableOn (fun θ => |Γ θ|) (Ioo 0 θ₀) := by
    have h := hΓ.norm
    simpa only [Real.norm_eq_abs, IntegrableOn] using h
  have hanti : Antitone (fun n : ℕ => Ioo 0 (shrink θ₀ n)) :=
    fun m n hmn => Ioo_subset_Ioo_right (shrink_antitone hmn)
  have hex : ∃ i, IntegrableOn (fun θ => |Γ θ|) (Ioo 0 (shrink θ₀ i)) :=
    ⟨0, hΓabs.mono_set (fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 (by
      have h := shrink_le (θ₀ := θ₀) 0; nlinarith [hθ₀])⟩)⟩
  have hmain := MeasureTheory.tendsto_setIntegral_of_antitone
    (μ := volume) (f := fun θ => |Γ θ|) (s := fun n : ℕ => Ioo 0 (shrink θ₀ n))
    (fun n => measurableSet_Ioo) hanti hex
  simpa only [shrink_iInter_eq_empty θ₀ (le_of_lt hθ₀), setIntegral_empty] using hmain

/-- **Left half of the slice dichotomy.**  `Phi f θ₀ - ∫_0^{θ₀} σ f f'' ≥ 0`. -/
theorem slice_left_integral_nonneg {f : ℝ → ℝ}
    (hf : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (h0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hint : MeasureTheory.IntegrableOn (sliceIntegrand f) (Set.Ioo 0 (Real.pi / 2)))
    {θ₀ : ℝ} (hθ₀ : θ₀ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ Phi f θ₀ - ∫ θ in Set.Ioo 0 θ₀, sliceIntegrand f θ := by
  by_contra hcon
  rw [not_le] at hcon
  have hθ₀0 : 0 < θ₀ := hθ₀.1
  have hθ₀lt : θ₀ < Real.pi / 2 := hθ₀.2
  have hΓint : IntegrableOn (sliceIntegrand f) (Ioo 0 θ₀) :=
    hint.mono_set (fun x hx => ⟨hx.1, lt_trans hx.2 hθ₀lt⟩)
  have hΓabs : IntegrableOn (fun θ => |sliceIntegrand f θ|) (Ioo 0 θ₀) := by
    have h := hΓint.norm
    simpa only [Real.norm_eq_abs, IntegrableOn] using h
  obtain ⟨S0, hS0⟩ : ∃ S0 : ℝ, S0 = Phi f θ₀ - ∫ θ in Ioo 0 θ₀, sliceIntegrand f θ :=
    ⟨_, rfl⟩
  have hS0lt : S0 < 0 := by rw [hS0]; exact hcon
  have hlim := integral_Ioo_shrink_tendsto_zero hθ₀0 (Γ := sliceIntegrand f) hΓint
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (∫ θ in Ioo 0 (shrink θ₀ n), |sliceIntegrand f θ|) < -S0 / 2 :=
    hlim.eventually_lt_const (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hsmall
  have htN : 0 < shrink θ₀ N := shrink_pos hθ₀0 N
  have htNle : shrink θ₀ N ≤ θ₀ / 2 := shrink_le N
  have htNlt : shrink θ₀ N < θ₀ := by nlinarith [hθ₀0]
  have hbad : ∀ θ ∈ Ioo 0 (shrink θ₀ N), Phi f θ ≤ -(-S0 / 2) := by
    intro θ hθ
    have hθ0 : 0 < θ := hθ.1
    have hθt : θ < shrink θ₀ N := hθ.2
    have hθθ₀ : θ < θ₀ := lt_trans hθt htNlt
    have htrunc := slice_second_trunc hf hθ0 hθ₀lt (le_of_lt hθθ₀)
    have hI : (∫ x in θ..θ₀, sliceIntegrand f x) = ∫ x in Ioc θ θ₀, sliceIntegrand f x :=
      intervalIntegral.integral_of_le (le_of_lt hθθ₀)
    have hJ : (∫ x in θ..θ₀, Psi f x) = ∫ x in Ioc θ θ₀, Psi f x :=
      intervalIntegral.integral_of_le (le_of_lt hθθ₀)
    rw [hI, hJ] at htrunc
    have hsplit : (∫ x in Ioo 0 θ₀, sliceIntegrand f x)
        = (∫ x in Ioo 0 θ, sliceIntegrand f x) + ∫ x in Ioc θ θ₀, sliceIntegrand f x := by
      have hIoc0θ : IntegrableOn (sliceIntegrand f) (Ioc (0:ℝ) θ) :=
        hint.mono_set (fun x hx => ⟨hx.1, by linarith [hx.2, hθθ₀, hθ₀lt]⟩)
      have hIocθθ₀ : IntegrableOn (sliceIntegrand f) (Ioc θ θ₀) :=
        hint.mono_set (fun x hx => ⟨lt_trans hθ0 hx.1, by linarith [hx.2, hθ₀lt]⟩)
      rw [setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := (0:ℝ)) (b := θ₀)),
          setIntegral_congr_set (Ioo_ae_eq_Ioc (μ := volume) (a := (0:ℝ)) (b := θ))]
      have hunion : Ioc (0:ℝ) θ₀ = Ioc 0 θ ∪ Ioc θ θ₀ := by
        ext x
        constructor
        · intro hx
          by_cases h : x ≤ θ
          · exact Or.inl ⟨hx.1, h⟩
          · exact Or.inr ⟨lt_of_not_ge h, hx.2⟩
        · intro hx
          rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact ⟨h1, le_trans h2 (le_of_lt hθθ₀)⟩
          · exact ⟨lt_trans hθ0 h1, h2⟩
      rw [hunion, setIntegral_union (disjoint_left.mpr (fun x hx1 hx2 =>
            absurd hx2.1 (not_lt.mpr hx1.2))) measurableSet_Ioc hIoc0θ hIocθθ₀]
    have hPsi_nonneg : 0 ≤ ∫ x in Ioc θ θ₀, Psi f x :=
      setIntegral_nonneg measurableSet_Ioc
        (fun x hx => Psi_nonneg ⟨lt_trans hθ0 hx.1, lt_of_le_of_lt hx.2 hθ₀lt⟩)
    have hΓle : (∫ x in Ioo 0 θ, sliceIntegrand f x)
        ≤ ∫ x in Ioo 0 θ, |sliceIntegrand f x| :=
      setIntegral_mono (hΓint.mono_set (Ioo_subset_Ioo_right (le_of_lt hθθ₀)))
        (hΓabs.mono_set (Ioo_subset_Ioo_right (le_of_lt hθθ₀))) (fun x => le_abs_self _)
    have hmono : (∫ x in Ioo 0 θ, |sliceIntegrand f x|)
        ≤ ∫ x in Ioo 0 (shrink θ₀ N), |sliceIntegrand f x| :=
      setIntegral_mono_set (hΓabs.mono_set (Ioo_subset_Ioo_right (le_of_lt htNlt)))
        (Filter.Eventually.of_forall (fun x => abs_nonneg _))
        (Filter.Eventually.of_forall (fun x hx => ⟨hx.1, lt_trans hx.2 hθt⟩))
    have key : Phi f θ ≤ S0 + ∫ x in Ioo 0 (shrink θ₀ N), |sliceIntegrand f x| := by
      have h1 : Phi f θ = Phi f θ₀ - (∫ x in Ioc θ θ₀, sliceIntegrand f x)
          - ∫ x in Ioc θ θ₀, Psi f x := by linarith [htrunc]
      have h2 : (∫ x in Ioc θ θ₀, sliceIntegrand f x)
          = (∫ x in Ioo 0 θ₀, sliceIntegrand f x) - ∫ x in Ioo 0 θ, sliceIntegrand f x := by
        linarith [hsplit]
      rw [h1, h2, hS0]
      linarith [hPsi_nonneg, hΓle, hmono]
    linarith [key, hN N le_rfl]
  refine slice_left_bad_case (d := shrink θ₀ N) (b := -S0 / 2) htN
    (by nlinarith [htNle, hθ₀lt]) (by linarith)
    (hf.mono (Ioo_subset_Ioo_right (le_of_lt (show shrink θ₀ N < Real.pi / 2 by
      nlinarith [htNle, hθ₀lt])))) h0 hbad
    (hint.mono_set (fun x hx => ⟨hx.1, lt_of_lt_of_le hx.2 (by nlinarith [htNle, hθ₀lt])⟩))

end Work.FTS.EllipticEst.Cores.AeStep2Aux
