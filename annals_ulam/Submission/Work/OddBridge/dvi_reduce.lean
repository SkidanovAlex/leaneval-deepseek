import Mathlib
import Submission.Work.OddBridge.KernelDefs
import Submission.Work.Geometry.Ulam.ulam_g2ds

/-!
# The two `KvecM → Kvec` bridges of `(dvi)`

`Work.OddBridge.dvi_of_volterra` compares the vector-valued expression

`- ∫₀¹ (√(τ(1-τ)))⁻¹ • KvecM n h s s (x s) (y s) (x's) (y's)
   + ∫_s^1 ∂₁ (u ↦ ∫₀¹ (√(τ(1-τ)))⁻¹ • KvecM n h (u+τ(σ-u)) σ (x σ) (y σ) (x'σ) (y'σ))`

(the formalisation of Ryabogin's `(dvi)`, Annals 195 (2022), with the *manifest* kernel `KvecM` of
`KernelDefs.lean`) with the right hand side `Qtilde`, whereas the Volterra system `VolterraEqOn`
is stated with the paper's `Kvec` and the *componentwise* derivatives `∂₁ (G₂)ᵢ`.

The two facts about this comparison that are *unconditional* are isolated here: the triangle
`a ≤ u ≤ σ ≤ 1` on which `hae` identifies the two kernels also carries the moving point
`u + τ(σ-u)` of the Abel average, so on the neighbourhood `(a,σ)` of `s` the two vector-valued
functions agree, hence so do their `deriv`s (`Filter.EventuallyEq.deriv_eq` needs no regularity).

The remaining input -- that a vector-valued `deriv` may be read off componentwise -- is *not*
available from the hypotheses of `dvi_of_volterra`; see the discussion in
`Submission/Work/OddBridge/dvi_of_volterra.lean`.
-/

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval

namespace Work.OddBridge

open Work.OddVolterra

noncomputable section

/-- The Abel weight `(√(τ(1-τ)))⁻¹` is interval integrable on `[0,1]`. -/
lemma abelWeight_intervalIntegrable :
    IntervalIntegrable (fun τ : ℝ => (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹) volume (0 : ℝ) 1 :=
  Commons.Geometry.Ulam.intervalIntegrable_abel_weight

/-- **The diagonal value of `G₂`.**  On the diagonal `σ = s` the moving point `s + τ(σ-s)`
collapses, so `G₂` is the total Abel mass of the weight times the diagonal kernel:
`G₂(s,s,z) = (∫₀¹ (√(τ(1-τ)))⁻¹ dτ) • K(s,s,z)`.  Both sides are `Fin 2 → ℝ`. -/
lemma G2_self_eq_smul (n : ℕ) (h : ℝ → ℝ) (s : ℝ) (x y x' y' : ℝ) :
    G2 n h s s x y x' y'
      = (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹) •
          Kvec n h s s x y x' y' := by
  funext i
  simp only [G2, Pi.smul_apply, smul_eq_mul]
  have harg : ∀ τ : ℝ, s + τ * (s - s) = s := fun τ => by ring
  simp_rw [harg]
  have hfun : (fun τ : ℝ => Kvec n h s s x y x' y' i / Real.sqrt (τ * ((1 : ℝ) - τ)))
      = fun τ : ℝ => Kvec n h s s x y x' y' i * (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ := by
    funext τ
    rw [div_eq_mul_inv]
  rw [hfun, intervalIntegral.integral_const_mul]
  ring

/-- **The first term of `(dvi)`.**  `hae` at `(s,s)` identifies the manifest diagonal kernel with
the paper's, and the `τ`-integral of a constant vector against the Abel weight is the total mass
times the vector; hence the first term of `(dvi)` written with `KvecM` is exactly the diagonal
value of `G₂`. -/
theorem dvi_first_term_eq (n : ℕ) {h x y : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hae : ∀ s σ : ℝ, a ≤ s → s ≤ σ → σ ≤ 1 →
      KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)
        = Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)) :
    ∀ s ∈ Set.Ioo a 1,
      (∫ τ in (0 : ℝ)..1, (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ •
          KvecM n h s s (x s) (y s) (deriv x s) (deriv y s))
        = G2 n h s s (x s) (y s) (deriv x s) (deriv y s) := by
  intro s hs
  rw [intervalIntegral.integral_smul_const, G2_self_eq_smul,
    hae s s (le_of_lt hs.1) le_rfl (le_of_lt hs.2)]

/-- **The second term of `(dvi)`.**  For `σ ∈ (s,1)` and `u ∈ (a,σ)` the moving point
`u + τ(σ-u)` lies in `[u,σ] ⊆ [a,1]`, so `hae` applies to the whole `τ`-integrals and the two
vector-valued functions `u ↦ ∫₀¹ (√(τ(1-τ)))⁻¹ • KvecM n h (u+τ(σ-u)) σ …` and
`u ↦ G₂ n h u σ …` agree on the neighbourhood `(a,σ)` of `s`; hence their `deriv`s at `s` agree,
and so do the `σ`-integrals.

The inner `τ`-integrability is the only extra input: it is what allows the component of the
`τ`-integral to be computed componentwise (`ContinuousLinearMap.intervalIntegral_comp_comm`). -/
theorem dvi_second_term_eq_G2 (n : ℕ) {h x y : ℝ → ℝ} {a : ℝ} (ha : 0 < a)
    (hae : ∀ s σ : ℝ, a ≤ s → s ≤ σ → σ ≤ 1 →
      KvecM n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ)
        = Kvec n h s σ (x σ) (y σ) (deriv x σ) (deriv y σ))
    (hint : ∀ σ : ℝ, ∀ u ∈ Set.Ioo a σ,
      IntervalIntegrable (fun τ : ℝ => (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ •
        KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ) (deriv x σ) (deriv y σ))
        volume (0 : ℝ) 1) :
    ∀ s ∈ Set.Ioo a 1,
      (∫ σ in s..1, deriv (fun u : ℝ => ∫ τ in (0 : ℝ)..1,
          (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ •
          KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s)
        = (∫ σ in s..1, deriv (fun u : ℝ =>
            G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) s) := by
  intro s hs
  have hsa : a < s := hs.1
  refine intervalIntegral.integral_congr_Ioo_of_le (le_of_lt hs.2) (fun σ hσ => ?_)
  have hsσ : s < σ := hσ.1
  have hσ1 : σ < 1 := hσ.2
  have hmem : Set.Ioo a σ ∈ 𝓝 s := isOpen_Ioo.mem_nhds ⟨hsa, hsσ⟩
  refine Filter.EventuallyEq.deriv_eq ?_
  filter_upwards [hmem] with u hu
  have hu_lt : u < σ := hu.2
  funext i
  have hproj := ContinuousLinearMap.intervalIntegral_comp_comm (𝕜 := ℝ)
    (L := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i)
    (hint σ u hu)
  rw [ContinuousLinearMap.proj_apply] at hproj
  rw [show (G2 n h u σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i
      = ∫ τ in (0 : ℝ)..1,
          (Kvec n h (u + τ * (σ - u)) σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i /
            Real.sqrt (τ * ((1 : ℝ) - τ)) from rfl]
  rw [← hproj]
  refine intervalIntegral.integral_congr (fun τ hτ => ?_)
  rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hτ
  have hτ0 : 0 ≤ τ := hτ.1
  have hτ1 : τ ≤ 1 := hτ.2
  have hsub_nonneg : 0 ≤ σ - u := by linarith
  have hle_a : a ≤ u + τ * (σ - u) := by
    nlinarith [mul_nonneg hτ0 hsub_nonneg, hu.1]
  have hle_σ : u + τ * (σ - u) ≤ σ := by
    nlinarith [mul_le_of_le_one_left hsub_nonneg hτ1]
  show (Real.sqrt (τ * ((1 : ℝ) - τ)))⁻¹ *
        KvecM n h (u + τ * (σ - u)) σ (x σ) (y σ) (deriv x σ) (deriv y σ) i
    = (Kvec n h (u + τ * (σ - u)) σ (x σ) (y σ) (deriv x σ) (deriv y σ)) i /
        Real.sqrt (τ * ((1 : ℝ) - τ))
  rw [hae (u + τ * (σ - u)) σ hle_a hle_σ (le_of_lt hσ1), div_eq_mul_inv]
  ring

end

end Work.OddBridge
