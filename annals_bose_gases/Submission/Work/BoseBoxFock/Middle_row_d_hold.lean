import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.Middle_channels_aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.Middle_row_d_hold` — the `(d)`-channel of the cubic middle kernel

This is the `(d)`-channel evaluation of `Middle` (design:
`FINDING_Middle_expansion_FALSE.md`, `Middle_eq_of_rows`): with
`c_s = fLh v fc μ N s`, `d_k = W1h v h μ fu N k`, `κ_n = kmomLab ℓ N n`, `ℓ = ellH v μ`,
`χ̂(p) = hatChi (ℓ • p)` and `χ_Λ = chiLam ℓ`,

    Σ_{s,k} c_s d_k · χ̂(ℓ•κ_{s−k})·θ_y·(e^{i⟪κ_s,x⟫}θ_x)·(χ̂(ℓ•κ_k)·θ_u)
      = θ_y·θ_x·θ_u·ℓ^{-3}·∫_w χ_Λ(w)·Ksfr(x+w)·Kχfr(w).

The `(d)`-channel differs from `(b)`/`(c)` in that the `u`-slot carries **no** phase: the whole
`u`-dependence is the prefactor `θ_u` (this is exactly the correction of
`FINDING_Middle_expansion_FALSE.md`), so the `k`-sum keeps only the `w` of the `χ̂`-representation
and produces the even frame `Kχfr` rather than a shifted phase.

## Proof

Write `inv3 = (ℓ³)⁻¹`.  The point of the computation is the box Fourier inversion
`χ̂(ℓ•κ_{s−k}) = inv3·∫_z χ_Λ(z)·e^{i⟪κ_s−κ_k,z⟫}dz` (`hatChi_eq_integral_plus`, with `hsub`
supplying `κ_{s−k} = κ_s − κ_k`).  Substituting this in each summand, pulling the *constant*
factors `c_s d_k·inv3·(e^{i⟪κ_s,x⟫}·χ̂(ℓ•κ_k))` into the integral
(`integral_const_mul`/`integral_mul_const`), swapping the (finite) double sum with the integral
(`integral_finsetSum`), and using

    e^{i⟪κ_s,x⟫}·e^{i⟪κ_s−κ_k,z⟫} = e^{i⟪κ_s,x+z⟫}·e^{−i⟪κ_k,z⟫}

(`Middle_row_d_phase2`, `Middle_row_d_exp_split`), the summed integrand factorises as

    inv3·χ_Λ(z)·(Σ_s c_s e^{i⟪κ_s,x+z⟫})·(Σ_k d_k χ̂(ℓ•κ_k) e^{−i⟪κ_k,z⟫})
      = inv3·χ_Λ(z)·Ksfr(x+z)·Kχfr(z),

the last factor by the reindexing `Kχfr_negPhase` (`k ↦ −k`, parity of `W1h`, `hatChih`,
`kmomLab`).  The `θ`-prefactors are constant in `(s,k)` and in `z` and are simply extracted.

All ingredients are `sorry`-free: `hatChi_eq_integral_plus`, `Kχfr_negPhase`,
`integrable_chiLam_mul_exp_plus` (`Middle_channels_aux`), the `Ksfr`/`Kχfr` definitions
(`pcfFrameDefs`), the box identity `ellH_zpow_neg_three` (`Middle_aux`) and the reindexing
`sum_neg_excited` (`Middle_aux`).  The only `MeasureTheory` inputs are linearity of the Bochner
integral and its finiteness for finite sums.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseBoxFock

local notation "Ω" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- `e^{i⟪a,x⟫}·e^{i⟪a,z⟫} = e^{i⟪a,x+z⟫}` (channel `(d)`: the `u`-slot carries no phase, so the
surviving phase is the `s`-phase with the shifted argument `x + z`). -/
lemma Middle_row_d_phase2 (a x z : Ω) :
    Complex.exp (Complex.I * (inner ℝ a x : ℂ)) * Complex.exp (Complex.I * (inner ℝ a z : ℂ))
      = Complex.exp (Complex.I * (inner ℝ a (x + z) : ℂ)) := by
  rw [← Complex.exp_add, inner_add_right]
  congr 1
  push_cast
  ring

/-- `e^{i⟪a−b,z⟫} = e^{i⟪a,z⟫}·e^{−i⟪b,z⟫}` (splitting the shifted phase into the `s`- and
`k`-frames). -/
lemma Middle_row_d_exp_split (a b z : Ω) :
    Complex.exp (Complex.I * (inner ℝ (a - b) z : ℂ))
      = Complex.exp (Complex.I * (inner ℝ a z : ℂ))
        * Complex.exp (-(Complex.I * (inner ℝ b z : ℂ))) := by
  rw [← Complex.exp_add]
  congr 1
  simp only [inner_sub_left]
  push_cast
  ring

theorem Middle_row_d_hold (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v)
    (fc fu : Work.BoseBoxFix.LowCut) (μ : ℝ) (N : ℕ) (x y u : EuclideanSpace ℝ (Fin 3))
    (hsub : ∀ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
      Work.BoseBoxFock.fLh v fc μ N s ≠ 0 →
      ∀ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
        Work.BoseBoxFock.W1h v h μ fu N k ≠ 0 →
      Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N (s - k)
        = Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s
          - Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k) :
    (∑ s ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
      ∑ k ∈ Work.BoseB7.excited (Work.BoseBoxFock.Lab N),
        ((Work.BoseBoxFock.fLh v fc μ N s * Work.BoseBoxFock.W1h v h μ fu N k : ℝ) : ℂ)
          * (((Work.BoseK15.corpusBox.hatChi ((Work.BoseBoxFock.ellH v μ) •
                  Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N (s - k)) : ℝ) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) y
              * (Complex.exp (Complex.I * (inner ℝ
                    (Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N s) x : ℂ))
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x)
              * (((Work.BoseK15.corpusBox.hatChi ((Work.BoseBoxFock.ellH v μ) •
                    Work.BoseBoxFock.kmomLab (Work.BoseBoxFock.ellH v μ) N k) : ℝ) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) u)))
      = Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) y
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) x
          * Work.BoseK15.corpusBox.thetaFun (Work.BoseBoxFock.ellH v μ) u
          * (((Work.BoseBoxFock.ellH v μ) ^ (-(3 : ℤ)) : ℝ) : ℂ)
          * ∫ w : EuclideanSpace ℝ (Fin 3),
              ((Work.BoseK15.corpusBox.chiLam (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)
              * Work.BoseBoxFock.Ksfr v fc μ N (x + w)
              * Work.BoseBoxFock.Kχfr v h μ fu N w := by
  set ℓ : ℝ := Work.BoseBoxFock.ellH v μ with hℓ
  set ex : Finset (Lab N) := Work.BoseB7.excited (Lab N) with hex
  set ĥ : Lab N → ℂ := fun n => ((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomLab ℓ N n) : ℝ) : ℂ) with hĥ
  set Es : Lab N → ℂ := fun s => Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N s) x : ℂ)) with hEs
  set ww : Lab N → Lab N → ℂ := fun s k => ((Work.BoseBoxFock.fLh v fc μ N s * Work.BoseBoxFock.W1h v h μ fu N k : ℝ) : ℂ) with hww
  set θy : ℂ := Work.BoseK15.corpusBox.thetaFun ℓ y with hθy
  set θx : ℂ := Work.BoseK15.corpusBox.thetaFun ℓ x with hθx
  set θu : ℂ := Work.BoseK15.corpusBox.thetaFun ℓ u with hθu
  set χc : Ω → ℂ := fun z => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ) with hχc
  show (∑ s ∈ ex, ∑ k ∈ ex, ww s k * (ĥ (s - k) * θy * (Es s * θx) * (ĥ k * θu)))
      = θy * θx * θu * ((ℓ ^ (-(3 : ℤ)) : ℝ) : ℂ)
        * ∫ w : Ω, χc w * Ksfr v fc μ N (x + w) * Kχfr v h μ fu N w
  -- Step 1: the `θ`-prefactors are constant in `(s,k)`; extract them.
  have hLHS : (∑ s ∈ ex, ∑ k ∈ ex, ww s k * (ĥ (s - k) * θy * (Es s * θx) * (ĥ k * θu)))
      = θy * θx * θu * (∑ s ∈ ex, ∑ k ∈ ex, ww s k * (ĥ (s - k) * Es s * ĥ k)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    ring
  -- Step 2: the core double sum.
  have hcore : (∑ s ∈ ex, ∑ k ∈ ex, ww s k * (ĥ (s - k) * Es s * ĥ k))
      = ((ℓ ^ 3 : ℝ) : ℂ)⁻¹ * ∫ w : Ω, χc w * Ksfr v fc μ N (x + w) * Kχfr v h μ fu N w := by
    set G : Lab N → Lab N → Ω → ℂ := fun s k z => ww s k * (((ℓ ^ 3 : ℝ) : ℂ)⁻¹ * ((χc z * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N s - Work.BoseBoxFock.kmomLab ℓ N k) z : ℂ))) * (Es s * ĥ k))) with hG
    -- each term of `G` is integrable (a constant times `χ_Λ·(plane wave)`)
    have hintG : ∀ s k, Integrable (G s k) := by
      intro s k
      have hbase : Integrable (fun z : Ω => ((Work.BoseK15.corpusBox.chiLam ℓ z : ℝ) : ℂ)
          * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N s - Work.BoseBoxFock.kmomLab ℓ N k) z : ℂ))) :=
        integrable_chiLam_mul_exp_plus ℓ (ellH_pos v μ) _
      refine (hbase.const_mul (ww s k * ((ℓ ^ 3 : ℝ) : ℂ)⁻¹ * (Es s * ĥ k))).congr ?_
      filter_upwards with z
      rw [hG]
      ring
    -- the per-summand Fourier inversion
    have hterm : ∀ s ∈ ex, ∀ k ∈ ex, ww s k * (ĥ (s - k) * Es s * ĥ k) = ∫ z : Ω, G s k z := by
      intro s hs k hk
      by_cases hw : ww s k = 0
      · rw [hw, zero_mul]
        have hz : G s k = fun _ : Ω => (0 : ℂ) := by
          funext z
          rw [hG]
          simp only [hw, zero_mul]
        rw [hz, MeasureTheory.integral_zero]
      · have hfl : fLh v fc μ N s ≠ 0 := fun hf => hw (by simp only [hww, hf, zero_mul, Complex.ofReal_zero])
        have hW1 : W1h v h μ fu N k ≠ 0 := fun hf => hw (by simp only [hww, hf, mul_zero, Complex.ofReal_zero])
        have hsub' : Work.BoseBoxFock.kmomLab ℓ N (s - k) = Work.BoseBoxFock.kmomLab ℓ N s - Work.BoseBoxFock.kmomLab ℓ N k := hsub s hs hfl k hk hW1
        have hkey : ĥ (s - k) = ((ℓ ^ 3 : ℝ) : ℂ)⁻¹ * ∫ z : Ω, χc z * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N s - Work.BoseBoxFock.kmomLab ℓ N k) z : ℂ)) := by
          have h1 : ĥ (s - k) = ((Work.BoseK15.corpusBox.hatChi (ℓ • (Work.BoseBoxFock.kmomLab ℓ N s - Work.BoseBoxFock.kmomLab ℓ N k)) : ℝ) : ℂ) := by
            show ((Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomLab ℓ N (s - k)) : ℝ) : ℂ) = _
            rw [hsub']
          rw [h1]
          exact hatChi_eq_integral_plus (ellH_pos v μ) _
        rw [hkey]
        rw [show ww s k * ((((ℓ ^ 3 : ℝ) : ℂ)⁻¹ * ∫ z : Ω, χc z * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N s - Work.BoseBoxFock.kmomLab ℓ N k) z : ℂ))) * Es s * ĥ k)
            = ww s k * (((ℓ ^ 3 : ℝ) : ℂ)⁻¹ * ((∫ z : Ω, χc z * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N s - Work.BoseBoxFock.kmomLab ℓ N k) z : ℂ))) * (Es s * ĥ k))) from by ring]
        rw [← integral_mul_const (Es s * ĥ k) (fun z : Ω => χc z * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N s - Work.BoseBoxFock.kmomLab ℓ N k) z : ℂ)))]
        rw [← integral_const_mul]
        rw [← integral_const_mul]
    -- swap the finite double sum with the integral
    have hfub : (∑ s ∈ ex, ∑ k ∈ ex, ∫ z : Ω, G s k z) = ∫ z : Ω, ∑ s ∈ ex, ∑ k ∈ ex, G s k z := by
      have h1 : ∫ z : Ω, (∑ s ∈ ex, ∑ k ∈ ex, G s k z) = ∑ s ∈ ex, ∫ z : Ω, ∑ k ∈ ex, G s k z :=
        integral_finsetSum ex (f := fun s z => ∑ k ∈ ex, G s k z)
          (fun s _ => integrable_finsetSum ex (fun k _ => hintG s k))
      have h2 : ∀ s ∈ ex, (∑ k ∈ ex, ∫ z : Ω, G s k z) = ∫ z : Ω, ∑ k ∈ ex, G s k z :=
        fun s _ => (integral_finsetSum ex (f := fun k => G s k) (fun k _ => hintG s k)).symm
      rw [h1]
      exact Finset.sum_congr rfl h2
    -- the summed integrand is `inv3·χ_Λ(z)·Ksfr(x+z)·Kχfr(z)`
    have hGp : ∀ z : Ω, (∑ s ∈ ex, ∑ k ∈ ex, G s k z)
        = ((ℓ ^ 3 : ℝ) : ℂ)⁻¹ * (χc z * Ksfr v fc μ N (x + z) * Kχfr v h μ fu N z) := by
      intro z
      have h1 : (∑ s ∈ ex, ∑ k ∈ ex, G s k z)
          = ((ℓ ^ 3 : ℝ) : ℂ)⁻¹ * χc z * (∑ s ∈ ex, ∑ k ∈ ex, ww s k * (Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N s - Work.BoseBoxFock.kmomLab ℓ N k) z : ℂ)) * Es s * ĥ k)) := by
        simp only [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [hG]
        ring
      have h2 : (∑ s ∈ ex, ∑ k ∈ ex, ww s k * (Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N s - Work.BoseBoxFock.kmomLab ℓ N k) z : ℂ)) * Es s * ĥ k))
          = (∑ s ∈ ex, (((fLh v fc μ N s : ℝ) : ℂ) * Es s * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N s) z : ℂ))))
            * (∑ k ∈ ex, ((((W1h v h μ fu N k * Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomLab ℓ N k)) : ℝ) : ℂ) * Complex.exp (-(Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) z : ℂ))))) := by
        have hk : ∀ s ∈ ex, (∑ k ∈ ex, ww s k * (Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N s - Work.BoseBoxFock.kmomLab ℓ N k) z : ℂ)) * Es s * ĥ k))
            = (((fLh v fc μ N s : ℝ) : ℂ) * Es s * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N s) z : ℂ)))
              * (∑ k ∈ ex, ((((W1h v h μ fu N k * Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomLab ℓ N k)) : ℝ) : ℂ) * Complex.exp (-(Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) z : ℂ))))) := by
          intro s _
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          simp only [hww, hEs, hĥ, Middle_row_d_exp_split (Work.BoseBoxFock.kmomLab ℓ N s) (Work.BoseBoxFock.kmomLab ℓ N k) z]
          rw [Complex.ofReal_mul, Complex.ofReal_mul]
          ring
        rw [Finset.sum_congr rfl hk]
        rw [← Finset.sum_mul]
      have h3 : (∑ s ∈ ex, (((fLh v fc μ N s : ℝ) : ℂ) * Es s * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N s) z : ℂ)))) = Ksfr v fc μ N (x + z) := by
        rw [Ksfr]
        rw [hex]
        refine Finset.sum_congr rfl (fun s _ => ?_)
        simp only [hEs, ← hℓ]
        rw [show ((fLh v fc μ N s : ℝ) : ℂ) * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N s) x : ℂ)) * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N s) z : ℂ))
            = ((fLh v fc μ N s : ℝ) : ℂ) * (Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N s) x : ℂ)) * Complex.exp (Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N s) z : ℂ))) from by ring]
        rw [Middle_row_d_phase2]
      have h4 : (∑ k ∈ ex, ((((W1h v h μ fu N k * Work.BoseK15.corpusBox.hatChi (ℓ • Work.BoseBoxFock.kmomLab ℓ N k)) : ℝ) : ℂ) * Complex.exp (-(Complex.I * (inner ℝ (Work.BoseBoxFock.kmomLab ℓ N k) z : ℂ))))) = Kχfr v h μ fu N z := by
        rw [Kχfr_negPhase]
        rw [hex]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simp only [hatChih, ← hℓ]
      rw [h1, h2, h3, h4]
      ring
    calc (∑ s ∈ ex, ∑ k ∈ ex, ww s k * (ĥ (s - k) * Es s * ĥ k))
        = ∑ s ∈ ex, ∑ k ∈ ex, ∫ z : Ω, G s k z :=
          Finset.sum_congr rfl (fun s hs => Finset.sum_congr rfl (fun k hk => hterm s hs k hk))
      _ = ∫ z : Ω, ∑ s ∈ ex, ∑ k ∈ ex, G s k z := hfub
      _ = ∫ z : Ω, ((ℓ ^ 3 : ℝ) : ℂ)⁻¹ * (χc z * Ksfr v fc μ N (x + z) * Kχfr v h μ fu N z) :=
          integral_congr_ae (Filter.Eventually.of_forall hGp)
      _ = ((ℓ ^ 3 : ℝ) : ℂ)⁻¹ * ∫ z : Ω, χc z * Ksfr v fc μ N (x + z) * Kχfr v h μ fu N z :=
          integral_const_mul _ _
  -- Step 3: reassemble.
  rw [hLHS, hcore, ellH_zpow_neg_three]
  ring

end Work.BoseBoxFock
