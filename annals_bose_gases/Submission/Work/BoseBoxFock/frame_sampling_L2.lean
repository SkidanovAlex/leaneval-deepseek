import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.kinFT_neg_eq_conj
import Submission.Work.BoseBoxFock.latticePoisson_kernel
import Submission.Work.BoseBoxFock.sampling_integral
import Submission.Work.BoseFixB1.chi_boundary_taylor
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.frame_sampling_L2` — the `L²` frame-sampling identity

The theorem is the Poisson/aliasing ("frame") identity of the dilute-Bose-gas box analysis:

    (ℓ³)⁻¹ Σ_n Ŵ(k_n) Φ̂(k_n) conj(Ψ̂(k_n))
      = ∫_y ∫_z Φ(y) Ψ(z) Σ_m W(z − y + ℓ·m)  dy dz ,

where `k_n = kmomInt ℓ n = (2π/ℓ)·n` is the sampling lattice, `W` is smooth with compact
support, `Φ = χ_ℓ·u`, `Ψ = χ_ℓ·v` are the windowed states (`χ_ℓ = chiScale ℓ`, a smooth bump
supported in the box `[−ℓ/2,ℓ/2]³`), and `̂` is the `p`-convention Fourier transform
`Submission.BoseGases.kinFT`.

## Proof

The two sides are computed separately.

* The **right-hand side**.  For fixed `z`, `Σ_m W(z − y + ℓm) = P(z − y)` is the `ℓℤ³`-
  periodisation of `W`, and `Work.BoseBoxFock.latticePoisson_kernel` (the corpus's Poisson
  summation `Work.BoseFixR.poisson_scaled` applied to the translate `W(· + z − y)`) expands it
  in the sampling lattice:

      Σ_m W(z − y + ℓm) = (ℓ³)⁻¹ Σ_n Ŵ(k_n) e^{i⟪k_n, z − y⟫} .

  Splitting the phase and integrating in `z` against `Ψ` (interchange provided by the
  just-committed `Work.BoseBoxFock.sampling_integral`, used here in its `+i` form) gives, for
  every `y`,

      ∫_z Ψ(z) Σ_m W(z − y + ℓm) dz
        = (ℓ³)⁻¹ Σ_n Ŵ(k_n) conj(Ψ̂(k_n)) e^{−i⟪k_n, y⟫} ,

  the conjugation coming from the real-valuedness of `Ψ` (`Work.BoseBoxFock.kinFT_neg_eq_conj`).

* The **left-hand side** is then obtained by integrating in `y` against `Φ` with the `−i` form
  of `Work.BoseBoxFock.sampling_integral`, which converts `e^{−i⟪k_n, y⟫}` into `Φ̂(k_n)`.

All series are absolutely convergent: `Ŵ(k_n) = O((1+‖k_n‖)^{-4})` by smoothness and compact
support of `W` (`Work.OneBodyKin.kinFT_decay_le`), and `Φ̂`, `Ψ̂` are bounded by the `L¹` norms
of the windowed states.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 800000

/-! ## Elementary phase bookkeeping -/

private lemma norm_exp_I_ofReal (x : ℝ) : ‖Complex.exp (Complex.I * (x : ℂ))‖ = 1 := by
  rw [mul_comm Complex.I (x : ℂ)]
  exact Complex.norm_exp_ofReal_mul_I x

private lemma norm_exp_neg_I_ofReal (x : ℝ) : ‖Complex.exp (-(Complex.I * (x : ℂ)))‖ = 1 := by
  rw [show -(Complex.I * (x : ℂ)) = ((-x : ℝ) : ℂ) * Complex.I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

private lemma exp_neg_I_negC (y : ℂ) :
    Complex.exp (-(Complex.I * (-y))) = Complex.exp (Complex.I * y) := by
  congr 1
  ring

/-- The trivial bound `‖kinFT g p‖ ≤ ∫ ‖g‖`. -/
private lemma norm_kinFT_le (g : E3 → ℂ) (p : E3) :
    ‖Submission.BoseGases.kinFT g p‖ ≤ ∫ z, ‖g z‖ := by
  rw [Submission.BoseGases.kinFT]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Eventually.of_forall (fun y => ?_))
  simp only [norm_mul, norm_exp_neg_I_ofReal, one_mul]

/-- The `+i` form of the term-by-term integration, obtained from the `-i` form
`Work.BoseBoxFock.sampling_integral_tsum` by negating the momenta. -/
private theorem sampling_integral_pos {ℓ : ℝ} {c : (Fin 3 → ℤ) → ℂ}
    (hc : Summable fun m => ‖c m‖) {g : E3 → ℂ} (hg : MeasureTheory.Integrable g) :
    (∫ s, g s * (∑' m : Fin 3 → ℤ, c m
        * Complex.exp (Complex.I * (inner ℝ (kmomInt ℓ m) s : ℂ))))
      = ∑' m : Fin 3 → ℤ, c m * Submission.BoseGases.kinFT g (-(kmomInt ℓ m)) := by
  have hphase : ∀ (m : Fin 3 → ℤ) (s : E3),
      Complex.exp (-(Complex.I * (inner ℝ (-(kmomInt ℓ m)) s : ℂ)))
        = Complex.exp (Complex.I * (inner ℝ (kmomInt ℓ m) s : ℂ)) := by
    intro m s
    rw [inner_neg_left, Complex.ofReal_neg, exp_neg_I_negC]
  have key := sampling_integral_tsum (c := c) (p := fun m : Fin 3 → ℤ => -(kmomInt ℓ m)) hc hg
  have hterm : ∀ m : Fin 3 → ℤ,
      (∫ s, g s * Complex.exp (-(Complex.I * (inner ℝ (-(kmomInt ℓ m)) s : ℂ))))
        = Submission.BoseGases.kinFT g (-(kmomInt ℓ m)) := by
    intro m
    rw [show (fun s : E3 => g s * Complex.exp (-(Complex.I * (inner ℝ (-(kmomInt ℓ m)) s : ℂ))))
        = fun s : E3 => Complex.exp (-(Complex.I * (inner ℝ (-(kmomInt ℓ m)) s : ℂ))) * g s
        from funext (fun s => mul_comm _ _)]
    rw [Submission.BoseGases.kinFT]
  have hLHS : (∫ s, g s * (∑' m : Fin 3 → ℤ, c m
        * Complex.exp (Complex.I * (inner ℝ (kmomInt ℓ m) s : ℂ))))
      = ∫ s, g s * (∑' m : Fin 3 → ℤ, c m
          * Complex.exp (-(Complex.I * (inner ℝ (-(kmomInt ℓ m)) s : ℂ)))) := by
    have hpt : ∀ s : E3, g s * (∑' m : Fin 3 → ℤ, c m
          * Complex.exp (Complex.I * (inner ℝ (kmomInt ℓ m) s : ℂ)))
        = g s * (∑' m : Fin 3 → ℤ, c m
          * Complex.exp (-(Complex.I * (inner ℝ (-(kmomInt ℓ m)) s : ℂ)))) := by
      intro s
      congr 1
      exact tsum_congr (fun m => by rw [hphase m s])
    exact integral_congr_ae (Eventually.of_forall hpt)
  rw [hLHS, key]
  refine tsum_congr (fun m => ?_)
  rw [hterm m]

/-- **The inner aliasing identity.**  For a real-valued integrable `g`, the `z`-integral of `g`
against the `ℓℤ³`-periodisation of `W` is the sampling series of `Ŵ` against `ĝ`, phase-shifted
by `y`.  This is the first half of `frame_sampling_L2`. -/
private theorem frame_sampling_L2_inner {ℓ : ℝ} (hℓ : 0 < ℓ) {W : E3 → ℂ}
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (hWs : HasCompactSupport W)
    {g : E3 → ℂ} (hg : MeasureTheory.Integrable g)
    (hgstar : ∀ x, (starRingEnd ℂ) (g x) = g x) (y : E3) :
    (∫ z, g z * (∑' m : Fin 3 → ℤ, W (z - y + ℓ • latVec m)))
      = ((ℓ : ℂ) ^ 3)⁻¹ * (∑' n : Fin 3 → ℤ,
          Submission.BoseGases.kinFT W (kmomInt ℓ n)
            * (starRingEnd ℂ) (Submission.BoseGases.kinFT g (kmomInt ℓ n))
            * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) y : ℂ)))) := by
  have hne : ((ℓ : ℂ) ^ 3) ≠ 0 := pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (ne_of_gt hℓ))
  -- the periodisation of `W`, expanded on the sampling lattice
  have hPz : ∀ z : E3, (∑' m : Fin 3 → ℤ, W (z - y + ℓ • latVec m))
      = ((ℓ : ℂ) ^ 3)⁻¹ * (∑' n : Fin 3 → ℤ, Submission.BoseGases.kinFT W (kmomInt ℓ n)
          * Complex.exp (Complex.I * (inner ℝ (kmomInt ℓ n) (z - y) : ℂ))) := by
    intro z
    have h := latticePoisson_kernel ℓ hℓ W hW hWs (z - y)
    rw [h, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
    rfl
  -- the phase split `e^{i⟪k, z-y⟫} = e^{-i⟪k,y⟫} e^{i⟪k,z⟫}`
  have hph : ∀ (z : E3) (n : Fin 3 → ℤ),
      Complex.exp (Complex.I * (inner ℝ (kmomInt ℓ n) (z - y) : ℂ))
        = Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) y : ℂ)))
          * Complex.exp (Complex.I * (inner ℝ (kmomInt ℓ n) z : ℂ)) := by
    intro z n
    rw [inner_sub_right]
    push_cast
    rw [show Complex.I * ((inner ℝ (kmomInt ℓ n) z : ℂ) - (inner ℝ (kmomInt ℓ n) y : ℂ))
        = (Complex.I * (inner ℝ (kmomInt ℓ n) z : ℂ))
            + (-(Complex.I * (inner ℝ (kmomInt ℓ n) y : ℂ))) by ring, Complex.exp_add]
    ring
  -- the coefficient family and its absolute summability
  set c : (Fin 3 → ℤ) → ℂ := fun n => Submission.BoseGases.kinFT W (kmomInt ℓ n)
      * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) y : ℂ))) with hcdef
  have hsumKin : Summable (fun n : Fin 3 → ℤ => ‖Submission.BoseGases.kinFT W (kmomInt ℓ n)‖) := by
    have h := summable_kinFT_lattice_phase (ℓ := ℓ) hℓ hW hWs (0 : E3)
    simpa using h.norm
  have hc : Summable (fun n : Fin 3 → ℤ => ‖c n‖) := by
    refine hsumKin.congr (fun n => ?_)
    show ‖Submission.BoseGases.kinFT W (kmomInt ℓ n)‖
      = ‖Submission.BoseGases.kinFT W (kmomInt ℓ n)
          * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) y : ℂ)))‖
    rw [norm_mul, norm_exp_neg_I_ofReal, mul_one]
  -- the inner sum in the form consumed by the term-by-term integration
  have hsumrw : ∀ z : E3, (∑' n : Fin 3 → ℤ, Submission.BoseGases.kinFT W (kmomInt ℓ n)
        * Complex.exp (Complex.I * (inner ℝ (kmomInt ℓ n) (z - y) : ℂ)))
      = ∑' n : Fin 3 → ℤ, c n * Complex.exp (Complex.I * (inner ℝ (kmomInt ℓ n) z : ℂ)) := by
    intro z
    refine tsum_congr (fun n => ?_)
    rw [hph z n, hcdef]
    ring
  have h1 : (∫ z, g z * (∑' m : Fin 3 → ℤ, W (z - y + ℓ • latVec m)))
      = ((ℓ : ℂ) ^ 3)⁻¹ * (∫ z, g z * (∑' n : Fin 3 → ℤ, c n
          * Complex.exp (Complex.I * (inner ℝ (kmomInt ℓ n) z : ℂ)))) := by
    have hpt : ∀ z : E3, g z * (∑' m : Fin 3 → ℤ, W (z - y + ℓ • latVec m))
        = ((ℓ : ℂ) ^ 3)⁻¹ * (g z * (∑' n : Fin 3 → ℤ, c n
            * Complex.exp (Complex.I * (inner ℝ (kmomInt ℓ n) z : ℂ)))) := by
      intro z
      rw [hPz z, hsumrw z]
      ring
    rw [integral_congr_ae (Eventually.of_forall hpt), integral_const_mul]
  rw [h1, sampling_integral_pos hc hg]
  congr 1
  refine tsum_congr (fun n => ?_)
  rw [kinFT_neg_eq_conj hgstar hg (kmomInt ℓ n), hcdef]
  ring

/-! ## The target -/

theorem frame_sampling_L2 {ℓ : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (hWs : HasCompactSupport W)
    {u v : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hu : MeasureTheory.Integrable u) (hv : MeasureTheory.Integrable v) :
    (ℓ ^ 3)⁻¹ * (∑' n : Fin 3 → ℤ,
        Submission.BoseGases.kinFT (fun z => (W z : ℂ)) (Work.BoseBoxFock.kmomInt ℓ n)
          * Submission.BoseGases.kinFT
              (fun z => (((Submission.BoseGases.chiScale ℓ z) * (u z) : ℝ) : ℂ))
              (Work.BoseBoxFock.kmomInt ℓ n)
          * (starRingEnd ℂ) (Submission.BoseGases.kinFT
              (fun z => (((Submission.BoseGases.chiScale ℓ z) * (v z) : ℝ) : ℂ))
              (Work.BoseBoxFock.kmomInt ℓ n)))
      = MeasureTheory.integral MeasureTheory.volume (fun y : EuclideanSpace ℝ (Fin 3) =>
          MeasureTheory.integral MeasureTheory.volume (fun z : EuclideanSpace ℝ (Fin 3) =>
            (((Submission.BoseGases.chiScale ℓ y) * (u y) : ℝ) : ℂ)
              * (((Submission.BoseGases.chiScale ℓ z) * (v z) : ℝ) : ℂ)
              * (∑' m : Fin 3 → ℤ,
                  (W (z - y + ℓ • WithLp.toLp 2 (fun i : Fin 3 => (m i : ℝ))) : ℂ)))) := by
  classical
  let Wc : E3 → ℂ := fun z => (W z : ℂ)
  let Φ : E3 → ℂ := fun y => (((Submission.BoseGases.chiScale ℓ y) * (u y) : ℝ) : ℂ)
  let Ψ : E3 → ℂ := fun z => (((Submission.BoseGases.chiScale ℓ z) * (v z) : ℝ) : ℂ)
  let A : (Fin 3 → ℤ) → ℂ := fun n => Submission.BoseGases.kinFT Wc (kmomInt ℓ n)
  let B : (Fin 3 → ℤ) → ℂ := fun n => Submission.BoseGases.kinFT Ψ (kmomInt ℓ n)
  let C : (Fin 3 → ℤ) → ℂ := fun n => Submission.BoseGases.kinFT Φ (kmomInt ℓ n)
  let T : E3 → ℂ := fun y => ∑' n : Fin 3 → ℤ, A n * (starRingEnd ℂ) (B n)
      * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) y : ℂ)))
  have hχcont : Continuous (fun z : E3 => Submission.BoseGases.chiScale ℓ z) :=
    Submission.BoseGases.chiScale_continuous ℓ
  have hχbdd : ∀ z : E3,
      ‖Submission.BoseGases.chiScale ℓ z‖ ≤ (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ := by
    intro z
    rw [Real.norm_eq_abs]
    exact Submission.BoseGases.abs_chiScale_le ℓ z
  have hΨ : Integrable Ψ := by
    show Integrable (fun z => ((Submission.BoseGases.chiScale ℓ z * v z : ℝ) : ℂ))
    exact (hv.bdd_mul hχcont.aestronglyMeasurable (Eventually.of_forall hχbdd)).ofReal
  have hΦ : Integrable Φ := by
    show Integrable (fun y => ((Submission.BoseGases.chiScale ℓ y * u y : ℝ) : ℂ))
    exact (hu.bdd_mul hχcont.aestronglyMeasurable (Eventually.of_forall hχbdd)).ofReal
  have hΨstar : ∀ x, (starRingEnd ℂ) (Ψ x) = Ψ x := by
    intro x
    show (starRingEnd ℂ) ((↑(Submission.BoseGases.chiScale ℓ x * v x) : ℝ) : ℂ)
      = ((↑(Submission.BoseGases.chiScale ℓ x * v x) : ℝ) : ℂ)
    exact Complex.conj_ofReal _
  have hWc : ContDiff ℝ (⊤ : ℕ∞) Wc := by
    show ContDiff ℝ (⊤ : ℕ∞) (fun z : E3 => (W z : ℂ))
    exact Complex.ofRealCLM.contDiff.comp hW
  have hWcs : HasCompactSupport Wc := by
    show HasCompactSupport (fun z : E3 => (W z : ℂ))
    exact hWs.comp_left (g := fun r : ℝ => (r : ℂ)) (by norm_num)
  have hsumA : Summable (fun n : Fin 3 → ℤ => ‖A n‖) := by
    show Summable (fun n : Fin 3 → ℤ => ‖Submission.BoseGases.kinFT Wc (kmomInt ℓ n)‖)
    have h := summable_kinFT_lattice_phase (ℓ := ℓ) hℓ hWc hWcs (0 : E3)
    simpa using h.norm
  have hBA : Summable (fun n : Fin 3 → ℤ => ‖A n * (starRingEnd ℂ) (B n)‖) := by
    have hb0 : ∀ n : Fin 3 → ℤ, ‖(starRingEnd ℂ) (B n)‖ ≤ ∫ z, ‖Ψ z‖ := by
      intro n
      rw [starRingEnd_apply, norm_star]
      show ‖Submission.BoseGases.kinFT Ψ (kmomInt ℓ n)‖ ≤ ∫ z, ‖Ψ z‖
      exact norm_kinFT_le Ψ (kmomInt ℓ n)
    have h : Summable (fun n : Fin 3 → ℤ => A n * (starRingEnd ℂ) (B n)) := by
      refine Summable.of_norm_bounded (g := fun n : Fin 3 → ℤ => ‖A n‖ * (∫ z, ‖Ψ z‖)) ?_ ?_
      · exact hsumA.mul_right _
      · intro n
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hb0 n) (norm_nonneg (A n))
    exact h.norm
  -- the inner identity, for each `y`
  have hkey : ∀ y : E3, (∫ z, Ψ z * (∑' m : Fin 3 → ℤ, Wc (z - y + ℓ • latVec m)))
      = ((ℓ : ℂ) ^ 3)⁻¹ * (∑' n : Fin 3 → ℤ, A n * (starRingEnd ℂ) (B n)
          * Complex.exp (-(Complex.I * (inner ℝ (kmomInt ℓ n) y : ℂ)))) := by
    intro y
    exact frame_sampling_L2_inner hℓ hWc hWcs hΨ hΨstar y
  have hX : (∫ y, ∫ z, Φ y * Ψ z * (∑' m : Fin 3 → ℤ, Wc (z - y + ℓ • latVec m)))
      = ((ℓ : ℂ) ^ 3)⁻¹ * (∑' n : Fin 3 → ℤ, A n * (starRingEnd ℂ) (B n) * C n) := by
    have h2 : ∀ y : E3, (∫ z, Φ y * Ψ z * (∑' m : Fin 3 → ℤ, Wc (z - y + ℓ • latVec m)))
        = Φ y * (∫ z, Ψ z * (∑' m : Fin 3 → ℤ, Wc (z - y + ℓ • latVec m))) := by
      intro y
      rw [← integral_const_mul]
      exact integral_congr_ae (Eventually.of_forall (fun z => by ring))
    have hpt : ∀ y : E3, (∫ z, Φ y * Ψ z * (∑' m : Fin 3 → ℤ, Wc (z - y + ℓ • latVec m)))
        = Φ y * (((ℓ : ℂ) ^ 3)⁻¹ * T y) := by
      intro y
      rw [h2 y, hkey y]
    have h1 : (∫ y, ∫ z, Φ y * Ψ z * (∑' m : Fin 3 → ℤ, Wc (z - y + ℓ • latVec m)))
        = ∫ y, Φ y * (((ℓ : ℂ) ^ 3)⁻¹ * T y) :=
      integral_congr_ae (Eventually.of_forall hpt)
    have hpt2 : ∀ y : E3, Φ y * (((ℓ : ℂ) ^ 3)⁻¹ * T y) = ((ℓ : ℂ) ^ 3)⁻¹ * (Φ y * T y) :=
      fun y => by ring
    have h3 : (∫ y, Φ y * (((ℓ : ℂ) ^ 3)⁻¹ * T y))
        = ((ℓ : ℂ) ^ 3)⁻¹ * (∑' n : Fin 3 → ℤ, A n * (starRingEnd ℂ) (B n) * C n) := by
      rw [integral_congr_ae (Eventually.of_forall hpt2), integral_const_mul]
      congr 1
      exact sampling_integral (ℓ := ℓ) hBA hΦ
    exact h1.trans h3
  have hY : (ℓ ^ 3)⁻¹ * (∑' n : Fin 3 → ℤ, A n * C n * (starRingEnd ℂ) (B n))
      = ((ℓ : ℂ) ^ 3)⁻¹ * (∑' n : Fin 3 → ℤ, A n * (starRingEnd ℂ) (B n) * C n) := by
    have hc : (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) = ((ℓ : ℂ) ^ 3)⁻¹ := by
      rw [Complex.ofReal_inv, Complex.ofReal_pow]
    rw [hc]
    congr 1
    exact tsum_congr (fun n => by ring)
  show (ℓ ^ 3)⁻¹ * (∑' n : Fin 3 → ℤ, A n * C n * (starRingEnd ℂ) (B n))
      = ∫ y, ∫ z, Φ y * Ψ z * (∑' m : Fin 3 → ℤ, Wc (z - y + ℓ • latVec m))
  rw [hY, hX]

end Work.BoseBoxFock
