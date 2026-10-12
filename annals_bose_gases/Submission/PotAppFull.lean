import ChallengeDeps
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Submission.OneBodyBound
import Submission.PotAppM2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Layer 5, S5d - the FS potential lower bound `lm:potapp eq:Q4aprioribound`

Proof of `Submission.BoseGases.potapp_q4`: for `0 ≤ μ` and continuous `Φ` over
`abox N ℓ`,

    qLHSword ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ
      ≥ − potappC·(N²ℓ⁻³ + μ²ℓ³)·(a v)·∫Φ² + ½·q4word ℓ (wPairC ℓ v) (omC w0) Φ

Strategy (a corpus-native transcription of FS `lm:potapp`):

1.  Split `qLHSword = −μ·musum + pairpart` (`qLHSword_split`), where the pair
    part is `½Σ_p∫Φ²·w(x_{p.1},x_{p.2})`.
2.  Per pair `p = (i,j)` use the exact square-completion identity
    (`potapp_pair_sq_ge` / `potapp_pair_sq_ge'`), i.e. with
    `M = Φ − QᵢQⱼΦ`, `E = q4B Φ` and `O(x,y) = w₀(x−y)`:

        2Φ² − E² ≥ −2(1−O)²·M²,

    so the weighted per-pair integrand
    `½Φ²w − ¼E²w + ½(1−O)²M²w` is pointwise `≥ 0`
    (`potapp_core_nonneg`: pairpart − ¼Σ∫E²w + ½·M²sum ≥ 0), i.e.
    `pairpart ≥ ½·q4word − ½·M²sum`.
3.  Bound the two losses by fibre-type estimates, all linear in `‖Φ‖²`:
    * `−μ·musum ≥ −μ·(chiSup²·2·8π·a v)·N̂·‖Φ‖²` (`potapp_musum_abs_le`
      and `|∫_y w₁(xᵢ,y)| ≤ chiSup²·2·8π·a v`);
    * `M²sum ≤ 100·(chiSup²·2·8π·a v)·(ℓ³)⁻¹·N̂²·‖Φ‖²`
      (`Submission.PotAppM2.potapp_M2sq_le`, whose per-pair integrability is
      `potapp_M2pair_integrable` and whose kernel-fibre control is the
      single-slot peel `Submission.PotAppPeel.peel_sq_kernel_le`).
4.  Convert `μN̂ ≤ ½(μ²ℓ³+N̂²ℓ⁻³)` (AM–GM), `ℓ⁻³N̂² ≤ X`, and finish with
    the explicit constant `potappC = 1000·chiSup²·8π`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The constant of the FS `lm:potapp` bound. -/
noncomputable def potappC : ℝ := 1000 * chiSup ^ 2 * (8 * π)

set_option maxHeartbeats 4000000

lemma potapp_pair_sq_ge {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {w0 : ℝ³ → ℝ} {Φ : XN N → ℝ} (hΦc : Continuous Φ) (x : XN N) :
    2 * (Φ x) ^ 2 - (q4B ℓ (omC w0) Φ (i, j) x) ^ 2 ≥
      - 2 * (1 - omC w0 (x i) (x j)) ^ 2 * (Φ x - aQ ℓ i (aQ ℓ j Φ) x) ^ 2 := by
  let A : ℝ := aP ℓ i (aP ℓ j Φ) x
  let B : ℝ := aP ℓ i (aQ ℓ j Φ) x
  let C : ℝ := aQ ℓ i (aP ℓ j Φ) x
  let D : ℝ := aQ ℓ i (aQ ℓ j Φ) x
  let O : ℝ := omC w0 (x i) (x j)
  let M : ℝ := A + B + C
  have hpat : A + B + C + D = Φ x := by
    simpa [A, B, C, D] using pattern_sum hℓ hij hΦc x
  have hM : M = Φ x - D := by
    dsimp [M]
    nlinarith
  have hPhi : Φ x = M + D := by
    dsimp [M]
    nlinarith
  have h1 : aQ ℓ j (aQ ℓ i Φ) x = D := by
    simpa [D] using (aQ_comm hℓ hij hΦc x).symm
  have hA' : aP ℓ j (aP ℓ i Φ) x = A := by
    simpa [A] using (aP_comm hℓ i j hΦc x).symm
  have hB' : aP ℓ j (aQ ℓ i Φ) x = C := by
    simpa [C] using aP_aQ_comm hℓ hij.symm hΦc x
  have hC' : aQ ℓ j (aP ℓ i Φ) x = B := by
    simpa [B] using (aP_aQ_comm hℓ hij hΦc x).symm
  have hE : q4B ℓ (omC w0) Φ (i, j) x = D + O * M := by
    unfold q4B
    rw [h1, hA', hB', hC']
    dsimp [O, M]
    ring
  have hEq : 2 * (Φ x) ^ 2 - (q4B ℓ (omC w0) Φ (i, j) x) ^ 2 =
      (Φ x + (1 - O) * M) ^ 2 - 2 * (1 - O) ^ 2 * M ^ 2 := by
    rw [hE, hPhi]
    ring
  calc
    2 * (Φ x) ^ 2 - (q4B ℓ (omC w0) Φ (i, j) x) ^ 2
        = (Φ x + (1 - O) * M) ^ 2 - 2 * (1 - O) ^ 2 * M ^ 2 := hEq
    _ ≥ - 2 * (1 - O) ^ 2 * M ^ 2 := by
        have hsq : 0 ≤ (Φ x + (1 - O) * M) ^ 2 := sq_nonneg _
        nlinarith
    _ = - 2 * (1 - O) ^ 2 * (Φ x - D) ^ 2 := by
        rw [← hM]

/-- `qLHSword` splits into its chemical-potential part and its pair part. -/
lemma qLHSword_split {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (μ : ℝ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ =
      (- μ) * (∑ i : Fin N, muPhi ℓ (wPairC ℓ (g0 v h)) Φ i)
      + (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (Φ x) ^ 2 * wPairC ℓ v (x p.1) (x p.2)) := by
  let w : ℝ³ → ℝ³ → ℝ := wPairC ℓ v
  let w1 : ℝ³ → ℝ³ → ℝ := wPairC ℓ (g0 v h)
  let F : ℝ³ → ℝ := fun z => ∫ y in acube ℓ, wPair ℓ (g0 v h) z y
  let C0 : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  have hCb : ∀ z ∈ acube ℓ, |F z| ≤ C0 := by
    intro z hz
    have hb := w1c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
    simpa [F, C0, wPairC] using hb
  have hFaem : AEStronglyMeasurable F (volume.restrict (acube ℓ)) := by
    exact fibre_acube_aem (h := g0 v h) (g0_integrable hR hv_supp h)
  have hSΦc : Continuous (fun x : XN N => (Φ x) ^ 2) := by fun_prop
  have hfi (i : Fin N) :
      IntegrableOn (fun x : XN N => (Φ x) ^ 2 * w1Fibre ℓ (wPairC ℓ (g0 v h)) (x i))
        (abox N ℓ) volume := by
    have hif : IntegrableOn (fun x : XN N => (Φ x) ^ 2 * F (x i)) (abox N ℓ) volume :=
      integrableOn_slot_fibre hℓ i hFaem hCb hSΦc
    simpa [F, w1Fibre, wPairC] using hif
  have hWi : ∀ p ∈ pairSet N,
      IntegrableOn (fun x : XN N => (Φ x) ^ 2 * w (x p.1) (x p.2)) (abox N ℓ) volume := by
    intro p hp
    have hpne : p.1 ≠ p.2 := by simpa [pairSet] using hp
    have hif : IntegrableOn (fun x : XN N => (Φ x) ^ 2 * wPair ℓ v (x p.1) (x p.2))
        (abox N ℓ) volume :=
      integrableOn_slot_wPair (h := v) hℓ (v_integrable hv_memL1)
        (fun z hz => v_eq_zero_of_norm_ge hv_supp hz) hRℓ hpne hSΦc
    simpa [w, wPairC] using hif
  have hmu : (∫ x in abox N ℓ, (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))) =
      - μ * (∑ i : Fin N, muPhi ℓ w1 Φ i) := by
    calc
      (∫ x in abox N ℓ, (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))))
          = (∫ x in abox N ℓ, (- μ) * ((Φ x) ^ 2 * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))) := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = - μ * (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ i : Fin N, w1Fibre ℓ w1 (x i))) := by
            rw [← integral_const_mul (- μ) (fun x : XN N => (Φ x) ^ 2 * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))]
      _ = - μ * (∑ i : Fin N, (∫ x in abox N ℓ, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i))) := by
            congr 1
            calc
              (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))
                  = ∫ x in abox N ℓ, (∑ i : Fin N, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i)) := by
                    apply integral_congr_ae
                    filter_upwards with x
                    rw [Finset.mul_sum]
              _ = ∑ i : Fin N, (∫ x in abox N ℓ, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i)) := by
                    exact integral_finsetSum (Finset.univ : Finset (Fin N)) (fun i hi => by simpa [IntegrableOn] using hfi i)
      _ = - μ * (∑ i : Fin N, muPhi ℓ w1 Φ i) := by
            simp [muPhi]
  have hpair : (∫ x in abox N ℓ, (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))) =
      (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
    calc
      (∫ x in abox N ℓ, (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2))))
          = (∫ x in abox N ℓ, (1 / 2) * ((Φ x) ^ 2 * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))) := by
            apply integral_congr_ae
            filter_upwards with x
            ring
      _ = (1 / 2) * (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ p ∈ pairSet N, w (x p.1) (x p.2))) := by
            rw [← integral_const_mul (1 / 2 : ℝ) (fun x : XN N => (Φ x) ^ 2 * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))]
      _ = (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
            congr 1
            calc
              (∫ x in abox N ℓ, (Φ x) ^ 2 * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))
                  = ∫ x in abox N ℓ, (∑ p ∈ pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
                    apply integral_congr_ae
                    filter_upwards with x
                    rw [Finset.mul_sum]
              _ = ∑ p ∈ pairSet N, (∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
                    exact integral_finsetSum (pairSet N) (fun p hp => by simpa [IntegrableOn] using hWi p hp)
  have hint1 : IntegrableOn (fun x : XN N =>
      (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))) (abox N ℓ) volume := by
    have hfs : IntegrableOn (fun x : XN N => (∑ i : Fin N, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i)))
        (abox N ℓ) volume := by
      change Integrable (fun x : XN N => ∑ i : Fin N, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i))
          (volume.restrict (abox N ℓ))
      simpa using (integrable_finsetSum (Finset.univ : Finset (Fin N))
        (f := fun (i : Fin N) (x : XN N) => (Φ x) ^ 2 * w1Fibre ℓ w1 (x i))
        (fun i hi => by simpa [IntegrableOn] using hfi i))
    have hpt : (fun x : XN N => (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))) =ᵐ[volume.restrict (abox N ℓ)]
        fun x : XN N => (- μ) * (∑ i : Fin N, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i)) := by
      apply ae_of_all
      intro x
      calc
        (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))
            = (- μ) * ((Φ x) ^ 2 * (∑ i : Fin N, w1Fibre ℓ w1 (x i))) := by ring
        _ = (- μ) * (∑ i : Fin N, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i)) := by
              rw [Finset.mul_sum]
    have hfsm : Integrable (fun x : XN N => (- μ) * (∑ i : Fin N, (Φ x) ^ 2 * w1Fibre ℓ w1 (x i)))
        (volume.restrict (abox N ℓ)) := by
      simpa [IntegrableOn] using hfs.const_mul (-μ)
    change Integrable (fun x : XN N =>
        (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i)))) (volume.restrict (abox N ℓ))
    exact hfsm.congr hpt.symm
  have hint2 : IntegrableOn (fun x : XN N =>
      (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))) (abox N ℓ) volume := by
    have hfs : IntegrableOn (fun x : XN N => (∑ p ∈ pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2)))
        (abox N ℓ) volume := by
      change Integrable (fun x : XN N => ∑ p ∈ pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2))
          (volume.restrict (abox N ℓ))
      simpa using (integrable_finsetSum (pairSet N)
        (f := fun (p : Fin N × Fin N) (x : XN N) => (Φ x) ^ 2 * w (x p.1) (x p.2))
        (fun p hp => by simpa [IntegrableOn] using hWi p hp))
    have hpt : (fun x : XN N => (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))) =ᵐ[volume.restrict (abox N ℓ)]
        fun x : XN N => (1 / 2) * (∑ p ∈ pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
      apply ae_of_all
      intro x
      calc
        (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))
            = (1 / 2) * ((Φ x) ^ 2 * (∑ p ∈ pairSet N, w (x p.1) (x p.2))) := by ring
        _ = (1 / 2) * (∑ p ∈ pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
              rw [Finset.mul_sum]
    have hfsm : Integrable (fun x : XN N => (1 / 2) * (∑ p ∈ pairSet N, (Φ x) ^ 2 * w (x p.1) (x p.2)))
        (volume.restrict (abox N ℓ)) := by
      simpa [IntegrableOn] using hfs.const_mul (1 / 2)
    change Integrable (fun x : XN N =>
        (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))) (volume.restrict (abox N ℓ))
    exact hfsm.congr hpt.symm
  calc
    qLHSword (N := N) ℓ μ w w1 Φ = ∫ x in abox N ℓ, (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))
        + (1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2))) := by
          rfl
    _ = (∫ x in abox N ℓ, (Φ x) ^ 2 * (- μ * (∑ i : Fin N, w1Fibre ℓ w1 (x i))))
        + (∫ x in abox N ℓ, (Φ x) ^ 2 * ((1 / 2) * (∑ p ∈ pairSet N, w (x p.1) (x p.2)))) := by
            rw [← integral_add hint1 hint2]
            apply integral_congr_ae
            filter_upwards with x
            ring
    _ = - μ * (∑ i : Fin N, muPhi ℓ w1 Φ i)
        + (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * w (x p.1) (x p.2)) := by
          rw [hmu, hpair]




/-- Absolute bound for the chemical-potential sum `Σ_i muPhi`. -/
lemma potapp_musum_abs_le {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    |∑ i : Fin N, muPhi ℓ (wPairC ℓ (g0 v h)) Φ i|
      ≤ chiSup ^ 2 * 2 * (8 * π * a v) * (N : ℝ) *
          (∫ x in abox N ℓ, (Φ x) ^ 2) := by
  let C0 : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  let F : ℝ³ → ℝ := fun z => ∫ y in acube ℓ, wPair ℓ (g0 v h) z y
  have hFb : ∀ z : ℝ³, |F z| ≤ C0 := by
    intro z
    have hb := w1c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ z
    simpa [F, C0] using hb
  have hFaem : AEStronglyMeasurable F (volume.restrict (acube ℓ)) := by
    exact fibre_acube_aem (h := g0 v h) (g0_integrable hR hv_supp h)
  have hSΦc : Continuous (fun x : XN N => (Φ x) ^ 2) := by fun_prop
  have hCb : ∀ z ∈ acube ℓ, |F z| ≤ C0 := fun z hz => hFb z
  let μ : Measure (XN N) := volume.restrict (abox N ℓ)
  have hfi (i : Fin N) : IntegrableOn (fun x : XN N => (Φ x) ^ 2 * F (x i)) (abox N ℓ) volume :=
    integrableOn_slot_fibre hℓ i hFaem hCb hSΦc
  have hI : 0 ≤ (∫ x in abox N ℓ, (Φ x) ^ 2) :=
    integral_nonneg (fun x : XN N => sq_nonneg (Φ x))
  have hC0nn : 0 ≤ C0 := by
    have hav0 : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
    dsimp [C0]
    positivity
  have hper (i : Fin N) :
      |muPhi ℓ (wPairC ℓ (g0 v h)) Φ i| ≤ C0 * (∫ x in abox N ℓ, (Φ x) ^ 2) := by
    have hEq : muPhi ℓ (wPairC ℓ (g0 v h)) Φ i = ∫ x in abox N ℓ, (Φ x) ^ 2 * F (x i) := by
      dsimp [muPhi, F, w1Fibre]
      apply integral_congr_ae
      filter_upwards with x
      congr 1
    rw [hEq]
    calc
      |∫ x in abox N ℓ, (Φ x) ^ 2 * F (x i)|
          ≤ ∫ x in abox N ℓ, |(Φ x) ^ 2 * F (x i)| := by
              change |∫ x : XN N, (Φ x) ^ 2 * F (x i) ∂μ| ≤
                ∫ x : XN N, |(Φ x) ^ 2 * F (x i)| ∂μ
              exact abs_integral_le_integral_abs (μ := μ) (f := fun x : XN N => (Φ x) ^ 2 * F (x i))
      _ ≤ ∫ x in abox N ℓ, (Φ x) ^ 2 * C0 := by
              refine integral_mono_of_nonneg (μ := μ)
                (f := fun x : XN N => |(Φ x) ^ 2 * F (x i)|)
                (g := fun x : XN N => (Φ x) ^ 2 * C0) ?_ ?_ ?_
              · filter_upwards with x
                exact abs_nonneg _
              · have hcont : Continuous (fun x : XN N => (Φ x) ^ 2 * C0) := by fun_prop
                change Integrable (fun x : XN N => (Φ x) ^ 2 * C0) μ
                simpa [μ, IntegrableOn] using (integrableOn_abox_of_continuous hℓ hcont)
              · filter_upwards with x
                have hb : |F (x i)| ≤ C0 := hFb (x i)
                calc
                  |(Φ x) ^ 2 * F (x i)| = (Φ x) ^ 2 * |F (x i)| := by
                    rw [abs_mul, abs_of_nonneg (sq_nonneg (Φ x))]
                  _ ≤ (Φ x) ^ 2 * C0 := mul_le_mul_of_nonneg_left hb (sq_nonneg (Φ x))
      _ = C0 * (∫ x in abox N ℓ, (Φ x) ^ 2) := by
              have hEqc : (fun x : XN N => (Φ x) ^ 2 * C0) = fun x : XN N => C0 * (Φ x) ^ 2 := by
                funext x
                ring
              rw [hEqc, integral_const_mul]
  calc
    |∑ i : Fin N, muPhi ℓ (wPairC ℓ (g0 v h)) Φ i|
        ≤ ∑ i : Fin N, |muPhi ℓ (wPairC ℓ (g0 v h)) Φ i| := by
            simpa using (Finset.abs_sum_le_sum_abs (s := Finset.univ)
              (f := fun i : Fin N => muPhi ℓ (wPairC ℓ (g0 v h)) Φ i))
    _ ≤ ∑ i : Fin N, C0 * (∫ x in abox N ℓ, (Φ x) ^ 2) := by
            exact Finset.sum_le_sum (fun i hi => hper i)
    _ = C0 * (N : ℝ) * (∫ x in abox N ℓ, (Φ x) ^ 2) := by
            rw [Finset.sum_const]
            simp [nsmul_eq_mul]
            ring
    _ = chiSup ^ 2 * 2 * (8 * π * a v) * (N : ℝ) * (∫ x in abox N ℓ, (Φ x) ^ 2) := by
            rfl

/-- A.e. `|1 − w₀(xᵢ−xⱼ)| ≤ 2` on the box (from `0 ≤ w₀ ≤ 1` a.e.). -/
lemma potapp_ae_omega_le2 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ} {R : ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    {i j : Fin N} (hij : i ≠ j) :
    ∀ᵐ x ∂(volume.restrict (abox N ℓ)), |1 - Classical.choose h (x i - x j)| ≤ 2 := by
  have hspec := w0_spec h
  have hb := scattering_bounds_ae hR hv_nonneg hvrad hv_supp hspec.1 hspec.2
  have hb2 : ∀ᵐ z : ℝ³, |1 - Classical.choose h z| ≤ 2 := by
    filter_upwards [hb.1, hb.2] with z hz0 hz1
    have hnon : 0 ≤ 1 - Classical.choose h z := by linarith
    rw [abs_of_nonneg hnon]
    linarith
  exact ae_pair_pullback hℓ hij hb2

/-- Per-pair integrability of the `M²`-integrand of `potapp_q4`. -/
lemma potapp_M2pair_integrable {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ)
    {i j : Fin N} (hij : i ≠ j) :
    IntegrableOn (fun x : XN N =>
      (1 - Classical.choose h (x i - x j)) ^ 2 *
      (aP ℓ i (aP ℓ j Φ) x + aP ℓ i (aQ ℓ j Φ) x + aQ ℓ i (aP ℓ j Φ) x) ^ 2 *
      wPairC ℓ v (x i) (x j)) (abox N ℓ) volume := by
  let w0 : ℝ³ → ℝ := Classical.choose h
  let M : XN N → ℝ := fun x =>
    aP ℓ i (aP ℓ j Φ) x + aP ℓ i (aQ ℓ j Φ) x + aQ ℓ i (aP ℓ j Φ) x
  let F : XN N → ℝ := fun x =>
    (1 - w0 (x i - x j)) ^ 2 * (M x) ^ 2 * wPairC ℓ v (x i) (x j)
  let μ : Measure (XN N) := volume.restrict (abox N ℓ)
  have hMcont : Continuous M := by
    have h1 : Continuous (aP ℓ i (aP ℓ j Φ)) := aP_continuous hℓ i (aP_continuous hℓ j hΦc)
    have h2 : Continuous (aP ℓ i (aQ ℓ j Φ)) := aP_continuous hℓ i (aQ_continuous hℓ j hΦc)
    have h3 : Continuous (aQ ℓ i (aP ℓ j Φ)) := aQ_continuous hℓ i (aP_continuous hℓ j hΦc)
    dsimp [M]
    fun_prop
  obtain ⟨B, hB⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn (s := abox N ℓ) (f := M) hMcont.continuousOn
  have hB0 : 0 ≤ B := by
    have hb := hB (0 : XN N) (zero_mem_abox hℓ.le)
    exact le_trans (norm_nonneg (M (0 : XN N))) hb
  let D : ℝ := 2 * B ^ 2
  have hrewpt : ∀ x : XN N, F x = (1 - w0 (x i - x j)) * wPair ℓ (g0 v h) (x i) (x j) * (M x) ^ 2 := by
    intro x
    dsimp [F, M]
    simp only [wPairC]
    rw [w1_eq_w_mul_one_sub h ℓ (x i) (x j)]
    ring
  have hwaem0 : AEStronglyMeasurable (fun x : XN N => w0 (x i - x j)) μ :=
    w0_diff_aem hℓ hij (IsScatteringSolution.lhs_integrable (w0_spec h).2)
  have h1aem : AEStronglyMeasurable (fun x : XN N => (1 - w0 (x i - x j)) ^ 2) μ := by
    have hc : AEStronglyMeasurable (fun x : XN N => (1 : ℝ) - w0 (x i - x j)) μ :=
      (aestronglyMeasurable_const : AEStronglyMeasurable (fun _ : XN N => (1 : ℝ)) μ).sub hwaem0
    exact hc.pow 2
  have hMaem : AEStronglyMeasurable (fun x : XN N => (M x) ^ 2) μ :=
    hMcont.aestronglyMeasurable.pow 2
  have hvaem : AEStronglyMeasurable (fun x : XN N => wPair ℓ v (x i) (x j)) μ :=
    aesm_wPair_pair hℓ (v_integrable hv_memL1) i j hij
  have haesmF : AEStronglyMeasurable F μ := by
    have hprod : AEStronglyMeasurable (fun x : XN N =>
        (1 - w0 (x i - x j)) ^ 2 * wPair ℓ v (x i) (x j) * (M x) ^ 2) μ :=
      (h1aem.mul hvaem).mul hMaem
    refine AEStronglyMeasurable.congr hprod ?_
    apply ae_of_all
    intro x
    dsimp [F]
    simp only [wPairC]
    ring
  have hw1i : IntegrableOn (fun x : XN N => |wPair ℓ (g0 v h) (x i) (x j)|) (abox N ℓ) volume :=
    integrableOn_wPair_abs_sub_abox hℓ (g0_integrable hR hv_supp h)
      (fun z hz => g0_zero_of_norm_ge hv_supp hz h) hRℓ i j hij
  have hg : Integrable (fun x : XN N => D * |wPair ℓ (g0 v h) (x i) (x j)|) μ := by
    have hc : Integrable (fun x : XN N => |wPair ℓ (g0 v h) (x i) (x j)|) μ := by
      simpa [μ, IntegrableOn] using hw1i
    exact hc.const_mul D
  have hle1 : ∀ᵐ x ∂μ, |1 - w0 (x i - x j)| ≤ 2 := by
    simpa [w0] using (potapp_ae_omega_le2 hℓ hR hv_nonneg hvrad hv_supp h hij)
  have hle2 : ∀ᵐ x ∂μ, |M x| ≤ B := by
    rw [ae_restrict_iff' (abox_measurable N ℓ)]
    apply ae_of_all
    intro x hx
    simpa [Real.norm_eq_abs] using hB x hx
  have hdom : ∀ᵐ x ∂μ, ‖F x‖ ≤ D * |wPair ℓ (g0 v h) (x i) (x j)| := by
    filter_upwards [hle1, hle2] with x hO hMx
    rw [Real.norm_eq_abs]
    calc
      |F x| = |(1 - w0 (x i - x j)) * wPair ℓ (g0 v h) (x i) (x j) * (M x) ^ 2| := by
            rw [hrewpt x]
      _ ≤ |1 - w0 (x i - x j)| * |wPair ℓ (g0 v h) (x i) (x j)| * |(M x) ^ 2| := by
            rw [abs_mul, abs_mul]
      _ = |1 - w0 (x i - x j)| * |wPair ℓ (g0 v h) (x i) (x j)| * |M x| ^ 2 := by
            rw [abs_pow]
      _ ≤ 2 * |wPair ℓ (g0 v h) (x i) (x j)| * B ^ 2 := by
            have hsq : |M x| ^ 2 ≤ B ^ 2 := by
              have hb : |(|M x|)| ≤ |B| := by
                simpa [abs_of_nonneg (abs_nonneg (M x)), abs_of_nonneg hB0] using hMx
              exact sq_le_sq.mpr hb
            have hstep1 : |1 - w0 (x i - x j)| * |wPair ℓ (g0 v h) (x i) (x j)| ≤
                2 * |wPair ℓ (g0 v h) (x i) (x j)| := by
              exact mul_le_mul_of_nonneg_right hO (abs_nonneg (wPair ℓ (g0 v h) (x i) (x j)))
            have hm1 : |1 - w0 (x i - x j)| * |wPair ℓ (g0 v h) (x i) (x j)| * |M x| ^ 2 ≤
                (2 * |wPair ℓ (g0 v h) (x i) (x j)|) * |M x| ^ 2 := by
              exact mul_le_mul_of_nonneg_right hstep1 (sq_nonneg |M x|)
            have hm2 : (2 * |wPair ℓ (g0 v h) (x i) (x j)|) * |M x| ^ 2 ≤
                (2 * |wPair ℓ (g0 v h) (x i) (x j)|) * B ^ 2 := by
              exact mul_le_mul_of_nonneg_left hsq
                (mul_nonneg (by norm_num) (abs_nonneg (wPair ℓ (g0 v h) (x i) (x j))))
            calc
              |1 - w0 (x i - x j)| * |wPair ℓ (g0 v h) (x i) (x j)| * |M x| ^ 2
                  ≤ (2 * |wPair ℓ (g0 v h) (x i) (x j)|) * |M x| ^ 2 := hm1
              _ ≤ (2 * |wPair ℓ (g0 v h) (x i) (x j)|) * B ^ 2 := hm2
              _ = 2 * |wPair ℓ (g0 v h) (x i) (x j)| * B ^ 2 := by ring
      _ = D * |wPair ℓ (g0 v h) (x i) (x j)| := by
            dsimp [D]
            ring
  change Integrable F μ
  exact Integrable.mono' hg haesmF hdom

/-- Per-pair integrand nonnegativity with `M = Φ − QᵢQⱼΦ` explicit. -/
lemma potapp_pair_sq_ge' {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {i j : Fin N} (hij : i ≠ j)
    {w0 : ℝ³ → ℝ} {Φ : XN N → ℝ} (hΦc : Continuous Φ) (x : XN N) :
    2 * (Φ x) ^ 2 - (q4B ℓ (omC w0) Φ (i, j) x) ^ 2
        + 2 * (1 - omC w0 (x i) (x j)) ^ 2 *
          (aP ℓ i (aP ℓ j Φ) x + aP ℓ i (aQ ℓ j Φ) x + aQ ℓ i (aP ℓ j Φ) x) ^ 2 ≥ 0 := by
  have hg := potapp_pair_sq_ge hℓ hij (w0 := w0) hΦc x
  have hM : aP ℓ i (aP ℓ j Φ) x + aP ℓ i (aQ ℓ j Φ) x + aQ ℓ i (aP ℓ j Φ) x =
      Φ x - aQ ℓ i (aQ ℓ j Φ) x := by
    have hpat := pattern_sum hℓ hij hΦc x
    nlinarith
  have hsq : (Φ x - aQ ℓ i (aQ ℓ j Φ) x) ^ 2 =
      (aP ℓ i (aP ℓ j Φ) x + aP ℓ i (aQ ℓ j Φ) x + aQ ℓ i (aP ℓ j Φ) x) ^ 2 := by
    rw [hM]
  nlinarith [hg, hsq]


/-- **core**: `pairpart − ¼·Σ∫E²w + ½·M²sum ≥ 0` (sum of pointwise squares). -/
lemma potapp_core_nonneg {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {v : ℝ³ → ℝ}
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))
      - (1 / 4) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (q4B ℓ (omC (Classical.choose h)) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))
      + (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (1 - Classical.choose h (x p.1 - x p.2)) ^ 2 *
          (aP ℓ p.1 (aP ℓ p.2 Φ) x + aP ℓ p.1 (aQ ℓ p.2 Φ) x + aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 *
          wPairC ℓ v (x p.1) (x p.2))
      ≥ 0 := by
  let w0 : ℝ³ → ℝ := Classical.choose h
  let μ : Measure (XN N) := volume.restrict (abox N ℓ)
  -- per-p: the combined integrand is pointwise ≥ 0
  have hpi : ∀ p ∈ pairSet N, ∀ x : XN N,
      0 ≤ (1 / 2) * (Φ x) ^ 2 * wPairC ℓ v (x p.1) (x p.2)
        - (1 / 4) * (q4B ℓ (omC w0) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2)
        + (1 / 2) * (1 - w0 (x p.1 - x p.2)) ^ 2 *
          (aP ℓ p.1 (aP ℓ p.2 Φ) x + aP ℓ p.1 (aQ ℓ p.2 Φ) x + aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 *
          wPairC ℓ v (x p.1) (x p.2) := by
    intro p hp x
    have hpne : p.1 ≠ p.2 := by simpa [pairSet] using hp
    have hw : 0 ≤ wPairC ℓ v (x p.1) (x p.2) := wPairC_nonneg hv_nonneg ℓ (x p.1) (x p.2)
    have hq4val : q4B ℓ (omC w0) Φ (p.1, p.2) x = q4B ℓ (omC w0) Φ p x := by rfl
    have hT : (1 / 2) * (Φ x) ^ 2 * wPairC ℓ v (x p.1) (x p.2)
        - (1 / 4) * (q4B ℓ (omC w0) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2)
        + (1 / 2) * (1 - w0 (x p.1 - x p.2)) ^ 2 *
          (aP ℓ p.1 (aP ℓ p.2 Φ) x + aP ℓ p.1 (aQ ℓ p.2 Φ) x + aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 *
          wPairC ℓ v (x p.1) (x p.2)
        = (1 / 4) * wPairC ℓ v (x p.1) (x p.2) *
          (2 * (Φ x) ^ 2 - (q4B ℓ (omC w0) Φ p x) ^ 2
            + 2 * (1 - w0 (x p.1 - x p.2)) ^ 2 *
              (aP ℓ p.1 (aP ℓ p.2 Φ) x + aP ℓ p.1 (aQ ℓ p.2 Φ) x + aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2) := by
      rw [← hq4val]
      ring
    have hg0 : 0 ≤ 2 * (Φ x) ^ 2 - (q4B ℓ (omC w0) Φ p x) ^ 2
        + 2 * (1 - w0 (x p.1 - x p.2)) ^ 2 *
          (aP ℓ p.1 (aP ℓ p.2 Φ) x + aP ℓ p.1 (aQ ℓ p.2 Φ) x + aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 := by
      have hg := potapp_pair_sq_ge' hℓ hpne (w0 := w0) hΦc x
      simpa [hq4val, omC] using hg
    rw [hT]
    exact mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 4) hw) hg0
  -- per-p: integral of the combined integrand ≥ 0, expanded by linearity
  have hper : ∀ p ∈ pairSet N,
      0 ≤ (1 / 2) * (∫ x in abox N ℓ, (Φ x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))
        - (1 / 4) * (∫ x in abox N ℓ, (q4B ℓ (omC w0) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))
        + (1 / 2) * (∫ x in abox N ℓ,
            (1 - w0 (x p.1 - x p.2)) ^ 2 *
            (aP ℓ p.1 (aP ℓ p.2 Φ) x + aP ℓ p.1 (aQ ℓ p.2 Φ) x + aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 *
            wPairC ℓ v (x p.1) (x p.2)) := by
    intro p hp
    have hpne : p.1 ≠ p.2 := by simpa [pairSet] using hp
    let fΦ : XN N → ℝ := fun x => (Φ x) ^ 2 * wPairC ℓ v (x p.1) (x p.2)
    let fE : XN N → ℝ := fun x => (q4B ℓ (omC w0) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2)
    let fM : XN N → ℝ := fun x => (1 - w0 (x p.1 - x p.2)) ^ 2 *
        (aP ℓ p.1 (aP ℓ p.2 Φ) x + aP ℓ p.1 (aQ ℓ p.2 Φ) x + aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 *
        wPairC ℓ v (x p.1) (x p.2)
    have hInt : 0 ≤ (∫ x in abox N ℓ,
        (1 / 2) * fΦ x - (1 / 4) * fE x + (1 / 2) * fM x) := by
      apply integral_nonneg
      intro x
      have h := hpi p hp x
      dsimp [fΦ, fE, fM] at h ⊢
      ring_nf at h ⊢
      exact h
    have hIntfΦ : IntegrableOn fΦ (abox N ℓ) volume := by
      have hSc1 : Continuous (fun x : XN N => (Φ x) ^ 2) := by fun_prop
      have hif : IntegrableOn (fun x : XN N => (Φ x) ^ 2 * wPair ℓ v (x p.1) (x p.2))
          (abox N ℓ) volume :=
        integrableOn_slot_wPair (h := v) hℓ (v_integrable hv_memL1)
          (fun z hz => v_eq_zero_of_norm_ge hv_supp hz) hRℓ hpne hSc1
      simpa [fΦ, wPairC] using hif
    have hIntfE : IntegrableOn fE (abox N ℓ) volume := by
      have hfg := integrableOn_fg4_chosen hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hpne
      have hEq : fE = fun x : XN N => 2 * fg4 ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ p.1 p.2 x := by
        funext x
        dsimp [fg4, fE]
        simp [w0]
        ring
      rw [hEq]
      exact hfg.const_mul 2
    have hIntfM : IntegrableOn fM (abox N ℓ) volume := by
      have h2 := potapp_M2pair_integrable hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc hpne
      have hEq : fM = fun x : XN N =>
          (1 - Classical.choose h (x p.1 - x p.2)) ^ 2 *
          (aP ℓ p.1 (aP ℓ p.2 Φ) x + aP ℓ p.1 (aQ ℓ p.2 Φ) x + aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 *
          wPairC ℓ v (x p.1) (x p.2) := by
        funext x
        simp [fM, w0]
      rw [hEq]
      exact h2
    have hfΦ : Integrable fΦ μ := by simpa [μ, fΦ, IntegrableOn] using hIntfΦ
    have hfE : Integrable fE μ := by simpa [μ, fE, IntegrableOn] using hIntfE
    have hfM : Integrable fM μ := by simpa [μ, fM, IntegrableOn] using hIntfM
    have hExp : (∫ x : XN N, (1 / 2) * fΦ x - (1 / 4) * fE x + (1 / 2) * fM x ∂μ)
        = (1 / 2) * (∫ x : XN N, fΦ x ∂μ) - (1 / 4) * (∫ x : XN N, fE x ∂μ)
          + (1 / 2) * (∫ x : XN N, fM x ∂μ) := by
      let A : XN N → ℝ := fun x => (1 / 2) * fΦ x
      let B : XN N → ℝ := fun x => (1 / 4) * fE x
      let C : XN N → ℝ := fun x => (1 / 2) * fM x
      have hA : Integrable A μ := by simpa [A, μ, IntegrableOn] using hIntfΦ.const_mul (1 / 2)
      have hB : Integrable B μ := by simpa [B, μ, IntegrableOn] using hIntfE.const_mul (1 / 4)
      have hC : Integrable C μ := by simpa [C, μ, IntegrableOn] using hIntfM.const_mul (1 / 2)
      have hExp1 : (∫ x : XN N, A x - B x + C x ∂μ) = (∫ x : XN N, A x ∂μ) - (∫ x : XN N, B x ∂μ)
          + (∫ x : XN N, C x ∂μ) := by
        calc
          (∫ x : XN N, A x - B x + C x ∂μ) = ∫ x : XN N, (A - B) x + C x ∂μ := by rfl
          _ = (∫ x : XN N, (A - B) x ∂μ) + (∫ x : XN N, C x ∂μ) := by
                exact integral_add (hA.sub hB) hC
          _ = (∫ x : XN N, A x ∂μ) - (∫ x : XN N, B x ∂μ) + (∫ x : XN N, C x ∂μ) := by
                have hpt : (fun x : XN N => (A - B) x) = fun x : XN N => A x - B x := by
                  funext x
                  rfl
                rw [hpt]
                rw [integral_sub hA hB]
      have hExp2 : (∫ x : XN N, A x - B x + C x ∂μ) =
          (∫ x : XN N, (1 / 2) * fΦ x - (1 / 4) * fE x + (1 / 2) * fM x ∂μ) := by
        apply integral_congr_ae
        apply ae_of_all
        intro x
        rfl
      have hA' : (∫ x : XN N, A x ∂μ) = (1 / 2) * (∫ x : XN N, fΦ x ∂μ) := by
        change (∫ x : XN N, (1 / 2) * fΦ x ∂μ) = (1 / 2) * (∫ x : XN N, fΦ x ∂μ)
        exact integral_const_mul (1 / 2) fΦ
      have hB' : (∫ x : XN N, B x ∂μ) = (1 / 4) * (∫ x : XN N, fE x ∂μ) := by
        change (∫ x : XN N, (1 / 4) * fE x ∂μ) = (1 / 4) * (∫ x : XN N, fE x ∂μ)
        exact integral_const_mul (1 / 4) fE
      have hC' : (∫ x : XN N, C x ∂μ) = (1 / 2) * (∫ x : XN N, fM x ∂μ) := by
        change (∫ x : XN N, (1 / 2) * fM x ∂μ) = (1 / 2) * (∫ x : XN N, fM x ∂μ)
        exact integral_const_mul (1 / 2) fM
      calc
        (∫ x : XN N, (1 / 2) * fΦ x - (1 / 4) * fE x + (1 / 2) * fM x ∂μ)
            = ∫ x : XN N, A x - B x + C x ∂μ := by
                rw [hExp2]
        _ = (∫ x : XN N, A x ∂μ) - (∫ x : XN N, B x ∂μ) + (∫ x : XN N, C x ∂μ) := hExp1
        _ = (1 / 2) * (∫ x : XN N, fΦ x ∂μ) - (1 / 4) * (∫ x : XN N, fE x ∂μ)
            + (1 / 2) * (∫ x : XN N, fM x ∂μ) := by
                rw [hA', hB', hC']
    have hInt' : 0 ≤ (1 / 2) * (∫ x : XN N, fΦ x ∂μ) - (1 / 4) * (∫ x : XN N, fE x ∂μ)
        + (1 / 2) * (∫ x : XN N, fM x ∂μ) := by
      rw [← hExp]
      simpa [μ] using hInt
    have hBox : (1 / 2) * (∫ x : XN N, fΦ x ∂μ) - (1 / 4) * (∫ x : XN N, fE x ∂μ)
        + (1 / 2) * (∫ x : XN N, fM x ∂μ)
        = (1 / 2) * (∫ x in abox N ℓ, (Φ x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))
          - (1 / 4) * (∫ x in abox N ℓ, (q4B ℓ (omC w0) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))
          + (1 / 2) * (∫ x in abox N ℓ, (1 - w0 (x p.1 - x p.2)) ^ 2 *
            (aP ℓ p.1 (aP ℓ p.2 Φ) x + aP ℓ p.1 (aQ ℓ p.2 Φ) x + aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 *
            wPairC ℓ v (x p.1) (x p.2)) := by
      simp [μ, fΦ, fE, fM]
    rw [← hBox]
    exact hInt'
  -- sum over pairs
  have hsum : 0 ≤ ∑ p ∈ pairSet N, ((1 / 2) * (∫ x in abox N ℓ, (Φ x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))
        - (1 / 4) * (∫ x in abox N ℓ, (q4B ℓ (omC w0) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))
        + (1 / 2) * (∫ x in abox N ℓ,
            (1 - w0 (x p.1 - x p.2)) ^ 2 *
            (aP ℓ p.1 (aP ℓ p.2 Φ) x + aP ℓ p.1 (aQ ℓ p.2 Φ) x + aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 *
            wPairC ℓ v (x p.1) (x p.2))) := by
    exact Finset.sum_nonneg (fun p hp => hper p hp)
  -- the core LHS equals that sum
  have hEqSum : (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ, (Φ x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))
      - (1 / 4) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (q4B ℓ (omC w0) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))
      + (1 / 2) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (1 - w0 (x p.1 - x p.2)) ^ 2 *
          (aP ℓ p.1 (aP ℓ p.2 Φ) x + aP ℓ p.1 (aQ ℓ p.2 Φ) x + aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 *
          wPairC ℓ v (x p.1) (x p.2))
      = ∑ p ∈ pairSet N, ((1 / 2) * (∫ x in abox N ℓ, (Φ x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))
        - (1 / 4) * (∫ x in abox N ℓ, (q4B ℓ (omC w0) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))
        + (1 / 2) * (∫ x in abox N ℓ,
            (1 - w0 (x p.1 - x p.2)) ^ 2 *
            (aP ℓ p.1 (aP ℓ p.2 Φ) x + aP ℓ p.1 (aQ ℓ p.2 Φ) x + aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 *
            wPairC ℓ v (x p.1) (x p.2))) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    rw [Finset.sum_add_distrib]
    rw [Finset.sum_sub_distrib]
  rw [hEqSum]
  simpa [w0] using hsum



/-- **potapp_q4** (scratch version) -/
theorem potapp_q4 {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (μ : ℝ) (hμ : 0 ≤ μ)
    {v : ℝ³ → ℝ} (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    {R : ℝ} (hR : 0 < R) (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hRℓ : R ≤ ℓ * chiR0) {Φ : XN N → ℝ} (hΦc : Continuous Φ) :
    qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ ≥
      - potappC * ((N : ℝ) ^ 2 / ℓ ^ 3 + μ ^ 2 * ℓ ^ 3) * (a v) *
          (∫ x in abox N ℓ, (Φ x) ^ 2)
      + (1 / 2) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
  let C0 : ℝ := chiSup ^ 2 * 2 * (8 * π * a v)
  let I : ℝ := ∫ x in abox N ℓ, (Φ x) ^ 2
  let X : ℝ := (N : ℝ) ^ 2 / ℓ ^ 3 + μ ^ 2 * ℓ ^ 3
  let w0 : ℝ³ → ℝ := Classical.choose h
  let musum : ℝ := ∑ i : Fin N, muPhi ℓ (wPairC ℓ (g0 v h)) Φ i
  let M2sum : ℝ := ∑ p ∈ pairSet N, ∫ x in abox N ℓ,
      (1 - w0 (x p.1 - x p.2)) ^ 2 *
      (aP ℓ p.1 (aP ℓ p.2 Φ) x + aP ℓ p.1 (aQ ℓ p.2 Φ) x + aQ ℓ p.1 (aP ℓ p.2 Φ) x) ^ 2 *
      wPairC ℓ v (x p.1) (x p.2)
  have hsplit := qLHSword_split hℓ μ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
  have hcore := potapp_core_nonneg hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
  have hm2 := potapp_M2sq_le hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
  have hmuabs := potapp_musum_abs_le hℓ hv_nonneg hvrad hv_memL1 hR hv_supp h hRℓ hΦc
  have hAv : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    positivity
  have hI : 0 ≤ I := by
    dsimp [I]
    exact integral_nonneg (fun x : XN N => sq_nonneg (Φ x))
  -- half of q4
  have hq4h : (1 / 2) * q4word (N := N) ℓ (wPairC ℓ v) (omC w0) Φ =
      (1 / 4) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (q4B ℓ (omC w0) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2)) := by
    unfold q4word
    ring
  -- main lower bound in terms of musum and M2sum
  have hMain : qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ ≥
      (1 / 2) * q4word (N := N) ℓ (wPairC ℓ v) (omC w0) Φ - μ * musum - (1 / 2) * M2sum := by
    have hMu : qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ
        = (- μ) * musum + (1 / 2) * (∑ p ∈ pairSet N,
            ∫ x in abox N ℓ, (Φ x) ^ 2 * wPairC ℓ v (x p.1) (x p.2)) := by
      simpa [musum] using hsplit
    have hq4 : (1 / 2) * q4word (N := N) ℓ (wPairC ℓ v) (omC w0) Φ =
        (1 / 4) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
          (q4B ℓ (omC w0) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2)) := hq4h
    have hpaircore : (1 / 2) * (∑ p ∈ pairSet N,
          ∫ x in abox N ℓ, (Φ x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))
        ≥ (1 / 2) * q4word (N := N) ℓ (wPairC ℓ v) (omC w0) Φ - (1 / 2) * M2sum := by
      have hc' : (1 / 2) * (∑ p ∈ pairSet N,
            ∫ x in abox N ℓ, (Φ x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))
          - (1 / 4) * (∑ p ∈ pairSet N, ∫ x in abox N ℓ,
              (q4B ℓ (omC w0) Φ p x) ^ 2 * wPairC ℓ v (x p.1) (x p.2))
          + (1 / 2) * M2sum ≥ 0 := by
        simpa [w0] using hcore
      rw [hq4]
      nlinarith [hc']
    rw [hMu]
    nlinarith [hpaircore]
  -- convert the losses into the (X, I)-form
  have hmus : (- μ) * musum ≥ - μ * (C0 * (N : ℝ) * I) := by
    have hmusabs : |musum| ≤ C0 * (N : ℝ) * I := by
      simpa [musum, C0, I] using hmuabs
    have hm2_ : musum ≤ C0 * (N : ℝ) * I := le_trans (le_abs_self musum) hmusabs
    have hm3_ : -musum ≤ C0 * (N : ℝ) * I := by
      have h1 : -musum ≤ |musum| := neg_le_abs musum
      exact le_trans h1 hmusabs
    have h1 : (- μ) * musum ≥ - μ * (C0 * (N : ℝ) * I) := by
      have h : μ * musum ≤ μ * (C0 * (N : ℝ) * I) := mul_le_mul_of_nonneg_left hm2_ hμ
      linarith
    exact h1
  have hM2 : - (1 / 2) * M2sum ≥ - (1 / 2) * (100 * C0 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * I) := by
    have hm : M2sum ≤ 100 * C0 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * I := by
      simpa [M2sum, C0, I] using hm2
    have hM0 : 0 ≤ (1 / 2 : ℝ) := by norm_num
    have hm' : (1 / 2) * M2sum ≤ (1 / 2) * (100 * C0 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * I) :=
      mul_le_mul_of_nonneg_left hm hM0
    linarith
  -- AM-GM: μ·N̂·I ≤ (1/2)·X·I ; and (N̂²/ℓ³)·I ≤ X·I
  have hXN : μ * (N : ℝ) ≤ (1 / 2) * ((N : ℝ) ^ 2 / ℓ ^ 3 + μ ^ 2 * ℓ ^ 3) := by
    have hℓ3 : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
    have hsq : 0 ≤ (μ * ℓ ^ 3 - (N : ℝ)) ^ 2 := sq_nonneg _
    have hdiv : 0 ≤ (μ * ℓ ^ 3 - (N : ℝ)) ^ 2 / ℓ ^ 3 :=
      div_nonneg hsq (pow_nonneg hℓ.le 3)
    have heq : (μ * ℓ ^ 3 - (N : ℝ)) ^ 2 / ℓ ^ 3 =
        μ ^ 2 * ℓ ^ 3 - 2 * μ * (N : ℝ) + (N : ℝ) ^ 2 / ℓ ^ 3 := by
      field_simp [hℓ3]
      ring
    rw [heq] at hdiv
    nlinarith [mul_nonneg hμ (by positivity : 0 ≤ (N : ℝ))]
  have hNl : (N : ℝ) ^ 2 / ℓ ^ 3 ≤ X := by
    dsimp [X]
    nlinarith [sq_nonneg μ, pow_nonneg hℓ.le 3]
  have hC0I : 0 ≤ C0 * I := mul_nonneg hC0 hI
  have hX0 : 0 ≤ X := by
    dsimp [X]
    positivity
  -- AM-GM: μ·N̂ ≤ (1/2)·X
  have hXN : μ * (N : ℝ) ≤ (1 / 2) * X := by
    have hℓ3 : ℓ ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hℓ)
    have hsq : 0 ≤ (μ * ℓ ^ 3 - (N : ℝ)) ^ 2 := sq_nonneg _
    have hdiv : 0 ≤ (μ * ℓ ^ 3 - (N : ℝ)) ^ 2 / ℓ ^ 3 :=
      div_nonneg hsq (pow_nonneg hℓ.le 3)
    have heq : (μ * ℓ ^ 3 - (N : ℝ)) ^ 2 / ℓ ^ 3 =
        μ ^ 2 * ℓ ^ 3 - 2 * μ * (N : ℝ) + (N : ℝ) ^ 2 / ℓ ^ 3 := by
      field_simp [hℓ3]
      ring
    rw [heq] at hdiv
    have hpos : 0 ≤ μ * (N : ℝ) := mul_nonneg hμ (by positivity)
    dsimp [X]
    nlinarith
  have hmus : (- μ) * musum ≥ - μ * (C0 * (N : ℝ) * I) := by
    have hmusabs : |musum| ≤ C0 * (N : ℝ) * I := by
      simpa [musum, C0, I] using hmuabs
    have hm2_ : musum ≤ C0 * (N : ℝ) * I := le_trans (le_abs_self musum) hmusabs
    have h1 : μ * musum ≤ μ * (C0 * (N : ℝ) * I) := mul_le_mul_of_nonneg_left hm2_ hμ
    nlinarith
  have hA1 : - μ * (C0 * (N : ℝ) * I) ≥ - (1 / 2) * C0 * X * I := by
    have hμX : μ * (N : ℝ) ≤ (1 / 2) * X := hXN
    have h1 : C0 * (μ * (N : ℝ)) ≤ C0 * ((1 / 2) * X) :=
      mul_le_mul_of_nonneg_left hμX hC0
    have h2 : (C0 * (μ * (N : ℝ))) * I ≤ (C0 * ((1 / 2) * X)) * I :=
      mul_le_mul_of_nonneg_right h1 hI
    have h3 : μ * (C0 * (N : ℝ)) * I ≤ (1 / 2) * C0 * X * I := by
      nlinarith [h2]
    nlinarith
  have hM2 : - (1 / 2) * M2sum ≥ - 50 * C0 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * I := by
    have hm : M2sum ≤ 100 * C0 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * I := by
      simpa [M2sum, C0, I] using hm2
    nlinarith
  have hNl2 : (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 ≤ X := by
    have hEq : (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 = (N : ℝ) ^ 2 / ℓ ^ 3 := by ring
    rw [hEq]
    dsimp [X]
    nlinarith [sq_nonneg μ, pow_nonneg hℓ.le 3]
  have hM3 : - 50 * C0 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * I ≥ - 50 * C0 * X * I := by
    have h1 : (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 ≤ X := hNl2
    have hC50 : 0 ≤ 50 * C0 := by positivity
    have h2 : ((ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2) * (50 * C0) ≤ X * (50 * C0) :=
      mul_le_mul_of_nonneg_right h1 hC50
    have h2' : 50 * C0 * ((ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2) ≤ 50 * C0 * X := by
      calc
        50 * C0 * ((ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2) = ((ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2) * (50 * C0) := by ring
        _ ≤ X * (50 * C0) := h2
        _ = 50 * C0 * X := by ring
    have h3 : 50 * C0 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * I ≤ 50 * C0 * X * I := by
      have h4 : 50 * C0 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 ≤ 50 * C0 * X := by
        calc
          50 * C0 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 = 50 * C0 * ((ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2) := by ring
          _ ≤ 50 * C0 * X := h2'
      exact mul_le_mul_of_nonneg_right h4 hI
    linarith
  have hconst : (1 / 2) * C0 + 50 * C0 ≤ potappC * (a v) := by
    dsimp [potappC, C0]
    let u : ℝ := chiSup ^ 2 * (8 * π) * (a v)
    have hu : 0 ≤ u := by
      dsimp [u]
      positivity
    have hstep : (101 : ℝ) * u ≤ 1000 * u := by
      have hnn : (101 : ℝ) ≤ 1000 := by norm_num
      calc
        (101 : ℝ) * u = u * 101 := by ring
        _ ≤ u * 1000 := mul_le_mul_of_nonneg_left hnn hu
        _ = 1000 * u := by ring
    nlinarith
  have hfinish : - (1 / 2) * C0 * X * I - 50 * C0 * X * I ≥
      - potappC * X * (a v) * I := by
    have hPot : 0 ≤ potappC * (a v) := by
      dsimp [potappC]
      positivity
    have hF : ((1 / 2) * C0 + 50 * C0) * X * I ≤ (potappC * (a v)) * X * I := by
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hconst hX0) hI
    nlinarith [hF]
  calc
    qLHSword (N := N) ℓ μ (wPairC ℓ v) (wPairC ℓ (g0 v h)) Φ
        ≥ (1 / 2) * q4word (N := N) ℓ (wPairC ℓ v) (omC w0) Φ - μ * musum - (1 / 2) * M2sum := hMain
    _ ≥ (1 / 2) * q4word (N := N) ℓ (wPairC ℓ v) (omC w0) Φ
        - μ * (C0 * (N : ℝ) * I) - (1 / 2) * M2sum := by
          have h1 : - μ * musum ≥ - μ * (C0 * (N : ℝ) * I) := hmus
          linarith
    _ ≥ (1 / 2) * q4word (N := N) ℓ (wPairC ℓ v) (omC w0) Φ
        - μ * (C0 * (N : ℝ) * I) - 50 * C0 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * I := by
          have h1 : - (1 / 2) * M2sum ≥ - 50 * C0 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * I := hM2
          linarith
    _ ≥ (1 / 2) * q4word (N := N) ℓ (wPairC ℓ v) (omC w0) Φ
        - (1 / 2) * C0 * X * I - 50 * C0 * X * I := by
          have h1 : - μ * (C0 * (N : ℝ) * I) ≥ - (1 / 2) * C0 * X * I := hA1
          have h2 : - 50 * C0 * (ℓ ^ 3)⁻¹ * (N : ℝ) ^ 2 * I ≥ - 50 * C0 * X * I := hM3
          linarith
    _ ≥ (1 / 2) * q4word (N := N) ℓ (wPairC ℓ v) (omC w0) Φ
        - potappC * X * (a v) * I := by
          linarith [hfinish]
    _ = - potappC * ((N : ℝ) ^ 2 / ℓ ^ 3 + μ ^ 2 * ℓ ^ 3) * (a v) * I
        + (1 / 2) * q4word (N := N) ℓ (wPairC ℓ v) (omC (Classical.choose h)) Φ := by
          have hX : X = (N : ℝ) ^ 2 / ℓ ^ 3 + μ ^ 2 * ℓ ^ 3 := by rfl
          have hw0 : omC w0 = omC (Classical.choose h) := by rfl
          rw [hX]
          ring

end BoseGases
end Submission
