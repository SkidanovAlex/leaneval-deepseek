import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.ChosenDensity
import Submission.Work.SboxESlice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The corpus per-sector small-box ground energy `eB` and its superadditivity

The corpus replay of the FS `e_B` (the `n`-particle ground-state energy of the
`μ`-dependent box Hamiltonian) over the centred box `abox n s`:

    eB n s μ v h := ⨅_{Φ ∈ CSBox n s} sboxE n s μ (wPairC s v) (wPairC s (g0 v h)) Φ / ‖Φ‖²

with `CSBox n s` the smooth nonzero states with positive centred-box norm
(mirror of `CNeu`, over `abox` instead of the plain box).  Contents:

  * `CSBox`, `CSBox.ofFun`, `eB`;
  * chosen-branch lower bounds of `qLHSden`/`qLHSword`/`sboxE`
    (the fibre bound `w1c_fibre_acube_abs_le` + `wPairC_nonneg`);
  * `eB_quot_bddBelow`, `eB_le_quot_ofFun`, `sboxE_mul_le_chosen`
    (mirrors of `eNeu_quot_bddBelow` / `eNeu_le_quot_ofFun` /
    `es_eNeu_mul_le`);
  * the block bounds `sbox_block1_bound` / `sbox_block2_bound` and the
    per-state / superadditivity theorems (mirrors of `es_block1_bound` /
    `es_per_state` / `eNeu_superadd`), all at the chosen kernels.
-/

set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## The trial space and the infimum -/

/-- Trial states for the small-box ground energy over the centred box:
smooth on the whole configuration space, nonzero, with positive centred-box
norm. -/
structure CSBox (N : ℕ) (s : ℝ) where
  toFun : X N → ℝ
  /-- Smooth on the whole space. -/
  contDiff : ContDiff ℝ ∞ toFun
  /-- Not the zero function. -/
  nezero : toFun ≠ 0
  /-- Positive `L²`-norm over the centred box. -/
  sq_pos : 0 < ∫ x in abox N s, (toFun x) ^ 2

instance (N : ℕ) (s : ℝ) : CoeFun (CSBox N s) (fun _ ↦ X N → ℝ) where
  coe Φ := Φ.toFun

/-- Build a `CSBox` state from a smooth nonzero function with positive
centred-box norm. -/
noncomputable def CSBox.ofFun {N : ℕ} {s : ℝ} {f : X N → ℝ} (hf : ContDiff ℝ ∞ f)
    (hne : f ≠ 0) (hpos : 0 < ∫ x in abox N s, (f x) ^ 2) : CSBox N s :=
  ⟨f, hf, hne, hpos⟩

/-- The chosen-branch `g₀`-fibre bound × the particle number (the constant of
the pointwise lower bounds below). -/
noncomputable def sboxC (N : ℕ) (μ : ℝ) (v : ℝ³ → ℝ) : ℝ :=
  μ * (N : ℝ) * (chiSup ^ 2 * 2 * (8 * π * (a v)))

/-- The corpus small-box ground energy at the chosen kernels: the infimum of
the `sboxE`-quotients over `CSBox N s`. -/
noncomputable def eB (N : ℕ) (s μ : ℝ) (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) : ℝ :=
  ⨅ Φ : CSBox N s, (sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) (Φ : X N → ℝ)) /
    (∫ x in abox N s, ((Φ : X N → ℝ) x) ^ 2)

/-! ## Chosen-branch boundedness of the `qLHSword` density -/

/-- The `g₀`-fibre over the centred cube is bounded above by the `sboxC`
constant (per particle). -/
lemma chosen_g0_fibre_ub {N : ℕ} {s R : ℝ} {v : ℝ³ → ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (i : Fin N) (x : X N) :
    w1Fibre s (wPairC s (g0 v h)) (x i) ≤ chiSup ^ 2 * 2 * (8 * π * (a v)) := by
  have hb := w1c_fibre_acube_abs_le hR hv_nonneg hvrad hv_supp h hs hRs (x i)
  exact le_of_abs_le hb

/-- Pointwise lower bound of the `qLHSword` diagonal density over the whole
configuration space (chosen kernels): `qLHSden ≥ −sboxC` pointwise. -/
lemma qLHSden_chosen_lower {N : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 ≤ μ) (x : X N) :
    - sboxC N μ v ≤ qLHSden N s μ (wPairC s v) (wPairC s (g0 v h)) x := by
  let Cf : ℝ := chiSup ^ 2 * 2 * (8 * π * (a v))
  have hav : 0 ≤ a v := (av_bounds_weak hR hv_nonneg hvrad hv_supp h).1
  have hC0 : 0 ≤ Cf := by
    dsimp [Cf]
    have h8 : 0 ≤ 8 * π * (a v) := by
      exact mul_nonneg (mul_nonneg (by norm_num : 0 ≤ (8 : ℝ)) (le_of_lt Real.pi_pos)) hav
    exact mul_nonneg (mul_nonneg (sq_nonneg chiSup) (by norm_num : 0 ≤ (2 : ℝ))) h8
  have hfib : ∀ i : Fin N, w1Fibre s (wPairC s (g0 v h)) (x i) ≤ Cf := by
    intro i
    simpa [Cf] using chosen_g0_fibre_ub (N := N) hR hv_nonneg hvrad hv_supp h hs hRs i x
  have hfibSum : (∑ i : Fin N, w1Fibre s (wPairC s (g0 v h)) (x i)) ≤ (N : ℝ) * Cf := by
    calc
      (∑ i : Fin N, w1Fibre s (wPairC s (g0 v h)) (x i))
          ≤ ∑ i : Fin N, Cf := Finset.sum_le_sum (fun i _ => hfib i)
      _ = (N : ℝ) * Cf := by simp
  have hw : ∀ p ∈ pairSet N, 0 ≤ wPairC s v (x p.1) (x p.2) := fun p _ =>
    wPairC_nonneg hv_nonneg s (x p.1) (x p.2)
  have hwSum : 0 ≤ ∑ p ∈ pairSet N, wPairC s v (x p.1) (x p.2) :=
    Finset.sum_nonneg (fun p hp => hw p hp)
  dsimp [sboxC]
  rw [qLHSden]
  have h1 : 0 ≤ (1 / 2 : ℝ) * (∑ p ∈ pairSet N, wPairC s v (x p.1) (x p.2)) := by
    exact mul_nonneg (by norm_num) hwSum
  have h2 : - μ * (∑ i : Fin N, w1Fibre s (wPairC s (g0 v h)) (x i)) ≥ - μ * (Cf * (N : ℝ)) := by
    have hmul := mul_le_mul_of_nonneg_left hfibSum hμ
    nlinarith
  nlinarith

/-- The `qLHSword` of a smooth state is bounded below by `−sboxC·‖Φ‖²`
(chosen kernels). -/
lemma qLHSword_chosen_lower {N : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 ≤ μ) {Φ : X N → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) :
    - sboxC N μ v * (∫ x in abox N s, (Φ x) ^ 2)
      ≤ qLHSword (N := N) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
  have hD : IntegrableOn (fun x : X N => (Φ x) ^ 2 *
      qLHSden N s μ (wPairC s v) (wPairC s (g0 v h)) x) (abox N s) volume :=
    chosen_qLHSden_integrableOn (N := N) hs hR hv_nonneg hvrad hv_memL1 hv_supp h hRs hΦc.continuous
  have hC : IntegrableOn (fun x : X N => (Φ x) ^ 2) (abox N s) volume :=
    integrableOn_abox_of_continuous hs (hΦc.continuous.pow 2)
  have hCg : IntegrableOn (fun x : X N => (Φ x) ^ 2 * (- sboxC N μ v)) (abox N s) volume := by
    change Integrable (fun x : X N => (Φ x) ^ 2 * (- sboxC N μ v)) (volume.restrict (abox N s))
    simpa [mul_comm] using (hC.const_mul (- sboxC N μ v))
  rw [qLHSword_eq_integral_qLHSden]
  have hle : (∫ x in abox N s, (Φ x) ^ 2 * (- sboxC N μ v))
      ≤ ∫ x in abox N s, (Φ x) ^ 2 * qLHSden N s μ (wPairC s v) (wPairC s (g0 v h)) x := by
    refine integral_mono ?_ ?_ ?_
    · exact hCg
    · exact hD
    · intro x
      have hd := qLHSden_chosen_lower (N := N) hR hv_nonneg hvrad hv_supp h hs hRs hμ x
      exact mul_le_mul_of_nonneg_left hd (sq_nonneg (Φ x))
  have hEq : (∫ x in abox N s, (Φ x) ^ 2 * (- sboxC N μ v))
      = - sboxC N μ v * (∫ x in abox N s, (Φ x) ^ 2) := by
    rw [integral_mul_const]
    ring
  rw [hEq] at hle
  exact hle

/-- `sboxE` of a smooth state is bounded below by `−sboxC·‖Φ‖²` (the kinetic
word is nonnegative). -/
lemma sboxE_chosen_lower {N : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 ≤ μ) {Φ : X N → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) :
    - sboxC N μ v * (∫ x in abox N s, (Φ x) ^ 2) ≤ sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
  have hq := qLHSword_chosen_lower (N := N) hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRs hμ hΦc
  have hk : 0 ≤ kinWord N s Φ := kinWord_nonneg N s Φ
  unfold sboxE
  nlinarith

/-- The `eB`-quotients are bounded below by `−sboxC` (chosen branch). -/
lemma eB_quot_bddBelow {N : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 ≤ μ) :
    BddBelow (Set.range (fun Φ : CSBox N s =>
      (sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) (Φ : X N → ℝ)) /
        (∫ x in abox N s, ((Φ : X N → ℝ) x) ^ 2))) := by
  refine ⟨- sboxC N μ v, ?_⟩
  intro y hy
  rcases hy with ⟨Φ, rfl⟩
  have hb := sboxE_chosen_lower (N := N) hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRs hμ
    (Φ := (Φ : X N → ℝ)) Φ.contDiff
  exact (le_div_iff₀ Φ.sq_pos).mpr hb

/-- `eB` is a lower bound for the quotient of any admissible smooth state. -/
lemma eB_le_quot_ofFun {N : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 ≤ μ) {Φ : X N → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) (hne : Φ ≠ 0)
    (hpos : 0 < ∫ x in abox N s, (Φ x) ^ 2) :
    eB N s μ v h ≤
      (sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) Φ) /
        (∫ x in abox N s, (Φ x) ^ 2) := by
  have hbdd := eB_quot_bddBelow (N := N) hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRs hμ
  let Φ₀ : CSBox N s := CSBox.ofFun hΦc hne hpos
  have hle := ciInf_le hbdd Φ₀
  unfold eB
  simpa [Φ₀, CSBox.ofFun] using hle

/-- **`eB`-Rayleigh inequality**: `eB·‖Φ‖² ≤ sboxE Φ` for every smooth
`Φ` (the zero-norm case uses `sboxE ≥ −sboxC·0 = 0`, the positive case the
quotient bound). -/
lemma sboxE_mul_le_chosen {N : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 < μ) {Φ : X N → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) :
    eB N s μ v h * (∫ x in abox N s, (Φ x) ^ 2)
      ≤ sboxE N s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
  by_cases hz : (∫ x in abox N s, (Φ x) ^ 2) = 0
  · rw [hz, mul_zero]
    have hb := sboxE_chosen_lower (N := N) hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRs hμ.le
      (Φ := Φ) hΦc
    rw [hz] at hb
    simpa using hb
  · have hpos : 0 < ∫ x in abox N s, (Φ x) ^ 2 :=
      lt_of_le_of_ne (integral_nonneg (fun x => sq_nonneg (Φ x))) (Ne.symm hz)
    have hne : Φ ≠ 0 := by
      intro hΦ0
      apply hz
      simp [hΦ0]
    have hq := eB_le_quot_ofFun (N := N) hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRs hμ.le
      hΦc hne hpos
    exact (le_div_iff₀ hpos).mp hq

/-! ## Block bounds, per-state inequality and superadditivity -/

/-- Per-`w`: the `eB(N1)`-Rayleigh inequality for the first-block slice
(the `es_slice1_VI` mirror, expressed with the merged-box densities). -/
lemma sbox_slice1_bound {N1 N2 : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 < μ) {Φ : X (N1+N2) → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) (w : X N2) :
    eB N1 s μ v h *
      (∫ u in abox N1 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2)
      ≤ (∫ u in abox N1 s, es_kinB1 N1 N2 Φ (mergeBlock N1 N2 (u, w)))
        + (∫ u in abox N1 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2 *
            qLHSden1 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h))
              (mergeBlock N1 N2 (u, w))) := by
  have hs1 := sboxE_mul_le_chosen (N := N1) hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRs hμ
    (Φ := sbs_slice Φ w) (es_slice1_contDiff hΦc w)
  have hE : sboxE N1 s μ (wPairC s v) (wPairC s (g0 v h)) (sbs_slice Φ w)
      = (∫ u in abox N1 s, es_kinB1 N1 N2 Φ (mergeBlock N1 N2 (u, w)))
        + (∫ u in abox N1 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2 *
            qLHSden1 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h))
              (mergeBlock N1 N2 (u, w))) := by
    calc
      sboxE N1 s μ (wPairC s v) (wPairC s (g0 v h)) (sbs_slice Φ w)
          = kinWord N1 s (sbs_slice Φ w)
              + qLHSword (N := N1) s μ (wPairC s v) (wPairC s (g0 v h)) (sbs_slice Φ w) := rfl
      _ = (∫ u in abox N1 s, es_kinAll N1 (sbs_slice Φ w) u)
              + qLHSword (N := N1) s μ (wPairC s v) (wPairC s (g0 v h)) (sbs_slice Φ w) := by
            rw [kinWord_eq_integral_es_kinAll (N := N1) (s := s) hs (ψ := sbs_slice Φ w)
              (es_slice1_contDiff hΦc w)]
      _ = (∫ u in abox N1 s, es_kinAll N1 (sbs_slice Φ w) u)
              + ∫ u in abox N1 s, (sbs_slice Φ w u) ^ 2 *
                  qLHSden N1 s μ (wPairC s v) (wPairC s (g0 v h)) u := by rfl
      _ = (∫ u in abox N1 s, es_kinB1 N1 N2 Φ (mergeBlock N1 N2 (u, w)))
              + ∫ u in abox N1 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2 *
                  qLHSden N1 s μ (wPairC s v) (wPairC s (g0 v h)) u := by
            congr 1
            apply integral_congr_ae
            filter_upwards with u
            exact (slice1_kinAll_eq hΦc u w)
      _ = (∫ u in abox N1 s, es_kinB1 N1 N2 Φ (mergeBlock N1 N2 (u, w)))
              + ∫ u in abox N1 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2 *
                  qLHSden1 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h))
                    (mergeBlock N1 N2 (u, w)) := by
            congr 1
            apply integral_congr_ae
            filter_upwards with u
            rw [qLHSden1_merge (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) u w]
  have hm : (∫ u in abox N1 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2)
      = ∫ u in abox N1 s, (sbs_slice Φ w u) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with u
    rfl
  rw [← hm] at hs1
  rw [hE] at hs1
  exact hs1

/-- Block-1 bound: `eB(N1)·‖Φ‖² ≤ sboxE1` for smooth `Φ` over the merged box. -/
lemma sbox_block1_bound {N1 N2 : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 < μ) {Φ : X (N1+N2) → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) :
    eB N1 s μ v h * (∫ x in abox (N1+N2) s, (Φ x) ^ 2) ≤
      sboxE1 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
  let E1 := eB N1 s μ v h
  have hP0 : IntegrableOn (fun x : X (N1+N2) => (Φ x) ^ 2) (abox (N1+N2) s) volume :=
    integrableOn_abox_of_continuous hs (hΦc.continuous.pow 2)
  have hK1 : IntegrableOn (es_kinB1 N1 N2 Φ) (abox (N1+N2) s) volume :=
    es_kinB1_integrableOn_abox hs hΦc
  have hD1 : IntegrableOn (fun x : X (N1+N2) => (Φ x) ^ 2 *
      qLHSden1 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) x)
      (abox (N1+N2) s) volume :=
    chosen_qLHSden1_integrableOn (N1 := N1) (N2 := N2) hs hR hv_nonneg hvrad hv_memL1 hv_supp h
      hRs hΦc.continuous
  have hDm : IntegrableOn (fun w : X N2 =>
      ∫ u in abox N1 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2) (abox N2 s) volume := by
    exact Integrable.integral_prod_right
      (abox_prod_integrable (N1 := N1) (N2 := N2) s (fun x : X (N1+N2) => (Φ x) ^ 2) hP0)
  have hK : IntegrableOn (fun w : X N2 =>
      ∫ u in abox N1 s, es_kinB1 N1 N2 Φ (mergeBlock N1 N2 (u, w))) (abox N2 s) volume := by
    exact Integrable.integral_prod_right
      (abox_prod_integrable (N1 := N1) (N2 := N2) s (es_kinB1 N1 N2 Φ) hK1)
  have hI : IntegrableOn (fun w : X N2 =>
      ∫ u in abox N1 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2 *
        qLHSden1 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h))
          (mergeBlock N1 N2 (u, w))) (abox N2 s) volume := by
    exact Integrable.integral_prod_right
      (abox_prod_integrable (N1 := N1) (N2 := N2) s
        (fun x : X (N1+N2) => (Φ x) ^ 2 *
          qLHSden1 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) x) hD1)
  have hineq : (∫ w in abox N2 s, E1 *
      (∫ u in abox N1 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2)) ≤
      (∫ w in abox N2 s,
        ((∫ u in abox N1 s, es_kinB1 N1 N2 Φ (mergeBlock N1 N2 (u, w))) +
          (∫ u in abox N1 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2 *
            qLHSden1 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h))
              (mergeBlock N1 N2 (u, w))))) := by
    refine integral_mono ?_ ?_ ?_
    · exact hDm.const_mul E1
    · exact Integrable.add hK hI
    · intro w
      exact sbox_slice1_bound (N1 := N1) (N2 := N2) hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRs
        hμ hΦc w
  have hstep0 : (∫ w in abox N2 s, E1 *
      (∫ u in abox N1 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2))
      = E1 * (∫ x in abox (N1+N2) s, (Φ x) ^ 2) := by
    rw [integral_const_mul]
    congr 1
    exact aboxFubini_swapped (N1 := N1) (N2 := N2) s (fun x : X (N1+N2) => (Φ x) ^ 2) hP0
  have hstepR :
      (∫ w in abox N2 s,
        ((∫ u in abox N1 s, es_kinB1 N1 N2 Φ (mergeBlock N1 N2 (u, w))) +
          (∫ u in abox N1 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2 *
            qLHSden1 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h))
              (mergeBlock N1 N2 (u, w)))))
      = (∫ x in abox (N1+N2) s, es_kinB1 N1 N2 Φ x) +
          (∫ x in abox (N1+N2) s, (Φ x) ^ 2 *
            qLHSden1 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) x) := by
    rw [integral_add hK hI]
    congr 1
    · exact aboxFubini_swapped (N1 := N1) (N2 := N2) s (es_kinB1 N1 N2 Φ) hK1
    · exact aboxFubini_swapped (N1 := N1) (N2 := N2) s
        (fun x : X (N1+N2) => (Φ x) ^ 2 *
          qLHSden1 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) x) hD1
  rw [hstep0, hstepR] at hineq
  rw [← integral_add hK1 hD1] at hineq
  have hE1 : (∫ x in abox (N1+N2) s,
      (es_kinB1 N1 N2 Φ x + (Φ x) ^ 2 *
        qLHSden1 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) x))
      = sboxE1 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
    calc
      (∫ x in abox (N1+N2) s,
          (es_kinB1 N1 N2 Φ x + (Φ x) ^ 2 *
            qLHSden1 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) x))
          = (∫ x in abox (N1+N2) s, es_kinB1 N1 N2 Φ x)
            + (∫ x in abox (N1+N2) s, (Φ x) ^ 2 *
              qLHSden1 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) x) := by
            exact integral_add hK1 hD1
      _ = (∑ i₁ : Fin N1, ∑ k : Fin 3, ∫ x in abox (N1+N2) s,
              (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.castAdd N2 i₁) k)) ^ 2)
            + (∫ x in abox (N1+N2) s, (Φ x) ^ 2 *
              qLHSden1 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) x) := by
            rw [← block1kin_eq_integral_es_kinB1 hs hΦc]
      _ = sboxE1 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
            rfl
  rwa [hE1] at hineq

/-- Per-`u`: the `eB(N2)`-Rayleigh inequality for the second-block slice. -/
lemma sbox_slice2_bound {N1 N2 : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 < μ) {Φ : X (N1+N2) → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) (u : X N1) :
    eB N2 s μ v h *
      (∫ w in abox N2 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2)
      ≤ (∫ w in abox N2 s, es_kinB2 N1 N2 Φ (mergeBlock N1 N2 (u, w)))
        + (∫ w in abox N2 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2 *
            qLHSden2 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h))
              (mergeBlock N1 N2 (u, w))) := by
  have hs2 := sboxE_mul_le_chosen (N := N2) hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRs hμ
    (Φ := sbs_slice2 Φ u) (es_slice2_contDiff hΦc u)
  have hE : sboxE N2 s μ (wPairC s v) (wPairC s (g0 v h)) (sbs_slice2 Φ u)
      = (∫ w in abox N2 s, es_kinB2 N1 N2 Φ (mergeBlock N1 N2 (u, w)))
        + (∫ w in abox N2 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2 *
            qLHSden2 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h))
              (mergeBlock N1 N2 (u, w))) := by
    calc
      sboxE N2 s μ (wPairC s v) (wPairC s (g0 v h)) (sbs_slice2 Φ u)
          = kinWord N2 s (sbs_slice2 Φ u)
              + qLHSword (N := N2) s μ (wPairC s v) (wPairC s (g0 v h)) (sbs_slice2 Φ u) := rfl
      _ = (∫ w in abox N2 s, es_kinAll N2 (sbs_slice2 Φ u) w)
              + qLHSword (N := N2) s μ (wPairC s v) (wPairC s (g0 v h)) (sbs_slice2 Φ u) := by
            rw [kinWord_eq_integral_es_kinAll (N := N2) (s := s) hs (ψ := sbs_slice2 Φ u)
              (es_slice2_contDiff hΦc u)]
      _ = (∫ w in abox N2 s, es_kinAll N2 (sbs_slice2 Φ u) w)
              + ∫ w in abox N2 s, (sbs_slice2 Φ u w) ^ 2 *
                  qLHSden N2 s μ (wPairC s v) (wPairC s (g0 v h)) w := by rfl
      _ = (∫ w in abox N2 s, es_kinB2 N1 N2 Φ (mergeBlock N1 N2 (u, w)))
              + ∫ w in abox N2 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2 *
                  qLHSden N2 s μ (wPairC s v) (wPairC s (g0 v h)) w := by
            congr 1
            apply integral_congr_ae
            filter_upwards with w
            exact (slice2_kinAll_eq hΦc u w)
      _ = (∫ w in abox N2 s, es_kinB2 N1 N2 Φ (mergeBlock N1 N2 (u, w)))
              + ∫ w in abox N2 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2 *
                  qLHSden2 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h))
                    (mergeBlock N1 N2 (u, w)) := by
            congr 1
            apply integral_congr_ae
            filter_upwards with w
            rw [qLHSden2_merge (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) u w]
  have hm : (∫ w in abox N2 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2)
      = ∫ w in abox N2 s, (sbs_slice2 Φ u w) ^ 2 := by
    apply integral_congr_ae
    filter_upwards with w
    rfl
  rw [← hm] at hs2
  rw [hE] at hs2
  exact hs2

/-- Block-2 bound: `eB(N2)·‖Φ‖² ≤ sboxE2` for smooth `Φ` over the merged box. -/
lemma sbox_block2_bound {N1 N2 : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 < μ) {Φ : X (N1+N2) → ℝ}
    (hΦc : ContDiff ℝ ∞ Φ) :
    eB N2 s μ v h * (∫ x in abox (N1+N2) s, (Φ x) ^ 2) ≤
      sboxE2 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
  let E2 := eB N2 s μ v h
  have hP0 : IntegrableOn (fun x : X (N1+N2) => (Φ x) ^ 2) (abox (N1+N2) s) volume :=
    integrableOn_abox_of_continuous hs (hΦc.continuous.pow 2)
  have hK2 : IntegrableOn (es_kinB2 N1 N2 Φ) (abox (N1+N2) s) volume :=
    es_kinB2_integrableOn_abox hs hΦc
  have hD2 : IntegrableOn (fun x : X (N1+N2) => (Φ x) ^ 2 *
      qLHSden2 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) x)
      (abox (N1+N2) s) volume :=
    chosen_qLHSden2_integrableOn (N1 := N1) (N2 := N2) hs hR hv_nonneg hvrad hv_memL1 hv_supp h
      hRs hΦc.continuous
  have hDm : IntegrableOn (fun u : X N1 =>
      ∫ w in abox N2 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2) (abox N1 s) volume := by
    exact Integrable.integral_prod_left
      (abox_prod_integrable (N1 := N1) (N2 := N2) s (fun x : X (N1+N2) => (Φ x) ^ 2) hP0)
  have hK : IntegrableOn (fun u : X N1 =>
      ∫ w in abox N2 s, es_kinB2 N1 N2 Φ (mergeBlock N1 N2 (u, w))) (abox N1 s) volume := by
    exact Integrable.integral_prod_left
      (abox_prod_integrable (N1 := N1) (N2 := N2) s (es_kinB2 N1 N2 Φ) hK2)
  have hI : IntegrableOn (fun u : X N1 =>
      ∫ w in abox N2 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2 *
        qLHSden2 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h))
          (mergeBlock N1 N2 (u, w))) (abox N1 s) volume := by
    exact Integrable.integral_prod_left
      (abox_prod_integrable (N1 := N1) (N2 := N2) s
        (fun x : X (N1+N2) => (Φ x) ^ 2 *
          qLHSden2 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) x) hD2)
  have hineq : (∫ u in abox N1 s, E2 *
      (∫ w in abox N2 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2)) ≤
      (∫ u in abox N1 s,
        ((∫ w in abox N2 s, es_kinB2 N1 N2 Φ (mergeBlock N1 N2 (u, w))) +
          (∫ w in abox N2 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2 *
            qLHSden2 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h))
              (mergeBlock N1 N2 (u, w))))) := by
    refine integral_mono ?_ ?_ ?_
    · exact hDm.const_mul E2
    · exact Integrable.add hK hI
    · intro u
      exact sbox_slice2_bound (N1 := N1) (N2 := N2) hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRs
        hμ hΦc u
  have hstep0 : (∫ u in abox N1 s, E2 *
      (∫ w in abox N2 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2))
      = E2 * (∫ x in abox (N1+N2) s, (Φ x) ^ 2) := by
    rw [integral_const_mul]
    congr 1
    exact aboxFubini (N1 := N1) (N2 := N2) s (fun x : X (N1+N2) => (Φ x) ^ 2) hP0
  have hstepR :
      (∫ u in abox N1 s,
        ((∫ w in abox N2 s, es_kinB2 N1 N2 Φ (mergeBlock N1 N2 (u, w))) +
          (∫ w in abox N2 s, (Φ (mergeBlock N1 N2 (u, w))) ^ 2 *
            qLHSden2 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h))
              (mergeBlock N1 N2 (u, w)))))
      = (∫ x in abox (N1+N2) s, es_kinB2 N1 N2 Φ x) +
          (∫ x in abox (N1+N2) s, (Φ x) ^ 2 *
            qLHSden2 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) x) := by
    rw [integral_add hK hI]
    congr 1
    · exact aboxFubini (N1 := N1) (N2 := N2) s (es_kinB2 N1 N2 Φ) hK2
    · exact aboxFubini (N1 := N1) (N2 := N2) s
        (fun x : X (N1+N2) => (Φ x) ^ 2 *
          qLHSden2 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) x) hD2
  rw [hstep0, hstepR] at hineq
  rw [← integral_add hK2 hD2] at hineq
  have hE2 : (∫ x in abox (N1+N2) s,
      (es_kinB2 N1 N2 Φ x + (Φ x) ^ 2 *
        qLHSden2 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) x))
      = sboxE2 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
    calc
      (∫ x in abox (N1+N2) s,
          (es_kinB2 N1 N2 Φ x + (Φ x) ^ 2 *
            qLHSden2 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) x))
          = (∫ x in abox (N1+N2) s, es_kinB2 N1 N2 Φ x)
            + (∫ x in abox (N1+N2) s, (Φ x) ^ 2 *
              qLHSden2 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) x) := by
            exact integral_add hK2 hD2
      _ = (∑ j₂ : Fin N2, ∑ k : Fin 3, ∫ x in abox (N1+N2) s,
              (fderiv ℝ Φ x (kcDir (N1+N2) (Fin.natAdd N1 j₂) k)) ^ 2)
            + (∫ x in abox (N1+N2) s, (Φ x) ^ 2 *
              qLHSden2 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) x) := by
            rw [← block2kin_eq_integral_es_kinB2 hs hΦc]
      _ = sboxE2 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) Φ := by
            rfl
  rwa [hE2] at hineq

/-- **Per-state inequality**: for every smooth admissible state of `N1+N2`
particles, the sum of the two block ground energies is at most the quotient
of the full small-box energy (mirror of `EneuSuperadd.es_per_state`). -/
lemma sbox_per_state {N1 N2 : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 < μ) (Φ : CSBox (N1+N2) s) :
    eB N1 s μ v h + eB N2 s μ v h ≤
      (sboxE (N1+N2) s μ (wPairC s v) (wPairC s (g0 v h)) (Φ : X (N1+N2) → ℝ)) /
        (∫ x in abox (N1+N2) s, ((Φ : X (N1+N2) → ℝ) x) ^ 2) := by
  let IΦ := ∫ x in abox (N1+N2) s, ((Φ : X (N1+N2) → ℝ) x) ^ 2
  have hφ : ContDiff ℝ ∞ (Φ : X (N1+N2) → ℝ) := Φ.contDiff
  have hb1 := sbox_block1_bound (N1 := N1) (N2 := N2) hR hv_nonneg hvrad hv_memL1 hv_supp h hs
    hRs hμ (Φ := (Φ : X (N1+N2) → ℝ)) hφ
  have hb2 := sbox_block2_bound (N1 := N1) (N2 := N2) hR hv_nonneg hvrad hv_memL1 hv_supp h hs
    hRs hμ (Φ := (Φ : X (N1+N2) → ℝ)) hφ
  have hD1 : IntegrableOn (fun x : X (N1+N2) => ((Φ : X (N1+N2) → ℝ) x) ^ 2 *
      qLHSden1 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) x)
      (abox (N1+N2) s) volume :=
    chosen_qLHSden1_integrableOn (N1 := N1) (N2 := N2) hs hR hv_nonneg hvrad hv_memL1 hv_supp h
      hRs Φ.contDiff.continuous
  have hD2 : IntegrableOn (fun x : X (N1+N2) => ((Φ : X (N1+N2) → ℝ) x) ^ 2 *
      qLHSden2 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) x)
      (abox (N1+N2) s) volume :=
    chosen_qLHSden2_integrableOn (N1 := N1) (N2 := N2) hs hR hv_nonneg hvrad hv_memL1 hv_supp h
      hRs Φ.contDiff.continuous
  have hD : IntegrableOn (fun x : X (N1+N2) => ((Φ : X (N1+N2) → ℝ) x) ^ 2 *
      qLHSden (N1+N2) s μ (wPairC s v) (wPairC s (g0 v h)) x)
      (abox (N1+N2) s) volume :=
    chosen_qLHSden_integrableOn (N := N1+N2) hs hR hv_nonneg hvrad hv_memL1 hv_supp h hRs
      Φ.contDiff.continuous
  have hiii := sboxE_ge_sboxE1_add_sboxE2 (N1 := N1) (N2 := N2) (s := s) (μ := μ)
    (wPairC s v) (wPairC s (g0 v h)) (wPairC_nonneg hv_nonneg s)
    (Φ := (Φ : X (N1+N2) → ℝ)) hφ hD1 hD2 hD
  have hb1' : eB N1 s μ v h * IΦ ≤
      sboxE1 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) (Φ : X (N1+N2) → ℝ) := by
    simpa [IΦ] using hb1
  have hb2' : eB N2 s μ v h * IΦ ≤
      sboxE2 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) (Φ : X (N1+N2) → ℝ) := by
    simpa [IΦ] using hb2
  have hadd : (eB N1 s μ v h + eB N2 s μ v h) * IΦ ≤
      sboxE1 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) (Φ : X (N1+N2) → ℝ)
        + sboxE2 (N1 := N1) (N2 := N2) s μ (wPairC s v) (wPairC s (g0 v h)) (Φ : X (N1+N2) → ℝ) := by
    nlinarith
  have hle : (eB N1 s μ v h + eB N2 s μ v h) * IΦ ≤
      sboxE (N1+N2) s μ (wPairC s v) (wPairC s (g0 v h)) (Φ : X (N1+N2) → ℝ) :=
    le_trans hadd hiii
  have hpos : 0 < IΦ := by
    simpa [IΦ] using Φ.sq_pos
  exact (le_div_iff₀ hpos).mpr hle

/-- Integral of a constant over the centred box: `∫_abox c = c·(s³)ᴺ`. -/
lemma abox_integral_const (N : ℕ) {s : ℝ} (hs : 0 < s) (c : ℝ) :
    (∫ x : X N in abox N s, c) = c * (s ^ 3) ^ N := by
  have h1 : (∫ x : X N in abox N s, c)
      = (((volume : Measure (X N)).restrict (abox N s)).real Set.univ) • c := by
    exact (MeasureTheory.integral_const (μ := (volume : Measure (X N)).restrict (abox N s)) (c := c))
  rw [h1]
  have hm : ((volume : Measure (X N)).restrict (abox N s)).real Set.univ
      = ((volume : Measure (X N)) (abox N s)).toReal := by
    rw [MeasureTheory.measureReal_def, Measure.restrict_apply_univ]
  rw [hm, abox_volume N s hs.le]
  have ht : (ENNReal.ofReal ((s ^ 3) ^ N)).toReal = (s ^ 3) ^ N := by
    exact ENNReal.toReal_ofReal (pow_nonneg (pow_nonneg hs.le 3) N)
  rw [ht]
  ring

/-- The centred-box `L²`-norm of the constant-one state is positive. -/
lemma abox_integral_one_pos {N : ℕ} {s : ℝ} (hs : 0 < s) :
    0 < ∫ x in abox N s, (((1 : X N → ℝ) x) ^ 2) := by
  have hInt : (∫ x in abox N s, (((1 : X N → ℝ) x) ^ 2)) = (s ^ 3) ^ N := by
    calc
      (∫ x in abox N s, (((1 : X N → ℝ) x) ^ 2))
          = ∫ x in abox N s, (1 : ℝ) := by
            apply integral_congr_ae
            filter_upwards with x
            norm_num
      _ = (1 : ℝ) * (s ^ 3) ^ N := abox_integral_const N hs 1
      _ = (s ^ 3) ^ N := by ring
  rw [hInt]
  positivity

/-- A `CSBox` state exists for every particle number and positive side. -/
noncomputable def constCSBox (N : ℕ) {s : ℝ} (hs : 0 < s) : CSBox N s where
  toFun := (1 : X N → ℝ)
  contDiff := contDiff_const
  nezero := by
    intro h
    have hc := congrFun h (0 : X N)
    norm_num at hc
  sq_pos := by
    simpa using (abox_integral_one_pos (N := N) hs)

/-- `CSBox N s` is nonempty for `0 < s`. -/
lemma nonempty_CSBox (N : ℕ) {s : ℝ} (hs : 0 < s) : Nonempty (CSBox N s) :=
  ⟨constCSBox N hs⟩

/-- **`eB` is superadditive in the particle number** (the FS small-box group
trick): `eB(N1+N2) ≥ eB(N1) + eB(N2)` at the fixed chemical potential `μ`. -/
lemma eB_superadd_chosen {N1 N2 : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ} (hR : 0 < R)
    (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 < μ) :
    eB N1 s μ v h + eB N2 s μ v h ≤ eB (N1+N2) s μ v h := by
  haveI : Nonempty (CSBox (N1+N2) s) := nonempty_CSBox (N1+N2) hs
  unfold eB
  exact le_ciInf (fun Φ : CSBox (N1+N2) s =>
    sbox_per_state (N1 := N1) (N2 := N2) hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRs hμ Φ)

end BoseGases

end Submission
