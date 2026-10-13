import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.remov.EllEstUnifStepAux
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.remov.high_chain_sum_self
import Submission.Work.FTS.EllipticEst.TT.HkMem_descend_open
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen
import Submission.Work.FTS.EllipticEst.HkSq_congr_open
import Submission.Work.FTS.EllipticEst.remov.ATop.Tk_le_of_pointwise
import Submission.Work.FTS.LocData.HkMem_of_majorant
import Submission.Work.FTS.EllipticEst.lobAux.HkSqDzTransfer
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-- The shifted mixed slots, at the genuine smooth order: for `f` of class `C^∞` on the open
quadrant and `(z,θ)` in the open quadrant, `D_z^j D_θ^i (D_z f) = D_z^{j+1} D_θ^i f`.
This is `D_z`-commutation with `D_θ^i` (`DthIterDzCommOpen`) followed by
`D_z^j (D_z g) = D_z^{j+1} g` and the local congruence of iterated `D_z` on the open quadrant. -/
theorem mixed_Dz_shift_eq_clean {j i : ℕ} (f : ℝ → ℝ → ℝ) {z θ : ℝ} (hz : 0 < z)
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ = Work.Spaces.mixed (j + 1) i f z θ := by
  have hcomm : Set.EqOn (Function.uncurry (Work.Spaces.Dz (Work.Spaces.DthIter i f)))
      (Function.uncurry (Work.Spaces.DthIter i (Work.Spaces.Dz f))) Step.Qd :=
    Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen f hg i
  have hpt : (z, θ) ∈ Step.Qd := ⟨hz, hθ⟩
  have hcongr : Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
      = Work.Spaces.DzIter j (Work.Spaces.Dz (Work.Spaces.DthIter i f)) z θ :=
    Step.DzIter_congr_of_isOpen Step.isOpen_Qd hcomm.symm j hpt
  show Work.Spaces.DzIter j (Work.Spaces.DthIter i (Work.Spaces.Dz f)) z θ
    = Work.Spaces.DzIter (j + 1) (Work.Spaces.DthIter i f) z θ
  rw [hcongr, Step.DzIter_Dz j (Work.Spaces.DthIter i f)]

/-- **The pointwise `D_z`-shift bound on the open quadrant, at the genuine smooth order.**
Every slot of `HkIntegrand α (k-1) (D_z f)` is a slot of `HkIntegrand α k f` (up to the
commutation of `D_z` with `D_θ^i`), and each single slot is dominated by the whole integrand;
counting `k` radial and `k·k` mixed slots gives the factor `k + k²`. -/
theorem HkIntegrand_Dz_shift_le_clean (α : ℝ) {k : ℕ} (hk : 1 ≤ k) (f : ℝ → ℝ → ℝ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hg : Work.FTS.EllipticEst.SmoothOpen f) :
    Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
  have hHnn : 0 ≤ Work.Spaces.HkIntegrand α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  have hZ : Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
      ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
    have hterm : ∀ i ∈ Finset.range k,
        (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Step.Zu z θ) ^ 2
          ≤ Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hik : i + 1 ≤ k := by
        have := Finset.mem_range.mp hi
        omega
      rw [Step.DzIter_Dz i f]
      exact Work.Spaces.sq_le_HkIntegrand_z α k f z θ (i + 1) hik
    have h1 : Step.Zsum (k - 1) (Work.Spaces.Dz f) z θ
        = ∑ i ∈ Finset.range k,
            (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Step.Zu z θ) ^ 2 := by
      unfold Step.Zsum
      exact Finset.sum_congr (by rw [show k - 1 + 1 = k from by omega])
        (fun i _ => rfl)
    rw [h1]
    calc (∑ i ∈ Finset.range k,
          (Work.Spaces.DzIter i (Work.Spaces.Dz f) z θ * Step.Zu z θ) ^ 2)
        ≤ ∑ _i ∈ Finset.range k, Work.Spaces.HkIntegrand α k f z θ :=
          Finset.sum_le_sum hterm
      _ = (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hM : Step.Msum α (k - 1) (Work.Spaces.Dz f) z θ
      ≤ ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
    rw [Step.Msum_eq_rows, show k - 1 + 1 = k from by omega]
    have hterm : ∀ i ∈ Finset.range k,
        (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ := by
      intro i hi
      have hstep : (∑ j ∈ Finset.range (k - i),
          (if 1 ≤ i then (Work.Spaces.mixed j i (Work.Spaces.Dz f) z θ
            * Work.Spaces.Wt α z θ) ^ 2 else 0))
          ≤ ∑ _j ∈ Finset.range (k - i), Work.Spaces.HkIntegrand α k f z θ := by
        refine Finset.sum_le_sum (fun j hj => ?_)
        by_cases hi1 : 1 ≤ i
        · rw [if_pos hi1]
          rw [mixed_Dz_shift_eq_clean f hz hθ hg]
          have hj' : i + (j + 1) ≤ k := by
            have := Finset.mem_range.mp hj
            omega
          exact Work.Spaces.sq_le_HkIntegrand_mixed α k f z θ i (j + 1) hi1 hj'
        · rw [if_neg hi1]
          exact hHnn
      refine le_trans hstep ?_
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hcast : ((k - i : ℕ) : ℝ) ≤ (k : ℝ) := by
        have : k - i ≤ k := by omega
        exact_mod_cast this
      have hci : (0 : ℝ) ≤ ((k - i : ℕ) : ℝ) := by positivity
      nlinarith [hHnn, hcast, hci]
    refine le_trans (Finset.sum_le_sum hterm) ?_
    have hsum : (∑ _i ∈ Finset.range k, (k : ℝ) * Work.Spaces.HkIntegrand α k f z θ)
        = ((k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    exact hsum.le
  rw [Step.HkIntegrand_eq α k f z θ] at hZ hM ⊢
  rw [Step.HkIntegrand_eq α (k - 1) (Work.Spaces.Dz f) z θ]
  have hnn : 0 ≤ Step.Zsum k f z θ + Step.Msum α k f z θ :=
    Work.Spaces.HkIntegrand_nonneg α k f z θ
  nlinarith [hZ, hM, hnn]


/-- **Membership form of the `D_z`-shift**: if `f` is `C^∞` on the open quadrant and in
`ℋ^k` (`k ≥ 1`), then `D_z f ∈ ℋ^{k-1}`. -/
theorem HkMem_Dz_shift_clean {α : ℝ} {k : ℕ} (hk : 1 ≤ k) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α (k - 1) (Work.Spaces.Dz f) := by
  refine Work.FTS.LocData.HkMem_of_majorant α (k - 1) (f := Work.Spaces.Dz f)
    (M := fun z θ => ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ)
    ?_ ?_ ?_ ?_
  · exact (Work.FTS.EllipticEst.SmoothOpen.Dz hf).continuousOn_HkIntegrand α (k - 1)
  · intro z hz
    exact (hmem.1 z hz).const_mul _
  · show MeasureTheory.Integrable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        ((k : ℝ) + (k : ℝ) * (k : ℝ)) * Work.Spaces.HkIntegrand α k f z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iz)
    simpa only [MeasureTheory.integral_const_mul] using hmem.2.const_mul _
  · intro z hz θ hθ
    have hkey : Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.Dz f) z θ = 0 ∨
        (0 < z ∧ 0 < θ ∧ θ < Real.pi / 2) := by
      by_cases hz0 : z = 0
      · refine Or.inl ?_
        rw [hz0, Work.FTS.EllipticEst.lobAux.HkIntegrand_eq_zero_of_z_eq_zero α (k - 1)
          (Work.Spaces.Dz f) θ]
      · by_cases hθ0 : θ = 0
        · refine Or.inl ?_
          rw [hθ0, Work.FTS.EllipticEst.lobAux.HkIntegrand_eq_zero_of_sin α (k - 1)
            (Work.Spaces.Dz f) (by simp)]
        · by_cases hπ : θ = Real.pi / 2
          · refine Or.inl ?_
            rw [hπ, Work.FTS.EllipticEst.lobAux.HkIntegrand_eq_zero_of_sin α (k - 1)
              (Work.Spaces.Dz f) (by rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi])]
          · exact Or.inr ⟨lt_of_le_of_ne (Set.mem_Ici.mp hz) (Ne.symm hz0),
              lt_of_le_of_ne hθ.1 (Ne.symm hθ0), lt_of_le_of_ne hθ.2 hπ⟩
    rcases hkey with h0 | hpos
    · rw [h0]
      exact mul_nonneg (by positivity) (Work.Spaces.HkIntegrand_nonneg α k f z θ)
    · exact HkIntegrand_Dz_shift_le_clean α hk f hpos.1 ⟨hpos.2.1, hpos.2.2⟩ hf

/-! ## Auxiliaries for the `A`-part of the top angular slot

Everything below is bookkeeping for the proof of `A_top_slot_bound`: the pointwise bound on the
open quadrant of `|D_θ^k (z²∂_z²Ψ)|` by the slots of `D_z(∂_θθΨ)`, `∂_θθΨ` and `z²∂_zzΨ`. -/

/-- The open quadrant. -/
private def QQ : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

private theorem isOpen_QQ : IsOpen QQ := isOpen_Ioi.prod isOpen_Ioo

private theorem mem_QQ {z θ : ℝ} : (z, θ) ∈ QQ ↔ 0 < z ∧ 0 < θ ∧ θ < Real.pi / 2 := by
  simp only [QQ, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo]

private theorem sin_two_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

private theorem sin_two_nonneg_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 ≤ Real.sin (2 * θ) := (sin_two_pos_of_mem hθ).le

/-- The zeroth coefficient of `D_θ^m` vanishes for `m ≥ 1` (both sides are operators with no
zeroth order term). -/
private theorem dthCoef_zero_fun {m : ℕ} (hm : 1 ≤ m) :
    selfdth.dthCoef m 0 = fun _ : ℝ => (0 : ℝ) := by
  induction m with
  | zero => omega
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        funext θ
        show Real.sin (2 * θ) * (deriv (selfdth.dthCoef 0 0) θ
          + (if 1 ≤ 0 then selfdth.dthCoef 0 (0 - 1) θ else 0)) = 0
        simp [selfdth.dthCoef]
      · have h0 := ih hk
        funext θ
        show Real.sin (2 * θ) * (deriv (selfdth.dthCoef k 0) θ
          + (if 1 ≤ 0 then selfdth.dthCoef k (0 - 1) θ else 0)) = 0
        rw [h0]
        simp

private theorem dthCoef_apply_zero {m : ℕ} (hm : 1 ≤ m) (θ : ℝ) :
    selfdth.dthCoef m 0 θ = 0 := congrFun (dthCoef_zero_fun hm) θ

/-! ## The sharpened reverse expansion

`D_θ^m = Σ_{r ≤ m} a_{m,r} ∂_θ^r` with `a_{m,0} = 0` for `m ≥ 1` gives, on solving for the top
term, the *reverse* expansion without any zeroth-order term. -/

/-- **Sharpened reverse expansion.**  For every `m` there is `C > 0` such that for every `f` which
is `C^∞` at the point `(z,θ)` and every `θ ∈ (0,π/2)`,

  `sin(2θ)^m |∂_θ^m f(z,θ)| ≤ C (|D_θ^m f(z,θ)| + Σ_{1 ≤ r < m} sin(2θ)^r |∂_θ^r f(z,θ)|)`.

The point is the absence of the `r = 0` term, which is what `a_{m,0} = 0` buys. -/
private theorem sharp_reverse (m : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ → ℝ) (z θ : ℝ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry f) (z, θ)) →
      (Real.sin (2 * θ)) ^ m * |Work.Spaces.pthIter m f z θ|
        ≤ C * (|Work.Spaces.DthIter m f z θ|
            + ∑ r ∈ Finset.Icc 1 (m - 1),
                (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r f z θ|) := by
  classical
  choose K hKpos hKbd using fun r => selfdth.DthCoef_sin_pow_bound m r
  have hKnn : (0 : ℝ) ≤ ∑ r ∈ Finset.range (m + 1), K r :=
    Finset.sum_nonneg fun i _ => (hKpos i).le
  refine ⟨1 + ∑ r ∈ Finset.range (m + 1), K r, by linarith, fun f z θ hθ hf => ?_⟩
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem hθ
  have hexp := selfdth.DthIter_expansion_local m f z θ hf
  have hself : selfdth.dthCoef m m θ = (Real.sin (2 * θ)) ^ m :=
    congrFun (selfdth.dthCoef_self m) θ
  have hsplit : (Real.sin (2 * θ)) ^ m * Work.Spaces.pthIter m f z θ
      = Work.Spaces.DthIter m f z θ
        - ∑ r ∈ Finset.range m,
            selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ := by
    rw [hexp, Finset.sum_range_succ, hself]
    ring
  have habs : |(Real.sin (2 * θ)) ^ m * Work.Spaces.pthIter m f z θ|
      = (Real.sin (2 * θ)) ^ m * |Work.Spaces.pthIter m f z θ| := by
    rw [abs_mul, abs_of_nonneg (pow_nonneg hs.le m)]
  rw [← habs, hsplit]
  have htri : |Work.Spaces.DthIter m f z θ
        - ∑ r ∈ Finset.range m,
            selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ|
      ≤ |Work.Spaces.DthIter m f z θ|
        + ∑ r ∈ Finset.range m,
            |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ| := by
    have h1 : |Work.Spaces.DthIter m f z θ
          - ∑ r ∈ Finset.range m,
              selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ|
        ≤ |Work.Spaces.DthIter m f z θ|
          + |∑ r ∈ Finset.range m,
              selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ| := by
      simpa using abs_sub_le (Work.Spaces.DthIter m f z θ) 0
        (∑ r ∈ Finset.range m,
          selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ)
    have h2 : |∑ r ∈ Finset.range m,
          selfdth.dthCoef m r θ * Work.Spaces.pthIter r f z θ|
        ≤ ∑ r ∈ Finset.range m,
            |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ| := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      exact le_of_eq (Finset.sum_congr rfl fun r _ => abs_mul _ _)
    exact le_trans h1 (add_le_add le_rfl h2)
  refine le_trans htri ?_
  have h0 : (∑ r ∈ Finset.range m,
        |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ|)
      = ∑ r ∈ Finset.Icc 1 (m - 1),
          |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ| := by
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · subst hm0; simp
    · have hmem : 0 ∈ Finset.range m := Finset.mem_range.mpr hmpos
      have hset : (Finset.range m).erase 0 = Finset.Icc 1 (m - 1) := by
        ext r
        simp only [Finset.mem_erase, Finset.mem_range, Finset.mem_Icc]
        omega
      have h1 : (∑ r ∈ (Finset.range m).erase 0,
            |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ|)
          + |selfdth.dthCoef m 0 θ| * |Work.Spaces.pthIter 0 f z θ|
          = ∑ r ∈ Finset.range m,
            |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ| :=
        Finset.sum_erase_add (Finset.range m)
          (fun r => |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ|) hmem
      rw [hset, dthCoef_apply_zero hmpos] at h1
      simp only [abs_zero, zero_mul, add_zero] at h1
      exact h1.symm
  rw [h0]
  have hb : ∀ r ∈ Finset.Icc 1 (m - 1),
      |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ|
        ≤ (1 + ∑ i ∈ Finset.range (m + 1), K i)
          * ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r f z θ|) := by
    intro r hr
    obtain ⟨hr1, hrle⟩ := Finset.mem_Icc.mp hr
    have hr' : r ∈ Finset.range (m + 1) := Finset.mem_range.mpr (by omega)
    have hKle : K r ≤ 1 + ∑ i ∈ Finset.range (m + 1), K i := by
      have := Finset.single_le_sum (fun i _ => (hKpos i).le) hr'
      linarith
    have hbb := hKbd r θ
    rw [abs_of_pos hs] at hbb
    have hspow : 0 ≤ (Real.sin (2 * θ)) ^ r := pow_nonneg hs.le r
    calc |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ|
        ≤ (K r * (Real.sin (2 * θ)) ^ r) * |Work.Spaces.pthIter r f z θ| := by
          exact mul_le_mul_of_nonneg_right hbb (abs_nonneg _)
      _ = K r * ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r f z θ|) := by ring
      _ ≤ (1 + ∑ i ∈ Finset.range (m + 1), K i)
            * ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r f z θ|) :=
          mul_le_mul_of_nonneg_right hKle (mul_nonneg hspow (abs_nonneg _))
  calc |Work.Spaces.DthIter m f z θ|
        + ∑ r ∈ Finset.Icc 1 (m - 1),
            |selfdth.dthCoef m r θ| * |Work.Spaces.pthIter r f z θ|
      ≤ |Work.Spaces.DthIter m f z θ|
        + ∑ r ∈ Finset.Icc 1 (m - 1),
            (1 + ∑ i ∈ Finset.range (m + 1), K i)
              * ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r f z θ|) :=
        add_le_add le_rfl (Finset.sum_le_sum hb)
    _ ≤ (1 + ∑ i ∈ Finset.range (m + 1), K i)
          * (|Work.Spaces.DthIter m f z θ|
            + ∑ r ∈ Finset.Icc 1 (m - 1),
                (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r f z θ|) := by
        have h1 : (1 : ℝ) ≤ 1 + ∑ i ∈ Finset.range (m + 1), K i := by linarith
        have hA : |Work.Spaces.DthIter m f z θ|
            ≤ (1 + ∑ i ∈ Finset.range (m + 1), K i) * |Work.Spaces.DthIter m f z θ| :=
          le_mul_of_one_le_left (abs_nonneg _) h1
        have hB : ∑ r ∈ Finset.Icc 1 (m - 1),
            (1 + ∑ i ∈ Finset.range (m + 1), K i)
              * ((Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r f z θ|)
            = (1 + ∑ i ∈ Finset.range (m + 1), K i)
              * ∑ r ∈ Finset.Icc 1 (m - 1),
                  (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r f z θ| := by
          rw [Finset.mul_sum]
        rw [hB]
        linarith [hA]

/-- **Elimination of the lower order terms.**  For `m ≥ 1` there is `C > 0` such that for every
`f` which is `C^∞` at `(z,θ)` and every `θ ∈ (0,π/2)`,

  `sin(2θ)^m |∂_θ^m f(z,θ)| ≤ C Σ_{1 ≤ q ≤ m} |D_θ^q f(z,θ)|`. -/
private theorem elimination (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ → ℝ) (z θ : ℝ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry f) (z, θ)) →
      (Real.sin (2 * θ)) ^ m * |Work.Spaces.pthIter m f z θ|
        ≤ C * ∑ q ∈ Finset.Icc 1 m, |Work.Spaces.DthIter q f z θ| := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    obtain ⟨C, hCpos, hC⟩ := sharp_reverse m
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · -- `m = 1`
      have hm1 : m = 1 := by omega
      subst hm1
      refine ⟨C, hCpos, fun f z θ hθ hf => ?_⟩
      have h := hC f z θ hθ hf
      have h0 : (∑ r ∈ Finset.Icc 1 (1 - 1),
          (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r f z θ|) = 0 := by
        rw [show (Finset.Icc 1 (1 - 1)) = (∅ : Finset ℕ) from by decide, Finset.sum_empty]
      rw [h0, add_zero] at h
      have h1 : (∑ q ∈ Finset.Icc 1 1, |Work.Spaces.DthIter q f z θ|)
          = |Work.Spaces.DthIter 1 f z θ| := by
        rw [show (Finset.Icc 1 1) = ({1} : Finset ℕ) from by decide, Finset.sum_singleton]
      rw [h1]
      simpa using h
    · -- `m ≥ 2`: use the sharpened reverse bound and the induction hypothesis
      have hfac : ∀ r : ℕ, ∃ Cr : ℝ, 0 < Cr ∧ (r ∈ Finset.Icc 1 (m - 1) →
          ∀ (f : ℝ → ℝ → ℝ) (z θ : ℝ), θ ∈ Set.Ioo 0 (Real.pi / 2) →
            (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry f) (z, θ)) →
            (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r f z θ|
              ≤ Cr * ∑ q ∈ Finset.Icc 1 m, |Work.Spaces.DthIter q f z θ|) := by
        intro r
        by_cases hr : r ∈ Finset.Icc 1 (m - 1)
        · obtain ⟨hr1, hrle⟩ := Finset.mem_Icc.mp hr
          have hrm : r < m := by omega
          obtain ⟨Cr, hCrpos, hCr⟩ := ih r hrm hr1
          refine ⟨Cr, hCrpos, fun _ f z θ hθ hf => ?_⟩
          have hsub : Finset.Icc 1 r ⊆ Finset.Icc 1 m := by
            intro q hq
            obtain ⟨hq1, hqr⟩ := Finset.mem_Icc.mp hq
            exact Finset.mem_Icc.mpr ⟨hq1, by omega⟩
          have hmono : (∑ q ∈ Finset.Icc 1 r, |Work.Spaces.DthIter q f z θ|)
              ≤ ∑ q ∈ Finset.Icc 1 m, |Work.Spaces.DthIter q f z θ| :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun q _ _ => abs_nonneg _)
          exact le_trans (hCr f z θ hθ hf) (mul_le_mul_of_nonneg_left hmono hCrpos.le)
        · exact ⟨1, one_pos, fun h => absurd h hr⟩
      choose C' hC'pos hC' using hfac
      have hC'nn : (0 : ℝ) ≤ ∑ r ∈ Finset.Icc 1 (m - 1), C' r :=
        Finset.sum_nonneg fun r _ => (hC'pos r).le
      refine ⟨C * (1 + ∑ r ∈ Finset.Icc 1 (m - 1), C' r),
        by nlinarith [hCpos, hC'nn], fun f z θ hθ hf => ?_⟩
      have h := hC f z θ hθ hf
      have hb : ∑ r ∈ Finset.Icc 1 (m - 1), (Real.sin (2 * θ)) ^ r
            * |Work.Spaces.pthIter r f z θ|
          ≤ (∑ r ∈ Finset.Icc 1 (m - 1), C' r)
              * ∑ q ∈ Finset.Icc 1 m, |Work.Spaces.DthIter q f z θ| := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun r hr => hC' r hr f z θ hθ hf
      have hDm : |Work.Spaces.DthIter m f z θ|
          ≤ ∑ q ∈ Finset.Icc 1 m, |Work.Spaces.DthIter q f z θ| := by
        have hm' : m ∈ Finset.Icc 1 m := Finset.mem_Icc.mpr ⟨hm, le_refl m⟩
        exact Finset.single_le_sum (s := Finset.Icc 1 m)
          (f := fun q => |Work.Spaces.DthIter q f z θ|) (fun q _ => abs_nonneg _) hm'
      calc (Real.sin (2 * θ)) ^ m * |Work.Spaces.pthIter m f z θ|
          ≤ C * (|Work.Spaces.DthIter m f z θ|
              + ∑ r ∈ Finset.Icc 1 (m - 1), (Real.sin (2 * θ)) ^ r
                  * |Work.Spaces.pthIter r f z θ|) := h
        _ ≤ C * ((∑ q ∈ Finset.Icc 1 m, |Work.Spaces.DthIter q f z θ|)
              + (∑ r ∈ Finset.Icc 1 (m - 1), C' r)
                * ∑ q ∈ Finset.Icc 1 m, |Work.Spaces.DthIter q f z θ|) :=
            mul_le_mul_of_nonneg_left (add_le_add hDm hb) hCpos.le
        _ = C * (1 + ∑ r ∈ Finset.Icc 1 (m - 1), C' r)
              * ∑ q ∈ Finset.Icc 1 m, |Work.Spaces.DthIter q f z θ| := by ring

/-! ## Iterated derivatives: coefficient extraction, congruence, commutation

The next lemmas are the pointwise calculus needed to compare the weighted slots of the
`ℋ^k`-integrands with the plain `θ`-derivatives appearing in the expansion of `D_θ^k`. -/

/-- Two functions agree on the open quadrant. -/
private def EqQ (f g : ℝ → ℝ → ℝ) : Prop := ∀ z θ : ℝ, (z, θ) ∈ QQ → f z θ = g z θ

/-- Extracting a `z`-dependent coefficient from the iterated `θ`-derivative. -/
private theorem pthIter_const_mul_z (m : ℕ) (c : ℝ → ℝ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter m (fun z θ => c z * g z θ)
      = fun z θ => c z * Work.Spaces.pthIter m g z θ := by
  induction m with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]
      funext z θ
      show deriv (fun θ' => c z * Work.Spaces.pthIter k g z θ') θ
        = c z * deriv (fun θ' => Work.Spaces.pthIter k g z θ') θ
      rw [deriv_const_mul_field]

/-- `pthIter (m+n) f = pthIter m (pthIter n f)`. -/
private theorem pthIter_add' (m n : ℕ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.pthIter (m + n) f = Work.Spaces.pthIter m (Work.Spaces.pthIter n f) := by
  induction m with
  | zero => simp
  | succ k ih =>
      rw [Nat.succ_add, Work.Spaces.pthIter_succ, ih, Work.Spaces.pthIter_succ]

/-- Extracting a `θ`-dependent coefficient from the plain `z`-derivative. -/
private theorem pz_const_mul_th (a : ℝ → ℝ) (h : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pz (fun z θ => a θ * h z θ) z θ = a θ * Work.Spaces.pz h z θ := by
  show deriv (fun z' => a θ * h z' θ) z = a θ * deriv (fun z' => h z' θ) z
  rw [deriv_const_mul_field]

/-- `z² ∂_z² Φ = D_z² Φ - D_z Φ`, at a point where the `z`-slice of `∂_z Φ` is differentiable. -/
private theorem zsq_pzIter2_eq (Φ : ℝ → ℝ → ℝ) {z θ : ℝ}
    (h : DifferentiableAt ℝ (fun z' => Work.Spaces.pz Φ z' θ) z) :
    z ^ 2 * Work.Spaces.pzIter 2 Φ z θ
      = Work.Spaces.DzIter 2 Φ z θ - Work.Spaces.DzIter 1 Φ z θ := by
  have heq : (fun z' : ℝ => z' * Work.Spaces.pz Φ z' θ)
      = id * (fun z' => Work.Spaces.pz Φ z' θ) := rfl
  have hd : deriv (id * (fun z' => Work.Spaces.pz Φ z' θ)) z
      = 1 * Work.Spaces.pz Φ z θ + z * Work.Spaces.pzIter 2 Φ z θ := by
    rw [deriv_mul differentiableAt_id h, deriv_id]
    rfl
  rw [show Work.Spaces.DzIter 2 Φ z θ
        = z * deriv (id * (fun z' => Work.Spaces.pz Φ z' θ)) z from by
      show z * deriv (fun z' => z' * Work.Spaces.pz Φ z' θ) z = _
      rw [heq],
    show Work.Spaces.DzIter 1 Φ z θ = z * Work.Spaces.pz Φ z θ from rfl, hd]
  ring

/-! ## Congruence on the open quadrant -/

private theorem pth_congr_QQ {f g : ℝ → ℝ → ℝ} (h : EqQ f g) {z θ : ℝ} (hz : (z, θ) ∈ QQ) :
    Work.Spaces.pth f z θ = Work.Spaces.pth g z θ := by
  have hnb : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ QQ :=
    (Continuous.prodMk_right z).continuousAt.eventually (isOpen_QQ.mem_nhds hz)
  have hslice : (fun θ' => f z θ') =ᶠ[𝓝 θ] (fun θ' => g z θ') := by
    filter_upwards [hnb] with θ' hθ'
    exact h z θ' hθ'
  have hder := hslice.deriv_eq
  simpa only [Work.Spaces.pth] using hder

private theorem pz_congr_QQ {f g : ℝ → ℝ → ℝ} (h : EqQ f g) {z θ : ℝ} (hz : (z, θ) ∈ QQ) :
    Work.Spaces.pz f z θ = Work.Spaces.pz g z θ := by
  have hnb : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ QQ :=
    (Continuous.prodMk_left θ).continuousAt.eventually (isOpen_QQ.mem_nhds hz)
  have hslice : (fun z' => f z' θ) =ᶠ[𝓝 z] (fun z' => g z' θ) := by
    filter_upwards [hnb] with z' hz'
    exact h z' θ hz'
  have hder := hslice.deriv_eq
  simpa only [Work.Spaces.pz] using hder

private theorem Dth_congr_QQ {f g : ℝ → ℝ → ℝ} (h : EqQ f g) {z θ : ℝ} (hz : (z, θ) ∈ QQ) :
    Work.Spaces.Dth f z θ = Work.Spaces.Dth g z θ :=
  congrArg (fun t => Real.sin (2 * θ) * t) (pth_congr_QQ h hz)

private theorem pthIter_congr_QQ (m : ℕ) {f g : ℝ → ℝ → ℝ} (h : EqQ f g) :
    EqQ (Work.Spaces.pthIter m f) (Work.Spaces.pthIter m g) := by
  induction m with
  | zero => exact h
  | succ k ih => intro z θ hz; exact pth_congr_QQ ih hz

private theorem pzIter_congr_QQ (m : ℕ) {f g : ℝ → ℝ → ℝ} (h : EqQ f g) :
    EqQ (Work.Spaces.pzIter m f) (Work.Spaces.pzIter m g) := by
  induction m with
  | zero => exact h
  | succ k ih => intro z θ hz; exact pz_congr_QQ ih hz

private theorem DthIter_congr_QQ (m : ℕ) {f g : ℝ → ℝ → ℝ} (h : EqQ f g) :
    EqQ (Work.Spaces.DthIter m f) (Work.Spaces.DthIter m g) := by
  induction m with
  | zero => exact h
  | succ k ih => intro z θ hz; exact Dth_congr_QQ ih hz

/-! ## Smoothness of the iterates on the open quadrant -/

private theorem pthIter_smooth {G : ℝ → ℝ → ℝ} (hG : SmoothOpen G) (m : ℕ) :
    SmoothOpen (Work.Spaces.pthIter m G) := by
  induction m with
  | zero => simpa using hG
  | succ k ih => rw [Work.Spaces.pthIter_succ]; exact ih.pth

private theorem zsq_pzIter2_smooth {G : ℝ → ℝ → ℝ} (hG : SmoothOpen G) :
    SmoothOpen (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 G z θ) := by
  have h1 : SmoothOpen (Work.Spaces.pzIter 2 G) := hG.pzIter 2
  have h2 : ContDiffOn ℝ Work.Stability.smoothOrder (fun p : ℝ × ℝ => p.1 ^ 2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by fun_prop
  exact h2.mul h1

/-! ## Commutation of the `θ`-derivatives with the `z`-derivatives -/

private theorem pz_pth_comm_pt {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ)) :
    Work.Spaces.pz (Work.Spaces.pth f) z θ = Work.Spaces.pth (Work.Spaces.pz f) z θ :=
  Work.Spaces.pz_pth_comm h

private theorem pth_pz_comm_pt {f : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ)) :
    Work.Spaces.pth (Work.Spaces.pz f) z θ = Work.Spaces.pz (Work.Spaces.pth f) z θ :=
  (pz_pth_comm_pt h).symm

/-- `∂_θ` commutes with `D_z = z∂_z`. -/
private theorem pth_Dz_comm_pt {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ)) :
    Work.Spaces.pth (Work.Spaces.Dz g) z θ = Work.Spaces.Dz (Work.Spaces.pth g) z θ := by
  have hz : Work.Spaces.pth (Work.Spaces.Dz g) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz g) z θ := by
    show deriv (fun θ' => z * Work.Spaces.pz g z θ') θ
      = z * Work.Spaces.pth (Work.Spaces.pz g) z θ
    rw [deriv_const_mul_field]
    rw [show Work.Spaces.pth (Work.Spaces.pz g) z θ
        = deriv (fun θ' => Work.Spaces.pz g z θ') θ from rfl]
  rw [hz, pth_pz_comm_pt h]
  rfl

/-- `D_θ` commutes with `∂_z`. -/
private theorem Dth_pz_comm_pt {g : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ContDiffAt ℝ 2 (Function.uncurry g) (z, θ)) :
    Work.Spaces.Dth (Work.Spaces.pz g) z θ = Work.Spaces.pz (Work.Spaces.Dth g) z θ := by
  have h1 : Work.Spaces.Dth (Work.Spaces.pz g) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.pz g) z θ := rfl
  have h2 : Work.Spaces.pz (Work.Spaces.Dth g) z θ
      = Real.sin (2 * θ) * Work.Spaces.pz (Work.Spaces.pth g) z θ :=
    pz_const_mul_th (fun θ => Real.sin (2 * θ)) (Work.Spaces.pth g) z θ
  rw [h1, pth_pz_comm_pt h, h2]

/-- `∂_θ^m` commutes with `∂_z` on the open quadrant. -/
private theorem pthIter_pz_comm_QQ (m : ℕ) {G : ℝ → ℝ → ℝ} (hG : SmoothOpen G) :
    EqQ (Work.Spaces.pthIter m (Work.Spaces.pz G)) (Work.Spaces.pz (Work.Spaces.pthIter m G)) := by
  induction m with
  | zero => intro z θ _; rfl
  | succ k ih =>
      intro z θ hy
      rw [Work.Spaces.pthIter_succ, pth_congr_QQ ih hy]
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pthIter k G)) (z, θ) :=
        ((pthIter_smooth hG k).forall 2).contDiffAt (isOpen_QQ.mem_nhds hy)
      rw [pth_pz_comm_pt hcd]
      rfl

/-- `D_θ` commutes with `∂_z^j` on the open quadrant. -/
private theorem Dth_pzIter_comm_QQ (j : ℕ) {G : ℝ → ℝ → ℝ} (hG : SmoothOpen G) :
    EqQ (Work.Spaces.Dth (Work.Spaces.pzIter j G))
      (Work.Spaces.pzIter j (Work.Spaces.Dth G)) := by
  induction j with
  | zero => intro z θ _; rfl
  | succ k ih =>
      intro z θ hy
      rw [Work.Spaces.pzIter_succ,
        Dth_pz_comm_pt (((hG.pzIter k).forall 2).contDiffAt (isOpen_QQ.mem_nhds hy)),
        pz_congr_QQ ih hy]
      rfl

/-- `D_θ^m` commutes with `∂_z^j` on the open quadrant. -/
private theorem DthIter_pzIter_comm_QQ (m j : ℕ) {G : ℝ → ℝ → ℝ} (hG : SmoothOpen G) :
    EqQ (Work.Spaces.DthIter m (Work.Spaces.pzIter j G))
      (Work.Spaces.pzIter j (Work.Spaces.DthIter m G)) := by
  induction m with
  | zero => intro z θ _; rfl
  | succ k ih =>
      intro z θ hy
      rw [Work.Spaces.DthIter_succ, Dth_congr_QQ ih hy,
        Dth_pzIter_comm_QQ j (hG.DthIter k) z θ hy]
      rfl

/-- `∂_θ^m` commutes with `∂_z^j` on the open quadrant. -/
private theorem pthIter_pzIter_comm_QQ (m j : ℕ) {G : ℝ → ℝ → ℝ} (hG : SmoothOpen G) :
    EqQ (Work.Spaces.pthIter m (Work.Spaces.pzIter j G))
      (Work.Spaces.pzIter j (Work.Spaces.pthIter m G)) := by
  induction j with
  | zero => intro z θ _; rfl
  | succ k ih =>
      intro z θ hy
      rw [Work.Spaces.pzIter_succ, pthIter_pz_comm_QQ m (hG.pzIter k) z θ hy,
        pz_congr_QQ ih hy]
      rfl

/-! ## Two elementary summation bounds -/

/-- `(Σ f i)² ≤ card(s)² T` when each `f i² ≤ T`. -/
private theorem sq_sum_le_card_sq_mul {s : Finset ℕ} {f : ℕ → ℝ} {T : ℝ} (hT : 0 ≤ T)
    (hf : ∀ i ∈ s, (f i) ^ 2 ≤ T) : (∑ i ∈ s, f i) ^ 2 ≤ ((s.card : ℝ)) ^ 2 * T := by
  have h1 : (∑ i ∈ s, f i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have h2 : (∑ i ∈ s, (f i) ^ 2) ≤ (s.card : ℝ) * T := by
    calc (∑ i ∈ s, (f i) ^ 2) ≤ ∑ _i ∈ s, T := Finset.sum_le_sum hf
      _ = (s.card : ℝ) * T := by rw [Finset.sum_const, nsmul_eq_mul]
  have h3 : (s.card : ℝ) * ∑ i ∈ s, (f i) ^ 2 ≤ (s.card : ℝ) * ((s.card : ℝ) * T) :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : (s.card : ℝ) * ((s.card : ℝ) * T) = ((s.card : ℝ)) ^ 2 * T := by ring
  linarith [h1, h3]

/-- A crude bound for the cardinality of `Icc a b`. -/
private theorem card_Icc_le (a b C : ℕ) (h : b < C) : ((Finset.Icc a b).card : ℝ) ≤ (C : ℝ) := by
  have h1 : (Finset.Icc a b).card ≤ C := by
    have := Finset.card_le_card (s := Finset.Icc a b) (t := Finset.range C)
      (fun x hx => by
        obtain ⟨hx1, hx2⟩ := Finset.mem_Icc.mp hx
        exact Finset.mem_range.mpr (by omega))
    simpa [Finset.card_range] using this
  exact_mod_cast h1

/-! ## The pointwise bound on the open quadrant

Write `A = z²∂_z²Ψ` and `B = ∂_θθΨ`.  On the open quadrant the exact expansion of `D_θ^k` gives
`D_θ^k A = Σ_{r ≤ k} a_{k,r}(θ) ∂_θ^r A`, with `a_{k,0} = 0` and `|a_{k,r}| ≤ K sin(2θ)^r`.  Each
term is compared with slots of the two `ℋ^{k-1}`-integrands of `A` and of `D_z B`:

* for `1 ≤ r ≤ k-1` the elimination of the lower order terms applied to `A` gives
  `sin(2θ)^r |∂_θ^r A| ≤ C Σ_{1 ≤ q ≤ r} |D_θ^q A|`;
* for `r = k` one writes `∂_θ^k A = z²∂_z²(∂_θ^kΨ) = z²D_θ^{k-2}∂_z²B` and applies the
  elimination to `∂_z²B`, whose `D_θ^q`-derivatives are the slots of `D_z B`. -/

/-- **The pointwise bound**: on the open quadrant, `(D_θ^k A · Wt)²` is dominated by the sum of
the two `ℋ^{k-1}`-integrands of `A` and of `D_z B`. -/
private theorem A_top_pointwise (k : ℕ) (hk : 3 ≤ k) :
    ∃ K : ℝ, 0 < K ∧ ∀ (α : ℝ) (Ψ : ℝ → ℝ → ℝ), SmoothOpen Ψ → ∀ z θ : ℝ, (z, θ) ∈ QQ →
      (Work.Spaces.DthIter k (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          * Work.Spaces.Wt α z θ) ^ 2
        ≤ K * (Work.Spaces.HkIntegrand α (k - 1)
              (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
            + Work.Spaces.HkIntegrand α (k - 1)
              (Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ)) z θ) := by
  classical
  choose Kc hKcpos hKcbd using fun r => selfdth.DthCoef_sin_pow_bound k r
  have hKcNn : (0 : ℝ) ≤ ∑ r ∈ Finset.range (k + 1), Kc r :=
    Finset.sum_nonneg fun r _ => (hKcpos r).le
  have hE : ∀ m : ℕ, ∃ C : ℝ, 0 < C ∧ (1 ≤ m → ∀ (f : ℝ → ℝ → ℝ) (z θ : ℝ),
      θ ∈ Set.Ioo 0 (Real.pi / 2) →
      (∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry f) (z, θ)) →
      (Real.sin (2 * θ)) ^ m * |Work.Spaces.pthIter m f z θ|
        ≤ C * ∑ q ∈ Finset.Icc 1 m, |Work.Spaces.DthIter q f z θ|) := by
    intro m
    by_cases hm : 1 ≤ m
    · obtain ⟨C, hCpos, hC⟩ := elimination m hm
      exact ⟨C, hCpos, fun _ => hC⟩
    · exact ⟨1, one_pos, fun h => absurd h hm⟩
  choose Ce hCepos hCe using hE
  have hCeNn : (0 : ℝ) ≤ ∑ m ∈ Finset.Icc 1 (k - 1), Ce m :=
    Finset.sum_nonneg fun m _ => (hCepos m).le
  set Km : ℝ := (∑ r ∈ Finset.range (k + 1), Kc r) + 1 with hKm
  set Ke : ℝ := (∑ m ∈ Finset.Icc 1 (k - 1), Ce m) + 1 with hKe
  have hKm1 : 1 ≤ Km := by rw [hKm]; linarith
  have hKe1 : 1 ≤ Ke := by rw [hKe]; linarith
  have hKmnn : 0 ≤ Km := le_trans zero_le_one hKm1
  have hKenn : 0 ≤ Ke := le_trans zero_le_one hKe1
  refine ⟨(((k : ℝ) + 3) ^ 4 * (Km * Ke) ^ 2 * 16) + 1, by positivity, ?_⟩
  intro α Ψ hΨ z θ hz
  have hθ : θ ∈ Set.Ioo 0 (Real.pi / 2) := hz.2
  have hs : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem hθ
  have hspos : 0 ≤ Real.sin (2 * θ) := hs.le
  have hwt : 0 ≤ Work.Spaces.Wt α z θ := by
    rw [Work.Spaces.Wt, Work.Spaces.w, Work.Spaces.wTheta]
    refine mul_nonneg (div_nonneg (by positivity) (by positivity)) ?_
    exact Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1],
      by linarith [hθ.2, Real.pi_pos]⟩) _
  set A : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ with hAdef
  set B : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ with hBdef
  have hA_sm : SmoothOpen A := zsq_pzIter2_smooth hΨ
  have hB_sm : SmoothOpen B := pthIter_smooth hΨ 2
  have hAcd : ∀ n : ℕ, ContDiffAt ℝ n (Function.uncurry A) (z, θ) :=
    fun n => (hA_sm.forall n).contDiffAt (isOpen_QQ.mem_nhds hz)
  have hB2cd : ∀ n : ℕ, ContDiffAt ℝ n
      (Function.uncurry (Work.Spaces.pzIter 2 B)) (z, θ) :=
    fun n => ((hB_sm.pzIter 2).forall n).contDiffAt (isOpen_QQ.mem_nhds hz)
  set HA : ℝ := Work.Spaces.HkIntegrand α (k - 1) A z θ with hHA
  set HB : ℝ := Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.DzIter 1 B) z θ with hHB
  have hHAnn : 0 ≤ HA := Work.Spaces.HkIntegrand_nonneg α (k - 1) A z θ
  have hHBnn : 0 ≤ HB := Work.Spaces.HkIntegrand_nonneg α (k - 1) (Work.Spaces.DzIter 1 B) z θ
  -- slots of `A`
  have hslotA : ∀ q ∈ Finset.Icc 1 (k - 1),
      (Work.Spaces.DthIter q A z θ * Work.Spaces.Wt α z θ) ^ 2 ≤ HA := by
    intro q hq
    obtain ⟨hq1, hqk⟩ := Finset.mem_Icc.mp hq
    have h1 : (Work.Spaces.mixed 0 q A z θ * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α (k - 1) A z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α (k - 1) A z θ q 0 hq1 (by omega)
    rw [Work.Spaces.mixed_zero_left] at h1
    rw [hHA]
    exact h1
  -- slots of `D_z B`
  have hcommDz : ∀ (q : ℕ) (z' θ' : ℝ), (z', θ') ∈ QQ →
      Work.Spaces.DthIter q (Work.Spaces.DzIter 1 B) z' θ'
        = Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z' θ' := fun q z' θ' hz' =>
    (Work.FTS.EllipticEst.DzAmgm.DthIterDzCommOpen B hB_sm q
      (show (z', θ') ∈ Work.FTS.EllipticEst.Q0 from hz')).symm
  have hslotB1 : ∀ q ∈ Finset.Icc 1 (k - 2),
      (Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ) ^ 2 ≤ HB := by
    intro q hq
    obtain ⟨hq1, hqk⟩ := Finset.mem_Icc.mp hq
    have h1 : (Work.Spaces.mixed 0 q (Work.Spaces.DzIter 1 B) z θ
        * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.DzIter 1 B) z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α (k - 1) (Work.Spaces.DzIter 1 B) z θ q 0 hq1
        (by omega)
    rw [Work.Spaces.mixed_zero_left, hcommDz q z θ hz] at h1
    rw [hHB]
    exact h1
  have hslotB2 : ∀ q ∈ Finset.Icc 1 (k - 2),
      (Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ) ^ 2 ≤ HB := by
    intro q hq
    obtain ⟨hq1, hqk⟩ := Finset.mem_Icc.mp hq
    have h1 : (Work.Spaces.mixed 1 q (Work.Spaces.DzIter 1 B) z θ
        * Work.Spaces.Wt α z θ) ^ 2
        ≤ Work.Spaces.HkIntegrand α (k - 1) (Work.Spaces.DzIter 1 B) z θ :=
      Work.Spaces.sq_le_HkIntegrand_mixed α (k - 1) (Work.Spaces.DzIter 1 B) z θ q 1 hq1
        (by omega)
    have h3 : Work.Spaces.mixed 1 q (Work.Spaces.DzIter 1 B) z θ
        = Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ := by
      have hcongr := Step.DzIter_congr_of_isOpen isOpen_QQ
        (fun y hy => hcommDz q y.1 y.2 hy) 1 hz
      exact hcongr
    rw [h3] at h1
    rw [hHB]
    exact h1
  -- the slot sums
  set SA : ℝ := ∑ q ∈ Finset.Icc 1 (k - 1), |Work.Spaces.DthIter q A z θ| with hSA
  set SB : ℝ := ∑ q ∈ Finset.Icc 1 (k - 2),
    (|Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ|
      + |Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ|) with hSB
  have hSAnn : 0 ≤ SA := Finset.sum_nonneg fun q _ => abs_nonneg _
  have hSBnn : 0 ≤ SB := Finset.sum_nonneg fun q _ => by positivity
  -- the two slot sums, by Cauchy-Schwarz
  have hSAW : (SA * Work.Spaces.Wt α z θ) ^ 2
      ≤ ((k : ℝ) + 3) * (((k : ℝ) + 3) * HA) := by
    have hcard : ((Finset.Icc 1 (k - 1)).card : ℝ) ≤ (k : ℝ) + 3 := by
      simpa using card_Icc_le 1 (k - 1) (k + 3) (by omega)
    have heq : SA * Work.Spaces.Wt α z θ
        = ∑ q ∈ Finset.Icc 1 (k - 1),
            |Work.Spaces.DthIter q A z θ * Work.Spaces.Wt α z θ| := by
      rw [hSA, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [abs_mul, abs_of_nonneg hwt]
    rw [heq]
    have hsq : ∀ q ∈ Finset.Icc 1 (k - 1),
        (|Work.Spaces.DthIter q A z θ * Work.Spaces.Wt α z θ|) ^ 2 ≤ HA := by
      intro q hq
      simpa only [sq_abs] using hslotA q hq
    have h2 : (∑ q ∈ Finset.Icc 1 (k - 1),
          (|Work.Spaces.DthIter q A z θ * Work.Spaces.Wt α z θ|) ^ 2)
        ≤ ((k : ℝ) + 3) * HA := by
      calc (∑ q ∈ Finset.Icc 1 (k - 1),
            (|Work.Spaces.DthIter q A z θ * Work.Spaces.Wt α z θ|) ^ 2)
          ≤ ∑ _q ∈ Finset.Icc 1 (k - 1), HA := Finset.sum_le_sum hsq
        _ = ((Finset.Icc 1 (k - 1)).card : ℝ) * HA := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((k : ℝ) + 3) * HA := mul_le_mul_of_nonneg_right hcard hHAnn
    calc (∑ q ∈ Finset.Icc 1 (k - 1),
          |Work.Spaces.DthIter q A z θ * Work.Spaces.Wt α z θ|) ^ 2
        ≤ ((Finset.Icc 1 (k - 1)).card : ℝ)
          * ∑ q ∈ Finset.Icc 1 (k - 1),
              (|Work.Spaces.DthIter q A z θ * Work.Spaces.Wt α z θ|) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ ((k : ℝ) + 3) * (((k : ℝ) + 3) * HA) :=
          mul_le_mul hcard h2 (by positivity) (by positivity)
  have hSBW : (SB * Work.Spaces.Wt α z θ) ^ 2
      ≤ ((k : ℝ) + 3) * (((k : ℝ) + 3) * (4 * HB)) := by
    have hcard : ((Finset.Icc 1 (k - 2)).card : ℝ) ≤ (k : ℝ) + 3 := by
      simpa using card_Icc_le 1 (k - 2) (k + 3) (by omega)
    have heq : SB * Work.Spaces.Wt α z θ
        = ∑ q ∈ Finset.Icc 1 (k - 2),
            (|Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ|
              + |Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ
                * Work.Spaces.Wt α z θ|) := by
      rw [hSB, Finset.sum_mul]
      refine Finset.sum_congr rfl fun q _ => ?_
      simp only [add_mul, abs_mul, abs_of_nonneg hwt]
    rw [heq]
    have hsq : ∀ q ∈ Finset.Icc 1 (k - 2),
        (|Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ|
          + |Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ|) ^ 2
        ≤ 4 * HB := by
      intro q hq
      have h2 : (Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ
          * Work.Spaces.Wt α z θ) ^ 2 ≤ HB := hslotB2 q hq
      have h3 : (Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ
          * Work.Spaces.Wt α z θ) ^ 2 ≤ HB := hslotB1 q hq
      have h4 : |Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ| ^ 2
          ≤ HB := by simpa only [sq_abs] using h2
      have h5 : |Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ| ^ 2
          ≤ HB := by simpa only [sq_abs] using h3
      have h7 : (0:ℝ) ≤ |Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ
          * Work.Spaces.Wt α z θ| := abs_nonneg _
      have h8 : (0:ℝ) ≤ |Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ
          * Work.Spaces.Wt α z θ| := abs_nonneg _
      nlinarith [h4, h5, h7, h8]
    have h2 : (∑ q ∈ Finset.Icc 1 (k - 2),
          (|Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ|
            + |Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ
              * Work.Spaces.Wt α z θ|) ^ 2) ≤ ((k : ℝ) + 3) * (4 * HB) := by
      calc (∑ q ∈ Finset.Icc 1 (k - 2),
            (|Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ|
              + |Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ
                * Work.Spaces.Wt α z θ|) ^ 2)
          ≤ ∑ _q ∈ Finset.Icc 1 (k - 2), (4 * HB) := Finset.sum_le_sum hsq
        _ = ((Finset.Icc 1 (k - 2)).card : ℝ) * (4 * HB) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((k : ℝ) + 3) * (4 * HB) := mul_le_mul_of_nonneg_right hcard (by positivity)
    calc (∑ q ∈ Finset.Icc 1 (k - 2),
          (|Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ|
            + |Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ
              * Work.Spaces.Wt α z θ|)) ^ 2
        ≤ ((Finset.Icc 1 (k - 2)).card : ℝ)
          * ∑ q ∈ Finset.Icc 1 (k - 2),
              (|Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ * Work.Spaces.Wt α z θ|
                + |Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ
                  * Work.Spaces.Wt α z θ|) ^ 2 :=
          sq_sum_le_card_mul_sum_sq
      _ ≤ ((k : ℝ) + 3) * (((k : ℝ) + 3) * (4 * HB)) :=
          mul_le_mul hcard h2 (by positivity) (by positivity)
  have hA2 : ∀ z' θ' : ℝ, (z', θ') ∈ QQ → Work.Spaces.pthIter 2 A z' θ'
      = z' ^ 2 * Work.Spaces.pzIter 2 B z' θ' := by
    intro z' θ' hz'
    have e1 : Work.Spaces.pthIter 2 A
        = fun z θ => z ^ 2 * Work.Spaces.pthIter 2 (Work.Spaces.pzIter 2 Ψ) z θ := by
      rw [hAdef]
      exact pthIter_const_mul_z 2 (fun z => z ^ 2) (Work.Spaces.pzIter 2 Ψ)
    have hv := congrFun (congrFun e1 z') θ'
    rw [hv, pthIter_pzIter_comm_QQ 2 2 hΨ z' θ' hz']
  -- the term-by-term bound
  have hterm : ∀ r ∈ Finset.Icc 1 k,
      (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r A z θ| ≤ Ke * (SA + SB) := by
    have keyk : (Real.sin (2 * θ)) ^ k * |Work.Spaces.pthIter k A z θ| ≤ Ke * (SA + SB) := by
      -- the value of `∂_θ^k A` in terms of `∂_z² (∂_θ^{k-2} ∂_θ² Ψ)`
      have h2k : 2 ≤ k := by omega
      have e1 : Work.Spaces.pthIter k A
          = Work.Spaces.pthIter (k - 2) (Work.Spaces.pthIter 2 A) := by
        have h := pthIter_add' (k - 2) 2 A
        rw [Nat.sub_add_cancel h2k] at h
        exact h
      have e3 := pthIter_const_mul_z (k - 2) (fun z => z ^ 2) (Work.Spaces.pzIter 2 B)
      have e5 : Work.Spaces.pthIter (k - 2) B = Work.Spaces.pthIter k Ψ := by
        have h := pthIter_add' (k - 2) 2 Ψ
        rw [Nat.sub_add_cancel h2k] at h
        rw [hBdef]
        exact h.symm
      have hcong := pthIter_congr_QQ (k - 2) (f := Work.Spaces.pthIter 2 A)
        (g := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 B z θ)
        (fun z' θ' hz' => hA2 z' θ' hz')
      have e4 : ∀ z' θ' : ℝ, (z', θ') ∈ QQ →
          Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z' θ'
            = Work.Spaces.pzIter 2 (Work.Spaces.pthIter (k - 2) B) z' θ' :=
        fun z' θ' hz' => pthIter_pzIter_comm_QQ (k - 2) 2 hB_sm z' θ' hz'
      have h1 : Work.Spaces.pthIter k A z θ
          = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter k Ψ) z θ := by
        calc Work.Spaces.pthIter k A z θ
            = Work.Spaces.pthIter (k - 2) (Work.Spaces.pthIter 2 A) z θ := by rw [e1]
          _ = Work.Spaces.pthIter (k - 2)
                (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 B z θ) z θ := hcong z θ hz
          _ = z ^ 2 * Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ := by rw [e3]
          _ = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter (k - 2) B) z θ := by
              rw [e4 z θ hz]
          _ = z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.pthIter k Ψ) z θ := by rw [e5]
      have h2 := hCe (k - 2) (by omega) (Work.Spaces.pzIter 2 B) z θ hθ hB2cd
      have h3 : ∀ q : ℕ, Work.Spaces.DthIter q (Work.Spaces.pzIter 2 B) z θ
          = Work.Spaces.pzIter 2 (Work.Spaces.DthIter q B) z θ := fun q =>
        DthIter_pzIter_comm_QQ q 2 hB_sm z θ hz
      have h4 : ∀ q : ℕ, z ^ 2 * |Work.Spaces.pzIter 2 (Work.Spaces.DthIter q B) z θ|
          ≤ |Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ|
            + |Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ| := by
        intro q
        have hdiff : z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DthIter q B) z θ
            = Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ
              - Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ :=
          zsq_pzIter2_eq (Work.Spaces.DthIter q B)
            (((hB_sm.DthIter q).pz).hasDerivAt_slice hθ hz.1).differentiableAt
        have hshow : z ^ 2 * |Work.Spaces.pzIter 2 (Work.Spaces.DthIter q B) z θ|
            = |z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DthIter q B) z θ| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ z ^ 2)]
        rw [hshow, hdiff]
        have ha := le_abs_self (Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ)
        have ha' := neg_le_abs (Work.Spaces.DzIter 2 (Work.Spaces.DthIter q B) z θ)
        have hb := le_abs_self (Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ)
        have hb' := neg_le_abs (Work.Spaces.DzIter 1 (Work.Spaces.DthIter q B) z θ)
        exact abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩
      have h5z : z ^ 2 * ∑ q ∈ Finset.Icc 1 (k - 2),
            |Work.Spaces.DthIter q (Work.Spaces.pzIter 2 B) z θ| ≤ SB := by
        rw [Finset.mul_sum, hSB]
        refine Finset.sum_le_sum fun q hq => ?_
        rw [h3 q]
        exact h4 q
      have hstep : z ^ 2 * ((Real.sin (2 * θ)) ^ (k - 2)
            * |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ|)
          ≤ z ^ 2 * (Ce (k - 2) * ∑ q ∈ Finset.Icc 1 (k - 2),
              |Work.Spaces.DthIter q (Work.Spaces.pzIter 2 B) z θ|) :=
        mul_le_mul_of_nonneg_left h2 (sq_nonneg z)
      have hstep' : z ^ 2 * (Ce (k - 2) * ∑ q ∈ Finset.Icc 1 (k - 2),
              |Work.Spaces.DthIter q (Work.Spaces.pzIter 2 B) z θ|)
          = Ce (k - 2) * (z ^ 2 * ∑ q ∈ Finset.Icc 1 (k - 2),
              |Work.Spaces.DthIter q (Work.Spaces.pzIter 2 B) z θ|) := by ring
      have hfin : z ^ 2 * ((Real.sin (2 * θ)) ^ (k - 2)
            * |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ|)
          ≤ Ce (k - 2) * SB := by
        rw [hstep'] at hstep
        exact le_trans hstep (mul_le_mul_of_nonneg_left h5z (hCepos (k - 2)).le)
      have hpow : (Real.sin (2 * θ)) ^ k
          = ((Real.sin (2 * θ)) ^ (k - 2)) * (Real.sin (2 * θ)) ^ 2 := by
        rw [← pow_add]
        congr 1
        omega
      have hs2 : (Real.sin (2 * θ)) ^ 2 ≤ 1 := by
        nlinarith [Real.sin_le_one (2 * θ), hspos]
      have hkey1 : |Work.Spaces.pzIter 2 (Work.Spaces.pthIter k Ψ) z θ|
          = |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ| := by
        rw [← e5]
        exact congrArg (fun t => |t|) (e4 z θ hz).symm
      have hfin2 : (Real.sin (2 * θ)) ^ k * |Work.Spaces.pthIter k A z θ|
          ≤ z ^ 2 * ((Real.sin (2 * θ)) ^ (k - 2)
              * |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ|) := by
        rw [h1, abs_mul, abs_of_nonneg (sq_nonneg z), hpow, hkey1]
        rw [show ((Real.sin (2 * θ)) ^ (k - 2) * (Real.sin (2 * θ)) ^ 2)
              * (z ^ 2 * |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ|)
            = z ^ 2 * ((Real.sin (2 * θ)) ^ (k - 2)
              * ((Real.sin (2 * θ)) ^ 2
                * |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ|)) from by ring]
        have hsp : 0 ≤ (Real.sin (2 * θ)) ^ (k - 2) := pow_nonneg hspos _
        have hpn : 0 ≤ |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ| := abs_nonneg _
        have hz2 : 0 ≤ z ^ 2 := sq_nonneg z
        have hs2' : (Real.sin (2 * θ)) ^ 2
            * |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ|
            ≤ |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ| :=
          mul_le_of_le_one_left hpn hs2
        have h1' : (Real.sin (2 * θ)) ^ (k - 2)
            * ((Real.sin (2 * θ)) ^ 2
              * |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ|)
            ≤ (Real.sin (2 * θ)) ^ (k - 2)
              * |Work.Spaces.pthIter (k - 2) (Work.Spaces.pzIter 2 B) z θ| :=
          mul_le_mul_of_nonneg_left hs2' hsp
        exact mul_le_mul_of_nonneg_left h1' hz2
      have hCen : Ce (k - 2) ≤ Ke := by
        rw [hKe]
        have hmem : k - 2 ∈ Finset.Icc 1 (k - 1) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
        have := Finset.single_le_sum (fun m _ => (hCepos m).le) hmem
        linarith
      refine le_trans hfin2 (le_trans hfin ?_)
      have hcenn : 0 ≤ Ce (k - 2) := (hCepos (k - 2)).le
      nlinarith [hCen, hcenn, hSAnn, hSBnn]
    intro r hr
    obtain ⟨hr1, hrk⟩ := Finset.mem_Icc.mp hr
    rcases lt_or_eq_of_le hrk with hrlt | hreq
    · have hCr : Ce r ≤ Ke := by
        rw [hKe]
        have hrmem : r ∈ Finset.Icc 1 (k - 1) := Finset.mem_Icc.mpr ⟨hr1, by omega⟩
        have := Finset.single_le_sum (fun m _ => (hCepos m).le) hrmem
        linarith
      have h1 := hCe r hr1 A z θ hθ hAcd
      have h2 : (∑ q ∈ Finset.Icc 1 r, |Work.Spaces.DthIter q A z θ|) ≤ SA := by
        rw [hSA]
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun q _ _ => abs_nonneg _)
        intro q hq
        obtain ⟨hq1, hqr⟩ := Finset.mem_Icc.mp hq
        exact Finset.mem_Icc.mpr ⟨hq1, by omega⟩
      have hsum_nn : 0 ≤ ∑ q ∈ Finset.Icc 1 r, |Work.Spaces.DthIter q A z θ| :=
        Finset.sum_nonneg fun q _ => abs_nonneg _
      have hCrnn : 0 ≤ Ce r := (hCepos r).le
      have hstep : (Real.sin (2 * θ)) ^ r * |Work.Spaces.pthIter r A z θ|
          ≤ Ce r * ∑ q ∈ Finset.Icc 1 r, |Work.Spaces.DthIter q A z θ| := h1
      have hstep2 : Ce r * (∑ q ∈ Finset.Icc 1 r, |Work.Spaces.DthIter q A z θ|)
          ≤ Ke * SA := by
        have hk1 : Ce r * (∑ q ∈ Finset.Icc 1 r, |Work.Spaces.DthIter q A z θ|)
            ≤ Ke * (∑ q ∈ Finset.Icc 1 r, |Work.Spaces.DthIter q A z θ|) :=
          mul_le_mul_of_nonneg_right hCr hsum_nn
        exact le_trans hk1 (mul_le_mul_of_nonneg_left h2 hKenn)
      exact le_trans (le_trans hstep hstep2) (mul_le_mul_of_nonneg_left (by linarith) hKenn)
    · rw [hreq]
      exact keyk
  -- the expansion
  have hcoef : ∀ r : ℕ, |selfdth.dthCoef k r θ| ≤ Km * (Real.sin (2 * θ)) ^ r := by
    intro r
    rcases lt_or_ge k r with hr | hr
    · have h0 : selfdth.dthCoef k r θ = 0 :=
        congrFun (selfdth.dthCoef_zero_of_gt hr) θ
      rw [h0]
      simp only [abs_zero]
      positivity
    · have hr' : r ∈ Finset.range (k + 1) := Finset.mem_range.mpr (by omega)
      have h1 := hKcbd r θ
      rw [abs_of_pos hs] at h1
      have h2 : Kc r ≤ Km := by
        rw [hKm]
        have := Finset.single_le_sum (fun i _ => (hKcpos i).le) hr'
        linarith
      exact le_trans h1 (mul_le_mul_of_nonneg_right h2 (pow_nonneg hspos r))
  have hexp := selfdth.DthIter_expansion_local k A z θ hAcd
  have hstep1 : |Work.Spaces.DthIter k A z θ|
      ≤ Km * ∑ i ∈ Finset.range k,
          (Real.sin (2 * θ)) ^ (i + 1) * |Work.Spaces.pthIter (i + 1) A z θ| := by
    have h := hexp
    rw [Finset.sum_range_succ'] at h
    have hz0 : selfdth.dthCoef k 0 θ * Work.Spaces.pthIter 0 A z θ = 0 := by
      have h0 : selfdth.dthCoef k 0 = fun _ : ℝ => (0 : ℝ) :=
        dthCoef_zero_fun (by omega)
      rw [h0]
      simp
    rw [hz0, add_zero] at h
    rw [h]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc |selfdth.dthCoef k (i + 1) θ * Work.Spaces.pthIter (i + 1) A z θ|
        = |selfdth.dthCoef k (i + 1) θ| * |Work.Spaces.pthIter (i + 1) A z θ| :=
          abs_mul _ _
      _ ≤ (Km * (Real.sin (2 * θ)) ^ (i + 1)) * |Work.Spaces.pthIter (i + 1) A z θ| :=
          mul_le_mul_of_nonneg_right (hcoef (i + 1)) (abs_nonneg _)
      _ = Km * ((Real.sin (2 * θ)) ^ (i + 1)
            * |Work.Spaces.pthIter (i + 1) A z θ|) := by ring
  have hstep2 : Km * ∑ i ∈ Finset.range k,
        (Real.sin (2 * θ)) ^ (i + 1) * |Work.Spaces.pthIter (i + 1) A z θ|
      ≤ Km * ((k : ℝ) * (Ke * (SA + SB))) := by
    refine mul_le_mul_of_nonneg_left ?_ hKmnn
    have hle : ∑ i ∈ Finset.range k,
          (Real.sin (2 * θ)) ^ (i + 1) * |Work.Spaces.pthIter (i + 1) A z θ|
        ≤ ∑ _i ∈ Finset.range k, (Ke * (SA + SB)) :=
      Finset.sum_le_sum fun i hi => by
        refine hterm (i + 1) (Finset.mem_Icc.mpr
          ⟨Nat.succ_le_succ (Nat.zero_le i), by
            have := Finset.mem_range.mp hi; omega⟩)
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hle
    exact hle
  have key : (Work.Spaces.DthIter k A z θ * Work.Spaces.Wt α z θ) ^ 2
      ≤ (Km * ((k : ℝ) * (Ke * (SA + SB)))) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 := by
    have habs : |Work.Spaces.DthIter k A z θ| ≤ Km * ((k : ℝ) * (Ke * (SA + SB))) :=
      le_trans hstep1 hstep2
    have hsq : (Work.Spaces.DthIter k A z θ) ^ 2
        ≤ (Km * ((k : ℝ) * (Ke * (SA + SB)))) ^ 2 := by
      have h := mul_self_le_mul_self (abs_nonneg (Work.Spaces.DthIter k A z θ)) habs
      have h' : |Work.Spaces.DthIter k A z θ| ^ 2
          ≤ (Km * ((k : ℝ) * (Ke * (SA + SB)))) ^ 2 := by
        simpa [pow_two] using h
      rwa [sq_abs] at h'
    calc (Work.Spaces.DthIter k A z θ * Work.Spaces.Wt α z θ) ^ 2
        = (Work.Spaces.DthIter k A z θ) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 := by ring
      _ ≤ (Km * ((k : ℝ) * (Ke * (SA + SB)))) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2 :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
  have expand : (Km * ((k : ℝ) * (Ke * (SA + SB)))) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
      ≤ (Km * ((k : ℝ) * Ke)) ^ 2 * 2
        * ((SA * Work.Spaces.Wt α z θ) ^ 2 + (SB * Work.Spaces.Wt α z θ) ^ 2) := by
    have hfac : (Km * ((k : ℝ) * (Ke * (SA + SB)))) ^ 2 * (Work.Spaces.Wt α z θ) ^ 2
        = (Km * ((k : ℝ) * Ke)) ^ 2 * ((SA + SB) * Work.Spaces.Wt α z θ) ^ 2 := by ring
    rw [hfac]
    have h2 : ((SA + SB) * Work.Spaces.Wt α z θ) ^ 2
        ≤ 2 * ((SA * Work.Spaces.Wt α z θ) ^ 2 + (SB * Work.Spaces.Wt α z θ) ^ 2) := by
      have he : (SA + SB) * Work.Spaces.Wt α z θ
          = SA * Work.Spaces.Wt α z θ + SB * Work.Spaces.Wt α z θ := by ring
      have h3 : (SA * Work.Spaces.Wt α z θ + SB * Work.Spaces.Wt α z θ) ^ 2
          ≤ 2 * ((SA * Work.Spaces.Wt α z θ) ^ 2 + (SB * Work.Spaces.Wt α z θ) ^ 2) := by
        nlinarith [sq_nonneg (SA * Work.Spaces.Wt α z θ - SB * Work.Spaces.Wt α z θ)]
      rw [he]
      exact h3
    have hnn : (0 : ℝ) ≤ (Km * ((k : ℝ) * Ke)) ^ 2 := by positivity
    calc (Km * ((k : ℝ) * Ke)) ^ 2 * ((SA + SB) * Work.Spaces.Wt α z θ) ^ 2
        ≤ (Km * ((k : ℝ) * Ke)) ^ 2
            * (2 * ((SA * Work.Spaces.Wt α z θ) ^ 2 + (SB * Work.Spaces.Wt α z θ) ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 hnn
      _ = (Km * ((k : ℝ) * Ke)) ^ 2 * 2
            * ((SA * Work.Spaces.Wt α z θ) ^ 2 + (SB * Work.Spaces.Wt α z θ) ^ 2) := by ring
  refine le_trans key (le_trans expand ?_)
  rw [hHA, hHB]
  have hk3 : (3 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hsum : (SA * Work.Spaces.Wt α z θ) ^ 2 + (SB * Work.Spaces.Wt α z θ) ^ 2
      ≤ ((((k : ℝ) + 3) ^ 2) + (((k : ℝ) + 3) ^ 2 * 4)) * (HA + HB) := by
    have hA' : (SA * Work.Spaces.Wt α z θ) ^ 2 ≤ ((k : ℝ) + 3) ^ 2 * HA := by
      have h := hSAW
      nlinarith [h, hHAnn]
    have hB' : (SB * Work.Spaces.Wt α z θ) ^ 2 ≤ ((k : ℝ) + 3) ^ 2 * (4 * HB) := by
      have h := hSBW
      nlinarith [h, hHBnn]
    nlinarith [hA', hB', hHAnn, hHBnn]
  calc (Km * ((k : ℝ) * Ke)) ^ 2 * 2
        * ((SA * Work.Spaces.Wt α z θ) ^ 2 + (SB * Work.Spaces.Wt α z θ) ^ 2)
      ≤ (Km * ((k : ℝ) * Ke)) ^ 2 * 2
          * (((((k : ℝ) + 3) ^ 2) + (((k : ℝ) + 3) ^ 2 * 4)) * (HA + HB)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ ≤ (((k : ℝ) + 3) ^ 4 * (Km * Ke) ^ 2 * 16) * (HA + HB) := by
        have h16 : (0:ℝ) ≤ HA + HB := by linarith
        have h17 : (Km * ((k : ℝ) * Ke)) ^ 2 * 2
            * ((((k : ℝ) + 3) ^ 2) + (((k : ℝ) + 3) ^ 2 * 4))
            ≤ ((k : ℝ) + 3) ^ 4 * (Km * Ke) ^ 2 * 16 := by
          have h18 : (0:ℝ) ≤ (k:ℝ) + 3 := by positivity
          have h19 : (0:ℝ) ≤ Km * Ke := by positivity
          nlinarith [h18, h19, hk3, sq_nonneg Km, sq_nonneg Ke, sq_nonneg ((k:ℝ) + 3),
            sq_nonneg (Km * Ke), sq_nonneg (Km * Ke - 1), sq_nonneg ((k:ℝ) - 3)]
        have h20 := mul_le_mul_of_nonneg_right h17 h16
        linarith [h20]
    _ ≤ ((((k : ℝ) + 3) ^ 4 * (Km * Ke) ^ 2 * 16) + 1) * (HA + HB) := by
        have h16 : (0:ℝ) ≤ HA + HB := by linarith
        nlinarith [h16]

/-! ## The measure-theoretic comparison

`Tk_le_of_pointwise` (proved in `Submission.Work.FTS.EllipticEst.remov.ATop.Tk_le_of_pointwise`)
integrates the pointwise bound of `A_top_pointwise` against its honest majorant; it is the
measure-theoretic half of the target below. -/

theorem A_top_slot_bound_clean (D : ℝ) (hD : 0 < D) :
    ∀ k : ℕ, 3 ≤ k → ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 Ψ)
        ≤ D * Work.Spaces.HkNorm α k F →
      α ^ 2 * Work.Spaces.HkNorm α (k - 1)
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ)
          + Work.Spaces.HkNorm α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ))
        ≤ D * Work.Spaces.HkNorm α k F →
      α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ))
        ≤ C * Work.Spaces.HkNorm α k F := by
  intro k hk
  obtain ⟨K, hKpos, hKpt⟩ := A_top_pointwise k hk
  refine ⟨2 * D * Real.sqrt K + 1, ?_, ?_⟩
  · nlinarith [Real.sqrt_pos.mpr hKpos, hD]
  · intro α F Ψ hα hα4 hwk h1 h2
    set A : ℝ → ℝ → ℝ := fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ with hAdef
    set B : ℝ → ℝ → ℝ := Work.Spaces.pthIter 2 Ψ with hBdef
    set Φ : ℝ → ℝ → ℝ := Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) with hΦdef
    set nF : ℝ := Work.Spaces.HkNorm α k F with hnFdef
    have hnFnn : 0 ≤ nF := Work.Spaces.HkNorm_nonneg α k F
    have hα2pos : 0 < α ^ 2 := by positivity
    have hα2le : α ^ 2 ≤ 1 := by nlinarith [hα, hα4]
    have hSnF : 0 ≤ D * nF := mul_nonneg hD.le hnFnn
    have hXnn : 0 ≤ D * nF / α ^ 2 := div_nonneg hSnF hα2pos.le
    -- the smoothness of the data on the open quadrant
    have hΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
      Work.FTS.EllipticEst.smoothOpen_of_forall hwk.smooth
    have hA_sm : Work.FTS.EllipticEst.SmoothOpen A := zsq_pzIter2_smooth hΨ
    have hΦ_sm : Work.FTS.EllipticEst.SmoothOpen Φ := (pthIter_smooth hΨ 2).Dz
    -- the honesty of the two integrands at level `k-1`
    have hmemA' : Work.Spaces.HkMem α k A := hwk.memA
    have hmemA : Work.Spaces.HkMem α (k - 1) A :=
      Work.FTS.EllipticEst.TT.HkMem_descend_open (k := k - 1) (l := k) (f := A) (by omega)
        ((Work.FTS.EllipticEst.smoothOpen_iff_forall A).mp hA_sm) hmemA'
    have hmemΦ : Work.Spaces.HkMem α (k - 1) Φ :=
      HkMem_Dz_shift_clean (α := α) (k := k) (by omega)
        (pthIter_smooth hΨ 2) hwk.memB
    -- the pointwise bound of `A_top_pointwise` in the shape the integral comparison wants
    have hpt : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        (Work.Spaces.DthIter k A z θ * Work.Spaces.Wt α z θ) ^ 2
          ≤ K * (Work.Spaces.HkIntegrand α (k - 1) A z θ
              + Work.Spaces.HkIntegrand α (k - 1) Φ z θ) :=
      fun z θ hz hθ hlt => hKpt α Ψ hΨ z θ ⟨hz, hθ, hlt⟩
    have hint : Work.FTS.EllipticEst.remov.Step.Tk α k A
        ≤ K * (Work.Spaces.HkSq α (k - 1) A + Work.Spaces.HkSq α (k - 1) Φ) :=
      Work.FTS.EllipticEst.remov.ATop.Tk_le_of_pointwise hKpos.le hmemA hmemΦ hpt
    -- `Φ` agrees with the function of the second hypothesis
    have hagree : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
        Φ z θ = Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ) z θ := by
      intro z θ hz hθ hlt
      have hv : Work.Spaces.DzIter 1 Ψ
          = fun z θ => z * Work.Spaces.pzIter 1 Ψ z θ := rfl
      have hcm : Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)
          = fun z θ => z * Work.Spaces.pthIter 2 (Work.Spaces.pzIter 1 Ψ) z θ := by
        rw [hv]
        exact pthIter_const_mul_z 2 (fun z => z) (Work.Spaces.pzIter 1 Ψ)
      rw [hΦdef, hcm]
      show Work.Spaces.DzIter 1 (Work.Spaces.pthIter 2 Ψ) z θ
        = z * Work.Spaces.pthIter 2 (Work.Spaces.pzIter 1 Ψ) z θ
      rw [pthIter_pzIter_comm_QQ 2 1 hΨ z θ ⟨hz, hθ, hlt⟩]
      rfl
    have hcong : Work.Spaces.HkSq α (k - 1) Φ
        = Work.Spaces.HkSq α (k - 1) (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) :=
      Work.FTS.EllipticEst.HkSq_congr_open α (k - 1) hagree
    -- the two norm bounds coming from the hypotheses
    have h1' : α ^ 2 * Work.Spaces.HkNorm α (k - 1) A ≤ D * nF := by
      have hBnn : 0 ≤ Work.Spaces.HkNorm α (k - 1) B := Work.Spaces.HkNorm_nonneg α (k - 1) B
      exact le_trans (le_add_of_nonneg_right hBnn) h1
    have hnormA : Work.Spaces.HkNorm α (k - 1) A ≤ D * nF / α ^ 2 := by
      rw [le_div_iff₀ hα2pos]
      calc Work.Spaces.HkNorm α (k - 1) A * α ^ 2
          = α ^ 2 * Work.Spaces.HkNorm α (k - 1) A := by ring
        _ ≤ D * nF := h1'
    have h2' : Work.Spaces.HkNorm α (k - 1)
        (Work.Spaces.pthIter 2 (Work.Spaces.DzIter 1 Ψ)) ≤ D * nF := by
      have hAnn' : 0 ≤ α ^ 2 * Work.Spaces.HkNorm α (k - 1)
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 (Work.Spaces.DzIter 1 Ψ) z θ) :=
        mul_nonneg hα2pos.le (Work.Spaces.HkNorm_nonneg α (k - 1) _)
      exact le_trans (le_add_of_nonneg_left hAnn') h2
    have hnormΦ : Work.Spaces.HkNorm α (k - 1) Φ ≤ D * nF := by
      change Real.sqrt (Work.Spaces.HkSq α (k - 1) Φ) ≤ D * nF
      rw [hcong]
      exact h2'
    -- squaring
    have hSqA : Work.Spaces.HkSq α (k - 1) A ≤ (D * nF / α ^ 2) ^ 2 := by
      have h : Work.Spaces.HkSq α (k - 1) A = (Work.Spaces.HkNorm α (k - 1) A) ^ 2 := by
        rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α (k - 1) A)]
      rw [h]
      have hh := mul_self_le_mul_self (Work.Spaces.HkNorm_nonneg α (k - 1) A) hnormA
      simpa [pow_two] using hh
    have hSqΦ : Work.Spaces.HkSq α (k - 1) Φ ≤ (D * nF) ^ 2 := by
      have h : Work.Spaces.HkSq α (k - 1) Φ = (Work.Spaces.HkNorm α (k - 1) Φ) ^ 2 := by
        rw [Work.Spaces.HkNorm, Real.sq_sqrt (Work.Spaces.HkSq_nonneg α (k - 1) Φ)]
      rw [h]
      have hh := mul_self_le_mul_self (Work.Spaces.HkNorm_nonneg α (k - 1) Φ) hnormΦ
      simpa [pow_two] using hh
    have hTK : Work.FTS.EllipticEst.remov.Step.Tk α k A
        ≤ K * ((D * nF / α ^ 2) ^ 2 + (D * nF) ^ 2) := by
      refine le_trans hint ?_
      exact mul_le_mul_of_nonneg_left (add_le_add hSqA hSqΦ) hKpos.le
    -- square roots
    have hsqrt1 : Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k A)
        ≤ Real.sqrt (K * ((D * nF / α ^ 2) ^ 2 + (D * nF) ^ 2)) := Real.sqrt_le_sqrt hTK
    have hsqrt2 : Real.sqrt (K * ((D * nF / α ^ 2) ^ 2 + (D * nF) ^ 2))
        ≤ Real.sqrt K * (D * nF / α ^ 2 + D * nF) := by
      rw [Real.sqrt_mul hKpos.le]
      refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg K)
      rw [Real.sqrt_le_iff]
      refine ⟨add_nonneg hXnn hSnF, ?_⟩
      nlinarith [hXnn, hSnF]
    have hfin : α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k A)
        ≤ (2 * D * Real.sqrt K + 1) * nF := by
      have hdiv : α ^ 2 * (D * nF / α ^ 2) = D * nF := by
        rw [mul_comm]
        exact div_mul_cancel₀ _ (ne_of_gt hα2pos)
      have hident : α ^ 2 * (Real.sqrt K * (D * nF / α ^ 2 + D * nF))
          = Real.sqrt K * (D * nF + α ^ 2 * (D * nF)) := by
        rw [show α ^ 2 * (Real.sqrt K * (D * nF / α ^ 2 + D * nF))
            = Real.sqrt K * (α ^ 2 * (D * nF / α ^ 2 + D * nF)) by ring,
          mul_add, hdiv]
      have h1s : α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k A)
          ≤ α ^ 2 * (Real.sqrt K * (D * nF / α ^ 2 + D * nF)) :=
        mul_le_mul_of_nonneg_left (le_trans hsqrt1 hsqrt2) hα2pos.le
      have h2s : D * nF + α ^ 2 * (D * nF) ≤ 2 * (D * nF) := by
        have h := mul_le_mul_of_nonneg_right hα2le hSnF
        linarith
      have h3s : Real.sqrt K * (D * nF + α ^ 2 * (D * nF))
          ≤ Real.sqrt K * (2 * (D * nF)) :=
        mul_le_mul_of_nonneg_left h2s (Real.sqrt_nonneg K)
      calc α ^ 2 * Real.sqrt (Work.FTS.EllipticEst.remov.Step.Tk α k A)
          ≤ α ^ 2 * (Real.sqrt K * (D * nF / α ^ 2 + D * nF)) := h1s
        _ = Real.sqrt K * (D * nF + α ^ 2 * (D * nF)) := hident
        _ ≤ Real.sqrt K * (2 * (D * nF)) := h3s
        _ = (2 * D * Real.sqrt K) * nF := by ring
        _ ≤ (2 * D * Real.sqrt K + 1) * nF := by
            have h := mul_le_mul_of_nonneg_right (by linarith : 2 * D * Real.sqrt K
              ≤ 2 * D * Real.sqrt K + 1) hnFnn
            simpa using h
    simpa only [hnFdef] using hfin

end Work.FTS.EllipticEst.remov
