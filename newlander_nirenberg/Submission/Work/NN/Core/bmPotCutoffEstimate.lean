import Mathlib
import Submission.Work.NN.Core.bmRow
import Submission.Work.NN.Final.bmRow_bound
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comm
import Submission.Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
import Submission.Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.CR.Flat.Holder.holderNorm_neg
import Submission.Work.CR.Flat.Cauchy.bmKernel_divergence_aux

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.NN.Core

open scoped NNReal ENNReal ContDiff Topology
open Set Filter

noncomputable section

/-! ## Elementary auxiliaries

`bmH χ η i l m = ∂̄_m χ · η i l + ∂̄_i χ · η l m - ∂̄_l χ · η i m` is *algebraic* in `η`: it
involves no derivative of `η`.  The estimate for `bmH` therefore only needs a `C^{k,α}` bound on
`η` on the polydisc where the cut-off lives, together with the elementary fact that multiplication
by a compactly supported smooth function is bounded in the `C^{k,α}` scale
(`holderNorm_mul_le_of_hasCompactSupport`).  The cut-off `χ` is only assumed *smooth* (and not
analytic), so the third argument of the potential gains regularity through
`Work.NN.Final.bmRow_bound`. -/

/-- If `f` vanishes near `z` then its `(0,1)`-Wirtinger derivative vanishes at `z`. -/
private lemma dbarCoord_eq_zero_of_eventuallyEq_zero {n : ℕ} {f : Cn n → ℂ} {z : Cn n}
    (h : f =ᶠ[𝓝 z] 0) (k : Fin n) : Work.CR.Flat.dbarCoord k f z = 0 := by
  unfold Work.CR.Flat.dbarCoord
  rw [h.fderiv_eq]
  simp

/-- `∂̄_j` of a smooth function is smooth. -/
private lemma contDiff_dbarCoord_of {n : ℕ} {f : Cn n → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (j : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (fun z => Work.CR.Flat.dbarCoord j f z) := by
  rw [Work.CR.Flat.Polydisc.dbarCoord_eq_comp]
  exact (Work.CR.Flat.Polydisc.dbarCoordPhi j).contDiff.comp (hf.fderiv_right (by simp))

/-- A function vanishing on the closed exterior of a polydisc with positive radii has compact
support. -/
private lemma hasCompactSupport_of_vanishing_polydisc {n : ℕ} {r : Fin n → ℝ}
    (hr : ∀ j, 0 < r j) {f : Cn n → ℂ} (hf : ∀ z, (∃ i, r i ≤ ‖z i‖) → f z = 0) :
    HasCompactSupport f := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : Cn n) (∑ i, r i)) ?_
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right]
  rw [Function.mem_support] at hz
  by_contra hcon
  rw [not_le] at hcon
  have hex : ∃ i, r i ≤ ‖z i‖ := by
    by_contra h
    have h' : ∀ i, ‖z i‖ < r i := fun i => not_le.mp (fun hle => h ⟨i, hle⟩)
    have h2 : ‖z‖ ≤ ∑ i, r i := by
      rw [pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => (hr i).le)]
      intro i
      exact le_trans (le_of_lt (h' i))
        (Finset.single_le_sum (fun i _ => (hr i).le) (Finset.mem_univ i))
    linarith
  exact hz (hf z hex)

/-- The components of `bmH χ η i l m` vanish on the closed exterior of `polydisc 0 r` as soon as
`ρ''' < r` componentwise and `χ` vanishes on the closed exterior of `polydisc 0 ρ'''`. -/
private lemma bmH_component_eq_zero {n : ℕ} {ρ''' r : Fin n → ℝ} (hr : ∀ j, ρ''' j < r j)
    (χ : Cn n → ℂ) (hχzero : ∀ z : Cn n, (∃ j, ρ''' j ≤ ‖z j‖) → χ z = 0)
    (η : Fin n → Fin n → Cn n → ℂ) (i l m : Fin n) :
    ∀ z : Cn n, (∃ i', r i' ≤ ‖z i'‖) → bmH χ η i l m z = 0 := by
  intro z hz
  obtain ⟨i', hi'⟩ := hz
  have hev : χ =ᶠ[𝓝 z] 0 := by
    have hopen : IsOpen {w : Cn n | ρ''' i' < ‖w i'‖} :=
      isOpen_lt continuous_const ((continuous_apply i').norm)
    filter_upwards [hopen.mem_nhds (lt_of_lt_of_le (hr i') hi')] with w hw
    exact hχzero w ⟨i', le_of_lt hw⟩
  have hd0 : ∀ t : Fin n, Work.CR.Flat.dbarCoord t χ z = 0 :=
    fun t => dbarCoord_eq_zero_of_eventuallyEq_zero hev t
  simp only [bmH, hd0, zero_mul, add_zero, sub_zero]

/-- `bmH χ η i l m` is of class `C^{k+1}` whenever `χ` is smooth and the `η i l` are `C^{k+1}`. -/
private lemma contDiff_bmH_component {n k : ℕ} {χ : Cn n → ℂ} {η : Fin n → Fin n → Cn n → ℂ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hη : ∀ j l, ContDiff ℝ (k + 1) (η j l)) (i l m : Fin n) :
    ContDiff ℝ (k + 1) (fun w => bmH χ η i l m w) := by
  have hdχ : ContDiff ℝ (k + 1) (fun z => Work.CR.Flat.dbarCoord m χ z) :=
    (contDiff_dbarCoord_of hχ m).of_le (by simp)
  have hdχi : ContDiff ℝ (k + 1) (fun z => Work.CR.Flat.dbarCoord i χ z) :=
    (contDiff_dbarCoord_of hχ i).of_le (by simp)
  have hdχl : ContDiff ℝ (k + 1) (fun z => Work.CR.Flat.dbarCoord l χ z) :=
    (contDiff_dbarCoord_of hχ l).of_le (by simp)
  have heq : (fun w => bmH χ η i l m w) =
      (fun w => Work.CR.Flat.dbarCoord m χ w * η i l w
        + Work.CR.Flat.dbarCoord i χ w * η l m w
        - Work.CR.Flat.dbarCoord l χ w * η i m w) := by
    funext w; simp only [bmH]
  rw [heq]
  exact (((hdχ.mul (hη i l)).add (hdχi.mul (hη l m))).sub (hdχl.mul (hη i m)))

/-- Pulling two `ofReal`s together, with an arbitrary tail. -/
private lemma ofReal_mul_mul_assoc {a b : ℝ} (ha : 0 ≤ a) (_hb : 0 ≤ b) (X : ℝ≥0∞) :
    ENNReal.ofReal a * (ENNReal.ofReal b * X) = ENNReal.ofReal (a * b) * X := by
  rw [← mul_assoc, ← ENNReal.ofReal_mul ha]

/-! ## The cutoff estimate -/

theorem bmPotCutoffEstimate {n : ℕ} (hn : 0 < n) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {ρ ρ'' ρ''' : Fin n → ℝ} (hρ''pos : ∀ j, 0 < ρ'' j) (hρ'''2ρ'' : ∀ j, ρ''' j < 2 * ρ'' j)
    (hρ'''ρ : ∀ j, ρ''' j < ρ j)
    (χ : Work.NN.Core.Cn n → ℂ) (hχ_sm : ContDiff ℝ (⊤ : ℕ∞) χ) (hχ_cs : HasCompactSupport χ)
    (hχzero : ∀ z : Work.NN.Core.Cn n, (∃ j, ρ''' j ≤ ‖z j‖) → χ z = 0) :
    ∃ C : ℕ → ℝ, (∀ k, 0 < C k) ∧
      ∀ (k : ℕ) (η : Fin n → Fin n → Work.NN.Core.Cn n → ℂ),
        (∀ j l, ContDiff ℝ (k + 1) (η j l)) →
        ∀ i l : Fin n,
          Work.CR.Flat.holderNorm (k + 1) α
              (fun y => Work.CR.Flat.Cauchy.bmPot (fun l' => Work.NN.Core.bmH χ η i l l') y)
              (Work.CR.Flat.polydisc 0 ρ'')
            ≤ ENNReal.ofReal (C k) *
                ∑ j, ∑ l, Work.CR.Flat.holderNorm k α (η j l) (Work.CR.Flat.polydisc 0 ρ) := by
  classical
  by_cases hdeg : ∃ j, ρ''' j ≤ 0
  · -- degenerate case: then `χ ≡ 0` and everything vanishes
    obtain ⟨j0, hj0⟩ := hdeg
    have hχ0 : ∀ z : Cn n, χ z = 0 := fun z => hχzero z ⟨j0, le_trans hj0 (norm_nonneg (z j0))⟩
    refine ⟨fun _ => 1, fun _ => one_pos, ?_⟩
    intro k η hη i l
    have hd0 : ∀ (t : Fin n) (w : Cn n), Work.CR.Flat.dbarCoord t χ w = 0 := fun t w =>
      dbarCoord_eq_zero_of_eventuallyEq_zero (Filter.Eventually.of_forall hχ0) t
    have hfun : (fun y : Cn n => Work.CR.Flat.Cauchy.bmPot (fun l' => bmH χ η i l l') y)
        = (0 : Cn n → ℂ) := by
      funext y
      simp only [Work.CR.Flat.Cauchy.bmPot]
      refine Finset.sum_eq_zero fun t _ => ?_
      have hzero : ∀ x : Cn n, Work.CR.Flat.Cauchy.bmKernel t x
          * bmH χ η i l t (y + x) = 0 := by
        intro x
        rw [show bmH χ η i l t (y + x) = 0 from by
          simp only [bmH, hd0, zero_mul, add_zero, sub_zero]]
        ring
      simp only [hzero]
      simp
    rw [hfun, Work.CR.Flat.holderNorm_zero]
    simp
  · -- main case: `ρ''' > 0`
    have hρ'''pos : ∀ j, 0 < ρ''' j := fun j => lt_of_not_ge (fun h => hdeg ⟨j, h⟩)
    have hρpos : ∀ j, 0 < ρ j := fun j => lt_trans (hρ'''pos j) (hρ'''ρ j)
    -- an intermediate multi-radius strictly between `ρ'''` and `ρ`
    have hmid_gt : ∀ j, ρ''' j < (ρ''' j + ρ j) / 2 := fun j => by linarith [hρ'''ρ j]
    have hmid_lt : ∀ j, (ρ''' j + ρ j) / 2 < ρ j := fun j => by linarith [hρ'''ρ j]
    have hmid_pos : ∀ j, 0 < (ρ''' j + ρ j) / 2 := fun j => by linarith [hρ'''pos j, hρpos j]
    -- `∂̄χ` vanishes on the closed exterior of the intermediate polydisc
    have hdbar_zero : ∀ (a : Fin n) (z : Cn n),
        (∃ i, (ρ''' i + ρ i) / 2 ≤ ‖z i‖) → Work.CR.Flat.dbarCoord a χ z = 0 := by
      intro a z hz
      obtain ⟨i', hi'⟩ := hz
      have hev : χ =ᶠ[𝓝 z] 0 := by
        have hopen : IsOpen {w : Cn n | ρ''' i' < ‖w i'‖} :=
          isOpen_lt continuous_const ((continuous_apply i').norm)
        filter_upwards [hopen.mem_nhds (lt_of_lt_of_le (hmid_gt i') hi')] with w hw
        exact hχzero w ⟨i', le_of_lt hw⟩
      exact dbarCoord_eq_zero_of_eventuallyEq_zero hev a
    have hcsd : ∀ a : Fin n, HasCompactSupport (fun z => Work.CR.Flat.dbarCoord a χ z) :=
      fun a => hasCompactSupport_of_vanishing_polydisc hmid_pos (fun z hz => hdbar_zero a z hz)
    have hmain : ∀ k : ℕ, ∃ D : ℝ, 0 < D ∧ ∀ (η : Fin n → Fin n → Cn n → ℂ),
        (∀ j l, ContDiff ℝ (k + 1) (η j l)) → ∀ i l : Fin n,
          Work.CR.Flat.holderNorm (k + 1) α
              (fun y => Work.CR.Flat.Cauchy.bmPot (fun l' => bmH χ η i l l') y)
              (Work.CR.Flat.polydisc 0 ρ'')
            ≤ ENNReal.ofReal D *
                ∑ j, ∑ l, Work.CR.Flat.holderNorm k α (η j l) (Work.CR.Flat.polydisc 0 ρ) := by
      intro k
      -- the Schauder input for the potential of compactly supported data
      obtain ⟨C₁, hC₁pos, hrow⟩ := Work.NN.Final.bmRow_bound (n := n) hα hα1 k (c := 0)
        (ρ := fun j => 2 * ρ'' j) (fun j => by linarith [hρ''pos j])
      -- multiplication by `∂̄_a χ` in the `C^{k,α}` scale on `polydisc 0 ρ`
      have hΩud : UniqueDiffOn ℝ (Work.CR.Flat.polydisc 0 ρ) :=
        (Work.CR.Flat.isOpen_polydisc 0 ρ).uniqueDiffOn
      have hconst : ∀ a : Fin n, ∃ Ca : ℝ, 0 < Ca ∧
          ∀ f : Cn n → ℂ, ContDiffOn ℝ (k : ℕ∞) f (Work.CR.Flat.polydisc 0 ρ) →
            Work.CR.Flat.holderNorm k α (fun z => Work.CR.Flat.dbarCoord a χ z * f z)
                (Work.CR.Flat.polydisc 0 ρ)
              ≤ ENNReal.ofReal Ca * Work.CR.Flat.holderNorm k α f (Work.CR.Flat.polydisc 0 ρ) :=
        fun a => Work.CR.Flat.Cauchy.holderNorm_mul_le_of_hasCompactSupport
          (Ω := Work.CR.Flat.polydisc 0 ρ) hΩud hα.le hα1.le
          ((contDiff_dbarCoord_of hχ_sm a).of_le (by simp)) (hcsd a)
      choose Ca hCapos hCa using hconst
      set C3 : ℝ := ∑ a, Ca a with hC3def
      have hC3pos : 0 < C3 := by
        rw [hC3def]
        exact lt_of_lt_of_le (hCapos (⟨0, hn⟩ : Fin n))
          (Finset.single_le_sum (f := fun a => Ca a) (fun a _ => le_of_lt (hCapos a))
            (Finset.mem_univ (⟨0, hn⟩ : Fin n)))
      have hC3nn : 0 ≤ C3 := le_of_lt hC3pos
      have hCa_le : ∀ a : Fin n, Ca a ≤ C3 := fun a => by
        rw [hC3def]
        exact Finset.single_le_sum (f := fun a => Ca a) (fun a _ => le_of_lt (hCapos a))
          (Finset.mem_univ a)
      refine ⟨C₁ * (C3 + C3 + C3) * ((n : ℝ) * n) + 1, by positivity, ?_⟩
      intro η hη i l
      set S : ℝ≥0∞ := ∑ j, ∑ l, Work.CR.Flat.holderNorm k α (η j l)
        (Work.CR.Flat.polydisc 0 ρ) with hSdef
      -- the `C^{k,α}` norm of `bmH` on the polydisc
      have hcont_ps : ∀ (a r s : Fin n),
          ContDiffOn ℝ (k : ℕ∞) (fun w => Work.CR.Flat.dbarCoord a χ w * η r s w)
            (Work.CR.Flat.polydisc 0 ρ) := fun a r s =>
        (((contDiff_dbarCoord_of hχ_sm a).of_le (by simp)).mul (hη r s)).contDiffOn.of_le (by simp)
      have hP : ∀ (a r s : Fin n),
          Work.CR.Flat.holderNorm k α (fun w => Work.CR.Flat.dbarCoord a χ w * η r s w)
              (Work.CR.Flat.polydisc 0 ρ)
            ≤ ENNReal.ofReal C3 * S := by
        intro a r s
        have h1 := hCa a (η r s) ((hη r s).contDiffOn.of_le (by simp))
        have hSle : Work.CR.Flat.holderNorm k α (η r s) (Work.CR.Flat.polydisc 0 ρ) ≤ S := by
          rw [hSdef]
          exact (Finset.single_le_sum (f := fun l =>
              Work.CR.Flat.holderNorm k α (η r l) (Work.CR.Flat.polydisc 0 ρ))
              (fun l _ => bot_le) (Finset.mem_univ s)).trans
            (Finset.single_le_sum (f := fun j => ∑ l,
              Work.CR.Flat.holderNorm k α (η j l) (Work.CR.Flat.polydisc 0 ρ))
              (fun j _ => bot_le) (Finset.mem_univ r))
        exact h1.trans (mul_le_mul (ENNReal.ofReal_le_ofReal (hCa_le a)) hSle bot_le bot_le)
      have hbmH_S : ∀ m : Fin n,
          Work.CR.Flat.holderNorm k α (fun w => bmH χ η i l m w) (Work.CR.Flat.polydisc 0 ρ)
            ≤ ENNReal.ofReal (C3 + C3 + C3) * S := by
        intro m
        have heq : (fun w => bmH χ η i l m w) =
            (fun w => Work.CR.Flat.dbarCoord m χ w * η i l w)
              + (fun w => Work.CR.Flat.dbarCoord i χ w * η l m w)
              + (-(fun w => Work.CR.Flat.dbarCoord l χ w * η i m w)) := by
          funext w; simp only [bmH, Pi.add_apply, Pi.neg_apply]; ring
        rw [heq]
        calc Work.CR.Flat.holderNorm k α
              ((fun w => Work.CR.Flat.dbarCoord m χ w * η i l w)
                + (fun w => Work.CR.Flat.dbarCoord i χ w * η l m w)
                + (-(fun w => Work.CR.Flat.dbarCoord l χ w * η i m w)))
              (Work.CR.Flat.polydisc 0 ρ)
            ≤ Work.CR.Flat.holderNorm k α
                ((fun w => Work.CR.Flat.dbarCoord m χ w * η i l w)
                  + (fun w => Work.CR.Flat.dbarCoord i χ w * η l m w))
                (Work.CR.Flat.polydisc 0 ρ)
              + Work.CR.Flat.holderNorm k α
                (-(fun w => Work.CR.Flat.dbarCoord l χ w * η i m w))
                (Work.CR.Flat.polydisc 0 ρ) :=
              Work.CR.Flat.Holder.holderNorm_add_le ((hcont_ps m i l).add (hcont_ps i l m))
                (hcont_ps l i m).neg hΩud
          _ ≤ (Work.CR.Flat.holderNorm k α (fun w => Work.CR.Flat.dbarCoord m χ w * η i l w)
                  (Work.CR.Flat.polydisc 0 ρ)
                + Work.CR.Flat.holderNorm k α (fun w => Work.CR.Flat.dbarCoord i χ w * η l m w)
                  (Work.CR.Flat.polydisc 0 ρ))
              + Work.CR.Flat.holderNorm k α (fun w => Work.CR.Flat.dbarCoord l χ w * η i m w)
                  (Work.CR.Flat.polydisc 0 ρ) :=
              add_le_add
                (Work.CR.Flat.Holder.holderNorm_add_le (hcont_ps m i l) (hcont_ps i l m) hΩud)
                (le_of_eq (Work.CR.Flat.Holder.holderNorm_neg (hcont_ps l i m) hΩud))
          _ ≤ (ENNReal.ofReal C3 * S + ENNReal.ofReal C3 * S) + ENNReal.ofReal C3 * S :=
              add_le_add (add_le_add (hP m i l) (hP i l m)) (hP l i m)
          _ = ENNReal.ofReal (C3 + C3 + C3) * S := by
              rw [← add_mul, ← ENNReal.ofReal_add hC3nn hC3nn, ← add_mul,
                ← ENNReal.ofReal_add (by linarith) (by linarith)]
      -- the same on all of `ℂⁿ`
      have hbmH_u : ∀ m : Fin n,
          Work.CR.Flat.holderNorm k α (fun w => bmH χ η i l m w) Set.univ
            ≤ ENNReal.ofReal (C3 + C3 + C3) * S := fun m =>
        (Work.CR.Flat.Cauchy.holderNorm_univ_le_holderNorm_polydisc_of_vanishing (c := 0)
          (r := fun j => (ρ''' j + ρ j) / 2) (r' := ρ) hmid_lt hα.le (fun z hz =>
            bmH_component_eq_zero hmid_gt χ hχzero η i l m z (by simpa using hz))).trans
          (hbmH_S m)
      -- apply the row estimate to the family `m ↦ bmH χ η i l m`
      have hb := hrow (fun (j m : Fin n) (w : Cn n) => bmH χ η i l m w)
        (fun j m => contDiff_bmH_component hχ_sm hη i l m)
        (fun j m z hz => by
          have hz' : ∃ i', 2 * ρ'' i' ≤ ‖z i'‖ := by simpa using hz
          exact bmH_component_eq_zero hρ'''2ρ'' χ hχzero η i l m z hz')
        ⟨0, hn⟩
      rw [show (fun i => 2 * ρ'' i / 2) = ρ'' from funext fun i => by ring] at hb
      calc Work.CR.Flat.holderNorm (k + 1) α
              (fun y => Work.CR.Flat.Cauchy.bmPot (fun l' => bmH χ η i l l') y)
              (Work.CR.Flat.polydisc 0 ρ'')
          ≤ ENNReal.ofReal C₁ * (∑ j : Fin n, ∑ m : Fin n,
              Work.CR.Flat.holderNorm k α (fun w => bmH χ η i l m w) Set.univ) := hb
        _ ≤ ENNReal.ofReal C₁ * (∑ _j : Fin n, ∑ _m : Fin n,
              ENNReal.ofReal (C3 + C3 + C3) * S) :=
              mul_le_mul_right (Finset.sum_le_sum fun j _ =>
                Finset.sum_le_sum fun m _ => hbmH_u m) _
        _ = ENNReal.ofReal (C₁ * (C3 + C3 + C3) * ((n : ℝ) * n)) * S := by
              simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
              rw [← ENNReal.ofReal_natCast n]
              rw [ofReal_mul_mul_assoc (by positivity : (0 : ℝ) ≤ (n : ℝ))
                    (by positivity : (0 : ℝ) ≤ (n : ℝ)) (ENNReal.ofReal (C3 + C3 + C3) * S),
                  ofReal_mul_mul_assoc (by positivity : (0 : ℝ) ≤ (n : ℝ) * (n : ℝ))
                    (by positivity : (0 : ℝ) ≤ C3 + C3 + C3) S,
                  ofReal_mul_mul_assoc hC₁pos.le (by positivity : (0 : ℝ) ≤ (n : ℝ) * (n : ℝ) * (C3 + C3 + C3)) S]
              congr 1
              ring_nf
        _ ≤ ENNReal.ofReal (C₁ * (C3 + C3 + C3) * ((n : ℝ) * n) + 1) * S := by
              refine mul_le_mul_left ?_ _
              exact ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right zero_le_one)
    choose C hC using hmain
    exact ⟨C, fun k => (hC k).1, fun k η hη i l => (hC k).2 η hη i l⟩

end

end Work.NN.Core
