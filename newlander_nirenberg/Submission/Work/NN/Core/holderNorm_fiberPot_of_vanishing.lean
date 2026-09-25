import Mathlib
import Submission.Work.NN.Core.fiberBeurling
import Submission.Work.NN.Core.VanishingDefs
import Submission.Work.NN.Core.holderNorm_zero_fiberPotAnn_le
import Submission.Work.NN.Core.fderiv_fiberPotAnn_apply
import Submission.Work.NN.Core.fiberPot_eq_fiberPotAnn
import Submission.Work.NN.Core.holderNorm_succ_fiberPotAnn_le
import Submission.Work.NN.Core.exists_holderNorm_wirtinger_le
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comm

noncomputable section
open scoped NNReal ENNReal
open MeasureTheory Set Filter

namespace Work.NN.Core

lemma ofReal_add_mul {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (H : ℝ≥0∞) :
    ENNReal.ofReal a * H + ENNReal.ofReal b * H = ENNReal.ofReal (a + b) * H := by
  rw [← add_mul, ENNReal.ofReal_add ha hb]

lemma contDiff_dCoord_of {n : ℕ} {η : Cn n → ℂ} {k : ℕ} (hη : ContDiff ℝ (k + 1) η)
    (i' : Fin n) : ContDiff ℝ k (fun y => Work.CR.Flat.dCoord i' η y) := by
  have h1 : ContDiff ℝ k (fderiv ℝ η) := hη.fderiv_right (by simp)
  have h2 : ContDiff ℝ k (dCoordLin i' ∘ fderiv ℝ η) := (dCoordLin i').contDiff.comp h1
  rw [show (fun y => Work.CR.Flat.dCoord i' η y) = dCoordLin i' ∘ fderiv ℝ η from by
    funext y; exact congrFun (dCoord_eq_comp i' η) y]
  exact h2

lemma contDiff_dbarCoord_of {n : ℕ} {η : Cn n → ℂ} {k : ℕ} (hη : ContDiff ℝ (k + 1) η)
    (i' : Fin n) : ContDiff ℝ k (fun y => Work.CR.Flat.dbarCoord i' η y) := by
  have h1 : ContDiff ℝ k (fderiv ℝ η) := hη.fderiv_right (by simp)
  have h2 : ContDiff ℝ k (Work.CR.Flat.Polydisc.dbarCoordPhi i' ∘ fderiv ℝ η) :=
    (Work.CR.Flat.Polydisc.dbarCoordPhi i').contDiff.comp h1
  rw [show (fun y => Work.CR.Flat.dbarCoord i' η y)
      = Work.CR.Flat.Polydisc.dbarCoordPhi i' ∘ fderiv ℝ η from by
    funext y; exact congrFun (Work.CR.Flat.Polydisc.dbarCoord_eq_comp i' η) y]
  exact h2

lemma holderNorm_dCoord_le {n : ℕ} (k : ℕ) {α : ℝ} {Ω : Set (Cn n)} (hΩ : IsOpen Ω)
    {f : Cn n → ℂ} (hf : ContDiffOn ℝ (k + 1) f Ω) (i' : Fin n) :
    Work.CR.Flat.holderNorm k α (fun x => Work.CR.Flat.dCoord i' f x) Ω
      ≤ Work.CR.Flat.holderNorm (k + 1) α f Ω := by
  have heq : Work.CR.Flat.holderNorm k α (fun x => Work.CR.Flat.dCoord i' f x) Ω
      = Work.CR.Flat.holderNorm k α (dCoordLin i' ∘ fderiv ℝ f) Ω :=
    holderNorm_congr (fun x _ => congrFun (dCoord_eq_comp i' f) x)
  rw [heq]
  exact holderNorm_comp_fderiv_le k α hΩ hf (dCoordLin i') (norm_dCoordLin_le i')

lemma holderNorm_dbarCoord_le {n : ℕ} (k : ℕ) {α : ℝ} {Ω : Set (Cn n)} (hΩ : IsOpen Ω)
    {f : Cn n → ℂ} (hf : ContDiffOn ℝ (k + 1) f Ω) (i' : Fin n) :
    Work.CR.Flat.holderNorm k α (fun x => Work.CR.Flat.dbarCoord i' f x) Ω
      ≤ Work.CR.Flat.holderNorm (k + 1) α f Ω := by
  have heq : Work.CR.Flat.holderNorm k α (fun x => Work.CR.Flat.dbarCoord i' f x) Ω
      = Work.CR.Flat.holderNorm k α (Work.CR.Flat.Polydisc.dbarCoordPhi i' ∘ fderiv ℝ f) Ω :=
    holderNorm_congr (fun x _ => congrFun (Work.CR.Flat.Polydisc.dbarCoord_eq_comp i' f) x)
  rw [heq]
  exact holderNorm_comp_fderiv_le k α hΩ hf (Work.CR.Flat.Polydisc.dbarCoordPhi i')
    (norm_dbarCoordPhi_le i')

theorem key_induction {n : ℕ} {R α : ℝ} (hR : 0 < R) (j : Fin n) (hα : 0 < α) (hα1 : α < 1)
    (m : ℕ) {r s : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i)
    (hsR : ∀ i, s i < R) :
    ∀ i : ℕ, i ≤ m → ∃ C : ℕ → ℝ, (∀ l, 0 < C l) ∧
      ∀ l : ℕ, i + l ≤ m → ∀ η : Cn n → ℂ, ContDiff ℝ (i + l) η →
        Work.CR.Flat.holderNorm i α (fiberPotAnn j l (fiberAnnulus (s j) R) η)
            (Work.CR.Flat.polydisc 0 r)
          ≤ ENNReal.ofReal (C l) *
            Work.CR.Flat.holderNorm (i + l) α η (fiberAccess r j R) := by
  classical
  have hB : ∀ l : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ η : Cn n → ℂ, Continuous η →
      Work.CR.Flat.holderNorm 0 α (fiberPotAnn j l (fiberAnnulus (s j) R) η)
          (Work.CR.Flat.polydisc 0 r)
        ≤ ENNReal.ofReal C * Work.CR.Flat.holderNorm 0 α η (fiberAccess r j R) :=
    fun l => holderNorm_zero_fiberPotAnn_le (R := R) hR j hα hα1 hr hrs hsR l
  choose Cb hCbpos hCbbd using hB
  intro i
  induction i with
  | zero =>
      intro _hm
      refine ⟨Cb, hCbpos, ?_⟩
      intro l _hl η hη
      refine le_trans (hCbbd l η hη.continuous) ?_
      exact mul_le_mul' le_rfl (Work.CR.Flat.holderNorm_mono_k (Nat.zero_le _) α η _)
  | succ i ih =>
      intro hsucc
      have hi : i ≤ m := by omega
      obtain ⟨Ci, hCipos, hCi⟩ := ih hi
      have hK : ∀ l : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ η : Cn n → ℂ, ContDiff ℝ (i + 1 + l) η →
          Work.CR.Flat.holderNorm (i + 1) α
              (fiberPotAnn j l (fiberAnnulus (s j) R) η) (Work.CR.Flat.polydisc 0 r)
            ≤ ENNReal.ofReal C *
              (Work.CR.Flat.holderNorm 0 α
                  (fiberPotAnn j l (fiberAnnulus (s j) R) η) (Work.CR.Flat.polydisc 0 r)
               + ∑ i' ∈ Finset.univ.erase j,
                   (Work.CR.Flat.holderNorm i α
                      (fiberPotAnn j l (fiberAnnulus (s j) R)
                        (fun y => Work.CR.Flat.dCoord i' η y)) (Work.CR.Flat.polydisc 0 r)
                    + Work.CR.Flat.holderNorm i α
                      (fiberPotAnn j l (fiberAnnulus (s j) R)
                        (fun y => Work.CR.Flat.dbarCoord i' η y)) (Work.CR.Flat.polydisc 0 r))
               + Work.CR.Flat.holderNorm i α
                  (fiberPotAnn j (l + 1) (fiberAnnulus (s j) R) η)
                  (Work.CR.Flat.polydisc 0 r)) :=
        fun l => holderNorm_succ_fiberPotAnn_le (R := R) hR j hα hα1 hr hrs hsR l i
      choose K hKpos hKbd using hK
      refine ⟨fun l => K l * (Cb l + (n : ℝ) * (2 * Ci l) + Ci (l + 1)) + 1,
        fun l => by
          have hK := hKpos l
          have hCb := hCbpos l
          have hCi := hCipos l
          have hCi1 := hCipos (l + 1)
          have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
          have h2 : (0:ℝ) ≤ (n : ℝ) * (2 * Ci l) := mul_nonneg hn (by linarith)
          have hX : (0:ℝ) ≤ Cb l + (n : ℝ) * (2 * Ci l) + Ci (l + 1) := by linarith
          nlinarith [mul_nonneg (le_of_lt hK) hX], ?_⟩
      intro l hl η hη
      have hile : i + l ≤ m := by omega
      set H : ℝ≥0∞ := Work.CR.Flat.holderNorm (i + 1 + l) α η (fiberAccess r j R) with hH
      have hpiece : ∀ i' ∈ Finset.univ.erase j,
          Work.CR.Flat.holderNorm i α
              (fiberPotAnn j l (fiberAnnulus (s j) R) (fun y => Work.CR.Flat.dCoord i' η y))
              (Work.CR.Flat.polydisc 0 r)
            + Work.CR.Flat.holderNorm i α
              (fiberPotAnn j l (fiberAnnulus (s j) R) (fun y => Work.CR.Flat.dbarCoord i' η y))
              (Work.CR.Flat.polydisc 0 r)
          ≤ ENNReal.ofReal (2 * Ci l) * H := by
        intro i' hi'
        have hη' : ContDiff ℝ ((i + l) + 1) η := by
          rw [add_right_comm]
          exact hη
        have h1 : Work.CR.Flat.holderNorm i α
              (fiberPotAnn j l (fiberAnnulus (s j) R) (fun y => Work.CR.Flat.dCoord i' η y))
              (Work.CR.Flat.polydisc 0 r) ≤ ENNReal.ofReal (Ci l) * H := by
          refine le_trans (hCi l hile (fun y => Work.CR.Flat.dCoord i' η y)
            (contDiff_dCoord_of hη' i')) ?_
          have hmono : Work.CR.Flat.holderNorm (i + l) α
                (fun y => Work.CR.Flat.dCoord i' η y) (fiberAccess r j R) ≤ H := by
            rw [hH]
            refine le_trans (holderNorm_dCoord_le (i + l) (fiberAccess_isOpen r j R)
              hη'.contDiffOn i') ?_
            exact le_of_eq (by rw [add_right_comm])
          exact mul_le_mul' le_rfl hmono
        have h2 : Work.CR.Flat.holderNorm i α
              (fiberPotAnn j l (fiberAnnulus (s j) R) (fun y => Work.CR.Flat.dbarCoord i' η y))
              (Work.CR.Flat.polydisc 0 r) ≤ ENNReal.ofReal (Ci l) * H := by
          refine le_trans (hCi l hile (fun y => Work.CR.Flat.dbarCoord i' η y)
            (contDiff_dbarCoord_of hη' i')) ?_
          have hmono : Work.CR.Flat.holderNorm (i + l) α
                (fun y => Work.CR.Flat.dbarCoord i' η y) (fiberAccess r j R) ≤ H := by
            rw [hH]
            refine le_trans (holderNorm_dbarCoord_le (i + l) (fiberAccess_isOpen r j R)
              hη'.contDiffOn i') ?_
            exact le_of_eq (by rw [add_right_comm])
          exact mul_le_mul' le_rfl hmono
        have hCi_nn : (0:ℝ) ≤ Ci l := le_of_lt (hCipos l)
        rw [show (2:ℝ) * Ci l = Ci l + Ci l from by ring, ← ofReal_add_mul hCi_nn hCi_nn]
        exact add_le_add h1 h2
      have hlast : Work.CR.Flat.holderNorm i α
            (fiberPotAnn j (l + 1) (fiberAnnulus (s j) R) η) (Work.CR.Flat.polydisc 0 r)
          ≤ ENNReal.ofReal (Ci (l + 1)) * H := by
        have hη2 : ContDiff ℝ (i + (l + 1)) η := by
          rw [← add_assoc, add_right_comm]
          exact hη
        refine le_trans (hCi (l + 1) (by omega) η hη2) ?_
        rw [hH]
        refine mul_le_mul' le_rfl (le_of_eq ?_)
        rw [← add_assoc, add_right_comm]
      have h0 : Work.CR.Flat.holderNorm 0 α
            (fiberPotAnn j l (fiberAnnulus (s j) R) η) (Work.CR.Flat.polydisc 0 r)
          ≤ ENNReal.ofReal (Cb l) * H :=
        le_trans (hCbbd l η hη.continuous)
          (mul_le_mul' le_rfl (Work.CR.Flat.holderNorm_mono_k (Nat.zero_le _) α η _))
      have hstep := hKbd l η hη
      refine le_trans hstep ?_
      have hsum : (∑ i' ∈ Finset.univ.erase j,
            (Work.CR.Flat.holderNorm i α
                (fiberPotAnn j l (fiberAnnulus (s j) R) (fun y => Work.CR.Flat.dCoord i' η y))
                (Work.CR.Flat.polydisc 0 r)
              + Work.CR.Flat.holderNorm i α
                (fiberPotAnn j l (fiberAnnulus (s j) R)
                  (fun y => Work.CR.Flat.dbarCoord i' η y)) (Work.CR.Flat.polydisc 0 r)))
          ≤ ENNReal.ofReal ((n : ℝ) * (2 * Ci l)) * H := by
        calc (∑ i' ∈ Finset.univ.erase j, _)
            ≤ ∑ _i' ∈ Finset.univ.erase j, ENNReal.ofReal (2 * Ci l) * H :=
              Finset.sum_le_sum hpiece
          _ = ((Finset.univ.erase j).card : ENNReal) * (ENNReal.ofReal (2 * Ci l) * H) := by
              rw [Finset.sum_const, nsmul_eq_mul]
          _ = ENNReal.ofReal (((Finset.univ.erase j).card : ℕ) : ℝ)
                * (ENNReal.ofReal (2 * Ci l) * H) := by
              rw [ENNReal.ofReal_natCast]
          _ ≤ ENNReal.ofReal (n : ℝ) * (ENNReal.ofReal (2 * Ci l) * H) :=
              mul_le_mul' (ENNReal.ofReal_le_ofReal (by
                have hc := Finset.card_erase_le (s := Finset.univ) (a := j)
                simp only [Finset.card_univ, Fintype.card_fin] at hc
                exact_mod_cast hc)) le_rfl
          _ = ENNReal.ofReal ((n : ℝ) * (2 * Ci l)) * H := by
              rw [← mul_assoc, ← ENNReal.ofReal_mul (by have := hCipos l; linarith)]
      have hbig : Work.CR.Flat.holderNorm 0 α
              (fiberPotAnn j l (fiberAnnulus (s j) R) η) (Work.CR.Flat.polydisc 0 r)
            + (∑ i' ∈ Finset.univ.erase j,
                (Work.CR.Flat.holderNorm i α
                    (fiberPotAnn j l (fiberAnnulus (s j) R) (fun y => Work.CR.Flat.dCoord i' η y))
                    (Work.CR.Flat.polydisc 0 r)
                  + Work.CR.Flat.holderNorm i α
                    (fiberPotAnn j l (fiberAnnulus (s j) R)
                      (fun y => Work.CR.Flat.dbarCoord i' η y)) (Work.CR.Flat.polydisc 0 r)))
            + Work.CR.Flat.holderNorm i α
              (fiberPotAnn j (l + 1) (fiberAnnulus (s j) R) η) (Work.CR.Flat.polydisc 0 r)
          ≤ ENNReal.ofReal (Cb l + (n : ℝ) * (2 * Ci l) + Ci (l + 1)) * H := by
        have hCb_nn : (0:ℝ) ≤ Cb l := le_of_lt (hCbpos l)
        have hCi_nn : (0:ℝ) ≤ Ci l := le_of_lt (hCipos l)
        have hCil1_nn : (0:ℝ) ≤ Ci (l + 1) := le_of_lt (hCipos (l + 1))
        have hn_nn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
        have hAB : (0:ℝ) ≤ Cb l + (n : ℝ) * (2 * Ci l) := by
          have h2 : (0:ℝ) ≤ (n : ℝ) * (2 * Ci l) := mul_nonneg hn_nn (by linarith)
          linarith
        have h2n : (0:ℝ) ≤ (n : ℝ) * (2 * Ci l) := mul_nonneg hn_nn (by linarith)
        rw [show Cb l + (n : ℝ) * (2 * Ci l) + Ci (l + 1)
              = (Cb l + (n : ℝ) * (2 * Ci l)) + Ci (l + 1) from rfl,
          ← ofReal_add_mul hAB hCil1_nn, ← ofReal_add_mul hCb_nn h2n]
        exact add_le_add (add_le_add h0 hsum) hlast
      have hn : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have h2n : (0:ℝ) ≤ (n : ℝ) * (2 * Ci l) := mul_nonneg hn (by have := hCipos l; linarith)
      have hXnn : (0:ℝ) ≤ Cb l + (n : ℝ) * (2 * Ci l) + Ci (l + 1) := by
        have := hCbpos l; have := hCipos (l + 1); linarith
      have hKX : (0:ℝ) ≤ K l * (Cb l + (n : ℝ) * (2 * Ci l) + Ci (l + 1)) :=
        mul_nonneg (le_of_lt (hKpos l)) hXnn
      refine le_trans (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) hbig) ?_
      dsimp only
      rw [ENNReal.ofReal_add hKX (by norm_num : (0:ℝ) ≤ 1), add_mul, ENNReal.ofReal_one, one_mul,
        ENNReal.ofReal_mul (le_of_lt (hKpos l)), ← mul_assoc]
      exact le_self_add

/-- The fixed-disc potential of data vanishing on `polydisc 0 s` (with `r i < s i < R`) is estimated on `polydisc 0 r` by the data's `C^{m,α}` norm on the access polydisc `fiberAccess r j R`: for `z` near `polydisc 0 r` the integrand `v (z[j:=w])/(w - z j)` vanishes for `‖w‖ < s j`, so the integral runs over the fixed region `s j ≤ ‖w‖ < R` on which the Cauchy kernel is smooth and all derivatives may be taken under the integral sign.

Suggested route: rewrite `fiberPot R j v = -(1/π) ∫_{w in {w | s j ≤ ‖w‖ ∧ ‖w‖ < R}} v (z[j:=w])/(w - z j) dw` for `z` in a neighbourhood of `polydisc 0 r` (the integrand vanishes on the rest of the disc, and `{(z,w) | ‖z - z'‖ < ...}` stays inside `polydisc 0 s`); then differentiate under the integral sign repeatedly (Mathlib's `hasFDerivAt_integral_of_dominated_loc_of_deriv_le`, or induction on `m`), bounding the derivatives of `w ↦ v (z[j:=w])/(w - z j)` by the sup norms and `α`-seminorms of the derivatives of `v` on `fiberAccess r j R` (all accessed points lie there) times bounded kernel factors (the kernel is smooth on `s j ≤ ‖w‖ < R`, `‖z j‖ < r j < s j`). -/
theorem holderNorm_fiberPot_of_vanishing {n : ℕ} {R α : ℝ} (hR : 0 < R) (j : Fin n) (hα : 0 < α)
    (hα1 : α < 1) (m : ℕ) {r s : Fin n → ℝ} (hr : ∀ i, 0 < r i) (hrs : ∀ i, r i < s i)
    (hsR : ∀ i, s i < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ v : Cn n → ℂ, ContDiff ℝ m v →
      (∀ z : Cn n, (∀ i, ‖z i‖ < s i) → v z = 0) →
      Work.CR.Flat.holderNorm m α (fiberPot R j v) (Work.CR.Flat.polydisc 0 r)
        ≤ ENNReal.ofReal C * Work.CR.Flat.holderNorm m α v (fiberAccess r j R) := by
  classical
  obtain ⟨C, hCpos, hCbd⟩ :=
    key_induction (n := n) (R := R) (α := α) (r := r) (s := s)
      hR j hα hα1 m hr hrs hsR m (le_refl m)
  refine ⟨C 0, hCpos 0, ?_⟩
  intro v hv hvan
  have heq : Set.EqOn (fiberPot R j v) (fiberPotAnn j 0 (fiberAnnulus (s j) R) v)
      (Work.CR.Flat.polydisc 0 r) :=
    fiberPot_eq_fiberPotAnn hrs (hsR j) hvan hv.continuous
  have hcongr := holderNorm_congr (k := m) (α := α)
    (Ω := Work.CR.Flat.polydisc (0 : Cn n) r) (fun x hx => heq hx)
  rw [hcongr]
  have h := hCbd 0 (by omega) v (by simpa using hv)
  simpa only [add_zero] using h


end Work.NN.Core
