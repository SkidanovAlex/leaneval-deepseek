import Mathlib
import Submission.Work.CR.Flat.Holder
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Holder.holderNorm_comp_add
import Submission.Work.CR.Flat.Holder.holderNorm_add_le
import Submission.Work.CR.Flat.Polydisc.dbarCoord_comp_diagAffine
import Submission.Work.CR.Flat.Cauchy.dbar_oneshot_estimate
import Submission.Work.CR.Flat.Cauchy.holderNorm_le_sup_of_holomorphic_open
import Submission.Work.NN.Core.open_poincare_one
import Submission.Work.NN.Core.dbar_solver_open_ratio

set_option maxHeartbeats 2000000

namespace Work.CR.Flat.Cauchy

open scoped NNReal ENNReal ContDiff
open Set
open Work.CR.Flat

/-! ## Translation of the flat `∂̄`-operator and of polydiscs -/

/-- Chain rule for a translation: `∂̄_j (g ∘ (· + a)) = (∂̄_j g) ∘ (· + a)`. -/
lemma dbarCoord_translate {n : ℕ} (j : Fin n) {a z : Fin n → ℂ} {g : (Fin n → ℂ) → ℂ}
    (hg : DifferentiableAt ℝ g (a + z)) :
    dbarCoord j (fun y => g (a + y)) z = dbarCoord j g (a + z) := by
  have hg' : DifferentiableAt ℝ g (fun i => a i + (1 : ℂ) * z i) := by
    have e : (fun i : Fin n => a i + (1 : ℂ) * z i) = a + z := by funext i; simp
    rw [e]; exact hg
  have h := Polydisc.dbarCoord_comp_diagAffine (n := n) (a := fun _ => (1 : ℝ)) (b := a) j
    (U := g) (z := z) hg'
  simp only [Complex.ofReal_one, one_mul] at h
  exact h

/-- Translating a centred polydisc gives the polydisc with the translated centre. -/
lemma polydisc_translate_image {n : ℕ} (c : Fin n → ℂ) (r : Fin n → ℝ) :
    (fun z : Fin n → ℂ => c + z) '' polydisc 0 r = polydisc c r := by
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩ i
    simpa using (mem_polydisc.mp hy) i
  · intro hz
    refine ⟨z - c, ?_, ?_⟩
    · intro i
      simpa using (mem_polydisc.mp hz) i
    · funext i; simp

/-! ## The holomorphic estimate with an `ℝ≥0∞` bound on the supremum -/

/-- The local Cauchy estimate for holomorphic functions, stated with the `ℝ≥0∞`-valued
supremum of `‖h‖` on the outer polydisc (so that no finiteness hypothesis is needed). -/
lemma holderNorm_succ_le_sup_holomorphic {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ}
    {ρi ρo : Fin n → ℝ} (hmono : ∀ j, ρi j < ρo j) {α : ℝ} (hα : 0 ≤ α) (hα1 : α ≤ 1)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h : (Fin n → ℂ) → ℂ,
      ContDiffOn ℝ (((k+1 : ℕ)) : WithTop ℕ∞) h (polydisc c ρo) →
      (∀ j, ∀ z ∈ polydisc c ρo, dbarCoord j h z = 0) →
      holderNorm (k+1) α h (polydisc c ρi)
        ≤ ENNReal.ofReal C * (⨆ z ∈ polydisc c ρo, ENNReal.ofReal ‖h z‖) := by
  obtain ⟨C, hCpos, hC⟩ :=
    holderNorm_le_sup_of_holomorphic_bound hn (c := c) (ρi := ρi) (ρo := ρo) hmono hα hα1 k
  refine ⟨C, hCpos, ?_⟩
  intro h hsmooth hhol
  set S : ℝ≥0∞ := ⨆ z ∈ polydisc c ρo, ENNReal.ofReal ‖h z‖ with hS
  rcases eq_or_ne S ⊤ with htop | hne
  · rw [htop, ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr hCpos))]
    exact le_top
  · have hfin : S = ENNReal.ofReal S.toReal := (ENNReal.ofReal_toReal hne).symm
    have hbound : ∀ z ∈ polydisc c ρo, ‖h z‖ ≤ S.toReal := by
      intro z hz
      have h1 : ENNReal.ofReal ‖h z‖ ≤ S := le_iSup₂_of_le z hz le_rfl
      rw [hfin] at h1
      exact (ENNReal.ofReal_le_ofReal_iff ENNReal.toReal_nonneg).mp h1
    calc holderNorm (k+1) α h (polydisc c ρi)
        ≤ ENNReal.ofReal (C * S.toReal) :=
          hC h S.toReal ENNReal.toReal_nonneg hsmooth hhol hbound
      _ = ENNReal.ofReal C * S := by rw [ENNReal.ofReal_mul hCpos.le, ← hfin]

/-! ## The `C^0` interior Schauder estimate at the origin -/

private theorem center0 {n : ℕ} (hn : 0 < n) {ρi ρo : Fin n → ℝ}
    (hlt : ∀ j, ρi j < ρo j) (hρo : ∀ j, 0 < ρo j) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : (Fin n → ℂ) → ℂ) (f : Fin n → (Fin n → ℂ) → ℂ) (B : ℝ),
      ContDiff ℝ (k + 1) u → (∀ j, ContDiff ℝ (k + 1) (f j)) → IsClosedForm f →
      (∀ j, ∀ z : Fin n → ℂ, (∀ i, ‖z i‖ < ρo i) → dbarCoord j u z = f j z) →
      (∀ z : Fin n → ℂ, (∀ i, ‖z i‖ < ρo i) → ‖u z‖ ≤ B) →
      holderNorm (k + 1) α u (polydisc 0 ρi)
        ≤ ENNReal.ofReal C * ((∑ j, holderNorm k α (f j) (polydisc 0 ρo))
            + ENNReal.ofReal B) := by
  by_cases hpos : ∀ j, 0 < ρi j
  · -- ## non-degenerate case
    have hα0 : (0 : ℝ) ≤ α := le_of_lt hα
    have hα1' : α ≤ 1 := le_of_lt hα1
    set ρs : Fin n → ℝ := fun j => (ρi j + ρo j) / 2 with hρs
    have hρspos : ∀ j, 0 < ρs j := fun j => by rw [hρs]; linarith [hpos j, hρo j]
    have his : ∀ j, ρi j < ρs j := fun j => by rw [hρs]; linarith [hlt j]
    have hso : ∀ j, ρs j < ρo j := fun j => by rw [hρs]; linarith [hlt j]
    -- the solver on the intermediate polydisc, with an arbitrary radius loss
    obtain ⟨T, Csol, hCsolpos, hsolve, hest, hTsm, _hTsmOn⟩ :=
      Work.NN.Core.dbar_solver_open_ratio (n := n) hn hα hα1 hρo hρspos hso
    -- the chain of one-step estimates, leaving a `C^{0,α}` remainder
    obtain ⟨Cch, hCchpos, hchain⟩ :=
      Work.NN.Core.holderNorm_succ_le_of_dbar (n := n) hn hα hα1 k hρo hpos his
        (fun j => le_of_lt (hso j))
    -- the local Cauchy estimate for the holomorphic part
    obtain ⟨Chol, hCholpos, hhol⟩ :=
      holderNorm_succ_le_sup_holomorphic (n := n) hn (c := 0) (ρi := ρi) (ρo := ρs) his hα0 hα1' k
    refine ⟨Chol + Chol * Csol + Cch * (1 + Csol), by positivity, ?_⟩
    intro u f B hu hf hfcl heq hbound
    have hu' : ContDiff ℝ ((↑k : WithTop ℕ∞) + 1) u := by simpa using hu
    have hf' : ∀ j, ContDiff ℝ ((↑k : WithTop ℕ∞) + 1) (f j) := fun j => by simpa using hf j
    have hf1 : ∀ j, ContDiff ℝ 1 (f j) :=
      fun j => (hf j).of_le (by exact_mod_cast (show (1 : ℕ) ≤ k + 1 by omega))
    have hTsm' : ContDiff ℝ ((↑k : WithTop ℕ∞) + 1) (T f) := hTsm k f hf' hfcl
    have hwsm : ContDiff ℝ (k + 1) (T f) := by simpa using hTsm'
    have hwsolve : ∀ j z, z ∈ polydisc 0 ρs → dbarCoord j (T f) z = f j z :=
      hsolve f hf1 hfcl
    set S : ℝ≥0∞ := ∑ j, holderNorm k α (f j) (polydisc 0 ρo) with hS
    set S0 : ℝ≥0∞ := ∑ j, holderNorm 0 α (f j) (polydisc 0 ρo) with hS0
    have hS0S : S0 ≤ S := by
      rw [hS, hS0]
      exact Finset.sum_le_sum fun j _ => holderNorm_mono_k (Nat.zero_le k) α (f j) _
    have hw1 : holderNorm 1 α (T f) (polydisc 0 ρs) ≤ ENNReal.ofReal Csol * S0 := by
      rw [hS0]; exact hest f hf1 hfcl
    have hw0 : holderNorm 0 α (T f) (polydisc 0 ρs) ≤ ENNReal.ofReal Csol * S0 :=
      (holderNorm_mono_k (Nat.zero_le 1) α (T f) _).trans hw1
    -- the `C^{k+1,α}` bound for the particular solution
    have hw_bound : holderNorm (k + 1) α (T f) (polydisc 0 ρi)
        ≤ ENNReal.ofReal (Cch * (1 + Csol)) * S := by
      have h1 : holderNorm (k + 1) α (T f) (polydisc 0 ρi)
          ≤ ENNReal.ofReal Cch * (S + ENNReal.ofReal Csol * S0) := by
        rw [hS]
        exact (hchain (T f) f hwsm hf' hfcl hwsolve).trans
          (mul_le_mul_right (add_le_add le_rfl hw0) _)
      calc holderNorm (k + 1) α (T f) (polydisc 0 ρi)
          ≤ ENNReal.ofReal Cch * (S + ENNReal.ofReal Csol * S0) := h1
        _ ≤ ENNReal.ofReal Cch * (S + ENNReal.ofReal Csol * S) :=
            mul_le_mul_right (add_le_add le_rfl (mul_le_mul_right hS0S _)) _
        _ = ENNReal.ofReal Cch * (ENNReal.ofReal (1 + Csol) * S) := by
            congr 1
            rw [ENNReal.ofReal_add zero_le_one hCsolpos.le, ENNReal.ofReal_one, add_mul, one_mul]
        _ = ENNReal.ofReal (Cch * (1 + Csol)) * S := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hCchpos.le]
    -- the holomorphic remainder
    set hh : (Fin n → ℂ) → ℂ := fun z => u z - T f z with hhh
    have hhh_sm : ContDiff ℝ (k + 1) hh := by rw [hhh]; exact hu.sub hwsm
    have hhh_hol : ∀ j, ∀ z ∈ polydisc 0 ρs, dbarCoord j hh z = 0 := by
      intro j z hz
      have hzO : ∀ i, ‖z i‖ < ρo i := fun i => by simpa using lt_trans (hz i) (hso i)
      have hdu : DifferentiableAt ℝ u z := (hu.differentiable (by simp)).differentiableAt
      have hdw : DifferentiableAt ℝ (T f) z := (hwsm.differentiable (by simp)).differentiableAt
      rw [hhh]
      rw [dbarCoord_sub j u (T f) z hdu hdw, heq j z hzO, hwsolve j z hz, sub_self]
    have hsup_h : (⨆ z ∈ polydisc 0 ρs, ENNReal.ofReal ‖hh z‖)
        ≤ ENNReal.ofReal B + ENNReal.ofReal Csol * S0 := by
      have h1 : (⨆ z ∈ polydisc 0 ρs, ENNReal.ofReal ‖hh z‖)
          ≤ (⨆ z ∈ polydisc 0 ρs, ENNReal.ofReal ‖u z‖)
            + (⨆ z ∈ polydisc 0 ρs, ENNReal.ofReal ‖T f z‖) := by
        refine iSup₂_le fun z hz => ?_
        calc ENNReal.ofReal ‖hh z‖ = ENNReal.ofReal ‖u z - T f z‖ := by rw [hhh]
          _ ≤ ENNReal.ofReal (‖u z‖ + ‖T f z‖) := ENNReal.ofReal_le_ofReal (norm_sub_le _ _)
          _ = ENNReal.ofReal ‖u z‖ + ENNReal.ofReal ‖T f z‖ :=
              ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)
          _ ≤ _ := add_le_add (le_iSup₂_of_le z hz le_rfl) (le_iSup₂_of_le z hz le_rfl)
      have h2 : (⨆ z ∈ polydisc 0 ρs, ENNReal.ofReal ‖u z‖) ≤ ENNReal.ofReal B :=
        iSup₂_le fun z hz =>
          ENNReal.ofReal_le_ofReal (hbound z (fun i => by simpa using lt_trans (hz i) (hso i)))
      have h3 : (⨆ z ∈ polydisc 0 ρs, ENNReal.ofReal ‖T f z‖) ≤ ENNReal.ofReal Csol * S0 := by
        rw [← iterDerivNorm_zero]
        exact (iterDerivNorm_le_holderNorm 1 α (T f) _ (Nat.zero_le 1)).trans hw1
      exact h1.trans (add_le_add h2 h3)
    have hh_bound : holderNorm (k + 1) α hh (polydisc 0 ρi)
        ≤ ENNReal.ofReal Chol * (ENNReal.ofReal B + ENNReal.ofReal Csol * S0) :=
      (hhol hh hhh_sm.contDiffOn hhh_hol).trans (mul_le_mul_right hsup_h _)
    -- ## the assembly
    have hsplit : ENNReal.ofReal Chol * (ENNReal.ofReal B + ENNReal.ofReal Csol * S0)
          + ENNReal.ofReal (Cch * (1 + Csol)) * S
        ≤ ENNReal.ofReal (Chol + Chol * Csol + Cch * (1 + Csol)) * (S + ENNReal.ofReal B) := by
      have h1 : (0 : ℝ) ≤ Chol * Csol := mul_nonneg hCholpos.le hCsolpos.le
      have h2 : (0 : ℝ) ≤ Cch * (1 + Csol) := by positivity
      have hC1 : Chol ≤ Chol + Chol * Csol + Cch * (1 + Csol) := by linarith
      have hC2 : Chol * Csol + Cch * (1 + Csol) ≤ Chol + Chol * Csol + Cch * (1 + Csol) := by
        linarith [hCholpos.le]
      have e1 : ENNReal.ofReal Chol * (ENNReal.ofReal B + ENNReal.ofReal Csol * S0)
          = ENNReal.ofReal Chol * ENNReal.ofReal B
            + ENNReal.ofReal Chol * ENNReal.ofReal Csol * S0 := by
        rw [mul_add, mul_assoc]
      have e2 : ENNReal.ofReal Chol * ENNReal.ofReal Csol = ENNReal.ofReal (Chol * Csol) :=
        (ENNReal.ofReal_mul hCholpos.le).symm
      have e3 : ENNReal.ofReal (Chol * Csol) + ENNReal.ofReal (Cch * (1 + Csol))
          = ENNReal.ofReal (Chol * Csol + Cch * (1 + Csol)) :=
        (ENNReal.ofReal_add h1 h2).symm
      calc ENNReal.ofReal Chol * (ENNReal.ofReal B + ENNReal.ofReal Csol * S0)
              + ENNReal.ofReal (Cch * (1 + Csol)) * S
          = ENNReal.ofReal Chol * ENNReal.ofReal B
              + (ENNReal.ofReal Chol * ENNReal.ofReal Csol * S0
                 + ENNReal.ofReal (Cch * (1 + Csol)) * S) := by rw [e1, add_assoc]
        _ ≤ ENNReal.ofReal Chol * ENNReal.ofReal B
              + (ENNReal.ofReal (Chol * Csol) * S
                 + ENNReal.ofReal (Cch * (1 + Csol)) * S) := by
            refine add_le_add le_rfl (add_le_add ?_ le_rfl)
            rw [e2]
            exact mul_le_mul_right hS0S _
        _ = ENNReal.ofReal Chol * ENNReal.ofReal B
              + (ENNReal.ofReal (Chol * Csol) + ENNReal.ofReal (Cch * (1 + Csol))) * S := by
            rw [add_mul]
        _ = ENNReal.ofReal Chol * ENNReal.ofReal B
              + ENNReal.ofReal (Chol * Csol + Cch * (1 + Csol)) * S := by rw [e3]
        _ ≤ ENNReal.ofReal (Chol + Chol * Csol + Cch * (1 + Csol)) * ENNReal.ofReal B
              + ENNReal.ofReal (Chol + Chol * Csol + Cch * (1 + Csol)) * S :=
            add_le_add (mul_le_mul_left (ENNReal.ofReal_le_ofReal hC1) _)
              (mul_le_mul_left (ENNReal.ofReal_le_ofReal hC2) _)
        _ = ENNReal.ofReal (Chol + Chol * Csol + Cch * (1 + Csol)) * (ENNReal.ofReal B + S) :=
            (mul_add _ _ _).symm
        _ = ENNReal.ofReal (Chol + Chol * Csol + Cch * (1 + Csol)) * (S + ENNReal.ofReal B) := by
            congr 1
            exact add_comm _ _
    calc holderNorm (k + 1) α u (polydisc 0 ρi)
        = holderNorm (k + 1) α (fun z => hh z + T f z) (polydisc 0 ρi) := by
          rw [show (fun z => hh z + T f z) = u from funext fun z => by simp [hhh]]
      _ ≤ holderNorm (k + 1) α hh (polydisc 0 ρi)
            + holderNorm (k + 1) α (T f) (polydisc 0 ρi) :=
          Holder.holderNorm_add_le hhh_sm.contDiffOn hwsm.contDiffOn
            (isOpen_polydisc 0 ρi).uniqueDiffOn
      _ ≤ ENNReal.ofReal Chol * (ENNReal.ofReal B + ENNReal.ofReal Csol * S0)
            + ENNReal.ofReal (Cch * (1 + Csol)) * S := add_le_add hh_bound hw_bound
      _ ≤ ENNReal.ofReal (Chol + Chol * Csol + Cch * (1 + Csol)) * (S + ENNReal.ofReal B) := hsplit
  · -- ## degenerate case: the target polydisc is empty
    refine ⟨1, one_pos, ?_⟩
    intro u f B hu hf hfcl heq hbound
    simp only [not_forall, not_lt] at hpos
    obtain ⟨j0, hj0⟩ := hpos
    have hempty : polydisc (0 : Fin n → ℂ) ρi = ∅ := by
      ext z
      simp only [Set.mem_empty_iff_false, iff_false, mem_polydisc]
      intro h
      have h1 : ‖z j0‖ < ρi j0 := by simpa using h j0
      exact absurd h1 (not_lt.mpr (le_trans hj0 (norm_nonneg (z j0))))
    have hzero : holderNorm (k + 1) α u (polydisc 0 ρi) = 0 := by
      rw [hempty]
      simp [holderNorm, iterDerivNorm, holderSeminorm]
    rw [hzero]
    exact bot_le

/-! ## The estimate for an arbitrary centre, by translation -/

theorem dbar_interior_oneshot_C0 {n : ℕ} (hn : 0 < n) {c : Fin n → ℂ} {ρi ρo : Fin n → ℝ}
    (hlt : ∀ j, ρi j < ρo j) (hρo : ∀ j, 0 < ρo j) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : (Fin n → ℂ) → ℂ) (f : Fin n → (Fin n → ℂ) → ℂ) (B : ℝ),
      ContDiff ℝ (k + 1) u → (∀ j, ContDiff ℝ (k + 1) (f j)) → IsClosedForm f →
      (∀ j, ∀ z : Fin n → ℂ, (∀ i, ‖z i - c i‖ < ρo i) → dbarCoord j u z = f j z) →
      (∀ z : Fin n → ℂ, (∀ i, ‖z i - c i‖ < ρo i) → ‖u z‖ ≤ B) →
      holderNorm (k + 1) α u (polydisc c ρi)
        ≤ ENNReal.ofReal C * ((∑ j, holderNorm k α (f j) (polydisc c ρo))
            + ENNReal.ofReal B) := by
  obtain ⟨C, hC, hCprop⟩ := center0 (n := n) hn (ρi := ρi) (ρo := ρo) hlt hρo hα hα1 k
  refine ⟨C, hC, ?_⟩
  intro u f B hu hf hfcl heq hbound
  have htransl : ContDiff ℝ (k + 1) (fun z : Fin n → ℂ => c + z) :=
    contDiff_const.add contDiff_id
  set ut : (Fin n → ℂ) → ℂ := fun z => u (c + z) with hut
  set ft : Fin n → (Fin n → ℂ) → ℂ := fun j z => f j (c + z) with hft
  have hu' : ContDiff ℝ (k + 1) ut := by rw [hut]; exact hu.comp htransl
  have hf' : ∀ j, ContDiff ℝ (k + 1) (ft j) := by
    intro j; rw [hft]; exact (hf j).comp htransl
  have hfcl' : IsClosedForm ft := by
    intro j l z
    have hd1 : DifferentiableAt ℝ (f l) (c + z) := ((hf l).differentiable (by simp)).differentiableAt
    have hd2 : DifferentiableAt ℝ (f j) (c + z) := ((hf j).differentiable (by simp)).differentiableAt
    have h1 : dbarCoord l (ft j) z = dbarCoord l (f j) (c + z) := by
      rw [hft]; exact dbarCoord_translate l hd2
    have h2 : dbarCoord j (ft l) z = dbarCoord j (f l) (c + z) := by
      rw [hft]; exact dbarCoord_translate j hd1
    rw [h1, h2, hfcl j l (c + z)]
  have heq' : ∀ j z, (∀ i, ‖z i‖ < ρo i) → dbarCoord j ut z = ft j z := by
    intro j z hz
    have hd : DifferentiableAt ℝ u (c + z) := (hu.differentiable (by simp)).differentiableAt
    have h1 : dbarCoord j ut z = dbarCoord j u (c + z) := by
      rw [hut]; exact dbarCoord_translate j hd
    rw [h1, hft]
    exact heq j (c + z) (fun i => by simpa using hz i)
  have hbound' : ∀ z, (∀ i, ‖z i‖ < ρo i) → ‖ut z‖ ≤ B := by
    intro z hz
    rw [hut]
    exact hbound (c + z) (fun i => by simpa using hz i)
  have hres := hCprop ut ft B hu' hf' hfcl' heq' hbound'
  have e1 : holderNorm (k + 1) α ut (polydisc 0 ρi) = holderNorm (k + 1) α u (polydisc c ρi) := by
    rw [hut, Holder.holderNorm_comp_add, polydisc_translate_image]
  have e2 : (∑ j, holderNorm k α (ft j) (polydisc 0 ρo))
      = ∑ j, holderNorm k α (f j) (polydisc c ρo) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hft, Holder.holderNorm_comp_add, polydisc_translate_image]
  rw [e1, e2] at hres
  exact hres

end Work.CR.Flat.Cauchy

/-- The same statement under the (duplicated) namespace name appearing in the request. -/
theorem Work.CR.Flat.Cauchy.Work.CR.Flat.Cauchy.dbar_interior_oneshot_C0 {n : ℕ} (hn : 0 < n)
    {c : Fin n → ℂ} {ρi ρo : Fin n → ℝ}
    (hlt : ∀ j, ρi j < ρo j) (hρo : ∀ j, 0 < ρo j) {α : ℝ} (hα : 0 < α) (hα1 : α < 1)
    (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u : (Fin n → ℂ) → ℂ) (f : Fin n → (Fin n → ℂ) → ℂ) (B : ℝ),
      ContDiff ℝ (k + 1) u → (∀ j, ContDiff ℝ (k + 1) (f j)) → IsClosedForm f →
      (∀ j, ∀ z : Fin n → ℂ, (∀ i, ‖z i - c i‖ < ρo i) → dbarCoord j u z = f j z) →
      (∀ z : Fin n → ℂ, (∀ i, ‖z i - c i‖ < ρo i) → ‖u z‖ ≤ B) →
      holderNorm (k + 1) α u (polydisc c ρi)
        ≤ ENNReal.ofReal C * ((∑ j, holderNorm k α (f j) (polydisc c ρo))
            + ENNReal.ofReal B) :=
  _root_.Work.CR.Flat.Cauchy.dbar_interior_oneshot_C0 hn hlt hρo hα hα1 k
