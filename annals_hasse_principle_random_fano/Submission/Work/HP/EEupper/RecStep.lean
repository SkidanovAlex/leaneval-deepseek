import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.GonLib
import Submission.Work.HP.ball_count_schmidt
import Submission.Work.HP.FM.RecDefs
import Submission.Work.HP.FM.latStepAux
import Submission.Work.HP.lat_min_attained
import Submission.Work.HP.Sig2.Recursion

/-!
# The peeling step for Minkowski's second theorem

For an injective presentation `D.Φ : ℝ^R → E` of a rank-`R` lattice, a shortest primitive
coefficient vector `D.u` and its completion `D.v` to a `ℤ`-basis of `ℤ^R`, the projected
presentation `D.step` (orthogonal projection onto `D.p^⊥`) satisfies

`λ_{j+1}(D.Φ)/2 ≤ λ_j(D.step)`,  `j ≥ 1`.

This is the comparison of successive minima used in the recursion for Minkowski's second
theorem.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

noncomputable section

open Finset

namespace Work.HP.EEupper

open Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Elementary rounding -/

/-- Every real number is within `1/2` of an integer. -/
lemma exists_int_abs_sub_le_half (x : ℝ) : ∃ k : ℤ, |x - (k : ℝ)| ≤ 1 / 2 := by
  refine ⟨⌊x + 1 / 2⌋, ?_⟩
  have h1 : ((⌊x + 1 / 2⌋ : ℤ) : ℝ) ≤ x + 1 / 2 := Int.floor_le _
  have h2 : x + 1 / 2 < ((⌊x + 1 / 2⌋ : ℤ) : ℝ) + 1 := Int.lt_floor_add_one _
  rw [abs_le]
  constructor <;> linarith

/-! ## Elementary facts about `latMin` -/

/-- The successive minima are nonnegative. -/
lemma latMin_nonneg' {R : ℕ} (Φ : LatMap (ι := ι) R) (i : ℕ) : 0 ≤ latMin Φ i := by
  have hdef : latMin Φ i = sInf (setOf fun r : ℝ => 0 ≤ r ∧ ∃ f : Fin i → (Fin R → ℤ),
      LinearIndependent ℤ f ∧ ∀ k, ‖Φ (fun j => (f k j : ℝ))‖ ≤ r) := rfl
  rw [hdef]
  by_cases h : (setOf fun r : ℝ => 0 ≤ r ∧ ∃ f : Fin i → (Fin R → ℤ),
      LinearIndependent ℤ f ∧ ∀ k, ‖Φ (fun j => (f k j : ℝ))‖ ≤ r).Nonempty
  · exact le_csInf h fun r hr => hr.1
  · rw [Set.not_nonempty_iff_eq_empty.mp h, Real.sInf_empty]

/-- If `i` exceeds the rank `R` then `latMin Φ i = 0`. -/
lemma latMin_eq_zero_of_gt {R : ℕ} (Φ : LatMap (ι := ι) R) {i : ℕ} (hi : R < i) :
    latMin Φ i = 0 := by
  have hdef : latMin Φ i = sInf (setOf fun r : ℝ => 0 ≤ r ∧ ∃ f : Fin i → (Fin R → ℤ),
      LinearIndependent ℤ f ∧ ∀ k, ‖Φ (fun j => (f k j : ℝ))‖ ≤ r) := rfl
  rw [hdef]
  have hempty : ¬ (setOf fun r : ℝ => 0 ≤ r ∧ ∃ f : Fin i → (Fin R → ℤ),
      LinearIndependent ℤ f ∧ ∀ k, ‖Φ (fun j => (f k j : ℝ))‖ ≤ r).Nonempty := by
    rintro ⟨r, -, f, hfind, -⟩
    have hle := hfind.fintype_card_le_finrank
    rw [Fintype.card_fin] at hle
    have hR : Module.finrank ℤ (Fin R → ℤ) = R := by
      rw [Module.finrank_fintype_fun_eq_card ℤ, Fintype.card_fin]
    rw [hR] at hle
    omega
  rw [Set.not_nonempty_iff_eq_empty.mp hempty, Real.sInf_empty]

/-- The first successive minimum is bounded by the norm of any nonzero lattice vector. -/
lemma latMin_one_le_norm {R : ℕ} (Φ : LatMap (ι := ι) R) {y : Fin R → ℤ} (hy : y ≠ 0) :
    latMin Φ 1 ≤ ‖Φ (fun i => (y i : ℝ))‖ := by
  have hmem : ‖Φ (fun i => (y i : ℝ))‖ ∈ {r : ℝ | 0 ≤ r ∧ ∃ f : Fin 1 → (Fin R → ℤ),
      LinearIndependent ℤ f ∧ ∀ k, ‖Φ (fun i => (f k i : ℝ))‖ ≤ r} := by
    refine ⟨norm_nonneg _, fun _ => y, ?_, fun _ => le_rfl⟩
    rw [linearIndependent_unique_iff]
    exact hy
  have hbdd : BddBelow {r : ℝ | 0 ≤ r ∧ ∃ f : Fin 1 → (Fin R → ℤ),
      LinearIndependent ℤ f ∧ ∀ k, ‖Φ (fun i => (f k i : ℝ))‖ ≤ r} := ⟨0, fun r hr => hr.1⟩
  rw [latMin]
  exact csInf_le hbdd hmem

/-- A family of `j` independent lattice vectors whose norms are bounded by `latMin Φ j + ε`. -/
lemma exists_latMin_witness {R : ℕ} (Φ : LatMap (ι := ι) R) {j : ℕ} (hj : j ≤ R)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : Fin j → (Fin R → ℤ), LinearIndependent ℤ f ∧
      ∀ k, ‖Φ (fun i => (f k i : ℝ))‖ ≤ latMin Φ j + ε := by
  have hne := Work.HP.Sig2Rec.latMin_set_nonempty Φ hj
  have hlt : sInf {r : ℝ | 0 ≤ r ∧ ∃ f : Fin j → (Fin R → ℤ), LinearIndependent ℤ f ∧
      ∀ k, ‖Φ (fun i => (f k i : ℝ))‖ ≤ r} < latMin Φ j + ε := by
    rw [← latMin]; linarith
  obtain ⟨r, ⟨-, f, hfind, hfr⟩, hrlt⟩ := exists_lt_of_csInf_lt hne hlt
  exact ⟨f, hfind, fun k => le_trans (hfr k) hrlt.le⟩

/-- The realification of a `ℤ`-linear combination. -/
lemma toR_sum_smul_aux {κ : Type*} [Fintype κ] {R : ℕ} (a : κ → ℤ) (F : κ → (Fin R → ℤ)) :
    (fun k => ((∑ m, a m • F m) k : ℝ)) =
      ∑ m, (a m : ℝ) • (fun k => (F m k : ℝ)) := by
  funext k
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/-! ## The comparison of successive minima -/

/-- **The peeling comparison.**  If `D.u` is a shortest primitive vector of the lattice presented
by `D.Φ`, then the successive minima of the projected presentation `D.step` dominate those of
`D.Φ`, up to the factor `2`:
`λ_{j+1}(D.Φ) ≤ 2 λ_j(D.step)` for every `j ≥ 1`. -/
theorem latStepMinMine {R : ℕ} (D : Work.HP.FM.RecData R ι) (hu : ‖D.p‖ = latMin D.Φ 1)
    {j : ℕ} (hj : 1 ≤ j) :
    latMin D.Φ (j + 1) / 2 ≤ latMin D.step j := by
  by_cases hcase : j + 1 ≤ R
  · have hR2 : 2 ≤ R := by omega
    have hjR : j ≤ R - 1 := by omega
    have h1R : 1 ≤ R - 1 := by omega
    have hΨinj : Function.Injective D.step := D.step_injective
    have hμpos : 0 < latMin D.step j :=
      Work.HP.Sig2Rec.latMin_pos D.step hΨinj hj hjR
    have hμ1le : latMin D.step 1 ≤ latMin D.step j :=
      Work.HP.Sig2Rec.latMin_mono D.step hj hjR
    have hprojU_idem : ∀ x : EuclideanSpace ℝ ι, projU D.p (projU D.p x) = projU D.p x := by
      intro x
      rw [projU_apply D.p (projU D.p x), inner_projU_left D.p x, mul_zero, zero_smul, sub_zero]
    -- the decomposition of a vector along `D.p`
    have decomp : ∀ x : EuclideanSpace ℝ ι,
        x = projU D.p x + ((‖D.p‖ ^ 2)⁻¹ * inner ℝ x D.p) • D.p := by
      intro x
      rw [projU_apply]
      exact (sub_add_cancel _ _).symm
    -- (i) λ₁ ≤ (2/√3) λ_j(step)
    have hlam1_bound : ‖D.p‖ ≤ (2 / Real.sqrt 3) * latMin D.step j := by
      obtain ⟨t, ht0, htp, htmin⟩ := lat_min_attained h1R D.step hΨinj
      have hΨt_ne : D.step (fun i => (t i : ℝ)) ≠ 0 := by
        intro hzero
        have hpos := Work.HP.Sig2Rec.latMin_pos D.step hΨinj (le_refl 1) h1R
        rw [← htmin, hzero, norm_zero] at hpos
        exact lt_irrefl 0 hpos
      set w : Fin R → ℤ := ∑ i, t i • D.v i with hwdef
      have hstep1 : D.step (fun i => (t i : ℝ)) = projU D.p (D.Φ (fun k => (w k : ℝ))) :=
        D.step_cast t
      set c : ℝ := inner ℝ (D.Φ (fun k => (w k : ℝ))) D.p / ‖D.p‖ ^ 2 with hcdef
      have hc_eq : (‖D.p‖ ^ 2)⁻¹ * inner ℝ (D.Φ (fun k => (w k : ℝ))) D.p = c := by
        rw [hcdef, div_eq_inv_mul, mul_comm]
      have hdecomp : D.Φ (fun k => (w k : ℝ)) =
          projU D.p (D.Φ (fun k => (w k : ℝ))) + c • D.p := by
        have h := decomp (D.Φ (fun k => (w k : ℝ)))
        rw [hc_eq] at h
        exact h
      obtain ⟨k, hk⟩ := exists_int_abs_sub_le_half c
      set w' : Fin R → ℤ := w - k • D.u with hw'def
      have hw'cast : (fun i => (w' i : ℝ)) =
          (fun k => (w k : ℝ)) - (k : ℝ) • (fun i => (D.u i : ℝ)) := by
        funext i
        rw [hw'def]
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul,
          Int.cast_ofNat]
      have hΦw' : D.Φ (fun i => (w' i : ℝ)) =
          projU D.p (D.Φ (fun k => (w k : ℝ))) + (c - (k : ℝ)) • D.p := by
        calc D.Φ (fun i => (w' i : ℝ))
            = D.Φ (fun k => (w k : ℝ)) - (k : ℝ) • D.p := by
              rw [hw'cast, map_sub, map_smul]
              rfl
          _ = (projU D.p (D.Φ (fun k => (w k : ℝ))) + c • D.p) - (k : ℝ) • D.p := by
              conv_lhs => rw [hdecomp]
          _ = projU D.p (D.Φ (fun k => (w k : ℝ))) + (c - (k : ℝ)) • D.p := by
              rw [sub_smul]
              abel
      have hnorm : ‖D.Φ (fun i => (w' i : ℝ))‖ ^ 2 =
          ‖D.step (fun i => (t i : ℝ))‖ ^ 2 + ((c - (k : ℝ)) * ‖D.p‖) ^ 2 := by
        rw [hΦw', norm_sq_add_smul' D.p (c - (k : ℝ)) (D.Φ (fun k => (w k : ℝ))), ← hstep1]
      have hbound : ‖D.Φ (fun i => (w' i : ℝ))‖ ^ 2 ≤
          (latMin D.step j) ^ 2 + ((1 / 2) * ‖D.p‖) ^ 2 := by
        rw [hnorm]
        have h1 : ‖D.step (fun i => (t i : ℝ))‖ ^ 2 ≤ (latMin D.step j) ^ 2 := by
          rw [htmin]
          exact pow_le_pow_left₀ (latMin_nonneg' D.step 1) hμ1le 2
        have h2 : ((c - (k : ℝ)) * ‖D.p‖) ^ 2 ≤ ((1 / 2) * ‖D.p‖) ^ 2 := by
          have h3 : |(c - (k : ℝ)) * ‖D.p‖| ≤ (1 / 2) * ‖D.p‖ := by
            rw [abs_mul, abs_of_nonneg (norm_nonneg D.p)]
            exact mul_le_mul_of_nonneg_right hk (norm_nonneg D.p)
          rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2) * ‖D.p‖)]
          exact h3
        linarith
      have hw'ne : (fun i => (w' i : ℝ)) ≠ 0 := by
        intro hzero
        have h1 : projU D.p (D.Φ (fun i => (w' i : ℝ))) = D.step (fun i => (t i : ℝ)) := by
          rw [hΦw', projU_add_smul D.p (c - (k : ℝ)) (projU D.p (D.Φ (fun k => (w k : ℝ)))),
            hprojU_idem, ← hstep1]
        rw [hzero] at h1
        simp only [map_zero] at h1
        exact hΨt_ne h1.symm
      have hw'int_ne : w' ≠ 0 := by
        intro hzero
        refine hw'ne ?_
        rw [hzero]
        funext i
        simp
      have hlam_le : ‖D.p‖ ≤ ‖D.Φ (fun i => (w' i : ℝ))‖ := by
        have h := latMin_one_le_norm D.Φ hw'int_ne
        rwa [← hu] at h
      have hsq : ‖D.p‖ ^ 2 ≤ (latMin D.step j) ^ 2 + (1 / 2 * ‖D.p‖) ^ 2 :=
        le_trans (pow_le_pow_left₀ (norm_nonneg D.p) hlam_le 2) hbound
      have h4 : (3 / 4) * ‖D.p‖ ^ 2 ≤ (latMin D.step j) ^ 2 := by nlinarith [hsq]
      have hfac : (2 / Real.sqrt 3) ^ 2 = 4 / 3 := by
        rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
        norm_num
      have hkey : ‖D.p‖ ^ 2 ≤ ((2 / Real.sqrt 3) * latMin D.step j) ^ 2 := by
        rw [mul_pow, hfac]
        nlinarith [h4]
      calc ‖D.p‖ = Real.sqrt (‖D.p‖ ^ 2) := (Real.sqrt_sq (norm_nonneg D.p)).symm
        _ ≤ Real.sqrt (((2 / Real.sqrt 3) * latMin D.step j) ^ 2) := Real.sqrt_le_sqrt hkey
        _ = (2 / Real.sqrt 3) * latMin D.step j := by
            rw [Real.sqrt_sq]
            positivity
    -- (ii) the family of witnesses
    have hεpos : 0 < latMin D.step j / 2 := by linarith
    obtain ⟨T, hTind, hTnorm⟩ := exists_latMin_witness D.step hjR hεpos
    have hTbound : ∀ i, ‖D.step (fun m => (T i m : ℝ))‖ ≤ 3 / 2 * latMin D.step j := by
      intro i
      have h := hTnorm i
      linarith
    set W : Fin j → (Fin R → ℤ) := fun i => ∑ m, T i m • D.v m with hWdef
    have hstepT : ∀ i, D.step (fun m => (T i m : ℝ)) =
        projU D.p (D.Φ (fun k => (W i k : ℝ))) := fun i => D.step_cast (T i)
    have hround : ∀ i : Fin j, ∃ k : ℤ,
        |inner ℝ (D.Φ (fun k' => (W i k' : ℝ))) D.p / ‖D.p‖ ^ 2 - (k : ℝ)| ≤ 1 / 2 :=
      fun i => exists_int_abs_sub_le_half _
    let kk : Fin j → ℤ := fun i => Classical.choose (hround i)
    have hkk : ∀ i,
        |inner ℝ (D.Φ (fun k' => (W i k' : ℝ))) D.p / ‖D.p‖ ^ 2 - (kk i : ℝ)| ≤ 1 / 2 :=
      fun i => Classical.choose_spec (hround i)
    let W' : Fin j → (Fin R → ℤ) := fun i => W i - kk i • D.u
    have hdecompW : ∀ i, D.Φ (fun k => (W i k : ℝ)) =
        projU D.p (D.Φ (fun k => (W i k : ℝ))) +
          (inner ℝ (D.Φ (fun k => (W i k : ℝ))) D.p / ‖D.p‖ ^ 2) • D.p := by
      intro i
      have h := decomp (D.Φ (fun k => (W i k : ℝ)))
      rw [show (‖D.p‖ ^ 2)⁻¹ * inner ℝ (D.Φ (fun k => (W i k : ℝ))) D.p
          = inner ℝ (D.Φ (fun k => (W i k : ℝ))) D.p / ‖D.p‖ ^ 2 by
        rw [div_eq_inv_mul, mul_comm]] at h
      exact h
    have hΦWi : ∀ i, D.Φ (fun k => (W' i k : ℝ)) =
        projU D.p (D.Φ (fun k => (W i k : ℝ))) +
          ((inner ℝ (D.Φ (fun k => (W i k : ℝ))) D.p / ‖D.p‖ ^ 2) - (kk i : ℝ)) • D.p := by
      intro i
      have hcast : (fun k => (W' i k : ℝ)) =
          (fun k => (W i k : ℝ)) - (kk i : ℝ) • (fun k => (D.u k : ℝ)) := by
        funext k
        simp only [W', Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Int.cast_sub, Int.cast_mul,
          Int.cast_ofNat]
      calc D.Φ (fun k => (W' i k : ℝ))
          = D.Φ (fun k => (W i k : ℝ)) - (kk i : ℝ) • D.p := by
            rw [hcast, map_sub, map_smul]
            rfl
        _ = (projU D.p (D.Φ (fun k => (W i k : ℝ))) +
              (inner ℝ (D.Φ (fun k => (W i k : ℝ))) D.p / ‖D.p‖ ^ 2) • D.p)
            - (kk i : ℝ) • D.p := by
            conv_lhs => rw [hdecompW i]
        _ = projU D.p (D.Φ (fun k => (W i k : ℝ))) +
              ((inner ℝ (D.Φ (fun k => (W i k : ℝ))) D.p / ‖D.p‖ ^ 2) - (kk i : ℝ)) • D.p := by
            rw [sub_smul]
            abel
    have hWi_proj : ∀ i, projU D.p (D.Φ (fun k => (W' i k : ℝ))) =
        D.step (fun m => (T i m : ℝ)) := by
      intro i
      rw [hΦWi i, projU_add_smul D.p _ (projU D.p (D.Φ (fun k => (W i k : ℝ)))),
        hprojU_idem, ← hstepT i]
    have hWi_norm : ∀ i, ‖D.Φ (fun k => (W' i k : ℝ))‖ ≤ 2 * latMin D.step j := by
      intro i
      have hnorm : ‖D.Φ (fun k => (W' i k : ℝ))‖ ^ 2 =
          ‖D.step (fun m => (T i m : ℝ))‖ ^ 2 +
            (((inner ℝ (D.Φ (fun k => (W i k : ℝ))) D.p / ‖D.p‖ ^ 2) - (kk i : ℝ))
              * ‖D.p‖) ^ 2 := by
        rw [hΦWi i, norm_sq_add_smul' D.p _ (D.Φ (fun k => (W i k : ℝ))), ← hstepT i]
      have hb : ‖D.Φ (fun k => (W' i k : ℝ))‖ ^ 2 ≤ (2 * latMin D.step j) ^ 2 := by
        rw [hnorm]
        have h1 : ‖D.step (fun m => (T i m : ℝ))‖ ^ 2 ≤ (3 / 2 * latMin D.step j) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) (hTbound i) 2
        have h2 : (((inner ℝ (D.Φ (fun k => (W i k : ℝ))) D.p / ‖D.p‖ ^ 2) - (kk i : ℝ))
            * ‖D.p‖) ^ 2 ≤ ((1 / 2) * ‖D.p‖) ^ 2 := by
          have h3 : |((inner ℝ (D.Φ (fun k => (W i k : ℝ))) D.p / ‖D.p‖ ^ 2) - (kk i : ℝ))
              * ‖D.p‖| ≤ (1 / 2) * ‖D.p‖ := by
            rw [abs_mul, abs_of_nonneg (norm_nonneg D.p)]
            exact mul_le_mul_of_nonneg_right (hkk i) (norm_nonneg D.p)
          rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (1 / 2) * ‖D.p‖)]
          exact h3
        have hlam_sq : ‖D.p‖ ^ 2 ≤ ((2 / Real.sqrt 3) * latMin D.step j) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg D.p) hlam1_bound 2
        have hs3 : (2 / Real.sqrt 3) ^ 2 = 4 / 3 := by
          rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
          norm_num
        nlinarith [h1, h2, hlam_sq, hs3, hμpos]
      have h2μ : (0 : ℝ) ≤ 2 * latMin D.step j := by linarith
      have := sq_le_sq.mp hb
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg h2μ] at this
    -- (iii) independence of `(u, W')`
    let F : Fin (j + 1) → (Fin R → ℤ) := Fin.cons D.u W'
    have hF0 : F 0 = D.u := rfl
    have hFs : ∀ i : Fin j, F i.succ = W' i := fun i => rfl
    have hindep : LinearIndependent ℤ F := by
      rw [Fintype.linearIndependent_iff]
      intro a ha
      have h1 : ∑ m, (a m : ℝ) • projU D.p (D.Φ (fun k => (F m k : ℝ))) = 0 := by
        have h := congrArg (fun v : Fin R → ℤ => projU D.p (D.Φ (fun k => (v k : ℝ)))) ha
        rw [toR_sum_smul_aux a F] at h
        have hz : (fun k => (((0 : Fin R → ℤ)) k : ℝ)) = (0 : Fin R → ℝ) := by
          funext k; simp
        rw [hz, map_zero, map_zero] at h
        simpa only [map_sum, map_smul] using h
      have hu_term : projU D.p (D.Φ (fun k => (D.u k : ℝ))) = 0 := by
        rw [show D.Φ (fun k => (D.u k : ℝ)) = D.p from rfl, projU_self_eq_zero D.p D.p_ne_zero]
      have h2 : (a 0 : ℝ) • projU D.p (D.Φ (fun k => (D.u k : ℝ))) +
          ∑ i : Fin j, (a i.succ : ℝ) • projU D.p (D.Φ (fun k => (W' i k : ℝ))) = 0 := by
        rw [← h1, Fin.sum_univ_succ]
        simp only [F, Fin.cons_zero, Fin.cons_succ]
      have h3 : ∑ i : Fin j, (a i.succ : ℝ) • D.step (fun m => (T i m : ℝ)) = 0 := by
        rw [← h2, hu_term, smul_zero, zero_add]
        exact Finset.sum_congr rfl fun i _ => by rw [hWi_proj i]
      have h4 : D.step (∑ i : Fin j, (a i.succ : ℝ) • (fun m => (T i m : ℝ))) = 0 := by
        rw [← h3]
        simp only [map_sum, map_smul]
      have h5 : ∑ i : Fin j, (a i.succ : ℝ) • (fun m => (T i m : ℝ)) = 0 := by
        have h6 : D.step (∑ i : Fin j, (a i.succ : ℝ) • (fun m => (T i m : ℝ))) = D.step 0 := by
          rw [h4, map_zero]
        exact hΨinj h6
      have hT_int : ∑ i : Fin j, a i.succ • T i = 0 := by
        funext m
        have h6 := congrFun h5 m
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h6
        have h7 : ((∑ i : Fin j, a i.succ * T i m : ℤ) : ℝ) = 0 := by
          rw [Int.cast_sum]
          simpa only [Int.cast_mul, Int.cast_zero] using h6
        have h8 : (∑ i : Fin j, a i.succ • T i) m = ∑ i : Fin j, a i.succ * T i m := by
          simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [h8]
        exact_mod_cast h7
      have hTzero : ∀ i : Fin j, a i.succ = 0 :=
        Fintype.linearIndependent_iff.mp hTind (fun i => a i.succ) hT_int
      have hzero : a 0 • D.u = 0 := by
        have h := ha
        rw [Fin.sum_univ_succ] at h
        have h4' : ∑ i : Fin j, a i.succ • F i.succ = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [show F i.succ = W' i from rfl, hTzero i, zero_smul]
        rw [h4', add_zero] at h
        rwa [show F 0 = D.u from rfl] at h
      have h0 : a 0 = 0 := by
        by_contra hne
        have hk : ∀ k, D.u k = 0 := by
          intro k
          have h6 := congrFun hzero k
          simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at h6
          exact (mul_eq_zero.mp h6).resolve_left hne
        exact D.u_ne (funext hk)
      intro m
      rcases Fin.eq_zero_or_eq_succ m with h | ⟨i, rfl⟩
      · rw [h]; exact h0
      · exact hTzero i
    -- (iv) conclude
    have hmain : latMin D.Φ (j + 1) ≤ 2 * latMin D.step j := by
      rw [latMin]
      refine csInf_le ⟨0, fun r hr => hr.1⟩ ?_
      refine ⟨by linarith, F, hindep, fun m => ?_⟩
      rcases Fin.eq_zero_or_eq_succ m with h | ⟨i, rfl⟩
      · rw [h, hF0]
        change ‖D.p‖ ≤ 2 * latMin D.step j
        calc ‖D.p‖ ≤ (2 / Real.sqrt 3) * latMin D.step j := hlam1_bound
          _ ≤ 2 * latMin D.step j := by
              have hle : (2 / Real.sqrt 3) ≤ 2 := by
                rw [div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))]
                have h1 : (1 : ℝ) ≤ Real.sqrt 3 := Real.one_le_sqrt.mpr (by norm_num)
                linarith
              exact mul_le_mul_of_nonneg_right hle (le_of_lt hμpos)
      · rw [hFs i]
        exact hWi_norm i
    linarith
  · -- the degenerate case `j + 1 > R`
    have hz : latMin D.Φ (j + 1) = 0 := latMin_eq_zero_of_gt D.Φ (by omega)
    have hz2 : latMin D.step j = 0 := latMin_eq_zero_of_gt D.step (by omega)
    rw [hz, hz2]
    norm_num

end Work.HP.EEupper
