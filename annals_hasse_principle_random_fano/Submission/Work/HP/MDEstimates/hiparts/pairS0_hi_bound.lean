import Mathlib
import Submission.Work.HP.MDEstimates.hiparts.HiDefs
import Submission.Work.HP.MDEstimates.ballCount_R0_M
import Submission.Work.HP.MDEstimates.detGam_lower
import Submission.Work.HP.MDEstimates.dmin_facts
import Submission.Work.HP.MDEstimates.detL_le_prod_lam
import Submission.Work.HP.Sig2.lam_Gam_le_muXY
import Submission.Work.HP.Sig2.gam_rank_det
import Submission.Work.HP.Sig2.nu_indep
import Submission.Work.HP.Sig2.omega_li
import Submission.Work.HP.Sig2.mu_div_det_le
import Submission.Work.HP.Q44Child.witness_class_count
import Submission.Work.HP.MDBasic.mem_Gam_iff
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.MDCommon

set_option maxHeartbeats 1000000

namespace Work.HP.MDEstimates.hiparts

open Work.HP

/-- `pairS0` is a set of lattice points of `Gam d n x y` in the ball of radius `A`, hence is at
most the corresponding `ballCount`.  (Copy of `Work.HP.Sig2.pairS0_le_ballCount`, which lives in
a module that cannot be imported here because of a pre-existing name clash.) -/
private lemma pairS0_le_ballCount (d n : ℕ) (A : ℝ)
    (p : (Fin (n + 1) → ℤ) × (Fin (n + 1) → ℤ)) :
    pairS0 d n A p ≤ (ballCount (Gam d n p.1 p.2) A : ℝ) := by
  have hsub : {a ∈ primSet d n A (fun _ => True) |
      formEval d n a p.1 = 0 ∧ formEval d n a p.2 = 0} ⊆
      {v : Mon d n → ℤ | v ∈ Gam d n p.1 p.2 ∧ eNorm v ≤ A} := by
    rintro a ⟨⟨-, hnorm, -⟩, h1, h2⟩
    exact ⟨(Work.HP.MDBasic.mem_Gam_iff d n p.1 p.2 a).mpr ⟨h1, h2⟩, hnorm⟩
  have hfin : ({v : Mon d n → ℤ | v ∈ Gam d n p.1 p.2 ∧ eNorm v ≤ A}).Finite :=
    (Work.HP.MDBasic.finite_eNorm_le A).subset (fun v hv => hv.2)
  have h := Set.ncard_le_ncard hsub hfin
  simp only [pairS0, ballCount]
  exact_mod_cast h

/-- A vector of `Xi 4 4 B` has Euclidean norm at most `B`. -/
private lemma eNorm_le_of_mem_Xi44 {B : ℝ} {v : Fin 5 → ℤ}
    (hv : eNorm v ≤ B ^ (1 / ((4 : ℝ) + 1 - 4))) : eNorm v ≤ B := by
  rwa [show (1 : ℝ) / ((4 : ℝ) + 1 - 4) = 1 by norm_num, Real.rpow_one] at hv

/-- **Arithmetic of one `R0`-term.**  Combines the Lemma-R0 bound (with the sharp short-vector
parameter `M = λ₁/2`, whose second term is `(2A/λ₁)^{67-R0}`) with the Case-I conversion
`μ^{R0}/det Γ ≤ 48^{R0} B^{2(R0-4)} 𝔡₃^{-R0} Cdet`, and produces the corresponding `hiCell`
term with the uniform constant `48^{67} Cdet + 1`. -/
private lemma hi_pointwise (K1 Cdet A B d3 l mu G bc : ℝ) (R0 : ℕ)
    (hK1 : 0 < K1) (hCdet : 0 < Cdet)
    (hA : 1 ≤ A) (hB : 0 ≤ B) (hd3 : 0 < d3) (hl : 0 < l)
    (hR04 : 4 ≤ R0) (hR067 : R0 ≤ 67)
    (hmudiv : mu ^ R0 / G ≤ (48 : ℝ) ^ R0 * B ^ (2 * (R0 - 4)) * d3 ^ (-(R0 : ℝ)) * Cdet)
    (hbc : bc ≤ K1 * (A ^ (68 - R0) * mu ^ R0 / G + (A / (l / 2)) ^ (67 - R0))) :
    bc ≤ K1 * ((48 : ℝ) ^ 67 * Cdet + 1) * hiCell A B d3 l R0 := by
  have hAnn : (0 : ℝ) ≤ A ^ (68 - R0) := pow_nonneg (by linarith) _
  have hBnn : (0 : ℝ) ≤ B ^ (2 * R0 - 8) := pow_nonneg hB _
  have hd3nn : (0 : ℝ) ≤ d3 ^ (-(R0 : ℝ)) := Real.rpow_nonneg hd3.le _
  have halnn : (0 : ℝ) ≤ (A / (l / 2)) ^ (67 - R0) :=
    pow_nonneg (div_nonneg (by linarith) (by linarith)) _
  have h2Ann : (0 : ℝ) ≤ (2 * A / l) ^ (67 - R0) :=
    pow_nonneg (div_nonneg (by linarith) hl.le) _
  have hT1nn : (0 : ℝ) ≤ A ^ (68 - R0) * B ^ (2 * R0 - 8) * d3 ^ (-(R0 : ℝ)) :=
    mul_nonneg (mul_nonneg hAnn hBnn) hd3nn
  -- the dominating constant is at least one
  have hKc1 : (1 : ℝ) ≤ (48 : ℝ) ^ 67 * Cdet + 1 := by
    have h : (0 : ℝ) ≤ (48 : ℝ) ^ 67 * Cdet := mul_nonneg (pow_nonneg (by norm_num) _) hCdet.le
    linarith
  -- first term
  have ht1 : A ^ (68 - R0) * mu ^ R0 / G ≤ ((48 : ℝ) ^ 67 * Cdet + 1) *
      (A ^ (68 - R0) * B ^ (2 * R0 - 8) * d3 ^ (-(R0 : ℝ))) := by
    have h1 : A ^ (68 - R0) * (mu ^ R0 / G)
        ≤ A ^ (68 - R0) * ((48 : ℝ) ^ R0 * B ^ (2 * (R0 - 4)) * d3 ^ (-(R0 : ℝ)) * Cdet) :=
      mul_le_mul_of_nonneg_left hmudiv hAnn
    have h2 : A ^ (68 - R0) * ((48 : ℝ) ^ R0 * B ^ (2 * (R0 - 4)) * d3 ^ (-(R0 : ℝ)) * Cdet)
        = ((48 : ℝ) ^ R0 * Cdet) * (A ^ (68 - R0) * B ^ (2 * R0 - 8) * d3 ^ (-(R0 : ℝ))) := by
      rw [show 2 * (R0 - 4) = 2 * R0 - 8 by omega]
      ring
    have h3 : (48 : ℝ) ^ R0 * Cdet ≤ (48 : ℝ) ^ 67 * Cdet := by
      have hb1 : (1 : ℝ) ≤ 48 := by norm_num
      exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hb1 hR067) hCdet.le
    have h4 : (48 : ℝ) ^ R0 * Cdet ≤ (48 : ℝ) ^ 67 * Cdet + 1 := by linarith
    calc A ^ (68 - R0) * mu ^ R0 / G
        = A ^ (68 - R0) * (mu ^ R0 / G) := by ring
      _ ≤ A ^ (68 - R0) * ((48 : ℝ) ^ R0 * B ^ (2 * (R0 - 4)) * d3 ^ (-(R0 : ℝ)) * Cdet) := h1
      _ = ((48 : ℝ) ^ R0 * Cdet) * (A ^ (68 - R0) * B ^ (2 * R0 - 8) * d3 ^ (-(R0 : ℝ))) := h2
      _ ≤ ((48 : ℝ) ^ 67 * Cdet + 1) * (A ^ (68 - R0) * B ^ (2 * R0 - 8) * d3 ^ (-(R0 : ℝ))) :=
          mul_le_mul_of_nonneg_right h4 hT1nn
  -- second term
  have ht2 : (A / (l / 2)) ^ (67 - R0) ≤ ((48 : ℝ) ^ 67 * Cdet + 1) * (2 * A / l) ^ (67 - R0) := by
    have heq : A / (l / 2) = 2 * A / l := by
      rw [div_div_eq_mul_div, mul_comm]
    rw [heq]
    exact le_mul_of_one_le_left h2Ann hKc1
  calc bc ≤ K1 * (A ^ (68 - R0) * mu ^ R0 / G + (A / (l / 2)) ^ (67 - R0)) := hbc
    _ ≤ K1 * (((48 : ℝ) ^ 67 * Cdet + 1) *
            (A ^ (68 - R0) * B ^ (2 * R0 - 8) * d3 ^ (-(R0 : ℝ)))
          + ((48 : ℝ) ^ 67 * Cdet + 1) * (2 * A / l) ^ (67 - R0)) :=
        mul_le_mul_of_nonneg_left (add_le_add ht1 ht2) hK1.le
    _ = K1 * ((48 : ℝ) ^ 67 * Cdet + 1) *
          (A ^ (68 - R0) * B ^ (2 * R0 - 8) * d3 ^ (-(R0 : ℝ)) + (2 * A / l) ^ (67 - R0)) := by
        ring
    _ = K1 * ((48 : ℝ) ^ 67 * Cdet + 1) * hiCell A B d3 l R0 := by
        unfold hiCell
        rfl

/-- **Pointwise Lemma-R0 bound for a Case-I pair, in the form needed for the `𝔡₃ > A^{1/20}`
part of the case-`I` sum at `(d,n) = (4,4)`.**

For `p = (x,y) ∈ Omega 4 4 B` with `A < μ(x,y)`, with the maximum in `μ` being the first argument
(`𝔡₂³ > 𝔡₃‖x‖‖y‖`, the Case-I condition), and with `λ₁(Γ_{x,y}) ≤ A`, one has

`pairS0 4 4 A p ≤ K * hiMin A B (𝔡₃(x,y)) (λ₁(Γ_{x,y}))`

where `hiMin A B d l = min_{4 ≤ R0 ≤ 67}(A^{68-R0} B^{2R0-8} d^{-R0} + (2A/l)^{67-R0})`.

Hints.  `pairS0 4 4 A p ≤ ballCount (Gam 4 4 x y) A` (the counted coefficient vectors are
primitive vectors of `Γ_{x,y}` of norm at most `A`).  Then apply the Lemma-R0 bound
`Work.HP.MDEstimates.ballCount_R0_M` with `L = Gam 4 4 x y`, `R = 68` (so that `rk L = R` via
`Work.HP.Sig2.gam_rank_det` and `Q44Child.card_mon44`, which need
`LinearIndependent ℤ ![veronese 4 4 x, veronese 4 4 y]` from `Work.HP.Sig2.nu_indep` plus the
primitivity and `x ≠ ±y` coming from `p ∈ Omega 4 4 B`), `j = R0`, `T = A`, `M = λ₁(Γ)/2`
(so `2M ≤ λ₁` and `M ≤ A/2 ≤ T` because `λ₁ ≤ A`), `Y = μ(x,y)` (so `T ≤ Y` because `A < μ`, and
`λ₆₈(Γ) ≤ μ` by the two-vector key lemma `Work.HP.Sig2.lam_Gam_le_muXY`).  Also needed:
`0 < detL (Gam 4 4 x y)` and `detL (Gam 4 4 x y) ≤ ∏_{i<68} lam (Gam 4 4 x y) (i+1)`
(`Work.HP.MDEstimates.detL_le_prod_lam`).

It remains to replace `μ^{R0}/detL` by `B^{2R0-8} d^{-R0}` up to a constant: in Case I one has
`μ(x,y) = 48 𝔡₂/𝔡₃` (`max_eq_left` with the two-vector condition), and the lower bound for
`detL (Gam 4 4 x y)` (`Work.HP.MDEstimates.detGam_lower` with `d = n = 4`) gives
`detL ≥ Cdet · 𝔡₂ ‖x‖³ ‖y‖³`, so that
`μ^{R0}/detL ≤ 48^{R0} Cdet^{-1} 𝔡₂^{R0-1}/(𝔡₃^{R0} ‖x‖³‖y‖³)`, and Hadamard's bound
`𝔡₂ ≤ ‖x‖‖y‖` (`Work.HP.MDEstimates.dmin_facts`) plus `‖x‖, ‖y‖ ≤ B` (`p ∈ Omega`) turn this into
`48^{R0}Cdet^{-1} ‖x‖^{R0-4}‖y‖^{R0-4} 𝔡₃^{-R0} ≤ 48^{R0}Cdet^{-1} B^{2R0-8} 𝔡₃^{-R0}`
(for `R0 ≥ 4`).  Since the resulting constant is independent of `p`, `A`, `B` and `R0`, and since
`hiMin ≤ hiCell (R0)` for every `R0 ∈ {4,…,67}` (`hiMin_le_cell`), this gives the claim. -/
theorem pairS0_hi_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ A B : ℝ, 1 ≤ A →
      ∀ p : (Fin 5 → ℤ) × (Fin 5 → ℤ),
      p ∈ Omega 4 4 B →
      A < muXY 4 p.1 p.2 →
      ¬ (dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) * dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) ^ 2
          ≤ dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) * (eNorm p.1 * eNorm p.2)) →
      lam (Gam 4 4 p.1 p.2) 1 ≤ A →
      pairS0 4 4 A p
        ≤ K * hiMin A B (dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ))) (lam (Gam 4 4 p.1 p.2) 1) := by
  obtain ⟨K1, hK1pos, hK1⟩ := ballCount_R0_M (ι := Mon 4 4)
  obtain ⟨Cdet, hCdetpos, hCdet⟩ := detGam_lower 4 4 (by norm_num) (by norm_num)
  refine ⟨K1 * ((48 : ℝ) ^ 67 * Cdet + 1), ?_, ?_⟩
  · exact mul_pos hK1pos (by
      have h : (0 : ℝ) ≤ (48 : ℝ) ^ 67 * Cdet :=
        mul_nonneg (pow_nonneg (by norm_num) _) hCdetpos.le
      linarith)
  intro A B hA1 p hp hmu hcase hlamA
  -- unpack the pair
  have hx : IsPrim p.1 := hp.1.1
  have hy : IsPrim p.2 := hp.2.1.1
  have hne : p.1 ≠ p.2 := hp.2.2.1
  have hne' : p.1 ≠ -p.2 := hp.2.2.2
  have hLI : LinearIndependent ℤ ![p.1, p.2] := Sig2.li_of_mem_Omega 4 4 B p hp
  have hxB : eNorm p.1 ≤ B := eNorm_le_of_mem_Xi44 hp.1.2
  have hyB : eNorm p.2 ≤ B := eNorm_le_of_mem_Xi44 hp.2.1.2
  have hBpos : 0 < B := lt_of_lt_of_le (eNorm_pos_of_ne_zero (isPrim_ne_zero hx)) hxB
  have hB0 : 0 ≤ B := hBpos.le
  -- the lattice `Γ_{p.1,p.2}` has rank `68` and positive covolume
  have hnu : LinearIndependent ℤ ![veronese 4 4 p.1, veronese 4 4 p.2] :=
    Sig2.nu_indep 4 4 (by norm_num) p.1 p.2 hx hy hne hne'
  obtain ⟨hrkG, hdetpos⟩ := Sig2.gam_rank_det 4 4 p.1 p.2 hnu
  have h70 : NN 4 4 = 70 := by
    rw [show NN 4 4 = Fintype.card (Mon 4 4) from rfl, Q44Child.card_mon44]
  have hR : rk (Gam 4 4 p.1 p.2) = 68 := by rw [hrkG, h70]
  have hMink : detL (Gam 4 4 p.1 p.2) ≤
      ∏ i ∈ Finset.range 68, lam (Gam 4 4 p.1 p.2) (i + 1) := by
    have h := detL_le_prod_lam (Gam 4 4 p.1 p.2)
    rwa [hR] at h
  have h70' : NN 4 4 - 2 = 68 := by rw [h70]
  have hlam68 : lam (Gam 4 4 p.1 p.2) 68 ≤ muXY 4 p.1 p.2 := by
    have h := Sig2.lam_Gam_le_muXY 4 4 (by norm_num) (by norm_num) p.1 p.2 hx hy hLI
    rwa [h70'] at h
  -- the size facts about `𝔡₂`, `𝔡₃` and the norms
  have hdf := dmin_facts 4 (by norm_num)
  have hd2one : 1 ≤ dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) := hdf.1 p.1 p.2 hLI
  have hd2le : dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) ≤ eNorm p.1 * eNorm p.2 :=
    hdf.2.1 p.1 p.2 hLI
  have hd3one : 1 ≤ dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) := hdf.2.2.1 p.1 p.2 hLI
  have hd3pos : 0 < dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)) := lt_of_lt_of_le zero_lt_one hd3one
  have hd2pos : 0 < dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) := lt_of_lt_of_le zero_lt_one hd2one
  -- the covolume lower bound, in the form consumed by `mu_div_det_le`
  have hbase : dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) * eNorm p.1 ^ 3 * eNorm p.2 ^ 3
      ≤ Cdet * detL (Gam 4 4 p.1 p.2) := hCdet p.1 p.2 hx hy hLI
  have hdetinv : Cdet⁻¹ * dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) * eNorm p.1 ^ 3 * eNorm p.2 ^ 3
      ≤ detL (Gam 4 4 p.1 p.2) := by
    calc Cdet⁻¹ * dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) * eNorm p.1 ^ 3 * eNorm p.2 ^ 3
        = (dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) * eNorm p.1 ^ 3 * eNorm p.2 ^ 3) / Cdet := by
          ring
      _ ≤ detL (Gam 4 4 p.1 p.2) := by
          rw [div_le_iff₀ hCdetpos]
          calc dmin 2 ({p.1, p.2} : Set (Fin 5 → ℤ)) * eNorm p.1 ^ 3 * eNorm p.2 ^ 3
              ≤ Cdet * detL (Gam 4 4 p.1 p.2) := hbase
            _ = detL (Gam 4 4 p.1 p.2) * Cdet := by ring
  have hlam1one : 1 ≤ lam (Gam 4 4 p.1 p.2) 1 :=
    one_le_lam (Gam 4 4 p.1 p.2) (i := 1) (by norm_num) (by rw [hR]; norm_num)
  have hlpos : 0 < lam (Gam 4 4 p.1 p.2) 1 := lt_of_lt_of_le zero_lt_one hlam1one
  have hKcpos : 0 < K1 * ((48 : ℝ) ^ 67 * Cdet + 1) :=
    mul_pos hK1pos (by
      have h : (0 : ℝ) ≤ (48 : ℝ) ^ 67 * Cdet :=
        mul_nonneg (pow_nonneg (by norm_num) _) hCdetpos.le
      linarith)
  have hpc : pairS0 4 4 A p ≤ (ballCount (Gam 4 4 p.1 p.2) A : ℝ) :=
    pairS0_le_ballCount 4 4 A p
  have hmin : pairS0 4 4 A p / (K1 * ((48 : ℝ) ^ 67 * Cdet + 1))
      ≤ hiMin A B (dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ))) (lam (Gam 4 4 p.1 p.2) 1) := by
    refine le_hiMin A B (dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)))
      (lam (Gam 4 4 p.1 p.2) 1) (fun R0 hR0 => ?_)
    obtain ⟨hR04, hR067⟩ := Finset.mem_Icc.mp hR0
    -- the `R0`-th cell of the Lemma-R0 bound
    have hmudiv0 := Sig2.mu_div_det_le 4 4 (by norm_num) Cdet⁻¹ (inv_pos.mpr hCdetpos) R0 hR04
      p.1 p.2 B hB0 hd2pos hd3pos hd2le hxB hyB hdetinv hcase
    have h48 : (3 : ℝ) * ((4 : ℕ) : ℝ) ^ 2 = 48 := by norm_num
    have hdiv : ∀ X : ℝ, X / Cdet⁻¹ = X * Cdet := by
      intro X
      rw [div_eq_mul_inv, inv_inv]
    have hmudiv : (muXY 4 p.1 p.2) ^ R0 / detL (Gam 4 4 p.1 p.2)
        ≤ (48 : ℝ) ^ R0 * B ^ (2 * (R0 - 4))
            * (dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ))) ^ (-(R0 : ℝ)) * Cdet := by
      have h := hmudiv0
      rw [h48] at h
      rw [hdiv] at h
      exact h
    have hMT : lam (Gam 4 4 p.1 p.2) 1 / 2 ≤ A := by
      have h := lam_nonneg (Gam 4 4 p.1 p.2) 1
      linarith
    have hTY : A ≤ muXY 4 p.1 p.2 := le_of_lt hmu
    have hMpos : 0 < lam (Gam 4 4 p.1 p.2) 1 / 2 := by linarith
    have h2M : 2 * (lam (Gam 4 4 p.1 p.2) 1 / 2) ≤ lam (Gam 4 4 p.1 p.2) 1 := by linarith
    have hbc := hK1 (Gam 4 4 p.1 p.2) 68 R0 (lam (Gam 4 4 p.1 p.2) 1 / 2) (muXY 4 p.1 p.2) A
      hR (by norm_num) hR067 hA1 hMT hTY hlam68 hdetpos hMink hMpos h2M
    rw [show 68 - 1 - R0 = 67 - R0 by omega] at hbc
    have hpoint := le_trans hpc (hi_pointwise K1 Cdet A B (dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ)))
      (lam (Gam 4 4 p.1 p.2) 1) (muXY 4 p.1 p.2) (detL (Gam 4 4 p.1 p.2))
      (ballCount (Gam 4 4 p.1 p.2) A : ℝ) R0 hK1pos hCdetpos hA1 hB0 hd3pos hlpos hR04 hR067
      hmudiv hbc)
    rw [div_le_iff₀ hKcpos]
    calc pairS0 4 4 A p
        ≤ K1 * ((48 : ℝ) ^ 67 * Cdet + 1)
            * hiCell A B (dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ))) (lam (Gam 4 4 p.1 p.2) 1) R0 :=
          hpoint
      _ = hiCell A B (dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ))) (lam (Gam 4 4 p.1 p.2) 1) R0
            * (K1 * ((48 : ℝ) ^ 67 * Cdet + 1)) := by ring
  rw [div_le_iff₀ hKcpos] at hmin
  calc pairS0 4 4 A p
      ≤ hiMin A B (dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ))) (lam (Gam 4 4 p.1 p.2) 1)
          * (K1 * ((48 : ℝ) ^ 67 * Cdet + 1)) := hmin
    _ = K1 * ((48 : ℝ) ^ 67 * Cdet + 1)
          * hiMin A B (dmin 3 ({p.1, p.2} : Set (Fin 5 → ℤ))) (lam (Gam 4 4 p.1 p.2) 1) := by ring

end Work.HP.MDEstimates.hiparts
