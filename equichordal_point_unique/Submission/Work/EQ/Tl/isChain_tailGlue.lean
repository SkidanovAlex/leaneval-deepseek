import Mathlib
import Submission.Work.EQ.TailGlueDefs

namespace Work.EQ.Tl

open Complex Filter _root_.Topology
open scoped Topology

/-! ## Elementary facts about the multiplier `λ = eqLam a` -/

/-- `eqLam a < 1` for `0 < a < 1`. -/
private lemma eqLam_lt_one_local {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : eqLam a < 1 := by
  rw [eqLam, div_lt_one (by linarith)]; linarith

/-- Norm bound for the multiplier `λ`: for a complex exponent `k ≥ dep`,
`‖λ^k · ψ‖ ≤ λ^dep ‖ψ‖`. -/
private lemma norm_lamC_zpow_mul_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {dep : ℕ} {k : ℤ}
    (hk : (dep : ℤ) ≤ k) (ψ : ℂ) :
    ‖(eqLam a : ℂ) ^ k * ψ‖ ≤ (eqLam a) ^ dep * ‖ψ‖ := by
  rw [norm_mul, ac_norm_lamC_zpow ha0 ha1 k]
  have hk0 : (0 : ℤ) ≤ k := le_trans (by positivity) hk
  have hkn : (eqLam a : ℝ) ^ k = (eqLam a) ^ (k.toNat : ℕ) := by
    rw [← zpow_natCast, Int.toNat_of_nonneg hk0]
  rw [hkn]
  have hdep : dep ≤ k.toNat := by
    have h2 := Int.toNat_of_nonneg hk0
    omega
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one (le_of_lt (ac_eqLam_pos ha0 ha1))
      (le_of_lt (eqLam_lt_one_local ha0 ha1)) hdep)
    (norm_nonneg ψ)

/-- Natural-exponent version of `norm_lamC_zpow_mul_le`. -/
private lemma norm_lamC_pow_mul_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {dep k : ℕ}
    (hk : dep ≤ k) (ψ : ℂ) :
    ‖(eqLam a : ℂ) ^ k * ψ‖ ≤ (eqLam a) ^ dep * ‖ψ‖ := by
  have h := norm_lamC_zpow_mul_le ha0 ha1 (dep := dep) (k := (k : ℤ)) (by exact_mod_cast hk) ψ
  rwa [zpow_natCast] at h

/-! ## Two generic chain steps -/

/-- The forward step of the principal germ is regular. -/
private lemma regPair_germC_step {a : ℝ} {h : ℂ → ℂ} {ρg : ℝ}
    (hstep : ∀ u ∈ Metric.ball (0 : ℂ) ρg,
      RegPair a (germC a h u) (germC a h (((eqLam a : ℝ) : ℂ) * u)))
    {u : ℂ} (hu : ‖u‖ < ρg) :
    RegPair a (germC a h u) (germC a h (((eqLam a : ℝ) : ℂ) * u)) :=
  hstep u (by rwa [Metric.mem_ball, dist_zero_right])

/-- The backward step of the mirrored germ is regular (bisector reflection of the forward step). -/
private lemma regPair_ugermC_step {a : ℝ} {h : ℂ → ℂ} {ρg : ℝ}
    (hstep : ∀ u ∈ Metric.ball (0 : ℂ) ρg,
      RegPair a (germC a h u) (germC a h (((eqLam a : ℝ) : ℂ) * u)))
    {v : ℂ} (hv : ‖v‖ < ρg) :
    RegPair a (ugermC a h (((eqLam a : ℝ) : ℂ) * v)) (ugermC a h v) := by
  rw [ugermC, ugermC]
  exact (H0_invParam_ge_regPair_mirror).mpr (regPair_germC_step hstep hv)

/-- The last middle point of the glued chain: at index `-dep` it is the first point of the F3
branch chain, in particular also when `dep = 0` (where the forward tail already applies). -/
private lemma tailGlue_at_neg_dep {a : ℝ} {h : ℂ → ℂ} {cc z₀ : ℂ} {dep : ℕ}
    {σ : Fin (2 * dep) → Bool} {t : ℂ} :
    (tailGlue a h cc z₀ dep σ t).1 (-((dep : ℤ))) =
      branchPt a (endFun a h dep) z₀ 1 σ t ⟨0, by omega⟩ := by
  by_cases hdep0 : dep = 0
  · subst hdep0
    have hneg : -(((0 : ℕ) : ℤ)) = (0 : ℤ) := by norm_num
    rw [hneg, tailGlue_fwd (by norm_num : ((0 : ℕ) : ℤ) ≤ 0), zpow_zero, one_mul]
    have hl : (⟨0, by omega⟩ : Fin (2 * 0 + 1)) = Fin.last 0 := by
      apply Fin.ext; simp [Fin.last]
    rw [hl, branchPt_last]
    show germC a h (z₀ + t ^ (2 ^ (2 * 0))) =
      germC a h (((eqLam a : ℝ) : ℂ) ^ 0 * (z₀ + t ^ (2 ^ 0)))
    simp only [pow_zero, one_mul]
    congr 1
  · have hdep1 : 1 ≤ dep := by omega
    rw [tailGlue_mid (by omega : ¬ ((dep : ℤ) ≤ -((dep : ℤ))))
      (by omega : -((dep : ℤ)) ≤ -((dep : ℤ)))]
    congr 1
    apply Fin.ext
    simp only [Fin.val_mk]
    have hz : -((dep : ℤ)) + (dep : ℤ) = 0 := by ring
    rw [hz]
    rfl

/-- The glued chain is a chain of the equichordal relation. -/
theorem isChain_tailGlue {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {cc z₀ : ℂ} (hcc : cc ≠ 0) {dep : ℕ} {σ : Fin (2 * dep) → Bool} {t : ℂ}
    {ρg : ℝ} (hρg : 0 < ρg)
    (hgerm : AnalyticOnNhd ℂ (germC a h) (Metric.ball 0 ρg))
    (hstep : ∀ u ∈ Metric.ball (0 : ℂ) ρg,
      RegPair a (germC a h u) (germC a h (((eqLam a : ℝ) : ℂ) * u)))
    (hend : AnalyticOnNhd ℂ (endFun a h dep) (Metric.ball z₀ 1))
    (hsm₁ : (eqLam a) ^ dep * ‖z₀ + t ^ (2 ^ (2 * dep))‖ < ρg)
    (hsm₂ : (eqLam a) ^ dep * ‖cc / (z₀ + t ^ (2 ^ (2 * dep)))‖ < ρg)
    (hψne : z₀ + t ^ (2 ^ (2 * dep)) ≠ 0)
    (hAdm : Adm a (endFun a h dep) z₀ 1 σ)
    (htρ : ‖t‖ < rhoFin' a (endFun a h dep) z₀ 1 (2 * dep)) (ht0 : t ≠ 0)
    (hjun : branchPt a (endFun a h dep) z₀ 1 σ t ⟨0, by omega⟩ =
      ugermC a h (((eqLam a : ℝ) : ℂ) ^ dep * (cc / (z₀ + t ^ (2 ^ (2 * dep)))))) :
    IsChain a h (tailGlue a h cc z₀ dep σ t) := by
  have hlamne : ((eqLam a : ℝ) : ℂ) ≠ 0 := ac_eqLamC_ne_zero ha0 ha1
  set ψ₁ : ℂ := z₀ + t ^ (2 ^ (2 * dep)) with hψ₁
  set ψ₂ : ℂ := cc / ψ₁ with hψ₂
  have hψ₂raw : ψ₂ = cc / (z₀ + t ^ (2 ^ (2 * dep))) := by rw [hψ₂, ← hψ₁]
  rw [IsChain]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- ## global regularity of consecutive pairs
    intro n
    by_cases hn1 : (dep : ℤ) ≤ n
    · -- region F: forward tail
      have hF2 : (dep : ℤ) ≤ n + 1 := by omega
      rw [tailGlue_fwd hn1, tailGlue_fwd hF2, ← hψ₁]
      have hu : ‖((eqLam a : ℝ) : ℂ) ^ n * ψ₁‖ < ρg :=
        lt_of_le_of_lt (norm_lamC_zpow_mul_le ha0 ha1 hn1 ψ₁) hsm₁
      have hde : ((eqLam a : ℝ) : ℂ) ^ (n + 1) * ψ₁ =
          ((eqLam a : ℝ) : ℂ) * (((eqLam a : ℝ) : ℂ) ^ n * ψ₁) := by
        rw [zpow_add_one₀ hlamne]; ring
      rw [hde]
      exact regPair_germC_step hstep hu
    · by_cases hn2 : -((dep : ℤ)) ≤ n
      · -- region M: the middle F3 branch chain
        have hj : (n + (dep : ℤ)).toNat < 2 * dep := by
          have h0 : 0 ≤ n + (dep : ℤ) := by omega
          have hh : ((n + (dep : ℤ)).toNat : ℤ) < ((2 * dep : ℕ) : ℤ) := by
            rw [Int.toNat_of_nonneg h0]; push_cast; omega
          exact_mod_cast hh
        set j : Fin (2 * dep) := ⟨(n + (dep : ℤ)).toNat, hj⟩ with hjdef
        rw [tailGlue_mid hn1 hn2]
        have e1 : (⟨(n + (dep : ℤ)).toNat, by omega⟩ : Fin (2 * dep + 1)) = j.castSucc := by
          apply Fin.ext; simp [hjdef, Fin.val_castSucc]
        rw [e1]
        have hbr := branchPt_reg (a := a) (c := endFun a h dep) (u₀ := z₀) (R := 1)
          (N := 2 * dep) (σ := σ) one_pos hend hAdm htρ ht0 j
        by_cases hnext : n + 1 < (dep : ℤ)
        · -- both endpoints in the middle
          have h2a : ¬ ((dep : ℤ) ≤ n + 1) := by omega
          have h2b : -((dep : ℤ)) ≤ n + 1 := by omega
          rw [tailGlue_mid h2a h2b]
          have e2 : (⟨(n + 1 + (dep : ℤ)).toNat, by omega⟩ : Fin (2 * dep + 1)) = j.succ := by
            apply Fin.ext
            simp only [hjdef, Fin.val_succ]
            rw [show n + 1 + (dep : ℤ) = (n + (dep : ℤ)) + 1 by ring,
              Int.toNat_add (by omega : (0 : ℤ) ≤ n + (dep : ℤ)) (by norm_num)]
            norm_num
          rw [e2]
          exact hbr
        · -- the last middle step ends at the forward germ
          have hnext' : (dep : ℤ) ≤ n + 1 := by omega
          have hnt : n + 1 = (dep : ℤ) := by omega
          rw [tailGlue_fwd hnext']
          have hsucc : j.succ = Fin.last (2 * dep) := by
            apply Fin.ext
            simp only [hjdef, Fin.val_succ, Fin.last]
            have h0 : 0 ≤ n + (dep : ℤ) := by omega
            have hto := Int.toNat_of_nonneg h0
            omega
          have hgj : germC a h (((eqLam a : ℝ) : ℂ) ^ (n + 1) * (z₀ + t ^ (2 ^ (2 * dep)))) =
              branchPt a (endFun a h dep) z₀ 1 σ t j.succ := by
            rw [hsucc, branchPt_last, hnt, zpow_natCast]
            rfl
          rw [hgj]
          exact hbr
      · -- region B: backward tail (n < -dep)
        have hlt : n < -((dep : ℤ)) := by omega
        by_cases hjn : n + 1 < -((dep : ℤ))
        · -- pure backward step
          rw [tailGlue_bwd hlt, tailGlue_bwd hjn, ← hψ₂raw]
          have hk : (dep : ℤ) ≤ -(n + 1) := by omega
          have hv : ‖((eqLam a : ℝ) : ℂ) ^ (-(n + 1)) * ψ₂‖ < ρg :=
            lt_of_le_of_lt (norm_lamC_zpow_mul_le ha0 ha1 hk ψ₂) hsm₂
          have hde : ((eqLam a : ℝ) : ℂ) ^ (-n) * ψ₂ =
              ((eqLam a : ℝ) : ℂ) * (((eqLam a : ℝ) : ℂ) ^ (-(n + 1)) * ψ₂) := by
            rw [show -n = (-(n + 1)) + 1 by ring, zpow_add_one₀ hlamne]; ring
          rw [hde]
          exact regPair_ugermC_step hstep hv
        · -- junction: n + 1 = -dep
          have hjn' : n + 1 = -((dep : ℤ)) := by omega
          have hLm' : (tailGlue a h cc z₀ dep σ t).1 (n + 1) =
              ugermC a h (((eqLam a : ℝ) : ℂ) ^ dep * ψ₂) := by
            rw [hjn', tailGlue_at_neg_dep, hjun]
          rw [tailGlue_bwd hlt, hLm', ← hψ₂raw]
          have hde : ((eqLam a : ℝ) : ℂ) ^ (-n) * ψ₂ =
              ((eqLam a : ℝ) : ℂ) * (((eqLam a : ℝ) : ℂ) ^ dep * ψ₂) := by
            have hn : -n = (dep : ℤ) + 1 := by omega
            rw [hn, zpow_add_one₀ hlamne, zpow_natCast]
            ring
          have hv : ‖((eqLam a : ℝ) : ℂ) ^ dep * ψ₂‖ < ρg :=
            lt_of_le_of_lt (norm_lamC_pow_mul_le ha0 ha1 (le_refl dep) ψ₂) hsm₂
          rw [hde]
          exact regPair_ugermC_step hstep hv
  · -- ψ₁ ≠ 0
    rw [tailGlue_psi1, ← hψ₁]; exact hψne
  · -- ψ₂ ≠ 0
    rw [tailGlue_psi2, ← hψ₂raw, hψ₂]
    exact div_ne_zero hcc hψne
  · -- forward tail identity
    filter_upwards [eventually_ge_atTop dep] with n hn
    have hnd : (dep : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
    rw [tailGlue_fwd hnd, tailGlue_psi1, ← hψ₁, zpow_natCast]
  · -- backward tail identity
    filter_upwards [eventually_ge_atTop (dep + 1)] with n hn
    have hnd : (dep : ℤ) < (n : ℤ) := by omega
    have hlt : -(n : ℤ) < -((dep : ℤ)) := by omega
    rw [tailGlue_bwd hlt, tailGlue_psi2, ← hψ₂raw,
      show -(-(n : ℤ)) = (n : ℤ) by ring, zpow_natCast]

end Work.EQ.Tl
