import Mathlib
import Submission.Work.BW.Defs
import Submission.Work.BW.auxpolydefs
import Submission.Work.BW.ph_ge_nineteen
import Submission.Work.BW.sysRow_height_bound
import Submission.Work.BW.slack_core_lf_tiny
import Submission.Work.BW.log_factorial_le_dK_mul

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

theorem slack_ge_log_factorial_tiny {K : Type*} [Field K] [NumberField K] {n r : ℕ} (φ : K →+* ℂ)
    (α : Fin n → K) (b : Fin n → ℤ) (k : Fin n) (c : ℝ) (hst : Standing φ α b k c)
    (v : ℕ) (L : Fin r → Fin n → ℤ) (α' : Fin r → K) (σ : Fin r → ℝ)
    (hBH : BH φ α b v c r L α' σ) (hr : 2 ≤ r) :
    2 * (Module.finrank ℚ K : ℝ) * Real.log (((Module.finrank ℚ ↥(auxField α')).factorial : ℝ))
      ≤ 0.001 * ((pS r (Module.finrank ℚ K) (ph (hL b (Module.finrank ℚ K)) v) : ℝ) *
          pD r (Module.finrank ℚ K) σ) := by
  set dK : ℕ := Module.finrank ℚ K with hdK
  set dF : ℕ := Module.finrank ℚ ↥(auxField α') with hdF
  set hN : ℕ := ph (hL b dK) v with hhN
  set dR : ℝ := (dK : ℝ) with hdR
  set hR : ℝ := (hN : ℝ) with hhR
  have hdK1 : 1 ≤ dK := by rw [hdK]; exact Module.finrank_pos (R := ℚ) (M := K)
  have hdRpos : (0 : ℝ) < dR := by
    rw [hdR]; exact_mod_cast (show (0 : ℕ) < dK from by omega)
  have hdRnn : (0 : ℝ) ≤ dR := le_of_lt hdRpos
  -- `h = ph (h'(L)) v ≥ 19`
  have h19 : 19 ≤ hN := by rw [hhN, hdK]; exact ph_ge_nineteen φ α b k c v hst
  -- `∏σⱼ ≥ (1/[K:ℚ])^r`
  have hprod : ((1 : ℝ) / dR) ^ r ≤ ∏ j, σ j := by
    have hsig : ∀ j, (1 : ℝ) / dR ≤ σ j := by
      intro j
      have h1 := one_div_finrank_le_hmod (α' j) (lamP φ α v L j)
      have h2 := hBH.2.2.2.2.2.1 j
      have h3 : (1 : ℝ) / (Module.finrank ℚ K : ℝ) = (1 : ℝ) / dR := by rw [hdR, hdK]
      rw [h3] at h1
      linarith
    have hone : (∏ _j : Fin r, ((1 : ℝ) / dR)) ≤ ∏ j, σ j :=
      Finset.prod_le_prod₀ (fun j _ => div_nonneg zero_le_one hdRnn) (fun j _ => hsig j)
    have : (∏ _j : Fin r, ((1 : ℝ) / dR)) = ((1 : ℝ) / dR) ^ r := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rwa [this] at hone
  -- `log (dF!) ≤ dR (hR+1)`
  have hlogfact : Real.log ((dF.factorial : ℕ) : ℝ) ≤ dR * (hR + 1) :=
    log_factorial_le_dK_mul φ α b k c α' hst v
  -- numeric core
  have hcore : 2 * dR * dR * (hR + 1) ≤ 0.001 * (↑(pS r dK hN) * pD r dK σ) :=
    slack_core_lf_tiny (r := r) (d := dK) (h := hN) hr hdK1 h19 σ hprod
  calc 2 * dR * Real.log ((dF.factorial : ℕ) : ℝ)
      ≤ 2 * dR * (dR * (hR + 1)) := mul_le_mul_of_nonneg_left hlogfact (by linarith)
    _ = 2 * dR * dR * (hR + 1) := by ring
    _ ≤ 0.001 * (↑(pS r dK hN) * pD r dK σ) := hcore

end Work.BW
