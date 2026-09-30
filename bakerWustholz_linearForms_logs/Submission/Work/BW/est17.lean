import Mathlib
import Submission.Work.BW.DefsAC
import Submission.Work.BW.kummer_indep
import Submission.Work.BW.Est17Ext
import Submission.Work.BW.est17_finrank
import Submission.Work.BW.est17_acg_mem
import Submission.Work.BW.est17_gexp
import Submission.Work.BW.est17_height_ext1
import Submission.Work.BW.est17_arch
import Submission.Work.BW.est17_fin
import Submission.Work.BW.est17_num2
import Submission.Work.BW.est17_Omega_sum
import Submission.Work.BW.est17_fin_supports
import Submission.Work.BW.est17_finsum_log_two
import Submission.Work.BW.est15_height_id
import Submission.Work.BW.num_est15_slacks
import Submission.Work.BW.LiouvilleAux.product_formula_isolate
import Submission.Work.BW.LiouvilleAux.sum_mult_erase
import Submission.Work.BW.LiouvilleAux.finsum_log_le_posLog

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open Complex

set_option maxHeartbeats 1600000

theorem est17_core {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ}
    {α : Fin n → K} {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ}
    {α' : Fin r → K} {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    {ρ : Fin r → ℂ} [hNF : NumberField (EL φ ρ)]
    [hDE : DecidableEq (NumberField.InfinitePlace (EL φ ρ))]
    (H : ACHyp φ α b k c v L α' σ ι p)
    (J : ℕ) (μ : Fin r → ℕ) (Tst : ℝ) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (ht : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ Tst) (s : ℤ)
    (γ : EL φ ρ) (hγ : (γ : ℂ) = acg φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2))
    (hg : γ ≠ 0)
    (hfinrank : (Module.finrank ℚ (EL φ ρ) : ℝ) = (2 : ℝ) ^ r * (dK K : ℝ))
    (hheightid : (∑ w : NumberField.InfinitePlace (EL φ ρ), (w.mult : ℝ) *
          Real.log (⨆ lm, w (inclE φ ρ (p lm))))
        + (∑ᶠ w : NumberField.FinitePlace (EL φ ρ), Real.log (⨆ lm, w (inclE φ ρ (p lm))))
        = Height.logHeight (fun lm => inclE φ ρ (p lm)))
    (hheight : Height.logHeight (fun lm => inclE φ ρ (p lm)) = (2 : ℝ) ^ r * Height.logHeight p)
    (hOmega : (∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) *
          (∑ j, (pDj r (dK K) σ j : ℝ) *
            (if 0 ≤ s then w (inclE φ ρ (α' j)) else (w (inclE φ ρ (α' j)))⁻¹).posLog))
        + (∑ᶠ w : NumberField.FinitePlace (EL φ ρ),
          ∑ j, (pDj r (dK K) σ j : ℝ) *
            (if 0 ≤ s then w (inclE φ ρ (α' j)) else (w (inclE φ ρ (α' j)))⁻¹).posLog)
        ≤ (2 : ℝ) ^ r * acD K σ)
    (h2sum : (∑ᶠ w : NumberField.FinitePlace (EL φ ρ), |Real.log (w (inclE φ ρ (2 : K)))|)
        = (2 : ℝ) ^ r * (dK K : ℝ) * Real.log 2)
    (hsuppO : Function.HasFiniteSupport (fun w : NumberField.FinitePlace (EL φ ρ) =>
        ∑ j, (pDj r (dK K) σ j : ℝ) *
          (if 0 ≤ s then w (inclE φ ρ (α' j)) else (w (inclE φ ρ (α' j)))⁻¹).posLog))
    (hsuppA : Function.HasFiniteSupport (fun w : NumberField.FinitePlace (EL φ ρ) =>
        Real.log (⨆ lm, w (inclE φ ρ (p lm)))))
    (hsupp2 : Function.HasFiniteSupport (fun w : NumberField.FinitePlace (EL φ ρ) =>
        |Real.log (w (inclE φ ρ (2 : K)))|))
    (hnum : (2 ^ r * (dK K : ℝ) - 1) * ((acH K b v : ℝ) * Tst
          + 0.203 * acS K r b v * acD K σ / (dK K : ℝ)
          + Real.log ((acH K b v : ℝ) * ((pD0 r (dK K) σ : ℝ) + 1)
              * ∏ j, ((pDj r (dK K) σ j : ℝ) + 1)))
        + (2 ^ r * (dK K : ℝ) - 1) * (0.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σ / (dK K : ℝ))
        + (2 : ℝ) ^ r * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σ
        + (2 : ℝ) ^ r * (2 * ((J : ℝ) + 1) * (dK K : ℝ) * (acH K b v : ℝ)
            * ((pD0 r (dK K) σ : ℝ) + 1) * Real.log 2)
        ≤ (2 : ℝ) ^ r * ((1 - 1 / (2 ^ r * (dK K : ℝ)))
              * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ)
            + 1.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σ
            + 0.032 * acS K r b v * acD K σ + kumJ K b v σ J))
    (harch : ∀ w (hw : w ≠ w0 φ ρ), Real.log (w γ) ≤
          Real.log (⨆ lm, w (inclE φ ρ (p lm)))
          + ((acH K b v : ℝ) * Tst
            + (0.203 + 0.007 * ((((|s| : ℤ) : ℝ) / 2 / 2 ^ J) / acS K r b v))
                * acS K r b v * acD K σ / (dK K : ℝ)
            + Real.log ((acH K b v : ℝ) * ((pD0 r (dK K) σ : ℝ) + 1)
                * ∏ j, ((pDj r (dK K) σ j : ℝ) + 1))
            + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * ∑ j, (pDj r (dK K) σ j : ℝ) *
                (if 0 ≤ s then w (inclE φ ρ (α' j))
                   else (w (inclE φ ρ (α' j)))⁻¹).posLog))
    (hfin : ∀ w : NumberField.FinitePlace (EL φ ρ), Real.log (w γ) ≤
          Real.log (⨆ lm, w (inclE φ ρ (p lm)))
          + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * ∑ j, (pDj r (dK K) σ j : ℝ) *
              (if 0 ≤ s then w (inclE φ ρ (α' j)) else (w (inclE φ ρ (α' j)))⁻¹).posLog
          + 2 * ((J : ℝ) + 1) * (acH K b v : ℝ) * ((pD0 r (dK K) σ : ℝ) + 1)
              * |Real.log (w (inclE φ ρ (2 : K)))|) :
    Real.exp (lnp φ p - 2 ^ r * (Height.logHeight p +
        (1 - 1 / (2 ^ r * (dK K : ℝ))) *
          ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ) +
        1.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σ
        + 0.032 * acS K r b v * acD K σ + kumJ K b v σ J)) ≤
      ‖acg φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2)‖ := by
  classical
  -- ## abbreviations
  let zz : ℝ := ((|s| : ℤ) : ℝ) / 2 / 2 ^ J
  let dd : ℝ := (dK K : ℝ)
  let hh : ℝ := (acH K b v : ℝ)
  let SS : ℝ := acS K r b v
  let DD : ℝ := acD K σ
  let NN : ℝ := hh * ((pD0 r (dK K) σ : ℝ) + 1) * ∏ j, ((pDj r (dK K) σ j : ℝ) + 1)
  let Cst : ℝ := hh * Tst + (0.203 + 0.007 * (zz / SS)) * SS * DD / dd + Real.log NN
  let OMg : (EL φ ρ → ℝ) → ℝ := fun w => ∑ j, (pDj r (dK K) σ j : ℝ) *
      (if 0 ≤ s then w (inclE φ ρ (α' j)) else (w (inclE φ ρ (α' j)))⁻¹).posLog
  let SUPg : (EL φ ρ → ℝ) → ℝ := fun w => ⨆ lm, w (inclE φ ρ (p lm))
  let Cc : ℝ := 2 * ((J : ℝ) + 1) * hh * ((pD0 r (dK K) σ : ℝ) + 1)
  -- ## positivity
  have hSpos : 0 < SS := by
    have hr : 0 < r := lt_of_lt_of_le (by norm_num : (0:ℕ) < 2) H.hr
    have hd : 0 < dK K := Module.finrank_pos
    have hh19 : 0 < acH K b v := lt_of_lt_of_le (by norm_num : (0:ℕ) < 19) (acH_lower H).1
    simp only [SS, acS, pS]
    positivity
  have hDpos : 0 < DD := by
    have hr : 2 ≤ r := H.hr
    have hd : 1 ≤ dK K := Nat.one_le_iff_ne_zero.mpr (ne_of_gt (Module.finrank_pos (R := ℚ) (M := K)))
    have hσ : ∀ j, 1 / (dK K : ℝ) ≤ σ j := fun j => sigma_ge H j
    simp only [DD, acD]
    exact pD_pos hr hd σ hσ
  have hzz : 0 ≤ zz := by simp only [zz]; positivity
  have hdd : 0 < dd := by
    have := Module.finrank_pos (R := ℚ) (M := K); simp only [dd]; exact_mod_cast this
  have hdd1 : (1:ℝ) ≤ dd := by
    have h : 1 ≤ dK K := Nat.one_le_iff_ne_zero.mpr (ne_of_gt (Module.finrank_pos (R := ℚ) (M := K)))
    simp only [dd]; exact_mod_cast h
  have hh1 : 1 ≤ hh := by
    simp only [hh]
    exact_mod_cast (le_trans (by norm_num : (1:ℕ) ≤ 19) (acH_lower H).1)
  have hhh : 0 < hh := lt_of_lt_of_le one_pos hh1
  have hTst0 : 0 ≤ Tst := le_trans (Nat.cast_nonneg _) ht
  have hNN1 : 1 ≤ NN := by
    simp only [NN]
    have h2 : (1:ℝ) ≤ (pD0 r (dK K) σ : ℝ) + 1 := by
      have := Nat.cast_nonneg (pD0 r (dK K) σ) (α := ℝ); linarith
    have h3 : (1:ℝ) ≤ ∏ j : Fin r, ((pDj r (dK K) σ j : ℝ) + 1) := by
      have hnat : 1 ≤ ∏ j : Fin r, (pDj r (dK K) σ j + 1) :=
        Finset.one_le_prod (fun j _ => Nat.succ_le_succ (Nat.zero_le _))
      calc (1:ℝ) = ((1:ℕ) : ℝ) := by norm_num
        _ ≤ ((∏ j : Fin r, (pDj r (dK K) σ j + 1) : ℕ) : ℝ) := by exact_mod_cast hnat
        _ = ∏ j : Fin r, ((pDj r (dK K) σ j : ℝ) + 1) := by push_cast; rfl
    calc (1:ℝ) = 1 * 1 * 1 := by ring
      _ ≤ hh * ((pD0 r (dK K) σ : ℝ) + 1) * ∏ j, ((pDj r (dK K) σ j : ℝ) + 1) := by gcongr
  have hCst0 : 0 ≤ Cst := by
    simp only [Cst]
    have h1 : 0 ≤ hh * Tst := mul_nonneg (le_of_lt hhh) hTst0
    have h2 : 0 ≤ (0.203 + 0.007 * (zz / SS)) * SS * DD / dd := by
      apply div_nonneg _ (le_of_lt hdd)
      refine mul_nonneg (mul_nonneg ?_ (le_of_lt hSpos)) (le_of_lt hDpos)
      have : 0 ≤ zz / SS := div_nonneg hzz (le_of_lt hSpos)
      linarith
    have h3 : 0 ≤ Real.log NN := Real.log_nonneg hNN1
    linarith
  -- ## Liouville
  have hw0v : (w0 φ ρ) γ = ‖(γ : ℂ)‖ := w0_apply γ
  have hliou := LiouvilleAux.product_formula_isolate (K := EL φ ρ) (w0 φ ρ) hg
  rw [hw0v] at hliou
  -- ## the archimedean place `w0` and `lnp`
  have hw0sup : Real.log (⨆ lm, (w0 φ ρ) (inclE φ ρ (p lm))) = lnp φ p := by
    simp only [lnp, w0_apply, inclE_coe]
  -- ## splitting the erasure
  have herase : (∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) * Real.log (⨆ lm, w (inclE φ ρ (p lm))))
      = (∑ w : NumberField.InfinitePlace (EL φ ρ), (w.mult : ℝ) * Real.log (⨆ lm, w (inclE φ ρ (p lm))))
        - ((w0 φ ρ).mult : ℝ) * Real.log (⨆ lm, (w0 φ ρ) (inclE φ ρ (p lm))) := by
    have h := Finset.sum_erase_add Finset.univ
      (fun w : NumberField.InfinitePlace (EL φ ρ) => (w.mult : ℝ) * Real.log (⨆ lm, w (inclE φ ρ (p lm))))
      (Finset.mem_univ (w0 φ ρ))
    linarith
  have hsupfull : (∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) * Real.log (⨆ lm, w (inclE φ ρ (p lm))))
      + (∑ᶠ w : NumberField.FinitePlace (EL φ ρ), Real.log (⨆ lm, w (inclE φ ρ (p lm))))
      = 2 ^ r * Height.logHeight p - ((w0 φ ρ).mult : ℝ) * lnp φ p := by
    have h2 : (∑ w : NumberField.InfinitePlace (EL φ ρ),
          (w.mult : ℝ) * Real.log (⨆ lm, w (inclE φ ρ (p lm))))
        + (∑ᶠ w : NumberField.FinitePlace (EL φ ρ), Real.log (⨆ lm, w (inclE φ ρ (p lm))))
        = 2 ^ r * Height.logHeight p := by rw [hheightid, hheight]
    rw [herase, hw0sup]
    linarith

  -- ## more abbreviations
  let SA : ℝ := ∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ)
  let OMarch : ℝ := ∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) * OMg (fun y => w y)
  let OMfin : ℝ := ∑ᶠ w : NumberField.FinitePlace (EL φ ρ), OMg (fun y => w y)
  let S2 : ℝ := ∑ᶠ w : NumberField.FinitePlace (EL φ ρ), |Real.log (w (inclE φ ρ (2 : K)))|
  let ArchS : ℝ := ∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) * Real.log (SUPg (fun y => w y))
  let SupFin : ℝ := ∑ᶠ w : NumberField.FinitePlace (EL φ ρ), Real.log (SUPg (fun y => w y))
  let E : ℝ := (1 - 1 / (2 ^ r * dd)) * (dd * hh * Tst + 0.204 * SS * DD) + 1.007 * zz * DD
      + 0.032 * SS * DD + kumJ K b v σ J
  -- ## sizes
  have hSAlt : SA ≤ 2 ^ r * dd - 1 := by
    have h1 := LiouvilleAux.sum_mult_erase (K := EL φ ρ) (w0 φ ρ)
    have hm1 : (1:ℝ) ≤ ((w0 φ ρ).mult : ℝ) := by
      exact_mod_cast (NumberField.InfinitePlace.mult_pos (w := w0 φ ρ))
    simp only [SA, hfinrank] at h1 ⊢
    rw [h1]
    linarith
  have hOmega' : OMarch + OMfin ≤ 2 ^ r * DD := hOmega
  have h2sum' : S2 = (2:ℝ) ^ r * dd * Real.log 2 := h2sum
  have hE0 : 0 ≤ E := by
    simp only [E]
    have h1 : 0 ≤ (1 - 1 / (2 ^ r * dd)) * (dd * hh * Tst + 0.204 * SS * DD) := by
      apply mul_nonneg
      · rw [sub_nonneg, div_le_one (by positivity)]
        calc (1:ℝ) = 1 * 1 := by ring
          _ ≤ 2 ^ r * dd := mul_le_mul (one_le_pow₀ (by norm_num)) hdd1 zero_le_one (by positivity)
      · have hA : 0 ≤ dd * hh * Tst := mul_nonneg (mul_nonneg (le_of_lt hdd) (le_of_lt hhh)) hTst0
        have hB : 0 ≤ 0.204 * SS * DD := mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hSpos)) (le_of_lt hDpos)
        linarith
    have h2 : 0 ≤ 1.007 * zz * DD := by
      have := mul_nonneg hzz (le_of_lt hDpos); linarith [this]
    have hkl : 0 < Real.log (2 * (r:ℝ) * (dK K:ℝ)) := by
      apply Real.log_pos
      have h1 : (2:ℝ) ≤ (r:ℝ) := by exact_mod_cast H.hr
      have h2 : (1:ℝ) ≤ (dK K:ℝ) := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (ne_of_gt (Module.finrank_pos (R := ℚ) (M := K))))
      nlinarith
    have h3 : 0 ≤ kumJ K b v σ J := by
      simp only [kumJ]
      have h1 : 0 ≤ 0.044 * (J:ℝ) / Real.log (2 * (r:ℝ) * (dK K:ℝ)) :=
        div_nonneg (mul_nonneg (by norm_num) (Nat.cast_nonneg _)) (le_of_lt hkl)
      exact mul_nonneg (mul_nonneg h1 (le_of_lt hSpos)) (le_of_lt hDpos)
    have h4 : 0 ≤ 0.032 * SS * DD := mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hSpos)) (le_of_lt hDpos)
    linarith
  -- ## supports on the finite places
  have hsO : Function.HasFiniteSupport (fun w : NumberField.FinitePlace (EL φ ρ) => OMg (fun y => w y)) := hsuppO
  have hsA : Function.HasFiniteSupport (fun w : NumberField.FinitePlace (EL φ ρ) => Real.log (SUPg (fun y => w y))) := hsuppA
  have hs2 : Function.HasFiniteSupport (fun w : NumberField.FinitePlace (EL φ ρ) => |Real.log (w (inclE φ ρ (2 : K)))|) := hsupp2
  have hsZ : Function.HasFiniteSupport (fun w : NumberField.FinitePlace (EL φ ρ) => zz * OMg (fun y => w y)) := by
    exact Function.HasFiniteSupport.mul_right (fun _ : NumberField.FinitePlace (EL φ ρ) => zz) hsO
  have hsC : Function.HasFiniteSupport (fun w : NumberField.FinitePlace (EL φ ρ) => Cc * |Real.log (w (inclE φ ρ (2 : K)))|) := by
    exact Function.HasFiniteSupport.mul_right (fun _ : NumberField.FinitePlace (EL φ ρ) => Cc) hs2
  have hsG : Function.HasFiniteSupport (fun w : NumberField.FinitePlace (EL φ ρ) => Real.log (w γ)) := by
    rw [Function.HasFiniteSupport]
    refine (NumberField.FinitePlace.hasFiniteMulSupport hg).subset ?_
    intro w hw
    simp only [Function.mem_support, Function.mem_mulSupport] at hw ⊢
    intro h1
    exact hw (by rw [h1, Real.log_one])
  -- ## the per-place bounds in abbreviated form
  have harchlog : ∀ w (hw : w ≠ w0 φ ρ),
      Real.log (w γ) ≤ Real.log (SUPg (fun y => w y)) + (Cst + zz * OMg (fun y => w y)) := by
    intro w hw
    exact harch w hw
  have hfinlog : ∀ w : NumberField.FinitePlace (EL φ ρ),
      Real.log (w γ) ≤ Real.log (SUPg (fun y => w y)) + (zz * OMg (fun y => w y) + Cc * |Real.log (w (inclE φ ρ (2 : K)))|) := by
    intro w
    have h := hfin w
    have e : (Real.log (⨆ lm, w (inclE φ ρ (p lm)))
          + (((|s|:ℤ):ℝ)/2/2^J) * (∑ j, (pDj r (dK K) σ j : ℝ) *
              (if 0 ≤ s then w (inclE φ ρ (α' j)) else (w (inclE φ ρ (α' j)))⁻¹).posLog))
        + 2 * ((J:ℝ)+1) * (acH K b v : ℝ) * ((pD0 r (dK K) σ:ℝ)+1) * |Real.log (w (inclE φ ρ (2:K)))|
        = Real.log (SUPg (fun y => w y)) + (zz * OMg (fun y => w y) + Cc * |Real.log (w (inclE φ ρ (2 : K)))|) := by
      simp only [SUPg, OMg, zz, Cc, hh]
      ring
    rwa [e] at h
  -- ## archimedean sum
  have h1arch : (∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) * Real.log (w γ))
      ≤ ∑ w ∈ Finset.univ.erase (w0 φ ρ),
          (w.mult : ℝ) * (Real.log (SUPg (fun y => w y)) + (Cst + zz * OMg (fun y => w y))) :=
    Finset.sum_le_sum (fun w hw =>
      mul_le_mul_of_nonneg_left (harchlog w (Finset.mem_erase.mp hw).1) (Nat.cast_nonneg _))
  have h2arch : (∑ w ∈ Finset.univ.erase (w0 φ ρ),
        (w.mult : ℝ) * (Real.log (SUPg (fun y => w y)) + (Cst + zz * OMg (fun y => w y))))
      = ArchS + (SA * Cst + zz * OMarch) := by
    have e1 : (∑ w ∈ Finset.univ.erase (w0 φ ρ),
        (w.mult : ℝ) * (Real.log (SUPg (fun y => w y)) + (Cst + zz * OMg (fun y => w y))))
      = (∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) * Real.log (SUPg (fun y => w y)))
        + (∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) * (Cst + zz * OMg (fun y => w y))) := by
      simp only [mul_add]
      rw [Finset.sum_add_distrib]
    have e2 : (∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) * (Cst + zz * OMg (fun y => w y)))
      = (∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) * Cst)
        + (∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) * (zz * OMg (fun y => w y))) := by
      simp only [mul_add]
      rw [Finset.sum_add_distrib]
    have e3 : (∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) * Cst)
      = (∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ)) * Cst := (Finset.sum_mul _ _ _).symm
    have e4 : (∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) * (zz * OMg (fun y => w y)))
      = zz * (∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) * OMg (fun y => w y)) := by
      have h : (∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) * (zz * OMg (fun y => w y)))
          = ∑ w ∈ Finset.univ.erase (w0 φ ρ), zz * ((w.mult : ℝ) * OMg (fun y => w y)) :=
        Finset.sum_congr rfl (fun w _ => by ring)
      rw [h, ← Finset.mul_sum]
    rw [e1, e2, e3, e4]
  -- ## finite sum
  have h1fin : (∑ᶠ w : NumberField.FinitePlace (EL φ ρ), Real.log (w γ))
      ≤ ∑ᶠ w : NumberField.FinitePlace (EL φ ρ),
          (Real.log (SUPg (fun y => w y)) + (zz * OMg (fun y => w y) + Cc * |Real.log (w (inclE φ ρ (2 : K)))|)) :=
    finsum_le_finsum hsG (hsA.add (hsZ.add hsC)) (fun w => hfinlog w)
  have hsZC : Function.HasFiniteSupport (fun w : NumberField.FinitePlace (EL φ ρ) =>
      zz * OMg (fun y => w y) + Cc * |Real.log (w (inclE φ ρ (2 : K)))|) := hsZ.add hsC
  have h2fin : (∑ᶠ w : NumberField.FinitePlace (EL φ ρ),
        (Real.log (SUPg (fun y => w y)) + (zz * OMg (fun y => w y) + Cc * |Real.log (w (inclE φ ρ (2 : K)))|)))
      = SupFin + (zz * OMfin + Cc * S2) := by
    rw [finsum_add_distrib hsA hsZC, finsum_add_distrib hsZ hsC,
      ← mul_finsum' (fun w : NumberField.FinitePlace (EL φ ρ) => OMg (fun y => w y)) zz hsO,
      ← mul_finsum' (fun w : NumberField.FinitePlace (EL φ ρ) => |Real.log (w (inclE φ ρ (2 : K)))|) Cc hs2]
  -- ## the C-part
  have hC : (SA * Cst + zz * OMarch) + (zz * OMfin + Cc * S2) ≤ (2:ℝ) ^ r * E := by
    have hb1 : SA * Cst ≤ (2 ^ r * dd - 1) * Cst := mul_le_mul_of_nonneg_right hSAlt hCst0
    have hb2 : zz * (OMarch + OMfin) ≤ zz * (2 ^ r * DD) := mul_le_mul_of_nonneg_left hOmega' hzz
    have hb2' : zz * OMarch + zz * OMfin = zz * (OMarch + OMfin) := by ring
    have hb3 : Cc * S2 = (2:ℝ) ^ r * (2 * ((J:ℝ)+1) * dd * hh * ((pD0 r (dK K) σ : ℝ) + 1) * Real.log 2) := by
      rw [h2sum']
      simp only [Cc]
      ring
    have hCst_eq : Cst = hh * Tst + 0.203 * SS * DD / dd + Real.log NN + 0.007 * zz * DD / dd := by
      have hSne : SS ≠ 0 := ne_of_gt hSpos
      have hdne : dd ≠ 0 := ne_of_gt hdd
      simp only [Cst]
      have h1 : (0.203 + 0.007 * (zz / SS)) * SS * DD / dd
          = 0.203 * SS * DD / dd + 0.007 * zz * DD / dd := by
        field_simp
      rw [h1]
      ring
    have hnum' : (2 ^ r * dd - 1) * (hh * Tst + 0.203 * SS * DD / dd + Real.log NN)
          + (2 ^ r * dd - 1) * (0.007 * zz * DD / dd)
          + (2:ℝ) ^ r * zz * DD
          + (2:ℝ) ^ r * (2 * ((J:ℝ)+1) * dd * hh * ((pD0 r (dK K) σ : ℝ) + 1) * Real.log 2)
          ≤ (2:ℝ) ^ r * E := hnum
    have hkey : (2 ^ r * dd - 1) * Cst + zz * (2 ^ r * DD)
        + (2:ℝ) ^ r * (2 * ((J:ℝ)+1) * dd * hh * ((pD0 r (dK K) σ : ℝ) + 1) * Real.log 2)
        ≤ (2:ℝ) ^ r * E := by
      rw [hCst_eq]
      have hdist : (2 ^ r * dd - 1) * (hh * Tst + 0.203 * SS * DD / dd + Real.log NN + 0.007 * zz * DD / dd)
          = (2 ^ r * dd - 1) * (hh * Tst + 0.203 * SS * DD / dd + Real.log NN)
            + (2 ^ r * dd - 1) * (0.007 * zz * DD / dd) := by ring
      rw [hdist]
      have hzzDD : zz * (2 ^ r * DD) = (2:ℝ) ^ r * zz * DD := by ring
      rw [hzzDD]
      linarith [hnum']
    linarith [hb1, hb2', hb2, hb3, hkey]
  -- ## Liouville + per-place bounds
  have hbound : (∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) * Real.log (w γ))
      + (∑ᶠ w : NumberField.FinitePlace (EL φ ρ), Real.log (w γ))
      ≤ (2 ^ r * Height.logHeight p - ((w0 φ ρ).mult : ℝ) * lnp φ p) + (2:ℝ) ^ r * E := by
    have ha : (∑ w ∈ Finset.univ.erase (w0 φ ρ), (w.mult : ℝ) * Real.log (w γ))
        ≤ ArchS + (SA * Cst + zz * OMarch) := le_trans h1arch (le_of_eq h2arch)
    have hb : (∑ᶠ w : NumberField.FinitePlace (EL φ ρ), Real.log (w γ))
        ≤ SupFin + (zz * OMfin + Cc * S2) := le_trans h1fin (le_of_eq h2fin)
    have hc : (SA * Cst + zz * OMarch) + (zz * OMfin + Cc * S2) ≤ (2:ℝ) ^ r * E := hC
    have hd : ArchS + SupFin = 2 ^ r * Height.logHeight p - ((w0 φ ρ).mult : ℝ) * lnp φ p := hsupfull
    linarith [ha, hb, hc, hd]
  -- ## conclusion
  have hMpos : (0:ℝ) < ((w0 φ ρ).mult : ℝ) := by
    exact_mod_cast (NumberField.InfinitePlace.mult_pos (w := w0 φ ρ))
  have hM1 : (1:ℝ) ≤ ((w0 φ ρ).mult : ℝ) := by
    have h : 1 ≤ (w0 φ ρ).mult :=
      Nat.one_le_iff_ne_zero.mpr (ne_of_gt (NumberField.InfinitePlace.mult_pos (w := w0 φ ρ)))
    exact_mod_cast h
  have hLH0 : 0 ≤ Height.logHeight p := Height.logHeight_nonneg p
  have h2r : (0:ℝ) ≤ (2:ℝ) ^ r := by positivity
  have hX : 0 ≤ (2:ℝ) ^ r * (Height.logHeight p + E) := mul_nonneg h2r (add_nonneg hLH0 hE0)
  have hMX : (2:ℝ) ^ r * (Height.logHeight p + E) ≤
      ((w0 φ ρ).mult : ℝ) * ((2:ℝ) ^ r * (Height.logHeight p + E)) := by nlinarith [hM1, hX]
  have hlog : Real.log ‖(γ : ℂ)‖ ≥ lnp φ p - 2 ^ r * (Height.logHeight p + E) := by
    have hMne : ((w0 φ ρ).mult : ℝ) ≠ 0 := ne_of_gt hMpos
    have h1 : ((w0 φ ρ).mult : ℝ) * Real.log ‖(γ : ℂ)‖
        ≥ ((w0 φ ρ).mult : ℝ) * (lnp φ p - 2 ^ r * (Height.logHeight p + E)) := by
      linarith [hliou, hbound, hMX]
    have h2 : ((w0 φ ρ).mult : ℝ) * (lnp φ p - 2 ^ r * (Height.logHeight p + E))
        / ((w0 φ ρ).mult : ℝ) = (lnp φ p - 2 ^ r * (Height.logHeight p + E)) :=
      mul_div_cancel_left₀ _ hMne
    have h3 : ((w0 φ ρ).mult : ℝ) * Real.log ‖(γ : ℂ)‖ / ((w0 φ ρ).mult : ℝ)
        = Real.log ‖(γ : ℂ)‖ := mul_div_cancel_left₀ _ hMne
    rw [← h3, ← h2]
    exact div_le_div_of_nonneg_right h1 hMpos.le
  have hpos : 0 < ‖(γ : ℂ)‖ := by
    rw [norm_pos_iff]
    intro h
    exact hg (Subtype.ext h)
  have hmain : Real.exp (lnp φ p - 2 ^ r * (Height.logHeight p + E)) ≤ ‖(γ : ℂ)‖ :=
    (Real.le_log_iff_exp_le hpos).mp hlog
  have hkey : lnp φ p - 2 ^ r * (Height.logHeight p + E) =
      lnp φ p - 2 ^ r * (Height.logHeight p +
        (1 - 1 / (2 ^ r * (dK K : ℝ))) *
          ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ) +
        1.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σ
        + 0.032 * acS K r b v * acD K σ + kumJ K b v σ J) := by
    simp only [E, zz, dd, hh, SS, DD]
    ring
  rw [hkey] at hmain
  simpa only [hγ] using hmain

/-- BW (17) at level `J` (p. 45–46): for `g(s/2) ≠ 0` (a number in `K' = K(α'^{1/2})`, `[K':K] = 2^r` by the Kummer condition), `2^{-r}{log|g(s/2)| − ln(p)} ≥ −{h(p) + (1 − 1/(2^r d))(dhT* + 0·204SD) + 1·007·2^{-J}|s/2|D} − 0·032SD − kum_J`. Uses `kummer_indep` (degree `2^r d`), the product formula over `K'`, `num_kum`. -/
theorem est17 {K : Type*} [Field K] [NumberField K] {n r : ℕ} {φ : K →+* ℂ} {α : Fin n → K}
    {b : Fin n → ℤ} {k : Fin n} {c : ℝ} {v : ℕ} {L : Fin r → Fin n → ℤ} {α' : Fin r → K}
    {σ : Fin r → ℝ} {ι : Fin (r - 1) → Fin n}
    {p : AuxIdx r (acH K b v) (pD0 r (dK K) σ) (pDj r (dK K) σ) → K}
    (H : ACHyp φ α b k c v L α' σ ι p) (J : ℕ) (μ : Fin r → ℕ) (Tst : ℝ) (hTst : Tst ≤ acT K σ) (t0 : ℕ) (t : Fin (r - 1) → ℕ)
    (ht : ((t0 + ∑ m, t m : ℕ) : ℝ) ≤ Tst) (s : ℤ)
    (hg : acg φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2) ≠ 0) :
    Real.exp (lnp φ p - 2 ^ r * (Height.logHeight p +
        (1 - 1 / (2 ^ r * (dK K : ℝ))) * ((dK K : ℝ) * (acH K b v : ℝ) * Tst + 0.204 * acS K r b v * acD K σ) +
        1.007 * (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * acD K σ + 0.032 * acS K r b v * acD K σ + kumJ K b v σ J)) ≤
      ‖acg φ α b k L ι v σ p J μ t0 t ((s : ℂ) / 2)‖ := by

  classical
  have hα'ne : ∀ j, α' j ≠ 0 := fun j => (H.hBH.2.2.1 j).1
  have hexp : ∀ j, Complex.exp (lamP φ α v L j) = φ (α' j) := fun j => (H.hBH.2.2.1 j).2
  have hKummer : KummerCond α' := H.hBH.2.2.2.1
  have hρ : ∀ j, rhoC φ α v L j ^ 2 = φ (α' j) := fun j =>
    rhoC_sq (Lm := L) (φ := φ) (α' := α') (α := α) (v := v) hexp j
  haveI hNF : NumberField (EL φ (rhoC φ α v L)) := EL_numberField hρ
  have hmem := est17_acg_mem H J μ t0 t s
  have hg0 : gamE α v L φ b k p J μ t0 t s hmem ≠ 0 := by
    intro h
    apply hg
    have h1 : ((gamE α v L φ b k p J μ t0 t s hmem : EL φ (rhoC φ α v L)) : ℂ) = 0 := by
      rw [h]; simp
    simpa [gamE_coe] using h1
  have hfinrank : (Module.finrank ℚ (EL φ (rhoC φ α v L)) : ℝ) = (2 : ℝ) ^ r * (dK K : ℝ) := by
    rw [est17_finrank hα'ne hρ hKummer]
    push_cast
    ring
  have hheightid : (∑ w : NumberField.InfinitePlace (EL φ (rhoC φ α v L)), (w.mult : ℝ) *
        Real.log (⨆ lm, w (inclE φ (rhoC φ α v L) (p lm))))
      + (∑ᶠ w : NumberField.FinitePlace (EL φ (rhoC φ α v L)),
          Real.log (⨆ lm, w (inclE φ (rhoC φ α v L) (p lm))))
      = Height.logHeight (fun lm => inclE φ (rhoC φ α v L) (p lm)) :=
    est15_height_id _ (by
      intro h
      apply H.hp0
      funext lm
      have h1 : inclE φ (rhoC φ α v L) (p lm) = 0 := congrFun h lm
      exact (inclE φ (rhoC φ α v L)).injective (by simpa using h1))
  have hheight := est17_height_ext_local hα'ne hρ hKummer p
  have h2sum := est17_finsum_log_two hα'ne hρ hKummer
  obtain ⟨hsupA, hOmg, h2supp, -⟩ := est17_fin_supports (K := K) (φ := φ) (α := α)
    (b := b) (k := k) (v := v) (L := L) (α' := α') (σl := σ) H.hp0 s J
  have hslack : (∑ j : Fin r, (pDj r (dK K) σ j : ℝ) * Height.logHeight₁ (α' j)) ≤ acD K σ :=
    (num_est15_slacks H 0).2.1
  have hOmega : (∑ w ∈ Finset.univ.erase (w0 φ (rhoC φ α v L)), (w.mult : ℝ) *
        (∑ j, (pDj r (dK K) σ j : ℝ) *
          (if 0 ≤ s then w (inclE φ (rhoC φ α v L) (α' j))
             else (w (inclE φ (rhoC φ α v L) (α' j)))⁻¹).posLog))
      + (∑ᶠ w : NumberField.FinitePlace (EL φ (rhoC φ α v L)),
          ∑ j, (pDj r (dK K) σ j : ℝ) *
            (if 0 ≤ s then w (inclE φ (rhoC φ α v L) (α' j))
               else (w (inclE φ (rhoC φ α v L) (α' j)))⁻¹).posLog)
      ≤ (2 : ℝ) ^ r * acD K σ := by
    have hbase := est17_Omega_sum (K := K) (r := r) (φ := φ) (ρ := rhoC φ α v L) (α' := α') (σl := σ) hα'ne s
    have h1 : (∑ j : Fin r, (pDj r (dK K) σ j : ℝ) *
        Height.logHeight₁ (inclE φ (rhoC φ α v L) (α' j)))
        = (2 : ℝ) ^ r * (∑ j : Fin r, (pDj r (dK K) σ j : ℝ) * Height.logHeight₁ (α' j)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by
        rw [est17_height_ext1 hα'ne hρ hKummer (α' j)]
        ring)
    rw [h1] at hbase
    exact le_trans hbase (mul_le_mul_of_nonneg_left hslack (by positivity))
  have hnum := est17_num2 H J Tst hTst s
  have hsup_pos_of : ∀ w : NumberField.InfinitePlace (EL φ (rhoC φ α v L)),
      0 < ⨆ lm, w (inclE φ (rhoC φ α v L) (p lm)) := by
    intro w
    obtain ⟨lm₀, hl₀⟩ := Function.ne_iff.mp H.hp0
    refine lt_of_lt_of_le ?_ (le_ciSup_of_le (Finite.bddAbove_range _) lm₀ le_rfl)
    exact (NumberField.InfinitePlace.pos_iff (w := w)).mpr
      (fun h => hl₀ ((inclE φ (rhoC φ α v L)).injective (by simpa using h)))
  have hsup_pos_fin : ∀ w : NumberField.FinitePlace (EL φ (rhoC φ α v L)),
      0 < ⨆ lm, w (inclE φ (rhoC φ α v L) (p lm)) := by
    intro w
    obtain ⟨lm₀, hl₀⟩ := Function.ne_iff.mp H.hp0
    refine lt_of_lt_of_le ?_ (le_ciSup_of_le (Finite.bddAbove_range _) lm₀ le_rfl)
    exact (NumberField.FinitePlace.pos_iff (w := w)).mpr
      (fun h => hl₀ ((inclE φ (rhoC φ α v L)).injective (by simpa using h)))
  have harch : ∀ w (hw : w ≠ w0 φ (rhoC φ α v L)),
      Real.log (w (gamE α v L φ b k p J μ t0 t s hmem)) ≤
        Real.log (⨆ lm, w (inclE φ (rhoC φ α v L) (p lm)))
        + ((acH K b v : ℝ) * Tst
          + (0.203 + 0.007 * ((((|s| : ℤ) : ℝ) / 2 / 2 ^ J) / acS K r b v))
              * acS K r b v * acD K σ / (dK K : ℝ)
          + Real.log ((acH K b v : ℝ) * ((pD0 r (dK K) σ : ℝ) + 1)
              * ∏ j, ((pDj r (dK K) σ j : ℝ) + 1))
          + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * ∑ j, (pDj r (dK K) σ j : ℝ) *
              (if 0 ≤ s then w (inclE φ (rhoC φ α v L) (α' j))
                 else (w (inclE φ (rhoC φ α v L) (α' j)))⁻¹).posLog) := by
    intro w hw
    have hb := est17_arch H J μ Tst hTst t0 t ht s hmem w hw
    have hwg : 0 < w (gamE α v L φ b k p J μ t0 t s hmem) :=
      (NumberField.InfinitePlace.pos_iff (w := w)).mpr hg0
    have h1 := Real.log_le_log hwg hb
    rwa [Real.log_mul (ne_of_gt (hsup_pos_of w)) (Real.exp_ne_zero _), Real.log_exp] at h1
  have hfin : ∀ w : NumberField.FinitePlace (EL φ (rhoC φ α v L)),
      Real.log (w (gamE α v L φ b k p J μ t0 t s hmem)) ≤
        Real.log (⨆ lm, w (inclE φ (rhoC φ α v L) (p lm)))
        + (((|s| : ℤ) : ℝ) / 2 / 2 ^ J) * ∑ j, (pDj r (dK K) σ j : ℝ) *
            (if 0 ≤ s then w (inclE φ (rhoC φ α v L) (α' j))
               else (w (inclE φ (rhoC φ α v L) (α' j)))⁻¹).posLog
        + 2 * ((J : ℝ) + 1) * (acH K b v : ℝ) * ((pD0 r (dK K) σ : ℝ) + 1)
            * |Real.log (w (inclE φ (rhoC φ α v L) (2 : K)))| := by
    intro w
    have hb := est17_fin H J μ Tst hTst t0 t ht s hmem w
    have hwg : 0 < w (gamE α v L φ b k p J μ t0 t s hmem) :=
      (NumberField.FinitePlace.pos_iff (w := w)).mpr hg0
    have h1 := Real.log_le_log hwg hb
    rw [Real.log_mul (ne_of_gt (hsup_pos_fin w)) (Real.exp_ne_zero _), Real.log_exp] at h1
    rw [← add_assoc] at h1
    exact h1
  exact est17_core H J μ Tst t0 t ht s (gamE α v L φ b k p J μ t0 t s hmem) rfl hg0
    hfinrank hheightid hheight hOmega h2sum hOmg hsupA h2supp hnum harch hfin

end Work.BW
