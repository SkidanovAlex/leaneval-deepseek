import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Op.diagShift_spec
import Submission.Work.TMC16Core.Op.geomWeight_ratio
import Submission.Work.TMC16Core.Op.geomWeight_support
import Submission.Work.TMC16Core.Op.norm_sum_single_four

open LeanEval.Analysis.TenMartini
open scoped Topology ENNReal
open Filter

set_option maxHeartbeats 1000000

noncomputable section

namespace Work.TMC16Core.Basic

/-! ## Auxiliary facts proved elsewhere in the workspace

These are proved in `Submission/Work/TMC16Core/Op/`. -/

private theorem diagShift_aux (c : ℤ → ℂ) (k : ℤ) (K : ℝ) (hK : ∀ n, ‖c n‖ ≤ K) :
    ∃ T : EllTwo →L[ℂ] EllTwo, (∀ f n, T f n = c n * f (n + k)) ∧ ‖T‖ ≤ K :=
  Work.TMC16Core.Op.diagShift_spec c k K hK

private theorem geomWeight_ratio_aux {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (n₀ n : ℤ) :
    |ρ ^ ((n - n₀).natAbs) / ρ ^ ((n + 1 - n₀).natAbs) - 1| ≤ (1 - ρ) / ρ ∧
      |ρ ^ ((n - n₀).natAbs) / ρ ^ ((n - 1 - n₀).natAbs) - 1| ≤ (1 - ρ) / ρ :=
  Work.TMC16Core.Op.geomWeight_ratio hρ0 hρ1 n₀ n

private theorem geomWeight_support_aux {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (n₀ : ℤ) (N : ℕ)
    (hb : n₀.natAbs ≤ N) :
    ∀ z : ℤ, (z = (N : ℤ) + 1 ∨ z = (N : ℤ) ∨ z = -((N : ℤ)) ∨ z = -((N : ℤ) + 1)) →
      ρ ^ ((z - n₀).natAbs) ≤ ρ ^ (N - n₀.natAbs) :=
  Work.TMC16Core.Op.geomWeight_support hρ0 hρ1 n₀ N hb

private theorem norm_sum_single_four_aux {s : Finset ℤ} {f : ℤ → ℂ} {L : ℝ} (hL : 0 ≤ L)
    (hs : s.card ≤ 4) (h : ∀ i ∈ s, ‖f i‖ ≤ L) :
    ‖∑ i ∈ s, lp.single 2 i (f i)‖ ≤ 2 * L :=
  Work.TMC16Core.Op.norm_sum_single_four hL hs h

/-- The elementary limit `(m+2)ρ^m → 0` for `0 < ρ < 1`. -/
private theorem geomTendsto_aux (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) :
    Tendsto (fun m : ℕ => ((m : ℝ) + 2) * ρ ^ m) atTop (𝓝 0) := by
  have hsum : Summable (fun m : ℕ => (m : ℝ) * ρ ^ m) := by
    simpa [pow_one] using
      (summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := ρ)
        (by rw [Real.norm_eq_abs, abs_of_pos hρ0]; exact hρ1))
  have h1 : Tendsto (fun m : ℕ => (m : ℝ) * ρ ^ m) atTop (𝓝 0) := hsum.tendsto_atTop_zero
  have h2 : Tendsto (fun m : ℕ => (2 : ℝ) * ρ ^ m) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hρ0.le hρ1).const_mul (2 : ℝ)
  have h3 := h1.add h2
  have heq : (fun m : ℕ => ((m : ℝ) + 2) * ρ ^ m)
      = fun m : ℕ => (m : ℝ) * ρ ^ m + 2 * ρ ^ m := by
    funext m; ring
  rw [heq]
  simpa using h3

/-- The geometric weight `ρ^{|n-n₀|}` as a complex-valued multiplier. -/
private def wt (ρ : ℝ) (n₀ : ℤ) (n : ℤ) : ℂ := ((ρ ^ ((n - n₀).natAbs) : ℝ) : ℂ)

/-- The symmetric cutoff indicator `1_{[-Np,Np]}`. -/
private def ind (Np : ℤ) (m : ℤ) : ℂ := if -Np ≤ m ∧ m ≤ Np then (1 : ℂ) else 0

/-- The standard basis vector `δ_m` of `ℓ²(ℤ)`, as an element of `EllTwo`. -/
private def delta (m : ℤ) (c : ℂ) : EllTwo := lp.single (E := fun _ : ℤ => ℂ) 2 m c

private theorem delta_self (m : ℤ) (c : ℂ) : delta m c m = c := by
  show lp.single (E := fun _ : ℤ => ℂ) 2 m c m = c
  exact lp.single_apply_self (E := fun _ : ℤ => ℂ) 2 m c

private theorem delta_ne (m : ℤ) (c : ℂ) {j : ℤ} (h : j ≠ m) : delta m c j = 0 := by
  show lp.single (E := fun _ : ℤ => ℂ) 2 m c j = 0
  exact lp.single_apply_ne (E := fun _ : ℤ => ℂ) 2 m c h

/-- A polynomially bounded nonzero formal solution of the almost Mathieu equation forces
the energy into the spectrum (the "easy" direction of Schnol's theorem, proved by a
weighted-resolvent / Combes-Thomas argument). -/
private theorem mem_spectrum_of_genEigen {α lam θ E : ℝ}
    (H : EllTwo →L[ℂ] EllTwo)
    (hcoord : ∀ (f : EllTwo) (n : ℤ),
      H f n = f (n + 1) + f (n - 1) + ((amoPot α lam θ n : ℝ) : ℂ) * f n)
    (hnotspec : (E : ℂ) ∉ spectrum ℂ H)
    {u : ℤ → ℂ} (hueq : ∀ n : ℤ, amoAct α lam θ u n = (E : ℂ) * u n)
    {C : ℝ} (hCb : ∀ n : ℤ, ‖u n‖ ≤ C * (1 + |(n : ℝ)|))
    {n₀ : ℤ} (hn₀ : u n₀ ≠ 0) : False := by
  have hunit : IsUnit ((E : ℂ) • (1 : EllTwo →L[ℂ] EllTwo) - H) := by
    by_contra hc
    exact hnotspec (by
      rw [spectrum.mem_iff, Algebra.algebraMap_eq_smul_one]
      exact hc)
  obtain ⟨v, hv⟩ := hunit
  set S : EllTwo →L[ℂ] EllTwo := (E : ℂ) • 1 - H with hSdef
  set R : EllTwo →L[ℂ] EllTwo := ↑(v⁻¹) with hRdef
  have hvS : (↑v : EllTwo →L[ℂ] EllTwo) = S := by rw [hSdef]; exact hv
  have hRS : R * S = 1 := by
    rw [hRdef, ← hvS]
    exact Units.inv_mul v
  have hRbound : ∀ f : EllTwo, ‖f‖ ≤ ‖R‖ * ‖S f‖ := by
    intro f
    have hmul : (R * S) f = (1 : EllTwo →L[ℂ] EllTwo) f := by rw [hRS]
    have h1 : R (S f) = f := by
      simpa [ContinuousLinearMap.mul_apply, ContinuousLinearMap.one_apply] using hmul
    calc ‖f‖ = ‖R (S f)‖ := by rw [h1]
      _ ≤ ‖R‖ * ‖S f‖ := ContinuousLinearMap.le_opNorm R (S f)
  have hRne : R ≠ 0 := by
    intro h0
    have h : R * S = 0 := by rw [h0, zero_mul]
    rw [hRS] at h
    have h1 : (lp.single 2 (0 : ℤ) (1 : ℂ) : EllTwo) = 0 := by
      have h2 := congrArg (fun (T : EllTwo →L[ℂ] EllTwo) => T (lp.single 2 (0 : ℤ) (1 : ℂ))) h
      simpa using h2
    have h3 : (1 : ℂ) = 0 := by
      have h2 := congrArg (fun (f : EllTwo) => f (0 : ℤ)) h1
      simpa [lp.single_apply_self] using h2
    exact one_ne_zero h3
  have hRpos : 0 < ‖R‖ := norm_pos_iff.mpr hRne
  -- the geometric decay rate
  set ε : ℝ := min (1 / 4) (3 / (16 * ‖R‖)) with hεdef
  have hε0 : 0 < ε := by
    rw [hεdef]
    exact lt_min (by norm_num) (by positivity)
  have hεle : ε ≤ 1 / 4 := by rw [hεdef]; exact min_le_left _ _
  have hεr : ε ≤ 3 / (16 * ‖R‖) := by rw [hεdef]; exact min_le_right _ _
  set ρ : ℝ := 1 - ε with hρdef
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith
  have hρ1 : ρ ≤ 1 := by rw [hρdef]; linarith
  have hδ : 2 * ((1 - ρ) / ρ) * ‖R‖ ≤ 1 / 2 := by
    have h1 : (1 - ρ) / ρ = ε / (1 - ε) := by
      rw [hρdef]; congr 1; ring
    rw [h1]
    have h2 : (0 : ℝ) < 1 - ε := by linarith
    have h3 : ε / (1 - ε) ≤ ε * (4 / 3) := by
      rw [div_le_iff₀ h2]
      nlinarith
    have h4 : ε * (4 / 3) * ‖R‖ ≤ 1 / 4 := by
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * ‖R‖)] at hεr
      nlinarith
    nlinarith [h3, h4, norm_nonneg R]
  -- normalise the polynomial growth bound
  set C' : ℝ := max C 0 with hC'def
  have hC'0 : 0 ≤ C' := by rw [hC'def]; exact le_max_right _ _
  have hC'b : ∀ n : ℤ, ‖u n‖ ≤ C' * (1 + |(n : ℝ)|) := by
    intro n
    have h2 : (0 : ℝ) ≤ 1 + |(n : ℝ)| := by positivity
    refine le_trans (hCb n) (mul_le_mul_of_nonneg_right ?_ h2)
    rw [hC'def]; exact le_max_left _ _
  set b : ℕ := n₀.natAbs with hbdef
  -- the main estimate, at every cutoff scale N
  have key : ∀ N : ℕ, b + 1 ≤ N →
      ‖u n₀‖ ≤ 4 * ‖R‖ * C' * ((N : ℝ) + 2) * ρ ^ (N - b) := by
    intro N hN
    have hbN : n₀.natAbs ≤ N := by omega
    have hN1 : 1 ≤ N := by omega
    set Np : ℤ := (N : ℤ) with hNpdef
    have hNpcast : (Np : ℝ) = (N : ℝ) := by rw [hNpdef]; simp
    have hNp0 : (0 : ℤ) ≤ Np := by rw [hNpdef]; exact_mod_cast Nat.zero_le N
    have hNp1 : (1 : ℤ) ≤ Np := by rw [hNpdef]; exact_mod_cast hN1
    set ψ : EllTwo := ∑ m ∈ Finset.Icc (-Np) Np, delta m (u m) with hψdef
    have hψcoord : ∀ m : ℤ, ψ m = ind Np m * u m := by
      intro m
      rw [hψdef, lp.coeFn_sum, Finset.sum_apply]
      by_cases hm : m ∈ Finset.Icc (-Np) Np
      · have h0 : ∀ z ∈ Finset.Icc (-Np) Np, z ≠ m → delta z (u z) m = 0 := by
          intro z _ hz
          exact delta_ne z (u z) (Ne.symm hz)
        rw [Finset.sum_eq_single m h0]
        · rw [delta_self]
          unfold ind
          rw [if_pos (Finset.mem_Icc.mp hm)]
          ring
        · intro hm2
          exact absurd hm hm2
      · have h0 : ∀ z ∈ Finset.Icc (-Np) Np, delta z (u z) m = 0 := by
          intro z hz
          have h1 : -Np ≤ z ∧ z ≤ Np := Finset.mem_Icc.mp hz
          have h2 : ¬ (-Np ≤ m ∧ m ≤ Np) := by rwa [Finset.mem_Icc] at hm
          have hzm : z ≠ m := by
            intro hzm
            exact h2 (hzm ▸ h1)
          exact delta_ne z (u z) (Ne.symm hzm)
        rw [Finset.sum_eq_zero h0]
        unfold ind
        have h2 : ¬ (-Np ≤ m ∧ m ≤ Np) := by rwa [Finset.mem_Icc] at hm
        rw [if_neg h2]
        ring
    have hScoord : ∀ f : EllTwo, ∀ n : ℤ, S f n =
        (E : ℂ) * f n - (f (n + 1) + f (n - 1) + ((amoPot α lam θ n : ℝ) : ℂ) * f n) := by
      intro f n
      rw [hSdef]
      rw [show ((E : ℂ) • (1 : EllTwo →L[ℂ] EllTwo) - H) f n
          = (E : ℂ) * f n - H f n from rfl, hcoord f n]
    have hSψval : ∀ n : ℤ, S ψ n =
        (ind Np n - ind Np (n + 1)) * u (n + 1) + (ind Np n - ind Np (n - 1)) * u (n - 1) := by
      intro n
      have hEu : (E : ℂ) * u n = u (n + 1) + u (n - 1) + ((amoPot α lam θ n : ℝ) : ℂ) * u n :=
        (hueq n).symm
      rw [hScoord ψ n, hψcoord n, hψcoord (n + 1), hψcoord (n - 1),
        show (E : ℂ) * (ind Np n * u n) = ind Np n * ((E : ℂ) * u n) from by ring, hEu]
      ring
    have hIvalN : ind Np Np = 1 := by
      unfold ind
      rw [if_pos (by omega : -Np ≤ Np ∧ Np ≤ Np)]
    have hIvalN1 : ind Np (Np + 1) = 0 := by
      unfold ind
      rw [if_neg (by omega : ¬ (-Np ≤ Np + 1 ∧ Np + 1 ≤ Np))]
    have hIvalN2 : ind Np (Np + 2) = 0 := by
      unfold ind
      rw [if_neg (by omega : ¬ (-Np ≤ Np + 2 ∧ Np + 2 ≤ Np))]
    have hIvalNm1 : ind Np (Np - 1) = 1 := by
      unfold ind
      rw [if_pos (by omega : -Np ≤ Np - 1 ∧ Np - 1 ≤ Np)]
    have hIvalmN : ind Np (-Np) = 1 := by
      unfold ind
      rw [if_pos (by omega : -Np ≤ -Np ∧ -Np ≤ Np)]
    have hIvalmN1 : ind Np (-Np + 1) = 1 := by
      unfold ind
      rw [if_pos (by omega : -Np ≤ -Np + 1 ∧ -Np + 1 ≤ Np)]
    have hIvalmNm1 : ind Np (-Np - 1) = 0 := by
      unfold ind
      rw [if_neg (by omega : ¬ (-Np ≤ -Np - 1 ∧ -Np - 1 ≤ Np))]
    have hIvalmN2 : ind Np (-Np - 2) = 0 := by
      unfold ind
      rw [if_neg (by omega : ¬ (-Np ≤ -Np - 2 ∧ -Np - 2 ≤ Np))]
    have hval1 : S ψ Np = u (Np + 1) := by
      have h := hSψval Np
      rw [h, hIvalN, hIvalN1, hIvalNm1]
      ring
    have hval2 : S ψ (Np + 1) = -u Np := by
      have h := hSψval (Np + 1)
      rw [show Np + 1 + 1 = Np + 2 from by ring, show Np + 1 - 1 = Np from by ring] at h
      rw [h, hIvalN1, hIvalN2, hIvalN]
      ring
    have hval3 : S ψ (-Np) = u (-Np - 1) := by
      have h := hSψval (-Np)
      rw [show -Np + 1 = -Np + 1 from rfl] at h
      rw [h, hIvalmN, hIvalmN1, hIvalmNm1]
      ring
    have hval4 : S ψ (-Np - 1) = -u (-Np) := by
      have h := hSψval (-Np - 1)
      rw [show -Np - 1 + 1 = -Np from by ring, show -Np - 1 - 1 = -Np - 2 from by ring] at h
      rw [h, hIvalmNm1, hIvalmN, hIvalmN2]
      ring
    have hIup : ∀ n : ℤ, n ≠ Np → n ≠ -Np - 1 → ind Np n = ind Np (n + 1) := by
      intro n hn1 hn2
      have hiff : (-Np ≤ n ∧ n ≤ Np) ↔ (-Np ≤ n + 1 ∧ n + 1 ≤ Np) := by
        constructor
        · intro hc; exact ⟨by omega, by omega⟩
        · intro hc; exact ⟨by omega, by omega⟩
      unfold ind
      rw [if_congr hiff rfl rfl]
    have hIdn : ∀ n : ℤ, n ≠ Np + 1 → n ≠ -Np → ind Np n = ind Np (n - 1) := by
      intro n hn1 hn2
      have hiff : (-Np ≤ n ∧ n ≤ Np) ↔ (-Np ≤ n - 1 ∧ n - 1 ≤ Np) := by
        constructor
        · intro hc; exact ⟨by omega, by omega⟩
        · intro hc; exact ⟨by omega, by omega⟩
      unfold ind
      rw [if_congr hiff rfl rfl]
    have hzero : ∀ n : ℤ, n ≠ Np → n ≠ Np + 1 → n ≠ -Np → n ≠ -Np - 1 → S ψ n = 0 := by
      intro n h1 h2 h3 h4
      rw [hSψval n, ← hIup n h1 h4, ← hIdn n h2 h3]
      ring
    -- the weight, the weighted solution, and the perturbation operators
    have hwmem : Memℓp (fun n : ℤ => wt ρ n₀ n * ψ n) 2 := by
      refine Memℓp.mono (lp.memℓp ψ).norm (fun n => ?_)
      show ‖wt ρ n₀ n * ψ n‖ ≤ ‖ψ n‖
      have h1 : ‖wt ρ n₀ n‖ ≤ 1 := by
        have h2 : ‖wt ρ n₀ n‖ = |ρ ^ ((n - n₀).natAbs)| := RCLike.norm_ofReal _
        rw [h2, abs_of_nonneg (pow_nonneg hρ0.le _)]
        exact pow_le_one₀ hρ0.le hρ1
      calc ‖wt ρ n₀ n * ψ n‖ = ‖wt ρ n₀ n‖ * ‖ψ n‖ := norm_mul _ _
        _ ≤ 1 * ‖ψ n‖ := by gcongr
        _ = ‖ψ n‖ := one_mul _
    set ξ : EllTwo := ⟨fun n : ℤ => wt ρ n₀ n * ψ n, hwmem⟩ with hξdef
    have hξc : ∀ n : ℤ, ξ n = wt ρ n₀ n * ψ n := fun n => rfl
    have hwne : ∀ m : ℤ, wt ρ n₀ m ≠ 0 := by
      intro m h
      have h1 : ‖wt ρ n₀ m‖ = 0 := by rw [h, norm_zero]
      have h2 : 0 < ‖wt ρ n₀ m‖ := by
        have h3 : ‖wt ρ n₀ m‖ = |ρ ^ ((m - n₀).natAbs)| := RCLike.norm_ofReal _
        rw [h3, abs_of_pos (pow_pos hρ0 _)]
        exact pow_pos hρ0 _
      linarith
    have hc1 : ∀ n : ℤ, ‖(1 : ℂ) - wt ρ n₀ n / wt ρ n₀ (n + 1)‖ ≤ (1 - ρ) / ρ := by
      intro n
      have h := (geomWeight_ratio_aux hρ0 hρ1 n₀ n).1
      have h2 : ‖(1 : ℂ) - wt ρ n₀ n / wt ρ n₀ (n + 1)‖
          = |1 - ρ ^ ((n - n₀).natAbs) / ρ ^ ((n + 1 - n₀).natAbs)| := by
        rw [show wt ρ n₀ n = (((ρ ^ ((n - n₀).natAbs) : ℝ)) : ℂ) from rfl,
          show wt ρ n₀ (n + 1) = (((ρ ^ ((n + 1 - n₀).natAbs) : ℝ)) : ℂ) from rfl,
          ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_sub]
        exact RCLike.norm_ofReal _
      rw [h2, abs_sub_comm]
      exact h
    have hc2 : ∀ n : ℤ, ‖(1 : ℂ) - wt ρ n₀ n / wt ρ n₀ (n - 1)‖ ≤ (1 - ρ) / ρ := by
      intro n
      have h := (geomWeight_ratio_aux hρ0 hρ1 n₀ n).2
      have h2 : ‖(1 : ℂ) - wt ρ n₀ n / wt ρ n₀ (n - 1)‖
          = |1 - ρ ^ ((n - n₀).natAbs) / ρ ^ ((n - 1 - n₀).natAbs)| := by
        rw [show wt ρ n₀ n = (((ρ ^ ((n - n₀).natAbs) : ℝ)) : ℂ) from rfl,
          show wt ρ n₀ (n - 1) = (((ρ ^ ((n - 1 - n₀).natAbs) : ℝ)) : ℂ) from rfl,
          ← Complex.ofReal_one, ← Complex.ofReal_div, ← Complex.ofReal_sub]
        exact RCLike.norm_ofReal _
      rw [h2, abs_sub_comm]
      exact h
    obtain ⟨T₁, hT₁c, hT₁n⟩ :=
      diagShift_aux (fun n : ℤ => (1 : ℂ) - wt ρ n₀ n / wt ρ n₀ (n + 1)) 1 ((1 - ρ) / ρ) hc1
    obtain ⟨T₂, hT₂c, hT₂n⟩ :=
      diagShift_aux (fun n : ℤ => (1 : ℂ) - wt ρ n₀ n / wt ρ n₀ (n - 1)) (-1) ((1 - ρ) / ρ) hc2
    set d : EllTwo := -(T₁ ξ + T₂ ξ) with hddef
    have hdnorm : ‖d‖ ≤ 2 * ((1 - ρ) / ρ) * ‖ξ‖ := by
      have e1 : ‖T₁ ξ‖ ≤ (1 - ρ) / ρ * ‖ξ‖ :=
        (ContinuousLinearMap.le_opNorm T₁ ξ).trans
          (mul_le_mul_of_nonneg_right hT₁n (norm_nonneg ξ))
      have e2 : ‖T₂ ξ‖ ≤ (1 - ρ) / ρ * ‖ξ‖ :=
        (ContinuousLinearMap.le_opNorm T₂ ξ).trans
          (mul_le_mul_of_nonneg_right hT₂n (norm_nonneg ξ))
      have h1 : ‖d‖ ≤ ‖T₁ ξ + T₂ ξ‖ := by rw [hddef]; exact le_of_eq (norm_neg _)
      have h2 : ‖T₁ ξ + T₂ ξ‖ ≤ ‖T₁ ξ‖ + ‖T₂ ξ‖ := norm_add_le _ _
      linarith
    -- the weighted defect
    set ESupp : Finset ℤ := {-Np - 1, -Np, Np, Np + 1} with hESuppdef
    set we : EllTwo := ∑ z ∈ ESupp, delta z (wt ρ n₀ z * (S ψ) z) with hwedef
    have hwecoord : ∀ n : ℤ, we n = wt ρ n₀ n * (S ψ) n := by
      intro n
      rw [hwedef, lp.coeFn_sum, Finset.sum_apply]
      by_cases hn : n ∈ ESupp
      · have h0 : ∀ z ∈ ESupp, z ≠ n → delta z (wt ρ n₀ z * (S ψ) z) n = 0 := by
          intro z _ hz
          exact delta_ne z (wt ρ n₀ z * (S ψ) z) (Ne.symm hz)
        rw [Finset.sum_eq_single n h0]
        · rw [delta_self]
        · intro hn2
          exact absurd hn hn2
      · have h0 : ∀ z ∈ ESupp, delta z (wt ρ n₀ z * (S ψ) z) n = 0 := by
          intro z hz
          have h1 : z = -Np - 1 ∨ z = -Np ∨ z = Np ∨ z = Np + 1 := by
            simpa only [hESuppdef, Finset.mem_insert, Finset.mem_singleton] using hz
          have h2 : n ≠ -Np - 1 ∧ n ≠ -Np ∧ n ≠ Np ∧ n ≠ Np + 1 := by
            simpa only [hESuppdef, Finset.mem_insert, Finset.mem_singleton, not_or] using hn
          have hzn : z ≠ n := by rcases h1 with h | h | h | h <;> omega
          exact delta_ne z (wt ρ n₀ z * (S ψ) z) (Ne.symm hzn)
        rw [Finset.sum_eq_zero h0]
        have h2 : n ≠ -Np - 1 ∧ n ≠ -Np ∧ n ≠ Np ∧ n ≠ Np + 1 := by
          simpa only [hESuppdef, Finset.mem_insert, Finset.mem_singleton, not_or] using hn
        rw [hzero n h2.2.2.1 h2.2.2.2 h2.2.1 h2.1, mul_zero]
    have hwe_norm : ‖we‖ ≤ 2 * (C' * ((N : ℝ) + 2) * ρ ^ (N - b)) := by
      rw [hwedef]
      refine norm_sum_single_four_aux (s := ESupp) (f := fun z : ℤ => wt ρ n₀ z * (S ψ) z)
        (L := C' * ((N : ℝ) + 2) * ρ ^ (N - b)) (by positivity) ?_ ?_
      · rw [hESuppdef]
        have h2 : ({-Np - 1, -Np, Np, Np + 1} : Finset ℤ)
            = insert (-Np - 1) (insert (-Np) (insert Np (insert (Np + 1) ∅))) := rfl
        rw [h2]
        have h3 := Finset.card_insert_le (-Np - 1)
          (insert (-Np) (insert Np (insert (Np + 1) ∅)) : Finset ℤ)
        have h4 := Finset.card_insert_le (-Np) (insert Np (insert (Np + 1) ∅) : Finset ℤ)
        have h5 := Finset.card_insert_le Np (insert (Np + 1) ∅ : Finset ℤ)
        have h6 := Finset.card_insert_le (Np + 1) (∅ : Finset ℤ)
        simp only [Finset.card_empty] at h6
        omega
      · intro z hz
        have hz' : z = -Np - 1 ∨ z = -Np ∨ z = Np ∨ z = Np + 1 := by
          simpa only [hESuppdef, Finset.mem_insert, Finset.mem_singleton] using hz
        have hwz : ‖wt ρ n₀ z‖ ≤ ρ ^ (N - b) := by
          have hs : z = (N : ℤ) + 1 ∨ z = (N : ℤ) ∨ z = -((N : ℤ)) ∨ z = -((N : ℤ) + 1) := by
            rcases hz' with h | h | h | h
            · exact Or.inr (Or.inr (Or.inr (by rw [h, hNpdef]; ring)))
            · exact Or.inr (Or.inr (Or.inl (by rw [h, hNpdef])))
            · exact Or.inr (Or.inl (by rw [h, hNpdef]))
            · exact Or.inl (by rw [h, hNpdef])
          have hsup := geomWeight_support_aux hρ0 hρ1 n₀ N hbN z (by
            rcases hs with h | h | h | h
            · exact Or.inl h
            · exact Or.inr (Or.inl h)
            · exact Or.inr (Or.inr (Or.inl h))
            · exact Or.inr (Or.inr (Or.inr h)))
          have h2 : ‖wt ρ n₀ z‖ = |ρ ^ ((z - n₀).natAbs)| := RCLike.norm_ofReal _
          rw [h2, abs_of_nonneg (pow_nonneg hρ0.le _)]
          exact hsup
        have hb1 : ‖u (Np + 1)‖ ≤ C' * ((N : ℝ) + 2) := by
          have h := hC'b (Np + 1)
          have h1 : |(((Np + 1 : ℤ)) : ℝ)| ≤ (N : ℝ) + 1 := by
            have h2 : (((Np + 1 : ℤ)) : ℝ) = (N : ℝ) + 1 := by push_cast; rw [hNpcast]
            rw [h2, abs_of_nonneg (by positivity)]
          nlinarith [h, h1, hC'0]
        have hb2 : ‖u Np‖ ≤ C' * ((N : ℝ) + 2) := by
          have h := hC'b Np
          have h1 : |((Np : ℤ) : ℝ)| ≤ (N : ℝ) + 1 := by
            rw [hNpcast, abs_of_nonneg (by positivity)]
            linarith
          nlinarith [h, h1, hC'0]
        have hb3 : ‖u (-Np - 1)‖ ≤ C' * ((N : ℝ) + 2) := by
          have h := hC'b (-Np - 1)
          have h1 : |(((-Np - 1 : ℤ)) : ℝ)| ≤ (N : ℝ) + 1 := by
            have h2 : (((-Np - 1 : ℤ)) : ℝ) = -((N : ℝ) + 1) := by push_cast; rw [hNpcast]; ring
            rw [h2, abs_neg, abs_of_nonneg (by positivity)]
          nlinarith [h, h1, hC'0]
        have hb4 : ‖u (-Np)‖ ≤ C' * ((N : ℝ) + 2) := by
          have h := hC'b (-Np)
          have h1 : |(((-Np : ℤ)) : ℝ)| ≤ (N : ℝ) + 1 := by
            have h2 : (((-Np : ℤ)) : ℝ) = -(N : ℝ) := by push_cast; rw [hNpcast]
            rw [h2, abs_neg, abs_of_nonneg (by positivity)]
            linarith
          nlinarith [h, h1, hC'0]
        have hSz : ‖(S ψ) z‖ ≤ C' * ((N : ℝ) + 2) := by
          rcases hz' with h | h | h | h
          · rw [h, hval4, norm_neg]; exact hb4
          · rw [h, hval3]; exact hb3
          · rw [h, hval1]; exact hb1
          · rw [h, hval2, norm_neg]; exact hb2
        calc ‖wt ρ n₀ z * (S ψ) z‖ = ‖wt ρ n₀ z‖ * ‖(S ψ) z‖ := norm_mul _ _
          _ ≤ ρ ^ (N - b) * (C' * ((N : ℝ) + 2)) :=
              mul_le_mul hwz hSz (norm_nonneg _) (by positivity)
          _ = C' * ((N : ℝ) + 2) * ρ ^ (N - b) := by ring
    -- the pointwise identity `S ξ = we + d`
    have hpoint : S ξ = we + d := by
      refine lp.ext (funext fun q => ?_)
      show S ξ q = we q + d q
      have hSξval : S ξ q = wt ρ n₀ q * (S ψ q) + (wt ρ n₀ q - wt ρ n₀ (q + 1)) * ψ (q + 1)
          + (wt ρ n₀ q - wt ρ n₀ (q - 1)) * ψ (q - 1) := by
        have hEψ : (E : ℂ) * ψ q =
            S ψ q + ψ (q + 1) + ψ (q - 1) + ((amoPot α lam θ q : ℝ) : ℂ) * ψ q := by
          rw [hScoord ψ q]
          ring
        rw [hScoord ξ q, hξc q, hξc (q + 1), hξc (q - 1),
          show (E : ℂ) * (wt ρ n₀ q * ψ q) = wt ρ n₀ q * ((E : ℂ) * ψ q) from by ring, hEψ]
        ring
      have hdval : d q = (wt ρ n₀ q - wt ρ n₀ (q + 1)) * ψ (q + 1)
          + (wt ρ n₀ q - wt ρ n₀ (q - 1)) * ψ (q - 1) := by
        have h1 : d q = -(T₁ ξ q + T₂ ξ q) := by
          rw [hddef]
          rfl
        have hw1 : wt ρ n₀ (q + 1) ≠ 0 := hwne (q + 1)
        have hw2 : wt ρ n₀ (q - 1) ≠ 0 := hwne (q - 1)
        rw [h1, hT₁c ξ q, hT₂c ξ q, show q + (-1) = q - 1 from by ring, hξc (q + 1),
          hξc (q - 1)]
        field_simp
        ring
      rw [hSξval, hwecoord q, hdval]
      ring
    have hξnorm : ‖ξ‖ ≤ 2 * ‖R‖ * ‖we‖ := by
      have hb1 : ‖ξ‖ ≤ ‖R‖ * ‖S ξ‖ := hRbound ξ
      have hb2 : ‖S ξ‖ ≤ ‖we‖ + ‖d‖ := by rw [hpoint]; exact norm_add_le _ _
      have hb3 : ‖d‖ ≤ 2 * ((1 - ρ) / ρ) * ‖ξ‖ := hdnorm
      have hb1' : ‖ξ‖ ≤ ‖R‖ * (‖we‖ + ‖d‖) :=
        hb1.trans (mul_le_mul_of_nonneg_left hb2 (norm_nonneg R))
      have hb4 : ‖R‖ * (‖we‖ + ‖d‖) ≤ ‖R‖ * (‖we‖ + 2 * ((1 - ρ) / ρ) * ‖ξ‖) := by
        gcongr
      have hb5 : ‖R‖ * (‖we‖ + 2 * ((1 - ρ) / ρ) * ‖ξ‖)
          = ‖R‖ * ‖we‖ + 2 * ((1 - ρ) / ρ) * ‖R‖ * ‖ξ‖ := by ring
      nlinarith [hb1', hb3, hb4, hb5, hδ, norm_nonneg ξ, norm_nonneg we,
        norm_nonneg d, norm_nonneg R, hRpos]
    have hξn₀ : ξ n₀ = u n₀ := by
      have h1 : wt ρ n₀ n₀ = 1 := by
        show (((ρ ^ ((n₀ - n₀).natAbs) : ℝ)) : ℂ) = 1
        rw [sub_self, Int.natAbs_zero, pow_zero]
        exact Complex.ofReal_one
      rw [hξc n₀, h1, one_mul, hψcoord n₀]
      have h2 : ind Np n₀ = 1 := by
        unfold ind
        have h4 : -(n₀.natAbs : ℤ) ≤ n₀ := by
          have h6 : -n₀ ≤ (((-n₀).natAbs : ℤ)) := Int.le_natAbs
          rw [Int.natAbs_neg] at h6
          omega
        have h5 : n₀ ≤ (n₀.natAbs : ℤ) := Int.le_natAbs
        have h3 : (n₀.natAbs : ℤ) ≤ (N : ℤ) := by exact_mod_cast hbN
        rw [if_pos (by rw [hNpdef]; exact ⟨by omega, by omega⟩)]
      rw [h2, one_mul]
    have hu_bound : ‖u n₀‖ ≤ ‖ξ‖ := by
      have h1 := lp.norm_apply_le_norm (p := 2) (by norm_num) ξ n₀
      rwa [hξn₀] at h1
    calc ‖u n₀‖ ≤ ‖ξ‖ := hu_bound
      _ ≤ 2 * ‖R‖ * ‖we‖ := hξnorm
      _ ≤ 2 * ‖R‖ * (2 * (C' * ((N : ℝ) + 2) * ρ ^ (N - b))) :=
            mul_le_mul_of_nonneg_left hwe_norm (by positivity)
      _ = 4 * ‖R‖ * C' * ((N : ℝ) + 2) * ρ ^ (N - b) := by ring
  -- the limiting argument: the bound at scale `m + b` decays away, contradicting `u n₀ ≠ 0`
  have hbase : Tendsto (fun m : ℕ => ((m : ℝ) + 2) * ρ ^ m) atTop (𝓝 0) :=
    geomTendsto_aux ρ hρ0 (by linarith)
  have hlim : Tendsto (fun m : ℕ => 4 * ‖R‖ * C' * ((b : ℝ) + 1) *
      (((m : ℝ) + 2) * ρ ^ m)) atTop (𝓝 0) := by
    have h := hbase.const_mul (4 * ‖R‖ * C' * ((b : ℝ) + 1))
    simpa [mul_assoc] using h
  have hpos : 0 < ‖u n₀‖ := norm_pos_iff.mpr hn₀
  have hev : ∀ᶠ m : ℕ in atTop,
      4 * ‖R‖ * C' * ((b : ℝ) + 1) * (((m : ℝ) + 2) * ρ ^ m) < ‖u n₀‖ :=
    hlim.eventually_lt_const hpos
  obtain ⟨m₁, hm₁⟩ := eventually_atTop.mp hev
  set m : ℕ := max m₁ 1 with hmdef
  have hm0 : m₁ ≤ m := le_max_left _ _
  have hkey := key (m + b) (by omega)
  have hsub : m + b - b = m := Nat.add_sub_cancel _ _
  rw [hsub] at hkey
  have hle : 4 * ‖R‖ * C' * (((m + b : ℕ) : ℝ) + 2) * ρ ^ m
      ≤ 4 * ‖R‖ * C' * ((b : ℝ) + 1) * (((m : ℝ) + 2) * ρ ^ m) := by
    have h1 : (((m + b : ℕ)) : ℝ) + 2 ≤ ((b : ℝ) + 1) * ((m : ℝ) + 2) := by
      rw [Nat.cast_add]
      have hb0 : (0 : ℝ) ≤ (b : ℝ) := Nat.cast_nonneg b
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      nlinarith [hb0, hm0]
    have h2 : 0 ≤ 4 * ‖R‖ * C' * ρ ^ m := by positivity
    calc 4 * ‖R‖ * C' * (((m + b : ℕ) : ℝ) + 2) * ρ ^ m
        = (4 * ‖R‖ * C' * ρ ^ m) * ((((m + b : ℕ)) : ℝ) + 2) := by ring
      _ ≤ (4 * ‖R‖ * C' * ρ ^ m) * (((b : ℝ) + 1) * ((m : ℝ) + 2)) :=
            mul_le_mul_of_nonneg_left h1 h2
      _ = 4 * ‖R‖ * C' * ((b : ℝ) + 1) * (((m : ℝ) + 2) * ρ ^ m) := by ring
  have hm := hm₁ m hm0
  linarith [hkey, hle, hm]

theorem genEigen_mem_spec (h1 : Work.TMC16Core.P_OpBasics) {α lam θ E : ℝ} (hα : Irrational α)
    {u : ℤ → ℂ} (hu : Work.TMC16Core.IsGenEigen α lam θ E u) :
    E ∈ Work.TMC16Core.amoSpec α lam := by
  obtain ⟨hune, hueq, C, hCb⟩ := hu
  obtain ⟨H, hH⟩ := h1.1 α lam θ
  have hcoord : ∀ (f : EllTwo) (n : ℤ),
      H f n = f (n + 1) + f (n - 1) + ((amoPot α lam θ n : ℝ) : ℂ) * f n := by
    intro f n
    simpa [IsAlmostMathieuOperator, amoPot] using hH f n
  have hspec : (E : ℂ) ∈ spectrum ℂ H := by
    by_contra hnotspec
    obtain ⟨n₀, hn₀⟩ : ∃ n₀ : ℤ, u n₀ ≠ 0 := by
      by_contra h
      push_neg at h
      exact hune (funext h)
    exact mem_spectrum_of_genEigen H hcoord hnotspec hueq hCb hn₀
  obtain ⟨H₀, hH₀⟩ := h1.1 α lam 0
  have hphase : spectrum ℂ H = spectrum ℂ H₀ := h1.2.2 α lam θ 0 hα H H₀ hH hH₀
  exact ⟨H₀, hH₀, hphase ▸ hspec⟩

end Work.TMC16Core.Basic
