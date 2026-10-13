import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.RadialWAux.radGreen_eq_rescaled
import Submission.Work.FTS.PhiStar.Series.SmoothAux.Deleg.radPhi_general
import Submission.Work.FTS.PhiStar.Series.SmoothAux.Deleg.radPsi_rec
import Submission.Work.FTS.PhiStar.Honesty.CptQSmooth.radPsi_zero_bound_hasDerivAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Topology
open MeasureTheory Set Filter
open Work.FTS.PhiStar.RadialWAux (radPhi radPsi radK radP radQ radK_pos radQ_pos)
open Work.FTS.PhiStar.Radial (radGreen)
open Work.FTS.PhiStar.Series.SmoothAux.Deleg (radPhi_general radPsi_rec)

namespace Work.FTS.PhiStar.Honesty.CptQSmooth

/-- Additivity of `iteratedDeriv` for a sum, from `HasDerivAt` chains at all lower levels. -/
private lemma iteratedDeriv_add_of_chain {f g : ℝ → ℝ} :
    ∀ k : ℕ, (∀ n : ℕ, n < k → ∀ x : ℝ, 0 < x →
        HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f x) x) →
      (∀ n : ℕ, n < k → ∀ x : ℝ, 0 < x →
        HasDerivAt (iteratedDeriv n g) (iteratedDeriv (n + 1) g x) x) →
      ∀ x : ℝ, 0 < x → iteratedDeriv k (f + g) x = iteratedDeriv k f x + iteratedDeriv k g x := by
  intro k
  induction k with
  | zero => intro hf hg x hx; simp
  | succ k ih =>
      intro hf hg x hx
      have hfk : ∀ n : ℕ, n < k → ∀ y : ℝ, 0 < y →
          HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f y) y :=
        fun n hn => hf n (by omega)
      have hgk : ∀ n : ℕ, n < k → ∀ y : ℝ, 0 < y →
          HasDerivAt (iteratedDeriv n g) (iteratedDeriv (n + 1) g y) y :=
        fun n hn => hg n (by omega)
      have hev : iteratedDeriv k (f + g) =ᶠ[𝓝 x]
          fun y => iteratedDeriv k f y + iteratedDeriv k g y := by
        filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy
        exact ih hfk hgk y hy
      rw [iteratedDeriv_succ, Filter.EventuallyEq.deriv_eq hev, iteratedDeriv_succ,
        iteratedDeriv_succ]
      exact deriv_add (hf k (Nat.lt_succ_self k) x hx).differentiableAt
        (hg k (Nat.lt_succ_self k) x hx).differentiableAt

/-- The value of the `k`-th derivative of `radGreen` as `radK·(Φ^{(k)} + Ψ^{(k)})`. -/
private lemma radGreen_step {α : ℝ} (hα : 0 < α) {m : ℕ} {c : ℝ → ℝ} {N : ℕ}
    (hchainΦ : ∀ n : ℕ, n + 1 ≤ N → ∀ x : ℝ, 0 < x →
        HasDerivAt (iteratedDeriv n (radPhi α m c)) (iteratedDeriv (n + 1) (radPhi α m c) x) x)
    (hchainΨ : ∀ n : ℕ, n + 1 ≤ N → ∀ x : ℝ, 0 < x →
        HasDerivAt (iteratedDeriv n (radPsi α m c)) (iteratedDeriv (n + 1) (radPsi α m c) x) x)
    {k : ℕ} (hk : k ≤ N) {x : ℝ} (hx : 0 < x) :
    iteratedDeriv k (radGreen α m c) x
      = radK α m * (iteratedDeriv k (radPhi α m c) x + iteratedDeriv k (radPsi α m c) x) := by
  have hev : radGreen α m c =ᶠ[𝓝 x]
      fun w => radK α m * (radPhi α m c w + radPsi α m c w) := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with w hw
    exact Work.FTS.PhiStar.RadialWAux.radGreen_eq_rescaled hα m c w hw
  have hadd := iteratedDeriv_add_of_chain k (fun n hn => hchainΦ n (by omega))
    (fun n hn => hchainΨ n (by omega)) x hx
  rw [Filter.EventuallyEq.iteratedDeriv_eq k hev, iteratedDeriv_const_mul_field]
  exact congrArg (fun v => radK α m * v) hadd

/-- The `a`-th derivative of `radGreen` differentiates to the `(a+1)`-st one. -/
private lemma radGreen_conj1_of_chains {α : ℝ} (hα : 0 < α) {a : ℕ} {m : ℕ} {c : ℝ → ℝ}
    (hchainΦ : ∀ n : ℕ, n + 1 ≤ a + 1 → ∀ x : ℝ, 0 < x →
        HasDerivAt (iteratedDeriv n (radPhi α m c)) (iteratedDeriv (n + 1) (radPhi α m c) x) x)
    (hchainΨ : ∀ n : ℕ, n + 1 ≤ a + 1 → ∀ x : ℝ, 0 < x →
        HasDerivAt (iteratedDeriv n (radPsi α m c)) (iteratedDeriv (n + 1) (radPsi α m c) x) x)
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (iteratedDeriv a (radGreen α m c)) (iteratedDeriv (a + 1) (radGreen α m c) z) z := by
  have hΦ := hchainΦ a le_rfl z hz
  have hΨ := hchainΨ a le_rfl z hz
  have hmul := (hΦ.add hΨ).const_mul (radK α m)
  have h2 := radGreen_step hα hchainΦ hchainΨ (k := a + 1) le_rfl hz
  have hfin : HasDerivAt (fun w => radK α m * (iteratedDeriv a (radPhi α m c) w
      + iteratedDeriv a (radPsi α m c) w)) (iteratedDeriv (a + 1) (radGreen α m c) z) z := by
    rw [h2]
    exact hmul
  have hev : iteratedDeriv a (radGreen α m c) =ᶠ[𝓝 z]
      fun w => radK α m * (iteratedDeriv a (radPhi α m c) w
        + iteratedDeriv a (radPsi α m c) w) := by
    filter_upwards [isOpen_Ioi.mem_nhds hz] with w hw
    exact radGreen_step hα hchainΦ hchainΨ (k := a) (Nat.le_succ a) hw
  exact hfin.congr_of_eventuallyEq hev

theorem radGreen_general_bound {α : ℝ} (hα : 0 < α) (hα2 : α < 2) {a₀ b z₀ : ℝ}
    (ha₀ : 0 < a₀) (hz₀ : 0 < z₀) (a : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {c : ℝ → ℝ} {K : ℝ}, 0 ≤ K →
      ContDiffOn ℝ (↑(a + 1)) c (Set.Ioi 0) → Work.FTS.PhiStar.BddDeriv (a + 1) c K →
      (∀ t : ℝ, t ∉ Set.Icc a₀ b → c t = 0) →
      (∀ m : ℕ, ∀ z : ℝ, 0 < z →
        HasDerivAt (fun z' => iteratedDeriv a (fun z'' => Work.FTS.PhiStar.Radial.radGreen α m c z'') z')
          (iteratedDeriv (a + 1) (fun z'' => Work.FTS.PhiStar.Radial.radGreen α m c z'') z) z)
      ∧ (∀ m : ℕ, ∀ z : ℝ, z₀ ≤ z →
        |iteratedDeriv a (fun z'' => Work.FTS.PhiStar.Radial.radGreen α m c z'') z|
          ≤ C * ((m : ℝ) + 1) ^ a * K) := by
  obtain ⟨C₂, hC₂0, hC₂⟩ :=
    radPsi_zero_bound_hasDerivAt (α := α) (a := a) (a₀ := a₀) (b := b) (z₀ := z₀) ha₀ hz₀
  set C₁ : ℝ := max 1 (2 / (α * z₀) + ((a : ℝ) + 2) / z₀) with hC₁
  have hC₁1 : 1 ≤ C₁ := by rw [hC₁]; exact le_max_left _ _
  have hC₁nn : 0 ≤ C₁ := le_trans zero_le_one hC₁1
  have hC₁pow : 0 ≤ C₁ ^ a := pow_nonneg hC₁nn a
  set Cv : ℝ := 1 / (4 * α) * (1 + C₂ + 2 * C₁ ^ a) + 1 with hCv
  have hCv0 : 0 ≤ Cv := by
    rw [hCv]
    have h1 : 0 ≤ 1 / (4 * α) := by positivity
    have h2 : 0 ≤ 1 + C₂ + 2 * C₁ ^ a := by linarith
    exact add_nonneg (mul_nonneg h1 h2) zero_le_one
  have hle1 : ∀ m : ℕ, (1 : ℝ) ≤ (a : ℝ) + radQ α m := by
    intro m
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have hq : 1 < radQ α m := by
      simp only [radQ, Work.FTS.PhiStar.RadialWAux.radQ]
      rw [lt_div_iff₀ hα]
      nlinarith [hα2, hm0]
    have ha0 : (0 : ℝ) ≤ (a : ℝ) := Nat.cast_nonneg a
    linarith
  have hradK_le : ∀ m : ℕ, radK α m ≤ 1 / (4 * α) := by
    intro m
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    simp only [radK, Work.FTS.PhiStar.RadialWAux.radK]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hα, hm0]
  refine ⟨Cv, hCv0, ?_⟩
  intro c K hK hc hb hsupp
  have key : ∀ m : ℕ,
      (∀ z : ℝ, 0 < z → HasDerivAt (iteratedDeriv a (radGreen α m c))
        (iteratedDeriv (a + 1) (radGreen α m c) z) z)
      ∧ (∀ z : ℝ, z₀ ≤ z → |iteratedDeriv a (radGreen α m c) z|
        ≤ Cv * ((m : ℝ) + 1) ^ a * K) := by
    intro m
    have hPhil := radPhi_general (α := α) (m := m) (N := a + 1) (c := c) (K := K)
      hα hK hc hb
    have hchainΦ : ∀ n : ℕ, n + 1 ≤ a + 1 → ∀ x : ℝ, 0 < x →
        HasDerivAt (iteratedDeriv n (radPhi α m c)) (iteratedDeriv (n + 1) (radPhi α m c) x) x := by
      intro n hn x hx
      have h1 := (hPhil n (by omega) x hx).2.2 hn
      have h3 : iteratedDeriv (n + 1) (radPhi α m c) x
          = ∫ u in (0 : ℝ)..1, iteratedDeriv (n + 1) c (x * u)
              * u ^ ((n : ℝ) + 1 + radQ α m - 1) := by
        rw [(hPhil (n + 1) (by omega) x hx).1]
        apply intervalIntegral.integral_congr
        intro u _
        rw [show (((n + 1 : ℕ) : ℝ) + radQ α m - 1) = ((n : ℝ) + 1 + radQ α m - 1) from by
          push_cast; ring]
      rwa [h3]
    have hPhiK : ∀ x : ℝ, 0 < x → |iteratedDeriv a (radPhi α m c) x| ≤ K := by
      intro x hx
      refine le_trans (hPhil a (by omega) x hx).2.1 ?_
      rw [div_le_iff₀ (by have := radQ_pos hα m; positivity)]
      nlinarith [hK, hle1 m]
    rcases eq_or_ne m 0 with hm | hm
    · have hΨfun : radPsi α m c = radPsi α 0 c := by rw [hm]
      have h0 := hC₂ (c := c) (K := K) hK hc hb hsupp
      have hchainΨ : ∀ n : ℕ, n + 1 ≤ a + 1 → ∀ x : ℝ, 0 < x →
          HasDerivAt (iteratedDeriv n (radPsi α m c)) (iteratedDeriv (n + 1) (radPsi α m c) x) x := by
        intro n hn x hx
        rw [hΨfun]
        exact h0.2 n hn x hx
      have hPsi_bd : ∀ z : ℝ, z₀ ≤ z → |iteratedDeriv a (radPsi α m c) z| ≤ C₂ * K := by
        intro z hz
        rw [hΨfun]
        exact h0.1 a le_rfl z hz
      refine ⟨fun z hz => radGreen_conj1_of_chains hα hchainΦ hchainΨ hz, fun z hz => ?_⟩
      have hzpos : 0 < z := lt_of_lt_of_le hz₀ hz
      have hstep := radGreen_step hα hchainΦ hchainΨ (k := a) (Nat.le_succ a) hzpos
      have hb1 : |iteratedDeriv a (radPhi α m c) z + iteratedDeriv a (radPsi α m c) z|
          ≤ K + C₂ * K :=
        (abs_add_le _ _).trans (add_le_add (hPhiK z hzpos) (hPsi_bd z hz))
      have hA : |iteratedDeriv a (radGreen α m c) z| ≤ 1 / (4 * α) * (1 + C₂) * K := by
        calc |iteratedDeriv a (radGreen α m c) z|
            = radK α m * |iteratedDeriv a (radPhi α m c) z
                + iteratedDeriv a (radPsi α m c) z| := by
                rw [hstep, abs_mul, abs_of_pos (radK_pos hα m)]
          _ ≤ 1 / (4 * α) * (K + C₂ * K) :=
                mul_le_mul (hradK_le m) hb1 (abs_nonneg _) (by positivity)
          _ = 1 / (4 * α) * (1 + C₂) * K := by ring
      have hB : 1 / (4 * α) * (1 + C₂) * K ≤ Cv * K := by
        refine mul_le_mul_of_nonneg_right ?_ hK
        have h4 : 1 + C₂ ≤ 1 + C₂ + 2 * C₁ ^ a := by linarith
        have h5 : 1 / (4 * α) * (1 + C₂) ≤ 1 / (4 * α) * (1 + C₂ + 2 * C₁ ^ a) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
        rw [hCv]
        linarith
      have hCe : Cv * K ≤ Cv * ((m : ℝ) + 1) ^ a * K := by
        have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        have hpow : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ a :=
          one_le_pow₀ (by linarith)
        calc Cv * K = Cv * 1 * K := by ring
          _ ≤ Cv * ((m : ℝ) + 1) ^ a * K :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hCv0) hK
      exact le_trans hA (le_trans hB hCe)
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
      have hmr1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
      have hp1 : 1 < radP α m := by
        simp only [radP, Work.FTS.PhiStar.RadialWAux.radP]
        rw [lt_div_iff₀ hα]
        nlinarith [hmr1, hα2]
      set M : ℝ := max 1 ((radP α m + ((a + 1 : ℕ) : ℝ) + 1) / z₀) with hM
      have hM1 : 1 ≤ M := by rw [hM]; exact le_max_left _ _
      have hMz : (radP α m + ((a + 1 : ℕ) : ℝ) + 1) / z₀ ≤ M := by
        rw [hM]; exact le_max_right _ _
      have hPe := radPsi_rec (α := α) (m := m) (N := a + 1) (c := c) (K := K) (M := M)
        (z₀ := z₀) hα hK hc hb hp1 hz₀ hM1 hMz
      have hchainΨ : ∀ n : ℕ, n + 1 ≤ a + 1 → ∀ x : ℝ, 0 < x →
          HasDerivAt (iteratedDeriv n (radPsi α m c)) (iteratedDeriv (n + 1) (radPsi α m c) x) x :=
        fun n hn x hx => hPe.2 n hn x hx
      have hPsi_bd : ∀ z : ℝ, z₀ ≤ z → |iteratedDeriv a (radPsi α m c) z| ≤ 2 * M ^ a * K :=
        fun z hz => hPe.1 a (Nat.le_succ a) z hz
      refine ⟨fun z hz => radGreen_conj1_of_chains hα hchainΦ hchainΨ hz, fun z hz => ?_⟩
      have hzpos : 0 < z := lt_of_lt_of_le hz₀ hz
      have hstep := radGreen_step hα hchainΦ hchainΨ (k := a) (Nat.le_succ a) hzpos
      have hb1 : |iteratedDeriv a (radPhi α m c) z + iteratedDeriv a (radPsi α m c) z|
          ≤ K + 2 * M ^ a * K :=
        (abs_add_le _ _).trans (add_le_add (hPhiK z hzpos) (hPsi_bd z hz))
      have hMle : M ≤ C₁ * ((m : ℝ) + 1) := by
        have hcast : (((a + 1 : ℕ) : ℝ)) = (a : ℝ) + 1 := by push_cast; ring
        refine max_le ?_ ?_
        · nlinarith [hC₁1, hmr1]
        · rw [div_le_iff₀ hz₀, hcast]
          have hT : 2 / (α * z₀) + ((a : ℝ) + 2) / z₀ ≤ C₁ := by
            rw [hC₁]; exact le_max_right _ _
          have hkey : radP α m + ((a : ℝ) + 1) + 1
              ≤ (2 / (α * z₀) + ((a : ℝ) + 2) / z₀) * (z₀ * ((m : ℝ) + 1)) := by
            rw [show (2 / (α * z₀) + ((a : ℝ) + 2) / z₀) * (z₀ * ((m : ℝ) + 1))
                = (2 / α) * ((m : ℝ) + 1) + ((a : ℝ) + 2) * ((m : ℝ) + 1) from by
              field_simp]
            have h1 : radP α m ≤ (2 / α) * ((m : ℝ) + 1) := by
              rw [show radP α m = (2 / α) * (m : ℝ) from by
                simp only [radP, Work.FTS.PhiStar.RadialWAux.radP]; ring]
              exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
            have h2 : (a : ℝ) + 2 ≤ ((a : ℝ) + 2) * ((m : ℝ) + 1) :=
              le_mul_of_one_le_right (by positivity) (by linarith)
            linarith
          calc radP α m + ((a : ℝ) + 1) + 1
              ≤ (2 / (α * z₀) + ((a : ℝ) + 2) / z₀) * (z₀ * ((m : ℝ) + 1)) := hkey
            _ ≤ C₁ * (z₀ * ((m : ℝ) + 1)) := mul_le_mul_of_nonneg_right hT (by positivity)
            _ = C₁ * ((m : ℝ) + 1) * z₀ := by ring
      have hMpow : M ^ a ≤ C₁ ^ a * ((m : ℝ) + 1) ^ a := by
        calc M ^ a ≤ (C₁ * ((m : ℝ) + 1)) ^ a :=
              pow_le_pow_left₀ (by positivity) hMle a
          _ = C₁ ^ a * ((m : ℝ) + 1) ^ a := by rw [mul_pow]
      have hstep1 : K + 2 * M ^ a * K ≤ (1 + 2 * C₁ ^ a) * ((m : ℝ) + 1) ^ a * K := by
        have h3 : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ a := one_le_pow₀ (by linarith)
        have h5 : 2 * M ^ a ≤ 2 * C₁ ^ a * ((m : ℝ) + 1) ^ a := by linarith
        have h4 : (1 : ℝ) + 2 * M ^ a ≤ (1 + 2 * C₁ ^ a) * ((m : ℝ) + 1) ^ a :=
          calc (1 : ℝ) + 2 * M ^ a ≤ ((m : ℝ) + 1) ^ a + 2 * C₁ ^ a * ((m : ℝ) + 1) ^ a :=
                add_le_add h3 h5
            _ = (1 + 2 * C₁ ^ a) * ((m : ℝ) + 1) ^ a := by ring
        calc K + 2 * M ^ a * K = K * (1 + 2 * M ^ a) := by ring
          _ ≤ K * ((1 + 2 * C₁ ^ a) * ((m : ℝ) + 1) ^ a) := mul_le_mul_of_nonneg_left h4 hK
          _ = (1 + 2 * C₁ ^ a) * ((m : ℝ) + 1) ^ a * K := by ring
      have hsum0 : (0 : ℝ) ≤ K + 2 * M ^ a * K := by
        have h : (0 : ℝ) ≤ M ^ a := pow_nonneg (le_trans zero_le_one hM1) a
        nlinarith [hK, h]
      calc |iteratedDeriv a (radGreen α m c) z|
          = radK α m * |iteratedDeriv a (radPhi α m c) z
              + iteratedDeriv a (radPsi α m c) z| := by
              rw [hstep, abs_mul, abs_of_pos (radK_pos hα m)]
        _ ≤ 1 / (4 * α) * (K + 2 * M ^ a * K) :=
              mul_le_mul (hradK_le m) hb1 (abs_nonneg _) (by positivity)
        _ ≤ 1 / (4 * α) * ((1 + 2 * C₁ ^ a) * ((m : ℝ) + 1) ^ a * K) :=
              mul_le_mul_of_nonneg_left hstep1 (by positivity)
        _ = 1 / (4 * α) * (1 + 2 * C₁ ^ a) * ((m : ℝ) + 1) ^ a * K := by ring
        _ ≤ Cv * ((m : ℝ) + 1) ^ a * K := by
              have hP : (0 : ℝ) ≤ ((m : ℝ) + 1) ^ a := by positivity
              have h4 : 1 + 2 * C₁ ^ a ≤ 1 + C₂ + 2 * C₁ ^ a := by linarith [hC₂0]
              have h5 : 1 / (4 * α) * (1 + 2 * C₁ ^ a)
                  ≤ 1 / (4 * α) * (1 + C₂ + 2 * C₁ ^ a) :=
                mul_le_mul_of_nonneg_left h4 (by positivity)
              have h8 := mul_le_mul_of_nonneg_right h5 hP
              rw [hCv]
              refine mul_le_mul_of_nonneg_right ?_ hK
              nlinarith [h8, hP]
  exact ⟨fun m z hz => (key m).1 z hz, fun m z hz => (key m).2 z hz⟩

end Work.FTS.PhiStar.Honesty.CptQSmooth
