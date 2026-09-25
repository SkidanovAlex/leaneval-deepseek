import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Fourier

open MeasureTheory Filter MeasureTheory.Measure
open scoped ENNReal Topology BigOperators

/-- The windowed dilation operator `u ↦ (g * Ψ_u)(x)`, where `Ψ_u(y) = u⁻¹ Ψ(y/u)`. -/
private noncomputable def winOp (Ψ : SchwartzMap ℝ ℂ) (f : ℝ → ℂ) (x u : ℝ) : ℂ :=
  ∫ y : ℝ, f y * (u⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / u))

/-! ### A decay bound for the Schwartz kernel -/

private lemma schwartz_decay_two (Ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, ‖(Ψ : ℝ → ℂ) t‖ ≤ C * ((1 + |t|)⁻¹) ^ 2 := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Ψ.decay 0 0
  obtain ⟨C₂, hC₂pos, hC₂⟩ := Ψ.decay 2 0
  refine ⟨2 * C₀ + 2 * C₂, by linarith, fun t => ?_⟩
  have h1 : ‖(Ψ : ℝ → ℂ) t‖ ≤ C₀ := by
    have h := hC₀ t
    simpa using h
  have h2 : |t| ^ 2 * ‖(Ψ : ℝ → ℂ) t‖ ≤ C₂ := by
    have h := hC₂ t
    simpa [Real.norm_eq_abs, sq_abs] using h
  have hm : 0 ≤ ‖(Ψ : ℝ → ℂ) t‖ := norm_nonneg _
  have hsq : 2 * |t| ≤ |t| ^ 2 + 1 := by nlinarith [sq_nonneg (|t| - 1)]
  have h3 : 2 * |t| * ‖(Ψ : ℝ → ℂ) t‖ ≤ (|t| ^ 2 + 1) * ‖(Ψ : ℝ → ℂ) t‖ :=
    mul_le_mul_of_nonneg_right hsq hm
  have hb : (1 + |t|) ^ 2 * ‖(Ψ : ℝ → ℂ) t‖ ≤ 2 * C₀ + 2 * C₂ := by
    nlinarith [h1, h2, h3, hm, abs_nonneg t]
  have hpos : (0:ℝ) < (1 + |t|) ^ 2 := by positivity
  have hkey : ‖(Ψ : ℝ → ℂ) t‖ ≤ (2 * C₀ + 2 * C₂) * ((1 + |t|) ^ 2)⁻¹ := by
    rw [le_mul_inv_iff₀ hpos]
    rw [mul_comm]
    exact hb
  calc ‖(Ψ : ℝ → ℂ) t‖ ≤ (2 * C₀ + 2 * C₂) * ((1 + |t|) ^ 2)⁻¹ := hkey
    _ = (2 * C₀ + 2 * C₂) * ((1 + |t|)⁻¹) ^ 2 := by rw [inv_pow]

/-! ### The pointwise kernel bound at dilated scales -/

private lemma kernel_scale_bound (Ψ : SchwartzMap ℝ ℂ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (u₀ u t : ℝ), 0 < u₀ → u₀ / 2 ≤ u → u ≤ 2 * u₀ →
      ‖u⁻¹ • (Ψ : ℝ → ℂ) (t / u)‖ ≤ 8 * u₀ * C * ((u₀ + |t|)⁻¹) ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := schwartz_decay_two Ψ
  refine ⟨C, hCpos, fun u₀ u t hu₀ hu1 hu2 => ?_⟩
  have hu : 0 < u := lt_of_lt_of_le (by linarith) hu1
  have hnorm : ‖u⁻¹ • (Ψ : ℝ → ℂ) (t / u)‖ = u⁻¹ * ‖(Ψ : ℝ → ℂ) (t / u)‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hu)]
  rw [hnorm]
  have huabs : |t / u| = |t| / u := by rw [abs_div, abs_of_pos hu]
  have hinv : (1 + |t / u|)⁻¹ = u / (u + |t|) := by
    rw [huabs, show (1:ℝ) + |t| / u = (u + |t|) / u by
      rw [add_div, div_self hu.ne'], inv_div]
  have hdec := hC (t / u)
  rw [hinv] at hdec
  have hmain : u⁻¹ * (C * (u / (u + |t|)) ^ 2) = C * (u / (u + |t|) ^ 2) := by
    rw [div_pow]
    field_simp
  have hcalc : u / (u + |t|) ^ 2 ≤ 8 * u₀ * ((u₀ + |t|)⁻¹) ^ 2 := by
    have h4a : u / (u + |t|) ^ 2 ≤ 2 * u₀ / (u + |t|) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [abs_nonneg t, hu1, hu2, hu]
    have h4b : 2 * u₀ / (u + |t|) ^ 2 ≤ 2 * u₀ / (u₀ / 2 + |t|) ^ 2 := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      nlinarith [abs_nonneg t, hu1]
    have h5 : 2 * u₀ / (u₀ / 2 + |t|) ^ 2 ≤ 8 * u₀ / (u₀ + |t|) ^ 2 := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hle : u₀ + |t| ≤ 2 * (u₀ / 2 + |t|) := by linarith [abs_nonneg t]
      have h0 : (0:ℝ) ≤ u₀ + |t| := by positivity
      have hsq : (u₀ + |t|) ^ 2 ≤ (2 * (u₀ / 2 + |t|)) ^ 2 := pow_le_pow_left₀ h0 hle 2
      nlinarith [hsq, hu₀]
    have h6 : (8 * u₀ / (u₀ + |t|) ^ 2) = 8 * u₀ * ((u₀ + |t|)⁻¹) ^ 2 := by
      rw [inv_pow]; field_simp
    calc u / (u + |t|) ^ 2 ≤ 2 * u₀ / (u + |t|) ^ 2 := h4a
      _ ≤ 2 * u₀ / (u₀ / 2 + |t|) ^ 2 := h4b
      _ ≤ 8 * u₀ / (u₀ + |t|) ^ 2 := h5
      _ = 8 * u₀ * ((u₀ + |t|)⁻¹) ^ 2 := h6
  calc u⁻¹ * ‖(Ψ : ℝ → ℂ) (t / u)‖ ≤ u⁻¹ * (C * (u / (u + |t|)) ^ 2) :=
        mul_le_mul_of_nonneg_left hdec (inv_nonneg.mpr hu.le)
    _ = C * (u / (u + |t|) ^ 2) := hmain
    _ ≤ C * (8 * u₀ * ((u₀ + |t|)⁻¹) ^ 2) := mul_le_mul_of_nonneg_left hcalc hCpos.le
    _ = 8 * u₀ * C * ((u₀ + |t|)⁻¹) ^ 2 := by ring

/-- Uniform bound of the dilated kernel by a fixed `L²` profile. -/
private lemma kernel_bound' (Ψ : SchwartzMap ℝ ℂ) (u₀ : ℝ) (hu₀ : 0 < u₀) :
    ∃ C' : ℝ, 0 < C' ∧ ∀ (u t : ℝ), u₀ / 2 ≤ u → u ≤ 2 * u₀ →
      ‖u⁻¹ • (Ψ : ℝ → ℂ) (t / u)‖ ≤ C' * ((1 + |t|)⁻¹) ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ := kernel_scale_bound Ψ
  set c : ℝ := min (u₀ / 2) 1 with hc
  have hcpos : 0 < c := by rw [hc]; exact lt_min (by linarith) one_pos
  refine ⟨8 * u₀ * C / c ^ 2, by positivity, fun u t hu1 hu2 => ?_⟩
  have hbase := hC u₀ u t hu₀ hu1 hu2
  have hcl : c * (1 + |t|) ≤ u₀ + |t| := by
    have h1 : c ≤ u₀ / 2 := by rw [hc]; exact min_le_left _ _
    have h2 : c ≤ 1 := by rw [hc]; exact min_le_right _ _
    nlinarith [abs_nonneg t]
  have hclpos : 0 < c * (1 + |t|) := by positivity
  have hinv : ((u₀ + |t|)⁻¹) ^ 2 ≤ ((c * (1 + |t|))⁻¹) ^ 2 := by
    have h : (c * (1 + |t|))⁻¹ ≥ (u₀ + |t|)⁻¹ := inv_anti₀ (by positivity) hcl
    nlinarith [h, inv_nonneg.mpr hclpos.le, inv_nonneg.mpr (by positivity : (0:ℝ) ≤ u₀ + |t|)]
  calc ‖u⁻¹ • (Ψ : ℝ → ℂ) (t / u)‖ ≤ 8 * u₀ * C * ((u₀ + |t|)⁻¹) ^ 2 := hbase
    _ ≤ 8 * u₀ * C * ((c * (1 + |t|))⁻¹) ^ 2 := by
        apply mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = 8 * u₀ * C / c ^ 2 * ((1 + |t|)⁻¹) ^ 2 := by
        field_simp

/-! ### Integrability of the dominating profile -/

private lemma integrable_translate_inv_sq (x : ℝ) :
    Integrable (fun y : ℝ => (1 + (x - y) ^ 2)⁻¹) volume := by
  have h := (integrable_inv_one_add_sq).comp_sub_right x
  have heq : (fun t : ℝ => (1 + (t - x) ^ 2)⁻¹) = fun y : ℝ => (1 + (x - y) ^ 2)⁻¹ := by
    funext t; ring_nf
  rwa [heq] at h

private lemma memLp_translate_inv_sq (x : ℝ) :
    MemLp (fun y : ℝ => ((1 + |x - y|)⁻¹) ^ 2) 2 volume := by
  have hbase : MemLp (fun y : ℝ => (1 + (x - y) ^ 2)⁻¹) 2 volume := by
    rw [memLp_two_iff_integrable_sq_norm (by fun_prop :
      AEStronglyMeasurable (fun y : ℝ => (1 + (x - y) ^ 2)⁻¹) volume)]
    refine Integrable.mono' (integrable_translate_inv_sq x) (by fun_prop) ?_
    filter_upwards with y
    have hnn : (0:ℝ) ≤ (1 + (x - y) ^ 2)⁻¹ := by positivity
    have hnorm : ‖(1 + (x - y) ^ 2)⁻¹‖ = (1 + (x - y) ^ 2)⁻¹ := Real.norm_of_nonneg hnn
    rw [Real.norm_of_nonneg (show (0:ℝ) ≤ ‖(1 + (x - y) ^ 2)⁻¹‖ ^ 2 by positivity), hnorm]
    rw [sq]
    have hle1 : (1 + (x - y) ^ 2)⁻¹ ≤ 1 := by
      rw [inv_le_one₀ (by positivity)]; nlinarith [sq_nonneg (x - y)]
    nlinarith [hnn, hle1]
  refine MemLp.of_le hbase (by fun_prop) ?_
  filter_upwards with y
  have hnorm : ‖((1 + |x - y|)⁻¹) ^ 2‖ = ((1 + |x - y|)⁻¹) ^ 2 :=
    Real.norm_of_nonneg (by positivity)
  have hbase_norm : ‖(1 + (x - y) ^ 2)⁻¹‖ = (1 + (x - y) ^ 2)⁻¹ :=
    Real.norm_of_nonneg (by positivity)
  rw [hnorm, hbase_norm]
  have hle : (1 : ℝ) + (x - y) ^ 2 ≤ (1 + |x - y|) ^ 2 := by
    have h2 : |x - y| ^ 2 = (x - y) ^ 2 := sq_abs _
    nlinarith [abs_nonneg (x - y), h2]
  calc ((1 + |x - y|)⁻¹) ^ 2 = (((1 + |x - y|) ^ 2)⁻¹) := inv_pow _ _
    _ ≤ ((1 + (x - y) ^ 2)⁻¹) := inv_anti₀ (by positivity) hle

/-! ### Continuity of the windowed dilation in the scale parameter -/

private lemma continuousAt_winOp (Ψ : SchwartzMap ℝ ℂ) {g : ℝ → ℂ} (hg : MemLp g 2 volume)
    (x u₀ : ℝ) (hu₀ : 0 < u₀) :
    ContinuousAt (fun u => winOp Ψ g x u) u₀ := by
  obtain ⟨C', hC'pos, hC'⟩ := kernel_bound' Ψ u₀ hu₀
  set bound : ℝ → ℝ := fun y => ‖g y‖ * (C' * ((1 + |x - y|)⁻¹) ^ 2) with hbound
  have hmeas : ∀ᶠ u in 𝓝 u₀, AEStronglyMeasurable
      (fun y : ℝ => g y * (u⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / u))) volume :=
    Filter.Eventually.of_forall (fun u => hg.aestronglyMeasurable.mul (by fun_prop))
  have hle : ∀ᶠ u in 𝓝 u₀, ∀ᵐ y ∂volume,
      ‖g y * (u⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / u))‖ ≤ bound y := by
    filter_upwards [isOpen_Ioo.mem_nhds (show u₀ ∈ Set.Ioo (u₀/2) (2*u₀) from
      ⟨by linarith, by linarith⟩)] with u hu
    filter_upwards with y
    rw [hbound]
    rw [norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    exact hC' u (x - y) hu.1.le hu.2.le
  have hint : Integrable bound volume := by
    rw [hbound]
    have h1 : MemLp (fun y : ℝ => ‖g y‖) 2 volume := hg.norm
    have h2 : MemLp (fun y : ℝ => C' * ((1 + |x - y|)⁻¹) ^ 2) 2 volume :=
      (memLp_translate_inv_sq x).const_mul C'
    exact MemLp.integrable_mul h1 h2
  have hlim : ∀ᵐ y ∂volume, Tendsto (fun u : ℝ => g y * (u⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / u)))
      (𝓝 u₀) (𝓝 (g y * (u₀⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / u₀)))) := by
    filter_upwards with y
    have hnz : u₀ ≠ 0 := hu₀.ne'
    have h1 : ContinuousAt (fun u : ℝ => u⁻¹) u₀ := continuousAt_inv₀ hnz
    have h2 : ContinuousAt (fun u : ℝ => (Ψ : ℝ → ℂ) ((x - y) / u)) u₀ := by
      apply Ψ.continuous.continuousAt.comp
      exact continuousAt_const.div continuousAt_id hnz
    exact (h1.smul h2).const_mul (g y)
  exact tendsto_integral_filter_of_dominated_convergence bound hmeas hle hint hlim

/-! ### Measurability of the windowed dilation in the space variable -/

private lemma aestronglyMeasurable_winOp (Ψ : SchwartzMap ℝ ℂ) {g : ℝ → ℂ}
    (hg : AEStronglyMeasurable g volume) (u : ℝ) :
    AEStronglyMeasurable (fun x : ℝ => winOp Ψ g x u) volume := by
  have hjoint : AEStronglyMeasurable
      (fun p : ℝ × ℝ => g p.2 * (u⁻¹ • (Ψ : ℝ → ℂ) ((p.1 - p.2) / u)))
      (volume.prod volume) := by
    refine hg.comp_snd.mul ?_
    have hcont : Continuous (fun p : ℝ × ℝ => u⁻¹ • (Ψ : ℝ → ℂ) ((p.1 - p.2) / u)) := by
      fun_prop
    exact hcont.aestronglyMeasurable
  exact hjoint.integral_prod_right'

/-! ### Chains of scales and the associated variation -/

private abbrev Ip (J : ℕ) := Fin (J + 1) → {t : ℝ // 0 < t}

private abbrev Qp (J : ℕ) := Fin (J + 1) → {q : ℚ // 0 < q}

private noncomputable def cI {J : ℕ} (d : Qp J) : Ip J :=
  fun j => ⟨((d j : ℚ) : ℝ), by exact_mod_cast (d j).2⟩

private def Uset (J : ℕ) : Set (Ip J) := {u | StrictMono (fun j => (u j : ℝ))}

private noncomputable def chainFun (Ψ : SchwartzMap ℝ ℂ) (g : ℝ → ℂ) (s : ℝ) (J : ℕ)
    (u : Ip J) (x : ℝ) : ℝ :=
  (∑ j : Fin J,
      ‖winOp Ψ g x ((u (Fin.castSucc j)) : ℝ) - winOp Ψ g x ((u (Fin.succ j)) : ℝ)‖ ^ s)
    ^ ((1:ℝ)/s)

private noncomputable def chainVal (Ψ : SchwartzMap ℝ ℂ) (g : ℝ → ℂ) (s : ℝ) (J : ℕ)
    (u : Ip J) (x : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (chainFun Ψ g s J u x)

private lemma exists_rat_approx (J : ℕ) (u : Ip J) (n : ℕ) :
    ∃ d : Qp J, ∀ j : Fin (J + 1),
      |((d j : ℚ) : ℝ) - (u j : ℝ)| < 1 / ((n : ℝ) + 1) := by
  have hδ : (0:ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  choose q hq using fun j : Fin (J + 1) =>
    exists_rat_btwn (x := max ((u j : ℝ) - 1 / ((n : ℝ) + 1)) 0)
      (y := (u j : ℝ) + 1 / ((n : ℝ) + 1)) (by
        have hpos : (0:ℝ) < (u j : ℝ) := (u j).2
        apply max_lt <;> linarith)
  refine ⟨fun j => ⟨q j, ?_⟩, fun j => ?_⟩
  · have h1 := (hq j).1
    have h2 : (0:ℝ) < (q j : ℝ) := lt_of_le_of_lt (le_max_right _ _) h1
    exact_mod_cast h2
  · show |(q j : ℝ) - (u j : ℝ)| < 1 / ((n : ℝ) + 1)
    have h1 := (hq j).1
    have h2 := (hq j).2
    have h3 : (u j : ℝ) - 1 / ((n : ℝ) + 1) < (q j : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) h1
    rw [abs_lt]
    exact ⟨by linarith, by linarith⟩

/-! ### Reduction of the supremum over all chains to rational chains -/

private lemma iSup_eq_iSup_rat {J : ℕ} {H : Ip J → ℝ≥0∞}
    (hH : ∀ u ∈ Uset J, ContinuousAt H u) :
    (⨆ (u : Ip J) (_ : u ∈ Uset J), H u) =
      ⨆ (d : Qp J) (_ : cI d ∈ Uset J), H (cI d) := by
  apply le_antisymm
  · refine iSup_le fun u => iSup_le fun hu => ?_
    choose d hd using fun n : ℕ => exists_rat_approx J u n
    have hcoord : ∀ j : Fin (J + 1),
        Tendsto (fun n : ℕ => ((d n j : ℚ) : ℝ)) atTop (𝓝 ((u j : ℝ))) := by
      intro j
      have hε : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
        tendsto_one_div_add_atTop_nhds_zero_nat
      have hlo : Tendsto (fun n : ℕ => (u j : ℝ) - 1 / ((n : ℝ) + 1)) atTop
          (𝓝 ((u j : ℝ))) := by
        have h := hε.const_sub (u j : ℝ)
        simpa using h
      have hhi : Tendsto (fun n : ℕ => (u j : ℝ) + 1 / ((n : ℝ) + 1)) atTop
          (𝓝 ((u j : ℝ))) := by
        have h := hε.const_add (u j : ℝ)
        simpa using h
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun n => ?_) (fun n => ?_)
      · have h := hd n j; rw [abs_lt] at h; linarith [h.1]
      · have h := hd n j; rw [abs_lt] at h; linarith [h.2]
    have hci : ∀ n j, ((cI (d n)) j : ℝ) = ((d n j : ℚ) : ℝ) := fun n j => rfl
    have htend : Tendsto (fun n : ℕ => cI (d n)) atTop (𝓝 u) := by
      rw [tendsto_pi_nhds]
      intro j
      rw [tendsto_subtype_rng]
      simpa [hci] using hcoord j
    have hev : ∀ᶠ n : ℕ in atTop, cI (d n) ∈ Uset J := by
      have hpair : ∀ᶠ n : ℕ in atTop, ∀ i : Fin (J + 1), ∀ j : Fin (J + 1),
          i < j → ((cI (d n)) i : ℝ) < ((cI (d n)) j : ℝ) := by
        rw [Filter.eventually_all]
        intro i
        rw [Filter.eventually_all]
        intro j
        by_cases hij : i < j
        · filter_upwards [Filter.Tendsto.eventually_lt
            (by simpa [hci] using hcoord i) (by simpa [hci] using hcoord j) (hu hij)]
            with n hn
          exact fun _ => hn
        · exact Filter.Eventually.of_forall (fun _ hij' => absurd hij' hij)
      filter_upwards [hpair] with n hn
      exact hn
    have hlim : Tendsto (fun n : ℕ => H (cI (d n))) atTop (𝓝 (H u)) :=
      (hH u hu).tendsto.comp htend
    have ha_ev : (fun n : ℕ => ⨆ (_ : cI (d n) ∈ Uset J), H (cI (d n)))
        =ᶠ[atTop] fun n => H (cI (d n)) := by
      filter_upwards [hev] with n hn
      exact iSup_pos hn
    have ha_tend : Tendsto (fun n : ℕ => ⨆ (_ : cI (d n) ∈ Uset J), H (cI (d n)))
        atTop (𝓝 (H u)) := Filter.Tendsto.congr' ha_ev.symm hlim
    have ha_le : ∀ n, (⨆ (_ : cI (d n) ∈ Uset J), H (cI (d n)))
        ≤ ⨆ (d : Qp J) (hd : cI d ∈ Uset J), H (cI d) := by
      intro n
      by_cases hn : cI (d n) ∈ Uset J
      · rw [iSup_pos hn]
        exact le_iSup_of_le (d n) (le_iSup_of_le hn le_rfl)
      · rw [iSup_neg hn]; exact bot_le
    exact le_of_tendsto' ha_tend ha_le
  · refine iSup_le fun d => iSup_le fun hd =>
      le_iSup_of_le (cI d) (le_iSup_of_le hd le_rfl)

/-! ### Elementary facts about the chain functional -/

private lemma rpow_sum_le_single {ι : Type*} (t : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ t, 0 ≤ a i) {s : ℝ} (hs : s < 0) {j : ι} (hj : j ∈ t) (hjpos : 0 < a j) :
    (∑ i ∈ t, a i ^ s) ^ s⁻¹ ≤ a j := by
  have hsum : 0 ≤ ∑ i ∈ t, a i ^ s :=
    Finset.sum_nonneg (fun i hi => Real.rpow_nonneg (ha i hi) s)
  have hle : a j ^ s ≤ ∑ i ∈ t, a i ^ s :=
    Finset.single_le_sum (fun i hi => Real.rpow_nonneg (ha i hi) s) hj
  have hpos : 0 < a j ^ s := Real.rpow_pos_of_pos hjpos s
  calc (∑ i ∈ t, a i ^ s) ^ s⁻¹ ≤ (a j ^ s) ^ s⁻¹ :=
        Real.rpow_le_rpow_of_nonpos hpos hle (inv_nonpos.mpr hs.le)
    _ = a j := Real.rpow_rpow_inv (le_of_lt hjpos) hs.ne

private lemma chainFun_zero_exp (Ψ : SchwartzMap ℝ ℂ) (g : ℝ → ℂ) (J : ℕ) (u : Ip J)
    (x : ℝ) : chainFun Ψ g 0 J u x = 1 := by
  unfold chainFun
  simp [Real.rpow_zero]

/-! ### Continuity of the chain functional -/

private lemma continuous_winOp_coord (Ψ : SchwartzMap ℝ ℂ) {g : ℝ → ℂ}
    (hg : MemLp g 2 volume) (x : ℝ) {J : ℕ} (c : Fin (J + 1)) :
    Continuous (fun u : Ip J => winOp Ψ g x ((u c) : ℝ)) := by
  rw [continuous_iff_continuousAt]
  intro u
  have h1 : ContinuousAt (fun p : Ip J => ((p c) : ℝ)) u :=
    continuous_subtype_val.continuousAt.comp (continuous_apply c).continuousAt
  exact ContinuousAt.comp (f := fun p : Ip J => ((p c) : ℝ))
    (continuousAt_winOp Ψ hg x ((u c) : ℝ) (u c).2) h1

private lemma continuous_chainFun_of_pos (Ψ : SchwartzMap ℝ ℂ) {g : ℝ → ℂ}
    (hg : MemLp g 2 volume) {s : ℝ} (hs : 0 < s) (x : ℝ) (J : ℕ) :
    Continuous (fun u : Ip J => chainFun Ψ g s J u x) := by
  unfold chainFun
  refine (Real.continuous_rpow_const (by positivity : (0:ℝ) ≤ 1 / s)).comp ?_
  exact continuous_finsetSum _ (fun j _ =>
    (Real.continuous_rpow_const hs.le).comp
      (((continuous_winOp_coord Ψ hg x (Fin.castSucc j)).sub
        (continuous_winOp_coord Ψ hg x (Fin.succ j))).norm))

private lemma continuous_chainVal_of_pos (Ψ : SchwartzMap ℝ ℂ) {g : ℝ → ℂ}
    (hg : MemLp g 2 volume) {s : ℝ} (hs : 0 < s) (x : ℝ) (J : ℕ) :
    Continuous (fun u : Ip J => chainVal Ψ g s J u x) := by
  unfold chainVal
  exact ENNReal.continuous_ofReal.comp (continuous_chainFun_of_pos Ψ hg hs x J)

private lemma chainVal_one (Ψ : SchwartzMap ℝ ℂ) (g : ℝ → ℂ) {s : ℝ} (hs : s ≠ 0)
    (v : Ip 1) (x : ℝ) :
    chainVal Ψ g s 1 v x =
      ENNReal.ofReal ‖winOp Ψ g x ((v 0) : ℝ) - winOp Ψ g x ((v 1) : ℝ)‖ := by
  unfold chainVal chainFun
  congr 1
  rw [Fin.sum_univ_one]
  rw [show (Fin.castSucc (0 : Fin 1)) = (0 : Fin 2) from Fin.castSucc_zero,
    show (Fin.succ (0 : Fin 1)) = (1 : Fin 2) from Fin.succ_zero_eq_one]
  rw [one_div]
  exact Real.rpow_rpow_inv (norm_nonneg _) hs

private lemma continuous_chainVal_one (Ψ : SchwartzMap ℝ ℂ) {g : ℝ → ℂ}
    (hg : MemLp g 2 volume) {s : ℝ} (hs : s ≠ 0) (x : ℝ) :
    Continuous (fun v : Ip 1 => chainVal Ψ g s 1 v x) := by
  have hfun : (fun v : Ip 1 => chainVal Ψ g s 1 v x)
      = fun v : Ip 1 =>
          ENNReal.ofReal ‖winOp Ψ g x ((v 0) : ℝ) - winOp Ψ g x ((v 1) : ℝ)‖ := by
    funext v; exact chainVal_one Ψ g hs v x
  rw [hfun]
  refine ENNReal.continuous_ofReal.comp ?_
  exact ((continuous_winOp_coord Ψ hg x (0 : Fin 2)).sub
    (continuous_winOp_coord Ψ hg x (1 : Fin 2))).norm

private lemma chainVal_le_chainVal_one (Ψ : SchwartzMap ℝ ℂ) (g : ℝ → ℂ) {s : ℝ} (hs : s < 0)
    {J : ℕ} (u : Ip J) (hu : u ∈ Uset J) (x : ℝ) :
    chainVal Ψ g s J u x ≤ ⨆ (v : Ip 1) (_ : v ∈ Uset 1), chainVal Ψ g s 1 v x := by
  by_cases hex : ∃ j : Fin J,
      0 < ‖winOp Ψ g x ((u (Fin.castSucc j)) : ℝ) - winOp Ψ g x ((u (Fin.succ j)) : ℝ)‖
  · obtain ⟨j₀, hj₀⟩ := hex
    set v₀ : Ip 1 := ![u (Fin.castSucc j₀), u (Fin.succ j₀)] with hv₀def
    have hv₀ : v₀ ∈ Uset 1 := by
      show StrictMono (fun i : Fin 2 => (v₀ i : ℝ))
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [v₀]
      exact hu Fin.castSucc_lt_succ
    have hkey : chainFun Ψ g s J u x ≤
        ‖winOp Ψ g x ((u (Fin.castSucc j₀)) : ℝ) - winOp Ψ g x ((u (Fin.succ j₀)) : ℝ)‖ := by
      unfold chainFun
      rw [one_div]
      exact rpow_sum_le_single Finset.univ
        (fun j => ‖winOp Ψ g x ((u (Fin.castSucc j)) : ℝ) - winOp Ψ g x ((u (Fin.succ j)) : ℝ)‖)
        (fun j _ => norm_nonneg _) hs (Finset.mem_univ j₀) hj₀
    have hvaleq : chainVal Ψ g s 1 v₀ x =
        ENNReal.ofReal
          ‖winOp Ψ g x ((u (Fin.castSucc j₀)) : ℝ) - winOp Ψ g x ((u (Fin.succ j₀)) : ℝ)‖ := by
      rw [chainVal_one Ψ g hs.ne v₀ x, hv₀def]
      simp
    have hle : chainVal Ψ g s J u x ≤ chainVal Ψ g s 1 v₀ x := by
      rw [hvaleq]
      exact ENNReal.ofReal_le_ofReal hkey
    exact hle.trans (le_iSup_of_le v₀ (le_iSup_of_le hv₀ le_rfl))
  · simp only [not_exists, not_lt] at hex
    have hzero : chainVal Ψ g s J u x = 0 := by
      unfold chainVal chainFun
      have hsum : (∑ j : Fin J,
          ‖winOp Ψ g x ((u (Fin.castSucc j)) : ℝ) - winOp Ψ g x ((u (Fin.succ j)) : ℝ)‖ ^ s)
          = 0 := by
        apply Finset.sum_eq_zero
        intro j _
        have h0 : ‖winOp Ψ g x ((u (Fin.castSucc j)) : ℝ)
            - winOp Ψ g x ((u (Fin.succ j)) : ℝ)‖ = 0 :=
          le_antisymm (hex j) (norm_nonneg _)
        rw [h0, Real.zero_rpow hs.ne]
      rw [hsum, one_div, Real.zero_rpow (inv_ne_zero hs.ne), ENNReal.ofReal_zero]
    rw [hzero]
    exact bot_le

/-! ### The main reduction -/

private lemma aemeasurable_finset_sum {ι α M : Type*} [MeasurableSpace α] {μ : Measure α}
    [AddCommMonoid M] [MeasurableSpace M] [MeasurableAdd₂ M]
    {s : Finset ι} {f : ι → α → M} (h : ∀ i ∈ s, AEMeasurable (f i) μ) :
    AEMeasurable (fun x => ∑ i ∈ s, f i x) μ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      have hone : (fun x : α => ∑ i ∈ (∅ : Finset ι), f i x) = fun _ => 0 := by
        funext x; simp
      rw [hone]
      exact aemeasurable_const
  | insert a s ha ih =>
      have ha' : AEMeasurable (f a) μ := h a (Finset.mem_insert_self a s)
      have ih' := ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
      have hgoal : (fun x : α => ∑ i ∈ insert a s, f i x) = fun x => f a x + ∑ i ∈ s, f i x := by
        funext x; rw [Finset.sum_insert ha]
      rw [hgoal]
      exact ha'.add ih'

private lemma aemeasurable_chainVal (Ψ : SchwartzMap ℝ ℂ) {g : ℝ → ℂ}
    (hg : MemLp g 2 volume) (s : ℝ) (J : ℕ) (d : Qp J) :
    AEMeasurable (fun x : ℝ => chainVal Ψ g s J (cI d) x) volume := by
  have hwin : ∀ c : ℝ, AEMeasurable (fun x : ℝ => winOp Ψ g x c) volume :=
    fun c => (aestronglyMeasurable_winOp Ψ hg.aestronglyMeasurable c).aemeasurable
  have hrpow : Measurable (fun a : ℝ => a ^ s) := by
    have h : Measurable (fun p : ℝ × ℝ => p.1 ^ p.2) := by measurability
    exact h.comp (measurable_id.prodMk measurable_const)
  have hrpow2 : Measurable (fun a : ℝ => a ^ ((1:ℝ)/s)) := by
    have h : Measurable (fun p : ℝ × ℝ => p.1 ^ p.2) := by measurability
    exact h.comp (measurable_id.prodMk measurable_const)
  change AEMeasurable (fun x : ℝ => ENNReal.ofReal
    ((∑ j : Fin J, ‖winOp Ψ g x ((cI d (Fin.castSucc j)) : ℝ)
        - winOp Ψ g x ((cI d (Fin.succ j)) : ℝ)‖ ^ s) ^ ((1:ℝ)/s))) volume
  refine AEMeasurable.ennreal_ofReal ?_
  have hsum : AEMeasurable (fun x : ℝ => ∑ j : Fin J,
      ‖winOp Ψ g x ((cI d (Fin.castSucc j)) : ℝ)
        - winOp Ψ g x ((cI d (Fin.succ j)) : ℝ)‖ ^ s) volume :=
    aemeasurable_finset_sum (s := Finset.univ)
      (f := fun j x => ‖winOp Ψ g x ((cI d (Fin.castSucc j)) : ℝ)
        - winOp Ψ g x ((cI d (Fin.succ j)) : ℝ)‖ ^ s)
      (fun j _ => hrpow.comp_aemeasurable (((hwin _).sub (hwin _)).norm))
  exact hrpow2.comp_aemeasurable hsum

private lemma chain_iSup_eq_iSup_rat (Ψ : SchwartzMap ℝ ℂ) {g : ℝ → ℂ} (hg : MemLp g 2 volume)
    {s : ℝ} (hs : s ≠ 0) (x : ℝ) :
    (⨆ (J : ℕ) (u : Ip J), ⨆ (_ : u ∈ Uset J), chainVal Ψ g s J u x) =
      ⨆ (J : ℕ) (d : Qp J), ⨆ (_ : cI d ∈ Uset J), chainVal Ψ g s J (cI d) x := by
  apply le_antisymm
  · refine iSup_le fun J => iSup_le fun u => iSup_le fun hu => ?_
    rcases lt_or_gt_of_ne hs with hsneg | hspos
    · have h1 : (⨆ (v : Ip 1) (hv : v ∈ Uset 1), chainVal Ψ g s 1 v x)
          = ⨆ (d : Qp 1) (hd : cI d ∈ Uset 1), chainVal Ψ g s 1 (cI d) x :=
        iSup_eq_iSup_rat (fun v _ => (continuous_chainVal_one Ψ hg hs x).continuousAt)
      have h2 : (⨆ (v : Ip 1) (hv : v ∈ Uset 1), chainVal Ψ g s 1 v x)
          ≤ ⨆ (J' : ℕ) (d' : Qp J'), ⨆ (_ : cI d' ∈ Uset J'),
              chainVal Ψ g s J' (cI d') x := by
        rw [h1]; exact le_iSup_of_le 1 le_rfl
      exact (chainVal_le_chainVal_one Ψ g hsneg u hu x).trans h2
    · have h1 : (⨆ (v : Ip J) (hv : v ∈ Uset J), chainVal Ψ g s J v x)
          = ⨆ (d : Qp J) (hd : cI d ∈ Uset J), chainVal Ψ g s J (cI d) x :=
        iSup_eq_iSup_rat (fun v _ => (continuous_chainVal_of_pos Ψ hg hspos x J).continuousAt)
      have h2 : (⨆ (v : Ip J) (hv : v ∈ Uset J), chainVal Ψ g s J v x)
          ≤ ⨆ (J' : ℕ) (d' : Qp J'), ⨆ (_ : cI d' ∈ Uset J'),
              chainVal Ψ g s J' (cI d') x := by
        rw [h1]; exact le_iSup_of_le J le_rfl
      have hle_u : chainVal Ψ g s J u x
          ≤ ⨆ (v : Ip J) (hv : v ∈ Uset J), chainVal Ψ g s J v x :=
        le_iSup_of_le u (le_iSup_of_le hu le_rfl)
      exact hle_u.trans h2
  · refine iSup_le fun J => iSup_le fun d => iSup_le fun hd =>
      le_iSup_of_le J (le_iSup_of_le (cI d) (le_iSup_of_le hd le_rfl))

theorem dilation_variation_aemeasurable (Ψ : SchwartzMap ℝ ℂ) (s : ℝ) :
    ∀ g : ℝ → ℂ,
      AEMeasurable g (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      MeasureTheory.MemLp g 2 (MeasureTheory.volume : MeasureTheory.Measure ℝ) →
      AEMeasurable
        (fun x : ℝ => ⨆ (J : ℕ) (u : Fin (J + 1) → {t : ℝ // 0 < t}),
          ⨆ (_ : StrictMono (fun j => (u j : ℝ))),
            ENNReal.ofReal ((∑ j : Fin J,
              ‖(∫ y : ℝ, g y * (((u (Fin.castSucc j) : ℝ))⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / ((u (Fin.castSucc j) : ℝ)))))
               - (∫ y : ℝ, g y * (((u (Fin.succ j) : ℝ))⁻¹ • (Ψ : ℝ → ℂ) ((x - y) / ((u (Fin.succ j) : ℝ)))))‖ ^ s) ^ ((1:ℝ)/s)))
        (MeasureTheory.volume : MeasureTheory.Measure ℝ) := by
  intro g hgmeas hg
  change AEMeasurable (fun x : ℝ => ⨆ (J : ℕ) (u : Ip J), ⨆ (_ : u ∈ Uset J),
    chainVal Ψ g s J u x) volume
  have hB : ∀ t : ℝ, AEMeasurable (fun x : ℝ => ⨆ (J : ℕ) (d : Qp J),
      ⨆ (_ : cI d ∈ Uset J), chainVal Ψ g t J (cI d) x) volume := by
    intro t
    apply AEMeasurable.iSup
    intro J
    apply AEMeasurable.iSup
    intro d
    exact AEMeasurable.iSup (fun _ : cI d ∈ Uset J => aemeasurable_chainVal Ψ hg t J d)
  rcases lt_trichotomy s 0 with hsneg | hs0 | hspos
  · have hEq : (fun x : ℝ => ⨆ (J : ℕ) (u : Ip J), ⨆ (_ : u ∈ Uset J), chainVal Ψ g s J u x)
        = fun x : ℝ => ⨆ (J : ℕ) (d : Qp J), ⨆ (_ : cI d ∈ Uset J),
            chainVal Ψ g s J (cI d) x :=
      funext (fun x => chain_iSup_eq_iSup_rat Ψ hg hsneg.ne x)
    rw [hEq]
    exact hB s
  · subst hs0
    have hconst : (fun x : ℝ => ⨆ (J : ℕ) (u : Ip J), ⨆ (_ : u ∈ Uset J),
          chainVal Ψ g 0 J u x) = fun _ : ℝ => ENNReal.ofReal (1:ℝ) := by
      funext x
      apply le_antisymm
      · refine iSup_le fun J => iSup_le fun u => iSup_le fun _ => ?_
        show chainVal Ψ g 0 J u x ≤ ENNReal.ofReal (1:ℝ)
        rw [chainVal, chainFun_zero_exp]
      · have hmono : (fun _ : Fin 1 => (⟨1, one_pos⟩ : {t : ℝ // 0 < t}))
            ∈ Uset 0 := by
          show StrictMono (fun _ : Fin 1 => ((⟨1, one_pos⟩ : {t : ℝ // 0 < t}) : ℝ))
          intro a b hab
          exact absurd (Subsingleton.elim a b) (ne_of_lt hab)
        refine le_iSup_of_le 0 (le_iSup_of_le (fun _ : Fin 1 => ⟨1, one_pos⟩)
          (le_iSup_of_le hmono ?_))
        show ENNReal.ofReal (1:ℝ) ≤ chainVal Ψ g 0 0 (fun _ : Fin 1 => ⟨1, one_pos⟩) x
        rw [chainVal, chainFun_zero_exp]
    rw [hconst]
    exact aemeasurable_const
  · have hEq : (fun x : ℝ => ⨆ (J : ℕ) (u : Ip J), ⨆ (_ : u ∈ Uset J), chainVal Ψ g s J u x)
        = fun x : ℝ => ⨆ (J : ℕ) (d : Qp J), ⨆ (_ : cI d ∈ Uset J),
            chainVal Ψ g s J (cI d) x :=
      funext (fun x => chain_iSup_eq_iSup_rat Ψ hg hspos.ne' x)
    rw [hEq]
    exact hB s

end Commons.Analysis.Fourier