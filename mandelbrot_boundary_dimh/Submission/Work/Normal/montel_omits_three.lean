import Mathlib
import Submission.Work.Normal.Basic
import Submission.Work.Normal.montel_locallyBounded
import Submission.Work.Normal.schottky_two_omitted
import Submission.Work.Normal.hurwitz_nonvanishing
import Submission.Work.Normal.isNormalFamily_of_locally

namespace Work.Normal

open Set Filter Topology Function
open scoped Topology BigOperators

theorem exists_bdd_subseq_or_tendsto_atTop_norm (w : ℕ → ℂ) :
    (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ M : ℝ, ∀ k : ℕ, ‖w (φ k)‖ ≤ M) ∨
      (∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ R : ℝ, ∃ N : ℕ, ∀ k ≥ N, R ≤ ‖w (φ k)‖) := by
  by_cases h : ∃ M : ℝ, ∀ n : ℕ, ‖w n‖ ≤ M
  · exact Or.inl ⟨id, strictMono_id, h⟩
  · push_neg at h
    have hbig : ∀ n k : ℕ, ∃ m : ℕ, k < m ∧ (n : ℝ) ≤ ‖w m‖ := by
      intro n k
      obtain ⟨m, hm⟩ := h (max (n : ℝ) (∑ i ∈ Finset.range (k + 1), ‖w i‖))
      refine ⟨m, ?_, le_trans (le_max_left _ _) (le_of_lt hm)⟩
      by_contra hle
      push_neg at hle
      have hmem : m ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hle)
      have hsum : ‖w m‖ ≤ ∑ i ∈ Finset.range (k + 1), ‖w i‖ :=
        Finset.single_le_sum (fun i _ => norm_nonneg _) hmem
      have h2 : ‖w m‖ ≤ max (n : ℝ) (∑ i ∈ Finset.range (k + 1), ‖w i‖) :=
        le_trans hsum (le_max_right _ _)
      linarith
    let φ : ℕ → ℕ := fun k => Nat.rec 0 (fun k prev => Classical.choose (hbig (k + 1) prev)) k
    have hstep : ∀ k : ℕ, φ k < φ (k + 1) := by
      intro k
      exact (Classical.choose_spec (hbig (k + 1) (φ k))).1
    have hmono : StrictMono φ := strictMono_nat_of_lt_succ hstep
    have hbound : ∀ k : ℕ, (k : ℝ) ≤ ‖w (φ k)‖ := by
      intro k
      cases k with
      | zero => simp
      | succ k => exact (Classical.choose_spec (hbig (k + 1) (φ k))).2
    refine Or.inr ⟨φ, hmono, fun R => ⟨Nat.ceil R, fun k hk => ?_⟩⟩
    have h1 : R ≤ (k : ℝ) := le_trans (Nat.le_ceil R) (by exact_mod_cast hk)
    exact le_trans h1 (hbound k)

theorem tendstoLocallyUniformlyOn_const_mul_add {v : ℕ → ℂ → ℂ} {G : ℂ → ℂ} {U : Set ℂ} (b a : ℂ)
    (h : TendstoLocallyUniformlyOn v G atTop U) :
    TendstoLocallyUniformlyOn (fun n z => a + b * v n z) (fun z => a + b * G z) atTop U := by
  have hg : UniformContinuous fun w : ℂ => a + b * w := by fun_prop
  simpa [Function.comp_def] using hg.comp_tendstoLocallyUniformlyOn h

theorem tendstoLocallyUniformlyAtTop_congr {v w : ℕ → ℂ → ℂ} {U : Set ℂ}
    (h : TendstoLocallyUniformlyAtTop v U) (hvw : ∀ n z, z ∈ U → v n z = w n z) :
    TendstoLocallyUniformlyAtTop w U := by
  intro K hKU hK R
  obtain ⟨N, hN⟩ := h K hKU hK R
  exact ⟨N, fun n hn z hz => by rw [← hvw n z (hKU hz)]; exact hN n hn z hz⟩

theorem tendstoLocallyUniformlyAtTop_const_mul_add {v : ℕ → ℂ → ℂ} {U : Set ℂ} (b a : ℂ)
    (hb : b ≠ 0) (h : TendstoLocallyUniformlyAtTop v U) :
    TendstoLocallyUniformlyAtTop (fun n z => a + b * v n z) U := by
  intro K hKU hK R
  have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hb
  obtain ⟨N, hN⟩ := h K hKU hK ((R + ‖a‖) / ‖b‖)
  refine ⟨N, fun n hn z hz => ?_⟩
  have h1 : (R + ‖a‖) / ‖b‖ ≤ ‖v n z‖ := hN n hn z hz
  have h2 : R + ‖a‖ ≤ ‖b‖ * ‖v n z‖ := by
    have h3 := mul_le_mul_of_nonneg_left h1 hbpos.le
    rwa [mul_div_cancel₀ _ (ne_of_gt hbpos)] at h3
  have h4 : ‖b * v n z‖ - ‖a‖ ≤ ‖a + b * v n z‖ := by
    have h5 := norm_sub_le (a + b * v n z) a
    have h6 : a + b * v n z - a = b * v n z := by ring
    rw [h6] at h5
    linarith
  rw [norm_mul] at h4
  linarith

theorem tendstoLocallyUniformlyOn_inv {v : ℕ → ℂ → ℂ} {G : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (h : TendstoLocallyUniformlyOn v G atTop U) (hG : ∀ z ∈ U, G z ≠ 0)
    (hGc : ContinuousOn G U) (hv : ∀ n z, z ∈ U → v n z ≠ 0) :
    TendstoLocallyUniformlyOn (fun n z => (v n z)⁻¹) (fun z => (G z)⁻¹) atTop U := by
  have hmain : ∀ K, K ⊆ U → IsCompact K →
      TendstoUniformlyOn (fun n z => (v n z)⁻¹) (fun z => (G z)⁻¹) atTop K := by
    intro K hKU hK
    have h' := (tendstoLocallyUniformlyOn_iff_forall_isCompact (s := U) hU).mp h K hKU hK
    rw [Metric.tendstoUniformlyOn_iff] at h' ⊢
    intro ε hε
    rcases K.eq_empty_or_nonempty with rfl | hne
    · filter_upwards with n
      simp
    · obtain ⟨z₁, hz₁K, hmin⟩ := hK.exists_isMinOn hne (hGc.norm.mono hKU)
      have hz₁U : z₁ ∈ U := hKU hz₁K
      have hδ : 0 < ‖G z₁‖ := norm_pos_iff.mpr (hG z₁ hz₁U)
      have hδ2 : 0 < ‖G z₁‖ / 2 := by linarith
      filter_upwards [h' (min (‖G z₁‖ / 2) (ε * (‖G z₁‖ / 2 * ‖G z₁‖)))
        (lt_min hδ2 (by positivity))] with n hn
      intro z hz
      have hzU : z ∈ U := hKU hz
      have h1 : dist (G z) (v n z) < min (‖G z₁‖ / 2) (ε * (‖G z₁‖ / 2 * ‖G z₁‖)) := hn z hz
      rw [dist_eq_norm] at h1
      have hGz : 0 < ‖G z‖ := norm_pos_iff.mpr (hG z hzU)
      have hmin' : ‖G z₁‖ ≤ ‖G z‖ := hmin hz
      have hvz : v n z ≠ 0 := hv n z hzU
      have hvn : ‖G z₁‖ / 2 ≤ ‖v n z‖ := by
        have h5 : ‖G z‖ - ‖v n z‖ ≤ ‖G z - v n z‖ :=
          le_trans (le_abs_self _) (abs_norm_sub_norm_le (G z) (v n z))
        have h4 : ‖G z - v n z‖ < ‖G z₁‖ / 2 := lt_of_lt_of_le h1 (min_le_left _ _)
        linarith
      have hbdd : ‖G z - v n z‖ < ε * (‖G z₁‖ / 2 * ‖G z₁‖) := lt_of_lt_of_le h1 (min_le_right _ _)
      rw [dist_eq_norm, inv_sub_inv (hG z hzU) hvz, norm_div, norm_mul, norm_sub_rev (v n z) (G z)]
      have hden : ‖G z₁‖ / 2 * ‖G z₁‖ ≤ ‖v n z‖ * ‖G z‖ := by
        have hA : ‖G z₁‖ / 2 * ‖G z₁‖ ≤ ‖G z₁‖ / 2 * ‖G z‖ :=
          mul_le_mul_of_nonneg_left hmin' hδ2.le
        have hB : ‖G z₁‖ / 2 * ‖G z‖ ≤ ‖v n z‖ * ‖G z‖ :=
          mul_le_mul_of_nonneg_right hvn (norm_nonneg (G z))
        linarith
      have hlt : ‖G z - v n z‖ < ε * (‖v n z‖ * ‖G z‖) :=
        lt_of_lt_of_le hbdd (mul_le_mul_of_nonneg_left hden hε.le)
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < ‖G z‖ * ‖v n z‖)]
      calc ‖G z - v n z‖ < ε * (‖v n z‖ * ‖G z‖) := hlt
        _ = ε * (‖G z‖ * ‖v n z‖) := by ring
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact (s := U) hU).mpr hmain

theorem tendstoLocallyUniformlyAtTop_inv_of_tendsto_zero {v : ℕ → ℂ → ℂ} {G : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (h : TendstoLocallyUniformlyOn v G atTop U) (hG0 : ∀ z ∈ U, G z = 0)
    (hv : ∀ n z, z ∈ U → v n z ≠ 0) :
    TendstoLocallyUniformlyAtTop (fun n z => (v n z)⁻¹) U := by
  intro K hKU hK R
  have h' := (tendstoLocallyUniformlyOn_iff_forall_isCompact (s := U) hU).mp h K hKU hK
  rw [Metric.tendstoUniformlyOn_iff] at h'
  have hR : 0 < max R 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h' (max R 1)⁻¹ (inv_pos.mpr hR))
  refine ⟨N, fun n hn z hz => ?_⟩
  have h1 : ‖v n z‖ < (max R 1)⁻¹ := by
    have h2 := hN n hn z hz
    rw [hG0 z (hKU hz), dist_eq_norm, zero_sub, norm_neg] at h2
    exact h2
  have hpos : 0 < ‖v n z‖ := norm_pos_iff.mpr (hv n z (hKU hz))
  rw [norm_inv]
  have h3 := (inv_le_inv₀ (inv_pos.mpr hR) hpos).mpr (le_of_lt h1)
  rw [inv_inv] at h3
  exact le_trans (le_max_left _ _) h3

theorem tendstoLocallyUniformlyOn_inv_of_tendstoLocallyUniformlyAtTop {v : ℕ → ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (h : TendstoLocallyUniformlyAtTop v U) :
    TendstoLocallyUniformlyOn (fun n z => (v n z)⁻¹) (fun _ => 0) atTop U := by
  have hmain : ∀ K, K ⊆ U → IsCompact K →
      TendstoUniformlyOn (fun n z => (v n z)⁻¹) (fun _ => 0) atTop K := by
    intro K hKU hK
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := h K hKU hK (2 / ε)
    refine eventually_atTop.mpr ⟨N, fun n hn z hz => ?_⟩
    have h1 : 2 / ε ≤ ‖v n z‖ := hN n hn z hz
    have hpos : 0 < ‖v n z‖ := lt_of_lt_of_le (by positivity) h1
    have h2 : ‖v n z‖⁻¹ ≤ ε / 2 := by
      have h3 : ‖v n z‖⁻¹ ≤ (2 / ε)⁻¹ := (inv_le_inv₀ hpos (by positivity)).mpr h1
      rwa [inv_div] at h3
    rw [dist_zero_left, norm_inv]
    linarith
  exact (tendstoLocallyUniformlyOn_iff_forall_isCompact (s := U) hU).mpr hmain

theorem schottky_ball {c : ℂ} {R M r : ℝ} (hR : 0 < R) (hr : r < R) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ f : ℂ → ℂ, DifferentiableOn ℂ f (Metric.ball c R) →
      (∀ z ∈ Metric.ball c R, f z ≠ 0 ∧ f z ≠ 1) → ‖f c‖ ≤ M →
      ∀ z : ℂ, ‖z - c‖ ≤ r → ‖f z‖ ≤ B := by
  by_cases hM : M ≤ 0
  · refine ⟨0, le_rfl, fun f hf homit hfc z hz => ?_⟩
    have hc : ‖f c‖ = 0 := le_antisymm (le_trans hfc hM) (norm_nonneg _)
    exact absurd (norm_eq_zero.mp hc) (homit c (Metric.mem_ball_self hR)).1
  · push_neg at hM
    obtain ⟨B, hB0, hB⟩ :=
      schottky_two_omitted (r := r / R) (M := M) ((div_lt_one hR).mpr hr) hM.le
    refine ⟨max B M, le_trans hB0 (le_max_left _ _), fun f hf homit hfc z hz => ?_⟩
    let F : ℂ → ℂ := fun ζ => f (c + R * ζ)
    have hRc : ‖(R : ℂ)‖ = R := by
      rw [Complex.norm_def, Complex.normSq_ofReal]
      exact Real.sqrt_mul_self (le_of_lt hR)
    have hmemR : ∀ ζ : ℂ, ‖ζ‖ < 1 → c + R * ζ ∈ Metric.ball c R := by
      intro ζ hζ
      rw [Metric.mem_ball, dist_eq_norm]
      have he : c + R * ζ - c = (R : ℂ) * ζ := by ring
      rw [he, norm_mul, hRc]
      calc R * ‖ζ‖ < R * 1 := mul_lt_mul_of_pos_left hζ hR
        _ = R := by ring
    have hFhol : DifferentiableOn ℂ F (Metric.ball 0 1) := by
      have hlin : DifferentiableOn ℂ (fun ζ : ℂ => c + R * ζ) Set.univ :=
        ((by fun_prop : Differentiable ℂ fun ζ : ℂ => c + R * ζ)).differentiableOn
      refine hf.comp (hlin.mono (subset_univ _)) ?_
      intro ζ hζ
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hζ
      exact hmemR ζ hζ
    have hFomit : ∀ ζ ∈ Metric.ball 0 1, F ζ ≠ 0 ∧ F ζ ≠ 1 := by
      intro ζ hζ
      rw [Metric.mem_ball, dist_eq_norm, sub_zero] at hζ
      exact homit _ (hmemR ζ hζ)
    have hb := hB F hFhol hFomit (by show ‖f (c + R * 0)‖ ≤ M; simpa using hfc)
    have hz1 : ‖(z - c) / R‖ ≤ r / R := by
      rw [norm_div, hRc]
      exact div_le_div_of_nonneg_right hz hR.le
    have hRne : (R : ℂ) ≠ 0 := fun h => absurd (by simpa using congrArg Complex.re h : R = 0)
      (ne_of_gt hR)
    have he : c + R * ((z - c) / R) = z := by
      field_simp
      ring
    have hval : F ((z - c) / R) = f z := by
      show f (c + R * ((z - c) / R)) = f z
      rw [he]
    have hfin := hb ((z - c) / R) hz1
    rw [hval] at hfin
    exact le_trans hfin (le_max_left _ _)

theorem isLocallyBoundedOn_range_of_forall_le {v : ℕ → ℂ → ℂ} {V : Set ℂ} {B : ℝ}
    (h : ∀ n z, z ∈ V → ‖v n z‖ ≤ B) : IsLocallyBoundedOn (Set.range v) V :=
  fun K hKV hK => ⟨max B 0, fun f hf z hz => by
    obtain ⟨n, rfl⟩ := hf
    exact le_trans (h n z (hKV hz)) (le_max_left _ _)⟩


/-! ### The main assembly -/

theorem montel_two_omitted {Fam : Set (ℂ → ℂ)} {U : Set ℂ} {a b : ℂ} (hab : a ≠ b)
    (hU : IsOpen U) (hUc : IsPreconnected U)
    (hhol : ∀ f ∈ Fam, DifferentiableOn ℂ f U)
    (homit : ∀ f ∈ Fam, ∀ z ∈ U, f z ≠ a ∧ f z ≠ b) :
    IsNormalFamily Fam U := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
  refine isNormalFamily_of_locally hU hUc ?_
  intro z₀ hz₀
  obtain ⟨R, hR, hRU⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds hz₀)
  refine ⟨Metric.ball z₀ (R / 2), Metric.mem_ball_self (by linarith), Metric.isOpen_ball, ?_⟩
  intro u hu
  set V : Set ℂ := Metric.ball z₀ (R / 2) with hV
  have hVopen : IsOpen V := by rw [hV]; exact Metric.isOpen_ball
  have hVU : V ⊆ U := by
    intro z hz
    refine hRU ?_
    rw [hV] at hz
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    linarith
  have hVR : V ⊆ Metric.ball z₀ R := by
    intro z hz
    rw [hV] at hz
    rw [Metric.mem_ball, dist_eq_norm] at hz ⊢
    linarith
  set v : ℕ → ℂ → ℂ := fun n z => (u n z - a) / (b - a) with hv_def
  have hvhol : ∀ n, DifferentiableOn ℂ (v n) (Metric.ball z₀ R) := by
    intro n
    have hu' : DifferentiableOn ℂ (u n) (Metric.ball z₀ R) := (hhol (u n) (hu n)).mono hRU
    have h2 : DifferentiableOn ℂ (fun z => (u n z - a) / (b - a)) (Metric.ball z₀ R) :=
      (hu'.sub_const a).div_const (b - a)
    simpa only [hv_def] using h2
  have hvomit : ∀ n z, z ∈ Metric.ball z₀ R → v n z ≠ 0 ∧ v n z ≠ 1 := by
    intro n z hz
    have hzU : z ∈ U := hRU hz
    have h0 : u n z ≠ a := (homit (u n) (hu n) z hzU).1
    have h1 : u n z ≠ b := (homit (u n) (hu n) z hzU).2
    constructor
    · intro hcon
      rw [hv_def, div_eq_zero_iff] at hcon
      rcases hcon with h | h
      · exact h0 (sub_eq_zero.mp h)
      · exact hba h
    · intro hcon
      rw [hv_def, div_eq_one_iff_eq hba] at hcon
      exact h1 (by linear_combination hcon)
  have hid : ∀ n z, a + (b - a) * v n z = u n z := by
    intro n z
    rw [hv_def]
    field_simp
    ring
  obtain hbdd | hbig := exists_bdd_subseq_or_tendsto_atTop_norm (fun n => v n z₀)
  · obtain ⟨φ, hφ, M, hM⟩ := hbdd
    obtain ⟨B, hB0, hB⟩ := schottky_ball (c := z₀) (R := R) (M := M) (r := R / 2) hR (by linarith)
    have hbnd : ∀ k z, z ∈ V → ‖v (φ k) z‖ ≤ B := by
      intro k z hz
      refine hB (v (φ k)) (hvhol (φ k)) (hvomit (φ k)) (hM k) z ?_
      rw [hV] at hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      exact le_of_lt hz
    have hlb : IsLocallyBoundedOn (Set.range fun k => v (φ k)) V :=
      isLocallyBoundedOn_range_of_forall_le hbnd
    have hhol' : ∀ f ∈ Set.range (fun k => v (φ k)), DifferentiableOn ℂ f V := by
      rintro f ⟨k, rfl⟩
      exact (hvhol (φ k)).mono hVR
    obtain ⟨σ, hσ, H⟩ := montel_locallyBounded hVopen hhol' hlb
      (fun k => v (φ k)) (fun k => ⟨k, rfl⟩)
    rcases H with ⟨G, hG⟩ | hG
    · refine ⟨φ ∘ σ, hφ.comp hσ, Or.inl ⟨fun z => a + (b - a) * G z, ?_⟩⟩
      have h1 : TendstoLocallyUniformlyOn (fun k z => a + (b - a) * v (φ (σ k)) z)
          (fun z => a + (b - a) * G z) atTop V :=
        tendstoLocallyUniformlyOn_const_mul_add (b := b - a) (a := a) hG
      refine h1.congr (fun k => ?_)
      intro z hz
      simp only [Function.comp_apply]
      exact hid (φ (σ k)) z
    · refine ⟨φ ∘ σ, hφ.comp hσ, Or.inr ?_⟩
      have h1 : TendstoLocallyUniformlyAtTop (fun k z => a + (b - a) * v (φ (σ k)) z) V :=
        tendstoLocallyUniformlyAtTop_const_mul_add (b := b - a) (a := a) hba hG
      exact tendstoLocallyUniformlyAtTop_congr h1 (fun k z hz => hid (φ (σ k)) z)
  · obtain ⟨φ, hφ, hbig'⟩ := hbig
    obtain ⟨N, hN⟩ := hbig' 1
    set ψ : ℕ → ℕ := fun k => φ (k + N) with hψ_def
    have hψmono : StrictMono ψ := by
      intro p q hpq
      simp only [hψ_def]
      exact hφ (by omega)
    have hψN : ∀ k, 1 ≤ ‖v (ψ k) z₀‖ := by
      intro k
      have h := hN (k + N) (Nat.le_add_left N k)
      simpa only [hψ_def] using h
    set g : ℕ → ℂ → ℂ := fun k z => (v (ψ k) z)⁻¹ with hg_def
    have hgn : ∀ k, ‖g k z₀‖ ≤ 1 := by
      intro k
      have h := hψN k
      simp only [hg_def, norm_inv]
      exact inv_le_one_of_one_le₀ h
    have hgomit : ∀ k z, z ∈ Metric.ball z₀ R → g k z ≠ 0 ∧ g k z ≠ 1 := by
      intro k z hz
      have h := hvomit (ψ k) z hz
      constructor
      · simp only [hg_def]
        exact inv_ne_zero h.1
      · intro hcon
        exact h.2 (inv_eq_one.mp hcon)
    have hghol : ∀ k, DifferentiableOn ℂ (g k) (Metric.ball z₀ R) := by
      intro k
      have h1 : DifferentiableOn ℂ (v (ψ k)) (Metric.ball z₀ R) := hvhol (ψ k)
      have h2 : DifferentiableOn ℂ (fun z => (v (ψ k) z)⁻¹) (Metric.ball z₀ R) :=
        h1.inv (fun z hz => (hvomit (ψ k) z hz).1)
      simpa only [hg_def] using h2
    obtain ⟨B, hB0, hB⟩ := schottky_ball (c := z₀) (R := R) (M := 1) (r := R / 2) hR (by linarith)
    have hbnd : ∀ k z, z ∈ V → ‖g k z‖ ≤ B := by
      intro k z hz
      refine hB (g k) (hghol k) (hgomit k) (hgn k) z ?_
      rw [hV] at hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      exact le_of_lt hz
    have hlb : IsLocallyBoundedOn (Set.range fun k => g k) V :=
      isLocallyBoundedOn_range_of_forall_le hbnd
    have hhol' : ∀ f ∈ Set.range (fun k => g k), DifferentiableOn ℂ f V := by
      rintro f ⟨k, rfl⟩
      exact (hghol k).mono hVR
    obtain ⟨σ, hσ, H⟩ := montel_locallyBounded hVopen hhol' hlb
      (fun k => g k) (fun k => ⟨k, rfl⟩)
    rcases H with ⟨G, hG⟩ | hG
    · have hGhol : DifferentiableOn ℂ G V :=
        hG.differentiableOn (Eventually.of_forall (fun k => hhol' _ ⟨σ k, rfl⟩)) hVopen
      have hVpre : IsPreconnected V := by
        rw [hV]; exact (convex_ball z₀ (R / 2)).isPreconnected
      rcases hurwitz_nonvanishing hVopen hVpre (fun k => g (σ k)) G
          (fun k => hhol' _ ⟨σ k, rfl⟩)
          (fun k z hz => (hgomit (σ k) z (hVR hz)).1) hG with hne | hzero
      · refine ⟨ψ ∘ σ, hψmono.comp hσ, Or.inl ⟨fun z => a + (b - a) * (G z)⁻¹, ?_⟩⟩
        have h1 : TendstoLocallyUniformlyOn (fun k z => (g (σ k) z)⁻¹) (fun z => (G z)⁻¹) atTop V :=
          tendstoLocallyUniformlyOn_inv hVopen hG hne hGhol.continuousOn
            (fun k z hz => (hgomit (σ k) z (hVR hz)).1)
        have h2 := tendstoLocallyUniformlyOn_const_mul_add (b := b - a) (a := a) h1
        refine h2.congr (fun k => ?_)
        intro z hz
        simp only [Function.comp_apply, hg_def, inv_inv]
        exact hid (ψ (σ k)) z
      · refine ⟨ψ ∘ σ, hψmono.comp hσ, Or.inr ?_⟩
        have h1 : TendstoLocallyUniformlyAtTop (fun k z => (g (σ k) z)⁻¹) V :=
          tendstoLocallyUniformlyAtTop_inv_of_tendsto_zero hVopen hG hzero
            (fun k z hz => (hgomit (σ k) z (hVR hz)).1)
        have h2 : TendstoLocallyUniformlyAtTop (fun k z => v (ψ (σ k)) z) V :=
          tendstoLocallyUniformlyAtTop_congr h1 (fun k z hz => by simp only [hg_def, inv_inv])
        have h3 := tendstoLocallyUniformlyAtTop_const_mul_add (b := b - a) (a := a) hba h2
        exact tendstoLocallyUniformlyAtTop_congr h3 (fun k z hz => hid (ψ (σ k)) z)
    · have h2 : TendstoLocallyUniformlyOn (fun k z => v (ψ (σ k)) z) (fun _ => 0) atTop V := by
        have h0 := tendstoLocallyUniformlyOn_inv_of_tendstoLocallyUniformlyAtTop hVopen hG
        refine h0.congr (fun k => ?_)
        intro z hz
        simp only [hg_def, inv_inv]
      have h3 : TendstoLocallyUniformlyOn (fun k z => a + (b - a) * v (ψ (σ k)) z)
          (fun _ => a) atTop V := by
        have h4 := tendstoLocallyUniformlyOn_const_mul_add (b := b - a) (a := a) h2
        simpa using h4
      refine ⟨ψ ∘ σ, hψmono.comp hσ, Or.inl ⟨fun _ => a, ?_⟩⟩
      refine h3.congr (fun k => ?_)
      intro z hz
      simp only [Function.comp_apply]
      exact hid (ψ (σ k)) z


theorem montel_omits_three {Fam : Set (ℂ → ℂ)} {U : Set ℂ} {a b c : ℂ}
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (hU : IsOpen U) (hUc : IsPreconnected U)
    (hhol : ∀ f ∈ Fam, DifferentiableOn ℂ f U)
    (homit : ∀ f ∈ Fam, ∀ z ∈ U, f z ≠ a ∧ f z ≠ b ∧ f z ≠ c) :
    IsNormalFamily Fam U :=
  montel_two_omitted hab hU hUc hhol fun f hf z hz => ⟨(homit f hf z hz).1, (homit f hf z hz).2.1⟩


end Work.Normal
