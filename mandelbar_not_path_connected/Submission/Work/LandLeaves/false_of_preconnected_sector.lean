import Mathlib
import Submission.Work.LandLeaves.cos_nonpos_iff_exists_Icc
import Submission.Work.LandLeaves.preconnected_subset_one_of_disjoint_closed

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Filter Asymptotics Set
open scoped Topology

namespace Work.LandLeaves

noncomputable section

/-! ## 1. The exponential parametrisation `θ ↦ e^{iθ}` of the unit circle -/

/-- `expI θ = e^{iθ}`. -/
def expI (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)

@[simp] lemma expI_zero : expI 0 = 1 := by simp [expI]

lemma expI_add (θ θ' : ℝ) : expI (θ + θ') = expI θ * expI θ' := by
  simp only [expI, Complex.ofReal_add, add_mul, Complex.exp_add]

lemma expI_nat_mul (θ : ℝ) (n : ℕ) : expI ((n : ℝ) * θ) = expI θ ^ n := by
  rw [expI, expI, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

@[simp] lemma norm_expI (θ : ℝ) : ‖expI θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp] lemma expI_re (θ : ℝ) : (expI θ).re = Real.cos θ := Complex.exp_ofReal_mul_I_re θ

@[simp] lemma expI_im (θ : ℝ) : (expI θ).im = Real.sin θ := Complex.exp_ofReal_mul_I_im θ

lemma expI_eq_iff (θ θ' : ℝ) :
    expI θ = expI θ' ↔ ∃ q : ℤ, θ = θ' + (q : ℝ) * (2 * Real.pi) := by
  have h : expI θ = expI θ' ↔ Circle.exp θ = Circle.exp θ' := by
    constructor
    · intro hf
      refine Subtype.ext ?_
      show Complex.exp (↑θ * Complex.I) = Complex.exp (↑θ' * Complex.I)
      simpa only [expI] using hf
    · intro hf
      have := congrArg (Subtype.val : Circle → ℂ) hf
      simpa only [Circle.coe_exp, expI] using this
  rw [h, Circle.exp_eq_exp]

lemma expI_int_mul_two_pi (θ : ℝ) (q : ℤ) :
    expI (θ + (q : ℝ) * (2 * Real.pi)) = expI θ := by
  rw [expI_eq_iff]
  exact ⟨q, rfl⟩

/-! ## 2. Closed arcs of the unit circle -/

/-- The closed arc `{e^{iθ} : a ≤ θ ≤ b}` of the unit circle. -/
def cArc (a b : ℝ) : Set ℂ := expI '' Set.Icc a b

lemma mem_cArc_iff {a b : ℝ} {z : ℂ} : z ∈ cArc a b ↔ ∃ θ ∈ Set.Icc a b, expI θ = z :=
  Iff.rfl

lemma continuous_expI : Continuous expI := by
  unfold expI
  fun_prop

lemma isCompact_cArc (a b : ℝ) : IsCompact (cArc a b) :=
  isCompact_Icc.image continuous_expI

lemma isClosed_cArc (a b : ℝ) : IsClosed (cArc a b) :=
  (isCompact_cArc a b).isClosed

lemma cArc_int_shift (a b : ℝ) (q : ℤ) :
    cArc (a + (q : ℝ) * (2 * Real.pi)) (b + (q : ℝ) * (2 * Real.pi)) = cArc a b := by
  ext z
  constructor
  · rintro ⟨t, ht, htz⟩
    refine ⟨t - (q : ℝ) * (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
    · linarith [ht.1]
    · linarith [ht.2]
    · have hper : expI ((t - (q : ℝ) * (2 * Real.pi)) + (q : ℝ) * (2 * Real.pi))
          = expI (t - (q : ℝ) * (2 * Real.pi)) :=
        expI_int_mul_two_pi (t - (q : ℝ) * (2 * Real.pi)) q
      rw [show (t - (q : ℝ) * (2 * Real.pi)) + (q : ℝ) * (2 * Real.pi) = t by ring] at hper
      rw [← hper]
      exact htz
  · rintro ⟨t, ht, htz⟩
    refine ⟨t + (q : ℝ) * (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
    · linarith [ht.1]
    · linarith [ht.2]
    · rw [expI_int_mul_two_pi]
      exact htz

/-! ## 3. The arcs cut out by the sector `cos (arg c + n θ) ≤ 0` -/

/-- Left endpoint of the `k`-th arc. -/
def arcA (γ : ℝ) (n : ℕ) (k : ℤ) : ℝ :=
  (Real.pi / 2 - γ) / (n : ℝ) + (k : ℝ) * (2 * Real.pi / (n : ℝ))

/-- Right endpoint of the `k`-th arc. -/
def arcB (γ : ℝ) (n : ℕ) (k : ℤ) : ℝ :=
  (Real.pi / 2 + Real.pi - γ) / (n : ℝ) + (k : ℝ) * (2 * Real.pi / (n : ℝ))

/-- The `k`-th closed arc of the sector. -/
def arcJ (γ : ℝ) (n : ℕ) (k : ℤ) : Set ℂ := cArc (arcA γ n k) (arcB γ n k)

lemma arcA_mono (γ : ℝ) (n : ℕ) (hn : 0 ≤ (n : ℝ)) (k k' : ℤ) (h : k ≤ k') :
    arcA γ n k ≤ arcA γ n k' := by
  have hc : (0 : ℝ) ≤ 2 * Real.pi / (n : ℝ) := div_nonneg (by positivity) hn
  have hk : ((k : ℤ) : ℝ) ≤ ((k' : ℤ) : ℝ) := by exact_mod_cast h
  simp only [arcA]
  exact add_le_add_right (mul_le_mul_of_nonneg_right hk hc) _

lemma arcB_mono (γ : ℝ) (n : ℕ) (hn : 0 ≤ (n : ℝ)) (k k' : ℤ) (h : k ≤ k') :
    arcB γ n k ≤ arcB γ n k' := by
  have hc : (0 : ℝ) ≤ 2 * Real.pi / (n : ℝ) := div_nonneg (by positivity) hn
  have hk : ((k : ℤ) : ℝ) ≤ ((k' : ℤ) : ℝ) := by exact_mod_cast h
  simp only [arcB]
  exact add_le_add_right (mul_le_mul_of_nonneg_right hk hc) _

lemma n_mul_arcA (γ : ℝ) (n : ℕ) (hn0 : (n : ℝ) ≠ 0) (k : ℤ) :
    (n : ℝ) * arcA γ n k = Real.pi / 2 - γ + (k : ℝ) * (2 * Real.pi) := by
  simp only [arcA]
  field_simp

lemma n_mul_arcB (γ : ℝ) (n : ℕ) (hn0 : (n : ℝ) ≠ 0) (k : ℤ) :
    (n : ℝ) * arcB γ n k = Real.pi / 2 + Real.pi - γ + (k : ℝ) * (2 * Real.pi) := by
  simp only [arcB]
  field_simp

lemma arcA_succ_sub_arcB (γ : ℝ) (n : ℕ) (hn0 : (n : ℝ) ≠ 0) (k : ℤ) :
    arcA γ n (k + 1) - arcB γ n k = Real.pi / (n : ℝ) := by
  simp only [arcA, arcB]; push_cast; field_simp; ring

lemma arcB_last_sub_arcA_zero (γ : ℝ) (n : ℕ) (hn0 : (n : ℝ) ≠ 0) :
    arcB γ n ((n : ℤ) - 1) - arcA γ n 0 = 2 * Real.pi - Real.pi / (n : ℝ) := by
  simp only [arcA, arcB]; push_cast; field_simp; ring

lemma arcA_add_int_mul (γ : ℝ) (n : ℕ) (hn0 : (n : ℝ) ≠ 0) (k q : ℤ) :
    arcA γ n (k + n * q) = arcA γ n k + (q : ℝ) * (2 * Real.pi) := by
  have hcast : ((k + n * q : ℤ) : ℝ) = (k : ℝ) + (n : ℝ) * (q : ℝ) := by
    push_cast; ring
  simp only [arcA, hcast]
  field_simp
  ring

lemma arcB_add_int_mul (γ : ℝ) (n : ℕ) (hn0 : (n : ℝ) ≠ 0) (k q : ℤ) :
    arcB γ n (k + n * q) = arcB γ n k + (q : ℝ) * (2 * Real.pi) := by
  have hcast : ((k + n * q : ℤ) : ℝ) = (k : ℝ) + (n : ℝ) * (q : ℝ) := by
    push_cast; ring
  simp only [arcB, hcast]
  field_simp
  ring

lemma arcJ_add_int_mul (γ : ℝ) (n : ℕ) (hn0 : (n : ℝ) ≠ 0) (k q : ℤ) :
    arcJ γ n (k + n * q) = arcJ γ n k := by
  simp only [arcJ]
  rw [arcA_add_int_mul γ n hn0 k q, arcB_add_int_mul γ n hn0 k q, cArc_int_shift]

lemma arcJ_emod (γ : ℝ) (n : ℕ) (hn0 : (n : ℝ) ≠ 0) (k : ℤ) :
    arcJ γ n k = arcJ γ n (k % n) := by
  conv_lhs => rw [← Int.emod_add_mul_ediv k n]
  rw [arcJ_add_int_mul γ n hn0 (k % n) (k / n)]

lemma arcJ_disjoint_of_lt (γ : ℝ) (n : ℕ) (hn : 0 < n) (k k' : ℤ)
    (hk : 0 ≤ k) (hk' : k' < (n : ℤ)) (hlt : k < k') :
    Disjoint (arcJ γ n k) (arcJ γ n k') := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnR : (0 : ℝ) ≤ (n : ℝ) := hn0.le
  have hπn : 0 < Real.pi / (n : ℝ) := div_pos Real.pi_pos hn0
  rw [Set.disjoint_left]
  intro z hz hz'
  obtain ⟨θ, hθ, hθz⟩ := hz
  obtain ⟨θ', hθ', hθ'z⟩ := hz'
  have heq : expI θ = expI θ' := by rw [hθz, hθ'z]
  obtain ⟨q, hq⟩ := (expI_eq_iff θ θ').mp heq
  have hlow : Real.pi / (n : ℝ) ≤ θ' - θ := by
    have h1 : arcA γ n (k + 1) = arcB γ n k + Real.pi / (n : ℝ) := by
      have := arcA_succ_sub_arcB γ n hn0.ne' k
      linarith
    have h2 : arcA γ n (k + 1) ≤ arcA γ n k' := arcA_mono γ n hnR (k + 1) k' (by omega)
    linarith [hθ.1, hθ.2, hθ'.1, hθ'.2, h2, h1]
  have hup : θ' - θ < 2 * Real.pi := by
    have h1 : arcB γ n ((n : ℤ) - 1) = arcA γ n 0 + (2 * Real.pi - Real.pi / (n : ℝ)) := by
      have := arcB_last_sub_arcA_zero γ n hn0.ne'
      linarith
    have h2 : arcB γ n k' ≤ arcB γ n ((n : ℤ) - 1) :=
      arcB_mono γ n hnR k' ((n : ℤ) - 1) (by omega)
    have h3 : arcA γ n 0 ≤ arcA γ n k := arcA_mono γ n hnR 0 k hk
    linarith [hθ.1, hθ.2, hθ'.1, hθ'.2, h2, h3, h1, hπn]
  have hqR : (q : ℝ) * (2 * Real.pi) = θ - θ' := by rw [hq]; ring
  have hqneg : (q : ℝ) < 0 := by
    have h : (q : ℝ) * (2 * Real.pi) < 0 := by rw [hqR]; linarith
    nlinarith [Real.pi_pos]
  have hqgt : (-1 : ℝ) < (q : ℝ) := by
    have h : -(2 * Real.pi) < (q : ℝ) * (2 * Real.pi) := by rw [hqR]; linarith
    nlinarith [Real.pi_pos]
  have hqz : ((-1 : ℤ) : ℝ) < (q : ℝ) := by push_cast; exact hqgt
  have hq_int : (-1 : ℤ) < q := by exact_mod_cast hqz
  have hq_int_neg : q < 0 := by exact_mod_cast hqneg
  omega

lemma arcJ_disjoint (γ : ℝ) (n : ℕ) (hn : 0 < n) (k k' : ℤ)
    (hk : 0 ≤ k) (hk' : k < (n : ℤ)) (hl : 0 ≤ k') (hl' : k' < (n : ℤ)) (hne : k ≠ k') :
    Disjoint (arcJ γ n k) (arcJ γ n k') := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact arcJ_disjoint_of_lt γ n hn k k' hk hl' h
  · rw [disjoint_comm]
    exact arcJ_disjoint_of_lt γ n hn k' k hl hk' h

/-! ## 4. The real/complex computations -/

lemma expI_arg_of_norm_one {z : ℂ} (hz : ‖z‖ = 1) : expI z.arg = z := by
  have h := Complex.norm_mul_exp_arg_mul_I z
  rw [hz] at h
  simpa [expI] using h

lemma re_mul_pow_expI (c : ℂ) (θ : ℝ) (n : ℕ) :
    (c * expI θ ^ n).re = ‖c‖ * Real.cos (c.arg + (n : ℝ) * θ) := by
  have hc' : c = (‖c‖ : ℂ) * expI c.arg := by
    simp only [expI]
    exact (Complex.norm_mul_exp_arg_mul_I c).symm
  conv_lhs => rw [hc', ← expI_nat_mul, mul_assoc, ← expI_add]
  simp [Complex.mul_re]

lemma re_mul_pow_of_norm_one (c d : ℂ) (hd : ‖d‖ = 1) (n : ℕ) :
    (c * d ^ n).re = ‖c‖ * Real.cos (c.arg + (n : ℝ) * d.arg) := by
  have hd' : expI d.arg = d := expI_arg_of_norm_one hd
  have hc' : c = (‖c‖ : ℂ) * expI c.arg := by
    simp only [expI]
    exact (Complex.norm_mul_exp_arg_mul_I c).symm
  have hdn : d ^ n = expI ((n : ℝ) * d.arg) := by
    conv_lhs => rw [← hd']
    rw [← expI_nat_mul]
  conv_lhs => rw [hc', hdn, mul_assoc, ← expI_add]
  simp [Complex.mul_re]

lemma norm_eq_one_of_pow_eq_one {z : ℂ} {n : ℕ} (hn : n ≠ 0) (hzn : z ^ n = 1) :
    ‖z‖ = 1 := by
  have h : ‖z‖ ^ n = 1 := by rw [← norm_pow, hzn, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg z) hn).mp h

/-! ## 5. The sector and its covering by arcs -/

lemma arcJ_subset_sector (c : ℂ) (hc : c ≠ 0) (n : ℕ) (hn : 0 < n) (k : ℤ) :
    arcJ c.arg n k ⊆ {d : ℂ | ‖d‖ = 1 ∧ (c * d ^ n).re ≤ 0} := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  intro d hd
  obtain ⟨θ, hθ, rfl⟩ := hd
  refine ⟨norm_expI θ, ?_⟩
  rw [re_mul_pow_expI c θ n]
  have h1 : Real.pi / 2 ≤ c.arg + (n : ℝ) * θ - (k : ℝ) * (2 * Real.pi) := by
    have h := mul_le_mul_of_nonneg_left hθ.1 hn0.le
    rw [n_mul_arcA c.arg n hn0.ne' k] at h
    linarith
  have h2 : c.arg + (n : ℝ) * θ - (k : ℝ) * (2 * Real.pi) ≤ Real.pi + Real.pi / 2 := by
    have h := mul_le_mul_of_nonneg_left hθ.2 hn0.le
    rw [n_mul_arcB c.arg n hn0.ne' k] at h
    linarith
  have hcos := Real.cos_nonpos_of_pi_div_two_le_of_le h1 h2
  rw [← Real.cos_sub_int_mul_two_pi (c.arg + (n : ℝ) * θ) k]
  exact mul_nonpos_of_nonneg_of_nonpos hcpos.le hcos

lemma sector_subset_arcs (c : ℂ) (hc : c ≠ 0) (n : ℕ) (hn : 0 < n) (d : ℂ)
    (hd : ‖d‖ = 1) (hsec : (c * d ^ n).re ≤ 0) :
    d ∈ ⋃ k ∈ Finset.Icc (0 : ℤ) ((n : ℤ) - 1), arcJ c.arg n k := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hrew := re_mul_pow_of_norm_one c d hd n
  have hcos : Real.cos (c.arg + (n : ℝ) * d.arg) ≤ 0 := by
    have h : ‖c‖ * Real.cos (c.arg + (n : ℝ) * d.arg) ≤ 0 := by
      rw [← hrew]; exact hsec
    exact nonpos_of_mul_nonpos_right h hcpos
  obtain ⟨m, hm⟩ := cos_nonpos_iff_exists_Icc (c.arg + (n : ℝ) * d.arg) |>.mp hcos
  have hmA : arcA c.arg n m ≤ d.arg := by
    have h1 : (n : ℝ) * arcA c.arg n m ≤ (n : ℝ) * d.arg := by
      rw [n_mul_arcA c.arg n hn0.ne' m]; linarith [hm.1]
    exact le_of_mul_le_mul_left h1 hn0
  have hmB : d.arg ≤ arcB c.arg n m := by
    have h1 : (n : ℝ) * d.arg ≤ (n : ℝ) * arcB c.arg n m := by
      rw [n_mul_arcB c.arg n hn0.ne' m]; linarith [hm.2]
    exact le_of_mul_le_mul_left h1 hn0
  have hdmem : d ∈ arcJ c.arg n m := ⟨d.arg, ⟨hmA, hmB⟩, expI_arg_of_norm_one hd⟩
  rw [arcJ_emod c.arg n hn0.ne' m] at hdmem
  refine Set.mem_iUnion₂.mpr ⟨m % n, ?_, hdmem⟩
  rw [Finset.mem_Icc]
  constructor
  · exact Int.emod_nonneg m (by exact_mod_cast hn.ne')
  · have := Int.emod_lt_of_pos m (show (0 : ℤ) < (n : ℤ) by omega)
    omega

/-- Multiplication by a unit complex number `z = expI z.arg` carries the arc `cArc a b` to the arc
`cArc (z.arg + a) (z.arg + b)`. -/
lemma mulSet_cArc {z : ℂ} (hz : z = expI z.arg) (a b : ℝ) :
    (fun w => z * w) '' cArc a b = cArc (z.arg + a) (z.arg + b) := by
  ext w
  constructor
  · rintro ⟨u, ⟨θ, hθ, rfl⟩, rfl⟩
    refine ⟨z.arg + θ, ⟨by linarith [hθ.1], by linarith [hθ.2]⟩, ?_⟩
    show expI (z.arg + θ) = z * expI θ
    rw [expI_add]
    exact (congrArg (fun v => v * expI θ) hz).symm
  · rintro ⟨φ, hφ, rfl⟩
    refine ⟨expI (φ - z.arg),
      ⟨φ - z.arg, ⟨by linarith [hφ.1], by linarith [hφ.2]⟩, rfl⟩, ?_⟩
    calc z * expI (φ - z.arg) = expI z.arg * expI (φ - z.arg) :=
          congrArg (fun v => v * expI (φ - z.arg)) hz
      _ = expI (z.arg + (φ - z.arg)) := (expI_add z.arg (φ - z.arg)).symm
      _ = expI φ := by congr 1; ring

/-- The `z`-action on the sector arcs. -/
lemma mulSet_arcJ {z : ℂ} (hz : z = expI z.arg) (γ : ℝ) (n : ℕ) (hn0 : (n : ℝ) ≠ 0)
    {m : ℤ} (hm : (n : ℝ) * z.arg = (m : ℝ) * (2 * Real.pi)) (k : ℤ) :
    (fun w => z * w) '' arcJ γ n k = arcJ γ n (k + m) := by
  have hzarg : z.arg = (m : ℝ) * (2 * Real.pi) / (n : ℝ) := by
    rw [eq_div_iff hn0]; linarith [hm]
  have hA : z.arg + arcA γ n k = arcA γ n (k + m) := by
    simp only [arcA]
    rw [hzarg]
    push_cast
    ring
  have hB : z.arg + arcB γ n k = arcB γ n (k + m) := by
    simp only [arcB]
    rw [hzarg]
    push_cast
    ring
  simp only [arcJ]
  rw [mulSet_cArc hz, hA, hB]

/-! ## 6. The main theorem -/

set_option linter.unusedVariables false in
theorem false_of_preconnected_sector {n : ℕ} (hn : 2 ≤ n) {c z : ℂ} (hc : c ≠ 0)
    (hzn : z ^ n = 1) (hz1 : z ≠ 1) {L : Set ℂ} (hLcpt : IsCompact L)
    (hLpre : IsPreconnected L) (hLne : L.Nonempty) (hLsph : L ⊆ Metric.sphere (0 : ℂ) 1)
    (hLsect : ∀ d ∈ L, (c * d ^ n).re ≤ 0) (hLinv : ∀ d ∈ L, z * d ∈ L) : False := by
  have hn0 : 0 < n := by omega
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hnR' : (n : ℝ) ≠ 0 := hnR.ne'
  have hnZ : (n : ℤ) ≠ 0 := by omega
  -- ### Step 1: `L` lies in one of the arcs.
  have hcover : L ⊆ ⋃ k ∈ Finset.Icc (0 : ℤ) ((n : ℤ) - 1), arcJ c.arg n k := by
    intro d hd
    have hd1 : ‖d‖ = 1 := by
      have h := Metric.mem_sphere.mp (hLsph hd)
      simpa [dist_eq_norm] using h
    exact sector_subset_arcs c hc n hn0 d hd1 (hLsect d hd)
  obtain ⟨j, hj, hLj⟩ :=
    preconnected_subset_one_of_disjoint_closed hLpre hLne
      (Finset.Icc (0 : ℤ) ((n : ℤ) - 1)) (fun k => arcJ c.arg n k)
      (fun k => isClosed_cArc (arcA c.arg n k) (arcB c.arg n k))
      (fun k hk k' hk' hne =>
        arcJ_disjoint c.arg n hn0 k k'
          (Finset.mem_Icc.mp hk).1 (by have := (Finset.mem_Icc.mp hk).2; omega)
          (Finset.mem_Icc.mp hk').1 (by have := (Finset.mem_Icc.mp hk').2; omega) hne)
      hcover
  have hj0 : 0 ≤ j := (Finset.mem_Icc.mp hj).1
  have hjn : j < (n : ℤ) := by have := (Finset.mem_Icc.mp hj).2; omega
  -- ### Step 2: the `n`-th root of unity `z` and the integer `m` with `n * arg z = m * 2π`.
  have hz1n : ‖z‖ = 1 := norm_eq_one_of_pow_eq_one (by omega) hzn
  have hzexp : z = expI z.arg := (expI_arg_of_norm_one hz1n).symm
  have hzn' : expI ((n : ℝ) * z.arg) = 1 := by
    rw [expI_nat_mul, ← hzexp, hzn]
  obtain ⟨m, hm⟩ := (expI_eq_iff ((n : ℝ) * z.arg) 0).mp (by simpa [expI_zero] using hzn')
  have hmz : (n : ℝ) * z.arg = (m : ℝ) * (2 * Real.pi) := by linarith [hm]
  have hndvd : ¬ ((n : ℤ) ∣ m) := by
    rintro ⟨t, ht⟩
    have hzt : z.arg = (t : ℝ) * (2 * Real.pi) := by
      have h : (n : ℝ) * z.arg = (n : ℝ) * ((t : ℝ) * (2 * Real.pi)) := by
        rw [hmz, ht]; push_cast; ring
      exact mul_left_cancel₀ hnR' h
    apply hz1
    rw [hzexp, hzt]
    simpa using expI_int_mul_two_pi 0 t
  -- ### Step 3: `z * L ⊆ L` meets two different arcs.
  have hzimg : (fun d => z * d) '' L ⊆ arcJ c.arg n j :=
    Subset.trans (by rintro _ ⟨d, hd, rfl⟩; exact hLinv d hd) hLj
  set j' : ℤ := (j + m) % n with hj'def
  have hj'0 : 0 ≤ j' := Int.emod_nonneg (j + m) hnZ
  have hj'n : j' < (n : ℤ) := Int.emod_lt_of_pos (j + m) (by omega)
  have hne' : j' ≠ j := by
    intro h
    apply hndvd
    refine ⟨(j + m) / n, ?_⟩
    have h1 : (j + m) % n + n * ((j + m) / n) = j + m := Int.emod_add_mul_ediv (j + m) n
    rw [← hj'def, h] at h1
    omega
  have hmul : (fun w => z * w) '' arcJ c.arg n j = arcJ c.arg n j' := by
    rw [mulSet_arcJ hzexp c.arg n hnR' hmz j, arcJ_emod c.arg n hnR']
  have hzimg' : (fun d => z * d) '' L ⊆ arcJ c.arg n j' := by
    rw [← hmul]
    exact Set.image_mono hLj
  have hdisj := arcJ_disjoint c.arg n hn0 j j' hj0 hjn hj'0 hj'n (Ne.symm hne')
  obtain ⟨d, hd⟩ := hLne.image (fun d => z * d)
  exact (Set.disjoint_left.mp hdisj (hzimg hd)) (hzimg' hd)

end

end Work.LandLeaves
