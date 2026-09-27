import Mathlib
import Submission.Work.Drive.N2.exists_exp_Icc_cover

/-!
# Arc rigidity on the circle

`Work.Drive.N2.arcRigidity`: if `A` is a closed connected subset of the unit circle `Circle`
with nonempty interior and `y : Circle → Circle` is continuous and injective on `A`, then the
maps `x ↦ x / y x` and `x ↦ x * y x` cannot both be surjective onto `Circle`.

The proof uses the parametrisation of `A` as `Circle.exp '' Icc α β` with `β - α ≤ 2π`
(`Work.Drive.N2.exists_exp_Icc_cover`), lifts along the covering map `Circle.exp : ℝ → Circle`,
and uses that on an interval the lifted difference `s ↦ γ s - φ s` has range of extent `< 2π`.
-/

namespace Work.Drive.N2

open Set Function

open scoped Topology

noncomputable section

/-! ## Clamping to the unit interval -/

/-- Clamp a real number into `[0, 1]`. -/
def clamp01 (s : ℝ) : ℝ := max 0 (min 1 s)

lemma clamp01_continuous : Continuous clamp01 :=
  continuous_const.max (continuous_const.min continuous_id)

lemma clamp01_mem (s : ℝ) : clamp01 s ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma clamp01_of_mem {s : ℝ} (h : s ∈ Icc (0 : ℝ) 1) : clamp01 s = s := by
  rw [clamp01, min_eq_right h.2, max_eq_right h.1]

/-! ## Lifting along `Circle.exp` -/

/-- A continuous map `ℝ → Circle` admits a continuous real lift. -/
theorem exists_continuous_lift {g : ℝ → Circle} (hg : Continuous g) :
    ∃ φ : ℝ → ℝ, Continuous φ ∧ ∀ s, Circle.exp (φ s) = g s := by
  obtain ⟨e, he⟩ := Circle.exp_surjective (g 0)
  obtain ⟨F, ⟨-, hFcomp⟩, -⟩ := Circle.isCoveringMap_exp.existsUnique_continuousMap_lifts
    (⟨g, hg⟩ : C(ℝ, Circle)) 0 e he
  exact ⟨fun s => F s, F.continuous, fun s => congrFun hFcomp s⟩

/-! ## The image of a short interval is a proper arc -/

/-- An interval of length `< 2π` does not map onto the circle. -/
theorem exp_image_Icc_ne_univ {m M : ℝ} (h : M - m < 2 * Real.pi) :
    Circle.exp '' Icc m M ≠ univ := by
  intro hc
  set ε : ℝ := (2 * Real.pi - (M - m)) / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  have hlt : M < m + 2 * Real.pi - ε := by rw [hε]; linarith
  have hmem : Circle.exp (m - ε) ∈ Circle.exp '' Icc m M := by rw [hc]; trivial
  obtain ⟨t, ht, hte⟩ := hmem
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hte
  have ht1 : m ≤ t := ht.1
  have ht2 : t ≤ M := ht.2
  have hk0 : (0 : ℤ) < k := by
    have h1 : ε ≤ (k : ℝ) * (2 * Real.pi) := by rw [hk] at ht1; linarith
    have h4 : 0 < (k : ℝ) * (2 * Real.pi) := lt_of_lt_of_le hεpos h1
    have h5 : 0 < (k : ℝ) :=
      pos_of_mul_pos_left (a := (k : ℝ)) (b := 2 * Real.pi) h4 (le_of_lt Real.two_pi_pos)
    exact_mod_cast h5
  have hk1 : (1 : ℤ) ≤ k := by omega
  have h2 : m + 2 * Real.pi - ε ≤ t := by
    rw [hk]
    have h3 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
    nlinarith [Real.two_pi_pos]
  linarith

/-! ## The counting argument on the lifted line -/

/-- If `γ` and `φ` are strictly increasing on `[0,1]` with increments at most `2π`, then the
lifted difference `γ - φ` has range of extent `< 2π`. -/
theorem exp_image_sub_ne_univ {γ φ : ℝ → ℝ}
    (hγc : ContinuousOn γ (Icc (0 : ℝ) 1)) (hφc : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hγmono : StrictMonoOn γ (Icc (0 : ℝ) 1)) (hφmono : StrictMonoOn φ (Icc (0 : ℝ) 1))
    (hG : γ 1 - γ 0 ≤ 2 * Real.pi) (hP : φ 1 - φ 0 ≤ 2 * Real.pi) :
    Circle.exp '' ((fun s => γ s - φ s) '' Icc (0 : ℝ) 1) ≠ univ := by
  obtain ⟨sm, hsm, hmin⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMinOn
    ⟨0, by norm_num⟩ (hγc.sub hφc)
  obtain ⟨sM, hsM, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_isMaxOn
    ⟨0, by norm_num⟩ (hγc.sub hφc)
  have hsub : (fun s => γ s - φ s) '' Icc (0 : ℝ) 1 ⊆
      Icc (γ sm - φ sm) (γ sM - φ sM) := by
    rintro _ ⟨s, hs, rfl⟩
    exact ⟨hmin hs, hmax hs⟩
  have hdiff : (γ sM - φ sM) - (γ sm - φ sm) < 2 * Real.pi := by
    rcases lt_trichotomy sM sm with h | h | h
    · have hφlt : φ sM < φ sm := hφmono hsM hsm h
      have h1 : φ sm - φ sM ≤ φ 1 - φ 0 := by
        have hA : φ sm ≤ φ 1 := hφmono.monotoneOn hsm ⟨by norm_num, le_rfl⟩ hsm.2
        have hB : φ 0 ≤ φ sM := hφmono.monotoneOn ⟨le_rfl, by norm_num⟩ hsM hsM.1
        linarith
      have h2 : γ sM - γ sm < 0 := by
        have := hγmono hsM hsm h
        linarith
      linarith
    · rw [h]; linarith [Real.two_pi_pos]
    · have h1 : γ sM - γ sm ≤ γ 1 - γ 0 := by
        have hA : γ sM ≤ γ 1 := hγmono.monotoneOn hsM ⟨by norm_num, le_rfl⟩ hsM.2
        have hB : γ 0 ≤ γ sm := hγmono.monotoneOn ⟨le_rfl, by norm_num⟩ hsm hsm.1
        linarith
      have h2 : 0 < φ sM - φ sm := by
        have := hφmono hsm hsM h
        linarith
      linarith
  exact fun huniv => exp_image_Icc_ne_univ hdiff (eq_univ_of_subset (image_mono hsub) huniv)

/-- The antitone version of `exp_image_sub_ne_univ`. -/
theorem exp_image_add_ne_univ {γ φ : ℝ → ℝ}
    (hγc : ContinuousOn γ (Icc (0 : ℝ) 1)) (hφc : ContinuousOn φ (Icc (0 : ℝ) 1))
    (hγmono : StrictMonoOn γ (Icc (0 : ℝ) 1)) (hφanti : StrictAntiOn φ (Icc (0 : ℝ) 1))
    (hG : γ 1 - γ 0 ≤ 2 * Real.pi) (hP : φ 0 - φ 1 ≤ 2 * Real.pi) :
    Circle.exp '' ((fun s => γ s + φ s) '' Icc (0 : ℝ) 1) ≠ univ := by
  have hle : (fun s => -φ s) 1 - (fun s => -φ s) 0 ≤ 2 * Real.pi := by
    have : (fun s => -φ s) 1 - (fun s => -φ s) 0 = φ 0 - φ 1 := by ring
    rw [this]; exact hP
  have h := exp_image_sub_ne_univ (γ := γ) (φ := fun s => -φ s) hγc hφc.neg hγmono
    hφanti.neg hG hle
  simpa only [sub_neg_eq_add] using h

/-! ## Relating the images of `x ↦ x / y x` and `x ↦ x * y x` to the lifted expression -/

lemma image_div_eq {y : Circle → Circle} {A : Set Circle} {γ φ : ℝ → ℝ}
    (hA : A = Circle.exp '' (γ '' Icc (0 : ℝ) 1))
    (hφ : ∀ s ∈ Icc (0 : ℝ) 1, Circle.exp (φ s) = y (Circle.exp (γ s))) :
    (fun x => x / y x) '' A = Circle.exp '' ((fun s => γ s - φ s) '' Icc (0 : ℝ) 1) := by
  rw [hA]
  ext z
  simp only [mem_image]
  constructor
  · rintro ⟨x, ⟨a, ⟨s, hs, hgs⟩, hxa⟩, hzx⟩
    exact ⟨γ s - φ s, ⟨s, hs, rfl⟩, by rw [← hzx, ← hxa, ← hgs, Circle.exp_sub, ← hφ s hs]⟩
  · rintro ⟨_w, ⟨s, hs, hws⟩, hzw⟩
    exact ⟨Circle.exp (γ s), ⟨γ s, ⟨s, hs, rfl⟩, rfl⟩,
      by rw [← hzw, ← hws, Circle.exp_sub, ← hφ s hs]⟩

lemma image_mul_eq {y : Circle → Circle} {A : Set Circle} {γ φ : ℝ → ℝ}
    (hA : A = Circle.exp '' (γ '' Icc (0 : ℝ) 1))
    (hφ : ∀ s ∈ Icc (0 : ℝ) 1, Circle.exp (φ s) = y (Circle.exp (γ s))) :
    (fun x => x * y x) '' A = Circle.exp '' ((fun s => γ s + φ s) '' Icc (0 : ℝ) 1) := by
  rw [hA]
  ext z
  simp only [mem_image]
  constructor
  · rintro ⟨x, ⟨a, ⟨s, hs, hgs⟩, hxa⟩, hzx⟩
    exact ⟨γ s + φ s, ⟨s, hs, rfl⟩, by rw [← hzx, ← hxa, ← hgs, Circle.exp_add, ← hφ s hs]⟩
  · rintro ⟨_w, ⟨s, hs, hws⟩, hzw⟩
    exact ⟨Circle.exp (γ s), ⟨γ s, ⟨s, hs, rfl⟩, rfl⟩,
      by rw [← hzw, ← hws, Circle.exp_add, ← hφ s hs]⟩

/-! ## The proper arc case -/

theorem not_both_surj_of_lt {A : Set Circle} {y : Circle → Circle} (hy : ContinuousOn y A)
    (hinj : Set.InjOn y A) {α β : ℝ} (hαβ : α < β) (hlt : β - α < 2 * Real.pi)
    (hcover : A = Circle.exp '' Icc α β) :
    ¬ ((∀ t : Circle, ∃ x ∈ A, t = x / y x) ∧ (∀ t : Circle, ∃ x ∈ A, t = x * y x)) := by
  rintro ⟨hd, hs⟩
  set γ : ℝ → ℝ := fun s => α + (β - α) * clamp01 s with hγdef
  have hγc : Continuous γ := by
    rw [hγdef]
    exact continuous_const.add (clamp01_continuous.const_mul (β - α))
  have hγmem : ∀ s : ℝ, γ s ∈ Icc α β := by
    intro s
    have h := clamp01_mem s
    constructor <;> nlinarith [h.1, h.2, hαβ]
  have hγlin : ∀ s ∈ Icc (0 : ℝ) 1, γ s = α + (β - α) * s := by
    intro s hs
    rw [hγdef]
    simp only [clamp01_of_mem hs]
  have hγcont : ContinuousOn γ (Icc (0 : ℝ) 1) := hγc.continuousOn
  have hγmono : StrictMonoOn γ (Icc (0 : ℝ) 1) := by
    intro x hx t ht hxt
    rw [hγlin x hx, hγlin t ht]
    nlinarith
  have hγ0 : γ 0 = α := by rw [hγlin 0 (by norm_num)]; ring
  have hγ1 : γ 1 = β := by rw [hγlin 1 (by norm_num)]; ring
  have hG : γ 1 - γ 0 ≤ 2 * Real.pi := by rw [hγ1, hγ0]; linarith
  have hγimg : γ '' Icc (0 : ℝ) 1 = Icc α β := by
    rw [hγcont.image_Icc_of_monotoneOn (by norm_num) hγmono.monotoneOn, hγ0, hγ1]
  have hmemA : ∀ s : ℝ, Circle.exp (γ s) ∈ A := by
    intro s
    rw [hcover]
    exact ⟨γ s, hγmem s, rfl⟩
  have hg : Continuous fun s : ℝ => y (Circle.exp (γ s)) :=
    hy.comp_continuous (Circle.exp.continuous.comp hγc) hmemA
  obtain ⟨φ, hφc, hφlift⟩ := exists_continuous_lift hg
  have hφinj : InjOn φ (Icc (0 : ℝ) 1) := by
    intro s hsc t htc hst
    have hy_eq : y (Circle.exp (γ s)) = y (Circle.exp (γ t)) := by
      rw [← hφlift s, ← hφlift t, hst]
    have hexp_eq : Circle.exp (γ s) = Circle.exp (γ t) :=
      hinj (hmemA s) (hmemA t) hy_eq
    have hγ_eq : γ s = γ t := Circle.exp_injOn_Icc hlt (hγmem s) (hγmem t) hexp_eq
    exact hγmono.injOn hsc htc hγ_eq
  have hA' : A = Circle.exp '' (γ '' Icc (0 : ℝ) 1) := by rw [hcover, hγimg]
  rcases hφc.continuousOn.strictMonoOn_of_injOn_Icc' (by norm_num) hφinj with hmono | hanti
  · have hP : φ 1 - φ 0 < 2 * Real.pi := by
      by_contra hcon
      have hcon' : 2 * Real.pi ≤ φ 1 - φ 0 := not_lt.mp hcon
      have hmem : φ 0 + 2 * Real.pi ∈ Icc (φ 0) (φ 1) :=
        ⟨by linarith [Real.two_pi_pos], by linarith⟩
      obtain ⟨s, hsr, hsv⟩ := intermediate_value_Icc (by norm_num) hφc.continuousOn hmem
      have hs0 : 0 < s := by
        rcases lt_or_eq_of_le hsr.1 with hh | hh
        · exact hh
        · exfalso; rw [← hh] at hsv; linarith [Real.two_pi_pos]
      have hy_eq : y (Circle.exp (γ s)) = y (Circle.exp (γ 0)) := by
        rw [← hφlift s, ← hφlift 0, hsv, Circle.exp_add_two_pi]
      have hexp : Circle.exp (γ s) = Circle.exp (γ 0) := hinj (hmemA s) (hmemA 0) hy_eq
      have hγeq : γ s = γ 0 := Circle.exp_injOn_Icc hlt (hγmem s) (hγmem 0) hexp
      have : s = 0 := hγmono.injOn hsr (by norm_num) hγeq
      linarith
    have hdA := image_div_eq (γ := γ) (φ := φ) hA' (fun s _ => hφlift s)
    have hduniv : (fun x => x / y x) '' A = univ :=
      eq_univ_of_forall fun t => by obtain ⟨x, hx, rfl⟩ := hd t; exact ⟨x, hx, rfl⟩
    refine exp_image_sub_ne_univ hγcont hφc.continuousOn hγmono hmono hG hP.le ?_
    rw [← hdA, hduniv]
  · have hP : φ 0 - φ 1 < 2 * Real.pi := by
      by_contra hcon
      have hcon' : 2 * Real.pi ≤ φ 0 - φ 1 := not_lt.mp hcon
      have hmem : φ 1 + 2 * Real.pi ∈ Icc (φ 1) (φ 0) :=
        ⟨by linarith [Real.two_pi_pos], by linarith⟩
      obtain ⟨s, hsr, hsv⟩ := intermediate_value_Icc' (by norm_num) hφc.continuousOn hmem
      have hs1 : s < 1 := by
        rcases lt_or_eq_of_le hsr.2 with hh | hh
        · exact hh
        · exfalso; rw [hh] at hsv; linarith [Real.two_pi_pos]
      have hy_eq : y (Circle.exp (γ s)) = y (Circle.exp (γ 1)) := by
        rw [← hφlift s, ← hφlift 1, hsv, Circle.exp_add_two_pi]
      have hexp : Circle.exp (γ s) = Circle.exp (γ 1) := hinj (hmemA s) (hmemA 1) hy_eq
      have hγeq : γ s = γ 1 := Circle.exp_injOn_Icc hlt (hγmem s) (hγmem 1) hexp
      have : s = 1 := hγmono.injOn hsr (by norm_num) hγeq
      linarith
    have hsA := image_mul_eq (γ := γ) (φ := φ) hA' (fun s _ => hφlift s)
    have hsuniv : (fun x => x * y x) '' A = univ :=
      eq_univ_of_forall fun t => by obtain ⟨x, hx, rfl⟩ := hs t; exact ⟨x, hx, rfl⟩
    refine exp_image_add_ne_univ hγcont hφc.continuousOn hγmono hanti hG hP.le ?_
    rw [← hsA, hsuniv]

/-- If `f` is continuous on `[0,1]`, injective on `[0,1)` and strictly increasing on `(0,1)`,
then `f 0 < f t` for every `t ∈ (0,1)`. -/
lemma lt_apply_left_of_strictMonoOn_Ioo {f : ℝ → ℝ} (hcont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hinj : InjOn f (Ico (0 : ℝ) 1)) (hmono : StrictMonoOn f (Ioo (0 : ℝ) 1)) :
    ∀ t ∈ Ioo (0 : ℝ) 1, f 0 < f t := by
  intro t ht
  have h0 : (0 : ℝ) ∈ Ico (0 : ℝ) 1 := ⟨le_rfl, by norm_num⟩
  have ht' : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  have hne : f 0 ≠ f t := fun he => absurd (hinj h0 ht' he) (ne_of_gt ht.1).symm
  rcases lt_or_gt_of_ne hne with h | h
  · exact h
  · exfalso
    obtain ⟨z, hz0, hzt⟩ := exists_between ht.1
    have hz : z ∈ Ioo (0 : ℝ) 1 := ⟨hz0, hzt.trans ht.2⟩
    have hzfz : f z < f t := hmono hz ht hzt
    have hmem : f t ∈ Icc (f z) (f 0) := ⟨hzfz.le, h.le⟩
    obtain ⟨w, hwr, hwv⟩ := intermediate_value_Icc' hz0.le
      (hcont.mono (Icc_subset_Icc le_rfl (hzt.trans ht.2).le)) hmem
    have hw : w ∈ Ico (0 : ℝ) 1 := ⟨hwr.1, hwr.2.trans_lt (hzt.trans ht.2)⟩
    have := hinj hw ht' hwv
    linarith [hwr.2, hzt, this]

/-- If `f` is continuous on `[0,1]`, injective on `[0,1)`, strictly increasing on `(0,1)` and
`f` never takes the value `f 1` on `(0,1)`, then `f t < f 1` for every `t ∈ (0,1)`. -/
lemma apply_lt_right_of_strictMonoOn_Ioo {f : ℝ → ℝ} (hcont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hinj : InjOn f (Ico (0 : ℝ) 1)) (hmono : StrictMonoOn f (Ioo (0 : ℝ) 1))
    (hone : ∀ t ∈ Ioo (0 : ℝ) 1, f t ≠ f 1) :
    ∀ t ∈ Ioo (0 : ℝ) 1, f t < f 1 := by
  intro t ht
  have ht' : t ∈ Ico (0 : ℝ) 1 := ⟨ht.1.le, ht.2⟩
  have hne : f t ≠ f 1 := hone t ht
  rcases lt_or_gt_of_ne hne with h | h
  · exact h
  · exfalso
    obtain ⟨z, htz, hz1⟩ := exists_between ht.2
    have hz : z ∈ Ioo (0 : ℝ) 1 := ⟨ht.1.trans htz, hz1⟩
    have hzt : f t < f z := hmono ht hz htz
    have hmem : f t ∈ Icc (f 1) (f z) := ⟨h.le, hzt.le⟩
    obtain ⟨w, hwr, hwv⟩ := intermediate_value_Icc' hz1.le
      (hcont.mono (Icc_subset_Icc (le_of_lt (ht.1.trans htz)) le_rfl)) hmem
    have hw1 : w ≠ 1 := by
      intro hw1
      rw [hw1] at hwv
      exact hne hwv.symm
    have hw : w ∈ Ico (0 : ℝ) 1 :=
      ⟨le_trans ht.1.le (le_trans htz.le hwr.1), lt_of_le_of_ne hwr.2 hw1⟩
    have := hinj hw ht' hwv
    linarith [hwr.1, htz, this]

/-- The antitone version of `lt_apply_left_of_strictMonoOn_Ioo`. -/
lemma lt_apply_left_of_strictAntiOn_Ioo {f : ℝ → ℝ} (hcont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hinj : InjOn f (Ico (0 : ℝ) 1)) (hanti : StrictAntiOn f (Ioo (0 : ℝ) 1)) :
    ∀ t ∈ Ioo (0 : ℝ) 1, f t < f 0 := by
  have hinj' : InjOn (fun s => -f s) (Ico (0 : ℝ) 1) :=
    fun x hx y hy h => hinj hx hy (neg_injective h)
  have h := lt_apply_left_of_strictMonoOn_Ioo (f := fun s => -f s) hcont.neg hinj' hanti.neg
  intro t ht
  have := h t ht
  simpa using this

/-- The antitone version of `apply_lt_right_of_strictMonoOn_Ioo`. -/
lemma apply_lt_right_of_strictAntiOn_Ioo {f : ℝ → ℝ} (hcont : ContinuousOn f (Icc (0 : ℝ) 1))
    (hinj : InjOn f (Ico (0 : ℝ) 1)) (hanti : StrictAntiOn f (Ioo (0 : ℝ) 1))
    (hone : ∀ t ∈ Ioo (0 : ℝ) 1, f t ≠ f 1) :
    ∀ t ∈ Ioo (0 : ℝ) 1, f 1 < f t := by
  have hinj' : InjOn (fun s => -f s) (Ico (0 : ℝ) 1) :=
    fun x hx y hy h => hinj hx hy (neg_injective h)
  have hone' : ∀ t ∈ Ioo (0 : ℝ) 1, (fun s => -f s) t ≠ (fun s => -f s) 1 :=
    fun t ht h => hone t ht (neg_injective h)
  have h := apply_lt_right_of_strictMonoOn_Ioo (f := fun s => -f s) hcont.neg hinj' hanti.neg hone'
  intro t ht
  have := h t ht
  simpa using this

/-- `t ∈ [0,1)` with `Circle.exp (2π t) = 1` forces `t = 0`. -/
lemma eq_zero_of_exp_two_pi_mul_eq_one {t : ℝ} (ht : t ∈ Ico (0 : ℝ) 1)
    (h : Circle.exp (2 * Real.pi * t) = 1) : t = 0 := by
  obtain ⟨j, hj⟩ := Circle.exp_eq_one.mp h
  have ht' : t = (j : ℝ) := by
    rw [mul_comm (2 * Real.pi) t] at hj
    exact mul_right_cancel₀ (ne_of_gt Real.two_pi_pos) hj
  have h3 : (-1 : ℝ) < (j : ℝ) := by rw [← ht']; linarith [ht.1, ht.2]
  have h4 : (j : ℝ) < 1 := by rw [← ht']; linarith [ht.1, ht.2]
  have h5 : (-1 : ℤ) < j := by exact_mod_cast h3
  have h6 : j < (1 : ℤ) := by exact_mod_cast h4
  have hj0 : j = 0 := by omega
  rw [hj0] at ht'
  simpa using ht'

/-- Injectivity of a continuous lift `φ` of `s ↦ y (Circle.exp (2π s))` on `[0,1)`. -/
lemma injOn_Ico_of_lift {y : Circle → Circle} (hinj : Set.InjOn y univ) {φ : ℝ → ℝ}
    (hφ : ∀ s ∈ Icc (0 : ℝ) 1, Circle.exp (φ s) = y (Circle.exp (2 * Real.pi * s))) :
    InjOn φ (Ico (0 : ℝ) 1) := by
  intro s hs t ht hst
  have hss : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1, hs.2.le⟩
  have htt : t ∈ Icc (0 : ℝ) 1 := ⟨ht.1, ht.2.le⟩
  have hy_eq : y (Circle.exp (2 * Real.pi * s)) = y (Circle.exp (2 * Real.pi * t)) := by
    rw [← hφ s hss, ← hφ t htt, hst]
  have hexp : Circle.exp (2 * Real.pi * s) = Circle.exp (2 * Real.pi * t) :=
    hinj (mem_univ _) (mem_univ _) hy_eq
  obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hexp
  have hk' : s - t = (k : ℝ) := by
    have h2 : (2 * Real.pi) * (s - t) = (2 * Real.pi) * (k : ℝ) := by
      have := hk
      ring_nf at this ⊢
      linarith [this]
    exact mul_left_cancel₀ (ne_of_gt Real.two_pi_pos) h2
  have h1 : (-1 : ℝ) < (k : ℝ) := by rw [← hk']; linarith [hs.1, hs.2, ht.1, ht.2]
  have h2 : (k : ℝ) < 1 := by rw [← hk']; linarith [hs.1, hs.2, ht.1, ht.2]
  have h3 : (-1 : ℤ) < k := by exact_mod_cast h1
  have h4 : k < (1 : ℤ) := by exact_mod_cast h2
  have hk0 : k = 0 := by omega
  rw [hk0] at hk'
  simp only [Int.cast_zero] at hk'
  linarith

/-- **Endpoint analysis for the full-circle case.**  A continuous lift `φ` of
`s ↦ y (Circle.exp (2π s))` over `[0,1]`, with `y` injective, is strictly monotone on `[0,1]`,
and its total increment is `±2π` with the sign matching the monotonicity. -/
theorem lift_mono_endpoint {y : Circle → Circle} (hinj : Set.InjOn y univ) {φ : ℝ → ℝ}
    (hφc : Continuous φ)
    (hφ : ∀ s ∈ Icc (0 : ℝ) 1, Circle.exp (φ s) = y (Circle.exp (2 * Real.pi * s))) :
    (StrictMonoOn φ (Icc (0 : ℝ) 1) ∧ φ 1 = φ 0 + 2 * Real.pi) ∨
      (StrictAntiOn φ (Icc (0 : ℝ) 1) ∧ φ 0 = φ 1 + 2 * Real.pi) := by
  have hcont : ContinuousOn φ (Icc (0 : ℝ) 1) := hφc.continuousOn
  have hinjφ : InjOn φ (Ico (0 : ℝ) 1) := injOn_Ico_of_lift hinj hφ
  have hkey : ∀ t : ℝ, t ∈ Ico (0 : ℝ) 1 → Circle.exp (2 * Real.pi * t) = 1 → t = 0 :=
    fun t ht h => eq_zero_of_exp_two_pi_mul_eq_one ht h
  have hEp : Circle.exp (φ 1) = Circle.exp (φ 0) := by
    rw [hφ 1 (by norm_num), hφ 0 (by norm_num)]
    simp [Circle.exp_two_pi]
  obtain ⟨k, hk⟩ : ∃ k : ℤ, φ 1 - φ 0 = (k : ℝ) * (2 * Real.pi) := by
    obtain ⟨k, hk⟩ := Circle.exp_eq_exp.mp hEp
    exact ⟨k, by linarith⟩
  have hcontIoo : ContinuousOn φ (Ioo (0 : ℝ) 1) :=
    hcont.mono Ioo_subset_Icc_self
  rcases hcontIoo.strictMonoOn_of_injOn_Ioo (by norm_num) (hinjφ.mono Ioo_subset_Ico_self) with
    hmono | hanti
  · -- increasing case
    have hone : ∀ t ∈ Ioo (0 : ℝ) 1, φ t ≠ φ 1 := by
      intro t ht he
      have hy : y (Circle.exp (2 * Real.pi * t)) = y (Circle.exp (2 * Real.pi * 1)) := by
        rw [← hφ t ⟨ht.1.le, ht.2.le⟩, ← hφ 1 (by norm_num), he]
      have h2 : Circle.exp (2 * Real.pi * t) = Circle.exp (2 * Real.pi * 1) :=
        hinj (mem_univ _) (mem_univ _) hy
      have h2' : Circle.exp (2 * Real.pi * t) = 1 := by
        rw [h2]; simp [Circle.exp_two_pi]
      exact (ne_of_gt ht.1) (hkey t ⟨ht.1.le, ht.2⟩ h2')
    have hlt0 : ∀ t ∈ Ioo (0 : ℝ) 1, φ 0 < φ t :=
      fun t ht => lt_apply_left_of_strictMonoOn_Ioo hcont hinjφ hmono t ht
    have hlt1 : ∀ t ∈ Ioo (0 : ℝ) 1, φ t < φ 1 :=
      fun t ht => apply_lt_right_of_strictMonoOn_Ioo hcont hinjφ hmono hone t ht
    have h01 : φ 0 < φ 1 := by
      have h1 := hlt0 (1 / 2) (by norm_num)
      have h2 := hlt1 (1 / 2) (by norm_num)
      linarith
    have hstrict : StrictMonoOn φ (Icc (0 : ℝ) 1) := by
      intro a ha b hb hab
      by_cases ha0 : a = 0
      · subst ha0
        by_cases hb1 : b = 1
        · subst hb1; exact h01
        · exact hlt0 b ⟨hab, lt_of_le_of_ne hb.2 hb1⟩
      · by_cases hb1 : b = 1
        · subst hb1
          exact hlt1 a ⟨lt_of_le_of_ne ha.1 (Ne.symm ha0), hab⟩
        · exact hmono ⟨lt_of_le_of_ne ha.1 (Ne.symm ha0), lt_of_lt_of_le hab hb.2⟩
            ⟨lt_of_lt_of_le (lt_of_le_of_ne ha.1 (Ne.symm ha0)) hab.le, lt_of_le_of_ne hb.2 hb1⟩
            hab
    refine Or.inl ⟨hstrict, ?_⟩
    have hkpos : (0 : ℤ) < k := by
      have h : 0 < (k : ℝ) * (2 * Real.pi) := by rw [← hk]; linarith
      have : 0 < (k : ℝ) := pos_of_mul_pos_left h (le_of_lt Real.two_pi_pos)
      exact_mod_cast this
    have hk2 : k ≤ 1 := by
      by_contra hcon
      have hcon' : (2 : ℤ) ≤ k := by omega
      have hbig : 4 * Real.pi ≤ φ 1 - φ 0 := by
        have hc : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hcon'
        rw [hk]; nlinarith [Real.two_pi_pos]
      have hmem : φ 0 + 2 * Real.pi ∈ Icc (φ 0) (φ 1) :=
        ⟨by linarith [Real.two_pi_pos], by linarith⟩
      obtain ⟨t, htr, htv⟩ := intermediate_value_Icc (by norm_num) hcont hmem
      have ht0 : t ≠ 0 := by
        intro hh; rw [hh] at htv; linarith [Real.two_pi_pos]
      have ht1lt : t < 1 := by
        rcases lt_or_eq_of_le htr.2 with hh | hh
        · exact hh
        · exfalso; rw [hh] at htv; linarith
      have htmem : t ∈ Ico (0 : ℝ) 1 := ⟨htr.1, ht1lt⟩
      have hexp1 : Circle.exp (2 * Real.pi * t) = 1 := by
        have hy : y (Circle.exp (2 * Real.pi * t)) = y 1 := by
          rw [← hφ t htr, htv, Circle.exp_add_two_pi, hφ 0 (by norm_num)]
          simp
        have := hinj (mem_univ _) (mem_univ _) hy
        simpa using this
      exact ht0 (hkey t htmem hexp1)
    have hk1 : k = 1 := by omega
    rw [hk1] at hk
    norm_num at hk
    linarith
  · -- decreasing case
    have hone : ∀ t ∈ Ioo (0 : ℝ) 1, φ t ≠ φ 1 := by
      intro t ht he
      have hy : y (Circle.exp (2 * Real.pi * t)) = y (Circle.exp (2 * Real.pi * 1)) := by
        rw [← hφ t ⟨ht.1.le, ht.2.le⟩, ← hφ 1 (by norm_num), he]
      have h2 : Circle.exp (2 * Real.pi * t) = Circle.exp (2 * Real.pi * 1) :=
        hinj (mem_univ _) (mem_univ _) hy
      have h2' : Circle.exp (2 * Real.pi * t) = 1 := by
        rw [h2]; simp [Circle.exp_two_pi]
      exact (ne_of_gt ht.1) (hkey t ⟨ht.1.le, ht.2⟩ h2')
    have hlt0 : ∀ t ∈ Ioo (0 : ℝ) 1, φ t < φ 0 :=
      fun t ht => lt_apply_left_of_strictAntiOn_Ioo hcont hinjφ hanti t ht
    have hlt1 : ∀ t ∈ Ioo (0 : ℝ) 1, φ 1 < φ t :=
      fun t ht => apply_lt_right_of_strictAntiOn_Ioo hcont hinjφ hanti hone t ht
    have h10 : φ 1 < φ 0 := by
      have h1 := hlt0 (1 / 2) (by norm_num)
      have h2 := hlt1 (1 / 2) (by norm_num)
      linarith
    have hstrict : StrictAntiOn φ (Icc (0 : ℝ) 1) := by
      intro a ha b hb hab
      by_cases ha0 : a = 0
      · subst ha0
        by_cases hb1 : b = 1
        · subst hb1; exact h10
        · exact hlt0 b ⟨hab, lt_of_le_of_ne hb.2 hb1⟩
      · by_cases hb1 : b = 1
        · subst hb1
          exact hlt1 a ⟨lt_of_le_of_ne ha.1 (Ne.symm ha0), hab⟩
        · exact hanti ⟨lt_of_le_of_ne ha.1 (Ne.symm ha0), lt_of_lt_of_le hab hb.2⟩
            ⟨lt_of_lt_of_le (lt_of_le_of_ne ha.1 (Ne.symm ha0)) hab.le, lt_of_le_of_ne hb.2 hb1⟩
            hab
    refine Or.inr ⟨hstrict, ?_⟩
    have hkneg : k < 0 := by
      have h : (k : ℝ) * (2 * Real.pi) < 0 := by rw [← hk]; linarith
      have : (k : ℝ) < 0 := by
        by_contra hcon
        have hcon' : 0 ≤ (k : ℝ) := not_lt.mp hcon
        nlinarith [Real.two_pi_pos, h]
      exact_mod_cast this
    have hk1 : (-1 : ℤ) ≤ k := by
      by_contra hcon
      have hcon' : k ≤ -2 := by omega
      have hbig : φ 1 - φ 0 ≤ -4 * Real.pi := by
        have hc : (k : ℝ) ≤ -2 := by exact_mod_cast hcon'
        rw [hk]; nlinarith [Real.two_pi_pos]
      have hmem : φ 0 - 2 * Real.pi ∈ Icc (φ 1) (φ 0) :=
        ⟨by linarith, by linarith [Real.two_pi_pos]⟩
      obtain ⟨t, htr, htv⟩ := intermediate_value_Icc' (by norm_num) hcont hmem
      have ht0 : t ≠ 0 := by
        intro hh; rw [hh] at htv; linarith [Real.two_pi_pos]
      have ht1lt : t < 1 := by
        rcases lt_or_eq_of_le htr.2 with hh | hh
        · exact hh
        · exfalso; rw [hh] at htv; linarith [hk, Real.two_pi_pos]
      have htmem : t ∈ Ico (0 : ℝ) 1 := ⟨htr.1, ht1lt⟩
      have hexp1 : Circle.exp (2 * Real.pi * t) = 1 := by
        have hy : y (Circle.exp (2 * Real.pi * t)) = y 1 := by
          rw [← hφ t htr, htv, Circle.exp_sub_two_pi, hφ 0 (by norm_num)]
          simp
        have := hinj (mem_univ _) (mem_univ _) hy
        simpa using this
      exact ht0 (hkey t htmem hexp1)
    have hk1' : k = -1 := by omega
    rw [hk1'] at hk
    norm_num at hk
    linarith

/-! ## The full circle case -/

theorem not_both_surj_of_eq {A : Set Circle} {y : Circle → Circle} (hy : ContinuousOn y A)
    (hinj : Set.InjOn y A) {α β : ℝ} (hαβ : α < β) (heq : β - α = 2 * Real.pi)
    (hcover : A = Circle.exp '' Icc α β) :
    ¬ ((∀ t : Circle, ∃ x ∈ A, t = x / y x) ∧ (∀ t : Circle, ∃ x ∈ A, t = x * y x)) := by
  rintro ⟨hd, hs⟩
  have hAuniv : A = univ := by
    rw [hcover, show β = α + 2 * Real.pi by linarith,
      Circle.periodic_exp.image_Icc (c := 2 * Real.pi) Real.two_pi_pos (a := α),
      Circle.exp_surjective.range_eq]
  have hinj' : Set.InjOn y univ := by simpa [hAuniv] using hinj
  set γ : ℝ → ℝ := fun s => 2 * Real.pi * clamp01 s with hγdef
  have hγc : Continuous γ := by
    rw [hγdef]
    exact continuous_const.mul clamp01_continuous
  have hγlin : ∀ s ∈ Icc (0 : ℝ) 1, γ s = 2 * Real.pi * s := by
    intro s hs
    rw [hγdef]
    simp only [clamp01_of_mem hs]
  have hγcont : ContinuousOn γ (Icc (0 : ℝ) 1) := hγc.continuousOn
  have hγmono : StrictMonoOn γ (Icc (0 : ℝ) 1) := by
    intro x hx t ht hxt
    rw [hγlin x hx, hγlin t ht]
    nlinarith [Real.two_pi_pos]
  have hγ0 : γ 0 = 0 := by rw [hγlin 0 (by norm_num)]; ring
  have hγ1 : γ 1 = 2 * Real.pi := by rw [hγlin 1 (by norm_num)]; ring
  have hG : γ 1 - γ 0 ≤ 2 * Real.pi := by rw [hγ1, hγ0]; linarith
  have hγimg : γ '' Icc (0 : ℝ) 1 = Icc (0 : ℝ) (2 * Real.pi) := by
    rw [hγcont.image_Icc_of_monotoneOn (by norm_num) hγmono.monotoneOn, hγ0, hγ1]
  have hmemA : ∀ s : ℝ, Circle.exp (γ s) ∈ A := by
    intro s; rw [hAuniv]; trivial
  have hg : Continuous fun s : ℝ => y (Circle.exp (γ s)) :=
    hy.comp_continuous (Circle.exp.continuous.comp hγc) hmemA
  obtain ⟨φ, hφc, hφlift⟩ := exists_continuous_lift hg
  have hφlin : ∀ s ∈ Icc (0 : ℝ) 1, Circle.exp (φ s) = y (Circle.exp (2 * Real.pi * s)) := by
    intro s hs
    rw [hφlift s, hγlin s hs]
  have hend : (StrictMonoOn φ (Icc (0 : ℝ) 1) ∧ φ 1 = φ 0 + 2 * Real.pi) ∨
      (StrictAntiOn φ (Icc (0 : ℝ) 1) ∧ φ 0 = φ 1 + 2 * Real.pi) :=
    lift_mono_endpoint hinj' hφc hφlin
  have hsurj : Circle.exp '' Icc (0 : ℝ) (2 * Real.pi) = univ := by
    have h := Circle.periodic_exp.image_Icc (c := 2 * Real.pi) Real.two_pi_pos (a := (0 : ℝ))
    rw [zero_add] at h
    rw [h, Circle.exp_surjective.range_eq]
  have hA' : A = Circle.exp '' (γ '' Icc (0 : ℝ) 1) := by
    rw [hγimg, hsurj, hAuniv]
  rcases hend with ⟨hmono, hPeq⟩ | ⟨hanti, hPeq⟩
  · have hdA := image_div_eq (γ := γ) (φ := φ) hA' (fun s _ => hφlift s)
    have hduniv : (fun x => x / y x) '' A = univ :=
      eq_univ_of_forall fun t => by obtain ⟨x, hx, rfl⟩ := hd t; exact ⟨x, hx, rfl⟩
    have hP : φ 1 - φ 0 ≤ 2 * Real.pi := by
      have : φ 1 - φ 0 = 2 * Real.pi := by rw [hPeq]; ring
      rw [this]
    refine exp_image_sub_ne_univ hγcont hφc.continuousOn hγmono hmono hG hP ?_
    rw [← hdA, hduniv]
  · have hsA := image_mul_eq (γ := γ) (φ := φ) hA' (fun s _ => hφlift s)
    have hsuniv : (fun x => x * y x) '' A = univ :=
      eq_univ_of_forall fun t => by obtain ⟨x, hx, rfl⟩ := hs t; exact ⟨x, hx, rfl⟩
    have hP : φ 0 - φ 1 ≤ 2 * Real.pi := by
      have : φ 0 - φ 1 = 2 * Real.pi := by rw [hPeq]; ring
      rw [this]
    refine exp_image_add_ne_univ hγcont hφc.continuousOn hγmono hanti hG hP ?_
    rw [← hsA, hsuniv]

/-! ## The theorem -/

theorem arcRigidity {A : Set Circle} (hclosed : IsClosed A) (hconn : IsConnected A)
    (hint : ∃ z, z ∈ interior A) {y : Circle → Circle} (hy : ContinuousOn y A)
    (hinj : Set.InjOn y A) :
    ¬ ((∀ t : Circle, ∃ x ∈ A, t = x / y x) ∧ (∀ t : Circle, ∃ x ∈ A, t = x * y x)) := by
  obtain ⟨α, β, hαβ, hG, hcover⟩ := exists_exp_Icc_cover hclosed hconn hint
  rcases lt_or_eq_of_le hG with hlt | heq
  · exact not_both_surj_of_lt hy hinj hαβ hlt hcover
  · exact not_both_surj_of_eq hy hinj hαβ heq hcover

end

end Work.Drive.N2
