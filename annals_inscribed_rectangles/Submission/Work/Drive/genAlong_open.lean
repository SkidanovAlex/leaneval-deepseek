import Mathlib
import Submission.Work.Drive.genFunctionalStable

/-!
# The set of functionals generic along a smooth curve is open

`Work.Drive.GenAlong ℓ V` says that the functional `ℓ` does not vanish at the initial parameter
of the (smooth) curve `V : ℝ → Eucl 3` and that its zero set on `[0,1]` is finite with all zeros
simple.  This file proves that the class of such functionals is **open**: `genAlong_open`.

The proof is the standard one-sided stability argument.  Since the zeros of `f := ℓ ∘ V` on `[0,1]`
are finite and simple, each of them has a neighbourhood on which `|deriv f|` is bounded below by a
positive constant `Q z`, and `|f|` is bounded below by a positive constant `c` away from (a union of
such neighbourhoods of) the zeros (compactness of `[0,1]`).  Any `ℓ'` with `‖ℓ' - ℓ‖` small enough
then has `ℓ' ∘ V` uniformly close to `ℓ ∘ V` (with constant `‖ℓ' - ℓ‖ · sup ‖V‖`) as well as
`deriv (ℓ' ∘ V) = ℓ' ∘ deriv V` uniformly close to `deriv (ℓ ∘ V)` (with constant
`‖ℓ' - ℓ‖ · sup ‖deriv V‖`); hence the zeros of `ℓ' ∘ V` on `[0,1]` all lie in the small
neighbourhoods of the zeros of `f`, at most one in each of them (by the mean value theorem, since
`deriv (ℓ' ∘ V)` has no zero there), and each of them is simple.
-/

namespace Work.Drive

open Set

theorem genAlong_open {V : ℝ → Eucl 3} (hVs : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) V)
    {ℓ : Eucl 3 →L[ℝ] ℝ} (hℓ : Work.Drive.GenAlong ℓ V) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ℓ' : Eucl 3 →L[ℝ] ℝ, ‖ℓ' - ℓ‖ < δ → Work.Drive.GenAlong ℓ' V := by
  obtain ⟨h0, hfin, hreg⟩ := hℓ
  set f : ℝ → ℝ := fun t => ℓ (V t)
  have hVdiff : Differentiable ℝ V := hVs.differentiable (by simp)
  have hfdiff : ∀ t : ℝ, HasDerivAt f (ℓ (deriv V t)) t := fun t =>
    (ContinuousLinearMap.hasFDerivAt ℓ).comp_hasDerivAt t ((hVdiff t).hasDerivAt)
  have hderivf : ∀ t : ℝ, deriv f t = ℓ (deriv V t) := fun t => (hfdiff t).deriv
  have hfcont : Continuous f := ℓ.continuous.comp hVs.continuous
  have hderivcont : Continuous (deriv f) := by
    have heq : deriv f = fun t => ℓ (deriv V t) := funext hderivf
    rw [heq]
    exact ℓ.continuous.comp (hVs.continuous_deriv (by simp))
  -- uniform bounds on `V` and on `deriv V` over `[0,1]`
  obtain ⟨C₁, hC₁⟩ := isCompact_Icc.exists_bound_of_continuousOn hVs.continuous.continuousOn
  set M : ℝ := max C₁ 0
  have hM0 : 0 ≤ M := le_max_right _ _
  have hM : ∀ t ∈ Icc (0:ℝ) 1, ‖V t‖ ≤ M := fun t ht => le_trans (hC₁ t ht) (le_max_left _ _)
  obtain ⟨C₂, hC₂⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hVs.continuous_deriv (by simp)).continuousOn
  set Md : ℝ := max C₂ 0
  have hMd0 : 0 ≤ Md := le_max_right _ _
  have hMd : ∀ t ∈ Icc (0:ℝ) 1, ‖deriv V t‖ ≤ Md := fun t ht => le_trans (hC₂ t ht) (le_max_left _ _)
  -- the (finite) zero set of `f` on `[0,1]`, as a `Finset`
  set Z : Set ℝ := {t : ℝ | t ∈ Icc (0:ℝ) 1 ∧ f t = 0}
  have hfinZ : Z.Finite := hfin
  set s : Finset ℝ := hfinZ.toFinset
  have hmem : ∀ t : ℝ, t ∈ s ↔ t ∈ Z := fun t => hfinZ.mem_toFinset
  -- around every zero of `f` there is an interval on which `|deriv f|` is bounded below by a
  -- positive constant
  have hRlocal : ∀ z ∈ s, ∃ p : ℝ × ℝ, 0 < p.1 ∧ 0 < p.2 ∧
      ∀ t ∈ Icc (z - p.1) (z + p.1) ∩ Icc (0:ℝ) 1, p.2 ≤ |deriv f t| := by
    intro z hz
    obtain ⟨hz01, hz0⟩ := (hmem z).mp hz
    have hregz : deriv f z ≠ 0 := hreg z hz01 hz0
    obtain ⟨η, hηpos, hη⟩ :=
      Metric.continuousAt_iff.mp hderivcont.continuousAt (|deriv f z| / 2) (by positivity)
    refine ⟨(η / 2, |deriv f z| / 2), by linarith, by positivity, ?_⟩
    intro t ht
    have htz : dist t z < η := by
      rw [Real.dist_eq]
      have h2 : |t - z| ≤ η / 2 := by
        rw [abs_le]
        exact ⟨by linarith [ht.1.1], by linarith [ht.1.2]⟩
      linarith
    have h3 := hη htz
    rw [Real.dist_eq] at h3
    have htri : |deriv f z| ≤ |deriv f t| + |deriv f z - deriv f t| := by
      have h4 : deriv f z = deriv f t + (deriv f z - deriv f t) := by ring
      calc |deriv f z| = |deriv f t + (deriv f z - deriv f t)| := congrArg abs h4
        _ ≤ |deriv f t| + |deriv f z - deriv f t| := abs_add_le _ _
    rw [abs_sub_comm (deriv f z) (deriv f t)] at htri
    linarith
  set R : ℝ → ℝ := (fun z => if h : z ∈ s then (hRlocal z h).choose.1 else 1) with hR
  set Q : ℝ → ℝ := (fun z => if h : z ∈ s then (hRlocal z h).choose.2 else 1) with hQ
  have hRpos : ∀ z ∈ s, 0 < R z := fun z hz => by
    rw [hR]; simp only [dif_pos hz]; exact (hRlocal z hz).choose_spec.1
  have hQpos : ∀ z ∈ s, 0 < Q z := fun z hz => by
    rw [hQ]; simp only [dif_pos hz]; exact (hRlocal z hz).choose_spec.2.1
  have hRQ : ∀ z ∈ s, ∀ t ∈ Icc (z - R z) (z + R z) ∩ Icc (0:ℝ) 1, Q z ≤ |deriv f t| := by
    intro z hz t ht
    have hRz : R z = (hRlocal z hz).choose.1 := by rw [hR]; simp only [dif_pos hz]
    have hQz : Q z = (hRlocal z hz).choose.2 := by rw [hQ]; simp only [dif_pos hz]
    rw [hRz] at ht
    rw [hQz]
    exact (hRlocal z hz).choose_spec.2.2 t ht
  -- the uniform lower bound on `|deriv f|` at the zeros
  set m : ℝ := (if h : s.Nonempty then s.inf' h Q else 1) with hm
  have hmpos : 0 < m := by
    by_cases h : s.Nonempty
    · rw [hm]; simp only [dif_pos h]
      exact (Finset.lt_inf'_iff h).mpr (fun i hi => hQpos i hi)
    · rw [hm]; simp only [dif_neg h]; norm_num
  have hmle : ∀ z ∈ s, m ≤ Q z := by
    intro z hz
    by_cases h : s.Nonempty
    · rw [hm]; simp only [dif_pos h]
      exact Finset.inf'_le Q hz
    · exact absurd ⟨z, hz⟩ h
  -- the union of the intervals around the zeros
  set U : Set ℝ := ⋃ z ∈ (s : Set ℝ), Ioo (z - R z) (z + R z) with hU
  have hUopen : IsOpen U := by
    rw [hU]
    exact isOpen_iUnion fun z => isOpen_iUnion fun _ => isOpen_Ioo
  have hU_of_zero : ∀ t ∈ Icc (0:ℝ) 1, f t = 0 → t ∈ U := by
    intro t ht hft
    have hts : t ∈ s := (hmem t).mpr ⟨ht, hft⟩
    rw [hU]
    refine Set.mem_iUnion₂.mpr ⟨t, by simpa using hts, ?_⟩
    have hp := hRpos t hts
    exact ⟨by linarith, by linarith⟩
  -- `|f|` is bounded below away from `U`
  have hc : ∃ c : ℝ, 0 < c ∧ ∀ t ∈ Icc (0:ℝ) 1, t ∉ U → c ≤ |f t| := by
    by_cases hL : (Icc (0:ℝ) 1 \ U).Nonempty
    · obtain ⟨x, hx, hxmin⟩ := (isCompact_Icc.diff hUopen).exists_isMinOn hL hfcont.abs.continuousOn
      refine ⟨|f x|, abs_pos.mpr (fun hfx => hx.2 (hU_of_zero x hx.1 hfx)),
        fun t ht htnU => hxmin ⟨ht, htnU⟩⟩
    · exact ⟨1, one_pos, fun t ht htnU => absurd ⟨t, ht, htnU⟩ hL⟩
  obtain ⟨c, hcpos, hc'⟩ := hc
  have hkey : ∀ {X B D : ℝ}, 0 < D → 0 ≤ B → X < D / (B + 1) → X * B < D := by
    intro X B D hD hB hX
    rcases eq_or_lt_of_le hB with hB0 | hBpos
    · rw [← hB0, mul_zero]; exact hD
    · have hB1 : (0:ℝ) < B + 1 := by linarith
      calc X * B < (D / (B + 1)) * B := mul_lt_mul_of_pos_right hX hBpos
        _ ≤ (D / (B + 1)) * (B + 1) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith
        _ = D := by field_simp
  refine ⟨min ((|f 0| / 2) / (M + 1)) (min (c / (M + 1)) ((m / 2) / (Md + 1))), ?_, ?_⟩
  · exact lt_min (div_pos (div_pos (abs_pos.mpr h0) two_pos) (by linarith))
      (lt_min (div_pos hcpos (by linarith)) (div_pos (div_pos hmpos two_pos) (by linarith)))
  · intro ℓ' hδ
    set g : ℝ → ℝ := fun t => ℓ' (V t)
    have hgd : ∀ t : ℝ, HasDerivAt g (ℓ' (deriv V t)) t := fun t =>
      (ContinuousLinearMap.hasFDerivAt ℓ').comp_hasDerivAt t ((hVdiff t).hasDerivAt)
    have hgderiv : ∀ t : ℝ, deriv g t = ℓ' (deriv V t) := fun t => (hgd t).deriv
    have hgcont : Continuous g := ℓ'.continuous.comp hVs.continuous
    have hgdiff : Differentiable ℝ g := fun x => (hgd x).differentiableAt
    set Z' : Set ℝ := {t : ℝ | t ∈ Icc (0:ℝ) 1 ∧ g t = 0}
    have hδ1 : ‖ℓ' - ℓ‖ < (|f 0| / 2) / (M + 1) := lt_of_lt_of_le hδ (min_le_left _ _)
    have hδ2 : ‖ℓ' - ℓ‖ < c / (M + 1) :=
      lt_of_lt_of_le hδ (le_trans (min_le_right _ _) (min_le_left _ _))
    have hδ3 : ‖ℓ' - ℓ‖ < (m / 2) / (Md + 1) :=
      lt_of_lt_of_le hδ (le_trans (min_le_right _ _) (min_le_right _ _))
    have hclose : ∀ t ∈ Icc (0:ℝ) 1, |g t - f t| ≤ ‖ℓ' - ℓ‖ * M := by
      intro t ht
      have h1 : g t - f t = (ℓ' - ℓ) (V t) := by rw [sub_apply]
      calc |g t - f t| = |(ℓ' - ℓ) (V t)| := by rw [h1]
        _ = ‖(ℓ' - ℓ) (V t)‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖ℓ' - ℓ‖ * ‖V t‖ := (ℓ' - ℓ).le_opNorm (V t)
        _ ≤ ‖ℓ' - ℓ‖ * M := mul_le_mul_of_nonneg_left (hM t ht) (norm_nonneg _)
    have hclosederiv : ∀ u ∈ Icc (0:ℝ) 1, |deriv g u - deriv f u| ≤ ‖ℓ' - ℓ‖ * Md := by
      intro u hu
      have h1 : deriv g u - deriv f u = (ℓ' - ℓ) (deriv V u) := by
        rw [hgderiv, hderivf, sub_apply]
      calc |deriv g u - deriv f u| = |(ℓ' - ℓ) (deriv V u)| := by rw [h1]
        _ = ‖(ℓ' - ℓ) (deriv V u)‖ := by rw [Real.norm_eq_abs]
        _ ≤ ‖ℓ' - ℓ‖ * ‖deriv V u‖ := (ℓ' - ℓ).le_opNorm _
        _ ≤ ‖ℓ' - ℓ‖ * Md := mul_le_mul_of_nonneg_left (hMd u hu) (norm_nonneg _)
    have hg0 : g 0 ≠ 0 := by
      have h2 : |f 0| / 2 < |g 0| := by
        have h3 := abs_sub_abs_le_abs_sub (f 0) (g 0)
        rw [abs_sub_comm (f 0) (g 0)] at h3
        have h4 := hkey (div_pos (abs_pos.mpr h0) two_pos) hM0 hδ1
        have h5 := hclose 0 (by norm_num)
        linarith
      intro hh
      rw [hh, abs_zero] at h2
      linarith [abs_pos.mpr h0]
    -- the zeros of `g` on `[0,1]` are locally unique
    have hsubz : ∀ z ∈ (s : Set ℝ), (Z' ∩ Ioo (z - R z) (z + R z)).Subsingleton := by
      intro z hzs
      have hzs' : z ∈ s := hzs
      have hderivg : ∀ u ∈ Ioo (max (z - R z) 0) (min (z + R z) 1), deriv g u ≠ 0 := by
        intro u hu
        have huU : u ∈ Ioo (z - R z) (z + R z) :=
          ⟨lt_of_le_of_lt (le_max_left _ _) hu.1, lt_of_lt_of_le hu.2 (min_le_left _ _)⟩
        have hu01 : u ∈ Icc (0:ℝ) 1 :=
          ⟨le_of_lt (lt_of_le_of_lt (le_max_right _ _) hu.1),
            le_of_lt (lt_of_lt_of_le hu.2 (min_le_right _ _))⟩
        have hfu : m ≤ |deriv f u| :=
          le_trans (hmle z hzs') (hRQ z hzs' u ⟨⟨le_of_lt huU.1, le_of_lt huU.2⟩, hu01⟩)
        have hdu : |deriv g u - deriv f u| < m / 2 := by
          have h5 := hclosederiv u hu01
          have h6 := hkey (div_pos hmpos two_pos) hMd0 hδ3
          linarith
        have h8 : m / 2 < |deriv g u| := by
          have h7 := abs_sub_abs_le_abs_sub (deriv f u) (deriv g u)
          rw [abs_sub_comm (deriv f u) (deriv g u)] at h7
          linarith
        intro hzero
        rw [hzero, abs_zero] at h8
        linarith [hmpos]
      intro t ht t' ht'
      have hmemt : t ∈ Icc (max (z - R z) 0) (min (z + R z) 1) :=
        ⟨max_le (le_of_lt ht.2.1) ht.1.1.1, le_min (le_of_lt ht.2.2) ht.1.1.2⟩
      have hmemt' : t' ∈ Icc (max (z - R z) 0) (min (z + R z) 1) :=
        ⟨max_le (le_of_lt ht'.2.1) ht'.1.1.1, le_min (le_of_lt ht'.2.2) ht'.1.1.2⟩
      have heq : g t = g t' := by rw [ht.1.2, ht'.1.2]
      rcases le_total t t' with hle | hle
      · rcases lt_or_eq_of_le hle with hlt | heq'
        · obtain ⟨cc, hcc, hccd⟩ := exists_deriv_eq_slope g hlt hgcont.continuousOn
            hgdiff.differentiableOn
          have hcz : deriv g cc = 0 := by rw [hccd, heq, sub_self, zero_div]
          exact absurd hcz (hderivg cc ⟨lt_of_le_of_lt hmemt.1 hcc.1, lt_of_lt_of_le hcc.2 hmemt'.2⟩)
        · exact heq'
      · rcases lt_or_eq_of_le hle with hlt | heq'
        · obtain ⟨cc, hcc, hccd⟩ := exists_deriv_eq_slope g hlt hgcont.continuousOn
            hgdiff.differentiableOn
          have hcz : deriv g cc = 0 := by rw [hccd, heq, sub_self, zero_div]
          exact absurd hcz (hderivg cc ⟨lt_of_le_of_lt hmemt'.1 hcc.1, lt_of_lt_of_le hcc.2 hmemt.2⟩)
        · exact heq'.symm
    have hZ'sub : Z' ⊆ ⋃ z ∈ (s : Set ℝ), (Z' ∩ Ioo (z - R z) (z + R z)) := by
      intro t ht
      have hex : ∃ z ∈ s, t ∈ Ioo (z - R z) (z + R z) := by
        by_contra hcon
        have htnU : t ∉ U := by
          rw [hU]
          intro hmem'
          obtain ⟨z, hzs, hzt⟩ := Set.mem_iUnion₂.mp hmem'
          exact hcon ⟨z, hzs, hzt⟩
        have hc't := hc' t ht.1 htnU
        have h5 : |f t| < c := by
          have h6 : |f t| = |g t - f t| := by rw [ht.2, zero_sub, abs_neg]
          have h7 := hclose t ht.1
          have h8 := hkey hcpos hM0 hδ2
          rw [h6]; linarith
        linarith
      obtain ⟨z, hzs, hzt⟩ := hex
      exact Set.mem_iUnion₂.mpr ⟨z, hzs, ht, hzt⟩
    have hZ'fin : Z'.Finite :=
      (Finset.finite_toSet s |>.biUnion (fun z hz => (hsubz z hz).finite)).subset hZ'sub
    have hreg' : ∀ t ∈ Icc (0:ℝ) 1, g t = 0 → deriv g t ≠ 0 := by
      intro t ht hgt
      have htU : t ∈ U := by
        by_contra htnU
        have hc't := hc' t ht htnU
        have h6 : |f t| = |g t - f t| := by rw [hgt, zero_sub, abs_neg]
        have h7 := hclose t ht
        have h8 := hkey hcpos hM0 hδ2
        rw [h6] at hc't
        linarith
      rw [hU] at htU
      obtain ⟨z, hzs, hzt⟩ := Set.mem_iUnion₂.mp htU
      have hzs' : z ∈ s := hzs
      have hfu : m ≤ |deriv f t| :=
        le_trans (hmle z hzs') (hRQ z hzs' t ⟨⟨le_of_lt hzt.1, le_of_lt hzt.2⟩, ht⟩)
      have hdu : |deriv g t - deriv f t| < m / 2 := by
        have h5 := hclosederiv t ht
        have h6 := hkey (div_pos hmpos two_pos) hMd0 hδ3
        linarith
      have h8 : m / 2 < |deriv g t| := by
        have h7 := abs_sub_abs_le_abs_sub (deriv f t) (deriv g t)
        rw [abs_sub_comm (deriv f t) (deriv g t)] at h7
        linarith
      intro hzero
      rw [hzero, abs_zero] at h8
      linarith [hmpos]
    exact ⟨hg0, hZ'fin, hreg'⟩

end Work.Drive
