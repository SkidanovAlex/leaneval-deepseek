import Mathlib

namespace Work.RPB1a.Caratheodory.Maehara

open Set Real

/-- If `m * c` (as a real) has absolute value strictly less than `c` for a positive real `c`, then
the integer `m` is zero. -/
private lemma int_cast_eq_zero_of_abs_mul_lt {m : ℤ} {c : ℝ} (hc : 0 < c)
    (h : |(m:ℝ) * c| < c) : m = 0 := by
  have h1 : |(m:ℝ)| * c < c := by
    have := h
    rwa [abs_mul, abs_of_pos hc] at this
  have h2 : |(m:ℝ)| < 1 := lt_of_mul_lt_mul_right (by simpa using h1) hc.le
  have h2' : |m| < (1:ℤ) := by exact_mod_cast h2
  exact Int.abs_lt_one_iff.mp h2'

/-- Comparison of integers through multiplication by a positive real: `p * c ≤ q * c` (in `ℝ`)
holds exactly when `p ≤ q`. -/
private lemma int_mul_le_int_mul_iff {p q : ℤ} {c : ℝ} (hc : 0 < c) :
    (p:ℝ) * c ≤ (q:ℝ) * c ↔ p ≤ q := by
  constructor
  · intro h
    have h1 : (0:ℝ) ≤ ((q:ℝ) - p) * c := by nlinarith
    have h2 : (0:ℝ) ≤ (q:ℝ) - p := nonneg_of_mul_nonneg_left h1 hc
    have h3 : (p:ℝ) ≤ (q:ℝ) := by linarith
    exact_mod_cast h3
  · intro h
    have h3 : (p:ℝ) ≤ (q:ℝ) := by exact_mod_cast h
    exact mul_le_mul_of_nonneg_right h3 hc.le

/-- **The circle between two points is the union of two arcs.**  Let `γ : Circle → X` be continuous
and injective, and let `za ≠ zb` be two points of the circle.  Then the image of `γ` is the union of
two "arcs" `pc '' [0,1]` and `pd '' [0,1]`, each parametrised by a continuous map from `[0,1]`
taking `0` to `γ za` and `1` to `γ zb`, each injective on `[0,1]`, and the two arcs meet exactly in
the two endpoints.

Route.  Choose `θ : ℝ` with `Circle.exp θ = za`, and put `u t = γ (Circle.exp (θ + t))`; this is
`2π`-periodic and `u 0 = γ za`.  Since `zb ≠ za`, there is a unique `β ∈ (0, 2π)` with `u β = γ zb`.
Take `pc s = u (s * β)` and `pd s = u (2π - s * (2π - β))`.
Use `Circle.exp_surjective`, `Circle.periodic_exp` (`Function.Periodic.exists_mem_Ico`),
`Circle.exp_eq_exp` (`Circle.exp x = Circle.exp y ↔ ∃ m : ℤ, x = y + m * (2 * π)`),
`Circle.exp_sub_two_pi` and `Circle.exp_add_two_pi`. -/
theorem circle_two_arcs {X : Type*} [TopologicalSpace X] (γ : Circle → X) (hγ : Continuous γ)
    (hinj : Function.Injective γ) {za zb : Circle} (hne : za ≠ zb) :
    ∃ pc pd : ℝ → X, Continuous pc ∧ Continuous pd ∧
      pc 0 = γ za ∧ pc 1 = γ zb ∧ pd 0 = γ za ∧ pd 1 = γ zb ∧
      (∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, pc s = pc t → s = t) ∧
      (∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, pd s = pd t → s = t) ∧
      pc '' Set.Icc (0:ℝ) 1 ∪ pd '' Set.Icc (0:ℝ) 1 = Set.range γ ∧
      pc '' Set.Icc (0:ℝ) 1 ∩ pd '' Set.Icc (0:ℝ) 1 = {γ za, γ zb} := by
  obtain ⟨θ, hθ⟩ := Circle.exp_surjective za
  let u : ℝ → X := fun t => γ (Circle.exp (θ + t))
  have hu_apply : ∀ t : ℝ, u t = γ (Circle.exp (θ + t)) := fun t => rfl
  have hu_cont : Continuous u :=
    hγ.comp (Circle.exp.continuous.comp (continuous_const.add continuous_id))
  have hchar : ∀ s t : ℝ, u s = u t ↔ ∃ m : ℤ, s = t + (m:ℝ) * (2*π) := by
    intro s t
    constructor
    · intro h
      have h2 : Circle.exp (θ + s) = Circle.exp (θ + t) := by
        apply hinj
        rw [← hu_apply s, ← hu_apply t]
        exact h
      obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h2
      exact ⟨m, by linarith⟩
    · rintro ⟨m, hm⟩
      rw [hu_apply, hu_apply]
      exact congrArg γ (Circle.exp_eq_exp.mpr ⟨m, by linarith⟩)
  let β : ℝ := Circle.angleDiff za zb
  have hβpos : 0 < β := Circle.angleDiff_pos hne
  have hβlt : β < 2*π := Circle.angleDiff_lt_two_pi za zb
  have hβge : 0 ≤ β := le_of_lt hβpos
  have hβle : β ≤ 2*π := le_of_lt hβlt
  have h2πβ : 0 < 2*π - β := by linarith
  have hu0 : u 0 = γ za := by rw [hu_apply, add_zero, hθ]
  have huβ : u β = γ zb := by
    have h : Circle.exp (θ + β) = zb := by
      rw [Circle.exp_add, hθ, mul_comm]
      exact Circle.exp_angleDiff_mul (x := za) (y := zb)
    rw [hu_apply]; exact congrArg γ h
  let pc : ℝ → X := fun s => u (s * β)
  let pd : ℝ → X := fun s => u (2*π - s * (2*π - β))
  have hpc_apply : ∀ s : ℝ, pc s = u (s * β) := fun s => rfl
  have hpd_apply : ∀ s : ℝ, pd s = u (2*π - s * (2*π - β)) := fun s => rfl
  have hpc_cont : Continuous pc := hu_cont.comp (continuous_id.mul continuous_const)
  have hpd_cont : Continuous pd :=
    hu_cont.comp (continuous_const.sub (continuous_id.mul continuous_const))
  have hpc0 : pc 0 = γ za := by rw [hpc_apply, zero_mul, hu_apply, add_zero, hθ]
  have hpc1 : pc 1 = γ zb := by rw [hpc_apply, one_mul]; exact huβ
  have hpd0 : pd 0 = γ za := by
    rw [hpd_apply, zero_mul, sub_zero, hu_apply, Circle.exp_add_two_pi, hθ]
  have hpd1 : pd 1 = γ zb := by
    have h : 2*π - 1 * (2*π - β) = β := by ring
    rw [hpd_apply, h]
    exact huβ
  have hpc_fst : ∀ s ∈ Set.Icc (0:ℝ) 1, s * β ∈ Set.Icc (0:ℝ) β := fun s hs =>
    ⟨mul_nonneg hs.1 hβge, by simpa using mul_le_mul_of_nonneg_right hs.2 hβge⟩
  have hpd_fst : ∀ s ∈ Set.Icc (0:ℝ) 1, 2*π - s*(2*π-β) ∈ Set.Icc β (2*π) := by
    intro s hs
    refine ⟨?_, ?_⟩
    · have h : s * (2*π - β) ≤ 1 * (2*π - β) := mul_le_mul_of_nonneg_right hs.2 h2πβ.le
      linarith
    · have h : 0 ≤ s * (2*π - β) := mul_nonneg hs.1 h2πβ.le
      linarith
  have hpc_inj : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, pc s = pc t → s = t := by
    intro s hs t ht hst
    have h : u (s*β) = u (t*β) := by rw [← hpc_apply s, ← hpc_apply t]; exact hst
    obtain ⟨m, hm⟩ := (hchar (s*β) (t*β)).mp h
    have habs : |s - t| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith [hs.1, ht.2], by linarith [ht.1, hs.2]⟩
    have hkey : (s - t) * β = (m:ℝ) * (2*π) := by nlinarith [hm]
    have hmlt : |(m:ℝ) * (2*π)| < 2*π := by
      rw [← hkey, abs_mul, abs_of_pos hβpos]
      calc |s - t| * β ≤ 1 * β := mul_le_mul_of_nonneg_right habs hβge
        _ < 2*π := by rw [one_mul]; exact hβlt
    have hm0 : m = 0 := int_cast_eq_zero_of_abs_mul_lt Real.two_pi_pos hmlt
    rw [hm0] at hm
    simp only [Int.cast_zero, zero_mul, add_zero] at hm
    nlinarith [hm, hβpos]
  have hpd_inj : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1, pd s = pd t → s = t := by
    intro s hs t ht hst
    have h : u (2*π - s*(2*π-β)) = u (2*π - t*(2*π-β)) := by
      rw [← hpd_apply s, ← hpd_apply t]; exact hst
    obtain ⟨m, hm⟩ := (hchar _ _).mp h
    have habs : |s - t| ≤ 1 := by
      rw [abs_le]; exact ⟨by linarith [hs.1, ht.2], by linarith [ht.1, hs.2]⟩
    have hkey : (t - s) * (2*π - β) = (m:ℝ) * (2*π) := by nlinarith [hm]
    have hmlt : |(m:ℝ) * (2*π)| < 2*π := by
      rw [← hkey, abs_mul, abs_of_pos h2πβ]
      calc |t - s| * (2*π - β) ≤ 1 * (2*π - β) :=
            mul_le_mul_of_nonneg_right (by rw [abs_sub_comm]; exact habs) h2πβ.le
        _ < 2*π := by rw [one_mul]; linarith
    have hm0 : m = 0 := int_cast_eq_zero_of_abs_mul_lt Real.two_pi_pos hmlt
    rw [hm0] at hm
    simp only [Int.cast_zero, zero_mul, add_zero] at hm
    nlinarith [hm, h2πβ]
  have hpc_image : pc '' Set.Icc (0:ℝ) 1 = u '' Set.Icc (0:ℝ) β := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨s*β, hpc_fst s hs, (hpc_apply s).symm⟩
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨σ/β, ⟨div_nonneg hσ.1 hβge, ?_⟩, ?_⟩
      · rw [div_le_one hβpos]; exact hσ.2
      · rw [hpc_apply, div_mul_cancel₀ σ (ne_of_gt hβpos)]
  have hpd_image : pd '' Set.Icc (0:ℝ) 1 = u '' Set.Icc β (2*π) := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact ⟨2*π - s*(2*π-β), hpd_fst s hs, (hpd_apply s).symm⟩
    · rintro ⟨σ, hσ, rfl⟩
      refine ⟨(2*π - σ)/(2*π - β), ⟨div_nonneg (by linarith [hσ.2]) h2πβ.le, ?_⟩, ?_⟩
      · rw [div_le_one h2πβ]; linarith [hσ.1]
      · rw [hpd_apply]
        have h : 2*π - (2*π - σ)/(2*π - β) * (2*π - β) = σ := by
          rw [div_mul_cancel₀ (2*π - σ) (ne_of_gt h2πβ)]; ring
        rw [h]
  have hIcc : Set.Icc (0:ℝ) β ∪ Set.Icc β (2*π) = Set.Icc (0:ℝ) (2*π) :=
    Set.Icc_union_Icc_eq_Icc hβge hβle
  have hu_range : u '' Set.Icc (0:ℝ) (2*π) = Set.range γ := by
    apply Set.Subset.antisymm
    · rintro y ⟨t, ht, rfl⟩
      exact ⟨Circle.exp (θ+t), rfl⟩
    · rintro y ⟨w, rfl⟩
      obtain ⟨ψ, hψ⟩ := Circle.exp_surjective w
      obtain ⟨s, hs, hsw⟩ := Circle.periodic_exp.exists_mem_Ico Real.two_pi_pos ψ θ
      refine ⟨s - θ, ⟨by linarith [hs.1], by linarith [hs.2.le]⟩, ?_⟩
      show γ (Circle.exp (θ + (s - θ))) = γ w
      rw [show θ + (s - θ) = s by ring, ← hsw, hψ]
  have hunion : pc '' Set.Icc (0:ℝ) 1 ∪ pd '' Set.Icc (0:ℝ) 1 = Set.range γ := by
    rw [hpc_image, hpd_image, ← Set.image_union, hIcc, hu_range]
  have hinter : pc '' Set.Icc (0:ℝ) 1 ∩ pd '' Set.Icc (0:ℝ) 1 = {γ za, γ zb} := by
    rw [hpc_image, hpd_image, ← hu0, ← huβ]
    apply Set.Subset.antisymm
    · rintro y ⟨⟨σ, hσ, hσy⟩, ⟨τ, hτ, hτy⟩⟩
      have hστ : u σ = u τ := hσy.trans hτy.symm
      obtain ⟨m, hm⟩ := (hchar σ τ).mp hστ
      have hmR : (m:ℝ) * (2*π) = σ - τ := by nlinarith [hm]
      have hle : (m:ℝ) * (2*π) ≤ 0 := by linarith [hmR, hσ.2, hτ.1]
      have hge : (-2*π:ℝ) ≤ (m:ℝ) * (2*π) := by linarith [hmR, hσ.1, hτ.2]
      have hm_le0 : m ≤ 0 :=
        (int_mul_le_int_mul_iff (p := m) (q := 0) Real.two_pi_pos).mp (by simpa using hle)
      have hm_ge1 : (-1:ℤ) ≤ m := by
        refine (int_mul_le_int_mul_iff (p := (-1:ℤ)) (q := m) Real.two_pi_pos).mp ?_
        have hh : ((↑(-1:ℤ) : ℝ)) = (-1:ℝ) := by norm_num
        rw [hh]; linarith
      have hm_cases : m = -1 ∨ m = 0 := by omega
      rcases hm_cases with hm1 | hm0
      · have hτeq : τ = σ + 2*π := by
          rw [hm1] at hm; push_cast at hm; linarith
        have hσ0 : σ = 0 := by linarith [hτeq, hτ.2, hσ.1]
        exact Or.inl (by rw [← hσy, hσ0, hu0])
      · have hστ' : σ = τ := by
          rw [hm0] at hm; push_cast at hm; linarith
        have hσβ : σ = β := by linarith [hστ', hσ.2, hτ.1]
        refine Or.inr ?_
        rw [Set.mem_singleton_iff]
        rw [← hσy, hσβ, huβ]
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · refine ⟨⟨0, ⟨le_refl 0, hβge⟩, rfl⟩, ⟨2*π, ⟨hβle, le_refl _⟩, ?_⟩⟩
        rw [hu_apply, hu_apply, add_zero, Circle.exp_add_two_pi]
      · exact ⟨⟨β, ⟨hβge, le_refl β⟩, rfl⟩, ⟨β, ⟨le_refl β, hβle⟩, rfl⟩⟩
  exact ⟨pc, pd, hpc_cont, hpd_cont, hpc0, hpc1, hpd0, hpd1, hpc_inj, hpd_inj, hunion, hinter⟩

end Work.RPB1a.Caratheodory.Maehara
