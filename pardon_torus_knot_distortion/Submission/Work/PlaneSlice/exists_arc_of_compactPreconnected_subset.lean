import Mathlib
import Submission.Work.Smooth.JordanSeparation.All
import Submission.Work.Smooth.JordanSeparation.subcontinuum_trace_interval
import Submission.Work.Smooth.Plane.Defs
import Submission.Work.InnermostDisk.All

namespace Work.PlaneSlice

open Set

theorem exists_arc_of_compactPreconnected_subset {c : ℝ → LeanEval.KnotTheory.PardonDistortion.R3}
    (hc : Continuous c) (hper : Function.Periodic c (2 * Real.pi))
    (hinj : Set.InjOn c (Set.Ico 0 (2 * Real.pi)))
    {K : Set LeanEval.KnotTheory.PardonDistortion.R3} (hKc : IsCompact K)
    (hKp : IsPreconnected K) (hKs : K ⊆ Set.range c) {s : ℝ} (hs : c s ∉ K) :
    ∃ a : C(Work.Smooth.Plane.ArcInterval, LeanEval.KnotTheory.PardonDistortion.R3),
      Function.Injective a ∧ Set.range a ⊆ Set.range c ∧ K ⊆ Set.range a := by
  classical
  by_cases hKne : K.Nonempty
  · -- ## Main case: `K` is a nonempty subcontinuum of the circle `range c`
    --
    -- Cut the circle at the parameter `s`: the parameters of `K` can be shifted into the
    -- fundamental interval `[s, s + 2π]`, where `c` is injective.
    set A : Set ℝ := c ⁻¹' K with hAdef
    set T : Set ℝ := A ∩ Set.Icc s (s + 2 * Real.pi) with hTdef
    have hAmem : ∀ t : ℝ, t ∈ A ↔ c t ∈ K := by
      intro t; rw [hAdef]; exact Iff.rfl
    have hTmem : ∀ t : ℝ, t ∈ T ↔ c t ∈ K ∧ t ∈ Set.Icc s (s + 2 * Real.pi) := by
      intro t; rw [hTdef, Set.mem_inter_iff, hAmem]
    have hAclosed : IsClosed A := by rw [hAdef]; exact hKc.isClosed.preimage hc
    have hAper : ∀ t : ℝ, (t + 2 * Real.pi ∈ A) ↔ t ∈ A := by
      intro t; rw [hAmem (t + 2 * Real.pi), hAmem t, hper t]
    have hsA : s ∉ A := fun h => hs ((hAmem s).mp h)
    have hsA' : s + 2 * Real.pi ∉ A := fun h => hsA ((hAper s).mp h)
    have hTcompact : IsCompact T := by
      rw [hTdef, Set.inter_comm]
      exact isCompact_Icc.inter_right hAclosed
    have hTsub : T ⊆ Set.Ico s (s + 2 * Real.pi) := by
      intro t ht
      obtain ⟨hctK, htIcc⟩ := (hTmem t).mp ht
      have htA : t ∈ A := (hAmem t).mpr hctK
      refine ⟨htIcc.1, lt_of_le_of_ne htIcc.2 ?_⟩
      intro hcon
      exact hsA' (hcon ▸ htA)
    -- `c` is injective on any half-open interval of length `2π`, in particular on `T`
    have hinjIco : ∀ {t u : ℝ}, t ∈ Set.Ico s (s + 2 * Real.pi) →
        u ∈ Set.Ico s (s + 2 * Real.pi) → c t = c u → t = u := by
      intro t u ht hu htu
      obtain ⟨k, hk⟩ := (Work.InnermostDisk.eq_iff_sub_int_mul_two_pi hper hinj t u).mp htu
      have hk' : t - u = (k : ℝ) * (2 * Real.pi) := by linarith
      have habs : |t - u| < 2 * Real.pi := by
        rw [abs_lt]; constructor <;> linarith [ht.1, ht.2, hu.1, hu.2]
      rw [hk'] at habs
      have hk0 : k = 0 := Work.Smooth.JordanSeparation.int_eq_zero_of_mul_two_pi_abs_lt k habs
      rw [hk0] at hk'
      simp at hk'
      linarith
    have hTinj : Set.InjOn c T := fun _ ht _ hu htu => hinjIco (hTsub ht) (hTsub hu) htu
    -- every point of `K` has a parameter in `T`
    have hKmemT : ∀ t : ℝ, c t ∈ K → ∃ t' ∈ T, c t' = c t := by
      intro t ht
      set m : ℤ := ⌊(t - s) / (2 * Real.pi)⌋ with hm
      have hper_m : c (t - (m : ℝ) * (2 * Real.pi) + (m : ℝ) * (2 * Real.pi)) =
          c (t - (m : ℝ) * (2 * Real.pi)) := (hper.int_mul m) _
      rw [show t - (m : ℝ) * (2 * Real.pi) + (m : ℝ) * (2 * Real.pi) = t from by ring] at hper_m
      refine ⟨t - (m : ℝ) * (2 * Real.pi), ?_, hper_m.symm⟩
      refine (hTmem _).mpr ⟨hper_m ▸ ht, ?_⟩
      have hpos : (0 : ℝ) < 2 * Real.pi := by positivity
      have h1 : (m : ℝ) * (2 * Real.pi) ≤ t - s := by
        rw [hm]
        exact (le_div_iff₀ hpos).mp (Int.floor_le ((t - s) / (2 * Real.pi)))
      have h2 : t - s < (m : ℝ) * (2 * Real.pi) + 2 * Real.pi := by
        rw [hm]
        have := (div_lt_iff₀ hpos).mp (Int.lt_floor_add_one ((t - s) / (2 * Real.pi)))
        linarith
      constructor <;> linarith
    have hTne : T.Nonempty := by
      obtain ⟨x, hx⟩ := hKne
      obtain ⟨t, ht⟩ := hKs hx
      obtain ⟨t', ht'T, _⟩ := hKmemT t (by rw [ht]; exact hx)
      exact ⟨t', ht'T⟩
    have hTrange : c '' T = K := by
      apply Set.Subset.antisymm
      · rintro _ ⟨t, ht, rfl⟩
        exact ((hTmem t).mp ht).1
      · intro x hx
        obtain ⟨t, ht⟩ := hKs hx
        obtain ⟨t', ht'T, ht'c⟩ := hKmemT t (by rw [ht]; exact hx)
        exact ⟨t', ht'T, ht'c.trans ht⟩
    -- `T` is an interval: `K = c '' T` with `c` injective on `T`
    have hTord : T.OrdConnected := by
      refine ⟨?_⟩
      rintro a ha b hb z hz
      obtain ⟨haz, hzb⟩ := hz
      by_contra hzT
      have hne1 : (c '' (T ∩ Set.Iic z)).Nonempty := ⟨c a, a, ⟨ha, haz⟩, rfl⟩
      have hne2 : (c '' (T ∩ Set.Ici z)).Nonempty := ⟨c b, b, ⟨hb, hzb⟩, rfl⟩
      have hcov : K ⊆ c '' (T ∩ Set.Iic z) ∪ c '' (T ∩ Set.Ici z) := by
        intro x hx
        rw [← hTrange] at hx
        obtain ⟨t, ht, rfl⟩ := hx
        rcases le_total t z with h | h
        · exact Or.inl ⟨t, ⟨ht, h⟩, rfl⟩
        · exact Or.inr ⟨t, ⟨ht, h⟩, rfl⟩
      have hdisj : Disjoint (c '' (T ∩ Set.Iic z)) (c '' (T ∩ Set.Ici z)) := by
        rw [Set.disjoint_left]
        rintro y ⟨t₁, ht₁, rfl⟩ ⟨t₂, ht₂, h₂⟩
        have heq : t₁ = t₂ := hTinj ht₁.1 ht₂.1 h₂.symm
        have hcz : t₁ = z := le_antisymm ht₁.2 (heq ▸ ht₂.2)
        exact hzT (hcz ▸ ht₁.1)
      have hcl1 : IsClosed (c '' (T ∩ Set.Iic z)) :=
        ((hTcompact.inter_right isClosed_Iic).image hc).isClosed
      have hcl2 : IsClosed (c '' (T ∩ Set.Ici z)) := by
        rw [Set.inter_comm]
        exact ((hTcompact.inter_left isClosed_Ici).image hc).isClosed
      have hdisj' : K ∩ ((c '' (T ∩ Set.Iic z)) ∩ (c '' (T ∩ Set.Ici z))) = ∅ := by
        rw [Set.eq_empty_iff_forall_notMem]
        rintro y ⟨-, hy1, hy2⟩
        exact Set.disjoint_left.mp hdisj hy1 hy2
      rcases (isPreconnected_iff_subset_of_disjoint_closed.mp hKp)
        (c '' (T ∩ Set.Iic z)) (c '' (T ∩ Set.Ici z)) hcl1 hcl2 hcov hdisj' with h | h
      · obtain ⟨w, hw⟩ := hne2
        rw [Set.mem_image] at hw
        obtain ⟨s', hsX, hsw⟩ := hw
        exact Set.disjoint_left.mp hdisj (h (hsw ▸ ((hTmem s').mp hsX.1).1)) ⟨s', hsX, hsw⟩
      · obtain ⟨w, hw⟩ := hne1
        rw [Set.mem_image] at hw
        obtain ⟨s', hsX, hsw⟩ := hw
        exact Set.disjoint_right.mp hdisj (h (hsw ▸ ((hTmem s').mp hsX.1).1)) ⟨s', hsX, hsw⟩
    obtain ⟨a0, ha0T, ha0least⟩ := hTcompact.exists_isLeast hTne
    obtain ⟨b0, hb0T, hb0greatest⟩ := hTcompact.exists_isGreatest hTne
    have hTeq : T = Set.Icc a0 b0 := by
      apply Set.Subset.antisymm
      · intro x hx; exact ⟨ha0least hx, hb0greatest hx⟩
      · intro x hx; exact hTord.out' ha0T hb0T hx
    have ha0b0 : a0 ≤ b0 := ha0least hb0T
    have ha0gt : s < a0 := by
      rcases lt_or_eq_of_le ((hTmem a0).mp ha0T).2.1 with h | h
      · exact h
      · exact absurd (h ▸ ((hTmem a0).mp ha0T).1) hs
    have hb0lt : b0 < s + 2 * Real.pi := by
      rcases lt_or_eq_of_le ((hTmem b0).mp hb0T).2.2 with h | h
      · exact h
      · exact absurd ((hAmem (s + 2 * Real.pi)).mpr (h ▸ ((hTmem b0).mp hb0T).1)) hsA'
    -- the arc of the circle containing `T`: `[a0, a0 + L]`
    set L : ℝ := (b0 - a0) + (s + 2 * Real.pi - b0) / 2 with hLdef
    have hLpos : 0 < L := by
      rw [hLdef]; linarith
    have hb0_le : b0 ≤ a0 + L := by
      rw [hLdef]; linarith
    have ha0L_lt : a0 + L < s + 2 * Real.pi := by
      rw [hLdef]; linarith
    have hIcc_sub : Set.Icc a0 (a0 + L) ⊆ Set.Ico s (s + 2 * Real.pi) := fun t ht =>
      ⟨by linarith [ht.1], by linarith [ht.2]⟩
    refine ⟨⟨fun u : Work.Smooth.Plane.ArcInterval => c (a0 + (u : ℝ) * L), ?_⟩,
      ?_, ?_, ?_⟩
    · exact hc.comp (continuous_const.add (continuous_subtype_val.mul continuous_const))
    · intro u v huv
      have hu : a0 + (u : ℝ) * L ∈ Set.Icc a0 (a0 + L) :=
        ⟨by nlinarith [hLpos, u.2.1], by nlinarith [hLpos, u.2.2]⟩
      have hv : a0 + (v : ℝ) * L ∈ Set.Icc a0 (a0 + L) :=
        ⟨by nlinarith [hLpos, v.2.1], by nlinarith [hLpos, v.2.2]⟩
      exact Subtype.ext (by nlinarith [hLpos, hinjIco (hIcc_sub hu) (hIcc_sub hv) huv])
    · rintro _ ⟨u, rfl⟩
      exact ⟨_, rfl⟩
    · rw [← hTrange, hTeq]
      rintro _ ⟨t, ht, rfl⟩
      have htL : t ∈ Set.Icc a0 (a0 + L) := ⟨ht.1, le_trans ht.2 hb0_le⟩
      refine ⟨⟨(t - a0) / L, ?_, ?_⟩, ?_⟩
      · exact div_nonneg (by linarith [htL.1]) (le_of_lt hLpos)
      · rw [div_le_one hLpos]; linarith [htL.2]
      · show c (a0 + (t - a0) / L * L) = c t
        have h1 : a0 + (t - a0) / L * L = t := by
          rw [div_mul_cancel₀ (t - a0) (ne_of_gt hLpos)]
          ring
        rw [h1]
  · -- ## Degenerate case: `K = ∅`
    have hKempt : K = ∅ := Set.not_nonempty_iff_eq_empty.mp hKne
    refine ⟨⟨fun u : Work.Smooth.Plane.ArcInterval => c (Real.pi * (u : ℝ)), ?_⟩,
      ?_, ?_, ?_⟩
    · exact hc.comp (continuous_const.mul continuous_subtype_val)
    · intro u v huv
      have hu : Real.pi * (u : ℝ) ∈ Set.Ico 0 (2 * Real.pi) := by
        refine ⟨by nlinarith [Real.pi_pos, u.2.1], by nlinarith [Real.pi_pos, u.2.2]⟩
      have hv : Real.pi * (v : ℝ) ∈ Set.Ico 0 (2 * Real.pi) := by
        refine ⟨by nlinarith [Real.pi_pos, v.2.1], by nlinarith [Real.pi_pos, v.2.2]⟩
      exact Subtype.ext (by nlinarith [Real.pi_pos, hinj hu hv huv])
    · rintro _ ⟨u, rfl⟩
      exact ⟨_, rfl⟩
    · rw [hKempt]; exact Set.empty_subset _

end Work.PlaneSlice
