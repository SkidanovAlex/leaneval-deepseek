import Mathlib
import Submission.Work.Spike.spikePreconnected

/-!
# Cutting a crosscut in two: both halves have preconnected complement

`Work.Spike.half_preconnected`: if `K` is compact with `Kᶜ` preconnected and `γ` is an arc whose
interior misses `K`, then for every interior parameter `t₀` the complements of `K ∪ γ[0,t₀]` and of
`K ∪ γ[t₀,1]` are both preconnected.  This is the input that lets the global "at most two
components" argument start from either half.

The proof is two applications of the spike lemma `Work.Spike.spikePreconnected` to the reparametrised
halves `arcPrefix`, `arcSuffixRev`; the six lemmas below are the side conditions (injectivity, that
the half starts in `K`, and that it leaves `K` immediately).

**Lean note (witness handling).**  When the half-arc `h` is defined by a subtype-valued expression,
the witness of `h ⟨0,…⟩` comes from the definition and cannot be named.  The workable route is to
*avoid introducing a fresh witness*: prove `h ⟨0,…⟩ = γ ⟨0,…⟩` by `apply congrArg γ` (which unfolds
the definition and unifies the definition's own witness into the goal) followed by `Subtype.ext` and
an arithmetic step; for the "leaves `K`" lemmas, name the bound proof (`have hb : … := ⟨…⟩`) so that
the same term appears on both sides and `hint ⟨…, hb⟩` applies directly.
-/

open Set

namespace Work.Spike

noncomputable section

/-- The arc `s ↦ γ (t₀ · s)`, running from `γ 0` to `γ t₀`. -/
def arcPrefix (γ : C(Set.Icc (0 : ℝ) 1, ℂ)) (t₀ : ℝ) (h0 : 0 ≤ t₀) (h1 : t₀ ≤ 1) :
    C(Set.Icc (0 : ℝ) 1, ℂ) where
  toFun := fun s => γ ⟨t₀ * (s : ℝ),
    ⟨mul_nonneg h0 s.2.1, by
      have h := mul_le_mul h1 s.2.2 s.2.1 (by norm_num : (0 : ℝ) ≤ 1)
      simpa using h⟩⟩
  continuous_toFun := γ.continuous.comp (Continuous.subtype_mk (by fun_prop) _)

/-- The arc `s ↦ γ (1 - (1 - t₀) · s)`, running from `γ 1` to `γ t₀`. -/
def arcSuffixRev (γ : C(Set.Icc (0 : ℝ) 1, ℂ)) (t₀ : ℝ) (h0 : 0 ≤ t₀) (h1 : t₀ ≤ 1) :
    C(Set.Icc (0 : ℝ) 1, ℂ) where
  toFun := fun s => γ ⟨1 - (1 - t₀) * (s : ℝ),
    ⟨by
      have hle : (1 - t₀) * (s : ℝ) ≤ 1 - t₀ := by
        have h := mul_le_mul_of_nonneg_left s.2.2 (by linarith : (0 : ℝ) ≤ 1 - t₀)
        simpa using h
      linarith,
     by
      have hnn : 0 ≤ (1 - t₀) * (s : ℝ) := mul_nonneg (by linarith) s.2.1
      linarith⟩⟩
  continuous_toFun := γ.continuous.comp (Continuous.subtype_mk (by fun_prop) _)

/-! ## The six side conditions -/

/-- Injectivity of the first half-arc (`t₀ ≠ 0`). -/
theorem arcPrefix_injective {γ : C(Set.Icc (0 : ℝ) 1, ℂ)} (hγ : Function.Injective γ)
    {t₀ : ℝ} (h0 : 0 ≤ t₀) (h1 : t₀ ≤ 1) (ht₀ : 0 < t₀) :
    Function.Injective (arcPrefix γ t₀ h0 h1) := by
  intro s u hsu
  have hval : (⟨t₀ * (s : ℝ), _⟩ : Set.Icc (0 : ℝ) 1) = ⟨t₀ * (u : ℝ), _⟩ := hγ hsu
  have h2 : t₀ * (s : ℝ) = t₀ * (u : ℝ) := congrArg Subtype.val hval
  exact Subtype.ext (mul_left_cancel₀ (ne_of_gt ht₀) h2)

/-- The first half-arc starts in `K`. -/
theorem arcPrefix_zero_mem {γ : C(Set.Icc (0 : ℝ) 1, ℂ)} {K : Set ℂ} {t₀ : ℝ}
    (h0 : 0 ≤ t₀) (h1 : t₀ ≤ 1) (h₀ : γ ⟨0, by norm_num⟩ ∈ K) :
    (arcPrefix γ t₀ h0 h1) ⟨0, by norm_num⟩ ∈ K := by
  rw [show (arcPrefix γ t₀ h0 h1) ⟨0, by norm_num⟩
      = γ (⟨0, by norm_num⟩ : Set.Icc (0 : ℝ) 1) from by
    apply congrArg γ
    apply Subtype.ext
    norm_num]
  exact h₀

/-- The first half-arc leaves `K` immediately. -/
theorem arcPrefix_out {γ : C(Set.Icc (0 : ℝ) 1, ℂ)} {K : Set ℂ} {t₀ : ℝ}
    (h0 : 0 ≤ t₀) (h1 : t₀ ≤ 1) (ht₀ : 0 < t₀)
    (hint : ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → γ t ∉ K) :
    ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → (arcPrefix γ t₀ h0 h1) t ∉ K := by
  intro t ht
  have hb : t₀ * (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨mul_nonneg h0 t.2.1, by
    have h := mul_le_mul h1 t.2.2 t.2.1 (by norm_num : (0 : ℝ) ≤ 1)
    simpa using h⟩
  rw [show (arcPrefix γ t₀ h0 h1) t = γ (⟨t₀ * (t : ℝ), hb⟩ : Set.Icc (0 : ℝ) 1) from by
    apply congrArg γ
    apply Subtype.ext
    rfl]
  exact hint ⟨t₀ * (t : ℝ), hb⟩ (mul_pos ht₀ ht)

/-- Injectivity of the reversed second half-arc (`t₀ ≠ 1`). -/
theorem arcSuffixRev_injective {γ : C(Set.Icc (0 : ℝ) 1, ℂ)} (hγ : Function.Injective γ)
    {t₀ : ℝ} (h0 : 0 ≤ t₀) (h1 : t₀ ≤ 1) (ht₀ : t₀ < 1) :
    Function.Injective (arcSuffixRev γ t₀ h0 h1) := by
  intro s u hsu
  have hval : (⟨1 - (1 - t₀) * (s : ℝ), _⟩ : Set.Icc (0 : ℝ) 1)
      = ⟨1 - (1 - t₀) * (u : ℝ), _⟩ := hγ hsu
  have h2 : 1 - (1 - t₀) * (s : ℝ) = 1 - (1 - t₀) * (u : ℝ) := congrArg Subtype.val hval
  have h3 : (1 - t₀) * (s : ℝ) = (1 - t₀) * (u : ℝ) := by linarith
  have hne : (1 - t₀) ≠ 0 := by intro h; linarith
  exact Subtype.ext (mul_left_cancel₀ hne h3)

/-- The reversed second half-arc starts in `K`. -/
theorem arcSuffixRev_zero_mem {γ : C(Set.Icc (0 : ℝ) 1, ℂ)} {K : Set ℂ} {t₀ : ℝ}
    (h0 : 0 ≤ t₀) (h1 : t₀ ≤ 1) (h₁ : γ ⟨1, by norm_num⟩ ∈ K) :
    (arcSuffixRev γ t₀ h0 h1) ⟨0, by norm_num⟩ ∈ K := by
  rw [show (arcSuffixRev γ t₀ h0 h1) ⟨0, by norm_num⟩
      = γ (⟨1, by norm_num⟩ : Set.Icc (0 : ℝ) 1) from by
    apply congrArg γ
    apply Subtype.ext
    norm_num]
  exact h₁

/-- The reversed second half-arc leaves `K` immediately. -/
theorem arcSuffixRev_out {γ : C(Set.Icc (0 : ℝ) 1, ℂ)} {K : Set ℂ} {t₀ : ℝ}
    (h0 : 0 ≤ t₀) (h1 : t₀ ≤ 1) (ht₀ : 0 < t₀) (ht₁ : t₀ < 1)
    (hint : ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → γ t ∉ K) :
    ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → (arcSuffixRev γ t₀ h0 h1) t ∉ K := by
  intro t ht
  have hle : (1 - t₀) * (t : ℝ) ≤ 1 - t₀ := by
    have h := mul_le_mul_of_nonneg_left t.2.2 (by linarith [h1] : (0 : ℝ) ≤ 1 - t₀)
    simpa using h
  have hlt : (1 - t₀) * (t : ℝ) < 1 := lt_of_le_of_lt hle (sub_lt_self 1 ht₀)
  have hpos : 0 < 1 - (1 - t₀) * (t : ℝ) := sub_pos.mpr hlt
  have hb : 1 - (1 - t₀) * (t : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨le_of_lt hpos, by
    have h2 : 0 ≤ (1 - t₀) * (t : ℝ) := mul_nonneg (by linarith [h1]) t.2.1
    linarith⟩
  rw [show (arcSuffixRev γ t₀ h0 h1) t
      = γ (⟨1 - (1 - t₀) * (t : ℝ), hb⟩ : Set.Icc (0 : ℝ) 1) from by
    apply congrArg γ
    apply Subtype.ext
    rfl]
  exact hint ⟨1 - (1 - t₀) * (t : ℝ), hb⟩ hpos

/-! ## The theorem -/

/-- **Both halves of a crosscut at an interior parameter have preconnected complement.** -/
theorem half_preconnected {K : Set ℂ} (hK : IsCompact K) (hconn : IsPreconnected Kᶜ)
    {γ : C(Set.Icc (0 : ℝ) 1, ℂ)} (hγ : Function.Injective γ)
    {t₀ : ℝ} (ht₀ : t₀ ∈ Set.Ioo (0 : ℝ) 1)
    (h₀ : γ ⟨0, by norm_num⟩ ∈ K) (h₁ : γ ⟨1, by norm_num⟩ ∈ K)
    (hint : ∀ t : Set.Icc (0 : ℝ) 1, 0 < (t : ℝ) → γ t ∉ K) :
    IsPreconnected ((K ∪ Set.range (arcPrefix γ t₀ ht₀.1.le ht₀.2.le))ᶜ) ∧
      IsPreconnected ((K ∪ Set.range (arcSuffixRev γ t₀ ht₀.1.le ht₀.2.le))ᶜ) :=
  ⟨spikePreconnected hK hconn (arcPrefix_injective hγ ht₀.1.le ht₀.2.le ht₀.1)
     (arcPrefix_zero_mem ht₀.1.le ht₀.2.le h₀)
     (arcPrefix_out ht₀.1.le ht₀.2.le ht₀.1 hint),
   spikePreconnected hK hconn (arcSuffixRev_injective hγ ht₀.1.le ht₀.2.le ht₀.2)
     (arcSuffixRev_zero_mem ht₀.1.le ht₀.2.le h₁)
     (arcSuffixRev_out ht₀.1.le ht₀.2.le ht₀.1 ht₀.2 hint)⟩


/-! ## The ranges of the two halves -/

/-- The first half-arc traces exactly `γ` over `[0,t₀]`. -/
theorem range_arcPrefix {γ : C(Set.Icc (0 : ℝ) 1, ℂ)} {t₀ : ℝ} (h0 : 0 ≤ t₀) (h1 : t₀ ≤ 1)
    (ht₀ : 0 < t₀) :
    Set.range (arcPrefix γ t₀ h0 h1)
      = γ '' {s : Set.Icc (0 : ℝ) 1 | (s : ℝ) ∈ Set.Icc 0 t₀} := by
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    have hb : t₀ * (s : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨mul_nonneg h0 s.2.1, by
      have h := mul_le_mul h1 s.2.2 s.2.1 (by norm_num : (0 : ℝ) ≤ 1)
      simpa using h⟩
    refine ⟨⟨t₀ * (s : ℝ), hb⟩, ?_, ?_⟩
    · exact ⟨mul_nonneg h0 s.2.1, by simpa using mul_le_mul_of_nonneg_left s.2.2 h0⟩
    · rw [show (arcPrefix γ t₀ h0 h1) s = γ (⟨t₀ * (s : ℝ), hb⟩ : Set.Icc (0 : ℝ) 1) from by
        apply congrArg γ
        apply Subtype.ext
        rfl]
  · rintro ⟨s, hs, rfl⟩
    refine ⟨⟨(s : ℝ) / t₀, ⟨div_nonneg hs.1 h0, (div_le_one ht₀).mpr hs.2⟩⟩, ?_⟩
    rw [show (arcPrefix γ t₀ h0 h1)
          ⟨(s : ℝ) / t₀, ⟨div_nonneg hs.1 h0, (div_le_one ht₀).mpr hs.2⟩⟩ = γ s from by
      apply congrArg γ
      apply Subtype.ext
      field_simp]

/-- The reversed second half-arc traces exactly `γ` over `[t₀,1]`. -/
theorem range_arcSuffixRev {γ : C(Set.Icc (0 : ℝ) 1, ℂ)} {t₀ : ℝ} (h0 : 0 ≤ t₀) (h1 : t₀ ≤ 1)
    (ht₁ : t₀ < 1) :
    Set.range (arcSuffixRev γ t₀ h0 h1)
      = γ '' {s : Set.Icc (0 : ℝ) 1 | (s : ℝ) ∈ Set.Icc t₀ 1} := by
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    have hle : (1 - t₀) * (s : ℝ) ≤ 1 - t₀ := by
      have h := mul_le_mul_of_nonneg_left s.2.2 (by linarith : (0 : ℝ) ≤ 1 - t₀)
      simpa using h
    have hnn : 0 ≤ (1 - t₀) * (s : ℝ) := mul_nonneg (by linarith) s.2.1
    have hb : 1 - (1 - t₀) * (s : ℝ) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    refine ⟨⟨1 - (1 - t₀) * (s : ℝ), hb⟩, ?_, ?_⟩
    · exact ⟨by linarith, by linarith⟩
    · rw [show (arcSuffixRev γ t₀ h0 h1) s
          = γ (⟨1 - (1 - t₀) * (s : ℝ), hb⟩ : Set.Icc (0 : ℝ) 1) from by
        apply congrArg γ
        apply Subtype.ext
        rfl]
  · rintro ⟨s, hs, rfl⟩
    have hne : (1 - t₀) ≠ 0 := by intro h; linarith [hs.2]
    refine ⟨⟨(1 - (s : ℝ)) / (1 - t₀), ⟨div_nonneg (by linarith [hs.2]) (by linarith),
      (div_le_one (by linarith : (0 : ℝ) < 1 - t₀)).mpr (by linarith [hs.1])⟩⟩, ?_⟩
    rw [show (arcSuffixRev γ t₀ h0 h1)
          ⟨(1 - (s : ℝ)) / (1 - t₀), ⟨div_nonneg (by linarith [hs.2]) (by linarith),
            (div_le_one (by linarith : (0 : ℝ) < 1 - t₀)).mpr (by linarith [hs.1])⟩⟩
        = γ s from by
      apply congrArg γ
      apply Subtype.ext
      field_simp; ring]


/-- The two half-arcs meet exactly in the interior point `γ t₀`. -/
theorem range_arcPrefix_inter_range_arcSuffixRev {γ : C(Set.Icc (0 : ℝ) 1, ℂ)}
    (hγ : Function.Injective γ) {t₀ : ℝ} (h0 : 0 ≤ t₀) (h1 : t₀ ≤ 1) (ht₀ : 0 < t₀)
    (ht₁ : t₀ < 1) :
    Set.range (arcPrefix γ t₀ h0 h1) ∩ Set.range (arcSuffixRev γ t₀ h0 h1)
      = {γ (⟨t₀, h0, h1⟩ : Set.Icc (0 : ℝ) 1)} := by
  apply Set.Subset.antisymm
  · rintro z ⟨hz1, hz2⟩
    rw [range_arcPrefix h0 h1 ht₀] at hz1
    rw [range_arcSuffixRev h0 h1 ht₁] at hz2
    obtain ⟨s, hs, hsγ⟩ := hz1
    obtain ⟨u, hu, huγ⟩ := hz2
    have hsu : s = u := hγ (hsγ.trans huγ.symm)
    have hval : (s : ℝ) = (u : ℝ) := congrArg Subtype.val hsu
    have ht : (s : ℝ) = t₀ := le_antisymm hs.2 (by rw [hval]; exact hu.1)
    rw [Set.mem_singleton_iff, ← hsγ]
    exact congrArg γ (Subtype.ext ht)
  · intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    refine ⟨?_, ?_⟩
    · rw [range_arcPrefix h0 h1 ht₀]
      exact ⟨⟨t₀, h0, h1⟩, ⟨h0, le_refl t₀⟩, rfl⟩
    · rw [range_arcSuffixRev h0 h1 ht₁]
      exact ⟨⟨t₀, h0, h1⟩, ⟨le_refl t₀, h1⟩, rfl⟩


/-- The two half-arcs together trace all of `γ`. -/
theorem range_arcPrefix_union_range_arcSuffixRev {γ : C(Set.Icc (0 : ℝ) 1, ℂ)}
    {t₀ : ℝ} (h0 : 0 ≤ t₀) (h1 : t₀ ≤ 1) (ht₀ : 0 < t₀) (ht₁ : t₀ < 1) :
    Set.range (arcPrefix γ t₀ h0 h1) ∪ Set.range (arcSuffixRev γ t₀ h0 h1) = Set.range γ := by
  apply Set.Subset.antisymm
  · rintro z (hz | hz)
    · rw [range_arcPrefix h0 h1 ht₀] at hz
      obtain ⟨s, -, rfl⟩ := hz
      exact ⟨s, rfl⟩
    · rw [range_arcSuffixRev h0 h1 ht₁] at hz
      obtain ⟨s, -, rfl⟩ := hz
      exact ⟨s, rfl⟩
  · rintro z ⟨t, rfl⟩
    rcases le_total (t : ℝ) t₀ with htle | htge
    · refine Or.inl ⟨⟨(t : ℝ) / t₀, ⟨div_nonneg t.2.1 h0, (div_le_one ht₀).mpr htle⟩⟩, ?_⟩
      rw [show (arcPrefix γ t₀ h0 h1)
            ⟨(t : ℝ) / t₀, ⟨div_nonneg t.2.1 h0, (div_le_one ht₀).mpr htle⟩⟩ = γ t from by
        apply congrArg γ
        apply Subtype.ext
        field_simp]
    · refine Or.inr ⟨⟨(1 - (t : ℝ)) / (1 - t₀),
          ⟨div_nonneg (by linarith [t.2.2]) (by linarith),
           (div_le_one (by linarith : (0 : ℝ) < 1 - t₀)).mpr (by linarith [t.2.1])⟩⟩, ?_⟩
      rw [show (arcSuffixRev γ t₀ h0 h1)
            ⟨(1 - (t : ℝ)) / (1 - t₀),
              ⟨div_nonneg (by linarith [t.2.2]) (by linarith),
               (div_le_one (by linarith : (0 : ℝ) < 1 - t₀)).mpr (by linarith [t.2.1])⟩⟩
          = γ t from by
        apply congrArg γ
        apply Subtype.ext
        have hne : (1 - t₀) ≠ 0 := by intro h; linarith [h]
        have h1' : (1 - t₀) * ((1 - (t : ℝ)) / (1 - t₀)) = 1 - (t : ℝ) := by
          field_simp
        linarith]

end

end Work.Spike
