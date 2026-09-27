import Mathlib

namespace Work.Mostow

/-- One-sided Dini-type estimate: a continuous function on `[a,b]` whose upper right
increments at every interior point are eventually bounded by `(1+ε)` times the step,
for every `ε > 0`, satisfies `f b ≤ f a + (b - a)`. -/
theorem oneSidedLipschitz {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hloc : ∀ t ∈ Set.Ico a b, ∀ ε > 0, ∃ δ > 0, ∀ h ∈ Set.Ioo 0 δ,
      f (t + h) ≤ f t + h * (1 + ε)) :
    f b ≤ f a + (b - a) := by
  have key : ∀ ε > 0, f b ≤ f a + (1 + ε) * (b - a) := by
    intro ε hε
    set A : Set ℝ := Set.Icc a b ∩ {t | f t ≤ f a + (1 + ε) * (t - a)} with hA
    have hcontg : ContinuousOn (fun t : ℝ => f t - (1 + ε) * (t - a) - f a)
        (Set.Icc a b) := by
      have h1 : ContinuousOn (fun t : ℝ => (1 + ε) * (t - a)) (Set.Icc a b) :=
        continuousOn_const.mul (continuousOn_id.sub continuousOn_const)
      exact (hcont.sub h1).sub continuousOn_const
    have heq : A = Set.Icc a b ∩
        (fun t : ℝ => f t - (1 + ε) * (t - a) - f a) ⁻¹' Set.Iic 0 := by
      ext t
      simp only [hA, Set.mem_inter_iff, Set.mem_Icc, Set.mem_ofPred_eq,
        Set.mem_preimage, Set.mem_Iic]
      constructor <;> rintro ⟨h1, h2⟩ <;> exact ⟨h1, by linarith⟩
    have hAclosed : IsClosed A := by
      rw [heq]
      exact hcontg.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have haA : a ∈ A := ⟨⟨le_refl a, hab⟩, by simp⟩
    have hnonempty : A.Nonempty := ⟨a, haA⟩
    have hsub : A ⊆ Set.Icc a b := by rw [hA]; exact Set.inter_subset_left
    have hbdd : BddAbove A := bddAbove_Icc.mono hsub
    have hsA : sSup A ∈ A := hAclosed.csSup_mem hnonempty hbdd
    have hs_le_b : sSup A ≤ b := csSup_le hnonempty (fun x hx => hx.1.2)
    have rightopen : ∀ t ∈ A, t < b → ∃ δ > 0, ∀ u ∈ Set.Ioo t (t + δ), u ∈ A := by
      intro t ht htb
      have htIco : t ∈ Set.Ico a b := ⟨ht.1.1, htb⟩
      have hft : f t ≤ f a + (1 + ε) * (t - a) := ht.2
      obtain ⟨δ0, hδ0pos, hδ0⟩ := hloc t htIco ε hε
      refine ⟨min δ0 (b - t), lt_min hδ0pos (sub_pos.mpr htb), ?_⟩
      intro u hu
      have hu0 : 0 < u - t := sub_pos.mpr hu.1
      have huδ : u - t < min δ0 (b - t) := by linarith [hu.2]
      have hle := hδ0 (u - t) ⟨hu0, lt_of_lt_of_le huδ (min_le_left _ _)⟩
      have huteq : t + (u - t) = u := by ring
      rw [huteq] at hle
      have hub : u ≤ b := by
        have : u - t < b - t := lt_of_lt_of_le huδ (min_le_right _ _)
        linarith
      have hau : a ≤ u := le_trans ht.1.1 (le_of_lt hu.1)
      refine ⟨⟨hau, hub⟩, ?_⟩
      calc f u ≤ f t + (u - t) * (1 + ε) := hle
        _ ≤ (f a + (1 + ε) * (t - a)) + (u - t) * (1 + ε) := by linarith
        _ = f a + (1 + ε) * (u - a) := by ring
    have hsb : sSup A = b := by
      by_contra hne
      have hlt : sSup A < b := lt_of_le_of_ne hs_le_b hne
      obtain ⟨δ, hδpos, hδA⟩ := rightopen (sSup A) hsA hlt
      have hmem : sSup A + δ / 2 ∈ A := hδA _ ⟨by linarith, by linarith⟩
      have hle := le_csSup hbdd hmem
      linarith
    have hbA : b ∈ A := hsb ▸ hsA
    exact hbA.2
  apply le_of_forall_pos_le_add
  intro η hη
  have hbapos : (0 : ℝ) < b - a + 1 := by linarith
  have hεη : 0 < η / (b - a + 1) := div_pos hη hbapos
  have hkey := key (η / (b - a + 1)) hεη
  have hbd : (1 + η / (b - a + 1)) * (b - a) ≤ (b - a) + η := by
    have hle1 : η / (b - a + 1) * (b - a) ≤ η / (b - a + 1) * (b - a + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    rw [div_mul_cancel₀ η (ne_of_gt hbapos)] at hle1
    linarith
  linarith

end Work.Mostow
