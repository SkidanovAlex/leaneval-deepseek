import Mathlib

/-!
# Two reparametrisation tools

* `continuous_choose_range`: the inverse of an injective open map `γ : ℝ → X`, viewed on
  `range γ`, is continuous.
* `exists_continuous_injective_surjective_eqOn_Ioo`: a continuous injection `h : ℝ → ℝ` can be
  changed outside a bounded interval so as to become surjective, keeping it fixed on `Ioo (-N) N`.
  (Used to make two parametrisations of nested arc ranges agree on a growing interval.)
-/

namespace Work.Smooth.SphereJordan.LocalArc

open Set Function

open scoped Topology

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X]

/-- **The inverse of an injective open map, on its range, is continuous.** -/
theorem continuous_choose_range {γ : ℝ → X} (hinj : Function.Injective γ)
    (hopen : IsOpenMap γ) :
    Continuous (fun y : Set.range γ => Classical.choose (Set.mem_range.mp y.2)) := by
  rw [continuous_def]
  intro W hW
  have hset : (fun y : Set.range γ => Classical.choose (Set.mem_range.mp y.2)) ⁻¹' W =
      Subtype.val ⁻¹' (γ '' W) := by
    ext y
    constructor
    · intro hy
      exact ⟨Classical.choose (Set.mem_range.mp y.2), hy,
        Classical.choose_spec (Set.mem_range.mp y.2)⟩
    · rintro ⟨w, hw, hw'⟩
      have h1 : γ (Classical.choose (Set.mem_range.mp y.2)) = γ w := by
        rw [Classical.choose_spec (Set.mem_range.mp y.2), hw']
      have h2 : Classical.choose (Set.mem_range.mp y.2) = w := hinj h1
      show Classical.choose (Set.mem_range.mp y.2) ∈ W
      rw [h2]
      exact hw
  rw [hset]
  exact (hopen W hW).preimage continuous_subtype_val

/-- **A strictly increasing injection on `Ioo (a-1) (b+1)` extends to a surjection of `ℝ`,
linearly off `[a,b]`.** -/
theorem exists_surjective_extend_of_strictMonoOn {h : ℝ → ℝ} (hc : Continuous h)
    {a b : ℝ} (hab : a < b) (hm : StrictMonoOn h (Set.Ioo (a - 1) (b + 1))) :
    ∃ h' : ℝ → ℝ, Continuous h' ∧ Function.Injective h' ∧ Function.Surjective h' ∧
      Set.EqOn h' h (Set.Ioo a b) := by
  have hmemA : a ∈ Set.Ioo (a - 1) (b + 1) := ⟨by linarith, by linarith⟩
  have hmemB : b ∈ Set.Ioo (a - 1) (b + 1) := ⟨by linarith, by linarith⟩
  have hmem : ∀ t ∈ Set.Ioo a b, t ∈ Set.Ioo (a - 1) (b + 1) := by
    intro t ht
    obtain ⟨h1, h2⟩ := ht
    exact ⟨by linarith, by linarith⟩
  have hltab : h a < h b := hm hmemA hmemB hab
  let f : ℝ → ℝ := fun t =>
    if t ≤ a then h a + (t - a) else if b ≤ t then h b + (t - b) else h t
  have A1 : ∀ t, t ≤ a → f t = h a + (t - a) := fun t ht => if_pos ht
  have A3 : ∀ t, b ≤ t → f t = h b + (t - b) := by
    intro t ht
    show (if t ≤ a then h a + (t - a) else if b ≤ t then h b + (t - b) else h t) = _
    rw [if_neg (not_le.mpr (by linarith)), if_pos ht]
  have A2 : ∀ t, a ≤ t → t ≤ b → f t = h t := by
    intro t hat htb
    show (if t ≤ a then h a + (t - a) else if b ≤ t then h b + (t - b) else h t) = h t
    rcases eq_or_lt_of_le hat with h | h
    · rw [h, if_pos le_rfl, sub_self, add_zero]
    · rcases eq_or_lt_of_le htb with h' | h'
      · rw [← h', if_neg (by linarith), if_pos le_rfl, sub_self, add_zero]
      · rw [if_neg (not_le.mpr h), if_neg (by linarith)]
  have hfb : f b = h b := by
    show (if b ≤ a then h a + (b - a) else if b ≤ b then h b + (b - b) else h b) = h b
    rw [if_neg (by linarith), if_pos le_rfl, sub_self, add_zero]
  have B4 : ∀ t, a < t → h a < f t := by
    intro t hat
    rcases lt_trichotomy t b with htb | htb | htb
    · rw [A2 t hat.le htb.le]
      exact hm hmemA (hmem t ⟨hat, htb⟩) hat
    · rw [htb, hfb]
      exact hltab
    · rw [A3 t htb.le]
      linarith
  have B5 : ∀ t, t < b → f t < h b := by
    intro t htb
    rcases lt_trichotomy t a with hta | hta | hta
    · rw [A1 t hta.le]; linarith
    · rw [hta, A2 a le_rfl hab.le]; exact hltab
    · rw [A2 t hta.le htb.le]
      exact hm (hmem t ⟨hta, htb⟩) hmemB htb
  refine ⟨f, ?_, ?_, ?_, fun t ht => A2 t ht.1.le ht.2.le⟩
  · have hinner : Continuous fun t : ℝ => if b ≤ t then h b + (t - b) else h t :=
      Continuous.if_le (continuous_const.add (continuous_id.sub continuous_const)) hc
        continuous_const continuous_id (fun x hx => by rw [hx]; ring)
    refine Continuous.if_le (continuous_const.add (continuous_id.sub continuous_const)) hinner
      continuous_id continuous_const ?_
    intro x hx
    rw [hx]
    show h a + (a - a) = (if b ≤ a then h b + (a - b) else h a)
    rw [sub_self, add_zero, if_neg (by linarith)]
  · intro t₁ t₂ heq
    have hstep : ∀ u v : ℝ, u < v → f u < f v := by
      intro u v huv
      rcases le_or_gt v a with h2 | h2
      · rw [A1 u (le_trans huv.le h2), A1 v h2]; linarith
      · rcases le_or_gt u a with h1 | h1
        · rw [A1 u h1]; linarith [B4 v h2]
        · rcases le_or_gt v b with h2b | h2b
          · rcases eq_or_lt_of_le h2b with h2' | h2''
            · have hb : u < b := by rw [h2'] at huv; exact huv
              rw [h2', A2 u h1.le hb.le, hfb]
              exact hm (hmem u ⟨h1, hb⟩) hmemB hb
            · rw [A2 u h1.le (le_of_lt (lt_trans huv h2'')), A2 v h2.le h2''.le]
              exact hm (hmem u ⟨h1, lt_trans huv h2''⟩) (hmem v ⟨h2, h2''⟩) huv
          · rcases lt_or_ge u b with h1b | h1b
            · rw [A3 v h2b.le]
              have := B5 u h1b
              linarith
            · rw [A3 u h1b, A3 v h2b.le]; linarith
    rcases lt_trichotomy t₁ t₂ with h12 | h12 | h12
    · exact absurd heq (hstep t₁ t₂ h12).ne
    · exact h12
    · exact absurd heq.symm (hstep t₂ t₁ h12).ne
  · intro y
    rcases le_or_gt y (h a) with hy | hy
    · exact ⟨a + (y - h a), by rw [A1 _ (by linarith)]; ring⟩
    · rcases le_or_gt (h b) y with hy2 | hy2
      · exact ⟨b + (y - h b), by rw [A3 _ (by linarith)]; ring⟩
      · have hyI : y ∈ Set.Icc (h a) (h b) := ⟨hy.le, hy2.le⟩
        obtain ⟨t, ht, hty⟩ := intermediate_value_Icc hab.le hc.continuousOn hyI
        exact ⟨t, by rw [A2 t ht.1 ht.2, hty]⟩

/-- **A continuous injective `ℝ → ℝ` becomes surjective after being changed off a bounded
interval, keeping it fixed there.** -/
theorem exists_continuous_injective_surjective_eqOn_Ioo {h : ℝ → ℝ} (hc : Continuous h)
    (hi : Function.Injective h) (N : ℝ) (hN : 0 < N) :
    ∃ h' : ℝ → ℝ, Continuous h' ∧ Function.Injective h' ∧ Function.Surjective h' ∧
      Set.EqOn h' h (Set.Ioo (-N) N) := by
  have hmono : StrictMonoOn h (Set.Ioo (-N - 1) (N + 1)) ∨
      StrictAntiOn h (Set.Ioo (-N - 1) (N + 1)) :=
    ContinuousOn.strictMonoOn_of_injOn_Ioo (by linarith) hc.continuousOn
      (fun x _ y _ hxy => hi hxy)
  rcases hmono with hm | hm
  · exact exists_surjective_extend_of_strictMonoOn hc (by linarith) hm
  · obtain ⟨H', h1, h2, h3, h4⟩ :=
      exists_surjective_extend_of_strictMonoOn (h := fun t => -h t) (by fun_prop)
        (a := -N) (b := N) (by linarith) hm.neg
    refine ⟨fun t => -H' t, by fun_prop, ?_, ?_, ?_⟩
    · intro x y hxy
      exact h2 (neg_injective (by simpa using hxy))
    · intro y
      obtain ⟨x, hx⟩ := h3 (-y)
      exact ⟨x, by show -H' x = y; rw [hx]; ring⟩
    · intro t ht
      have h5 := h4 ht
      simp only [Pi.neg_apply] at h5
      linarith [h5]

end

end Work.Smooth.SphereJordan.LocalArc
