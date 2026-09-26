import Mathlib

namespace Work.Drive.Mono.compPeriodic

/-- If `A` is invariant under translation by `T`, it is invariant under translation by any
natural multiple of `T`. -/
lemma add_nat_mul_mem_iff {A : Set ℝ} {T : ℝ} (hAper : ∀ t : ℝ, t + T ∈ A ↔ t ∈ A)
    (n : ℕ) (x : ℝ) : x + n * T ∈ A ↔ x ∈ A := by
  induction n generalizing x with
  | zero => simp
  | succ k ih =>
    have h : x + (k + 1 : ℕ) * T = (x + k * T) + T := by push_cast; ring
    rw [h, hAper, ih]

theorem component_add_nat_mul
    {A : Set ℝ} {T : ℝ} (hT : 0 < T) (hAper : ∀ t : ℝ, t + T ∈ A ↔ t ∈ A)
    (hne : (Aᶜ).Nonempty) :
    ∀ (t : ℝ) (n : ℕ),
      sSup {s : ℝ | s ∉ A ∧ s < t + n * T} = sSup {s : ℝ | s ∉ A ∧ s < t} + n * T ∧
      sInf {s : ℝ | t + n * T < s ∧ s ∉ A} = sInf {s : ℝ | t < s ∧ s ∉ A} + n * T := by
  intro t n
  obtain ⟨p, hp⟩ := hne
  have hper : ∀ x : ℝ, x + (n:ℝ) * T ∈ A ↔ x ∈ A := fun x => add_nat_mul_mem_iff hAper n x
  -- the set of complement points below `t` is nonempty (periodicity lets us go down)
  have hneLT : ({s : ℝ | s ∉ A ∧ s < t}).Nonempty := by
    obtain ⟨k, hk⟩ := exists_nat_gt ((p - t) / T)
    refine ⟨p - (k:ℝ) * T, ?_, ?_⟩
    · intro hmem
      have h1 : p ∈ A ↔ p - (k:ℝ)*T ∈ A := by
        have h2 : (p - (k:ℝ)*T) + (k:ℝ)*T ∈ A ↔ p - (k:ℝ)*T ∈ A :=
          add_nat_mul_mem_iff hAper k _
        rwa [sub_add_cancel] at h2
      exact hp (h1.mpr hmem)
    · have hkT : p - t < (k:ℝ) * T := by
        have := mul_lt_mul_of_pos_right hk hT
        rwa [div_mul_cancel₀ _ hT.ne'] at this
      linarith
  -- the set of complement points above `t` is nonempty
  have hneGT : ({s : ℝ | t < s ∧ s ∉ A}).Nonempty := by
    obtain ⟨k, hk⟩ := exists_nat_gt ((t - p) / T)
    refine ⟨p + (k:ℝ)*T, ?_, ?_⟩
    · have hkT : t - p < (k:ℝ) * T := by
        have := mul_lt_mul_of_pos_right hk hT
        rwa [div_mul_cancel₀ _ hT.ne'] at this
      linarith
    · intro hmem
      have h1 : p + (k:ℝ)*T ∈ A ↔ p ∈ A := add_nat_mul_mem_iff hAper k p
      exact hp (h1.mp hmem)
  have hbddAbove : BddAbove {s : ℝ | s ∉ A ∧ s < t} := ⟨t, fun s hs => le_of_lt hs.2⟩
  have hbddBelow : BddBelow {s : ℝ | t < s ∧ s ∉ A} := ⟨t, fun s hs => le_of_lt hs.1⟩
  -- shifting by `n * T` is an order isomorphism of `ℝ`
  have hsetSup : {s : ℝ | s ∉ A ∧ s < t + (n:ℝ)*T}
      = (OrderIso.addRight ((n:ℝ)*T)) '' {s : ℝ | s ∉ A ∧ s < t} := by
    ext s
    constructor
    · intro hs
      refine ⟨s - (n:ℝ)*T, ⟨?_, ?_⟩, ?_⟩
      · intro hmem
        exact hs.1 (by simpa using (hper (s - (n:ℝ)*T)).mpr hmem)
      · linarith [hs.2]
      · simp
    · rintro ⟨u, hu, rfl⟩
      rw [OrderIso.addRight_apply]
      exact ⟨fun h => hu.1 ((hper u).mp h), by linarith [hu.2]⟩
  have hsetInf : {s : ℝ | t + (n:ℝ)*T < s ∧ s ∉ A}
      = (OrderIso.addRight ((n:ℝ)*T)) '' {s : ℝ | t < s ∧ s ∉ A} := by
    ext s
    constructor
    · intro hs
      refine ⟨s - (n:ℝ)*T, ⟨?_, ?_⟩, ?_⟩
      · linarith [hs.1]
      · intro hmem
        exact hs.2 (by simpa using (hper (s - (n:ℝ)*T)).mpr hmem)
      · simp
    · rintro ⟨u, hu, rfl⟩
      rw [OrderIso.addRight_apply]
      exact ⟨by linarith [hu.1], fun h => hu.2 ((hper u).mp h)⟩
  have hsup : sSup ((OrderIso.addRight ((n:ℝ)*T)) '' {s : ℝ | s ∉ A ∧ s < t})
      = sSup {s : ℝ | s ∉ A ∧ s < t} + (n:ℝ)*T := by
    rw [← OrderIso.map_csSup' (OrderIso.addRight ((n:ℝ)*T)) hneLT hbddAbove,
      OrderIso.addRight_apply]
  have hinf : sInf ((OrderIso.addRight ((n:ℝ)*T)) '' {s : ℝ | t < s ∧ s ∉ A})
      = sInf {s : ℝ | t < s ∧ s ∉ A} + (n:ℝ)*T := by
    rw [← OrderIso.map_csInf' (OrderIso.addRight ((n:ℝ)*T)) hneGT hbddBelow,
      OrderIso.addRight_apply]
  exact ⟨by rw [hsetSup, hsup], by rw [hsetInf, hinf]⟩

end Work.Drive.Mono.compPeriodic
