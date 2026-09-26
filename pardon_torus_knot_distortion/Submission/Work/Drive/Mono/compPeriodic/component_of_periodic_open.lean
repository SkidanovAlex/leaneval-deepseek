import Mathlib

namespace Work.Drive.Mono.compPeriodic

theorem component_of_periodic_open
    {A : Set ℝ} {T : ℝ} (hT : 0 < T) (hAopen : IsOpen A)
    (hAper : ∀ t : ℝ, t + T ∈ A ↔ t ∈ A) (hne : (Aᶜ).Nonempty) :
    ∀ t ∈ A, sSup {s : ℝ | s ∉ A ∧ s < t} < t ∧
      t < sInf {s : ℝ | t < s ∧ s ∉ A} ∧
      Set.Ioo (sSup {s : ℝ | s ∉ A ∧ s < t}) (sInf {s : ℝ | t < s ∧ s ∉ A}) ⊆ A ∧
      sSup {s : ℝ | s ∉ A ∧ s < t} ∈ closure A ∧
      sInf {s : ℝ | t < s ∧ s ∉ A} ∈ closure A ∧
      sSup {s : ℝ | s ∉ A ∧ s < t} ∉ A ∧
      sInf {s : ℝ | t < s ∧ s ∉ A} ∉ A := by
  -- Iterated periodicity: shifting by a natural multiple of `T` preserves membership in `A`.
  have hplus : ∀ (x : ℝ) (n : ℕ), x ∉ A → x + n * T ∉ A := by
    intro x n hx
    induction n with
    | zero => simpa using hx
    | succ k ih =>
      have h1 : x + (↑(k + 1) : ℝ) * T = (x + ↑k * T) + T := by push_cast; ring
      rw [h1]
      intro h
      exact ih ((hAper (x + ↑k * T)).mp h)
  have hminus : ∀ (x : ℝ) (n : ℕ), x ∉ A → x - n * T ∉ A := by
    intro x n hx
    induction n with
    | zero => simpa using hx
    | succ k ih =>
      have h1 : x - (↑(k + 1) : ℝ) * T = (x - ↑k * T) - T := by push_cast; ring
      rw [h1]
      intro h
      have h2 : ((x - ↑k * T) - T) + T ∈ A := (hAper ((x - ↑k * T) - T)).mpr h
      have h3 : ((x - ↑k * T) - T) + T = x - ↑k * T := by ring
      rw [h3] at h2
      exact ih h2
  intro t htA
  obtain ⟨x, hx⟩ := hne
  set L : Set ℝ := {s : ℝ | s ∉ A ∧ s < t} with hL
  set R : Set ℝ := {s : ℝ | t < s ∧ s ∉ A} with hR
  -- The two "component" sets are nonempty, by periodicity.
  have hLne : L.Nonempty := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((x - t) / T)
    rw [div_lt_iff₀ hT] at hn
    refine ⟨x - n * T, ?_⟩
    rw [hL]
    exact ⟨hminus x n hx, by linarith⟩
  have hRne : R.Nonempty := by
    obtain ⟨n, hn⟩ := exists_nat_gt ((t - x) / T)
    rw [div_lt_iff₀ hT] at hn
    refine ⟨x + n * T, ?_⟩
    rw [hR]
    exact ⟨by linarith, hplus x n hx⟩
  have hLbdd : BddAbove L := ⟨t, fun b hb => by rw [hL] at hb; exact le_of_lt hb.2⟩
  have hRbdd : BddBelow R := ⟨t, fun b hb => by rw [hR] at hb; exact le_of_lt hb.1⟩
  -- `A` is open at `t`, giving a symmetric interval inside `A`.
  obtain ⟨δ, hδpos, hδ⟩ : ∃ δ > 0, Set.Ioo (t - δ) (t + δ) ⊆ A := by
    obtain ⟨ε, hεpos, hεsub⟩ := (Metric.isOpen_iff.mp hAopen) t htA
    rw [Real.ball_eq_Ioo] at hεsub
    exact ⟨ε, hεpos, hεsub⟩
  -- Consequently `L` lives below `t - δ` and `R` above `t + δ`.
  have hLsub : ∀ b ∈ L, b ≤ t - δ := by
    intro b hb
    rw [hL] at hb
    obtain ⟨hbA, hbt⟩ := hb
    by_contra h
    rw [not_le] at h
    exact hbA (hδ ⟨h, by linarith⟩)
  have hRsub : ∀ b ∈ R, t + δ ≤ b := by
    intro b hb
    rw [hR] at hb
    obtain ⟨htb, hbA⟩ := hb
    by_contra h
    rw [not_le] at h
    exact hbA (hδ ⟨by linarith, h⟩)
  have hLsSup_le : sSup L ≤ t - δ := csSup_le hLne hLsub
  have hLsSup_lt_t : sSup L < t := by linarith
  have hRsInf_ge : t + δ ≤ sInf R := le_csInf hRne hRsub
  have ht_lt_sInfR : t < sInf R := by linarith
  -- Everything strictly between the two ends lies in `A`.
  have hIoo : Set.Ioo (sSup L) (sInf R) ⊆ A := by
    rintro s ⟨hsl, hsr⟩
    by_contra hsA
    rcases lt_trichotomy s t with h | h | h
    · have : s ≤ sSup L := le_csSup hLbdd (by rw [hL]; exact ⟨hsA, h⟩)
      linarith
    · rw [h] at hsA
      exact hsA htA
    · have : sInf R ≤ s := csInf_le hRbdd (by rw [hR]; exact ⟨h, hsA⟩)
      linarith
  -- `sSup L` is not in `A` (else `A` would contain points of `L` above `sSup L - ε`).
  have hsSupL_notin : sSup L ∉ A := by
    intro hmem
    obtain ⟨ε, hεpos, hεsub⟩ := (Metric.isOpen_iff.mp hAopen) (sSup L) hmem
    rw [Real.ball_eq_Ioo] at hεsub
    obtain ⟨b, hbL, hbgt⟩ := (lt_csSup_iff hLbdd hLne).mp (show sSup L - ε < sSup L by linarith)
    have hble : b ≤ sSup L := le_csSup hLbdd hbL
    rw [hL] at hbL
    exact hbL.1 (hεsub ⟨hbgt, by linarith⟩)
  have hsInfR_notin : sInf R ∉ A := by
    intro hmem
    obtain ⟨ε, hεpos, hεsub⟩ := (Metric.isOpen_iff.mp hAopen) (sInf R) hmem
    rw [Real.ball_eq_Ioo] at hεsub
    obtain ⟨b, hbR, hblt⟩ := (csInf_lt_iff hRbdd hRne).mp (show sInf R < sInf R + ε by linarith)
    have hble : sInf R ≤ b := csInf_le hRbdd hbR
    rw [hR] at hbR
    exact hbR.2 (hεsub ⟨by linarith, hblt⟩)
  -- ... but it is in the closure, since the interval above it lies in `A`.
  have hsSupL_closure : sSup L ∈ closure A := by
    have hsub : Set.Ioo (sSup L) t ⊆ A := fun s hs =>
      hIoo ⟨hs.1, by linarith [hs.2, ht_lt_sInfR]⟩
    have hmem : sSup L ∈ closure (Set.Ioo (sSup L) t) := by
      rw [closure_Ioo (ne_of_lt hLsSup_lt_t)]
      exact ⟨le_rfl, le_of_lt hLsSup_lt_t⟩
    exact closure_mono hsub hmem
  have hsInfR_closure : sInf R ∈ closure A := by
    have hsub : Set.Ioo t (sInf R) ⊆ A := fun s hs =>
      hIoo ⟨by linarith [hs.1, hLsSup_lt_t], hs.2⟩
    have hmem : sInf R ∈ closure (Set.Ioo t (sInf R)) := by
      rw [closure_Ioo (ne_of_lt ht_lt_sInfR)]
      exact ⟨le_of_lt ht_lt_sInfR, le_rfl⟩
    exact closure_mono hsub hmem
  exact ⟨hLsSup_lt_t, ht_lt_sInfR, hIoo, hsSupL_closure, hsInfR_closure,
    hsSupL_notin, hsInfR_notin⟩

end Work.Drive.Mono.compPeriodic
