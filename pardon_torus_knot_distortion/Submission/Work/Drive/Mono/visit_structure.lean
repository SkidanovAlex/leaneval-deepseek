import Mathlib

namespace Work.Drive.Mono

open Set in
theorem visit_structure {Y : Set ℝ} (hYo : IsOpen Y)
    (hYper : ∀ t : ℝ, t + 2 * Real.pi ∈ Y ↔ t ∈ Y)
    (hYne : ∃ t : ℝ, t ∉ Y) {c : ℝ} (hc : c ∈ Y) :
    c ∈ connectedComponentIn Y c ∧
      connectedComponentIn Y c ⊆ Y ∧
      (connectedComponentIn Y c).OrdConnected ∧
      IsOpen (connectedComponentIn Y c) ∧
      (∃ a b : ℝ, connectedComponentIn Y c ⊆ Set.Icc a b) ∧
      sInf (connectedComponentIn Y c) ∈ closure (connectedComponentIn Y c) ∧
      sSup (connectedComponentIn Y c) ∈ closure (connectedComponentIn Y c) ∧
      sInf (connectedComponentIn Y c) ∉ Y ∧
      sSup (connectedComponentIn Y c) ∉ Y ∧
      closure (connectedComponentIn Y c) ⊆ Set.Icc (sInf (connectedComponentIn Y c))
          (sSup (connectedComponentIn Y c)) ∧
      Set.Ioo (sInf (connectedComponentIn Y c)) (sSup (connectedComponentIn Y c)) ⊆
          connectedComponentIn Y c ∧
      connectedComponentIn Y c ⊆ Set.Ioo (sInf (connectedComponentIn Y c))
          (sSup (connectedComponentIn Y c)) := by
  classical
  set C := connectedComponentIn Y c with hCdef
  have hcC : c ∈ C := mem_connectedComponentIn hc
  have hCY : C ⊆ Y := connectedComponentIn_subset Y c
  have hCoord : C.OrdConnected := isPreconnected_connectedComponentIn.ordConnected
  have hCopen : IsOpen C := hYo.connectedComponentIn
  have hpi : 0 < 2 * Real.pi := by positivity
  have hperNat : ∀ (t : ℝ) (n : ℕ), t + n * (2 * Real.pi) ∈ Y ↔ t ∈ Y := by
    intro t n
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep : t + (↑(n + 1) : ℝ) * (2 * Real.pi) =
          (t + ↑n * (2 * Real.pi)) + 2 * Real.pi := by
        push_cast; ring
      rw [hstep, hYper]
      exact ih
  have hperNeg : ∀ (t : ℝ) (n : ℕ), t - n * (2 * Real.pi) ∈ Y ↔ t ∈ Y := by
    intro t n
    induction n with
    | zero => simp
    | succ n ih =>
      have hstep : t - (↑(n + 1) : ℝ) * (2 * Real.pi) =
          (t - ↑n * (2 * Real.pi)) - 2 * Real.pi := by
        push_cast; ring
      have hYper' : ∀ u : ℝ, u - 2 * Real.pi ∈ Y ↔ u ∈ Y := by
        intro u
        have h := hYper (u - 2 * Real.pi)
        rw [sub_add_cancel] at h
        exact h.symm
      rw [hstep, hYper']
      exact ih
  -- Y is invariant under translations by multiples of 2π, and it is a proper subset
  -- of ℝ, so no connected component of Y can be unbounded.
  have hbddAbove : BddAbove C := by
    by_contra h
    rw [bddAbove_def] at h
    push Not at h
    have hYuniv : Y = univ := by
      ext t
      obtain ⟨n, hn⟩ := exists_nat_ge ((c - t) / (2 * Real.pi))
      have hs : c ≤ t + n * (2 * Real.pi) := by
        have h2 := (div_le_iff₀ hpi).mp hn
        linarith
      obtain ⟨x, hxC, hx⟩ := h (t + n * (2 * Real.pi))
      have hsC : t + n * (2 * Real.pi) ∈ C := hCoord.out hcC hxC ⟨hs, le_of_lt hx⟩
      exact ⟨fun _ => trivial, fun _ => (hperNat t n).mp (hCY hsC)⟩
    obtain ⟨t0, ht0⟩ := hYne
    rw [hYuniv] at ht0
    exact ht0 trivial
  have hbddBelow : BddBelow C := by
    by_contra h
    rw [bddBelow_def] at h
    push Not at h
    have hYuniv : Y = univ := by
      ext t
      obtain ⟨n, hn⟩ := exists_nat_ge ((t - c) / (2 * Real.pi))
      have hs : t - n * (2 * Real.pi) ≤ c := by
        have h2 := (div_le_iff₀ hpi).mp hn
        linarith
      obtain ⟨y, hyC, hy⟩ := h (t - n * (2 * Real.pi))
      have hsC : t - n * (2 * Real.pi) ∈ C := hCoord.out hyC hcC ⟨le_of_lt hy, hs⟩
      exact ⟨fun _ => trivial, fun _ => (hperNeg t n).mp (hCY hsC)⟩
    obtain ⟨t0, ht0⟩ := hYne
    rw [hYuniv] at ht0
    exact ht0 trivial
  have hnonempty : C.Nonempty := ⟨c, hcC⟩
  -- the endpoints of the component are not themselves in C (C is open)
  have haC : sInf C ∉ C := by
    intro ha
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hCopen.mem_nhds ha)
    have hmem : sInf C - ε / 2 ∈ C := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hle := csInf_le hbddBelow hmem
    linarith
  have hbC : sSup C ∉ C := by
    intro hb
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hCopen.mem_nhds hb)
    have hmem : sSup C + ε / 2 ∈ C := by
      apply hball
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hle := le_csSup hbddAbove hmem
    linarith
  -- C is exactly the open interval between its endpoints
  have hIoo_sub : Ioo (sInf C) (sSup C) ⊆ C := by
    intro x hx
    obtain ⟨hax, hxb⟩ := mem_Ioo.mp hx
    obtain ⟨y, hyC, hxy⟩ := (lt_csSup_iff hbddAbove hnonempty).mp hxb
    obtain ⟨z, hzC, hzx⟩ := (csInf_lt_iff hbddBelow hnonempty).mp hax
    exact hCoord.out hzC hyC ⟨le_of_lt hzx, le_of_lt hxy⟩
  have hsub_Ioo : C ⊆ Ioo (sInf C) (sSup C) := by
    intro x hx
    refine mem_Ioo.mpr ⟨?_, ?_⟩
    · refine lt_of_le_of_ne (csInf_le hbddBelow hx) ?_
      intro heq
      exact haC (heq.symm ▸ hx)
    · refine lt_of_le_of_ne (le_csSup hbddAbove hx) ?_
      intro heq
      exact hbC (heq ▸ hx)
  -- the endpoints are not in Y either: otherwise Y would contain a slightly larger
  -- interval meeting C, and maximality of the component would push the endpoint into C
  have haY : sInf C ∉ Y := by
    intro haY
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hYo.mem_nhds haY)
    obtain ⟨hac, hcb⟩ := mem_Ioo.mp (hsub_Ioo hcC)
    have hSY : Ioo (sInf C - ε) (sSup C) ⊆ Y := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := mem_Ioo.mp hx
      rcases lt_or_ge (sInf C) x with hlt | hle
      · exact hCY (hIoo_sub (mem_Ioo.mpr ⟨hlt, hx2⟩))
      · apply hball
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith
    have hcS : c ∈ Ioo (sInf C - ε) (sSup C) := mem_Ioo.mpr ⟨by linarith, hcb⟩
    have hSC : Ioo (sInf C - ε) (sSup C) ⊆ C :=
      isPreconnected_Ioo.subset_connectedComponentIn hcS hSY
    have hmem : sInf C - ε / 2 ∈ C := hSC (mem_Ioo.mpr ⟨by linarith, by linarith⟩)
    obtain ⟨h1, _⟩ := mem_Ioo.mp (hsub_Ioo hmem)
    linarith
  have hbY : sSup C ∉ Y := by
    intro hsY
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hYo.mem_nhds hsY)
    obtain ⟨hac, hcb⟩ := mem_Ioo.mp (hsub_Ioo hcC)
    have hSY : Ioo (sInf C) (sSup C + ε) ⊆ Y := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := mem_Ioo.mp hx
      rcases lt_or_ge x (sSup C) with hlt | hge
      · exact hCY (hIoo_sub (mem_Ioo.mpr ⟨hx1, hlt⟩))
      · apply hball
        rw [Metric.mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith
    have hcS : c ∈ Ioo (sInf C) (sSup C + ε) := mem_Ioo.mpr ⟨hac, by linarith⟩
    have hSC : Ioo (sInf C) (sSup C + ε) ⊆ C :=
      isPreconnected_Ioo.subset_connectedComponentIn hcS hSY
    have hmem : sSup C + ε / 2 ∈ C := hSC (mem_Ioo.mpr ⟨by linarith, by linarith⟩)
    obtain ⟨_, h2⟩ := mem_Ioo.mp (hsub_Ioo hmem)
    linarith
  have hclosure_sub : closure C ⊆ Icc (sInf C) (sSup C) := by
    have hsub : C ⊆ Icc (sInf C) (sSup C) :=
      fun x hx => ⟨le_of_lt (hsub_Ioo hx).1, le_of_lt (hsub_Ioo hx).2⟩
    calc closure C ⊆ closure (Icc (sInf C) (sSup C)) := closure_mono hsub
      _ = Icc (sInf C) (sSup C) := closure_Icc _ _
  have hbounded : ∃ a b : ℝ, C ⊆ Icc a b := by
    obtain ⟨b, hb⟩ := bddAbove_def.mp hbddAbove
    obtain ⟨a, ha⟩ := bddBelow_def.mp hbddBelow
    exact ⟨a, b, fun x hx => ⟨ha x hx, hb x hx⟩⟩
  exact ⟨hcC, hCY, hCoord, hCopen, hbounded, csInf_mem_closure hnonempty hbddBelow,
    csSup_mem_closure hnonempty hbddAbove, haY, hbY, hclosure_sub, hIoo_sub, hsub_Ioo⟩

end Work.Drive.Mono
