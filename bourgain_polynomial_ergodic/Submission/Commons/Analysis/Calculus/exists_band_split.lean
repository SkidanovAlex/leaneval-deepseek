import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.GDelta.MetrizableSpace

namespace Commons.Analysis.Calculus

/-- Given a function `g` on `[a,b]` that grows at least linearly with slope `δ`
(`δ * (y-x) ≤ g y - g x` for `x ≤ y` in `[a,b]`) and is continuous there, and a
positive level `m`, there is a window `[p,q] ⊆ [a,b]` of length at most `2m/δ`
with `g ≤ -m` strictly to the left of `p` and `g ≥ m` strictly to the right of
`q`. -/
theorem exists_band_split {a b m δ : ℝ} (hab : a ≤ b) (hm : 0 < m) (hδ : 0 < δ)
    (g : ℝ → ℝ)
    (hcont : ContinuousOn g (Set.Icc a b))
    (hgr : ∀ ⦃x y : ℝ⦄, x ∈ Set.Icc a b → y ∈ Set.Icc a b → x ≤ y →
      δ * (y - x) ≤ g y - g x) :
    ∃ p q : ℝ, a ≤ p ∧ p ≤ q ∧ q ≤ b ∧
      (∀ x : ℝ, x ∈ Set.Ioo a p → g x ≤ -m) ∧
      (∀ x : ℝ, x ∈ Set.Ioo q b → m ≤ g x) ∧
      q - p ≤ 2 * m / δ := by
  -- The set of points of `[a,b]` at which `g ≥ -m`, resp. `g ≤ m`.
  set A : Set ℝ := Set.Icc a b ∩ g ⁻¹' Set.Ici (-m) with hA
  set B : Set ℝ := Set.Icc a b ∩ g ⁻¹' Set.Iic m with hB
  have hAclosed : IsClosed A := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici
  have hBclosed : IsClosed B := hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hmemA : ∀ x : ℝ, x ∈ A ↔ a ≤ x ∧ x ≤ b ∧ -m ≤ g x := by
    intro x; rw [hA]
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_preimage, Set.mem_Ici]
    tauto
  have hmemB : ∀ x : ℝ, x ∈ B ↔ a ≤ x ∧ x ≤ b ∧ g x ≤ m := by
    intro x; rw [hB]
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_preimage, Set.mem_Iic]
    tauto
  -- `A ∪ {b}` is a nonempty set bounded below by `a`;
  -- `B ∪ {a}` is a nonempty set bounded above by `b`.
  have hSbdd : BddBelow (A ∪ {b}) := ⟨a, by
    rintro x (hx | hx)
    · exact ((hmemA x).mp hx).1
    · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hab⟩
  have hTbdd : BddAbove (B ∪ {a}) := ⟨b, by
    rintro x (hx | hx)
    · exact ((hmemB x).mp hx).2.1
    · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hab⟩
  have hSne : (A ∪ {b}).Nonempty := ⟨b, Or.inr (by simp)⟩
  have hTne : (B ∪ {a}).Nonempty := ⟨a, Or.inr (by simp)⟩
  -- Basic order facts about `p := sInf (A ∪ {b})` and `q := sSup (B ∪ {a})`.
  have hp_ge_a : a ≤ sInf (A ∪ {b}) := le_csInf hSne (fun x hx => by
    rcases hx with hx | hx
    · exact ((hmemA x).mp hx).1
    · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hab)
  have hp_le_b : sInf (A ∪ {b}) ≤ b := csInf_le hSbdd (Or.inr (by simp))
  have hq_le_b : sSup (B ∪ {a}) ≤ b := csSup_le hTne (fun x hx => by
    rcases hx with hx | hx
    · exact ((hmemB x).mp hx).2.1
    · rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hab)
  have hq_ge_a : a ≤ sSup (B ∪ {a}) := le_csSup hTbdd (Or.inr (by simp))
  -- `g ≤ -m` on the open interval `(a,p)`.
  have hp_int : ∀ x : ℝ, x ∈ Set.Ioo a (sInf (A ∪ {b})) → g x ≤ -m := by
    intro x hx
    have hxIcc : x ∈ Set.Icc a b := ⟨le_of_lt hx.1, le_trans (le_of_lt hx.2) hp_le_b⟩
    by_contra hg
    have hmx : -m ≤ g x := le_of_lt (not_le.mp hg)
    have : sInf (A ∪ {b}) ≤ x :=
      csInf_le hSbdd (Or.inl ((hmemA x).mpr ⟨hxIcc.1, hxIcc.2, hmx⟩))
    linarith [hx.2]
  -- `g ≥ m` on the open interval `(q,b)`.
  have hq_int : ∀ x : ℝ, x ∈ Set.Ioo (sSup (B ∪ {a})) b → m ≤ g x := by
    intro x hx
    have hxIcc : x ∈ Set.Icc a b := ⟨le_trans hq_ge_a (le_of_lt hx.1), le_of_lt hx.2⟩
    by_contra hg
    have hxm : g x ≤ m := le_of_lt (not_le.mp hg)
    have : x ≤ sSup (B ∪ {a}) :=
      le_csSup hTbdd (Or.inl ((hmemB x).mpr ⟨hxIcc.1, hxIcc.2, hxm⟩))
    linarith [hx.1]
  -- `p ≤ q`: otherwise the midpoint would lie both in `A` and in `B`.
  have hpq : sInf (A ∪ {b}) ≤ sSup (B ∪ {a}) := by
    by_contra h
    have hqp : sSup (B ∪ {a}) < sInf (A ∪ {b}) := not_le.mp h
    set y : ℝ := (sInf (A ∪ {b}) + sSup (B ∪ {a})) / 2 with hy
    have hqy : sSup (B ∪ {a}) < y := by rw [hy]; linarith
    have hyp : y < sInf (A ∪ {b}) := by rw [hy]; linarith
    have hyIcc : y ∈ Set.Icc a b :=
      ⟨le_trans hq_ge_a (le_of_lt hqy), le_trans (le_of_lt hyp) hp_le_b⟩
    have hyA : y ∉ A := by
      intro hAy
      have : sInf (A ∪ {b}) ≤ y := csInf_le hSbdd (Or.inl hAy)
      linarith
    have hyB : y ∉ B := by
      intro hBy
      have : y ≤ sSup (B ∪ {a}) := le_csSup hTbdd (Or.inl hBy)
      linarith
    have hylt : g y < -m := by
      by_contra hc
      exact hyA ((hmemA y).mpr ⟨hyIcc.1, hyIcc.2, not_lt.mp hc⟩)
    have hygt : m < g y := by
      by_contra hc
      exact hyB ((hmemB y).mpr ⟨hyIcc.1, hyIcc.2, not_lt.mp hc⟩)
    linarith
  -- Membership of the extremal points.
  have hSclosed : IsClosed (A ∪ {b}) := hAclosed.union isClosed_singleton
  have hTclosed : IsClosed (B ∪ {a}) := hBclosed.union isClosed_singleton
  have hpS : sInf (A ∪ {b}) ∈ A ∪ {b} := hSclosed.csInf_mem hSne hSbdd
  have hqT : sSup (B ∪ {a}) ∈ B ∪ {a} := hTclosed.csSup_mem hTne hTbdd
  refine ⟨sInf (A ∪ {b}), sSup (B ∪ {a}), hp_ge_a, hpq, hq_le_b, hp_int, hq_int, ?_⟩
  -- Bound on `q - p`.
  rcases hpS with hpA | hpB
  · -- `p ∈ A`
    have hgp : -m ≤ g (sInf (A ∪ {b})) := ((hmemA _).mp hpA).2.2
    rcases hqT with hqB | hqA
    · -- `q ∈ B`: apply the growth condition at `p` and `q`.
      have hgq : g (sSup (B ∪ {a})) ≤ m := ((hmemB _).mp hqB).2.2
      have hpIcc : sInf (A ∪ {b}) ∈ Set.Icc a b :=
        ⟨((hmemA _).mp hpA).1, ((hmemA _).mp hpA).2.1⟩
      have hqIcc : sSup (B ∪ {a}) ∈ Set.Icc a b :=
        ⟨((hmemB _).mp hqB).1, ((hmemB _).mp hqB).2.1⟩
      have hgr' := hgr hpIcc hqIcc hpq
      rw [le_div_iff₀ hδ]
      nlinarith [hgr', hgp, hgq]
    · -- `q = a ≤ p`, so `q - p ≤ 0`.
      have hqa : sSup (B ∪ {a}) = a := by
        rwa [Set.mem_singleton_iff] at hqA
      rw [hqa]
      have h2 : 0 ≤ 2 * m / δ := div_nonneg (by linarith) (le_of_lt hδ)
      linarith [hp_ge_a]
  · -- `p = b`
    have hpb : sInf (A ∪ {b}) = b := by
      rwa [Set.mem_singleton_iff] at hpB
    rcases hqT with hqB | hqA
    · -- `q ≤ b = p`, so `q - p ≤ 0`.
      have hqIccb : sSup (B ∪ {a}) ≤ b := ((hmemB _).mp hqB).2.1
      rw [hpb]
      have h2 : 0 ≤ 2 * m / δ := div_nonneg (by linarith) (le_of_lt hδ)
      linarith [hqIccb]
    · -- `q = a ≤ b = p`, so `q - p = a - b ≤ 0`.
      have hqa : sSup (B ∪ {a}) = a := by
        rwa [Set.mem_singleton_iff] at hqA
      rw [hpb, hqa]
      have h2 : 0 ≤ 2 * m / δ := div_nonneg (by linarith) (le_of_lt hδ)
      linarith [hab]

end Commons.Analysis.Calculus