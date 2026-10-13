import Mathlib
import Submission.Work.WilC4aAL.Defs
import Submission.Work.WilC4aAL.Basic

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
namespace Work.WilC4aAL
open WilkiesDesign.CG.C4a

/-- If `f` is continuous, non-zero at `p` and at `q`, and has no zero strictly between `p` and
`q`, then `f` has the same sign at `p` and at `q`.  This is `sign_eq_of_no_zero_between`
written with `min`/`max` so that no order between the two points has to be established. -/
theorem sign_eq_of_no_zero_between' {f : ℝ → ℝ} (hf : Continuous f) {p q : ℝ}
    (hne : ∀ x ∈ Set.Ioo (min p q) (max p q), f x ≠ 0)
    (hp : f p ≠ 0) (hq : f q ≠ 0) :
    SignType.sign (f p) = SignType.sign (f q) := by
  rcases le_total p q with h | h
  · rw [min_eq_left h, max_eq_right h] at hne
    exact sign_eq_of_no_zero_between h (fun x _ => hf.continuousAt) hne hp hq
  · rw [min_eq_right h, max_eq_left h] at hne
    exact (sign_eq_of_no_zero_between h (fun x _ => hf.continuousAt) hne hq hp).symm

/-- **Cell decomposition, pointwise.**  Fix a parameter value `r`.  Suppose that the real zero set
of every `mpoly (c i) r ·` is contained in the set of branch values `ζ i j r`, and that the
constant `C` strictly dominates every branch value at `r`.  Then for *every* real `z` one of the
fixed finitely many representatives `cand ξ C j` (midpoints of pairs of branch values and the two
constants `±C`) has the same sign vector as `z`. -/
theorem exists_cand_idx_of_root_cover {k : ℕ} {d : Fin k → ℕ} {c : ∀ i, Fin (d i) → ℝ → ℝ}
    {m : Fin k → ℕ} (ζ : ∀ i, Fin (m i) → ℝ → ℝ) {C r z : ℝ}
    (hcover : ∀ i (w : ℝ), WilkiesDesign.CG.C4a.mpoly (c i) r w = 0 → ∃ j, w = ζ i j r)
    (hbd : ∀ i j, |ζ i j r| < C) :
    ∃ j : CandIdx (Σ i : Fin k, Fin (m i)),
      SameSign c r (cand (fun t : Σ i : Fin k, Fin (m i) => ζ t.1 t.2) C j r) z := by
  classical
  -- the finite set of branch values at the parameter value `r`
  let vals : Finset ℝ := Finset.univ.image (fun t : Σ i : Fin k, Fin (m i) => ζ t.1 t.2 r)
  -- every root of every `mpoly (c i) r ·` is a branch value
  have hroot_vals : ∀ (i : Fin k) (w : ℝ), mpoly (c i) r w = 0 → w ∈ vals := by
    intro i w hw
    obtain ⟨j, hj⟩ := hcover i w hw
    exact Finset.mem_image.mpr ⟨⟨i, j⟩, Finset.mem_univ _, hj.symm⟩
  -- every branch value is strictly between `-C` and `C`
  have hhbd : ∀ v ∈ vals, -C < v ∧ v < C := by
    intro v hv
    obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hv
    have h := hbd t.1 t.2
    rw [ht] at h
    exact abs_lt.mp h
  by_cases hzm : z ∈ vals
  · -- Case A: `z` is itself a branch value; take the degenerate midpoint with itself
    obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hzm
    refine ⟨Sum.inl (t, t), ?_⟩
    have hcv : cand (fun t : Σ i : Fin k, Fin (m i) => ζ t.1 t.2) C (Sum.inl (t, t)) r = z := by
      show (ζ t.1 t.2 r + ζ t.1 t.2 r) / 2 = z
      rw [ht]; ring
    rw [hcv]
    exact SameSign.refl c r z
  · -- Cases B, C, D
    have hz : z ∉ vals := hzm
    -- a uniform way to close a case, given the representative value `p` and the fact that the
    -- open interval between `p` and `z` contains no branch value
    have finish : ∀ (j : CandIdx (Σ i : Fin k, Fin (m i))) (p : ℝ),
        cand (fun t : Σ i : Fin k, Fin (m i) => ζ t.1 t.2) C j r = p → p ∉ vals →
        (∀ v ∈ vals, v ∉ Set.Ioo (min p z) (max p z)) →
        SameSign c r (cand (fun t : Σ i : Fin k, Fin (m i) => ζ t.1 t.2) C j r) z := by
      intro j p hj hp havoid i
      rw [hj]
      refine sign_eq_of_no_zero_between' (continuous_mpoly_right (c i) r) ?_ ?_ ?_
      · intro x hx hx0
        exact havoid x (hroot_vals i x hx0) hx
      · intro h0
        exact hp (hroot_vals i p h0)
      · intro h0
        exact hz (hroot_vals i z h0)
    -- the branch indices whose value is below / above `z`
    let below : Finset (Σ i : Fin k, Fin (m i)) :=
      Finset.univ.filter (fun t => ζ t.1 t.2 r < z)
    let above : Finset (Σ i : Fin k, Fin (m i)) :=
      Finset.univ.filter (fun t => z < ζ t.1 t.2 r)
    by_cases hbelow : below.Nonempty
    · by_cases habove : above.Nonempty
      · -- Case D: branch values on both sides of `z`; take the midpoint of the closest pair
        obtain ⟨ta, hta_mem, hta_max⟩ :=
          Finset.exists_max_image below (fun t : Σ i : Fin k, Fin (m i) => ζ t.1 t.2 r) hbelow
        obtain ⟨tb, htb_mem, htb_min⟩ :=
          Finset.exists_min_image above (fun t : Σ i : Fin k, Fin (m i) => ζ t.1 t.2 r) habove
        have ha_lt : ζ ta.1 ta.2 r < z := (Finset.mem_filter.mp hta_mem).2
        have hb_gt : z < ζ tb.1 tb.2 r := (Finset.mem_filter.mp htb_mem).2
        -- every branch value is `≤ a` or `≥ b`
        have hno_between : ∀ v ∈ vals, v ≤ ζ ta.1 ta.2 r ∨ ζ tb.1 tb.2 r ≤ v := by
          intro v hv
          obtain ⟨t', -, ht'⟩ := Finset.mem_image.mp hv
          by_cases hvz : v < z
          · left
            have h' := hta_max t'
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [ht']; exact hvz⟩)
            rwa [ht'] at h'
          · right
            have hzv : z < v := by
              rcases lt_trichotomy v z with h | h | h
              · exact absurd h hvz
              · exact absurd (h ▸ hv) hz
              · exact h
            have h' := htb_min t'
              (Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [ht']; exact hzv⟩)
            rwa [ht'] at h'
        refine ⟨Sum.inl (ta, tb), finish (Sum.inl (ta, tb))
          ((ζ ta.1 ta.2 r + ζ tb.1 tb.2 r) / 2) rfl ?_ ?_⟩
        · -- the midpoint is not a branch value
          intro hmem
          rcases hno_between _ hmem with h | h <;> linarith
        · -- no branch value lies between the midpoint and `z`
          intro v hv hmem
          rcases hno_between v hv with h | h
          · have hmin : ζ ta.1 ta.2 r < min ((ζ ta.1 ta.2 r + ζ tb.1 tb.2 r) / 2) z :=
              lt_min (by linarith) ha_lt
            exact (lt_asymm (lt_of_le_of_lt h hmin)) hmem.1
          · have hmax : max ((ζ ta.1 ta.2 r + ζ tb.1 tb.2 r) / 2) z < ζ tb.1 tb.2 r :=
              max_lt (by linarith) hb_gt
            exact (lt_asymm (lt_of_lt_of_le hmax h)) hmem.2
      · -- Case C: every branch value is `< z`; take `+C`
        have hlt : ∀ v ∈ vals, v < z := by
          intro v hv
          obtain ⟨t', -, ht'⟩ := Finset.mem_image.mp hv
          have hnvab : ¬ z < v := by
            intro h
            exact habove ⟨t', by
              rw [Finset.mem_filter]
              exact ⟨Finset.mem_univ _, by rw [ht']; exact h⟩⟩
          rcases lt_trichotomy v z with h | h | h
          · exact h
          · exact absurd (h ▸ hv) hz
          · exact absurd h hnvab
        refine ⟨Sum.inr true, finish (Sum.inr true) C rfl ?_ ?_⟩
        · intro hmem
          exact absurd (hhbd C hmem).2 (lt_irrefl C)
        · intro v hv hmem
          have hmin : v < min C z := lt_min (hhbd v hv).2 (hlt v hv)
          exact (lt_asymm hmin) hmem.1
    · -- Case B: every branch value is `> z` (or there are none); take `-C`
      have hgt : ∀ v ∈ vals, z < v := by
        intro v hv
        obtain ⟨t', -, ht'⟩ := Finset.mem_image.mp hv
        have hnvbe : ¬ v < z := by
          intro h
          exact hbelow ⟨t', by
            rw [Finset.mem_filter]
            exact ⟨Finset.mem_univ _, by rw [ht']; exact h⟩⟩
        rcases lt_trichotomy v z with h | h | h
        · exact absurd h hnvbe
        · exact absurd (h ▸ hv) hz
        · exact h
      refine ⟨Sum.inr false, finish (Sum.inr false) (-C) rfl ?_ ?_⟩
      · intro hmem
        exact absurd (hhbd (-C) hmem).1 (lt_irrefl (-C))
      · intro v hv hmem
        have hmax : max (-C) z < v := max_lt (hhbd v hv).1 (hgt v hv)
        exact (lt_asymm hmax) hmem.2

end Work.WilC4aAL
