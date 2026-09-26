import Mathlib
import Submission.Commons.Topology.Strip.wall_blocks_translate_path

namespace Commons.Topology.Strip

open Set

/-- **A `T^m`-equivariant plane curve meets its own `p`-translate (for `m ≥ 2`).**

Let `p > 0`, `m ≥ 2`, and let `γ : ℝ → ℝ × ℝ` be continuous with
`γ (s + 1) = γ s + (m*p, 0)` for all `s`.  Then `γ` meets its translate by `(p, 0)`: there are real
`s, t` with `γ s = γ t + (p, 0)`.

**Proof.**  Assume no such pair exists.  Then, by the periodicity, the curve meets no translate by
`(j*m + 1) * p` (`j ∈ ℤ`) either.  Let `A = γ '' [0,1]` be one period of the curve and let
`K = ⋃_{j∈ℤ} (A + (j*m*p, 0))` be the full image of `γ`; it is a closed set, invariant under the
translation by `(m*p, 0)`, and contained in the horizontal strip between the extreme heights of `A`.
The arc `A` is connected and its height-projection meets both extreme heights, so the commons lemma
`wall_blocks_translate_path` applies: *no* translate path from a point `z` of the strip to
`z + (m*p, 0)` avoiding `K` can exist.  But the shifted arc
`σ(u) = γ(u + p) - (p, 0)` (`u ∈ [0,1]`) is exactly such a path: it starts at
`z = γ p - (p,0)`, ends at `z + (m*p, 0)`, stays in the strip and avoids `K`, because a point of
`σ` lying in `K` would exhibit a translate of the curve by `(j*m+1)*p`, contrary to the
hypothesis.  Contradiction. -/
theorem path_meets_translate {p : ℝ} (hp : 0 < p) {m : ℕ} (hm : 2 ≤ m) {γ : ℝ → ℝ × ℝ}
    (hc : Continuous γ)
    (hper : ∀ s : ℝ, γ (s + 1) = ((γ s).1 + m * p, (γ s).2)) :
    ∃ s t : ℝ, γ s = ((γ t).1 + p, (γ t).2) := by
  by_contra hcon
  push Not at hcon
  have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hm2 : (2:ℝ) ≤ (m:ℝ) := by exact_mod_cast hm
  set P : ℝ := (m:ℝ) * p with hPdef
  have hPpos : 0 < P := by rw [hPdef]; exact mul_pos hmpos hp
  have hperP : ∀ s : ℝ, γ (s + 1) = ((γ s).1 + P, (γ s).2) := by
    intro s; rw [hper s, hPdef]
  have hshiftNat : ∀ (n : ℕ) (s : ℝ), γ (s + (n:ℝ)) = ((γ s).1 + (n:ℝ)*P, (γ s).2) := by
    intro n
    induction n with
    | zero => intro s; simp
    | succ k ih =>
      intro s
      have step : γ (s + ((k:ℝ)+1)) = ((γ (s+(k:ℝ))).1 + P, (γ (s+(k:ℝ))).2) := by
        rw [show s + ((k:ℝ)+1) = (s + (k:ℝ)) + 1 by ring]; exact hperP _
      rw [show ((k+1:ℕ):ℝ) = (k:ℝ)+1 by push_cast; ring, step, ih s]
      exact Prod.ext (by ring) rfl
  have hshiftInt : ∀ (j : ℤ) (s : ℝ), γ (s + (j:ℝ)) = ((γ s).1 + (j:ℝ)*P, (γ s).2) := by
    intro j s
    rcases Int.eq_nat_or_neg j with ⟨n, hn | hn⟩
    · rw [hn]; push_cast; exact hshiftNat n s
    · rw [hn]
      have h := hshiftNat n (s + -(n:ℝ))
      rw [show s + -(n:ℝ) + (n:ℝ) = s by ring] at h
      have h1 : (γ s).1 = (γ (s + -(n:ℝ))).1 + (n:ℝ)*P := by simpa using (Prod.ext_iff.mp h).1
      have h2 : (γ s).2 = (γ (s + -(n:ℝ))).2 := by simpa using (Prod.ext_iff.mp h).2
      refine Prod.ext ?_ ?_
      · push_cast; linarith
      · push_cast; linarith
  have hlevel : ∀ (j : ℤ) (s t : ℝ), γ s ≠ ((γ t).1 + (1 + (j:ℝ)*(m:ℝ))*p, (γ t).2) := by
    intro j s t heq
    have h := hshiftInt j t
    have h1 : (γ (t + (j:ℝ))).1 = (γ t).1 + (j:ℝ)*(m:ℝ)*p := by
      have hh : (γ (t + (j:ℝ))).1 = (γ t).1 + (j:ℝ)*P := by simpa using (Prod.ext_iff.mp h).1
      nlinarith [hh, hPdef]
    have h2 : (γ (t + (j:ℝ))).2 = (γ t).2 := by simpa using (Prod.ext_iff.mp h).2
    refine hcon s (t + (j:ℝ)) ?_
    rw [heq]
    exact Prod.ext (by rw [h1]; ring) (by rw [h2])
  set A : Set (ℝ × ℝ) := γ '' Set.Icc (0:ℝ) 1 with hAdef
  have hAcpt : IsCompact A := isCompact_Icc.image hc
  have hAne : A.Nonempty := ⟨γ 0, 0, by norm_num, rfl⟩
  obtain ⟨qmin, hqminA, hqmin⟩ := hAcpt.exists_isMinOn hAne continuous_snd.continuousOn
  obtain ⟨qmax, hqmaxA, hqmax⟩ := hAcpt.exists_isMaxOn hAne continuous_snd.continuousOn
  have hmin_le_max : qmin.2 ≤ qmax.2 := hqmin hqmaxA
  have hyglob : ∀ s : ℝ, qmin.2 ≤ (γ s).2 ∧ (γ s).2 ≤ qmax.2 := by
    intro s
    set n : ℤ := ⌊s⌋ with hn
    have hmem : s - (n:ℝ) ∈ Set.Icc (0:ℝ) 1 :=
      ⟨by have := Int.floor_le s; linarith, by have := Int.lt_floor_add_one s; linarith⟩
    have h := hshiftInt n (s - (n:ℝ))
    rw [show s - (n:ℝ) + (n:ℝ) = s by ring] at h
    rw [show (γ s).2 = (γ (s - (n:ℝ))).2 from by rw [h]]
    exact ⟨hqmin ⟨s - (n:ℝ), hmem, rfl⟩, hqmax ⟨s - (n:ℝ), hmem, rfl⟩⟩
  by_cases hconst : qmin.2 = qmax.2
  · have hconst_all : ∀ s ∈ Set.Icc (0:ℝ) 1, (γ s).2 = (γ 0).2 := by
      intro s hs
      have h1 : qmin.2 ≤ (γ s).2 := hqmin ⟨s, hs, rfl⟩
      have h2 : (γ s).2 ≤ qmax.2 := hqmax ⟨s, hs, rfl⟩
      have h3 : qmin.2 ≤ (γ 0).2 := hqmin ⟨0, by norm_num, rfl⟩
      have h4 : (γ 0).2 ≤ qmax.2 := hqmax ⟨0, by norm_num, rfl⟩
      linarith
    have hfcont : Continuous (fun s : ℝ => (γ s).1) := continuous_fst.comp hc
    have hf1 : (γ 1).1 = (γ 0).1 + (m:ℝ)*p := by
      have h := hper 0
      simp only [zero_add] at h
      rw [h, hPdef]
    obtain ⟨s, hs, hfs⟩ := intermediate_value_Icc (by norm_num : (0:ℝ) ≤ 1)
      hfcont.continuousOn
      (show ((γ 0).1 + p) ∈ Set.Icc ((γ 0).1) ((γ 1).1) from
        ⟨by linarith [hp], by rw [hf1]; nlinarith [hp, hmpos, hm2]⟩)
    exact hcon s 0 (Prod.ext hfs (by rw [hconst_all s hs, hconst_all 0 (by norm_num)]))
  · have hab : qmin.2 < qmax.2 := lt_of_le_of_ne hmin_le_max hconst
    set K : Set (ℝ × ℝ) := qA P ⁻¹' (qA P '' A) with hKdef
    have hKmem : ∀ q : ℝ × ℝ, q ∈ K ↔ ∃ a ∈ A, ∃ j : ℤ,
        q = ((a.1 + (j:ℝ)*P), a.2) := by
      intro q
      constructor
      · intro hq
        obtain ⟨a, haA, haq⟩ := hq
        obtain ⟨n, hn1, hn2⟩ := (qA_eq_iff P a q).mp haq
        exact ⟨a, haA, n, Prod.ext hn1 hn2⟩
      · rintro ⟨a, haA, j, rfl⟩
        refine ⟨a, haA, ?_⟩
        exact (qA_eq_iff P a ((a.1 + (j:ℝ)*P), a.2)).mpr ⟨j, rfl, rfl⟩
    have hKclosed : IsClosed K := by
      rw [hKdef]
      exact (hAcpt.image (qA_continuous P)).isClosed.preimage (qA_continuous P)
    have hKsub : K ⊆ {q : ℝ × ℝ | qmin.2 ≤ q.2 ∧ q.2 ≤ qmax.2} := by
      intro q hq
      obtain ⟨a, haA, j, hj⟩ := (hKmem q).mp hq
      have hq2 : q.2 = a.2 := by simpa using (Prod.ext_iff.mp hj).2
      change qmin.2 ≤ q.2 ∧ q.2 ≤ qmax.2
      rw [hq2]
      exact ⟨hqmin haA, hqmax haA⟩
    have hKper : ∀ q : ℝ × ℝ, q ∈ K ↔ (q.1 + P, q.2) ∈ K := by
      intro q
      rw [hKmem q, hKmem (q.1 + P, q.2)]
      constructor
      · rintro ⟨a, haA, j, hj⟩
        refine ⟨a, haA, j + 1, ?_⟩
        have hj1 : q.1 = a.1 + (j:ℝ)*P := by simpa using (Prod.ext_iff.mp hj).1
        have hj2 : q.2 = a.2 := by simpa using (Prod.ext_iff.mp hj).2
        refine Prod.ext ?_ ?_
        · push_cast; rw [hj1]; ring
        · exact hj2
      · rintro ⟨a, haA, j, hj⟩
        refine ⟨a, haA, j - 1, ?_⟩
        have hj1 : q.1 + P = a.1 + (j:ℝ)*P := by simpa using (Prod.ext_iff.mp hj).1
        have hj2 : q.2 = a.2 := by simpa using (Prod.ext_iff.mp hj).2
        have hj1' : q.1 = a.1 + (j:ℝ)*P - P := by linarith
        refine Prod.ext ?_ ?_
        · push_cast; rw [hj1']; ring
        · exact hj2
    have hA_sub : A ⊆ K := by
      intro a ha
      exact (hKmem a).mpr ⟨a, ha, 0, by refine Prod.ext ?_ ?_ <;> simp⟩
    have hApre : IsPreconnected A := by
      rw [hAdef]; exact isPreconnected_Icc.image γ hc.continuousOn
    have ha_closure : qmin.2 ∈ closure ((fun q : ℝ × ℝ => q.2) '' A) :=
      subset_closure ⟨qmin, hqminA, rfl⟩
    have hb_closure : qmax.2 ∈ closure ((fun q : ℝ × ℝ => q.2) '' A) :=
      subset_closure ⟨qmax, hqmaxA, rfl⟩
    set z : ℝ × ℝ := ((γ p).1 - p, (γ p).2) with hzdef
    have hzK : z ∉ K := by
      intro hz
      obtain ⟨a, haA, j, hj⟩ := (hKmem z).mp hz
      obtain ⟨v, hv, rfl⟩ := haA
      have h1 : (γ p).1 = (γ v).1 + (1 + (j:ℝ)*(m:ℝ))*p := by
        have hh : z.1 = (γ v).1 + (j:ℝ)*P := by simpa using (Prod.ext_iff.mp hj).1
        simp only [hzdef] at hh
        nlinarith [hh, hPdef]
      have h2 : (γ p).2 = (γ v).2 := by simpa using (Prod.ext_iff.mp hj).2
      exact hlevel j p v (Prod.ext h1 h2)
    set σ : C(Set.Icc (0:ℝ) 1, ℝ × ℝ) :=
      ⟨fun u => ((γ ((u:ℝ) + p)).1 - p, (γ ((u:ℝ) + p)).2), by
        apply Continuous.prodMk
        · exact (continuous_fst.comp (hc.comp (continuous_subtype_val.add continuous_const))).sub
            continuous_const
        · exact continuous_snd.comp (hc.comp (continuous_subtype_val.add continuous_const))⟩ with hσdef
    have hσval : ∀ u : Set.Icc (0:ℝ) 1, σ u = ((γ ((u:ℝ) + p)).1 - p, (γ ((u:ℝ) + p)).2) :=
      fun u => rfl
    have hσ0 : σ 0 = z := by
      rw [hσval 0]; simp [hzdef]
    have hσ1 : σ 1 = (z.1 + P, z.2) := by
      have h := hperP p
      rw [hσval 1, show (((1 : Set.Icc (0:ℝ) 1) : ℝ) + p) = p + 1 by rw [show (((1 : Set.Icc (0:ℝ) 1) : ℝ)) = 1 from rfl, add_comm]]
      refine Prod.ext ?_ ?_
      · have h1 : (γ (p+1)).1 = (γ p).1 + P := by simpa using (Prod.ext_iff.mp h).1
        rw [h1, hzdef]; ring
      · have h2 : (γ (p+1)).2 = (γ p).2 := by simpa using (Prod.ext_iff.mp h).2
        rw [h2, hzdef]
    have hσstrip : ∀ u : Set.Icc (0:ℝ) 1, qmin.2 ≤ (σ u).2 ∧ (σ u).2 ≤ qmax.2 := by
      intro u
      rw [hσval u]; exact hyglob ((u:ℝ) + p)
    have hσK : ∀ u : Set.Icc (0:ℝ) 1, σ u ∉ K := by
      intro u hu
      obtain ⟨a, haA, j, hj⟩ := (hKmem (σ u)).mp hu
      obtain ⟨v, hv, rfl⟩ := haA
      have h1 : (γ ((u:ℝ) + p)).1 = (γ v).1 + (1 + (j:ℝ)*(m:ℝ))*p := by
        have hh : (σ u).1 = (γ v).1 + (j:ℝ)*P := by simpa using (Prod.ext_iff.mp hj).1
        simp only [hσval u] at hh
        nlinarith [hh, hPdef]
      have h2 : (γ ((u:ℝ) + p)).2 = (γ v).2 := by
        have h' := (Prod.ext_iff.mp hj).2
        rw [hσval u] at h'
        exact h'
      exact hlevel j ((u:ℝ) + p) v (Prod.ext h1 h2)
    exact wall_blocks_translate_path hPpos hab hKclosed hKsub hKper hA_sub hApre
      ha_closure hb_closure z (hyglob p).1 (hyglob p).2 hzK
      ⟨σ, hσ0, hσ1, hσstrip, hσK⟩

end Commons.Topology.Strip
