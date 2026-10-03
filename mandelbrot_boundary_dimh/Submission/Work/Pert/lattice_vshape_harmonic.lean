import Mathlib

/-!
# Harmonic sums along a monotone "V-shaped" lattice walk

This file proves `Work.Pert.lattice_vshape_harmonic`: if `Y : ℕ → ℝ` is monotone on `{0,…,n-1}`
with increments of modulus at least `ν` and stays inside `[-M, M]`, then

`∑_{j<n} 1 / max |Y j| H ≤ (2/ν) (2 + log (1 + M/H)) + 2/H`.

The walk moves monotonically, so `|Y ·|` is V-shaped: it decreases towards the crossing of `0`
and increases afterwards; on each of the two branches `|Y j|` grows at rate `ν` away from the
crossing, so each branch contributes at most one "harmonic tail" sum.  The crossing index is
`m = #{j < n : Y j < 0}` (a down-closed set, hence an initial segment), and each branch is
compared with the range sum `∑_{l < L} 1/max (l ν) H`, estimated in `sum_max_lattice_arith`
below (`Work.Pert.sum_inv_max_lattice` is the same statement, proved separately).

The non-increasing case is reduced to the increasing one by negating `Y`.
-/

namespace Work.Pert

/-- Monotone-growth Lemma: if the increments of `Y` on `{0,…,n-1}` are at least `ν`, then
`Y i + (j-i) ν ≤ Y j` for `i ≤ j < n`. -/
private lemma mono_step {Y : ℕ → ℝ} {ν : ℝ} {n : ℕ} (hstep : ∀ j < n, ν ≤ Y (j + 1) - Y j)
    {i j : ℕ} (hij : i ≤ j) (hjn : j < n) : Y i + ((j - i : ℕ) : ℝ) * ν ≤ Y j := by
  have key : ∀ d : ℕ, i + d ≤ j → Y i + (d : ℝ) * ν ≤ Y (i + d) := by
    intro d
    induction d with
    | zero => intro _; simp
    | succ d ih =>
        intro hd
        have hdj : i + d ≤ j := by omega
        have hlt : i + d < n := by omega
        have h1 : Y i + (d : ℝ) * ν ≤ Y (i + d) := ih hdj
        have h2 : ν ≤ Y (i + d + 1) - Y (i + d) := hstep (i + d) hlt
        have h3 : Y (i + d + 1) = Y (i + (d + 1)) := by rw [Nat.add_assoc]
        rw [h3] at h2
        have h4 : ((d : ℝ) + 1) * ν = (d : ℝ) * ν + ν := by ring
        push_cast
        rw [h4]
        linarith
  have := key (j - i) (by omega)
  rwa [Nat.add_sub_of_le hij] at this

/-- A down-closed finite set of naturals is an initial segment. -/
private lemma downclosed_eq_range (S : Finset ℕ) (h : ∀ j ∈ S, ∀ i ≤ j, i ∈ S) :
    S = Finset.range S.card := by
  have hsub : S ⊆ Finset.range S.card := by
    intro i hi
    rw [Finset.mem_range]
    have h1 : Finset.range (i + 1) ⊆ S := by
      intro k hk
      rw [Finset.mem_range] at hk
      exact h i hi k (Nat.lt_succ_iff.mp hk)
    have h2 : (Finset.range (i + 1)).card ≤ S.card := Finset.card_le_card h1
    simpa using h2
  exact Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_range])

/-- Harmonic range bound: `∑_{i ≤ d} 1/(a+i) ≤ 1 + log ((a+d)/a)` for `a ≥ 1`. -/
private lemma harm_range_bound {a d : ℕ} (ha : 1 ≤ a) :
    (∑ i ∈ Finset.range (d + 1), (1 : ℝ) / ((a + i : ℕ) : ℝ))
      ≤ 1 + Real.log (((a + d : ℕ) : ℝ) / (a : ℝ)) := by
  have hterm : ∀ i ∈ Finset.range d,
      (1 : ℝ) / ((a + (i + 1) : ℕ) : ℝ)
        ≤ Real.log (((a + (i + 1) : ℕ) : ℝ)) - Real.log (((a + i : ℕ) : ℝ)) := by
    intro i _
    have hcast : ((a + (i + 1) : ℕ) : ℝ) = ((a + i : ℕ) : ℝ) + 1 := by push_cast; ring
    have hx : (0 : ℝ) < (((a + i : ℕ) : ℝ) + 1) / ((a + i : ℕ) : ℝ) := by positivity
    have h := Real.one_sub_inv_le_log_of_pos hx
    rw [inv_div] at h
    have h1 : (1 : ℝ) - ((a + i : ℕ) : ℝ) / (((a + i : ℕ) : ℝ) + 1)
        = 1 / (((a + i : ℕ) : ℝ) + 1) := by
      field_simp
      ring
    have h2 : Real.log ((((a + i : ℕ) : ℝ) + 1) / ((a + i : ℕ) : ℝ))
        = Real.log (((a + i : ℕ) : ℝ) + 1) - Real.log (((a + i : ℕ) : ℝ)) :=
      Real.log_div (by positivity) (by positivity)
    rw [h1, h2] at h
    rw [hcast]
    exact h
  have hsum := Finset.sum_le_sum hterm
  have htel : ∑ k ∈ Finset.range d,
      (Real.log (((a + (k + 1) : ℕ) : ℝ)) - Real.log (((a + k : ℕ) : ℝ)))
      = Real.log (((a + d : ℕ) : ℝ)) - Real.log ((a : ℕ) : ℝ) := by
    have h := Finset.sum_range_sub (fun k : ℕ => Real.log (((a + k : ℕ) : ℝ))) d
    simpa using h
  rw [Finset.sum_range_succ']
  have h0 : (1 : ℝ) / ((a + 0 : ℕ) : ℝ) = 1 / (a : ℝ) := by simp
  rw [h0]
  have ha1 : (1 : ℝ) / (a : ℝ) ≤ 1 := by
    rw [div_le_one (by positivity)]
    exact_mod_cast ha
  have hlog : Real.log (((a + d : ℕ) : ℝ) / (a : ℝ))
      = Real.log (((a + d : ℕ) : ℝ)) - Real.log ((a : ℕ) : ℝ) :=
    Real.log_div (by positivity) (by positivity)
  rw [hlog]
  linarith

/-- Arithmetic core: for `L : ℕ` with `(L-1) ν ≤ M`, the range sum of `1/max (l ν) H` is at
most `2/ν + 1/H + (1/ν) log (1 + M/H)`.

Split the indices at `t = #{l < L : l ν ≤ H}` (a down-closed set).  The indices `l < t` each
contribute `1/H`, and `t ≤ H/ν + 1` because `t-1` is still in the set.  The indices `l ≥ t`
contribute `1/(lν)`, a harmonic range sum which telescopes against `log`: the truncation
`(L-1) ν ≤ M` gives the ratio bound `(L-1)/t ≤ M/H`. -/
private lemma sum_max_lattice_arith {ν H M : ℝ} (hν : 0 < ν) (hH : 0 < H) (hM0 : 0 ≤ M)
    {L : ℕ} (hL : ((L : ℝ) - 1) * ν ≤ M) :
    (∑ l ∈ Finset.range L, 1 / max ((l : ℝ) * ν) H)
      ≤ 2 / ν + 1 / H + (1 / ν) * Real.log (1 + M / H) := by
  set S : Finset ℕ := (Finset.range L).filter (fun l => (l : ℝ) * ν ≤ H) with hSdef
  set t : ℕ := S.card with htdef
  have hSdown : ∀ j ∈ S, ∀ i ≤ j, i ∈ S := by
    intro j hj i hij
    rw [hSdef] at hj ⊢
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    obtain ⟨hjL, hjν⟩ := hj
    refine ⟨lt_of_le_of_lt hij hjL, ?_⟩
    have : (i : ℝ) * ν ≤ (j : ℝ) * ν := by
      apply mul_le_mul_of_nonneg_right _ (le_of_lt hν)
      exact_mod_cast hij
    linarith
  have hSeq : S = Finset.range t := by rw [htdef]; exact downclosed_eq_range S hSdown
  have hmem : ∀ l, l ∈ S ↔ l < t := by intro l; rw [hSeq, Finset.mem_range]
  have hmem' : ∀ l, l ∈ S ↔ (l < L ∧ (l : ℝ) * ν ≤ H) := by
    intro l; rw [hSdef, Finset.mem_filter, Finset.mem_range]
  have htle : t ≤ L := by
    have := Finset.card_le_card
      (Finset.filter_subset (fun l : ℕ => (l : ℝ) * ν ≤ H) (Finset.range L))
    simpa [htdef, hSdef, Finset.card_range] using this
  have hpartA : (∑ l ∈ Finset.range t, 1 / max ((l : ℝ) * ν) H) ≤ 1 / ν + 1 / H := by
    have hconst : (∑ l ∈ Finset.range t, 1 / max ((l : ℝ) * ν) H) = (t : ℝ) / H := by
      have h1 : ∀ l ∈ Finset.range t, 1 / max ((l : ℝ) * ν) H = 1 / H := by
        intro l hl
        have hlS : l ∈ S := (hmem l).mpr (Finset.mem_range.mp hl)
        rw [max_eq_right ((hmem' l).mp hlS).2]
      rw [Finset.sum_congr rfl h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    rw [hconst]
    have htbound : (t : ℝ) ≤ H / ν + 1 := by
      rcases Nat.eq_zero_or_pos t with h0 | hpos
      · rw [h0]
        have hnn : (0 : ℝ) ≤ H / ν + 1 := by
          have := div_nonneg (le_of_lt hH) (le_of_lt hν)
          linarith
        simpa using hnn
      · have hmemS : t - 1 ∈ S := (hmem (t - 1)).mpr (by omega)
        have h2 := (hmem' (t - 1)).mp hmemS
        have hcast : ((t - 1 : ℕ) : ℝ) = (t : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ t)]; norm_num
        have h3' : ((t : ℝ) - 1) * ν ≤ H := by
          rw [← hcast]
          exact h2.2
        have h3 : ((t : ℝ) - 1) ≤ H / ν := (le_div_iff₀ hν).mpr h3'
        linarith
    have hmono := div_le_div_of_nonneg_right htbound (le_of_lt hH)
    have heq : (H / ν + 1) / H = 1 / ν + 1 / H := by field_simp
    linarith [hmono, heq.le]
  have hpartB : (∑ i ∈ Finset.range (L - t), 1 / max (((t + i : ℕ) : ℝ) * ν) H)
      ≤ (1 / ν) * (1 + Real.log (1 + M / H)) := by
    rcases Nat.eq_zero_or_pos (L - t) with h0 | hpos
    · rw [h0, Finset.range_zero, Finset.sum_empty]
      have hnn : (0 : ℝ) ≤ 1 / ν * (1 + Real.log (1 + M / H)) := by
        have hMdiv : (0 : ℝ) ≤ M / H := div_nonneg hM0 (le_of_lt hH)
        have hlog : (0 : ℝ) ≤ Real.log (1 + M / H) := Real.log_nonneg (by linarith)
        have hiv : (0 : ℝ) < 1 / ν := by positivity
        exact mul_nonneg (le_of_lt hiv) (by linarith)
      exact hnn
    · have htL : t < L := by omega
      have ht1 : 1 ≤ t := by
        have h0mem : (0 : ℕ) ∈ S := by
          refine (hmem' 0).mpr ⟨by omega, ?_⟩
          have h0c : ((0 : ℕ) : ℝ) = (0 : ℝ) := by norm_num
          rw [h0c, zero_mul]
          exact le_of_lt hH
        have := (hmem 0).mp h0mem
        omega
      have htpos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht1
      have hnotS : ¬ ((t : ℝ) * ν ≤ H) := by
        intro hc
        have : t ∈ S := (hmem' t).mpr ⟨htL, hc⟩
        have := (hmem t).mp this
        omega
      have hgt : H < (t : ℝ) * ν := not_le.mp hnotS
      have hval : ∀ i ∈ Finset.range (L - t),
          1 / max (((t + i : ℕ) : ℝ) * ν) H = 1 / (((t + i : ℕ) : ℝ) * ν) := by
        intro i hi
        have hle : H ≤ ((t + i : ℕ) : ℝ) * ν := by
          have hcast : (t : ℝ) ≤ ((t + i : ℕ) : ℝ) := by
            push_cast; exact_mod_cast Nat.le_add_right t i
          nlinarith [hgt, hν, hcast]
        rw [max_eq_left hle]
      rw [Finset.sum_congr rfl hval]
      have hfac : (∑ i ∈ Finset.range (L - t), 1 / (((t + i : ℕ) : ℝ) * ν))
          = (1 / ν) * (∑ i ∈ Finset.range (L - t), 1 / ((t + i : ℕ) : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        have hcastpos : (0 : ℝ) < ((t + i : ℕ) : ℝ) := by
          have : 0 < t + i := by omega
          exact_mod_cast this
        field_simp
      rw [hfac]
      have hrange : (L - 1 - t) + 1 = L - t := by omega
      have hharm := harm_range_bound (a := t) (d := L - 1 - t) ht1
      have hcast2 : ((t + (L - 1 - t) : ℕ) : ℝ) = ((L - 1 : ℕ) : ℝ) :=
        congrArg (fun k : ℕ => ((k : ℕ) : ℝ)) (by omega : t + (L - 1 - t) = L - 1)
      rw [hcast2, hrange] at hharm
      have hratio : ((L - 1 : ℕ) : ℝ) / (t : ℝ) ≤ M / H := by
        have hLcast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ L)]; norm_num
        have h1 : ((L - 1 : ℕ) : ℝ) * ν ≤ M := by rw [hLcast]; exact hL
        have hkey : ((L - 1 : ℕ) : ℝ) * H ≤ M * (t : ℝ) := by
          have h2 : ((L - 1 : ℕ) : ℝ) * H ≤ ((L - 1 : ℕ) : ℝ) * ((t : ℝ) * ν) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            linarith [hgt]
          have h3 : ((L - 1 : ℕ) : ℝ) * ((t : ℝ) * ν) = (((L - 1 : ℕ) : ℝ) * ν) * (t : ℝ) := by
            ring
          rw [h3] at h2
          have h4 : (((L - 1 : ℕ) : ℝ) * ν) * (t : ℝ) ≤ M * (t : ℝ) :=
            mul_le_mul_of_nonneg_right h1 (Nat.cast_nonneg t)
          linarith
        rw [div_le_iff₀ htpos]
        have : M / H * (t : ℝ) = M * (t : ℝ) / H := by ring
        rw [this, le_div_iff₀ hH]
        exact hkey
      have hratio1 : (1 : ℝ) ≤ ((L - 1 : ℕ) : ℝ) / (t : ℝ) := by
        rw [le_div_iff₀ htpos]
        have h4 : (t : ℝ) ≤ ((L - 1 : ℕ) : ℝ) := by
          exact_mod_cast (by omega : t ≤ L - 1)
        linarith
      have hMpos : (0 : ℝ) < M / H := by linarith
      have hlog1 : Real.log (((L - 1 : ℕ) : ℝ) / (t : ℝ)) ≤ Real.log (M / H) :=
        Real.log_le_log (by linarith) hratio
      have hlog2 : Real.log (M / H) ≤ Real.log (1 + M / H) :=
        Real.log_le_log hMpos (by linarith)
      have hstep : (1 / ν) * (∑ i ∈ Finset.range (L - t), 1 / ((t + i : ℕ) : ℝ))
          ≤ (1 / ν) * (1 + Real.log (1 + M / H)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith [hharm, hlog1, hlog2]
      exact hstep
  have hsplit : (∑ l ∈ Finset.range L, 1 / max ((l : ℝ) * ν) H)
      = (∑ l ∈ Finset.range t, 1 / max ((l : ℝ) * ν) H)
        + ∑ i ∈ Finset.range (L - t), 1 / max (((t + i : ℕ) : ℝ) * ν) H := by
    have h := Finset.sum_range_add (fun l : ℕ => 1 / max ((l : ℝ) * ν) H) t (L - t)
    rwa [Nat.add_sub_of_le htle] at h
  rw [hsplit]
  have hfin : (1 / ν + 1 / H) + (1 / ν) * (1 + Real.log (1 + M / H))
      = 2 / ν + 1 / H + (1 / ν) * Real.log (1 + M / H) := by
    ring
  linarith [hpartA, hpartB, hfin.le]

/-- The V-shape estimate for a *monotone* walk: the two branches of `|Y ·|` (before and after the
crossing of `0`) each contribute at most the arithmetic bound of `sum_max_lattice_arith`. -/
private theorem vshape_mono {Y : ℕ → ℝ} {ν H M : ℝ} {n : ℕ}
    (hν : 0 < ν) (hH : 0 < H) (hM0 : 0 ≤ M)
    (hstep : ∀ j < n, ν ≤ |Y (j + 1) - Y j|)
    (hmono : ∀ j < n, Y j ≤ Y (j + 1))
    (hM : ∀ j < n, |Y j| ≤ M)
    (arith : ∀ {ν H M : ℝ}, 0 < ν → 0 < H → 0 ≤ M → ∀ {L : ℕ}, ((L : ℝ) - 1) * ν ≤ M →
      (∑ l ∈ Finset.range L, 1 / max ((l : ℝ) * ν) H)
        ≤ 2 / ν + 1 / H + (1 / ν) * Real.log (1 + M / H)) :
    (∑ j ∈ Finset.range n, 1 / max |Y j| H) ≤ (2 / ν) * (2 + Real.log (1 + M / H)) + 2 / H := by
  have hstep' : ∀ j < n, ν ≤ Y (j + 1) - Y j := by
    intro j hj
    have h := hstep j hj
    rwa [abs_of_nonneg (sub_nonneg.mpr (hmono j hj))] at h
  -- `S` = the negative indices; `m` = their number; `S` is an initial segment
  set S : Finset ℕ := (Finset.range n).filter (fun j => Y j < 0) with hSdef
  set m : ℕ := S.card with hmdef
  have hSsub : S ⊆ Finset.range n := Finset.filter_subset _ _
  have hSdown : ∀ j ∈ S, ∀ i ≤ j, i ∈ S := by
    intro j hj i hij
    rw [hSdef] at hj ⊢
    simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
    obtain ⟨hjn, hjY⟩ := hj
    refine ⟨lt_of_le_of_lt hij hjn, ?_⟩
    have h1 : Y i + ((j - i : ℕ) : ℝ) * ν ≤ Y j := mono_step hstep' hij hjn
    have h2 : (0 : ℝ) ≤ ((j - i : ℕ) : ℝ) * ν := by positivity
    linarith
  have hSeq : S = Finset.range m := by rw [hmdef]; exact downclosed_eq_range S hSdown
  have hmle : m ≤ n := by
    have := Finset.card_le_card hSsub
    simpa [hmdef, Finset.card_range] using this
  have hmemS : ∀ j, j ∈ S ↔ j < m := by intro j; rw [hSeq, Finset.mem_range]
  have hmemS' : ∀ j, j ∈ S ↔ (j < n ∧ Y j < 0) := by
    intro j; rw [hSdef, Finset.mem_filter, Finset.mem_range]
  -- ## the negative branch `j < m`: `|Y j| ≥ (m-1-j) ν`
  have hnegN : ∀ j < m, ((m - 1 - j : ℕ) : ℝ) * ν ≤ |Y j| := by
    intro j hj
    have hjS : j ∈ S := (hmemS j).mpr hj
    obtain ⟨hjn, hjY⟩ := (hmemS' j).mp hjS
    have hm1S : m - 1 ∈ S := (hmemS (m - 1)).mpr (by omega)
    obtain ⟨hm1n, hm1Y⟩ := (hmemS' (m - 1)).mp hm1S
    have h1 : Y j + ((m - 1 - j : ℕ) : ℝ) * ν ≤ Y (m - 1) := mono_step hstep' (by omega) hm1n
    rw [abs_of_neg hjY]
    linarith
  have hneg : (∑ j ∈ Finset.range m, 1 / max |Y j| H)
      ≤ ∑ l ∈ Finset.range m, 1 / max ((l : ℝ) * ν) H := by
    have hp : ∀ j ∈ Finset.range m,
        1 / max |Y j| H ≤ 1 / max (((m - 1 - j : ℕ) : ℝ) * ν) H := by
      intro j hj
      rw [Finset.mem_range] at hj
      have hb : 0 < max (((m - 1 - j : ℕ) : ℝ) * ν) H := lt_of_lt_of_le hH (le_max_right _ _)
      have hle : max (((m - 1 - j : ℕ) : ℝ) * ν) H ≤ max |Y j| H :=
        max_le_max (hnegN j hj) le_rfl
      exact one_div_le_one_div_of_le hb hle
    calc (∑ j ∈ Finset.range m, 1 / max |Y j| H)
        ≤ ∑ j ∈ Finset.range m, 1 / max (((m - 1 - j : ℕ) : ℝ) * ν) H := Finset.sum_le_sum hp
      _ = ∑ l ∈ Finset.range m, 1 / max ((l : ℝ) * ν) H :=
          Finset.sum_range_reflect (fun l : ℕ => 1 / max ((l : ℝ) * ν) H) m
  -- ## the nonnegative branch `m + i`: `|Y (m+i)| ≥ i ν`
  have hposN : ∀ i < n - m, ((i : ℕ) : ℝ) * ν ≤ |Y (m + i)| := by
    intro i hi
    have hmin : m < n := by omega
    have hmy : 0 ≤ Y m := by
      by_contra h
      have hmS : m ∈ S := (hmemS' m).mpr ⟨hmin, not_le.mp h⟩
      have : m < m := (hmemS m).mp hmS
      omega
    have h1 : Y m + ((m + i - m : ℕ) : ℝ) * ν ≤ Y (m + i) :=
      mono_step hstep' (by omega) (by omega)
    have h2 : ((m + i - m : ℕ) : ℝ) = (i : ℝ) := by rw [Nat.add_sub_cancel_left]
    rw [h2] at h1
    have : ((i : ℕ) : ℝ) * ν ≤ Y (m + i) := by linarith
    exact le_trans this (le_abs_self _)
  have hpos : (∑ i ∈ Finset.range (n - m), 1 / max |Y (m + i)| H)
      ≤ ∑ l ∈ Finset.range (n - m), 1 / max ((l : ℝ) * ν) H := by
    apply Finset.sum_le_sum
    intro i hi
    rw [Finset.mem_range] at hi
    have hb : 0 < max (((i : ℕ) : ℝ) * ν) H := lt_of_lt_of_le hH (le_max_right _ _)
    have hle : max (((i : ℕ) : ℝ) * ν) H ≤ max |Y (m + i)| H :=
      max_le_max (hposN i hi) le_rfl
    exact one_div_le_one_div_of_le hb hle
  -- ## truncation of the two branch lengths: `(L-1) ν ≤ M`
  have hLneg : ((m : ℝ) - 1) * ν ≤ M := by
    rcases Nat.eq_zero_or_pos m with h0 | hpos
    · rw [h0]; push_cast; nlinarith [hν, hM0]
    · have h0S : 0 ∈ S := (hmemS 0).mpr hpos
      obtain ⟨h0n, h0Y⟩ := (hmemS' 0).mp h0S
      have hb := hnegN 0 hpos
      have hM0' : |Y 0| ≤ M := hM 0 h0n
      have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ m)]; norm_num
      rw [Nat.sub_zero] at hb
      rw [hcast] at hb
      linarith
  have hLpos : (((n - m : ℕ) : ℝ) - 1) * ν ≤ M := by
    rcases Nat.eq_zero_or_pos (n - m) with h0 | hpos
    · rw [h0]; push_cast; nlinarith [hν, hM0]
    · have hi : n - m - 1 < n - m := by omega
      have hb := hposN (n - m - 1) hi
      have hMn : |Y (m + (n - m - 1))| ≤ M := hM _ (by omega)
      have hcast : (((n - m - 1 : ℕ)) : ℝ) = ((n - m : ℕ) : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ n - m)]; norm_num
      rw [hcast] at hb
      linarith
  -- ## assembly
  have hsplit : (∑ j ∈ Finset.range n, 1 / max |Y j| H)
      = (∑ j ∈ Finset.range m, 1 / max |Y j| H)
        + ∑ i ∈ Finset.range (n - m), 1 / max |Y (m + i)| H := by
    have h := Finset.sum_range_add (fun j : ℕ => 1 / max |Y j| H) m (n - m)
    rwa [Nat.add_sub_of_le hmle] at h
  have hb1 : (∑ j ∈ Finset.range m, 1 / max |Y j| H)
      ≤ 2 / ν + 1 / H + (1 / ν) * Real.log (1 + M / H) :=
    le_trans hneg (arith hν hH hM0 hLneg)
  have hb2 : (∑ i ∈ Finset.range (n - m), 1 / max |Y (m + i)| H)
      ≤ 2 / ν + 1 / H + (1 / ν) * Real.log (1 + M / H) :=
    le_trans hpos (arith hν hH hM0 hLpos)
  have htot : (∑ j ∈ Finset.range n, 1 / max |Y j| H)
      ≤ (2 / ν + 1 / H + (1 / ν) * Real.log (1 + M / H)) * 2 := by
    rw [hsplit]; linarith
  refine le_trans htot ?_
  have hfin : (2 / ν + 1 / H + (1 / ν) * Real.log (1 + M / H)) * 2
      = (2 / ν) * (2 + Real.log (1 + M / H)) + 2 / H := by
    field_simp
    ring
  rw [hfin]

theorem lattice_vshape_harmonic {Y : ℕ → ℝ} {ν H M : ℝ} {n : ℕ}
    (hν : 0 < ν) (hH : 0 < H) (hM0 : 0 ≤ M)
    (hstep : ∀ j < n, ν ≤ |Y (j+1) - Y j|)
    (hdir : (∀ j < n, Y j ≤ Y (j+1)) ∨ (∀ j < n, Y (j+1) ≤ Y j))
    (hM : ∀ j < n, |Y j| ≤ M) :
    (∑ j ∈ Finset.range n, 1 / max |Y j| H)
      ≤ (2 / ν) * (2 + Real.log (1 + M / H)) + 2 / H := by
  rcases hdir with hmono | hanti
  · exact vshape_mono hν hH hM0 hstep hmono hM sum_max_lattice_arith
  · -- negate `Y` to reduce to the monotone case
    have hstep' : ∀ j < n, ν ≤ |(fun j => -Y j) (j+1) - (fun j => -Y j) j| := by
      intro j hj
      have h := hstep j hj
      change ν ≤ |-Y (j+1) - -Y j|
      rw [show -Y (j+1) - -Y j = -(Y (j+1) - Y j) by ring, abs_neg]
      exact h
    have hmono' : ∀ j < n, (fun j => -Y j) j ≤ (fun j => -Y j) (j+1) := by
      intro j hj
      have := hanti j hj
      simp only
      linarith
    have hM' : ∀ j < n, |(fun j => -Y j) j| ≤ M := by
      intro j hj
      simpa using hM j hj
    have := vshape_mono hν hH hM0 hstep' hmono' hM' sum_max_lattice_arith
    simpa using this

end Work.Pert
