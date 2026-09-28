import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.HP2.GridDefs
import Submission.Work.HP.HP2.grid_rounding
import Submission.Work.HP.tau_basic

set_option autoImplicit false

noncomputable section

open Classical MeasureTheory
open scoped BigOperators Pointwise ENNReal

namespace Work.HP.HP2

/-! ## Auxiliary definitions and lemmas for `grid_count_bounds` -/

/-- The closed Euclidean `r`-neighbourhood of a set `S ⊆ ℝ^m`. -/
def thickNbd (m : ℕ) (r : ℝ) (S : Set (Fin m → ℝ)) : Set (Fin m → ℝ) :=
  {x | ∃ y ∈ S, rNorm (x - y) ≤ r}

/-- Finiteness of the integers in a real interval. -/
lemma finite_setOf_int_abs_le (K : ℝ) : {k : ℤ | |(k : ℝ)| ≤ K}.Finite := by
  refine (Set.finite_Icc (-⌈K⌉) ⌈K⌉).subset ?_
  intro k hk
  simp only [Set.mem_Icc, Set.mem_ofPred_eq] at hk ⊢
  constructor
  · have h1 : -(K : ℝ) ≤ (k : ℝ) := (abs_le.1 hk).1
    have h2 : (((-⌈K⌉ : ℤ)) : ℝ) ≤ (k : ℝ) := by
      push_cast
      linarith [Int.le_ceil K]
    exact_mod_cast h2
  · have h1 : (k : ℝ) ≤ K := (abs_le.1 hk).2
    have h2 : (k : ℝ) ≤ ((⌈K⌉ : ℤ) : ℝ) := le_trans h1 (Int.le_ceil K)
    exact_mod_cast h2

/-- A bounded set contains only finitely many points of the grid `b + W ℤ^m`. -/
lemma finite_gridIdxIn (m : ℕ) {W : ℕ} (hW : 0 < W) (b : Fin m → ℤ) (S : Set (Fin m → ℝ))
    (hS : Bornology.IsBounded S) : (gridIdxIn m W b S).Finite := by
  have hWℝ : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hone : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fin m → ℝ)).1 hS
  refine (Set.Finite.pi' (fun i => finite_setOf_int_abs_le (R + |((b i : ℤ) : ℝ)|))).subset ?_
  intro z hz
  simp only [gridIdxIn, Set.mem_ofPred_eq] at hz
  have hdist : dist (gridVal m W b z) 0 ≤ R := hR hz
  have hRnn : 0 ≤ R := le_trans dist_nonneg hdist
  have hcoord : ∀ i, |gridVal m W b z i| ≤ R := by
    intro i
    have h := (dist_pi_le_iff hRnn).1 hdist i
    simpa [Real.dist_eq] using h
  intro i
  have h1 : |(z i : ℝ)| ≤ R + |((b i : ℤ) : ℝ)| := by
    have h2 : (W : ℝ) * |(z i : ℝ)| ≤ R + |((b i : ℤ) : ℝ)| := by
      have h3 : (W : ℝ) * |(z i : ℝ)| = |gridVal m W b z i - ((b i : ℤ) : ℝ)| := by
        rw [show (W : ℝ) * |(z i : ℝ)| = |(W : ℝ) * (z i : ℝ)| by
          rw [abs_mul, abs_of_pos hWℝ]]
        congr 1
        simp only [gridVal]
        ring
      rw [h3]
      calc |gridVal m W b z i - ((b i : ℤ) : ℝ)| ≤ |gridVal m W b z i| + |((b i : ℤ) : ℝ)| :=
            abs_sub _ _
        _ ≤ R + |((b i : ℤ) : ℝ)| := by linarith [hcoord i]
    have h4 : |(z i : ℝ)| ≤ (W : ℝ) * |(z i : ℝ)| := by
      nlinarith [abs_nonneg (z i : ℝ), hone]
    linarith
  exact h1

/-! ## Volume of the fundamental box and of its translates -/

lemma measurableSet_fundBox (m : ℕ) (W : ℝ) : MeasurableSet (fundBox m W) :=
  MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Ico

lemma volume_fundBox (m : ℕ) (W : ℝ) (hW : 0 ≤ W) :
    volume (fundBox m W) = ENNReal.ofReal (W ^ m) := by
  rw [fundBox, volume_pi_pi]
  simp only [Real.volume_Ico, sub_zero]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← ENNReal.ofReal_pow hW]

lemma volume_fundBox_toReal (m : ℕ) (W : ℝ) (hW : 0 ≤ W) :
    (volume (fundBox m W)).toReal = W ^ m := by
  rw [volume_fundBox m W hW, ENNReal.toReal_ofReal (pow_nonneg hW m)]

lemma measurableSet_gridCell (m : ℕ) (W : ℝ) (t : Fin m → ℝ) :
    MeasurableSet (gridCell m W t) := by
  rw [gridCell_eq_preimage]
  exact (measurableSet_fundBox m W).preimage (measurable_id.const_add (-t))

lemma volume_gridCell (m : ℕ) (W : ℝ) (t : Fin m → ℝ) :
    volume (gridCell m W t) = volume (fundBox m W) := by
  rw [gridCell_eq_preimage]
  exact measure_preimage_add volume (-t) (fundBox m W)

lemma volume_gridCell_toReal (m : ℕ) (W : ℝ) (hW : 0 ≤ W) (t : Fin m → ℝ) :
    (volume (gridCell m W t)).toReal = W ^ m := by
  rw [volume_gridCell, volume_fundBox_toReal m W hW]

/-- Two cells of the grid `b + W ℤ^m` with distinct centres are disjoint. -/
lemma disjoint_gridCell (m : ℕ) {W : ℕ} (hW : 0 < W) (b : Fin m → ℤ) {z z' : Fin m → ℤ}
    (h : z ≠ z') :
    Disjoint (gridCell m (W : ℝ) (gridVal m W b z)) (gridCell m (W : ℝ) (gridVal m W b z')) := by
  have hWℝ : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [mem_gridCell] at hx hx'
  rw [fundBox, Set.mem_pi] at hx hx'
  have hne : ∃ i, z i ≠ z' i := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact h (funext hcon)
  obtain ⟨i, hi⟩ := hne
  have h1 : (0 : ℝ) ≤ x i - gridVal m W b z i := (hx i (Set.mem_univ i)).1
  have h2 : x i - gridVal m W b z i < (W : ℝ) := (hx i (Set.mem_univ i)).2
  have h3 : (0 : ℝ) ≤ x i - gridVal m W b z' i := (hx' i (Set.mem_univ i)).1
  have h4 : x i - gridVal m W b z' i < (W : ℝ) := (hx' i (Set.mem_univ i)).2
  have h5 : gridVal m W b z' i - gridVal m W b z i
      = (x i - gridVal m W b z i) - (x i - gridVal m W b z' i) := by ring
  have h6 : |gridVal m W b z' i - gridVal m W b z i| < (W : ℝ) := by
    rw [h5, abs_lt]
    constructor <;> linarith
  have h7 : gridVal m W b z' i - gridVal m W b z i
      = (W : ℝ) * ((z' i : ℝ) - (z i : ℝ)) := by
    simp only [gridVal]
    ring
  have h8 : (W : ℝ) ≤ |(W : ℝ) * ((z' i : ℝ) - (z i : ℝ))| := by
    rw [abs_mul, abs_of_pos hWℝ]
    have hz : z' i - z i ≠ 0 := sub_ne_zero.mpr (Ne.symm hi)
    have hk : (1 : ℝ) ≤ |(z' i : ℝ) - (z i : ℝ)| := by
      have hkZ : (1 : ℤ) ≤ |z' i - z i| := Int.one_le_abs hz
      have hcast : ((|z' i - z i| : ℤ) : ℝ) = |(z' i : ℝ) - (z i : ℝ)| := by
        rw [Int.cast_abs, Int.cast_sub]
      rw [← hcast]
      exact_mod_cast hkZ
    nlinarith
  rw [h7] at h6
  linarith

/-- The measure of the union of the grid cells indexed by a finset of integer vectors. -/
lemma volume_biUnion_gridCell (m : ℕ) {W : ℕ} (hW : 0 < W) (b : Fin m → ℤ)
    (Z : Finset (Fin m → ℤ)) :
    volume (⋃ z ∈ Z, gridCell m (W : ℝ) (gridVal m W b z))
      = (Z.card : ENNReal) * ENNReal.ofReal ((W : ℝ) ^ m) := by
  have hdisj : (Z : Set (Fin m → ℤ)).PairwiseDisjoint
      fun z => gridCell m (W : ℝ) (gridVal m W b z) :=
    fun z _ z' _ hne => disjoint_gridCell m hW b hne
  have hmeas : ∀ z ∈ Z, MeasurableSet (gridCell m (W : ℝ) (gridVal m W b z)) :=
    fun z _ => measurableSet_gridCell m (W : ℝ) _
  have hsum : ∀ z ∈ Z, volume (gridCell m (W : ℝ) (gridVal m W b z))
      = ENNReal.ofReal ((W : ℝ) ^ m) := by
    intro z _
    rw [volume_gridCell, volume_fundBox m (W : ℝ) (le_of_lt (by exact_mod_cast hW))]
  rw [measure_biUnion_finset hdisj hmeas, Finset.sum_congr rfl hsum, Finset.sum_const,
    nsmul_eq_mul]

/-! ## Elementary bounds -/

lemma sqrt_mul_le_8 (m : ℕ) (hm : 1 ≤ m) (W : ℝ) (hW : 0 ≤ W) :
    Real.sqrt m * W ≤ 8 * (m : ℝ) * W := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have h1 : Real.sqrt m ≤ 8 * (m : ℝ) := by
    calc Real.sqrt m ≤ Real.sqrt ((m : ℝ) ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = (m : ℝ) := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith)]
      _ ≤ 8 * (m : ℝ) := by linarith
  exact mul_le_mul_of_nonneg_right h1 hW

/-! ## The last point of `S` on a segment -/

/-- If `s ∈ S` and `y ∉ S`, the segment from `s` to `y` meets the frontier of `S`. -/
lemma segment_frontier {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {S : Set E} {s y : E} (hs : s ∈ S) (hy : y ∉ S) :
    ∃ t ∈ Set.Icc (0 : ℝ) 1, s + t • (y - s) ∈ frontier S := by
  classical
  let p : ℝ → E := fun t => s + t • (y - s)
  have hp0 : p 0 = s := by simp [p]
  have hp1 : p 1 = y := by simp [p]
  have hpcont : Continuous p := continuous_const.add (continuous_id.smul continuous_const)
  let A : Set ℝ := {t | t ∈ Set.Icc (0 : ℝ) 1 ∧ p t ∈ S}
  have hA0 : (0 : ℝ) ∈ A := ⟨⟨le_refl _, zero_le_one⟩, by rw [hp0]; exact hs⟩
  have hAne : A.Nonempty := ⟨0, hA0⟩
  have hAbdd : BddAbove A := ⟨1, fun t ht => ht.1.2⟩
  have hle : ∀ t ∈ A, t ≤ sSup A := fun t ht => le_csSup hAbdd ht
  have hsup0 : (0 : ℝ) ≤ sSup A := le_csSup hAbdd hA0
  have hsup1 : sSup A ≤ 1 := csSup_le hAne fun t ht => ht.1.2
  have hcl : p (sSup A) ∈ closure S := by
    have h1 : sSup A ∈ closure A := csSup_mem_closure hAne hAbdd
    have h2 : p '' closure A ⊆ closure (p '' A) := image_closure_subset_closure_image hpcont
    have h3 : closure (p '' A) ⊆ closure S := closure_mono fun x hx => by
      obtain ⟨t, ht, rfl⟩ := hx
      exact ht.2
    exact h3 (h2 ⟨sSup A, h1, rfl⟩)
  have hclc : p (sSup A) ∈ closure Sᶜ := by
    rcases lt_or_eq_of_le hsup1 with hlt | heq
    · rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨δ, hδ0, hδ⟩ := (Metric.continuousAt_iff.1 (hpcont.continuousAt (x := sSup A))) ε hε
      have hpos : 0 < min (δ / 2) ((1 - sSup A) / 2) := lt_min (by linarith) (by linarith)
      refine ⟨p (sSup A + min (δ / 2) ((1 - sSup A) / 2)), ?_, ?_⟩
      · simp only [Set.mem_compl_iff]
        intro hmem
        have hA' : sSup A + min (δ / 2) ((1 - sSup A) / 2) ∈ A := by
          refine ⟨⟨by linarith, ?_⟩, hmem⟩
          linarith [min_le_right (δ / 2) ((1 - sSup A) / 2)]
        have h2 := hle _ hA'
        linarith
      · rw [dist_comm]
        apply hδ
        rw [Real.dist_eq,
          show sSup A + min (δ / 2) ((1 - sSup A) / 2) - sSup A
            = min (δ / 2) ((1 - sSup A) / 2) by ring, abs_of_pos hpos]
        linarith [min_le_left (δ / 2) ((1 - sSup A) / 2)]
    · have hpy : p (sSup A) = y := by rw [heq, hp1]
      rw [hpy]
      exact subset_closure hy
  exact ⟨sSup A, ⟨hsup0, hsup1⟩, by
    rw [frontier_eq_closure_inter_closure]
    exact ⟨hcl, hclc⟩⟩

/-- Euclidean form: some point of the frontier of `S` is at least as close to `s` as `y` is. -/
lemma frontier_rNorm_le (m : ℕ) {S : Set (Fin m → ℝ)} {s y : Fin m → ℝ} (hs : s ∈ S)
    (hy : y ∉ S) : ∃ c ∈ frontier S, rNorm (s - c) ≤ rNorm (s - y) := by
  obtain ⟨t, ht, hc⟩ := segment_frontier (E := Fin m → ℝ) hs hy
  refine ⟨s + t • (y - s), hc, ?_⟩
  have hsub : s - (s + t • (y - s)) = t • (s - y) := by
    rw [show s - (s + t • (y - s)) = -(t • (y - s)) by abel, ← smul_neg, neg_sub]
  rw [hsub, rNorm_smul', abs_of_nonneg ht.1]
  nlinarith [rNorm_nonneg (s - y), ht.2]

/-! ## Finiteness of the volume of bounded thickenings -/

lemma volume_closedBall_lt_top (m : ℕ) (c : Fin m → ℝ) (R : ℝ) :
    volume (Metric.closedBall c R) < ⊤ := by
  rcases lt_or_ge R 0 with hR | hR
  · rw [Metric.closedBall_eq_empty.mpr hR]
    simp
  · rw [volume_pi_closedBall c hR]
    have hprod : (∏ i : Fin m, volume (Metric.closedBall (c i) R))
        = ENNReal.ofReal ((2 * R) ^ m) := by
      simp only [Real.volume_closedBall]
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
        ← ENNReal.ofReal_pow (by linarith)]
    rw [hprod]
    exact ENNReal.ofReal_lt_top

lemma volume_lt_top_of_isBounded (m : ℕ) {S : Set (Fin m → ℝ)} (hS : Bornology.IsBounded S) :
    volume S < ⊤ := by
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Fin m → ℝ)).1 hS
  exact lt_of_le_of_lt (measure_mono hR) (volume_closedBall_lt_top m 0 R)

lemma isBounded_thickNbd (m : ℕ) {S : Set (Fin m → ℝ)} (hS : Bornology.IsBounded S) {r : ℝ}
    (hr : 0 ≤ r) : Bornology.IsBounded (thickNbd m r S) := by
  rcases S.eq_empty_or_nonempty with h | ⟨y₀, hy₀⟩
  · rw [h, show thickNbd m r (∅ : Set (Fin m → ℝ)) = ∅ from by ext x; simp [thickNbd]]
    exact Metric.isBounded_iff.2 ⟨0, by simp⟩
  · obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall y₀).1 hS
    refine (Metric.isBounded_closedBall (x := y₀) (r := r + R)).subset fun x hx => ?_
    obtain ⟨y, hyS, hxy⟩ := hx
    have h1 : dist x y ≤ r := by
      rw [dist_pi_le_iff hr]
      intro i
      rw [Real.dist_eq]
      exact le_trans (abs_apply_le_rNorm (x - y) i) hxy
    calc dist x y₀ ≤ dist x y + dist y y₀ := dist_triangle x y y₀
      _ ≤ r + R := add_le_add h1 (hR hyS)

lemma volume_thickNbd_lt_top (m : ℕ) {S : Set (Fin m → ℝ)} (hS : Bornology.IsBounded S) {r : ℝ}
    (hr : 0 ≤ r) : volume (thickNbd m r S) < ⊤ :=
  volume_lt_top_of_isBounded m (isBounded_thickNbd m hS hr)

/-! ## The grid count bound -/

/-- Points of a coset of `W * Z^m`, written as `x = b + W*z` with `b : Fin m → ℤ`, inside a closed
bounded set `S ⊆ ℝ^m`, compared with `MeasureTheory.volume S / (W:ℝ)^m`.  The loss is the volume of
the `8*m*W`-neighbourhood of the frontier of `S`.

Route.  `F = ∏ᵢ [0,W)` is a fundamental domain of `W * Z^m` (`MeasureTheory.volume F = W^m`,
`diam F = √m * W`) and the translates `λ + F`, `λ ∈ b + W*Z^m`, tile `ℝ^m` up to a null set.
Upper bound: `{λ : (λ+F) ∩ S ≠ ∅} ⊆ S - F`, and
`#(Λ ∩ (S-F)) * MeasureTheory.volume F ≤ MeasureTheory.volume ((S-F)+F) ≤ MeasureTheory.volume (S ⊕ B(2√m W))`.
Lower bound: `MeasureTheory.volume S ≤ #(Λ ∩ (S ⊕ F)) * W^m`; and `(S ⊕ F) \ S ⊆ T_{√m W}(frontier S)`
because for `x = s + f` with `s ∈ S`, `x ∉ S`, the last point of the closed set `S` on the segment
`[s,x]` lies in the frontier of `S`.  Then `#(Λ ∩ T) * W^m ≤ MeasureTheory.volume (T ⊕ B(2√m W))`
and `T ⊕ B(2√m W) ⊆ T_{3√m W}(frontier S)`. -/
theorem grid_count_bounds (m : ℕ) (hm : 1 ≤ m) (W : ℕ) (hW : 0 < W) (b : Fin m → ℤ)
    (S : Set (Fin m → ℝ)) (hSclosed : IsClosed S) (hSbd : Bornology.IsBounded S) :
    (({x : Fin m → ℝ | x ∈ S ∧ ∃ z : Fin m → ℤ,
        x = fun i => (b i : ℝ) + (W : ℝ) * (z i)}).ncard : ℝ)
      ≥ ((MeasureTheory.volume S).toReal - (MeasureTheory.volume {x : Fin m → ℝ | ∃ y ∈ frontier S,
          rNorm (x - y) ≤ 8 * (m : ℝ) * W}).toReal) / (W : ℝ) ^ m
    ∧ (({x : Fin m → ℝ | x ∈ S ∧ ∃ z : Fin m → ℤ,
        x = fun i => (b i : ℝ) + (W : ℝ) * (z i)}).ncard : ℝ)
      ≤ ((MeasureTheory.volume {x : Fin m → ℝ | ∃ y ∈ S,
            rNorm (x - y) ≤ 8 * (m : ℝ) * W}).toReal) / (W : ℝ) ^ m := by
  have hΛ : ({x : Fin m → ℝ | x ∈ S ∧ ∃ z : Fin m → ℤ,
      x = fun i => (b i : ℝ) + (W : ℝ) * (z i)} : Set (Fin m → ℝ)) = gridIn m W b S := rfl
  have hTup : ({x : Fin m → ℝ | ∃ y ∈ S, rNorm (x - y) ≤ 8 * (m : ℝ) * W} : Set (Fin m → ℝ))
      = thickNbd m (8 * (m : ℝ) * (W : ℝ)) S := rfl
  have hTlow : ({x : Fin m → ℝ | ∃ y ∈ frontier S, rNorm (x - y) ≤ 8 * (m : ℝ) * W}
      : Set (Fin m → ℝ)) = thickNbd m (8 * (m : ℝ) * (W : ℝ)) (frontier S) := rfl
  rw [hΛ, hTup, hTlow]
  have hWℝ : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
  have hvm : (0 : ℝ) < (W : ℝ) ^ m := pow_pos hWℝ m
  have hsqrt : Real.sqrt m * (W : ℝ) ≤ 8 * (m : ℝ) * (W : ℝ) :=
    sqrt_mul_le_8 m hm (W : ℝ) hWℝ.le
  have hr : (0 : ℝ) ≤ 8 * (m : ℝ) * (W : ℝ) := by positivity
  have hfin : (gridIdxIn m W b S).Finite := finite_gridIdxIn m hW b S hSbd
  set Z : Finset (Fin m → ℤ) := hfin.toFinset with hZ
  have hZcoe : (Z : Set (Fin m → ℤ)) = gridIdxIn m W b S := by
    rw [hZ]
    exact Set.Finite.coe_toFinset hfin
  have hN : (gridIn m W b S).ncard = Z.card := by
    rw [ncard_gridIn_eq m hW b S, ← hZcoe]
    exact Set.ncard_coe_finset Z
  have hunion_eq : (⋃ u ∈ gridIn m W b S, gridCell m (W : ℝ) u)
      = (⋃ z ∈ Z, gridCell m (W : ℝ) (gridVal m W b z)) := by
    have hgrid : gridIn m W b S = gridVal m W b '' (Z : Set (Fin m → ℤ)) := by
      rw [gridIn_eq_image m W b S, hZcoe]
    rw [hgrid]
    ext x
    simp only [Set.mem_iUnion, Set.mem_image, exists_prop]
    constructor
    · rintro ⟨u, ⟨z, hz, rfl⟩, hx⟩
      exact ⟨z, hz, hx⟩
    · rintro ⟨z, hz, hx⟩
      exact ⟨gridVal m W b z, ⟨z, hz, rfl⟩, hx⟩
  have hunion_measure : volume (⋃ u ∈ gridIn m W b S, gridCell m (W : ℝ) u)
      = ((gridIn m W b S).ncard : ENNReal) * ENNReal.ofReal ((W : ℝ) ^ m) := by
    rw [hunion_eq, volume_biUnion_gridCell m hW b Z, ← hN]
  have hcover : S \ thickNbd m (8 * (m : ℝ) * (W : ℝ)) (frontier S)
      ⊆ ⋃ u ∈ gridIn m W b S, gridCell m (W : ℝ) u := by
    intro x hx
    obtain ⟨hxS, hxT⟩ := hx
    have hxT' : ∀ y ∈ frontier S, 8 * (m : ℝ) * (W : ℝ) < rNorm (x - y) := by
      intro y hy
      by_contra hcon
      exact hxT ⟨y, hy, not_lt.mp hcon⟩
    refine Set.mem_iUnion.2 ⟨gridPt m W b x, Set.mem_iUnion.2 ⟨?_, ?_⟩⟩
    · refine ⟨?_, gridPt_mem_coset m W b x⟩
      by_contra hnotS
      obtain ⟨c, hc, hcle⟩ := frontier_rNorm_le (m := m) (S := S) hxS hnotS
      have h1 : rNorm (x - c) ≤ Real.sqrt m * (W : ℝ) :=
        le_trans hcle ((grid_rounding m hW b).2.1 x)
      exact absurd (hxT' c hc) (not_lt.2 (le_trans h1 hsqrt))
    · rw [mem_gridCell]
      exact (grid_rounding m hW b).1 x
  have hsub_up : (⋃ u ∈ gridIn m W b S, gridCell m (W : ℝ) u)
      ⊆ thickNbd m (8 * (m : ℝ) * (W : ℝ)) S := by
    intro x hx
    obtain ⟨u, hu⟩ := Set.mem_iUnion.1 hx
    obtain ⟨huS, hxu⟩ := Set.mem_iUnion.1 hu
    refine ⟨u, huS.1, ?_⟩
    have h2 : x - u ∈ fundBox m (W : ℝ) := mem_gridCell.1 hxu
    exact le_trans ((grid_rounding m hW b).2.2 (x - u) h2) hsqrt
  have hSup : ((gridIn m W b S).ncard : ENNReal) * ENNReal.ofReal ((W : ℝ) ^ m)
      ≤ volume (thickNbd m (8 * (m : ℝ) * (W : ℝ)) S) := by
    rw [← hunion_measure]
    exact measure_mono hsub_up
  have hSlow : volume S ≤ volume (thickNbd m (8 * (m : ℝ) * (W : ℝ)) (frontier S))
      + ((gridIn m W b S).ncard : ENNReal) * ENNReal.ofReal ((W : ℝ) ^ m) := by
    have h3 : volume (S \ thickNbd m (8 * (m : ℝ) * (W : ℝ)) (frontier S))
        ≤ ((gridIn m W b S).ncard : ENNReal) * ENNReal.ofReal ((W : ℝ) ^ m) :=
      le_trans (measure_mono hcover) (le_of_eq hunion_measure)
    calc volume S ≤ volume (thickNbd m (8 * (m : ℝ) * (W : ℝ)) (frontier S)
          ∪ (S \ thickNbd m (8 * (m : ℝ) * (W : ℝ)) (frontier S))) :=
          measure_mono fun x hx => by
            by_cases h : x ∈ thickNbd m (8 * (m : ℝ) * (W : ℝ)) (frontier S)
            · exact Or.inl h
            · exact Or.inr ⟨hx, h⟩
      _ ≤ volume (thickNbd m (8 * (m : ℝ) * (W : ℝ)) (frontier S))
            + volume (S \ thickNbd m (8 * (m : ℝ) * (W : ℝ)) (frontier S)) :=
          measure_union_le _ _
      _ ≤ volume (thickNbd m (8 * (m : ℝ) * (W : ℝ)) (frontier S))
            + ((gridIn m W b S).ncard : ENNReal) * ENNReal.ofReal ((W : ℝ) ^ m) :=
          add_le_add le_rfl h3
  have hTupfin : volume (thickNbd m (8 * (m : ℝ) * (W : ℝ)) S) < ⊤ :=
    volume_thickNbd_lt_top m hSbd hr
  have hfr : frontier S ⊆ S :=
    Set.Subset.trans frontier_subset_closure (le_of_eq hSclosed.closure_eq)
  have hTlowfin : volume (thickNbd m (8 * (m : ℝ) * (W : ℝ)) (frontier S)) < ⊤ :=
    lt_of_le_of_lt (measure_mono fun x hx => by
      obtain ⟨y, hy, hxy⟩ := hx
      exact ⟨y, hfr hy, hxy⟩) hTupfin
  have hXfin : ((gridIn m W b S).ncard : ENNReal) * ENNReal.ofReal ((W : ℝ) ^ m) < ⊤ :=
    ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr (ENNReal.natCast_ne_top _)) ENNReal.ofReal_lt_top
  constructor
  · have hb : volume (thickNbd m (8 * (m : ℝ) * (W : ℝ)) (frontier S))
        + ((gridIn m W b S).ncard : ENNReal) * ENNReal.ofReal ((W : ℝ) ^ m) ≠ ⊤ :=
      ne_of_lt (ENNReal.add_lt_top.2 ⟨hTlowfin, hXfin⟩)
    have hreal : (volume S).toReal
        ≤ (volume (thickNbd m (8 * (m : ℝ) * (W : ℝ)) (frontier S))).toReal
          + ((gridIn m W b S).ncard : ℝ) * (W : ℝ) ^ m := by
      have h := ENNReal.toReal_mono hb hSlow
      rwa [ENNReal.toReal_add (ne_of_lt hTlowfin) (ne_of_lt hXfin), ENNReal.toReal_mul,
        ENNReal.toReal_natCast, ENNReal.toReal_ofReal (pow_nonneg hWℝ.le m)] at h
    rw [ge_iff_le, div_le_iff₀ hvm]
    linarith
  · have hreal : ((gridIn m W b S).ncard : ℝ) * (W : ℝ) ^ m
        ≤ (volume (thickNbd m (8 * (m : ℝ) * (W : ℝ)) S)).toReal := by
      have h := ENNReal.toReal_mono (ne_of_lt hTupfin) hSup
      rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast,
        ENNReal.toReal_ofReal (pow_nonneg hWℝ.le m)] at h
    rw [le_div_iff₀ hvm]
    exact hreal

end Work.HP.HP2
