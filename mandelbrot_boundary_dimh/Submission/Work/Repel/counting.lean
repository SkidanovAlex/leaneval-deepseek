import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.chain
import Submission.Work.Repel.lipschitz_window_card

/-!
# REPEL: counting the integer translates of a Lemma-6.2 chain inside `D(η')`

Shishikura §6, Step 3: if the backward chain `W` of Lemma 6.2 marches to the end indicated by
`sgn` at speed `< C₀ + 1` and has one disc below the counting region, then at least
`η'²/(64(C₀+1))` integer translates `W j + k` lie entirely inside the perturbative disc
`closedBall (±iη') (η'/4)`.  These are the `γ(η')²` "gates" of the paper.

(This file restores the counting lemmas proved in the earlier `chain_returns_ext.lean`.
The statements and proofs are unchanged.)
-/

namespace Work.Repel

open MandelDim Complex Set Metric Filter Topology

/-- The number of integers in a closed real interval `[c, c+L]` is at least `L - 1`. -/
lemma integer_interval_card (c L : ℝ) (hL : 0 ≤ L) :
    L - 1 ≤ ((Finset.Icc (Int.ceil c) (Int.floor (c + L))).card : ℝ) := by
  have hcardZ : ((Finset.Icc (Int.ceil c) (Int.floor (c + L))).card : ℤ)
      = Int.floor (c + L) + 1 - Int.ceil c := by
    apply Int.card_Icc_of_le
    linarith [Int.ceil_le_floor_add_one c, Int.floor_mono (show c ≤ c + L by linarith)]
  have h3 : ((Finset.Icc (Int.ceil c) (Int.floor (c + L))).card : ℝ)
      = (Int.floor (c + L) : ℝ) + 1 - (Int.ceil c : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hcardZ
    push_cast at this
    exact this
  have h1 : (c + L - 1 : ℝ) ≤ (Int.floor (c + L) : ℝ) := by
    have := Int.floor_le (c + L)
    have := Int.lt_floor_add_one (c + L)
    linarith
  have h2 : (Int.ceil c : ℝ) ≤ c + 1 := by
    have := Int.ceil_lt_add_one c
    linarith
  rw [h3]; linarith

/-- **Per-disc counting.**  If `W` is bounded of diameter `< 1/2`, `p ∈ W` has `|p.im - Y| ≤ ρ/2`
and `4 ≤ ρ`, then at least `ρ/2` integer translates of `W` lie in `closedBall (i*Y) ρ`. -/
lemma exists_shifts_card_rho {W : Set ℂ} {p : ℂ} {Y ρ : ℝ}
    (hp : p ∈ W) (hbdd : Bornology.IsBounded W) (hdiam : Metric.diam W < 1 / 2)
    (hρ : 4 ≤ ρ) (him : |p.im - Y| ≤ ρ / 2) :
    ∃ K : Finset ℤ, (ρ / 2 ≤ (K.card : ℝ)) ∧
      ∀ k ∈ K, (fun w : ℂ => w + ((k : ℤ) : ℂ)) '' W ⊆ Metric.closedBall (Complex.I * Y) ρ := by
  set d : ℝ := Metric.diam W with hddef
  have hd : d < 1 / 2 := by rw [hddef]; exact hdiam
  have hd0 : 0 ≤ d := by rw [hddef]; exact Metric.diam_nonneg
  set R : ℝ := Real.sqrt ((ρ - d) ^ 2 - (p.im - Y) ^ 2) with hRdef
  have hρpos : 0 < ρ := by linarith
  have hb2 : (p.im - Y) ^ 2 ≤ (ρ / 2) ^ 2 := by
    rw [← sq_abs (p.im - Y)]
    exact pow_le_pow_left₀ (abs_nonneg _) him 2
  have harg : 0 ≤ (ρ - d) ^ 2 - (p.im - Y) ^ 2 := by
    have h1 : ρ / 2 < ρ - d := by linarith
    nlinarith [hb2, h1, hρpos]
  have hR2 : R ^ 2 = (ρ - d) ^ 2 - (p.im - Y) ^ 2 := by
    rw [hRdef]; exact Real.sq_sqrt harg
  have hRnonneg : 0 ≤ R := by rw [hRdef]; exact Real.sqrt_nonneg _
  have hRbound : ρ / 2 + 2 ≤ 2 * R := by
    have h4 : (ρ / 2 + 2) ^ 2 ≤ 4 * R ^ 2 := by
      rw [show 4 * R ^ 2 = 4 * ((ρ - d) ^ 2 - (p.im - Y) ^ 2) by rw [hR2]]
      nlinarith [hb2, hd, hρ]
    have h6 : 0 ≤ ρ / 2 + 2 := by linarith
    have h7 : 0 ≤ 2 * R := by linarith
    nlinarith [h4, h6, h7]
  have hRd : d ≤ R := by linarith
  set c : ℝ := -R - p.re + d with hcdef
  set L : ℝ := 2 * R - 2 * d with hLdef
  have hL0 : 0 ≤ L := by rw [hLdef]; linarith
  have hcL : c + L = R - p.re - d := by rw [hcdef, hLdef]; ring
  refine ⟨Finset.Icc (Int.ceil c) (Int.floor (c + L)), ?_, ?_⟩
  · -- cardinality: the interval has length `L = 2R - 2d`
    have hlen : L - 1 ≤ ((Finset.Icc (Int.ceil c) (Int.floor (c + L))).card : ℝ) :=
      integer_interval_card c L hL0
    have h2d : 2 * d ≤ 1 := by linarith
    rw [hLdef] at hlen
    linarith
  · intro k hk
    rintro z ⟨w, hw, rfl⟩
    rw [Metric.mem_closedBall, dist_eq_norm]
    have hk' : |p.re + (k : ℝ)| ≤ R - d := by
      have h1 : c ≤ (k : ℝ) := le_trans (Int.le_ceil c) (by exact_mod_cast (Finset.mem_Icc.mp hk).1)
      have h2 : (k : ℝ) ≤ c + L := le_trans (by exact_mod_cast (Finset.mem_Icc.mp hk).2)
        (Int.floor_le (c + L))
      rw [abs_le]
      constructor <;> linarith [hcdef, hcL]
    have hpk : ‖p + (k : ℂ) - Complex.I * Y‖ ≤ ρ - d := by
      have h1 : ‖p + (k : ℂ) - Complex.I * Y‖ ^ 2 ≤ (ρ - d) ^ 2 := by
        have hre : (p + (k : ℂ) - Complex.I * Y).re = p.re + (k : ℝ) := by simp
        have him' : (p + (k : ℂ) - Complex.I * Y).im = p.im - Y := by simp
        rw [Complex.sq_norm, Complex.normSq_apply, hre, him']
        nlinarith [abs_le.mp hk', hR2, hRd, hd0, hRnonneg]
      have h3 : 0 ≤ ρ - d := by linarith
      have h4 := sq_le_sq.mp h1
      rwa [abs_of_nonneg (norm_nonneg _), abs_of_nonneg h3] at h4
    have hwp : ‖w - p‖ ≤ d := by
      have h := Metric.dist_le_diam_of_mem hbdd hw hp
      rwa [dist_eq_norm] at h
    have hsplit : w + (k : ℂ) - Complex.I * Y = (w - p) + (p + (k : ℂ) - Complex.I * Y) := by
      ring
    rw [hsplit]
    calc ‖(w - p) + (p + (k : ℂ) - Complex.I * Y)‖
        ≤ ‖w - p‖ + ‖p + (k : ℂ) - Complex.I * Y‖ := norm_add_le _ _
      _ ≤ d + (ρ - d) := add_le_add hwp hpk
      _ = ρ := by ring

/-- **Counting the copies for a chain marching to `+∞`.**  At least `Y²/(64(C₀+1))` integer
translates of the discs `W j` lie in `closedBall (i*Y) (Y/4)`. -/
theorem count_up_copies (W : ℕ → Set ℂ) (C₀ Y : ℝ) (hC : 0 < C₀) (hY : 64 * (C₀ + 1) ≤ Y)
    (hbdd : ∀ j, Bornology.IsBounded (W j))
    (hdiam : ∀ j, Metric.diam (W j) < 1 / 2)
    (hstep : ∀ j, ∃ u ∈ W j, ∃ u' ∈ W (j + 1), ‖u - u'‖ < C₀)
    (hup : ∀ M : ℝ, ∃ J : ℕ, ∀ j, J ≤ j → ∀ w ∈ W j, M < w.im)
    (hlow : ∃ j₀ : ℕ, ∃ w ∈ W j₀, w.im < Y / 4) :
    ∃ S : Finset (ℕ × ℤ), (Y ^ 2 / (64 * (C₀ + 1)) ≤ (S.card : ℝ)) ∧
      ∀ q ∈ S, (fun w : ℂ => w + ((q.2 : ℤ) : ℂ)) '' W q.1 ⊆
        Metric.closedBall (Complex.I * Y) (Y / 4) := by
  classical
  have hδpos : 0 < C₀ + 1 := by linarith
  have hY64 : 64 ≤ Y := by nlinarith [hY, hC]
  have hYpos : 0 < Y := by linarith
  have hY8 : 8 * (C₀ + 1) ≤ Y := by linarith
  -- nonemptiness and choice of one point per piece
  have hne : ∀ j, (W j).Nonempty := fun j => by
    obtain ⟨u, hu, -⟩ := hstep j
    exact ⟨u, hu⟩
  choose p hp using hne
  have hdiam_le : ∀ j, ∀ x ∈ W j, ∀ y ∈ W j, dist x y < 1 / 2 := fun j x hx y hy =>
    lt_of_le_of_lt (Metric.dist_le_diam_of_mem (hbdd j) hx hy) (hdiam j)
  have hlip : ∀ j, |(p (j + 1)).im - (p j).im| ≤ C₀ + 1 := by
    intro j
    obtain ⟨u, hu, u', hu', hd⟩ := hstep j
    have hu1 : ‖p (j + 1) - u'‖ < 1 / 2 := by
      have := hdiam_le (j + 1) (p (j + 1)) (hp (j + 1)) u' hu'
      rwa [dist_eq_norm] at this
    have hu2 : ‖u - p j‖ < 1 / 2 := by
      have := hdiam_le j (p j) (hp j) u hu
      rw [dist_eq_norm] at this
      rwa [norm_sub_rev] at this
    have hu3 : ‖u' - u‖ < C₀ := by rwa [norm_sub_rev] at hd
    have hsum : ‖p (j + 1) - p j‖ < 1 / 2 + C₀ + 1 / 2 := by
      have h3 : ‖p (j + 1) - p j‖ ≤ ‖p (j + 1) - u'‖ + ‖u' - u‖ + ‖u - p j‖ := by
        have heq : p (j + 1) - p j = (p (j + 1) - u') + (u' - u) + (u - p j) := by ring
        rw [heq]; exact norm_add₃_le
      linarith
    have h7 : |(p (j + 1)).im - (p j).im| ≤ ‖p (j + 1) - p j‖ := by
      have := Complex.abs_im_le_norm (p (j + 1) - p j)
      rwa [Complex.sub_im] at this
    linarith
  obtain ⟨j₀, w₀, hw₀, hlow_im⟩ := hlow
  have htlow : (p j₀).im - Y ≤ -(Y / 8) := by
    have h1 : ‖p j₀ - w₀‖ < 1 / 2 := by
      have := hdiam_le j₀ (p j₀) (hp j₀) w₀ hw₀
      rwa [dist_eq_norm] at this
    have h3 : |(p j₀).im - w₀.im| ≤ ‖p j₀ - w₀‖ := by
      have := Complex.abs_im_le_norm (p j₀ - w₀)
      rwa [Complex.sub_im] at this
    have h4 : (p j₀).im - w₀.im < 1 / 2 := lt_of_le_of_lt (le_trans (le_abs_self _) h3) h1
    have h5 : (p j₀).im < Y / 4 + 1 / 2 := by linarith
    linarith
  obtain ⟨J₀, hJ₀⟩ := hup (2 * Y)
  let J : ℕ := max J₀ (j₀ + 1)
  have hJge : J₀ ≤ J := le_max_left _ _
  have hJgt : j₀ < J := by
    have : j₀ + 1 ≤ J := le_max_right _ _
    omega
  have hthigh : Y / 8 ≤ (p J).im - Y := by
    have h : 2 * Y < (p J).im := hJ₀ J hJge (p J) (hp J)
    linarith
  let t : ℕ → ℝ := fun j => (p j).im - Y
  have hlip_t : ∀ j, |t (j + 1) - t j| ≤ C₀ + 1 := by
    intro j; simpa [t] using hlip j
  let A : Finset ℕ := (Finset.Icc j₀ J).filter (fun j => |t j| ≤ Y / 8)
  have hAcard : Y / (8 * (C₀ + 1)) ≤ (A.card : ℝ) := by
    have h := lipschitz_window_card t (C₀ + 1) (Y / 8) hδpos hlip_t (le_of_lt hJgt)
      (by simpa [t] using htlow) (by simpa [t] using hthigh)
    have h2 : 2 * (Y / 8) / (C₀ + 1) - 1 ≥ Y / (8 * (C₀ + 1)) := by
      have h3 : 1 ≤ Y / (8 * (C₀ + 1)) := by
        rw [le_div_iff₀ (by positivity)]
        linarith
      have h4 : 2 * (Y / 8) / (C₀ + 1) = (Y / (8 * (C₀ + 1))) * 2 := by
        field_simp
      rw [h4]
      linarith
    linarith
  have hex' : ∀ j : ℕ, ∃ K : Finset ℤ, j ∈ A → (Y / 8 ≤ (K.card : ℝ)) ∧
      ∀ k ∈ K, (fun w : ℂ => w + ((k : ℤ) : ℂ)) '' W j ⊆
        Metric.closedBall (Complex.I * Y) (Y / 4) := by
    intro j
    by_cases hj : j ∈ A
    · have ht : |t j| ≤ Y / 8 := (Finset.mem_filter.mp hj).2
      have htwo : (4 : ℝ) ≤ Y / 4 := by linarith
      have him : |(p j).im - Y| ≤ (Y / 4) / 2 := by
        rw [show (Y / 4) / 2 = Y / 8 by ring]
        simpa [t] using ht
      obtain ⟨K, hcard, hsub⟩ := exists_shifts_card_rho (hp j) (hbdd j) (hdiam j) htwo him
      exact ⟨K, fun _ => ⟨by linarith, hsub⟩⟩
    · exact ⟨∅, fun h => absurd h hj⟩
  let K : ℕ → Finset ℤ := fun j => Classical.choose (hex' j)
  have hKcard : ∀ j ∈ A, Y / 8 ≤ ((K j).card : ℝ) :=
    fun j hj => ((Classical.choose_spec (hex' j)) hj).1
  have hKsub : ∀ j ∈ A, ∀ k ∈ K j,
      (fun w : ℂ => w + ((k : ℤ) : ℂ)) '' W j ⊆ Metric.closedBall (Complex.I * Y) (Y / 4) :=
    fun j hj k hk => ((Classical.choose_spec (hex' j)) hj).2 k hk
  let emb : ℕ → ℤ ↪ (ℕ × ℤ) := fun j => ⟨fun k => (j, k), fun a b h => by simpa using h⟩
  set S : Finset (ℕ × ℤ) := A.biUnion (fun j => (K j).map (emb j)) with hSdef
  have hcardS_nat : S.card = ∑ j ∈ A, (K j).card := by
    rw [hSdef, Finset.card_biUnion]
    · exact Finset.sum_congr rfl (fun j hj => Finset.card_map (emb j))
    · intro x hx y hy hxy
      show Disjoint ((K x).map (emb x)) ((K y).map (emb y))
      rw [Finset.disjoint_left]
      intro q hqx hqy
      rw [Finset.mem_map] at hqx hqy
      obtain ⟨k, _, hkq⟩ := hqx
      obtain ⟨k', _, hkq'⟩ := hqy
      exact hxy (Prod.mk.inj (hkq.trans hkq'.symm)).1
  have hcardS : (S.card : ℝ) = ∑ j ∈ A, ((K j).card : ℝ) := by
    rw [hcardS_nat]; push_cast; rfl
  refine ⟨S, ?_, ?_⟩
  · rw [hcardS]
    have h1 : Y ^ 2 / (64 * (C₀ + 1)) ≤ (A.card : ℝ) * (Y / 8) := by
      have h2 : (Y / (8 * (C₀ + 1))) * (Y / 8) = Y ^ 2 / (64 * (C₀ + 1)) := by
        field_simp
        ring
      rw [← h2]
      exact mul_le_mul_of_nonneg_right hAcard (by positivity)
    have h3 : (A.card : ℝ) * (Y / 8) = ∑ j ∈ A, (Y / 8 : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    have h4 : ∑ j ∈ A, (Y / 8 : ℝ) ≤ ∑ j ∈ A, ((K j).card : ℝ) :=
      Finset.sum_le_sum (fun j hj => hKcard j hj)
    linarith
  · intro q hq
    rw [hSdef] at hq
    rw [Finset.mem_biUnion] at hq
    obtain ⟨j, hjA, hqj⟩ := hq
    rw [Finset.mem_map] at hqj
    obtain ⟨k, hkK, hkq⟩ := hqj
    rw [← hkq]
    exact hKsub j hjA k hkK

/-- **Counting the lifted copies of the Lemma-6.2 chain.**  Let `W` be an `IsChain` marching to
the end indicated by `sgn` (`+1`: the upper end `iη'`; `-1`: the lower end `-iη'`), with the
counting anchor `hanchor`, and suppose the chain is fine enough (`64(C₀+1) ≤ η'`).  Then at least
`η'²/(64(C₀+1))` integer translates of the discs `W j` lie inside the perturbative disc
`closedBall (±iη') (η'/4)` (Shishikura's `D(η')`, the region where the fields of `P₁` are
available). -/
theorem chain_count_copies {R : ℂ → ℂ} {DR : Set ℂ} {β : ℂ} {ζa ζb : ℂ} {ρ sgn C₀ C₁ C₁' : ℝ}
    {W : ℕ → Set ℂ} (h : Work.L62.IsChain R β DR ζa ζb ρ sgn C₀ C₁ C₁' W) {η' : ℝ}
    (hC : 0 < C₀) (hY : 64 * (C₀ + 1) ≤ η')
    (hanchor : ∃ j₀ : ℕ, ∃ w ∈ W j₀, sgn * w.im < η' / 4) :
    ∃ S : Finset (ℕ × ℤ), (η' ^ 2 / (64 * (C₀ + 1)) ≤ (S.card : ℝ)) ∧
      ∀ q ∈ S, (fun w : ℂ => w + ((q.2 : ℤ) : ℂ)) '' W q.1 ⊆
        (if sgn = 1 then Metric.closedBall (Complex.I * η') (η' / 4)
          else Metric.closedBall (-Complex.I * η') (η' / 4)) := by
  have hbdd : ∀ j, Bornology.IsBounded (W j) := fun j => (h.bounded j).1
  have hdiam : ∀ j, Metric.diam (W j) < 1 / 2 := fun j => (h.bounded j).2
  rcases h.sign with hs | hs
  · -- upper end
    have hup : ∀ M : ℝ, ∃ J : ℕ, ∀ j, J ≤ j → ∀ w ∈ W j, M < w.im := by
      intro M
      obtain ⟨J, hJ⟩ := h.marching M
      exact ⟨J, fun j hj w hw => by simpa [hs] using hJ j hj w hw⟩
    have hlow : ∃ j₀ : ℕ, ∃ w ∈ W j₀, w.im < η' / 4 := by
      obtain ⟨j₀, w, hw, hlt⟩ := hanchor
      exact ⟨j₀, w, hw, by simpa [hs] using hlt⟩
    obtain ⟨S, hcard, hsub⟩ :=
      count_up_copies W C₀ η' hC hY hbdd hdiam h.close hup hlow
    exact ⟨S, hcard, fun q hq => by
      rw [if_pos hs]; exact hsub q hq⟩
  · -- lower end: reflect the whole chain by `w ↦ -w`
    have hneg : sgn = -1 := hs
    set W' : ℕ → Set ℂ := fun j => (fun w : ℂ => -w) '' W j with hW'def
    have hbdd' : ∀ j, Bornology.IsBounded (W' j) := by
      intro j
      obtain ⟨C, hCb⟩ := Metric.isBounded_iff.mp (hbdd j)
      refine Metric.isBounded_iff.mpr ⟨C, ?_⟩
      rintro x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
      have h1 : dist (-a) (-b) = dist a b := by
        rw [dist_eq_norm, dist_eq_norm, show -a - -b = -(a - b) by ring, norm_neg]
      rw [h1]
      exact hCb ha hb
    have hdiam' : ∀ j, Metric.diam (W' j) < 1 / 2 := by
      intro j
      change Metric.diam ((fun w : ℂ => -w) '' W j) < 1 / 2
      rw [Isometry.diam_image isometry_neg]
      exact hdiam j
    have hstep' : ∀ j, ∃ u ∈ W' j, ∃ u' ∈ W' (j + 1), ‖u - u'‖ < C₀ := by
      intro j
      obtain ⟨u, hu, u', hu', hd⟩ := h.close j
      exact ⟨-u, ⟨u, hu, by simp⟩, -u', ⟨u', hu', by simp⟩, by
        rw [show -u - -u' = -(u - u') by ring, norm_neg]; exact hd⟩
    have hup' : ∀ M : ℝ, ∃ J : ℕ, ∀ j, J ≤ j → ∀ w ∈ W' j, M < w.im := by
      intro M
      obtain ⟨J, hJ⟩ := h.marching M
      refine ⟨J, fun j hj w hw => ?_⟩
      obtain ⟨v, hv, rfl⟩ := hw
      have h1 : M < -v.im := by simpa [hneg] using hJ j hj v hv
      simpa using h1
    have hlow' : ∃ j₀ : ℕ, ∃ w ∈ W' j₀, w.im < η' / 4 := by
      obtain ⟨j₀, v, hv, hlt⟩ := hanchor
      refine ⟨j₀, -v, ⟨v, hv, by simp⟩, ?_⟩
      have h1 : -v.im < η' / 4 := by simpa [hneg] using hlt
      simpa using h1
    obtain ⟨S, hcard, hsub⟩ :=
      count_up_copies W' C₀ η' hC hY hbdd' hdiam' hstep' hup' hlow'
    refine ⟨S.map ⟨fun q : ℕ × ℤ => (q.1, -q.2), ?_⟩, ?_, ?_⟩
    · intro a b hab
      simp only [Prod.mk.injEq] at hab
      exact Prod.ext hab.1 (by simpa using hab.2)
    · rw [Finset.card_map]; exact hcard
    · rw [if_neg (by rw [hneg]; norm_num)]
      intro q hq
      rw [Finset.mem_map] at hq
      obtain ⟨q₁, hq₁, rfl⟩ := hq
      intro z hz
      obtain ⟨x, hx, rfl⟩ := hz
      have hmem : (-x + ((q₁.2 : ℤ) : ℂ)) ∈ (fun w : ℂ => w + ((q₁.2 : ℤ) : ℂ)) '' W' q₁.1 :=
        ⟨-x, ⟨x, hx, by simp⟩, by ring⟩
      have h4 := hsub q₁ hq₁ hmem
      rw [Metric.mem_closedBall, dist_eq_norm] at h4 ⊢
      have h5 : x + ((-q₁.2 : ℤ) : ℂ) - (-Complex.I * η')
          = -((-x + ((q₁.2 : ℤ) : ℂ)) - Complex.I * η') := by
        push_cast; ring
      show ‖x + ((-q₁.2 : ℤ) : ℂ) - (-Complex.I * η')‖ ≤ η' / 4
      rw [h5, norm_neg]
      exact h4

/-- The counting region of §6 Step 3: the disc `closedBall (iη) (η/8)` in the lifted coordinate.
It is contained in `Dsm η = closedBall (iη) (|η|/4)`, the region where `PertData.φ_star_close`
controls `φ*_f = τ₀⁻¹ ∘ φ_f`. -/
def Dflat (η : ℝ) : Set ℂ := Metric.closedBall (Complex.I * η) (|η| / 8)

/-- The `n`-th box of the level-0 count: a translate in `Re` of the rectangle
`(1/6, 1/3) × (η + log(1/2)/2π, η + log(3/2)/2π)`.  `π` maps it onto the annulus
`{e^{-2πη}/2 < ‖ζ‖ < 3e^{-2πη}/2}`; distinct `n` give disjoint boxes. -/
def box (η : ℝ) (n : ℤ) : Set ℂ :=
  {z : ℂ | (n : ℝ) + 1 / 6 < z.re ∧ z.re < (n : ℝ) + 1 / 3 ∧
    η + Real.log (1 / 2) / (2 * Real.pi) < z.im ∧
    z.im < η + Real.log (3 / 2) / (2 * Real.pi)}

end Work.Repel
