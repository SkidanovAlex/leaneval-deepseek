import Mathlib
import Submission.Work.Spike.twoPoints_pieces
import Submission.Work.Spike.nonSeparatingContinuaSeparate

/-!
# The union of two continua meeting in two points separates the plane

`Work.Spike.unionTwoContinuaSeparates`: if `K₁`, `K₂ ⊆ ℂ` are compact and preconnected and meet in
exactly two points `p ≠ q`, then there are two points `a`, `b` of the complement of `K₁ ∪ K₂` which
lie in *different* connected components of that complement (Janiszewski's theorem B: the sum of two
compact continua cuts the plane when their common part is not connected).

The proof is elementary and by contradiction.  Assume `(K₁ ∪ K₂)ᶜ` preconnected.

* Put `W := (K₁ ∪ K₂)ᶜ`.  Since `W` is preconnected and contained in the open set `K₂ᶜ`, it lies in
  a component `V₂` of `K₂ᶜ`; the frontier of a component of an open set lies in the complement, so
  `frontier V₂ ⊆ K₂` (and symmetrically `frontier V₁ ⊆ K₁` for the component `V₁` of `K₁ᶜ`).
* Hence `frontier W ⊆ {p, q}`: a point `x ∈ frontier W` lies in `K₁ ∪ K₂`; if it were in `K₁ ∖ {p,q}`
  then `x ∉ K₂` so `x ∉ V₂`, while `x ∈ closure W ⊆ closure V₂`, i.e. `x ∈ frontier V₂ ⊆ K₂`, a
  contradiction; the case `x ∈ K₂ ∖ {p,q}` is symmetric.
* So `(K₁ ∪ K₂) ∖ {p,q} ⊆ int (K₁ ∪ K₂)`.  A small ball around `x ∈ K₁ ∖ {p,q}` is then contained in
  `K₁ ∪ K₂` and avoids `{p,q}`, so it is covered by the two disjoint closed pieces `∩ K₁`, `∩ K₂`;
  being preconnected it lies in one of them, hence `x ∈ int K₁`.
* Therefore `U := int K₁` is open, bounded and non-empty with `frontier U ⊆ {p,q}` — impossible,
  since a ray from a point of `U`, in a direction avoiding the two points `p`, `q`, must leave the
  bounded set `U` at a point of its frontier, which is then not `p` or `q`.
-/

namespace Work.Spike

open Set

noncomputable section

/-- The frontier of a connected component of an open subset of `ℂ` lies in its complement. -/
theorem frontier_connectedComponentIn_subset_compl {O : Set ℂ} (hO : IsOpen O) {x : ℂ}
    (hx : x ∈ O) : frontier (connectedComponentIn O x) ⊆ (Oᶜ : Set ℂ) := by
  have hVopen : IsOpen (connectedComponentIn O x) := hO.connectedComponentIn
  rw [hVopen.frontier_eq]
  rintro z ⟨hzc, hzV⟩ hzO
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO z hzO
  obtain ⟨y, hyV, hzy⟩ := Metric.mem_closure_iff.mp hzc ε hε
  have hyball : y ∈ Metric.ball z ε := by rw [Metric.mem_ball, dist_comm]; exact hzy
  have hpre : IsPreconnected (Metric.ball z ε ∪ connectedComponentIn O x) :=
    IsPreconnected.union y hyball hyV (convex_ball z ε).isPreconnected
      isPreconnected_connectedComponentIn
  have hsubO : Metric.ball z ε ∪ connectedComponentIn O x ⊆ O :=
    fun w hw => hw.elim (fun h => hball h) (fun h => connectedComponentIn_subset O x h)
  have hzV' : z ∈ connectedComponentIn O y :=
    (hpre.subset_connectedComponentIn (x := y) (Or.inl hyball) hsubO)
      (Or.inl (Metric.mem_ball_self hε))
  rw [← connectedComponentIn_eq hyV] at hzV'
  exact hzV hzV'

/-- An open non-empty subset of `ℂ` contains a point outside any prescribed two-point set. -/
theorem exists_mem_notMem_pair {U : Set ℂ} (hUo : IsOpen U) (hUne : U.Nonempty) {p q : ℂ} :
    ∃ a ∈ U, a ∉ ({p, q} : Set ℂ) := by
  by_contra h
  push_neg at h
  have hint : interior ({p, q} : Set ℂ) = ∅ := by
    rw [interior_eq_empty_iff_dense_compl]
    exact (Set.toFinite ({p, q} : Set ℂ)).countable.dense_compl ℂ
  have hsub : U ⊆ interior ({p, q} : Set ℂ) := interior_maximal (fun w hw => h w hw) hUo
  obtain ⟨a, ha⟩ := hUne
  rw [hint] at hsub
  exact hsub ha

/-- Given two nonzero `d₀, d₁ : ℂ` there is a direction `w ≠ 0` such that no positive multiple of
`w` equals `d₀` or `d₁`. -/
theorem exists_direction {d₀ d₁ : ℂ} (h₀ : d₀ ≠ 0) (h₁ : d₁ ≠ 0) :
    ∃ w : ℂ, w ≠ 0 ∧ (∀ t : ℝ, 0 < t → t • w ≠ d₀) ∧ (∀ t : ℝ, 0 < t → t • w ≠ d₁) := by
  by_cases hpar : ∃ c : ℝ, d₁ = c • d₀
  · refine ⟨Complex.I * d₀, mul_ne_zero Complex.I_ne_zero h₀, ?_, ?_⟩
    · intro t _ h
      rw [Complex.real_smul] at h
      have h' : (↑t * Complex.I - 1) * d₀ = 0 := by
        rw [sub_mul, one_mul, mul_assoc, h, sub_self]
      rcases mul_eq_zero.mp h' with h2 | h2
      · have := congrArg Complex.re (sub_eq_zero.mp h2)
        simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
          Complex.I_im] at this
      · exact h₀ h2
    · intro t _ h
      obtain ⟨c, hc⟩ := hpar
      rw [hc] at h
      simp only [Complex.real_smul] at h
      have h' : (↑t * Complex.I - ↑c) * d₀ = 0 := by
        rw [sub_mul, mul_assoc, h, sub_self]
      rcases mul_eq_zero.mp h' with h2 | h2
      · have hc0 : c = 0 := by
          have := congrArg Complex.re (sub_eq_zero.mp h2)
          simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
            Complex.I_im] at this
          exact this.symm
        rw [hc0, zero_smul] at hc
        exact h₁ hc
      · exact h₀ h2
  · refine ⟨d₀ + d₁, ?_, ?_, ?_⟩
    · intro hz
      refine hpar ⟨-1, ?_⟩
      rw [neg_smul, one_smul, eq_neg_iff_add_eq_zero, add_comm]
      exact hz
    · intro t ht h
      have htne : t ≠ 0 := ne_of_gt ht
      have h4 : t • d₁ = d₀ - t • d₀ := by
        rw [smul_add] at h; rw [eq_sub_iff_add_eq, add_comm]; exact h
      have h3 : t • d₁ = (1 - t) • d₀ := by rw [h4, sub_smul, one_smul]
      have h2 : d₁ = (t⁻¹ * (1 - t)) • d₀ := by
        calc d₁ = (1 : ℝ) • d₁ := (one_smul _ _).symm
          _ = (t⁻¹ * t) • d₁ := by rw [inv_mul_cancel₀ htne, one_smul]
          _ = t⁻¹ • (t • d₁) := (smul_smul _ _ _).symm
          _ = t⁻¹ • ((1 - t) • d₀) := by rw [h3]
          _ = (t⁻¹ * (1 - t)) • d₀ := smul_smul _ _ _
      exact hpar ⟨t⁻¹ * (1 - t), h2⟩
    · intro t ht h
      have htne : t ≠ 0 := ne_of_gt ht
      have h4 : t • d₀ = d₁ - t • d₁ := by
        rw [smul_add] at h; rw [eq_sub_iff_add_eq]; exact h
      have h3 : t • d₀ = (1 - t) • d₁ := by rw [h4, sub_smul, one_smul]
      have h2 : d₀ = (t⁻¹ * (1 - t)) • d₁ := by
        calc d₀ = (1 : ℝ) • d₀ := (one_smul _ _).symm
          _ = (t⁻¹ * t) • d₀ := by rw [inv_mul_cancel₀ htne, one_smul]
          _ = t⁻¹ • (t • d₀) := (smul_smul _ _ _).symm
          _ = t⁻¹ • ((1 - t) • d₁) := by rw [h3]
          _ = (t⁻¹ * (1 - t)) • d₁ := smul_smul _ _ _
      have hBne : t⁻¹ * (1 - t) ≠ 0 := by
        intro hz
        exact h₀ (by rw [h2, hz, zero_smul])
      exact hpar ⟨(t⁻¹ * (1 - t))⁻¹, by rw [h2, smul_smul, inv_mul_cancel₀ hBne, one_smul]⟩

/-- A non-empty open bounded subset of `ℂ` cannot have its frontier contained in a two-point set. -/
theorem not_open_bounded_frontier_subset_pair {U : Set ℂ} (hUo : IsOpen U)
    (hUb : Bornology.IsBounded U) (hUne : U.Nonempty) {p q : ℂ}
    (hfr : frontier U ⊆ ({p, q} : Set ℂ)) : False := by
  obtain ⟨a, haU, hapq⟩ := exists_mem_notMem_pair hUo hUne
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hapq
  push_neg at hapq
  obtain ⟨hap, haq⟩ := hapq
  have hpa : p - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hap)
  have hqa : q - a ≠ 0 := sub_ne_zero.mpr (Ne.symm haq)
  obtain ⟨w, hwne, hw0, hw1⟩ := exists_direction (d₀ := p - a) (d₁ := q - a) hpa hqa
  obtain ⟨R, hR⟩ := hUb.subset_closedBall (0 : ℂ)
  have hRge : 0 ≤ R := by
    have h := hR haU
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h
    linarith [norm_nonneg a]
  have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hwne
  have hRapos : 0 < R + ‖a‖ + 1 := by linarith [norm_nonneg a]
  have hexit : ∃ t : ℝ, 0 ≤ t ∧ a + t • w ∉ U := by
    refine ⟨(R + ‖a‖ + 1) / ‖w‖, le_of_lt (div_pos hRapos hwpos), ?_⟩
    intro hmem
    have h1 : ‖a + ((R + ‖a‖ + 1) / ‖w‖) • w‖ ≤ R := by
      have := hR hmem
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at this
      exact this
    have h2 : ((R + ‖a‖ + 1) / ‖w‖) * ‖w‖ ≤ ‖a + ((R + ‖a‖ + 1) / ‖w‖) • w‖ + ‖a‖ := by
      have h3 : ‖((R + ‖a‖ + 1) / ‖w‖) • w‖ ≤
          ‖a + ((R + ‖a‖ + 1) / ‖w‖) • w‖ + ‖a‖ := by
        have h4 := norm_sub_le (a + ((R + ‖a‖ + 1) / ‖w‖) • w) a
        rwa [add_sub_cancel_left] at h4
      rwa [norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt (div_pos hRapos hwpos))] at h3
    have h5 : ((R + ‖a‖ + 1) / ‖w‖) * ‖w‖ = R + ‖a‖ + 1 := by
      field_simp
    linarith [h1, h2, h5]
  set S : Set ℝ := {t | 0 ≤ t ∧ a + t • w ∉ U} with hSdef
  have hSne : S.Nonempty := hexit
  have hScl : IsClosed S := by
    have heq : S = Set.Ici (0 : ℝ) ∩ {t | a + t • w ∉ U} := by
      ext t; simp only [hSdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_Ici]
    rw [heq]
    exact isClosed_Ici.inter (hUo.isClosed_compl.preimage (by fun_prop))
  have hSbdd : BddBelow S := ⟨0, fun t ht => ht.1⟩
  set t₀ := sInf S with ht₀def
  have ht₀S : t₀ ∈ S := hScl.csInf_mem hSne hSbdd
  have ht₀lb : ∀ t ∈ S, t₀ ≤ t := fun t ht => csInf_le hSbdd ht
  have ht₀pos : 0 < t₀ := by
    rcases ht₀S with ⟨hge, hnotU⟩
    rcases lt_or_eq_of_le hge with h | h
    · exact h
    · exfalso
      exact hnotU (by rw [← h, zero_smul, add_zero]; exact haU)
  have hcl : a + t₀ • w ∈ closure U := by
    rw [Metric.mem_closure_iff]
    intro ε hε
    refine ⟨a + (t₀ - min (t₀ / 2) (ε / (2 * ‖w‖ + 2))) • w, ?_, ?_⟩
    · have hδpos : 0 < min (t₀ / 2) (ε / (2 * ‖w‖ + 2)) :=
        lt_min (by positivity) (div_pos hε (by positivity))
      have hδlt : min (t₀ / 2) (ε / (2 * ‖w‖ + 2)) < t₀ :=
        lt_of_le_of_lt (min_le_left _ _) (by linarith)
      have htge : 0 ≤ t₀ - min (t₀ / 2) (ε / (2 * ‖w‖ + 2)) := by linarith
      have hnotS : t₀ - min (t₀ / 2) (ε / (2 * ‖w‖ + 2)) ∉ S :=
        fun hmem => absurd (ht₀lb _ hmem) (by linarith)
      simp only [hSdef, Set.mem_setOf_eq, not_and, not_not] at hnotS
      exact hnotS htge
    · rw [dist_eq_norm]
      have heq : a + t₀ • w - (a + (t₀ - min (t₀ / 2) (ε / (2 * ‖w‖ + 2))) • w)
          = (min (t₀ / 2) (ε / (2 * ‖w‖ + 2))) • w := by
        rw [add_sub_add_left_eq_sub, ← sub_smul]
        congr 1
        ring
      rw [heq, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (le_of_lt (lt_min (by positivity) (div_pos hε (by positivity))))]
      calc min (t₀ / 2) (ε / (2 * ‖w‖ + 2)) * ‖w‖ ≤ (ε / (2 * ‖w‖ + 2)) * ‖w‖ :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg _)
        _ < ε := by
            rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
            nlinarith [norm_nonneg w]
  have hfrmem : a + t₀ • w ∈ frontier U := by
    rw [hUo.frontier_eq]
    exact ⟨hcl, ht₀S.2⟩
  have hmem : a + t₀ • w ∈ ({p, q} : Set ℂ) := hfr hfrmem
  rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with h | h
  · exact hw0 t₀ ht₀pos (sub_eq_zero.mp (by rw [← h]; abel))
  · exact hw1 t₀ ht₀pos (sub_eq_zero.mp (by rw [← h]; abel))

theorem unionTwoContinuaSeparates {K₁ K₂ : Set ℂ} (h₁ : IsCompact K₁) (h₂ : IsCompact K₂)
    (hc₁ : IsPreconnected K₁) (hc₂ : IsPreconnected K₂) {p q : ℂ} (hpq : p ≠ q)
    (hint : K₁ ∩ K₂ = {p, q}) :
    ∃ a b : ℂ, a ∉ K₁ ∪ K₂ ∧ b ∉ K₁ ∪ K₂ ∧
      b ∉ connectedComponentIn (K₁ ∪ K₂)ᶜ a := by
  by_contra hcon
  push_neg at hcon
  have hcon' : ∀ a b : ℂ, a ∉ K₁ ∪ K₂ → b ∉ K₁ ∪ K₂ →
      b ∈ connectedComponentIn (K₁ ∪ K₂)ᶜ a := hcon
  have hKcpt : IsCompact (K₁ ∪ K₂) := h₁.union h₂
  -- the complement of the union is non-empty
  have hWne : ((K₁ ∪ K₂)ᶜ : Set ℂ).Nonempty := by
    have hp12 : p ∈ K₁ := (by rw [hint]; exact Or.inl rfl : p ∈ K₁ ∩ K₂).1
    obtain ⟨R, hR⟩ := hKcpt.isBounded.subset_closedBall (0 : ℂ)
    have hRp : 0 ≤ R := by
      have h2 := hR (Or.inl hp12)
      rw [Metric.mem_closedBall, dist_eq_norm, sub_zero] at h2
      exact le_trans (norm_nonneg p) h2
    refine ⟨(R + 1) • (1 : ℂ), ?_⟩
    intro hmem
    have h2 := hR hmem
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by linarith), norm_one, mul_one] at h2
    linarith
  obtain ⟨w₀, hw₀⟩ := hWne
  -- the complement of the union is preconnected (that is the negation of the goal)
  have hpre : IsPreconnected ((K₁ ∪ K₂)ᶜ : Set ℂ) := by
    have heq : ((K₁ ∪ K₂)ᶜ : Set ℂ) = connectedComponentIn ((K₁ ∪ K₂)ᶜ) w₀ :=
      Subset.antisymm (fun y hy => hcon' w₀ y hw₀ hy) (connectedComponentIn_subset _ _)
    rw [heq]; exact isPreconnected_connectedComponentIn
  -- under this assumption the complement of each `Kᵢ` is preconnected as well
  have hd₁ : IsPreconnected (K₁ᶜ : Set ℂ) := by
    set V₁ : Set ℂ := connectedComponentIn (K₁ᶜ) w₀ with hV₁def
    have hw₁ : w₀ ∈ (K₁ᶜ : Set ℂ) := fun h => hw₀ (Or.inl h)
    have hsubV₁ : ((K₁ ∪ K₂)ᶜ : Set ℂ) ⊆ V₁ := by
      rw [hV₁def]
      exact hpre.subset_connectedComponentIn hw₀ (fun z hz => fun h => hz (Or.inl h))
    have heq : (K₁ᶜ : Set ℂ) = V₁ := by
      refine Subset.antisymm ?_ (by rw [hV₁def]; exact connectedComponentIn_subset _ _)
      intro x hx
      by_contra hxV₁
      have hx' : x ∈ (K₁ᶜ : Set ℂ) := hx
      set V' : Set ℂ := connectedComponentIn (K₁ᶜ) x with hV'def
      have hV'ne : V'.Nonempty := ⟨x, mem_connectedComponentIn hx'⟩
      have hV'open : IsOpen V' := h₁.isClosed.isOpen_compl.connectedComponentIn
      have hV'sub₂ : V' ⊆ K₂ := by
        intro y hy
        by_contra hyK₂
        have hyW : y ∈ ((K₁ ∪ K₂)ᶜ : Set ℂ) :=
          fun h => h.elim (fun h1 => (connectedComponentIn_subset _ _ hy : y ∈ K₁ᶜ) h1) hyK₂
        have : y ∈ V₁ := hsubV₁ hyW
        have hyV' : y ∈ V' := hy
        rw [hV₁def] at this
        have hdisj : Disjoint V' V₁ := by
          rw [Set.disjoint_left]
          intro z hzV' hzV₁
          have h1 : connectedComponentIn (K₁ᶜ) x = connectedComponentIn (K₁ᶜ) z :=
            connectedComponentIn_eq hzV'
          have h2 : connectedComponentIn (K₁ᶜ) w₀ = connectedComponentIn (K₁ᶜ) z :=
            connectedComponentIn_eq hzV₁
          exact hxV₁ (by rw [hV₁def, h2, ← h1]; exact mem_connectedComponentIn hx')
        exact (Set.disjoint_left.mp hdisj hyV') this
      have hV'bdd : Bornology.IsBounded V' := h₂.isBounded.subset hV'sub₂
      have hfr₁ : frontier V' ⊆ K₁ := by
        rw [hV'def]
        have h := frontier_connectedComponentIn_subset_compl h₁.isClosed.isOpen_compl hx'
        rwa [compl_compl] at h
      have hfr₂ : frontier V' ⊆ K₂ := fun z hz =>
        h₂.isClosed.closure_eq ▸ closure_mono hV'sub₂ (frontier_subset_closure hz)
      refine not_open_bounded_frontier_subset_pair (p := p) (q := q) hV'open hV'bdd hV'ne ?_
      intro z hz
      exact hint ▸ (⟨hfr₁ hz, hfr₂ hz⟩ : z ∈ K₁ ∩ K₂)
    rw [heq]
    exact isPreconnected_connectedComponentIn
  have hd₂ : IsPreconnected (K₂ᶜ : Set ℂ) := by
    set V₂ : Set ℂ := connectedComponentIn (K₂ᶜ) w₀ with hV₂def
    have hw₂ : w₀ ∈ (K₂ᶜ : Set ℂ) := fun h => hw₀ (Or.inr h)
    have hsubV₂ : ((K₁ ∪ K₂)ᶜ : Set ℂ) ⊆ V₂ := by
      rw [hV₂def]
      exact hpre.subset_connectedComponentIn hw₀ (fun z hz => fun h => hz (Or.inr h))
    have heq : (K₂ᶜ : Set ℂ) = V₂ := by
      refine Subset.antisymm ?_ (by rw [hV₂def]; exact connectedComponentIn_subset _ _)
      intro x hx
      by_contra hxV₂
      have hx' : x ∈ (K₂ᶜ : Set ℂ) := hx
      set V' : Set ℂ := connectedComponentIn (K₂ᶜ) x with hV'def
      have hV'ne : V'.Nonempty := ⟨x, mem_connectedComponentIn hx'⟩
      have hV'open : IsOpen V' := h₂.isClosed.isOpen_compl.connectedComponentIn
      have hV'sub₁ : V' ⊆ K₁ := by
        intro y hy
        by_contra hyK₁
        have hyW : y ∈ ((K₁ ∪ K₂)ᶜ : Set ℂ) :=
          fun h => h.elim hyK₁ (fun h2 => (connectedComponentIn_subset _ _ hy : y ∈ K₂ᶜ) h2)
        have : y ∈ V₂ := hsubV₂ hyW
        have hyV' : y ∈ V' := hy
        rw [hV₂def] at this
        have hdisj : Disjoint V' V₂ := by
          rw [Set.disjoint_left]
          intro z hzV' hzV₂
          have h1 : connectedComponentIn (K₂ᶜ) x = connectedComponentIn (K₂ᶜ) z :=
            connectedComponentIn_eq hzV'
          have h2 : connectedComponentIn (K₂ᶜ) w₀ = connectedComponentIn (K₂ᶜ) z :=
            connectedComponentIn_eq hzV₂
          exact hxV₂ (by rw [hV₂def, h2, ← h1]; exact mem_connectedComponentIn hx')
        exact (Set.disjoint_left.mp hdisj hyV') this
      have hV'bdd : Bornology.IsBounded V' := h₁.isBounded.subset hV'sub₁
      have hfr₁ : frontier V' ⊆ K₂ := by
        rw [hV'def]
        have h := frontier_connectedComponentIn_subset_compl h₂.isClosed.isOpen_compl hx'
        rwa [compl_compl] at h
      have hfr₂ : frontier V' ⊆ K₁ := fun z hz =>
        h₁.isClosed.closure_eq ▸ closure_mono hV'sub₁ (frontier_subset_closure hz)
      refine not_open_bounded_frontier_subset_pair (p := p) (q := q) hV'open hV'bdd hV'ne ?_
      intro z hz
      exact hint ▸ (⟨hfr₂ hz, hfr₁ hz⟩ : z ∈ K₁ ∩ K₂)
    rw [heq]
    exact isPreconnected_connectedComponentIn
  obtain ⟨a, b, ha, hb, hcomp⟩ :=
    Work.Spike.nonSeparatingContinuaSeparate h₁ h₂ hc₁ hc₂ hd₁ hd₂ hpq hint
  exact hcomp (hcon' a b ha hb)

end

end Work.Spike
