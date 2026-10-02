import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Conc.Pi
import Submission.Work.Deep.Prob.Chernoff.chernoff_upper

namespace Work.Deep.Kahn

open scoped BigOperators

/-- **Bridge between the two finite probability layers.**  On `Fin m → Fin k` (`k ≥ 1`) the
uniform counting probability of `Work.Deep.Conc` coincides with the `mass`-weighted
probability of the `FinProbSpace` layer: both are `|E| / k ^ m`.

This is what lets the concentration results proved for abstract finite probability spaces
(`Work.Deep.Prob`) be applied to the uniform product space of `Work.Deep.Conc`. -/
lemma conc_prob_eq_uniformColouring {m k : ℕ} (hk : 0 < k) (E : Set (Fin m → Fin k)) :
    Work.Deep.Conc.prob E
      = (Work.Deep.Prob.FinProbSpace.uniformColouring m k hk).prob E := by
  have hconst : ∀ (ω : Fin m → Fin k) (a : ℝ),
      E.indicator (fun _ : Fin m → Fin k => a) ω = a * E.indicator (fun _ => (1 : ℝ)) ω := by
    intro ω a
    by_cases h : ω ∈ E
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem h, mul_one]
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem h, mul_zero]
  have hmass : (Work.Deep.Prob.FinProbSpace.uniformColouring m k hk).mass
      = fun _ : Fin m → Fin k => ((Fintype.card (Fin m → Fin k) : ℕ) : ℝ)⁻¹ := by
    funext ω
    exact Work.Deep.Prob.FinProbSpace.uniformColouring_mass ω
  rw [Work.Deep.Prob.FinProbSpace.prob, hmass,
    Finset.sum_congr rfl (fun ω _ => hconst ω _), ← Finset.mul_sum]
  rw [Work.Deep.Conc.prob, Work.Deep.Conc.expect, div_eq_inv_mul]

/-- **Marginal law of a coordinate.**  Under the uniform measure on `Fin m → Fin k` the
probability that coordinate `i` lands in `b` is `|b| / k`. -/
lemma uniformColouring_prob_cyl {m k : ℕ} (hk : 0 < k) (i : Fin m) (b : Finset (Fin k)) :
    (Work.Deep.Prob.FinProbSpace.uniformColouring m k hk).prob {ω : Fin m → Fin k | ω i ∈ b}
      = (b.card : ℝ) / (k : ℝ) := by
  have hne : ∀ _ : Fin m, Nonempty (Fin k) := fun _ => ⟨⟨0, hk⟩⟩
  rw [← conc_prob_eq_uniformColouring hk]
  have h1 : Work.Deep.Conc.prob {ω : Fin m → Fin k | ω i ∈ b}
      = Work.Deep.Conc.expect (fun ω : Fin m → Fin k =>
          if ω i ∈ b then (1 : ℝ) else 0) := by
    apply Work.Deep.Conc.expect_congr
    intro ω
    by_cases h : ω i ∈ b
    · rw [Set.indicator_of_mem (s := {ω : Fin m → Fin k | ω i ∈ b})
          (show ω ∈ {ω : Fin m → Fin k | ω i ∈ b} from h), if_pos h]
    · rw [Set.indicator_of_notMem (s := {ω : Fin m → Fin k | ω i ∈ b})
          (show ω ∉ {ω : Fin m → Fin k | ω i ∈ b} from h), if_neg h]
  rw [h1, Work.Deep.Conc.expect_coord i (fun a : Fin k => if a ∈ b then (1 : ℝ) else 0) hne]
  have hsum : (∑ a : Fin k, (if a ∈ b then (1 : ℝ) else 0)) = (b.card : ℝ) := by
    rw [Finset.sum_boole]
    rw [show (Finset.univ.filter (fun a : Fin k => a ∈ b)) = b from by ext a; simp]
  rw [hsum, Fintype.card_fin]

/-- **Independence of the coordinate "bad set" events.**  For arbitrary bad sets
`B i : Finset (Fin k)`, the events `{ω | ω i ∈ B i}` are independent under the uniform measure
on `Fin m → Fin k`.  (The coordinates of the product space are independent; this is the
event-level form of that fact, showing that the family has the product law of its outcome
pattern, i.e. that `FinProbSpace.IndepEvents` holds.)

The proof computes both sides with the coordinate-independence results of
`Work.Deep.Conc.Pi`: the indicator of an atom of the pattern of the family is the product
`∏ i, 1[decide (ω i ∈ B i) = s i]` of the coordinate indicators, whose expectation
factorises (`expect_prod_coord`), while the marginal of a single (possibly complemented)
event is `(∑ a, 1[decide (a ∈ B i) = s i]) / k` (`expect_coord`). -/
lemma uniformColouring_indep_cyl {m k : ℕ} (hk : 0 < k) (B : Fin m → Finset (Fin k)) :
    Work.Deep.Prob.FinProbSpace.IndepEvents
      (Work.Deep.Prob.FinProbSpace.uniformColouring m k hk)
      (fun i : Fin m => {ω : Fin m → Fin k | ω i ∈ B i}) := by
  intro s
  set A : Fin m → Set (Fin m → Fin k) := fun i => {ω | ω i ∈ B i} with hA
  set f : (i : Fin m) → Fin k → ℝ :=
    fun i a => if decide (a ∈ B i) = s i then (1 : ℝ) else 0 with hf
  have hf_apply : ∀ (i : Fin m) (a : Fin k),
      f i a = if decide (a ∈ B i) = s i then (1 : ℝ) else 0 := by
    intro i a; rw [hf]
  have hAmem : ∀ (i : Fin m) (ω : Fin m → Fin k), (ω ∈ A i) ↔ ω i ∈ B i := by
    intro i ω; rw [hA]; rfl
  have hne : ∀ _ : Fin m, Nonempty (Fin k) := fun _ => ⟨⟨0, hk⟩⟩
  have hmem : ∀ (ω : Fin m → Fin k) (i : Fin m),
      (ω ∈ (if s i then A i else (A i)ᶜ)) ↔ decide (ω i ∈ B i) = s i := by
    intro ω i
    by_cases hsi : s i = true
    · rw [if_pos hsi, hAmem i ω, hsi]
      exact decide_eq_true_iff.symm
    · have hsi' : s i = false := by cases h : s i <;> simp_all
      rw [if_neg hsi, Set.mem_compl_iff, hAmem i ω, hsi', decide_eq_false_iff_not]
  have hprod_if : ∀ ω : Fin m → Fin k,
      ∏ i : Fin m, f i (ω i)
        = if (∀ i, decide (ω i ∈ B i) = s i) then (1 : ℝ) else 0 := by
    intro ω
    by_cases hall : ∀ i, decide (ω i ∈ B i) = s i
    · rw [if_pos hall]
      refine Finset.prod_eq_one fun i _ => ?_
      rw [hf_apply]; simp [hall i]
    · rw [if_neg hall]
      push Not at hall
      obtain ⟨i, hi⟩ := hall
      refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
      rw [hf_apply]; simp [hi]
  have hpoint : ∀ ω : Fin m → Fin k,
      (⋂ i, if s i then A i else (A i)ᶜ).indicator (fun _ => (1 : ℝ)) ω = ∏ i, f i (ω i) := by
    intro ω
    have hmem' : (ω ∈ ⋂ i, if s i then A i else (A i)ᶜ)
        ↔ ∀ i, decide (ω i ∈ B i) = s i := by
      rw [Set.mem_iInter]; exact forall_congr' (fun i => hmem ω i)
    by_cases h : ω ∈ ⋂ i, if s i then A i else (A i)ᶜ
    · rw [Set.indicator_of_mem h, hprod_if, if_pos (hmem'.mp h)]
    · rw [Set.indicator_of_notMem h, hprod_if, if_neg (fun hh => h (hmem'.mpr hh))]
  have hsingle : ∀ (i : Fin m) (ω : Fin m → Fin k),
      (if s i then A i else (A i)ᶜ).indicator (fun _ => (1 : ℝ)) ω = f i (ω i) := by
    intro i ω
    by_cases h : ω ∈ (if s i then A i else (A i)ᶜ)
    · rw [Set.indicator_of_mem h, hf_apply, if_pos ((hmem ω i).mp h)]
    · rw [Set.indicator_of_notMem h, hf_apply, if_neg (fun hh => h ((hmem ω i).mpr hh))]
  have hL : (Work.Deep.Prob.FinProbSpace.uniformColouring m k hk).prob
        (⋂ i, if s i then A i else (A i)ᶜ)
      = ∏ i, ((∑ a, f i a) / (k : ℝ)) := by
    rw [← conc_prob_eq_uniformColouring hk, Work.Deep.Conc.prob]
    rw [Work.Deep.Conc.expect_congr (fun ω => hpoint ω)]
    rw [Work.Deep.Conc.expect_prod_coord Finset.univ f hne]
    simp
  have hR : ∏ i, (Work.Deep.Prob.FinProbSpace.uniformColouring m k hk).prob
        (if s i then A i else (A i)ᶜ)
      = ∏ i, ((∑ a, f i a) / (k : ℝ)) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← conc_prob_eq_uniformColouring hk, Work.Deep.Conc.prob]
    rw [Work.Deep.Conc.expect_congr (fun ω => hsingle i ω)]
    rw [Work.Deep.Conc.expect_coord i (f i) hne]
    simp
  rw [hL, hR]

/-- **The count of bad coordinates as a sum of indicators.** -/
lemma sum_indicator_eq_card_filter {m k : ℕ} (B : Fin m → Finset (Fin k)) (ω : Fin m → Fin k) :
    (∑ i : Fin m, ({ω' : Fin m → Fin k | ω' i ∈ B i} : Set (Fin m → Fin k)).indicator
        (fun _ => (1 : ℝ)) ω)
      = ((Finset.univ.filter (fun i : Fin m => ω i ∈ B i)).card : ℝ) := by
  have hsum : ((Finset.univ.filter (fun i : Fin m => ω i ∈ B i)).card : ℝ)
      = ∑ i : Fin m, (if ω i ∈ B i then (1 : ℝ) else 0) := by
    rw [Finset.sum_boole]
  rw [hsum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : ω i ∈ B i
  · rw [Set.indicator_of_mem (s := {ω' : Fin m → Fin k | ω' i ∈ B i})
        (show ω ∈ {ω' : Fin m → Fin k | ω' i ∈ B i} from h), if_pos h]
  · rw [Set.indicator_of_notMem (s := {ω' : Fin m → Fin k | ω' i ∈ B i})
        (show ω ∉ {ω' : Fin m → Fin k | ω' i ∈ B i} from h), if_neg h]

/-- **Chernoff bound on a uniform product space.**  Let `ω : Fin m → Fin k` be uniformly
random (each coordinate independently uniform on `Fin k`), let `B i : Finset (Fin k)` be "bad
sets", and let `μ := ∑ i, |B i| / k`.  Then for every `t ≥ 0` the probability that at least
`μ + t` coordinates land in their bad set is at most `exp (-(t^2) / (2 * (μ + t/3)))`. -/
theorem chernoff_uniform_prod {m k : ℕ} (B : Fin m → Finset (Fin k)) {t : ℝ} (ht : 0 ≤ t) :
    Work.Deep.Conc.prob {ω : Fin m → Fin k |
      (∑ i, (((B i).card : ℝ) / (k : ℝ))) + t ≤
        ((Finset.univ.filter (fun i => ω i ∈ B i)).card : ℝ)} ≤
      Real.exp (-(t^2) / (2 * ((∑ i, (((B i).card : ℝ) / (k : ℝ))) + t/3))) := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- Degenerate case `k = 0`: `Fin 0` is empty, so all bad sets are empty.
    subst hk0
    have hB0 : ∀ i : Fin m, B i = ∅ := by
      intro i
      rw [Finset.eq_empty_iff_forall_notMem]
      intro a
      exact fun _ => Fin.elim0 a
    have hfil : ∀ ω : Fin m → Fin 0,
        (Finset.univ.filter (fun i : Fin m => ω i ∈ B i)).card = 0 := by
      intro ω; simp [hB0]
    have hμ0 : (∑ i : Fin m, (((B i).card : ℝ) / ((0 : ℕ) : ℝ))) = 0 := by
      simp [hB0]
    have hEv : {ω : Fin m → Fin 0 |
          (∑ i : Fin m, (((B i).card : ℝ) / ((0 : ℕ) : ℝ))) + t ≤
            ((Finset.univ.filter (fun i : Fin m => ω i ∈ B i)).card : ℝ)}
        = {ω : Fin m → Fin 0 | t ≤ 0} := by
      ext ω
      simp only [Set.mem_ofPred_eq]
      rw [hμ0, zero_add, hfil ω]
      simp
    rcases eq_or_lt_of_le ht with ht0 | htpos
    · -- `t = 0`: the event is everything and the bound is `1`.
      subst ht0
      rw [hEv]
      have h1 : Work.Deep.Conc.prob {ω : Fin m → Fin 0 | (0 : ℝ) ≤ 0} ≤ 1 := by
        rcases Nat.eq_zero_or_pos (Fintype.card (Fin m → Fin 0)) with hc | hc
        · rw [Work.Deep.Conc.prob, Work.Deep.Conc.expect, hc]
          norm_num
        · exact Work.Deep.Conc.prob_le_one _ hc
      refine le_trans h1 ?_
      norm_num
    · -- `t > 0`: the event is empty.
      have hempty : {ω : Fin m → Fin 0 | t ≤ (0 : ℝ)} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.notMem_empty, iff_false, not_le]
        exact htpos
      rw [hEv, hempty, Work.Deep.Conc.prob_empty]
      exact (Real.exp_pos _).le
  · -- Main case `k ≥ 1`.
    let P := Work.Deep.Prob.FinProbSpace.uniformColouring m k hkpos
    set μ : ℝ := ∑ i : Fin m, (((B i).card : ℝ) / (k : ℝ)) with hμ
    have hIndep : Work.Deep.Prob.FinProbSpace.IndepEvents P
        (fun i : Fin m => {ω : Fin m → Fin k | ω i ∈ B i}) :=
      uniformColouring_indep_cyl hkpos B
    have hprob : ∀ i : Fin m, P.prob {ω : Fin m → Fin k | ω i ∈ B i}
        = (((B i).card : ℝ) / (k : ℝ)) :=
      fun i => uniformColouring_prob_cyl hkpos i (B i)
    have hbound := Work.Deep.Prob.Chernoff.chernoff_upper (P := P)
      (A := fun i : Fin m => {ω : Fin m → Fin k | ω i ∈ B i}) hIndep
      (w := fun _ => (1 : ℝ)) (fun _ => zero_le_one) zero_le_one (fun _ => le_refl 1) ht
    have hevent : {ω : Fin m → Fin k | μ + t ≤
          ((Finset.univ.filter (fun i => ω i ∈ B i)).card : ℝ)}
        = {ω : Fin m → Fin k | t ≤ (∑ i, ({ω' : Fin m → Fin k | ω' i ∈ B i} :
            Set (Fin m → Fin k)).indicator (fun _ => (1 : ℝ)) ω)
            - ∑ i, P.prob ({ω' : Fin m → Fin k | ω' i ∈ B i}) * 1} := by
      ext ω
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, sum_indicator_eq_card_filter B ω]
      rw [Finset.sum_congr rfl (fun i _ => by rw [hprob i, mul_one])]
      constructor <;> intro h <;> linarith
    calc Work.Deep.Conc.prob {ω : Fin m → Fin k | μ + t ≤
            ((Finset.univ.filter (fun i => ω i ∈ B i)).card : ℝ)}
        = P.prob {ω : Fin m → Fin k | μ + t ≤
            ((Finset.univ.filter (fun i => ω i ∈ B i)).card : ℝ)} :=
          conc_prob_eq_uniformColouring hkpos _
      _ = P.prob {ω : Fin m → Fin k | t ≤ (∑ i, ({ω' : Fin m → Fin k | ω' i ∈ B i} :
            Set (Fin m → Fin k)).indicator (fun _ => (1 : ℝ)) ω)
            - ∑ i, P.prob ({ω' : Fin m → Fin k | ω' i ∈ B i}) * 1} := by rw [hevent]
      _ ≤ Real.exp (-(t^2) / (2 * 1 * (∑ i, P.prob ({ω' : Fin m → Fin k | ω' i ∈ B i}) * 1
            + t/3))) := hbound
      _ = Real.exp (-(t^2) / (2 * (μ + t/3))) := by
          congr 1
          rw [Finset.sum_congr rfl (fun i _ => by rw [hprob i, mul_one]), hμ, mul_one]

end Work.Deep.Kahn
