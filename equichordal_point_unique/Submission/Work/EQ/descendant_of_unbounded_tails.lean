import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.regComp_lift_over_annulus
import Submission.Work.EQ.regular_of_uncountable_junction
import Submission.Work.EQ.H0_junction_value_of_cluster
import Submission.Work.EQ.LaTB.la_fan_trichotomy_v2
import Submission.Work.EQ.LaTB.flattening_impossible
import Submission.Work.EQ.LaTB.flattening_impossible_bwd
import Submission.Work.EQ.tb_fan_run
import Submission.Work.EQ.charVal_main
import Submission.Work.EQ.walk_count
import Submission.Work.EQ.bwdP_fan_degenerate_countable
import Submission.Work.EQ.junction_nt_unbounded
import Submission.Work.EQ.junction_regular_of_uncountable
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.StableTailDefs
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.H0_tail_bounded

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/EQ/DESIGN_LA.md (the lead's closing route for exists_compact_regular_cycle's limit_analysis; the fan-rigidity chain and la_witness route are retired).

# descendant_of_unbounded_tails (3–5k; replaces href, ltbv_main's reflection, case_i_words_bounded and the LaTB fan-rigidity chain)

**Claim.** Let `S k` be regular components with values `c k → c₀`, and let `q k ∈ S k` be chains
over the annulus with unbounded tails. Then some regular component has a descendant value
`c₀μ₁μ₂`, with `(μ₁,μ₂) ≠ (1,1)` in `CharSet`.

**Route** (lead). Spread the chains over an uncountable annulus minus a countable exceptional set
(`regComp_lift_over_annulus`), transfer the unboundedness of the tails to the lifted chains, apply
the junction lemma `junction_nontrivial_of_unbounded_tails` (which produces an uncountable junction
set for `c₀μ₁μ₂` with `(μ₁,μ₂) ≠ (1,1)`), and finish with `regular_of_uncountable_junction`.
-/

namespace Work.EQ

open Filter _root_.Topology

noncomputable section


/-- **An open annulus minus a countable set is uncountable.** -/
theorem not_countable_annulus_diff_countable {r₁ r₂ : ℝ} (hr₁ : 0 < r₁) (hr : r₁ < r₂)
    {P : Set ℂ} (hP : P.Countable) :
    ¬ ({z : ℂ | r₁ < ‖z‖ ∧ ‖z‖ < r₂} \ P).Countable := by
  intro hc
  have hAnn : ({z : ℂ | r₁ < ‖z‖ ∧ ‖z‖ < r₂} : Set ℂ).Countable :=
    (hc.union hP).mono (by
      intro z hz
      by_cases hzP : z ∈ P
      · exact Or.inr hzP
      · exact Or.inl ⟨hz, hzP⟩)
  have hfinj : Function.Injective (fun t : ℝ => (t : ℂ)) := by
    intro x y hxy
    have := congrArg Complex.re hxy
    simpa using this
  have himg : (fun t : ℝ => (t : ℂ)) '' Set.Ioo r₁ r₂ ⊆
      ({z : ℂ | r₁ < ‖z‖ ∧ ‖z‖ < r₂} : Set ℂ) := by
    rintro z ⟨t, ht, rfl⟩
    have ht0 : 0 < t := lt_trans hr₁ ht.1
    simp only [Set.mem_setOf_eq, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    exact ht
  have hIoo : (Set.Ioo r₁ r₂).Countable := by
    have h1 : ((fun t : ℝ => (t : ℂ)) ⁻¹'
        ((fun t : ℝ => (t : ℂ)) '' Set.Ioo r₁ r₂)).Countable :=
      (hAnn.mono himg).preimage hfinj
    refine h1.mono ?_
    intro t ht
    exact ⟨t, ht, rfl⟩
  have hIooUnc : ¬ (Set.Ioo r₁ r₂).Countable := by
    intro h
    have h1 : Cardinal.mk (↥(Set.Ioo r₁ r₂)) ≤ Cardinal.aleph0 :=
      Cardinal.le_aleph0_iff_set_countable.mpr h
    rw [Cardinal.mk_Ioo_real hr] at h1
    exact absurd h1 (not_le.mpr Cardinal.aleph0_lt_continuum)
  exact hIooUnc hIoo

/-- The two principal-tail conditions at depth `M`, in the form used by the hypotheses of
`descendant_of_unbounded_tails`. -/
def BothTailsP (a : ℝ) (h : ℂ → ℂ) (q : ChainData) (M : ℕ) : Prop :=
  (∀ m : ℕ, M ≤ m → q.1 (m : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ m * q.2.1)) ∧
    (∀ m : ℕ, M ≤ m → q.1 (-(m : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ m * q.2.2))

/-- `BothTailsP` is `TailP` together with the explicit backward condition. -/
lemma bothTailsP_iff {a : ℝ} {h : ℂ → ℂ} {q : ChainData} {M : ℕ} :
    BothTailsP a h q M ↔ TailP a h q M ∧
      ∀ m : ℕ, M ≤ m → q.1 (-(m : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ m * q.2.2) := by
  unfold BothTailsP TailP
  constructor
  · intro hq
    exact ⟨fun m hm => by simpa using hq.1 m hm, hq.2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun m hm => by simpa using h1 m hm, h2⟩

/-- `BothTailsP` is monotone in the depth. -/
lemma bothTailsP_mono {a : ℝ} {h : ℂ → ℂ} {q : ChainData} {M M' : ℕ} (hM : M ≤ M')
    (hq : BothTailsP a h q M) : BothTailsP a h q M' :=
  ⟨fun m hm => hq.1 m (le_trans hM hm), fun m hm => hq.2 m (le_trans hM hm)⟩

/-- **Unbounded tails produce a descendant value (replaces the case-(ii) reflection `href`).**
Let `S k` be regular components with values `c k → c₀`, and let `q k ∈ S k` be chains over the
annulus whose tails are not uniformly principal from any depth. Then for some characteristic
values `(μ₁, μ₂) ≠ (1, 1)`, some regular component has the descendant value `c₀ μ₁ μ₂`. -/
theorem descendant_of_unbounded_tails {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (r₁ r₂ : ℝ), 0 < r₁ → r₁ < r₂ → r₂ < δ → 1 / eqLam a < r₂ / r₁ →
      ∀ (S : ℕ → Set ChainData) (c : ℕ → ℂ) (c₀ : ℂ) (q : ℕ → ChainData),
        (∀ k, IsRegComp a h (S k) (c k)) → Tendsto c atTop (𝓝 c₀) →
        (∀ k, q k ∈ S k ∧ (q k).2.1 ∈ Ann r₁ r₂) →
        (∀ M : ℕ, ∃ k, ¬ ((∀ m : ℕ, M ≤ m → (q k).1 (m : ℤ) =
              germC a h (((eqLam a : ℝ) : ℂ) ^ m * (q k).2.1)) ∧
            (∀ m : ℕ, M ≤ m → (q k).1 (-(m : ℤ)) =
              ugermC a h (((eqLam a : ℝ) : ℂ) ^ m * (q k).2.2)))) →
        ∃ μ₁ ∈ CharSet a h, ∃ μ₂ ∈ CharSet a h, (μ₁ ≠ 1 ∨ μ₂ ≠ 1) ∧
          ∃ T : Set ChainData, IsRegComp a h T (c₀ * μ₁ * μ₂) := by
  obtain ⟨δA, hδApos, hA⟩ := junction_nt_unbounded ha0 ha1 hh
  obtain ⟨δR, hδRpos, hR⟩ := junction_regular_of_uncountable ha0 ha1 hh
  obtain ⟨P, hPcount, hlift⟩ := regComp_lift_over_annulus ha0 ha1 hh
  obtain ⟨ρ, hρ0, hρge⟩ := H0_invParam_ge ha0 ha1 hh
  refine ⟨min δA δR / 2, by positivity, ?_⟩
  intro r₁ r₂ hr₁ hr₁₂ hr₂ hratio S c c₀ q hS hlim hq hbad
  -- ## the limit value is nonzero (Rychlik Lemma 17)
  have hc₀ : c₀ ≠ 0 := by
    intro h0
    have hle : ∀ k, ρ ≤ ‖c k‖ := by
      intro k
      have h := hρge (q k) ((hS k).1 (hq k).1)
      rw [(hS k).2.2 (q k) (hq k).1] at h
      exact h
    have h2 : ρ ≤ ‖c₀‖ := ge_of_tendsto' hlim.norm hle
    rw [h0, norm_zero] at h2
    linarith
  -- ## a uniform bound on the values
  obtain ⟨B, hBpos, hB⟩ : ∃ B : ℝ, 0 < B ∧ ∀ k, ‖c k‖ ≤ B := by
    obtain ⟨K, hK⟩ := eventually_atTop.mp
      (hlim.norm.eventually (eventually_lt_nhds (lt_add_one ‖c₀‖)))
    refine ⟨max (‖c₀‖ + 1)
        ((Finset.range (K + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.succ_pos K)⟩
          fun i => ‖c i‖),
      lt_of_lt_of_le (by positivity : (0 : ℝ) < ‖c₀‖ + 1) (le_max_left _ _), fun k => ?_⟩
    by_cases hk : k < K
    · exact le_trans (Finset.le_sup' (fun i => ‖c i‖)
        (Finset.mem_range.mpr (Nat.lt_succ_of_lt hk))) (le_max_right _ _)
    · exact le_trans (le_of_lt (hK k (by omega))) (le_max_left _ _)
  -- ## the scale of the cluster
  set δ : ℝ := min δA δR / 2 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδleA : δ ≤ δA := by
    rw [hδdef]; have h1 : min δA δR ≤ δA := min_le_left _ _; linarith
  have hδleR : δ ≤ δR := by
    rw [hδdef]; have h1 : min δA δR ≤ δR := min_le_right _ _; linarith
  set r₁' : ℝ := r₁ / 2 with hr₁'def
  set r₂' : ℝ := (r₂ + δ) / 2 with hr₂'def
  have hr₁'pos : 0 < r₁' := by rw [hr₁'def]; linarith
  have hr₁'r₂' : r₁' < r₂' := by rw [hr₁'def, hr₂'def]; linarith
  have hr₂'δ : r₂' < δ := by rw [hr₂'def]; linarith
  -- ## the failure sets are infinite, giving a reindexing with failures at every depth
  have hBadInf : ∀ M : ℕ, ({k : ℕ | ¬ BothTailsP a h (q k) M}).Infinite := by
    intro M
    by_contra hfin
    rw [Set.not_infinite] at hfin
    -- the finite set of failing chains has a bounded maximal depth
    obtain ⟨m, hm⟩ : ∃ m : ℕ, ∀ k ∈ ({k : ℕ | ¬ BothTailsP a h (q k) M}),
        max (tailIdx a h (q k)) (tailIdx a h (mirrorChain (q k))) ≤ m := by
      have hne : ({k : ℕ | ¬ BothTailsP a h (q k) M} : Set ℕ).Nonempty := by
        obtain ⟨k, hk⟩ := hbad M
        exact ⟨k, hk⟩
      refine ⟨hfin.toFinset.sup' (hfin.toFinset_nonempty.mpr hne) (fun k =>
        max (tailIdx a h (q k)) (tailIdx a h (mirrorChain (q k)))), fun k hk => ?_⟩
      exact Finset.le_sup' (fun k => max (tailIdx a h (q k))
        (tailIdx a h (mirrorChain (q k)))) ((hfin.mem_toFinset).mpr hk)
    -- but the hypothesis supplies a failing chain at the deeper level `max M m + 1`
    obtain ⟨k, hk⟩ := hbad (max M m + 1)
    have hkM : ¬ BothTailsP a h (q k) M := fun hc =>
      hk (bothTailsP_mono (le_trans (le_max_left M m) (Nat.le_succ _)) hc)
    have hkbound := hm k hkM
    -- a chain failing at depth `M` has a tail index larger than `max M m + 1`
    have hchain : IsChain a h (q k) := isChain_of_mem_H0 ((hS k).1 (hq k).1)
    have hbwd : TailP a h (mirrorChain (q k)) (max M m + 1) ↔
        ∀ j : ℕ, max M m + 1 ≤ j → (q k).1 (-(j : ℤ)) =
          ugermC a h (((eqLam a : ℝ) : ℂ) ^ j * (q k).2.2) := by
      constructor
      · intro h j hj
        have h1 := h j hj
        rw [mirrorChain_fst, mirrorChain_psi1] at h1
        have h2 := congrArg eqMirror h1
        simpa [ugermC, eqMirror] using h2
      · intro h j hj
        have h1 := h j hj
        have h2 := congrArg eqMirror h1
        rw [mirrorChain_fst, mirrorChain_psi1]
        simpa [ugermC, eqMirror] using h2
    have hstep : max (tailIdx a h (q k)) (tailIdx a h (mirrorChain (q k))) >
        max M m + 1 := by
      have hdisj : ¬ TailP a h (q k) (max M m + 1) ∨
          ¬ (∀ j : ℕ, max M m + 1 ≤ j → (q k).1 (-(j : ℤ)) =
            ugermC a h (((eqLam a : ℝ) : ℂ) ^ j * (q k).2.2)) := by
        by_contra hc
        rw [not_or, not_not, not_not] at hc
        exact hk (bothTailsP_iff.mpr ⟨hc.1, hc.2⟩)
      rcases hdisj with hk | hk
      · have hlt : max M m + 1 < tailIdx a h (q k) :=
          not_le.mp fun hle => hk ((tailIdx_le_iff (tailP_of_isChain hchain)).mp hle)
        exact lt_of_lt_of_le hlt (le_max_left _ _)
      · have hlt : max M m + 1 < tailIdx a h (mirrorChain (q k)) :=
          not_le.mp fun hle => hk (hbwd.mp ((tailIdx_le_iff (tailP_of_isChain
            (isChain_mirrorChain hchain))).mp hle))
        exact lt_of_lt_of_le hlt (le_max_right _ _)
    omega
  choose κ hκmem hκlt using fun M : ℕ => (hBadInf M).exists_gt M
  -- ## the reindexed data
  set S' : ℕ → Set ChainData := fun M => S (κ M) with hS'def
  set c' : ℕ → ℂ := fun M => c (κ M) with hc'def
  set q' : ℕ → ChainData := fun M => q (κ M) with hq'def
  have hS' : ∀ M, IsRegComp a h (S' M) (c' M) := fun M => hS (κ M)
  have hq' : ∀ M, q' M ∈ S' M ∧ (q' M).2.1 ∈ Ann r₁ r₂ := fun M => hq (κ M)
  have hκtop : Tendsto κ atTop atTop := Filter.tendsto_atTop_atTop.mpr fun n =>
    ⟨n, fun m hm => le_of_lt (lt_of_le_of_lt hm (hκlt m))⟩
  have hlim' : Tendsto c' atTop (𝓝 c₀) := hlim.comp hκtop
  have hB' : ∀ M, ‖c' M‖ ≤ B := fun M => hB (κ M)
  have hbad' : ∀ M, ¬ BothTailsP a h (q' M) M := fun M => hκmem M
  -- ## lift the chains to every parameter of the enlarged annulus
  have hq'in : ∀ M, r₁' < ‖(q' M).2.1‖ ∧ ‖(q' M).2.1‖ < r₂' := by
    intro M
    obtain ⟨h1, h2⟩ := (hq' M).2
    exact ⟨by rw [hr₁'def]; linarith, by rw [hr₂'def]; linarith⟩
  obtain ⟨n₀, hn₀⟩ := hlift (r₁ := r₁') (r₂ := r₂') (B := B) hr₁'pos hr₁'r₂'
  have hliftOne : ∀ z ∈ ({z : ℂ | r₁' < ‖z‖ ∧ ‖z‖ < r₂'} \ P), ∀ M : ℕ,
      ∃ q'' ∈ S' M, q''.2.1 = z ∧
        (∀ n : ℕ, n₀ ≤ n → (TailP a h (q' M) n ↔ TailP a h q'' n) ∧
          ((∀ m : ℕ, n ≤ m → (q' M).1 (-(m : ℤ)) =
              ugermC a h (((eqLam a : ℝ) : ℂ) ^ m * (q' M).2.2)) ↔
            (∀ m : ℕ, n ≤ m → q''.1 (-(m : ℤ)) =
              ugermC a h (((eqLam a : ℝ) : ℂ) ^ m * q''.2.2)))) := by
    intro z hz M
    obtain ⟨q'', hq''mem, hq''psi, htail⟩ :=
      hn₀ (hS' M) (hB' M) (q' M) (hq' M).1 (hq'in M).1 (hq'in M).2
        z (hz.1.1) (hz.1.2) (hz.2)
    exact ⟨q'', hq''mem, hq''psi, htail⟩
  classical
  set Z : Set ℂ := ({z : ℂ | r₁' < ‖z‖ ∧ ‖z‖ < r₂'} \ P) with hZdef
  let X : ℂ → ℕ → ChainData := fun z M =>
    if hz : z ∈ Z then (hliftOne z hz M).choose else q' M
  have hXspec : ∀ z ∈ Z, ∀ M, X z M ∈ S' M ∧ (X z M).2.1 = z ∧
      (∀ n : ℕ, n₀ ≤ n → (TailP a h (q' M) n ↔ TailP a h (X z M) n) ∧
        ((∀ m : ℕ, n ≤ m → (q' M).1 (-(m : ℤ)) =
            ugermC a h (((eqLam a : ℝ) : ℂ) ^ m * (q' M).2.2)) ↔
          (∀ m : ℕ, n ≤ m → (X z M).1 (-(m : ℤ)) =
            ugermC a h (((eqLam a : ℝ) : ℂ) ^ m * (X z M).2.2)))) := by
    intro z hz M
    have h := (hliftOne z hz M).choose_spec
    simpa only [X, dif_pos hz] using h
  have hZunc : ¬ Z.Countable := by
    rw [hZdef]
    exact not_countable_annulus_diff_countable hr₁'pos hr₁'r₂' hPcount
  -- ## the unboundedness transfers to the lifted chains
  have hbadX : ∀ z ∈ Z, ∀ B' : ℕ, ∃ k : ℕ, ¬ (TailP a h (X z k) B' ∧
      ∀ m : ℕ, B' ≤ m → (X z k).1 (-(m : ℤ)) =
        ugermC a h (((eqLam a : ℝ) : ℂ) ^ m * (X z k).2.2)) := by
    intro z hz B'
    obtain ⟨-, hpsi, htail⟩ := hXspec z hz (max B' n₀)
    obtain ⟨heq1, heq2⟩ := htail (max B' n₀) (le_max_right B' n₀)
    -- the source chain fails at the deeper level `max B' n₀`
    have hfail : ¬ BothTailsP a h (q' (max B' n₀)) (max B' n₀) := hbad' _
    refine ⟨max B' n₀, fun hcon => hfail ?_⟩
    rw [bothTailsP_iff]
    refine ⟨heq1.mpr (TailP_mono hcon.1 (le_max_left B' n₀)), fun m hm => ?_⟩
    exact heq2.mpr (fun m hm' => hcon.2 m (le_trans (le_max_left B' n₀) hm')) m hm
  -- ## the junction lemma
  obtain ⟨N, ε, η, s, μ₁, μ₂, hεlen, hηlen, hslen, hμ₁, hμ₂, hne, hprod, hcountδ⟩ :=
    hA hδpos hδleA hr₁'pos hr₁'r₂' hr₂'δ hc₀ hZunc
      (fun z hz => ⟨le_of_lt hz.1.1, le_of_lt hz.1.2⟩)
      (fun z hz k => (hS' k).1 (hXspec z hz k).1)
      (fun z hz => by
        have h := (hXspec z hz)
        exact tendsto_const_nhds.congr' (Eventually.of_forall (fun k => ((h k).2.1).symm)))
      (fun z hz => by
        refine hlim'.congr' (Eventually.of_forall (fun k => ?_))
        obtain ⟨hmem, hpsi, -⟩ := hXspec z hz k
        exact ((hS' k).2.2 (X z k) hmem).symm)
      hbadX
  -- ## conclude with the regular component of the descendant value
  have hCne : μ₁ * μ₂ * c₀ ≠ 0 := mul_ne_zero hprod hc₀
  have hcountR : ¬ {w : ℂ | w ≠ 0 ∧ ‖w‖ < δR ∧
      ‖((eqLam a : ℝ) : ℂ) ^ N * ((μ₁ * μ₂ * c₀) / w)‖ < δR ∧
      bwdP a s (fan a h ε w) =
        eqMirror (fan a h η (((eqLam a : ℝ) : ℂ) ^ N * ((μ₁ * μ₂ * c₀) / w)))}.Countable := by
    intro hc
    refine hcountδ (hc.mono ?_)
    rintro w ⟨hw0, hwδ, hwfar, hwj⟩
    exact ⟨hw0, lt_of_lt_of_le hwδ hδleR, lt_of_lt_of_le hwfar hδleR, hwj⟩
  obtain ⟨T, hT⟩ := hR N ε η s (μ₁ * μ₂ * c₀) hεlen hslen hCne hcountR
  exact ⟨μ₁, hμ₁, μ₂, hμ₂, hne, T, by
    rw [show μ₁ * μ₂ * c₀ = c₀ * μ₁ * μ₂ by ring] at hT; exact hT⟩

end

end Work.EQ
