import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.StableTailDefs
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.HeteroAlgebra
import Submission.Work.EQ.fan_estimates
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.Analysis.Complex.punctured_ball_connected

namespace Work.EQ

open Filter _root_.Topology
open Complex
open Classical

noncomputable section

section

variable {a : ℝ} {h : ℂ → ℂ}

/-! ## Auxiliary facts -/

/-- **Every point of a chain of `H0` is a fan value** at the chain's own `ψ₁`-parameter scaled by
`λⁿ`. -/
theorem fan_slice_mem_H0 (ha0 : 0 < a) (ha1 : a < 1) {q : ChainData}
    (hq : q ∈ H0 a h) (n : ℤ) :
    ∃ ε : List Bool, q.1 n = fan a h ε ((eqLam a : ℂ) ^ n * q.2.1) := by
  have hchain : IsChain a h q := isChain_of_mem_H0 hq
  have hchain' : IsChain a h (shiftZ a n q) := isChain_shiftZ ha0 ha1 hchain n
  obtain ⟨ε, hε⟩ := chain_eq_fan' ha0 ha1 hchain'
  refine ⟨ε, ?_⟩
  have h0 : (shiftZ a n q).1 0 = q.1 n := by
    rw [shiftZ_fst]; norm_num
  rw [← h0, hε, shiftZ_psi1]

/-- **The backward radicand of a fan value lies in the slit plane.**  There is a radius `δ > 0`
such that for every branch word `ε` and every `‖v‖ < δ` the number
`((fan a h ε v).1 + a/2)^2 + (fan a h ε v).2^2` is in the slit plane. -/
theorem fan_slitPlane (ha0 : 0 < a) (ha1 : a < 1) {r : ℝ} (hh : IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (ε : List Bool) (v : ℂ), ‖v‖ < δ →
      ((fan a h ε v).1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + (fan a h ε v).2 ^ 2 ∈ Complex.slitPlane := by
  obtain ⟨Ke, Lam, Q, δf, hKe, hLam, hQ, hδf, hFan⟩ := fan_induction ha0 ha1 hh
  refine ⟨δf, hδf, fun ε v hv => ?_⟩
  have hg := hFan ε v (by rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hv)
  have hre : 0 < (((fan a h ε v).1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + (fan a h ε v).2 ^ 2).re := by
    convert hg.2.2.2.2 using 2
    push_cast
    ring
  exact Complex.mem_slitPlane_iff.mpr (Or.inl hre)

/-- **The two backward branches at a point in the slit plane are distinct.** -/
theorem invBranch_true_ne_false_of_slit {Q : ℂ × ℂ}
    (h : ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ∈ Complex.slitPlane) :
    invBranch a true Q ≠ invBranch a false Q := by
  intro hcon
  have hne : ((Q.1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + Q.2 ^ 2) ≠ 0 := Complex.slitPlane_ne_zero h
  have hne' : bsq (subO1 a Q) ≠ 0 := by simpa only [subO1, bsq] using hne
  set X : ℂ × ℂ := (brho (subO1 a Q))⁻¹ • subO1 a Q with hXdef
  have h1 : invBranch a false Q + Q = -X := by
    have hh := invBranch_add a false Q
    rw [hXdef]; simpa using hh
  have h2 : invBranch a true Q + Q = X := by
    have hh := invBranch_add a true Q
    rw [hXdef]; simpa using hh
  have h3 : X = -X := by
    calc X = invBranch a true Q + Q := h2.symm
      _ = invBranch a false Q + Q := by rw [hcon]
      _ = -X := h1
  have h2X : (2 : ℂ) • X = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h3]
    abel
  have hX0 : X = 0 := (smul_eq_zero.mp h2X).resolve_left (by norm_num)
  have hbr : (brho (subO1 a Q))⁻¹ ≠ 0 := inv_ne_zero (brho_ne_zero hne')
  have hsub : subO1 a Q = 0 := by
    rcases smul_eq_zero.mp (show (brho (subO1 a Q))⁻¹ • subO1 a Q = 0 from by rw [← hXdef]; exact hX0)
      with h' | h'
    · exact absurd h' hbr
    · exact h'
  exact hne' (by rw [hsub]; simp [bsq])

/-- **The branch label of a step is constant on a preconnected parameter set.** -/
theorem label_dichotomy {D : Set ℂ} {P Q : ℂ → ℂ × ℂ} (hD : IsPreconnected D)
    (hP : ContinuousOn P D) (hQ : ContinuousOn Q D)
    (hrel : ∀ ζ ∈ D, EqRelC a (P ζ) (Q ζ))
    (hslit : ∀ ζ ∈ D, ((Q ζ).1 + ((a / 2 : ℝ) : ℂ)) ^ 2 + (Q ζ).2 ^ 2 ∈ Complex.slitPlane) :
    (∀ ζ ∈ D, P ζ = invBranch a true (Q ζ)) ∨ (∀ ζ ∈ D, P ζ = invBranch a false (Q ζ)) := by
  haveI : PreconnectedSpace D := Subtype.preconnectedSpace hD
  have hPc : Continuous (fun ζ : D => P (ζ : ℂ)) := hP.domRestrict
  have hQc : Continuous (fun ζ : D => Q (ζ : ℂ)) := hQ.domRestrict
  have hgc : ∀ s : Bool, Continuous (fun ζ : D => invBranch a s (Q (ζ : ℂ))) := by
    intro s
    refine continuous_iff_continuousAt.mpr fun ζ => ?_
    have hinner : ContinuousAt (fun x : D => Q (x : ℂ)) ζ := hQc.continuousAt
    have hout : ContinuousAt (invBranch a s) ((fun x : D => Q (x : ℂ)) ζ) :=
      (analyticAt_invBranch (a := a) (s := s) (hslit (ζ : ℂ) ζ.2)).continuousAt
    exact hout.comp (f := fun x : D => Q (x : ℂ)) (x := ζ) hinner
  set A : Set D := {ζ | P (ζ : ℂ) = invBranch a true (Q (ζ : ℂ))} with hAdef
  set B : Set D := {ζ | P (ζ : ℂ) = invBranch a false (Q (ζ : ℂ))} with hBdef
  have hAcl : IsClosed A := isClosed_eq hPc (hgc true)
  have hBcl : IsClosed B := isClosed_eq hPc (hgc false)
  have hsub : (Set.univ : Set D) ⊆ A ∪ B := by
    intro ζ _
    have hne := Complex.slitPlane_ne_zero (hslit (ζ : ℂ) ζ.2)
    have hne' : bsq (subO1 a (Q (ζ : ℂ))) ≠ 0 := by simpa only [subO1, bsq] using hne
    rcases eqRelC_solutions (hrel (ζ : ℂ) ζ.2) hne' with hh | hh
    · exact Or.inl hh
    · exact Or.inr hh
  have hdisj : (Set.univ : Set D) ∩ (A ∩ B) = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.mpr fun ζ hz => ?_
    obtain ⟨-, hzA, hzB⟩ := hz
    exact invBranch_true_ne_false_of_slit (hslit (ζ : ℂ) ζ.2) (hzA.symm.trans hzB)
  rcases (isPreconnected_iff_subset_of_disjoint_closed.mp
      (isPreconnected_univ : IsPreconnected (Set.univ : Set D)) A B hAcl hBcl hsub hdisj)
    with hh | hh
  · left; intro ζ hζ; exact hh (Set.mem_univ (⟨ζ, hζ⟩ : D))
  · right; intro ζ hζ; exact hh (Set.mem_univ (⟨ζ, hζ⟩ : D))

/-- **True labels above an index force the principal tail.** -/
theorem TailP_of_invBranch_true_ge (ha0 : 0 < a) (ha1 : a < 1) {q : ChainData}
    (hq : IsChain a h q) {B ρ : ℝ} (hB0 : 0 ≤ B) (hB : ‖q.2.1‖ ≤ B)
    (hgerm : ∀ u ∈ Metric.ball (0 : ℂ) ρ,
      invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u)
    {M : ℕ} (hM : (eqLam a) ^ M * B < ρ)
    (htrue : ∀ m : ℕ, M ≤ m → q.1 (m : ℤ) = invBranch a true (q.1 ((m : ℤ) + 1))) :
    TailP a h q M := by
  have hl0 : (0 : ℝ) < eqLam a := eqLam_pos' ha0 ha1
  have hl1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hTail := TailP_of_isChain hq
  intro n hn
  obtain ⟨N, hN⟩ : ∃ N : ℕ, max n (tailIdx a h q) ≤ N := ⟨_, le_refl _⟩
  have hNn : n ≤ N := le_trans (le_max_left _ _) hN
  have hNtail : q.1 (N : ℤ) = germC a h ((eqLam a : ℂ) ^ N * q.2.1) :=
    hTail N (le_trans (le_max_right _ _) hN)
  have step : ∀ k : ℕ, k ≤ N - n → q.1 ((N - k : ℕ) : ℤ) =
      germC a h ((eqLam a : ℂ) ^ (N - k) * q.2.1) := by
    intro k
    induction k with
    | zero => intro _; simpa using hNtail
    | succ k ih =>
      intro hk
      have hk' : k ≤ N - n := by omega
      have h1 := ih hk'
      have hm : M ≤ N - (k + 1) := le_trans hn (by omega)
      have htrue' := htrue (N - (k + 1)) hm
      have hidx : (((N - (k + 1) : ℕ)) : ℤ) + 1 = ((N - k : ℕ) : ℤ) := by omega
      rw [hidx, h1] at htrue'
      have harg : (eqLam a : ℂ) ^ (N - (k + 1)) * q.2.1 ∈ Metric.ball (0 : ℂ) ρ := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        have h1' : ‖(eqLam a : ℂ) ^ (N - (k + 1)) * q.2.1‖
            = (eqLam a) ^ (N - (k + 1)) * ‖q.2.1‖ := by
          rw [norm_mul, norm_pow, Complex.norm_of_nonneg (le_of_lt hl0)]
        rw [h1']
        have hpow : (eqLam a) ^ (N - (k + 1)) ≤ (eqLam a) ^ M :=
          pow_le_pow_of_le_one (le_of_lt hl0) (le_of_lt hl1) (by omega)
        calc (eqLam a) ^ (N - (k + 1)) * ‖q.2.1‖
            ≤ (eqLam a) ^ M * B :=
              mul_le_mul hpow hB (norm_nonneg _) (pow_nonneg (le_of_lt hl0) _)
          _ < ρ := hM
      have hid := hgerm ((eqLam a : ℂ) ^ (N - (k + 1)) * q.2.1) harg
      have hpow : (eqLam a : ℂ) * ((eqLam a : ℂ) ^ (N - (k + 1)) * q.2.1)
          = (eqLam a : ℂ) ^ (N - k) * q.2.1 := by
        rw [show N - k = N - (k + 1) + 1 by omega, pow_succ]
        ring
      rw [hpow] at hid
      rw [htrue', hid]
  have hfin := step (N - n) (by omega)
  rw [show N - (N - n) = n by omega] at hfin
  exact hfin

end

/-! ## The main theorem -/

/-- **The tail index is bounded near a puncture of `H0`.**  Along a punctured chart
(`IsPuncturedChart`: a family of chains of `H0` with `ψ₁ (e ζ) = u₀ + κ ζᵏ`, `u₀ ≠ 0`, `κ ≠ 0`,
all chain coordinates meromorphic at `0`), the forward tail of every chain of the chart is the
principal leaf from a *uniform* index on.

The requester's hint is formalised here with one correction: the "the two branch values are
continuous in `ζ`" step is *false* across the branch cut of the principal square root (the label
flips there, see `H0_path_limit`).  What replaces it is the Rychlik fan estimate
`Work.EQ.fan_induction`: below a uniform index the point `P_{m+1} ζ` is a fan value with small
parameter, so its backward radicand lies in the slit plane (`fan_slitPlane`); the branch values are
then continuous in `ζ` and `label_dichotomy` gives a `ζ`-independent label sequence above that
index.  The label at the reference parameter `ζ = 1/2` is eventually `true` (`TailP` of the chain),
so from some index on all labels are `true` for *every* `ζ`, and the descent
`TailP_of_invBranch_true_ge` finishes. -/
theorem tailP_bdd_near_puncture {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {e : ℂ → ChainData} {u₀ : ℂ} {k : ℕ}
    (he : IsPuncturedChart a h e u₀ k) :
    ∃ (δ : ℝ) (M : ℕ), 0 < δ ∧ ∀ ζ : ℂ, 0 < ‖ζ‖ → ‖ζ‖ < δ → TailP a h (e ζ) M := by
  obtain ⟨hk0, hu0, κ, hκ, hchart, hinj, hcont, hmer2, hmer1⟩ := he
  obtain ⟨δf, hδf, hslitFan⟩ := fan_slitPlane (h := h) ha0 ha1 hh
  obtain ⟨ρ, hρ, hgermAn, hgerm0, hgermPr, hinjY, hderivY⟩ := germC_facts (h := h) ha0 ha1 hh
  have hl0 : (0 : ℝ) < eqLam a := eqLam_pos' ha0 ha1
  have hl1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hlC : ((eqLam a : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hl0)
  set B : ℝ := ‖u₀‖ + ‖κ‖ + 1 with hBdef
  have hBpos : 0 < B := by rw [hBdef]; positivity
  set D : Set ℂ := Metric.ball (0 : ℂ) 1 \ {0} with hDdef
  -- `ψ₁` is bounded on the chart
  have hpsiB : ∀ ζ ∈ D, ‖(e ζ).2.1‖ ≤ B := by
    intro ζ hζ
    have hz : ‖ζ‖ < 1 := by
      have h := hζ.1
      rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at h
    rw [(hchart ζ hζ).2]
    calc ‖u₀ + κ * ζ ^ k‖ ≤ ‖u₀‖ + ‖κ * ζ ^ k‖ := norm_add_le _ _
      _ = ‖u₀‖ + ‖κ‖ * ‖ζ‖ ^ k := by rw [norm_mul, norm_pow]
      _ ≤ ‖u₀‖ + ‖κ‖ * 1 := by
          have hk1 : ‖ζ‖ ^ k ≤ 1 := pow_le_one₀ (norm_nonneg _) (le_of_lt hz)
          nlinarith [norm_nonneg κ]
      _ ≤ B := by rw [hBdef]; linarith
  -- an index beyond which the parameters are in both discs
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, (eqLam a) ^ n * B < min δf ρ := by
    have hmin : 0 < min δf ρ := lt_min hδf hρ
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hmin hBpos) hl1
    refine ⟨n, ?_⟩
    have h2 : (eqLam a) ^ n * B < (min δf ρ / B) * B := mul_lt_mul_of_pos_right hn hBpos
    rwa [div_mul_cancel₀ _ (ne_of_gt hBpos)] at h2
  have hn₁δ : ∀ m : ℕ, n₁ ≤ m → (eqLam a) ^ m * B < δf := by
    intro m hm
    have h1 : (eqLam a) ^ m ≤ (eqLam a) ^ n₁ :=
      pow_le_pow_of_le_one (le_of_lt hl0) (le_of_lt hl1) hm
    have h2 : (eqLam a) ^ m * B ≤ (eqLam a) ^ n₁ * B := mul_le_mul_of_nonneg_right h1 hBpos.le
    exact lt_of_le_of_lt h2 (lt_of_lt_of_le hn₁ (min_le_left _ _))
  have hn₁ρ : ∀ m : ℕ, n₁ ≤ m → (eqLam a) ^ m * B < ρ := by
    intro m hm
    have h1 : (eqLam a) ^ m ≤ (eqLam a) ^ n₁ :=
      pow_le_pow_of_le_one (le_of_lt hl0) (le_of_lt hl1) hm
    have h2 : (eqLam a) ^ m * B ≤ (eqLam a) ^ n₁ * B := mul_le_mul_of_nonneg_right h1 hBpos.le
    exact lt_of_le_of_lt h2 (lt_of_lt_of_le hn₁ (min_le_right _ _))
  -- the punctured disc is preconnected
  have hDpre : IsPreconnected D := by
    have hball : IsConnected (Metric.ball (0 : ℂ) 1) := Metric.isConnected_ball zero_lt_one
    have h0 : (0 : ℂ) ∈ interior (Metric.ball (0 : ℂ) 1) := by
      rw [Metric.isOpen_ball.interior_eq]; simpa using zero_lt_one
    have hc := Work.Analysis.Complex.isConnected_diff_singleton_of_mem_interior hball h0
    rw [hDdef]; exact hc.2
  -- the coordinates are continuous
  have hcoord : ∀ n : ℤ, ContinuousOn (fun ζ : ℂ => (e ζ).1 n) D := fun n =>
    ((continuous_apply n).comp continuous_fst).comp_continuousOn hcont
  -- the backward radicand of every point above the threshold is in the slit plane
  have hslit : ∀ ζ ∈ D, ∀ m : ℕ, n₁ ≤ m →
      (((e ζ).1 ((m : ℤ) + 1)).1 + ((a / 2 : ℝ) : ℂ)) ^ 2
        + ((e ζ).1 ((m : ℤ) + 1)).2 ^ 2 ∈ Complex.slitPlane := by
    intro ζ hζ m hm
    obtain ⟨ε, hε⟩ := fan_slice_mem_H0 (h := h) ha0 ha1 (hchart ζ hζ).1 ((m : ℤ) + 1)
    have hv : ‖((eqLam a : ℂ) ^ ((m : ℤ) + 1) * (e ζ).2.1)‖ < δf := by
      rw [show ((m : ℤ) + 1) = (((m + 1 : ℕ)) : ℤ) by omega, zpow_natCast]
      have h1 : ‖(eqLam a : ℂ) ^ (m + 1) * (e ζ).2.1‖ = (eqLam a) ^ (m + 1) * ‖(e ζ).2.1‖ := by
        rw [norm_mul, norm_pow, Complex.norm_of_nonneg (le_of_lt hl0)]
      rw [h1]
      exact lt_of_le_of_lt
        (mul_le_mul_of_nonneg_left (hpsiB ζ hζ) (pow_nonneg (le_of_lt hl0) _))
        (hn₁δ (m + 1) (by omega))
    rw [hε]
    exact hslitFan ε _ hv
  -- the relation between consecutive points
  have hrel : ∀ ζ ∈ D, ∀ m : ℕ, EqRelC a ((e ζ).1 (m : ℤ)) ((e ζ).1 ((m : ℤ) + 1)) := by
    intro ζ hζ m
    exact (isChain_of_mem_H0 (hchart ζ hζ).1).1 (m : ℤ) |>.1
  -- the label sequence above the threshold is independent of `ζ`
  have hdich : ∀ m : ℕ, n₁ ≤ m →
      (∀ ζ ∈ D, (e ζ).1 (m : ℤ) = invBranch a true ((e ζ).1 ((m : ℤ) + 1))) ∨
      (∀ ζ ∈ D, (e ζ).1 (m : ℤ) = invBranch a false ((e ζ).1 ((m : ℤ) + 1))) := by
    intro m hm
    exact label_dichotomy hDpre (hcoord _) (hcoord _) (fun ζ hζ => hrel ζ hζ m)
      (fun ζ hζ => hslit ζ hζ m hm)
  -- the reference chain
  have hζ0 : (1 / 2 : ℂ) ∈ D := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, sub_zero]; norm_num
    · simp
  have hq0 : IsChain a h (e (1 / 2)) := isChain_of_mem_H0 (hchart (1 / 2) hζ0).1
  have hTail0 : TailP a h (e (1 / 2)) (tailIdx a h (e (1 / 2))) := TailP_of_isChain hq0
  -- the uniform index
  refine ⟨1, max (tailIdx a h (e (1 / 2)) + 1) (n₁ + 1), one_pos, ?_⟩
  intro ζ hζpos hζlt
  have hζD : ζ ∈ D := by
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, sub_zero]; exact hζlt
    · simpa using hζpos
  set M : ℕ := max (tailIdx a h (e (1 / 2)) + 1) (n₁ + 1) with hMdef
  have htrue : ∀ m : ℕ, M ≤ m → (e ζ).1 (m : ℤ) = invBranch a true ((e ζ).1 ((m : ℤ) + 1)) := by
    intro m hm
    have hm₁ : n₁ ≤ m := le_trans (le_trans (Nat.le_succ n₁) (le_max_right _ _)) hm
    rcases hdich m hm₁ with htrue | hfalse
    · exact htrue ζ hζD
    · exfalso
      -- at the reference point the label is true
      have hmN : tailIdx a h (e (1 / 2)) ≤ m :=
        le_trans (Nat.le_succ _) (le_trans (le_max_left _ _) hm)
      have h1 : (e (1 / 2)).1 (m : ℤ) =
          germC a h ((eqLam a : ℂ) ^ m * (e (1 / 2)).2.1) := hTail0 m hmN
      have h2 : (e (1 / 2)).1 ((m : ℤ) + 1) =
          germC a h ((eqLam a : ℂ) ^ (m + 1) * (e (1 / 2)).2.1) := by
        have h3 := hTail0 (m + 1) (by omega)
        rwa [show (((m + 1 : ℕ)) : ℤ) = (m : ℤ) + 1 by omega] at h3
      have harg : (eqLam a : ℂ) ^ m * (e (1 / 2)).2.1 ∈ Metric.ball (0 : ℂ) ρ := by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        have h1' : ‖(eqLam a : ℂ) ^ m * (e (1 / 2)).2.1‖
            = (eqLam a) ^ m * ‖(e (1 / 2)).2.1‖ := by
          rw [norm_mul, norm_pow, Complex.norm_of_nonneg (le_of_lt hl0)]
        rw [h1']
        exact lt_of_le_of_lt
          (mul_le_mul_of_nonneg_left (hpsiB (1 / 2) hζ0) (pow_nonneg (le_of_lt hl0) _))
          (hn₁ρ m hm₁)
      have h3 : (e (1 / 2)).1 (m : ℤ) =
          invBranch a true ((e (1 / 2)).1 ((m : ℤ) + 1)) := by
        rw [h1, h2]
        have h4 := (hgermPr ((eqLam a : ℂ) ^ m * (e (1 / 2)).2.1) harg).2
        have hpow : (eqLam a : ℂ) * ((eqLam a : ℂ) ^ m * (e (1 / 2)).2.1)
            = (eqLam a : ℂ) ^ (m + 1) * (e (1 / 2)).2.1 := by
          rw [pow_succ]; ring
        rw [hpow] at h4
        exact h4.symm
      have h4 := hfalse (1 / 2) hζ0
      have h5 := hslit (1 / 2) hζ0 m hm₁
      exact invBranch_true_ne_false_of_slit h5 (h3.symm.trans h4)
  have hMle : (eqLam a) ^ M * B < ρ :=
    hn₁ρ M (le_trans (Nat.le_succ n₁) (le_max_right _ _))
  exact TailP_of_invBranch_true_ge (h := h) ha0 ha1 (isChain_of_mem_H0 (hchart ζ hζD).1)
    hBpos.le (hpsiB ζ hζD) (fun u hu => (hgermPr u hu).2) hMle htrue

end

end Work.EQ
