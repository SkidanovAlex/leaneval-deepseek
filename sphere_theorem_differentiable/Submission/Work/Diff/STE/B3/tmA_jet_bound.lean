import Mathlib
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.tmA_props
import Submission.Work.Diff.STE.Comp.pdVec_eq_iteratedFDeriv
import Submission.Work.Diff.STE.flat.level_linear
import Submission.Work.Diff.STE.B3.norm_multilinear_le_of_basis
import Submission.Work.Diff.STE.B3.iteratedFDeriv_le_of_pdVec
import Submission.Work.Diff.STE.B3.transport_low_jet_bound_uniform

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

open scoped BigOperators

set_option maxHeartbeats 1000000

/-!
# Jet bounds of the periodic coefficient matrix `tmA`

The target `Work.Diff.STE.B3.tmA_jet_bound` is proved from two independent ingredients, developed
here:

* `Work.Diff.STE.B3.tmAjet_tmPer_pdVec_le` — the order-`m` jet bound for the periodisation
  (`tsupport f ⊆ Metric.ball 0 R`, `R ≤ 1/2`, so at every point at most one lattice translate of
  `f` is non-zero near that point);
* `Work.Diff.STE.B3.tmAjet_gm_pdVec_le` — the order-`m` product-rule bound for the summand
  `gm φ γ lam' p q = φ · (γ · p q - lam' · δ)` on its own support.

The remaining content of the target is the pointwise order-`0` bound of `tmA_props` and the
observation that the constant `(if p = q then lam' else 0)` is killed by differentiation of order
`≥ 1` (`tmAjet_pdVec_const_add`).
-/

/-! ## Auxiliary facts about `pdVec` -/

lemma tmAjet_pdVec_zero {ι : Type*} [Fintype ι] [DecidableEq ι] (l : Fin 0 → ι)
    (f : (ι → ℝ) → ℂ) : Work.Diff.STE.pdVec 0 l f = f := by
  rw [Work.Diff.STE.pdVec, Work.Diff.STE.pdList, List.ofFn_zero, List.foldr_nil]

lemma tmAjet_pdVec_succ_cons {ι : Type*} [Fintype ι] [DecidableEq ι] (k : ℕ)
    (l : Fin (k + 1) → ι) (f : (ι → ℝ) → ℂ) :
    Work.Diff.STE.pdVec (k + 1) l f
      = Work.Diff.STE.pd (l 0) (Work.Diff.STE.pdVec k (Fin.tail l) f) := by
  have h : List.ofFn l = l 0 :: List.ofFn (Fin.tail l) := by
    conv_lhs => rw [← Fin.cons_self_tail l]
    rw [List.ofFn_cons]
  simp only [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]
  rw [h, List.foldr_cons]

/-- Adding a constant does not change the jets of order `≥ 1`. -/
lemma tmAjet_pdVec_const_add {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ (k : ℕ) (l : Fin k → ι) (c : ℂ) (h : (ι → ℝ) → ℂ), 1 ≤ k →
      Work.Diff.STE.pdVec k l (fun y => c + h y) = Work.Diff.STE.pdVec k l h := by
  intro k
  induction k with
  | zero => intro l c h hk; omega
  | succ k ih =>
      intro l c h hk
      rcases Nat.eq_zero_or_pos k with hk0 | hkpos
      · subst hk0
        funext y
        rw [tmAjet_pdVec_succ_cons 0 l, tmAjet_pdVec_succ_cons 0 l]
        simp only [tmAjet_pdVec_zero]
        simp only [Work.Diff.STE.pd]
        rw [fderiv_const_add]
      · rw [tmAjet_pdVec_succ_cons k l, tmAjet_pdVec_succ_cons k l,
          ih (Fin.tail l) c h hkpos]

/-- Translation does not change `pdVec`-jets (as functions of the base point). -/
lemma tmAjet_pdVec_shift {ι : Type*} [Fintype ι] [DecidableEq ι] (g : (ι → ℝ) → ℂ)
    (a : ι → ℝ) : ∀ (k : ℕ) (l : Fin k → ι),
      Work.Diff.STE.pdVec k l (fun y => g (y + a))
        = fun z => Work.Diff.STE.pdVec k l g (z + a) := by
  intro k
  induction k with
  | zero =>
      intro l
      rw [Work.Diff.STE.pdVec, Work.Diff.STE.pdList, List.ofFn_zero, List.foldr_nil]
      rfl
  | succ k ih =>
      intro l
      rw [tmAjet_pdVec_succ_cons k l, ih (Fin.tail l)]
      funext z
      simp only [Work.Diff.STE.pd]
      rw [fderiv_comp_add_right, tmAjet_pdVec_succ_cons k l]
      simp only [Work.Diff.STE.pd]

lemma tmAjet_pdVec_zero_fun {ι : Type*} [Fintype ι] [DecidableEq ι] :
    ∀ (k : ℕ) (l : Fin k → ι),
      Work.Diff.STE.pdVec k l (fun _ : ι → ℝ => (0 : ℂ)) = fun _ => 0 := by
  intro k
  induction k with
  | zero => intro l; rw [tmAjet_pdVec_zero]
  | succ k ih =>
      intro l
      rw [tmAjet_pdVec_succ_cons k l, ih (Fin.tail l)]
      funext z
      simp [Work.Diff.STE.pd]

/-! ## The jet bound for the periodisation -/

/-- **Order-`m` jet bound for the periodisation `tmPer`.**

`tmPer f = ∑' m : Fin n → ℤ, f (· + iVec m)` is the real periodisation of `f`
(`Work.Diff.STE.B3.tmPer`) and `tsupport f ⊆ Metric.ball 0 R` with `R ≤ 1/2`, so that two distinct
lattice translates `f (· + iVec a)`, `f (· + iVec a')` have disjoint closed supports (a common point
would give `‖iVec a - iVec a'‖ < 2R ≤ 1`).  Claim: if every `m'`-th partial-derivative vector of `f`
at every point of `tsupport f` is bounded by `B` (`m' ≤ M`), then the same holds for the
periodisation at every point `z`.  This is the order-`m` generalisation of
`Work.Diff.STE.B3.tmPer_pdR_le_tsupport` (the case `M = 1`). -/
theorem tmAjet_tmPer_pdVec_le {n : ℕ} (R B : ℝ) (M : ℕ) (hR : R ≤ 1 / 2) (hB0 : 0 ≤ B)
    (f : (Fin n → ℝ) → ℝ) (hf : ContDiff ℝ ((⊤ : ENat) : WithTop ENat) f)
    (hts : tsupport f ⊆ Metric.ball 0 R)
    (hB : ∀ (w : Fin n → ℝ), w ∈ tsupport f → ∀ (m : ℕ), m ≤ M → ∀ (β : Fin m → Fin n),
      ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ)) w‖ ≤ B) :
    ∀ (z : Fin n → ℝ) (m : ℕ), m ≤ M → ∀ (β : Fin m → Fin n),
      ‖Work.Diff.STE.pdVec m β
        (fun y : Fin n → ℝ => ((Work.Diff.STE.B3.tmPer f y : ℝ) : ℂ)) z‖ ≤ B := by
  classical
  have hsupp : Function.support f ⊆
      Set.pi Set.univ (fun _ : Fin n => Set.Ioo (-(1 / 2 : ℝ)) (1 / 2)) :=
    fun x hx => ball_subset_cube hR (hts (subset_tsupport f hx))
  intro z m hm β
  obtain ⟨S, hS⟩ := tmPer_eventuallyEq_finset hsupp z
  -- the periodisation germ-equals the finite sum of translates near `z`
  have hS' : (fun y : Fin n → ℝ => ((∑ a ∈ S, f (y + Work.Diff.STE.iVec a) : ℝ) : ℂ))
      =ᶠ[nhds z] (fun y : Fin n → ℝ => ((Work.Diff.STE.B3.tmPer f y : ℝ) : ℂ)) := by
    filter_upwards [hS] with y hy
    rw [hy]
  rw [← pdVec_congr_germ hS' m β]
  have hsum : (fun y : Fin n → ℝ => ((∑ a ∈ S, f (y + Work.Diff.STE.iVec a) : ℝ) : ℂ))
      = fun y : Fin n → ℝ =>
          ∑ a ∈ S, ((f (y + Work.Diff.STE.iVec a) : ℝ) : ℂ) := by
    funext y
    rw [Complex.ofReal_sum]
  rw [hsum]
  have hsm : ∀ a : Fin n → ℤ, ContDiff ℝ (⊤ : ℕ∞)
      (fun y : Fin n → ℝ => ((f (y + Work.Diff.STE.iVec a) : ℝ) : ℂ)) := by
    intro a
    have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => f (y + Work.Diff.STE.iVec a)) :=
      hf.comp (contDiff_id.add contDiff_const)
    exact Complex.ofRealCLM.contDiff.comp h1
  rw [congrFun (Work.Diff.STE.flat.pdVec_finset_sum S β
    (fun a y => ((f (y + Work.Diff.STE.iVec a) : ℝ) : ℂ)) hsm) z]
  -- each summand is the translated jet of `f`
  have hshift : ∀ a : Fin n → ℤ,
      Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((f (y + Work.Diff.STE.iVec a) : ℝ) : ℂ)) z
        = Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ))
            (z + Work.Diff.STE.iVec a) := by
    intro a
    exact congrFun (tmAjet_pdVec_shift (fun w : Fin n → ℝ => ((f w : ℝ) : ℂ))
      (Work.Diff.STE.iVec a) m β) z
  rw [Finset.sum_congr rfl (fun a _ => hshift a)]
  -- only the translates whose base point lies in `tsupport f` can contribute
  set S' : Finset (Fin n → ℤ) :=
    S.filter (fun a => z + Work.Diff.STE.iVec a ∈ tsupport f) with hS'def
  have hdrop : ∑ a ∈ S, Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ))
        (z + Work.Diff.STE.iVec a)
      = ∑ a ∈ S', Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ))
        (z + Work.Diff.STE.iVec a) := by
    rw [hS'def]
    symm
    refine Finset.sum_subset (Finset.filter_subset _ S) fun a haS haS' => ?_
    have hnot : z + Work.Diff.STE.iVec a ∉ tsupport f := fun hcon =>
      haS' (Finset.mem_filter.mpr ⟨haS, hcon⟩)
    have hnb : (tsupport f)ᶜ ∈ nhds (z + Work.Diff.STE.iVec a) :=
      (isClosed_tsupport f).isOpen_compl.mem_nhds hnot
    have heq : f =ᶠ[nhds (z + Work.Diff.STE.iVec a)] (fun _ : Fin n → ℝ => (0 : ℝ)) :=
      Filter.eventually_of_mem hnb (fun y hy => by
        by_contra hc
        exact hy (subset_tsupport f (Function.mem_support.mpr hc)))
    have heqC : (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ))
        =ᶠ[nhds (z + Work.Diff.STE.iVec a)] (fun _ : Fin n → ℝ => (0 : ℂ)) := by
      filter_upwards [heq] with y hy
      rw [hy]
      rfl
    rw [pdVec_congr_germ heqC m β]
    simp [tmAjet_pdVec_zero_fun]
  rw [hdrop]
  -- the bound
  have hcard : S'.card ≤ 1 := by
    rw [hS'def, Finset.card_le_one]
    intro a ha b hb
    exact eq_of_mem_ball hR (hts (Finset.mem_filter.mp ha).2) (hts (Finset.mem_filter.mp hb).2)
  calc ‖∑ a ∈ S', Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ))
          (z + Work.Diff.STE.iVec a)‖
      ≤ ∑ a ∈ S', ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((f y : ℝ) : ℂ))
          (z + Work.Diff.STE.iVec a)‖ := norm_sum_le _ _
    _ ≤ ∑ a ∈ S', B := by
        refine Finset.sum_le_sum fun a ha => ?_
        rw [hS'def] at ha
        exact hB _ (Finset.mem_filter.mp ha).2 m hm β
    _ = B * (S'.card : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ B * 1 := mul_le_mul_of_nonneg_left (by exact_mod_cast hcard) hB0
    _ = B := by ring

/-! ## The jet bound for the summand `gm` -/

/-- **Jet bound for the summand `gm` of the periodic coefficient matrix.**

`Work.Diff.STE.B3.gm φ γ lam' p q = fun y => φ y * (γ y p q - (if p = q then lam' else 0))`.
If the `m`-jets (`m ≤ k`) of `φ` are bounded by `Mφ` everywhere and those of the entries `γ · p q`
are bounded by `Kr` on `Metric.ball 0 R`, and `tsupport φ ⊆ Metric.ball 0 R`, then there is
`C = C(n, R, c, Kr, Mφ, k)` bounding the `m`-jets (`m ≤ k`) of `gm φ γ lam' p q` on
`tsupport (gm φ γ lam' p q) ⊆ tsupport φ ⊆ Metric.ball 0 R`.  This is the order-`m` analogue of
`Work.Diff.STE.B3.abs_pdR_gm_le`. -/
theorem tmAjet_gm_pdVec_le {n : ℕ} (R c Kr Mφ : ℝ) (hR : R ≤ 1 / 2) (hc : 0 < c)
    (hKr : 0 ≤ Kr) (hMφ : 0 ≤ Mφ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (φ : (Fin n → ℝ) → ℝ) (γ : (Fin n → ℝ) → Fin n → Fin n → ℝ) (lam' : ℝ),
        0 < lam' → lam' ≤ c →
        ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ → (∀ z, 0 ≤ φ z) → (∀ z, φ z ≤ 1) →
        (∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin n) (z : Fin n → ℝ),
          ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((φ y : ℝ) : ℂ)) z‖ ≤ Mφ) →
        tsupport φ ⊆ Metric.ball 0 R →
        (∀ p q, ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) (fun w => γ w p q) (Metric.ball 0 R)) →
        (∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin n) (z : Fin n → ℝ) (p q : Fin n),
          z ∈ Metric.ball 0 R →
          ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((γ y p q : ℝ) : ℂ)) z‖ ≤ Kr) →
        ∀ (p q : Fin n) (w : Fin n → ℝ), w ∈ tsupport (Work.Diff.STE.B3.gm φ γ lam' p q) →
          ∀ (m : ℕ), m ≤ k → ∀ (β : Fin m → Fin n),
          ‖Work.Diff.STE.pdVec m β
            (fun y : Fin n → ℝ => ((Work.Diff.STE.B3.gm φ γ lam' p q y : ℝ) : ℂ)) w‖ ≤ C := by
  classical
  refine ⟨((k : ℝ) + 1) ^ 2 * (2 : ℝ) ^ k * ((n : ℝ) + 1) ^ k * ((n : ℝ) + 1) ^ k
      * (Mφ + 1) * (Kr + c + 1), ?_, ?_⟩
  · positivity
  · intro φ γ lam' hlam hlamc hφ hφ0 hφ1 hφd hφts hγs hγd p q w hw m hm β
    have hwts : w ∈ tsupport φ := tsupport_gm_subset (γ := γ) (lam' := lam') p q hw
    have hwR : w ∈ Metric.ball 0 R := hφts hwts
    set c₀ : ℝ := (if p = q then lam' else 0) with hc₀
    set Φ : (Fin n → ℝ) → ℂ := fun y => ((φ y : ℝ) : ℂ) with hΦ
    set Δ : (Fin n → ℝ) → ℂ := fun y => ((γ y p q - c₀ : ℝ) : ℂ) with hΔ
    -- smoothness of the two factors
    have hΦsm : ContDiff ℝ (⊤ : ℕ∞) Φ := Complex.ofRealCLM.contDiff.comp hφ
    have hΔsm : ContDiffOn ℝ (⊤ : ℕ∞) Δ (Metric.ball 0 R) := by
      have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => γ y p q - c₀)
          (Metric.ball 0 R) := (hγs p q).sub contDiffOn_const
      exact Complex.ofRealCLM.contDiff.comp_contDiffOn h1
    have hΔsmAt : ContDiffAt ℝ (⊤ : ℕ∞) Δ w :=
      hΔsm.contDiffAt (Metric.isOpen_ball.mem_nhds hwR)
    have hsm : ContDiffAt ℝ (⊤ : ℕ∞) (fun y : Fin n → ℝ => Φ y * Δ y) w :=
      hΦsm.contDiffAt.mul hΔsmAt
    -- the bound on the subtracted constant
    have hc₀le : |c₀| ≤ c := by
      rw [hc₀]
      by_cases hpq : p = q
      · rw [if_pos hpq, abs_of_pos hlam]; exact hlamc
      · rw [if_neg hpq, abs_zero]; linarith
    -- `pdVec`-bounds of the two factors at `w`
    have hΦpd : ∀ (j : ℕ), j ≤ k → ∀ (β' : Fin j → Fin n),
        ‖Work.Diff.STE.pdVec j β' Φ w‖ ≤ Mφ := by
      intro j hj β'
      rw [hΦ]
      exact hφd j hj β' w
    have hΔpd : ∀ (j : ℕ), j ≤ k → ∀ (β' : Fin j → Fin n),
        ‖Work.Diff.STE.pdVec j β' Δ w‖ ≤ Kr + c := by
      intro j hj β'
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · subst hj0
        rw [tmAjet_pdVec_zero β', hΔ]
        have h1 : |γ w p q| ≤ Kr := by
          have h := hγd 0 (Nat.zero_le k) (Fin.elim0 : Fin 0 → Fin n) w p q hwR
          rw [tmAjet_pdVec_zero (Fin.elim0 : Fin 0 → Fin n)] at h
          simpa using h
        calc ‖((γ w p q - c₀ : ℝ) : ℂ)‖ = |γ w p q - c₀| :=
              RCLike.norm_ofReal (K := ℂ) (γ w p q - c₀)
          _ ≤ |γ w p q| + |c₀| := abs_sub _ _
          _ ≤ Kr + c := add_le_add h1 hc₀le
      · have hsplit : (fun y : Fin n → ℝ => ((γ y p q - c₀ : ℝ) : ℂ))
            = fun y : Fin n → ℝ => ((-c₀ : ℝ) : ℂ) + ((γ y p q : ℝ) : ℂ) := by
          funext y
          rw [show γ y p q - c₀ = (-c₀) + γ y p q from by ring, Complex.ofReal_add]
        rw [hΔ, hsplit, tmAjet_pdVec_const_add j β' ((-c₀ : ℝ) : ℂ)
          (fun y : Fin n → ℝ => ((γ y p q : ℝ) : ℂ)) hjpos]
        exact le_trans (hγd j hj β' w p q hwR) (by linarith)
    -- iterated-derivative bounds of the two factors at `w`
    have hconv : ∀ (F : (Fin n → ℝ) → ℂ) (Kd : ℝ), 0 ≤ Kd → ContDiffAt ℝ (⊤ : ℕ∞) F w →
        (∀ (j : ℕ), j ≤ k → ∀ (β' : Fin j → Fin n),
          ‖Work.Diff.STE.pdVec j β' F w‖ ≤ Kd) →
        ∀ j ≤ k, ‖iteratedFDeriv ℝ j F w‖ ≤ (n : ℝ) ^ j * Kd := by
      intro F Kd hKd hFsm hbd j hj
      have hb : ∀ γ' : Fin j → Fin n,
          ‖iteratedFDeriv ℝ j F w (fun i => Pi.single (γ' i) (1 : ℝ))‖ ≤ Kd := by
        intro γ'
        rw [← pdVec_eq_iteratedFDeriv_at hFsm j γ']
        exact hbd j hj γ'
      exact norm_multilinear_le_of_basis (iteratedFDeriv ℝ j F w) hKd hb
    have hΦit : ∀ j ≤ k, ‖iteratedFDeriv ℝ j Φ w‖ ≤ (n : ℝ) ^ j * Mφ :=
      hconv Φ Mφ hMφ hΦsm.contDiffAt hΦpd
    have hΔit : ∀ j ≤ k, ‖iteratedFDeriv ℝ j Δ w‖ ≤ (n : ℝ) ^ j * (Kr + c) :=
      hconv Δ (Kr + c) (by linarith) hΔsmAt hΔpd
    -- the Leibniz bound
    have hLeib : ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => Φ y * Δ y) w‖
        ≤ ∑ i ∈ Finset.range (m + 1),
            (m.choose i : ℝ) * ((n : ℝ) ^ i * Mφ) * ((n : ℝ) ^ (m - i) * (Kr + c)) := by
      have hwit := norm_iteratedFDerivWithin_mul_le hΦsm.contDiffOn hΔsm
        Metric.isOpen_ball.uniqueDiffOn hwR
        (show ((m : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) from
          WithTop.coe_le_coe.mpr le_top)
      rw [iteratedFDerivWithin_of_isOpen m Metric.isOpen_ball hwR] at hwit
      refine le_trans hwit (Finset.sum_le_sum fun i hi => ?_)
      have hi' : i ≤ m := Finset.mem_range_succ_iff.mp hi
      have h1 : iteratedFDerivWithin ℝ i Φ (Metric.ball 0 R) w
          = iteratedFDeriv ℝ i Φ w :=
        iteratedFDerivWithin_of_isOpen i Metric.isOpen_ball hwR
      have h2 : iteratedFDerivWithin ℝ (m - i) Δ (Metric.ball 0 R) w
          = iteratedFDeriv ℝ (m - i) Δ w :=
        iteratedFDerivWithin_of_isOpen (m - i) Metric.isOpen_ball hwR
      rw [h1, h2]
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hΦit i (le_trans hi' hm)) (Nat.cast_nonneg _))
        (hΔit (m - i) (le_trans (Nat.sub_le m i) hm)) (norm_nonneg _)
        (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (pow_nonneg (Nat.cast_nonneg n) i) hMφ))
    -- the arithmetic
    set Y : ℝ := (2 : ℝ) ^ k * (((n : ℝ) + 1) ^ k * ((n : ℝ) + 1) ^ k) * (Mφ + 1)
      * (Kr + c + 1) with hYdef
    have hY : 0 ≤ Y := by rw [hYdef]; positivity
    have hfinal : ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * ((n : ℝ) ^ i * Mφ) * ((n : ℝ) ^ (m - i) * (Kr + c))
        ≤ ((k : ℝ) + 1) ^ 2 * Y := by
      have hchoose : ∀ i : ℕ, i ≤ m → (m.choose i : ℝ) ≤ (2 : ℝ) ^ k := by
        intro i hi
        have h1 : m.choose i ≤ 2 ^ m := by
          have h2 := Finset.single_le_sum (f := fun j => m.choose j)
            (fun j _ => Nat.zero_le _) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
          rwa [Nat.sum_range_choose] at h2
        have h3 : (2 : ℝ) ^ m ≤ (2 : ℝ) ^ k := pow_le_pow_right₀ (by norm_num) hm
        exact le_trans (by exact_mod_cast h1) h3
      have hpow : ∀ (j : ℕ), j ≤ k → (n : ℝ) ^ j ≤ ((n : ℝ) + 1) ^ k := by
        intro j hj
        have h1 : (n : ℝ) ^ j ≤ ((n : ℝ) + 1) ^ j :=
          pow_le_pow_left₀ (Nat.cast_nonneg n) (by linarith) j
        have h2 : ((n : ℝ) + 1) ^ j ≤ ((n : ℝ) + 1) ^ k :=
          pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1) hj
        linarith
      have hterm : ∀ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * ((n : ℝ) ^ i * Mφ) * ((n : ℝ) ^ (m - i) * (Kr + c)) ≤ Y := by
        intro i hi
        have hi' : i ≤ m := Finset.mem_range_succ_iff.mp hi
        have hA := hchoose i hi'
        have hB1 := hpow i (le_trans hi' hm)
        have hB2 := hpow (m - i) (le_trans (Nat.sub_le m i) hm)
        have h1 : (m.choose i : ℝ) * ((n : ℝ) ^ i * Mφ)
            ≤ (2 : ℝ) ^ k * (((n : ℝ) + 1) ^ k * (Mφ + 1)) :=
          mul_le_mul hA (mul_le_mul hB1 (by linarith) hMφ (by positivity))
            (by positivity) (by positivity)
        have h2 : (n : ℝ) ^ (m - i) * (Kr + c) ≤ ((n : ℝ) + 1) ^ k * (Kr + c + 1) :=
          mul_le_mul hB2 (by linarith) (by linarith) (by positivity)
        calc (m.choose i : ℝ) * ((n : ℝ) ^ i * Mφ) * ((n : ℝ) ^ (m - i) * (Kr + c))
            ≤ ((2 : ℝ) ^ k * (((n : ℝ) + 1) ^ k * (Mφ + 1)))
                * (((n : ℝ) + 1) ^ k * (Kr + c + 1)) :=
              mul_le_mul h1 h2 (by positivity) (by positivity)
          _ = Y := by rw [hYdef]; ring
      calc ∑ i ∈ Finset.range (m + 1),
            (m.choose i : ℝ) * ((n : ℝ) ^ i * Mφ) * ((n : ℝ) ^ (m - i) * (Kr + c))
          ≤ ∑ i ∈ Finset.range (m + 1), Y := Finset.sum_le_sum hterm
        _ = ((m : ℝ) + 1) * Y := by
              rw [Finset.sum_const, nsmul_eq_mul, Finset.card_range]; norm_num
        _ ≤ ((k : ℝ) + 1) * Y := by
              have hm' : (m : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hm
              exact mul_le_mul_of_nonneg_right (by linarith) hY
        _ ≤ ((k : ℝ) + 1) ^ 2 * Y := by
              have h2 : (0 : ℝ) ≤ (k : ℝ) + 1 := by
                linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ (k : ℝ))]
              have h4 : Y ≤ ((k : ℝ) + 1) * Y := by
                calc Y = 1 * Y := by ring
                  _ ≤ ((k : ℝ) + 1) * Y := mul_le_mul_of_nonneg_right (by linarith) hY
              calc ((k : ℝ) + 1) * Y ≤ ((k : ℝ) + 1) * (((k : ℝ) + 1) * Y) :=
                    mul_le_mul_of_nonneg_left h4 h2
                _ = ((k : ℝ) + 1) ^ 2 * Y := by ring
    -- assemble
    have hfun : (fun y : Fin n → ℝ => ((gm φ γ lam' p q y : ℝ) : ℂ))
        = fun y : Fin n → ℝ => Φ y * Δ y := by
      funext y
      simp only [hΦ, hΔ, hc₀]
      rw [show gm φ γ lam' p q y
            = φ y * (γ y p q - (if p = q then lam' else 0)) from rfl, Complex.ofReal_mul]
    calc ‖Work.Diff.STE.pdVec m β
          (fun y : Fin n → ℝ => ((gm φ γ lam' p q y : ℝ) : ℂ)) w‖
        = ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => Φ y * Δ y) w
            (fun i => Pi.single (β i) (1 : ℝ))‖ := by
          rw [hfun, pdVec_eq_iteratedFDeriv_at hsm m β]
      _ ≤ ‖iteratedFDeriv ℝ m (fun y : Fin n → ℝ => Φ y * Δ y) w‖ := by
          have h := ContinuousMultilinearMap.le_opNorm
            (iteratedFDeriv ℝ m (fun y : Fin n → ℝ => Φ y * Δ y) w)
            (fun i : Fin m => (Pi.single (β i) (1 : ℝ) : Fin n → ℝ))
          have hprod : ∏ i : Fin m, ‖(Pi.single (β i) (1 : ℝ) : Fin n → ℝ)‖ = 1 := by
            simp [Pi.norm_single]
          rwa [hprod, mul_one] at h
      _ ≤ ∑ i ∈ Finset.range (m + 1),
            (m.choose i : ℝ) * ((n : ℝ) ^ i * Mφ) * ((n : ℝ) ^ (m - i) * (Kr + c)) := hLeib
      _ ≤ ((k : ℝ) + 1) ^ 2 * (2 : ℝ) ^ k * ((n : ℝ) + 1) ^ k * ((n : ℝ) + 1) ^ k
            * (Mφ + 1) * (Kr + c + 1) := by
          rw [show ((k : ℝ) + 1) ^ 2 * (2 : ℝ) ^ k * ((n : ℝ) + 1) ^ k * ((n : ℝ) + 1) ^ k
                * (Mφ + 1) * (Kr + c + 1) = ((k : ℝ) + 1) ^ 2 * Y from by rw [hYdef]; ring]
          exact hfinal

/-- **Jet bounds of the periodic coefficient matrix `tmA φ lam' γ`.**

`tmA φ lam' γ z p q = (if p = q then lam' else 0) + tmPer (fun w => φ w * (γ w p q - (if p = q then lam' else 0))) z`,
where `tmPer` is the real periodisation of a compactly supported function
(`Work.Diff.STE.B3.tmPer`, `Submission/Work/Diff/STE/B3/transport_tame_defs.lean`).  This is the
order-`≤ k` generalisation of the already proved order-`0,1` result `Work.Diff.STE.B3.tmA_props`
(`Submission/Work/Diff/STE/B3/tmA_props.lean`), which is the template to follow: its helpers
`tmPer_eq_of_support`, `eq_of_mem_ball`, `tmPer_eventuallyEq_finset`, `pdR_mul_eq`,
`pdR_sub_const`, `abs_pdR_gm_le` and `tmPer_pdR_le_tsupport` are all proved there (import that
module rather than reproving them); the new content is the order-`m` analogue of
`tmPer_pdR_le_tsupport` (and of the two product-rule bounds).

WHY IT IS TRUE.  `support φ ⊆ tsupport φ ⊆ Metric.ball 0 R` with `R ≤ 1/2`, so two distinct lattice
translates can never both lie in `Metric.ball 0 R`; hence `tmPer gm` (with
`gm := φ * (γ - lam'•1)`) is, at every `z`, the value of `gm` at the single contributing translate
(see `Work.Diff.STE.B3.tmA_eq_govIdx`), and its `m`-jet is obtained from the `m`-jet of `gm` there by
the translation (which does not change `pdVec`-jets).  The `m`-th order product rule for
`φ * (γ - lam'•1)` uses only jets of order `≤ m` of `φ` (bounded by `Mφ`) and of `γ` (bounded by
`Kr` on `Metric.ball 0 R`, the support of the product).  So `C = C(R, c, Kr, Mφ, k)` exists.
Degenerate cases (`R ≤ 0` forces `φ ≡ 0` and `tmA = lam'•1`; `n = 0`; `k = 0`) are all fine, and the
claim is not vacuous (e.g. `φ` a bump and `γ` constant).  Note `lam'` occurs only linearly in
`(γ - lam'•1)` and `lam' ≤ c`, so a single `C` covers all admissible `lam'`.

PROOF.  The two ingredients are the companion lemmas `Work.Diff.STE.B3.tmAjet_gm_pdVec_le` (the
order-`m` product-rule bound for the summand `gm = φ * (γ - lam'•1)`, on
`tsupport gm ⊆ tsupport φ ⊆ Metric.ball 0 R`) and `Work.Diff.STE.B3.tmAjet_tmPer_pdVec_le` (the
order-`m` jet bound for the periodisation of a function supported in `Metric.ball 0 R`, `R ≤ 1/2`).
At `m = 0` the bound is the pointwise one of `tmA_props` (`abs_gm_le` + `abs_tmPer_le`); for `m ≥ 1`
the constant `(if p = q then lam' else 0)` is killed by differentiation
(`tmAjet_pdVec_const_add`), leaving exactly the jet of `tmPer (gm φ γ lam' p q)`. -/
theorem tmA_jet_bound {n : ℕ} (R c Kr Mφ : ℝ) (hR : R ≤ 1 / 2) (hc : 0 < c) (hKr : 0 ≤ Kr)
    (hMφ : 0 ≤ Mφ) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (φ : (Fin n → ℝ) → ℝ) (γ : (Fin n → ℝ) → Fin n → Fin n → ℝ) (lam' : ℝ),
        0 < lam' → lam' ≤ c →
        ContDiff ℝ ((⊤ : ENat) : WithTop ENat) φ → (∀ z, 0 ≤ φ z) → (∀ z, φ z ≤ 1) →
        (∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin n) (z : Fin n → ℝ),
          ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((φ y : ℝ) : ℂ)) z‖ ≤ Mφ) →
        tsupport φ ⊆ Metric.ball 0 R →
        (∀ p q, ContDiffOn ℝ ((⊤ : ENat) : WithTop ENat) (fun w => γ w p q) (Metric.ball 0 R)) →
        (∀ z ∈ Metric.ball 0 R, ∀ p q, γ z p q = γ z q p) →
        (∀ z ∈ Metric.ball 0 R, ∀ ξ : Fin n → ℝ,
          c * ∑ p, (ξ p) ^ 2 ≤ ∑ p, ∑ q, γ z p q * ξ p * ξ q) →
        (∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin n) (z : Fin n → ℝ) (p q : Fin n),
          z ∈ Metric.ball 0 R →
          ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ => ((γ y p q : ℝ) : ℂ)) z‖ ≤ Kr) →
        ∀ (m : ℕ) (hm : m ≤ k) (β : Fin m → Fin n) (z : Fin n → ℝ) (p q : Fin n),
          ‖Work.Diff.STE.pdVec m β (fun y : Fin n → ℝ =>
            ((Work.Diff.STE.B3.tmA φ lam' γ y p q : ℝ) : ℂ)) z‖ ≤ C := by
  -- the order-`m` jet bound for the summand `gm = φ * (γ - lam'·1)` on its support
  obtain ⟨Jb, hJb0, hJb⟩ := tmAjet_gm_pdVec_le (n := n) R c Kr Mφ hR hc hKr hMφ k
  refine ⟨max (2 * c + Kr) Jb, ?_, ?_⟩
  · exact le_trans (by linarith : (0 : ℝ) ≤ 2 * c + Kr) (le_max_left _ _)
  · intro φ γ lam' hlam hlamc hφ hφ0 hφ1 hφd hφts hγs hγsymm hγpos hγd m hm β z p q
    have hφsupp : Function.support φ ⊆ Metric.ball 0 R :=
      fun x hx => hφts (subset_tsupport φ hx)
    rcases Nat.eq_zero_or_pos m with hm0 | hmpos
    · -- ## order `0`: the pointwise bound of `tmA_props`
      subst hm0
      rw [tmAjet_pdVec_zero β]
      have hγb : ∀ z' ∈ Metric.ball 0 R, ∀ p' q' : Fin n, |γ z' p' q'| ≤ Kr := by
        intro z' hz' p' q'
        have h := hγd 0 (Nat.zero_le k) (Fin.elim0 : Fin 0 → Fin n) z' p' q' hz'
        rw [tmAjet_pdVec_zero (Fin.elim0 : Fin 0 → Fin n)] at h
        simpa using h
      have hval : |tmA φ lam' γ z p q| ≤ 2 * c + Kr := by
        show |(if p = q then lam' else 0) + tmPer (gm φ γ lam' p q) z| ≤ 2 * c + Kr
        have hδ : |(if (p : Fin n) = q then lam' else 0)| ≤ c := by
          by_cases hpq : p = q
          · rw [if_pos hpq, abs_of_pos hlam]; exact hlamc
          · rw [if_neg hpq, abs_zero]; linarith
        have hgm : ∀ w, |gm φ γ lam' p q w| ≤ Kr + c :=
          abs_gm_le p q hc hKr hlam hlamc hφ0 hφ1 hφsupp hγb
        have hT : |tmPer (gm φ γ lam' p q) z| ≤ Kr + c :=
          abs_tmPer_le hR
            (support_gm_subset_ball (γ := γ) (lam' := lam') p q hφsupp) hgm z
        calc |(if p = q then lam' else 0) + tmPer (gm φ γ lam' p q) z|
            ≤ |(if p = q then lam' else 0)| + |tmPer (gm φ γ lam' p q) z| := abs_add_le _ _
          _ ≤ c + (Kr + c) := add_le_add hδ hT
          _ ≤ 2 * c + Kr := by linarith
      calc ‖((tmA φ lam' γ z p q : ℝ) : ℂ)‖ = |tmA φ lam' γ z p q| := by simp
        _ ≤ 2 * c + Kr := hval
        _ ≤ max (2 * c + Kr) Jb := le_max_left _ _
    · -- ## order `≥ 1`: kill the constant and use the periodisation's jet bound
      have hB : ∀ (w : Fin n → ℝ), w ∈ tsupport (gm φ γ lam' p q) → ∀ (m' : ℕ), m' ≤ k →
          ∀ (β' : Fin m' → Fin n),
            ‖Work.Diff.STE.pdVec m' β'
              (fun y : Fin n → ℝ => ((gm φ γ lam' p q y : ℝ) : ℂ)) w‖ ≤ Jb :=
        fun w hw m' hm' β' =>
          hJb φ γ lam' hlam hlamc hφ hφ0 hφ1 hφd hφts hγs hγd p q w hw m' hm' β'
      have htmPer := tmAjet_tmPer_pdVec_le (n := n) R Jb k hR hJb0 (gm φ γ lam' p q)
        (contDiff_gm p q hφ hφts (hγs p q))
        (fun x hx => hφts (tsupport_gm_subset (γ := γ) (lam' := lam') p q hx)) hB
      have hsplit : (fun y : Fin n → ℝ => ((tmA φ lam' γ y p q : ℝ) : ℂ))
          = fun y : Fin n → ℝ => (((if p = q then lam' else 0 : ℝ)) : ℂ)
              + ((tmPer (gm φ γ lam' p q) y : ℝ) : ℂ) := by
        funext y
        rw [show tmA φ lam' γ y p q
              = (if p = q then lam' else 0) + tmPer (gm φ γ lam' p q) y from rfl]
        rw [Complex.ofReal_add]
      have hfin : ‖Work.Diff.STE.pdVec m β
          (fun y : Fin n → ℝ => ((tmA φ lam' γ y p q : ℝ) : ℂ)) z‖ ≤ Jb := by
        rw [hsplit, tmAjet_pdVec_const_add m β (((if p = q then lam' else 0 : ℝ)) : ℂ)
          (fun y : Fin n → ℝ => ((tmPer (gm φ γ lam' p q) y : ℝ) : ℂ)) hmpos]
        exact htmPer z m hm β
      exact le_trans hfin (le_max_right _ _)

end Work.Diff.STE.B3
