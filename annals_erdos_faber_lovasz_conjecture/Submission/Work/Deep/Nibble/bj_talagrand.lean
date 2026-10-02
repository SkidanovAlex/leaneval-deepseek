import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Reed.Prob.Certified.Analysis
import Submission.Work.Deep.Reed.Prob.Certified.EngineStep
import Submission.Work.Deep.Reed.Prob.Product
import Submission.Work.Deep.Reed.Prob.lll_symmetric
import Submission.Work.Deep.Nibble.BJ.layer_cake
import Submission.Work.Deep.Nibble.BJ.exists_median

/-
# Bruhn--Joos concentration from certificates, for a general product measure

This file proves `Work.Deep.Nibble.bj_talagrand`: the Bruhn--Joos
(Annals of Math. 198 (2) 2023, Theorem 2.1 in the arXiv source, `thm:bj-tala`)
concentration inequality for a random variable on a product of finite
probability spaces of full support, with exceptional outcomes.

The route is the one in Bruhn--Joos, *A stronger bound for the strong chromatic
index* (arXiv:1504.02583), Section "Talagrand's inequality and exceptional
outcomes":

* `pi_two_set` : Talagrand's convex distance inequality for a general
  full-support product measure, in two-set form with a unit witness vector
  (from the convex-distance engine `Work.Deep.Reed.Prob.engine_all`).
* `pi_two_set_certified` : the same with a certificate set `I` and `r`
  disagreements, via the witness `1_I / sqrt |I|`.
* `pi_median_tail` : concentration around a **median**, Lemma `lem: talagrand
  excep1` of Bruhn--Joos, obtained by applying the two-set estimate to the two
  medians.
* `exp_le_gamma_sum` / `abs_exp_le` : the layer-cake estimate for the
  expectation of `|X - m|`.
* `exp_sub_median_le` : the mean-median estimate `|E X - m| <= 22 c sqrt s`
  (Bruhn--Joos' `lem: med exp`, with better constants, using the numerical sum
  bound `BJ.exp_sum_bound`).
* the final assembly, where the shift `|E X - m| <= 22 c sqrt s < t/2`
  (valid because `t > 50 c sqrt s`) and the exponent identity
  `(t/2)^2/(4 c^2 s) = t^2/(16 c^2 s)` give the claimed bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

open scoped BigOperators
open Work.Deep.Reed
namespace Work.Deep.Nibble

private lemma prob_setOf {Ω : Type*} [Fintype Ω] (ν : FinProb Ω) (P : Ω → Prop) [DecidablePred P] :
    ν.prob {ω | P ω} = ∑ ω, if P ω then ν.wt ω else 0 := by
  classical
  rw [FinProb.prob]
  refine Finset.sum_congr rfl (fun ω _ => ?_)
  by_cases h : P ω
  · rw [if_pos h, if_pos (show ω ∈ {ω | P ω} from h)]
  · rw [if_neg h, if_neg (show ¬ (ω ∈ {ω | P ω}) from h)]

private lemma prob_mul_le_sdiff {Ω : Type*} [Fintype Ω] (ν : FinProb Ω) (L H S : Set Ω) :
    ν.prob L * ν.prob H ≤ ν.prob (L \ S) * ν.prob (H \ S) + ν.prob (L ∩ S) + ν.prob (H ∩ S) := by
  classical
  have hL : ν.prob L = ν.prob (L \ S) + ν.prob (L ∩ S) := by
    have h := FinProb.prob_union_add_inter ν (L \ S) (L ∩ S)
    have h1 : (L \ S) ∪ (L ∩ S) = L := by
      ext x; simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]; tauto
    have h2 : (L \ S) ∩ (L ∩ S) = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]; tauto
    rw [h1, h2, FinProb.prob_empty] at h
    linarith
  have hH : ν.prob H = ν.prob (H \ S) + ν.prob (H ∩ S) := by
    have h := FinProb.prob_union_add_inter ν (H \ S) (H ∩ S)
    have h1 : (H \ S) ∪ (H ∩ S) = H := by
      ext x; simp only [Set.mem_union, Set.mem_sdiff, Set.mem_inter_iff]; tauto
    have h2 : (H \ S) ∩ (H ∩ S) = ∅ := by
      ext x; simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_empty_iff_false, iff_false]; tauto
    rw [h1, h2, FinProb.prob_empty] at h
    linarith
  rw [hL, hH]
  have hb : ν.prob (L \ S) ≤ 1 := FinProb.prob_le_one ν _
  have hHle : ν.prob (H \ S) + ν.prob (H ∩ S) ≤ 1 := by rw [← hH]; exact FinProb.prob_le_one ν H
  have ha : 0 ≤ ν.prob (H ∩ S) := FinProb.prob_nonneg ν _
  have hbs : 0 ≤ ν.prob (L ∩ S) := FinProb.prob_nonneg ν _
  have h1 := mul_le_of_le_one_left ha hb
  have h2 := mul_le_of_le_one_left hbs hHle
  nlinarith [h1, h2]

private lemma abs_exp_le {Ω : Type*} [Fintype Ω] (ν : FinProb Ω) (Y : Ω → ℝ) :
    |ν.exp Y| ≤ ν.exp (fun ω => |Y ω|) := by
  have h1 : ν.exp Y ≤ ν.exp (fun ω => |Y ω|) := ν.exp_mono (fun ω => le_abs_self _)
  have h2 : ν.exp (fun ω => -Y ω) ≤ ν.exp (fun ω => |Y ω|) := ν.exp_mono (fun ω => neg_le_abs _)
  rw [show (fun ω => -Y ω) = (fun ω => (-1 : ℝ) * Y ω) by funext ω; ring] at h2
  rw [FinProb.exp_mul_left] at h2
  rw [abs_le]
  constructor <;> linarith

private lemma unit_witness_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {I : Finset ι} (hI : I.Nonempty) :
    Prob.sqnorm (fun i => if i ∈ I then 1 / Real.sqrt (I.card : ℝ) else 0) = 1 := by
  have hIcardpos : 0 < (I.card : ℝ) := by exact_mod_cast Finset.card_pos.mpr hI
  rw [Prob.sqnorm]
  have hpt : ∀ i : ι, (if i ∈ I then 1 / Real.sqrt (I.card : ℝ) else 0) ^ 2
      = if i ∈ I then (1 / Real.sqrt (I.card : ℝ)) ^ 2 else 0 := by
    intro i; by_cases hi : i ∈ I <;> simp [hi]
  rw [Finset.sum_congr rfl (fun i _ => hpt i),
    show (∑ i : ι, if i ∈ I then (1 / Real.sqrt (I.card : ℝ)) ^ 2 else 0)
      = ∑ _i ∈ I, (1 / Real.sqrt (I.card : ℝ)) ^ 2 by
      rw [← Finset.sum_filter]; simp,
    Finset.sum_const, nsmul_eq_mul]
  rw [div_pow, one_pow, Real.sq_sqrt hIcardpos.le]
  field_simp

private lemma witness_mul_sum_pi {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, DecidableEq (Ω i)]
    (I : Finset ι) (x y : ∀ i, Ω i) :
    ((I.filter (fun i => x i ≠ y i)).card : ℝ) / Real.sqrt (I.card : ℝ)
      = ∑ i : ι, (if i ∈ I then 1 / Real.sqrt (I.card : ℝ) else 0) * Prob.disag x y i := by
  classical
  have hdis : ∀ i, Prob.disag x y i = ((if x i ≠ y i then 1 else 0 : ℕ) : ℝ) := by
    intro i; by_cases h : x i = y i <;> simp [Prob.disag, h]
  have h1 : (∑ i : ι, (if i ∈ I then 1 / Real.sqrt (I.card : ℝ) else 0) * Prob.disag x y i)
      = ∑ i ∈ I, (1 / Real.sqrt (I.card : ℝ)) * Prob.disag x y i := by
    rw [show (∑ i : ι, (if i ∈ I then 1 / Real.sqrt (I.card : ℝ) else 0) * Prob.disag x y i)
        = ∑ i : ι, (if i ∈ I then (1 / Real.sqrt (I.card : ℝ)) * Prob.disag x y i else 0) by
      exact Finset.sum_congr rfl (fun i _ => by by_cases hi : i ∈ I <;> simp [hi])]
    rw [← Finset.sum_filter]
    simp
  rw [h1, ← Finset.mul_sum]
  have h3 : (∑ i ∈ I, Prob.disag x y i) = ((I.filter (fun i => x i ≠ y i)).card : ℝ) := by
    have h : (∑ i ∈ I, Prob.disag x y i)
        = ∑ i ∈ I, ((if x i ≠ y i then 1 else 0 : ℕ) : ℝ) :=
      Finset.sum_congr rfl (fun i _ => hdis i)
    rw [h, ← Nat.cast_sum, ← Finset.card_filter]
  rw [h3]
  ring

private lemma pi_two_set {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (μ : ∀ i, FinProb (Ω i)) (hfull : ∀ i x, 0 < (μ i).wt x)
    (A B : Set (∀ i, Ω i)) (τ : ℝ) (hτ : 0 ≤ τ)
    (h : ∀ ω ∈ B, ∃ α : ι → ℝ, Prob.sqnorm α = 1 ∧ (∀ i, 0 ≤ α i) ∧
      ∀ ω' ∈ A, τ ≤ ∑ i, α i * Prob.disag ω ω' i) :
    (FinProb.pi μ).prob A * (FinProb.pi μ).prob B ≤ Real.exp (-τ ^ 2 / 4) := by
  classical
  by_cases hAne : A.Nonempty
  · have hEng : (FinProb.pi μ).prob A * (FinProb.pi μ).exp (fun f => Real.exp (Prob.cdsq A f / 4)) ≤ 1 :=
      Prob.engine_all ι Ω μ hfull A
    have htail := Prob.engine_tail μ hEng hτ
    have hBsub : B ⊆ {f | τ ≤ Prob.cd A f} := by
      intro ω hω
      obtain ⟨α, hαsq, hαnn, hα⟩ := h ω hω
      have hwit : τ ^ 2 ≤ Prob.sqnorm α * Prob.cdsq A ω :=
        Prob.cdsq_ge_of_witness (A := A) (x := ω) (a := α) hαnn hAne hτ hα
      have hcd : τ ^ 2 ≤ Prob.cdsq A ω := by rw [hαsq, one_mul] at hwit; exact hwit
      show τ ≤ Prob.cd A ω
      rw [Prob.cd, ← Real.sqrt_sq hτ]
      exact Real.sqrt_le_sqrt hcd
    calc (FinProb.pi μ).prob A * (FinProb.pi μ).prob B
        ≤ (FinProb.pi μ).prob A * (FinProb.pi μ).prob {f | τ ≤ Prob.cd A f} :=
          mul_le_mul_of_nonneg_left (FinProb.prob_mono (FinProb.pi μ) hBsub) (FinProb.prob_nonneg (FinProb.pi μ) A)
      _ ≤ Real.exp (-τ ^ 2 / 4) := htail
  · rw [Set.not_nonempty_iff_eq_empty.mp hAne, FinProb.prob_empty, zero_mul]
    exact (Real.exp_pos _).le

private lemma pi_two_set_certified {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (μ : ∀ i, FinProb (Ω i)) (hfull : ∀ i x, 0 < (μ i).wt x)
    (A B : Set (∀ i, Ω i)) (r : ℝ) (hr : 0 ≤ r) (s : ℕ) (hs : 1 ≤ s)
    (h : ∀ ω ∈ B, ∃ I : Finset ι, I.card ≤ s ∧
        ∀ ω' ∈ A, r ≤ ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ)) :
    (FinProb.pi μ).prob A * (FinProb.pi μ).prob B ≤ Real.exp (-r ^ 2 / (4 * (s : ℝ))) := by
  classical
  by_cases hA : A = ∅
  · rw [hA, FinProb.prob_empty, zero_mul]
    exact (Real.exp_pos _).le
  have hAne : A.Nonempty := Set.nonempty_iff_ne_empty.mpr hA
  rcases eq_or_lt_of_le hr with hr0 | hrpos
  · have hrhs : Real.exp (-r ^ 2 / (4 * (s : ℝ))) = 1 := by rw [← hr0]; norm_num
    rw [hrhs]
    exact mul_le_one₀ (FinProb.prob_le_one (FinProb.pi μ) A) (FinProb.prob_nonneg (FinProb.pi μ) B)
      (FinProb.prob_le_one (FinProb.pi μ) B)
  have hspos : 0 < (s : ℝ) := by exact_mod_cast hs
  have hsqrtpos : 0 < Real.sqrt (s : ℝ) := Real.sqrt_pos.mpr hspos
  have hwit : ∀ ω ∈ B, ∃ α : ι → ℝ, Prob.sqnorm α = 1 ∧ (∀ i, 0 ≤ α i) ∧
      ∀ ω' ∈ A, r / Real.sqrt (s : ℝ) ≤ ∑ i, α i * Prob.disag ω ω' i := by
    intro ω hω
    obtain ⟨I, hIcard, hI⟩ := h ω hω
    obtain ⟨ω0, hω0⟩ := hAne
    have hIne : I.Nonempty := by
      rcases Finset.eq_empty_or_nonempty I with he | hne
      · exfalso
        have := hI ω0 hω0
        rw [he] at this
        simp at this
        linarith
      · exact hne
    refine ⟨fun i => if i ∈ I then 1 / Real.sqrt (I.card : ℝ) else 0, unit_witness_pi hIne, ?_, ?_⟩
    · intro i; by_cases hi : i ∈ I <;> simp [hi]
    · intro ω' hω'
      have hcount : r ≤ ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) := hI ω' hω'
      have hcnt_nonneg : 0 ≤ ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) := Nat.cast_nonneg _
      have hsqrtI : 0 < Real.sqrt (I.card : ℝ) :=
        Real.sqrt_pos.mpr (by exact_mod_cast Finset.card_pos.mpr hIne)
      rw [← witness_mul_sum_pi I ω ω']
      calc r / Real.sqrt (s : ℝ)
          ≤ ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) / Real.sqrt (s : ℝ) :=
            div_le_div_of_nonneg_right hcount hsqrtpos.le
        _ ≤ ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) / Real.sqrt (I.card : ℝ) := by
            rw [div_le_div_iff₀ hsqrtpos hsqrtI]
            exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hIcard)) hcnt_nonneg
  have hfin := pi_two_set μ hfull A B (r / Real.sqrt (s : ℝ)) (div_nonneg hr hsqrtpos.le) hwit
  have hrw : -(r / Real.sqrt (s : ℝ)) ^ 2 / 4 = -r ^ 2 / (4 * (s : ℝ)) := by
    rw [div_pow, Real.sq_sqrt hspos.le]; ring
  rwa [hrw] at hfin

theorem pi_median_tail {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (μ : ∀ i, FinProb (Ω i)) (hfull : ∀ i x, 0 < (μ i).wt x)
    (X : (∀ i, Ω i) → ℝ) (c : ℝ) (hc : 1 ≤ c) (s : ℕ) (hs : 1 ≤ s)
    (Ωstar : Set (∀ i, Ω i))
    (hcert : ∀ u : ℝ, 0 < u → ∀ ω, ω ∉ Ωstar →
      ∃ I : Finset ι, I.card ≤ s ∧
        ∀ ω', ω' ∉ Ωstar →
          ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) < u / c → X ω' < X ω + u)
    {m : ℝ} (hmL : 1 / 2 ≤ (FinProb.pi μ).prob {ω | X ω ≤ m})
    (hmH : 1 / 2 ≤ (FinProb.pi μ).prob {ω | m ≤ X ω})
    (u : ℝ) (hu : 0 ≤ u) :
    (FinProb.pi μ).prob {ω | u ≤ |X ω - m|} ≤
      4 * Real.exp (-u ^ 2 / (4 * c ^ 2 * (s : ℝ))) + 4 * (FinProb.pi μ).prob Ωstar := by
  classical
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  rcases eq_or_lt_of_le hu with hu0 | hupos
  · rw [← hu0]
    have he : Real.exp (-(0 : ℝ) ^ 2 / (4 * c ^ 2 * (s : ℝ))) = 1 := by norm_num
    rw [he]
    have h1 : (FinProb.pi μ).prob {ω | (0 : ℝ) ≤ |X ω - m|} ≤ 1 := FinProb.prob_le_one _ _
    have h2 : 0 ≤ (FinProb.pi μ).prob Ωstar := FinProb.prob_nonneg _ _
    linarith
  have hExpEq : Real.exp (-(u / c) ^ 2 / (4 * (s : ℝ)))
      = Real.exp (-u ^ 2 / (4 * c ^ 2 * (s : ℝ))) := by
    congr 1
    rw [div_pow]
    field_simp
  have two_set : ∀ (L H : Set (∀ i, Ω i)), (∀ ω ∈ L, ∀ ω' ∈ H, X ω + u ≤ X ω') →
      (FinProb.pi μ).prob (H \ Ωstar) * (FinProb.pi μ).prob (L \ Ωstar)
        ≤ Real.exp (-u ^ 2 / (4 * c ^ 2 * (s : ℝ))) := by
    intro L H hLH
    have hcert' : ∀ ω ∈ L \ Ωstar, ∃ I : Finset ι, I.card ≤ s ∧
        ∀ ω' ∈ H \ Ωstar, u / c ≤ ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) := by
      intro ω hω
      have hωL : ω ∈ L := hω.1
      have hωS : ω ∉ Ωstar := hω.2
      obtain ⟨I, hIcard, hI⟩ := hcert u hupos ω hωS
      refine ⟨I, hIcard, fun ω' hω' => ?_⟩
      have hω'H : ω' ∈ H := hω'.1
      have hω'S : ω' ∉ Ωstar := hω'.2
      by_contra hcon
      have hx := hI ω' hω'S (not_le.mp hcon)
      linarith [hLH ω hωL ω' hω'H]
    have h2 := pi_two_set_certified μ hfull (H \ Ωstar) (L \ Ωstar) (u / c)
      (div_nonneg hupos.le hcpos.le) s hs hcert'
    rwa [hExpEq] at h2
  have key : ∀ (L H : Set (∀ i, Ω i)), Disjoint L H →
      (∀ ω ∈ L, ∀ ω' ∈ H, X ω + u ≤ X ω') →
      (FinProb.pi μ).prob L * (FinProb.pi μ).prob H
        ≤ Real.exp (-u ^ 2 / (4 * c ^ 2 * (s : ℝ))) + (FinProb.pi μ).prob Ωstar := by
    intro L H hdisj hLH
    have hslop := prob_mul_le_sdiff (FinProb.pi μ) L H Ωstar
    have hE := two_set L H hLH
    have hEE : (FinProb.pi μ).prob (L \ Ωstar) * (FinProb.pi μ).prob (H \ Ωstar)
        ≤ Real.exp (-u ^ 2 / (4 * c ^ 2 * (s : ℝ))) := by
      rw [mul_comm]; exact hE
    have hsum : (FinProb.pi μ).prob (L ∩ Ωstar) + (FinProb.pi μ).prob (H ∩ Ωstar)
        ≤ (FinProb.pi μ).prob Ωstar := by
      have hsub : (L ∩ Ωstar) ∪ (H ∩ Ωstar) ⊆ Ωstar := by
        rintro x (hx | hx) <;> exact hx.2
      have hinter : (L ∩ Ωstar) ∩ (H ∩ Ωstar) = ∅ := by
        rw [show (L ∩ Ωstar) ∩ (H ∩ Ωstar) = (L ∩ H) ∩ Ωstar by
              ext x; simp only [Set.mem_inter_iff]; tauto,
          Set.disjoint_iff_inter_eq_empty.mp hdisj, Set.empty_inter]
      have h := FinProb.prob_union_add_inter (FinProb.pi μ) (L ∩ Ωstar) (H ∩ Ωstar)
      rw [hinter, FinProb.prob_empty] at h
      linarith [FinProb.prob_mono (FinProb.pi μ) hsub, h]
    linarith
  have hLow : (FinProb.pi μ).prob {ω | X ω ≤ m - u}
      ≤ 2 * Real.exp (-u ^ 2 / (4 * c ^ 2 * (s : ℝ))) + 2 * (FinProb.pi μ).prob Ωstar := by
    have hdisj : Disjoint {ω | X ω ≤ m - u} {ω | m ≤ X ω} := by
      rw [Set.disjoint_left]
      intro x hx hx'
      rw [Set.mem_ofPred_eq] at hx hx'
      linarith
    have hguard : ∀ ω ∈ {ω | X ω ≤ m - u}, ∀ ω' ∈ {ω | m ≤ X ω}, X ω + u ≤ X ω' := by
      intro ω hω ω' hω'
      rw [Set.mem_ofPred_eq] at hω hω'
      linarith
    have hk := key _ _ hdisj hguard
    have h2 : (FinProb.pi μ).prob {ω | X ω ≤ m - u} * (1 / 2)
        ≤ Real.exp (-u ^ 2 / (4 * c ^ 2 * (s : ℝ))) + (FinProb.pi μ).prob Ωstar := by
      have hm := mul_le_mul_of_nonneg_left hmH (FinProb.prob_nonneg (FinProb.pi μ) {ω | X ω ≤ m - u})
      linarith
    linarith
  have hUp : (FinProb.pi μ).prob {ω | m + u ≤ X ω}
      ≤ 2 * Real.exp (-u ^ 2 / (4 * c ^ 2 * (s : ℝ))) + 2 * (FinProb.pi μ).prob Ωstar := by
    have hdisj : Disjoint {ω | X ω ≤ m} {ω | m + u ≤ X ω} := by
      rw [Set.disjoint_left]
      intro x hx hx'
      rw [Set.mem_ofPred_eq] at hx hx'
      linarith
    have hguard : ∀ ω ∈ {ω | X ω ≤ m}, ∀ ω' ∈ {ω | m + u ≤ X ω}, X ω + u ≤ X ω' := by
      intro ω hω ω' hω'
      rw [Set.mem_ofPred_eq] at hω hω'
      linarith
    have hk := key _ _ hdisj hguard
    have h2 : (FinProb.pi μ).prob {ω | m + u ≤ X ω} * (1 / 2)
        ≤ Real.exp (-u ^ 2 / (4 * c ^ 2 * (s : ℝ))) + (FinProb.pi μ).prob Ωstar := by
      have hm := mul_le_mul_of_nonneg_left hmL (FinProb.prob_nonneg (FinProb.pi μ) {ω | m + u ≤ X ω})
      linarith
    linarith
  have hsub : {ω | u ≤ |X ω - m|} ⊆ {ω | X ω ≤ m - u} ∪ {ω | m + u ≤ X ω} := by
    intro ω hω
    have h1 : u ≤ |X ω - m| := hω
    rw [Set.mem_union]
    rcases le_total (X ω - m) 0 with h | h
    · exact Or.inl (by rw [Set.mem_ofPred_eq]; rw [abs_of_nonpos h] at h1; linarith)
    · exact Or.inr (by rw [Set.mem_ofPred_eq]; rw [abs_of_nonneg h] at h1; linarith)
  calc (FinProb.pi μ).prob {ω | u ≤ |X ω - m|}
      ≤ (FinProb.pi μ).prob ({ω | X ω ≤ m - u} ∪ {ω | m + u ≤ X ω}) :=
        FinProb.prob_mono _ hsub
    _ ≤ (FinProb.pi μ).prob {ω | X ω ≤ m - u} + (FinProb.pi μ).prob {ω | m + u ≤ X ω} :=
        FinProb.prob_union_le _ _ _
    _ ≤ 4 * Real.exp (-u ^ 2 / (4 * c ^ 2 * (s : ℝ))) + 4 * (FinProb.pi μ).prob Ωstar := by
        linarith
private lemma exp_le_gamma_sum {Ω : Type*} [Fintype Ω] (ν : FinProb Ω) (Y : Ω → ℝ) {γ : ℝ}
    (hγ : 0 < γ) (K : ℕ) (hY : ∀ ω, 0 ≤ Y ω) (hYK : ∀ ω, Y ω < ((K : ℝ) + 1) * γ) :
    ν.exp Y ≤ γ * ∑ k ∈ Finset.range (K + 1), ν.prob {ω | (k : ℝ) * γ ≤ Y ω} := by
  classical
  have hpt : ∀ ω, Y ω ≤ γ * (((Finset.range (K + 1)).filter (fun k : ℕ => (k:ℝ) * γ ≤ Y ω)).card : ℝ) :=
    fun ω => BJ.layer_cake (hY ω) hγ K (hYK ω)
  have key : (∑ k ∈ Finset.range (K + 1), ν.prob {ω | (k : ℝ) * γ ≤ Y ω})
      = ∑ ω, ν.wt ω * (((Finset.range (K + 1)).filter (fun k : ℕ => (k:ℝ) * γ ≤ Y ω)).card : ℝ) := by
    rw [show (∑ k ∈ Finset.range (K + 1), ν.prob {ω | (k : ℝ) * γ ≤ Y ω})
        = ∑ k ∈ Finset.range (K + 1), ∑ ω, (if (k : ℝ) * γ ≤ Y ω then ν.wt ω else 0) by
      refine Finset.sum_congr rfl (fun k _ => prob_setOf ν _)]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    have hcard : (((Finset.range (K + 1)).filter (fun k : ℕ => (k:ℝ) * γ ≤ Y ω)).card : ℝ)
        = ∑ x ∈ Finset.range (K + 1), (if (x : ℝ) * γ ≤ Y ω then (1:ℝ) else 0) := by
      rw [Finset.card_filter]
      push_cast
      rfl
    rw [hcard]
    rw [show (∑ x ∈ Finset.range (K + 1), (if (x : ℝ) * γ ≤ Y ω then ν.wt ω else 0))
        = ∑ x ∈ Finset.range (K + 1), ν.wt ω * (if (x : ℝ) * γ ≤ Y ω then (1:ℝ) else 0) by
      refine Finset.sum_congr rfl (fun x _ => ?_)
      by_cases h : (x : ℝ) * γ ≤ Y ω <;> simp [h]]
    rw [Finset.mul_sum]
  calc ν.exp Y = ∑ ω, ν.wt ω * Y ω := rfl
    _ ≤ ∑ ω, ν.wt ω * (γ * (((Finset.range (K + 1)).filter (fun k : ℕ => (k:ℝ) * γ ≤ Y ω)).card : ℝ)) :=
        Finset.sum_le_sum (fun ω _ => mul_le_mul_of_nonneg_left (hpt ω) (ν.wt_nonneg ω))
    _ = γ * ∑ ω, ν.wt ω * (((Finset.range (K + 1)).filter (fun k : ℕ => (k:ℝ) * γ ≤ Y ω)).card : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun ω _ => by ring)
    _ = γ * ∑ k ∈ Finset.range (K + 1), ν.prob {ω | (k : ℝ) * γ ≤ Y ω} := by rw [key]

private lemma exp_step (k : ℕ) :
    Real.exp (-(((2 * k + 1 : ℕ) : ℝ)) / 4) ≤ 1 / ((k : ℝ) + 1) := by
  have hx : (0 : ℝ) ≤ (((2 * k + 1 : ℕ) : ℝ)) / 4 := by positivity
  have h1 : 1 + (((2 * k + 1 : ℕ) : ℝ)) / 4 + ((((2 * k + 1 : ℕ) : ℝ)) / 4) ^ 2 / 2
      ≤ Real.exp ((((2 * k + 1 : ℕ) : ℝ)) / 4) := by
    have h := Real.sum_le_exp_of_nonneg hx 3
    simpa [Finset.sum_range_succ] using h
  have h2 : ((k : ℝ) + 1) ≤ 1 + (((2 * k + 1 : ℕ) : ℝ)) / 4
      + ((((2 * k + 1 : ℕ) : ℝ)) / 4) ^ 2 / 2 := by
    push_cast
    nlinarith [sq_nonneg (2 * (k : ℝ) - 3)]
  have h3 : (0 : ℝ) < ((k : ℝ) + 1) := by positivity
  have h4 : (0 : ℝ) < Real.exp ((((2 * k + 1 : ℕ) : ℝ)) / 4) := Real.exp_pos _
  rw [show -(((2 * k + 1 : ℕ) : ℝ)) / 4 = -((((2 * k + 1 : ℕ) : ℝ)) / 4) by ring, Real.exp_neg,
    one_div]
  exact (inv_le_inv₀ h4 h3).mpr (by linarith)

/-- `exp (-k^2/4) <= 1/k!` — the factorial majorant of the Gaussian terms. -/
private lemma exp_sq_le_inv_factorial (k : ℕ) :
    Real.exp (-((k : ℝ) ^ 2) / 4) ≤ 1 / ((k.factorial : ℝ)) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hc1 : ((↑(k + 1) : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
      have hstep : Real.exp (-(((k : ℝ) + 1) ^ 2) / 4)
          = Real.exp (-((k : ℝ) ^ 2) / 4) * Real.exp (-(((2 * k + 1 : ℕ) : ℝ)) / 4) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring
      rw [hc1, hstep]
      have h2 : Real.exp (-(((2 * k + 1 : ℕ) : ℝ)) / 4) ≤ 1 / ((k : ℝ) + 1) := exp_step k
      have hkf : (0 : ℝ) < 1 / ((k.factorial : ℝ)) := by positivity
      have hc : (0 : ℝ) < Real.exp (-(((2 * k + 1 : ℕ) : ℝ)) / 4) := Real.exp_pos _
      calc Real.exp (-((k : ℝ) ^ 2) / 4) * Real.exp (-(((2 * k + 1 : ℕ) : ℝ)) / 4)
          ≤ (1 / ((k.factorial : ℝ))) * (1 / ((k : ℝ) + 1)) := mul_le_mul ih h2 hc.le hkf.le
        _ = 1 / (((k + 1).factorial : ℝ)) := by
            rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
            field_simp

/-- The numerical sum bound used in the layer-cake estimate. -/
private lemma exp_sum_bound_local (N : ℕ) :
    ∑ k ∈ Finset.range N, Real.exp (-((k : ℝ) ^ 2) / 4) ≤ (3 : ℝ) := by
  have h1 : ∑ k ∈ Finset.range N, Real.exp (-((k : ℝ) ^ 2) / 4)
      ≤ ∑ k ∈ Finset.range N, 1 / ((k.factorial : ℝ)) :=
    Finset.sum_le_sum (fun k _ => exp_sq_le_inv_factorial k)
  have h2 : ∑ k ∈ Finset.range N, 1 / ((k.factorial : ℝ)) ≤ Real.exp 1 := by
    have h := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 1 by norm_num) N
    simpa using h
  have h3 : Real.exp 1 ≤ 3 := le_of_lt Real.exp_one_lt_three
  linarith

private lemma exp_sub_median_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (μ : ∀ i, FinProb (Ω i)) (hfull : ∀ i x, 0 < (μ i).wt x)
    (X : (∀ i, Ω i) → ℝ) (M : ℝ) (hM : 1 ≤ M) (hsup : ∀ ω, |X ω| ≤ M)
    (c : ℝ) (hc : 1 ≤ c) (s : ℕ) (hs : 1 ≤ s) (Ωstar : Set (∀ i, Ω i))
    (hcert : ∀ u : ℝ, 0 < u → ∀ ω, ω ∉ Ωstar →
      ∃ I : Finset ι, I.card ≤ s ∧
        ∀ ω', ω' ∉ Ωstar →
          ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) < u / c → X ω' < X ω + u)
    {m : ℝ} (hmL : 1 / 2 ≤ (FinProb.pi μ).prob {ω | X ω ≤ m})
    (hmH : 1 / 2 ≤ (FinProb.pi μ).prob {ω | m ≤ X ω}) (hmabs : |m| ≤ M)
    (hexc : (FinProb.pi μ).prob Ωstar ≤ 1 / M ^ 2) :
    |(FinProb.pi μ).exp X - m| ≤ 24 * (c * Real.sqrt (s : ℝ)) := by
  classical
  set γ := c * Real.sqrt (s : ℝ) with hγdef
  have hsreal : 0 < (s : ℝ) := by exact_mod_cast hs
  have hsqrt1 : 1 ≤ Real.sqrt (s : ℝ) := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hs)
  have hγ1 : 1 ≤ γ := by
    rw [hγdef]; nlinarith [hc, hsqrt1]
  have hγpos : 0 < γ := lt_of_lt_of_le zero_lt_one hγ1
  have hγsq : γ ^ 2 = c ^ 2 * (s : ℝ) := by
    rw [hγdef, mul_pow, Real.sq_sqrt hsreal.le]
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  set K := ⌊2 * M / γ⌋₊ with hKdef
  have hKlt : 2 * M < ((K : ℝ) + 1) * γ := by
    have h1 := Nat.lt_floor_add_one (2 * M / γ)
    have h2 := mul_lt_mul_of_pos_right h1 hγpos
    rw [div_mul_cancel₀ _ (ne_of_gt hγpos)] at h2
    simpa [hKdef] using h2
  have hσnn : 0 ≤ (FinProb.pi μ).prob Ωstar := FinProb.prob_nonneg _ _
  have hEY : (FinProb.pi μ).exp (fun ω => |X ω - m|) ≤ 24 * γ := by
    have hYnn : ∀ ω, 0 ≤ |X ω - m| := fun ω => abs_nonneg _
    have hYK : ∀ ω, |X ω - m| < ((K : ℝ) + 1) * γ := by
      intro ω
      have h2M : |X ω - m| ≤ 2 * M := by
        calc |X ω - m| ≤ |X ω| + |m| := abs_sub _ _
          _ ≤ M + M := add_le_add (hsup ω) hmabs
          _ = 2 * M := by ring
      linarith
    have hlayer := exp_le_gamma_sum (FinProb.pi μ) (fun ω => |X ω - m|) hγpos K hYnn hYK
    have hterm : ∀ k ∈ Finset.range (K + 1),
        (FinProb.pi μ).prob {ω | (k : ℝ) * γ ≤ |X ω - m|}
          ≤ 4 * Real.exp (-((k : ℝ) ^ 2) / 4) + 4 * (FinProb.pi μ).prob Ωstar := by
      intro k hk
      have hu : 0 ≤ (k : ℝ) * γ := mul_nonneg (Nat.cast_nonneg k) hγpos.le
      have hmed := pi_median_tail μ hfull X c hc s hs Ωstar hcert hmL hmH ((k : ℝ) * γ) hu
      have hexp' : -((k : ℝ) * γ) ^ 2 / (4 * c ^ 2 * (s : ℝ)) = -((k : ℝ) ^ 2) / 4 := by
        rw [mul_pow, hγsq]
        field_simp
      rwa [hexp'] at hmed
    have hsumle : (∑ k ∈ Finset.range (K + 1), (FinProb.pi μ).prob {ω | (k : ℝ) * γ ≤ |X ω - m|})
        ≤ 4 * (∑ k ∈ Finset.range (K + 1), Real.exp (-((k : ℝ) ^ 2) / 4))
          + 4 * ((K : ℝ) + 1) * (FinProb.pi μ).prob Ωstar := by
      calc (∑ k ∈ Finset.range (K + 1), (FinProb.pi μ).prob {ω | (k : ℝ) * γ ≤ |X ω - m|})
          ≤ ∑ k ∈ Finset.range (K + 1),
              (4 * Real.exp (-((k : ℝ) ^ 2) / 4) + 4 * (FinProb.pi μ).prob Ωstar) :=
            Finset.sum_le_sum hterm
        _ = 4 * (∑ k ∈ Finset.range (K + 1), Real.exp (-((k : ℝ) ^ 2) / 4))
              + 4 * (K + 1) * (FinProb.pi μ).prob Ωstar := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_const, Finset.card_range,
                nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
            ring
    have hS : (∑ k ∈ Finset.range (K + 1), Real.exp (-((k : ℝ) ^ 2) / 4)) ≤ 3 :=
      exp_sum_bound_local (K + 1)
    have hKbound : ((K : ℝ) + 1) * γ ≤ 2 * M + γ := by
      have h1 : (K : ℝ) ≤ 2 * M / γ := Nat.floor_le (by positivity)
      have h2 := mul_le_mul_of_nonneg_right h1 hγpos.le
      rw [div_mul_cancel₀ _ (ne_of_gt hγpos)] at h2
      nlinarith
    have hσterm : 4 * γ * (FinProb.pi μ).prob Ωstar * ((K : ℝ) + 1) ≤ 12 * γ := by
      have h1 : 4 * γ * (FinProb.pi μ).prob Ωstar * ((K : ℝ) + 1)
          = 4 * (FinProb.pi μ).prob Ωstar * (((K : ℝ) + 1) * γ) := by ring
      rw [h1]
      have h2 : 4 * (FinProb.pi μ).prob Ωstar * (((K : ℝ) + 1) * γ)
          ≤ 4 * (FinProb.pi μ).prob Ωstar * (2 * M + γ) :=
        mul_le_mul_of_nonneg_left hKbound (by positivity)
      have h3 : 4 * (FinProb.pi μ).prob Ωstar * (2 * M + γ) ≤ 12 * γ := by
        have hMinv : 1 / M ≤ 1 := by rw [div_le_one hMpos]; exact hM
        have hMinvγ : 1 / M ≤ γ := le_trans hMinv hγ1
        have hMinvM : 1 / M ^ 2 ≤ 1 / M := by
          rw [one_div, one_div, inv_le_inv₀ (by positivity) hMpos]
          nlinarith
        have hMsig : M * (FinProb.pi μ).prob Ωstar ≤ 1 / M := by
          have h := mul_le_mul_of_nonneg_left hexc hMpos.le
          have he : M * (1 / M ^ 2) = 1 / M := by field_simp
          linarith
        nlinarith [hMinvM, hMsig, hσnn, hMpos, hγpos, hγ1]
      linarith
    calc (FinProb.pi μ).exp (fun ω => |X ω - m|)
        ≤ γ * (∑ k ∈ Finset.range (K + 1), (FinProb.pi μ).prob {ω | (k : ℝ) * γ ≤ |X ω - m|}) := hlayer
      _ ≤ γ * (4 * (∑ k ∈ Finset.range (K + 1), Real.exp (-((k : ℝ) ^ 2) / 4))
              + 4 * ((K : ℝ) + 1) * (FinProb.pi μ).prob Ωstar) :=
            mul_le_mul_of_nonneg_left hsumle hγpos.le
      _ ≤ 24 * γ := by
            have h4 : γ * (4 * (∑ k ∈ Finset.range (K + 1), Real.exp (-((k : ℝ) ^ 2) / 4))
                + 4 * ((K : ℝ) + 1) * (FinProb.pi μ).prob Ωstar)
                = 4 * γ * (∑ k ∈ Finset.range (K + 1), Real.exp (-((k : ℝ) ^ 2) / 4))
                  + 4 * γ * (FinProb.pi μ).prob Ωstar * ((K : ℝ) + 1) := by ring
            rw [h4]
            have h5 : 4 * γ * (∑ k ∈ Finset.range (K + 1), Real.exp (-((k : ℝ) ^ 2) / 4)) ≤ 4 * γ * 3 :=
              mul_le_mul_of_nonneg_left hS (by positivity)
            linarith
  have hfin : |(FinProb.pi μ).exp X - m| ≤ (FinProb.pi μ).exp (fun ω => |X ω - m|) := by
    have h1 : (FinProb.pi μ).exp (fun ω => X ω - m) = (FinProb.pi μ).exp X - m := by
      rw [FinProb.exp_sub, FinProb.exp_const]
    have h2 := abs_exp_le (FinProb.pi μ) (fun ω => X ω - m)
    rw [h1] at h2
    exact h2
  calc |(FinProb.pi μ).exp X - m| ≤ (FinProb.pi μ).exp (fun ω => |X ω - m|) := hfin
    _ ≤ 24 * γ := hEY
    _ = 24 * (c * Real.sqrt (s : ℝ)) := by rw [hγdef]

private theorem bj_talagrand_core {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (μ : ∀ i, FinProb (Ω i)) (hfull : ∀ i x, 0 < (μ i).wt x)
    (X : (∀ i, Ω i) → ℝ) (M : ℝ) (hM : 1 ≤ M) (hsup : ∀ ω, |X ω| ≤ M)
    (c : ℝ) (hc : 1 ≤ c) (s : ℕ) (hs : 1 ≤ s)
    (Ωstar : Set (∀ i, Ω i))
    (hexc : (FinProb.pi μ).prob Ωstar ≤ 1 / M ^ 2)
    (hcert : ∀ u : ℝ, 0 < u → ∀ ω, ω ∉ Ωstar →
      ∃ I : Finset ι, I.card ≤ s ∧
        ∀ ω', ω' ∉ Ωstar →
          ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) < u / c → X ω' < X ω + u)
    {m : ℝ} (hmem : m ∈ Finset.univ.image X)
    (hmL : 1 / 2 ≤ (FinProb.pi μ).prob {ω | X ω ≤ m})
    (hmH : 1 / 2 ≤ (FinProb.pi μ).prob {ω | m ≤ X ω}) :
    ∀ t : ℝ, 50 * c * Real.sqrt (s : ℝ) < t →
      (FinProb.pi μ).prob {ω | t ≤ |X ω - (FinProb.pi μ).exp X|}
        ≤ 4 * Real.exp (- t ^ 2 / (16 * c ^ 2 * (s : ℝ))) + 4 * (FinProb.pi μ).prob Ωstar := by
  intro t ht
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hsqrt1 : 1 ≤ Real.sqrt (s : ℝ) := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt (by exact_mod_cast hs)
  have hγpos : 0 < c * Real.sqrt (s : ℝ) := mul_pos hcpos (lt_of_lt_of_le zero_lt_one hsqrt1)
  have hbase : 0 < 50 * c * Real.sqrt (s : ℝ) := by positivity
  have htpos : 0 < t := lt_of_lt_of_le hbase ht.le
  have hmabs : |m| ≤ M := by
    obtain ⟨ω, -, hω⟩ := Finset.mem_image.mp hmem
    rw [← hω]; exact hsup ω
  have hgap := exp_sub_median_le μ hfull X M hM hsup c hc s hs Ωstar hcert hmL hmH hmabs hexc
  have hlt : |m - (FinProb.pi μ).exp X| < t / 2 := by
    rw [abs_sub_comm]
    linarith [hgap, ht, hγpos]
  have ht2 : 0 ≤ t / 2 := by linarith
  have hmedtail := pi_median_tail μ hfull X c hc s hs Ωstar hcert hmL hmH (t / 2) ht2
  have hexp2 : -(t / 2) ^ 2 / (4 * c ^ 2 * (s : ℝ)) = -t ^ 2 / (16 * c ^ 2 * (s : ℝ)) := by
    field_simp
    ring
  rw [hexp2] at hmedtail
  refine le_trans (FinProb.prob_mono _ ?_) hmedtail
  intro ω hω
  rw [Set.mem_ofPred_eq] at hω ⊢
  have h1 : |X ω - (FinProb.pi μ).exp X| ≤ |X ω - m| + |m - (FinProb.pi μ).exp X| :=
    abs_sub_le _ _ _
  linarith

/-- **Bruhn--Joos: concentration from certificates, for a general
full-support product measure.**  If `X : ∏ i, Ω i → ℝ` is bounded by `M ≥ 1`, and off an
exceptional set `Ωstar` of probability at most `M⁻²` it admits *`(s,c)`-certificates*
(for every outcome `ω` and every `u > 0` there is a set `I` of at most `s` coordinates such
that any non-exceptional outcome agreeing with `ω` outside all but fewer than `u/c`
coordinates of `I` satisfies `X ω' < X ω + u`), then for `t > 50 c √s` the variable `X` is
concentrated around its mean. -/
theorem bj_talagrand {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (μ : ∀ i, Work.Deep.Reed.FinProb (Ω i)) (hfull : ∀ i x, 0 < (μ i).wt x)
    (X : (∀ i, Ω i) → ℝ) (M : ℝ) (hM : 1 ≤ M) (hsup : ∀ ω, |X ω| ≤ M)
    (c : ℝ) (hc : 1 ≤ c) (s : ℕ) (hs : 1 ≤ s)
    (Ωstar : Set (∀ i, Ω i))
    (hexc : (Work.Deep.Reed.FinProb.pi μ).prob Ωstar ≤ 1 / M ^ 2)
    (hcert : ∀ u : ℝ, 0 < u → ∀ ω, ω ∉ Ωstar →
      ∃ I : Finset ι, I.card ≤ s ∧
        ∀ ω', ω' ∉ Ωstar →
          ((I.filter (fun i => ω i ≠ ω' i)).card : ℝ) < u / c → X ω' < X ω + u) :
    ∀ t : ℝ, 50 * c * Real.sqrt (s : ℝ) < t →
      (Work.Deep.Reed.FinProb.pi μ).prob {ω | t ≤ |X ω - (Work.Deep.Reed.FinProb.pi μ).exp X|}
        ≤ 4 * Real.exp (- t ^ 2 / (16 * c ^ 2 * (s : ℝ)))
          + 4 * (Work.Deep.Reed.FinProb.pi μ).prob Ωstar := by
  intro t ht
  obtain ⟨m, hmem, hmL, hmH⟩ := BJ.exists_median (FinProb.pi μ) X
  exact bj_talagrand_core μ hfull X M hM hsup c hc s hs Ωstar hexc hcert hmem hmL hmH t ht

end Work.Deep.Nibble
