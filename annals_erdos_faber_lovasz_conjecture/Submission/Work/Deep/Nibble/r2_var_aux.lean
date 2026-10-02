import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.r2_setup
import Submission.Work.Deep.Nibble.r2_own_b
import Submission.Work.Deep.Reed.Prob.FunDepends
import Submission.Work.Deep.Reed.Prob.freeze_exp
import Submission.Work.Deep.Reed.Prob.freeze_exp_slice
import Submission.Work.Deep.Reed.Prob.pi_exp_mul_of_disjoint
import Submission.Work.Deep.Reed.Prob.freeze_exp_of_depends

/-!
# Auxiliary lemmas for `Work.Deep.Nibble.r2_var`

This module collects the definitions and estimates used in the proof of `r2_var`.

* `ssf 𝓖 v ω` is the summand of `collMult`: the number of kept edges through `v`, counted only
  when there are at least two of them.
* `kgap 𝓖 g v ω` is the number of kept edges through `v` apart from the prescribed edge `g`.

The estimates are: the exact variance of `keptF.card`, the exact second moment `E[k(k-1)]`, the
box probabilities for `kgap`, and the per-vertex and per-pair bounds feeding the variance of
`collMult`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped BigOperators

namespace Work.Deep.Nibble

open Work.Deep.Reed

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## The two random variables of the round -/

/-- The summand of `collMult`: the number of kept edges through `v`, counted only when at least
two of them are kept. -/
noncomputable def ssf (𝓖 : Set (Set V)) (v : V) (ω : 𝓖 → Bool) : ℝ :=
  ((if 2 ≤ kAtF 𝓖 ω v then kAtF 𝓖 ω v else 0 : ℕ) : ℝ)

/-- The number of kept edges through `v` apart from the prescribed edge `g`. -/
noncomputable def kgap (𝓖 : Set (Set V)) (g : 𝓖) (v : V) (ω : 𝓖 → Bool) : ℕ :=
  (((thruF 𝓖 v).erase g).filter (fun e => ω e = true)).card

lemma collMult_cast (𝓖 : Set (Set V)) (ω : 𝓖 → Bool) :
    ((collMult 𝓖 ω : ℕ) : ℝ) = ∑ v : V, ssf 𝓖 v ω := by
  rw [collMult, Nat.cast_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [kAt_eq_kAtF, ssf]

lemma ssf_dependsOn (𝓖 : Set (Set V)) (v : V) :
    Work.Deep.Nibble.DependsOnFun (thruF 𝓖 v) (ssf 𝓖 v) := by
  intro ω ω' h
  have hfil : (thruF 𝓖 v).filter (fun e => ω e = true)
      = (thruF 𝓖 v).filter (fun e => ω' e = true) := by
    refine Finset.filter_congr fun e he => ?_
    rw [h e he]
  rw [ssf, ssf, kAtF, kAtF, hfil]

lemma ssf_nonneg (𝓖 : Set (Set V)) (v : V) (ω : 𝓖 → Bool) : 0 ≤ ssf 𝓖 v ω :=
  Nat.cast_nonneg _

/-! ## The variance of a finite sum of real random variables -/

/-- The variance of a finite sum of real random variables unfolds into the double sum of
covariances. -/
theorem variance_sum {Ω ι : Type*} [Fintype Ω] [Fintype ι] (μ : FinProb Ω) (X : ι → Ω → ℝ) :
    variance μ (fun ω => ∑ i, X i ω)
      = ∑ i, ∑ j, (μ.exp (fun ω => X i ω * X j ω) - μ.exp (X i) * μ.exp (X j)) := by
  have h1 : μ.exp (fun ω => (∑ i, X i ω) ^ 2)
      = ∑ i, ∑ j, μ.exp (fun ω => X i ω * X j ω) := by
    rw [show (fun ω => (∑ i, X i ω) ^ 2) = (fun ω => ∑ i, ∑ j, X i ω * X j ω) from
      funext fun ω => by rw [pow_two, Finset.sum_mul_sum]]
    rw [FinProb.exp_sum]
    exact Finset.sum_congr rfl fun i _ => FinProb.exp_sum μ (fun j ω => X i ω * X j ω)
  have h2 : (μ.exp (fun ω => ∑ i, X i ω)) ^ 2
      = ∑ i, ∑ j, μ.exp (X i) * μ.exp (X j) := by
    rw [FinProb.exp_sum, pow_two, Finset.sum_mul_sum]
  rw [variance, h1, h2, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_sub_distrib]

/-! ## The edges as finite sets of vertices -/

lemma eFin_card (𝓖 : Set (Set V)) (e : 𝓖) : (eFin 𝓖 e).card = ((e : Set V)).ncard := by
  have h : (eFin 𝓖 e : Set V) = (e : Set V) := by
    ext x; simp
  rw [← h]
  simp

lemma eFin_card_of_hunif {𝓖 : Set (Set V)} {r : ℕ} (huni : HUnif 𝓖 r) (e : 𝓖) :
    (eFin 𝓖 e).card = r := by
  rw [eFin_card, huni (e : Set V) e.2]

/-! ## The variance of the number of kept edges -/

/-- The second moment of the indicator product of two coordinates. -/
lemma exp_ind_mul (𝓖 : Set (Set V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (e f : 𝓖) :
    (edgeMeasure 𝓖 p hp0 hp1).exp
        (fun ω => (if ω e = true then (1 : ℝ) else 0) * (if ω f = true then (1 : ℝ) else 0))
      = if e = f then p else p * p := by
  classical
  rw [show (fun ω : 𝓖 → Bool =>
        (if ω e = true then (1 : ℝ) else 0) * (if ω f = true then (1 : ℝ) else 0))
      = (fun ω => if (ω e = true ∧ ω f = true) then (1 : ℝ) else 0) from
      funext fun ω => by by_cases h1 : ω e = true <;> by_cases h2 : ω f = true <;> simp [h1, h2]]
  rw [FinProb.exp_indicator]
  by_cases hef : e = f
  · subst hef
    have hset : {ω : 𝓖 → Bool | ω e = true ∧ ω e = true} = {ω : 𝓖 → Bool | ω e = true} := by
      ext ω; simp
    rw [hset, edgeMeasure_prob_coord]
    simp
  · have hset : {ω : 𝓖 → Bool | ω e = true ∧ ω f = true}
        = {ω : 𝓖 → Bool | ∀ x ∈ ({e, f} : Finset 𝓖), ω x = (true : Bool)} := by
      ext ω
      simp only [Set.mem_setOf_eq, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨h1, h2⟩ x (rfl | rfl) <;> assumption
      · intro h
        exact ⟨h e (Or.inl rfl), h f (Or.inr rfl)⟩
    rw [hset, edgeMeasure_prob_box', if_neg hef]
    have hprod : (∏ x ∈ ({e, f} : Finset 𝓖), (if (true : Bool) = true then p else 1 - p))
        = p * p := by
      rw [Finset.prod_pair hef]
      simp
    rw [hprod]

/-- The variance of the number of kept edges is `|𝓖| p (1-p)`. -/
theorem r2_var_keptF (𝓖 : Set (Set V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    variance (edgeMeasure 𝓖 p hp0 hp1) (fun ω => ((keptF 𝓖 ω).card : ℝ))
      = (Nat.card 𝓖 : ℝ) * p * (1 - p) := by
  classical
  have hpt : ∀ ω : 𝓖 → Bool, ((keptF 𝓖 ω).card : ℝ)
      = ∑ e : 𝓖, (if ω e = true then (1 : ℝ) else 0) := by
    intro ω
    rw [keptF_card_eq_sum 𝓖 ω, Nat.cast_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    by_cases h : ω e = true <;> simp [h]
  rw [show (fun ω : 𝓖 → Bool => ((keptF 𝓖 ω).card : ℝ))
      = (fun ω => ∑ e : 𝓖, (if ω e = true then (1 : ℝ) else 0)) from funext hpt]
  rw [variance_sum]
  have hterm : ∀ e f : 𝓖,
      (edgeMeasure 𝓖 p hp0 hp1).exp
          (fun ω => (if ω e = true then (1 : ℝ) else 0) * (if ω f = true then (1 : ℝ) else 0))
        - (edgeMeasure 𝓖 p hp0 hp1).exp (fun ω => if ω e = true then (1 : ℝ) else 0)
          * (edgeMeasure 𝓖 p hp0 hp1).exp (fun ω => if ω f = true then (1 : ℝ) else 0)
      = if e = f then p * (1 - p) else 0 := by
    intro e f
    rw [exp_ind_mul 𝓖 hp0 hp1 e f, exp_coord 𝓖 hp0 hp1 e, exp_coord 𝓖 hp0 hp1 f]
    by_cases hef : e = f
    · rw [if_pos hef, if_pos hef]; ring
    · rw [if_neg hef, if_neg hef]; ring
  rw [Finset.sum_congr rfl (fun e _ => Finset.sum_congr rfl (fun f _ => hterm e f))]
  have hinner : ∀ e : 𝓖, (∑ f : 𝓖, (if e = f then p * (1 - p) else 0)) = p * (1 - p) := by
    intro e
    rw [Finset.sum_eq_single e]
    · rw [if_pos rfl]
    · intro f _ hfe
      rw [if_neg (Ne.symm hfe)]
    · intro h
      exact absurd (Finset.mem_univ e) h
  rw [Finset.sum_congr rfl (fun e _ => hinner e)]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  ring

/-! ## The degree gap when a prescribed edge is toggled -/

lemma kAtF_update_true (𝓖 : Set (Set V)) {u : V} {g : 𝓖} (hg : g ∈ thruF 𝓖 u)
    (ω : 𝓖 → Bool) :
    kAtF 𝓖 (Function.update ω g true) u = kgap 𝓖 g u ω + 1 := by
  classical
  rw [kAtF, kgap]
  have hset : (thruF 𝓖 u).filter (fun e => (Function.update ω g true) e = true)
      = insert g (((thruF 𝓖 u).erase g).filter (fun e => ω e = true)) := by
    ext e
    rw [Finset.mem_filter, Finset.mem_insert, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨heT, hev⟩
      by_cases heg : e = g
      · exact Or.inl heg
      · refine Or.inr ⟨⟨heg, heT⟩, ?_⟩
        rwa [Function.update_of_ne heg true ω] at hev
    · rintro (rfl | ⟨⟨heg, heT⟩, hev⟩)
      · exact ⟨hg, by rw [Function.update_self]⟩
      · refine ⟨heT, ?_⟩
        rw [Function.update_of_ne heg true ω]
        exact hev
  have hnotmem : g ∉ (((thruF 𝓖 u).erase g).filter (fun e => ω e = true)) := by
    intro hmem
    rw [Finset.mem_filter, Finset.mem_erase] at hmem
    exact hmem.1.1 rfl
  rw [hset, Finset.card_insert_of_notMem hnotmem]

lemma kAtF_update_false (𝓖 : Set (Set V)) {u : V} {g : 𝓖} (hg : g ∈ thruF 𝓖 u)
    (ω : 𝓖 → Bool) :
    kAtF 𝓖 (Function.update ω g false) u = kgap 𝓖 g u ω := by
  classical
  rw [kAtF, kgap]
  have hset : (thruF 𝓖 u).filter (fun e => (Function.update ω g false) e = true)
      = ((thruF 𝓖 u).erase g).filter (fun e => ω e = true) := by
    ext e
    rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨heT, hev⟩
      have heg : e ≠ g := by
        rintro rfl
        rw [Function.update_self] at hev
        exact Bool.noConfusion hev
      refine ⟨⟨heg, heT⟩, ?_⟩
      rwa [Function.update_of_ne heg false ω] at hev
    · rintro ⟨⟨heg, heT⟩, hev⟩
      refine ⟨heT, ?_⟩
      rw [Function.update_of_ne heg false ω]
      exact hev
  rw [hset]

/-- The number of preserved coordinates after removing one element. -/
lemma erase_card_add_one (𝓖 : Set (Set V)) {g : 𝓖} {u : V} (hg : g ∈ thruF 𝓖 u) :
    ((thruF 𝓖 u).erase g).card + 1 = hd 𝓖 u := by
  rw [hd_eq_card_thruF, Finset.card_erase_add_one hg]

/-! ## Box probabilities for `kgap` -/

lemma prob_kgap_zero (𝓖 : Set (Set V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u : V) (g : 𝓖) :
    (edgeMeasure 𝓖 p hp0 hp1).prob {ω : 𝓖 → Bool | kgap 𝓖 g u ω = 0}
      = (1 - p) ^ ((thruF 𝓖 u).erase g).card := by
  classical
  have hset : {ω : 𝓖 → Bool | kgap 𝓖 g u ω = 0}
      = {ω : 𝓖 → Bool | ∀ e ∈ (thruF 𝓖 u).erase g, ω e = false} := by
    ext ω
    rw [Set.mem_setOf_eq, Set.mem_setOf_eq, kgap, Finset.card_eq_zero,
      Finset.filter_eq_empty_iff]
    constructor
    · intro h e he
      cases hω : ω e <;> simp_all
    · intro h e he
      rw [h e he]
      simp
  rw [hset, edgeMeasure_prob_unkept]

lemma prob_kgap_one (𝓖 : Set (Set V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u : V) (g : 𝓖) :
    (edgeMeasure 𝓖 p hp0 hp1).prob {ω : 𝓖 → Bool | kgap 𝓖 g u ω = 1}
      = (((thruF 𝓖 u).erase g).card : ℝ) * p * (1 - p) ^ (((thruF 𝓖 u).erase g).card - 1) := by
  classical
  have hset : {ω : 𝓖 → Bool | kgap 𝓖 g u ω = 1}
      = ⋃ e ∈ (thruF 𝓖 u).erase g,
          {ω : 𝓖 → Bool | ω e = true ∧
            ∀ f ∈ ((thruF 𝓖 u).erase g).erase e, ω f = false} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · intro h
      obtain ⟨e, he⟩ := Finset.card_eq_one.mp h
      have hmem : e ∈ ((thruF 𝓖 u).erase g).filter (fun e => ω e = true) := by
        rw [he]; exact Finset.mem_singleton_self e
      obtain ⟨heS, hωe⟩ := Finset.mem_filter.mp hmem
      refine ⟨e, heS, hωe, fun f hf => ?_⟩
      by_contra hc
      have hfmem : f ∈ ((thruF 𝓖 u).erase g).filter (fun e => ω e = true) :=
        Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hf).2, by simpa using hc⟩
      rw [he] at hfmem
      exact (Finset.mem_erase.mp hf).1 (Finset.mem_singleton.mp hfmem)
    · rintro ⟨e, heS, hωe, hrest⟩
      rw [kgap]
      have hfil : ((thruF 𝓖 u).erase g).filter (fun f => ω f = true) = {e} := by
        ext f
        rw [Finset.mem_singleton]
        constructor
        · intro hf
          obtain ⟨hfS, hωf⟩ := Finset.mem_filter.mp hf
          by_contra hfe
          have h1 : ω f = false := hrest f (Finset.mem_erase.mpr ⟨hfe, hfS⟩)
          rw [h1] at hωf
          exact Bool.noConfusion hωf
        · intro hfe
          rw [hfe]
          exact Finset.mem_filter.mpr ⟨heS, hωe⟩
      rw [hfil, Finset.card_singleton]
  have hdisj : ∀ e ∈ (thruF 𝓖 u).erase g, ∀ f ∈ (thruF 𝓖 u).erase g, e ≠ f →
      Disjoint {ω : 𝓖 → Bool | ω e = true ∧
          ∀ h ∈ ((thruF 𝓖 u).erase g).erase e, ω h = false}
        {ω : 𝓖 → Bool | ω f = true ∧
          ∀ h ∈ ((thruF 𝓖 u).erase g).erase f, ω h = false} := by
    intro e he f hf hef
    rw [Set.disjoint_left]
    rintro ω ⟨hωe, hrest⟩ ⟨hωf, -⟩
    have h1 : ω f = false := hrest f (Finset.mem_erase.mpr ⟨Ne.symm hef, hf⟩)
    rw [h1] at hωf
    exact Bool.noConfusion hωf
  rw [hset, FinProb.prob_biUnion_disjoint _ _ _ hdisj]
  rw [show (∑ e ∈ (thruF 𝓖 u).erase g, (edgeMeasure 𝓖 p hp0 hp1).prob
          {ω : 𝓖 → Bool | ω e = true ∧
            ∀ f ∈ ((thruF 𝓖 u).erase g).erase e, ω f = false})
      = ∑ _e ∈ (thruF 𝓖 u).erase g,
          p * (1 - p) ^ (((thruF 𝓖 u).erase g).card - 1) from
      Finset.sum_congr rfl (fun e he => prob_box_pattern 𝓖 hp0 hp1 ((thruF 𝓖 u).erase g) e he)]
  rw [Finset.sum_const, nsmul_eq_mul]
  ring

lemma prob_kgap_ge_one (𝓖 : Set (Set V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u : V) (g : 𝓖) :
    (edgeMeasure 𝓖 p hp0 hp1).prob {ω : 𝓖 → Bool | 1 ≤ kgap 𝓖 g u ω}
      = 1 - (1 - p) ^ ((thruF 𝓖 u).erase g).card := by
  rw [show {ω : 𝓖 → Bool | 1 ≤ kgap 𝓖 g u ω}
      = {ω : 𝓖 → Bool | kgap 𝓖 g u ω = 0}ᶜ from by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff]
    omega]
  rw [FinProb.prob_compl, prob_kgap_zero]

/-- The binomial comparison behind `E[k 1[k ≥ 2]] ≤ 1`. -/
lemma pow_mul_le_pow {t : ℕ} {p : ℝ} (hle : (t : ℝ) * p ≤ 1 - p) :
    (t : ℝ) * p * (1 - p) ^ (t - 1) ≤ (1 - p) ^ t := by
  rcases Nat.eq_zero_or_pos t with h0 | hpos
  · subst h0
    simp
  · have hq : 0 ≤ 1 - p := by
      rcases le_total 0 p with hp | hp
      · have ht0 : (0 : ℝ) ≤ (t : ℝ) := Nat.cast_nonneg t
        nlinarith [hle, hp, ht0]
      · linarith
    have h1 : (1 - p) ^ t = (1 - p) ^ (t - 1) * (1 - p) := by
      rw [← pow_succ, Nat.sub_add_cancel hpos]
    calc (t : ℝ) * p * (1 - p) ^ (t - 1) ≤ (1 - p) * (1 - p) ^ (t - 1) :=
          mul_le_mul_of_nonneg_right hle (pow_nonneg hq _)
      _ = (1 - p) ^ t := by rw [h1]; ring

lemma prob_kgap_one_le_zero (𝓖 : Set (Set V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (u : V)
    (g : 𝓖) (hle : (((thruF 𝓖 u).erase g).card : ℝ) * p ≤ 1 - p) :
    (edgeMeasure 𝓖 p hp0 hp1).prob {ω : 𝓖 → Bool | kgap 𝓖 g u ω = 1}
      ≤ (edgeMeasure 𝓖 p hp0 hp1).prob {ω : 𝓖 → Bool | kgap 𝓖 g u ω = 0} := by
  rw [prob_kgap_one, prob_kgap_zero]
  exact pow_mul_le_pow hle

/-- The pure-natural-number gap formula for `ssf` when the degree increases by one. -/
lemma gap_nat (m : ℕ) :
    (((if 2 ≤ m + 1 then m + 1 else 0 : ℕ)) : ℝ) - (((if 2 ≤ m then m else 0 : ℕ)) : ℝ)
      = (if 1 ≤ m then (1 : ℝ) else 0) + (if m = 1 then (1 : ℝ) else 0) := by
  rcases m with _ | _ | n
  · norm_num
  · norm_num
  · have h1 : ¬ (n + 2 = 1) := by omega
    have h2 : 1 ≤ n + 2 := by omega
    have h3 : 2 ≤ n + 2 := by omega
    have h4 : 2 ≤ n + 2 + 1 := by omega
    simp only [h1, h2, h3, h4, if_true, if_false]
    push_cast
    ring

lemma ssf_update_gap (𝓖 : Set (Set V)) {u : V} {g : 𝓖} (hg : g ∈ thruF 𝓖 u) (ω : 𝓖 → Bool) :
    ssf 𝓖 u (Function.update ω g true) - ssf 𝓖 u (Function.update ω g false)
      = (if 1 ≤ kgap 𝓖 g u ω then (1 : ℝ) else 0)
        + (if kgap 𝓖 g u ω = 1 then (1 : ℝ) else 0) := by
  rw [ssf, ssf, kAtF_update_true 𝓖 hg ω, kAtF_update_false 𝓖 hg ω]
  exact gap_nat (kgap 𝓖 g u ω)

/-! ## Covariance through a single shared coordinate -/

/-- The frozen measure at the coordinate `g` with value `c`. -/
noncomputable def frozMeas (𝓖 : Set (Set V)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (g : 𝓖) (c : Bool) : FinProb (𝓖 → Bool) :=
  FinProb.pi (FinProb.freeze (fun _ : 𝓖 => boolProb p hp0 hp1) g c)

lemma frozMeas_slice (𝓖 : Set (Set V)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (g : 𝓖) (c : Bool)
    (Z : (𝓖 → Bool) → ℝ) :
    (frozMeas 𝓖 p hp0 hp1 g c).exp Z
      = (frozMeas 𝓖 p hp0 hp1 g c).exp (fun ω => Z (Function.update ω g c)) :=
  Work.Deep.Reed.Prob.freeze_exp_slice (fun _ : 𝓖 => boolProb p hp0 hp1) g c Z

lemma frozMeas_of_depends (𝓖 : Set (Set V)) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {g : 𝓖}
    (c : Bool) {S : Finset 𝓖} (hg : g ∉ S) {Z : (𝓖 → Bool) → ℝ}
    (hZ : Work.Deep.Reed.Prob.FunDepends S Z) :
    (frozMeas 𝓖 p hp0 hp1 g c).exp Z = (edgeMeasure 𝓖 p hp0 hp1).exp Z :=
  Work.Deep.Reed.Prob.freeze_exp_of_depends (fun _ : 𝓖 => boolProb p hp0 hp1) hg hZ c

/-- **Covariance through a single shared coordinate.**  If `X` depends only on the coordinates in
`S` and `Y` only on those in `T`, and `S ∩ T = {g}`, then the covariance of `X` and `Y` is
exactly the covariance of their slice expectations over the single coordinate `g`. -/
theorem cov_of_share_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {Ω : ι → Type*} [∀ i, Fintype (Ω i)] (ν : ∀ i, FinProb (Ω i))
    {g : ι} {S T : Finset ι} (hST : S ∩ T = {g})
    {X Y : (∀ i, Ω i) → ℝ}
    (hX : Work.Deep.Reed.Prob.FunDepends S X) (hY : Work.Deep.Reed.Prob.FunDepends T Y) :
    (FinProb.pi ν).exp (fun f => X f * Y f) - (FinProb.pi ν).exp X * (FinProb.pi ν).exp Y
      = ∑ c : Ω g, (ν g).wt c * ((FinProb.pi (FinProb.freeze ν g c)).exp X
            * (FinProb.pi (FinProb.freeze ν g c)).exp Y)
        - (∑ c : Ω g, (ν g).wt c * (FinProb.pi (FinProb.freeze ν g c)).exp X)
          * (∑ c : Ω g, (ν g).wt c * (FinProb.pi (FinProb.freeze ν g c)).exp Y) := by
  classical
  have hdepX : ∀ c : Ω g, Work.Deep.Reed.Prob.FunDepends (S.erase g)
      (fun f => X (Function.update f g c)) := by
    intro c f f' h
    refine hX _ _ ?_
    intro i hi
    by_cases hig : i = g
    · subst hig
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hig, Function.update_of_ne hig]
      exact h i (Finset.mem_erase.mpr ⟨hig, hi⟩)
  have hdepY : ∀ c : Ω g, Work.Deep.Reed.Prob.FunDepends (T.erase g)
      (fun f => Y (Function.update f g c)) := by
    intro c f f' h
    refine hY _ _ ?_
    intro i hi
    by_cases hig : i = g
    · subst hig
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne hig, Function.update_of_ne hig]
      exact h i (Finset.mem_erase.mpr ⟨hig, hi⟩)
  have hdisj : Disjoint (S.erase g) (T.erase g) := by
    rw [Finset.disjoint_left]
    intro i hiS hiT
    have h1 : i ∈ S ∩ T :=
      Finset.mem_inter.mpr ⟨(Finset.mem_erase.mp hiS).2, (Finset.mem_erase.mp hiT).2⟩
    rw [hST] at h1
    exact (Finset.mem_erase.mp hiS).1 (Finset.mem_singleton.mp h1)
  have hfac : ∀ c : Ω g, (FinProb.pi (FinProb.freeze ν g c)).exp (fun f => X f * Y f)
      = (FinProb.pi (FinProb.freeze ν g c)).exp X
        * (FinProb.pi (FinProb.freeze ν g c)).exp Y := by
    intro c
    rw [Work.Deep.Reed.Prob.freeze_exp_slice ν g c (fun f => X f * Y f),
      Work.Deep.Reed.Prob.freeze_exp_slice ν g c X,
      Work.Deep.Reed.Prob.freeze_exp_slice ν g c Y]
    exact Work.Deep.Reed.Prob.pi_exp_mul_of_disjoint _ hdisj (hdepX c) (hdepY c)
  rw [Work.Deep.Reed.Prob.freeze_exp ν g (fun f => X f * Y f),
    Work.Deep.Reed.Prob.freeze_exp ν g X, Work.Deep.Reed.Prob.freeze_exp ν g Y]
  rw [show (∑ c, (ν g).wt c * (FinProb.pi (FinProb.freeze ν g c)).exp (fun f => X f * Y f))
      = ∑ c, (ν g).wt c * ((FinProb.pi (FinProb.freeze ν g c)).exp X
            * (FinProb.pi (FinProb.freeze ν g c)).exp Y) from
    Finset.sum_congr rfl (fun c _ => by rw [hfac c])]

/-- The arithmetic of the Bool covariance. -/
lemma cov_bool_le {p a₀ a₁ b₀ b₁ : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ha0 : a₀ ≤ a₁) (ha1 : a₁ - a₀ ≤ 1) (hb0 : b₀ ≤ b₁) (hb1 : b₁ - b₀ ≤ 1) :
    p * (a₁ * b₁) + (1 - p) * (a₀ * b₀) - (p * a₁ + (1 - p) * a₀) * (p * b₁ + (1 - p) * b₀)
      ≤ p * (1 - p) := by
  have hfac : p * (a₁ * b₁) + (1 - p) * (a₀ * b₀)
        - (p * a₁ + (1 - p) * a₀) * (p * b₁ + (1 - p) * b₀)
      = p * (1 - p) * ((a₁ - a₀) * (b₁ - b₀)) := by ring
  rw [hfac]
  have h1 : 0 ≤ p * (1 - p) := by nlinarith
  have h2 : (a₁ - a₀) * (b₁ - b₀) ≤ 1 := by
    have := mul_le_mul ha1 hb1 (sub_nonneg.mpr hb0) zero_le_one
    simpa using this
  calc p * (1 - p) * ((a₁ - a₀) * (b₁ - b₀)) ≤ p * (1 - p) * 1 :=
        mul_le_mul_of_nonneg_left h2 h1
    _ = p * (1 - p) := by ring

/-! ## The edge meeting structure -/

/-- The set of edges through `u` and through `v` is a singleton when `u ≠ v`. -/
lemma inter_eq_singleton (𝓖 : Set (Set V)) (hlin : HLin 𝓖) {u v : V} (huv : u ≠ v) {g : 𝓖}
    (hgu : g ∈ thruF 𝓖 u) (hgv : g ∈ thruF 𝓖 v) :
    thruF 𝓖 u ∩ thruF 𝓖 v = {g} := by
  refine Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_inter.mpr ⟨hgu, hgv⟩, ?_⟩
  intro e he
  obtain ⟨heu, hev⟩ := Finset.mem_inter.mp he
  by_contra hne
  have h1 : u ∈ (e : Set V) := (mem_thruF (𝓖 := 𝓖)).mp heu
  have h2 : v ∈ (e : Set V) := (mem_thruF (𝓖 := 𝓖)).mp hev
  have h3 : u ∈ (g : Set V) := (mem_thruF (𝓖 := 𝓖)).mp hgu
  have h4 : v ∈ (g : Set V) := (mem_thruF (𝓖 := 𝓖)).mp hgv
  have hs : ((g : Set V) ∩ (e : Set V)).Subsingleton :=
    hlin g.2 e.2 (fun h => hne (Subtype.ext h).symm)
  exact huv (hs ⟨h3, h1⟩ ⟨h4, h2⟩)

/-! ## The gap in the frozen expectations at a vertex -/

lemma erase_card_mul_le_one_sub (𝓖 : Set (Set V)) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 2)
    {D : ℕ} (hD : 1 ≤ D) (hdeg : ∀ v : V, (hd 𝓖 v : ℝ) ≤ 2 * (D : ℝ)) {u : V} {g : 𝓖}
    (hgu : g ∈ thruF 𝓖 u) :
    (((thruF 𝓖 u).erase g).card : ℝ) * (θ / (D : ℝ)) ≤ 1 - θ / (D : ℝ) := by
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hcard : (((thruF 𝓖 u).erase g).card : ℝ) + 1 = (hd 𝓖 u : ℝ) := by
    exact_mod_cast erase_card_add_one 𝓖 hgu
  have h2 : (hd 𝓖 u : ℝ) * (θ / (D : ℝ)) ≤ 2 * θ := by
    have h3 : (hd 𝓖 u : ℝ) * (θ / (D : ℝ)) ≤ (2 * (D : ℝ)) * (θ / (D : ℝ)) :=
      mul_le_mul_of_nonneg_right (hdeg u) (div_nonneg hθ0.le hDpos.le)
    have h4 : (2 * (D : ℝ)) * (θ / (D : ℝ)) = 2 * θ := by
      field_simp
    linarith [h3, h4.symm.le, h4.le]
  nlinarith [hcard, h2, hθ1]

lemma agap_bounds (𝓖 : Set (Set V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) {u : V} {g : 𝓖}
    (hgu : g ∈ thruF 𝓖 u)
    (hle : (((thruF 𝓖 u).erase g).card : ℝ) * p ≤ 1 - p) :
    0 ≤ (frozMeas 𝓖 p hp0 hp1 g true).exp (ssf 𝓖 u)
          - (frozMeas 𝓖 p hp0 hp1 g false).exp (ssf 𝓖 u)
    ∧ (frozMeas 𝓖 p hp0 hp1 g true).exp (ssf 𝓖 u)
          - (frozMeas 𝓖 p hp0 hp1 g false).exp (ssf 𝓖 u) ≤ 1 := by
  classical
  have hsub : ∀ c : Bool, (frozMeas 𝓖 p hp0 hp1 g c).exp (ssf 𝓖 u)
      = (edgeMeasure 𝓖 p hp0 hp1).exp (fun ω => ssf 𝓖 u (Function.update ω g c)) := by
    intro c
    rw [frozMeas_slice]
    refine frozMeas_of_depends 𝓖 p hp0 hp1 c (Finset.notMem_erase g (thruF 𝓖 u)) ?_
    intro ω ω' h
    refine ssf_dependsOn 𝓖 u _ _ ?_
    intro e he
    by_cases heg : e = g
    · subst heg
      rw [Function.update_self, Function.update_self]
    · rw [Function.update_of_ne heg c ω, Function.update_of_ne heg c ω']
      exact h e (Finset.mem_erase.mpr ⟨heg, he⟩)
  have hdiff : (edgeMeasure 𝓖 p hp0 hp1).exp (fun ω => ssf 𝓖 u (Function.update ω g true))
      - (edgeMeasure 𝓖 p hp0 hp1).exp (fun ω => ssf 𝓖 u (Function.update ω g false))
      = (edgeMeasure 𝓖 p hp0 hp1).prob {ω : 𝓖 → Bool | 1 ≤ kgap 𝓖 g u ω}
        + (edgeMeasure 𝓖 p hp0 hp1).prob {ω : 𝓖 → Bool | kgap 𝓖 g u ω = 1} := by
    rw [← FinProb.exp_sub]
    rw [show (fun ω : 𝓖 → Bool => ssf 𝓖 u (Function.update ω g true)
          - ssf 𝓖 u (Function.update ω g false))
        = (fun ω => (if 1 ≤ kgap 𝓖 g u ω then (1 : ℝ) else 0)
            + (if kgap 𝓖 g u ω = 1 then (1 : ℝ) else 0)) from
      funext fun ω => ssf_update_gap 𝓖 hgu ω]
    rw [FinProb.exp_add, FinProb.exp_indicator, FinProb.exp_indicator]
  constructor
  · rw [hsub true, hsub false, hdiff]
    have h1 := (edgeMeasure 𝓖 p hp0 hp1).prob_nonneg {ω : 𝓖 → Bool | 1 ≤ kgap 𝓖 g u ω}
    have h2 := (edgeMeasure 𝓖 p hp0 hp1).prob_nonneg {ω : 𝓖 → Bool | kgap 𝓖 g u ω = 1}
    linarith
  · rw [hsub true, hsub false, hdiff, prob_kgap_ge_one, prob_kgap_one]
    have h2 := prob_kgap_one_le_zero 𝓖 hp0 hp1 u g hle
    rw [prob_kgap_one, prob_kgap_zero] at h2
    linarith

/-! ## The covariance bound for a pair of vertices sharing an edge -/

lemma cov_le_of_share (𝓖 : Set (Set V)) {r : ℕ} (hr : 2 ≤ r) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1 / 2) {D : ℕ} (hD : 1 ≤ D) (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1)
    (hlin : HLin 𝓖) (huni : HUnif 𝓖 r) (hdeg : ∀ v : V, (hd 𝓖 v : ℝ) ≤ 2 * (D : ℝ))
    {u v : V} (huv : u ≠ v) {g : 𝓖} (hgu : g ∈ thruF 𝓖 u) (hgv : g ∈ thruF 𝓖 v) :
    (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (fun ω => ssf 𝓖 u ω * ssf 𝓖 v ω)
      - (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (ssf 𝓖 u)
        * (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (ssf 𝓖 v)
      ≤ (θ / (D : ℝ)) * (1 - θ / (D : ℝ)) := by
  classical
  unfold edgeMeasure
  have hST : thruF 𝓖 u ∩ thruF 𝓖 v = {g} := inter_eq_singleton 𝓖 hlin huv hgu hgv
  have hcov := cov_of_share_one (fun _ : 𝓖 => boolProb (θ / (D : ℝ)) hp0 hp1) (g := g)
    (S := thruF 𝓖 u) (T := thruF 𝓖 v) hST (ssf_dependsOn 𝓖 u) (ssf_dependsOn 𝓖 v)
  have hleu := erase_card_mul_le_one_sub 𝓖 hθ0 hθ1 hD hdeg hgu
  have hlev := erase_card_mul_le_one_sub 𝓖 hθ0 hθ1 hD hdeg hgv
  obtain ⟨hau0, hau1⟩ := agap_bounds 𝓖 hp0 hp1 hgu hleu
  obtain ⟨hav0, hav1⟩ := agap_bounds 𝓖 hp0 hp1 hgv hlev
  rw [hcov]
  simp only [Fintype.sum_bool, boolProb_wt_true, boolProb_wt_false]
  have ha0 : (frozMeas 𝓖 (θ / (D : ℝ)) hp0 hp1 g false).exp (ssf 𝓖 u)
      ≤ (frozMeas 𝓖 (θ / (D : ℝ)) hp0 hp1 g true).exp (ssf 𝓖 u) := by linarith
  have hb0 : (frozMeas 𝓖 (θ / (D : ℝ)) hp0 hp1 g false).exp (ssf 𝓖 v)
      ≤ (frozMeas 𝓖 (θ / (D : ℝ)) hp0 hp1 g true).exp (ssf 𝓖 v) := by linarith
  exact cov_bool_le hp0 hp1 ha0 hau1 hb0 hav1

/-! ## The diagonal term: the variance of `ssf` at a single vertex -/

lemma sq_le_two_mul_pred (m : ℕ) :
    (((if 2 ≤ m then m else 0 : ℕ)) : ℝ) ^ 2 ≤ 2 * ((m : ℝ) * ((m : ℝ) - 1)) := by
  rcases m with _ | _ | n
  · norm_num
  · norm_num
  · have h : 2 ≤ n + 2 := by omega
    rw [if_pos h]
    push_cast
    have h0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [h0]

lemma exp_k_sq (𝓖 : Set (Set V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : V) :
    (edgeMeasure 𝓖 p hp0 hp1).exp (fun ω => (kAtF 𝓖 ω v : ℝ) ^ 2)
      = (hd 𝓖 v : ℝ) * p * (1 - p) + ((hd 𝓖 v : ℝ)) ^ 2 * p ^ 2 := by
  classical
  set S := thruF 𝓖 v with hS
  have hScard : (S.card : ℝ) = (hd 𝓖 v : ℝ) := by rw [hS, hd_eq_card_thruF]
  have hkind : ∀ ω : 𝓖 → Bool, (kAtF 𝓖 ω v : ℝ) = ∑ e ∈ S,
      (if ω e = true then (1 : ℝ) else 0) := by
    intro ω
    rw [kAtF_eq_sum 𝓖 ω v, hS, Nat.cast_sum]
    exact Finset.sum_congr rfl fun e _ => by by_cases h : ω e = true <;> simp [h]
  have hpt : ∀ ω : 𝓖 → Bool, (kAtF 𝓖 ω v : ℝ) ^ 2 = ∑ e ∈ S, ∑ f ∈ S,
      (if ω e = true then (1 : ℝ) else 0) * (if ω f = true then (1 : ℝ) else 0) := by
    intro ω
    rw [hkind ω, pow_two, Finset.sum_mul_sum]
  rw [show (fun ω : 𝓖 → Bool => (kAtF 𝓖 ω v : ℝ) ^ 2)
      = (fun ω => ∑ e ∈ S, ∑ f ∈ S, (if ω e = true then (1 : ℝ) else 0)
          * (if ω f = true then (1 : ℝ) else 0)) from funext hpt]
  rw [FinProb.exp_sum_finset]
  have hinner : ∀ e ∈ S, (edgeMeasure 𝓖 p hp0 hp1).exp
      (fun ω => ∑ f ∈ S, (if ω e = true then (1 : ℝ) else 0)
        * (if ω f = true then (1 : ℝ) else 0))
      = p + ((S.card : ℝ) - 1) * (p * p) := by
    intro e he
    rw [FinProb.exp_sum_finset]
    rw [Finset.sum_congr rfl (fun f _ => exp_ind_mul 𝓖 hp0 hp1 e f)]
    have hsplit : (∑ f ∈ S, (if e = f then p else p * p))
        = (∑ f ∈ S, p * p) + ∑ f ∈ S, (if e = f then p - p * p else 0) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun f _ => ?_
      by_cases h : e = f
      · rw [if_pos h, if_pos h]; ring
      · rw [if_neg h, if_neg h]; ring
    rw [hsplit, Finset.sum_ite_eq, if_pos he, Finset.sum_const, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hinner]
  rw [Finset.sum_const, nsmul_eq_mul, hScard]
  ring

lemma exp_k_mul_pred (𝓖 : Set (Set V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (v : V) :
    (edgeMeasure 𝓖 p hp0 hp1).exp
        (fun ω => (kAtF 𝓖 ω v : ℝ) * ((kAtF 𝓖 ω v : ℝ) - 1))
      = (hd 𝓖 v : ℝ) * ((hd 𝓖 v : ℝ) - 1) * p ^ 2 := by
  have hpt : (fun ω : 𝓖 → Bool => (kAtF 𝓖 ω v : ℝ) * ((kAtF 𝓖 ω v : ℝ) - 1))
      = (fun ω => (kAtF 𝓖 ω v : ℝ) ^ 2 - (kAtF 𝓖 ω v : ℝ)) := by
    funext ω; ring
  rw [hpt, FinProb.exp_sub, exp_k_sq 𝓖 hp0 hp1 v, (r2_exp_basic 𝓖 hp0 hp1).2.2.1 v]
  ring

theorem cov_self_le (𝓖 : Set (Set V)) {r : ℕ} (hr : 2 ≤ r) {θ : ℝ} (hθ0 : 0 < θ)
    (hθ1 : θ ≤ 1 / 2) {D : ℕ} (hD : 1 ≤ D) (hp0 : 0 ≤ θ / (D : ℝ)) (hp1 : θ / (D : ℝ) ≤ 1)
    (hlin : HLin 𝓖) (huni : HUnif 𝓖 r) (hdeg : ∀ v : V, (hd 𝓖 v : ℝ) ≤ 2 * (D : ℝ)) (u : V) :
    (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp
        (fun ω => ssf 𝓖 u ω * ssf 𝓖 u ω)
      - (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (ssf 𝓖 u)
        * (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (ssf 𝓖 u)
      ≤ 8 * θ ^ 2 := by
  classical
  have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast hD
  have hsq : ∀ ω : 𝓖 → Bool, ssf 𝓖 u ω * ssf 𝓖 u ω
      ≤ 2 * ((kAtF 𝓖 ω u : ℝ) * ((kAtF 𝓖 ω u : ℝ) - 1)) := by
    intro ω
    rw [← sq]
    exact sq_le_two_mul_pred (kAtF 𝓖 ω u)
  have hmono : (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp
        (fun ω => ssf 𝓖 u ω * ssf 𝓖 u ω)
      ≤ 2 * ((hd 𝓖 u : ℝ) * ((hd 𝓖 u : ℝ) - 1) * (θ / (D : ℝ)) ^ 2) := by
    have h := FinProb.exp_mono (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1) hsq
    rw [FinProb.exp_mul_left, exp_k_mul_pred 𝓖 hp0 hp1 u] at h
    exact h
  have harith : 2 * ((hd 𝓖 u : ℝ) * ((hd 𝓖 u : ℝ) - 1) * (θ / (D : ℝ)) ^ 2) ≤ 8 * θ ^ 2 := by
    have hdu : (hd 𝓖 u : ℝ) ≤ 2 * (D : ℝ) := hdeg u
    have h0 : (0 : ℝ) ≤ (hd 𝓖 u : ℝ) := Nat.cast_nonneg _
    have hp2 : 0 ≤ (θ / (D : ℝ)) ^ 2 := sq_nonneg _
    have h1 : (hd 𝓖 u : ℝ) * ((hd 𝓖 u : ℝ) - 1) ≤ (2 * (D : ℝ)) ^ 2 := by nlinarith [hdu, h0]
    have h2 : (2 * (D : ℝ)) ^ 2 * (θ / (D : ℝ)) ^ 2 = 4 * θ ^ 2 := by
      rw [mul_pow, div_pow]
      field_simp
      ring
    have h3 : (hd 𝓖 u : ℝ) * ((hd 𝓖 u : ℝ) - 1) * (θ / (D : ℝ)) ^ 2
        ≤ (2 * (D : ℝ)) ^ 2 * (θ / (D : ℝ)) ^ 2 := mul_le_mul_of_nonneg_right h1 hp2
    calc 2 * ((hd 𝓖 u : ℝ) * ((hd 𝓖 u : ℝ) - 1) * (θ / (D : ℝ)) ^ 2)
        ≤ 2 * ((2 * (D : ℝ)) ^ 2 * (θ / (D : ℝ)) ^ 2) := by linarith
      _ = 2 * (4 * θ ^ 2) := by rw [h2]
      _ = 8 * θ ^ 2 := by ring
  have hexp : 0 ≤ (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (ssf 𝓖 u) :=
    FinProb.exp_nonneg _ fun ω => ssf_nonneg 𝓖 u ω
  have hgoal : (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp
        (fun ω => ssf 𝓖 u ω * ssf 𝓖 u ω)
      - (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (ssf 𝓖 u)
        * (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (ssf 𝓖 u)
      = (edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp
          (fun ω => ssf 𝓖 u ω * ssf 𝓖 u ω)
        - ((edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (ssf 𝓖 u)) ^ 2 := by
    rw [sq]
  rw [hgoal]
  nlinarith [hmono, harith, sq_nonneg ((edgeMeasure 𝓖 (θ / (D : ℝ)) hp0 hp1).exp (ssf 𝓖 u))]

/-! ## The diagonal-free case of the pairwise covariance -/

lemma cov_eq_zero_of_disjoint (𝓖 : Set (Set V)) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {u v : V} (hdisj : Disjoint (thruF 𝓖 u) (thruF 𝓖 v)) :
    (edgeMeasure 𝓖 p hp0 hp1).exp (fun ω => ssf 𝓖 u ω * ssf 𝓖 v ω)
      - (edgeMeasure 𝓖 p hp0 hp1).exp (ssf 𝓖 u)
        * (edgeMeasure 𝓖 p hp0 hp1).exp (ssf 𝓖 v) = 0 := by
  rw [show (edgeMeasure 𝓖 p hp0 hp1).exp (fun ω => ssf 𝓖 u ω * ssf 𝓖 v ω)
      = (edgeMeasure 𝓖 p hp0 hp1).exp (ssf 𝓖 u)
        * (edgeMeasure 𝓖 p hp0 hp1).exp (ssf 𝓖 v) from ?_]
  · ring
  · exact Work.Deep.Reed.Prob.pi_exp_mul_of_disjoint (fun _ : 𝓖 => boolProb p hp0 hp1)
      hdisj (ssf_dependsOn 𝓖 u) (ssf_dependsOn 𝓖 v)

end Work.Deep.Nibble
