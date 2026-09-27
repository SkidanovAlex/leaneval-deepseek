import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.FanDefs
import Submission.Work.EQ.germCHelpers
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.charValDefs
import Submission.Work.EQ.charVal_aux
import Submission.Work.EQ.walk_bounds
import Submission.Work.EQ.charVal_main
import Submission.Work.EQ.charVal_props
import Submission.Work.EQ.fan_step_deriv
import Submission.Work.EQ.walk_count
import Submission.Work.EQ.SqrtNearOne
import Submission.Work.EQ.FanSep.Defs
import Submission.Work.EQ.FanSep.axis_walk
import Submission.Work.EQ.FanSep.centre_numbers
import Submission.Work.EQ.FanSep.germ_lip
import Submission.Work.EQ.FanSep.step_x
import Submission.Work.EQ.FanSep.step_w
import Submission.Work.EQ.FanTri.Base
import Submission.Work.EQ.FanTri.fan_decay
import Submission.Work.EQ.FanTri.fan_split2

/-! Provenance note: this file is the statement `Work.EQ.LaTB.la_fan_trichotomy`, a copy of
`Work.EQ.fan_trichotomy` (file `Submission/Work/EQ/fan_trichotomy.lean`) in which the case-(ii)
alternative no longer asserts a `TendstoUniformlyOn` conjunct.  Consequently the proof below is
the proof of `fan_trichotomy` with exactly the `fan_gap_unif`-dependent final step of the
case-(ii) branch removed, and with the corresponding `δ₂` dropped from the `min` defining `δ`.

The six `sorry`-free helper lemmas of `fan_trichotomy.lean` are reproduced here (in the local
namespace) so that this module does not depend on `Submission.Work.EQ.fan_trichotomy` and hence
not on the `sorry` in `Work.EQ.FanTri.fan_gap_unif`. -/

namespace Work.EQ.LaTB

open Work.EQ Complex Filter _root_.Topology
open scoped BigOperators

noncomputable section

lemma charVal_eq_sgnAux {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) (ε : List Bool) :
    charVal a h ε = (sgnAux a ε.reverse 0 : ℂ) := by
  rw [charVal_eq_rprod ha0 ha1 hh ε, rprod_eq_sgnAux]

lemma fan_centre_of_ret {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {C : List Bool} (hC : stAux C.reverse 0 = 0) :
    fan a h C 0 = ((-1 / 2 : ℂ), (0 : ℂ)) := by
  rw [fan_centre_walk ha0 ha1 hh, hC]
  simp [stCtr, stIdx]

lemma norm_eqLam_pow_mul_le {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (n : ℕ) (v : ℂ) :
    ‖(eqLam a : ℂ) ^ n * v‖ ≤ ‖v‖ := by
  have hl0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hl1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  rw [norm_mul, norm_pow]
  have h4 : ‖((eqLam a : ℝ) : ℂ)‖ = eqLam a := by
    rw [Complex.norm_def, Complex.normSq_ofReal, ← sq, Real.sqrt_sq hl0.le]
  rw [h4]
  exact mul_le_of_le_one_left (norm_nonneg v) (pow_le_one₀ hl0.le hl1.le)

/-- The unbounded-visit subsequence. -/
lemma exists_fVis_subseq (ε : ℕ → List Bool)
    (hbdd : ¬ ∃ N : ℕ, ∀ k, fVis (ε k) ≤ N) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ k, k + 1 ≤ fVis (ε (φ k)) := by
  classical
  have hex : ∀ (N m : ℕ), ∃ k : ℕ, m < k ∧ N < fVis (ε k) := by
    intro N m
    by_contra hcon
    push_neg at hcon
    refine hbdd ⟨max N ((Finset.range (m + 1)).sup (fun k => fVis (ε k))), ?_⟩
    intro k
    by_cases hk : k ≤ m
    · refine le_trans (Finset.le_sup (f := fun k => fVis (ε k))
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))) (le_max_right N _)
    · exact le_trans (hcon k (by omega)) (le_max_left _ _)
  let g : ℕ → ℕ := fun m => Classical.choose (hex (m + 2) m)
  have gspec : ∀ m, m < g m ∧ m + 2 < fVis (ε (g m)) := fun m =>
    Classical.choose_spec (hex (m + 2) m)
  let φ : ℕ → ℕ := fun n => Nat.rec (Classical.choose (hex 1 0))
      (fun (m : ℕ) (prev : ℕ) => g prev) n
  have hstep : ∀ n, φ n < φ (n + 1) := by
    intro n
    exact (gspec (φ n)).1
  refine ⟨φ, strictMono_nat_of_lt_succ hstep, ?_⟩
  have hmono : StrictMono φ := strictMono_nat_of_lt_succ hstep
  intro n
  cases n with
  | zero =>
      have h0 : 1 < fVis (ε (φ 0)) := by
        simp only [φ]
        exact (Classical.choose_spec (hex 1 0)).2
      exact le_of_lt h0
  | succ n =>
      have h2 : φ n + 2 < fVis (ε (φ (n + 1))) := by
        simp only [φ]
        exact (gspec (φ n)).2
      have h3 : n ≤ φ n := hmono.id_le n
      omega

/-- Prepending a word does not change the fan map when the tail already equals the germ. -/
lemma fan_prepend_eq_of_germ {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {δ : ℝ}
    (w : List Bool) (hgerm : Set.EqOn (fan a h w) (germC a h) (Metric.ball 0 δ)) :
    ∀ l : List Bool, Set.EqOn (fan a h (l ++ w)) (fan a h l) (Metric.ball 0 δ) := by
  intro l
  induction l with
  | nil =>
      intro u hu
      exact hgerm hu
  | cons c l ih =>
      intro u hu
      have hmem : (eqLam a : ℂ) * u ∈ Metric.ball (0 : ℂ) δ := by
        rw [Metric.mem_ball, dist_zero_right] at hu ⊢
        refine lt_of_le_of_lt ?_ hu
        simpa using norm_eqLam_pow_mul_le ha0 ha1 1 u
      show fan a h (c :: (l ++ w)) u = fan a h (c :: l) u
      rw [fan, fan, ih hmem]

/-- Prepending stationary principal steps to a germ-equal tail keeps it germ-equal. -/
lemma fan_true_prepend_eq_germ {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {δ : ℝ}
    {C : List Bool} (hgerm : Set.EqOn (fan a h C) (germC a h) (Metric.ball 0 δ))
    (hinv : ∀ u : ℂ, u ∈ Metric.ball 0 δ →
      invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u) :
    ∀ n : ℕ, Set.EqOn (fan a h (List.replicate n true ++ C)) (germC a h) (Metric.ball 0 δ) := by
  intro n
  induction n with
  | zero => simpa using hgerm
  | succ n ih =>
      intro u hu
      have hmem : (eqLam a : ℂ) * u ∈ Metric.ball (0 : ℂ) δ := by
        rw [Metric.mem_ball, dist_zero_right] at hu ⊢
        refine lt_of_le_of_lt ?_ hu
        simpa using norm_eqLam_pow_mul_le ha0 ha1 1 u
      show fan a h (true :: (List.replicate n true ++ C)) u = germC a h u
      rw [fan, ih hmem, hinv u hu]

/-- **Rychlik's fan trichotomy (as `Work.EQ.fan_trichotomy`), with the uniform-convergence
conjunct of the case-(ii) branch removed.**

This is a copy of the theorem `Work.EQ.fan_trichotomy` (file
`Submission/Work/EQ/fan_trichotomy.lean`) in a fresh namespace, with one change: the
case-(ii) alternative does *not* assert `TendstoUniformlyOn (fun k => fan (ε (φ k))) (fun u =>
fan ε₀ (charVal ε₁ * u)) atTop (ball 0 δ)`.  It therefore does **not** need
`Work.EQ.FanTri.fan_gap_unif` (whose proof still carries a `sorry`).

Provenance (please copy, do not reinvent): the proof in `fan_trichotomy.lean` proves the
bounded-`fVis` branch by `FanTri.fan_split2` (giving either literally constant words, or the
shape `ε₀ ++ true^s ++ C` with `charVal (C k) = charVal ε₁` and `re < 1`), and the unbounded
branch by `FanTri.fan_decay` (giving the shrinking case).  The only use of `fan_gap_unif` in
that proof is the final step of the case-(ii) branch deriving the `TendstoUniformlyOn` conjunct;
delete exactly those lines (the `have hg := hgap ...` step and everything after it, keeping the
`refine ⟨ε₀, ε₁, s, C, hst, hword, fun k => ⟨hC0 k, hchar k⟩, he₁0, him, hpos, hlt⟩`), and drop
the now-unused `δ₂` from the `min`.  The helpers `Work.EQ.charVal_eq_sgnAux`,
`Work.EQ.fan_centre_of_ret`, `Work.EQ.norm_eqLam_pow_mul_le`, `Work.EQ.exists_fVis_subseq`,
`Work.EQ.fan_prepend_eq_of_germ`, `Work.EQ.fan_true_prepend_eq_germ` in `fan_trichotomy.lean`
are yours to use (they are `sorry`-free); do **not** use `Work.EQ.fan_trichotomy` itself (it
depends on the `sorry` in `fan_gap_unif`). -/
theorem la_fan_trichotomy {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : Work.EQ.IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℕ → List Bool, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ ε₀ : List Bool, ∀ k, Set.EqOn (Work.EQ.fan a h (ε (φ k))) (Work.EQ.fan a h ε₀)
          (Metric.ball 0 δ)) ∨
       (∃ (ε₀ ε₁ : List Bool) (s : ℕ → ℕ) (C : ℕ → List Bool),
          Filter.Tendsto s Filter.atTop Filter.atTop ∧
          (∀ k, ε (φ k) = ε₀ ++ List.replicate (s k) true ++ C k) ∧
          (∀ k, Work.EQ.fan a h (C k) 0 = ((-1 / 2 : ℂ), (0 : ℂ)) ∧
            Work.EQ.charVal a h (C k) = Work.EQ.charVal a h ε₁) ∧
          Work.EQ.fan a h ε₁ 0 = ((-1 / 2 : ℂ), (0 : ℂ)) ∧
          (Work.EQ.charVal a h ε₁).im = 0 ∧ 0 < (Work.EQ.charVal a h ε₁).re ∧
          (Work.EQ.charVal a h ε₁).re < 1) ∨
       ((∀ n : ℕ, ∀ᶠ k in Filter.atTop, n ≤ Work.EQ.nonA1Count a h (ε (φ k))) ∧
          ∀ η : ℝ, 0 < η → ∀ᶠ k in Filter.atTop, ∀ u ∈ Metric.ball (0 : ℂ) δ,
            ‖(Work.EQ.fan a h (ε (φ k)) u).1 - (Work.EQ.fan a h (ε (φ k)) 0).1‖ < η ∧
            ‖(Work.EQ.fan a h (ε (φ k)) u).2‖ < η *
              ‖(Work.EQ.fan a h (ε (φ k)) u).1 - ((a / 2 : ℝ) : ℂ)‖)) := by
  obtain ⟨δ₁, Q, hδ₁, hQ, hest⟩ := FanTri.fan_decay ha0 ha1 hh
  obtain ⟨δ₃, hδ₃, hprops, -⟩ := charVal_props ha0 ha1 hh
  obtain ⟨-, -, -, δ₄, hδ₄, hinv₄⟩ := germC_diff_at_zero ha0 ha1 hh
  have hϑ0 : 0 < fanTh a := fanTh_pos ha0 ha1
  have hϑ1 : fanTh a < 1 := fanTh_lt_one ha0 ha1
  have h1a : (0 : ℝ) < 1 - a := by linarith
  set δ : ℝ := min (min δ₁ (min δ₃ δ₄)) ((1 - a) / (4 * Q)) with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min hδ₁ (lt_min hδ₃ hδ₄)) (by positivity)
  have hδ₁' : δ ≤ δ₁ := by rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ₃' : δ ≤ δ₃ := by
    rw [hδdef]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ₄' : δ ≤ δ₄ := by
    rw [hδdef]
    exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  have hδQ : δ ≤ (1 - a) / (4 * Q) := by rw [hδdef]; exact min_le_right _ _
  have hQδ : Q * δ ≤ (1 - a) / 4 := by
    have h := mul_le_mul_of_nonneg_left hδQ (le_of_lt hQ)
    have h2 : Q * ((1 - a) / (4 * Q)) = (1 - a) / 4 := by field_simp
    rwa [h2] at h
  refine ⟨δ, hδ0, ?_⟩
  intro ε
  by_cases hbdd : ∃ N : ℕ, ∀ k, fVis (ε k) ≤ N
  · obtain ⟨N, hN⟩ := hbdd
    obtain ⟨φ, hφmono, hsplit⟩ := FanTri.fan_split2 ha0 ha1 ε N hN
    refine ⟨φ, hφmono, ?_⟩
    rcases hsplit with ⟨ε₀, hconst⟩ | ⟨ε₀, C, s, ε₁, hst, hword, hCret, he₁ret, hsgn⟩
    · left
      exact ⟨ε₀, fun k => by rw [hconst k]; exact fun u _ => rfl⟩
    · have hC0 : ∀ k, fan a h (C k) 0 = ((-1 / 2 : ℂ), (0 : ℂ)) :=
        fun k => fan_centre_of_ret ha0 ha1 hh (hCret k)
      have hchar : ∀ k, charVal a h (C k) = charVal a h ε₁ := by
        intro k
        rw [charVal_eq_sgnAux ha0 ha1 hh (C k), hsgn k, ← charVal_eq_sgnAux ha0 ha1 hh ε₁]
      have he₁0 : fan a h ε₁ 0 = ((-1 / 2 : ℂ), (0 : ℂ)) :=
        fan_centre_of_ret ha0 ha1 hh he₁ret
      by_cases hmu1 : charVal a h ε₁ = 1
      · left
        refine ⟨ε₀, fun k => ?_⟩
        have hger : Set.EqOn (fan a h (C k)) (germC a h) (Metric.ball 0 δ) := fun u hu =>
          (hprops (C k) (hC0 k)).2.2.2 (by rw [hchar k]; exact hmu1)
            (lt_of_lt_of_le hu hδ₃')
        have hinv' : ∀ u : ℂ, u ∈ Metric.ball 0 δ →
            invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u :=
          fun u hu => hinv₄ u (lt_of_lt_of_le hu hδ₄')
        have htail := fan_true_prepend_eq_germ ha0 ha1 (C := C k) hger hinv' (s k)
        have hmain := fan_prepend_eq_of_germ ha0 ha1 (w := List.replicate (s k) true ++ C k)
          htail ε₀
        intro u hu
        rw [hword k, List.append_assoc]
        exact hmain hu
      · right; left
        obtain ⟨him, hpos, hle, -⟩ := hprops ε₁ he₁0
        have hre : (charVal a h ε₁).re ≠ 1 := by
          intro hcon
          exact hmu1 (by
            apply Complex.ext
            · simpa using hcon
            · simpa using him)
        have hlt : (charVal a h ε₁).re < 1 := lt_of_le_of_ne hle hre
        exact ⟨ε₀, ε₁, s, C, hst, hword, fun k => ⟨hC0 k, hchar k⟩, he₁0, him, hpos, hlt⟩
  · obtain ⟨φ, hφmono, hφfvis⟩ := exists_fVis_subseq ε hbdd
    refine ⟨φ, hφmono, Or.inr (Or.inr ?_)⟩
    refine ⟨?_, ?_⟩
    · intro n
      filter_upwards [Filter.eventually_ge_atTop n] with k hk
      rw [nonA1Count_eq_fVis ha0 ha1 hh]
      exact le_trans (Nat.le_succ_of_le hk) (hφfvis k)
    · intro η hη
      obtain ⟨K, hK⟩ : ∃ K : ℕ, Q * δ * fanTh a ^ K < η := by
        have hpos : 0 < η / (Q * δ) := by positivity
        obtain ⟨K, hK⟩ := exists_pow_lt_of_lt_one hpos hϑ1
        refine ⟨K, ?_⟩
        rw [lt_div_iff₀ (by positivity : (0 : ℝ) < Q * δ)] at hK
        linarith
      filter_upwards [Filter.eventually_ge_atTop K] with k hk
      intro u hu
      have hu₁ : u ∈ Metric.ball (0 : ℂ) δ₁ := lt_of_lt_of_le hu hδ₁'
      rw [Metric.mem_ball, dist_zero_right] at hu
      obtain ⟨-, hw, hx⟩ := hest (ε (φ k)) u hu₁
      have hϑle : fanTh a ^ (fVis (ε (φ k))) ≤ fanTh a ^ K :=
        pow_le_pow_of_le_one hϑ0.le hϑ1.le (le_trans (Nat.le_succ_of_le hk) (hφfvis k))
      have hbound : Q * ‖u‖ * fanTh a ^ (fVis (ε (φ k))) < η := by
        calc Q * ‖u‖ * fanTh a ^ (fVis (ε (φ k)))
            ≤ Q * δ * fanTh a ^ K := by
              have h2 : Q * ‖u‖ ≤ Q * δ := mul_le_mul_of_nonneg_left hu.le (le_of_lt hQ)
              have h3 : Q * ‖u‖ * fanTh a ^ (fVis (ε (φ k))) ≤ Q * ‖u‖ * fanTh a ^ K :=
                mul_le_mul_of_nonneg_left hϑle (by positivity)
              have h4 : Q * ‖u‖ * fanTh a ^ K ≤ Q * δ * fanTh a ^ K :=
                mul_le_mul_of_nonneg_right h2 (pow_nonneg hϑ0.le _)
              linarith
          _ < η := hK
      have hxne : (fan a h (ε (φ k)) u).1 - ((a / 2 : ℝ) : ℂ) ≠ 0 := by
        intro hcon
        have hx0 : (1 - a) / 2 ≤ ‖(fan a h (ε (φ k)) 0).1 - ((a / 2 : ℝ) : ℂ)‖ := by
          rw [fan_centre_walk ha0 ha1 hh]
          have h := ((FanSep.centre_numbers ha0 ha1).1
            (stIdx (stAux (ε (φ k)).reverse 0))).2
          simpa only [stCtr] using h
        have hxd : ‖(fan a h (ε (φ k)) u).1 - (fan a h (ε (φ k)) 0).1‖ ≤ Q * δ := by
          refine le_trans hx ?_
          have h1 : fanTh a ^ (fVis (ε (φ k))) ≤ 1 := pow_le_one₀ hϑ0.le hϑ1.le
          have h2 : Q * ‖u‖ ≤ Q * δ := mul_le_mul_of_nonneg_left hu.le (le_of_lt hQ)
          calc Q * ‖u‖ * fanTh a ^ (fVis (ε (φ k)))
              ≤ Q * ‖u‖ * 1 := mul_le_mul_of_nonneg_left h1 (by positivity)
            _ = Q * ‖u‖ := by ring
            _ ≤ Q * δ := h2
        have htri : ‖(fan a h (ε (φ k)) 0).1 - ((a / 2 : ℝ) : ℂ)‖
            ≤ ‖(fan a h (ε (φ k)) u).1 - ((a / 2 : ℝ) : ℂ)‖
              + ‖(fan a h (ε (φ k)) u).1 - (fan a h (ε (φ k)) 0).1‖ := by
          have h := norm_sub_le ((fan a h (ε (φ k)) u).1 - ((a / 2 : ℝ) : ℂ))
            ((fan a h (ε (φ k)) u).1 - (fan a h (ε (φ k)) 0).1)
          convert h using 1 <;> ring
        rw [hcon, norm_zero, zero_add] at htri
        linarith [hx0, htri, hxd, hQδ, h1a]
      have hy : (fan a h (ε (φ k)) u).2
          = wFan a h (ε (φ k)) u * ((fan a h (ε (φ k)) u).1 - ((a / 2 : ℝ) : ℂ)) := by
        rw [wFan, div_mul_cancel₀ _ hxne]
      constructor
      · exact lt_of_le_of_lt hx hbound
      · rw [hy, norm_mul]
        have hpos : 0 < ‖(fan a h (ε (φ k)) u).1 - ((a / 2 : ℝ) : ℂ)‖ :=
          norm_pos_iff.mpr hxne
        have hη : ‖wFan a h (ε (φ k)) u‖ < η := lt_of_le_of_lt hw hbound
        nlinarith [hη, hpos]

end

end Work.EQ.LaTB
