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
import Submission.Work.EQ.FanTri.fan_gap_unif
import Submission.Work.EQ.FanTri.fan_split2

/-! Guidance from the project lead (the requester):

ROUTE: read Submission/Work/EQ/DESIGN.md, DESIGN_CORE.md and PAPER_PROOFS.md (the lead's full paper proofs for the sketched Rychlik steps; follow them). Defs: Submission/Work/EQ/Defs.lean + DefsCore.lean (namespace Work.EQ; do NOT edit; IsPuncturedChart now carries a scale κ). Proved UNIFORMIZATION library in this workspace (Submission.UnifMain etc.). With UnifMain imported write `open _root_.Topology`.

# fan_trichotomy: compactness of the stable fan (Rychlik Thm 7(2)(3)) (4–8k) — CORRECTED STATEMENT

**Change (2026-09-25).** Case (ii) now also gives the structure `ε(φ k) = ε₀ ++ trueˢ⁽ᵏ⁾ ++ C k`,
with:
* `s k → ∞`;
* `fan (C k) 0 = A₁`;
* `charVal (C k) = charVal ε₁` for all `k`.
`H0_structure` needs this: a diverging leading `true`-run forces `ε₀ = trueˡ`. Anything proved for
the old statement carries over.

**Proof.** `PAPER_PROOFS.md` §2:
* Case (iii) comes from the fan estimates. The number of visits costs `ϑ^{#visits}`.
* Otherwise, decompose each word into gaps (maximal `true`-runs at centre `A₁`) and excursions
  (length ≤ N'+1, at most N' of them). Take the **outermost** diverging gap.
* **Big-gap lemma**: `invBranch(true)^s ∘ c ∘ (λˢ·) → germC(μ·)` uniformly over the fan family.
  On `n`-jets the linear part is `diag(−λⁿ, λ^{n−1})`, so jets converge geometrically. Cauchy
  estimates plus the uniform bounds of `fan_estimates` then give uniform convergence on a smaller
  disc.
* `μ = 1` falls back into case (i) (`charVal_props`).

**Pitfall.** The `δ` of the statement must be taken smaller than the `fan_estimates` radius (Cauchy
loss).

**Formalisation note.** The proof below is assembled from the shared lemmas
`Work.EQ.FanTri.fan_decay` (the quantitative fan estimates), `Work.EQ.FanTri.fan_gap_unif` (the
big-gap limit, uniform in the trailing word), `Work.EQ.FanTri.fan_split2` (the combinatorial
splitting of a sequence of words with bounded visits, with a constant characteristic weight),
`Work.EQ.charVal_props`, and the local lemmas in this file. -/

namespace Work.EQ

open Complex Filter _root_.Topology
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

theorem fan_trichotomy {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℕ → List Bool, ∃ φ : ℕ → ℕ, StrictMono φ ∧
      ((∃ ε₀ : List Bool, ∀ k, Set.EqOn (fan a h (ε (φ k))) (fan a h ε₀) (Metric.ball 0 δ)) ∨
       (∃ (ε₀ ε₁ : List Bool) (s : ℕ → ℕ) (C : ℕ → List Bool),
          Tendsto s atTop atTop ∧
          (∀ k, ε (φ k) = ε₀ ++ List.replicate (s k) true ++ C k) ∧
          (∀ k, fan a h (C k) 0 = ((-1 / 2 : ℂ), (0 : ℂ)) ∧
            charVal a h (C k) = charVal a h ε₁) ∧
          fan a h ε₁ 0 = ((-1 / 2 : ℂ), (0 : ℂ)) ∧
          (charVal a h ε₁).im = 0 ∧ 0 < (charVal a h ε₁).re ∧ (charVal a h ε₁).re < 1 ∧
          TendstoUniformlyOn (fun k => fan a h (ε (φ k)))
            (fun u => fan a h ε₀ (charVal a h ε₁ * u)) atTop (Metric.ball 0 δ)) ∨
       ((∀ n : ℕ, ∀ᶠ k in atTop, n ≤ nonA1Count a h (ε (φ k))) ∧
          ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ u ∈ Metric.ball (0 : ℂ) δ,
            ‖(fan a h (ε (φ k)) u).1 - (fan a h (ε (φ k)) 0).1‖ < η ∧
            ‖(fan a h (ε (φ k)) u).2‖ < η * ‖(fan a h (ε (φ k)) u).1 - ((a / 2 : ℝ) : ℂ)‖)) := by
  obtain ⟨δ₁, Q, hδ₁, hQ, hest⟩ := FanTri.fan_decay ha0 ha1 hh
  obtain ⟨δ₂, hδ₂, hgap⟩ := FanTri.fan_gap_unif ha0 ha1 hh
  obtain ⟨δ₃, hδ₃, hprops, -⟩ := charVal_props ha0 ha1 hh
  obtain ⟨-, -, -, δ₄, hδ₄, hinv₄⟩ := germC_diff_at_zero ha0 ha1 hh
  have hϑ0 : 0 < fanTh a := fanTh_pos ha0 ha1
  have hϑ1 : fanTh a < 1 := fanTh_lt_one ha0 ha1
  have h1a : (0 : ℝ) < 1 - a := by linarith
  set δ : ℝ := min (min δ₁ (min δ₂ (min δ₃ δ₄))) ((1 - a) / (4 * Q)) with hδdef
  have hδ0 : 0 < δ := by
    rw [hδdef]
    exact lt_min (lt_min hδ₁ (lt_min hδ₂ (lt_min hδ₃ hδ₄))) (by positivity)
  have hδ₁' : δ ≤ δ₁ := by rw [hδdef]; exact le_trans (min_le_left _ _) (min_le_left _ _)
  have hδ₂' : δ ≤ δ₂ := by
    rw [hδdef]; exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ₃' : δ ≤ δ₃ := by
    rw [hδdef]
    exact le_trans (min_le_left _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδ₄' : δ ≤ δ₄ := by
    rw [hδdef]
    exact le_trans (min_le_left _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
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
        refine ⟨ε₀, ε₁, s, C, hst, hword, fun k => ⟨hC0 k, hchar k⟩, he₁0, him, hpos, hlt, ?_⟩
        have hg := hgap ε₀ s C (charVal a h ε₁) hst hC0 hchar
        have heq : (fun k => fan a h (ε₀ ++ List.replicate (s k) true ++ C k))
            = fun k => fan a h (ε (φ k)) := by
          funext k
          rw [hword k]
        rw [heq] at hg
        exact hg.mono (fun x hx => by
          rw [Metric.mem_ball, dist_zero_right] at hx ⊢
          exact lt_of_lt_of_le hx hδ₂')
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

end Work.EQ
