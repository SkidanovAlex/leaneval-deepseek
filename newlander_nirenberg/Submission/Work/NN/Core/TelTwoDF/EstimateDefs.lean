/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The tracking polydiscs of the parameterised `(0,2)`-telescoping

`Work.NN.Core.TelTwoDF.E G m` (`Submission/Work/NN/Core/TelTwoDF/Rec2.lean`) is the region on
which the stage-`m` data of the parameterised recursion are tracked: the coordinates `k < m`
already processed lie in the solving polydisc `|z k| < G.e k`, the others only in the support
polydisc `|z k| < G.b k`.

This file records that `E G m` is the polydisc with multi-radius

  `Erad G m = fun k => if (k : ℕ) < m then G.e k else G.b k`,

and collects the elementary geometry of these polydiscs: openness, monotonicity in `m`
(`Erad G m` decreases coordinatewise in `m`), the two boundary cases `E G 0 = polydisc 0 G.b`
and `E G n = polydisc 0 G.e`, a uniform sup-norm bound, and the finiteness of the `C^{k,α}`
norms of smooth functions on them.

It also contains the vanishing lemma for the iterated derivatives of a function which vanishes
beyond a fibre strip: such a function is `C^k`, so its iterated derivatives vanish on the
*closure* of the exterior of the strip as well (`iteratedFDeriv_eq_zero_of_ge`).  This is what
lets one use the closed fibre `‖y s‖ ≤ G.b s` in the transform estimates without a strict gap
between the fibre threshold and the tracking radius.
-/
import Mathlib
import Submission.Work.NN.Core.TelTwoDF.Defs
import Submission.Work.NN.Core.TelTwoDF.Rec2
import Submission.Work.CR.Flat.Holder.holderNorm_ne_top_of_isBounded

noncomputable section

open scoped NNReal ENNReal ContDiff
open Set

namespace Work.NN.Core.TelTwoDF

variable {n : ℕ}

/-- The multi-radius of the tracking polydisc of stage `m`. -/
noncomputable def Erad (G : Geom n) (m : ℕ) : Fin n → ℝ :=
  fun k => if (k : ℕ) < m then G.e k else G.b k

/-- The tracking polydisc of stage `m`, as a `polydisc`. -/
noncomputable def Eset (G : Geom n) (m : ℕ) : Set (Fin n → ℂ) :=
  Work.CR.Flat.polydisc 0 (Erad G m)

lemma mem_Eset {G : Geom n} {m : ℕ} {z : Fin n → ℂ} :
    z ∈ Eset G m ↔ ∀ k : Fin n, ‖z k‖ < Erad G m k := by
  rw [Eset, Work.CR.Flat.mem_polydisc]
  constructor
  · intro h k; simpa using h k
  · intro h k; simpa using h k

lemma Eset_eq_E (G : Geom n) (m : ℕ) : Eset G m = E G m := by
  ext z
  rw [mem_Eset]
  constructor
  · intro h k
    by_cases hk : (k : ℕ) < m
    · exact ⟨fun _ => by simpa [Erad, hk] using h k,
        fun hle => absurd hle (not_le.mpr hk)⟩
    · exact ⟨fun hlt => absurd hlt hk, fun _ => by simpa [Erad, hk] using h k⟩
  · intro h k
    by_cases hk : (k : ℕ) < m
    · simpa [Erad, hk] using (h k).1 hk
    · simpa [Erad, hk] using (h k).2 (not_lt.mp hk)

lemma isOpen_Eset (G : Geom n) (m : ℕ) : IsOpen (Eset G m) :=
  Work.CR.Flat.isOpen_polydisc 0 (Erad G m)

lemma Erad_le_Erad (G : Geom n) {m m' : ℕ} (h : m ≤ m') (k : Fin n) :
    Erad G m' k ≤ Erad G m k := by
  by_cases hk : (k : ℕ) < m
  · have hk' : (k : ℕ) < m' := lt_of_lt_of_le hk h
    simp only [Erad, hk, hk', ite_true, le_refl]
  · rw [show Erad G m k = G.b k from by simp [Erad, hk]]
    by_cases hk' : (k : ℕ) < m'
    · rw [show Erad G m' k = G.e k from by simp [Erad, hk']]
      exact (G.e_lt_b k).le
    · rw [show Erad G m' k = G.b k from by simp [Erad, hk']]

lemma Eset_mono (G : Geom n) {m m' : ℕ} (h : m ≤ m') : Eset G m' ⊆ Eset G m := by
  intro z hz
  rw [mem_Eset] at hz
  intro k
  simpa using lt_of_lt_of_le (hz k) (Erad_le_Erad G h k)

lemma Erad_le_b (G : Geom n) (m : ℕ) (k : Fin n) : Erad G m k ≤ G.b k := by
  by_cases hk : (k : ℕ) < m
  · rw [show Erad G m k = G.e k from by simp [Erad, hk]]
    exact (G.e_lt_b k).le
  · rw [show Erad G m k = G.b k from by simp [Erad, hk]]

lemma Eset_subset_b (G : Geom n) (m : ℕ) :
    Eset G m ⊆ Work.CR.Flat.polydisc 0 G.b := by
  intro z hz k
  rw [mem_Eset] at hz
  simpa using lt_of_lt_of_le (hz k) (Erad_le_b G m k)

lemma Erad_zero (G : Geom n) : Erad G 0 = G.b := by
  funext k; simp [Erad]

lemma Erad_n (G : Geom n) : Erad G n = G.e := by
  funext k; simp [Erad, k.isLt]

lemma Eset_zero (G : Geom n) : Eset G 0 = Work.CR.Flat.polydisc 0 G.b := by
  rw [Eset, Erad_zero]

lemma Eset_n (G : Geom n) : Eset G n = Work.CR.Flat.polydisc 0 G.e := by
  rw [Eset, Erad_n]

lemma Eset_succ_subset (G : Geom n) (s : ℕ) : Eset G (s + 1) ⊆ Eset G s :=
  Eset_mono G (Nat.le_succ s)

lemma norm_le_of_mem_Eset (G : Geom n) (m : ℕ) {z : Fin n → ℂ} (hz : z ∈ Eset G m) :
    ‖z‖ ≤ ∑ k : Fin n, G.b k := by
  rw [mem_Eset] at hz
  have hb : 0 ≤ ∑ k : Fin n, G.b k := Finset.sum_nonneg fun k _ => (G.b_pos k).le
  have h : ‖z‖₊ ≤ (⟨∑ k : Fin n, G.b k, hb⟩ : ℝ≥0) := by
    rw [Pi.nnnorm_def]
    refine Finset.sup_le_iff.mpr fun k _ => ?_
    have h3 : G.b k ≤ ∑ j : Fin n, G.b j :=
      Finset.single_le_sum (fun j _ => (G.b_pos j).le) (Finset.mem_univ k)
    exact_mod_cast le_trans (le_of_lt (hz k)) (le_trans (Erad_le_b G m k) h3)
  exact_mod_cast h

/-- The `C^{k,α}` norm of a `C^{k+1}` function is finite on a tracking polydisc. -/
lemma holderNorm_ne_top_Eset (G : Geom n) (m : ℕ) {k : ℕ} {α : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1) {f : (Fin n → ℂ) → ℂ} (hf : ContDiff ℝ (k + 1) f) :
    Work.CR.Flat.holderNorm k α f (Eset G m) ≠ ⊤ :=
  Work.CR.Flat.Holder.holderNorm_ne_top_of_isBounded (isOpen_Eset G m)
    (fun z hz => norm_le_of_mem_Eset G m hz) hα0 hα1 hf

/-! ## Vanishing of the iterated derivatives on the fibre strip -/

/-- A derivative of a function vanishing on a closed set vanishes on the interior of its
complement, i.e. the support of `D^i g` is contained in the closure of the support of `g`. -/
lemma iteratedFDeriv_eq_zero_of_lt_norm {n : ℕ} {B : ℝ} {s : Fin n}
    {g : (Fin n → ℂ) → ℂ} (hsupp : ∀ y : Fin n → ℂ, B ≤ ‖y s‖ → g y = 0) (i : ℕ) :
    ∀ y : Fin n → ℂ, B < ‖y s‖ → iteratedFDeriv ℝ i g y = 0 := by
  have hclosed : IsClosed {y : Fin n → ℂ | ‖y s‖ ≤ B} :=
    isClosed_le ((continuous_apply s).norm) continuous_const
  have hsub : tsupport g ⊆ {y : Fin n → ℂ | ‖y s‖ ≤ B} :=
    closure_minimal (fun z hz => le_of_not_gt fun hz' => hz (hsupp z hz'.le)) hclosed
  intro y hy
  have h1 : y ∉ tsupport g := fun h => absurd (hsub h) (not_le.mpr hy)
  have h2 : y ∉ tsupport (iteratedFDeriv ℝ i g) :=
    fun h => h1 (tsupport_iteratedFDeriv_subset i h)
  by_contra hne
  exact h2 (subset_tsupport _ (Function.mem_support.mpr hne))

/-- **Iterated derivatives vanish on the closed exterior of a fibre strip.**

If `g` is `C^k` and vanishes for `‖y s‖ ≥ B` with `B > 0`, then its `i`-th iterated derivative
vanishes there as well, for every `i ≤ k`: it vanishes on the open exterior `‖y s‖ > B`, and the
derivative is continuous.
-/
lemma iteratedFDeriv_eq_zero_of_ge {n : ℕ} {B : ℝ} {s : Fin n} {k i : ℕ} (hB : 0 < B) (hi : i ≤ k)
    {g : (Fin n → ℂ) → ℂ} (hg : ContDiff ℝ k g)
    (hsupp : ∀ y : Fin n → ℂ, B ≤ ‖y s‖ → g y = 0) :
    ∀ y : Fin n → ℂ, B ≤ ‖y s‖ → iteratedFDeriv ℝ i g y = 0 := by
  have hcont : Continuous (iteratedFDeriv ℝ i g) :=
    hg.continuous_iteratedFDeriv (m := i) (by exact_mod_cast hi)
  have hclosed : IsClosed {y : Fin n → ℂ | iteratedFDeriv ℝ i g y = 0} :=
    isClosed_eq hcont continuous_const
  have hsub : {y : Fin n → ℂ | B < ‖y s‖} ⊆ {y : Fin n → ℂ | iteratedFDeriv ℝ i g y = 0} :=
    fun y hy => iteratedFDeriv_eq_zero_of_lt_norm hsupp i y hy
  refine fun y hy => hclosed.closure_subset_iff.mpr hsub ?_
  rw [Metric.mem_closure_iff]
  intro ε hε
  set d : ℝ := 2 * max ‖y‖ 1 with hd
  have hdpos : 0 < d := by
    have h1 : (1 : ℝ) ≤ max ‖y‖ 1 := le_max_right _ _
    rw [hd]; linarith
  have hc : (1 : ℝ) < 1 + ε / d := by
    have := div_pos hε hdpos
    linarith
  refine ⟨(((1 + ε / d : ℝ)) : ℂ) • y, ?_, ?_⟩
  · have hmod : ‖((((1 + ε / d : ℝ)) : ℂ) • y) s‖ = (1 + ε / d) * ‖y s‖ := by
      simp only [Pi.smul_apply, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ 1 + ε / d)]
    rw [Set.mem_ofPred_eq, hmod]
    exact lt_of_le_of_lt hy (lt_mul_of_one_lt_left (lt_of_lt_of_le hB hy) hc)
  · rw [dist_eq_norm]
    have hsub' : y - (((1 + ε / d : ℝ)) : ℂ) • y = -((((ε / d : ℝ)) : ℂ) • y) := by
      rw [show (((1 + ε / d : ℝ)) : ℂ) = 1 + ((ε / d : ℝ) : ℂ) by push_cast; ring]
      rw [add_smul, one_smul]
      abel
    rw [hsub', norm_neg, norm_smul, Complex.norm_real,
      Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ ε / d)]
    have hbnd : ‖y‖ / d ≤ 1 / 2 := by
      rw [div_le_iff₀ hdpos]
      have h1 : ‖y‖ ≤ max ‖y‖ 1 := le_max_left _ _
      rw [hd]
      linarith
    have hprod : ε / d * ‖y‖ = ε * (‖y‖ / d) := by ring
    rw [hprod]
    nlinarith [hbnd, hε]

/-! ## The fibre relations between the two tracking polydiscs of one step -/

lemma Erad_succ_self (G : Geom n) (s : Fin n) : Erad G ((s : ℕ) + 1) s = G.e s := by
  simp [Erad]

lemma Erad_self (G : Geom n) (s : Fin n) : Erad G (s : ℕ) s = G.b s := by
  simp [Erad]

lemma Erad_succ_of_ne (G : Geom n) {s l : Fin n} (h : l ≠ s) :
    Erad G ((s : ℕ) + 1) l = Erad G (s : ℕ) l := by
  by_cases hl : (l : ℕ) < (s : ℕ)
  · have hl' : (l : ℕ) < (s : ℕ) + 1 := by omega
    simp only [Erad, hl, hl', ite_true]
  · have hl' : ¬ ((l : ℕ) < (s : ℕ) + 1) := by
      intro hc
      exact h (Fin.ext (by omega))
    simp only [Erad, hl, hl', ite_false]

/-- Changing the `s`-th coordinate of a vector of `ℂⁿ` moves it by the distance between the
two values of that coordinate. -/
lemma dist_update_self {n : ℕ} (y : Fin n → ℂ) (s : Fin n) (c : ℂ) :
    dist (Function.update y s c) y = ‖c - y s‖ := by
  rw [dist_eq_norm]
  have h : Function.update y s c - y = Function.update (0 : Fin n → ℂ) s (c - y s) := by
    funext l
    by_cases hl : l = s
    · subst hl; simp
    · simp [Function.update_of_ne hl]
  rw [h]
  rw [show Function.update (0 : Fin n → ℂ) s (c - y s) = Pi.single s (c - y s) from by
    funext l
    by_cases hl : l = s
    · subst hl; simp
    · rw [Function.update_of_ne hl, Pi.single_eq_of_ne hl]; rfl]
  exact congrArg (fun r : NNReal => (r : ℝ))
    (Pi.nnnorm_single (G := fun _ : Fin n => ℂ) (i := s) (c - y s))

/-- A point of the fibre of `z ∈ Eset G (s+1)` whose `s`-coordinate is *strictly* inside the
support radius lies in the stage-`s` tracking polydisc. -/
lemma mem_Eset_of_fiber (G : Geom n) {s : Fin n} {z y : Fin n → ℂ}
    (hz : z ∈ Eset G ((s : ℕ) + 1)) (hy : ∀ l, l ≠ s → y l = z l) (hys : ‖y s‖ < G.b s) :
    y ∈ Eset G (s : ℕ) := by
  rw [mem_Eset] at hz ⊢
  intro l
  by_cases hl : l = s
  · subst hl
    rw [Erad_self]; exact hys
  · rw [hy l hl, ← Erad_succ_of_ne G hl]; exact hz l

/-- A point of the fibre of `z ∈ Eset G (s+1)` whose `s`-coordinate is at most the support radius
lies in the *closure* of the stage-`s` tracking polydisc. -/
lemma mem_closure_Eset_of_fiber (G : Geom n) {s : Fin n} {z y : Fin n → ℂ}
    (hz : z ∈ Eset G ((s : ℕ) + 1)) (hy : ∀ l, l ≠ s → y l = z l) (hys : ‖y s‖ ≤ G.b s) :
    y ∈ closure (Eset G (s : ℕ)) := by
  rw [Metric.mem_closure_iff]
  intro ε hε
  set d : ℝ := 2 * max ‖y‖ 1 with hd
  have hdpos : 0 < d := by
    have h1 : (1 : ℝ) ≤ max ‖y‖ 1 := le_max_right _ _
    rw [hd]; linarith
  set δ : ℝ := min (ε / d) (1 / 2) with hδ
  have hδpos : 0 < δ := lt_min (div_pos hε hdpos) (by norm_num)
  have hδlt : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδle : δ ≤ ε / d := min_le_left _ _
  refine ⟨Function.update y s ((1 - δ) * y s), ?_, ?_⟩
  · rw [mem_Eset]
    intro l
    by_cases hl : l = s
    · subst hl
      rw [Erad_self, Function.update_apply, if_pos rfl]
      have hcast : ((1 - δ : ℝ) : ℂ) = 1 - (δ : ℂ) := by push_cast; ring
      rw [← hcast, norm_mul, Complex.norm_real,
        Real.norm_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - δ)]
      nlinarith [hδpos, hys, G.b_pos l]
    · rw [Function.update_of_ne hl, hy l hl]
      rw [mem_Eset] at hz
      have := hz l
      rwa [Erad_succ_of_ne G hl] at this
  · rw [dist_comm, dist_update_self]
    have h : ‖(1 - δ) * y s - y s‖ = δ * ‖y s‖ := by
      rw [show ((1 - δ) * y s - y s : ℂ) = (-(δ : ℂ)) * y s by push_cast; ring]
      rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hδpos)]
    rw [h]
    have hys_le : ‖y s‖ ≤ d / 2 := by
      have h1 : ‖y s‖ ≤ ‖y‖ := norm_le_pi_norm y s
      have h2 : ‖y‖ ≤ max ‖y‖ 1 := le_max_left _ _
      rw [hd]; linarith
    calc δ * ‖y s‖ ≤ δ * (d / 2) := mul_le_mul_of_nonneg_left hys_le (le_of_lt hδpos)
      _ ≤ (ε / d) * (d / 2) := mul_le_mul_of_nonneg_right hδle (by positivity)
      _ = ε / 2 := by field_simp
      _ < ε := by linarith

end Work.NN.Core.TelTwoDF
