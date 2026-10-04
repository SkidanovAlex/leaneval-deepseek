import Mathlib
import Submission.Commons.Analysis.ODE.limit_at_right_of_lipschitzOnWith_of_lt
import Submission.Commons.Analysis.ODE.exists_hasDerivWithinAt_Icc_of_lipschitzWith
import Submission.Commons.Analysis.ODE.exists_extension_of_tendsto_atRight_of_lipschitzWith
import Submission.Commons.Analysis.ODE.norm_sub_le_gronwallBound_of_hasDerivAt_of_lipschitzWith

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.Analysis.ODE

open Filter Set Metric
open scoped Topology NNReal

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
/-- **A priori bound for a solution of a globally Lipschitz ODE.**

If `z` solves `z' = f ∘ z` on an interval `Set.Ioo a b` containing `0`, then for every `t` in the
interval, `‖z t - z 0‖` is bounded by the Grönwall bound depending only on the endpoints `a`, `b`.
For `t ≥ 0` this is applied directly on `[0, t]`; for `t ≤ 0` it is applied to the time-reversed
trajectory `s ↦ z (-s)` and the field `y ↦ -f y`. -/
theorem norm_sub_le_gronwallBound_of_hasDerivAt_of_mem_Ioo
    {f : E → E} {L : ℝ≥0} (hf : LipschitzWith L f) {z : ℝ → E} {a b : ℝ}
    (h0 : (0 : ℝ) ∈ Set.Ioo a b) (hz : ∀ t ∈ Set.Ioo a b, HasDerivAt z (f (z t)) t) :
    ∀ t ∈ Set.Ioo a b,
      ‖z t - z 0‖ ≤ gronwallBound 0 (L : ℝ) ‖f (z 0)‖ (max b (-a)) := by
  intro t ht
  have hmono := gronwallBound_mono (le_refl (0 : ℝ)) (norm_nonneg (f (z 0)))
    (NNReal.coe_nonneg L)
  rcases le_total 0 t with ht0 | ht0
  · have hI : Set.Icc (0 : ℝ) t ⊆ Set.Ioo a b :=
      fun s hs => ⟨lt_of_lt_of_le h0.1 hs.1, lt_of_le_of_lt hs.2 ht.2⟩
    have h := norm_sub_le_gronwallBound_of_hasDerivAt_of_lipschitzWith hf (T := t) ht0
      (fun s hs => hz s (hI hs)) t ⟨ht0, le_refl t⟩
    exact le_trans h (hmono (le_trans (le_of_lt ht.2) (le_max_left b (-a))))
  · set g : E → E := fun y => -f y with hg
    have hgl : LipschitzWith L g := by
      change LipschitzWith L (fun y => -f y)
      exact hf.neg
    have hw : ∀ s ∈ Set.Icc (0 : ℝ) (-t),
        HasDerivAt (fun s => z (-s)) (g ((fun s => z (-s)) s)) s := by
      intro s hs
      have hmem : -s ∈ Set.Ioo a b :=
        ⟨by linarith [ht.1, hs.2], by linarith [hs.1, h0.2]⟩
      have h1 : HasDerivAt z (f (z (-s))) (-s) := hz (-s) hmem
      have h2 : HasDerivAt (fun s : ℝ => -s) (-1 : ℝ) s := hasDerivAt_neg s
      have h3 := h1.scomp s h2
      simpa [hg, Function.comp_def] using h3
    have hneg : (0 : ℝ) ≤ -t := by linarith
    have h := norm_sub_le_gronwallBound_of_hasDerivAt_of_lipschitzWith hgl
      (z := fun s => z (-s)) hneg hw (-t) ⟨by linarith, le_refl (-t)⟩
    have hg0 : ‖g (z 0)‖ = ‖f (z 0)‖ := by
      change ‖-f (z 0)‖ = ‖f (z 0)‖
      simp
    rw [neg_neg, neg_zero, hg0] at h
    exact le_trans h (hmono (le_trans (by linarith [ht.1]) (le_max_right b (-a))))

omit [CompleteSpace E] in
/-- A solution of a globally Lipschitz ODE on an interval containing `0` is Lipschitz there, with
constant given by the Grönwall bound on the interval. -/
theorem exists_lipschitzOnWith_of_hasDerivAt_of_lipschitzWith
    {f : E → E} {L : ℝ≥0} (hf : LipschitzWith L f) {z : ℝ → E} {a b : ℝ}
    (h0 : (0 : ℝ) ∈ Set.Ioo a b) (hz : ∀ t ∈ Set.Ioo a b, HasDerivAt z (f (z t)) t) :
    ∃ M : ℝ≥0, LipschitzOnWith M z (Set.Ioo a b) := by
  have hbnd := norm_sub_le_gronwallBound_of_hasDerivAt_of_mem_Ioo hf h0 hz
  set G : ℝ := gronwallBound 0 (L : ℝ) ‖f (z 0)‖ (max b (-a)) with hG
  have hG0 : 0 ≤ G := by
    rw [hG]
    calc (0 : ℝ) = gronwallBound 0 (L : ℝ) ‖f (z 0)‖ 0 :=
          (gronwallBound_x0 0 (L : ℝ) ‖f (z 0)‖).symm
      _ ≤ gronwallBound 0 (L : ℝ) ‖f (z 0)‖ (max b (-a)) :=
          gronwallBound_mono (le_refl (0 : ℝ)) (norm_nonneg (f (z 0))) (NNReal.coe_nonneg L)
            (le_trans (le_of_lt h0.2) (le_max_left b (-a)))
  refine ⟨⟨‖f (z 0)‖ + (L : ℝ) * G, add_nonneg (norm_nonneg _)
    (mul_nonneg (NNReal.coe_nonneg L) hG0)⟩, ?_⟩
  refine Convex.lipschitzOnWith_of_nnnorm_deriv_le (fun t ht => (hz t ht).differentiableAt)
    (fun t ht => ?_) (convex_Ioo a b)
  change ‖deriv z t‖ ≤ ‖f (z 0)‖ + (L : ℝ) * G
  rw [(hz t ht).deriv]
  have h1 : ‖f (z t)‖ ≤ ‖f (z 0)‖ + (L : ℝ) * G := by
    have hlip := hf.dist_le_mul (z t) (z 0)
    rw [dist_eq_norm, dist_eq_norm] at hlip
    have hb := hbnd t ht
    rw [hG]
    calc ‖f (z t)‖ ≤ ‖f (z t) - f (z 0)‖ + ‖f (z 0)‖ := norm_le_norm_sub_add _ _
      _ ≤ (L : ℝ) * ‖z t - z 0‖ + ‖f (z 0)‖ := by linarith
      _ ≤ (L : ℝ) * gronwallBound 0 (L : ℝ) ‖f (z 0)‖ (max b (-a)) + ‖f (z 0)‖ := by
          have := mul_le_mul_of_nonneg_left hb (NNReal.coe_nonneg L)
          linarith
      _ = ‖f (z 0)‖ + (L : ℝ) * gronwallBound 0 (L : ℝ) ‖f (z 0)‖ (max b (-a)) := by ring
  exact h1

/-- **Right extension on a bounded window.**

If a solution of a globally Lipschitz ODE on `Set.Ioo a b` (with `a < 0 < b`) takes the value `p`
at `0`, then it extends to `Set.Ioo a R` for every `R ≥ b`.  The proof takes the supremum `τ` of
the right endpoints of windows on which a solution exists; a solution is assembled on the whole
window `(a, τ)` using uniqueness, the Grönwall bound shows that it is Lipschitz there (so it has a
limit at `τ`), and the extension lemma then produces a window strictly bigger than `τ`. -/
theorem exists_solution_Ioo_of_exists_solution_Ioo
    {f : E → E} {L : ℝ≥0} (hf : LipschitzWith L f) {p : E} {a b R : ℝ}
    (ha : a < 0) (hb : 0 < b) (hbR : b ≤ R)
    (hz : ∃ z : ℝ → E, z 0 = p ∧ ∀ t ∈ Set.Ioo a b, HasDerivAt z (f (z t)) t) :
    ∃ z : ℝ → E, z 0 = p ∧ ∀ t ∈ Set.Ioo a R, HasDerivAt z (f (z t)) t := by
  classical
  let S : Set ℝ := {c | b ≤ c ∧ c ≤ R ∧
    ∃ z : ℝ → E, z 0 = p ∧ ∀ t ∈ Set.Ioo a c, HasDerivAt z (f (z t)) t}
  have hSne : S.Nonempty := ⟨b, le_rfl, hbR, hz⟩
  have hSbdd : BddAbove S := ⟨R, fun c hc => hc.2.1⟩
  have hbT : b ≤ sSup S := le_csSup hSbdd ⟨le_rfl, hbR, hz⟩
  have hTle : sSup S ≤ R := csSup_le hSne (fun c hc => hc.2.1)
  have hTpos : (0 : ℝ) < sSup S := lt_of_lt_of_le hb hbT
  have haT : a < sSup S := lt_trans ha hTpos
  have hltS : ∀ t : ℝ, t < sSup S → ∃ c ∈ S, t < c :=
    fun t ht => (lt_csSup_iff hSbdd hSne).mp ht
  let cOf : ∀ t : ℝ, t < sSup S → ℝ := fun t ht => (hltS t ht).choose
  have hcOf_mem : ∀ (t : ℝ) (ht : t < sSup S), cOf t ht ∈ S :=
    fun t ht => (hltS t ht).choose_spec.1
  have hcOf_lt : ∀ (t : ℝ) (ht : t < sSup S), t < cOf t ht :=
    fun t ht => (hltS t ht).choose_spec.2
  let sol : ∀ t : ℝ, t < sSup S → ℝ → E := fun t ht => (hltS t ht).choose_spec.1.2.2.choose
  have hsol0 : ∀ (t : ℝ) (ht : t < sSup S), sol t ht 0 = p :=
    fun t ht => (hltS t ht).choose_spec.1.2.2.choose_spec.1
  have hsol : ∀ (t : ℝ) (ht : t < sSup S) (u : ℝ), u ∈ Set.Ioo a (cOf t ht) →
      HasDerivAt (sol t ht) (f (sol t ht u)) u :=
    fun t ht u hu => (hltS t ht).choose_spec.1.2.2.choose_spec.2 u hu
  have hcompat : ∀ (t : ℝ) (ht : t < sSup S) (s : ℝ) (hs : s < sSup S),
      Set.EqOn (sol t ht) (sol s hs) (Set.Ioo a (min (cOf t ht) (cOf s hs))) := by
    intro t ht s hs
    refine ODE_solution_unique_of_mem_Ioo (v := fun _ : ℝ => f) (s := fun _ => Set.univ)
      (K := L) (f := sol t ht) (g := sol s hs) (t₀ := 0)
      (fun u _ => hf.lipschitzOnWith) ?_ (fun u hu => ⟨?_, trivial⟩)
      (fun u hu => ⟨?_, trivial⟩) ?_
    · exact ⟨ha, lt_min (lt_of_lt_of_le hb (hcOf_mem t ht).1) (lt_of_lt_of_le hb (hcOf_mem s hs).1)⟩
    · exact hsol t ht u ⟨hu.1, lt_of_lt_of_le hu.2 (min_le_left _ _)⟩
    · exact hsol s hs u ⟨hu.1, lt_of_lt_of_le hu.2 (min_le_right _ _)⟩
    · rw [hsol0 t ht, hsol0 s hs]
  let zT : ℝ → E := fun t => if ht : t < sSup S then sol t ht t else p
  have hzT0 : zT 0 = p := by
    simp only [zT]
    rw [dif_pos hTpos]
    exact hsol0 0 hTpos
  have hzT_ev : ∀ (t : ℝ) (ht : t ∈ Set.Ioo a (sSup S)), zT =ᶠ[𝓝 t] sol t ht.2 := by
    intro t ht
    filter_upwards [isOpen_Ioo.mem_nhds
      (show t ∈ Set.Ioo a (cOf t ht.2) from ⟨ht.1, hcOf_lt t ht.2⟩)] with s hs
    have hsT : s < sSup S := lt_of_lt_of_le hs.2 (le_csSup hSbdd (hcOf_mem t ht.2))
    simp only [zT]
    rw [dif_pos hsT]
    exact hcompat s hsT t ht.2 ⟨hs.1, lt_min (hcOf_lt s hsT) hs.2⟩
  have hzT_deriv : ∀ t ∈ Set.Ioo a (sSup S), HasDerivAt zT (f (zT t)) t := by
    intro t ht
    have h := (hsol t ht.2 t ⟨ht.1, hcOf_lt t ht.2⟩).congr_of_eventuallyEq (hzT_ev t ht)
    rw [show zT t = sol t ht.2 t from (hzT_ev t ht).eq_of_nhds]
    exact h
  have hTR : sSup S = R := by
    by_contra hne
    have hlt : sSup S < R := lt_of_le_of_ne hTle hne
    obtain ⟨M, hM⟩ := exists_lipschitzOnWith_of_hasDerivAt_of_lipschitzWith hf
      ⟨ha, hTpos⟩ hzT_deriv
    obtain ⟨l, hl⟩ := limit_at_right_of_lipschitzOnWith_of_lt haT hM
    obtain ⟨δ, hδ, w, hw, hweq⟩ :=
      exists_extension_of_tendsto_atRight_of_lipschitzWith hf haT hzT_deriv hl
    set c' : ℝ := min (sSup S + δ) R with hc'def
    have hc'gt : sSup S < c' := lt_min (by linarith) hlt
    have hw0 : w 0 = p := (hweq ⟨ha, hTpos⟩).trans hzT0
    have hc'mem : c' ∈ S := by
      refine ⟨le_trans hbT (le_of_lt hc'gt), min_le_right _ _, w, hw0, ?_⟩
      intro t ht
      exact hw t ⟨ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
    have hle := le_csSup hSbdd hc'mem
    linarith
  refine ⟨zT, hzT0, ?_⟩
  intro t ht
  exact hzT_deriv t (by rw [← hTR] at ht; exact ht)

/-- **Existence on a symmetric bounded interval.**  A globally Lipschitz ODE has a solution on
`Set.Ioo (-N) N` through any initial point at time `0`. -/
theorem exists_solution_Ioo_neg_Ioo
    {f : E → E} {L : ℝ≥0} (hf : LipschitzWith L f) (x : E) {N : ℝ} (hN : 0 < N) :
    ∃ z : ℝ → E, z 0 = x ∧ ∀ t ∈ Set.Ioo (-N) N, HasDerivAt z (f (z t)) t := by
  obtain ⟨ε, hε, y, hy0, hy⟩ := exists_hasDerivWithinAt_Icc_of_lipschitzWith hf x 0
  have hyderiv : ∀ t ∈ Set.Ioo (-ε) ε, HasDerivAt y (f (y t)) t := fun t ht =>
    (hy t (show t ∈ Set.Icc (0 - ε) (0 + ε) from
      ⟨by linarith [ht.1], by linarith [ht.2]⟩)).hasDerivAt
      (Icc_mem_nhds (by linarith [ht.1]) (by linarith [ht.2]))
  set a₀ : ℝ := max (-N) (-ε) with ha₀
  set b₀ : ℝ := min N ε with hb₀
  have ha₀lt : a₀ < 0 := max_lt (by linarith) (by linarith)
  have hb₀gt : 0 < b₀ := lt_min hN hε
  have hsub : Set.Ioo a₀ b₀ ⊆ Set.Ioo (-ε) ε := by
    intro t ht
    rw [ha₀, hb₀] at ht
    exact ⟨by linarith [ht.1, le_max_right (-N) (-ε)],
      by linarith [ht.2, min_le_right N ε]⟩
  have hbase : ∃ z : ℝ → E, z 0 = x ∧ ∀ t ∈ Set.Ioo a₀ b₀, HasDerivAt z (f (z t)) t :=
    ⟨y, hy0, fun t ht => hyderiv t (hsub ht)⟩
  have hb₀N : b₀ ≤ N := by rw [hb₀]; exact min_le_left N ε
  obtain ⟨z₁, hz₁0, hz₁⟩ := exists_solution_Ioo_of_exists_solution_Ioo hf ha₀lt hb₀gt hb₀N hbase
  -- reverse time and extend on the left, then reverse back
  set g : E → E := fun y => -f y with hg
  have hgl : LipschitzWith L g := by
    change LipschitzWith L (fun y => -f y)
    exact hf.neg
  set w : ℝ → E := fun s => z₁ (-s) with hw
  have hw0 : w 0 = x := by simp [hw, hz₁0]
  have hwderiv : ∀ s ∈ Set.Ioo (-N) (-a₀), HasDerivAt w (g (w s)) s := by
    intro s hs
    have hmem : -s ∈ Set.Ioo a₀ N := ⟨by linarith [hs.2], by linarith [hs.1]⟩
    have h3 := (hz₁ (-s) hmem).scomp s (hasDerivAt_neg s)
    simpa [hw, hg, Function.comp_def] using h3
  have hnega₀ : 0 < -a₀ := by linarith
  have hleNa₀ : -a₀ ≤ N := by rw [ha₀]; linarith [le_max_left (-N) (-ε)]
  obtain ⟨w₂, hw₂0, hw₂⟩ := exists_solution_Ioo_of_exists_solution_Ioo hgl
    (a := -N) (b := -a₀) (R := N) (by linarith) hnega₀ hleNa₀ ⟨w, hw0, hwderiv⟩
  refine ⟨fun t => w₂ (-t), ?_, ?_⟩
  · simpa using hw₂0
  · intro t ht
    have hmem : -t ∈ Set.Ioo (-N) N := ⟨by linarith [ht.2], by linarith [ht.1]⟩
    have h3 := (hw₂ (-t) hmem).scomp t (hasDerivAt_neg t)
    simpa [hg, Function.comp_def] using h3

/-- **A globally Lipschitz vector field on a complete space is complete.**

If `f : E → E` is Lipschitz with constant `L` on a complete normed space and `x : E`, then the
initial value problem `y' = f ∘ y`, `y 0 = x` has a solution defined on all of `ℝ`.

Solutions on the symmetric windows `Set.Ioo (-N) N` are constructed above; two of them agree on
the intersection of their windows by uniqueness of ODE solutions, so a single global solution is
obtained by evaluating, at `t`, any solution whose window contains `t`. -/
theorem exists_global_solution_of_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {f : E → E} {L : ℝ≥0} (hf : LipschitzWith L f) (x : E) :
    ∃ y : ℝ → E, y 0 = x ∧ ∀ t : ℝ, HasDerivAt y (f (y t)) t := by
  classical
  let Z : ℝ → ℝ → E := fun N t =>
    if h : 0 < N then (exists_solution_Ioo_neg_Ioo hf x h).choose t else x
  have hZ0 : ∀ (N : ℝ) (hN : 0 < N), Z N 0 = x := by
    intro N hN
    simp only [Z, dif_pos hN]
    exact (exists_solution_Ioo_neg_Ioo hf x hN).choose_spec.1
  have hZ : ∀ (N : ℝ) (hN : 0 < N) (t : ℝ), t ∈ Set.Ioo (-N) N →
      HasDerivAt (Z N) (f (Z N t)) t := by
    intro N hN t ht
    have h := (exists_solution_Ioo_neg_Ioo hf x hN).choose_spec.2 t ht
    simpa only [Z, dif_pos hN] using h
  have hcompat : ∀ (N M : ℝ) (hN : 0 < N) (hM : 0 < M),
      Set.EqOn (Z N) (Z M) (Set.Ioo (-(min N M)) (min N M)) := by
    intro N M hN hM
    refine ODE_solution_unique_of_mem_Ioo (v := fun _ : ℝ => f) (s := fun _ => Set.univ)
      (K := L) (f := Z N) (g := Z M) (t₀ := 0) (a := -(min N M)) (b := min N M)
      (fun u _ => hf.lipschitzOnWith) ⟨by linarith [lt_min hN hM], lt_min hN hM⟩
      (fun u hu => ⟨?_, trivial⟩) (fun u hu => ⟨?_, trivial⟩) ?_
    · exact hZ N hN u ⟨by linarith [hu.1, min_le_left N M], by linarith [hu.2, min_le_left N M]⟩
    · exact hZ M hM u ⟨by linarith [hu.1, min_le_right N M], by linarith [hu.2, min_le_right N M]⟩
    · rw [hZ0 N hN, hZ0 M hM]
  let y : ℝ → E := fun t => Z (|t| + 1) t
  have hy_ev : ∀ t : ℝ, y =ᶠ[𝓝 t] Z (|t| + 1) := by
    intro t
    have ht : t ∈ Set.Ioo (-(|t| + 1)) (|t| + 1) :=
      ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
    have hsabs : |s| < |t| + 1 := by
      rw [abs_lt]; exact ⟨hs.1, hs.2⟩
    show Z (|s| + 1) s = Z (|t| + 1) s
    have hmin : |s| < min (|s| + 1) (|t| + 1) := lt_min (by linarith) hsabs
    exact hcompat (|s| + 1) (|t| + 1) (by positivity) (by positivity)
      ⟨by linarith [neg_le_abs s, hmin], by linarith [le_abs_self s, hmin]⟩
  refine ⟨y, ?_, ?_⟩
  · show Z (|(0 : ℝ)| + 1) 0 = x
    rw [hZ0]
    norm_num
  · intro t
    have ht : t ∈ Set.Ioo (-(|t| + 1)) (|t| + 1) :=
      ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    have hp : (0 : ℝ) < |t| + 1 := by positivity
    have h := hZ (|t| + 1) hp t ht
    have h1 := hy_ev t
    rw [h1.eq_of_nhds]
    exact h.congr_of_eventuallyEq h1

end Commons.Analysis.ODE
