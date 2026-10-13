import Mathlib
import Submission.Work.WilE3.Defs

namespace Work.WilE3.Taylor

set_option autoImplicit false
open Classical Topology
open WilkiesDesign.E

/-
  annals_wilkies_conjecture, AREA E3: the elementary reductions of the target lemma
  `Work.WilE3.Taylor.hasLoj_of_multiplicity` — the trivial cases, monotonicity in the exponent, and
  the `y ∉ Z` case.  Independent of the deep analytic input.
-/

/-! ## Elementary reductions of `hasLoj_of_multiplicity`

The statement of `Work.WilE3.Taylor.hasLoj_of_multiplicity` is a consequence of Gabrielov 1995,
Thm 3.4 (the effective Łojasiewicz inequality for Pfaffian functions), whose proof goes through his
§3 polar-curve theory.  The *elementary* reductions of the statement (the trivial cases, the
monotonicity in the exponent, and the `y ∉ Z` case) are proved here; they are needed by any proof
and are independent of the deep input.  See `NOTES_hasLoj_of_multiplicity.md` in this directory for
the precise remaining gap. -/

/-- `Metric.infDist` of the empty set is `0`. -/
theorem infDist_empty_eq_zero {k : ℕ} (x : Fin k → ℝ) :
    Metric.infDist x (∅ : Set (Fin k → ℝ)) = 0 := by
  simp [Metric.infDist]

/-- `Metric.infDist · Z` does not increase faster than `1` near any base point. -/
theorem eventually_infDist_le {k : ℕ} (Z : Set (Fin k → ℝ)) (y : Fin k → ℝ) :
    ∀ᶠ x in 𝓝 y, Metric.infDist x Z ≤ Metric.infDist y Z + 1 := by
  filter_upwards [Metric.ball_mem_nhds y (by norm_num : (0 : ℝ) < 1)] with x hx
  have h1 : Metric.infDist x Z ≤ Metric.infDist y Z + dist x y :=
    Metric.infDist_le_infDist_add_dist
  have h2 : dist x y < 1 := by simpa [Metric.mem_ball] using hx
  linarith

/-- `HasLoj` is monotone in the exponent. -/
theorem HasLoj.mono {k : ℕ} {F : (Fin k → ℝ) → ℝ} {Z : Set (Fin k → ℝ)} {x : Fin k → ℝ}
    {q q' : ℕ} (h : Work.WilE3.HasLoj F Z x q) (hqq' : q ≤ q')
    (hbd : ∀ᶠ y in 𝓝 x, Metric.infDist y Z ≤ 1) : Work.WilE3.HasLoj F Z x q' := by
  obtain ⟨C, hC, hF⟩ := h
  refine ⟨C, hC, ?_⟩
  filter_upwards [hF, hbd] with y h1 h2
  have h2' : Metric.infDist y Z ^ q' ≤ Metric.infDist y Z ^ q :=
    pow_le_pow_of_le_one Metric.infDist_nonneg h2 hqq'
  calc C * Metric.infDist y Z ^ q' ≤ C * Metric.infDist y Z ^ q :=
        mul_le_mul_of_nonneg_left h2' hC.le
    _ ≤ |F y| := h1

/-- If `|F|` is bounded away from `0` at the base point, the Łojasiewicz inequality holds for every
exponent (the `y ∉ Z` case and, in particular, the case `B.eqs = []` of a system whose residue does
not vanish at `y`). -/
theorem hasLoj_of_pos {k : ℕ} {F : (Fin k → ℝ) → ℝ} {Z : Set (Fin k → ℝ)} {x : Fin k → ℝ}
    (hcont : ContinuousAt F x) (hpos : 0 < |F x|) (q : ℕ) : Work.WilE3.HasLoj F Z x q := by
  have hc : ContinuousAt (fun y : Fin k → ℝ => |F y|) x := hcont.abs
  have hF : ∀ᶠ y in 𝓝 x, |F x| / 2 ≤ |F y| := by
    have hmem : |F x| ∈ Set.Ioi (|F x| / 2) := by simp only [Set.mem_Ioi]; linarith
    filter_upwards [hc.tendsto.eventually (isOpen_Ioi.mem_nhds hmem)] with y hy
    exact le_of_lt hy
  have hxpos : 0 < |F x| := hpos
  by_cases hZ : Z = ∅
  · subst hZ
    refine ⟨min 1 (|F x| / 2), lt_min one_pos (by linarith), ?_⟩
    filter_upwards [hF] with y hy
    rw [infDist_empty_eq_zero]
    have h0q : (0 : ℝ) ^ q ≤ 1 := by
      rcases Nat.eq_zero_or_pos q with h | h
      · subst h; norm_num
      · rw [zero_pow (Nat.pos_iff_ne_zero.mp h)]; norm_num
    have hnn : (0 : ℝ) ≤ min 1 (|F x| / 2) :=
      le_min zero_le_one (by linarith [abs_nonneg (F x)])
    calc min 1 (|F x| / 2) * (0 : ℝ) ^ q ≤ min 1 (|F x| / 2) * 1 :=
          mul_le_mul_of_nonneg_left h0q hnn
      _ = min 1 (|F x| / 2) := mul_one _
      _ ≤ |F x| / 2 := min_le_right _ _
      _ ≤ |F y| := hy
  · obtain ⟨z, hz⟩ := Set.nonempty_iff_ne_empty.mpr hZ
    obtain ⟨D, hD, hDle⟩ : ∃ D : ℝ, 0 < D ∧ ∀ᶠ y in 𝓝 x, Metric.infDist y Z ≤ D := by
      refine ⟨dist x z + 1, by positivity, ?_⟩
      filter_upwards [eventually_infDist_le Z x] with y hy
      have h2 : Metric.infDist x Z ≤ dist x z := Metric.infDist_le_dist_of_mem hz
      linarith
    refine ⟨|F x| / 2 / (D ^ q + 1), by positivity, ?_⟩
    filter_upwards [hF, hDle] with y hy hdy
    have hpow : Metric.infDist y Z ^ q ≤ D ^ q :=
      pow_le_pow_left₀ Metric.infDist_nonneg hdy q
    have hDq : 0 ≤ D ^ q := pow_nonneg hD.le q
    have hkey : |F x| / 2 / (D ^ q + 1) * D ^ q ≤ |F x| / 2 := by
      rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith [hDq]
    calc |F x| / 2 / (D ^ q + 1) * Metric.infDist y Z ^ q
        ≤ |F x| / 2 / (D ^ q + 1) * D ^ q :=
          mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ |F x| / 2 := hkey
      _ ≤ |F y| := hy

/-- The residual `∑_{f ∈ L} |eaEval c f x|` is `≥ 0`. -/
theorem sum_abs_eaEval_nonneg {k r : ℕ} (c : EAChain k r) (L : List (EAPoly k r))
    (x : Fin k → ℝ) : 0 ≤ (L.map fun f => |eaEval c f x|).sum :=
  List.sum_nonneg fun _ hy => by
    obtain ⟨f, _, rfl⟩ := List.mem_map.mp hy
    exact abs_nonneg _

/-- The residual of the empty system vanishes identically, and its zero set is everything, so
`HasLoj` holds trivially *for positive exponents*.  (For `q = 0` it would be false: it would ask for
a positive constant bounded by `0`.)  This is why the threshold `K.eval B.deg < q` deliberately
forces `q ≥ 1`. -/
theorem hasLoj_of_eqs_empty {k r : ℕ} (c : EAChain k r) (y : Fin k → ℝ) {q : ℕ} (hq : 1 ≤ q) :
    Work.WilE3.HasLoj (fun x => (([] : List (EAPoly k r)).map fun f => |eaEval c f x|).sum)
      {x | ∀ f' ∈ ([] : List (EAPoly k r)), eaEval c f' x = 0} y q := by
  refine ⟨1, one_pos, ?_⟩
  filter_upwards with x
  have h0 : Metric.infDist x {x : Fin k → ℝ | ∀ f' ∈ ([] : List (EAPoly k r)),
      eaEval c f' x = 0} = 0 := by
    refine le_antisymm ?_ Metric.infDist_nonneg
    have hx : x ∈ {x : Fin k → ℝ | ∀ f' ∈ ([] : List (EAPoly k r)), eaEval c f' x = 0} := by simp
    calc Metric.infDist x {x : Fin k → ℝ | ∀ f' ∈ ([] : List (EAPoly k r)),
            eaEval c f' x = 0} ≤ dist x x := Metric.infDist_le_dist_of_mem hx
      _ = 0 := dist_self x
  rw [h0, zero_pow (by omega : q ≠ 0)]
  simp


end Work.WilE3.Taylor
