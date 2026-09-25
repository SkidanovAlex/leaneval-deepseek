import Mathlib.Algebra.Order.Ring.Star
import Mathlib.MeasureTheory.Covering.Vitali
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Maximal

open MeasureTheory Filter Finset
open scoped BigOperators ENNReal Topology

/-- The (centred) maximal average over intervals of length at most `N`, evaluated in
`ℝ≥0∞`:
`hlTruncMax g x N = sup { (b-a)⁻¹ ∫_a^b g : a ≤ x ≤ b, b - a ≤ N }`. -/
noncomputable def hlTruncMax (g : ℝ → ℝ≥0∞) (x N : ℝ) : ℝ≥0∞ :=
  ⨆ (p : {q : ℝ × ℝ // q.1 ≤ x ∧ x ≤ q.2 ∧ q.2 - q.1 ≤ N}),
    ENNReal.ofReal (p.1.2 - p.1.1)⁻¹ * ∫⁻ y in Set.Icc p.1.1 p.1.2, g y

/-- The (centred) maximal average over all intervals containing `x`, evaluated in `ℝ≥0∞`. -/
noncomputable def hlMax (g : ℝ → ℝ≥0∞) (x : ℝ) : ℝ≥0∞ :=
  ⨆ (a : ℝ) (b : ℝ) (_ : a ≤ x ∧ x ≤ b), ENNReal.ofReal (b - a)⁻¹ * ∫⁻ y in Set.Icc a b, g y

/-- Elementary `ℝ≥0∞` manipulation: if `A < B` and
`ofReal lam < ofReal (B - A)⁻¹ * I`, then `ofReal lam * ofReal (B - A) ≤ I`.
(Put differently: the average of `I` over an interval of length `B - A` exceeds `lam`.) -/
lemma ofReal_mul_le_of_lt_mul_inv {I : ℝ≥0∞} {lam A B : ℝ} (hAB : A < B)
    (h : ENNReal.ofReal lam < ENNReal.ofReal (B - A)⁻¹ * I) :
    ENNReal.ofReal lam * ENNReal.ofReal (B - A) ≤ I := by
  have hpos : 0 < B - A := sub_pos.mpr hAB
  have hne0 : ENNReal.ofReal (B - A) ≠ 0 := (ENNReal.ofReal_pos.mpr hpos).ne'
  have hnetop : ENNReal.ofReal (B - A) ≠ ∞ := ENNReal.ofReal_ne_top
  have h1 : ENNReal.ofReal lam * ENNReal.ofReal (B - A)
      < (ENNReal.ofReal (B - A)⁻¹ * I) * ENNReal.ofReal (B - A) :=
    ENNReal.mul_lt_mul_left hne0 hnetop h
  have h2 : ENNReal.ofReal (B - A)⁻¹ * ENNReal.ofReal (B - A) = 1 := by
    rw [ENNReal.ofReal_inv_of_pos hpos, ENNReal.inv_mul_cancel hne0 hnetop]
  refine le_of_lt (h1.trans_eq ?_)
  rw [mul_assoc, mul_comm I (ENNReal.ofReal (B - A)), ← mul_assoc, h2, one_mul]

/-- Elementary `ℝ≥0∞` manipulation: `ofReal lam * X ≤ I` implies `X ≤ (ofReal lam)⁻¹ * I`. -/
lemma le_inv_mul_of_mul_le {I X : ℝ≥0∞} {lam : ℝ} (hlam : 0 < lam)
    (h : ENNReal.ofReal lam * X ≤ I) : X ≤ (ENNReal.ofReal lam)⁻¹ * I := by
  have h0 : ENNReal.ofReal lam ≠ 0 := (ENNReal.ofReal_pos.mpr hlam).ne'
  have ht : ENNReal.ofReal lam ≠ ∞ := ENNReal.ofReal_ne_top
  calc X = 1 * X := (one_mul X).symm
    _ = ((ENNReal.ofReal lam)⁻¹ * ENNReal.ofReal lam) * X := by
        rw [ENNReal.inv_mul_cancel h0 ht]
    _ = (ENNReal.ofReal lam)⁻¹ * (ENNReal.ofReal lam * X) := by ring
    _ ≤ (ENNReal.ofReal lam)⁻¹ * I := mul_le_mul_right h _

/-- **Weak `(1,1)` type of the truncated maximal function.**  For the maximal function
restricted to intervals of length at most `N`, the level set `{x | lam < M_N f x}` has measure
at most `(4 / lam) ‖f‖₁`.  This is the quantitative core of the Hardy--Littlewood maximal
inequality, proved by a Vitali covering argument. -/
lemma volume_levelSet_truncMax_le (φ : ℝ → ℝ) {lam N : ℝ} (hlam : 0 < lam) :
    volume {x : ℝ | ENNReal.ofReal lam < hlTruncMax (fun y : ℝ => ‖φ y‖ₑ) x N}
      ≤ ENNReal.ofReal (4 / lam) * ∫⁻ y, ‖φ y‖ₑ := by
  set S : Set ℝ := {x : ℝ | ENNReal.ofReal lam < hlTruncMax (fun y : ℝ => ‖φ y‖ₑ) x N} with hS
  -- choose, for each point of `S`, a good interval of length at most `N`
  have hch : ∀ x : S, ∃ A B : ℝ, A ≤ x.1 ∧ x.1 ≤ B ∧ B - A ≤ N ∧
      ENNReal.ofReal lam < ENNReal.ofReal (B - A)⁻¹ * ∫⁻ y in Set.Icc A B, ‖φ y‖ₑ := by
    intro x
    have hx : ENNReal.ofReal lam < hlTruncMax (fun y : ℝ => ‖φ y‖ₑ) (x : ℝ) N := x.2
    simp only [hlTruncMax] at hx
    rcases lt_iSup_iff.mp hx with ⟨p, hp⟩
    exact ⟨p.1.1, p.1.2, p.2.1, p.2.2.1, p.2.2.2, hp⟩
  choose A B hAB using hch
  -- the interval is nondegenerate
  have hlt : ∀ x : S, A x < B x := by
    intro x
    obtain ⟨h1, h2, h3, h4⟩ := hAB x
    by_contra hcon
    have hcon' : B x ≤ A x := not_lt.mp hcon
    have hEq : B x - A x = 0 := by linarith
    have hz : ENNReal.ofReal (B x - A x)⁻¹ * (∫⁻ y in Set.Icc (A x) (B x), ‖φ y‖ₑ) = 0 := by
      rw [hEq, inv_zero, ENNReal.ofReal_zero, zero_mul]
    rw [hz] at h4
    exact absurd h4 (not_lt_of_ge (ENNReal.ofReal_pos.mpr hlam).le)
  -- the level-set hypothesis in the form used below
  have hkey : ∀ x : S,
      ENNReal.ofReal lam * volume (Set.Icc (A x) (B x)) ≤ ∫⁻ y in Set.Icc (A x) (B x), ‖φ y‖ₑ := by
    intro x
    have h := ofReal_mul_le_of_lt_mul_inv (I := ∫⁻ y in Set.Icc (A x) (B x), ‖φ y‖ₑ)
      (hlt x) (hAB x).2.2.2
    rwa [Real.volume_Icc]
  -- the family of intervals, described by centre and radius
  let c : S → ℝ := fun x => (A x + B x) / 2
  let r : S → ℝ := fun x => (B x - A x) / 2
  have hmem : ∀ x : S, x.1 ∈ Metric.closedBall (c x) (r x) := by
    intro x
    rw [Real.closedBall_eq_Icc]
    have h1 := (hAB x).1
    have h2 := (hAB x).2.1
    simp only [c, r]
    constructor <;> linarith
  have hrpos : ∀ x : S, 0 < r x := by
    intro x
    have h := hlt x
    simp only [r]
    linarith
  have hrle : ∀ x : S, r x ≤ N / 2 := by
    intro x
    have h := (hAB x).2.2.1
    simp only [r]
    linarith
  -- Vitali covering: extract a disjoint subfamily whose 4-dilates cover everything
  obtain ⟨u, -, hdisj, hcov⟩ := Vitali.exists_disjoint_subfamily_covering_enlargement_closedBall
    (t := Set.univ) c r (N / 2) (fun a _ => hrle a) 4 (by norm_num)
  have hballeq : ∀ x : S, Metric.closedBall (c x) (r x) = Set.Icc (A x) (B x) := by
    intro x
    rw [Real.closedBall_eq_Icc]
    congr 1 <;> · simp only [c, r]; ring
  have hcount : u.Countable := hdisj.countable_of_nonempty_interior fun i _ =>
    (Metric.nonempty_ball.mpr (hrpos i)).mono Metric.ball_subset_interior_closedBall
  have hcount' : Countable (↑u) := hcount.to_subtype
  have hSsub : S ⊆ ⋃ i ∈ u, Metric.closedBall (c i) (4 * r i) := by
    intro x hx
    obtain ⟨b, hbu, hb⟩ := hcov ⟨x, hx⟩ (Set.mem_univ _)
    exact Set.mem_iUnion.mpr ⟨b, Set.mem_iUnion.mpr ⟨hbu, hb (hmem ⟨x, hx⟩)⟩⟩
  -- volume of the dilates, in terms of the length of the intervals
  have hdil : ∀ b : u, volume (Metric.closedBall (c b) (4 * r b))
      = 4 * ENNReal.ofReal (B b - A b) := by
    intro b
    rw [Real.closedBall_eq_Icc, Real.volume_Icc]
    have : (c b + 4 * r b) - (c b - 4 * r b) = 4 * (B b - A b) := by
      simp only [c, r]; ring
    rw [this, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4), ENNReal.ofReal_ofNat]
  have hbd : ∀ b : u, ENNReal.ofReal (B b - A b)
      ≤ (ENNReal.ofReal lam)⁻¹ * ∫⁻ y in Set.Icc (A b) (B b), ‖φ y‖ₑ := by
    intro b
    have hb := hkey b
    rw [Real.volume_Icc] at hb
    exact le_inv_mul_of_mul_le hlam hb
  have hd : Pairwise (Function.onFun Disjoint fun b : u => Set.Icc (A b) (B b)) := by
    intro b1 b2 hne
    have hdd : Disjoint (Set.Icc (A b1) (B b1)) (Set.Icc (A b2) (B b2)) := by
      have h := hdisj b1.2 b2.2 (fun hh => hne (Subtype.ext hh))
      simpa only [Function.onFun, hballeq] using h
    exact hdd
  calc volume S
      ≤ ∑' b : u, volume (Metric.closedBall (c b) (4 * r b)) :=
        (measure_mono hSsub).trans (measure_biUnion_le volume hcount _)
    _ = ∑' b : u, 4 * ENNReal.ofReal (B b - A b) := by simp only [hdil]
    _ = 4 * ∑' b : u, ENNReal.ofReal (B b - A b) := ENNReal.tsum_mul_left
    _ ≤ 4 * ∑' b : u, (ENNReal.ofReal lam)⁻¹ * ∫⁻ y in Set.Icc (A b) (B b), ‖φ y‖ₑ :=
        mul_le_mul_right (ENNReal.tsum_le_tsum fun b => hbd b) 4
    _ = 4 * ((ENNReal.ofReal lam)⁻¹ * ∑' b : u, ∫⁻ y in Set.Icc (A b) (B b), ‖φ y‖ₑ) := by
        rw [ENNReal.tsum_mul_left]
    _ = (4 * (ENNReal.ofReal lam)⁻¹) * ∑' b : u, ∫⁻ y in Set.Icc (A b) (B b), ‖φ y‖ₑ := by
        ring
    _ = (4 * (ENNReal.ofReal lam)⁻¹) * ∫⁻ y in ⋃ b : u, Set.Icc (A b) (B b), ‖φ y‖ₑ := by
        rw [← @lintegral_iUnion ℝ u _ volume _ (fun b : u => Set.Icc (A b) (B b))
          (fun b => measurableSet_Icc) hd (fun y => ‖φ y‖ₑ)]
    _ ≤ (4 * (ENNReal.ofReal lam)⁻¹) * ∫⁻ y, ‖φ y‖ₑ := by
        refine mul_le_mul_right ?_ _
        simpa using lintegral_mono_set (μ := volume)
          (f := fun y : ℝ => ‖φ y‖ₑ) (Set.subset_univ (⋃ b : u, Set.Icc (A b) (B b)))
    _ = ENNReal.ofReal (4 / lam) * ∫⁻ y, ‖φ y‖ₑ := by
        rw [ENNReal.ofReal_div_of_pos hlam, ENNReal.ofReal_ofNat, div_eq_mul_inv]

/-- `ofReal (4 / lam) = 4 * (ofReal lam)⁻¹` for `lam > 0`. -/
lemma ofReal_four_div {lam : ℝ} (hlam : 0 < lam) :
    ENNReal.ofReal (4 / lam) = 4 * (ENNReal.ofReal lam)⁻¹ := by
  rw [ENNReal.ofReal_div_of_pos hlam, ENNReal.ofReal_ofNat, div_eq_mul_inv]

/-- Weak `(1,1)` type of the (centred) Hardy--Littlewood maximal function on `ℝ`:
for every `lam > 0`, the measure of the set where the maximal function exceeds `lam` is
bounded by `C / lam` times the `L¹` norm.  The maximal function is
`M f x = sup { (b-a)⁻¹ ∫_a^b |f| : a ≤ x ≤ b }`, stated in `ℝ≥0∞` (so that the
supremum is genuine). -/
theorem real_maximal_weak_type :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : ℝ → ℝ) (lam : ℝ), 0 < lam →
      (volume {x : ℝ | ENNReal.ofReal lam <
          ⨆ (a : ℝ) (b : ℝ) (_ : a ≤ x ∧ x ≤ b),
            ENNReal.ofReal (b - a)⁻¹ * ∫⁻ y in Set.Icc a b, ‖f y‖ₑ})
        ≤ ENNReal.ofReal (C / lam) * ∫⁻ x, ‖f x‖ₑ := by
  refine ⟨4, by norm_num, fun f lam hlam => ?_⟩
  change volume {x : ℝ | ENNReal.ofReal lam < hlMax (fun y : ℝ => ‖f y‖ₑ) x}
      ≤ ENNReal.ofReal (4 / lam) * ∫⁻ x, ‖f x‖ₑ
  -- the truncated level sets increase to the full level set
  have hsub : ∀ n : ℕ, {x : ℝ | ENNReal.ofReal lam < hlTruncMax (fun y : ℝ => ‖f y‖ₑ) x (n : ℝ)}
      ⊆ {x : ℝ | ENNReal.ofReal lam < hlMax (fun y : ℝ => ‖f y‖ₑ) x} := by
    intro n x hx
    have hx' : ENNReal.ofReal lam < hlTruncMax (fun y : ℝ => ‖f y‖ₑ) x (n : ℝ) := hx
    simp only [hlTruncMax] at hx'
    simp only [hlMax]
    refine lt_of_lt_of_le hx' (iSup_le fun p => ?_)
    exact le_iSup_of_le p.1.1 (le_iSup_of_le p.1.2 (le_iSup_of_le ⟨p.2.1, p.2.2.1⟩ le_rfl))
  have hsup : {x : ℝ | ENNReal.ofReal lam < hlMax (fun y : ℝ => ‖f y‖ₑ) x}
      ⊆ ⋃ n : ℕ, {x : ℝ | ENNReal.ofReal lam < hlTruncMax (fun y : ℝ => ‖f y‖ₑ) x (n : ℝ)} := by
    intro x hx
    have hx' : ENNReal.ofReal lam < hlMax (fun y : ℝ => ‖f y‖ₑ) x := hx
    simp only [hlMax] at hx'
    rcases lt_iSup_iff.mp hx' with ⟨a, ha⟩
    rcases lt_iSup_iff.mp ha with ⟨b, hb⟩
    rcases lt_iSup_iff.mp hb with ⟨hab, hval⟩
    refine Set.mem_iUnion.mpr ⟨Nat.ceil (b - a), ?_⟩
    simp only [hlTruncMax]
    refine lt_of_lt_of_le hval ?_
    exact le_iSup_of_le ⟨(a, b), hab.1, hab.2, Nat.le_ceil (b - a)⟩ le_rfl
  have hmono : Monotone fun n : ℕ =>
      {x : ℝ | ENNReal.ofReal lam < hlTruncMax (fun y : ℝ => ‖f y‖ₑ) x (n : ℝ)} := by
    intro m n hmn x hx
    have hx' : ENNReal.ofReal lam < hlTruncMax (fun y : ℝ => ‖f y‖ₑ) x (m : ℝ) := hx
    simp only [hlTruncMax] at hx'
    simp only [hlTruncMax]
    refine lt_of_lt_of_le hx' (iSup_le fun p => ?_)
    exact le_iSup_of_le ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.trans (by exact_mod_cast hmn)⟩ le_rfl
  calc volume {x : ℝ | ENNReal.ofReal lam < hlMax (fun y : ℝ => ‖f y‖ₑ) x}
      = volume (⋃ n : ℕ, {x : ℝ | ENNReal.ofReal lam < hlTruncMax (fun y : ℝ => ‖f y‖ₑ) x (n : ℝ)}) := by
        rw [Set.Subset.antisymm hsup (Set.iUnion_subset hsub)]
    _ = ⨆ n : ℕ, volume {x : ℝ | ENNReal.ofReal lam < hlTruncMax (fun y : ℝ => ‖f y‖ₑ) x (n : ℝ)} :=
        Monotone.measure_iUnion hmono
    _ ≤ ENNReal.ofReal (4 / lam) * ∫⁻ y, ‖f y‖ₑ :=
        iSup_le fun n : ℕ => volume_levelSet_truncMax_le f hlam

end Commons.Analysis.Maximal