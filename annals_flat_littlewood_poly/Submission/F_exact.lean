import Mathlib
import Submission.LMAux
import Submission.F_diag
import Submission.F_compact

/-!
Exact partial-coloring in the Euclidean-space setting (child task).

TASK: prove `exact_coloring` below.  Add helpers above as needed.

STATEMENT.  For n ≥ 1, x0 ∈ [-1,1]^n, nonzero vectors v : ι → Vec n and
thresholds c ≥ 0 with Σ exp (-(c j)²/16) ≤ n/16, there is x : Vec n with
  · |x i| ≤ 1 for every coordinate,
  · |⟨x − x0, v j⟩| ≤ c j ‖v j‖ for every row j,
  · at least ⌈n/2⌉ = (n+1)/2 coordinates are EXACTLY ±1:
      ((n + 1) / 2 : ℕ) ≤ Fintype.card {i : Fin n // x i = 1 ∨ x i = -1}.

ROUTE (compactness / diagonal limit).
 1. Use `diag_eps` (Submission.F_diag; needs hn hx0 hc hne hsum) to get a
    sequence xseq : ℕ → Vec n with δ_k := 1/((k:ℝ)+10) and
      (a) ∀ k i, |xseq k i| ≤ 1
      (b) ∀ k j, |⟨xseq k − x0, v j⟩| ≤ c j ‖v j‖
      (c) ∀ k, (n:ℝ)/2 ≤ ((frozenVars δ_k (xseq k)).card : ℝ).
 2. Apply `exists_subseq_limit_coord` (Submission.F_compact) to
    a k i := (xseq k) i  (bounded by (a)); get φ strictly monotone and
    x* : Fin n → ℝ with coordinates in [-1,1] and, for every i,
    Tendsto (fun k => (xseq (φ k)) i) atTop (𝓝 (x* i)).
    Put xV : Vec n := toV x*  (so (xV) i = x* i, by `toV_apply`).
 3. Rows pass to the limit: for each j, the real sequences
    `vin (xseq (φ k) - x0) (v j)` are bounded by c j ‖v j‖ (by (b)) and
    converge to `vin (xV - x0) (v j)` because vin is a finite sum of products
    of coordinates (vin_sum : vin a b = Σ i, a i * b i) and each coordinate
    converges; hence |⟨xV − x0, v j⟩| ≤ c j ‖v j‖
    (use `le_of_tendsto_of_tendsto`/`tendsto_finset_sum`, or prove the row set
    is closed and the sequence converges in norm — your choice; you may first
    show norm-convergence ‖xseq (φ k) − xV‖ → 0 from the coordinatewise
    convergence using ‖u‖ ≤ Σ i |u i| (from norm_sq_sum) and
    `tendsto_finset_sum`).
 4. Coordinates |(xV) i| ≤ 1 from the compactness statement (Icc membership).
 5. Frozen counts pass to the limit: for every k₀ : ℕ,
        (n:ℝ)/2 ≤ ((frozenVars δ_{k₀} (xV)).card : ℝ)
    Proof idea: fix k₀.  Since φ is strictly monotone, φ l → ∞; for l large
    (φ l ≥ k₀) we have δ_{φ l} ≤ δ_{k₀}, so
    frozenVars δ_{k₀} y ⊇ frozenVars δ_{φ l} y for every y, hence
    |frozenVars δ_{k₀} (xseq (φ l))| ≥ |frozenVars δ_{φ l} (xseq (φ l))| ≥ n/2
    for all large l (by (c)).  Now for coordinates i with |(xV) i| < 1 − δ_{k₀}
    (the complement of frozenVars δ_{k₀} (xV)) the sequence |(xseq (φ l)) i|
    converges to |(xV) i|, so for large l it is also < 1 − δ_{k₀}, i.e.
    i ∉ frozenVars δ_{k₀} (xseq (φ l)).  Since there are finitely many such i,
    one l₀ works for all of them; then for l = l₀
        frozenVars δ_{k₀} (xseq (φ l₀)) ⊆ frozenVars δ_{k₀} (xV),
    so n/2 ≤ the smaller set's size ≤ the bigger one.  (Alternatively show the
    sets {y | n/2 ≤ |frozenVars δ y|} are closed in the product topology and
    use the limit — your choice.)
 6. Count exactly-±1 coordinates.  Let B : Finset (Fin n) :=
    Finset.univ.filter (fun i => (xV) i = 1 ∨ (xV) i = -1).
    From step 5, |frozenVars δ_k (xV)| ≥ n/2 for every k.
    For i ∉ B: |(xV) i| < 1 (coords are in [-1,1]), so pick K_i with
    δ_{K_i} < 1 − |(xV) i| (δ_k = 1/(k+10) → 0: exists by archimedean/`exists_nat_gt`).
    Let K := max of K_i over i ∉ B (finite max, or pick one K ≥ all K_i).
    Then for every i ∉ B and k ≥ K: δ_k ≤ δ_K < 1 − |(xV) i|, so
    i ∉ frozenVars δ_k (xV); hence frozenVars δ_K (xV) ⊆ B.
    So |B| ≥ |frozenVars δ_K (xV)| ≥ n/2.  Since |B| is an integer and
    |B| ≤ n, conclude (n:ℝ)/2 ≤ (|B| : ℝ) implies ((n+1)/2 : ℕ) ≤ |B|
    (nlinarith/omega; then `Fintype.card {i // ...} = |B|` by simp).
 7. Return x := xV.
-/

open scoped BigOperators RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Filter

noncomputable section
open Classical

namespace Submission.Discrepancy

/-- If δ' ≤ δ then the frozen set at level δ' is contained in that at level δ. -/
lemma frozenVars_subset_of_delta_le {n : ℕ} {δ δ' : ℝ} {x : Vec n} (h : δ' ≤ δ) :
    frozenVars δ' x ⊆ frozenVars δ x := by
  intro i hi
  have hi' : 1 - δ' ≤ |x i| := by
    simpa [frozenVars, Finset.mem_univ, Finset.mem_filter] using hi
  have hthr : 1 - δ ≤ 1 - δ' := by linarith
  unfold frozenVars
  simp only [Finset.mem_univ, Finset.mem_filter, true_and]
  exact le_trans hthr hi'

/-- A strictly monotone sequence of naturals dominates the identity. -/
lemma self_le_strictMono {φ : ℕ → ℕ} (hφ : StrictMono φ) : ∀ k : ℕ, k ≤ φ k := by
  intro k
  induction k with
  | zero => exact Nat.zero_le (φ 0)
  | succ k ih =>
      exact Nat.succ_le_of_lt (lt_of_le_of_lt ih (hφ (Nat.lt_succ_self k)))

/-- δ_k = 1/(k+10) is decreasing. -/
lemma delta_decreasing {k l : ℕ} (h : k ≤ l) :
    1 / ((l : ℝ) + 10) ≤ 1 / ((k : ℝ) + 10) := by
  have hk : 0 < (k : ℝ) + 10 := by positivity
  have hkl : (k : ℝ) + 10 ≤ (l : ℝ) + 10 := by
    have h' : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast h
    linarith
  exact one_div_le_one_div_of_le hk hkl

/-- Archimedean: δ_k = 1/(k+10) eventually drops below any positive ε. -/
lemma exists_nat_gt_inv {ε : ℝ} (hε : 0 < ε) : ∃ K : ℕ, 1 / ((K : ℝ) + 10) < ε := by
  rcases exists_nat_gt (1 / ε) with ⟨K, hK⟩
  refine ⟨K, ?_⟩
  have hK10 : 0 < (K : ℝ) + 10 := by positivity
  have hlt : 1 / ε < (K : ℝ) + 10 := by
    have h' : (K : ℝ) ≤ (K : ℝ) + 10 := by linarith
    linarith
  have h1 : 1 < ((K : ℝ) + 10) * ε := by
    have hm := mul_lt_mul_of_pos_right hlt hε
    simpa [inv_mul_cancel₀ hε.ne'] using hm
  rw [div_lt_iff₀ hK10]
  simpa [mul_comm] using h1

/-- Frozen counts pass to coordinatewise limits: if a subsequence `xseq (φ k)`
converges coordinatewise to `xV` and each term has ≥ n/2 coordinates frozen at
its own level `δ (φ k)`, then the limit has ≥ n/2 coordinates frozen at level
`δ k₀` for every `k₀` (here δ : ℕ → ℝ is decreasing). -/
lemma frozen_card_limit {n : ℕ} (xseq : ℕ → Vec n) (xV : Vec n) (φ : ℕ → ℕ)
    (hφ : StrictMono φ) (δ : ℕ → ℝ)
    (hδdec : ∀ {a b : ℕ}, a ≤ b → δ b ≤ δ a)
    (hconv : ∀ i : Fin n, Tendsto (fun k : ℕ => (xseq (φ k)) i) atTop (𝓝 (xV i)))
    (hfr : ∀ k : ℕ, (n : ℝ) / 2 ≤ ((frozenVars (δ k) (xseq k)).card : ℝ)) :
    ∀ k₀ : ℕ, (n : ℝ) / 2 ≤ ((frozenVars (δ k₀) xV).card : ℝ) := by
  intro k₀
  have hnot_ev : ∀ i : Fin n, |xV i| < 1 - δ k₀ →
      ∀ᶠ k : ℕ in atTop, |(xseq (φ k)) i| < 1 - δ k₀ := by
    intro i hlt
    have hc : Tendsto (fun k : ℕ => |(xseq (φ k)) i|) atTop (𝓝 |xV i|) := (hconv i).abs
    exact (tendsto_order.1 hc).2 (1 - δ k₀) hlt
  let Bad : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => |xV i| < 1 - δ k₀)
  have hbadev : ∀ i ∈ Bad, ∀ᶠ k : ℕ in atTop, |(xseq (φ k)) i| < 1 - δ k₀ := by
    intro i hi
    exact hnot_ev i (by simpa [Bad] using hi)
  have hbadev' : ∀ᶠ k : ℕ in atTop, ∀ i ∈ Bad, |(xseq (φ k)) i| < 1 - δ k₀ := by
    exact (eventually_all_finset Bad).2 hbadev
  rcases (eventually_atTop).1 hbadev' with ⟨N, hN⟩
  let k₁ : ℕ := max N k₀
  have hNk₁ : N ≤ k₁ := le_max_left N k₀
  have hk₀k₁ : k₀ ≤ k₁ := le_max_right N k₀
  have hφk₁ : k₀ ≤ φ k₁ := le_trans hk₀k₁ (self_le_strictMono hφ k₁)
  have hδφ : δ (φ k₁) ≤ δ k₀ := hδdec hφk₁
  have hA : (n : ℝ) / 2 ≤ ((frozenVars (δ k₀) (xseq (φ k₁))).card : ℝ) := by
    have hfr' : (n : ℝ) / 2 ≤ ((frozenVars (δ (φ k₁)) (xseq (φ k₁))).card : ℝ) := hfr (φ k₁)
    have hsub : frozenVars (δ (φ k₁)) (xseq (φ k₁)) ⊆ frozenVars (δ k₀) (xseq (φ k₁)) :=
      frozenVars_subset_of_delta_le hδφ
    exact le_trans hfr' (by exact_mod_cast (Finset.card_le_card hsub))
  have hB : frozenVars (δ k₀) (xseq (φ k₁)) ⊆ frozenVars (δ k₀) xV := by
    intro i hi
    by_contra hni
    have hnle : ¬ 1 - δ k₀ ≤ |xV i| := by
      simpa [frozenVars, Finset.mem_univ, Finset.mem_filter] using hni
    have hlt : |xV i| < 1 - δ k₀ := not_le.mp hnle
    have hiBad : i ∈ Bad := by
      simp [Bad, hlt]
    have hval : |(xseq (φ k₁)) i| < 1 - δ k₀ := hN k₁ hNk₁ i hiBad
    have hle : 1 - δ k₀ ≤ |(xseq (φ k₁)) i| := by
      simpa [frozenVars, Finset.mem_univ, Finset.mem_filter] using hi
    exact (not_lt_of_ge hle) hval
  exact le_trans hA (by exact_mod_cast (Finset.card_le_card hB))

/-- Cardinality of a subtype over a predicate equals the cardinality of the
corresponding filter of `univ`. -/
lemma card_eq_filter {n : ℕ} (p : Fin n → Prop) [DecidablePred p] :
    Fintype.card {i : Fin n // p i} = (Finset.univ.filter p).card := by
  simp [Fintype.card_subtype]

/-- Integer rounding: (n : ℝ)/2 ≤ (r : ℝ) forces (n+1)/2 ≤ r for naturals. -/
lemma half_le_card {n r : ℕ} (h : n ≤ 2 * r) : (n + 1) / 2 ≤ r := by
  omega

/-- Exact partial coloring over nonzero vectors. -/
theorem exact_coloring {ι : Type*} [Fintype ι] (n : ℕ) (x0 : Vec n) (v : ι → Vec n)
    (c : ι → ℝ) (hn : 1 ≤ n) (hx0 : ∀ i : Fin n, |x0 i| ≤ 1) (hc : ∀ j : ι, 0 ≤ c j)
    (hne : ∀ j : ι, ‖v j‖ ≠ 0) (hsum : ∑ j : ι, Real.exp (-(c j) ^ 2 / 16) ≤ (n : ℝ) / 16) :
    ∃ x : Vec n,
      (∀ i : Fin n, |x i| ≤ 1) ∧
      (∀ j : ι, |vin (x - x0) (v j)| ≤ c j * ‖v j‖) ∧
      (((n + 1) / 2 : ℕ) ≤ Fintype.card {i : Fin n // x i = 1 ∨ x i = -1}) := by
  -- 1. diagonal sequence from the ε-version
  rcases diag_eps (n := n) x0 v c hn hx0 hc hne hsum with ⟨xseq, hxseq1, hxseqrow, hxseqfrozen⟩
  -- 2. coordinatewise convergent subsequence
  let a : ℕ → Fin n → ℝ := fun k i => xseq k i
  have ha : ∀ k : ℕ, ∀ i : Fin n, a k i ∈ Set.Icc (-1) 1 := by
    intro k i
    exact abs_le.mp (hxseq1 k i)
  rcases exists_subseq_limit_coord n a ha with ⟨φ, hφmono, xs, hxs, hconv⟩
  let xV : Vec n := toV xs
  have hcoord : ∀ i : Fin n, Tendsto (fun k : ℕ => (xseq (φ k)) i) atTop (𝓝 (xV i)) := by
    intro i
    simpa [a, xV] using hconv i
  -- 4. coordinates of xV in [-1,1]
  have hxVb : ∀ i : Fin n, |xV i| ≤ 1 := by
    intro i
    have hmem : xs i ∈ Set.Icc (-1) 1 := hxs i
    have hb : |xs i| ≤ 1 := abs_le.mpr hmem
    simpa [xV] using hb
  -- 3. rows pass to the limit
  have hrowlim : ∀ j : ι,
      Tendsto (fun k : ℕ => vin (xseq (φ k) - x0) (v j)) atTop (𝓝 (vin (xV - x0) (v j))) := by
    intro j
    have hterm : ∀ i : Fin n,
        Tendsto (fun k : ℕ => ((xseq (φ k)) i - x0 i) * (v j) i)
          atTop (𝓝 ((xV i - x0 i) * (v j) i)) := by
      intro i
      have hsub : Tendsto (fun k : ℕ => (xseq (φ k)) i - x0 i) atTop (𝓝 (xV i - x0 i)) :=
        (hcoord i).sub (tendsto_const_nhds (x := x0 i))
      exact hsub.mul (tendsto_const_nhds (x := (v j) i))
    have hsum : Tendsto (fun k : ℕ => ∑ i : Fin n, ((xseq (φ k)) i - x0 i) * (v j) i)
        atTop (𝓝 (∑ i : Fin n, (xV i - x0 i) * (v j) i)) := by
      simpa using (tendsto_finsetSum (s := (Finset.univ : Finset (Fin n)))
        (f := fun (i : Fin n) (k : ℕ) => ((xseq (φ k)) i - x0 i) * (v j) i)
        (a := fun (i : Fin n) => (xV i - x0 i) * (v j) i)
        (fun i hi => hterm i))
    have h1 : (fun k : ℕ => vin (xseq (φ k) - x0) (v j)) =
        fun k : ℕ => ∑ i : Fin n, ((xseq (φ k)) i - x0 i) * (v j) i := by
      funext k
      rw [vin_sum]
      simp
    have h2 : vin (xV - x0) (v j) = ∑ i : Fin n, (xV i - x0 i) * (v j) i := by
      rw [vin_sum]
      simp
    rw [h1, h2]
    exact hsum
  have hxVrow : ∀ j : ι, |vin (xV - x0) (v j)| ≤ c j * ‖v j‖ := by
    intro j
    exact le_of_tendsto_of_tendsto (hrowlim j).abs tendsto_const_nhds
      (Eventually.of_forall (fun k => hxseqrow (φ k) j))
  -- 5. frozen counts pass to the limit
  let δ : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 10)
  have hfr : ∀ k₀ : ℕ, (n : ℝ) / 2 ≤ ((frozenVars (δ k₀) xV).card : ℝ) := by
    exact frozen_card_limit xseq xV φ hφmono δ
      (fun {a b : ℕ} (hab : a ≤ b) => delta_decreasing hab) hcoord
      (fun k => by simpa [δ] using hxseqfrozen k)
  -- 6. count exactly-±1 coordinates
  let B : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => xV i = 1 ∨ xV i = -1)
  have hBabs : ∀ i : Fin n, i ∉ B → |xV i| < 1 := by
    intro i hiB
    have hle : |xV i| ≤ 1 := hxVb i
    by_contra hnot
    have hge : 1 ≤ |xV i| := le_of_not_gt hnot
    have habs : |xV i| = 1 := le_antisymm hle hge
    have hcases : xV i = 1 ∨ xV i = -1 := eq_or_eq_neg_of_abs_eq habs
    have hmem : i ∈ B := by
      simp [B, hcases]
    exact hiB hmem
  let Bad2 : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => i ∉ B)
  have hdev : ∀ i ∈ Bad2, ∀ᶠ k : ℕ in atTop, 1 / ((k : ℝ) + 10) < 1 - |xV i| := by
    intro i hi
    have hiB : i ∉ B := by simpa [Bad2] using hi
    have hlt1 : |xV i| < 1 := hBabs i hiB
    have hε : 0 < 1 - |xV i| := by linarith
    rcases exists_nat_gt_inv hε with ⟨K, hK⟩
    rw [eventually_atTop]
    refine ⟨K, ?_⟩
    intro k hk
    have hmono : 1 / ((k : ℝ) + 10) ≤ 1 / ((K : ℝ) + 10) := delta_decreasing hk
    exact lt_of_le_of_lt hmono hK
  have hdev' : ∀ᶠ k : ℕ in atTop, ∀ i ∈ Bad2, 1 / ((k : ℝ) + 10) < 1 - |xV i| := by
    exact (eventually_all_finset Bad2).2 hdev
  rcases (eventually_atTop).1 hdev' with ⟨K, hK⟩
  have hsubB : frozenVars (δ K) xV ⊆ B := by
    intro i hi
    by_contra hiB
    have hiB2 : i ∈ Bad2 := by
      simp [Bad2, hiB]
    have hsmall : 1 / ((K : ℝ) + 10) < 1 - |xV i| := hK K le_rfl i hiB2
    have hnf : i ∉ frozenVars (δ K) xV := by
      intro hmem
      have hle : 1 - 1 / ((K : ℝ) + 10) ≤ |xV i| := by
        simpa [frozenVars, Finset.mem_univ, Finset.mem_filter, δ] using hmem
      linarith
    exact hnf hi
  have hc1 : (n : ℝ) / 2 ≤ ((frozenVars (δ K) xV).card : ℝ) := hfr K
  have hc2 : (n : ℝ) / 2 ≤ (B.card : ℝ) :=
    le_trans hc1 (by exact_mod_cast (Finset.card_le_card hsubB))
  have hnatc : (n + 1) / 2 ≤ B.card := by
    have h2 : (n : ℝ) ≤ 2 * (B.card : ℝ) := by linarith
    have hnat : n ≤ 2 * B.card := by
      exact_mod_cast h2
    exact half_le_card hnat
  refine ⟨xV, hxVb, hxVrow, ?_⟩
  have hcard : Fintype.card {i : Fin n // xV i = 1 ∨ xV i = -1} = B.card := by
    simpa [B] using card_eq_filter (p := fun i : Fin n => xV i = 1 ∨ xV i = -1)
  rw [hcard]
  exact hnatc

end Discrepancy

end Submission
