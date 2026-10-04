import Submission.Length

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Riemannian distance

This module introduces the **Riemannian distance** on a manifold with a Riemannian metric, as the
infimum of the lengths of piecewise smooth paths.

## Design

A *piecewise smooth path* (`PwPath I x y`) from `x` to `y` is a finite list of globally `C¹` curves
`c 0, …, c N : ℝ → M`, traversed on the parameter intervals `[a i, b i]` and joined end to end
(`c i (b i) = c (i+1) (a (i+1))`), starting at `x` and ending at `y`.  Its **length**
(`PwPath.length`) is the sum `∑ i ≤ N, ∫_{a i}^{b i} ‖c i'‖`.  Indexing the pieces by `ℕ` with an
explicit bound `N` makes the concatenation `PwPath.trans` of two paths — the key step for the
triangle inequality — a purely arithmetic operation on indices, and makes the length of a
concatenation the sum of the lengths (`PwPath.length_trans`, from `Finset.sum_range_add`).  No
reparametrisation of curves is needed anywhere in the construction.

## Main results

* `PwPath.length_nonneg`, `PwPath.length_refl`, `PwPath.trans`, `PwPath.length_trans`;
* `PwPath.ofCurve` / `PwPath.length_ofCurve`: a single smooth curve is a path with one piece;
* `riemannianDist` (the infimum of the lengths), `riemannianDist_nonneg`, `riemannianDist_self`;
* `riemannianDist_le_length`, `riemannianDist_le_curveLength`: every path/curve gives an upper bound;
* `riemannianDist_triangle`: the triangle inequality, for two points joined by a piecewise smooth
  path (the statement takes `PwLengthSet I x y` and `PwLengthSet I y z` nonempty);
* `contMDiffAt_chartGram`, `continuousAt_chartGram`: the chart metric is smooth (hence continuous)
  in the base point on the chart — the first ingredient for comparing the distance with the
  topology;
* `chartGram_self_apply`: at the base point the chart metric is the Euclidean scalar product.

## Next steps

1. **Existence of paths.**  In a connected manifold any two points are joined by a piecewise smooth
   path; for this, a locally `C¹` curve inside a chart must be extended to a globally `C¹` curve
   (clamp the parameter with a smooth function whose range lies in the chart where the curve is
   `C¹`).  With that, `riemannianDist_triangle` becomes unconditional on a connected `M`, and
   `riemannianDist` is a metric.
2. **Comparison with the topology.**  From `continuousAt_chartGram` and
   `Commons.Analysis.Calculus.norm_sub_le_intervalIntegral_norm_deriv`: a curve inside a chart and
   staying in a ball of radius `r` has length `≥ √λ · |u(b) - u(a)|`, where `λ > 0` is a lower
   bound for the chart metric on the ball (from `chartGram_self_apply` + continuity).  This gives
   `riemannianDist x y > 0` for `x ≠ y` and the two-sided local comparison with the chart metric
   (hence that `riemannianDist` induces the topology).  The upper bound uses the coordinate straight
   line and `curveSpeed_chartCurve`.
3. **Local minimality of geodesics**: `riemannianDist x₀ (expMap x₀ v) = ‖v‖_{x₀}` for small `v`,
   from Gauss's lemma (`gauss_lemma_radial_metric`), and then Hopf–Rinow for compact `M`.

## Gotchas

* `I` must not be rebound as an explicit parameter of a definition whose body uses `PwPath I x y`:
  the section's instance hypotheses are about the *section's* `I`, so instance synthesis for the
  structure's `RiemannianBundle`/`NormedAddCommGroup` arguments fails.  Definitions are therefore
  written with `I` as an auto-implicit argument (occurring in the value), and used as
  `PwLengthSet (I := I) x y`, `riemannianDist (I := I) x y`, ….
* `Set ℝ` has pointwise addition only with `open scoped Pointwise`.
* `csInf_le_csInf'` requires `ConditionallyCompleteLinearOrderBot ℝ`, which does not exist; use
  `csInf_le_csInf` (which needs a `BddBelow` of the *ambient* set) and `csInf_add`.
* `Real.sInf_nonneg` (not `le_csInf`) is the convenient way to prove `0 ≤ sInf` (it also covers the
  empty set).
-/
set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem
open scoped Manifold ContDiff Bundle Topology BigOperators Pointwise
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Submission.Geodesic
open Submission.ChartConnection
open Submission.Length
open Submission.Gauss

namespace Submission.Distance

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

variable {x y z : M}

noncomputable section

/-- A **piecewise smooth path** from `x` to `y`: finitely many globally `C¹` curves, traversed on
the parameter intervals `[a i, b i]` and joined end to end. -/
structure PwPath (I : ModelWithCorners ℝ E H) (x y : M) where
  /-- the index of the last piece -/
  N : ℕ
  c : ℕ → ℝ → M
  a : ℕ → ℝ
  b : ℕ → ℝ
  hab : ∀ i, a i ≤ b i
  hsmooth : ∀ i, ContMDiff 𝓘(ℝ) I 1 (c i)
  hjoin : ∀ i, i < N → c i (b i) = c (i + 1) (a (i + 1))
  hx : c 0 (a 0) = x
  hy : c N (b N) = y

/-- The **length** of a piecewise smooth path. -/
def PwPath.length (p : PwPath I x y) : ℝ :=
  ∑ i ∈ Finset.range (p.N + 1), (∫ s in (p.a i)..(p.b i), curveSpeed (I := I) (p.c i) s)

lemma PwPath.length_nonneg (p : PwPath I x y) : 0 ≤ p.length :=
  Finset.sum_nonneg fun i _ =>
    intervalIntegral.integral_nonneg_of_forall (p.hab i)
      fun s => curveSpeed_nonneg (I := I) (p.c i) s

/-- The constant path. -/
def PwPath.refl (x : M) : PwPath I x x where
  N := 0
  c := fun _ _ => x
  a := fun _ => 0
  b := fun _ => 0
  hab := fun _ => le_rfl
  hsmooth := fun _ => contMDiff_const
  hjoin := by intro i hi; exact absurd hi (Nat.not_lt_zero i)
  hx := rfl
  hy := rfl

lemma PwPath.length_refl (x : M) : (PwPath.refl (I := I) x).length = 0 := by
  simp only [PwPath.length, PwPath.refl, Finset.range_one, Finset.sum_singleton]
  simp

/-! ## Concatenation of paths -/

/-- **Concatenation of piecewise smooth paths.** -/
def PwPath.trans (p : PwPath I x y) (q : PwPath I y z) : PwPath I x z where
  N := p.N + q.N + 1
  c := fun k => if k ≤ p.N then p.c k else q.c (k - p.N - 1)
  a := fun k => if k ≤ p.N then p.a k else q.a (k - p.N - 1)
  b := fun k => if k ≤ p.N then p.b k else q.b (k - p.N - 1)
  hab := by
    intro k
    by_cases h : k ≤ p.N
    · simpa only [if_pos h] using p.hab k
    · simpa only [if_neg h] using q.hab (k - p.N - 1)
  hsmooth := by
    intro k
    by_cases h : k ≤ p.N
    · simpa only [if_pos h] using p.hsmooth k
    · simpa only [if_neg h] using q.hsmooth (k - p.N - 1)
  hjoin := by
    intro k hk
    by_cases h1 : k < p.N
    · have h2 : k + 1 ≤ p.N := by omega
      simp only [if_pos (le_of_lt h1), if_pos h2]
      exact p.hjoin k h1
    · by_cases h2 : k = p.N
      · subst h2
        have h3 : ¬ (p.N + 1 ≤ p.N) := by omega
        have h4 : p.N + 1 - p.N - 1 = 0 := by omega
        simp only [if_pos le_rfl, if_neg h3, h4]
        rw [p.hy]
        exact q.hx.symm
      · have h3 : ¬ (k ≤ p.N) := by omega
        have h4 : ¬ (k + 1 ≤ p.N) := by omega
        have h5 : k + 1 - p.N - 1 = (k - p.N - 1) + 1 := by omega
        simp only [if_neg h3, if_neg h4, h5]
        exact q.hjoin (k - p.N - 1) (by omega)
  hx := by
    have h : (0 : ℕ) ≤ p.N := Nat.zero_le _
    simp only [if_pos h]
    exact p.hx
  hy := by
    have h : ¬ (p.N + q.N + 1 ≤ p.N) := by omega
    have hidx : p.N + q.N + 1 - p.N - 1 = q.N := by omega
    simp only [if_neg h, hidx]
    exact q.hy

lemma PwPath.trans_c_apply_left (p : PwPath I x y) (q : PwPath I y z)
    {k : ℕ} (hk : k ≤ p.N) : (p.trans q).c k = p.c k := if_pos hk
lemma PwPath.trans_a_apply_left (p : PwPath I x y) (q : PwPath I y z)
    {k : ℕ} (hk : k ≤ p.N) : (p.trans q).a k = p.a k := if_pos hk
lemma PwPath.trans_b_apply_left (p : PwPath I x y) (q : PwPath I y z)
    {k : ℕ} (hk : k ≤ p.N) : (p.trans q).b k = p.b k := if_pos hk
lemma PwPath.trans_c_apply_right (p : PwPath I x y) (q : PwPath I y z)
    {k : ℕ} (hk : ¬ k ≤ p.N) : (p.trans q).c k = q.c (k - p.N - 1) := if_neg hk
lemma PwPath.trans_a_apply_right (p : PwPath I x y) (q : PwPath I y z)
    {k : ℕ} (hk : ¬ k ≤ p.N) : (p.trans q).a k = q.a (k - p.N - 1) := if_neg hk
lemma PwPath.trans_b_apply_right (p : PwPath I x y) (q : PwPath I y z)
    {k : ℕ} (hk : ¬ k ≤ p.N) : (p.trans q).b k = q.b (k - p.N - 1) := if_neg hk

/-- **The length of a concatenation is the sum of the lengths.** -/
theorem PwPath.length_trans (p : PwPath I x y) (q : PwPath I y z) :
    (p.trans q).length = p.length + q.length := by
  have hterm : ∀ k : ℕ, (∫ s in ((p.trans q).a k)..((p.trans q).b k),
      curveSpeed (I := I) ((p.trans q).c k) s)
      = if k ≤ p.N then ∫ s in (p.a k)..(p.b k), curveSpeed (I := I) (p.c k) s
        else ∫ s in (q.a (k - p.N - 1))..(q.b (k - p.N - 1)),
          curveSpeed (I := I) (q.c (k - p.N - 1)) s := by
    intro k
    by_cases h : k ≤ p.N
    · rw [if_pos h, PwPath.trans_a_apply_left p q h, PwPath.trans_b_apply_left p q h,
        PwPath.trans_c_apply_left p q h]
    · rw [if_neg h, PwPath.trans_a_apply_right p q h, PwPath.trans_b_apply_right p q h,
        PwPath.trans_c_apply_right p q h]
  have hN : (p.trans q).N + 1 = (p.N + 1) + (q.N + 1) := by
    show p.N + q.N + 1 + 1 = (p.N + 1) + (q.N + 1)
    omega
  simp only [PwPath.length, hN]
  rw [Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun k hk => ?_
    simp only [Finset.mem_range] at hk
    rw [hterm k, if_pos (by omega)]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [hterm (p.N + 1 + j), if_neg (by omega)]
    have hidx : p.N + 1 + j - p.N - 1 = j := by omega
    rw [hidx]

/-! ## The Riemannian distance -/

/-- The set of lengths of piecewise smooth paths from `x` to `y`. -/
def PwLengthSet (x y : M) : Set ℝ :=
  Set.range (fun p : PwPath I x y => p.length)

/-- A single globally `C¹` curve from `x` to `y` is a piecewise smooth path. -/
def PwPath.ofCurve (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ) I 1 γ) (x y : M)
    (hx : γ 0 = x) (hy : γ 1 = y) : PwPath I x y where
  N := 0
  c := fun _ => γ
  a := fun _ => 0
  b := fun _ => 1
  hab := fun _ => zero_le_one
  hsmooth := fun _ => hγ
  hjoin := fun i hi => absurd hi (Nat.not_lt_zero i)
  hx := hx
  hy := hy

lemma PwPath.length_ofCurve (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ) I 1 γ) (x y : M)
    (hx : γ 0 = x) (hy : γ 1 = y) :
    (PwPath.ofCurve (I := I) γ hγ x y hx hy).length = curveLength (I := I) γ 0 1 := by
  have h : (PwPath.ofCurve (I := I) γ hγ x y hx hy).length = curveLength (I := I) γ 0 1 := by
    simp only [PwPath.length, PwPath.ofCurve, curveLength]
    norm_num
  exact h

/-! ## Smoothness of the chart metric in the base point

These are the first ingredients of the comparison between the Riemannian distance and the manifold
topology: the chart metric `chartGram x₀ · a b` is smooth (hence continuous) in the base point on
the chart, and at the base point `x₀` it is the Euclidean scalar product. -/

/-- The chart metric is smooth in the base point, on the chart at `x₀`. -/
lemma contMDiffAt_chartGram (x₀ : M) (a b : E) {x : M} (hx : x ∈ (chartAt H x₀).source) :
    CMDiffAt ∞ (fun q : M => chartGram (I := I) x₀ q a b) x :=
  ContMDiffAt.inner_bundle (contMDiffAt_frameSection (I := I) x₀ a hx)
    (contMDiffAt_frameSection (I := I) x₀ b hx)

lemma continuousAt_chartGram (x₀ : M) (a b : E) {x : M} (hx : x ∈ (chartAt H x₀).source) :
    ContinuousAt (fun q : M => chartGram (I := I) x₀ q a b) x :=
  (contMDiffAt_chartGram (I := I) x₀ a b hx).continuousAt

/-- At the base point the chart metric is the Euclidean scalar product of the coordinates: this is
the identity `frameVector x₀ x₀ v = v`.  (The statement below records the equality of the two
inner products in the form in which it is used.) -/
lemma chartGram_self_apply [I.Boundaryless] (x₀ : M) (v w : E) :
    chartGram (I := I) x₀ x₀ v w
      = inner ℝ (show TangentSpace I x₀ from v) (show TangentSpace I x₀ from w) := by
  rw [chartGram_apply, frameVector_self, frameVector_self]

/-- A single globally `C¹` curve from `x` to `y` is a piecewise smooth path. -/
lemma PwLengthSet.nonneg (x y : M) : ∀ r ∈ PwLengthSet (I := I) x y, 0 ≤ r := by
  rintro r ⟨p, rfl⟩
  exact PwPath.length_nonneg p

lemma PwLengthSet.bddBelow (x y : M) : BddBelow (PwLengthSet (I := I) x y) :=
  ⟨0, fun r hr => PwLengthSet.nonneg x y r hr⟩

/-- **The Riemannian distance** between two points: the infimum of the lengths of piecewise smooth
paths joining them. -/
noncomputable def riemannianDist (x y : M) : ℝ :=
  sInf (PwLengthSet (I := I) x y)

lemma riemannianDist_nonneg (x y : M) : 0 ≤ riemannianDist (I := I) x y :=
  Real.sInf_nonneg (PwLengthSet.nonneg x y)

lemma riemannianDist_self (x : M) : riemannianDist (I := I) x x = 0 := by
  refine le_antisymm ?_ (riemannianDist_nonneg (I := I) x x)
  refine csInf_le (PwLengthSet.bddBelow (I := I) x x) ?_
  exact ⟨PwPath.refl (I := I) x, by simp only [PwPath.length_refl]⟩

lemma riemannianDist_le_length (p : PwPath I x y) : riemannianDist (I := I) x y ≤ p.length :=
  csInf_le (PwLengthSet.bddBelow (I := I) x y) (Set.mem_range_self (f := fun p' => p'.length) p)

/-- **The distance is bounded by the length of any smooth curve joining the two points.** -/
theorem riemannianDist_le_curveLength (γ : ℝ → M) (hγ : ContMDiff 𝓘(ℝ) I 1 γ) (x y : M)
    (hx : γ 0 = x) (hy : γ 1 = y) :
    riemannianDist (I := I) x y ≤ curveLength (I := I) γ 0 1 := by
  rw [← PwPath.length_ofCurve (I := I) γ hγ x y hx hy]
  exact riemannianDist_le_length _

lemma PwLengthSet.trans_subset (p : PwPath I x y) (q : PwPath I y z) :
    PwLengthSet (I := I) x y + PwLengthSet (I := I) y z ⊆ PwLengthSet (I := I) x z := by
  rintro r ⟨b, hb, c, hc, rfl⟩
  obtain ⟨p', rfl⟩ := hb
  obtain ⟨q', rfl⟩ := hc
  exact ⟨p'.trans q', by simpa only [] using PwPath.length_trans p' q'⟩

/-- **The triangle inequality for the Riemannian distance.** -/
theorem riemannianDist_triangle (hxy : (PwLengthSet (I := I) x y).Nonempty)
    (hyz : (PwLengthSet (I := I) y z).Nonempty) :
    riemannianDist (I := I) x z
      ≤ riemannianDist (I := I) x y + riemannianDist (I := I) y z := by
  obtain ⟨r, hr⟩ := hxy
  obtain ⟨p, rfl⟩ := hr
  obtain ⟨s, hs⟩ := hyz
  obtain ⟨q, rfl⟩ := hs
  have htne : (PwLengthSet (I := I) x y + PwLengthSet (I := I) y z).Nonempty :=
    ⟨p.length + q.length,
      Set.add_mem_add (Set.mem_range_self (f := fun p' : PwPath I x y => p'.length) p)
        (Set.mem_range_self (f := fun q' : PwPath I y z => q'.length) q)⟩
  rw [riemannianDist, riemannianDist, riemannianDist]
  calc sInf (PwLengthSet (I := I) x z)
      ≤ sInf (PwLengthSet (I := I) x y + PwLengthSet (I := I) y z) :=
        csInf_le_csInf (PwLengthSet.bddBelow (I := I) x z) htne
          (PwLengthSet.trans_subset p q)
    _ = sInf (PwLengthSet (I := I) x y) + sInf (PwLengthSet (I := I) y z) :=
        csInf_add
          ⟨p.length, Set.mem_range_self (f := fun p' : PwPath I x y => p'.length) p⟩
          (PwLengthSet.bddBelow (I := I) x y)
          ⟨q.length, Set.mem_range_self (f := fun q' : PwPath I y z => q'.length) q⟩
          (PwLengthSet.bddBelow (I := I) y z)

end

end Submission.Distance
