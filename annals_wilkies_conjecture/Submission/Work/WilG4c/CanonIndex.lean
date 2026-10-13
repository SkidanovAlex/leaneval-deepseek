/-
  WilG4c — the canonical-form conversion for BNZ §5.4.

  The `γ`-choice `CurveFamAlpha` and the engine `curve_bound` are indexed by the *canonical*
  multiindex `(j, M)` (`j` copies of the `x`-direction followed by the `y`-directions of `M`),
  while `subdiv_normle_multi` (which turns the curve bounds into operator bounds) is indexed by a
  direction tuple `v : Fin m → Fin (n+1)`.  This file bridges the two: every tuple is a
  permutation of a unique canonical multiindex (`exists_canonical_perm`), and `iterDir` is
  invariant under permutation (`iterDir_perm`), so the tuple form of the bounds follows from the
  canonical form.  The `Classical.choose` selection `canonJ`/`canonM` makes the bridge a
  *function* of the tuple, so that `subdiv_normle_multi` can be applied with
  `fun m v => γc (canonJ v) (canonM v)`.
-/
import Mathlib
import Submission.Work.WilG4c.StepHigherDefs
import Submission.Work.WilG4c.exists_canonical_perm
import Submission.Work.WilG4c.iterDir_eq_iteratedFDeriv
import Submission.Work.WilG4c.iterDir_perm

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Classical

open scoped BigOperators Topology

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- `canonJ v` is the number of `x`-directions of the canonical multiindex equivalent to `v`. -/
noncomputable def canonJ {n m : ℕ} (v : Fin m → Fin (n + 1)) : ℕ :=
  Classical.choose (Work.WilG4c.exists_canonical_perm (n := n) v)

/-- `canonM v` is the `y`-part of the canonical multiindex equivalent to `v`. -/
noncomputable def canonM {n m : ℕ} (v : Fin m → Fin (n + 1)) : List (Fin n) :=
  Classical.choose (Classical.choose_spec (Work.WilG4c.exists_canonical_perm (n := n) v))

theorem canonJ_add_length {n m : ℕ} (v : Fin m → Fin (n + 1)) :
    canonJ v + (canonM v).length = m :=
  (Classical.choose_spec (Classical.choose_spec (Work.WilG4c.exists_canonical_perm (n := n) v))).1

theorem canon_perm {n m : ℕ} (v : Fin m → Fin (n + 1)) :
    (List.ofFn v).Perm
      (List.replicate (canonJ v) (0 : Fin (n + 1)) ++ (canonM v).map Fin.succ) :=
  (Classical.choose_spec (Classical.choose_spec (Work.WilG4c.exists_canonical_perm (n := n) v))).2

/-! ## The canonical/tuple bridge

The two conversions below are the last piece of the canonical/tuple bridge.  The only
syntactic difficulty is that `(List.ofFn v).length` is *not* definitionally `m`, so the
dependent type `Fin (List.ofFn v).length → _` of the direction tuple does not match
`Fin m → _`.  This is handled once and for all by `iteratedFDeriv_congr_fin`, which transports
`iteratedFDeriv` along an equality of the index; `iterDir_ofFn` is then the tuple form of the
list form `iterDir (List.ofFn v)`. -/

/-- Transport of the evaluated iterated derivative along an equality of the index `m = m'`. -/
private lemma iteratedFDeriv_congr_fin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m m' : ℕ} (h : m = m')
    (f : E → ℝ) (x : E) (v : Fin m → E) (w : Fin m' → E)
    (hw : ∀ i : Fin m, w (Fin.cast h i) = v i) :
    iteratedFDeriv ℝ m f x v = iteratedFDeriv ℝ m' f x w := by
  subst h
  congr 1
  funext i
  exact (hw i).symm

/-- The evaluated iterated derivative along the coordinate directions of a tuple `v` is the
iterated directional derivative along the list `List.ofFn v`. -/
theorem iterDir_ofFn {n m : ℕ} (v : Fin m → Fin (n + 1)) (G : (Fin (n + 1) → ℝ) → ℝ)
    (z : Fin (n + 1) → ℝ) (hG : ContDiffAt ℝ m G z) :
    iterDir (List.ofFn v) G z = iteratedFDeriv ℝ m G z (fun k => Pi.single (v k) 1) := by
  have hG' : ContDiffAt ℝ (List.ofFn v).length G z := by
    rw [List.length_ofFn]; exact hG
  rw [Work.WilG4c.iterDir_eq_iteratedFDeriv (List.ofFn v) G z hG']
  refine iteratedFDeriv_congr_fin List.length_ofFn G z
    (fun k => Pi.single ((List.ofFn v).get k) 1) (fun k => Pi.single (v k) 1) (fun i => ?_)
  congr 1
  rw [List.get_ofFn]

/-- The curve family indexed by direction tuples, induced by the canonical family `γc`
(one curve per multiindex `(j, M)`): `canonGamma γc m v := γc (canonJ v) (canonM v)`. -/
def canonGamma {n : ℕ} (γc : (j : ℕ) → List (Fin n) → ℝ → Fin n → ℝ) :
    (m : ℕ) → (Fin m → Fin (n + 1)) → ℝ → Fin n → ℝ :=
  fun _ v => γc (canonJ v) (canonM v)

theorem canonGamma_apply {n : ℕ} (γc : (j : ℕ) → List (Fin n) → ℝ → Fin n → ℝ) (m : ℕ)
    (v : Fin m → Fin (n + 1)) : canonGamma γc m v = γc (canonJ v) (canonM v) := rfl

/-- **The canonical/tuple bridge.**  The hypotheses `hmax`/`hcurve` of
`Work.WilG4c.subdiv_normle_multi` for the tuple-indexed curve family
`canonGamma γc m v = γc (canonJ v) (canonM v)` follow from their canonical counterparts for the
multiindex-indexed family `γc`, provided the canonical multiindices of the tuples are within
order `r`. -/
theorem subdiv_hyp_multi {n r : ℕ} (hr : 1 ≤ r) (G : (Fin (n + 1) → ℝ) → ℝ)
    (γc : (j : ℕ) → List (Fin n) → ℝ → Fin n → ℝ)
    (hnearmax : ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ) (y : Fin n → ℝ), j + M.length ≤ r →
      x ∈ I → y ∈ openCube n →
      ContDiffAt ℝ ((j + M.length : ℕ) : WithTop ℕ∞) G (pt x y) →
      |iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G (pt x y)| ≤
        2 * |iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G
              (curveFun (γc j M) x)|)
    (hcurvesm : ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ), j + M.length ≤ r → x ∈ I →
      ContDiffAt ℝ ((j + M.length : ℕ) : WithTop ℕ∞) G (curveFun (γc j M) x))
    (hcurve : ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ), j + M.length ≤ r → x ∈ I →
      |iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G
          (curveFun (γc j M) x)| ≤
        Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j) :
    (∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ), m ≤ r → x ∈ I →
        y ∈ openCube n → ContDiffAt ℝ m G (pt x y) →
      |iteratedFDeriv ℝ m G (pt x y) (fun k => Pi.single (v k) 1)| ≤
        2 * |iteratedFDeriv ℝ m G (curveFun (canonGamma γc m v) x)
              (fun k => Pi.single (v k) 1)|) ∧
    (∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ), m ≤ r → x ∈ I →
      |iteratedFDeriv ℝ m G (curveFun (canonGamma γc m v) x) (fun k => Pi.single (v k) 1)| ≤
        Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) := by
  -- the canonical multiindex of `v`, and the arithmetic that identifies `m` with `j + |M|`
  have hjl : ∀ {m : ℕ} (v : Fin m → Fin (n + 1)),
      canonJ v + (canonM v).length = m := fun v => canonJ_add_length v
  have hprm : ∀ {m : ℕ} (v : Fin m → Fin (n + 1)),
      (List.ofFn v).Perm
        (List.replicate (canonJ v) (0 : Fin (n + 1)) ++ (canonM v).map Fin.succ) :=
    fun v => canon_perm v
  -- both sides of the two statements, in canonical form
  have key : ∀ {m : ℕ} (v : Fin m → Fin (n + 1)) (z : Fin (n + 1) → ℝ),
      ContDiffAt ℝ m G z →
      iteratedFDeriv ℝ m G z (fun k => Pi.single (v k) 1) =
        iterDir (List.replicate (canonJ v) (0 : Fin (n + 1)) ++ (canonM v).map Fin.succ) G z := by
    intro m v z hG
    have hlen : (List.ofFn v).length = m := by rw [List.length_ofFn]
    have hGv : ContDiffAt ℝ (List.ofFn v).length G z := by rw [hlen]; exact hG
    rw [← iterDir_ofFn v G z hG, Work.WilG4c.iterDir_perm G (hprm v) z hGv]
  have hbase : (1 : ℝ) ≤ r * (1 + n * Real.exp 1) := by
    have hr' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    nlinarith [mul_nonneg hn he.le, mul_nonneg (mul_nonneg hn he.le) (le_trans zero_le_one hr')]
  constructor
  · intro m v x y hm hx hy hG
    simp only [canonGamma]
    have hjm : canonJ v + (canonM v).length = m := hjl v
    have hGpt : ContDiffAt ℝ ((canonJ v + (canonM v).length : ℕ) : WithTop ℕ∞) G (pt x y) := by
      rw [hjm]; exact hG
    have hGcu : ContDiffAt ℝ m G (curveFun (γc (canonJ v) (canonM v)) x) :=
      (hcurvesm (canonJ v) (canonM v) x (by omega) hx).of_le
        (by exact_mod_cast (by omega : m ≤ canonJ v + (canonM v).length))
    rw [key v (pt x y) hG, key v (curveFun (γc (canonJ v) (canonM v)) x) hGcu]
    exact hnearmax (canonJ v) (canonM v) x y (by omega) hx hy hGpt
  · intro m v x hm hx
    simp only [canonGamma]
    have hjm : canonJ v + (canonM v).length = m := hjl v
    have hGcu : ContDiffAt ℝ m G (curveFun (γc (canonJ v) (canonM v)) x) :=
      (hcurvesm (canonJ v) (canonM v) x (by omega) hx).of_le
        (by exact_mod_cast (by omega : m ≤ canonJ v + (canonM v).length))
    rw [key v (curveFun (γc (canonJ v) (canonM v)) x) hGcu]
    have h := hcurve (canonJ v) (canonM v) x (by omega) hx
    refine h.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
    exact pow_le_pow_right₀ hbase (by omega)

/-- **The canonical/tuple bridge, off a bad set.**  Same as `subdiv_hyp_multi`, but the
near-maximality hypothesis (and the corresponding half of the conclusion) is only required for
`x` outside a finite set `B` of `x`-coordinates.  This is the form used by the §5.4 assembly:
at the points of `B` (where the fibre supremum of the derivative is infinite and hence no
near-maximiser exists) the bound is recovered from the neighbouring good points by continuity
(`Work.WilG4c.subdiv_normle_multi_bad`). -/
theorem subdiv_hyp_multi_bad {n r : ℕ} (hr : 1 ≤ r) (G : (Fin (n + 1) → ℝ) → ℝ)
    (γc : (j : ℕ) → List (Fin n) → ℝ → Fin n → ℝ) (B : Finset ℝ)
    (hnearmax : ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ) (y : Fin n → ℝ), j + M.length ≤ r →
      x ∈ I → x ∉ (B : Set ℝ) → y ∈ openCube n →
      ContDiffAt ℝ ((j + M.length : ℕ) : WithTop ℕ∞) G (pt x y) →
      |iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G (pt x y)| ≤
        2 * |iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G
              (curveFun (γc j M) x)|)
    (hcurvesm : ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ), j + M.length ≤ r → x ∈ I →
      ContDiffAt ℝ ((j + M.length : ℕ) : WithTop ℕ∞) G (curveFun (γc j M) x))
    (hcurve : ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ), j + M.length ≤ r → x ∈ I →
      |iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G
          (curveFun (γc j M) x)| ≤
        Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j) :
    (∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ), m ≤ r → x ∈ I →
        x ∉ (B : Set ℝ) → y ∈ openCube n → ContDiffAt ℝ m G (pt x y) →
      |iteratedFDeriv ℝ m G (pt x y) (fun k => Pi.single (v k) 1)| ≤
        2 * |iteratedFDeriv ℝ m G (curveFun (canonGamma γc m v) x)
              (fun k => Pi.single (v k) 1)|) ∧
    (∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ), m ≤ r → x ∈ I →
      |iteratedFDeriv ℝ m G (curveFun (canonGamma γc m v) x) (fun k => Pi.single (v k) 1)| ≤
        Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) := by
  have hjl : ∀ {m : ℕ} (v : Fin m → Fin (n + 1)),
      canonJ v + (canonM v).length = m := fun v => canonJ_add_length v
  have hprm : ∀ {m : ℕ} (v : Fin m → Fin (n + 1)),
      (List.ofFn v).Perm
        (List.replicate (canonJ v) (0 : Fin (n + 1)) ++ (canonM v).map Fin.succ) :=
    fun v => canon_perm v
  have key : ∀ {m : ℕ} (v : Fin m → Fin (n + 1)) (z : Fin (n + 1) → ℝ),
      ContDiffAt ℝ m G z →
      iteratedFDeriv ℝ m G z (fun k => Pi.single (v k) 1) =
        iterDir (List.replicate (canonJ v) (0 : Fin (n + 1)) ++ (canonM v).map Fin.succ) G z := by
    intro m v z hG
    have hlen : (List.ofFn v).length = m := by rw [List.length_ofFn]
    have hGv : ContDiffAt ℝ (List.ofFn v).length G z := by rw [hlen]; exact hG
    rw [← iterDir_ofFn v G z hG, Work.WilG4c.iterDir_perm G (hprm v) z hGv]
  have hbase : (1 : ℝ) ≤ r * (1 + n * Real.exp 1) := by
    have hr' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    nlinarith [mul_nonneg hn he.le, mul_nonneg (mul_nonneg hn he.le) (le_trans zero_le_one hr')]
  constructor
  · intro m v x y hm hx hxB hy hG
    simp only [canonGamma]
    have hjm : canonJ v + (canonM v).length = m := hjl v
    have hGpt : ContDiffAt ℝ ((canonJ v + (canonM v).length : ℕ) : WithTop ℕ∞) G (pt x y) := by
      rw [hjm]; exact hG
    have hGcu : ContDiffAt ℝ m G (curveFun (γc (canonJ v) (canonM v)) x) :=
      (hcurvesm (canonJ v) (canonM v) x (by omega) hx).of_le
        (by exact_mod_cast (by omega : m ≤ canonJ v + (canonM v).length))
    rw [key v (pt x y) hG, key v (curveFun (γc (canonJ v) (canonM v)) x) hGcu]
    exact hnearmax (canonJ v) (canonM v) x y (by omega) hx hxB hy hGpt
  · intro m v x hm hx
    simp only [canonGamma]
    have hjm : canonJ v + (canonM v).length = m := hjl v
    have hGcu : ContDiffAt ℝ m G (curveFun (γc (canonJ v) (canonM v)) x) :=
      (hcurvesm (canonJ v) (canonM v) x (by omega) hx).of_le
        (by exact_mod_cast (by omega : m ≤ canonJ v + (canonM v).length))
    rw [key v (curveFun (γc (canonJ v) (canonM v)) x) hGcu]
    have h := hcurve (canonJ v) (canonM v) x (by omega) hx
    refine h.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
    exact pow_le_pow_right₀ hbase (by omega)

/-- **The canonical/tuple bridge, all hypotheses off the bad set `B`.**  Same as
`subdiv_hyp_multi_bad`, but now the *curve smoothness* hypothesis `hcurvesm` and the curve
bound `hcurve` are also required only for `x ∉ B`, and the conclusion's curve half is likewise
restricted to `x ∉ B`.

This is the form the §5.4 assembly actually needs: at a bad `x ∈ B` the slice of the member is
not known to be `C^{|L|}` at the chosen curve point, so neither the smoothness at the curve
point nor the engine's curve bound is available there; but the consumer
`Work.WilkG4c.pt_jet_le_multi_bad_offB` needs the pair `(hmax, hcurve)` only off `B`. -/
theorem subdiv_hyp_multi_badB {n r : ℕ} (hr : 1 ≤ r) (G : (Fin (n + 1) → ℝ) → ℝ)
    (γc : (j : ℕ) → List (Fin n) → ℝ → Fin n → ℝ) (B : Finset ℝ)
    (hnearmax : ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ) (y : Fin n → ℝ), j + M.length ≤ r →
      x ∈ I → x ∉ (B : Set ℝ) → y ∈ openCube n →
      ContDiffAt ℝ ((j + M.length : ℕ) : WithTop ℕ∞) G (pt x y) →
      |iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G (pt x y)| ≤
        2 * |iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G
              (curveFun (γc j M) x)|)
    (hcurvesm : ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ), j + M.length ≤ r → x ∈ I →
      x ∉ (B : Set ℝ) →
      ContDiffAt ℝ ((j + M.length : ℕ) : WithTop ℕ∞) G (curveFun (γc j M) x))
    (hcurve : ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ), j + M.length ≤ r → x ∈ I →
      x ∉ (B : Set ℝ) →
      |iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G
          (curveFun (γc j M) x)| ≤
        Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j) :
    (∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ), m ≤ r → x ∈ I →
        x ∉ (B : Set ℝ) → y ∈ openCube n → ContDiffAt ℝ m G (pt x y) →
      |iteratedFDeriv ℝ m G (pt x y) (fun k => Pi.single (v k) 1)| ≤
        2 * |iteratedFDeriv ℝ m G (curveFun (canonGamma γc m v) x)
              (fun k => Pi.single (v k) 1)|) ∧
    (∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ), m ≤ r → x ∈ I → x ∉ (B : Set ℝ) →
      |iteratedFDeriv ℝ m G (curveFun (canonGamma γc m v) x) (fun k => Pi.single (v k) 1)| ≤
        Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ m) := by
  have hjl : ∀ {m : ℕ} (v : Fin m → Fin (n + 1)),
      canonJ v + (canonM v).length = m := fun v => canonJ_add_length v
  have hprm : ∀ {m : ℕ} (v : Fin m → Fin (n + 1)),
      (List.ofFn v).Perm
        (List.replicate (canonJ v) (0 : Fin (n + 1)) ++ (canonM v).map Fin.succ) :=
    fun v => canon_perm v
  have key : ∀ {m : ℕ} (v : Fin m → Fin (n + 1)) (z : Fin (n + 1) → ℝ),
      ContDiffAt ℝ m G z →
      iteratedFDeriv ℝ m G z (fun k => Pi.single (v k) 1) =
        iterDir (List.replicate (canonJ v) (0 : Fin (n + 1)) ++ (canonM v).map Fin.succ) G z := by
    intro m v z hG
    have hlen : (List.ofFn v).length = m := by rw [List.length_ofFn]
    have hGv : ContDiffAt ℝ (List.ofFn v).length G z := by rw [hlen]; exact hG
    rw [← iterDir_ofFn v G z hG, Work.WilG4c.iterDir_perm G (hprm v) z hGv]
  have hbase : (1 : ℝ) ≤ r * (1 + n * Real.exp 1) := by
    have hr' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
    nlinarith [mul_nonneg hn he.le, mul_nonneg (mul_nonneg hn he.le) (le_trans zero_le_one hr')]
  constructor
  · intro m v x y hm hx hxB hy hG
    simp only [canonGamma]
    have hjm : canonJ v + (canonM v).length = m := hjl v
    have hGpt : ContDiffAt ℝ ((canonJ v + (canonM v).length : ℕ) : WithTop ℕ∞) G (pt x y) := by
      rw [hjm]; exact hG
    have hGcu : ContDiffAt ℝ m G (curveFun (γc (canonJ v) (canonM v)) x) :=
      (hcurvesm (canonJ v) (canonM v) x (by omega) hx hxB).of_le
        (by exact_mod_cast (by omega : m ≤ canonJ v + (canonM v).length))
    rw [key v (pt x y) hG, key v (curveFun (γc (canonJ v) (canonM v)) x) hGcu]
    exact hnearmax (canonJ v) (canonM v) x y (by omega) hx hxB hy hGpt
  · intro m v x hm hx hxB
    simp only [canonGamma]
    have hjm : canonJ v + (canonM v).length = m := hjl v
    have hGcu : ContDiffAt ℝ m G (curveFun (γc (canonJ v) (canonM v)) x) :=
      (hcurvesm (canonJ v) (canonM v) x (by omega) hx hxB).of_le
        (by exact_mod_cast (by omega : m ≤ canonJ v + (canonM v).length))
    rw [key v (curveFun (γc (canonJ v) (canonM v)) x) hGcu]
    have h := hcurve (canonJ v) (canonM v) x (by omega) hx hxB
    refine h.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
    exact pow_le_pow_right₀ hbase (by omega)

end Work.WilkG4c
