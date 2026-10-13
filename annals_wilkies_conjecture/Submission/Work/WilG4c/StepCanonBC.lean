/-
  WilG4c — the *conditional* canonical/tuple bridge of BNZ §5.4.

  `Work.WilkG4c.subdiv_hyp_multi_badB` restricts the curve smoothness `hcurvesm` and the curve
  bound `hcurve` to the complement of the finite bad set `B` of `x`-coordinates.  That is not
  enough for the §5.4 assembly: at an `x` whose fibre `{y ∈ openCube n}` contains no point where
  the member is `C^{|L|}` (a possibility that is *not* excluded off any finite set, since the bad
  locus of a definable function may contain a whole vertical segment), the sliced choice lemma
  gives nothing, so neither the smoothness nor the curve bound is available there — yet
  `CurveData` and its consumers `Work.WilG4c.{subdiv_normle_multi_badBC,
  pullback_pylipdef_multi_badBC}` use them only where a fibre point *is* smooth (this is how
  `Work.WilkG4c.pt_jet_le_multi_bad_offBC` recovers the pointwise bound at the bad `x` by
  continuity).  Accordingly the hypotheses here carry the witness `y ∈ openCube n` together with
  `ContDiffAt ℝ (j+M.length) G (pt x y)`, exactly as the near-maximality hypothesis `hnearmax`
  already does.

  Everything else — the permutation invariance of `iterDir` and the identification of the
  canonical multiindex of a direction tuple — is verbatim `subdiv_hyp_multi_badB`.
-/
import Mathlib
import Submission.Work.WilG4c.CanonIndex

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open Classical

open scoped BigOperators Topology

namespace Work.WilkG4c

open WilkiesDesign WilkiesDesign.CG

/-- **The conditional canonical/tuple bridge.**  Given the near-maximality `hnearmax`, the
smoothness `hcurvesm` and the curve bound `hcurve` of the canonical multiindices `(j,M)` — all
three required only at coordinates `x ∈ I \ B` at which the fibre contains a point `pt x y` at
which `G` is `C^{j+|M|}` — the tuple form of the same three statements holds for the
tuple-indexed curve family `canonGamma γc m v = γc (canonJ v) (canonM v)`. -/
theorem subdiv_hyp_multi_badBC {n r : ℕ} (hr : 1 ≤ r) (G : (Fin (n + 1) → ℝ) → ℝ)
    (γc : (j : ℕ) → List (Fin n) → ℝ → Fin n → ℝ) (B : Finset ℝ)
    (hnearmax : ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ) (y : Fin n → ℝ), j + M.length ≤ r →
      x ∈ I → x ∉ (B : Set ℝ) → y ∈ openCube n →
      ContDiffAt ℝ ((j + M.length : ℕ) : WithTop ℕ∞) G (pt x y) →
      |iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G (pt x y)| ≤
        2 * |iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G
              (curveFun (γc j M) x)|)
    (hcurvesm : ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ) (y : Fin n → ℝ), j + M.length ≤ r →
      x ∈ I → x ∉ (B : Set ℝ) → y ∈ openCube n →
      ContDiffAt ℝ ((j + M.length : ℕ) : WithTop ℕ∞) G (pt x y) →
      ContDiffAt ℝ ((j + M.length : ℕ) : WithTop ℕ∞) G (curveFun (γc j M) x))
    (hcurve : ∀ (j : ℕ) (M : List (Fin n)) (x : ℝ) (y : Fin n → ℝ), j + M.length ≤ r →
      x ∈ I → x ∉ (B : Set ℝ) → y ∈ openCube n →
      ContDiffAt ℝ ((j + M.length : ℕ) : WithTop ℕ∞) G (pt x y) →
      |iterDir (List.replicate j (0 : Fin (n + 1)) ++ M.map Fin.succ) G
          (curveFun (γc j M) x)| ≤
        Real.exp 1 * (r * (1 + n * Real.exp 1)) ^ j) :
    (∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ), m ≤ r → x ∈ I →
        x ∉ (B : Set ℝ) → y ∈ openCube n → ContDiffAt ℝ m G (pt x y) →
      |iteratedFDeriv ℝ m G (pt x y) (fun k => Pi.single (v k) 1)| ≤
        2 * |iteratedFDeriv ℝ m G (curveFun (canonGamma γc m v) x)
              (fun k => Pi.single (v k) 1)|) ∧
    (∀ (m : ℕ) (v : Fin m → Fin (n + 1)) (x : ℝ) (y : Fin n → ℝ), m ≤ r → x ∈ I →
        x ∉ (B : Set ℝ) → y ∈ openCube n → ContDiffAt ℝ m G (pt x y) →
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
      (hcurvesm (canonJ v) (canonM v) x y (by omega) hx hxB hy hGpt).of_le
        (by exact_mod_cast (by omega : m ≤ canonJ v + (canonM v).length))
    rw [key v (pt x y) hG, key v (curveFun (γc (canonJ v) (canonM v)) x) hGcu]
    exact hnearmax (canonJ v) (canonM v) x y (by omega) hx hxB hy hGpt
  · intro m v x y hm hx hxB hy hG
    simp only [canonGamma]
    have hjm : canonJ v + (canonM v).length = m := hjl v
    have hGpt : ContDiffAt ℝ ((canonJ v + (canonM v).length : ℕ) : WithTop ℕ∞) G (pt x y) := by
      rw [hjm]; exact hG
    have hGcu : ContDiffAt ℝ m G (curveFun (γc (canonJ v) (canonM v)) x) :=
      (hcurvesm (canonJ v) (canonM v) x y (by omega) hx hxB hy hGpt).of_le
        (by exact_mod_cast (by omega : m ≤ canonJ v + (canonM v).length))
    rw [key v (curveFun (γc (canonJ v) (canonM v)) x) hGcu]
    have h := hcurve (canonJ v) (canonM v) x y (by omega) hx hxB hy hGpt
    refine h.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos 1).le
    exact pow_le_pow_right₀ hbase (by omega)

end Work.WilkG4c
