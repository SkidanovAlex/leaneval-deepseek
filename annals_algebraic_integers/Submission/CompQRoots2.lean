import Submission.AdjustedCheb
import Submission.Bclps
import Submission.ChebSerre
import Submission.DivLinear
import Submission.MarkovInterval
import Submission.CompQNums
import Submission.CompQ
import Submission.CompQ
import Submission.CompQRoots
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Norms and local growth of the complementary polynomial (Smith's `lem:comp_Q_roots2`)

adjust.tex, Lemma `lem:comp_Q_roots2`, single interval.  Given the
`defn:comp_Q` data (polynomial `T` from `lem:Bclps` — monic degree `r`, within
`κ^r/64` of `T̃ = prunedPoly r` pointwise on the Serre interval, `±`-sign and
`|T| ≥ κ^r/64` at the bracket points; `Q0 = ∏_{j'<D}(T − c_{j'})`;
`Q − Q0 = Σ_t ε_t·auxPoly t + N` with `ε_t ∈ [0,2)`, `0 ≤ N ≤ 2·C2val⁻¹·κ^{Dr}`),
for all sufficiently large `r`:

* `‖Q‖ ≤ r^C·κ^{Dr}`  (from `‖T‖ ≤ (r+3)^7·κ^r` via the closeness clause,
  `|c_{j'}| < κ^r/64`, `Σ|ε_t·auxPoly t| ≤ 4κ^{d+1}/(κ−1)`, `N ≤ 2·C2val⁻¹·κ^{Dr}`);
* `‖Q′‖ ≤ r^C·κ^{Dr}`  (Markov's inequality on the interval, degree `Dr`);
* local growth near each root `β` of `Q`:
  `|Q(w)| ≥ r^{−C}·κ^{Dr}·|w−β|` for `|w−β| ≤ r^{−C}`.

For the local growth, the bracket intervals around roots from
`Submission.CompQRoots.comp_Q_roots` and the paper's Rolle-type "headache"
argument are used: on a bracket `[x,y]` containing only the root `β`,
`|Q_β| = |Q/(X−β)|` takes its minimum at an endpoint (all roots of `Q_β` lie
outside `[x,y]`, and between consecutive roots `Q_β′` vanishes exactly once, at
a local extremum of `|Q_β|` of maximum type), so
`|Q_β(w)| ≥ min(|Q_β(x)|,|Q_β(y)|) ≥ r^{−C}·κ^{Dr}` throughout `[x,y]`.
-/

noncomputable section

set_option maxHeartbeats 800000

open scoped Real BigOperators
open Polynomial
open ComplexOrder

namespace Submission.CompQRoots2

open Submission.SerreExample
open Submission.ChebSerre
open Submission.AdjustedCheb
open Submission.Bclps
open Submission.DivLinear
open Submission.CompQNums
open Submission.CompQRoots

/-- the auxiliary-degree `d = (D−1)·r`. -/
def d (r : ℕ) : ℕ := (Bclps.Dconst - 1) * r


/-! ## Generic: minimum of a real-rooted product on an interval is at an endpoint -/

/-- log is concave on positive reals (weighted form). -/
lemma log_concave_on_pos {a b : ℝ} {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * Real.log α + b * Real.log β ≤ Real.log (a * α + b * β) := by
  rcases (strictConcaveOn_log_Ioi.concaveOn) with ⟨hconv, hpt⟩
  have hαi : α ∈ Set.Ioi (0 : ℝ) := by simpa using hα
  have hβi : β ∈ Set.Ioi (0 : ℝ) := by simpa using hβ
  have h := hpt hαi hβi (a := a) (b := b) ha hb hab
  simpa [smul_eq_mul] using h

/-- pointwise concavity inequality on an interval -/
def conc (f : ℝ → ℝ) (x y : ℝ) : Prop :=
  ∀ u v : ℝ, u ∈ Set.Icc x y → v ∈ Set.Icc x y → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a + b = 1 →
    a * f u + b * f v ≤ f (a * u + b * v)

/-- (fun w => log (w - c)) satisfies conc on [x,y] when c < x. -/
lemma conc_log_sub {c x y : ℝ} (_hxy : x < y) (hc : c < x) :
    conc (fun w : ℝ => Real.log (w - c)) x y := by
  intro u v hu hv a b ha hb hab
  have hul : (0 : ℝ) < u - c := by
    have hux : x ≤ u := hu.1
    linarith
  have hvl : (0 : ℝ) < v - c := by
    have hvx : x ≤ v := hv.1
    linarith
  have hlog := log_concave_on_pos (α := u - c) (β := v - c) hul hvl ha hb hab
  have habs : a * (u - c) + b * (v - c) = a * u + b * v - c := by
    calc
      a * (u - c) + b * (v - c) = a * u + b * v - (a * c + b * c) := by ring
      _ = a * u + b * v - c := by
          congr 1
          rw [← add_mul, hab, one_mul]
  calc
    a * Real.log (u - c) + b * Real.log (v - c) ≤ Real.log (a * (u - c) + b * (v - c)) := hlog
    _ = Real.log (a * u + b * v - c) := by rw [habs]

/-- (fun w => log (c - w)) satisfies conc on [x,y] when y < c. -/
lemma conc_log_sub' {c x y : ℝ} (_hxy : x < y) (hc : y < c) :
    conc (fun w : ℝ => Real.log (c - w)) x y := by
  intro u v hu hv a b ha hb hab
  have hul : (0 : ℝ) < c - u := by
    have huy : u ≤ y := hu.2
    linarith
  have hvl : (0 : ℝ) < c - v := by
    have hvy : v ≤ y := hv.2
    linarith
  have hlog := log_concave_on_pos (α := c - u) (β := c - v) hul hvl ha hb hab
  have habs : a * (c - u) + b * (c - v) = c - (a * u + b * v) := by
    calc
      a * (c - u) + b * (c - v) = (a * c + b * c) - (a * u + b * v) := by ring
      _ = c - (a * u + b * v) := by
          rw [show a * c + b * c = c by rw [← add_mul, hab, one_mul]]
  calc
    a * Real.log (c - u) + b * Real.log (c - v) ≤ Real.log (a * (c - u) + b * (c - v)) := hlog
    _ = Real.log (c - (a * u + b * v)) := by rw [habs]

/-- log |w - c| satisfies conc on [x,y] when c is outside the interval. -/
lemma conc_log_abs {c x y : ℝ} (hxy : x < y) (hc : c < x ∨ y < c) :
    conc (fun w : ℝ => Real.log |w - c|) x y := by
  rcases hc with hlt | hgt
  · have hmain := conc_log_sub (c := c) hxy hlt
    intro u v hu hv a b ha hb hab
    have h1 := hmain u v hu hv a b ha hb hab
    have habsu : |u - c| = u - c := by
      have huc : 0 < u - c := by
        have hux : x ≤ u := hu.1
        linarith
      exact abs_of_pos huc
    have habsv : |v - c| = v - c := by
      have hvc : 0 < v - c := by
        have hvx : x ≤ v := hv.1
        linarith
      exact abs_of_pos hvc
    have hcom : |a * u + b * v - c| = a * u + b * v - c := by
      have hc0 : 0 < a * u + b * v - c := by
        have hx1 : x ≤ a * u + b * v := by
          have huu : a * x ≤ a * u := mul_le_mul_of_nonneg_left hu.1 ha
          have hvv : b * x ≤ b * v := mul_le_mul_of_nonneg_left hv.1 hb
          calc
            x = (a + b) * x := by rw [hab, one_mul]
            _ = a * x + b * x := by rw [add_mul]
            _ ≤ a * u + b * v := add_le_add huu hvv
        linarith
      exact abs_of_pos hc0
    calc
      a * Real.log |u - c| + b * Real.log |v - c|
          = a * Real.log (u - c) + b * Real.log (v - c) := by rw [habsu, habsv]
      _ ≤ Real.log (a * u + b * v - c) := h1
      _ = Real.log |a * u + b * v - c| := by rw [hcom]
  · have hmain := conc_log_sub' (c := c) hxy hgt
    intro u v hu hv a b ha hb hab
    have h1 := hmain u v hu hv a b ha hb hab
    have habsu : |u - c| = c - u := by
      have hcu : 0 < c - u := by
        have huy : u ≤ y := hu.2
        linarith
      rw [show |u - c| = |c - u| by rw [abs_sub_comm]]
      exact abs_of_pos hcu
    have habsv : |v - c| = c - v := by
      have hcv : 0 < c - v := by
        have hvy : v ≤ y := hv.2
        linarith
      rw [show |v - c| = |c - v| by rw [abs_sub_comm]]
      exact abs_of_pos hcv
    have hcom : |a * u + b * v - c| = c - (a * u + b * v) := by
      have hc0 : a * u + b * v - c < 0 := by
        have huu : a * u ≤ a * y := mul_le_mul_of_nonneg_left hu.2 ha
        have hvv : b * v ≤ b * y := mul_le_mul_of_nonneg_left hv.2 hb
        have hy1 : a * u + b * v ≤ y := by
          calc
            a * u + b * v ≤ a * y + b * y := add_le_add huu hvv
            _ = (a + b) * y := by rw [add_mul]
            _ = y := by rw [hab, one_mul]
        linarith
      rw [show |a * u + b * v - c| = |c - (a * u + b * v)| by rw [abs_sub_comm]]
      rw [abs_of_pos (by linarith : 0 < c - (a * u + b * v))]
    calc
      a * Real.log |u - c| + b * Real.log |v - c|
          = a * Real.log (c - u) + b * Real.log (c - v) := by rw [habsu, habsv]
      _ ≤ Real.log (c - (a * u + b * v)) := h1
      _ = Real.log |a * u + b * v - c| := by rw [hcom]

/-- finite sums of `conc` functions satisfy `conc` -/
lemma conc_sum {ι : Type*} (t : Finset ι) {x y : ℝ} (f : ι → ℝ → ℝ)
    (hf : ∀ k : ι, k ∈ t → conc (f k) x y) :
    conc (fun w : ℝ => ∑ k ∈ t, f k w) x y := by
  classical
  have hgen : ∀ t' : Finset ι, t' ⊆ t →
      conc (fun w : ℝ => ∑ k ∈ t', f k w) x y := by
    intro t'
    refine Finset.induction_on t' ?_ ?_
    · intro ht'0 u v hu hv a b ha hb hab
      simp
    · intro xa s has ih hs u v hu hv a b ha hb hab
      have hxat : xa ∈ t := hs (by simp)
      have h1 := (hf xa hxat) u v hu hv a b ha hb hab
      have h2 := ih (fun k hk => hs (by simp [hk])) u v hu hv a b ha hb hab
      calc
        a * (∑ k ∈ insert xa s, f k u) + b * (∑ k ∈ insert xa s, f k v)
            = a * (f xa u + ∑ k ∈ s, f k u) + b * (f xa v + ∑ k ∈ s, f k v) := by
                rw [Finset.sum_insert has, Finset.sum_insert has]
        _ = (a * f xa u + b * f xa v) + (a * (∑ k ∈ s, f k u) + b * (∑ k ∈ s, f k v)) := by ring
        _ ≤ f xa (a * u + b * v) + (∑ k ∈ s, f k (a * u + b * v)) := add_le_add h1 h2
        _ = ∑ k ∈ insert xa s, f k (a * u + b * v) := by rw [Finset.sum_insert has]
  exact hgen t (by intro k hk; exact hk)

/-- a `conc` function attains its minimum on [x,y] at an endpoint -/
lemma conc_min_endpoint {x y w : ℝ} {f : ℝ → ℝ} (hxy : x < y) (hf : conc f x y)
    (hw : w ∈ Set.Icc x y) : min (f x) (f y) ≤ f w := by
  let t : ℝ := (w - x) / (y - x)
  have hxy0 : 0 < y - x := sub_pos.mpr hxy
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hw.1) (le_of_lt hxy0)
  have ht1 : t ≤ 1 := by
    rw [div_le_iff₀ hxy0]
    nlinarith [hw.2]
  have hxi : x ∈ Set.Icc x y := ⟨le_rfl, le_of_lt hxy⟩
  have hyi : y ∈ Set.Icc x y := ⟨le_of_lt hxy, le_rfl⟩
  have hseg : (1 - t) * x + t * y = w := by
    dsimp [t]
    field_simp [ne_of_gt hxy0]
    ring
  have hmain := hf x y hxi hyi (1 - t) t (by linarith) ht0 (by ring)
  have hmain' : (1 - t) * f x + t * f y ≤ f w := by
    simpa [hseg] using hmain
  have hmin : min (f x) (f y) ≤ (1 - t) * f x + t * f y := by
    have h1 := min_le_left (f x) (f y)
    have h2 := min_le_right (f x) (f y)
    have ht1' : 0 ≤ 1 - t := by linarith
    have hm1 := mul_le_mul_of_nonneg_left h1 ht1'
    have hm2 := mul_le_mul_of_nonneg_left h2 ht0
    calc
      min (f x) (f y) = (1 - t) * min (f x) (f y) + t * min (f x) (f y) := by
          rw [← add_mul]
          rw [show (1 - t) + t = 1 by ring, one_mul]
      _ ≤ (1 - t) * f x + t * f y := add_le_add hm1 hm2
  exact le_trans hmin hmain'

/-- log of an absolute product equals sum of logs (nonzero factors) -/
lemma log_abs_prod {ι : Type*} (t : Finset ι) (g : ι → ℝ)
    (hg : ∀ k : ι, k ∈ t → g k ≠ 0) :
    Real.log (∏ k ∈ t, |g k|) = ∑ k ∈ t, Real.log |g k| := by
  classical
  have hgen : ∀ t' : Finset ι, t' ⊆ t →
      Real.log (∏ k ∈ t', |g k|) = ∑ k ∈ t', Real.log |g k| := by
    intro t'
    refine Finset.induction_on t' ?_ ?_
    · intro ht'0
      rw [Finset.prod_empty, Finset.sum_empty]
      norm_num
    · intro xa s has ih hs
      have hga : g xa ≠ 0 := hg xa (hs (by simp))
      calc
        Real.log (∏ k ∈ insert xa s, |g k|)
            = Real.log (|g xa| * (∏ k ∈ s, |g k|)) := by rw [Finset.prod_insert has]
        _ = Real.log |g xa| + Real.log (∏ k ∈ s, |g k|) := by
            apply Real.log_mul
            · exact abs_ne_zero.mpr hga
            · apply ne_of_gt
              apply Finset.prod_pos
              intro k hk
              exact abs_pos.mpr (hg k (hs (by simp [hk])))
        _ = Real.log |g xa| + (∑ k ∈ s, Real.log |g k|) := by
            rw [ih (fun k hk => hs (by simp [hk]))]
        _ = ∑ k ∈ insert xa s, Real.log |g k| := by rw [Finset.sum_insert has]
  exact hgen t (by intro k hk; exact hk)

/-- min of |∏(w−ρk)| over w∈[x,y] (no root in the interval) is attained at an endpoint -/
lemma min_abs_prod_endpoint {ι : Type*} [DecidableEq ι] (s : Finset ι) (ρ : ι → ℝ)
    {x y : ℝ} (hxy : x < y)
    (hnot : ∀ w : ℝ, w ∈ Set.Icc x y → ∀ k : ι, k ∈ s → w ≠ ρ k) :
    ∀ w : ℝ, w ∈ Set.Icc x y →
      min (|(∏ k ∈ s, ((X : Polynomial ℝ) - C (ρ k))).eval x|)
          (|(∏ k ∈ s, ((X : Polynomial ℝ) - C (ρ k))).eval y|) ≤
        |(∏ k ∈ s, ((X : Polynomial ℝ) - C (ρ k))).eval w| := by
  classical
  intro w hw
  let P : Polynomial ℝ := ∏ k ∈ s, (X - C (ρ k))
  let f : ℝ → ℝ := fun z => ∑ k ∈ s, Real.log |z - ρ k|
  have hnot_z : ∀ k : ι, k ∈ s → ρ k < x ∨ y < ρ k := by
    intro k hk
    by_cases h1 : ρ k < x
    · exact Or.inl h1
    · right
      by_contra hnoty
      have hxle : x ≤ ρ k := le_of_not_gt h1
      have hyle : ρ k ≤ y := le_of_not_gt hnoty
      exact hnot (ρ k) ⟨hxle, hyle⟩ k hk rfl
  have hfc : conc f x y := by
    dsimp [f]
    apply conc_sum s (fun k => (fun z : ℝ => Real.log |z - ρ k|)) (x := x) (y := y)
    intro k hk
    exact conc_log_abs (c := ρ k) hxy (hnot_z k hk)
  have hmin : min (f x) (f y) ≤ f w := conc_min_endpoint hxy hfc hw
  -- relate |P z| with exp(f z)
  have hPz : ∀ z : ℝ, P.eval z = ∏ k ∈ s, (z - ρ k) := by
    intro z
    dsimp [P]
    rw [Polynomial.eval_prod]
    simp
  have hPeval : ∀ z : ℝ, z ∈ Set.Icc x y → |P.eval z| ≠ 0 := by
    intro z hz
    rw [hPz z]
    rw [Finset.abs_prod]
    apply ne_of_gt
    apply Finset.prod_pos
    intro k hk
    exact abs_pos.mpr (sub_ne_zero.mpr (hnot z hz k hk))
  have hlogP : ∀ z : ℝ, z ∈ Set.Icc x y → Real.log |P.eval z| = f z := by
    intro z hz
    rw [hPz z]
    rw [Finset.abs_prod]
    dsimp [f]
    exact log_abs_prod s (fun k => z - ρ k) (fun k hk => sub_ne_zero.mpr (hnot z hz k hk))
  have hxi : x ∈ Set.Icc x y := ⟨le_rfl, le_of_lt hxy⟩
  have hyi : y ∈ Set.Icc x y := ⟨le_of_lt hxy, le_rfl⟩
  have hmin' : min (Real.log |P.eval x|) (Real.log |P.eval y|) ≤ Real.log |P.eval w| := by
    simpa [hlogP x hxi, hlogP y hyi, hlogP w hw] using hmin
  have hmono := Real.exp_monotone
  have hm := hmono hmin'
  have hmapmin : min (Real.exp (Real.log |P.eval x|)) (Real.exp (Real.log |P.eval y|))
      = Real.exp (min (Real.log |P.eval x|) (Real.log |P.eval y|)) := by
    rw [hmono.map_min]
  have hm' : min (Real.exp (Real.log |P.eval x|)) (Real.exp (Real.log |P.eval y|)) ≤
      Real.exp (Real.log |P.eval w|) := by
    rwa [← hmapmin] at hm
  have he1 : Real.exp (Real.log |P.eval x|) = |P.eval x| := by
    rw [Real.exp_log_eq_abs (hPeval x hxi), abs_abs]
  have he2 : Real.exp (Real.log |P.eval y|) = |P.eval y| := by
    rw [Real.exp_log_eq_abs (hPeval y hyi), abs_abs]
  have he3 : Real.exp (Real.log |P.eval w|) = |P.eval w| := by
    rw [Real.exp_log_eq_abs (hPeval w hw), abs_abs]
  rwa [he1, he2, he3] at hm'


/-! ## Construction data: root brackets -/

/-- For every fixed real constant `c` there is `N` such that `c ≤ r+3` for all
`r ≥ N`. -/
lemma const_le_r3 (c : ℝ) : ∃ N : ℕ, ∀ r : ℕ, N ≤ r → (c : ℝ) ≤ ((r : ℝ) + 3) := by
  rcases exists_nat_ge (c - 3) with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro r hr
  have hcast : (N : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  linarith

/-- distance between two points of `[a,b]` is at most `b−a`. -/
lemma abs_sub_le_of_mem_Icc {a b x y : ℝ} (hx : x ∈ Set.Icc a b) (hy : y ∈ Set.Icc a b) :
    |x - y| ≤ b - a := by
  rw [abs_sub_le_iff]
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

/-- `C2val ≥ 8`. -/
lemma C2val_ge_eight' : (8 : ℝ) ≤ C2val := by
  dsimp [C2val]
  have hD : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast D_pos
  have hbase : (1 : ℝ) ≤ 128 * (D : ℝ) := by nlinarith
  have hp : (1 : ℝ) ≤ (128 * (D : ℝ)) ^ D := one_le_pow₀ hbase
  nlinarith

/-- Root data of the complementary polynomial (re-run of the
`Submission.CompQRoots.comp_Q_roots_core` construction, keeping the root list,
factorization and separated brackets). -/
lemma root_data (r : ℕ) (hr2 : 2 ≤ r)
    (h6r : (4 : ℝ) / ((kappaC - 1) * kappaC ^ (r - 1)) < 6 * C2val⁻¹)
    (h4r : (4 : ℝ) / ((kappaC - 1) * kappaC ^ (r - 1)) < 4 * C2val⁻¹)
    {T Q0 Q1 Q : Polynomial ℝ} (eps : ℕ → ℝ) (N : ℝ)
    (hTmon : T.Monic) (hTdeg : T.natDegree = r)
    (hTsgn : ∀ i : Fin (r + 1),
      0 < T.eval (bracketPoint r i) * (prunedPoly r).eval (bracketPoint r i))
    (hTmag : ∀ i : Fin (r + 1), |T.eval (bracketPoint r i)| ≥ kappaC ^ r / 64)
    (hQ0 : Q0 = ∏ j' ∈ Finset.range Bclps.Dconst, (T - Polynomial.C (factorCenter r j')))
    (hQ1 : Q1 = Q0 + (∑ t ∈ Finset.Icc 1 (d r), Polynomial.C (eps t) * Bclps.auxPoly t))
    (hQ : Q = Q1 + Polynomial.C N)
    (hEps : ∀ t : ℕ, t ∈ Finset.Icc 1 (d r) → 0 ≤ eps t ∧ eps t < 2)
    (hN0 : 0 ≤ N) (hNle : N ≤ 2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r)) :
    ∃ rho : (Fin r × Fin D) → ℝ,
      ∃ xx yy : (Fin r × Fin D) → ℝ,
        (∀ k : Fin r × Fin D,
          aSerre ≤ xx k ∧ xx k < rho k ∧ rho k < yy k ∧ yy k ≤ bSerre) ∧
        (∀ k : Fin r × Fin D,
          2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ≤ |Q.eval (xx k)| ∧
            2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ≤ |Q.eval (yy k)|) ∧
        Q = (∏ k : Fin r × Fin D, (X - C (rho k))) ∧
        (∀ β : ℝ, Q.eval β = 0 → ∃ k : Fin r × Fin D, β = rho k) ∧
        (∀ k : Fin r × Fin D, ∀ w : ℝ, xx k ≤ w → w ≤ yy k →
          Q.eval w = 0 → w = rho k) ∧
        (∀ ⦃k k' : Fin r × Fin D⦄, k ≠ k' →
          yy k ≤ xx k' ∨ yy k' ≤ xx k) := by
  classical
  let K : ℝ := 2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r)
  have hKpos : 0 < K := by
    dsimp [K]
    exact mul_pos (mul_pos (by norm_num) (inv_pos.mpr C2val_pos))
      (pow_pos kappa_pos (Bclps.Dconst * r))
  have hepsAbs : ∀ t : ℕ, t ∈ Finset.Icc 1 (d r) → |eps t| < 2 := by
    intro t ht
    have h := hEps t ht
    rw [abs_of_nonneg h.1]
    exact h.2
  have hpert : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
      |Q.eval x - Q0.eval x| ≤ kappaC ^ (Bclps.Dconst * r) *
        (4 / ((kappaC - 1) * kappaC ^ (r - 1)) + 2 * C2val⁻¹) := by
    intro x hx
    exact Submission.CompQpert.pert_bound_total r (eps := eps) (N := N) hQ1 hQ hepsAbs hN0 hNle hx
  have hclose8 : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → |Q.eval x - Q0.eval x| <
      8 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by
    intro x hx
    have h := hpert x hx
    have hsum : 4 / ((kappaC - 1) * kappaC ^ (r - 1)) + 2 * C2val⁻¹ < 8 * C2val⁻¹ := by
      nlinarith [h6r]
    have hpos : 0 < kappaC ^ (Bclps.Dconst * r) := pow_pos kappa_pos (Bclps.Dconst * r)
    have hlt : kappaC ^ (Bclps.Dconst * r) *
          (4 / ((kappaC - 1) * kappaC ^ (r - 1)) + 2 * C2val⁻¹) <
        8 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by
      nlinarith [mul_lt_mul_of_pos_right hsum hpos, hpos]
    exact lt_of_le_of_lt h hlt
  have hclose6 : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → |Q.eval x - Q0.eval x| <
      6 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by
    intro x hx
    have h := hpert x hx
    have hsum : 4 / ((kappaC - 1) * kappaC ^ (r - 1)) + 2 * C2val⁻¹ < 6 * C2val⁻¹ := by
      nlinarith [h4r]
    have hpos : 0 < kappaC ^ (Bclps.Dconst * r) := pow_pos kappa_pos (Bclps.Dconst * r)
    have hlt : kappaC ^ (Bclps.Dconst * r) *
          (4 / ((kappaC - 1) * kappaC ^ (r - 1)) + 2 * C2val⁻¹) <
        6 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by
      nlinarith [mul_lt_mul_of_pos_right hsum hpos, hpos]
    exact lt_of_le_of_lt h hlt
  have hgap : ∀ i : Fin r, ∃ s : Fin (D + 1) → ℝ,
      (∀ j : Fin (D + 1), bracketPoint r ⟨i.val + 1, by omega⟩ ≤ s j ∧
          s j ≤ bracketPoint r ⟨i.val, by omega⟩) ∧
      (∀ j : Fin D, s ⟨j.val, by omega⟩ < s ⟨j.val + 1, by omega⟩) ∧
      (∀ j : Fin D, Q.eval (s ⟨j.val, by omega⟩) * Q.eval (s ⟨j.val + 1, by omega⟩) < 0 ∧
        K ≤ |Q.eval (s ⟨j.val, by omega⟩)| ∧ K ≤ |Q.eval (s ⟨j.val + 1, by omega⟩)|) := by
    intro i
    rcases (Submission.CompQRoots.gap_segments r hr2 hQ0 hTsgn hTmag hclose8 hclose6 i)
      with ⟨s, hs1, hs2, hs3⟩
    refine ⟨s, hs1, hs2, ?_⟩
    intro j
    have h3 := hs3 j
    exact ⟨h3.1, by simpa [K] using h3.2.1, by simpa [K] using h3.2.2⟩
  let sfunc : Fin r → Fin (D + 1) → ℝ := fun i => Classical.choose (hgap i)
  have sfunc_spec : ∀ i : Fin r,
      (∀ j : Fin (D + 1), bracketPoint r ⟨i.val + 1, by omega⟩ ≤ sfunc i j ∧
          sfunc i j ≤ bracketPoint r ⟨i.val, by omega⟩) ∧
      (∀ j : Fin D, sfunc i ⟨j.val, by omega⟩ < sfunc i ⟨j.val + 1, by omega⟩) ∧
      (∀ j : Fin D, Q.eval (sfunc i ⟨j.val, by omega⟩) * Q.eval (sfunc i ⟨j.val + 1, by omega⟩) < 0 ∧
        K ≤ |Q.eval (sfunc i ⟨j.val, by omega⟩)| ∧ K ≤ |Q.eval (sfunc i ⟨j.val + 1, by omega⟩)|) :=
    fun i => Classical.choose_spec (hgap i)
  let xx : Fin r × Fin D → ℝ := fun k => sfunc k.1 ⟨k.2.val, by omega⟩
  let yy : Fin r × Fin D → ℝ := fun k => sfunc k.1 ⟨k.2.val + 1, by omega⟩
  have hdeg : Q0.Monic ∧ Q0.natDegree = Bclps.Dconst * r ∧ Q.Monic ∧ Q.natDegree = Bclps.Dconst * r :=
    Submission.CompQdeg.monic_degree r (by omega : 1 ≤ r) eps N hTmon hTdeg hQ0 hQ1 hQ
  have hGmon : Q.Monic := hdeg.2.2.1
  have hQdegDr : Q.natDegree = Bclps.Dconst * r := hdeg.2.2.2
  have hGdeg : Q.natDegree = Fintype.card (Fin r × Fin D) := by
    rw [hQdegDr]
    calc
      (Bclps.Dconst * r) = r * Bclps.Dconst := by rw [mul_comm]
      _ = r * D := rfl
      _ = Fintype.card (Fin r × Fin D) := by
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hxy : ∀ k : Fin r × Fin D, xx k < yy k := by
    intro k
    dsimp [xx, yy]
    exact (sfunc_spec k.1).2.1 k.2
  have hsign : ∀ k : Fin r × Fin D, Q.eval (xx k) * Q.eval (yy k) < 0 := by
    intro k
    dsimp [xx, yy]
    exact ((sfunc_spec k.1).2.2 k.2).1
  have hIcc : ∀ k : Fin r × Fin D, aSerre ≤ xx k ∧ yy k ≤ bSerre := by
    intro k
    dsimp [xx, yy]
    have hx : aSerre ≤ sfunc k.1 ⟨k.2.val, by omega⟩ :=
      le_trans (bracketPoint_mem_Icc r ⟨k.1.val + 1, by omega⟩).1
        ((sfunc_spec k.1).1 ⟨k.2.val, by omega⟩).1
    have hy : sfunc k.1 ⟨k.2.val + 1, by omega⟩ ≤ bSerre :=
      le_trans ((sfunc_spec k.1).1 ⟨k.2.val + 1, by omega⟩).2
        (bracketPoint_mem_Icc r ⟨k.1.val, by omega⟩).2
    exact ⟨hx, hy⟩
  have hK : ∀ k : Fin r × Fin D, K ≤ |Q.eval (xx k)| ∧ K ≤ |Q.eval (yy k)| := by
    intro k
    dsimp [xx, yy]
    exact ⟨((sfunc_spec k.1).2.2 k.2).2.1, ((sfunc_spec k.1).2.2 k.2).2.2⟩
  have hsep : ∀ ⦃k k' : Fin r × Fin D⦄, k ≠ k' → yy k ≤ xx k' ∨ yy k' ≤ xx k := by
    intro k k' hkk'
    by_cases h1 : k.1.val < k'.1.val
    · right
      have hA : yy k' ≤ bracketPoint r ⟨k'.1.val, by omega⟩ := by
        dsimp [yy]
        exact ((sfunc_spec k'.1).1 ⟨k'.2.val + 1, by omega⟩).2
      have hB : bracketPoint r ⟨k'.1.val, by omega⟩ ≤ bracketPoint r ⟨k.1.val + 1, by omega⟩ :=
        Submission.CompQRoots.gap_cross (r := r) (i := k.1) (j := k'.1) h1
      have hC : bracketPoint r ⟨k.1.val + 1, by omega⟩ ≤ xx k := by
        dsimp [xx]
        exact ((sfunc_spec k.1).1 ⟨k.2.val, by omega⟩).1
      exact le_trans hA (le_trans hB hC)
    · by_cases h2 : k'.1.val < k.1.val
      · left
        have hA : yy k ≤ bracketPoint r ⟨k.1.val, by omega⟩ := by
          dsimp [yy]
          exact ((sfunc_spec k.1).1 ⟨k.2.val + 1, by omega⟩).2
        have hB : bracketPoint r ⟨k.1.val, by omega⟩ ≤ bracketPoint r ⟨k'.1.val + 1, by omega⟩ :=
          Submission.CompQRoots.gap_cross (r := r) (i := k'.1) (j := k.1) h2
        have hC : bracketPoint r ⟨k'.1.val + 1, by omega⟩ ≤ xx k' := by
          dsimp [xx]
          exact ((sfunc_spec k'.1).1 ⟨k'.2.val, by omega⟩).1
        exact le_trans hA (le_trans hB hC)
      · have hEq : k.1 = k'.1 := by
          apply Fin.ext
          omega
        have hne2 : k.2 ≠ k'.2 := by
          intro h
          exact hkk' (Prod.ext hEq h)
        have hj : k.2.val < k'.2.val ∨ k'.2.val < k.2.val :=
          lt_or_gt_of_ne (fun h => hne2 (Fin.ext h))
        rcases hj with hjlt | hjgt
        · left
          have hmon : sfunc k'.1 ⟨k.2.val + 1, by omega⟩ ≤ sfunc k'.1 ⟨k'.2.val, by omega⟩ :=
            Submission.CompQRoots.chain_mono_nat (s := sfunc k'.1) (sfunc_spec k'.1).2.1
              (k.2.val + 1) k'.2.val (by omega) (by omega)
          have hyy : yy k ≤ xx k' := by
            dsimp [yy, xx]
            rw [hEq]
            exact hmon
          exact hyy
        · right
          have hmon : sfunc k'.1 ⟨k'.2.val + 1, by omega⟩ ≤ sfunc k'.1 ⟨k.2.val, by omega⟩ :=
            Submission.CompQRoots.chain_mono_nat (s := sfunc k'.1) (sfunc_spec k'.1).2.1
              (k'.2.val + 1) k.2.val (by omega) (by omega)
          have hyy : yy k' ≤ xx k := by
            dsimp [yy, xx]
            rw [hEq]
            exact hmon
          exact hyy
  rcases (Submission.CompQRoots.split_of_segments (G := Q) hGmon hGdeg hxy hsign hIcc hK hsep)
    with ⟨rho, hrho1, hfacQ, hclassQ, hbracket⟩
  refine ⟨rho, xx, yy, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro k
    have hbr : xx k < rho k ∧ rho k < yy k ∧ Q.eval (rho k) = 0 := hrho1 k
    exact ⟨(hIcc k).1, hbr.1, hbr.2.1, (hIcc k).2⟩
  · intro k
    exact ⟨by simpa [K] using (hK k).1, by simpa [K] using (hK k).2⟩
  · exact hfacQ
  · intro β hβ
    rcases hclassQ β hβ with ⟨k, hkβ⟩
    exact ⟨k, hkβ⟩
  · intro k w hxw hyw hwroot
    have hw := hbracket k w hxw hyw hwroot
    exact hw
  · intro k k' hne
    exact hsep (k := k) (k' := k') hne


/-- **Norms and local growth of the complementary polynomial.**  From the
`defn:comp_Q` data (as in `Submission.CompQRoots.comp_Q_roots`), for all
`r ≥ C`: sup-norms of `Q` and `Q′` are `≤ r^C·κ^{Dr}`, and each root `β` of
`Q` has the linear local-growth lower bound on the ball of radius `r^{−C}`. -/
theorem comp_Q_roots2 : ∃ C : ℝ, 0 < C ∧ 1 ≤ C ∧
  ∀ (r : ℕ), (C : ℝ) ≤ (r : ℝ) → 2 ≤ r →
  ∀ (T Q0 Q1 Q : Polynomial ℝ) (eps : ℕ → ℝ) (N : ℝ),
    T.Monic → T.natDegree = r →
    (∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
      |T.eval x - (prunedPoly r).eval x| ≤ kappaC ^ r / 64) →
    (∀ i : Fin (r + 1),
      0 < T.eval (bracketPoint r i) * (prunedPoly r).eval (bracketPoint r i) ∧
      |T.eval (bracketPoint r i)| ≥ kappaC ^ r / 64) →
    Q0 = ∏ j' ∈ Finset.range Bclps.Dconst,
          (T - Polynomial.C (factorCenter r j')) →
    Q1 = Q0 + (∑ t ∈ Finset.Icc 1 (d r),
          Polynomial.C (eps t) * Bclps.auxPoly t) →
    Q = Q1 + Polynomial.C N →
    (∀ t : ℕ, t ∈ Finset.Icc 1 (d r) → 0 ≤ eps t ∧ eps t < 2) →
    0 ≤ N → N ≤ 2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) →
    DivLinear.supNorm Q ≤ (((r : ℝ) + 3) ^ C) * kappaC ^ (Bclps.Dconst * r) ∧
    DivLinear.supNorm Q.derivative ≤ (((r : ℝ) + 3) ^ C) * kappaC ^ (Bclps.Dconst * r) ∧
    (∀ β : ℝ, Q.eval β = 0 → ∀ w : ℝ, |w - β| ≤ ((r : ℝ) + 3) ^ (-C) →
      |Q.eval w| ≥ ((r : ℝ) + 3) ^ (-C) * kappaC ^ (Bclps.Dconst * r) * |w - β|) := by
  classical
  rcases Submission.CompQNums.large_r with ⟨C6, hC6⟩
  rcases Submission.CompQRoots.large_r4 with ⟨C4, hC4⟩
  let N0 : ℕ := 7 * Bclps.Dconst + 2
  let N1 : ℕ := N0 + 4
  rcases const_le_r3 (2 * (D : ℝ) ^ 2 / (bSerre - aSerre)) with ⟨Rabs, hRabs⟩
  rcases const_le_r3 (C2val * (bSerre - aSerre)) with ⟨Rbig, hRbig⟩
  let CN : ℕ := max (max C6 C4) (max Rabs (max Rbig (max (N1 + 1) 2)))
  have hCN2 : 2 ≤ CN := by
    dsimp [CN]
    omega
  refine ⟨(CN : ℝ), ?_⟩
  · constructor
    · exact_mod_cast (lt_of_lt_of_le (by omega : (0 : ℕ) < 2) hCN2)
    · constructor
      · exact_mod_cast (le_trans (by omega : (1 : ℕ) ≤ 2) hCN2)
      · intro r hrC hr2
        have hCNr : CN ≤ r := by exact_mod_cast hrC
        have hrC6 : C6 ≤ r := by dsimp [CN] at hCNr; omega
        have hrC4 : C4 ≤ r := by dsimp [CN] at hCNr; omega
        have hrRabs : Rabs ≤ r := by dsimp [CN] at hCNr; omega
        have hrRbig : Rbig ≤ r := by dsimp [CN] at hCNr; omega
        have hN1r : N1 + 1 ≤ r := by dsimp [CN] at hCNr; omega
        have hN0CN : N0 ≤ CN := by dsimp [CN, N0, N1]; omega
        have hN1CN : N1 ≤ CN := by dsimp [CN, N1]; omega
        have hkappa_nonneg : ∀ n : ℕ, (0 : ℝ) ≤ kappaC ^ n := fun n =>
          pow_nonneg (le_of_lt kappa_pos) n
        have hkappa_posn : ∀ n : ℕ, (0 : ℝ) < kappaC ^ n := fun n =>
          pow_pos kappa_pos n
        let xr : ℝ := (r : ℝ) + 3
        have hxr1 : 1 ≤ xr := by
          dsimp [xr]
          have hrR : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr2
          linarith
        have hxrpos : 0 < xr := by linarith
        have hxr0 : 0 ≤ xr := le_of_lt hxrpos
        intro T Q0 Q1 Q eps N hTmon hTdeg hTclose hTsm hQ0 hQ1 hQ hEps hN0 hNle
        have hr1 : 1 ≤ r := by omega
        have hTsgn : ∀ i : Fin (r + 1),
            0 < T.eval (bracketPoint r i) * (prunedPoly r).eval (bracketPoint r i) :=
          fun i => (hTsm i).1
        have hTmag : ∀ i : Fin (r + 1), |T.eval (bracketPoint r i)| ≥ kappaC ^ r / 64 :=
          fun i => (hTsm i).2
        have h6r : (4 : ℝ) / ((kappaC - 1) * kappaC ^ (r - 1)) < 6 * C2val⁻¹ := by
          simpa [div_eq_mul_inv] using (hC6 r hrC6)
        have h4r : (4 : ℝ) / ((kappaC - 1) * kappaC ^ (r - 1)) < 4 * C2val⁻¹ := by
          simpa [div_eq_mul_inv] using (hC4 r hrC4)
        -- ‖Q‖ pointwise bound
        have hTle : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
            |T.eval x| ≤ xr ^ 6 * kappaC ^ r + kappaC ^ r / 64 := by
          intro x hx
          have hp := AdjustedCheb.prunedPoly_bound r hr2 hx
          have hp' : |(prunedPoly r).eval x| ≤ xr ^ 6 * kappaC ^ r := by
            have hcast : ((r + 3 : ℕ) : ℝ) = xr := by
              dsimp [xr]
              norm_num
            simpa [hcast] using hp
          have hcl := hTclose x hx
          calc
            |T.eval x| = |(prunedPoly r).eval x + (T.eval x - (prunedPoly r).eval x)| := by
                  congr 1
                  ring
            _ ≤ |(prunedPoly r).eval x| + |T.eval x - (prunedPoly r).eval x| := abs_add_le _ _
            _ ≤ xr ^ 6 * kappaC ^ r + kappaC ^ r / 64 := by
                  have h := add_le_add hp' hcl
                  nlinarith [h]
        have hTb : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → |T.eval x| ≤ xr ^ 7 * kappaC ^ r := by
          intro x hx
          have htl := hTle x hx
          have hpos : 0 ≤ kappaC ^ r := hkappa_nonneg r
          have h7 : xr ^ 6 + 1 / 64 ≤ xr ^ 7 := by
            have hxr6 : 1 ≤ xr ^ 6 := one_le_pow₀ hxr1
            have hx2 : (2 : ℝ) ≤ xr := by dsimp [xr]; linarith
            have hbig2 : 2 * xr ^ 6 ≤ xr ^ 7 := by
              calc
                2 * xr ^ 6 ≤ xr * xr ^ 6 :=
                  mul_le_mul_of_nonneg_right hx2 (pow_nonneg hxr0 6)
                _ = xr ^ 7 := by
                    have h61 : xr ^ (6 + 1) = xr * xr ^ 6 := by rw [pow_succ']
                    rw [show xr ^ 7 = xr ^ (6 + 1) by norm_num, h61]
            nlinarith
          calc
            |T.eval x| ≤ xr ^ 6 * kappaC ^ r + kappaC ^ r / 64 := htl
            _ = (xr ^ 6 + 1 / 64) * kappaC ^ r := by ring
            _ ≤ xr ^ 7 * kappaC ^ r := by
                exact mul_le_mul_of_nonneg_right h7 hpos
        have hfact : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → ∀ j' : ℕ, j' < Bclps.Dconst →
            |(T - Polynomial.C (factorCenter r j')).eval x| ≤ xr ^ 7 * kappaC ^ r := by
          intro x hx j' hj'
          have hT1 := hTle x hx
          have hc : factorCenter r j' ≤ kappaC ^ r / 64 := le_of_lt (factor_center_lt hj')
          have hc0 : 0 ≤ factorCenter r j' := le_of_lt (factorCenter_pos r j')
          have hmain : |(T - C (factorCenter r j')).eval x| ≤ |T.eval x| + factorCenter r j' := by
            have heval : (T - C (factorCenter r j')).eval x = T.eval x - factorCenter r j' := by
              simp
            rw [heval, sub_eq_add_neg]
            calc
              |T.eval x + -factorCenter r j'| ≤ |T.eval x| + |-factorCenter r j'| := abs_add_le _ _
              _ = |T.eval x| + factorCenter r j' := by
                  rw [abs_neg, abs_of_nonneg hc0]
          have hbig : |T.eval x| + factorCenter r j' ≤ xr ^ 7 * kappaC ^ r := by
            have hpos : 0 ≤ kappaC ^ r := hkappa_nonneg r
            have htl2 : |T.eval x| + factorCenter r j' ≤ xr ^ 6 * kappaC ^ r + kappaC ^ r / 32 := by
              have h1 := add_le_add hT1 hc
              nlinarith [h1]
            have h7 : xr ^ 6 + 1 / 32 ≤ xr ^ 7 := by
              have hxr6 : 1 ≤ xr ^ 6 := one_le_pow₀ hxr1
              have hx2 : (2 : ℝ) ≤ xr := by dsimp [xr]; linarith
              have hbig2 : 2 * xr ^ 6 ≤ xr ^ 7 := by
                calc
                  2 * xr ^ 6 ≤ xr * xr ^ 6 :=
                    mul_le_mul_of_nonneg_right hx2 (pow_nonneg hxr0 6)
                  _ = xr ^ 7 := by
                      have h61 : xr ^ (6 + 1) = xr * xr ^ 6 := by rw [pow_succ']
                      rw [show xr ^ 7 = xr ^ (6 + 1) by norm_num, h61]
              nlinarith
            calc
              |T.eval x| + factorCenter r j' ≤ xr ^ 6 * kappaC ^ r + kappaC ^ r / 32 := htl2
              _ = (xr ^ 6 + 1 / 32) * kappaC ^ r := by ring
              _ ≤ xr ^ 7 * kappaC ^ r := by
                  exact mul_le_mul_of_nonneg_right h7 hpos
          exact le_trans hmain hbig
        have hQ0pt : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
            |Q0.eval x| ≤ xr ^ (7 * Bclps.Dconst) * kappaC ^ (Bclps.Dconst * r) := by
          intro x hx
          rw [hQ0]
          rw [Polynomial.eval_prod]
          calc
            |∏ j' ∈ Finset.range Bclps.Dconst, (T - C (factorCenter r j')).eval x|
                = ∏ j' ∈ Finset.range Bclps.Dconst,
                    |(T - C (factorCenter r j')).eval x| := by
                    rw [Finset.abs_prod]
            _ ≤ ∏ j' ∈ Finset.range Bclps.Dconst, (xr ^ 7 * kappaC ^ r) := by
                apply Finset.prod_le_prod
                · intro j' hj'
                  exact abs_nonneg _
                · intro j' hj'
                  exact hfact x hx j' (Finset.mem_range.mp hj')
            _ = (xr ^ 7 * kappaC ^ r) ^ Bclps.Dconst := by
                rw [Finset.prod_const, Finset.card_range]
            _ = (xr ^ 7) ^ Bclps.Dconst * (kappaC ^ r) ^ Bclps.Dconst := by rw [mul_pow]
            _ = xr ^ (7 * Bclps.Dconst) * kappaC ^ (Bclps.Dconst * r) := by
                have h1 : (xr ^ 7) ^ Bclps.Dconst = xr ^ (7 * Bclps.Dconst) := by
                  rw [← pow_mul]
                have h2 : (kappaC ^ r) ^ Bclps.Dconst = kappaC ^ (Bclps.Dconst * r) := by
                  rw [← pow_mul]
                  rw [Nat.mul_comm r Bclps.Dconst]
                rw [h1, h2]
        have hepsAbs : ∀ t : ℕ, t ∈ Finset.Icc 1 (d r) → |eps t| < 2 := by
          intro t ht
          have h := hEps t ht
          rw [abs_of_nonneg h.1]
          exact h.2
        have hpert : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → |Q.eval x - Q0.eval x| ≤
            kappaC ^ (Bclps.Dconst * r) *
              (4 / ((kappaC - 1) * kappaC ^ (r - 1)) + 2 * C2val⁻¹) := by
          intro x hx
          exact Submission.CompQpert.pert_bound_total r (eps := eps) (N := N) hQ1 hQ hepsAbs
            hN0 hNle hx
        have hpert_small : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
            |Q.eval x - Q0.eval x| ≤ kappaC ^ (Bclps.Dconst * r) := by
          intro x hx
          have h := hpert x hx
          have hlt : 4 / ((kappaC - 1) * kappaC ^ (r - 1)) + 2 * C2val⁻¹ ≤ 1 := by
            have h8 : (8 : ℝ) ≤ C2val := C2val_ge_eight'
            have hC2pos : 0 < C2val := C2val_pos
            have h41 : 4 * C2val⁻¹ ≤ 1 / 2 := by
              have hinv : C2val⁻¹ ≤ (8 : ℝ)⁻¹ := by
                exact (inv_le_inv₀ hC2pos (by norm_num)).2 h8
              nlinarith
            have h41' : 4 / C2val ≤ 1 / 2 := by
              simpa [div_eq_mul_inv] using h41
            have h4small : 4 / ((kappaC - 1) * kappaC ^ (r - 1)) < 4 / C2val := by
              simpa [div_eq_mul_inv] using h4r
            have h4small' : 4 / ((kappaC - 1) * kappaC ^ (r - 1)) < 1 / 2 :=
              lt_of_lt_of_le h4small h41'
            have h2 : 2 * C2val⁻¹ ≤ 1 / 4 := by
              have hinv : C2val⁻¹ ≤ (8 : ℝ)⁻¹ := by
                exact (inv_le_inv₀ hC2pos (by norm_num)).2 h8
              nlinarith
            nlinarith
          have hpos : 0 ≤ kappaC ^ (Bclps.Dconst * r) := hkappa_nonneg (Bclps.Dconst * r)
          calc
            |Q.eval x - Q0.eval x| ≤ kappaC ^ (Bclps.Dconst * r) *
                (4 / ((kappaC - 1) * kappaC ^ (r - 1)) + 2 * C2val⁻¹) := h
            _ ≤ kappaC ^ (Bclps.Dconst * r) * 1 := by
                exact mul_le_mul_of_nonneg_left hlt hpos
            _ = kappaC ^ (Bclps.Dconst * r) := by ring
        have hQpt : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
            |Q.eval x| ≤ xr ^ N0 * kappaC ^ (Bclps.Dconst * r) := by
          intro x hx
          have h0 := hQ0pt x hx
          have hp := hpert_small x hx
          have hmain : |Q.eval x| ≤ |Q0.eval x| + |Q.eval x - Q0.eval x| := by
            calc
              |Q.eval x| = |Q0.eval x + (Q.eval x - Q0.eval x)| := by congr 1; ring
              _ ≤ |Q0.eval x| + |Q.eval x - Q0.eval x| := abs_add_le _ _
          have hsum : |Q0.eval x| + |Q.eval x - Q0.eval x| ≤
              xr ^ N0 * kappaC ^ (Bclps.Dconst * r) := by
            have hpos : 0 ≤ kappaC ^ (Bclps.Dconst * r) := hkappa_nonneg (Bclps.Dconst * r)
            have hA1 : (1 : ℝ) ≤ xr ^ (7 * Bclps.Dconst) := one_le_pow₀ hxr1
            have hpart2 : |Q.eval x - Q0.eval x| ≤
                xr ^ (7 * Bclps.Dconst) * kappaC ^ (Bclps.Dconst * r) := by
              exact le_trans hp (by
                simpa using (mul_le_mul_of_nonneg_right hA1 hpos))
            have h2 : 2 * xr ^ (7 * Bclps.Dconst) ≤ xr ^ N0 := by
              have hx2 : (2 : ℝ) ≤ xr := by dsimp [xr]; linarith
              have h1 : 2 * xr ^ (7 * Bclps.Dconst) ≤ xr * xr ^ (7 * Bclps.Dconst) := by
                exact mul_le_mul_of_nonneg_right hx2 (pow_nonneg hxr0 (7 * Bclps.Dconst))
              calc
                2 * xr ^ (7 * Bclps.Dconst) ≤ xr * xr ^ (7 * Bclps.Dconst) := h1
                _ = xr ^ (7 * Bclps.Dconst + 1) := by
                    have hsucc : xr ^ (7 * Bclps.Dconst + 1) = xr ^ (7 * Bclps.Dconst) * xr := by
                      rw [pow_succ]
                    rw [hsucc]
                    ring
                _ ≤ xr ^ N0 := by
                    apply pow_le_pow_right₀ hxr1
                    dsimp [N0]
                    omega
            calc
              |Q0.eval x| + |Q.eval x - Q0.eval x|
                  ≤ xr ^ (7 * Bclps.Dconst) * kappaC ^ (Bclps.Dconst * r)
                      + xr ^ (7 * Bclps.Dconst) * kappaC ^ (Bclps.Dconst * r) :=
                      add_le_add h0 hpart2
              _ = 2 * xr ^ (7 * Bclps.Dconst) * kappaC ^ (Bclps.Dconst * r) := by ring
              _ ≤ xr ^ N0 * kappaC ^ (Bclps.Dconst * r) := by
                  exact mul_le_mul_of_nonneg_right h2 hpos
          exact le_trans (le_trans hmain hsum) (by rfl)
        have hsupQ : DivLinear.supNorm Q ≤ xr ^ N0 * kappaC ^ (Bclps.Dconst * r) := by
          rw [DivLinear.supNorm_le_iff]
          exact hQpt
        -- derivative bound via Markov
        have hdegQ : Q.natDegree = Bclps.Dconst * r := by
          exact (Submission.CompQdeg.monic_degree r hr1 eps N hTmon hTdeg hQ0 hQ1 hQ).2.2.2
        have hderbd : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
            |Q.derivative.eval x| ≤ xr ^ N1 * kappaC ^ (Bclps.Dconst * r) := by
          intro x hx
          have hdegle : Q.natDegree ≤ Bclps.Dconst * r := by rw [hdegQ]
          have hM0 : 0 ≤ xr ^ N0 * kappaC ^ (Bclps.Dconst * r) := by
            exact mul_nonneg (pow_nonneg hxr0 N0) (hkappa_nonneg (Bclps.Dconst * r))
          have hbdy : ∀ y : ℝ, y ∈ Set.Icc aSerre bSerre →
              |Q.eval y| ≤ xr ^ N0 * kappaC ^ (Bclps.Dconst * r) := hQpt
          have hmm := Submission.MarkovInterval.markov_interval (P := Q) (n := Bclps.Dconst * r)
            hdegle hM0 hbdy x hx
          have hmm' : |Q.derivative.eval x| ≤
              (2 * ((Bclps.Dconst * r : ℕ) : ℝ) ^ 2 / (bSerre - aSerre)) *
                (xr ^ N0 * kappaC ^ (Bclps.Dconst * r)) := by
            simpa using hmm
          have habs1 : (2 * ((Bclps.Dconst * r : ℕ) : ℝ) ^ 2 / (bSerre - aSerre)) *
                (xr ^ N0 * kappaC ^ (Bclps.Dconst * r)) ≤
              xr ^ N1 * kappaC ^ (Bclps.Dconst * r) := by
            have hpos : 0 ≤ kappaC ^ (Bclps.Dconst * r) := hkappa_nonneg (Bclps.Dconst * r)
            have hc : (2 * ((Bclps.Dconst * r : ℕ) : ℝ) ^ 2 / (bSerre - aSerre)) * xr ^ N0 ≤
                xr ^ N1 := by
              have hcast : ((Bclps.Dconst * r : ℕ) : ℝ) = (Bclps.Dconst : ℝ) * (r : ℝ) := by
                exact_mod_cast rfl
              have hD : (Bclps.Dconst : ℝ) = (D : ℝ) := by rfl
              have hrle : (r : ℝ) ^ 2 ≤ xr ^ 2 := by
                rw [sq_le_sq]
                have hr0 : 0 ≤ (r : ℝ) := by exact_mod_cast (Nat.zero_le r)
                rw [abs_of_nonneg hr0, abs_of_nonneg hxr0]
                dsimp [xr]
                linarith
              have hL : 0 < bSerre - aSerre := by norm_num [aSerre, bSerre]
              have hA : 0 ≤ 2 * (D : ℝ) ^ 2 / (bSerre - aSerre) := by
                exact div_nonneg (by positivity) (le_of_lt hL)
              have hR := hRabs r hrRabs
              have h1 : (2 * (D : ℝ) ^ 2 / (bSerre - aSerre)) ≤ xr := by
                simpa using hR
              calc
                (2 * ((Bclps.Dconst * r : ℕ) : ℝ) ^ 2 / (bSerre - aSerre)) * xr ^ N0
                    = ((2 * (D : ℝ) ^ 2 / (bSerre - aSerre)) * (r : ℝ) ^ 2) * xr ^ N0 := by
                        rw [hcast, hD, mul_pow]
                        ring
                _ ≤ ((2 * (D : ℝ) ^ 2 / (bSerre - aSerre)) * xr ^ 2) * xr ^ N0 := by
                        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrle hA)
                          (pow_nonneg hxr0 N0)
                _ = (2 * (D : ℝ) ^ 2 / (bSerre - aSerre)) * xr ^ 2 * xr ^ N0 := by ring
                _ ≤ xr * xr ^ 2 * xr ^ N0 := by
                        exact mul_le_mul_of_nonneg_right
                          (mul_le_mul_of_nonneg_right h1 (pow_nonneg hxr0 2))
                          (pow_nonneg hxr0 N0)
                _ = xr ^ (N0 + 3) := by
                        have h3 : xr ^ 3 = xr * xr ^ 2 := by
                          rw [show xr ^ 3 = xr ^ (2 + 1) by norm_num]
                          rw [pow_succ']
                        have hpow : xr * xr ^ 2 * xr ^ N0 = xr ^ (N0 + 3) := by
                          rw [show xr * xr ^ 2 = xr ^ 3 by rw [h3]]
                          rw [← pow_add]
                          congr 1
                          omega
                        exact hpow
                _ ≤ xr ^ N1 := by
                        apply pow_le_pow_right₀ hxr1
                        dsimp [N1]
                        omega
            calc
              (2 * ((Bclps.Dconst * r : ℕ) : ℝ) ^ 2 / (bSerre - aSerre)) *
                  (xr ^ N0 * kappaC ^ (Bclps.Dconst * r))
                  = ((2 * ((Bclps.Dconst * r : ℕ) : ℝ) ^ 2 / (bSerre - aSerre)) * xr ^ N0) *
                      kappaC ^ (Bclps.Dconst * r) := by ring
              _ ≤ xr ^ N1 * kappaC ^ (Bclps.Dconst * r) := by
                  exact mul_le_mul_of_nonneg_right hc hpos
          exact le_trans hmm' habs1
        have hsupQder : DivLinear.supNorm Q.derivative ≤ xr ^ N1 * kappaC ^ (Bclps.Dconst * r) := by
          rw [DivLinear.supNorm_le_iff]
          exact hderbd
        -- convert natural-exponent bounds to exponent CN (real)
        have hsupQr : DivLinear.supNorm Q ≤ xr ^ (CN : ℝ) * kappaC ^ (Bclps.Dconst * r) := by
          have hcast : xr ^ N0 = xr ^ (N0 : ℝ) := by rw [Real.rpow_natCast]
          calc
            DivLinear.supNorm Q ≤ xr ^ N0 * kappaC ^ (Bclps.Dconst * r) := hsupQ
            _ = xr ^ (N0 : ℝ) * kappaC ^ (Bclps.Dconst * r) := by rw [hcast]
            _ ≤ xr ^ (CN : ℝ) * kappaC ^ (Bclps.Dconst * r) := by
                exact mul_le_mul_of_nonneg_right
                  (Real.rpow_le_rpow_of_exponent_le hxr1 (by exact_mod_cast hN0CN))
                  (hkappa_nonneg (Bclps.Dconst * r))
        have hsupQdr : DivLinear.supNorm Q.derivative ≤ xr ^ (CN : ℝ) * kappaC ^ (Bclps.Dconst * r) := by
          have hcast : xr ^ N1 = xr ^ (N1 : ℝ) := by rw [Real.rpow_natCast]
          calc
            DivLinear.supNorm Q.derivative ≤ xr ^ N1 * kappaC ^ (Bclps.Dconst * r) := hsupQder
            _ = xr ^ (N1 : ℝ) * kappaC ^ (Bclps.Dconst * r) := by rw [hcast]
            _ ≤ xr ^ (CN : ℝ) * kappaC ^ (Bclps.Dconst * r) := by
                exact mul_le_mul_of_nonneg_right
                  (Real.rpow_le_rpow_of_exponent_le hxr1 (by exact_mod_cast hN1CN))
                  (hkappa_nonneg (Bclps.Dconst * r))
        -- local growth
        have hlocal : ∀ β : ℝ, Q.eval β = 0 → ∀ w : ℝ, |w - β| ≤ xr ^ (-(CN : ℝ)) →
            xr ^ (-(CN : ℝ)) * kappaC ^ (Bclps.Dconst * r) * |w - β| ≤ |Q.eval w| := by
          let B0 : ℝ := 2 * C2val⁻¹
          let ρ : ℝ := xr ^ (-(CN : ℝ))
          have hbig : C2val * (bSerre - aSerre) ≤ xr := by
            have hR := hRbig r hrRbig
            simpa [xr] using hR
          have hL0 : (0 : ℝ) < bSerre - aSerre := by
            exact lt_trans (by norm_num : (0 : ℝ) < 4)
              (Submission.SerreExample.cap_gt_one)
          have hL04 : (4 : ℝ) ≤ bSerre - aSerre := le_of_lt (Submission.SerreExample.cap_gt_one)
          have hxrge : C2val / 2 ≤ xr := by
            have hC2 : 0 ≤ C2val := le_of_lt C2val_pos
            have hm : C2val * (bSerre - aSerre) ≤ xr := hbig
            have h1 : C2val / 2 ≤ C2val * (bSerre - aSerre) := by
              have hL1 : (1 : ℝ) ≤ bSerre - aSerre := by linarith
              -- C2val/2 ≤ C2val·L0  ⟸ 1 ≤ 2·L0 (C2val≥0)
              nlinarith [hL1]
            exact le_trans h1 hbig
          have hC2pos : 0 < C2val := C2val_pos
          have hB0 : (0 : ℝ) < B0 := by
            dsimp [B0]
            exact mul_pos (by norm_num) (inv_pos.mpr hC2pos)
          have hB0ge : (0 : ℝ) ≤ B0 := le_of_lt hB0
          have hρform : xr ^ (-(CN : ℝ)) = (xr ^ CN)⁻¹ := by
            rw [Real.rpow_neg hxr0]
            rw [Real.rpow_natCast]
          have hρmul : ρ * xr ^ CN = 1 := by
            dsimp [ρ]
            rw [← Real.rpow_natCast]
            rw [← Real.rpow_add hxrpos]
            have h : -(CN : ℝ) + (CN : ℝ) = 0 := by ring
            rw [h, Real.rpow_zero]
          have hρ_le : ∀ c : ℝ, (1 ≤ c * xr ^ CN) → ρ ≤ c := by
            intro c hc
            refine (mul_le_mul_iff_of_pos_right (pow_pos hxrpos CN)).1 ?_
            rw [hρmul]
            exact hc
          have hCN1 : 1 ≤ CN := by dsimp [CN]; omega
          have hCNgN1 : N1 + 1 ≤ CN := by dsimp [CN]; omega
          have hxp : xr ≤ xr ^ (CN - N1) := by
            have h1 : 1 ≤ CN - N1 := by omega
            have hbase : xr ≤ xr ^ 1 := by rw [pow_one]
            exact le_trans hbase (pow_le_pow_right₀ hxr1 h1)
          have hB0big1 : 1 ≤ B0 * xr ^ CN := by
            -- B0·xr^{CN} ≥ B0·xr^{N1}·xr ≥ ... we show via xr^{CN} ≥ xr·xr^{N1} hmm direct:
            -- simpler: xr^{CN} ≥ xr ≥ C2val·L0 and B0·C2val·L0 ≥ 2 ≥ 1 with CN ≥ 1
            have h1 : xr ≤ xr ^ CN := by
              have hb : xr ≤ xr ^ 1 := by rw [pow_one]
              exact le_trans hb (pow_le_pow_right₀ hxr1 hCN1)
            have h2 : C2val * (bSerre - aSerre) ≤ xr ^ CN := le_trans hbig h1
            have h3 : (2 * C2val⁻¹) * (C2val * (bSerre - aSerre)) ≤ B0 * xr ^ CN := by
              dsimp [B0]
              exact mul_le_mul_of_nonneg_left h2 (by positivity : 0 ≤ 2 * C2val⁻¹)
            have h4 : (1 : ℝ) ≤ (2 * C2val⁻¹) * (C2val * (bSerre - aSerre)) := by
              have h5 : (2 * C2val⁻¹) * (C2val * (bSerre - aSerre)) = 2 * (bSerre - aSerre) := by
                calc
                  (2 * C2val⁻¹) * (C2val * (bSerre - aSerre))
                      = ((2 * C2val⁻¹) * C2val) * (bSerre - aSerre) := by ring
                  _ = 2 * (bSerre - aSerre) := by
                      congr 1
                      field_simp [ne_of_gt hC2pos]
              rw [h5]
              nlinarith [hL04]
            exact le_trans h4 h3
          have hx0y0_w : ∀ β0 x0 y0 : ℝ, (x0 < β0 ∧ β0 < y0) →
              (ρ ≤ β0 - x0) → (ρ ≤ y0 - β0) → ∀ w : ℝ, |w - β0| ≤ ρ →
                w ∈ Set.Icc x0 y0 := by
            intro β0 x0 y0 hxy hρx hρy w hw
            have hwabs : |w - β0| = |β0 - w| := abs_sub_comm w β0
            have h1 : w ≥ β0 - ρ := by
              have hw1 : |w - β0| ≤ ρ := hw
              have hbw : β0 - w ≤ ρ := by
                have hb := abs_sub_le_iff.mp (by simpa [abs_sub_comm] using hw1)
                exact hb.1
              linarith
            have h2 : w ≤ β0 + ρ := by
              have hw1 : |w - β0| ≤ ρ := hw
              have hbw : w - β0 ≤ ρ := (abs_sub_le_iff.mp hw1).1
              linarith
            constructor
            · linarith [h1, hρx, hxy.1]
            · linarith [h2, hρy, hxy.2]
          -- root data
          rcases (root_data r hr2 h6r h4r eps N hTmon hTdeg hTsgn hTmag hQ0 hQ1 hQ hEps hN0 hNle)
            with ⟨rho, xx, yy, hIccx, hKx, hfac, hclass, hbracket, hsep⟩
          have hrinj : Function.Injective rho := by
            intro k l hkl
            by_contra hne
            rcases (hsep (k := k) (k' := l) hne) with hylx | hlyx
            · have h1 : rho k < rho l := lt_trans (hIccx k).2.2.1
                (lt_of_le_of_lt hylx (hIccx l).2.1)
              exact (ne_of_lt h1) hkl
            · have h1 : rho l < rho k := lt_trans (hIccx l).2.2.1
                (lt_of_le_of_lt hlyx (hIccx k).2.1)
              exact (ne_of_lt h1) hkl.symm
          intro β hβ w hw
          -- locate β among the roots
          rcases hclass β hβ with ⟨k0, hk0⟩
          let ι : Type := Fin r × Fin D
          -- bracket of k0
          let x0 : ℝ := xx k0
          let y0 : ℝ := yy k0
          have hx0b : x0 < β := by
            dsimp [x0]
            rw [hk0]
            exact (hIccx k0).2.1
          have hβy0 : β < y0 := by
            dsimp [y0]
            rw [hk0]
            exact (hIccx k0).2.2.1
          have hxy : x0 < y0 := lt_trans hx0b hβy0
          have hx0I : x0 ∈ Set.Icc aSerre bSerre := by
            dsimp [x0]
            exact ⟨(hIccx k0).1,
              le_trans (le_of_lt (hIccx k0).2.1)
                (le_trans (le_of_lt (hIccx k0).2.2.1) (hIccx k0).2.2.2)⟩
          have hy0I : y0 ∈ Set.Icc aSerre bSerre := by
            dsimp [y0]
            exact ⟨le_trans (hIccx k0).1
                (le_of_lt (lt_trans (hIccx k0).2.1 (hIccx k0).2.2.1)),
              (hIccx k0).2.2.2⟩
          have hβI : β ∈ Set.Icc aSerre bSerre := by
            rw [hk0]
            exact ⟨le_trans (hIccx k0).1 (le_of_lt (hIccx k0).2.1),
              le_trans (le_of_lt (hIccx k0).2.2.1) (hIccx k0).2.2.2⟩
          -- quotient polynomial Qβ
          let s0 : Finset ι := (Finset.univ : Finset ι).erase k0
          let Qβ : Polynomial ℝ := ∏ k ∈ s0, (X - C (rho k))
          have hQβeval : ∀ v : ℝ, Qβ.eval v = ∏ k ∈ s0, (v - rho k) := by
            intro v
            dsimp [Qβ]
            rw [Polynomial.eval_prod]
            simp
          have hQdec_eval : ∀ v : ℝ, Q.eval v = (v - β) * Qβ.eval v := by
            intro v
            have huniv : (Finset.univ : Finset ι) = insert k0 s0 := by
              dsimp [s0]
              rw [Finset.insert_erase (Finset.mem_univ k0)]
            have hfac' : Q = (∏ k : ι, (X - C (rho k))) := hfac
            have hsplit : (∏ k : ι, (X - C (rho k))) =
                (X - C (rho k0)) * (∏ k ∈ s0, (X - C (rho k))) := by
              rw [show (∏ k : ι, (X - C (rho k))) =
                  ∏ k ∈ (Finset.univ : Finset ι), (X - C (rho k)) by rfl]
              have hne0 : k0 ∉ s0 := by
                dsimp [s0]
                simp
              rw [huniv, Finset.prod_insert hne0]
            calc
              Q.eval v = (∏ k : ι, (X - C (rho k))).eval v := by rw [hfac]
              _ = ((X - C (rho k0)) * (∏ k ∈ s0, (X - C (rho k)))).eval v := by rw [hsplit]
              _ = (v - rho k0) * (∏ k ∈ s0, (X - C (rho k))).eval v := by
                  rw [Polynomial.eval_mul]
                  simp
              _ = (v - β) * Qβ.eval v := by
                  rw [← hk0]
          -- no other root of Qβ in the bracket
          have hQβroot_ne : ∀ k : ι, k ∈ s0 → rho k ≠ rho k0 := by
            intro k hk
            have hne : k ≠ k0 := by
              dsimp [s0] at hk
              exact (Finset.mem_erase.mp hk).1
            intro h
            exact hne (hrinj h)
          have hnot_root : ∀ w : ℝ, w ∈ Set.Icc x0 y0 → ∀ k : ι, k ∈ s0 → w ≠ rho k := by
            intro w hwI k hk hwρ
            have hQβ0 : Qβ.eval w = 0 := by
              rw [hQβeval w, hwρ]
              exact Finset.prod_eq_zero hk (by ring)
            have hQw0 : Q.eval w = 0 := by
              rw [hQdec_eval w, hQβ0]
              ring
            have hwβ : w = β := by
              exact (hbracket k0 w hwI.1 hwI.2 hQw0).trans hk0.symm
            have hρ : rho k = rho k0 := by
              calc
                rho k = w := hwρ.symm
                _ = β := hwβ
                _ = rho k0 := hk0
            exact hQβroot_ne k hk hρ
          -- min at endpoint
          have hminend : ∀ w : ℝ, w ∈ Set.Icc x0 y0 →
              min (|Qβ.eval x0|) (|Qβ.eval y0|) ≤ |Qβ.eval w| := by
            intro w hwI
            -- apply min_abs_prod_endpoint with s := s0 over ι
            have hpp := min_abs_prod_endpoint (s := s0) (ρ := rho) (x := x0) (y := y0) hxy
              (by intro v hvI k hk; exact hnot_root v hvI k hk)
            simpa [Qβ] using (hpp w hwI)
          -- endpoint lower bounds
          have hQx0 : B0 * kappaC ^ (Bclps.Dconst * r) ≤ |Q.eval x0| := by
            have hh := (hKx k0).1
            dsimp [B0]
            simpa [mul_assoc] using hh
          have hQy0 : B0 * kappaC ^ (Bclps.Dconst * r) ≤ |Q.eval y0| := by
            have hh := (hKx k0).2
            dsimp [B0]
            simpa [mul_assoc] using hh
          -- derivative bound (needed for FTC)
          have hderbd0 : ∀ z : ℝ, z ∈ Set.Icc aSerre bSerre →
              |Q.derivative.eval z| ≤ xr ^ N1 * kappaC ^ (Bclps.Dconst * r) := hderbd
          have hLipschitz : ∀ u v : ℝ, u ∈ Set.Icc aSerre bSerre → v ∈ Set.Icc aSerre bSerre →
              |Q.eval u - Q.eval v| ≤ (xr ^ N1 * kappaC ^ (Bclps.Dconst * r)) * |u - v| := by
            intro u v hu hv
            exact AdjustedCheb.poly_lipschitz (P := Q) (x := u) (y := v)
              (C := xr ^ N1 * kappaC ^ (Bclps.Dconst * r)) hu hv hderbd0
          have hFTCx : (β - x0) * xr ^ N1 ≥ B0 := by
            have hlp := hLipschitz β x0 hβI hx0I
            have hQβ0 : Q.eval β = 0 := hβ
            have hmain : |Q.eval x0| ≤ (xr ^ N1 * kappaC ^ (Bclps.Dconst * r)) * (β - x0) := by
              have hlp' : |Q.eval β - Q.eval x0| ≤
                  (xr ^ N1 * kappaC ^ (Bclps.Dconst * r)) * |β - x0| := hlp
              have habs : |β - x0| = β - x0 := by
                rw [abs_of_pos (sub_pos.mpr hx0b)]
              have hrew : |Q.eval β - Q.eval x0| = |Q.eval x0| := by
                rw [hQβ0]
                simp
              calc
                |Q.eval x0| = |Q.eval β - Q.eval x0| := hrew.symm
                _ ≤ (xr ^ N1 * kappaC ^ (Bclps.Dconst * r)) * |β - x0| := hlp'
                _ = (xr ^ N1 * kappaC ^ (Bclps.Dconst * r)) * (β - x0) := by rw [habs]
            have hbig' : B0 * kappaC ^ (Bclps.Dconst * r) ≤
                (xr ^ N1 * kappaC ^ (Bclps.Dconst * r)) * (β - x0) :=
              le_trans hQx0 hmain
            have hκ : 0 < kappaC ^ (Bclps.Dconst * r) := hkappa_posn (Bclps.Dconst * r)
            have hrew : (xr ^ N1 * kappaC ^ (Bclps.Dconst * r)) * (β - x0) =
                (xr ^ N1 * (β - x0)) * kappaC ^ (Bclps.Dconst * r) := by ring
            have hbig'' : B0 * kappaC ^ (Bclps.Dconst * r) ≤
                (xr ^ N1 * (β - x0)) * kappaC ^ (Bclps.Dconst * r) := by
              rw [← hrew]
              exact hbig'
            have hF : B0 ≤ xr ^ N1 * (β - x0) :=
              (mul_le_mul_iff_of_pos_right hκ).1 hbig''
            rwa [mul_comm (xr ^ N1) (β - x0)] at hF
          have hFTCy : (y0 - β) * xr ^ N1 ≥ B0 := by
            have hlp := hLipschitz y0 β hy0I hβI
            have hQβ0 : Q.eval β = 0 := hβ
            have hmain : |Q.eval y0| ≤ (xr ^ N1 * kappaC ^ (Bclps.Dconst * r)) * (y0 - β) := by
              have hlp' : |Q.eval y0 - Q.eval β| ≤
                  (xr ^ N1 * kappaC ^ (Bclps.Dconst * r)) * |y0 - β| := hlp
              have habs : |y0 - β| = y0 - β := by
                rw [abs_of_pos (sub_pos.mpr hβy0)]
              have hrew : |Q.eval y0 - Q.eval β| = |Q.eval y0| := by
                rw [hQβ0]
                simp
              calc
                |Q.eval y0| = |Q.eval y0 - Q.eval β| := hrew.symm
                _ ≤ (xr ^ N1 * kappaC ^ (Bclps.Dconst * r)) * |y0 - β| := hlp'
                _ = (xr ^ N1 * kappaC ^ (Bclps.Dconst * r)) * (y0 - β) := by rw [habs]
            have hbig' : B0 * kappaC ^ (Bclps.Dconst * r) ≤
                (xr ^ N1 * kappaC ^ (Bclps.Dconst * r)) * (y0 - β) :=
              le_trans hQy0 hmain
            have hκ : 0 < kappaC ^ (Bclps.Dconst * r) := hkappa_posn (Bclps.Dconst * r)
            have hrew : (xr ^ N1 * kappaC ^ (Bclps.Dconst * r)) * (y0 - β) =
                (xr ^ N1 * (y0 - β)) * kappaC ^ (Bclps.Dconst * r) := by ring
            have hbig'' : B0 * kappaC ^ (Bclps.Dconst * r) ≤
                (xr ^ N1 * (y0 - β)) * kappaC ^ (Bclps.Dconst * r) := by
              rw [← hrew]
              exact hbig'
            have hF : B0 ≤ xr ^ N1 * (y0 - β) :=
              (mul_le_mul_iff_of_pos_right hκ).1 hbig''
            rwa [mul_comm (xr ^ N1) (y0 - β)] at hF
          -- distance from β to the bracket endpoints ≥ ρ
          have hρx : ρ ≤ β - x0 := by
            apply hρ_le
            have hb := hFTCx
            have hpowadd : xr ^ CN = xr ^ N1 * xr ^ (CN - N1) := by
              rw [← pow_add]
              congr 1
              omega
            have hge0 : 0 ≤ xr ^ (CN - N1) := pow_nonneg hxr0 (CN - N1)
            have h1 : B0 * xr ^ (CN - N1) ≤ ((β - x0) * xr ^ N1) * xr ^ (CN - N1) :=
              mul_le_mul_of_nonneg_right hb hge0
            have hstep : 1 ≤ B0 * xr ^ (CN - N1) := by
              have hB0x : B0 * xr ≤ B0 * xr ^ (CN - N1) := by
                exact mul_le_mul_of_nonneg_left hxp hB0ge
              have hbig2 : (1 : ℝ) ≤ B0 * xr := by
                have h1' : B0 * (C2val * (bSerre - aSerre)) ≤ B0 * xr := by
                  exact mul_le_mul_of_nonneg_left hbig hB0ge
                have h2' : (1 : ℝ) ≤ B0 * (C2val * (bSerre - aSerre)) := by
                  have hc : B0 * (C2val * (bSerre - aSerre)) = 2 * (bSerre - aSerre) := by
                    dsimp [B0]
                    calc
                      (2 * C2val⁻¹) * (C2val * (bSerre - aSerre))
                          = ((2 * C2val⁻¹) * C2val) * (bSerre - aSerre) := by ring
                      _ = 2 * (bSerre - aSerre) := by
                          congr 1
                          field_simp [ne_of_gt hC2pos]
                  rw [hc]
                  nlinarith [hL04]
                exact le_trans h2' h1'
              exact le_trans hbig2 hB0x
            have hgoal : 1 ≤ ((β - x0) * xr ^ N1) * xr ^ (CN - N1) := le_trans hstep h1
            rw [hpowadd]
            rw [← mul_assoc]
            exact hgoal
          have hρy : ρ ≤ y0 - β := by
            apply hρ_le
            have hb := hFTCy
            have hpowadd : xr ^ CN = xr ^ N1 * xr ^ (CN - N1) := by
              rw [← pow_add]
              congr 1
              omega
            have hge0 : 0 ≤ xr ^ (CN - N1) := pow_nonneg hxr0 (CN - N1)
            have h1 : B0 * xr ^ (CN - N1) ≤ ((y0 - β) * xr ^ N1) * xr ^ (CN - N1) :=
              mul_le_mul_of_nonneg_right hb hge0
            have hstep : 1 ≤ B0 * xr ^ (CN - N1) := by
              have hB0x : B0 * xr ≤ B0 * xr ^ (CN - N1) := by
                exact mul_le_mul_of_nonneg_left hxp hB0ge
              have hbig2 : (1 : ℝ) ≤ B0 * xr := by
                have h1' : B0 * (C2val * (bSerre - aSerre)) ≤ B0 * xr := by
                  exact mul_le_mul_of_nonneg_left hbig hB0ge
                have h2' : (1 : ℝ) ≤ B0 * (C2val * (bSerre - aSerre)) := by
                  have hc : B0 * (C2val * (bSerre - aSerre)) = 2 * (bSerre - aSerre) := by
                    dsimp [B0]
                    calc
                      (2 * C2val⁻¹) * (C2val * (bSerre - aSerre))
                          = ((2 * C2val⁻¹) * C2val) * (bSerre - aSerre) := by ring
                      _ = 2 * (bSerre - aSerre) := by
                          congr 1
                          field_simp [ne_of_gt hC2pos]
                  rw [hc]
                  nlinarith [hL04]
                exact le_trans h2' h1'
              exact le_trans hbig2 hB0x
            have hgoal : 1 ≤ ((y0 - β) * xr ^ N1) * xr ^ (CN - N1) := le_trans hstep h1
            rw [hpowadd]
            rw [← mul_assoc]
            exact hgoal
          -- endpoint lower bounds of Qβ (values of Q divided by distance ≤ L0)
          have hQβx0b : (B0 * kappaC ^ (Bclps.Dconst * r)) / (bSerre - aSerre) ≤ |Qβ.eval x0| := by
            have hdec := hQdec_eval x0
            have habs : |Q.eval x0| = |x0 - β| * |Qβ.eval x0| := by
              rw [hdec, abs_mul]
            have h1 : B0 * kappaC ^ (Bclps.Dconst * r) ≤ |x0 - β| * |Qβ.eval x0| := by
              rw [← habs]
              exact hQx0
            have hpos : 0 < |x0 - β| := abs_pos.mpr (sub_ne_zero.mpr (ne_of_lt hx0b))
            have h2 : (B0 * kappaC ^ (Bclps.Dconst * r)) / |x0 - β| ≤ |Qβ.eval x0| := by
              exact (div_le_iff₀ hpos).mpr (by simpa [mul_comm] using h1)
            have hbL : |x0 - β| ≤ bSerre - aSerre := abs_sub_le_of_mem_Icc hx0I hβI
            have hA0 : 0 ≤ B0 * kappaC ^ (Bclps.Dconst * r) :=
              mul_nonneg hB0ge (hkappa_nonneg (Bclps.Dconst * r))
            have hLe : (B0 * kappaC ^ (Bclps.Dconst * r)) / (bSerre - aSerre) ≤
                (B0 * kappaC ^ (Bclps.Dconst * r)) / |x0 - β| := by
              exact div_le_div_of_nonneg_left hA0 hpos hbL
            exact le_trans hLe h2
          have hQβy0b : (B0 * kappaC ^ (Bclps.Dconst * r)) / (bSerre - aSerre) ≤ |Qβ.eval y0| := by
            have hdec := hQdec_eval y0
            have habs : |Q.eval y0| = |y0 - β| * |Qβ.eval y0| := by
              rw [hdec, abs_mul]
            have h1 : B0 * kappaC ^ (Bclps.Dconst * r) ≤ |y0 - β| * |Qβ.eval y0| := by
              rw [← habs]
              exact hQy0
            have hpos : 0 < |y0 - β| := abs_pos.mpr (sub_ne_zero.mpr (ne_of_gt hβy0))
            have h2 : (B0 * kappaC ^ (Bclps.Dconst * r)) / |y0 - β| ≤ |Qβ.eval y0| := by
              exact (div_le_iff₀ hpos).mpr (by simpa [mul_comm] using h1)
            have hbL : |y0 - β| ≤ bSerre - aSerre := abs_sub_le_of_mem_Icc hy0I hβI
            have hA0 : 0 ≤ B0 * kappaC ^ (Bclps.Dconst * r) :=
              mul_nonneg hB0ge (hkappa_nonneg (Bclps.Dconst * r))
            have hLe : (B0 * kappaC ^ (Bclps.Dconst * r)) / (bSerre - aSerre) ≤
                (B0 * kappaC ^ (Bclps.Dconst * r)) / |y0 - β| := by
              exact div_le_div_of_nonneg_left hA0 hpos hbL
            exact le_trans hLe h2
          -- ρ is also ≤ B0/L0 (so that ρ·κ^{Dr} ≤ the endpoint lower bound)
          have hρ0 : ρ ≤ B0 / (bSerre - aSerre) := by
            apply hρ_le
            have hxrCN1 : xr ≤ xr ^ CN := by
              have hb : xr ≤ xr ^ 1 := by rw [pow_one]
              exact le_trans hb (pow_le_pow_right₀ hxr1 hCN1)
            have hB0C2 : (1 : ℝ) ≤ B0 * C2val := by
              have hc : B0 * C2val = 2 := by
                dsimp [B0]
                field_simp [ne_of_gt hC2pos]
              rw [hc]
              norm_num
            have h2 : C2val * (bSerre - aSerre) ≤ xr ^ CN := le_trans hbig hxrCN1
            have h1' : B0 * (C2val * (bSerre - aSerre)) ≤ B0 * xr ^ CN :=
              mul_le_mul_of_nonneg_left h2 hB0ge
            have h4 : B0 * C2val * (bSerre - aSerre) ≤ B0 * xr ^ CN := by
              simpa [← mul_assoc] using h1'
            have h3 : (bSerre - aSerre) ≤ B0 * C2val * (bSerre - aSerre) := by
              simpa using (mul_le_mul_of_nonneg_right hB0C2 (le_of_lt hL0))
            have hxbigCN : (bSerre - aSerre) ≤ B0 * xr ^ CN := le_trans h3 h4
            -- goal 1 ≤ (B0/(b−a))·xr^{CN}  ⟺  (b−a) ≤ B0·xr^{CN}
            have hg : 1 ≤ (B0 / (bSerre - aSerre)) * xr ^ CN := by
              rw [div_mul_eq_mul_div]
              exact (le_div_iff₀ hL0).mpr (by simpa using hxbigCN)
            exact hg
          -- w lies in the bracket
          have hwIcc : w ∈ Set.Icc x0 y0 := hx0y0_w β x0 y0 ⟨hx0b, hβy0⟩ hρx hρy w hw
          -- min-at-endpoint value at w
          have hminw : min (|Qβ.eval x0|) (|Qβ.eval y0|) ≤ |Qβ.eval w| := hminend w hwIcc
          have hboundβ : (B0 * kappaC ^ (Bclps.Dconst * r)) / (bSerre - aSerre) ≤ |Qβ.eval w| := by
            have hmn : (B0 * kappaC ^ (Bclps.Dconst * r)) / (bSerre - aSerre) ≤
                min (|Qβ.eval x0|) (|Qβ.eval y0|) := by
              exact le_min hQβx0b hQβy0b
            exact le_trans hmn hminw
          have hρρ : ρ * kappaC ^ (Bclps.Dconst * r) ≤
              (B0 * kappaC ^ (Bclps.Dconst * r)) / (bSerre - aSerre) := by
            have hm := mul_le_mul_of_nonneg_right hρ0 (hkappa_nonneg (Bclps.Dconst * r))
            have hrew : (B0 / (bSerre - aSerre)) * kappaC ^ (Bclps.Dconst * r) =
                (B0 * kappaC ^ (Bclps.Dconst * r)) / (bSerre - aSerre) := by
              rw [div_mul_eq_mul_div]
            rwa [hrew] at hm
          have hδ0 : 0 ≤ |w - β| := abs_nonneg _
          have habsw : |Q.eval w| = |w - β| * |Qβ.eval w| := by
            rw [hQdec_eval w, abs_mul]
          have hm1 : ρ * kappaC ^ (Bclps.Dconst * r) ≤ |Qβ.eval w| :=
            le_trans hρρ hboundβ
          have hfin : |w - β| * (ρ * kappaC ^ (Bclps.Dconst * r)) ≤ |Q.eval w| := by
            rw [habsw]
            exact mul_le_mul_of_nonneg_left hm1 hδ0
          have hfin' : ρ * kappaC ^ (Bclps.Dconst * r) * |w - β| ≤ |Q.eval w| := by
            simpa [mul_assoc, mul_comm, mul_left_comm] using hfin
          simpa [ρ] using hfin'

        -- assemble; express xr as ((r:ℝ)+3)
        have hc1fin : DivLinear.supNorm Q ≤ (((r : ℝ) + 3) ^ (CN : ℝ)) *
            kappaC ^ (Bclps.Dconst * r) := by
          simpa [xr] using hsupQr
        have hc2fin : DivLinear.supNorm Q.derivative ≤ (((r : ℝ) + 3) ^ (CN : ℝ)) *
            kappaC ^ (Bclps.Dconst * r) := by
          simpa [xr] using hsupQdr
        have hc3fin : ∀ β : ℝ, Q.eval β = 0 → ∀ w : ℝ, |w - β| ≤ ((r : ℝ) + 3) ^ (-(CN : ℝ)) →
            |Q.eval w| ≥ ((r : ℝ) + 3) ^ (-(CN : ℝ)) *
              kappaC ^ (Bclps.Dconst * r) * |w - β| := by
          intro β hβ w hw
          have hh := hlocal β hβ w hw
          simpa [xr] using hh
        exact ⟨hc1fin, hc2fin, hc3fin⟩

end Submission.CompQRoots2
