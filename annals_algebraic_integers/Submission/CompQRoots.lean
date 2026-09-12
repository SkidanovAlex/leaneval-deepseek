import Submission.AdjustedCheb
import Submission.Bclps
import Submission.ChebSerre
import Submission.DivLinear
import Submission.CompQNums
import Submission.ChainLevels
import Submission.ChainDown
import Submission.CompQpert
import Submission.CompQdeg
import Submission.CompQlevels
import Submission.CompQlevelsPair
import Submission.CompQlevelsPow
import Submission.CompQauxSum
import Mathlib.Analysis.CStarAlgebra.Classes

/-!
# Root location of the complementary polynomial (Smith's `lem:comp_Q_roots`)

adjust.tex, Lemma `lem:comp_Q_roots`, single interval.  Given the construction
data of `defn:comp_Q` (a polynomial `T` from `lem:Bclps` with alternating sign
`±`, `|T| ≥ κ^r/64` at the bracket points and hence `≥ D·levelStep r` on the
positive side of each bracket gap; `Q0 = ∏_{j'<D}(T − c_{j'})`; and a
perturbation `Q − Q0 = Σ_t ε_t·auxPoly t + N` with `ε_t ∈ [0,2)`,
`0 ≤ N ≤ 2·C2val⁻¹·κ^{Dr}`), for all sufficiently large `r`:

* every complex root of `Q` lies in the OPEN Serre interval `(aSerre, bSerre)`
  (so all roots are real);
* `Q` splits as a product over `Dr` strictly increasing roots in the interval;
* around each root `β` there is a bracket `[x,y] ⊆ [aSerre,bSerre]` with
  `x < β < y`, `|Q(x)|, |Q(y)| ≥ C⁻¹·κ^{Dr}`, and no other root of `Q` in
  `[x,y]`.

## Proof sketch (as in the paper)

The sign of `T̃ = prunedPoly r` at `bracketPoint r i` alternates with `i`
(`(−1)^i`), and `T` shares its sign and has `|T| ≥ κ^r/64 = D·levelStep r`
there; hence in every bracket gap `(bracketPoint r (i+1), bracketPoint r i)`
`T` changes sign.  Choose `v_0` in the gap with `T(v_0) = 0`, then recursively
`v_{j+1} ∈ (v_j, y⁺]` with `T(v_{j+1}) = (j+1)·levelStep r` (IVT; `y⁺` is the
positive end of the gap).  Then `T(v_j) = j·levelStep r`, so
`sign(Q0(v_j)) = (−1)^{D−j}` and
`|Q0(v_j)| ≥ (levelStep r/2)^D = κ^{Dr}/(128D)^D = 8·C2val⁻¹·κ^{Dr}`.
The perturbation bound (pointwise on the interval)
`|Q − Q0| ≤ Σ_{t=1}^{d} |ε_t|·|auxPoly t| + N ≤ κ^{Dr}·(4·κ^{1−r}/(κ−1) + 2·C2val⁻¹)`
together with `CompQNums.large_r` gives, for `r ≥ C`, `|Q − Q0| < 8·C2val⁻¹·κ^{Dr}`,
so `Q` has the same sign as `Q0` at every `v_j`.  Consequently `Q` changes sign
across each of the `r·D` disjoint intervals `(v_{i,j}, v_{i,j+1})`, hence has
at least `Dr` distinct real roots there; since `deg Q = Dr`, exactly one root
per interval, no other roots, and every root is simple and lies in the open
interval.
-/

noncomputable section


open scoped Real BigOperators
open ComplexOrder
open Polynomial

namespace Submission.CompQRoots

open Submission.SerreExample
open Submission.ChebSerre
open Submission.AdjustedCheb
open Submission.Bclps
open Submission.DivLinear
open Submission.CompQNums

/-- the auxiliary-degree `d = (D−1)·r`. -/
def d (r : ℕ) : ℕ := (Bclps.Dconst - 1) * r



/-! ## Bracket-point position and sign helpers -/

/-- every bracket point lies left of the dropped root `ρ0`. -/
lemma bracketPoint_lt_root_zero (r : ℕ) (i : Fin (r + 1)) :
    bracketPoint r i < rootPoint (r + 3) 0 := by
  have hN : 1 ≤ r + 3 := by omega
  have h1 : bracketPoint r i ≤ extPoint (r + 3) 1 := by
    unfold bracketPoint
    by_cases h0 : i.val = 0
    · have hi : i.val + 1 = 1 := by omega
      rw [hi]
    · have hlt : 1 < i.val + 1 := by omega
      exact le_of_lt (extPoint_antitone (N := r + 3) hN (j := i.val + 1) (i := 1) (by omega) hlt)
  have h2 : extPoint (r + 3) 1 < rootPoint (r + 3) 0 :=
    (extPoint_rootPoint_interleave (N := r + 3) (k := 0) hN (by omega)).1
  exact lt_of_le_of_lt h1 h2

/-- every bracket point lies right of the dropped root `ρ_{r+1}`. -/
lemma root_rp1_lt_bracketPoint (r : ℕ) (i : Fin (r + 1)) :
    rootPoint (r + 3) (r + 1) < bracketPoint r i := by
  have hN : 1 ≤ r + 3 := by omega
  have h1 : rootPoint (r + 3) (r + 1) < extPoint (r + 3) (r + 1) :=
    (extPoint_rootPoint_interleave (N := r + 3) (k := r + 1) hN (by omega)).2
  have h2 : extPoint (r + 3) (r + 1) ≤ bracketPoint r i := by
    unfold bracketPoint
    by_cases h0 : i.val = r
    · have hi : i.val + 1 = r + 1 := by omega
      rw [hi]
    · have hlt : i.val + 1 < r + 1 := by omega
      exact le_of_lt (extPoint_antitone (N := r + 3) hN (j := r + 1) (i := i.val + 1) (by omega) hlt)
  calc
    rootPoint (r + 3) (r + 1) < extPoint (r + 3) (r + 1) := h1
    _ ≤ bracketPoint r i := h2

/-- every bracket point lies right of the dropped root `ρ_{r+2}`. -/
lemma root_rp2_lt_bracketPoint (r : ℕ) (i : Fin (r + 1)) :
    rootPoint (r + 3) (r + 2) < bracketPoint r i := by
  have hN : 1 ≤ r + 3 := by omega
  have h1 : rootPoint (r + 3) (r + 2) < extPoint (r + 3) (r + 2) :=
    (extPoint_rootPoint_interleave (N := r + 3) (k := r + 2) hN (by omega)).2
  have h2 : extPoint (r + 3) (r + 2) ≤ bracketPoint r i := by
    unfold bracketPoint
    by_cases h0 : i.val = r - 1
    · have hi : i.val + 1 = r + 2 → i.val + 1 = r + 2 := by intro h; exact h
      -- i+1 = r+1 < r+2 or i+1 = r+2
      have hle : i.val + 1 ≤ r + 1 := by omega
      -- here i.val = r-1 so i.val + 1 = r; extPoint(r+2) ≤ extPoint(r+1)?
      -- we need extPoint (r+3)(r+2) ≤ extPoint (r+3)(i.val+1) = extPoint(r+3) r
      have hgt : i.val + 1 < r + 2 := by omega
      exact le_of_lt (extPoint_antitone (N := r + 3) hN (j := r + 2) (i := i.val + 1) (by omega) hgt)
    · have hlt2 : i.val + 1 ≠ r + 2 := by omega
      have hlt : i.val + 1 < r + 2 := by omega
      exact le_of_lt (extPoint_antitone (N := r + 3) hN (j := r + 2) (i := i.val + 1) (by omega) hlt)
  calc
    rootPoint (r + 3) (r + 2) < extPoint (r + 3) (r + 2) := h1
    _ ≤ bracketPoint r i := h2

/-- `droppedCubic` is strictly negative at every bracket point. -/
lemma cubic_bracket_neg (r : ℕ) (i : Fin (r + 1)) :
    (droppedCubic r).eval (bracketPoint r i) < 0 := by
  unfold droppedCubic
  simp
  have ha : bracketPoint r i - rootPoint (r + 3) 0 < 0 :=
    sub_neg.mpr (bracketPoint_lt_root_zero r i)
  have hb : 0 < bracketPoint r i - rootPoint (r + 3) (r + 1) :=
    sub_pos.mpr (root_rp1_lt_bracketPoint r i)
  have hc : 0 < bracketPoint r i - rootPoint (r + 3) (r + 2) :=
    sub_pos.mpr (root_rp2_lt_bracketPoint r i)
  exact mul_neg_of_neg_of_pos ha (mul_pos hb hc)

/-- sign of the pruned polynomial at the brackets: `pruned(b_i) = sign (−1)^i`,
i.e. `pruned(b_i)·(−1)^i > 0`. -/
lemma pruned_bracket_sign (r : ℕ) (hr : 2 ≤ r) (i : Fin (r + 1)) :
    0 < (prunedPoly r).eval (bracketPoint r i) * (-1 : ℝ) ^ (i.val) := by
  have hN : 1 ≤ r + 3 := by omega
  have hcb : (chebT (r + 3)).eval (bracketPoint r i) =
      2 * kappaC ^ (r + 3) * (-1 : ℝ) ^ (i.val + 1) := by
    dsimp [bracketPoint]
    exact chebT_eval_extPoint (r + 3) (i.val + 1) hN (by omega)
  have hfac : chebT (r + 3) = droppedCubic r * prunedPoly r :=
    chebT_eq_dropped_mul_pruned r hr
  have hcb'' : ((droppedCubic r).eval (bracketPoint r i)) *
        ((prunedPoly r).eval (bracketPoint r i)) * (-1 : ℝ) ^ (i.val + 1) =
      2 * kappaC ^ (r + 3) := by
    calc
      ((droppedCubic r).eval (bracketPoint r i)) * ((prunedPoly r).eval (bracketPoint r i))
          * (-1 : ℝ) ^ (i.val + 1)
          = ((droppedCubic r * prunedPoly r).eval (bracketPoint r i)) * (-1 : ℝ) ^ (i.val + 1) := by
              rw [← Polynomial.eval_mul]
      _ = (chebT (r + 3)).eval (bracketPoint r i) * (-1 : ℝ) ^ (i.val + 1) := by rw [hfac]
      _ = (2 * kappaC ^ (r + 3) * (-1 : ℝ) ^ (i.val + 1)) * (-1 : ℝ) ^ (i.val + 1) := by rw [hcb]
      _ = 2 * kappaC ^ (r + 3) := by
          have hpow : (-1 : ℝ) ^ (i.val + 1) * (-1 : ℝ) ^ (i.val + 1) = 1 := by
            calc (-1 : ℝ) ^ (i.val + 1) * (-1 : ℝ) ^ (i.val + 1)
                = ((-1 : ℝ) ^ (i.val + 1)) ^ 2 := by rw [pow_two]
            _ = (-1 : ℝ) ^ ((i.val + 1) * 2) := by rw [← pow_mul]
            _ = (-1 : ℝ) ^ (2 * (i.val + 1)) := by rw [mul_comm]
            _ = ((-1 : ℝ) ^ 2) ^ (i.val + 1) := by rw [pow_mul]
            _ = 1 := by norm_num
          rw [mul_assoc]
          rw [hpow]
          ring
  have hmain : (prunedPoly r).eval (bracketPoint r i) * (-1 : ℝ) ^ (i.val + 1) < 0 := by
    have hcneg : (droppedCubic r).eval (bracketPoint r i) < 0 := cubic_bracket_neg r i
    have hpos : 0 < (droppedCubic r).eval (bracketPoint r i) *
        ((prunedPoly r).eval (bracketPoint r i) * (-1 : ℝ) ^ (i.val + 1)) := by
      have hk : 0 < kappaC ^ (r + 3) := pow_pos (AdjustedCheb.kappaC_pos) _
      calc
        0 < 2 * kappaC ^ (r + 3) := by nlinarith
        _ = (droppedCubic r).eval (bracketPoint r i) * (prunedPoly r).eval (bracketPoint r i)
            * (-1 : ℝ) ^ (i.val + 1) := hcb''.symm
        _ = (droppedCubic r).eval (bracketPoint r i) *
            ((prunedPoly r).eval (bracketPoint r i) * (-1 : ℝ) ^ (i.val + 1)) := by ring
    rcases (mul_pos_iff.mp hpos) with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have : (0 : ℝ) < (droppedCubic r).eval (bracketPoint r i) := h1
      linarith
    · exact h2
  have hflip : (prunedPoly r).eval (bracketPoint r i) * (-1 : ℝ) ^ (i.val + 1) =
      - ((prunedPoly r).eval (bracketPoint r i) * (-1 : ℝ) ^ (i.val)) := by
    rw [pow_succ]
    ring
  rw [hflip] at hmain
  linarith

/-- the pruned polynomial is nonzero at bracket points. -/
lemma pruned_bracket_ne_zero (r : ℕ) (hr : 2 ≤ r) (i : Fin (r + 1)) :
    (prunedPoly r).eval (bracketPoint r i) ≠ 0 := by
  intro hp
  have h := pruned_bracket_sign r hr i
  rw [hp] at h
  linarith

/-! ## Sign and magnitude of `T` at the bracket points -/

/-- `0 < pruned(b)·(−1)^i` and the bracket sign hypothesis force the signed
value `(−1)^i·T(b_i)` to be positive. -/
lemma T_bracket_sign (r : ℕ) (hr : 2 ≤ r) {T : Polynomial ℝ}
    (hTsgn : ∀ i : Fin (r + 1),
      0 < T.eval (bracketPoint r i) * (prunedPoly r).eval (bracketPoint r i))
    (i : Fin (r + 1)) : 0 < (-1 : ℝ) ^ (i.val) * T.eval (bracketPoint r i) := by
  have hp1 : 0 < T.eval (bracketPoint r i) * (prunedPoly r).eval (bracketPoint r i) := hTsgn i
  have hp2 : 0 < (prunedPoly r).eval (bracketPoint r i) * (-1 : ℝ) ^ (i.val) :=
    pruned_bracket_sign r hr i
  have hprod : 0 < (T.eval (bracketPoint r i) * (prunedPoly r).eval (bracketPoint r i)) *
      ((prunedPoly r).eval (bracketPoint r i) * (-1 : ℝ) ^ (i.val)) := mul_pos hp1 hp2
  have hpne : (prunedPoly r).eval (bracketPoint r i) ≠ 0 := pruned_bracket_ne_zero r hr i
  have hrew : (T.eval (bracketPoint r i) * (prunedPoly r).eval (bracketPoint r i)) *
        ((prunedPoly r).eval (bracketPoint r i) * (-1 : ℝ) ^ (i.val)) =
      (T.eval (bracketPoint r i) * (-1 : ℝ) ^ (i.val)) *
        ((prunedPoly r).eval (bracketPoint r i)) ^ 2 := by ring
  have hmain : 0 < (T.eval (bracketPoint r i) * (-1 : ℝ) ^ (i.val)) *
      ((prunedPoly r).eval (bracketPoint r i)) ^ 2 := by
    rwa [hrew] at hprod
  rcases mul_pos_iff.mp hmain with ⟨hT, hsq⟩ | ⟨hT, hsq⟩
  · have : 0 < (-1 : ℝ) ^ (i.val) * T.eval (bracketPoint r i) := by
      simpa [mul_comm] using hT
    exact this
  · have hsqn : ¬ ((prunedPoly r).eval (bracketPoint r i)) ^ 2 < 0 := by
      nlinarith [sq_nonneg ((prunedPoly r).eval (bracketPoint r i))]
    contradiction

/-- the magnitude hypothesis at a bracket point gives the signed bound
`(−1)^i·T(b_i) ≥ D·levelStep r = κ^r/64`. -/
lemma bracket_T_signed_mag (r : ℕ) (hr : 2 ≤ r) {T : Polynomial ℝ}
    (hTsgn : ∀ i : Fin (r + 1),
      0 < T.eval (bracketPoint r i) * (prunedPoly r).eval (bracketPoint r i))
    (hTmag : ∀ i : Fin (r + 1), |T.eval (bracketPoint r i)| ≥ kappaC ^ r / 64)
    (i : Fin (r + 1)) : (D : ℝ) * levelStep r ≤ (-1 : ℝ) ^ (i.val) * T.eval (bracketPoint r i) := by
  have hs : 0 < (-1 : ℝ) ^ (i.val) * T.eval (bracketPoint r i) := T_bracket_sign r hr hTsgn i
  have hm : |T.eval (bracketPoint r i)| ≥ kappaC ^ r / 64 := hTmag i
  have hmag : (D : ℝ) * levelStep r ≤ |T.eval (bracketPoint r i)| := by
    rw [← level_top r] at hm
    exact hm
  have habs : |(-1 : ℝ) ^ (i.val) * T.eval (bracketPoint r i)| = |T.eval (bracketPoint r i)| := by
    rw [abs_mul]
    have hnegabs : |(-1 : ℝ) ^ (i.val)| = 1 := by
      rcases (neg_one_pow_eq_or ℝ (i.val)) with h | h
      · rw [h]; norm_num
      · rw [h]; norm_num
    rw [hnegabs, one_mul]
  calc
    (D : ℝ) * levelStep r ≤ |T.eval (bracketPoint r i)| := hmag
    _ = |(-1 : ℝ) ^ (i.val) * T.eval (bracketPoint r i)| := habs.symm
    _ = (-1 : ℝ) ^ (i.val) * T.eval (bracketPoint r i) := abs_of_pos hs

/-- a "large r" inequality with the constant `4` (stronger decay than `large_r`
with `6`): `4/((κ−1)·κ^{r−1}) < 4/C2val` eventually. -/
lemma large_r4 : ∃ C : ℕ, ∀ r : ℕ, C ≤ r →
    (4 : ℝ) / ((kappaC - 1) * kappaC ^ (r - 1)) < 4 / C2val := by
  have hk1 : (1 : ℝ) < kappaC := kappaC_gt_one
  have hkpos : 0 < kappaC - 1 := by linarith
  have hc2pos : 0 < C2val := C2val_pos
  have hunb := pow_unbounded_of_one_lt (C2val / (kappaC - 1)) hk1
  rcases hunb with ⟨N, hN⟩
  refine ⟨N + 1, ?_⟩
  intro r hr
  have hmono : kappaC ^ N ≤ kappaC ^ (r - 1) := by
    apply pow_le_pow_right₀ (le_of_lt hk1)
    omega
  have hbound : C2val / (kappaC - 1) < kappaC ^ (r - 1) := lt_of_lt_of_le hN hmono
  have hmain : (4 : ℝ) < (4 / C2val) * ((kappaC - 1) * kappaC ^ (r - 1)) := by
    have h1 : C2val < (kappaC - 1) * kappaC ^ (r - 1) := by
      have h1' : C2val < kappaC ^ (r - 1) * (kappaC - 1) := (div_lt_iff₀ hkpos).mp hbound
      simpa [mul_comm, mul_left_comm, mul_assoc] using h1'
    have h2 : 4 * C2val < 4 * ((kappaC - 1) * kappaC ^ (r - 1)) := by
      exact mul_lt_mul_of_pos_left h1 (by norm_num)
    calc
      (4 : ℝ) < (4 * ((kappaC - 1) * kappaC ^ (r - 1))) / C2val := (lt_div_iff₀ hc2pos).mpr h2
      _ = (4 / C2val) * ((kappaC - 1) * kappaC ^ (r - 1)) := by ring
  exact (div_lt_iff₀ (mul_pos hkpos (pow_pos (lt_trans zero_lt_one hk1) (r - 1)))).mpr hmain



/-! ## Order helpers for the bracket construction -/

/-- a natural-indexed sequence that strictly increases at every step below `N`
is monotone on `0..N`. -/
lemma seq_mono {N : ℕ} {seq : ℕ → ℝ}
    (h : ∀ n : ℕ, n < N → seq n < seq (n + 1)) :
    ∀ m n : ℕ, m ≤ n → n ≤ N → seq m ≤ seq n := by
  intro m n hmn hnN
  induction n generalizing m with
  | zero =>
      have hm : m = 0 := by omega
      rw [hm]
  | succ n ih =>
      by_cases hmn' : m ≤ n
      · have hnn : n < N := by omega
        exact le_trans (ih m hmn' (by omega)) (le_of_lt (h n hnn))
      · have hm : m = n + 1 := by omega
        rw [hm]

/-- a chain strictly increasing between consecutive entries is monotone. -/
lemma chain_mono {N : ℕ} {s : Fin (N + 1) → ℝ}
    (h : ∀ j : Fin N, s ⟨j.val, by omega⟩ < s ⟨j.val + 1, by omega⟩) :
    ∀ j1 j2 : Fin (N + 1), j1.val ≤ j2.val → s j1 ≤ s j2 := by
  let seq : ℕ → ℝ := fun n => s ⟨min n N, by omega⟩
  have hseq : ∀ n : ℕ, n < N → seq n < seq (n + 1) := by
    intro n hn
    have h1 : (⟨min n N, by omega⟩ : Fin (N + 1)) = ⟨n, by omega⟩ := by
      apply Fin.ext
      exact min_eq_left (by omega : n ≤ N)
    have h2 : (⟨min (n + 1) N, by omega⟩ : Fin (N + 1)) = ⟨n + 1, by omega⟩ := by
      apply Fin.ext
      exact min_eq_left (by omega : n + 1 ≤ N)
    dsimp [seq]
    calc
      s ⟨min n N, by omega⟩ = s ⟨n, by omega⟩ := congrArg s h1
      _ < s ⟨n + 1, by omega⟩ := h ⟨n, by omega⟩
      _ = s ⟨min (n + 1) N, by omega⟩ := (congrArg s h2).symm
  intro j1 j2 hj
  have hmon := seq_mono hseq j1.val j2.val hj (by omega : j2.val ≤ N)
  have h1 : (⟨min j1.val N, by omega⟩ : Fin (N + 1)) = j1 := by
    apply Fin.ext
    exact min_eq_left (by omega : j1.val ≤ N)
  have h2 : (⟨min j2.val N, by omega⟩ : Fin (N + 1)) = j2 := by
    apply Fin.ext
    exact min_eq_left (by omega : j2.val ≤ N)
  calc
    s j1 = s ⟨min j1.val N, by omega⟩ := (congrArg s h1).symm
    _ ≤ s ⟨min j2.val N, by omega⟩ := by simpa [seq] using hmon
    _ = s j2 := congrArg s h2

/-- a chain strictly increasing between consecutive entries, compared at
natural indices (the index is bounded by `N`). -/
lemma chain_mono_nat {N : ℕ} {s : Fin (N + 1) → ℝ}
    (h : ∀ j : Fin N, s ⟨j.val, by omega⟩ < s ⟨j.val + 1, by omega⟩)
    (m n : ℕ) (hm : m ≤ n) (hn : n ≤ N) : s ⟨m, by omega⟩ ≤ s ⟨n, by omega⟩ := by
  let seq : ℕ → ℝ := fun n => s ⟨min n N, by omega⟩
  have hseq : ∀ n : ℕ, n < N → seq n < seq (n + 1) := by
    intro n hn
    have h1 : (⟨min n N, by omega⟩ : Fin (N + 1)) = ⟨n, by omega⟩ := by
      apply Fin.ext
      exact min_eq_left (by omega : n ≤ N)
    have h2 : (⟨min (n + 1) N, by omega⟩ : Fin (N + 1)) = ⟨n + 1, by omega⟩ := by
      apply Fin.ext
      exact min_eq_left (by omega : n + 1 ≤ N)
    dsimp [seq]
    calc
      s ⟨min n N, by omega⟩ = s ⟨n, by omega⟩ := congrArg s h1
      _ < s ⟨n + 1, by omega⟩ := h ⟨n, by omega⟩
      _ = s ⟨min (n + 1) N, by omega⟩ := (congrArg s h2).symm
  have hmon := seq_mono hseq m n hm (by omega : n ≤ N)
  have h1 : (⟨min m N, by omega⟩ : Fin (N + 1)) = ⟨m, by omega⟩ := by
    apply Fin.ext
    exact min_eq_left (by omega : m ≤ N)
  have h2 : (⟨min n N, by omega⟩ : Fin (N + 1)) = ⟨n, by omega⟩ := by
    apply Fin.ext
    exact min_eq_left (by omega : n ≤ N)
  calc
    s ⟨m, by omega⟩ = s ⟨min m N, by omega⟩ := (congrArg s h1).symm
    _ ≤ s ⟨min n N, by omega⟩ := by simpa [seq] using hmon
    _ = s ⟨n, by omega⟩ := congrArg s h2

/-- bracket points are antitone in the index. -/
lemma bracketPoint_antitone_le (r : ℕ) {i j : Fin (r + 1)} (hij : i.val ≤ j.val) :
    bracketPoint r j ≤ bracketPoint r i := by
  rcases lt_or_eq_of_le hij with hlt | heq
  · exact le_of_lt (bracketPoint_decreasing r hlt)
  · have hbp : bracketPoint r i = bracketPoint r j := by
      unfold bracketPoint
      rw [heq]
    rw [hbp]

/-- for two gaps with `i.val < j.val`, gap `j` lies (weakly) to the left of
gap `i`: `R_j ≤ L_i`. -/
lemma gap_cross {r : ℕ} {i j : Fin r} (hij : i.val < j.val) :
    bracketPoint r ⟨j.val, by omega⟩ ≤ bracketPoint r ⟨i.val + 1, by omega⟩ := by
  exact bracketPoint_antitone_le r (by omega : i.val + 1 ≤ j.val)

/-! ## Generic: sign changes in disjoint brackets give the full root structure -/

/-- intermediate value theorem for a real polynomial: sign change ⇒ root. -/
lemma exists_root_of_mul_neg {p : Polynomial ℝ} {a b : ℝ} (hab : a < b)
    (h : p.eval a * p.eval b < 0) : ∃ r : ℝ, a < r ∧ r < b ∧ p.eval r = 0 := by
  rcases (mul_neg_iff.mp h) with hlt | hlt
  · have hpa_pos : 0 < p.eval a := hlt.1
    have hpb_neg : p.eval b < 0 := hlt.2
    have hIcc : (0 : ℝ) ∈ Set.Icc (p.eval b) (p.eval a) := ⟨le_of_lt hpb_neg, le_of_lt hpa_pos⟩
    have hset : Set.Icc (p.eval b) (p.eval a) ⊆ (fun x => p.eval x) '' Set.Icc a b :=
      intermediate_value_Icc' (le_of_lt hab) p.continuous.continuousOn
    rcases hset hIcc with ⟨c, hcIcc, hc0⟩
    refine ⟨c, ?_, ?_, hc0⟩
    · have hc_ne : c ≠ a := by
        intro hca
        subst c
        linarith
      exact lt_of_le_of_ne hcIcc.1 (Ne.symm hc_ne)
    · have hc_ne : c ≠ b := by
        intro hcb
        subst c
        linarith
      exact lt_of_le_of_ne hcIcc.2 hc_ne
  · have hpa_neg : p.eval a < 0 := hlt.1
    have hpb_pos : 0 < p.eval b := hlt.2
    have hIcc : (0 : ℝ) ∈ Set.Icc (p.eval a) (p.eval b) := ⟨le_of_lt hpa_neg, le_of_lt hpb_pos⟩
    have hset : Set.Icc (p.eval a) (p.eval b) ⊆ (fun x => p.eval x) '' Set.Icc a b :=
      intermediate_value_Icc (le_of_lt hab) p.continuous.continuousOn
    rcases hset hIcc with ⟨c, hcIcc, hc0⟩
    refine ⟨c, ?_, ?_, hc0⟩
    · have hc_ne : c ≠ a := by
        intro hca
        subst c
        linarith
      exact lt_of_le_of_ne hcIcc.1 (Ne.symm hc_ne)
    · have hc_ne : c ≠ b := by
        intro hcb
        subst c
        linarith
      exact lt_of_le_of_ne hcIcc.2 hc_ne

/-- A real monic polynomial whose values at the endpoints of pairwise separated
brackets `[x k, y k]` change sign on each bracket splits over the real roots
found there: one root per bracket, factorization, no other roots, and each
bracket contains no other root. -/
lemma split_of_segments {ι : Type*} [Fintype ι] [DecidableEq ι] {G : Polynomial ℝ}
    (hGmon : G.Monic) (hGdeg : G.natDegree = Fintype.card ι)
    {x y : ι → ℝ} {K : ℝ}
    (hxy : ∀ k : ι, x k < y k)
    (hsign : ∀ k : ι, G.eval (x k) * G.eval (y k) < 0)
    (hIcc : ∀ k : ι, aSerre ≤ x k ∧ y k ≤ bSerre)
    (hK : ∀ k : ι, K ≤ |G.eval (x k)| ∧ K ≤ |G.eval (y k)|)
    (hsep : ∀ ⦃k k' : ι⦄, k ≠ k' → y k ≤ x k' ∨ y k' ≤ x k) :
    ∃ r : ι → ℝ,
      (∀ k : ι, x k < r k ∧ r k < y k ∧ G.eval (r k) = 0) ∧
      G = ∏ k : ι, (Polynomial.X - Polynomial.C (r k)) ∧
      (∀ β : ℝ, G.eval β = 0 → ∃ k : ι, β = r k) ∧
      (∀ k : ι, ∀ w : ℝ, x k ≤ w → w ≤ y k → G.eval w = 0 → w = r k) := by
  classical
  have hroot : ∀ k : ι, ∃ ρ : ℝ, x k < ρ ∧ ρ < y k ∧ G.eval ρ = 0 := fun k =>
    exists_root_of_mul_neg (hxy k) (hsign k)
  let r : ι → ℝ := fun k => Classical.choose (hroot k)
  have hr_gt : ∀ k : ι, x k < r k := fun k => (Classical.choose_spec (hroot k)).1
  have hr_lt : ∀ k : ι, r k < y k := fun k => (Classical.choose_spec (hroot k)).2.1
  have hr_root : ∀ k : ι, G.eval (r k) = 0 := fun k => (Classical.choose_spec (hroot k)).2.2
  have hrinj : Function.Injective r := by
    intro k l hkl
    by_contra hne
    rcases hsep (k := k) (k' := l) hne with hylx | hlyx
    · have hlt : r k < r l := lt_trans (hr_lt k) (lt_of_le_of_lt hylx (hr_gt l))
      exact (ne_of_lt hlt) hkl
    · have hlt : r l < r k := lt_trans (hr_lt l) (lt_of_le_of_lt hlyx (hr_gt k))
      exact (ne_of_lt hlt) hkl.symm
  have hAmon : (∏ k : ι, (Polynomial.X - Polynomial.C (r k))).Monic := by
    rw [show (∏ k : ι, (Polynomial.X - Polynomial.C (r k))) =
        ∏ k ∈ (Finset.univ : Finset ι), (Polynomial.X - Polynomial.C (r k)) by rfl]
    exact Polynomial.monic_prod_of_monic (Finset.univ : Finset ι)
      (fun k => Polynomial.X - Polynomial.C (r k))
      (by intro k hk; exact Polynomial.monic_X_sub_C (r k))
  have hAdeg : (∏ k : ι, (Polynomial.X - Polynomial.C (r k))).natDegree = Fintype.card ι := by
    rw [show (∏ k : ι, (Polynomial.X - Polynomial.C (r k))) =
        ∏ k ∈ (Finset.univ : Finset ι), (Polynomial.X - Polynomial.C (r k)) by rfl]
    rw [Polynomial.natDegree_prod_of_monic]
    · calc
        (∑ k ∈ (Finset.univ : Finset ι), ((Polynomial.X - Polynomial.C (r k)).natDegree))
            = ∑ _k ∈ (Finset.univ : Finset ι), (1 : ℕ) := by
                apply Finset.sum_congr rfl
                intro k hk
                rw [Polynomial.natDegree_X_sub_C]
        _ = Fintype.card ι := by
                rw [Finset.sum_const, Finset.card_univ]
                simp
    · intro k hk
      exact Polynomial.monic_X_sub_C (r k)
  have hdiv : (∏ k : ι, (Polynomial.X - Polynomial.C (r k))) ∣ G := by
    refine Fintype.prod_dvd_of_coprime ?_ ?_
    · exact Polynomial.pairwise_coprime_X_sub_C hrinj
    · intro k
      rw [Polynomial.dvd_iff_isRoot]
      exact hr_root k
  have hfac : G = ∏ k : ι, (Polynomial.X - Polynomial.C (r k)) := by
    exact Polynomial.eq_of_monic_of_dvd_of_natDegree_le hAmon hGmon hdiv (by rw [hAdeg, hGdeg])
  -- classification of real roots
  have hclass : ∀ β : ℝ, G.eval β = 0 → ∃ k : ι, β = r k := by
    intro β hβ
    have hz : (Polynomial.eval β) (∏ k : ι, (Polynomial.X - Polynomial.C (r k))) = 0 := by
      simpa [hfac] using hβ
    have hprod : (∏ k : ι, (β - r k)) = 0 := by
      simpa [Polynomial.eval_prod] using hz
    rw [show (∏ k : ι, (β - r k)) =
        ∏ k ∈ (Finset.univ : Finset ι), (β - r k) by rfl] at hprod
    rcases (Finset.prod_eq_zero_iff.mp hprod) with ⟨k, hk, hzero⟩
    refine ⟨k, ?_⟩
    exact sub_eq_zero.mp hzero
  refine ⟨r, ?_, hfac, hclass, ?_⟩
  · intro k
    exact ⟨hr_gt k, hr_lt k, hr_root k⟩
  · intro k w hxw hyw hwroot
    rcases hclass w hwroot with ⟨k', hwk'⟩
    by_cases hkk : k' = k
    · subst k'
      exact hwk'
    · have hne : k ≠ k' := fun h => hkk h.symm
      have hsep' := hsep (k := k) (k' := k') hne
      rcases hsep' with hylx | hlyx
      · have h1 : x k' < r k' := hr_gt k'
        have h2 : r k' ≤ y k := by
          rw [← hwk']
          exact hyw
        linarith [h1, h2, hylx]
      · have h1 : r k' < y k' := hr_lt k'
        have h2 : x k ≤ r k' := by
          rw [← hwk']
          exact hxw
        linarith [h1, hlyx, h2]

/-! ## Transfer of magnitude and sign from `Q0` to `Q` at the level points -/

/-- at a level point (`|Q0| ≥ 8·C2val⁻¹·κ^{Dr}`) with `|Q − Q0| < 6·C2val⁻¹·κ^{Dr}`
we get `|Q| ≥ 2·C2val⁻¹·κ^{Dr}`. -/
lemma Q_level_mag {T Q0 Q : Polynomial ℝ} {v : ℝ} {r : ℕ}
    (hQ0 : Q0 = ∏ j' ∈ Finset.range Bclps.Dconst, (T - Polynomial.C (factorCenter r j')))
    (m : ℕ) (hv : T.eval v = (m : ℝ) * levelStep r)
    (hclose : |Q.eval v - Q0.eval v| < 6 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r)) :
    2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ≤ |Q.eval v| := by
  have hq0 : 8 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ≤ |Q0.eval v| :=
    CompQlevels.level_mag r hQ0 m hv
  have htri : |Q0.eval v| ≤ |Q.eval v| + |Q0.eval v - Q.eval v| := by
    calc
      |Q0.eval v| = |(Q0.eval v - Q.eval v) + Q.eval v| := by congr 1; ring
      _ ≤ |Q0.eval v - Q.eval v| + |Q.eval v| := abs_add_le _ _
      _ = |Q.eval v| + |Q0.eval v - Q.eval v| := by rw [add_comm]
  have hq0a : |Q0.eval v - Q.eval v| = |Q.eval v - Q0.eval v| := abs_sub_comm _ _
  have hcpos : 0 < C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) :=
    mul_pos (inv_pos.mpr C2val_pos) (pow_pos kappa_pos (Bclps.Dconst * r))
  nlinarith [hq0, htri, hclose, hcpos, hq0a]

/-- `Q0` is nonzero at a level point (it has the big magnitude lower bound). -/
lemma Q0_level_ne_zero {T Q0 : Polynomial ℝ} {v : ℝ} {r : ℕ}
    (hQ0 : Q0 = ∏ j' ∈ Finset.range Bclps.Dconst, (T - Polynomial.C (factorCenter r j')))
    (m : ℕ) (hv : T.eval v = (m : ℝ) * levelStep r) : Q0.eval v ≠ 0 := by
  have hmag := CompQlevels.level_mag r hQ0 m hv
  have hpos : (0 : ℝ) < 8 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by
    exact mul_pos (mul_pos (by norm_num) (inv_pos.mpr C2val_pos))
      (pow_pos kappa_pos (Bclps.Dconst * r))
  have hmagpos : 0 < |Q0.eval v| := lt_of_lt_of_le hpos hmag
  exact (abs_pos.mp hmagpos)

/-- at a pair of consecutive level points, closeness to `Q0` (which changes
sign) makes `Q` change sign.  Here `x` has level `(m+1)·u` and `y` level `m·u`. -/
lemma Q_level_pair_neg {T Q0 Q : Polynomial ℝ} {x y : ℝ} {r m : ℕ}
    (hQ0 : Q0 = ∏ j' ∈ Finset.range Bclps.Dconst, (T - Polynomial.C (factorCenter r j')))
    (hmD : m + 1 ≤ D)
    (hxL : T.eval x = ((m + 1 : ℕ) : ℝ) * levelStep r)
    (hyL : T.eval y = (m : ℝ) * levelStep r)
    (hx : |Q.eval x - Q0.eval x| < |Q0.eval x|)
    (hy : |Q.eval y - Q0.eval y| < |Q0.eval y|) :
    Q.eval x * Q.eval y < 0 := by
  have hq0 : Q0.eval y * Q0.eval x < 0 := CompQlevelsPair.level_pair_neg r hQ0 m hyL hxL hmD
  have hxne : Q0.eval x ≠ 0 := Q0_level_ne_zero hQ0 (m + 1) hxL
  have hyne : Q0.eval y ≠ 0 := Q0_level_ne_zero hQ0 m hyL
  have sx : 0 < Q.eval x * Q0.eval x := Bclps.mul_pos_of_close hxne hx
  have sy : 0 < Q.eval y * Q0.eval y := Bclps.mul_pos_of_close hyne hy
  have hprod : 0 < (Q.eval x * Q.eval y) * (Q0.eval x * Q0.eval y) := by
    calc
      0 < (Q.eval x * Q0.eval x) * (Q.eval y * Q0.eval y) := mul_pos sx sy
      _ = (Q.eval x * Q.eval y) * (Q0.eval x * Q0.eval y) := by ring
  have hneg : Q0.eval x * Q0.eval y < 0 := by simpa [mul_comm] using hq0
  rcases mul_pos_iff.mp hprod with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have : 0 < Q0.eval x * Q0.eval y := h2
    linarith
  · exact h1

/-! ## The level chain in one bracket gap -/

/-- In each bracket gap the polynomial `Q` changes sign between consecutive
level points and keeps the value bound `2·C2val⁻¹·κ^{Dr}` at those points. -/
lemma gap_segments (r : ℕ) (hr2 : 2 ≤ r) {T Q0 Q : Polynomial ℝ}
    (hQ0 : Q0 = ∏ j' ∈ Finset.range Bclps.Dconst, (T - Polynomial.C (factorCenter r j')))
    (hTsgn : ∀ i : Fin (r + 1),
      0 < T.eval (bracketPoint r i) * (prunedPoly r).eval (bracketPoint r i))
    (hTmag : ∀ i : Fin (r + 1), |T.eval (bracketPoint r i)| ≥ kappaC ^ r / 64)
    (hc8 : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → |Q.eval x - Q0.eval x| <
      8 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r))
    (hc6 : ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre → |Q.eval x - Q0.eval x| <
      6 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r))
    (i : Fin r) :
    ∃ s : Fin (D + 1) → ℝ,
      (∀ j : Fin (D + 1), bracketPoint r ⟨i.val + 1, by omega⟩ ≤ s j ∧
          s j ≤ bracketPoint r ⟨i.val, by omega⟩) ∧
      (∀ j : Fin D, s ⟨j.val, by omega⟩ < s ⟨j.val + 1, by omega⟩) ∧
      (∀ j : Fin D, Q.eval (s ⟨j.val, by omega⟩) * Q.eval (s ⟨j.val + 1, by omega⟩) < 0 ∧
        2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ≤ |Q.eval (s ⟨j.val, by omega⟩)| ∧
        2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ≤ |Q.eval (s ⟨j.val + 1, by omega⟩)|) := by
  classical
  let u : ℝ := levelStep r
  have hu : 0 < u := levelStep_pos r
  let L : ℝ := bracketPoint r ⟨i.val + 1, by omega⟩
  let R : ℝ := bracketPoint r ⟨i.val, by omega⟩
  have hLR : L < R := by
    dsimp [L, R]
    exact bracketPoint_decreasing r (by omega : i.val < i.val + 1)
  have hL_Icc : L ∈ Set.Icc aSerre bSerre := by
    dsimp [L]
    exact bracketPoint_mem_Icc r ⟨i.val + 1, by omega⟩
  have hR_Icc : R ∈ Set.Icc aSerre bSerre := by
    dsimp [R]
    exact bracketPoint_mem_Icc r ⟨i.val, by omega⟩
  have hclose_at : ∀ x : ℝ, L ≤ x → x ≤ R → |Q.eval x - Q0.eval x| <
      8 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by
    intro x hxL hxR
    exact hc8 x ⟨le_trans hL_Icc.1 hxL, le_trans hxR hR_Icc.2⟩
  have hclose_at6 : ∀ x : ℝ, L ≤ x → x ≤ R → |Q.eval x - Q0.eval x| <
      6 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by
    intro x hxL hxR
    exact hc6 x ⟨le_trans hL_Icc.1 hxL, le_trans hxR hR_Icc.2⟩
  -- sign/magnitude helpers on a chain point that sits inside the gap
  have level_close_lt : ∀ (v : ℝ) (m : ℕ), L ≤ v → v ≤ R →
      T.eval v = (m : ℝ) * u →
      |Q.eval v - Q0.eval v| < |Q0.eval v| := by
    intro v m hvL hvR hvm
    exact lt_of_lt_of_le (hclose_at v hvL hvR) (CompQlevels.level_mag r hQ0 m hvm)
  by_cases heven : Even i.val
  · -- levels ascend with x; positive end is `R`
    have hnegL : T.eval L ≤ -((D : ℝ) * u) := by
      have h1 := bracket_T_signed_mag r hr2 hTsgn hTmag ⟨i.val + 1, by omega⟩
      have hodd1 : Odd (i.val + 1) := by
        rcases (even_iff_two_dvd.mp heven) with ⟨c, hc⟩
        exact ⟨c, by omega⟩
      have hpow : (-1 : ℝ) ^ (i.val + 1) = -1 := (Odd.neg_one_pow (n := i.val + 1)) hodd1
      dsimp [L, u]
      rw [hpow] at h1
      nlinarith
    have hposR : (D : ℝ) * u ≤ T.eval R := by
      have h1 := bracket_T_signed_mag r hr2 hTsgn hTmag ⟨i.val, by omega⟩
      have hpow : (-1 : ℝ) ^ (i.val) = 1 := heven.neg_one_pow
      dsimp [R, u]
      rw [hpow] at h1
      simpa using h1
    rcases (Submission.ChainLevels.chain_up (D := D) D_pos hu (p := T) hLR hnegL hposR) with ⟨s, hs1, hs2, hs3⟩
    have hbounds : ∀ j : Fin (D + 1), L ≤ s j ∧ s j ≤ R := by
      intro j
      have h := hs1 j
      exact ⟨le_of_lt h.1, h.2⟩
    refine ⟨s, hbounds, hs3, ?_⟩
    intro j
    let m : ℕ := j.val
    have hvl : T.eval (s ⟨j.val + 1, by omega⟩) = ((m + 1 : ℕ) : ℝ) * u := by
      dsimp [m]
      simpa [u] using hs2 ⟨j.val + 1, by omega⟩
    have hvr : T.eval (s ⟨j.val, by omega⟩) = (m : ℝ) * u := by
      dsimp [m]
      simpa [u] using hs2 ⟨j.val, by omega⟩
    have hx : |Q.eval (s ⟨j.val + 1, by omega⟩) - Q0.eval (s ⟨j.val + 1, by omega⟩)| <
        |Q0.eval (s ⟨j.val + 1, by omega⟩)| := level_close_lt (s ⟨j.val + 1, by omega⟩) (m + 1)
          (hbounds ⟨j.val + 1, by omega⟩).1 (hbounds ⟨j.val + 1, by omega⟩).2 hvl
    have hy : |Q.eval (s ⟨j.val, by omega⟩) - Q0.eval (s ⟨j.val, by omega⟩)| <
        |Q0.eval (s ⟨j.val, by omega⟩)| := level_close_lt (s ⟨j.val, by omega⟩) m
          (hbounds ⟨j.val, by omega⟩).1 (hbounds ⟨j.val, by omega⟩).2 hvr
    have hsign : Q.eval (s ⟨j.val, by omega⟩) * Q.eval (s ⟨j.val + 1, by omega⟩) < 0 := by
      have hp := Q_level_pair_neg hQ0 (m := m) (hmD := by dsimp [m]; omega) hvl hvr hx hy
      simpa [mul_comm] using hp
    have hmg1 : 2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ≤
        |Q.eval (s ⟨j.val, by omega⟩)| :=
      Q_level_mag hQ0 m hvr (hclose_at6 (s ⟨j.val, by omega⟩)
        (hbounds ⟨j.val, by omega⟩).1 (hbounds ⟨j.val, by omega⟩).2)
    have hmg2 : 2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ≤
        |Q.eval (s ⟨j.val + 1, by omega⟩)| :=
      Q_level_mag hQ0 (m + 1) hvl (hclose_at6 (s ⟨j.val + 1, by omega⟩)
        (hbounds ⟨j.val + 1, by omega⟩).1 (hbounds ⟨j.val + 1, by omega⟩).2)
    exact ⟨hsign, hmg1, hmg2⟩
  · -- levels descend with x; positive end is `L`
    have hposL : (D : ℝ) * u ≤ T.eval L := by
      have h1 := bracket_T_signed_mag r hr2 hTsgn hTmag ⟨i.val + 1, by omega⟩
      have hodd : Odd i.val := (Nat.even_or_odd i.val).resolve_left heven
      have heven1 : Even (i.val + 1) := by
        rcases hodd with ⟨c, hc⟩
        refine ⟨c + 1, ?_⟩
        omega
      have hpow : (-1 : ℝ) ^ (i.val + 1) = 1 := (Even.neg_one_pow (n := i.val + 1)) heven1
      dsimp [L, u]
      rw [hpow] at h1
      simpa using h1
    have hnegR : T.eval R ≤ -((D : ℝ) * u) := by
      have h1 := bracket_T_signed_mag r hr2 hTsgn hTmag ⟨i.val, by omega⟩
      have hodd : Odd i.val := (Nat.even_or_odd i.val).resolve_left heven
      have hpow : (-1 : ℝ) ^ (i.val) = -1 := (Odd.neg_one_pow (n := i.val)) hodd
      dsimp [R, u]
      rw [hpow] at h1
      nlinarith
    rcases (Submission.ChainDown.chain_down (D := D) D_pos hu (p := T) hLR hnegR hposL) with ⟨s, hs1, hs2, hs3⟩
    have hbounds : ∀ j : Fin (D + 1), L ≤ s j ∧ s j ≤ R := hs1
    refine ⟨s, hbounds, hs3, ?_⟩
    intro j
    let m : ℕ := D - (j.val + 1)
    have hvl : T.eval (s ⟨j.val, by omega⟩) = ((m + 1 : ℕ) : ℝ) * u := by
      dsimp [m]
      have hcast : (D - (j.val + 1) + 1 : ℕ) = (D - j.val : ℕ) := by omega
      rw [hcast]
      simpa [u] using hs2 ⟨j.val, by omega⟩
    have hvr : T.eval (s ⟨j.val + 1, by omega⟩) = (m : ℝ) * u := by
      dsimp [m]
      simpa [u] using hs2 ⟨j.val + 1, by omega⟩
    have hx : |Q.eval (s ⟨j.val, by omega⟩) - Q0.eval (s ⟨j.val, by omega⟩)| <
        |Q0.eval (s ⟨j.val, by omega⟩)| := level_close_lt (s ⟨j.val, by omega⟩) (m + 1)
          (hbounds ⟨j.val, by omega⟩).1 (hbounds ⟨j.val, by omega⟩).2 hvl
    have hy : |Q.eval (s ⟨j.val + 1, by omega⟩) - Q0.eval (s ⟨j.val + 1, by omega⟩)| <
        |Q0.eval (s ⟨j.val + 1, by omega⟩)| := level_close_lt (s ⟨j.val + 1, by omega⟩) m
          (hbounds ⟨j.val + 1, by omega⟩).1 (hbounds ⟨j.val + 1, by omega⟩).2 hvr
    have hsign : Q.eval (s ⟨j.val, by omega⟩) * Q.eval (s ⟨j.val + 1, by omega⟩) < 0 := by
      exact Q_level_pair_neg hQ0 (m := m) (hmD := by dsimp [m]; omega) hvl hvr hx hy
    have hmg1 : 2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ≤
        |Q.eval (s ⟨j.val, by omega⟩)| :=
      Q_level_mag hQ0 (m + 1) hvl (hclose_at6 (s ⟨j.val, by omega⟩)
        (hbounds ⟨j.val, by omega⟩).1 (hbounds ⟨j.val, by omega⟩).2)
    have hmg2 : 2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ≤
        |Q.eval (s ⟨j.val + 1, by omega⟩)| :=
      Q_level_mag hQ0 m hvr (hclose_at6 (s ⟨j.val + 1, by omega⟩)
        (hbounds ⟨j.val + 1, by omega⟩).1 (hbounds ⟨j.val + 1, by omega⟩).2)
    exact ⟨hsign, hmg1, hmg2⟩

/-! ## The core construction -/

/-- The root-location core: given the construction data and the two large-`r`
thresholds, all roots of `Q` are real in the open Serre interval and every root
is bracketed by level points with endpoint bound `2·C2val⁻¹·κ^{Dr}` and no
other root in the bracket. -/
lemma comp_Q_roots_core (r : ℕ) (hr2 : 2 ≤ r)
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
    (∀ z : ℂ, Polynomial.aeval z Q = 0 → (aSerre : ℂ) < z ∧ z < (bSerre : ℂ)) ∧
    (∀ β : ℝ, Q.eval β = 0 → ∃ x y : ℝ,
      aSerre ≤ x ∧ x < β ∧ β < y ∧ y ≤ bSerre ∧
      (2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ≤ |Q.eval x|) ∧
      (2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ≤ |Q.eval y|) ∧
      (∀ w : ℝ, x ≤ w → w ≤ y → Q.eval w = 0 → w = β)) := by
  classical
  let K : ℝ := 2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r)
  have hKpos : 0 < K := by
    dsimp [K]
    exact mul_pos (mul_pos (by norm_num) (inv_pos.mpr C2val_pos))
      (pow_pos kappa_pos (Bclps.Dconst * r))
  -- pointwise closeness of Q and Q0 on the interval
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
    have hpos : 0 < kappaC ^ (Bclps.Dconst * r) := pow_pos kappa_pos _
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
    have hpos : 0 < kappaC ^ (Bclps.Dconst * r) := pow_pos kappa_pos _
    have hlt : kappaC ^ (Bclps.Dconst * r) *
          (4 / ((kappaC - 1) * kappaC ^ (r - 1)) + 2 * C2val⁻¹) <
        6 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by
      nlinarith [mul_lt_mul_of_pos_right hsum hpos, hpos]
    exact lt_of_le_of_lt h hlt
  -- per-gap chains
  have hgap : ∀ i : Fin r, ∃ s : Fin (D + 1) → ℝ,
      (∀ j : Fin (D + 1), bracketPoint r ⟨i.val + 1, by omega⟩ ≤ s j ∧
          s j ≤ bracketPoint r ⟨i.val, by omega⟩) ∧
      (∀ j : Fin D, s ⟨j.val, by omega⟩ < s ⟨j.val + 1, by omega⟩) ∧
      (∀ j : Fin D, Q.eval (s ⟨j.val, by omega⟩) * Q.eval (s ⟨j.val + 1, by omega⟩) < 0 ∧
        K ≤ |Q.eval (s ⟨j.val, by omega⟩)| ∧ K ≤ |Q.eval (s ⟨j.val + 1, by omega⟩)|) := by
    intro i
    rcases (gap_segments r hr2 hQ0 hTsgn hTmag hclose8 hclose6 i) with ⟨s, hs1, hs2, hs3⟩
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
  let ι : Type := Fin r × Fin D
  let xx : ι → ℝ := fun k => sfunc k.1 ⟨k.2.val, by omega⟩
  let yy : ι → ℝ := fun k => sfunc k.1 ⟨k.2.val + 1, by omega⟩
  -- monic degree Dr
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
  -- hypotheses of the generic splitting lemma
  have hxy : ∀ k : ι, xx k < yy k := by
    intro k
    dsimp [ι, xx, yy]
    exact (sfunc_spec k.1).2.1 k.2
  have hsign : ∀ k : ι, Q.eval (xx k) * Q.eval (yy k) < 0 := by
    intro k
    dsimp [ι, xx, yy]
    exact ((sfunc_spec k.1).2.2 k.2).1
  have hIcc : ∀ k : ι, aSerre ≤ xx k ∧ yy k ≤ bSerre := by
    intro k
    dsimp [ι, xx, yy]
    have hx : aSerre ≤ sfunc k.1 ⟨k.2.val, by omega⟩ :=
      le_trans (bracketPoint_mem_Icc r ⟨k.1.val + 1, by omega⟩).1
        ((sfunc_spec k.1).1 ⟨k.2.val, by omega⟩).1
    have hy : sfunc k.1 ⟨k.2.val + 1, by omega⟩ ≤ bSerre :=
      le_trans ((sfunc_spec k.1).1 ⟨k.2.val + 1, by omega⟩).2
        (bracketPoint_mem_Icc r ⟨k.1.val, by omega⟩).2
    exact ⟨hx, hy⟩
  have hK : ∀ k : ι, K ≤ |Q.eval (xx k)| ∧ K ≤ |Q.eval (yy k)| := by
    intro k
    dsimp [ι, xx, yy]
    exact ⟨((sfunc_spec k.1).2.2 k.2).2.1, ((sfunc_spec k.1).2.2 k.2).2.2⟩
  have hsep : ∀ ⦃k k' : ι⦄, k ≠ k' → yy k ≤ xx k' ∨ yy k' ≤ xx k := by
    intro k k' hkk'
    by_cases h1 : k.1.val < k'.1.val
    · right
      -- gap k is right of gap k'; so gap k' lies left: yy k' ≤ xx k
      have hA : yy k' ≤ bracketPoint r ⟨k'.1.val, by omega⟩ := by
        dsimp [yy]
        exact ((sfunc_spec k'.1).1 ⟨k'.2.val + 1, by omega⟩).2
      have hB : bracketPoint r ⟨k'.1.val, by omega⟩ ≤ bracketPoint r ⟨k.1.val + 1, by omega⟩ :=
        gap_cross (r := r) (i := k.1) (j := k'.1) h1
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
          gap_cross (r := r) (i := k'.1) (j := k.1) h2
        have hC : bracketPoint r ⟨k'.1.val + 1, by omega⟩ ≤ xx k' := by
          dsimp [xx]
          exact ((sfunc_spec k'.1).1 ⟨k'.2.val, by omega⟩).1
        exact le_trans hA (le_trans hB hC)
      · -- same gap index, different segment index
        have hEq : k.1 = k'.1 := by
          apply Fin.ext
          omega
        have hne2 : k.2 ≠ k'.2 := by
          intro h
          exact hkk' (Prod.ext hEq h)
        have hj : k.2.val < k'.2.val ∨ k'.2.val < k.2.val :=
          lt_or_gt_of_ne (fun h => hne2 (Fin.ext h))
        rcases hj with hjlt | hjgt
        · left
          -- within the same gap the segments are ordered
          have hmon : sfunc k'.1 ⟨k.2.val + 1, by omega⟩ ≤ sfunc k'.1 ⟨k'.2.val, by omega⟩ :=
            chain_mono_nat (s := sfunc k'.1) (sfunc_spec k'.1).2.1
              (k.2.val + 1) k'.2.val (by omega) (by omega)
          have hyy : yy k ≤ xx k' := by
            dsimp [yy, xx]
            rw [hEq]
            exact hmon
          exact hyy
        · right
          have hk2D : k.2.val ≤ D := by omega
          have hmon : sfunc k'.1 ⟨k'.2.val + 1, by omega⟩ ≤ sfunc k'.1 ⟨k.2.val, by omega⟩ :=
            chain_mono_nat (s := sfunc k'.1) (sfunc_spec k'.1).2.1
              (k'.2.val + 1) k.2.val (by omega) (by omega)
          have hyy : yy k' ≤ xx k := by
            dsimp [yy, xx]
            rw [hEq]
            exact hmon
          exact hyy
  -- invoke the generic splitting lemma
  rcases (split_of_segments (G := Q) hGmon hGdeg hxy hsign hIcc hK hsep) with
    ⟨rho, hrho1, hfacQ, hclassQ, hbracket⟩
  constructor
  · -- all complex roots lie in the open Serre interval
    intro z hz
    have hzfac : (Polynomial.aeval z) (∏ k : ι, (Polynomial.X - Polynomial.C (rho k))) = 0 := by
      simpa [hfacQ] using hz
    have hprod : (∏ k : ι, (z - (rho k : ℂ))) = 0 := by
      simpa using hzfac
    rw [show (∏ k : ι, (z - (rho k : ℂ))) =
        ∏ k ∈ (Finset.univ : Finset ι), (z - (rho k : ℂ)) by rfl] at hprod
    rcases (Finset.prod_eq_zero_iff.mp hprod) with ⟨k, hk, hzi⟩
    have hz_eq : z = (rho k : ℂ) := sub_eq_zero.mp hzi
    constructor
    · rw [hz_eq]
      exact Complex.real_lt_real.mpr (lt_of_le_of_lt (hIcc k).1 (hrho1 k).1)
    · rw [hz_eq]
      exact Complex.real_lt_real.mpr (lt_of_lt_of_le (hrho1 k).2.1 (hIcc k).2)
  · -- bracket around each real root
    intro β hβ
    rcases hclassQ β hβ with ⟨k, hkβ⟩
    refine ⟨xx k, yy k, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (hIcc k).1
    · rw [hkβ]
      exact (hrho1 k).1
    · rw [hkβ]
      exact (hrho1 k).2.1
    · exact (hIcc k).2
    · have hb : 2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ≤ |Q.eval (xx k)| := by
        simpa [K] using (hK k).1
      exact hb
    · have hb : 2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) ≤ |Q.eval (yy k)| := by
        simpa [K] using (hK k).2
      exact hb
    · intro w hxw hyw hwroot
      have hw := hbracket k w hxw hyw hwroot
      rw [hkβ]
      exact hw

/-- **Root location of the complementary polynomial.**  Any polynomial `Q`
built from the `defn:comp_Q` data (input `P` of degree `n` plays no role in
this statement) has, for all `r ≥ C`, all roots in the open Serre interval,
splits into `Dr` strictly increasing real roots there, and each root is
bracketed by an interval with endpoint lower bounds `C⁻¹·κ^{Dr}` and no other
root inside. -/
theorem comp_Q_roots : ∃ C0 : ℕ, 2 ≤ C0 ∧
  ∀ (r : ℕ), C0 ≤ r → ∀ (T Q0 Q1 Q : Polynomial ℝ) (eps : ℕ → ℝ) (N : ℝ),
    T.Monic → T.natDegree = r →
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
    (∀ z : ℂ, Polynomial.aeval z Q = 0 → (aSerre : ℂ) < z ∧ z < (bSerre : ℂ)) ∧
    (∃ C : ℝ, 0 < C ∧
      (∀ β : ℝ, Q.eval β = 0 → ∃ x y : ℝ,
        aSerre ≤ x ∧ x < β ∧ β < y ∧ y ≤ bSerre ∧
        |Q.eval x| ≥ C⁻¹ * kappaC ^ (Bclps.Dconst * r) ∧
        |Q.eval y| ≥ C⁻¹ * kappaC ^ (Bclps.Dconst * r) ∧
        (∀ w : ℝ, x ≤ w → w ≤ y → Q.eval w = 0 → w = β))) := by
  classical
  rcases large_r with ⟨C6, hC6⟩
  rcases large_r4 with ⟨C4, hC4⟩
  let C0 : ℕ := max (max C6 C4) 2
  refine ⟨C0, ?_, ?_⟩
  · dsimp [C0]
    omega
  · intro r hr T Q0 Q1 Q eps N hTmon hTdeg hTsm hQ0 hQ1 hQ hEps hN0 hNle
    have hr2 : 2 ≤ r := by dsimp [C0] at hr; omega
    have hC6r : C6 ≤ r := by dsimp [C0] at hr; omega
    have hC4r : C4 ≤ r := by dsimp [C0] at hr; omega
    have h6r : (4 : ℝ) / ((kappaC - 1) * kappaC ^ (r - 1)) < 6 * C2val⁻¹ := by
      simpa [div_eq_mul_inv] using (hC6 r hC6r)
    have h4r : (4 : ℝ) / ((kappaC - 1) * kappaC ^ (r - 1)) < 4 * C2val⁻¹ := by
      simpa [div_eq_mul_inv] using (hC4 r hC4r)
    have hTsgn : ∀ i : Fin (r + 1),
        0 < T.eval (bracketPoint r i) * (prunedPoly r).eval (bracketPoint r i) := fun i => (hTsm i).1
    have hTmag : ∀ i : Fin (r + 1), |T.eval (bracketPoint r i)| ≥ kappaC ^ r / 64 := fun i => (hTsm i).2
    have hcore := comp_Q_roots_core r hr2 h6r h4r eps N hTmon hTdeg hTsgn hTmag hQ0 hQ1 hQ hEps hN0 hNle
    constructor
    · exact hcore.1
    · -- second part: constant C := C2val/2
      have hc2pos : 0 < C2val := C2val_pos
      refine ⟨C2val / 2, div_pos hc2pos (by norm_num), ?_⟩
      intro β hβ
      rcases hcore.2 β hβ with ⟨x, y, hx1, hx2, hx3, hx4, hKx, hKy, hnone⟩
      refine ⟨x, y, hx1, hx2, hx3, hx4, ?_, ?_, hnone⟩
      · have hrew : (C2val / 2)⁻¹ * kappaC ^ (Bclps.Dconst * r) =
            2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by
          have hc2ne : C2val ≠ 0 := ne_of_gt C2val_pos
          field_simp [hc2ne]
        rw [hrew]
        exact hKx
      · have hrew : (C2val / 2)⁻¹ * kappaC ^ (Bclps.Dconst * r) =
            2 * C2val⁻¹ * kappaC ^ (Bclps.Dconst * r) := by
          have hc2ne : C2val ≠ 0 := ne_of_gt C2val_pos
          field_simp [hc2ne]
        rw [hrew]
        exact hKy

