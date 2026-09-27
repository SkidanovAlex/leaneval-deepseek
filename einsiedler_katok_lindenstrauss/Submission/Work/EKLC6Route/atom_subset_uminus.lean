import Mathlib
import Submission.Work.EKLC6Route.Defs
import Submission.Work.EKLC6Core.uniform_contraction_horo
import Submission.Work.EKLC6Core.covAlong
import Submission.Work.EKLC6Core.firstReturn_partition
import Submission.Work.EKLC6Core.atom_iSup_comap_iterate_eq
import Submission.Work.EKLC6Core.tendsto_of_mem_V
import Submission.Work.EKLC6Route.S_surj
import Submission.Work.EKLC6Route.piece_mem_of_mem_W
import Submission.Work.EKLC6Route.piece_partition
import Submission.Work.EKLC6Route.eq_of_mem_V_of_smul_eq
import Submission.Work.EKLC6Route.mem_uminus_of_shadowing_seq
import Submission.Work.EKLC6Route.conj_rate_and_bound
import Submission.Work.EKLC6Route.chartSet_measurable
import Submission.Work.EKLC6Route.gridIdx_ratio_mem_V
import Submission.Work.EKLC6Route.VtSet_mul_inv
import Submission.Work.EKLC6Route.aDiag_conj_mem_V_of_mem_VtSet
import Submission.Work.EKLC6Route.aDiag_conj_mem_V_of_mem_uminus
import Submission.Work.EKLC6Route.track_mem_V
import Submission.Work.EKLC6Route.track_conj_mem_V
import Submission.Work.EKLC6Route.gridLev_mul_exp_le_one
import Submission.Work.EKLC6Route.dev_estimates
import Submission.Work.EKLProd.aDiag_nsmul
import Submission.Work.EKLContract.Lemmas.V_open_one

noncomputable section
namespace Work.EKLC6Route
open MeasureTheory Filter Topology
open scoped ENNReal
open Work.EKLContract Work.EKLC6Core
open Classical

/-!
# `Work.EKLC6Route.atom_subset_uminus`

The upper bound (Pisa 7.53, tracking form) of the window route: if `x` visits the window `w.W`
infinitely often at every depth (`hvis`) and never enters `w.N0`, then every point of the past
atom `[x]_{w.A}` is of the form `u • x` with `u ∈ Uminus t`, with entries bounded by `2` when
`x ∈ w.W`, and conversely every `u ∈ Uminus t` with `u • x ∈ [x]_{w.A}` is bounded.

The proof tracks the "displacement" `g_k` at the `k`-th visit of `x` to `w.W`: writing
`T^{n_k} x = (u_k k_k) • z₀` and `T^{n_k} y = (u'_k k'_k) • z₀` in the chart, the elements
`g_k = u'_k (k'_k k_k⁻¹) u_k⁻¹` (which send `T^{n_k}x` to `T^{n_k}y`) are conjugate by the powers
`T^{n_{k+1}-n_k}` (chart injectivity), so `g_k = a^{n_k-n_0} g_0 a^{-(n_k-n_0)}`; pinning along a
subsequence of visits of growing depth (`Window.hCsmall`) then places `g_0` in `Uminus t`
(`mem_uminus_of_shadowing_seq`).
-/

variable {μ : MeasureTheory.Measure X3} {t : Fin 3 → ℝ}

/-! ## The visit times of a point -/

/-- The times at which the `Tm t`-orbit of `x` meets `W`. -/
def visitPred (t : Fin 3 → ℝ) (W : Set X3) (x : X3) : ℕ → Prop :=
  fun n => (Tm t)^[n] x ∈ W

/-- The `k`-th visit time of `x` to `W` (the `k`-th element of `visitPred t W x`). -/
def visitTime (t : Fin 3 → ℝ) (W : Set X3) (x : X3) (k : ℕ) : ℕ :=
  Nat.nth (visitPred t W x) k

lemma visitTime_mem {t : Fin 3 → ℝ} {W : Set X3} {x : X3}
    (h : (Set.ofPred (visitPred t W x)).Infinite) (k : ℕ) :
    (Tm t)^[visitTime t W x k] x ∈ W :=
  Nat.nth_mem_of_infinite h k

lemma visitTime_strictMono {t : Fin 3 → ℝ} {W : Set X3} {x : X3}
    (h : (Set.ofPred (visitPred t W x)).Infinite) : StrictMono (visitTime t W x) :=
  Nat.nth_strictMono h

lemma visitTime_lt {t : Fin 3 → ℝ} {W : Set X3} {x : X3}
    (h : (Set.ofPred (visitPred t W x)).Infinite) {k l : ℕ} (hkl : k < l) :
    visitTime t W x k < visitTime t W x l :=
  (Nat.nth_lt_nth h).mpr hkl

lemma visitTime_zero_of_mem {t : Fin 3 → ℝ} {W : Set X3} {x : X3} (hx : x ∈ W) :
    visitTime t W x 0 = 0 :=
  Nat.nth_zero_of_zero hx

/-- No visit time lies strictly between two consecutive visit times. -/
lemma not_mem_between {t : Fin 3 → ℝ} {W : Set X3} {x : X3} {k m : ℕ}
    (hm : (Tm t)^[m] x ∈ W) (h1 : visitTime t W x k < m)
    (h2 : m < visitTime t W x (k + 1)) : False := by
  have h2' : m < Nat.nth (visitPred t W x) (k + 1) := h2
  have h1' : Nat.nth (visitPred t W x) k < m := h1
  have := Nat.le_nth_of_lt_nth_succ (p := visitPred t W x) h2' hm
  omega

/-- Any visit time strictly after the `k`-th visit is at least the `(k+1)`-st visit. -/
lemma next_visit_le {t : Fin 3 → ℝ} {W : Set X3} {x : X3} {k m : ℕ}
    (hm : (Tm t)^[m] x ∈ W) (h1 : visitTime t W x k < m) :
    visitTime t W x (k + 1) ≤ m := by
  by_contra h
  exact not_mem_between hm h1 (by omega)

lemma visitTime_succ_sub_pos {t : Fin 3 → ℝ} {W : Set X3} {x : X3}
    (h : (Set.ofPred (visitPred t W x)).Infinite) (k : ℕ) :
    1 ≤ visitTime t W x (k + 1) - visitTime t W x k := by
  have := visitTime_lt h (Nat.lt_succ_self k)
  simp only [Nat.succ_eq_add_one] at this
  omega

/-- At the `k`-th visit, the gap to the next visit is the first return time. -/
lemma firstReturn_gap {t : Fin 3 → ℝ} {W : Set X3} {x : X3}
    (h : (Set.ofPred (visitPred t W x)).Infinite) (k : ℕ) :
    (Tm t)^[visitTime t W x k + (visitTime t W x (k + 1) - visitTime t W x k)] x ∈ W ∧
      ∀ j : ℕ, 1 ≤ j → j < visitTime t W x (k + 1) - visitTime t W x k →
        (Tm t)^[visitTime t W x k + j] x ∉ W := by
  have hlt := visitTime_lt h (Nat.lt_succ_self k)
  simp only [Nat.succ_eq_add_one] at hlt
  have hsum : visitTime t W x k + (visitTime t W x (k + 1) - visitTime t W x k)
      = visitTime t W x (k + 1) := by omega
  refine ⟨?_, ?_⟩
  · rw [hsum]; exact visitTime_mem h (k + 1)
  · intro j hj hjlt
    intro hcon
    exact not_mem_between hcon (by omega) (by omega : visitTime t W x k + j < visitTime t W x (k+1))

/-- Iterates compose: `(Tm t)^[m] ((Tm t)^[n] x) = (Tm t)^[n + m] x`. -/
lemma iterate_apply_apply (n m : ℕ) (x : X3) :
    (Tm t)^[m] ((Tm t)^[n] x) = (Tm t)^[n + m] x := by
  rw [← Function.iterate_add_apply, Nat.add_comm]

/-! ## The atom of the past σ-algebra

The measurability hypothesis of `Work.EKLC6Geo.AtomPastSigIterateSubset` is not needed: the atom
of `σ (range S)` is characterised by agreement on the members of `S`. -/

lemma atom_pastSigSet_apply {t : Fin 3 → ℝ} {S : ℕ → Set X3} {x y : X3}
    (hy : y ∈ atom (pastSigSet t S) x) {n m : ℕ} (hx : (Tm t)^[n] x ∈ S m) :
    (Tm t)^[n] y ∈ S m := by
  have key : ∀ k : ℕ, (Tm t)^[k] y ∈
      atom (MeasurableSpace.generateFrom (Set.range S)) ((Tm t)^[k] x) := by
    intro k
    have h := hy
    rw [pastSigSet, atom_iSup_comap_iterate_eq (MeasurableSpace.generateFrom (Set.range S))
      (Tm t) x] at h
    exact h k
  exact ((mem_atom_iff.mp (key n)) (S m)
    (MeasurableSpace.measurableSet_generateFrom (Set.mem_range_self m))).1 hx

/-! ## The window and its coding pieces -/

lemma mem_W_facts {w : Window μ t} {z : X3} (hz : z ∈ w.W) :
    w.uc z ∈ Work.EKLComp.Uball (Uminus t) w.r ∧ w.θ z ∈ VtSet t ∩ V w.ρ ∧
      (w.uc z * w.θ z) • w.z0 = z := hz

lemma measurableSet_W (w : Window μ t) : MeasurableSet w.W :=
  chartSet_measurable (t := t) (z0 := w.z0) (uc := w.uc) (θ := w.θ) w.huc w.hθ w.r w.ρ

/-- Facts extracted from a membership in a `D`-piece: the return time is nonzero, the point lies
in the corresponding first-return set and `Jset`, and the grid label is `c`. -/
lemma mem_D_facts (w : Window μ t) {z : X3} {i : ℕ} {J : Option ℕ} {c : Fin 3 → Fin 3 → ℤ}
    (hz : z ∈ w.piece (some (some (i, J, c)))) :
    i ≠ 0 ∧ z ∈ firstReturnSet t w.W i ∧ z ∈ w.Jset J ∧
      gridIdx w.ρ (gridLev t i) (w.θ z) = c ∧ z ∉ w.N0 :=
  (w.mem_D).1 (by simpa only [Window.piece] using hz)

lemma theta_mem_C_of_mem_Jset (w : Window μ t) {z : X3} {j : ℕ} (hz : z ∈ w.Jset (some j)) :
    w.θ z ∈ w.C j := hz.2.1

lemma theta_mem_C_of_mem_Jset_none (w : Window μ t) {z : X3} (hz : z ∈ w.Jset none) (j : ℕ) :
    w.θ z ∈ w.C j := (Set.mem_iInter.1 hz.2) j

/-- If `θ z ∈ C j` and `z ∈ Jset (some j')`, then `j ≤ j'`. -/
lemma le_of_mem_Jset_some (w : Window μ t) {z : X3} {j j' : ℕ} (hz : z ∈ w.Jset (some j'))
    (hC : w.θ z ∈ w.C j) : j ≤ j' := by
  by_contra h
  have h1 : j' + 1 ≤ j := by omega
  exact hz.2.2 (w.hCanti h1 hC)

/-- **The depth bound.**  Two points whose `θ`-coordinates lie in the same `Jset J` have
`θ`-ratio in `V ((1/2)^d δ/100)`, provided `d` is at most the depth of `J`. -/
lemma ratio_mem_V (w : Window μ t) {z z' : X3} {J : Option ℕ} {d : ℕ}
    (hz : z ∈ w.Jset J) (hz' : z' ∈ w.Jset J) (hd : ∀ j, J = some j → d ≤ j) :
    w.θ z' * (w.θ z)⁻¹ ∈ V ((1 / 2 : ℝ) ^ d * w.δ / 100) := by
  rcases J with _ | j
  · exact w.hCsmall d _ (theta_mem_C_of_mem_Jset_none w hz d) _
      (theta_mem_C_of_mem_Jset_none w hz' d)
  · have hdj : d ≤ j := hd j rfl
    refine V_subset_of_le ?_ (w.hCsmall j _ (theta_mem_C_of_mem_Jset w hz) _
      (theta_mem_C_of_mem_Jset w hz'))
    have hp : (1 / 2 : ℝ) ^ j ≤ (1 / 2 : ℝ) ^ d :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) hdj
    have hδ : 0 ≤ w.δ / 100 := by linarith [w.hδ]
    nlinarith

/-- **The piece at a visit.**  At the `k`-th visit of `x` to `w.W`, the piece of the coding
partition that contains the visit has first-return time exactly the gap to the next visit, and
the `k`-th visit of `y` (for `y` in the past atom of `x`) lies in that same piece. -/
lemma visit_piece (w : Window μ t) {x y : X3}
    (hinf : (Set.ofPred (visitPred t w.W x)).Infinite)
    (hN0 : ∀ n, (Tm t)^[n] x ∉ w.N0) (hy : y ∈ atom w.A x) (k : ℕ) :
    ∃ (J : Option ℕ) (c : Fin 3 → Fin 3 → ℤ),
      (Tm t)^[visitTime t w.W x k] x ∈
        w.piece (some (some (visitTime t w.W x (k + 1) - visitTime t w.W x k, J, c))) ∧
      (Tm t)^[visitTime t w.W x k] y ∈
        w.piece (some (some (visitTime t w.W x (k + 1) - visitTime t w.W x k, J, c))) := by
  classical
  obtain ⟨i, J, c, hi1, hfr, hJset, hgrid, hpiece⟩ :=
    piece_mem_of_mem_W w (visitTime_mem hinf k) (hN0 _)
  -- unfold the first-return set at the visit
  have hfr' := (firstReturn_partition (t := t) (Ω := w.W) (measurableSet_W w)).2.2.2.2.1 i hi1
  rw [hfr', Set.mem_ofPred_eq] at hfr
  obtain ⟨hzW, hzi, hno⟩ := hfr
  -- the first return time at the visit is the gap to the next visit
  have hgap : i = visitTime t w.W x (k + 1) - visitTime t w.W x k := by
    have hmono := visitTime_lt hinf (Nat.lt_succ_self k)
    simp only [Nat.succ_eq_add_one] at hmono
    have hle : visitTime t w.W x (k + 1) - visitTime t w.W x k ≤ i := by
      have hvisit : (Tm t)^[visitTime t w.W x k + i] x ∈ w.W := by
        have := hzi
        rw [iterate_apply_apply] at this
        exact this
      have hgt : visitTime t w.W x k < visitTime t w.W x k + i := by omega
      have := next_visit_le hvisit hgt
      omega
    have hge : i ≤ visitTime t w.W x (k + 1) - visitTime t w.W x k := by
      by_contra h
      have h1 : 1 ≤ visitTime t w.W x (k + 1) - visitTime t w.W x k := by omega
      have h2 : visitTime t w.W x (k + 1) - visitTime t w.W x k < i := by omega
      have hno' := hno (visitTime t w.W x (k + 1) - visitTime t w.W x k) h1 h2
      rw [iterate_apply_apply] at hno'
      have heq : visitTime t w.W x k + (visitTime t w.W x (k + 1) - visitTime t w.W x k)
          = visitTime t w.W x (k + 1) := by omega
      rw [heq] at hno'
      exact hno' (visitTime_mem hinf (k + 1))
    omega
  subst hgap
  refine ⟨J, c, hpiece, ?_⟩
  obtain ⟨m, hm⟩ := S_surj w (some (some (visitTime t w.W x (k + 1) - visitTime t w.W x k, J, c)))
  have hxm : (Tm t)^[visitTime t w.W x k] x ∈ w.S m := by rw [hm]; exact hpiece
  have hym := atom_pastSigSet_apply (t := t) (S := w.S) (x := x) (y := y) hy hxm
  rwa [hm] at hym

/-! ## Tracking the displacement between the two orbits -/

/-- The displacement at the `k`-th visit: the element of `SL₃(ℝ)` which sends the `k`-th visit of
`x` to the `k`-th visit of `y`, read off from the chart coordinates. -/
def trackEl (w : Window μ t) (x y : X3) (k : ℕ) : SL3 :=
  w.uc ((Tm t)^[visitTime t w.W x k] y) *
    (w.θ ((Tm t)^[visitTime t w.W x k] y) * (w.θ ((Tm t)^[visitTime t w.W x k] x))⁻¹) *
    (w.uc ((Tm t)^[visitTime t w.W x k] x))⁻¹

lemma mem_W_of_mem_piece (w : Window μ t) {z : X3} {i : ℕ} {J : Option ℕ}
    {c : Fin 3 → Fin 3 → ℤ} (hz : z ∈ w.piece (some (some (i, J, c)))) : z ∈ w.W :=
  (mem_D_facts w hz).2.1.1.1

/-- Iterating `Tm t` from a visit: `(Tm t)^[m+n] x = aDiag t ^ n • ((Tm t)^[m] x)`. -/
lemma iterate_Tm_add (m n : ℕ) (x : X3) :
    (Tm t)^[m + n] x = aDiag t ^ n • ((Tm t)^[m] x) := by
  have h1 : (Tm t)^[m + n] x = aDiag t ^ (m + n) • x := by
    simpa using congrFun (smul_iterate (aDiag t) (m + n)) x
  have h2 : (Tm t)^[m] x = aDiag t ^ m • x := by
    simpa using congrFun (smul_iterate (aDiag t) m) x
  rw [h1, h2, ← mul_smul, ← pow_add, Nat.add_comm]

lemma smul_conj_pow (i : ℕ) (g : SL3) (z : X3) :
    (aDiag t ^ i * g * (aDiag t ^ i)⁻¹) • (aDiag t ^ i • z) = aDiag t ^ i • (g • z) := by
  rw [mul_smul, mul_smul, inv_smul_smul]

/-- The tracked displacement sends the `k`-th visit of `x` to the `k`-th visit of `y`. -/
lemma trackEl_smul (w : Window μ t) {x y : X3} {k : ℕ}
    (hx : (Tm t)^[visitTime t w.W x k] x ∈ w.W)
    (hy : (Tm t)^[visitTime t w.W x k] y ∈ w.W) :
    trackEl w x y k • ((Tm t)^[visitTime t w.W x k] x) = (Tm t)^[visitTime t w.W x k] y := by
  obtain ⟨-, -, hx'⟩ := mem_W_facts hx
  obtain ⟨-, -, hy'⟩ := mem_W_facts hy
  rw [← hx', ← hy']
  simp only [trackEl, mul_smul, inv_smul_smul, one_smul]

/-- **The tracked displacement is `V w.δ`-small.**  This is the three-factor estimate
`u' · (k' k⁻¹) · u⁻¹` of the route document, with the grid bound `k' k⁻¹ ∈ V (100 · 2^{-L} ρ)`
furnished by the coding partition. -/
lemma trackEl_mem_V (w : Window μ t) {x y : X3}
    (hinf : (Set.ofPred (visitPred t w.W x)).Infinite)
    (hN0 : ∀ n, (Tm t)^[n] x ∉ w.N0) (hy : y ∈ atom w.A x) (k : ℕ) :
    trackEl w x y k ∈ V w.δ := by
  obtain ⟨J, c, hpx, hpy⟩ := visit_piece w hinf hN0 hy k
  obtain ⟨-, -, -, hgx, -⟩ := mem_D_facts w hpx
  obtain ⟨-, -, -, hgy, -⟩ := mem_D_facts w hpy
  have hgrid : gridIdx w.ρ
        (gridLev t (visitTime t w.W x (k + 1) - visitTime t w.W x k))
        (w.θ ((Tm t)^[visitTime t w.W x k] x))
      = gridIdx w.ρ
        (gridLev t (visitTime t w.W x (k + 1) - visitTime t w.W x k))
        (w.θ ((Tm t)^[visitTime t w.W x k] y)) := by
    rw [hgx, hgy]
  exact track_mem_V w (mem_W_facts (visitTime_mem hinf k)).1 (mem_W_facts (mem_W_of_mem_piece w hpy)).1
    (mem_W_facts (visitTime_mem hinf k)).2.1 (mem_W_facts (mem_W_of_mem_piece w hpy)).2.1 hgrid

/-- **The tracking step.**  The displacement at the `(k+1)`-st visit is the displacement at the
`k`-th visit conjugated by the return time: both are `V w.δ`-small and both send the
`(k+1)`-st visit of `x` to the `(k+1)`-st visit of `y`, so chart injectivity identifies them. -/
lemma trackEl_step (w : Window μ t) {x y : X3}
    (hinf : (Set.ofPred (visitPred t w.W x)).Infinite)
    (hN0 : ∀ n, (Tm t)^[n] x ∉ w.N0) (hy : y ∈ atom w.A x) (k : ℕ) :
    trackEl w x y (k + 1) =
      aDiag t ^ (visitTime t w.W x (k + 1) - visitTime t w.W x k) *
        trackEl w x y k *
        (aDiag t ^ (visitTime t w.W x (k + 1) - visitTime t w.W x k))⁻¹ := by
  set i := visitTime t w.W x (k + 1) - visitTime t w.W x k with hi
  have hzW : (Tm t)^[visitTime t w.W x k] x ∈ w.W := visitTime_mem hinf k
  have hz1W : (Tm t)^[visitTime t w.W x (k + 1)] x ∈ w.W := visitTime_mem hinf (k + 1)
  obtain ⟨J, c, hpx, hpy⟩ := visit_piece w hinf hN0 hy k
  obtain ⟨J₁, c₁, hp1x, hp1y⟩ := visit_piece w hinf hN0 hy (k + 1)
  have hzyW : (Tm t)^[visitTime t w.W x k] y ∈ w.W := mem_W_of_mem_piece w hpy
  have hz1yW : (Tm t)^[visitTime t w.W x (k + 1)] y ∈ w.W := mem_W_of_mem_piece w hp1y
  have hg : trackEl w x y k • ((Tm t)^[visitTime t w.W x k] x) =
      (Tm t)^[visitTime t w.W x k] y := trackEl_smul w hzW hzyW
  have hg1 : trackEl w x y (k + 1) • ((Tm t)^[visitTime t w.W x (k + 1)] x) =
      (Tm t)^[visitTime t w.W x (k + 1)] y := trackEl_smul w hz1W hz1yW
  -- the conjugate is small
  have hstep : aDiag t ^ i * trackEl w x y k * (aDiag t ^ i)⁻¹ ∈ V w.δ := by
    obtain ⟨-, -, -, hgx, -⟩ := mem_D_facts w hpx
    obtain ⟨-, -, -, hgy, -⟩ := mem_D_facts w hpy
    have hgrid : gridIdx w.ρ (gridLev t i) (w.θ ((Tm t)^[visitTime t w.W x k] x))
        = gridIdx w.ρ (gridLev t i) (w.θ ((Tm t)^[visitTime t w.W x k] y)) := by
      rw [hgx, hgy]
    have hLev : (1 / 2 : ℝ) ^ gridLev t i * Real.exp ((i : ℝ) * betaExp t) ≤ 1 := by
      rw [hi]
      exact gridLev_mul_exp_le_one t (visitTime t w.W x (k + 1) - visitTime t w.W x k)
    exact track_conj_mem_V w (mem_W_facts hzW).1 (mem_W_facts hzyW).1
      (mem_W_facts hzW).2.1 (mem_W_facts hzyW).2.1 hgrid hLev
  -- the two elements agree at the next visit
  have hle1 : visitTime t w.W x k ≤ visitTime t w.W x (k + 1) := by
    have := visitTime_lt hinf (Nat.lt_succ_self k)
    simp only [Nat.succ_eq_add_one] at this
    exact this.le
  have hsum1 : visitTime t w.W x (k + 1) = visitTime t w.W x k + i := by
    rw [hi]; omega
  have hz1eq : (Tm t)^[visitTime t w.W x (k + 1)] x =
      aDiag t ^ i • ((Tm t)^[visitTime t w.W x k] x) := by
    rw [hsum1, iterate_Tm_add]
  have hz1yeq : (Tm t)^[visitTime t w.W x (k + 1)] y =
      aDiag t ^ i • ((Tm t)^[visitTime t w.W x k] y) := by
    rw [hsum1, iterate_Tm_add]
  have heq : (aDiag t ^ i * trackEl w x y k * (aDiag t ^ i)⁻¹)
        • ((Tm t)^[visitTime t w.W x (k + 1)] x)
      = trackEl w x y (k + 1) • ((Tm t)^[visitTime t w.W x (k + 1)] x) := by
    simp only [hz1eq]
    rw [smul_conj_pow, hg, ← hz1yeq, ← hz1eq]
    exact hg1.symm
  exact (eq_of_mem_V_of_smul_eq w hz1W hstep
    (trackEl_mem_V w hinf hN0 hy (k + 1)) heq).symm

/-- **The tracked displacement is conjugate to the one at the first visit.** -/
lemma trackEl_eq (w : Window μ t) {x y : X3}
    (hinf : (Set.ofPred (visitPred t w.W x)).Infinite)
    (hN0 : ∀ n, (Tm t)^[n] x ∉ w.N0) (hy : y ∈ atom w.A x) (k : ℕ) :
    trackEl w x y k =
      aDiag t ^ (visitTime t w.W x k - visitTime t w.W x 0) * trackEl w x y 0 *
        (aDiag t ^ (visitTime t w.W x k - visitTime t w.W x 0))⁻¹ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [trackEl_step w hinf hN0 hy k, ih]
    have h0k : visitTime t w.W x 0 ≤ visitTime t w.W x k :=
      Nat.nth_monotone hinf (Nat.zero_le k)
    have hkk : visitTime t w.W x k ≤ visitTime t w.W x (k + 1) := by
      have := visitTime_lt hinf (Nat.lt_succ_self k)
      simp only [Nat.succ_eq_add_one] at this
      exact this.le
    have hexp : visitTime t w.W x (k + 1) - visitTime t w.W x 0
        = (visitTime t w.W x k - visitTime t w.W x 0)
          + (visitTime t w.W x (k + 1) - visitTime t w.W x k) := by omega
    rw [hexp, pow_add]
    group


/-! ## Pinning: the displacement at the first visit lies in `Uminus t` -/

/-- **Pinning.**  Along a subsequence of visits of growing depth the conjugates
`a^{N_k} g_0 a^{-N_k} = u'_k w_k u_k⁻¹` split as `(u'_k u_k⁻¹) · (u_k w_k u_k⁻¹)`, with the first
factor in `Uminus t ∩ V R` and the second entrywise tending to `1`; the shadowing lemma
`mem_uminus_of_shadowing_seq` then places `g_0` in `Uminus t`. -/
lemma trackEl_zero_mem_uminus (w : Window μ t) {x y : X3}
    (hvis : ∀ j : ℕ, ∃ᶠ n in Filter.atTop,
      (Tm t)^[n] x ∈ w.W ∩ w.θ ⁻¹' w.C j)
    (hN0 : ∀ n, (Tm t)^[n] x ∉ w.N0) (hy : y ∈ atom w.A x) :
    trackEl w x y 0 ∈ Uminus t := by
  classical
  have hinf : (Set.ofPred (visitPred t w.W x)).Infinite :=
    Set.infinite_of_forall_exists_gt fun a => by
      obtain ⟨b, hab, hb⟩ := Filter.frequently_atTop.mp (hvis 0) (a + 1)
      exact ⟨b, hb.1, by omega⟩
  -- infinitely many visits lie at depth `≥ k`
  have hex : ∀ k b : ℕ, ∃ m, b < m ∧ w.θ ((Tm t)^[visitTime t w.W x m] x) ∈ w.C k := by
    intro k b
    obtain ⟨n, hn_ge, hn_mem⟩ :=
      Filter.frequently_atTop.mp (hvis k) (visitTime t w.W x (b + 1))
    have hp : visitPred t w.W x n := hn_mem.1
    refine ⟨Nat.count (visitPred t w.W x) n, ?_, ?_⟩
    · refine Nat.lt_of_not_le fun hle => ?_
      have h2 : n ≤ visitTime t w.W x b := (Nat.count_le_iff_le_nth hinf).1 hle
      have h3 : visitTime t w.W x b < visitTime t w.W x (b + 1) := by
        have := visitTime_lt hinf (Nat.lt_succ_self b)
        simpa [Nat.succ_eq_add_one] using this
      omega
    · have heq : visitTime t w.W x (Nat.count (visitPred t w.W x) n) = n := Nat.nth_count hp
      rw [heq]
      exact hn_mem.2
  -- the greedy subsequence of visits, the `k`-th one at depth `≥ k`
  set σ : ℕ → ℕ := fun K => Nat.rec (Nat.find (hex 0 0))
    (fun k prev => Nat.find (hex (k + 1) prev)) K with hσ
  have hσ_zero : σ 0 = Nat.find (hex 0 0) := rfl
  have hσ_succ : ∀ k, σ (k + 1) = Nat.find (hex (k + 1) (σ k)) := fun k => rfl
  have hgood : ∀ k, w.θ ((Tm t)^[visitTime t w.W x (σ k)] x) ∈ w.C k := by
    intro k
    cases k with
    | zero => rw [hσ_zero]; exact (Nat.find_spec (hex 0 0)).2
    | succ k => rw [hσ_succ]; exact (Nat.find_spec (hex (k + 1) (σ k))).2
  have hlt_succ : ∀ k, σ k < σ (k + 1) := by
    intro k
    rw [hσ_succ]
    exact (Nat.find_spec (hex (k + 1) (σ k))).1
  have hσmono : StrictMono σ := strictMono_nat_of_lt_succ hlt_succ
  -- the ratio bound along the subsequence
  have hratio : ∀ k, w.θ ((Tm t)^[visitTime t w.W x (σ k)] y) *
      (w.θ ((Tm t)^[visitTime t w.W x (σ k)] x))⁻¹ ∈
      V ((1 / 2 : ℝ) ^ k * w.δ / 100) := by
    intro k
    obtain ⟨J, c, hpx, hpy⟩ := visit_piece w hinf hN0 hy (σ k)
    obtain ⟨-, -, hJx, -, -⟩ := mem_D_facts w hpx
    refine ratio_mem_V w hJx (mem_D_facts w hpy).2.2.1 (fun j hj => ?_)
    rw [hj] at hJx
    exact le_of_mem_Jset_some w hJx (hgood k)
  -- the `y`-visits lie in the window
  have hyW : ∀ k, (Tm t)^[visitTime t w.W x (σ k)] y ∈ w.W := by
    intro k
    obtain ⟨J, c, hpx, hpy⟩ := visit_piece w hinf hN0 hy (σ k)
    exact mem_W_of_mem_piece w hpy
  -- the sequence of exponents tends to infinity
  have hNmono : StrictMono (fun m => visitTime t w.W x m - visitTime t w.W x 0) := by
    intro a b hab
    have ha : visitTime t w.W x 0 ≤ visitTime t w.W x a := Nat.nth_monotone hinf (Nat.zero_le a)
    exact Nat.sub_lt_sub_right ha (visitTime_lt hinf hab)
  have hφ : Tendsto (fun k => visitTime t w.W x (σ k) - visitTime t w.W x 0) atTop atTop :=
    hNmono.tendsto_atTop.comp hσmono.tendsto_atTop
  -- the `θ`-ratios tend to `1`
  have hwtend : Tendsto (fun k => w.θ ((Tm t)^[visitTime t w.W x (σ k)] y) *
      (w.θ ((Tm t)^[visitTime t w.W x (σ k)] x))⁻¹) atTop (nhds 1) := by
    refine Work.EKLC6Core.tendsto_of_mem_V ?_ hratio
    have hpow : Tendsto (fun k : ℕ => (1 / 2 : ℝ) ^ k) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    simpa only [mul_assoc, div_eq_mul_inv, zero_mul] using (hpow.mul_const (w.δ / 100))
  -- the `V 1`-bound on the chart coordinates of the visits
  have hu1 : ∀ k, w.uc ((Tm t)^[visitTime t w.W x (σ k)] x) ∈ V 1 := by
    intro k
    have h := (mem_W_facts (visitTime_mem hinf (σ k))).1
    refine fun i j => lt_of_lt_of_le (h.2 i j) ?_
    linarith [w.hrδ, w.hδ1]
  obtain ⟨ε, C, hεt, hεnn, hCpos, hεb, hCb⟩ := conj_rate_and_bound hu1 hwtend
  -- the pinning lemma
  refine mem_uminus_of_shadowing_seq (t := t) (g := trackEl w x y 0)
    (φ := fun k => visitTime t w.W x (σ k) - visitTime t w.W x 0)
    (ε := ε) (R := 50 * w.r) hφ hεt (by linarith [w.hr]) ?_ ?_
  · -- the conjugates are bounded
    refine ⟨2, fun k i j => ?_⟩
    have heq : aDiag t ^ (visitTime t w.W x (σ k) - visitTime t w.W x 0) * trackEl w x y 0 *
        (aDiag t ^ (visitTime t w.W x (σ k) - visitTime t w.W x 0))⁻¹
        = trackEl w x y (σ k) := (trackEl_eq w hinf hN0 hy (σ k)).symm
    rw [heq]
    have h := (trackEl_mem_V w hinf hN0 hy (σ k)) i j
    have h1 : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
      rw [Matrix.one_apply]; split <;> norm_num
    calc |(trackEl w x y (σ k) : Matrix (Fin 3) (Fin 3) ℝ) i j|
        = |((trackEl w x y (σ k) : Matrix (Fin 3) (Fin 3) ℝ) i j
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) + (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by
          rw [sub_add_cancel]
      _ ≤ |(trackEl w x y (σ k) : Matrix (Fin 3) (Fin 3) ℝ) i j
            - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| :=
          abs_add_le _ _
      _ ≤ 2 := by
          have hδ1 : w.δ ≤ 1 := by linarith [w.hδ1]
          linarith [le_of_lt h, h1]
  · -- the factorisation
    intro k
    have huzU : w.uc ((Tm t)^[visitTime t w.W x (σ k)] x) ∈ Uminus t :=
      (mem_W_facts (visitTime_mem hinf (σ k))).1.1
    have huz'U : w.uc ((Tm t)^[visitTime t w.W x (σ k)] y) ∈ Uminus t :=
      (mem_W_facts (hyW k)).1.1
    refine ⟨w.uc ((Tm t)^[visitTime t w.W x (σ k)] y) *
        (w.uc ((Tm t)^[visitTime t w.W x (σ k)] x))⁻¹,
      mul_mem huz'U (Subgroup.inv_mem _ huzU), ?_,
      w.uc ((Tm t)^[visitTime t w.W x (σ k)] x) *
        (w.θ ((Tm t)^[visitTime t w.W x (σ k)] y) *
          (w.θ ((Tm t)^[visitTime t w.W x (σ k)] x))⁻¹) *
        (w.uc ((Tm t)^[visitTime t w.W x (σ k)] x))⁻¹, ?_, ?_⟩
    · -- membership in `V R`
      have huz : w.uc ((Tm t)^[visitTime t w.W x (σ k)] x) ∈ V w.r :=
        (mem_W_facts (visitTime_mem hinf (σ k))).1.2
      have huz' : w.uc ((Tm t)^[visitTime t w.W x (σ k)] y) ∈ V w.r :=
        (mem_W_facts (hyW k)).1.2
      have hinv : (w.uc ((Tm t)^[visitTime t w.W x (σ k)] x))⁻¹ ∈ V (10 * w.r) :=
        Work.EKLComp.inv_mem_V w.hr (by linarith [w.hrδ, w.hδ1]) huz
      have hdev1 : dev (w.uc ((Tm t)^[visitTime t w.W x (σ k)] y)) < w.r :=
        (mem_V_iff_dev_lt _ _).1 huz'
      have hdev2 : dev ((w.uc ((Tm t)^[visitTime t w.W x (σ k)] x))⁻¹) < 10 * w.r :=
        (mem_V_iff_dev_lt _ _).1 hinv
      have hmul := dev_mul_le (w.uc ((Tm t)^[visitTime t w.W x (σ k)] y))
        ((w.uc ((Tm t)^[visitTime t w.W x (σ k)] x))⁻¹)
      rw [mem_V_iff_dev_lt]
      have hr1 : w.r ≤ 1 := by linarith [w.hrδ, w.hδ1]
      have hd1 : 0 ≤ dev (w.uc ((Tm t)^[visitTime t w.W x (σ k)] y)) :=
        le_trans (abs_nonneg _) (abs_dev_entry _ 0 0)
      have hd2 : 0 ≤ dev ((w.uc ((Tm t)^[visitTime t w.W x (σ k)] x))⁻¹) :=
        le_trans (abs_nonneg _) (abs_dev_entry _ 0 0)
      nlinarith [w.hr, hr1, hmul, hdev1, hdev2, hd1, hd2]
    · -- entrywise closeness to `1`
      exact hεb k
    · -- the factorisation identity
      rw [← trackEl_eq w hinf hN0 hy (σ k)]
      simp only [trackEl]
      group


/-! ## The atomic conclusion -/

/-- **Every point of the past atom is a `Uminus t`-translate of `x`**, with an explicit entrywise
bound: `y = u • x` for `u = a^{-n₀} g₀ a^{n₀}`, the displacement at the first visit conjugated
back to time `0`. -/
lemma exists_uminus_smul_of_mem_atom (w : Window μ t) {x y : X3}
    (hvis : ∀ j : ℕ, ∃ᶠ n in Filter.atTop,
      (Tm t)^[n] x ∈ w.W ∩ w.θ ⁻¹' w.C j)
    (hN0 : ∀ n, (Tm t)^[n] x ∉ w.N0) (hy : y ∈ atom w.A x) :
    ∃ u ∈ Uminus t, y = u • x ∧
      ∀ i j : Fin 3, |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤
        2 * Real.exp (betaExp t * (visitTime t w.W x 0 : ℝ)) := by
  classical
  have hinf : (Set.ofPred (visitPred t w.W x)).Infinite :=
    Set.infinite_of_forall_exists_gt fun a => by
      obtain ⟨b, hab, hb⟩ := Filter.frequently_atTop.mp (hvis 0) (a + 1)
      exact ⟨b, hb.1, by omega⟩
  have hgU : trackEl w x y 0 ∈ Uminus t := trackEl_zero_mem_uminus w hvis hN0 hy
  have hgV : trackEl w x y 0 ∈ V w.δ := trackEl_mem_V w hinf hN0 hy 0
  -- the `y`-visit at the first visit time lies in `w.W`
  have hy0W : (Tm t)^[visitTime t w.W x 0] y ∈ w.W := by
    obtain ⟨J, c, hpx, hpy⟩ := visit_piece w hinf hN0 hy 0
    exact mem_W_of_mem_piece w hpy
  -- the displacement carries the first visit of `x` to the first visit of `y`
  have hg := trackEl_smul w (visitTime_mem hinf 0) hy0W
  have hx0 : (Tm t)^[visitTime t w.W x 0] x = aDiag t ^ visitTime t w.W x 0 • x := by
    simpa using congrFun (smul_iterate (aDiag t) (visitTime t w.W x 0)) x
  have hy0 : (Tm t)^[visitTime t w.W x 0] y = aDiag t ^ visitTime t w.W x 0 • y := by
    simpa using congrFun (smul_iterate (aDiag t) (visitTime t w.W x 0)) y
  rw [hx0, hy0] at hg
  -- the conjugated displacement is again in `Uminus t` (conjugation by a diagonal keeps it)
  have hmem : (aDiag t ^ visitTime t w.W x 0)⁻¹ * trackEl w x y 0 * aDiag t ^ visitTime t w.W x 0
      ∈ Uminus t := by
    have hs : aDiag (-(visitTime t w.W x 0 • t)) = (aDiag t ^ visitTime t w.W x 0)⁻¹ := by
      rw [← Work.EKLProd.aDiag_nsmul t (visitTime t w.W x 0)]
      exact (inv_eq_of_mul_eq_one_left
        (Work.EKLContract.aDiag_neg_mul (visitTime t w.W x 0 • t))).symm
    have h := (uminus_isHoro t).1.2.1 (-(visitTime t w.W x 0 • t)) (trackEl w x y 0) hgU
    rwa [hs, inv_inv] at h
  refine ⟨(aDiag t ^ visitTime t w.W x 0)⁻¹ * trackEl w x y 0 * aDiag t ^ visitTime t w.W x 0,
    hmem, ?_, ?_⟩
  · -- `y = u • x`
    rw [mul_smul, mul_smul, hg, inv_smul_smul]
  · -- the entrywise bound
    intro i j
    rw [Work.EKLC6Core.boxi_conj_pow_apply_inv, abs_mul, abs_of_pos (Real.exp_pos _)]
    have hle : t j - t i ≤ betaExp t :=
      le_trans (le_abs_self _)
        (Finset.le_sup' (s := Finset.univ) (f := fun p : Fin 3 × Fin 3 => |t p.1 - t p.2|)
          (Finset.mem_univ (j, i)))
    have hexp : Real.exp ((visitTime t w.W x 0 : ℝ) * (t j - t i)) ≤
        Real.exp (betaExp t * (visitTime t w.W x 0 : ℝ)) := by
      refine Real.exp_le_exp.mpr ?_
      have h : (visitTime t w.W x 0 : ℝ) * (t j - t i) ≤
          (visitTime t w.W x 0 : ℝ) * betaExp t :=
        mul_le_mul_of_nonneg_left hle (Nat.cast_nonneg _)
      linarith [h]
    have hg2 : |(trackEl w x y 0 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 2 := by
      have h := hgV i j
      have h1 : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
        rw [Matrix.one_apply]; split <;> norm_num
      have hδ1 : w.δ ≤ 1 := by linarith [w.hδ1]
      calc |(trackEl w x y 0 : Matrix (Fin 3) (Fin 3) ℝ) i j|
          = |((trackEl w x y 0 : Matrix (Fin 3) (Fin 3) ℝ) i j
              - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j) + (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by
            rw [sub_add_cancel]
        _ ≤ |(trackEl w x y 0 : Matrix (Fin 3) (Fin 3) ℝ) i j
              - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| :=
            abs_add_le _ _
        _ ≤ 2 := by linarith [le_of_lt h, h1, hδ1]
    calc Real.exp ((visitTime t w.W x 0 : ℝ) * (t j - t i)) *
          |(trackEl w x y 0 : Matrix (Fin 3) (Fin 3) ℝ) i j|
        ≤ Real.exp (betaExp t * (visitTime t w.W x 0 : ℝ)) * 2 :=
          mul_le_mul hexp hg2 (abs_nonneg _) (Real.exp_pos _).le
      _ = 2 * Real.exp (betaExp t * (visitTime t w.W x 0 : ℝ)) := by ring

/-- The action of `Uminus t` is **free** at a point whose orbit visits `w.W` at arbitrarily large
times: for `v ∈ Uminus t` with `v • x = x`, the conjugate `a^n v a^{-n}` is `V w.δ`-close to `1`
for all large `n` (`Work.EKLC6Core.uminus_isHoro`) and fixes the visit `T^n x`, so chart
injectivity forces it to be `1`. -/
lemma eq_one_of_mem_uminus_of_smul_eq (w : Window μ t) {x : X3}
    (hvis : ∀ j : ℕ, ∃ᶠ n in Filter.atTop,
      (Tm t)^[n] x ∈ w.W ∩ w.θ ⁻¹' w.C j)
    {v : SL3} (hv : v ∈ Uminus t) (hfix : v • x = x) : v = 1 := by
  have hVopen : V w.δ ∈ nhds (1 : SL3) :=
    (Work.EKLContract.Lemmas.V_open_one w.δ w.hδ).1.mem_nhds
      (Work.EKLContract.Lemmas.V_open_one w.δ w.hδ).2
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (((uminus_isHoro t).2 v hv).eventually hVopen)
  obtain ⟨n, hnN, hnvis⟩ := Filter.frequently_atTop.mp (hvis 0) N
  have hfixn : (aDiag t ^ n * v * (aDiag t ^ n)⁻¹) • ((Tm t)^[n] x) = (Tm t)^[n] x := by
    have hx : (Tm t)^[n] x = aDiag t ^ n • x := by
      simpa using congrFun (smul_iterate (aDiag t) n) x
    rw [hx, mul_smul, mul_smul, inv_smul_smul, hfix, ← hx]
  have h1 : aDiag t ^ n * v * (aDiag t ^ n)⁻¹ = 1 :=
    eq_of_mem_V_of_smul_eq w hnvis.1 (hN n hnN)
      (Work.EKLContract.Lemmas.V_open_one w.δ w.hδ).2 (by rw [one_smul]; exact hfixn)
  calc v = (aDiag t ^ n)⁻¹ * (aDiag t ^ n * v * (aDiag t ^ n)⁻¹) * aDiag t ^ n := by group
    _ = (aDiag t ^ n)⁻¹ * 1 * aDiag t ^ n := by rw [h1]
    _ = 1 := by group

/-! ## The requested lemma -/

theorem atom_subset_uminus {μ : MeasureTheory.Measure Work.EKLContract.X3}
    [MeasureTheory.IsProbabilityMeasure μ] {t : Fin 3 → ℝ} (w : Work.EKLC6Route.Window μ t)
    {x : Work.EKLContract.X3}
    (hvis : ∀ j : ℕ, ∃ᶠ n in Filter.atTop,
      (Work.EKLC6Route.Tm t)^[n] x ∈ w.W ∩ w.θ ⁻¹' w.C j)
    (hN0 : ∀ n, (Work.EKLC6Route.Tm t)^[n] x ∉ w.N0) :
    ∃ C : ℝ, (x ∈ w.W → C = 2) ∧
      (∀ y ∈ Work.EKLContract.atom w.A x, ∃ u ∈ Work.EKLC6Core.Uminus t, y = u • x ∧
          ∀ i j : Fin 3, |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C) ∧
      (∀ u ∈ Work.EKLC6Core.Uminus t, u • x ∈ Work.EKLContract.atom w.A x →
          ∀ i j : Fin 3, |(u : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ C) := by
  classical
  refine ⟨2 * Real.exp (betaExp t * (visitTime t w.W x 0 : ℝ)), ?_, ?_, ?_⟩
  · intro hxW
    rw [visitTime_zero_of_mem hxW, Nat.cast_zero, mul_zero, Real.exp_zero, mul_one]
  · intro y hy
    exact exists_uminus_smul_of_mem_atom w hvis hN0 hy
  · intro u hu hmem
    obtain ⟨u', hu', heq, hbd⟩ := exists_uminus_smul_of_mem_atom w hvis hN0 hmem
    have hmul : u'⁻¹ * u ∈ Uminus t := Subgroup.mul_mem _ (Subgroup.inv_mem _ hu') hu
    have hfix : (u'⁻¹ * u) • x = x := by
      rw [mul_smul, heq, inv_smul_smul]
    have hone : u'⁻¹ * u = 1 := eq_one_of_mem_uminus_of_smul_eq w hvis hmul hfix
    have hueq : u = u' := by
      calc u = u' * (u'⁻¹ * u) := by group
        _ = u' * 1 := by rw [hone]
        _ = u' := by rw [mul_one]
    rw [hueq]
    exact hbd

end Work.EKLC6Route
