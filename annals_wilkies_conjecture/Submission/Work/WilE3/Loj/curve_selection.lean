import Submission.Work.WilC4aCS.CurveSelStep
import Submission.Work.WilC4aRW.Main
import Submission.Work.WilC4aAL.Main
import Submission.Work.WilC4aP.Main
import Submission.Work.WilC4aTS.TS

set_option autoImplicit false

namespace Work.WilE3.Loj

open scoped Topology

/-- Curve selection in every dimension, assembled from the four C4a inputs: simultaneous real
Weierstrass preparation (`C4a_RW_proved`), real Puiseux (`C4a_puiseux_proved`), the lifting of sign
conditions over an arc (`C4a_arcLift_proved`) and Tarski--Seidenberg for one projection
(`C4a_TS1_proved`). -/
theorem curveSel_full : ∀ n, WilkiesDesign.CG.C4a.CurveSel n :=
  Work.WilC4aCS.curveSel_all WilkiesDesign.CG.C4a.C4a_RW_proved
    (Work.WilC4aAL.C4a_arcLift_proved WilkiesDesign.CG.C4a.C4a_puiseux_proved)
    Work.WilC4aTS.C4a_TS1_proved

/-- Some coordinate of `x - y` realises the sup-distance `dist x y`. -/
lemma exists_dist_eq_coord {k : ℕ} (hk : 0 < k) (x y : Fin k → ℝ) :
    ∃ i : Fin k, dist x y = |x i - y i| := by
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin k)) hne
      (fun b => ‖(x - y) b‖₊)
  refine ⟨i, ?_⟩
  rw [dist_eq_norm, Pi.norm_def, hi, coe_nnnorm, Pi.sub_apply, Real.norm_eq_abs]

/-- `a ^ (2 * q) = (|a| ^ q) ^ 2`. -/
lemma pow_two_mul_abs (a : ℝ) (q : ℕ) : a ^ (2 * q) = (|a| ^ q) ^ 2 := by
  have h1 : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
  calc a ^ (2 * q) = (a ^ 2) ^ q := pow_mul a 2 q
    _ = (|a| ^ 2) ^ q := by rw [h1]
    _ = |a| ^ (2 * q) := (pow_mul |a| 2 q).symm
    _ = |a| ^ (q * 2) := by rw [mul_comm]
    _ = (|a| ^ q) ^ 2 := pow_mul |a| q 2

/-- `0 < (xᵢ − yᵢ)^{2q} − 4 Φ(x)²` forces `2 |Φ(x)| < |xᵢ − yᵢ|^q`. -/
lemma two_abs_Phi_lt_of_pos {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {y x : Fin k → ℝ} {q : ℕ} {i : Fin k}
    (h : 0 < (x i - y i) ^ (2 * q) - 4 * (Φ x) ^ 2) :
    2 * |Φ x| < |x i - y i| ^ q := by
  have hgx : 4 * (Φ x) ^ 2 < (x i - y i) ^ (2 * q) := by linarith
  have h4 : (2 * |Φ x|) ^ 2 = 4 * (Φ x) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
  have hsq : (2 * |Φ x|) ^ 2 < (|x i - y i| ^ q) ^ 2 := by
    rw [h4, ← pow_two_mul_abs (x i - y i) q]; exact hgx
  have h2 := sq_lt_sq.mp hsq
  rwa [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * |Φ x|),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ |x i - y i| ^ q)] at h2

/-- `2 |Φ(x)| < |xᵢ − yᵢ|^q` forces `0 < (xᵢ − yᵢ)^{2q} − 4 Φ(x)²`. -/
lemma pos_of_two_abs_Phi_lt {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} {y x : Fin k → ℝ} {q : ℕ} {i : Fin k}
    (h : 2 * |Φ x| < |x i - y i| ^ q) :
    0 < (x i - y i) ^ (2 * q) - 4 * (Φ x) ^ 2 := by
  have hsq : (2 * |Φ x|) ^ 2 < (|x i - y i| ^ q) ^ 2 :=
    pow_lt_pow_left₀ h (by positivity : (0 : ℝ) ≤ 2 * |Φ x|) (by norm_num : (2 : ℕ) ≠ 0)
  have h4 : (2 * |Φ x|) ^ 2 = 4 * (Φ x) ^ 2 := by rw [mul_pow, sq_abs]; norm_num
  have hle : 4 * (Φ x) ^ 2 < (x i - y i) ^ (2 * q) := by
    rw [← h4, pow_two_mul_abs (x i - y i) q]; exact hsq
  linarith

/-- Curve selection (Łojasiewicz) for the "bad" set of a real analytic function: if points
arbitrarily close to `y` (other than `y`) satisfy `2 * |Φ x| < dist x y ^ q`, then there is a real
analytic arc through `y` along which the same strict inequality holds for all small `t > 0`. -/
theorem curve_selection {k : ℕ} {Φ : (Fin k → ℝ) → ℝ} (hΦ : ∀ x, AnalyticAt ℝ Φ x)
    (y : Fin k → ℝ) (hy : Φ y = 0) (q : ℕ)
    (hseq : ∀ n : ℕ, ∃ x : Fin k → ℝ, x ≠ y ∧ dist x y < 1 / (n + 1) ∧
      2 * |Φ x| < dist x y ^ q) :
    ∃ γ : ℝ → Fin k → ℝ, AnalyticAt ℝ γ 0 ∧ γ 0 = y ∧
      (∀ᶠ t in 𝓝[>] (0 : ℝ), γ t ≠ y ∧ 2 * |Φ (γ t)| < dist (γ t) y ^ q) := by
  cases k with
  | zero =>
      obtain ⟨x, hx, _⟩ := hseq 0
      have hxy : x = y := funext (fun i : Fin 0 => Fin.elim0 i)
      exact absurd hxy hx
  | succ m =>
      let gfun : Fin (m + 1) → (Fin (m + 1) → ℝ) → ℝ :=
        fun i x => (x i - y i) ^ (2 * q) - 4 * (Φ x) ^ 2
      let A : Fin (m + 1) → Set (Fin (m + 1) → ℝ) :=
        fun i => WilkiesDesign.CG.C4a.BasicSA (fun _ : Fin (m + 1) → ℝ => 0)
          (fun _ : Fin 1 => gfun i)
      have hgan : ∀ i : Fin (m + 1), AnalyticAt ℝ (gfun i) y := by
        intro i
        have hcoord : AnalyticAt ℝ (fun x : Fin (m + 1) → ℝ => x i) y := by
          have h := ContinuousLinearMap.analyticAt
            (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin (m + 1) => ℝ) i) y
          refine h.congr ?_
          filter_upwards with x
          exact ContinuousLinearMap.proj_apply i x
        have h2 : AnalyticAt ℝ (fun x : Fin (m + 1) → ℝ => x i - y i) y :=
          hcoord.sub (analyticAt_const (v := y i))
        have h1 : AnalyticAt ℝ (fun x : Fin (m + 1) → ℝ => (x i - y i) ^ (2 * q)) y :=
          h2.pow (2 * q)
        have h3 : AnalyticAt ℝ (fun x : Fin (m + 1) → ℝ => 4 * (Φ x) ^ 2) y :=
          (analyticAt_const (v := (4 : ℝ))).mul ((hΦ y).pow 2)
        show AnalyticAt ℝ (fun x : Fin (m + 1) → ℝ => (x i - y i) ^ (2 * q)
          - 4 * (Φ x) ^ 2) y
        exact h1.sub h3
      have memA : ∀ (i : Fin (m + 1)) (z : Fin (m + 1) → ℝ), z ∈ A i ↔ 0 < gfun i z := by
        intro i z
        simp [A, WilkiesDesign.CG.C4a.BasicSA]
      have hmem_target : ∀ x : Fin (m + 1) → ℝ, 2 * |Φ x| < dist x y ^ q → x ∈ ⋃ i, A i := by
        intro x hx
        obtain ⟨i, hi⟩ := exists_dist_eq_coord (Nat.succ_pos m) x y
        refine Set.mem_iUnion.mpr ⟨i, ?_⟩
        rw [memA]
        exact pos_of_two_abs_Phi_lt (i := i) (by rwa [hi] at hx)
      have hA_sub : ∀ i : Fin (m + 1), A i ⊆ {x | 2 * |Φ x| < dist x y ^ q} := by
        intro i x hx
        rw [memA] at hx
        have hlt := two_abs_Phi_lt_of_pos (i := i) hx
        have hle : |x i - y i| ^ q ≤ dist x y ^ q := by
          have hd : |x i - y i| ≤ dist x y := by
            simpa [dist_eq_norm, Real.norm_eq_abs, Pi.sub_apply] using norm_le_pi_norm (x - y) i
          exact pow_le_pow_left₀ (abs_nonneg _) hd q
        exact lt_of_lt_of_le hlt hle
      by_cases hq0 : q = 0
      · -- `q = 0`: the straight line into a ball on which `2 |Φ| < 1`
        let i0 : Fin (m + 1) := ⟨0, Nat.succ_pos m⟩
        let e : Fin (m + 1) → ℝ := Pi.single i0 (1 : ℝ)
        refine ⟨fun t : ℝ => t • e + y, ?_, ?_, ?_⟩
        · exact ((analyticAt_id : AnalyticAt ℝ (fun t : ℝ => t) 0).smul analyticAt_const).add
            analyticAt_const
        · simp
        · have hγc : ContinuousAt (fun t : ℝ => t • e + y) 0 := by fun_prop
          have hcomp : ContinuousAt (fun t : ℝ => Φ (t • e + y)) 0 :=
            ContinuousAt.comp' (x := (0 : ℝ)) (f := fun t : ℝ => t • e + y)
              (hΦ ((0 : ℝ) • e + y)).continuousAt hγc
          have hcont : ContinuousAt (fun t : ℝ => 2 * |Φ (t • e + y)|) 0 :=
            continuousAt_const.mul hcomp.abs
          have hval : (fun t : ℝ => 2 * |Φ (t • e + y)|) 0 < 1 := by
            simp [hy]
          have hev1 : ∀ᶠ t in 𝓝 (0 : ℝ), 2 * |Φ (t • e + y)| < 1 :=
            (tendsto_order.mp hcont.tendsto).2 1 hval
          have arcne : ∀ t : ℝ, t ≠ 0 → t • e + y ≠ y := by
            intro t ht hEq
            have h1 : (t • e + y) i0 = y i0 := by rw [hEq]
            simp only [e, Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
              at h1
            exact ht (by linarith)
          rw [eventually_nhdsWithin_iff]
          filter_upwards [hev1] with t ht htpos
          exact ⟨arcne t (ne_of_gt htpos), by simpa [hq0] using ht⟩
      · -- `q ≥ 1`
        have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
        have hycl : y ∈ closure (⋃ i, A i) := by
          rw [Metric.mem_closure_iff]
          intro ε hε
          obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
          obtain ⟨x, _, hxd, hxineq⟩ := hseq n
          exact ⟨x, hmem_target x hxineq, by rw [dist_comm]; exact lt_trans hxd hn⟩
        have hsub : (⋃ i, A i) ⊆ ⋃ i, closure (A i) := by
          intro z hz
          obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hz
          exact Set.mem_iUnion.mpr ⟨i, subset_closure hi⟩
        have hycl' : y ∈ ⋃ i, closure (A i) :=
          closure_minimal hsub (isClosed_iUnion_of_finite (fun _ => isClosed_closure)) hycl
        obtain ⟨i0, hi0⟩ := Set.mem_iUnion.mp hycl'
        obtain ⟨γ, hγan, hγ0, ε₀, hε₀, hγmem⟩ :=
          curveSel_full (m + 1) 1 (fun _ : Fin (m + 1) → ℝ => 0) (fun _ : Fin 1 => gfun i0)
            y analyticAt_const (fun _ => hgan i0) hi0
        refine ⟨γ, hγan, hγ0, ?_⟩
        have hmem : Set.Ioo (0 : ℝ) ε₀ ∈ 𝓝[>] (0 : ℝ) :=
          Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_le_nhds (Iio_mem_nhds hε₀))
        filter_upwards [hmem] with t ht
        have hAt : γ t ∈ A i0 := hγmem t ht
        have hineq := hA_sub i0 hAt
        rw [memA] at hAt
        have hlt' := two_abs_Phi_lt_of_pos (i := i0) hAt
        have hpos : 0 < |γ t i0 - y i0| ^ q := lt_of_le_of_lt (by positivity) hlt'
        refine ⟨?_, hineq⟩
        intro hEq
        have hzero : γ t i0 - y i0 = 0 := by rw [hEq, sub_self]
        rw [hzero, abs_zero, zero_pow hqpos.ne'] at hpos
        exact absurd hpos (lt_irrefl (0 : ℝ))

end Work.WilE3.Loj
