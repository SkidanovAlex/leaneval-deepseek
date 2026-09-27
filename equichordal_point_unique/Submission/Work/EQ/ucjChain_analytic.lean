import Mathlib
import Submission.Work.EQ.ucj_defs
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.fan_estimates

namespace Work.EQ

open Complex Metric Filter _root_.Topology

noncomputable section

/-- The bisector reflection `(x, y) ↦ (-x, y)` is analytic as a map `ℂ × ℂ → ℂ × ℂ`. -/
lemma ucj_analyticAt_eqMirror (P : ℂ × ℂ) : AnalyticAt ℂ eqMirror P := by
  have h := ((analyticAt_fst (𝕜 := ℂ) (p := P)).neg).prod
    (analyticAt_snd (𝕜 := ℂ) (p := P))
  exact h

/-- **Every coordinate of `ucjChain` is analytic on `U`.**  If `U` is open, avoids `0`, has
`‖z‖ < min δf ρg` and `‖λ^N · (C/z)‖ < min δf ρg` throughout, and the prescribed middle maps
`g k` (`k ≤ N`) are analytic on `U`, then every coordinate `n : ℤ` of the chain `ucjChain`
(`Submission.Work.EQ.ucj_defs`) is analytic on `U`. -/
theorem ucjChain_analytic {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) {Ke Lam Q δf ρg : ℝ}
    (hFG : ∀ (ε' : List Bool) (v : ℂ), ‖v‖ < δf → FanGood a h Ke Lam Q ε' v)
    (hgan : AnalyticOnNhd ℂ (germC a h) (Metric.ball 0 ρg))
    {N : ℕ} {ε η s : List Bool} (hε : ε.length = N) {C : ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hU0 : ∀ z ∈ U, z ≠ 0)
    (hUz : ∀ z ∈ U, ‖z‖ < min δf ρg)
    (hUc : ∀ z ∈ U, ‖(((eqLam a : ℝ) : ℂ)) ^ N * (C / z)‖ < min δf ρg)
    {g : ℕ → ℂ → ℂ × ℂ} (hg : ∀ k ≤ N, AnalyticOnNhd ℂ (g k) U) :
    ∀ n : ℤ, AnalyticOnNhd ℂ (fun z => (ucjChain a h ε η s N C g z).1 n) U := by
  have hfan : ∀ ε' : List Bool, AnalyticOnNhd ℂ (fan a h ε') (Metric.ball 0 δf) :=
    fun ε' v hv => (hFG ε' v (by simpa [Metric.mem_ball, dist_eq_norm] using hv)).1
  have hl0 : 0 < eqLam a := eqLam_pos' ha0 ha1
  have hl1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
  have hwne : (((eqLam a : ℝ) : ℂ)) ≠ 0 := by
    rw [← Complex.ofReal_zero]
    exact fun hcon => ne_of_gt hl0 (Complex.ofReal_inj.mp hcon)
  have hpow : ∀ m : ℕ, ‖(((eqLam a : ℝ) : ℂ) ^ (m : ℤ))‖ ≤ 1 := by
    intro m
    have h1 : (((eqLam a : ℝ) : ℂ) ^ (m : ℤ)) = (((eqLam a) ^ m : ℝ) : ℂ) := by
      rw [zpow_natCast, ← Complex.ofReal_pow]
    rw [h1]
    rw [Complex.norm_def, Complex.normSq_ofReal,
      Real.sqrt_mul_self (pow_nonneg (le_of_lt hl0) m)]
    exact pow_le_one₀ (le_of_lt hl0) (le_of_lt hl1)
  intro n
  by_cases hn : 0 ≤ n
  · have hn' : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn
    have hn1 : ‖(((eqLam a : ℝ) : ℂ) ^ n)‖ ≤ 1 := by rw [← hn']; exact hpow n.toNat
    by_cases hk : n.toNat ≤ N
    · have hfe : (fun z => (ucjChain a h ε η s N C g z).1 n)
          = fun z => fan a h (ε.drop n.toNat) (((eqLam a : ℝ) : ℂ) ^ n * z) := by
        funext z
        rw [ucjChain_fst_apply, if_pos hn, if_pos hk]
      rw [hfe]
      have hgmul : AnalyticOnNhd ℂ (fun z : ℂ => (((eqLam a : ℝ) : ℂ) ^ n) * z) U :=
        fun z _ => (analyticAt_const (v := ((eqLam a : ℝ) : ℂ) ^ n) (x := z)).mul
          (analyticAt_id (z := z))
      have hmap : Set.MapsTo (fun z : ℂ => (((eqLam a : ℝ) : ℂ) ^ n) * z) U
          (Metric.ball 0 δf) := fun z hz => by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        calc ‖(((eqLam a : ℝ) : ℂ) ^ n) * z‖
            = ‖(((eqLam a : ℝ) : ℂ) ^ n)‖ * ‖z‖ := norm_mul _ _
          _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hn1 (norm_nonneg _)
          _ = ‖z‖ := one_mul _
          _ < δf := lt_of_lt_of_le (hUz z hz) (min_le_left _ _)
      have hcomp := AnalyticOnNhd.comp (t := Metric.ball 0 δf) (hfan (ε.drop n.toNat))
        hgmul hmap
      simpa [Function.comp_def] using hcomp
    · have hfe : (fun z => (ucjChain a h ε η s N C g z).1 n)
          = fun z => germC a h (((eqLam a : ℝ) : ℂ) ^ n * z) := by
        funext z
        rw [ucjChain_fst_apply, if_pos hn, if_neg hk]
      rw [hfe]
      have hgmul : AnalyticOnNhd ℂ (fun z : ℂ => (((eqLam a : ℝ) : ℂ) ^ n) * z) U :=
        fun z _ => (analyticAt_const (v := ((eqLam a : ℝ) : ℂ) ^ n) (x := z)).mul
          (analyticAt_id (z := z))
      have hmap : Set.MapsTo (fun z : ℂ => (((eqLam a : ℝ) : ℂ) ^ n) * z) U
          (Metric.ball 0 ρg) := fun z hz => by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        calc ‖(((eqLam a : ℝ) : ℂ) ^ n) * z‖
            = ‖(((eqLam a : ℝ) : ℂ) ^ n)‖ * ‖z‖ := norm_mul _ _
          _ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hn1 (norm_nonneg _)
          _ = ‖z‖ := one_mul _
          _ < ρg := lt_of_lt_of_le (hUz z hz) (min_le_right _ _)
      have hcomp := AnalyticOnNhd.comp (t := Metric.ball 0 ρg) hgan hgmul hmap
      simpa [Function.comp_def] using hcomp
  · by_cases hk : (-n).toNat ≤ N
    · have hfe : (fun z => (ucjChain a h ε η s N C g z).1 n)
          = fun z => g ((-n).toNat) z := by
        funext z
        rw [ucjChain_fst_apply, if_neg hn, if_pos hk]
      rw [hfe]
      exact (hg (-n).toNat hk)
    · have hklt : N < (-n).toNat := lt_of_not_ge hk
      have hfe : (fun z => (ucjChain a h ε η s N C g z).1 n)
          = fun z => eqMirror (fan a h (η.drop ((-n).toNat - N))
              (((eqLam a : ℝ) : ℂ) ^ (((-n).toNat : ℤ)) * (C / z))) := by
        funext z
        rw [ucjChain_fst_apply, if_neg hn, if_neg hk]
      rw [hfe]
      have hNk : N ≤ (-n).toNat := le_of_lt hklt
      have hsplit : (((eqLam a : ℝ) : ℂ) ^ (((-n).toNat : ℤ)))
          = (((eqLam a : ℝ) : ℂ) ^ ((((-n).toNat - N : ℕ) : ℤ)))
              * (((eqLam a : ℝ) : ℂ) ^ ((N : ℤ))) := by
        have hk_eq : (((-n).toNat : ℤ)) = ((((-n).toNat - N : ℕ) : ℤ)) + ((N : ℤ)) := by
          rw [Int.natCast_sub hNk]; ring
        rw [hk_eq, zpow_add₀ hwne]
      have hbound : ∀ z ∈ U,
          ‖(((eqLam a : ℝ) : ℂ) ^ (((-n).toNat : ℤ)) * (C / z))‖ < δf := by
        intro z hz
        calc ‖(((eqLam a : ℝ) : ℂ) ^ (((-n).toNat : ℤ)) * (C / z))‖
            = ‖(((eqLam a : ℝ) : ℂ) ^ ((((-n).toNat - N : ℕ) : ℤ)))
                * ((((eqLam a : ℝ) : ℂ) ^ ((N : ℤ))) * (C / z))‖ := by rw [hsplit]; ring
          _ = ‖(((eqLam a : ℝ) : ℂ) ^ ((((-n).toNat - N : ℕ) : ℤ)))‖
                * ‖(((eqLam a : ℝ) : ℂ) ^ ((N : ℤ))) * (C / z)‖ := by rw [norm_mul]
          _ ≤ 1 * ‖(((eqLam a : ℝ) : ℂ) ^ ((N : ℤ))) * (C / z)‖ :=
              mul_le_mul_of_nonneg_right (hpow ((-n).toNat - N)) (norm_nonneg _)
          _ = ‖(((eqLam a : ℝ) : ℂ) ^ N) * (C / z)‖ := by rw [zpow_natCast, one_mul]
          _ < δf := lt_of_lt_of_le (hUc z hz) (min_le_left _ _)
      have hdiv : AnalyticOnNhd ℂ (fun z : ℂ => C / z) U := fun z hz =>
        AnalyticAt.div (analyticAt_const (v := C) (x := z)) (analyticAt_id (z := z)) (hU0 z hz)
      have hEg : AnalyticOnNhd ℂ
          (fun z : ℂ => (((eqLam a : ℝ) : ℂ) ^ (((-n).toNat : ℤ))) * (C / z)) U :=
        fun z hz => (analyticAt_const (v := (((eqLam a : ℝ) : ℂ) ^ (((-n).toNat : ℤ))))
          (x := z)).mul (hdiv z hz)
      have hmap : Set.MapsTo
          (fun z : ℂ => (((eqLam a : ℝ) : ℂ) ^ (((-n).toNat : ℤ))) * (C / z)) U
          (Metric.ball 0 δf) := fun z hz => by
        rw [Metric.mem_ball, dist_eq_norm, sub_zero]
        exact hbound z hz
      have hcomp := AnalyticOnNhd.comp (t := Metric.ball 0 δf)
        (hfan (η.drop ((-n).toNat - N))) hEg hmap
      intro z hz
      exact (ucj_analyticAt_eqMirror (fan a h (η.drop ((-n).toNat - N))
          (((eqLam a : ℝ) : ℂ) ^ (((-n).toNat : ℤ)) * (C / z)))).comp
        (f := fun u => fan a h (η.drop ((-n).toNat - N))
          (((eqLam a : ℝ) : ℂ) ^ (((-n).toNat : ℤ)) * (C / u))) (x := z) (hcomp z hz)

end

end Work.EQ
