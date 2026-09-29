import Mathlib
import Submission.Work.TMComp.IDSDefs
import Submission.Work.TMComp.RotBasics.PS
import Submission.Work.TMComp.IDSPrufer.pruferIter_cocycle
import Submission.Work.TMComp.IDSPrufer.contx

/-!
# `rotLift_approx`: Cesàro averages of Prüfer angles converge at rate `1 / n`

The lifted fibered rotation number

`rotLift α lam E = limUnder atTop (fun n => (∫ x in 0..1, F^n_x 0) / n)`

is the Cesàro limit of the integrated Prüfer angles `F^n_x(0) = pruferIter α lam E n x 0`
(`rotLift` is defined by `limUnder`, which *is* the limit as soon as the latter exists).
Here we prove the quantitative form

`|rotLift α lam E - (∫ x in 0..1, F^n_x 0) / n| ≤ 1 / n`  for `n ≥ 1`,

i.e. the convergence rate `1/n` characteristic of an almost additive sequence with error `1`.

The proof has three independent layers.

* **Prüfer structure.** `pruferStep a` is a nondecreasing degree-one lift
  (`pruferStep_mono`, `pruferStep_add_one`, in `RotBasics/PS`), so for every `m` and `y` the
  map `t ↦ F^m_y t` is nondecreasing with `F^m_y (t+1) = F^m_y t + 1`.  Hence
  `|F^m_y t - t - F^m_y 0| ≤ 1` (`monoDegreeOne_le_one`), the *displacement bound*.

* **Almost additivity.** The cocycle identity `F^{n+m}_x = F^m_{x+nα} ∘ F^n_x`
  (`pruferIter_cocycle`) gives, with the displacement bound and the translation invariance of
  `∫₀¹` for `1`-periodic integrands,

  `|∫₀¹ F^{n+m}_x 0 dx - ∫₀¹ F^n_x 0 dx - ∫₀¹ F^m_x 0 dx| ≤ 1`.

* **Almost additive sequences.** For `a : ℕ → ℝ` with `a 0 = 0` and
  `|a(n+m) - a n - a m| ≤ c`, one has `|n a_m - m a_n| ≤ (n+m-2) c`, so `a_n/n` is Cauchy,
  converges, and `|lim a_n/n - a_n/n| ≤ c/n` (`almostAdditive_limUnder_aux`); `limUnder`
  returns that limit.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace Work.TMComp.IDSPrufer

/-! ## 1. Almost additive sequences -/

/-- An almost additive sequence `a` with `a 0 = 0` and error `≤ c`: the Cesàro limit
`lim a_n / n` exists, and `a_n / n` approaches it at rate `c / n`.  Written with `limUnder`,
which is a limit of the sequence whenever a limit exists. -/
theorem almostAdditive_limUnder_aux (a : ℕ → ℝ) (c : ℝ) (hc : 0 ≤ c) (h0 : a 0 = 0)
    (hadd : ∀ n m : ℕ, |a (n + m) - a n - a m| ≤ c) :
    ∀ n : ℕ, 1 ≤ n →
      |Filter.limUnder atTop (fun k : ℕ => a k / (k : ℝ)) - a n / (n : ℝ)| ≤ c / (n : ℝ) := by
  -- `|a r| ≤ r (|a 1| + c)`
  have hlin : ∀ r : ℕ, |a r| ≤ (r : ℝ) * (|a 1| + c) := by
    intro r
    induction r with
    | zero => simp [h0]
    | succ r ih =>
      have h := hadd r 1
      have hkey : a (r + 1) = (a (r + 1) - a r - a 1) + a r + a 1 := by ring
      rw [hkey]
      have htri : |(a (r + 1) - a r - a 1) + a r + a 1|
          ≤ |a (r + 1) - a r - a 1| + |a r| + |a 1| := by
        have h1 := abs_add_le (a (r + 1) - a r - a 1) (a r)
        have h2 := abs_add_le ((a (r + 1) - a r - a 1) + a r) (a 1)
        linarith
      calc |(a (r + 1) - a r - a 1) + a r + a 1|
          ≤ |a (r + 1) - a r - a 1| + |a r| + |a 1| := htri
        _ ≤ c + (r : ℝ) * (|a 1| + c) + |a 1| := by linarith
        _ = ((r + 1 : ℕ) : ℝ) * (|a 1| + c) := by push_cast; ring
  -- `|a (k N) - k a N| ≤ (k-1) c`
  have hmult : ∀ (k N : ℕ), |a ((k + 1) * N) - ((k + 1 : ℕ) : ℝ) * a N| ≤ (k : ℝ) * c := by
    intro k
    induction k with
    | zero => intro N; simp
    | succ k ih =>
      intro N
      have h := hadd ((k + 1) * N) N
      have hidx : (k + 1) * N + N = (k + 1 + 1) * N := by ring
      have hkey : a ((k + 1 + 1) * N) - ((k + 1 + 1 : ℕ) : ℝ) * a N
          = (a ((k + 1) * N + N) - a ((k + 1) * N) - a N)
            + (a ((k + 1) * N) - ((k + 1 : ℕ) : ℝ) * a N) := by
        rw [hidx]; push_cast; ring
      rw [hkey]
      have htri := abs_add_le (a ((k + 1) * N + N) - a ((k + 1) * N) - a N)
        (a ((k + 1) * N) - ((k + 1 : ℕ) : ℝ) * a N)
      calc |(a ((k + 1) * N + N) - a ((k + 1) * N) - a N)
            + (a ((k + 1) * N) - ((k + 1 : ℕ) : ℝ) * a N)|
          ≤ |a ((k + 1) * N + N) - a ((k + 1) * N) - a N|
            + |a ((k + 1) * N) - ((k + 1 : ℕ) : ℝ) * a N| := htri
        _ ≤ c + (k : ℝ) * c := by have ihN := ih N; linarith
        _ = ((k + 1 : ℕ) : ℝ) * c := by push_cast; ring
  -- `|m a n - n a m| ≤ c m + c n`
  have hdiff : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
      |(m : ℝ) * a n - (n : ℝ) * a m| ≤ c * (m : ℝ) + c * (n : ℝ) := by
    intro n m _ _
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    have h1 : |a ((n' + 1) * (m' + 1)) - ((n' + 1 : ℕ) : ℝ) * a (m' + 1)| ≤ (n' : ℝ) * c :=
      hmult n' (m' + 1)
    have h2 : |a ((m' + 1) * (n' + 1)) - ((m' + 1 : ℕ) : ℝ) * a (n' + 1)| ≤ (m' : ℝ) * c :=
      hmult m' (n' + 1)
    have hkey : ((m' + 1 : ℕ) : ℝ) * a (n' + 1) - ((n' + 1 : ℕ) : ℝ) * a (m' + 1)
        = (((m' + 1 : ℕ) : ℝ) * a (n' + 1) - a ((m' + 1) * (n' + 1)))
          + (a ((m' + 1) * (n' + 1)) - ((n' + 1 : ℕ) : ℝ) * a (m' + 1)) := by ring
    rw [hkey]
    have htri := abs_add_le (((m' + 1 : ℕ) : ℝ) * a (n' + 1) - a ((m' + 1) * (n' + 1)))
      (a ((m' + 1) * (n' + 1)) - ((n' + 1 : ℕ) : ℝ) * a (m' + 1))
    have h2' : |((m' + 1 : ℕ) : ℝ) * a (n' + 1) - a ((m' + 1) * (n' + 1))| ≤ (m' : ℝ) * c := by
      rw [abs_sub_comm]; exact h2
    have h1' : |a ((m' + 1) * (n' + 1)) - ((n' + 1 : ℕ) : ℝ) * a (m' + 1)| ≤ (n' : ℝ) * c := by
      rw [Nat.mul_comm (m' + 1) (n' + 1)]; exact h1
    calc |(((m' + 1 : ℕ) : ℝ) * a (n' + 1) - a ((m' + 1) * (n' + 1)))
            + (a ((m' + 1) * (n' + 1)) - ((n' + 1 : ℕ) : ℝ) * a (m' + 1))|
          ≤ |((m' + 1 : ℕ) : ℝ) * a (n' + 1) - a ((m' + 1) * (n' + 1))|
            + |a ((m' + 1) * (n' + 1)) - ((n' + 1 : ℕ) : ℝ) * a (m' + 1)| := htri
        _ ≤ (m' : ℝ) * c + (n' : ℝ) * c := by linarith
        _ ≤ c * (m' + 1 : ℕ) + c * (n' + 1 : ℕ) := by push_cast; nlinarith
  -- `|a n / n - a m / m| ≤ c / n + c / m`
  have hbm : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
      |a n / (n : ℝ) - a m / (m : ℝ)| ≤ c / (n : ℝ) + c / (m : ℝ) := by
    intro n m hn hm
    have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
    have hexp : a n / (n : ℝ) - a m / (m : ℝ)
        = ((m : ℝ) * a n - (n : ℝ) * a m) / ((n : ℝ) * (m : ℝ)) := by
      field_simp
    rw [hexp, abs_div, abs_of_pos (by positivity : (0:ℝ) < (n:ℝ) * (m:ℝ)),
      div_le_iff₀ (by positivity : (0:ℝ) < (n:ℝ) * (m:ℝ))]
    have hR : (c / (n : ℝ) + c / (m : ℝ)) * ((n : ℝ) * (m : ℝ)) = c * m + c * n := by
      field_simp
    rw [hR]
    exact hdiff n m hn hm
  -- uniform bound on the averages
  have hbdd : ∀ m : ℕ, |a m / (m : ℝ)| ≤ |a 1| + c := by
    intro m
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      rw [h0]
      simp only [zero_div, abs_zero]
      positivity
    · have hm' : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      rw [abs_div, abs_of_pos hm', div_le_iff₀ hm']
      have h := hlin m
      calc |a m| ≤ (m : ℝ) * (|a 1| + c) := h
        _ = (|a 1| + c) * (m : ℝ) := by ring
  -- the sequence of averages is Cauchy
  have hcauchy : CauchySeq (fun k : ℕ => a k / (k : ℝ)) := by
    refine cauchySeq_of_le_tendsto_0'
      (fun N : ℕ => if N = 0 then |a 1| + c else 2 * c / (N : ℝ)) ?_ ?_
    · intro n m hnm
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        rw [Real.dist_eq, if_pos rfl]
        have hz : a 0 / ((0 : ℕ) : ℝ) = 0 := by simp [h0]
        rw [hz, zero_sub, abs_neg]
        exact hbdd m
      · have hn1 : 1 ≤ n := hn
        have hm1 : 1 ≤ m := le_trans hn1 hnm
        have hb := hbm n m hn1 hm1
        have hn0 : n ≠ 0 := by omega
        rw [Real.dist_eq, if_neg hn0]
        have hcm : c / (m : ℝ) ≤ c / (n : ℝ) := by
          apply div_le_div_of_nonneg_left hc
          · exact_mod_cast (show 0 < n by omega)
          · exact_mod_cast hnm
        have h2 : 2 * c / (n : ℝ) = c / (n : ℝ) + c / (n : ℝ) := by ring
        rw [h2]
        linarith
    · have h0t : Tendsto (fun N : ℕ => 2 * c / (N : ℝ)) atTop (𝓝 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      refine h0t.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with N hN
      simp [show N ≠ 0 by omega]
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- the limit is within `c / n` of each average
  have hkey : ∀ n : ℕ, 1 ≤ n → |L - a n / (n : ℝ)| ≤ c / (n : ℝ) := by
    intro n hn
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hten : Tendsto (fun m : ℕ => |a m / (m : ℝ) - a n / (n : ℝ)|) atTop
        (𝓝 |L - a n / (n : ℝ)|) := (hL.sub tendsto_const_nhds).abs
    refine le_of_tendsto hten ?_
    have hdiv : Tendsto (fun m : ℕ => c / (m : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    filter_upwards [eventually_ge_atTop 1, hdiv.eventually (isOpen_Iio.mem_nhds (Set.mem_Iio.mpr hε))]
      with m hm1 hmε
    have hb := hbm m n hm1 hn
    linarith
  -- `limUnder` is that limit
  intro n hn
  have hLU : Filter.limUnder atTop (fun k : ℕ => a k / (k : ℝ)) = L := by
    have h1 : Tendsto (fun k : ℕ => a k / (k : ℝ)) atTop
        (𝓝 (Filter.limUnder atTop (fun k : ℕ => a k / (k : ℝ)))) :=
      tendsto_nhds_limUnder ⟨L, hL⟩
    exact tendsto_nhds_unique h1 hL
  rw [hLU]
  exact hkey n hn

/-! ## 2. Monotone degree-one lifts -/

/-- A nondecreasing degree-one lift `G` of a circle map (`G (t+1) = G t + 1`) stays within
distance `1` of the identity, measured from its value at `0`. -/
theorem monoDegreeOne_le_one {G : ℝ → ℝ} (hmono : Monotone G)
    (hper : ∀ t, G (t + 1) = G t + 1) : ∀ t : ℝ, |G t - t - G 0| ≤ 1 := by
  set f : ℝ → ℝ := fun s => G s - s - G 0 with hf
  have hfper : ∀ s, f (s + 1) = f s := by
    intro s
    simp only [hf]
    rw [hper]
    ring
  have hfN : ∀ (k : ℕ) (s : ℝ), f (s + k) = f s := by
    intro k
    induction k with
    | zero => intro s; simp
    | succ k ih =>
      intro s
      rw [show s + ((k : ℕ) + 1 : ℕ) = (s + k) + 1 by push_cast; ring, hfper, ih]
  have hfZ : ∀ (z : ℤ) (s : ℝ), f (s + z) = f s := by
    intro z s
    obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg z
    · rw [hk]; push_cast; exact hfN k s
    · rw [hk]
      push_cast
      have h := hfN k (s + -(k : ℝ))
      rw [show s + -(k : ℝ) + (k : ℝ) = s by ring] at h
      rw [h]
  intro t
  obtain ⟨z, hz0, hz1⟩ : ∃ z : ℤ, 0 ≤ t - (z : ℝ) ∧ t - (z : ℝ) < 1 :=
    ⟨⌊t⌋, by linarith [Int.floor_le t], by linarith [Int.lt_floor_add_one t]⟩
  have hft : f t = f (t - z) := by
    have h := hfZ z (t - z)
    rw [show t - (z : ℝ) + (z : ℝ) = t by ring] at h
    exact h
  have hG1 : G 1 = G 0 + 1 := by simpa using hper 0
  have h1 : G 0 ≤ G (t - (z : ℝ)) := hmono hz0
  have h2 : G (t - (z : ℝ)) ≤ G 0 + 1 := by
    have h := hmono (by linarith : t - (z : ℝ) ≤ 1)
    rwa [hG1] at h
  have hft' : f t = G (t - (z : ℝ)) - (t - (z : ℝ)) - G 0 := by
    rw [hft]
  show |f t| ≤ 1
  rw [hft', abs_le]
  constructor <;> linarith

/-! ## 3. Prüfer structure: monotonicity, degree one, periodicity, continuity -/

theorem pruferIter_mono (α lam E : ℝ) (n : ℕ) (x : ℝ) :
    Monotone (Work.TMContract.pruferIter α lam E n x) := by
  induction n with
  | zero => exact monotone_id
  | succ n ih =>
    intro s t hst
    simp only [Work.TMContract.pruferIter]
    exact Work.TMComp.RotBasics.pruferStep_mono _ (ih hst)

theorem pruferIter_add_one (α lam E : ℝ) (n : ℕ) (x t : ℝ) :
    Work.TMContract.pruferIter α lam E n x (t + 1)
      = Work.TMContract.pruferIter α lam E n x t + 1 := by
  induction n with
  | zero => simp [Work.TMContract.pruferIter]
  | succ n ih =>
    simp only [Work.TMContract.pruferIter]
    rw [ih, Work.TMComp.RotBasics.pruferStep_add_one]

theorem pruferIter_periodic_x (α lam E : ℝ) (n : ℕ) (x t : ℝ) :
    Work.TMContract.pruferIter α lam E n (x + 1) t = Work.TMContract.pruferIter α lam E n x t := by
  induction n with
  | zero => simp [Work.TMContract.pruferIter]
  | succ n ih =>
    simp only [Work.TMContract.pruferIter]
    rw [ih]
    congr 2
    have h2 : 2 * Real.pi * (x + 1 + (n : ℝ) * α)
        = 2 * Real.pi * (x + (n : ℝ) * α) + 2 * Real.pi := by ring
    rw [h2, Real.cos_add_two_pi]

theorem pruferIter_continuous (α lam E : ℝ) (n : ℕ) :
    Continuous (fun p : ℝ × ℝ => Work.TMContract.pruferIter α lam E n p.1 p.2) := by
  induction n with
  | zero =>
    simp only [Work.TMContract.pruferIter]
    exact continuous_snd
  | succ n ih =>
    simp only [Work.TMContract.pruferIter]
    have harg : Continuous (fun p : ℝ × ℝ =>
        (E - 2 * lam * Real.cos (2 * Real.pi * (p.1 + (n : ℝ) * α)),
          Work.TMContract.pruferIter α lam E n p.1 p.2)) := by
      refine Continuous.prodMk ?_ ih
      fun_prop
    exact pruferStep_pair_cont.comp harg

/-! ## 4. Translation invariance of `∫₀¹` for `1`-periodic integrands -/

theorem integral_shift_periodic (α lam E : ℝ) (m : ℕ) (c : ℝ) :
    (∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α lam E m (x + c) 0)
      = ∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α lam E m x 0 := by
  have hper : Function.Periodic (fun y : ℝ => Work.TMContract.pruferIter α lam E m y 0) 1 :=
    fun y => pruferIter_periodic_x α lam E m y 0
  have h11 : (1 : ℝ) + c = c + 1 := by ring
  rw [intervalIntegral.integral_comp_add_right
    (fun y : ℝ => Work.TMContract.pruferIter α lam E m y 0) c, zero_add, h11]
  simpa only [zero_add] using hper.intervalIntegral_add_eq c 0

/-! ## 5. Almost additivity of the integrated Prüfer angles -/

/-- The displacement of the `m`-th Prüfer iterate over a full period differs by at most `1`
from its value at the angle `0` (the displacement bound for a monotone degree-one lift). -/
theorem pruferIter_disp_le (α lam E : ℝ) (m : ℕ) (y s : ℝ) :
    |Work.TMContract.pruferIter α lam E m y s - s - Work.TMContract.pruferIter α lam E m y 0|
      ≤ 1 :=
  monoDegreeOne_le_one (pruferIter_mono α lam E m y)
    (fun t => pruferIter_add_one α lam E m y t) s

/-- Almost additivity, with error `1`, of the integrated Prüfer angles
`a n = ∫₀¹ F^n_x(0) dx`. -/
theorem almostAdditive_int (α lam E : ℝ) :
    ∀ n m : ℕ,
      |(∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α lam E (n + m) x 0)
        - (∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α lam E n x 0)
        - (∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α lam E m x 0)| ≤ 1 := by
  intro n m
  set Fn : ℝ → ℝ := fun x => Work.TMContract.pruferIter α lam E n x 0 with hFn
  set Gn : ℝ → ℝ := fun x => Work.TMContract.pruferIter α lam E m (x + (n : ℝ) * α)
      (Work.TMContract.pruferIter α lam E n x 0) with hGn
  set Q : ℝ → ℝ := fun x => Work.TMContract.pruferIter α lam E m (x + (n : ℝ) * α) 0 with hQ
  set P : ℝ → ℝ := fun x => Gn x - Fn x with hP
  have hcoc : ∀ x : ℝ, Work.TMContract.pruferIter α lam E (n + m) x 0 = Gn x := by
    intro x
    rw [hGn, pruferIter_cocycle]
  have hcont_n : Continuous Fn := by
    rw [hFn]
    exact (pruferIter_continuous α lam E n).comp (Continuous.prodMk continuous_id continuous_const)
  have hcont_m : Continuous (fun p : ℝ × ℝ => Work.TMContract.pruferIter α lam E m p.1 p.2) :=
    pruferIter_continuous α lam E m
  have hcont_G : Continuous Gn := by
    rw [hGn]
    exact hcont_m.comp (Continuous.prodMk (continuous_id.add continuous_const) hcont_n)
  have hcont_Q : Continuous Q := by
    rw [hQ]
    exact hcont_m.comp (Continuous.prodMk (continuous_id.add continuous_const) continuous_const)
  have hcont_P : Continuous P := by
    rw [hP]
    exact hcont_G.sub hcont_n
  have hcont_PQ : Continuous (fun x : ℝ => P x - Q x) := hcont_P.sub hcont_Q
  have hIntFn : IntervalIntegrable Fn volume (0 : ℝ) 1 := hcont_n.intervalIntegrable 0 1
  have hIntP : IntervalIntegrable P volume (0 : ℝ) 1 := hcont_P.intervalIntegrable 0 1
  have hIntQ : IntervalIntegrable Q volume (0 : ℝ) 1 := hcont_Q.intervalIntegrable 0 1
  have hPQ : ∀ x : ℝ, |P x - Q x| ≤ 1 := by
    intro x
    rw [hP, hQ, hGn]
    exact pruferIter_disp_le α lam E m (x + (n : ℝ) * α)
      (Work.TMContract.pruferIter α lam E n x 0)
  have hstep1 : (∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α lam E (n + m) x 0)
      = ∫ x in (0 : ℝ)..1, (Fn x + P x) := by
    have hfun : ∀ x : ℝ, Work.TMContract.pruferIter α lam E (n + m) x 0 = Fn x + P x := by
      intro x
      rw [hcoc x, hP]
      ring
    simp only [hfun]
  have hstep2 : (∫ x in (0 : ℝ)..1, (Fn x + P x))
      = (∫ x in (0 : ℝ)..1, Fn x) + ∫ x in (0 : ℝ)..1, P x :=
    intervalIntegral.integral_add hIntFn hIntP
  have hstep3 : (∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α lam E m x 0)
      = ∫ x in (0 : ℝ)..1, Q x := by
    rw [hQ]
    exact (integral_shift_periodic α lam E m ((n : ℝ) * α)).symm
  have hstep4 : (∫ x in (0 : ℝ)..1, P x) - (∫ x in (0 : ℝ)..1, Q x)
      = ∫ x in (0 : ℝ)..1, (P x - Q x) :=
    (intervalIntegral.integral_sub hIntP hIntQ).symm
  have hchain : (∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α lam E (n + m) x 0)
        - (∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α lam E n x 0)
        - (∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α lam E m x 0)
      = ∫ x in (0 : ℝ)..1, (P x - Q x) := by
    rw [hstep1, hstep2, ← hFn, hstep3]
    have hrearr : (∫ x in (0 : ℝ)..1, Fn x) + (∫ x in (0 : ℝ)..1, P x)
        - (∫ x in (0 : ℝ)..1, Fn x) - (∫ x in (0 : ℝ)..1, Q x)
        = (∫ x in (0 : ℝ)..1, P x) - (∫ x in (0 : ℝ)..1, Q x) := by ring
    rw [hrearr, hstep4]
  rw [hchain]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := 1)
    (f := fun x : ℝ => P x - Q x) (fun x _ => by rw [Real.norm_eq_abs]; exact hPQ x)
  simpa using hb

/-! ## 6. The target -/

theorem rotLift_approx (α lam E : ℝ) {n : ℕ} (hn : 1 ≤ n) :
    |Work.TMContract.rotLift α lam E
      - (∫ x in (0:ℝ)..1, Work.TMContract.pruferIter α lam E n x 0) / (n : ℝ)|
      ≤ 1 / (n : ℝ) := by
  have h0 : (fun k : ℕ => ∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α lam E k x 0) 0 = 0 := by
    simp [Work.TMContract.pruferIter]
  have h := almostAdditive_limUnder_aux
    (fun k : ℕ => ∫ x in (0 : ℝ)..1, Work.TMContract.pruferIter α lam E k x 0) 1
    zero_le_one h0 (almostAdditive_int α lam E) n hn
  simpa only [Work.TMContract.rotLift] using h

end Work.TMComp.IDSPrufer
