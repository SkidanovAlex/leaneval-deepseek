/-
  Work.WilE2 — global integral curves from *uniform* local existence.

  If an autonomous ODE `x' = v x` admits, for every initial point `x`, a solution on the *same*
  time interval `(-δ, δ)` (with `δ > 0`), then it admits global solutions.  The proof is the
  standard "step and glue" argument:

  * write `s = δ / 2` (so that both endpoints of a step are interior to `(-δ, δ)`);
  * for `y : E` choose a local solution `φ y` of the ODE on `(-δ, δ)` with `φ y 0 = y`, and let
    `Φ y = φ y s` be the advance by time `s`;
  * the `k`-th `s`-step is the translate `g k := fun t => φ (Φ^[k] x) (t - k * s)`, which solves
    the ODE on the closed interval `[k * s, (k+1) * s]`; consecutive steps agree at the junction
    `(k+1) * s`, so the curve `γ t = φ (Φ^[⌊t/s⌋] x) (t - ⌊t/s⌋ * s)` solves the ODE for all
    `t ≥ 0` (the junction points are handled with one-sided derivatives);
  * running the same construction for `-v` and reversing time gives a solution for all `t ≤ 0`;
  * gluing the two halves at `0` gives a global solution.

  Note that the global Lipschitz hypothesis on `v` is *not* used; uniform local existence alone
  suffices.
-/
import Mathlib
import Submission.Work.WilE2.glue_integral_curve
import Submission.Work.WilE2.segment_hasDerivAt

set_option autoImplicit false
set_option maxHeartbeats 800000

open Set
open scoped Topology

namespace Work.WilE2

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- **Time reversal.**  If `γ` solves `γ' = v ∘ γ` on `(-δ, δ)`, then `u ↦ γ (-u)` solves
`x' = (-v) ∘ x` there. -/
theorem hasDerivAt_comp_neg {v : E → E} {γ : ℝ → E} {δ : ℝ}
    (h : ∀ t ∈ Ioo (-δ) δ, HasDerivAt γ (v (γ t)) t) :
    ∀ t ∈ Ioo (-δ) δ, HasDerivAt (fun s => γ (-s)) ((-v) ((fun s => γ (-s)) t)) t := by
  intro t ht
  have ht' : -t ∈ Ioo (-δ) δ := ⟨by linarith [ht.2], by linarith [ht.1]⟩
  have h1 : HasDerivAt (fun s => γ (-s)) ((-1 : ℝ) • v (γ (-t))) t :=
    (h (-t) ht').scomp t (hasDerivAt_neg' t)
  have h2 : ((-1 : ℝ) • v (γ (-t))) = (-v) ((fun s => γ (-s)) t) := by
    simp
  rw [h2] at h1
  exact h1

/-- **Forward stepping.**  Uniform local existence of solutions of `v` on `(-δ, δ)` yields, for
every initial point `x`, an integral curve defined for all non-negative times. -/
theorem exists_solution_nonneg {v : E → E} {δ : ℝ} (hδ : 0 < δ)
    (hloc : ∀ x : E, ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t ∈ Ioo (-δ) δ, HasDerivAt γ (v (γ t)) t)
    (x : E) :
    ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t : ℝ, 0 ≤ t → HasDerivAt γ (v (γ t)) t := by
  set s : ℝ := δ / 2 with hsdef
  have hs : 0 < s := by rw [hsdef]; linarith
  have hsd : s < δ := by rw [hsdef]; linarith
  -- chosen local solutions of the ODE
  set φ : E → ℝ → E := fun y => (hloc y).choose with hφdef
  have hφ0 : ∀ y, φ y 0 = y := fun y => (hloc y).choose_spec.1
  have hφd : ∀ y : E, ∀ t ∈ Ioo (-δ) δ, HasDerivAt (φ y) (v (φ y t)) t :=
    fun y => (hloc y).choose_spec.2
  -- the starting points of the successive `s`-steps
  set pt : ℕ → E := fun m => ((fun y => φ y s)^[m]) x with hptdef
  have hpt_succ : ∀ m, pt (m + 1) = φ (pt m) s := fun m => by
    have h := Function.iterate_succ_apply' (fun y => φ y s) m x
    simp only [hptdef]
    simpa [Nat.succ_eq_add_one] using h
  -- the candidate global curve
  set γ : ℝ → E := fun t => φ (pt (Nat.floor (t / s))) (t - (Nat.floor (t / s) : ℝ) * s)
    with hγdef
  refine ⟨γ, ?_, ?_⟩
  · show φ (pt (Nat.floor ((0 : ℝ) / s))) (0 - (Nat.floor ((0 : ℝ) / s) : ℝ) * s) = x
    simp only [zero_div, Nat.floor_zero, Nat.cast_zero, zero_mul, sub_zero]
    rw [hφ0]
    simp only [hptdef, Function.iterate_zero_apply]
  · intro t ht
    -- floor bookkeeping for `t ≥ 0`
    have hle : ((Nat.floor (t / s) : ℝ)) * s ≤ t := by
      have h1 : (Nat.floor (t / s) : ℝ) ≤ t / s := Nat.floor_le (div_nonneg ht hs.le)
      have h2 := mul_le_mul_of_nonneg_right h1 hs.le
      rwa [div_mul_cancel₀ t (ne_of_gt hs)] at h2
    have hlt : t < ((Nat.floor (t / s) : ℝ) + 1) * s := by
      have h1 : t / s < (Nat.floor (t / s) : ℝ) + 1 := Nat.lt_floor_add_one (t / s)
      have h2 := mul_lt_mul_of_pos_right h1 hs
      rwa [div_mul_cancel₀ t (ne_of_gt hs)] at h2
    have hlt' : t < (Nat.floor (t / s) : ℝ) * s + s := by
      have h : ((Nat.floor (t / s) : ℝ) + 1) * s = (Nat.floor (t / s) : ℝ) * s + s := by ring
      rwa [h] at hlt
    rcases Nat.eq_zero_or_pos (Nat.floor (t / s)) with hk0 | hkpos
    · -- `t < s`: the curve agrees with the local solution at `x` near `t`
      have hts : t < s := by
        have h := hlt
        rw [hk0] at h
        simpa using h
      have hagree0 : ∀ u < s, γ u = φ x u := by
        intro u hu
        have hpt0 : pt 0 = x := by simp only [hptdef, Function.iterate_zero_apply]
        have hfloor : Nat.floor (u / s) = 0 := Nat.floor_eq_zero.mpr ((div_lt_one hs).mpr hu)
        show φ (pt (Nat.floor (u / s))) (u - (Nat.floor (u / s) : ℝ) * s) = φ x u
        rw [hfloor, hpt0]
        simp
      have hev : γ =ᶠ[𝓝 t] (φ x) := by
        filter_upwards [Iio_mem_nhds hts] with u hu
        exact hagree0 u hu
      have hmem : t ∈ Ioo (-δ) δ := ⟨by linarith, by linarith [hts, hsd]⟩
      have hd := (hφd x t hmem).congr_of_eventuallyEq hev
      rw [hagree0 t hts]
      exact hd
    · -- `t` lies in the segment of index `k = ⌊t/s⌋ ≥ 1`
      have hcast : (((Nat.floor (t / s) - 1 : ℕ)) : ℝ) = (Nat.floor (t / s) : ℝ) - 1 := by
        have h : (Nat.floor (t / s) - 1 : ℕ) + 1 = Nat.floor (t / s) := Nat.sub_add_cancel hkpos
        have h' := congrArg (fun n : ℕ => (n : ℝ)) h
        push_cast at h'
        linarith
      -- the segment of index `m` agrees with `γ` on its own time interval
      have hagree : ∀ (m : ℕ) (u : ℝ), (m : ℝ) * s ≤ u → u ≤ (m : ℝ) * s + s →
          γ u = φ (pt m) (u - (m : ℝ) * s) := by
        intro m u h1 h2
        have hu0 : 0 ≤ u := le_trans (mul_nonneg (Nat.cast_nonneg m) hs.le) h1
        have hdiv0 : 0 ≤ u / s := div_nonneg hu0 hs.le
        rcases eq_or_lt_of_le h2 with h2eq | h2lt
        · -- `u = m * s + s` is the right end of the segment, i.e. the next starting point
          have hfloor : Nat.floor (u / s) = m + 1 := by
            refine (Nat.floor_eq_iff hdiv0).mpr ⟨?_, ?_⟩
            · have hc : (((m + 1 : ℕ)) : ℝ) * s = (m : ℝ) * s + s := by push_cast; ring
              rw [le_div_iff₀ hs, hc, h2eq]
            · have hc : (((m + 1 : ℕ)) : ℝ) + 1 = ((m : ℝ) + 1) + 1 := by push_cast; ring
              rw [div_lt_iff₀ hs, hc]
              nlinarith [h2eq, hs]
          show φ (pt (Nat.floor (u / s))) (u - (Nat.floor (u / s) : ℝ) * s)
            = φ (pt m) (u - (m : ℝ) * s)
          rw [hfloor]
          have e1 : u - (((m + 1 : ℕ)) : ℝ) * s = 0 := by
            have hc : (((m + 1 : ℕ)) : ℝ) * s = (m : ℝ) * s + s := by push_cast; ring
            rw [hc, h2eq]; ring
          have e2 : u - (m : ℝ) * s = s := by rw [h2eq]; ring
          rw [e1, e2, hφ0]
          exact hpt_succ m
        · -- `u` is in the interior of the segment
          have hfloor : Nat.floor (u / s) = m := by
            refine (Nat.floor_eq_iff hdiv0).mpr ⟨?_, ?_⟩
            · rw [le_div_iff₀ hs]; exact h1
            · rw [div_lt_iff₀ hs]
              nlinarith [h2lt, hs]
          show φ (pt (Nat.floor (u / s))) (u - (Nat.floor (u / s) : ℝ) * s)
            = φ (pt m) (u - (m : ℝ) * s)
          rw [hfloor]
      by_cases hteq : t = (Nat.floor (t / s) : ℝ) * s
      · -- junction between the segments `k-1` and `k`: one-sided derivatives
        have hmemR : t ∈ Icc ((Nat.floor (t / s) : ℝ) * s) ((Nat.floor (t / s) : ℝ) * s + s) :=
          ⟨le_of_eq hteq.symm, by linarith [hteq, hs]⟩
        have hmemL : t ∈ Icc ((((Nat.floor (t / s) - 1 : ℕ)) : ℝ) * s)
            ((((Nat.floor (t / s) - 1 : ℕ)) : ℝ) * s + s) := by
          constructor
          · rw [hcast]; nlinarith [hteq, hs]
          · rw [hcast]; nlinarith [hteq, hs]
        have hR : HasDerivWithinAt γ (v (γ t)) (Ici t) t := by
          have hev : γ =ᶠ[𝓝[Ici t] t]
              (fun w => φ (pt (Nat.floor (t / s))) (w - (Nat.floor (t / s) : ℝ) * s)) := by
            dsimp only [Filter.EventuallyEq]
            rw [eventually_nhdsWithin_iff]
            filter_upwards [Iio_mem_nhds (show t < t + s by linarith)] with u hu
            intro hmem
            have hu' : u < t + s := hu
            exact hagree (Nat.floor (t / s)) u (le_trans (le_of_eq hteq.symm) hmem)
              (le_of_lt (by linarith [hu', hteq]))
          have hseg := (segment_hasDerivAt hs.le hsd hφd x (Nat.floor (t / s)) t
            hmemR.1 hmemR.2).hasDerivWithinAt (s := Ici t)
          have h2 := hseg.congr_of_eventuallyEq hev
            (hagree (Nat.floor (t / s)) t hmemR.1 hmemR.2)
          rw [hagree (Nat.floor (t / s)) t hmemR.1 hmemR.2]
          exact h2
        have hL : HasDerivWithinAt γ (v (γ t)) (Iic t) t := by
          have hev : γ =ᶠ[𝓝[Iic t] t]
              (fun w => φ (pt (Nat.floor (t / s) - 1))
                (w - (((Nat.floor (t / s) - 1 : ℕ)) : ℝ) * s)) := by
            dsimp only [Filter.EventuallyEq]
            rw [eventually_nhdsWithin_iff]
            filter_upwards [Ioi_mem_nhds (show t - s < t by linarith)] with u hu
            intro hmem
            have hu' : t - s < u := hu
            have hmem' : u ≤ t := hmem
            refine hagree (Nat.floor (t / s) - 1) u ?_ ?_
            · rw [hcast]; nlinarith [hu', hteq]
            · rw [hcast]; nlinarith [hmem', hteq]
          have hseg := (segment_hasDerivAt hs.le hsd hφd x (Nat.floor (t / s) - 1) t
            hmemL.1 hmemL.2).hasDerivWithinAt (s := Iic t)
          have h2 := hseg.congr_of_eventuallyEq hev
            (hagree (Nat.floor (t / s) - 1) t hmemL.1 hmemL.2)
          rw [hagree (Nat.floor (t / s) - 1) t hmemL.1 hmemL.2]
          exact h2
        refine (hL.union hR).hasDerivAt ?_
        rw [Set.Iic_union_Ici]
        exact Filter.univ_mem
      · -- interior of the `k`-th segment
        have ht_gt : (Nat.floor (t / s) : ℝ) * s < t := lt_of_le_of_ne hle (Ne.symm hteq)
        have hmemR : t ∈ Icc ((Nat.floor (t / s) : ℝ) * s) ((Nat.floor (t / s) : ℝ) * s + s) :=
          ⟨le_of_lt ht_gt, le_of_lt hlt'⟩
        have hIoo : Ioo ((Nat.floor (t / s) : ℝ) * s) ((Nat.floor (t / s) : ℝ) * s + s) ∈ 𝓝 t :=
          Ioo_mem_nhds ht_gt hlt'
        have hev : γ =ᶠ[𝓝 t]
            (fun w => φ (pt (Nat.floor (t / s))) (w - (Nat.floor (t / s) : ℝ) * s)) := by
          filter_upwards [hIoo] with u hu
          exact hagree (Nat.floor (t / s)) u (le_of_lt hu.1) (le_of_lt hu.2)
        have hd := (segment_hasDerivAt hs.le hsd hφd x (Nat.floor (t / s)) t
          hmemR.1 hmemR.2).congr_of_eventuallyEq hev
        rw [hagree (Nat.floor (t / s)) t hmemR.1 hmemR.2]
        exact hd

/-- **Global existence from uniform local existence.**  If for every point `x` there is an integral
curve of the autonomous field `v` through `x` on the *fixed* interval `(-δ, δ)`, then every point
lies on a global integral curve.  (Global Lipschitzness of `v` is not needed for this.) -/
theorem global_integralCurve_of_uniform_local {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E]
    (v : E → E) (K : NNReal) (hK : LipschitzWith K v) (δ : ℝ) (hδ : 0 < δ)
    (hloc : ∀ x : E, ∃ γ : ℝ → E, γ 0 = x ∧
      ∀ t ∈ Set.Ioo (-δ) δ, HasDerivAt γ (v (γ t)) t) :
    ∀ x : E, ∃ γ : ℝ → E, γ 0 = x ∧ ∀ t : ℝ, HasDerivAt γ (v (γ t)) t := by
  intro x
  obtain ⟨γf, hγf0, hγfd⟩ := exists_solution_nonneg hδ hloc x
  have hloc' : ∀ y : E, ∃ γ : ℝ → E, γ 0 = y ∧
      ∀ t ∈ Set.Ioo (-δ) δ, HasDerivAt γ ((-v) (γ t)) t := by
    intro y
    obtain ⟨γ, hγ0, hγd⟩ := hloc y
    exact ⟨fun u => γ (-u), by simpa using hγ0, hasDerivAt_comp_neg hγd⟩
  obtain ⟨η, hη0, hηd⟩ := exists_solution_nonneg hδ hloc' x
  refine ⟨fun u => if u ≤ 0 then η (-u) else γf u, ?_, ?_⟩
  · show (if (0 : ℝ) ≤ 0 then η (-0) else γf 0) = x
    rw [if_pos le_rfl, neg_zero]
    exact hη0
  · have hf : ∀ t ≤ 0, HasDerivAt (fun u => η (-u)) (v ((fun u => η (-u)) t)) t := by
      intro t ht
      have h1 : HasDerivAt (fun u => η (-u)) ((-1 : ℝ) • ((-v) (η (-t)))) t :=
        (hηd (-t) (by linarith)).scomp t (hasDerivAt_neg' t)
      have h2 : ((-1 : ℝ) • ((-v) (η (-t)))) = v (η (-t)) := by
        simp
      rw [h2] at h1
      simpa using h1
    have hglue := glue_integral_curve (v := v) (f := fun u => η (-u)) (g := γf) (a := 0)
      (by show η (-0) = γf 0; rw [neg_zero, hη0, hγf0]) hf hγfd
    exact hglue

end Work.WilE2
