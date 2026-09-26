import Mathlib
import Submission.Work.Smooth.SphereJordan.planeIndex
import Submission.Work.Topology.PlaneCurve.windNumber_ne_zero_of_bounded_component
import Submission.Work.Smooth.SphereJordan.planeIndexGeom
import Submission.Work.Smooth.SphereJordan.loopIndexTrans
import Submission.Work.Smooth.SphereJordan.windNumber_eq_zero_or_odd_uncond
import Submission.Work.Smooth.SphereJordan.exists_sqrt_curve_of_even_windNumber
import Submission.Work.Smooth.SphereJordan.range_eq_of_subset_of_periodic
import Submission.Work.Smooth.SphereJordan.loopIndex_symm
import Submission.Work.Smooth.JordanSeparation.ComplHelpers

/-!
# A Jordan curve enclosing `0` carries a loop of index `1`

`Work.Smooth.SphereJordan.jordanLoopIndexOne`: for a continuous `2π`-periodic curve `γ : ℝ → ℂ`
injective on one period, avoiding `0`, and with `0` lying in a *bounded* connected component of the
complement of its trace, there is a closed loop `c : [0,1] → ℂ` with values in the trace of `γ` and
index `1`.

The mathematical content is the classical statement that a *simple* closed plane curve has winding
number `±1` around the points of its bounded complementary component — the workspace already
provides the weaker "`0` or odd" (`windNumber_eq_zero_or_odd_uncond`) and the nonvanishing of the
winding number at a bounded component (`windNumber_ne_zero_of_bounded_component`), but not the
sharp value.

## The route

Write `k = windNumber γ hγ 0 ≠ 0`.  The two orientation generators of the trace are the loop
`t ↦ γ (2π t)` (index `k`) and its reverse (index `-k`), so the theorem is exactly the statement
`|k| = 1`, and this is what is proved here.

If `|k| = n ≥ 2` we may take the `n`-th root of the curve
(`exists_powCurve_of_windNumber`): there is a curve `η` with `η ^ n = γ` pointwise and
`windNumber (η) 0 = k / n = ±1`.  Then `η` is again a Jordan curve (`η s = η t` forces
`γ s = γ t`, hence `s = t` modulo a period) whose trace still encloses `0`, and
`jordanTraceMeetsRotation` (a rotation-invariance form of the classical nesting of disjoint Jordan
curves: a Jordan curve enclosing `0` meets its rotation by any root of unity `ζ ≠ 1`) produces
`s, t` with `η s = ζ η t` for a primitive `n`-th root of unity `ζ`.  Raising to the `n`-th power
gives `γ s = γ t`, whence `s ≡ t` modulo `2π`, so `η t = ζ η t` and hence `η t = 0` — the
contradiction that forces `n = 1`.
-/

noncomputable section

open Set
open Classical

namespace Work.Smooth.SphereJordan

/-- **Additivity of the index under taking powers of a loop.**  The `n`-th power of a nowhere
vanishing closed loop has index `n` times the index of the loop. -/
theorem loopIndex_pow (u : C(unitInterval, ℂ)) (hu : ∀ t, u t ≠ 0) (hloop : u 0 = u 1)
    (n : ℕ) : loopIndex (u ^ n) = (n : ℤ) * loopIndex u := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h1 : (u ^ 0 : C(unitInterval, ℂ)) = ContinuousMap.const unitInterval 1 := by
      ext t; simp
    rw [h1, loopIndex_const 1 one_ne_zero]
    simp
  · obtain ⟨Λ, hΛ, -, -⟩ := argChangeLift u hu
    have hne : ∀ t : unitInterval, (u ^ n) t ≠ 0 := fun t => pow_ne_zero n (hu t)
    have hloop' : (u ^ n) 0 = (u ^ n) 1 := by
      simp only [ContinuousMap.pow_apply]; rw [hloop]
    set L : C(unitInterval, ℂ) :=
      ⟨fun t => (n : ℂ) * Λ t, continuous_const.mul Λ.continuous⟩ with hL
    have hlift : ∀ t, Complex.exp (L t) = (u ^ n) t := by
      intro t
      show Complex.exp ((n : ℂ) * Λ t) = (u ^ n) t
      rw [Complex.exp_nat_mul, hΛ t]
      simp [ContinuousMap.pow_apply]
    have hspec := loopIndex_spec (u ^ n) hne hloop' L hlift
    have hspecu := loopIndex_spec u hu hloop Λ hΛ
    have hkey : ((loopIndex (u ^ n) : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I)
        = (((n : ℤ) * loopIndex u : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) := by
      calc ((loopIndex (u ^ n) : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I)
          = L 1 - L 0 := hspec.symm
        _ = (n : ℂ) * (Λ 1 - Λ 0) := by
              show (n : ℂ) * Λ 1 - (n : ℂ) * Λ 0 = (n : ℂ) * (Λ 1 - Λ 0); ring
        _ = (n : ℂ) * (((loopIndex u : ℤ)) : ℂ) * (2 * ↑Real.pi * Complex.I) := by
              rw [hspecu]; ring
        _ = (((n : ℤ) * loopIndex u : ℤ) : ℂ) * (2 * ↑Real.pi * Complex.I) := by
              push_cast; ring
    exact Int.cast_inj.mp (mul_right_cancel₀ two_pi_I_ne_zero hkey)

/-- **A non-zero winding number puts the point in a bounded complementary component.**

If `windNumber κ hκ z ≠ 0` then the connected component of `z` in the complement of the trace is
bounded: otherwise it would contain points of arbitrarily large norm, where the winding number
vanishes (`windNumber_eq_zero_of_norm_gt`), contradicting the constancy of the winding number on a
connected component (`windNumber_eq_of_preconnected_subset`). -/
theorem isBounded_componentIn_zero_of_windNumber_ne_zero {κ : ℝ → ℂ} (hκ : Continuous κ)
    (hper : Function.Periodic κ (2 * Real.pi)) {z : ℂ} (hz : z ∉ Set.range κ)
    (hW : windNumber κ hκ z ≠ 0) :
    Bornology.IsBounded (connectedComponentIn (Set.range κ)ᶜ z) := by
  obtain ⟨R, hR⟩ :=
    (Work.Topology.PlaneCurve.isCompact_range_of_periodic hκ hper).isBounded.exists_norm_le
  have hR' : ∀ t : ℝ, ‖κ t‖ ≤ R := fun t => hR (κ t) ⟨t, rfl⟩
  by_contra hbdd
  have hbig : ∃ w ∈ connectedComponentIn (Set.range κ)ᶜ z, R + ‖z‖ + 1 < ‖w‖ := by
    by_contra hcon
    push Not at hcon
    exact hbdd ((Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R + ‖z‖ + 1)).subset
      (fun w hw => by rw [Metric.mem_closedBall, dist_zero_right]; exact hcon w hw))
  obtain ⟨w, hwmem, hwbig⟩ := hbig
  have hconst : windNumber κ hκ w = windNumber κ hκ z :=
    windNumber_eq_of_preconnected_subset hκ hper (S := connectedComponentIn (Set.range κ)ᶜ z)
      isPreconnected_connectedComponentIn (connectedComponentIn_subset _ _)
      (mem_connectedComponentIn hz) w hwmem
  have hzero : windNumber κ hκ w = 0 :=
    windNumber_eq_zero_of_norm_gt hκ hper hR' (by linarith [norm_nonneg z])
  exact hW (by rw [← hconst, hzero])

/-- **The `n`-th root of a curve, with its winding number.**  If the winding number of `γ` about
`z` is divisible by `n ≥ 1`, say `windNumber γ hγ z = n * m`, then `γ - z` has a continuous
`2π`-periodic `n`-th root `η` whose winding number about `0` is `m`: the argument lift of the
curve is divided by `n` (compare `exists_sqrt_curve_of_even_windNumber`, the case `n = 2`). -/
theorem exists_powCurve_of_windNumber {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) {z : ℂ} (hz : ∀ t : ℝ, γ t ≠ z) {n : ℕ}
    (hn : 1 ≤ n) {m : ℤ}
    (hW : windNumber γ hγ z = (n : ℤ) * m) :
    ∃ η : C(ℝ, ℂ), (∀ t : ℝ, η t ^ n = γ t - z) ∧ (∀ t : ℝ, η t ≠ 0) ∧
      Function.Periodic (fun t : ℝ => η t) (2 * Real.pi) ∧
      windNumber (fun t : ℝ => η t) η.continuous 0 = m := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnneC : (n : ℂ) ≠ 0 := by
    have h : ((n : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn0)
    simpa using h
  have hneN : n ≠ 0 := by omega
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  letI : Fact ((0 : ℝ) < 2 * Real.pi) := ⟨h2π⟩
  have h01 : ((0 : ℝ) ≤ 1) := zero_le_one
  set c : C(unitInterval, ℂ) := curveLoop (fun t : ℝ => γ t - z) (hγ.sub continuous_const) with hc
  have hcne : ∀ t : unitInterval, c t ≠ 0 := by
    intro t
    rw [hc]
    exact sub_ne_zero.mpr (by simpa using hz (2 * Real.pi * (t : ℝ)))
  have hcloop : c 0 = c 1 := by
    rw [hc]
    show γ (2 * Real.pi * ((0 : unitInterval) : ℝ)) - z
      = γ (2 * Real.pi * ((1 : unitInterval) : ℝ)) - z
    have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by norm_num
    have h1 : 2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi := by norm_num
    have h1' : γ (2 * Real.pi) = γ 0 := by simpa using hper 0
    rw [h0, h1, h1']
  have hWc : loopIndex c = (n : ℤ) * m := by rw [hc]; exact hW
  obtain ⟨Λ, hΛ, -, -⟩ := argChangeLift c hcne
  have hspec := loopIndex_spec c hcne hcloop Λ hΛ
  have hinc : Λ 1 - Λ 0 = (n : ℂ) * ((m : ℂ) * (2 * ↑Real.pi * Complex.I)) := by
    rw [hspec, hWc]; push_cast; ring
  have hΛ1 : Λ (1 : unitInterval)
      = Λ (0 : unitInterval) + (n : ℂ) * ((m : ℂ) * (2 * ↑Real.pi * Complex.I)) := by
    linear_combination hinc
  set g : ℝ → ℂ :=
    fun σ => Complex.exp (Λ (Set.projIcc (0 : ℝ) 1 h01 (σ / (2 * Real.pi))) / (n : ℂ)) with hg
  have hgc : Continuous g := by
    rw [hg]
    exact Complex.continuous_exp.comp (Continuous.div_const
      (Λ.continuous.comp (continuous_projIcc.comp (continuous_id.div_const _))) (n : ℂ))
  have hg0 : g 0 = Complex.exp (Λ (0 : unitInterval) / (n : ℂ)) := by
    have e : Set.projIcc (0 : ℝ) 1 h01 ((0 : ℝ) / (2 * Real.pi)) = (0 : unitInterval) := by
      rw [show (0 : ℝ) / (2 * Real.pi) = 0 by simp]
      rw [Set.projIcc_of_mem h01 (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)]
      exact Subtype.ext rfl
    show Complex.exp (Λ (Set.projIcc (0 : ℝ) 1 h01 ((0 : ℝ) / (2 * Real.pi))) / (n : ℂ))
      = Complex.exp (Λ (0 : unitInterval) / (n : ℂ))
    rw [e]
  have hgπ : g (2 * Real.pi) = Complex.exp (Λ (1 : unitInterval) / (n : ℂ)) := by
    have e : Set.projIcc (0 : ℝ) 1 h01 ((2 * Real.pi) / (2 * Real.pi)) = (1 : unitInterval) := by
      rw [show (2 * Real.pi) / (2 * Real.pi) = 1 by field_simp]
      rw [Set.projIcc_of_mem h01 (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by norm_num)]
      exact Subtype.ext rfl
    show Complex.exp (Λ (Set.projIcc (0 : ℝ) 1 h01 ((2 * Real.pi) / (2 * Real.pi))) / (n : ℂ))
      = Complex.exp (Λ (1 : unitInterval) / (n : ℂ))
    rw [e]
  have hkey : Λ (1 : unitInterval) / (n : ℂ)
      = Λ (0 : unitInterval) / (n : ℂ) + (m : ℂ) * (2 * ↑Real.pi * Complex.I) := by
    rw [hΛ1]
    field_simp
  have hg01 : g 0 = g (2 * Real.pi) := by
    rw [hg0, hgπ, hkey, Complex.exp_add, exp_int_mul_two_pi_I m, mul_one]
  let G : AddCircle (2 * Real.pi) → ℂ := AddCircle.liftIco (2 * Real.pi) 0 g
  have hGc : Continuous G :=
    AddCircle.liftIco_zero_continuous (p := 2 * Real.pi) hg01 hgc.continuousOn
  let η : C(ℝ, ℂ) :=
    ⟨fun τ : ℝ => G (τ : AddCircle (2 * Real.pi)), hGc.comp continuous_quotient_mk'⟩
  have hηper : Function.Periodic (fun t : ℝ => η t) (2 * Real.pi) := by
    intro t
    show G (((t + 2 * Real.pi : ℝ)) : AddCircle (2 * Real.pi))
      = G ((t : ℝ) : AddCircle (2 * Real.pi))
    rw [AddCircle.coe_add_period]
  have huIco : ∀ t : ℝ, toIcoMod h2π 0 t ∈ Set.Ico 0 (2 * Real.pi) := by
    intro t
    have h := toIcoMod_mem_Ico h2π 0 t
    rwa [zero_add] at h
  have huty : ∀ t : ℝ, t = toIcoMod h2π 0 t + (toIcoDiv h2π 0 t : ℝ) * (2 * Real.pi) := by
    intro t
    have h := toIcoMod_add_toIcoDiv_zsmul h2π 0 t
    rw [zsmul_eq_mul] at h
    linarith [h]
  have hgval : ∀ σ : ℝ, σ ∈ Set.Ico 0 (2 * Real.pi) → η σ = g σ := by
    intro σ hσ
    show G ((σ : ℝ) : AddCircle (2 * Real.pi)) = g σ
    exact AddCircle.liftIco_zero_coe_apply hσ
  have hηpow : ∀ t : ℝ, η t ^ n = γ t - z := by
    intro t
    set u : ℝ := toIcoMod h2π 0 t with hu
    have huI : u ∈ Set.Ico 0 (2 * Real.pi) := by rw [hu]; exact huIco t
    have hut : t = u + (toIcoDiv h2π 0 t : ℝ) * (2 * Real.pi) := by rw [hu]; exact huty t
    have hηu : η t = η u := by
      rw [hut]; exact (hηper.int_mul (toIcoDiv h2π 0 t)) u
    have htu : γ t = γ u := by
      rw [hut]; exact (hper.int_mul (toIcoDiv h2π 0 t)) u
    have hu2 : 2 * Real.pi * (u / (2 * Real.pi)) = u := by
      rw [mul_comm, div_mul_cancel₀ u (ne_of_gt h2π)]
    have hmem1 : u / (2 * Real.pi) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg huI.1 h2π.le, by rw [div_le_one h2π]; exact huI.2.le⟩
    have hgexp : g u = Complex.exp (Λ (⟨u / (2 * Real.pi), hmem1⟩ : unitInterval) / (n : ℂ)) := by
      show Complex.exp (Λ (Set.projIcc (0 : ℝ) 1 h01 (u / (2 * Real.pi))) / (n : ℂ))
        = Complex.exp (Λ (⟨u / (2 * Real.pi), hmem1⟩ : unitInterval) / (n : ℂ))
      rw [Set.projIcc_of_mem h01 hmem1]
    have hcurlift : Complex.exp (Λ (⟨u / (2 * Real.pi), hmem1⟩ : unitInterval)) = γ u - z := by
      have h := hΛ (⟨u / (2 * Real.pi), hmem1⟩ : unitInterval)
      rw [hc] at h
      simpa [curveLoop, hu2] using h
    have hpow : Complex.exp (Λ (⟨u / (2 * Real.pi), hmem1⟩ : unitInterval) / (n : ℂ)) ^ n
        = Complex.exp (Λ (⟨u / (2 * Real.pi), hmem1⟩ : unitInterval)) := by
      rw [← Complex.exp_nat_mul]
      congr 1
      field_simp
    rw [hηu, hgval u huI, hgexp, hpow, hcurlift, htu]
  have hηne : ∀ t : ℝ, η t ≠ 0 := by
    intro t ht
    have h := hηpow t
    rw [ht, zero_pow hneN] at h
    exact hz t (sub_eq_zero.mp h.symm)
  have hηwind : windNumber (fun t : ℝ => η t) η.continuous 0 = m := by
    set u : C(unitInterval, ℂ) :=
      curveLoop (fun t : ℝ => η t - 0) (η.continuous.sub continuous_const) with hu
    have hune : ∀ t, u t ≠ 0 := by
      intro t
      rw [hu]
      exact sub_ne_zero.mpr (by simpa using hηne (2 * Real.pi * (t : ℝ)))
    have huloop : u 0 = u 1 := by
      rw [hu]
      show η (2 * Real.pi * ((0 : unitInterval) : ℝ)) - 0
        = η (2 * Real.pi * ((1 : unitInterval) : ℝ)) - 0
      have h0 : 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by norm_num
      have h1 : 2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi := by norm_num
      have hper0 : η 0 = η (2 * Real.pi) := by simpa using (hηper 0).symm
      rw [h0, h1, sub_zero, sub_zero]
      exact hper0
    have hprod : ∀ t : unitInterval, (u ^ n) t = c t := by
      intro t
      rw [ContinuousMap.pow_apply, hu, hc]
      show (η (2 * Real.pi * (t : ℝ)) - 0) ^ n = γ (2 * Real.pi * (t : ℝ)) - z
      rw [sub_zero, hηpow]
    have hpune : ∀ t : unitInterval, (u ^ n) t ≠ 0 := fun t => pow_ne_zero n (hune t)
    have huloop' : (u ^ n) 0 = (u ^ n) 1 := by
      simp only [ContinuousMap.pow_apply]; rw [huloop]
    have hcongr := loopIndex_congr hprod hpune hcne huloop' hcloop
    have hwind : windNumber (fun t : ℝ => η t) η.continuous 0 = loopIndex u := rfl
    have hcancel : (n : ℤ) * loopIndex u = (n : ℤ) * m := by
      rw [← loopIndex_pow u hune huloop n, hcongr, hWc]
    have hnZ : (n : ℤ) ≠ 0 := by omega
    rw [hwind]
    exact mul_left_cancel₀ hnZ hcancel
  exact ⟨η, hηpow, hηne, hηper, hηwind⟩

/-- **The two components of the complement of a Jordan trace.**

For a curve `κ` which is a Jordan curve (`Continuous`, `2π`-periodic, injective on one period),
avoiding `0` and with the component of `0` in the complement of the trace *bounded*, the complement
of the trace has exactly two components: the component `K` of `0` (the bounded one) and the
component of a far point `w` (the unbounded one).  Concretely, the complement is covered by the two
components, they are disjoint and open, `K` is the frontier of nothing of its own (its frontier is
the trace) and the trace is preconnected.

The maximum of the norm on the trace is attained (at `t₀`), and it bounds `K`. -/
theorem exists_two_components {κ : ℝ → ℂ} (hκ : Continuous κ)
    (hper : Function.Periodic κ (2 * Real.pi)) (hinj : Set.InjOn κ (Set.Ico 0 (2 * Real.pi)))
    (h0 : (0 : ℂ) ∉ Set.range κ)
    (hbdd : Bornology.IsBounded (connectedComponentIn (Set.range κ)ᶜ (0 : ℂ))) :
    ∃ (R : ℝ) (w : ℂ) (t₀ : ℝ), (∀ t : ℝ, ‖κ t‖ ≤ R) ∧ ‖κ t₀‖ = R ∧ R < ‖w‖ ∧
      IsOpen (connectedComponentIn (Set.range κ)ᶜ (0 : ℂ)) ∧
      IsOpen (connectedComponentIn (Set.range κ)ᶜ w) ∧
      Disjoint (connectedComponentIn (Set.range κ)ᶜ (0 : ℂ))
        (connectedComponentIn (Set.range κ)ᶜ w) ∧
      (∀ p : ℂ, p ∉ Set.range κ → p ∈ connectedComponentIn (Set.range κ)ᶜ w ∪
        connectedComponentIn (Set.range κ)ᶜ (0 : ℂ)) ∧
      IsPreconnected (Set.range κ) ∧
      frontier (connectedComponentIn (Set.range κ)ᶜ (0 : ℂ)) = Set.range κ := by
  have hKcpt := Work.Topology.PlaneCurve.isCompact_range_of_periodic hκ hper
  obtain ⟨x₀, hx₀, hx₀max⟩ :=
    hKcpt.exists_isMaxOn ⟨κ 0, ⟨0, rfl⟩⟩ continuous_norm.continuousOn
  obtain ⟨t₀, ht₀⟩ := hx₀
  set R : ℝ := ‖κ t₀‖ with hRdef
  have hR : ∀ t : ℝ, ‖κ t‖ ≤ R := by
    intro t
    rw [hRdef, ht₀]
    exact hx₀max ⟨t, rfl⟩
  have hR0 : 0 ≤ R := by rw [hRdef]; exact norm_nonneg _
  set w : ℂ := ((R + 1 : ℝ) : ℂ) with hwdef
  have hwn : ‖w‖ = R + 1 := by
    rw [hwdef, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  have hwR : R < ‖w‖ := by rw [hwn]; linarith
  have hW : windNumber κ hκ 0 ≠ 0 :=
    windNumber_ne_zero_of_bounded_component hκ hper hinj h0 hbdd
  have hcl : IsClosed (Set.range κ) := hKcpt.isClosed
  have hKo : IsOpen (connectedComponentIn (Set.range κ)ᶜ (0 : ℂ)) :=
    hcl.isOpen_compl.connectedComponentIn
  have hWo : IsOpen (connectedComponentIn (Set.range κ)ᶜ w) :=
    hcl.isOpen_compl.connectedComponentIn
  have hwK : w ∉ Set.range κ := by
    rintro ⟨t, ht⟩
    have h1 := hR t
    rw [ht] at h1
    linarith [hwn]
  -- the far region is preconnected and contained in the component of `w`
  have hfar_sub : {u : ℂ | R < ‖u‖} ⊆ (Set.range κ)ᶜ := by
    intro u hu
    rintro ⟨t, ht⟩
    have h1 := hR t
    rw [ht] at h1
    exact absurd h1 (not_le.mpr hu)
  have hfarW : {u : ℂ | R < ‖u‖} ⊆ connectedComponentIn (Set.range κ)ᶜ w :=
    (Work.Smooth.JordanSeparation.isPreconnected_lt_norm_compl R hR0).subset_connectedComponentIn
      (by rw [Set.mem_setOf_eq, hwn]; linarith) hfar_sub
  -- the component of `w` is unbounded, hence different from the (bounded) component of `0`
  have hKne : connectedComponentIn (Set.range κ)ᶜ (0 : ℂ) ≠ connectedComponentIn (Set.range κ)ᶜ w := by
    intro heq
    have hb' : Bornology.IsBounded {u : ℂ | R < ‖u‖} := by
      rw [← heq] at hfarW
      exact hbdd.subset hfarW
    obtain ⟨M, hM⟩ := hb'.exists_norm_le
    set u : ℂ := ((max M (R + 1) + 1 : ℝ) : ℂ) with hudef
    have hun : ‖u‖ = max M (R + 1) + 1 := by
      rw [hudef, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ max M (R + 1) + 1)]
    have humem : u ∈ {u : ℂ | R < ‖u‖} := by
      rw [Set.mem_setOf_eq, hun]
      linarith [le_max_right M (R + 1)]
    have h1 := hM u humem
    rw [hun] at h1
    linarith [le_max_left M (R + 1)]
  have hdisj : Disjoint (connectedComponentIn (Set.range κ)ᶜ (0 : ℂ))
      (connectedComponentIn (Set.range κ)ᶜ w) := by
    rw [Set.disjoint_left]
    intro p hpK hpW
    refine hKne ?_
    exact (connectedComponentIn_eq hpK).trans (connectedComponentIn_eq hpW).symm
  have hcover := fun (p : ℂ) (hp : p ∉ Set.range κ) =>
    components_cover hκ hper hinj hR hwR h0 hW hp
  have hpre : IsPreconnected (Set.range κ) := isPreconnected_range hκ
  have hfr : frontier (connectedComponentIn (Set.range κ)ᶜ (0 : ℂ)) = Set.range κ :=
    Work.Topology.PlaneCurve.frontier_component_eq_range hκ hper hinj
      (not_isPreconnected_compl_of_windNumber_ne_zero hκ hper hR hwR h0 hW) 0 h0
  exact ⟨R, w, t₀, hR, rfl, hwR, hKo, hWo, hdisj, hcover, hpre, hfr⟩

/-- **Two disjoint Jordan traces enclosing `0` are nested.**  If the traces of two Jordan curves are
disjoint and `0` lies in a bounded complementary component of each, then one trace is contained in
the component of `0` of the complement of the other. -/
theorem jordanTracesDichotomy {η₁ η₂ : ℝ → ℂ}
    (hη₁ : Continuous η₁) (hper₁ : Function.Periodic η₁ (2 * Real.pi))
    (hinj₁ : Set.InjOn η₁ (Set.Ico 0 (2 * Real.pi))) (h0₁ : (0 : ℂ) ∉ Set.range η₁)
    (hbdd₁ : Bornology.IsBounded (connectedComponentIn (Set.range η₁)ᶜ (0 : ℂ)))
    (hη₂ : Continuous η₂) (hper₂ : Function.Periodic η₂ (2 * Real.pi))
    (hinj₂ : Set.InjOn η₂ (Set.Ico 0 (2 * Real.pi))) (h0₂ : (0 : ℂ) ∉ Set.range η₂)
    (hbdd₂ : Bornology.IsBounded (connectedComponentIn (Set.range η₂)ᶜ (0 : ℂ)))
    (hdisj : Disjoint (Set.range η₁) (Set.range η₂)) :
    Set.range η₁ ⊆ connectedComponentIn (Set.range η₂)ᶜ (0 : ℂ) ∨
      Set.range η₂ ⊆ connectedComponentIn (Set.range η₁)ᶜ (0 : ℂ) := by
  obtain ⟨R₁, w₁, t₁, hR₁, ht₁, hw₁R, hK₁o, hW₁o, hdisj₁, hcover₁, hpre₁, hfr₁⟩ :=
    exists_two_components hη₁ hper₁ hinj₁ h0₁ hbdd₁
  obtain ⟨R₂, w₂, t₂, hR₂, ht₂, hw₂R, hK₂o, hW₂o, hdisj₂, hcover₂, hpre₂, hfr₂⟩ :=
    exists_two_components hη₂ hper₂ hinj₂ h0₂ hbdd₂
  have hsub₁ : Set.range η₁ ⊆ connectedComponentIn (Set.range η₂)ᶜ w₂ ∪
      connectedComponentIn (Set.range η₂)ᶜ (0 : ℂ) := by
    intro p hp
    exact hcover₂ p (fun h => (Set.disjoint_left.mp hdisj) hp h)
  rcases hpre₁.subset_or_subset hW₂o hK₂o hdisj₂.symm hsub₁ with h | h
  · -- the first trace lies in the unbounded component of the second
    have hsub₂ : Set.range η₂ ⊆ connectedComponentIn (Set.range η₁)ᶜ w₁ ∪
        connectedComponentIn (Set.range η₁)ᶜ (0 : ℂ) := by
      intro p hp
      exact hcover₁ p (fun h => (Set.disjoint_left.mp hdisj) h hp)
    rcases hpre₂.subset_or_subset hW₁o hK₁o hdisj₁.symm hsub₂ with h' | h'
    · -- each trace lies in the unbounded component of the other: impossible
      have hK₂sub : connectedComponentIn (Set.range η₂)ᶜ (0 : ℂ) ⊆
          connectedComponentIn (Set.range η₁)ᶜ (0 : ℂ) := by
        refine IsPreconnected.subset_connectedComponentIn isPreconnected_connectedComponentIn
          (mem_connectedComponentIn h0₂) ?_
        intro p hp
        rintro hprange
        exact (Set.disjoint_left.mp hdisj₂) hp (h hprange)
      have hT₂sub : Set.range η₂ ⊆ connectedComponentIn (Set.range η₁)ᶜ (0 : ℂ) := by
        intro p hp
        have hpfr : p ∈ frontier (connectedComponentIn (Set.range η₂)ᶜ (0 : ℂ)) := by
          rw [hfr₂]; exact hp
        have hpcl : p ∈ closure (connectedComponentIn (Set.range η₁)ᶜ (0 : ℂ)) :=
          closure_mono hK₂sub (frontier_subset_closure hpfr)
        rw [closure_eq_interior_union_frontier, IsOpen.interior_eq hK₁o, hfr₁] at hpcl
        rcases hpcl with h1 | h1
        · exact h1
        · exact absurd h1 (fun hr => (Set.disjoint_left.mp hdisj) hr hp)
      exact absurd (hT₂sub ⟨0, rfl⟩) (fun hmem => (Set.disjoint_left.mp hdisj₁) hmem (h' ⟨0, rfl⟩))
    · exact Or.inr h'
  · exact Or.inl h

/-- **A Jordan curve enclosing `0` meets its rotation by any non-trivial root of unity.**

If `η` is a Jordan curve whose trace avoids `0` and whose complementary component of `0` is bounded,
and `ζ ≠ 1` satisfies `ζ ^ n = 1` for some `n ≥ 2`, then the trace of `η` meets the trace of the
rotated curve `t ↦ ζ * η t`: there are `s, t` with `η s = ζ * η t`.

This is the classical nesting statement for disjoint Jordan curves: two disjoint traces enclosing
`0` are nested (`jordanTracesDichotomy`), while a trace cannot be *strictly* inside its own rotation
because the rotation preserves norms — the norm-maximising point of the inner curve can be pushed
outwards inside the (open) region of the outer one, contradicting the norm bound for that region.
The case `ζ = -1` is the workspace's "antipodal" statement
(`antipodal_free_false_of_bounded_component`). -/
theorem jordanTraceMeetsRotation {η : ℝ → ℂ} (hη : Continuous η)
    (hper : Function.Periodic η (2 * Real.pi)) (hinj : Set.InjOn η (Set.Ico 0 (2 * Real.pi)))
    (h0 : (0 : ℂ) ∉ Set.range η)
    (hbdd : Bornology.IsBounded (connectedComponentIn (Set.range η)ᶜ (0 : ℂ)))
    {n : ℕ} (hn : 2 ≤ n) {ζ : ℂ} (hζ : ζ ^ n = 1) (hζ1 : ζ ≠ 1) :
    ∃ s t : ℝ, η s = ζ * η t := by
  by_contra hcon
  push Not at hcon
  have hn0 : n ≠ 0 := by omega
  have hζne : ζ ≠ 0 := by
    intro h
    rw [h, zero_pow hn0] at hζ
    exact one_ne_zero hζ.symm
  have hζnorm : ‖ζ‖ = 1 := by
    have h1 : ‖ζ‖ ^ n = 1 := by rw [← norm_pow, hζ, norm_one]
    rcases lt_trichotomy ‖ζ‖ 1 with h | h | h
    · exact absurd h1 (ne_of_lt (pow_lt_one₀ (norm_nonneg ζ) h hn0))
    · exact h
    · exact absurd h1 (ne_of_gt (one_lt_pow₀ h hn0))
  set κ : ℝ → ℂ := fun t => ζ * η t with hκdef
  have hκ : Continuous κ := continuous_const.mul hη
  have hκper : Function.Periodic κ (2 * Real.pi) := fun t => by simp [hκdef, hper t]
  have hκinj : Set.InjOn κ (Set.Ico 0 (2 * Real.pi)) := by
    intro a ha b hb hab
    refine hinj ha hb (mul_left_cancel₀ hζne ?_)
    simpa [hκdef] using hab
  have h0κ : (0 : ℂ) ∉ Set.range κ := by
    rintro ⟨t, ht⟩
    have h : η t = 0 := by
      have h2 : ζ * η t = 0 := by simpa [hκdef] using ht
      exact (mul_eq_zero.mp h2).resolve_left hζne
    exact h0 ⟨t, h⟩
  have hdisj : Disjoint (Set.range η) (Set.range κ) := by
    rw [Set.disjoint_left]
    rintro p ⟨s, hs⟩ ⟨t, ht⟩
    have hps : η s = p := hs
    have hpt : ζ * η t = p := by simpa [hκdef] using ht
    exact hcon s t (by rw [hps, hpt])
  obtain ⟨R, w, t₀, hR, htR, hwR, hKo, hWo, hdisjK, hcover, hpre, hfr⟩ :=
    exists_two_components hη hper hinj h0 hbdd
  have hW : windNumber η hη 0 ≠ 0 := windNumber_ne_zero_of_bounded_component hη hper hinj h0 hbdd
  have hKb : ∀ p ∈ connectedComponentIn (Set.range η)ᶜ (0 : ℂ), ‖p‖ ≤ R :=
    fun p hp => component_zero_bounded hη hper hinj hR hwR h0 hW hp
  have hK'o : IsOpen (connectedComponentIn (Set.range κ)ᶜ (0 : ℂ)) :=
    (Work.Topology.PlaneCurve.isCompact_range_of_periodic hκ hκper).isClosed.isOpen_compl.connectedComponentIn
  have hKp_eq : connectedComponentIn (Set.range κ)ᶜ (0 : ℂ) =
      (fun p => ζ * p) '' connectedComponentIn (Set.range η)ᶜ (0 : ℂ) := by
    refine Subset.antisymm ?_ ?_
    · have hpre' : IsPreconnected
          ((fun q => ζ⁻¹ * q) '' connectedComponentIn (Set.range κ)ᶜ (0 : ℂ)) :=
        isPreconnected_connectedComponentIn.image _ (continuous_const.mul continuous_id).continuousOn
      have hsub : ((fun q => ζ⁻¹ * q) '' connectedComponentIn (Set.range κ)ᶜ (0 : ℂ)) ⊆
          (Set.range η)ᶜ := by
        rintro p ⟨q, hq, rfl⟩
        rintro ⟨t, ht⟩
        have hq' : q ∈ Set.range κ := ⟨t, by
          show ζ * η t = q
          rw [ht, ← mul_assoc, mul_inv_cancel₀ hζne, one_mul]⟩
        exact (connectedComponentIn_subset _ _ hq) hq'
      have hK : ((fun q => ζ⁻¹ * q) '' connectedComponentIn (Set.range κ)ᶜ (0 : ℂ)) ⊆
          connectedComponentIn (Set.range η)ᶜ (0 : ℂ) :=
        IsPreconnected.subset_connectedComponentIn hpre'
          ⟨0, mem_connectedComponentIn h0κ, by simp⟩ hsub
      rintro q hq
      refine ⟨ζ⁻¹ * q, hK ⟨q, hq, rfl⟩, ?_⟩
      show ζ * (ζ⁻¹ * q) = q
      rw [← mul_assoc, mul_inv_cancel₀ hζne, one_mul]
    · refine IsPreconnected.subset_connectedComponentIn ?_ ?_ ?_
      · exact isPreconnected_connectedComponentIn.image _
          (continuous_const.mul continuous_id).continuousOn
      · exact ⟨0, mem_connectedComponentIn h0, by simp⟩
      · rintro q ⟨p, hp, rfl⟩
        rintro ⟨t, ht⟩
        have ht' : ζ * η t = ζ * p := by
          have h' : κ t = ζ * p := ht
          rw [hκdef] at h'
          exact h'
        exact (connectedComponentIn_subset _ _ hp) ⟨t, mul_left_cancel₀ hζne ht'⟩
  have hK'b_all : ∀ q ∈ connectedComponentIn (Set.range κ)ᶜ (0 : ℂ), ‖q‖ ≤ R := by
    intro q hq
    rw [hKp_eq] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    rw [Complex.norm_mul, hζnorm, one_mul]
    exact hKb p hp
  have hbddκ : Bornology.IsBounded (connectedComponentIn (Set.range κ)ᶜ (0 : ℂ)) :=
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)).subset (fun q hq => by
      rw [Metric.mem_closedBall, dist_zero_right]
      exact hK'b_all q hq)
  have bump : ∀ (S : Set ℂ), IsOpen S → (∀ q ∈ S, ‖q‖ ≤ R) → ∀ p ∈ S, ‖p‖ = R → p ≠ 0 →
      False := by
    intro S hSo hSb p hpS hpnorm hp0
    have hpos : 0 < ‖p‖ := norm_pos_iff.mpr hp0
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hSo p hpS
    set δ : ℝ := ε / (2 * ‖p‖) with hδdef
    have hδpos : 0 < δ := by rw [hδdef]; positivity
    set p' : ℂ := p * ((1 + δ : ℝ) : ℂ) with hp'def
    have hmem : p' ∈ S := by
      apply hball
      rw [Metric.mem_ball, dist_eq_norm]
      have hdiff : p' - p = p * ((δ : ℝ) : ℂ) := by
        rw [hp'def]; push_cast; ring
      rw [hdiff, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
      have hε2 : ‖p‖ * δ = ε / 2 := by rw [hδdef]; field_simp
      rw [hε2]; linarith
    have hbig : R < ‖p'‖ := by
      rw [hp'def, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by linarith : (0 : ℝ) < 1 + δ), hpnorm]
      nlinarith [hδpos]
    exact absurd (hSb p' hmem) (not_le.mpr hbig)
  have hdich := jordanTracesDichotomy hη hper hinj h0 hbdd hκ hκper hκinj h0κ hbddκ hdisj
  rcases hdich with hcase | hcase
  · exact bump _ hK'o hK'b_all (η t₀) (hcase ⟨t₀, rfl⟩) htR (fun h => h0 ⟨t₀, h⟩)
  · have hκt₀ : ‖κ t₀‖ = R := by
      rw [hκdef, Complex.norm_mul, hζnorm, one_mul]; exact htR
    exact bump _ hKo hKb (κ t₀) (hcase ⟨t₀, rfl⟩) hκt₀ (fun h => h0κ ⟨t₀, h⟩)

theorem jordanLoopIndexOne {γ : ℝ → ℂ} (hγ : Continuous γ)
    (hper : Function.Periodic γ (2 * Real.pi)) (hinj : Set.InjOn γ (Set.Ico 0 (2 * Real.pi)))
    (h0 : (0 : ℂ) ∉ Set.range γ)
    (hbdd : Bornology.IsBounded (connectedComponentIn (Set.range γ)ᶜ (0 : ℂ))) :
    ∃ c : C(unitInterval, ℂ), (∀ t, c t ∈ Set.range γ) ∧ c 0 = c 1 ∧
      Work.Smooth.SphereJordan.loopIndex c = 1 := by
  set k : ℤ := windNumber γ hγ 0 with hk
  have hkne : k ≠ 0 := windNumber_ne_zero_of_bounded_component hγ hper hinj h0 hbdd
  -- the loop traced by `γ`
  set c₀ : C(unitInterval, ℂ) := curveLoop (fun t : ℝ => γ t - 0) (hγ.sub continuous_const) with hc₀
  have hc₀ne : ∀ t : unitInterval, c₀ t ≠ 0 := by
    intro t
    rw [hc₀]
    exact sub_ne_zero.mpr (fun h => h0 ⟨2 * Real.pi * (t : ℝ), h⟩)
  have hc₀loop : c₀ 0 = c₀ 1 := by
    rw [hc₀]
    show γ (2 * Real.pi * ((0 : unitInterval) : ℝ)) - 0
      = γ (2 * Real.pi * ((1 : unitInterval) : ℝ)) - 0
    have h0' : 2 * Real.pi * ((0 : unitInterval) : ℝ) = 0 := by norm_num
    have h1' : 2 * Real.pi * ((1 : unitInterval) : ℝ) = 2 * Real.pi := by norm_num
    rw [h0', h1', sub_zero, sub_zero]
    simpa using (hper 0).symm
  have hc₀idx : loopIndex c₀ = k := rfl
  by_cases hk1 : k = 1
  · refine ⟨c₀, ?_, hc₀loop, by rw [hc₀idx, hk1]⟩
    intro t
    refine ⟨2 * Real.pi * (t : ℝ), ?_⟩
    rw [hc₀]
    simp [curveLoop]
  · -- `k ≠ 1`: the index must be `-1`
    have hkm1 : k = -1 := by
      by_contra hkm1
      set n : ℕ := k.natAbs with hn
      have hn2 : 2 ≤ n := by omega
      have hn1 : 1 ≤ n := by omega
      set m : ℤ := if 0 < k then 1 else -1 with hm
      have hm_ne : m ≠ 0 := by rw [hm]; split_ifs <;> norm_num
      have hkm : windNumber γ hγ 0 = (n : ℤ) * m := by
        rw [← hk]
        by_cases hkpos : 0 < k
        · have h1 : k = (n : ℤ) := by omega
          rw [h1]; simp [hm, hkpos]
        · have h1 : k = -(n : ℤ) := by omega
          rw [h1]; simp [hm, hkpos]
      obtain ⟨η, hηpow, hηne, hηper, hηwind⟩ :=
        exists_powCurve_of_windNumber hγ hper (z := 0) (fun t ht => h0 ⟨t, ht⟩) hn1 hkm
      -- `η` is again a Jordan curve
      have hηinj : Set.InjOn η (Set.Ico 0 (2 * Real.pi)) := by
        intro a ha b hb hab
        have hγab : γ a = γ b := by
          have h1 : η a ^ n = η b ^ n := by rw [hab]
          rw [hηpow a, hηpow b] at h1
          simpa using h1
        obtain ⟨j, hj⟩ := exists_int_sub_eq_of_periodic_injOn hper hinj hγab
        have hlt : |a - b| < 2 * Real.pi := by
          rw [abs_lt]
          constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
        rcases lt_trichotomy j 0 with hj0 | hj0 | hj0
        · have hjz : j ≠ 0 := by omega
          have h3 : (1 : ℝ) ≤ |(j : ℝ)| := by
            rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hjz
          have h2πpos : (0 : ℝ) < 2 * Real.pi := by positivity
          have h4 : 2 * Real.pi ≤ |a - b| := by
            rw [hj, abs_mul, abs_of_pos h2πpos]
            calc 2 * Real.pi = 1 * (2 * Real.pi) := (one_mul _).symm
              _ ≤ |(j : ℝ)| * (2 * Real.pi) := mul_le_mul_of_nonneg_right h3 h2πpos.le
          linarith
        · rw [hj0] at hj; simp at hj; linarith
        · have hjz : j ≠ 0 := by omega
          have h3 : (1 : ℝ) ≤ |(j : ℝ)| := by
            rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hjz
          have h2πpos : (0 : ℝ) < 2 * Real.pi := by positivity
          have h4 : 2 * Real.pi ≤ |a - b| := by
            rw [hj, abs_mul, abs_of_pos h2πpos]
            calc 2 * Real.pi = 1 * (2 * Real.pi) := (one_mul _).symm
              _ ≤ |(j : ℝ)| * (2 * Real.pi) := mul_le_mul_of_nonneg_right h3 h2πpos.le
          linarith
      have h0η : (0 : ℂ) ∉ Set.range η := fun h => h.elim (fun t ht => hηne t ht)
      have hηbdd : Bornology.IsBounded (connectedComponentIn (Set.range η)ᶜ (0 : ℂ)) :=
        isBounded_componentIn_zero_of_windNumber_ne_zero η.continuous hηper h0η
          (by rw [hηwind]; exact hm_ne)
      -- the primitive `n`-th root of unity
      set ζ : ℂ := Complex.exp (((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I) with hζdef
      have hζn : ζ ^ n = 1 := by
        rw [hζdef, ← Complex.exp_nat_mul]
        rw [show (n : ℂ) * (((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I)
            = (((n : ℝ) * (2 * Real.pi / (n : ℝ)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
        rw [show (n : ℝ) * (2 * Real.pi / (n : ℝ)) = 2 * Real.pi by field_simp]
        exact Complex.exp_eq_one_iff.mpr ⟨1, by push_cast; ring⟩
      have hζ1 : ζ ≠ 1 := by
        intro hζone
        have hexp : Complex.exp (((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I) = 1 := by
          rw [← hζdef]; exact hζone
        obtain ⟨j, hj⟩ := Complex.exp_eq_one_iff.mp hexp
        have hzero : 2 * Real.pi / (n : ℝ) = (j : ℝ) * (2 * Real.pi) := by
          have h := congrArg Complex.im hj
          simp [Complex.mul_im] at h
          exact h
        have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
        have hnj : (n : ℝ) * (j : ℝ) = 1 := by
          have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
          field_simp at hzero
          nlinarith [hzero, Real.pi_pos]
        have hjpos : 0 < (j : ℝ) := by nlinarith [hnj, hnpos]
        have hj0Z : (0 : ℤ) < j := by exact_mod_cast hjpos
        have hj1 : (1 : ℤ) ≤ j := by omega
        have hj1' : (1 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj1
        have hn2' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
        nlinarith [hnj, hj1', hn2']
      obtain ⟨s, t, hst⟩ :=
        jordanTraceMeetsRotation η.continuous hηper hηinj h0η hηbdd hn2 hζn hζ1
      have hγst : γ s = γ t := by
        have h1 : η s ^ n = η t ^ n := by
          rw [hst, mul_pow, hζn, one_mul]
        rw [hηpow s, hηpow t] at h1
        simpa using h1
      obtain ⟨j, hj⟩ := exists_int_sub_eq_of_periodic_injOn hper hinj hγst
      have hηst : η s = η t := by
        have hs : s = t + (j : ℝ) * (2 * Real.pi) := by linarith [hj]
        rw [hs]
        exact (hηper.int_mul j) t
      have hζη : η t = 0 := by
        have h2 : η t = ζ * η t := by rw [← hst, hηst]
        have h3 : (1 - ζ) * η t = 0 := by
          rw [sub_mul, one_mul, sub_eq_zero]
          exact h2
        rcases mul_eq_zero.mp h3 with h4 | h4
        · exact absurd (sub_eq_zero.mp h4) (Ne.symm hζ1)
        · exact h4
      exact hηne t hζη
    -- the reversed loop has index `-k = 1`
    let p : Path (c₀ 0) (c₀ 0) := ⟨c₀, rfl, hc₀loop.symm⟩
    refine ⟨(p.symm : C(unitInterval, ℂ)), ?_, ?_, ?_⟩
    · intro t
      have hval : (p.symm : C(unitInterval, ℂ)) t = c₀ (unitInterval.symm t) := rfl
      rw [hval, hc₀]
      exact ⟨2 * Real.pi * ((unitInterval.symm t : unitInterval) : ℝ), by simp [curveLoop]⟩
    · show ((p.symm : C(unitInterval, ℂ)) 0) = ((p.symm : C(unitInterval, ℂ)) 1)
      rw [show ((p.symm : C(unitInterval, ℂ)) 0) = p.symm 0 from rfl, Path.source,
        show ((p.symm : C(unitInterval, ℂ)) 1) = p.symm 1 from rfl, Path.target]
    · have hsymm := loopIndex_symm p (fun t => hc₀ne t)
      have hp_idx : loopIndex (p : C(unitInterval, ℂ)) = k := hc₀idx
      rw [hsymm, hp_idx, hkm1]
      norm_num

end Work.Smooth.SphereJordan
