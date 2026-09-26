import Mathlib
import Submission.Work.RadialSpace.Basic
import Submission.Work.RadialSpace.contDiff_glue
import Submission.Work.RadialSpace.borel_lemma
import Submission.Work.Radial.exp_mul_decay_smooth
import Submission.Work.Radial.cutoff_deriv_bound
import Submission.Work.Radial.Basic

/-!
# One-sided approximation by a compactly supported smooth function

`Work.Radial.exp_approx_smooth` is the one-sided approximation lemma with the smoothness
class `∞` (= `C^∞`, *not* the analytic class): given `Ξ : ℝ → ℂ` which is `C^∞` on
`[0, ∞)` and whose one-sided iterated derivatives decay faster than any polynomial after
multiplication by `exp (π y t)` (`y > 0`), and given `J K : ℕ`, `ε > 0`, there is a
compactly supported smooth `h : ℝ → ℂ` such that `exp (-π y t) * (Ξ - h)` is small in the
weighted `C^J` norm on `[0, ∞)`.

The proof is self-contained here: it glues the one-sided smooth `Ξ` to a smooth function on
all of `ℝ` (Borel's lemma, `Work.RadialSpace.borel_lemma`, together with
`Work.RadialSpace.contDiff_glue`), multiplies by a fixed-shape smooth cutoff
(`Real.smoothTransition`), and uses the decay of `Ξ`, transported to
`s ↦ exp (-π y s) * Ξ s` by `Work.Radial.exp_mul_decay_smooth`, to control the transition
region.
-/

namespace Work.Radial

open Filter Topology Set
open scoped Topology ContDiff

/-- A smooth compactly supported complex-valued function has uniformly bounded iterated
derivatives (the `∞`-analogue of `Work.Radial.bounded_iteratedDeriv_compact`). -/
theorem bounded_iteratedDeriv_compact_of_smooth (ψ : ℝ → ℂ) (hsm : ContDiff ℝ ∞ ψ)
    (hc : HasCompactSupport ψ) (J : ℕ) :
    ∃ C : ℝ, ∀ m : ℕ, m ≤ J → ∀ t : ℝ, ‖iteratedDeriv m ψ t‖ ≤ C := by
  have hcs : ∀ m : ℕ, HasCompactSupport (iteratedDeriv m ψ) := by
    intro m
    induction m with
    | zero => simpa using hc
    | succ n ih => rw [iteratedDeriv_succ]; exact ih.deriv
  have hcont : ∀ m : ℕ, Continuous (iteratedDeriv m ψ) := fun m =>
    hsm.continuous_iteratedDeriv m (Work.RadialSpace.natCast_le_smooth m)
  choose Cb hCb using fun m => (hcs m).exists_bound_of_continuous (hcont m)
  refine ⟨∑ m ∈ Finset.range (J + 1), max (Cb m) 0, ?_⟩
  intro m hm t
  have hmem : m ∈ Finset.range (J + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le hm)
  calc ‖iteratedDeriv m ψ t‖ ≤ Cb m := hCb m t
    _ ≤ max (Cb m) 0 := le_max_left _ _
    _ ≤ ∑ i ∈ Finset.range (J + 1), max (Cb i) 0 :=
        Finset.single_le_sum (fun i _ => le_max_right _ _) hmem

/-- **One-sided approximation by a compactly supported smooth function.**

Let `Ξ : ℝ → ℂ` be `C^∞` on `[0, ∞)` with all one-sided derivatives decaying faster than any
polynomial after multiplication by `exp (π y t)`. Then for every `J`, `K` and `ε > 0` there is
a compactly supported smooth `h` with `exp (-π y t) (Ξ - h)` small in the weighted `C^J`
norm on `[0, ∞)`. -/

theorem exp_approx_smooth (y : ℝ) (hy : 0 < y) (Ξ : ℝ → ℂ)
    (hsm : ContDiffOn ℝ ∞ Ξ (Set.Ici 0))
    (hdec : ∀ j K : ℕ, ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      (1 + t) ^ K * Real.exp (-(Real.pi * y * t)) *
        ‖iteratedDerivWithin j Ξ (Set.Ici 0) t‖ ≤ ε)
    (J K : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ h : ℝ → ℂ, ContDiff ℝ ∞ h ∧ (∃ R : ℝ, ∀ t : ℝ, R ≤ |t| → h t = 0) ∧
      ∀ j : ℕ, j ≤ J → ∀ t : ℝ, 0 ≤ t →
        (1 + t) ^ K * ‖iteratedDerivWithin j
          (fun s : ℝ => Real.exp (-(Real.pi * y * s)) * (Ξ s - h s)) (Set.Ici 0) t‖ ≤ ε
    := by
  -- ## Uniform bound on the derivatives of the cutoff, and the numerical constants
  obtain ⟨B, hBnn, hB⟩ := cutoff_deriv_bound J
  have hB1 : 0 ≤ 1 + B := by linarith
  set Sb : ℝ := ∑ i ∈ Finset.range (J + 1), ((J.choose i : ℕ) : ℝ) * (1 + B) with hSbdef
  have hSb0 : 0 ≤ Sb := by rw [hSbdef]; positivity
  set D : ℝ := Sb + 1 with hDdef
  have hDpos : 0 < D := by rw [hDdef]; linarith
  set δ : ℝ := ε / D with hδdef
  have hδpos : 0 < δ := div_pos hε hDpos
  -- ## Decay of the Gaussian-weighted function
  obtain ⟨T₀, hT₀⟩ := exp_mul_decay_smooth y hy Ξ hsm hdec J K hδpos
  set T : ℝ := max T₀ 1 with hTdef
  have hT1 : 1 ≤ T := by rw [hTdef]; exact le_max_right _ _
  have hT0T : T₀ ≤ T := by rw [hTdef]; exact le_max_left _ _
  have hTpos : 0 < T := by linarith
  -- ## The cutoff
  set ρ : ℝ → ℂ := fun s => ((Real.smoothTransition (s + 1) *
      Real.smoothTransition (T + 2 - s) : ℝ) : ℂ) with hρdef
  have hσ : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff (n := ⊤)
  have hρsm : ContDiff ℝ ∞ ρ := by
    rw [hρdef]
    exact Complex.ofRealCLM.contDiff.comp
      ((hσ.comp (contDiff_id.add contDiff_const)).mul (hσ.comp (contDiff_const.sub contDiff_id)))
  have hρb : ∀ m : ℕ, m ≤ J → ∀ t : ℝ, ‖iteratedDeriv m ρ t‖ ≤ B := by
    intro m hm t
    rw [hρdef]
    exact hB T m hm t
  have hρ_one : ∀ s : ℝ, 0 ≤ s → s ≤ T → ρ s = 1 := by
    intro s h0 hT
    have h1 : Real.smoothTransition (s + 1) = 1 :=
      Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ s + 1)
    have h2 : Real.smoothTransition (T + 2 - s) = 1 :=
      Real.smoothTransition.one_of_one_le (by linarith : (1:ℝ) ≤ T + 2 - s)
    show ((Real.smoothTransition (s + 1) * Real.smoothTransition (T + 2 - s) : ℝ) : ℂ) = 1
    rw [h1, h2]
    norm_num
  have hρ_zero_left : ∀ s : ℝ, s ≤ -1 → ρ s = 0 := by
    intro s hs
    have h1 : Real.smoothTransition (s + 1) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by linarith : s + 1 ≤ 0)
    show ((Real.smoothTransition (s + 1) * Real.smoothTransition (T + 2 - s) : ℝ) : ℂ) = 0
    rw [h1, zero_mul, Complex.ofReal_zero]
  have hρ_zero_right : ∀ s : ℝ, T + 2 ≤ s → ρ s = 0 := by
    intro s hs
    have h1 : Real.smoothTransition (T + 2 - s) = 0 :=
      Real.smoothTransition.zero_of_nonpos (by linarith : T + 2 - s ≤ 0)
    show ((Real.smoothTransition (s + 1) * Real.smoothTransition (T + 2 - s) : ℝ) : ℂ) = 0
    rw [h1, mul_zero, Complex.ofReal_zero]
  -- ## A smooth extension of `Ξ` to all of `ℝ`
  set b : ℕ → ℂ := fun m => iteratedDerivWithin m Ξ (Set.Ici 0) 0 with hbdef
  obtain ⟨W, hWsm, hWderiv⟩ := Work.RadialSpace.borel_lemma b
  have hjet : ∀ m : ℕ, Tendsto (iteratedDeriv m Ξ) (nhdsWithin (0 : ℝ) (Ioi 0))
      (nhds (iteratedDeriv m W 0)) := by
    intro m
    rw [hWderiv m]
    have hcont : ContinuousOn (iteratedDerivWithin m Ξ (Set.Ici 0)) (Set.Ici 0) :=
      hsm.continuousOn_iteratedDerivWithin (m := m)
        (Work.RadialSpace.natCast_le_smooth m) (uniqueDiffOn_Ici 0)
    have h1 : Tendsto (iteratedDerivWithin m Ξ (Set.Ici 0)) (nhdsWithin (0 : ℝ) (Set.Ici 0))
        (nhds (iteratedDerivWithin m Ξ (Set.Ici 0) 0)) :=
      hcont.continuousWithinAt (Set.mem_Ici.mpr le_rfl)
    have h2 : Tendsto (iteratedDerivWithin m Ξ (Set.Ici 0)) (nhdsWithin (0 : ℝ) (Ioi 0))
        (nhds (iteratedDerivWithin m Ξ (Set.Ici 0) 0)) :=
      h1.mono_left (nhdsWithin_mono 0 Set.Ioi_subset_Ici_self)
    have heq : (iteratedDerivWithin m Ξ (Set.Ici 0)) =ᶠ[nhdsWithin (0 : ℝ) (Ioi 0)]
        (iteratedDeriv m Ξ) := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0)
        ((hsm.contDiffAt (Ici_mem_nhds hs)).of_le (Work.RadialSpace.natCast_le_smooth m))
        (Set.mem_Ici.mpr hs.le)
    exact Tendsto.congr' heq h2
  set Xe : ℝ → ℂ := fun s => if 0 < s then Ξ s else W s with hXedef
  have hXesm : ContDiff ℝ ∞ Xe :=
    Work.RadialSpace.contDiff_glue (hsm.mono Set.Ioi_subset_Ici_self) hWsm hjet
  have hXe_eq : ∀ s : ℝ, 0 ≤ s → Xe s = Ξ s := by
    intro s hs
    rw [hXedef]
    rcases lt_or_eq_of_le hs with h | h
    · simp only [if_pos h]
    · subst h
      simp only [lt_irrefl, if_false]
      have h0 : W 0 = b 0 := by
        have := hWderiv 0
        simpa using this
      rw [h0, hbdef]
      simp
  -- ## The candidate and its two easy properties
  refine ⟨fun s => ρ s * Xe s, hρsm.mul hXesm, ?_, ?_⟩
  · refine ⟨T + 3, fun t ht => ?_⟩
    have ht' : |t| ≥ T + 3 := ht
    rcases le_abs.mp ht' with h | h
    · change ρ t * Xe t = 0
      rw [hρ_zero_right t (by linarith : T + 2 ≤ t), zero_mul]
    · change ρ t * Xe t = 0
      rw [hρ_zero_left t (by linarith : t ≤ -1), zero_mul]
  · -- ## The weighted bound
    have hGh_eq : Set.EqOn
        (fun s : ℝ => Real.exp (-(Real.pi * y * s)) * (Ξ s - ρ s * Xe s))
        (fun s : ℝ => (1 - ρ s) * ((Real.exp (-(Real.pi * y * s)) : ℂ) * Ξ s)) (Set.Ici 0) := by
      intro s hs
      show (Real.exp (-(Real.pi * y * s)) : ℂ) * (Ξ s - ρ s * Xe s)
        = (1 - ρ s) * ((Real.exp (-(Real.pi * y * s)) : ℂ) * Ξ s)
      rw [hXe_eq s hs]
      ring
    intro j hj t ht
    by_cases htT : T ≤ t
    · -- ## `t ≥ T`: Leibniz plus the decay estimate
      have ht0 : (0 : ℝ) ≤ t := le_trans hTpos.le htT
      have hmem : t ∈ Set.Ici (0 : ℝ) := ht0
      have hcongr := iteratedDerivWithin_congr (n := j) hGh_eq hmem
      rw [hcongr]
      -- put the second factor into product form so that the Leibniz rule applies
      set A : ℕ → ℂ := fun i => iteratedDerivWithin i (fun s : ℝ => 1 - ρ s) (Set.Ici 0) t
        with hAdef
      set Bc : ℕ → ℂ := fun i => iteratedDerivWithin i
        (fun s : ℝ => (Real.exp (-(Real.pi * y * s)) : ℂ) * Ξ s) (Set.Ici 0) t with hBcdef
      have hunit : ContDiffWithinAt ℝ (j : ℕ∞ω) (fun s : ℝ => 1 - ρ s) (Set.Ici 0) t :=
        ((contDiff_const.sub hρsm).contDiffWithinAt).of_le (Work.RadialSpace.natCast_le_smooth j)
      have hexp : ContDiffWithinAt ℝ (j : ℕ∞ω)
          (fun s : ℝ => (Real.exp (-(Real.pi * y * s)) : ℂ)) (Set.Ici 0) t := by
        have h1 : ContDiff ℝ ∞ (fun s : ℝ => -(Real.pi * y * s)) := by fun_prop
        have h3 := Complex.ofRealCLM.contDiff.comp ((Real.contDiff_exp (n := ∞)).comp h1)
        have h4 : ContDiff ℝ ∞ (fun s : ℝ => (Real.exp (-(Real.pi * y * s)) : ℂ)) := by
          simpa [Function.comp_def] using h3
        exact h4.contDiffWithinAt.of_le (Work.RadialSpace.natCast_le_smooth j)
      have hXi : ContDiffWithinAt ℝ (j : ℕ∞ω) Ξ (Set.Ici 0) t :=
        (hsm.contDiffWithinAt hmem).of_le (Work.RadialSpace.natCast_le_smooth j)
      have hFd : ContDiffWithinAt ℝ (j : ℕ∞ω)
          (fun s : ℝ => (Real.exp (-(Real.pi * y * s)) : ℂ) * Ξ s) (Set.Ici 0) t :=
        hexp.mul hXi
      change (1 + t) ^ K * ‖iteratedDerivWithin j
        ((fun s : ℝ => 1 - ρ s) *
          (fun s : ℝ => (Real.exp (-(Real.pi * y * s)) : ℂ) * Ξ s)) (Set.Ici 0) t‖ ≤ ε
      rw [iteratedDerivWithin_mul (x := t) (s := Set.Ici 0) (n := j) hmem
        (uniqueDiffOn_Ici 0) hunit hFd]
      -- bounds on the two families of factors
      have hAb : ∀ i : ℕ, i ≤ j → ‖A i‖ ≤ 1 + B := by
        intro i hij
        have hiJ : i ≤ J := le_trans hij hj
        change ‖iteratedDerivWithin i (fun s : ℝ => 1 - ρ s) (Set.Ici 0) t‖ ≤ 1 + B
        have hwit : iteratedDerivWithin i (fun s : ℝ => 1 - ρ s) (Set.Ici 0) t
            = iteratedDeriv i (fun s : ℝ => 1 - ρ s) t :=
          iteratedDerivWithin_eq_iteratedDeriv (uniqueDiffOn_Ici 0)
            ((contDiff_const.sub hρsm).contDiffAt.of_le (Work.RadialSpace.natCast_le_smooth i))
            hmem
        rw [hwit]
        rcases Nat.eq_zero_or_pos i with hi0 | hipos
        · subst hi0
          rw [iteratedDeriv_zero]
          have hb := hρb 0 (Nat.zero_le J) t
          simp only [iteratedDeriv_zero] at hb
          calc ‖(1 : ℂ) - ρ t‖ ≤ ‖(1 : ℂ)‖ + ‖ρ t‖ := norm_sub_le _ _
            _ = 1 + ‖ρ t‖ := by rw [norm_one]
            _ ≤ 1 + B := by linarith
        · have hsub : iteratedDeriv i (fun s : ℝ => 1 - ρ s) t = - iteratedDeriv i ρ t := by
            rw [iteratedDeriv_const_sub (f := ρ) hipos (1 : ℂ)]
            simp
          rw [hsub, norm_neg]
          exact le_trans (hρb i hiJ t) (by linarith)
      have hBcb : ∀ i : ℕ, i ≤ j → (1 + t) ^ K * ‖Bc (j - i)‖ ≤ δ := by
        intro i hij
        have hji : j - i ≤ J := by omega
        change (1 + t) ^ K * ‖iteratedDerivWithin (j - i)
          (fun s : ℝ => (Real.exp (-(Real.pi * y * s)) : ℂ) * Ξ s) (Set.Ici 0) t‖ ≤ δ
        exact hT₀ t (le_trans hT0T htT) (j - i) hji
      -- the per-term estimate
      have hper : ∀ i ∈ Finset.range (j + 1),
          (1 + t) ^ K * ‖((j.choose i : ℕ) : ℂ) * A i * Bc (j - i)‖
            ≤ ((j.choose i : ℕ) : ℝ) * (1 + B) * δ := by
        intro i hi
        have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
        have hCi : (0:ℝ) ≤ ((j.choose i : ℕ) : ℝ) := Nat.cast_nonneg _
        have hAi : ‖A i‖ ≤ 1 + B := hAb i hij
        have hBi : (1 + t) ^ K * ‖Bc (j - i)‖ ≤ δ := hBcb i hij
        rw [norm_mul, norm_mul]
        simp only [norm_natCast]
        calc (1 + t) ^ K * (((j.choose i : ℕ) : ℝ) * ‖A i‖ * ‖Bc (j - i)‖)
            = ((j.choose i : ℕ) : ℝ) * ‖A i‖ * ((1 + t) ^ K * ‖Bc (j - i)‖) := by ring
          _ ≤ ((j.choose i : ℕ) : ℝ) * (1 + B) * δ := by
              apply mul_le_mul
              · exact mul_le_mul_of_nonneg_left hAi hCi
              · exact hBi
              · positivity
              · positivity
      -- sum over the range, then extend the range and use binomial monotonicity
      have hsum1 : (1 + t) ^ K * ‖∑ i ∈ Finset.range (j + 1),
            ((j.choose i : ℕ) : ℂ) * A i * Bc (j - i)‖
          ≤ ∑ i ∈ Finset.range (j + 1), ((j.choose i : ℕ) : ℝ) * (1 + B) * δ := by
        calc (1 + t) ^ K * ‖∑ i ∈ Finset.range (j + 1),
              ((j.choose i : ℕ) : ℂ) * A i * Bc (j - i)‖
            ≤ (1 + t) ^ K * ∑ i ∈ Finset.range (j + 1),
              ‖((j.choose i : ℕ) : ℂ) * A i * Bc (j - i)‖ :=
              mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
          _ = ∑ i ∈ Finset.range (j + 1),
              (1 + t) ^ K * ‖((j.choose i : ℕ) : ℂ) * A i * Bc (j - i)‖ := by
              rw [Finset.mul_sum]
          _ ≤ ∑ i ∈ Finset.range (j + 1), ((j.choose i : ℕ) : ℝ) * (1 + B) * δ :=
              Finset.sum_le_sum hper
      have hchoose : (∑ i ∈ Finset.range (j + 1), ((j.choose i : ℕ) : ℝ) * (1 + B) * δ)
          ≤ Sb * δ := by
        rw [hSbdef, ← Finset.sum_mul]
        apply mul_le_mul_of_nonneg_right _ hδpos.le
        calc (∑ i ∈ Finset.range (j + 1), ((j.choose i : ℕ) : ℝ) * (1 + B))
            ≤ ∑ i ∈ Finset.range (j + 1), ((J.choose i : ℕ) : ℝ) * (1 + B) := by
              apply Finset.sum_le_sum
              intro i hi
              have hij : i ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
              exact mul_le_mul_of_nonneg_right
                (by exact_mod_cast Nat.choose_le_choose (c := i) hj) hB1
          _ ≤ ∑ i ∈ Finset.range (J + 1), ((J.choose i : ℕ) : ℝ) * (1 + B) := by
              apply Finset.sum_le_sum_of_subset_of_nonneg
              · exact Finset.range_mono (Nat.succ_le_succ hj)
              · intro i _ _
                positivity
      have hfin : Sb * δ ≤ ε := by
        have hSD : Sb ≤ D := by rw [hDdef]; linarith
        calc Sb * δ ≤ D * δ := mul_le_mul_of_nonneg_right hSD hδpos.le
          _ = ε := by rw [hδdef, ← mul_div_assoc, mul_div_cancel_left₀ ε hDpos.ne']
      exact le_trans hsum1 (le_trans hchoose hfin)
    · -- ## `t < T`: the function vanishes identically near `t`
      have hlt : t < T := lt_of_not_ge htT
      have hGzero : (fun s : ℝ => Real.exp (-(Real.pi * y * s)) * (Ξ s - ρ s * Xe s))
          =ᶠ[nhdsWithin t (Set.Ici (0:ℝ))] (0 : ℝ → ℂ) := by
        have hGev : ∀ᶠ s in nhdsWithin t (Set.Ici (0:ℝ)),
            (fun s : ℝ => Real.exp (-(Real.pi * y * s)) * (Ξ s - ρ s * Xe s)) s
              = (0 : ℝ → ℂ) s := by
          rw [eventually_nhdsWithin_iff]
          have hε' : 0 < T - t := by linarith
          filter_upwards [Metric.ball_mem_nhds t hε'] with s hs hsI
          have hsle : s ≤ T := by
            rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
            linarith [hs.2]
          have hs0 : 0 ≤ s := hsI
          change Real.exp (-(Real.pi * y * s)) * (Ξ s - ρ s * Xe s) = 0
          rw [hρ_one s hs0 hsle, hXe_eq s hs0]
          ring
        exact hGev
      have hGz : (fun s : ℝ => Real.exp (-(Real.pi * y * s)) * (Ξ s - ρ s * Xe s))
          =ᶠ[nhdsWithin t (insert t (Set.Ici (0:ℝ)))] (0 : ℝ → ℂ) := by
        rw [insert_eq_of_mem (Set.mem_Ici.mpr ht)]
        exact hGzero
      have hz : iteratedDerivWithin j
          (fun s : ℝ => Real.exp (-(Real.pi * y * s)) * (Ξ s - ρ s * Xe s)) (Set.Ici 0) t = 0 := by
        rw [Filter.EventuallyEq.iteratedDerivWithin_eq_of_nhds_insert j hGz]
        simp
      rw [hz, norm_zero, mul_zero]
      exact hε.le

end Work.Radial
