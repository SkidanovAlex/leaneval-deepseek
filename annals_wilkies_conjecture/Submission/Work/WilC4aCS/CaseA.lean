/-
  WilC4aCS.CaseA: the induction step when the defining function `F` vanishes identically near the
  origin.  Only inequalities remain, so we manufacture an equation: for each small radius we maximise
  `ψ = ∏ gⱼ` over the closed ball intersected with `{g ≥ 0}`.  The maximiser has all `gⱼ > 0` and is
  a constrained critical point, hence satisfies the (Fermat or Lagrange) equation `rotSq ψ = 0`, and
  it tends to `0`.  So `{rotSq ψ = 0} ∩ Y` still accumulates at `0`.

  In the degenerate case where `rotSq ψ` itself vanishes identically near `0`, we perturb,
  `ψ ↦ ψ · (1 + x_k)`.  If *every* such perturbation were degenerate, then `x_a ψ` would vanish near
  `0` for every coordinate `a ≠ k`; `ψ` vanishes on the (dense near `0`) open set where some
  coordinate `a ≠ k` is nonzero, so by continuity `ψ` vanishes on a whole ball around `0`, contrary
  to `∏ gⱼ` being positive at the points of `Y` accumulating at `0`.
-/
import Submission.Work.WilC4aCS.Defs
import Submission.Work.WilC4aCS.rotSq_analytic
import Submission.Work.WilC4aCS.rotSq_eq_zero_iff
import Submission.Work.WilC4aCS.rotSq_eq_zero_of_eventually
import Submission.Work.WilC4aCS.rotTerm_mul_affine
import Submission.Work.WilC4aCS.analyticAt_finset_prod_fam
import Submission.Work.WilC4aCS.EucMax

set_option autoImplicit false
noncomputable section
open Classical Topology Filter
open scoped BigOperators
open WilkiesConjecture WilkiesDesign WilkiesDesign.CG

namespace Work.WilC4aCS

open WilkiesDesign.CG.C4a
open WilkiesDesign.E

/-! ## The inequality-only maximiser lemma (proved in `EucMax`) -/

private theorem dev_closure_rotSq {m l : ℕ} (ψ : (Fin m → ℝ) → ℝ)
    (g : Fin l → (Fin m → ℝ) → ℝ)
    (hψ : ∀ᶠ x in nhds (0 : Fin m → ℝ), AnalyticAt ℝ ψ x)
    (hg : ∀ᶠ x in nhds (0 : Fin m → ℝ), ∀ j, ContinuousAt (g j) x)
    (hkills : ∀ x, (∀ j, 0 ≤ g j x) → 0 < ψ x → ∀ j, 0 < g j x)
    (hposY : ∀ᶠ x in nhds (0 : Fin m → ℝ), (∀ j, 0 < g j x) → 0 < ψ x)
    (hcl : (0 : Fin m → ℝ) ∈ closure {x : Fin m → ℝ | ∀ j, 0 < g j x}) :
    (0 : Fin m → ℝ) ∈ closure ({x : Fin m → ℝ | rotSq ψ x = 0} ∩
      {x : Fin m → ℝ | ∀ j, 0 < g j x}) :=
  closure_rotSq ψ g hψ hg hkills hposY hcl


/-- `rotSq` vanishes at the origin. -/
lemma rotSq_zero (m : ℕ) (ψ : (Fin m → ℝ) → ℝ) : rotSq ψ 0 = 0 := by
  rw [rotSq_eq_sum]
  refine Finset.sum_eq_zero fun p _ => ?_
  simp [rotTerm]

/-- **Case A.**  With only inequalities left (`F` vanishes identically near `0`, and the reduced
family has `gⱼ 0 = 0`), an analytic equation `E` can be manufactured which is not identically zero
as a germ and whose zero set still accumulates at the origin inside `{g > 0}`. -/
theorem caseA_equation {m l : ℕ} (hm : 2 ≤ m) (hl : 1 ≤ l) (g : Fin l → (Fin m → ℝ) → ℝ)
    (hg : ∀ j, AnalyticAt ℝ (g j) 0) (hg0 : ∀ j, g j 0 = 0)
    (hcl : (0 : Fin m → ℝ) ∈ closure {x : Fin m → ℝ | ∀ j, 0 < g j x}) :
    ∃ E : (Fin m → ℝ) → ℝ, AnalyticAt ℝ E 0 ∧ E 0 = 0 ∧ ¬ (E =ᶠ[𝓝 0] 0) ∧
      (0 : Fin m → ℝ) ∈ closure ({x : Fin m → ℝ | E x = 0} ∩
        {x : Fin m → ℝ | ∀ j, 0 < g j x}) := by
  let ψ : (Fin m → ℝ) → ℝ := fun x => ∏ j, g j x
  have hψan : AnalyticAt ℝ ψ 0 := analyticAt_finset_prod_fam g hg
  have hψev : ∀ᶠ x in 𝓝 (0 : Fin m → ℝ), AnalyticAt ℝ ψ x := hψan.eventually_analyticAt
  have hψ0 : ψ 0 = 0 := by
    show (∏ j, g j 0) = 0
    exact Finset.prod_eq_zero (Finset.mem_univ (⟨0, by omega⟩ : Fin l)) (hg0 _)
  have hgcont : ∀ᶠ x in 𝓝 (0 : Fin m → ℝ), ∀ j, ContinuousAt (g j) x := by
    rw [Filter.eventually_all]
    intro j
    filter_upwards [(hg j).eventually_analyticAt] with x hx
    exact hx.continuousAt
  have hψpos : ∀ x : Fin m → ℝ, (∀ j, 0 < g j x) → 0 < ψ x :=
    fun x hx => Finset.prod_pos fun j _ => hx j
  have hψnz : ¬ (ψ =ᶠ[𝓝 0] 0) := by
    intro h
    obtain ⟨r, hr, hr'⟩ := Metric.eventually_nhds_iff.mp h
    obtain ⟨x, hxg, hxr⟩ := Metric.mem_closure_iff.mp hcl r hr
    have h1 : ψ x = 0 := hr' (by simpa [dist_eq_norm] using hxr)
    have h2 : 0 < ψ x := hψpos x hxg
    rw [h1] at h2
    exact lt_irrefl 0 h2
  have hkills : ∀ x, (∀ j, 0 ≤ g j x) → 0 < ψ x → ∀ j, 0 < g j x := by
    intro x hge hpos j
    rcases lt_or_eq_of_le (hge j) with h | h
    · exact h
    · have hz : ψ x = 0 := Finset.prod_eq_zero (Finset.mem_univ j) h.symm
      rw [hz] at hpos
      exact absurd hpos (lt_irrefl 0)
  by_cases hdeg : ∀ᶠ x in 𝓝 (0 : Fin m → ℝ), rotSq ψ x = 0
  · -- degenerate: some perturbation `ψ · (1 + x_k)` is nondegenerate
    have hmain : ∃ k : Fin m,
        ¬ (∀ᶠ x in 𝓝 (0 : Fin m → ℝ), rotSq (fun y : Fin m → ℝ => ψ y * (1 + y k)) x = 0) := by
      by_contra hcon
      push_neg at hcon
      set k₀ : Fin m := ⟨0, by omega⟩ with hk₀
      have hcoord : ∀ a : Fin m, a ≠ k₀ → (fun y : Fin m → ℝ => y a * ψ y) =ᶠ[𝓝 0] 0 := by
        intro a ha
        have hterm : ∀ᶠ y in 𝓝 (0 : Fin m → ℝ),
            rotTerm (fun z : Fin m → ℝ => ψ z * (1 + z k₀)) y a k₀ = 0 :=
          (rotSq_eq_zero_of_eventually (fun z : Fin m → ℝ => ψ z * (1 + z k₀))).mp
            (hcon k₀) a k₀
        have htermψ : ∀ᶠ y in 𝓝 (0 : Fin m → ℝ), rotTerm ψ y a k₀ = 0 :=
          (rotSq_eq_zero_of_eventually ψ).mp hdeg a k₀
        filter_upwards [hterm, htermψ, hψev] with y hy hyψ hyan
        have hid := rotTerm_mul_affine ψ y k₀ a k₀ hyan
        rw [hid, hyψ] at hy
        have h1 : (Pi.single k₀ (1 : ℝ) : Fin m → ℝ) k₀ = 1 := Pi.single_eq_same ..
        have h2 : (Pi.single k₀ (1 : ℝ) : Fin m → ℝ) a = 0 := Pi.single_eq_of_ne ha _
        simp only [h1, h2, mul_one, mul_zero, sub_zero, zero_add] at hy
        rw [mul_comm]
        exact hy
      have hoff : ∀ᶠ y in 𝓝 (0 : Fin m → ℝ),
          (∃ a : Fin m, a ≠ k₀ ∧ y a ≠ 0) → ψ y = 0 := by
        have hall : ∀ᶠ y in 𝓝 (0 : Fin m → ℝ), ∀ a : Fin m, a ≠ k₀ → y a * ψ y = 0 := by
          rw [Filter.eventually_all]
          intro a
          by_cases ha : a = k₀
          · filter_upwards with y hy
            exact absurd ha hy
          · filter_upwards [hcoord a ha] with y hy _
            exact hy
        filter_upwards [hall] with y hy hne
        obtain ⟨a, ha, hay⟩ := hne
        rcases mul_eq_zero.mp (hy a ha) with h | h
        · exact absurd h hay
        · exact h
      obtain ⟨ρ, hρ, hρ'⟩ := Metric.eventually_nhds_iff.mp hoff
      obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp hψev
      -- ψ is continuous near `0` and vanishes on the complement of the coordinate subspace
      have hball : ∀ᶠ z in 𝓝 (0 : Fin m → ℝ), ψ z = 0 := by
        refine Metric.eventually_nhds_iff.mpr ⟨min ρ δ / 2, by positivity, fun z hz => ?_⟩
        have hz' : ‖z‖ < min ρ δ / 2 := by simpa [dist_eq_norm] using hz
        have hzρ : ‖z‖ < ρ := lt_of_lt_of_le hz' (by linarith [min_le_left ρ δ])
        have hzδ : ‖z‖ < δ := lt_of_lt_of_le hz' (by linarith [min_le_right ρ δ])
        have hcontz : ContinuousAt ψ z :=
          (hδ' (by simpa [dist_eq_norm] using hzδ)).continuousAt
        have hzρ' : dist z 0 < ρ := by simpa [dist_eq_norm] using hzρ
        obtain ⟨a, ha⟩ : ∃ a : Fin m, a ≠ k₀ := ⟨⟨1, by omega⟩, by simp [hk₀]⟩
        set e : Fin m → ℝ := Pi.single a (1 : ℝ) with he
        have ht : Tendsto (fun n : ℕ => ρ / 4 / (n + 1 : ℝ)) atTop (𝓝 0) := by
          simpa [div_eq_mul_inv] using
            tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (ρ / 4)
        have htn : ∀ᶠ n : ℕ in atTop, 0 < ρ / 4 / (n + 1 : ℝ) :=
          Filter.Eventually.of_forall fun n => by positivity
        have hy : Tendsto (fun n : ℕ => z + (ρ / 4 / (n + 1 : ℝ)) • e) atTop (𝓝 z) := by
          have h0 : Tendsto (fun n : ℕ => (ρ / 4 / (n + 1 : ℝ)) • e) atTop (𝓝 (0 : Fin m → ℝ)) := by
            have h1 : Tendsto (fun _ : ℕ => e) atTop (𝓝 e) := tendsto_const_nhds
            have h2 := ht.smul h1
            simpa using h2
          simpa using (tendsto_const_nhds.add h0)
        have hea : e a = 1 := Pi.single_eq_same ..
        have hzn : ∀ᶠ n : ℕ in atTop, z a + ρ / 4 / (n + 1 : ℝ) ≠ 0 := by
          rcases eq_or_ne (z a) 0 with hza | hza
          · filter_upwards [htn] with n hn
            rw [hza, zero_add]
            exact ne_of_gt hn
          · have h1 : ∀ᶠ n : ℕ in atTop, ρ / 4 / (n + 1 : ℝ) ≠ -z a :=
              ht.eventually (isOpen_compl_singleton.mem_nhds (by simpa using hza))
            filter_upwards [h1] with n hn hzero
            exact hn (by linarith)
        have hzn0 : ∀ᶠ n : ℕ in atTop, ψ (z + (ρ / 4 / (n + 1 : ℝ)) • e) = 0 := by
          have hne : ∀ᶠ n : ℕ in atTop,
              (∃ a' : Fin m, a' ≠ k₀ ∧ (z + (ρ / 4 / (n + 1 : ℝ)) • e) a' ≠ 0) := by
            filter_upwards [hzn] with n hn
            refine ⟨a, ha, ?_⟩
            have hval : (z + (ρ / 4 / (n + 1 : ℝ)) • e) a = z a + ρ / 4 / (n + 1 : ℝ) := by
              rw [Pi.add_apply, Pi.smul_apply, he, Pi.single_eq_same, smul_eq_mul, mul_one]
            rw [hval]
            exact hn
          have hdist : ∀ᶠ n : ℕ in atTop,
              dist (z + (ρ / 4 / (n + 1 : ℝ)) • e) 0 < ρ :=
            hy.eventually (Metric.isOpen_ball.mem_nhds hzρ')
          filter_upwards [hne, hdist] with n hn hd
          exact hρ' (by simpa [dist_eq_norm] using hd) hn
        have hlim : Tendsto (fun n : ℕ => ψ (z + (ρ / 4 / (n + 1 : ℝ)) • e)) atTop (𝓝 (ψ z)) :=
          hcontz.tendsto.comp hy
        have hlim0 : Tendsto (fun n : ℕ => ψ (z + (ρ / 4 / (n + 1 : ℝ)) • e)) atTop (𝓝 0) :=
          Tendsto.congr' (hzn0.mono fun n hn => hn.symm) tendsto_const_nhds
        exact tendsto_nhds_unique (f := fun n : ℕ => ψ (z + (ρ / 4 / (n + 1 : ℝ)) • e))
          hlim hlim0
      exact hψnz hball
    obtain ⟨k, hk⟩ := hmain
    refine ⟨rotSq (fun y : Fin m → ℝ => ψ y * (1 + y k)), ?_, rotSq_zero m _, hk, ?_⟩
    · have hproj : AnalyticAt ℝ (fun y : Fin m → ℝ => y k) 0 :=
        (((ContinuousLinearMap.proj (R := ℝ) k) : (Fin m → ℝ) →L[ℝ] ℝ).analyticAt
          (0 : Fin m → ℝ))
      exact rotSq_analytic (hψan.mul (analyticAt_const.add hproj))
    · refine dev_closure_rotSq (fun y : Fin m → ℝ => ψ y * (1 + y k)) g ?_ hgcont ?_ ?_ hcl
      · filter_upwards [hψev] with x hx
        exact hx.mul (analyticAt_const.add
          ((((ContinuousLinearMap.proj (R := ℝ) k) : (Fin m → ℝ) →L[ℝ] ℝ).analyticAt x)))
      · intro x hge hpos
        have hψge : 0 ≤ ψ x := Finset.prod_nonneg fun j _ => hge j
        have hψx : 0 < ψ x := by
          rcases lt_or_eq_of_le hψge with h | h
          · exact h
          · rw [← h, zero_mul] at hpos
            exact absurd hpos (lt_irrefl 0)
        exact hkills x hge hψx
      · have h1k : ∀ᶠ x in 𝓝 (0 : Fin m → ℝ), 0 < 1 + x k := by
          have hcont : Continuous (fun y : Fin m → ℝ => 1 + y k) :=
            continuous_const.add
              (((ContinuousLinearMap.proj (R := ℝ) k) : (Fin m → ℝ) →L[ℝ] ℝ).continuous)
          exact hcont.continuousAt.tendsto.eventually_mem (isOpen_Ioi.mem_nhds (by norm_num))
        filter_upwards [h1k] with x hxk hgx
        exact mul_pos (hψpos x hgx) hxk
  · refine ⟨rotSq ψ, rotSq_analytic hψan, rotSq_zero m ψ, hdeg, ?_⟩
    exact dev_closure_rotSq ψ g hψev hgcont hkills (Filter.Eventually.of_forall hψpos) hcl

end Work.WilC4aCS
