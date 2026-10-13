import Mathlib
import Submission.Work.WilE3.Taylor.Grad.gradOrderLe
import Submission.Work.Taylor.Grad.grad_eaEval
import Submission.Work.WilE3.Taylor.HasLoj.polar_count_deformed
import Submission.Work.WilE3.Taylor.Grad.PolarDefs
import Submission.Work.WilE3.eaEval_analytic
import Submission.Work.WilE3.Taylor.Arc.branch_count
import Submission.Work.WilE3.Taylor.Arc.complexify_order
import Submission.Work.WilE3.Taylor.Arc.ofReal_order
import Submission.Work.WilE3.Taylor.Arc.eaEvalC_arc_order
import Submission.Work.WilE3.Taylor.Arc.card_le_mul_card_image
import Submission.Work.WilE3.Taylor.Arc.fibre_card_le
import Submission.Work.WilE3.Frame.eaEvalC_toC
import Submission.Work.WilE3.API.eaEvalC_fderiv_analytic

import Submission.Work.WilE3.Taylor.CaseII.GenCount

namespace Work.WilE3.Taylor.CaseII.Gen

open Filter
open scoped Topology

theorem squareCount_goodLevel (hMB : Work.WilE3.MultiplicityBound) (F : ℕ) :
    ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : WilkiesDesign.E.EAChain k r)
      (Φ : WilkiesDesign.E.EAPoly k r) (y : Fin k → ℝ) (γ : ℝ → Fin k → ℝ)
      (P : Fin k → WilkiesDesign.E.EAPoly k r) (m a : ℕ) (i₀ : Fin k),
      P i₀ = Φ → (∀ i, WilkiesDesign.E.atomDeg (P i) ≤ 3 * WilkiesDesign.E.atomDeg Φ + 3) →
      k + r ≤ F → AnalyticAt ℝ γ 0 → γ 0 = y → 0 < a → 0 < m →
      analyticOrderAt (fun t : ℝ => γ t - y) 0 = a →
      analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)) 0 = m →
      (∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i : Fin k, i ≠ i₀ →
        WilkiesDesign.E.eaEval c (P i) (γ t) = 0) →
      (¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (Matrix.of fun i j => WilkiesDesign.E.eaEval c
          (WilkiesDesign.E.eaD c j (P i)) (γ t)).det = 0) →
      m ≤ a * K.eval (WilkiesDesign.E.atomDeg Φ) := by
  obtain ⟨M, hM⟩ := Work.WilE3.Taylor.HasLoj.polar_count_deformed hMB F
  refine ⟨M, ?_⟩
  intro k r c Φ y γ P m a i₀ hP hdeg0 hkr hγ hγ0 ha hm hram hord hminors hdet
  -- The arc is not eventually constant: `Φ ∘ γ` has finite nonzero order `m`, whereas an arc
  -- which is eventually constantly `y` would give `Φ ∘ γ =ᶠ 0` (as `ord₀ (Φ ∘ γ) = m > 0` forces
  -- `Φ y = 0`) and hence order `⊤`.
  have hne : ¬ (γ =ᶠ[nhds (0 : ℝ)] fun _ => y) := by
    intro hconst
    have hΦy : WilkiesDesign.E.eaEval c Φ y = 0 := by
      have h1 : analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)) 0 ≠ 0 := by
        rw [hord]; exact_mod_cast hm.ne'
      have h2 := apply_eq_zero_of_analyticOrderAt_ne_zero
        (f := fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)) (z₀ := (0 : ℝ)) h1
      simpa [hγ0] using h2
    have hev : (fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)) =ᶠ[𝓝 (0 : ℝ)]
        (fun _ => (0 : ℝ)) := by
      filter_upwards [hconst] with t ht
      rw [ht, hΦy]
    have htop : analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)) 0 = ⊤ :=
      analyticOrderAt_eq_top.mpr hev
    rw [hord] at htop
    exact ENat.natCast_ne_top m htop
  -- The level points of the polar branch together with their shrinking radius.
  obtain ⟨S, ρ, hρpos, hρtend, hS⟩ :=
    polarPointsAtLevelGen c Φ y γ i₀ P hγ hγ0 ha hm hram hord hne hminors hdet
  -- The base point `toC y` is a zero of the (undeformed) polar system.
  have hPx : ∀ i : Fin k,
      Work.WilE3.eaEvalC c (P i)
        (Work.WilE3.Frame.toC y) = 0 :=
    toCGen c Φ y γ i₀ P hP hγ hγ0 hm hord hminors
  -- Degree bookkeeping: every row of the polar system has atom degree `≤ 3 * atomDeg Φ + 3`.
  have hdeg : ∀ i : Fin k, WilkiesDesign.E.atomDeg (P i)
      ≤ 3 * WilkiesDesign.E.atomDeg Φ + 3 :=
    hdeg0
  -- The multiplicity bound for the polar system, deformed by `-ε` in the pivot row.
  have hcount := hM k r c Φ (P) i₀
    (Work.WilE3.Frame.toC y) hkr hPx hdeg ρ hρpos hρtend
  -- Both statements are "eventually in `ε ≠ 0`"; make the thresholds explicit.
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hcount hS
  obtain ⟨δ₁, hδ₁, hc₁⟩ := hcount
  obtain ⟨δ₂, hδ₂, hc₂⟩ := hS
  -- A level at which both hold.
  set ε : ℂ := (((min δ₁ δ₂) / 2 : ℝ) : ℂ) with hεdef
  have hεnorm : ‖ε‖ = min δ₁ δ₂ / 2 := by
    rw [hεdef, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hεpos : 0 < ‖ε‖ := by rw [hεnorm]; positivity
  have hε0 : ε ≠ 0 := norm_pos_iff.mp hεpos
  have hεmem : ε ∈ ({(0 : ℂ)}ᶜ : Set ℂ) := by
    rw [Set.mem_compl_iff, Set.mem_singleton_iff]; exact hε0
  have hεδ₁ : dist ε 0 < δ₁ := by
    rw [dist_zero_right, hεnorm]; have := min_le_left δ₁ δ₂; linarith
  have hεδ₂ : dist ε 0 < δ₂ := by
    rw [dist_zero_right, hεnorm]; have := min_le_right δ₁ δ₂; linarith
  have hSε := hc₂ (y := ε) hεδ₂ hεmem
  have hcard : (S ε).card ≤ M.eval (WilkiesDesign.E.atomDeg Φ) :=
    hc₁ (y := ε) hεδ₁ hεmem (S ε) ?_ ?_
  · calc m ≤ a * (S ε).card := hSε.2.2.2.1
      _ ≤ a * M.eval (WilkiesDesign.E.atomDeg Φ) := Nat.mul_le_mul_left a hcard
  · -- The points of `S ε` are nondegenerate zeros of the deformed polar system.
    intro z hz
    refine ⟨fun i => ?_, hSε.2.2.1 z hz⟩
    by_cases hi : i = i₀
    · -- pivot row: `Φ z = ε`
      have hpol : P i = Φ := by
        rw [hi]; exact hP
      have hzε := hSε.1 z hz
      rw [hpol, hzε, ite_eq_left hi]
      ring
    · -- other rows: the minors vanish
      rw [ite_eq_right hi, mul_zero, add_zero]
      exact hSε.2.1 z hz i hi
  · -- `S ε` lies in the `ρ ε`-ball around the base point.
    intro z hz
    exact hSε.2.2.2.2 z hz


open Classical in
theorem squareSystem_deficit (hMB : Work.WilE3.MultiplicityBound) (F : ℕ) :
    ∃ K : Polynomial ℕ, ∀ (k r : ℕ) (c : WilkiesDesign.E.EAChain k r)
      (Φ : WilkiesDesign.E.EAPoly k r) (y : Fin k → ℝ) (γ : ℝ → Fin k → ℝ) (P : Fin k → WilkiesDesign.E.EAPoly k r) (m a : ℕ)
      (i₀ : Fin k),
      P i₀ = Φ → (∀ i, WilkiesDesign.E.atomDeg (P i) ≤ 3 * WilkiesDesign.E.atomDeg Φ + 3) →
      k + r ≤ F → AnalyticAt ℝ γ 0 → γ 0 = y → 0 < a → 0 < m →
      analyticOrderAt (fun t : ℝ => γ t - y) 0 = a →
      analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c Φ (γ t)) 0 = m →
      (∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), ∀ i : Fin k, i ≠ i₀ →
        WilkiesDesign.E.eaEval c (P i) (γ t) = 0) →
      (¬ ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (Matrix.of fun i j => WilkiesDesign.E.eaEval c
          (WilkiesDesign.E.eaD c j (P i)) (γ t)).det = 0) →
      ∃ (i : Fin k) (n : ℕ),
        analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c i Φ) (γ t)) 0
          = n ∧
        (K.eval (WilkiesDesign.E.atomDeg Φ) + 1) * n ≤ K.eval (WilkiesDesign.E.atomDeg Φ) * m := by
  obtain ⟨K, hK⟩ := squareCount_goodLevel hMB F
  refine ⟨K, ?_⟩
  intro k r c Φ y γ P m a i₀ hP hdeg0 hkr hγ hγ0 ha hm hram hord hminors hdet
  -- the good-level count
  have hcount : m ≤ a * K.eval (WilkiesDesign.E.atomDeg Φ) :=
    hK k r c Φ y γ P m a i₀ hP hdeg0 hkr hγ hγ0 ha hm hram hord hminors hdet
  -- the minimal order of a partial derivative of `Φ` along the arc
  let ordOf : Fin k → ℕ∞ := fun l =>
    analyticOrderAt (fun t : ℝ => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c l Φ) (γ t)) 0
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin k)) ordOf ⟨i₀, Finset.mem_univ i₀⟩
  have hmin : ∀ l : Fin k, ordOf i ≤ ordOf l := fun l => hi l (Finset.mem_univ l)
  -- the gradient of `eaEval c Φ` is `eaEval c (eaD c · Φ)`
  have hgrad : ∀ l : Fin k,
      (fun t : ℝ => Work.WilE3.Taylor.grad (fun z : Fin k → ℝ => WilkiesDesign.E.eaEval c Φ z)
          (γ t) l)
        = fun t : ℝ => WilkiesDesign.E.eaEval c (WilkiesDesign.E.eaD c l Φ) (γ t) := by
    intro l
    funext t
    exact Work.Taylor.Grad.grad_eaEval c Φ (γ t) l
  -- the minimal order is finite: otherwise the chain rule with the numerical bound `m + 1`
  -- contradicts `m` finite
  have hne_top : ordOf i ≠ ⊤ := by
    intro htop
    have hr : ∀ l : Fin k, ((m + 1 : ℕ) : ℕ∞) ≤
        analyticOrderAt (fun t : ℝ =>
          Work.WilE3.Taylor.grad (fun z : Fin k → ℝ => WilkiesDesign.E.eaEval c Φ z)
            (γ t) l) 0 := by
      intro l
      rw [hgrad l]
      have hle : ordOf l = ⊤ := le_antisymm le_top (by rw [← htop]; exact hmin l)
      show ((m + 1 : ℕ) : ℕ∞) ≤ ordOf l
      rw [hle]
      exact le_top
    have hbad := Work.WilE3.Taylor.Grad.gradOrderLe
      (Φ := fun z : Fin k → ℝ => WilkiesDesign.E.eaEval c Φ z)
      hγ (fun x => Work.WilE3.eaEval_analytic c Φ x) ha hm hram hord hr
    omega
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hne_top
  refine ⟨i, n, ?_, ?_⟩
  · -- `ord₀ (∂ᵢΦ ∘ γ) = n`
    show ordOf i = (n : ℕ∞)
    exact hn.symm
  · -- the order bound
    set D := K.eval (WilkiesDesign.E.atomDeg Φ) with hD
    -- the chain-rule bound `n + a ≤ m`
    have hr : ∀ l : Fin k, (n : ℕ∞) ≤
        analyticOrderAt (fun t : ℝ =>
          Work.WilE3.Taylor.grad (fun z : Fin k → ℝ => WilkiesDesign.E.eaEval c Φ z)
            (γ t) l) 0 := by
      intro l
      rw [hgrad l]
      show (n : ℕ∞) ≤ ordOf l
      rw [hn]
      exact hmin l
    have hnle : n + a ≤ m := Work.WilE3.Taylor.Grad.gradOrderLe
      (Φ := fun z : Fin k → ℝ => WilkiesDesign.E.eaEval c Φ z)
      hγ (fun x => Work.WilE3.eaEval_analytic c Φ x) ha hm hram hord hr
    -- arithmetic
    have ha_le_m : a ≤ m := by omega
    have hnm : n ≤ m - a := (Nat.le_sub_iff_add_le ha_le_m).mpr hnle
    have hkey : m ≤ (D + 1) * a := by
      calc m ≤ a * D := hcount
        _ ≤ a * (D + 1) := Nat.mul_le_mul_left a (Nat.le_succ D)
        _ = (D + 1) * a := Nat.mul_comm _ _
    calc (D + 1) * n ≤ (D + 1) * (m - a) := Nat.mul_le_mul_left _ hnm
      _ = (D + 1) * m - (D + 1) * a := Nat.mul_sub_left_distrib _ _ _
      _ ≤ (D + 1) * m - m := Nat.sub_le_sub_left hkey ((D + 1) * m)
      _ = D * m := by
          have h : (D + 1) * m = D * m + m := by ring
          rw [h, Nat.add_sub_cancel]



end Work.WilE3.Taylor.CaseII.Gen
