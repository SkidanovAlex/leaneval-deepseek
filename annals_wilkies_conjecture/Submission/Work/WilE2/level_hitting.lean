import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE8.Basic
import Submission.Work.WilE2.posComps_finite

namespace Work.WilE2

open Classical Filter
open WilkiesDesign WilkiesDesign.E

noncomputable section

/-!
## The level-hitting lemma for the positivity set of an EA polynomial in the cube

`level_hitting` says: if `Q` is positive somewhere in the cube `[-1,1]^k`, then there is a
single level `δ > 0` which is met by every connected component of
`S := cubeC k ∩ {0 < eaEval c Q x}`.

The proof has two halves.

* *Finiteness of the component family* (delegated as `Work.WilE2.posComps_finite`): the
  components of the whole positivity set are finitely many.  This is the deep input (Khovanskii
  finiteness for a semi-Pfaffian sign condition).
* *The geometric reduction* (this file): every component other than `S` itself has `eaEval c Q`
  values arbitrarily close to `0`.  Indeed a component `C ≠ S` is open in the cube (the
  components of a positivity set are open), so it is not closed there; a boundary point `p` in
  the cube then lies outside `S`, i.e. `eaEval c Q p ≤ 0`, while points of `C` approach `p` and
  carry positive values.  Consequently, for a finite hitting set `s` of the components, the
  level `δ := (1/2) · min {eaEval c Q y | y ∈ s}` is met by every component: a component `C`
  contains some `y ∈ s` with `eaEval c Q y ≥ 2δ > δ` and (as just explained) also points with
  values `< δ`, so the intermediate value theorem on the preconnected `C` produces a point of
  `C` with value exactly `δ`.

If instead `S` has a single component, then `δ := eaEval c Q x₀` for any `x₀ ∈ S` works, since
all points of `S` then lie in the same component as `x₀`.
-/

/-- `x ↦ eaEval c Q x` is continuous. -/
theorem continuous_eaEval {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) :
    Continuous fun x : Fin k → ℝ => eaEval c Q x := by
  show Continuous fun x : Fin k → ℝ =>
    MvPolynomial.eval (Sum.elim x fun j => Real.exp (c.ell j x)) Q
  refine (MvPolynomial.continuous_eval Q).comp ?_
  refine continuous_pi (fun v => ?_)
  rcases v with i | j
  · exact continuous_apply i
  · refine Real.continuous_exp.comp ?_
    have h : c.ell j = fun x : Fin k → ℝ => ∑ i, c.a j i * x i + c.b j := by
      funext x
      simp only [EAChain.ell]
    rw [h]
    exact (continuous_finsetSum _ (fun i _ => continuous_const.mul (continuous_apply i))).add
      continuous_const

/-- **The components of a positivity set are open in the cube.**  Every point `y` of the set has
a cube-neighbourhood contained in the component of `y`. -/
theorem component_open {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r) {y : Fin k → ℝ}
    (hy : y ∈ cubeC k ∩ {z | 0 < eaEval c Q z}) :
    ∃ ε > 0, ∀ z : Fin k → ℝ, z ∈ cubeC k → dist z y < ε → 0 < eaEval c Q z →
      z ∈ connectedComponentIn (cubeC k ∩ {z | 0 < eaEval c Q z}) y := by
  have hcont := continuous_eaEval c Q
  have hopen : {z : Fin k → ℝ | 0 < eaEval c Q z} ∈ nhds y :=
    (isOpen_lt continuous_const hcont).mem_nhds hy.2
  obtain ⟨ε, hεpos, hε⟩ := Metric.mem_nhds_iff.1 hopen
  refine ⟨ε, hεpos, fun z hzc hzd hzf => ?_⟩
  have hpre : IsPreconnected (cubeC k ∩ Metric.ball y ε) :=
    ((Work.WilE8.cubeC_convex k).inter (convex_ball y ε)).isPreconnected
  have hsub : cubeC k ∩ Metric.ball y ε ⊆ cubeC k ∩ {z | 0 < eaEval c Q z} :=
    fun w hw => ⟨hw.1, hε hw.2⟩
  have hyV : y ∈ cubeC k ∩ Metric.ball y ε := ⟨hy.1, Metric.mem_ball_self hεpos⟩
  have hzV : z ∈ cubeC k ∩ Metric.ball y ε := ⟨hzc, Metric.mem_ball.mpr hzd⟩
  exact hpre.subset_connectedComponentIn hyV hsub hzV

/-- **Every component other than the whole positivity set has values accumulating at `0`.**

Let `S = cubeC k ∩ {0 < eaEval c Q x}` and let `C` be the component of `x` in `S`, with `C ≠ S`.
Then for every `ε > 0` there is `y ∈ C` with `eaEval c Q y < ε`. -/
theorem exists_lt_of_mem_component {k r : ℕ} (c : EAChain k r) (Q : EAPoly k r)
    {x : Fin k → ℝ} (hxS : x ∈ cubeC k ∩ {z | 0 < eaEval c Q z})
    (hne : connectedComponentIn (cubeC k ∩ {z | 0 < eaEval c Q z}) x ≠
      cubeC k ∩ {z | 0 < eaEval c Q z})
    {ε : ℝ} (hε : 0 < ε) :
    ∃ y ∈ connectedComponentIn (cubeC k ∩ {z | 0 < eaEval c Q z}) x, eaEval c Q y < ε := by
  have hcont := continuous_eaEval c Q
  set S : Set (Fin k → ℝ) := cubeC k ∩ {z | 0 < eaEval c Q z} with hS
  set C : Set (Fin k → ℝ) := connectedComponentIn S x with hCdef
  have hCsub : C ⊆ S := connectedComponentIn_subset S x
  have hxC : x ∈ C := mem_connectedComponentIn hxS
  obtain ⟨z, hzS, hzC⟩ : ∃ z, z ∈ S ∧ z ∉ C := by
    by_contra h
    push Not at h
    exact hne (le_antisymm hCsub h)
  -- the segment from `x` to `z`, staying in the cube
  set γ : ℝ → Fin k → ℝ := fun t => x + t • (z - x) with hγdef
  have hγcont : Continuous γ := by
    rw [hγdef]; fun_prop
  have hγmem : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ cubeC k := by
    intro t ht
    have hsplit : γ t = (1 - t) • x + t • z := by
      rw [hγdef]; ext i
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]; ring
    rw [hsplit]
    exact (Work.WilE8.cubeC_convex k) hxS.1 hzS.1 (by linarith [ht.2]) ht.1 (by ring)
  -- the parameter set of the part of the segment inside `C`
  set A : Set ℝ := {t | t ∈ Set.Icc (0:ℝ) 1 ∧ γ t ∈ C} with hAdef
  have hA0 : (0:ℝ) ∈ A := by
    refine ⟨⟨le_refl 0, zero_le_one⟩, ?_⟩
    rw [hγdef]; simpa using hxC
  have hA1 : (1:ℝ) ∉ A := by
    rintro ⟨-, h1⟩
    refine hzC ?_
    rw [hγdef] at h1
    simpa using h1
  have hAne : A.Nonempty := ⟨0, hA0⟩
  have hAbdd : BddAbove A := ⟨1, fun t ht => ht.1.2⟩
  set T : ℝ := sSup A with hTdef
  have hTlb : ∀ t ∈ A, t ≤ T := fun t ht => le_csSup hAbdd ht
  have hTin : T ∈ Set.Icc (0:ℝ) 1 :=
    ⟨le_trans (by norm_num) (hTlb 0 hA0), csSup_le hAne (fun t ht => ht.1.2)⟩
  -- `A` is open in `[0,1]`
  have hAopen : ∀ t ∈ A, ∃ r > 0, ∀ s, s ∈ Set.Icc (0:ℝ) 1 → |s - t| < r → s ∈ A := by
    intro t htA
    have hγtS : γ t ∈ S := hCsub htA.2
    obtain ⟨δ, hδpos, hδ⟩ := component_open c Q hγtS
    have hft : 0 < eaEval c Q (γ t) := hγtS.2
    have hcont' : Continuous fun s : ℝ => eaEval c Q (γ s) := hcont.comp hγcont
    have hnb : {s : ℝ | 0 < eaEval c Q (γ s)} ∈ nhds t :=
      (isOpen_lt continuous_const hcont').mem_nhds hft
    obtain ⟨ρ, hρpos, hρ⟩ := Metric.mem_nhds_iff.1 hnb
    refine ⟨min (δ / (‖z - x‖ + 1)) ρ, lt_min (by positivity) hρpos, fun s hsI hsd => ?_⟩
    refine ⟨hsI, ?_⟩
    have hsδ : |s - t| * ‖z - x‖ < δ := by
      have h1 : |s - t| * ‖z - x‖ ≤ |s - t| * (‖z - x‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (z - x)]) (abs_nonneg _)
      have h2 : |s - t| * (‖z - x‖ + 1) < (δ / (‖z - x‖ + 1)) * (‖z - x‖ + 1) :=
        mul_lt_mul_of_pos_right (lt_of_lt_of_le hsd (min_le_left _ _)) (by positivity)
      have h3 : (δ / (‖z - x‖ + 1)) * (‖z - x‖ + 1) = δ :=
        div_mul_cancel₀ δ (by positivity)
      linarith
    have hsdδ : dist (γ s) (γ t) < δ := by
      have hdiff : γ s - γ t = (s - t) • (z - x) := by
        rw [hγdef]
        ext i
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs]
      exact hsδ
    have hfs : 0 < eaEval c Q (γ s) :=
      hρ (Metric.mem_ball.mpr (by
        rw [Real.dist_eq]
        exact lt_of_lt_of_le hsd (min_le_right _ _)))
    have hzC' : γ s ∈ connectedComponentIn S (γ t) := hδ (γ s) (hγmem s hsI) hsdδ hfs
    rw [hCdef, connectedComponentIn_eq htA.2]
    exact hzC'
  -- `T ∉ A`
  have hTnotin : T ∉ A := by
    intro hTA
    obtain ⟨r, hrpos, hr⟩ := hAopen T hTA
    by_cases hT1 : T < 1
    · have h1 : (0:ℝ) ≤ T + r / 2 := by linarith [hTin.1, hrpos]
      have h2 : (0:ℝ) ≤ 1 := zero_le_one
      have hs1 : min (T + r / 2) 1 ∈ Set.Icc (0:ℝ) 1 := ⟨le_min h1 h2, min_le_right _ _⟩
      have hlt : T < min (T + r / 2) 1 := lt_min (by linarith) hT1
      have hs2 : |min (T + r / 2) 1 - T| < r := by
        rw [abs_lt]
        exact ⟨by linarith, by linarith [min_le_left (T + r / 2) (1:ℝ)]⟩
      linarith [hTlb _ (hr _ hs1 hs2)]
    · have hTeq : T = 1 := le_antisymm hTin.2 (le_of_not_gt hT1)
      exact hA1 (hTeq ▸ hTA)
  -- `γ T` is in the closure of `C`
  have hTcl : γ T ∈ closure C := by
    rw [Metric.mem_closure_iff]
    intro η hη
    have hden : 0 < ‖z - x‖ + 1 := by positivity
    have hpos : 0 < η / (‖z - x‖ + 1) := div_pos hη (by positivity)
    obtain ⟨t, htA, htgt⟩ := exists_lt_of_lt_csSup hAne (show T - η / (‖z - x‖ + 1) < sSup A by
      rw [hTdef]; linarith)
    refine ⟨γ t, htA.2, ?_⟩
    have hdiff : γ T - γ t = (T - t) • (z - x) := by
      rw [hγdef]
      ext i
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have hle : |t - T| < η / (‖z - x‖ + 1) := by
      rw [abs_lt]
      exact ⟨by linarith [hTlb t htA, htgt], by linarith [hTlb t htA]⟩
    have hb : |t - T| * ‖z - x‖ < η := by
      have h1 : |t - T| * ‖z - x‖ ≤ |t - T| * (‖z - x‖ + 1) :=
        mul_le_mul_of_nonneg_left (by linarith [norm_nonneg (z - x)]) (abs_nonneg _)
      have h2 : |t - T| * (‖z - x‖ + 1) < (η / (‖z - x‖ + 1)) * (‖z - x‖ + 1) :=
        mul_lt_mul_of_pos_right hle (by positivity)
      have h3 : (η / (‖z - x‖ + 1)) * (‖z - x‖ + 1) = η :=
        div_mul_cancel₀ η (by positivity)
      linarith
    rw [dist_eq_norm, hdiff, norm_smul, Real.norm_eq_abs, abs_sub_comm]
    exact hb
  -- `γ T` is not in `S`
  have hTnotS : γ T ∉ S := by
    intro hTS
    obtain ⟨δ, hδpos, hδ⟩ := component_open c Q hTS
    obtain ⟨u, huC, hud⟩ := (Metric.mem_closure_iff.mp hTcl) δ hδpos
    have huS : u ∈ S := hCsub huC
    have hucomp : u ∈ connectedComponentIn S (γ T) :=
      hδ u huS.1 (by rwa [dist_comm] at hud) huS.2
    have hCu : C = connectedComponentIn S (γ T) := by
      rw [hCdef, connectedComponentIn_eq huC, connectedComponentIn_eq hucomp]
    have : γ T ∈ C := by
      rw [hCu]
      exact mem_connectedComponentIn hTS
    exact hTnotin ⟨hTin, this⟩
  have hTle : eaEval c Q (γ T) ≤ 0 := by
    by_contra h
    push Not at h
    exact hTnotS ⟨hγmem T hTin, h⟩
  -- conclude by continuity at `γ T`
  have hev : {w : Fin k → ℝ | eaEval c Q w < ε} ∈ nhds (γ T) :=
    (isOpen_lt hcont continuous_const).mem_nhds (lt_of_le_of_lt hTle hε)
  obtain ⟨ρ, hρpos, hρ⟩ := Metric.mem_nhds_iff.1 hev
  obtain ⟨y, hyC, hyd⟩ := (Metric.mem_closure_iff.mp hTcl) ρ hρpos
  exact ⟨y, hyC, hρ (Metric.mem_ball.mpr (by rwa [dist_comm] at hyd))⟩

theorem level_hitting {k r : ℕ} (c : WilkiesDesign.E.EAChain k r)
    (Q : WilkiesDesign.E.EAPoly k r)
    (hpos : ∃ x ∈ WilkiesDesign.E.cubeC k, 0 < WilkiesDesign.E.eaEval c Q x) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ x ∈ WilkiesDesign.E.cubeC k, 0 < WilkiesDesign.E.eaEval c Q x →
        ∃ y ∈ WilkiesDesign.E.cubeC k, WilkiesDesign.E.eaEval c Q y = δ ∧
          connectedComponentIn
              (WilkiesDesign.E.cubeC k ∩ {z | 0 < WilkiesDesign.E.eaEval c Q z}) x
            = connectedComponentIn
              (WilkiesDesign.E.cubeC k ∩ {z | 0 < WilkiesDesign.E.eaEval c Q z}) y := by
  classical
  obtain ⟨x0, hx0c, hx0pos⟩ := hpos
  set S : Set (Fin k → ℝ) := cubeC k ∩ {z | 0 < eaEval c Q z} with hS
  have hx0S : x0 ∈ S := ⟨hx0c, hx0pos⟩
  by_cases hone : ∀ x ∈ S, ∀ y ∈ S, connectedComponentIn S x = connectedComponentIn S y
  · -- `S` has a single component
    refine ⟨eaEval c Q x0, hx0pos, fun x hxc hxpos =>
      ⟨x0, hx0c, rfl, hone x ⟨hxc, hxpos⟩ x0 hx0S⟩⟩
  · push Not at hone
    obtain ⟨x1, hx1S, y1, hy1S, hdiff⟩ := hone
    -- no component equals `S`
    have hneS : ∀ x ∈ S, connectedComponentIn S x ≠ S := by
      intro x hxS hcon
      have hpre : IsPreconnected S := hcon ▸ isPreconnected_connectedComponentIn
      exact hdiff (by rw [hpre.connectedComponentIn hx1S, hpre.connectedComponentIn hy1S])
    -- the finite hitting set of the components of `S`
    obtain ⟨s, hsS, hshits⟩ := posComps_finite c Q
    have hsS' : (↑s : Set (Fin k → ℝ)) ⊆ S := hsS
    have hshits' : ∀ x ∈ S, ∃ y ∈ s, connectedComponentIn S x = connectedComponentIn S y :=
      hshits
    have hsne : s.Nonempty := by
      obtain ⟨y, hy, -⟩ := hshits' x1 hx1S
      exact ⟨y, hy⟩
    -- the level: half the minimum of `eaEval c Q` over `s`
    set m : ℝ := (s.image fun y => eaEval c Q y).min' (hsne.image _) with hm
    have hmmem : m ∈ s.image (fun y => eaEval c Q y) := Finset.min'_mem _ _
    have hmpos : 0 < m := by
      obtain ⟨y, hys, hyv⟩ := Finset.mem_image.mp hmmem
      rw [← hyv]
      exact (hsS' hys).2
    refine ⟨m / 2, by linarith, fun x hxc hxpos => ?_⟩
    have hxS : x ∈ S := ⟨hxc, hxpos⟩
    obtain ⟨y, hys, hycomp⟩ := hshits' x hxS
    have hyS : y ∈ S := hsS' hys
    have hyC : y ∈ connectedComponentIn S x := by
      rw [hycomp]
      exact mem_connectedComponentIn hyS
    have hyle : m ≤ eaEval c Q y := by
      rw [hm]
      exact Finset.min'_le _ _ (Finset.mem_image.mpr ⟨y, hys, rfl⟩)
    have hygt : m / 2 < eaEval c Q y := by linarith
    obtain ⟨z, hzC, hzlt⟩ :=
      exists_lt_of_mem_component c Q hxS (hneS x hxS) (by linarith : 0 < m / 2)
    -- intermediate value theorem on the preconnected component
    have hpre : IsPreconnected (connectedComponentIn S x) := isPreconnected_connectedComponentIn
    have hcont : ContinuousOn (fun w : Fin k → ℝ => eaEval c Q w) (connectedComponentIn S x) :=
      (continuous_eaEval c Q).continuousOn
    have hIVT := hpre.intermediate_value hzC hyC hcont
    have hmem : m / 2 ∈ Set.Icc (eaEval c Q z) (eaEval c Q y) := ⟨le_of_lt hzlt, le_of_lt hygt⟩
    obtain ⟨w, hwC, hwv⟩ := hIVT hmem
    have hwS : w ∈ S := connectedComponentIn_subset S x hwC
    refine ⟨w, hwS.1, hwv, ?_⟩
    rw [connectedComponentIn_eq hwC]

end

end Work.WilE2
