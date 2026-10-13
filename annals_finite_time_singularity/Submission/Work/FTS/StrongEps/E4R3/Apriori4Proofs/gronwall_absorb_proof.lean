import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Algebra.Module.ModuleTopology

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `E4R3/Apriori4Proofs/gronwall_absorb_proof` — Grönwall with an absorbed quadratic defect

A continuous `e : ℝ → ℝ` with
`e' ≤ Λ (1 + e) + ε C₁ (1 + e)²` on `(0,T)`, `e 0 ≤ E0` and the smallness condition
`ε C₁ · 2 (1 + E0) e^{2(Λ+1)T} ≤ Λ + 1` satisfies `1 + e τ ≤ (1 + E0) e^{2(Λ+1)T}` on `[0,T]`.

Write `u := 1 + e` and `M := (1+E0) e^{2(Λ+1)T}`, so that `u 0 ≤ 1 + E0 < M` and
`u' ≤ Λ u + ε C₁ u²`.  The proof is the standard barrier (first-crossing) argument, split into
three independent ingredients:

* `grAux_gronwall_le_exp` — one-sided linear Grönwall comparison (integrating factor):
  `u b ≤ u a e^{K (b-a)}` whenever `u' ≤ K u` on `(a,b)`.  No sign hypothesis on `u`.
* `grAux_no_cross_up` — a solution of `u' ≤ Λ u + ε C₁ u²` (`Λ, C₁, ε ≥ 0`) that is `≤ 0` at
  some time can never become positive later: on the region `u ≤ 0` the quadratic term works in
  the same direction, and the integrating factor traps the trajectory below `0`.
* the crossing analysis in `gronwall_absorb_proof`: if `u` exceeds `M` at some time, let `τ₀` be
  the first time at which the *initial segment* bound `u ≤ M` fails.  Then `u ≤ M` on `[0,τ₀]`
  with `u τ₀ = M`, so on `[0,τ₀]` the quadratic term is absorbed into the linear one using
  `ε C₁ M ≤ (Λ+1)/2 < Λ+1`; either `u` is positive on all of `[0,τ₀]` — then Grönwall from `0`
  gives `u τ₀ ≤ (1+E0) e^{(Λ+εC₁M)T} < M`, a contradiction — or `u` dips `≤ 0` at some point of
  `[0,τ₀]`, whence `u τ₀ ≤ 0` by `grAux_no_cross_up`, again a contradiction.
-/

noncomputable section

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs

/-! ### Auxiliary real-analysis lemmas -/

/-- **One-sided Grönwall comparison.**  If `u` is continuous on `[a,b]` and satisfies the
one-sided differential inequality `u' ≤ K * u` at every interior point, then
`u b ≤ u a * exp (K * (b - a))`.  The point is that the integrating factor
`τ ↦ u τ * exp (-K (τ - a))` is antitone; no sign hypothesis on `u` is needed. -/
theorem grAux_gronwall_le_exp {u : ℝ → ℝ} {a b K : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn u (Set.Icc a b))
    (hd : ∀ τ ∈ Set.Ioo a b, ∃ u' : ℝ, HasDerivAt u u' τ ∧ u' ≤ K * u τ) :
    u b ≤ u a * Real.exp (K * (b - a)) := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · set psi : ℝ → ℝ := fun τ => u τ * Real.exp (-K * (τ - a)) with hpsi
    have hcont_psi : ContinuousOn psi (Set.Icc a b) := by
      rw [hpsi]
      exact hcont.mul
        ((Real.continuous_exp.comp ((continuous_id.sub continuous_const).const_mul (-K))).continuousOn)
    have hderiv : ∀ x ∈ Set.Ioo a b,
        HasDerivAt psi ((deriv u x - K * u x) * Real.exp (-K * (x - a))) x := by
      intro x hx
      obtain ⟨u', hu', _⟩ := hd x hx
      have hu : HasDerivAt u (deriv u x) x := by rw [hu'.deriv]; exact hu'
      have hexp : HasDerivAt (fun τ : ℝ => Real.exp (-K * (τ - a)))
          (Real.exp (-K * (x - a)) * (-K)) x := by
        have hlin : HasDerivAt (fun τ : ℝ => -K * (τ - a)) (-K * 1) x := by
          simpa using ((hasDerivAt_id x).sub_const a).const_mul (-K)
        simpa using hlin.exp
      have hmain := hu.mul hexp
      have hfun : psi = (fun τ : ℝ => u τ * Real.exp (-K * (τ - a))) := hpsi
      rw [hfun]
      convert hmain using 1
      ring
    have hnonpos : ∀ x ∈ interior (Set.Icc a b), deriv psi x ≤ 0 := by
      intro x hx
      rw [interior_Icc] at hx
      rw [(hderiv x hx).deriv]
      have h1 : deriv u x - K * u x ≤ 0 := by
        obtain ⟨u', hu', hle'⟩ := hd x hx
        rw [hu'.deriv]
        linarith
      exact mul_nonpos_of_nonpos_of_nonneg h1 (Real.exp_pos _).le
    have hdiff : DifferentiableOn ℝ psi (interior (Set.Icc a b)) := by
      intro x hx
      rw [interior_Icc] at hx
      exact (hderiv x hx).differentiableAt.differentiableWithinAt
    have hanti : AntitoneOn psi (Set.Icc a b) :=
      antitoneOn_of_deriv_nonpos (convex_Icc a b) hcont_psi hdiff hnonpos
    have hba : psi b ≤ psi a :=
      hanti (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab
    have hpsi_a : psi a = u a := by
      rw [hpsi]; simp
    have h1 : u b * Real.exp (-K * (b - a)) ≤ u a := by
      rw [← hpsi_a]; exact hba
    have h2 : Real.exp (-K * (b - a)) * Real.exp (K * (b - a)) = 1 := by
      rw [← Real.exp_add]
      have : -K * (b - a) + K * (b - a) = 0 := by ring
      rw [this, Real.exp_zero]
    have h3 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (K * (b - a))).le
    rw [mul_assoc, h2, mul_one] at h3
    simpa using h3
  · subst heq; simp

/-- ε–δ form of continuity within the interval: at a point `τ` where `u` exceeds `c`, `u` stays
above `c` in a whole relative neighbourhood of `τ`. -/
theorem grAux_exists_pos_forall_gt {u : ℝ → ℝ} {T τ c : ℝ} (hcont : ContinuousOn u (Set.Icc 0 T))
    (hτ : τ ∈ Set.Icc 0 T) (hc : c < u τ) :
    ∃ δ > 0, ∀ z ∈ Set.Icc 0 T, |z - τ| < δ → c < u z := by
  have hcw : ContinuousWithinAt u (Set.Icc 0 T) τ := hcont.continuousWithinAt hτ
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousWithinAt_iff.mp hcw (u τ - c) (by linarith)
  refine ⟨δ, hδpos, fun z hz hzd => ?_⟩
  have h1 := hδ hz (by rwa [Real.dist_eq])
  rw [Real.dist_eq] at h1
  have h2 : u τ - u z ≤ |u z - u τ| := by
    have h3 : u τ - u z = -(u z - u τ) := by ring
    rw [h3]
    exact neg_le_abs (u z - u τ)
  linarith

/-- ε–δ form of continuity within the interval, dual form. -/
theorem grAux_exists_lt_forall_lt {u : ℝ → ℝ} {T τ c : ℝ} (hcont : ContinuousOn u (Set.Icc 0 T))
    (hτ : τ ∈ Set.Icc 0 T) (hc : u τ < c) :
    ∃ δ > 0, ∀ z ∈ Set.Icc 0 T, |z - τ| < δ → u z < c := by
  have hcw : ContinuousWithinAt u (Set.Icc 0 T) τ := hcont.continuousWithinAt hτ
  obtain ⟨δ, hδpos, hδ⟩ := Metric.continuousWithinAt_iff.mp hcw (c - u τ) (by linarith)
  refine ⟨δ, hδpos, fun z hz hzd => ?_⟩
  have h1 := hδ hz (by rwa [Real.dist_eq])
  rw [Real.dist_eq] at h1
  have h2 : u z - u τ ≤ |u z - u τ| := le_abs_self _
  linarith

set_option linter.unusedVariables false in
/-- **A subsolution of `u' ≤ Λ u + ε C₁ u²` cannot cross up through `0`.**  If `u` is continuous
on `[0,T]`, satisfies the quadratic differential inequality on `(0,T)` with `Λ, C₁, ε ≥ 0`, and
`u x ≤ 0` at some `x ∈ [0,T]`, then `u` never exceeds `0` afterwards; in particular it cannot be
`> M` for `M > 0` at a later time. -/
theorem grAux_no_cross_up {u : ℝ → ℝ} {Λ C₁ ε M x y T : ℝ} (hΛ : 0 ≤ Λ) (hC₁ : 0 ≤ C₁)
    (hε : 0 ≤ ε) (hMpos : 0 < M) (hcont : ContinuousOn u (Set.Icc 0 T))
    (hd : ∀ τ ∈ Set.Ioo 0 T, ∃ u' : ℝ, HasDerivAt u u' τ ∧
      u' ≤ Λ * u τ + ε * C₁ * (u τ) ^ 2)
    (hx0 : 0 ≤ x) (hxy : x ≤ y) (hyT : y ≤ T) (hxle : u x ≤ 0) (hylt : M < u y) : False := by
  -- the set of times `≤ 0`, and its supremum
  have hxmem : x ∈ {q : ℝ | q ∈ Set.Icc x y ∧ u q ≤ 0} := ⟨Set.left_mem_Icc.mpr hxy, hxle⟩
  have hne : ({q : ℝ | q ∈ Set.Icc x y ∧ u q ≤ 0}).Nonempty := ⟨x, hxmem⟩
  have hbdd : BddAbove ({q : ℝ | q ∈ Set.Icc x y ∧ u q ≤ 0}) := ⟨y, fun q hq => hq.1.2⟩
  set ν : ℝ := sSup {q : ℝ | q ∈ Set.Icc x y ∧ u q ≤ 0} with hν
  have hxν : x ≤ ν := by rw [hν]; exact le_csSup hbdd hxmem
  have hνy : ν ≤ y := by rw [hν]; exact csSup_le hne (fun q hq => hq.1.2)
  have hνIcc : ν ∈ Set.Icc 0 T := ⟨le_trans hx0 hxν, le_trans hνy hyT⟩
  -- the supremum itself is a nonpositive point
  have hνle0 : u ν ≤ 0 := by
    by_contra hc
    have hc' : 0 < u ν := not_le.mp hc
    obtain ⟨δ, hδpos, hδ⟩ := grAux_exists_pos_forall_gt hcont hνIcc hc'
    have hlt : ν - δ < sSup {q : ℝ | q ∈ Set.Icc x y ∧ u q ≤ 0} := by rw [← hν]; linarith
    obtain ⟨q, hq, hqgt⟩ := (lt_csSup_iff hbdd hne).mp hlt
    have hqν : q ≤ ν := by rw [hν]; exact le_csSup hbdd hq
    have hqT : q ∈ Set.Icc 0 T := ⟨le_trans hx0 hq.1.1, le_trans hq.1.2 hyT⟩
    have habs : |q - ν| < δ := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    have := hδ q hqT habs
    linarith [hq.2]
  -- `u` is positive on `(ν, y]`
  have hpos : ∀ z ∈ Set.Ioo ν y, 0 < u z := by
    intro z hz
    by_contra hc
    have hznonpos : u z ≤ 0 := not_lt.mp hc
    have hzmem : z ∈ {q : ℝ | q ∈ Set.Icc x y ∧ u q ≤ 0} :=
      ⟨⟨le_trans hxν hz.1.le, hz.2.le⟩, hznonpos⟩
    have hle : z ≤ ν := by rw [hν]; exact le_csSup hbdd hzmem
    linarith [hz.1]
  -- on `[ν,y]` the quadratic term is dominated by a constant, so Grönwall applies
  have hcont' : ContinuousOn u (Set.Icc ν y) :=
    hcont.mono (fun z hz => ⟨le_trans hνIcc.1 hz.1, le_trans hz.2 hyT⟩)
  obtain ⟨ζ, -, hζmax⟩ :=
    IsCompact.exists_isMaxOn isCompact_Icc
      (⟨ν, Set.left_mem_Icc.mpr hνy⟩ : (Set.Icc ν y).Nonempty) hcont'
  have hgr : u y ≤ u ν * Real.exp ((Λ + ε * C₁ * u ζ) * (y - ν)) := by
    refine grAux_gronwall_le_exp hνy hcont' ?_
    intro z hz
    have hzT : z ∈ Set.Ioo 0 T := ⟨lt_of_le_of_lt hνIcc.1 hz.1, lt_of_lt_of_le hz.2 hyT⟩
    obtain ⟨u', hu', hle⟩ := hd z hzT
    refine ⟨u', hu', ?_⟩
    have hzpos : 0 < u z := hpos z hz
    have hzle : u z ≤ u ζ := hζmax ⟨hz.1.le, hz.2.le⟩
    have huu : Λ + ε * C₁ * u z ≤ Λ + ε * C₁ * u ζ := by
      have := mul_le_mul_of_nonneg_left hzle (mul_nonneg hε hC₁)
      linarith
    calc u' ≤ Λ * u z + ε * C₁ * (u z) ^ 2 := hle
      _ = u z * (Λ + ε * C₁ * u z) := by ring
      _ ≤ u z * (Λ + ε * C₁ * u ζ) := mul_le_mul_of_nonneg_left huu hzpos.le
      _ = (Λ + ε * C₁ * u ζ) * u z := by ring
  have hy0 : u y ≤ 0 := by
    have h := mul_nonpos_of_nonpos_of_nonneg hνle0
      (Real.exp_pos ((Λ + ε * C₁ * u ζ) * (y - ν))).le
    linarith
  linarith

/-! ### The absorption estimate -/

theorem gronwall_absorb_proof {e : ℝ → ℝ} {T Λ C₁ ε E0 : ℝ} (hT : 0 < T) (hΛ : 0 ≤ Λ)
    (hC₁ : 0 ≤ C₁) (hε : 0 ≤ ε) (hE0 : 0 ≤ E0)
    (hcont : ContinuousOn e (Set.Icc 0 T))
    (hd : ∀ τ ∈ Set.Ioo 0 T, ∃ e' : ℝ, HasDerivAt e e' τ ∧
      e' ≤ Λ * (1 + e τ) + ε * C₁ * (1 + e τ) ^ 2)
    (he0 : e 0 ≤ E0)
    (hsmall : ε * C₁ * (2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T)) ≤ Λ + 1) :
    ∀ τ ∈ Set.Icc 0 T, 1 + e τ ≤ (1 + E0) * Real.exp (2 * (Λ + 1) * T) := by
  set u : ℝ → ℝ := fun τ => 1 + e τ with hu
  set M : ℝ := (1 + E0) * Real.exp (2 * (Λ + 1) * T) with hM
  have hu_cont : ContinuousOn u (Set.Icc 0 T) := by
    rw [hu]; exact continuousOn_const.add hcont
  have hd' : ∀ τ ∈ Set.Ioo 0 T, ∃ u' : ℝ, HasDerivAt u u' τ ∧
      u' ≤ Λ * u τ + ε * C₁ * (u τ) ^ 2 := by
    intro τ hτ
    obtain ⟨e', he', hle⟩ := hd τ hτ
    refine ⟨e', ?_, ?_⟩
    · rw [hu]; exact he'.const_add 1
    · rw [hu]; exact hle
  have h1E0pos : (0 : ℝ) < 1 + E0 := by linarith
  have hMpos : 0 < M := by
    rw [hM]; exact mul_pos h1E0pos (Real.exp_pos _)
  have hE0lt : 1 + E0 < M := by
    rw [hM]
    have hE : 1 < Real.exp (2 * (Λ + 1) * T) := by
      have hΛ1 : 0 < Λ + 1 := by linarith
      have hpos : (0 : ℝ) < 2 * (Λ + 1) * T := by positivity
      simpa using Real.exp_lt_exp.mpr hpos
    calc 1 + E0 = (1 + E0) * 1 := by ring
      _ < (1 + E0) * Real.exp (2 * (Λ + 1) * T) := mul_lt_mul_of_pos_left hE h1E0pos
  have hu0 : u 0 ≤ 1 + E0 := by rw [hu]; simpa using he0
  have hsmall' : ε * C₁ * M ≤ (Λ + 1) / 2 := by
    have h2 : 2 * (1 + E0) * Real.exp (2 * (Λ + 1) * T) = 2 * M := by rw [hM]; ring
    rw [h2] at hsmall
    linarith
  have hKlt : Λ + ε * C₁ * M < 2 * (Λ + 1) := by linarith
  have hKnonneg : (0 : ℝ) ≤ Λ + ε * C₁ * M := by
    have : 0 ≤ ε * C₁ * M := mul_nonneg (mul_nonneg hε hC₁) hMpos.le
    linarith
  -- main claim
  have hmain : ∀ τ ∈ Set.Icc 0 T, u τ ≤ M := by
    intro τ hτ
    by_contra hcon
    have hgt : M < u τ := not_le.mp hcon
    -- first time the "initial segment bound" could fail
    have hBne : ({s : ℝ | s ∈ Set.Icc 0 T ∧ M < u s}).Nonempty := ⟨τ, hτ, hgt⟩
    have hBbdd : BddBelow ({s : ℝ | s ∈ Set.Icc 0 T ∧ M < u s}) := ⟨0, fun s hs => hs.1.1⟩
    set τ₀ : ℝ := sInf {s : ℝ | s ∈ Set.Icc 0 T ∧ M < u s} with hτ₀
    have hτ₀nonneg : 0 ≤ τ₀ := by
      rw [hτ₀]; exact le_csInf hBne (fun s hs => hs.1.1)
    have hτ₀leT : τ₀ ≤ T := by
      rw [hτ₀]
      obtain ⟨b, hb⟩ := hBne
      exact le_trans (csInf_le hBbdd hb) hb.1.2
    have hτ₀mem : τ₀ ∈ Set.Icc 0 T := ⟨hτ₀nonneg, hτ₀leT⟩
    have hP2 : ∀ s ∈ Set.Icc 0 τ₀, u s ≤ M := by
      intro s hs
      rcases lt_or_eq_of_le hs.2 with hlt | heq
      · -- `s < τ₀`: otherwise `τ₀` would not be a lower bound
        by_contra h
        have hMs : M < u s := not_le.mp h
        have hsT : s ∈ Set.Icc 0 T := ⟨hs.1, le_trans hs.2 hτ₀leT⟩
        have hle : τ₀ ≤ s := by rw [hτ₀]; exact csInf_le hBbdd ⟨hsT, hMs⟩
        linarith
      · -- `s = τ₀`: by continuity
        rw [heq]
        by_contra h
        have hMτ : M < u τ₀ := not_le.mp h
        rcases lt_or_eq_of_le hτ₀nonneg with hpos | hzero
        · obtain ⟨δ, hδpos, hδ⟩ := grAux_exists_pos_forall_gt hu_cont hτ₀mem hMτ
          have hmpos : 0 < min δ τ₀ := lt_min hδpos hpos
          have hzt : |(τ₀ - min δ τ₀ / 2) - τ₀| < δ := by
            have h1 : (τ₀ - min δ τ₀ / 2) - τ₀ = -(min δ τ₀ / 2) := by ring
            rw [h1, abs_neg, abs_of_pos (by linarith : 0 < min δ τ₀ / 2)]
            have h2 : min δ τ₀ ≤ δ := min_le_left δ τ₀
            linarith
          have hz0 : 0 ≤ τ₀ - min δ τ₀ / 2 := by
            have h2 : min δ τ₀ ≤ τ₀ := min_le_right δ τ₀
            linarith
          have hzT : τ₀ - min δ τ₀ / 2 ≤ T := by linarith
          have hzmem : τ₀ - min δ τ₀ / 2 ∈ {s : ℝ | s ∈ Set.Icc 0 T ∧ M < u s} :=
            ⟨⟨hz0, hzT⟩, hδ _ ⟨hz0, hzT⟩ hzt⟩
          have hle : τ₀ ≤ τ₀ - min δ τ₀ / 2 := by
            rw [hτ₀]; exact csInf_le hBbdd hzmem
          linarith
        · rw [← hzero] at hMτ
          linarith [hu0, hE0lt]
    -- take the crossing witness above `τ₀`
    obtain ⟨b, hb⟩ := hBne
    have hτ₀b : τ₀ ≤ b := by rw [hτ₀]; exact csInf_le hBbdd hb
    have hbT : b ≤ T := hb.1.2
    have hbM : M < u b := hb.2
    have hbgt : τ₀ < b := by
      rcases lt_or_eq_of_le hτ₀b with h | h
      · exact h
      · exfalso
        have hle := hP2 τ₀ ⟨hτ₀nonneg, le_rfl⟩
        rw [h] at hle
        linarith
    by_cases hcase : ∃ p ∈ Set.Icc 0 τ₀, u p ≤ 0
    · -- `u` was nonpositive somewhere before `τ₀`: it cannot come back up
      obtain ⟨p, hp, hp0⟩ := hcase
      exact grAux_no_cross_up hΛ hC₁ hε hMpos hu_cont hd' hp.1
        (le_trans hp.2 hbgt.le) hbT hp0 hbM
    · push Not at hcase
      -- first time at which `u` reaches `M`
      have hSne : ({p : ℝ | p ∈ Set.Icc 0 b ∧ M ≤ u p}).Nonempty :=
        ⟨b, ⟨⟨le_trans hτ₀nonneg hbgt.le, le_rfl⟩, hbM.le⟩⟩
      have hSbdd : BddBelow ({p : ℝ | p ∈ Set.Icc 0 b ∧ M ≤ u p}) := ⟨0, fun p hp => hp.1.1⟩
      set τ₁ : ℝ := sInf {p : ℝ | p ∈ Set.Icc 0 b ∧ M ≤ u p} with hτ₁
      have hτ₁nonneg : 0 ≤ τ₁ := by
        rw [hτ₁]; exact le_csInf hSne (fun p hp => hp.1.1)
      have hτ₁leb : τ₁ ≤ b := by
        rw [hτ₁]
        exact csInf_le hSbdd ⟨⟨le_trans hτ₀nonneg hbgt.le, le_rfl⟩, hbM.le⟩
      have hτ₁ge : M ≤ u τ₁ := by
        by_contra h
        have hlt : u τ₁ < M := not_le.mp h
        obtain ⟨δ, hδpos, hδ⟩ :=
          grAux_exists_lt_forall_lt hu_cont ⟨hτ₁nonneg, le_trans hτ₁leb hbT⟩ hlt
        have hlt2 : sInf {p : ℝ | p ∈ Set.Icc 0 b ∧ M ≤ u p} < τ₁ + δ := by
          rw [← hτ₁]; linarith
        obtain ⟨q, hq, hqlt⟩ := (csInf_lt_iff hSbdd hSne).mp hlt2
        have hqτ₁ : τ₁ ≤ q := by rw [hτ₁]; exact csInf_le hSbdd hq
        have hqT : q ∈ Set.Icc 0 T := ⟨hq.1.1, le_trans hq.1.2 hbT⟩
        have hqd : |q - τ₁| < δ := by
          rw [abs_of_nonneg (by linarith)]
          linarith
        have hqq := hδ q hqT hqd
        linarith [hq.2]
      by_cases hcase2 : ∃ p ∈ Set.Icc 0 τ₁, u p ≤ 0
      · obtain ⟨p, hp, hp0⟩ := hcase2
        exact grAux_no_cross_up hΛ hC₁ hε hMpos hu_cont hd' hp.1
          (le_trans hp.2 hτ₁leb) hbT hp0 hbM
      · push Not at hcase2
        -- `u` is positive on `[0,τ₁]`, so the quadratic term is absorbed on `(0,τ₁)`
        have hgr : u τ₁ ≤ u 0 * Real.exp ((Λ + ε * C₁ * M) * (τ₁ - 0)) := by
          refine grAux_gronwall_le_exp hτ₁nonneg
            (hu_cont.mono (fun z hz => ⟨hz.1, le_trans hz.2 (le_trans hτ₁leb hbT)⟩)) ?_
          intro z hz
          obtain ⟨u', hu', hle⟩ :=
            hd' z ⟨hz.1, lt_of_lt_of_le hz.2 (le_trans hτ₁leb hbT)⟩
          refine ⟨u', hu', ?_⟩
          have hzpos : 0 < u z := hcase2 z ⟨hz.1.le, hz.2.le⟩
          have hzltM : u z < M := by
            by_contra h
            have hMz : M ≤ u z := not_lt.mp h
            have hzmem : z ∈ {p : ℝ | p ∈ Set.Icc 0 b ∧ M ≤ u p} :=
              ⟨⟨hz.1.le, le_trans hz.2.le hτ₁leb⟩, hMz⟩
            have hle2 : τ₁ ≤ z := by rw [hτ₁]; exact csInf_le hSbdd hzmem
            linarith [hz.2]
          calc u' ≤ Λ * u z + ε * C₁ * (u z) ^ 2 := hle
            _ = u z * (Λ + ε * C₁ * u z) := by ring
            _ ≤ u z * (Λ + ε * C₁ * M) := mul_le_mul_of_nonneg_left (by
                  have := mul_le_mul_of_nonneg_left hzltM.le (mul_nonneg hε hC₁)
                  linarith) hzpos.le
            _ = (Λ + ε * C₁ * M) * u z := by ring
        have h1 : u 0 * Real.exp ((Λ + ε * C₁ * M) * (τ₁ - 0)) ≤
            (1 + E0) * Real.exp ((Λ + ε * C₁ * M) * T) := by
          have hexp : Real.exp ((Λ + ε * C₁ * M) * (τ₁ - 0)) ≤
              Real.exp ((Λ + ε * C₁ * M) * T) := by
            apply Real.exp_le_exp.mpr
            exact mul_le_mul_of_nonneg_left (by linarith : τ₁ - 0 ≤ T) hKnonneg
          calc u 0 * Real.exp ((Λ + ε * C₁ * M) * (τ₁ - 0))
              ≤ (1 + E0) * Real.exp ((Λ + ε * C₁ * M) * (τ₁ - 0)) :=
                mul_le_mul_of_nonneg_right hu0 (Real.exp_pos _).le
            _ ≤ (1 + E0) * Real.exp ((Λ + ε * C₁ * M) * T) :=
                mul_le_mul_of_nonneg_left hexp h1E0pos.le
        have h2 : (1 + E0) * Real.exp ((Λ + ε * C₁ * M) * T) <
            (1 + E0) * Real.exp (2 * (Λ + 1) * T) := by
          apply mul_lt_mul_of_pos_left _ h1E0pos
          apply Real.exp_lt_exp.mpr
          have hh := mul_lt_mul_of_pos_right hKlt hT
          linarith
        have h3 : (1 + E0) * Real.exp (2 * (Λ + 1) * T) = M := by rw [hM]
        linarith [hτ₁ge, hgr, h1, h2]
  intro τ hτ
  have h := hmain τ hτ
  rw [hu] at h
  rw [hM] at h
  exact h

end Work.FTS.StrongEps.E4R3.Apriori4Proofs
