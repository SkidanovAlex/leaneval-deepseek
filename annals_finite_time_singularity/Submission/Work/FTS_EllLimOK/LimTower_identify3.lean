import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.RCLike.Lemmas
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.RingTheory.Finiteness.Prod
import Submission.Work.FTS_EllLimOK.LimTower_c2
import Submission.Work.FTS_EllLimOK.LimTower_identify

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK

open scoped Real Topology

/-! ## `C³` from a continuous third-order partial tower on an open subset of `ℝ²`

`contDiffOn_two_of_partial_tower` (in `LimTower_c2`) upgrades a continuous partial-derivative
tower of order `2` to `C²`.  Here we need the order-`3` version: continuity of the tower entries
`D a b` for `a + b ≤ 3` together with the slice-derivative relations for `a + b ≤ 2` give
`C³` for the bottom entry `D 0 0`.

The proof is the two-step closure, exactly as for `contDiffOn_two_of_partial_tower`:
the shifted towers `D (1 + ·) ·` and `D · (1 + ·)` have continuous entries up to order `2` and
slice relations up to order `1`, so `contDiffOn_two_of_partial_tower` gives `C²` of `D 1 0` and
`D 0 1`; the Fréchet derivative of `D 0 0` is `p ↦ cop (D 1 0 p) (D 0 1 p)`
(`diffOn_uncurry_of_slices`), which is then `C²` by `contDiffOn_cop`, and
`contDiffOn_succ_of_fderiv_apply` closes. -/
theorem contDiffOn_three_of_partial_tower {φ : ℝ → ℝ → ℝ} {D : ℕ → ℕ → ℝ → ℝ → ℝ}
    {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hφ : ∀ z θ, φ z θ = D 0 0 z θ)
    (hcont : ∀ a b : ℕ, a + b ≤ 3 → ContinuousOn (fun p : ℝ × ℝ => D a b p.1 p.2) U)
    (hsz : ∀ a b : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ U →
      HasDerivAt (fun z' => D a b z' θ) (D (a + 1) b z θ) z)
    (hth : ∀ a b : ℕ, a + b ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ U →
      HasDerivAt (fun θ' => D a b z θ') (D a (b + 1) z θ) θ) :
    ContDiffOn ℝ 3 (Function.uncurry φ) U := by
  -- the two shifted towers are `C²`
  have h2_10 : ContDiffOn ℝ 2 (Function.uncurry (D 1 0)) U :=
    contDiffOn_two_of_partial_tower hU (fun z θ => rfl)
      (fun a b hab => hcont (1 + a) b (by omega))
      (fun a b hab => hsz (1 + a) b (by omega))
      (fun a b hab => hth (1 + a) b (by omega))
  have h2_01 : ContDiffOn ℝ 2 (Function.uncurry (D 0 1)) U :=
    contDiffOn_two_of_partial_tower hU (fun z θ => rfl)
      (fun a b hab => hcont a (1 + b) (by omega))
      (fun a b hab => hsz a (1 + b) (by omega))
      (fun a b hab => hth a (1 + b) (by omega))
  have hcop : ContDiffOn ℝ 2
      (fun p : ℝ × ℝ => cop (D 1 0 p.1 p.2) (D 0 1 p.1 p.2)) U :=
    contDiffOn_cop h2_10 h2_01
  have hdiff := diffOn_uncurry_of_slices hU (hsz 0 0 (by norm_num)) (hth 0 0 (by norm_num))
    (hcont 1 0 (by norm_num)) (hcont 0 1 (by norm_num))
  have hstep : ContDiffOn ℝ (2 + 1) (Function.uncurry (D 0 0)) U := by
    refine contDiffOn_succ_of_fderiv_apply (n := 2) hdiff.1 (fun hω => absurd hω (by simp))
      (fun y => ?_)
    refine (hcop.clm_apply (contDiffOn_const (c := y))).congr fun x hx => ?_
    rw [hdiff.2 hx]
  have hφD : Function.uncurry φ = Function.uncurry (D 0 0) := by
    funext p; exact hφ p.1 p.2
  rw [hφD]
  exact hstep

theorem LimTower_identify3 {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (hcont : ∀ (c d : ℕ), c + d ≤ 3 → ContinuousOn (fun p : ℝ × ℝ => F c d p.1 p.2)
      Work.FTS.EllipticEst.Q0)
    (hdz : ∀ (c d : ℕ), c + d ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z)
    (hdth : ∀ (c d : ℕ), c + d ≤ 2 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ) :
    ContDiffOn ℝ 3 (Function.uncurry (F 0 0)) Work.FTS.EllipticEst.Q0 ∧
      ∀ (c d : ℕ), c + d ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        F c d z θ = Work.Spaces.mixed c d (F 0 0) z θ := by
  constructor
  · -- ## `C³` of `F 0 0`, in the coordinates `u = log z`, `v = log tan θ`
    -- the map `(u,v) ↦ (exp u, arctan (exp v))` lands in the open quadrant
    have hmemQ : ∀ p : ℝ × ℝ,
        (Real.exp p.1, Real.arctan (Real.exp p.2)) ∈ Work.FTS.EllipticEst.Q0 := by
      intro p
      refine Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos p.1, ?_, ?_⟩
      · rw [Real.arctan_pos]; exact Real.exp_pos p.2
      · exact Real.arctan_lt_pi_div_two _
    have hΦcont : Continuous fun p : ℝ × ℝ => (Real.exp p.1, Real.arctan (Real.exp p.2)) := by
      fun_prop
    -- continuity of every tower entry in the `(u,v)`-coordinates
    have hcontT : ∀ a b : ℕ, a + b ≤ 3 →
        ContinuousOn (fun p : ℝ × ℝ => T F a b p.1 p.2) Set.univ := by
      intro a b hab
      have h1 : ContinuousOn (fun p : ℝ × ℝ =>
          F a b (Real.exp p.1) (Real.arctan (Real.exp p.2))) Set.univ :=
        (hcont a b hab).comp hΦcont.continuousOn (fun p _ => hmemQ p)
      simpa only [T] using h1.div_const (2 ^ b)
    -- the `u`-derivative relation
    have hszT : ∀ a b : ℕ, a + b ≤ 2 → ∀ u v : ℝ,
        HasDerivAt (fun u' : ℝ => T F a b u' v) (T F (a + 1) b u v) u := by
      intro a b hab u v
      have hθ : Real.arctan (Real.exp v) ∈ Set.Ioo (0 : ℝ) (π / 2) :=
        ⟨by rw [Real.arctan_pos]; exact Real.exp_pos v, Real.arctan_lt_pi_div_two _⟩
      have hzQ : (Real.exp u, Real.arctan (Real.exp v)) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos u, hθ⟩
      have hd := hdz a b hab (Real.exp u) (Real.arctan (Real.exp v)) hzQ
      have hcomp := hd.comp u (Real.hasDerivAt_exp u)
      have hval : F (a + 1) b (Real.exp u) (Real.arctan (Real.exp v)) / Real.exp u
          * Real.exp u = F (a + 1) b (Real.exp u) (Real.arctan (Real.exp v)) := by
        field_simp
      rw [hval] at hcomp
      have h2 := hcomp.div_const (2 ^ b)
      simpa only [T, Function.comp_apply] using h2
    -- the `v`-derivative relation
    have hthT : ∀ a b : ℕ, a + b ≤ 2 → ∀ u v : ℝ,
        HasDerivAt (fun v' : ℝ => T F a b u v') (T F a (b + 1) u v) v := by
      intro a b hab u v
      have hθ : Real.arctan (Real.exp v) ∈ Set.Ioo (0 : ℝ) (π / 2) :=
        ⟨by rw [Real.arctan_pos]; exact Real.exp_pos v, Real.arctan_lt_pi_div_two _⟩
      have hzQ : (Real.exp u, Real.arctan (Real.exp v)) ∈ Work.FTS.EllipticEst.Q0 :=
        Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos u, hθ⟩
      have hd := hdth a b hab (Real.exp u) (Real.arctan (Real.exp v)) hzQ
      have hcomp := hd.comp v (Work.FTS.StrongEps.LocUnif.hasDerivAt_arctan_exp v)
      have hsin : Real.sin (2 * Real.arctan (Real.exp v)) ≠ 0 := by
        rw [show Real.sin (2 * Real.arctan (Real.exp v))
              = 2 * Real.exp v / (1 + (Real.exp v) ^ 2) from by
            have hS : (0 : ℝ) < 1 + (Real.exp v) ^ 2 := by positivity
            rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
            rw [show (2 : ℝ) * (Real.exp v / √(1 + (Real.exp v) ^ 2))
                  * (1 / √(1 + (Real.exp v) ^ 2))
                = 2 * Real.exp v / (√(1 + (Real.exp v) ^ 2)) ^ 2 from by ring]
            rw [Real.sq_sqrt hS.le]]
        positivity
      have hval : F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v))
            / Real.sin (2 * Real.arctan (Real.exp v))
            * (Real.sin (2 * Real.arctan (Real.exp v)) / 2)
          = F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v)) / 2 := by
        field_simp
      rw [hval] at hcomp
      have h2 := hcomp.div_const (2 ^ b)
      have hval2 : F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v)) / 2 / 2 ^ b
          = F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v)) / 2 ^ (b + 1) := by
        rw [pow_succ]; ring
      rw [hval2] at h2
      simpa only [T, Function.comp_apply] using h2
    -- the partial tower on `ℝ²` and the transfer back through the smooth coordinate change
    have h3 := contDiffOn_three_of_partial_tower (φ := fun u v => T F 0 0 u v) (D := T F)
      isOpen_univ (fun u v => rfl) hcontT
      (fun a b hab z θ _ => hszT a b hab z θ) (fun a b hab z θ _ => hthT a b hab z θ)
    have hcomp := h3.comp (Work.FTS.StrongEps.LocUnif.contDiffOn_logLog_Q0 3)
      (fun p _ => Set.mem_univ _)
    exact hcomp.congr fun p hp => comp_logLog_T00 F hp
  · -- ## Identification of the tower entries with the `mixed` derivatives of `F 0 0`
    -- first: `F 0 d = D_θ^d (F 0 0)`, by the `θ`-tower relations
    have step1 : ∀ d : ℕ, d ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        F 0 d z θ = Work.Spaces.DthIter d (F 0 0) z θ := by
      intro d
      induction d with
      | zero => intro _ z θ _; rfl
      | succ d ih =>
          intro hd z θ hzθ
          have hprev : d ≤ 3 := by omega
          have heq : ∀ θ' : ℝ, (z, θ') ∈ Work.FTS.EllipticEst.Q0 →
              F 0 d z θ' = Work.Spaces.DthIter d (F 0 0) z θ' :=
            fun θ' hθ' => ih hprev z θ' hθ'
          have hderiv : deriv (fun θ' : ℝ => F 0 d z θ') θ
              = deriv (fun θ' : ℝ => Work.Spaces.DthIter d (F 0 0) z θ') θ := by
            refine Filter.EventuallyEq.deriv_eq ?_
            have hsl : {θ' : ℝ | (z, θ') ∈ Work.FTS.EllipticEst.Q0} ∈ 𝓝 θ :=
              (Work.FTS.EllipticEst.isOpen_Q0.preimage
                (by fun_prop : Continuous fun θ' : ℝ => (z, θ'))).mem_nhds hzθ
            filter_upwards [hsl] with θ' hθ'
            exact heq θ' hθ'
          obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
          have hsin : Real.sin (2 * θ) ≠ 0 :=
            ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
          have hval := (hdth 0 d (by omega) z θ hzθ).deriv
          calc F 0 (d + 1) z θ
              = Real.sin (2 * θ) * (F 0 (d + 1) z θ / Real.sin (2 * θ)) := by field_simp
            _ = Real.sin (2 * θ) * deriv (fun θ' : ℝ => F 0 d z θ') θ := by rw [hval]
            _ = Real.sin (2 * θ) *
                  deriv (fun θ' : ℝ => Work.Spaces.DthIter d (F 0 0) z θ') θ := by rw [hderiv]
            _ = Work.Spaces.DthIter (d + 1) (F 0 0) z θ := rfl
    -- then: `F c d = D_z^c (D_θ^d (F 0 0))`, by the `z`-tower relations
    have step2 : ∀ d : ℕ, d ≤ 3 → ∀ c : ℕ, c + d ≤ 3 → ∀ z θ : ℝ,
        (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        F c d z θ = Work.Spaces.DzIter c (Work.Spaces.DthIter d (F 0 0)) z θ := by
      intro d hd c
      induction c with
      | zero =>
          intro hcd z θ hzθ
          exact step1 d hd z θ hzθ
      | succ c ih =>
          intro hcd z θ hzθ
          have hprev : c + d ≤ 3 := by omega
          have heq : ∀ z' : ℝ, (z', θ) ∈ Work.FTS.EllipticEst.Q0 →
              F c d z' θ = Work.Spaces.DzIter c (Work.Spaces.DthIter d (F 0 0)) z' θ :=
            fun z' hz' => ih hprev z' θ hz'
          have hderiv : deriv (fun z' : ℝ => F c d z' θ) z
              = deriv (fun z' : ℝ =>
                  Work.Spaces.DzIter c (Work.Spaces.DthIter d (F 0 0)) z' θ) z := by
            refine Filter.EventuallyEq.deriv_eq ?_
            have hsl : {z' : ℝ | (z', θ) ∈ Work.FTS.EllipticEst.Q0} ∈ 𝓝 z :=
              (Work.FTS.EllipticEst.isOpen_Q0.preimage
                (by fun_prop : Continuous fun z' : ℝ => (z', θ))).mem_nhds hzθ
            filter_upwards [hsl] with z' hz'
            exact heq z' hz'
          obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
          have hval := (hdz c d (by omega) z θ hzθ).deriv
          calc F (c + 1) d z θ
              = z * (F (c + 1) d z θ / z) := by field_simp
            _ = z * deriv (fun z' : ℝ => F c d z' θ) z := by rw [hval]
            _ = z * deriv (fun z' : ℝ =>
                  Work.Spaces.DzIter c (Work.Spaces.DthIter d (F 0 0)) z' θ) z := by rw [hderiv]
            _ = Work.Spaces.DzIter (c + 1) (Work.Spaces.DthIter d (F 0 0)) z θ := rfl
    intro c d hcd z θ hzθ
    have hd3 : d ≤ 3 := by omega
    exact step2 d hd3 c hcd z θ hzθ

end Work.FTS_EllLimOK
