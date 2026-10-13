import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.StrongLWP.Sobolev.contDiffOn_four_of_partial_tower
import Submission.Work.FTS.StrongEps.LocUnif.LocAux
import Submission.Work.FTS.StrongEps.LocUnif.mixed_partials_of_smoothOpen

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.LocUnif

set_option autoImplicit false
set_option maxHeartbeats 1000000


/-! ## The extraction data -/

/-- **The data produced by the extraction.**  A subsequence `φ`, the limits `F c d` of the
families `mixed c d (G (φ n))` (`c + d ≤ 4`), their local uniform convergence on `Q0`, and the two
"tower" relations obtained by differentiating the *definitional* relations
`mixed (c+1) d (G n) = D_z (mixed c d (G n))` and `mixed c (d+1) (G n) = D_θ (mixed c d (G n))`
along the sequence. -/
structure LimData (G : ℕ → ℝ → ℝ → ℝ) (φ : ℕ → ℕ) (F : ℕ → ℕ → ℝ → ℝ → ℝ) : Prop where
  /-- the fifteen families converge locally uniformly on `Q0`. -/
  conv : ∀ (c d : ℕ), c + d ≤ 4 → TendstoLocallyUniformlyOn
    (fun n p => Work.Spaces.mixed c d (G (φ n)) p.1 p.2)
    (fun p => F c d p.1 p.2) Filter.atTop Work.FTS.EllipticEst.Q0
  /-- the `z`-tower relation `D_z (F c d) = F (c+1) d`. -/
  dz : ∀ (c d : ℕ), c + d ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
    HasDerivAt (fun z' : ℝ => F c d z' θ) (F (c + 1) d z θ / z) z
  /-- the `θ`-tower relation `D_θ (F c d) = F c (d+1)`. -/
  dth : ∀ (c d : ℕ), c + d ≤ 3 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
    HasDerivAt (fun θ' : ℝ => F c d z θ') (F c (d + 1) z θ / Real.sin (2 * θ)) θ

/-- The limits of the extraction are continuous on `Q0` (locally uniform limits of the continuous
functions `mixed c d (G (φ n))`). -/
theorem LimData.continuousOn {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n)) (h : LimData G φ F)
    (c d : ℕ) (hcd : c + d ≤ 4) :
    ContinuousOn (fun p : ℝ × ℝ => F c d p.1 p.2) Work.FTS.EllipticEst.Q0 := by
  refine (h.conv c d hcd).continuousOn (Frequently.of_forall fun n => ?_)
  exact (show ContDiffOn ℝ Work.Stability.smoothOrder
      (Function.uncurry (Work.Spaces.mixed c d (G (φ n)))) Work.FTS.EllipticEst.Q0 from
    (hsm (φ n)).mixed c d).continuousOn

/-! ## `C⁴` for `F 0 0`, via the `(log z, log tan θ)`-coordinates -/

/-- In the coordinates `u = log z`, `v = log tan θ` the operators `D_z` and `D_θ` become the
plain derivatives `∂_u` and `2 ∂_v`; consequently the limits `F c d` (scaled by `2^{-d}`) form a
partial-derivative tower on all of `ℝ²`, and the partial-tower lemma
`Work.FTS.StrongLWP.Sobolev.contDiffOn_four_of_partial_tower` gives `C⁴` for `F 0 0` after
composing back with `(z,θ) ↦ (log z, log tan θ)`, which is smooth on `Q0`. -/
theorem contDiffOn_four_of_LimData {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n)) (h : LimData G φ F) :
    ContDiffOn ℝ 4 (Function.uncurry (F 0 0)) Work.FTS.EllipticEst.Q0 := by
  classical
  -- the composed family (the factor `2^{-d}` makes `D_θ = 2 ∂_v` into `∂_v`)
  set S : ℕ → ℕ → ℝ → ℝ → ℝ := fun c d u v =>
    F c d (Real.exp u) (Real.arctan (Real.exp v)) / 2 ^ d with hSdef
  -- the composed map lands in the open quadrant
  have hmemQ : ∀ p : ℝ × ℝ, (Real.exp p.1, Real.arctan (Real.exp p.2))
      ∈ Work.FTS.EllipticEst.Q0 := by
    intro p
    refine Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos p.1, ?_, ?_⟩
    · rw [Real.arctan_pos]; exact Real.exp_pos p.2
    · exact Real.arctan_lt_pi_div_two _
  have hΦcont : Continuous fun p : ℝ × ℝ =>
      (Real.exp p.1, Real.arctan (Real.exp p.2)) := by fun_prop
  -- continuity of every tower entry on `ℝ²`
  have hcont : ∀ a b : ℕ, a + b ≤ 4 →
      ContinuousOn (fun p : ℝ × ℝ => S a b p.1 p.2) Set.univ := by
    intro a b hab
    have h1 : ContinuousOn (fun p : ℝ × ℝ =>
        F a b (Real.exp p.1) (Real.arctan (Real.exp p.2))) Set.univ :=
      (h.continuousOn hsm a b hab).comp hΦcont.continuousOn (fun p _ => hmemQ p)
    exact h1.div_const _
  -- the `u`-derivative relation
  have hsz : ∀ a b : ℕ, a + b ≤ 3 → ∀ u v : ℝ,
      HasDerivAt (fun u' : ℝ => S a b u' v) (S (a + 1) b u v) u := by
    intro a b hab u v
    have hθ : Real.arctan (Real.exp v) ∈ Set.Ioo (0 : ℝ) (π / 2) :=
      ⟨by rw [Real.arctan_pos]; exact Real.exp_pos v, Real.arctan_lt_pi_div_two _⟩
    have hzQ : (Real.exp u, Real.arctan (Real.exp v)) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos u, hθ⟩
    have hd := h.dz a b hab (Real.exp u) (Real.arctan (Real.exp v)) hzQ
    have hcomp := hd.comp u (Real.hasDerivAt_exp u)
    have hval : F (a + 1) b (Real.exp u) (Real.arctan (Real.exp v)) / Real.exp u
        * Real.exp u = F (a + 1) b (Real.exp u) (Real.arctan (Real.exp v)) := by
      field_simp
    rw [hval] at hcomp
    have h2 := hcomp.div_const (2 ^ b)
    show HasDerivAt (fun u' : ℝ => F a b (Real.exp u') (Real.arctan (Real.exp v)) / 2 ^ b)
      (F (a + 1) b (Real.exp u) (Real.arctan (Real.exp v)) / 2 ^ b) u
    exact h2
  -- the `v`-derivative relation
  have hth : ∀ a b : ℕ, a + b ≤ 3 → ∀ u v : ℝ,
      HasDerivAt (fun v' : ℝ => S a b u v') (S a (b + 1) u v) v := by
    intro a b hab u v
    have hθ : Real.arctan (Real.exp v) ∈ Set.Ioo (0 : ℝ) (π / 2) :=
      ⟨by rw [Real.arctan_pos]; exact Real.exp_pos v, Real.arctan_lt_pi_div_two _⟩
    have hzQ : (Real.exp u, Real.arctan (Real.exp v)) ∈ Work.FTS.EllipticEst.Q0 :=
      Work.FTS.EllipticEst.mem_Q0.mpr ⟨Real.exp_pos u, hθ⟩
    have hd := h.dth a b hab (Real.exp u) (Real.arctan (Real.exp v)) hzQ
    have hcomp := hd.comp v (hasDerivAt_arctan_exp v)
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
    have hgoal : HasDerivAt (fun v' : ℝ => F a b (Real.exp u) (Real.arctan (Real.exp v')) / 2 ^ b)
        (F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v)) / 2 / 2 ^ b) v := h2
    have hval2 : F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v)) / 2 / 2 ^ b
        = F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v)) / 2 ^ (b + 1) := by
      rw [pow_succ]
      ring
    rw [hval2] at hgoal
    show HasDerivAt (fun v' : ℝ => F a b (Real.exp u) (Real.arctan (Real.exp v')) / 2 ^ b)
      (F a (b + 1) (Real.exp u) (Real.arctan (Real.exp v)) / 2 ^ (b + 1)) v
    exact hgoal
  -- the partial-derivative tower on `ℝ²`
  have h4 := Work.FTS.StrongLWP.Sobolev.contDiffOn_four_of_partial_tower
    (φ := fun u v => S 0 0 u v) (D := S) isOpen_univ (fun u v => rfl) hcont
    (fun a b hab z θ _ => hsz a b hab z θ) (fun a b hab z θ _ => hth a b hab z θ)
  -- transfer back through the smooth inverse coordinate change
  have hcomp2 : ContDiffOn ℝ 4
      ((fun p : ℝ × ℝ => S 0 0 p.1 p.2) ∘
        (fun p : ℝ × ℝ => (Real.log p.1, Real.log (Real.tan p.2))))
      Work.FTS.EllipticEst.Q0 :=
    h4.comp (contDiffOn_logLog_Q0 4) (fun p _ => Set.mem_univ _)
  refine hcomp2.congr fun p hp => ?_
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
  have htan : Real.tan p.2 ≠ 0 :=
    ne_of_gt (Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθ1)
  have hθπ : p.2 ∈ Set.Ioo (-(π / 2)) (π / 2) :=
    ⟨by linarith [Real.pi_pos], by linarith⟩
  simp only [Function.comp_apply, Function.uncurry]
  rw [hSdef]
  simp only [Real.exp_log hz, Real.exp_log (Real.tan_pos_of_pos_of_lt_pi_div_two hθ0 hθ1),
    Real.arctan_tan hθπ.1 hθπ.2, pow_zero, div_one]

/-! ## Identification of the limits with the mixed derivatives of `F 0 0` -/

/-- **The limits are the mixed derivatives of the limit function.**  This uses only the tower
relations of `LimData` and the *definitional* identities `DzIter (c+1) = Dz ∘ DzIter c` and
`DthIter (d+1) = Dth ∘ DthIter d`. -/
theorem identify {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (h : LimData G φ F) :
    ∀ (c d : ℕ), c + d ≤ 4 → Set.EqOn (fun p : ℝ × ℝ => F c d p.1 p.2)
      (fun p : ℝ × ℝ => Work.Spaces.mixed c d (F 0 0) p.1 p.2)
      Work.FTS.EllipticEst.Q0 := by
  classical
  -- first: `F 0 d = D_θ^d (F 0 0)`, by the `θ`-tower relations
  have step1 : ∀ d : ℕ, d ≤ 4 → ∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      F 0 d z θ = Work.Spaces.DthIter d (F 0 0) z θ := by
    intro d
    induction d with
    | zero => intro _ z θ _; rfl
    | succ d ih =>
        intro hd z θ hzθ
        have hprev : d ≤ 4 := by omega
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
        have hval := (h.dth 0 d (by omega) z θ hzθ).deriv
        calc F 0 (d + 1) z θ
            = Real.sin (2 * θ) * (F 0 (d + 1) z θ / Real.sin (2 * θ)) := by field_simp
          _ = Real.sin (2 * θ) * deriv (fun θ' : ℝ => F 0 d z θ') θ := by rw [hval]
          _ = Real.sin (2 * θ) *
                deriv (fun θ' : ℝ => Work.Spaces.DthIter d (F 0 0) z θ') θ := by rw [hderiv]
          _ = Work.Spaces.DthIter (d + 1) (F 0 0) z θ := rfl
  -- then: `F c d = D_z^c (D_θ^d (F 0 0))`, by the `z`-tower relations
  have step2 : ∀ d : ℕ, d ≤ 4 → ∀ c : ℕ, c + d ≤ 4 → ∀ z θ : ℝ,
      (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
      F c d z θ = Work.Spaces.DzIter c (Work.Spaces.DthIter d (F 0 0)) z θ := by
    intro d hd c
    induction c with
    | zero =>
        intro hcd z θ hzθ
        exact step1 d hd z θ hzθ
    | succ c ih =>
        intro hcd z θ hzθ
        have hprev : c + d ≤ 4 := by omega
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
        have hval := (h.dz c d (by omega) z θ hzθ).deriv
        calc F (c + 1) d z θ
            = z * (F (c + 1) d z θ / z) := by field_simp
          _ = z * deriv (fun z' : ℝ => F c d z' θ) z := by rw [hval]
          _ = z * deriv (fun z' : ℝ =>
                Work.Spaces.DzIter c (Work.Spaces.DthIter d (F 0 0)) z' θ) z := by rw [hderiv]
          _ = Work.Spaces.DzIter (c + 1) (Work.Spaces.DthIter d (F 0 0)) z θ := rfl
  intro c d hcd p hp
  have hd4 : d ≤ 4 := by omega
  exact step2 d hd4 c hcd p.1 p.2 hp

/-! ## The tower relations for the limits -/

/-- **The tower relations of `LimData` from the convergence alone.**  Differentiating the
*definitional* identities `mixed (c+1) d (G n) = D_z (mixed c d (G n))` and
`mixed c (d+1) (G n) = D_θ (mixed c d (G n))` along the convergent subsequence gives the two
relations `D_z (F c d) = F (c+1) d` and `D_θ (F c d) = F c (d+1)`; the second one uses the
commutation `D_θ ∘ D_z^c = D_z^c ∘ D_θ` on the `C^∞` functions `G (φ n)`
(`DzDthIterCommOn_smooth`). -/
theorem limData_of_conv {G : ℕ → ℝ → ℝ → ℝ} {φ : ℕ → ℕ} {F : ℕ → ℕ → ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, Work.FTS.EllipticEst.SmoothOpen (G n))
    (hconv : ∀ (c d : ℕ), c + d ≤ 4 → TendstoLocallyUniformlyOn
      (fun n p => Work.Spaces.mixed c d (G (φ n)) p.1 p.2)
      (fun p => F c d p.1 p.2) Filter.atTop Work.FTS.EllipticEst.Q0) :
    LimData G φ F := by
  refine ⟨hconv, ?_, ?_⟩
  · -- the `z`-relations
    intro c d hcd z θ hzθ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have hsl : ∀ z' ∈ Set.Ioi (0 : ℝ), (z', θ) ∈ Work.FTS.EllipticEst.Q0 :=
      fun z' hz' => ⟨hz', hθ0, hθ1⟩
    have hinv : ContinuousOn (fun p : ℝ × ℝ => (p.1)⁻¹) Work.FTS.EllipticEst.Q0 :=
      continuousOn_fst.inv₀ fun p hp => ne_of_gt (Work.FTS.EllipticEst.mem_Q0.mp hp).1
    have hdiv : TendstoLocallyUniformlyOn
        (fun (n : ℕ) (p : ℝ × ℝ) => Work.Spaces.mixed (c + 1) d (G (φ n)) p.1 p.2 / p.1)
        (fun p : ℝ × ℝ => F (c + 1) d p.1 p.2 / p.1) Filter.atTop
        Work.FTS.EllipticEst.Q0 := by
      have h1 := tendstoLocallyUniformlyOn_mul_continuousOn
        Work.FTS.EllipticEst.isOpen_Q0 (hconv (c + 1) d (by omega)) hinv
      simpa only [div_eq_mul_inv, mul_comm] using h1
    have hf' : TendstoLocallyUniformlyOn
        (fun n (z' : ℝ) => Work.Spaces.mixed (c + 1) d (G (φ n)) z' θ / z')
        (fun z' : ℝ => F (c + 1) d z' θ / z') Filter.atTop (Set.Ioi 0) :=
      tendstoLocallyUniformlyOn_slice_fst hsl hdiv
    have hf : TendstoLocallyUniformlyOn
        (fun n (z' : ℝ) => Work.Spaces.mixed c d (G (φ n)) z' θ)
        (fun z' : ℝ => F c d z' θ) Filter.atTop (Set.Ioi 0) :=
      tendstoLocallyUniformlyOn_slice_fst hsl (hconv c d (by omega))
    have hder : ∀ᶠ n in Filter.atTop, ∀ z' ∈ Set.Ioi (0 : ℝ),
        HasDerivAt (fun z'' : ℝ => Work.Spaces.mixed c d (G (φ n)) z'' θ)
          (Work.Spaces.mixed (c + 1) d (G (φ n)) z' θ / z') z' := by
      refine Eventually.of_forall fun n z' hz' => ?_
      have hd := ((hsm (φ n)).mixed c d).hasDerivAt_slice ⟨hθ0, hθ1⟩ hz'
      rwa [(mixed_partials_of_smoothOpen c d (hsm (φ n))).1 z' θ (hsl z' hz')] at hd
    have hmain : HasDerivAt (fun z' : ℝ => F c d z' θ)
        ((fun z' : ℝ => F (c + 1) d z' θ / z') z) z := by
      refine hasDerivAt_of_tendstoLocallyUniformlyOn
        (f' := fun n (z' : ℝ) => Work.Spaces.mixed (c + 1) d (G (φ n)) z' θ / z')
        (g' := fun z' : ℝ => F (c + 1) d z' θ / z') isOpen_Ioi hf' hder ?_ hz
      intro z' hz'
      exact hf.tendsto_at hz'
    exact hmain
  · -- the `θ`-relations
    intro c d hcd z θ hzθ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have hsl : ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2), (z, θ') ∈ Work.FTS.EllipticEst.Q0 :=
      fun θ' hθ' => ⟨hz, hθ'⟩
    have hsin0 : ∀ p ∈ Work.FTS.EllipticEst.Q0, Real.sin (2 * p.2) ≠ 0 := by
      intro p hp
      obtain ⟨-, hp0, hp1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
      exact ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos]))
    have hinv : ContinuousOn (fun p : ℝ × ℝ => (Real.sin (2 * p.2))⁻¹)
        Work.FTS.EllipticEst.Q0 :=
      ((Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn).inv₀ hsin0
    have hdiv : TendstoLocallyUniformlyOn
        (fun (n : ℕ) (p : ℝ × ℝ) => Work.Spaces.mixed c (d + 1) (G (φ n)) p.1 p.2
          / Real.sin (2 * p.2))
        (fun p : ℝ × ℝ => F c (d + 1) p.1 p.2 / Real.sin (2 * p.2)) Filter.atTop
        Work.FTS.EllipticEst.Q0 := by
      have h1 := tendstoLocallyUniformlyOn_mul_continuousOn
        Work.FTS.EllipticEst.isOpen_Q0 (hconv c (d + 1) (by omega)) hinv
      simpa only [div_eq_mul_inv, mul_comm] using h1
    have hf' : TendstoLocallyUniformlyOn
        (fun n (θ' : ℝ) => Work.Spaces.mixed c (d + 1) (G (φ n)) z θ' / Real.sin (2 * θ'))
        (fun θ' : ℝ => F c (d + 1) z θ' / Real.sin (2 * θ')) Filter.atTop
        (Set.Ioo 0 (π / 2)) :=
      tendstoLocallyUniformlyOn_slice_snd hsl hdiv
    have hf : TendstoLocallyUniformlyOn
        (fun n (θ' : ℝ) => Work.Spaces.mixed c d (G (φ n)) z θ')
        (fun θ' : ℝ => F c d z θ') Filter.atTop (Set.Ioo 0 (π / 2)) :=
      tendstoLocallyUniformlyOn_slice_snd hsl (hconv c d (by omega))
    have hder : ∀ᶠ n in Filter.atTop, ∀ θ' ∈ Set.Ioo (0 : ℝ) (π / 2),
        HasDerivAt (fun θ'' : ℝ => Work.Spaces.mixed c d (G (φ n)) z θ'')
          (Work.Spaces.mixed c (d + 1) (G (φ n)) z θ' / Real.sin (2 * θ')) θ' := by
      refine Eventually.of_forall fun n θ' hθ' => ?_
      have hd : HasDerivAt (fun θ'' : ℝ => Work.Spaces.mixed c d (G (φ n)) z θ'')
          (Work.Spaces.pth (Work.Spaces.mixed c d (G (φ n))) z θ') θ' :=
        (((hsm (φ n)).mixed c d).curry_θ hz).contDiffAt
          (isOpen_Ioo.mem_nhds hθ') |>.differentiableAt (by simp) |>.hasDerivAt
      rwa [(mixed_partials_of_smoothOpen c d (hsm (φ n))).2.1 z θ' (hsl θ' hθ')] at hd
    have hmain : HasDerivAt (fun θ' : ℝ => F c d z θ')
        ((fun θ' : ℝ => F c (d + 1) z θ' / Real.sin (2 * θ')) θ) θ := by
      refine hasDerivAt_of_tendstoLocallyUniformlyOn
        (f' := fun n (θ' : ℝ) => Work.Spaces.mixed c (d + 1) (G (φ n)) z θ' / Real.sin (2 * θ'))
        (g' := fun θ' : ℝ => F c (d + 1) z θ' / Real.sin (2 * θ')) isOpen_Ioo hf' hder ?_
        ⟨hθ0, hθ1⟩
      intro θ' hθ'
      exact hf.tendsto_at hθ'
    exact hmain


end Work.FTS.StrongEps.LocUnif
