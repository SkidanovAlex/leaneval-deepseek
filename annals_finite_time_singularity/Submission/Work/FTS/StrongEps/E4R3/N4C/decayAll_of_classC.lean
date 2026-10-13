/-
# `E4R3/N4C/decayAll_of_classC` — `ClassC ∧ CoerAdmO ⇒ DecayAll 4`

The honest (open-quadrant) row table of `E4R3/N4C` consumes the **`L¹`-decay of the plain
partials** `DecayAll 4 g` of the test profile (`N4C.HAdm`).  `ClassC` deliberately carries *no*
decay field (it is the linear class of `FTS_HARD_DESIGN.md` §1, closed under `+` and `c • ·`),
but it does carry `BdryTraces α 6 g` and `norm : normTh g = g`, and those two fields are enough:

* **angular interior.**  For `θ ∈ (0,π/2)`, `BdryTraces α 6 g` gives
  `z·(mixed b a g z θ·w z)² → 0` at `+∞`, and `w z ≥ 1` for `z ≥ 1`, hence `mixed b a g z θ → 0`
  (`H2.HQ.BdryTraces.tendsto_atTop_zero`).  Since `D_z = z∂_z` and `D_θ = sin(2θ)∂_θ` are
  triangular changes of variable (`D_z^n = Σ_k S(n,k) z^k∂_z^k`,
  `D_θ^m = Σ_{r≤m} a_{m,r}(θ)∂_θ^r`, with diagonal `S(n,n) = 1` resp. `a_{m,m} = sin(2θ)^m ≠ 0`
  at interior angles), the decay of every *mixed* derivative implies the decay of every *plain*
  partial `pzIter j (pthIter i g) → 0` — the two `Tendsto`-inversions
  `tendsto_pzIter_of_tendsto_DzIter` (radial) and
  `tendsto_pzIter_pthIter_of_tendsto_pzIter_DthIter` (angular).

* **the two endpoints `θ = 0, π/2`.**  Here `norm` (i.e. `normTh g = g`) forces `g z θ = 0` for
  every `θ ∉ (0,π/2)`, so the angular slices at `0` and `π/2` vanish on a half-line.  A function
  vanishing on `(-∞,c]` has `deriv = 0` at `c` (the `deriv` of a non-differentiable function is
  `0` by definition, and if it is differentiable the one-sided derivative forces `0`), which gives
  `pthIter i g z 0 = 0` (`pthIter_eq_zero_of_forall_nonpos`) and after that
  `pzIter j (pthIter i g) z 0 = 0`, i.e. both `DecayInZ` and `DecayMixed` at the endpoints are
  *identically* zero (`DzIter_DthIter_eq_zero_of_forall_nonpos` and its right-hand twin).
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.ClassC.Defs
import Submission.Work.FTS.StrongEps.EpsE4Thr.OpenClass
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.GalBasis.GalDense.Xmb

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-! ## `scoef n n = 1`, the diagonal of the Stirling expansion of `D_z^n` -/

theorem scoef_self (n : ℕ) : Work.Spaces.scoef n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show (n + 1) * Work.Spaces.scoef n (n + 1) + Work.Spaces.scoef n n = 1
    rw [Work.Spaces.scoef_eq_zero_of_lt (Nat.lt_succ_self n), ih]
    ring

/-! ## A function vanishing on a half-line has zero derivative at its endpoint -/

/-- If `f` vanishes on `(-∞,c]` then `deriv f c = 0`. -/
theorem deriv_eq_zero_of_forall_le {f : ℝ → ℝ} {c : ℝ} (h : ∀ x, x ≤ c → f x = 0) :
    deriv f c = 0 := by
  show fderiv ℝ f c 1 = 0
  by_cases hd : DifferentiableAt ℝ f c
  · have h1 : HasFDerivWithinAt f (fderiv ℝ f c) (Set.Iic c) c :=
      hd.hasFDerivAt.hasFDerivWithinAt
    have h2 : fderivWithin ℝ f (Set.Iic c) c = fderiv ℝ f c :=
      h1.fderivWithin (uniqueDiffWithinAt_Iic c)
    have h3 : HasFDerivWithinAt f (0 : ℝ →L[ℝ] ℝ) (Set.Iic c) c :=
      (hasFDerivWithinAt_const (𝕜 := ℝ) (0 : ℝ) c (Set.Iic c)).congr
        (fun y hy => h y hy) (h c le_rfl)
    have h4 : fderivWithin ℝ f (Set.Iic c) c = 0 :=
      h3.fderivWithin (uniqueDiffWithinAt_Iic c)
    have h5 : fderiv ℝ f c = 0 := by rw [← h2, h4]
    rw [h5]; simp
  · rw [fderiv_zero_of_not_differentiableAt hd]; simp

/-- If `f` vanishes on `[c,∞)` then `deriv f c = 0`. -/
theorem deriv_eq_zero_of_forall_ge {f : ℝ → ℝ} {c : ℝ} (h : ∀ x, c ≤ x → f x = 0) :
    deriv f c = 0 := by
  show fderiv ℝ f c 1 = 0
  by_cases hd : DifferentiableAt ℝ f c
  · have h1 : HasFDerivWithinAt f (fderiv ℝ f c) (Set.Ici c) c :=
      hd.hasFDerivAt.hasFDerivWithinAt
    have h2 : fderivWithin ℝ f (Set.Ici c) c = fderiv ℝ f c :=
      h1.fderivWithin (uniqueDiffWithinAt_Ici c)
    have h3 : HasFDerivWithinAt f (0 : ℝ →L[ℝ] ℝ) (Set.Ici c) c :=
      (hasFDerivWithinAt_const (𝕜 := ℝ) (0 : ℝ) c (Set.Ici c)).congr
        (fun y hy => h y hy) (h c le_rfl)
    have h4 : fderivWithin ℝ f (Set.Ici c) c = 0 :=
      h3.fderivWithin (uniqueDiffWithinAt_Ici c)
    have h5 : fderiv ℝ f c = 0 := by rw [← h2, h4]
    rw [h5]; simp
  · rw [fderiv_zero_of_not_differentiableAt hd]; simp

/-! ## The angular slices at `θ = 0` and `θ = π/2` of a function vanishing off the quadrant -/

/-- If `f` vanishes on the closed half-plane `θ ≤ 0` then so does every `pthIter i f`. -/
theorem pthIter_eq_zero_of_forall_nonpos {f : ℝ → ℝ → ℝ} (h : ∀ z θ, θ ≤ 0 → f z θ = 0) :
    ∀ i z θ, θ ≤ 0 → Work.Spaces.pthIter i f z θ = 0 := by
  intro i
  induction i with
  | zero => exact h
  | succ n ih =>
    intro z θ hθ
    rcases lt_or_eq_of_le hθ with hlt | heq
    · have hev : (fun θ' : ℝ => Work.Spaces.pthIter n f z θ') =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
        refine Filter.eventuallyEq_iff_exists_mem.mpr
          ⟨Set.Iio 0, isOpen_Iio.mem_nhds hlt, fun θ' hθ' => ih z θ' (le_of_lt hθ')⟩
      show deriv (fun θ' : ℝ => Work.Spaces.pthIter n f z θ') θ = 0
      rw [hev.deriv_eq, deriv_const]
    · subst heq
      exact deriv_eq_zero_of_forall_le (fun θ' hθ' => ih z θ' hθ')

/-- If `f` vanishes on the closed half-plane `θ ≥ π/2` then so does every `pthIter i f`. -/
theorem pthIter_eq_zero_of_forall_ge_pi_half {f : ℝ → ℝ → ℝ}
    (h : ∀ z θ, Real.pi / 2 ≤ θ → f z θ = 0) :
    ∀ i z θ, Real.pi / 2 ≤ θ → Work.Spaces.pthIter i f z θ = 0 := by
  intro i
  induction i with
  | zero => exact h
  | succ n ih =>
    intro z θ hθ
    rcases lt_or_eq_of_le hθ with hlt | heq
    · have hev : (fun θ' : ℝ => Work.Spaces.pthIter n f z θ') =ᶠ[𝓝 θ] fun _ => (0 : ℝ) := by
        refine Filter.eventuallyEq_iff_exists_mem.mpr
          ⟨Set.Ioi (Real.pi / 2), isOpen_Ioi.mem_nhds hlt, fun θ' hθ' => ih z θ' (le_of_lt hθ')⟩
      show deriv (fun θ' : ℝ => Work.Spaces.pthIter n f z θ') θ = 0
      rw [hev.deriv_eq, deriv_const]
    · subst heq
      exact deriv_eq_zero_of_forall_ge (fun θ' hθ' => ih z θ' hθ')

/-- The `θ = 0` slices of `∂_z^j∂_θ^i f` vanish identically for a function vanishing at `θ ≤ 0`. -/
theorem pzIter_pthIter_eq_zero_of_forall_nonpos {f : ℝ → ℝ → ℝ}
    (h : ∀ z θ, θ ≤ 0 → f z θ = 0) (j i : ℕ) (z : ℝ) :
    Work.Spaces.pzIter j (Work.Spaces.pthIter i f) z 0 = 0 := by
  induction j generalizing z with
  | zero => simpa using pthIter_eq_zero_of_forall_nonpos h i z 0 le_rfl
  | succ n ih =>
    have hfun : (fun z' : ℝ => Work.Spaces.pzIter n (Work.Spaces.pthIter i f) z' 0)
        = fun _ : ℝ => (0 : ℝ) := funext fun z' => ih z'
    show deriv (fun z' : ℝ => Work.Spaces.pzIter n (Work.Spaces.pthIter i f) z' 0) z = 0
    rw [hfun, deriv_const]

/-- The `θ = π/2` slices of `∂_z^j∂_θ^i f` vanish identically for a function vanishing at
`θ ≥ π/2`. -/
theorem pzIter_pthIter_eq_zero_of_forall_ge_pi_half {f : ℝ → ℝ → ℝ}
    (h : ∀ z θ, Real.pi / 2 ≤ θ → f z θ = 0) (j i : ℕ) (z : ℝ) :
    Work.Spaces.pzIter j (Work.Spaces.pthIter i f) z (Real.pi / 2) = 0 := by
  induction j generalizing z with
  | zero => simpa using pthIter_eq_zero_of_forall_ge_pi_half h i z (Real.pi / 2) le_rfl
  | succ n ih =>
    have hfun : (fun z' : ℝ => Work.Spaces.pzIter n (Work.Spaces.pthIter i f) z' (Real.pi / 2))
        = fun _ : ℝ => (0 : ℝ) := funext fun z' => ih z'
    show deriv (fun z' : ℝ =>
      Work.Spaces.pzIter n (Work.Spaces.pthIter i f) z' (Real.pi / 2)) z = 0
    rw [hfun, deriv_const]

/-- The `θ = 0` slices of the mixed operators `D_z^b D_θ^a f` vanish identically for a function
vanishing at `θ ≤ 0`. -/
theorem DzIter_DthIter_eq_zero_of_forall_nonpos {f : ℝ → ℝ → ℝ}
    (h : ∀ z θ, θ ≤ 0 → f z θ = 0) :
    ∀ a b z, Work.Spaces.DzIter b (Work.Spaces.DthIter a f) z 0 = 0 := by
  have hD : ∀ a z, Work.Spaces.DthIter a f z 0 = 0 := by
    intro a
    induction a with
    | zero => intro z; exact h z 0 le_rfl
    | succ n ih =>
      intro z
      show Real.sin (2 * 0) * Work.Spaces.pth (Work.Spaces.DthIter n f) z 0 = 0
      rw [show (2 : ℝ) * 0 = 0 by ring, Real.sin_zero, zero_mul]
  intro a b
  induction b with
  | zero => intro z; simpa using hD a z
  | succ n ih =>
    intro z
    have hfun : (fun z' : ℝ => Work.Spaces.DzIter n (Work.Spaces.DthIter a f) z' 0)
        = fun _ : ℝ => (0 : ℝ) := funext fun z' => ih z'
    show z * deriv (fun z' : ℝ => Work.Spaces.DzIter n (Work.Spaces.DthIter a f) z' 0) z = 0
    rw [hfun, deriv_const, mul_zero]

/-- The `θ = π/2` slices of the mixed operators `D_z^b D_θ^a f` vanish identically for a function
vanishing at `θ ≥ π/2`. -/
theorem DzIter_DthIter_eq_zero_of_forall_ge_pi_half {f : ℝ → ℝ → ℝ}
    (h : ∀ z θ, Real.pi / 2 ≤ θ → f z θ = 0) :
    ∀ a b z, Work.Spaces.DzIter b (Work.Spaces.DthIter a f) z (Real.pi / 2) = 0 := by
  have hD : ∀ a z, Work.Spaces.DthIter a f z (Real.pi / 2) = 0 := by
    intro a
    induction a with
    | zero => intro z; exact h z (Real.pi / 2) le_rfl
    | succ n ih =>
      intro z
      show Real.sin (2 * (Real.pi / 2))
        * Work.Spaces.pth (Work.Spaces.DthIter n f) z (Real.pi / 2) = 0
      rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi, zero_mul]
  intro a b
  induction b with
  | zero => intro z; simpa using hD a z
  | succ n ih =>
    intro z
    have hfun : (fun z' : ℝ => Work.Spaces.DzIter n (Work.Spaces.DthIter a f) z' (Real.pi / 2))
        = fun _ : ℝ => (0 : ℝ) := funext fun z' => ih z'
    show z * deriv (fun z' : ℝ =>
      Work.Spaces.DzIter n (Work.Spaces.DthIter a f) z' (Real.pi / 2)) z = 0
    rw [hfun, deriv_const, mul_zero]

/-! ## The two triangular inversions -/

/-- **Radial inversion.**  At an interior angle, if all the mixed radial derivatives `D_z^b F`
(`b ≤ B`) decay at `+∞` then so do all the plain partials `∂_z^j F` (`j ≤ B`), because
`D_z^n = Σ_{k≤n} S(n,k) z^k ∂_z^k` with `S(n,n) = 1` and `z^k ≥ 1` for `z ≥ 1`. -/
theorem tendsto_pzIter_of_tendsto_DzIter {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) {B : ℕ}
    (hD : ∀ b ≤ B, Tendsto (fun z => Work.Spaces.DzIter b F z θ) atTop (𝓝 0)) :
    ∀ j ≤ B, Tendsto (fun z => Work.Spaces.pzIter j F z θ) atTop (𝓝 0) := by
  have hexp : ∀ n (z : ℝ), 0 < z → Work.Spaces.DzIter n F z θ
      = ∑ k ∈ Finset.range (n + 1), (Work.Spaces.scoef n k : ℝ)
          * (z ^ k * Work.Spaces.pzIter k F z θ) := by
    intro n z hz
    exact Work.FTS.GalBasis.Xmb.DzIter_eq_sum_scoef_of_contDiffOn F Work.FTS.EllipticEst.Q0
      Work.FTS.EllipticEst.isOpen_Q0 n (Work.FTS.EllipticEst.SmoothOpen.forall hsm (n + 1)) z θ
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)
  have key : ∀ j, j ≤ B → ∀ k ≤ j,
      Tendsto (fun z => z ^ k * Work.Spaces.pzIter k F z θ) atTop (𝓝 0) := by
    intro j
    induction j with
    | zero =>
      intro _ k hk
      have hk0 : k = 0 := Nat.eq_zero_of_le_zero hk
      subst hk0
      simpa using hD 0 (Nat.zero_le B)
    | succ n ih =>
      intro hn k hk
      rcases eq_or_lt_of_le hk with heq | hlt
      · subst heq
        have hprev := ih (by omega)
        have hDs : Tendsto (fun z => Work.Spaces.DzIter (n + 1) F z θ) atTop (𝓝 0) :=
          hD (n + 1) hn
        have hsum : Tendsto (fun z => ∑ k ∈ Finset.range (n + 1),
              (Work.Spaces.scoef (n + 1) k : ℝ) * (z ^ k * Work.Spaces.pzIter k F z θ))
            atTop (𝓝 0) := by
          have hmain : Tendsto (fun z => ∑ k ∈ Finset.range (n + 1),
              (Work.Spaces.scoef (n + 1) k : ℝ) * (z ^ k * Work.Spaces.pzIter k F z θ))
              atTop (𝓝 (∑ k ∈ Finset.range (n + 1), (0 : ℝ))) := by
            refine tendsto_finsetSum _ (fun k hk => ?_)
            simpa using (hprev k (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))).const_mul
              (↑(Work.Spaces.scoef (n + 1) k))
          simpa using hmain
        have hcomb : Tendsto (fun z => Work.Spaces.DzIter (n + 1) F z θ
              - ∑ k ∈ Finset.range (n + 1),
                  (Work.Spaces.scoef (n + 1) k : ℝ) * (z ^ k * Work.Spaces.pzIter k F z θ))
            atTop (𝓝 0) := by
          simpa using hDs.sub hsum
        refine hcomb.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
        show Work.Spaces.DzIter (n + 1) F z θ
            - ∑ k ∈ Finset.range (n + 1),
                (Work.Spaces.scoef (n + 1) k : ℝ) * (z ^ k * Work.Spaces.pzIter k F z θ)
          = z ^ (n + 1) * Work.Spaces.pzIter (n + 1) F z θ
        rw [hexp (n + 1) z hz, Finset.sum_range_succ, scoef_self]
        push_cast
        ring
      · exact ih (by omega) k (by omega)
  intro j hj
  have hzj : Tendsto (fun z => z ^ j * Work.Spaces.pzIter j F z θ) atTop (𝓝 0) :=
    key j hj j le_rfl
  have hnorm : Tendsto (fun z => |Work.Spaces.pzIter j F z θ|) atTop (𝓝 0) := by
    have hgn : Tendsto (fun z => |z ^ j * Work.Spaces.pzIter j F z θ|) atTop (𝓝 0) := by
      simpa [Real.norm_eq_abs] using hzj.norm
    refine squeeze_zero' (Eventually.of_forall (fun z => abs_nonneg _)) ?_ hgn
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with z hz1
    have h1 : (1 : ℝ) ≤ z ^ j := one_le_pow₀ hz1
    calc |Work.Spaces.pzIter j F z θ| = |Work.Spaces.pzIter j F z θ| * 1 := by ring
      _ ≤ |Work.Spaces.pzIter j F z θ| * z ^ j :=
          mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |z ^ j * Work.Spaces.pzIter j F z θ| := by
          rw [abs_mul, abs_of_nonneg (pow_nonneg (by linarith : (0 : ℝ) ≤ z) j)]
          ring
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa [Real.norm_eq_abs] using hnorm)

/-- **Angular inversion.**  At an interior angle and for a fixed radial order `j`, if all the
derivatives `∂_z^j D_θ^a F` (`a ≤ A`) decay at `+∞` then so do the plain mixed partials
`∂_z^j∂_θ^i F` (`i ≤ A`), because `D_θ^m = Σ_{r≤m} a_{m,r}(θ) ∂_θ^r` with
`a_{m,m} = sin(2θ)^m ≠ 0` at interior angles. -/
theorem tendsto_pzIter_pthIter_of_tendsto_pzIter_DthIter {F : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) {j A : ℕ}
    (hD : ∀ a ≤ A, Tendsto (fun z => Work.Spaces.pzIter j (Work.Spaces.DthIter a F) z θ)
      atTop (𝓝 0)) :
    ∀ i ≤ A, Tendsto (fun z => Work.Spaces.pzIter j (Work.Spaces.pthIter i F) z θ)
      atTop (𝓝 0) := by
  have hsinpos : 0 < Real.sin (2 * θ) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have hexp : ∀ a (z : ℝ), 0 < z → Work.Spaces.pzIter j (Work.Spaces.DthIter a F) z θ
      = ∑ r ∈ Finset.range (a + 1), Work.FTS.EllipticEst.remov.selfdth.dthCoef a r θ
          * Work.Spaces.pzIter j (Work.Spaces.pthIter r F) z θ := by
    intro a z hz
    exact Work.FTS.GalBasis.Xmb.pzIter_DthIter_expansion (U := Work.FTS.EllipticEst.Q0)
      Work.FTS.EllipticEst.isOpen_Q0 (N := a + j + 2)
      (Work.FTS.EllipticEst.SmoothOpen.forall hsm (a + j + 2))
      (b := a) (k := j) (by omega) (by omega)
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)
  have key : ∀ i, i ≤ A → ∀ r ≤ i,
      Tendsto (fun z => Work.Spaces.pzIter j (Work.Spaces.pthIter r F) z θ) atTop (𝓝 0) := by
    intro i
    induction i with
    | zero =>
      intro _ r hr
      have hr0 : r = 0 := Nat.eq_zero_of_le_zero hr
      subst hr0
      simpa using hD 0 (Nat.zero_le A)
    | succ n ih =>
      intro hn r hr
      rcases eq_or_lt_of_le hr with heq | hlt
      · subst heq
        have hprev := ih (by omega)
        have hDs : Tendsto (fun z => Work.Spaces.pzIter j (Work.Spaces.DthIter (n + 1) F) z θ)
            atTop (𝓝 0) := hD (n + 1) hn
        have hsum : Tendsto (fun z => ∑ r ∈ Finset.range (n + 1),
              Work.FTS.EllipticEst.remov.selfdth.dthCoef (n + 1) r θ
                * Work.Spaces.pzIter j (Work.Spaces.pthIter r F) z θ) atTop (𝓝 0) := by
          have hmain : Tendsto (fun z => ∑ r ∈ Finset.range (n + 1),
              Work.FTS.EllipticEst.remov.selfdth.dthCoef (n + 1) r θ
                * Work.Spaces.pzIter j (Work.Spaces.pthIter r F) z θ)
              atTop (𝓝 (∑ r ∈ Finset.range (n + 1), (0 : ℝ))) := by
            refine tendsto_finsetSum _ (fun r hr => ?_)
            simpa using (hprev r
              (Nat.lt_succ_iff.mp (Finset.mem_range.mp hr))).const_mul
                (Work.FTS.EllipticEst.remov.selfdth.dthCoef (n + 1) r θ)
          simpa using hmain
        have hcomb : Tendsto (fun z =>
              Work.Spaces.pzIter j (Work.Spaces.DthIter (n + 1) F) z θ
              - ∑ r ∈ Finset.range (n + 1),
                  Work.FTS.EllipticEst.remov.selfdth.dthCoef (n + 1) r θ
                    * Work.Spaces.pzIter j (Work.Spaces.pthIter r F) z θ) atTop (𝓝 0) := by
          simpa using hDs.sub hsum
        have hscaled : Tendsto (fun z => ((Real.sin (2 * θ)) ^ (n + 1))⁻¹
              * (Work.Spaces.pzIter j (Work.Spaces.DthIter (n + 1) F) z θ
                - ∑ r ∈ Finset.range (n + 1),
                    Work.FTS.EllipticEst.remov.selfdth.dthCoef (n + 1) r θ
                      * Work.Spaces.pzIter j (Work.Spaces.pthIter r F) z θ)) atTop (𝓝 0) := by
          have := hcomb.const_mul (((Real.sin (2 * θ)) ^ (n + 1))⁻¹)
          simpa using this
        refine hscaled.congr' ?_
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
        have hid : Work.Spaces.pzIter j (Work.Spaces.pthIter (n + 1) F) z θ
            = ((Real.sin (2 * θ)) ^ (n + 1))⁻¹
              * (Work.Spaces.pzIter j (Work.Spaces.DthIter (n + 1) F) z θ
                - ∑ r ∈ Finset.range (n + 1),
                    Work.FTS.EllipticEst.remov.selfdth.dthCoef (n + 1) r θ
                      * Work.Spaces.pzIter j (Work.Spaces.pthIter r F) z θ) := by
          have hx := hexp (n + 1) z hz
          rw [hx, Finset.sum_range_succ, Work.FTS.EllipticEst.remov.selfdth.dthCoef_self]
          have hsp : Real.sin (2 * θ) ^ (n + 1) ≠ 0 := pow_ne_zero _ (ne_of_gt hsinpos)
          field_simp
          ring
        exact hid.symm
      · exact ih (by omega) r (by omega)
  intro i hi
  exact key i hi i le_rfl

/-! ## The target -/

theorem decayAll_of_classC {α : ℝ} (hα : 0 < α) {g : Work.FTS.Galerkin.Fn}
    (hg : Work.FTS.ClassC.ClassC α g) (hco : Work.FTS.StrongEps.EpsE4Thr.CoerAdmO α g) :
    Work.Spaces.DecayAll 4 g := by
  -- `normTh g = g` kills the two endpoint angles
  have hzeroL : ∀ z θ, θ ≤ 0 → g z θ = 0 := by
    intro z θ hθ
    have h1 : g z θ = Work.FTS.ClassC.normTh g z θ := (congrFun (congrFun hg.norm z) θ).symm
    rw [h1, Work.FTS.ClassC.normTh_apply_of_not_mem]
    intro hmem
    exact absurd hmem.1 (not_lt.mpr hθ)
  have hzeroR : ∀ z θ, Real.pi / 2 ≤ θ → g z θ = 0 := by
    intro z θ hθ
    have h1 : g z θ = Work.FTS.ClassC.normTh g z θ := (congrFun (congrFun hg.norm z) θ).symm
    rw [h1, Work.FTS.ClassC.normTh_apply_of_not_mem]
    intro hmem
    exact absurd hmem.2 (not_lt.mpr hθ)
  constructor
  · -- `DecayInZ 4`
    intro j i hij θ hθ
    rcases lt_or_eq_of_le hθ.1 with hθ0 | hθ0
    · rcases lt_or_eq_of_le hθ.2 with hθ2 | hθ2
      · -- interior angle
        have hθI : θ ∈ Set.Ioo 0 (π / 2) := ⟨hθ0, hθ2⟩
        have hmix : ∀ a b : ℕ, a + b ≤ 4 →
            Tendsto (fun z => Work.Spaces.DzIter b (Work.Spaces.DthIter a g) z θ)
              atTop (𝓝 0) :=
          fun a b hab => Work.FTS.H2.HQ.BdryTraces.tendsto_atTop_zero hg.tr (by omega) hθI
        have hstep : ∀ a k, a + k ≤ 4 →
            Tendsto (fun z => Work.Spaces.pzIter k (Work.Spaces.DthIter a g) z θ)
              atTop (𝓝 0) := by
          intro a k hak
          have ha : a ≤ 4 := by omega
          refine tendsto_pzIter_of_tendsto_DzIter (B := 4 - a) (hg.reg.DthIter a) hθI ?_ k ?_
          · intro b hb
            exact hmix a b (by omega)
          · omega
        refine tendsto_pzIter_pthIter_of_tendsto_pzIter_DthIter hg.reg hθI (j := j)
          (A := i) ?_ i le_rfl
        · intro a ha
          exact hstep a j (by omega)
      · -- `θ = π/2`
        subst hθ2
        have hfun : (fun z : ℝ => Work.Spaces.pzIter j (Work.Spaces.pthIter i g) z (Real.pi / 2))
            = fun _ : ℝ => (0 : ℝ) :=
          funext fun z => pzIter_pthIter_eq_zero_of_forall_ge_pi_half hzeroR j i z
        rw [hfun]
        exact tendsto_const_nhds
    · -- `θ = 0`
      subst hθ0
      have hfun : (fun z : ℝ => Work.Spaces.pzIter j (Work.Spaces.pthIter i g) z 0)
          = fun _ : ℝ => (0 : ℝ) :=
        funext fun z => pzIter_pthIter_eq_zero_of_forall_nonpos hzeroL j i z
      rw [hfun]
      exact tendsto_const_nhds
  · -- `DecayMixed 4`
    intro a b hab θ hθ
    rcases lt_or_eq_of_le hθ.1 with hθ0 | hθ0
    · rcases lt_or_eq_of_le hθ.2 with hθ2 | hθ2
      · exact Work.FTS.H2.HQ.BdryTraces.tendsto_atTop_zero hg.tr (by omega) ⟨hθ0, hθ2⟩
      · subst hθ2
        have hfun : (fun z : ℝ => Work.Spaces.mixed b a g z (Real.pi / 2)) =
            fun _ : ℝ => (0 : ℝ) :=
          funext fun z => DzIter_DthIter_eq_zero_of_forall_ge_pi_half hzeroR a b z
        rw [hfun]
        exact tendsto_const_nhds
    · subst hθ0
      have hfun : (fun z : ℝ => Work.Spaces.mixed b a g z 0) = fun _ : ℝ => (0 : ℝ) :=
        funext fun z => DzIter_DthIter_eq_zero_of_forall_nonpos hzeroL a b z
      rw [hfun]
      exact tendsto_const_nhds

end Work.FTS.StrongEps.E4R3.N4C
