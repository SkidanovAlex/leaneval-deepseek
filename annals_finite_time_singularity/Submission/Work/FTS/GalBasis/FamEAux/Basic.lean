import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Tactic.NormNum.BigOperators
import Submission.Work.FTS.GalBasis.Defs
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.DzDthIterCommOn

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.GalBasis

open Work.FTS.Galerkin (Fn galFun)
open Work.Spaces

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## Plumbing: smoothness, congruence and linearity of the plain iterated derivatives -/

/-- `pzIter i f z θ` is the `i`-fold iterate of `deriv` applied to the `z`-slice. -/
theorem pzIter_apply_eq_iterate_deriv (i : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter i f z θ = deriv^[i] (fun z' => f z' θ) z := by
  induction i generalizing z with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.pzIter_succ, Work.Spaces.pz, Function.iterate_succ_apply']
      congr 1
      funext z'
      exact ih z'

/-- `pthIter i f z θ` is the `i`-fold iterate of `deriv` applied to the `θ`-slice. -/
theorem pthIter_apply_eq_iterate_deriv (i : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter i f z θ = deriv^[i] (fun θ' => f z θ') θ := by
  induction i generalizing θ with
  | zero => rfl
  | succ n ih =>
      rw [Work.Spaces.pthIter_succ, Work.Spaces.pth, Function.iterate_succ_apply']
      congr 1
      funext θ'
      exact ih θ'

/-- `ContDiffOn` is stable under the plain `z`-partial, losing one order. -/
theorem famAux_contDiffOn_uncurry_pz_le {X : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) (n : ℕ)
    (hX : ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) (Function.uncurry X) V) :
    ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.pz X)) V := by
  have hdiff : DifferentiableOn ℝ (Function.uncurry X) V :=
    hX.differentiableOn (by simp)
  have h1 : ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (fderiv ℝ (Function.uncurry X)) V :=
    hX.fderiv_of_isOpen hV (by simp)
  have h2 : ContDiffOn ℝ ((n : ℕ) : ℕ∞ω)
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry X) p) (1, 0)) V :=
    h1.clm_apply contDiffOn_const
  refine h2.congr (fun p hp => ?_)
  exact deriv_slice_fst _ _ _ ((hdiff.differentiableAt (hV.mem_nhds hp)))

/-- Iterated version: the `i`-th plain `z`-partial loses `i` orders of smoothness. -/
theorem famAux_contDiffOn_uncurry_pzIter_le {X : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ (i N : ℕ), i < N → ContDiffOn ℝ (N : ℕ∞ω) (Function.uncurry X) V →
      ContDiffOn ℝ ((N - i : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.pzIter i X)) V := by
  intro i
  induction i with
  | zero => intro N hN h; simpa using h
  | succ n ih =>
      intro N hN h
      have h1 : ContDiffOn ℝ ((N - n : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.pzIter n X)) V :=
        ih N (by omega) h
      have h2 : ContDiffOn ℝ (((N - n) - 1 : ℕ) : ℕ∞ω)
          (Function.uncurry (Work.Spaces.pz (Work.Spaces.pzIter n X))) V :=
        famAux_contDiffOn_uncurry_pz_le hV (N - n - 1) (by
          rw [show (N - n - 1 + 1 : ℕ) = N - n from by omega]; exact h1)
      have h3 : (N - (n + 1) : ℕ) = (N - n) - 1 := by omega
      rw [h3]
      simpa [Work.Spaces.pzIter_succ] using h2

/-- `ContDiffOn` is stable under the plain `θ`-partial, losing one order. -/
theorem famAux_contDiffOn_uncurry_pth_le {X : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) (n : ℕ)
    (hX : ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) (Function.uncurry X) V) :
    ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.pth X)) V := by
  have hdiff : DifferentiableOn ℝ (Function.uncurry X) V :=
    hX.differentiableOn (by simp)
  have h1 : ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (fderiv ℝ (Function.uncurry X)) V :=
    hX.fderiv_of_isOpen hV (by simp)
  have h2 : ContDiffOn ℝ ((n : ℕ) : ℕ∞ω)
      (fun p : ℝ × ℝ => (fderiv ℝ (Function.uncurry X) p) (0, 1)) V :=
    h1.clm_apply contDiffOn_const
  refine h2.congr (fun p hp => ?_)
  exact deriv_slice_snd _ _ _ ((hdiff.differentiableAt (hV.mem_nhds hp)))

/-- Iterated version: the `i`-th plain `θ`-partial loses `i` orders of smoothness. -/
theorem famAux_contDiffOn_uncurry_pthIter_le {X : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ (i N : ℕ), i < N → ContDiffOn ℝ (N : ℕ∞ω) (Function.uncurry X) V →
      ContDiffOn ℝ ((N - i : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.pthIter i X)) V := by
  intro i
  induction i with
  | zero => intro N hN h; simpa using h
  | succ n ih =>
      intro N hN h
      have h1 : ContDiffOn ℝ ((N - n : ℕ) : ℕ∞ω) (Function.uncurry (Work.Spaces.pthIter n X)) V :=
        ih N (by omega) h
      have h2 : ContDiffOn ℝ (((N - n) - 1 : ℕ) : ℕ∞ω)
          (Function.uncurry (Work.Spaces.pth (Work.Spaces.pthIter n X))) V :=
        famAux_contDiffOn_uncurry_pth_le hV (N - n - 1) (by
          rw [show (N - n - 1 + 1 : ℕ) = N - n from by omega]; exact h1)
      have h3 : (N - (n + 1) : ℕ) = (N - n) - 1 := by omega
      rw [h3]
      simpa [Work.Spaces.pthIter_succ] using h2

/-- The `z`-slice of a `C^n` function is `C^n` on the corresponding `z`-section. -/
theorem contDiffOn_slice_z {X : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (hX : ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (Function.uncurry X) V) {θ : ℝ} :
    ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (fun z => X z θ) {z | (z, θ) ∈ V} := by
  have h1 : ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (fun z : ℝ => (z, θ)) {z | (z, θ) ∈ V} :=
    ContDiffOn.prodMk contDiffOn_id contDiffOn_const
  exact (hX.comp h1 fun z hz => hz)

/-- The `θ`-slice of a `C^n` function is `C^n` on the corresponding `θ`-section. -/
theorem contDiffOn_slice_th {X : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) {n : ℕ}
    (hX : ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (Function.uncurry X) V) {z : ℝ} :
    ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (fun θ => X z θ) {θ | (z, θ) ∈ V} := by
  have h1 : ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (fun θ : ℝ => (z, θ)) {θ | (z, θ) ∈ V} :=
    ContDiffOn.prodMk contDiffOn_const contDiffOn_id
  exact (hX.comp h1 fun θ hθ => hθ)

/-- A `C^n` (`n ≥ 1`) function on an open set is differentiable in `z` at each point. -/
theorem differentiableAt_slice_z_of_contDiffOn {X : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) {n : ℕ} (hn : 1 ≤ n)
    (hX : ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (Function.uncurry X) V) {z θ : ℝ} (hzθ : (z, θ) ∈ V) :
    DifferentiableAt ℝ (fun z' => X z' θ) z := by
  have h1 : DifferentiableAt ℝ (Function.uncurry X) (z, θ) :=
    (hX.contDiffAt (hV.mem_nhds hzθ)).differentiableAt (by simp; omega)
  have h2 : DifferentiableAt ℝ (fun z' : ℝ => (z', θ)) z := by fun_prop
  simpa [Function.comp_def, Function.uncurry] using h1.comp z h2

/-- A `C^n` (`n ≥ 1`) function on an open set is differentiable in `θ` at each point. -/
theorem differentiableAt_slice_th_of_contDiffOn {X : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) {n : ℕ} (hn : 1 ≤ n)
    (hX : ContDiffOn ℝ ((n : ℕ) : ℕ∞ω) (Function.uncurry X) V) {z θ : ℝ} (hzθ : (z, θ) ∈ V) :
    DifferentiableAt ℝ (fun θ' => X z θ') θ := by
  have h1 : DifferentiableAt ℝ (Function.uncurry X) (z, θ) :=
    (hX.contDiffAt (hV.mem_nhds hzθ)).differentiableAt (by simp; omega)
  have h2 : DifferentiableAt ℝ (fun θ' : ℝ => (z, θ')) θ := by fun_prop
  simpa [Function.comp_def, Function.uncurry] using h1.comp θ h2

/-! ## Congruence of the plain iterated derivatives on an open set -/

theorem pzIter_congr_of_isOpen {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pzIter i u))
      (Function.uncurry (Work.Spaces.pzIter i v)) V := by
  induction i with
  | zero => exact h
  | succ n ih => exact fun p hp => Work.Spaces.pz_congr_of_isOpen hV ih hp

theorem pthIter_congr_of_isOpen {u v : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V)
    (h : Set.EqOn (Function.uncurry u) (Function.uncurry v) V) (i : ℕ) :
    Set.EqOn (Function.uncurry (Work.Spaces.pthIter i u))
      (Function.uncurry (Work.Spaces.pthIter i v)) V := by
  induction i with
  | zero => exact h
  | succ n ih => exact fun p hp => Work.Spaces.pth_congr_of_isOpen hV ih hp

/-! ## Linear algebra of the iterated derivatives -/

theorem iterate_deriv_const_mul (i : ℕ) (c : ℝ) (f : ℝ → ℝ) (x : ℝ) :
    deriv^[i] (fun x => c * f x) x = c * deriv^[i] f x := by
  induction i generalizing x with
  | zero => rfl
  | succ n ih =>
      have hfun : deriv^[n] (fun x => c * f x) = fun x => c * deriv^[n] f x := funext ih
      rw [Function.iterate_succ_apply', hfun, Function.iterate_succ_apply', deriv_const_mul_field]

theorem iterate_deriv_mul_const (i : ℕ) (f : ℝ → ℝ) (c : ℝ) (x : ℝ) :
    deriv^[i] (fun x => f x * c) x = deriv^[i] f x * c := by
  induction i generalizing x with
  | zero => rfl
  | succ n ih =>
      have hfun : deriv^[n] (fun x => f x * c) = fun x => deriv^[n] f x * c := funext ih
      rw [Function.iterate_succ_apply', hfun, Function.iterate_succ_apply', deriv_mul_const_field]

theorem iterate_deriv_pow_eq (i n : ℕ) (x : ℝ) :
    deriv^[i] (fun x : ℝ => x ^ n) x = (∏ l ∈ Finset.range i, ((n : ℝ) - l)) * x ^ (n - i) :=
  iter_deriv_pow n x i

/-- The iterated `z`-derivative of a product of a `z`-only and a `θ`-only function. -/
theorem pzIter_mul_zonly_thetaonly (i : ℕ) (f : ℝ → ℝ) (h : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter i (fun z' θ' => f z' * h θ') z θ = deriv^[i] f z * h θ := by
  rw [pzIter_apply_eq_iterate_deriv]
  have : (fun z' : ℝ => f z' * h θ) = (fun z' : ℝ => (fun z'' => f z'') z' * h θ) := rfl
  rw [this, iterate_deriv_mul_const]

/-- The iterated `θ`-derivative of a product of a `z`-only and a `θ`-only function. -/
theorem pthIter_mul_zonly_thetaonly (j : ℕ) (f : ℝ → ℝ) (h : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter j (fun z' θ' => f z' * h θ') z θ = f z * deriv^[j] h θ := by
  rw [pthIter_apply_eq_iterate_deriv]
  have : (fun θ' : ℝ => f z * h θ') = (fun θ' : ℝ => f z * (fun θ'' => h θ'') θ') := rfl
  rw [this, iterate_deriv_const_mul]

/-- **The monomial formula** for the mixed iterated derivatives. -/
theorem pzIter_pthIter_monom (i j a b : ℕ) (A z θ : ℝ) :
    Work.Spaces.pzIter i (Work.Spaces.pthIter j (fun z θ => A * (z ^ a * θ ^ b))) z θ
      = A * ((∏ l ∈ Finset.range i, ((a : ℝ) - l)) * z ^ (a - i))
          * ((∏ l ∈ Finset.range j, ((b : ℝ) - l)) * θ ^ (b - j)) := by
  have hpth : Work.Spaces.pthIter j (fun z θ => A * (z ^ a * θ ^ b))
      = fun z θ => (A * z ^ a) * ((∏ l ∈ Finset.range j, ((b : ℝ) - l)) * θ ^ (b - j)) := by
    funext z θ
    have h1 : (fun z θ => A * (z ^ a * θ ^ b)) = fun z θ => (A * z ^ a) * θ ^ b := by
      funext z θ; ring
    rw [h1, pthIter_mul_zonly_thetaonly j (fun z => A * z ^ a) (fun θ => θ ^ b) z θ,
      iterate_deriv_pow_eq]
  rw [hpth, pzIter_mul_zonly_thetaonly i (fun z => A * z ^ a)
    (fun θ => (∏ l ∈ Finset.range j, ((b : ℝ) - l)) * θ ^ (b - j)) z θ,
    iterate_deriv_const_mul, iterate_deriv_pow_eq]

/-! ## Linearity of the iterated derivatives over differences and finite sums -/

theorem pzIter_sub_eqOn {X Y : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ i : ℕ, ContDiffOn ℝ ((i + 1 : ℕ) : ℕ∞ω) (Function.uncurry X) V →
      ContDiffOn ℝ ((i + 1 : ℕ) : ℕ∞ω) (Function.uncurry Y) V →
      Set.EqOn (Function.uncurry (Work.Spaces.pzIter i (fun z θ => X z θ - Y z θ)))
        (Function.uncurry (fun z θ => Work.Spaces.pzIter i X z θ
          - Work.Spaces.pzIter i Y z θ)) V := by
  intro i
  induction i with
  | zero => intro _ _ p hp; rfl
  | succ n ih =>
      intro hX hY p hp
      have hX' : ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) (Function.uncurry X) V :=
        hX.of_le (by exact_mod_cast (by omega : n + 1 ≤ n + 2))
      have hY' : ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) (Function.uncurry Y) V :=
        hY.of_le (by exact_mod_cast (by omega : n + 1 ≤ n + 2))
      have hsec : ∀ᶠ z' : ℝ in 𝓝 p.1, (z', p.2) ∈ V :=
        (Continuous.prodMk_left p.2).continuousAt.eventually (hV.mem_nhds hp)
      have hev : (fun z' : ℝ => Work.Spaces.pzIter n (fun z θ => X z θ - Y z θ) z' p.2)
          =ᶠ[𝓝 p.1] (fun z' : ℝ => Work.Spaces.pzIter n X z' p.2
            - Work.Spaces.pzIter n Y z' p.2) := by
        filter_upwards [hsec] with z' hz'
        exact ih hX' hY' hz'
      have hcX : ContDiffOn ℝ (1 : ℕ∞ω) (Function.uncurry (Work.Spaces.pzIter n X)) V := by
        have h := famAux_contDiffOn_uncurry_pzIter_le hV n (n + 1) (by omega) hX'
        rwa [show n + 1 - n = 1 from by omega] at h
      have hdX : DifferentiableAt ℝ (fun z' : ℝ => Work.Spaces.pzIter n X z' p.2) p.1 :=
        differentiableAt_slice_z_of_contDiffOn hV (n := 1) le_rfl hcX hp
      have hcY : ContDiffOn ℝ (1 : ℕ∞ω) (Function.uncurry (Work.Spaces.pzIter n Y)) V := by
        have h := famAux_contDiffOn_uncurry_pzIter_le hV n (n + 1) (by omega) hY'
        rwa [show n + 1 - n = 1 from by omega] at h
      have hdY : DifferentiableAt ℝ (fun z' : ℝ => Work.Spaces.pzIter n Y z' p.2) p.1 :=
        differentiableAt_slice_z_of_contDiffOn hV (n := 1) le_rfl hcY hp
      show deriv (fun z' : ℝ => Work.Spaces.pzIter n (fun z θ => X z θ - Y z θ) z' p.2) p.1
        = deriv (fun z' : ℝ => Work.Spaces.pzIter n X z' p.2) p.1
          - deriv (fun z' : ℝ => Work.Spaces.pzIter n Y z' p.2) p.1
      rw [hev.deriv_eq,
        show (fun z' : ℝ => Work.Spaces.pzIter n X z' p.2 - Work.Spaces.pzIter n Y z' p.2)
          = (fun z' : ℝ => Work.Spaces.pzIter n X z' p.2)
            - (fun z' : ℝ => Work.Spaces.pzIter n Y z' p.2) from rfl,
        deriv_sub hdX hdY]

theorem pthIter_sub_eqOn {X Y : ℝ → ℝ → ℝ} {V : Set (ℝ × ℝ)} (hV : IsOpen V) :
    ∀ i : ℕ, ContDiffOn ℝ ((i + 1 : ℕ) : ℕ∞ω) (Function.uncurry X) V →
      ContDiffOn ℝ ((i + 1 : ℕ) : ℕ∞ω) (Function.uncurry Y) V →
      Set.EqOn (Function.uncurry (Work.Spaces.pthIter i (fun z θ => X z θ - Y z θ)))
        (Function.uncurry (fun z θ => Work.Spaces.pthIter i X z θ
          - Work.Spaces.pthIter i Y z θ)) V := by
  intro i
  induction i with
  | zero => intro _ _ p hp; rfl
  | succ n ih =>
      intro hX hY p hp
      have hX' : ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) (Function.uncurry X) V :=
        hX.of_le (by exact_mod_cast (by omega : n + 1 ≤ n + 2))
      have hY' : ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) (Function.uncurry Y) V :=
        hY.of_le (by exact_mod_cast (by omega : n + 1 ≤ n + 2))
      have hsec : ∀ᶠ θ' : ℝ in 𝓝 p.2, (p.1, θ') ∈ V :=
        (Continuous.prodMk_right p.1).continuousAt.eventually (hV.mem_nhds hp)
      have hev : (fun θ' : ℝ => Work.Spaces.pthIter n (fun z θ => X z θ - Y z θ) p.1 θ')
          =ᶠ[𝓝 p.2] (fun θ' : ℝ => Work.Spaces.pthIter n X p.1 θ'
            - Work.Spaces.pthIter n Y p.1 θ') := by
        filter_upwards [hsec] with θ' hθ'
        exact ih hX' hY' hθ'
      have hcX : ContDiffOn ℝ (1 : ℕ∞ω) (Function.uncurry (Work.Spaces.pthIter n X)) V := by
        have h := famAux_contDiffOn_uncurry_pthIter_le hV n (n + 1) (by omega) hX'
        rwa [show n + 1 - n = 1 from by omega] at h
      have hdX : DifferentiableAt ℝ (fun θ' : ℝ => Work.Spaces.pthIter n X p.1 θ') p.2 :=
        differentiableAt_slice_th_of_contDiffOn hV (n := 1) le_rfl hcX hp
      have hcY : ContDiffOn ℝ (1 : ℕ∞ω) (Function.uncurry (Work.Spaces.pthIter n Y)) V := by
        have h := famAux_contDiffOn_uncurry_pthIter_le hV n (n + 1) (by omega) hY'
        rwa [show n + 1 - n = 1 from by omega] at h
      have hdY : DifferentiableAt ℝ (fun θ' : ℝ => Work.Spaces.pthIter n Y p.1 θ') p.2 :=
        differentiableAt_slice_th_of_contDiffOn hV (n := 1) le_rfl hcY hp
      show deriv (fun θ' : ℝ => Work.Spaces.pthIter n (fun z θ => X z θ - Y z θ) p.1 θ') p.2
        = deriv (fun θ' : ℝ => Work.Spaces.pthIter n X p.1 θ') p.2
          - deriv (fun θ' : ℝ => Work.Spaces.pthIter n Y p.1 θ') p.2
      rw [hev.deriv_eq,
        show (fun θ' : ℝ => Work.Spaces.pthIter n X p.1 θ' - Work.Spaces.pthIter n Y p.1 θ')
          = (fun θ' : ℝ => Work.Spaces.pthIter n X p.1 θ')
            - (fun θ' : ℝ => Work.Spaces.pthIter n Y p.1 θ') from rfl,
        deriv_sub hdX hdY]

theorem pzIter_sum_eqOn {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ → ℝ) {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) :
    ∀ i : ℕ, (∀ k ∈ s, ContDiffOn ℝ ((i + 1 : ℕ) : ℕ∞ω) (Function.uncurry (F k)) V) →
      Set.EqOn (Function.uncurry (Work.Spaces.pzIter i (fun z θ => ∑ k ∈ s, F k z θ)))
        (Function.uncurry (fun z θ => ∑ k ∈ s, Work.Spaces.pzIter i (F k) z θ)) V := by
  intro i
  induction i with
  | zero => intro _ p hp; rfl
  | succ n ih =>
      intro hF p hp
      have hF' : ∀ k ∈ s, ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) (Function.uncurry (F k)) V :=
        fun k hk => (hF k hk).of_le (by exact_mod_cast (by omega : n + 1 ≤ n + 2))
      have hsec : ∀ᶠ z' : ℝ in 𝓝 p.1, (z', p.2) ∈ V :=
        (Continuous.prodMk_left p.2).continuousAt.eventually (hV.mem_nhds hp)
      have hev : (fun z' : ℝ => Work.Spaces.pzIter n (fun z θ => ∑ k ∈ s, F k z θ) z' p.2)
          =ᶠ[𝓝 p.1] (fun z' : ℝ => ∑ k ∈ s, Work.Spaces.pzIter n (F k) z' p.2) := by
        filter_upwards [hsec] with z' hz'
        exact ih hF' hz'
      have hd : ∀ k ∈ s, DifferentiableAt ℝ
          (fun z' : ℝ => Work.Spaces.pzIter n (F k) z' p.2) p.1 := fun k hk => by
        have hc : ContDiffOn ℝ (1 : ℕ∞ω) (Function.uncurry (Work.Spaces.pzIter n (F k))) V := by
          have h := famAux_contDiffOn_uncurry_pzIter_le hV n (n + 1) (by omega) (hF' k hk)
          rwa [show n + 1 - n = 1 from by omega] at h
        exact differentiableAt_slice_z_of_contDiffOn hV (n := 1) le_rfl hc hp
      show deriv (fun z' : ℝ => Work.Spaces.pzIter n (fun z θ => ∑ k ∈ s, F k z θ) z' p.2) p.1
        = ∑ k ∈ s, deriv (fun z' : ℝ => Work.Spaces.pzIter n (F k) z' p.2) p.1
      rw [hev.deriv_eq]
      have hfun : (fun z' : ℝ => ∑ k ∈ s, Work.Spaces.pzIter n (F k) z' p.2)
          = ∑ k ∈ s, (fun z' : ℝ => Work.Spaces.pzIter n (F k) z' p.2) := by
        funext z'; rw [Finset.sum_apply]
      rw [hfun, deriv_sum (fun k hk => hd k hk)]

theorem pthIter_sum_eqOn {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ → ℝ) {V : Set (ℝ × ℝ)}
    (hV : IsOpen V) :
    ∀ i : ℕ, (∀ k ∈ s, ContDiffOn ℝ ((i + 1 : ℕ) : ℕ∞ω) (Function.uncurry (F k)) V) →
      Set.EqOn (Function.uncurry (Work.Spaces.pthIter i (fun z θ => ∑ k ∈ s, F k z θ)))
        (Function.uncurry (fun z θ => ∑ k ∈ s, Work.Spaces.pthIter i (F k) z θ)) V := by
  intro i
  induction i with
  | zero => intro _ p hp; rfl
  | succ n ih =>
      intro hF p hp
      have hF' : ∀ k ∈ s, ContDiffOn ℝ ((n + 1 : ℕ) : ℕ∞ω) (Function.uncurry (F k)) V :=
        fun k hk => (hF k hk).of_le (by exact_mod_cast (by omega : n + 1 ≤ n + 2))
      have hsec : ∀ᶠ θ' : ℝ in 𝓝 p.2, (p.1, θ') ∈ V :=
        (Continuous.prodMk_right p.1).continuousAt.eventually (hV.mem_nhds hp)
      have hev : (fun θ' : ℝ => Work.Spaces.pthIter n (fun z θ => ∑ k ∈ s, F k z θ) p.1 θ')
          =ᶠ[𝓝 p.2] (fun θ' : ℝ => ∑ k ∈ s, Work.Spaces.pthIter n (F k) p.1 θ') := by
        filter_upwards [hsec] with θ' hθ'
        exact ih hF' hθ'
      have hd : ∀ k ∈ s, DifferentiableAt ℝ
          (fun θ' : ℝ => Work.Spaces.pthIter n (F k) p.1 θ') p.2 := fun k hk => by
        have hc : ContDiffOn ℝ (1 : ℕ∞ω) (Function.uncurry (Work.Spaces.pthIter n (F k))) V := by
          have h := famAux_contDiffOn_uncurry_pthIter_le hV n (n + 1) (by omega) (hF' k hk)
          rwa [show n + 1 - n = 1 from by omega] at h
        exact differentiableAt_slice_th_of_contDiffOn hV (n := 1) le_rfl hc hp
      show deriv (fun θ' : ℝ => Work.Spaces.pthIter n (fun z θ => ∑ k ∈ s, F k z θ) p.1 θ') p.2
        = ∑ k ∈ s, deriv (fun θ' : ℝ => Work.Spaces.pthIter n (F k) p.1 θ') p.2
      rw [hev.deriv_eq]
      have hfun : (fun θ' : ℝ => ∑ k ∈ s, Work.Spaces.pthIter n (F k) p.1 θ')
          = ∑ k ∈ s, (fun θ' : ℝ => Work.Spaces.pthIter n (F k) p.1 θ') := by
        funext θ'; rw [Finset.sum_apply]
      rw [hfun, deriv_sum (fun k hk => hd k hk)]

/-! ## The normalising constant of the `8`-fold antiderivative, and the monomial facts -/

/-- The product of the eight falling-factorial denominators attached to the exponents `(a,b)`. -/
def Kf (a b : ℕ) : ℝ :=
  (((a : ℝ) + 1) * ((a : ℝ) + 2) * ((a : ℝ) + 3) * ((a : ℝ) + 4))
    * (((b : ℝ) + 1) * ((b : ℝ) + 2) * ((b : ℝ) + 3) * ((b : ℝ) + 4))

theorem Kf_pos (a b : ℕ) : 0 < Kf a b := by
  unfold Kf; positivity

theorem Kf_ne (a b : ℕ) : Kf a b ≠ 0 := (Kf_pos a b).ne'

theorem prod_range_four_sub (a : ℕ) :
    (∏ l ∈ Finset.range 4, (((a + 4 : ℕ) : ℝ) - (l : ℝ)))
      = (((a : ℝ) + 1) * ((a : ℝ) + 2) * ((a : ℝ) + 3) * ((a : ℝ) + 4)) := by
  rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ, Finset.prod_range_succ]
  push_cast
  ring

theorem prod_range_mul_zero (j b : ℕ) (hj : j < b) :
    (∏ l ∈ Finset.range j, ((b : ℝ) - l)) * (0 : ℝ) ^ (b - j) = 0 := by
  rw [zero_pow (by omega), mul_zero]

/-! ## The `8`-fold antiderivative of a monomial sum -/

theorem pzIter_pthIter_antideriv_monom (i j a b : ℕ) (c : ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter i (Work.Spaces.pthIter j (fun z θ =>
        (c / Kf a b) * z ^ (a + 4) * θ ^ (b + 4))) z θ
      = c * ((∏ l ∈ Finset.range i, (((a : ℝ) + 4) - l)) * z ^ (a + 4 - i))
          * ((∏ l ∈ Finset.range j, (((b : ℝ) + 4) - l)) * θ ^ (b + 4 - j)) / Kf a b := by
  have h1 : (fun z θ => (c / Kf a b) * z ^ (a + 4) * θ ^ (b + 4))
      = fun z θ => (c / Kf a b) * (z ^ (a + 4) * θ ^ (b + 4)) := by
    funext z θ; ring
  rw [h1, pzIter_pthIter_monom i j (a + 4) (b + 4) (c / Kf a b) z θ]
  push_cast
  ring

end Work.FTS.GalBasis
