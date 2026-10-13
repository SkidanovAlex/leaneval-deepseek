import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.ContinuousMap.Weierstrass
import Submission.Work.FTS.GalBasis.Defs
import Submission.Work.FTS.GalBasis.exists_poly_approx_c4
import Submission.Work.FTS.GalBasis.exists_poly2_uniform
import Submission.Work.FTS.GalBasis.exists_fin_monomial_sum
import Submission.Work.Spaces.pz_aux
import Submission.Work.Spaces.mixed_comm
import Submission.Work.FTS.GalBasis.PolyApprox.exists_contDiffOn_Ioo_of_contDiffAt_Icc
import Submission.Work.FTS.GalBasis.GalApprox.ladder_bound
import Submission.Work.FTS.GalBasis.GalApprox.contDiffAt_pzIter_pthIter
import Submission.Work.FTS.GalBasis.GalApprox.pzIter_pthIter_comm
import Submission.Work.FTS.GalBasis.GalApprox.exists_monomial_form_of_shift_sum

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ContDiff BigOperators
open Set Filter

namespace Work.FTS.GalBasis.GalApprox

set_option autoImplicit false
set_option maxHeartbeats 1600000


/-! ## Bridge lemmas between `pzIter`/`pthIter` and `iteratedDeriv` -/

/-- `pthIter i f z θ` is the `i`-th iterated derivative of the `θ`-slice. -/
theorem pthIter_eq_iteratedDeriv (j : ℕ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter j f z θ = iteratedDeriv j (fun θ' => f z θ') θ := by
  rw [iteratedDeriv_eq_iterate]
  induction j generalizing θ with
  | zero => rfl
  | succ n ih =>
      simp only [Work.Spaces.pthIter_succ, Work.Spaces.pth]
      have h : (fun θ' => Work.Spaces.pthIter n f z θ') = deriv^[n] (fun θ' => f z θ') := by
        funext θ'; exact ih θ'
      rw [h, Function.iterate_succ_apply']

/-! ## Iterated derivatives of `x ↦ x ^ n` and the falling factorial -/

theorem iteratedDeriv_pow_eq (i n : ℕ) (x : ℝ) :
    iteratedDeriv i (fun y : ℝ => y ^ n) x = ((n.descFactorial i : ℕ) : ℝ) * x ^ (n - i) :=
  iteratedDeriv_pow n i

/-- Iterated derivatives of a shifted power. -/
theorem iteratedDeriv_shifted_pow (i P : ℕ) (A z : ℝ) :
    iteratedDeriv i (fun z : ℝ => (z - A) ^ P) z
      = ((P.descFactorial i : ℕ) : ℝ) * (z - A) ^ (P - i) := by
  have h := congr_fun (iteratedDeriv_comp_sub_const (𝕜 := ℝ) i (fun y : ℝ => y ^ P) A) z
  rw [h, iteratedDeriv_pow_eq]

/-! ## Separable functions: iterated derivatives of `z ↦ f z * h θ` -/

theorem iterate_deriv_mul_const' (i : ℕ) (g : ℝ → ℝ) (c : ℝ) (x : ℝ) :
    deriv^[i] (fun y => g y * c) x = deriv^[i] g x * c := by
  induction i generalizing x with
  | zero => rfl
  | succ n ih =>
      have hfun : deriv^[n] (fun y => g y * c) = fun y => deriv^[n] g y * c := funext ih
      rw [Function.iterate_succ_apply', hfun, Function.iterate_succ_apply', deriv_mul_const_field]

theorem iterate_deriv_const_mul' (i : ℕ) (c : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    deriv^[i] (fun y => c * g y) x = c * deriv^[i] g x := by
  induction i generalizing x with
  | zero => rfl
  | succ n ih =>
      have hfun : deriv^[n] (fun y => c * g y) = fun y => c * deriv^[n] g y := funext ih
      rw [Function.iterate_succ_apply', hfun, Function.iterate_succ_apply', deriv_const_mul_field]

/-- Iterated `θ`-derivative of a separable function. -/
theorem pthIter_separable (j : ℕ) (f h : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter j (fun z θ => f z * h θ) z θ = f z * deriv^[j] h θ := by
  rw [pthIter_eq_iteratedDeriv, iteratedDeriv_eq_iterate]
  induction j generalizing θ with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have : deriv^[n] (fun θ' => f z * h θ') = fun θ' => f z * deriv^[n] h θ' := funext ih
      rw [this, Function.iterate_succ_apply', deriv_const_mul_field]

/-- Iterated `z`-derivative of a separable function. -/
theorem pzIter_separable (i : ℕ) (f h : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter i (fun z θ => f z * h θ) z θ = deriv^[i] f z * h θ := by
  rw [Work.Spaces.pzIter_eq_iteratedDeriv, iteratedDeriv_eq_iterate]
  induction i generalizing z with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      have : deriv^[n] (fun z' => f z' * h θ) = fun z' => deriv^[n] f z' * h θ := funext ih
      rw [this, Function.iterate_succ_apply', deriv_mul_const_field]

/-- Iterated mixed derivative of a separable function. -/
theorem pzIter_pthIter_separable (i j : ℕ) (f h : ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pzIter i (Work.Spaces.pthIter j (fun z θ => f z * h θ)) z θ
      = deriv^[i] f z * deriv^[j] h θ := by
  have hp : Work.Spaces.pthIter j (fun z θ => f z * h θ)
      = fun z θ => f z * deriv^[j] h θ := by
    funext z θ; exact pthIter_separable j f h z θ
  rw [hp, pzIter_separable]


/-! ## The shifted monomial: mixed iterated derivatives -/

theorem pzIter_pthIter_shifted_monom (i j P Q : ℕ) (A C cc z θ : ℝ) :
    Work.Spaces.pzIter i (Work.Spaces.pthIter j
        (fun z θ => cc * (z - A) ^ P * (θ - C) ^ Q)) z θ
      = cc * (((P.descFactorial i : ℕ) : ℝ) * (z - A) ^ (P - i))
          * (((Q.descFactorial j : ℕ) : ℝ) * (θ - C) ^ (Q - j)) := by
  have hfun : (fun z θ => cc * (z - A) ^ P * (θ - C) ^ Q)
      = (fun z θ => (cc * (z - A) ^ P) * (θ - C) ^ Q) := rfl
  rw [hfun, pzIter_pthIter_separable]
  rw [← iteratedDeriv_eq_iterate, ← iteratedDeriv_eq_iterate]
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_shifted_pow, iteratedDeriv_shifted_pow]

/-! ## Linearities on slices -/

theorem slice_th_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ → ℝ) (z : ℝ) :
    (fun θ => ∑ k ∈ s, F k z θ) = ∑ k ∈ s, (fun θ => F k z θ) := by
  funext θ; rw [Finset.sum_apply]

theorem slice_z_sum {ι : Type*} (s : Finset ι) (F : ι → ℝ → ℝ → ℝ) (θ : ℝ) :
    (fun z => ∑ k ∈ s, F k z θ) = ∑ k ∈ s, (fun z => F k z θ) := by
  funext z; rw [Finset.sum_apply]

/-- A monomial (as a function of one variable) is `C^n` everywhere. -/
theorem contDiffAt_monom_θ (j : ℕ) (a : ℝ) (Q : ℕ) (C v : ℝ) :
    ContDiffAt ℝ j (fun θ : ℝ => a * (θ - C) ^ Q) v := by
  fun_prop

theorem contDiffAt_monom_z (i : ℕ) (a : ℝ) (P : ℕ) (A v : ℝ) :
    ContDiffAt ℝ i (fun z : ℝ => a * (z - A) ^ P) v := by
  fun_prop

/-! ## A finite sum of shifted monomials -/

theorem pzIter_pthIter_smon_sum (i j : ℕ) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (P Q : ι → ℕ)
    (A C z θ : ℝ) :
    Work.Spaces.pzIter i (Work.Spaces.pthIter j
        (fun z θ => ∑ k ∈ s, c k * (z - A) ^ (P k) * (θ - C) ^ (Q k))) z θ
      = ∑ k ∈ s, (c k * (((P k).descFactorial i : ℕ) : ℝ) * (((Q k).descFactorial j : ℕ) : ℝ))
          * (z - A) ^ (P k - i) * (θ - C) ^ (Q k - j) := by
  have hθ : (fun z' => Work.Spaces.pthIter j
        (fun z θ => ∑ k ∈ s, c k * (z - A) ^ (P k) * (θ - C) ^ (Q k)) z' θ)
      = fun z' => ∑ k ∈ s, c k * (z' - A) ^ (P k) * (((Q k).descFactorial j : ℕ) : ℝ)
          * (θ - C) ^ (Q k - j) := by
    funext z'
    rw [pthIter_eq_iteratedDeriv]
    have hslice : (fun θ' => ∑ k ∈ s, c k * (z' - A) ^ (P k) * (θ' - C) ^ (Q k))
        = ∑ k ∈ s, (fun θ' => c k * (z' - A) ^ (P k) * (θ' - C) ^ (Q k)) := by
      funext θ'; rw [Finset.sum_apply]
    rw [hslice, iteratedDeriv_sum (fun k hk => contDiffAt_monom_θ j (c k * (z' - A) ^ (P k))
        (Q k) C θ)]
    exact Finset.sum_congr rfl fun k hk => by
      rw [iteratedDeriv_const_mul_field, iteratedDeriv_shifted_pow]
      ring
  rw [Work.Spaces.pzIter_eq_iteratedDeriv, hθ]
  have hz : (fun z' => ∑ k ∈ s, c k * (z' - A) ^ (P k) * (((Q k).descFactorial j : ℕ) : ℝ)
        * (θ - C) ^ (Q k - j))
      = ∑ k ∈ s, (fun z' => (c k * (((Q k).descFactorial j : ℕ) : ℝ) * (θ - C) ^ (Q k - j))
          * (z' - A) ^ (P k)) := by
    funext z'
    rw [Finset.sum_apply]
    exact Finset.sum_congr rfl fun k hk => by ring
  rw [hz, iteratedDeriv_sum (fun k hk => contDiffAt_monom_z i
      (c k * (((Q k).descFactorial j : ℕ) : ℝ) * (θ - C) ^ (Q k - j)) (P k) A z)]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [iteratedDeriv_const_mul_field, iteratedDeriv_shifted_pow]
  ring


/-! ## Linearity of the iterated partials over addition and subtraction -/

theorem pzIter_add {i : ℕ} {X Y : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hX : ContDiffAt ℝ i (fun z' => X z' θ) z)
    (hY : ContDiffAt ℝ i (fun z' => Y z' θ) z) :
    Work.Spaces.pzIter i (fun z θ => X z θ + Y z θ) z θ
      = Work.Spaces.pzIter i X z θ + Work.Spaces.pzIter i Y z θ := by
  rw [Work.Spaces.pzIter_eq_iteratedDeriv, Work.Spaces.pzIter_eq_iteratedDeriv,
    Work.Spaces.pzIter_eq_iteratedDeriv]
  have h : (fun z' => X z' θ + Y z' θ) = (fun z' => X z' θ) + (fun z' => Y z' θ) := rfl
  rw [h, iteratedDeriv_add hX hY]

theorem pzIter_sub {i : ℕ} {X Y : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hX : ContDiffAt ℝ i (fun z' => X z' θ) z)
    (hY : ContDiffAt ℝ i (fun z' => Y z' θ) z) :
    Work.Spaces.pzIter i (fun z θ => X z θ - Y z θ) z θ
      = Work.Spaces.pzIter i X z θ - Work.Spaces.pzIter i Y z θ := by
  rw [Work.Spaces.pzIter_eq_iteratedDeriv, Work.Spaces.pzIter_eq_iteratedDeriv,
    Work.Spaces.pzIter_eq_iteratedDeriv]
  have h : (fun z' => X z' θ - Y z' θ) = (fun z' => X z' θ) - (fun z' => Y z' θ) := rfl
  rw [h, iteratedDeriv_sub hX hY]

theorem pthIter_add {i : ℕ} {X Y : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hX : ContDiffAt ℝ i (fun θ' => X z θ') θ)
    (hY : ContDiffAt ℝ i (fun θ' => Y z θ') θ) :
    Work.Spaces.pthIter i (fun z θ => X z θ + Y z θ) z θ
      = Work.Spaces.pthIter i X z θ + Work.Spaces.pthIter i Y z θ := by
  rw [pthIter_eq_iteratedDeriv, pthIter_eq_iteratedDeriv, pthIter_eq_iteratedDeriv]
  have h : (fun θ' => X z θ' + Y z θ') = (fun θ' => X z θ') + (fun θ' => Y z θ') := rfl
  rw [h, iteratedDeriv_add hX hY]

theorem pthIter_sub {i : ℕ} {X Y : ℝ → ℝ → ℝ} {z θ : ℝ}
    (hX : ContDiffAt ℝ i (fun θ' => X z θ') θ)
    (hY : ContDiffAt ℝ i (fun θ' => Y z θ') θ) :
    Work.Spaces.pthIter i (fun z θ => X z θ - Y z θ) z θ
      = Work.Spaces.pthIter i X z θ - Work.Spaces.pthIter i Y z θ := by
  rw [pthIter_eq_iteratedDeriv, pthIter_eq_iteratedDeriv, pthIter_eq_iteratedDeriv]
  have h : (fun θ' => X z θ' - Y z θ') = (fun θ' => X z θ') - (fun θ' => Y z θ') := rfl
  rw [h, iteratedDeriv_sub hX hY]

/-! ## Smoothness of a finite sum of shifted monomials -/

theorem contDiffAt_smonSum (n : ℕ) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (P Q : ι → ℕ)
    (A C z θ : ℝ) :
    ContDiffAt ℝ n (Function.uncurry (fun z θ => ∑ k ∈ s, c k * (z - A) ^ (P k) * (θ - C) ^ (Q k)))
      (z, θ) := by
  have h : (fun p : ℝ × ℝ => ∑ k ∈ s, c k * (p.1 - A) ^ (P k) * (p.2 - C) ^ (Q k))
      = Function.uncurry (fun z θ => ∑ k ∈ s, c k * (z - A) ^ (P k) * (θ - C) ^ (Q k)) := rfl
  rw [← h]
  exact ContDiffAt.sum (fun k hk => by fun_prop)

/-- Smoothness of a `θ`-slice of a finite sum of shifted monomials. -/
theorem contDiffAt_smonSum_θ (n : ℕ) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (P Q : ι → ℕ)
    (A C z θ : ℝ) :
    ContDiffAt ℝ n (fun θ' => ∑ k ∈ s, c k * (z - A) ^ (P k) * (θ' - C) ^ (Q k)) θ :=
  ContDiffAt.sum (f := fun k θ' => c k * (z - A) ^ (P k) * (θ' - C) ^ (Q k))
    (fun k _ => by fun_prop)

/-- Smoothness of a `z`-slice of a finite sum of shifted monomials. -/
theorem contDiffAt_smonSum_z (n : ℕ) {ι : Type*} (s : Finset ι) (c : ι → ℝ) (P Q : ι → ℕ)
    (A C z θ : ℝ) :
    ContDiffAt ℝ n (fun z' => ∑ k ∈ s, c k * (z' - A) ^ (P k) * (θ - C) ^ (Q k)) z :=
  ContDiffAt.sum (f := fun k z' => c k * (z' - A) ^ (P k) * (θ - C) ^ (Q k))
    (fun k _ => by fun_prop)


/-! ## Uniform approximation by shifted monomial sums -/

theorem exists_poly1_uniform_shift {h : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hh : ContinuousOn h (Set.Icc a b)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Finset ℕ) (c : ℕ → ℝ), ∀ x ∈ Set.Icc a b,
      |(∑ k ∈ s, c k * (x - a) ^ k) - h x| < ε := by
  have hmaps : Set.MapsTo (fun y : ℝ => y + a) (Set.Icc 0 (b - a)) (Set.Icc a b) := by
    intro y hy; exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hcont : ContinuousOn (fun y : ℝ => h (y + a)) (Set.Icc 0 (b - a)) :=
    hh.comp (continuous_id.add continuous_const).continuousOn hmaps
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn 0 (b - a) (fun y => h (y + a))
    hcont ε hε
  refine ⟨Finset.range (p.natDegree + 1), fun k => p.coeff k, ?_⟩
  intro x hx
  have hy : x - a ∈ Set.Icc 0 (b - a) := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have h1 := hp (x - a) hy
  have h2 : p.eval (x - a) = ∑ k ∈ Finset.range (p.natDegree + 1), p.coeff k * (x - a) ^ k :=
    Polynomial.eval_eq_sum_range (x - a)
  have h3 : x - a + a = x := by ring
  rw [h2, h3] at h1
  exact h1

theorem exists_poly2_uniform_shift {h : ℝ → ℝ → ℝ} {A B C D : ℝ} (hAB : A ≤ B) (hCD : C ≤ D)
    (hh : ContinuousOn (Function.uncurry h) (Set.Icc A B ×ˢ Set.Icc C D)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (m : ℕ) (p q : Fin m → ℕ) (c : Fin m → ℝ),
      ∀ z ∈ Set.Icc A B, ∀ θ ∈ Set.Icc C D,
        |(∑ k, c k * (z - A) ^ (p k) * (θ - C) ^ (q k)) - h z θ| < ε := by
  have hmaps : Set.MapsTo (fun u : ℝ × ℝ => (u.1 + A, u.2 + C))
      (Set.Icc 0 (B - A) ×ˢ Set.Icc 0 (D - C)) (Set.Icc A B ×ˢ Set.Icc C D) := by
    rintro ⟨u, v⟩ ⟨hu, hv⟩
    exact ⟨⟨by linarith [hu.1], by linarith [hu.2]⟩, ⟨by linarith [hv.1], by linarith [hv.2]⟩⟩
  have hg : ContinuousOn (fun u : ℝ × ℝ => (u.1 + A, u.2 + C))
      (Set.Icc 0 (B - A) ×ˢ Set.Icc 0 (D - C)) := by fun_prop
  have hcont : ContinuousOn (Function.uncurry (fun u v : ℝ => h (u + A) (v + C)))
      (Set.Icc 0 (B - A) ×ˢ Set.Icc 0 (D - C)) := by
    have hcomp := hh.comp hg hmaps
    exact hcomp
  obtain ⟨m, p, q, c, hc⟩ := Work.FTS.GalBasis.exists_poly2_uniform (A := 0) (B := B - A)
    (C := 0) (D := D - C) (h := fun u v : ℝ => h (u + A) (v + C)) (by linarith) (by linarith)
    hcont hε
  refine ⟨m, p, q, c, ?_⟩
  intro z hz θ hθ
  have h1 := hc (z - A) ⟨by linarith [hz.1], by linarith [hz.2]⟩ (θ - C)
    ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  simp only [show z - A + A = z from by ring, show θ - C + C = θ from by ring] at h1
  exact h1


/-! ## Linearity of the iterated partials over `Finset` sums -/

theorem pzIter_finset_sum {ι : Type*} (s : Finset ι) (G : ι → ℝ → ℝ → ℝ) (i : ℕ) {z θ : ℝ}
    (h : ∀ k ∈ s, ContDiffAt ℝ i (fun z' => G k z' θ) z) :
    Work.Spaces.pzIter i (fun z θ => ∑ k ∈ s, G k z θ) z θ
      = ∑ k ∈ s, Work.Spaces.pzIter i (G k) z θ := by
  rw [Work.Spaces.pzIter_eq_iteratedDeriv]
  have hslice : (fun z' => ∑ k ∈ s, G k z' θ) = ∑ k ∈ s, (fun z' => G k z' θ) := by
    funext z'; rw [Finset.sum_apply]
  rw [hslice, iteratedDeriv_sum (fun k hk => h k hk)]
  exact Finset.sum_congr rfl (fun k hk => (Work.Spaces.pzIter_eq_iteratedDeriv i (G k) z θ).symm)

theorem pthIter_finset_sum {ι : Type*} (s : Finset ι) (G : ι → ℝ → ℝ → ℝ) (i : ℕ) {z θ : ℝ}
    (h : ∀ k ∈ s, ContDiffAt ℝ i (fun θ' => G k z θ') θ) :
    Work.Spaces.pthIter i (fun z θ => ∑ k ∈ s, G k z θ) z θ
      = ∑ k ∈ s, Work.Spaces.pthIter i (G k) z θ := by
  rw [pthIter_eq_iteratedDeriv]
  have hslice : (fun θ' => ∑ k ∈ s, G k z θ') = ∑ k ∈ s, (fun θ' => G k z θ') := by
    funext θ'; rw [Finset.sum_apply]
  rw [hslice, iteratedDeriv_sum (fun k hk => h k hk)]
  exact Finset.sum_congr rfl (fun k hk => (pthIter_eq_iteratedDeriv i (G k) z θ).symm)


/-! ## Evaluation of the θ-derivatives of the two pieces of `Q` -/

/-- The `θ`-derivative of order `r ≤ 3` at `θ = C` of the "boundary-matching" piece:
only the exponent `r` survives. -/
theorem pthIter_VL {A C : ℝ} {sv : Fin 4 → Finset ℕ} {vc : (s : Fin 4) → ℕ → ℝ}
    (z : ℝ) (r : Fin 4) :
    Work.Spaces.pthIter r.1 (fun z θ => ∑ s : Fin 4,
        ((∑ k ∈ sv s, vc s k * (z - A) ^ k) / ((s.1).factorial : ℝ)) * (θ - C) ^ (s.1)) z C
      = ∑ k ∈ sv r, vc r k * (z - A) ^ k := by
  rw [pthIter_finset_sum _ _ _ (fun s _ => by fun_prop)]
  rw [Finset.sum_eq_single r]
  · rw [pthIter_separable, ← iteratedDeriv_eq_iterate, iteratedDeriv_shifted_pow]
    rw [Nat.sub_self, sub_self, pow_zero, Nat.descFactorial_self, mul_one]
    rw [div_mul_cancel₀]
    exact_mod_cast (Nat.factorial_ne_zero r.1)
  · intro s _ hsr
    rw [pthIter_separable, ← iteratedDeriv_eq_iterate, iteratedDeriv_shifted_pow]
    rcases lt_trichotomy s.1 r.1 with hlt | heq | hgt
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr hlt]; simp
    · exact absurd (Fin.ext heq) hsr
    · have h : s.1 - r.1 ≠ 0 := by omega
      rw [sub_self, zero_pow h]; ring
  · intro hmem
    exact absurd (Finset.mem_univ r) hmem

/-- The `θ`-derivative of order `r ≤ 3` at `θ = C` of the "top" piece vanishes. -/
theorem pthIter_VR {A C : ℝ} {n : ℕ} {qp qq : Fin n → ℕ} {qc : Fin n → ℝ}
    (z : ℝ) (r : ℕ) (hr : r ≤ 3) :
    Work.Spaces.pthIter r (fun z θ => ∑ k : Fin n,
        ((qc k * (z - A) ^ (qp k)) / (((qq k + 4).descFactorial 4 : ℕ) : ℝ))
          * (θ - C) ^ (qq k + 4)) z C = 0 := by
  rw [pthIter_finset_sum _ _ _ (fun k _ => by fun_prop)]
  refine Finset.sum_eq_zero (fun k _ => ?_)
  rw [pthIter_separable, ← iteratedDeriv_eq_iterate, iteratedDeriv_shifted_pow]
  have h : qq k + 4 - r ≠ 0 := by omega
  rw [sub_self, zero_pow h]
  ring

/-- The fourth `θ`-derivative of the "boundary-matching" piece vanishes identically. -/
theorem pthIter4_VL {A C : ℝ} {sv : Fin 4 → Finset ℕ} {vc : (s : Fin 4) → ℕ → ℝ} (z θ : ℝ) :
    Work.Spaces.pthIter 4 (fun z θ => ∑ s : Fin 4,
        ((∑ k ∈ sv s, vc s k * (z - A) ^ k) / ((s.1).factorial : ℝ)) * (θ - C) ^ (s.1)) z θ = 0 := by
  rw [pthIter_finset_sum _ _ _ (fun s _ => by fun_prop)]
  refine Finset.sum_eq_zero (fun s _ => ?_)
  rw [pthIter_separable, ← iteratedDeriv_eq_iterate, iteratedDeriv_shifted_pow]
  rw [Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : s.1 < 4)]
  ring

/-- The fourth `θ`-derivative of the "top" piece. -/
theorem pthIter4_VR {A C : ℝ} {n : ℕ} {qp qq : Fin n → ℕ} {qc : Fin n → ℝ} (z θ : ℝ) :
    Work.Spaces.pthIter 4 (fun z θ => ∑ k : Fin n,
        ((qc k * (z - A) ^ (qp k)) / (((qq k + 4).descFactorial 4 : ℕ) : ℝ))
          * (θ - C) ^ (qq k + 4)) z θ
      = ∑ k : Fin n, qc k * (z - A) ^ (qp k) * (θ - C) ^ (qq k) := by
  rw [pthIter_finset_sum _ _ _ (fun k _ => by fun_prop)]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [pthIter_separable, ← iteratedDeriv_eq_iterate, iteratedDeriv_shifted_pow]
  have hne : (((qq k + 4).descFactorial 4 : ℕ) : ℝ) ≠ 0 := by
    have hpos : 0 < (qq k + 4).descFactorial 4 := by
      rw [Nat.pos_iff_ne_zero, Ne, Nat.descFactorial_eq_zero_iff_lt]; omega
    exact_mod_cast hpos.ne'
  rw [show qq k + 4 - 4 = qq k from by omega]
  field_simp


/-! ## The class of shifted monomial sums -/

/-- A function of two variables which is a finite sum of *shifted* monomials
`c * (z - A) ^ p * (θ - C) ^ q`. -/
def IsShiftMono (A C : ℝ) (f : ℝ → ℝ → ℝ) : Prop :=
  ∃ (m : ℕ) (p q : Fin m → ℕ) (c : Fin m → ℝ),
    ∀ z θ, f z θ = ∑ k, c k * (z - A) ^ (p k) * (θ - C) ^ (q k)

theorem isShiftMono_congr {A C : ℝ} {f g : ℝ → ℝ → ℝ} (h : ∀ z θ, f z θ = g z θ)
    (hg : IsShiftMono A C g) : IsShiftMono A C f := by
  obtain ⟨m, p, q, c, hc⟩ := hg
  exact ⟨m, p, q, c, fun z θ => (h z θ).trans (hc z θ)⟩

theorem isShiftMono_monom (A C : ℝ) (p q : ℕ) (c : ℝ) :
    IsShiftMono A C (fun z θ => c * (z - A) ^ p * (θ - C) ^ q) := by
  refine ⟨1, fun _ => p, fun _ => q, fun _ => c, fun z θ => ?_⟩
  simp

theorem isShiftMono_zero (A C : ℝ) : IsShiftMono A C (0 : ℝ → ℝ → ℝ) := by
  refine ⟨1, fun _ => 0, fun _ => 0, fun _ => 0, fun z θ => ?_⟩
  simp

theorem isShiftMono_const (A C : ℝ) (r : ℝ) : IsShiftMono A C (fun _ _ : ℝ => r) := by
  refine ⟨1, fun _ => 0, fun _ => 0, fun _ => r, fun z θ => ?_⟩
  simp

theorem isShiftMono_add {A C : ℝ} {f g : ℝ → ℝ → ℝ} (hf : IsShiftMono A C f)
    (hg : IsShiftMono A C g) : IsShiftMono A C (fun z θ => f z θ + g z θ) := by
  obtain ⟨m₁, p₁, q₁, c₁, h₁⟩ := hf
  obtain ⟨m₂, p₂, q₂, c₂, h₂⟩ := hg
  refine ⟨m₁ + m₂, Fin.append p₁ p₂, Fin.append q₁ q₂, Fin.append c₁ c₂, fun z θ => ?_⟩
  change f z θ + g z θ = _
  rw [h₁ z θ, h₂ z θ, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right]

theorem isShiftMono_smul {A C : ℝ} (r : ℝ) {f : ℝ → ℝ → ℝ} (hf : IsShiftMono A C f) :
    IsShiftMono A C (fun z θ => r * f z θ) := by
  obtain ⟨m, p, q, c, hc⟩ := hf
  refine ⟨m, p, q, fun k => r * c k, fun z θ => ?_⟩
  change r * f z θ = _
  rw [hc z θ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem isShiftMono_mul_sub_z {A C : ℝ} {f : ℝ → ℝ → ℝ} (hf : IsShiftMono A C f) :
    IsShiftMono A C (fun z θ => (z - A) * f z θ) := by
  obtain ⟨m, p, q, c, hc⟩ := hf
  refine ⟨m, fun k => p k + 1, q, c, fun z θ => ?_⟩
  change (z - A) * f z θ = _
  rw [hc z θ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [pow_succ']; ring

theorem isShiftMono_mul_sub_theta {A C : ℝ} {f : ℝ → ℝ → ℝ} (hf : IsShiftMono A C f) :
    IsShiftMono A C (fun z θ => (θ - C) * f z θ) := by
  obtain ⟨m, p, q, c, hc⟩ := hf
  refine ⟨m, p, fun k => q k + 1, c, fun z θ => ?_⟩
  change (θ - C) * f z θ = _
  rw [hc z θ, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [pow_succ']; ring

theorem isShiftMono_mul_sub_theta_pow {A C : ℝ} {f : ℝ → ℝ → ℝ} (hf : IsShiftMono A C f) :
    ∀ q : ℕ, IsShiftMono A C (fun z θ => (θ - C) ^ q * f z θ) := by
  intro q
  induction q with
  | zero => simpa using hf
  | succ n ih =>
      have h := isShiftMono_mul_sub_theta ih
      refine isShiftMono_congr (fun z θ => ?_) h
      rw [pow_succ]; ring

theorem isShiftMono_sub {A C : ℝ} {f g : ℝ → ℝ → ℝ} (hf : IsShiftMono A C f)
    (hg : IsShiftMono A C g) : IsShiftMono A C (fun z θ => f z θ - g z θ) := by
  have h := isShiftMono_add hf (isShiftMono_smul (-1) hg)
  refine isShiftMono_congr (fun z θ => ?_) h
  ring

theorem isShiftMono_finset_sum {A C : ℝ} {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ → ℝ)
    (h : ∀ i ∈ s, IsShiftMono A C (f i)) : IsShiftMono A C (∑ i ∈ s, f i) :=
  Finset.sum_induction f (IsShiftMono A C) (fun _ _ ha hb => isShiftMono_add ha hb)
    (isShiftMono_zero A C) h

/-- A shifted monomial sum is a monomial sum in the unshifted variables. -/
theorem isMonoSum_of_isShiftMono {A C : ℝ} {f : ℝ → ℝ → ℝ} (h : IsShiftMono A C f) :
    IsMonoSum (fun u v => f (u + A) (v + C)) := by
  obtain ⟨m, p, q, c, hc⟩ := h
  exact ⟨m, p, q, c, fun u v => by
    have := hc (u + A) (v + C)
    simpa [show u + A - A = u from by ring, show v + C - C = v from by ring] using this⟩

/-- Conversely, a monomial sum of the translated function is a shifted monomial sum. -/
theorem isShiftMono_of_isMonoSum {A C : ℝ} {f : ℝ → ℝ → ℝ}
    (h : IsMonoSum (fun u v => f (u + A) (v + C))) : IsShiftMono A C f := by
  obtain ⟨m, p, q, c, hc⟩ := h
  exact ⟨m, p, q, c, fun z θ => by
    have := hc (z - A) (θ - C)
    simpa [show z - A + A = z from by ring, show θ - C + C = θ from by ring] using this⟩


end Work.FTS.GalBasis.GalApprox
