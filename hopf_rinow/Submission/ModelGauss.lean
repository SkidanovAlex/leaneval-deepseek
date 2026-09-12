import Submission.Model
import Submission.ModelCore
import Submission.ModelSpeed
import Submission.ModelFlowCont
import Submission.ModelJacobi
import Submission.ModelJacLin
import Submission.ModelVarConv
import Submission.ModelVarFrechet
import Submission.ModelDerivId
import Submission.ModelUniq
import Mathlib

/-!
# Gauss lemma identity at the model level

We prove the Gauss-lemma identity for a geodesic `(c, vel)` and a solution `J` of the
linearized (Jacobi) equation with `J 0 = (0, w)`:

    d/dt [ g (c t) ((J t).1) (vel t) ] = g x₀ w v₀        (t ∈ Ioo (-ε) ε)

Strategy (two independent pieces):

* **Part I** (`gauss_deriv_pointwise`): by a direct product-rule computation the derivative of
  `s ↦ g (c s) ((J s).1) (vel s)` at `t` equals

      ψ t := (g (c t)) ((J t).2) (vel t) + ½ ((fderiv ℝ g (c t)) ((J t).1)) (vel t) (vel t)

  (this uses only the first component of the linearized equation, the geodesic equation for
  `vel`, and the symmetry of the metric and of its derivative).

* **Part II** (`gauss_psi_locally_constant`): `ψ` is locally constant near every point `t₀`.
  Fix `t₀`; let `z₀ := (c t₀, vel t₀)`.  The local flow around `z₀` gives a two-parameter
  family of geodesics `(s, u) ↦ Φ (z₀ + s • J t₀) u`; for each fixed `s` the metric speed is
  constant in `u` (model `speed_const`), hence the energy
  `E(s,u) := ½ g(γ(s,u))(vel(s,u))(vel(s,u))` satisfies `E(s,u) = E(s,0)`.  Differentiating at
  `s = 0` (using the Fréchet differentiability of the flow in the initial data and the fact
  that its derivative is the linearized solution, `flow_pair_fderiv`) gives `ψ(t₀+u) = ψ(t₀)`.

  Since `ψ` is locally constant on the connected interval `Ioo (-ε) ε`, it is constant there;
  at `t = 0` one has `ψ 0 = (g x₀) w v₀` because `J 0 = (0, w)`, `c 0 = x₀`, `vel 0 = v₀`.
  Combining with Part I yields the theorem.
-/

open ContinuousLinearMap
open scoped ContDiff Topology
open Set Metric

namespace Submission.Model

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

noncomputable section
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false

/-- derivative of the metric is symmetric in the two vector arguments -/
lemma metric_fderiv_symmetric (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hsym : ∀ x u v, (g x) u v = (g x) v u) (x h u v : E) :
    (((fderiv ℝ g x) h) u) v = (((fderiv ℝ g x) h) v) u := by
  have hgfd : HasFDerivAt g (fderiv ℝ g x) x :=
    (hg.contDiffAt.differentiableAt (by norm_num : (3 : ℕ∞ω) ≠ 0)).hasFDerivAt
  have hF1 : HasFDerivAt (fun y : E => ((g y) u) v) (((fderiv ℝ g x).flip u).flip v) x := by
    have h1 := hgfd.clm_apply (hasFDerivAt_const u x)
    have h2 : HasFDerivAt (fun y : E => (g y) u) ((fderiv ℝ g x).flip u) x := by simpa using h1
    have h3 := h2.clm_apply (hasFDerivAt_const v x)
    simpa using h3
  have hF2 : HasFDerivAt (fun y : E => ((g y) v) u) (((fderiv ℝ g x).flip v).flip u) x := by
    have h1 := hgfd.clm_apply (hasFDerivAt_const v x)
    have h2 : HasFDerivAt (fun y : E => (g y) v) ((fderiv ℝ g x).flip v) x := by simpa using h1
    have h3 := h2.clm_apply (hasFDerivAt_const u x)
    simpa using h3
  have hfd : (((fderiv ℝ g x).flip u).flip v) = (((fderiv ℝ g x).flip v).flip u) := by
    have hsub := hF1.sub hF2
    have hzero : HasFDerivAt ((fun y : E => ((g y) u) v) - (fun y : E => ((g y) v) u))
        (0 : E →L[ℝ] ℝ) x := by
      have hc : HasFDerivAt (fun _ : E => (0 : ℝ)) (0 : E →L[ℝ] ℝ) x := hasFDerivAt_const 0 x
      refine hc.congr_of_eventuallyEq ?_
      filter_upwards with y
      simp [hsym y u v]
    exact sub_eq_zero.mp (hsub.unique hzero)
  have happ := congrArg (fun L : E →L[ℝ] ℝ => L h) hfd
  simpa [ContinuousLinearMap.flip_apply] using happ

/-- first component of the derivative of the geodesic field applied to a variation is the
velocity component of the variation -/
lemma fst_fderiv_odeField (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (p δ : E × E) :
    ((fderiv ℝ (odeField g) p) δ).1 = δ.2 := by
  have hdif : DifferentiableAt ℝ (odeField g) p :=
    (odeField_contDiffAt g hg hinv p.1 p.2).differentiableAt (by norm_num : (1 : ℕ∞ω) ≠ 0)
  have hf := (fderiv.fst hdif)
  have hfunext : (fun q : E × E => (odeField g q).1) = Prod.snd := by
    funext q
    rfl
  calc
    ((fderiv ℝ (odeField g) p) δ).1 = ((ContinuousLinearMap.fst ℝ E E ∘SL (fderiv ℝ (odeField g) p)) δ) := by simp
    _ = (fderiv ℝ (fun q : E × E => (odeField g q).1) p) δ := by rw [← hf]
    _ = (fderiv ℝ Prod.snd p) δ := by rw [hfunext]
    _ = δ.2 := by simp [fderiv_snd]

/-- product rule for a scalar built from a bilinear form and two vectors (at time `a`) -/
lemma bilinear_deriv_at {a : ℝ} (B : ℝ → Bilin E) (b : Bilin E)
    (u w : ℝ → E) (u0 w0 : E) (hB : HasDerivAt B b a)
    (hu : HasDerivAt u u0 a) (hw : HasDerivAt w w0 a) :
    HasDerivAt (fun s : ℝ => (B s) (u s) (w s))
      (((b (u a)) (w a)) + (((B a) u0) (w a)) + ((B a) (u a)) w0) a := by
  have hφ : HasDerivAt (fun s : ℝ => (B s) (u s)) ((b (u a)) + ((B a) u0)) a := by
    simpa [add_comm] using (HasDerivAt.clm_apply (𝕜 := ℝ) (F := E) (G := E →L[ℝ] ℝ)
      (c := B) (c' := b) (u := u) (u' := u0) hB hu)
  simpa [add_assoc] using (HasDerivAt.clm_apply (𝕜 := ℝ) (F := E) (G := ℝ)
    (c := fun s : ℝ => (B s) (u s)) (c' := (b (u a)) + ((B a) u0)) (u := w) (u' := w0) hφ hw)

/-- derivative of a shifted function: `s ↦ f (t₀ + s)` -/
lemma hasDerivAt_shift_right {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : ℝ → F) (t₀ x : ℝ) {d : F} (hf : HasDerivAt f d (t₀ + x)) :
    HasDerivAt (fun u : ℝ => f (t₀ + u)) d x := by
  have hAdd : HasDerivAt (fun u : ℝ => t₀ + u) (1 : ℝ) x := by
    have h₁ : HasDerivAt (fun y : ℝ => y + t₀) (1 : ℝ) x := by
      simpa using (hasDerivAt_add_const_iff (c := t₀) (f := fun y : ℝ => y) (f' := (1 : ℝ)) (x := x)).mpr (hasDerivAt_id x)
    refine h₁.congr_of_eventuallyEq ?_
    filter_upwards with y
    simp [add_comm]
  have hc : HasDerivAt (f ∘ fun u : ℝ => t₀ + u) d x := by
    simpa using HasDerivAt.scomp x (h := fun u : ℝ => t₀ + u) (g₁ := f) (g₁' := d) hf hAdd
  simpa [Function.comp_def] using hc

/-- The derivative-relevant quantity in the Gauss identity (the value of the derivative of the
pairing `g(c)((J·).1, vel)`). -/
noncomputable def gaussPsi (g : E → Bilin E) (c vel : ℝ → E) (J : ℝ → E × E) (t : ℝ) : ℝ :=
  ((g (c t)) ((J t).2)) (vel t) + (1 / 2 : ℝ) * ((((fderiv ℝ g (c t)) ((J t).1)) (vel t)) (vel t))

/-- s-derivative of the half-energy of a curve `s ↦ (x(s), v(s))` in `E × E` -/
lemma pair_energy_deriv (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (Q : ℝ → E × E) (d : E × E) (hQ : HasDerivAt Q d 0) :
    HasDerivAt (fun s : ℝ => (1 / 2) * ((g (Q s).1) ((Q s).2)) ((Q s).2))
      (((1 / 2) * (((fderiv ℝ g (Q 0).1) d.1) ((Q 0).2)) ((Q 0).2)) +
        ((g (Q 0).1) d.2) ((Q 0).2)) 0 := by
  have hQ1 : HasDerivAt (fun s : ℝ => (Q s).1) d.1 0 := by
    have hf := hQ.hasFDerivAt.fst.hasDerivAt
    simpa using hf
  have hQ2 : HasDerivAt (fun s : ℝ => (Q s).2) d.2 0 := by
    have hf := hQ.hasFDerivAt.snd.hasDerivAt
    simpa using hf
  have hB : HasDerivAt (fun s : ℝ => g (Q s).1) ((fderiv ℝ g (Q 0).1) d.1) 0 := by
    have hgfd : HasFDerivAt g (fderiv ℝ g (Q 0).1) (Q 0).1 :=
      (hg.contDiffAt.differentiableAt (by norm_num : (3 : ℕ∞ω) ≠ 0)).hasFDerivAt
    have hc := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := E) (E := Bilin E)
      (f := fun s : ℝ => (Q s).1) (f' := d.1) 0 hgfd hQ1
    simpa [Function.comp_def] using hc
  have hRaw := bilinear_deriv_at (a := 0) (B := fun s : ℝ => g (Q s).1)
    (b := (fderiv ℝ g (Q 0).1) d.1) (u := fun s : ℝ => (Q s).2) (w := fun s : ℝ => (Q s).2)
    (u0 := d.2) (w0 := d.2) hB hQ2 hQ2
  have hc2 := hRaw.const_mul (1 / 2)
  apply hc2.congr_deriv
  have hsym' : ((g (Q 0).1) ((Q 0).2)) d.2 = ((g (Q 0).1) d.2) ((Q 0).2) := by
    simpa using hsym (Q 0).1 ((Q 0).2) d.2
  ring_nf
  rw [← hsym']
  ring

/-- Pointwise derivative of the metric pairing of position-variation with velocity along a
geodesic equals `gaussPsi`. -/
lemma gauss_deriv_pointwise (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    {ε : ℝ} (hε : 0 < ε) {c vel : ℝ → E} {J : ℝ → E × E}
    (hc : ∀ t ∈ Ioo (-ε) ε, HasDerivAt c (vel t) t)
    (hv : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t)
    (hJ : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt J ((fderiv ℝ (odeField g)) (c t, vel t) (J t)) t) :
    ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt (fun s : ℝ => ((g (c s)) ((J s).1)) (vel s)) (gaussPsi g c vel J t) t := by
  intro t ht
  let A : Bilin E := g (c t)
  let T : E →L[ℝ] Bilin E := fderiv ℝ g (c t)
  let u : E := vel t
  let Jp : E := (J t).1
  let Jv : E := (J t).2
  let u' : E := accel A T u
  have hgfd : HasFDerivAt g (fderiv ℝ g (c t)) (c t) := by
    exact (hg.contDiffAt.differentiableAt (by norm_num : (3 : ℕ∞ω) ≠ 0)).hasFDerivAt
  have hgc : HasDerivAt (fun s : ℝ => g (c s)) (T u) t := by
    have h1 : HasDerivAt (g ∘ c) ((fderiv ℝ g (c t)) (vel t)) t :=
      HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := E) (E := Bilin E)
        (f := c) (f' := vel t) t hgfd (hc t ht)
    convert h1 using 1
    funext s
    rfl
  have hv' : HasDerivAt vel u' t := by
    simpa [A, T, u, u'] using hv t ht
  have hJ1 : HasDerivAt (fun s : ℝ => (J s).1) Jv t := by
    have h1 : HasDerivAt (fun s : ℝ => (J s).1) ((fderiv ℝ (odeField g)) (c t, vel t) (J t)).1 t := by
      have hf := (hJ t ht).hasFDerivAt.fst.hasDerivAt
      simpa using hf
    convert h1 using 1
    exact (fst_fderiv_odeField g hg hinv (c t, vel t) (J t)).symm
  have hF := bilinear_deriv_at (B := fun s : ℝ => g (c s)) (b := T u)
    (u := fun s : ℝ => (J s).1) (w := vel) (u0 := Jv) (w0 := u') hgc hJ1 hv'
  have hODE : A u' = rhsCovector T u := by
    have hAinv : A.IsInvertible := by simpa [A] using hinv (c t)
    calc
      A u' = A ((ContinuousLinearMap.inverse A) (rhsCovector T u)) := by simp [u', accel]
      _ = rhsCovector T u :=
        ContinuousLinearMap.IsInvertible.self_apply_inverse hAinv (rhsCovector T u)
  have hsymA : ∀ a b : E, (A a) b = (A b) a := by
    intro a b
    simpa [A] using hsym (c t) a b
  have hsymT : ∀ h a b : E, ((T h) a) b = ((T h) b) a := by
    intro h a b
    simpa [T] using metric_fderiv_symmetric g hg hsym (c t) h a b
  have hmiddle : ((T u) Jp) u + ((A Jp) u') = (1 / 2) * ((T Jp) u) u := by
    calc
      ((T u) Jp) u + ((A Jp) u') = ((T u) u) Jp + ((A u') Jp) := by
        rw [hsymT u Jp u, hsymA Jp u']
      _ = ((T u) u) Jp + (rhsCovector T u) Jp := by rw [hODE]
      _ = ((T u) u) Jp + ((1 / 2) * (((T Jp) u) u) - ((T u) u) Jp) := by
        rw [rhsCovector_apply]
      _ = (1 / 2) * ((T Jp) u) u := by ring
  have hpsi : (((T u) Jp) u + ((A Jv) u) + ((A Jp) u')) = gaussPsi g c vel J t := by
    dsimp [gaussPsi, A, T, u, Jp, Jv, u']
    have hsum' : ((((fderiv ℝ g (c t)) (vel t)) ((J t).1)) (vel t)) + (((g (c t)) ((J t).1)) (accel (g (c t)) (fderiv ℝ g (c t)) (vel t))) = (1 / 2) * ((((fderiv ℝ g (c t)) ((J t).1)) (vel t)) (vel t)) := by
      simpa [A, T, u, Jp, u'] using hmiddle
    calc
      ((((fderiv ℝ g (c t)) (vel t)) ((J t).1)) (vel t)) + (((g (c t)) ((J t).2)) (vel t)) + (((g (c t)) ((J t).1)) (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)))
          = (((g (c t)) ((J t).2)) (vel t)) + ((((fderiv ℝ g (c t)) (vel t)) ((J t).1)) (vel t) + (((g (c t)) ((J t).1)) (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)))) := by ring
      _ = (((g (c t)) ((J t).2)) (vel t)) + (1 / 2) * ((((fderiv ℝ g (c t)) ((J t).1)) (vel t)) (vel t)) := by rw [hsum']
  convert hF using 1
  exact hpsi.symm

/-- Around any base point the flow exists, is differentiable in the initial data, and the
derivative applied to a direction is the solution of the linearized equation.  The time window
is at most `a`. -/
lemma flow_pair_fderiv (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (z₀ : E × E) (a : ℝ) (ha : 0 < a) :
    ∃ T > 0, T ≤ a ∧ ∃ Φ : E × E → ℝ → E × E,
      (∀ z ∈ closedBall z₀ 1, Φ z 0 = z ∧
         ∀ t ∈ Icc (-T) T, HasDerivAt (Φ z) (odeField g (Φ z t)) t) ∧
      (∀ t ∈ Ioo (-T) T, ∃ L : E × E →L[ℝ] E × E,
         HasFDerivAt (fun z => Φ z t) L z₀ ∧
         ∀ w : E × E, ∀ J : ℝ → E × E,
           J 0 = w →
           (∀ s ∈ Ioo (-T) T,
             HasDerivAt J ((fderiv ℝ (odeField g)) (Φ z₀ s) (J s)) s) →
           L w = J t) := by
  classical
  rcases flowOnUnitBall g hg hinv z₀ with ⟨Tf, hTf, Lf, Φ, hΦF, hLipF⟩
  rcases canonical_solutions g hg hinv z₀ Tf hTf Φ hΦF with
    ⟨Tj, hTj0, hTjTf, Jc, hJc0, hJcd, hJcadd, hJcsmul⟩
  rcases flow_fderiv_canonical g hg hinv z₀ Tf hTf Lf Φ hΦF hLipF Tj hTj0 hTjTf
    Jc hJc0 hJcd hJcadd hJcsmul with ⟨T1, hT10, hT1Tf, hFd⟩
  let T : ℝ := min T1 (min (Tj / 2) (a / 2))
  have hTpos : 0 < T := by
    dsimp [T]
    exact lt_min hT10 (by positivity)
  have hTleA : T ≤ a := by
    dsimp [T]
    calc min T1 (min (Tj / 2) (a / 2)) ≤ min (Tj / 2) (a / 2) := min_le_right _ _
      _ ≤ a / 2 := min_le_right _ _
      _ ≤ a := by linarith
  have hTT1 : T ≤ T1 := by dsimp [T]; exact min_le_left _ _
  have hTltTj : T < Tj := by
    have : T ≤ Tj / 2 := by
      dsimp [T]
      exact le_trans (min_le_right T1 (min (Tj / 2) (a / 2))) (min_le_left (Tj / 2) (a / 2))
    have h2 : Tj / 2 < Tj := by linarith
    exact lt_of_le_of_lt this h2
  have hTltTf : T < Tf := lt_of_le_of_lt hTT1 hT1Tf
  have hΦ₀T : ∀ z ∈ closedBall z₀ 1, Φ z 0 = z ∧
      ∀ t ∈ Icc (-T) T, HasDerivAt (Φ z) (odeField g (Φ z t)) t := by
    intro z hz
    constructor
    · exact (hΦF z hz).1
    · intro t ht
      exact (hΦF z hz).2 t (by
        constructor
        · exact le_trans (neg_le_neg (le_of_lt hTltTf)) ht.1
        · exact le_trans ht.2 (le_of_lt hTltTf))
  have hz₀mem : z₀ ∈ closedBall z₀ 1 := by simp
  refine ⟨T, hTpos, hTleA, Φ, hΦ₀T, ?_⟩
  · intro t ht
    have ht1 : t ∈ Icc (-T1) T1 := by
      constructor
      · exact le_trans (neg_le_neg hTT1) (le_of_lt ht.1)
      · exact le_trans (le_of_lt ht.2) hTT1
    rcases hFd t ht1 with ⟨L, hLfd, hLval⟩
    refine ⟨L, hLfd, ?_⟩
    intro w J hJ0' hJ'
    have hbase (s : ℝ) (hs : s ∈ Ioo (-T) T) :
        HasDerivAt (fun u => Φ z₀ u) (odeField g (Φ z₀ s)) s := by
      have hsI : s ∈ Icc (-T) T := Ioo_subset_Icc_self hs
      exact (hΦ₀T z₀ hz₀mem).2 s hsI
    have hJc_w : Jc w 0 = w ∧ ∀ s ∈ Ioo (-T) T,
        HasDerivAt (Jc w) ((fderiv ℝ (odeField g)) (Φ z₀ s) (Jc w s)) s := by
      constructor
      · exact hJc0 w
      · intro s hs
        have hsj : s ∈ Ioo (-Tj) Tj := by
          constructor
          · exact lt_trans (neg_lt_neg hTltTj) hs.1
          · exact lt_trans hs.2 hTltTj
        exact hJcd w s hsj
    have hJ'z : J 0 = w ∧ ∀ s ∈ Ioo (-T) T,
        HasDerivAt J ((fderiv ℝ (odeField g)) (Φ z₀ s) (J s)) s := by
      constructor
      · exact hJ0'
      · intro s hs
        exact hJ' s hs
    have huniq := jacobi_unique_along_flow g hg hinv (ε := T) hTpos (z := fun u => Φ z₀ u)
      (hz := hbase) (J₁ := Jc w) (J₂ := J) (w := w) hJc_w hJ'z
    calc
      L w = Jc w t := hLval w
      _ = J t := huniq t ht

/-- speed is constant along every trajectory of a local flow that solves the geodesic ODE -/
lemma flow_speed_const (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    (z₀ : E × E) (T : ℝ) (hT : 0 < T) (Φ : E × E → ℝ → E × E) (z : E × E)
    (hΦz : ∀ t ∈ Ioo (-T) T, HasDerivAt (Φ z) (odeField g (Φ z t)) t) :
    ∀ t ∈ Ioo (-T) T,
      HasDerivAt (fun u : ℝ => (g ((Φ z u).1)) ((Φ z u).2) ((Φ z u).2)) 0 t := by
  intro t ht
  let c : ℝ → E := fun u => (Φ z u).1
  let vel : ℝ → E := fun u => (Φ z u).2
  have hc (t' : ℝ) (ht' : t' ∈ Ioo (-T) T) : HasDerivAt c (vel t') t' := by
    have h1 : HasDerivAt (fun u => (Φ z u).1) (odeField g (Φ z t')).1 t' := by
      have hf := (hΦz t' ht').hasFDerivAt.fst.hasDerivAt
      simpa using hf
    simpa [c, vel, odeField] using h1
  have hv (t' : ℝ) (ht' : t' ∈ Ioo (-T) T) :
      HasDerivAt vel (accel (g (c t')) (fderiv ℝ g (c t')) (vel t')) t' := by
    have h1 : HasDerivAt (fun u => (Φ z u).2) (odeField g (Φ z t')).2 t' := by
      have hf := (hΦz t' ht').hasFDerivAt.snd.hasDerivAt
      simpa using hf
    simpa [c, vel, odeField] using h1
  have hs := speed_const g hg hinv hsym (hε := hT) hc hv
  have hs' := hs t ht
  simpa [c, vel] using hs'

/-- a function on an open interval with zero derivative is constant -/
lemma eq_of_deriv_eq_zero_on_Ioo {f : ℝ → ℝ} {δ : ℝ} (hδ : 0 < δ)
    (hderiv : ∀ u ∈ Ioo (-δ) δ, HasDerivAt f 0 u) :
    ∀ u ∈ Ioo (-δ) δ, f u = f 0 := by
  intro u hu
  have hf : DifferentiableOn ℝ f (Ioo (-δ) δ) := by
    intro u' hu'
    exact (hderiv u' hu').differentiableAt.differentiableWithinAt
  have hder : EqOn (deriv f) 0 (Ioo (-δ) δ) := by
    intro u' hu'
    exact (hderiv u' hu').deriv
  rcases IsOpen.exists_is_const_of_deriv_eq_zero (𝕜 := ℝ) (G := ℝ) (s := Ioo (-δ) δ)
    (hs := isOpen_Ioo) (hs' := isPreconnected_Ioo) hf hder with ⟨a, ha⟩
  have h0 : 0 ∈ Ioo (-δ) δ := by constructor <;> linarith
  calc
    f u = a := ha u hu
    _ = f 0 := (ha 0 h0).symm

/-- The quantity `gaussPsi` is locally constant in time (Gauss-lemma constancy). -/
lemma gauss_psi_locally_constant (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    {ε : ℝ} (hε : 0 < ε) {c vel : ℝ → E} {J : ℝ → E × E}
    (hc : ∀ t ∈ Ioo (-ε) ε, HasDerivAt c (vel t) t)
    (hv : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t)
    (hJ : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt J ((fderiv ℝ (odeField g)) (c t, vel t) (J t)) t) :
    ∀ t₀ ∈ Ioo (-ε) ε,
      ∃ δ > 0, ∀ u : ℝ, |u| < δ → t₀ + u ∈ Ioo (-ε) ε →
        gaussPsi g c vel J (t₀ + u) = gaussPsi g c vel J t₀ := by
  intro t₀ ht₀
  let z₀ : E × E := (c t₀, vel t₀)
  let d : E × E := J t₀
  let ρ₀ : ℝ := min (ε + t₀) (ε - t₀)
  have ht₀lo : -ε < t₀ := ht₀.1
  have ht₀hi : t₀ < ε := ht₀.2
  have hρ₀pos : 0 < ρ₀ := by
    dsimp [ρ₀]
    exact lt_min (by linarith) (by linarith)
  have hρ₀l : ρ₀ ≤ ε + t₀ := by
    dsimp [ρ₀]
    exact min_le_left (ε + t₀) (ε - t₀)
  have hρ₀r : ρ₀ ≤ ε - t₀ := by
    dsimp [ρ₀]
    exact min_le_right (ε + t₀) (ε - t₀)
  have hρ₀I : ∀ s : ℝ, |s| < ρ₀ → t₀ + s ∈ Ioo (-ε) ε := by
    intro s hs
    rcases abs_lt.mp hs with ⟨hlo, hhi⟩
    constructor <;> linarith
  rcases flow_pair_fderiv g hg hinv z₀ ρ₀ hρ₀pos with ⟨T, hT, hTleρ, Φ, hΦ₀, hFd⟩
  let s₀ : ℝ := min 1 (1 / (‖d‖ + 1))
  have hs₀pos : 0 < s₀ := by dsimp [s₀]; exact lt_min zero_lt_one (by positivity)
  have hzball (s : ℝ) (hs : |s| ≤ s₀) : z₀ + s • d ∈ closedBall z₀ 1 := by
    rw [mem_closedBall, dist_eq_norm]
    calc
      ‖(z₀ + s • d) - z₀‖ = ‖s • d‖ := by simp
      _ = |s| * ‖d‖ := by rw [norm_smul, Real.norm_eq_abs]
      _ ≤ s₀ * ‖d‖ := mul_le_mul_of_nonneg_right hs (norm_nonneg d)
      _ ≤ (1 / (‖d‖ + 1)) * ‖d‖ := by
        exact mul_le_mul_of_nonneg_right (by dsimp [s₀]; exact min_le_right 1 (1 / (‖d‖ + 1))) (norm_nonneg d)
      _ = ‖d‖ / (‖d‖ + 1) := by ring
      _ ≤ 1 := by
        have hdn : 0 < ‖d‖ + 1 := by positivity
        exact (div_le_one hdn).mpr (by linarith)
  have hmu (u : ℝ) (hu : u ∈ Ioo (-T) T) : t₀ + u ∈ Ioo (-ε) ε := by
    apply hρ₀I
    have hub : |u| < T := by
      rw [abs_lt]
      exact hu
    exact lt_of_lt_of_le hub hTleρ
  -- the shifted base trajectory (c, vel)(t₀ + ·) is a geodesic
  have hcs (u : ℝ) (hu : u ∈ Ioo (-T) T) : HasDerivAt (fun s : ℝ => c (t₀ + s)) (vel (t₀ + u)) u := by
    exact hasDerivAt_shift_right c t₀ u (hc (t₀ + u) (hmu u hu))
  have hvs (u : ℝ) (hu : u ∈ Ioo (-T) T) :
      HasDerivAt (fun s : ℝ => vel (t₀ + s)) (accel (g (c (t₀ + u))) (fderiv ℝ g (c (t₀ + u))) (vel (t₀ + u))) u := by
    exact hasDerivAt_shift_right vel t₀ u (hv (t₀ + u) (hmu u hu))
  have hCf (u : ℝ) (hu : u ∈ Ioo (-T) T) : HasDerivAt (fun s : ℝ => (Φ z₀ s).1) ((Φ z₀ u).2) u := by
    have hz₀mem : z₀ ∈ closedBall z₀ 1 := by simp
    have hd := (hΦ₀ z₀ hz₀mem).2 u (Ioo_subset_Icc_self hu)
    have h1 : HasDerivAt (fun s : ℝ => (Φ z₀ s).1) (odeField g (Φ z₀ u)).1 u := by
      have hf := hd.hasFDerivAt.fst.hasDerivAt
      simpa using hf
    simpa [odeField] using h1
  have hVf (u : ℝ) (hu : u ∈ Ioo (-T) T) :
      HasDerivAt (fun s : ℝ => (Φ z₀ s).2) (accel (g ((Φ z₀ u).1)) (fderiv ℝ g ((Φ z₀ u).1)) ((Φ z₀ u).2)) u := by
    have hz₀mem : z₀ ∈ closedBall z₀ 1 := by simp
    have hd := (hΦ₀ z₀ hz₀mem).2 u (Ioo_subset_Icc_self hu)
    have h1 : HasDerivAt (fun s : ℝ => (Φ z₀ s).2) (odeField g (Φ z₀ u)).2 u := by
      have hf := hd.hasFDerivAt.snd.hasDerivAt
      simpa using hf
    simpa [odeField] using h1
  have hz₀mem : z₀ ∈ closedBall z₀ 1 := by simp
  have hz0 : Φ z₀ 0 = z₀ := (hΦ₀ z₀ hz₀mem).1
  have hcs0 : c (t₀ + 0) = (Φ z₀ 0).1 := by simp [z₀, hz0]
  have hvs0 : vel (t₀ + 0) = (Φ z₀ 0).2 := by simp [z₀, hz0]
  have huniq := unique_geodesic g hg hinv (hε := hT)
    (c₁ := fun s : ℝ => c (t₀ + s)) (vel₁ := fun s : ℝ => vel (t₀ + s))
    (c₂ := fun s : ℝ => (Φ z₀ s).1) (vel₂ := fun s : ℝ => (Φ z₀ s).2)
    hcs hvs hCf hVf hcs0 hvs0
  have hflow_eq (u : ℝ) (hu : u ∈ Ioo (-T) T) : Φ z₀ u = (c (t₀ + u), vel (t₀ + u)) := by
    ext <;> simp [huniq.1 u hu, huniq.2 u hu]
  -- the shifted linearized solution solves along the flow trajectory
  have hJs (u : ℝ) (hu : u ∈ Ioo (-T) T) :
      HasDerivAt (fun s : ℝ => J (t₀ + s)) ((fderiv ℝ (odeField g)) (Φ z₀ u) (J (t₀ + u))) u := by
    have hJu := hJ (t₀ + u) (hmu u hu)
    have hsh := hasDerivAt_shift_right J t₀ u hJu
    have hval : (fderiv ℝ (odeField g)) (c (t₀ + u), vel (t₀ + u)) (J (t₀ + u)) =
        (fderiv ℝ (odeField g)) (Φ z₀ u) (J (t₀ + u)) := by
      rw [← hflow_eq u hu]
    exact hsh.congr_deriv hval
  have hLd (u : ℝ) (hu : u ∈ Ioo (-T) T) :
      ∃ L : E × E →L[ℝ] E × E, HasFDerivAt (fun z => Φ z u) L z₀ ∧ L d = J (t₀ + u) := by
    rcases hFd u hu with ⟨L, hLfd, hLid⟩
    refine ⟨L, hLfd, ?_⟩
    exact hLid d (fun s : ℝ => J (t₀ + s)) (by simp [d]) hJs
  let Efun : (s u : ℝ) → ℝ := fun s u =>
    (1 / 2) * ((g ((Φ (z₀ + s • d) u).1)) ((Φ (z₀ + s • d) u).2)) ((Φ (z₀ + s • d) u).2)
  have hspd (s : ℝ) (hs : |s| ≤ s₀) :
      ∀ t ∈ Ioo (-T) T,
        HasDerivAt (fun u : ℝ => (g ((Φ (z₀ + s • d) u).1)) ((Φ (z₀ + s • d) u).2) ((Φ (z₀ + s • d) u).2)) 0 t := by
    exact flow_speed_const g hg hinv hsym z₀ T hT Φ (z₀ + s • d) (by
      intro t ht
      exact (hΦ₀ (z₀ + s • d) (hzball s hs)).2 t (Ioo_subset_Icc_self ht))
  have hEconst (s : ℝ) (hs : |s| ≤ s₀) (u : ℝ) (hu : u ∈ Ioo (-T) T) : Efun s u = Efun s 0 := by
    have hzero (u' : ℝ) (hu' : u' ∈ Ioo (-T) T) : HasDerivAt (fun v : ℝ => Efun s v) 0 u' := by
      have hsp := hspd s hs u' hu'
      exact (hsp.const_mul (1 / 2)).congr_deriv (by norm_num)
    exact eq_of_deriv_eq_zero_on_Ioo hT hzero u hu
  have hQu (u : ℝ) (hu : u ∈ Ioo (-T) T) :
      HasDerivAt (fun s : ℝ => Φ (z₀ + s • d) u) (J (t₀ + u)) 0 := by
    rcases hLd u hu with ⟨L, hLfd, hLd'⟩
    have hlin : HasDerivAt (fun s : ℝ => z₀ + s • d) d 0 := by
      have hsmul : HasDerivAt (fun s : ℝ => s • d) d 0 := by
        simpa using ((hasDerivAt_id (𝕜 := ℝ) (0 : ℝ)).smul_const d)
      have hadd := (hasDerivAt_const (𝕜 := ℝ) (0 : ℝ) z₀).add hsmul
      have hval : (0 : E × E) + d = d := by simp
      exact hadd.congr_deriv hval
    have hLfd0 : HasFDerivAt (fun z => Φ z u) L (z₀ + (0 : ℝ) • d) := by
      have hz : z₀ + (0 : ℝ) • d = z₀ := by simp
      simpa [hz] using hLfd
    have hQ' := HasFDerivAt.comp_hasDerivAt (𝕜 := ℝ) (F := E × E) (E := E × E)
      (f := fun s : ℝ => z₀ + s • d) (f' := d) 0 hLfd0 hlin
    have hQ'' : HasDerivAt (fun s : ℝ => Φ (z₀ + s • d) u) (L d) 0 := by
      simpa [Function.comp_def] using hQ'
    exact hQ''.congr_deriv hLd'
  have hEderiv (u : ℝ) (hu : u ∈ Ioo (-T) T) :
      HasDerivAt (fun s : ℝ => Efun s u) (gaussPsi g c vel J (t₀ + u)) 0 := by
    have hpe := pair_energy_deriv g hg hsym (Q := fun s : ℝ => Φ (z₀ + s • d) u)
      (d := J (t₀ + u)) (hQu u hu)
    have hV : (((1 / 2) * (((fderiv ℝ g ((Φ z₀ u).1)) ((J (t₀ + u)).1)) ((Φ z₀ u).2)) ((Φ z₀ u).2)) +
        ((g ((Φ z₀ u).1)) ((J (t₀ + u)).2)) ((Φ z₀ u).2)) = gaussPsi g c vel J (t₀ + u) := by
      rw [hflow_eq u hu]
      dsimp [gaussPsi]
      ring
    have hpe' : HasDerivAt (fun s : ℝ => Efun s u)
        (((1 / 2) * (((fderiv ℝ g ((Φ z₀ u).1)) ((J (t₀ + u)).1)) ((Φ z₀ u).2)) ((Φ z₀ u).2)) +
          ((g ((Φ z₀ u).1)) ((J (t₀ + u)).2)) ((Φ z₀ u).2)) 0 := by
      simpa [Efun] using hpe
    exact hpe'.congr_deriv hV
  -- conclusion: value at t₀+u equals value at t₀ (u in the window)
  refine ⟨T, hT, ?_⟩
  intro u hu hmemu
  have huI : u ∈ Ioo (-T) T := by
    rw [abs_lt] at hu
    exact hu
  have hagree : (fun s : ℝ => Efun s 0) =ᶠ[𝓝 (0 : ℝ)] (fun s : ℝ => Efun s u) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) (by positivity : 0 < s₀ / 2)] with s hs
    have hsle : |s| ≤ s₀ := by
      have hlt : |s| < s₀ / 2 := by
        simpa [Real.dist_eq] using (mem_ball.mp hs)
      linarith
    rw [hEconst s hsle 0 (by constructor <;> linarith)]
    exact (hEconst s hsle u huI).symm
  have hE0 : HasDerivAt (fun s : ℝ => Efun s 0) (gaussPsi g c vel J t₀) 0 := by
    simpa using hEderiv 0 (by constructor <;> linarith)
  have hEu : HasDerivAt (fun s : ℝ => Efun s u) (gaussPsi g c vel J (t₀ + u)) 0 := hEderiv u huI
  have hE0' : HasDerivAt (fun s : ℝ => Efun s 0) (gaussPsi g c vel J (t₀ + u)) 0 :=
    hEu.congr_of_eventuallyEq hagree
  exact HasDerivAt.unique hE0' hE0

/-- `gaussPsi` has derivative zero everywhere on the interval (it is locally constant). -/
lemma gauss_psi_deriv_zero (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    {ε : ℝ} (hε : 0 < ε) {c vel : ℝ → E} {J : ℝ → E × E}
    (hc : ∀ t ∈ Ioo (-ε) ε, HasDerivAt c (vel t) t)
    (hv : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t)
    (hJ : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt J ((fderiv ℝ (odeField g)) (c t, vel t) (J t)) t) :
    ∀ t₀ ∈ Ioo (-ε) ε, HasDerivAt (gaussPsi g c vel J) 0 t₀ := by
  intro t₀ ht₀
  rcases gauss_psi_locally_constant g hg hinv hsym (hε := hε) hc hv hJ t₀ ht₀ with ⟨δ, hδ, h⟩
  let ρ : ℝ := min (ε + t₀) (ε - t₀)
  have htlo : -ε < t₀ := ht₀.1
  have hthi : t₀ < ε := ht₀.2
  have hρpos : 0 < ρ := by
    dsimp [ρ]
    exact lt_min (by linarith) (by linarith)
  have hρl : ρ ≤ ε + t₀ := by
    dsimp [ρ]
    exact min_le_left (ε + t₀) (ε - t₀)
  have hρr : ρ ≤ ε - t₀ := by
    dsimp [ρ]
    exact min_le_right (ε + t₀) (ε - t₀)
  have hρmem : ∀ r : ℝ, |r| < ρ → t₀ + r ∈ Ioo (-ε) ε := by
    intro r hr
    rcases abs_lt.mp hr with ⟨hlo, hhi⟩
    constructor <;> linarith
  let δ' : ℝ := min δ (ρ / 2)
  have hδ'pos : 0 < δ' := by
    dsimp [δ']
    exact lt_min hδ (by positivity)
  have heq : gaussPsi g c vel J =ᶠ[𝓝 t₀] (fun _ : ℝ => gaussPsi g c vel J t₀) := by
    filter_upwards [Metric.ball_mem_nhds t₀ hδ'pos] with s hs
    have hlt : |s - t₀| < δ' := by
      simpa [Real.dist_eq] using (mem_ball.mp hs)
    have h1 : |s - t₀| < δ := lt_of_lt_of_le hlt (by dsimp [δ']; exact min_le_left δ (ρ / 2))
    have h2 : |s - t₀| < ρ := lt_of_lt_of_le hlt (by
      dsimp [δ']
      exact le_trans (min_le_right δ (ρ / 2)) (by linarith))
    have hmem : t₀ + (s - t₀) ∈ Ioo (-ε) ε := hρmem (s - t₀) h2
    have hres := h (s - t₀) h1 hmem
    -- hres : gaussPsi g c vel J (t₀ + (s - t₀)) = gaussPsi g c vel J t₀
    simpa using hres
  have hconst : HasDerivAt (fun _ : ℝ => gaussPsi g c vel J t₀) 0 t₀ := by
    simpa using hasDerivAt_const t₀ (gaussPsi g c vel J t₀)
  exact hconst.congr_of_eventuallyEq heq

/-- The Gauss lemma identity: along a geodesic, the metric pairing of the position part of the
linearized solution with the velocity grows linearly in time, with slope the initial metric
pairing of the velocity variation with the velocity. -/
theorem gauss_identity (g : E → Bilin E) (hg : ContDiff ℝ 3 g)
    (hinv : ∀ x, (g x).IsInvertible) (hsym : ∀ x u v, (g x) u v = (g x) v u)
    {ε : ℝ} (hε : 0 < ε) {x₀ v₀ : E} {c vel : ℝ → E} {w : E}
    (hc0 : c 0 = x₀) (hv0 : vel 0 = v₀)
    (hc : ∀ t ∈ Ioo (-ε) ε, HasDerivAt c (vel t) t)
    (hv : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt vel (accel (g (c t)) (fderiv ℝ g (c t)) (vel t)) t)
    {J : ℝ → E × E} (hJ0 : J 0 = (0, w))
    (hJ : ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt J ((fderiv ℝ (odeField g)) (c t, vel t) (J t)) t) :
    ∀ t ∈ Ioo (-ε) ε,
      HasDerivAt (fun s => g (c s) ((J s).1) (vel s)) (g x₀ w v₀) t := by
  intro t ht
  have hder := gauss_deriv_pointwise g hg hinv hsym (hε := hε) hc hv hJ t ht
  -- hder : HasDerivAt (fun s => ((g (c s)) ((J s).1)) (vel s)) (gaussPsi g c vel J t) t
  have hpsi0 : gaussPsi g c vel J 0 = (g x₀) w v₀ := by
    dsimp [gaussPsi]
    rw [hc0, hv0]
    simp [hJ0]
  have hdzero := gauss_psi_deriv_zero g hg hinv hsym (hε := hε) hc hv hJ
  have hdiff : DifferentiableOn ℝ (gaussPsi g c vel J) (Ioo (-ε) ε) := by
    intro t₀ ht₀
    exact (hdzero t₀ ht₀).differentiableAt.differentiableWithinAt
  have hzer : EqOn (deriv (gaussPsi g c vel J)) 0 (Ioo (-ε) ε) := by
    intro t₀ ht₀
    exact (hdzero t₀ ht₀).deriv
  rcases IsOpen.exists_is_const_of_deriv_eq_zero (𝕜 := ℝ) (G := ℝ) (s := Ioo (-ε) ε)
    (hs := isOpen_Ioo) (hs' := isPreconnected_Ioo) hdiff hzer with ⟨a, ha⟩
  have h0mem : 0 ∈ Ioo (-ε) ε := by constructor <;> linarith
  have hpsi_t : gaussPsi g c vel J t = (g x₀) w v₀ := by
    calc
      gaussPsi g c vel J t = a := ha t ht
      _ = gaussPsi g c vel J 0 := (ha 0 h0mem).symm
      _ = (g x₀) w v₀ := hpsi0
  exact hder.congr_deriv hpsi_t

end

end Submission.Model
