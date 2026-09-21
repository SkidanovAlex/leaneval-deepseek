import Mathlib
import Submission.Work.OddVolterra.Defs
import Submission.Work.OddVolterra.KernelExt.Defs
import Submission.Work.OddVolterra.KernelExt.Rnu_spec
import Submission.Work.OddVolterra.Kernel.Diag

/-!
# A self-contained copy of the jet encoding `Q` of the Bell recursion `Rnu`

This file contains the jet encoding of `KernelExt.Rnu` (`Q`, `Jjet`, `jrest`, `jshift`) and the
identity `Rnu_eq_Q`, copied verbatim (under the namespace `Qaux`) from
`Submission/Work/Window/fed_thetaM_state_bounds.lean`, together with the fact that `Q ν m` is
`C^∞`.  The point of copying rather than importing is that the source module also contains a
number of unrelated uniform estimates which are still in flux.
-/

namespace Work.OddVolterra.Window

namespace Qaux

open MeasureTheory Set Filter
open scoped Topology ContDiff Interval
open Work.OddVolterra Work.OddVolterra.KernelExt


noncomputable section

/-! ## The jet encoding of the Bell recursion `Rnu`

`Rnu ν h init m (a,σ,t)` is the recursion `R_{m+1} = Z·∂_aR_m + (ν-m)·(∂_aZ)·R_m` with
`R_0 = init`, where `Z = Zrad h (·,σ,t)`: the formal recursion that produces the manifest Abel
numerators off the diagonal (`Rnu_spec`).  Since it only involves `∂_a` of `Z` and the `a`-jets of
`init`, its value is a *fixed* function of the finite jet

`(∂_a^0 Z, …, ∂_a^m Z, ∂_a^0 init, …, ∂_a^m init)`.

The point of the encoding below is that this function `Q ν m` is defined *without reference to
`h`*, so that bounds on `Rnu` follow from compactness of the set of jets, which is what makes the
constants uniform in `h`.  The identity `Rnu = Q ∘ J` is proved by a formal induction and uses no
positivity of `Z`. -/

/-- The radicand section `a ↦ Zrad h (a,σ,t)`. -/
def Zsec (h : ℝ → ℝ) (σ t : ℝ) : ℝ → ℝ := fun a => KernelExt.Zrad h (a, σ, t)

/-- The `a`-jet of `(Z, init)`, indexed by `(j, false)` for `Z` and `(j, true)` for `init`. -/
def Jjet (h : ℝ → ℝ) (init : ℝ × ℝ × ℝ → ℝ) (σ t : ℝ) (m : ℕ) (a : ℝ) :
    (Fin (m + 1) × Bool → ℝ) :=
  fun p => if p.2 then iteratedDeriv p.1.1 (fun x => init (x, σ, t)) a
           else iteratedDeriv p.1.1 (Zsec h σ t) a

/-- Restriction of a jet by one level. -/
def jrest {m : ℕ} (u : Fin (m + 2) × Bool → ℝ) : Fin (m + 1) × Bool → ℝ :=
  fun p => u (p.1.castSucc, p.2)

/-- Shift of a jet by one level. -/
def jshift {m : ℕ} (u : Fin (m + 2) × Bool → ℝ) : Fin (m + 1) × Bool → ℝ :=
  fun p => u (p.1.succ, p.2)

/-- **The jet-level recursion.**  `Q ν m` is the value of the Bell recursion `Rnu ν · m` as a
function of the jet. -/
noncomputable def Q (ν : ℝ) : (m : ℕ) → (Fin (m + 1) × Bool → ℝ) → ℝ
  | 0 => fun u => u (0, true)
  | (m + 1) => fun u =>
      u (0, false) * fderiv ℝ (Q ν m) (jrest u) (jshift u)
        + (ν - (m : ℝ)) * u (1, false) * Q ν m (jrest u)

@[simp] lemma Q_zero (ν : ℝ) (u : Fin 1 × Bool → ℝ) : Q ν 0 u = u (0, true) := rfl

lemma Q_succ (ν : ℝ) (m : ℕ) (u : Fin (m + 2) × Bool → ℝ) :
    Q ν (m + 1) u = u (0, false) * fderiv ℝ (Q ν m) (jrest u) (jshift u)
      + (ν - (m : ℝ)) * u (1, false) * Q ν m (jrest u) := rfl

lemma contDiff_jrest {m : ℕ} : ContDiff ℝ (⊤ : ℕ∞) (jrest (m := m)) := by
  rw [contDiff_pi]
  intro p
  exact (contDiff_apply ℝ ℝ (p.1.castSucc, p.2))

lemma contDiff_jshift {m : ℕ} : ContDiff ℝ (⊤ : ℕ∞) (jshift (m := m)) := by
  rw [contDiff_pi]
  intro p
  exact (contDiff_apply ℝ ℝ (p.1.succ, p.2))

/-- `Q ν m` is smooth. -/
theorem contDiff_Q (ν : ℝ) (m : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (Q ν m) := by
  induction m with
  | zero => exact contDiff_apply ℝ ℝ (0, true)
  | succ m ih =>
    have hfun : Q ν (m + 1) = fun u : Fin (m + 2) × Bool → ℝ =>
        u (0, false) * fderiv ℝ (Q ν m) (jrest u) (jshift u)
          + (ν - (m : ℝ)) * u (1, false) * Q ν m (jrest u) := by
      funext u; rw [Q_succ]
    rw [hfun]
    refine ContDiff.add (ContDiff.mul (contDiff_apply ℝ ℝ (0, false)) ?_)
      (ContDiff.mul (ContDiff.mul contDiff_const (contDiff_apply ℝ ℝ (1, false))) ?_)
    · have h1 : ContDiff ℝ (⊤ : ℕ∞)
          (fun p : (Fin (m + 1) × Bool → ℝ) × (Fin (m + 1) × Bool → ℝ) =>
            fderiv ℝ (Q ν m) p.1 p.2) :=
        ih.contDiff_fderiv_apply (by simp)
      exact h1.comp (contDiff_jrest.prodMk contDiff_jshift)
    · exact ih.comp contDiff_jrest

/-- Unfolding lemmas for the jet. -/
@[simp] lemma Jjet_false (h : ℝ → ℝ) (init : ℝ × ℝ × ℝ → ℝ) (σ t a : ℝ) (m : ℕ)
    (j : Fin (m + 1)) :
    Jjet h init σ t m a (j, false) = iteratedDeriv j.1 (Zsec h σ t) a := rfl

@[simp] lemma Jjet_true (h : ℝ → ℝ) (init : ℝ × ℝ × ℝ → ℝ) (σ t a : ℝ) (m : ℕ)
    (j : Fin (m + 1)) :
    Jjet h init σ t m a (j, true) = iteratedDeriv j.1 (fun x => init (x, σ, t)) a := rfl

@[simp] lemma jrest_apply {m : ℕ} (u : Fin (m + 2) × Bool → ℝ) (j : Fin (m + 1)) (b : Bool) :
    jrest u (j, b) = u (j.castSucc, b) := rfl

@[simp] lemma jshift_apply {m : ℕ} (u : Fin (m + 2) × Bool → ℝ) (j : Fin (m + 1)) (b : Bool) :
    jshift u (j, b) = u (j.succ, b) := rfl

lemma jrest_Jjet (h : ℝ → ℝ) (init : ℝ × ℝ × ℝ → ℝ) (σ t a : ℝ) (m : ℕ) :
    jrest (Jjet h init σ t (m + 1) a) = Jjet h init σ t m a := by
  funext p
  obtain ⟨j, b⟩ := p
  cases b <;> simp

/-- The radicand section is smooth. -/
lemma contDiff_Zsec {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (Zsec h σ t) :=
  (KernelExt.Zrad_contDiff_aux hh).comp (by fun_prop)

/-- The `a`-jet of the radicand is smooth in `a`. -/
lemma contDiff_Zsec_jet {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h) (σ t : ℝ) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv j (Zsec h σ t)) := by
  have h := (contDiff_Zsec hh σ t).iterate_deriv j
  simpa only [iteratedDeriv_eq_iterate] using h

/-- The `a`-jet of the initial datum is smooth in `a`. -/
lemma contDiff_Isec_jet {init : ℝ × ℝ × ℝ → ℝ} (hinit : ContDiff ℝ (⊤ : ℕ∞) init)
    (σ t : ℝ) (j : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv j (fun x : ℝ => init (x, σ, t))) := by
  have h0 : ContDiff ℝ (⊤ : ℕ∞) (fun x : ℝ => init (x, σ, t)) :=
    hinit.comp (by fun_prop)
  have h := h0.iterate_deriv j
  simpa only [iteratedDeriv_eq_iterate] using h

/-- The jet curve `a ↦ Jjet h init σ t m a` is smooth. -/
lemma contDiff_Jjet {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {init : ℝ × ℝ × ℝ → ℝ} (hinit : ContDiff ℝ (⊤ : ℕ∞) init) (σ t : ℝ) (m : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun a : ℝ => Jjet h init σ t m a) := by
  rw [contDiff_pi]
  intro p
  obtain ⟨j, b⟩ := p
  cases b
  · simpa using contDiff_Zsec_jet hh σ t j.1
  · simpa using contDiff_Isec_jet hinit σ t j.1

/-- The pointwise `a`-derivative of the jet is the shifted jet. -/
lemma deriv_Jjet_apply {h : ℝ → ℝ} (_hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {init : ℝ × ℝ × ℝ → ℝ} (_hinit : ContDiff ℝ (⊤ : ℕ∞) init) (σ t : ℝ) (m : ℕ) (a : ℝ)
    (j : Fin (m + 1)) (b : Bool) :
    deriv (fun a' : ℝ => Jjet h init σ t m a' (j, b)) a
      = Jjet h init σ t (m + 1) a (j.succ, b) := by
  cases b
  · simp only [Jjet_false]
    have h := congrFun (iteratedDeriv_succ (n := j.1) (f := Zsec h σ t)).symm a
    rw [Fin.val_succ]
    simpa using h
  · simp only [Jjet_true]
    have h := congrFun (iteratedDeriv_succ (n := j.1)
      (f := fun x : ℝ => init (x, σ, t))).symm a
    rw [Fin.val_succ]
    simpa using h

/-- **The `a`-derivative of the jet is the shifted jet.** -/
lemma deriv_Jjet {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {init : ℝ × ℝ × ℝ → ℝ} (hinit : ContDiff ℝ (⊤ : ℕ∞) init) (σ t : ℝ) (m : ℕ) (a : ℝ) :
    deriv (fun a' : ℝ => Jjet h init σ t m a') a = jshift (Jjet h init σ t (m + 1) a) := by
  rw [deriv_pi]
  · funext p
    obtain ⟨j, b⟩ := p
    rw [jshift_apply]
    exact deriv_Jjet_apply hh hinit σ t m a j b
  · intro p
    have hd : DifferentiableAt ℝ (fun a' : ℝ => Jjet h init σ t m a') a :=
      ((contDiff_Jjet hh hinit σ t m).differentiable (by simp)).differentiableAt
    obtain ⟨j, b⟩ := p
    exact (differentiableAt_pi.mp hd) (j, b)

/-- **The central identity:** the Bell recursion `Rnu` is `Q` composed with the jet. -/
theorem Rnu_eq_Q (ν : ℝ) {h : ℝ → ℝ} (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    {init : ℝ × ℝ × ℝ → ℝ} (hinit : ContDiff ℝ (⊤ : ℕ∞) init) (m : ℕ) :
    ∀ a σ t : ℝ, KernelExt.Rnu ν h init m (a, σ, t) = Q ν m (Jjet h init σ t m a) := by
  induction m with
  | zero =>
    intro a σ t
    have h1 : KernelExt.Rnu ν h init 0 (a, σ, t) = init (a, σ, t) := rfl
    rw [h1, Q_zero, Jjet_true]
    simp
  | succ m ih =>
    intro a σ t
    have hdiff : DifferentiableAt ℝ (KernelExt.Rnu ν h init m) (a, σ, t) :=
      (((KernelExt.Rnu_contDiff_aux ν hh hinit m).contDiffAt).differentiableAt (by simp))
    have hZdiff : DifferentiableAt ℝ (KernelExt.Zrad h) (a, σ, t) :=
      ((KernelExt.Zrad_contDiff_aux hh).contDiffAt).differentiableAt (by simp)
    have hsect := KernelExt.hasDerivAt_section (p := (a, σ, t)) hdiff
    have hZsec := KernelExt.hasDerivAt_section (p := (a, σ, t)) hZdiff
    have hsec : (fun u : ℝ => KernelExt.Rnu ν h init m (u, σ, t))
        = fun u : ℝ => Q ν m (Jjet h init σ t m u) := by
      funext u; exact ih u σ t
    have hchain : deriv (fun u : ℝ => Q ν m (Jjet h init σ t m u)) a
        = fderiv ℝ (Q ν m) (Jjet h init σ t m a) (jshift (Jjet h init σ t (m + 1) a)) := by
      have hJ : HasDerivAt (fun u : ℝ => Jjet h init σ t m u)
          (jshift (Jjet h init σ t (m + 1) a)) a := by
        rw [← deriv_Jjet hh hinit σ t m a]
        exact ((contDiff_Jjet hh hinit σ t m).differentiable (by simp)).differentiableAt.hasDerivAt
      have hQ : HasFDerivAt (Q ν m) ((fderiv ℝ (Q ν m)) (Jjet h init σ t m a))
          (Jjet h init σ t m a) :=
        (((contDiff_Q ν m).differentiable (by simp)).differentiableAt).hasFDerivAt
      exact (hQ.comp_hasDerivAt a hJ).deriv
    have hZ0 : KernelExt.Zrad h (a, σ, t) = Jjet h init σ t (m + 1) a (0, false) := by
      simp [Jjet, Zsec]
    have hZ1 : (fderiv ℝ (KernelExt.Zrad h) (a, σ, t)) (1, 0, 0)
        = Jjet h init σ t (m + 1) a (1, false) := by
      rw [← hZsec.deriv]
      simp only [Jjet_false, Fin.val_one]
      change deriv (Zsec h σ t) a = iteratedDeriv 1 (Zsec h σ t) a
      rw [iteratedDeriv_one]
    have hRm : KernelExt.Rnu ν h init m (a, σ, t)
        = Q ν m (jrest (Jjet h init σ t (m + 1) a)) := by
      rw [ih a σ t, jrest_Jjet]
    rw [KernelExt.Rnu]
    dsimp only
    rw [← hsect.deriv, hsec, hchain, hZ0, hZ1, hRm, Q_succ, jrest_Jjet]


end

end Qaux

end Work.OddVolterra.Window
