import Mathlib
import Submission.Work.ODE.CompactSupportBounds
import Submission.Work.ODE.GlobalFlow
import Submission.Work.ODE.SmoothFlow

set_option autoImplicit false

/-!
# The flow map of a smooth compactly supported vector field

We prove that the time-one map of a smooth compactly supported vector field on `ℝ^m` is a smooth
injective map with injective derivative, fixing the zeros of the field, and moving every point by
at most `sup ‖X‖`.
-/

open scoped Topology ContDiff NNReal
open Set Function

namespace Work.Whitney

variable {m : ℕ}

/-- Two integral curves of the same time-independent Lipschitz field which agree at one time agree
everywhere. -/
lemma integralCurve_eq_of_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {X : E → E} {L : NNReal} (hL : LipschitzWith L X) {γ₁ γ₂ : ℝ → E}
    (h₁ : IsIntegralCurve γ₁ (fun _ z => X z)) (h₂ : IsIntegralCurve γ₂ (fun _ z => X z))
    {t : ℝ} (h : γ₁ t = γ₂ t) : γ₁ = γ₂ :=
  ODE_solution_unique_univ (E := E) (v := fun _ z => X z) (s := fun _ => univ) (K := L) (t₀ := t)
    (fun _ => hL.lipschitzOnWith) (fun s => ⟨h₁ s, mem_univ _⟩) (fun s => ⟨h₂ s, mem_univ _⟩) h

/-- The `k`-fold iterate of a smooth self-map is smooth. -/
lemma contDiff_iterate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ℕ) {f : E → E}
    (hf : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f^[k] := by
  induction k with
  | zero => simpa using contDiff_id (𝕜 := ℝ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞)) (E := E)
  | succ k ih => rw [Function.iterate_succ]; exact ih.comp hf

theorem exists_flow_map_of_compactSupport {m : ℕ}
    (X : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m))
    (hX : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) X) (hc : HasCompactSupport X) :
    ∃ (Φ : EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m)) (M : ℝ),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ ∧ Function.Injective Φ ∧
      (∀ y, Function.Injective (fderiv ℝ Φ y)) ∧
      (∀ y, X y = 0 → Φ y = y) ∧
      (∀ y, ∃ γ : ℝ → EuclideanSpace ℝ (Fin m),
        γ 0 = y ∧ IsIntegralCurve γ (fun _ z => X z) ∧ γ 1 = Φ y) ∧
      (∀ z, ‖X z‖ ≤ M) ∧ (∀ y, ‖Φ y - y‖ ≤ M) := by
  classical
  have hX1 : ContDiff ℝ 1 X := hX.of_le (by norm_num)
  obtain ⟨L, hL⟩ := Work.ODE.exists_lipschitzWith_of_contDiff_hasCompactSupport hX1 hc
  obtain ⟨M, hM0, hMb⟩ := Work.ODE.exists_norm_le_of_hasCompactSupport hX.continuous hc
  have hfdc : Continuous (fderiv ℝ X) := hX.continuous_fderiv (by norm_num)
  have hfcs : HasCompactSupport (fderiv ℝ X) := hc.fderiv (𝕜 := ℝ)
  obtain ⟨K, hK0, hKb⟩ := Work.ODE.exists_norm_le_of_hasCompactSupport hfdc hfcs
  -- the global flow function
  have hglob : ∀ y, ∃ γ : ℝ → EuclideanSpace ℝ (Fin m),
      γ 0 = y ∧ IsIntegralCurve γ (fun _ z => X z) :=
    fun y => Work.ODE.exists_isIntegralCurve_of_lipschitzWith X hL hMb y
  let Φf : ℝ → EuclideanSpace ℝ (Fin m) → EuclideanSpace ℝ (Fin m) :=
    fun t y => (Classical.choose (hglob y)) t
  have hΦ0 : ∀ y, Φf 0 y = y := fun y => (Classical.choose_spec (hglob y)).1
  have hΦcurve : ∀ y, IsIntegralCurve (Classical.choose (hglob y)) (fun _ z => X z) :=
    fun y => (Classical.choose_spec (hglob y)).2
  have hΦ : ∀ t y, ∃ γ : ℝ → EuclideanSpace ℝ (Fin m),
      γ 0 = y ∧ IsIntegralCurve γ (fun _ z => X z) ∧ γ t = Φf t y :=
    fun t y => ⟨Classical.choose (hglob y), hΦ0 y, hΦcurve y, rfl⟩
  obtain ⟨δ, hδpos, hδsmooth⟩ := Work.ODE.contDiff_flow_timeSlice X hX M K hMb hKb Φf hΦ
  -- the semigroup property
  have hsem : ∀ (a b : ℝ) (y : EuclideanSpace ℝ (Fin m)), Φf (a + b) y = Φf a (Φf b y) := by
    intro a b y
    have h1 : IsIntegralCurve (fun s : ℝ => Φf (s + b) y) (fun _ z => X z) := by
      have h := (hΦcurve y).comp_add b
      simpa [Function.comp_def, Φf, add_comm] using h
    have h2 : IsIntegralCurve (fun s : ℝ => Φf s (Φf b y)) (fun _ z => X z) :=
      hΦcurve (Φf b y)
    have heq : (fun s : ℝ => Φf (s + b) y) 0 = (fun s : ℝ => Φf s (Φf b y)) 0 := by
      simp [hΦ0]
    have huniq := integralCurve_eq_of_eq (L := L) hL h1 h2 heq
    exact congrFun huniq a
  -- iterating the semigroup
  have hiter : ∀ (n : ℕ) (s : ℝ) (y : EuclideanSpace ℝ (Fin m)),
      Φf ((n : ℝ) * s) y = (Φf s)^[n] y := by
    intro n
    induction n with
    | zero => intro s y; simpa using hΦ0 y
    | succ n ih =>
      intro s y
      rw [Nat.cast_succ, add_mul, one_mul, hsem, ih, Function.iterate_succ_apply]
  have hiter' : ∀ (k : ℕ) (t : ℝ) (y : EuclideanSpace ℝ (Fin m)),
      Φf (((k : ℝ) + 1) * t) y = (Φf t)^[k + 1] y := by
    intro k t y
    have hc : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
    rw [hc, hiter]
  -- a uniform small step
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδpos
  have hNpos : 0 < n + 1 := Nat.succ_pos n
  have hNδ : (1 : ℝ) / ((n : ℝ) + 1) < δ := hn
  have hstep : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φf ((1 : ℝ) / ((n : ℝ) + 1))) :=
    hδsmooth _ (by rw [abs_of_pos (by positivity)]; exact le_of_lt hNδ)
  have hstepneg : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Φf (-((1 : ℝ) / ((n : ℝ) + 1)))) :=
    hδsmooth _ (by rw [abs_neg, abs_of_pos (by positivity)]; exact le_of_lt hNδ)
  have hpow : ∀ y : EuclideanSpace ℝ (Fin m),
      Φf 1 y = (Φf ((1 : ℝ) / ((n : ℝ) + 1)))^[n + 1] y := by
    intro y
    have h1 : ((n : ℝ) + 1) * ((1 : ℝ) / ((n : ℝ) + 1)) = 1 := by
      field_simp
    have h2 : Φf 1 y = Φf (((n : ℝ) + 1) * ((1 : ℝ) / ((n : ℝ) + 1))) y := by rw [h1]
    rw [h2, hiter' ]
  have hpowneg : ∀ y : EuclideanSpace ℝ (Fin m),
      Φf (-1) y = (Φf (-((1 : ℝ) / ((n : ℝ) + 1))))^[n + 1] y := by
    intro y
    have h1 : ((n : ℝ) + 1) * (-((1 : ℝ) / ((n : ℝ) + 1))) = -1 := by
      field_simp
    have h2 : Φf (-1) y = Φf (((n : ℝ) + 1) * (-((1 : ℝ) / ((n : ℝ) + 1)))) y := by rw [h1]
    rw [h2, hiter']
  have hΦ1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => Φf 1 y) := by
    have : (fun y : EuclideanSpace ℝ (Fin m) => Φf 1 y)
        = (Φf ((1 : ℝ) / ((n : ℝ) + 1)))^[n + 1] := funext hpow
    rw [this]
    exact contDiff_iterate (n + 1) hstep
  have hΦneg1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y => Φf (-1) y) := by
    have : (fun y : EuclideanSpace ℝ (Fin m) => Φf (-1) y)
        = (Φf (-((1 : ℝ) / ((n : ℝ) + 1))))^[n + 1] := funext hpowneg
    rw [this]
    exact contDiff_iterate (n + 1) hstepneg
  -- injectivity
  have hleft : Function.LeftInverse (fun y => Φf (-1) y) (fun y => Φf 1 y) := by
    intro y
    have h := hsem (-1) 1 y
    rw [show (-1 : ℝ) + 1 = 0 by norm_num, hΦ0 y] at h
    exact h.symm
  have hright : Function.RightInverse (fun y => Φf (-1) y) (fun y => Φf 1 y) := by
    intro y
    have h := hsem 1 (-1) y
    rw [show (1 : ℝ) + -1 = 0 by norm_num, hΦ0 y] at h
    exact h.symm
  have hinj : Function.Injective (fun y => Φf 1 y) := hleft.injective
  -- injectivity of the derivative
  have hderiv_inj : ∀ y, Function.Injective (fderiv ℝ (fun y => Φf 1 y) y) := by
    intro y
    have hker : ∀ v, (fderiv ℝ (fun y => Φf 1 y) y) v = 0 → v = 0 := by
      intro v hv
      have hcomp : (fun y : EuclideanSpace ℝ (Fin m) => Φf (-1) (Φf 1 y)) = id := funext hleft
      have hA : DifferentiableAt ℝ (fun y => Φf 1 y) y := (hΦ1.differentiable (by norm_num)) y
      have hB : DifferentiableAt ℝ (fun y => Φf (-1) y) (Φf 1 y) :=
        (hΦneg1.differentiable (by norm_num)) _
      have hchain : fderiv ℝ (fun y => Φf (-1) (Φf 1 y)) y
          = (fderiv ℝ (fun y => Φf (-1) y) (Φf 1 y)) ∘L (fderiv ℝ (fun y => Φf 1 y) y) :=
        fderiv_comp y hB hA
      have hBA : (fderiv ℝ (fun y => Φf (-1) y) (Φf 1 y)) ∘L (fderiv ℝ (fun y => Φf 1 y) y)
          = ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m)) := by
        rw [← hchain, hcomp]
        exact fderiv_id
      have h1 : ((fderiv ℝ (fun y => Φf (-1) y) (Φf 1 y)) ∘L
          (fderiv ℝ (fun y => Φf 1 y) y)) v = v := by
        rw [hBA]
        rfl
      rw [ContinuousLinearMap.comp_apply, hv, map_zero] at h1
      exact h1.symm
    intro a b hab
    refine sub_eq_zero.mp (hker (a - b) ?_)
    rw [map_sub, hab, sub_self]
  -- the zeros of `X` are fixed
  have hzero : ∀ y, X y = 0 → Φf 1 y = y := by
    intro y hy
    have hconst : IsIntegralCurve (fun _ : ℝ => y) (fun _ z => X z) :=
      isIntegralCurve_const (fun _ => hy)
    have heq : (fun _ : ℝ => y) 0 = (Classical.choose (hglob y)) 0 := by
      show y = Φf 0 y
      rw [hΦ0 y]
    have huniq := integralCurve_eq_of_eq (L := L) hL hconst (hΦcurve y) heq
    have h1 := congrFun huniq 1
    simp only [Φf] at h1 ⊢
    exact h1.symm
  -- the displacement bound
  have hbound : ∀ y, ‖Φf 1 y - y‖ ≤ M := by
    intro y
    have hderiv : ∀ s ∈ Set.uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => Φf s y) (X (Φf s y)) s := by
      intro s _
      simpa [Φf] using hΦcurve y s
    have hcont : Continuous (fun s : ℝ => X (Φf s y)) := by
      have hc1 : Continuous (fun s : ℝ => Φf s y) := by
        simpa [Φf] using (hΦcurve y).continuous
      exact hX.continuous.comp hc1
    have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (hcont.intervalIntegrable 0 1)
    have hnorm : ‖∫ s in (0 : ℝ)..1, X (Φf s y)‖ ≤ M := by
      have := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1) (C := M)
        (f := fun s => X (Φf s y)) (fun x _ => hMb (Φf x y))
      simpa using this
    calc ‖Φf 1 y - y‖ = ‖∫ s in (0 : ℝ)..1, X (Φf s y)‖ := by
          rw [hfund, hΦ0 y]
      _ ≤ M := hnorm
  exact ⟨fun y => Φf 1 y, M, hΦ1, hinj, hderiv_inj, hzero,
    (fun y => ⟨Classical.choose (hglob y), hΦ0 y, hΦcurve y, rfl⟩), hMb, hbound⟩

end Work.Whitney
