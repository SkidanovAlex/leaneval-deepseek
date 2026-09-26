import Mathlib
import Submission.Work.BoxShrink.PinchOff.IB.Defs
import Submission.Work.BoxShrink.PinchOff.IB.Pieces

/-!
# Loops with prescribed winding from paths in the parameter plane

A continuous map `Λ : ℝ → ℂ` which is *quasi-periodic*, `Λ (t + 2π) = Λ t + periodPt a b`, and
whose values lie in the preimage `X̃` of a region `X`, projects to a closed curve of the torus
contained in `X` with winding vector `(a, b)`.  Such a quasi-periodic map is produced from any
continuous path `c : ℝ → ℂ` from `p` to `p + periodPt a b` inside `X̃` by "straightening out" the
clamped path modulo the lattice:

`Λ t = F (t mod 2π) + (t / 2π) · periodPt a b`,  where `F` is the descent to `ℝ / 2πℤ` of
`u ↦ c (clamp u) - (u / 2π) · periodPt a b`, whose endpoints at `0` and `2π` agree.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- The `k`-fold multiple of a lattice vector is a lattice vector. -/
theorem periodPt_int_mul (k a b : ℤ) :
    periodPt (k * a) (k * b) = ((k : ℝ) : ℂ) * periodPt a b := by
  apply Complex.ext
  · simp only [periodPt_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    push_cast
    ring
  · simp only [periodPt_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      zero_add]
    push_cast
    ring

theorem periodPt_int_mul_mem (k a b : ℤ) : periodPt (k * a) (k * b) ∈ periodLattice :=
  ⟨(k * a, k * b), rfl⟩

/-- **A path from `p` to `p + periodPt a b` inside the preimage of `X` produces a loop of the
torus contained in `X` with winding vector `(a, b)`.** -/
theorem exists_closedCurve_of_path {P : Work.CoreTopology.ParamTorus} {X : Set R3}
    {a b : ℤ} {p : ℂ} (c : ℝ → ℂ) (hc : Continuous c) (h0 : c 0 = p)
    (h2 : c (2 * Real.pi) = p + periodPt a b)
    (hmem : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), c t ∈ Xtilde P X) :
    ∃ γ : Work.CoreTopology.ClosedCurve P, (∀ t, γ.γ t ∈ X) ∧
      Work.SurgeryInvariance.windingOf P γ = (a, b) := by
  classical
  have hπ : (0:ℝ) < 2 * Real.pi := by positivity
  haveI : Fact (0 < (2 * Real.pi : ℝ)) := ⟨hπ⟩
  set ν : ℂ := periodPt a b with hν
  -- the clamped, straightened path
  set f : ℝ → ℂ := fun u => c (Set.projIcc (0:ℝ) (2 * Real.pi) hπ.le u)
      - ((u / (2 * Real.pi) : ℝ) : ℂ) * ν with hfdef
  have hfcont : Continuous f := by
    rw [hfdef]
    refine Continuous.sub ?_ ?_
    · exact hc.comp (continuous_subtype_val.comp continuous_projIcc)
    · fun_prop
  have hf0 : f 0 = p := by
    have h : Set.projIcc (0:ℝ) (2 * Real.pi) hπ.le 0 = ⟨0, ⟨le_refl 0, hπ.le⟩⟩ := by
      apply Subtype.ext
      simp
    rw [hfdef]
    simp only
    rw [h, h0]
    simp
  have hf2 : f (2 * Real.pi) = p := by
    have h : Set.projIcc (0:ℝ) (2 * Real.pi) hπ.le (2 * Real.pi)
        = ⟨2 * Real.pi, ⟨hπ.le, le_refl _⟩⟩ := by
      apply Subtype.ext
      simp
    rw [hfdef]
    simp only
    rw [h, h2, hν]
    have hdiv : ((2 * Real.pi) / (2 * Real.pi) : ℝ) = 1 := by
      field_simp
    rw [hdiv]
    push_cast
    ring
  have hmatch : f 0 = f (2 * Real.pi) := by rw [hf0, hf2]
  -- the quasi-periodic lift
  set Λ : ℝ → ℂ := fun t =>
    AddCircle.liftIco (2 * Real.pi) 0 f (t : AddCircle (2 * Real.pi))
      + ((t / (2 * Real.pi) : ℝ) : ℂ) * ν with hΛdef
  have hΛcont : Continuous Λ := by
    have hF : Continuous (AddCircle.liftIco (2 * Real.pi) 0 f) :=
      AddCircle.liftIco_continuous (by simpa using hmatch) hfcont.continuousOn
    have hcoe : Continuous fun t : ℝ => (t : AddCircle (2 * Real.pi)) := by fun_prop
    have hstraight : Continuous fun t : ℝ => ((t / (2 * Real.pi) : ℝ) : ℂ) * ν := by fun_prop
    exact (hF.comp hcoe).add hstraight
  have hΛzero : Λ 0 = p := by
    rw [hΛdef]
    simp only
    rw [AddCircle.liftIco_zero_coe_apply (show (0:ℝ) ∈ Set.Ico 0 (2 * Real.pi) from
      ⟨le_refl 0, hπ⟩)]
    rw [show ((0:ℝ) / (2 * Real.pi) : ℝ) = 0 by simp, hf0]
    simp
  have hΛshift : ∀ t, Λ (t + 2 * Real.pi) = Λ t + ν := by
    intro t
    have hcoe : ((t + 2 * Real.pi : ℝ) : AddCircle (2 * Real.pi))
        = (t : AddCircle (2 * Real.pi)) := by
      rw [show (t + 2 * Real.pi : ℝ) = t + 2 * Real.pi by ring]
      exact AddCircle.coe_add_period (2 * Real.pi) t
    have hsplit : ((t + 2 * Real.pi) / (2 * Real.pi) : ℝ) = t / (2 * Real.pi) + 1 := by
      field_simp
    rw [hΛdef]
    simp only
    rw [hcoe, hsplit]
    push_cast
    ring
  /- the values of `Λ` on one period are those of the path -/
  have hΛon : ∀ t ∈ Set.Icc (0:ℝ) (2 * Real.pi), Λ t = c t := by
    intro t ht
    rcases lt_or_eq_of_le ht.2 with hlt | heq
    · rw [hΛdef]
      simp only
      rw [AddCircle.liftIco_zero_coe_apply (show t ∈ Set.Ico 0 (2 * Real.pi) from ⟨ht.1, hlt⟩)]
      rw [hfdef]
      simp only
      rw [Set.projIcc_of_mem hπ.le ht]
      ring
    · subst heq
      rw [show (2 * Real.pi) = 0 + 2 * Real.pi by ring, hΛshift 0, hΛzero, ← h2]
      ring
  -- the quasi-periodicity for integer multiples
  have hΛnat : ∀ (n : ℕ) (t : ℝ),
      Λ (t + (n : ℝ) * (2 * Real.pi)) = Λ t + ((n : ℝ) : ℂ) * ν := by
    intro n
    induction n with
    | zero => intro t; simp
    | succ n ih =>
        intro t
        rw [show t + (((n : ℕ) + 1 : ℕ) : ℝ) * (2 * Real.pi)
            = (t + (n : ℝ) * (2 * Real.pi)) + 2 * Real.pi by push_cast; ring]
        rw [hΛshift, ih]
        push_cast
        ring
  have hΛmul : ∀ (k : ℤ) (t : ℝ),
      Λ (t + (k : ℝ) * (2 * Real.pi)) = Λ t + ((k : ℝ) : ℂ) * ν := by
    intro k t
    rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
    · exact hΛnat n t
    · have h := hΛnat n (t - (n : ℝ) * (2 * Real.pi))
      rw [show t - (n : ℝ) * (2 * Real.pi) + (n : ℝ) * (2 * Real.pi) = t by ring] at h
      have h2 : Λ (t - (n : ℝ) * (2 * Real.pi)) = Λ t + ((-(n : ℝ)) : ℂ) * ν := by
        rw [h]
        ring
      rw [show t + ((-(n : ℤ) : ℤ) : ℝ) * (2 * Real.pi)
          = t - (n : ℝ) * (2 * Real.pi) by push_cast; ring]
      rw [h2]
      push_cast
      ring
  -- the closed curve
  refine ⟨{ γ := fun t => planePsi P (Λ t)
            cont := (continuous_planePsi P).comp hΛcont
            periodic := fun t => by
              show planePsi P (Λ (t + 2 * Real.pi)) = planePsi P (Λ t)
              rw [hΛshift t, hν, planePsi_add_periodPt]
            mem := fun t => planePsi_mem_carrier P (Λ t) }, ?_, ?_⟩
  · -- membership
    intro t
    show planePsi P (Λ t) ∈ X
    have hmem' : Λ t ∈ Xtilde P X := by
      obtain ⟨k, hk⟩ := exists_int_shift_mem_Ico t
      set t₀ : ℝ := t + (k : ℝ) * (2 * Real.pi) with ht₀
      have ht₀mem : t₀ ∈ Set.Ico (0:ℝ) (2 * Real.pi) := hk
      have ht_eq : t = t₀ - (k : ℝ) * (2 * Real.pi) := by rw [ht₀]; ring
      have hΛt : Λ t = Λ t₀ + ((-k : ℤ) : ℝ) * ν := by
        rw [ht_eq]
        rw [show t₀ - (k : ℝ) * (2 * Real.pi) = t₀ + ((-k : ℤ) : ℝ) * (2 * Real.pi) by
          push_cast; ring]
        exact hΛmul (-k) t₀
      have hw_mem : ((-k : ℤ) : ℝ) * ν ∈ periodLattice := by
        rw [hν, ← periodPt_int_mul (-k) a b]
        exact periodPt_int_mul_mem (-k) a b
      have hct : c t₀ ∈ Xtilde P X := hmem t₀ ⟨ht₀mem.1, ht₀mem.2.le⟩
      have h1 : Λ t₀ ∈ Xtilde P X := by rw [hΛon t₀ ⟨ht₀mem.1, ht₀mem.2.le⟩]; exact hct
      rw [hΛt]
      exact (Xtilde_add_periodLattice P X (Λ t₀) _ hw_mem).mpr h1
    exact hmem'
  · -- the winding vector
    have hLift : (⟨fun t => (Λ t).re, fun t => (Λ t).im,
        Complex.continuous_re.comp hΛcont, Complex.continuous_im.comp hΛcont,
        fun t => rfl⟩ : Work.CoreTopology.LiftOf P
          { γ := fun t => planePsi P (Λ t)
            cont := (continuous_planePsi P).comp hΛcont
            periodic := fun t => by
              show planePsi P (Λ (t + 2 * Real.pi)) = planePsi P (Λ t)
              rw [hΛshift t, hν, planePsi_add_periodPt]
            mem := fun t => planePsi_mem_carrier P (Λ t) }).winding = (a, b) := by
      set L : Work.CoreTopology.LiftOf P
          { γ := fun t => planePsi P (Λ t)
            cont := (continuous_planePsi P).comp hΛcont
            periodic := fun t => by
              show planePsi P (Λ (t + 2 * Real.pi)) = planePsi P (Λ t)
              rw [hΛshift t, hν, planePsi_add_periodPt]
            mem := fun t => planePsi_mem_carrier P (Λ t) } :=
        ⟨fun t => (Λ t).re, fun t => (Λ t).im,
          Complex.continuous_re.comp hΛcont, Complex.continuous_im.comp hΛcont,
          fun t => rfl⟩ with hL
      have hspec := L.winding_spec
      have hre : L.Θ (2 * Real.pi) = L.Θ 0 + (a : ℝ) * (2 * Real.pi) := by
        have h1 := congrArg Complex.re (hΛshift 0)
        simp only [hL, hν, Complex.add_re, periodPt_re, zero_add] at h1
        linarith [h1]
      have him : L.Φ (2 * Real.pi) = L.Φ 0 + (b : ℝ) * (2 * Real.pi) := by
        have h1 := congrArg Complex.im (hΛshift 0)
        simp only [hL, hν, Complex.add_im, periodPt_im, zero_add] at h1
        linarith [h1]
      have h2π : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      have hfst : (L.winding).1 = a := by
        have h : ((L.winding).1 : ℝ) * (2 * Real.pi) = (a : ℝ) * (2 * Real.pi) := by
          linarith [hspec.1, hre]
        exact_mod_cast mul_right_cancel₀ h2π h
      have hsnd : (L.winding).2 = b := by
        have h : ((L.winding).2 : ℝ) * (2 * Real.pi) = (b : ℝ) * (2 * Real.pi) := by
          linarith [hspec.2, him]
        exact_mod_cast mul_right_cancel₀ h2π h
      exact Prod.ext hfst hsnd
    rw [Work.SurgeryInvariance.windingOf_eq P _ _]
    exact hLift

end

end Work.BoxShrink.PinchOff
