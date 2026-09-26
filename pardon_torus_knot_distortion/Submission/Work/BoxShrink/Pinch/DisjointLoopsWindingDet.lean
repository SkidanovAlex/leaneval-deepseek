import Mathlib
import Submission.Work.BoxShrink.Pinch.Trace
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.CoreTopology.Winding
import Submission.Work.TorusCover.ParamTorus_exists_liftOf
import Submission.Work.Smooth.SphereJordan.planeIndexGeom
import Submission.Work.Smooth.SphereJordan.loopIndex_eq_of_homotopy

/-!
# Two disjoint loops of a parametrised torus have proportional winding vectors

The winding vector of a closed curve of a parametrised torus `P` is the pair of integer multiples
of `2π` by which a lift of the curve to the parameter plane advances over one period
(`Work.SurgeryInvariance.windingOf`).  The determinant

`cross γ δ = (windingOf P γ).1 * (windingOf P δ).2 - (windingOf P γ).2 * (windingOf P δ).1`

is the *algebraic intersection number* of the two curves, computed from the intersection form of
the torus `ℚ²` (`Work.BoxShrink.Pinch.cross`).  The main theorem of this file,

`Work.BoxShrink.Pinch.DisjointLoopsWindingDet`,

says that this number vanishes for two *disjoint* loops: geometric intersection number zero forces
algebraic intersection number zero.  Equivalently: two loops of the torus with linearly independent
winding vectors cannot be disjoint, so all the components of the trace of a surface in the torus
(for instance of a cutting plane) lie in one line of `H₁(T²;ℚ)`.  This is ingredient (K0) of
Pardon's pinch (`Work.BoxShrink.Pinch.TraceLine`).

## The proof

Work in the parameter plane.  Let `F`, `G : ℝ → ℂ` be the two lifts (the two coordinates of
`LiftOf`, read as a complex number), so that

`F (s + 2π) = F s + 2π·u`,  `G (t + 2π) = G t + 2π·v`

with `u = a + b i`, `v = c + d i` the two winding vectors and `D = ad - bc ≠ 0` by assumption.
The hypothesis is that `F s - G t` avoids the lattice `2πℤ[i]` for all `s, t`.

The *difference map* `f (s + i t) = F s - G t` is equivariant with linear part `s u - t v`, and
`A ∘ f` with `A` the real-linear map normalised by `A u = 1`, `A v = -i` is a *bounded*
perturbation of the identity: `‖A (f z) - z‖ ≤ C` for all `z`, because `A ∘ F - id` and `A ∘ G + i·id`
are `2π`-periodic.  On the other hand `A ∘ f` never vanishes (as `A` is injective and `f` misses
the lattice, which contains `0`).

Now evaluate on the circle `z = R e^{2π i t}` for `R > C`.  On the one hand the loop
`t ↦ (A ∘ f) (R e^{2π i t})` is null-homotopic in `ℂ \ {0}` — it extends to the disc by shrinking
the radius — so its index about the origin is `0`.  On the other hand it is homotopic to the circle
`t ↦ R e^{2π i t}`, whose index is `1`, through the straight-line homotopy, which stays away from
`0` because `‖A (f z) - z‖ ≤ C < R` on the circle.  This contradiction proves `D = 0`.
-/

open Set
open Work.Smooth.SphereJordan

namespace Work.BoxShrink.Pinch

noncomputable section

open Classical

/-! ## Two elementary tools -/

/-- **A continuous `2π`-periodic complex-valued function is bounded.** -/
theorem exists_bound_of_periodic {f : ℝ → ℂ} (hf : Continuous f)
    (hp : Function.Periodic f (2 * Real.pi)) :
    ∃ C : ℝ, ∀ s : ℝ, ‖f s‖ ≤ C := by
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  obtain ⟨x₀, hx₀mem, hx₀max⟩ :=
    IsCompact.exists_isMaxOn isCompact_Icc ⟨0, by constructor <;> positivity⟩ hf.norm.continuousOn
  refine ⟨‖f x₀‖, fun s => ?_⟩
  set n : ℤ := ⌊s / (2 * Real.pi)⌋ with hn
  set r : ℝ := s - (n : ℝ) * (2 * Real.pi) with hr
  have hs : s = r + (n : ℝ) * (2 * Real.pi) := by rw [hr]; ring
  have hr0 : 0 ≤ r := by
    have h1 : (n : ℝ) ≤ s / (2 * Real.pi) := Int.floor_le (s / (2 * Real.pi))
    have h2 : (n : ℝ) * (2 * Real.pi) ≤ s := by
      rw [le_div_iff₀ h2π] at h1; linarith
    rw [hr]; linarith
  have hr2 : r < 2 * Real.pi := by
    have h1 : s / (2 * Real.pi) < (n : ℝ) + 1 := Int.lt_floor_add_one (s / (2 * Real.pi))
    have h2 : s < ((n : ℝ) + 1) * (2 * Real.pi) := by
      rw [div_lt_iff₀ h2π] at h1; linarith
    rw [hr]; nlinarith [h2]
  rw [hs, (hp.int_mul n) r]
  exact hx₀max ⟨hr0, hr2.le⟩

/-- **The normalising map.**  For real `a b c d D` with `ad - bc = D`, the real-linear map of `ℂ`
sending `a + bi ↦ 1` and `c + di ↦ -I`. -/
def linM (a b c d D : ℝ) (z : ℂ) : ℂ :=
  (((d * z.re - c * z.im) / D : ℝ) : ℂ)
    + ((((b * z.re - a * z.im) / D : ℝ) : ℂ)) * Complex.I

theorem linM_add (a b c d D : ℝ) (z w : ℂ) :
    linM a b c d D (z + w) = linM a b c d D z + linM a b c d D w := by
  simp only [linM, Complex.add_re, Complex.add_im]
  push_cast
  ring

theorem linM_neg (a b c d D : ℝ) (z : ℂ) :
    linM a b c d D (-z) = -linM a b c d D z := by
  simp only [linM, Complex.neg_re, Complex.neg_im]
  push_cast
  ring

theorem linM_sub (a b c d D : ℝ) (z w : ℂ) :
    linM a b c d D (z - w) = linM a b c d D z - linM a b c d D w := by
  simp only [linM, Complex.sub_re, Complex.sub_im]
  push_cast
  ring

theorem linM_smul (a b c d D : ℝ) (t : ℝ) (z : ℂ) :
    linM a b c d D ((t : ℂ) * z) = (t : ℂ) * linM a b c d D z := by
  simp only [linM, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  push_cast
  ring

theorem linM_zero (a b c d D : ℝ) : linM a b c d D 0 = 0 := by
  simp [linM]

theorem linM_cont (a b c d D : ℝ) : Continuous (linM a b c d D) := by
  unfold linM
  fun_prop

theorem linM_re (a b c d D : ℝ) (z : ℂ) : (linM a b c d D z).re = (d * z.re - c * z.im) / D := by
  simp [linM]

theorem linM_im (a b c d D : ℝ) (z : ℂ) : (linM a b c d D z).im = (b * z.re - a * z.im) / D := by
  simp [linM]

/-- `linM` is injective when `D ≠ 0`. -/
theorem linM_eq_zero_iff {a b c d D : ℝ} (hD : a * d - b * c = D) (hD0 : D ≠ 0) (z : ℂ) :
    linM a b c d D z = 0 ↔ z = 0 := by
  constructor
  · intro h
    have hre : (d * z.re - c * z.im) / D = 0 := by
      have := congrArg Complex.re h
      simpa [linM] using this
    have him : (b * z.re - a * z.im) / D = 0 := by
      have := congrArg Complex.im h
      simpa [linM] using this
    have h1 : d * z.re - c * z.im = 0 := (div_eq_zero_iff).mp hre |>.resolve_right hD0
    have h2 : b * z.re - a * z.im = 0 := (div_eq_zero_iff).mp him |>.resolve_right hD0
    have hx' : (a * d - b * c) * z.re = 0 := by linear_combination a * h1 - c * h2
    have hy' : (a * d - b * c) * z.im = 0 := by linear_combination b * h1 - d * h2
    rw [hD] at hx' hy'
    exact Complex.ext ((mul_eq_zero.mp hx').resolve_left hD0)
      ((mul_eq_zero.mp hy').resolve_left hD0)
  · rintro rfl; exact linM_zero a b c d D


/-- **Two disjoint closed curves of a parametrised torus have proportional winding vectors.** -/
theorem DisjointLoopsWindingDet (P : Work.CoreTopology.ParamTorus)
    (γ δ : Work.CoreTopology.ClosedCurve P)
    (hdisj : Disjoint (Set.range γ.γ) (Set.range δ.γ)) :
    (Work.SurgeryInvariance.windingOf P γ).1 * (Work.SurgeryInvariance.windingOf P δ).2 -
      (Work.SurgeryInvariance.windingOf P γ).2 * (Work.SurgeryInvariance.windingOf P δ).1 = 0 := by
  let Lγ : Work.CoreTopology.LiftOf P γ :=
    Classical.choice (Work.TorusCover.ParamTorus_exists_liftOf P γ)
  let Lδ : Work.CoreTopology.LiftOf P δ :=
    Classical.choice (Work.TorusCover.ParamTorus_exists_liftOf P δ)
  rw [Work.SurgeryInvariance.windingOf_eq P γ Lγ, Work.SurgeryInvariance.windingOf_eq P δ Lδ]
  let a : ℤ := Lγ.winding.1
  let b : ℤ := Lγ.winding.2
  let c : ℤ := Lδ.winding.1
  let d : ℤ := Lδ.winding.2
  change a * d - b * c = 0
  by_contra hne
  have hDc : (a : ℝ) * (d : ℝ) - (b : ℝ) * (c : ℝ) ≠ 0 := by
    intro h
    exact hne (by exact_mod_cast h)
  let Dc : ℝ := (a : ℝ) * (d : ℝ) - (b : ℝ) * (c : ℝ)
  have hDcne : Dc ≠ 0 := hDc
  let U : ℂ := (a : ℝ) + (b : ℝ) * Complex.I
  let V : ℂ := (c : ℝ) + (d : ℝ) * Complex.I
  -- the two lifted curves, as complex-valued functions
  let F : ℝ → ℂ := fun s => (Lγ.Θ s : ℂ) + (Lγ.Φ s : ℂ) * Complex.I
  let G : ℝ → ℂ := fun t => (Lδ.Θ t : ℂ) + (Lδ.Φ t : ℂ) * Complex.I
  have hFre : ∀ s : ℝ, (F s).re = Lγ.Θ s := fun s => by simp [F]
  have hFim : ∀ s : ℝ, (F s).im = Lγ.Φ s := fun s => by simp [F]
  have hGre : ∀ t : ℝ, (G t).re = Lδ.Θ t := fun t => by simp [G]
  have hGim : ∀ t : ℝ, (G t).im = Lδ.Φ t := fun t => by simp [G]
  have hFcont : Continuous F :=
    (Complex.continuous_ofReal.comp Lγ.contΘ).add
      ((Complex.continuous_ofReal.comp Lγ.contΦ).mul continuous_const)
  have hGcont : Continuous G :=
    (Complex.continuous_ofReal.comp Lδ.contΘ).add
      ((Complex.continuous_ofReal.comp Lδ.contΦ).mul continuous_const)
  -- periods
  have hFper : ∀ s : ℝ, F (s + 2 * Real.pi) = F s + ((2 * Real.pi : ℝ) : ℂ) * U := by
    intro s
    obtain ⟨h1, h2⟩ := Lγ.period_shift_winding s
    have h1a : Lγ.winding.1 = a := rfl
    have h2b : Lγ.winding.2 = b := rfl
    simp only [F, U, h1a, h2b] at h1 h2 ⊢
    rw [h1, h2]
    push_cast
    ring
  have hGper : ∀ t : ℝ, G (t + 2 * Real.pi) = G t + ((2 * Real.pi : ℝ) : ℂ) * V := by
    intro t
    obtain ⟨h1, h2⟩ := Lδ.period_shift_winding t
    have h1c : Lδ.winding.1 = c := rfl
    have h2d : Lδ.winding.2 = d := rfl
    simp only [G, V, h1c, h2d] at h1 h2 ⊢
    rw [h1, h2]
    push_cast
    ring
  -- the normalising map and the conjugated data
  let A : ℂ → ℂ := linM (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) Dc
  have hAcont : Continuous A := linM_cont _ _ _ _ _
  have hAadd : ∀ z w : ℂ, A (z + w) = A z + A w := fun z w => linM_add _ _ _ _ _ z w
  have hAsub : ∀ z w : ℂ, A (z - w) = A z - A w := fun z w => linM_sub _ _ _ _ _ z w
  have hAsmul : ∀ (t : ℝ) (z : ℂ), A ((t : ℂ) * z) = (t : ℂ) * A z :=
    fun t z => linM_smul _ _ _ _ _ t z
  have hAinj : ∀ z : ℂ, A z = 0 → z = 0 := fun z h =>
    (linM_eq_zero_iff (a := (a : ℝ)) (b := (b : ℝ)) (c := (c : ℝ)) (d := (d : ℝ)) (D := Dc)
      rfl hDcne z).mp h
  have hUre : U.re = (a : ℝ) := by simp [U]
  have hUim : U.im = (b : ℝ) := by simp [U]
  have hVre : V.re = (c : ℝ) := by simp [V]
  have hVim : V.im = (d : ℝ) := by simp [V]
  have hAU : A U = 1 := by
    have h1 : (A U).re = 1 := by
      rw [show A U = linM (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) Dc U from rfl, linM_re, hUre, hUim]
      rw [show (d : ℝ) * (a : ℝ) - (c : ℝ) * (b : ℝ) = Dc from by simp only [Dc]; ring]
      exact div_self hDcne
    have h2 : (A U).im = 0 := by
      rw [show A U = linM (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) Dc U from rfl, linM_im, hUre, hUim]
      rw [show (b : ℝ) * (a : ℝ) - (a : ℝ) * (b : ℝ) = 0 from by ring]
      simp
    exact Complex.ext (by rw [h1]; simp) (by rw [h2]; simp)
  have hAV : A V = -Complex.I := by
    have h1 : (A V).re = 0 := by
      rw [show A V = linM (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) Dc V from rfl, linM_re, hVre, hVim]
      rw [show (d : ℝ) * (c : ℝ) - (c : ℝ) * (d : ℝ) = 0 from by ring]
      simp
    have h2 : (A V).im = -1 := by
      rw [show A V = linM (a : ℝ) (b : ℝ) (c : ℝ) (d : ℝ) Dc V from rfl, linM_im, hVre, hVim]
      rw [show (b : ℝ) * (c : ℝ) - (a : ℝ) * (d : ℝ) = -Dc from by simp only [Dc]; ring]
      rw [neg_div, div_self hDcne]
    exact Complex.ext (by rw [h1]; simp) (by rw [h2]; simp)
  -- the conjugated curves
  let F' : ℝ → ℂ := fun s => A (F s)
  let G' : ℝ → ℂ := fun t => A (G t)
  have hF'per : ∀ s : ℝ, F' (s + 2 * Real.pi) = F' s + ((2 * Real.pi : ℝ) : ℂ) := by
    intro s
    have h : F' (s + 2 * Real.pi) = A (F s + ((2 * Real.pi : ℝ) : ℂ) * U) := by
      simp only [F', hFper s]
    rw [h, hAadd]
    have h2 : A (((2 * Real.pi : ℝ) : ℂ) * U) = ((2 * Real.pi : ℝ) : ℂ) := by
      rw [hAsmul (2 * Real.pi) U, hAU, mul_one]
    rw [h2, show F' s = A (F s) from rfl]
  have hG'per : ∀ t : ℝ, G' (t + 2 * Real.pi) = G' t - ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
    intro t
    have h : G' (t + 2 * Real.pi) = A (G t + ((2 * Real.pi : ℝ) : ℂ) * V) := by
      simp only [G', hGper t]
    rw [h, hAadd]
    have h2 : A (((2 * Real.pi : ℝ) : ℂ) * V) = -(((2 * Real.pi : ℝ) : ℂ)) * Complex.I := by
      rw [hAsmul (2 * Real.pi) V, hAV]
      ring
    rw [h2, show G' t = A (G t) from rfl]
    ring
  let Pc : ℝ → ℂ := fun s => F' s - (s : ℂ)
  let Qc : ℝ → ℂ := fun t => G' t + (t : ℂ) * Complex.I
  have hPcper : Function.Periodic Pc (2 * Real.pi) := by
    intro s
    have h := hF'per s
    simp only [Pc, h]
    push_cast
    ring
  have hQcper : Function.Periodic Qc (2 * Real.pi) := by
    intro t
    have h := hG'per t
    simp only [Qc, h]
    push_cast
    ring
  have hPccont : Continuous Pc := (hAcont.comp hFcont).sub Complex.continuous_ofReal
  have hQccont : Continuous Qc := (hAcont.comp hGcont).add
    (Complex.continuous_ofReal.mul continuous_const)
  obtain ⟨C₁, hC₁⟩ := exists_bound_of_periodic hPccont hPcper
  obtain ⟨C₂, hC₂⟩ := exists_bound_of_periodic hQccont hQcper
  let C : ℝ := C₁ + C₂
  -- the difference maps
  let f : ℂ → ℂ := fun z => F z.re - G z.im
  let f' : ℂ → ℂ := fun z => F' z.re - G' z.im
  have hf'eq : ∀ z : ℂ, f' z = A (f z) := by
    intro z
    simp only [f', f, F', G', hAsub]
  have hf'cont : Continuous f' :=
    ((hAcont.comp hFcont).comp Complex.continuous_re).sub
      ((hAcont.comp hGcont).comp Complex.continuous_im)
  have hbound : ∀ z : ℂ, ‖f' z - z‖ ≤ C := by
    intro z
    have hz : f' z - z = Pc z.re - Qc z.im := by
      have hzi : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := (Complex.re_add_im z).symm
      rw [hzi]
      simp only [f', Pc, Qc, Complex.add_re, Complex.ofReal_re, Complex.add_im,
        Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_one,
        mul_zero, sub_zero, add_zero]
      ring_nf
    rw [hz]
    calc ‖Pc z.re - Qc z.im‖ ≤ ‖Pc z.re‖ + ‖Qc z.im‖ := norm_sub_le _ _
      _ ≤ C := add_le_add (hC₁ _) (hC₂ _)
  -- disjointness, read on the lifts
  have hdisj' : ∀ s t : ℝ, γ.γ s ≠ δ.γ t := fun s t h =>
    Set.disjoint_left.mp hdisj (Set.mem_range_self s) (h.symm ▸ Set.mem_range_self t)
  have hpsi : ∀ s t : ℝ, P.psi (Lγ.Θ s) (Lγ.Φ s) ≠ P.psi (Lδ.Θ t) (Lδ.Φ t) := by
    intro s t h
    exact hdisj' s t (by rw [← Lγ.lifts s, ← Lδ.lifts t]; exact h)
  have hlat : ∀ s t : ℝ, ¬ (∃ k l : ℤ,
      F s - G t = ((k : ℝ) : ℂ) * (((2 * Real.pi : ℝ)) : ℂ)
        + ((l : ℝ) : ℂ) * (((2 * Real.pi : ℝ)) : ℂ) * Complex.I) := by
    intro s t ⟨k, l, hkl⟩
    have hcong : (∃ k : ℤ, Lγ.Θ s = Lδ.Θ t + k * (2 * Real.pi)) ∧
        (∃ l : ℤ, Lγ.Φ s = Lδ.Φ t + l * (2 * Real.pi)) := by
      constructor
      · refine ⟨k, ?_⟩
        have hre := congrArg Complex.re hkl
        simp only [F, G, Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.mul_im, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
          sub_zero, add_zero] at hre
        linarith
      · refine ⟨l, ?_⟩
        have him := congrArg Complex.im hkl
        simp only [F, G, Complex.sub_im, Complex.add_im, Complex.ofReal_re, Complex.mul_re,
          Complex.mul_im, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, mul_one,
          sub_zero, add_zero] at him
        linarith
    exact hpsi s t ((P.inj_mod (Lγ.Θ s) (Lγ.Φ s) (Lδ.Θ t) (Lδ.Φ t)).mpr hcong)
  have hf'ne : ∀ z : ℂ, f' z ≠ 0 := by
    intro z hz
    have h1 : A (f z) = 0 := by rw [← hf'eq z]; exact hz
    have h2 : f z = 0 := hAinj _ h1
    refine hlat z.re z.im ⟨0, 0, ?_⟩
    simpa [f] using h2
  -- the circle
  obtain ⟨R, hRpos, hRC⟩ : ∃ R : ℝ, 0 < R ∧ C < R :=
    ⟨|C| + 1, by positivity, by have h := le_abs_self C; linarith⟩
  let E : ℝ → ℂ := fun t => Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)
  have hEcont : Continuous E := by
    have h : E = fun t : ℝ => Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I) := rfl
    rw [h]; fun_prop
  have hE0 : E 0 = 1 := by
    show Complex.exp (((2 * Real.pi * 0 : ℝ) : ℂ) * Complex.I) = 1
    simp
  have hE1 : E 1 = 1 := by
    show Complex.exp (((2 * Real.pi * 1 : ℝ) : ℂ) * Complex.I) = 1
    rw [show ((2 * Real.pi * 1 : ℝ) : ℂ) = 2 * (Real.pi : ℂ) from by push_cast; ring]
    exact Complex.exp_two_pi_mul_I
  have hEnorm : ∀ t : ℝ, ‖E t‖ = 1 := fun t => Complex.norm_exp_ofReal_mul_I (2 * Real.pi * t)
  let c₁ : C(unitInterval, ℂ) := ⟨fun t => (R : ℂ) * E (t : ℝ),
    continuous_const.mul (hEcont.comp continuous_subtype_val)⟩
  let c₀ : C(unitInterval, ℂ) := ⟨fun t => f' ((R : ℂ) * E (t : ℝ)),
    hf'cont.comp (continuous_const.mul (hEcont.comp continuous_subtype_val))⟩
  have hc₁val : ∀ t : unitInterval, c₁ t = (R : ℂ) * E (t : ℝ) := fun t => rfl
  have hc₀val : ∀ t : unitInterval, c₀ t = f' ((R : ℂ) * E (t : ℝ)) := fun t => rfl
  have hc₁norm : ∀ t : unitInterval, ‖c₁ t‖ = R := by
    intro t
    rw [hc₁val t, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hRpos, hEnorm t,
      mul_one]
  have hc₁ne : ∀ t : unitInterval, c₁ t ≠ 0 := by
    intro t h
    have := hc₁norm t
    rw [h, norm_zero] at this
    linarith
  have hc₀ne : ∀ t : unitInterval, c₀ t ≠ 0 := fun t => hf'ne _
  have hc₁loop : c₁ 0 = c₁ 1 := by simp [c₁, hE0, hE1]
  have hc₀loop : c₀ 0 = c₀ 1 := by simp [c₀, hE0, hE1]
  -- the index of the circle is `1`
  have hc₁idx : loopIndex c₁ = 1 := by
    let Λ : C(unitInterval, ℂ) :=
      ⟨fun t => ((Real.log R : ℝ) : ℂ) + (((2 * Real.pi * (t : ℝ)) : ℝ) : ℂ) * Complex.I,
        by fun_prop⟩
    have hΛ : ∀ t : unitInterval, Complex.exp (Λ t) = c₁ t := by
      intro t
      show Complex.exp (((Real.log R : ℝ) : ℂ) + (((2 * Real.pi * (t : ℝ)) : ℝ) : ℂ) * Complex.I)
        = (R : ℂ) * E (t : ℝ)
      rw [Complex.exp_add, ← Complex.ofReal_exp, Real.exp_log hRpos]
    have hval : Λ 1 - Λ 0 = 2 * (Real.pi : ℂ) * Complex.I := by
      have h1 : Λ 1 = ((Real.log R : ℝ) : ℂ) + ((2 * Real.pi : ℝ) : ℂ) * Complex.I := by
        simp only [Λ, ContinuousMap.coe_mk]
        congr 1
        push_cast
        ring
      have h0 : Λ 0 = ((Real.log R : ℝ) : ℂ) := by
        simp [Λ]
      rw [h1, h0]
      push_cast
      ring
    have hspec := loopIndex_spec c₁ hc₁ne hc₁loop Λ hΛ
    rw [hval] at hspec
    have h3 : ((loopIndex c₁ : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)
        = 1 * (2 * (Real.pi : ℂ) * Complex.I) := by
      rw [hspec.symm, one_mul]
    have h4 : ((loopIndex c₁ : ℤ) : ℂ) = 1 :=
      mul_right_cancel₀ Work.Smooth.SphereJordan.two_pi_I_ne_zero h3
    exact_mod_cast h4
  -- the index of the conjugate loop is `0` (it is null-homotopic)
  have hc₀idx : loopIndex c₀ = 0 := by
    have hKne : ∀ t : unitInterval, (ContinuousMap.const unitInterval (f' 0)) t ≠ 0 :=
      fun _ => hf'ne 0
    have hKloop : (ContinuousMap.const unitInterval (f' 0)) 0
        = (ContinuousMap.const unitInterval (f' 0)) 1 := rfl
    have hHcont : Continuous fun p : unitInterval × unitInterval =>
        f' ((((1 - (p.2 : ℝ)) * R : ℝ) : ℂ) * E (p.1 : ℝ)) :=
      hf'cont.comp ((Complex.continuous_ofReal.comp
        ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
          (continuous_const : Continuous fun _ : unitInterval × unitInterval => R))).mul
        (hEcont.comp (continuous_subtype_val.comp continuous_fst)))
    let H : C(unitInterval × unitInterval, ℂ) :=
      ⟨fun p => f' ((((1 - (p.2 : ℝ)) * R : ℝ) : ℂ) * E (p.1 : ℝ)), hHcont⟩
    have hHval : ∀ p : unitInterval × unitInterval,
        H p = f' ((((1 - (p.2 : ℝ)) * R : ℝ) : ℂ) * E (p.1 : ℝ)) := fun p => rfl
    have hHne : ∀ p : unitInterval × unitInterval, H p ≠ 0 := fun p => hf'ne _
    have hH0 : ∀ t : unitInterval, H (t, 0) = c₀ t := by
      intro t
      rw [hHval (t, 0), hc₀val t,
        show ((0 : unitInterval) : ℝ) = 0 from rfl]
      congr 1
      push_cast
      ring
    have hH1 : ∀ t : unitInterval, H (t, 1) = (ContinuousMap.const unitInterval (f' 0)) t := by
      intro t
      rw [hHval (t, 1), show ((1 : unitInterval) : ℝ) = 1 from rfl]
      congr 1
      push_cast
      ring
    have hHloop : ∀ s : unitInterval, H (0, s) = H (1, s) := by
      intro s
      rw [hHval (0, s), hHval (1, s),
        show ((0 : unitInterval) : ℝ) = 0 from rfl,
        show ((1 : unitInterval) : ℝ) = 1 from rfl, hE0, hE1]
    rw [loopIndex_eq_of_homotopy hc₀ne hKne H hHne hH0 hH1 hHloop,
      loopIndex_const (f' 0) (hf'ne 0)]
  -- the two loops are homotopic through loops avoiding `0`
  have hcmp : loopIndex c₀ = loopIndex c₁ := by
    have hHcont : Continuous fun p : unitInterval × unitInterval =>
        (1 - ((p.2 : ℝ) : ℂ)) * c₀ p.1 + ((p.2 : ℝ) : ℂ) * c₁ p.1 :=
      ((continuous_const.sub (Complex.continuous_ofReal.comp
        (continuous_subtype_val.comp continuous_snd))).mul
        (c₀.continuous.comp continuous_fst)).add
        ((Complex.continuous_ofReal.comp (continuous_subtype_val.comp continuous_snd)).mul
          (c₁.continuous.comp continuous_fst))
    let H : C(unitInterval × unitInterval, ℂ) :=
      ⟨fun p => (1 - ((p.2 : ℝ) : ℂ)) * c₀ p.1 + ((p.2 : ℝ) : ℂ) * c₁ p.1, hHcont⟩
    have hHval : ∀ p : unitInterval × unitInterval,
        H p = (1 - ((p.2 : ℝ) : ℂ)) * c₀ p.1 + ((p.2 : ℝ) : ℂ) * c₁ p.1 := fun p => rfl
    have hHne : ∀ p : unitInterval × unitInterval, H p ≠ 0 := by
      intro p
      have h2 : ‖c₀ p.1 - c₁ p.1‖ ≤ C := by
        have hz := hbound ((R : ℂ) * E (p.1 : ℝ))
        rw [hc₀val p.1, hc₁val p.1]
        exact hz
      have hτ : (0 : ℝ) ≤ 1 - (p.2 : ℝ) := by have h := p.2.2.2; linarith
      intro hzero
      rw [hHval p] at hzero
      have hHp : (1 - ((p.2 : ℝ) : ℂ)) * c₀ p.1 + ((p.2 : ℝ) : ℂ) * c₁ p.1
          = c₁ p.1 + (1 - ((p.2 : ℝ) : ℂ)) * (c₀ p.1 - c₁ p.1) := by ring
      have haux : c₁ p.1 + (1 - ((p.2 : ℝ) : ℂ)) * (c₀ p.1 - c₁ p.1) = 0 := by
        rw [← hHp]; exact hzero
      have hkey : c₁ p.1 = -((1 - ((p.2 : ℝ) : ℂ)) * (c₀ p.1 - c₁ p.1)) :=
        eq_neg_of_add_eq_zero_left haux
      have hcoef : (1 : ℂ) - ((p.2 : ℝ) : ℂ) = ((1 - (p.2 : ℝ) : ℝ) : ℂ) := by
        push_cast; ring
      have hmain : ‖c₁ p.1‖ = ‖(1 - ((p.2 : ℝ) : ℂ)) * (c₀ p.1 - c₁ p.1)‖ := by
        conv_lhs => rw [hkey, norm_neg]
      have hle : ‖c₁ p.1‖ ≤ (1 - (p.2 : ℝ)) * ‖c₀ p.1 - c₁ p.1‖ := by
        calc ‖c₁ p.1‖ = ‖(1 - ((p.2 : ℝ) : ℂ)) * (c₀ p.1 - c₁ p.1)‖ := hmain
          _ = ‖(1 - ((p.2 : ℝ) : ℂ))‖ * ‖c₀ p.1 - c₁ p.1‖ := norm_mul _ _
          _ ≤ (1 - (p.2 : ℝ)) * ‖c₀ p.1 - c₁ p.1‖ := by
              rw [hcoef, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hτ]
      have h4 : (1 - (p.2 : ℝ)) * ‖c₀ p.1 - c₁ p.1‖ ≤ ‖c₀ p.1 - c₁ p.1‖ := by
        have hmul := mul_le_mul_of_nonneg_right
          (show (1 - (p.2 : ℝ)) ≤ 1 by have h := p.2.2.1; linarith)
          (norm_nonneg (c₀ p.1 - c₁ p.1))
        rwa [one_mul] at hmul
      have hfin : R ≤ C := by
        have h1 : ‖c₁ p.1‖ = R := hc₁norm p.1
        linarith
      linarith
    have hH0 : ∀ t : unitInterval, H (t, 0) = c₀ t := by
      intro t
      rw [hHval (t, 0), show ((0 : unitInterval) : ℝ) = 0 from rfl]
      push_cast
      ring
    have hH1 : ∀ t : unitInterval, H (t, 1) = c₁ t := by
      intro t
      rw [hHval (t, 1), show ((1 : unitInterval) : ℝ) = 1 from rfl]
      push_cast
      ring
    have hHloop : ∀ s : unitInterval, H (0, s) = H (1, s) := by
      intro s
      rw [hHval (0, s), hHval (1, s), hc₀loop, hc₁loop]
    exact loopIndex_eq_of_homotopy hc₀ne hc₁ne H hHne hH0 hH1 hHloop
  have h01 : (0 : ℤ) = 1 := by rw [← hc₀idx, hcmp, hc₁idx]
  exact absurd h01 (by norm_num)

end

end Work.BoxShrink.Pinch
