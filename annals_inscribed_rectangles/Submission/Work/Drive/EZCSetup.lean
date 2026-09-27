import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Drive.boxParity

/-!
# Setup for `even_zero_count_homotopy`

This file sets up the objects used in the proof of `Work.Drive.even_zero_count_homotopy`.

The strategy: given `F : ℝ × 𝔼^n → 𝔼^n` smooth with no zeros on the side `[0,1] × ∂[0,1]ⁿ`
and with `0` a regular value of the partial maps at `t = 0` and `t = 1`, we perturb `F` by a
function of the form `t ↦ (t*(1-t)) • u`:

* `ezG F u z = F (t, x) - (t*(1-t)) • u` where `z = (t,x)`,

so that the perturbed map agrees with `F` at `t = 0` and `t = 1` (the zero sets there are
*unchanged*), and we choose `u` small so that the perturbed map is still non-zero on the side.

The choice of `u` is a Baire genericity argument: for every fixed `t`, the set of "bad" `u`, namely
those for which `t*(1-t) • u` is the value at some point of the box where the *partial* derivative
`fderiv ℝ (fun y => F (t,y)) x` is singular, is a closed null set (`ezBad`); by Baire there is a
small `u` outside all of them for a countable dense set of `t`, and by closedness (compactness of
the set of bad `(t,x)`) this propagates to all `t ∈ [0,1]`.

## Contents

* `ezBox`, `ezToProd`, `ezOfProd`: the box `[0,1]ⁿ` and the identification `𝔼^{n+1} ≅ ℝ × 𝔼ⁿ`;
* `sard_partial_crit_eq_zero`: for every `t`, the singular values of the partial map
  `x ↦ F (t,x)` on the box form a null set (Mathlib's equal-dimension Sard);
* `det_ne_zero_surjective`, `det_eq_zero_of_not_surjective`: the equivalence between non-vanishing
  determinant and surjectivity for the partial derivative;
* `partial_fderiv_apply`: `fderiv ℝ F (t,x) (0,v) = fderiv ℝ (fun y => F (t,y)) x v`;
* `ezBad`: the set of bad perturbation values at a fixed time `t`.
-/

namespace Work.Drive

open scoped ContDiff Topology
open Set MeasureTheory

noncomputable section

/-- The closed unit box `[0,1]^n` in `𝔼^n`. -/
def ezBox (n : ℕ) : Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/-- The identification `𝔼^{n+1} → ℝ × 𝔼^n`, `z ↦ (z 0, (z 1, …, z n))`, as a continuous linear
map. -/
def ezToProd (n : ℕ) : EuclideanSpace ℝ (Fin (n+1)) →L[ℝ] (ℝ × EuclideanSpace ℝ (Fin n)) :=
  (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin (n+1))).prod
    (((EuclideanSpace.equiv (Fin n) ℝ).symm).toContinuousLinearMap ∘L
      ContinuousLinearMap.pi (fun i : Fin n => EuclideanSpace.proj (𝕜 := ℝ) (i.succ)))

/-- The inverse identification `ℝ × 𝔼^n → 𝔼^{n+1}`. -/
def ezOfProd (n : ℕ) (p : ℝ × EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n+1)) :=
  WithLp.toLp 2 (Fin.cons p.1 p.2.ofLp)

@[simp] theorem ezToProd_snd (n : ℕ) (z : EuclideanSpace ℝ (Fin (n+1))) :
    ezToProd n z = (z 0, WithLp.toLp 2 (fun i : Fin n => z i.succ)) := rfl

theorem ezToProd_snd_apply (n : ℕ) (z : EuclideanSpace ℝ (Fin (n+1))) (i : Fin n) :
    (ezToProd n z).2 i = z i.succ := by
  simp [ezToProd]

@[simp] theorem ezToProd_fst (n : ℕ) (z : EuclideanSpace ℝ (Fin (n+1))) :
    (ezToProd n z).1 = z 0 := rfl

theorem ezOfProd_fst (n : ℕ) (p : ℝ × EuclideanSpace ℝ (Fin n)) : (ezOfProd n p) 0 = p.1 := by
  simp [ezOfProd]

theorem ezOfProd_snd (n : ℕ) (p : ℝ × EuclideanSpace ℝ (Fin n)) (i : Fin n) :
    (ezOfProd n p) i.succ = p.2 i := by
  simp [ezOfProd]

theorem ezToProd_ofProd (n : ℕ) (p : ℝ × EuclideanSpace ℝ (Fin n)) :
    ezToProd n (ezOfProd n p) = p := by
  rw [ezToProd_snd]
  refine Prod.ext ?_ ?_
  · simp [ezOfProd]
  · congr 1

theorem ezOfProd_toProd (n : ℕ) (z : EuclideanSpace ℝ (Fin (n+1))) :
    ezOfProd n (ezToProd n z) = z := by
  rw [ezToProd_snd]
  simp only [ezOfProd]
  congr 1
  ext i
  rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, h⟩
  · subst h; simp
  · subst h
    simp only [Fin.cons_succ]

theorem mem_unitBox_iff (n : ℕ) (z : EuclideanSpace ℝ (Fin (n+1))) :
    z ∈ Submission.Drive.unitBox n ↔
      z 0 ∈ Set.Icc (0:ℝ) 1 ∧ (ezToProd n z).2 ∈ ezBox n := by
  constructor
  · intro h
    exact ⟨h 0, fun i => h i.succ⟩
  · rintro ⟨h0, htail⟩ i
    rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, h⟩
    · subst h; exact h0
    · subst h
      have := htail j
      rw [ezToProd_snd_apply] at this
      exact this

theorem mem_unitBoxBdry_iff (n : ℕ) (z : EuclideanSpace ℝ (Fin (n+1))) :
    z ∈ Submission.Drive.unitBoxBdry n ↔
      z 0 ∈ Set.Icc (0:ℝ) 1 ∧ (ezToProd n z).2 ∈ ezBox n ∧
        (z 0 = 0 ∨ z 0 = 1 ∨ ∃ i : Fin n, (ezToProd n z).2 i = 0 ∨ (ezToProd n z).2 i = 1) := by
  constructor
  · rintro ⟨hbox, i, hi⟩
    obtain ⟨h0, htail⟩ := (mem_unitBox_iff n z).mp hbox
    refine ⟨h0, htail, ?_⟩
    rcases Fin.eq_zero_or_eq_succ i with h | ⟨j, h⟩
    · subst h
      rcases hi with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · subst h
      refine Or.inr (Or.inr ⟨j, ?_⟩)
      show z j.succ = 0 ∨ z j.succ = 1
      exact hi
  · rintro ⟨h0, htail, h | h | ⟨i, hi⟩⟩
    · exact ⟨(mem_unitBox_iff n z).mpr ⟨h0, htail⟩, 0, Or.inl h⟩
    · exact ⟨(mem_unitBox_iff n z).mpr ⟨h0, htail⟩, 0, Or.inr h⟩
    · refine ⟨(mem_unitBox_iff n z).mpr ⟨h0, htail⟩, i.succ, ?_⟩
      show z i.succ = 0 ∨ z i.succ = 1
      exact hi

/-- The standard perturbation shape `t ↦ t (1 - t)`. -/
def ezPhi (t : ℝ) : ℝ := t * (1 - t)

@[simp] theorem ezPhi_zero : ezPhi 0 = 0 := by simp [ezPhi]
@[simp] theorem ezPhi_one : ezPhi 1 = 0 := by simp [ezPhi]
theorem ezPhi_pos {t : ℝ} (h0 : 0 < t) (h1 : t < 1) : 0 < ezPhi t := by
  have : 0 < 1 - t := by linarith
  exact mul_pos h0 this
theorem ezPhi_nonneg {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : 0 ≤ ezPhi t := by
  exact mul_nonneg h0 (by linarith)
theorem ezPhi_eq (t : ℝ) : ezPhi t = 1/4 - (t - 1/2)^2 := by
  unfold ezPhi; ring

theorem ezPhi_le (t : ℝ) : ezPhi t ≤ 1/4 := by
  rw [ezPhi_eq]
  have := sq_nonneg (t - 1/2)
  linarith

/-- On `[0,1]`, `|t (1-t)| ≤ 1`. -/
theorem abs_ezPhi_le_one {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 1) : |ezPhi t| ≤ 1 := by
  rw [abs_of_nonneg (ezPhi_nonneg h0 h1)]
  have := ezPhi_le t
  linarith

theorem contDiff_ezPhi : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ezPhi := by
  unfold ezPhi
  fun_prop

/-- The perturbed map: `ezG F u z = F (t, x) - t*(1-t) • u` on `z = (t,x)`. -/
def ezG (n : ℕ) (F : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (u : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin n) :=
  fun z => F (ezToProd n z) - ezPhi (z 0) • u

/-- The perturbed map for an arbitrary perturbation profile `lam`: `p ↦ F p - lam p.1`. -/
def ezGen (n : ℕ) (F : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (lam : ℝ → EuclideanSpace ℝ (Fin n)) : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun p => F p - lam p.1

/-- The perturbed map, transported to `𝔼^{n+1}` along `ezToProd`. -/
def ezGen' (n : ℕ) (F : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (lam : ℝ → EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n+1)) → EuclideanSpace ℝ (Fin n) :=
  fun z => ezGen n F lam (ezToProd n z)

@[simp] theorem ezGen_apply (n : ℕ) (F : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (lam : ℝ → EuclideanSpace ℝ (Fin n)) (p : ℝ × EuclideanSpace ℝ (Fin n)) :
    ezGen n F lam p = F p - lam p.1 := rfl

@[simp] theorem ezGen'_apply (n : ℕ) (F : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (lam : ℝ → EuclideanSpace ℝ (Fin n)) (z : EuclideanSpace ℝ (Fin (n+1))) :
    ezGen' n F lam z = F (ezToProd n z) - lam (z 0) := by
  simp [ezGen', ezGen, ezToProd_fst]

/-- The set of **bad perturbation values** at time `t`: those `u` for which `ezPhi t • u` is the
value at a point of the box where the partial derivative in the `x`-variable is singular. -/
def ezBad (n : ℕ) (F : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (t : ℝ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {u | ∃ x ∈ ezBox n, F (t, x) = ezPhi t • u ∧
    (fderiv ℝ (fun y => F (t, y)) x).det = 0}

/-! ### The determinant of the partial derivative -/

/-- For an endomorphism of a finite dimensional real vector space, a non-zero determinant implies
surjectivity. -/
theorem det_ne_zero_surjective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {g : E →L[ℝ] E} (h : g.det ≠ 0) : Function.Surjective g := by
  rw [ContinuousLinearMap.det] at h
  have hker : g.toLinearMap.ker = ⊥ := by
    by_contra hc
    exact h ((LinearMap.det_eq_zero_iff_ker_ne_bot).mpr hc)
  have hinj : Function.Injective g := by
    have : Function.Injective g.toLinearMap := by
      rw [← LinearMap.ker_eq_bot]; exact hker
    exact this
  have hfin : Module.finrank ℝ E = Module.finrank ℝ E := rfl
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hfin (f := g.toLinearMap)).mp hinj

/-- A non-surjective endomorphism of a finite dimensional real vector space has vanishing
determinant. -/
theorem det_eq_zero_of_not_surjective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {g : E →L[ℝ] E} (h : ¬ Function.Surjective g) : g.det = 0 := by
  by_contra hd
  exact h (det_ne_zero_surjective hd)

/-- A surjective endomorphism of a finite dimensional real vector space has non-vanishing
determinant. -/
theorem det_ne_zero_of_surjective {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {g : E →L[ℝ] E} (h : Function.Surjective g) : g.det ≠ 0 := by
  intro hd
  rw [ContinuousLinearMap.det] at hd
  have hker : g.toLinearMap.ker ≠ ⊥ := (LinearMap.det_eq_zero_iff_ker_ne_bot).mp hd
  have hninj : ¬ Function.Injective g := fun hinj => hker ((LinearMap.ker_eq_bot).mpr hinj)
  have hinj : Function.Injective g :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (show Module.finrank ℝ E = Module.finrank ℝ E from rfl) (f := g.toLinearMap)).mpr h
  exact hninj hinj

/-- The box `[0,1]ⁿ` is compact. -/
theorem isCompact_ezBox (n : ℕ) : IsCompact (ezBox n) := by
  have h : ezBox n = (PiLp.homeomorph 2 (fun _ : Fin n => ℝ)) ⁻¹'
      (Set.univ.pi fun _ : Fin n => Set.Icc (0 : ℝ) 1) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, ezBox, Set.mem_ofPred_eq]
    exact Iff.rfl
  rw [h]
  exact (Homeomorph.isCompact_preimage _).mpr (isCompact_univ_pi fun _ => isCompact_Icc)

/-- The box `[0,1]ⁿ` is closed. -/
theorem isClosed_ezBox (n : ℕ) : IsClosed (ezBox n) := (isCompact_ezBox n).isClosed

/-- The partial derivative in the `x`-variable of `F` at `(t,x)` is the restriction of
`fderiv ℝ F (t,x)` to the directions with vanishing time component. -/
theorem partial_fderiv_apply {n : ℕ} {F : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (t : ℝ) (x v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ F (t, x) (0, v) = fderiv ℝ (fun y => F (t, y)) x v := by
  have h1 : HasFDerivAt (fun y : EuclideanSpace ℝ (Fin n) => (t, y))
      (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin n))) x :=
    hasFDerivAt_prodMk_right t x
  have h2 : HasFDerivAt F (fderiv ℝ F (t, x)) (t, x) :=
    ((hF.differentiable (by simp)).differentiableAt).hasFDerivAt
  have h5 : fderiv ℝ (fun y => F (t, y)) x = (fderiv ℝ F (t, x)).comp
      (ContinuousLinearMap.inr ℝ ℝ (EuclideanSpace ℝ (Fin n))) :=
    (h2.comp x h1).fderiv
  rw [h5]
  simp

/-- **Sard's theorem, fibre by fibre.**  For fixed `t`, the values of the partial map
`x ↦ F (t,x)` at points of the box where its derivative is singular form a set of measure zero. -/
theorem sard_partial_crit_eq_zero (n : ℕ)
    (F : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F) (t : ℝ) :
    volume {y : EuclideanSpace ℝ (Fin n) | ∃ x : EuclideanSpace ℝ (Fin n),
      x ∈ ezBox n ∧ F (t, x) = y ∧ (fderiv ℝ (fun y => F (t, y)) x).det = 0} = 0 := by
  have hdiff : Differentiable ℝ (fun y : EuclideanSpace ℝ (Fin n) => F (t, y)) := by
    have : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : EuclideanSpace ℝ (Fin n) => F (t, y)) := by
      fun_prop
    exact this.differentiable (by simp)
  have hmain := addHaar_image_eq_zero_of_det_fderivWithin_eq_zero (μ := volume)
    (s := {x : EuclideanSpace ℝ (Fin n) | (fderiv ℝ (fun y => F (t, y)) x).det = 0} ∩ ezBox n)
    (f := fun y : EuclideanSpace ℝ (Fin n) => F (t, y))
    (f' := fun x => fderiv ℝ (fun y => F (t, y)) x)
    (fun x _ => (hdiff.differentiableAt.hasFDerivAt).hasFDerivWithinAt)
    (fun x hx => hx.1)
  refine measure_mono_null ?_ hmain
  rintro y ⟨x, hx, rfl, hdet⟩
  exact ⟨x, ⟨hdet, hx⟩, rfl⟩


/-- The derivative of the perturbed map in the `x`-directions. -/
theorem partial_fderiv_ezGen (n : ℕ)
    (F : ℝ × EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (lam : ℝ → EuclideanSpace ℝ (Fin n))
    (hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F)
    (hlam : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) lam)
    (p : ℝ × EuclideanSpace ℝ (Fin n)) (v : EuclideanSpace ℝ (Fin n)) :
    fderiv ℝ (ezGen n F lam) p (0, v) = fderiv ℝ (fun y => F (p.1, y)) p.2 v := by
  have hfst : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) => lam q.1)
      ((fderiv ℝ lam p.1).comp (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n)))) p :=
    (((hlam.differentiable (by simp)).differentiableAt).hasFDerivAt).comp p hasFDerivAt_fst
  have hF' : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) => F q) (fderiv ℝ F p) p :=
    ((hF.differentiable (by simp)).differentiableAt).hasFDerivAt
  have h1 : HasFDerivAt (fun q : ℝ × EuclideanSpace ℝ (Fin n) => F q - lam q.1)
      ((fderiv ℝ F p) - (fderiv ℝ lam p.1).comp
        (ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin n)))) p := hF'.sub hfst
  have h_eq : ezGen n F lam = fun q : ℝ × EuclideanSpace ℝ (Fin n) => F q - lam q.1 := rfl
  rw [h_eq, h1.fderiv, ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    partial_fderiv_apply hF]
  simp

end

end Work.Drive
