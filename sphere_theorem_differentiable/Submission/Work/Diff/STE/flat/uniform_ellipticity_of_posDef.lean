import Mathlib
import Submission.Work.Diff.STE.FlatPDE

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Uniform ellipticity of a continuous, periodic, positive definite matrix field

Let `u : (Fin n → ℝ) → MatC n` be a continuous, `1`-periodic matrix-valued function whose real
part is positive definite at every point.  Then the quadratic forms
`v ↦ ∑ i, ∑ j, (reMat (u x)) i j * v i * v j` are uniformly bounded below by `lam * ∑ i, (v i)^2`
for a single constant `lam > 0` and *all* `x`, `v`.

This is the ellipticity input of the flat (torus) analytic core of short-time existence: the
principal part of the DeTurck operator is `∑_{cd} (reMat (u x))^{-1}_{cd} ∂_c ∂_d`, and Gårding's
inequality requires a *uniform* lower bound of the symbol `reMat (u x)` in `x`.

## Proof

The set of matrices is compact because `u` is periodic (so it is determined by its values on the
compact cube `[0,1]^n`) and continuous.  Minimising the continuous function
`(x, v) ↦ ∑ i, ∑ j, reMat (u x) i j * v i * v j` over the compact set
`cubeBox n ×ˢ sphereSet n` (cube times the unit Euclidean sphere) gives a constant `lam > 0`,
positive because `reMat (u x)` is positive definite and `v ≠ 0` on the sphere.  The general pair
`(x, v)` is handled by (i) periodicity, which moves `x` into the cube, and (ii) homogeneity,
`Q (s • w) = s² * Q w`, for the normalisation `w = v / ‖v‖`.
-/

open scoped BigOperators

namespace Work.Diff.STE.flat

/-! ### The compact fundamental domain and the unit sphere -/

/-- The closed unit cube `[0,1]^n`, a compact fundamental domain for the `1`-periodic functions on
`Fin n → ℝ`. -/
def cubeBox (n : ℕ) : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ : Fin n => Set.Icc (0:ℝ) 1)

/-- The unit Euclidean sphere `{v | ∑ i, (v i)^2 = 1}`. -/
def sphereSet (n : ℕ) : Set (Fin n → ℝ) := {v | ∑ i, (v i)^2 = 1}

lemma isCompact_cubeBox (n : ℕ) : IsCompact (cubeBox n) :=
  isCompact_univ_pi (fun _ => isCompact_Icc)

lemma isCompact_sphereSet (n : ℕ) : IsCompact (sphereSet n) := by
  refine (isCompact_univ_pi (fun _ : Fin n => isCompact_Icc (a := (-1:ℝ)) (b := 1))).of_isClosed_subset
    ?_ ?_
  · exact isClosed_eq (by fun_prop) continuous_const
  · intro v hv i _
    have hv' : ∑ k, (v k)^2 = 1 := hv
    have hle : (v i)^2 ≤ 1 := by
      have h := Finset.single_le_sum (f := fun k => (v k)^2) (fun k _ => sq_nonneg _)
        (Finset.mem_univ i)
      rwa [hv'] at h
    exact abs_le.mp ((sq_le_one_iff_abs_le_one (v i)).mp hle)

/-! ### The quadratic form of the real part -/

/-- The quadratic form of the real part of the matrix field: `v ⬝ᵥ (reMat (u x)).mulVec v`. -/
def reQform {n : ℕ} (u : (Fin n → ℝ) → Work.Diff.STE.Flat.MatC n) (x v : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, Work.Diff.STE.Flat.reMat (u x) i j * v i * v j

lemma continuous_reQform {n : ℕ} {u : (Fin n → ℝ) → Work.Diff.STE.Flat.MatC n}
    (hu : Continuous u) :
    Continuous fun p : (Fin n → ℝ) × (Fin n → ℝ) => reQform u p.1 p.2 := by
  unfold reQform Work.Diff.STE.Flat.reMat
  fun_prop

/-- Homogeneity of the quadratic form in its vector argument. -/
lemma reQform_smul {n : ℕ} (u : (Fin n → ℝ) → Work.Diff.STE.Flat.MatC n) (x : Fin n → ℝ)
    (a : ℝ) (v : Fin n → ℝ) : reQform u x (a • v) = a^2 * reQform u x v := by
  simp only [reQform, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro j _
  ring

/-- The quadratic form is the matrix dot product `star v ⬝ᵥ M *ᵥ v`. -/
lemma dotProduct_mulVec_eq_sum_mul {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    star v ⬝ᵥ M.mulVec v = ∑ i, ∑ j, M i j * v i * v j := by
  rw [star_trivial]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro i _
  apply Finset.sum_congr rfl; intro j _
  ring

/-! ### Periodicity: reducing to the fundamental domain -/

lemma periodic1_zsmul_single {n : ℕ} {β : Type*} {f : (Fin n → ℝ) → β}
    (hf : Work.Diff.STE.Periodic1 f) (i : Fin n) (m : ℤ) (x : Fin n → ℝ) :
    f (x + m • Pi.single i 1) = f x := by
  have h : Function.Periodic f (Pi.single i 1) := hf i
  exact (h.zsmul m) x

lemma periodic1_add_sum {n : ℕ} {β : Type*} {f : (Fin n → ℝ) → β}
    (hf : Work.Diff.STE.Periodic1 f) (c : Fin n → ℤ) (y : Fin n → ℝ) :
    f (y + ∑ i, (c i) • Pi.single i 1) = f y := by
  have aux : ∀ s : Finset (Fin n), ∀ y : Fin n → ℝ,
      f (y + ∑ i ∈ s, (c i) • Pi.single i 1) = f y := by
    intro s
    induction s using Finset.induction with
    | empty => intro y; simp
    | insert a s ha ih =>
      intro y
      have hsplit : y + ∑ i ∈ insert a s, (c i) • Pi.single i 1
          = (y + ∑ i ∈ s, (c i) • Pi.single i 1) + (c a) • Pi.single a 1 := by
        rw [Finset.sum_insert ha]; abel
      rw [hsplit, periodic1_zsmul_single hf a (c a) (y + _)]
      exact ih y
  exact aux Finset.univ y

/-- Every point of the torus has the same value as its fractional part, which lies in the unit
cube.  This is the (integer) translation invariance of a `1`-periodic function. -/
lemma exists_mem_cubeBox_of_periodic {n : ℕ} {β : Type*} {f : (Fin n → ℝ) → β}
    (hf : Work.Diff.STE.Periodic1 f) (x : Fin n → ℝ) :
    ∃ y ∈ cubeBox n, f y = f x := by
  refine ⟨fun i => Int.fract (x i), ?_, ?_⟩
  · intro i _
    exact ⟨Int.fract_nonneg (x i), (Int.fract_lt_one (x i)).le⟩
  · have hsum : (∑ i, (⌊x i⌋ : ℤ) • Pi.single i 1 : Fin n → ℝ) = fun i => (⌊x i⌋ : ℝ) := by
      ext k
      simp only [Finset.sum_apply, zsmul_eq_mul]
      simp [Pi.single_apply, Finset.sum_ite_eq]
    have hz : (fun i => Int.fract (x i)) + (∑ i, (⌊x i⌋ : ℤ) • Pi.single i 1) = x := by
      rw [hsum]; funext i; simp only [Pi.add_apply]; linarith [Int.fract_add_floor (x i)]
    have hmain := periodic1_add_sum hf (fun i => ⌊x i⌋) (fun i => Int.fract (x i))
    rw [hz] at hmain
    exact hmain.symm

/-! ### The main theorem -/

theorem uniform_ellipticity_of_posDef {n : ℕ} (u : Work.Diff.STE.Flat.Torus n)
    (hu : Continuous u) (hper : Work.Diff.STE.Periodic1 u) (h : ∀ x, Work.Diff.STE.Flat.PosDefM (u x)) :
    ∃ lam : ℝ, 0 < lam ∧ ∀ (x : Fin n → ℝ) (v : Fin n → ℝ),
      lam * ∑ i, (v i) ^ 2 ≤ ∑ i, ∑ j,
        Work.Diff.STE.Flat.reMat (u x) i j * v i * v j := by
  by_cases hn : n = 0
  · subst hn
    exact ⟨1, one_pos, fun x v => by simp⟩
  · obtain ⟨i₀⟩ := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    have hKc : IsCompact (cubeBox n) := isCompact_cubeBox n
    have hSc : IsCompact (sphereSet n) := isCompact_sphereSet n
    have hKSc : IsCompact (cubeBox n ×ˢ sphereSet n) := hKc.prod hSc
    -- the fibre of the unit sphere at `Pi.single i₀ 1`, which lies in the cube
    have hne : (cubeBox n ×ˢ sphereSet n).Nonempty := by
      refine ⟨((fun _ : Fin n => (0:ℝ)), (fun j : Fin n => if j = i₀ then (1:ℝ) else 0)), ?_, ?_⟩
      · intro i _; exact ⟨le_refl 0, zero_le_one⟩
      · show ∑ i, ((fun j : Fin n => if j = i₀ then (1:ℝ) else 0) i)^2 = 1
        rw [Finset.sum_eq_single i₀]
        · simp
        · intro b _ hb; simp [hb]
        · intro hb; exact absurd (Finset.mem_univ i₀) hb
    have hcont : ContinuousOn (fun p : (Fin n → ℝ) × (Fin n → ℝ) => reQform u p.1 p.2)
        (cubeBox n ×ˢ sphereSet n) := (continuous_reQform hu).continuousOn
    obtain ⟨p, hp, hpmin⟩ := hKSc.exists_isMinOn hne hcont
    have hpmin' : ∀ q ∈ cubeBox n ×ˢ sphereSet n, reQform u p.1 p.2 ≤ reQform u q.1 q.2 :=
      isMinOn_iff.mp hpmin
    have hp2 : p.2 ∈ sphereSet n := hp.2
    have hp2_ne : p.2 ≠ 0 := by
      intro h0
      have h1 : ∑ i, (p.2 i)^2 = 1 := hp2
      rw [h0] at h1
      simp at h1
    -- the minimum is positive: it is the quadratic form of a positive definite matrix at a
    -- nonzero vector
    have hlam_pos : 0 < reQform u p.1 p.2 := by
      have hpd : 0 < star p.2 ⬝ᵥ (Work.Diff.STE.Flat.reMat (u p.1)).mulVec p.2 :=
        (h p.1).dotProduct_mulVec_pos hp2_ne
      rw [dotProduct_mulVec_eq_sum_mul] at hpd
      simpa [reQform] using hpd
    refine ⟨reQform u p.1 p.2, hlam_pos, ?_⟩
    intro x v
    obtain ⟨y, hyK, hyx⟩ := exists_mem_cubeBox_of_periodic hper x
    have hkey : ∀ w : Fin n → ℝ, reQform u x w = reQform u y w := fun w => by
      simp only [reQform, hyx]
    by_cases hv : (∑ i, (v i)^2) = 0
    · -- `v = 0`: both sides vanish
      have hv0 : v = 0 := by
        funext i
        have h1 := (Finset.sum_eq_zero_iff_of_nonneg (f := fun k => (v k)^2)
          (fun k _ => sq_nonneg _)).mp hv
        exact sq_eq_zero_iff.mp (h1 i (Finset.mem_univ i))
      rw [hv, hv0]
      simp [reQform]
    · -- normalise `v` to the unit sphere and use homogeneity
      have hpos : 0 < ∑ i, (v i)^2 :=
        lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hv)
      obtain ⟨s, hs_pos, hs_sq⟩ : ∃ s : ℝ, 0 < s ∧ s^2 = ∑ i, (v i)^2 :=
        ⟨Real.sqrt _, Real.sqrt_pos.mpr hpos, Real.sq_sqrt hpos.le⟩
      have hs_ne : s ≠ 0 := ne_of_gt hs_pos
      set w : Fin n → ℝ := fun i => v i / s with hwdef
      have hwS : w ∈ sphereSet n := by
        show ∑ i, (w i)^2 = 1
        have h1 : ∀ i, (w i)^2 = (v i)^2 / s^2 := by
          intro i
          have hwi : w i = v i / s := by rw [hwdef]
          rw [hwi, div_pow]
        calc ∑ i, (w i)^2 = ∑ i, (v i)^2 / s^2 := Finset.sum_congr rfl (fun i _ => h1 i)
          _ = (∑ i, (v i)^2) / s^2 := (Finset.sum_div Finset.univ (fun i => (v i)^2) (s^2)).symm
          _ = s^2 / s^2 := by rw [hs_sq]
          _ = 1 := div_self (pow_ne_zero 2 hs_ne)
      have h1 : reQform u p.1 p.2 ≤ reQform u y w := hpmin' (y, w) ⟨hyK, hwS⟩
      have hvw : v = s • w := by
        funext i
        have hwi : w i = v i / s := by rw [hwdef]
        simp only [Pi.smul_apply, smul_eq_mul, hwi]
        field_simp
      calc reQform u p.1 p.2 * ∑ i, (v i)^2
          = reQform u p.1 p.2 * s^2 := by rw [hs_sq]
        _ ≤ reQform u y w * s^2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg s)
        _ = s^2 * reQform u y w := by ring
        _ = reQform u x (s • w) := by rw [reQform_smul, hkey w]
        _ = reQform u x v := by rw [hvw]

end Work.Diff.STE.flat
