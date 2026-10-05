import Mathlib
import Submission.Work.RPA3.Defs
import Submission.Work.RPA3.Symp
import Submission.Work.RPA3.lagrangian_orthogonal

/-!
# RPA3, D3 (follow the family): the tangential correction field `Y`

This file collects the definitions used by the proof of `Work.RPA3.follow_family`.  Given a
`LagFamilyAll` `L` and a Hamiltonian `H`, we want to write the "defect"

`W(τ,x,t) = X_H(ℓ τ (x,t)) - ∂_τℓ(τ,x,t)`

as a combination of the two slice derivatives `∂_xℓ`, `∂_tℓ`:

`W = Y₁ ∂_xℓ + Y₂ ∂_tℓ`.

Since `(∂_xℓ, ∂_tℓ)` is a basis of a Lagrangian plane, `W` is in its span precisely when it is
`ω`-orthogonal to both generators, and then the coefficients are recovered from the Gram matrix
(with respect to the standard Euclidean inner product `ip`).

The file deliberately contains *only* definitions (plus the trivial reduction lemmas); the
mathematical content lives in the companion files.
-/

open scoped ContDiff

set_option autoImplicit false

noncomputable section

namespace Work.RPA3

/-- `∂_τℓ(τ,x,t)`. -/
def dTau (L : LagFamilyAll) (τ x t : ℝ) : PS := deriv (fun σ => L.ℓ σ (x, t)) τ

/-- `∂_xℓ(τ,x,t)`. -/
def dX (L : LagFamilyAll) (τ x t : ℝ) : PS := deriv (fun y => L.ℓ τ (y, t)) x

/-- `∂_tℓ(τ,x,t)`. -/
def dT (L : LagFamilyAll) (τ x t : ℝ) : PS := deriv (fun s => L.ℓ τ (x, s)) t

/-- The defect `X_H(ℓ τ (x,t)) - ∂_τℓ(τ,x,t)`. -/
def Wvec (L : LagFamilyAll) (H : ℝ → PS → ℝ) (τ x t : ℝ) : PS :=
  hamVF (H τ) (L.ℓ τ (x, t)) - dTau L τ x t

/-- `⟪∂_xℓ, ∂_xℓ⟫`. -/
def gramA (L : LagFamilyAll) (τ x t : ℝ) : ℝ := ip (dX L τ x t) (dX L τ x t)

/-- `⟪∂_xℓ, ∂_tℓ⟫`. -/
def gramB (L : LagFamilyAll) (τ x t : ℝ) : ℝ := ip (dX L τ x t) (dT L τ x t)

/-- `⟪∂_tℓ, ∂_tℓ⟫`. -/
def gramC (L : LagFamilyAll) (τ x t : ℝ) : ℝ := ip (dT L τ x t) (dT L τ x t)

/-- The determinant of the Gram matrix of `(∂_xℓ, ∂_tℓ)`. -/
def gramDet (L : LagFamilyAll) (τ x t : ℝ) : ℝ :=
  gramA L τ x t * gramC L τ x t - gramB L τ x t ^ 2

/-- The tangential correction coefficients: `G⁻¹` applied to the pairings of `W` with `∂_xℓ`,
`∂_tℓ`, where `G` is the Gram matrix of `(∂_xℓ, ∂_tℓ)`. -/
def Ycoef (L : LagFamilyAll) (H : ℝ → PS → ℝ) (τ x t : ℝ) : ℝ × ℝ :=
  ((gramC L τ x t * ip (Wvec L H τ x t) (dX L τ x t)
      - gramB L τ x t * ip (Wvec L H τ x t) (dT L τ x t)) / gramDet L τ x t,
   (gramA L τ x t * ip (Wvec L H τ x t) (dT L τ x t)
      - gramB L τ x t * ip (Wvec L H τ x t) (dX L τ x t)) / gramDet L τ x t)

/-- The tangential correction field on the `(x,t)`-plane. -/
def Yfield (L : LagFamilyAll) (H : ℝ → PS → ℝ) : ℝ → (ℝ × ℝ) → (ℝ × ℝ) :=
  fun τ q => Ycoef L H τ q.1 q.2

/-- The uncurried family map `(τ,x,t) ↦ ℓ τ (x,t)`. -/
def Efun (L : LagFamilyAll) : ℝ × (ℝ × ℝ) → PS := fun z => L.ℓ z.1 z.2

@[simp] theorem Yfield_apply (L : LagFamilyAll) (H : ℝ → PS → ℝ) (τ : ℝ) (q : ℝ × ℝ) :
    Yfield L H τ q = Ycoef L H τ q.1 q.2 := rfl

@[simp] theorem Efun_apply (L : LagFamilyAll) (τ : ℝ) (q : ℝ × ℝ) :
    Efun L (τ, q) = L.ℓ τ q := rfl

/-! ## Bilinearity of `ip`

`ip a b = a.1.1*b.1.1 + a.1.2*b.1.2 + a.2.1*b.2.1 + a.2.2*b.2.2` is a symmetric bilinear form; these
are the linearity lemmas needed for the Gram-matrix computations. -/

theorem ip_add_left (a a' b : PS) : ip (a + a') b = ip a b + ip a' b := by
  simp only [ip, Prod.fst_add, Prod.snd_add]; ring

theorem ip_add_right (a b b' : PS) : ip a (b + b') = ip a b + ip a b' := by
  simp only [ip, Prod.fst_add, Prod.snd_add]; ring

theorem ip_sub_left (a a' b : PS) : ip (a - a') b = ip a b - ip a' b := by
  simp only [ip, Prod.fst_sub, Prod.snd_sub]; ring

theorem ip_sub_right (a b b' : PS) : ip a (b - b') = ip a b - ip a b' := by
  simp only [ip, Prod.fst_sub, Prod.snd_sub]; ring

theorem ip_smul_left (c : ℝ) (a b : PS) : ip (c • a) b = c * ip a b := by
  simp only [ip, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem ip_smul_right (c : ℝ) (a b : PS) : ip a (c • b) = c * ip a b := by
  simp only [ip, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

/-- The Gram determinant of `(∂_xℓ, ∂_tℓ)` is strictly positive: the two vectors are linearly
independent by `LagFamilyAll.imm`, and the Gram determinant of an independent pair for the positive
definite form `ip` is positive. -/
theorem gramDet_pos (L : LagFamilyAll) (τ x t : ℝ) : 0 < gramDet L τ x t := by
  have hind := L.imm τ x t
  have hu0 : dX L τ x t ≠ 0 := by
    intro h
    have h' : deriv (fun y => L.ℓ τ (y, t)) x = 0 := h
    have h1 := hind 1 0 (by rw [h']; simp)
    exact one_ne_zero h1.1
  have hApos : 0 < ip (dX L τ x t) (dX L τ x t) := by
    rcases lt_or_eq_of_le (ip_self_nonneg (dX L τ x t)) with h | h
    · exact h
    · exact absurd ((ip_self_eq_zero_iff (dX L τ x t)).mp h.symm) hu0
  have hkey : ip (ip (dX L τ x t) (dX L τ x t) • dT L τ x t
        - ip (dX L τ x t) (dT L τ x t) • dX L τ x t)
      (ip (dX L τ x t) (dX L τ x t) • dT L τ x t
        - ip (dX L τ x t) (dT L τ x t) • dX L τ x t)
      = ip (dX L τ x t) (dX L τ x t) * gramDet L τ x t := by
    simp only [gramDet, gramA, gramB, gramC]
    simp only [ip, Prod.smul_fst, Prod.smul_snd, Prod.fst_sub, Prod.snd_sub,
      smul_eq_mul]
    ring
  have hnn : 0 ≤ ip (ip (dX L τ x t) (dX L τ x t) • dT L τ x t
        - ip (dX L τ x t) (dT L τ x t) • dX L τ x t)
      (ip (dX L τ x t) (dX L τ x t) • dT L τ x t
        - ip (dX L τ x t) (dT L τ x t) • dX L τ x t) := ip_self_nonneg _
  rw [hkey] at hnn
  refine lt_of_le_of_ne (by nlinarith) ?_
  intro h0
  have hz : ip (ip (dX L τ x t) (dX L τ x t) • dT L τ x t
        - ip (dX L τ x t) (dT L τ x t) • dX L τ x t)
      (ip (dX L τ x t) (dX L τ x t) • dT L τ x t
        - ip (dX L τ x t) (dT L τ x t) • dX L τ x t) = 0 := by
    rw [hkey, h0.symm, mul_zero]
  have hvz := (ip_self_eq_zero_iff _).mp hz
  have hrel : (-(ip (dX L τ x t) (dT L τ x t))) • dX L τ x t
      + (ip (dX L τ x t) (dX L τ x t)) • dT L τ x t = 0 :=
    (by simpa only [neg_smul, sub_eq_add_neg, add_comm] using hvz)
  exact hApos.ne' (hind _ _ hrel).2

/-! ## Smoothness of the `τ`-slice derivative -/

/-- The slice derivative `(τ,x,t) ↦ ∂_τ ℓ τ (x,t)` is `C⁷`. -/
theorem contDiff_sliceDerivTau (L : LagFamilyAll) :
    ContDiff ℝ 7 (fun p : ℝ × ℝ × ℝ => deriv (fun σ => L.ℓ σ (p.2.1, p.2.2)) p.1) := by
  have hf : ContDiff ℝ 8
      (Function.uncurry (fun (x : ℝ × ℝ × ℝ) (y : ℝ) => L.ℓ y (x.2.1, x.2.2))) := by
    have hΨ : ContDiff ℝ 8
        (fun q : (ℝ × ℝ × ℝ) × ℝ => ((q.2, (q.1.2.1, q.1.2.2)) : ℝ × (ℝ × ℝ))) := by
      fun_prop
    have := L.smooth.comp hΨ
    convert this using 1
    funext q
    rfl
  have hg : ContDiff ℝ 7 (fun x : ℝ × ℝ × ℝ => x.1) := by fun_prop
  have hk : ContDiff ℝ 7 (fun _ : ℝ × ℝ × ℝ => (1 : ℝ)) := contDiff_const
  have hmain := ContDiff.fderiv_apply
    (f := fun (x : ℝ × ℝ × ℝ) (y : ℝ) => L.ℓ y (x.2.1, x.2.2)) hf hg hk (by norm_num)
  simpa only [fderiv_apply_one_eq_deriv] using hmain

/-- `dTau` is the `τ`-slice derivative, in the strip coordinates. -/
theorem dTau_eq (L : LagFamilyAll) (τ x t : ℝ) :
    dTau L τ x t = deriv (fun σ => L.ℓ σ (x, t)) τ := rfl

/-! ## The pairing of the Hamiltonian field with a vector -/

/-- `ω(X_H(y), v) = -dH(v)`: the Hamiltonian vector field is the `ω`-dual of `-dH`.  No
differentiability of `H` is needed -- both sides only depend on the (always linear) Fréchet
derivative `fderiv ℝ H y`. -/
theorem symp_hamVF (H : PS → ℝ) (y v : PS) :
    symp (hamVF H y) v = -fderiv ℝ H y v := by
  have hv : v = v.1.1 • (((1, 0), (0, 0)) : PS) + v.1.2 • (((0, 1), (0, 0)) : PS)
      + v.2.1 • (((0, 0), (1, 0)) : PS) + v.2.2 • (((0, 0), (0, 1)) : PS) := by
    ext <;> simp
  have hLv : fderiv ℝ H y v
      = v.1.1 * fderiv ℝ H y (((1, 0), (0, 0)) : PS)
        + v.1.2 * fderiv ℝ H y (((0, 1), (0, 0)) : PS)
        + v.2.1 * fderiv ℝ H y (((0, 0), (1, 0)) : PS)
        + v.2.2 * fderiv ℝ H y (((0, 0), (0, 1)) : PS) := by
    conv_lhs => rw [hv]
    simp only [map_add, map_smul, smul_eq_mul]
  rw [hLv]
  simp only [hamVF, symp]
  ring

/-! ## The cut-off field

To apply the global-flow theorem we need a field that is globally Lipschitz and bounded and which
agrees with `Yfield` on `[0,1] × ℝ²`.  Multiplying `Yfield` by a smooth time cut-off `chi` (equal
to `1` on `[-1,2]` and supported in `[-2,3]`) and a smooth spatial bump `bump c` (equal to `1` on
`{q₁²+q₂² ≤ c-1}` and supported in `{q₁²+q₂² ≤ c}`) produces a `C¹`, compactly supported field. -/

/-- The smooth time cut-off `1` on `[-1,2]`, `0` outside `[-2,3]`. -/
def chi : ℝ → ℝ := fun t => Real.smoothTransition (t + 2) * Real.smoothTransition (3 - t)

/-- The smooth spatial bump: `1` where `q₁²+q₂² ≤ c-1`, `0` where `c ≤ q₁²+q₂²`. -/
def bump (c : ℝ) (q : ℝ × ℝ) : ℝ := Real.smoothTransition (c - (q.1 ^ 2 + q.2 ^ 2))

/-- The cut-off tangential field. -/
def Zfield (L : LagFamilyAll) (H : ℝ → PS → ℝ) (c : ℝ) : ℝ → (ℝ × ℝ) → (ℝ × ℝ) :=
  fun τ q => (chi τ * bump c q) • Yfield L H τ q

theorem chi_contDiff : ContDiff ℝ 1 chi := by
  unfold chi; fun_prop

theorem chi_one {t : ℝ} (ht : t ∈ Set.Icc (-1 : ℝ) 2) : chi t = 1 := by
  unfold chi
  rw [Real.smoothTransition.one_of_one_le (by linarith [ht.1] : (1:ℝ) ≤ t + 2),
      Real.smoothTransition.one_of_one_le (by linarith [ht.2] : (1:ℝ) ≤ 3 - t), mul_one]

theorem chi_zero_left {t : ℝ} (ht : t ≤ -2) : chi t = 0 := by
  unfold chi
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : t + 2 ≤ 0), zero_mul]

theorem chi_zero_right {t : ℝ} (ht : 3 ≤ t) : chi t = 0 := by
  unfold chi
  rw [Real.smoothTransition.zero_of_nonpos (by linarith : 3 - t ≤ 0), mul_zero]

theorem chi_bounds (t : ℝ) : 0 ≤ chi t ∧ chi t ≤ 1 := by
  refine ⟨mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _), ?_⟩
  calc chi t = Real.smoothTransition (t + 2) * Real.smoothTransition (3 - t) := rfl
    _ ≤ 1 * Real.smoothTransition (3 - t) :=
        mul_le_mul_of_nonneg_right (Real.smoothTransition.le_one _)
          (Real.smoothTransition.nonneg _)
    _ = Real.smoothTransition (3 - t) := one_mul _
    _ ≤ 1 := Real.smoothTransition.le_one _

theorem bump_contDiff (c : ℝ) : ContDiff ℝ 1 (bump c) := by
  unfold bump; fun_prop

theorem bump_one {c : ℝ} {q : ℝ × ℝ} (hq : q.1 ^ 2 + q.2 ^ 2 ≤ c - 1) : bump c q = 1 := by
  unfold bump
  exact Real.smoothTransition.one_of_one_le (by linarith)

theorem bump_zero {c : ℝ} {q : ℝ × ℝ} (hq : c ≤ q.1 ^ 2 + q.2 ^ 2) : bump c q = 0 := by
  unfold bump
  exact Real.smoothTransition.zero_of_nonpos (by linarith)

theorem bump_bounds (c : ℝ) (q : ℝ × ℝ) : 0 ≤ bump c q ∧ bump c q ≤ 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

theorem Zfield_apply (L : LagFamilyAll) (H : ℝ → PS → ℝ) (c : ℝ) (τ : ℝ) (q : ℝ × ℝ) :
    Zfield L H c τ q = (chi τ * bump c q) • Yfield L H τ q := rfl

/-- On the region where the cut-offs are `1`, `Zfield` agrees with `Yfield`. -/
theorem Zfield_eq_Yfield (L : LagFamilyAll) (H : ℝ → PS → ℝ) (c : ℝ) (τ : ℝ) (q : ℝ × ℝ)
    (h1 : chi τ = 1) (h2 : bump c q = 1) : Zfield L H c τ q = Yfield L H τ q := by
  rw [Zfield_apply, h1, h2, one_mul, one_smul]

end Work.RPA3
