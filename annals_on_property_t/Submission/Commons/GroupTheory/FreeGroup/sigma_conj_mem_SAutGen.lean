import Mathlib

set_option autoImplicit false

namespace Commons.GroupTheory.FreeGroup

/-!
# Nielsen transvections, single-generator inversions, and the generating set of `SAut(F_n)`

This file sets up, from scratch (only `Mathlib`), the Nielsen transvections
`ρᵤᵥ` (`a_u ↦ a_u a_v`), `ρᵤᵥ⁻¹`, `λᵤᵥ` (`a_u ↦ a_v a_u`), `λᵤᵥ⁻¹` and the
single-generator inversions `σᵢ` (`a_i ↦ a_i⁻¹`), together with the generating
set `SAutGen n = {ρᵤᵥ^{±1}, λᵤᵥ^{±1}}` of `SAut(F_n)`.

It then proves the normalisation statement used in the proof that `Aut(F_n)`
has property (T): **conjugation by `σᵢ` preserves `SAutGen n`**.

The computation is elementary:  `σᵢ ρᵤᵥ σᵢ` is

* `ρᵤᵥ` if `i ∉ {u,v}`,
* `λᵤᵥ⁻¹` if `i = u`,
* `ρᵤᵥ⁻¹` if `i = v`,

and similarly for the other three families; the remaining cases follow because
conjugation by `σᵢ` is an involution (`σᵢ σᵢ = 1`).
-/

noncomputable section

variable {n : ℕ}

/-! ### The Nielsen transvections and the single-generator inversion -/

abbrev a (i : Fin n) : FreeGroup (Fin n) := FreeGroup.of i

def rhoHom (i j : Fin n) : FreeGroup (Fin n) →* FreeGroup (Fin n) :=
  FreeGroup.lift (fun k : Fin n => if k = i then a i * a j else a k)

def rhoInvHom (i j : Fin n) : FreeGroup (Fin n) →* FreeGroup (Fin n) :=
  FreeGroup.lift (fun k : Fin n => if k = i then a i * (a j)⁻¹ else a k)

lemma rhoHom_comp_rhoInvHom (i j : Fin n) (hij : i ≠ j) :
    (rhoHom i j).comp (rhoInvHom i j) = MonoidHom.id (FreeGroup (Fin n)) := by
  apply FreeGroup.ext_hom
  intro k
  by_cases hk : k = i
  · subst k
    have hji : j ≠ i := fun h => hij h.symm
    calc
      (rhoHom i j) ((rhoInvHom i j) (a i)) = (rhoHom i j) (a i * (a j)⁻¹) := by
        congr 1
        simp [rhoInvHom]
      _ = (rhoHom i j) (a i) * (rhoHom i j) ((a j)⁻¹) := by
        rw [map_mul]
      _ = (a i * a j) * (a j)⁻¹ := by
        rw [show (rhoHom i j) (a i) = a i * a j by simp [rhoHom]]
        rw [show (rhoHom i j) ((a j)⁻¹) = (a j)⁻¹ by
          rw [map_inv]
          congr 1
          simp [rhoHom, hji]]
      _ = a i := by
        rw [mul_assoc, mul_inv_cancel, mul_one]
  · calc
      (rhoHom i j) ((rhoInvHom i j) (a k)) = (rhoHom i j) (a k) := by
        congr 1
        simp [rhoInvHom, hk]
      _ = a k := by
        simp [rhoHom, hk]

lemma rhoInvHom_comp_rhoHom (i j : Fin n) (hij : i ≠ j) :
    (rhoInvHom i j).comp (rhoHom i j) = MonoidHom.id (FreeGroup (Fin n)) := by
  apply FreeGroup.ext_hom
  intro k
  by_cases hk : k = i
  · subst k
    have hji : j ≠ i := fun h => hij h.symm
    calc
      (rhoInvHom i j) ((rhoHom i j) (a i)) = (rhoInvHom i j) (a i * a j) := by
        congr 1
        simp [rhoHom]
      _ = (rhoInvHom i j) (a i) * (rhoInvHom i j) (a j) := by
        rw [map_mul]
      _ = (a i * (a j)⁻¹) * a j := by
        rw [show (rhoInvHom i j) (a i) = a i * (a j)⁻¹ by simp [rhoInvHom]]
        rw [show (rhoInvHom i j) (a j) = a j by
          simp [rhoInvHom, hji]]
      _ = a i := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
  · calc
      (rhoInvHom i j) ((rhoHom i j) (a k)) = (rhoInvHom i j) (a k) := by
        congr 1
        simp [rhoHom, hk]
      _ = a k := by
        simp [rhoInvHom, hk]

def rho (i j : Fin n) (hij : i ≠ j) : MulAut (FreeGroup (Fin n)) where
  toFun := rhoHom i j
  invFun := rhoInvHom i j
  left_inv x := by
    have h := congrArg (fun φ : FreeGroup (Fin n) →* FreeGroup (Fin n) => φ x)
      (rhoInvHom_comp_rhoHom i j hij)
    simpa using h
  right_inv x := by
    have h := congrArg (fun φ : FreeGroup (Fin n) →* FreeGroup (Fin n) => φ x)
      (rhoHom_comp_rhoInvHom i j hij)
    simpa using h
  map_mul' x y := (rhoHom i j).map_mul x y

lemma rho_apply_self (i j : Fin n) (hij : i ≠ j) :
    (rho i j hij) (a i) = a i * a j := by
  simp [rho, rhoHom]

lemma rho_apply_other {i j k : Fin n} (hij : i ≠ j) (hk : k ≠ i) :
    (rho i j hij) (a k) = a k := by
  simp [rho, rhoHom, hk]

def rhoNeg (i j : Fin n) (hij : i ≠ j) : MulAut (FreeGroup (Fin n)) where
  toFun := rhoInvHom i j
  invFun := rhoHom i j
  left_inv x := by
    have h := congrArg (fun φ : FreeGroup (Fin n) →* FreeGroup (Fin n) => φ x)
      (rhoHom_comp_rhoInvHom i j hij)
    simpa using h
  right_inv x := by
    have h := congrArg (fun φ : FreeGroup (Fin n) →* FreeGroup (Fin n) => φ x)
      (rhoInvHom_comp_rhoHom i j hij)
    simpa using h
  map_mul' x y := (rhoInvHom i j).map_mul x y

lemma rhoNeg_apply_self (i j : Fin n) (hij : i ≠ j) :
    (rhoNeg i j hij) (a i) = a i * (a j)⁻¹ := by
  simp [rhoNeg, rhoInvHom]

lemma rhoNeg_apply_other {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hk : k ≠ i) :
    (rhoNeg i j hij) (a k) = a k := by
  simp [rhoNeg, rhoInvHom, hk]

def lamHom (i j : Fin n) : FreeGroup (Fin n) →* FreeGroup (Fin n) :=
  FreeGroup.lift (fun k : Fin n => if k = i then a j * a i else a k)

def lamInvHom (i j : Fin n) : FreeGroup (Fin n) →* FreeGroup (Fin n) :=
  FreeGroup.lift (fun k : Fin n => if k = i then (a j)⁻¹ * a i else a k)

lemma lamHom_comp_lamInvHom (i j : Fin n) (hij : i ≠ j) :
    (lamHom i j).comp (lamInvHom i j) = MonoidHom.id (FreeGroup (Fin n)) := by
  apply FreeGroup.ext_hom
  intro k
  by_cases hk : k = i
  · subst k
    have hji : j ≠ i := fun h => hij h.symm
    calc
      (lamHom i j) ((lamInvHom i j) (a i)) = (lamHom i j) ((a j)⁻¹ * a i) := by
        congr 1
        simp [lamInvHom]
      _ = (lamHom i j) ((a j)⁻¹) * (lamHom i j) (a i) := by
        rw [map_mul]
      _ = (a j)⁻¹ * (a j * a i) := by
        rw [show (lamHom i j) (a i) = a j * a i by simp [lamHom]]
        rw [show (lamHom i j) ((a j)⁻¹) = (a j)⁻¹ by
          rw [map_inv]
          congr 1
          simp [lamHom, hji]]
      _ = a i := by
        rw [← mul_assoc, inv_mul_cancel, one_mul]
  · calc
      (lamHom i j) ((lamInvHom i j) (a k)) = (lamHom i j) (a k) := by
        congr 1
        simp [lamInvHom, hk]
      _ = a k := by
        simp [lamHom, hk]

lemma lamInvHom_comp_lamHom (i j : Fin n) (hij : i ≠ j) :
    (lamInvHom i j).comp (lamHom i j) = MonoidHom.id (FreeGroup (Fin n)) := by
  apply FreeGroup.ext_hom
  intro k
  by_cases hk : k = i
  · subst k
    have hji : j ≠ i := fun h => hij h.symm
    calc
      (lamInvHom i j) ((lamHom i j) (a i)) = (lamInvHom i j) (a j * a i) := by
        congr 1
        simp [lamHom]
      _ = (lamInvHom i j) (a j) * (lamInvHom i j) (a i) := by
        rw [map_mul]
      _ = a j * ((a j)⁻¹ * a i) := by
        rw [show (lamInvHom i j) (a i) = (a j)⁻¹ * a i by simp [lamInvHom]]
        rw [show (lamInvHom i j) (a j) = a j by
          simp [lamInvHom, hji]]
      _ = a i := by
        rw [← mul_assoc, mul_inv_cancel, one_mul]
  · calc
      (lamInvHom i j) ((lamHom i j) (a k)) = (lamInvHom i j) (a k) := by
        congr 1
        simp [lamHom, hk]
      _ = a k := by
        simp [lamInvHom, hk]

def lam (i j : Fin n) (hij : i ≠ j) : MulAut (FreeGroup (Fin n)) where
  toFun := lamHom i j
  invFun := lamInvHom i j
  left_inv x := by
    have h := congrArg (fun φ : FreeGroup (Fin n) →* FreeGroup (Fin n) => φ x)
      (lamInvHom_comp_lamHom i j hij)
    simpa using h
  right_inv x := by
    have h := congrArg (fun φ : FreeGroup (Fin n) →* FreeGroup (Fin n) => φ x)
      (lamHom_comp_lamInvHom i j hij)
    simpa using h
  map_mul' x y := (lamHom i j).map_mul x y

lemma lam_apply_self (i j : Fin n) (hij : i ≠ j) :
    (lam i j hij) (a i) = a j * a i := by
  simp [lam, lamHom]

lemma lam_apply_other {i j k : Fin n} (hij : i ≠ j) (hk : k ≠ i) :
    (lam i j hij) (a k) = a k := by
  simp [lam, lamHom, hk]

def lamNeg (i j : Fin n) (hij : i ≠ j) : MulAut (FreeGroup (Fin n)) where
  toFun := lamInvHom i j
  invFun := lamHom i j
  left_inv x := by
    have h := congrArg (fun φ : FreeGroup (Fin n) →* FreeGroup (Fin n) => φ x)
      (lamHom_comp_lamInvHom i j hij)
    simpa using h
  right_inv x := by
    have h := congrArg (fun φ : FreeGroup (Fin n) →* FreeGroup (Fin n) => φ x)
      (lamInvHom_comp_lamHom i j hij)
    simpa using h
  map_mul' x y := (lamInvHom i j).map_mul x y

lemma lamNeg_apply_self (i j : Fin n) (hij : i ≠ j) :
    (lamNeg i j hij) (a i) = (a j)⁻¹ * a i := by
  simp [lamNeg, lamInvHom]

lemma lamNeg_apply_other {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hk : k ≠ i) :
    (lamNeg i j hij) (a k) = a k := by
  simp [lamNeg, lamInvHom, hk]

def sigmaHom (i : Fin n) : FreeGroup (Fin n) →* FreeGroup (Fin n) :=
  FreeGroup.lift (fun k : Fin n => if k = i then (a i)⁻¹ else a k)

lemma sigmaHom_comp_self (i : Fin n) :
    (sigmaHom i).comp (sigmaHom i) = MonoidHom.id (FreeGroup (Fin n)) := by
  apply FreeGroup.ext_hom
  intro k
  by_cases hk : k = i
  · subst k
    calc
      (sigmaHom i) ((sigmaHom i) (a i)) = (sigmaHom i) ((a i)⁻¹) := by
        congr 1
        simp [sigmaHom]
      _ = ((sigmaHom i) (a i))⁻¹ := by rw [map_inv]
      _ = (a i)⁻¹⁻¹ := by
        congr 1
        simp [sigmaHom]
      _ = a i := by simp
  · calc
      (sigmaHom i) ((sigmaHom i) (a k)) = (sigmaHom i) (a k) := by
        congr 1
        simp [sigmaHom, hk]
      _ = a k := by
        simp [sigmaHom, hk]

def sigma (i : Fin n) : MulAut (FreeGroup (Fin n)) where
  toFun := sigmaHom i
  invFun := sigmaHom i
  left_inv x := by
    have h := congrArg (fun φ : FreeGroup (Fin n) →* FreeGroup (Fin n) => φ x)
      (sigmaHom_comp_self i)
    simpa using h
  right_inv x := by
    have h := congrArg (fun φ : FreeGroup (Fin n) →* FreeGroup (Fin n) => φ x)
      (sigmaHom_comp_self i)
    simpa using h
  map_mul' x y := (sigmaHom i).map_mul x y

lemma sigma_apply_self (i : Fin n) : (sigma i) (a i) = (a i)⁻¹ := by
  simp [sigma, sigmaHom]

lemma sigma_apply_other {i k : Fin n} (hk : k ≠ i) : (sigma i) (a k) = a k := by
  simp [sigma, sigmaHom, hk]

lemma sigma_inv (i : Fin n) : (sigma i)⁻¹ = sigma i := by
  ext x
  rfl

abbrev SAutIdx (n : ℕ) := {p : (Fin n × Fin n) × (Bool × Bool) // p.1.1 ≠ p.1.2}

def sAutAut {n : ℕ} (p : SAutIdx n) : MulAut (FreeGroup (Fin n)) :=
  match p with
  | ⟨v, h⟩ =>
    match v with
    | (ij, be) =>
      match ij with
      | (i, j) =>
        match be with
        | (b, e) =>
            if b then (if e then rho i j h else rhoNeg i j h)
            else (if e then lam i j h else lamNeg i j h)

noncomputable def SAutGen (n : ℕ) : Finset (MulAut (FreeGroup (Fin n))) := by
  classical
  exact Finset.univ.image sAutAut

/-- Two automorphisms of the free group that agree on the basis agree. -/
theorem mulAut_eq_of_gen_eq {n : ℕ} {f g : MulAut (FreeGroup (Fin n))}
    (h : ∀ k : Fin n, f (FreeGroup.of k) = g (FreeGroup.of k)) : f = g := by
  apply MulEquiv.ext
  have hhom : f.toMonoidHom = g.toMonoidHom := FreeGroup.ext_hom _ _ h
  intro x
  exact DFunLike.congr_fun hhom x

/-- `σᵢ` is an involution. -/
lemma sigma_mul_self {n : ℕ} (i : Fin n) : sigma i * sigma i = 1 := by
  calc sigma i * sigma i = (sigma i)⁻¹ * sigma i := by rw [sigma_inv i]
    _ = 1 := inv_mul_cancel (sigma i)

/-- Conjugation by `σᵢ` is an involution on `Aut(F_n)`. -/
lemma sigma_conj_invol {n : ℕ} (i : Fin n) (f : MulAut (FreeGroup (Fin n))) :
    sigma i * (sigma i * f * sigma i) * sigma i = f := by
  have h2 := sigma_mul_self i
  calc sigma i * (sigma i * f * sigma i) * sigma i
      = (sigma i * sigma i) * f * (sigma i * sigma i) := by group
    _ = f := by rw [h2, one_mul, mul_one]

/-! ### The four direct computations -/

/-- `σᵤ ρᵤᵥ σᵤ = λᵤᵥ⁻¹`. -/
lemma sigma_conj_rho_left {n : ℕ} (u v : Fin n) (huv : u ≠ v) :
    sigma u * rho u v huv * sigma u = lamNeg u v huv := by
  apply mulAut_eq_of_gen_eq
  intro k
  rw [MulAut.mul_apply, MulAut.mul_apply]
  by_cases hku : k = u
  · subst k
    simp only [sigma_apply_self, MulEquiv.map_inv, rho_apply_self, mul_inv_rev, MulEquiv.map_mul,
      sigma_apply_other (show v ≠ u from fun h => huv h.symm), inv_inv, lamNeg_apply_self]
  · by_cases hkv : k = v
    · subst k
      simp only [sigma_apply_other hku, rho_apply_other huv hku, lamNeg_apply_other huv hku]
    · simp only [sigma_apply_other hku, rho_apply_other huv hku, lamNeg_apply_other huv hku]

/-- `σᵥ ρᵤᵥ σᵥ = ρᵤᵥ⁻¹`. -/
lemma sigma_conj_rho_right {n : ℕ} (u v : Fin n) (huv : u ≠ v) :
    sigma v * rho u v huv * sigma v = rhoNeg u v huv := by
  apply mulAut_eq_of_gen_eq
  intro k
  rw [MulAut.mul_apply, MulAut.mul_apply]
  by_cases hkv : k = v
  · subst k
    simp only [sigma_apply_self, MulEquiv.map_inv,
      rho_apply_other huv (show v ≠ u from fun h => huv h.symm),
      inv_inv, rhoNeg_apply_other huv (show v ≠ u from fun h => huv h.symm)]
  · by_cases hku : k = u
    · subst k
      simp only [sigma_apply_other huv, rho_apply_self, MulEquiv.map_mul,
        sigma_apply_self, rhoNeg_apply_self]
    · simp only [sigma_apply_other hkv, rho_apply_other huv hku, rhoNeg_apply_other huv hku]

/-- `σᵤ ρᵤᵥ⁻¹ σᵤ = λᵤᵥ`. -/
lemma sigma_conj_rhoNeg_left {n : ℕ} (u v : Fin n) (huv : u ≠ v) :
    sigma u * rhoNeg u v huv * sigma u = lam u v huv := by
  apply mulAut_eq_of_gen_eq
  intro k
  rw [MulAut.mul_apply, MulAut.mul_apply]
  by_cases hku : k = u
  · subst k
    simp only [sigma_apply_self, MulEquiv.map_inv, rhoNeg_apply_self, mul_inv_rev, MulEquiv.map_mul,
      sigma_apply_other (show v ≠ u from fun h => huv h.symm), inv_inv, lam_apply_self]
  · by_cases hkv : k = v
    · subst k
      simp only [sigma_apply_other hku, rhoNeg_apply_other huv hku, lam_apply_other huv hku]
    · simp only [sigma_apply_other hku, rhoNeg_apply_other huv hku, lam_apply_other huv hku]

/-- `σᵥ λᵤᵥ σᵥ = λᵤᵥ⁻¹`. -/
lemma sigma_conj_lam_right {n : ℕ} (u v : Fin n) (huv : u ≠ v) :
    sigma v * lam u v huv * sigma v = lamNeg u v huv := by
  apply mulAut_eq_of_gen_eq
  intro k
  rw [MulAut.mul_apply, MulAut.mul_apply]
  by_cases hkv : k = v
  · subst k
    simp only [sigma_apply_self, MulEquiv.map_inv,
      lam_apply_other huv (show v ≠ u from fun h => huv h.symm),
      inv_inv, lamNeg_apply_other huv (show v ≠ u from fun h => huv h.symm)]
  · by_cases hku : k = u
    · subst k
      simp only [sigma_apply_other huv, lam_apply_self, MulEquiv.map_mul,
        sigma_apply_self, lamNeg_apply_self]
    · simp only [sigma_apply_other hkv, lam_apply_other huv hku, lamNeg_apply_other huv hku]

/-! ### The remaining three cases of each family, by the involution property -/

/-- `σᵤ λᵤᵥ σᵤ = ρᵤᵥ⁻¹`. -/
lemma sigma_conj_lam_left {n : ℕ} (u v : Fin n) (huv : u ≠ v) :
    sigma u * lam u v huv * sigma u = rhoNeg u v huv := by
  rw [← sigma_conj_rhoNeg_left u v huv]
  exact sigma_conj_invol u (rhoNeg u v huv)

/-- `σᵤ λᵤᵥ⁻¹ σᵤ = ρᵤᵥ`. -/
lemma sigma_conj_lamNeg_left {n : ℕ} (u v : Fin n) (huv : u ≠ v) :
    sigma u * lamNeg u v huv * sigma u = rho u v huv := by
  rw [← sigma_conj_rho_left u v huv]
  exact sigma_conj_invol u (rho u v huv)

/-- `σᵥ ρᵤᵥ⁻¹ σᵥ = ρᵤᵥ`. -/
lemma sigma_conj_rhoNeg_right {n : ℕ} (u v : Fin n) (huv : u ≠ v) :
    sigma v * rhoNeg u v huv * sigma v = rho u v huv := by
  rw [← sigma_conj_rho_right u v huv]
  exact sigma_conj_invol v (rho u v huv)

/-- `σᵥ λᵤᵥ⁻¹ σᵥ = λᵤᵥ`. -/
lemma sigma_conj_lamNeg_right {n : ℕ} (u v : Fin n) (huv : u ≠ v) :
    sigma v * lamNeg u v huv * sigma v = lam u v huv := by
  rw [← sigma_conj_lam_right u v huv]
  exact sigma_conj_invol v (lam u v huv)

/-! ### The three `i ∉ {u,v}` cases, where conjugation does nothing -/

/-- If `i ∉ {u,v}` then `σᵢ` commutes with `ρᵤᵥ`. -/
lemma sigma_conj_rho_neither {n : ℕ} (i u v : Fin n) (huv : u ≠ v)
    (h1 : i ≠ u) (h2 : i ≠ v) : sigma i * rho u v huv * sigma i = rho u v huv := by
  apply mulAut_eq_of_gen_eq
  intro k
  rw [MulAut.mul_apply, MulAut.mul_apply]
  by_cases hki : k = i
  · subst k
    simp only [sigma_apply_self, MulEquiv.map_inv, rho_apply_other huv h1, inv_inv]
  · by_cases hku : k = u
    · subst k
      simp only [sigma_apply_other h1.symm, rho_apply_self, MulEquiv.map_mul,
        sigma_apply_other h2.symm, rho_apply_self]
    · by_cases hkv : k = v
      · subst k
        simp only [sigma_apply_other h2.symm,
          rho_apply_other huv (show v ≠ u from fun h => huv h.symm)]
      · simp only [sigma_apply_other hki, rho_apply_other huv hku]

/-- If `i ∉ {u,v}` then `σᵢ` commutes with `ρᵤᵥ⁻¹`. -/
lemma sigma_conj_rhoNeg_neither {n : ℕ} (i u v : Fin n) (huv : u ≠ v)
    (h1 : i ≠ u) (h2 : i ≠ v) : sigma i * rhoNeg u v huv * sigma i = rhoNeg u v huv := by
  apply mulAut_eq_of_gen_eq
  intro k
  rw [MulAut.mul_apply, MulAut.mul_apply]
  by_cases hki : k = i
  · subst k
    simp only [sigma_apply_self, MulEquiv.map_inv, rhoNeg_apply_other huv h1, inv_inv]
  · by_cases hku : k = u
    · subst k
      simp only [sigma_apply_other h1.symm, rhoNeg_apply_self, MulEquiv.map_mul,
        MulEquiv.map_inv, sigma_apply_other h2.symm, rhoNeg_apply_self]
    · by_cases hkv : k = v
      · subst k
        simp only [sigma_apply_other h2.symm,
          rhoNeg_apply_other huv (show v ≠ u from fun h => huv h.symm)]
      · simp only [sigma_apply_other hki, rhoNeg_apply_other huv hku]

/-- If `i ∉ {u,v}` then `σᵢ` commutes with `λᵤᵥ`. -/
lemma sigma_conj_lam_neither {n : ℕ} (i u v : Fin n) (huv : u ≠ v)
    (h1 : i ≠ u) (h2 : i ≠ v) : sigma i * lam u v huv * sigma i = lam u v huv := by
  apply mulAut_eq_of_gen_eq
  intro k
  rw [MulAut.mul_apply, MulAut.mul_apply]
  by_cases hki : k = i
  · subst k
    simp only [sigma_apply_self, MulEquiv.map_inv, lam_apply_other huv h1, inv_inv]
  · by_cases hku : k = u
    · subst k
      simp only [sigma_apply_other h1.symm, lam_apply_self, MulEquiv.map_mul,
        sigma_apply_other h2.symm, lam_apply_self]
    · by_cases hkv : k = v
      · subst k
        simp only [sigma_apply_other h2.symm,
          lam_apply_other huv (show v ≠ u from fun h => huv h.symm)]
      · simp only [sigma_apply_other hki, lam_apply_other huv hku]

/-- If `i ∉ {u,v}` then `σᵢ` commutes with `λᵤᵥ⁻¹`. -/
lemma sigma_conj_lamNeg_neither {n : ℕ} (i u v : Fin n) (huv : u ≠ v)
    (h1 : i ≠ u) (h2 : i ≠ v) : sigma i * lamNeg u v huv * sigma i = lamNeg u v huv := by
  apply mulAut_eq_of_gen_eq
  intro k
  rw [MulAut.mul_apply, MulAut.mul_apply]
  by_cases hki : k = i
  · subst k
    simp only [sigma_apply_self, MulEquiv.map_inv, lamNeg_apply_other huv h1, inv_inv]
  · by_cases hku : k = u
    · subst k
      simp only [sigma_apply_other h1.symm, lamNeg_apply_self, MulEquiv.map_mul,
        MulEquiv.map_inv, sigma_apply_other h2.symm, lamNeg_apply_self]
    · by_cases hkv : k = v
      · subst k
        simp only [sigma_apply_other h2.symm,
          lamNeg_apply_other huv (show v ≠ u from fun h => huv h.symm)]
      · simp only [sigma_apply_other hki, lamNeg_apply_other huv hku]

/-! ### Membership of the conjugates in `SAutGen n` -/

/-- `σᵢ` conjugates `ρᵤᵥ` into `SAutGen n`. -/
lemma sigma_conj_rho_mem {n : ℕ} (i u v : Fin n) (huv : u ≠ v) :
    sigma i * rho u v huv * sigma i ∈ SAutGen n := by
  classical
  by_cases hiu : i = u
  · rw [hiu]
    rw [SAutGen]
    refine Finset.mem_image.mpr ⟨⟨((u, v), (false, false)), huv⟩, Finset.mem_univ _, ?_⟩
    rw [show sAutAut (⟨((u, v), (false, false)), huv⟩ : SAutIdx n) = lamNeg u v huv by
      simp [sAutAut]]
    exact (sigma_conj_rho_left u v huv).symm
  · by_cases hiv : i = v
    · rw [hiv]
      rw [SAutGen]
      refine Finset.mem_image.mpr ⟨⟨((u, v), (true, false)), huv⟩, Finset.mem_univ _, ?_⟩
      rw [show sAutAut (⟨((u, v), (true, false)), huv⟩ : SAutIdx n) = rhoNeg u v huv by
        simp [sAutAut]]
      exact (sigma_conj_rho_right u v huv).symm
    · rw [SAutGen]
      refine Finset.mem_image.mpr ⟨⟨((u, v), (true, true)), huv⟩, Finset.mem_univ _, ?_⟩
      rw [show sAutAut (⟨((u, v), (true, true)), huv⟩ : SAutIdx n) = rho u v huv by
        simp [sAutAut]]
      exact (sigma_conj_rho_neither i u v huv hiu hiv).symm

/-- `σᵢ` conjugates `ρᵤᵥ⁻¹` into `SAutGen n`. -/
lemma sigma_conj_rhoNeg_mem {n : ℕ} (i u v : Fin n) (huv : u ≠ v) :
    sigma i * rhoNeg u v huv * sigma i ∈ SAutGen n := by
  classical
  by_cases hiu : i = u
  · rw [hiu]
    rw [SAutGen]
    refine Finset.mem_image.mpr ⟨⟨((u, v), (false, true)), huv⟩, Finset.mem_univ _, ?_⟩
    rw [show sAutAut (⟨((u, v), (false, true)), huv⟩ : SAutIdx n) = lam u v huv by
      simp [sAutAut]]
    exact (sigma_conj_rhoNeg_left u v huv).symm
  · by_cases hiv : i = v
    · rw [hiv]
      rw [SAutGen]
      refine Finset.mem_image.mpr ⟨⟨((u, v), (true, true)), huv⟩, Finset.mem_univ _, ?_⟩
      rw [show sAutAut (⟨((u, v), (true, true)), huv⟩ : SAutIdx n) = rho u v huv by
        simp [sAutAut]]
      exact (sigma_conj_rhoNeg_right u v huv).symm
    · rw [SAutGen]
      refine Finset.mem_image.mpr ⟨⟨((u, v), (true, false)), huv⟩, Finset.mem_univ _, ?_⟩
      rw [show sAutAut (⟨((u, v), (true, false)), huv⟩ : SAutIdx n) = rhoNeg u v huv by
        simp [sAutAut]]
      exact (sigma_conj_rhoNeg_neither i u v huv hiu hiv).symm

/-- `σᵢ` conjugates `λᵤᵥ` into `SAutGen n`. -/
lemma sigma_conj_lam_mem {n : ℕ} (i u v : Fin n) (huv : u ≠ v) :
    sigma i * lam u v huv * sigma i ∈ SAutGen n := by
  classical
  by_cases hiu : i = u
  · rw [hiu]
    rw [SAutGen]
    refine Finset.mem_image.mpr ⟨⟨((u, v), (true, false)), huv⟩, Finset.mem_univ _, ?_⟩
    rw [show sAutAut (⟨((u, v), (true, false)), huv⟩ : SAutIdx n) = rhoNeg u v huv by
      simp [sAutAut]]
    exact (sigma_conj_lam_left u v huv).symm
  · by_cases hiv : i = v
    · rw [hiv]
      rw [SAutGen]
      refine Finset.mem_image.mpr ⟨⟨((u, v), (false, false)), huv⟩, Finset.mem_univ _, ?_⟩
      rw [show sAutAut (⟨((u, v), (false, false)), huv⟩ : SAutIdx n) = lamNeg u v huv by
        simp [sAutAut]]
      exact (sigma_conj_lam_right u v huv).symm
    · rw [SAutGen]
      refine Finset.mem_image.mpr ⟨⟨((u, v), (false, true)), huv⟩, Finset.mem_univ _, ?_⟩
      rw [show sAutAut (⟨((u, v), (false, true)), huv⟩ : SAutIdx n) = lam u v huv by
        simp [sAutAut]]
      exact (sigma_conj_lam_neither i u v huv hiu hiv).symm

/-- `σᵢ` conjugates `λᵤᵥ⁻¹` into `SAutGen n`. -/
lemma sigma_conj_lamNeg_mem {n : ℕ} (i u v : Fin n) (huv : u ≠ v) :
    sigma i * lamNeg u v huv * sigma i ∈ SAutGen n := by
  classical
  by_cases hiu : i = u
  · rw [hiu]
    rw [SAutGen]
    refine Finset.mem_image.mpr ⟨⟨((u, v), (true, true)), huv⟩, Finset.mem_univ _, ?_⟩
    rw [show sAutAut (⟨((u, v), (true, true)), huv⟩ : SAutIdx n) = rho u v huv by
      simp [sAutAut]]
    exact (sigma_conj_lamNeg_left u v huv).symm
  · by_cases hiv : i = v
    · rw [hiv]
      rw [SAutGen]
      refine Finset.mem_image.mpr ⟨⟨((u, v), (false, true)), huv⟩, Finset.mem_univ _, ?_⟩
      rw [show sAutAut (⟨((u, v), (false, true)), huv⟩ : SAutIdx n) = lam u v huv by
        simp [sAutAut]]
      exact (sigma_conj_lamNeg_right u v huv).symm
    · rw [SAutGen]
      refine Finset.mem_image.mpr ⟨⟨((u, v), (false, false)), huv⟩, Finset.mem_univ _, ?_⟩
      rw [show sAutAut (⟨((u, v), (false, false)), huv⟩ : SAutIdx n) = lamNeg u v huv by
        simp [sAutAut]]
      exact (sigma_conj_lamNeg_neither i u v huv hiu hiv).symm

/-- Conjugation by the single-generator inversion `sigma i` preserves the
Nielsen transvection generating set `SAutGen n = {ρᵤᵥ^{±1}, λᵤᵥ^{±1}}` of
`SAut(F_n)`.

Concretely, for `g = rho u v` (resp. `rhoNeg u v`, `lam u v`, `lamNeg u v`):
`sigma i * g * sigma i` is again one of these four families, according to
whether the index `i` occurs in `{u,v}`:

* `i ∉ {u,v}`: `sigma i * g * sigma i = g`;
* `i = u` (resp. `i = v`): the exponent of the second generator flips, e.g.
  `sigma i * rho i v * sigma i = rhoNeg i v` and
  `sigma i * rho u i * sigma i = rhoNeg u i`.

(`sigma i` fixes every generator except `a i`, which it inverts.)

Proof suggested route: `rw [SAutGen] at *`, `Finset.mem_image` gives
`p : SAutIdx n` with `sAutAut p = g`; destruct `p` down to
`⟨((u, v), (b, e)), h⟩`; produce the witness index for the conjugate and
compare values on the free generators via `FreeGroup.ext_hom` (using
`rho_apply_self`, `rho_apply_other`, `rhoNeg_apply_self`, `rhoNeg_apply_other`,
`lam_apply_self`, `lam_apply_other`, `lamNeg_apply_self`, `lamNeg_apply_other`,
`sigma_apply_self`, `sigma_apply_other`, and `MulAut.mul_apply`), then conclude
with `Finset.mem_image.mpr`. -/
theorem sigma_conj_mem_SAutGen (n : ℕ) (i : Fin n) {g : MulAut (FreeGroup (Fin n))}
    (hg : g ∈ SAutGen n) : sigma i * g * sigma i ∈ SAutGen n := by
  classical
  rw [SAutGen] at hg
  obtain ⟨p, -, hp⟩ := Finset.mem_image.mp hg
  rw [← hp]
  obtain ⟨⟨⟨u, v⟩, b, e⟩, huv⟩ := p
  cases b <;> cases e <;>
    simp only [sAutAut]
  · exact sigma_conj_lamNeg_mem i u v huv
  · exact sigma_conj_lam_mem i u v huv
  · exact sigma_conj_rhoNeg_mem i u v huv
  · exact sigma_conj_rho_mem i u v huv

end

end Commons.GroupTheory.FreeGroup
