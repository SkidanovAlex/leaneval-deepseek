import ChallengeDeps
import Mathlib.GroupTheory.FreeGroup.Basic

set_option autoImplicit false

namespace Submission.FreeGroupAut

noncomputable section

variable {n : ℕ}

/-- The free group on `Fin n`, with basis element `a i = FreeGroup.of i`. -/
abbrev a (i : Fin n) : FreeGroup (Fin n) := FreeGroup.of i

/-- Right Nielsen transvection with exponent `+1`: sends `a_i ↦ a_i * a_j`. -/
def rhoHom (i j : Fin n) : FreeGroup (Fin n) →* FreeGroup (Fin n) :=
  FreeGroup.lift (fun k : Fin n => if k = i then a i * a j else a k)

/-- Right Nielsen transvection with exponent `-1`: sends `a_i ↦ a_i * a_j⁻¹`. -/
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

/-- The right Nielsen transvection `rho_{ij}` (`a_i ↦ a_i * a_j`), for `i ≠ j`. -/
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

/-- The right Nielsen transvection with exponent `-1` is the inverse of `rho`. -/
lemma rho_inv (i j : Fin n) (hij : i ≠ j) :
    (rho i j hij)⁻¹ = rhoInvHom i j := by
  -- both are the unique inverse; compute inverse of MulEquiv:
  rfl


/-- `rho` sends the `i`-th generator to `a_i * a_j`. -/
lemma rho_apply_self (i j : Fin n) (hij : i ≠ j) :
    (rho i j hij) (a i) = a i * a j := by
  simp [rho, rhoHom]

/-- `rho` fixes the generators other than `a_i`. -/
lemma rho_apply_other {i j k : Fin n} (hij : i ≠ j) (hk : k ≠ i) :
    (rho i j hij) (a k) = a k := by
  simp [rho, rhoHom, hk]

/-- Right Nielsen transvection with exponent `-1` as an automorphism. -/
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

/-- The inverse of `rho` is the transvection with exponent `-1`. -/
lemma rho_inv_eq (i j : Fin n) (hij : i ≠ j) :
    (rho i j hij)⁻¹ = rhoNeg i j hij := by
  ext x
  rfl

/-- `rhoNeg` sends the `i`-th generator to `a_i * a_j⁻¹`. -/
lemma rhoNeg_apply_self (i j : Fin n) (hij : i ≠ j) :
    (rhoNeg i j hij) (a i) = a i * (a j)⁻¹ := by
  simp [rhoNeg, rhoInvHom]

/-- Left Nielsen transvection with exponent `+1`: sends `a_i ↦ a_j * a_i`. -/
def lamHom (i j : Fin n) : FreeGroup (Fin n) →* FreeGroup (Fin n) :=
  FreeGroup.lift (fun k : Fin n => if k = i then a j * a i else a k)

/-- Left Nielsen transvection with exponent `-1`: sends `a_i ↦ a_j⁻¹ * a_i`. -/
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

/-- The left Nielsen transvection `lambda_{ij}` (`a_i ↦ a_j * a_i`), for `i ≠ j`. -/
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

/-- `lam` sends the `i`-th generator to `a_j * a_i`. -/
lemma lam_apply_self (i j : Fin n) (hij : i ≠ j) :
    (lam i j hij) (a i) = a j * a i := by
  simp [lam, lamHom]

/-- `lam` fixes the generators other than `a_i`. -/
lemma lam_apply_other {i j k : Fin n} (hij : i ≠ j) (hk : k ≠ i) :
    (lam i j hij) (a k) = a k := by
  simp [lam, lamHom, hk]

/-- Left Nielsen transvection with exponent `-1` as an automorphism. -/
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

/-- The inverse of `lam` is the transvection with exponent `-1`. -/
lemma lam_inv_eq (i j : Fin n) (hij : i ≠ j) :
    (lam i j hij)⁻¹ = lamNeg i j hij := by
  ext x
  rfl

/-- `lamNeg` sends the `i`-th generator to `a_j⁻¹ * a_i`. -/
lemma lamNeg_apply_self (i j : Fin n) (hij : i ≠ j) :
    (lamNeg i j hij) (a i) = (a j)⁻¹ * a i := by
  simp [lamNeg, lamInvHom]

/-- Homomorphism inverting the single basis element `a_i`. -/
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

/-- The automorphism inverting the single basis element `a_i`. -/
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

/-- The inverse of `rhoNeg` is `rho`. -/
lemma rhoNeg_inv_eq (i j : Fin n) (hij : i ≠ j) :
    (rhoNeg i j hij)⁻¹ = rho i j hij := by
  ext x
  rfl

/-- The inverse of `lamNeg` is `lam`. -/
lemma lamNeg_inv_eq (i j : Fin n) (hij : i ≠ j) :
    (lamNeg i j hij)⁻¹ = lam i j hij := by
  ext x
  rfl
/-- Index type for the Nielsen generators of `SAut(F_n)`: an ordered pair `(i,j)`
with `i ≠ j`, a left/right flag and an exponent flag. -/
abbrev SAutIdx (n : ℕ) := {p : (Fin n × Fin n) × (Bool × Bool) // p.1.1 ≠ p.1.2}

/-- The automorphism of `SAut(F_n)` indexed by `p` (right or left Nielsen transvection,
exponent `±1`). -/
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

/-- The Nielsen generating set of `SAut(F_n)` (the paper's generating set
`{ρᵢⱼ^{±1}, λᵢⱼ^{±1}}`, `i ≠ j`). -/
noncomputable def SAutGen (n : ℕ) : Finset (MulAut (FreeGroup (Fin n))) := by
  classical
  exact Finset.univ.image sAutAut

/-- The index obtained from `p` by flipping the exponent. -/
def SAutIdx_invExp {n : ℕ} (p : SAutIdx n) : SAutIdx n :=
  match p with
  | ⟨(ij, (b, e)), h⟩ =>
    match ij with
    | (i, j) => ⟨((i, j), (b, if e then false else true)), h⟩

/-- Every Nielsen generator is invertible within the generating set. -/
lemma sAutAut_inv_exists {n : ℕ} (p : SAutIdx n) :
    ∃ q : SAutIdx n, sAutAut q = (sAutAut p)⁻¹ := by
  classical
  refine ⟨SAutIdx_invExp p, ?_⟩
  rcases p with ⟨v, h⟩
  rcases v with ⟨ij, be⟩
  rcases ij with ⟨i, j⟩
  rcases be with ⟨b, e⟩
  simp [SAutIdx_invExp, sAutAut]
  by_cases hb : b
  · by_cases he : e
    · simp [hb, he]
      exact (rho_inv_eq i j h).symm
    · simp [hb, he]
      exact (rhoNeg_inv_eq i j h).symm
  · by_cases he : e
    · simp [hb, he]
      exact (lam_inv_eq i j h).symm
    · simp [hb, he]
      exact (lamNeg_inv_eq i j h).symm

/-- Inverses of Nielsen generators stay in the generating set. -/
lemma sAutAut_inv_mem (n : ℕ) (p : SAutIdx n) : (sAutAut p)⁻¹ ∈ (SAutGen n : Set (MulAut (FreeGroup (Fin n)))) := by
  classical
  rw [SAutGen]
  rcases sAutAut_inv_exists p with ⟨q, hq⟩
  exact Finset.mem_image.mpr ⟨q, Finset.mem_univ q, hq⟩

/-- The Nielsen generating set of `SAut(F_n)` is symmetric. -/
lemma sAutGen_symm (n : ℕ) : ((SAutGen n : Set (MulAut (FreeGroup (Fin n))))⁻¹) = (SAutGen n : Set (MulAut (FreeGroup (Fin n)))) := by
  classical
  ext g
  constructor
  · intro hg
    have hg' : g⁻¹ ∈ (SAutGen n : Set (MulAut (FreeGroup (Fin n)))) := Set.mem_inv.mp hg
    rw [SAutGen] at hg'
    rcases (Finset.mem_image.mp hg') with ⟨p, hp, hpg⟩
    rcases sAutAut_inv_exists p with ⟨q, hq⟩
    rw [SAutGen]
    refine Finset.mem_image.mpr ⟨q, Finset.mem_univ q, ?_⟩
    calc
      sAutAut q = (sAutAut p)⁻¹ := hq
      _ = g := by
        rw [hpg]
        simp
  · intro hg
    rw [SAutGen] at hg
    rcases (Finset.mem_image.mp hg) with ⟨p, hp, hgp⟩
    rcases sAutAut_inv_exists p with ⟨q, hq⟩
    rw [SAutGen]
    apply Set.mem_inv.mpr
    refine Finset.mem_image.mpr ⟨q, Finset.mem_univ q, ?_⟩
    calc
      sAutAut q = (sAutAut p)⁻¹ := hq
      _ = g⁻¹ := by rw [hgp]

/-- The single-generator inversions `sigma i`. -/
noncomputable def SigmaSet (n : ℕ) : Finset (MulAut (FreeGroup (Fin n))) := by
  classical
  exact Finset.univ.image (sigma : Fin n → MulAut (FreeGroup (Fin n)))
/-- The set of single-generator inversions is symmetric. -/
lemma sigmaSet_symm (n : ℕ) : ((SigmaSet n : Set (MulAut (FreeGroup (Fin n))))⁻¹)
    = (SigmaSet n : Set (MulAut (FreeGroup (Fin n)))) := by
  classical
  rw [SigmaSet]
  rw [Finset.coe_image]
  simp
  ext g
  constructor
  · intro hg
    have hg' : g⁻¹ ∈ Set.range (sigma : Fin n → MulAut (FreeGroup (Fin n))) := Set.mem_inv.mp hg
    rcases hg' with ⟨i, hi⟩
    refine ⟨i, ?_⟩
    have hinv : (sigma i)⁻¹ = g := by
      -- from sigma i = g⁻¹
      calc
        (sigma i)⁻¹ = (g⁻¹)⁻¹ := by rw [hi]
        _ = g := by simp
    calc
      sigma i = (sigma i)⁻¹ := (sigma_inv i).symm
      _ = g := hinv
  · intro hg
    rcases hg with ⟨i, hi⟩
    apply Set.mem_inv.mpr
    refine ⟨i, ?_⟩
    calc
      sigma i = (sigma i)⁻¹ := (sigma_inv i).symm
      _ = g⁻¹ := by rw [hi]

/-- The full generating set of `Aut(F_n)` (Nielsen generators plus all inversions). -/
noncomputable def AutGen (n : ℕ) : Finset (MulAut (FreeGroup (Fin n))) := by
  classical
  exact SAutGen n ∪ SigmaSet n

/-- The full generating set `AutGen n` is symmetric. -/
lemma autGen_symm (n : ℕ) : ((AutGen n : Set (MulAut (FreeGroup (Fin n))))⁻¹)
    = (AutGen n : Set (MulAut (FreeGroup (Fin n)))) := by
  classical
  rw [AutGen]
  rw [Finset.coe_union]
  have h : ((↑(SAutGen n) ∪ ↑(SigmaSet n) : Set (MulAut (FreeGroup (Fin n))))⁻¹)
      = (↑(SAutGen n))⁻¹ ∪ (↑(SigmaSet n))⁻¹ := by
    ext x
    simp [Set.mem_inv]
  rw [h]
  rw [sAutGen_symm n]
  rw [sigmaSet_symm n]
/-- `rhoNeg` fixes the generators other than `a_i`. -/
lemma rhoNeg_apply_other {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hk : k ≠ i) :
    (rhoNeg i j hij) (a k) = a k := by
  simp [rhoNeg, rhoInvHom, hk]

/-- `lamNeg` fixes the generators other than `a_i`. -/
lemma lamNeg_apply_other {n : ℕ} {i j k : Fin n} (hij : i ≠ j) (hk : k ≠ i) :
    (lamNeg i j hij) (a k) = a k := by
  simp [lamNeg, lamInvHom, hk]

end

end Submission.FreeGroupAut
