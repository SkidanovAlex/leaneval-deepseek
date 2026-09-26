import Submission.Work.RouteB.MethodI

open OnPropertyT Submission.FreeGroupAut Submission.Helpers
open scoped BigOperators

set_option autoImplicit false

/-!
# The transport `ℝ[Aut(F_n)] → ℝ[Aut(F_m)]` for `n ≤ m`

The paper's computer-assisted certificate lives in `ℝ[Aut(F_5)]`; the
symmetrisation step needs it in `ℝ[Aut(F_m)]`.  The bridge is the group
homomorphism `extendAut : Aut(F_n) →* Aut(F_m)` extending an automorphism of
`F_n` by the identity on the extra generators, together with the induced ring
homomorphism of group rings.  This file builds that transport.
-/

namespace Submission.RouteB

variable {n m : ℕ}

/-! ## The inclusion `F_n → F_m` -/

/-- The embedding `Fin n ↪ Fin m` for `n ≤ m`. -/
def embedFin (h : n ≤ m) (i : Fin n) : Fin m := ⟨i.val, lt_of_lt_of_le i.isLt h⟩

@[simp] lemma embedFin_val (h : n ≤ m) (i : Fin n) : (embedFin h i).val = i.val := rfl

lemma embedFin_injective (h : n ≤ m) : Function.Injective (embedFin h) :=
  fun a b hab => Fin.ext (by simpa using congrArg Fin.val hab)

lemma embedFin_of_val (h : n ≤ m) (j : Fin m) (hj : j.val < n) :
    embedFin h ⟨j.val, hj⟩ = j := Fin.ext rfl

/-- The inclusion of the first `n` generators: `F_n →* F_m`. -/
def inclHom (h : n ≤ m) : FreeGroup (Fin n) →* FreeGroup (Fin m) :=
  FreeGroup.lift (fun i : Fin n => FreeGroup.of (embedFin h i))

lemma inclHom_of (h : n ≤ m) (i : Fin n) :
    inclHom h (FreeGroup.of i) = FreeGroup.of (embedFin h i) :=
  FreeGroup.lift_apply_of

/-- The retraction killing the extra generators. -/
def retractHom (h : n ≤ m) : FreeGroup (Fin m) →* FreeGroup (Fin n) :=
  FreeGroup.lift (fun j : Fin m => if hj : j.val < n then FreeGroup.of ⟨j.val, hj⟩ else 1)

lemma retractHom_of (h : n ≤ m) (j : Fin m) :
    retractHom h (FreeGroup.of j)
      = if hj : j.val < n then FreeGroup.of ⟨j.val, hj⟩ else 1 :=
  FreeGroup.lift_apply_of

lemma retractHom_comp_inclHom (h : n ≤ m) :
    (retractHom h).comp (inclHom h) = MonoidHom.id (FreeGroup (Fin n)) := by
  apply FreeGroup.ext_hom
  intro i
  rw [MonoidHom.comp_apply, MonoidHom.id_apply, inclHom_of, retractHom_of]
  rw [dif_pos (show (embedFin h i).val < n from i.isLt)]
  exact congrArg FreeGroup.of (Fin.ext rfl)

lemma retractHom_inclHom (h : n ≤ m) (x : FreeGroup (Fin n)) :
    retractHom h (inclHom h x) = x :=
  congrFun (congrArg DFunLike.coe (retractHom_comp_inclHom h)) x

lemma inclHom_injective (h : n ≤ m) : Function.Injective (inclHom h) := by
  intro x y hxy
  have hx : x = retractHom h (inclHom h x) := (retractHom_inclHom h x).symm
  rw [hx, hxy, retractHom_inclHom h y]

/-! ## The extension of an endomorphism -/

/-- The extension of a monoid endomorphism of `F_n` to `F_m` (identity on the
extra generators). -/
def extendHom (h : n ≤ m) (α : FreeGroup (Fin n) →* FreeGroup (Fin n)) :
    FreeGroup (Fin m) →* FreeGroup (Fin m) :=
  FreeGroup.lift (fun j : Fin m =>
    if hj : j.val < n then inclHom h (α (FreeGroup.of ⟨j.val, hj⟩)) else FreeGroup.of j)

lemma extendHom_of (h : n ≤ m) (α : FreeGroup (Fin n) →* FreeGroup (Fin n)) (j : Fin m) :
    extendHom h α (FreeGroup.of j)
      = if hj : j.val < n then inclHom h (α (FreeGroup.of ⟨j.val, hj⟩)) else FreeGroup.of j :=
  FreeGroup.lift_apply_of

lemma extendHom_inclHom_of (h : n ≤ m) (α : FreeGroup (Fin n) →* FreeGroup (Fin n))
    (i : Fin n) : extendHom h α (inclHom h (FreeGroup.of i)) = inclHom h (α (FreeGroup.of i)) := by
  rw [inclHom_of, extendHom_of]
  rw [dif_pos (show (embedFin h i).val < n from i.isLt)]
  exact congrArg (fun z : Fin n => inclHom h (α (FreeGroup.of z)))
    (Fin.ext (show (embedFin h i).val = i.val from rfl))

lemma extendHom_inclHom (h : n ≤ m) (α : FreeGroup (Fin n) →* FreeGroup (Fin n))
    (x : FreeGroup (Fin n)) : extendHom h α (inclHom h x) = inclHom h (α x) := by
  have hcomp : (extendHom h α).comp (inclHom h) = (inclHom h).comp α := by
    apply FreeGroup.ext_hom
    intro i
    rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
    exact extendHom_inclHom_of h α i
  exact congrFun (congrArg DFunLike.coe hcomp) x

lemma extendHom_comp_extendHom (h : n ≤ m)
    (α β : FreeGroup (Fin n) →* FreeGroup (Fin n)) :
    (extendHom h α).comp (extendHom h β) = extendHom h (α.comp β) := by
  apply FreeGroup.ext_hom
  intro j
  rw [MonoidHom.comp_apply, extendHom_of]
  by_cases hj : j.val < n
  · rw [dif_pos hj, extendHom_inclHom]
    simp only [extendHom_of, dif_pos hj]
    rfl
  · rw [dif_neg hj]
    simp only [extendHom_of, dif_neg hj]

lemma extendHom_one (h : n ≤ m) :
    extendHom h (MonoidHom.id (FreeGroup (Fin n))) = MonoidHom.id (FreeGroup (Fin m)) := by
  apply FreeGroup.ext_hom
  intro j
  rw [extendHom_of]
  by_cases hj : j.val < n
  · rw [dif_pos hj, MonoidHom.id_apply, inclHom_of,
      embedFin_of_val h j hj, MonoidHom.id_apply]
  · rw [dif_neg hj, MonoidHom.id_apply]

/-! ## The extension of an automorphism -/

/-- The extension of an automorphism of `F_n` to an automorphism of `F_m`. -/
def extendAut (h : n ≤ m) (α : MulAut (FreeGroup (Fin n))) : MulAut (FreeGroup (Fin m)) where
  toFun := extendHom h (α : FreeGroup (Fin n) →* FreeGroup (Fin n))
  invFun := extendHom h ((α⁻¹ : MulAut (FreeGroup (Fin n))) :
    FreeGroup (Fin n) →* FreeGroup (Fin n))
  left_inv x := by
    show extendHom h ((α⁻¹ : MulAut (FreeGroup (Fin n))) : FreeGroup (Fin n) →* FreeGroup (Fin n))
      (extendHom h (α : FreeGroup (Fin n) →* FreeGroup (Fin n)) x) = x
    rw [← MonoidHom.comp_apply, extendHom_comp_extendHom]
    have hinv : ((α⁻¹ : MulAut (FreeGroup (Fin n))) : FreeGroup (Fin n) →* FreeGroup (Fin n)).comp
        (α : FreeGroup (Fin n) →* FreeGroup (Fin n)) = MonoidHom.id (FreeGroup (Fin n)) := by
      apply FreeGroup.ext_hom
      intro i
      rw [MonoidHom.comp_apply, MonoidHom.id_apply]
      simp
    rw [hinv, extendHom_one, MonoidHom.id_apply]
  right_inv x := by
    show extendHom h (α : FreeGroup (Fin n) →* FreeGroup (Fin n))
      (extendHom h ((α⁻¹ : MulAut (FreeGroup (Fin n))) : FreeGroup (Fin n) →* FreeGroup (Fin n)) x) = x
    rw [← MonoidHom.comp_apply, extendHom_comp_extendHom]
    have hinv : (α : FreeGroup (Fin n) →* FreeGroup (Fin n)).comp
        ((α⁻¹ : MulAut (FreeGroup (Fin n))) : FreeGroup (Fin n) →* FreeGroup (Fin n))
        = MonoidHom.id (FreeGroup (Fin n)) := by
      apply FreeGroup.ext_hom
      intro i
      rw [MonoidHom.comp_apply, MonoidHom.id_apply]
      simp
    rw [hinv, extendHom_one, MonoidHom.id_apply]
  map_mul' x y := (extendHom h (α : FreeGroup (Fin n) →* FreeGroup (Fin n))).map_mul x y

@[simp] lemma extendAut_apply (h : n ≤ m) (α : MulAut (FreeGroup (Fin n)))
    (x : FreeGroup (Fin m)) :
    extendAut h α x = extendHom h (α : FreeGroup (Fin n) →* FreeGroup (Fin n)) x := rfl

lemma extendAut_mul (h : n ≤ m) (α β : MulAut (FreeGroup (Fin n))) :
    extendAut h (α * β) = extendAut h α * extendAut h β := by
  have hcoe : ((α * β : MulAut (FreeGroup (Fin n))) : FreeGroup (Fin n) →* FreeGroup (Fin n))
      = (α : FreeGroup (Fin n) →* FreeGroup (Fin n)).comp
          (β : FreeGroup (Fin n) →* FreeGroup (Fin n)) := rfl
  ext x
  rw [MulAut.mul_apply, extendAut_apply, extendAut_apply, extendAut_apply, hcoe,
    ← MonoidHom.comp_apply, extendHom_comp_extendHom]

lemma extendAut_one (h : n ≤ m) : extendAut h (1 : MulAut (FreeGroup (Fin n))) = 1 := by
  ext x
  show extendHom h ((1 : MulAut (FreeGroup (Fin n))) : FreeGroup (Fin n) →* FreeGroup (Fin n)) x = x
  rw [show ((1 : MulAut (FreeGroup (Fin n))) : FreeGroup (Fin n) →* FreeGroup (Fin n))
      = MonoidHom.id (FreeGroup (Fin n)) from rfl, extendHom_one, MonoidHom.id_apply]

/-- The extension map as a monoid homomorphism. -/
def extendAutHom (h : n ≤ m) :
    MulAut (FreeGroup (Fin n)) →* MulAut (FreeGroup (Fin m)) where
  toFun := extendAut h
  map_one' := extendAut_one h
  map_mul' := extendAut_mul h

/-! ## Compatibility with the Nielsen generators -/

lemma extendAut_of (h : n ≤ m) (α : MulAut (FreeGroup (Fin n))) (j : Fin m) :
    extendAut h α (FreeGroup.of j)
      = if hj : j.val < n then inclHom h (α (FreeGroup.of ⟨j.val, hj⟩)) else FreeGroup.of j :=
  FreeGroup.lift_apply_of

lemma extendAut_of_val (h : n ≤ m) (α : MulAut (FreeGroup (Fin n))) (k : Fin m)
    (hk : k.val < n) :
    extendAut h α (FreeGroup.of k) = inclHom h (α (FreeGroup.of ⟨k.val, hk⟩)) := by
  rw [extendAut_of, dif_pos hk]

lemma extendAut_of_not (h : n ≤ m) (α : MulAut (FreeGroup (Fin n))) (k : Fin m)
    (hk : ¬ k.val < n) : extendAut h α (FreeGroup.of k) = FreeGroup.of k := by
  rw [extendAut_of, dif_neg hk]

lemma embedFin_incl_of_val (h : n ≤ m) (k : Fin m) (hk : k.val < n) :
    FreeGroup.of k = inclHom h (FreeGroup.of ⟨k.val, hk⟩) := by
  rw [inclHom_of, embedFin_of_val h k hk]

lemma extendAut_rho_of (h : n ≤ m) {i j : Fin n} (hij : i ≠ j) (k : Fin n) :
    inclHom h (rho i j hij (FreeGroup.of k))
      = rho (embedFin h i) (embedFin h j) (fun hh => hij (embedFin_injective h hh))
          (FreeGroup.of (embedFin h k)) := by
  rcases eq_or_ne k i with rfl | hki
  · rw [rho_apply_self, rho_apply_self, map_mul, inclHom_of, inclHom_of]
  · rw [rho_apply_other hij hki, inclHom_of,
      rho_apply_other _ (fun hh => hki (embedFin_injective h hh))]

lemma extendAut_rhoNeg_of (h : n ≤ m) {i j : Fin n} (hij : i ≠ j) (k : Fin n) :
    inclHom h (rhoNeg i j hij (FreeGroup.of k))
      = rhoNeg (embedFin h i) (embedFin h j) (fun hh => hij (embedFin_injective h hh))
          (FreeGroup.of (embedFin h k)) := by
  rcases eq_or_ne k i with rfl | hki
  · rw [rhoNeg_apply_self, rhoNeg_apply_self, map_mul, map_inv, inclHom_of, inclHom_of]
  · rw [rhoNeg_apply_other hij hki, inclHom_of,
      rhoNeg_apply_other _ (fun hh => hki (embedFin_injective h hh))]

lemma extendAut_lam_of (h : n ≤ m) {i j : Fin n} (hij : i ≠ j) (k : Fin n) :
    inclHom h (lam i j hij (FreeGroup.of k))
      = lam (embedFin h i) (embedFin h j) (fun hh => hij (embedFin_injective h hh))
          (FreeGroup.of (embedFin h k)) := by
  rcases eq_or_ne k i with rfl | hki
  · rw [lam_apply_self, lam_apply_self, map_mul, inclHom_of, inclHom_of]
  · rw [lam_apply_other hij hki, inclHom_of,
      lam_apply_other _ (fun hh => hki (embedFin_injective h hh))]

lemma extendAut_lamNeg_of (h : n ≤ m) {i j : Fin n} (hij : i ≠ j) (k : Fin n) :
    inclHom h (lamNeg i j hij (FreeGroup.of k))
      = lamNeg (embedFin h i) (embedFin h j) (fun hh => hij (embedFin_injective h hh))
          (FreeGroup.of (embedFin h k)) := by
  rcases eq_or_ne k i with rfl | hki
  · rw [lamNeg_apply_self, lamNeg_apply_self, map_mul, map_inv, inclHom_of, inclHom_of]
  · rw [lamNeg_apply_other hij hki, inclHom_of,
      lamNeg_apply_other _ (fun hh => hki (embedFin_injective h hh))]

lemma extendAut_rho (h : n ≤ m) {i j : Fin n} (hij : i ≠ j) :
    extendAut h (rho i j hij)
      = rho (embedFin h i) (embedFin h j) (fun hh => hij (embedFin_injective h hh)) := by
  apply MulEquiv.toMonoidHom_injective
  apply FreeGroup.ext_hom
  intro k
  change extendAut h (rho i j hij) (FreeGroup.of k)
    = rho (embedFin h i) (embedFin h j) (fun hh => hij (embedFin_injective h hh))
        (FreeGroup.of k)
  by_cases hk : k.val < n
  · rw [extendAut_of_val h (rho i j hij) k hk]
    have hgen := extendAut_rho_of h hij ⟨k.val, hk⟩
    rw [embedFin_of_val h k hk] at hgen
    exact hgen
  · rw [extendAut_of_not h (rho i j hij) k hk]
    rw [rho_apply_other _ (fun hh => hk (by rw [hh]; exact i.isLt))]

lemma extendAut_rhoNeg (h : n ≤ m) {i j : Fin n} (hij : i ≠ j) :
    extendAut h (rhoNeg i j hij)
      = rhoNeg (embedFin h i) (embedFin h j) (fun hh => hij (embedFin_injective h hh)) := by
  apply MulEquiv.toMonoidHom_injective
  apply FreeGroup.ext_hom
  intro k
  change extendAut h (rhoNeg i j hij) (FreeGroup.of k)
    = rhoNeg (embedFin h i) (embedFin h j) (fun hh => hij (embedFin_injective h hh))
        (FreeGroup.of k)
  by_cases hk : k.val < n
  · rw [extendAut_of_val h (rhoNeg i j hij) k hk]
    have hgen := extendAut_rhoNeg_of h hij ⟨k.val, hk⟩
    rw [embedFin_of_val h k hk] at hgen
    exact hgen
  · rw [extendAut_of_not h (rhoNeg i j hij) k hk]
    rw [rhoNeg_apply_other _ (fun hh => hk (by rw [hh]; exact i.isLt))]

lemma extendAut_lam (h : n ≤ m) {i j : Fin n} (hij : i ≠ j) :
    extendAut h (lam i j hij)
      = lam (embedFin h i) (embedFin h j) (fun hh => hij (embedFin_injective h hh)) := by
  apply MulEquiv.toMonoidHom_injective
  apply FreeGroup.ext_hom
  intro k
  change extendAut h (lam i j hij) (FreeGroup.of k)
    = lam (embedFin h i) (embedFin h j) (fun hh => hij (embedFin_injective h hh))
        (FreeGroup.of k)
  by_cases hk : k.val < n
  · rw [extendAut_of_val h (lam i j hij) k hk]
    have hgen := extendAut_lam_of h hij ⟨k.val, hk⟩
    rw [embedFin_of_val h k hk] at hgen
    exact hgen
  · rw [extendAut_of_not h (lam i j hij) k hk]
    rw [lam_apply_other _ (fun hh => hk (by rw [hh]; exact i.isLt))]

lemma extendAut_lamNeg (h : n ≤ m) {i j : Fin n} (hij : i ≠ j) :
    extendAut h (lamNeg i j hij)
      = lamNeg (embedFin h i) (embedFin h j) (fun hh => hij (embedFin_injective h hh)) := by
  apply MulEquiv.toMonoidHom_injective
  apply FreeGroup.ext_hom
  intro k
  change extendAut h (lamNeg i j hij) (FreeGroup.of k)
    = lamNeg (embedFin h i) (embedFin h j) (fun hh => hij (embedFin_injective h hh))
        (FreeGroup.of k)
  by_cases hk : k.val < n
  · rw [extendAut_of_val h (lamNeg i j hij) k hk]
    have hgen := extendAut_lamNeg_of h hij ⟨k.val, hk⟩
    rw [embedFin_of_val h k hk] at hgen
    exact hgen
  · rw [extendAut_of_not h (lamNeg i j hij) k hk]
    rw [lamNeg_apply_other _ (fun hh => hk (by rw [hh]; exact i.isLt))]

lemma extendAut_sigma_of (h : n ≤ m) (i k : Fin n) :
    inclHom h (sigma i (FreeGroup.of k))
      = sigma (embedFin h i) (FreeGroup.of (embedFin h k)) := by
  rcases eq_or_ne k i with rfl | hki
  · rw [sigma_apply_self, sigma_apply_self, map_inv, inclHom_of]
  · rw [sigma_apply_other hki, inclHom_of,
      sigma_apply_other (fun hh => hki (embedFin_injective h hh))]

lemma extendAut_sigma (h : n ≤ m) (i : Fin n) :
    extendAut h (sigma i) = sigma (embedFin h i) := by
  apply MulEquiv.toMonoidHom_injective
  apply FreeGroup.ext_hom
  intro k
  change extendAut h (sigma i) (FreeGroup.of k) = sigma (embedFin h i) (FreeGroup.of k)
  by_cases hk : k.val < n
  · rw [extendAut_of_val h (sigma i) k hk]
    have hgen := extendAut_sigma_of h i ⟨k.val, hk⟩
    rw [embedFin_of_val h k hk] at hgen
    exact hgen
  · rw [extendAut_of_not h (sigma i) k hk]
    rw [sigma_apply_other (fun hh => hk (by rw [hh]; exact i.isLt))]

/-! ## The induced ring homomorphism and the transport of the edge Laplacians -/

lemma extendAut_injective (h : n ≤ m) : Function.Injective (extendAut h) := by
  intro α β hab
  have hgen : ∀ i : Fin n, α (FreeGroup.of i) = β (FreeGroup.of i) := by
    intro i
    have h1 : extendAut h α (inclHom h (FreeGroup.of i))
        = extendAut h β (inclHom h (FreeGroup.of i)) := by rw [hab]
    rw [extendAut_apply, extendAut_apply, extendHom_inclHom, extendHom_inclHom] at h1
    exact inclHom_injective h h1
  have hhom : (α : FreeGroup (Fin n) →* FreeGroup (Fin n))
      = (β : FreeGroup (Fin n) →* FreeGroup (Fin n)) := FreeGroup.ext_hom _ _ hgen
  exact MulEquiv.ext (fun v => congrFun (congrArg DFunLike.coe hhom) v)

/-- The ring homomorphism of group rings induced by `extendAut`. -/
noncomputable def extendRingHom (h : n ≤ m) :
    MonoidAlgebra ℝ (MulAut (FreeGroup (Fin n))) →+*
      MonoidAlgebra ℝ (MulAut (FreeGroup (Fin m))) :=
  MonoidAlgebra.mapDomainRingHom ℝ (extendAutHom h)

lemma extendRingHom_apply (h : n ≤ m) :
    ⇑(extendRingHom h) = MonoidAlgebra.mapDomain (extendAutHom h) := rfl

lemma extendRingHom_star (h : n ≤ m)
    (x : MonoidAlgebra ℝ (MulAut (FreeGroup (Fin n)))) :
    extendRingHom h (star x) = star (extendRingHom h x) :=
  (Submission.Helpers.mapDomain_hom_star (extendAutHom h) x).symm

namespace Edge

/-- The edge of the `m`-simplex spanned by the images of the vertices of an edge
of the `n`-simplex. -/
noncomputable def embedEdge (h : n ≤ m) (p : Edge n) : Edge m :=
  edgeOf (embedFin h p.1.1) (embedFin h p.1.2)
    (fun hh => ne_of_lt p.2 (embedFin_injective h hh))

lemma embedEdge_toFinset (h : n ≤ m) (p : Edge n) :
    (embedEdge h p).toFinset = p.toFinset.image (embedFin h) := by
  rw [embedEdge, toFinset_edgeOf, toFinset, Finset.image_insert,
    Finset.image_singleton]

lemma embedEdge_injective (h : n ≤ m) : Function.Injective (embedEdge h) := by
  intro p q hpq
  have h1 : p.toFinset.image (embedFin h) = q.toFinset.image (embedFin h) := by
    rw [← embedEdge_toFinset, ← embedEdge_toFinset]
    exact congrArg toFinset hpq
  exact toFinset_injective ((Finset.image_inj (embedFin_injective h)).mp h1)

lemma edgeOf_val_lt {i j : Fin m} (hij : i ≠ j) {n : ℕ} (hi : i.val < n) (hj : j.val < n) :
    (edgeOf i j hij).1.1.val < n ∧ (edgeOf i j hij).1.2.val < n := by
  unfold edgeOf
  split
  · exact ⟨hi, hj⟩
  · exact ⟨hj, hi⟩

lemma embedEdge_mem_Esub (h : n ≤ m) {p : Edge n} (hp : p ∈ Esub n n) :
    embedEdge h p ∈ Esub m n := by
  rw [mem_Esub] at hp ⊢
  have h1 : (embedFin h p.1.1).val < n := by simpa using hp.1
  have h2 : (embedFin h p.1.2).val < n := by simpa using hp.2
  exact edgeOf_val_lt (fun hh => ne_of_lt p.2 (embedFin_injective h hh)) h1 h2

lemma dirEdge_image_extend (h : n ≤ m) {i j : Fin n} (hij : i ≠ j) :
    (dirEdge i j hij).image (extendAut h)
      = dirEdge (embedFin h i) (embedFin h j) (fun hh => hij (embedFin_injective h hh)) := by
  ext x
  rw [Finset.mem_image]
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [mem_dirEdge] at hg ⊢
    rcases hg with hg1 | hg1 | hg1 | hg1
    · exact Or.inl (hg1 ▸ extendAut_rho h hij)
    · exact Or.inr (Or.inl (hg1 ▸ extendAut_rhoNeg h hij))
    · exact Or.inr (Or.inr (Or.inl (hg1 ▸ extendAut_lam h hij)))
    · exact Or.inr (Or.inr (Or.inr (hg1 ▸ extendAut_lamNeg h hij)))
  · intro hx
    rw [mem_dirEdge] at hx
    rcases hx with h | h | h | h
    · exact ⟨rho i j hij, by rw [mem_dirEdge]; exact Or.inl rfl,
        by rw [h, extendAut_rho]⟩
    · exact ⟨rhoNeg i j hij, by rw [mem_dirEdge]; exact Or.inr (Or.inl rfl),
        by rw [h, extendAut_rhoNeg]⟩
    · exact ⟨lam i j hij, by rw [mem_dirEdge]; exact Or.inr (Or.inr (Or.inl rfl)),
        by rw [h, extendAut_lam]⟩
    · exact ⟨lamNeg i j hij, by rw [mem_dirEdge]; exact Or.inr (Or.inr (Or.inr rfl)),
        by rw [h, extendAut_lamNeg]⟩

lemma sEdgeOf_image_extend (h : n ≤ m) {i j : Fin n} (hij : i ≠ j) :
    (sEdgeOf i j hij).image (extendAut h)
      = sEdgeOf (embedFin h i) (embedFin h j) (fun hh => hij (embedFin_injective h hh)) := by
  rw [sEdgeOf, sEdgeOf, Finset.image_union, dirEdge_image_extend, dirEdge_image_extend]

lemma SEdge_image_extend (h : n ≤ m) (p : Edge n) :
    (SEdge p).image (extendAut h) = SEdge (embedEdge h p) := by
  have h1 : (SEdge p).image (extendAut h)
      = sEdgeOf (embedFin h p.1.1) (embedFin h p.1.2)
          (fun hh => ne_of_lt p.2 (embedFin_injective h hh)) := by
    rw [SEdge_def]
    exact sEdgeOf_image_extend h (ne_of_lt p.2)
  rw [h1, embedEdge, SEdge_eq_sEdgeOf_edgeOf]

theorem extendRingHom_edgeLap (h : n ≤ m) (p : Edge n) :
    extendRingHom h (edgeLap p) = edgeLap (embedEdge h p) := by
  have hmap : extendRingHom h (edgeLap p)
      = MonoidAlgebra.mapDomain (extendAutHom h) (OnPropertyT.Laplacian (SEdge p)) := by
    rw [edgeLap, extendRingHom_apply]
  rw [hmap, Submission.PropertyT.mapDomain_laplacian (extendAutHom h) (SEdge p)
    (fun a _ b _ hab => extendAut_injective h hab)]
  change OnPropertyT.Laplacian ((SEdge p).image (extendAut h)) = edgeLap (embedEdge h p)
  rw [edgeLap, SEdge_image_extend]

/-- The transport of the sub-simplex Laplacian: the edges of the `n`-simplex are
exactly the edges of the sub-simplex on the first `n` vertices of the `m`-simplex. -/
theorem extendRingHom_deltaSub_self (h : n ≤ m) :
    extendRingHom h (deltaSub n n) = deltaSub m n := by
  rw [deltaSub_eq_sum, deltaSub_eq_sum, map_sum]
  rw [Finset.sum_congr rfl (fun p _ => extendRingHom_edgeLap h p)]
  refine Finset.sum_bij (fun p _ => embedEdge h p) (fun p hp => embedEdge_mem_Esub h hp)
    (fun p _ q _ hpq => embedEdge_injective h hpq) ?_ (fun p _ => rfl)
  intro q hq
  rw [mem_Esub] at hq
  refine ⟨edgeOf ⟨q.1.1.val, hq.1⟩ ⟨q.1.2.val, hq.2⟩
    (fun hh => ne_of_lt q.2 (Fin.ext (congrArg (fun x : Fin n => x.val) hh))), ?_, ?_⟩
  · rw [mem_Esub]
    exact ⟨(by simp), (by simp)⟩
  · apply toFinset_injective
    rw [embedEdge_toFinset, toFinset_edgeOf, Finset.image_insert, Finset.image_singleton,
      embedFin_of_val h q.1.1 hq.1, embedFin_of_val h q.1.2 hq.2, toFinset]

/-! ## The transport of the pair sums `Sq`, `Adj`, `Op` -/

lemma disjoint_image_iff {α β : Type*} [DecidableEq α] [DecidableEq β] (f : α → β)
    (hf : Function.Injective f)
    {s t : Finset α} : Disjoint (s.image f) (t.image f) ↔ Disjoint s t := by
  rw [Finset.disjoint_iff_inter_eq_empty, Finset.disjoint_iff_inter_eq_empty,
    ← Finset.image_inter s t hf, Finset.image_eq_empty]

lemma adj_embedEdge_iff (h : n ≤ m) (p q : Edge n) :
    Adj (embedEdge h p) (embedEdge h q) ↔ Adj p q := by
  rw [Adj, Adj, embedEdge_toFinset, embedEdge_toFinset,
    disjoint_image_iff (embedFin h) (embedFin_injective h)]
  refine and_congr ?_ Iff.rfl
  exact ⟨fun hh he => hh (by rw [he]), fun hh he => hh (embedEdge_injective h he)⟩

lemma op_embedEdge_iff (h : n ≤ m) (p q : Edge n) :
    Op (embedEdge h p) (embedEdge h q) ↔ Op p q := by
  rw [Op, Op, embedEdge_toFinset, embedEdge_toFinset,
    disjoint_image_iff (embedFin h) (embedFin_injective h)]

lemma embedEdgePair_mem_Dsub (h : n ≤ m) {x : Edge n × Edge n} (hx : x ∈ Dsub n n) :
    (embedEdge h x.1, embedEdge h x.2) ∈ Dsub m n := by
  rw [mem_Dsub] at hx ⊢
  refine ⟨by rw [hx.1], ?_⟩
  rw [← hx.1]
  exact embedEdge_mem_Esub h hx.2

lemma embedEdgePair_mem_Psub (h : n ≤ m) {x : Edge n × Edge n} (hx : x ∈ Psub n n) :
    (embedEdge h x.1, embedEdge h x.2) ∈ Psub m n := by
  rw [mem_Psub] at hx ⊢
  exact ⟨(adj_embedEdge_iff h x.1 x.2).mpr hx.1, embedEdge_mem_Esub h hx.2.1,
    embedEdge_mem_Esub h hx.2.2⟩

lemma embedEdgePair_mem_Qsub (h : n ≤ m) {x : Edge n × Edge n} (hx : x ∈ Qsub n n) :
    (embedEdge h x.1, embedEdge h x.2) ∈ Qsub m n := by
  rw [mem_Qsub] at hx ⊢
  exact ⟨(op_embedEdge_iff h x.1 x.2).mpr hx.1, embedEdge_mem_Esub h hx.2.1,
    embedEdge_mem_Esub h hx.2.2⟩

lemma embedEdgePair_injective (h : n ≤ m) :
    Function.Injective (fun x : Edge n × Edge n => (embedEdge h x.1, embedEdge h x.2)) := by
  intro x y hxy
  have h1 : embedEdge h x.1 = embedEdge h y.1 := congrArg Prod.fst hxy
  have h2 : embedEdge h x.2 = embedEdge h y.2 := congrArg Prod.snd hxy
  exact Prod.ext (embedEdge_injective h h1) (embedEdge_injective h h2)

/-- The preimage of an edge of the sub-simplex under `embedEdge`. -/
noncomputable def preEdge (h : n ≤ m) (q : Edge m) (hq : q ∈ Esub m n) : Edge n :=
  edgeOf ⟨q.1.1.val, (mem_Esub.mp hq).1⟩ ⟨q.1.2.val, (mem_Esub.mp hq).2⟩
    (fun hh => ne_of_lt q.2 (Fin.ext (congrArg (fun x : Fin n => x.val) hh)))

lemma embedEdge_preEdge (h : n ≤ m) (q : Edge m) (hq : q ∈ Esub m n) :
    embedEdge h (preEdge h q hq) = q := by
  apply toFinset_injective
  rw [embedEdge_toFinset, preEdge, toFinset_edgeOf, Finset.image_insert, Finset.image_singleton,
    embedFin_of_val h q.1.1 (mem_Esub.mp hq).1, embedFin_of_val h q.1.2 (mem_Esub.mp hq).2,
    toFinset]

theorem extendRingHom_SqPair_self (h : n ≤ m) :
    extendRingHom h (SqPair n n) = SqPair m n := by
  rw [SqPair, SqPair, map_sum]
  rw [Finset.sum_congr rfl (fun x _ => by
    rw [map_mul, extendRingHom_edgeLap, extendRingHom_edgeLap])]
  refine Finset.sum_bij (fun x _ => (embedEdge h x.1, embedEdge h x.2))
    (fun x hx => embedEdgePair_mem_Dsub h hx)
    (fun x _ y _ hxy => embedEdgePair_injective h hxy) ?_ (fun x _ => rfl)
  intro y hy
  rw [mem_Dsub] at hy
  refine ⟨(preEdge h y.1 hy.2, preEdge h y.1 hy.2), ?_, ?_⟩
  · rw [mem_Dsub]
    exact ⟨rfl, by rw [Esub_self]; exact Finset.mem_univ _⟩
  · exact Prod.ext (embedEdge_preEdge h y.1 hy.2) (by
      rw [embedEdge_preEdge h y.1 hy.2, hy.1])

theorem extendRingHom_AdjPair_self (h : n ≤ m) :
    extendRingHom h (AdjPair n n) = AdjPair m n := by
  rw [AdjPair, AdjPair, map_sum]
  rw [Finset.sum_congr rfl (fun x _ => by
    rw [map_mul, extendRingHom_edgeLap, extendRingHom_edgeLap])]
  refine Finset.sum_bij (fun x _ => (embedEdge h x.1, embedEdge h x.2))
    (fun x hx => embedEdgePair_mem_Psub h hx)
    (fun x _ y _ hxy => embedEdgePair_injective h hxy) ?_ (fun x _ => rfl)
  intro y hy
  rw [mem_Psub] at hy
  refine ⟨(preEdge h y.1 hy.2.1, preEdge h y.2 hy.2.2), ?_, ?_⟩
  · rw [mem_Psub]
    refine ⟨?_, by rw [Esub_self]; exact Finset.mem_univ _,
      by rw [Esub_self]; exact Finset.mem_univ _⟩
    show Adj (preEdge h y.1 hy.2.1) (preEdge h y.2 hy.2.2)
    rw [← adj_embedEdge_iff h, embedEdge_preEdge h y.1 hy.2.1,
      embedEdge_preEdge h y.2 hy.2.2]
    exact hy.1
  · exact Prod.ext (embedEdge_preEdge h y.1 hy.2.1) (embedEdge_preEdge h y.2 hy.2.2)

theorem extendRingHom_OpPair_self (h : n ≤ m) :
    extendRingHom h (OpPair n n) = OpPair m n := by
  rw [OpPair, OpPair, map_sum]
  rw [Finset.sum_congr rfl (fun x _ => by
    rw [map_mul, extendRingHom_edgeLap, extendRingHom_edgeLap])]
  refine Finset.sum_bij (fun x _ => (embedEdge h x.1, embedEdge h x.2))
    (fun x hx => embedEdgePair_mem_Qsub h hx)
    (fun x _ y _ hxy => embedEdgePair_injective h hxy) ?_ (fun x _ => rfl)
  intro y hy
  rw [mem_Qsub] at hy
  refine ⟨(preEdge h y.1 hy.2.1, preEdge h y.2 hy.2.2), ?_, ?_⟩
  · rw [mem_Qsub]
    refine ⟨?_, by rw [Esub_self]; exact Finset.mem_univ _,
      by rw [Esub_self]; exact Finset.mem_univ _⟩
    show Op (preEdge h y.1 hy.2.1) (preEdge h y.2 hy.2.2)
    rw [← op_embedEdge_iff h, embedEdge_preEdge h y.1 hy.2.1,
      embedEdge_preEdge h y.2 hy.2.2]
    exact hy.1
  · exact Prod.ext (embedEdge_preEdge h y.1 hy.2.1) (embedEdge_preEdge h y.2 hy.2.2)

end Edge

end Submission.RouteB
