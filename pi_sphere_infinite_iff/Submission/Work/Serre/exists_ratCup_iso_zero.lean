import Mathlib
import Submission.Work.Serre.Engine
import Submission.Work.Cohomology.CupRing
import Submission.Work.StemsB.FieldDualUCT
import Submission.Work.Serre.ratCup_unit_exists
import Submission.Work.Serre.ratH_zero_of_pathConnected

/-!
# A cup-product isomorphism in degree `r + 1` for a space with `H_{r+1}(B;ℚ) ≅ ℚ`

Let `B` be a path-connected space with `H_{r+1}(B;ℚ) ≅ ℚ` (`r ≥ 1`).  Then there is a class
`e ∈ H^{r+1}(B;ℚ)` such that cupping with `e` is an isomorphism `H^0(B;ℚ) → H^{r+1}(B;ℚ)`.

The proof is the elementary one:

* `H^{r+1}(B;ℚ) ≅ ℚ` from the hypothesis by the universal coefficient theorem over the field `ℚ`
  (`Work.StemsB.ratDualUCT`), and `H^0(B;ℚ) ≅ ℚ` since `B` is path connected;
* choose `e` to be the image of `1` under `ℚ ≅ H^{r+1}(B;ℚ)`;
* since both `H^0(B;ℚ)` and `H^{r+1}(B;ℚ)` are isomorphic to `ℚ`, it suffices to see that the
  map `x ↦ x ⌣ e` is non-zero; this holds because `1 ⌣ e = e ≠ 0`, where `1` is the unit class
  of the cup-product ring (`Work.Serre.ratCup_unit_exists`).

Everything is over `ℚ`, so no torsion or divisibility issues arise.
-/

namespace Work.Serre

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-! ## Elementary lemmas about `ℚ`-linear maps `ℚ → ℚ` and about conjugation by isomorphisms -/

/-- A `ℚ`-linear endomorphism of `ℚ` is determined by its value at `1`; hence if that value is
non-zero the map is a bijection (it is multiplication by a non-zero scalar). -/
theorem ratCupAux_ratEnd_bijective_of_apply_one_ne_zero {g : ℚ →ₗ[ℚ] ℚ} (h : g 1 ≠ 0) :
    Function.Bijective g := by
  constructor
  · intro x y hxy
    have hx : g x = x * g 1 := by simpa using map_smul g x (1 : ℚ)
    have hy : g y = y * g 1 := by simpa using map_smul g y (1 : ℚ)
    rw [hx, hy] at hxy
    exact mul_right_cancel₀ h hxy
  · intro y
    refine ⟨y / g 1, ?_⟩
    have hx : g (y / g 1) = (y / g 1) * g 1 := by
      simpa using map_smul g (y / g 1) (1 : ℚ)
    rw [hx]
    field_simp

/-- The previous lemma in the form used below: a `ℚ`-linear endomorphism of `ℚ` which is non-zero
at `1` is non-zero. -/
theorem ratCupAux_ratEnd_ne_zero_of_apply_one_ne_zero {g : ℚ →ₗ[ℚ] ℚ} (h : g 1 ≠ 0) :
    g ≠ 0 := by
  intro hg
  exact h (by rw [hg]; rfl)

/-- A non-zero `ℚ`-linear endomorphism of `ℚ` is an isomorphism of `ℚ`-modules. -/
theorem ratCupAux_isIso_ofHom_rat_ne_zero (g : ℚ →ₗ[ℚ] ℚ) (hg : g ≠ 0) :
    IsIso (ModuleCat.ofHom g) := by
  have hg1 : g 1 ≠ 0 := by
    intro h
    apply hg
    refine LinearMap.ext (fun x => ?_)
    have hx : g x = x * g 1 := by simpa using map_smul g x (1 : ℚ)
    rw [hx, h, mul_zero]
    rfl
  exact (ConcreteCategory.isIso_iff_bijective _).mpr
    (ratCupAux_ratEnd_bijective_of_apply_one_ne_zero hg1)

/-- If `f : M ⟶ N` becomes an isomorphism after conjugating by isomorphisms `M ≅ ℚ` and
`N ≅ ℚ`, then `f` is an isomorphism. -/
theorem ratCupAux_isIso_of_iso_conj_rat {M N : ModuleCat ℚ} {f : M ⟶ N}
    {u : M ≅ ModuleCat.of ℚ ℚ} {v : N ≅ ModuleCat.of ℚ ℚ}
    (hg : IsIso (u.inv ≫ (f ≫ v.hom))) : IsIso f := by
  haveI := hg
  have h : f = u.hom ≫ ((u.inv ≫ (f ≫ v.hom)) ≫ v.inv) := by simp
  rw [h]
  infer_instance

/-- The computation rule for the conjugated map `u.inv ≫ (f ≫ v.hom)` at a point of the form
`u x`. -/
theorem ratCupAux_conj_apply {M N : ModuleCat ℚ} (f : M ⟶ N) (u : M ≅ ModuleCat.of ℚ ℚ)
    (v : N ≅ ModuleCat.of ℚ ℚ) (x : ↥M) :
    (u.inv ≫ (f ≫ v.hom)).hom ((u.hom).hom x) = (v.hom).hom (f.hom x) := by
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
  congr 1
  have h2 := congrArg (fun (φ : M ⟶ M) => φ.hom x) (Iso.hom_inv_id u)
  simpa [ModuleCat.hom_comp] using h2

/-- If a `ℚ`-module is isomorphic to `ℚ`, so is its `ℚ`-dual `Hom_ℚ(M, ℚ)`. -/
def ratCupAux_dualIsoRat {M : ModuleCat ℚ} (h : M ≅ ModuleCat.of ℚ ℚ) :
    ModuleCat.of ℚ (↥M →ₗ[ℚ] ℚ) ≅ ModuleCat.of ℚ ℚ :=
  LinearEquiv.toModuleIso
    { toFun := fun g => g ((h.inv).hom 1)
      invFun := fun c => c • (h.hom).hom
      left_inv := by
        intro g
        refine LinearMap.ext (fun x => ?_)
        have h1 : (h.inv).hom ((h.hom).hom x) = x := by
          have h2 := congrArg (fun (φ : M ⟶ M) => φ.hom x) (Iso.hom_inv_id h)
          simpa using h2
        have hx : ((h.hom).hom x) • ((h.inv).hom (1 : ℚ)) = x := by
          calc ((h.hom).hom x) • ((h.inv).hom (1 : ℚ))
              = (h.inv).hom (((h.hom).hom x) • (1 : ℚ)) := (map_smul _ _ _).symm
            _ = (h.inv).hom ((h.hom).hom x) := by simp
            _ = x := h1
        show (g ((h.inv).hom 1)) • ((h.hom).hom x) = g x
        calc (g ((h.inv).hom 1)) • ((h.hom).hom x)
            = ((h.hom).hom x) • (g ((h.inv).hom 1)) := by
                rw [smul_eq_mul, smul_eq_mul, mul_comm]
          _ = g (((h.hom).hom x) • ((h.inv).hom 1)) := (map_smul g _ _).symm
          _ = g x := by rw [hx]
      right_inv := by
        intro c
        have h1 : (h.hom).hom ((h.inv).hom 1) = 1 := by
          have h2 := congrArg (fun (φ : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℚ) => φ.hom 1)
            (Iso.inv_hom_id h)
          simpa using h2
        show c • ((h.hom).hom ((h.inv).hom 1)) = c
        rw [h1, smul_eq_mul, mul_one]
      map_add' := fun g g' => rfl
      map_smul' := fun c g => rfl }

/-! ## The main statement -/

theorem exists_ratCup_iso_zero (B : Type) [TopologicalSpace B] [PathConnectedSpace B]
    (r : ℕ) (hr : 1 ≤ r)
    (h : Nonempty (Work.Serre.ratH (TopCat.of B) (r + 1) ≅ ModuleCat.of ℚ ℚ)) :
    ∃ e : Work.Serre.ratCoh (TopCat.of B) (r + 1),
      CategoryTheory.IsIso (ModuleCat.ofHom
        (Work.Serre.cupWith (TopCat.of B) (r + 1) e 0)) := by
  -- `H^{r+1}(B;ℚ) ≅ ℚ`, from the hypothesis and the universal coefficient theorem over `ℚ`
  obtain ⟨hH1⟩ := h
  have hr1 : Work.Serre.ratCoh (TopCat.of B) (r + 1) ≅ ModuleCat.of ℚ ℚ :=
    (Work.StemsB.ratDualUCT (Work.Serre.ratChains (TopCat.of B)) (r + 1)).some ≪≫
      ratCupAux_dualIsoRat hH1
  -- `H^0(B;ℚ) ≅ ℚ` since `B` is path connected
  obtain ⟨hH0⟩ := Work.Serre.ratH_zero_of_pathConnected B
  have h0 : Work.Serre.ratCoh (TopCat.of B) 0 ≅ ModuleCat.of ℚ ℚ :=
    (Work.StemsB.ratDualUCT (Work.Serre.ratChains (TopCat.of B)) 0).some ≪≫
      ratCupAux_dualIsoRat hH0
  refine ⟨(hr1.inv).hom 1, ?_⟩
  obtain ⟨u, hu⟩ := Work.Serre.ratCup_unit_exists B
  set f : Work.Serre.ratCoh (TopCat.of B) 0 →ₗ[ℚ]
      Work.Serre.ratCoh (TopCat.of B) (0 + (r + 1)) :=
    Work.Serre.cupWith (TopCat.of B) (r + 1) ((hr1.inv).hom 1) 0 with hf
  -- the isomorphism `H^{0 + (r+1)}(B;ℚ) ≅ ℚ`, obtained from `hr1` along the degree identity
  set v1 : Work.Serre.ratCoh (TopCat.of B) (0 + (r + 1)) ≅ ModuleCat.of ℚ ℚ :=
    eqToIso (congrArg (Work.Serre.ratCoh (TopCat.of B)) (Nat.zero_add (r + 1))) ≪≫ hr1 with hv1
  -- the degree-change isomorphism acts on the underlying carrier as `Eq.rec`
  have hbridge : ∀ {a b : ℕ} (h : a = b) (y : ↥(Work.Serre.ratCoh (TopCat.of B) a)),
      (ModuleCat.Hom.hom (eqToHom (congrArg (Work.Serre.ratCoh (TopCat.of B)) h))) y = h ▸ y :=
    fun h y => by cases h; rfl
  have h1iso : (hr1.hom).hom ((hr1.inv).hom 1) = 1 := by
    have h2 := congrArg (fun (φ : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℚ) => φ.hom 1)
      (Iso.inv_hom_id hr1)
    simpa [ModuleCat.hom_comp] using h2
  -- the chosen class is detected by `v1`
  have hv1apply : (v1.hom).hom (f u) = 1 := by
    have hkey1 : (Nat.zero_add (r + 1)) ▸ (f u) = (hr1.inv).hom 1 := by
      rw [hf]
      simp only [Work.Serre.cupWith, LinearMap.flip_apply]
      exact (hu (r + 1) ((hr1.inv).hom 1)).1
    have hcomp : (v1.hom).hom (f u) =
        (ModuleCat.Hom.hom (hr1.hom))
          ((ModuleCat.Hom.hom (eqToHom (congrArg (Work.Serre.ratCoh (TopCat.of B))
            (Nat.zero_add (r + 1))))) (f u)) := by
      rw [hv1, Iso.trans_hom, ModuleCat.hom_comp]
      rfl
    rw [hcomp, hbridge (Nat.zero_add (r + 1)) (f u), hkey1, h1iso]
  have hf0 : f u ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hv1apply
    exact one_ne_zero hv1apply.symm
  -- the conjugated map is a non-zero endomorphism of `ℚ`
  have hleft : ∀ x : ↥(Work.Serre.ratCoh (TopCat.of B) 0),
      (h0.inv).hom ((h0.hom).hom x) = x := by
    intro x
    have h2 := congrArg (fun (φ : Work.Serre.ratCoh (TopCat.of B) 0 ⟶
        Work.Serre.ratCoh (TopCat.of B) 0) => φ.hom x) (Iso.hom_inv_id h0)
    simpa [ModuleCat.hom_comp] using h2
  have hα : (h0.hom).hom u ≠ 0 := by
    intro hz
    apply hf0
    have hu0 : u = 0 := by rw [← hleft u, hz, map_zero]
    rw [hu0, map_zero]
  have h3 : (h0.hom).hom ((h0.inv).hom 1) = 1 := by
    have h2 := congrArg (fun (φ : ModuleCat.of ℚ ℚ ⟶ ModuleCat.of ℚ ℚ) => φ.hom 1)
      (Iso.inv_hom_id h0)
    simpa [ModuleCat.hom_comp] using h2
  have hkey : (h0.inv).hom (1 : ℚ) = ((h0.hom).hom u)⁻¹ • u := by
    have hinj : Function.Injective (h0.hom).hom := by
      intro a b hab
      rw [← hleft a, ← hleft b, hab]
    apply hinj
    rw [h3, map_smul, smul_eq_mul, inv_mul_cancel₀ hα]
  have hG1 : (h0.inv ≫ (ModuleCat.ofHom f ≫ v1.hom)).hom 1 ≠ 0 := by
    have hstep : (h0.inv ≫ (ModuleCat.ofHom f ≫ v1.hom)).hom 1 =
        (v1.hom).hom (f ((h0.inv).hom 1)) := by
      have h := ratCupAux_conj_apply (ModuleCat.ofHom f) h0 v1 ((h0.inv).hom 1)
      rw [ModuleCat.hom_ofHom] at h
      rw [h3] at h
      exact h
    rw [hstep, hkey]
    rw [map_smul, map_smul, hv1apply, smul_eq_mul, mul_one]
    exact inv_ne_zero hα
  have hGeq : (h0.inv ≫ (ModuleCat.ofHom f ≫ v1.hom)) =
      ModuleCat.ofHom ((h0.inv ≫ (ModuleCat.ofHom f ≫ v1.hom)).hom) :=
    ModuleCat.hom_ext (by rw [ModuleCat.hom_ofHom])
  have hconj : IsIso (h0.inv ≫ (ModuleCat.ofHom f ≫ v1.hom)) := by
    rw [hGeq]
    exact ratCupAux_isIso_ofHom_rat_ne_zero _
      (ratCupAux_ratEnd_ne_zero_of_apply_one_ne_zero hG1)
  exact ratCupAux_isIso_of_iso_conj_rat hconj

end

end Work.Serre
