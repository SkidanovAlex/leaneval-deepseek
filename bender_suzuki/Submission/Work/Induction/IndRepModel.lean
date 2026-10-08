import Mathlib
import Submission.Work.Induction.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The fixed-functions model of the induced representation

For a finite group `G`, a subgroup `H ≤ G` and a finite dimensional complex representation
`V` of `H`, this file sets up the model of the induced representation `Ind_H^G V` used to
prove `Work.Induction.exists_fdRep_of_indFun`.

On the space `F = G → V` of all functions one has

* `indQh V h`, `(indQh V h f) x = V.ρ h (f (h⁻¹ * x))`;
* `indQ = |H|⁻¹ • ∑_{h : H} indQh V h`, the projection onto the `H`-fixed functions
  `indW V = range indQ`;
* `indT V g`, `(indT V g f) x = f (x * g)`; the maps `indT V g` commute with every `indQh V h`,
  hence preserve `indW V`, and their restrictions form a representation `indRhoV V` of `G`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open Classical
open scoped Pointwise

namespace Work.Induction

variable {G : Type*} [Group G] [Fintype G] {H : Subgroup G}

/-- The linear map `indQh V h` on `G → V`, `(indQh V h f) x = V.ρ h (f (h⁻¹ * x))`. -/
def indQh (V : FDRep ℂ H) (h : H) : (G → V) →ₗ[ℂ] (G → V) where
  toFun f := fun x => V.ρ h (f (h⁻¹ * x))
  map_add' f g := by ext x; simp
  map_smul' c f := by ext x; simp

/-- The averaging map `indQ V = |H|⁻¹ • ∑_{h : H} indQh V h`. -/
def indQ (V : FDRep ℂ H) : (G → V) →ₗ[ℂ] (G → V) :=
  (Nat.card H : ℂ)⁻¹ • ∑ h : H, indQh V h

/-- The linear map `(indT V g f) x = f (x * g)`. -/
def indT (V : FDRep ℂ H) (g : G) : (G → V) →ₗ[ℂ] (G → V) where
  toFun f := fun x => f (x * g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The fixed-functions submodule, the range of the projection `indQ V`. -/
def indW (V : FDRep ℂ H) : Submodule ℂ (G → V) := LinearMap.range (indQ V)

/-- Evaluation at `y`, as a linear map `(G → V) →ₗ V`. -/
def indEval (V : FDRep ℂ H) (y : G) : (G → V) →ₗ[ℂ] V where
  toFun f := f y
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Insertion of a vector at `z`, as a linear map `V →ₗ (G → V)`. -/
def indIns (V : FDRep ℂ H) (z : G) : V →ₗ[ℂ] (G → V) where
  toFun v := fun x => if x = z then v else 0
  map_add' a b := by ext x; by_cases h : x = z <;> simp [h]
  map_smul' c v := by ext x; by_cases h : x = z <;> simp [h]

/-- The rank-one piece `indE V h g y` of `indT V g ∘ indQh V h`. -/
def indE (V : FDRep ℂ H) (h : H) (g y : G) : (G → V) →ₗ[ℂ] (G → V) :=
  (indIns V ((h : G) * y * g⁻¹)).comp ((V.ρ h).comp (indEval V y))

@[simp] lemma indQh_apply (V : FDRep ℂ H) (h : H) (f : G → V) (x : G) :
    indQh V h f x = V.ρ h (f (h⁻¹ * x)) := rfl

@[simp] lemma indT_apply (V : FDRep ℂ H) (g : G) (f : G → V) (x : G) :
    indT V g f x = f (x * g) := rfl

@[simp] lemma indEval_apply (V : FDRep ℂ H) (y : G) (f : G → V) :
    indEval V y f = f y := rfl

@[simp] lemma indIns_apply (V : FDRep ℂ H) (z : G) (v : V) (x : G) :
    indIns V z v x = if x = z then v else 0 := rfl

@[simp] lemma indE_apply (V : FDRep ℂ H) (h : H) (g y : G) (f : G → V) (x : G) :
    indE V h g y f x =
      if x = (h : G) * y * g⁻¹ then V.ρ h (f y) else 0 := rfl

lemma indQh_comp (V : FDRep ℂ H) (h h' : H) :
    (indQh V h).comp (indQh V h') = indQh V (h * h') := by
  apply LinearMap.ext; intro f; apply funext; intro x
  simp [indQh_apply, map_mul, Module.End.mul_apply, mul_inv_rev, mul_assoc]

lemma indT_comp (V : FDRep ℂ H) (g g' : G) :
    (indT V g).comp (indT V g') = indT V (g * g') := by
  apply LinearMap.ext; intro f; apply funext; intro x
  simp [indT_apply, mul_assoc]

/-- Composing on the left with a finite sum of linear maps. -/
lemma comp_sum_eq (V : FDRep ℂ H) {ι : Type*} (f : (G → V) →ₗ[ℂ] (G → V)) (s : Finset ι)
    (g : ι → (G → V) →ₗ[ℂ] (G → V)) :
    f.comp (∑ i ∈ s, g i) = ∑ i ∈ s, f.comp (g i) := by
  ext x
  simp [LinearMap.comp_apply, map_sum]

/-- Composing on the right with a finite sum of linear maps. -/
lemma sum_comp_eq (V : FDRep ℂ H) {ι : Type*} (s : Finset ι)
    (f : ι → (G → V) →ₗ[ℂ] (G → V)) (g : (G → V) →ₗ[ℂ] (G → V)) :
    (∑ i ∈ s, f i).comp g = ∑ i ∈ s, (f i).comp g := by
  ext x
  simp [LinearMap.comp_apply, map_sum]

lemma indT_comp_indQh (V : FDRep ℂ H) (g : G) (h : H) :
    (indT V g).comp (indQh V h) = (indQh V h).comp (indT V g) := by
  apply LinearMap.ext; intro f; apply funext; intro x
  simp only [LinearMap.comp_apply, indQh_apply, indT_apply]
  congr 1
  rw [mul_assoc]

lemma indQh_comp_indQ (V : FDRep ℂ H) (h : H) :
    (indQh V h).comp (indQ V) = indQ V := by
  unfold indQ
  rw [LinearMap.comp_smul]
  congr 1
  rw [comp_sum_eq]
  simp only [indQh_comp]
  exact Equiv.sum_comp (Equiv.mulLeft h) (fun h'' : H => indQh V h'')

lemma indQ_idem (V : FDRep ℂ H) : (indQ V).comp (indQ V) = indQ V := by
  have hH : (Nat.card H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have h : (indQ V).comp (indQ V) = (Nat.card H : ℂ)⁻¹ • ∑ _h : H, (indQ V) := by
    rw [indQ, LinearMap.smul_comp, sum_comp_eq]
    congr 1
    exact Finset.sum_congr rfl (fun h _ => indQh_comp_indQ V h)
  rw [h]
  have hsum : (∑ _h : H, (indQ V)) = (Nat.card H : ℂ) • (indQ V) := by
    rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]
  rw [hsum, smul_smul, inv_mul_cancel₀ hH, one_smul]

lemma isProj_indQ (V : FDRep ℂ H) : LinearMap.IsProj (indW V) (indQ V) :=
  LinearMap.IsIdempotentElem.isProj_range (indQ V) (by
    show (indQ V) * (indQ V) = indQ V
    rw [Module.End.mul_eq_comp]
    exact indQ_idem V)

lemma indT_comp_indQ (V : FDRep ℂ H) (g : G) :
    (indT V g).comp (indQ V) = (indQ V).comp (indT V g) := by
  unfold indQ
  rw [LinearMap.comp_smul, LinearMap.smul_comp, comp_sum_eq V, sum_comp_eq V]
  congr 1
  exact Finset.sum_congr rfl (fun h _ => indT_comp_indQh V g h)

lemma indQ_comp_subtype (V : FDRep ℂ H) :
    (indQ V).comp (indW V).subtype = (indW V).subtype := by
  apply LinearMap.ext; intro w
  exact (isProj_indQ V).map_id (w : G → V) w.2

lemma indT_one (V : FDRep ℂ H) : indT V 1 = LinearMap.id := by
  apply LinearMap.ext; intro f; funext x
  simp [indT_apply]

lemma indT_mem_indW (V : FDRep ℂ H) (g : G) {f : G → V} (hf : f ∈ indW V) :
    indT V g f ∈ indW V := by
  obtain ⟨x, rfl⟩ := LinearMap.mem_range.mp hf
  refine ⟨indT V g x, ?_⟩
  rw [← LinearMap.comp_apply, ← indT_comp_indQ V g, LinearMap.comp_apply]

/-- The restriction of `indT V g` to the fixed-functions submodule `indW V`. -/
def indTW (V : FDRep ℂ H) (g : G) : (indW V) →ₗ[ℂ] (indW V) :=
  (isProj_indQ V).codRestrict.comp ((indT V g).comp (indW V).subtype)

lemma indTW_apply (V : FDRep ℂ H) (g : G) (w : indW V) :
    ((indTW V g w : indW V) : G → V) = indQ V (indT V g (w : G → V)) :=
  LinearMap.IsProj.codRestrict_apply (isProj_indQ V) _

lemma indTW_apply_eq (V : FDRep ℂ H) (g : G) (w : indW V) :
    ((indTW V g w : indW V) : G → V) = indT V g (w : G → V) := by
  rw [indTW_apply]
  exact (isProj_indQ V).map_id _ (indT_mem_indW V g w.2)

lemma codRestrict_comp_subtype (V : FDRep ℂ H) :
    (isProj_indQ V).codRestrict.comp (indW V).subtype = LinearMap.id := by
  apply LinearMap.ext; intro w
  exact LinearMap.IsProj.codRestrict_apply_cod (isProj_indQ V) w

lemma indTW_one (V : FDRep ℂ H) : indTW V 1 = 1 := by
  rw [indTW, indT_one, LinearMap.id_comp, codRestrict_comp_subtype, Module.End.one_eq_id]

lemma indTW_mul (V : FDRep ℂ H) (g g' : G) :
    indTW V (g * g') = (indTW V g).comp (indTW V g') := by
  apply LinearMap.ext; intro w
  apply Subtype.ext
  simp only [LinearMap.comp_apply, indTW_apply_eq]
  funext x
  simp only [indT_apply]
  rw [mul_assoc]

/-- **The induced representation**, on the fixed-functions submodule `indW V ≤ (G → V)`. -/
def indRhoV (V : FDRep ℂ H) : Representation ℂ G (indW V) where
  toFun g := indTW V g
  map_one' := indTW_one V
  map_mul' g g' := by
    show indTW V (g * g') = (indTW V g).comp (indTW V g')
    exact indTW_mul V g g'

@[simp] lemma indRhoV_apply (V : FDRep ℂ H) (g : G) : indRhoV V g = indTW V g := rfl

/-- The trace of the restricted operator is the trace of `indT V g ∘ indQ V` on `G → V`. -/
lemma trace_indTW (V : FDRep ℂ H) (g : G) :
    LinearMap.trace ℂ (indW V) (indTW V g) =
      LinearMap.trace ℂ (G → V) ((indT V g).comp (indQ V)) := by
  have h := LinearMap.trace_comp_comm' (R := ℂ) (M := indW V) (N := G → V)
    (indW V).subtype ((isProj_indQ V).codRestrict.comp (indT V g))
  rw [show ((isProj_indQ V).codRestrict.comp (indT V g)) ∘ₗ (indW V).subtype
        = indTW V g from rfl] at h
  rw [h]
  congr 1
  rw [← LinearMap.comp_assoc, LinearMap.IsProj.subtype_comp_codRestrict, indT_comp_indQ]

end Work.Induction
