/-
AREA RESOL — the (mapping) telescope of a sequence of cochain complexes.

Given a sequence of complexes `P 0 → P 1 → P 2 → …` with transition maps `t n : P n ⟶ P (n+1)`,
let `A := ∐ n, P n` be the small coproduct, and let

* `shift P t : A ⟶ A` be the "shift" with components `ι n ≫ shift = t n ≫ ι (n+1)`;
* `telD P t := 𝟙 A - shift P t` (in the blueprint: `1 - shift`);
* `tel P t := mappingCone (telD P t)`.

The telescope `tel P t` is the "homotopy colimit" of the sequence: it is cofibrant (a coproduct
of cofibrant complexes followed by a mapping cone) and it maps quasi-isomorphically to any
complex receiving a compatible cocone of the `P n`.

This file contains only the definitions and the formal lemmas connecting them to the
co-coordinates; the analytic statements live in separate files.
-/
import Mathlib
import Submission.Work.RESOL.Basic
import Submission.Work.RESOL.SigmaSetup

open CategoryTheory Limits LightProfinite LightCondensed
open _root_.LightCondensed

noncomputable section

namespace Work.RESOL

attribute [local instance 2000] Sheaf.instHasColimitsOfShape

/-! ## The coordinate maps of a small coproduct

For a family `X : ℕ → LightCondAb` with a coproduct, `coord X m : ∐ n, X n ⟶ X m` is the `m`-th
coordinate: the map out of the coproduct whose `n`-th component is the identity if `n = m` and
zero otherwise.  These maps are the ones that detect zero maps into a coproduct. -/

/-- The `m`-th coordinate map of a small coproduct of light condensed abelian groups. -/
def coord (X : ℕ → LightCondAb) [HasCoproduct X] (m : ℕ) : (∐ X) ⟶ X m :=
  Sigma.desc (fun n => if h : n = m then eqToHom (congrArg X h) else 0)

lemma Sigma_ι_coord (X : ℕ → LightCondAb) [HasCoproduct X] (m n : ℕ) :
    Sigma.ι X n ≫ coord X m = if h : n = m then eqToHom (congrArg X h) else 0 :=
  Sigma.ι_comp_desc _ n

lemma coord_eq_zero_of_ne (X : ℕ → LightCondAb) [HasCoproduct X] {m n : ℕ} (h : n ≠ m) :
    Sigma.ι X n ≫ coord X m = 0 := by
  rw [Sigma_ι_coord, dite_eq_right h]

lemma Sigma_ι_coord_self (X : ℕ → LightCondAb) [HasCoproduct X] (m : ℕ) :
    Sigma.ι X m ≫ coord X m = 𝟙 (X m) := by
  rw [Sigma_ι_coord, dite_eq_left rfl]
  simp

/-- The canonical map from a small coproduct to the corresponding product. -/
def sigmaToPi (X : ℕ → LightCondAb) [HasCoproduct X] [HasProduct X] : (∐ X) ⟶ (∏ᶜ X) :=
  Pi.lift (fun m => coord X m)

lemma Pi_π_sigmaToPi (X : ℕ → LightCondAb) [HasCoproduct X] [HasProduct X] (m : ℕ) :
    sigmaToPi X ≫ Pi.π X m = coord X m :=
  Pi.lift_comp_π _ m

/-! ## The shift and the telescope -/

/-- The shift map `s : ∐ n, P n ⟶ ∐ n, P n` with components `ι n ≫ s = t n ≫ ι (n+1)`. -/
def smap (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1)) :
    (∐ P) ⟶ (∐ P) :=
  Sigma.desc (fun n => t n ≫ Sigma.ι P (n+1))

lemma Sigma_ι_smap (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1)) (n : ℕ) :
    Sigma.ι P n ≫ smap P t = t n ≫ Sigma.ι P (n+1) :=
  Sigma.ι_comp_desc _ n

/-- `telD P t = 1 - shift` for the sequence `P`. -/
def telD (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1)) :
    (∐ P) ⟶ (∐ P) :=
  𝟙 (∐ P) - smap P t

lemma Sigma_ι_telD (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1)) (n : ℕ) :
    Sigma.ι P n ≫ telD P t = Sigma.ι P n - t n ≫ Sigma.ι P (n+1) := by
  rw [telD, Preadditive.comp_sub, Sigma_ι_smap, Category.comp_id]

/-- The telescope of a sequence of complexes: the mapping cone of `1 - shift`. -/
def tel (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1)) : Cpx :=
  CochainComplex.mappingCone (telD P t)

/-! ## The map from the telescope to a target receiving a compatible cocone

Given `f n : P n ⟶ K` with `t n ≫ f (n+1) = f n`, the induced map `∐ n, P n ⟶ K` kills
`telD = 1 - shift`, hence descends to the telescope `tel P t = mappingCone (telD P t)`. -/

/-- The map `∐ n, P n ⟶ K` with components `f n`. -/
def coconeMap (P : ℕ → Cpx) [HasCoproduct P] {K : Cpx} (f : ∀ n : ℕ, P n ⟶ K) :
    (∐ P) ⟶ K :=
  Sigma.desc f

lemma Sigma_ι_coconeMap (P : ℕ → Cpx) [HasCoproduct P] {K : Cpx} (f : ∀ n : ℕ, P n ⟶ K) (n : ℕ) :
    Sigma.ι P n ≫ coconeMap P f = f n :=
  Sigma.ι_comp_desc _ n

lemma smap_coconeMap (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1)) {K : Cpx}
    (f : ∀ n : ℕ, P n ⟶ K) (hf : ∀ n : ℕ, t n ≫ f (n+1) = f n) :
    smap P t ≫ coconeMap P f = coconeMap P f := by
  apply Sigma.hom_ext
  intro n
  rw [← Category.assoc, Sigma_ι_smap, Category.assoc, Sigma_ι_coconeMap, hf n,
    Sigma_ι_coconeMap]

lemma telD_coconeMap (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1)) {K : Cpx}
    (f : ∀ n : ℕ, P n ⟶ K) (hf : ∀ n : ℕ, t n ≫ f (n+1) = f n) :
    telD P t ≫ coconeMap P f = 0 := by
  rw [telD, Preadditive.sub_comp, Category.id_comp, smap_coconeMap P t f hf, sub_self]

/-- The compatibility condition for the construction of `telDesc`. -/
lemma telD_descEq (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1)) (K : Cpx)
    (f : ∀ n : ℕ, P n ⟶ K) (hf : ∀ n : ℕ, t n ≫ f (n+1) = f n) :
    CochainComplex.HomComplex.δ (-1) (0 : ℤ)
        (0 : CochainComplex.HomComplex.Cochain (∐ P) K (-1)) =
      CochainComplex.HomComplex.Cochain.ofHom (telD P t ≫ coconeMap P f) := by
  have h : CochainComplex.HomComplex.δ (-1) (0 : ℤ)
      (0 : CochainComplex.HomComplex.Cochain (∐ P) K (-1)) = 0 :=
    CochainComplex.HomComplex.δ_zero (-1) 0
  rw [h, telD_coconeMap P t f hf, CochainComplex.HomComplex.Cochain.ofHom_zero]

/-- The map from the telescope of the sequence to `K`, induced by the compatible cocone `f`. -/
def telDesc (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1)) (K : Cpx)
    (f : ∀ n : ℕ, P n ⟶ K) (hf : ∀ n : ℕ, t n ≫ f (n+1) = f n) :
    tel P t ⟶ K :=
  CochainComplex.mappingCone.desc (telD P t) 0 (coconeMap P f) (telD_descEq P t K f hf)

lemma telDesc_inr (P : ℕ → Cpx) [HasCoproduct P] (t : ∀ n : ℕ, P n ⟶ P (n+1)) (K : Cpx)
    (f : ∀ n : ℕ, P n ⟶ K) (hf : ∀ n : ℕ, t n ≫ f (n+1) = f n) :
    CochainComplex.mappingCone.inr (telD P t) ≫ telDesc P t K f hf = coconeMap P f :=
  CochainComplex.mappingCone.inr_desc (telD P t) 0 (coconeMap P f) (telD_descEq P t K f hf)

end Work.RESOL
