import Mathlib
import Submission.Work.Cohomology.CompatTrans.prodSphereAux
import Submission.Work.Cohomology.sphere_compl_singleton_contractible
import Submission.Work.Cohomology.sphereCapContractible
import Submission.Work.Cohomology.sphereHomologyTop
import Submission.Work.Morse.TwoBallsBasic

set_option synthInstance.maxHeartbeats 400000

/-!
# The spaces occurring in the computation of `Hₙ(Sᵖ × Sᵍ)`

This file fixes the notation for the proof of `Work.Cohomology.homology_prod_sphere`:

* `sphN m`, `sphS m` — the north and south poles of the unit sphere `S^m ⊆ ℝ^(m+1)`;
* `PSph p q` — the product `Sᵖ × Sᵍ` of unit spheres, as a topological space;
* `ptP p q` — the base point `(Nₚ, N_q)`;
* `Yset p q` — the complement of the base point, and `Vset p q` — the product of the two caps
  `capA p × capA q` (a contractible open set containing the base point);
* `A1set p q`, `B1set p q` — the two subsets `(Sᵖ \ {N}) × Sᵍ` and `Sᵖ × (Sᵍ \ {N})` of `Yset`;
* the projections `proj₁`, `proj₂`, and the two sections used to see that they are split
  surjective on homology.
-/

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
set_option linter.unusedVariables false

open CategoryTheory AlgebraicTopology Limits
open scoped Topology

namespace Work.Cohomology

noncomputable section

/-! ## 1. The poles -/

/-- The two descriptions of the sphere agree. -/
lemma sphereSet_eq' (m : ℕ) :
    Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1 = sphSet m := by
  ext x
  rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
  rfl

/-- The north pole of the unit sphere of `ℝ^(m+1)`. -/
def sphN (m : ℕ) : ↥(sphSet (m+1)) :=
  ⟨Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin m)) 1, by
    show ‖Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin m)) 1‖ = 1
    have h : ‖Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin m)) 1‖ ^ 2 = 1 := by
      rw [Work.Morse.snocLp_norm_sq, norm_zero, zero_pow (by norm_num)]
      ring_nf
    nlinarith [norm_nonneg (Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin m)) 1)]⟩

/-- The south pole of the unit sphere of `ℝ^(m+1)`. -/
def sphS (m : ℕ) : ↥(sphSet (m+1)) :=
  ⟨Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin m)) (-1), by
    show ‖Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin m)) (-1)‖ = 1
    have h : ‖Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin m)) (-1)‖ ^ 2 = 1 := by
      rw [Work.Morse.snocLp_norm_sq, norm_zero, zero_pow (by norm_num)]
      ring_nf
    nlinarith [norm_nonneg (Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin m)) (-1))]⟩

lemma sphN_last (m : ℕ) : (sphN m).1 (Fin.last m) = 1 := by
  show Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin m)) 1 (Fin.last m) = 1
  rw [Work.Morse.snocLp_ofLp_last]

lemma sphS_last (m : ℕ) : (sphS m).1 (Fin.last m) = -1 := by
  show Work.Morse.snocLp (0 : EuclideanSpace ℝ (Fin m)) (-1) (Fin.last m) = -1
  rw [Work.Morse.snocLp_ofLp_last]

lemma sphN_mem_capA (m : ℕ) : sphN m ∈ capA m := by
  show (sphN m).1 (Fin.last m) > -(1/2)
  rw [sphN_last]; norm_num

lemma sphS_mem_capB (m : ℕ) : sphS m ∈ capB m := by
  show (sphS m).1 (Fin.last m) < 1/2
  rw [sphS_last]; norm_num

lemma sphN_ne_sphS (m : ℕ) : sphN m ≠ sphS m := by
  intro h
  have h1 := sphN_last m
  have h2 := sphS_last m
  rw [h] at h1
  linarith [h1, h2]

/-- The sphere with the north pole removed is contractible. -/
lemma contractible_compl_sphN (m : ℕ) :
    ContractibleSpace {z : ↥(sphSet (m+1)) // z ≠ sphN m} := by
  have e : ↥(sphSet (m+1)) ≃ₜ Metric.sphere (0 : EuclideanSpace ℝ (Fin (m+1))) 1 :=
    (Homeomorph.setCongr (sphereSet_eq' (m+1))).symm
  let c : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m+1))) 1 := e (sphN m)
  haveI : ContractibleSpace ↥({y : Metric.sphere (0 : EuclideanSpace ℝ (Fin (m+1))) 1 | y ≠ c}) :=
    sphere_compl_singleton_contractible _ c
  have himg : e '' {z : ↥(sphSet (m+1)) | z ≠ sphN m} = {y | y ≠ c} := by
    have h1 : {z : ↥(sphSet (m+1)) | z ≠ sphN m} = ({sphN m} : Set ↥(sphSet (m+1)))ᶜ := by
      ext z; simp
    rw [h1, Set.image_compl_eq e.bijective, Set.image_singleton]
    rfl
  exact Homeomorph.contractibleSpace
    ((Homeomorph.image e {z : ↥(sphSet (m+1)) | z ≠ sphN m}).trans (Homeomorph.setCongr himg))

/-! ## 2. The product of the two spheres and the pieces of the two covers -/

/-- The product `Sᵖ × Sᵍ` of unit spheres, as a topological space. -/
abbrev PSph (p q : ℕ) : TopCat := TopCat.of (↥(sphSet (p+1)) × ↥(sphSet (q+1)))

/-- The base point `(Nₚ, N_q)` of `Sᵖ × Sᵍ`. -/
def ptP (p q : ℕ) : ↥(PSph p q) := (sphN p, sphN q)

/-- The complement of the base point in `Sᵖ × Sᵍ`. -/
def Yset (p q : ℕ) : Set (PSph p q) := {z | z ≠ ptP p q}

/-- The product of the two caps `capA p × capA q ⊆ Sᵖ × Sᵍ`. -/
def Vset (p q : ℕ) : Set (PSph p q) := {z | z.1 ∈ capA p ∧ z.2 ∈ capA q}

/-- `(Sᵖ \ {Nₚ}) × Sᵍ`, inside the complement of the base point. -/
def A1set (p q : ℕ) : Set ↥(Yset p q) := {z | (z : ↥(PSph p q)).1 ≠ sphN p}

/-- `Sᵖ × (Sᵍ \ {N_q})`, inside the complement of the base point. -/
def B1set (p q : ℕ) : Set ↥(Yset p q) := {z | (z : ↥(PSph p q)).2 ≠ sphN q}

/-- The first projection `Sᵖ × Sᵍ ⟶ Sᵖ`. -/
def proj₁ (p q : ℕ) : PSph p q ⟶ sphTop (p+1) :=
  TopCat.ofHom ⟨Prod.fst, continuous_fst⟩

/-- The second projection `Sᵖ × Sᵍ ⟶ Sᵍ`. -/
def proj₂ (p q : ℕ) : PSph p q ⟶ sphTop (q+1) :=
  TopCat.ofHom ⟨Prod.snd, continuous_snd⟩

@[simp]
lemma proj₁_apply (p q : ℕ) (z : ↥(PSph p q)) : (proj₁ p q) z = z.1 := rfl

@[simp]
lemma proj₂_apply (p q : ℕ) (z : ↥(PSph p q)) : (proj₂ p q) z = z.2 := rfl

lemma ptP_mem_Vset (p q : ℕ) : ptP p q ∈ Vset p q :=
  ⟨sphN_mem_capA p, sphN_mem_capA q⟩

/-- The inclusion `Sᵖ × Sᵍ \ {pt} ⟶ Sᵖ × Sᵍ`. -/
def inclY (p q : ℕ) : TopCat.of ↥(Yset p q) ⟶ PSph p q :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The first projection restricted to `Sᵖ × Sᵍ \ {pt}`. -/
def proj₁Y (p q : ℕ) : TopCat.of ↥(Yset p q) ⟶ sphTop (p+1) :=
  TopCat.ofHom ⟨fun z => ((z : ↥(Yset p q)) : ↥(PSph p q)).1,
    continuous_fst.comp continuous_subtype_val⟩

/-- The second projection restricted to `Sᵖ × Sᵍ \ {pt}`. -/
def proj₂Y (p q : ℕ) : TopCat.of ↥(Yset p q) ⟶ sphTop (q+1) :=
  TopCat.ofHom ⟨fun z => ((z : ↥(Yset p q)) : ↥(PSph p q)).2,
    continuous_snd.comp continuous_subtype_val⟩

/-- The section `x ↦ (x, S_q)` of the first projection on `Sᵖ × Sᵍ \ {pt}`. -/
def sec₁ (p q : ℕ) : sphTop (p+1) ⟶ TopCat.of ↥(Yset p q) :=
  TopCat.ofHom ⟨fun x => ⟨(x, sphS q), by
      intro h
      exact sphN_ne_sphS q (congrArg Prod.snd h).symm⟩,
    Continuous.subtype_mk (continuous_id.prodMk continuous_const) _⟩

/-- The section `y ↦ (S_p, y)` of the second projection on `Sᵖ × Sᵍ \ {pt}`. -/
def sec₂ (p q : ℕ) : sphTop (q+1) ⟶ TopCat.of ↥(Yset p q) :=
  TopCat.ofHom ⟨fun y => ⟨(sphS p, y), by
      intro h
      exact sphN_ne_sphS p (congrArg Prod.fst h).symm⟩,
    Continuous.subtype_mk (continuous_const.prodMk continuous_id) _⟩

@[simp]
lemma sec₁_comp_proj₁Y (p q : ℕ) : sec₁ p q ≫ proj₁Y p q = 𝟙 (sphTop (p+1)) := by
  apply TopCat.hom_ext
  ext x
  rfl

@[simp]
lemma sec₂_comp_proj₂Y (p q : ℕ) : sec₂ p q ≫ proj₂Y p q = 𝟙 (sphTop (q+1)) := by
  apply TopCat.hom_ext
  ext y
  rfl

lemma sec₂_comp_proj₁Y (p q : ℕ) :
    sec₂ p q ≫ proj₁Y p q = TopCat.ofHom (ContinuousMap.const _ (sphS p)) := by
  apply TopCat.hom_ext
  ext y
  rfl

/-- `Vset p q ∩ Yset p q`, the punctured product of the two caps. -/
def Wset (p q : ℕ) : Set (PSph p q) := Vset p q ∩ Yset p q

/-- The second projection `↥(A1set p q) ⟶ S^q`. -/
def proj₂A1 (p q : ℕ) : TopCat.of ↥(A1set p q) ⟶ sphTop (q+1) :=
  TopCat.ofHom ⟨fun z => (((z : ↥(A1set p q)) : ↥(Yset p q)) : ↥(PSph p q)).2,
    continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)⟩

/-- The first projection `↥(B1set p q) ⟶ S^p`. -/
def proj₁B1 (p q : ℕ) : TopCat.of ↥(B1set p q) ⟶ sphTop (p+1) :=
  TopCat.ofHom ⟨fun z => (((z : ↥(B1set p q)) : ↥(Yset p q)) : ↥(PSph p q)).1,
    continuous_fst.comp (continuous_subtype_val.comp continuous_subtype_val)⟩

lemma Wset_eq_inter (p q : ℕ) : Wset p q = Yset p q ∩ Vset p q := by
  rw [Wset, Set.inter_comm]

lemma sec₁_comp_proj₂Y (p q : ℕ) :
    sec₁ p q ≫ proj₂Y p q = TopCat.ofHom (ContinuousMap.const _ (sphS q)) := by
  apply TopCat.hom_ext
  ext x
  rfl

/-! ## 3. Elementary properties of the pieces -/

lemma isOpen_Yset (p q : ℕ) : IsOpen (Yset p q) := by
  rw [show Yset p q = {ptP p q}ᶜ by ext z; simp [Yset]]
  exact isClosed_singleton.isOpen_compl

lemma isOpen_Vset (p q : ℕ) : IsOpen (Vset p q) :=
  ((isOpen_capA p).preimage continuous_fst).inter ((isOpen_capA q).preimage continuous_snd)

lemma Vset_union_Yset (p q : ℕ) : Vset p q ∪ Yset p q = Set.univ := by
  ext z
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases h : z = ptP p q
  · exact Or.inl (h ▸ ptP_mem_Vset p q)
  · exact Or.inr h

lemma Yset_union_Vset (p q : ℕ) : Yset p q ∪ Vset p q = Set.univ :=
  (Set.union_comm _ _).trans (Vset_union_Yset p q)

lemma Yset_inter_Vset (p q : ℕ) : (Yset p q : Set (PSph p q)) ∩ Vset p q
    = {z | z ∈ Vset p q ∧ z ≠ ptP p q} := by
  ext z; simp [Yset, and_comm]

lemma isOpen_A1set (p q : ℕ) : IsOpen (A1set p q) := by
  have hcont : Continuous fun z : ↥(Yset p q) => ((z : ↥(PSph p q)).1) :=
    continuous_fst.comp continuous_subtype_val
  rw [show A1set p q = (fun z : ↥(Yset p q) => ((z : ↥(PSph p q)).1)) ⁻¹' ({sphN p}ᶜ) from by
    ext z; simp [A1set]]
  exact hcont.isOpen_preimage _ isClosed_singleton.isOpen_compl

lemma isOpen_B1set (p q : ℕ) : IsOpen (B1set p q) := by
  have hcont : Continuous fun z : ↥(Yset p q) => ((z : ↥(PSph p q)).2) :=
    continuous_snd.comp continuous_subtype_val
  rw [show B1set p q = (fun z : ↥(Yset p q) => ((z : ↥(PSph p q)).2)) ⁻¹' ({sphN q}ᶜ) from by
    ext z; simp [B1set]]
  exact hcont.isOpen_preimage _ isClosed_singleton.isOpen_compl

lemma A1set_union_B1set (p q : ℕ) : A1set p q ∪ B1set p q = Set.univ := by
  ext z
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  by_cases h : (z : ↥(PSph p q)).1 ≠ sphN p
  · exact Or.inl h
  · refine Or.inr ?_
    intro h2
    exact z.2 (Prod.ext (not_not.mp h) h2)

end

end Work.Cohomology
