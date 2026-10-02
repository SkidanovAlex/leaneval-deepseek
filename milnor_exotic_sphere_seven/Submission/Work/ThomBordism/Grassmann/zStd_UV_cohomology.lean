import Mathlib
import Submission.Work.ThomBordism.Grassmann.zStdSetup
import Submission.Work.ThomBordism.Grassmann.UVOverlap
import Submission.Work.ThomBordism.Grassmann.uvPieceIsOpen
import Submission.Work.ThomBordism.Grassmann.uvPieceHomotopyEquiv
import Submission.Work.LerayHirsch.mv2_exact
import Submission.Work.Cohomology.isZero_dualComplex_empty

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-!
# `H³` of the overlap `UR ∩ VR = {Re ≠ 0, Im ≠ 0}` vanishes

This is the last input of the proof that `Work.Thom.pontryagin1 zStd ≠ 0`
(`Submission/Work/ThomBordism/Grassmann/zStd_pontryagin_ne_zero.lean`).

The overlap `Y = UR ∩ VR` is the locus of the punctured total space of `W` on which both the real
part `U` and the imaginary part `V` of the fibre vector are nonzero.  Since `zStd` is the
realification of a complex line bundle, the *ratio* `uvRatio = V/U` (in the `ccoord`-coordinates) is
a well defined continuous function `uvRatio : ↥Y → ℂ` with values in `ℂ ∖ {0}`
(`UVOverlap.lean`, `uvPieceIsOpen.lean`), and the two regions

* `uvA = {ratio ∉ ℝ_{≥0}}`, `uvB = {ratio ∉ ℝ_{≤0}}`

cover `Y` (`uvA_union_uvB`), because only `0` lies in both rays while the ratio never vanishes.
Each of the four pieces `uvA`, `uvB`, `uvP = {Im ratio > 0}`, `uvQ = {Im ratio < 0}` is homotopy
equivalent to `zeroComplement zStd` (`uvPieceHomotopyEquiv`), so `H³` vanishes for each of them, and
`uvA ∩ uvB = uvP ∪ uvQ` with `uvP ∩ uvQ = ∅`.

The proof is two Mayer–Vietoris arguments (`Work.LerayHirsch.mv2_exact`):

* on `uvA ∩ uvB`, covered by the two disjoint pieces `uvP`, `uvQ` (whose intersection is empty, and
  `H³(∅) = 0`), giving `H³(uvA ∩ uvB) = 0`;
* on `Y = uvA ∪ uvB`, giving `H³(Y) = 0` since `H³(uvA) = H³(uvB) = H³(uvA ∩ uvB) = 0`.
-/


namespace Work.ThomBordism.Grassmann

open Work.TangentClasses

open CategoryTheory Limits

open scoped Simplicial

noncomputable section

/-! ## The cohomology of the empty space -/

/-- **The cohomology of the empty space vanishes.** -/
theorem uvEmptyCohomology (X : Type) [TopologicalSpace X] (n : ℕ) :
    Subsingleton (Work.Thom.Coh ℤ n ↥(∅ : Set X)) := by
  change Subsingleton ((Work.Cohomology.singularCochainComplex ℤ
    (TopCat.of (∅ : Set X))).homology n)
  have hcoch : CategoryTheory.Limits.IsZero
      (Work.Cohomology.singularCochainComplex ℤ (TopCat.of (∅ : Set X))) := by
    rw [← Work.Cohomology.dualComplex_singularChains ℤ (TopCat.of (∅ : Set X))]
    exact Work.Cohomology.isZero_dualComplex_empty (TopCat.of X)
  have hX : CategoryTheory.Limits.IsZero
      ((Work.Cohomology.singularCochainComplex ℤ (TopCat.of (∅ : Set X))).X n) :=
    CategoryTheory.Functor.map_isZero (HomologicalComplex.eval (ModuleCat ℤ) (ComplexShape.up ℕ) n)
      hcoch
  exact ModuleCat.subsingleton_of_isZero ((HomologicalComplex.exactAt_iff_isZero_homology _ n).mp
    (HomologicalComplex.ExactAt.of_isZero hX))

/-! ## The vanishing of `H^k` on a piece -/

/-- **`H^k` of the punctured total space of `zStd` vanishes for `k ≠ 0, 5`** (it is `ℂ³∖0 ≃ S⁵`). -/
theorem uvC_cohomology_zero (k : ℕ) (hk0 : k ≠ 0) (hk5 : k ≠ 5) :
    Subsingleton (Work.Thom.Coh ℤ k ↥(Work.Thom.zeroComplement zStd)) := by
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
    punctHomeoTautDualTwoR.toHomotopyEquiv k
  exact ModuleCat.subsingleton_of_isZero (CategoryTheory.Limits.IsZero.of_iso
    (puncturedTautDualTwoHZero k hk0 hk5) iso.symm)

/-- **`H^k` of a piece `{ratio ∈ Reg}` vanishes** for `k ≠ 0, 5`, when `Reg ⊆ ℂ ∖ {0}` is
star-shaped with respect to a point `κ ∈ Reg`. -/
theorem uvPiece_cohomology_zero (Reg : Set ℂ) (κ : ℂ) (hκ : κ ∈ Reg) (h0 : (0 : ℂ) ∉ Reg)
    (hstar : ∀ r ∈ Reg, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (1 - t) * r + t * κ ∈ Reg)
    (k : ℕ) (hk0 : k ≠ 0) (hk5 : k ≠ 5) :
    Subsingleton (Work.Thom.Coh ℤ k ↥(uvPiece Reg)) := by
  haveI : Subsingleton (Work.Thom.Coh ℤ k ↥(Work.Thom.zeroComplement zStd)) :=
    uvC_cohomology_zero k hk0 hk5
  obtain ⟨e⟩ := uvPieceHomotopyEquiv Reg κ hκ h0 hstar
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv e k
  exact ModuleCat.subsingleton_of_isZero (CategoryTheory.Limits.IsZero.of_iso
    (ModuleCat.isZero_of_subsingleton (Work.Thom.Coh ℤ k ↥(Work.Thom.zeroComplement zStd))) iso)

/-! ## The two rays are closed -/

theorem rayNN_eq : rayNN
    = (Complex.re ⁻¹' (Set.Ici (0 : ℝ)) ∩ Complex.im ⁻¹' ({0} : Set ℝ) : Set ℂ) := by
  ext r
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨ha, by simp⟩
  · rintro ⟨h1, h2⟩
    refine ⟨r.re, h1, ?_⟩
    rw [Complex.ext_iff]
    exact ⟨by simp, by simpa using h2⟩

theorem rayNP_eq : rayNP
    = (Complex.re ⁻¹' (Set.Iic (0 : ℝ)) ∩ Complex.im ⁻¹' ({0} : Set ℝ) : Set ℂ) := by
  ext r
  constructor
  · rintro ⟨a, ha, rfl⟩
    exact ⟨by simpa using ha, by simp⟩
  · rintro ⟨h1, h2⟩
    have h1' : r.re ≤ 0 := h1
    refine ⟨-r.re, by linarith, ?_⟩
    rw [Complex.ext_iff]
    exact ⟨by simp, by simpa using h2⟩

theorem isClosed_rayNN : IsClosed rayNN := by
  rw [rayNN_eq]
  exact (isClosed_Ici.preimage Complex.continuous_re).inter
    (isClosed_singleton.preimage Complex.continuous_im)

theorem isClosed_rayNP : IsClosed rayNP := by
  rw [rayNP_eq]
  exact (isClosed_Iic.preimage Complex.continuous_re).inter
    (isClosed_singleton.preimage Complex.continuous_im)

theorem isOpen_rayNN_compl : IsOpen (rayNNᶜ) := isClosed_rayNN.isOpen_compl

theorem isOpen_rayNP_compl : IsOpen (rayNPᶜ) := isClosed_rayNP.isOpen_compl

theorem isOpen_upperHalf : IsOpen upperHalf := isOpen_lt continuous_const Complex.continuous_im

theorem isOpen_lowerHalf : IsOpen lowerHalf := isOpen_lt Complex.continuous_im continuous_const

theorem zero_mem_rayNN : (0 : ℂ) ∈ rayNN := ⟨0, le_refl 0, by simp⟩

theorem zero_mem_rayNP : (0 : ℂ) ∈ rayNP := ⟨0, le_refl 0, by simp⟩

theorem neg_one_notMem_rayNN : (-1 : ℂ) ∉ rayNN := by
  rintro ⟨a, ha, h⟩
  have h' : ((-1 : ℝ) : ℂ) = ((a : ℝ) : ℂ) := by simpa using h
  have ha' : ((-1 : ℝ)) = a := Complex.ofReal_injective h'
  have ha2 : a = -1 := by linarith
  rw [ha2] at ha
  norm_num at ha

theorem one_notMem_rayNP : (1 : ℂ) ∉ rayNP := by
  rintro ⟨a, ha, h⟩
  have h' : ((1 : ℝ) : ℂ) = -((a : ℝ) : ℂ) := by simpa using h
  have h'' : ((1 : ℝ) : ℂ) = ((-a : ℝ) : ℂ) := by simpa using h'
  have ha' : (1 : ℝ) = -a := Complex.ofReal_injective h''
  have ha2 : a = -1 := by linarith
  rw [ha2] at ha
  norm_num at ha

theorem mem_upperHalf_I : Complex.I ∈ upperHalf := by simp [upperHalf]

theorem mem_lowerHalf_negI : -Complex.I ∈ lowerHalf := by simp [lowerHalf]

/-! ## The star-shapedness of the four regions -/

theorem eq_ofReal_div_of_mul {r : ℂ} {t a : ℝ} (h1t : (0 : ℝ) < 1 - t)
    (h : (1 - (t : ℂ)) * r = (a : ℂ) + (t : ℂ)) :
    r = (((a + t) / (1 - t) : ℝ) : ℂ) := by
  have hne : (1 - (t : ℂ)) ≠ 0 := by
    have : ((1 - t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt h1t)
    simpa using this
  push_cast
  rw [eq_div_iff hne, mul_comm r]
  exact h

theorem eq_neg_ofReal_div_of_mul {r : ℂ} {t a : ℝ} (h1t : (0 : ℝ) < 1 - t)
    (h : (1 - (t : ℂ)) * r = -((a : ℂ) + (t : ℂ))) :
    r = -(((a + t) / (1 - t) : ℝ) : ℂ) := by
  have hne : (1 - (t : ℂ)) ≠ 0 := by
    have : ((1 - t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt h1t)
    simpa using this
  have hgoal : r * (1 - (t : ℂ)) = -((a : ℂ) + (t : ℂ)) := by
    rw [mul_comm r]; exact h
  rw [show -(((a + t) / (1 - t) : ℝ) : ℂ) = (-((a : ℂ) + (t : ℂ))) / (1 - (t : ℂ)) from by
    push_cast; ring]
  rw [eq_div_iff hne]
  exact hgoal

theorem rayNN_compl_star (r : ℂ) (hr : r ∈ rayNNᶜ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * r + t * (-1) ∈ rayNNᶜ := by
  intro hmem
  by_cases ht : t = 1
  · rw [ht] at hmem
    have h1 : (1 - (1 : ℝ)) * r + (1 : ℝ) * (-1 : ℂ) = -1 := by push_cast; ring
    rw [h1] at hmem
    exact neg_one_notMem_rayNN hmem
  · have h1t : (0 : ℝ) < 1 - t := by
      have : t < 1 := lt_of_le_of_ne ht1 ht
      linarith
    obtain ⟨a, ha, hae⟩ := hmem
    have hgoal : (1 - (t : ℂ)) * r = (a : ℂ) + (t : ℂ) := by
      have h := hae
      push_cast at h
      linear_combination h
    refine hr ⟨(a + t) / (1 - t), div_nonneg (by linarith) (le_of_lt h1t), ?_⟩
    exact eq_ofReal_div_of_mul h1t hgoal

theorem rayNP_compl_star (r : ℂ) (hr : r ∈ rayNPᶜ) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * r + t * 1 ∈ rayNPᶜ := by
  intro hmem
  by_cases ht : t = 1
  · rw [ht] at hmem
    have h1 : (1 - (1 : ℝ)) * r + (1 : ℝ) * (1 : ℂ) = 1 := by push_cast; ring
    rw [h1] at hmem
    exact one_notMem_rayNP hmem
  · have h1t : (0 : ℝ) < 1 - t := by
      have : t < 1 := lt_of_le_of_ne ht1 ht
      linarith
    obtain ⟨a, ha, hae⟩ := hmem
    have hgoal : (1 - (t : ℂ)) * r = -((a : ℂ) + (t : ℂ)) := by
      have h := hae
      push_cast at h
      linear_combination h
    refine hr ⟨(a + t) / (1 - t), div_nonneg (by linarith) (le_of_lt h1t), ?_⟩
    exact eq_neg_ofReal_div_of_mul h1t hgoal

theorem upperHalf_star (r : ℂ) (hr : r ∈ upperHalf) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * r + t * Complex.I ∈ upperHalf := by
  have hr' : 0 < r.im := hr
  have h2 : ((1 - t) * r + t * Complex.I).im = (1 - t) * r.im + t := by
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [upperHalf, Set.mem_setOf_eq, h2]
  rcases eq_or_lt_of_le ht1 with h | h
  · subst h; norm_num
  · have hlt : (0 : ℝ) < 1 - t := by linarith
    nlinarith

theorem lowerHalf_star (r : ℂ) (hr : r ∈ lowerHalf) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * r + t * (-Complex.I) ∈ lowerHalf := by
  have hr' : r.im < 0 := hr
  have h2 : ((1 - t) * r + t * (-Complex.I)).im = (1 - t) * r.im - t := by
    simp [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, sub_eq_add_neg]
  rw [lowerHalf, Set.mem_setOf_eq, h2]
  rcases eq_or_lt_of_le ht1 with h | h
  · subst h; norm_num
  · have hlt : (0 : ℝ) < 1 - t := by linarith
    nlinarith

/-! ## The vanishing of `H^k` on `uvA`, `uvB`, `uvP`, `uvQ` -/

theorem uvA_cohomology_zero (k : ℕ) (hk0 : k ≠ 0) (hk5 : k ≠ 5) :
    Subsingleton (Work.Thom.Coh ℤ k ↥uvA) :=
  uvPiece_cohomology_zero rayNNᶜ (-1) neg_one_notMem_rayNN (by simpa using zero_mem_rayNN)
    rayNN_compl_star k hk0 hk5

theorem uvB_cohomology_zero (k : ℕ) (hk0 : k ≠ 0) (hk5 : k ≠ 5) :
    Subsingleton (Work.Thom.Coh ℤ k ↥uvB) :=
  uvPiece_cohomology_zero rayNPᶜ 1 one_notMem_rayNP (by simpa using zero_mem_rayNP)
    rayNP_compl_star k hk0 hk5

theorem uvP_cohomology_zero (k : ℕ) (hk0 : k ≠ 0) (hk5 : k ≠ 5) :
    Subsingleton (Work.Thom.Coh ℤ k ↥uvP) :=
  uvPiece_cohomology_zero upperHalf Complex.I mem_upperHalf_I (by simp [upperHalf])
    upperHalf_star k hk0 hk5

theorem uvQ_cohomology_zero (k : ℕ) (hk0 : k ≠ 0) (hk5 : k ≠ 5) :
    Subsingleton (Work.Thom.Coh ℤ k ↥uvQ) :=
  uvPiece_cohomology_zero lowerHalf (-Complex.I) mem_lowerHalf_negI (by simp [lowerHalf])
    lowerHalf_star k hk0 hk5

/-! ## Mayer–Vietoris -/

/-- An element of a biproduct is determined by its two components. -/
lemma biprod_eq_of_fst_snd {A X Y : ModuleCat ℤ} (f : A ⟶ X ⊞ Y) {a b : A}
    (h₁ : (biprod.fst : X ⊞ Y ⟶ X).hom (ModuleCat.Hom.hom f a)
      = (biprod.fst : X ⊞ Y ⟶ X).hom (ModuleCat.Hom.hom f b))
    (h₂ : (biprod.snd : X ⊞ Y ⟶ Y).hom (ModuleCat.Hom.hom f a)
      = (biprod.snd : X ⊞ Y ⟶ Y).hom (ModuleCat.Hom.hom f b)) :
    ModuleCat.Hom.hom f a = ModuleCat.Hom.hom f b := by
  have htot := congrArg (fun (g : X ⊞ Y ⟶ X ⊞ Y) => ModuleCat.Hom.hom g (ModuleCat.Hom.hom f a))
    biprod.total
  have htot' := congrArg (fun (g : X ⊞ Y ⟶ X ⊞ Y) => ModuleCat.Hom.hom g (ModuleCat.Hom.hom f b))
    biprod.total
  simp only [ModuleCat.hom_add, ModuleCat.hom_comp, LinearMap.add_apply, LinearMap.comp_apply,
    ModuleCat.hom_id, LinearMap.id_apply] at htot htot'
  rw [h₁, h₂] at htot
  exact htot.symm.trans htot'

/-- **Two-set Mayer–Vietoris in the form used below**: if `H^k` vanishes on two open sets covering
a space, and `H^{k-1}` vanishes on their intersection, then `H^k` vanishes on the space.

Indeed, the exact sequence `H^{k-1}(U ∩ V) --δ--> H^k(X) --F--> H^k(U) ⊞ H^k(V)` has `F` with
trivial target, so `H^k(X) = ker F = range δ = 0`. -/
theorem subsingleton_of_mv2 {X : Type} [TopologicalSpace X] (U V : Set X) (hU : IsOpen U)
    (hV : IsOpen V) (hcov : U ∪ V = Set.univ) (k : ℕ) (hk : 1 ≤ k)
    (hU' : Subsingleton (Work.Thom.Coh ℤ k ↥U)) (hV' : Subsingleton (Work.Thom.Coh ℤ k ↥V))
    (hUV : Subsingleton (Work.Thom.Coh ℤ (k - 1) ↥(U ∩ V))) :
    Subsingleton (Work.Thom.Coh ℤ k X) := by
  haveI := hU'
  haveI := hV'
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  haveI : Subsingleton (Work.Thom.Coh ℤ k' ↥(U ∩ V)) := by simpa using hUV
  have hmv := Work.LerayHirsch.mv2_exact U V hU hV hcov
  have hdelta : (Work.LerayHirsch.mv2δ U V hU hV hcov k').hom = 0 := by
    refine LinearMap.ext fun x => ?_
    rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
  have hker : (Work.LerayHirsch.mv2F U V (k' + 1)).hom.ker = ⊥ := by
    rw [← hmv.2.2.1 k', hdelta, LinearMap.range_zero]
  have hinj : Function.Injective (Work.LerayHirsch.mv2F U V (k' + 1)).hom :=
    LinearMap.ker_eq_bot.mp hker
  refine ⟨fun a b => hinj ?_⟩
  refine biprod_eq_of_fst_snd _ ?_ ?_
  · exact Subsingleton.elim _ _
  · exact Subsingleton.elim _ _

/-- The underlying point of a point of `uvA ∩ uvB`, as a point of the overlap. -/
def uvSubMap : ↥(uvA ∩ uvB) → ↥(UR ∩ VR) := fun p => p.1

/-- The part of `uvA ∩ uvB` lying over a subset `T` of the overlap. -/
def uvSubSet (T : Set ↥(UR ∩ VR)) : Set ↥(uvA ∩ uvB) := uvSubMap ⁻¹' T

/-- The first component of `uvA ∩ uvB`. -/
abbrev uvPsub : Set ↥(uvA ∩ uvB) := uvSubSet uvP

/-- The second component of `uvA ∩ uvB`. -/
abbrev uvQsub : Set ↥(uvA ∩ uvB) := uvSubSet uvQ

/-- The `T`-part of `uvA ∩ uvB` is the piece `T`. -/
def uvSubHomeo (T : Set ↥(UR ∩ VR)) (hT : T ⊆ uvA ∩ uvB) :
    ↥(uvSubSet T) ≃ₜ ↥T where
  toFun p := ⟨p.1.1, p.2⟩
  invFun q := ⟨⟨q.1, hT q.2⟩, q.2⟩
  left_inv p := Subtype.ext (Subtype.ext rfl)
  right_inv q := Subtype.ext rfl
  continuous_toFun := Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val)
    (fun p => p.2)
  continuous_invFun := Continuous.subtype_mk
    (Continuous.subtype_mk continuous_subtype_val (fun q => hT q.2)) (fun q => q.2)

theorem uvP_subset : uvP ⊆ uvA ∩ uvB := by
  rw [uvA_inter_uvB]
  exact Set.subset_union_left

theorem uvQ_subset : uvQ ⊆ uvA ∩ uvB := by
  rw [uvA_inter_uvB]
  exact Set.subset_union_right

theorem isOpen_uvPsub : IsOpen uvPsub :=
  (uvPieceIsOpen upperHalf isOpen_upperHalf).preimage continuous_subtype_val

theorem isOpen_uvQsub : IsOpen uvQsub :=
  (uvPieceIsOpen lowerHalf isOpen_lowerHalf).preimage continuous_subtype_val

theorem uvSubSet_cov : ∀ q : ↥(UR ∩ VR), q ∈ uvA ∩ uvB → q ∈ uvP ∪ uvQ := by
  intro q hq
  rw [uvA_inter_uvB] at hq
  exact hq

theorem uvSubSet_disj : ∀ q : ↥(UR ∩ VR), q ∈ uvP ∩ uvQ → False := by
  intro q hq
  rw [uvP_inter_uvQ] at hq
  exact hq

theorem uvPsub_union_uvQsub : uvPsub ∪ uvQsub = Set.univ := by
  refine Set.eq_univ_of_forall fun p => ?_
  rcases uvSubSet_cov p.1 p.2 with hp | hp
  · exact Or.inl hp
  · exact Or.inr hp

theorem uvPsub_inter_uvQsub : uvPsub ∩ uvQsub = ∅ := by
  ext p
  constructor
  · rintro ⟨h1, h2⟩
    exact uvSubSet_disj p.1 ⟨h1, h2⟩
  · intro h
    exact absurd h (Set.notMem_empty p)

theorem uvPsub_cohomology_zero (k : ℕ) (hk0 : k ≠ 0) (hk5 : k ≠ 5) :
    Subsingleton (Work.Thom.Coh ℤ k ↥uvPsub) := by
  haveI : Subsingleton (Work.Thom.Coh ℤ k ↥uvP) := uvP_cohomology_zero k hk0 hk5
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
    (uvSubHomeo uvP uvP_subset).toHomotopyEquiv k
  exact ModuleCat.subsingleton_of_isZero
    (CategoryTheory.Limits.IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) iso)

theorem uvQsub_cohomology_zero (k : ℕ) (hk0 : k ≠ 0) (hk5 : k ≠ 5) :
    Subsingleton (Work.Thom.Coh ℤ k ↥uvQsub) := by
  haveI : Subsingleton (Work.Thom.Coh ℤ k ↥uvQ) := uvQ_cohomology_zero k hk0 hk5
  obtain ⟨iso⟩ := Work.Cohomology.cohomologyIso_of_homotopyEquiv
    (uvSubHomeo uvQ uvQ_subset).toHomotopyEquiv k
  exact ModuleCat.subsingleton_of_isZero
    (CategoryTheory.Limits.IsZero.of_iso (ModuleCat.isZero_of_subsingleton _) iso)

theorem uvPsubQ_cohomology_zero (k : ℕ) :
    Subsingleton (Work.Thom.Coh ℤ k ↥(uvPsub ∩ uvQsub)) := by
  rw [uvPsub_inter_uvQsub]
  exact uvEmptyCohomology ↥(uvA ∩ uvB) k

/-- **`H^k` of `uvA ∩ uvB = uvP ⊔ uvQ` vanishes** for `1 ≤ k`, `k ≠ 0, 5`. -/
theorem uvAB_cohomology_zero (k : ℕ) (hk : 1 ≤ k) (hk0 : k ≠ 0) (hk5 : k ≠ 5) :
    Subsingleton (Work.Thom.Coh ℤ k ↥(uvA ∩ uvB)) :=
  subsingleton_of_mv2 uvPsub uvQsub isOpen_uvPsub isOpen_uvQsub uvPsub_union_uvQsub k hk
    (uvPsub_cohomology_zero k hk0 hk5) (uvQsub_cohomology_zero k hk0 hk5)
    (uvPsubQ_cohomology_zero (k - 1))

/-! ## The target -/

theorem zStd_UV_cohomology :
    Subsingleton (Work.Thom.Coh ℤ 3 ↥(Work.ThomBordism.Grassmann.UR ∩ Work.ThomBordism.Grassmann.VR)) :=
  subsingleton_of_mv2 uvA uvB (uvPieceIsOpen rayNNᶜ isOpen_rayNN_compl)
    (uvPieceIsOpen rayNPᶜ isOpen_rayNP_compl) uvA_union_uvB 3 (by norm_num)
    (uvA_cohomology_zero 3 (by norm_num) (by norm_num))
    (uvB_cohomology_zero 3 (by norm_num) (by norm_num))
    (uvAB_cohomology_zero 2 (by norm_num) (by norm_num) (by norm_num))

end

end Work.ThomBordism.Grassmann
