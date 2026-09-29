import Submission.Transcendence.LindemannB
import Submission.Helpers

/-!
# Lindemann–Weierstrass: Lemma B and Lindemann's theorem

**This module completes the Lindemann–Weierstrass chapter** whose engine
(Lemma A, `lemmaA_orbit_contradiction`) and symmetrization data
(`ChoiceFun`, `chCoeff`/`chVal`, `chValues`/`chGrouped`/`chSupport`,
`lemmaA_grouped`) live in `LindemannB.lean` (see its docstring and the §11
roadmap in `Lindemann.lean`).

**§17.3b — conjugacy closure and class constancy.**  For a conj-closed
injective algebraic family `γ : Fin N → ℂ` the grouped coefficients
`chGrouped γ b` are constant on the `conjRoots`-classes of values and every
value-class is conj-closed.  The proof goes through the *family field*
`famField γ` (the compositum of the splitting fields of the minimal
polynomials — normal over ℚ, contains every `γ k`), Galois automorphisms
σ of it, and the *relabeling* action `relabel π` on choice functions
(`chValF_aut_relabel`: σ applied to a choice-sum equals the value of the
π-relabeled choice, where σ sends `γ i ↦ γ (π i)`).

* the family field: `famField`, `famField_mem`, `famField_normal`,
  `famElem`; in-field sums `chValF` with `chValF_val`/`chValF_relabel`;
* conjugates live in the field (`conj_mem_famField`); the value element
  `chValElem`; `exists_gal_of_conj` (a Galois automorphism moving a value
  to a given conjugate); `gal_map_conjRoots` (automorphisms permute the
  family through conjugates); `exists_perm_of_gal`;
* `chVal_conj_relabel` — a conjugate value of a choice is the relabeled
  value of the same choice;
* `conj_mem_chValues`, `chGrouped_conj` — class constancy.

**§17.4 — the nonzero grouped coefficient.**  Equip ℂ with the
lexicographic order (real then imaginary part): `LexLT`/`LexLE`,
`LexLT_sum_of_pointwise` (additive strictness), the lex-max choice
`lexMaxChoice`; every *supported* choice has strictly smaller value than
the lex-max one, so the lex-max value has grouped coefficient equal to the
lex-max choice's own product coefficient (nonzero):
`chGrouped_eq_chCoeff_of_max`, `exists_nonzero_chGrouped`.

**§17.5 — Lemma B for conj-closed families.**  `lemmaB_conjClosed`: an
injective conj-closed algebraic family with an integer coefficient not all
zero cannot satisfy `Σ_k b_k·e^{γ_k} = 0` (feeds `lemmaA_grouped`).

**§17.6 — dropping the hypothesis.**  `conjSet` (the finite union of the
conjugacy classes), `conjEnum` (its enumeration), `conjExtendCoeff`
(zero-extension of the coefficients); `lemmaB` — Lemma B proper: distinct
algebraic exponents with integer coefficients, not all zero, have no
exponential relation.

**§17.7 — Lindemann's theorem.**  `cexp_transcendental_of_algebraic_ne_zero`:
`e^z` is transcendental over ℚ for algebraic `z ≠ 0` (via Lemma B on the
exponents `{0, z, …, d·z}` from a ℤ-minimal relation of `e^z`).

**§17.8 — corollaries.**  `isAlgebraic_I`; `transcendental_pi_complex`
(π transcendental over ℚ); `isAlgebraic_rat_complex`;
`transcendental_log_rat` (the real logarithm of a positive rational ≠ 1 is
transcendental); `irrational_log_one_add_inv_sq` (the `m = n` corner of
CDT Theorem C: `(log(1+1/m))²` is irrational for `m ∉ {-1,0}`).
-/

open scoped BigOperators
open scoped Complex
open Polynomial
set_option maxHeartbeats 800000
noncomputable section

namespace Submission.Transcendence

/-- relabel a choice function: (relabel π k)(τ) = k (π⁻¹ * τ). -/
def relabel {N : ℕ} (π : Equiv.Perm (Fin N)) (k : ChoiceFun N) : ChoiceFun N :=
  fun τ => k (π⁻¹ * τ)

/-- The relabeled value equals the sum with each exponent acted on by π. -/
lemma chVal_relabel {N : ℕ} (γ : Fin N → ℂ) (π : Equiv.Perm (Fin N)) (k : ChoiceFun N) :
    chVal γ (relabel π k) = ∑ σ : Equiv.Perm (Fin N), γ (π (σ (k σ))) := by
  classical
  let G := Equiv.Perm (Fin N)
  let f : G → ℂ := fun τ => γ (τ (k (π⁻¹ * τ)))
  have hsub : (∑ σ : G, γ ((π * σ) (k σ))) = (∑ τ : G, f τ) := by
    -- apply Equiv.sum_comp with e := mulLeft π, g := f :  ∑ σ f (π*σ) = ∑ σ f σ
    calc
      (∑ σ : G, γ ((π * σ) (k σ))) = (∑ σ : G, f (π * σ)) := by
        apply Finset.sum_congr rfl
        intro σ hσ
        dsimp [f]
        congr 1
        rw [inv_mul_cancel_left]  -- π⁻¹ * (π * σ) = σ -- hmm need π⁻¹*(π*σ): correct group lemma?
      _ = (∑ τ : G, f τ) := by
        simpa using (Equiv.sum_comp (e := (Equiv.mulLeft π : G ≃ G)) (g := f))
  have hmain : chVal γ (relabel π k) = (∑ σ : G, γ ((π * σ) (k σ))) := by
    calc
      chVal γ (relabel π k) = (∑ τ : G, f τ) := by
        dsimp [chVal, relabel, f]
      _ = (∑ σ : G, γ ((π * σ) (k σ))) := hsub.symm
  calc
    chVal γ (relabel π k) = (∑ σ : G, γ ((π * σ) (k σ))) := hmain
    _ = ∑ σ : G, γ (π (σ (k σ))) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [Equiv.Perm.mul_apply]

/-- relabeling preserves the coefficient (product over the whole group). -/
lemma chCoeff_relabel {N : ℕ} (b : Fin N → ℤ) (π : Equiv.Perm (Fin N)) (k : ChoiceFun N) :
    chCoeff b (relabel π k) = chCoeff b k := by
  classical
  let G := Equiv.Perm (Fin N)
  calc
    chCoeff b (relabel π k) = ∏ σ : G, b (k (π⁻¹ * σ)) := by
      dsimp [chCoeff, relabel]
    _ = ∏ σ : G, b (k σ) := by
      -- Equiv.prod_comp (mulLeft π⁻¹): ∏ σ g(π⁻¹ * σ) = ∏ σ g(σ), g := fun τ => b (k τ)
      simpa using (Equiv.prod_comp (e := (Equiv.mulLeft (π⁻¹) : G ≃ G)) (g := fun τ : G => b (k τ)))
    _ = chCoeff b k := by
      dsimp [chCoeff]

/-- relabeling is a bijection of choice functions (inverse: relabel π⁻¹). -/
def relabelEquiv {N : ℕ} (π : Equiv.Perm (Fin N)) : ChoiceFun N ≃ ChoiceFun N where
  toFun := relabel π
  invFun := relabel π⁻¹
  left_inv k := by
    ext τ
    dsimp [relabel]
    simp [mul_assoc]
  right_inv k := by
    ext τ
    dsimp [relabel]
    simp [mul_assoc]

/-- coe of the relabeling equivalence -/
@[simp] lemma relabelEquiv_apply {N : ℕ} (π : Equiv.Perm (Fin N)) (k : ChoiceFun N) :
    relabelEquiv π k = relabel π k := rfl

/-! ## §17.3b development (in scratch) — the normal family field -/

/-- The splitting-field compositum of the minimal polynomials of the family
values: a normal intermediate field containing every `γ k`. -/
def famField {N : ℕ} (γ : Fin N → ℂ) : IntermediateField ℚ ℂ :=
  ⨆ k : Fin N, IntermediateField.adjoin ℚ ((minpoly ℚ (γ k)).rootSet ℂ)

lemma famField_mem_rootSet {N : ℕ} (γ : Fin N → ℂ) (halg : ∀ k : Fin N, IsAlgebraic ℚ (γ k))
    (k : Fin N) : γ k ∈ (minpoly ℚ (γ k)).rootSet ℂ := by
  have hzi : IsIntegral ℚ (γ k) := isAlgebraic_iff_isIntegral.mp (halg k)
  rw [Polynomial.rootSet_def]
  exact Multiset.mem_toFinset.2 (by
    rw [Polynomial.mem_aroots]
    exact ⟨minpoly.ne_zero hzi, minpoly.aeval ℚ (γ k)⟩)

lemma famField_mem {N : ℕ} (γ : Fin N → ℂ) (halg : ∀ k : Fin N, IsAlgebraic ℚ (γ k))
    (k : Fin N) : γ k ∈ famField γ := by
  dsimp [famField]
  exact (le_iSup (fun i : Fin N =>
      IntermediateField.adjoin ℚ ((minpoly ℚ (γ i)).rootSet ℂ)) k)
    (IntermediateField.subset_adjoin ℚ ((minpoly ℚ (γ k)).rootSet ℂ)
      (famField_mem_rootSet γ halg k))

/-- The family field is normal over ℚ. -/
lemma famField_normal {N : ℕ} (γ : Fin N → ℂ) : Normal ℚ (famField γ) := by
  classical
  have ht : ∀ i : Fin N, Normal ℚ (IntermediateField.adjoin ℚ ((minpoly ℚ (γ i)).rootSet ℂ)) := by
    intro i
    haveI : IsSplittingField ℚ (IntermediateField.adjoin ℚ ((minpoly ℚ (γ i)).rootSet ℂ))
        (minpoly ℚ (γ i)) := by
      exact IntermediateField.adjoin_rootSet_isSplittingField
        (p := minpoly ℚ (γ i))
        (IsAlgClosed.splits ((minpoly ℚ (γ i)).map (algebraMap ℚ ℂ)))
    exact Normal.of_isSplittingField (p := minpoly ℚ (γ i))
  change Normal ℚ ((⨆ i : Fin N,
    (IntermediateField.adjoin ℚ ((minpoly ℚ (γ i)).rootSet ℂ) : IntermediateField ℚ ℂ)) : IntermediateField ℚ ℂ)
  exact @IntermediateField.normal_iSup ℚ ℂ _ _ _ (Fin N)
    (fun i => (IntermediateField.adjoin ℚ ((minpoly ℚ (γ i)).rootSet ℂ) : IntermediateField ℚ ℂ)) ht

/-- the family as elements of the family field -/
def famElem {N : ℕ} (γ : Fin N → ℂ) (halg : ∀ k : Fin N, IsAlgebraic ℚ (γ k))
    (k : Fin N) : famField γ := ⟨γ k, famField_mem γ halg k⟩

@[simp] lemma famElem_val {N : ℕ} (γ : Fin N → ℂ) (halg : ∀ k : Fin N, IsAlgebraic ℚ (γ k))
    (k : Fin N) : (famElem γ halg k : ℂ) = γ k := rfl

/-! ### §17.3b — value of a choice under a field automorphism (relabel) -/

/-- the choice-sum computed inside an intermediate field -/
def chValF {N : ℕ} {F : Type*} [Field F] (γF : Fin N → F) (k : ChoiceFun N) : F :=
  ∑ τ : Equiv.Perm (Fin N), γF (τ (k τ))

/-- σ-linearity of the choice-sum in F (map_sum form) -/
lemma chValF_map {N : ℕ} {F : Type*} [Field F] {G : Type*} [FunLike G F F]
    [AddMonoidHomClass G F F] (σ : G) (γF : Fin N → F) (k : ChoiceFun N) :
    σ (chValF γF k) = chValF (fun i => σ (γF i)) k := by
  classical
  dsimp [chValF]
  rw [map_sum σ (fun τ : Equiv.Perm (Fin N) => γF (τ (k τ))) (Finset.univ)]

/-- val (coercion ℂ) of the F-sum is the ℂ-sum -/
lemma chValF_val {N : ℕ} (E : IntermediateField ℚ ℂ) (γE : Fin N → E) (k : ChoiceFun N) :
    ((chValF (F := E) γE k : E) : ℂ) = chVal (fun i : Fin N => (γE i : ℂ)) k := by
  classical
  change E.val (chValF (F := E) γE k) = (chVal (fun i : Fin N => (γE i : ℂ)) k)
  unfold chValF chVal
  exact map_sum (E.val : E →+* ℂ) (fun τ : Equiv.Perm (Fin N) => γE (τ (k τ))) (Finset.univ)
/-- relabel identity for the F-sum (generic field version of `chVal_relabel`). -/
lemma chValF_relabel {N : ℕ} {F : Type*} [Field F] (γF : Fin N → F)
    (π : Equiv.Perm (Fin N)) (k : ChoiceFun N) :
    chValF γF (relabel π k) = ∑ σ : Equiv.Perm (Fin N), γF (π (σ (k σ))) := by
  classical
  let G := Equiv.Perm (Fin N)
  let f : G → F := fun τ => γF (τ (k (π⁻¹ * τ)))
  have hsub : (∑ σ : G, γF ((π * σ) (k σ))) = (∑ τ : G, f τ) := by
    calc
      (∑ σ : G, γF ((π * σ) (k σ))) = (∑ σ : G, f (π * σ)) := by
        apply Finset.sum_congr rfl
        intro σ hσ
        dsimp [f]
        congr 1
        rw [inv_mul_cancel_left]
      _ = (∑ τ : G, f τ) := by
        simpa using (Equiv.sum_comp (e := (Equiv.mulLeft π : G ≃ G)) (g := f))
  calc
    chValF γF (relabel π k) = (∑ τ : G, f τ) := by
      dsimp [chValF, relabel, f]
    _ = (∑ σ : G, γF ((π * σ) (k σ))) := hsub.symm
    _ = ∑ σ : G, γF (π (σ (k σ))) := by
      apply Finset.sum_congr rfl
      intro σ hσ
      rw [Equiv.Perm.mul_apply]

/-- Under an automorphism sending `γF i ↦ γF (π i)`, the value of a choice
transforms by the relabeling: `σ (chValF γF k) = chValF γF (relabel π k)`. -/
lemma chValF_aut_relabel {N : ℕ} (γ : Fin N → ℂ) (halg : ∀ k : Fin N, IsAlgebraic ℚ (γ k))
    (π : Equiv.Perm (Fin N)) (σ : famField γ ≃ₐ[ℚ] famField γ)
    (hσ : ∀ i : Fin N, σ (famElem γ halg i) = famElem γ halg (π i))
    (k : ChoiceFun N) :
    σ (chValF (famElem γ halg) k) = chValF (famElem γ halg) (relabel π k) := by
  classical
  let E := famField γ
  let γE : Fin N → E := famElem γ halg
  have h1 : σ (chValF (F := E) γE k) = chValF (fun i => σ (γE i)) k := chValF_map (F := E) σ γE k
  have h2 : chValF (fun i => σ (γE i)) k = chValF γE (relabel π k) := by
    have hσf : (fun i => σ (γE i)) = fun i => γE (π i) := by
      funext i
      exact hσ i
    rw [hσf, chValF_relabel γE π k]
    dsimp [chValF]
  calc
    σ (chValF (F := E) γE k) = chValF (fun i => σ (γE i)) k := h1
    _ = chValF γE (relabel π k) := h2

/-! ### §17.3b — the Galois permutation for a conjugate value -/

/-- a finite sum of family elements stays in the family field -/
lemma famField_sum_mem {N : ℕ} (γ : Fin N → ℂ) (halg : ∀ k : Fin N, IsAlgebraic ℚ (γ k))
    (s : Finset (Equiv.Perm (Fin N))) (k : ChoiceFun N) :
    (∑ σ ∈ s, γ (σ (k σ))) ∈ famField γ := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [famField]  -- zero_mem of intermediate field? try
  · intro τ s hτ ih
    rw [Finset.sum_insert hτ]
    exact add_mem (famField_mem γ halg (τ (k τ))) ih

/-- the choice value of a choice function lies in the family field -/
lemma chVal_mem_famField {N : ℕ} (γ : Fin N → ℂ) (halg : ∀ k : Fin N, IsAlgebraic ℚ (γ k))
    (k : ChoiceFun N) : chVal γ k ∈ famField γ := by
  classical
  dsimp [chVal]
  exact famField_sum_mem γ halg (Finset.univ : Finset (Equiv.Perm (Fin N))) k

/-- the value element of the family field -/
def chValElem {N : ℕ} (γ : Fin N → ℂ) (halg : ∀ k : Fin N, IsAlgebraic ℚ (γ k))
    (k : ChoiceFun N) : famField γ := ⟨chVal γ k, chVal_mem_famField γ halg k⟩

@[simp] lemma chValElem_val {N : ℕ} (γ : Fin N → ℂ) (halg : ∀ k : Fin N, IsAlgebraic ℚ (γ k))
    (k : ChoiceFun N) : (chValElem γ halg k : ℂ) = chVal γ k := rfl

/-- chValElem equals the in-field choice-sum -/
lemma chValElem_eq_chValF {N : ℕ} (γ : Fin N → ℂ) (halg : ∀ k : Fin N, IsAlgebraic ℚ (γ k))
    (k : ChoiceFun N) : chValElem γ halg k = chValF (F := famField γ) (famElem γ halg) k := by
  classical
  apply Subtype.ext
  rw [chValF_val (famField γ) (famElem γ halg) k]
  simp

/-- a conjugate of a value lies in the family field (normality) -/
lemma conj_mem_famField {N : ℕ} (γ : Fin N → ℂ) (halg : ∀ k : Fin N, IsAlgebraic ℚ (γ k))
    (k : ChoiceFun N) {u : ℂ} (hu : u ∈ conjRoots (chVal γ k)) : u ∈ famField γ := by
  classical
  let F := famField γ
  let v := chVal γ k
  let vF : F := ⟨v, chVal_mem_famField γ halg k⟩
  haveI : Normal ℚ F := famField_normal γ
  have hvintF : IsIntegral ℚ vF := Normal.isIntegral (famField_normal γ) vF
  have hmin_eq : minpoly ℚ v = minpoly ℚ (vF : F) := by
    exact (minpoly.algebraMap_eq (A := ℚ) (h := by
      -- injectivity of val : F → ℂ
      intro x y hxy
      exact Subtype.ext hxy) vF)
  have hintV : IsIntegral ℚ v := by
    refine ⟨minpoly ℚ vF, ?_, ?_⟩
    · exact minpoly.monic hvintF
    · rw [← hmin_eq]
      exact minpoly.aeval ℚ v
  have hmin_ne0 : minpoly ℚ v ≠ 0 := minpoly.ne_zero hintV
  have haeval_u : aeval u (minpoly ℚ v) = 0 := by
    simpa [v] using (aeval_mem_conjRoots (z := v) hu)
  have hConj : IsConjRoot ℚ v u := by
    exact isConjRoot_of_aeval_eq_zero (K := ℚ) hintV haeval_u
  have hminu : minpoly ℚ u = minpoly ℚ v := hConj.symm
  have hintU : IsIntegral ℚ u := IsConjRoot.isIntegral hintV hConj
  have hspl : Splits ((minpoly ℚ u).map (algebraMap ℚ F)) := by
    rw [hminu, hmin_eq]
    have hs := Normal.splits (famField_normal γ) vF
    simpa using hs
  exact IsIntegral.mem_intermediateField_of_minpoly_splits (K := ℚ) (L := ℂ)
    (F := F) hintU hspl

/-- an automorphism of the family field preserves the minimal polynomial of
each family element (i.e. maps it to a conjugate). -/
lemma gal_map_conjRoots {N : ℕ} (γ : Fin N → ℂ) (halg : ∀ k : Fin N, IsAlgebraic ℚ (γ k))
    (σ : famField γ ≃ₐ[ℚ] famField γ) (i : Fin N) :
    (σ (famElem γ halg i) : ℂ) ∈ conjRoots (γ i) := by
  classical
  let F := famField γ
  have hConjF : IsConjRoot ℚ (famElem γ halg i) (σ (famElem γ halg i)) := by
    exact isConjRoot_of_algEquiv (famElem γ halg i) σ
  have hminF_γ : minpoly ℚ (famElem γ halg i : F) = minpoly ℚ (γ i) := by
    exact (minpoly.algebraMap_eq (A := ℚ) (h := by
      intro x y hxy
      exact Subtype.ext hxy) (famElem γ halg i)).symm
  have hminσ : minpoly ℚ (σ (famElem γ halg i) : F) = minpoly ℚ ((σ (famElem γ halg i) : F) : ℂ) := by
    exact (minpoly.algebraMap_eq (A := ℚ) (h := by
      intro x y hxy
      exact Subtype.ext hxy) (σ (famElem γ halg i) : F)).symm
  have h1 : minpoly ℚ (γ i) = minpoly ℚ ((σ (famElem γ halg i) : F) : ℂ) := by
    calc
      minpoly ℚ (γ i) = minpoly ℚ (famElem γ halg i : F) := hminF_γ.symm
      _ = minpoly ℚ (σ (famElem γ halg i) : F) := by
        exact (hConjF : minpoly ℚ (famElem γ halg i) = minpoly ℚ (σ (famElem γ halg i)))
      _ = minpoly ℚ ((σ (famElem γ halg i) : F) : ℂ) := hminσ
  have haev : aeval ((σ (famElem γ halg i) : F) : ℂ) (minpoly ℚ (γ i)) = 0 := by
    rw [h1]
    exact minpoly.aeval ℚ ((σ (famElem γ halg i) : F) : ℂ)
  exact conjRoots_of_aeval (halg i) haev

/-- an element of the family field integral over ℚ is integral as a complex number -/
lemma isIntegral_val {F : IntermediateField ℚ ℂ} (x : F) (hx : IsIntegral ℚ x) :
    IsIntegral ℚ (x : ℂ) := by
  refine ⟨minpoly ℚ x, minpoly.monic hx, ?_⟩
  have hmin : minpoly ℚ (x : ℂ) = minpoly ℚ x := by
    exact minpoly.algebraMap_eq (A := ℚ) (h := by
      intro a b hab
      exact Subtype.ext hab) x
  rw [← hmin]
  exact minpoly.aeval ℚ (x : ℂ)

/-- the minimal polynomial over ℚ of a value and of its conjugate coincide -/
lemma minpoly_conj_eq {N : ℕ} (γ : Fin N → ℂ) (halg : ∀ k : Fin N, IsAlgebraic ℚ (γ k))
    (k : ChoiceFun N) {u : ℂ} (hu : u ∈ conjRoots (chVal γ k)) :
    minpoly ℚ u = minpoly ℚ (chVal γ k) := by
  classical
  have hintC : IsIntegral ℚ (chVal γ k) := by
    let F := famField γ
    let vF : F := ⟨chVal γ k, chVal_mem_famField γ halg k⟩
    have hvintF : IsIntegral ℚ vF := by
      haveI : Normal ℚ F := famField_normal γ
      exact Normal.isIntegral (famField_normal γ) vF
    simpa using (isIntegral_val (F := F) vF hvintF)
  have haev : aeval u (minpoly ℚ (chVal γ k)) = 0 := by
    simpa using (aeval_mem_conjRoots (z := chVal γ k) hu)
  have hConj : IsConjRoot ℚ (chVal γ k) u :=
    isConjRoot_of_aeval_eq_zero (K := ℚ) hintC haev
  exact hConj.symm

/-- a conjugate of a value is moved by a Galois automorphism -/
lemma exists_gal_of_conj {N : ℕ} (γ : Fin N → ℂ) (halg : ∀ k : Fin N, IsAlgebraic ℚ (γ k))
    (k : ChoiceFun N) {u : ℂ} (hu : u ∈ conjRoots (chVal γ k)) :
    ∃ σ : famField γ ≃ₐ[ℚ] famField γ,
      σ (chValElem γ halg k) = ⟨u, conj_mem_famField γ halg k hu⟩ := by
  classical
  let F := famField γ
  let vF : F := chValElem γ halg k
  let uF : F := ⟨u, conj_mem_famField γ halg k hu⟩
  haveI : Normal ℚ F := famField_normal γ
  have hIsConj : IsConjRoot ℚ uF vF := by
    dsimp [IsConjRoot, vF, uF, chValElem]
    calc
      minpoly ℚ (⟨u, conj_mem_famField γ halg k hu⟩ : F) = minpoly ℚ (u : ℂ) := by
        exact (minpoly.algebraMap_eq (A := ℚ) (h := by
          intro a b hab
          exact Subtype.ext hab) (⟨u, conj_mem_famField γ halg k hu⟩ : F)).symm
      _ = minpoly ℚ (chVal γ k) := minpoly_conj_eq γ halg k hu
      _ = minpoly ℚ (⟨chVal γ k, chVal_mem_famField γ halg k⟩ : F) := by
        exact minpoly.algebraMap_eq (A := ℚ) (h := by
          intro a b hab
          exact Subtype.ext hab) (⟨chVal γ k, chVal_mem_famField γ halg k⟩ : F)
  exact IsConjRoot.exists_algEquiv (K := ℚ) (x := uF) (y := vF) hIsConj

/-- a Galois automorphism permutes the indices of a conj-closed injective family -/
lemma exists_perm_of_gal {N : ℕ} (γ : Fin N → ℂ) (hinj : Function.Injective γ)
    (hclosed : conjClosedFamily γ) (halg : ∀ k : Fin N, IsAlgebraic ℚ (γ k))
    (σ : famField γ ≃ₐ[ℚ] famField γ) :
    ∃ π : Equiv.Perm (Fin N), ∀ i : Fin N, σ (famElem γ halg i) = famElem γ halg (π i) := by
  classical
  have hσroot : ∀ i : Fin N, (σ (famElem γ halg i) : ℂ) ∈ conjRoots (γ i) :=
    gal_map_conjRoots γ halg σ
  have hpre : ∀ i : Fin N, ∃ t : Fin N, γ t = (σ (famElem γ halg i) : ℂ) := by
    intro i
    exact hclosed i (σ (famElem γ halg i) : ℂ) (hσroot i)
  choose πfun hπ using hpre
  have hinjπ : Function.Injective πfun := by
    intro i j hij
    have hγi : γ (πfun i) = (σ (famElem γ halg i) : ℂ) := hπ i
    have hγj : γ (πfun j) = (σ (famElem γ halg j) : ℂ) := hπ j
    have hvals : (σ (famElem γ halg i) : ℂ) = (σ (famElem γ halg j) : ℂ) := by
      rw [← hγi, ← hγj, hij]
    have hσeq : σ (famElem γ halg i) = σ (famElem γ halg j) := Subtype.ext hvals
    have hFeq : famElem γ halg i = famElem γ halg j := σ.injective hσeq
    have hγeq : γ i = γ j := by
      exact congrArg Subtype.val hFeq
    exact hinj hγeq
  have hsurjπ : Function.Surjective πfun := (Finite.injective_iff_surjective (α := Fin N)).mp hinjπ
  refine ⟨Equiv.ofBijective πfun ⟨hinjπ, hsurjπ⟩, ?_⟩
  intro i
  apply Subtype.ext
  exact (hπ i).symm

/-- main conjugacy-closure step: a conjugate value of a choice value is the
relabeled value of the same choice under a suitable permutation -/
lemma chVal_conj_relabel {N : ℕ} (γ : Fin N → ℂ) (hinj : Function.Injective γ)
    (halg : ∀ k : Fin N, IsAlgebraic ℚ (γ k)) (hclosed : conjClosedFamily γ)
    (k : ChoiceFun N) {u : ℂ} (hu : u ∈ conjRoots (chVal γ k)) :
    ∃ π : Equiv.Perm (Fin N), ∀ k' : ChoiceFun N,
      chVal γ k' = chVal γ k → chVal γ (relabel π k') = u := by
  classical
  obtain ⟨σ, hσ⟩ := exists_gal_of_conj γ halg k hu
  obtain ⟨π, hπ⟩ := exists_perm_of_gal γ hinj hclosed halg σ
  refine ⟨π, ?_⟩
  intro k' hk'
  let E := famField γ
  let γE : Fin N → E := famElem γ halg
  have hrel := chValF_aut_relabel γ halg π σ hπ k'
  -- vals of both sides
  have hval_eq : (σ (chValF (F := E) γE k') : ℂ) = (chValF (F := E) γE (relabel π k') : ℂ) := by
    exact congrArg (fun x : E => (x : ℂ)) hrel
  have hceq : chValElem γ halg k' = chValElem γ halg k := by
    apply Subtype.ext
    dsimp [chValElem]
    exact hk'
  have hFk' : chValF (F := E) γE k' = chValElem γ halg k := by
    rw [← chValElem_eq_chValF γ halg k']
    exact hceq
  calc
    chVal γ (relabel π k') = (chValF (F := E) γE (relabel π k') : ℂ) := by
      -- val of chValF γE (relabel π k') = chVal (fun i => (γE i : ℂ)) (relabel π k') = chVal γ (relabel π k')
      rw [chValF_val E γE (relabel π k')]
      simp [γE]
    _ = (σ (chValF (F := E) γE k') : ℂ) := hval_eq.symm
    _ = (σ (chValElem γ halg k) : ℂ) := by
      rw [hFk']
    _ = (⟨u, conj_mem_famField γ halg k hu⟩ : E) := congrArg (fun x : E => (x : ℂ)) hσ
    _ = u := rfl

/-- conjRoots is symmetric for conjugate algebraic numbers -/
lemma conjRoots_symm {v u : ℂ} (hv : IsAlgebraic ℚ v) (h : u ∈ conjRoots v) : v ∈ conjRoots u := by
  classical
  have hvi : IsIntegral ℚ v := isAlgebraic_iff_isIntegral.mp hv
  have hconj : IsConjRoot ℚ v u :=
    isConjRoot_of_aeval_eq_zero (K := ℚ) hvi (aeval_mem_conjRoots (z := v) h)
  have hui : IsIntegral ℚ u := IsConjRoot.isIntegral hvi hconj
  rw [conjRoots, Polynomial.mem_aroots]
  constructor
  · exact minpoly.ne_zero hui
  · rw [← hconj]
    exact minpoly.aeval ℚ v

/-- a choice value is algebraic -/
lemma isAlgebraic_chVal {N : ℕ} (γ : Fin N → ℂ) (halg : ∀ k : Fin N, IsAlgebraic ℚ (γ k))
    (k : ChoiceFun N) : IsAlgebraic ℚ (chVal γ k) := by
  classical
  let F := famField γ
  haveI : Normal ℚ F := famField_normal γ
  have hvF : IsIntegral ℚ (chValElem γ halg k) :=
    Normal.isIntegral (famField_normal γ) (chValElem γ halg k)
  exact (isAlgebraic_iff_isIntegral).mpr (isIntegral_val (F := F) (chValElem γ halg k) hvF)

/-- a conjugate of a value is again a value of the family -/
lemma conj_mem_chValues {N : ℕ} (γ : Fin N → ℂ) (hinj : Function.Injective γ)
    (halg : ∀ k : Fin N, IsAlgebraic ℚ (γ k)) (hclosed : conjClosedFamily γ)
    (k0 : ChoiceFun N) {u : ℂ} (hu : u ∈ conjRoots (chVal γ k0)) :
    u ∈ chValues γ := by
  classical
  obtain ⟨π, hπ⟩ := chVal_conj_relabel γ hinj halg hclosed k0 hu
  dsimp [chValues]
  exact Finset.mem_image.mpr ⟨relabel π k0, Finset.mem_univ _, hπ k0 rfl⟩

/-- grouped coefficients are constant on conjugate classes of values -/
lemma chGrouped_conj {N : ℕ} (γ : Fin N → ℂ) (b : Fin N → ℤ) (hinj : Function.Injective γ)
    (halg : ∀ k : Fin N, IsAlgebraic ℚ (γ k)) (hclosed : conjClosedFamily γ)
    (k0 : ChoiceFun N) {u : ℂ} (hu : u ∈ conjRoots (chVal γ k0)) :
    chGrouped γ b u = chGrouped γ b (chVal γ k0) := by
  classical
  obtain ⟨π, hπ⟩ := chVal_conj_relabel γ hinj halg hclosed k0 hu
  unfold chGrouped
  -- the two filtered finsets over the common univ
  let U : Finset (ChoiceFun N) := Finset.univ
  let fv : Finset (ChoiceFun N) := U.filter (fun k => chVal γ k = chVal γ k0)
  let fu : Finset (ChoiceFun N) := U.filter (fun k => chVal γ k = u)
  have himg_sub : fv.image (relabel π) ⊆ fu := by
    intro x hx
    rcases (Finset.mem_image.mp hx) with ⟨k, hk, hxk⟩
    dsimp [fu, fv] at hk ⊢
    have hkf : chVal γ k = chVal γ k0 := (Finset.mem_filter.mp hk).2
    have hxval : chVal γ x = u := by
      rw [← hxk]
      exact hπ k hkf
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxval⟩
  have hv_in_u : chVal γ k0 ∈ conjRoots u :=
    conjRoots_symm (isAlgebraic_chVal γ halg k0) hu
  obtain ⟨ρ, hρ⟩ := chVal_conj_relabel γ hinj halg hclosed (relabel π k0) (by
      rw [hπ k0 rfl]
      exact hv_in_u)
  have hinj_ρ : Function.Injective (relabel ρ) := by
    intro x y hxy
    apply (relabelEquiv ρ).injective
    simpa using hxy
  have hinj_π : Function.Injective (relabel π) := by
    intro x y hxy
    apply (relabelEquiv π).injective
    simpa using hxy
  have himg_sup_card : fu.card ≤ fv.card := by
    have hsubρ : fu.image (relabel ρ) ⊆ fv := by
      intro x hx
      rcases (Finset.mem_image.mp hx) with ⟨k, hk, hxk⟩
      dsimp [fu, fv] at hk ⊢
      have hkf : chVal γ k = u := (Finset.mem_filter.mp hk).2
      have hxval : chVal γ x = chVal γ k0 := by
        rw [← hxk]
        exact hρ k (by
          rw [hkf]
          exact (hπ k0 rfl).symm)
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, hxval⟩
    calc
      fu.card = (fu.image (relabel ρ)).card := by
        exact (Finset.card_image_of_injective fu hinj_ρ).symm
      _ ≤ fv.card := Finset.card_le_card hsubρ
  have hle1 : fv.card ≤ fu.card := by
    calc
      fv.card = (fv.image (relabel π)).card := by
        exact (Finset.card_image_of_injective fv hinj_π).symm
      _ ≤ fu.card := Finset.card_le_card himg_sub
  have hcard_eq : fv.card = fu.card := le_antisymm hle1 himg_sup_card
  have himg_card : (fv.image (relabel π)).card = fu.card := by
    rw [hcard_eq.symm]
    exact Finset.card_image_of_injective fv hinj_π
  have himg_eq : fv.image (relabel π) = fu := by
    exact Finset.eq_of_subset_of_card_le himg_sub (by
      rw [himg_card])
  have hsum1 : (∑ x ∈ fv.image (relabel π), chCoeff b x) = (∑ k ∈ fv, chCoeff b k) := by
    rw [Finset.sum_image (f := fun x : ChoiceFun N => chCoeff b x) (s := fv) (g := relabel π)]
    · apply Finset.sum_congr rfl
      intro x hx
      exact chCoeff_relabel b π x
    · intro x hx y hy hxy
      exact hinj_π hxy
  have hmain : (∑ k ∈ fv, chCoeff b k) = (∑ x ∈ fu, chCoeff b x) := by
    calc
      (∑ k ∈ fv, chCoeff b k) = (∑ x ∈ fv.image (relabel π), chCoeff b x) := hsum1.symm
      _ = (∑ x ∈ fu, chCoeff b x) := by rw [himg_eq]
  -- tie to the goal
  simpa [fv, fu, U] using hmain.symm

/-! ### §17.4 — lexicographic order and the nonzero grouped coefficient -/

/-- lexicographic (real, then imaginary) strict order on ℂ -/
def LexLT (x y : ℂ) : Prop := x.re < y.re ∨ (x.re = y.re ∧ x.im < y.im)

/-- lexicographic (real, then imaginary) non-strict order on ℂ -/
def LexLE (x y : ℂ) : Prop := x.re < y.re ∨ (x.re = y.re ∧ x.im ≤ y.im)

lemma lexLE_refl (x : ℂ) : LexLE x x := Or.inr ⟨rfl, le_rfl⟩

lemma LexLE.trans {x y z : ℂ} (hxy : LexLE x y) (hyz : LexLE y z) : LexLE x z := by
  rcases hxy with hx | ⟨hre, hx⟩
  · rcases hyz with hy | ⟨hre', hy⟩
    · exact Or.inl (lt_trans hx hy)
    · rw [hre'] at hx
      exact Or.inl hx
  · rcases hyz with hy | ⟨hre', hy⟩
    · rw [← hre] at hy
      exact Or.inl hy
    · exact Or.inr ⟨hre.trans hre', hx.trans hy⟩

lemma lexLE_total (x y : ℂ) : LexLE x y ∨ LexLE y x := by
  by_cases hxy : x.re < y.re
  · left
    exact Or.inl hxy
  · by_cases hyx : y.re < x.re
    · right
      exact Or.inl hyx
    · have hre : x.re = y.re := le_antisymm (le_of_not_gt hyx) (le_of_not_gt hxy)
      by_cases hx : x.im ≤ y.im
      · left
        right
        exact ⟨hre, hx⟩
      · right
        right
        constructor
        · exact hre.symm
        · exact le_of_lt (lt_of_not_ge hx)

lemma LexLT_of_LexLE_ne {x y : ℂ} (hle : LexLE x y) (hne : x ≠ y) : LexLT x y := by
  rcases hle with h | h
  · exact Or.inl h
  · right
    constructor
    · exact h.1
    · refine lt_of_le_of_ne h.2 ?_
      intro him
      exact hne (Complex.ext h.1 him)

lemma LexLT_ne {x y : ℂ} (h : LexLT x y) : x ≠ y := by
  intro heq
  rcases h with h | h
  · exact (ne_of_lt h) (congrArg Complex.re heq)
  · exact (ne_of_lt h.2) (congrArg Complex.im heq)

/-- additive strictness: pointwise non-strict with one strict gives strict -/
lemma LexLT_sum_of_pointwise {ι : Type*} [Fintype ι] (a b : ι → ℂ)
    (hle : ∀ i, LexLE (a i) (b i)) (hlt : ∃ i, LexLT (a i) (b i)) :
    LexLT (∑ i, a i) (∑ i, b i) := by
  classical
  let s : Finset ι := Finset.univ
  have hre_le : ∀ i, (a i).re ≤ (b i).re := by
    intro i
    rcases hle i with h | h
    · exact le_of_lt h
    · exact le_of_eq h.1
  have him_le_of_re_eq : ∀ i, (a i).re = (b i).re → (a i).im ≤ (b i).im := by
    intro i hre
    rcases hle i with h | h
    · exact False.elim ((ne_of_lt h) hre)
    · simpa [hre] using h.2
  have hsum_re_le : (∑ i, a i).re ≤ (∑ i, b i).re := by
    rw [Complex.re_sum, Complex.re_sum]
    exact Finset.sum_le_sum (s := s) (f := fun i => (a i).re) (g := fun i => (b i).re) (by
      intro i hi
      exact hre_le i)
  by_cases hstr : (∑ i, a i).re < (∑ i, b i).re
  · exact Or.inl hstr
  · right
    have hre_eq : (∑ i, a i).re = (∑ i, b i).re := le_antisymm hsum_re_le (le_of_not_gt hstr)
    have hsum_re : (∑ i ∈ s, (a i).re) = (∑ i ∈ s, (b i).re) := by
      simpa [Complex.re_sum, s] using hre_eq
    have hsum0 : (∑ i ∈ s, ((b i).re - (a i).re)) = 0 := by
      rw [Finset.sum_sub_distrib]
      rw [hsum_re]
      ring
    have hall0 : ∀ i, (b i).re - (a i).re = 0 := by
      intro i
      have hnonneg : ∀ j ∈ s, 0 ≤ (b j).re - (a j).re := by
        intro j hj
        exact sub_nonneg.mpr (hre_le j)
      have hiff := Finset.sum_eq_zero_iff_of_nonneg (s := s)
        (f := fun i => (b i).re - (a i).re) hnonneg
      exact (hiff.mp hsum0) i (Finset.mem_univ i)
    have hall_re : ∀ i, (a i).re = (b i).re := by
      intro i
      exact (sub_eq_zero.mp (hall0 i)).symm
    have hle_im : ∀ i, (a i).im ≤ (b i).im := by
      intro i
      exact him_le_of_re_eq i (hall_re i)
    have him_strict : ∃ i, (a i).im < (b i).im := by
      rcases hlt with ⟨i, hi⟩
      rcases hi with h | h
      · exact False.elim ((ne_of_lt h) (hall_re i))
      · refine ⟨i, h.2⟩
    have hsum_im_lt : (∑ i, a i).im < (∑ i, b i).im := by
      rw [Complex.im_sum, Complex.im_sum]
      exact Finset.sum_lt_sum (s := s) (f := fun i => (a i).im) (g := fun i => (b i).im)
        (by intro i hi; exact hle_im i)
        (by rcases him_strict with ⟨i, hi⟩; exact ⟨i, Finset.mem_univ i, hi⟩)
    constructor
    · exact hre_eq
    · exact hsum_im_lt


/-- maximum of finitely many complex numbers in the lex order exists -/
lemma exists_max_lex {N : ℕ} (f : Fin N → ℂ) (J : Finset (Fin N)) (hJ : J.Nonempty) :
    ∃ j0 ∈ J, ∀ j ∈ J, LexLE (f j) (f j0) := by
  classical
  induction J using Finset.induction_on with
  | empty =>
      rcases hJ with ⟨x, hx⟩
      simp at hx
  | insert j J' hjn ih =>
      by_cases hJ' : J'.Nonempty
      · rcases ih hJ' with ⟨j0, hj0J', hmax⟩
        rcases lexLE_total (f j) (f j0) with h | h
        · refine ⟨j0, Finset.mem_insert.mpr (Or.inr hj0J'), ?_⟩
          intro t ht
          rcases (Finset.mem_insert.mp ht) with htj | ht'
          · rw [htj]
            exact h
          · exact hmax t ht'
        · refine ⟨j, Finset.mem_insert_self j J', ?_⟩
          intro t ht
          rcases (Finset.mem_insert.mp ht) with htj | ht'
          · rw [htj]
            exact lexLE_refl (f j)
          · exact LexLE.trans (hmax t ht') h
      · refine ⟨j, Finset.mem_insert_self j J', ?_⟩
        intro t ht
        rcases (Finset.mem_insert.mp ht) with htj | ht'
        · rw [htj]
          exact lexLE_refl (f j)
        · exact (hJ' ⟨t, ht'⟩).elim

/-- existence of the lex-max index among the nonzero-coefficient indices -/
lemma exists_lex_max_index {N : ℕ} (γ : Fin N → ℂ) (σ : Equiv.Perm (Fin N))
    (b : Fin N → ℤ) (hbnz : ∃ j, b j ≠ 0) :
    ∃ j0, b j0 ≠ 0 ∧ ∀ j, b j ≠ 0 → LexLE (γ (σ j)) (γ (σ j0)) := by
  classical
  let J : Finset (Fin N) := (Finset.univ : Finset (Fin N)).filter (fun j => b j ≠ 0)
  have hJ : J.Nonempty := by
    rcases hbnz with ⟨j, hj⟩
    refine ⟨j, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩
  obtain ⟨j0, hj0J, hmax⟩ := exists_max_lex (f := fun j => γ (σ j)) J hJ
  refine ⟨j0, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hj0J).2
  · intro j hj
    exact hmax j (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩)

/-- the lex-max choice function (one index per factor, from nonzero coefficients) -/
def lexMaxChoice {N : ℕ} (γ : Fin N → ℂ) (b : Fin N → ℤ)
    (hbnz : ∃ j, b j ≠ 0) : ChoiceFun N :=
  fun σ => Classical.choose (exists_lex_max_index γ σ b hbnz)

/-- the lex-max choice has nonzero coefficient in every factor -/
lemma lexMaxChoice_mem {N : ℕ} (γ : Fin N → ℂ) (b : Fin N → ℤ)
    (hbnz : ∃ j, b j ≠ 0) (σ : Equiv.Perm (Fin N)) : b (lexMaxChoice γ b hbnz σ) ≠ 0 := by
  dsimp [lexMaxChoice]
  exact (Classical.choose_spec (exists_lex_max_index γ σ b hbnz)).1

/-- the lex-max choice dominates every supported choice -/
lemma lexMaxChoice_max {N : ℕ} (γ : Fin N → ℂ) (b : Fin N → ℤ)
    (hbnz : ∃ j, b j ≠ 0) (σ : Equiv.Perm (Fin N)) :
    ∀ j, b j ≠ 0 → LexLE (γ (σ j)) (γ (σ (lexMaxChoice γ b hbnz σ))) := by
  intro j hj
  dsimp [lexMaxChoice]
  exact (Classical.choose_spec (exists_lex_max_index γ σ b hbnz)).2 j hj

/-- the lex-max choice has nonzero product coefficient -/
lemma chCoeff_lexMax_ne_zero {N : ℕ} (γ : Fin N → ℂ) (b : Fin N → ℤ)
    (hbnz : ∃ j, b j ≠ 0) : chCoeff b (lexMaxChoice γ b hbnz) ≠ 0 := by
  classical
  dsimp [chCoeff]
  apply Finset.prod_ne_zero_iff.mpr
  intro σ hσ
  exact lexMaxChoice_mem γ b hbnz σ

/-- any other supported choice has a strictly smaller value -/
lemma chVal_lexMax_strict {N : ℕ} (γ : Fin N → ℂ) (b : Fin N → ℤ)
    (hinj : Function.Injective γ) (hbnz : ∃ j, b j ≠ 0) (k : ChoiceFun N)
    (hsupp : ∀ σ, b (k σ) ≠ 0) (hk : k ≠ lexMaxChoice γ b hbnz) :
    LexLT (chVal γ k) (chVal γ (lexMaxChoice γ b hbnz)) := by
  classical
  have hne : ∃ σ, k σ ≠ lexMaxChoice γ b hbnz σ := by
    by_contra h
    apply hk
    funext σ
    by_contra hσ
    exact h ⟨σ, hσ⟩
  rcases hne with ⟨σ0, hσ0⟩
  -- the per-factor dominance with a strict factor
  have hle : ∀ σ : Equiv.Perm (Fin N), LexLE (γ (σ (k σ))) (γ (σ (lexMaxChoice γ b hbnz σ))) := by
    intro σ
    exact lexMaxChoice_max γ b hbnz σ (k σ) (hsupp σ)
  have hstrict : ∃ σ : Equiv.Perm (Fin N), LexLT (γ (σ (k σ))) (γ (σ (lexMaxChoice γ b hbnz σ))) := by
    refine ⟨σ0, ?_⟩
    apply LexLT_of_LexLE_ne (hle σ0)
    intro heq
    exact hσ0 (σ0.injective (hinj heq))
  -- sums
  have h1 := LexLT_sum_of_pointwise (ι := Equiv.Perm (Fin N))
    (a := fun σ : Equiv.Perm (Fin N) => γ (σ (k σ)))
    (b := fun σ : Equiv.Perm (Fin N) => γ (σ (lexMaxChoice γ b hbnz σ))) hle hstrict
  dsimp [chVal]
  exact h1

/-- for the lex-max value, the grouped coefficient is just the max choice's
coefficient (all other realizing choices are unsupported) -/
lemma chGrouped_eq_chCoeff_of_max {N : ℕ} (γ : Fin N → ℂ) (b : Fin N → ℤ)
    (hinj : Function.Injective γ) (hbnz : ∃ k, b k ≠ 0) :
    chGrouped γ b (chVal γ (lexMaxChoice γ b hbnz)) = chCoeff b (lexMaxChoice γ b hbnz) := by
  classical
  unfold chGrouped
  apply Finset.sum_eq_single (lexMaxChoice γ b hbnz)
  · intro k hk hkne
    have hmemval : chVal γ k = chVal γ (lexMaxChoice γ b hbnz) := (Finset.mem_filter.mp hk).2
    have hunsupported : ¬ (∀ σ : Equiv.Perm (Fin N), b (k σ) ≠ 0) := by
      intro hsupp
      exact (LexLT_ne (chVal_lexMax_strict γ b hinj hbnz k hsupp hkne)) hmemval
    rcases (not_forall.mp hunsupported) with ⟨σ, hσ⟩
    dsimp [chCoeff]
    refine Finset.prod_eq_zero (Finset.mem_univ σ) ?_
    by_contra hb
    exact hσ hb
  · intro hk'
    exact False.elim (hk' (Finset.mem_filter.mpr
      ⟨Finset.mem_univ (lexMaxChoice γ b hbnz), rfl⟩))

/-- there is a value with nonzero grouped coefficient (Lemma B's nonzero step) -/
lemma exists_nonzero_chGrouped {N : ℕ} (γ : Fin N → ℂ) (b : Fin N → ℤ)
    (hinj : Function.Injective γ) (hbnz : ∃ k, b k ≠ 0) :
    ∃ v ∈ chValues γ, chGrouped γ b v ≠ 0 := by
  classical
  refine ⟨chVal γ (lexMaxChoice γ b hbnz), ?_, ?_⟩
  · dsimp [chValues]
    exact Finset.mem_image.mpr ⟨lexMaxChoice γ b hbnz, Finset.mem_univ _, rfl⟩
  · rw [chGrouped_eq_chCoeff_of_max γ b hinj hbnz]
    exact chCoeff_lexMax_ne_zero γ b hbnz


/-- support values are algebraic -/
lemma chSupport_algebraic {N : ℕ} (γ : Fin N → ℂ) (halg : ∀ k : Fin N, IsAlgebraic ℚ (γ k))
    (b : Fin N → ℤ) {v : ℂ} (hv : v ∈ chSupport γ b) : IsAlgebraic ℚ v := by
  classical
  have hvch : v ∈ chValues γ := (Finset.mem_filter.mp hv).1
  rcases (Finset.mem_image.mp hvch) with ⟨k, hk, hkv⟩
  rw [← hkv]
  exact isAlgebraic_chVal γ halg k

/-- lemma B for conj-closed injective algebraic families (S_N engine) -/
lemma lemmaB_conjClosed {N : ℕ} (γ : Fin N → ℂ) (b : Fin N → ℤ)
    (hinj : Function.Injective γ) (halg : ∀ k : Fin N, IsAlgebraic ℚ (γ k))
    (hclosed : conjClosedFamily γ) (hbnz : ∃ k : Fin N, b k ≠ 0)
    (hrel : (∑ k : Fin N, (b k : ℂ) * cexp (γ k)) = 0) : False := by
  classical
  let S : Finset ℂ := chSupport γ b
  let D : ℂ → ℤ := chGrouped γ b
  have hSnz : ∀ v ∈ S, D v ≠ 0 := by
    intro v hv
    exact (Finset.mem_filter.mp hv).2
  have hSalg : ∀ v ∈ S, IsAlgebraic ℚ v := by
    intro v hv
    exact chSupport_algebraic γ halg b hv
  have hconj : ∀ v ∈ S, ∀ w : ℂ, w ∈ conjRoots v → w ∈ S := by
    intro v hv w hw
    have hvch : v ∈ chValues γ := (Finset.mem_filter.mp hv).1
    rcases (Finset.mem_image.mp hvch) with ⟨k0, hk0, hkv⟩
    have hwch : w ∈ chValues γ :=
      conj_mem_chValues γ hinj halg hclosed k0 (by simpa [hkv] using hw)
    have hDw : D w = D (chVal γ k0) := by
      dsimp [D]
      exact chGrouped_conj γ b hinj halg hclosed k0 (by simpa [hkv] using hw)
    exact Finset.mem_filter.mpr ⟨hwch, by
      simpa [D, hDw, hkv] using (hSnz v hv)⟩
  have hcls : ∀ v ∈ S, ∀ w ∈ S, w ∈ conjRoots v → D w = D v := by
    intro v hv w hw hwv
    have hvch : v ∈ chValues γ := (Finset.mem_filter.mp hv).1
    rcases (Finset.mem_image.mp hvch) with ⟨k0, hk0, hkv⟩
    dsimp [D]
    rw [← hkv]
    exact chGrouped_conj γ b hinj halg hclosed k0 (by simpa [hkv] using hwv)
  have hSne : S.Nonempty := by
    rcases exists_nonzero_chGrouped γ b hinj hbnz with ⟨v, hvch, hD⟩
    refine ⟨v, ?_⟩
    exact Finset.mem_filter.mpr ⟨hvch, hD⟩
  exact lemmaA_grouped S D hSne hSnz hSalg hconj hcls (ch_support_relation_zero γ b hrel)


/-! ### §17.6 — the conj-closed extension of a finite algebraic family -/

/-- the finite set of all conjugates of the family values -/
def conjSet {n : ℕ} (γ : Fin n → ℂ) : Finset ℂ :=
  (Finset.univ : Finset (Fin n)).biUnion (fun k => (conjRoots (γ k)).toFinset)

/-- membership in the conjugate set -/
lemma mem_conjSet {n : ℕ} (γ : Fin n → ℂ) (x : ℂ) :
    x ∈ conjSet γ ↔ ∃ k : Fin n, x ∈ conjRoots (γ k) := by
  classical
  dsimp [conjSet]
  simp [Finset.mem_biUnion]

/-- the original values lie in the conjugate set -/
lemma mem_conjSet_self {n : ℕ} (γ : Fin n → ℂ) (halg : ∀ k : Fin n, IsAlgebraic ℚ (γ k))
    (k : Fin n) : γ k ∈ conjSet γ := by
  rw [mem_conjSet]
  exact ⟨k, mem_conjRoots_self (halg k)⟩

/-- conjugate sets of conjugate values coincide -/
lemma conjRoots_eq_of_conj {z u : ℂ} (hz : IsAlgebraic ℚ z) (hu : u ∈ conjRoots z) :
    conjRoots u = conjRoots z := by
  classical
  have hzi : IsIntegral ℚ z := isAlgebraic_iff_isIntegral.mp hz
  have hc : IsConjRoot ℚ z u :=
    isConjRoot_of_aeval_eq_zero (K := ℚ) hzi (aeval_mem_conjRoots (z := z) hu)
  have hui : IsIntegral ℚ u := IsConjRoot.isIntegral hzi hc
  dsimp [conjRoots]
  rw [hc]

/-- the conjugate set is closed under conjugation -/
lemma conjSet_closed {n : ℕ} (γ : Fin n → ℂ) (halg : ∀ k : Fin n, IsAlgebraic ℚ (γ k))
    {x : ℂ} (hx : x ∈ conjSet γ) {w : ℂ} (hw : w ∈ conjRoots x) : w ∈ conjSet γ := by
  classical
  rcases (mem_conjSet γ x).mp hx with ⟨k, hxk⟩
  rw [mem_conjSet]
  refine ⟨k, ?_⟩
  have h := conjRoots_eq_of_conj (halg k) hxk
  rw [← h]
  exact hw

/-- the finite enumeration of the conjugate set -/
def conjEnum {n : ℕ} (γ : Fin n → ℂ) :
    Fin (conjSet γ).card → ℂ :=
  fun i => ((Finset.equivFin (conjSet γ)).symm i : ℂ)

/-- the enumeration is injective -/
lemma conjEnum_injective {n : ℕ} (γ : Fin n → ℂ) :
    Function.Injective (conjEnum γ) := by
  intro i j hij
  apply (Finset.equivFin (conjSet γ)).symm.injective
  apply Subtype.ext
  exact hij

/-- the enumeration is conj-closed -/
lemma conjEnum_closed {n : ℕ} (γ : Fin n → ℂ) (halg : ∀ k : Fin n, IsAlgebraic ℚ (γ k))
    : conjClosedFamily (conjEnum γ) := by
  intro i w hw
  have hx : conjEnum γ i ∈ conjSet γ := by
    exact ((Finset.equivFin (conjSet γ)).symm i).2
  have hwmem : w ∈ conjSet γ := conjSet_closed γ halg hx hw
  refine ⟨(Finset.equivFin (conjSet γ)) ⟨w, hwmem⟩, ?_⟩
  dsimp [conjEnum]
  simp

/-- the enumeration is surjective onto the conjugate set -/
lemma conjEnum_surj {n : ℕ} (γ : Fin n → ℂ) {x : ℂ} (hx : x ∈ conjSet γ) :
    ∃ i : Fin (conjSet γ).card, conjEnum γ i = x := by
  refine ⟨(Finset.equivFin (conjSet γ)) ⟨x, hx⟩, ?_⟩
  dsimp [conjEnum]
  simp

/-- index of an original value in the enumeration -/
def conjIdx {n : ℕ} (γ : Fin n → ℂ) (halg : ∀ k : Fin n, IsAlgebraic ℚ (γ k))
    (k : Fin n) : Fin (conjSet γ).card :=
  (Finset.equivFin (conjSet γ)) ⟨γ k, mem_conjSet_self γ halg k⟩

/-- the index reproduces the original value -/
lemma conjIdx_val {n : ℕ} (γ : Fin n → ℂ) (halg : ∀ k : Fin n, IsAlgebraic ℚ (γ k))
    (k : Fin n) : conjEnum γ (conjIdx γ halg k) = γ k := by
  dsimp [conjIdx, conjEnum]
  simp


/-- zero extension of the coefficients to the conjugate set -/
def conjExtendCoeff {n N : ℕ} (γ : Fin n → ℂ) (b : Fin n → ℤ)
    (γN : Fin N → ℂ) : Fin N → ℤ :=
  fun j => if h : ∃ k : Fin n, γN j = γ k then b (Classical.choose h) else 0

/-- the extension reproduces the coefficient at an original index -/
lemma conjExtendCoeff_at {n N : ℕ} (γ : Fin n → ℂ) (hinj : Function.Injective γ)
    (b : Fin n → ℤ) (γN : Fin N → ℂ) {j : Fin N} {k : Fin n} (hjk : γN j = γ k) :
    conjExtendCoeff γ b γN j = b k := by
  classical
  have hw : ∃ k0 : Fin n, γN j = γ k0 := ⟨k, hjk⟩
  have hch : γN j = γ (Classical.choose hw) := Classical.choose_spec hw
  have hk' : k = Classical.choose hw := hinj (hjk.symm.trans hch)
  dsimp [conjExtendCoeff]
  rw [dif_pos hw]
  exact (congrArg b hk').symm

/-- the extension is zero outside the original range -/
lemma conjExtendCoeff_zero {n N : ℕ} (γ : Fin n → ℂ) (b : Fin n → ℤ)
    (γN : Fin N → ℂ) {j : Fin N} (hj : ∀ k : Fin n, γN j ≠ γ k) :
    conjExtendCoeff γ b γN j = 0 := by
  classical
  dsimp [conjExtendCoeff]
  rw [dif_neg]
  · exact not_exists.mpr hj

/-- the extended family preserves the exponential relation -/
lemma conjEnum_relation {n : ℕ} (γ : Fin n → ℂ) (b : Fin n → ℤ)
    (halg : ∀ k : Fin n, IsAlgebraic ℚ (γ k)) (hinj : Function.Injective γ)
    (hrel : (∑ k : Fin n, (b k : ℂ) * cexp (γ k)) = 0) :
    (∑ j : Fin (conjSet γ).card,
        (conjExtendCoeff γ b (conjEnum γ) j : ℂ) * cexp (conjEnum γ j)) = 0 := by
  classical
  let γN : Fin (conjSet γ).card → ℂ := conjEnum γ
  let bN : Fin (conjSet γ).card → ℤ := conjExtendCoeff γ b γN
  let idx : Fin n → Fin (conjSet γ).card := conjIdx γ halg
  have hinjN : Function.Injective γN := conjEnum_injective γ
  have hidx_val : ∀ k : Fin n, γN (idx k) = γ k := by
    intro k
    exact conjIdx_val γ halg k
  have hidx_coeff : ∀ k : Fin n, bN (idx k) = b k := by
    intro k
    exact conjExtendCoeff_at γ hinj b γN (hidx_val k)
  have hbN_zero : ∀ j : Fin (conjSet γ).card,
      (∀ k : Fin n, γN j ≠ γ k) → bN j = 0 := by
    intro j hj
    exact conjExtendCoeff_zero γ b γN hj
  have hinj_idx : Function.Injective idx := by
    intro k t hkt
    apply hinj
    rw [← hidx_val k, ← hidx_val t]
    rw [hkt]
  let s : Finset (Fin (conjSet γ).card) := (Finset.univ : Finset (Fin n)).image idx
  have hsub : s ⊆ (Finset.univ : Finset (Fin (conjSet γ).card)) := by
    intro x hx
    exact Finset.mem_univ x
  have hout : ∀ x ∈ (Finset.univ : Finset (Fin (conjSet γ).card)), x ∉ s →
      (bN x : ℂ) * cexp (γN x) = 0 := by
    intro x hx hxs
    have hz : bN x = 0 := by
      apply hbN_zero x
      intro k hk
      exact hxs (Finset.mem_image.mpr ⟨k, Finset.mem_univ k, by
        apply hinjN
        exact (hidx_val k).trans hk.symm⟩)
    simp [hz]
  have h2 : (∑ x ∈ s, (bN x : ℂ) * cexp (γN x))
      = ∑ k : Fin n, (bN (idx k) : ℂ) * cexp (γN (idx k)) := by
    let f : Fin (conjSet γ).card → ℂ := fun x => (bN x : ℂ) * cexp (γN x)
    have hsi := Finset.sum_image (f := f) (s := (Finset.univ : Finset (Fin n))) (g := idx) (by
      intro x hx y hy hxy
      exact hinj_idx hxy)
    calc
      (∑ x ∈ s, f x) = (∑ x ∈ (Finset.univ : Finset (Fin n)), f (idx x)) := by
        simpa [s] using hsi
      _ = ∑ k : Fin n, f (idx k) := rfl
  calc
    (∑ j : Fin (conjSet γ).card, (bN j : ℂ) * cexp (γN j))
        = (∑ x ∈ s, (bN x : ℂ) * cexp (γN x)) := by
          exact (Finset.sum_subset hsub hout).symm
    _ = ∑ k : Fin n, (bN (idx k) : ℂ) * cexp (γN (idx k)) := h2
    _ = ∑ k : Fin n, (b k : ℂ) * cexp (γ k) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [hidx_coeff k, hidx_val k]
    _ = 0 := hrel


/-- Lemma B (integer coefficients, distinct algebraic exponents) -/
lemma lemmaB {n : ℕ} (γ : Fin n → ℂ) (b : Fin n → ℤ) (hinj : Function.Injective γ)
    (halg : ∀ k : Fin n, IsAlgebraic ℚ (γ k)) (hbnz : ∃ k : Fin n, b k ≠ 0)
    (hrel : (∑ k : Fin n, (b k : ℂ) * cexp (γ k)) = 0) : False := by
  classical
  let N := (conjSet γ).card
  let γN : Fin N → ℂ := conjEnum γ
  let bN : Fin N → ℤ := conjExtendCoeff γ b γN
  have hinjN : Function.Injective γN := conjEnum_injective γ
  have hbNnz : ∃ j : Fin N, bN j ≠ 0 := by
    rcases hbnz with ⟨k0, hk0⟩
    refine ⟨conjIdx γ halg k0, ?_⟩
    have hc := conjExtendCoeff_at γ hinj b γN (hjk := (conjIdx_val γ halg k0))
    exact (by simpa [bN, γN] using (hc ▸ hk0))
  have hrelN : (∑ j : Fin N, (bN j : ℂ) * cexp (γN j)) = 0 := by
    simpa [N, γN, bN] using conjEnum_relation γ b halg hinj hrel
  have halgN : ∀ j : Fin N, IsAlgebraic ℚ (γN j) := by
    intro j
    have hxmem : γN j ∈ conjSet γ := by
      dsimp [γN, conjEnum]
      exact ((Finset.equivFin (conjSet γ)).symm j).2
    rcases (mem_conjSet γ (γN j)).mp hxmem with ⟨k, hjk⟩
    have hzi : IsIntegral ℚ (γ k) := isAlgebraic_iff_isIntegral.mp (halg k)
    have huI : IsIntegral ℚ (γN j) := by
      refine ⟨minpoly ℚ (γ k), minpoly.monic hzi, ?_⟩
      exact aeval_mem_conjRoots (z := γ k) hjk
    exact (isAlgebraic_iff_isIntegral).mpr huI
  exact lemmaB_conjClosed γN bN hinjN halgN (conjEnum_closed γ halg) hbNnz hrelN


/-! ### §17.7 — Lindemann's theorem (e^z transcendental for algebraic z ≠ 0) -/

/-- a ℤ-polynomial vanishing at x gives an integer coefficient relation in powers -/
lemma aeval_IntPoly_as_sum {x : ℂ} (p : ℤ[X]) :
    (aeval x p) = ∑ i ∈ Finset.range (p.natDegree + 1), ((p.coeff i : ℤ) : ℂ) * x ^ i := by
  classical
  calc
    (aeval x p) = aeval x (∑ i ∈ Finset.range (p.natDegree + 1), C (p.coeff i) * X ^ i) := by
      conv_lhs => rw [Polynomial.as_sum_range_C_mul_X_pow p]
    _ = ∑ i ∈ Finset.range (p.natDegree + 1), ((p.coeff i : ℤ) : ℂ) * x ^ i := by
      rw [map_sum (aeval x)]
      apply Finset.sum_congr rfl
      intro i hi
      simp

/-- Lindemann: `e^z` is transcendental over ℚ for algebraic nonzero `z` -/
theorem cexp_transcendental_of_algebraic_ne_zero {z : ℂ} (hz : IsAlgebraic ℚ z) (hz0 : z ≠ 0) :
    Transcendental ℚ (cexp z) := by
  classical
  by_contra htr
  have hβalg : IsAlgebraic ℚ (cexp z) := (not_not.mp htr)
  have hβalgZ : IsAlgebraic ℤ (cexp z) := by
    exact (IsFractionRing.isAlgebraic_iff (A := ℤ) (K := ℚ) (C := ℂ)).mpr hβalg
  rcases hβalgZ with ⟨p, hp0, hpaeval⟩
  let d : ℕ := p.natDegree
  let γ : Fin (d + 1) → ℂ := fun i => (i : ℕ) • z
  let b : Fin (d + 1) → ℤ := fun i => p.coeff (i : ℕ)
  -- exponents are distinct
  have hinjγ : Function.Injective γ := by
    intro i j hij
    apply Fin.ext
    dsimp [γ] at hij
    -- (i : ℕ) • z = (j : ℕ) • z: nsmul
    have hn : (i : ℕ) = (j : ℕ) := by
      -- ((i:ℕ):ℂ) • z = ...: nsmul equal: use nsmul_injective_of_ne_zero? in Lindemann.lean? there was nsmul_injective_of_ne_zero (z) (hz)
      exact nsmul_injective_of_ne_zero hz0 hij
    omega
  -- coefficients are algebraic integers-free but integer: some nonzero
  have hb0 : p.coeff d ≠ 0 := by
    dsimp [d]
    -- coeff at natDegree = leadingCoeff ≠ 0 since p ≠ 0
    exact (Polynomial.leadingCoeff_ne_zero).mpr hp0  -- hmm direction: leadingCoeff_ne_zero : p.leadingCoeff ≠ 0 ↔ p ≠ 0: so .mpr hp0 : leadingCoeff ≠ 0 = coeff d ≠ 0 via coeff_natDegree
  have hbnz : ∃ k : Fin (d + 1), b k ≠ 0 := by
    refine ⟨⟨d, Nat.lt_succ_self d⟩, ?_⟩
    exact hb0
  -- algebraicity of the exponents
  have halgγ : ∀ i : Fin (d + 1), IsAlgebraic ℚ (γ i) := by
    intro i
    dsimp [γ]
    exact IsAlgebraic.nsmul hz (i : ℕ)
  -- the relation
  have hrel : (∑ i : Fin (d + 1), (b i : ℂ) * cexp (γ i)) = 0 := by
    -- 0 = aeval β p = ∑_{i<d+1} (p.coeff i) β^i = ∑ (b i) cexp((i:ℕ)•z)
    have hzsum : (∑ i ∈ Finset.range (d + 1), ((p.coeff i : ℤ) : ℂ) * (cexp z) ^ i) = 0 := by
      -- from aeval_IntPoly_as_sum: aeval β p = that; and hpaeval : aeval β p = 0
      have hcalc := aeval_IntPoly_as_sum (x := cexp z) p
      rw [← hcalc]
      exact hpaeval
    -- convert: sum over Fin (d+1) of (b i : ℂ) * cexp (γ i) equals the range sum
    calc
      (∑ i : Fin (d + 1), (b i : ℂ) * cexp (γ i))
          = ∑ i ∈ Finset.range (d + 1), ((p.coeff i : ℤ) : ℂ) * (cexp z) ^ i := by
            -- each term: cexp ((i:ℕ) • z) = (cexp z)^(i:ℕ) via exp_nsmul; range sum = Fin sum via Fin.sum_univ_eq_sum_range
            calc
              (∑ i : Fin (d + 1), (b i : ℂ) * cexp (γ i))
                  = ∑ i : Fin (d + 1), ((p.coeff (i : ℕ) : ℤ) : ℂ) * (cexp z) ^ (i : ℕ) := by
                    apply Finset.sum_congr rfl
                    intro i hi
                    dsimp [b, γ]
                    congr 1
                    exact Complex.exp_nsmul z (i : ℕ)
              _ = ∑ i ∈ Finset.range (d + 1), ((p.coeff i : ℤ) : ℂ) * (cexp z) ^ i := by
                    exact Fin.sum_univ_eq_sum_range (fun n : ℕ => ((p.coeff n : ℤ) : ℂ) * (cexp z) ^ n) (d + 1)
      _ = 0 := hzsum
  exact lemmaB γ b hinjγ halgγ hbnz hrel

/-! ## §17.8 — corollaries of Lindemann's theorem -/

/-- I is algebraic over ℚ -/
lemma isAlgebraic_I : IsAlgebraic ℚ (Complex.I : ℂ) := by
  classical
  refine ⟨(X : ℚ[X]) ^ 2 + 1, ?_, ?_⟩
  · intro hp
    have h2 := congrArg (fun q : ℚ[X] => q.coeff 2) hp
    simp [Polynomial.coeff_one] at h2
  · simp

/-- π is transcendental over ℚ -/
theorem transcendental_pi_complex : Transcendental ℚ ((Real.pi : ℝ) : ℂ) := by
  classical
  by_contra htr
  have hpi : IsAlgebraic ℚ ((Real.pi : ℝ) : ℂ) := (not_not.mp htr)
  have hz : IsAlgebraic ℚ (Complex.I * ((Real.pi : ℝ) : ℂ)) := IsAlgebraic.mul isAlgebraic_I hpi
  have hz0 : Complex.I * ((Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact mul_ne_zero (by simp) (by exact_mod_cast Real.pi_ne_zero)
  have htrz := cexp_transcendental_of_algebraic_ne_zero hz hz0
  -- cexp (I * π) = -1
  have hcexp : cexp (Complex.I * ((Real.pi : ℝ) : ℂ)) = -1 := by
    rw [mul_comm]
    exact Complex.exp_pi_mul_I
  have hc : IsAlgebraic ℚ (cexp (Complex.I * ((Real.pi : ℝ) : ℂ))) := by
    rw [hcexp]
    simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (-1 : ℚ))
  exact htrz hc

/-- algebraic number cast lemma: an ℚ-algebraic element of a ℚ-algebra cast into ℂ -/
lemma isAlgebraic_rat_complex (q : ℚ) : IsAlgebraic ℚ ((q : ℂ)) := by
  exact isAlgebraic_algebraMap (R := ℚ) (A := ℂ) q

/-- real logarithm of a positive rational ≠ 1 is transcendental (over ℂ cast) -/
theorem transcendental_log_rat {q : ℚ} (hqpos : 0 < q) (hq1 : q ≠ 1) :
    Transcendental ℚ ((Real.log (q : ℝ)) : ℂ) := by
  classical
  by_contra htr
  have htalg : IsAlgebraic ℚ ((Real.log (q : ℝ)) : ℂ) := (not_not.mp htr)
  have hz0 : (Real.log (q : ℝ) : ℂ) ≠ 0 := by
    have hlog0 : Real.log (q : ℝ) ≠ 0 := by
      intro h
      have hz := (Real.log_eq_zero.mp h)
      rcases hz with hq0 | hq1' | hqneg1
      · exact (ne_of_gt hqpos) (by exact_mod_cast hq0)  -- q = 0
      · exact hq1 (by exact_mod_cast hq1')
      · -- q = -1: contradicts 0 < q
        have : (-1 : ℚ) < 0 := by norm_num
        have hqneg1' : q = -1 := by exact_mod_cast hqneg1
        rw [hqneg1'] at hqpos
        exact (not_lt_of_ge (le_of_lt this)) hqpos
    exact_mod_cast hlog0
  have htrz := cexp_transcendental_of_algebraic_ne_zero htalg hz0
  have hcexp : cexp ((Real.log (q : ℝ)) : ℂ) = (q : ℂ) := by
    rw [← Complex.ofReal_exp]
    exact congrArg (fun x : ℝ => (x : ℂ)) (Real.exp_log (by exact_mod_cast hqpos))
  have hc : IsAlgebraic ℚ (cexp ((Real.log (q : ℝ)) : ℂ)) := by
    rw [hcexp]
    exact isAlgebraic_rat_complex q
  exact htrz hc

/-- irrationality of the square of log(1+1/m) (the m = n corner of CDT Theorem C) -/
lemma irrational_log_one_add_inv_sq (m : ℤ) (hm : m ≠ -1) (hm0 : m ≠ 0) :
    Irrational ((Real.log (1 + 1 / (m : ℝ))) ^ 2) := by
  classical
  let r0 : ℚ := 1 + 1 / (m : ℚ)
  let t : ℝ := Real.log (1 + 1 / (m : ℝ))
  have hcast : (r0 : ℝ) = 1 + 1 / (m : ℝ) := by
    dsimp [r0]
    norm_num
  have hr0pos : 0 < r0 := by
    have h := (Submission.Helpers.one_add_inv_int_pos (m := m) hm0 hm)
    rw [← hcast] at h
    exact_mod_cast h
  have hr01 : r0 ≠ 1 := by
    intro h
    have hc := congrArg (fun x : ℚ => (x : ℝ)) h
    rw [hcast] at hc
    exact Submission.Helpers.one_add_inv_int_ne_one hm0 (by simpa using hc)
  have hlog : t = Real.log (r0 : ℝ) := by
    dsimp [t]
    rw [hcast]
  have htr : Transcendental ℚ (t : ℂ) := by
    rw [hlog]
    exact transcendental_log_rat hr0pos hr01
  by_contra hnot
  have hr : ∃ q : ℚ, (q : ℝ) = t ^ 2 := by
    rw [Irrational, Set.mem_range] at hnot
    exact Classical.not_not.mp hnot
  rcases hr with ⟨q, hq⟩
  exact htr (by
    -- algebraicity of (t : ℂ): root of X² - C q over ℚ
    refine ⟨(X : ℚ[X]) ^ 2 - C q, ?_, ?_⟩
    · -- nonzero: coeff at 2 is 1
      intro hp
      have h2 := congrArg (fun p : ℚ[X] => p.coeff 2) hp
      simp [Polynomial.coeff_one, Polynomial.coeff_C] at h2
    · -- aeval t (X² - C q) = 0
      have htq : (t : ℂ) ^ 2 = (q : ℂ) := by
        calc
          (t : ℂ) ^ 2 = ((t ^ 2 : ℝ) : ℂ) := by norm_num
          _ = (q : ℂ) := congrArg (fun x : ℝ => (x : ℂ)) hq.symm
      have hpow : (aeval (t : ℂ)) ((X : ℚ[X]) ^ 2 - C q) = (t : ℂ) ^ 2 - (q : ℂ) := by simp
      rw [hpow, htq]
      ring)


end Submission.Transcendence