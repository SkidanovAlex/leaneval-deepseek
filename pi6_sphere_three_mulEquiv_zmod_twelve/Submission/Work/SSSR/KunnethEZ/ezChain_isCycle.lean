import Mathlib
import Submission.Work.SSSR.KunnethEZ.Defs
import Submission.Work.SSSR.KunnethEZ.EZComb
import Submission.Work.SSSR.KunnethEZ.ezGen_boundary
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

variable {R : Type} [CommRing R] [Nontrivial R]

set_option maxHeartbeats 1000000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open CategoryTheory AlgebraicTopology Simplicial Limits MonoidalCategory
open scoped Simplicial
namespace Work.SSSR.KunnethEZ

noncomputable section

open Work.SSSR.Cohomology.Crux33
/-- The generator of the `n`-chains of a simplicial set attached to a simplex. -/
abbrev genC (X : SSet) {k : ℕ} (x : X _⦋k⦌) : (X.chainComplex (ezR R)).X k :=
  (X.ιChainComplex (R := (ezR R)) x).hom 1

/-! ## Bilinearity of the shuffle chain -/

/-- Pulling a scalar out of a finite sum. -/
lemma smul_mul_sum {ι M : Type*} [AddCommMonoid M] [Module R M] (s : Finset ι) (a : R)
    (b : ι → R) (g : ι → M) :
    (∑ τ ∈ s, (a * b τ) • g τ) = a • ∑ τ ∈ s, b τ • g τ := by
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl (fun τ _ => mul_smul a (b τ) (g τ))

/-- The bilinear map underlying the Eilenberg–Zilber shuffle chain: the double linear extension of
`ezGen`, as a linear map in each variable. -/
noncomputable def ezBilin (p q : ℕ) (X Y : SSet) :
    (X _⦋p⦌ →₀ R) →ₗ[R] ((Y _⦋q⦌ →₀ R) →ₗ[R] ↑(((X ⊗ Y).chainComplex (ezR R)).X (p + q))) :=
  Finsupp.linearCombination R
    (fun σ => Finsupp.linearCombination R (fun τ => ezGen p q X Y σ τ))

/-- `ezChain R` factors through the coordinate functions as the bilinear extension `ezBilin`. -/
lemma ezChain_eq_ezBilin (p q : ℕ) (X Y : SSet)
    (u : (X.chainComplex (ezR R)).X p) (v : (Y.chainComplex (ezR R)).X q) :
    ezChain R p q X Y u v = ezBilin p q X Y (coords X p u) (coords Y q v) := by
  unfold ezChain ezBilin
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [show (((coords X p) u) d • Finsupp.linearCombination R (fun τ => ezGen p q X Y d τ)) ((coords Y q) v)
      = ((coords X p) u) d • (Finsupp.linearCombination R (fun τ => ezGen p q X Y d τ)) ((coords Y q) v)
      from rfl]
  conv_rhs => rw [Finsupp.linearCombination_apply, Finsupp.sum]
  exact smul_mul_sum ((coords Y q) v).support (((coords X p) u) d)
    (fun τ => ((coords Y q) v) τ) (fun τ => ezGen p q X Y d τ)

/-- Linearity of the shuffle chain in a finite sum in the first variable. -/
lemma ezChain_sum_left_zsmul (p q : ℕ) (X Y : SSet) {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    (w : ι → (X.chainComplex (ezR R)).X p) (v : (Y.chainComplex (ezR R)).X q) :
    ezChain R p q X Y (∑ i ∈ s, a i • w i) v = ∑ i ∈ s, a i • ezChain R p q X Y (w i) v := by
  simp only [ezChain_eq_ezBilin]
  conv_lhs => rw [map_sum (g := coords X p)]
  simp only [map_zsmul]
  conv_lhs => rw [map_sum (g := ezBilin p q X Y)]
  rw [LinearMap.sum_apply]
  simp only [map_zsmul]
  rfl

/-- Linearity of the shuffle chain in a finite sum in the first variable. -/
lemma ezChain_sum_left (p q : ℕ) (X Y : SSet) {ι : Type*} (s : Finset ι) (a : ι → R)
    (w : ι → (X.chainComplex (ezR R)).X p) (v : (Y.chainComplex (ezR R)).X q) :
    ezChain R p q X Y (∑ i ∈ s, a i • w i) v = ∑ i ∈ s, a i • ezChain R p q X Y (w i) v := by
  simp only [ezChain_eq_ezBilin]
  conv_lhs => rw [map_sum (g := coords X p)]
  simp only [map_smul]
  conv_lhs => rw [map_sum (g := ezBilin p q X Y)]
  rw [LinearMap.sum_apply]
  simp only [map_smul]
  rfl

/-- Linearity of the shuffle chain in a finite sum in the second variable. -/
lemma ezChain_sum_right_zsmul (p q : ℕ) (X Y : SSet) {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    (w : ι → (Y.chainComplex (ezR R)).X q) (u : (X.chainComplex (ezR R)).X p) :
    ezChain R p q X Y u (∑ i ∈ s, a i • w i) = ∑ i ∈ s, a i • ezChain R p q X Y u (w i) := by
  simp only [ezChain_eq_ezBilin]
  conv_lhs => rw [map_sum (g := coords Y q)]
  simp only [map_zsmul]
  conv_lhs => rw [map_sum (g := ezBilin p q X Y (coords X p u))]
  simp only [map_zsmul]
/-- Linearity of the shuffle chain in a finite sum in the second variable. -/
lemma ezChain_sum_right (p q : ℕ) (X Y : SSet) {ι : Type*} (s : Finset ι) (a : ι → R)
    (w : ι → (Y.chainComplex (ezR R)).X q) (u : (X.chainComplex (ezR R)).X p) :
    ezChain R p q X Y u (∑ i ∈ s, a i • w i) = ∑ i ∈ s, a i • ezChain R p q X Y u (w i) := by
  simp only [ezChain_eq_ezBilin]
  conv_lhs => rw [map_sum (g := coords Y q)]
  simp only [map_smul]
  conv_lhs => rw [map_sum (g := ezBilin p q X Y (coords X p u))]
  simp only [map_smul]

/-! ## A chain is the sum of its generators -/

/-- `mk` of a finitely supported function, expanded in generators. -/
theorem mk_eq_sum_gen (X : SSet) (n : ℕ) (c : X _⦋n⦌ →₀ R) :
    mk X n c = ∑ x ∈ c.support, (c x) • genC X x := by
  change (Finsupp.liftAddHom
    (fun x : X _⦋n⦌ => (ModuleCat.Hom.hom (X.ιChainComplex (R := (ezR R)) x)).toAddMonoidHom)) c
    = ∑ x ∈ c.support, (c x) • (X.ιChainComplex (R := (ezR R)) x).hom 1
  rw [Finsupp.liftAddHom_apply, Finsupp.sum]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  show (ModuleCat.Hom.hom (X.ιChainComplex (R := (ezR R)) x)) (c x) = _
  rw [show c x = (c x) • (1 : R) from ((smul_eq_mul _ _).trans (mul_one _)).symm, map_smul,
    show (c x) • (1 : R) = c x from (smul_eq_mul _ _).trans (mul_one _)]

/-- A chain is the sum of its generators. -/
theorem chain_eq_sum_gen (X : SSet) (n : ℕ) (u : (X.chainComplex (ezR R)).X n) :
    u = ∑ x ∈ (coords X n u).support, (coords X n u x) • genC X x := by
  rw [← mk_eq_sum_gen X n (coords X n u)]
  exact (LinearMap.congr_fun (mk_comp_coords X n) u).symm

/-! ## The boundary of a generator -/

/-- The differential pulls a finite `ℤ`-linear combination out of a sum. -/
lemma d_sum_gen1_zsmul (X : SSet) (n : ℕ) {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    (w : ι → (X.chainComplex (ezR R)).X (n + 1)) :
    (((X.chainComplex (ezR R)).d (n + 1) n).hom) (∑ x ∈ s, a x • w x)
      = ∑ x ∈ s, a x • (((X.chainComplex (ezR R)).d (n + 1) n).hom) (w x) := by
  rw [map_sum]
  exact Finset.sum_congr rfl (fun x _ => map_zsmul _ _ _)

/-- The differential pulls a finite `ℤ`-linear combination out of a sum. -/
lemma d_sum_gen1 (X : SSet) (n : ℕ) {ι : Type*} (s : Finset ι) (a : ι → R)
    (w : ι → (X.chainComplex (ezR R)).X (n + 1)) :
    (((X.chainComplex (ezR R)).d (n + 1) n).hom) (∑ x ∈ s, a x • w x)
      = ∑ x ∈ s, a x • (((X.chainComplex (ezR R)).d (n + 1) n).hom) (w x) := by
  rw [map_sum]
  exact Finset.sum_congr rfl (fun x _ => map_smul _ _ _)

/-- The differential pulls a finite `ℤ`-linear combination out of a sum (level form). -/
lemma d_sum_gen_zsmul (X : SSet) (N : ℕ) {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    (w : ι → (X.chainComplex (ezR R)).X N) :
    (((X.chainComplex (ezR R)).d N (N - 1)).hom) (∑ x ∈ s, a x • w x)
      = ∑ x ∈ s, a x • (((X.chainComplex (ezR R)).d N (N - 1)).hom) (w x) := by
  rw [map_sum]
  exact Finset.sum_congr rfl (fun x _ => map_zsmul _ _ _)

/-- The differential pulls a finite `ℤ`-linear combination out of a sum (level form). -/
lemma d_sum_gen (X : SSet) (N : ℕ) {ι : Type*} (s : Finset ι) (a : ι → R)
    (w : ι → (X.chainComplex (ezR R)).X N) :
    (((X.chainComplex (ezR R)).d N (N - 1)).hom) (∑ x ∈ s, a x • w x)
      = ∑ x ∈ s, a x • (((X.chainComplex (ezR R)).d N (N - 1)).hom) (w x) := by
  rw [map_sum]
  exact Finset.sum_congr rfl (fun x _ => map_smul _ _ _)

/-- The boundary of a generator, expanded in the face generators. -/
lemma d_genC (n : ℕ) (X : SSet) (x : X _⦋n + 1⦌) :
    ((X.chainComplex (ezR R)).d (n + 1) n).hom (genC X x)
      = ∑ i : Fin (n + 2), ((-1 : ℤ) ^ (i : ℕ)) • genC X (X.δ i x) := by
  have h := SSet.ιChainComplex_d X (ezR R) x
  have h2 := congrArg (fun (f : (ezR R) ⟶ (X.chainComplex (ezR R)).X n) => f.hom (1 : R)) h
  simp only [ModuleCat.hom_comp, ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.comp_apply] at h2
  exact h2

/-! ## The two "boundary" bilinear maps of the prism identity -/

/-- The `X`-boundary shuffle map: the linear extension, in the first variable, of the `(p,q+1)`
component of `∂ (ezGen (p+1) (q+1))`. -/
noncomputable def rawXBilin (p q : ℕ) (X Y : SSet) :
    (X _⦋p⦌ →₀ R) →ₗ[R]
      ((Y _⦋q + 1⦌ →₀ R) →ₗ[R] ↑(((X ⊗ Y).chainComplex (ezR R)).X ((p + 1) + (q + 1) - 1))) :=
  ∑ T : Sh23 (p + 1) (q + 1), shufSignN T.1 •
    (Finsupp.linearCombination R (fun ρ : X _⦋p⦌ =>
      Finsupp.linearCombination R (fun τ : Y _⦋q + 1⦌ =>
        genP R (X.map (aMap23 (p + 1) (q + 1) T).op ρ)
          (Y.map (bMap23 (p + 1) (q + 1) T).op τ))))

/-- The `Y`-boundary shuffle map: the linear extension, in the second variable, of the `(p+1,q)`
component of `∂ (ezGen (p+1) (q+1))`. -/
noncomputable def rawYBilin (p q : ℕ) (X Y : SSet) :
    (X _⦋p + 1⦌ →₀ R) →ₗ[R]
      ((Y _⦋q⦌ →₀ R) →ₗ[R] ↑(((X ⊗ Y).chainComplex (ezR R)).X ((p + 1) + (q + 1) - 1))) :=
  ∑ U : Sh32 (p + 1) (q + 1), shufSignN U.1 •
    (Finsupp.linearCombination R (fun ρ : X _⦋p + 1⦌ =>
      Finsupp.linearCombination R (fun τ : Y _⦋q⦌ =>
        genP R (X.map (aMap32 (p + 1) (q + 1) U).op ρ)
          (Y.map (bMap32 (p + 1) (q + 1) U).op τ))))

/-- The `X`-boundary term of the derivation identity on chains. -/
noncomputable def rawX (p q : ℕ) (X Y : SSet) (w : (X.chainComplex (ezR R)).X p)
    (v : (Y.chainComplex (ezR R)).X (q + 1)) :
    ((X ⊗ Y).chainComplex (ezR R)).X ((p + 1) + (q + 1) - 1) :=
  rawXBilin p q X Y (coords X p w) (coords Y (q + 1) v)

/-- The `Y`-boundary term of the derivation identity on chains. -/
noncomputable def rawY (p q : ℕ) (X Y : SSet) (u : (X.chainComplex (ezR R)).X (p + 1))
    (w : (Y.chainComplex (ezR R)).X q) :
    ((X ⊗ Y).chainComplex (ezR R)).X ((p + 1) + (q + 1) - 1) :=
  rawYBilin p q X Y (coords X (p + 1) u) (coords Y q w)

/-- The `X`-boundary term on a pair of generators. -/
lemma rawX_gen (p q : ℕ) (X Y : SSet) (σ : X _⦋p⦌) (τ : Y _⦋q + 1⦌) :
    rawX p q X Y (genC X σ) (genC Y τ)
      = ∑ T : Sh23 (p + 1) (q + 1), shufSignN T.1 •
          genP R (X.map (aMap23 (p + 1) (q + 1) T).op σ)
          (Y.map (bMap23 (p + 1) (q + 1) T).op τ) := by
  unfold rawX rawXBilin
  rw [coords_ι, coords_ι]
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  show shufSignN T.1 • ((Finsupp.linearCombination R (fun ρ : X _⦋p⦌ =>
      Finsupp.linearCombination R (fun τ' : Y _⦋q + 1⦌ =>
        genP R (X.map (aMap23 (p + 1) (q + 1) T).op ρ)
          (Y.map (bMap23 (p + 1) (q + 1) T).op τ')))) (Finsupp.single σ 1)
        (Finsupp.single τ 1))
      = shufSignN T.1 • genP R (X.map (aMap23 (p + 1) (q + 1) T).op σ)
          (Y.map (bMap23 (p + 1) (q + 1) T).op τ)
  congr 1
  rw [Finsupp.linearCombination_single (R := R) (v := fun ρ : X _⦋p⦌ =>
      Finsupp.linearCombination R (fun τ' : Y _⦋q + 1⦌ =>
        genP R (X.map (aMap23 (p + 1) (q + 1) T).op ρ)
          (Y.map (bMap23 (p + 1) (q + 1) T).op τ'))) (c := 1) (a := σ)]
  rw [one_smul]
  rw [Finsupp.linearCombination_single (R := R) (v := fun τ' : Y _⦋q + 1⦌ =>
      genP R (X.map (aMap23 (p + 1) (q + 1) T).op σ)
          (Y.map (bMap23 (p + 1) (q + 1) T).op τ')) (c := 1) (a := τ)]
  rw [one_smul]

lemma rawY_gen (p q : ℕ) (X Y : SSet) (σ : X _⦋p + 1⦌) (τ : Y _⦋q⦌) :
    rawY p q X Y (genC X σ) (genC Y τ)
      = ∑ U : Sh32 (p + 1) (q + 1), shufSignN U.1 •
          genP R (X.map (aMap32 (p + 1) (q + 1) U).op σ)
          (Y.map (bMap32 (p + 1) (q + 1) U).op τ) := by
  unfold rawY rawYBilin
  rw [coords_ι, coords_ι]
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  refine Finset.sum_congr rfl (fun T _ => ?_)
  show shufSignN T.1 • ((Finsupp.linearCombination R (fun ρ : X _⦋p + 1⦌ =>
      Finsupp.linearCombination R (fun τ' : Y _⦋q⦌ =>
        genP R (X.map (aMap32 (p + 1) (q + 1) T).op ρ)
          (Y.map (bMap32 (p + 1) (q + 1) T).op τ')))) (Finsupp.single σ 1)
        (Finsupp.single τ 1))
      = shufSignN T.1 • genP R (X.map (aMap32 (p + 1) (q + 1) T).op σ)
          (Y.map (bMap32 (p + 1) (q + 1) T).op τ)
  congr 1
  rw [Finsupp.linearCombination_single (R := R) (v := fun ρ : X _⦋p + 1⦌ =>
      Finsupp.linearCombination R (fun τ' : Y _⦋q⦌ =>
        genP R (X.map (aMap32 (p + 1) (q + 1) T).op ρ)
          (Y.map (bMap32 (p + 1) (q + 1) T).op τ'))) (c := 1) (a := σ)]
  rw [one_smul]
  rw [Finsupp.linearCombination_single (R := R) (v := fun τ' : Y _⦋q⦌ =>
      genP R (X.map (aMap32 (p + 1) (q + 1) T).op σ)
          (Y.map (bMap32 (p + 1) (q + 1) T).op τ')) (c := 1) (a := τ)]
  rw [one_smul]

/-- Linearity of `rawX` in the first variable. -/
lemma rawX_sum_left_zsmul (p q : ℕ) (X Y : SSet) {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    (w : ι → (X.chainComplex (ezR R)).X p) (v : (Y.chainComplex (ezR R)).X (q + 1)) :
    rawX p q X Y (∑ i ∈ s, a i • w i) v = ∑ i ∈ s, a i • rawX p q X Y (w i) v := by
  simp only [rawX]
  conv_lhs => rw [map_sum (g := coords X p)]
  simp only [map_zsmul]
  conv_lhs => rw [map_sum (g := rawXBilin p q X Y)]
  rw [LinearMap.sum_apply]
  simp only [map_zsmul]
  rfl

/-- Linearity of `rawX` in the first variable. -/
lemma rawX_sum_left (p q : ℕ) (X Y : SSet) {ι : Type*} (s : Finset ι) (a : ι → R)
    (w : ι → (X.chainComplex (ezR R)).X p) (v : (Y.chainComplex (ezR R)).X (q + 1)) :
    rawX p q X Y (∑ i ∈ s, a i • w i) v = ∑ i ∈ s, a i • rawX p q X Y (w i) v := by
  simp only [rawX]
  conv_lhs => rw [map_sum (g := coords X p)]
  simp only [map_smul]
  conv_lhs => rw [map_sum (g := rawXBilin p q X Y)]
  rw [LinearMap.sum_apply]
  simp only [map_smul]
  rfl

/-- Linearity of `rawX` in the second variable. -/
lemma rawX_sum_right_zsmul (p q : ℕ) (X Y : SSet) {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    (w : ι → (Y.chainComplex (ezR R)).X (q + 1)) (u : (X.chainComplex (ezR R)).X p) :
    rawX p q X Y u (∑ i ∈ s, a i • w i) = ∑ i ∈ s, a i • rawX p q X Y u (w i) := by
  simp only [rawX]
  conv_lhs => rw [map_sum (g := coords Y (q + 1))]
  simp only [map_zsmul]
  conv_lhs => rw [map_sum (g := rawXBilin p q X Y (coords X p u))]
  simp only [map_zsmul]

/-- Linearity of `rawX` in the second variable. -/
lemma rawX_sum_right (p q : ℕ) (X Y : SSet) {ι : Type*} (s : Finset ι) (a : ι → R)
    (w : ι → (Y.chainComplex (ezR R)).X (q + 1)) (u : (X.chainComplex (ezR R)).X p) :
    rawX p q X Y u (∑ i ∈ s, a i • w i) = ∑ i ∈ s, a i • rawX p q X Y u (w i) := by
  simp only [rawX]
  conv_lhs => rw [map_sum (g := coords Y (q + 1))]
  simp only [map_smul]
  conv_lhs => rw [map_sum (g := rawXBilin p q X Y (coords X p u))]
  simp only [map_smul]

/-- Linearity of `rawY` in the first variable. -/
lemma rawY_sum_left_zsmul (p q : ℕ) (X Y : SSet) {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    (w : ι → (X.chainComplex (ezR R)).X (p + 1)) (v : (Y.chainComplex (ezR R)).X q) :
    rawY p q X Y (∑ i ∈ s, a i • w i) v = ∑ i ∈ s, a i • rawY p q X Y (w i) v := by
  simp only [rawY]
  conv_lhs => rw [map_sum (g := coords X (p + 1))]
  simp only [map_zsmul]
  conv_lhs => rw [map_sum (g := rawYBilin p q X Y)]
  rw [LinearMap.sum_apply]
  simp only [map_zsmul]
  rfl

/-- Linearity of `rawY` in the first variable. -/
lemma rawY_sum_left (p q : ℕ) (X Y : SSet) {ι : Type*} (s : Finset ι) (a : ι → R)
    (w : ι → (X.chainComplex (ezR R)).X (p + 1)) (v : (Y.chainComplex (ezR R)).X q) :
    rawY p q X Y (∑ i ∈ s, a i • w i) v = ∑ i ∈ s, a i • rawY p q X Y (w i) v := by
  simp only [rawY]
  conv_lhs => rw [map_sum (g := coords X (p + 1))]
  simp only [map_smul]
  conv_lhs => rw [map_sum (g := rawYBilin p q X Y)]
  rw [LinearMap.sum_apply]
  simp only [map_smul]
  rfl

/-- Linearity of `rawY` in the second variable. -/
lemma rawY_sum_right_zsmul (p q : ℕ) (X Y : SSet) {ι : Type*} (s : Finset ι) (a : ι → ℤ)
    (w : ι → (Y.chainComplex (ezR R)).X q) (u : (X.chainComplex (ezR R)).X (p + 1)) :
    rawY p q X Y u (∑ i ∈ s, a i • w i) = ∑ i ∈ s, a i • rawY p q X Y u (w i) := by
  simp only [rawY]
  conv_lhs => rw [map_sum (g := coords Y q)]
  simp only [map_zsmul]
  conv_lhs => rw [map_sum (g := rawYBilin p q X Y (coords X (p + 1) u))]
  simp only [map_zsmul]

/-- Linearity of `rawY` in the second variable. -/
lemma rawY_sum_right (p q : ℕ) (X Y : SSet) {ι : Type*} (s : Finset ι) (a : ι → R)
    (w : ι → (Y.chainComplex (ezR R)).X q) (u : (X.chainComplex (ezR R)).X (p + 1)) :
    rawY p q X Y u (∑ i ∈ s, a i • w i) = ∑ i ∈ s, a i • rawY p q X Y u (w i) := by
  simp only [rawY]
  conv_lhs => rw [map_sum (g := coords Y q)]
  simp only [map_smul]
  conv_lhs => rw [map_sum (g := rawYBilin p q X Y (coords X (p + 1) u))]
  simp only [map_smul]

/-- The prism identity on a pair of generators, transported to the chain level: the boundary of
`ezGen (p+1) (q+1) σ τ` is the two `rawX`/`rawY` boundary terms applied to the boundaries of the
generators. -/
lemma d_ezGen (p q : ℕ) (X Y : SSet) (σ : X _⦋p + 1⦌) (τ : Y _⦋q + 1⦌) :
    (((X ⊗ Y).chainComplex (ezR R)).d ((p + 1) + (q + 1)) ((p + 1) + (q + 1) - 1)).hom
        (ezGen (p + 1) (q + 1) X Y σ τ)
      = rawX p q X Y (((X.chainComplex (ezR R)).d (p + 1) p).hom (genC X σ)) (genC Y τ)
        + (-1 : ℤ) ^ (p + 1) •
            rawY p q X Y (genC X σ) (((Y.chainComplex (ezR R)).d (q + 1) q).hom (genC Y τ)) := by
  rw [d_genC p X σ, d_genC q Y τ, rawX_sum_left_zsmul, rawY_sum_right_zsmul, ezGen_boundary]
  have hA : (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
        (∑ T : Sh23 (p + 1) (q + 1), shufSignN T.1 •
          genP R (X.map (aMap23 (p + 1) (q + 1) T).op (X.δ i σ))
          (Y.map (bMap23 (p + 1) (q + 1) T).op τ)))
      = (∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) •
          rawX p q X Y (genC X (X.δ i σ)) (genC Y τ)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [rawX_gen]
  have hB : (∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) •
        (∑ U : Sh32 (p + 1) (q + 1), shufSignN U.1 •
          genP R (X.map (aMap32 (p + 1) (q + 1) U).op σ)
          (Y.map (bMap32 (p + 1) (q + 1) U).op (Y.δ j τ))))
      = (∑ j : Fin (q + 2), (-1 : ℤ) ^ (j : ℕ) •
          rawY p q X Y (genC X σ) (genC Y (Y.δ j τ))) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [rawY_gen]
  rw [hA, hB]

/-- The `R`-action commutes with the `ℤ`-action. -/
lemma smul_zsmul_comm {M : Type*} [AddCommGroup M] [Module R M] (r : R) (s : ℤ) (x : M) :
    r • (s • x) = s • (r • x) := by
  rw [← Int.cast_smul_eq_zsmul (R := R) s x, ← Int.cast_smul_eq_zsmul (R := R) s (r • x),
    smul_smul, smul_smul, mul_comm]

/-- **The derivation identity** (in the shifted form): the boundary of the shuffle chain of two
chains is the `X`-boundary term applied to `∂u` plus `(-1)^{p+1}` times the `Y`-boundary term
applied to `∂v`. -/
theorem ezChain_derivation (p q : ℕ) (X Y : SSet)
    (u : (X.chainComplex (ezR R)).X (p + 1)) (v : (Y.chainComplex (ezR R)).X (q + 1)) :
    (((X ⊗ Y).chainComplex (ezR R)).d ((p + 1) + (q + 1)) ((p + 1) + (q + 1) - 1)).hom
        (ezChain R (p + 1) (q + 1) X Y u v)
      = rawX p q X Y (((X.chainComplex (ezR R)).d (p + 1) p).hom u) v
        + (-1 : ℤ) ^ (p + 1) • rawY p q X Y u (((Y.chainComplex (ezR R)).d (q + 1) q).hom v) := by
  have hL : (((X ⊗ Y).chainComplex (ezR R)).d ((p + 1) + (q + 1)) ((p + 1) + (q + 1) - 1)).hom
        (ezChain R (p + 1) (q + 1) X Y u v)
      = ∑ σ ∈ (coords X (p + 1) u).support, (coords X (p + 1) u) σ •
          (∑ τ ∈ (coords Y (q + 1) v).support, (coords Y (q + 1) v) τ •
            (((X ⊗ Y).chainComplex (ezR R)).d ((p + 1) + (q + 1)) ((p + 1) + (q + 1) - 1)).hom
              (ezGen (p + 1) (q + 1) X Y σ τ)) := by
    conv_lhs => rw [chain_eq_sum_gen X (p + 1) u, chain_eq_sum_gen Y (q + 1) v]
    rw [ezChain_sum_left]
    simp only [ezChain_sum_right, ezChain_gen]
    rw [d_sum_gen (X := X ⊗ Y) (N := (p + 1) + (q + 1))]
    refine Finset.sum_congr rfl (fun σ _ => ?_)
    rw [d_sum_gen (X := X ⊗ Y) (N := (p + 1) + (q + 1))]
  have hX : rawX p q X Y (((X.chainComplex (ezR R)).d (p + 1) p).hom u) v
      = ∑ σ ∈ (coords X (p + 1) u).support, (coords X (p + 1) u) σ •
          (∑ τ ∈ (coords Y (q + 1) v).support, (coords Y (q + 1) v) τ •
            rawX p q X Y (((X.chainComplex (ezR R)).d (p + 1) p).hom (genC X σ)) (genC Y τ)) := by
    conv_lhs => rw [chain_eq_sum_gen X (p + 1) u, chain_eq_sum_gen Y (q + 1) v]
    rw [d_sum_gen1 (X := X) (n := p), rawX_sum_left]
    simp only [rawX_sum_right]
  have hY : rawY p q X Y u (((Y.chainComplex (ezR R)).d (q + 1) q).hom v)
      = ∑ σ ∈ (coords X (p + 1) u).support, (coords X (p + 1) u) σ •
          (∑ τ ∈ (coords Y (q + 1) v).support, (coords Y (q + 1) v) τ •
            rawY p q X Y (genC X σ) (((Y.chainComplex (ezR R)).d (q + 1) q).hom (genC Y τ))) := by
    conv_lhs => rw [chain_eq_sum_gen X (p + 1) u, chain_eq_sum_gen Y (q + 1) v]
    rw [d_sum_gen1 (X := Y) (n := q), rawY_sum_left]
    simp only [rawY_sum_right]
  rw [hL, hX, hY]
  simp only [d_ezGen, smul_add, Finset.sum_add_distrib, Finset.smul_sum, smul_smul,
    mul_comm, mul_left_comm, mul_assoc]
  congr 1
  simp only [smul_zsmul_comm]

end

end Work.SSSR.KunnethEZ
