import Mathlib
import Submission.Work.Cohomology.relCupH
import Submission.Work.Cohomology.relKernMono
import Submission.Work.Cohomology.cupNaturalH
import Submission.Work.Cohomology.mixedRelCupH
import Submission.Work.Cohomology.relIncl_relCupH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000


/-!
# The "A+B" cochain complex with coefficients in a general commutative ring

For open `A, B ⊆ X` and any commutative ring `R`, this file defines the `A+B` cochain complex
`C^*(X, A+B;R) = C^*(X,A;R) ∩ C^*(X,B;R)`, the inclusion `C^*(X, A∪B;R) → C^*(X,A+B;R)`, the
Alexander–Whitney product of a relative `A`-cochain with a relative `B`-cochain (landing in the
`A+B` complex), the resulting relative-relative cup product on cohomology and its compatibility
with the absolute cup product.  The single remaining input is the quasi-isomorphism
`pdABInclRelR` (proved in `Submission/Work/Whitney/relABQuasiIso.lean`).
-/


set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Whitney.ThreeCup

noncomputable section
open Work.Cohomology

variable {R : Type} [CommRing R]

/-- Three-complex Leibniz rule. -/
def Leibniz3 (K₁ K₂ L : CochainComplex (ModuleCat R) ℕ)
    (star : ∀ m n : ℕ, K₁.X m →ₗ[R] K₂.X n →ₗ[R] L.X (m + n)) : Prop :=
  ∀ {m n : ℕ} (a : K₁.X m) (b : K₂.X n),
    (L.d (m + n) (m + n + 1)).hom (star m n a b) =
      (Nat.add_right_comm m 1 n ▸ star (m + 1) n ((K₁.d m (m + 1)).hom a) b) +
      ((-1 : R) ^ m) • star m (n + 1) a ((K₂.d n (n + 1)).hom b)

variable {K₁ K₂ L : CochainComplex (ModuleCat R) ℕ}
variable {star : ∀ m n : ℕ, K₁.X m →ₗ[R] K₂.X n →ₗ[R] L.X (m + n)}

lemma star3_add_left (m n : ℕ) (a a' : K₁.X m) (b : K₂.X n) :
    star m n (a + a') b = star m n a b + star m n a' b := by
  rw [map_add, LinearMap.add_apply]

lemma star3_smul_left (m n : ℕ) (c : R) (a : K₁.X m) (b : K₂.X n) :
    star m n (c • a) b = c • star m n a b := by
  rw [map_smul, LinearMap.smul_apply]

lemma star3_zero_left (m n : ℕ) (b : K₂.X n) : star m n 0 b = 0 := by
  rw [map_zero, LinearMap.zero_apply]

lemma star3_add_right (m n : ℕ) (a : K₁.X m) (b b' : K₂.X n) :
    star m n a (b + b') = star m n a b + star m n a b' :=
  map_add (star m n a) b b'

lemma star3_smul_right (m n : ℕ) (c : R) (a : K₁.X m) (b : K₂.X n) :
    star m n a (c • b) = c • star m n a b :=
  map_smul (star m n a) c b

lemma star3_zero_right (m n : ℕ) (a : K₁.X m) : star m n a 0 = 0 :=
  map_zero (star m n a)

lemma star3_leibniz_right (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ) (a : K₁.X m)
    (ha : (K₁.d m (m + 1)).hom a = 0) (x : K₂.X n) :
    (L.d (m + n) (m + (n + 1))).hom (star m n a x) =
      ((-1 : R) ^ m) • star m (n + 1) a ((K₂.d n (n + 1)).hom x) := by
  have h0 := hleib a x
  rw [ha, star3_zero_left, eqRec_zero_K, zero_add] at h0
  exact h0

lemma star3_leibniz_left (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ) (x : K₁.X m) (b : K₂.X n)
    (hb : (K₂.d n (n + 1)).hom b = 0) :
    (L.d (m + n) ((m + 1) + n)).hom (star m n x b) =
      star (m + 1) n ((K₁.d m (m + 1)).hom x) b := by
  have hh : (m + 1) + n = m + n + 1 := Nat.add_right_comm m 1 n
  set γ : L.X ((m + 1) + n) := star (m + 1) n ((K₁.d m (m + 1)).hom x) b with hγ
  have h : (L.d (m + n) (m + n + 1)).hom (star m n x b) = hh ▸ γ := by
    have h0 := hleib x b
    rw [hb, star3_zero_right, smul_zero, add_zero] at h0
    exact h0
  have hd := HomologicalComplex.d_comp_XIsoOfEq_inv L hh (m + n)
  have hd2 : (L.d (m + n) ((m + 1) + n)).hom (star m n x b) =
      (L.XIsoOfEq hh).inv ((L.d (m + n) (m + n + 1)).hom (star m n x b)) := by
    have hd' := congrArg (fun (g : L.X (m + n) ⟶ L.X ((m + 1) + n)) => g.hom (star m n x b)) hd
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at hd'
    exact hd'.symm
  have key : (L.XIsoOfEq hh).inv (hh ▸ γ) = γ := by
    rw [XIsoOfEq_inv_apply_K, eqRec_symm_eqRec_self_K]
  calc (L.d (m + n) ((m + 1) + n)).hom (star m n x b)
      = (L.XIsoOfEq hh).inv ((L.d (m + n) (m + n + 1)).hom (star m n x b)) := hd2
    _ = (L.XIsoOfEq hh).inv (hh ▸ γ) := by rw [h]
    _ = γ := key

lemma star3_cocycle_cochain (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ) (a : K₁.X m) (b : K₂.X n)
    (ha : (K₁.d m (m + 1)).hom a = 0) (hb : (K₂.d n (n + 1)).hom b = 0) :
    (L.d (m + n) (m + n + 1)).hom (star m n a b) = 0 := by
  have h := hleib a b
  rw [ha, hb, star3_zero_left, star3_zero_right, smul_zero, add_zero, eqRec_zero_K] at h
  exact h

noncomputable def cup3ZK (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ)
    (z : K₁.cycles m) (w : K₂.cycles n) : L.cycles (m + n) :=
  cocycleOfK L (star m n ((K₁.iCycles m).hom z) ((K₂.iCycles n).hom w))
    (star3_cocycle_cochain hleib m n _ _ (iCycles_d_apply_K K₁ m z) (iCycles_d_apply_K K₂ n w))

lemma iCycles_cup3ZK (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ)
    (z : K₁.cycles m) (w : K₂.cycles n) :
    (L.iCycles (m + n)).hom (cup3ZK hleib m n z w) =
      star m n ((K₁.iCycles m).hom z) ((K₂.iCycles n).hom w) :=
  iCycles_cocycleOfK L _ _

lemma cup3ZK_add_left (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ)
    (z z' : K₁.cycles m) (w : K₂.cycles n) :
    cup3ZK hleib m n (z + z') w = cup3ZK hleib m n z w + cup3ZK hleib m n z' w := by
  apply iCycles_injective_K L (m + n)
  rw [iCycles_add_K, iCycles_cup3ZK, iCycles_add_K, iCycles_cup3ZK, iCycles_cup3ZK]
  exact star3_add_left m n _ _ _

lemma cup3ZK_smul_left (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ) (a : R)
    (z : K₁.cycles m) (w : K₂.cycles n) :
    cup3ZK hleib m n (a • z) w = a • cup3ZK hleib m n z w := by
  apply iCycles_injective_K L (m + n)
  rw [iCycles_smul_K, iCycles_cup3ZK, iCycles_smul_K, iCycles_cup3ZK]
  exact star3_smul_left m n a _ _

lemma cup3ZK_add_right (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ)
    (z : K₁.cycles m) (w w' : K₂.cycles n) :
    cup3ZK hleib m n z (w + w') = cup3ZK hleib m n z w + cup3ZK hleib m n z w' := by
  apply iCycles_injective_K L (m + n)
  rw [iCycles_add_K, iCycles_cup3ZK, iCycles_add_K, iCycles_cup3ZK, iCycles_cup3ZK]
  exact star3_add_right m n _ _ _

lemma cup3ZK_smul_right (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ) (a : R)
    (z : K₁.cycles m) (w : K₂.cycles n) :
    cup3ZK hleib m n z (a • w) = a • cup3ZK hleib m n z w := by
  apply iCycles_injective_K L (m + n)
  rw [iCycles_smul_K, iCycles_cup3ZK, iCycles_smul_K, iCycles_cup3ZK]
  exact star3_smul_right m n a _ _

/-- The product with a fixed cycle of `K₁`, as a linear map on the cycles of `K₂`. -/
noncomputable def cup3ZWK (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ) (z : K₁.cycles m) :
    K₂.cycles n →ₗ[R] L.cycles (m + n) where
  toFun w := cup3ZK hleib m n z w
  map_add' := cup3ZK_add_right hleib m n z
  map_smul' := fun a w => cup3ZK_smul_right hleib m n a z w

/-- The map on cycles `w ↦ [a ⋆ w]`, where `a = iCycles z`. -/
noncomputable def chi3WK (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ) (z : K₁.cycles m) :
    K₂.cycles n ⟶ L.homology (m + n) :=
  ModuleCat.ofHom (((L.homologyπ (m + n)).hom).comp (cup3ZWK hleib m n z))

lemma chi3WK_apply (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ) (z : K₁.cycles m)
    (w : K₂.cycles n) :
    (chi3WK hleib m n z).hom w = (L.homologyπ (m + n)).hom (cup3ZK hleib m n z w) := rfl

lemma toCycles_chi3WK (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ) (z : K₁.cycles m) :
    K₂.toCycles ((ComplexShape.up ℕ).prev n) n ≫ chi3WK hleib m n z = 0 := by
  generalize hpm : (ComplexShape.up ℕ).prev n = pm
  rcases n with _ | n'
  · have hpm' : pm = 0 := by rw [← hpm]; simp
    rw [hpm']
    rw [HomologicalComplex.toCycles_eq_zero _ (by simp [ComplexShape.up_Rel])]
    simp
  · have hpm' : pm = n' := by rw [← hpm]; simp
    rw [hpm']
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hchain : (K₂.iCycles (n' + 1)).hom ((K₂.toCycles n' (n' + 1)).hom x) =
        (K₂.d n' (n' + 1)).hom x :=
      iCycles_toCycles_K K₂ n' (n' + 1) x
    have hZ : (chi3WK hleib m (n' + 1) z).hom ((K₂.toCycles n' (n' + 1)).hom x) = 0 := by
      rw [chi3WK_apply]
      refine homologyπ_eq_zero_of_d_K L (m + (n' + 1)) (m + n')
        (cup3ZK hleib m (n' + 1) z ((K₂.toCycles n' (n' + 1)).hom x))
        (((-1 : R) ^ m) • star m n' ((K₁.iCycles m).hom z) x) ?_
      rw [iCycles_cup3ZK, hchain, map_smul]
      rw [star3_leibniz_right hleib m n' ((K₁.iCycles m).hom z)
          (iCycles_d_apply_K K₁ m z) x,
        smul_smul, neg_one_pow_mul_self, one_smul]
    simpa using hZ

/-- The underlying linear map of the second descent: `[w] ↦ [a ⋆ w]`. -/
noncomputable def Psi3FunK (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ) (z : K₁.cycles m) :
    K₂.homology n →ₗ[R] L.homology (m + n) :=
  (descH_K K₂ n (chi3WK hleib m n z) (toCycles_chi3WK hleib m n z)).hom

lemma Psi3FunK_apply (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ) (z : K₁.cycles m)
    (w : K₂.cycles n) :
    Psi3FunK hleib m n z ((K₂.homologyπ n).hom w) = (chi3WK hleib m n z).hom w :=
  descH_apply_K K₂ _ _ w

lemma Psi3FunK_add (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ) (z z' : K₁.cycles m) :
    Psi3FunK hleib m n (z + z') = Psi3FunK hleib m n z + Psi3FunK hleib m n z' := by
  apply LinearMap.ext
  intro y
  obtain ⟨w, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((K₂.homologyπ n))).mp inferInstance y
  rw [LinearMap.add_apply, Psi3FunK_apply, Psi3FunK_apply, Psi3FunK_apply, chi3WK_apply,
    chi3WK_apply, chi3WK_apply, cup3ZK_add_left, homologyπ_add_K]

lemma Psi3FunK_smul (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ) (a : R) (z : K₁.cycles m) :
    Psi3FunK hleib m n (a • z) = a • Psi3FunK hleib m n z := by
  apply LinearMap.ext
  intro y
  obtain ⟨w, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((K₂.homologyπ n))).mp inferInstance y
  rw [LinearMap.smul_apply, Psi3FunK_apply, Psi3FunK_apply, chi3WK_apply, chi3WK_apply,
    cup3ZK_smul_left, homologyπ_smul_K]

/-- Descent in the second variable. -/
noncomputable def Psi3K (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ) :
    K₁.cycles m →ₗ[R] (K₂.homology n →ₗ[R] L.homology (m + n)) where
  toFun := Psi3FunK hleib m n
  map_add' := Psi3FunK_add hleib m n
  map_smul' := Psi3FunK_smul hleib m n

lemma Psi3K_apply (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ) (z : K₁.cycles m)
    (w : K₂.cycles n) :
    Psi3K hleib m n z ((K₂.homologyπ n).hom w) = (chi3WK hleib m n z).hom w :=
  Psi3FunK_apply hleib m n z w

lemma toCycles_Psi3K (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ) :
    K₁.toCycles ((ComplexShape.up ℕ).prev m) m ≫ ModuleCat.ofHom (Psi3K hleib m n) = 0 := by
  generalize hpn : (ComplexShape.up ℕ).prev m = pm
  rcases m with _ | m'
  · have hpn' : pm = 0 := by rw [← hpn]; simp
    rw [hpn']
    rw [HomologicalComplex.toCycles_eq_zero _ (by simp [ComplexShape.up_Rel])]
    simp
  · have hpn' : pm = m' := by rw [← hpn]; simp
    rw [hpn']
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have hx : Psi3K hleib (m' + 1) n ((K₁.toCycles m' (m' + 1)).hom x) = 0 := by
      apply LinearMap.ext
      intro y
      obtain ⟨w, rfl⟩ :=
        (ModuleCat.epi_iff_surjective ((K₂.homologyπ n))).mp inferInstance y
      rw [Psi3K_apply, chi3WK_apply]
      have hchain : (K₁.iCycles (m' + 1)).hom ((K₁.toCycles m' (m' + 1)).hom x) =
          (K₁.d m' (m' + 1)).hom x :=
        iCycles_toCycles_K K₁ m' (m' + 1) x
      refine homologyπ_eq_zero_of_d_K L ((m' + 1) + n) (m' + n)
        (cup3ZK hleib (m' + 1) n ((K₁.toCycles m' (m' + 1)).hom x) w)
        (star m' n x ((K₂.iCycles n).hom w)) ?_
      rw [iCycles_cup3ZK, hchain]
      exact (star3_leibniz_left hleib m' n x ((K₂.iCycles n).hom w)
        (iCycles_d_apply_K K₂ n w)).symm
    simpa using hx

/-- The three-complex cup product pairing on the cohomology of `K₁` and `K₂`. -/
noncomputable def cup3MapK (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ) :
    K₁.homology m ⟶ ModuleCat.of R (K₂.homology n →ₗ[R] L.homology (m + n)) :=
  descH_K K₁ m (ModuleCat.ofHom (Psi3K hleib m n)) (toCycles_Psi3K hleib m n)

lemma cup3MapK_apply (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ) (z : K₁.cycles m) :
    (cup3MapK hleib m n).hom ((K₁.homologyπ m).hom z) = Psi3K hleib m n z :=
  descH_apply_K K₁ _ _ z

lemma cup3ZK_cocycleOfK (hleib : Leibniz3 K₁ K₂ L star) (m n : ℕ) (a : K₁.X m) (b : K₂.X n)
    (ha : (K₁.d m (m + 1)).hom a = 0) (hb : (K₂.d n (n + 1)).hom b = 0)
    (h : (L.d (m + n) (m + n + 1)).hom (star m n a b) = 0) :
    cup3ZK hleib m n (cocycleOfK K₁ a ha) (cocycleOfK K₂ b hb) =
      cocycleOfK L (star m n a b) h := by
  apply iCycles_injective_K L (m + n)
  rw [iCycles_cup3ZK, iCycles_cocycleOfK, iCycles_cocycleOfK, iCycles_cocycleOfK]

/-- **The abstract three-complex descent.** -/
theorem exists_cup3_of_generic (K₁ K₂ L : CochainComplex (ModuleCat R) ℕ)
    (star : ∀ m n : ℕ, K₁.X m →ₗ[R] K₂.X n →ₗ[R] L.X (m + n))
    (hleib : Leibniz3 K₁ K₂ L star) :
    ∃ cupH : ∀ m n : ℕ, K₁.homology m →ₗ[R] K₂.homology n →ₗ[R] L.homology (m + n),
      ∀ (m n : ℕ) (a : K₁.X m) (b : K₂.X n)
        (ha : (K₁.d m (m + 1)).hom a = 0) (hb : (K₂.d n (n + 1)).hom b = 0)
        (h : (L.d (m + n) (m + n + 1)).hom (star m n a b) = 0),
        cupH m n ((K₁.homologyπ m).hom (cocycleOfK K₁ a ha))
                 ((K₂.homologyπ n).hom (cocycleOfK K₂ b hb)) =
          (L.homologyπ (m + n)).hom (cocycleOfK L (star m n a b) h) := by
  refine ⟨fun m n => (cup3MapK hleib m n).hom, ?_⟩
  intro m n a b ha hb h
  rw [cup3MapK_apply, Psi3K_apply, chi3WK_apply, cup3ZK_cocycleOfK hleib m n a b ha hb h]

end
end Work.Whitney.ThreeCup

namespace Work.Whitney
open Work.Cohomology

noncomputable section
open CategoryTheory AlgebraicTopology CategoryTheory.Limits

variable {R : Type} [CommRing R]

/-- The degree-`n` part of the `A+B` complex over `R`. -/
def pdABKernR (X : TopCat) (A B : Set X) (n : ℕ) :
    Submodule R ((singularCochainComplex R X).X n) :=
  relKern R X A n ⊓ relKern R X B n

theorem relKern_d_memR (X : TopCat) (A : Set X) (n : ℕ)
    (y : (singularCochainComplex R X).X n) (hy : y ∈ relKern R X A n) :
    ((singularCochainComplex R X).d n (n+1)).hom y ∈ relKern R X A (n+1) := by
  rw [relKern, LinearMap.mem_ker] at hy ⊢
  have hc := congrArg ModuleCat.Hom.hom ((restr R X A).comm n (n+1))
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hc
  have hcx := LinearMap.congr_fun hc y
  simp only [LinearMap.comp_apply] at hcx
  simp only [hy, map_zero] at hcx
  exact hcx.symm

/-- The differential of the `A+B` complex. -/
def pdABDiffLMR (X : TopCat) (A B : Set X) (n : ℕ) :
    (pdABKernR (R := R) X A B n) →ₗ[R] (pdABKernR (R := R) X A B (n+1)) :=
  (((singularCochainComplex R X).d n (n+1)).hom.comp
      (Submodule.subtype (pdABKernR (R := R) X A B n))).codRestrict
    (pdABKernR (R := R) X A B (n+1))
    (fun x => Submodule.mem_inf.mpr
      ⟨relKern_d_memR X A n x.1 (Submodule.mem_inf.mp x.2).1,
       relKern_d_memR X B n x.1 (Submodule.mem_inf.mp x.2).2⟩)

@[simp] theorem pdABDiffLMR_coe (X : TopCat) (A B : Set X) (n : ℕ)
    (x : pdABKernR (R := R) X A B n) :
    (pdABDiffLMR X A B n x).1 = ((singularCochainComplex R X).d n (n+1)).hom x.1 := rfl

/-- The differential of the `A+B` complex, as a morphism of modules. -/
def pdABDiffR (X : TopCat) (A B : Set X) (n : ℕ) :
    ModuleCat.of R (pdABKernR (R := R) X A B n) ⟶
      ModuleCat.of R (pdABKernR (R := R) X A B (n+1)) :=
  ModuleCat.ofHom (pdABDiffLMR X A B n)

/-- **The `A+B` cochain complex** `C^*(X, A+B) = C^*(X,A) ∩ C^*(X,B)`. -/
def pdABCohR (X : TopCat) (A B : Set X) : CochainComplex (ModuleCat R) ℕ :=
  CochainComplex.of (fun n => ModuleCat.of R (pdABKernR (R := R) X A B n))
    (fun n => pdABDiffR X A B n)
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero, LinearMap.zero_apply,
        Submodule.coe_zero]
      show ((pdABDiffLMR X A B (n+1)) ((pdABDiffLMR X A B n) x)).1 = 0
      rw [pdABDiffLMR_coe, pdABDiffLMR_coe]
      have h := congrArg ModuleCat.Hom.hom
        (HomologicalComplex.d_comp_d (singularCochainComplex R X) n (n+1) (n+2))
      rw [ModuleCat.hom_comp, ModuleCat.hom_zero] at h
      have h2 := LinearMap.congr_fun h x.1
      simp only [LinearMap.comp_apply, LinearMap.zero_apply] at h2
      exact h2)

@[simp] theorem pdABCohR_d (X : TopCat) (A B : Set X) (n : ℕ) :
    (pdABCohR (R := R) X A B).d n (n+1) = pdABDiffR X A B n :=
  CochainComplex.of_d (fun n => ModuleCat.of R (pdABKernR (R:=R) X A B n)) (fun n => pdABDiffR X A B n) n

theorem pdABCohR_d_coe (X : TopCat) (A B : Set X) (n : ℕ)
    (x : (pdABCohR (R := R) X A B).X n) :
    (((pdABCohR (R := R) X A B).d n (n+1)).hom x).1 =
      ((singularCochainComplex R X).d n (n+1)).hom x.1 := by
  rw [pdABCohR_d]; rfl

/-- The inclusion `C^*(X,A+B) ⟶ C^*(X)`. -/
def pdABInclL (X : TopCat) (A B : Set X) :
    pdABCohR (R := R) X A B ⟶ singularCochainComplex R X :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (Submodule.subtype (pdABKernR X A B n)))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
      rw [pdABCohR_d]
      rfl)

/-- **The inclusion `C^*(X, A∪B) ⟶ C^*(X, A+B)`.** -/
def pdABInclRelR (X : TopCat) (A B : Set X) :
    relComplex R X (A ∪ B) ⟶ pdABCohR (R := R) X A B :=
  CochainComplex.ofHom
    (fun n => ModuleCat.ofHom (Submodule.inclusion
      (le_inf (relKern_mono (R := R) (Set.subset_union_left : A ⊆ A ∪ B))
              (relKern_mono (R := R) (Set.subset_union_right : B ⊆ A ∪ B)))))
    (fun n => by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply,
        relComplex_d, pdABCohR_d]
      rfl)

end

end Work.Whitney

namespace Work.Whitney
open Work.Cohomology

noncomputable section
open CategoryTheory AlgebraicTopology CategoryTheory.Limits

variable {R : Type} [CommRing R]

/-- Transporting along an equality of degrees commutes with the underlying cochain, for the
`A+B` complex. -/
lemma eqRec_pdABKernR_coe (X : TopCat) (A B : Set X) {p q : ℕ} (h : p = q)
    (x : pdABKernR (R := R) X A B p) :
    (h ▸ x).1 = h ▸ x.1 := by
  cases h; rfl

/-- **The Alexander–Whitney product of a relative `A`-cochain and a relative `B`-cochain**, as an
element of the `A+B` complex. -/
noncomputable def starAB (X : TopCat) (A B : Set X) (m n : ℕ) :
    (relComplex R X A).X m →ₗ[R] (relComplex R X B).X n →ₗ[R]
      (pdABCohR (R := R) X A B).X (m + n) where
  toFun a :=
    { toFun := fun b => ⟨cup R (TopCat.toSSet.obj X) a.1 b.1,
        Submodule.mem_inf.mpr ⟨cup_mem_relKern_left R X A a.2 b.1,
          cup_mem_relKern_right R X B a.1 b.2⟩⟩
      map_add' := fun b b' => by
        apply Subtype.ext
        simp only [Submodule.coe_add]
        exact (cupBilinear R (TopCat.toSSet.obj X) m n).2.2.1 a.1 b.1 b'.1
      map_smul' := fun c b => by
        apply Subtype.ext
        simp only [Submodule.coe_smul]
        exact (cupBilinear R (TopCat.toSSet.obj X) m n).2.2.2 c a.1 b.1 }
  map_add' := fun a a' => by
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    simp only [LinearMap.add_apply, Submodule.coe_add]
    exact (cupBilinear R (TopCat.toSSet.obj X) m n).1 a.1 a'.1 b.1
  map_smul' := fun c a => by
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    simp only [LinearMap.smul_apply, Submodule.coe_smul]
    exact (cupBilinear R (TopCat.toSSet.obj X) m n).2.1 c a.1 b.1

@[simp] lemma starAB_coe (X : TopCat) (A B : Set X) (m n : ℕ)
    (a : (relComplex R X A).X m) (b : (relComplex R X B).X n) :
    (starAB X A B m n a b).1 = cup R (TopCat.toSSet.obj X) a.1 b.1 := rfl

/-- The underlying cochain of the differential of the relative complex. -/
lemma relComplex_d_coe' (X : TopCat) (A : Set X) (m : ℕ) (a : (relComplex R X A).X m) :
    ((((relComplex R X A).d m (m+1)) a).1 : (singularCochainComplex R X).X (m+1))
      = ((singularCochainComplex R X).d m (m+1)).hom a.1 := by
  simp only [relComplex_d, relDiff, ModuleCat.hom_ofHom]
  exact relDiffLM_coe R X A m a

set_option maxHeartbeats 1000000 in
/-- **The Leibniz rule** for `starAB`. -/
theorem Leibniz3_starAB (X : TopCat) (A B : Set X) :
    ThreeCup.Leibniz3 (relComplex R X A) (relComplex R X B)
      (pdABCohR (R := R) X A B) (starAB (R := R) X A B) := by
  intro m n a b
  apply Subtype.ext
  rw [pdABCohR_d_coe, starAB_coe]
  rw [Submodule.coe_add, Submodule.coe_smul]
  rw [eqRec_pdABKernR_coe, starAB_coe, starAB_coe]
  rw [relComplex_d_coe', relComplex_d_coe']
  simp only [singularCochain_d_apply]
  exact cupLeibniz R (TopCat.toSSet.obj X) a.1 b.1

end

end Work.Whitney

namespace Work.Whitney
open Work.Cohomology

noncomputable section
open CategoryTheory AlgebraicTopology CategoryTheory.Limits

variable {R : Type} [CommRing R]

/-- The relative-relative cup product on cohomology, from the abstract three-complex descent. -/
noncomputable def relRelCupHMap (X : TopCat) (A B : Set X) (m n : ℕ) :
    (relComplex R X A).homology m →ₗ[R] (relComplex R X B).homology n →ₗ[R]
      (pdABCohR (R := R) X A B).homology (m + n) :=
  (Classical.choose (ThreeCup.exists_cup3_of_generic (relComplex R X A) (relComplex R X B)
    (pdABCohR (R := R) X A B) (starAB (R := R) X A B) (Leibniz3_starAB X A B))) m n

theorem relRelCupHMap_apply (X : TopCat) (A B : Set X) (m n : ℕ)
    (a : (relComplex R X A).X m) (b : (relComplex R X B).X n)
    (ha : (relComplex R X A).d m (m + 1) a = 0) (hb : (relComplex R X B).d n (n + 1) b = 0)
    (h : (pdABCohR (R := R) X A B).d (m + n) (m + n + 1)
      (starAB (R := R) X A B m n a b) = 0) :
    relRelCupHMap (R := R) X A B m n
        (((relComplex R X A).homologyπ m).hom (cocycleOfK (relComplex R X A) a ha))
        (((relComplex R X B).homologyπ n).hom (cocycleOfK (relComplex R X B) b hb)) =
      ((pdABCohR (R := R) X A B).homologyπ (m + n)).hom
        (cocycleOfK (pdABCohR (R := R) X A B) (starAB (R := R) X A B m n a b) h) :=
  Classical.choose_spec (ThreeCup.exists_cup3_of_generic (relComplex R X A) (relComplex R X B)
    (pdABCohR (R := R) X A B) (starAB (R := R) X A B) (Leibniz3_starAB X A B)) m n a b ha hb h

end
end Work.Whitney

namespace Work.Whitney
open Work.Cohomology

noncomputable section
open CategoryTheory AlgebraicTopology CategoryTheory.Limits

variable {R : Type} [CommRing R]

lemma relIncl_eq_pdABInclRelR_comp (X : TopCat) (A B : Set X) :
    relIncl R X (A ∪ B) = pdABInclRelR (R := R) X A B ≫ pdABInclL (R := R) X A B := by
  apply HomologicalComplex.hom_ext
  intro k
  rw [HomologicalComplex.comp_f]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  rfl

lemma pdABKernR_cochainDiff_zero (X : TopCat) (A B : Set X) {k : ℕ}
    (γ : (pdABCohR (R := R) X A B).X k)
    (hγ : ((pdABCohR (R := R) X A B).d k (k + 1)).hom γ = 0) :
    cochainDiff R (TopCat.toSSet.obj X) γ.1 = 0 := by
  have h := congrArg Subtype.val hγ
  rw [pdABCohR_d_coe, Submodule.coe_zero] at h
  rwa [singularCochain_d_apply] at h

/-- The underlying element of `cyclesMap` on a cycle. -/
lemma cyclesMap_i_apply_gen {K L : CochainComplex (ModuleCat R) ℕ} (φ : K ⟶ L) (i : ℕ)
    (z : K.cycles i) :
    (L.iCycles i).hom ((HomologicalComplex.cyclesMap φ i).hom z) =
      (φ.f i).hom ((K.iCycles i).hom z) := by
  have h := congrArg (fun (g : K.cycles i ⟶ L.X i) => g.hom z)
    (HomologicalComplex.cyclesMap_i φ i)
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h
  exact h

lemma pdABInclL_homologyMap_cocycleOfK (X : TopCat) (A B : Set X) {k : ℕ}
    (γ : (pdABCohR (R := R) X A B).X k)
    (hγ : ((pdABCohR (R := R) X A B).d k (k + 1)).hom γ = 0) :
    (HomologicalComplex.homologyMap (pdABInclL (R := R) X A B) k).hom
        (((pdABCohR (R := R) X A B).homologyπ k).hom
          (cocycleOfK (pdABCohR (R := R) X A B) γ hγ))
      = cohomologyClassOf R (TopCat.toSSet.obj X) γ.1
          (pdABKernR_cochainDiff_zero X A B γ hγ) := by
  rw [cohomologyClassOf_eq_homologyπ_cocycleOfK R (TopCat.toSSet.obj X) γ.1
      (pdABKernR_cochainDiff_zero X A B γ hγ) (by
        rw [SSetCochainComplex_d_hom]; exact pdABKernR_cochainDiff_zero X A B γ hγ)]
  change (HomologicalComplex.homologyMap (pdABInclL (R := R) X A B) k).hom
        (((pdABCohR (R := R) X A B).homologyπ k).hom
          (cocycleOfK (pdABCohR (R := R) X A B) γ hγ))
      = ((singularCochainComplex R X).homologyπ k).hom
          (cocycleOfK (singularCochainComplex R X) γ.1 _)
  rw [homologyMap_homologyπ]
  apply congrArg ((singularCochainComplex R X).homologyπ k).hom
  apply iCycles_injective_K (singularCochainComplex R X) k
  rw [cyclesMap_i_apply_gen (pdABInclL (R := R) X A B) k
      (cocycleOfK (pdABCohR (R := R) X A B) γ hγ),
    iCycles_cocycleOfK (pdABCohR (R := R) X A B) γ hγ,
    iCycles_cocycleOfK (singularCochainComplex R X) γ.1 _]
  rfl

end
end Work.Whitney

namespace Work.Whitney
open Work.Cohomology

noncomputable section
open CategoryTheory AlgebraicTopology CategoryTheory.Limits

variable {R : Type} [CommRing R]

theorem exists_relRelCup_of_quasiIso (X : TopCat) (A B : Set X)
    (hIso : ∀ N, IsIso (HomologicalComplex.homologyMap (pdABInclRelR (R := R) X A B) N))
    (m n : ℕ) :
    ∃ cup : (relComplex R X A).homology m →ₗ[R] (relComplex R X B).homology n →ₗ[R]
        (relComplex R X (A ∪ B)).homology (m + n),
      (∀ (a : (relComplex R X A).homology m) (b : (relComplex R X B).homology n),
        (HomologicalComplex.homologyMap (relIncl R X (A ∪ B)) (m + n)).hom (cup a b)
          = cupH' R (TopCat.toSSet.obj X) m n
              ((HomologicalComplex.homologyMap (relIncl R X A) m).hom a)
              ((HomologicalComplex.homologyMap (relIncl R X B) n).hom b)) := by
  let φ : (relComplex R X (A ∪ B)).homology (m + n) ⟶
      (pdABCohR (R := R) X A B).homology (m + n) :=
    HomologicalComplex.homologyMap (pdABInclRelR (R := R) X A B) (m + n)
  haveI : IsIso φ := hIso (m + n)
  let g : (pdABCohR (R := R) X A B).homology (m + n) ⟶
      (relComplex R X (A ∪ B)).homology (m + n) := CategoryTheory.inv φ
  have hgapply : ∀ y, φ.hom (g.hom y) = y := by
    intro y
    show φ.hom ((CategoryTheory.inv φ).hom y) = y
    exact IsIso.inv_hom_id_apply φ y
  have hrel : (HomologicalComplex.homologyMap (relIncl R X (A ∪ B)) (m + n))
      = HomologicalComplex.homologyMap (pdABInclRelR (R := R) X A B) (m + n)
        ≫ HomologicalComplex.homologyMap (pdABInclL (R := R) X A B) (m + n) := by
    rw [← HomologicalComplex.homologyMap_comp, relIncl_eq_pdABInclRelR_comp]
  refine ⟨{ toFun := fun a => (g.hom).comp (relRelCupHMap (R := R) X A B m n a),
            map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro a a'
    ext b
    simp only [LinearMap.add_apply, LinearMap.comp_apply, map_add]
  · intro c a
    ext b
    simp only [LinearMap.smul_apply, LinearMap.comp_apply, map_smul, RingHom.id_apply]
  · intro a b
    obtain ⟨α, hα, rfl⟩ := exists_relClassOf R X A m a
    obtain ⟨β, hβ, rfl⟩ := exists_relClassOf R X B n b
    change (HomologicalComplex.homologyMap (relIncl R X (A ∪ B)) (m + n)).hom
        (g.hom (relRelCupHMap (R := R) X A B m n
          (relClassOf R X A α hα) (relClassOf R X B β hβ)))
      = cupH' R (TopCat.toSSet.obj X) m n
          ((HomologicalComplex.homologyMap (relIncl R X A) m).hom (relClassOf R X A α hα))
          ((HomologicalComplex.homologyMap (relIncl R X B) n).hom (relClassOf R X B β hβ))
    have hα' : ((relComplex R X A).d m (m + 1)).hom α = 0 := by
      rw [relComplex_d_apply]; exact hα
    have hβ' : ((relComplex R X B).d n (n + 1)).hom β = 0 := by
      rw [relComplex_d_apply]; exact hβ
    have hstar : ((pdABCohR (R := R) X A B).d (m + n) (m + n + 1))
        (starAB (R := R) X A B m n α β) = 0 :=
      ThreeCup.star3_cocycle_cochain (Leibniz3_starAB X A B) m n α β hα' hβ'
    rw [relIncl_homologyMap_relClassOf R X A α hα,
        relIncl_homologyMap_relClassOf R X B β hβ]
    rw [cupH'_apply' R (TopCat.toSSet.obj X) α.1 β.1 _ _]
    rw [relClassOf_eq_homologyπ_cocycleOfK R X A α hα hα',
        relClassOf_eq_homologyπ_cocycleOfK R X B β hβ hβ']
    rw [relRelCupHMap_apply (R := R) X A B m n α β hα' hβ' hstar]
    rw [show (HomologicalComplex.homologyMap (relIncl R X (A ∪ B)) (m + n)).hom
          (g.hom (((pdABCohR (R := R) X A B).homologyπ (m + n)).hom
            (cocycleOfK (pdABCohR (R := R) X A B) (starAB (R := R) X A B m n α β) hstar)))
        = (HomologicalComplex.homologyMap (pdABInclL (R := R) X A B) (m + n)).hom
            (((pdABCohR (R := R) X A B).homologyπ (m + n)).hom
              (cocycleOfK (pdABCohR (R := R) X A B) (starAB (R := R) X A B m n α β) hstar)) from by
      rw [hrel]
      simp only [ModuleCat.hom_comp, LinearMap.comp_apply]
      rw [hgapply]]
    rw [pdABInclL_homologyMap_cocycleOfK X A B (starAB (R := R) X A B m n α β) hstar]
    exact cohomologyClassOf_congr R (TopCat.toSSet.obj X)
      (starAB_coe (R := R) X A B m n α β) _ _

end
end Work.Whitney
