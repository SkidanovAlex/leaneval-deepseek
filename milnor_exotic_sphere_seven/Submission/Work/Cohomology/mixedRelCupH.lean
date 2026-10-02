import Mathlib
import Submission.Work.Cohomology.RelCup
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.relCupH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The cup product of an absolute class with a relative class

For a topological space `X`, a subset `A ⊆ X` and a commutative ring `R`, we construct the pairing

  `H^m(X;R) × H^n(X,A;R) ⟶ H^{m+n}(X,A;R)`

which on the classes of cocycles `a ∈ C^m(X;R)` and `b ∈ C^n(X,A;R)` is the class of the
Alexander–Whitney product `a ⌣ b` (which is automatically relative, since `b` vanishes on `A`).
This is the module structure of the relative cohomology `H^*(X,A;R)` over the ring `H^*(X;R)`.

The only thing the descent needs is that the product `⋆ : K^m × L^n → L^{m+n}` is bilinear and
satisfies the Leibniz rule `δ(a ⋆ b) = (δa) ⋆ b + (-1)^m · a ⋆ (δb)`, where the differential on the
left is that of `L`.  Because the second variable takes its values in `L` (where the product lands),
the descent argument is carried out in two steps: first in the second variable (a boundary in `L`
is killed, by the Leibniz rule with the first variable a cocycle), giving a map
`K.cycles m ⟶ (L.homology n ⟶ L.homology (m+n))`; then in the first variable (a boundary in `K`
is killed, by the Leibniz rule with the second variable a cocycle).  The resulting abstract theorem
is `exists_mixedCup_of_generic`, and the requested statement is its instantiation to the mixed
product `mixedRelStar` on the absolute/relative singular cochains of `(X,A)`.
-/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits

namespace Work.Cohomology

noncomputable section

/-! ## The abstract mixed descent -/

section MixedGeneric

variable {R : Type} [CommRing R]

/-- The Leibniz rule for a bilinear pairing `star : K.X m × L.X n → L.X (m+n)` of two cochain
complexes, with values in the second one:

  `δ(a ⋆ b) = (δa) ⋆ b + (-1)^m · a ⋆ (δb)`,

where `δ` denotes the differential of `L` and `δa` the differential of `K`. -/
def MixedLeibniz (K L : CochainComplex (ModuleCat R) ℕ)
    (star : ∀ m n : ℕ, K.X m →ₗ[R] L.X n →ₗ[R] L.X (m + n)) : Prop :=
  ∀ {m n : ℕ} (a : K.X m) (b : L.X n),
    (L.d (m + n) (m + n + 1)).hom (star m n a b) =
      (Nat.add_right_comm m 1 n ▸ star (m + 1) n ((K.d m (m + 1)).hom a) b) +
      ((-1 : R) ^ m) • star m (n + 1) a ((L.d n (n + 1)).hom b)

variable {K L : CochainComplex (ModuleCat R) ℕ}
variable {star : ∀ m n : ℕ, K.X m →ₗ[R] L.X n →ₗ[R] L.X (m + n)}

/-! ### Bilinearity of `star` -/

lemma mstar_add_left (m n : ℕ) (a a' : K.X m) (b : L.X n) :
    star m n (a + a') b = star m n a b + star m n a' b := by
  rw [map_add, LinearMap.add_apply]

lemma mstar_smul_left (m n : ℕ) (c : R) (a : K.X m) (b : L.X n) :
    star m n (c • a) b = c • star m n a b := by
  rw [map_smul, LinearMap.smul_apply]

lemma mstar_zero_left (m n : ℕ) (b : L.X n) : star m n 0 b = 0 := by
  rw [map_zero, LinearMap.zero_apply]

lemma mstar_add_right (m n : ℕ) (a : K.X m) (b b' : L.X n) :
    star m n a (b + b') = star m n a b + star m n a b' :=
  map_add (star m n a) b b'

lemma mstar_smul_right (m n : ℕ) (c : R) (a : K.X m) (b : L.X n) :
    star m n a (c • b) = c • star m n a b :=
  map_smul (star m n a) c b

lemma mstar_zero_right (m n : ℕ) (a : K.X m) : star m n a 0 = 0 :=
  map_zero (star m n a)

/-! ### The Leibniz rule, right and left -/

/-- Leibniz rule in the second variable: for a cocycle `a` of degree `m` in `K` and an arbitrary
cochain `x` of degree `n` in `L`, `δ(a ⋆ x) = (-1)^m · a ⋆ δx`. -/
lemma mstar_leibniz_right (hleib : MixedLeibniz K L star) (m n : ℕ) (a : K.X m)
    (ha : (K.d m (m + 1)).hom a = 0) (x : L.X n) :
    (L.d (m + n) (m + (n + 1))).hom (star m n a x) =
      ((-1 : R) ^ m) • star m (n + 1) a ((L.d n (n + 1)).hom x) := by
  have h : (L.d (m + n) (m + n + 1)).hom (star m n a x) =
      ((-1 : R) ^ m) • star m (n + 1) a ((L.d n (n + 1)).hom x) := by
    have h0 := hleib a x
    rw [ha, mstar_zero_left, eqRec_zero_K, zero_add] at h0
    exact h0
  exact h

/-- Leibniz rule in the first variable: for an arbitrary cochain `x` of degree `m` in `K` and a
cocycle `b` of degree `n` in `L`, `δ(x ⋆ b) = δx ⋆ b`. -/
lemma mstar_leibniz_left (hleib : MixedLeibniz K L star) (m n : ℕ) (x : K.X m) (b : L.X n)
    (hb : (L.d n (n + 1)).hom b = 0) :
    (L.d (m + n) ((m + 1) + n)).hom (star m n x b) =
      star (m + 1) n ((K.d m (m + 1)).hom x) b := by
  have hh : (m + 1) + n = m + n + 1 := Nat.add_right_comm m 1 n
  set γ : L.X ((m + 1) + n) := star (m + 1) n ((K.d m (m + 1)).hom x) b with hγ
  have h : (L.d (m + n) (m + n + 1)).hom (star m n x b) = hh ▸ γ := by
    have h0 := hleib x b
    rw [hb, mstar_zero_right, smul_zero, add_zero] at h0
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

/-! ### The product of two cocycles -/

/-- The product of a cocycle of `K` and a cocycle of `L` is a cocycle of `L`. -/
lemma mstar_cocycle_cochain (hleib : MixedLeibniz K L star) (m n : ℕ) (a : K.X m) (b : L.X n)
    (ha : (K.d m (m + 1)).hom a = 0) (hb : (L.d n (n + 1)).hom b = 0) :
    (L.d (m + n) (m + n + 1)).hom (star m n a b) = 0 := by
  have h := hleib a b
  rw [ha, hb, mstar_zero_left, mstar_zero_right, smul_zero, add_zero, eqRec_zero_K] at h
  exact h

/-- The product of two cycles, as a cycle of `L`. -/
noncomputable def mcupZK (hleib : MixedLeibniz K L star) (m n : ℕ)
    (z : K.cycles m) (w : L.cycles n) : L.cycles (m + n) :=
  cocycleOfK L (star m n ((K.iCycles m).hom z) ((L.iCycles n).hom w))
    (mstar_cocycle_cochain hleib m n _ _ (iCycles_d_apply_K K m z) (iCycles_d_apply_K L n w))

/-- The underlying cochain of a product of cycles. -/
lemma iCycles_mcupZK (hleib : MixedLeibniz K L star) (m n : ℕ)
    (z : K.cycles m) (w : L.cycles n) :
    (L.iCycles (m + n)).hom (mcupZK hleib m n z w) =
      star m n ((K.iCycles m).hom z) ((L.iCycles n).hom w) :=
  iCycles_cocycleOfK L _ _

lemma mcupZK_add_left (hleib : MixedLeibniz K L star) (m n : ℕ)
    (z z' : K.cycles m) (w : L.cycles n) :
    mcupZK hleib m n (z + z') w = mcupZK hleib m n z w + mcupZK hleib m n z' w := by
  apply iCycles_injective_K L (m + n)
  rw [iCycles_add_K, iCycles_mcupZK, iCycles_add_K, iCycles_mcupZK, iCycles_mcupZK]
  exact mstar_add_left m n _ _ _

lemma mcupZK_smul_left (hleib : MixedLeibniz K L star) (m n : ℕ) (a : R)
    (z : K.cycles m) (w : L.cycles n) :
    mcupZK hleib m n (a • z) w = a • mcupZK hleib m n z w := by
  apply iCycles_injective_K L (m + n)
  rw [iCycles_smul_K, iCycles_mcupZK, iCycles_smul_K, iCycles_mcupZK]
  exact mstar_smul_left m n a _ _

lemma mcupZK_add_right (hleib : MixedLeibniz K L star) (m n : ℕ)
    (z : K.cycles m) (w w' : L.cycles n) :
    mcupZK hleib m n z (w + w') = mcupZK hleib m n z w + mcupZK hleib m n z w' := by
  apply iCycles_injective_K L (m + n)
  rw [iCycles_add_K, iCycles_mcupZK, iCycles_add_K, iCycles_mcupZK, iCycles_mcupZK]
  exact mstar_add_right m n _ _ _

lemma mcupZK_smul_right (hleib : MixedLeibniz K L star) (m n : ℕ) (a : R)
    (z : K.cycles m) (w : L.cycles n) :
    mcupZK hleib m n z (a • w) = a • mcupZK hleib m n z w := by
  apply iCycles_injective_K L (m + n)
  rw [iCycles_smul_K, iCycles_mcupZK, iCycles_smul_K, iCycles_mcupZK]
  exact mstar_smul_right m n a _ _

/-- The product with a fixed cycle of `K`, as a linear map on the cycles of `L`. -/
noncomputable def mcupZWK (hleib : MixedLeibniz K L star) (m n : ℕ) (z : K.cycles m) :
    L.cycles n →ₗ[R] L.cycles (m + n) where
  toFun w := mcupZK hleib m n z w
  map_add' := mcupZK_add_right hleib m n z
  map_smul' := fun a w => mcupZK_smul_right hleib m n a z w

/-! ### Descent in the second variable -/

/-- The map on cycles `w ↦ [a ⋆ w]`, where `a = iCycles z`. -/
noncomputable def chiWK (hleib : MixedLeibniz K L star) (m n : ℕ) (z : K.cycles m) :
    L.cycles n ⟶ L.homology (m + n) :=
  ModuleCat.ofHom (((L.homologyπ (m + n)).hom).comp (mcupZWK hleib m n z))

lemma chiWK_apply (hleib : MixedLeibniz K L star) (m n : ℕ) (z : K.cycles m) (w : L.cycles n) :
    (chiWK hleib m n z).hom w = (L.homologyπ (m + n)).hom (mcupZK hleib m n z w) := rfl

/-- A boundary in the second variable is killed by `chiWK`. -/
lemma toCycles_chiWK (hleib : MixedLeibniz K L star) (m n : ℕ) (z : K.cycles m) :
    L.toCycles ((ComplexShape.up ℕ).prev n) n ≫ chiWK hleib m n z = 0 := by
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
    have hchain : (L.iCycles (n' + 1)).hom ((L.toCycles n' (n' + 1)).hom x) =
        (L.d n' (n' + 1)).hom x :=
      iCycles_toCycles_K L n' (n' + 1) x
    have hZ : (chiWK hleib m (n' + 1) z).hom ((L.toCycles n' (n' + 1)).hom x) = 0 := by
      rw [chiWK_apply]
      refine homologyπ_eq_zero_of_d_K L (m + (n' + 1)) (m + n')
        (mcupZK hleib m (n' + 1) z ((L.toCycles n' (n' + 1)).hom x))
        (((-1 : R) ^ m) • star m n' ((K.iCycles m).hom z) x) ?_
      rw [iCycles_mcupZK, hchain, map_smul]
      rw [mstar_leibniz_right hleib m n' ((K.iCycles m).hom z)
          (iCycles_d_apply_K K m z) x,
        smul_smul, neg_one_pow_mul_self, one_smul]
    simpa using hZ

/-- The underlying linear map of the second descent: `[w] ↦ [a ⋆ w]`. -/
noncomputable def PsiFunK (hleib : MixedLeibniz K L star) (m n : ℕ) (z : K.cycles m) :
    L.homology n →ₗ[R] L.homology (m + n) :=
  (descH_K L n (chiWK hleib m n z) (toCycles_chiWK hleib m n z)).hom

lemma PsiFunK_apply (hleib : MixedLeibniz K L star) (m n : ℕ) (z : K.cycles m)
    (w : L.cycles n) :
    PsiFunK hleib m n z ((L.homologyπ n).hom w) = (chiWK hleib m n z).hom w :=
  descH_apply_K L _ _ w

lemma PsiFunK_add (hleib : MixedLeibniz K L star) (m n : ℕ) (z z' : K.cycles m) :
    PsiFunK hleib m n (z + z') = PsiFunK hleib m n z + PsiFunK hleib m n z' := by
  apply LinearMap.ext
  intro y
  obtain ⟨w, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((L.homologyπ n))).mp inferInstance y
  rw [LinearMap.add_apply, PsiFunK_apply, PsiFunK_apply, PsiFunK_apply, chiWK_apply, chiWK_apply,
    chiWK_apply, mcupZK_add_left, homologyπ_add_K]

lemma PsiFunK_smul (hleib : MixedLeibniz K L star) (m n : ℕ) (a : R) (z : K.cycles m) :
    PsiFunK hleib m n (a • z) = a • PsiFunK hleib m n z := by
  apply LinearMap.ext
  intro y
  obtain ⟨w, rfl⟩ :=
    (ModuleCat.epi_iff_surjective ((L.homologyπ n))).mp inferInstance y
  rw [LinearMap.smul_apply, PsiFunK_apply, PsiFunK_apply, chiWK_apply, chiWK_apply,
    mcupZK_smul_left, homologyπ_smul_K]

/-- Descent in the second variable. -/
noncomputable def PsiK (hleib : MixedLeibniz K L star) (m n : ℕ) :
    K.cycles m →ₗ[R] (L.homology n →ₗ[R] L.homology (m + n)) where
  toFun := PsiFunK hleib m n
  map_add' := PsiFunK_add hleib m n
  map_smul' := PsiFunK_smul hleib m n

lemma PsiK_apply (hleib : MixedLeibniz K L star) (m n : ℕ) (z : K.cycles m) (w : L.cycles n) :
    PsiK hleib m n z ((L.homologyπ n).hom w) = (chiWK hleib m n z).hom w :=
  PsiFunK_apply hleib m n z w

/-! ### Descent in the first variable -/

/-- A boundary in the first variable is killed by `PsiK`. -/
lemma toCycles_PsiK (hleib : MixedLeibniz K L star) (m n : ℕ) :
    K.toCycles ((ComplexShape.up ℕ).prev m) m ≫ ModuleCat.ofHom (PsiK hleib m n) = 0 := by
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
    have hx : PsiK hleib (m' + 1) n ((K.toCycles m' (m' + 1)).hom x) = 0 := by
      apply LinearMap.ext
      intro y
      obtain ⟨w, rfl⟩ :=
        (ModuleCat.epi_iff_surjective ((L.homologyπ n))).mp inferInstance y
      rw [PsiK_apply, chiWK_apply]
      have hchain : (K.iCycles (m' + 1)).hom ((K.toCycles m' (m' + 1)).hom x) =
          (K.d m' (m' + 1)).hom x :=
        iCycles_toCycles_K K m' (m' + 1) x
      refine homologyπ_eq_zero_of_d_K L ((m' + 1) + n) (m' + n)
        (mcupZK hleib (m' + 1) n ((K.toCycles m' (m' + 1)).hom x) w)
        (star m' n x ((L.iCycles n).hom w)) ?_
      rw [iCycles_mcupZK, hchain]
      exact (mstar_leibniz_left hleib m' n x ((L.iCycles n).hom w)
        (iCycles_d_apply_K L n w)).symm
    simpa using hx

/-- The mixed cup product pairing on the cohomology of `K` and `L`. -/
noncomputable def mixedCupHMapK (hleib : MixedLeibniz K L star) (m n : ℕ) :
    K.homology m ⟶ ModuleCat.of R (L.homology n →ₗ[R] L.homology (m + n)) :=
  descH_K K m (ModuleCat.ofHom (PsiK hleib m n)) (toCycles_PsiK hleib m n)

lemma mixedCupHMapK_apply (hleib : MixedLeibniz K L star) (m n : ℕ) (z : K.cycles m) :
    (mixedCupHMapK hleib m n).hom ((K.homologyπ m).hom z) = PsiK hleib m n z :=
  descH_apply_K K _ _ z

lemma mcupZK_cocycleOfK (hleib : MixedLeibniz K L star) (m n : ℕ) (a : K.X m) (b : L.X n)
    (ha : (K.d m (m + 1)).hom a = 0) (hb : (L.d n (n + 1)).hom b = 0)
    (h : (L.d (m + n) (m + n + 1)).hom (star m n a b) = 0) :
    mcupZK hleib m n (cocycleOfK K a ha) (cocycleOfK L b hb) =
      cocycleOfK L (star m n a b) h := by
  apply iCycles_injective_K L (m + n)
  rw [iCycles_mcupZK, iCycles_cocycleOfK, iCycles_cocycleOfK, iCycles_cocycleOfK]

/-- **The abstract mixed descent.**  A bilinear pairing of two cochain complexes satisfying the
Leibniz rule induces a bilinear pairing of their cohomologies, which on the classes of two cocycles
is the class of their product. -/
theorem exists_mixedCup_of_generic (K L : CochainComplex (ModuleCat R) ℕ)
    (star : ∀ m n : ℕ, K.X m →ₗ[R] L.X n →ₗ[R] L.X (m + n))
    (hleib : MixedLeibniz K L star) :
    ∃ cupH : ∀ m n : ℕ, K.homology m →ₗ[R] L.homology n →ₗ[R] L.homology (m + n),
      ∀ (m n : ℕ) (a : K.X m) (b : L.X n)
        (ha : (K.d m (m + 1)).hom a = 0) (hb : (L.d n (n + 1)).hom b = 0)
        (h : (L.d (m + n) (m + n + 1)).hom (star m n a b) = 0),
        cupH m n ((K.homologyπ m).hom (cocycleOfK K a ha))
                 ((L.homologyπ n).hom (cocycleOfK L b hb)) =
          (L.homologyπ (m + n)).hom (cocycleOfK L (star m n a b) h) := by
  refine ⟨fun m n => (mixedCupHMapK hleib m n).hom, ?_⟩
  intro m n a b ha hb h
  rw [mixedCupHMapK_apply, PsiK_apply, chiWK_apply, mcupZK_cocycleOfK hleib m n a b ha hb h]

end MixedGeneric

/-! ## Instantiation to the absolute/relative singular cochains -/

section Relative

variable (R : Type) [CommRing R] (X : TopCat) (A : Set X)

/-- **The mixed Alexander–Whitney product**: an absolute `m`-cochain cupped with a relative
`n`-cochain is a relative `(m+n)`-cochain (the back face of a simplex lying in `A` lies in `A`). -/
noncomputable def mixedRelStar (m n : ℕ) :
    Cochain R (TopCat.toSSet.obj X) m →ₗ[R] relKern R X A n →ₗ[R] relKern R X A (m + n) where
  toFun a :=
    { toFun := fun b => ⟨cup R (TopCat.toSSet.obj X) a b.1, cup_mem_relKern_right R X A a b.2⟩
      map_add' := fun b b' => by
        apply Subtype.ext
        simp only [Submodule.coe_add]
        exact (cupBilinear R (TopCat.toSSet.obj X) m n).2.2.1 a b.1 b'.1
      map_smul' := fun c b => by
        apply Subtype.ext
        simp only [Submodule.coe_smul]
        exact (cupBilinear R (TopCat.toSSet.obj X) m n).2.2.2 c a b.1 }
  map_add' := fun a a' => by
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    simp only [LinearMap.add_apply, Submodule.coe_add]
    exact (cupBilinear R (TopCat.toSSet.obj X) m n).1 a a' b.1
  map_smul' := fun c a => by
    apply LinearMap.ext
    intro b
    apply Subtype.ext
    simp only [LinearMap.smul_apply, Submodule.coe_smul]
    exact (cupBilinear R (TopCat.toSSet.obj X) m n).2.1 c a b.1

/-- The underlying cochain of a mixed product. -/
@[simp]
lemma mixedRelStar_coe (m n : ℕ) (a : Cochain R (TopCat.toSSet.obj X) m)
    (b : relKern R X A n) :
    (mixedRelStar R X A m n a b).1 = cup R (TopCat.toSSet.obj X) a b.1 := rfl
/-- The differential of the singular cochain complex of a simplicial set on an element is
`cochainDiff`. -/
@[simp]
lemma SSetCochainComplex_d_hom (X : SSet) {n : ℕ} (α : Cochain R X n) :
    ((SSetCochainComplex R X).d n (n + 1)).hom α = cochainDiff R X α := by
  rw [SSetCochainComplex_d]; rfl

set_option maxHeartbeats 1000000 in
/-- **The mixed Leibniz rule**, an instance of the abstract `MixedLeibniz`. -/
lemma mixedLeibniz_mixedRelStar :
    MixedLeibniz (SSetCochainComplex R (TopCat.toSSet.obj X)) (relComplex R X A)
      (mixedRelStar R X A) := by
  intro m n a b
  rw [relComplex_d_apply]
  apply Subtype.ext
  rw [Submodule.coe_add, Submodule.coe_smul, eqRec_relKern_coe R X A]
  erw [relDiffLM_coe]
  erw [mixedRelStar_coe]
  erw [singularCochain_d_apply]
  erw [mixedRelStar_coe]
  erw [SSetCochainComplex_d_hom]
  erw [mixedRelStar_coe]
  erw [relComplex_d_apply]
  erw [relDiffLM_coe]
  erw [singularCochain_d_apply]
  exact cupLeibniz R (TopCat.toSSet.obj X) a b.1

/-- The cohomology class of an absolute cocycle is the generic class of its cycle. -/
lemma cohomologyClassOf_eq_homologyπ_cocycleOfK (X : SSet) {n : ℕ} (α : Cochain R X n)
    (h : cochainDiff R X α = 0) (h' : ((SSetCochainComplex R X).d n (n + 1)).hom α = 0) :
    cohomologyClassOf R X α h =
      ((SSetCochainComplex R X).homologyπ n).hom (cocycleOfK (SSetCochainComplex R X) α h') :=
  rfl

/-- **The cup product of an absolute class with a relative class.**  The relative cohomology
`H^*(X,A;R)` is a module over `H^*(X;R)`; on classes of cocycles it is the Alexander–Whitney
product. -/
theorem mixedRelCupH (R : Type) [CommRing R] (X : TopCat) (A : Set X) :
    ∃ cup : ∀ m n : ℕ, Work.Cohomology.singularCohomology R m X →ₗ[R]
        (Work.Cohomology.relCohomology R X A n →ₗ[R] Work.Cohomology.relCohomology R X A (m + n)),
      ∀ (m n : ℕ) (a : Work.Cohomology.Cochain R (TopCat.toSSet.obj X) m)
        (b : Work.Cohomology.relKern R X A n)
        (ha : Work.Cohomology.cochainDiff R (TopCat.toSSet.obj X) a = 0)
        (hb : Work.Cohomology.relDiffLM R X A n b = 0),
        ∃ (hmem : Work.Cohomology.cup R (TopCat.toSSet.obj X) a
              (b.1 : Work.Cohomology.Cochain R (TopCat.toSSet.obj X) n) ∈
            Work.Cohomology.relKern R X A (m + n)),
          ∃ (h : Work.Cohomology.relDiffLM R X A (m + n)
                ⟨Work.Cohomology.cup R (TopCat.toSSet.obj X) a
                  (b.1 : Work.Cohomology.Cochain R (TopCat.toSSet.obj X) n), hmem⟩ = 0),
            cup m n (Work.Cohomology.cohomologyClassOf R (TopCat.toSSet.obj X) a ha)
                (Work.Cohomology.relClassOf R X A b hb) =
              Work.Cohomology.relClassOf R X A
                ⟨Work.Cohomology.cup R (TopCat.toSSet.obj X) a
                  (b.1 : Work.Cohomology.Cochain R (TopCat.toSSet.obj X) n), hmem⟩ h := by
  obtain ⟨cupH, hcupH⟩ :=
    exists_mixedCup_of_generic (SSetCochainComplex R (TopCat.toSSet.obj X)) (relComplex R X A)
      (mixedRelStar R X A) (mixedLeibniz_mixedRelStar R X A)
  refine ⟨cupH, ?_⟩
  intro m n a b ha hb
  have ha' : ((SSetCochainComplex R (TopCat.toSSet.obj X)).d m (m + 1)).hom a = 0 := by
    rw [SSetCochainComplex_d_hom]; exact ha
  have hb' : ((relComplex R X A).d n (n + 1)).hom b = 0 := by
    rw [relComplex_d_apply]; exact hb
  have h' : ((relComplex R X A).d (m + n) (m + n + 1)).hom (mixedRelStar R X A m n a b) = 0 :=
    mstar_cocycle_cochain (mixedLeibniz_mixedRelStar R X A) m n a b ha' hb'
  let c : relKern R X A (m + n) := mixedRelStar R X A m n a b
  have h2 : relDiffLM R X A (m + n) ⟨cup R (TopCat.toSSet.obj X) a b.1, c.2⟩ = 0 := by
    rw [show (⟨cup R (TopCat.toSSet.obj X) a b.1, c.2⟩ : relKern R X A (m + n)) = c from rfl]
    exact (relComplex_d_apply R X A c).symm.trans h'
  refine ⟨c.2, h2, ?_⟩
  rw [cohomologyClassOf_eq_homologyπ_cocycleOfK R (TopCat.toSSet.obj X) a ha ha',
      relClassOf_eq_homologyπ_cocycleOfK R X A b hb hb']
  refine (hcupH m n a b ha' hb' h').trans ?_
  rw [relClassOf_eq_homologyπ_cocycleOfK R X A
        ⟨cup R (TopCat.toSSet.obj X) a b.1, c.2⟩ h2 h']
  rfl

end Relative

end

end Work.Cohomology
