import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.SSGRoute.prop5Data_exists
import Submission.Work.SSGRoute.gradedPiece_one
import Submission.Work.SSGRoute.two_torsion_lift_two
import Submission.Work.SSGRoute.prop5.pCentralSeries_le_pow_sup_commutator
import Submission.Work.CohomologicalShrinking.nonempty_prop5Data_one_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Work.CohomologicalShrinking

set_option maxHeartbeats 4000000

/-! ## The kernel of `Q_{(i,2)} → Q_{(i,1)}` as the graded piece `E(n,(i,1))` -/

section Transfer

variable {G : Type*} [Group G] (n i : ℕ)

/-- The refined term `F(n)^{(i,1)} = F(n)_i`. -/
noncomputable abbrev stepBase : Subgroup (Work.Shrinking.freeOperatorGroup G n) :=
  flowTerm 2 G n i 1

/-- The next refined term `F(n)^{(i,1)+1}`, i.e. the subgroup defining the kernel of the projection
`Q_{(i,1)+1} → Q_{(i,1)}`. -/
noncomputable abbrev stepSucc : Subgroup (Work.Shrinking.freeOperatorGroup G n) :=
  flowTerm 2 G n (tauSucc i 1).1 (tauSucc i 1).2

theorem stepSucc_le_stepBase : stepSucc (G := G) n i ≤ stepBase (G := G) n i :=
  refinedTerm_tauSucc_le 2 _ i 1

instance : (stepSucc (G := G) n i).Normal := inferInstance

/-- The class of `z ∈ F(n)_i` in the graded piece `E(n,(i,1))`. -/
noncomputable def toE (z : Work.Shrinking.freeOperatorGroup G n)
    (hz : z ∈ stepBase (G := G) n i) : E 2 G n i 1 :=
  Additive.ofMul (QuotientGroup.mk'
    ((stepSucc (G := G) n i).subgroupOf (stepBase (G := G) n i)) ⟨z, hz⟩)

/-- The class of `z ∈ F(n)` in the ambient quotient `Q_i = F(n)/F(n)^{(i,1)+1}`. -/
noncomputable def toQ (z : Work.Shrinking.freeOperatorGroup G n) :
    flowQuotient 2 G n (tauSucc i 1).1 (tauSucc i 1).2 :=
  QuotientGroup.mk' ((stepSucc (G := G) n i).subgroupOf ⊤) ⟨z, Subgroup.mem_top z⟩

@[simp] lemma toQ_one : toQ (G := G) n i 1 =
    (1 : flowQuotient 2 G n (tauSucc i 1).1 (tauSucc i 1).2) := by
  rw [toQ]
  exact map_one _

@[simp] lemma toE_zero : toE (G := G) n i 1 (stepBase (G := G) n i).one_mem = 0 := by
  rw [toE, show (⟨(1 : Work.Shrinking.freeOperatorGroup G n),
      (stepBase (G := G) n i).one_mem⟩ : stepBase (G := G) n i) = 1 from rfl, map_one,
    ofMul_one]

lemma toE_eq_iff {a b : Work.Shrinking.freeOperatorGroup G n}
    (ha : a ∈ stepBase (G := G) n i) (hb : b ∈ stepBase (G := G) n i) :
    toE n i a ha = toE n i b hb ↔ a⁻¹ * b ∈ stepSucc (G := G) n i := by
  rw [toE, toE, Additive.ofMul.injective.eq_iff, QuotientGroup.mk'_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

theorem toE_eq_of_mem_stepSucc {a b : Work.Shrinking.freeOperatorGroup G n}
    (ha : a ∈ stepBase (G := G) n i) (hb : b ∈ stepBase (G := G) n i)
    (h : a⁻¹ * b ∈ stepSucc (G := G) n i) : toE n i a ha = toE n i b hb :=
  (toE_eq_iff n i ha hb).mpr h

lemma toQ_eq_iff {a b : Work.Shrinking.freeOperatorGroup G n} :
    toQ n i a = toQ n i b ↔ a⁻¹ * b ∈ stepSucc (G := G) n i := by
  rw [toQ, toQ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  rfl

lemma toE_mul {a b : Work.Shrinking.freeOperatorGroup G n}
    (ha : a ∈ stepBase (G := G) n i) (hb : b ∈ stepBase (G := G) n i)
    (hab : a * b ∈ stepBase (G := G) n i) :
    toE n i (a * b) hab = toE n i a ha + toE n i b hb := by
  rw [toE, toE, toE]
  have h : QuotientGroup.mk' ((stepSucc (G := G) n i).subgroupOf (stepBase (G := G) n i))
        ⟨a * b, hab⟩
      = QuotientGroup.mk' ((stepSucc (G := G) n i).subgroupOf (stepBase (G := G) n i)) ⟨a, ha⟩
        * QuotientGroup.mk' ((stepSucc (G := G) n i).subgroupOf (stepBase (G := G) n i))
            ⟨b, hb⟩ := by
    rw [show (⟨a * b, hab⟩ : stepBase (G := G) n i) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl]
    exact map_mul _ _ _
  rw [h, ofMul_mul]

lemma toQ_mul (a b : Work.Shrinking.freeOperatorGroup G n) :
    toQ n i (a * b) = toQ n i a * toQ n i b := by
  rw [toQ, toQ, toQ]
  exact map_mul (QuotientGroup.mk' ((stepSucc (G := G) n i).subgroupOf ⊤))
    ⟨a, Subgroup.mem_top a⟩ ⟨b, Subgroup.mem_top b⟩

lemma toQ_pow_two {z : Work.Shrinking.freeOperatorGroup G n}
    (hz : z ∈ stepBase (G := G) n i) : toQ n i z ^ 2 = 1 := by
  have h2 : z ^ 2 ∈ stepSucc (G := G) n i := pow_refinedTerm_le 2 i 1 hz
  have h : toQ n i (z ^ 2) = toQ n i 1 := (toQ_eq_iff n i).mpr (by simpa using h2)
  rw [toQ_one] at h
  calc toQ n i z ^ 2 = toQ n i z * toQ n i z := pow_two (toQ n i z)
    _ = toQ n i (z * z) := (toQ_mul n i z z).symm
    _ = toQ n i (z ^ 2) := by rw [pow_two]
    _ = 1 := h

/-- Every element of the graded piece has order two (it is an elementary abelian `2`-group). -/
lemma E_neg_self (x : E 2 G n i 1) : -x = x := by
  have h : (-1 : ZMod 2) = 1 := by decide
  rw [← neg_one_smul (ZMod 2) x, h, one_smul]

lemma toE_smul (g : G) {z : Work.Shrinking.freeOperatorGroup G n}
    (hz : z ∈ stepBase (G := G) n i) (hgz : g • z ∈ stepBase (G := G) n i) :
    g • toE n i z hz = toE n i (g • z) hgz := by
  rw [toE, toE]
  have hsmul : g • Additive.ofMul (QuotientGroup.mk'
        ((stepSucc (G := G) n i).subgroupOf (stepBase (G := G) n i)) ⟨z, hz⟩)
      = Additive.ofMul (g • (QuotientGroup.mk'
        ((stepSucc (G := G) n i).subgroupOf (stepBase (G := G) n i)) ⟨z, hz⟩ :
          refinedQuotient 2 (Work.Shrinking.freeOperatorGroup G n) i 1)) := rfl
  rw [hsmul]
  have hH : (stepBase (G := G) n i).map
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G n) g).toMonoidHom
      = stepBase (G := G) n i :=
    map_refinedTerm_eq 2 _ i 1
  have hK : (stepSucc (G := G) n i).map
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G n) g).toMonoidHom
      = stepSucc (G := G) n i :=
    map_refinedTerm_eq 2 _ (tauSucc i 1).1 (tauSucc i 1).2
  change Additive.ofMul (Work.Shrinking.quotAut (stepBase (G := G) n i) (stepSucc (G := G) n i)
      g hH hK (QuotientGroup.mk' ((stepSucc (G := G) n i).subgroupOf (stepBase (G := G) n i))
        ⟨z, hz⟩))
    = Additive.ofMul (QuotientGroup.mk' ((stepSucc (G := G) n i).subgroupOf (stepBase (G := G) n i))
        ⟨g • z, hgz⟩)
  rw [Work.Shrinking.quotAut_mk]
  exact congrArg (QuotientGroup.mk' ((stepSucc (G := G) n i).subgroupOf (stepBase (G := G) n i)))
    (Subtype.ext (Work.Shrinking.subAut_coe (stepBase (G := G) n i) g hH ⟨z, hz⟩))

lemma toQ_smul (g : G) (z : Work.Shrinking.freeOperatorGroup G n) :
    flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 g (toQ n i z) = toQ n i (g • z) := by
  rw [toQ, toQ]
  have hP : (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).map
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G n) g).toMonoidHom
      = ⊤ :=
    Subgroup.map_top_of_surjective _ (MulDistribMulAction.toMulAut G _ g).surjective
  have hK : (stepSucc (G := G) n i).map
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G n) g).toMonoidHom
      = stepSucc (G := G) n i :=
    map_refinedTerm_eq 2 _ (tauSucc i 1).1 (tauSucc i 1).2
  change Work.Shrinking.quotAut ⊤ (stepSucc (G := G) n i) g hP hK
      (QuotientGroup.mk' ((stepSucc (G := G) n i).subgroupOf ⊤)
        ⟨z, Subgroup.mem_top z⟩) = _
  rw [Work.Shrinking.quotAut_mk]
  exact congrArg _ (Subtype.ext (Work.Shrinking.subAut_coe (⊤ : Subgroup
    (Work.Shrinking.freeOperatorGroup G n)) g hP ⟨z, Subgroup.mem_top z⟩))

end Transfer

/-! ## The exponent-sum homomorphism and injectivity of the `j = 1` value map

`zetaHom : F(n) →* Multiplicative (Fin n × G → ℤ)` is the exponent-sum (abelianisation)
homomorphism, and `pushHom` is the coordinatewise reduction mod `2`.  The value map
`z ↦ z^{2^{i-1}}` on `F(n)/F(n)^2` is injective because `zetaHom (z^{2^{i-1}}) = 2^{i-1} · zetaHom z`
lies in the image of `F(n)^{(i,1)+1}`, whose coordinates are all divisible by `2^i`. -/

section Crux

open scoped commutatorElement

attribute [local instance] Classical.decEq

variable {G : Type*} [Group G] [Fintype G] (n : ℕ)

/-- The exponent-sum homomorphism `F(n) →* Multiplicative (Fin n × G → ℤ)`. -/
noncomputable def zetaHom (G : Type*) [Group G] (n : ℕ) :
    Work.Shrinking.freeOperatorGroup G n →* Multiplicative (Fin n × G → ℤ) :=
  FreeGroup.lift (fun x => Multiplicative.ofAdd (Pi.single x (1 : ℤ)))

theorem zetaHom_of (x : Fin n × G) :
    zetaHom G n (FreeGroup.of x) = Multiplicative.ofAdd (Pi.single x (1 : ℤ)) :=
  FreeGroup.lift_apply_of

/-- The coordinatewise reduction mod `2` of an exponent vector. -/
noncomputable def pushHom (G : Type*) [Group G] (n : ℕ) :
    Multiplicative (Fin n × G → ℤ) →* Multiplicative (Fin n × G → ZMod 2) where
  toFun f := Multiplicative.ofAdd fun x => ((Multiplicative.toAdd f x : ℤ) : ZMod 2)
  map_one' := by
    show Multiplicative.ofAdd (fun x => ((Multiplicative.toAdd
      (1 : Multiplicative (Fin n × G → ℤ))) x : ZMod 2)) = 1
    rw [toAdd_one]
    rw [show (fun x : Fin n × G => (((0 : Fin n × G → ℤ) x : ℤ) : ZMod 2)) = 0 from by
      funext x; simp, ofAdd_zero]
  map_mul' f g := by
    show Multiplicative.ofAdd (fun x => ((Multiplicative.toAdd (f * g)) x : ZMod 2))
      = Multiplicative.ofAdd (fun x => ((Multiplicative.toAdd f) x : ZMod 2))
        * Multiplicative.ofAdd (fun x => ((Multiplicative.toAdd g) x : ZMod 2))
    rw [toAdd_mul]
    rw [show (fun x : Fin n × G =>
          (((Multiplicative.toAdd f + Multiplicative.toAdd g) x : ℤ) : ZMod 2))
        = (fun x : Fin n × G => ((Multiplicative.toAdd f x : ℤ) : ZMod 2))
          + (fun x : Fin n × G => ((Multiplicative.toAdd g x : ℤ) : ZMod 2)) from by
      funext x; simp [Pi.add_apply], ofAdd_add]

theorem pushHom_ofAdd (v : Fin n × G → ℤ) :
    pushHom G n (Multiplicative.ofAdd v)
      = Multiplicative.ofAdd (fun y => ((v y : ℤ) : ZMod 2)) := rfl

theorem freeToFun_eq_pushHom_zetaHom (z : Work.Shrinking.freeOperatorGroup G n) :
    freeToFun 2 G n z = pushHom G n (zetaHom G n z) := by
  have h : (freeToFun 2 G n) = (pushHom G n).comp (zetaHom G n) := by
    refine FreeGroup.ext_hom _ _ fun x => ?_
    show freeToFun 2 G n (FreeGroup.of x) = pushHom G n (zetaHom G n (FreeGroup.of x))
    rw [zetaHom_of, freeToFun_of, pushHom_ofAdd]
    apply Multiplicative.ofAdd.injective
    funext y
    show ((Pi.single x (1 : ZMod 2) : Fin n × G → ZMod 2) y)
      = (((Pi.single x (1 : ℤ) : Fin n × G → ℤ) y : ℤ) : ZMod 2)
    rw [Pi.single_apply, Pi.single_apply]
    by_cases hy : y = x <;> simp [hy]
  exact congrFun (congrArg DFunLike.coe h) z

theorem freeToFun_eq_one_iff_qmk_eq_zero (z : Work.Shrinking.freeOperatorGroup G n) :
    freeToFun 2 G n z = 1 ↔ prop5.qmk 2 G n z = 0 := by
  classical
  set Z : prop5.Ptop 2 G n := ⟨z, Subgroup.mem_top z⟩ with hZ
  have hfac : quotHom 2 G n (QuotientGroup.mk'
      ((prop5.Pone 2 G n).subgroupOf (prop5.Ptop 2 G n)) Z) = freeToFun 2 G n z := rfl
  have hqmk : prop5.qmk 2 G n z = Additive.ofMul (QuotientGroup.mk'
      ((prop5.Pone 2 G n).subgroupOf (prop5.Ptop 2 G n)) Z) := rfl
  have hinj : Function.Injective (quotHom 2 G n) := by
    intro a b hab
    have h1 : squareQuotientToFun 2 G n (Additive.ofMul a)
        = squareQuotientToFun 2 G n (Additive.ofMul b) := by
      show Multiplicative.toAdd (quotHom 2 G n (Additive.toMul (Additive.ofMul a)))
        = Multiplicative.toAdd (quotHom 2 G n (Additive.toMul (Additive.ofMul b)))
      rw [show Additive.toMul (Additive.ofMul a) = a from rfl,
        show Additive.toMul (Additive.ofMul b) = b from rfl, hab]
    exact Additive.ofMul.injective ((modsquare.squareQuotientToFun_bijective 2 G n).1 h1)
  constructor
  · intro hz
    have h2 : QuotientGroup.mk' ((prop5.Pone 2 G n).subgroupOf (prop5.Ptop 2 G n)) Z = 1 := by
      apply hinj
      rw [hfac, hz, map_one]
    rw [hqmk, h2]
    rfl
  · intro hz
    have h2 : QuotientGroup.mk' ((prop5.Pone 2 G n).subgroupOf (prop5.Ptop 2 G n)) Z = 1 := by
      rw [hqmk] at hz
      exact Additive.ofMul.injective hz
    rw [← hfac, h2, map_one]

/-- The subgroup of exponent vectors all of whose coordinates are divisible by `2^i`. -/
noncomputable def divSub (G : Type*) [Group G] (n i : ℕ) :
    Subgroup (Multiplicative (Fin n × G → ℤ)) where
  carrier := {u | ∀ x : Fin n × G, (2 : ℤ) ^ i ∣ Multiplicative.toAdd u x}
  one_mem' := by intro x; simp
  mul_mem' := by
    intro u v hu hv x
    rw [toAdd_mul, Pi.add_apply]
    exact dvd_add (hu x) (hv x)
  inv_mem' := by
    intro u hu x
    have h : Multiplicative.toAdd u + Multiplicative.toAdd u⁻¹ = 0 := by
      rw [← toAdd_mul, mul_inv_cancel, toAdd_one]
    have h2 : Multiplicative.toAdd u⁻¹ = - Multiplicative.toAdd u :=
      eq_neg_of_add_eq_zero_right h
    rw [h2, Pi.neg_apply]
    exact dvd_neg.mpr (hu x)

/-- `zetaHom` kills commutators (its target is abelian). -/
theorem zetaHom_commutator (a b : Work.Shrinking.freeOperatorGroup G n) :
    zetaHom G n ⁅a, b⁆ = 1 := by
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_commute.mpr (mul_comm _ _)

/-- The derived subgroup `γ₂ = [F,F]` consists of commutators. -/
theorem lowerCentralSeries_one_eq :
    (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries 1
      = ⁅(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)), ⊤⁆ :=
  Subgroup.top_lowerCentralSeries_one

theorem centralSeries_two_eq :
    centralSeries (Work.Shrinking.freeOperatorGroup G n) 2
      = ⁅(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)), ⊤⁆ := by
  rw [show centralSeries (Work.Shrinking.freeOperatorGroup G n) 2
      = ⁅centralSeries (Work.Shrinking.freeOperatorGroup G n) 1, ⊤⁆ from
    centralSeries_succ_succ _ 0, centralSeries_one]

/-- The exponent-sum map sends the `k`-th `p`-central term into the exponent vectors whose
coordinates are divisible by `2^k`. -/
theorem pCentralSeries_le_divSub_comap (k : ℕ) :
    Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G n) k
      ≤ (divSub G n k).comap (zetaHom G n) := by
  induction k with
  | zero => intro u _ x; simp
  | succ k ih =>
      rw [Work.Shrinking.pCentralSeries_succ, Work.Shrinking.pCentralStep]
      refine sup_le ?_ ?_
      · rw [Work.Shrinking.powSubgroup]
        refine (Subgroup.closure_le _).mpr ?_
        rintro u ⟨y, hy, rfl⟩
        intro x
        rw [map_pow, toAdd_pow, Pi.smul_apply, nsmul_eq_mul]
        obtain ⟨d, hd⟩ := ih hy x
        rw [hd]
        push_cast
        refine ⟨d, ?_⟩
        rw [pow_succ]
        ring
      · refine (Subgroup.commutator_le).mpr fun a _ b _ => ?_
        rw [Subgroup.mem_comap, zetaHom_commutator (n := n)]
        intro x; simp

/-- The image of the `j = 1` refined term under the exponent-sum map has coordinates divisible
by `2^i`. -/
theorem refinedTerm_le_divSub_comap (i : ℕ) (hi : 1 ≤ i) :
    refinedTerm 2 (Work.Shrinking.freeOperatorGroup G n)
        (tauSucc i 1).1 (tauSucc i 1).2
      ≤ (divSub G n i).comap (zetaHom G n) := by
  rcases eq_or_lt_of_le hi with h1 | h2
  · subst h1
    show refinedTerm 2 (Work.Shrinking.freeOperatorGroup G n) 2 1 ≤ _
    rw [refinedTerm_one, show pSeries 2 (Work.Shrinking.freeOperatorGroup G n) 2
      = Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G n) 1 from rfl]
    exact pCentralSeries_le_divSub_comap (G := G) n 1
  · have hτ : tauSucc i 1 = (i, 2) := tauSucc_of_lt h2
    rw [hτ, refinedTerm, centralSeries_two_eq]
    refine sup_le ?_ ?_
    · refine le_trans inf_le_right (le_trans ?_ (le_refl _))
      intro u hu
      have hu' : u ∈ ⁅(⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)), ⊤⁆ := hu
      exact (Subgroup.commutator_le.mpr (fun a _ b _ => by
        rw [Subgroup.mem_comap, zetaHom_commutator (n := n)]
        intro x; simp)) hu'
    · show pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (i + 1) ≤ _
      rw [show pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (i + 1)
        = Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G n) i from rfl]
      exact pCentralSeries_le_divSub_comap (G := G) n i

/-- **Injectivity of the `j = 1` value map at `p = 2`.** -/
theorem pow_two_pow_mem_refinedTerm_imp_qmk_eq_zero
    (G : Type*) [Group G] [Fintype G] (n i : ℕ) (hi : 1 ≤ i)
    {z : Work.Shrinking.freeOperatorGroup G n}
    (hz : z ^ (2 ^ (i - 1)) ∈ Work.CohomologicalShrinking.refinedTerm 2
      (Work.Shrinking.freeOperatorGroup G n)
      (Work.CohomologicalShrinking.tauSucc i 1).1
      (Work.CohomologicalShrinking.tauSucc i 1).2) :
    Work.SSGRoute.prop5.qmk 2 G n z = 0 := by
  have hmem : zetaHom G n (z ^ 2 ^ (i - 1)) ∈ divSub G n i :=
    refinedTerm_le_divSub_comap (G := G) n i hi hz
  have hcoord : ∀ x : Fin n × G, (2 : ℤ) ∣ Multiplicative.toAdd (zetaHom G n z) x := by
    intro x
    have h := hmem x
    rw [map_pow, toAdd_pow, Pi.smul_apply, nsmul_eq_mul] at h
    push_cast at h
    have h2 : (2 : ℤ) ^ i = (2 : ℤ) ^ (i - 1) * 2 := by
      rw [← pow_succ]
      congr 1
      omega
    rw [h2, mul_dvd_mul_iff_left (pow_ne_zero _ (by norm_num))] at h
    exact h
  have hpush : freeToFun 2 G n z = 1 := by
    rw [freeToFun_eq_pushHom_zetaHom]
    apply Multiplicative.ofAdd.injective
    funext x
    obtain ⟨d, hd⟩ := hcoord x
    show ((Multiplicative.toAdd (zetaHom G n z) x : ℤ) : ZMod 2) = (0 : ZMod 2)
    rw [hd]
    push_cast
    rw [show (2 : ZMod 2) = 0 from by decide, zero_mul]
  exact (freeToFun_eq_one_iff_qmk_eq_zero (G := G) n z).mp hpush

end Crux



/-! ## The `p`-central series is generated by powers together with `γ₂` (any universe)

The workspace's `Work.SSGRoute.prop5.pCentralSeries_le_pow_sup_commutator` is stated for
`P : Type` (universe `0`); the version below is universe-polymorphic, which is what the present
file needs (`G : Type*`). -/

section Generation

open scoped commutatorElement

variable {P : Type*}

private theorem mul_pow_mul_pow_inv_mem_lcs (n : ℕ) [Group P] (u v : P) :
    (u * v) ^ n * (u ^ n * v ^ n)⁻¹ ∈ (⊤ : Subgroup P).lowerCentralSeries 1 := by
  rw [Subgroup.top_lowerCentralSeries_one, ← Abelianization.ker_of, MonoidHom.mem_ker]
  simp [map_mul, map_pow, mul_pow]

private theorem pow_mem_powSubgroup_sup (p k : ℕ) [Group P] {x : P}
    (hx : x ∈ Work.Shrinking.powSubgroup (p ^ k) (⊤ : Subgroup P)) :
    x ^ p ∈ Work.Shrinking.powSubgroup (p ^ (k + 1)) (⊤ : Subgroup P) ⊔
      (⊤ : Subgroup P).lowerCentralSeries 1 := by
  simp only [Work.Shrinking.powSubgroup] at hx ⊢
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hx
  · rintro z ⟨y, -, rfl⟩
    apply Subgroup.mem_sup_left
    rw [← pow_mul, ← pow_succ]
    exact Subgroup.subset_closure ⟨y, Subgroup.mem_top y, rfl⟩
  · rw [one_pow]
    exact Subgroup.one_mem _
  · intro a b _ _ iha ihb
    have hkey : (a * b) ^ p = ((a * b) ^ p * (a ^ p * b ^ p)⁻¹) * (a ^ p * b ^ p) := by
      group
    rw [hkey]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mul_pow_mul_pow_inv_mem_lcs p a b))
      (Subgroup.mul_mem _ iha ihb)
  · intro a _ iha
    rw [inv_pow]
    exact Subgroup.inv_mem _ iha

private theorem sup_pow_mem (p k : ℕ) [Group P] {x : P}
    (hx : x ∈ Work.Shrinking.powSubgroup (p ^ k) (⊤ : Subgroup P) ⊔
      (⊤ : Subgroup P).lowerCentralSeries 1) :
    x ^ p ∈ Work.Shrinking.powSubgroup (p ^ (k + 1)) (⊤ : Subgroup P) ⊔
      (⊤ : Subgroup P).lowerCentralSeries 1 := by
  set C := Work.Shrinking.powSubgroup (p ^ (k + 1)) (⊤ : Subgroup P) ⊔
    (⊤ : Subgroup P).lowerCentralSeries 1 with hC
  obtain ⟨u, hu, v, hv, huv⟩ :=
    (Subgroup.mem_sup_of_normal_right (s := Work.Shrinking.powSubgroup (p ^ k) (⊤ : Subgroup P))
      (t := (⊤ : Subgroup P).lowerCentralSeries 1)).mp hx
  rw [← huv]
  have hu' : u ^ p ∈ C := pow_mem_powSubgroup_sup p k hu
  have hvC : v ∈ C := Subgroup.mem_sup_right hv
  have hv' : v ^ p ∈ C := Subgroup.pow_mem C hvC p
  have hkey : (u * v) ^ p = ((u * v) ^ p * (u ^ p * v ^ p)⁻¹) * (u ^ p * v ^ p) := by
    group
  rw [hkey]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (mul_pow_mul_pow_inv_mem_lcs p u v))
    (Subgroup.mul_mem _ hu' hv')

private theorem pCentralSeries_le_powSubgroup_sup (p : ℕ) (P : Type*) [Group P] (k : ℕ) :
    Work.Shrinking.pCentralSeries p P k ≤
      Work.Shrinking.powSubgroup (p ^ k) (⊤ : Subgroup P) ⊔
        (⊤ : Subgroup P).lowerCentralSeries 1 := by
  induction k with
  | zero =>
      rw [Work.Shrinking.pCentralSeries_zero]
      intro y _
      apply Subgroup.mem_sup_left
      rw [Work.Shrinking.powSubgroup]
      exact Subgroup.subset_closure ⟨y, Subgroup.mem_top y, by simp⟩
  | succ k ih =>
      rw [Work.Shrinking.pCentralSeries_succ]
      unfold Work.Shrinking.pCentralStep
      apply sup_le
      · rw [Work.Shrinking.powSubgroup]
        rw [Subgroup.closure_le]
        rintro z ⟨y, hy, rfl⟩
        exact sup_pow_mem p k (ih hy)
      · have h : ⁅(⊤ : Subgroup P), ⊤⁆ = (⊤ : Subgroup P).lowerCentralSeries 1 := by
          rw [Subgroup.top_lowerCentralSeries_one, _root_.commutator_def]
        apply le_trans (Subgroup.commutator_mono (le_top) le_rfl)
        rw [h]
        exact le_sup_right

/-- **The `p`-central series lies in `⟨y^{p^{i-1}}⟩·γ₂`**, universe-polymorphic form. -/
theorem pCentralSeries_le_pow_sup_commutator' (p : ℕ) {P : Type*} [Group P] (i : ℕ)
    (hi : 1 ≤ i) :
    Work.Shrinking.pCentralSeries p P (i - 1) ≤
      Subgroup.closure {x : P | ∃ y : P, x = y ^ (p ^ (i - 1))} ⊔
        (⊤ : Subgroup P).lowerCentralSeries 1 := by
  refine le_trans (pCentralSeries_le_powSubgroup_sup p P (i - 1)) ?_
  apply sup_le_sup _ le_rfl
  rw [Work.Shrinking.powSubgroup]
  apply Subgroup.closure_mono
  rintro z ⟨y, -, rfl⟩
  exact ⟨y, rfl⟩

end Generation


/-! ## The `j = 1` value map `θ` as an additive bijection -/

section Theta

variable {G : Type*} [Group G] [Fintype G] (n i : ℕ)

/-- The class of a *bundled* element of `F(n)_i` in the graded piece `E(n,(i,1))`. -/
noncomputable def toE' (z : stepBase (G := G) n i) : E 2 G n i 1 :=
  Additive.ofMul (QuotientGroup.mk' ((stepSucc (G := G) n i).subgroupOf
    (stepBase (G := G) n i)) z)

theorem toE_eq_toE' (z : Work.Shrinking.freeOperatorGroup G n) (hz : z ∈ stepBase (G := G) n i) :
    toE n i z hz = toE' (G := G) n i ⟨z, hz⟩ := rfl

theorem toE'_congr (z w : stepBase (G := G) n i) (h : (z : Work.Shrinking.freeOperatorGroup G n)
    = w) : toE' (G := G) n i z = toE' (G := G) n i w := by
  rw [Subtype.ext h]

theorem toE'_mul (a b : stepBase (G := G) n i) :
    toE' (G := G) n i (a * b) = toE' (G := G) n i a + toE' (G := G) n i b := by
  rw [toE', toE', toE']
  rw [show QuotientGroup.mk' ((stepSucc (G := G) n i).subgroupOf (stepBase (G := G) n i)) (a * b)
      = QuotientGroup.mk' ((stepSucc (G := G) n i).subgroupOf (stepBase (G := G) n i)) a
        * QuotientGroup.mk' ((stepSucc (G := G) n i).subgroupOf (stepBase (G := G) n i)) b
      from map_mul _ _ _]
  exact ofMul_mul _ _

theorem toE'_eq_iff (a b : stepBase (G := G) n i) :
    toE' (G := G) n i a = toE' (G := G) n i b ↔
      (a : Work.Shrinking.freeOperatorGroup G n)⁻¹ * (b : Work.Shrinking.freeOperatorGroup G n)
        ∈ stepSucc (G := G) n i := by
  rw [toE', toE', Additive.ofMul.injective.eq_iff, QuotientGroup.mk'_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

/-- The `j = 1` value map `θ : F(n)/F(n)^2 → E(n,(i,1))`, sending the class of `z` to the class of
`z^{2^{i-1}}`. -/
noncomputable def thetaE (hi : 1 ≤ i) (v : squareQuotient 2 G n) : E 2 G n i 1 :=
  prop5.valFn 2 G i 1 n le_rfl hi (fun _ : Fin 1 => prop5.repOf 2 G n v)

theorem update_fin_one {α : Type*} (a b : α) :
    Function.update (fun _ : Fin 1 => a) 0 b = fun _ : Fin 1 => b := by
  funext k
  fin_cases k
  simp

theorem thetaE_qmk (hi : 1 ≤ i) (Z : Work.Shrinking.freeOperatorGroup G n) :
    thetaE (G := G) n i hi (prop5.qmk 2 G n Z)
      = prop5.valFn 2 G i 1 n le_rfl hi (fun _ : Fin 1 => Z) :=
  prop5.valFn_congr 2 G i 1 n le_rfl hi (fun _ => by
    show prop5.qmk 2 G n (prop5.repOf 2 G n (prop5.qmk 2 G n Z)) = prop5.qmk 2 G n Z
    rw [prop5.repOf_spec])

theorem thetaE_zero (hi : 1 ≤ i) : thetaE (G := G) n i hi 0 = 0 := by
  rw [← prop5.qmk_one 2 G n, thetaE_qmk]
  rw [← update_fin_one (1 : Work.Shrinking.freeOperatorGroup G n) 1]
  exact prop5.valFn_update_one_gen 2 G i 1 n le_rfl hi (dec := inferInstance)
    (fun _ : Fin 1 => 1) 0

theorem thetaE_add (hi : 1 ≤ i) (v w : squareQuotient 2 G n) :
    thetaE (G := G) n i hi (v + w) = thetaE (G := G) n i hi v + thetaE (G := G) n i hi w := by
  rw [thetaE, thetaE, thetaE]
  have hA : prop5.valFn 2 G i 1 n le_rfl hi (fun _ : Fin 1 => prop5.repOf 2 G n v)
      + prop5.valFn 2 G i 1 n le_rfl hi (fun _ : Fin 1 => prop5.repOf 2 G n w)
      = prop5.valFn 2 G i 1 n le_rfl hi (Function.update
          (fun _ : Fin 1 => prop5.repOf 2 G n v) 0
          (prop5.repOf 2 G n v * prop5.repOf 2 G n w)) := by
    rw [prop5.valFn_update_mul_gen 2 G i 1 n le_rfl hi (dec := inferInstance)
      (fun _ : Fin 1 => prop5.repOf 2 G n v) 0 (prop5.repOf 2 G n v) (prop5.repOf 2 G n w),
      update_fin_one, update_fin_one]
  have hB : prop5.valFn 2 G i 1 n le_rfl hi (Function.update
        (fun _ : Fin 1 => prop5.repOf 2 G n v) 0
        (prop5.repOf 2 G n v * prop5.repOf 2 G n w))
      = prop5.valFn 2 G i 1 n le_rfl hi (fun _ : Fin 1 => prop5.repOf 2 G n (v + w)) :=
    prop5.valFn_congr 2 G i 1 n le_rfl hi (fun k => by
      fin_cases k
      show prop5.qmk 2 G n (prop5.repOf 2 G n v * prop5.repOf 2 G n w)
        = prop5.qmk 2 G n (prop5.repOf 2 G n (v + w))
      rw [prop5.qmk_mul, prop5.repOf_spec, prop5.repOf_spec, prop5.repOf_spec])
  exact (hA.trans hB).symm

theorem valFn_eq_zero_iff (hi : 1 ≤ i) (z : Work.Shrinking.freeOperatorGroup G n)
    (hz : z ^ (2 ^ (i - 1)) ∈ refinedTerm 2 (Work.Shrinking.freeOperatorGroup G n) i 1) :
    prop5.valFn 2 G i 1 n le_rfl hi (fun _ : Fin 1 => z) = 0 ↔
      z ^ (2 ^ (i - 1)) ∈ refinedTerm 2 (Work.Shrinking.freeOperatorGroup G n)
        (tauSucc i 1).1 (tauSucc i 1).2 := by
  constructor
  · intro h
    have h2 : (QuotientGroup.mk'
        ((refinedTerm 2 (Work.Shrinking.freeOperatorGroup G n)
            (tauSucc i 1).1 (tauSucc i 1).2).subgroupOf
          (refinedTerm 2 (Work.Shrinking.freeOperatorGroup G n) i 1))
        ⟨(prop5.commWord 1 (fun _ : Fin 1 => z)) ^ (2 ^ (i - 1)), hz⟩ :
        refinedQuotient 2 (Work.Shrinking.freeOperatorGroup G n) i 1) = 1 := by
      rw [prop5.valFn_eq, prop5.valFnOf] at h
      exact Additive.ofMul.injective h
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)
  · intro h
    rw [prop5.valFn_eq, prop5.valFnOf]
    exact congrArg Additive.ofMul ((QuotientGroup.eq_one_iff _).mpr
      (Subgroup.mem_subgroupOf.mpr h))

theorem thetaE_neg (hi : 1 ≤ i) (v : squareQuotient 2 G n) :
    thetaE (G := G) n i hi (-v) = - thetaE (G := G) n i hi v := by
  have h : thetaE (G := G) n i hi (-v) + thetaE (G := G) n i hi v = 0 := by
    rw [← thetaE_add, neg_add_cancel, thetaE_zero]
  exact eq_neg_of_add_eq_zero_left h

theorem thetaE_eq_zero_imp (hi : 1 ≤ i) (v : squareQuotient 2 G n)
    (hv : thetaE (G := G) n i hi v = 0) : v = 0 := by
  have hmem : (prop5.repOf 2 G n v) ^ (2 ^ (i - 1)) ∈ refinedTerm 2
      (Work.Shrinking.freeOperatorGroup G n)
      (tauSucc i 1).1 (tauSucc i 1).2 :=
    (valFn_eq_zero_iff (G := G) n i hi (prop5.repOf 2 G n v)
      (prop5.commWord_pow_mem_refinedTerm 2 G i 1 n le_rfl hi
        (fun _ : Fin 1 => prop5.repOf 2 G n v))).mp hv
  exact (prop5.repOf_spec 2 G n v).symm.trans
    (pow_two_pow_mem_refinedTerm_imp_qmk_eq_zero (G := G) n i hi hmem)

theorem thetaE_injective (hi : 1 ≤ i) : Function.Injective (thetaE (G := G) n i hi) := by
  intro v w hvw
  have h : v - w = 0 := thetaE_eq_zero_imp (G := G) n i hi (v - w) (by
    rw [sub_eq_add_neg, thetaE_add, hvw, thetaE_neg, add_neg_cancel])
  exact sub_eq_zero.mp h

theorem thetaE_smul (hi : 1 ≤ i) (g : G) (v : squareQuotient 2 G n) :
    thetaE (G := G) n i hi (g • v) = g • thetaE (G := G) n i hi v := by
  rw [thetaE, thetaE]
  refine (prop5.valFn_congr 2 G i 1 n le_rfl hi (fun _ => ?_)).trans
    (prop5.valFn_smul 2 G i 1 n le_rfl hi g (fun _ : Fin 1 => prop5.repOf 2 G n v))
  show prop5.qmk 2 G n (prop5.repOf 2 G n (g • v))
    = prop5.qmk 2 G n (g • prop5.repOf 2 G n v)
  rw [prop5.repOf_spec,
    ← prop5.qmk_smul 2 G n g (prop5.repOf 2 G n v), prop5.repOf_spec]

theorem pow_mem_stepBase (hi : 1 ≤ i) (y : Work.Shrinking.freeOperatorGroup G n) :
    y ^ (2 ^ (i - 1)) ∈ stepBase (G := G) n i := by
  have h := prop5.pow_mem_pSeries 2 1 (i - 1) le_rfl y (Subgroup.mem_top y)
  rw [show 1 + (i - 1) - 1 = i - 1 from by omega] at h
  rwa [stepBase, flowTerm, refinedTerm_one]

theorem gamma2_inf_stepBase_le_stepSucc (hi : 1 ≤ i) :
    (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries 1 ⊓
      stepBase (G := G) n i ≤ stepSucc (G := G) n i := by
  rcases eq_or_lt_of_le hi with h1 | h2
  · subst h1
    rw [stepSucc, flowTerm, show tauSucc 1 1 = (2, 1) from tauSucc_of_le le_rfl, refinedTerm_one,
      show pSeries 2 (Work.Shrinking.freeOperatorGroup G n) 2
        = Work.Shrinking.pCentralStep 2 (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))
        from rfl, Work.Shrinking.pCentralStep]
    exact le_trans inf_le_left le_sup_right
  · have hτ : tauSucc i 1 = (i, 2) := tauSucc_of_lt h2
    rw [stepSucc, flowTerm, hτ, refinedTerm]
    refine le_trans ?_ le_sup_left
    refine le_inf ?_ ?_
    · rw [stepBase, flowTerm, refinedTerm_one]
      exact inf_le_right
    · rw [centralSeries_succ_succ, centralSeries_one]
      exact inf_le_left

theorem toE'_one : toE' (G := G) n i (1 : stepBase (G := G) n i) = 0 := by
  rw [toE', show (1 : stepBase (G := G) n i)
    = (⟨(1 : Work.Shrinking.freeOperatorGroup G n), (stepBase (G := G) n i).one_mem⟩ :
      stepBase (G := G) n i) from Subtype.ext rfl]
  exact toE_zero (G := G) n i

/-- The `2^{i-1}`-st powers of all elements of `F(n)` generate the graded piece `E(n,(i,1))`. -/
theorem thetaE_surjective (hi : 1 ≤ i) : Function.Surjective (thetaE (G := G) n i hi) := by
  set S : Subgroup (Work.Shrinking.freeOperatorGroup G n) :=
    Subgroup.closure {x : Work.Shrinking.freeOperatorGroup G n |
      ∃ y : Work.Shrinking.freeOperatorGroup G n, x = y ^ (2 ^ (i - 1))} with hS
  have hSle : S ≤ stepBase (G := G) n i := by
    rw [hS, Subgroup.closure_le]
    rintro u ⟨y, rfl⟩
    exact pow_mem_stepBase (G := G) n i hi y
  -- every element of `S` is in the range of `θ`
  have key : ∀ u (hu : u ∈ S), ∃ v : squareQuotient 2 G n,
      thetaE (G := G) n i hi v = toE' (G := G) n i ⟨u, hSle hu⟩ := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem x hx =>
        obtain ⟨y, rfl⟩ := hx
        refine ⟨prop5.qmk 2 G n y, ?_⟩
        rw [thetaE_qmk, prop5.valFn_eq, prop5.valFnOf, toE']
        exact congrArg Additive.ofMul (congrArg
          (QuotientGroup.mk' ((stepSucc (G := G) n i).subgroupOf (stepBase (G := G) n i)))
          (Subtype.ext (by
            show (prop5.commWord 1 (fun _ : Fin 1 => y)) ^ (2 ^ (i - 1))
              = y ^ (2 ^ (i - 1))
            rw [prop5.commWord_one])))
    | one => exact ⟨0, by rw [thetaE_zero, toE', show (⟨(1 : Work.Shrinking.freeOperatorGroup G n),
        _⟩ : stepBase (G := G) n i) = 1 from Subtype.ext rfl, map_one, ofMul_one]⟩
    | mul a b ha hb iha ihb =>
        obtain ⟨v, hv⟩ := iha
        obtain ⟨w, hw⟩ := ihb
        refine ⟨v + w, ?_⟩
        rw [thetaE_add, hv, hw, ← toE'_mul]
        rfl
    | inv a ha iha =>
        obtain ⟨v, hv⟩ := iha
        refine ⟨-v, ?_⟩
        rw [thetaE_neg, hv]
        have h2 : toE' (G := G) n i ⟨a⁻¹, hSle (Subgroup.inv_mem _ ha)⟩
            = - toE' (G := G) n i ⟨a, hSle ha⟩ := by
          have h3 : toE' (G := G) n i ⟨a⁻¹, hSle (Subgroup.inv_mem _ ha)⟩
              + toE' (G := G) n i ⟨a, hSle ha⟩ = 0 := by
            rw [← toE'_mul, show (⟨a⁻¹, hSle (Subgroup.inv_mem _ ha)⟩ :
                stepBase (G := G) n i) * ⟨a, hSle ha⟩ = 1 from by
              rw [Subtype.ext_iff]
              simp, toE'_one]
          exact eq_neg_of_add_eq_zero_left h3
        exact h2.symm
  intro x
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective
    ((stepSucc (G := G) n i).subgroupOf (stepBase (G := G) n i)) (Additive.toMul x)
  have hxy : toE' (G := G) n i y = x := by
    show Additive.ofMul (QuotientGroup.mk'
      ((stepSucc (G := G) n i).subgroupOf (stepBase (G := G) n i)) y) = x
    rw [hy]
    rfl
  have hyP : (y : Work.Shrinking.freeOperatorGroup G n) ∈
      Work.Shrinking.pCentralSeries 2 (Work.Shrinking.freeOperatorGroup G n) (i - 1) := by
    simpa [stepBase, flowTerm, refinedTerm_one] using y.2
  have hyS : (y : Work.Shrinking.freeOperatorGroup G n) ∈ S ⊔
      (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries 1 := by
    rw [hS]
    exact pCentralSeries_le_pow_sup_commutator' 2 i hi hyP
  obtain ⟨u, hu, g, hg, hug⟩ := (Subgroup.mem_sup_of_normal_right (s := S)
    (t := (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).lowerCentralSeries 1)).mp hyS
  have hgmem : (g : Work.Shrinking.freeOperatorGroup G n) ∈ stepBase (G := G) n i := by
    have hge : (g : Work.Shrinking.freeOperatorGroup G n)
        = (u : Work.Shrinking.freeOperatorGroup G n)⁻¹
          * (y : Work.Shrinking.freeOperatorGroup G n) := by
      rw [← hug]
      group
    rw [hge]
    exact (stepBase (G := G) n i).mul_mem (Subgroup.inv_mem _ (hSle hu)) y.2
  have hgss : (g : Work.Shrinking.freeOperatorGroup G n) ∈ stepSucc (G := G) n i :=
    gamma2_inf_stepBase_le_stepSucc (G := G) n i hi (Subgroup.mem_inf.mpr ⟨hg, hgmem⟩)
  have hQ : toE' (G := G) n i ⟨u, hSle hu⟩ = toE' (G := G) n i y := by
    refine (toE'_eq_iff (G := G) n i _ _).mpr ?_
    rw [show (⟨u, hSle hu⟩ : stepBase (G := G) n i).1⁻¹
        * (y : Work.Shrinking.freeOperatorGroup G n)
        = (g : Work.Shrinking.freeOperatorGroup G n) from by
      rw [← hug]
      group]
    exact hgss
  obtain ⟨v, hv⟩ := key u hu
  exact ⟨v, hv.trans (hQ.trans hxy)⟩

/-- **Proposition 5 of Schmidt–Wingberg for `j = 1`, as an isomorphism.** -/
theorem exists_thetaEquiv (hi : 1 ≤ i) :
    ∃ θ : squareQuotient 2 G n ≃+ E 2 G n i 1,
      (∀ (g : G) (v : squareQuotient 2 G n), θ (g • v) = g • θ v) ∧
      (∀ Z : Work.Shrinking.freeOperatorGroup G n,
        θ (prop5.qmk 2 G n Z) = prop5.valFn 2 G i 1 n le_rfl hi (fun _ : Fin 1 => Z)) := by
  refine ⟨AddEquiv.ofBijective (show squareQuotient 2 G n →+ E 2 G n i 1 from
      { toFun := thetaE (G := G) n i hi
        map_zero' := thetaE_zero (G := G) n i hi
        map_add' := thetaE_add (G := G) n i hi })
    ⟨thetaE_injective (G := G) n i hi, thetaE_surjective (G := G) n i hi⟩, ?_, ?_⟩
  · intro g v
    show thetaE (G := G) n i hi (g • v) = g • thetaE (G := G) n i hi v
    exact thetaE_smul n i hi g v
  · intro Z
    show thetaE (G := G) n i hi (prop5.qmk 2 G n Z)
      = prop5.valFn 2 G i 1 n le_rfl hi (fun _ : Fin 1 => Z)
    exact thetaE_qmk n i hi Z

end Theta


/-! ## The graded step in the additive language and the target theorem -/

section Target

variable {G : Type*} [Group G] [Fintype G] (n : ℕ)

/-- Every `δ`-fixed element of the graded piece `E(n,(i,1))` is a `δ`-difference. -/
theorem E_fixed_is_delta_difference (i : ℕ) (hi : 1 ≤ i) (δ : G) (hδ : δ * δ = 1)
    (hδ1 : δ ≠ 1) :
    ∀ x : E 2 G n i 1, δ • x = x → ∃ y : E 2 G n i 1, x = δ • y - y := by
  rcases eq_or_lt_of_le hi with h1 | h2
  · subst h1
    exact E_one_one_fixed_is_delta_difference G n δ hδ hδ1
  · intro x hx
    obtain ⟨θ, hθsmul, _hθqmk⟩ := exists_thetaEquiv (G := G) n i hi
    have hva : δ • (θ.symm x) = θ.symm x := by
      apply θ.injective
      rw [hθsmul, θ.apply_symm_apply, hx]
    obtain ⟨w, hw⟩ := squareQuotient_fixed_is_delta_difference G n δ hδ hδ1 (θ.symm x) hva
    refine ⟨θ w, ?_⟩
    have h1 : δ • θ w - θ w = θ (δ • w - w) := by rw [map_sub, hθsmul]
    rw [h1, ← hw, θ.apply_symm_apply]

end Target


section FinalAux

variable {G : Type*} [Group G] (n i : ℕ)

theorem toE_inv {z : Work.Shrinking.freeOperatorGroup G n}
    (hz : z ∈ stepBase (G := G) n i) (hzi : z⁻¹ ∈ stepBase (G := G) n i) :
    toE n i z⁻¹ hzi = - toE n i z hz := by
  rw [toE, toE, show (⟨z⁻¹, hzi⟩ : stepBase (G := G) n i)
    = (⟨z, hz⟩ : stepBase (G := G) n i)⁻¹ from Subtype.ext rfl, map_inv]
  rfl

theorem toQ_inv (z : Work.Shrinking.freeOperatorGroup G n) :
    toQ n i z⁻¹ = (toQ n i z)⁻¹ := by
  rw [toQ, toQ]
  exact map_inv (QuotientGroup.mk' ((stepSucc (G := G) n i).subgroupOf
    (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)))) ⟨z, Subgroup.mem_top z⟩

theorem toE_congr (z : Work.Shrinking.freeOperatorGroup G n)
    (h h' : z ∈ stepBase (G := G) n i) : toE n i z h = toE n i z h' :=
  toE_eq_of_mem_stepSucc n i h h' (by
    rw [inv_mul_cancel]
    exact (stepSucc (G := G) n i).one_mem)

theorem smul_mem_stepBase (δ : G) {z : Work.Shrinking.freeOperatorGroup G n}
    (hz : z ∈ stepBase (G := G) n i) : δ • z ∈ stepBase (G := G) n i :=
  Work.Shrinking.mem_smul_mem (stepBase (G := G) n i) δ
    (map_refinedTerm_eq 2 (MulDistribMulAction.toMulAut G
      (Work.Shrinking.freeOperatorGroup G n) δ) i 1) hz

end FinalAux

/-- **The `j = 1` half of the level-by-level graded step of the `p = 2` correction.** -/
theorem gradedStep_j_one (G : Type*) [Group G] [Fintype G] (n : ℕ) (δ : G) (hδ : δ * δ = 1)
    (hδ1 : δ ≠ 1) :
    ∀ (i : ℕ), 1 ≤ i →
      ∀ c : Work.CohomologicalShrinking.flowQuotient 2 G n
          (Work.CohomologicalShrinking.tauSucc i 1).1
          (Work.CohomologicalShrinking.tauSucc i 1).2,
        Work.SSGRoute.flowQuotSucc 2 G n i 1 c = 1 →
        Work.CohomologicalShrinking.flowAction 2 G n
            (Work.CohomologicalShrinking.tauSucc i 1).1
            (Work.CohomologicalShrinking.tauSucc i 1).2 δ c = c⁻¹ →
        ∃ e : Work.CohomologicalShrinking.flowQuotient 2 G n
              (Work.CohomologicalShrinking.tauSucc i 1).1
              (Work.CohomologicalShrinking.tauSucc i 1).2,
          c = (Work.CohomologicalShrinking.flowAction 2 G n
                (Work.CohomologicalShrinking.tauSucc i 1).1
                (Work.CohomologicalShrinking.tauSucc i 1).2 δ e)⁻¹ * e := by
  intro i hi c hker hanti
  obtain ⟨Z, hZ⟩ := QuotientGroup.mk'_surjective ((stepSucc (G := G) n i).subgroupOf
    (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n))) c
  have hc : toQ n i Z.1 = c := by
    rw [toQ]
    exact (congrArg (QuotientGroup.mk' ((stepSucc (G := G) n i).subgroupOf
      (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)))) (Subtype.ext rfl)).trans hZ
  have hZmem : Z.1 ∈ stepBase (G := G) n i := by
    have h := hker
    rw [← hc, toQ] at h
    rw [flowQuotSucc_mk] at h
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h)
  have hc2 : c ^ 2 = 1 := by
    rw [← hc]
    exact toQ_pow_two (G := G) n i hZmem
  have hc2' : c * c = 1 := by
    rw [pow_two] at hc2
    exact hc2
  have hfix : flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 δ c = c := by
    rw [hanti]
    exact inv_eq_of_mul_eq_one_right hc2'
  have hxfix : δ • toE n i Z.1 hZmem = toE n i Z.1 hZmem := by
    rw [toE_smul (G := G) n i δ hZmem (smul_mem_stepBase (G := G) n i δ hZmem)]
    refine toE_eq_of_mem_stepSucc n i _ _ ?_
    refine (toQ_eq_iff n i).mp ?_
    rw [← toQ_smul (G := G) n i δ Z.1, hc, hfix]
  obtain ⟨y, hy⟩ := E_fixed_is_delta_difference (G := G) n i hi δ hδ hδ1 (toE n i Z.1 hZmem) hxfix
  obtain ⟨W, hW⟩ := QuotientGroup.mk'_surjective ((stepSucc (G := G) n i).subgroupOf
    (stepBase (G := G) n i)) (Additive.toMul y)
  have hWy : toE' (G := G) n i W = y := by
    show Additive.ofMul (QuotientGroup.mk' _ W) = y
    rw [hW]
    rfl
  refine ⟨toQ n i W.1, ?_⟩
  have hδW : (δ • W.1) ∈ stepBase (G := G) n i := smul_mem_stepBase (G := G) n i δ W.2
  have hprod : (δ • W.1)⁻¹ * W.1 ∈ stepBase (G := G) n i :=
    (stepBase (G := G) n i).mul_mem (Subgroup.inv_mem _ hδW) W.2
  have h1 : (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 δ (toQ n i W.1))⁻¹
      * toQ n i W.1 = toQ n i ((δ • W.1)⁻¹ * W.1) := by
    rw [toQ_smul (G := G) n i δ W.1, ← toQ_inv (G := G) n i (δ • W.1),
      ← toQ_mul (G := G) n i _ _]
  have hWy' : toE n i W.1 W.2 = y := (toE_eq_toE' (G := G) n i W.1 W.2).trans (by
    rw [show (⟨W.1, W.2⟩ : stepBase (G := G) n i) = W from Subtype.ext rfl, hWy])
  have hE : toE n i ((δ • W.1)⁻¹ * W.1) hprod = toE n i Z.1 hZmem := by
    rw [toE_mul (G := G) n i (Subgroup.inv_mem _ hδW) W.2 hprod,
      toE_inv (G := G) n i hδW (Subgroup.inv_mem _ hδW),
      ← toE_smul (G := G) n i δ W.2 hδW, hWy']
    rw [E_neg_self (G := G) n i (δ • y), hy, sub_eq_add_neg, E_neg_self (G := G) n i y]
  have h2 : toQ n i ((δ • W.1)⁻¹ * W.1) = c := by
    rw [← hc]
    exact (toQ_eq_iff n i).mpr ((toE_eq_iff n i hprod hZmem).mp hE)
  exact (h1.trans h2).symm

end Work.SSGRoute

