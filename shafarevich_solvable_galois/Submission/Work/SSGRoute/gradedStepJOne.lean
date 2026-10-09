import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.SSGRoute.two_torsion_base
import Submission.Work.SSGRoute.two_torsion_assembly
import Submission.Work.SSGRoute.prop5Data_exists
import Submission.Work.SSGRoute.gradedPiece_one
import Submission.Work.SSGRoute.prop5.pCentralSeries_le_pow_sup_commutator
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open Work.CohomologicalShrinking

attribute [local instance] Classical.decEq

set_option maxHeartbeats 4000000

namespace JOne

open scoped commutatorElement

/-- Abbreviation for the free `G`-operator group of rank `n`. -/
abbrev FO (G : Type*) [Group G] (n : ℕ) : Type _ := Work.Shrinking.freeOperatorGroup G n

/-! ## The exponent-sum homomorphism `F(n) →* (Fin n × G → ℤ)` and divisibility -/

noncomputable def zetaHom (G : Type*) [Group G] (n : ℕ) :
    FO G n →* Multiplicative (Fin n × G → ℤ) :=
  FreeGroup.lift (fun x => Multiplicative.ofAdd (Pi.single x (1 : ℤ)))

theorem zetaHom_of (G : Type*) [Group G] (n : ℕ) (x : Fin n × G) :
    zetaHom G n (FreeGroup.of x) = Multiplicative.ofAdd (Pi.single x (1 : ℤ)) :=
  FreeGroup.lift_apply_of

theorem zetaHom_commutator (G : Type*) [Group G] (n : ℕ) (a b : FO G n) :
    zetaHom G n ⁅a, b⁆ = 1 := by
  rw [map_commutatorElement]
  exact commutatorElement_eq_one_iff_commute.mpr (mul_comm _ _)

/-- The subgroup of exponent vectors all of whose coordinates are divisible by `2 ^ k`. -/
noncomputable def divSub (G : Type*) [Group G] (n k : ℕ) :
    Subgroup (Multiplicative (Fin n × G → ℤ)) where
  carrier := {u | ∀ x : Fin n × G, (2 : ℤ) ^ k ∣ Multiplicative.toAdd u x}
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

/-- The exponent-sum map sends the `k`-th `p`-central term into the exponent vectors whose
coordinates are divisible by `2 ^ k`. -/
theorem pCentralSeries_le_divSub_comap (G : Type*) [Group G] (n k : ℕ) :
    Work.Shrinking.pCentralSeries 2 (FO G n) k ≤ (divSub G n k).comap (zetaHom G n) := by
  induction k with
  | zero => intro u _ x; simp
  | succ k ih =>
      rw [Work.Shrinking.pCentralSeries_succ, Work.Shrinking.pCentralStep]
      refine sup_le ?_ ?_
      · rw [Work.Shrinking.powSubgroup]
        refine (Subgroup.closure_le _).mpr ?_
        rintro u ⟨y, hy, rfl⟩
        change zetaHom G n (y ^ 2) ∈ divSub G n (k + 1)
        intro x
        rw [map_pow, toAdd_pow, Pi.smul_apply, nsmul_eq_mul]
        obtain ⟨d, hd⟩ := ih hy x
        rw [hd]
        refine ⟨d, ?_⟩
        rw [pow_succ]
        ring
      · refine (Subgroup.commutator_le).mpr fun a _ b _ => ?_
        change zetaHom G n ⁅a, b⁆ ∈ divSub G n (k + 1)
        rw [zetaHom_commutator]
        exact Subgroup.one_mem _

/-- `zetaHom` kills the derived subgroup `γ₂`. -/
theorem lowerCentralSeries_one_le_zetaKer (G : Type*) [Group G] (n : ℕ) :
    (⊤ : Subgroup (FO G n)).lowerCentralSeries 1 ≤ (zetaHom G n).ker := by
  rw [Subgroup.top_lowerCentralSeries_one]
  refine (Subgroup.commutator_le).mpr fun a _ b _ => ?_
  rw [MonoidHom.mem_ker, zetaHom_commutator]

/-- The image of the `j = 1` refined term `F(n)^{(i,2)}` under the exponent-sum map has
coordinates divisible by `2 ^ i`. -/
theorem refinedTerm_le_divSub_comap (G : Type*) [Group G] (n i : ℕ) (hi : 1 ≤ i) :
    refinedTerm 2 (FO G n) (tauSucc i 1).1 (tauSucc i 1).2
      ≤ (divSub G n i).comap (zetaHom G n) := by
  rcases eq_or_lt_of_le hi with h1 | h2
  · subst h1
    rw [tauSucc_of_le (le_refl 1), refinedTerm_one]
    exact pCentralSeries_le_divSub_comap G n 1
  · rw [tauSucc_of_lt h2, refinedTerm]
    refine sup_le ?_ ?_
    · refine le_trans inf_le_right ?_
      refine le_trans (lowerCentralSeries_one_le_zetaKer G n) ?_
      intro u hu
      change zetaHom G n u ∈ divSub G n i
      have hu' : zetaHom G n u = 1 := hu
      rw [hu']
      exact Subgroup.one_mem _
    · exact pCentralSeries_le_divSub_comap G n i

/-! ## The coordinatewise reduction mod `2` and the model of `F(n)/F(n)²` -/

noncomputable def pushHom (G : Type*) [Group G] (n : ℕ) :
    Multiplicative (Fin n × G → ℤ) →* Multiplicative (Fin n × G → ZMod 2) where
  toFun f := Multiplicative.ofAdd fun x => ((Multiplicative.toAdd f x : ℤ) : ZMod 2)
  map_one' := by
    show Multiplicative.ofAdd (fun x =>
      ((Multiplicative.toAdd (1 : Multiplicative (Fin n × G → ℤ))) x : ZMod 2)) = 1
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

theorem pushHom_ofAdd (G : Type*) [Group G] (n : ℕ) (v : Fin n × G → ℤ) :
    pushHom G n (Multiplicative.ofAdd v)
      = Multiplicative.ofAdd (fun y => ((v y : ℤ) : ZMod 2)) := rfl

/-- The value of `pushHom` on an arbitrary exponent vector. -/
theorem pushHom_apply (G : Type*) [Group G] (n : ℕ) (f : Multiplicative (Fin n × G → ℤ)) :
    pushHom G n f = Multiplicative.ofAdd
      (fun y => ((Multiplicative.toAdd f y : ℤ) : ZMod 2)) := rfl

/-- The canonical map `F(n) →* 𝔽₂[G]^n` factors through the exponent-sum map. -/
theorem freeToFun_eq_pushHom_zetaHom (G : Type*) [Group G] (n : ℕ) (z : FO G n) :
    freeToFun 2 G n z = pushHom G n (zetaHom G n z) := by
  have h : (freeToFun 2 G n) = (pushHom G n).comp (zetaHom G n) := by
    refine FreeGroup.ext_hom _ _ fun x => ?_
    show freeToFun 2 G n (FreeGroup.of x) = pushHom G n (zetaHom G n (FreeGroup.of x))
    rw [zetaHom_of, freeToFun_of, pushHom_ofAdd]
    apply Multiplicative.ofAdd.injective
    funext y
    show (Pi.single x (1 : ZMod 2) : Fin n × G → ZMod 2) y
      = (((Pi.single x (1 : ℤ) : Fin n × G → ℤ) y : ℤ) : ZMod 2)
    rw [Pi.single_apply, Pi.single_apply]
    by_cases hy : y = x <;> simp [hy]
  exact congrFun (congrArg DFunLike.coe h) z

theorem squareQuotientToFun_qmk (G : Type*) [Group G] (n : ℕ) (z : FO G n) :
    squareQuotientToFun 2 G n (prop5.qmk 2 G n z)
      = Multiplicative.toAdd (freeToFun 2 G n z) := by
  show Multiplicative.toAdd (quotHom 2 G n (Additive.toMul (prop5.qmk 2 G n z))) = _
  rfl

theorem qmk_eq_zero_of_freeToFun_eq_one (G : Type*) [Group G] [Fintype G] (n : ℕ) (z : FO G n)
    (h : freeToFun 2 G n z = 1) : prop5.qmk 2 G n z = 0 := by
  apply (modsquare.squareQuotientToFun_bijective 2 G n).1
  rw [squareQuotientToFun_qmk, h, toAdd_one, map_zero]

/-! ## Injectivity of the degree-`1` value map `v ↦ v^{2^{i-1}}` -/

theorem valFn_eq_zero_iff (G : Type*) [Group G] (n i : ℕ) (hi : 1 ≤ i) (z : FO G n)
    (hz : z ^ (2 ^ (i - 1)) ∈ refinedTerm 2 (FO G n) i 1) :
    prop5.valFn 2 G i 1 n le_rfl hi (fun _ : Fin 1 => z) = 0 ↔
      z ^ (2 ^ (i - 1)) ∈ refinedTerm 2 (FO G n) (tauSucc i 1).1 (tauSucc i 1).2 := by
  constructor
  · intro h
    rw [prop5.valFn_eq, prop5.valFnOf] at h
    have h2 := Additive.ofMul.injective h
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)
  · intro h
    rw [prop5.valFn_eq, prop5.valFnOf]
    refine congrArg Additive.ofMul ?_
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr h)

theorem valFn_eq_zero_imp_qmk_eq_zero (G : Type*) [Group G] [Fintype G] (n i : ℕ) (hi : 1 ≤ i)
    (z : FO G n) :
    prop5.valFn 2 G i 1 n le_rfl hi (fun _ : Fin 1 => z) = 0 → prop5.qmk 2 G n z = 0 := by
  intro h
  have hmem1 : z ^ (2 ^ (i - 1)) ∈ refinedTerm 2 (FO G n) i 1 := by
    rw [refinedTerm_one]
    have h1 := prop5.pow_mem_pSeries 2 (P := FO G n) 1 (i - 1) le_rfl z (Subgroup.mem_top z)
    have hidx : (1 : ℕ) + (i - 1) - 1 = i - 1 := by omega
    rwa [hidx] at h1
  have hmem2 := (valFn_eq_zero_iff G n i hi z hmem1).mp h
  have hdiv := refinedTerm_le_divSub_comap G n i hi hmem2
  have hcoord : ∀ y : Fin n × G, (2 : ℤ) ∣ Multiplicative.toAdd (zetaHom G n z) y := by
    intro y
    have hh := hdiv y
    rw [map_pow, toAdd_pow, Pi.smul_apply, nsmul_eq_mul] at hh
    have h2 : (2 : ℤ) ^ i = 2 ^ (i - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel hi]
    rw [h2] at hh
    exact (mul_dvd_mul_iff_left (pow_ne_zero (i - 1) (by norm_num : (2 : ℤ) ≠ 0))).mp hh
  have hff : freeToFun 2 G n z = 1 := by
    rw [freeToFun_eq_pushHom_zetaHom, pushHom_apply]
    have hfun : (fun y : Fin n × G =>
        ((Multiplicative.toAdd (zetaHom G n z) y : ℤ) : ZMod 2)) = 0 := by
      funext y
      obtain ⟨d, hd⟩ := hcoord y
      rw [hd]
      have h2z : ((2 : ℤ) : ZMod 2) = 0 := by decide
      rw [Int.cast_mul, h2z, zero_mul]
      rfl
    rw [hfun, ofAdd_zero]
  exact qmk_eq_zero_of_freeToFun_eq_one G n z hff

/-! ## The kernel of `Q_{(i,2)} → Q_{(i,1)}` and the transfer to the ambient group -/

/-- The refined term `F(n)^{(i,1)} = F(n)_i`. -/
noncomputable abbrev stepBase (G : Type*) [Group G] (n i : ℕ) : Subgroup (FO G n) :=
  flowTerm 2 G n i 1

/-- The next refined term `F(n)^{(i,1)+1}`, defining the kernel of `Q_{(i,2)} → Q_{(i,1)}`. -/
noncomputable abbrev stepSucc (G : Type*) [Group G] (n i : ℕ) : Subgroup (FO G n) :=
  flowTerm 2 G n (tauSucc i 1).1 (tauSucc i 1).2

theorem stepSucc_le_stepBase (G : Type*) [Group G] (n i : ℕ) :
    stepSucc G n i ≤ stepBase G n i :=
  refinedTerm_tauSucc_le 2 _ i 1

theorem pow_mem_stepBase (G : Type*) [Group G] (n i : ℕ) (hi : 1 ≤ i) (z : FO G n) :
    z ^ (2 ^ (i - 1)) ∈ stepBase G n i := by
  change z ^ (2 ^ (i - 1)) ∈ refinedTerm 2 (FO G n) i 1
  rw [refinedTerm_one]
  have h1 := prop5.pow_mem_pSeries 2 (P := FO G n) 1 (i - 1) le_rfl z (Subgroup.mem_top z)
  have hidx : (1 : ℕ) + (i - 1) - 1 = i - 1 := by omega
  rwa [hidx] at h1

/-- The class of `z ∈ F(n)_i` in the graded piece `E(n,(i,1))`. -/
noncomputable def toE (G : Type*) [Group G] (n i : ℕ) (z : FO G n) (hz : z ∈ stepBase G n i) :
    E 2 G n i 1 :=
  Additive.ofMul (QuotientGroup.mk' ((stepSucc G n i).subgroupOf (stepBase G n i)) ⟨z, hz⟩)

/-- The class of `z` in the ambient quotient `Q_{(i,2)} = F(n)/F(n)^{(i,2)}`. -/
noncomputable def toQ (G : Type*) [Group G] (n i : ℕ) (z : FO G n) :
    flowQuotient 2 G n (tauSucc i 1).1 (tauSucc i 1).2 :=
  QuotientGroup.mk' ((stepSucc G n i).subgroupOf (⊤ : Subgroup (FO G n)))
    ⟨z, Subgroup.mem_top z⟩

theorem toE_eq_iff (G : Type*) [Group G] (n i : ℕ) {a b : FO G n}
    (ha : a ∈ stepBase G n i) (hb : b ∈ stepBase G n i) :
    toE G n i a ha = toE G n i b hb ↔ a⁻¹ * b ∈ stepSucc G n i := by
  rw [toE, toE, Additive.ofMul.injective.eq_iff, QuotientGroup.mk'_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  rfl

theorem toE_eq_of_mem_stepSucc (G : Type*) [Group G] (n i : ℕ) {a b : FO G n}
    (ha : a ∈ stepBase G n i) (hb : b ∈ stepBase G n i) (h : a⁻¹ * b ∈ stepSucc G n i) :
    toE G n i a ha = toE G n i b hb :=
  (toE_eq_iff G n i ha hb).mpr h

theorem toQ_eq_iff (G : Type*) [Group G] (n i : ℕ) {a b : FO G n} :
    toQ G n i a = toQ G n i b ↔ a⁻¹ * b ∈ stepSucc G n i := by
  rw [toQ, toQ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    Subgroup.mem_subgroupOf]
  rfl

theorem toQ_one (G : Type*) [Group G] (n i : ℕ) :
    toQ G n i (1 : FO G n) = 1 := by
  rw [toQ]
  exact map_one (QuotientGroup.mk' ((stepSucc G n i).subgroupOf (⊤ : Subgroup (FO G n))))

theorem toE_one (G : Type*) [Group G] (n i : ℕ) (h : (1 : FO G n) ∈ stepBase G n i) :
    toE G n i 1 h = 0 := by
  rw [toE, show (⟨(1 : FO G n), h⟩ : stepBase G n i) = 1 from Subtype.ext rfl,
    map_one (QuotientGroup.mk' ((stepSucc G n i).subgroupOf (stepBase G n i)))]
  exact ofMul_one

theorem toQ_mul (G : Type*) [Group G] (n i : ℕ) (a b : FO G n) :
    toQ G n i (a * b) = toQ G n i a * toQ G n i b := by
  show QuotientGroup.mk' ((stepSucc G n i).subgroupOf (⊤ : Subgroup (FO G n)))
      (⟨a * b, Subgroup.mem_top (a * b)⟩ : ↥(⊤ : Subgroup (FO G n)))
    = QuotientGroup.mk' ((stepSucc G n i).subgroupOf (⊤ : Subgroup (FO G n)))
        (⟨a, Subgroup.mem_top a⟩ : ↥(⊤ : Subgroup (FO G n)))
      * QuotientGroup.mk' ((stepSucc G n i).subgroupOf (⊤ : Subgroup (FO G n)))
        (⟨b, Subgroup.mem_top b⟩ : ↥(⊤ : Subgroup (FO G n)))
  rw [show (⟨a * b, Subgroup.mem_top (a * b)⟩ : ↥(⊤ : Subgroup (FO G n)))
      = (⟨a, Subgroup.mem_top a⟩ : ↥(⊤ : Subgroup (FO G n)))
        * ⟨b, Subgroup.mem_top b⟩ from Subtype.ext rfl]
  exact map_mul (QuotientGroup.mk' ((stepSucc G n i).subgroupOf (⊤ : Subgroup (FO G n))))
    (⟨a, Subgroup.mem_top a⟩ : ↥(⊤ : Subgroup (FO G n))) ⟨b, Subgroup.mem_top b⟩

theorem toQ_inv (G : Type*) [Group G] (n i : ℕ) (a : FO G n) :
    toQ G n i a⁻¹ = (toQ G n i a)⁻¹ := by
  rw [toQ, toQ]
  exact map_inv (QuotientGroup.mk' ((stepSucc G n i).subgroupOf (⊤ : Subgroup (FO G n))))
    (⟨a, Subgroup.mem_top a⟩ : ↥(⊤ : Subgroup (FO G n)))

theorem toQ_smul (G : Type*) [Group G] (n i : ℕ) (g : G) (z : FO G n) :
    flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 g (toQ G n i z) = toQ G n i (g • z) := by
  rw [toQ, toQ]
  have hP : (⊤ : Subgroup (FO G n)).map
      (MulDistribMulAction.toMulAut G (FO G n) g).toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (MulDistribMulAction.toMulAut G (FO G n) g).surjective
  have hK : (stepSucc G n i).map
      (MulDistribMulAction.toMulAut G (FO G n) g).toMonoidHom = stepSucc G n i :=
    map_refinedTerm_eq 2 _ (tauSucc i 1).1 (tauSucc i 1).2
  change Work.Shrinking.quotAut ⊤ (stepSucc G n i) g hP hK
      (QuotientGroup.mk' ((stepSucc G n i).subgroupOf ⊤)
        ⟨z, Subgroup.mem_top z⟩) = _
  rw [Work.Shrinking.quotAut_mk]
  exact congrArg _ (Subtype.ext (Work.Shrinking.subAut_coe ⊤ g hP ⟨z, Subgroup.mem_top z⟩))

theorem toE_smul (G : Type*) [Group G] (n i : ℕ) (g : G) {z : FO G n}
    (hz : z ∈ stepBase G n i) (hgz : g • z ∈ stepBase G n i) :
    g • toE G n i z hz = toE G n i (g • z) hgz := by
  rw [toE, toE]
  have hsmul : g • Additive.ofMul (QuotientGroup.mk'
        ((stepSucc G n i).subgroupOf (stepBase G n i)) ⟨z, hz⟩)
      = Additive.ofMul (g • (QuotientGroup.mk'
        ((stepSucc G n i).subgroupOf (stepBase G n i)) ⟨z, hz⟩ :
          refinedQuotient 2 (FO G n) i 1)) := rfl
  rw [hsmul]
  have hH : (stepBase G n i).map
      (MulDistribMulAction.toMulAut G (FO G n) g).toMonoidHom = stepBase G n i :=
    map_refinedTerm_eq 2 _ i 1
  have hK : (stepSucc G n i).map
      (MulDistribMulAction.toMulAut G (FO G n) g).toMonoidHom = stepSucc G n i :=
    map_refinedTerm_eq 2 _ (tauSucc i 1).1 (tauSucc i 1).2
  change Additive.ofMul (Work.Shrinking.quotAut (stepBase G n i) (stepSucc G n i) g hH hK
      (QuotientGroup.mk' ((stepSucc G n i).subgroupOf (stepBase G n i)) ⟨z, hz⟩))
    = Additive.ofMul (QuotientGroup.mk'
        ((stepSucc G n i).subgroupOf (stepBase G n i)) ⟨g • z, hgz⟩)
  rw [Work.Shrinking.quotAut_mk]
  exact congrArg (QuotientGroup.mk' ((stepSucc G n i).subgroupOf (stepBase G n i)))
    (Subtype.ext (Work.Shrinking.subAut_coe (stepBase G n i) g hH ⟨z, hz⟩))

theorem toE_mul (G : Type*) [Group G] (n i : ℕ) {a b : FO G n}
    (ha : a ∈ stepBase G n i) (hb : b ∈ stepBase G n i) (hab : a * b ∈ stepBase G n i) :
    toE G n i (a * b) hab = toE G n i a ha + toE G n i b hb := by
  rw [toE, toE, toE]
  have h : QuotientGroup.mk' ((stepSucc G n i).subgroupOf (stepBase G n i)) ⟨a * b, hab⟩
      = QuotientGroup.mk' ((stepSucc G n i).subgroupOf (stepBase G n i)) ⟨a, ha⟩
        * QuotientGroup.mk' ((stepSucc G n i).subgroupOf (stepBase G n i)) ⟨b, hb⟩ := by
    rw [show (⟨a * b, hab⟩ : stepBase G n i) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl]
    exact map_mul _ _ _
  rw [h, ofMul_mul]

theorem toE_inv (G : Type*) [Group G] (n i : ℕ) {z : FO G n}
    (hz : z ∈ stepBase G n i) (hzi : z⁻¹ ∈ stepBase G n i) :
    toE G n i z⁻¹ hzi = - toE G n i z hz := by
  rw [toE, toE, show (⟨z⁻¹, hzi⟩ : stepBase G n i)
    = (⟨z, hz⟩ : stepBase G n i)⁻¹ from Subtype.ext rfl, map_inv]
  rfl

theorem E_neg_self (G : Type*) [Group G] (n i : ℕ) (x : E 2 G n i 1) : -x = x := by
  have h : (-1 : ZMod 2) = 1 := by decide
  rw [← neg_one_smul (ZMod 2) x, h, one_smul]

theorem smul_mem_stepBase (G : Type*) [Group G] (n i : ℕ) (δ : G) {z : FO G n}
    (hz : z ∈ stepBase G n i) : δ • z ∈ stepBase G n i :=
  Work.Shrinking.mem_smul_mem (stepBase G n i) δ
    (map_refinedTerm_eq 2 (MulDistribMulAction.toMulAut G (FO G n) δ) i 1) hz

theorem toQ_pow_two (G : Type*) [Group G] (n i : ℕ) {z : FO G n} (hz : z ∈ stepBase G n i) :
    toQ G n i z ^ 2 = 1 := by
  have h2 : z ^ 2 ∈ stepSucc G n i := pow_refinedTerm_le 2 i 1 hz
  have h : toQ G n i (z ^ 2) = 1 := by
    rw [toQ]
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    exact Subgroup.mem_subgroupOf.mpr h2
  calc toQ G n i z ^ 2 = toQ G n i z * toQ G n i z := pow_two (toQ G n i z)
    _ = toQ G n i (z * z) := (toQ_mul G n i z z).symm
    _ = toQ G n i (z ^ 2) := by rw [pow_two]
    _ = 1 := h

/-- `γ₂ ∩ F(n)_i` is contained in the kernel of `Q_{(i,2)} → Q_{(i,1)}`. -/
theorem lowerCentralSeries_one_inf_stepBase_le_stepSucc (G : Type*) [Group G] (n i : ℕ)
    (hi : 1 ≤ i) :
    (⊤ : Subgroup (FO G n)).lowerCentralSeries 1 ⊓ stepBase G n i ≤ stepSucc G n i := by
  have hbase : stepBase G n i = refinedTerm 2 (FO G n) i 1 := rfl
  rcases eq_or_lt_of_le hi with h1 | h2
  · subst h1
    have hbtop : refinedTerm 2 (FO G n) 1 1 = ⊤ := by
      rw [refinedTerm_one]; rfl
    have hs : stepSucc G n 1 = Work.Shrinking.pCentralStep 2 (⊤ : Subgroup (FO G n)) := by
      show refinedTerm 2 (FO G n) (tauSucc 1 1).1 (tauSucc 1 1).2 = _
      rw [tauSucc_of_le (le_refl 1), refinedTerm_one]
      rfl
    rw [hbase, hbtop, inf_top_eq, hs]
    exact le_sup_right
  · have hbase' : stepBase G n i = pSeries 2 (FO G n) i := by
      rw [hbase, refinedTerm_one]
    have hs : stepSucc G n i
        = (pSeries 2 (FO G n) i ⊓ centralSeries (FO G n) 2) ⊔ pSeries 2 (FO G n) (i + 1) := by
      show refinedTerm 2 (FO G n) (tauSucc i 1).1 (tauSucc i 1).2 = _
      rw [tauSucc_of_lt h2]
      rfl
    rw [hbase', hs]
    exact (le_of_eq (inf_comm _ _)).trans le_sup_left

/-! ## `F(n)_i` is generated by `2^{i-1}`-st powers modulo `γ₂`

Elementary `p`-central-series computation: the descending `p`-central series is contained in the
subgroup generated by the `p^{k}`-st powers together with the derived subgroup.  This is the only
place where the "generation by power elements" enters; it is universe-polymorphic (contrary to the
specialised version `Work.SSGRoute.prop5.pCentralSeries_le_pow_sup_commutator`), which is why it is
reproduced here. -/

section Generation

/-- Modulo the derived subgroup, `(u v)^n` and `u^n v^n` agree: their quotient lies in the kernel
of the abelianisation. -/
theorem mul_pow_mul_pow_inv_mem_commutator {P : Type*} [Group P] (n : ℕ) (u v : P) :
    (u * v) ^ n * (u ^ n * v ^ n)⁻¹ ∈ (⊤ : Subgroup P).lowerCentralSeries 1 := by
  rw [Subgroup.top_lowerCentralSeries_one, ← Abelianization.ker_of, MonoidHom.mem_ker]
  simp [map_mul, map_pow, mul_pow]

/-- The `p`-th power of an element of the subgroup generated by the `p ^ k`-st powers lies in the
subgroup generated by the `p ^ (k+1)`-st powers together with the derived subgroup. -/
theorem pow_mem_powSubgroup_sup {P : Type*} [Group P] (p k : ℕ) {x : P}
    (hx : x ∈ Work.Shrinking.powSubgroup (p ^ k) (⊤ : Subgroup P)) :
    x ^ p ∈ Work.Shrinking.powSubgroup (p ^ (k + 1)) (⊤ : Subgroup P) ⊔
      (⊤ : Subgroup P).lowerCentralSeries 1 := by
  simp only [Work.Shrinking.powSubgroup] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem z hz =>
      obtain ⟨y, -, rfl⟩ := hz
      apply Subgroup.mem_sup_left
      rw [← pow_mul, ← pow_succ]
      exact Subgroup.subset_closure ⟨y, Subgroup.mem_top y, rfl⟩
  | one => rw [one_pow]; exact Subgroup.one_mem _
  | mul a b ha hb iha ihb =>
      have hkey : (a * b) ^ p = ((a * b) ^ p * (a ^ p * b ^ p)⁻¹) * (a ^ p * b ^ p) := by group
      rw [hkey]
      refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_) (Subgroup.mul_mem _ iha ihb)
      exact mul_pow_mul_pow_inv_mem_commutator p a b
  | inv a ha iha =>
      rw [inv_pow]
      exact Subgroup.inv_mem _ iha

/-- The `p`-th power map preserves `⟨x^{p^k} : x⟩ · γ₂`. -/
theorem sup_pow_mem {P : Type*} [Group P] (p k : ℕ) {x : P}
    (hx : x ∈ Work.Shrinking.powSubgroup (p ^ k) (⊤ : Subgroup P) ⊔
      (⊤ : Subgroup P).lowerCentralSeries 1) :
    x ^ p ∈ Work.Shrinking.powSubgroup (p ^ (k + 1)) (⊤ : Subgroup P) ⊔
      (⊤ : Subgroup P).lowerCentralSeries 1 := by
  set C := Work.Shrinking.powSubgroup (p ^ (k + 1)) (⊤ : Subgroup P) ⊔
    (⊤ : Subgroup P).lowerCentralSeries 1 with hC
  obtain ⟨u, hu, v, hv, huv⟩ := (Subgroup.mem_sup_of_normal_right
    (s := Work.Shrinking.powSubgroup (p ^ k) (⊤ : Subgroup P))
    (t := (⊤ : Subgroup P).lowerCentralSeries 1)).mp hx
  rw [← huv]
  have hu' : u ^ p ∈ C := pow_mem_powSubgroup_sup p k hu
  have hv' : v ^ p ∈ C := Subgroup.mem_sup_right (Subgroup.pow_mem _ hv p)
  have hkey : (u * v) ^ p = ((u * v) ^ p * (u ^ p * v ^ p)⁻¹) * (u ^ p * v ^ p) := by group
  rw [hkey]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_right ?_) (Subgroup.mul_mem _ hu' hv')
  exact mul_pow_mul_pow_inv_mem_commutator p u v

/-- The `k`-th term of the descending `p`-central series is contained in
`⟨x^{p^k} : x⟩ · γ₂`. -/
theorem pCentralSeries_le_powSubgroup_sup (p : ℕ) (P : Type*) [Group P] (k : ℕ) :
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
      rw [Work.Shrinking.pCentralSeries_succ, Work.Shrinking.pCentralStep]
      apply sup_le
      · rw [Work.Shrinking.powSubgroup, Subgroup.closure_le]
        rintro z ⟨y, hy, rfl⟩
        exact sup_pow_mem p k (ih hy)
      · have h : ⁅(⊤ : Subgroup P), ⊤⁆ = (⊤ : Subgroup P).lowerCentralSeries 1 := by
          rw [Subgroup.top_lowerCentralSeries_one, _root_.commutator_def]
        refine le_trans (Subgroup.commutator_mono le_top le_rfl) ?_
        rw [h]
        exact le_sup_right

/-- **The `p`-central series is generated by `p`-th powers modulo the derived subgroup.**  A
universe-polymorphic replacement for
`Work.SSGRoute.prop5.pCentralSeries_le_pow_sup_commutator`. -/
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

/-! ## The equivariant linear map `F(n)/F(n)² → E(n,(i,1))` -/

noncomputable def thetaV (G : Type*) [Group G] [Fintype G] (n i : ℕ) (hi : 1 ≤ i) :
    squareQuotient 2 G n →ₗ[ZMod 2] E 2 G n i 1 where
  toFun v := prop5.thetaLin 2 G i 1 n le_rfl hi
    (PiTensorProduct.tprod (ZMod 2) (fun _ : Fin 1 => v))
  map_add' v w := by
    show prop5.thetaLin 2 G i 1 n le_rfl hi
        (PiTensorProduct.tprod (ZMod 2) (fun _ : Fin 1 => v + w))
      = prop5.thetaLin 2 G i 1 n le_rfl hi
          (PiTensorProduct.tprod (ZMod 2) (fun _ : Fin 1 => v))
        + prop5.thetaLin 2 G i 1 n le_rfl hi
          (PiTensorProduct.tprod (ZMod 2) (fun _ : Fin 1 => w))
    rw [← map_add]
    have hsum : PiTensorProduct.tprod (ZMod 2) (fun _ : Fin 1 => v + w)
        = PiTensorProduct.tprod (ZMod 2) (fun _ : Fin 1 => v)
          + PiTensorProduct.tprod (ZMod 2) (fun _ : Fin 1 => w) := by
      rw [← PiTensorProduct.subsingletonEquiv_symm_apply' (ι := Fin 1) 0 (v + w),
        ← PiTensorProduct.subsingletonEquiv_symm_apply' (ι := Fin 1) 0 v,
        ← PiTensorProduct.subsingletonEquiv_symm_apply' (ι := Fin 1) 0 w]
      exact map_add _ v w
    rw [hsum]
  map_smul' c v := by
    show prop5.thetaLin 2 G i 1 n le_rfl hi
        (PiTensorProduct.tprod (ZMod 2) (fun _ : Fin 1 => c • v))
      = c • prop5.thetaLin 2 G i 1 n le_rfl hi
          (PiTensorProduct.tprod (ZMod 2) (fun _ : Fin 1 => v))
    rw [← map_smul]
    have hsmul : PiTensorProduct.tprod (ZMod 2) (fun _ : Fin 1 => c • v)
        = c • PiTensorProduct.tprod (ZMod 2) (fun _ : Fin 1 => v) := by
      rw [← PiTensorProduct.subsingletonEquiv_symm_apply' (ι := Fin 1) 0 (c • v),
        ← PiTensorProduct.subsingletonEquiv_symm_apply' (ι := Fin 1) 0 v]
      exact map_smul _ c v
    rw [hsmul]

theorem thetaV_apply (G : Type*) [Group G] [Fintype G] (n i : ℕ) (hi : 1 ≤ i)
    (v : squareQuotient 2 G n) :
    thetaV G n i hi v = prop5.valFn 2 G i 1 n le_rfl hi (fun _ : Fin 1 => prop5.repOf 2 G n v) := by
  show prop5.thetaLin 2 G i 1 n le_rfl hi
    (PiTensorProduct.tprod (ZMod 2) (fun _ : Fin 1 => v)) = _
  rw [prop5.thetaLin_tprod, prop5.thetaFun_eq]
  rfl

theorem thetaV_qmk (G : Type*) [Group G] [Fintype G] (n i : ℕ) (hi : 1 ≤ i) (z : FO G n) :
    thetaV G n i hi (prop5.qmk 2 G n z)
      = toE G n i (z ^ (2 ^ (i - 1))) (pow_mem_stepBase G n i hi z) := by
  rw [thetaV_apply]
  rw [prop5.valFn_congr 2 G i 1 n le_rfl hi (fun _ => by
    show prop5.qmk 2 G n (prop5.repOf 2 G n (prop5.qmk 2 G n z)) = prop5.qmk 2 G n z
    rw [prop5.repOf_spec])]
  rw [prop5.valFn_eq, prop5.valFnOf]
  rfl

theorem thetaV_smul (G : Type*) [Group G] [Fintype G] (n i : ℕ) (hi : 1 ≤ i) (g : G)
    (v : squareQuotient 2 G n) :
    thetaV G n i hi (g • v) = g • thetaV G n i hi v := by
  show prop5.thetaLin 2 G i 1 n le_rfl hi
      (PiTensorProduct.tprod (ZMod 2) (fun _ : Fin 1 => g • v))
    = g • prop5.thetaLin 2 G i 1 n le_rfl hi
      (PiTensorProduct.tprod (ZMod 2) (fun _ : Fin 1 => v))
  have h : PiTensorProduct.tprod (ZMod 2) (fun _ : Fin 1 => g • v)
      = g • PiTensorProduct.tprod (ZMod 2) (fun _ : Fin 1 => v) := by
    rw [Work.Shrinking.smul_tensorPower_eq_map (p := 2) (M := squareQuotient 2 G n) 1 g,
      PiTensorProduct.map_tprod]
    rfl
  rw [h, prop5.thetaLin_smul]

theorem thetaV_injective (G : Type*) [Group G] [Fintype G] (n i : ℕ) (hi : 1 ≤ i) :
    Function.Injective (thetaV G n i hi) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  rw [thetaV_apply] at hv
  have h : prop5.qmk 2 G n (prop5.repOf 2 G n v) = 0 :=
    valFn_eq_zero_imp_qmk_eq_zero G n i hi (prop5.repOf 2 G n v) hv
  rw [← prop5.repOf_spec 2 G n v]
  exact h

/-- Surjectivity: `E(n,(i,1))` is generated by the classes of the `2^{i-1}`-st powers of all
elements of `F(n)` (this is the elementary content of Proposition 5 for `j = 1`). -/
theorem thetaV_surjective (G : Type*) [Group G] [Fintype G] (n i : ℕ) (hi : 1 ≤ i) :
    Function.Surjective (thetaV G n i hi) := by
  set S : Subgroup (FO G n) :=
    Subgroup.closure {y : FO G n | ∃ w : FO G n, y = w ^ (2 ^ (i - 1))} with hSdef
  have hSle : S ≤ stepBase G n i := by
    rw [hSdef, Subgroup.closure_le]
    rintro y ⟨w, rfl⟩
    exact pow_mem_stepBase G n i hi w
  have key : ∀ u ∈ S, ∀ hu : u ∈ stepBase G n i,
      ∃ v : squareQuotient 2 G n, thetaV G n i hi v = toE G n i u hu := by
    intro u hu
    induction hu using Subgroup.closure_induction with
    | mem y hy =>
        intro hb
        obtain ⟨w, rfl⟩ := hy
        exact ⟨prop5.qmk 2 G n w, thetaV_qmk G n i hi w⟩
    | one =>
        intro hb
        exact ⟨0, by rw [map_zero, toE_one G n i hb]⟩
    | mul a b ha hb iha ihb =>
        intro hab
        obtain ⟨v1, hv1⟩ := iha (hSle ha)
        obtain ⟨v2, hv2⟩ := ihb (hSle hb)
        refine ⟨v1 + v2, ?_⟩
        rw [map_add, hv1, hv2, toE_mul G n i (hSle ha) (hSle hb) hab]
    | inv a ha iha =>
        intro hinv
        obtain ⟨v1, hv1⟩ := iha (hSle ha)
        refine ⟨-v1, ?_⟩
        rw [map_neg, hv1, ← toE_inv G n i (hSle ha) (hSle (Subgroup.inv_mem _ ha))]
  intro x
  obtain ⟨Z, hZ⟩ := QuotientGroup.mk'_surjective
    ((stepSucc G n i).subgroupOf (stepBase G n i)) (Additive.toMul x)
  have hZ' : toE G n i Z.1 Z.2 = x := by
    show Additive.ofMul (QuotientGroup.mk' _ Z) = x
    rw [hZ]
    rfl
  obtain ⟨u, huS, c, hcγ, huc⟩ := (Subgroup.mem_sup_of_normal_right (s := S)
    (t := (⊤ : Subgroup (FO G n)).lowerCentralSeries 1)).mp (by
      rw [hSdef]
      have hZS : Z.1 ∈ Work.Shrinking.pCentralSeries 2 (FO G n) (i - 1) := by
        have h : Z.1 ∈ refinedTerm 2 (FO G n) i 1 := Z.2
        rwa [refinedTerm_one] at h
      exact pCentralSeries_le_pow_sup_commutator' 2 i hi hZS)
  have huB : u ∈ stepBase G n i := hSle huS
  have hcB : c ∈ stepBase G n i := by
    have hc_eq : c = u⁻¹ * Z.1 := by rw [← huc]; group
    rw [hc_eq]
    exact (stepBase G n i).mul_mem (Subgroup.inv_mem _ huB) Z.2
  have hcSS : c ∈ stepSucc G n i :=
    lowerCentralSeries_one_inf_stepBase_le_stepSucc G n i hi
      (Subgroup.mem_inf.mpr ⟨hcγ, hcB⟩)
  obtain ⟨v, hv⟩ := key u huS huB
  refine ⟨v, ?_⟩
  rw [← hZ', hv]
  have hZeq : toE G n i Z.1 Z.2 = toE G n i u huB + toE G n i c hcB := by
    have hucB : u * c ∈ stepBase G n i := by rw [huc]; exact Z.2
    have h1 : toE G n i (u * c) hucB = toE G n i Z.1 Z.2 :=
      toE_eq_of_mem_stepSucc G n i hucB Z.2
        (by rw [huc, inv_mul_cancel]; exact (stepSucc G n i).one_mem)
    rw [← h1, toE_mul G n i huB hcB hucB]
  have hc0 : toE G n i c hcB = 0 := by
    rw [toE_eq_of_mem_stepSucc G n i hcB (Subgroup.one_mem _)
        (by rw [mul_one]; exact (stepSucc G n i).inv_mem hcSS),
      toE_one G n i (Subgroup.one_mem _)]
  rw [hZeq, hc0, add_zero]

/-- **Every `δ`-fixed element of the graded piece `E(n,(i,1))` is a `δ`-difference.** -/
theorem E_fixed_is_delta_difference (G : Type*) [Group G] [Fintype G] (n i : ℕ) (hi : 1 ≤ i)
    (δ : G) (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ x : E 2 G n i 1, δ • x = x → ∃ y : E 2 G n i 1, x = δ • y - y := by
  rcases eq_or_lt_of_le hi with h1 | h2
  · subst h1
    exact E_one_one_fixed_is_delta_difference G n δ hδ hδ1
  · intro x hx
    obtain ⟨w, hw⟩ := thetaV_surjective G n i hi x
    rw [← hw] at hx ⊢
    have hwfix : δ • w = w := by
      apply thetaV_injective G n i hi
      rw [thetaV_smul G n i hi δ w]
      exact hx
    obtain ⟨u, hu⟩ := squareQuotient_fixed_is_delta_difference G n δ hδ hδ1 w hwfix
    refine ⟨thetaV G n i hi u, ?_⟩
    rw [hu, map_sub, thetaV_smul G n i hi δ u]

end JOne

/-- **The `j = 1` half of the level-by-level graded step of the `p = 2` correction.**

For a finite group `G`, an involution `δ ∈ G` with `δ ≠ 1`, `n ∈ ℕ`, and every `σ = (i,1)` with
`i ≥ 1`: every element `c` of the kernel of `Q_{(i,2)} → Q_{(i,1)}` which is anti-fixed under the
induced action of `δ` is a `δ`-difference in the ambient group `Q_{(i,2)} = F(n)/F(n)^{(i,2)}`.

The kernel is the graded piece `E(i,1) = F(n)_i/((F(n)_i ∩ γ₂)F(n)_{i+1})`, which is generated by the
images of the `2^{i-1}`-th powers of the free generators, on which `δ` acts by a free permutation.
Every `δ`-fixed element is a sum of free orbits and is a `δ`-difference in the ambient group: take `e`
to be the product of one half of each orbit, the error being a product of commutators
`[x^{2^{i-1}}, (δ x)^{2^{i-1}}] ∈ [F(n)_i, F(n)_i] ⊆ F(n)_{i+1} ⊆ F(n)^{(i,2)}`.

This is a strict piece of the family `Work.SSGRoute.GradedStep`
(`Submission/Work/SSGRoute/two_torsion_assembly.lean`), the `j ≥ 2` pieces being
`Work.SSGRoute.gradedStepJGeTwo`.  The case `i = 1` is
`Work.SSGRoute.E_one_one_fixed_is_delta_difference` of
`Submission/Work/SSGRoute/two_torsion_base.lean` (the transfer of
`Work.SSGRoute.squareQuotient_fixed_is_delta_difference` along the canonical identification
`F(n)/F(n)^2 ≅ E(2,G,n,1,1)`).

NOTE for the prover: the module `Submission/Work/SSGRoute/two_torsion_base.lean` carries the base
case in the vocabulary of the graded piece, and `Submission/Work/SSGRoute/two_torsion_assembly.lean`
the descent that consumes `GradedStep`.  The reduction of the `2^{i-1}`-power elements to the free
`δ`-permutation of the basis can be done with `Work.SSGRoute.prop5Data_exists` together with the
`2`-power part of the refinement `Work.SSGRoute.prop5.pCentralSeries_le_pow_sup_commutator`.
Please do **not** import `Submission.Work.SSGRoute.two_torsion_lift_two`, nor
`Submission.Work.SSGRoute.gradedStep_j_one` (that module must be able to import *this* one). -/
theorem gradedStepJOne (G : Type*) [Group G] [Fintype G] (n : ℕ) (δ : G) (hδ : δ * δ = 1)
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
  obtain ⟨Z, hZ⟩ := QuotientGroup.mk'_surjective
    ((JOne.stepSucc G n i).subgroupOf (⊤ : Subgroup (JOne.FO G n))) c
  have hc : JOne.toQ G n i Z.1 = c := by
    rw [JOne.toQ]
    exact (congrArg (QuotientGroup.mk'
      ((JOne.stepSucc G n i).subgroupOf (⊤ : Subgroup (JOne.FO G n)))) (Subtype.ext rfl)).trans hZ
  have hZmem : Z.1 ∈ JOne.stepBase G n i := by
    have h := hker
    rw [← hc, JOne.toQ] at h
    rw [flowQuotSucc_mk] at h
    exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h)
  have hc2 : c ^ 2 = 1 := by
    rw [← hc]
    exact JOne.toQ_pow_two G n i hZmem
  have hc2' : c * c = 1 := by
    rw [pow_two] at hc2
    exact hc2
  have hfix : flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 δ c = c := by
    rw [hanti, inv_eq_of_mul_eq_one_right hc2']
  have hxfix : δ • JOne.toE G n i Z.1 hZmem = JOne.toE G n i Z.1 hZmem := by
    rw [JOne.toE_smul G n i δ hZmem (JOne.smul_mem_stepBase G n i δ hZmem)]
    refine JOne.toE_eq_of_mem_stepSucc G n i _ _ ?_
    refine (JOne.toQ_eq_iff G n i).mp ?_
    rw [← JOne.toQ_smul G n i δ Z.1, hc, hfix]
  obtain ⟨y, hy⟩ := JOne.E_fixed_is_delta_difference G n i hi δ hδ hδ1
    (JOne.toE G n i Z.1 hZmem) hxfix
  obtain ⟨W, hW⟩ := QuotientGroup.mk'_surjective
    ((JOne.stepSucc G n i).subgroupOf (JOne.stepBase G n i)) (Additive.toMul y)
  have hWy : JOne.toE G n i W.1 W.2 = y := by
    show Additive.ofMul (QuotientGroup.mk' _ W) = y
    rw [hW]
    rfl
  refine ⟨JOne.toQ G n i W.1, ?_⟩
  have hδW : δ • W.1 ∈ JOne.stepBase G n i := JOne.smul_mem_stepBase G n i δ W.2
  have hprod : (δ • W.1)⁻¹ * W.1 ∈ JOne.stepBase G n i :=
    (JOne.stepBase G n i).mul_mem (Subgroup.inv_mem _ hδW) W.2
  have h1 : (flowAction 2 G n (tauSucc i 1).1 (tauSucc i 1).2 δ (JOne.toQ G n i W.1))⁻¹
      * JOne.toQ G n i W.1 = JOne.toQ G n i ((δ • W.1)⁻¹ * W.1) := by
    rw [JOne.toQ_smul G n i δ W.1, ← JOne.toQ_inv G n i (δ • W.1),
      ← JOne.toQ_mul G n i _ _]
  have hE : JOne.toE G n i ((δ • W.1)⁻¹ * W.1) hprod = JOne.toE G n i Z.1 hZmem := by
    rw [JOne.toE_mul G n i (Subgroup.inv_mem _ hδW) W.2 hprod,
      JOne.toE_inv G n i hδW (Subgroup.inv_mem _ hδW),
      ← JOne.toE_smul G n i δ W.2 hδW, hWy]
    rw [JOne.E_neg_self G n i (δ • y), hy, sub_eq_add_neg, JOne.E_neg_self G n i y]
  have h2 : JOne.toQ G n i ((δ • W.1)⁻¹ * W.1) = c := by
    rw [← hc]
    exact (JOne.toQ_eq_iff G n i).mpr ((JOne.toE_eq_iff G n i hprod hZmem).mp hE)
  exact (h1.trans h2).symm

end Work.SSGRoute
