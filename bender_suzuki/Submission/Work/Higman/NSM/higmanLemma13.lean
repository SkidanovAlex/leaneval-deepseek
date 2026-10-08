import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.chevalley_warning
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.center_eq_omega1_new
import Submission.Work.Higman.lemma9_maximal_abelian
import Submission.Work.Higman.MSA.lemma8_clean
import Submission.Work.Higman.NSM.dsq_setup
import Submission.Work.Higman.NSM.dsq_caseB

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Work.Higman.NSM

open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

/-! ## Chevalley–Warning bound for a group of class two

Self-contained copy of the commutator algebra of `Submission/Work/Higman/card_eq_sq_or_cube.lean`
(that module lies on an import cycle, so it cannot be imported here). -/

/-- `x * y * x⁻¹ = [x,y] * y`. -/
theorem czh_mul_mul_inv_eq_commutator_mul {G : Type*} [Group G] (x y : G) :
    x * y * x⁻¹ = ⁅x, y⁆ * y := by
  rw [commutatorElement_def]; group

/-- In a group of class two every commutator is central. -/
theorem czh_commutator_central_comm {G : Type*} [Group G]
    (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y z : G) :
    z * ⁅x, y⁆ = ⁅x, y⁆ * z :=
  Subgroup.mem_center_iff.mp
    (hZ (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))) z

/-- Class two: `[x * y, z] = [x,z] * [y,z]`. -/
theorem czh_commutator_mul_left {G : Type*} [Group G]
    (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y z : G) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have hcy : ∀ w : G, w * ⁅y, z⁆ = ⁅y, z⁆ * w := czh_commutator_central_comm hZ y z
  have hcx : ∀ w : G, w * ⁅x, z⁆ = ⁅x, z⁆ * w := czh_commutator_central_comm hZ x z
  have h1 : x * z * x⁻¹ = ⁅x, z⁆ * z := czh_mul_mul_inv_eq_commutator_mul x z
  have h2 : y * z * y⁻¹ = ⁅y, z⁆ * z := czh_mul_mul_inv_eq_commutator_mul y z
  rw [commutatorElement_def]
  rw [show x * y * z * (x * y)⁻¹ * z⁻¹ = x * (y * z * y⁻¹) * x⁻¹ * z⁻¹ by group]
  rw [h2]
  rw [show x * (⁅y, z⁆ * z) * x⁻¹ * z⁻¹ = (x * ⁅y, z⁆) * (z * x⁻¹) * z⁻¹ by group]
  rw [hcy x]
  rw [show (⁅y, z⁆ * x) * (z * x⁻¹) * z⁻¹ = ⁅y, z⁆ * (x * z * x⁻¹) * z⁻¹ by group]
  rw [h1]
  rw [show ⁅y, z⁆ * (⁅x, z⁆ * z) * z⁻¹ = ⁅y, z⁆ * ⁅x, z⁆ by group]
  rw [hcx ⁅y, z⁆]

/-- Class two: `[z, x * y] = [z, x] * [z, y]`. -/
theorem czh_commutator_mul_right {G : Type*} [Group G]
    (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y z : G) :
    ⁅z, x * y⁆ = ⁅z, x⁆ * ⁅z, y⁆ := by
  have h1 : ⁅z, x * y⁆ = ⁅x * y, z⁆⁻¹ := by rw [← commutatorElement_inv]
  rw [h1, czh_commutator_mul_left hZ x y z, mul_inv_rev, commutatorElement_inv,
    commutatorElement_inv]
  exact (czh_commutator_central_comm hZ z y ⁅z, x⁆).symm

/-- A central element commutes out of a commutator on the left. -/
theorem czh_commutator_eq_one_of_mem_center_left {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (x : G) : ⁅z, x⁆ = 1 := by
  rw [commutatorElement_def, ← Subgroup.mem_center_iff.mp hz x]
  group

/-- A central element commutes out of a commutator on the right. -/
theorem czh_commutator_eq_one_of_mem_center_right {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (x : G) : ⁅x, z⁆ = 1 := by
  rw [commutatorElement_def, Subgroup.mem_center_iff.mp hz x]
  group

/-- **Chevalley–Warning bound.**  If `Z(P) = Ω₁(P)`, every square is central and `P` has class
two, then `|P / Z(P)| ≤ |Z(P)|²`. -/
theorem card_quotient_center_le_sq_nsm (h : IsSuzuki2Grp P)
    (hZ : Subgroup.center P = omega1 P)
    (hsq : ∀ x : P, x ^ 2 ∈ Subgroup.center P)
    (hcommZ : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P) :
    Nat.card (P ⧸ Subgroup.center P) ≤ Nat.card ↥(Subgroup.center P) ^ 2 := by
  classical
  have hZ2 : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P := hcommZ
  have hsq2 : ∀ g : P, g * g ∈ Subgroup.center P := fun g => by
    have h1 := hsq g
    rwa [pow_two] at h1
  have hqcomm : ∀ a b : P ⧸ Subgroup.center P, a * b = b * a := by
    intro a b
    refine Quotient.inductionOn a (fun x => ?_)
    refine Quotient.inductionOn b (fun y => ?_)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hmem : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
      rw [commutatorElement_def]; group
    rw [hmem]
    exact hZ2 (Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _))
  letI : CommGroup (P ⧸ Subgroup.center P) :=
    { (inferInstance : Group (P ⧸ Subgroup.center P)) with mul_comm := hqcomm }
  letI : CommGroup ↥(Subgroup.center P) :=
    { (inferInstance : Group ↥(Subgroup.center P)) with
      mul_comm := fun a b => Subtype.ext ((Subgroup.mem_center_iff.mp b.2) (a : P)) }
  let mkc : P → Additive (P ⧸ Subgroup.center P) :=
    fun z => Additive.ofMul (QuotientGroup.mk z)
  have h2V : ∀ v : Additive (P ⧸ Subgroup.center P), (2 : ℕ) • v = 0 := by
    intro v
    refine Quotient.inductionOn v (fun x => ?_)
    change (2 : ℕ) • Additive.ofMul (QuotientGroup.mk x) = 0
    rw [← ofMul_pow, ofMul_eq_zero]
    have hxx : ((x * x : P) : P ⧸ Subgroup.center P) = 1 :=
      (QuotientGroup.eq_one_iff (N := Subgroup.center P) (x * x)).mpr (hsq2 x)
    simpa [pow_two] using hxx
  haveI hmodV : Module (ZMod 2) (Additive (P ⧸ Subgroup.center P)) :=
    AddCommGroup.zmodModule h2V
  have h2W : ∀ v : Additive ↥(Subgroup.center P), (2 : ℕ) • v = 0 := by
    intro v
    rw [← ofMul_toMul v, ← ofMul_pow]
    simp only [ofMul_eq_zero]
    apply Subtype.ext
    change ((v.toMul : ↥(Subgroup.center P)) : P) ^ 2 = 1
    have h1 : ((v.toMul : ↥(Subgroup.center P)) : P) ∈ omega1 P := by
      rw [← hZ]; exact (v.toMul).2
    exact h.mem_omega1.mp h1
  haveI hmodW : Module (ZMod 2) (Additive ↥(Subgroup.center P)) :=
    AddCommGroup.zmodModule h2W
  let qf : P → ↥(Subgroup.center P) := fun g => ⟨g * g, by simpa [pow_two] using hsq g⟩
  have hqw : ∀ a b : P, a⁻¹ * b ∈ Subgroup.center P → qf a = qf b := by
    intro a b hab
    obtain ⟨z, hz, rfl⟩ : ∃ z ∈ Subgroup.center P, b = a * z := ⟨a⁻¹ * b, hab, by group⟩
    apply Subtype.ext
    show a * a = (a * z) * (a * z)
    have hzc : z * z = 1 := by
      have h1 : z ∈ omega1 P := by rw [← hZ]; exact hz
      have h2 := h.mem_omega1.mp h1
      rwa [pow_two] at h2
    have hc : z * a = a * z := (Subgroup.mem_center_iff.mp hz a).symm
    calc a * a = a * a * (z * z) := by rw [hzc, mul_one]
      _ = a * (a * (z * z)) := by group
      _ = a * ((a * z) * z) := by group
      _ = a * ((z * a) * z) := by rw [hc]
      _ = (a * z) * (a * z) := by group
  have hqw' : ∀ a b : P, (QuotientGroup.leftRel (Subgroup.center P)) a b →
      Additive.ofMul (qf a) = Additive.ofMul (qf b) :=
    fun a b hab => congrArg Additive.ofMul (hqw a b (QuotientGroup.leftRel_apply.mp hab))
  let Q : Additive (P ⧸ Subgroup.center P) → Additive ↥(Subgroup.center P) :=
    fun v => Quotient.liftOn v.toMul (fun g => Additive.ofMul (qf g)) hqw'
  have Q_mk : ∀ g : P, Q (mkc g) = Additive.ofMul (qf g) :=
    fun g => congrArg Additive.ofMul
      (Quotient.liftOn_mk (s := QuotientGroup.leftRel (Subgroup.center P))
        (fun g => Additive.ofMul (qf g)) hqw' g)
  have Q_zero : Q 0 = 0 := by
    change Q (mkc 1) = 0
    rw [Q_mk, ofMul_eq_zero]
    apply Subtype.ext
    show (1 : P) * 1 = 1
    group
  have Q_aniso : ∀ v, Q v = 0 → v = 0 := by
    intro v
    refine Quotient.inductionOn v (fun g => ?_)
    intro hv
    have hv' : Q (mkc g) = 0 := hv
    rw [Q_mk, ofMul_eq_zero] at hv'
    have hg : g * g = 1 := congrArg Subtype.val hv'
    have hg2 : g ^ 2 = 1 := by rw [pow_two]; exact hg
    change mkc g = 0
    rw [ofMul_eq_zero, QuotientGroup.eq_one_iff, hZ]
    exact h.mem_omega1.mpr hg2
  let bZ : P → P → ↥(Subgroup.center P) :=
    fun x y => ⟨⁅y, x⁆, hcommZ (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top y) (Subgroup.mem_top x))⟩
  have bZ_mul₁ : ∀ a b y : P, bZ (a * b) y = bZ a y * bZ b y := by
    intro a b y
    apply Subtype.ext
    show ⁅y, a * b⁆ = ⁅y, a⁆ * ⁅y, b⁆
    exact czh_commutator_mul_right hZ2 a b y
  have bZ_mul₂ : ∀ y a b : P, bZ y (a * b) = bZ y a * bZ y b := by
    intro y a b
    apply Subtype.ext
    show ⁅a * b, y⁆ = ⁅a, y⁆ * ⁅b, y⁆
    exact czh_commutator_mul_left hZ2 a b y
  have bZ_wd : ∀ a₁ b₁ a₂ b₂ : P,
      (QuotientGroup.leftRel (Subgroup.center P)) a₁ a₂ →
      (QuotientGroup.leftRel (Subgroup.center P)) b₁ b₂ → bZ a₁ b₁ = bZ a₂ b₂ := by
    intro a₁ b₁ a₂ b₂ ha hb
    obtain ⟨z, hz, rfl⟩ : ∃ z ∈ Subgroup.center P, a₂ = a₁ * z :=
      ⟨a₁⁻¹ * a₂, QuotientGroup.leftRel_apply.mp ha, by group⟩
    obtain ⟨w, hw, rfl⟩ : ∃ w ∈ Subgroup.center P, b₂ = b₁ * w :=
      ⟨b₁⁻¹ * b₂, QuotientGroup.leftRel_apply.mp hb, by group⟩
    apply Subtype.ext
    show ⁅b₁, a₁⁆ = ⁅b₁ * w, a₁ * z⁆
    rw [czh_commutator_mul_left hZ2 b₁ w (a₁ * z),
        czh_commutator_eq_one_of_mem_center_left hw (a₁ * z), mul_one,
        czh_commutator_mul_right hZ2 a₁ z b₁,
        czh_commutator_eq_one_of_mem_center_right hz b₁, mul_one]
  let bZq : Additive (P ⧸ Subgroup.center P) → Additive (P ⧸ Subgroup.center P) →
      Additive ↥(Subgroup.center P) :=
    fun v w => Additive.ofMul (Quotient.liftOn₂ v.toMul w.toMul bZ bZ_wd)
  have bZq_mk : ∀ x y : P, bZq (mkc x) (mkc y) = Additive.ofMul (bZ x y) :=
    fun x y => congrArg Additive.ofMul (Quotient.liftOn₂_mk bZ bZ_wd x y)
  have hsum : ∀ x y : P, mkc x + mkc y = mkc (x * y) := by
    intro x y
    show Additive.ofMul (QuotientGroup.mk x) + Additive.ofMul (QuotientGroup.mk y) =
      Additive.ofMul (QuotientGroup.mk (x * y))
    rw [← ofMul_mul, ← QuotientGroup.mk_mul]
  have bZq_zero₁ : ∀ w : Additive (P ⧸ Subgroup.center P), bZq 0 w = 0 := by
    intro w
    refine Quotient.inductionOn w (fun z => ?_)
    change bZq (mkc 1) (mkc z) = 0
    rw [bZq_mk 1 z, ofMul_eq_zero]
    apply Subtype.ext
    show ⁅z, 1⁆ = 1
    rw [commutatorElement_def]; group
  have bZq_zero₂ : ∀ w : Additive (P ⧸ Subgroup.center P), bZq w 0 = 0 := by
    intro w
    refine Quotient.inductionOn w (fun z => ?_)
    change bZq (mkc z) (mkc 1) = 0
    rw [bZq_mk z 1, ofMul_eq_zero]
    apply Subtype.ext
    show ⁅1, z⁆ = 1
    rw [commutatorElement_def]; group
  have bZq_add₁ : ∀ v₁ v₂ w : Additive (P ⧸ Subgroup.center P),
      bZq (v₁ + v₂) w = bZq v₁ w + bZq v₂ w := by
    intro v₁ v₂ w
    refine Quotient.inductionOn v₁ (fun x => ?_)
    refine Quotient.inductionOn v₂ (fun y => ?_)
    refine Quotient.inductionOn w (fun z => ?_)
    change bZq (mkc x + mkc y) (mkc z) = bZq (mkc x) (mkc z) + bZq (mkc y) (mkc z)
    rw [hsum x y, bZq_mk (x * y) z, bZq_mk x z, bZq_mk y z, ← ofMul_mul, ← bZ_mul₁ x y z]
  have bZq_add₂ : ∀ v w₁ w₂ : Additive (P ⧸ Subgroup.center P),
      bZq v (w₁ + w₂) = bZq v w₁ + bZq v w₂ := by
    intro v w₁ w₂
    refine Quotient.inductionOn v (fun z => ?_)
    refine Quotient.inductionOn w₁ (fun x => ?_)
    refine Quotient.inductionOn w₂ (fun y => ?_)
    change bZq (mkc z) (mkc x + mkc y) = bZq (mkc z) (mkc x) + bZq (mkc z) (mkc y)
    rw [hsum x y, bZq_mk z (x * y), bZq_mk z x, bZq_mk z y, ← ofMul_mul, ← bZ_mul₂ z x y]
  have bZq_smul₁ : ∀ (c : ZMod 2) (v w : Additive (P ⧸ Subgroup.center P)),
      bZq (c • v) w = c • bZq v w := by
    intro c v w
    let φ : Additive (P ⧸ Subgroup.center P) →+ Additive ↥(Subgroup.center P) :=
      { toFun := fun x => bZq x w
        map_zero' := bZq_zero₁ w
        map_add' := fun x y => bZq_add₁ x y w }
    exact ZMod.map_smul φ c v
  have bZq_smul₂ : ∀ (c : ZMod 2) (v w : Additive (P ⧸ Subgroup.center P)),
      bZq v (c • w) = c • bZq v w := by
    intro c v w
    let φ : Additive (P ⧸ Subgroup.center P) →+ Additive ↥(Subgroup.center P) :=
      { toFun := fun x => bZq v x
        map_zero' := bZq_zero₂ v
        map_add' := fun x y => bZq_add₂ v x y }
    exact ZMod.map_smul φ c w
  let b : Additive (P ⧸ Subgroup.center P) →ₗ[ZMod 2]
      Additive (P ⧸ Subgroup.center P) →ₗ[ZMod 2] Additive ↥(Subgroup.center P) :=
    LinearMap.mk₂ (ZMod 2) bZq bZq_add₁ bZq_smul₁ bZq_add₂ bZq_smul₂
  have hb : ∀ v w, Q (v + w) = Q v + Q w + b v w := by
    intro v w
    refine Quotient.inductionOn v (fun x => ?_)
    refine Quotient.inductionOn w (fun y => ?_)
    change Q (mkc x + mkc y) = Q (mkc x) + Q (mkc y) + bZq (mkc x) (mkc y)
    rw [hsum x y, Q_mk, Q_mk x, Q_mk y, bZq_mk x y, ← ofMul_mul, ← ofMul_mul]
    congr 1
    apply Subtype.ext
    show (x * y) * (x * y) = (x * x) * (y * y) * ⁅y, x⁆
    have hc : ⁅y, x⁆ ∈ Subgroup.center P := hcommZ (Subgroup.commutator_mem_commutator
      (Subgroup.mem_top y) (Subgroup.mem_top x))
    have h1 : ⁅y, x⁆ * x = x * ⁅y, x⁆ := (Subgroup.mem_center_iff.mp hc x).symm
    have h2 : ⁅y, x⁆ * y = y * ⁅y, x⁆ := (Subgroup.mem_center_iff.mp hc y).symm
    have hcyx : y * x = ⁅y, x⁆ * x * y := by rw [commutatorElement_def]; group
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (⁅y, x⁆ * x * y) * y := by rw [hcyx]
      _ = (x * x) * (y * y) * ⁅y, x⁆ := by
            calc x * (⁅y, x⁆ * x * y) * y = x * (x * (⁅y, x⁆ * y)) * y := by
                  rw [h1]; group
              _ = x * (x * (y * ⁅y, x⁆)) * y := by rw [h2]
              _ = x * (x * y) * (⁅y, x⁆ * y) := by group
              _ = x * (x * y) * (y * ⁅y, x⁆) := by rw [h2]
              _ = (x * x) * (y * y) * ⁅y, x⁆ := by group
  exact card_le_sq_of_quadratic_anisotropic (V := Additive (P ⧸ Subgroup.center P))
    (W := Additive ↥(Subgroup.center P)) Q Q_zero b hb Q_aniso

/-- If `P` has class two, `Z(P) = Ω₁(P)` and every square is central, then
`|P| ≤ |Z(P)|³`. -/
theorem card_le_cube_of_class_two (h : IsSuzuki2Grp P)
    (hZ : Subgroup.center P = omega1 P)
    (hsq : ∀ x : P, x ^ 2 ∈ Subgroup.center P)
    (hcommZ : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P) :
    Nat.card P ≤ Nat.card ↥(Subgroup.center P) ^ 3 := by
  have h1 : Nat.card P = Nat.card (P ⧸ Subgroup.center P) * Nat.card ↥(Subgroup.center P) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 := card_quotient_center_le_sq_nsm h hZ hsq hcommZ
  calc Nat.card P = Nat.card (P ⧸ Subgroup.center P) * Nat.card ↥(Subgroup.center P) := h1
    _ ≤ Nat.card ↥(Subgroup.center P) ^ 2 * Nat.card ↥(Subgroup.center P) :=
        Nat.mul_le_mul_right _ h2
    _ = Nat.card ↥(Subgroup.center P) ^ 3 := by ring

/-! ## The `ξ`-invariant subgroups of `A`

`A` is homocyclic of exponent `2 ^ e` with `e ≤ 2`, so its `ξ`-invariant subgroups are
`⊥`, `A²` and `A`. -/

theorem xi_inv_sub_dichotomy_nsm (h : IsSuzuki2Grp P) {A : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    {B : Subgroup P} (hBA : B ≤ A) (hBinv : B.map (h.xi : MulAut P).toMonoidHom = B) :
    B = ⊥ ∨ B = Work.Higman.powSub A 2 ∨ B = A := by
  obtain ⟨e, hexp, hcard, htop, hsub⟩ := homogeneous_structure h hAab hAinv
  obtain ⟨i, hi⟩ := hsub B hBA hBinv
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · exact Or.inr (Or.inr (by rw [hi, h0, pow_zero, Work.Higman.powSub_one_eq]))
  · rcases Nat.lt_or_ge i 2 with hlt | hge
    · exact Or.inr (Or.inl (by
        have hi1 : i = 1 := by omega
        rw [hi, hi1]; norm_num))
    · exact Or.inl (by
        rw [hi]
        have hdvd : 4 ∣ 2 ^ i := ⟨2 ^ (i - 2), by
          have hi : i = 2 + (i - 2) := by omega
          rw [hi, pow_add]; norm_num⟩
        exact le_bot_iff.mp (hA4 ▸ Work.Higman.powSub_le_of_dvd hAab hdvd))

/-- The derived subgroup of a `ξ`-invariant normal subgroup lies in `A`, hence is `⊥`, `A²`
or `A`. -/
theorem dComm_dichotomy_nsm (h : IsSuzuki2Grp P) {A D : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D) :
    ⁅D, D⁆ = ⊥ ∨ ⁅D, D⁆ = Work.Higman.powSub A 2 ∨ ⁅D, D⁆ = A := by
  have hle : ⁅D, D⁆ ≤ A := by
    rw [← hGs]
    exact Subgroup.commutator_mono le_top le_top
  have hinv : (⁅D, D⁆).map (h.xi : MulAut P).toMonoidHom = ⁅D, D⁆ := by
    rw [Subgroup.map_commutator, hDinv]
  exact xi_inv_sub_dichotomy_nsm h hAab hAinv hA4 hle hinv

/-! ## Powers of `ξ` fixing one non-identity element

The Suzuki automorphism `ξ` is coarse in the following sense: if `ξ ^ k` fixes a single
non-identity element `x`, then `ξ ^ k` fixes *every* element of `Ω₁(P)`.  Indeed `x` has order
`2 ^ r`, so `x ^ (2 ^ (r - 1))` is an involution fixed by `ξ ^ k`; by the transitivity of `ξ` on
the involutions every involution is a `ξ`-conjugate of it, hence also fixed. -/

/-- **A power of `ξ` fixing one non-identity element fixes every involution.**  Indeed `x` has
order `2 ^ r`, so `x ^ (2 ^ (r - 1))` is an involution fixed by `ξ ^ k`; every involution is
`ξ ^ j`-conjugate to it by transitivity, hence also fixed. -/
theorem xi_pow_fixes_involutions_of_fixes_ne_one (h : IsSuzuki2Grp P) {k : ℕ} {x : P}
    (hx : x ≠ 1) (hfix : (h.xi ^ k) x = x) :
    ∀ z : P, orderOf z = 2 → (h.xi ^ k) z = z := by
  obtain ⟨r, hr⟩ := (IsPGroup.iff_orderOf).mp h.isPGroup x
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | hpos
    · exfalso
      rw [h0, pow_zero] at hr
      exact hx (orderOf_eq_one_iff.mp hr)
    · exact hpos
  set m : ℕ := 2 ^ (r - 1) with hm
  have hpowfix : ∀ n : ℕ, (h.xi ^ k) (x ^ n) = x ^ n := by
    intro n
    have h1 : (h.xi ^ k) (x ^ n) = ((h.xi ^ k) x) ^ n := by
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, map_mul, ih, pow_succ, hfix]
    rw [h1, hfix]
  have hmord : orderOf (x ^ m) = 2 := by
    rw [orderOf_pow, hr, hm, Nat.gcd_eq_right (Nat.pow_dvd_pow 2 (by omega))]
    rw [Nat.pow_div (by omega : r - 1 ≤ r) (by norm_num : 0 < 2)]
    rw [show r - (r - 1) = 1 by omega]
  intro z hz
  obtain ⟨j, hj⟩ := h.trans (x ^ m) z hmord hz
  rw [← hj]
  have hcomm : (h.xi ^ k) ((h.xi ^ j) (x ^ m)) = (h.xi ^ j) ((h.xi ^ k) (x ^ m)) := by
    rw [← MulAut.mul_apply, ← MulAut.mul_apply]
    congr 1
    rw [← pow_add, ← pow_add, Nat.add_comm]
  rw [hcomm, hpowfix m]

/-- **If a power of `ξ` fixes one non-identity element it fixes `Ω₁(P)` pointwise.**  Every
element of `Ω₁(P)` is `1` or an involution, so this is
`xi_pow_fixes_involutions_of_fixes_ne_one`.  (It does *not* force `ξ ^ k = 1`; the kernel of the
action of `⟨ξ⟩` on `P` may be non-trivial.) -/
theorem xi_pow_fixes_omega1_of_fixes_ne_one (h : IsSuzuki2Grp P) {k : ℕ} {x : P}
    (hx : x ≠ 1) (hfix : (h.xi ^ k) x = x) :
    ∀ z ∈ Work.Higman.omega1 P, (h.xi ^ k) z = z := by
  intro z hz
  rcases eq_or_ne z 1 with rfl | hz1
  · simp
  · have hz2 : orderOf z = 2 := by
      have hd : orderOf z ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (h.mem_omega1.mp hz)
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
      · exact absurd (orderOf_eq_one_iff.mp h1) hz1
      · exact h2
    exact xi_pow_fixes_involutions_of_fixes_ne_one h hx hfix z hz2

/-- **The deep configuration of the `C₄` exclusion.**  `A` is a maximal `ξ`-invariant abelian
normal subgroup of the Suzuki 2-group `P` with `[P,P] = A`, `A² = Ω₁(P) = Z(P)`, `A⁴ = 1` and
`|A| = q²`; `D` is a minimal `ξ`-invariant normal subgroup with `A < D ≤ P` and `[D,D] = A²`.

This is the case in which `D/A` is `ξ`-irreducible and `D` is a class-two subgroup of `P` with
`Z(D) = D' = D² = A²`; the sub-case `[A,D] = ⊥` is Gorenstein–Thompson (`H8.alt_pairing_false`)
and the sub-case `[A,D] = A²` is the genuinely hard one.  `H8.c4_sq_a2_card_quot` (axiom-clean)
gives `|D/A| = q`, hence `|D| = q³` and `D < P`, whence orbit counting gives `|P| ≥ q⁴`, so this
configuration *implies* `|P| ≥ q⁴` and is therefore exactly as hard as Higman's Theorem 1. -/
theorem deepSquareCase {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A D : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAmax : ∀ B : Subgroup P, B.Normal → B.map (h.xi : MulAut P).toMonoidHom = B →
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → A ≤ B → B = A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hAn : A.Normal) (hDn : D.Normal)
    (hDinv : D.map (h.xi : MulAut P).toMonoidHom = D)
    (hAD : A ≤ D) (hADne : D ≠ A)
    (hDd : ⁅D, D⁆ = Work.Higman.powSub A 2)
    (hcover : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E ≤ D → E = A ∨ E = D) :
    False := by
  have H : Work.Higman.NSM.C4 h A D :=
    ⟨hAab, hAinv, hAmax, hNA, hGs, hsq, hA4, htop, hcard, hAn, hDn, hDinv, hAD, hADne, hDd,
      hcover⟩
  by_cases hPD : ⁅(⊤ : Subgroup P), D⁆ ≤ Work.Higman.powSub A 2
  · exact Work.Higman.NSM.C4.caseA H hPD
  · exact Work.Higman.NSM.dsq_caseB h H hPD

/-- **The `C₄` exclusion** (Higman 1963, Theorem 1, the hard part): a maximal `ξ`-invariant
abelian normal subgroup `A` with `[P,P] = A` cannot have `A` of exponent four.

* if `P/A` is `ξ`-irreducible then Higman's Lemma 8 (`MSA.lemma8_clean`, axiom-clean) with the
  cover `C = ⊤` gives `exp A ∣ 2`, i.e. `A = A²`, contradicting `|A| = q² > q = |A²|`;
* otherwise a minimal `ξ`-invariant normal `D` with `A < D ≤ P` exists.  `[D,D] ∈ {⊥, A², A}`;
  `⊥` contradicts the maximality of `A` and `[D,D] = A` again gives `exp A ∣ 2` by Higman's
  Lemma 8 with the cover `C = D`; so `[D,D] = A²`, which is `deepSquareCase` above. -/
theorem noSquareMaximal {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAmax : ∀ B : Subgroup P, B.Normal → B.map (h.xi : MulAut P).toMonoidHom = B →
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → A ≤ B → B = A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2) :
    False := by
  have hAn : A.Normal := by
    rw [← hGs]
    exact Subgroup.commutator_normal _ _
  -- the contradiction `A = A²` from `exp A ∣ 2`
  have key : (∀ a ∈ A, a * a = 1) → False := by
    intro hexp
    have hAle : A ≤ Work.Higman.powSub A 2 := by
      intro a ha
      rw [htop, h.mem_omega1, pow_two]
      exact hexp a ha
    have hAeq : A = Work.Higman.powSub A 2 :=
      le_antisymm hAle (Work.Higman.powSub_le (by norm_num))
    have h1 : Nat.card ↥A = Nat.card ↥(Work.Higman.powSub A 2) :=
      congrArg (fun X : Subgroup P => Nat.card ↥X) hAeq
    rw [htop, hcard] at h1
    have h4 := h.omega1_card_ge_four
    nlinarith [h1, h4]
  by_cases hirr : ∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
      A ≤ E → E = A ∨ E = ⊤
  · -- Case 1: `P / A` is `ξ`-irreducible
    have hC2 : Work.Higman.powSub (⊤ : Subgroup P) 2 ≤ A := by
      rw [Work.Higman.powSub, Subgroup.closure_le]
      rintro y ⟨x, -, rfl⟩
      exact hsq x
    have hAne : A ≠ ⊤ := by
      intro htop'
      obtain ⟨x, y, hxy⟩ := h.noncomm
      exact hxy (hAab x (htop' ▸ Subgroup.mem_top x) y (htop' ▸ Subgroup.mem_top y))
    exact key (Work.Higman.MSA.lemma8_clean h ⟨hAn, hAinv, hAab⟩ Subgroup.normal_top
      (Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective) le_top hAne
      (fun E hEn hEinv hAE _ => hirr E hEn hEinv hAE) hC2 hGs)
  · -- Case 2: a proper `ξ`-invariant normal subgroup above `A` exists
    push_neg at hirr
    obtain ⟨D₀, hD₀n, hD₀inv, hAD₀, hD₀A, -⟩ := hirr
    obtain ⟨D, hDn, hDinv, hADlt, hcover⟩ : ∃ D : Subgroup P, D.Normal ∧
        D.map (h.xi : MulAut P).toMonoidHom = D ∧ A < D ∧
        (∀ E : Subgroup P, E.Normal → E.map (h.xi : MulAut P).toMonoidHom = E →
          A ≤ E → E ≤ D → E = A ∨ E = D) := by
      have hfin : ({E : Subgroup P | E.Normal ∧
          E.map (h.xi : MulAut P).toMonoidHom = E ∧ A < E} : Set (Subgroup P)).Finite :=
        Set.finite_univ.subset (fun _ _ => trivial)
      obtain ⟨D, hD⟩ := hfin.exists_minimal
        ⟨D₀, hD₀n, hD₀inv, lt_of_le_of_ne hAD₀ (Ne.symm hD₀A)⟩
      obtain ⟨hD1, hD2, hD3⟩ := hD.1
      refine ⟨D, hD1, hD2, hD3, ?_⟩
      intro E hEn hEinv hAE hED
      rcases eq_or_ne E A with rfl | hEA
      · exact Or.inl rfl
      · exact Or.inr (le_antisymm hED
          (hD.2 ⟨hEn, hEinv, lt_of_le_of_ne hAE (Ne.symm hEA)⟩ hED))
    have hAD : A ≤ D := le_of_lt hADlt
    have hADne : D ≠ A := (ne_of_lt hADlt).symm
    rcases dComm_dichotomy_nsm h hAab hAinv hA4 hGs hDinv with hbot | hDd | hDd
    · -- `[D,D] = ⊥`: `D` is abelian, `ξ`-invariant and normal above `A`
      exact absurd (hAmax D hDn hDinv (fun x hx y hy =>
        commutatorElement_eq_one_iff_mul_comm.mp (by
          have h1 : ⁅x, y⁆ ∈ (⊥ : Subgroup P) := by
            rw [← hbot]
            exact Subgroup.commutator_mem_commutator hx hy
          simpa using h1)) hAD) hADne
    · -- `[D,D] = A²`: the deep configuration
      exact deepSquareCase h hAab hAinv hAmax hNA hGs hsq hA4 htop hcard hAn hDn hDinv hAD hADne
        hDd hcover
    · -- `[D,D] = A`: Higman's Lemma 8 with the cover `D`
      have hC2 : Work.Higman.powSub D 2 ≤ A := by
        rw [Work.Higman.powSub, Subgroup.closure_le]
        rintro y ⟨x, -, rfl⟩
        exact hsq x
      exact key (Work.Higman.MSA.lemma8_clean h ⟨hAn, hAinv, hAab⟩ hDn hDinv hAD (Ne.symm hADne)
        hcover hC2 hDd)

theorem higmanLemma13 {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P) : Nat.card P ≤ Nat.card ↥(Subgroup.center P) ^ 3 := by
  classical
  have hZ : Subgroup.center P = Work.Higman.omega1 P := Work.Higman.center_eq_omega1_new h
  obtain ⟨A, hAn, hAinv, hAab, hAmax, hNA, hDA, hsq, hA4⟩ := Work.Higman.lemma9_maximal_abelian h
  obtain ⟨e, hexp, hcardlayer, htoplayer, hsub⟩ := Work.Higman.homogeneous_structure h hAab hAinv
  have hAinf : A ⊓ Work.Higman.omega1 P = Work.Higman.omega1 P := inf_eq_right.mpr hNA
  have hAcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ e := by
    have hh := hcardlayer 0 (Nat.zero_le e)
    rw [pow_zero, Work.Higman.powSub_one_eq, hAinf, Nat.sub_zero] at hh
    exact hh
  -- `e ≤ 2`
  have he2 : e ≤ 2 := by
    rcases Nat.lt_or_ge e 2 with hlt | hge
    · omega
    · have hc := hcardlayer 2 hge
      rw [show (2 : ℕ) ^ 2 = 4 by norm_num, hAinf, hA4, Subgroup.card_bot] at hc
      have hq : Nat.card ↥(Work.Higman.omega1 P) ≠ 1 := by
        have := h.omega1_card_ge_four
        omega
      have hz : e - 2 = 0 := (Nat.pow_eq_one.mp hc.symm).resolve_left hq
      omega
  -- `q ≥ 4` so `e ≠ 0`
  have hepos : 1 ≤ e := by
    by_contra hcon
    have h0 : e = 0 := by omega
    have h1 : A = ⊥ := by
      have hc : Nat.card ↥A = 1 := by rw [hAcard, h0, pow_zero]
      haveI : Subsingleton ↥A := (Nat.card_eq_one_iff_unique.mp hc).1
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have h2 : (⟨x, hx⟩ : ↥A) = 1 := Subsingleton.elim _ _
      simpa using congrArg Subtype.val h2
    have h3 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by
      have hb : Work.Higman.omega1 P = ⊥ := le_bot_iff.mp (h1 ▸ hNA)
      rw [hb, Subgroup.card_bot]
    have h4 := h.omega1_card_ge_four
    omega
  rcases (show e = 1 ∨ e = 2 by omega) with he | he
  · -- `e = 1`: `A = Ω₁(P) = Z(P)`
    have hAeq : A = Work.Higman.omega1 P := by
      have h1 : Nat.card ↥A = Nat.card ↥(Work.Higman.omega1 P) := by rw [hAcard, he, pow_one]
      exact (Subgroup.eq_of_le_of_card_ge hNA (le_of_eq h1)).symm
    refine card_le_cube_of_class_two h hZ ?_ ?_
    · intro x
      rw [hZ, ← hAeq]
      exact hsq x
    · rw [hZ, ← hAeq]
      exact hDA
  · -- `e = 2`
    have hA2 : Work.Higman.powSub A 2 = Work.Higman.omega1 P := by
      have hh := htoplayer
      rw [he, show (2 : ℕ) ^ (2 - 1) = 2 by norm_num] at hh
      rwa [hAinf] at hh
    have hA2card : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 := by
      rw [hAcard, he]
    have hDd_inv : Subgroup.map (h.xi : MulAut P).toMonoidHom ⁅(⊤ : Subgroup P), ⊤⁆
        = ⁅(⊤ : Subgroup P), ⊤⁆ := by
      rw [Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective]
    rcases xi_inv_sub_dichotomy_nsm h hAab hAinv hA4 hDA hDd_inv with hbot | hA' | hA'
    · -- `[P,P] = ⊥`: `P` is abelian, contradiction
      exfalso
      obtain ⟨x, y, hxy⟩ := h.noncomm
      exact hxy (commutatorElement_eq_one_iff_mul_comm.mp (by
        have h1 : ⁅x, y⁆ ∈ (⊥ : Subgroup P) := by
          rw [← hbot]
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
        simpa using h1))
    · -- `[P,P] = A² = Ω₁(P) = Z(P)`: class two
      have hcl : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P := by rw [hA', hA2, hZ]
      refine card_le_cube_of_class_two h hZ ?_ hcl
      · intro x
        rw [Subgroup.mem_center_iff]
        intro y
        have h2 : ⁅x, y⁆ ∈ Work.Higman.omega1 P := by
          rw [← hA2, ← hA']
          exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
        have h1 : ⁅x ^ 2, y⁆ = 1 := by
          rw [pow_two, czh_commutator_mul_left hcl x x y, ← pow_two, h.mem_omega1.mp h2]
        exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
    · -- `[P,P] = A`: the `C₄` configuration, excluded by `noSquareMaximal`
      exact (noSquareMaximal h hAab hAinv hAmax hNA hA' hsq hA4 hA2 hA2card).elim

end Work.Higman.NSM
