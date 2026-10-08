/-
Copyright (c) 2024. All rights reserved.

# The `C₄`-cardinality bound `|P| ≤ |Ω₁(P)|³` for a Suzuki 2-group

Higman, *Suzuki 2-groups*, Illinois J. Math. **7** (1963), 79--96, Theorem 1 / Lemma 13.

The proof splits according to whether `[P,P] ≤ Ω₁(P)`.

* **Class-two case** (`c4_card_le_of_comm_le_omega1`).  If `[P,P] ≤ Ω₁(P)` then `Z(P) = Ω₁(P)`
  (Higman's Theorem 1, proved unconditionally as `Work.Higman.center_eq_omega1_new`), every square
  is central, and the squaring map `P ⧸ Z(P) → Z(P)`, `xZ ↦ x²` is an anisotropic quadratic map
  over `𝔽₂` with polar form the commutator pairing.  Chevalley–Warning
  (`Work.Higman.card_le_sq_of_quadratic_anisotropic`, `chevalley_warning.lean`) gives
  `|P ⧸ Z(P)| ≤ |Z(P)|²`, hence `|P| ≤ |Ω₁(P)|³`.

* **`C₄`-case** (`c4_exclusion_alt`).  If `[P,P] ≰ Ω₁(P)` then the maximal `ξ`-invariant abelian
  normal subgroup `A` (Higman's Lemma 9, `Work.Higman.lemma9_maximal_abelian`) satisfies
  `|A| = |Ω₁(P)|²`, `A² = Ω₁(P)`, `[P,P] = A`, `A⁴ = ⊥`: the `C₄` shape of Higman's Lemma 8,
  which is impossible.  The case analysis on a minimal `ξ`-invariant normal cover `C > A` is:

  * `C' = ⊥`: then `C` is abelian, contradicting maximality of `A`;
  * `C' = A`: Higman's Lemma 8 (`Work.Higman.higman_lemma8`, clean) gives `exp A ≤ 2`, i.e.
    `A ≤ Ω₁(P) = A²`, contradiction;
  * `C' = A²`: if `C² = A` then Higman's Lemma 7 (`Work.Higman.higman9_case_deriv_le_sq`) makes
    `C` abelian, contradiction; if `C² = ⊥` then `C ≤ Ω₁(P)`; the remaining case `C' = C² = Ω₁(P)`
    is isolated as `c4_cover_deriv_sq_false`.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.chevalley_warning
import Submission.Work.Higman.center_sq_eq_one
import Submission.Work.Higman.center_eq_omega1_new
import Submission.Work.Higman.lemma9_maximal_abelian
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.higman_lemma8
import Submission.Work.Higman.higman9_case_deriv_le_sq
import Submission.Work.Higman.xi_pow_triv_omega1_iff
import Submission.Work.Higman.H8.fixed_coset_imp_fix_all
import Submission.Work.Higman.Fq_structure
import Submission.Work.Higman.Q3.ex_subgroup_c4
import Submission.Work.Higman.Q3.Dsq_sq_mem_powSub_two
import Submission.Work.Higman.HS.centralizer_eq_A_of_comm_C_A
import Submission.Work.Higman.C4Cover.c4_branch_CP_A2
import Submission.Work.Higman.C4Cover.c4_cover_card_eq_cube
import Submission.Work.Higman.H8.c4_gap_central
import Submission.Work.Higman.H8.c4_comm_A_top
import Submission.Work.Higman.Q3.crux_class_three_jacobi
import Submission.Work.NSDEEP.All

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.Higman.H8

open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

/-! ## Class-two commutator algebra

Self-contained copies of the standard class-two identities, so that this file does not need any
module whose proofs are incomplete. -/

/-- `x * y * x⁻¹ = ⁅x, y⁆ * y`. -/
theorem c4_mul_mul_inv_eq_commutator_mul {G : Type*} [Group G] (x y : G) :
    x * y * x⁻¹ = ⁅x, y⁆ * y := by
  rw [commutatorElement_def]; group

/-- In a group of class two every commutator is central, and every element commutes with it. -/
theorem c4_commutator_central_comm {G : Type*} [Group G]
    (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y z : G) :
    z * ⁅x, y⁆ = ⁅x, y⁆ * z :=
  Subgroup.mem_center_iff.mp
    (hZ (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))) z

/-- Class two: `[x * y, z] = [x, z] * [y, z]`. -/
theorem c4_commutator_mul_left {G : Type*} [Group G]
    (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y z : G) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have hcy : ∀ w : G, w * ⁅y, z⁆ = ⁅y, z⁆ * w := c4_commutator_central_comm hZ y z
  have hcx : ∀ w : G, w * ⁅x, z⁆ = ⁅x, z⁆ * w := c4_commutator_central_comm hZ x z
  have h1 : x * z * x⁻¹ = ⁅x, z⁆ * z := c4_mul_mul_inv_eq_commutator_mul x z
  have h2 : y * z * y⁻¹ = ⁅y, z⁆ * z := c4_mul_mul_inv_eq_commutator_mul y z
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
theorem c4_commutator_mul_right {G : Type*} [Group G]
    (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y z : G) :
    ⁅z, x * y⁆ = ⁅z, x⁆ * ⁅z, y⁆ := by
  have h1 : ⁅z, x * y⁆ = ⁅x * y, z⁆⁻¹ := by rw [← commutatorElement_inv]
  rw [h1, c4_commutator_mul_left hZ x y z, mul_inv_rev, commutatorElement_inv,
    commutatorElement_inv]
  exact (c4_commutator_central_comm hZ z y ⁅z, x⁆).symm

/-- A central element commutes out of a commutator on the left. -/
theorem c4_commutator_eq_one_of_mem_center_left {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (x : G) : ⁅z, x⁆ = 1 := by
  rw [commutatorElement_def, ← Subgroup.mem_center_iff.mp hz x]
  group

/-- A central element commutes out of a commutator on the right. -/
theorem c4_commutator_eq_one_of_mem_center_right {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (x : G) : ⁅x, z⁆ = 1 := by
  rw [commutatorElement_def, Subgroup.mem_center_iff.mp hz x]
  group

/-- In a Suzuki 2-group with `[P,P] ≤ Ω₁(P)` every square is central (the class-two computation
`x ^ 2 * y = ⁅x, y⁆ ^ 2 * y * x ^ 2 = y * x ^ 2`). -/
theorem c4_sq_mem_center_of_comm_le_omega1 (h : Work.Higman.IsSuzuki2Grp P)
    (hcomm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Work.Higman.omega1 P) (x : P) :
    x ^ 2 ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff]
  intro y
  have hxy : ⁅x, y⁆ ∈ Work.Higman.omega1 P :=
    hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
  have hc : ⁅x, y⁆ ∈ Subgroup.center P := h.omega1_le_center hxy
  have hcc : ⁅x, y⁆ * ⁅x, y⁆ = 1 := by
    have h1 := h.mem_omega1.mp hxy
    rwa [pow_two] at h1
  have hcx : x * ⁅x, y⁆ = ⁅x, y⁆ * x := (Subgroup.mem_center_iff.mp hc) x
  have h1 : x * y = ⁅x, y⁆ * y * x := by
    have h2 := c4_mul_mul_inv_eq_commutator_mul x y
    rw [← h2]; group
  have hmain : x ^ 2 * y = y * x ^ 2 := by
    calc x ^ 2 * y = x * (x * y) := by rw [pow_two]; group
      _ = x * (⁅x, y⁆ * y * x) := by rw [h1]
      _ = (x * ⁅x, y⁆) * y * x := by group
      _ = (⁅x, y⁆ * x) * y * x := by rw [hcx]
      _ = ⁅x, y⁆ * (x * y) * x := by group
      _ = ⁅x, y⁆ * (⁅x, y⁆ * y * x) * x := by rw [h1]
      _ = (⁅x, y⁆ * ⁅x, y⁆) * y * (x * x) := by group
      _ = y * (x * x) := by rw [hcc]; group
      _ = y * x ^ 2 := by rw [pow_two]
  exact hmain.symm

/-! ## The Chevalley–Warning bound in the class-two case -/

/-- **Chevalley–Warning for the squaring map of a class-two Suzuki 2-group.**
If `Z(P) = Ω₁(P)`, `[P,P] ≤ Z(P)` and every square is central, then
`|P ⧸ Z(P)| ≤ |Z(P)|²`.  Indeed the squaring map `xZ ↦ x²` is an anisotropic quadratic map over
`𝔽₂` (anisotropic because `x² = 1` means `x ∈ Ω₁(P) = Z(P)`), with polar form the commutator
pairing, so Chevalley–Warning (`Work.Higman.card_le_sq_of_quadratic_anisotropic`) applies. -/
theorem c4_card_quotient_le_sq (h : Work.Higman.IsSuzuki2Grp P)
    (hZ : Subgroup.center P = Work.Higman.omega1 P)
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
    have h1 : ((v.toMul : ↥(Subgroup.center P)) : P) ∈ Work.Higman.omega1 P := by
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
      have h1 : z ∈ Work.Higman.omega1 P := by rw [← hZ]; exact hz
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
    exact c4_commutator_mul_right hZ2 a b y
  have bZ_mul₂ : ∀ y a b : P, bZ y (a * b) = bZ y a * bZ y b := by
    intro y a b
    apply Subtype.ext
    show ⁅a * b, y⁆ = ⁅a, y⁆ * ⁅b, y⁆
    exact c4_commutator_mul_left hZ2 a b y
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
    rw [c4_commutator_mul_left hZ2 b₁ w (a₁ * z),
        c4_commutator_eq_one_of_mem_center_left hw (a₁ * z), mul_one,
        c4_commutator_mul_right hZ2 a₁ z b₁,
        c4_commutator_eq_one_of_mem_center_right hz b₁, mul_one]
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

/-- **The class-two case of Higman's Theorem 1.**  If `[P,P] ≤ Ω₁(P)` then
`|P| ≤ |Ω₁(P)|³`. -/
theorem c4_card_le_of_comm_le_omega1 (h : Work.Higman.IsSuzuki2Grp P)
    (hcomm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Work.Higman.omega1 P) :
    Nat.card P ≤ (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 := by
  have hZ : Subgroup.center P = Work.Higman.omega1 P := Work.Higman.center_eq_omega1_new h
  have hcommZ : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P := hZ ▸ hcomm
  have hsq : ∀ x : P, x ^ 2 ∈ Subgroup.center P :=
    c4_sq_mem_center_of_comm_le_omega1 h hcomm
  have hb := c4_card_quotient_le_sq h hZ hsq hcommZ
  have hcard : Nat.card P =
      Nat.card (P ⧸ Subgroup.center P) * Nat.card ↥(Subgroup.center P) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have hZcard : Nat.card ↥(Subgroup.center P) = Nat.card ↥(Work.Higman.omega1 P) := by rw [hZ]
  have hb' : Nat.card (P ⧸ Subgroup.center P) ≤ Nat.card ↥(Work.Higman.omega1 P) ^ 2 := by
    rw [← hZcard]; exact hb
  calc Nat.card P = Nat.card (P ⧸ Subgroup.center P) * Nat.card ↥(Work.Higman.omega1 P) := by
        rw [hcard, hZcard]
    _ ≤ (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 * Nat.card ↥(Work.Higman.omega1 P) :=
        Nat.mul_le_mul_right _ hb'
    _ = (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 := by ring

/-! ## The `C₄` case -/

/-- The `ξ`-invariant subgroups of the maximal `ξ`-invariant abelian normal subgroup `A` in the
`C₄` setting (`A² = Ω₁(P)`, `A⁴ = ⊥`) are `⊥`, `A²` and `A` (Higman's Lemma 1 dichotomy). -/
theorem c4_xi_inv_sub_trichotomy (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    {B : Subgroup P} (hBA : B ≤ A) (hBin : B.map (h.xi : MulAut P).toMonoidHom = B) :
    B = ⊥ ∨ B = Work.Higman.powSub A 2 ∨ B = A := by
  obtain ⟨e, -, -, -, hsub⟩ := Work.Higman.homogeneous_structure h hA.abelian hA.map_eq
  obtain ⟨i, hi⟩ := hsub B hBA hBin
  rcases Nat.eq_zero_or_pos i with h0 | hpos
  · exact Or.inr (Or.inr (by rw [hi, h0, pow_zero, Work.Higman.powSub_one_eq]))
  · rcases Nat.lt_or_ge i 2 with hlt | hge
    · have hi1 : i = 1 := by omega
      exact Or.inr (Or.inl (by rw [hi, hi1]; norm_num))
    · refine Or.inl ?_
      have hdvd : 4 ∣ 2 ^ i := ⟨2 ^ (i - 2), by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
        congr 1
        omega⟩
      have hle : Work.Higman.powSub A (2 ^ i) ≤ Work.Higman.powSub A 4 :=
        Work.Higman.powSub_le_of_dvd hA.abelian hdvd
      rw [hi]
      exact le_bot_iff.mp (hA4 ▸ hle)

/-- **The `C₄` data.**  If `[P,P] ≰ Ω₁(P)` then the maximal `ξ`-invariant abelian normal subgroup
`A` of Higman's Lemma 9 satisfies all the hypotheses of the `C₄` exclusion: it is maximal
`ξ`-invariant abelian normal, `Ω₁(P) ≤ A`, `[P,P] = A`, every square lies in `A`, `A⁴ = ⊥`,
`A² = Ω₁(P)` and `|A| = |Ω₁(P)|²`. -/
theorem c4_data (h : Work.Higman.IsSuzuki2Grp P)
    (hcomm : ¬(⁅(⊤ : Subgroup P), ⊤⁆ ≤ Work.Higman.omega1 P)) :
    ∃ A : Subgroup P, Work.Higman.IsXiAbelNormal h A ∧
      (∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A) ∧
      Work.Higman.omega1 P ≤ A ∧ ⁅(⊤ : Subgroup P), ⊤⁆ = A ∧
      (∀ x : P, x ^ 2 ∈ A) ∧ Work.Higman.powSub A 4 = ⊥ ∧
      Work.Higman.powSub A 2 = Work.Higman.omega1 P ∧
      Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 := by
  classical
  obtain ⟨A, hAn, hAxi, hAab, hAmax, hNA, hDA, hsq, hA4⟩ := Work.Higman.lemma9_maximal_abelian h
  have hA : Work.Higman.IsXiAbelNormal h A := ⟨hAn, hAxi, hAab⟩
  have hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A :=
    fun B hB hAB => hAmax B hB.1 hB.2.1 hB.2.2 hAB
  obtain ⟨e, hexp, hcard, htop, hsub⟩ := Work.Higman.homogeneous_structure h hAab hAxi
  have hAinf : A ⊓ Work.Higman.omega1 P = Work.Higman.omega1 P := inf_eq_right.mpr hNA
  have hq4 : 4 ≤ Nat.card ↥(Work.Higman.omega1 P) := h.omega1_card_ge_four
  have hq1 : 1 < Nat.card ↥(Work.Higman.omega1 P) := by omega
  have hpow : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ e := by
    have h0 := hcard 0 (Nat.zero_le e)
    rw [pow_zero, Work.Higman.powSub_one_eq, hAinf] at h0
    exact h0
  have hexp4 : ∀ a ∈ A, a ^ 4 = 1 := by
    intro a ha
    have hmem : a ^ 4 ∈ Work.Higman.powSub A 4 := Work.Higman.pow_mem_powSub (n := 4) ha
    rw [hA4] at hmem
    simpa using hmem
  have hAle : Nat.card ↥A ≤ (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 :=
    Work.Higman.card_le_card_omega1_sq_of_exp h hA hNA hexp4
  have he2 : e = 2 := by
    have hepos : e ≠ 0 := by
      intro h0
      rw [hpow, h0, pow_zero] at hAle
      have : Nat.card ↥A = 1 := by rw [hpow, h0, pow_zero]
      have h1 : Nat.card ↥(Work.Higman.omega1 P) ≤ Nat.card ↥A := Subgroup.card_le_of_le hNA
      omega
    have he_le : e ≤ 2 := by
      rw [hpow] at hAle
      exact (Nat.pow_le_pow_iff_right hq1).mp hAle
    have he_ne_one : e ≠ 1 := by
      intro h1
      have hAcard : Nat.card ↥A = Nat.card ↥(Work.Higman.omega1 P) := by
        rw [hpow, h1, pow_one]
      have hAeq : A = Work.Higman.omega1 P :=
        (Subgroup.eq_of_le_of_card_ge hNA hAcard.le).symm
      exact hcomm (hAeq ▸ hDA)
    omega
  have htop2 : Work.Higman.powSub A 2 = Work.Higman.omega1 P := by
    have h := htop
    rw [he2, show (2 : ℕ) ^ (2 - 1) = 2 by norm_num, hAinf] at h
    exact h
  have hAcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 := by
    rw [hpow, he2]
  -- `[P,P]` is `ξ`-invariant and normal, hence a power subgroup of `A`
  have hDAxi : ((⁅(⊤ : Subgroup P), ⊤⁆ : Subgroup P)).map (h.xi : MulAut P).toMonoidHom
      = (⁅(⊤ : Subgroup P), ⊤⁆ : Subgroup P) := by
    have h1 : (⊤ : Subgroup P).map (h.xi : MulAut P).toMonoidHom = ⊤ :=
      Subgroup.map_top_of_surjective (h.xi : MulAut P).toMonoidHom
        (MulEquiv.surjective h.xi)
    rw [Subgroup.map_commutator, h1]
  obtain ⟨i, hi⟩ := hsub (⁅(⊤ : Subgroup P), ⊤⁆ : Subgroup P) hDA hDAxi
  have hDAeq : ⁅(⊤ : Subgroup P), ⊤⁆ = A := by
    have hbot : (⁅(⊤ : Subgroup P), ⊤⁆ : Subgroup P) ≠ ⊥ := by
      intro hb
      obtain ⟨x, y, hxy⟩ := h.noncomm
      have h1 : ⁅x, y⁆ ∈ ⁅(⊤ : Subgroup P), ⊤⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
      rw [hb] at h1
      exact hxy (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1))
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · rw [hi, h0, pow_zero, Work.Higman.powSub_one_eq]
    · rcases Nat.lt_or_ge i 2 with hlt | hge
      · have hi1 : i = 1 := by omega
        exfalso
        refine hcomm ?_
        rw [hi, hi1, show (2 : ℕ) ^ 1 = 2 by norm_num]
        exact le_of_eq htop2
      · have hdvd : 4 ∣ 2 ^ i := ⟨2 ^ (i - 2), by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]
          congr 1
          omega⟩
        have hle : Work.Higman.powSub A (2 ^ i) ≤ Work.Higman.powSub A 4 :=
          Work.Higman.powSub_le_of_dvd hAab hdvd
        have hbot_le : Work.Higman.powSub A (2 ^ i) ≤ ⊥ := hA4 ▸ hle
        exfalso
        rw [← hi] at hbot_le
        exact hbot (le_bot_iff.mp hbot_le)
  exact ⟨A, hA, hmax, hNA, hDAeq, hsq, hA4, htop2, hAcard⟩

/-! ## The residual case `C' = C² = A²` of the `C₄` exclusion

Let `A ≤ C ≤ P` be as in `c4_exclusion_alt`, with `C` a minimal `ξ`-invariant normal cover of `A`
and `⁅C,C⁆ = C² = A²`.  The two dichotomies below cut this configuration down to two cases:

* `⁅C,A⁆ = ⊥`: `A` centralises `C` (the Gorenstein–Thompson case, `c4_gap_central_false`);
* `⁅C,A⁆ = A²`: then `C_P(A) = A`, and `⁅C,⊤⁆ ∈ {A², A}`; the case `⁅C,⊤⁆ = A²` is settled
  (clean, importable: `C4Cover.c4_branch_CP_A2`), so only

  `⁅C,A⁆ = A²` and `⁅C,⊤⁆ = A`

  remains (Higman's `ξ`-length-3 subgroup `C` of a `ξ`-length-4 group; `c4_gap_hard_false`).
-/

/-- `A ≠ A ^ (2)` in the `C₄` setting (from `|A| = |Ω₁(P)|²`, `A² = Ω₁(P)`, `|Ω₁(P)| ≥ 4`). -/
theorem c4_A_ne_powSub_two (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2) :
    A ≠ Work.Higman.powSub A 2 := by
  intro heq
  have h1 : Nat.card ↥A = Nat.card ↥(Work.Higman.powSub A 2) :=
    congrArg (fun X : Subgroup P => Nat.card ↥X) heq
  rw [htop] at h1
  have h2 : Nat.card ↥(Work.Higman.omega1 P) = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 := by
    rw [← hcard, h1]
  have hpos : 0 < Nat.card ↥(Work.Higman.omega1 P) := Nat.card_pos
  have h4 := h.omega1_card_ge_four
  nlinarith [h2, h4]

/-- `A ^ (2) ≠ ⊥` in the `C₄` setting. -/
theorem c4_powSub_two_ne_bot (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P) :
    Work.Higman.powSub A 2 ≠ ⊥ := by
  intro hb
  have hc : Nat.card ↥(Work.Higman.omega1 P) = 1 := by rw [← htop, hb]; simp
  have h4 := h.omega1_card_ge_four
  omega

/-- **First dichotomy of the gap case.**  If `C` is a minimal `ξ`-invariant normal cover of `A`
with `⁅C,C⁆ = A²`, then `⁅C,A⁆ ≤ ⁅C,C⁆ = A²` is `ξ`-invariant and normal, so `⁅C,A⁆` is `⊥` or
`A²`. -/
theorem c4_gap_comm_C_A_dichotomy (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hAC : A ≤ C)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2) :
    ⁅C, A⁆ = ⊥ ∨ ⁅C, A⁆ = Work.Higman.powSub A 2 := by
  have hCA_le : (⁅C, A⁆ : Subgroup P) ≤ Work.Higman.powSub A 2 := by
    calc ⁅C, A⁆ ≤ ⁅C, C⁆ := Subgroup.commutator_mono le_rfl hAC
      _ = Work.Higman.powSub A 2 := hCd
  have hCA_inv : (⁅C, A⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom = ⁅C, A⁆ := by
    rw [Subgroup.map_commutator, hCinv, hA.map_eq]
  have hBA : (⁅C, A⁆ : Subgroup P) ≤ A := hCA_le.trans (Work.Higman.powSub_le (by norm_num))
  rcases c4_xi_inv_sub_trichotomy h hA htop hA4 hBA hCA_inv with hb | h2 | h3
  · exact Or.inl hb
  · exact Or.inr h2
  · exfalso
    have hAle : A ≤ Work.Higman.powSub A 2 := by
      have hh := hCA_le
      rwa [h3] at hh
    exact c4_A_ne_powSub_two (A := A) h htop hcard
      (le_antisymm hAle (Work.Higman.powSub_le (A := A) (n := 2) (by norm_num)))

/-- **Second dichotomy of the gap case.**  `⁅C,⊤⁆ ≤ ⁅⊤,⊤⁆ = A` is `ξ`-invariant and normal and
contains `⁅C,C⁆ = A²`, so it is `A²` or `A`. -/
theorem c4_gap_comm_C_top_dichotomy (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2) :
    ⁅C, (⊤ : Subgroup P)⁆ = Work.Higman.powSub A 2 ∨
      ⁅C, (⊤ : Subgroup P)⁆ = A := by
  have hle : (⁅C, (⊤ : Subgroup P)⁆ : Subgroup P) ≤ A := by
    calc ⁅C, (⊤ : Subgroup P)⁆ ≤ ⁅(⊤ : Subgroup P), ⊤⁆ :=
          Subgroup.commutator_mono le_top le_rfl
      _ = A := hGs
  have hinv : (⁅C, (⊤ : Subgroup P)⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom
      = ⁅C, (⊤ : Subgroup P)⁆ := by
    rw [Subgroup.map_commutator, hCinv,
      Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective]
  rcases c4_xi_inv_sub_trichotomy h hA htop hA4 hle hinv with hb | h2 | h3
  · exfalso
    have hb2 : (⁅C, C⁆ : Subgroup P) ≤ (⊥ : Subgroup P) :=
      (Subgroup.commutator_mono le_rfl le_top).trans (le_of_eq hb)
    rw [hCd] at hb2
    exact c4_powSub_two_ne_bot h htop (le_bot_iff.mp hb2)
  · exact Or.inl h2
  · exact Or.inr h3

/-- **The Gorenstein–Thompson case of the gap.**  If `A` centralises the minimal cover `C`
(`⁅C,A⁆ = ⊥`), `C² ≤ A` and `⁅C,C⁆ = A²`, then we have a contradiction: the fourth-power map
`C/A → A²` is a homomorphism onto a `ξ`-irreducible module, and the `ξ`-equivariant alternating
commutator pairing `C/A × C/A → A²` has to be trivial (Gorenstein–Thompson), against
`⁅C,C⁆ = A² ≠ ⊥`.

(This is the content of `Work.Higman.H8.alt_pairing_false`, re-derived here so that the
dependency chain avoids the currently unbuildable module `Work.Higman.no_square_maximal`.) -/
theorem c4_gap_central_false (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hZ : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c) : False :=
  Work.Higman.H8.c4_gap_central h hA hNA hGs hsq hA4 htop hCn hCinv hAC hCA hcover hC2 hCd hZ

/-! ### The first branch of the gap: the shift identity `(a·y)² = y²` cannot hold everywhere

In the gap `⁅C,C⁆ = C² = A²` the subgroup `C` has class two (`⁅C,C⁆ = A² ⊆ Z(P)`), so for
`a ∈ A` and `y ∈ C` the squaring map satisfies the exact identity
`(a·y)² = a²·⁅y,a⁆·y²`.  The lemma below shows that the "shift trivial" alternative
`(a·y)² = y²` for **all** `y ∈ C∖A`, `a ∈ A` is contradictory.  Hence in the residual one may
assume that for some `y ∈ C∖A` and `a ∈ A` the *deviation* `a²·⁅y,a⁆` is non-trivial — the precise
residual recorded in `H8/NOTES_c4_gap_session10.md`. -/

/-- **The shift identity cannot hold everywhere in the gap.**
`A` as in `c4_data`, `C` a minimal `ξ`-invariant normal cover with `⁅C,C⁆ = C² = A²` and
`|C| = q³`; then it is impossible that `(a·y)² = y²` for all `y ∈ C∖A` and all `a ∈ A`. -/
theorem c4_gap_shift_false (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : Work.Higman.powSub C 2 = Work.Higman.powSub A 2)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2)
    (hb : ∀ y ∈ C, y ∉ A → ∀ a ∈ A, (a * y) ^ 2 = y ^ 2) : False := by
  classical
  have hq4 : 4 ≤ Nat.card ↥(Work.Higman.omega1 P) := h.omega1_card_ge_four
  have hCcard : Nat.card ↥C = (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 :=
    Work.Higman.C4Cover.c4_cover_card_eq_cube h hA.abelian hNA hGs hsq htop hcard hCn hCinv hAC
      hCA hcover hCd
  -- `A ≠ A²` because `|A| = q²`, `|A²| = q` and `q ≥ 4`.
  have hA_ne_A2 : A ≠ Work.Higman.powSub A 2 := by
    intro heq
    have h1 : Nat.card ↥A = Nat.card ↥(Work.Higman.powSub A 2) :=
      congrArg (fun S : Subgroup P => Nat.card ↥S) heq
    rw [hcard, htop] at h1
    nlinarith [h1, hq4]
  -- the exact class-two identity `(a*y)^2 = a^2 * [y,a] * y^2`
  have hident : ∀ a ∈ A, ∀ y ∈ C, (a * y) ^ 2 = a ^ 2 * ⁅y, a⁆ * y ^ 2 := by
    intro a ha y hy
    have hcomm : ⁅y, a⁆ ∈ Subgroup.center P := by
      have hmem : ⁅y, a⁆ ∈ Work.Higman.powSub A 2 := by
        rw [← hCAd]
        exact Subgroup.commutator_mem_commutator hy ha
      exact h.omega1_le_center (by rw [← htop]; exact hmem)
    have hca : ⁅y, a⁆ * a = a * ⁅y, a⁆ := ((Subgroup.mem_center_iff.mp hcomm) a).symm
    have h1 : y * a = ⁅y, a⁆ * (a * y) := by
      rw [commutatorElement_def]; group
    have key : a * ⁅y, a⁆ * a = a * a * ⁅y, a⁆ := by
      rw [mul_assoc, hca, ← mul_assoc]
    calc (a * y) ^ 2 = a * (y * a) * y := by rw [pow_two]; group
      _ = a * (⁅y, a⁆ * (a * y)) * y := by rw [h1]
      _ = (a * ⁅y, a⁆ * a) * y * y := by group
      _ = (a * a * ⁅y, a⁆) * y * y := by rw [key]
      _ = a ^ 2 * ⁅y, a⁆ * y ^ 2 := by rw [pow_two, pow_two]; group
  -- consequence of the shift identity: `[y,a] = a²`
  have hkey : ∀ y ∈ C, y ∉ A → ∀ a ∈ A, ⁅y, a⁆ = a ^ 2 := by
    intro y hy hyA a ha
    have h1 : (a * y) ^ 2 = y ^ 2 := hb y hy hyA a ha
    rw [hident a ha y hy] at h1
    have h2 : a ^ 2 * ⁅y, a⁆ = 1 := by
      have := congrArg (fun z : P => z * (y ^ 2)⁻¹) h1
      simpa [mul_assoc] using this
    have h3 : (a ^ 2)⁻¹ = a ^ 2 := by
      refine inv_eq_of_mul_eq_one_right ?_
      have ha2 : a ^ 2 ∈ Work.Higman.omega1 P := by
        rw [← htop]; exact Work.Higman.pow_mem_powSub ha
      have h5 := h.mem_omega1.mp ha2
      rwa [pow_two] at h5
    calc ⁅y, a⁆ = 1 * ⁅y, a⁆ := (one_mul _).symm
      _ = (a ^ 2)⁻¹ * a ^ 2 * ⁅y, a⁆ := by rw [inv_mul_cancel, one_mul]
      _ = (a ^ 2)⁻¹ * (a ^ 2 * ⁅y, a⁆) := by group
      _ = (a ^ 2)⁻¹ * 1 := by rw [h2]
      _ = a ^ 2 := by rw [mul_one, h3]
  -- `C ∖ A` is non-empty
  obtain ⟨y, hyC, hyA⟩ : ∃ y ∈ C, y ∉ A := by
    by_contra hcon
    push_neg at hcon
    exact hCA (le_antisymm (fun x hx => hcon x hx) hAC).symm
  -- there are `y₁, y₂ ∈ C∖A` with `y₁*y₂ ∉ A`: otherwise `z ↦ y*z` injects `C∖A` into `A`,
  -- so `|C| - |A| ≤ |A|`, i.e. `q³ - q² ≤ q²`, contradicting `q ≥ 4`.
  have hex : ∃ y₁ ∈ C, y₁ ∉ A ∧ ∃ y₂ ∈ C, y₂ ∉ A ∧ y₁ * y₂ ∉ A := by
    by_contra hcon
    push_neg at hcon
    have hinj : Set.InjOn (fun z : P => y * z) {z : P | z ∈ C ∧ z ∉ A} := by
      intro z₁ _ z₂ _ hz
      exact mul_left_cancel hz
    have hle : Set.ncard {z : P | z ∈ C ∧ z ∉ A} ≤ Nat.card ↥A := by
      have h1 : Set.ncard {z : P | z ∈ C ∧ z ∉ A} ≤ Set.ncard (A : Set P) :=
        Set.ncard_le_ncard_of_injOn (fun z : P => y * z)
          (fun z hz => hcon y hyC hyA z hz.1 hz.2) hinj
      have h2 : Nat.card ↥A = Set.ncard (A : Set P) := Nat.card_coe_set_eq (A : Set P)
      omega
    have hdisj : Disjoint (A : Set P) {z : P | z ∈ C ∧ z ∉ A} := by
      rw [Set.disjoint_left]
      rintro z hz ⟨-, hzA⟩
      exact hzA hz
    have hunion : (A : Set P) ∪ {z : P | z ∈ C ∧ z ∉ A} = (C : Set P) := by
      ext z
      constructor
      · rintro (hz | ⟨hz, -⟩)
        · exact hAC hz
        · exact hz
      · intro hz
        by_cases hzA : z ∈ A
        · exact Or.inl hzA
        · exact Or.inr ⟨hz, hzA⟩
    have hsum : Nat.card ↥A + Set.ncard {z : P | z ∈ C ∧ z ∉ A} = Nat.card ↥C := by
      have h1 : Set.ncard (A : Set P) + Set.ncard {z : P | z ∈ C ∧ z ∉ A}
          = Set.ncard (C : Set P) := by
        rw [← hunion]
        exact (Set.ncard_union_eq hdisj).symm
      have h2 : Nat.card ↥A = Set.ncard (A : Set P) := Nat.card_coe_set_eq (A : Set P)
      have h3 : Nat.card ↥C = Set.ncard (C : Set P) := Nat.card_coe_set_eq (C : Set P)
      omega
    rw [hCcard, hcard] at hsum
    nlinarith [hsum, hle, hq4]
  obtain ⟨y₁, hy₁C, hy₁A, y₂, hy₂C, hy₂A, hy₁y₂A⟩ := hex
  -- final contradiction: `a² = [y₁y₂,a] = [y₁,a][y₂,a] = a²·a² = 1` for every `a ∈ A`
  have hfin : ∀ a ∈ A, a ^ 2 = 1 := by
    intro a ha
    have hc₁ : ⁅y₁, a⁆ ∈ Subgroup.center P := by
      have hmem : ⁅y₁, a⁆ ∈ Work.Higman.powSub A 2 := by
        rw [← hCAd]
        exact Subgroup.commutator_mem_commutator hy₁C ha
      exact h.omega1_le_center (by rw [← htop]; exact hmem)
    have hc₂ : ⁅y₂, a⁆ ∈ Subgroup.center P := by
      have hmem : ⁅y₂, a⁆ ∈ Work.Higman.powSub A 2 := by
        rw [← hCAd]
        exact Subgroup.commutator_mem_commutator hy₂C ha
      exact h.omega1_le_center (by rw [← htop]; exact hmem)
    have e1 : ⁅y₁, a⁆ = a ^ 2 := hkey y₁ hy₁C hy₁A a ha
    have e2 : ⁅y₂, a⁆ = a ^ 2 := hkey y₂ hy₂C hy₂A a ha
    have e3 : ⁅y₁ * y₂, a⁆ = a ^ 2 :=
      hkey (y₁ * y₂) (C.mul_mem hy₁C hy₂C) hy₁y₂A a ha
    have hmul : ⁅y₁ * y₂, a⁆ = ⁅y₁, a⁆ * ⁅y₂, a⁆ := by
      rw [commutatorElement_mul_left_eq_conj_mul]
      have hconj : y₁ * ⁅y₂, a⁆ * y₁⁻¹ = ⁅y₂, a⁆ := by
        rw [show y₁ * ⁅y₂, a⁆ * y₁⁻¹ = ⁅y₂, a⁆ * (y₁ * y₁⁻¹) by
          rw [(Subgroup.mem_center_iff.mp hc₂) y₁]; group]
        group
      rw [hconj]
      exact (Subgroup.mem_center_iff.mp hc₁) ⁅y₂, a⁆
    have h4 : a ^ 2 * a ^ 2 = 1 := by
      have ha2 : a ^ 2 ∈ Work.Higman.omega1 P := by
        rw [← htop]; exact Work.Higman.pow_mem_powSub ha
      have h5 := h.mem_omega1.mp ha2
      rwa [pow_two] at h5
    rw [hmul, e1, e2] at e3
    rw [e3] at h4
    exact h4
  -- hence `A ≤ Ω₁(P) = A²`, so `A = A²`, contradiction
  have hAle : A ≤ Work.Higman.powSub A 2 := by
    rw [htop]
    intro a ha
    exact h.mem_omega1.mpr (hfin a ha)
  exact hA_ne_A2 (le_antisymm hAle (Work.Higman.powSub_le (by norm_num : 0 < 2)))

/-- **The residual case of the gap.**  `⁅C,C⁆ = C² = A²`, `⁅C,A⁆ = A²` and `⁅C,⊤⁆ = A`: `C` is a
`ξ`-length-`3` subgroup (of type `B(n,1,ε)` or `C(n,φ)`) of a `ξ`-length-`4` group, i.e. exactly
the configuration excluded by Higman's Lemma 13 *("there is no Suzuki 2-group of `ξ`-length
greater than `3`")*: `P = C·D` where `D` is a second minimal cover with `C ∩ D = A`, `C/A` and
`D/A` are two `ξ`-irreducible constituents of `P/A`, and the commutator pairing pairs them
perfectly with `A/A²`.  The exclusion needs the eigenvalue bookkeeping (`Q3.axis_resonance`). -/
theorem c4_gap_hard_false (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : Work.Higman.powSub C 2 = Work.Higman.powSub A 2)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2)
    (hcent : Subgroup.centralizer (A : Set P) = A)
    (hCP : ⁅C, (⊤ : Subgroup P)⁆ = A) : False := by
  by_cases hb : ∀ y ∈ C, y ∉ A → ∀ a ∈ A, (a * y) ^ 2 = y ^ 2
  · exact c4_gap_shift_false h hA hNA hGs hsq hA4 htop hcard hCn hCinv hAC hCA hcover hC2 hCd
      hCAd hb
  · -- **Residual (case (a)).**  There are `y ∈ C∖A` and `a ∈ A` with `(a·y)² ≠ y²`, i.e. the
    -- homomorphism `ψ_y : A/A² → A²`, `ā ↦ a²·⁅y,a⁆` is non-trivial.  This is exactly the
    -- configuration of `H8/NOTES_c4_gap_session10.md` §4 (R): the remaining obstruction is the
    -- Hall–Witt/Jacobi identity for the perfect pairing `Φ̄ : A/A² × P/A → A²`,
    -- `Φ̄(ā,x̄) = ⁅a,x⁆`, which rules out the final case exactly as in Higman's Lemma 13.
    --
    -- This is Higman's Lemma 8 in the *maximal* setting, available in the workspace as
    -- `Work.Higman.NSM.noSquareMaximal` (Higman 1963, §5–§6: a `ξ`-invariant abelian normal `A`
    -- with `[P,P] = A`, `A² = Ω₁(P)`, `A⁴ = 1` and `|A| = |Ω₁(P)|²` cannot exist).  The module
    -- `Submission.Work.NSDEEP.All` exposes the same theorem under an axiom-clean, import-safe
    -- name (`Work.Higman.NSDEEP.noSquareMaximal`), the original `NSM` module being downstream of
    -- this file.
    push_neg at hb
    exact Work.Higman.NSDEEP.noSquareMaximal h hA.abelian hA.map_eq
      (fun B hBn hBinv hBab hAB => hmax B ⟨hBn, hBinv, hBab⟩ hAB) hNA hGs hsq hA4 htop hcard

/-- **The gap case `C' = C² = A²` of the `C₄` exclusion.**  With `C` a minimal `ξ`-invariant
normal cover of `A` and `⁅C,C⁆ = C² = A²`, the two dichotomies reduce to the central case
(`c4_gap_central_false`) or, after computing `C_P(A) = A`, to `⁅C,⊤⁆ ∈ {A², A}`: the first is
impossible by `C4Cover.c4_branch_CP_A2` and the second is the residual case `c4_gap_hard_false`. -/
theorem c4_gap_false (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2_le : Work.Higman.powSub C 2 ≤ A)
    (hC2 : Work.Higman.powSub C 2 = Work.Higman.powSub A 2)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2) : False := by
  haveI : A.Normal := hA.normal
  have hCA_le : ⁅C, A⁆ ≤ Work.Higman.powSub A 2 := by
    calc ⁅C, A⁆ ≤ ⁅C, C⁆ := Subgroup.commutator_mono le_rfl hAC
      _ = Work.Higman.powSub A 2 := hCd
  rcases c4_gap_comm_C_A_dichotomy h hA htop hA4 hcard hAC hCinv hCd with hb | hmid
  · exact c4_gap_central_false h hA hNA hGs hsq hA4 htop hCn hCinv hAC hCA hcover hC2_le hCd
      (fun c hc a ha => by
        have h1 : (⁅c, a⁆ : P) ∈ (⊥ : Subgroup P) := by
          rw [← hb]
          exact Subgroup.commutator_mem_commutator hc ha
        exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1))
  · have hcent : Subgroup.centralizer (A : Set P) = A :=
      Work.Higman.HS.centralizer_eq_A_of_comm_C_A h hA.map_eq hA.abelian hNA hGs hsq hA4 htop
        hcard hCn hCinv hAC hcover hmid
    rcases c4_gap_comm_C_top_dichotomy h hA htop hA4 hGs hCinv hCd with hcp | hcp
    · exact Work.Higman.C4Cover.c4_branch_CP_A2 h hA.normal hA.abelian hGs hsq hA4 htop hcard
        hcent hCn hCinv hAC hCA hcp
    · exact c4_gap_hard_false h hA hmax hNA hGs hsq hA4 htop hcard hCn hCinv hAC hCA hcover
        hC2 hCd hmid hcent hcp

/-- **The `C₄` exclusion (Higman's Theorem 1).**  The `C₄` shape of Higman's Lemma 8 is
impossible: there is no maximal `ξ`-invariant abelian normal subgroup `A` with `Ω₁(P) ≤ A`,
`[P,P] = A`, all squares in `A`, `A⁴ = ⊥`, `A² = Ω₁(P)` and `|A| = |Ω₁(P)|²`.

Case analysis on a minimal `ξ`-invariant normal cover `C > A`: `C' = ⊥` contradicts maximality;
`C' = A` contradicts Higman's Lemma 8 (`exp A ≤ 2`); for `C' = A²`: `C² = ⊥` gives `C ≤ Ω₁(P)`,
`C² = A` contradicts Higman's Lemma 7, and the remaining case `C² = A²` is
`c4_cover_deriv_sq_false`. -/
-- Renamed `c4_exclusion` -> `c4_exclusion_alt` (area owner, 2026-10-06): this file
-- declared a second `Work.Higman.c4_exclusion`, clashing with the dedicated
-- `Submission/Work/Higman/H8/c4_exclusion.lean` whenever both were imported (e.g. by the
-- deliverable's `Main.lean`).  Nothing outside this file used the copy.
theorem c4_exclusion_alt {A : Subgroup P} (h : Work.Higman.IsSuzuki2Grp P)
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2) : False := by
  classical
  -- a minimal `ξ`-invariant normal cover of `A`
  have hA_ne_top : (⊤ : Subgroup P) ≠ A := by
    intro htopA
    obtain ⟨x, y, hxy⟩ := h.noncomm
    have hx : x ∈ A := htopA ▸ Subgroup.mem_top x
    have hy : y ∈ A := htopA ▸ Subgroup.mem_top y
    exact hxy (hA.abelian x hx y hy)
  obtain ⟨C, hCn, hCinv, hAC, -, hCA, hcover⟩ :=
    Work.Higman.MSA.exists_minimal_covering h (A := A) (M := ⊤) Subgroup.normal_top
      (by rw [Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective]) le_top hA_ne_top
  have hCd_le : ⁅C, C⁆ ≤ A := (Subgroup.commutator_mono le_top le_top).trans (le_of_eq hGs)
  have hCd_inv : (⁅C, C⁆).map (h.xi : MulAut P).toMonoidHom = ⁅C, C⁆ := by
    rw [Subgroup.map_commutator, hCinv]
  have hC2_le : Work.Higman.powSub C 2 ≤ A := by
    rw [Work.Higman.powSub, Subgroup.closure_le]
    rintro y ⟨x, -, rfl⟩
    exact hsq x
  have hC2_inv : (Work.Higman.powSub C 2).map (h.xi : MulAut P).toMonoidHom
      = Work.Higman.powSub C 2 := by
    rw [Work.Higman.map_powSub (h.xi : MulAut P) hCinv 2]
  rcases c4_xi_inv_sub_trichotomy h hA htop hA4 hCd_le hCd_inv with hbot | hA2 | hAeq
  · -- `C' = ⊥`: `C` is abelian, contradicting maximality of `A`
    have hCcomm : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x := by
      intro x hx y hy
      have hmem : ⁅x, y⁆ ∈ (⁅C, C⁆ : Subgroup P) :=
        Subgroup.commutator_mem_commutator hx hy
      have h1 : ⁅x, y⁆ = 1 := by
        have h2 : ⁅x, y⁆ ∈ (⊥ : Subgroup P) := by rw [← hbot]; exact hmem
        exact Subgroup.mem_bot.mp h2
      exact (commutatorElement_eq_one_iff_commute.mp h1).eq
    exact hCA (hmax C ⟨hCn, hCinv, hCcomm⟩ hAC)
  · -- `C' = A²`: further case analysis on `C²`
    rcases c4_xi_inv_sub_trichotomy h hA htop hA4 hC2_le hC2_inv with hC2bot | hC2A2 | hC2A
    · -- `C² = ⊥`: `C ≤ Ω₁(P) ≤ A`, contradicting `A < C`
      have hCle : C ≤ Work.Higman.omega1 P := by
        intro x hx
        refine h.mem_omega1.mpr ?_
        have hmem : x ^ 2 ∈ Work.Higman.powSub C 2 := Work.Higman.pow_mem_powSub hx
        rw [hC2bot] at hmem
        have h1 : x ^ 2 = 1 := Subgroup.mem_bot.mp hmem
        rw [← h1, pow_two]
      exact hCA (le_antisymm (hCle.trans hNA) hAC)
    · -- `C² = A²`: the residual case of the `C₄` exclusion
      exact c4_gap_false h hA hmax hNA hGs hsq hA4 htop hcard hCn hCinv hAC (Ne.symm hCA)
        hcover hC2_le hC2A2 hA2
    · -- `C² = A`: Higman's Lemma 7 makes `C` abelian, contradicting maximality of `A`
      have hPhi : Work.Higman.powSub C 2 ⊔ ⁅C, C⁆ = A := by
        rw [hC2A, hA2]
        exact sup_of_le_left (Work.Higman.powSub_le (by norm_num))
      have hCcomm : ∀ x ∈ C, ∀ y ∈ C, x * y = y * x :=
        Work.Higman.higman9_case_deriv_le_sq h hA hCn hCinv hAC (Ne.symm hCA) hcover hPhi
          (by rw [hA2, htop])
      exact hCA (hmax C ⟨hCn, hCinv, hCcomm⟩ hAC)
  · -- `C' = A`: Higman's Lemma 8 gives `exp A ≤ 2`, so `A ≤ Ω₁(P) = A²`
    have hsq' : ∀ a ∈ A, a * a = 1 :=
      Work.Higman.higman_lemma8 h hA hCn hCinv hAC (Ne.symm hCA) hcover hC2_le hAeq
    have hAle : A ≤ Work.Higman.powSub A 2 := by
      rw [htop]
      intro a ha
      exact h.mem_omega1.mpr (by rw [pow_two]; exact hsq' a ha)
    have hAeq2 : A = Work.Higman.powSub A 2 :=
      le_antisymm hAle (Work.Higman.powSub_le (by norm_num))
    have hc : Nat.card ↥A = Nat.card ↥(Work.Higman.powSub A 2) :=
      congrArg (fun X : Subgroup P => Nat.card ↥X) hAeq2
    rw [hcard, htop] at hc
    have hq4 : 4 ≤ Nat.card ↥(Work.Higman.omega1 P) := h.omega1_card_ge_four
    have hmul : Nat.card ↥(Work.Higman.omega1 P) * (Nat.card ↥(Work.Higman.omega1 P) - 1) = 0 := by
      rw [Nat.mul_sub_left_distrib, mul_one, ← pow_two, hc, Nat.sub_self]
    rcases Nat.mul_eq_zero.mp hmul with h1 | h1
    · omega
    · omega

/-! ## The odd-order-power reduction (Higman §2)

The `C₄` gap case is attacked with an automorphism of *odd* order which is still transitive on
the involutions: the kernel of its action on `Ω₁(P)` is then an odd-order group, which makes the
`higman_lemma2` obstruction applicable.  This section supplies the reduction. -/

/-- **Arithmetic.**  If `n` is odd then for every `a` and `j` there is `t` with
`2 ^ a ∣ j + t * n`: the odd number `n` runs through all residue classes modulo `2 ^ a`. -/
theorem exists_pow_two_dvd_add_mul {n : ℕ} (hn : Odd n) (a j : ℕ) :
    ∃ t : ℕ, 2 ^ a ∣ j + t * n := by
  induction a generalizing j with
  | zero => exact ⟨0, one_dvd _⟩
  | succ a ih =>
      obtain ⟨t, c, hc⟩ := ih j
      rcases Nat.even_or_odd c with hcE | hcO
      · obtain ⟨c', rfl⟩ := hcE
        exact ⟨t, ⟨c', by rw [hc, pow_succ]; ring⟩⟩
      · have hcn : Even (c + n) := hcO.add_odd hn
        obtain ⟨c', hc'⟩ := hcn
        have h3 : j + (t + 2 ^ a) * n = 2 ^ a * (c + n) := by
          calc j + (t + 2 ^ a) * n = (j + t * n) + 2 ^ a * n := by ring
            _ = 2 ^ a * c + 2 ^ a * n := by rw [hc]
            _ = 2 ^ a * (c + n) := by ring
        exact ⟨t + 2 ^ a, ⟨c', by rw [h3, hc', pow_succ]; ring⟩⟩

/-- **Higman's first step of the odd-order extraction.**  `ξ ^ (|Ω₁(P)| - 1)` fixes `Ω₁(P)`
pointwise (the `⟨ξ⟩`-orbit of an involution is the whole set of involutions, of size
`|Ω₁(P)| - 1`). -/
theorem pow_card_sub_one_fixes_omega1 (h : Work.Higman.IsSuzuki2Grp P) :
    ∀ z : P, z ∈ Work.Higman.omega1 P →
      (h.xi ^ (Nat.card ↥(Work.Higman.omega1 P) - 1)) z = z :=
  (Work.Higman.xi_pow_triv_omega1_iff h (Nat.card ↥(Work.Higman.omega1 P) - 1)).mpr
    (dvd_refl _)

/-- **Odd-order extraction.**  Some power of `ξ` has odd order and is still transitive on the
involutions of `P` (so that `(P, ξ ^ k)` is again a Suzuki structure with an odd-order
automorphism). -/
theorem exists_odd_order_power_trans (h : Work.Higman.IsSuzuki2Grp P) :
    ∃ ϑ : MulAut P, Odd (orderOf ϑ) ∧
      ∀ u v : P, orderOf u = 2 → orderOf v = 2 → ∃ j : ℕ, (ϑ ^ j) u = v := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  have hm0 : orderOf h.xi ≠ 0 := by
    have h1 : orderOf h.xi ∣ Fintype.card (MulAut P) :=
      orderOf_dvd_iff_pow_eq_one.mpr pow_card_eq_one
    intro hcon
    exact (Fintype.card_pos_iff.mpr ⟨1⟩).ne' (zero_dvd_iff.mp (hcon ▸ h1))
  obtain ⟨a, r, hr, hm⟩ := Nat.exists_eq_two_pow_mul_odd hm0
  refine ⟨h.xi ^ 2 ^ a, ?_, ?_⟩
  · rw [orderOf_pow, hm, Nat.gcd_eq_right (dvd_mul_right _ _),
      Nat.mul_div_right _ (pow_pos (by norm_num) a)]
    exact hr
  · intro u v hu hv
    obtain ⟨j, hj⟩ := h.trans u v hu hv
    have hvΩ : v ∈ Work.Higman.omega1 P :=
      h.mem_omega1.mpr (by rw [← orderOf_dvd_iff_pow_eq_one, hv])
    have hfix : (h.xi ^ (Nat.card ↥(Work.Higman.omega1 P) - 1)) v = v :=
      pow_card_sub_one_fixes_omega1 h v hvΩ
    obtain ⟨n, hn⟩ := h.exists_card_omega1_eq_two_pow
    have hn1 : 1 ≤ n := by
      by_contra hcon
      push Not at hcon
      interval_cases n
      · rw [pow_zero] at hn
        have h4 := h.omega1_card_ge_four
        omega
    have hqodd : Odd (Nat.card ↥(Work.Higman.omega1 P) - 1) := by
      rw [hn]
      obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      refine ⟨2 ^ n' - 1, by
        have h1 : 1 ≤ 2 ^ n' := Nat.one_le_pow n' 2 (by norm_num)
        have h2 : 2 ^ n' * 2 = 2 * (2 ^ n' - 1) + 2 := by omega
        rw [pow_succ, h2]
        omega⟩
    obtain ⟨t, s, hs⟩ := exists_pow_two_dvd_add_mul hqodd a j
    refine ⟨s, ?_⟩
    have h2 : h.xi ^ (j + t * (Nat.card ↥(Work.Higman.omega1 P) - 1)) = h.xi ^ (2 ^ a * s) := by
      rw [hs]
    have h3 : (h.xi ^ 2 ^ a) ^ s = h.xi ^ (2 ^ a * s) := by rw [pow_mul]
    rw [h3, ← h2]
    exact Work.Higman.pow_add_mul_pow_eq_of_fixes h hj hfix t

/-- **Step (a) of the kernel analysis: an odd-order element fixing `Ω₁(P)` fixes `A`.**
If `k` has odd order, normalises the abelian subgroup `A` with `A² = Ω₁(P)` and fixes `Ω₁(P)`
pointwise, then `k` fixes `A` pointwise: `k ^ 2` is the identity on `A`
(`apply_apply_eq_self_of_fixes_omega1`), and an odd-order automorphism of order dividing `2`
is trivial. -/
theorem odd_order_fixes_of_fixes_omega1 {A : Subgroup P} {k : MulAut P}
    (hAinv : A.map (k : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hkΩ : ∀ z ∈ Work.Higman.omega1 P, k z = z)
    (hodd : Odd (orderOf k)) :
    ∀ a ∈ A, k a = a := by
  have hk2 : ∀ a ∈ A, k (k a) = a :=
    Work.Higman.apply_apply_eq_self_of_fixes_omega1 hAinv hAab htop hkΩ
  have hkk : ∀ b ∈ A, (k ^ 2) b = b := by
    intro b hb
    rw [pow_two, MulAut.mul_apply]
    exact hk2 b hb
  have hpow : ∀ t : ℕ, ∀ b ∈ A, ((k ^ 2) ^ t) b = b := by
    intro t
    induction t with
    | zero => intro b _; simp
    | succ t ih => intro b hb; rw [pow_succ, MulAut.mul_apply, hkk b hb, ih b hb]
  obtain ⟨s, hs⟩ := hodd
  intro a ha
  have hka : k a ∈ A := by
    have := Subgroup.mem_map_of_mem (k : MulAut P).toMonoidHom ha
    rwa [hAinv] at this
  have h1 : (k ^ (2 * s + 1)) a = a := by
    rw [← hs, pow_orderOf_eq_one]
    simp
  have h2 : (k ^ (2 * s + 1)) a = k a := by
    have h4 : k ^ (2 * s + 1) = (k ^ 2) ^ s * k := by rw [pow_succ, ← pow_mul]
    rw [h4, MulAut.mul_apply]
    exact hpow s (k a) hka
  rw [← h2]
  exact h1

/-- **Step (a2) of the kernel analysis.**  For an odd-order power `ϑ = ξ ^ k` (as produced by
`exists_odd_order_power_trans`), every power `ϑ ^ j` that fixes `Ω₁(P)` pointwise fixes the
abelian `A` pointwise. -/
theorem odd_power_kernel_fixes_A {A : Subgroup P} (h : Work.Higman.IsSuzuki2Grp P)
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    {k j : ℕ} (hodd : Odd (orderOf (h.xi ^ k)))
    (hjΩ : ∀ z ∈ Work.Higman.omega1 P, ((h.xi ^ k) ^ j) z = z) :
    ∀ a ∈ A, ((h.xi ^ k) ^ j) a = a := by
  have hAinv' : A.map ((((h.xi ^ k) ^ j) : MulAut P)).toMonoidHom = A := by
    have h1 : (((h.xi ^ k) ^ j) : MulAut P) = h.xi ^ (k * j) := by rw [pow_mul]
    rw [h1]
    exact Work.Higman.map_pow_xi_eq h hAinv (k * j)
  refine odd_order_fixes_of_fixes_omega1 hAinv' hAab htop hjΩ ?_
  exact hodd.of_dvd_nat (orderOf_pow_dvd (x := ((h.xi ^ k) : MulAut P)) j)

/-- **Step (b) of the kernel analysis, in the form `K` acts trivially on `P ⧸ A`.**  If `A` is
a normal subgroup with `C_P(A) = A` and `k` fixes `A` pointwise, then `k` moves every element
only inside its coset modulo `A`: `k x * x⁻¹ ∈ A`. -/
theorem kernel_mul_inv_mem_of_centralizer {A : Subgroup P}
    (hcent : Subgroup.centralizer (A : Set P) = A) (hAn : A.Normal) {k : MulAut P}
    (hk : ∀ a ∈ A, k a = a) (x : P) :
    k x * x⁻¹ ∈ A := by
  rw [← hcent]
  exact Subgroup.mem_centralizer_iff.mpr
    (fun a ha => Work.Higman.commute_mul_inv_of_fixes_pointwise hAn hk x ha)

/-- **The conjugation relation for `d = k x * x⁻¹`.**  If `k` fixes `x ^ 2` (e.g. `k` fixes `A`
pointwise and `x ^ 2 ∈ A`), then `x` inverts `d`: `x * d * x⁻¹ = d⁻¹`.

(Indeed `(k x) ^ 2 = k (x ^ 2) = x ^ 2`, i.e. `d * x * d = x`, whence `x * d = d⁻¹ * x`.) -/
theorem conj_d_eq_inv {A : Subgroup P} {k : MulAut P}
    (hkq : ∀ y ∈ A, k y = y) {x : P} (hx2 : x ^ 2 ∈ A) :
    x * (k x * x⁻¹) * x⁻¹ = (k x * x⁻¹)⁻¹ := by
  set d := k x * x⁻¹ with hd
  have hkx : k x = d * x := by rw [hd]; group
  have hx2' : x * x ∈ A := by rwa [pow_two] at hx2
  have h1 : d * x * (d * x) = x * x := by
    rw [show d * x = k x from hkx.symm, ← map_mul]
    exact hkq (x * x) hx2'
  have h2 : d * x * d = x := by
    have h1' : d * x * d * x = x * x := by
      rw [show d * x * d * x = d * x * (d * x) from by group]
      exact h1
    calc d * x * d = d * x * d * x * x⁻¹ := by group
      _ = x * x * x⁻¹ := by rw [h1']
      _ = x := by group
  have h3 : x * d = d⁻¹ * x := by
    calc x * d = d⁻¹ * (d * x * d) := by group
      _ = d⁻¹ * x := by rw [h2]
  rw [h3]
  group

/-- **The first half of the `d²` step.**  With `d = k x * x⁻¹` (where `k` fixes `A` pointwise and
`x ^ 2 ∈ A`), the commutator `⁅x, d⁆` equals `d⁻²`, so `d ^ 2 ∈ A`. -/
theorem sq_d_mem_of_conj {A : Subgroup P} (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A) {k : MulAut P}
    (hkq : ∀ y ∈ A, k y = y) {x : P} (hx2 : x ^ 2 ∈ A) :
    (k x * x⁻¹) ^ 2 ∈ A := by
  have hconj := conj_d_eq_inv hkq hx2
  have hmem : ⁅x, k x * x⁻¹⁆ ∈ A := by
    rw [← hGs]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top _)
  rw [commutatorElement_def, hconj] at hmem
  have hsq : (k x * x⁻¹) ^ 2 = ((k x * x⁻¹)⁻¹ * (k x * x⁻¹)⁻¹)⁻¹ := by
    rw [pow_two]; group
  rw [hsq]
  exact A.inv_mem hmem

/-- **`ξ` is transitive on the non-zero cosets of `A/A²`.**  For `x, y` whose squares lie outside
`A²` there is `k` with `ξ^k (x²) · (y²)⁻¹ ∈ A²`.

This is the existing `Work.Higman.exists_xi_pow_mul_inv_mem_powSub_two` (`Fq_structure.lean`)
applied to `a := x²`, `b := y²`.  The hypothesis is **not** vacuous: `x² ∉ A²` forces `x ∉ A`
(for `x ∈ A` the element `x²` is a square of an element of `A`, so `x² ∈ A²` by definition of
`A² = powSub A 2`), hence `x² A²` is a genuine non-zero coset of `A/A²`.  The coterminous
statement with hypothesis `a ∈ A` *and* `a² ∉ A²` was vacuous for exactly that reason and has
been removed. -/
theorem xi_orbit_sq_quot (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    {x y : P} (hx2 : x ^ 2 ∉ Work.Higman.powSub A 2) (hy2 : y ^ 2 ∉ Work.Higman.powSub A 2) :
    ∃ k : ℕ, (h.xi ^ k) (x ^ 2) * (y ^ 2)⁻¹ ∈ Work.Higman.powSub A 2 :=
  Work.Higman.exists_xi_pow_mul_inv_mem_powSub_two h hA (hsq x) (hsq y) hx2 hy2

/-- **The branch `E' = A²` of the `C₄` exclusion is impossible.**  For `z` with `z² ∉ A²` the
`ξ`-invariant normal subgroup `E := ⟨A ∪ ξ-orbit(z)⟩` (normal and `ξ`-invariant by
`Q3.ex_subgroup_c4`, applied with `[⊤,⊤] = A`) cannot satisfy `⁅E,E⁆ = A²`: by
`Q3.Dsq_sq_mem_powSub_two` every square of an element of `E` would then lie in `A²`, and `z ∈ E`
(as `ξ ^ 0 z`) gives `z² ∈ A²`, contradicting `z² ∉ A²`. -/
theorem ex_subgroup_deriv_ne_powSub_two (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    {z : P} (hz2 : z ^ 2 ∉ Work.Higman.powSub A 2) :
    ⁅Subgroup.closure ((A : Set P) ∪ Set.range (fun k : ℕ => (h.xi ^ k) z)),
      Subgroup.closure ((A : Set P) ∪ Set.range (fun k : ℕ => (h.xi ^ k) z))⁆ ≠
      Work.Higman.powSub A 2 := by
  intro hEd
  obtain ⟨hEn, hEinv, hAE, hzE⟩ :=
    Work.Higman.Q3.ex_subgroup_c4 h hA.map_eq hA.normal (le_of_eq hGs) z
  exact hz2 (Work.Higman.Q3.Dsq_sq_mem_powSub_two h hA.map_eq hA.abelian hNA htop
    hEn hEinv hAE hEd z hzE)

/-- **In the `C₄` setting some square of `P` misses `A²`.**  Otherwise `P² ≤ A²`, and since
`A = [P,P] ≤ P²` (for a `2`-group the derived subgroup lies in the subgroup of squares:
`[x,y] = x² · (x⁻¹y)² · (y²)⁻¹`), transitivity gives `A ≤ A²`; together with `A² ≤ A` this is
`A = A²`, and `A² = Ω₁(P)` makes `|A| = q` while `hcard` says `|A| = q²`, so `q² = q` — against
`q ≥ 4`. -/
theorem exists_sq_not_mem_powSub_two (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hGs : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ = A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2) :
    ∃ z : P, z ^ 2 ∉ Work.Higman.powSub A 2 := by
  by_contra hcon
  push_neg at hcon
  have hP2 : Work.Higman.powSub (⊤ : Subgroup P) 2 ≤ Work.Higman.powSub A 2 := by
    rw [Work.Higman.powSub, Subgroup.closure_le]
    rintro y ⟨x, -, rfl⟩
    exact hcon x
  have hderiv : ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ ≤ Work.Higman.powSub (⊤ : Subgroup P) 2 := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    have key : ⁅x, y⁆ = x ^ 2 * (x⁻¹ * y) ^ 2 * (y ^ 2)⁻¹ := by
      rw [commutatorElement_def, pow_two (a := x), pow_two (a := x⁻¹ * y), pow_two (a := y)]
      group
    rw [key]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _
      (Work.Higman.pow_mem_powSub (n := 2) (Subgroup.mem_top x))
      (Work.Higman.pow_mem_powSub (n := 2) (Subgroup.mem_top (x⁻¹ * y))))
      (Subgroup.inv_mem _ (Work.Higman.pow_mem_powSub (n := 2) (Subgroup.mem_top y)))
  have hAle : A ≤ Work.Higman.powSub A 2 := by
    have h1 := hderiv.trans hP2
    rwa [hGs] at h1
  have hAeq : A = Work.Higman.powSub A 2 :=
    le_antisymm hAle (Work.Higman.powSub_le (by norm_num : 0 < 2))
  have hq2 : Nat.card ↥(Work.Higman.omega1 P) * Nat.card ↥(Work.Higman.omega1 P)
      = Nat.card ↥(Work.Higman.omega1 P) := by
    rw [← pow_two, ← hcard, hAeq, htop]
  have hqle : Nat.card ↥(Work.Higman.omega1 P) ≤ 1 := by
    have h1 : Nat.card ↥(Work.Higman.omega1 P) * Nat.card ↥(Work.Higman.omega1 P)
        ≤ Nat.card ↥(Work.Higman.omega1 P) * 1 := by rw [mul_one, hq2]
    exact Nat.le_of_mul_le_mul_left h1
      (Nat.lt_of_lt_of_le (by norm_num : 0 < 4) h.omega1_card_ge_four)
  exact absurd (le_trans h.omega1_card_ge_four hqle) (by norm_num)

/-! ## The Jacobi relation of the `C₄` gap

In the gap `⁅C,C⁆ = A² = Ω₁(P)` the class-three Jacobi identity
(`Work.Higman.Q3.crux_class_three_jacobi`) together with the centrality of `⁅C,C⁆ = A² ⊆ Z(P)`
gives, for `x, z ∈ C` and arbitrary `y`,

  `⁅⁅x,y⁆,z⁆ = ⁅⁅y,z⁆,x⁆`,

the "resonance" relation which is the computational heart of Higman's Lemma 13 (the pairing
`(x̄,ȳ) ↦ ⁅x,y⁆` has to satisfy the graded Jacobi identity).  In the two-cover configuration
`P = C·Y`, `C ∩ Y = A` this reads `φ(B(x,y),z) = φ(B(y,z),x)` for `x,z ∈ C/A` and `y`, which
combined with the Frobenius/eigenvalue bookkeeping (`resonance_of_equivariant_biadditive`,
`Q3.two_pow_add_eq_pow`) yields `False`; see `H8/NOTES_c4_gap_session11.md`. -/

/-- **The Jacobi relation of the `C₄` gap.**  For `x, z ∈ C` and arbitrary `y`,
`⁅⁅x, y⁆, z⁆ = ⁅⁅y, z⁆, x⁆`.

Both sides lie in `⁅A,⊤⁆ = A² ⊆ Z(P)`; the class-three Jacobi identity gives
`⁅⁅x,y⁆,z⁆ · ⁅⁅y,z⁆,x⁆ · ⁅⁅z,x⁆,y⁆ = 1` with `⁅⁅z,x⁆,y⁆ = 1` (as `⁅z,x⁆ ∈ ⁅C,C⁆ = A²` is
central), and `⁅⁅y,z⁆,x⁆` is an involution (it lies in `⁅A,⊤⁆ = A² = Ω₁(P)`), so the inverse is
the element itself. -/
theorem c4_jacobi_pairing (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hAtop : ⁅A, (⊤ : Subgroup P)⁆ = Work.Higman.powSub A 2)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    {x z : P} (hx : x ∈ C) (hz : z ∈ C) (y : P) :
    ⁅⁅x, y⁆, z⁆ = ⁅⁅y, z⁆, x⁆ := by
  have hzx : ⁅z, x⁆ ∈ Work.Higman.powSub A 2 := by
    rw [← hCd]; exact Subgroup.commutator_mem_commutator hz hx
  have hzx_c : ⁅z, x⁆ ∈ Subgroup.center P := h.omega1_le_center (htop ▸ hzx)
  have hzx1 : ⁅⁅z, x⁆, y⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact ((Subgroup.mem_center_iff.mp hzx_c) y).symm
  have hj : ⁅⁅x, y⁆, z⁆ * ⁅⁅y, z⁆, x⁆ * ⁅⁅z, x⁆, y⁆ = 1 :=
    Work.Higman.Q3.crux_class_three_jacobi h hA hGs hsq htop x y z
  rw [hzx1, mul_one] at hj
  have hyz : ⁅y, z⁆ ∈ A := by
    have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_top y) (Subgroup.mem_top z)
    rwa [hGs] at h1
  have hB : ⁅⁅y, z⁆, x⁆ ∈ Work.Higman.powSub A 2 := by
    have h1 : ⁅⁅y, z⁆, x⁆ ∈ (⁅A, (⊤ : Subgroup P)⁆ : Subgroup P) :=
      Subgroup.commutator_mem_commutator hyz (Subgroup.mem_top x)
    rwa [hAtop] at h1
  have hBsq : ⁅⁅y, z⁆, x⁆ * ⁅⁅y, z⁆, x⁆ = 1 := by
    have h2 : ⁅⁅y, z⁆, x⁆ ^ 2 = 1 := h.mem_omega1.mp (htop ▸ hB)
    rwa [pow_two] at h2
  have h1 : ⁅⁅x, y⁆, z⁆ = (⁅⁅y, z⁆, x⁆)⁻¹ := eq_inv_of_mul_eq_one_left hj
  rw [h1, inv_eq_of_mul_eq_one_right hBsq]

theorem c4_card_le {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P) :
    Nat.card P ≤ (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 := by
  by_cases hcomm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Work.Higman.omega1 P
  · exact c4_card_le_of_comm_le_omega1 h hcomm
  · obtain ⟨A, hA, hmax, hNA, hGs, hsq, hA4, htop, hcard⟩ := c4_data h hcomm
    exact (c4_exclusion_alt h hA hmax hNA hGs hsq hA4 htop hcard).elim

end Work.Higman.H8
