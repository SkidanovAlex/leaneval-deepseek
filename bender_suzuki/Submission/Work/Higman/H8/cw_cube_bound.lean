/-
Copyright (c) 2024. All rights reserved.

# Chevalley--Warning bound `|M| ≤ |Ω₁(P)|³` for subgroups with `M² ⊆ Ω₁(P)`, `[M,M] ⊆ Ω₁(P)`

`P` a Suzuki 2-group, `M ≤ P` with `Ω₁(P) ≤ M`, every square of `M` in `Ω₁(P)` and
`[M,M] ⊆ Ω₁(P)`.  Then `Q : M/Ω₁(P) → Ω₁(P)`, `Q(ȩ) = m²` is a well defined *anisotropic*
quadratic form whose polar form is the commutator `[·,·]` (valued in the central group
`Ω₁(P)`), so Chevalley--Warning gives `|M/Ω₁(P)| ≤ |Ω₁(P)|²`, whence `|M| ≤ |Ω₁(P)|³`.

This is a direct generalisation of `Work.Higman.Q3.card_le_cube_of_Dsq` (there `A² = Ω₁(P)`,
`M² ⊆ A²`, `[M,M] = A²`); the proof below is that proof with `A` replaced by `Ω₁(P)`, the
commutator identities being restated privately so that nothing from `card_eq_sq_or_cube`
needs importing.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.OmegaAux
import Submission.Work.Higman.chevalley_warning

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option linter.style.longLine false

namespace Work.Higman.H8

open scoped commutatorElement

/-! ## Class-two commutator identities (self contained copies) -/

private theorem cw_mul_mul_inv_eq_commutator_mul {G : Type*} [Group G] (x y : G) :
    x * y * x⁻¹ = ⁅x, y⁆ * y := by
  rw [commutatorElement_def]; group

private theorem cw_commutator_central_comm {G : Type*} [Group G]
    (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y z : G) :
    z * ⁅x, y⁆ = ⁅x, y⁆ * z :=
  Subgroup.mem_center_iff.mp
    (hZ (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))) z

private theorem cw_commutator_mul_left {G : Type*} [Group G]
    (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y z : G) :
    ⁅x * y, z⁆ = ⁅x, z⁆ * ⁅y, z⁆ := by
  have hcy : ∀ w : G, w * ⁅y, z⁆ = ⁅y, z⁆ * w := cw_commutator_central_comm hZ y z
  have hcx : ∀ w : G, w * ⁅x, z⁆ = ⁅x, z⁆ * w := cw_commutator_central_comm hZ x z
  have h1 : x * z * x⁻¹ = ⁅x, z⁆ * z := cw_mul_mul_inv_eq_commutator_mul x z
  have h2 : y * z * y⁻¹ = ⁅y, z⁆ * z := cw_mul_mul_inv_eq_commutator_mul y z
  rw [commutatorElement_def]
  rw [show x * y * z * (x * y)⁻¹ * z⁻¹ = x * (y * z * y⁻¹) * x⁻¹ * z⁻¹ by group]
  rw [h2]
  rw [show x * (⁅y, z⁆ * z) * x⁻¹ * z⁻¹ = (x * ⁅y, z⁆) * (z * x⁻¹) * z⁻¹ by group]
  rw [hcy x]
  rw [show (⁅y, z⁆ * x) * (z * x⁻¹) * z⁻¹ = ⁅y, z⁆ * (x * z * x⁻¹) * z⁻¹ by group]
  rw [h1]
  rw [show ⁅y, z⁆ * (⁅x, z⁆ * z) * z⁻¹ = ⁅y, z⁆ * ⁅x, z⁆ by group]
  rw [hcx ⁅y, z⁆]

private theorem cw_commutator_mul_right {G : Type*} [Group G]
    (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y z : G) :
    ⁅z, x * y⁆ = ⁅z, x⁆ * ⁅z, y⁆ := by
  have h1 : ⁅z, x * y⁆ = ⁅x * y, z⁆⁻¹ := by rw [← commutatorElement_inv]
  rw [h1, cw_commutator_mul_left hZ x y z, mul_inv_rev, commutatorElement_inv,
    commutatorElement_inv]
  exact (cw_commutator_central_comm hZ z y ⁅z, x⁆).symm

private theorem cw_commutator_eq_one_of_mem_center_left {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (x : G) : ⁅z, x⁆ = 1 := by
  rw [commutatorElement_def, ← Subgroup.mem_center_iff.mp hz x]
  group

private theorem cw_commutator_eq_one_of_mem_center_right {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (x : G) : ⁅x, z⁆ = 1 := by
  rw [commutatorElement_def, Subgroup.mem_center_iff.mp hz x]
  group

/-! ## The bound -/

/-- **Chevalley–Warning bound `|M| ≤ |Ω₁(P)|³`** for `Ω₁(P) ≤ M`, `M² ⊆ Ω₁(P)`,
`[M,M] ⊆ Ω₁(P)`. -/
theorem card_le_cube_of_sq_le_omega1 {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {M : Subgroup P}
    (hM : Work.Higman.omega1 P ≤ M)
    (hM2 : Work.Higman.powSub M 2 ≤ Work.Higman.omega1 P)
    (hMd : ⁅M, M⁆ ≤ Work.Higman.omega1 P) :
    Nat.card ↥M ≤ (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 := by
  classical
  have hZcent : Work.Higman.omega1 P ≤ Subgroup.center P := h.omega1_le_center
  have hZn : (Work.Higman.omega1 P).Normal := Subgroup.normal_of_le_center hZcent
  let ZD : Subgroup ↥M := (Work.Higman.omega1 P).subgroupOf M
  have hZDn : ZD.Normal := hZn.subgroupOf M
  haveI := hZDn
  -- `ZD` is contained in the centre of `M`
  have hZD_le_center : ZD ≤ Subgroup.center ↥M := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro d
    apply Subtype.ext
    have hzp : ((z : ↥M) : P) ∈ Work.Higman.omega1 P := by
      rwa [Subgroup.mem_subgroupOf] at hz
    exact (Subgroup.mem_center_iff.mp (hZcent hzp)) ((d : ↥M) : P)
  -- `M` has class two
  have hZ2D : ⁅(⊤ : Subgroup ↥M), ⊤⁆ ≤ Subgroup.center ↥M := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    apply hZD_le_center
    rw [Subgroup.mem_subgroupOf]
    rw [show ((⁅x, y⁆ : ↥M) : P) = ⁅(x : P), (y : P)⁆ by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]]
    exact hMd (Subgroup.commutator_mem_commutator x.2 y.2)
  -- squares of `M` lie in `Ω₁(P)`
  have hsqZ : ∀ g : ↥M, (g : P) * (g : P) ∈ Work.Higman.omega1 P := by
    intro g
    have h1 : (g : P) ^ 2 ∈ Work.Higman.powSub M 2 := Work.Higman.pow_mem_powSub g.2
    have h3 := hM2 h1
    rwa [pow_two] at h3
  have hsqZD : ∀ g : ↥M, g * g ∈ ZD := by
    intro g
    rw [Subgroup.mem_subgroupOf]
    exact hsqZ g
  -- commutators of `M` lie in `ZD`
  have hcommZD : ∀ x y : ↥M, ⁅y, x⁆ ∈ ZD := by
    intro x y
    rw [Subgroup.mem_subgroupOf]
    rw [show ((⁅y, x⁆ : ↥M) : P) = ⁅(y : P), (x : P)⁆ by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]]
    exact hMd (Subgroup.commutator_mem_commutator y.2 x.2)
  -- `M / ZD` is abelian
  have hqcomm : ∀ a b : ↥M ⧸ ZD, a * b = b * a := by
    intro a b
    refine Quotient.inductionOn a (fun x => ?_)
    refine Quotient.inductionOn b (fun y => ?_)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hmem : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by
      rw [commutatorElement_def]; group
    rw [hmem]
    exact hcommZD x⁻¹ y⁻¹
  letI : CommGroup (↥M ⧸ ZD) :=
    { (inferInstance : Group (↥M ⧸ ZD)) with mul_comm := hqcomm }
  letI : CommGroup ↥ZD :=
    { (inferInstance : Group ↥ZD) with
      mul_comm := fun a b => Subtype.ext (Subgroup.mem_center_iff.mp (hZD_le_center b.2) a) }
  -- the coset map
  let mkc : ↥M → Additive (↥M ⧸ ZD) := fun z => Additive.ofMul (QuotientGroup.mk z)
  have hsum : ∀ x y : ↥M, mkc x + mkc y = mkc (x * y) := by
    intro x y
    show Additive.ofMul (QuotientGroup.mk x) + Additive.ofMul (QuotientGroup.mk y) =
      Additive.ofMul (QuotientGroup.mk (x * y))
    rw [← ofMul_mul, ← QuotientGroup.mk_mul]
  -- `M / ZD` has exponent two
  have h2V : ∀ v : Additive (↥M ⧸ ZD), (2 : ℕ) • v = 0 := by
    intro v
    refine Quotient.inductionOn v (fun x => ?_)
    change (2 : ℕ) • mkc x = 0
    rw [← ofMul_pow, ofMul_eq_zero]
    have hxx : ((x * x : ↥M) : ↥M ⧸ ZD) = 1 :=
      (QuotientGroup.eq_one_iff (N := ZD) (x * x)).mpr (hsqZD x)
    simpa [pow_two] using hxx
  haveI hmodV : Module (ZMod 2) (Additive (↥M ⧸ ZD)) :=
    AddCommGroup.zmodModule h2V
  -- `ZD` has exponent two
  have h2W : ∀ v : Additive ↥ZD, (2 : ℕ) • v = 0 := by
    intro v
    have hv : v.toMul * v.toMul = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      show ((v.toMul : ↥M) : P) * ((v.toMul : ↥M) : P) = 1
      have hmem : ((v.toMul : ↥M) : P) ∈ Work.Higman.omega1 P := by
        have hh := (v.toMul).2
        rwa [Subgroup.mem_subgroupOf] at hh
      have h2 := h.mem_omega1.mp hmem
      rwa [pow_two] at h2
    have hstep : (2 : ℕ) • v = Additive.ofMul (v.toMul * v.toMul) :=
      calc (2 : ℕ) • v = v + v := two_nsmul v
        _ = Additive.ofMul v.toMul + Additive.ofMul v.toMul := by rw [ofMul_toMul]
        _ = Additive.ofMul (v.toMul * v.toMul) := by rw [← ofMul_mul]
    rw [hstep, ofMul_eq_zero, hv]
  haveI hmodW : Module (ZMod 2) (Additive ↥ZD) :=
    AddCommGroup.zmodModule h2W
  -- the squaring map `qf` on `M` and its descent to `M / ZD`
  let qf : ↥M → ↥ZD := fun g => ⟨g * g, hsqZD g⟩
  have hqw : ∀ a b : ↥M, a⁻¹ * b ∈ ZD → qf a = qf b := by
    intro a b hab
    obtain ⟨z, hz, rfl⟩ : ∃ z ∈ ZD, b = a * z := ⟨a⁻¹ * b, hab, by group⟩
    apply Subtype.ext
    show a * a = (a * z) * (a * z)
    have hzc : z ∈ Subgroup.center ↥M := hZD_le_center hz
    have hzz : z * z = 1 := by
      apply Subtype.ext
      have hzp : (z : P) ∈ Work.Higman.omega1 P := by
        have hh := hz
        rwa [Subgroup.mem_subgroupOf] at hh
      have hz2 := h.mem_omega1.mp hzp
      rwa [pow_two] at hz2
    have hcz : z * a = a * z := (Subgroup.mem_center_iff.mp hzc a).symm
    calc a * a = a * a * (z * z) := by rw [hzz, mul_one]
      _ = a * (a * (z * z)) := by group
      _ = a * ((a * z) * z) := by group
      _ = a * ((z * a) * z) := by rw [hcz]
      _ = (a * z) * (a * z) := by group
  have hqw' : ∀ a b : ↥M, (QuotientGroup.leftRel ZD) a b →
      Additive.ofMul (qf a) = Additive.ofMul (qf b) :=
    fun a b hab => congrArg Additive.ofMul (hqw a b (QuotientGroup.leftRel_apply.mp hab))
  let Q : Additive (↥M ⧸ ZD) → Additive ↥ZD :=
    fun v => Quotient.liftOn v.toMul (fun g => Additive.ofMul (qf g)) hqw'
  have Q_mk : ∀ g : ↥M, Q (mkc g) = Additive.ofMul (qf g) :=
    fun g => congrArg Additive.ofMul
      (Quotient.liftOn_mk (s := QuotientGroup.leftRel ZD)
        (fun g => Additive.ofMul (qf g)) hqw' g)
  have Q_zero : Q 0 = 0 := by
    change Q (mkc 1) = 0
    rw [Q_mk, ofMul_eq_zero]
    apply Subtype.ext
    show (1 : ↥M) * 1 = 1
    group
  have Q_aniso : ∀ v, Q v = 0 → v = 0 := by
    intro v
    refine Quotient.inductionOn v (fun g => ?_)
    intro hv
    have hv' : Q (mkc g) = 0 := hv
    rw [Q_mk, ofMul_eq_zero] at hv'
    have hg : g * g = 1 := congrArg Subtype.val hv'
    have hg2 : (g : P) ^ 2 = 1 := by
      have hc : ((g * g : ↥M) : P) = 1 := congrArg (fun d : ↥M => (d : P)) hg
      rw [Subgroup.coe_mul] at hc
      simpa [pow_two] using hc
    change mkc g = 0
    rw [ofMul_eq_zero, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact h.mem_omega1.mpr hg2
  -- the commutator form
  let bZ : ↥M → ↥M → ↥ZD := fun x y => ⟨⁅y, x⁆, hcommZD x y⟩
  have bZ_mul₁ : ∀ a b y : ↥M, bZ (a * b) y = bZ a y * bZ b y := by
    intro a b y
    apply Subtype.ext
    show ⁅y, a * b⁆ = ⁅y, a⁆ * ⁅y, b⁆
    exact cw_commutator_mul_right hZ2D a b y
  have bZ_mul₂ : ∀ y a b : ↥M, bZ y (a * b) = bZ y a * bZ y b := by
    intro y a b
    apply Subtype.ext
    show ⁅a * b, y⁆ = ⁅a, y⁆ * ⁅b, y⁆
    exact cw_commutator_mul_left hZ2D a b y
  have bZ_wd : ∀ a₁ b₁ a₂ b₂ : ↥M,
      (QuotientGroup.leftRel ZD) a₁ a₂ → (QuotientGroup.leftRel ZD) b₁ b₂ →
      bZ a₁ b₁ = bZ a₂ b₂ := by
    intro a₁ b₁ a₂ b₂ ha hb
    obtain ⟨z, hz, rfl⟩ : ∃ z ∈ ZD, a₂ = a₁ * z :=
      ⟨a₁⁻¹ * a₂, (QuotientGroup.leftRel_apply.mp ha), by group⟩
    obtain ⟨w, hw, rfl⟩ : ∃ w ∈ ZD, b₂ = b₁ * w :=
      ⟨b₁⁻¹ * b₂, (QuotientGroup.leftRel_apply.mp hb), by group⟩
    apply Subtype.ext
    have hzc : z ∈ Subgroup.center ↥M := hZD_le_center hz
    have hwc : w ∈ Subgroup.center ↥M := hZD_le_center hw
    show ⁅b₁, a₁⁆ = ⁅b₁ * w, a₁ * z⁆
    rw [cw_commutator_mul_left hZ2D b₁ w (a₁ * z),
      cw_commutator_eq_one_of_mem_center_left hwc (a₁ * z), mul_one,
      cw_commutator_mul_right hZ2D a₁ z b₁,
      cw_commutator_eq_one_of_mem_center_right hzc b₁, mul_one]
  let bZq : Additive (↥M ⧸ ZD) → Additive (↥M ⧸ ZD) → Additive ↥ZD :=
    fun v w => Additive.ofMul (Quotient.liftOn₂ v.toMul w.toMul bZ bZ_wd)
  have bZq_mk : ∀ x y : ↥M, bZq (mkc x) (mkc y) = Additive.ofMul (bZ x y) :=
    fun x y => congrArg Additive.ofMul (Quotient.liftOn₂_mk bZ bZ_wd x y)
  have bZq_zero₁ : ∀ w : Additive (↥M ⧸ ZD), bZq 0 w = 0 := by
    intro w
    refine Quotient.inductionOn w (fun z => ?_)
    change bZq (mkc 1) (mkc z) = 0
    rw [bZq_mk 1 z, ofMul_eq_zero]
    apply Subtype.ext
    show ⁅z, 1⁆ = 1
    rw [commutatorElement_def]; group
  have bZq_zero₂ : ∀ w : Additive (↥M ⧸ ZD), bZq w 0 = 0 := by
    intro w
    refine Quotient.inductionOn w (fun z => ?_)
    change bZq (mkc z) (mkc 1) = 0
    rw [bZq_mk z 1, ofMul_eq_zero]
    apply Subtype.ext
    show ⁅1, z⁆ = 1
    rw [commutatorElement_def]; group
  have bZq_add₁ : ∀ v₁ v₂ w : Additive (↥M ⧸ ZD),
      bZq (v₁ + v₂) w = bZq v₁ w + bZq v₂ w := by
    intro v₁ v₂ w
    refine Quotient.inductionOn v₁ (fun x => ?_)
    refine Quotient.inductionOn v₂ (fun y => ?_)
    refine Quotient.inductionOn w (fun z => ?_)
    change bZq (mkc x + mkc y) (mkc z) = bZq (mkc x) (mkc z) + bZq (mkc y) (mkc z)
    rw [hsum x y, bZq_mk (x * y) z, bZq_mk x z, bZq_mk y z, ← ofMul_mul, ← bZ_mul₁ x y z]
  have bZq_add₂ : ∀ v w₁ w₂ : Additive (↥M ⧸ ZD),
      bZq v (w₁ + w₂) = bZq v w₁ + bZq v w₂ := by
    intro v w₁ w₂
    refine Quotient.inductionOn v (fun z => ?_)
    refine Quotient.inductionOn w₁ (fun x => ?_)
    refine Quotient.inductionOn w₂ (fun y => ?_)
    change bZq (mkc z) (mkc x + mkc y) = bZq (mkc z) (mkc x) + bZq (mkc z) (mkc y)
    rw [hsum x y, bZq_mk z (x * y), bZq_mk z x, bZq_mk z y, ← ofMul_mul, ← bZ_mul₂ z x y]
  have bZq_smul₁ : ∀ (c : ZMod 2) (v w : Additive (↥M ⧸ ZD)),
      bZq (c • v) w = c • bZq v w := by
    intro c v w
    let φ : Additive (↥M ⧸ ZD) →+ Additive ↥ZD :=
      { toFun := fun x => bZq x w
        map_zero' := bZq_zero₁ w
        map_add' := fun x y => bZq_add₁ x y w }
    exact ZMod.map_smul φ c v
  have bZq_smul₂ : ∀ (c : ZMod 2) (v w : Additive (↥M ⧸ ZD)),
      bZq v (c • w) = c • bZq v w := by
    intro c v w
    let φ : Additive (↥M ⧸ ZD) →+ Additive ↥ZD :=
      { toFun := fun x => bZq v x
        map_zero' := bZq_zero₂ v
        map_add' := fun x y => bZq_add₂ v x y }
    exact ZMod.map_smul φ c w
  let b : Additive (↥M ⧸ ZD) →ₗ[ZMod 2] Additive (↥M ⧸ ZD) →ₗ[ZMod 2] Additive ↥ZD :=
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
    have hc : ⁅y, x⁆ ∈ Subgroup.center ↥M := hZD_le_center (hcommZD x y)
    have h1 : ⁅y, x⁆ * x = x * ⁅y, x⁆ := (Subgroup.mem_center_iff.mp hc x).symm
    have h2 : ⁅y, x⁆ * y = y * ⁅y, x⁆ := (Subgroup.mem_center_iff.mp hc y).symm
    have hcyx : y * x = ⁅y, x⁆ * x * y := by rw [commutatorElement_def]; group
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (⁅y, x⁆ * x * y) * y := by rw [hcyx]
      _ = (x * x) * (y * y) * ⁅y, x⁆ := by
            calc x * (⁅y, x⁆ * x * y) * y = x * (x * (⁅y, x⁆ * y)) * y := by rw [h1]; group
              _ = x * (x * (y * ⁅y, x⁆)) * y := by rw [h2]
              _ = x * (x * y) * (⁅y, x⁆ * y) := by group
              _ = x * (x * y) * (y * ⁅y, x⁆) := by rw [h2]
              _ = (x * x) * (y * y) * ⁅y, x⁆ := by group
  -- Chevalley--Warning
  have hCW : Nat.card (↥M ⧸ ZD) ≤ Nat.card ↥ZD ^ 2 :=
    card_le_sq_of_quadratic_anisotropic (V := Additive (↥M ⧸ ZD))
      (W := Additive ↥ZD) Q Q_zero b hb Q_aniso
  -- Lagrange and arithmetic
  have hcardM : Nat.card ↥M = Nat.card (↥M ⧸ ZD) * Nat.card ↥ZD :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup ZD
  have hcardZD : Nat.card ↥ZD = Nat.card ↥(Work.Higman.omega1 P) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hM).toEquiv
  calc Nat.card ↥M = Nat.card (↥M ⧸ ZD) * Nat.card ↥ZD := hcardM
    _ ≤ Nat.card ↥ZD ^ 2 * Nat.card ↥ZD := Nat.mul_le_mul_right _ hCW
    _ = Nat.card ↥ZD ^ 3 := by ring
    _ = (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 := by rw [hcardZD]

end Work.Higman.H8
