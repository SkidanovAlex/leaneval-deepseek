import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.chevalley_warning
import Submission.Work.Higman.center_sq_eq_one
import Submission.Work.Higman.commutator_le_omega1

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

namespace Work.Higman

open LeanEval.GroupTheory.Defs
open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

/-! ## Orbit counting

In a Suzuki 2-group `P`, `q = |Ω₁(P)| = |Invol P| + 1`.  The cyclic group `⟨ξ⟩` acts on `P`;
every orbit of a non-identity element has cardinality divisible by `q - 1` (the stabiliser of
`x ≠ 1` fixes the involution `x ^ 2 ^ (k-1)`, where `2 ^ k = orderOf x`, and the stabiliser of an
involution has order `|⟨ξ⟩| / (q-1)`).  Hence `q - 1 ∣ |P| - 1`. -/

/-- The orbit of an involution under `⟨ξ⟩` is the whole set of involutions. -/
theorem orbit_invol (h : IsSuzuki2Grp P) {u : P} (hu : orderOf u = 2) :
    (MulAction.orbit (Subgroup.zpowers h.xi) u : Set P) = Invol P := by
  ext z
  rw [MulAction.mem_orbit_iff, mem_Invol]
  constructor
  · rintro ⟨g, rfl⟩
    show orderOf (g • u) = 2
    rw [show g • u = (g : MulAut P) u from rfl, MulEquiv.orderOf_eq, hu]
  · intro hz
    obtain ⟨k, hk⟩ := h.trans u z hu hz
    refine ⟨⟨h.xi ^ k, ?_⟩, hk⟩
    exact Subgroup.pow_mem (Subgroup.zpowers h.xi) (Subgroup.mem_zpowers h.xi) k

/-- Every orbit of `⟨ξ⟩` on `P \ {1}` has cardinality divisible by `|Ω₁(P)| - 1`. -/
theorem invol_ncard_dvd_orbit (h : IsSuzuki2Grp P) {x : P} (hx : x ≠ 1) :
    (Invol P).ncard ∣ Nat.card ↥(MulAction.orbit (Subgroup.zpowers h.xi) x) := by
  classical
  set K : Subgroup (MulAut P) := Subgroup.zpowers h.xi with hK
  obtain ⟨u, -, hu2, -, -⟩ := h.manyInvol
  -- orbit–stabiliser for the involution `u`
  have horb_u : Nat.card ↥(MulAction.orbit K u) = (Invol P).ncard := by
    rw [Nat.card_coe_set_eq, orbit_invol h hu2]
  have hos_u : (Invol P).ncard * Nat.card ↥(MulAction.stabilizer K u) = orderOf h.xi := by
    have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K u)
    rw [Nat.card_prod, hK, Nat.card_zpowers] at hh
    rwa [horb_u] at hh
  -- `x` has `2`-power order
  obtain ⟨s, hs⟩ := h.isPGroup.exists_orderOf_eq_pow x
  have hs1 : 1 ≤ s := by
    rcases Nat.eq_zero_or_pos s with h0 | hpos
    · subst h0
      simp only [pow_zero] at hs
      exact absurd (orderOf_eq_one_iff.mp hs) hx
    · exact hpos
  set w : P := x ^ 2 ^ (s - 1) with hw
  have hw1 : w ≠ 1 := by
    intro hcon
    have hdvd : 2 ^ s ∣ 2 ^ (s - 1) := by
      rw [← hs]
      exact orderOf_dvd_iff_pow_eq_one.mpr (by rw [← hw]; exact hcon)
    have hlt : 2 ^ (s - 1) < 2 ^ s := Nat.pow_lt_pow_right (by norm_num) (by omega)
    exact absurd (Nat.le_of_dvd (pow_pos (by norm_num) _) hdvd) (by omega)
  have hw2 : orderOf w = 2 := by
    have hpow : w ^ 2 = 1 := by
      have hexp : 2 ^ (s - 1) * 2 = 2 ^ s := by
        rw [← pow_succ]
        congr 1
        omega
      rw [hw, ← pow_mul, hexp, ← hs, pow_orderOf_eq_one]
    have hd : orderOf w ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hpow
    rcases (Nat.dvd_prime Nat.prime_two).mp hd with h1 | h2
    · exact absurd (orderOf_eq_one_iff.mp h1) hw1
    · exact h2
  -- the stabiliser of `x` is contained in that of `w`
  have hstab_le : MulAction.stabilizer K x ≤ MulAction.stabilizer K w := by
    intro γ hγ
    rw [MulAction.mem_stabilizer_iff] at hγ ⊢
    have h1 : (γ : MulAut P) x = x := hγ
    show (γ : MulAut P) w = w
    rw [hw, map_pow, h1]
  -- stabilisers of involutions have the same cardinality
  have hcard_stab_w : Nat.card ↥(MulAction.stabilizer K w) =
      Nat.card ↥(MulAction.stabilizer K u) := by
    have h1 := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K w)
    rw [Nat.card_prod, hK, Nat.card_zpowers] at h1
    have h2 : Nat.card ↥(MulAction.orbit K w) = (Invol P).ncard := by
      rw [Nat.card_coe_set_eq, orbit_invol h hw2]
    rw [h2] at h1
    have hpos : 0 < (Invol P).ncard :=
      (Set.ncard_pos (Set.toFinite (Invol P))).mpr ⟨u, mem_Invol.mpr hu2⟩
    exact Nat.eq_of_mul_eq_mul_left hpos (by rw [h1, hos_u])
  -- orbit–stabiliser for `x`
  have hos_x : Nat.card ↥(MulAction.orbit K x) * Nat.card ↥(MulAction.stabilizer K x) =
      orderOf h.xi := by
    have hh := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup K x)
    rw [Nat.card_prod, hK, Nat.card_zpowers] at hh
    exact hh
  -- `|Stab x|` divides `|Stab u|`
  have hdiv : Nat.card ↥(MulAction.stabilizer K x) ∣
      Nat.card ↥(MulAction.stabilizer K u) := by
    rw [← hcard_stab_w]
    exact Subgroup.card_dvd_of_le hstab_le
  obtain ⟨c, hc⟩ := hdiv
  have key : Nat.card ↥(MulAction.orbit K x) * Nat.card ↥(MulAction.stabilizer K x) =
      (Invol P).ncard * Nat.card ↥(MulAction.stabilizer K u) := by rw [hos_x, hos_u]
  refine ⟨c, ?_⟩
  have hpos : 0 < Nat.card ↥(MulAction.stabilizer K x) := Nat.card_pos
  have h2 : Nat.card ↥(MulAction.orbit K x) * Nat.card ↥(MulAction.stabilizer K x) =
      ((Invol P).ncard * c) * Nat.card ↥(MulAction.stabilizer K x) := by
    rw [key, hc]
    ring
  exact Nat.eq_of_mul_eq_mul_right hpos h2

/-- **Orbit counting.**  `|Ω₁(P)| - 1` divides `|P| - 1` for a Suzuki 2-group `P`. -/
theorem card_omega1_sub_one_dvd_card_sub_one (h : IsSuzuki2Grp P) :
    Nat.card (omega1 P) - 1 ∣ Nat.card P - 1 := by
  classical
  haveI : Fintype P := Fintype.ofFinite P
  set K : Subgroup (MulAut P) := Subgroup.zpowers h.xi with hK
  have hq : Nat.card (omega1 P) - 1 = (Invol P).ncard := by
    rw [h.card_omega1, Nat.add_sub_cancel]
  rw [hq]
  -- `P \ {1}` is the disjoint union of its orbits
  set s : Finset P := Finset.univ.filter (fun x : P => x ≠ 1) with hs
  have hcard_s : s.card = Nat.card P - 1 := by
    rw [hs]
    have h1 : (Finset.univ.filter (fun x : P => x ≠ 1)).card +
        (Finset.univ.filter (fun x : P => ¬ x ≠ 1)).card = (Finset.univ : Finset P).card :=
      Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset P))
        (p := fun x : P => x ≠ 1)
    have h2 : (Finset.univ.filter (fun x : P => ¬ x ≠ 1)).card = 1 := by
      have hset : (Finset.univ.filter (fun x : P => ¬ x ≠ 1)) = {1} := by
        ext x
        simp
      rw [hset]
      simp
    have h3 : (Finset.univ : Finset P).card = Nat.card P := by
      rw [Finset.card_univ, Nat.card_eq_fintype_card]
    omega
  have hpartition := Finset.card_eq_sum_card_image
    (f := fun x : P => MulAction.orbit K x) s
  have hdvd : (Invol P).ncard ∣ s.card := by
    rw [hpartition]
    apply Finset.dvd_sum
    intro b hb
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hb
    have hx1 : x ≠ 1 := by simpa [hs] using hx
    have h1not : (1 : P) ∉ MulAction.orbit K x := by
      intro hmem
      rw [MulAction.mem_orbit_iff] at hmem
      obtain ⟨γ, hγ⟩ := hmem
      have : x = 1 := by
        calc x = γ⁻¹ • (γ • x) := by rw [inv_smul_smul]
          _ = γ⁻¹ • (1 : P) := by rw [hγ]
          _ = 1 := by simp
      exact hx1 this
    have hfiber : (s.filter (fun a : P => MulAction.orbit K a = MulAction.orbit K x)).card =
        Nat.card ↥(MulAction.orbit K x) := by
      have hset : (s.filter (fun a : P => MulAction.orbit K a = MulAction.orbit K x)) =
          ((MulAction.orbit K x : Set P)).toFinset := by
        ext a
        simp only [Finset.mem_filter, Set.mem_toFinset, MulAction.orbit_eq_iff, hs,
          Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨-, ha⟩
          exact ha
        · intro ha
          exact ⟨fun hcon => h1not (hcon ▸ ha), ha⟩
      rw [hset, Set.toFinset_card]
      exact (Nat.card_eq_fintype_card).symm
    rw [hfiber]
    exact invol_ncard_dvd_orbit h hx1
  rw [← hcard_s]
  exact hdvd

/-! ## The Chevalley–Warning bound for `P / Z(P)`

Assume `Z(P) = Ω₁(P)` and `P' ≤ Ω₁(P)`: then `P` has class two and `P / Z(P)` is elementary
abelian, the squaring map is a well defined anisotropic quadratic form `P / Z(P) → Z(P)`, and
Chevalley–Warning gives `|P / Z(P)| ≤ |Z(P)|²`. -/

/-! ### Commutator algebra for groups of class two

These three lemmas are self-contained copies (under fresh names) of the class-two commutator
identities, so that this file does not need to import any module whose proofs are incomplete. -/

/-- `x * y * x⁻¹ = [x,y] * y`. -/
theorem czh_mul_mul_inv_eq_commutator_mul {G : Type*} [Group G] (x y : G) :
    x * y * x⁻¹ = ⁅x, y⁆ * y := by
  rw [commutatorElement_def]; group

/-- In a group of class two every commutator is central, and every element commutes with it. -/
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
theorem suzuki_commutator_mul_right {G : Type*} [Group G]
    (hZ : ⁅(⊤ : Subgroup G), ⊤⁆ ≤ Subgroup.center G) (x y z : G) :
    ⁅z, x * y⁆ = ⁅z, x⁆ * ⁅z, y⁆ := by
  have h1 : ⁅z, x * y⁆ = ⁅x * y, z⁆⁻¹ := by rw [← commutatorElement_inv]
  rw [h1, czh_commutator_mul_left hZ x y z, mul_inv_rev, commutatorElement_inv,
    commutatorElement_inv]
  exact (czh_commutator_central_comm hZ z y ⁅z, x⁆).symm

/-- A central element commutes out of a commutator on the left. -/
theorem suzuki_commutator_eq_one_of_mem_center_left {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (x : G) : ⁅z, x⁆ = 1 := by
  rw [commutatorElement_def, ← Subgroup.mem_center_iff.mp hz x]
  group

/-- A central element commutes out of a commutator on the right. -/
theorem suzuki_commutator_eq_one_of_mem_center_right {G : Type*} [Group G] {z : G}
    (hz : z ∈ Subgroup.center G) (x : G) : ⁅x, z⁆ = 1 := by
  rw [commutatorElement_def, Subgroup.mem_center_iff.mp hz x]
  group

/-- Class-`2` computation: if `[P,P] ≤ Ω₁(P)` then every square is central.  This does not
cardinality assumption: `x ^ 2 * y = [x,y] ^ 2 * y * x ^ 2 = y * x ^ 2` because `[x,y]` is a
central involution. -/
theorem suzuki_sq_mul_eq_mul_sq (h : IsSuzuki2Grp P)
    (hcomm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ omega1 P) (x y : P) :
    x ^ 2 * y = y * x ^ 2 := by
  have hmem : ⁅x, y⁆ ∈ omega1 P :=
    hcomm (Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y))
  have hc : ⁅x, y⁆ ∈ Subgroup.center P := h.omega1_le_center hmem
  have hcc : ⁅x, y⁆ * ⁅x, y⁆ = 1 := by
    have h1 := h.mem_omega1.mp hmem
    rwa [pow_two] at h1
  have hcx : x * ⁅x, y⁆ = ⁅x, y⁆ * x := (Subgroup.mem_center_iff.mp hc) x
  have h1 : x * y = ⁅x, y⁆ * y * x := by
    have h2 := czh_mul_mul_inv_eq_commutator_mul x y
    rw [← h2]; group
  calc x ^ 2 * y = x * (x * y) := by rw [pow_two]; group
    _ = x * (⁅x, y⁆ * y * x) := by rw [h1]
    _ = (x * ⁅x, y⁆) * y * x := by group
    _ = (⁅x, y⁆ * x) * y * x := by rw [hcx]
    _ = ⁅x, y⁆ * (x * y) * x := by group
    _ = ⁅x, y⁆ * (⁅x, y⁆ * y * x) * x := by rw [h1]
    _ = (⁅x, y⁆ * ⁅x, y⁆) * y * (x * x) := by group
    _ = y * (x * x) := by rw [hcc]; group
    _ = y * x ^ 2 := by rw [pow_two]

/-- If `[P,P] ≤ Ω₁(P)` in a Suzuki 2-group then every square is central. -/
theorem suzuki_sq_mem_center (h : IsSuzuki2Grp P)
    (hcomm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ omega1 P) (x : P) :
    x ^ 2 ∈ Subgroup.center P := by
  rw [Subgroup.mem_center_iff]
  intro y
  exact (suzuki_sq_mul_eq_mul_sq h hcomm x y).symm

theorem card_quotient_center_le_sq (h : IsSuzuki2Grp P)
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
    exact suzuki_commutator_mul_right hZ2 a b y
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
        suzuki_commutator_eq_one_of_mem_center_left hw (a₁ * z), mul_one,
        suzuki_commutator_mul_right hZ2 a₁ z b₁,
        suzuki_commutator_eq_one_of_mem_center_right hz b₁, mul_one]
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


/-! ## Assembly

With `Z(P) = Ω₁(P)`, `|Z(P)| = 2ⁿ = q`, `|P| = 2ᵐ` and `n ∣ m`.  The Chevalley–Warning bound
gives `|P / Z| = 2^(m-n) ≤ q²`, so `m ≤ 3n`; since `P` is non-abelian, `m > n`, and therefore
`m / n ∈ {2, 3}`. -/

theorem card_eq_sq_or_cube_aux (h : IsSuzuki2Grp P)
    (hZ : Subgroup.center P = omega1 P)
    (hsq : ∀ x : P, x ^ 2 ∈ Subgroup.center P)
    (hcommZ : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P) :
    Nat.card P = Nat.card ↥(Subgroup.center P) ^ 2 ∨
      Nat.card P = Nat.card ↥(Subgroup.center P) ^ 3 := by
  obtain ⟨m, hm⟩ := h.isPGroup.exists_card_eq
  obtain ⟨n, hn⟩ := h.exists_card_omega1_eq_two_pow
  have hn2 : 2 ≤ n := by
    have hq4 : 4 ≤ 2 ^ n := by rw [← hn]; exact h.omega1_card_ge_four
    by_contra hcon
    push_neg at hcon
    interval_cases n <;> norm_num at hq4
  have hnpos : 0 < n := by omega
  have hZcard : Nat.card ↥(Subgroup.center P) = 2 ^ n := by rw [hZ]; exact hn
  have hdiv : 2 ^ n - 1 ∣ 2 ^ m - 1 := by
    have h1 := card_omega1_sub_one_dvd_card_sub_one h
    rwa [hn, hm] at h1
  have hnm : n ∣ m := by
    have h1 : (2 : ℕ) ^ n ≡ 1 [MOD 2 ^ n - 1] :=
      (Nat.modEq_of_dvd' (n := 2 ^ n - 1) (a := 1) (b := 2 ^ n) Nat.one_le_two_pow
        (by simpa using dvd_refl (2 ^ n - 1))).symm
    have hcomp : (2 : ℕ) ^ m = (2 ^ n) ^ (m / n) * 2 ^ (m % n) := by
      have hdec : m = n * (m / n) + m % n := (Nat.div_add_mod m n).symm
      conv_lhs => rw [hdec]
      rw [pow_add, pow_mul]
    have h3 : (2 : ℕ) ^ m ≡ 2 ^ (m % n) [MOD 2 ^ n - 1] := by
      rw [hcomp]
      simpa using (h1.pow (m / n)).mul (Nat.ModEq.refl (2 ^ (m % n)))
    have h4 : (2 : ℕ) ^ m ≡ 1 [MOD 2 ^ n - 1] :=
      (Nat.modEq_of_dvd' (n := 2 ^ n - 1) (a := 1) (b := 2 ^ m) Nat.one_le_two_pow hdiv).symm
    have h5 : (2 : ℕ) ^ (m % n) ≡ 1 [MOD 2 ^ n - 1] := h3.symm.trans h4
    have h6 : 2 ^ n - 1 ∣ 2 ^ (m % n) - 1 :=
      (Nat.modEq_iff_dvd' (n := 2 ^ n - 1) (a := 1) (b := 2 ^ (m % n))
        Nat.one_le_two_pow).mp h5.symm
    have h7 : 2 ^ (m % n) - 1 < 2 ^ n - 1 := by
      have hlt : 2 ^ (m % n) < 2 ^ n :=
        Nat.pow_lt_pow_right (by norm_num) (Nat.mod_lt m hnpos)
      have hlt2 : 1 ≤ 2 ^ (m % n) := Nat.one_le_two_pow
      omega
    have h8 : 2 ^ (m % n) - 1 = 0 := Nat.eq_zero_of_dvd_of_lt h6 h7
    have h9 : 2 ^ (m % n) = 1 := by
      have h10 : 1 ≤ 2 ^ (m % n) := Nat.one_le_two_pow
      omega
    have h10 : m % n = 0 := by
      rcases Nat.pow_eq_one.mp h9 with hh | hh
      · norm_num at hh
      · exact hh
    exact Nat.dvd_of_mod_eq_zero h10
  have hne : Nat.card ↥(Subgroup.center P) ≠ Nat.card P := by
    intro hcon
    obtain ⟨x, y, hxy⟩ := h.noncomm
    have htop : Subgroup.center P = ⊤ := Subgroup.eq_top_of_card_eq _ hcon
    have hx : x ∈ Subgroup.center P := by rw [htop]; trivial
    exact hxy ((Subgroup.mem_center_iff.mp hx y).symm)
  have hnle : n ≤ m := by
    have h1 : Nat.card P = Nat.card (P ⧸ Subgroup.center P) * Nat.card ↥(Subgroup.center P) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    have hpos : 0 < Nat.card (P ⧸ Subgroup.center P) := Nat.card_pos
    rw [hm, hZcard] at h1
    have hle : 2 ^ n ≤ 2 ^ m := by
      rw [h1]
      exact Nat.le_mul_of_pos_left (2 ^ n) hpos
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hle
  have hnlt : n < m := lt_of_le_of_ne hnle (fun heq => hne (by rw [hZcard, hm, heq]))
  have hquot : Nat.card (P ⧸ Subgroup.center P) = 2 ^ (m - n) := by
    have h1 : Nat.card P = Nat.card (P ⧸ Subgroup.center P) * Nat.card ↥(Subgroup.center P) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup _
    rw [hm, hZcard] at h1
    have h2 : 2 ^ n * Nat.card (P ⧸ Subgroup.center P) = 2 ^ n * 2 ^ (m - n) := by
      calc 2 ^ n * Nat.card (P ⧸ Subgroup.center P)
          = Nat.card (P ⧸ Subgroup.center P) * 2 ^ n := Nat.mul_comm _ _
        _ = 2 ^ m := h1.symm
        _ = 2 ^ (n + (m - n)) := by rw [Nat.add_sub_cancel' hnle]
        _ = 2 ^ n * 2 ^ (m - n) := by rw [pow_add]
    exact Nat.mul_left_cancel (by positivity) h2
  have hbound : 2 ^ (m - n) ≤ 2 ^ (2 * n) := by
    have hqb := card_quotient_center_le_sq h hZ hsq hcommZ
    rw [hquot, hZcard] at hqb
    calc 2 ^ (m - n) ≤ (2 ^ n) ^ 2 := hqb
      _ = 2 ^ (n * 2) := (Nat.pow_mul 2 n 2).symm
      _ = 2 ^ (2 * n) := by rw [Nat.mul_comm]
  have hmn : m - n ≤ 2 * n := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hbound
  have hmlt3 : m ≤ 3 * n := by omega
  set j := m / n with hjdef
  have hmj : m = n * j := by
    rw [hjdef]
    exact (Nat.div_mul_cancel hnm).symm.trans (Nat.mul_comm _ _)
  have hj2 : 2 ≤ j := by
    have hlt : n * 1 < n * j := by rw [mul_one, ← hmj]; exact hnlt
    exact Nat.succ_le_of_lt ((Nat.mul_lt_mul_left hnpos).mp hlt)
  have hj3 : j ≤ 3 := by
    have hle : n * j ≤ n * 3 := by
      rw [← hmj, ← Nat.mul_comm 3 n]
      exact hmlt3
    exact Nat.le_of_mul_le_mul_left hle hnpos
  have hPcard : Nat.card P = Nat.card ↥(Subgroup.center P) ^ j := by
    rw [hm, hZcard, hmj, Nat.pow_mul]
  rcases (show j = 2 ∨ j = 3 by omega) with h2 | h3
  · left; rw [hPcard, h2]
  · right; rw [hPcard, h3]


/-- A Suzuki 2-group `P` with `q = |Z(P)|` has order `q ^ 2` or `q ^ 3`
(Higman 1963, Theorem 1: types `A` have order `q²`, types `B`, `C`, `D` order `q³`). -/
theorem card_eq_sq_or_cube {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) :
    Nat.card P = Nat.card ↥(Subgroup.center P) ^ 2 ∨
      Nat.card P = Nat.card ↥(Subgroup.center P) ^ 3 := by
  have hZle : Subgroup.center P ≤ omega1 P :=
    fun z hz => h.mem_omega1.mpr (by rw [pow_two]; exact center_sq_eq_one h z hz)
  have hZ : Subgroup.center P = omega1 P := le_antisymm hZle h.omega1_le_center
  have hcomm : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ omega1 P := commutator_le_omega1 h
  have hcommZ : ⁅(⊤ : Subgroup P), ⊤⁆ ≤ Subgroup.center P := hcomm.trans h.omega1_le_center
  exact card_eq_sq_or_cube_aux h hZ (fun x => suzuki_sq_mem_center h hcomm x) hcommZ

end Work.Higman
