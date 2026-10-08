import Mathlib
import Submission.Work.FeitSibley.GroupTheory.S_Q1
import Submission.Work.CharCore.IrrDegreeAux
import Submission.Work.CharCore.mem_Irr_iff_fdrep
import Submission.Work.CharCore.principalChar_mem_Irr
import Submission.Work.NormalComplement.rat_eq_int_of_isIntegral

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.FeitSibley.Coherence.congr_aux`

Support for `irr_congr_mod_card_Q` (Peterfalvi II, Appendice XII, step (7)): the congruence
`ψ(z) ≡ ψ(1) mod |Q|` for an irreducible character `ψ` of `G` which is constant on `Z^#`,
where `Z ⊴ H`, `Z ≤ Q₁`, `Z` centralises `Q` and `Q` is a T.I. Hall subgroup of `G`.
-/

noncomputable section

open Classical

namespace Work.FeitSibley.Coherence

variable {G : Type} [Group G] [Fintype G]

/-! ## 1. Elementary structural facts -/

/-- `Z ≤ Q₁` centralising `Q₁` centralises `Q = S · Q₁`. -/
theorem Z_le_centralizer_Q (h : Work.FeitSibley.FSData G) {Z : Subgroup G} (hZQ1 : Z ≤ h.Q1)
    (hZcent : ∀ z ∈ Z, ∀ y ∈ h.Q1, z * y = y * z) :
    Z ≤ Subgroup.centralizer (h.Q : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨a, ha, b, hb, rfl⟩ := h.mem_Q_decomp hy
  have h1 : z * a = a * z := (h.commute a ha z (hZQ1 hz)).symm
  have h2 : z * b = b * z := hZcent z hz b hb
  calc (a * b) * z = a * (b * z) := by rw [mul_assoc]
    _ = a * (z * b) := by rw [h2]
    _ = a * z * b := by rw [mul_assoc]
    _ = z * a * b := by rw [h1]
    _ = z * (a * b) := by rw [mul_assoc]

/-- If `Z` centralises `Q` then so does every `z ∈ Z`. -/
theorem Q_le_centralizer_singleton (h : Work.FeitSibley.FSData G) {Z : Subgroup G}
    (hZQ : ∀ z ∈ Z, ∀ y ∈ h.Q, z * y = y * z) {z : G} (hz : z ∈ Z) :
    h.Q ≤ Subgroup.centralizer ({z} : Set G) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  rw [Set.mem_singleton_iff] at hw
  rw [hw]
  exact hZQ z hz y hy

/-- **The T.I. property in centraliser form**: for `1 ≠ q ∈ Q`, the centraliser of `q` in `G`
is contained in `H`. -/
theorem centralizer_le_H_of_mem_Q_ne_one (h : Work.FeitSibley.FSData G) {q : G}
    (hq : q ∈ h.Q) (hq1 : q ≠ 1) : Subgroup.centralizer ({q} : Set G) ≤ h.H := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff] at hx
  have hxq : x * q * x⁻¹ = q := by
    have h1 : q * x = x * q := hx q rfl
    rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
  by_contra hxH
  have hbot : h.Q ⊓ Submission.Blueprint.conj x h.Q = ⊥ := h.Q_TI x hxH
  have hmem : q ∈ h.Q ⊓ Submission.Blueprint.conj x h.Q := by
    refine Subgroup.mem_inf.mpr ⟨hq, ?_⟩
    refine Subgroup.mem_map.mpr ⟨q, hq, ?_⟩
    show x * q * x⁻¹ = q
    exact hxq
  rw [hbot] at hmem
  exact hq1 (Subgroup.mem_bot.mp hmem)

/-- **The decomposition of a power of `q * d`**: `(q * d)^n = q' * d^n` with `q' ∈ Q`. -/
theorem pow_mem_Q_mul_pow_D (h : Work.FeitSibley.FSData G) {q d : G} (hq : q ∈ h.Q)
    (hd : d ∈ h.D) : ∀ n : ℕ, ∃ q' ∈ h.Q, (q * d) ^ n = q' * d ^ n := by
  intro n
  induction n with
  | zero => exact ⟨1, one_mem _, by simp⟩
  | succ n ih =>
      obtain ⟨q', hq', hq'n⟩ := ih
      have hdN : d ∈ Subgroup.normalizer (h.Q : Set G) := h.Q_normal_in_H (h.D_le_H hd)
      have hdn : d ^ n ∈ Subgroup.normalizer (h.Q : Set G) := pow_mem hdN n
      have hconj : d ^ n * q * (d ^ n)⁻¹ ∈ h.Q :=
        (Subgroup.mem_normalizer_iff.mp hdn q).mp hq
      refine ⟨q' * (d ^ n * q * (d ^ n)⁻¹), mul_mem hq' hconj, ?_⟩
      calc (q * d) ^ (n + 1) = (q * d) ^ n * (q * d) := by rw [pow_succ]
        _ = (q' * d ^ n) * (q * d) := by rw [hq'n]
        _ = q' * (d ^ n * q * (d ^ n)⁻¹) * (d ^ n * d) := by group
        _ = q' * (d ^ n * q * (d ^ n)⁻¹) * d ^ (n + 1) := by rw [pow_succ]

/-- The stabiliser of `z` for the conjugation action of `ConjAct G` is the centraliser of `z`
in `G`, transported along the canonical group isomorphism `ConjAct G ≃* G`. -/
noncomputable def conjActStabilizerEquivCentralizer (z : G) :
    MulAction.stabilizer (ConjAct G) z ≃ Subgroup.centralizer ({z} : Set G) where
  toFun x := ⟨ConjAct.ofConjAct (x : ConjAct G), by
    have hx : ConjAct.ofConjAct (x : ConjAct G) * z * (ConjAct.ofConjAct (x : ConjAct G))⁻¹
        = z := by
      have h := x.2
      rwa [MulAction.mem_stabilizer_iff, ConjAct.smul_def] at h
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    calc z * ConjAct.ofConjAct (x : ConjAct G)
        = (ConjAct.ofConjAct (x : ConjAct G) * z * (ConjAct.ofConjAct (x : ConjAct G))⁻¹) *
            ConjAct.ofConjAct (x : ConjAct G) := by rw [hx]
      _ = ConjAct.ofConjAct (x : ConjAct G) * z := by group⟩
  invFun y := ⟨ConjAct.toConjAct (y : G), by
    have hy' : z * (y : G) = (y : G) * z := y.2 z rfl
    rw [MulAction.mem_stabilizer_iff, ConjAct.smul_def, ConjAct.ofConjAct_toConjAct]
    rw [mul_inv_eq_iff_eq_mul]
    exact hy'.symm⟩
  left_inv x := by
    ext
    simp
  right_inv y := by
    ext
    simp

/-- **A `G`-class meeting `Z^#` meets `H` only in `Z`** (Peterfalvi, App. XII (7)). -/
theorem class_inter_H_subset_Z (h : Work.FeitSibley.FSData G) {Z : Subgroup G}
    (hZnorm : h.H ≤ Subgroup.normalizer (Z : Set G)) (hZQ1 : Z ≤ h.Q1)
    {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    ∀ w : G, IsConj w z → w ∈ h.H → w ∈ Z := by
  intro w hw hwH
  obtain ⟨g, hg⟩ := isConj_iff.mp hw
  -- `hg : g * w * g⁻¹ = z`
  have hord : orderOf w = orderOf z := by
    have h := MulEquiv.orderOf_eq (MulAut.conj g) w
    rw [MulAut.conj_apply, hg] at h
    exact h.symm
  have hwdvd : orderOf w ∣ Nat.card h.Q := by
    rw [hord]
    exact (Subgroup.orderOf_dvd_natCard h.Q1 (hZQ1 hz)).trans h.card_Q1_dvd_card_Q
  -- write `w = q * d`
  obtain ⟨q, hq, d, hd, hwd⟩ := h.mem_H_decomp hwH
  have hd1 : d = 1 := by
    by_contra hdne
    obtain ⟨q', hq', hq'n⟩ := pow_mem_Q_mul_pow_D h hq hd (orderOf w)
    have h1 : (q * d) ^ orderOf w = 1 := by rw [← hwd]; exact pow_orderOf_eq_one w
    rw [hq'n] at h1
    obtain ⟨-, hdk⟩ := h.mul_eq_of_decomp hq' (one_mem _) (pow_mem hd _) (one_mem _)
      (by rw [one_mul]; exact h1)
    have hdvd : orderOf d ∣ orderOf w := orderOf_dvd_iff_pow_eq_one.mpr hdk
    have hdvdD : orderOf d ∣ Nat.card h.D := Subgroup.orderOf_dvd_natCard h.D hd
    have hone : orderOf d = 1 := by
      have hg1 := Nat.dvd_gcd hdvdD (hdvd.trans hwdvd)
      rw [h.coprime_D_Q.gcd_eq_one] at hg1
      exact Nat.dvd_one.mp hg1
    exact hdne (orderOf_eq_one_iff.mp hone)
  have hwQ : w ∈ h.Q := by rw [hwd, hd1, mul_one]; exact hq
  obtain ⟨g', hg'⟩ := isConj_iff.mp hw
  -- `hg' : g' * w * g'⁻¹ = z`
  by_cases hgH : g' ∈ h.H
  · have hwg : w = g'⁻¹ * z * g' := by rw [← hg']; group
    rw [hwg]
    have hmem := (Subgroup.mem_normalizer_iff.mp (hZnorm (inv_mem hgH)) z).mp hz
    simpa using hmem
  · exfalso
    have hbot : h.Q ⊓ Submission.Blueprint.conj g' h.Q = ⊥ := h.Q_TI g' hgH
    have hzmem : z ∈ h.Q ⊓ Submission.Blueprint.conj g' h.Q := by
      refine Subgroup.mem_inf.mpr ⟨h.Q1_le_Q (hZQ1 hz), ?_⟩
      exact Subgroup.mem_map.mpr ⟨w, hwQ, hg'⟩
    rw [hbot] at hzmem
    exact hz1 (Subgroup.mem_bot.mp hzmem)

/-- **`C_G(z) = Q` for `z ∈ Z^#`** when `Z ≤ Q₁` centralises `Q`. -/
theorem centralizer_eq_Q_of_mem_Z (h : Work.FeitSibley.FSData G) {Z : Subgroup G}
    (hZQ1 : Z ≤ h.Q1) (hZQ : ∀ z ∈ Z, ∀ y ∈ h.Q, z * y = y * z)
    {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    Subgroup.centralizer ({z} : Set G) = h.Q := by
  refine le_antisymm ?_ (Q_le_centralizer_singleton h hZQ hz)
  intro x hx
  rw [Subgroup.mem_centralizer_iff] at hx
  have hxz : x * z * x⁻¹ = z := by
    have h1 : z * x = x * z := hx z rfl
    rw [← h1, mul_assoc, mul_inv_cancel, mul_one]
  have hxH : x ∈ h.H := by
    by_contra hxH'
    have hbot : h.Q ⊓ Submission.Blueprint.conj x h.Q = ⊥ := h.Q_TI x hxH'
    have hmem : z ∈ h.Q ⊓ Submission.Blueprint.conj x h.Q := by
      refine Subgroup.mem_inf.mpr ⟨h.Q1_le_Q (hZQ1 hz), ?_⟩
      refine Subgroup.mem_map.mpr ⟨z, h.Q1_le_Q (hZQ1 hz), ?_⟩
      show x * z * x⁻¹ = z
      exact hxz
    rw [hbot] at hmem
    exact hz1 (Subgroup.mem_bot.mp hmem)
  obtain ⟨q, hq, d, hd, hxd⟩ := h.mem_H_decomp hxH
  have hcomm : z * q = q * z := hZQ z hz q hq
  have hqinv : q⁻¹ * z * q = z := by
    have h1 : q * (q⁻¹ * z * q) = q * z := by rw [← hcomm]; group
    exact mul_left_cancel h1
  have hdz : d * z * d⁻¹ = z := by
    have h3 : q * (d * z * d⁻¹) * q⁻¹ = z := by
      have h := hxz
      rw [hxd] at h
      calc q * (d * z * d⁻¹) * q⁻¹ = (q * d) * z * (q * d)⁻¹ := by group
        _ = z := h
    have h4 : d * z * d⁻¹ = q⁻¹ * z * q := by
      calc d * z * d⁻¹ = q⁻¹ * (q * (d * z * d⁻¹) * q⁻¹) * q := by group
        _ = q⁻¹ * z * q := by rw [h3]
    rw [h4]
    simpa [mul_assoc] using hqinv
  by_cases hd1 : d = 1
  · rw [hxd, hd1, mul_one]; exact hq
  · exact absurd (h.D_fpf_Q1 d hd hd1 z (hZQ1 hz) hdz) hz1

/-- The conjugacy class of `z ∈ Z^#` has `|G : Q|` elements. -/
theorem card_class_eq_index (h : Work.FeitSibley.FSData G) {Z : Subgroup G}
    (hZQ1 : Z ≤ h.Q1) (hZQ : ∀ z ∈ Z, ∀ y ∈ h.Q, z * y = y * z)
    {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1) :
    Fintype.card (ConjClasses.mk z).carrier = h.Q.index := by
  have hcz := centralizer_eq_Q_of_mem_Z h hZQ1 hZQ hz hz1
  have hcardN : Nat.card (ConjClasses.mk z).carrier = Nat.card G / Nat.card ↥h.Q := by
    rw [Nat.card_eq_fintype_card, ConjClasses.card_carrier z,
      Fintype.card_congr (conjActStabilizerEquivCentralizer z), hcz,
      ← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  have hdvd : Nat.card ↥h.Q ∣ Nat.card G := Subgroup.card_subgroup_dvd_card h.Q
  have hmul : Nat.card (ConjClasses.mk z).carrier * Nat.card ↥h.Q = Nat.card G := by
    rw [hcardN]
    exact Nat.div_mul_cancel hdvd
  have hQpos : 0 < Nat.card ↥h.Q := Nat.card_pos
  have h2 : Nat.card ↥h.Q * h.Q.index =
      Nat.card ↥h.Q * Nat.card (ConjClasses.mk z).carrier := by
    rw [Subgroup.card_mul_index, ← hmul, mul_comm]
  have h3 : h.Q.index = Nat.card (ConjClasses.mk z).carrier :=
    Nat.mul_left_cancel hQpos h2
  rw [h3, Nat.card_eq_fintype_card]

/-! ## 2. The trace identity for class sums -/

open scoped MonoidAlgebra

/-- **The central-character/multiplicativity identity**: for a simple submodule `N` of the regular
module and two conjugacy classes `C`, `C'`, the product of the associated central-character
values times the dimension is the sum of the character over all products `x * y` with `x ∈ C`,
`y ∈ C'`. -/
theorem centralChar_mul_eq_pair_sum {G : Type} [Group G] [Fintype G]
    (N : Submodule (Work.CharCore.groupAlgebra G) (Work.CharCore.groupAlgebra G))
    (hN : IsSimpleModule (Work.CharCore.groupAlgebra G) N)
    (C C' : ConjClasses G) :
    (Work.CharCore.centralChar N hN ⟨Work.CharCore.conjClassSum C, Work.CharCore.classSum_mem_center C⟩ *
      Work.CharCore.centralChar N hN
        ⟨Work.CharCore.conjClassSum C', Work.CharCore.classSum_mem_center C'⟩) *
        (Module.finrank ℂ N : ℂ)
      = ∑ p : C.carrier × C'.carrier, (Work.CharCore.submoduleRep N).character (p.1.1 * p.2.1) := by
  have hAA : (Work.CharCore.submoduleRep N).asAlgebraHom = Algebra.lsmul ℂ ℂ N := by
    ext a n
    simp [Representation.asAlgebraHom, Work.CharCore.submoduleRep, Representation.ofModule',
      Algebra.lsmul_apply]
  have hchar : ∀ g : G, (Work.CharCore.submoduleRep N).character g =
      LinearMap.trace ℂ N (Algebra.lsmul ℂ ℂ N (MonoidAlgebra.single g (1 : ℂ))) := by
    intro g
    rw [Representation.character, ← hAA, Representation.asAlgebraHom_single]
    simp
  have hls : ∀ D : ConjClasses G, Algebra.lsmul ℂ ℂ N (Work.CharCore.conjClassSum D) =
      (Work.CharCore.centralChar N hN
        ⟨Work.CharCore.conjClassSum D, Work.CharCore.classSum_mem_center D⟩) •
        (1 : N →ₗ[ℂ] N) := by
    intro D
    refine LinearMap.ext fun n => ?_
    rw [Algebra.lsmul_apply, LinearMap.smul_apply, Module.End.one_apply]
    exact Work.CharCore.centralChar_spec N hN ⟨_, _⟩ n
  have hsingle : Work.CharCore.conjClassSum C * Work.CharCore.conjClassSum C' =
      ∑ p : C.carrier × C'.carrier, MonoidAlgebra.single (p.1.1 * p.2.1) (1 : ℂ) := by
    rw [Work.CharCore.classSum_eq, Work.CharCore.classSum_eq, Finset.sum_mul_sum,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    rw [MonoidAlgebra.single_mul_single, mul_one]
  rw [Finset.sum_congr rfl (fun p _ => hchar (p.1.1 * p.2.1))]
  rw [← map_sum]
  rw [← map_sum]
  rw [← hsingle]
  rw [map_mul, hls C, hls C', smul_mul_smul, mul_one, map_smul, LinearMap.trace_one,
    smul_eq_mul]

/-! ## 3. Averaging over a free action -/

/-- **Averaging a `Q`-invariant function of algebraic integers over a free action**: if the
action of a finite group `Q` on `X` is free on the support of `f`, then
`|Q|⁻¹ ∑_x f x` is an algebraic integer. -/
theorem isIntegral_sum_div_card_of_free {Q : Type} [Group Q] [Fintype Q]
    {X : Type} [Fintype X] [MulAction Q X] (f : X → ℂ)
    (hinv : ∀ (q : Q) (x : X), f (q • x) = f x) (hint : ∀ x : X, IsIntegral ℤ (f x))
    (hfree : ∀ x : X, f x ≠ 0 → MulAction.stabilizer Q x = ⊥) :
    IsIntegral ℤ ((∑ x : X, f x) / (Fintype.card Q : ℂ)) := by
  classical
  have hsub : ∑ x : X, f x = ∑ x : {x : X // f x ≠ 0}, f x.1 := by
    rw [← Finset.sum_subtype (Finset.univ.filter (fun x : X => f x ≠ 0)) (by simp) f]
    refine (Finset.sum_subset (Finset.subset_univ _) (fun x _ hx => ?_)).symm
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    exact not_not.mp hx
  rw [hsub]
  letI inst : MulAction Q {x : X // f x ≠ 0} :=
    { smul := fun q x => ⟨q • x.1, by rw [hinv q x.1]; exact x.2⟩
      one_smul := fun x => Subtype.ext (one_smul Q x.1)
      mul_smul := fun a b x => Subtype.ext (mul_smul a b x.1) }
  have hQpos : 0 < Fintype.card Q := Fintype.card_pos
  have hQne : (Fintype.card Q : ℂ) ≠ 0 := by exact_mod_cast hQpos.ne'
  let R : Setoid {x : X // f x ≠ 0} := MulAction.orbitRel Q {x : X // f x ≠ 0}
  let Φ : Quotient R × Q → {x : X // f x ≠ 0} := fun p => p.2 • Quotient.out p.1
  have hΦ_orbit : ∀ (ω : Quotient R) (q : Q), Quotient.mk R (Φ (ω, q)) = ω := by
    intro ω q
    have h1 : Quotient.mk R (Φ (ω, q)) = Quotient.mk R (Quotient.out ω) := by
      refine Quotient.sound ?_
      show MulAction.orbitRel Q {x : X // f x ≠ 0} (Φ (ω, q)) (Quotient.out ω)
      rw [MulAction.orbitRel_apply]
      exact MulAction.mem_orbit_iff.mpr ⟨q, rfl⟩
    rw [h1, Quotient.out_eq]
  have coe_smul : ∀ (q : Q) (y : {x : X // f x ≠ 0}),
      (q • y).1 = q • y.1 := by
    intro q y
    show (inst.toSMul.smul q y).1 = q • y.1
    rfl
  have hinj : Function.Injective Φ := by
    rintro ⟨ω, q⟩ ⟨ω', q'⟩ heq
    have h1 : Quotient.mk R (Φ (ω, q)) = Quotient.mk R (Φ (ω', q')) :=
      congrArg (Quotient.mk R) heq
    rw [hΦ_orbit, hΦ_orbit] at h1
    subst h1
    have heq_sub : q • (Quotient.out ω) = q' • (Quotient.out ω) := heq
    have h2 : (q'⁻¹ * q) • (Quotient.out ω) = (Quotient.out ω) := by
      rw [mul_smul, heq_sub, ← mul_smul, inv_mul_cancel, one_smul]
    have h2X : (q'⁻¹ * q) • (Quotient.out ω).1 = (Quotient.out ω).1 := by
      rw [← coe_smul (q'⁻¹ * q) (Quotient.out ω), h2]
    have hstab : q'⁻¹ * q ∈ MulAction.stabilizer Q ((Quotient.out ω).1) := by
      rw [MulAction.mem_stabilizer_iff]
      exact h2X
    have hx : f (Quotient.out ω).1 ≠ 0 := (Quotient.out ω).2
    rw [hfree _ hx] at hstab
    exact Prod.ext rfl ((inv_mul_eq_one.mp (Subgroup.mem_bot.mp hstab)).symm)
  have hsurj : Function.Surjective Φ := by
    intro x
    obtain ⟨q, hq⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp
      (Quotient.exact ((Quotient.out_eq (Quotient.mk R x)).symm)))
    exact ⟨(Quotient.mk R x, q), hq⟩
  let rep : Quotient R → X := fun ω => (Quotient.out ω).1
  have hkey : ∑ y : {x : X // f x ≠ 0}, f y.1 =
      (Fintype.card Q : ℂ) * ∑ ω : Quotient R, f (rep ω) := by
    rw [(Fintype.sum_bijective Φ ⟨hinj, hsurj⟩ (fun p : Quotient R × Q => f (Φ p).1)
        (fun y : {x : X // f x ≠ 0} => f y.1) (fun p => rfl)).symm]
    rw [Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ω _ => ?_
    have h1 : ∀ q : Q, f ((Φ (ω, q)).1) = f (rep ω) := by
      intro q
      have h2 : (Φ (ω, q)).1 = q • rep ω := by
        show (inst.toSMul.smul q (Quotient.out ω)).1 = q • rep ω
        exact coe_smul q (Quotient.out ω)
      rw [h2, hinv q (rep ω)]
    rw [Finset.sum_congr rfl (fun q _ => h1 q), Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
  rw [hkey, mul_comm (Fintype.card Q : ℂ), mul_div_cancel_right₀ _ hQne]
  exact IsIntegral.sum _ (fun ω _ => hint (rep ω))

/-! ## 4. The pairs with `xy ∉ Z` -/

/-- Sums of `if P a then f a else 0` are sums over the subtype `{a // P a}`. -/
theorem sum_ite_eq_sum_subtype {A : Type*} [Fintype A] (P : A → Prop) [DecidablePred P]
    (f : A → ℂ) : (∑ a : A, (if P a then f a else 0)) = ∑ a : {a : A // P a}, f a := by
  rw [← Finset.sum_subtype (Finset.univ.filter P) (by simp) f, Finset.sum_filter]

/-- **The contribution of the pairs `(x, y)` with `x * y ∉ Z`**, divided by `|Q|`, is an algebraic
integer.  This is the "free action" step of Peterfalvi's proof of App. XII (7): `Q` acts by
conjugation on such pairs, freely. -/
theorem isIntegral_sum_pairs_out_Z (h : Work.FeitSibley.FSData G) {Z : Subgroup G}
    (hZnorm : h.H ≤ Subgroup.normalizer (Z : Set G)) (hZQ1 : Z ≤ h.Q1)
    {z z' : G} (hz : z ∈ Z) (hz1 : z ≠ 1) (hz' : z' ∈ Z) (hz'1 : z' ≠ 1)
    (ψ : G → ℂ) (hψcl : ∀ g x : G, ψ (g * x * g⁻¹) = ψ x)
    (hψint : ∀ x : G, IsIntegral ℤ (ψ x)) :
    IsIntegral ℤ ((∑ p : (ConjClasses.mk z).carrier × (ConjClasses.mk z').carrier,
        (if (p.1.1 * p.2.1 : G) ∈ Z then (0 : ℂ) else ψ (p.1.1 * p.2.1)))
      / (Nat.card h.Q : ℂ)) := by
  classical
  have hcarrier1 : ∀ x : G, x ∈ (ConjClasses.mk z).carrier ↔ IsConj x z := by
    intro x
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
  have hcarrier2 : ∀ x : G, x ∈ (ConjClasses.mk z').carrier ↔ IsConj x z' := by
    intro x
    rw [ConjClasses.mem_carrier_iff_mk_eq, ConjClasses.mk_eq_mk_iff_isConj]
  letI inst : MulAction h.Q ((ConjClasses.mk z).carrier × (ConjClasses.mk z').carrier) :=
    { smul := fun q p =>
        (⟨(q : G) * (p.1 : G) * (q : G)⁻¹, by
            rw [ConjClasses.mem_carrier_iff_mk_eq, Work.CharCore.ConjClasses.mk_mul_conj_eq,
              ← ConjClasses.mem_carrier_iff_mk_eq]
            exact p.1.2⟩,
          ⟨(q : G) * (p.2 : G) * (q : G)⁻¹, by
            rw [ConjClasses.mem_carrier_iff_mk_eq, Work.CharCore.ConjClasses.mk_mul_conj_eq,
              ← ConjClasses.mem_carrier_iff_mk_eq]
            exact p.2.2⟩)
      one_smul := fun p => by
        have h1 : ((1 : h.Q) : G) * (p.1.1 : G) * ((1 : h.Q) : G)⁻¹ = p.1.1 := by simp
        have h2 : ((1 : h.Q) : G) * (p.2.1 : G) * ((1 : h.Q) : G)⁻¹ = p.2.1 := by simp
        exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
      mul_smul := fun a b p => by
        have h1 : ((a * b : h.Q) : G) * (p.1.1 : G) * ((a * b : h.Q) : G)⁻¹
            = (a : G) * ((b : G) * (p.1.1 : G) * (b : G)⁻¹) * (a : G)⁻¹ := by
          simp only [Subgroup.coe_mul]; group
        have h2 : ((a * b : h.Q) : G) * (p.2.1 : G) * ((a * b : h.Q) : G)⁻¹
            = (a : G) * ((b : G) * (p.2.1 : G) * (b : G)⁻¹) * (a : G)⁻¹ := by
          simp only [Subgroup.coe_mul]; group
        exact Prod.ext (Subtype.ext h1) (Subtype.ext h2) }
  have coe_fst : ∀ (q : h.Q) (p : (ConjClasses.mk z).carrier × (ConjClasses.mk z').carrier),
      ((q • p).1 : G) = (q : G) * (p.1 : G) * (q : G)⁻¹ := by
    intro q p
    show (inst.toSMul.smul q p).1.1 = _
    rfl
  have coe_snd : ∀ (q : h.Q) (p : (ConjClasses.mk z).carrier × (ConjClasses.mk z').carrier),
      ((q • p).2 : G) = (q : G) * (p.2 : G) * (q : G)⁻¹ := by
    intro q p
    show (inst.toSMul.smul q p).2.1 = _
    rfl
  have hZconj : ∀ (q : h.Q) (x : G), (q : G) * x * (q : G)⁻¹ ∈ Z ↔ x ∈ Z := by
    intro q x
    have hq : (q : G) ∈ Subgroup.normalizer (Z : Set G) := hZnorm (h.Q_le_H q.2)
    exact (Subgroup.mem_normalizer_iff.mp hq x).symm
  let F : (ConjClasses.mk z).carrier × (ConjClasses.mk z').carrier → ℂ :=
    fun p => if (p.1.1 * p.2.1 : G) ∈ Z then (0 : ℂ) else ψ (p.1.1 * p.2.1)
  have hinv : ∀ (q : h.Q) (p : (ConjClasses.mk z).carrier × (ConjClasses.mk z').carrier),
      F (q • p) = F p := by
    intro q p
    show (if (((q • p).1 : G) * ((q • p).2 : G)) ∈ Z then (0 : ℂ)
        else ψ (((q • p).1 : G) * ((q • p).2 : G))) = _
    have hxy : ((q • p).1 : G) * ((q • p).2 : G)
        = (q : G) * (p.1.1 * p.2.1 : G) * (q : G)⁻¹ := by
      rw [coe_fst, coe_snd]; group
    rw [hxy, hZconj q (p.1.1 * p.2.1 : G), hψcl (q : G) (p.1.1 * p.2.1 : G)]
  have hint : ∀ p : (ConjClasses.mk z).carrier × (ConjClasses.mk z').carrier,
      IsIntegral ℤ (F p) := by
    intro p
    show IsIntegral ℤ (if (p.1.1 * p.2.1 : G) ∈ Z then (0 : ℂ) else ψ (p.1.1 * p.2.1))
    split_ifs with hp
    · exact isIntegral_zero
    · exact hψint _
  have hfree : ∀ p : (ConjClasses.mk z).carrier × (ConjClasses.mk z').carrier,
      F p ≠ 0 → MulAction.stabilizer h.Q p = ⊥ := by
    intro p hp
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    rw [MulAction.mem_stabilizer_iff] at hq
    by_contra hq1
    have hqx : (q : G) * (p.1.1 : G) * (q : G)⁻¹ = p.1.1 := by
      have h1 := congrArg (fun r : (ConjClasses.mk z).carrier × (ConjClasses.mk z').carrier =>
        ((r.1 : (ConjClasses.mk z).carrier) : G)) hq
      rw [coe_fst] at h1
      exact h1
    have hqy : (q : G) * (p.2.1 : G) * (q : G)⁻¹ = p.2.1 := by
      have h1 := congrArg (fun r : (ConjClasses.mk z).carrier × (ConjClasses.mk z').carrier =>
        ((r.2 : (ConjClasses.mk z').carrier) : G)) hq
      rw [coe_snd] at h1
      exact h1
    have hqne : (q : G) ≠ 1 := fun hc => hq1 (Subtype.ext hc)
    have hxH : (p.1.1 : G) ∈ h.H := by
      refine centralizer_le_H_of_mem_Q_ne_one h q.2 hqne ?_
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      have h2 := congrArg (fun t : G => t * (q : G)) hqx
      simpa [mul_assoc] using h2
    have hyH : (p.2.1 : G) ∈ h.H := by
      refine centralizer_le_H_of_mem_Q_ne_one h q.2 hqne ?_
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      have h2 := congrArg (fun t : G => t * (q : G)) hqy
      simpa [mul_assoc] using h2
    have hxZ : (p.1.1 : G) ∈ Z :=
      class_inter_H_subset_Z h hZnorm hZQ1 hz hz1 _ ((hcarrier1 _).mp p.1.2) hxH
    have hyZ : (p.2.1 : G) ∈ Z :=
      class_inter_H_subset_Z h hZnorm hZQ1 hz' hz'1 _ ((hcarrier2 _).mp p.2.2) hyH
    refine hp ?_
    show (if (p.1.1 * p.2.1 : G) ∈ Z then (0 : ℂ) else ψ (p.1.1 * p.2.1)) = 0
    rw [if_pos (mul_mem hxZ hyZ)]
  have key := isIntegral_sum_div_card_of_free F hinv hint hfree
  rw [Nat.card_eq_fintype_card]
  exact key

/-! ## 5. The pair counts and the splitting of the pair sum -/

/-- The number of pairs `(x, y) ∈ C × C'` with `x * y = 1`. -/
noncomputable def Vcount {G : Type} [Group G] [Fintype G] (C C' : ConjClasses G) : ℕ :=
  (Finset.univ.filter (fun p : C.carrier × C'.carrier => (p.1.1 * p.2.1 : G) = 1)).card

/-- The number of pairs `(x, y) ∈ C × C'` with `1 ≠ x * y ∈ Z`. -/
noncomputable def Ucount {G : Type} [Group G] [Fintype G] (Z : Subgroup G)
    (C C' : ConjClasses G) : ℕ :=
  (Finset.univ.filter (fun p : C.carrier × C'.carrier =>
    (p.1.1 * p.2.1 : G) ∈ Z ∧ (p.1.1 * p.2.1 : G) ≠ 1)).card

theorem Ucount_def {G : Type} [Group G] [Fintype G] (Z : Subgroup G) (C C' : ConjClasses G) :
    Ucount Z C C' = (Finset.univ.filter (fun p : C.carrier × C'.carrier =>
      (p.1.1 * p.2.1 : G) ∈ Z ∧ (p.1.1 * p.2.1 : G) ≠ 1)).card := rfl

theorem Vcount_def {G : Type} [Group G] [Fintype G] (C C' : ConjClasses G) :
    Vcount C C' = (Finset.univ.filter (fun p : C.carrier × C'.carrier =>
      (p.1.1 * p.2.1 : G) = 1)).card := rfl

variable {G : Type} [Group G] [Fintype G]

/-- **Splitting the pair sum**:  the sum of `ψ` over products `x * y`, `x ∈ C`, `y ∈ C'`, splits
into the terms with `x * y ∈ Z` (whose values are `ψ 1` when `x * y = 1` and `ψ z` when
`1 ≠ x * y ∈ Z`) and the terms with `x * y ∉ Z`. -/
theorem sum_pair_split (h : Work.FeitSibley.FSData G) {Z : Subgroup G} {z z' : G}
    (hz : z ∈ Z) (hz1 : z ≠ 1) (hz' : z' ∈ Z) (hz'1 : z' ≠ 1) {ψ : G → ℂ}
    (hconst : ∀ z'' ∈ Z, z'' ≠ 1 → ψ z'' = ψ z) :
    (∑ p : (ConjClasses.mk z).carrier × (ConjClasses.mk z').carrier, ψ (p.1.1 * p.2.1))
      = (ψ 1) * (Vcount (ConjClasses.mk z) (ConjClasses.mk z') : ℂ)
        + (ψ z) * (Ucount Z (ConjClasses.mk z) (ConjClasses.mk z') : ℂ)
        + (∑ p : (ConjClasses.mk z).carrier × (ConjClasses.mk z').carrier,
            if (p.1.1 * p.2.1 : G) ∈ Z then (0 : ℂ) else ψ (p.1.1 * p.2.1)) := by
  classical
  set C : ConjClasses G := ConjClasses.mk z with hC
  set C' : ConjClasses G := ConjClasses.mk z' with hC'
  have hsplit : ∀ p : C.carrier × C'.carrier,
      ψ (p.1.1 * p.2.1)
        = (if (p.1.1 * p.2.1 : G) ∈ Z then ψ (p.1.1 * p.2.1) else 0)
          + (if (p.1.1 * p.2.1 : G) ∈ Z then 0 else ψ (p.1.1 * p.2.1)) := by
    intro p
    by_cases hp : (p.1.1 * p.2.1 : G) ∈ Z <;> simp [hp]
  have hIn : (∑ p : C.carrier × C'.carrier, (if (p.1.1 * p.2.1 : G) ∈ Z then ψ (p.1.1 * p.2.1) else 0))
      = (ψ 1) * (Vcount C C' : ℂ) + (ψ z) * (Ucount Z C C' : ℂ) := by
    rw [← Finset.sum_filter]
    rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter (fun p : C.carrier × C'.carrier => (p.1.1 * p.2.1 : G) ∈ Z))
      (fun p : C.carrier × C'.carrier => (p.1.1 * p.2.1 : G) = 1)]
    congr 1
    · -- the pairs with `x * y = 1`
      rw [Finset.sum_congr rfl (fun p hp => ?_)]
      · rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        congr 1
        rw [Vcount_def, Finset.filter_filter]
        congr 1
        congr 1
        ext p
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨-, hQ⟩; exact hQ
        · intro hQ; exact ⟨hQ ▸ Subgroup.one_mem Z, hQ⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        rw [hp.2]
    · -- the pairs with `1 ≠ x * y ∈ Z`
      rw [Finset.sum_congr rfl (fun p hp => ?_)]
      · rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
        congr 1
        rw [Ucount_def, Finset.filter_filter]
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
        exact hconst _ hp.1 hp.2
  rw [Finset.sum_congr rfl (fun p _ => hsplit p), Finset.sum_add_distrib, hIn]

/-- `Vcount C C = 0` when no element of `C` is conjugate to its inverse. -/
theorem Vcount_self_eq_zero {z : G} (hnotconj : ∀ g : G, g * z * g⁻¹ ≠ z⁻¹) :
    Vcount (ConjClasses.mk z) (ConjClasses.mk z) = 0 := by
  classical
  rw [Vcount_def, Finset.card_eq_zero]
  refine Finset.eq_empty_of_forall_notMem fun p hp => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
  have hx : IsConj (p.1.1 : G) z :=
    ConjClasses.mk_eq_mk_iff_isConj.mp (ConjClasses.mem_carrier_iff_mk_eq.mp p.1.2)
  have hy : IsConj (p.2.1 : G) z :=
    ConjClasses.mk_eq_mk_iff_isConj.mp (ConjClasses.mem_carrier_iff_mk_eq.mp p.2.2)
  obtain ⟨a, ha⟩ := isConj_iff.mp hx
  obtain ⟨b, hb⟩ := isConj_iff.mp hy
  set x : G := (p.1.1 : G) with hxdef
  set y : G := (p.2.1 : G) with hydef
  have ha' : a * x * a⁻¹ = z := ha
  have hb' : b * y * b⁻¹ = z := hb
  have hxy : y = x⁻¹ := by
    rw [hxdef, hydef]
    exact eq_inv_of_mul_eq_one_right hp
  rw [hxy] at hb'
  refine hnotconj (b * a⁻¹) ?_
  have hxa : a⁻¹ * z * a = x := by
    rw [← ha']
    group
  calc (b * a⁻¹) * z * (b * a⁻¹)⁻¹ = b * (a⁻¹ * z * a) * b⁻¹ := by group
    _ = b * x * b⁻¹ := by rw [hxa]
    _ = z⁻¹ := by
      rw [← hb']
      group

/-- Inverse preserves conjugacy classes. -/
theorem mk_inv_eq {x y : G} (h : ConjClasses.mk x = ConjClasses.mk y) :
    ConjClasses.mk x⁻¹ = ConjClasses.mk y⁻¹ := by
  obtain ⟨a, ha⟩ := isConj_iff.mp (ConjClasses.mk_eq_mk_iff_isConj.mp h)
  rw [ConjClasses.mk_eq_mk_iff_isConj]
  refine isConj_iff.mpr ⟨a, ?_⟩
  rw [← ha]
  group

/-- The number of pairs `(x, y) ∈ C × C⁻¹` with `x * y = 1` is the size of `C`. -/
theorem Vcount_mk_inv {z : G} :
    Vcount (ConjClasses.mk z) (ConjClasses.mk z⁻¹) = Fintype.card (ConjClasses.mk z).carrier := by
  classical
  rw [Vcount_def]
  refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
  · intro p hp
    simp
  · intro p hp q hq heq
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    have hp' : (p.2.1 : G) = (p.1.1 : G)⁻¹ := eq_inv_of_mul_eq_one_right hp
    have hq' : (q.2.1 : G) = (q.1.1 : G)⁻¹ := eq_inv_of_mul_eq_one_right hq
    have heq' : (p.1.1 : G) = (q.1.1 : G) := congrArg Subtype.val heq
    refine Prod.ext heq (Subtype.ext ?_)
    rw [hp', hq', heq']
  · intro x hx
    refine ⟨(x, ⟨x⁻¹, ?_⟩), ?_, rfl⟩
    · rw [ConjClasses.mem_carrier_iff_mk_eq]
      exact mk_inv_eq (ConjClasses.mem_carrier_iff_mk_eq.mp x.2)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact mul_inv_cancel x.1

/-! ## 6. The master congruence -/

/-- The classes of `z` and of `z⁻¹` have the same size (via the bijection `x ↦ x⁻¹`). -/
noncomputable def classInvEquiv (z : G) :
    (ConjClasses.mk z⁻¹).carrier ≃ (ConjClasses.mk z).carrier where
  toFun x := ⟨x.1⁻¹, by
    rw [ConjClasses.mem_carrier_iff_mk_eq]
    exact (mk_inv_eq (ConjClasses.mem_carrier_iff_mk_eq.mp x.2)).trans (by rw [inv_inv])⟩
  invFun y := ⟨y.1⁻¹, by
    rw [ConjClasses.mem_carrier_iff_mk_eq]
    exact mk_inv_eq (ConjClasses.mem_carrier_iff_mk_eq.mp y.2)⟩
  left_inv x := Subtype.ext (inv_inv x.1)
  right_inv y := Subtype.ext (inv_inv y.1)

theorem card_class_inv_eq_card {z : G} :
    Fintype.card (ConjClasses.mk z⁻¹).carrier = Fintype.card (ConjClasses.mk z).carrier :=
  Fintype.card_congr (classInvEquiv z)

/-- The value of `ψ` on a representative of a class given by `ConjClasses.mk w`. -/
theorem rep_value_of_class_eq {ψ : G → ℂ} (hψclass : ∀ g x : G, ψ (g * x * g⁻¹) = ψ x)
    {C : ConjClasses G} {w : G} (hC : C = ConjClasses.mk w) :
    ψ (Work.CharCore.rep C) = ψ w := by
  subst hC
  have hconj : IsConj (Work.CharCore.rep (ConjClasses.mk w)) w :=
    ConjClasses.mk_eq_mk_iff_isConj.mp
      ((Work.CharCore.mk_rep (ConjClasses.mk w)).trans rfl)
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  calc ψ (Work.CharCore.rep (ConjClasses.mk w)) = ψ (g⁻¹ * w * g) := by
        have harg : Work.CharCore.rep (ConjClasses.mk w) = g⁻¹ * w * g := by
          have h2 : g⁻¹ * (g * Work.CharCore.rep (ConjClasses.mk w) * g⁻¹) * g
              = Work.CharCore.rep (ConjClasses.mk w) := by group
          rw [hg] at h2
          exact h2.symm
        rw [harg]
    _ = ψ w := by simpa using hψclass g⁻¹ w

/-- **The master congruence** (Peterfalvi, App. XII (7)): for an irreducible character `ψ` of `G`
which is constant with value `ψ z` on `Z^#`,
`ψ(z) (U₁₁ - U₁₂) ≡ ψ(1) |C₁| mod |Q|`, where `U₁₁`, `U₁₂` count the pairs with `1 ≠ xy ∈ Z` in
`C₁ × C₁` and `C₁ × C₁⁻¹` respectively (`C₁` the class of `z`). -/
theorem congr_master (h : Work.FeitSibley.FSData G) {Z : Subgroup G}
    (hZnorm : h.H ≤ Subgroup.normalizer (Z : Set G)) (hZQ1 : Z ≤ h.Q1)
    {z : G} (hz : z ∈ Z) (hz1 : z ≠ 1)
    (hnotconj : ∀ g : G, g * z * g⁻¹ ≠ z⁻¹)
    {ψ : G → ℂ} (hψ : ψ ∈ Work.CharCore.Irr G)
    (hconst : ∀ z' ∈ Z, z' ≠ 1 → ψ z' = ψ z) :
    IsIntegral ℤ (((ψ z) * ((Ucount Z (ConjClasses.mk z) (ConjClasses.mk z) : ℂ)
        - (Ucount Z (ConjClasses.mk z) (ConjClasses.mk z⁻¹) : ℂ))
      - (ψ 1) * ((Fintype.card (ConjClasses.mk z).carrier : ℕ) : ℂ))
      / (Nat.card h.Q : ℂ)) := by
  classical
  obtain ⟨N, hNmem, hchar⟩ := Work.CharCore.exists_mem_irrSubmodules_of_mem_Irr hψ
  have hN : IsSimpleModule (Work.CharCore.groupAlgebra G) N :=
    Work.CharCore.isSimpleModule_of_mem_irrSubmodules N hNmem
  set ω : ℂ := Work.CharCore.centralChar N hN
    ⟨Work.CharCore.conjClassSum (ConjClasses.mk z),
      Work.CharCore.classSum_mem_center (ConjClasses.mk z)⟩ with hω
  set ω₂ : ℂ := Work.CharCore.centralChar N hN
    ⟨Work.CharCore.conjClassSum (ConjClasses.mk z⁻¹),
      Work.CharCore.classSum_mem_center (ConjClasses.mk z⁻¹)⟩ with hω₂
  have hψclass : ∀ g x : G, ψ (g * x * g⁻¹) = ψ x := by
    intro g x
    rw [← hchar]
    exact Representation.char_conj (Work.CharCore.submoduleRep N) x g
  have hψint : ∀ x : G, IsIntegral ℤ (ψ x) := by
    intro x
    rw [← hchar]
    exact Representation.isIntegral_character (Work.CharCore.submoduleRep N) x
  have hfin : (Module.finrank ℂ N : ℂ) = ψ 1 := by
    rw [← hchar]
    exact (Representation.char_one (Work.CharCore.submoduleRep N)).symm
  have hψ1ne : ψ 1 ≠ 0 := by
    rw [Work.CharCore.irrDeg_spec hψ]
    exact_mod_cast Work.CharCore.irrDeg_ne_zero hψ
  -- the central characters of the two classes
  have hω1 : ω * ψ 1 = ((Fintype.card (ConjClasses.mk z).carrier : ℕ) : ℂ) * ψ z := by
    have h := Work.CharCore.centralChar_classSum_mul_finrank N hN (ConjClasses.mk z)
    rw [hchar] at h
    rw [rep_value_of_class_eq hψclass (C := ConjClasses.mk z) (w := z) rfl] at h
    rw [hfin] at h
    rw [← hω] at h
    exact h
  have hκ2 : Fintype.card (ConjClasses.mk z⁻¹).carrier
      = Fintype.card (ConjClasses.mk z).carrier := card_class_inv_eq_card
  have hω2 : ω₂ * ψ 1 = ((Fintype.card (ConjClasses.mk z).carrier : ℕ) : ℂ) * ψ z := by
    have h := Work.CharCore.centralChar_classSum_mul_finrank N hN (ConjClasses.mk z⁻¹)
    rw [hchar] at h
    rw [rep_value_of_class_eq hψclass (C := ConjClasses.mk z⁻¹) (w := z⁻¹) rfl] at h
    rw [hconst z⁻¹ (inv_mem hz) (fun hc => hz1 (inv_eq_one.mp hc))] at h
    rw [hκ2] at h
    rw [hfin] at h
    rw [← hω₂] at h
    exact h
  have hωeq : ω₂ = ω := mul_right_cancel₀ hψ1ne (hω2.trans hω1.symm)
  -- the trace identities
  have key1 : ψ 1 * (ω * ω) =
      ∑ p : (ConjClasses.mk z).carrier × (ConjClasses.mk z).carrier, ψ (p.1.1 * p.2.1) := by
    have h := centralChar_mul_eq_pair_sum N hN (ConjClasses.mk z) (ConjClasses.mk z)
    rw [hchar] at h
    rw [hfin] at h
    rw [← hω] at h
    rw [← h]
    ring
  have key2 : ψ 1 * (ω * ω) =
      ∑ p : (ConjClasses.mk z).carrier × (ConjClasses.mk z⁻¹).carrier, ψ (p.1.1 * p.2.1) := by
    have h := centralChar_mul_eq_pair_sum N hN (ConjClasses.mk z) (ConjClasses.mk z⁻¹)
    rw [hchar] at h
    rw [hfin] at h
    rw [← hω, ← hω₂, hωeq] at h
    rw [← h]
    ring
  -- the splittings
  have hi1 : (ψ z) * (Ucount Z (ConjClasses.mk z) (ConjClasses.mk z) : ℂ)
      + (∑ p : (ConjClasses.mk z).carrier × (ConjClasses.mk z).carrier,
          if (p.1.1 * p.2.1 : G) ∈ Z then (0 : ℂ) else ψ (p.1.1 * p.2.1))
      = ψ 1 * (ω * ω) := by
    rw [key1, sum_pair_split h hz hz1 hz hz1 hconst, Vcount_self_eq_zero hnotconj]
    ring
  have hi2 : (ψ 1) * ((Fintype.card (ConjClasses.mk z).carrier : ℕ) : ℂ)
      + (ψ z) * (Ucount Z (ConjClasses.mk z) (ConjClasses.mk z⁻¹) : ℂ)
      + (∑ p : (ConjClasses.mk z).carrier × (ConjClasses.mk z⁻¹).carrier,
          if (p.1.1 * p.2.1 : G) ∈ Z then (0 : ℂ) else ψ (p.1.1 * p.2.1))
      = ψ 1 * (ω * ω) := by
    rw [key2, sum_pair_split h hz hz1 (inv_mem hz) (fun hc => hz1 (inv_eq_one.mp hc)) hconst,
      Vcount_mk_inv]
  -- the out-of-`Z` sums
  have hint11 : IsIntegral ℤ ((∑ p : (ConjClasses.mk z).carrier × (ConjClasses.mk z).carrier,
      if (p.1.1 * p.2.1 : G) ∈ Z then (0 : ℂ) else ψ (p.1.1 * p.2.1))
      / (Nat.card h.Q : ℂ)) :=
    isIntegral_sum_pairs_out_Z h hZnorm hZQ1 hz hz1 hz hz1 ψ hψclass hψint
  have hint12 : IsIntegral ℤ ((∑ p : (ConjClasses.mk z).carrier
      × (ConjClasses.mk z⁻¹).carrier,
      if (p.1.1 * p.2.1 : G) ∈ Z then (0 : ℂ) else ψ (p.1.1 * p.2.1))
      / (Nat.card h.Q : ℂ)) :=
    isIntegral_sum_pairs_out_Z h hZnorm hZQ1 hz hz1 (inv_mem hz)
      (fun hc => hz1 (inv_eq_one.mp hc)) ψ hψclass hψint
  have hA : IsIntegral ℤ (((ψ z) * (Ucount Z (ConjClasses.mk z) (ConjClasses.mk z) : ℂ)
      - ψ 1 * (ω * ω)) / (Nat.card h.Q : ℂ)) := by
    have := hint11.neg
    convert this using 1
    rw [← hi1]
    ring
  have hB : IsIntegral ℤ (((ψ 1) * ((Fintype.card (ConjClasses.mk z).carrier : ℕ) : ℂ)
      + (ψ z) * (Ucount Z (ConjClasses.mk z) (ConjClasses.mk z⁻¹) : ℂ) - ψ 1 * (ω * ω))
      / (Nat.card h.Q : ℂ)) := by
    have := hint12.neg
    convert this using 1
    rw [← hi2]
    ring
  have hsub := hA.sub hB
  convert hsub using 1
  push_cast
  ring

/-! ## 7. Number-theoretic helpers -/

/-- The value of an irreducible character is an algebraic integer. -/
theorem isIntegral_irr_value {ψ : G → ℂ} (hψ : ψ ∈ Work.CharCore.Irr G) (x : G) :
    IsIntegral ℤ (ψ x) := by
  obtain ⟨N, hNmem, hNχ⟩ := Work.CharCore.exists_mem_irrSubmodules_of_mem_Irr hψ
  rw [← hNχ]
  exact Representation.isIntegral_character (Work.CharCore.submoduleRep N) x

/-- If `m / n` (for `m : ℤ`) is an algebraic integer then `n ∣ m`. -/
theorem dvd_of_isIntegral_int_div {n : ℕ} (hn : n ≠ 0) {m : ℤ}
    (h : IsIntegral ℤ (((m : ℤ) : ℂ) / (n : ℂ))) : (n : ℤ) ∣ m := by
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hq : IsIntegral ℤ ((((m : ℚ) / (n : ℚ) : ℚ)) : ℂ) := by
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
    exact h
  obtain ⟨s, hs⟩ := Work.NormalComplement.rat_eq_int_of_isIntegral hq
  refine ⟨s, ?_⟩
  have h2 : (m : ℚ) = (n : ℚ) * (s : ℚ) := by
    have h3 : (n : ℚ) * ((m : ℚ) / (n : ℚ)) = (m : ℚ) := by
      rw [mul_comm, div_mul_cancel₀ _ hnq]
    rw [hs] at h3
    exact h3.symm
  exact_mod_cast h2

/-- Bezout: coprime natural numbers are an integral linear combination of `1`. -/
theorem exists_bezout_int {k n : ℕ} (h : Nat.Coprime k n) :
    ∃ u v : ℤ, u * (k : ℤ) + v * (n : ℤ) = 1 := h.isCoprime

/-- **Cancelling a factor coprime to `n`**: if `x` and `k x / n` are algebraic integers with
`(k, n) = 1`, then so is `x / n`. -/
theorem isIntegral_div_of_coprime {n : ℕ} (hn : n ≠ 0) {x : ℂ} (hx : IsIntegral ℤ x)
    {k : ℕ} (hkx : IsIntegral ℤ (((k : ℂ) * x) / (n : ℂ))) (hcop : Nat.Coprime k n) :
    IsIntegral ℤ (x / (n : ℂ)) := by
  obtain ⟨u, v, huv⟩ := exists_bezout_int hcop
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have hcast : ((u * (k : ℤ) + v * (n : ℤ) : ℤ) : ℂ) = 1 := by
    rw [huv]
    norm_num
  have huk : (u : ℂ) * (k : ℂ) + (v : ℂ) * (n : ℂ) = 1 := by
    rw [← hcast]
    push_cast
    ring
  have h2 : x / (n : ℂ) = (u : ℂ) * (((k : ℂ) * x) / (n : ℂ)) + (v : ℂ) * x := by
    field_simp
    rw [mul_comm (n : ℂ) (v : ℂ), huk]
    ring
  rw [h2]
  exact ((isIntegral_intCast u).mul hkx).add ((isIntegral_intCast v).mul hx)

end Work.FeitSibley.Coherence
