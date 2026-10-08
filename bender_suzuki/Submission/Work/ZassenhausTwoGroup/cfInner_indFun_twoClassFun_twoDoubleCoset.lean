import Mathlib
import Submission.Work.Induction.All
import Submission.Work.CharCore.Main
import Submission.Work.ZassenhausTwoGroup.TwoClassFunSetup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-!
# The two-double-coset induction computation for a `(H, t)` cover `G = H ∪ HtH`

This file proves
`Work.ZassenhausTwoGroup.cfInner_indFun_twoClassFun_twoDoubleCoset`: if `H ≤ G`, `t² = 1`,
`t ∉ H` and `G = H ∪ HtH`, and `φ, ψ : H → ℂ` are class functions, then

`⟪Ind_H^G φ, Ind_H^G ψ⟫_G = ⟪φ, ψ⟫_H + |K|⁻¹ ∑_{d ∈ K} φ d · conj (ψ (t d t⁻¹))`,

where `K = H ⊓ H^t` is the "two-point stabiliser".  This is the classical double-coset
(Mackey) computation of the inner product of two induced class functions for the two
double cosets `H` and `HtH`.
-/

noncomputable section

open Classical Finset
open scoped BigOperators Pointwise

namespace Work.ZassenhausTwoGroup

variable {G : Type*} [Group G] [Fintype G]

/-- `MulAut.conj t` is an involution when `t² = 1`. -/
theorem MulAut_conj_invol {t : G} (ht : t * t = 1) (x : G) :
    (MulAut.conj t) ((MulAut.conj t) x) = x := by
  rw [MulAut.conj_apply, MulAut.conj_apply]
  rw [show t * (t * x * t⁻¹) * t⁻¹ = (t * t) * x * (t⁻¹ * t⁻¹) from by group]
  rw [ht]
  have h2 : t⁻¹ * t⁻¹ = 1 := by rw [← mul_inv_rev t t, ht, inv_one]
  rw [h2]
  group

/-- Summing an indicator over a finite type is the same as summing over the subtype. -/
theorem sum_ite_mem_eq_sum_subtype {α : Type*} [Fintype α] (p : α → Prop) [Fintype (Subtype p)]
    (F : α → ℂ) :
    (∑ a : α, if p a then F a else 0) = ∑ a : Subtype p, F a := by
  rw [← Finset.sum_filter (s := Finset.univ)]
  exact Finset.sum_subtype (Finset.univ.filter p) (fun a => by simp) F

/-- **Expansion of the inner product of two induced class functions.** -/
theorem cfInner_indFun_eq_tripleSum (H : Subgroup G) [Fintype ↥H] (φ ψ : ↥H → ℂ) :
    Work.CharCore.cfInner (Work.Induction.indFun H φ) (Work.Induction.indFun H ψ) =
      (Fintype.card G : ℂ)⁻¹ * (Nat.card ↥H : ℂ)⁻¹ * (Nat.card ↥H : ℂ)⁻¹ *
        ∑ g : G, ∑ x : G, ∑ y : G,
          extFun H φ (x * g * x⁻¹) * star (extFun H ψ (y * g * y⁻¹)) := by
  have hst : ∀ g : G, star (Work.Induction.indFun H ψ g)
      = (Nat.card ↥H : ℂ)⁻¹ * ∑ y : G, star (extFun H ψ (y * g * y⁻¹)) := by
    intro g
    rw [indFun_eq_sum_extFun H ψ g]
    show starRingEnd ℂ ((Nat.card ↥H : ℂ)⁻¹ * ∑ y : G, extFun H ψ (y * g * y⁻¹))
      = (Nat.card ↥H : ℂ)⁻¹ * ∑ y : G, starRingEnd ℂ (extFun H ψ (y * g * y⁻¹))
    rw [map_mul, map_inv₀, map_natCast, map_sum]
  have hterm : ∀ g : G, Work.Induction.indFun H φ g * star (Work.Induction.indFun H ψ g)
      = (Nat.card ↥H : ℂ)⁻¹ * (Nat.card ↥H : ℂ)⁻¹ *
          ((∑ x : G, extFun H φ (x * g * x⁻¹)) *
            ∑ y : G, star (extFun H ψ (y * g * y⁻¹))) := by
    intro g
    rw [indFun_eq_sum_extFun H φ g, hst g]
    ring
  have hsum : (∑ g : G, Work.Induction.indFun H φ g * star (Work.Induction.indFun H ψ g))
      = (Nat.card ↥H : ℂ)⁻¹ * (Nat.card ↥H : ℂ)⁻¹ *
          ∑ g : G, ∑ x : G, ∑ y : G,
            extFun H φ (x * g * x⁻¹) * star (extFun H ψ (y * g * y⁻¹)) := by
    rw [Finset.sum_congr rfl (fun g _ => hterm g)]
    rw [← Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl (fun g _ => ?_)
    exact Finset.sum_mul_sum Finset.univ Finset.univ
      (fun x : G => extFun H φ (x * g * x⁻¹))
      (fun y : G => star (extFun H ψ (y * g * y⁻¹)))
  rw [Work.CharCore.cfInner]
  show (Fintype.card G : ℂ)⁻¹ *
      (∑ g : G, Work.Induction.indFun H φ g * star (Work.Induction.indFun H ψ g)) = _
  rw [hsum]
  ring

/-- **Reindexing the triple sum.**  The substitution `(g, y) ↦ (x * g * x⁻¹, y * x⁻¹)`
(an equivalence of `G × G`) makes the inner sum independent of `x`, and the sum over `H`
of `extFun H φ` is the sum over `φ` itself. -/
theorem tripleSum_reindex (H : Subgroup G) [Fintype ↥H] (φ ψ : ↥H → ℂ) :
    (∑ g : G, ∑ x : G, ∑ y : G,
        extFun H φ (x * g * x⁻¹) * star (extFun H ψ (y * g * y⁻¹)))
      = (Fintype.card G : ℂ) *
          ∑ u : ↥H, ∑ z : G, φ u * star (extFun H ψ (z * (u : G) * z⁻¹)) := by
  have hinner : ∀ x : G,
      (∑ g : G, ∑ y : G, extFun H φ (x * g * x⁻¹) * star (extFun H ψ (y * g * y⁻¹)))
        = ∑ h : G, ∑ z : G, extFun H φ h * star (extFun H ψ (z * h * z⁻¹)) := by
    intro x
    have step1 : (∑ g : G, ∑ y : G, extFun H φ (x * g * x⁻¹) * star (extFun H ψ (y * g * y⁻¹)))
        = ∑ g : G, ∑ z : G,
            extFun H φ (x * g * x⁻¹) * star (extFun H ψ (z * (x * g * x⁻¹) * z⁻¹)) := by
      refine Finset.sum_congr rfl (fun g _ => ?_)
      refine Fintype.sum_equiv (Equiv.mulRight x⁻¹) _ _ (fun y => ?_)
      show extFun H φ (x * g * x⁻¹) * star (extFun H ψ (y * g * y⁻¹))
        = extFun H φ (x * g * x⁻¹)
            * star (extFun H ψ ((y * x⁻¹) * (x * g * x⁻¹) * (y * x⁻¹)⁻¹))
      rw [show (y * x⁻¹) * (x * g * x⁻¹) * (y * x⁻¹)⁻¹ = y * g * y⁻¹ from by group]
    rw [step1]
    exact Fintype.sum_equiv ((MulAut.conj x).toEquiv)
      (fun g => ∑ z : G, extFun H φ (x * g * x⁻¹) * star (extFun H ψ (z * (x * g * x⁻¹) * z⁻¹)))
      (fun h => ∑ z : G, extFun H φ h * star (extFun H ψ (z * h * z⁻¹)))
      (fun g => by
        show (∑ z : G, extFun H φ (x * g * x⁻¹) * star (extFun H ψ (z * (x * g * x⁻¹) * z⁻¹)))
          = ∑ z : G, extFun H φ ((MulAut.conj x) g) * star (extFun H ψ (z * (MulAut.conj x) g * z⁻¹))
        rw [MulAut.conj_apply])
  calc (∑ g : G, ∑ x : G, ∑ y : G, extFun H φ (x * g * x⁻¹) * star (extFun H ψ (y * g * y⁻¹)))
      = ∑ x : G, ∑ g : G, ∑ y : G, extFun H φ (x * g * x⁻¹) * star (extFun H ψ (y * g * y⁻¹)) := by
        rw [Finset.sum_comm]
    _ = ∑ x : G, ∑ h : G, ∑ z : G, extFun H φ h * star (extFun H ψ (z * h * z⁻¹)) :=
        Finset.sum_congr rfl (fun x _ => hinner x)
    _ = (Fintype.card G : ℂ) *
          (∑ h : G, ∑ z : G, extFun H φ h * star (extFun H ψ (z * h * z⁻¹))) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    _ = (Fintype.card G : ℂ) *
          ∑ u : ↥H, ∑ z : G, φ u * star (extFun H ψ (z * (u : G) * z⁻¹)) := by
        congr 1
        rw [show (∑ h : G, ∑ z : G, extFun H φ h * star (extFun H ψ (z * h * z⁻¹)))
              = ∑ h : G, extFun H φ h * (∑ z : G, star (extFun H ψ (z * h * z⁻¹))) from
            Finset.sum_congr rfl (fun h _ => (Finset.mul_sum Finset.univ _ _).symm)]
        rw [sum_extFun_mul H φ (fun h : G => ∑ z : G, star (extFun H ψ (z * h * z⁻¹)))]
        exact Finset.sum_congr rfl (fun u _ => Finset.mul_sum Finset.univ _ _)

/-- **Splitting the sum over `G` into `H` and `HtH`.** -/
theorem sum_eq_sum_subtype_add_dcos (H : Subgroup G) {t : G} [Fintype ↥H] (htH : t ∉ H)
    (hcover : ∀ g : G, g ∈ H ∨ ∃ a b : ↥H, g = (a : G) * t * (b : G)) (F : G → ℂ) :
    (∑ z : G, F z) =
      (∑ z : ↥H, F (z : G)) +
        ∑ z : {z : G // ∃ a b : ↥H, z = (a : G) * t * (b : G)}, F (z : G) := by
  have hdisj : ∀ z : G, ¬ (z ∈ H ∧ z ∈ dcos H t) := by
    rintro z ⟨hzH, a, b, hz⟩
    apply htH
    have he : t = (a : G)⁻¹ * z * (b : G)⁻¹ := by rw [hz]; group
    rw [he]
    exact H.mul_mem (H.mul_mem (H.inv_mem a.2) hzH) (H.inv_mem b.2)
  have hcover' : ∀ z : G, z ∈ H ∨ z ∈ dcos H t :=
    fun z => (hcover z).imp id (fun ⟨a, b, h⟩ => ⟨a, b, h⟩)
  have hterm : ∀ z : G, F z = (if z ∈ H then F z else 0) + (if z ∈ dcos H t then F z else 0) := by
    intro z
    rcases hcover' z with hz | hz
    · have hz' : z ∉ dcos H t := fun h => hdisj z ⟨hz, h⟩
      rw [if_pos hz, if_neg hz', add_zero]
    · have hz' : z ∉ H := fun h => hdisj z ⟨h, hz⟩
      rw [if_neg hz', if_pos hz, zero_add]
  rw [Finset.sum_congr rfl (fun z _ => hterm z), Finset.sum_add_distrib]
  congr 1
  · exact sum_ite_mem_eq_sum_subtype (fun z : G => z ∈ H) F
  · exact sum_ite_mem_eq_sum_subtype (fun z : G => ∃ a b : ↥H, z = (a : G) * t * (b : G)) F

/-- **The `H`-contribution.**  For `z ∈ H` the conjugate `z u z⁻¹` lies in `H` and
`ψ (z u z⁻¹) = ψ u`; the sum over `z` of the (constant) `conj (ψ u)` gives `|H| · conj (ψ u)`. -/
theorem sum_H_part (H : Subgroup G) [Fintype ↥H] (φ ψ : ↥H → ℂ)
    (hψ : Work.CharCore.IsClassFun ψ) :
    (∑ u : ↥H, φ u * ∑ z : ↥H, star (extFun H ψ ((z : G) * (u : G) * (z : G)⁻¹)))
      = (Fintype.card ↥H : ℂ) * ∑ u : ↥H, φ u * star (ψ u) := by
  have hinner : ∀ u : ↥H, (∑ z : ↥H, star (extFun H ψ ((z : G) * (u : G) * (z : G)⁻¹)))
      = (Fintype.card ↥H : ℂ) * star (ψ u) := by
    intro u
    have hterm : ∀ z : ↥H, star (extFun H ψ ((z : G) * (u : G) * (z : G)⁻¹)) = star (ψ u) := by
      intro z
      rw [show (z : G) * (u : G) * (z : G)⁻¹ = ((z * u * z⁻¹ : ↥H) : G) from rfl,
          extFun_of_mem ((z * u * z⁻¹ : ↥H).2)]
      have he : (⟨((z * u * z⁻¹ : ↥H) : G), (z * u * z⁻¹ : ↥H).2⟩ : ↥H) = z * u * z⁻¹ :=
        Subtype.ext rfl
      rw [he]
      congr 1
      exact hψ u z
    rw [Finset.sum_congr rfl (fun z _ => hterm z)]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Finset.sum_congr rfl (fun u _ => by rw [hinner u])]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun u _ => by ring)

/-! ## The `HtH`-contribution -/

section Dcos

variable {G' : Type*} [Group G']

/-- The two-point stabiliser `H ⊓ H^t`. -/
abbrev Ksub {G : Type*} [Group G] (H : Subgroup G) (t : G) : Subgroup G :=
  H ⊓ H.map (MulAut.conj t).toMonoidHom

/-- The double coset `H t H`, as a subtype of `G`. -/
abbrev DcosSet {G : Type*} [Group G] (H : Subgroup G) (t : G) :=
  {z : G // ∃ a b : ↥H, z = (a : G) * t * (b : G)}

/-- From `a * t * b = a' * t * b'` deduce `a'⁻¹ * a = t * (b' * b⁻¹) * t⁻¹`. -/
theorem mul_t_mul_eq {t a b a' b' : G'} (h : a * t * b = a' * t * b') :
    a'⁻¹ * a = t * (b' * b⁻¹) * t⁻¹ := by
  calc a'⁻¹ * a = a'⁻¹ * (a * t * b) * (b⁻¹ * t⁻¹) := by group
    _ = a'⁻¹ * (a' * t * b') * (b⁻¹ * t⁻¹) := by rw [h]
    _ = t * (b' * b⁻¹) * t⁻¹ := by group

/-- The converse of `mul_t_mul_eq`. -/
theorem eq_of_mul_t_mul_eq {t a b a' b' : G'}
    (h : a'⁻¹ * a = t * (b' * b⁻¹) * t⁻¹) : a * t * b = a' * t * b' := by
  calc a * t * b = a' * (a'⁻¹ * a) * t * b := by group
    _ = a' * (t * (b' * b⁻¹) * t⁻¹) * t * b := by rw [h]
    _ = a' * t * b' := by group

/-- The inclusion `H ⊓ H^t ↪ H`. -/
def dcosIncl {G : Type*} [Group G] (H : Subgroup G) (t : G) (d : ↥(Ksub H t)) : ↥H :=
  ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩

theorem dcosIncl_coe {G : Type*} [Group G] (H : Subgroup G) (t : G) (d : ↥(Ksub H t)) :
    (dcosIncl H t d : G) = (d : G) := rfl

/-- A chosen representation `z = a * t * b` of `z ∈ HtH`. -/
noncomputable def dcosA {G : Type*} [Group G] (H : Subgroup G) (t : G) (z : DcosSet H t) : ↥H :=
  Classical.choose z.2

/-- The second coordinate of the chosen representation of `z ∈ HtH`. -/
noncomputable def dcosB {G : Type*} [Group G] (H : Subgroup G) (t : G)
    (z : DcosSet H t) : ↥H := Classical.choose (Classical.choose_spec z.2)

theorem dcos_spec {G : Type*} [Group G] (H : Subgroup G) (t : G) (z : DcosSet H t) :
    (z : G) = (dcosA H t z : G) * t * (dcosB H t z : G) :=
  Classical.choose_spec (Classical.choose_spec z.2)

/-- `(a, b) ↦ a * t * b` as an element of the double coset. -/
noncomputable def dcosMk {G : Type*} [Group G] (H : Subgroup G) (t : G)
    (p : ↥H × ↥H) : DcosSet H t :=
  ⟨(p.1 : G) * t * (p.2 : G), ⟨p.1, p.2, rfl⟩⟩

theorem dcosMk_coe {G : Type*} [Group G] (H : Subgroup G) (t : G) (p : ↥H × ↥H) :
    ((dcosMk H t p : DcosSet H t) : G) = (p.1 : G) * t * (p.2 : G) := rfl

/-- The element `t⁻¹ d⁻¹ t ∈ H` attached to `d ∈ H ⊓ H^t`. -/
noncomputable def dcosTau {G : Type*} [Group G] (H : Subgroup G) (t : G)
    (d : ↥(Ksub H t)) : ↥H :=
  ⟨t⁻¹ * (d : G)⁻¹ * t, by
    obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp (Subgroup.mem_inf.mp d.2).2
    have hyeq' : (MulAut.conj t) y = (d : G) := hyeq
    have h : t⁻¹ * (d : G)⁻¹ * t = (y : G)⁻¹ := by
      rw [← hyeq', MulAut.conj_apply]; group
    rw [h]; exact H.inv_mem hy⟩

theorem dcosTau_apply {G : Type*} [Group G] (H : Subgroup G) (t : G) (d : ↥(Ksub H t)) :
    (dcosTau H t d : G) = t⁻¹ * (d : G)⁻¹ * t := rfl

/-- The map `(d, z) ↦ (a₀ d, (t⁻¹ d⁻¹ t) b₀)` where `z = a₀ t b₀`; it identifies
`K × HtH` with `H × H`. -/
noncomputable def dcosTheta {G : Type*} [Group G] (H : Subgroup G) (t : G)
    (q : ↥(Ksub H t) × DcosSet H t) : ↥H × ↥H :=
  (dcosA H t q.2 * dcosIncl H t q.1, dcosTau H t q.1 * dcosB H t q.2)

theorem dcosTheta_fst {G : Type*} [Group G] (H : Subgroup G) (t : G)
    (q : ↥(Ksub H t) × DcosSet H t) :
    (dcosTheta H t q).1 = dcosA H t q.2 * dcosIncl H t q.1 := rfl

theorem dcosTheta_snd {G : Type*} [Group G] (H : Subgroup G) (t : G)
    (q : ↥(Ksub H t) × DcosSet H t) :
    (dcosTheta H t q).2 = dcosTau H t q.1 * dcosB H t q.2 := rfl

/-- `Φ (Θ q) = q.2`, where `Φ (a,b) = a t b`. -/
theorem dcosPhi_theta {G : Type*} [Group G] (H : Subgroup G) (t : G)
    (q : ↥(Ksub H t) × DcosSet H t) :
    ((dcosTheta H t q).1 : G) * t * ((dcosTheta H t q).2 : G) = (q.2 : G) := by
  have h1 : ((dcosTheta H t q).1 : G) = (dcosA H t q.2 : G) * (q.1 : G) := rfl
  have h2 : ((dcosTheta H t q).2 : G) = (dcosTau H t q.1 : G) * (dcosB H t q.2 : G) := rfl
  rw [h1, h2, dcosTau_apply, dcos_spec H t q.2]
  exact eq_of_mul_t_mul_eq (by group)

/-- The candidate inverse of `dcosTheta`. -/
noncomputable def dcosXiK {G : Type*} [Group G] (H : Subgroup G) (t : G)
    (p : ↥H × ↥H) : ↥(Ksub H t) :=
  ⟨(dcosA H t (dcosMk H t p) : G)⁻¹ * (p.1 : G), by
    have h2 : (dcosA H t (dcosMk H t p) : G) * t * (dcosB H t (dcosMk H t p) : G)
        = (p.1 : G) * t * (p.2 : G) := by
      rw [← dcos_spec H t (dcosMk H t p)]; rfl
    refine Subgroup.mem_inf.mpr
      ⟨H.mul_mem (H.inv_mem (dcosA H t (dcosMk H t p)).2) p.1.2, ?_⟩
    have hkey : t * ((dcosB H t (dcosMk H t p) : G) * (p.2 : G)⁻¹) * t⁻¹
        = (dcosA H t (dcosMk H t p) : G)⁻¹ * (p.1 : G) := by
      have h4 : (dcosA H t (dcosMk H t p) : G) *
            (t * ((dcosB H t (dcosMk H t p) : G) * (p.2 : G)⁻¹) * t⁻¹)
          = (dcosA H t (dcosMk H t p) : G) *
            ((dcosA H t (dcosMk H t p) : G)⁻¹ * (p.1 : G)) := by
        have he1 : (dcosA H t (dcosMk H t p) : G) *
            ((dcosA H t (dcosMk H t p) : G)⁻¹ * (p.1 : G)) = (p.1 : G) := by group
        rw [he1]
        have he2 : (p.1 : G) = (p.1 : G) * t * (p.2 : G) * (t * (p.2 : G))⁻¹ := by group
        rw [he2, ← h2]; group
      exact mul_left_cancel h4
    refine Subgroup.mem_map.mpr
      ⟨(dcosB H t (dcosMk H t p) * p.2⁻¹ : ↥H),
        H.mul_mem (dcosB H t (dcosMk H t p)).2 (H.inv_mem p.2.2), ?_⟩
    show t * ((dcosB H t (dcosMk H t p) : G) * (p.2 : G)⁻¹) * t⁻¹
      = (dcosA H t (dcosMk H t p) : G)⁻¹ * (p.1 : G)
    exact hkey⟩

theorem dcosXiK_coe {G : Type*} [Group G] (H : Subgroup G) (t : G) (p : ↥H × ↥H) :
    (dcosXiK H t p : G) = (dcosA H t (dcosMk H t p) : G)⁻¹ * (p.1 : G) := rfl

/-- The candidate inverse of `dcosTheta`. -/
noncomputable def dcosXi {G : Type*} [Group G] (H : Subgroup G) (t : G)
    (p : ↥H × ↥H) : ↥(Ksub H t) × DcosSet H t :=
  (dcosXiK H t p, dcosMk H t p)

theorem dcosXi_fst {G : Type*} [Group G] (H : Subgroup G) (t : G) (p : ↥H × ↥H) :
    (dcosXi H t p).1 = dcosXiK H t p := rfl

theorem dcosXi_snd {G : Type*} [Group G] (H : Subgroup G) (t : G) (p : ↥H × ↥H) :
    (dcosXi H t p).2 = dcosMk H t p := rfl

theorem dcosTheta_left {G : Type*} [Group G] (H : Subgroup G) (t : G)
    (q : ↥(Ksub H t) × DcosSet H t) : dcosXi H t (dcosTheta H t q) = q := by
  obtain ⟨d, z⟩ := q
  have hz : dcosMk H t (dcosTheta H t (d, z)) = z := by
    apply Subtype.ext
    show ((dcosTheta H t (d, z)).1 : G) * t * ((dcosTheta H t (d, z)).2 : G) = (z : G)
    exact dcosPhi_theta H t (d, z)
  apply Prod.ext
  · rw [dcosXi_fst]
    apply Subtype.ext
    show (dcosA H t (dcosMk H t (dcosTheta H t (d, z))) : G)⁻¹
        * ((dcosTheta H t (d, z)).1 : G) = (d : G)
    rw [hz, dcosTheta_fst, Subgroup.coe_mul, dcosIncl_coe]
    group
  · rw [dcosXi_snd]
    exact hz

theorem dcosTheta_right {G : Type*} [Group G] (H : Subgroup G) (t : G)
    (p : ↥H × ↥H) : dcosTheta H t (dcosXi H t p) = p := by
  obtain ⟨a, b⟩ := p
  have h2 : (dcosA H t (dcosMk H t (a, b)) : G) * t * (dcosB H t (dcosMk H t (a, b)) : G)
      = (a : G) * t * (b : G) := by
    rw [← dcos_spec H t (dcosMk H t (a, b))]; rfl
  have hd : (dcosXiK H t (a, b) : G)
      = t * ((dcosB H t (dcosMk H t (a, b)) : G) * (b : G)⁻¹) * t⁻¹ := by
    rw [dcosXiK_coe]
    exact mul_t_mul_eq h2.symm
  apply Prod.ext
  · rw [dcosTheta_fst, dcosXi_fst]
    apply Subtype.ext
    show ((dcosA H t (dcosMk H t (a, b)) * dcosIncl H t (dcosXiK H t (a, b)) : ↥H) : G)
      = (a : G)
    rw [Subgroup.coe_mul, dcosIncl_coe, dcosXiK_coe]
    group
  · rw [dcosTheta_snd, dcosXi_fst]
    apply Subtype.ext
    show ((dcosTau H t (dcosXiK H t (a, b)) * dcosB H t (dcosMk H t (a, b)) : ↥H) : G)
      = (b : G)
    rw [Subgroup.coe_mul, dcosTau_apply, hd]
    group

/-- The bijection `K × HtH ≃ H × H`, `(d, a t b) ↦ (a d, (t⁻¹ d⁻¹ t) b)`. -/
noncomputable def dcosEquiv {G : Type*} [Group G] (H : Subgroup G) (t : G) :
    (↥(Ksub H t) × DcosSet H t) ≃ (↥H × ↥H) :=
  Equiv.mk (dcosTheta H t) (dcosXi H t) (dcosTheta_left H t) (dcosTheta_right H t)

theorem dcosEquiv_apply {G : Type*} [Group G] (H : Subgroup G) (t : G)
    (q : ↥(Ksub H t) × DcosSet H t) : dcosEquiv H t q = dcosTheta H t q := rfl

/-- **Fiber cardinality.**  Every element of `HtH` has exactly `|K|` representations as
`a * t * b` with `a, b ∈ H`. -/
theorem dcosFiberCard (H : Subgroup G) (t : G) [Fintype ↥H] (f : G → ℂ) :
    (Nat.card ↥(Ksub H t) : ℂ) * (∑ z : DcosSet H t, f (z : G))
      = ∑ a : ↥H, ∑ b : ↥H, f ((a : G) * t * (b : G)) := by
  have h2 : (∑ p : ↥H × ↥H, f ((p.1 : G) * t * (p.2 : G)))
      = ∑ q : ↥(Ksub H t) × DcosSet H t, f (q.2 : G) := by
    rw [← Equiv.sum_comp (dcosEquiv H t)
      (fun p : ↥H × ↥H => f ((p.1 : G) * t * (p.2 : G)))]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [dcosEquiv_apply, dcosPhi_theta]
  have h3 : (∑ q : ↥(Ksub H t) × DcosSet H t, f (q.2 : G))
      = (Fintype.card ↥(Ksub H t) : ℂ) * ∑ z : DcosSet H t, f (z : G) := by
    rw [Fintype.sum_prod_type]
    rw [show (∑ x : ↥(Ksub H t), ∑ y : DcosSet H t, f ((x, y).2 : G))
          = ∑ _x : ↥(Ksub H t), ∑ y : DcosSet H t, f (y : G) from rfl]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [Nat.card_eq_fintype_card, ← h3, ← h2, Fintype.sum_prod_type]

/-- The identity as a bijection `H ⊓ H^t ≃ {u : H // ↑u ∈ H ⊓ H^t}`. -/
noncomputable def dcosKBij {G : Type*} [Group G] (H : Subgroup G) (t : G) :
    ↥(Ksub H t) ≃ {u : ↥H // (u : G) ∈ Ksub H t} where
  toFun d := ⟨dcosIncl H t d, d.2⟩
  invFun u := ⟨(u.1 : G), u.2⟩
  left_inv d := Subtype.ext rfl
  right_inv u := Subtype.ext (Subtype.ext rfl)

theorem dcosKBij_apply {G : Type*} [Group G] (H : Subgroup G) (t : G) (d : ↥(Ksub H t)) :
    dcosKBij H t d = ⟨dcosIncl H t d, d.2⟩ := rfl

end Dcos

/-- **The `HtH`-contribution.**  Summing `conj (ψ̇ (z u z⁻¹))` over the double coset `HtH`
and then over `u ∈ H` gives `|H|² |K|⁻¹ ∑_{d ∈ K} φ d conj (ψ (t d t⁻¹))`. -/
theorem sum_dcos_part (H : Subgroup G) {t : G} [Fintype ↥H]
    [Fintype ↥(Ksub H t)] (ht : t * t = 1)
    (hDmap : ∀ d : ↥(Ksub H t), (MulAut.conj t) (d : G) ∈ Ksub H t)
    (φ ψ : ↥H → ℂ) (hφ : Work.CharCore.IsClassFun φ) (hψ : Work.CharCore.IsClassFun ψ) :
    (∑ u : ↥H, φ u * ∑ z : DcosSet H t, star (extFun H ψ ((z : G) * (u : G) * (z : G)⁻¹)))
      = (Nat.card ↥H : ℂ) ^ 2 * (Nat.card ↥(Ksub H t) : ℂ)⁻¹ *
          ∑ d : ↥(Ksub H t),
            φ ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ *
              star (ψ ⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩) := by
  have hKne : (Nat.card ↥(Ksub H t) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Nat.card_eq_fintype_card]; exact Fintype.card_ne_zero
  have hterm : ∀ u : ↥H, (Nat.card ↥(Ksub H t) : ℂ) *
        (∑ z : DcosSet H t, star (extFun H ψ ((z : G) * (u : G) * (z : G)⁻¹)))
      = (Nat.card ↥H : ℂ) *
        ∑ b : ↥H, star (extFun H ψ (t * (b : G) * (u : G) * (b : G)⁻¹ * t⁻¹)) := by
    intro u
    have hfib : (Nat.card ↥(Ksub H t) : ℂ) *
          (∑ z : DcosSet H t, star (extFun H ψ ((z : G) * (u : G) * (z : G)⁻¹)))
        = ∑ a : ↥H, ∑ b : ↥H,
            star (extFun H ψ (((a : G) * t * (b : G)) * (u : G) * ((a : G) * t * (b : G))⁻¹)) :=
      dcosFiberCard H t (fun x : G => star (extFun H ψ (x * (u : G) * x⁻¹)))
    rw [hfib]
    have hstep : ∀ a b : ↥H,
        star (extFun H ψ (((a : G) * t * (b : G)) * (u : G) * ((a : G) * t * (b : G))⁻¹))
          = star (extFun H ψ (t * (b : G) * (u : G) * (b : G)⁻¹ * t⁻¹)) := by
      intro a b
      rw [show ((a : G) * t * (b : G)) * (u : G) * ((a : G) * t * (b : G))⁻¹
            = (a : G) * (t * (b : G) * (u : G) * (b : G)⁻¹ * t⁻¹) * (a : G)⁻¹ from by group,
          extFun_conj hψ a (t * (b : G) * (u : G) * (b : G)⁻¹ * t⁻¹)]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hstep a b))]
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  have hstep1 : ∀ u : ↥H, (∑ z : DcosSet H t, star (extFun H ψ ((z : G) * (u : G) * (z : G)⁻¹)))
      = (Nat.card ↥(Ksub H t) : ℂ)⁻¹ * ((Nat.card ↥H : ℂ) *
          ∑ b : ↥H, star (extFun H ψ (t * (b : G) * (u : G) * (b : G)⁻¹ * t⁻¹))) := by
    intro u
    rw [← hterm u, inv_mul_cancel_left₀ hKne]
  have hmain : (∑ u : ↥H, φ u * ∑ z : DcosSet H t, star (extFun H ψ ((z : G) * (u : G) * (z : G)⁻¹)))
      = (Nat.card ↥(Ksub H t) : ℂ)⁻¹ * (Nat.card ↥H : ℂ) *
          ∑ u : ↥H, φ u * ∑ b : ↥H,
            star (extFun H ψ (t * (b : G) * (u : G) * (b : G)⁻¹ * t⁻¹)) := by
    rw [Finset.sum_congr rfl (fun u _ => by rw [hstep1 u])]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun u _ => by ring)
  rw [hmain]
  have hsub : (∑ u : ↥H, φ u * ∑ b : ↥H,
        star (extFun H ψ (t * (b : G) * (u : G) * (b : G)⁻¹ * t⁻¹)))
      = (Nat.card ↥H : ℂ) *
          ∑ d : ↥(Ksub H t),
            φ ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ *
              star (ψ ⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩) := by
    rw [show (∑ u : ↥H, φ u * ∑ b : ↥H,
            star (extFun H ψ (t * (b : G) * (u : G) * (b : G)⁻¹ * t⁻¹)))
          = ∑ b : ↥H, ∑ u : ↥H, φ u *
              star (extFun H ψ (t * (b : G) * (u : G) * (b : G)⁻¹ * t⁻¹)) from by
        rw [Finset.sum_congr rfl (fun u _ => Finset.mul_sum Finset.univ _ _)]
        rw [Finset.sum_comm]]
    have hC : (∑ u : ↥H, φ u * star (extFun H ψ (t * (u : G) * t⁻¹)))
        = ∑ d : ↥(Ksub H t),
            φ ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ *
              star (ψ ⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩) := by
      have hiff : ∀ u : ↥H, (u : G) ∈ Ksub H t ↔ (MulAut.conj t) (u : G) ∈ H := by
        intro u
        rw [Ksub, Subgroup.mem_inf]
        constructor
        · rintro ⟨-, hmap⟩
          obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.mp hmap
          have hyeq' : (MulAut.conj t) y = (u : G) := hyeq
          have hconv : (MulAut.conj t) (u : G) = y := by
            rw [← hyeq', MulAut_conj_invol ht]
          rw [hconv]
          exact hy
        · intro hmem
          exact ⟨u.2, Subgroup.mem_map.mpr ⟨(MulAut.conj t) (u : G), hmem, by
            change (MulAut.conj t) ((MulAut.conj t) (u : G)) = (u : G)
            rw [MulAut_conj_invol ht]⟩⟩
      rw [show (∑ u : ↥H, φ u * star (extFun H ψ (t * (u : G) * t⁻¹)))
            = ∑ u : ↥H, (if (u : G) ∈ Ksub H t then
                φ u * star (extFun H ψ (t * (u : G) * t⁻¹)) else 0) from
          Finset.sum_congr rfl (fun u _ => by
            by_cases hu : (u : G) ∈ Ksub H t
            · rw [if_pos hu]
            · rw [if_neg hu]
              rw [show t * (u : G) * t⁻¹ = (MulAut.conj t) (u : G) from
                (MulAut.conj_apply t (u : G)).symm]
              have hnot : ¬ ((MulAut.conj t) (u : G) ∈ H) := fun hm => hu ((hiff u).mpr hm)
              rw [extFun_of_notMem hnot, star_zero, mul_zero])]
      rw [sum_ite_mem_eq_sum_subtype (fun u : ↥H => (u : G) ∈ Ksub H t)
            (fun u : ↥H => φ u * star (extFun H ψ (t * (u : G) * t⁻¹)))]
      exact (Fintype.sum_equiv (dcosKBij H t)
        (fun d : ↥(Ksub H t) => φ ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ *
            star (ψ ⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩))
        (fun u : {u : ↥H // (u : G) ∈ Ksub H t} =>
            φ (u : ↥H) * star (extFun H ψ (t * ((u : ↥H) : G) * t⁻¹)))
        (fun d => by
          rw [dcosKBij_apply]
          show φ ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ *
              star (ψ ⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩)
            = φ (dcosIncl H t d) *
              star (extFun H ψ (t * (dcosIncl H t d : G) * t⁻¹))
          rw [dcosIncl_coe,
              show t * (d : G) * t⁻¹ = (MulAut.conj t) (d : G) from
                (MulAut.conj_apply t (d : G)).symm,
              extFun_of_mem ((Subgroup.mem_inf.mp (hDmap d)).1)]
          rfl)).symm
    have hbeq : ∀ b : ↥H, (∑ u : ↥H, φ u *
          star (extFun H ψ (t * (b : G) * (u : G) * (b : G)⁻¹ * t⁻¹)))
        = ∑ u : ↥H, φ u * star (extFun H ψ (t * (u : G) * t⁻¹)) := by
      intro b
      refine Fintype.sum_equiv ((MulAut.conj b).toEquiv) _ _ (fun u => ?_)
      show φ u * star (extFun H ψ (t * (b : G) * (u : G) * (b : G)⁻¹ * t⁻¹))
        = φ ((MulAut.conj b) u)
          * star (extFun H ψ (t * (((MulAut.conj b) u : ↥H) : G) * t⁻¹))
      rw [MulAut.conj_apply]
      congr 1
      · exact (hφ u b).symm
      · congr 1
        rw [show (↑(b * u * b⁻¹) : G) = (b : G) * (u : G) * (b : G)⁻¹ from rfl]
        group
    rw [Finset.sum_congr rfl (fun b _ => hbeq b)]
    rw [hC, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card]
  rw [hsub]
  rw [show (Nat.card ↥(Ksub H t) : ℂ)⁻¹ * (Nat.card ↥H : ℂ) *
        ((Nat.card ↥H : ℂ) * ∑ d : ↥(Ksub H t), φ ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ *
          star (ψ ⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩))
      = (Nat.card ↥H : ℂ) ^ 2 * (Nat.card ↥(Ksub H t) : ℂ)⁻¹ *
          ∑ d : ↥(Ksub H t), φ ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ *
            star (ψ ⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩) from by
    ring]

theorem cfInner_indFun_twoClassFun_twoDoubleCoset {G : Type} [Group G] [Fintype G]
    {H : Subgroup G} [Fintype ↥H] {t : G}
    [Fintype ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G)]
    (ht : t * t = 1) (htH : t ∉ H)
    (hcover : ∀ g : G, g ∈ H ∨ ∃ a b : H, g = (a : G) * t * (b : G))
    (hDmap : ∀ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G),
        (MulAut.conj t) (d : G) ∈ (H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G))
    (φ ψ : H → ℂ) (hφ : Work.CharCore.IsClassFun φ) (hψ : Work.CharCore.IsClassFun ψ) :
    Work.CharCore.cfInner (Work.Induction.indFun H φ) (Work.Induction.indFun H ψ) =
      Work.CharCore.cfInner φ ψ +
        (Nat.card ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G) : ℂ)⁻¹ *
          ∑ d : ↥(H ⊓ H.map (MulAut.conj t).toMonoidHom : Subgroup G),
            φ ⟨(d : G), (Subgroup.mem_inf.mp d.2).1⟩ *
              star (ψ ⟨(MulAut.conj t) (d : G), (Subgroup.mem_inf.mp (hDmap d)).1⟩) := by
  classical
  have hG : (Fintype.card G : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero]; exact Fintype.card_ne_zero
  have hB : (Nat.card ↥H : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Nat.card_eq_fintype_card]; exact Fintype.card_ne_zero
  have hK : (Nat.card ↥(Ksub H t) : ℂ) ≠ 0 := by
    rw [Nat.cast_ne_zero, Nat.card_eq_fintype_card]; exact Fintype.card_ne_zero
  -- cancel the `|G|` factor coming from the reindexing
  have hcancel : ∀ U : ℂ, (Fintype.card G : ℂ)⁻¹ * (Nat.card ↥H : ℂ)⁻¹ *
        (Nat.card ↥H : ℂ)⁻¹ * ((Fintype.card G : ℂ) * U)
      = (Nat.card ↥H : ℂ)⁻¹ * (Nat.card ↥H : ℂ)⁻¹ * U := by
    intro U
    rw [show (Fintype.card G : ℂ)⁻¹ * (Nat.card ↥H : ℂ)⁻¹ * (Nat.card ↥H : ℂ)⁻¹ *
            ((Fintype.card G : ℂ) * U)
          = ((Fintype.card G : ℂ)⁻¹ * (Fintype.card G : ℂ)) *
              ((Nat.card ↥H : ℂ)⁻¹ * (Nat.card ↥H : ℂ)⁻¹ * U) from by ring]
    rw [inv_mul_cancel₀ hG, one_mul]
  -- split the sum over `G` into the `H`-part and the `HtH`-part
  have hsplit : (∑ u : ↥H, ∑ z : G, φ u * star (extFun H ψ (z * (u : G) * z⁻¹)))
      = (∑ u : ↥H, φ u * ∑ z : ↥H, star (extFun H ψ ((z : G) * (u : G) * (z : G)⁻¹)))
        + (∑ u : ↥H, φ u * ∑ z : DcosSet H t,
            star (extFun H ψ ((z : G) * (u : G) * (z : G)⁻¹))) := by
    rw [show (∑ u : ↥H, ∑ z : G, φ u * star (extFun H ψ (z * (u : G) * z⁻¹)))
          = ∑ u : ↥H, φ u * ∑ z : G, star (extFun H ψ (z * (u : G) * z⁻¹)) from
        Finset.sum_congr rfl (fun u _ => (Finset.mul_sum Finset.univ _ _).symm)]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun u _ => ?_)
    rw [sum_eq_sum_subtype_add_dcos H htH hcover
          (fun z : G => star (extFun H ψ (z * (u : G) * z⁻¹))), mul_add]
  rw [cfInner_indFun_eq_tripleSum H φ ψ, tripleSum_reindex H φ ψ, hcancel, hsplit]
  rw [mul_add,
      sum_H_part H φ ψ hψ,
      sum_dcos_part H ht hDmap φ ψ hφ hψ]
  rw [← Nat.card_eq_fintype_card (α := ↥H)]
  rw [Work.CharCore.cfInner, ← Nat.card_eq_fintype_card (α := ↥H)]
  rw [show (∑ u : ↥H, φ u * star (ψ u))
        = ∑ x : ↥H, φ x * starRingEnd ℂ (ψ x) from rfl]
  field_simp

end Work.ZassenhausTwoGroup
