import Mathlib
import Submission.Work.PSU3.FineCoords.zeroDiagCocycle_is_coboundary

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.FineCoords

noncomputable section

/-- Version of `zeroDiagCocycle_is_coboundary` stated for a group with explicit
commutativity, so that it may be applied to a subgroup of the centre without
introducing a second (competing) `CommGroup` instance. -/
theorem coboundary_of_group {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    {M : Type*} [Group M] (hc : ∀ x y : M, x * y = y * x) (h2 : ∀ x : M, x * x = 1)
    (c : V → V → M)
    (h0l : ∀ v, c 0 v = 1) (h0r : ∀ v, c v 0 = 1)
    (hcoc : ∀ v u w, c v u * c (v + u) w = c u w * c v (u + w))
    (hdiag : ∀ v, c v v = 1) :
    ∃ f : V → M, f 0 = 1 ∧ ∀ v u, c v u = f (v + u) * f v * f u := by
  letI : CommGroup M := CommGroup.mk hc
  exact zeroDiagCocycle_is_coboundary (M := M) h2 c h0l h0r hcoc hdiag

/-- Rearrangement in a commutative group: `A * B * (C * D) = A * C * (B * D)`. -/
theorem rearr {M : Type*} [Group M] (hc : ∀ x y : M, x * y = y * x) (A B C D : M) :
    A * B * (C * D) = A * C * (B * D) := by
  letI : CommGroup M := CommGroup.mk hc
  ac_rfl

/-- Rearrangement lemma in a commutative group of exponent two:
from `G * C = F * A * B` conclude `A * B * C = G * F`. -/
theorem glue_commGroup {M : Type*} [Group M] (hc : ∀ x y : M, x * y = y * x)
    (hM : ∀ x : M, x * x = 1)
    (G F A B C : M) (h : G * C = F * A * B) : A * B * C = G * F := by
  letI : CommGroup M := CommGroup.mk hc
  have hG : G = F * A * B * C := by rw [← h, mul_assoc, hM C, mul_one]
  rw [hG]
  have e1 : F * A * B * C * F = A * B * C * (F * F) := by ac_rfl
  rw [e1, hM F, mul_one]

/-- Bundled data: a central extension of a `ZMod 2`-module `A` by an elementary abelian
`2`-subgroup `Z` of the centre, together with the property that every square lies in `Z`. -/
structure ExtData (A : Type*) [AddCommGroup A] [Module (ZMod 2) A] (G : Type*) [Group G] where
  Z : Subgroup G
  hZc : Z ≤ Subgroup.center G
  hZ2 : ∀ z ∈ Z, z * z = 1
  π : G →* Multiplicative A
  hπ : Function.Surjective π
  hker : π.ker = Z
  hsq : ∀ x : G, x ^ 2 ∈ Z

namespace ExtData

variable {A : Type*} [AddCommGroup A] [Module (ZMod 2) A] {G : Type*} [Group G] (D : ExtData A G)

/-- The `A`-coordinate of an element of `G`. -/
def tau (x : G) : A := Multiplicative.toAdd (D.π x)

theorem tau_mul (x y : G) : D.tau (x * y) = D.tau x + D.tau y := by
  simp [tau, map_mul]

/-- An unnormalised section of `π`. -/
def rawSec (a : A) : G := Function.surjInv D.hπ (Multiplicative.ofAdd a)

theorem pi_rawSec (a : A) : D.π (D.rawSec a) = Multiplicative.ofAdd a :=
  Function.surjInv_eq D.hπ (Multiplicative.ofAdd a)

/-- The section of `π` normalised so that `sec 0 = 1`. -/
def sec (a : A) : G := D.rawSec a * (D.rawSec 0)⁻¹

@[simp] theorem sec_zero : D.sec 0 = 1 := by simp [sec]

theorem pi_sec (a : A) : D.π (D.sec a) = Multiplicative.ofAdd a := by
  rw [sec, map_mul, map_inv, pi_rawSec, pi_rawSec]; simp

theorem tau_sec (a : A) : D.tau (D.sec a) = a := by
  rw [tau, pi_sec]; simp

/-- The `Z`-coordinate of `x`, so that `x = zc x * sec (tau x)`. -/
def zc (x : G) : D.Z :=
  ⟨x * (D.sec (D.tau x))⁻¹, by
    rw [← D.hker, MonoidHom.mem_ker, map_mul, map_inv, pi_sec]; simp [tau]⟩

theorem coe_zc_mul_sec (x : G) : (D.zc x : G) * D.sec (D.tau x) = x := by
  simp [zc]

theorem zc_central (x g : G) : (D.zc x : G) * g = g * (D.zc x : G) :=
  (Subgroup.mem_center_iff.mp (D.hZc (D.zc x).2) g).symm

theorem coe_central (z : D.Z) (g : G) : (z : G) * g = g * (z : G) :=
  (Subgroup.mem_center_iff.mp (D.hZc z.2) g).symm

/-- The `Z`-valued cocycle associated with the section `sec`. -/
def cc (a b : A) : D.Z :=
  ⟨D.sec a * D.sec b * (D.sec (a + b))⁻¹, by
    rw [← D.hker, MonoidHom.mem_ker, map_mul, map_mul, map_inv, pi_sec, pi_sec, pi_sec]
    simp⟩

theorem mul_cc (a b : A) : (D.cc a b : G) * D.sec (a + b) = D.sec a * D.sec b := by
  simp [cc]

theorem cc_central (a b : A) (g : G) : (D.cc a b : G) * g = g * (D.cc a b : G) :=
  D.coe_central (D.cc a b) g

@[simp] theorem cc_zero_left (a : A) : D.cc 0 a = 1 := by
  apply Subtype.ext; simp [cc]

@[simp] theorem cc_zero_right (a : A) : D.cc a 0 = 1 := by
  apply Subtype.ext; simp [cc]

theorem zc_mul (x y : G) : D.zc (x * y) = D.zc x * D.zc y * D.cc (D.tau x) (D.tau y) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  apply mul_right_cancel (b := D.sec (D.tau x + D.tau y))
  have hL : (D.zc (x * y) : G) * D.sec (D.tau x + D.tau y) = x * y := by
    rw [← D.tau_mul x y, D.coe_zc_mul_sec (x * y)]
  have hR : (↑(D.zc x) * ↑(D.zc y) * ↑(D.cc (D.tau x) (D.tau y))) *
      D.sec (D.tau x + D.tau y) = x * y := by
    rw [mul_assoc, D.mul_cc]
    conv_lhs =>
      rw [mul_assoc]
      enter [2]
      rw [← mul_assoc, D.zc_central, mul_assoc]
    rw [← mul_assoc, D.coe_zc_mul_sec, D.coe_zc_mul_sec]
  exact hL.trans hR.symm

theorem cc_cocycle (a b d : A) : D.cc a b * D.cc (a + b) d = D.cc b d * D.cc a (b + d) := by
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  apply mul_right_cancel (b := D.sec (a + b + d))
  have hL : (↑(D.cc a b) * ↑(D.cc (a + b) d)) * D.sec (a + b + d) =
      D.sec a * (D.sec b * D.sec d) := by
    rw [mul_assoc, D.mul_cc, ← mul_assoc, D.mul_cc, mul_assoc]
  have hR : (↑(D.cc b d) * ↑(D.cc a (b + d))) * D.sec (a + b + d) =
      D.sec a * (D.sec b * D.sec d) := by
    rw [mul_assoc, show (a + b) + d = a + (b + d) from add_assoc a b d,
        D.mul_cc a (b + d), ← mul_assoc, D.cc_central, mul_assoc, D.mul_cc b d]
  exact hL.trans hR.symm

theorem cc_self (a : A) : D.cc a a = ⟨(D.sec a) ^ 2, D.hsq (D.sec a)⟩ := by
  apply Subtype.ext
  show D.sec a * D.sec a * (D.sec (a + a))⁻¹ = (D.sec a) ^ 2
  rw [ZModModule.add_self, sec_zero, inv_one, mul_one, pow_two]

end ExtData

/-- If `g` is an isomorphism of the two central subgroups realising the same quadratic
form, then the `Z`-valued cocycles of the two compatible sections correspond. -/
theorem compat_cc {A : Type*} [AddCommGroup A] [Module (ZMod 2) A] {G G' : Type*} [Group G] [Group G']
    (D : ExtData A G) (D' : ExtData A G') (g : D.Z ≃* D'.Z)
    (hcompat : ∀ (x : G) (y : G'), D'.π y = D.π x → g ⟨x ^ 2, D.hsq x⟩ = ⟨y ^ 2, D'.hsq y⟩)
    (a : A) : g (D.cc a a) = D'.cc a a := by
  rw [D.cc_self a, D'.cc_self a]
  exact hcompat (D.sec a) (D'.sec a) (by rw [D'.pi_sec, D.pi_sec])

theorem quadratic_ext_iso {A : Type*} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    {P P' : Type*} [Group P] [Group P'] [Finite P] [Finite P']
    (Z : Subgroup P) (Z' : Subgroup P')
    (hZc : Z ≤ Subgroup.center P) (hZ2 : ∀ z ∈ Z, z * z = 1)
    (hZ'c : Z' ≤ Subgroup.center P') (hZ'2 : ∀ z ∈ Z', z * z = 1)
    (π : P →* Multiplicative A) (π' : P' →* Multiplicative A)
    (hπ : Function.Surjective π) (hπ' : Function.Surjective π')
    (hker : π.ker = Z) (hker' : π'.ker = Z')
    (g : Z ≃* Z')
    (hsq : ∀ x : P, x ^ 2 ∈ Z) (hsq' : ∀ x : P', x ^ 2 ∈ Z')
    (hcompat : ∀ (x : P) (y : P'), π' y = π x →
      g ⟨x ^ 2, hsq x⟩ = ⟨y ^ 2, hsq' y⟩) :
    ∃ e : P ≃* P', (∀ x : P, π' (e x) = π x) ∧ (∀ z : Z, (e (z : P) : P') = (g z : P')) := by
  let D : ExtData A P := ⟨Z, hZc, hZ2, π, hπ, hker, hsq⟩
  let D' : ExtData A P' := ⟨Z', hZ'c, hZ'2, π', hπ', hker', hsq'⟩
  have hcZ : ∀ x y : D'.Z, x * y = y * x := fun x y => by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    exact (Subgroup.mem_center_iff.mp (hZ'c x.2) (y : P')).symm
  have hM2 : ∀ x : D'.Z, x * x = 1 := fun x =>
    Subtype.ext (by
      show ((x * x : D'.Z) : P') = ((1 : D'.Z) : P')
      rw [Subgroup.coe_mul, Subgroup.coe_one]
      exact D'.hZ2 x x.2)
  -- The difference cocycle
  let δ : A → A → D'.Z := fun a b => g (D.cc a b) * D'.cc a b
  have hδ0l : ∀ a, δ 0 a = 1 := by
    intro a; change g (D.cc 0 a) * D'.cc 0 a = 1; simp
  have hδ0r : ∀ a, δ a 0 = 1 := by
    intro a; change g (D.cc a 0) * D'.cc a 0 = 1; simp
  have hδcoc : ∀ a b d, δ a b * δ (a + b) d = δ b d * δ a (b + d) := by
    intro a b d
    have hg : g (D.cc a b) * g (D.cc (a + b) d) = g (D.cc b d) * g (D.cc a (b + d)) := by
      rw [← map_mul, ← map_mul, D.cc_cocycle]
    have hc : D'.cc a b * D'.cc (a + b) d = D'.cc b d * D'.cc a (b + d) :=
      D'.cc_cocycle a b d
    change g (D.cc a b) * D'.cc a b * (g (D.cc (a + b) d) * D'.cc (a + b) d)
         = g (D.cc b d) * D'.cc b d * (g (D.cc a (b + d)) * D'.cc a (b + d))
    rw [show g (D.cc a b) * D'.cc a b * (g (D.cc (a + b) d) * D'.cc (a + b) d)
          = g (D.cc a b) * g (D.cc (a + b) d) * (D'.cc a b * D'.cc (a + b) d)
        from rearr hcZ (g (D.cc a b)) (D'.cc a b) (g (D.cc (a + b) d)) (D'.cc (a + b) d),
        hg, hc,
        show g (D.cc b d) * g (D.cc a (b + d)) * (D'.cc b d * D'.cc a (b + d))
          = g (D.cc b d) * D'.cc b d * (g (D.cc a (b + d)) * D'.cc a (b + d))
        from rearr hcZ (g (D.cc b d)) (g (D.cc a (b + d))) (D'.cc b d) (D'.cc a (b + d))]
  have hδdiag : ∀ v, δ v v = 1 := by
    intro v
    change g (D.cc v v) * D'.cc v v = 1
    rw [← compat_cc D D' g hcompat v, hM2]
  obtain ⟨f, hf0, hf⟩ :=
    coboundary_of_group hcZ hM2 δ hδ0l hδ0r hδcoc hδdiag
  -- The modified section of `π'`
  let sec2 : A → P' := fun a => (f a : P') * D'.sec a
  have hsec2_pi : ∀ a, D'.π (sec2 a) = Multiplicative.ofAdd a := by
    intro a
    change D'.π ((f a : P') * D'.sec a) = Multiplicative.ofAdd a
    have hmem : (f a : P') ∈ D'.π.ker := by rw [D'.hker]; exact (f a).2
    rw [map_mul, D'.pi_sec, MonoidHom.mem_ker.mp hmem]; simp
  have hfglue : ∀ a b : A,
      (f a : P') * (f b : P') * (D'.cc a b : P') = (g (D.cc a b) : P') * (f (a + b) : P') := by
    intro a b
    have h : g (D.cc a b) * D'.cc a b = f (a + b) * f a * f b := by
      change δ a b = f (a + b) * f a * f b
      exact hf a b
    have hZ : f a * f b * D'.cc a b = g (D.cc a b) * f (a + b) :=
      glue_commGroup hcZ hM2 (g (D.cc a b)) (f (a + b)) (f a) (f b) (D'.cc a b) h
    have hcoe : ((f a * f b * D'.cc a b : D'.Z) : P') =
        ((g (D.cc a b) * f (a + b) : D'.Z) : P') := congrArg _ hZ
    simp only [Subgroup.coe_mul] at hcoe
    exact hcoe
  have hsec2_mul : ∀ a b, sec2 a * sec2 b = (g (D.cc a b) : P') * sec2 (a + b) := by
    intro a b
    have key : sec2 a * sec2 b =
        ((g (D.cc a b) : P') * (f (a + b) : P')) * D'.sec (a + b) := by
      change ((f a : P') * D'.sec a) * ((f b : P') * D'.sec b) = _
      conv_lhs =>
        rw [mul_assoc]
        enter [2]
        rw [← mul_assoc, ← D'.coe_central, mul_assoc]
      conv_lhs => rw [← mul_assoc]
      conv_lhs => rw [← D'.mul_cc]
      conv_lhs => rw [← mul_assoc]
      conv_lhs => rw [hfglue]
    rw [key]
    show ((g (D.cc a b) : P') * (f (a + b) : P')) * D'.sec (a + b) =
      (g (D.cc a b) : P') * ((f (a + b) : P') * D'.sec (a + b))
    rw [mul_assoc]
  -- The candidate isomorphism
  let eFun : P → P' := fun x => (g (D.zc x) : P') * sec2 (D.tau x)
  have he_pi : ∀ x, D'.π (eFun x) = D.π x := by
    intro x
    change D'.π ((g (D.zc x) : P') * sec2 (D.tau x)) = D.π x
    have hmem : (g (D.zc x) : P') ∈ D'.π.ker := by rw [D'.hker]; exact (g (D.zc x)).2
    rw [map_mul, MonoidHom.mem_ker.mp hmem, hsec2_pi]
    simp [ExtData.tau]
  have he_tau : ∀ x, D'.tau (eFun x) = D.tau x := by
    intro x
    change Multiplicative.toAdd (D'.π (eFun x)) = Multiplicative.toAdd (D.π x)
    rw [he_pi x]
  have he_mul : ∀ x y, eFun (x * y) = eFun x * eFun y := by
    intro x y
    have key : eFun (x * y) =
        ((g (D.zc x) : P') * (g (D.zc y) : P') *
          (g (D.cc (D.tau x) (D.tau y)) : P')) * sec2 (D.tau x + D.tau y) := by
      change (g (D.zc (x * y)) : P') * sec2 (D.tau (x * y)) = _
      rw [D.tau_mul, D.zc_mul, map_mul, map_mul]
      simp only [Subgroup.coe_mul]
    have key2 : eFun x * eFun y =
        ((g (D.zc x) : P') * (g (D.zc y) : P') *
          (g (D.cc (D.tau x) (D.tau y)) : P')) * sec2 (D.tau x + D.tau y) := by
      change ((g (D.zc x) : P') * sec2 (D.tau x)) *
        ((g (D.zc y) : P') * sec2 (D.tau y)) = _
      conv_lhs =>
        rw [mul_assoc]
        enter [2]
        rw [← mul_assoc, ← D'.coe_central, mul_assoc]
      conv_lhs => rw [← mul_assoc]
      conv_lhs => rw [hsec2_mul]
      conv_lhs => rw [← mul_assoc]
    rw [key, key2]
  let zc2 : P' → D'.Z := fun y => ⟨y * (sec2 (D'.tau y))⁻¹, by
    rw [← D'.hker, MonoidHom.mem_ker, map_mul, map_inv, hsec2_pi]; simp [ExtData.tau]⟩
  let eInv : P' → P := fun y => (g.symm (zc2 y) : P) * D.sec (D'.tau y)
  have heInv_pi : ∀ y, D.π (eInv y) = D'.π y := by
    intro y
    change D.π ((g.symm (zc2 y) : P) * D.sec (D'.tau y)) = D'.π y
    have hmem : (g.symm (zc2 y) : P) ∈ D.π.ker := by rw [D.hker]; exact (g.symm (zc2 y)).2
    rw [map_mul, MonoidHom.mem_ker.mp hmem, D.pi_sec]
    simp [ExtData.tau]
  have heInv_tau : ∀ y, D.tau (eInv y) = D'.tau y := by
    intro y
    change Multiplicative.toAdd (D.π (eInv y)) = Multiplicative.toAdd (D'.π y)
    rw [heInv_pi y]
  have hleft : ∀ x, eInv (eFun x) = x := by
    intro x
    have hzc2 : zc2 (eFun x) = g (D.zc x) := by
      apply Subtype.ext
      change eFun x * (sec2 (D'.tau (eFun x)))⁻¹ = (g (D.zc x) : P')
      rw [he_tau x]
      show ((g (D.zc x) : P') * sec2 (D.tau x)) * (sec2 (D.tau x))⁻¹ = (g (D.zc x) : P')
      rw [mul_assoc, mul_inv_cancel, mul_one]
    change (g.symm (zc2 (eFun x)) : P) * D.sec (D'.tau (eFun x)) = x
    rw [hzc2, he_tau x, MulEquiv.symm_apply_apply]
    exact D.coe_zc_mul_sec x
  have hzc_eInv : ∀ y, D.zc (eInv y) = g.symm (zc2 y) := by
    intro y
    apply Subtype.ext
    change eInv y * (D.sec (D.tau (eInv y)))⁻¹ = (g.symm (zc2 y) : P)
    rw [heInv_tau y]
    show ((g.symm (zc2 y) : P) * D.sec (D'.tau y)) * (D.sec (D'.tau y))⁻¹ = (g.symm (zc2 y) : P)
    rw [mul_assoc, mul_inv_cancel, mul_one]
  have hright : ∀ y, eFun (eInv y) = y := by
    intro y
    have hzc2y : (zc2 y : P') * sec2 (D'.tau y) = y := by
      change (y * (sec2 (D'.tau y))⁻¹) * sec2 (D'.tau y) = y
      rw [mul_assoc, inv_mul_cancel, mul_one]
    change (g (D.zc (eInv y)) : P') * sec2 (D.tau (eInv y)) = y
    rw [hzc_eInv y, heInv_tau y, MulEquiv.apply_symm_apply]
    exact hzc2y
  refine ⟨MulEquiv.mk
    { toFun := eFun, invFun := eInv, left_inv := hleft, right_inv := hright } he_mul, ?_, ?_⟩
  · intro x; exact he_pi x
  · intro z
    have hπz : D.π (z : P) = 1 := MonoidHom.mem_ker.mp (by rw [D.hker]; exact z.2)
    have htauz : D.tau (z : P) = 0 := by
      change Multiplicative.toAdd (D.π (z : P)) = 0
      rw [hπz]; simp
    have hzcz : D.zc (z : P) = z := by
      apply Subtype.ext
      show (z : P) * (D.sec (D.tau (z : P)))⁻¹ = (z : P)
      rw [htauz, D.sec_zero, inv_one, mul_one]
    show (g (D.zc (z : P)) : P') * sec2 (D.tau (z : P)) = (g z : P')
    rw [hzcz, htauz]
    show (g z : P') * ((f 0 : P') * D'.sec 0) = (g z : P')
    rw [hf0, D'.sec_zero, Subgroup.coe_one, one_mul, mul_one]

end

end Work.PSU3.FineCoords
