import Mathlib.Tactic.Abel
import Mathlib.GroupTheory.QuotientGroup.Defs
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.GroupWithZero.Action.Defs
import Submission.Work.GroupCohomology.Connecting
import Submission.Work.GroupCohomology.H2pi_eq_iff
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u v w x

namespace Work.GroupCohomology

variable {G : Type u} {A : Type v} {B : Type w} {C : Type x} [Group G]
variable [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
variable [DistribMulAction G A] [DistribMulAction G B] [DistribMulAction G C]

namespace ShortExactSeq

variable (S : ShortExactSeq G A B C)

/-- `preimage` only depends on the element of `ker pi`, not on the proof that it lies there. -/
theorem preimage_proof_irrel (b : B) (h h' : b ∈ S.pi.ker) : S.preimage b h = S.preimage b h' :=
  congrArg Classical.choose (Subsingleton.elim (S.exists_preimage h) (S.exists_preimage h'))

/-- The differential of *any* lift of a `1`-cocycle of `C` lies in `ker pi`. -/
theorem pi_d1_eq_zero (c : G → C) (hc : c ∈ Z1 G C) (b : G → B) (hb : ∀ g, S.pi (b g) = c g)
    (g h : G) : S.pi (d1 G B b (g, h)) = 0 := by
  have h1 : S.pi (g • b h) = g • c h := by rw [S.pi_equivariant g (b h), hb h]
  have h2 : S.pi (b (g * h)) = c (g * h) := hb (g * h)
  have h3 : S.pi (b g) = c g := hb g
  have hc' : c (g * h) = g • c h + c g := hc g h
  simp only [d1_apply, map_sub, map_add, h1, h2, h3]
  rw [hc']
  abel

/-- **The connecting cocycle computed from a prescribed lift.**  For a `1`-cocycle `c : G → C` and
a cochain `b : G → B` with `pi ∘ b = c`, the pullback along `iota` of `d¹ b` is a `2`-cocycle with
values in `A`. -/
noncomputable def deltaCocycleOf (c : Z1 G C) (b : G → B)
    (hb : ∀ g, S.pi (b g) = (c : G → C) g) : Z2 G A :=
  ⟨fun p => S.preimage (d1 G B b p) (by
      obtain ⟨g, h⟩ := p
      exact S.pi_d1_eq_zero (c : G → C) c.2 b hb g h),
    by
      rw [mem_Z2_iff]
      intro g h k
      apply S.iota_injective
      rw [map_add, map_add, S.iota_equivariant, S.iota_preimage, S.iota_preimage,
        S.iota_preimage, S.iota_preimage]
      have hzero : g • d1 G B b (h, k) - d1 G B b (g * h, k) + d1 G B b (g, h * k) -
          d1 G B b (g, h) = 0 := by
        have h2 : d2 G B (d1 G B b) (g, h, k) = 0 := congrFun (d2_d1 G B b) (g, h, k)
        simpa only [Pi.zero_apply, d2_apply] using h2
      rw [← sub_eq_zero]
      rw [show d1 G B b (g * h, k) + d1 G B b (g, h) -
            (g • d1 G B b (h, k) + d1 G B b (g, h * k)) =
          -(g • d1 G B b (h, k) - d1 G B b (g * h, k) + d1 G B b (g, h * k) -
            d1 G B b (g, h)) from by abel]
      rw [hzero, neg_zero]⟩

@[simp] theorem deltaCocycleOf_apply (c : Z1 G C) (b : G → B)
    (hb : ∀ g, S.pi (b g) = (c : G → C) g) (g h : G) :
    (S.deltaCocycleOf c b hb : G × G → A) (g, h) =
      S.preimage (d1 G B b (g, h)) (S.pi_d1_eq_zero (c : G → C) c.2 b hb g h) := rfl

/-- Pushing `deltaCocycleOf` forward along `iota` recovers `d¹` of the lift. -/
theorem iota_deltaCocycleOf (c : Z1 G C) (b : G → B)
    (hb : ∀ g, S.pi (b g) = (c : G → C) g) (g h : G) :
    S.iota ((S.deltaCocycleOf c b hb : G × G → A) (g, h)) = d1 G B b (g, h) := by
  rw [S.deltaCocycleOf_apply]
  exact S.iota_preimage _ _

/-- For the canonical lift `S.liftCochain c`, `deltaCocycleOf` is `deltaCocycle`. -/
theorem deltaCocycleOf_self (c : Z1 G C) :
    S.deltaCocycleOf c (S.liftCochain (c : G → C)) (S.pi_liftCochain (c : G → C)) =
      S.deltaCocycle c := by
  apply Subtype.ext
  funext p
  obtain ⟨g, h⟩ := p
  rw [deltaCocycleOf_apply, deltaCocycle_apply]

/-- The class in `H²(G, A)` of the connecting cocycle computed from a prescribed lift. -/
noncomputable def deltaClassOf (c : Z1 G C) (b : G → B)
    (hb : ∀ g, S.pi (b g) = (c : G → C) g) : H2 G A :=
  H2π G A (S.deltaCocycleOf c b hb)

/-- Pushing `deltaCocycleOf` forward along `iota` recovers `d¹` of the lift, as a function. -/
theorem mapCochain2_iota_deltaCocycleOf (c : Z1 G C) (b : G → B)
    (hb : ∀ g, S.pi (b g) = (c : G → C) g) :
    mapCochain2 G S.iota (S.deltaCocycleOf c b hb : G × G → A) = d1 G B b := by
  funext p
  obtain ⟨g, h⟩ := p
  rw [mapCochain2_apply, S.iota_deltaCocycleOf]

/-- **Independence of the lift.**  Two lifts of the same `1`-cocycle of `C` define the same class
in `H²(G, A)`. -/
theorem deltaCocycleOf_eq_of_pi_eq (c : Z1 G C) (b b' : G → B)
    (hb : ∀ g, S.pi (b g) = (c : G → C) g) (hb' : ∀ g, S.pi (b' g) = (c : G → C) g) :
    H2π G A (S.deltaCocycleOf c b hb) = H2π G A (S.deltaCocycleOf c b' hb') := by
  rw [H2pi_eq_iff, mem_B2_iff]
  have hker : ∀ g : G, b g - b' g ∈ S.pi.ker := by
    intro g
    rw [AddMonoidHom.mem_ker, map_sub, hb g, hb' g, sub_self]
  choose k hk using fun g : G => S.exists_preimage (hker g)
  have hb_sub : b - b' = fun g => S.iota (k g) := funext fun g => (hk g).symm
  have hmap1 : mapCochain1 G S.iota k = fun g => S.iota (k g) := rfl
  have h1 : mapCochain2 G S.iota
      (↑(S.deltaCocycleOf c b hb - S.deltaCocycleOf c b' hb') : G × G → A) =
      mapCochain2 G S.iota (d1 G A k) := by
    rw [AddSubgroup.coe_sub, map_sub, S.mapCochain2_iota_deltaCocycleOf c b hb,
      S.mapCochain2_iota_deltaCocycleOf c b' hb', ← map_sub, hb_sub, ← hmap1,
      ← mapCochain2_d1 G S.iota S.iota_equivariant k]
  refine ⟨k, ?_⟩
  funext p
  obtain ⟨g, h⟩ := p
  exact S.iota_injective (by simpa only [mapCochain2_apply] using (congrFun h1 (g, h)).symm)

/-- For the canonical lift, the class of `deltaCocycle` is the class computed with any other
lift. -/
theorem deltaCocycle_eq_of_lift (c : Z1 G C) (b : G → B)
    (hb : ∀ g, S.pi (b g) = (c : G → C) g) :
    H2π G A (S.deltaCocycle c) = H2π G A (S.deltaCocycleOf c b hb) := by
  rw [← S.deltaCocycleOf_self c]
  exact S.deltaCocycleOf_eq_of_pi_eq c (S.liftCochain (c : G → C)) b
    (S.pi_liftCochain (c : G → C)) hb

end ShortExactSeq

end Work.GroupCohomology
